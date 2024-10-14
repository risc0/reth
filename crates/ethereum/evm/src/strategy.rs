//! Ethereum block execution strategy,

use crate::{
    dao_fork::{DAO_HARDFORK_BENEFICIARY, DAO_HARDKFORK_ACCOUNTS},
    EthEvmConfig,
};
use core::fmt::Display;
use reth_chainspec::{ChainSpec, EthereumHardfork, EthereumHardforks, MAINNET};
use reth_evm::{
    execute::{
        BlockExecutionError, BlockExecutionStrategy, BlockExecutionStrategyFactory,
        BlockValidationError, ProviderError,
    },
    system_calls::{OnStateHook, SystemCaller},
    ConfigureEvm, ConfigureEvmEnv,
};
use reth_primitives::{BlockWithSenders, Header, Receipt, Request};
use reth_revm::{
    db::{states::bundle_state::BundleRetention, BundleState},
    state_change::post_block_balance_increments,
    Database, DatabaseCommit, Evm, State,
};
use revm_primitives::{BlockEnv, CfgEnvWithHandlerCfg, EnvWithHandlerCfg, ResultAndState, U256};
use std::sync::Arc;

/// Factory for [`EthExecutionStrategy`].
#[derive(Debug, Clone)]
pub struct EthExecutionStrategyFactory<EvmConfig = EthEvmConfig> {
    /// The chainspec
    chain_spec: Arc<ChainSpec>,
    /// How to create an EVM.
    evm_config: EvmConfig,
}

impl EthExecutionStrategyFactory {
    /// Creates a new default ethereum executor strategy factory.
    pub fn ethereum(chain_spec: Arc<ChainSpec>) -> Self {
        Self::new(chain_spec.clone(), EthEvmConfig::new(chain_spec))
    }

    /// Returns a new factory for the mainnet.
    pub fn mainnet() -> Self {
        Self::ethereum(MAINNET.clone())
    }
}

impl<EvmConfig> EthExecutionStrategyFactory<EvmConfig> {
    /// Creates a new executor strategy factory.
    pub const fn new(chain_spec: Arc<ChainSpec>, evm_config: EvmConfig) -> Self {
        Self { chain_spec, evm_config }
    }
}

impl BlockExecutionStrategyFactory for EthExecutionStrategyFactory {
    type Strategy<DB: Database<Error: Into<ProviderError> + Display>> = EthExecutionStrategy<DB>;

    fn create_strategy<DB>(&self, db: DB) -> Self::Strategy<DB>
    where
        DB: Database<Error: Into<ProviderError> + Display>,
    {
        let state =
            State::builder().with_database(db).with_bundle_update().without_state_clear().build();
        EthExecutionStrategy::new(state, self.chain_spec.clone(), self.evm_config.clone())
    }
}

/// Block execution strategy for Ethereum.
#[allow(missing_debug_implementations)]
pub struct EthExecutionStrategy<DB, EvmConfig = EthEvmConfig> {
    /// The chainspec
    chain_spec: Arc<ChainSpec>,
    /// How to create an EVM.
    evm_config: EvmConfig,
    /// Current state for block execution.
    state: State<DB>,
    /// Utility to call system smart contracts.
    system_caller: SystemCaller<EvmConfig, ChainSpec>,
}

impl<DB> EthExecutionStrategy<DB> {
    /// Creates a new [`EthExecutionStrategy`]
    pub fn new(state: State<DB>, chain_spec: Arc<ChainSpec>, evm_config: EthEvmConfig) -> Self {
        let system_caller = SystemCaller::new(evm_config.clone(), (*chain_spec).clone());
        Self { state, chain_spec, evm_config, system_caller }
    }
}

impl<DB, EvmConfig> EthExecutionStrategy<DB, EvmConfig>
where
    DB: Database<Error: Into<ProviderError> + Display>,
    EvmConfig: ConfigureEvm<Header = Header>,
{
    /// Configures a new evm configuration and block environment for the given block.
    ///
    /// # Caution
    ///
    /// This does not initialize the tx environment.
    fn evm_env_for_block(&self, header: &Header, total_difficulty: U256) -> EnvWithHandlerCfg {
        let mut cfg = CfgEnvWithHandlerCfg::new(Default::default(), Default::default());
        let mut block_env = BlockEnv::default();
        self.evm_config.fill_cfg_and_block_env(&mut cfg, &mut block_env, header, total_difficulty);

        EnvWithHandlerCfg::new_with_cfg_env(cfg, block_env, Default::default())
    }

    #[allow(dead_code)]
    fn evm<'a>(
        &mut self,
        header: Header,
        total_difficulty: U256,
    ) -> Evm<'a, <EvmConfig as ConfigureEvm>::DefaultExternalContext<'_>, &mut State<DB>> {
        let env = self.evm_env_for_block(&header, total_difficulty);
        self.evm_config.evm_with_env(&mut self.state, env)
    }
}

impl<DB> BlockExecutionStrategy<DB> for EthExecutionStrategy<DB>
where
    DB: Database<Error: Into<ProviderError> + Display>,
{
    type Error = BlockExecutionError;

    fn apply_pre_execution_changes(&mut self, block: &BlockWithSenders) -> Result<(), Self::Error> {
        // Set state clear flag if the block is after the Spurious Dragon hardfork.
        let state_clear_flag =
            (*self.chain_spec).is_spurious_dragon_active_at_block(block.header.number);
        self.state.set_state_clear_flag(state_clear_flag);

        Ok(())
    }

    fn execute_transactions(
        &mut self,
        block: &BlockWithSenders,
        total_difficulty: U256,
    ) -> Result<(Vec<Receipt>, u64), Self::Error> {
        let env = self.evm_env_for_block(&block.header, total_difficulty);
        let mut evm = self.evm_config.evm_with_env(&mut self.state, env);

        let mut cumulative_gas_used = 0;
        let mut receipts = Vec::with_capacity(block.body.transactions.len());
        for (sender, transaction) in block.transactions_with_sender() {
            // The sum of the transaction’s gas limit, Tg, and the gas utilized in this block prior,
            // must be no greater than the block’s gasLimit.
            let block_available_gas = block.header.gas_limit - cumulative_gas_used;
            if transaction.gas_limit() > block_available_gas {
                return Err(BlockValidationError::TransactionGasLimitMoreThanAvailableBlockGas {
                    transaction_gas_limit: transaction.gas_limit(),
                    block_available_gas,
                }
                .into())
            }

            self.evm_config.fill_tx_env(evm.tx_mut(), transaction, *sender);

            // Execute transaction.
            let result_and_state = evm.transact().map_err(move |err| {
                let new_err = err.map_db_err(|e| e.into());
                // Ensure hash is calculated for error log, if not already done
                BlockValidationError::EVM {
                    hash: transaction.recalculate_hash(),
                    error: Box::new(new_err),
                }
            })?;
            self.system_caller.on_state(&result_and_state);
            let ResultAndState { result, state } = result_and_state;
            evm.db_mut().commit(state);

            // append gas used
            cumulative_gas_used += result.gas_used();

            // Push transaction changeset and calculate header bloom filter for receipt.
            receipts.push(
                #[allow(clippy::needless_update)] // side-effect of optimism fields
                Receipt {
                    tx_type: transaction.tx_type(),
                    // Success flag was added in `EIP-658: Embedding transaction status code in
                    // receipts`.
                    success: result.is_success(),
                    cumulative_gas_used,
                    // convert to reth log
                    logs: result.into_logs(),
                    ..Default::default()
                },
            );
        }
        Ok((receipts, cumulative_gas_used))
    }

    fn apply_post_execution_changes(
        &mut self,
        block: &BlockWithSenders,
        total_difficulty: U256,
        receipts: &[Receipt],
    ) -> Result<Vec<Request>, Self::Error> {
        let env = self.evm_env_for_block(&block.header, total_difficulty);
        let mut evm = self.evm_config.evm_with_env(&mut self.state, env);

        let requests = if self.chain_spec.is_prague_active_at_timestamp(block.timestamp) {
            // Collect all EIP-6110 deposits
            let deposit_requests =
                crate::eip6110::parse_deposits_from_receipts(&self.chain_spec, receipts)?;

            let post_execution_requests =
                self.system_caller.apply_post_execution_changes(&mut evm)?;

            [deposit_requests, post_execution_requests].concat()
        } else {
            vec![]
        };
        drop(evm);

        let mut balance_increments =
            post_block_balance_increments(&self.chain_spec, block, total_difficulty);

        // Irregular state change at Ethereum DAO hardfork
        if self.chain_spec.fork(EthereumHardfork::Dao).transitions_at_block(block.number) {
            // drain balances from hardcoded addresses.
            let drained_balance: u128 = self
                .state
                .drain_balances(DAO_HARDKFORK_ACCOUNTS)
                .map_err(|_| BlockValidationError::IncrementBalanceFailed)?
                .into_iter()
                .sum();

            // return balance to DAO beneficiary.
            *balance_increments.entry(DAO_HARDFORK_BENEFICIARY).or_default() += drained_balance;
        }
        // increment balances
        self.state
            .increment_balances(balance_increments)
            .map_err(|_| BlockValidationError::IncrementBalanceFailed)?;

        Ok(requests)
    }

    fn state_ref(&self) -> &State<DB> {
        &self.state
    }

    fn with_state_hook(&mut self, hook: Option<Box<dyn OnStateHook>>) {
        self.system_caller.with_state_hook(hook);
    }

    fn finish(&mut self) -> BundleState {
        self.state.merge_transitions(BundleRetention::Reverts);
        self.state.take_bundle()
    }
}
