//! Command for debugging execution.

use alloy_eips::BlockHashOrNumber;
use alloy_primitives::{BlockNumber, B256};
use clap::Parser;
use futures::StreamExt;
use reth_chainspec::ChainSpec;
use reth_cli::chainspec::ChainSpecParser;
use reth_cli_commands::common::{AccessRights, CliNodeTypes, Environment, EnvironmentArgs};
use reth_cli_runner::CliContext;
use reth_config::Config;
use reth_consensus::FullConsensus;
use reth_db::DatabaseEnv;
use reth_errors::ConsensusError;
use reth_ethereum_primitives::EthPrimitives;
use reth_network::{BlockDownloaderProvider, NetworkHandle};
use reth_network_p2p::{headers::client::HeadersClient, EthBlockClient};
use reth_node_api::NodeTypesWithDBAdapter;
use reth_node_core::{args::NetworkArgs, utils::get_single_header};
use reth_node_ethereum::consensus::EthBeaconConsensus;
use reth_node_events::node::NodeEvent;
use reth_provider::{
    providers::ProviderNodeTypes, ChainSpecProvider, ProviderFactory, StageCheckpointReader,
};
use reth_prune::PruneModes;
use reth_stages::{Pipeline, StageId};
use reth_static_file::StaticFileProducer;
use reth_tasks::TaskExecutor;
use std::{path::PathBuf, sync::Arc};
use tracing::*;

/// `reth debug execution` command
#[derive(Debug, Parser)]
pub struct Command<C: ChainSpecParser> {
    #[command(flatten)]
    env: EnvironmentArgs<C>,

    #[command(flatten)]
    network: NetworkArgs,

    /// The maximum block height.
    #[arg(long)]
    pub to: u64,

    /// The block interval for sync and unwind.
    /// Defaults to `1000`.
    #[arg(long, default_value = "1000")]
    pub interval: u64,
}

impl<C: ChainSpecParser<ChainSpec = ChainSpec>> Command<C> {
    fn build_pipeline<N, Client>(
        &self,
        _config: &Config,
        _client: Client,
        _consensus: Arc<dyn FullConsensus<N::Primitives, Error = ConsensusError>>,
        _provider_factory: ProviderFactory<N>,
        _task_executor: &TaskExecutor,
        _static_file_producer: StaticFileProducer<ProviderFactory<N>>,
    ) -> eyre::Result<Pipeline<N>>
    where
        N: ProviderNodeTypes<ChainSpec = C::ChainSpec, Primitives = EthPrimitives>,
        Client: EthBlockClient + 'static,
    {
        unimplemented!("Patched out.")
    }

    async fn build_network<
        N: CliNodeTypes<ChainSpec = C::ChainSpec, Primitives = EthPrimitives>,
    >(
        &self,
        _config: &Config,
        _task_executor: TaskExecutor,
        _provider_factory: ProviderFactory<NodeTypesWithDBAdapter<N, Arc<DatabaseEnv>>>,
        _network_secret_path: PathBuf,
        _default_peers_path: PathBuf,
    ) -> eyre::Result<NetworkHandle> {
        unimplemented!("Patched out.")
    }

    async fn fetch_block_hash<Client>(
        &self,
        client: Client,
        block: BlockNumber,
    ) -> eyre::Result<B256>
    where
        Client: HeadersClient<Header: reth_primitives_traits::BlockHeader>,
    {
        info!(target: "reth::cli", ?block, "Fetching block from the network.");
        loop {
            match get_single_header(&client, BlockHashOrNumber::Number(block)).await {
                Ok(tip_header) => {
                    info!(target: "reth::cli", ?block, "Successfully fetched block");
                    return Ok(tip_header.hash())
                }
                Err(error) => {
                    error!(target: "reth::cli", ?block, %error, "Failed to fetch the block. Retrying...");
                }
            }
        }
    }

    /// Execute `execution-debug` command
    pub async fn execute<N: CliNodeTypes<ChainSpec = C::ChainSpec, Primitives = EthPrimitives>>(
        self,
        ctx: CliContext,
    ) -> eyre::Result<()> {
        let Environment { provider_factory, config, data_dir } =
            self.env.init::<N>(AccessRights::RW)?;

        let consensus: Arc<dyn FullConsensus<N::Primitives, Error = ConsensusError>> =
            Arc::new(EthBeaconConsensus::new(provider_factory.chain_spec()));

        // Configure and build network
        let network_secret_path =
            self.network.p2p_secret_key.clone().unwrap_or_else(|| data_dir.p2p_secret());
        let network = self
            .build_network(
                &config,
                ctx.task_executor.clone(),
                provider_factory.clone(),
                network_secret_path,
                data_dir.known_peers(),
            )
            .await?;

        let static_file_producer =
            StaticFileProducer::new(provider_factory.clone(), PruneModes::default());

        // Configure the pipeline
        let fetch_client = network.fetch_client().await?;
        let mut pipeline = self.build_pipeline(
            &config,
            fetch_client.clone(),
            consensus.clone(),
            provider_factory.clone(),
            &ctx.task_executor,
            static_file_producer,
        )?;

        let provider = provider_factory.provider()?;

        let latest_block_number =
            provider.get_stage_checkpoint(StageId::Finish)?.map(|ch| ch.block_number);
        if latest_block_number.unwrap_or_default() >= self.to {
            info!(target: "reth::cli", latest = latest_block_number, "Nothing to run");
            return Ok(())
        }

        ctx.task_executor.spawn_critical(
            "events task",
            reth_node_events::node::handle_events(
                Some(Box::new(network)),
                latest_block_number,
                pipeline.events().map(Into::<NodeEvent<N::Primitives>>::into),
            ),
        );

        let mut current_max_block = latest_block_number.unwrap_or_default();
        while current_max_block < self.to {
            let next_block = current_max_block + 1;
            let target_block = self.to.min(current_max_block + self.interval);
            let target_block_hash =
                self.fetch_block_hash(fetch_client.clone(), target_block).await?;

            // Run the pipeline
            info!(target: "reth::cli", from = next_block, to = target_block, tip = ?target_block_hash, "Starting pipeline");
            pipeline.set_tip(target_block_hash);
            let result = pipeline.run_loop().await?;
            trace!(target: "reth::cli", from = next_block, to = target_block, tip = ?target_block_hash, ?result, "Pipeline finished");

            // Unwind the pipeline without committing.
            provider_factory.provider_rw()?.unwind_trie_state_range(next_block..=target_block)?;

            // Update latest block
            current_max_block = target_block;
        }

        Ok(())
    }
}

impl<C: ChainSpecParser> Command<C> {
    /// Returns the underlying chain being used to run this command
    pub const fn chain_spec(&self) -> Option<&Arc<C::ChainSpec>> {
        Some(&self.env.chain)
    }
}
