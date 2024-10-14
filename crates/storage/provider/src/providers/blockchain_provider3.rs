use crate::{
    providers::StaticFileProvider, AccountReader, BlockHashReader, BlockIdReader, BlockNumReader,
    BlockReader, BlockReaderIdExt, BlockSource, CanonChainTracker, CanonStateNotifications,
    CanonStateSubscriptions, ChainSpecProvider, ChangeSetReader, DatabaseProviderFactory,
    EvmEnvProvider, FullProvider, HeaderProvider, ProviderError, PruneCheckpointReader,
    ReceiptProvider, ReceiptProviderIdExt, RequestsProvider, StageCheckpointReader,
    StateProviderBox, StateProviderFactory, StateReader, StaticFileProviderFactory,
    TransactionVariant, TransactionsProvider, WithdrawalsProvider,
};
use alloy_eips::{BlockHashOrNumber, BlockId, BlockNumHash, BlockNumberOrTag, HashOrNumber};
use alloy_primitives::{Address, BlockHash, BlockNumber, Sealable, TxHash, TxNumber, B256, U256};
use alloy_rpc_types_engine::ForkchoiceState;
use parking_lot::RwLock;
use reth_chain_state::{
    BlockState, CanonicalInMemoryState, ForkChoiceNotifications, ForkChoiceSubscriptions,
    MemoryOverlayStateProvider,
};
use reth_chainspec::{ChainInfo, EthereumHardforks};
use reth_db::{models::BlockNumberAddress, Database};
use reth_db_api::models::{AccountBeforeTx, StoredBlockBodyIndices};
use reth_evm::ConfigureEvmEnv;
use reth_execution_types::{BundleStateInit, ExecutionOutcome, RevertsInit};
use reth_node_types::NodeTypesWithDB;
use reth_primitives::{
    Account, Block, BlockWithSenders, Header, Receipt, SealedBlock, SealedBlockWithSenders,
    SealedHeader, StorageEntry, TransactionMeta, TransactionSigned, TransactionSignedNoHash,
    Withdrawal, Withdrawals,
};
use reth_prune_types::{PruneCheckpoint, PruneSegment};
use reth_stages_types::{StageCheckpoint, StageId};
use reth_storage_api::{DBProvider, StorageChangeSetReader};
use reth_storage_errors::provider::ProviderResult;
use revm::{
    db::states::PlainStorageRevert,
    primitives::{BlockEnv, CfgEnvWithHandlerCfg},
};
use std::{
    collections::{hash_map, HashMap},
    marker::PhantomData,
    ops::{Add, Bound, RangeBounds, RangeInclusive, Sub},
    sync::Arc,
    time::Instant,
};
use tracing::trace;

use super::ProviderNodeTypes;

/// The main type for interacting with the blockchain.
///
/// This type serves as the main entry point for interacting with the blockchain and provides data
/// from database storage and from the blockchain tree (pending state etc.) It is a simple wrapper
/// type that holds an instance of the database and the blockchain tree.
#[derive(Debug)]
pub(crate) struct BlockchainProvider3<SP, N> {
    /// Storage provider.
    storage_provider: SP,
    /// Head block at time of [`Self`] creation
    head_block: Arc<BlockState>,
    /// Snapshotted chain. It starts as empty, requiring [`Self::in_memory_chain()`] to be called.
    /// Use `self.head_block.chain()` instead if you don't care about iteration order.
    memory_chain: RwLock<Arc<Vec<Arc<BlockState>>>>,
    /// In-memory canonical state. This is not a snapshot, and can change! Use with caution.
    canonical_state: CanonicalInMemoryState,
    _phantom: PhantomData<N>,
}

impl<SP, N> BlockchainProvider3<SP, N> {
    fn in_memory_chain(&self) -> Arc<Vec<Arc<BlockState>>> {
        let chain = self.memory_chain.read();
        if chain.is_empty() {
            drop(chain);
            let mut chain = self.memory_chain.write();
            *chain = Arc::new(self.head_block.clone().iter().collect::<Vec<_>>());
            return chain.clone()
        }
        chain.clone()
    }
}

impl<SP: Clone, N> Clone for BlockchainProvider3<SP, N> {
    fn clone(&self) -> Self {
        Self {
            storage_provider: self.storage_provider.clone(),
            head_block: self.head_block.clone(),
            canonical_state: self.canonical_state.clone(),
            memory_chain: RwLock::new(self.memory_chain.read().clone()),
            _phantom: Default::default(),
        }
    }
}

impl<SP, N> BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX> + FullProvider<N>,
    Self: ChangeSetReader + StorageChangeSetReader,
{
    /// Return the last N blocks of state, recreating the [`ExecutionOutcome`].
    ///
    /// If the range is empty, or there are no blocks for the given range, then this returns `None`.
    pub(crate) fn get_state(
        &self,
        range: RangeInclusive<BlockNumber>,
    ) -> ProviderResult<Option<ExecutionOutcome>> {
        if range.is_empty() {
            return Ok(None)
        }
        let start_block_number = *range.start();
        let end_block_number = *range.end();

        // We are not removing block meta as it is used to get block changesets.
        let mut block_bodies = Vec::new();
        for block_num in range.clone() {
            let block_body = self
                .block_body_indices(block_num)?
                .ok_or(ProviderError::BlockBodyIndicesNotFound(block_num))?;
            block_bodies.push((block_num, block_body))
        }

        // get transaction receipts
        let Some(from_transaction_num) = block_bodies.first().map(|body| body.1.first_tx_num())
        else {
            return Ok(None)
        };
        let Some(to_transaction_num) = block_bodies.last().map(|body| body.1.last_tx_num()) else {
            return Ok(None)
        };

        let mut account_changeset = Vec::new();
        for block_num in range.clone() {
            let changeset =
                self.account_block_changeset(block_num)?.into_iter().map(|elem| (block_num, elem));
            account_changeset.extend(changeset);
        }

        let mut storage_changeset = Vec::new();
        for block_num in range {
            let changeset = self.storage_changeset(block_num)?;
            storage_changeset.extend(changeset);
        }

        let (state, reverts) =
            self.populate_bundle_state(account_changeset, storage_changeset, end_block_number)?;

        let mut receipt_iter =
            self.receipts_by_tx_range(from_transaction_num..=to_transaction_num)?.into_iter();

        let mut receipts = Vec::with_capacity(block_bodies.len());
        // loop break if we are at the end of the blocks.
        for (_, block_body) in block_bodies {
            let mut block_receipts = Vec::with_capacity(block_body.tx_count as usize);
            for tx_num in block_body.tx_num_range() {
                let receipt = receipt_iter
                    .next()
                    .ok_or_else(|| ProviderError::ReceiptNotFound(tx_num.into()))?;
                block_receipts.push(Some(receipt));
            }
            receipts.push(block_receipts);
        }

        Ok(Some(ExecutionOutcome::new_init(
            state,
            reverts,
            // We skip new contracts since we never delete them from the database
            Vec::new(),
            receipts.into(),
            start_block_number,
            Vec::new(),
        )))
    }
}

impl<SP, N> BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX> + FullProvider<N>,
{
    /// Create a new provider using only the database, fetching the latest header from
    /// the database to initialize the provider.
    pub(crate) fn new<PF>(storage: PF, state: CanonicalInMemoryState) -> ProviderResult<Self>
    where
        PF: StaticFileProviderFactory + DatabaseProviderFactory<Provider = SP>,
    {
        Ok(Self {
            storage_provider: storage.database_provider_ro()?,
            head_block: state.head_state().expect("should have"), // TODO error
            canonical_state: state,
            memory_chain: RwLock::new(Arc::new(vec![])),
            _phantom: Default::default(),
        })
    }

    // Helper function to convert range bounds
    fn convert_range_bounds<T>(
        &self,
        range: impl RangeBounds<T>,
        end_unbounded: impl FnOnce() -> T,
    ) -> (T, T)
    where
        T: Copy + Add<Output = T> + Sub<Output = T> + From<u8>,
    {
        let start = match range.start_bound() {
            Bound::Included(&n) => n,
            Bound::Excluded(&n) => n + T::from(1u8),
            Bound::Unbounded => T::from(0u8),
        };

        let end = match range.end_bound() {
            Bound::Included(&n) => n,
            Bound::Excluded(&n) => n - T::from(1u8),
            Bound::Unbounded => end_unbounded(),
        };

        (start, end)
    }

    /// Populate a [`BundleStateInit`] and [`RevertsInit`] using cursors over the
    /// [`reth_db::PlainAccountState`] and [`reth_db::PlainStorageState`] tables, based on the given
    /// storage and account changesets.
    fn populate_bundle_state(
        &self,
        account_changeset: Vec<(u64, AccountBeforeTx)>,
        storage_changeset: Vec<(BlockNumberAddress, StorageEntry)>,
        block_range_end: BlockNumber,
    ) -> ProviderResult<(BundleStateInit, RevertsInit)> {
        let mut state: BundleStateInit = HashMap::new();
        let mut reverts: RevertsInit = HashMap::new();
        let state_provider = self.state_by_block_number_or_tag(block_range_end.into())?;

        // add account changeset changes
        for (block_number, account_before) in account_changeset.into_iter().rev() {
            let AccountBeforeTx { info: old_info, address } = account_before;
            match state.entry(address) {
                hash_map::Entry::Vacant(entry) => {
                    let new_info = state_provider.basic_account(address)?;
                    entry.insert((old_info, new_info, HashMap::new()));
                }
                hash_map::Entry::Occupied(mut entry) => {
                    // overwrite old account state.
                    entry.get_mut().0 = old_info;
                }
            }
            // insert old info into reverts.
            reverts.entry(block_number).or_default().entry(address).or_default().0 = Some(old_info);
        }

        // add storage changeset changes
        for (block_and_address, old_storage) in storage_changeset.into_iter().rev() {
            let BlockNumberAddress((block_number, address)) = block_and_address;
            // get account state or insert from plain state.
            let account_state = match state.entry(address) {
                hash_map::Entry::Vacant(entry) => {
                    let present_info = state_provider.basic_account(address)?;
                    entry.insert((present_info, present_info, HashMap::new()))
                }
                hash_map::Entry::Occupied(entry) => entry.into_mut(),
            };

            // match storage.
            match account_state.2.entry(old_storage.key) {
                hash_map::Entry::Vacant(entry) => {
                    let new_storage_value =
                        state_provider.storage(address, old_storage.key)?.unwrap_or_default();
                    entry.insert((old_storage.value, new_storage_value));
                }
                hash_map::Entry::Occupied(mut entry) => {
                    entry.get_mut().0 = old_storage.value;
                }
            };

            reverts
                .entry(block_number)
                .or_default()
                .entry(address)
                .or_default()
                .1
                .push(old_storage);
        }

        Ok((state, reverts))
    }

    /// Fetches a range of data from both in-memory state and persistent storage while a predicate
    /// is met.
    ///
    /// Creates a snapshot of the in-memory chain state and database provider to prevent
    /// inconsistencies. Splits the range into in-memory and storage sections, prioritizing
    /// recent in-memory blocks in case of overlaps.
    ///
    /// * `fetch_db_range` function (`F`) provides access to the database provider, allowing the
    ///   user to retrieve the required items from the database using [`RangeInclusive`].
    /// * `map_block_state_item` function (`G`) provides each block of the range in the in-memory
    ///   state, allowing for selection or filtering for the desired data.
    fn get_in_memory_or_storage_by_block_range_while<T, F, G, P>(
        &self,
        range: impl RangeBounds<BlockNumber>,
        fetch_db_range: F,
        map_block_state_item: G,
        mut predicate: P,
    ) -> ProviderResult<Vec<T>>
    where
        F: FnOnce(&SP, RangeInclusive<BlockNumber>, &mut P) -> ProviderResult<Vec<T>>,
        G: Fn(&BlockState, &mut P) -> Option<T>,
        P: FnMut(&T) -> bool,
    {
        // Each one provides a snapshot at the time of instantiation, but its order matters.
        //
        // If we acquire first the database provider, it's possible that before the in-memory chain
        // snapshot is instantiated, it will flush blocks to disk. This would
        // mean that our database provider would not have access to the flushed blocks (since it's
        // working under an older view), while the in-memory state may have deleted them
        // entirely. Resulting in gaps on the range.
        let mut in_memory_chain = self.head_block.chain().collect::<Vec<_>>();
        let db_provider = &self.storage_provider;

        let (start, end) = self.convert_range_bounds(range, || {
            // the first block is the highest one.
            in_memory_chain
                .first()
                .map(|b| b.number())
                .unwrap_or_else(|| db_provider.last_block_number().unwrap_or_default())
        });

        if start > end {
            return Ok(vec![])
        }

        // Split range into storage_range and in-memory range. If the in-memory range is not
        // necessary drop it early.
        //
        // The last block of `in_memory_chain` is the lowest block number.
        let (in_memory, storage_range) = match in_memory_chain.last().as_ref().map(|b| b.number()) {
            Some(lowest_memory_block) if lowest_memory_block <= end => {
                let highest_memory_block =
                    in_memory_chain.first().as_ref().map(|b| b.number()).expect("qed");

                // Database will for a time overlap with in-memory-chain blocks. In
                // case of a re-org, it can mean that the database blocks are of a forked chain, and
                // so, we should prioritize the in-memory overlapped blocks.
                let in_memory_range =
                    lowest_memory_block.max(start)..=end.min(highest_memory_block);

                // If requested range is in the middle of the in-memory range, remove the necessary
                // lowest blocks
                in_memory_chain.truncate(
                    in_memory_chain
                        .len()
                        .saturating_sub(start.saturating_sub(lowest_memory_block) as usize),
                );

                let storage_range =
                    (lowest_memory_block > start).then(|| start..=lowest_memory_block - 1);

                (Some((in_memory_chain, in_memory_range)), storage_range)
            }
            _ => {
                // Drop the in-memory chain so we don't hold blocks in memory.
                drop(in_memory_chain);

                (None, Some(start..=end))
            }
        };

        let mut items = Vec::with_capacity((end - start + 1) as usize);

        if let Some(storage_range) = storage_range {
            let mut db_items = fetch_db_range(db_provider, storage_range.clone(), &mut predicate)?;
            items.append(&mut db_items);

            // The predicate was not met, if the number of items differs from the expected. So, we
            // return what we have.
            if items.len() as u64 != storage_range.end() - storage_range.start() + 1 {
                return Ok(items)
            }
        }

        if let Some((in_memory_chain, in_memory_range)) = in_memory {
            for (num, block) in in_memory_range.zip(in_memory_chain.into_iter().rev()) {
                debug_assert!(num == block.number());
                if let Some(item) = map_block_state_item(block, &mut predicate) {
                    items.push(item);
                } else {
                    break
                }
            }
        }

        Ok(items)
    }

    /// This uses a given [`BlockState`] to initialize a state provider for that block.
    fn block_state_provider(
        &self,
        state: &BlockState,
    ) -> ProviderResult<MemoryOverlayStateProvider> {
        let anchor_hash = state.anchor().hash;
        let latest_historical = self.storage_provider.history_by_block_hash(anchor_hash)?;
        // TODO (joshie): mv state_provider_from_state to BlockState and/or block_state_provider
        Ok(self.canonical_state.state_provider_from_state(state, latest_historical))
    }

    /// Fetches data from either in-memory state or persistent storage for a range of transactions.
    ///
    /// * `fetch_from_db`: has a [`DatabaseProviderRO`] and the storage specific range.
    /// * `fetch_from_block_state`: has a [`RangeInclusive`] of elements that should be fetched from
    ///   [`BlockState`]. [`RangeInclusive`] is necessary to handle partial look-ups of a block.
    fn get_in_memory_or_storage_by_tx_range<S, M, R>(
        &self,
        range: impl RangeBounds<BlockNumber>,
        fetch_from_db: S,
        fetch_from_block_state: M,
    ) -> ProviderResult<Vec<R>>
    where
        S: FnOnce(&SP, RangeInclusive<TxNumber>) -> ProviderResult<Vec<R>>,
        M: Fn(RangeInclusive<usize>, &Arc<BlockState>) -> ProviderResult<Vec<R>>,
    {
        let in_mem_chain = self.in_memory_chain();
        let provider = &self.storage_provider;

        // Get the last block number stored in the storage which does NOT overlap with in-memory
        // chain.
        let last_database_block_number = in_mem_chain
            .last()
            .map(|b| Ok(b.anchor().number))
            .unwrap_or_else(|| provider.last_block_number())?;

        // Get the next tx number for the last block stored in the storage, which marks the start of
        // the in-memory state.
        let last_block_body_index = provider
            .block_body_indices(last_database_block_number)?
            .ok_or(ProviderError::BlockBodyIndicesNotFound(last_database_block_number))?;
        let mut in_memory_tx_num = last_block_body_index.next_tx_num();

        let (start, end) = self.convert_range_bounds(range, || {
            in_mem_chain
                .iter()
                .map(|b| b.block_ref().block().body.transactions.len() as u64)
                .sum::<u64>() +
                last_block_body_index.last_tx_num()
        });

        if start > end {
            return Ok(vec![])
        }

        let mut tx_range = start..=end;

        // If the range is entirely before the first in-memory transaction number, fetch from
        // storage
        if *tx_range.end() < in_memory_tx_num {
            return fetch_from_db(provider, tx_range);
        }

        let mut items = Vec::with_capacity((tx_range.end() - tx_range.start() + 1) as usize);

        // If the range spans storage and memory, get elements from storage first.
        if *tx_range.start() < in_memory_tx_num {
            // Determine the range that needs to be fetched from storage.
            let db_range = *tx_range.start()..=in_memory_tx_num.saturating_sub(1);

            // Set the remaining transaction range for in-memory
            tx_range = in_memory_tx_num..=*tx_range.end();

            items.extend(fetch_from_db(provider, db_range)?);
        }

        // Iterate from the lowest block to the highest in-memory chain
        for block_state in in_mem_chain.iter().rev() {
            let block_tx_count = block_state.block_ref().block().body.transactions.len();
            let remaining = (tx_range.end() - tx_range.start() + 1) as usize;

            // If the transaction range start is equal or higher than the next block first
            // transaction, advance
            if *tx_range.start() >= in_memory_tx_num + block_tx_count as u64 {
                in_memory_tx_num += block_tx_count as u64;
                continue
            }

            // This should only be more than 0 once, in case of a partial range inside a block.
            let skip = (tx_range.start() - in_memory_tx_num) as usize;

            items.extend(fetch_from_block_state(
                skip..=skip + (remaining.min(block_tx_count - skip) - 1),
                block_state,
            )?);

            in_memory_tx_num += block_tx_count as u64;

            // Break if the range has been fully processed
            if in_memory_tx_num > *tx_range.end() {
                break
            }

            // Set updated range
            tx_range = in_memory_tx_num..=*tx_range.end();
        }

        Ok(items)
    }

    /// Fetches data from either in-memory state or persistent storage by transaction
    /// [`HashOrNumber`].
    fn get_in_memory_or_storage_by_tx<S, M, R>(
        &self,
        id: HashOrNumber,
        fetch_from_db: S,
        fetch_from_block_state: M,
    ) -> ProviderResult<Option<R>>
    where
        S: FnOnce(&SP) -> ProviderResult<Option<R>>,
        M: Fn(usize, TxNumber, &BlockState) -> ProviderResult<Option<R>>,
    {
        // Order of instantiation matters. More information on:
        // `get_in_memory_or_storage_by_block_range_while`.
        let in_mem_chain = self.in_memory_chain();
        let provider = &self.storage_provider;

        // Get the last block number stored in the database which does NOT overlap with in-memory
        // chain.
        let last_database_block_number = in_mem_chain
            .last()
            .map(|b| Ok(b.anchor().number))
            .unwrap_or_else(|| provider.last_block_number())?;

        // Get the next tx number for the last block stored in the database and consider it the
        // first tx number of the in-memory state
        let last_block_body_index = provider
            .block_body_indices(last_database_block_number)?
            .ok_or(ProviderError::BlockBodyIndicesNotFound(last_database_block_number))?;
        let mut in_memory_tx_num = last_block_body_index.next_tx_num();

        // If the transaction number is less than the first in-memory transaction number, make a
        // database lookup
        if let HashOrNumber::Number(id) = id {
            if id < in_memory_tx_num {
                return fetch_from_db(provider)
            }
        }

        // Iterate from the lowest block to the highest
        for block_state in in_mem_chain.iter().rev() {
            let executed_block = block_state.block_ref();
            let block = executed_block.block();

            for tx_index in 0..block.body.transactions.len() {
                match id {
                    HashOrNumber::Hash(tx_hash) => {
                        if tx_hash == block.body.transactions[tx_index].hash() {
                            return fetch_from_block_state(tx_index, in_memory_tx_num, block_state)
                        }
                    }
                    HashOrNumber::Number(id) => {
                        if id == in_memory_tx_num {
                            return fetch_from_block_state(tx_index, in_memory_tx_num, block_state)
                        }
                    }
                }

                in_memory_tx_num += 1;
            }
        }

        // Not found in-memory, so check database.
        if let HashOrNumber::Hash(_) = id {
            return fetch_from_db(provider)
        }

        Ok(None)
    }

    /// Fetches data from either in-memory state or persistent storage by [`BlockHashOrNumber`].
    fn get_in_memory_or_storage_by_block<S, M, R>(
        &self,
        id: BlockHashOrNumber,
        fetch_from_db: S,
        fetch_from_block_state: M,
    ) -> ProviderResult<R>
    where
        S: FnOnce(&SP) -> ProviderResult<R>,
        M: Fn(&BlockState) -> ProviderResult<R>,
    {
        if let Some(block_state) = self.head_block.block_on_chain(id) {
            return fetch_from_block_state(block_state)
        }
        fetch_from_db(&self.storage_provider)
    }
}

impl<SP, N> BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX> + FullProvider<N>,
{
    /// Ensures that the given block number is canonical (synced)
    ///
    /// This is a helper for guarding the `HistoricalStateProvider` against block numbers that are
    /// out of range and would lead to invalid results, mainly during initial sync.
    ///
    /// Verifying the `block_number` would be expensive since we need to lookup sync table
    /// Instead, we ensure that the `block_number` is within the range of the
    /// [`Self::best_block_number`] which is updated when a block is synced.
    #[inline]
    fn ensure_canonical_block(&self, block_number: BlockNumber) -> ProviderResult<()> {
        let latest = self.best_block_number()?;
        if block_number > latest {
            Err(ProviderError::HeaderNotFound(block_number.into()))
        } else {
            Ok(())
        }
    }
}

impl<SP, N> StaticFileProviderFactory for BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX> + StaticFileProviderFactory,
{
    fn static_file_provider(&self) -> StaticFileProvider {
        self.storage_provider.static_file_provider()
    }
}

impl<SP, N> HeaderProvider for BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX> + FullProvider<N>,
{
    fn header(&self, block_hash: &BlockHash) -> ProviderResult<Option<Header>> {
        self.get_in_memory_or_storage_by_block(
            (*block_hash).into(),
            |db_provider| db_provider.header(block_hash),
            |block_state| Ok(Some(block_state.block_ref().block().header.header().clone())),
        )
    }

    fn header_by_number(&self, num: BlockNumber) -> ProviderResult<Option<Header>> {
        self.get_in_memory_or_storage_by_block(
            num.into(),
            |db_provider| db_provider.header_by_number(num),
            |block_state| Ok(Some(block_state.block_ref().block().header.header().clone())),
        )
    }

    fn header_td(&self, hash: &BlockHash) -> ProviderResult<Option<U256>> {
        if let Some(num) = self.block_number(*hash)? {
            self.header_td_by_number(num)
        } else {
            Ok(None)
        }
    }

    fn header_td_by_number(&self, number: BlockNumber) -> ProviderResult<Option<U256>> {
        // TODO(joshie): this needs to search our head.chain() for number
        let number = if self.canonical_state.hash_by_number(number).is_some() {
            // If the block exists in memory, we should return a TD for it.
            //
            // The canonical in memory state should only store post-merge blocks. Post-merge blocks
            // have zero difficulty. This means we can use the total difficulty for the last
            // finalized block number if present (so that we are not affected by reorgs), if not the
            // last number in the database will be used.
            if let Some(last_finalized_num_hash) = self.canonical_state.get_finalized_num_hash() {
                last_finalized_num_hash.number
            } else {
                self.last_block_number()?
            }
        } else {
            // Otherwise, return what we have on disk for the input block
            number
        };
        self.storage_provider.header_td_by_number(number)
    }

    fn headers_range(&self, range: impl RangeBounds<BlockNumber>) -> ProviderResult<Vec<Header>> {
        self.get_in_memory_or_storage_by_block_range_while(
            range,
            |db_provider, range, _| db_provider.headers_range(range),
            |block_state, _| Some(block_state.block_ref().block().header.header().clone()),
            |_| true,
        )
    }

    fn sealed_header(&self, number: BlockNumber) -> ProviderResult<Option<SealedHeader>> {
        self.get_in_memory_or_storage_by_block(
            number.into(),
            |db_provider| db_provider.sealed_header(number),
            |block_state| Ok(Some(block_state.block_ref().block().header.clone())),
        )
    }

    fn sealed_headers_range(
        &self,
        range: impl RangeBounds<BlockNumber>,
    ) -> ProviderResult<Vec<SealedHeader>> {
        self.get_in_memory_or_storage_by_block_range_while(
            range,
            |db_provider, range, _| db_provider.sealed_headers_range(range),
            |block_state, _| Some(block_state.block_ref().block().header.clone()),
            |_| true,
        )
    }

    fn sealed_headers_while(
        &self,
        range: impl RangeBounds<BlockNumber>,
        predicate: impl FnMut(&SealedHeader) -> bool,
    ) -> ProviderResult<Vec<SealedHeader>> {
        self.get_in_memory_or_storage_by_block_range_while(
            range,
            |db_provider, range, predicate| db_provider.sealed_headers_while(range, predicate),
            |block_state, predicate| {
                let header = &block_state.block_ref().block().header;
                predicate(header).then(|| header.clone())
            },
            predicate,
        )
    }
}

impl<SP, N> BlockHashReader for BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX> + FullProvider<N>,
{
    fn block_hash(&self, number: u64) -> ProviderResult<Option<B256>> {
        self.get_in_memory_or_storage_by_block(
            number.into(),
            |db_provider| db_provider.block_hash(number),
            |block_state| Ok(Some(block_state.hash())),
        )
    }

    fn canonical_hashes_range(
        &self,
        start: BlockNumber,
        end: BlockNumber,
    ) -> ProviderResult<Vec<B256>> {
        self.get_in_memory_or_storage_by_block_range_while(
            start..end,
            |db_provider, inclusive_range, _| {
                db_provider
                    .canonical_hashes_range(*inclusive_range.start(), *inclusive_range.end() + 1)
            },
            |block_state, _| Some(block_state.hash()),
            |_| true,
        )
    }
}

impl<SP, N> BlockNumReader for BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX> + FullProvider<N>,
{
    fn chain_info(&self) -> ProviderResult<ChainInfo> {
        Ok(self.canonical_state.chain_info())
    }

    fn best_block_number(&self) -> ProviderResult<BlockNumber> {
        // TODO(joshie): self.head?
        Ok(self.canonical_state.get_canonical_block_number())
    }

    fn last_block_number(&self) -> ProviderResult<BlockNumber> {
        // TODO(joshie): self.head?
        self.storage_provider.last_block_number()
    }

    fn block_number(&self, hash: B256) -> ProviderResult<Option<BlockNumber>> {
        self.get_in_memory_or_storage_by_block(
            hash.into(),
            |db_provider| db_provider.block_number(hash),
            |block_state| Ok(Some(block_state.number())),
        )
    }
}

impl<SP, N> BlockIdReader for BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX> + FullProvider<N>,
{
    fn pending_block_num_hash(&self) -> ProviderResult<Option<BlockNumHash>> {
        Ok(self.canonical_state.pending_block_num_hash())
    }

    fn safe_block_num_hash(&self) -> ProviderResult<Option<BlockNumHash>> {
        Ok(self.canonical_state.get_safe_num_hash())
    }

    fn finalized_block_num_hash(&self) -> ProviderResult<Option<BlockNumHash>> {
        Ok(self.canonical_state.get_finalized_num_hash())
    }
}

impl<SP, N> BlockReader for BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX> + FullProvider<N>,
{
    fn find_block_by_hash(&self, hash: B256, source: BlockSource) -> ProviderResult<Option<Block>> {
        match source {
            BlockSource::Any | BlockSource::Canonical => {
                // Note: it's fine to return the unsealed block because the caller already has
                // the hash
                self.get_in_memory_or_storage_by_block(
                    hash.into(),
                    |db_provider| db_provider.find_block_by_hash(hash, source),
                    |block_state| Ok(Some(block_state.block_ref().block().clone().unseal())),
                )
            }
            BlockSource::Pending => {
                Ok(self.canonical_state.pending_block().map(|block| block.unseal()))
            }
        }
    }

    fn block(&self, id: BlockHashOrNumber) -> ProviderResult<Option<Block>> {
        self.get_in_memory_or_storage_by_block(
            id,
            |db_provider| db_provider.block(id),
            |block_state| Ok(Some(block_state.block_ref().block().clone().unseal())),
        )
    }

    fn pending_block(&self) -> ProviderResult<Option<SealedBlock>> {
        Ok(self.canonical_state.pending_block())
    }

    fn pending_block_with_senders(&self) -> ProviderResult<Option<SealedBlockWithSenders>> {
        Ok(self.canonical_state.pending_block_with_senders())
    }

    fn pending_block_and_receipts(&self) -> ProviderResult<Option<(SealedBlock, Vec<Receipt>)>> {
        Ok(self.canonical_state.pending_block_and_receipts())
    }

    fn ommers(&self, id: BlockHashOrNumber) -> ProviderResult<Option<Vec<Header>>> {
        self.get_in_memory_or_storage_by_block(
            id,
            |db_provider| db_provider.ommers(id),
            |block_state| {
                if self.chain_spec().final_paris_total_difficulty(block_state.number()).is_some() {
                    return Ok(Some(Vec::new()))
                }

                Ok(Some(block_state.block_ref().block().body.ommers.clone()))
            },
        )
    }

    fn block_body_indices(
        &self,
        number: BlockNumber,
    ) -> ProviderResult<Option<StoredBlockBodyIndices>> {
        self.get_in_memory_or_storage_by_block(
            number.into(),
            |db_provider| db_provider.block_body_indices(number),
            |block_state| {
                // Find the last block indices on database
                let last_storage_block_number = block_state.anchor().number;
                let mut stored_indices = self
                    .storage_provider
                    .block_body_indices(last_storage_block_number)?
                    .ok_or(ProviderError::BlockBodyIndicesNotFound(last_storage_block_number))?;

                // Prepare our block indices
                stored_indices.first_tx_num = stored_indices.next_tx_num();
                stored_indices.tx_count = 0;

                // Iterate from the lowest block in memory until our target block
                for state in block_state.chain().collect::<Vec<_>>().into_iter().rev() {
                    let block_tx_count = state.block_ref().block.body.transactions.len() as u64;
                    if state.block_ref().block().number == number {
                        stored_indices.tx_count = block_tx_count;
                    } else {
                        stored_indices.first_tx_num += block_tx_count;
                    }
                }

                Ok(Some(stored_indices))
            },
        )
    }

    /// Returns the block with senders with matching number or hash from database.
    ///
    /// **NOTE: If [`TransactionVariant::NoHash`] is provided then the transactions have invalid
    /// hashes, since they would need to be calculated on the spot, and we want fast querying.**
    ///
    /// Returns `None` if block is not found.
    fn block_with_senders(
        &self,
        id: BlockHashOrNumber,
        transaction_kind: TransactionVariant,
    ) -> ProviderResult<Option<BlockWithSenders>> {
        self.get_in_memory_or_storage_by_block(
            id,
            |db_provider| db_provider.block_with_senders(id, transaction_kind),
            |block_state| Ok(Some(block_state.block_with_senders())),
        )
    }

    fn sealed_block_with_senders(
        &self,
        id: BlockHashOrNumber,
        transaction_kind: TransactionVariant,
    ) -> ProviderResult<Option<SealedBlockWithSenders>> {
        self.get_in_memory_or_storage_by_block(
            id,
            |db_provider| db_provider.sealed_block_with_senders(id, transaction_kind),
            |block_state| Ok(Some(block_state.sealed_block_with_senders())),
        )
    }

    fn block_range(&self, range: RangeInclusive<BlockNumber>) -> ProviderResult<Vec<Block>> {
        self.get_in_memory_or_storage_by_block_range_while(
            range,
            |db_provider, range, _| db_provider.block_range(range),
            |block_state, _| Some(block_state.block_ref().block().clone().unseal()),
            |_| true,
        )
    }

    fn block_with_senders_range(
        &self,
        range: RangeInclusive<BlockNumber>,
    ) -> ProviderResult<Vec<BlockWithSenders>> {
        self.get_in_memory_or_storage_by_block_range_while(
            range,
            |db_provider, range, _| db_provider.block_with_senders_range(range),
            |block_state, _| Some(block_state.block_with_senders()),
            |_| true,
        )
    }

    fn sealed_block_with_senders_range(
        &self,
        range: RangeInclusive<BlockNumber>,
    ) -> ProviderResult<Vec<SealedBlockWithSenders>> {
        self.get_in_memory_or_storage_by_block_range_while(
            range,
            |db_provider, range, _| db_provider.sealed_block_with_senders_range(range),
            |block_state, _| Some(block_state.sealed_block_with_senders()),
            |_| true,
        )
    }
}

impl<SP, N> TransactionsProvider for BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX> + FullProvider<N>,
{
    fn transaction_id(&self, tx_hash: TxHash) -> ProviderResult<Option<TxNumber>> {
        self.get_in_memory_or_storage_by_tx(
            tx_hash.into(),
            |db_provider| db_provider.transaction_id(tx_hash),
            |_, tx_number, _| Ok(Some(tx_number)),
        )
    }

    fn transaction_by_id(&self, id: TxNumber) -> ProviderResult<Option<TransactionSigned>> {
        self.get_in_memory_or_storage_by_tx(
            id.into(),
            |provider| provider.transaction_by_id(id),
            |tx_index, _, block_state| {
                Ok(block_state.block_ref().block().body.transactions.get(tx_index).cloned())
            },
        )
    }

    fn transaction_by_id_no_hash(
        &self,
        id: TxNumber,
    ) -> ProviderResult<Option<TransactionSignedNoHash>> {
        self.get_in_memory_or_storage_by_tx(
            id.into(),
            |provider| provider.transaction_by_id_no_hash(id),
            |tx_index, _, block_state| {
                Ok(block_state
                    .block_ref()
                    .block()
                    .body
                    .transactions
                    .get(tx_index)
                    .cloned()
                    .map(Into::into))
            },
        )
    }

    fn transaction_by_hash(&self, hash: TxHash) -> ProviderResult<Option<TransactionSigned>> {
        if let Some(tx) = self.head_block.transaction_on_chain(hash) {
            return Ok(Some(tx))
        }

        self.storage_provider.transaction_by_hash(hash)
    }

    fn transaction_by_hash_with_meta(
        &self,
        tx_hash: TxHash,
    ) -> ProviderResult<Option<(TransactionSigned, TransactionMeta)>> {
        if let Some((tx, meta)) = self.head_block.transaction_meta_on_chain(tx_hash) {
            return Ok(Some((tx, meta)))
        }

        self.storage_provider.transaction_by_hash_with_meta(tx_hash)
    }

    fn transaction_block(&self, id: TxNumber) -> ProviderResult<Option<BlockNumber>> {
        self.get_in_memory_or_storage_by_tx(
            id.into(),
            |provider| provider.transaction_block(id),
            |_, _, block_state| Ok(Some(block_state.block_ref().block().number)),
        )
    }

    fn transactions_by_block(
        &self,
        id: BlockHashOrNumber,
    ) -> ProviderResult<Option<Vec<TransactionSigned>>> {
        self.get_in_memory_or_storage_by_block(
            id,
            |provider| provider.transactions_by_block(id),
            |block_state| Ok(Some(block_state.block_ref().block().body.transactions.clone())),
        )
    }

    fn transactions_by_block_range(
        &self,
        range: impl RangeBounds<BlockNumber>,
    ) -> ProviderResult<Vec<Vec<TransactionSigned>>> {
        self.get_in_memory_or_storage_by_block_range_while(
            range,
            |db_provider, range, _| db_provider.transactions_by_block_range(range),
            |block_state, _| Some(block_state.block_ref().block().body.transactions.clone()),
            |_| true,
        )
    }

    fn transactions_by_tx_range(
        &self,
        range: impl RangeBounds<TxNumber>,
    ) -> ProviderResult<Vec<TransactionSignedNoHash>> {
        self.get_in_memory_or_storage_by_tx_range(
            range,
            |db_provider, db_range| db_provider.transactions_by_tx_range(db_range),
            |index_range, block_state| {
                Ok(block_state.block_ref().block().body.transactions[index_range]
                    .iter()
                    .cloned()
                    .map(Into::into)
                    .collect())
            },
        )
    }

    fn senders_by_tx_range(
        &self,
        range: impl RangeBounds<TxNumber>,
    ) -> ProviderResult<Vec<Address>> {
        self.get_in_memory_or_storage_by_tx_range(
            range,
            |db_provider, db_range| db_provider.senders_by_tx_range(db_range),
            |index_range, block_state| Ok(block_state.block_ref().senders[index_range].to_vec()),
        )
    }

    fn transaction_sender(&self, id: TxNumber) -> ProviderResult<Option<Address>> {
        self.get_in_memory_or_storage_by_tx(
            id.into(),
            |provider| provider.transaction_sender(id),
            |tx_index, _, block_state| Ok(block_state.block_ref().senders.get(tx_index).copied()),
        )
    }
}

impl<SP, N> ReceiptProvider for BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX> + FullProvider<N>,
{
    fn receipt(&self, id: TxNumber) -> ProviderResult<Option<Receipt>> {
        self.get_in_memory_or_storage_by_tx(
            id.into(),
            |provider| provider.receipt(id),
            |tx_index, _, block_state| {
                Ok(block_state.executed_block_receipts().get(tx_index).cloned())
            },
        )
    }

    fn receipt_by_hash(&self, hash: TxHash) -> ProviderResult<Option<Receipt>> {
        for block_state in self.head_block.chain() {
            let executed_block = block_state.block_ref();
            let block = executed_block.block();
            let receipts = block_state.executed_block_receipts();

            // assuming 1:1 correspondence between transactions and receipts
            debug_assert_eq!(
                block.body.transactions.len(),
                receipts.len(),
                "Mismatch between transaction and receipt count"
            );

            if let Some(tx_index) = block.body.transactions.iter().position(|tx| tx.hash() == hash)
            {
                // safe to use tx_index for receipts due to 1:1 correspondence
                return Ok(receipts.get(tx_index).cloned());
            }
        }

        self.storage_provider.receipt_by_hash(hash)
    }

    fn receipts_by_block(&self, block: BlockHashOrNumber) -> ProviderResult<Option<Vec<Receipt>>> {
        self.get_in_memory_or_storage_by_block(
            block,
            |db_provider| db_provider.receipts_by_block(block),
            |block_state| Ok(Some(block_state.executed_block_receipts())),
        )
    }

    fn receipts_by_tx_range(
        &self,
        range: impl RangeBounds<TxNumber>,
    ) -> ProviderResult<Vec<Receipt>> {
        self.get_in_memory_or_storage_by_tx_range(
            range,
            |db_provider, db_range| db_provider.receipts_by_tx_range(db_range),
            |index_range, block_state| {
                Ok(block_state.executed_block_receipts().drain(index_range).collect())
            },
        )
    }
}

impl<SP, N> ReceiptProviderIdExt for BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX> + FullProvider<N>,
{
    fn receipts_by_block_id(&self, block: BlockId) -> ProviderResult<Option<Vec<Receipt>>> {
        match block {
            BlockId::Hash(rpc_block_hash) => {
                let mut receipts = self.receipts_by_block(rpc_block_hash.block_hash.into())?;
                if receipts.is_none() && !rpc_block_hash.require_canonical.unwrap_or(false) {
                    let block_state = self
                        .canonical_state
                        .state_by_hash(rpc_block_hash.block_hash)
                        .ok_or(ProviderError::StateForHashNotFound(rpc_block_hash.block_hash))?;
                    receipts = Some(block_state.executed_block_receipts());
                }
                Ok(receipts)
            }
            BlockId::Number(num_tag) => match num_tag {
                BlockNumberOrTag::Pending => Ok(self
                    .canonical_state
                    .pending_state()
                    .map(|block_state| block_state.executed_block_receipts())),
                _ => {
                    if let Some(num) = self.convert_block_number(num_tag)? {
                        self.receipts_by_block(num.into())
                    } else {
                        Ok(None)
                    }
                }
            },
        }
    }
}

impl<SP, N> WithdrawalsProvider for BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX> + FullProvider<N>,
{
    fn withdrawals_by_block(
        &self,
        id: BlockHashOrNumber,
        timestamp: u64,
    ) -> ProviderResult<Option<Withdrawals>> {
        if !self.chain_spec().is_shanghai_active_at_timestamp(timestamp) {
            return Ok(None)
        }

        self.get_in_memory_or_storage_by_block(
            id,
            |db_provider| db_provider.withdrawals_by_block(id, timestamp),
            |block_state| Ok(block_state.block_ref().block().body.withdrawals.clone()),
        )
    }

    fn latest_withdrawal(&self) -> ProviderResult<Option<Withdrawal>> {
        let best_block_num = self.best_block_number()?;

        self.get_in_memory_or_storage_by_block(
            best_block_num.into(),
            |db_provider| db_provider.latest_withdrawal(),
            |block_state| {
                Ok(block_state
                    .block_ref()
                    .block()
                    .body
                    .withdrawals
                    .clone()
                    .and_then(|mut w| w.pop()))
            },
        )
    }
}

impl<SP, N> RequestsProvider for BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX> + FullProvider<N>,
{
    fn requests_by_block(
        &self,
        id: BlockHashOrNumber,
        timestamp: u64,
    ) -> ProviderResult<Option<reth_primitives::Requests>> {
        if !self.chain_spec().is_prague_active_at_timestamp(timestamp) {
            return Ok(None)
        }

        self.get_in_memory_or_storage_by_block(
            id,
            |db_provider| db_provider.requests_by_block(id, timestamp),
            |block_state| Ok(block_state.block_ref().block().body.requests.clone()),
        )
    }
}

impl<SP, N> StageCheckpointReader for BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX> + FullProvider<N>,
{
    fn get_stage_checkpoint(&self, id: StageId) -> ProviderResult<Option<StageCheckpoint>> {
        self.storage_provider.get_stage_checkpoint(id)
    }

    fn get_stage_checkpoint_progress(&self, id: StageId) -> ProviderResult<Option<Vec<u8>>> {
        self.storage_provider.get_stage_checkpoint_progress(id)
    }

    fn get_all_checkpoints(&self) -> ProviderResult<Vec<(String, StageCheckpoint)>> {
        self.storage_provider.get_all_checkpoints()
    }
}

impl<SP, N> EvmEnvProvider for BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX> + FullProvider<N>,
{
    fn fill_env_at<EvmConfig>(
        &self,
        cfg: &mut CfgEnvWithHandlerCfg,
        block_env: &mut BlockEnv,
        at: BlockHashOrNumber,
        evm_config: EvmConfig,
    ) -> ProviderResult<()>
    where
        EvmConfig: ConfigureEvmEnv<Header = Header>,
    {
        let hash = self.convert_number(at)?.ok_or(ProviderError::HeaderNotFound(at))?;
        let header = self.header(&hash)?.ok_or(ProviderError::HeaderNotFound(at))?;
        self.fill_env_with_header(cfg, block_env, &header, evm_config)
    }

    fn fill_env_with_header<EvmConfig>(
        &self,
        cfg: &mut CfgEnvWithHandlerCfg,
        block_env: &mut BlockEnv,
        header: &Header,
        evm_config: EvmConfig,
    ) -> ProviderResult<()>
    where
        EvmConfig: ConfigureEvmEnv<Header = Header>,
    {
        let total_difficulty = self
            .header_td_by_number(header.number)?
            .ok_or_else(|| ProviderError::HeaderNotFound(header.number.into()))?;
        evm_config.fill_cfg_and_block_env(cfg, block_env, header, total_difficulty);
        Ok(())
    }

    fn fill_cfg_env_at<EvmConfig>(
        &self,
        cfg: &mut CfgEnvWithHandlerCfg,
        at: BlockHashOrNumber,
        evm_config: EvmConfig,
    ) -> ProviderResult<()>
    where
        EvmConfig: ConfigureEvmEnv<Header = Header>,
    {
        let hash = self.convert_number(at)?.ok_or(ProviderError::HeaderNotFound(at))?;
        let header = self.header(&hash)?.ok_or(ProviderError::HeaderNotFound(at))?;
        self.fill_cfg_env_with_header(cfg, &header, evm_config)
    }

    fn fill_cfg_env_with_header<EvmConfig>(
        &self,
        cfg: &mut CfgEnvWithHandlerCfg,
        header: &Header,
        evm_config: EvmConfig,
    ) -> ProviderResult<()>
    where
        EvmConfig: ConfigureEvmEnv<Header = Header>,
    {
        let total_difficulty = self
            .header_td_by_number(header.number)?
            .ok_or_else(|| ProviderError::HeaderNotFound(header.number.into()))?;
        evm_config.fill_cfg_env(cfg, header, total_difficulty);
        Ok(())
    }
}

impl<SP, N> PruneCheckpointReader for BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX>
        + FullProvider<N>
        + PruneCheckpointReader,
{
    fn get_prune_checkpoint(
        &self,
        segment: PruneSegment,
    ) -> ProviderResult<Option<PruneCheckpoint>> {
        self.storage_provider.get_prune_checkpoint(segment)
    }

    fn get_prune_checkpoints(&self) -> ProviderResult<Vec<(PruneSegment, PruneCheckpoint)>> {
        self.storage_provider.get_prune_checkpoints()
    }
}

impl<SP, N> ChainSpecProvider for BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX> + FullProvider<N>,
{
    type ChainSpec = N::ChainSpec;

    fn chain_spec(&self) -> Arc<N::ChainSpec> {
        self.storage_provider.chain_spec()
    }
}

impl<SP, N> StateProviderFactory for BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX> + FullProvider<N>,
{
    /// Storage provider for latest block
    fn latest(&self) -> ProviderResult<StateProviderBox> {
        trace!(target: "providers::blockchain", "Getting latest block state provider");
        Ok(self.block_state_provider(&self.head_block)?.boxed())
    }

    fn history_by_block_number(
        &self,
        block_number: BlockNumber,
    ) -> ProviderResult<StateProviderBox> {
        trace!(target: "providers::blockchain", ?block_number, "Getting history by block number");
        self.ensure_canonical_block(block_number)?;
        let hash = self
            .block_hash(block_number)?
            .ok_or_else(|| ProviderError::HeaderNotFound(block_number.into()))?;
        self.history_by_block_hash(hash)
    }

    fn history_by_block_hash(&self, block_hash: BlockHash) -> ProviderResult<StateProviderBox> {
        trace!(target: "providers::blockchain", ?block_hash, "Getting history by block hash");

        self.get_in_memory_or_storage_by_block(
            block_hash.into(),
            |_| {
                // TODO(joshie): port history_by_block_hash to DatabaseProvider and use db_provider
                self.storage_provider.history_by_block_hash(block_hash)
            },
            |block_state| {
                let state_provider = self.block_state_provider(block_state)?;
                Ok(Box::new(state_provider))
            },
        )
    }

    fn state_by_block_hash(&self, hash: BlockHash) -> ProviderResult<StateProviderBox> {
        trace!(target: "providers::blockchain", ?hash, "Getting state by block hash");
        if let Ok(state) = self.history_by_block_hash(hash) {
            // This could be tracked by a historical block
            Ok(state)
        } else if let Ok(Some(pending)) = self.pending_state_by_hash(hash) {
            // .. or this could be the pending state
            Ok(pending)
        } else {
            // if we couldn't find it anywhere, then we should return an error
            Err(ProviderError::StateForHashNotFound(hash))
        }
    }

    /// Returns the state provider for pending state.
    ///
    /// If there's no pending block available then the latest state provider is returned:
    /// [`Self::latest`]
    fn pending(&self) -> ProviderResult<StateProviderBox> {
        trace!(target: "providers::blockchain", "Getting provider for pending state");

        if let Some(pending) = self.canonical_state.pending_state() {
            // we have a pending block
            return Ok(Box::new(self.block_state_provider(&pending)?));
        }

        // fallback to latest state if the pending block is not available
        self.latest()
    }

    fn pending_state_by_hash(&self, block_hash: B256) -> ProviderResult<Option<StateProviderBox>> {
        if let Some(pending) = self.canonical_state.pending_state() {
            if pending.hash() == block_hash {
                return Ok(Some(Box::new(self.block_state_provider(&pending)?)));
            }
        }
        Ok(None)
    }

    /// Returns a [`StateProviderBox`] indexed by the given block number or tag.
    fn state_by_block_number_or_tag(
        &self,
        number_or_tag: BlockNumberOrTag,
    ) -> ProviderResult<StateProviderBox> {
        match number_or_tag {
            BlockNumberOrTag::Latest => self.latest(),
            BlockNumberOrTag::Finalized => {
                // we can only get the finalized state by hash, not by num
                let hash =
                    self.finalized_block_hash()?.ok_or(ProviderError::FinalizedBlockNotFound)?;
                self.state_by_block_hash(hash)
            }
            BlockNumberOrTag::Safe => {
                // we can only get the safe state by hash, not by num
                let hash = self.safe_block_hash()?.ok_or(ProviderError::SafeBlockNotFound)?;
                self.state_by_block_hash(hash)
            }
            BlockNumberOrTag::Earliest => self.history_by_block_number(0),
            BlockNumberOrTag::Pending => self.pending(),
            BlockNumberOrTag::Number(num) => {
                let hash = self
                    .block_hash(num)?
                    .ok_or_else(|| ProviderError::HeaderNotFound(num.into()))?;
                self.state_by_block_hash(hash)
            }
        }
    }
}

impl<SP, N> CanonChainTracker for BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX> + FullProvider<N>,
{
    fn on_forkchoice_update_received(&self, _update: &ForkchoiceState) {
        // update timestamp
        self.canonical_state.on_forkchoice_update_received();
    }

    fn last_received_update_timestamp(&self) -> Option<Instant> {
        self.canonical_state.last_received_update_timestamp()
    }

    fn on_transition_configuration_exchanged(&self) {
        self.canonical_state.on_transition_configuration_exchanged();
    }

    fn last_exchanged_transition_configuration_timestamp(&self) -> Option<Instant> {
        self.canonical_state.last_exchanged_transition_configuration_timestamp()
    }

    fn set_canonical_head(&self, header: SealedHeader) {
        self.canonical_state.set_canonical_head(header);
    }

    fn set_safe(&self, header: SealedHeader) {
        self.canonical_state.set_safe(header);
    }

    fn set_finalized(&self, header: SealedHeader) {
        self.canonical_state.set_finalized(header);
    }
}

impl<SP, N> BlockReaderIdExt for BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX> + FullProvider<N>,
{
    fn block_by_id(&self, id: BlockId) -> ProviderResult<Option<Block>> {
        match id {
            BlockId::Number(num) => self.block_by_number_or_tag(num),
            BlockId::Hash(hash) => {
                // TODO: should we only apply this for the RPCs that are listed in EIP-1898?
                // so not at the provider level?
                // if we decide to do this at a higher level, then we can make this an automatic
                // trait impl
                if Some(true) == hash.require_canonical {
                    // check the database, canonical blocks are only stored in the database
                    self.find_block_by_hash(hash.block_hash, BlockSource::Canonical)
                } else {
                    self.block_by_hash(hash.block_hash)
                }
            }
        }
    }

    fn header_by_number_or_tag(&self, id: BlockNumberOrTag) -> ProviderResult<Option<Header>> {
        Ok(match id {
            BlockNumberOrTag::Latest => Some(self.canonical_state.get_canonical_head().unseal()),
            BlockNumberOrTag::Finalized => {
                self.canonical_state.get_finalized_header().map(|h| h.unseal())
            }
            BlockNumberOrTag::Safe => self.canonical_state.get_safe_header().map(|h| h.unseal()),
            BlockNumberOrTag::Earliest => self.header_by_number(0)?,
            BlockNumberOrTag::Pending => self.canonical_state.pending_header(),

            BlockNumberOrTag::Number(num) => self.header_by_number(num)?,
        })
    }

    fn sealed_header_by_number_or_tag(
        &self,
        id: BlockNumberOrTag,
    ) -> ProviderResult<Option<SealedHeader>> {
        match id {
            BlockNumberOrTag::Latest => Ok(Some(self.canonical_state.get_canonical_head())),
            BlockNumberOrTag::Finalized => Ok(self.canonical_state.get_finalized_header()),
            BlockNumberOrTag::Safe => Ok(self.canonical_state.get_safe_header()),
            BlockNumberOrTag::Earliest => self.header_by_number(0)?.map_or_else(
                || Ok(None),
                |h| {
                    let sealed = h.seal_slow();
                    let (header, seal) = sealed.into_parts();
                    Ok(Some(SealedHeader::new(header, seal)))
                },
            ),
            BlockNumberOrTag::Pending => Ok(self.canonical_state.pending_sealed_header()),
            BlockNumberOrTag::Number(num) => self.header_by_number(num)?.map_or_else(
                || Ok(None),
                |h| {
                    let sealed = h.seal_slow();
                    let (header, seal) = sealed.into_parts();
                    Ok(Some(SealedHeader::new(header, seal)))
                },
            ),
        }
    }

    fn sealed_header_by_id(&self, id: BlockId) -> ProviderResult<Option<SealedHeader>> {
        Ok(match id {
            BlockId::Number(num) => self.sealed_header_by_number_or_tag(num)?,
            BlockId::Hash(hash) => self.header(&hash.block_hash)?.map(|h| {
                let sealed = h.seal_slow();
                let (header, seal) = sealed.into_parts();
                SealedHeader::new(header, seal)
            }),
        })
    }

    fn header_by_id(&self, id: BlockId) -> ProviderResult<Option<Header>> {
        Ok(match id {
            BlockId::Number(num) => self.header_by_number_or_tag(num)?,
            BlockId::Hash(hash) => self.header(&hash.block_hash)?,
        })
    }

    fn ommers_by_id(&self, id: BlockId) -> ProviderResult<Option<Vec<Header>>> {
        match id {
            BlockId::Number(num) => self.ommers_by_number_or_tag(num),
            BlockId::Hash(hash) => {
                // TODO: EIP-1898 question, see above
                // here it is not handled
                self.ommers(BlockHashOrNumber::Hash(hash.block_hash))
            }
        }
    }
}

impl<SP, N> CanonStateSubscriptions for BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX> + FullProvider<N>,
{
    fn subscribe_to_canonical_state(&self) -> CanonStateNotifications {
        self.canonical_state.subscribe_canon_state()
    }
}

impl<SP, N> ForkChoiceSubscriptions for BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX> + FullProvider<N>,
{
    fn subscribe_safe_block(&self) -> ForkChoiceNotifications {
        let receiver = self.canonical_state.subscribe_safe_block();
        ForkChoiceNotifications(receiver)
    }

    fn subscribe_finalized_block(&self) -> ForkChoiceNotifications {
        let receiver = self.canonical_state.subscribe_finalized_block();
        ForkChoiceNotifications(receiver)
    }
}

impl<SP, N> StorageChangeSetReader for BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX>
        + FullProvider<N>
        + PruneCheckpointReader
        + StorageChangeSetReader,
{
    fn storage_changeset(
        &self,
        block_number: BlockNumber,
    ) -> ProviderResult<Vec<(BlockNumberAddress, StorageEntry)>> {
        if let Some(state) = self.head_block.block_on_chain(block_number.into()) {
            let changesets = state
                .block()
                .execution_output
                .bundle
                .reverts
                .clone()
                .into_plain_state_reverts()
                .storage
                .into_iter()
                .flatten()
                .flat_map(|revert: PlainStorageRevert| {
                    revert.storage_revert.into_iter().map(move |(key, value)| {
                        (
                            BlockNumberAddress((block_number, revert.address)),
                            StorageEntry { key: key.into(), value: value.to_previous_value() },
                        )
                    })
                })
                .collect();
            Ok(changesets)
        } else {
            // Perform checks on whether or not changesets exist for the block.

            // No prune checkpoint means history should exist and we should `unwrap_or(true)`
            let storage_history_exists = self
                .storage_provider
                .get_prune_checkpoint(PruneSegment::StorageHistory)?
                .and_then(|checkpoint| {
                    // return true if the block number is ahead of the prune checkpoint.
                    //
                    // The checkpoint stores the highest pruned block number, so we should make
                    // sure the block_number is strictly greater.
                    checkpoint.block_number.map(|checkpoint| block_number > checkpoint)
                })
                .unwrap_or(true);

            if !storage_history_exists {
                return Err(ProviderError::StateAtBlockPruned(block_number))
            }

            self.storage_provider.storage_changeset(block_number)
        }
    }
}

impl<SP, N> ChangeSetReader for BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX>
        + FullProvider<N>
        + PruneCheckpointReader,
{
    fn account_block_changeset(
        &self,
        block_number: BlockNumber,
    ) -> ProviderResult<Vec<AccountBeforeTx>> {
        if let Some(state) = self.head_block.block_on_chain(block_number.into()) {
            let changesets = state
                .block_ref()
                .execution_output
                .bundle
                .reverts
                .clone()
                .into_plain_state_reverts()
                .accounts
                .into_iter()
                .flatten()
                .map(|(address, info)| AccountBeforeTx { address, info: info.map(Into::into) })
                .collect();
            Ok(changesets)
        } else {
            // Perform checks on whether or not changesets exist for the block.

            // No prune checkpoint means history should exist and we should `unwrap_or(true)`
            let account_history_exists = self
                .storage_provider
                .get_prune_checkpoint(PruneSegment::AccountHistory)?
                .and_then(|checkpoint| {
                    // return true if the block number is ahead of the prune checkpoint.
                    //
                    // The checkpoint stores the highest pruned block number, so we should make
                    // sure the block_number is strictly greater.
                    checkpoint.block_number.map(|checkpoint| block_number > checkpoint)
                })
                .unwrap_or(true);

            if !account_history_exists {
                return Err(ProviderError::StateAtBlockPruned(block_number))
            }

            self.storage_provider.account_block_changeset(block_number)
        }
    }
}

impl<SP, N> AccountReader for BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX> + FullProvider<N>,
{
    /// Get basic account information.
    fn basic_account(&self, address: Address) -> ProviderResult<Option<Account>> {
        // use latest state provider
        let state_provider = self.latest()?;
        state_provider.basic_account(address)
    }
}

impl<SP, N> StateReader for BlockchainProvider3<SP, N>
where
    N: ProviderNodeTypes,
    SP: DBProvider<Tx = <<N as NodeTypesWithDB>::DB as Database>::TX> + FullProvider<N>,
    Self: ChangeSetReader + StorageChangeSetReader,
{
    /// Re-constructs the [`ExecutionOutcome`] from in-memory and database state, if necessary.
    ///
    /// If data for the block does not exist, this will return [`None`].
    ///
    /// NOTE: This cannot be called safely in a loop outside of the blockchain tree thread. This is
    /// because the [`CanonicalInMemoryState`] could change during a reorg, causing results to be
    /// inconsistent. Currently this can safely be called within the blockchain tree thread,
    /// because the tree thread is responsible for modifying the [`CanonicalInMemoryState`] in the
    /// first place.
    fn get_state(&self, block: BlockNumber) -> ProviderResult<Option<ExecutionOutcome>> {
        if let Some(state) = self.head_block.block_on_chain(block.into()) {
            let state = state.block_ref().execution_outcome().clone();
            Ok(Some(state))
        } else {
            self.get_state(block..=block)
        }
    }
}
