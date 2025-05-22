//! Helpers for setting up parts of the node.

use std::sync::Arc;

use crate::BlockTy;
use alloy_primitives::{BlockNumber, B256};
use reth_config::{config::StageConfig, PruneConfig};
use reth_consensus::{ConsensusError, FullConsensus};
use reth_evm::ConfigureEvm;
use reth_exex::ExExManagerHandle;
use reth_network_p2p::{
    bodies::downloader::BodyDownloader, headers::downloader::HeaderDownloader, BlockClient,
};
use reth_node_api::HeaderTy;
use reth_provider::{providers::ProviderNodeTypes, ProviderFactory};
use reth_stages::{prelude::DefaultStages, stages::ExecutionStage, Pipeline, StageSet};
use reth_static_file::StaticFileProducer;
use reth_tasks::TaskExecutor;
use reth_tracing::tracing::debug;
use tokio::sync::watch;

/// Constructs a [Pipeline] that's wired to the network
#[expect(clippy::too_many_arguments)]
pub fn build_networked_pipeline<N, Client, Evm>(
    _config: &StageConfig,
    _client: Client,
    _consensus: Arc<dyn FullConsensus<N::Primitives, Error = ConsensusError>>,
    _provider_factory: ProviderFactory<N>,
    _task_executor: &TaskExecutor,
    _metrics_tx: reth_stages::MetricEventsSender,
    _prune_config: Option<PruneConfig>,
    _max_block: Option<BlockNumber>,
    _static_file_producer: StaticFileProducer<ProviderFactory<N>>,
    _evm_config: Evm,
    _exex_manager_handle: ExExManagerHandle<N::Primitives>,
) -> eyre::Result<Pipeline<N>>
where
    N: ProviderNodeTypes,
    Client: BlockClient<Block = BlockTy<N>> + 'static,
    Evm: ConfigureEvm<Primitives = N::Primitives> + 'static,
{
    unimplemented!("Patched out.")
}

/// Builds the [Pipeline] with the given [`ProviderFactory`] and downloaders.
#[expect(clippy::too_many_arguments)]
pub fn build_pipeline<N, H, B, Evm>(
    provider_factory: ProviderFactory<N>,
    stage_config: &StageConfig,
    header_downloader: H,
    body_downloader: B,
    consensus: Arc<dyn FullConsensus<N::Primitives, Error = ConsensusError>>,
    max_block: Option<u64>,
    metrics_tx: reth_stages::MetricEventsSender,
    prune_config: Option<PruneConfig>,
    static_file_producer: StaticFileProducer<ProviderFactory<N>>,
    evm_config: Evm,
    exex_manager_handle: ExExManagerHandle<N::Primitives>,
) -> eyre::Result<Pipeline<N>>
where
    N: ProviderNodeTypes,
    H: HeaderDownloader<Header = HeaderTy<N>> + 'static,
    B: BodyDownloader<Block = BlockTy<N>> + 'static,
    Evm: ConfigureEvm<Primitives = N::Primitives> + 'static,
{
    let mut builder = Pipeline::<N>::builder();

    if let Some(max_block) = max_block {
        debug!(target: "reth::cli", max_block, "Configuring builder to use max block");
        builder = builder.with_max_block(max_block)
    }

    let (tip_tx, tip_rx) = watch::channel(B256::ZERO);

    let prune_modes = prune_config.map(|prune| prune.segments).unwrap_or_default();

    let pipeline = builder
        .with_tip_sender(tip_tx)
        .with_metrics_tx(metrics_tx)
        .add_stages(
            DefaultStages::new(
                provider_factory.clone(),
                tip_rx,
                Arc::clone(&consensus),
                header_downloader,
                body_downloader,
                evm_config.clone(),
                stage_config.clone(),
                prune_modes,
            )
            .set(ExecutionStage::new(
                evm_config,
                consensus,
                stage_config.execution.into(),
                stage_config.execution_external_clean_threshold(),
                exex_manager_handle,
            )),
        )
        .build(provider_factory, static_file_producer);

    Ok(pipeline)
}
