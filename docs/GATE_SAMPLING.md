# Blanc gate campaign policy

Generated from `scripts/gate-campaign-policy.json` and the economic inventory.

Production sampling is **disabled**. Every product-positive scenario and every
harness case remains complete; harness cases are conservatively classified as
mandatory boundaries. No optional production case exists, so no sampling boundary
moved and no 20-identity enablement claim is made.

Complete harness families (53): `beacon-deposit-assurance`, `beacon-deposit-current-mainnet`, `beacon-deposit-deployment`, `beacon-deposit-differential`, `beacon-deposit-model`, `current-mainnet`, `cycle-write-free-semantic`, `cycle-write-free-static`, `doc-counts`, `elab`, `execution-occurrence-semantic`, `execution-occurrence-static`, `execution-settlement`, `extraction-ownership`, `fmint-coverage`, `layering`, `lido-access`, `lido-artifact-profile`, `lido-circuit-breaker-assurance`, `lido-constructor`, `lido-deployment`, `lido-differential`, `lido-dispatchers`, `lido-enumeration`, `lido-history`, `lido-ossifiable-proxy-artifacts`, `lido-ossifiable-proxy-current-mainnet`, `lido-ossifiable-proxy-differential`, `lido-ossifiable-proxy-performance`, `lido-ossifiable-proxy-reference`, `lido-reference`, `lido-registry-semantic`, `lido-registry-static`, `lido-runtime-errors`, `lido-twg-census`, `lido-twg-differential`, `lido-twg-reference`, `proof-debt`, `proof-duplication`, `proof-module-size`, `proof-recipes`, `proof-residue`, `prorata-current-mainnet`, `prorata-fixtures`, `proxy-pair-upgrade-semantic`, `proxy-pair-upgrade-static`, `transient-settlement-semantic`, `transient-settlement-static`, `weth-coverage`, `weth10-current-mainnet`, `weth10-deployment`, `weth10-differential`, `weth10-reference`.

The deterministic sampler is retained and self-tested for a future family that
earns eligibility. It binds candidate, gate and schema; includes every stratum;
runs a complete audit every seventh scheduler day; and expands immediately after
a sampled failure.

Decision: No launch family has both a materially smaller eligible draw and 20 representative shadow identities. All candidate and harness cases therefore remain complete.
