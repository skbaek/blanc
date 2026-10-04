# New-host lane supporting reports

Worker and reviewer reports behind [`../UNISWAP_V2_NEWHOST_RETURN.md`](../UNISWAP_V2_NEWHOST_RETURN.md),
kept as written (local paths shortened). They are worker claims; the return document states
what the master verified.

- `sync.md`, `permit.md`, `deploy.md`, `skim-raw.md`, `skim-canonical.md`, `ledger.md`:
  per-packet theorem maps, correspondence rows, gate receipts and remaining obligations.
  Their "shared-wiring proposals" sections are superseded by the branch
  `claude/uv2nh-integration-proposal`. The diffs in `deploy.md` are a mistaken copy of
  `sync.md`'s; the proposal branch carries the correct deployment rows.
- `immediate-coverage.md`: correspondence and failure-branch coverage for transfer,
  approve, transferFrom, initialize and the 17 getters (Gemini 3.8 Flash inventory,
  spot-checked by the master).
- `model-review.md`: the different-family (Claude Opus 5.5) review of the GPT-authored
  model, with the full line-by-line correspondence table.
- Resource figures in these reports (peak memory, wall time) are this host's and
  informational only; they are not acceptance or cost claims.
