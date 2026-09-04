# PRORATA WETH vault — theorem-to-claim map

Which theorem carries which sentence of the frozen claim
(`~/plans/reports/prorata-erc4626-port-sf.md` §12), and — as importantly —
which sentences are **not yet carried**.

Every name below is audited: it appears in `scripts/AxiomCheck.lean` and is
pinned in `scripts/check.sh`, so `scripts/check.sh --no-build` fails if its
axiom set moves. Names are given unqualified within
`Blanc.ProrataWethVault` and `Blanc.Composition.ProrataWethVault`.

## Carried

| Claim sentence | Theorem |
|---|---|
| The frozen ERC-4626 surface has the stated exact functional and rounding behaviour | `deposit_compiled_effect`, `mint_compiled_effect`, `withdraw_compiled_effect`, `redeem_compiled_effect`; the conversion and preview effects; `maxMint_compiled_effect`, `maxDeposit_compiled_effect`, `maxWithdraw_compiled_effect` and their `_stable`/`_exact` forms |
| …and the stated allowance, return, event and rollback behaviour on the ERC-20 share surface | `approve_compiled_effect`, `transfer_compiled_effect`, `transferFrom_compiled_effect` |
| Capacity is honest — `max*` reports what the vault will accept at the same stable state | the `max*` compiled effects above, with `check-prorata-weth-vault-oracle.sh`'s tightness batteries as finite evidence |
| The share ledger is conserved by every operation | `vault_message_preserves_conserved` (all twenty-five targets, dispatch-exhaustive) |
| …and by every operation that makes no external call, with no premise about the asset at all | `vault_nonflow_message_preserves_conserved` |
| The pair invariant holds at a configured two-runtime root | `ConfiguredRoot.conserved`, `ConfiguredRoot.backed` |
| …and is preserved across a sequence of vault messages | `ConfiguredMessages.preserves_conserved`, `ConfiguredRoot.chain_conserved` |
| Donations are accounted rather than minted against | `donationStep`; `PairBacked.donation` |
| A compiled flow is the accounting step it induces | `inboundEffect_accountingStep`, `outboundEffect_accountingStep`, `deposit_message_accountingStep`, `redeem_message_accountingStep` |
| …and every non-flow message is a silent one | `nonflow_message_accountingStep`, via `silent_accountingStep` and `silent_accountingStep_of_view` |
| A sequence of vault messages is an accounting history | `SteppedMessages.toPath` |
| P1 — exact operation rounding | `roundtrip_loss_le`, `redemption_le_assets` |
| P3 — exact whole-history residue | `dust_trace_exact` (an equality, not a bound) |
| P4 — open context, no profit, victim loss | `attacker_open_context`, `attacker_no_profit`, `victim_loss_bound`, `victim_loss_le_over_history`, and `SteppedMessages.victim_loss_le` over a real message sequence |
| The attack carrier is inhabited | `attack_carrier_inhabited` — a concrete transcript whose numbers agree with two independently written oracles |

## Not carried, and why

| Claim sentence | Status |
|---|---|
| "…preserved over configured reachable **histories**" | The chaining exists (`SteppedMessages.toPath`), but the **rely rung** does not: nothing yet says a message to some *other* account leaves the vault's storage alone. That needs the other account's code, and the generic `ContractSpec` ladder cannot supply it for this vault's flows — see `Blanc/ProrataWethVaultLedgerSpec.lean` |
| `mint` and `withdraw` as accounting steps | A **modelling gap**, not a missing proof: they are quoted in the inverse direction, and `convertToShares (previewMint s) = s` is not an identity. Written up in `Blanc/Composition/ProrataWethVaultBacking.lean` |
| "…foreign debits of the vault WETH row are excluded" under the trace-local premise | Not proved. The `NoVaultAllowanceKeyCollision`-premised exclusion and the unconditional debit-authorization classification are both open |
| P2 — exact previews and maxima as a named transported result | The underlying compiled effects exist; the P2 statement itself is not transported |
| "Finite OpenZeppelin/oracle evidence supports conformance" | Half-carried. The independent oracle and the executed differential exist and their self-tests bite; the **compiled-reference** half does not, because the OpenZeppelin closure is not vendored |

## What this map is not

It does not assert that the carried rows exhaust the frozen claim. It asserts
that each carried row has the named theorem behind it, and that each row in the
second table has nothing behind it yet. A claim absent from both tables has not
been checked either way.
