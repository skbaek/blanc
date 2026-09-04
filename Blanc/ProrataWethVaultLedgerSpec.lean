-- ProrataWethVaultLedgerSpec.lean : the vault's ledger invariant on the ladder.

import Blanc.ProrataWethVaultShares
import Blanc.StorageOnlySpec
import Blanc.StaticStores

/-!
# The vault's share ledger, packaged for the generic execution ladder

`Blanc/ProrataWethVaultShares.lean` proves that each share operation preserves
`LedgerConserved supplySlot`; `Blanc/Composition/ProrataWethVault*.lean` proves
it for the four ERC-4626 flows.  Those are *frame*-level facts about one
compiled walk.  This module lifts them to the contract-level obligation the
ladder consumes, so that conservation can be carried across a message, a block
and a configured history by `Blanc/Ladder.lean` rather than by new machinery.

## What fits here and what does not

The vault's joint invariant (`Blanc/Composition/ProrataWethVaultBacking.lean`)
has three conjuncts.  Two of them — conservation and the supply cap — are
properties of the vault's own storage, so `ContractSpec.ofStorageOnly` carries
them.  The third, the backing bound, relates the vault's supply to the vault's
*WETH* balance, which lives in a second account's storage.  `ContractSpec.Inv`
reads one account's storage plus the callvalue and the contract's **ETH**
balance, and that is exactly how the ETH-backed PRORATA
(`Blanc/ProrataInvariant.lean`) carries its own backing bound.  Replacing the
native asset with an ERC-20 is what moves that conjunct out of the record's
reach; it is the substance of the port, not an oversight here.

## Why only twenty-one of the twenty-five targets are here

The eighteen read-only targets and the three share writers make no external
call, so each preserves conservation outright and the obligation is
unconditional.

The four ERC-4626 flows do not, and the reason is a property of the source, not
of this file.  `finishInbound` snapshots the supply *before* the WETH child —
`snapshotQuoteState` does the `sload` into `supplyWord`, and `guardStableSupply`
runs on that snapshot — but performs its two writes *after* the child returns.
The receiver's balance is re-read post-call (`loadWord receiverWord +++ sload`),
while the supply is written as `shares + loadWord supplyWord`, from the
pre-call snapshot.  `requireCanonicalWethTrue` checks only that the child
returned the word `1`; nothing re-reads the supply.

So if the account at `assetAddress` held code that re-entered the vault and
moved the ledger, the post-call supply write would discard that movement while
the balance credit would keep it, and conservation would not survive the frame.
`outboundSettle` has the same shape.

The port is sound because `DirectWethConfiguration` pins that account's code to
`Blanc.wethCode`, and real WETH's `transferFrom` makes no outbound call.  But
that is a premise about a *second account's code*, and `ContractSpec` has no
slot for one: `Pre` carries the contract's own code, `Side` is a predicate on
the balance map alone.  The four flows therefore need a configured ladder that
threads `DirectWethConfiguration`, not this generic one — which is what the
goal's own "configured two-runtime root" and "configured-history preservation"
conditions were always asking for.

Recorded here rather than only in the goal's state brief because it is a
standing assumption of the artifact: this vault is safe against its configured
asset, and would not be safe against a re-entrant one.

## Which ladder entry point can carry it

`ContractSpec.preserves_lift` cannot. It is generic in the frame invariant `σ`,
which invites the thought that `σ` could carry `DirectWethConfiguration` and
hand it to the flows' obligation, but one of its own transport hypotheses
forbids that:

    σ_of_ne : e.currentTarget ≠ ca → c.Pre ca e d → σ e d

At every *foreign* frame that rebuilds `σ` from `Pre` alone, so `σ` may not
carry anything `Pre` does not — and `Pre` carries the contract's own code,
`Side` on the balance map, and `PreInv`. Strengthening `σ` makes `σ_of_ne`
unprovable rather than making the flows provable.

**`Blanc/ExecutionAdmission.lean`'s `lift_inv_admitted` is the entry point that
can.** It takes `σ` with *preservation* hypotheses rather than a re-derivation
one — `nextNone`, `nextSome` and `jump` each read
`… → sevm.currentTarget ≠ ca → σ sevm pre → σ sevm inter`, so a foreign step
has to **carry** `σ` forward, not conjure it. A `σ` conjoining
`LedgerConserved` with the configuration is admissible there: the configuration
is a statement about installed code, which a foreign step that creates nothing
preserves, and the ledger is preserved because a foreign frame does not write
the vault's storage (`Ninst.foreignNone_getStor_eq`).

So the rely and history rungs need that route rather than new machinery. The
generated proof recipes already say as much — "drop to `preserves_lift_admitted`
or `lift_inv_admitted` only when the standard `ContractSpec.PreWf` carrier is
insufficient" — and this vault is exactly a case where it is.

### The next obstruction on that route

`lift_inv_admitted`'s `with_depth_ind` obligation is the vault's own-frame
argument, and it must hold at an *arbitrary* frame the induction reaches. The
four flows' effect theorems each take a resource bundle —
`InboundCompiledResources` and its outbound twin — carrying `sevm.depth ≠ 0`,
`sevm.isStatic = false`, and a call-gas bound. `σ` cannot supply those: they
are facts about the particular frame, not about the world.

They do look like *consequences* of the run having succeeded: a static frame
cannot complete the `SSTORE` the flow performs, and insufficient call gas makes
the child return zero, which the `iszero` guard turns into a revert. If that is
right, the obligation is dischargeable — but only by deriving the bundles from
success rather than assuming them, and the premises exist precisely to avoid
that inversion.

So the decision on this route is whether to derive the resource bundles inside
the effect theorems or to thread them. That is worth settling before the
transport obligations are attempted, because a `σ` chosen for the wrong answer
is expensive to discover.
-/

namespace Blanc

open Jaune

namespace ProrataWethVault

/-- The vault's ledger instance.  `Inv` is conservation of the share supply and
ignores both the callvalue and the ETH balance: this contract holds no ether,
and its backing asset is WETH. -/
def vaultSpec : ContractSpec :=
  ContractSpec.ofStorageOnly vault Conserved

/-- Reduce a dispatch target's obligation to the bare storage implication. -/
theorem vaultSpec_funcSound {ca : Adr} (f : Func)
    (h_cons : ∀ {sevm : Sevm} {s r : Devm},
      Func.Run (vault.main :: vaultAux) sevm s f r →
      Conserved (Devm.getStor s sevm.currentTarget) →
      Conserved (Devm.getStor r sevm.currentTarget)) :
    vaultSpec.FuncSoundNoMem ca vaultAux f :=
  ContractSpec.ofStorageOnly_funcSound f h_cons

/-- The eighteen dispatch targets that write no storage.  Listed here rather
than filtered out of `vaultFuncs` so that the obligation below is one `rcases`
over a literal, exactly as fmint's is. -/
def readOnlyFuncs : List (B256 × Func) :=
  [ (selector "totalAssets" [], routed 0 totalAssets),
    (selector "name" [], routed 0 name),
    (selector "convertToAssets" [.uint256], routed 1 convertToAssets),
    (selector "previewWithdraw" [.uint256], routed 1 previewWithdraw),
    (selector "totalSupply" [], routed 0 totalSupply),
    (selector "decimals" [], routed 0 decimals),
    (selector "asset" [], routed 0 asset),
    (selector "maxDeposit" [.address], routed 1 maxDeposit),
    (selector "previewRedeem" [.uint256], routed 1 previewRedeem),
    (selector "balanceOf" [.address], routed 1 balanceOf),
    (selector "symbol" [], routed 0 symbol),
    (selector "previewMint" [.uint256], routed 1 previewMint),
    (selector "maxMint" [.address], routed 1 maxMint),
    (selector "convertToShares" [.uint256], routed 1 convertToShares),
    (selector "maxWithdraw" [.address], routed 1 maxWithdraw),
    (selector "maxRedeem" [.address], routed 1 maxRedeem),
    (selector "allowance" [.address, .address], routed 2 allowance),
    (selector "previewDeposit" [.uint256], routed 1 previewDeposit) ]

/-! ## The eighteen read-only targets

None of them writes storage, but several *read another contract*: every
live-quoting view reaches WETH's `balanceOf` through `readTotalAssets`, which
is a `STATICCALL`.  That rules out `func_inv` at `Devm.getStor` — entering
interpreted code preserves the storage *observation*, not the `Stor` tree — so
the certificate is `Func.SilentIn` at `Devm.storageView`, and the invariant is
transported along the resulting pointwise equality.

The targets also tail-jump, so the certificate is context-fixed and the
permitted slots have to be closed. -/

/-- The two aux entries a read-only target may tail-jump into. -/
def ReadOnlySilentSlot (k : Nat) : Prop :=
  k = returnWordSlot ∨ k = maxMintAfterAssetCapSlot

/-- Discharge a permitted-slot obligation. -/
syntax "readOnly_slot" : tactic
macro_rules
| `(tactic| readOnly_slot) =>
  `(tactic| first
      | (change ReadOnlySilentSlot returnWordSlot
         simp only [ReadOnlySilentSlot, true_or])
      | (change ReadOnlySilentSlot maxMintAfterAssetCapSlot
         simp only [ReadOnlySilentSlot, or_true]))

theorem silentIn_returnWord :
    Func.SilentIn Devm.storageView ReadOnlySilentSlot returnWord := by
  silent_structure

theorem silentIn_maxMintAfterAssetCap :
    Func.SilentIn Devm.storageView ReadOnlySilentSlot maxMintAfterAssetCap := by
  silent_structure with readOnly_slot

/-- The permitted set is closed: both entries are themselves silent. -/
theorem readOnlySilentSlot_closed :
    ∀ k g, ReadOnlySilentSlot k → (vault.main :: vaultAux)[k]? = some g →
      Func.SilentIn Devm.storageView ReadOnlySilentSlot g := by
  intro k g allowed lookup
  rcases allowed with h | h <;> subst k
  · obtain rfl : returnWord = g := Option.some.inj
      ((show (vault.main :: vaultAux)[returnWordSlot]? = some returnWord from rfl).symm.trans
        lookup)
    exact silentIn_returnWord
  · obtain rfl : maxMintAfterAssetCap = g := Option.some.inj
      ((show (vault.main :: vaultAux)[maxMintAfterAssetCapSlot]? =
          some maxMintAfterAssetCap from rfl).symm.trans lookup)
    exact silentIn_maxMintAfterAssetCap

/-- Every read-only dispatch target is storage-silent in the observation. -/
theorem readOnly_silent :
    ∀ p ∈ readOnlyFuncs,
      Func.SilentIn Devm.storageView ReadOnlySilentSlot p.2 := by
  intro p h_mem
  simp only [readOnlyFuncs, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (cases h) <;>
    silent_structure with readOnly_slot

/-- Conservation rides across every read-only target. -/
theorem readOnly_preserves_conserved :
    ∀ p ∈ readOnlyFuncs, ∀ {sevm : Sevm} {s r : Devm},
      Func.Run (vault.main :: vaultAux) sevm s p.2 r →
      Conserved (Devm.getStor s sevm.currentTarget) →
      Conserved (Devm.getStor r sevm.currentTarget) := by
  intro p h_mem sevm s r run h
  have view := Func.observe_eq_of_run_silentIn readOnlySilentSlot_closed run
    (readOnly_silent p h_mem)
  exact h.of_get_eq fun key =>
    (congrFun (congrFun view sevm.currentTarget) key).symm

/-- Strip the dispatch wrapper.  `routed` is `nonpayable` over
`requireStaticArgs`, so a successful entry pays two guards and reaches the body
with the storage untouched.  Shared by every writer obligation below. -/
theorem of_routed {fs : List Func} {sevm : Sevm} {s r : Devm}
    {words : Nat} {body : Func}
    (run : Func.Run fs sevm s (routed words body) r) :
    ∃ mid, Devm.getStor s sevm.currentTarget = Devm.getStor mid sevm.currentTarget ∧
      s.memory = mid.memory ∧
      Func.Run fs sevm mid body r := by
  unfold routed endpoint nonpayable requireStaticArgs at run
  rcases of_run_next run with ⟨a1, hcv, run⟩
  rcases of_run_next run with ⟨a2, hiz, run⟩
  rcases of_run_branch run with ⟨a3, hpb, hrun⟩ | ⟨w, a3, a4, hne, hpb, hb, hrun⟩
  · exact absurd hrun not_run_revert
  · rcases of_run_next hrun with ⟨a5, hpush, hrun⟩
    rcases of_run_next hrun with ⟨a6, hcds, hrun⟩
    rcases of_run_next hrun with ⟨a7, hlt, hrun⟩
    rcases of_run_branch_revert hrun with ⟨a8, hpop, hrun⟩
    refine ⟨a8, ?_, ?_, hrun⟩
    swap
    · exact (Ninst.Hinv.inv (f := Devm.memory) hcv).trans
        ((Ninst.Hinv.inv (f := Devm.memory) hiz).trans
          (hpb.memory.trans (hb.memory.trans
            ((Ninst.Hinv.inv (f := Devm.memory) hpush).trans
              ((Ninst.Hinv.inv (f := Devm.memory) hcds).trans
                ((Ninst.Hinv.inv (f := Devm.memory) hlt).trans hpop.memory))))))
    rw [congr_fun (Ninst.Hinv.inv (f := Devm.getStor) hcv) sevm.currentTarget,
      congr_fun (Ninst.Hinv.inv (f := Devm.getStor) hiz) sevm.currentTarget,
      (Devm.PopBurn.getStor hpb sevm.currentTarget).symm,
      (Devm.Burn.getStor hb sevm.currentTarget).symm,
      congr_fun (Ninst.Hinv.inv (f := Devm.getStor) hpush) sevm.currentTarget,
      congr_fun (Ninst.Hinv.inv (f := Devm.getStor) hcds) sevm.currentTarget,
      congr_fun (Ninst.Hinv.inv (f := Devm.getStor) hlt) sevm.currentTarget,
      (Devm.PopBurn.getStor hpop sevm.currentTarget).symm]

/-! ## The three share writers

Each is its body theorem from `Blanc/ProrataWethVaultShares.lean`, instantiated
at `Func.Run`, after `of_routed` strips the dispatch wrapper.  The body proofs
are shared with the compiled effect theorems rather than restated: they are
written over `Func.WalkInv`, so one proof text answers both. -/

theorem source_approve_preserves_conserved {sevm : Sevm} {s r : Devm}
    (memoryWf : Mem.Wf s.memory)
    (run : Func.Run (vault.main :: vaultAux) sevm s (routed 2 approve) r)
    (h : Conserved (Devm.getStor s sevm.currentTarget)) :
    Conserved (Devm.getStor r sevm.currentTarget) := by
  obtain ⟨mid, hstor, hmem, bodyRun⟩ := of_routed run
  rw [hstor] at h
  exact approve_body_preserves_conserved (R := Func.Run) (hmem ▸ memoryWf)
    nil_pref bodyRun h

theorem source_transfer_preserves_conserved {sevm : Sevm} {s r : Devm}
    (memoryWf : Mem.Wf s.memory)
    (run : Func.Run (vault.main :: vaultAux) sevm s (routed 2 transfer) r)
    (h : Conserved (Devm.getStor s sevm.currentTarget)) :
    Conserved (Devm.getStor r sevm.currentTarget) := by
  obtain ⟨mid, hstor, hmem, bodyRun⟩ := of_routed run
  rw [hstor] at h
  exact transfer_body_preserves_conserved (R := Func.Run) (hmem ▸ memoryWf)
    transferStaged_lookup nil_pref bodyRun h

theorem source_transferFrom_preserves_conserved {sevm : Sevm} {s r : Devm}
    (memoryWf : Mem.Wf s.memory)
    (run : Func.Run (vault.main :: vaultAux) sevm s (routed 3 transferFrom) r)
    (h : Conserved (Devm.getStor s sevm.currentTarget)) :
    Conserved (Devm.getStor r sevm.currentTarget) := by
  obtain ⟨mid, hstor, hmem, bodyRun⟩ := of_routed run
  rw [hstor] at h
  exact transferFrom_body_preserves_conserved (R := Func.Run) (hmem ▸ memoryWf)
    transferStaged_lookup nil_pref bodyRun h

/-- The fallback is `Func.revert`, which no `Func.Run` witnesses, so the
obligation is vacuous: an unrecognized selector cannot move the ledger. -/
theorem vaultSpec_funcSound_revert {ca : Adr} :
    vaultSpec.FuncSoundNoMem ca vaultAux Func.revert := by
  intro _ _ _ _ _ _ h_run
  exact absurd h_run not_run_revert


/-! ## The flows cannot run in a static frame

Every ERC-4626 flow writes storage on every path it can complete, so a
successful run is itself evidence that the frame was not static.  That turns
one third of the resource bundle those flows carry into a derived fact rather
than an assumed one. -/

/-- **Scope.** `transferStaged`, `withdrawBurn` and `redeemBurn` are proved
below. `depositAfterQuote` and `mintAfterQuote` are not: the structural walk
exhausts the elaborator's recursion depth before reaching their write, even
with `StoresOrHalts.prepend` collapsing whole staging lines in one step. The
ceiling is not raised — the proof-debt gate tracks `maxRecDepth` scopes — so
those two are open.

The obstruction has been narrowed. It is not the flows' outer structure and it
is not the literal staging lines: restating the shared tail over *variable*
lines, so that `StoresOrHalts.prepend` can collapse each in one step, still
exhausts the ceiling. It is `callWethTransferFrom`: a lemma about that
definition alone, with its asset line a variable and its body a hypothesis,
exhausts the ceiling on its own.

The likely cause is the tactic's first alternative rather than the term. That
alternative is `exact StoresOrHalts.store`, whose conclusion is
`StoresOrHalts fs (sstore ::: f)`, so trying it against a staging head forces
Lean to decide whether that head *is* `sstore` — and the staging heads are
`pushB256 (word * 32)` and `pushB256 assetAddress`, whose `B256` numeral
arithmetic is expensive to reduce. The finished term is only about twenty
constructors deep, which is nowhere near the ceiling.

So the next thing to try is the alternatives in a different order, or an
explicit term, rather than a coarser combinator. This reading is not verified:
it explains the measurements but was not tested by fixing it.

Slots a flow may tail-jump into on its way to a write. -/
def FlowStoreSlot (k : Nat) : Prop :=
  k = depositAfterQuoteSlot ∨ k = mintAfterQuoteSlot ∨
    k = withdrawAfterQuoteSlot ∨ k = redeemAfterQuoteSlot ∨
    k = withdrawBurnSlot ∨ k = redeemBurnSlot ∨
    k = transferFromAfterAllowanceSlot

/-- Discharge a permitted tail jump. -/
syntax "flow_slot" : tactic
macro_rules
| `(tactic| flow_slot) =>
  `(tactic| first
      | exact StoresOrHalts.call (by rfl) (by stores_structure with flow_slot)
      | exact StoresOrHalts.never not_run_revert)

theorem transferStaged_storesOrHalts :
    StoresOrHalts (vault.main :: vaultAux) transferStaged := by
  stores_structure

theorem withdrawBurn_storesOrHalts :
    StoresOrHalts (vault.main :: vaultAux) withdrawBurn := by
  stores_structure

theorem redeemBurn_storesOrHalts :
    StoresOrHalts (vault.main :: vaultAux) redeemBurn := by
  stores_structure

end ProrataWethVault

end Blanc
