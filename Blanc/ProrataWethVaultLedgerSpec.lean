-- ProrataWethVaultLedgerSpec.lean : the vault's ledger invariant on the ladder.

import Blanc.ProrataWethVaultShares
import Blanc.StorageOnlySpec

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
    refine ⟨a8, ?_, hrun⟩
    rw [congr_fun (Ninst.Hinv.inv (f := Devm.getStor) hcv) sevm.currentTarget,
      congr_fun (Ninst.Hinv.inv (f := Devm.getStor) hiz) sevm.currentTarget,
      (Devm.PopBurn.getStor hpb sevm.currentTarget).symm,
      (Devm.Burn.getStor hb sevm.currentTarget).symm,
      congr_fun (Ninst.Hinv.inv (f := Devm.getStor) hpush) sevm.currentTarget,
      congr_fun (Ninst.Hinv.inv (f := Devm.getStor) hcds) sevm.currentTarget,
      congr_fun (Ninst.Hinv.inv (f := Devm.getStor) hlt) sevm.currentTarget,
      (Devm.PopBurn.getStor hpop sevm.currentTarget).symm]

/-! ## `approve`

The one storage write the vault's approval path makes, extracted at source
level.  Much less is needed here than in the compiled effect theorem
(`Blanc/ProrataWethVaultShares.lean`): the ledger obligation asks only *where*
the write lands, so the value, the emitted log and the memory images are all
out of scope, and the stack has to be tracked only from the hash preimage
onward. -/

theorem of_approve_storage {fs : List Func} {sevm : Sevm} {s r : Devm}
    (run : Func.Run fs sevm s approve r) :
    ∃ k v, ¬ ValidAdr k ∧ k ≠ supplySlot ∧
      Devm.getStor r sevm.currentTarget =
        (Devm.getStor s sevm.currentTarget).set k v := by
  unfold approve nonzeroCaller nonzeroAddressArg guardedAllowanceKey at run
  -- the nonzero-caller guard
  rcases of_run_next run with ⟨p1, hcaller, run⟩
  rw [congr_fun (Ninst.Hinv.inv (f := Devm.getStor) hcaller) sevm.currentTarget]
  rcases of_run_next run with ⟨p2, hzero, run⟩
  rw [congr_fun (Ninst.Hinv.inv (f := Devm.getStor) hzero) sevm.currentTarget]
  rcases of_run_branch_revert run with ⟨p3, hpop1, run⟩
  rw [(Devm.PopBurn.getStor hpop1 sevm.currentTarget).symm]
  -- the canonical nonzero spender guard
  rcases of_run_prepend _ _ run with ⟨p4, hargline, run⟩
  rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hargline) sevm.currentTarget]
  rcases of_run_next run with ⟨p5, hdup, run⟩
  rw [congr_fun (Ninst.Hinv.inv (f := Devm.getStor) hdup) sevm.currentTarget]
  rcases of_run_prepend _ _ run with ⟨p6, hcheck, run⟩
  rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hcheck) sevm.currentTarget]
  rcases of_run_branch_revert run with ⟨p7, hpop2, run⟩
  rw [(Devm.PopBurn.getStor hpop2 sevm.currentTarget).symm]
  rcases of_run_next run with ⟨p8, hzero2, run⟩
  rw [congr_fun (Ninst.Hinv.inv (f := Devm.getStor) hzero2) sevm.currentTarget]
  rcases of_run_branch_revert run with ⟨p9, hpop3, run⟩
  rw [(Devm.PopBurn.getStor hpop3 sevm.currentTarget).symm]
  -- stage the owner, the spender and the amount
  rcases of_run_next run with ⟨p10, hcaller2, run⟩
  rw [congr_fun (Ninst.Hinv.inv (f := Devm.getStor) hcaller2) sevm.currentTarget]
  rcases of_run_prepend _ _ run with ⟨p11, hstage1, run⟩
  rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hstage1) sevm.currentTarget]
  rcases of_run_prepend _ _ run with ⟨p12, hstage2, run⟩
  rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hstage2) sevm.currentTarget]
  rcases of_run_prepend _ _ run with ⟨p13, hstage3, run⟩
  rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hstage3) sevm.currentTarget]
  rcases of_run_prepend _ _ run with ⟨p14, hstage4, run⟩
  rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hstage4) sevm.currentTarget]
  rcases of_run_prepend _ _ run with ⟨p15, hstage5, run⟩
  rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hstage5) sevm.currentTarget]
  -- the allowance key: two memory words, then the hash
  rcases of_run_prepend _ _ run with ⟨p16, hkey1, run⟩
  rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hkey1) sevm.currentTarget]
  rcases of_run_prepend _ _ run with ⟨p17, hkey2, run⟩
  rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hkey2) sevm.currentTarget]
  rcases of_run_prepend _ _ run with ⟨p18, hkey3, run⟩
  rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hkey3) sevm.currentTarget]
  rcases of_run_prepend _ _ run with ⟨p19, hkey4, run⟩
  rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hkey4) sevm.currentTarget]
  rcases of_run_prepend _ _ run with ⟨p20, hrange, run⟩
  rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hrange) sevm.currentTarget]
  have hrangePrefix : [0, 64] <<+ p20.stack := by
    rcases Line.of_run_cons hrange with ⟨q1, hpush64, hrange'⟩
    rcases Line.of_run_cons hrange' with ⟨q2, hpush0, hrangeNil⟩
    cases hrangeNil
    exact prefix_of_push (of_run_pushB256 hpush0)
      (prefix_of_push (of_run_pushB256 hpush64) nil_pref)
  rcases of_run_next run with ⟨p21, hhash, run⟩
  rw [congr_fun (Ninst.Hinv.inv (f := Devm.getStor) hhash) sevm.currentTarget]
  rcases prefix_of_keccak256 hhash hrangePrefix with ⟨key, hkeyPrefix⟩
  -- the collision guard
  rcases of_run_prepend _ _ run with ⟨p22, hguard, run⟩
  rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hguard) sevm.currentTarget]
  rcases of_checkAllowanceSlotCollision hkeyPrefix hguard with
    ⟨flag, hflagPrefix, hflagSound⟩
  rcases of_run_branch_revert run with ⟨p23, hpop4, run⟩
  rw [(Devm.PopBurn.getStor hpop4 sevm.currentTarget).symm]
  have hpopStack := hpop4.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpopStack
  rw [hpopStack] at hflagPrefix
  have hflagZero : flag = 0 :=
    pref_head_unique hflagPrefix (pref_append [0] p23.stack)
  rcases hflagSound hflagZero with ⟨hnva, hnsup⟩
  rw [hflagZero] at hflagPrefix
  have hkeyAt : key :: ([] : Stack) <<+ p23.stack := cons_pref_cons_inv hflagPrefix
  -- the write itself, then a storage-silent tail
  rcases of_run_prepend _ _ run with ⟨p24, hamount, run⟩
  rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hamount) sevm.currentTarget]
  have hamountPrefix : ∃ w, [w, key] <<+ p24.stack := by
    rcases Line.of_run_cons hamount with ⟨q3, hpushOff, hamount'⟩
    rcases Line.of_run_cons hamount' with ⟨q4, hmload, hamountNil⟩
    cases hamountNil
    exact prefix_of_mload hmload
      (prefix_of_push (of_run_pushB256 hpushOff) hkeyAt)
  rcases hamountPrefix with ⟨amount, hamountAt⟩
  rcases of_run_next run with ⟨p25, hswap, run⟩
  rw [congr_fun (Ninst.Hinv.inv (f := Devm.getStor) hswap) sevm.currentTarget]
  have hswapPrefix : [key, amount] <<+ p25.stack := by
    refine Stack.prefix_of_swap ?_ (of_run_swap hswap) hamountAt
    exact Stack.swapCore_zero
  rcases of_run_next run with ⟨p26, hsstore, run⟩
  rcases sstore_getStor_setStorVal hsstore hswapPrefix with ⟨v, hset⟩
  refine ⟨key, v, hnva, hnsup, ?_⟩
  rw [← congr_fun (Func.of_inv Devm.getStor Devm.getStor (by func_inv) run)
    sevm.currentTarget]
  exact hset

/-- Conservation rides across `approve`: the guard has shown the write lands at
a key the balances cannot see and the supply word is not. -/
theorem source_approve_preserves_conserved {sevm : Sevm} {s r : Devm}
    (run : Func.Run (vault.main :: vaultAux) sevm s (routed 2 approve) r)
    (h : Conserved (Devm.getStor s sevm.currentTarget)) :
    Conserved (Devm.getStor r sevm.currentTarget) := by
  rcases of_routed run with ⟨mid, hframe, bodyRun⟩
  rw [hframe] at h
  rcases of_approve_storage bodyRun with ⟨k, v, hnva, hnsup, hset⟩
  refine h.of_rest_eq ?_ ?_
  · rw [hset]
    exact (rest_set_of_not_validAdr hnva).symm
  · rw [hset]
    exact Stor.get_set_ne _ hnsup _

/-- The fallback is `Func.revert`, which no `Func.Run` witnesses, so the
obligation is vacuous: an unrecognized selector cannot move the ledger. -/
theorem vaultSpec_funcSound_revert {ca : Adr} :
    vaultSpec.FuncSoundNoMem ca vaultAux Func.revert := by
  intro _ _ _ _ _ _ h_run
  exact absurd h_run not_run_revert

end ProrataWethVault

end Blanc
