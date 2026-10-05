import Blanc.Lift.UniswapV2Pair.ApproveSource
import Blanc.Lift.LedgerFootprintOrder

/-!
# U7 storage-key control: an allowance/balance slot alias breaks raw ledger conservation

The raw LP ledger over a finite footprint reads each account's balance at its hashed slot
`mapSlot a 1` and the supply at slot 0: `RawLedgerOn keys s` is
`footprintSum keys (rawBalance s) = (s.get 0).toNat`.

`approve_storage_alias_breaks_ledger` takes any successful literal pc-zero `approve` run
(`approve_bytecode_refines_raw`, whose post storage `approvePublicPost_facts` projects as one write
of the amount at `approveSlot`) and a storage alias, stated as a hypothesis: the allowance slot
written equals the balance slot of a tracked footprint account.  If the written amount differs from
that balance, the post storage no longer satisfies the raw ledger, whatever it held before; and the
alias is exactly what the positive writer refinement's freshness premise excludes.  This is the
`trackedSum_collision_breaks_backing` pattern for the Pair; it asserts no Keccak collision exists,
and uses none of the positive ledger or history proofs.

Evidence altitude: EVM, conditional.  It is universal over successful raw runs under the alias
hypothesis; it does not exhibit such a run (no colliding preimage is known).
-/

namespace Blanc.Lift.UniswapV2Pair.LedgerKeyControl

open Jaune

/-- An account's LP balance as raw Pair storage holds it. -/
def rawBalance (s : Stor) (a : Adr) : B256 := s.get (WriterKey.balance a).slot

/-- Raw ledger conservation over a finite key footprint: balances sum to the slot-0 supply. -/
def RawLedgerOn (keys : List Adr) (s : Stor) : Prop :=
  Blanc.footprintSum keys (rawBalance s) = (s.get 0).toNat

/-- **Control (U7).**  A successful raw `approve` whose allowance slot aliases the balance slot of
a tracked footprint account, writing an amount other than that balance, ends outside raw ledger
conservation; the alias also refutes the positive refinement's freshness premise. -/
theorem approve_storage_alias_breaks_ledger {K : WriterKey → Prop} {sevm : Sevm}
    {b post : Devm} {G : Nat} {keys : List Adr} {a : Adr}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x095ea7b3)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (tracked : K (.balance a)) (inj : WriterInj K) (apart : WriterApart K)
    (member : a ∈ keys)
    (aliasing : approveSlot sevm = (WriterKey.balance a).slot)
    (differs : approveAmount sevm ≠ rawBalance (b.getStor sevm.currentTarget) a)
    (ledger : RawLedgerOn keys (b.getStor sevm.currentTarget)) :
    ¬ WriterFreshKeys K (approveTouched sevm.caller (approveSpender sevm)) ∧
    ¬ RawLedgerOn keys (post.getStor sevm.currentTarget) := by
  constructor
  · intro fresh
    have sameSlot : (WriterKey.balance a).slot =
        (WriterKey.allowance sevm.caller (approveSpender sevm)).slot := aliasing.symm
    rcases fresh.1 _ (List.mem_singleton_self _) with allowance | ⟨_, apartKeys⟩
    · cases inj _ _ tracked allowance sameSlot
    · exact apartKeys _ tracked sameSlot
  · intro after
    obtain ⟨_, _, _, _, G', eq⟩ := approve_bytecode_refines_raw codeEq fork selector run
    have stor := (approvePublicPost_facts (sevm := sevm) (b := b) (R := [0x095ea7b3])
      (G := G') getterInitMemory_ptr).2.2.1
    rw [← eq] at stor
    have notZero : approveSlot sevm ≠ 0 := by
      rw [aliasing]
      intro zero
      exact apart _ tracked (zero ▸ List.mem_cons_self)
    have supply : (post.getStor sevm.currentTarget).get 0 =
        (b.getStor sevm.currentTarget).get 0 := by
      rw [stor, Stor.get_set_ne _ notZero]
    have row : ∀ x, rawBalance (post.getStor sevm.currentTarget) x =
        if approveSlot sevm = (WriterKey.balance x).slot then approveAmount sevm
        else rawBalance (b.getStor sevm.currentTarget) x := by
      intro x
      rw [rawBalance, rawBalance, stor, Stor.get_set_ite]
    have aliased : ∀ x, approveSlot sevm = (WriterKey.balance x).slot →
        rawBalance (b.getStor sevm.currentTarget) x =
          rawBalance (b.getStor sevm.currentTarget) a := by
      intro x same
      rw [rawBalance, rawBalance, ← same, aliasing]
    have rowA : rawBalance (post.getStor sevm.currentTarget) a = approveAmount sevm := by
      rw [row a, ite_eq_left aliasing]
    unfold RawLedgerOn at ledger after
    rw [supply, ← ledger] at after
    rcases Nat.lt_or_gt_of_ne (fun same => differs (B256.toNat_inj _ _ same)) with down | up
    · have smaller : Blanc.footprintSum keys (rawBalance (post.getStor sevm.currentTarget)) <
          Blanc.footprintSum keys (rawBalance (b.getStor sevm.currentTarget)) := by
        refine Blanc.footprintSum_lt_footprintSum ?_ member ?_
        · intro x _
          rw [row x]
          by_cases same : approveSlot sevm = (WriterKey.balance x).slot
          · rw [ite_eq_left same, aliased x same]
            exact Nat.le_of_lt down
          · rw [ite_eq_right same]
        · rw [rowA]
          exact down
      rw [after] at smaller
      exact Nat.lt_irrefl _ smaller
    · have larger : Blanc.footprintSum keys (rawBalance (b.getStor sevm.currentTarget)) <
          Blanc.footprintSum keys (rawBalance (post.getStor sevm.currentTarget)) := by
        refine Blanc.footprintSum_lt_footprintSum ?_ member ?_
        · intro x _
          rw [row x]
          by_cases same : approveSlot sevm = (WriterKey.balance x).slot
          · rw [ite_eq_left same, aliased x same]
            exact Nat.le_of_lt up
          · rw [ite_eq_right same]
        · rw [rowA]
          exact up
      rw [after] at larger
      exact Nat.lt_irrefl _ larger

end Blanc.Lift.UniswapV2Pair.LedgerKeyControl
