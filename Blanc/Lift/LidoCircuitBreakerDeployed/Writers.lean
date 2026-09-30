import Blanc.Lift.LidoCircuitBreakerDeployed.FrameMem
import Blanc.Lift.LidoCircuitBreakerDeployed.L2
import Blanc.Lift.LidoCircuitBreakerDeployed.SetPauserNonzero
import Blanc.Lift.LidoCircuitBreakerDeployed.NoHalt

/-!
# The deployed Lido `registerPauser` wrapper, walked

Ladder unit lido-writers-v1, the `registerPauser` field of `LidoWriterSpecsM`.
The route is selector wrapper 59 → ABI decoder 20 (entry 29 twice: the two
address arguments, each checked canonical) → body 21 (`onlyAdmin`, the
previous-pauser read, `setPauser` entry 32 → 4, the heartbeat tail entry 2 with
its two `_setHeartbeatExpiry` calls, entry 22).

The concrete per-frame premise `lidoA` lives here too: for the frame's two
calldata address words `t = dataWord 4`, `np = dataWord 36` (the words the
decoder reads), the `RegistryKeysFaithful (2 ^ 160)` instance of the `setPauser`
branch the frame-entry witness selects, and `ForeignApart (2 ^ 160)` of the two
`heartbeatExpiry` slots `registerPauser` may write; and, for `pause(t)`, the
branch instance of `setPauser(t, 0)`.
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune
open Blanc
open Blanc.Lift
open Blanc.LidoCircuitBreaker

theorem eq_of_eqCheck_ne {a b : B256} (h : B256.eqCheck a b ≠ 0) : a = b := by
  unfold B256.eqCheck at h
  split_ifs at h with he
  · exact he
  · exact absurd rfl h

theorem canonical_toAdr_toB256 (x : B256) : canonicalAddress x.toAdr.toB256 := by
  unfold canonicalAddress
  have e : x.toAdr.toB256.toNat = x.toAdr.toNat := by
    simp [Adr.toB256, Adr.toNat, B256.toNat, B128.toNat]
  rw [e]
  exact Adr.toNat_lt_size _

/-- A word equal to its low-160-bit mask is a canonical address. -/
theorem canonical_of_mask_eq {x : B256}
    (h : x = x &&& Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) : canonicalAddress x := by
  rw [B256.and_comm, ff20_and_word] at h
  rw [h]
  exact canonical_toAdr_toB256 x

/-! ## Entry 29: one ABI address argument -/

/-- Entry 29 (`abi_decode_address` at offset `off`) returns the calldata word at
`off`, which it has checked canonical. -/
theorem entry29_ret {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {off ra : B256}
    {xs : List B256} {D : Devm}
    (run : SFunc.Run prog sevm (St b (off :: ra :: xs) M G) t_0f93_c29 (.returned D)) :
    canonicalAddress (Sevm.dataWord sevm off) ∧ ∃ G', D = St b (Sevm.dataWord sevm off :: xs) M G' := by
  have run := run.cut
  unfold t_0f93_c29 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_dup (w := off) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_dup (w := Sevm.dataWord sevm off) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_and s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G7, rfl⟩ := ri_dup (w := Sevm.dataWord sevm off) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G8, rfl⟩ := ri_eq s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G9, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G10, run⟩ | ⟨hnz, G10, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run (by decide)).elim
  · refine ⟨canonical_of_mask_eq (eq_of_eqCheck_ne hnz), ?_⟩
    unfold t_0fb6_c29 at run
    obtain ⟨G11, run⟩ := ric_dest run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G12, rfl⟩ := ri_swap (n := 1) rfl s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G13, rfl⟩ := ri_swap (n := 0) rfl s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G14, rfl⟩ := ri_pop s1
    obtain ⟨G15, hr⟩ := ric_ret run
    injection hr with hr
    injection hr with hr
    exact ⟨G15, hr⟩

/-! ## Entry 20: the two-address decoder -/

/-- Entry 20 (`abi_decode_address_address` over `calldatasize`) returns the two
canonical calldata words at 4 and 36, the second on top. -/
theorem entry20_ret {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {cds ra : B256}
    {xs : List B256} {D : Devm}
    (run : SFunc.Run prog sevm (St b ((4 : B256) :: cds :: ra :: xs) M G) t_0fbb_c20
      (.returned D)) :
    canonicalAddress (Sevm.dataWord sevm 4) ∧ canonicalAddress (Sevm.dataWord sevm 36) ∧
      ∃ G', D = St b (Sevm.dataWord sevm 36 :: Sevm.dataWord sevm 4 :: xs) M G' := by
  have run := run.cut
  unfold t_0fbb_c20 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_dup (w := (4 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_dup (w := cds) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G7, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨z, G8, rfl⟩ := ri_slt s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G9, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G10, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G11, run⟩ | ⟨-, G11, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run (by decide)).elim
  unfold t_0fcc_c20 at run
  obtain ⟨G12, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G13, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G14, rfl⟩ := ri_dup (w := (4 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G15, rfl⟩ := ri_push s1
  obtain ⟨G16, hcall⟩ := ric_call (g := t_0f93_c29) rfl run
  rcases hcall with ⟨D1, r1, run⟩ | ⟨D1, -, hr⟩
  swap
  · cases hr
  obtain ⟨ht, G17, rfl⟩ := entry29_ret r1
  unfold t_0fd5_c20 at run
  obtain ⟨G18, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G19, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G20, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G21, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G22, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G23, rfl⟩ := ri_dup (w := (4 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G24, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G25, rfl⟩ := ri_push s1
  obtain ⟨G26, hcall⟩ := ric_call (g := t_0f93_c29) rfl run
  rcases hcall with ⟨D2, r2, run⟩ | ⟨D2, -, hr⟩
  swap
  · cases hr
  obtain ⟨hnp, G27, rfl⟩ := entry29_ret r2
  rw [show (4 : B256) + Bytes.toB256 [0x20] = 36 from by decide] at hnp run
  refine ⟨ht, hnp, ?_⟩
  unfold t_0fe3_c20 at run
  obtain ⟨G28, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G29, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G30, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G31, rfl⟩ := ri_swap (n := 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G32, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G33, rfl⟩ := ri_swap (n := 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G34, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G35, rfl⟩ := ri_pop s1
  obtain ⟨G36, hr⟩ := ric_ret run
  injection hr with hr
  injection hr with hr
  simp only [List.set] at hr
  exact ⟨G36, hr⟩

/-! ## Entry 22: `_setHeartbeatExpiry(p, v)` returns above its two arguments -/

/-- Entry 22 pops its two arguments and its return tag. -/
theorem entry22_ret {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {v p ra : B256}
    {xs : List B256} {D : Devm} (hfork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run prog sevm (St b (v :: p :: ra :: xs) M G) t_0cd5_c22 (.returned D)) :
    ∃ b' M' G', D = St b' xs M' G' := by
  have run := run.cut
  unfold t_0cd5_c22 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_and s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G7, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G8, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G9, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G10, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G11, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G12, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G13, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G14, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G15, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G16, rfl⟩ := ri_keccak s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G17, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G18, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G19, rfl⟩ := ri_sstore hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G20, rfl⟩ := ri_mload s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G21, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G22, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G23, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G24, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G25, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G26, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G27, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G28, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G29, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G30, rfl⟩ := ri_swap (n := 0) rfl s1
  dsimp only [List.set] at run
  obtain ⟨G31, run⟩ := ric_jump (List.not_mem_nil) (show prog[37]? = some t_0d2e_c37 from rfl) run
  unfold t_0d2e_c37 at run
  obtain ⟨G32, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G33, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G34, rfl⟩ := ri_mload s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G35, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G36, rfl⟩ := ri_swap (n := 1) rfl s1
  dsimp only [List.set] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G37, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G38, rfl⟩ := ri_swap (n := 0) rfl s1
  dsimp only [List.set] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨b', M', G39, rfl⟩ := ri_log2 s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G40, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G41, rfl⟩ := ri_pop s1
  obtain ⟨G42, hr⟩ := ric_ret run
  injection hr with hr
  injection hr with hr
  exact ⟨b', M', G42, hr⟩

/-! ## The concrete per-frame premise -/

/-- The logical keys the `setPauser(t, np)` branch selected by `entries` writes:
exactly the list the branch walk's `RegistryKeysFaithful` premise is over. -/
def setPauserKeys (entries : List Entry) (t np : B256) : List B256 :=
  match findEntry entries t with
  | some (index, old) =>
      if np = 0 then removalWriteKeys entries t old index
      else (nonzeroWrites entries t np old).map Prod.fst
  | none =>
      if np = 0 then (absentZeroWrites entries t).map Prod.fst
      else freshWriteKeys entries t np

/-- `registerPauser(t, np)`'s collision premise over the frame-entry witness: the
selected `setPauser` branch's keys are faithful at the fixed bound `2 ^ 160`, and
the `heartbeatExpiry` slots of the previous pauser (when there is one) and of
the new pauser (when nonzero) are off the Registry layout. -/
def RegisterPauserApart (entries : List Entry) (t np : B256) : Prop :=
  RegistryKeysFaithful (2 ^ 160) (setPauserKeys entries t np) ∧
  (assignmentAt entries t ≠ 0 → ForeignApart (2 ^ 160) (mapSlot (assignmentAt entries t) 2)) ∧
  (np ≠ 0 → ForeignApart (2 ^ 160) (mapSlot np 2))

/-- **The concrete Registry-writer premise `A`.**  For the frame's calldata
address words `t = dataWord 4` and `np = dataWord 36` (what the `registerPauser`
and `pause` decoders read), in implication form: when they are canonical and
`t` nonzero (the only calls that reach entry 32), `registerPauser(t, np)`'s
premise and `pause(t)`'s (the `setPauser(t, 0)` branch keys).  It is not
conditioned on the selector, since the dispatcher lemma does not track it
(decision logged in the report); for every other selector it is a collision
fact about the same finitely many keys of that frame's calldata words. -/
def lidoA : List Entry → Sevm → Prop := fun entries sevm =>
  (nonzeroCanonicalAddress (Sevm.dataWord sevm 4) →
    canonicalAddress (Sevm.dataWord sevm 36) →
    RegisterPauserApart entries (Sevm.dataWord sevm 4) (Sevm.dataWord sevm 36)) ∧
  (nonzeroCanonicalAddress (Sevm.dataWord sevm 4) →
    RegistryKeysFaithful (2 ^ 160) (setPauserKeys entries (Sevm.dataWord sevm 4) 0))

/-! ## Fresh registration from the unified premise -/

/-- The five chronological logical writes of a fresh registration. -/
def freshWrites (entries : List Entry) (t np : B256) : List (B256 × B256) :=
  [(assignmentSlot t, np),
   (arrayEntrySlot (Nat.toB256 (entries.length + 1)), t),
   (indexSlot t, Nat.toB256 (entries.length + 1)),
   (arrayLengthSlot, Nat.toB256 (entries.length + 1)),
   (countSlot np, Nat.toB256 (assignmentCount entries np + 1))]

theorem rawFreshPost_eq_apply (raw : Stor) (entries : List Entry) {t np : B256}
    (ht : canonicalAddress t) (hnp : canonicalAddress np)
    (hlen : entries.length + 1 < 2 ^ 252) :
    rawFreshPost raw entries t np = applyRegistryRawWrites raw (freshWrites entries t np) := by
  simp only [applyRegistryRawWrites, freshWrites, List.foldl_cons, List.foldl_nil]
  rw [solKey_assignmentSlot ht, registryRawValue_assignmentSlot ht,
    solKey_arrayEntrySlot hlen, registryRawValue_arrayEntrySlot hlen,
    solKey_indexSlot ht, registryRawValue_indexSlot ht,
    solKey_arrayLengthSlot, registryRawValue_arrayLengthSlot,
    solKey_countSlot hnp, registryRawValue_countSlot hnp]
  rfl

/-- Fresh registration preserves the Registry witness under `freshWriteKeys`
faithfulness: the fresh counterpart of `rawNonzero_preservesRegistry`. -/
theorem rawFresh_preservesRegistry_of_faithful
    {before after : Stor} {entries : List Entry} {t np : B256}
    (hw : RegistryWitness (solRegistryStorage before) entries)
    (ht : nonzeroCanonicalAddress t) (hnp : nonzeroCanonicalAddress np)
    (hfind : findEntry entries t = none)
    (hfaithful : RegistryKeysFaithful (entries.length + 1) (freshWriteKeys entries t np))
    (hwrites : ∀ key, after.get key = (rawFreshPost before entries t np).get key) :
    RegistryWitness (solRegistryStorage after) (entries ++ [(t, np)]) := by
  have hlen := hw.fresh_length_lt_2pow252
  have hlogical := RegistryWitness.applyFreshWritesOfReadEffect
    (post := ⟨fun key => (freshWrites entries t np).foldl
        (fun cur w => if w.1 = key then w.2 else cur) ((solRegistryStorage before).read key)⟩)
    hw ht hnp hfind (fun _ => rfl)
  have harr : entries.length < entries.length + 1 := by omega
  refine RegistryWitness.ofRawRegistryWrites (writes := freshWrites entries t np) hlen (by simp)
    hfaithful ?_ ?_
    (fun key => by rw [hwrites, rawFreshPost_eq_apply _ _ ht.2 hnp.2 hlen]) hlogical
  · intro w hw'
    simp only [freshWrites, List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨t, ht.2, rfl⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨entries.length, harr, rfl⟩)))
    · exact Or.inr (Or.inl ⟨t, ht.2, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inl ⟨np, hnp.2, rfl⟩))
  · intro w hw' hfam
    simp only [freshWrites, List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl | rfl | rfl
    · exact addressSlotReadWord_eq_self_of_lt hnp.2
    · exact addressSlotReadWord_eq_self_of_lt ht.2
    · rcases hfam with ⟨p, hp, heq⟩ | ⟨i, hi, heq⟩
      · exact absurd heq.symm (registryAddressFamilies_pairwise hp ht.2 ht.2).1
      · have hb : (Nat.toB256 (i + 1)).toNat < 2 ^ 252 := by
          rw [B256.toNat_toB256_of_lt (by omega)]; omega
        exact absurd heq (registryAddressFamilies_ne_arrayEntrySlot ht.2 ht.2 hb).2.1
    · rcases hfam with ⟨p, hp, heq⟩ | ⟨i, hi, heq⟩
      · exact absurd heq.symm (registryAddressFamilies_ne_arrayLengthSlot hp hp).1
      · exact absurd heq.symm (arrayEntrySlot_ne_arrayLengthSlot (by omega))
    · rcases hfam with ⟨p, hp, heq⟩ | ⟨i, hi, heq⟩
      · exact absurd heq.symm (registryAddressFamilies_pairwise hp hp hnp.2).2.1
      · have hb : (Nat.toB256 (i + 1)).toNat < 2 ^ 252 := by
          rw [B256.toNat_toB256_of_lt (by omega)]; omega
        exact absurd heq (registryAddressFamilies_ne_arrayEntrySlot hnp.2 hnp.2 hb).2.2

/-! ## Entry 32, all four branches -/

/-- Entry 32 reverts on a zero target. -/
theorem entry32_zero_false {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {np : B256}
    {base : List B256} {post : Devm}
    (run : SFunc.Run prog sevm (St b (np :: 0 :: base) M G) t_0934_c32 (.returned post)) :
    False := by
  have run := run.cut
  unfold t_0934_c32 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_dup (w := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_and s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G6, run⟩ | ⟨hnz, -, -⟩
  · exact SFunc.RunCutP.false_of_noOk run (by decide)
  · exact hnz (by decide)

/-- **`setPauser(t, np)`, whichever branch the witness selects.**  A successful
entry-32 run from well-formed memory preserves `RegInv` and returns to `base`,
given the selected branch's keys faithful at `2 ^ 160`. -/
theorem setPauser_step {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {np t : B256}
    {ra : B256} {base : List B256} {post : Devm} {entries : List Entry}
    (hfork : CoveredFork sevm.benvStat.fork) (hmem : MemOK M)
    (hw : RegistryWitness (solRegistryStorage (Devm.getStor b sevm.currentTarget)) entries)
    (ht : canonicalAddress t) (hnp : canonicalAddress np)
    (hkeys : t ≠ 0 → RegistryKeysFaithful (2 ^ 160) (setPauserKeys entries t np))
    (run : SFunc.Run prog sevm (St b (np :: t :: 3 :: ra :: base) M G) t_0934_c32
      (.returned post)) :
    RegInv (Devm.getStor post sevm.currentTarget) ∧ ∃ b' M' G', post = St b' base M' G' := by
  by_cases ht0 : t = 0
  · subst ht0; exact (entry32_zero_false run).elim
  have htn : nonzeroCanonicalAddress t := ⟨ht0, ht⟩
  have hk := hkeys ht0
  have hlenle := hw.entries_length_le
  cases hf : findEntry entries t with
  | none =>
    simp only [setPauserKeys, hf] at hk
    by_cases hnp0 : np = 0
    · subst hnp0
      simp only [↓reduceIte] at hk
      have hk' := hk.bound_mono (b := entries.length + 1) (by omega)
      obtain ⟨hwr, -, b', data, M', G', rfl, -⟩ :=
        setPauser_absentZero_inv hfork hmem.1 hmem.2 hw htn hf hk' run
      exact ⟨⟨entries, rawAbsentZero_preservesRegistry hw htn hf hk' hwr⟩, _, _, _, rfl⟩
    · simp only [hnp0, ↓reduceIte] at hk
      have hk' := hk.bound_mono (b := entries.length + 1) (by omega)
      obtain ⟨hwr, -, b', data, M', G', rfl, -⟩ :=
        setPauser_fresh_inv hfork hmem.1 hmem.2 hw htn ⟨hnp0, hnp⟩ hf hk' run
      exact ⟨⟨_, rawFresh_preservesRegistry_of_faithful hw htn ⟨hnp0, hnp⟩ hf hk' hwr⟩,
        _, _, _, rfl⟩
  | some val =>
    obtain ⟨index, old⟩ := val
    simp only [setPauserKeys, hf] at hk
    by_cases hnp0 : np = 0
    · subst hnp0
      simp only [↓reduceIte] at hk
      have hk' := hk.bound_mono (b := entries.length) (by omega)
      obtain ⟨hwr, -, b', data, M', G', rfl, -⟩ :=
        setPauser_removal_inv hfork hmem.1 hmem.2 hw htn hf hk' run
      exact ⟨⟨_, rawRemoval_preservesRegistry_of_registryKeysFaithful hw htn hf hk' hwr⟩,
        _, _, _, rfl⟩
    · simp only [hnp0, ↓reduceIte] at hk
      have hk' := hk.bound_mono (b := entries.length) (by omega)
      obtain ⟨hwr, -, b', data, M', G', rfl, -⟩ :=
        setPauser_nonzero_inv hfork hmem.1 hmem.2 hw htn ⟨hnp0, hnp⟩ hf hk' run
      exact ⟨⟨_, rawNonzero_preservesRegistry hw htn ⟨hnp0, hnp⟩ hf hk' hwr⟩, _, _, _, rfl⟩

/-! ## The heartbeat tail (entry 2) -/

theorem getStor_St (b : Devm) (S : List B256) (M : Mem) (G : Nat) (a : Adr) :
    Devm.getStor (St b S M G) a = Devm.getStor b a := rfl

theorem St_pref (b : Devm) (S : List B256) (M : Mem) (G : Nat) : S <<+ (St b S M G).stack := by
  simpa only [List.append_nil, St.stack] using pref_append S []

theorem stack_of_pref {S : List B256} {d : Devm} (h : S <<+ d.stack) :
    ∃ tl, d.stack = S ++ tl := by
  obtain ⟨tl, h⟩ := h
  exact ⟨tl, h⟩

/-- `t_044b_c2`: three pops and the return keep the base. -/
theorem t044b_ret {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {x y z ra : B256}
    {xs : List B256} {D : Devm}
    (run : SFunc.RunCut prog sevm [] (St b (x :: y :: z :: ra :: xs) M G) t_044b_c2
      (.done (.returned D))) :
    Devm.getStor D sevm.currentTarget = Devm.getStor b sevm.currentTarget := by
  unfold t_044b_c2 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_pop s1
  obtain ⟨G5, hr⟩ := ric_ret run
  injection hr with hr
  injection hr with hr
  rw [hr]
  rfl

/-- A call of entry 22 writing `v` at `mapSlot p 2`, for a canonical `p` whose
slot is off the Registry: it returns to the caller's stack below its three
words, keeping any storage predicate `Φ` stable under such writes. -/
theorem call22_preserves {Apart : B256 → Prop} {Φ : Stor → Prop}
    (hΦ : ∀ {s : Stor} {w v : B256}, Apart w → Φ s → Φ (s.set w v))
    {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {v p ra : B256}
    {xs : List B256} {f : SFunc} {r : Seg} (hfork : CoveredFork sevm.benvStat.fork)
    (hp : canonicalAddress p) (hfa : Apart (mapSlot p 2))
    (hinv : Φ (Devm.getStor b sevm.currentTarget))
    (run : SFunc.RunCut prog sevm [] (St b (Bytes.toB256 [0x0c, 0xd5] :: v :: p :: ra :: xs) M G)
      (.callNext 22 f) r)
    (hr : ∀ D, r ≠ .done (.halted D)) :
    ∃ b' M' G', Φ (Devm.getStor b' sevm.currentTarget) ∧
      SFunc.RunCut prog sevm [] (St b' xs M' G') f r := by
  obtain ⟨G1, hcall⟩ := ric_call (g := t_0cd5_c22) rfl run
  rcases hcall with ⟨D, r22, run⟩ | ⟨D, -, hh⟩
  swap
  · exact (hr D hh).elim
  have hs := entry22_stor (o := .returned D) (St_pref _ _ _ _) r22
  obtain ⟨b', M', G', rfl⟩ := entry22_ret hfork r22
  refine ⟨b', M', G', ?_, run⟩
  rw [show Devm.getStor b' sevm.currentTarget =
    Devm.getStor (Outcome.devm (.returned (St b' xs M' G'))) sevm.currentTarget from rfl, hs,
    getStor_St, B256.toAdr_toB256_of_lt hp]
  exact hΦ hfa hinv

/- The universal-registry interface remains a corollary. -/
theorem call22_foreign {Φ : Stor → Prop}
    (hΦ : ∀ {s : Stor} {w v : B256}, ForeignApart (2 ^ 160) w → Φ s → Φ (s.set w v))
    {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {v p ra : B256}
    {xs : List B256} {f : SFunc} {r : Seg} (hfork : CoveredFork sevm.benvStat.fork)
    (hp : canonicalAddress p) (hfa : ForeignApart (2 ^ 160) (mapSlot p 2))
    (hinv : Φ (Devm.getStor b sevm.currentTarget))
    (run : SFunc.RunCut prog sevm [] (St b (Bytes.toB256 [0x0c, 0xd5] :: v :: p :: ra :: xs) M G)
      (.callNext 22 f) r)
    (hr : ∀ D, r ≠ .done (.halted D)) :
    ∃ b' M' G', Φ (Devm.getStor b' sevm.currentTarget) ∧
      SFunc.RunCut prog sevm [] (St b' xs M' G') f r := by
  exact call22_preserves hΦ hfork hp hfa hinv run hr

/-- `t_0418_c2`: when the new pauser is nonzero, `_setHeartbeatExpiry(np, now +
heartbeatInterval)`; then pop and return.  Keeps any `Φ` stable under off-Registry writes. -/
theorem t0418_preserves {Apart : B256 → Prop} {Φ : Stor → Prop}
    (hΦ : ∀ {s : Stor} {w v : B256}, Apart w → Φ s → Φ (s.set w v))
    {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {p0 np t ra : B256}
    {xs : List B256} {D : Devm} (hfork : CoveredFork sevm.benvStat.fork)
    (hnp : canonicalAddress np) (hfa : np ≠ 0 → Apart (mapSlot np 2))
    (hinv : Φ (Devm.getStor b sevm.currentTarget))
    (run : SFunc.RunCut prog sevm [] (St b (p0 :: np :: t :: ra :: xs) M G) t_0418_c2
      (.done (.returned D))) :
    Φ (Devm.getStor D sevm.currentTarget) := by
  unfold t_0418_c2 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_dup (w := np) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_and s1
  rw [mask_and_canonical hnp] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨hz, G7, run⟩ | ⟨-, G7, run⟩
  · -- `np ≠ 0`: the new pauser's heartbeat
    have hnp0 : np ≠ 0 := by
      intro h; subst h; exact absurd hz (by decide)
    unfold t_0435_c2 at run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G8, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G9, rfl⟩ := ri_dup (w := np) rfl s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G10, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G11, rfl⟩ := ri_sload hfork s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G12, rfl⟩ := ri_timestamp s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G13, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G14, rfl⟩ := ri_swap (n := 1) rfl s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G15, rfl⟩ := ri_swap (n := 0) rfl s1
    dsimp only [List.set] at run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G16, rfl⟩ := ri_push s1
    obtain ⟨G17, hcall⟩ := ric_call (g := t_10a8_c23) rfl run
    rcases hcall with ⟨D23, r23, run⟩ | ⟨D23, -, hh⟩
    swap
    · cases hh
    obtain ⟨w, hw⟩ := entry23_ret (xs := np :: Bytes.toB256 [0x04, 0x4b] :: p0 :: np :: t :: ra :: xs)
      (St_pref _ _ _ _) r23
    obtain ⟨tl, hw⟩ := stack_of_pref hw
    have hst : D23.state = _ := silent_entry_state (k := 23) (by decide) rfl r23
    have hinv23 : Φ (Devm.getStor D23 sevm.currentTarget) := by
      rw [getStor_eq_of_state_eq hst, getStor_St, afterSload_getStor]
      exact hinv
    rw [St.self (d := D23) hw rfl] at run
    unfold t_0446_c2 at run
    obtain ⟨G18, run⟩ := ric_dest run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G19, rfl⟩ := ri_push s1
    obtain ⟨b', M', G', hinv', run⟩ := call22_preserves hΦ hfork hnp (hfa hnp0) hinv23 run
      (fun _ h => by cases h)
    exact (t044b_ret run) ▸ hinv'
  · exact (t044b_ret run) ▸ hinv

/-- `t_0409_c2` (entry 2's head, also inlined in `t_03e2_c21`): on a nonzero
flag `c` (the previous pauser has no pausables left), `_setHeartbeatExpiry(p0,
0)`, then the new pauser's heartbeat. -/
theorem t0409_preserves {Apart : B256 → Prop} {Φ : Stor → Prop}
    (hΦ : ∀ {s : Stor} {w v : B256}, Apart w → Φ s → Φ (s.set w v))
    {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {c p0 np t ra : B256}
    {xs : List B256} {D : Devm} (hfork : CoveredFork sevm.benvStat.fork)
    (hp0 : canonicalAddress p0) (hnp : canonicalAddress np)
    (hc : c ≠ 0 → Apart (mapSlot p0 2))
    (hfa : np ≠ 0 → Apart (mapSlot np 2))
    (hinv : Φ (Devm.getStor b sevm.currentTarget))
    (run : SFunc.RunCut prog sevm [] (St b (c :: p0 :: np :: t :: ra :: xs) M G) t_0409_c2
      (.done (.returned D))) :
    Φ (Devm.getStor D sevm.currentTarget) := by
  unfold t_0409_c2 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨hz, G4, run⟩ | ⟨-, G4, run⟩
  · have hc0 : c ≠ 0 := by
      intro h; subst h; exact absurd hz (by decide)
    unfold t_040f_c2 at run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G5, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G6, rfl⟩ := ri_dup (w := p0) rfl s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G7, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G8, rfl⟩ := ri_push s1
    obtain ⟨b', M', G', hinv', run⟩ := call22_preserves hΦ hfork hp0 (hc hc0) hinv run
      (fun _ h => by cases h)
    exact t0418_preserves hΦ hfork hnp hfa hinv' run
  · exact t0418_preserves hΦ hfork hnp hfa hinv run

/-! ## Entry 21: the `registerPauser` body -/

/-- Lift a registry-run postcondition through the exact heartbeat continuation,
using an arbitrary explicitly supplied set of apart raw slots. -/
theorem entry21_preserves {Apart : B256 → Prop} {Φ : Stor → Prop}
    (hΦ : ∀ {s : Stor} {w v : B256}, Apart w → Φ s → Φ (s.set w v))
    {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {np t ra : B256}
    {xs : List B256} {D : Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (hmem : MemOK M)
    (ht : canonicalAddress t) (hnp : canonicalAddress np)
    (hfa0 : t ≠ 0 → addressSlotReadWord (b.getStorVal sevm.currentTarget (mapSlot t 3)) ≠ 0 →
      Apart (mapSlot (addressSlotReadWord (b.getStorVal sevm.currentTarget (mapSlot t 3))) 2))
    (hfanp : t ≠ 0 → np ≠ 0 → Apart (mapSlot np 2))
    (hmid : t ≠ 0 → ∀ {b' : Devm} {M' : Mem} {G' : Nat} {post : Devm},
      Devm.getStor b' sevm.currentTarget = Devm.getStor b sevm.currentTarget → MemOK M' →
      SFunc.Run prog sevm (St b' (np :: t :: 3 :: 0x3c2 ::
        addressSlotReadWord (b.getStorVal sevm.currentTarget (mapSlot t 3)) :: np :: t :: ra :: xs)
        M' G') t_0934_c32 (.returned post) →
      Φ (Devm.getStor post sevm.currentTarget) ∧
      ∃ b2 M2 G2, post = St b2
        (addressSlotReadWord (b.getStorVal sevm.currentTarget (mapSlot t 3)) :: np :: t :: ra :: xs)
        M2 G2)
    (run : SFunc.Run prog sevm (St b (np :: t :: ra :: xs) M G) t_031c_c21 (.returned D)) :
    Φ (Devm.getStor D sevm.currentTarget) := by
  have run := run.cut
  unfold t_031c_c21 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_caller s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_and s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_eq s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G7, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G8, run⟩ | ⟨-, G8, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run (by decide)).elim
  unfold t_038b_c21 at run
  obtain ⟨G9, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G10, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G11, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G12, rfl⟩ := ri_dup (w := t) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G13, rfl⟩ := ri_and s1
  rw [mask_and_canonical ht] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G14, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G15, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G16, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G17, rfl⟩ := ri_mstore s1
  dsimp only [List.set] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G18, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G19, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G20, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G21, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G22, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G23, rfl⟩ := ri_keccak s1
  simp only [show (Bytes.toB256 [] : B256) = 0 from rfl,
    show (Bytes.toB256 [32] : B256) = 32 from rfl,
    show (Bytes.toB256 [64] : B256) = 64 from rfl,
    show (Bytes.toB256 [3] : B256) = 3 from rfl,
    show (0 : B256).toNat = 0 from rfl,
    show (32 : B256).toNat = 32 from rfl,
    show (64 : B256).toNat = 64 from rfl] at run
  have hscr := scratch_mapSlot hmem.1 hmem.2 t 3
  rw [hscr.1, hscr.2.1] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G24, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G25, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G26, rfl⟩ := ri_swap (n := 1) rfl s1
  dsimp only [List.set] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G27, rfl⟩ := ri_and s1
  rw [ff20_and_eq_read] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G28, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G29, rfl⟩ := ri_pop s1
  dsimp only [List.set] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G30, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G31, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G32, rfl⟩ := ri_dup (w := t) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G33, rfl⟩ := ri_dup (w := np) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G34, rfl⟩ := ri_push s1
  obtain ⟨G35, hcall⟩ := ric_call (g := t_0934_c32) rfl run
  rcases hcall with ⟨D32, r32, run⟩ | ⟨D32, -, hh⟩
  swap
  · cases hh
  rw [show (Bytes.toB256 [3] : B256) = 3 from rfl,
    show (Bytes.toB256 [0x03, 0xc2] : B256) = 0x3c2 from rfl] at r32
  by_cases ht0 : t = 0
  · subst ht0; exact (entry32_zero_false r32).elim
  obtain ⟨hinv2, b2, M2, G36, rfl⟩ :=
    hmid ht0 (afterSload_getStor _ _ _ _) ⟨hscr.2.2.1, hscr.2.2.2⟩ r32
  set p0 := addressSlotReadWord (b.getStorVal sevm.currentTarget (mapSlot t 3)) with hp0def
  have hp0c : canonicalAddress p0 := by
    rw [hp0def, addressSlotReadWord_eq_toAdr_toB256]
    exact canonical_toAdr_toB256 _
  have hfaOld : p0 ≠ 0 → Apart (mapSlot p0 2) := hfa0 ht0
  -- `t_03c2_c21`: test the previous pauser
  unfold t_03c2_c21 at run
  obtain ⟨G37, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G38, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G39, rfl⟩ := ri_dup (w := p0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G40, rfl⟩ := ri_and s1
  rw [mask_and_canonical hp0c] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G41, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G42, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G43, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G44, rfl⟩ := ri_swap (n := 0) rfl s1
  dsimp only [List.set] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G45, rfl⟩ := ri_push s1
  rcases ric_branchTo (k := 2) (g := t_0409_c2) (List.not_mem_nil) rfl run with
    ⟨hz, G46, run⟩ | ⟨hnz, G46, run⟩
  · -- a previous pauser: `t_03e2_c21` reads its remaining count, then entry 2's head
    have hp0nz : p0 ≠ 0 := by
      intro h; rw [h] at hz; exact absurd hz (by decide)
    unfold t_03e2_c21 at run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G47, rfl⟩ := ri_pop s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G48, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G49, rfl⟩ := ri_dup (w := p0) rfl s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G50, rfl⟩ := ri_and s1
    rw [mask_and_canonical hp0c] at run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G51, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G52, rfl⟩ := ri_swap (n := 0) rfl s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G53, rfl⟩ := ri_dup rfl s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G54, rfl⟩ := ri_mstore s1
    dsimp only [List.set] at run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G55, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G56, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G57, rfl⟩ := ri_mstore s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G58, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G59, rfl⟩ := ri_swap (n := 0) rfl s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G60, rfl⟩ := ri_keccak s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G61, rfl⟩ := ri_sload hfork s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G62, rfl⟩ := ri_iszero s1
    refine t0409_preserves hΦ hfork hp0c hnp (fun _ => hfaOld hp0nz) (hfanp ht0) ?_ run
    rw [afterSload_getStor]
    exact hinv2
  · -- no previous pauser: entry 2 skips its heartbeat
    have hp00 : p0 = 0 := eq_of_eqCheck_ne hnz
    refine t0409_preserves hΦ hfork hp0c hnp (fun h => absurd ?_ h) (hfanp ht0) hinv2 run
    rw [hp00]; decide

/-- **The `registerPauser(t, np)` body (entry 21)**, from well-formed memory and
the frame-entry witness, given `registerPauser`'s collision premise for that
witness: any storage predicate `Φ` stable under off-Registry writes that holds
after every successful entry-32 run from the call state holds at the end. -/
theorem entry21_foreign {Φ : Stor → Prop}
    (hΦ : ∀ {s : Stor} {w v : B256}, ForeignApart (2 ^ 160) w → Φ s → Φ (s.set w v))
    {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {np t ra : B256}
    {xs : List B256} {D : Devm} {entries : List Entry}
    (hfork : CoveredFork sevm.benvStat.fork) (hmem : MemOK M)
    (hw : RegistryWitness (solRegistryStorage (Devm.getStor b sevm.currentTarget)) entries)
    (ht : canonicalAddress t) (hnp : canonicalAddress np)
    (hA : t ≠ 0 → RegisterPauserApart entries t np)
    (hmid : ∀ {b' : Devm} {M' : Mem} {G' : Nat} {post : Devm},
      Devm.getStor b' sevm.currentTarget = Devm.getStor b sevm.currentTarget → MemOK M' →
      SFunc.Run prog sevm (St b' (np :: t :: 3 :: 0x3c2 ::
        addressSlotReadWord (b.getStorVal sevm.currentTarget (mapSlot t 3)) :: np :: t :: ra :: xs)
        M' G') t_0934_c32 (.returned post) →
      Φ (Devm.getStor post sevm.currentTarget))
    (run : SFunc.Run prog sevm (St b (np :: t :: ra :: xs) M G) t_031c_c21 (.returned D)) :
    Φ (Devm.getStor D sevm.currentTarget) := by
  refine entry21_preserves hΦ hfork hmem ht hnp ?_ ?_ ?_ run
  · intro ht0 hp0
    have heq : addressSlotReadWord (b.getStorVal sevm.currentTarget (mapSlot t 3)) =
        assignmentAt entries t := by
      have h := hw.assignments t ht
      rw [solRegistryStorage_assignment _ _ ht] at h
      exact h
    rw [heq] at hp0 ⊢
    exact (hA ht0).2.1 hp0
  · intro ht0
    exact (hA ht0).2.2
  · intro ht0 b' M' G' post hs hm r
    have hw1 : RegistryWitness (solRegistryStorage (Devm.getStor b' sevm.currentTarget)) entries := by
      rw [hs]; exact hw
    have h := hmid hs hm r
    obtain ⟨-, b2, M2, G2, hpost⟩ :=
      setPauser_step hfork hm hw1 ht hnp (fun _ => (hA ht0).1) r
    exact ⟨h, b2, M2, G2, hpost⟩

/-! ## The `registerPauser` selector wrapper (entry 59) -/

private instance : Inhabited SFunc := ⟨.undefined⟩

/-- **The `registerPauser(address,address)` wrapper (entry 59)**, for any storage
predicate `Φ` stable under off-Registry writes that every successful entry-32
run of `setPauser(t, np)` (from the frame's storage and well-formed memory)
establishes. -/
theorem registerPauser_wrapper_of_body {Φ : Stor → Prop}
    {sevm : Sevm} {d : Devm} {o : Outcome} {w : SFunc}
    (hw : prog[59]? = some w)
    (hbody : canonicalAddress (Sevm.dataWord sevm 4) → canonicalAddress (Sevm.dataWord sevm 36) →
      ∀ G D, SFunc.Run prog sevm
        (St d (Sevm.dataWord sevm 36 :: Sevm.dataWord sevm 4 :: Bytes.toB256 [0x01, 0xba] :: d.stack)
          d.memory G) t_031c_c21 (.returned D) → Φ (Devm.getStor D sevm.currentTarget))
    (run : SFunc.Run prog sevm d w o) :
    Φ (Devm.getStor (Outcome.devm o) sevm.currentTarget) := by
  rw [show prog[59]? = some t_01a7_c59 from rfl] at hw
  cases hw
  rw [St.self (d := d) rfl rfl] at run
  have run := run.cut
  unfold t_01a7_c59 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_calldatasize s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_push s1
  obtain ⟨G7, hcall⟩ := ric_call (g := t_0fbb_c20) rfl run
  rcases hcall with ⟨D20, r20, run⟩ | ⟨D20, r20, -⟩
  swap
  · exact (SFunc.RunP.not_halted_entry writerNoHalt_set (k := 20) (by decide) rfl r20 rfl).elim
  rw [show (Bytes.toB256 [0x04] : B256) = 4 from rfl] at r20
  obtain ⟨ht, hnp, G8, rfl⟩ := entry20_ret r20
  unfold t_01b5_c59 at run
  obtain ⟨G9, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G10, rfl⟩ := ri_push s1
  obtain ⟨G11, hcall⟩ := ric_call (g := t_031c_c21) rfl run
  rcases hcall with ⟨D21, r21, run⟩ | ⟨D21, r21, -⟩
  swap
  · exact (SFunc.RunP.not_halted_entry writerNoHalt_set (k := 21) (by decide) rfl r21 rfl).elim
  have hinv := hbody ht hnp G11 D21 r21
  have hst := SFunc.Run.state_of_silent (S := []) rfl (by decide) (by decide) run.uncut
  rw [getStor_eq_of_state_eq hst]
  exact hinv

theorem registerPauser_wrapper_foreign {Φ : Stor → Prop}
    (hΦ : ∀ {s : Stor} {w v : B256}, ForeignApart (2 ^ 160) w → Φ s → Φ (s.set w v))
    {sevm : Sevm} {d : Devm} {o : Outcome} {w : SFunc} {entries : List Entry}
    (hfork : CoveredFork sevm.benvStat.fork) (hw : prog[59]? = some w)
    (hA : EntryAt lidoA sevm d) (hmem : MemOK d.memory)
    (hwit : RegistryWitness (solRegistryStorage (Devm.getStor d sevm.currentTarget)) entries)
    (hmid : canonicalAddress (Sevm.dataWord sevm 4) → canonicalAddress (Sevm.dataWord sevm 36) →
      Sevm.dataWord sevm 4 ≠ 0 → ∀ {b' : Devm} {M' : Mem} {G' : Nat} {base : List B256}
      {post : Devm},
      Devm.getStor b' sevm.currentTarget = Devm.getStor d sevm.currentTarget → MemOK M' →
      SFunc.Run prog sevm (St b' (Sevm.dataWord sevm 36 :: Sevm.dataWord sevm 4 :: 3 :: 0x3c2 ::
        base) M' G') t_0934_c32 (.returned post) →
      Φ (Devm.getStor post sevm.currentTarget))
    (run : SFunc.Run prog sevm d w o) :
    Φ (Devm.getStor (Outcome.devm o) sevm.currentTarget) := by
  have hAe := hA entries hwit
  refine registerPauser_wrapper_of_body hw ?_ run
  intro ht hnp G D r21
  exact entry21_foreign hΦ hfork hmem hwit ht hnp (fun ht0 => hAe.1 ⟨ht0, ht⟩ hnp)
    (fun hs hm r => by
      by_cases ht0 : Sevm.dataWord sevm 4 = 0
      · rw [ht0] at r; exact (entry32_zero_false r).elim
      exact hmid ht hnp ht0 hs hm r) r21

/-- **`registerPauser(address,address)` (wrapper 59) establishes the frame
postcondition**: the `registerPauser` field of `LidoWriterSpecsM lidoA`. -/
theorem registerPauser_wrapper_post {sevm : Sevm} {d : Devm} {o : Outcome} {w : SFunc}
    (hfork : CoveredFork sevm.benvStat.fork) (hw : prog[59]? = some w)
    (_hloc : LocalApart sevm) (hA : EntryAt lidoA sevm d) (hmem : MemOK d.memory)
    (hpre : lidoSpec.Pre sevm.currentTarget sevm d) (run : SFunc.Run prog sevm d w o) :
    lidoSpec.Post sevm.currentTarget sevm (Outcome.devm o) := by
  obtain ⟨entries, hwit⟩ : RegInv (Devm.getStor d sevm.currentTarget) := hpre.inv.left rfl
  have hAe := hA entries hwit
  have h : RegInv (Devm.getStor (Outcome.devm o) sevm.currentTarget) :=
    registerPauser_wrapper_foreign (Φ := RegInv) (fun hfa h => RegInv.set_foreign hfa h)
      hfork hw hA hmem hwit
      (fun ht hnp ht0 _ _ _ _ _ hs hm r =>
        (setPauser_step hfork hm (by rw [hs]; exact hwit) ht hnp
          (fun _ => (hAe.1 ⟨ht0, ht⟩ hnp).1) r).1) run
  exact ⟨trivial, h⟩

end Blanc.Lift.LidoCircuitBreakerDeployed
