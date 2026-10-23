import Blanc.Lift.UniswapV2Pair.GetterScalarWalk
import Blanc.Lift.HistAccessWalk
import Blanc.HistoricalFork

/-!
# The Pair's scalar getters under historical fork rules

The pattern for the Pair's historical exact walks (L4.1/L4.3): the modern inversion chain
`getterScalar_bytecode_refines` takes `CoveredFork` only to run `ri_sload` with Prague access
rules. Here the same chain runs on the actual access schedule (`afterSloadH`, `ri_sloadH`) from
the two rule facts it reads, `rules.stateGas = none` (the carrier's `lift_sound_noStateGas`) and
`rules.bal = none`, so it holds on every `HistFork`: flat-access Muir Glacier, where the Pair was
deployed, as well as the EIP-2929 forks after Berlin. No equality with modern execution is used.

* `ScalarGetter.afterH` — the getter's successor base under the actual access schedule;
* `getterScalar_bytecode_refinesH` — a successful Pair frame at pc zero refines the source scalar
  getter, from the two rule facts;
* `token0_bytecode_refines_hist` — the `token0()` instance on a historical fork.
-/

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The scalar getter's successor base under the frame's actual access schedule. -/
def ScalarGetter.afterH (s : ScalarGetter) (sevm : Sevm) (b : Devm) : Devm :=
  match s with
  | .constant _ => b
  | .stored s => afterSloadH sevm b s.slot
  | .address s => afterSloadH sevm b s.slot

theorem ScalarGetter.afterH_storage (s : ScalarGetter) (sevm : Sevm) (b : Devm) (a : Adr) :
    Devm.getStor (s.afterH sevm b) a = Devm.getStor b a := by
  cases s with
  | constant _ => rfl
  | stored _ => exact afterSloadH_getStor _ _ _ _
  | address _ => exact afterSloadH_getStor _ _ _ _

theorem ScalarGetter.afterH_logs (s : ScalarGetter) (sevm : Sevm) (b : Devm) :
    (s.afterH sevm b).logs = b.logs := by
  cases s with
  | constant _ => rfl
  | stored _ => exact afterSloadH_logs _ _ _
  | address _ => exact afterSloadH_logs _ _ _

theorem storedScalar_callee_invH {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {ρ : B256} {o : Outcome} (s : StoredScalar)
    (bal : sevm.benvStat.rules.bal = none)
    (run : SFunc.Run fs sevm (St b (ρ :: R) M G) s.callee o) :
    ∃ G', o = .returned (St (afterSloadH sevm b s.slot)
      (b.getStorVal sevm.currentTarget s.slot :: ρ :: R) M G') := by
  have h := run.cut
  rw [s.callee_shape] at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_sloadH bal hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := ρ) rfl hd
  obtain ⟨g, hg⟩ := ric_ret h
  exact ⟨g, Seg.done.inj hg⟩

theorem addressScalar_callee_invH {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {ρ : B256} {o : Outcome} (s : AddressScalar)
    (bal : sevm.benvStat.rules.bal = none)
    (run : SFunc.Run fs sevm (St b (ρ :: R) M G) s.callee o) :
    ∃ G', o = .returned (St (afterSloadH sevm b s.slot)
      ((b.getStorVal sevm.currentTarget s.slot).toAdr.toB256 :: ρ :: R) M G') := by
  have h := run.cut
  rw [s.callee_shape] at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_sloadH bal hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_and hd
  change d = St (afterSloadH sevm b s.slot)
    ((Bytes.toB256 (List.replicate 20 0xff) &&& b.getStorVal sevm.currentTarget s.slot) ::
      ρ :: R) M _ at hd
  rw [show Bytes.toB256 (List.replicate 20 0xff) = ~~~ addressMask from by decide,
    show ((~~~ addressMask) &&& b.getStorVal sevm.currentTarget s.slot) =
      (b.getStorVal sevm.currentTarget s.slot).toAdr.toB256 from
        addressSlotReadWord_eq_toAdr_toB256 _] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := ρ) rfl hd
  obtain ⟨g, hg⟩ := ric_ret h
  exact ⟨g, Seg.done.inj hg⟩

theorem getterScalar_callee_invH {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {ρ : B256} {o : Outcome}
    (s : ScalarGetter) (bal : sevm.benvStat.rules.bal = none)
    (run : SFunc.Run fs sevm (St b (ρ :: R) M G) s.callee o) :
    ∃ G', o = .returned (St (s.afterH sevm b) (s.value sevm b :: ρ :: R) M G') := by
  cases s with
  | constant s => exact constantScalar_callee_inv s run
  | stored s => exact storedScalar_callee_invH s bal run
  | address s => exact addressScalar_callee_invH s bal run

/-- The getter tail over an arbitrary successor base `b'`: the tail reads no storage. -/
theorem getterScalar_tail_inv_base {fs : List SFunc} {sevm : Sevm} {b b' : Devm}
    {R : List B256} {M : Mem} {G : Nat} {o : Outcome} (s : ScalarGetter)
    (mem : PtrMem 128 96 M)
    (run : SFunc.Run fs sevm (St b' (s.value sevm b :: R) M G) s.tailTree o) :
    ∃ d, o = .halted d ∧ d.output = (s.value sevm b).toBytes ∧
      (∀ a, Devm.getStor d a = Devm.getStor b' a) ∧ d.logs = b'.logs := by
  cases s with
  | constant s =>
    cases s with
    | decimals =>
      exact getterMasked_tail_inv .decimals (by change (18 : B256) &&& 255 = 18; decide) mem run
    | minimumLiquidity => exact getterWord_tail_inv mem run
    | permitTypehash => exact getterWord_tail_inv mem run
  | stored s => exact getterWord_tail_inv mem run
  | address s =>
    refine getterMasked_tail_inv .address ?_ mem run
    rw [B256.and_comm]
    exact ff20_and_adr _

theorem getterScalar_entry_invH {sevm : Sevm} {b : Devm}
    {M : Mem} {G : Nat} {sel : B256} {o : Outcome} (s : ScalarGetter)
    (bal : sevm.benvStat.rules.bal = none) (mem : PtrMem 128 96 M)
    (run : SFunc.Run cert.prog sevm (St b [sel] M G) s.entryTree o) :
    ∃ d, o = .halted d ∧ d.output = (s.value sevm b).toBytes ∧
      (∀ a, Devm.getStor d a = Devm.getStor b a) ∧ d.logs = b.logs := by
  have h := run.cut
  rw [s.entry_shape] at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨_, h⟩ := ric_call s.callee_lookup h
  rcases h with ⟨d, hc, h⟩ | ⟨d, hc, _⟩
  · obtain ⟨_, eq⟩ := getterScalar_callee_invH s bal hc
    cases eq
    obtain ⟨d, ho, hout, hs, hl⟩ := getterScalar_tail_inv_base s mem h.uncut
    exact ⟨d, ho, hout, fun a => (hs a).trans (s.afterH_storage sevm b a),
      hl.trans (s.afterH_logs sevm b)⟩
  · obtain ⟨_, eq⟩ := getterScalar_callee_invH s bal hc
    cases eq

theorem getterScalar_pc0_invH {sevm : Sevm} {b post : Devm} {G : Nat}
    (s : ScalarGetter) (bal : sevm.benvStat.rules.bal = none)
    (selector : Blanc.Sevm.selector sevm = s.selector)
    (run : SProg.Run cert.prog sevm (St b [] Mem.empty G) post) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      post.output = (s.value sevm b).toBytes ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  obtain ⟨f, entry, run⟩ := run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨value, size, _, run⟩ := getter_guards_inv run
  obtain ⟨_, run⟩ := getterScalar_selector_inv s selector run
  obtain ⟨d, eq, out, stor, logs⟩ := getterScalar_entry_invH s bal getterInitMemory_ptr run
  cases eq
  exact ⟨value, size, out, stor, logs⟩

/-- **Scalar getters, historical rules.**  A successful Pair frame at pc zero whose selector is a
scalar getter refines the source getter, leaving storage and logs unchanged, from
`rules.stateGas = none` and `rules.bal = none` alone (any access schedule). -/
theorem getterScalar_bytecode_refinesH {sevm : Sevm} {b post : Devm} {G : Nat} {st : State}
    (s : ScalarGetter) (codeEq : sevm.code = code)
    (stateGas : sevm.benvStat.rules.stateGas = none) (bal : sevm.benvStat.rules.bal = none)
    (selector : Blanc.Sevm.selector sevm = s.selector)
    (slots : s.SlotMatches st sevm b)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      some post.output = getterResult st s.entry ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  obtain ⟨value, size, out, stor, logs⟩ :=
    getterScalar_pc0_invH s bal selector (lift_sound_noStateGas cert_check codeEq stateGas run)
  refine ⟨value, size, ?_, stor, logs⟩
  rw [s.source_value slots, out]

/-- `token0()` on any historical fork, including the Pair's Muir Glacier deployment fork. -/
theorem token0_bytecode_refines_hist {sevm : Sevm} {b post : Devm} {G : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : HistFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xdfe1681)
    (slots : st.token0 = (b.getStorVal sevm.currentTarget 6).toAdr)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      some post.output = getterResult st .token0 ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs :=
  getterScalar_bytecode_refinesH (.address .token0) codeEq fork.stateGas_none fork.bal_none
    selector slots run

end Blanc.Lift.UniswapV2Pair
