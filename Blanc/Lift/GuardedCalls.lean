import Blanc.Lift.SpawnKindsM
import Blanc.CallSpawnExact
import Blanc.ForwardCall
import Blanc.Lift.FrameWalk
import Blanc.Lift.InvWalkGas
import Blanc.Lift.ReturnDataBound
import Blanc.ExecutionCodeAt

/-!
# Flag-guarded calls: the children of a successful frame commit

A frame whose code tests the success flag of every call it makes (a failed call falls through to a
`REVERT`) cannot succeed after a child that did not commit.  This module states that discipline as a
byte-level fact about the code and proves its consequence for any successful derivation.

* `guardCheck code`: a linear walk over the instruction starts (stepping over `PUSH` immediates, as
  `callKindsCheck` does, reading `code.data.toList`) admitting at every start an external
  instruction only if it is `CALL` or `STATICCALL` and either
  - **flag-guarded**: the next bytes are `PUSH2 _ _; JUMPI; PUSH1 0; DUP1; REVERT`, so a zero flag
    falls through to the `REVERT`; or
  - **an identity copy**: the previous two instruction starts are `GAS` and `PUSH1 4`, so the target
    word is `4`.
* `guardCheck_sound`: what the walk guarantees at every reached position (`PushReach`);
* `Exec.rawFrameDescendants_of_guardCheck` (and its entry form `…_entry`): in a successful
  derivation of checked code, every raw frame descendant lies under a direct committed child —
  a child that did not commit leaves the flag `0`, which a guarded site reverts on, and an identity
  copy (target word `4`, tracked by `IdGuard` along the chain, the linear walk's predecessors being
  unique: `PushReach.succ_inj`) enters no code frame while the code at `4` is undelegated.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-! ## The walk -/

/-- The bytes after a flag-guarded call (the list starts at the call byte):
`PUSH2 _ _; JUMPI; PUSH1 0; DUP1; REVERT`. -/
def guardedAfter : List UInt8 → Bool
  | _ :: b1 :: _ :: _ :: b4 :: b5 :: b6 :: b7 :: b8 :: _ =>
    b1 == 0x61 && b4 == 0x57 && b5 == 0x60 && b6 == 0x00 && b7 == 0x80 && b8 == 0xfd
  | _ => false

/-- One instruction start at `pos` (byte `b`, bytes from it `xs`), whose two previous instruction
starts are `p1` and `p2`. -/
def guardSiteOk (full xs : List UInt8) (b : UInt8) (pos p1 p2 : Nat) : Bool :=
  b != 0xe6 && b != 0xe7 && b != 0xe8 &&
  match b.toXinst with
  | none => true
  | some x =>
    (x == .call || x == .staticcall) &&
      (guardedAfter xs ||
        (b == 0xf1 && p1 + 1 == pos && p2 + 2 == p1 && full[p1]? == some 0x5a &&
          full[p2]? == some 0x60 && full[p2 + 1]? == some 0x04))

/-- The linear instruction walk: `skip` immediate bytes still to pass, `p1`, `p2` the two previous
instruction starts. -/
def guardWalk (full : List UInt8) : List UInt8 → Nat → Nat → Nat → Nat → Bool
  | [], _, _, _, _ => true
  | b :: bs, pos, 0, p1, p2 =>
    guardSiteOk full (b :: bs) b pos p1 p2 && guardWalk full bs (pos + 1) (pushWidth b) pos p1
  | _ :: bs, pos, skip + 1, p1, p2 => guardWalk full bs (pos + 1) skip p1 p2

/-- **The flag-guard check** (see the module note). -/
def guardCheck (code : ByteArray) : Bool :=
  guardWalk code.data.toList code.data.toList 0 0 (code.size + 5) (code.size + 5)

/-! ## Soundness -/

/-- The successor of an instruction start on the linear walk. -/
abbrev pushSucc (cd : ByteArray) (p : Nat) (hp : p < cd.size) : Nat := p + 1 + pushWidth cd[p]

theorem guardWalk_drop (full : List UInt8) :
    ∀ (skip : Nat) (xs : List UInt8) (pos p1 p2 : Nat),
      guardWalk full xs pos skip p1 p2 = true →
      guardWalk full (xs.drop skip) (pos + skip) 0 p1 p2 = true
  | 0, _, _, _, _, h => h
  | _ + 1, [], _, _, _, _ => rfl
  | skip + 1, _ :: xs, pos, p1, p2, h => by
    have := guardWalk_drop full skip xs (pos + 1) p1 p2 h
    rwa [show pos + 1 + skip = pos + (skip + 1) by omega] at this

/-- What the walk records at an instruction start `j`: each of the two previous starts is the
sentinel `cd.size + 5` or a reached start whose successor is the next one. -/
def GuardInv (cd : ByteArray) (j p1 p2 : Nat) : Prop :=
  (p1 = cd.size + 5 ∨ ∃ hp : p1 < cd.size, PushReach cd p1 ∧ pushSucc cd p1 hp = j) ∧
    (p2 = cd.size + 5 ∨ ∃ hp : p2 < cd.size, PushReach cd p2 ∧ pushSucc cd p2 hp = p1)

theorem guardWalk_reach {cd : ByteArray} (h : guardCheck cd = true) :
    ∀ j, PushReach cd j → ∃ p1 p2,
      guardWalk cd.data.toList (cd.data.toList.drop j) j 0 p1 p2 = true ∧ GuardInv cd j p1 p2 := by
  have hlen : cd.data.toList.length = cd.size := Array.length_toList
  intro j hj
  induction hj with
  | zero => exact ⟨_, _, h, .inl rfl, .inl rfl⟩
  | @step p hp hreach ih =>
    obtain ⟨p1, p2, hw, hinv1, -⟩ := ih
    refine ⟨p, p1, ?_, .inr ⟨hp, hreach, rfl⟩, ?_⟩
    · rw [List.drop_eq_getElem_cons (hlen ▸ hp)] at hw
      simp only [guardWalk, Bool.and_eq_true] at hw
      have hd := guardWalk_drop _ _ _ _ _ _ hw.2
      rw [List.drop_drop] at hd
      have hg : cd.data.toList[p]'(hlen ▸ hp) = cd[p] := rfl
      rw [hg] at hd
      simpa only [Nat.add_comm (pushWidth cd[p]) (p + 1)] using hd
    · rcases hinv1 with e | ⟨hp1, hr1, hs1⟩
      · exact .inl e
      · exact .inr ⟨hp1, hr1, hs1⟩

/-- An identity copy at `q`: the previous two instruction starts are `GAS` at `q - 1` and
`PUSH1 4` at `q - 3`, each the predecessor of the next on the linear walk. -/
def IdCopyAt (cd : ByteArray) (q : Nat) : Prop :=
  ∃ (h1 : q - 1 < cd.size) (h3 : q - 3 < cd.size), 3 ≤ q ∧ cd.data.toList[q]? = some 0xf1 ∧
    PushReach cd (q - 1) ∧ pushSucc cd (q - 1) h1 = q ∧ cd[q - 1] = 0x5a ∧
    PushReach cd (q - 3) ∧ pushSucc cd (q - 3) h3 = q - 1 ∧ cd[q - 3] = 0x60 ∧
    cd.data.toList[q - 2]? = some 0x04

/-- The walk's verdict at a reached instruction start. -/
theorem guardCheck_site {cd : ByteArray} (h : guardCheck cd = true) {q : Nat}
    (hr : PushReach cd q) (hq : q < cd.size) : ∃ p1 p2,
      guardSiteOk cd.data.toList (cd.data.toList.drop q) cd[q] q p1 p2 = true ∧
        GuardInv cd q p1 p2 := by
  have hlen : cd.data.toList.length = cd.size := Array.length_toList
  obtain ⟨p1, p2, hw, hinv⟩ := guardWalk_reach h q hr
  rw [List.drop_eq_getElem_cons (hlen ▸ hq)] at hw
  simp only [guardWalk, Bool.and_eq_true] at hw
  refine ⟨p1, p2, ?_, hinv⟩
  rw [List.drop_eq_getElem_cons (hlen ▸ hq)]
  exact hw.1

/-- **No reached instruction start holds an `EIP-8024` immediate-taking opcode.** -/
theorem guardCheck_noImm {cd : ByteArray} (h : guardCheck cd = true) {q : Nat}
    (hr : PushReach cd q) (hq : q < cd.size) :
    cd[q] ≠ 0xe6 ∧ cd[q] ≠ 0xe7 ∧ cd[q] ≠ 0xe8 := by
  obtain ⟨p1, p2, hs, -⟩ := guardCheck_site h hr hq
  simp only [guardSiteOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hs
  exact ⟨hs.1.1.1, hs.1.1.2, hs.1.2⟩

/-- **What the walk guarantees at a reached external instruction** (see the module note). -/
theorem guardCheck_sound {cd : ByteArray} (h : guardCheck cd = true) {q : Nat} {x : Xinst}
    (hr : PushReach cd q) (hx : Xinst.At cd q x) :
    (x = .call ∨ x = .staticcall) ∧
      (guardedAfter (cd.data.toList.drop q) = true ∨ (x = .call ∧ IdCopyAt cd q)) := by
  have hlen : cd.data.toList.length = cd.size := Array.length_toList
  obtain ⟨hq, hbyte⟩ := getInst_exec_toXinst hx
  obtain ⟨p1, p2, hs, hinv1, hinv2⟩ := guardCheck_site h hr hq
  simp only [guardSiteOk, hbyte, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hs
  replace hs := hs.2
  refine ⟨hs.1, ?_⟩
  rcases hs.2 with hga | ⟨⟨⟨⟨⟨hc, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩
  · exact .inl hga
  · right
    have hcall : x = .call := by
      rw [hc] at hbyte
      exact (Option.some.inj hbyte).symm.trans rfl
    refine ⟨hcall, ?_⟩
    rcases hinv1 with e1 | ⟨hp1, hr1, hs1⟩
    · omega
    rcases hinv2 with e2 | ⟨hp2, hr2, hs2⟩
    · omega
    have e1 : p1 = q - 1 := by omega
    have e2 : p2 = q - 3 := by omega
    subst e1 e2
    have b1 : cd[q - 1] = 0x5a := by
      rw [List.getElem?_eq_getElem (hlen ▸ hp1)] at h3
      exact Option.some.inj h3
    have b2 : cd[q - 3] = 0x60 := by
      rw [List.getElem?_eq_getElem (hlen ▸ hp2)] at h4
      exact Option.some.inj h4
    exact ⟨hp1, hp2, by omega, by rw [List.getElem?_eq_getElem (hlen ▸ hq)]; exact congrArg some hc, hr1, hs1, b1,
      hr2, hs2, b2, by rw [← h5]; congr 1; omega⟩

/-! ## The linear walk has unique predecessors -/

/-- No reached start lies strictly inside the span of another reached start `r`. -/
theorem PushReach.not_inside {cd : ByteArray} {r : Nat} (hr : r < cd.size)
    (below : ∀ {p} (hp : p < cd.size), PushReach cd p → p < r → pushSucc cd p hp ≤ r) :
    ∀ {p}, PushReach cd p → ¬ (r < p ∧ p < pushSucc cd r hr) := by
  intro p hp
  induction hp with
  | zero => omega
  | @step s hs hsr ih =>
    intro ⟨h1, h2⟩
    by_cases hlt : s < r
    · have := below hs hsr hlt
      simp only [pushSucc] at this h1
      omega
    · by_cases hse : s = r
      · subst hse
        simp only [pushSucc] at h2
        omega
      · exact ih ⟨by omega, by simp only [pushSucc] at h2 ⊢; omega⟩

/-- **Two reached starts in order**: the first's successor is at most the second. -/
theorem PushReach.succ_le {cd : ByteArray} :
    ∀ p', PushReach cd p' → ∀ {p} (hp : p < cd.size), PushReach cd p → p < p' →
      pushSucc cd p hp ≤ p' := by
  intro p'
  induction p' using Nat.strong_induction_on with
  | _ p' ih =>
    intro hp' p hp hpr hlt
    cases hp' with
    | zero => omega
    | @step r hr hreach =>
      have below : ∀ {q} (hq : q < cd.size), PushReach cd q → q < r → pushSucc cd q hq ≤ r :=
        fun hq hqr hl => ih r (by omega) hreach hq hqr hl
      by_cases hpr' : p < r
      · have := below hp hpr hpr'
        omega
      · by_cases hpe : p = r
        · subst hpe; exact Nat.le_refl _
        · exact absurd ⟨by omega, hlt⟩ (PushReach.not_inside hr below hpr)

/-- **The linear walk has unique predecessors.** -/
theorem PushReach.succ_inj {cd : ByteArray} {p q : Nat} (hp : p < cd.size) (hq : q < cd.size)
    (hpr : PushReach cd p) (hqr : PushReach cd q) (h : pushSucc cd p hp = pushSucc cd q hq) :
    p = q := by
  rcases Nat.lt_trichotomy p q with hl | he | hg
  · have := PushReach.succ_le q hqr hp hpr hl
    simp only [pushSucc] at this h
    omega
  · exact he
  · have := PushReach.succ_le p hpr hq hqr hg
    simp only [pushSucc] at this h
    omega

/-! ## Where a continued step lands -/

theorem pushWidth_of_p (b : UInt8) (h : b.toInstType = .P) : b.toNat - 95 = pushWidth b := by
  have key : ∀ n : Fin 256, (UInt8.ofNat n.val).toInstType = .P →
      (UInt8.ofNat n.val).toNat - 95 = pushWidth (UInt8.ofNat n.val) := by decide +kernel
  have := key ⟨b.toNat, b.toNat_lt⟩
  rw [UInt8.ofNat_toNat] at this
  exact this h

theorem pushWidth_of_ne_p (b : UInt8) (h : b.toInstType ≠ .P) : pushWidth b = 0 := by
  have key : ∀ n : Fin 256, (UInt8.ofNat n.val).toInstType ≠ .P →
      pushWidth (UInt8.ofNat n.val) = 0 := by decide +kernel
  have := key ⟨b.toNat, b.toNat_lt⟩
  rw [UInt8.ofNat_toNat] at this
  exact this h

/-- An ordinary instruction decoded at `pc`, not an `EIP-8024` immediate-taking one, spans
`1 + pushWidth`. -/
theorem getInst_next_size {cd : ByteArray} {pc : Nat} {n : Ninst}
    (h : cd.getInst pc = some (.next n)) (hpc : pc < cd.size)
    (hne : cd[pc] ≠ 0xe6 ∧ cd[pc] ≠ 0xe7 ∧ cd[pc] ≠ 0xe8) :
    n.size = 1 + pushWidth cd[pc] := by
  unfold ByteArray.getInst at h
  simp only [hpc, ↓reduceDIte] at h
  split at h
  · rename_i hty
    rw [pushWidth_of_ne_p _ (by rw [hty]; nofun)]
    split at h
    · rename_i heq _; exact absurd heq hne.1
    · rename_i heq _; exact absurd heq hne.2.1
    · rename_i heq _; exact absurd heq hne.2.2
    · cases hr : UInt8.toRinst cd[pc] with
      | none => simp only [Functor.mapRev, hr, Option.map_eq_map, Option.map_none,
        reduceCtorEq] at h
      | some r =>
        simp only [Functor.mapRev, hr, Option.map_eq_map, Option.map_some, Function.comp_apply,
          Option.some.injEq, Inst.next.injEq] at h
        subst h
        rfl
  · rename_i hty
    rw [pushWidth_of_ne_p _ (by rw [hty]; nofun)]
    cases hx : UInt8.toXinst cd[pc] with
    | none => simp only [Functor.mapRev, hx, Option.map_eq_map, Option.map_none,
      reduceCtorEq] at h
    | some x =>
      simp only [Functor.mapRev, hx, Option.map_eq_map, Option.map_some, Function.comp_apply,
        Option.some.injEq, Inst.next.injEq] at h
      subst h
      rfl
  · cases hj : UInt8.toJinst cd[pc] <;> simp only [Functor.mapRev, hj, Option.map_eq_map,
      Option.map_none, reduceCtorEq, Option.map_some, Option.some.injEq] at h
  · cases hl : UInt8.toLinst cd[pc] <;> simp only [Functor.mapRev, hl, Option.map_eq_map,
      Option.map_none, reduceCtorEq, Option.map_some, Option.some.injEq] at h
  · rename_i hty
    cases Option.some.inj h
    simp only [Ninst.size, ByteArray.length_sliceD]
    rw [← pushWidth_of_p _ hty]
    omega

/-- A jump destination the interpreter accepts holds `JUMPDEST`. -/
theorem jumpdest_of_jumpable {cd : ByteArray} {k : Nat} (h : jumpable cd k = true) :
    ∃ hk : k < cd.size, cd[k] = 0x5b := by
  unfold jumpable at h
  split at h
  · rename_i hk
    split at h
    · rename_i hb
      exact ⟨hk, hb⟩
    · cases h
  · cases h

/-- **Where a continued step lands**: at the next instruction start of the linear walk, or on a
`JUMPDEST`. -/
theorem Evm.step_cont_succ {cd : ByteArray} {pc : Nat} {sevm : Sevm} {devm : Devm} {pc' : Nat}
    {devm' : Devm} (h : Evm.step ⟨pc, sevm, devm⟩ = .cont pc' devm') (hcode : sevm.code = cd)
    (hpc : pc < cd.size) (hne : cd[pc] ≠ 0xe6 ∧ cd[pc] ≠ 0xe7 ∧ cd[pc] ≠ 0xe8) :
    pc' = pushSucc cd pc hpc ∨ ∃ hk : pc' < cd.size, cd[pc'] = 0x5b := by
  subst hcode
  unfold Evm.step at h
  cases hg : Evm.getInst ⟨pc, sevm, devm⟩ with
  | none => simp only [hg, reduceCtorEq] at h
  | some inst =>
    rw [hg] at h
    have hg' : sevm.code.getInst pc = some inst := hg
    cases inst with
    | next n =>
      have hp := Ninst.step_cont_pc h
      simp only at hp
      left
      rw [hp, getInst_next_size hg' hpc hne]
      simp only [pushSucc]
      omega
    | jump j =>
      obtain ⟨_, hty⟩ := getInst_jump_inv hg'
      have hw : pushWidth sevm.code[pc] = 0 := pushWidth_of_ne_p _ (by rw [hty]; nofun)
      have hsucc : pc + 1 = pushSucc sevm.code pc hpc := by simp only [pushSucc, hw]
      have hj := Step.ofJump_cont h
      cases j
      case jumpdest =>
        simp only [Jinst.run, Jinst.runCore] at hj
        rcases hc : chargeGas gJumpdest devm with e | d1
        · simp only [bind, Except.bind, hc, reduceCtorEq] at hj
        · simp only [bind, Except.bind, hc, Except.ok.injEq, Prod.mk.injEq] at hj
          exact .inl (hj.1.symm.trans hsucc)
      case jump =>
        simp only [Jinst.run, Jinst.runCore] at hj
        rcases hp : devm.pop with e | ⟨x, d1⟩
        · simp only [bind, Except.bind, hp, reduceCtorEq] at hj
        · rcases hc : chargeGas gMid d1 with e | d2
          · simp only [bind, Except.bind, hp, hc, reduceCtorEq] at hj
          · by_cases hjp : jumpable sevm.code x.toNat = true
            · simp only [bind, Except.bind, hp, hc, Except.assert, hjp, ↓reduceIte,
                Except.ok.injEq, Prod.mk.injEq] at hj
              rw [← hj.1]
              exact .inr (jumpdest_of_jumpable hjp)
            · simp only [bind, Except.bind, hp, hc, Except.assert, hjp, Bool.false_eq_true,
                ↓reduceIte, reduceCtorEq] at hj
      case jumpi =>
        simp only [Jinst.run, Jinst.runCore] at hj
        rcases hp : devm.pop with e | ⟨x, d1⟩
        · simp only [bind, Except.bind, hp, reduceCtorEq] at hj
        · rcases hp2 : d1.pop with e | ⟨y, d2⟩
          · simp only [bind, Except.bind, hp, hp2, reduceCtorEq] at hj
          · rcases hc : chargeGas gHigh d2 with e | d3
            · simp only [bind, Except.bind, hp, hp2, hc, reduceCtorEq] at hj
            · by_cases hy : y = 0
              · simp only [bind, Except.bind, hp, hp2, hy, hc, ↓reduceIte, Except.ok.injEq,
                  Prod.mk.injEq] at hj
                exact .inl (hj.1.symm.trans hsucc)
              · by_cases hjp : jumpable sevm.code x.toNat = true
                · simp only [bind, Except.bind, hp, hp2, hc, hy, ↓reduceIte, Except.assert,
                    hjp, Except.ok.injEq, Prod.mk.injEq] at hj
                  rw [← hj.1]
                  exact .inr (jumpdest_of_jumpable hjp)
                · simp only [bind, Except.bind, hp, hp2, hc, hy, ↓reduceIte, Except.assert,
                    hjp, Bool.false_eq_true, reduceCtorEq] at hj
    | last l => simp only [reduceCtorEq] at h

/-! ## A spawning `CALL` -/

/-- A `CALL` that spawns popped its seven operands. -/
theorem call_spawn_stack {pc pc' : Nat} {sevm : Sevm} {s : Devm} {f : Frame} {rsm : Resume}
    (hfork : CoveredFork sevm.benvStat.fork)
    (h : Ninst.step ⟨pc, sevm, s⟩ Ninst.call = .spawn f rsm pc') :
    ∃ g c v ii is oi os rest, s.stack = g :: c :: v :: ii :: is :: oi :: os :: rest := by
  have hx : Xinst.step sevm s .call = .spawn f rsm :=
    XStep.toStep_spawn (by simpa only [Ninst.call, Ninst.step_exec] using h)
  simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hx
  rw [hfork.rules_stateGas_none] at hx
  rcases eq1 : Devm.pop s with _ | ⟨gas1, devm1⟩ <;> simp only [eq1] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  have e1 := (Devm.pop_of_pop eq1).stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e1
  rcases eq2 : Devm.popToAdr devm1 with _ | ⟨callee, devm2⟩ <;> simp only [eq2] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rcases Devm.pop_of_popToAdr eq2 with ⟨x2, -, h_pop2⟩
  have e2 := (Devm.pop_of_pop h_pop2).stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e2
  rcases eq3 : Devm.pop devm2 with _ | ⟨value, devm3⟩ <;> simp only [eq3] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  have e3 := (Devm.pop_of_pop eq3).stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e3
  rcases eq4 : Devm.popToNat devm3 with _ | ⟨inputIndex, devm4⟩ <;> simp only [eq4] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rcases Devm.pop_of_popToNat_val eq4 with ⟨x4, f4, -⟩
  have e4 := f4.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e4
  rcases eq5 : Devm.popToNat devm4 with _ | ⟨inputSize, devm5⟩ <;> simp only [eq5] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rcases Devm.pop_of_popToNat_val eq5 with ⟨x5, f5, -⟩
  have e5 := f5.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e5
  rcases eq6 : Devm.popToNat devm5 with _ | ⟨outputIndex, devm6⟩ <;> simp only [eq6] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rcases Devm.pop_of_popToNat_val eq6 with ⟨x6, f6, -⟩
  have e6 := f6.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e6
  rcases eq7 : Devm.popToNat devm6 with _ | ⟨outputSize, devm7⟩ <;> simp only [eq7] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rcases Devm.pop_of_popToNat_val eq7 with ⟨x7, f7, -⟩
  have e7 := f7.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e7
  exact ⟨_, _, _, _, _, _, _, _, by rw [e1, e2, e3, e4, e5, e6, e7]⟩

/-- **A `CALL` to an undelegated precompile enters no code frame.** -/
theorem call_enter_not_run {pc pc' : Nat} {sevm : Sevm} {s : Devm} {f : Frame} {rsm : Resume}
    {a : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (h : Ninst.step ⟨pc, sevm, s⟩ Ninst.call = .spawn f rsm pc')
    (ht : s.stack[1]? = some a) (hdel : getDelegatedCodeAddress (s.getCode a.toAdr) = none)
    (hpre : sevm.benvStat.rules.isPrecomp a.toAdr) {cevm : Evm} (henter : f.enter = .run cevm) :
    False := by
  obtain ⟨g, c, v, ii, is, oi, os, rest, hstack⟩ := call_spawn_stack hfork h
  have hc : c = a := by
    rw [hstack] at ht
    exact Option.some.inj ht
  subst hc
  obtain ⟨parent, dp, na, code, avail, -, -, -, -, hdel', hf, -⟩ :=
    Blanc.Ninst.step_call_spawn_exact h hstack hfork
  rcases hdel' with ⟨-, rfl, -, rfl⟩ | ⟨dd, hsome, -, -, -⟩
  · obtain ⟨benv, hbt, -⟩ := Frame.enter_run_inv henter
    have hstat : benv.stat = sevm.benvStat := by
      rw [benvAfterTransfer_stat hbt, hf]; rfl
    have e := Blanc.Frame.enter_eq_done_executePrecomp (adr := c.toAdr) hbt (by rw [hf]; rfl)
      (by
        rw [hf]
        simp only [Msg.withBenv, Frame.ofCall, callMsg, Bool.not_false, Bool.true_and]
        exact decide_eq_true (by rw [hstat]; exact hpre))
    rw [henter] at e
    cases e
  · rw [hdel] at hsome
    cases hsome

/-! ## Decoding from bytes -/

theorem ninstAt_of_drop {cd : ByteArray} {pc : Nat} {n : Ninst} {rest : List UInt8}
    (h : cd.data.toList.drop pc = Ninst.toBytes n ++ rest) : Ninst.At cd pc n := by
  apply Ninst.at_of_slice
  apply bytesAt_slice (ninst_bytes_ne_nil n)
  unfold bytesAt
  rw [h, List.take_left]
  exact decide_eq_true rfl

theorem byteAt_of_drop {cd : ByteArray} {pc : Nat} {b : UInt8} {rest : List UInt8}
    (h : cd.data.toList.drop pc = b :: rest) : byteAt cd pc = some b := by
  unfold byteAt
  have e := List.getElem?_drop (xs := cd.data.toList) (i := pc) (j := 0)
  rw [h, Nat.add_zero] at e
  exact e.symm

/-- A continued step at a decoded ordinary instruction is that instruction's run. -/
theorem run_of_cont_at {pc pc' : Nat} {sevm : Sevm} {d d' : Devm} {n : Ninst}
    (hat : Ninst.At sevm.code pc n) (h : Evm.step ⟨pc, sevm, d⟩ = .cont pc' d') :
    Ninst.Run sevm d n d' ∧ pc' = pc + n.size := by
  have hs := (Evm.step_next hat).symm.trans h
  refine ⟨⟨.none, trivial, pc, ?_⟩, Ninst.step_cont_pc hs⟩
  simp only [Ninst.StepRun, hs, Step.Run]
  exact ⟨trivial, trivial⟩

/-! ## The identity-copy guard along a frame's chain -/

/-- At an identity copy the call's target word is `4`, and at its `GAS` the word below is `4`. -/
def IdGuard (cd : ByteArray) (pc : Nat) (d : Devm) : Prop :=
  (IdCopyAt cd pc → d.stack[1]? = some 4) ∧ (IdCopyAt cd (pc + 1) → d.stack[0]? = some 4)

/-- A continued step never lands past the code's end. -/
theorem step_cont_lt {cd : ByteArray} {pc pc' : Nat} {sevm : Sevm} {d d' : Devm}
    (hcode : sevm.code = cd) (h : Evm.step ⟨pc, sevm, d⟩ = .cont pc' d') : pc < cd.size := by
  by_contra hn
  have hg : Evm.getInst ⟨pc, sevm, d⟩ = some (.last .stop) := by
    show sevm.code.getInst pc = _
    unfold ByteArray.getInst
    rw [hcode]
    simp only [hn, ↓reduceDIte]
  unfold Evm.step at h
  rw [hg] at h
  cases h

theorem idCopyAt_ne_toXinst {cd : ByteArray} {q : Nat} {x : Xinst} (hq : q < cd.size)
    (hx : cd[q].toXinst = some x) : ¬ IdCopyAt cd (q + 1) ∧ ¬ IdCopyAt cd (q + 2) := by
  have hlen : cd.data.toList.length = cd.size := Array.length_toList
  refine ⟨fun ⟨_, _, _, _, _, _, b1, _⟩ => ?_, fun ⟨_, _, _, _, _, _, _, _, _, _, b4⟩ => ?_⟩
  · simp only [Nat.add_sub_cancel] at b1
    rw [b1] at hx
    cases hx
  · rw [show q + 2 - 2 = q by omega, List.getElem?_eq_getElem (hlen ▸ hq)] at b4
    have : cd[q] = 0x04 := Option.some.inj b4
    rw [this] at hx
    cases hx

/-- After a spawning instruction the guard holds vacuously. -/
theorem idGuard_spawn {cd : ByteArray} {q : Nat} {x : Xinst} (hq : q < cd.size)
    (hx : cd[q].toXinst = some x) (d : Devm) : IdGuard cd (q + 1) d :=
  ⟨fun h => absurd h (idCopyAt_ne_toXinst hq hx).1,
    fun h => absurd h (idCopyAt_ne_toXinst hq hx).2⟩

/-- **The guard survives a continued step.** -/
theorem idGuard_cont {cd : ByteArray} (hg : guardCheck cd = true) {pc pc' : Nat} {sevm : Sevm}
    {d d' : Devm} (hcode : sevm.code = cd) (hb : noPushBefore cd pc 32 = true)
    (hG : IdGuard cd pc d) (h : Evm.step ⟨pc, sevm, d⟩ = .cont pc' d') : IdGuard cd pc' d' := by
  have hlen : cd.data.toList.length = cd.size := Array.length_toList
  have hpc := step_cont_lt hcode h
  have hreach := PushReach.of_noPushBefore cd pc hpc hb
  have hsucc := Evm.step_cont_succ h hcode hpc (guardCheck_noImm hg hreach hpc)
  refine ⟨fun hid => ?_, fun hid => ?_⟩
  · obtain ⟨h1, h3, hq3, hbyte, hr1, hs1, b1, hr3, hs3, b3, b4⟩ := hid
    rcases hsucc with e | ⟨hk, hj⟩
    · have hpe : pc = pc' - 1 := PushReach.succ_inj hpc h1 hreach hr1 (e.symm.trans hs1.symm)
      subst hpe
      have hat : Ninst.At sevm.code (pc' - 1) (.reg .gas) := by
        rw [hcode]
        apply ninstAt_of_drop (rest := cd.data.toList.drop pc')
        rw [List.drop_eq_getElem_cons (hlen ▸ h1)]
        show cd[pc' - 1] :: _ = _
        rw [b1, show pc' - 1 + 1 = pc' by omega]
        rfl
      obtain ⟨run, -⟩ := run_of_cont_at hat h
      rw [St.self rfl rfl (d := d)] at run
      obtain ⟨G', rfl⟩ := ri_gas_remaining run
      have hg0 := hG.2 (by rw [show pc' - 1 + 1 = pc' by omega]; exact ⟨h1, h3, hq3, hbyte, hr1,
        hs1, b1, hr3, hs3, b3, b4⟩)
      simpa only [St.stack, List.getElem?_cons_succ] using hg0
    · rw [List.getElem?_eq_getElem (hlen ▸ hk)] at hbyte
      have : cd[pc'] = 0xf1 := Option.some.inj hbyte
      rw [this] at hj
      cases hj
  · obtain ⟨h1, h3, hq3, -, -, -, b1, hr3, hs3, b3, b4⟩ := hid
    rcases hsucc with e | ⟨hk, hj⟩
    · have hpe : pc = pc' + 1 - 3 := PushReach.succ_inj hpc h3 hreach hr3
        (e.symm.trans (by rw [hs3]; omega))
      subst hpe
      have hat : Ninst.At sevm.code (pc' + 1 - 3) (.push [0x04] (by decide)) := by
        rw [hcode]
        apply ninstAt_of_drop (rest := cd.data.toList.drop (pc' + 1 - 3 + 2))
        rw [List.drop_eq_getElem_cons (hlen ▸ h3)]
        have h2 : pc' + 1 - 3 + 1 < cd.size := by omega
        rw [List.drop_eq_getElem_cons (hlen ▸ h2)]
        show cd[pc' + 1 - 3] :: cd[pc' + 1 - 3 + 1] :: _ = _
        have b4' : cd[pc' + 1 - 3 + 1] = 0x04 := by
          rw [show pc' + 1 - 2 = pc' + 1 - 3 + 1 by omega,
            List.getElem?_eq_getElem (hlen ▸ h2)] at b4
          exact Option.some.inj b4
        rw [b3, b4']
        rfl
      obtain ⟨run, -⟩ := run_of_cont_at hat h
      rw [St.self rfl rfl (d := d)] at run
      obtain ⟨G', rfl⟩ := ri_push run
      rfl
    · simp only [Nat.add_sub_cancel] at b1
      rw [b1] at hj
      cases hj

/-! ## A call child that does not commit leaves the flag `0` -/

/-- **A spawned `CALL`/`STATICCALL` child commits, or the parent resumes with `0` on top.** -/
theorem spawn_commits_or_zero {sevm : Sevm} {d d'' : Devm} {x : Xinst} {f : Frame}
    {rsm : Resume} {raw : Execution} (hfork : CoveredFork sevm.benvStat.fork)
    (hx : x = .call ∨ x = .staticcall) (hs : Xinst.step sevm d x = .spawn f rsm)
    (hr : rsm.run (f.settle raw) = .ok d'') :
    Frame.settlementCommits f raw = true ∨ d''.stack[0]? = some 0 := by
  have hshape := ReturnDataBound.call_shape (pre := d) hx hfork.rules_stateGas_none
  rw [hs] at hshape
  obtain ⟨msg, parent, oi, os, rfl, rfl⟩ := hshape
  cases hset : (Frame.ofCall msg).settle raw with
  | error e =>
    rw [hset] at hr
    exact (Resume.call_run_error hr).elim
  | ok child =>
    rw [hset] at hr
    have hst := Resume.call_stack_flag hr
    cases he : child.error.isSome with
    | true =>
      right
      rw [hst, he]
      rfl
    | false =>
      left
      unfold Frame.settlementCommits
      rw [hset]
      show child.error.isNone = true
      cases hce : child.error with
      | none => rfl
      | some _ => rw [hce] at he; cases he

/-- **A flag-guarded call's zero flag reverts**: no successful continuation starts after the
call with `0` on top. -/
theorem guarded_zero_false {cd : ByteArray} {pc : Nat} {sevm : Sevm} {d post : Devm}
    (hcode : sevm.code = cd) (hga : guardedAfter (cd.data.toList.drop pc) = true)
    (next : Exec (pc + 1) sevm d (.ok post)) (hgas : d.gasMeasure < 2 ^ 256)
    (hz : d.stack[0]? = some 0) : False := by
  obtain ⟨c0, a, b, rest, hdrop⟩ : ∃ c0 a b rest, cd.data.toList.drop pc =
      c0 :: 0x61 :: a :: b :: 0x57 :: 0x60 :: 0x00 :: 0x80 :: 0xfd :: rest := by
    unfold guardedAfter at hga
    split at hga
    · rename_i c0 b1 a b b4 b5 b6 b7 b8 rest hd
      simp only [Bool.and_eq_true, beq_iff_eq] at hga
      obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := hga
      exact ⟨c0, a, b, rest, hd⟩
    · cases hga
  have hd1 : cd.data.toList.drop (pc + 1) =
      0x61 :: a :: b :: 0x57 :: 0x60 :: 0x00 :: 0x80 :: 0xfd :: rest := by
    rw [← List.drop_drop, hdrop]; rfl
  have hd4 : cd.data.toList.drop (pc + 1 + 3) = 0x57 :: 0x60 :: 0x00 :: 0x80 :: 0xfd :: rest := by
    rw [← List.drop_drop, hd1]; rfl
  have hd5 : cd.data.toList.drop (pc + 1 + 3 + 1) = 0x60 :: 0x00 :: 0x80 :: 0xfd :: rest := by
    rw [← List.drop_drop, hd4]; rfl
  have hd7 : cd.data.toList.drop (pc + 1 + 3 + 1 + 2) = 0x80 :: 0xfd :: rest := by
    rw [← List.drop_drop, hd5]; rfl
  have hd8 : cd.data.toList.drop (pc + 1 + 3 + 1 + 2 + 1) = 0xfd :: rest := by
    rw [← List.drop_drop, hd7]; rfl
  subst hcode
  have h := XAt.of_exec next hgas
  obtain ⟨d1, run1, h1⟩ := xa_next (n := .push [a, b] (by simp only [List.length_cons, List.length_nil]; omega))
    (ninstAt_of_drop (rest := 0x57 :: 0x60 :: 0x00 :: 0x80 :: 0xfd :: rest) hd1) nofun h
  have hs1 := push_run_stack run1
  rcases xa_jumpi (byteAt_jinst_at (by
      show byteAt _ (pc + 1 + 3) = some (0x57 : UInt8)
      exact byteAt_of_drop hd4)) h1 with
    ⟨x, d2, pop, h2⟩ | ⟨x, y, d2, hy, pop, -⟩
  · obtain ⟨d3, run3, h3⟩ := xa_next (n := .push [0x00] (by decide))
      (ninstAt_of_drop (rest := 0x80 :: 0xfd :: rest) hd5) nofun h2
    obtain ⟨d4, -, h4⟩ := xa_next (n := .reg (.dup 0))
      (ninstAt_of_drop (rest := 0xfd :: rest) hd7) nofun h3
    exact xa_revert (byteAt_linst_at (by
      show byteAt _ (pc + 1 + 3 + 1 + 2 + 1) = some (0xfd : UInt8)
      exact byteAt_of_drop hd8)) h4
  · have hp := popBurn_two_stack pop
    rw [hs1] at hp
    have hd : d.stack = y :: d2.stack := (List.cons.inj hp).2
    rw [hd] at hz
    exact hy (Option.some.inj hz)

/-! ## Successful frames of flag-guarded code: every entered child commits -/

/-- **Every raw descendant of a successful frame of flag-guarded code lies under a committed
child.**  For code passing `guardCheck`, any successful derivation entered at a reached position
with the identity guard, the identity precompile at `4` undelegated and precompiled, and committed
children keeping the code at `4`: each raw frame descendant is a raw root of a direct committed
child.  A child that did not commit leaves the flag `0`, which a guarded site reverts on; an
identity copy targets `4` and enters no code frame. -/
theorem Exec.rawFrameDescendants_of_guardCheck {cd : ByteArray} (hg : guardCheck cd = true) :
    ∀ {pc : Nat} {sevm : Sevm} {d : Devm} {out : Execution} (exc : Exec pc sevm d out)
      {post : Devm}, out = .ok post → sevm.code = cd → CoveredFork sevm.benvStat.fork →
      sevm.benvStat.rules.isPrecomp (4 : Adr) →
      noPushBefore cd pc 32 = true → d.gasMeasure < 2 ^ 256 → IdGuard cd pc d →
      getDelegatedCodeAddress (d.getCode 4) = none →
      (∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
      ∀ r ∈ Exec.rawFrameDescendants exc, ∃ c ∈ Exec.childFrames exc,
        r ∈ Exec.rawFrameRoots c.run := by
  intro pc sevm d out exc
  induction exc with
  | halt _ =>
    intro post _ _ _ _ _ _ _ _ _ r hr
    simp only [Exec.rawFrameDescendants, List.not_mem_nil] at hr
  | @cont pc sevm d pc' d' ex hstep next ih =>
    intro post hout hcode hfork hpre hb hgas hG hdel h4 r hr
    have hc : Devm.CodeAt 4 d d' := Evm.step_codeAt (xl := .none) (out := .ok _) hfork
      (Xinst.avoidsAt_of_step (fun f rsm pc'' cevm h' => by rw [hstep] at h'; cases h'))
      trivial (by rw [hstep]; exact ⟨rfl, rfl⟩)
    exact ih hout hcode hfork hpre (Evm.step_cont_noPush hstep (hcode ▸ hb) |> (hcode ▸ ·))
      (lt_trans (gas_cont hstep) hgas) (idGuard_cont hg hcode hb hG hstep)
      (by rw [show d'.getCode 4 = d.getCode 4 from hc]; exact hdel)
      (by simpa only [Exec.childFrames] using h4) r (by simpa only [Exec.rawFrameDescendants] using hr)
  | doneErr _ _ _ =>
    intro post hout
    cases hout
  | @doneOk pc sevm d f rsm pc' res d' ex hstep henter hres next ih =>
    intro post hout hcode hfork hpre hb hgas hG hdel h4 r hr
    obtain ⟨x, hxat, -, rfl⟩ := Evm.step_spawn_inv hstep
    rw [hcode] at hxat
    obtain ⟨hpc, hbyte⟩ := getInst_exec_toXinst hxat
    obtain ⟨_, hty⟩ := getInst_exec_inv hxat
    have hc : Devm.CodeAt 4 d d' := Evm.step_codeAt (xl := .none) (out := .ok _) hfork
      (Xinst.avoidsAt_of_step (fun f' rsm' pc'' cevm h' hen => by
        rw [hstep] at h'; cases h'; rw [henter] at hen; cases hen))
      trivial (by rw [hstep]; exact ⟨_, RunFrame.of_done henter, hres.symm⟩)
    exact ih hout hcode hfork hpre
      (noPushBefore_succ_of_ne_p hpc hb (by rw [hty]; nofun))
      (lt_trans (gas_done hstep henter hres) hgas) (idGuard_spawn hpc hbyte d')
      (by rw [show d'.getCode 4 = d.getCode 4 from hc]; exact hdel)
      (by simpa only [Exec.childFrames] using h4) r (by simpa only [Exec.rawFrameDescendants] using hr)
  | runErr _ _ _ _ =>
    intro post hout
    cases hout
  | @runOk pc sevm d f rsm pc' cevm raw d' ex hstep henter child hres next ihc ihn =>
    intro post hout hcode hfork hpre hb hgas hG hdel h4 r hr
    obtain ⟨x, hxat, hxs, rfl⟩ := Evm.step_spawn_inv hstep
    have hxat' := hxat
    rw [hcode] at hxat'
    obtain ⟨hpc, hbyte⟩ := getInst_exec_toXinst hxat'
    obtain ⟨_, hty⟩ := getInst_exec_inv hxat'
    have hreach := PushReach.of_noPushBefore cd pc hpc hb
    obtain ⟨hcf, hcase⟩ := guardCheck_sound hg hreach hxat'
    rcases hcase with hga | ⟨rfl, hid⟩
    · rcases spawn_commits_or_zero hfork hcf hxs hres with hcom | hz
      · have hraw : Execution.commits raw = true := Frame.raw_commits_of_settlementCommits hcom
        have hcf' : Exec.childFrames (Exec.runOk hstep henter child hres next) =
            Exec.Frame.ofRun child hraw :: Exec.childFrames next := by
          simp only [Exec.childFrames, hcom, dite_true, List.singleton_append]
        rw [hcf'] at h4 ⊢
        have hrel : Xlot.Rel (Devm.CodeAt 4) (.some ⟨cevm, raw⟩) := by
          have e := h4 _ List.mem_cons_self
          cases raw with
          | error _ => cases hraw
          | ok body => exact e
        have hc : Devm.CodeAt 4 d d' := Evm.step_codeAt (xl := .some ⟨_, _⟩) (out := .ok _) hfork
          (Xinst.avoidsAt_of_step (fun f' rsm' pc'' cevm' h' hen hcr => by
            rw [hstep] at h'
            cases h'
            have hshape := ReturnDataBound.call_shape (pre := d) hcf hfork.rules_stateGas_none
            rw [hxs] at hshape
            obtain ⟨msg, parent, oi, os, hfm, -⟩ := hshape
            rw [hfm] at hcr
            cases hcr))
          hrel (by rw [hstep]; exact ⟨_, RunFrame.of_run henter, hres.symm⟩)
        simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append] at hr
        rcases hr with rfl | hr | hr
        · exact ⟨_, List.mem_cons_self, List.mem_cons_self⟩
        · exact ⟨_, List.mem_cons_self, List.mem_cons_of_mem _ hr⟩
        · obtain ⟨c, hcm, hcr⟩ := ihn hout hcode hfork hpre
            (noPushBefore_succ_of_ne_p hpc hb (by rw [hty]; nofun))
            (lt_trans (gas_run hstep henter child hres) hgas) (idGuard_spawn hpc hbyte d')
            (by rw [show d'.getCode 4 = d.getCode 4 from hc]; exact hdel)
            (fun c hc' => h4 c (List.mem_cons_of_mem _ hc')) r hr
          exact ⟨c, List.mem_cons_of_mem _ hcm, hcr⟩
      · exact (guarded_zero_false hcode hga (hout ▸ next)
          (lt_trans (gas_run hstep henter child hres) hgas) hz).elim
    · exfalso
      have hns : Ninst.step ⟨pc, sevm, d⟩ Ninst.call = .spawn f rsm (pc + 1) :=
        (Evm.step_next hxat).symm.trans hstep
      exact call_enter_not_run (a := 4) hfork hns (hG.1 hid) hdel hpre henter

/-- No identity guard is owed at a frame's entry. -/
theorem idGuard_zero (cd : ByteArray) (d : Devm) : IdGuard cd 0 d :=
  ⟨fun ⟨_, _, h, _⟩ => absurd h (by omega), fun ⟨_, _, h, _⟩ => absurd h (by omega)⟩

/-- **`Exec.rawFrameDescendants_of_guardCheck` at a frame's entry** (pc `0`). -/
theorem Exec.rawFrameDescendants_of_guardCheck_entry {cd : ByteArray} (hg : guardCheck cd = true)
    {sevm : Sevm} {d post : Devm} (exc : Exec 0 sevm d (.ok post)) (hcode : sevm.code = cd)
    (hfork : CoveredFork sevm.benvStat.fork) (hpre : sevm.benvStat.rules.isPrecomp (4 : Adr))
    (hgas : d.gasMeasure < 2 ^ 256) (hdel : getDelegatedCodeAddress (d.getCode 4) = none)
    (h4 : ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) :
    ∀ r ∈ Exec.rawFrameDescendants exc, ∃ c ∈ Exec.childFrames exc,
      r ∈ Exec.rawFrameRoots c.run :=
  Exec.rawFrameDescendants_of_guardCheck hg exc rfl hcode hfork hpre (noPushBefore_zero cd 32)
    hgas (idGuard_zero cd d) hdel h4

/-- The check refuses an unguarded `CALL` that is no identity copy. -/
example : guardCheck ⟨#[0x60, 0x00, 0xf1, 0x00]⟩ = false := by decide +kernel

/-- The check admits a flag-guarded `CALL`. -/
example : guardCheck ⟨#[0xf1, 0x61, 0x00, 0x09, 0x57, 0x60, 0x00, 0x80, 0xfd, 0x5b]⟩ = true := by
  decide +kernel

end Blanc.Lift
