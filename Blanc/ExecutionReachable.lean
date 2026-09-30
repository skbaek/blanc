import Blanc.Compiled
import Blanc.ExecutionFrames

/-!
# Reachable program counters

`Xinst.At code pc x` decodes at every offset, including offsets inside a `PUSH` immediate that no
execution ever reaches.  This module states what an execution does reach.

* `Evm.step_cont_noPush`: every program counter an execution reaches is one no `PUSH` immediate
  covers (`noPushBefore code pc 32 = true`, the boundary invariant Jaune's jump-destination
  analysis is stated in).  Entering at `0`, stepping on by an instruction's size, and jumping to a
  `jumpable` destination all preserve it.
* `SpawnFreeReach code`: no `CALL`-family or `CREATE`-family instruction decodes at such a
  position.  `Exec.rawFrameDescendants_eq_nil_of_reach`: a run of such code, entered at `0`,
  enters no descendant frame.
* `spawnFreeCheck code`, `spawnFreeReach_of_check`: a linear walk that a kernel decision can
  evaluate, sound for `SpawnFreeReach` (`PushReach.of_noPushBefore` shows every position no
  `PUSH` immediate covers is on the walk).  The walk over-approximates (it treats the immediate of `DUPN`,
  `SWAPN` and `EXCHANGE` as an instruction start), so it can only refuse more, never less.
-/

namespace Blanc

open Jaune

theorem noPushBefore_zero (cd : ByteArray) (m : Nat) : noPushBefore cd 0 m = true := by
  cases m <;> rfl

/-- Stepping over a one-byte opcode that is not a `PUSH`. -/
theorem noPushBefore_succ_of_ne_p {cd : ByteArray} {k : Nat} (hk : k < cd.size)
    (hb : noPushBefore cd k 32 = true) (hne : cd[k].toInstType ≠ .P) :
    noPushBefore cd (k + 1) 32 = true :=
  noPushBefore_add (s := 1) (fun _ => Or.inr ⟨not_push_byte_of_ne_p hne, rfl⟩) hb

/-- Stepping over the immediate byte `a` of an `EIP-8024` instruction, when `a` is not a `PUSH`
opcode.  Past the end of code the immediate is zero-filled and covers nothing. -/
theorem noPushBefore_succ_of_imm {cd : ByteArray} {k : Nat} {a : UInt8}
    (hb : noPushBefore cd k 32 = true) (ha : a.toInstType ≠ .P)
    (hbyte : ∀ hk : k < cd.size, cd[k] = a) :
    noPushBefore cd (k + 1) 32 = true :=
  noPushBefore_add (s := 1) (fun hk => Or.inr ⟨by
    rw [hbyte hk]; exact not_push_byte_of_ne_p ha, rfl⟩) hb

theorem byteD_succ_eq {cd : ByteArray} {k : Nat} :
    ∀ hk : k < cd.size, cd[k] = cd.byteD k := fun hk => by simp only [ByteArray.byteD, hk,
      ↓reduceDIte]

/-- One instruction of the boundary walk: stepping over an accepted ordinary instruction from a
position no `PUSH` immediate covers lands on such a position again. -/
theorem noPushBefore_next {cd : ByteArray} {pc : Nat} {n : Ninst}
    (h : cd.getInst pc = some (.next n)) (hacc : Ninst.immAccepted n = true)
    (hb : noPushBefore cd pc 32 = true) : noPushBefore cd (pc + n.size) 32 = true := by
  unfold ByteArray.getInst at h
  by_cases hpc : pc < cd.size
  · simp only [hpc, ↓reduceDIte] at h
    split at h
    · rename_i hty
      split at h
      · cases Option.some.inj h
        have hd : decodeSingle (cd.byteD (pc + 1)) ≠ none := by
          simpa only [ne_eq, Ninst.immAccepted, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
            decide_eq_false_iff_not] using hacc
        have h1 := noPushBefore_succ_of_ne_p hpc hb (by rw [hty]; simp only [ne_eq, reduceCtorEq,
          not_false_eq_true])
        exact noPushBefore_succ_of_imm h1 (toInstType_ne_p_of_decodeSingle hd) byteD_succ_eq
      · cases Option.some.inj h
        have hd : decodeSingle (cd.byteD (pc + 1)) ≠ none := by
          simpa only [ne_eq, Ninst.immAccepted, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
            decide_eq_false_iff_not] using hacc
        have h1 := noPushBefore_succ_of_ne_p hpc hb (by rw [hty]; simp only [ne_eq, reduceCtorEq,
          not_false_eq_true])
        exact noPushBefore_succ_of_imm h1 (toInstType_ne_p_of_decodeSingle hd) byteD_succ_eq
      · cases Option.some.inj h
        have hd : decodePair (cd.byteD (pc + 1)) ≠ none := by
          simpa only [ne_eq, Ninst.immAccepted, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
            decide_eq_false_iff_not] using hacc
        have h1 := noPushBefore_succ_of_ne_p hpc hb (by rw [hty]; simp only [ne_eq, reduceCtorEq,
          not_false_eq_true])
        exact noPushBefore_succ_of_imm h1 (toInstType_ne_p_of_decodePair hd) byteD_succ_eq
      · cases hr : UInt8.toRinst cd[pc] with
        | none => simp only [Functor.mapRev, hr, Option.map_eq_map, Option.map_none,
          reduceCtorEq] at h
        | some r =>
            simp only [Functor.mapRev, hr] at h
            have hn : n = .reg r := by
              have := Option.some.inj h
              simpa only [Function.comp_apply, Inst.next.injEq] using this.symm
            subst hn
            exact noPushBefore_succ_of_ne_p hpc hb (by rw [hty]; simp only [ne_eq, reduceCtorEq,
              not_false_eq_true])
    · -- `X`
      cases hx : UInt8.toXinst cd[pc] with
      | none => simp only [Functor.mapRev, hx, Option.map_eq_map, Option.map_none,
        reduceCtorEq] at h
      | some x =>
          simp only [Functor.mapRev, hx] at h
          have hn : n = .exec x := by
            have := Option.some.inj h
            simpa only [Function.comp_apply, Inst.next.injEq] using this.symm
          subst hn
          exact noPushBefore_succ_of_ne_p hpc hb (by rename_i hty; rw [hty]; simp only [ne_eq,
            reduceCtorEq, not_false_eq_true])
    · cases hj : UInt8.toJinst cd[pc] <;> simp [Functor.mapRev, hj] at h
    · cases hl : UInt8.toLinst cd[pc] <;> simp [Functor.mapRev, hl] at h
    · rename_i hty
      have hle := le_of_toInstType_eq_p _ hty
      cases Option.some.inj h
      refine noPushBefore_add (fun hk => ?_) hb
      simp only [Ninst.size, ByteArray.length_sliceD]
      by_cases h96 : 96 ≤ cd[pc].toNat
      · exact Or.inl ⟨h96, hle, by omega⟩
      · exact Or.inr ⟨Or.inl (by omega), by omega⟩
  · simp only [hpc, ↓reduceDIte] at h
    cases h

/-- A continued instruction step had an accepted immediate: a forbidden `EIP-8024` immediate
halts. -/
theorem Ninst.step_cont_immAccepted {evm : Evm} {n : Ninst} {pc' : Nat} {devm' : Devm}
    (h : Ninst.step evm n = .cont pc' devm') : Ninst.immAccepted n = true := by
  unfold Ninst.step at h
  rcases n with r | x | ⟨xs, hxs⟩ | a | a | a
  · rfl
  · rfl
  · rfl
  · have hex := (Step.ofExecution_cont h).2
    simp only [Ninst.immAccepted, decide_eq_true_eq]
    intro hnone
    split at hex <;> simp_all [Bind.bind, Except.bind]
    split at hex <;> simp_all only [ExceptT.stM_eq, reduceCtorEq]
  · have hex := (Step.ofExecution_cont h).2
    simp only [Ninst.immAccepted, decide_eq_true_eq]
    intro hnone
    split at hex <;> simp_all [Bind.bind, Except.bind]
    split at hex <;> simp_all only [ExceptT.stM_eq, reduceCtorEq]
  · have hex := (Step.ofExecution_cont h).2
    simp only [Ninst.immAccepted, decide_eq_true_eq]
    intro hnone
    split at hex <;> simp_all [Bind.bind, Except.bind]
    split at hex <;> simp_all only [ExceptT.stM_eq, reduceCtorEq]

/-- A jump destination the interpreter accepts is a position no `PUSH` immediate covers. -/
theorem noPushBefore_of_jumpable {cd : ByteArray} {k : Nat} (h : jumpable cd k = true) :
    noPushBefore cd k 32 = true := by
  unfold jumpable at h
  split at h
  · split at h
    · exact h
    · cases h
  · cases h

/-- A decoded jump instruction sits on a `J`-class byte. -/
theorem getInst_jump_inv {cd : ByteArray} {pc : Nat} {j : Jinst}
    (h : cd.getInst pc = some (.jump j)) :
    ∃ hpc : pc < cd.size, cd[pc].toInstType = .J := by
  unfold ByteArray.getInst at h
  by_cases hpc : pc < cd.size
  · refine ⟨hpc, ?_⟩
    simp only [hpc, ↓reduceDIte] at h
    split at h
    · exfalso
      split at h
      · cases h
      · cases h
      · cases h
      · cases hr : UInt8.toRinst cd[pc] <;> simp [Functor.mapRev, hr] at h
    · exfalso
      cases hx : UInt8.toXinst cd[pc] <;> simp [Functor.mapRev, hx] at h
    · assumption
    · exfalso
      cases hl : UInt8.toLinst cd[pc] <;> simp [Functor.mapRev, hl] at h
    · exfalso
      cases h
  · simp only [hpc, ↓reduceDIte] at h
    cases h

/-- **Every program counter an execution reaches is one no `PUSH` immediate covers.**  One step
that continues in the same frame moves from such a position to another one. -/
theorem Evm.step_cont_noPush {pc : Nat} {sevm : Sevm} {devm : Devm} {pc' : Nat} {devm' : Devm}
    (h : Evm.step ⟨pc, sevm, devm⟩ = .cont pc' devm')
    (hb : noPushBefore sevm.code pc 32 = true) : noPushBefore sevm.code pc' 32 = true := by
  unfold Evm.step at h
  cases hg : Evm.getInst ⟨pc, sevm, devm⟩ with
  | none => simp only [hg, reduceCtorEq] at h
  | some inst =>
      rw [hg] at h
      have hg' : sevm.code.getInst pc = some inst := hg
      cases inst with
      | next n =>
          have hpc := Ninst.step_cont_pc h
          have hacc := Ninst.step_cont_immAccepted h
          simp only at hpc
          rw [hpc]
          exact noPushBefore_next hg' hacc hb
      | jump j =>
          obtain ⟨hlt, hty⟩ := getInst_jump_inv hg'
          have hj := Step.ofJump_cont h
          have hsucc : ∀ pc'' : Nat, pc'' = pc + 1 → noPushBefore sevm.code pc'' 32 = true := by
            intro pc'' e
            subst e
            exact noPushBefore_succ_of_ne_p hlt hb (by rw [hty]; simp only [ne_eq, reduceCtorEq,
              not_false_eq_true])
          cases j
          case jumpdest =>
            simp only [Jinst.run, Jinst.runCore] at hj
            rcases hc : chargeGas gJumpdest devm with e | d1
            · simp only [bind, Except.bind, hc, reduceCtorEq] at hj
            · simp only [bind, Except.bind, hc, Except.ok.injEq, Prod.mk.injEq] at hj
              exact hsucc _ hj.1.symm
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
                  exact noPushBefore_of_jumpable hjp
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
                    exact hsucc _ hj.1.symm
                  · by_cases hjp : jumpable sevm.code x.toNat = true
                    · simp only [bind, Except.bind, hp, hp2, hc, hy, ↓reduceIte, Except.assert,
                      hjp, Except.ok.injEq, Prod.mk.injEq] at hj
                      rw [← hj.1]
                      exact noPushBefore_of_jumpable hjp
                    · simp only [bind, Except.bind, hp, hp2, hc, hy, ↓reduceIte, Except.assert,
                      hjp, Bool.false_eq_true, reduceCtorEq] at hj
      | last l => simp only [reduceCtorEq] at h

/-! ### Spawn-freedom at reachable positions -/

/-- **No spawning instruction sits at a reachable position.**  `SpawnFree code` forbids a
`CALL`-family or `CREATE`-family byte at every offset; this notion forbids one only at the
positions no `PUSH` immediate covers, which are the only positions an execution reaches
(`Evm.step_cont_noPush`). -/
def SpawnFreeReach (code : ByteArray) : Prop :=
  ∀ pc x, noPushBefore code pc 32 = true → ¬ Xinst.At code pc x

/-- A run of spawn-free-at-reachable-positions code, entered at a position no `PUSH` immediate
covers, enters no descendant frame. -/
theorem Exec.rawFrameDescendants_eq_nil_of_reach {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out)
    (hb : noPushBefore sevm.code pc 32 = true) (h : SpawnFreeReach sevm.code) :
    Exec.rawFrameDescendants run = [] := by
  revert hb h
  induction run with
  | halt hstep => intro _ _; simp only [rawFrameDescendants]
  | cont hstep next ih =>
      intro hb h
      simpa only [rawFrameDescendants] using ih (Evm.step_cont_noPush hstep hb) h
  | doneErr hstep henter hresume =>
      intro hb h
      obtain ⟨x, hx, -⟩ := Evm.step_spawn_inv hstep
      exact absurd hx (h _ x hb)
  | doneOk hstep henter hresume next ih =>
      intro hb h
      obtain ⟨x, hx, -⟩ := Evm.step_spawn_inv hstep
      exact absurd hx (h _ x hb)
  | runErr hstep henter child hresume ih =>
      intro hb h
      obtain ⟨x, hx, -⟩ := Evm.step_spawn_inv hstep
      exact absurd hx (h _ x hb)
  | runOk hstep henter child hresume next ihChild ihNext =>
      intro hb h
      obtain ⟨x, hx, -⟩ := Evm.step_spawn_inv hstep
      exact absurd hx (h _ x hb)

/-! ### A decidable check -/

/-- A call-type instruction decodes only on an `X`-class byte. -/
theorem getInst_exec_inv {cd : ByteArray} {pc : Nat} {x : Xinst}
    (h : cd.getInst pc = some (.next (.exec x))) :
    ∃ hpc : pc < cd.size, cd[pc].toInstType = .X := by
  unfold ByteArray.getInst at h
  by_cases hpc : pc < cd.size
  · refine ⟨hpc, ?_⟩
    simp only [hpc, ↓reduceDIte] at h
    split at h
    · exfalso
      split at h
      · cases h
      · cases h
      · cases h
      · cases hr : UInt8.toRinst cd[pc] <;> simp [Functor.mapRev, hr] at h
    · assumption
    · exfalso
      cases hj : UInt8.toJinst cd[pc] <;> simp [Functor.mapRev, hj] at h
    · exfalso
      cases hl : UInt8.toLinst cd[pc] <;> simp [Functor.mapRev, hl] at h
    · exfalso
      cases h
  · simp only [hpc, ↓reduceDIte] at h
    cases h

/-- The positions the linear instruction walk reaches from `0`, stepping over `PUSH` immediates. -/
inductive PushReach (cd : ByteArray) : Nat → Prop
  | zero : PushReach cd 0
  | step {p : Nat} (hp : p < cd.size) :
      PushReach cd p → PushReach cd (p + 1 + pushWidth cd[p])

/-- Every position in range that no `PUSH` immediate covers is on the linear walk. -/
theorem PushReach.of_noPushBefore (cd : ByteArray) :
    ∀ k, k < cd.size → noPushBefore cd k 32 = true → PushReach cd k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hb
    by_cases h0 : k = 0
    · subst h0; exact .zero
    · have hp0 : noPushBefore cd 0 32 = true := noPushBefore_zero cd 32
      set p := Nat.findGreatest (fun q => noPushBefore cd q 32 = true) (k - 1) with hpdef
      have hple : p ≤ k - 1 := Nat.findGreatest_le _
      have hP : noPushBefore cd p 32 = true :=
        Nat.findGreatest_spec (P := fun q => noPushBefore cd q 32 = true) (Nat.zero_le _) hp0
      have hmax : ∀ q, p < q → q ≤ k - 1 → noPushBefore cd q 32 ≠ true := fun q hq hqk =>
        Nat.findGreatest_is_greatest hq hqk
      have hpk : p < k := by omega
      have hpsz : p < cd.size := by omega
      -- the walk step from `p`
      have hspan : noPushBefore cd (p + 1 + pushWidth cd[p]) 32 = true := by
        have := noPushBefore_add (cd := cd) (k := p) (s := 1 + pushWidth cd[p]) (fun hk' => by
          unfold pushWidth
          by_cases hr : 0x60 ≤ cd[p].toNat ∧ cd[p].toNat ≤ 0x7f
          · exact Or.inl ⟨by omega, by omega, by simp only [hr, and_self, ↓reduceIte]; omega⟩
          · exact Or.inr ⟨by omega, by simp only [hr, ↓reduceIte, add_zero]⟩) hP
        simpa only [Nat.add_assoc] using this
      have hge : k ≤ p + 1 + pushWidth cd[p] := by
        by_contra hlt
        exact hmax _ (by omega) (by omega) hspan
      have hle : p + 1 + pushWidth cd[p] ≤ k := by
        by_contra hgt
        have hw : 0 < pushWidth cd[p] := by omega
        have hr : 0x60 ≤ cd[p].toNat ∧ cd[p].toNat ≤ 0x7f := by
          by_contra hr
          simp only [pushWidth, hr, ↓reduceIte, lt_self_iff_false] at hw
        have hw' : pushWidth cd[p] = cd[p].toNat - 0x5f := by simp only [pushWidth, hr, and_self,
          ↓reduceIte]
        have hfalse := (noPushBefore_eq_true_iff cd k 32 (le_refl 32)).mp hb p
          (by omega) hpk hpsz (by omega) (by omega) (by omega)
        rw [hfalse] at hP
        cases hP
      have heq : p + 1 + pushWidth cd[p] = k := le_antisymm hle hge
      have hreach := PushReach.step hpsz (ih p hpk hpsz hP)
      rwa [heq] at hreach

/-- A byte that could start a call-type instruction: any `X`-class byte. -/
def spawnByte (b : UInt8) : Bool := decide (b.toInstType = .X)

/-- The linear instruction walk, with a fuel of the code's size, refusing every `X`-class byte at
an instruction start.  Every step advances by at least one byte. -/
def spawnScan (cd : ByteArray) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, k =>
      if hk : k < cd.size then
        !spawnByte cd[k] && spawnScan cd fuel (k + 1 + pushWidth cd[k])
      else true

/-- The decidable check: no `X`-class byte at any instruction start of the linear walk. -/
def spawnFreeCheck (cd : ByteArray) : Bool := spawnScan cd cd.size 0

private theorem spawnScan_good {cd : ByteArray} {j : Nat}
    (h : ∃ fuel, cd.size ≤ j + fuel ∧ spawnScan cd fuel j = true) (hj : j < cd.size) :
    spawnByte cd[j] = false ∧
      ∃ fuel, cd.size ≤ (j + 1 + pushWidth cd[j]) + fuel ∧
        spawnScan cd fuel (j + 1 + pushWidth cd[j]) = true := by
  obtain ⟨fuel, hfuel, hscan⟩ := h
  cases fuel with
  | zero => omega
  | succ f =>
      simp only [spawnScan, hj, ↓reduceDIte, Bool.and_eq_true, Bool.not_eq_true'] at hscan
      exact ⟨hscan.1, f, by omega, hscan.2⟩

theorem spawnFreeReach_of_check {cd : ByteArray} (h : spawnFreeCheck cd = true) :
    SpawnFreeReach cd := by
  intro pc x hb hx
  obtain ⟨hpc, hty⟩ := getInst_exec_inv hx
  have hreach := PushReach.of_noPushBefore cd pc hpc hb
  have key : ∀ j, PushReach cd j →
      ∃ fuel, cd.size ≤ j + fuel ∧ spawnScan cd fuel j = true := by
    intro j hj
    induction hj with
    | zero => exact ⟨cd.size, by omega, h⟩
    | step hp _ ih => exact (spawnScan_good ih hp).2
  have := (spawnScan_good (key pc hreach) hpc).1
  simp only [spawnByte, hty, decide_true, Bool.true_eq_false] at this

end Blanc
