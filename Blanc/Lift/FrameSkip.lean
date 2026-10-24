import Blanc.Lift.Cursor
import Blanc.Lift.Silent
import Blanc.Lift.InvWalkWorld

/-!
# Frame skip: checked synthetic runs never touch the stack below their frame

The certificate checker (`checkNode`) tracks every node's operand stack as an abstract frame and
rejects any instruction that needs a word below it.  This module reads that fact back at the
level of synthetic runs (`SFunc.RunP`, `SFunc.RunCutP`), with no `Exec` derivation in sight:

* `FrameAt code c m pc a ρ R d f`: the tree `f` checks at `pc` with frame `a` and return arity
  `m`, and `d`'s stack is a segment matched by `a` (reading `.ret` as `ρ`) above `R`;
* `SFunc.RunP.stack_below`: a run from `FrameAt … R` that returns leaves `Y ++ R` with
  `Y.length = m` (and its frame mentions `.ret`);
* `SFunc.RunCutP.stack_below`: every stop of a cut run satisfies `CutStop`: a cut entry is
  entered with its declared frame above the same `R`, a return leaves `Y ++ R`;
* `SFunc.RunP.entry_stack_below`: the same for an entry run from its declared frame;
* `ric_call_silent`: a `callNext` into a `SilentSet` closure, inverted over the walk state
  `St b (dd :: S) M G`: the continuation runs from an unchanged world state with stack
  `Y ++ S.drop e.frame.length`, `Y.length = e.rets`.

`ric_call_silent` lets a walk cross any state-silent internal call (hashing, ABI encoding,
view-like helpers) without walking it.  Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- The frame invariant of a checked node: `f` checks at `pc` with frame `a` and return arity
`m`, and the stack is a segment matched by `a` above the untouched `R`. -/
def FrameAt (code : ByteArray) (c : Cert) (m pc : Nat) (a : List AVal) (ρ : B256)
    (R : List B256) (d : Devm) (f : SFunc) : Prop :=
  checkNode code c.entries m pc a f = true ∧ ∃ X, d.stack = X ++ R ∧ FrameMatches ρ a X

/-- Some checked node after one step from frame `a`: its frame mentions `.ret` only if `a`
does. -/
def FrameNext (code : ByteArray) (c : Cert) (m : Nat) (a : List AVal) (ρ : B256)
    (R : List B256) (d : Devm) (f : SFunc) : Prop :=
  ∃ pc a', (AVal.ret ∈ a' → AVal.ret ∈ a) ∧ FrameAt code c m pc a' ρ R d f

/-- About to enter entry `k` by a goto from frame `a`: its declared frame matches the stack
above `R`, and it returns with the current arity `m`. -/
def EntryAt (c : Cert) (m : Nat) (a : List AVal) (ρ : B256)
    (R : List B256) (k : Nat) (d : Devm) : Prop :=
  ∃ e, c.entries[k]? = some e ∧ e.rets = m ∧ (AVal.ret ∈ e.frame → AVal.ret ∈ a) ∧
    ∃ X, d.stack = X ++ R ∧ FrameMatches ρ e.frame X

/-- What a cut run from `FrameAt … a ρ R` guarantees where it stops. -/
def CutStop (c : Cert) (m : Nat) (a : List AVal) (ρ : B256)
    (R : List B256) : Seg → Prop
  | .at k d => EntryAt c m a ρ R k d
  | .done (.returned d) => AVal.ret ∈ a ∧ ∃ Y, d.stack = Y ++ R ∧ Y.length = m
  | .done (.halted _) => True

section Steps

variable {code : ByteArray} {c : Cert} {m pc : Nat} {a : List AVal} {ρ : B256}
  {R : List B256} {d d' : Devm}

theorem EntryAt.enter (hc : Cert.check code c = true) {k : Nat} {g : SFunc}
    (h : EntryAt c m a ρ R k d) (hg : c.prog[k]? = some g) :
    FrameNext code c m a ρ R d g := by
  obtain ⟨e, he, hrets, hret, X, hst, hfr⟩ := h
  exact ⟨e.pc, e.frame, hret, hrets ▸ cert_check_at hc k e g he hg, X, hst, hfr⟩

theorem EntryAt.weaken {a0 : List AVal} {k : Nat} (hr : AVal.ret ∈ a0 → AVal.ret ∈ a)
    (h : EntryAt c m a0 ρ R k d) : EntryAt c m a ρ R k d := by
  obtain ⟨e, he, hrets, hret, rest⟩ := h
  exact ⟨e, he, hrets, fun hm => hr (hret hm), rest⟩

theorem CutStop.weaken {a0 : List AVal} {r : Seg} (hr : AVal.ret ∈ a0 → AVal.ret ∈ a)
    (h : CutStop c m a0 ρ R r) : CutStop c m a ρ R r := by
  match r, h with
  | .at _ _, h => exact EntryAt.weaken hr h
  | .done (.returned _), h => exact ⟨hr h.1, h.2⟩
  | .done (.halted _), _ => trivial

theorem FrameAt.next_noStateGas {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none) {n : Ninst}
    {f : SFunc} (h : FrameAt code c m pc a ρ R d (.next n f)) (run : Ninst.Run sevm d n d') :
    FrameNext code c m a ρ R d' f := by
  obtain ⟨hcheck, X, hst, hfr⟩ := h
  simp only [checkNode, Bool.and_eq_true] at hcheck
  obtain ⟨_, hrest⟩ := hcheck
  cases habs : absNinst n a with
  | none => simp only [habs, Bool.false_eq_true] at hrest
  | some a' =>
    simp only [habs] at hrest
    obtain ⟨X', hst', hfr'⟩ := Cursor.absNinst_run_stack_noStateGas hsg habs hst hfr run
    exact ⟨_, a', Cursor.ret_mem_of_absNinst habs, hrest, X', hst', hfr'⟩

theorem FrameAt.next {sevm : Sevm} (hfork : CoveredFork sevm.benvStat.fork) {n : Ninst}
    {f : SFunc} (h : FrameAt code c m pc a ρ R d (.next n f)) (run : Ninst.Run sevm d n d') :
    FrameNext code c m a ρ R d' f :=
  FrameAt.next_noStateGas hfork.rules_stateGas_none h run

theorem FrameAt.dest {f : SFunc} (h : FrameAt code c m pc a ρ R d (.dest f))
    (burn : Devm.Burn d d') : FrameNext code c m a ρ R d' f := by
  obtain ⟨hcheck, X, hst, hfr⟩ := h
  have h' : byteAt code pc = some (Jinst.toUInt8 .jumpdest) ∧
      checkNode code c.entries m (pc + 1) a f = true := by
    simpa only [checkNode, Bool.and_eq_true, beq_iff_eq] using hcheck
  exact ⟨_, a, id, h'.2, X, by rw [← burn.stack, hst], hfr⟩

theorem FrameAt.pcAt {sevm : Sevm} {p : Nat} {f : SFunc}
    (h : FrameAt code c m pc a ρ R d (.pcAt p f))
    (hrun : Ninst.StepRun p sevm d (.reg .pc) .none (.ok d')) :
    FrameNext code c m a ρ R d' f := by
  obtain ⟨hcheck, X, hst, hfr⟩ := h
  have h' : (bytesAt code pc (Ninst.toBytes (Ninst.reg .pc)) = true ∧ p = pc) ∧
      checkNode code c.entries m (pc + 1) (.const (Nat.toB256 pc) :: a) f = true := by
    simpa only [checkNode, Bool.and_eq_true, beq_iff_eq] using hcheck
  obtain ⟨⟨_, rfl⟩, hrest⟩ := h'
  refine ⟨_, _, fun hm => by simpa only [List.mem_cons, reduceCtorEq, false_or] using hm, hrest,
    Nat.toB256 p :: X, ?_, List.Forall₂.cons rfl hfr⟩
  rw [pc_stepRun_stack hrun, hst]
  rfl

theorem FrameAt.branch_zero {f g : SFunc} {x : B256}
    (h : FrameAt code c m pc a ρ R d (.branch f g)) (pop : Devm.PopBurn [x, 0] d d') :
    FrameNext code c m a ρ R d' f := by
  obtain ⟨hcheck, X, hst, hfr⟩ := h
  match a, hcheck, hfr with
  | .const t :: v :: a', hcheck, hfr =>
    have h' : (byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
          (v.jumps? = some true ∨ checkNode code c.entries m (pc + 1) a' f = true)) ∧
        (v.jumps? = some false ∨ checkNode code c.entries m t.toNat a' g = true) := by
      simpa only [checkNode, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] using hcheck
    obtain ⟨_, X1, hst1, hfr1⟩ := Cursor.pop_two_frame hst hfr pop
    exact ⟨_, a', fun hm => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm),
      live_fall (Cursor.pop_two_second hst hfr pop) h'.1.2, X1, hst1, hfr1⟩
  | [], hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | [.const _], hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | .ret :: _, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | .unk :: _, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck

theorem FrameAt.branch_succ {f g : SFunc} {x w : B256}
    (h : FrameAt code c m pc a ρ R d (.branch f g)) (hw : w ≠ 0)
    (pop : Devm.PopBurn [x, w] d d') : FrameNext code c m a ρ R d' g := by
  obtain ⟨hcheck, X, hst, hfr⟩ := h
  match a, hcheck, hfr with
  | .const t :: v :: a', hcheck, hfr =>
    have h' : (byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
          (v.jumps? = some true ∨ checkNode code c.entries m (pc + 1) a' f = true)) ∧
        (v.jumps? = some false ∨ checkNode code c.entries m t.toNat a' g = true) := by
      simpa only [checkNode, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] using hcheck
    obtain ⟨_, X1, hst1, hfr1⟩ := Cursor.pop_two_frame hst hfr pop
    exact ⟨_, a', fun hm => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm),
      live_taken hw (Cursor.pop_two_second hst hfr pop) h'.2, X1, hst1, hfr1⟩
  | [], hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | [.const _], hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | .ret :: _, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | .unk :: _, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck

theorem FrameAt.branchTo_zero {f : SFunc} {k : Nat} {x : B256}
    (h : FrameAt code c m pc a ρ R d (.branchTo f k)) (pop : Devm.PopBurn [x, 0] d d') :
    FrameNext code c m a ρ R d' f := by
  obtain ⟨hcheck, X, hst, hfr⟩ := h
  match a, hcheck, hfr with
  | .const t :: v :: a', hcheck, hfr =>
    cases hk : c.entries[k]? with
    | none => simp only [checkNode, hk, Bool.false_eq_true] at hcheck
    | some e =>
      have h' : (((byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
            e.pc = t.toNat) ∧ e.rets = m) ∧ gotoCompat a' e.frame = true) ∧
            (v.jumps? = some true ∨ checkNode code c.entries m (pc + 1) a' f = true) := by
        simpa only [checkNode, hk, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] using hcheck
      obtain ⟨_, X1, hst1, hfr1⟩ := Cursor.pop_two_frame hst hfr pop
      exact ⟨_, a', fun hm => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm),
        live_fall (Cursor.pop_two_second hst hfr pop) h'.2, X1, hst1, hfr1⟩
  | [], hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | [.const _], hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | .ret :: _, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | .unk :: _, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck

theorem FrameAt.branchTo_succ {f : SFunc} {k : Nat} {x w : B256}
    (h : FrameAt code c m pc a ρ R d (.branchTo f k)) (pop : Devm.PopBurn [x, w] d d') :
    EntryAt c m a ρ R k d' := by
  obtain ⟨hcheck, X, hst, hfr⟩ := h
  match a, hcheck, hfr with
  | .const t :: v :: a', hcheck, hfr =>
    cases hk : c.entries[k]? with
    | none => simp only [checkNode, hk, Bool.false_eq_true] at hcheck
    | some e =>
      have h' : (((byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
            e.pc = t.toNat) ∧ e.rets = m) ∧ gotoCompat a' e.frame = true) ∧
            (v.jumps? = some true ∨ checkNode code c.entries m (pc + 1) a' f = true) := by
        simpa only [checkNode, hk, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] using hcheck
      obtain ⟨_, X1, hst1, hfr1⟩ := Cursor.pop_two_frame hst hfr pop
      exact ⟨e, hk, h'.1.1.2, fun hm => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (ret_mem_of_gotoCompat h'.1.2 hm)), X1, hst1, frameMatches_gotoCompat h'.1.2 hfr1⟩
  | [], hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | [.const _], hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | .ret :: _, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | .unk :: _, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck

theorem FrameAt.jump {k : Nat} {x : B256} (h : FrameAt code c m pc a ρ R d (.jump k))
    (pop : Devm.PopBurn [x] d d') : EntryAt c m a ρ R k d' := by
  obtain ⟨hcheck, X, hst, hfr⟩ := h
  match a, hcheck, hfr with
  | .const t :: a', hcheck, hfr =>
    cases hk : c.entries[k]? with
    | none => simp only [checkNode, hk, Bool.false_eq_true] at hcheck
    | some e =>
      have h' : (((byteAt code pc = some (Jinst.toUInt8 .jump) ∧
            e.pc = t.toNat) ∧ e.rets = m) ∧ gotoCompat a' e.frame = true) := by
        simpa only [checkNode, hk, Bool.and_eq_true, beq_iff_eq] using hcheck
      obtain ⟨_, X1, hst1, hfr1⟩ := Cursor.pop_one_frame hst hfr pop
      exact ⟨e, hk, h'.1.2, fun hm => List.mem_cons_of_mem _ (ret_mem_of_gotoCompat h'.2 hm),
        X1, hst1, frameMatches_gotoCompat h'.2 hfr1⟩
  | [], hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | .ret :: _, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | .unk :: _, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck

theorem FrameAt.ret {x : B256} (h : FrameAt code c m pc a ρ R d .ret)
    (pop : Devm.PopBurn [x] d d') :
    AVal.ret ∈ a ∧ ∃ Y, d'.stack = Y ++ R ∧ Y.length = m := by
  obtain ⟨hcheck, X, hst, hfr⟩ := h
  match a, hcheck, hfr with
  | .ret :: a', hcheck, hfr =>
    have h' : byteAt code pc = some (Jinst.toUInt8 .jump) ∧ a'.length = m := by
      simpa only [checkNode, Bool.and_eq_true, beq_iff_eq] using hcheck
    obtain ⟨_, Y, hY, hfrY⟩ := Cursor.pop_one_frame hst hfr pop
    exact ⟨List.mem_cons_self, Y, hY, by rw [← List.Forall₂.length_eq hfrY, h'.2]⟩
  | [], hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | .const _ :: _, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | .unk :: _, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck

/-- An internal call: the callee entry runs from its declared frame above the caller's
untouched words `sr ++ R`; if it returns `e.rets` words over them (which needs `.ret` in its
frame), the continuation is a checked node over `R` again. -/
theorem FrameAt.call (hc : Cert.check code c = true) {k : Nat} {f g : SFunc} {x : B256}
    (h : FrameAt code c m pc a ρ R d (.callNext k f)) (pop : Devm.PopBurn [x] d d')
    (hg : c.prog[k]? = some g) :
    ∃ e r sr, c.entries[k]? = some e ∧ FrameAt code c e.rets e.pc e.frame r (sr ++ R) d' g ∧
      ∀ {D : Devm} {Y : List B256}, AVal.ret ∈ e.frame → D.stack = Y ++ (sr ++ R) →
        Y.length = e.rets → FrameNext code c m a ρ R D f := by
  obtain ⟨hcheck, X, hst, hfr⟩ := h
  match a, f, hcheck, hfr with
  | .const t :: a', .dest f0, hcheck, hfr =>
    cases hk : c.entries[k]? with
    | none => simp only [checkNode, hk, Bool.false_eq_true] at hcheck
    | some e =>
      simp only [checkNode, hk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcheck
      obtain ⟨_, hmatch⟩ := hcheck
      obtain ⟨_, X0, hst0, hfr0⟩ := Cursor.pop_one_frame hst hfr pop
      have hentry := cert_check_at hc k e g hk hg
      cases hi : e.frame.findIdx? (· == .ret) with
      | none =>
        simp only [hi] at hmatch
        obtain ⟨sf, sr, hX0, hsf, _⟩ := frameMatches_callCompat hmatch hfr0
        refine ⟨e, 0, sr, rfl, ⟨hentry, sf, by rw [hst0, hX0, List.append_assoc], hsf⟩, ?_⟩
        intro D Y hm
        exact (ret_not_mem_of_findIdx_none hi _ hm rfl).elim
      | some i =>
        simp only [hi] at hmatch
        cases har : a'[i]? with
        | none => simp only [har, Bool.false_eq_true] at hmatch
        | some av =>
          cases av with
          | ret => simp only [har, Bool.false_eq_true] at hmatch
          | unk => simp only [har, Bool.false_eq_true] at hmatch
          | const r =>
            simp only [har, Bool.and_eq_true] at hmatch
            obtain ⟨hcall, hcont⟩ := hmatch
            obtain ⟨sf, sr, hX0, hsf, hsr⟩ := frameMatches_callCompat hcall hfr0
            refine ⟨e, r, sr, rfl, ⟨hentry, sf, by rw [hst0, hX0, List.append_assoc], hsf⟩, ?_⟩
            intro D Y _ hD hY
            refine ⟨r.toNat, List.replicate e.rets .unk ++ a'.drop e.frame.length, ?_, ?_,
              Y ++ sr, by rw [hD, List.append_assoc], ?_⟩
            · intro hm
              rcases List.mem_append.mp hm with hm | hm
              · simp only [List.mem_replicate, ne_eq, reduceCtorEq, and_false] at hm
              · exact List.mem_cons_of_mem _ (List.mem_of_mem_drop hm)
            · simpa only [checkNode, Bool.and_eq_true] using hcont
            · rw [← hY]
              exact List.rel_append (frameMatches_unk_length Y) hsr
  | [], _, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | .ret :: _, _, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | .unk :: _, _, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | .const _ :: _, .next _ _, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | .const _ :: _, .branch _ _, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | .const _ :: _, .branchTo _ _, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | .const _ :: _, .last _, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | .const _ :: _, .jump _, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | .const _ :: _, .callNext _ _, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | .const _ :: _, .ret, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | .const _ :: _, .pcAt _ _, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | .const _ :: _, .undefined, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck

end Steps

/-! ## The frame-skip theorems -/

variable {P : Sevm → Devm → Ninst → Devm → Prop} {code : ByteArray} {c : Cert} {sevm : Sevm}

/-- **Stack-below preservation.**  A run of a checked node that returns leaves exactly `m` words
above the untouched `R` (and the node's frame mentions its return address). -/
theorem SFunc.RunP.stack_below_noStateGas (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (hc : Cert.check code c = true) (hsg : sevm.benvStat.rules.stateGas = none)
    {d : Devm} {f : SFunc} {o : Outcome} (run : SFunc.RunP P c.prog sevm d f o) :
    ∀ {m pc : Nat} {a : List AVal} {ρ : B256} {R : List B256},
      FrameAt code c m pc a ρ R d f → ∀ {D : Devm}, o = .returned D →
        AVal.ret ∈ a ∧ ∃ Y, D.stack = Y ++ R ∧ Y.length = m := by
  induction run with
  | zero _ pop _ ih =>
    intro m pc a ρ R h D hD
    obtain ⟨_, _, hr, h'⟩ := h.branch_zero pop
    exact (ih h' hD).imp_left hr
  | succ _ _ hw pop _ ih =>
    intro m pc a ρ R h D hD
    obtain ⟨_, _, hr, h'⟩ := h.branch_succ hw pop
    exact (ih h' hD).imp_left hr
  | toZero _ pop _ ih =>
    intro m pc a ρ R h D hD
    obtain ⟨_, _, hr, h'⟩ := h.branchTo_zero pop
    exact (ih h' hD).imp_left hr
  | toSucc _ _ _ lookup pop _ ih =>
    intro m pc a ρ R h D hD
    obtain ⟨_, _, hr, h'⟩ := (h.branchTo_succ pop).enter hc lookup
    exact (ih h' hD).imp_left hr
  | last _ => intro m pc a ρ R _ D hD; cases hD
  | next hrun _ ih =>
    intro m pc a ρ R h D hD
    obtain ⟨_, _, hr, h'⟩ := h.next_noStateGas hsg (hP hrun)
    exact (ih h' hD).imp_left hr
  | dest burn _ ih =>
    intro m pc a ρ R h D hD
    obtain ⟨_, _, hr, h'⟩ := h.dest burn
    exact (ih h' hD).imp_left hr
  | jump _ lookup pop _ ih =>
    intro m pc a ρ R h D hD
    obtain ⟨_, _, hr, h'⟩ := (h.jump pop).enter hc lookup
    exact (ih h' hD).imp_left hr
  | ret _ pop =>
    intro m pc a ρ R h D hD
    cases hD
    exact h.ret pop
  | callHalt _ _ _ _ _ => intro m pc a ρ R _ D hD; cases hD
  | callRet _ lookup pop _ _ ihRun ihTail =>
    intro m pc a ρ R h D hD
    obtain ⟨_, _, _, _, hcallee, hcont⟩ := h.call hc pop lookup
    obtain ⟨hretE, _, hY, hlen⟩ := ihRun hcallee rfl
    obtain ⟨_, _, hr, h'⟩ := hcont hretE hY hlen
    exact (ihTail h' hD).imp_left hr
  | pcAt _ hstep _ ih =>
    intro m pc a ρ R h D hD
    obtain ⟨_, _, hr, h'⟩ := h.pcAt hstep
    exact (ih h' hD).imp_left hr

/-- Stack-below preservation on a covered fork. -/
theorem SFunc.RunP.stack_below (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (hc : Cert.check code c = true) (hfork : CoveredFork sevm.benvStat.fork)
    {d : Devm} {f : SFunc} {o : Outcome} (run : SFunc.RunP P c.prog sevm d f o) :
    ∀ {m pc : Nat} {a : List AVal} {ρ : B256} {R : List B256},
      FrameAt code c m pc a ρ R d f → ∀ {D : Devm}, o = .returned D →
        AVal.ret ∈ a ∧ ∃ Y, D.stack = Y ++ R ∧ Y.length = m :=
  run.stack_below_noStateGas hP hc hfork.rules_stateGas_none

/-- **Stack-below preservation, cut form.**  Every stop of a checked node's cut run keeps the
words below its frame: a cut entry is entered with its declared frame above `R`, and a return
leaves exactly `m` words above `R`. -/
theorem SFunc.RunCutP.stack_below (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (hc : Cert.check code c = true) (hfork : CoveredFork sevm.benvStat.fork)
    {C : List Nat} {d : Devm} {f : SFunc} {r : Seg} (run : SFunc.RunCutP P c.prog sevm C d f r) :
    ∀ {m pc : Nat} {a : List AVal} {ρ : B256} {R : List B256},
      FrameAt code c m pc a ρ R d f → CutStop c m a ρ R r := by
  induction run with
  | zero _ pop _ ih =>
    intro m pc a ρ R h
    obtain ⟨_, _, hr, h'⟩ := h.branch_zero pop
    exact (ih h').weaken hr
  | succ _ _ hw pop _ ih =>
    intro m pc a ρ R h
    obtain ⟨_, _, hr, h'⟩ := h.branch_succ hw pop
    exact (ih h').weaken hr
  | toZero _ pop _ ih =>
    intro m pc a ρ R h
    obtain ⟨_, _, hr, h'⟩ := h.branchTo_zero pop
    exact (ih h').weaken hr
  | toSuccCut _ _ _ _ pop => intro m pc a ρ R h; exact h.branchTo_succ pop
  | toSucc _ _ _ _ lookup pop _ ih =>
    intro m pc a ρ R h
    obtain ⟨_, _, hr, h'⟩ := (h.branchTo_succ pop).enter hc lookup
    exact (ih h').weaken hr
  | last _ => intro m pc a ρ R _; trivial
  | next hrun _ ih =>
    intro m pc a ρ R h
    obtain ⟨_, _, hr, h'⟩ := h.next hfork (hP hrun)
    exact (ih h').weaken hr
  | dest burn _ ih =>
    intro m pc a ρ R h
    obtain ⟨_, _, hr, h'⟩ := h.dest burn
    exact (ih h').weaken hr
  | jumpCut _ _ pop => intro m pc a ρ R h; exact h.jump pop
  | jump _ _ lookup pop _ ih =>
    intro m pc a ρ R h
    obtain ⟨_, _, hr, h'⟩ := (h.jump pop).enter hc lookup
    exact (ih h').weaken hr
  | ret _ pop => intro m pc a ρ R h; exact h.ret pop
  | callHalt _ _ _ _ => intro m pc a ρ R _; trivial
  | callRet _ lookup pop callee _ ih =>
    intro m pc a ρ R h
    obtain ⟨_, _, _, _, hcallee, hcont⟩ := h.call hc pop lookup
    obtain ⟨hretE, _, hY, hlen⟩ := callee.stack_below hP hc hfork hcallee rfl
    obtain ⟨_, _, hr, h'⟩ := hcont hretE hY hlen
    exact (ih h').weaken hr
  | pcAt _ hstep _ ih =>
    intro m pc a ρ R h
    obtain ⟨_, _, hr, h'⟩ := h.pcAt hstep
    exact (ih h').weaken hr

/-- An entry run from its declared frame above `R` that returns leaves `e.rets` words above
`R`. -/
theorem SFunc.RunP.entry_stack_below_noStateGas (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (hc : Cert.check code c = true) (hsg : sevm.benvStat.rules.stateGas = none)
    {k : Nat} {e : Entry} {g : SFunc} (he : c.entries[k]? = some e) (hg : c.prog[k]? = some g)
    {ρ : B256} {X R : List B256} {d D : Devm} (hst : d.stack = X ++ R)
    (hfr : FrameMatches ρ e.frame X) (run : SFunc.RunP P c.prog sevm d g (.returned D)) :
    ∃ Y, D.stack = Y ++ R ∧ Y.length = e.rets :=
  (run.stack_below_noStateGas hP hc hsg ⟨cert_check_at hc k e g he hg, X, hst, hfr⟩ rfl).2

/-- Stack-below preservation for an entry run on a covered fork. -/
theorem SFunc.RunP.entry_stack_below (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (hc : Cert.check code c = true) (hfork : CoveredFork sevm.benvStat.fork)
    {k : Nat} {e : Entry} {g : SFunc} (he : c.entries[k]? = some e) (hg : c.prog[k]? = some g)
    {ρ : B256} {X R : List B256} {d D : Devm} (hst : d.stack = X ++ R)
    (hfr : FrameMatches ρ e.frame X) (run : SFunc.RunP P c.prog sevm d g (.returned D)) :
    ∃ Y, D.stack = Y ++ R ∧ Y.length = e.rets :=
  run.entry_stack_below_noStateGas hP hc hfork.rules_stateGas_none he hg hst hfr

/-- **Crossing a silent internal call.**  A `callNext` into an entry of a `SilentSet` closure,
from the walk state `St b (dd :: S) M G` whose top words match the callee's declared frame:
either the callee returns and the continuation runs from a state with `b`'s world state and the
stack `Y ++ S.drop e.frame.length`, `Y.length = e.rets`, or it halts the frame with `b`'s world
state. -/
theorem ric_call_silent (hc : Cert.check code c = true) (hfork : CoveredFork sevm.benvStat.fork)
    {Sk : List Nat} (hS : SilentSet c.prog Sk = true) {k : Nat} (hkS : k ∈ Sk) {e : Entry}
    {g : SFunc} (he : c.entries[k]? = some e) (hg : c.prog[k]? = some g)
    {C : List Nat} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {dd ρ : B256} {f : SFunc}
    {r : Seg} (hframe : FrameMatches ρ e.frame (S.take e.frame.length))
    (run : SFunc.RunCut c.prog sevm C (St b (dd :: S) M G) (.callNext k f) r) :
    (∃ b' Y M' G', b'.state = b.state ∧ Y.length = e.rets ∧
        SFunc.RunCut c.prog sevm C (St b' (Y ++ S.drop e.frame.length) M' G') f r) ∨
      (∃ D, D.state = b.state ∧ r = .done (.halted D)) := by
  have hgS : g.silent = true ∧ g.refs.all (· ∈ Sk) = true := by
    have h := (List.all_eq_true.mp hS) k hkS
    rw [hg] at h
    simpa only [Bool.and_eq_true] using h
  obtain ⟨G', h⟩ := ric_call hg run
  rcases h with ⟨D, callee, cont⟩ | ⟨D, callee, hr⟩
  · have hstate : D.state = b.state := SFunc.Run.state_of_silent hS hgS.1 hgS.2 callee
    obtain ⟨Y, hY, hlen⟩ := callee.entry_stack_below id hc hfork he hg
      (List.take_append_drop _ _).symm hframe
    rw [St.stack] at hY
    refine .inl ⟨D, Y, D.memory, D.gasLeft, hstate, hlen, ?_⟩
    rw [← St.self hY rfl]
    exact cont
  · exact .inr ⟨D, SFunc.Run.state_of_silent hS hgS.1 hgS.2 callee, hr⟩

end Blanc.Lift
