import Blanc.Lift.Cursor

/-!
# Certified external-instruction operands

The observer reuses the checker's abstract operand frame and the existing
cursor's internal-call bookkeeping. Its conclusions concern actual decoded
same-frame occurrences, without a successful-frame premise.
-/

namespace Blanc.Lift

open Jaune

/-- Check an external instruction against its incoming abstract operand frame. -/
def SFunc.execOperandsSatisfy (es : List Entry)
    (observe : Xinst → List AVal → Bool) : List AVal → SFunc → Bool
  | a, .next (.exec x) f =>
    observe x a &&
    match absNinst (.exec x) a with
    | some a' => f.execOperandsSatisfy es observe a'
    | none => true
  | a, .next n f =>
    match absNinst n a with
    | some a' => f.execOperandsSatisfy es observe a'
    | none => true
  | a, .dest f => f.execOperandsSatisfy es observe a
  | _ :: _ :: a', .branchTo f _ => f.execOperandsSatisfy es observe a'
  | _ :: _ :: a', .branch f g =>
      f.execOperandsSatisfy es observe a' && g.execOperandsSatisfy es observe a'
  | _ :: a', .callNext k f =>
    match es[k]? with
    | some e => f.execOperandsSatisfy es observe
        (List.replicate e.rets .unk ++ a'.drop e.frame.length)
    | none => true
  | a, .pcAt p f => f.execOperandsSatisfy es observe (.const (Nat.toB256 p) :: a)
  | _, _ => true

/-- Every entry is observed under its declared abstract frame. -/
def Cert.execOperandsSatisfy (c : Cert) (observe : Xinst → List AVal → Bool) : Bool :=
  c.all fun (e, f) => f.execOperandsSatisfy c.entries observe e.frame

/-- The observation holds at the active tree and every suspended return. -/
def Cursor.ExecOperandsSatisfy (c : Cert) (observe : Xinst → List AVal → Bool)
    (κ : Cursor) : Prop :=
  κ.f.execOperandsSatisfy c.entries observe κ.a = true ∧
    ∀ k ∈ κ.K,
      k.f.execOperandsSatisfy c.entries observe
        (List.replicate k.rets .unk ++ k.a) = true

private theorem Cert.execOperandsSatisfy_entry {c : Cert}
    {observe : Xinst → List AVal → Bool} (checked : c.execOperandsSatisfy observe = true)
    {k : Nat} {e : Entry} {g : SFunc}
    (he : c.entries[k]? = some e) (hg : c.prog[k]? = some g) :
    g.execOperandsSatisfy c.entries observe e.frame = true := by
  have hk : k < c.length := by
    have hlt := (List.getElem?_eq_some_iff.mp he).1
    simpa only [Cert.entries, List.length_map] using hlt
  have he' : c.entries[k]? = some (c[k]).1 := by
    simp only [Cert.entries, List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some]
  have hg' : c.prog[k]? = some (c[k]).2 := by
    simp only [Cert.prog, List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some]
  have ee := Option.some.inj (he.symm.trans he')
  have eg := Option.some.inj (hg.symm.trans hg')
  have hmem : c[k] ∈ c := List.getElem_mem hk
  have holds := List.all_eq_true.mp checked c[k] hmem
  rw [ee, eg]
  exact holds

/-- Abstract next steps retain the observation, including internal returns. -/
theorem SStep.execOperandsSatisfy {c : Cert} {observe : Xinst → List AVal → Bool}
    (checked : c.execOperandsSatisfy observe = true) {before after : Cursor}
    (step : SStep c before after) (holds : before.ExecOperandsSatisfy c observe) :
    after.ExecOperandsSatisfy c observe := by
  obtain ⟨hf, hK⟩ := holds
  cases step with
  | @next n f pc a a' m K hn =>
      refine ⟨?_, hK⟩
      cases n with
      | exec x =>
          simp only [SFunc.execOperandsSatisfy, hn, Bool.and_eq_true] at hf
          exact hf.2
      | _ =>
          simp only [SFunc.execOperandsSatisfy, hn] at hf
          exact hf
  | dest | pcAt => exact ⟨hf, hK⟩
  | toZero =>
      simp only [SFunc.execOperandsSatisfy] at hf
      exact ⟨hf, hK⟩
  | zero =>
      simp only [SFunc.execOperandsSatisfy, Bool.and_eq_true] at hf
      exact ⟨hf.1, hK⟩
  | succ =>
      simp only [SFunc.execOperandsSatisfy, Bool.and_eq_true] at hf
      exact ⟨hf.2, hK⟩
  | toSucc he hg | jump he hg =>
      exact ⟨Cert.execOperandsSatisfy_entry checked he hg, hK⟩
  | call κc he hg hcf hca _ hcr =>
      refine ⟨Cert.execOperandsSatisfy_entry checked he hg, fun k hk => ?_⟩
      rcases List.mem_cons.mp hk with rfl | hk
      · rw [hcr, hca, hcf]
        simp only [SFunc.execOperandsSatisfy, he] at hf
        exact hf
      · exact hK k hk
  | ret =>
      exact ⟨hK _ List.mem_cons_self, fun k hk => hK k (List.mem_cons_of_mem _ hk)⟩

/-- A checked certificate's initial abstract frame is empty, as Cursor.start requires. -/
theorem Cursor.start_execOperandsSatisfy {code : ByteArray} {c : Cert}
    (valid : Cert.check code c = true) {observe : Xinst → List AVal → Bool}
    (checked : c.execOperandsSatisfy observe = true) :
    (Cursor.start c).ExecOperandsSatisfy c observe := by
  cases c with
  | nil =>
      simp only [Cert.check, List.all_nil, Bool.and_true, Bool.false_eq_true] at valid
  | cons entry rest =>
      rcases entry with ⟨e, f⟩
      have first := valid
      simp only [Cert.check, List.beq_nil_eq, List.all_cons, Bool.and_eq_true, beq_iff_eq,
        List.isEmpty_iff, List.all_eq_true, Prod.forall] at first
      have empty : e.frame = [] := first.1.2
      have observed := (List.all_eq_true.mp checked (e, f) List.mem_cons_self)
      refine ⟨?_, fun _ h => ?_⟩
      · simpa only [Cursor.start, empty] using observed
      · simp only [Cursor.start, List.not_mem_nil] at h

/-- Every synthetically reachable cursor retains the certificate's observation. -/
theorem Cursor.execOperandsSatisfy_of_reachable {code : ByteArray} {c : Cert}
    (valid : Cert.check code c = true) {observe : Xinst → List AVal → Bool}
    (checked : c.execOperandsSatisfy observe = true) {κ : Cursor}
    (reach : Relation.ReflTransGen (SStep c) (Cursor.start c) κ) :
    κ.ExecOperandsSatisfy c observe := by
  induction reach with
  | refl => exact Cursor.start_execOperandsSatisfy valid checked
  | tail _ step ih => exact step.execOperandsSatisfy checked ih

/-- Actual decoding selects the observation at the same checked cursor. -/
theorem CursorOK.execOperandsSatisfy {code : ByteArray} {c : Cert}
    {node : Exec.Deriv} {κ : Cursor} (ok : CursorOK code c node κ)
    {observe : Xinst → List AVal → Bool} (holds : κ.ExecOperandsSatisfy c observe)
    {x : Xinst} (instruction : Ninst.At node.sevm.code node.pc (.exec x)) :
    observe x κ.a = true := by
  obtain ⟨tail, tree, -⟩ := ok.tree_of_exec instruction
  have observed := holds.1
  rw [tree] at observed
  exact ((Bool.and_eq_true _ _).mp observed).1

private theorem FrameMatches.getElem?_const {ρ : B256} {a : List AVal} {s : List B256}
    (matched : FrameMatches ρ a s) {i : Nat} {w : B256}
    (known : a[i]? = some (.const w)) : s[i]? = some w := by
  induction matched generalizing i with
  | nil => simp only [List.getElem?_nil, reduceCtorEq] at known
  | @cons av v as vs head tail ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at known
          subst av
          change v = w at head
          exact congrArg some head
      | succ i =>
          simp only [List.getElem?_cons_succ] at known ⊢
          exact ih known

/-- A certified constant describes that exact word of the real operand stack. -/
theorem CursorOK.stack_getElem?_const {code : ByteArray} {c : Cert}
    {node : Exec.Deriv} {κ : Cursor} (ok : CursorOK code c node κ)
    {i : Nat} {w : B256} (known : κ.a[i]? = some (.const w)) :
    node.devm.stack[i]? = some w := by
  obtain ⟨S, rest, stack, matched, -⟩ := ok.stack
  have actual := FrameMatches.getElem?_const matched known
  rw [stack, List.getElem?_append_left (List.getElem?_eq_some_iff.mp actual).1]
  exact actual

end Blanc.Lift
