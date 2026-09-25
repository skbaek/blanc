import Blanc.Lift.Check

/-!
# The lifting theorem (safety direction)

`lift_sound`: if a certificate checks against the bytes, every successful Jaune
execution of those bytes from pc `0` with an empty stack is a synthetic run of
the certificate's program.  It is stated over arbitrary bytes and certificates;
a contract instantiates it with one kernel-checked `Cert.check … = true`.

The proof is one strong recursion over `Exec.Deriv` (`node_sound`).  Its
invariant relates the concrete operand stack to an abstract frame: the stack is
`S ++ base`, where `S` matches the frame word by word (`FrameMatches ρ`, with
`.ret` read as the current function's return address `ρ`) and `base` belongs to
the callers and is left untouched.  A node either halts, or returns: the current
function jumps to `ρ` leaving exactly `m` words above `base`, and the remaining
derivation from `ρ` is strictly smaller, which is what lets the caller's
`callNext` continue by recursion.
-/

namespace Blanc.Lift

open Jaune AbstractStackSafety

/-- One abstract word describes one concrete word, reading `.ret` as `ρ`. -/
def AVal.Matches (ρ : B256) : AVal → B256 → Prop
  | .const c, w => w = c
  | .ret, w => w = ρ
  | .unk, _ => True

def FrameMatches (ρ : B256) (a : List AVal) (s : List B256) : Prop :=
  List.Forall₂ (AVal.Matches ρ) a s

def concrete (ρ : B256) : AVal → Option B256
  | .const c => some c
  | .ret => some ρ
  | .unk => none

def label (a : List AVal) (ρ : B256) : Option B256 → Option B256
  | none => none
  | some i => (a[i.toNat]?).bind (concrete ρ)

lemma frameMatches_matches {ρ : B256} {a : List AVal} {s : List B256}
    (h : FrameMatches ρ a s) :
    AbstractStackSafety.Matches (a.map (concrete ρ)) s := by
  induction h with
  | nil => simp [AbstractStackSafety.Matches]
  | @cons x y xs ys h rest ih =>
    cases x <;>
      simp only [AVal.Matches, concrete, List.map,
        AbstractStackSafety.Matches] at h ⊢
    · exact ⟨Or.inr (congrArg some h.symm), ih⟩
    · exact ⟨Or.inr (congrArg some h.symm), ih⟩
    · exact ⟨Or.inl rfl, ih⟩

lemma take?_of_take_eq {xs ys : List UInt8}
    (h : xs.take ys.length = ys) : xs.take? ys.length = some ys := by
  induction ys generalizing xs with
  | nil => simp only [List.length_nil, List.take?]
  | cons y ys ih =>
    cases xs with
    | nil => simp at h
    | cons x xs =>
      simp only [List.take, List.take?, List.length_cons] at h ⊢
      simp only [List.cons.injEq] at h
      simpa [h.1] using congrArg (Option.map (fun z => x :: z)) (ih h.2)

lemma slice_of_drop_take_eq {xs : List UInt8} {pc : Nat} {bs : Bytes}
    (hne : bs ≠ []) (h : (xs.drop pc).take bs.length = bs) :
    List.Slice xs pc bs := by
  induction pc generalizing xs with
  | zero =>
    refine ⟨bs.length, ?_⟩
    simpa [List.slice?, List.drop?] using take?_of_take_eq h
  | succ pc ih =>
    cases xs with
    | nil =>
      have hb : bs = [] := by simpa using h
      exact (hne hb).elim
    | cons x xs =>
      exact ih (by simpa using h)

lemma bytesAt_slice {code : ByteArray} {pc : Nat} {bs : Bytes}
    (hne : bs ≠ []) (h : bytesAt code pc bs = true) :
    List.Slice code.toList pc bs := by
  unfold bytesAt at h
  apply slice_of_drop_take_eq hne
  exact of_decide_eq_true h

lemma byteAt_slice {xs : List UInt8} {pc : Nat} {b : UInt8}
    (h : xs[pc]? = some b) : List.Slice xs pc [b] := by
  have hempty : List.Slice xs (pc + 1) [] := by
    induction pc generalizing xs with
    | zero =>
      cases xs with
      | nil => simp at h
      | cons x xs => exact ⟨0, by simp [List.slice?, List.drop?, List.take?]⟩
    | succ pc ih =>
      cases xs with
      | nil => simp at h
      | cons x xs => apply ih; simpa using h
  apply List.slice_cons_iff.mpr
  exact ⟨h, hempty⟩

lemma byteAt_linst_at {code : ByteArray} {pc : Nat} {l : Linst}
    (h : byteAt code pc = some l.toUInt8) : Linst.At code pc l := by
  exact Linst.at_of_slice (byteAt_slice h)

lemma byteAt_jinst_at {code : ByteArray} {pc : Nat} {j : Jinst}
    (h : byteAt code pc = some j.toUInt8) : Jinst.At code pc j := by
  exact Jinst.at_of_slice (byteAt_slice h)

lemma ninst_bytes_ne_nil (n : Ninst) : Ninst.toBytes n ≠ [] := by
  cases n <;> simp [Ninst.toBytes, pushToB8L]

lemma cert_pair_mem : ∀ (c : Cert) (k : Nat) (e : Entry) (f : SFunc),
    c.entries[k]? = some e → c.prog[k]? = some f → List.Mem (e, f) c
  | [], _, _, _, he, _ => by simp [Cert.entries] at he
  | (e0, f0) :: c, 0, e, f, he, hf => by
      simp only [Cert.entries, Cert.prog, List.map_cons,
        List.getElem?_cons_zero, Option.some.injEq] at he hf
      cases he; cases hf; exact List.mem_cons_self
  | (e0, f0) :: c, k + 1, e, f, he, hf => by
      apply List.mem_cons_of_mem
      apply cert_pair_mem c k e f
      · simpa [Cert.entries] using he
      · simpa [Cert.prog] using hf

lemma cert_check_at {code : ByteArray} {c : Cert} (hc : Cert.check code c = true)
    (k : Nat) (e : Entry) (f : SFunc)
    (he : c.entries[k]? = some e) (hf : c.prog[k]? = some f) :
    checkNode code c.entries e.rets e.pc e.frame f = true := by
  have hmem := cert_pair_mem c k e f he hf
  have hc' := hc
  simp only [Cert.check, Bool.and_eq_true] at hc'
  exact List.all_eq_true.mp hc'.2 (e, f) hmem

lemma mapM_readBack_label {a a' : List AVal} {out : List (Option B256)}
    {ρ : B256} (h : out.mapM (readBack a) = some a') :
    out.map (label a ρ) = a'.map (concrete ρ) := by
  induction out generalizing a' with
  | nil => simp at h ⊢; cases h; rfl
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind] at h
    cases hr : readBack a x with
    | none => simp [hr] at h
    | some v =>
      cases ht : List.mapM (readBack a) xs with
      | none => simp [hr, ht] at h
      | some vs =>
        simp [hr, ht] at h
        subst a'
        simp only [List.map_cons]
        rw [ih ht]
        cases x with
        | none => simp [label, readBack] at hr ⊢; cases hr; rfl
        | some i => simp [label, readBack] at hr ⊢; rw [hr]; rfl

lemma indexPattern_map_label {a : List AVal} {ρ : B256}
    (hlen : a.length ≤ 1024) :
    (indexPattern a.length).map (label a ρ) = a.map (concrete ρ) := by
  have map_range_congr : ∀ {n : Nat} {f g : Nat → Option B256},
      (∀ i, i < n → f i = g i) →
      (List.range n).map f = (List.range n).map g := by
    intro n
    induction n with
    | zero => intro f g _; rfl
    | succ n ih =>
      intro f g h
      rw [List.range_succ, List.map_append]
      rw [ih (fun i hi => h i (by omega))]
      simp [h n (by omega)]
  induction a with
  | nil => rfl
  | cons x a ih =>
    simp only [List.length_cons] at hlen
    have htail : a.length ≤ 1024 := by omega
    simp only [indexPattern, List.length_cons, List.range_succ_eq_map,
      List.map_cons, List.map_map]
    have hshift :
        (List.range a.length).map
            (label (x :: a) ρ ∘ (fun i => some (Nat.toB256 i)) ∘ Nat.succ) =
          (List.range a.length).map (label a ρ ∘ fun i => some (Nat.toB256 i)) := by
      apply map_range_congr
      intro i hi
      simp [label, Function.comp_def,
        B256.toNat_toB256_of_lt (by omega : i + 1 < 2 ^ 256),
        B256.toNat_toB256_of_lt (by omega : i < 2 ^ 256)]
    rw [hshift, ← ih htail]
    have hzero : (Nat.toB256 0).toNat = 0 :=
      B256.toNat_toB256_of_lt (by omega)
    simp [label, concrete, hzero, Function.comp_def, indexPattern]

/-- The recursion invariant.  For a successful derivation at a node checked
with frame `a` and return arity `m`: the node's run halts with the derivation's
result, or the current function returns — then `.ret` occurs in the frame, the
run returns `devm'` whose stack is `S' ++ base` with `S'.length = m`, and the
rest of the execution is a strictly smaller derivation from `ρ`. -/
def NodeClaim (code : ByteArray) (c : Cert) (pk : Exec.Deriv) : Prop :=
  ∀ (post : Devm), pk.exn = .ok post → pk.sevm.code = code →
  ∀ (m : Nat) (a : List AVal) (f : SFunc) (ρ : B256) (S base : List B256),
    checkNode code c.entries m pk.pc a f = true →
    pk.devm.stack = S ++ base → FrameMatches ρ a S →
    SFunc.Run c.prog pk.sevm pk.devm f (.halted post) ∨
    (AVal.ret ∈ a ∧
      ∃ (devm' : Devm) (S' : List B256) (exc' : Exec ρ.toNat pk.sevm devm' (.ok post)),
        Exec.Deriv.lt ⟨ρ.toNat, pk.sevm, devm', .ok post, exc'⟩ pk ∧
        SFunc.Run c.prog pk.sevm pk.devm f (.returned devm') ∧
        devm'.stack = S' ++ base ∧ S'.length = m)

theorem node_sound {code : ByteArray} {c : Cert} (hc : Cert.check code c = true) :
    ∀ pk : Exec.Deriv, NodeClaim code c pk := by
  apply Exec.Deriv.strongRec
  intro pk ih
  intro post hpost hcode m a f ρ S base hcheck hstack hframe
  rcases pk with ⟨pc, sevm, devm, exn, exc⟩
  cases exn with
  | error e => cases hpost
  | ok post =>
    cases hpost
    cases f with
    | branch f g => sorry
    | last l =>
      have hbyte : byteAt code pc = some l.toUInt8 := by
        simpa [checkNode] using hcheck
      have h_at : Linst.At sevm.code pc l := by
        apply byteAt_linst_at
        rw [hcode]
        exact hbyte
      exact Or.inl (SFunc.Run.last (Linst.run_of_at exc h_at))
    | next n f => sorry
    | dest f => sorry
    | jump k => sorry
    | callNext k f => sorry
    | ret => sorry
    | undefined => sorry

/-- **The lifting theorem.**  A successful execution of certified bytes from
pc `0` with an empty operand stack is a run of the certified program. -/
theorem lift_sound {code : ByteArray} {c : Cert} (hc : Cert.check code c = true)
    {sevm : Sevm} {pre post : Devm} (hcode : sevm.code = code)
    (hstack : pre.stack = []) (exc : Exec 0 sevm pre (.ok post)) :
    SProg.Run c.prog sevm pre post := by
  sorry

end Blanc.Lift
