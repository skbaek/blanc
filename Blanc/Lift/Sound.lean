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
  apply of_decide_eq_true
  rw [ByteArray.toList_eq_toList_data]
  exact h

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
  apply Linst.at_of_slice
  rw [ByteArray.toList_eq_toList_data]
  apply byteAt_slice
  exact h

lemma byteAt_jinst_at {code : ByteArray} {pc : Nat} {j : Jinst}
    (h : byteAt code pc = some j.toUInt8) : Jinst.At code pc j := by
  apply Jinst.at_of_slice
  rw [ByteArray.toList_eq_toList_data]
  apply byteAt_slice
  exact h

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

lemma deriv_le_trans {p q r : Exec.Deriv}
    (hpq : Exec.Deriv.le p q) (hqr : Exec.Deriv.le q r) :
    Exec.Deriv.le p r := by
  induction hqr generalizing p with
  | refl => exact hpq
  | step hle prec ih => exact .step (ih hpq) prec

lemma deriv_lt_trans {p q r : Exec.Deriv}
    (hpq : Exec.Deriv.lt p q) (hqr : Exec.Deriv.lt q r) :
    Exec.Deriv.lt p r := by
  rcases hpq with ⟨p', hp, hp'⟩
  rcases hqr with ⟨q', hq, hq'⟩
  exact ⟨q', deriv_le_trans (Exec.Deriv.le.step hp hp') hq, hq'⟩

lemma jump_at_data {pc : Nat} {sevm : Sevm} {devm post : Devm}
    (exc : Exec pc sevm devm (.ok post))
    (jat : Jinst.At sevm.code pc .jump) :
    ∃ (x : B256) (inter : Devm) (exc' : Exec x.toNat sevm inter (.ok post)),
      Devm.PopBurn [x] devm inter ∧
      Exec.Deriv.Prec
        ⟨x.toNat, sevm, inter, .ok post, exc'⟩
        ⟨pc, sevm, devm, .ok post, exc⟩ := by
  rcases jump_at_exact exc jat with ⟨x, inter, exc', pop, _, _, prec⟩
  exact ⟨x, inter, exc', pop, prec⟩

lemma popBurn_one_stack {x : B256} {s s' : Devm}
    (h : Devm.PopBurn [x] s s') : s.stack = x :: s'.stack := by
  simpa [Stack.Pop, Split] using h.stack

lemma popBurn_two_stack {x y : B256} {s s' : Devm}
    (h : Devm.PopBurn [x, y] s s') : s.stack = x :: y :: s'.stack := by
  simpa [Stack.Pop, Split] using h.stack

lemma matches_some_map (xs : List B256) :
    AbstractStackSafety.Matches (xs.map some) xs := by
  induction xs with
  | nil => simp [AbstractStackSafety.Matches]
  | cons x xs ih => exact ⟨Or.inr rfl, ih⟩

lemma matches_some_map_eq {xs ys : List B256}
    (h : AbstractStackSafety.Matches (xs.map some) ys) : ys = xs := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => cases h
  | cons x xs ih =>
    cases ys with
    | nil => cases h
    | cons y ys =>
      have hy : y = x :=
        AbstractStackSafety.WordMatches.eq_of_some h.1
      subst y
      exact congrArg (fun z => x :: z) (ih h.2)

lemma mem_of_getElem?_eq_some {α} {xs : List α} {i : Nat} {x : α}
    (h : xs[i]? = some x) : x ∈ xs := by
  induction xs generalizing i with
  | nil => simp at h
  | cons y ys ih =>
    cases i with
    | zero => simp at h; cases h; simp
    | succ i => exact List.mem_cons_of_mem _ (ih (by simpa using h))

lemma ret_mem_of_readBack {a a' : List AVal} {out : List (Option B256)}
    (h : out.mapM (readBack a) = some a')
    (hm : AVal.ret ∈ a') : AVal.ret ∈ a := by
  induction out generalizing a' with
  | nil =>
    have ha : a' = [] := by simpa using h
    subst a'
    simp at hm
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    cases hr : readBack a x with
    | none => simp [hr] at h
    | some v =>
      cases ht : List.mapM (readBack a) xs with
      | none => simp [hr, ht] at h
      | some vs =>
        simp [hr, ht] at h
        subst a'
        simp only [List.mem_cons] at hm
        rcases hm with rfl | hm
        · cases x with
          | none => simp [readBack] at hr
          | some i =>
            apply mem_of_getElem?_eq_some
            simpa [readBack] using hr
        · exact ih ht hm

lemma matches_append {p q : Pattern} {s t : List B256}
    (hp : AbstractStackSafety.Matches p s)
    (hq : AbstractStackSafety.Matches q t) :
    AbstractStackSafety.Matches (p ++ q) (s ++ t) := by
  induction p generalizing s with
  | nil =>
    cases s with
    | nil => simpa using hq
    | cons x s => cases hp
  | cons w p ih =>
    cases s with
    | nil => cases hp
    | cons x s =>
      exact ⟨hp.1, ih hp.2⟩

lemma matches_split {p q : Pattern} {s : List B256}
    (h : AbstractStackSafety.Matches (p ++ q) s) :
    ∃ s1 s2, s = s1 ++ s2 ∧
      AbstractStackSafety.Matches p s1 ∧
      AbstractStackSafety.Matches q s2 := by
  induction p generalizing s with
  | nil => exact ⟨[], s, by simp, matches_nil, h⟩
  | cons w p ih =>
    cases s with
    | nil => cases h
    | cons x s =>
      rcases ih h.2 with ⟨s1, s2, hs, hp, hq⟩
      exact ⟨x :: s1, s2, by simp [hs], ⟨h.1, hp⟩, hq⟩

lemma matches_to_frame {ρ : B256} {a : List AVal} {s : List B256}
    (h : AbstractStackSafety.Matches (a.map (concrete ρ)) s) :
    FrameMatches ρ a s := by
  induction a generalizing s with
  | nil => cases s <;> simp [FrameMatches, AbstractStackSafety.Matches] at h ⊢
  | cons x a ih =>
    cases s with
    | nil => cases h
    | cons w s =>
      constructor
      · cases x with
        | const c => exact AbstractStackSafety.WordMatches.eq_of_some h.1
        | ret => exact AbstractStackSafety.WordMatches.eq_of_some h.1
        | unk => trivial
      · exact ih h.2

lemma push_run_stack {sevm : Sevm} {pre inter : Devm} {bs : Bytes}
    {fits : bs.length ≤ 32}
    (run : Ninst.Run sevm pre (.push bs fits) inter) :
    inter.stack = bs.toB256 :: pre.stack := by
  rcases run with ⟨xl, hfilled, pc, hstep⟩
  cases xl with
  | none =>
    rw [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at hstep
    rcases hstep with ⟨_, hstep⟩
    have hr :
        (chargeGas (if bs = [] then gBase else gVerylow) pre >>= fun d =>
          Devm.push bs.toB256 d) = .ok inter := hstep.symm
    rcases Except.bind_eq_ok hr with ⟨d, hcharge, hpush⟩
    rw [Devm.push_def] at hpush
    simp only [Except.assert, bind, Except.bind] at hpush
    split at hpush
    · cases hpush
    · injection hpush with hinter
      subst inter
      change bs.toB256 :: d.stack = bs.toB256 :: pre.stack
      rw [← (Devm.burn_of_chargeGas hcharge).stack]
  | some child =>
    rw [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at hstep
    cases hstep.1

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
    | branch f g =>
      cases a with
      | nil => simp [checkNode] at hcheck
      | cons av a0 =>
        cases av with
        | ret => simp [checkNode] at hcheck
        | unk => simp [checkNode] at hcheck
        | const t =>
          cases a0 with
          | nil => simp [checkNode] at hcheck
          | cons av2 a' =>
            have hcheck' :
                (byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
                  checkNode code c.entries m (pc + 1) a' f = true) ∧
                checkNode code c.entries m t.toNat a' g = true := by
              simpa [checkNode] using hcheck
            have h_at : Jinst.At sevm.code pc .jumpi := by
              apply byteAt_jinst_at
              rw [hcode]
              exact hcheck'.1.1
            cases S with
            | nil => cases hframe
            | cons s0 S0 =>
              cases S0 with
              | nil =>
                have hlen := List.Forall₂.length_eq hframe
                simp at hlen
              | cons s1 S1 =>
                cases hframe with
                | cons h0 hrest =>
                  cases hrest with
                  | cons h1 htail =>
                    have hs0 : s0 = t := h0
                    have hj := jumpi_at_exact exc h_at
                    rcases hj with z | z
                    · rcases z with ⟨x, inter, exc', pop, _, prec⟩
                      have hpop := popBurn_two_stack pop
                      rw [hstack] at hpop
                      have hx : x = t := by
                        have htx : s0 = x := by simpa using congrArg List.head? hpop
                        exact htx.symm.trans hs0
                      have hinter : inter.stack = S1 ++ base := by
                        have hpop' : s0 :: s1 :: (S1 ++ base) =
                            x :: 0 :: inter.stack := by simpa using hpop
                        have htail' : s1 :: (S1 ++ base) = 0 :: inter.stack :=
                          (List.cons.inj hpop').2
                        exact (List.cons.inj htail').2.symm
                      subst x
                      have hrun := ih
                        ⟨pc + 1, sevm, inter, .ok post, exc'⟩
                        (Exec.Deriv.lt_of_prec prec) post rfl hcode m a' f ρ S1 base
                        hcheck'.1.2 hinter htail
                      cases hrun with
                      | inl run => exact Or.inl (SFunc.Run.zero t pop run)
                      | inr run =>
                        rcases run with
                          ⟨hret, devm', S', exc'', hlt, run, hst, hlen⟩
                        exact Or.inr ⟨List.mem_cons_of_mem _
                            (List.mem_cons_of_mem _ hret), devm', S', exc'',
                          deriv_lt_trans hlt (Exec.Deriv.lt_of_prec prec),
                          SFunc.Run.zero t pop run, hst, hlen⟩
                    · rcases z with ⟨x, y, inter, exc', pop, _, _, hy, prec⟩
                      have hpop := popBurn_two_stack pop
                      rw [hstack] at hpop
                      have hx : x = t := by
                        have htx : s0 = x := by simpa using congrArg List.head? hpop
                        exact htx.symm.trans hs0
                      have hinter : inter.stack = S1 ++ base := by
                        have hpop' : s0 :: s1 :: (S1 ++ base) =
                            x :: y :: inter.stack := by simpa using hpop
                        have htail' : s1 :: (S1 ++ base) = y :: inter.stack :=
                          (List.cons.inj hpop').2
                        exact (List.cons.inj htail').2.symm
                      subst x
                      have hrun := ih
                        ⟨t.toNat, sevm, inter, .ok post, exc'⟩
                        (Exec.Deriv.lt_of_prec prec) post rfl hcode m a' g ρ S1 base
                        hcheck'.2 hinter htail
                      cases hrun with
                      | inl run => exact Or.inl (SFunc.Run.succ t y hy pop run)
                      | inr run =>
                        rcases run with
                          ⟨hret, devm', S', exc'', hlt, run, hst, hlen⟩
                        exact Or.inr ⟨List.mem_cons_of_mem _
                            (List.mem_cons_of_mem _ hret), devm', S', exc'',
                          deriv_lt_trans hlt (Exec.Deriv.lt_of_prec prec),
                          SFunc.Run.succ t y hy pop run, hst, hlen⟩
    | branchTo f k => sorry
    | last l =>
      have hbyte : byteAt code pc = some l.toUInt8 := by
        simpa [checkNode] using hcheck
      have h_at : Linst.At sevm.code pc l := by
        apply byteAt_linst_at
        rw [hcode]
        exact hbyte
      exact Or.inl (SFunc.Run.last (Linst.run_of_at exc h_at))
    | next n f =>
      cases n with
      | push bs fits =>
        have hcheck' :
            (bytesAt code pc (Ninst.toBytes (Ninst.push bs fits)) = true ∧
              Ninst.pcFree (Ninst.push bs fits) = true) ∧
            checkNode code c.entries m (pc + (Ninst.push bs fits).size)
              (.const (Bytes.toB256 bs) :: a) f = true := by
          simpa [checkNode, absNinst] using hcheck
        have h_at : Ninst.At sevm.code pc (.push bs fits) := by
          apply Ninst.at_of_slice
          apply bytesAt_slice (ninst_bytes_ne_nil (.push bs fits))
          rw [hcode]
          exact hcheck'.1.1
        rcases Ninst.run_of_at exc h_at with ⟨inter, exc', run, prec⟩
        have hstack' : inter.stack = Bytes.toB256 bs :: (S ++ base) := by
          rw [push_run_stack run, hstack]
        have hframe' :
            FrameMatches ρ (.const (Bytes.toB256 bs) :: a)
              (Bytes.toB256 bs :: S) := List.Forall₂.cons rfl hframe
        have hrun := ih ⟨pc + (Ninst.push bs fits).size, sevm, inter,
            .ok post, exc'⟩ (Exec.Deriv.lt_of_prec prec) post rfl hcode m
            (.const (Bytes.toB256 bs) :: a) f ρ
            (Bytes.toB256 bs :: S) base hcheck'.2 hstack' hframe'
        cases hrun with
        | inl run' => exact Or.inl (SFunc.Run.next run run')
        | inr run' =>
          rcases run' with ⟨hret, devm', S', exc'', hlt, run', hst, hlen⟩
          have hret' : AVal.ret ∈ a := by simpa using hret
          exact Or.inr ⟨hret', devm', S', exc'',
            deriv_lt_trans hlt (Exec.Deriv.lt_of_prec prec),
            SFunc.Run.next run run', hst, hlen⟩
      | reg r => sorry
      | exec x => sorry
      | dupn i => sorry
      | swapn i => sorry
      | exchange i => sorry
    | dest f =>
      have hcheck' : byteAt code pc = some (Jinst.toUInt8 .jumpdest) ∧
          checkNode code c.entries m (pc + 1) a f = true := by
        simpa [checkNode] using hcheck
      have hbyte : byteAt code pc = some (Jinst.toUInt8 .jumpdest) := hcheck'.1
      have h_at : Jinst.At sevm.code pc .jumpdest := by
        apply byteAt_jinst_at
        rw [hcode]
        exact hbyte
      rcases jumpdest_at_exact exc h_at with ⟨inter, exc', burn, _, prec⟩
      have hstack' : inter.stack = S ++ base := by
        rw [← burn.stack, hstack]
      have hrun := ih ⟨pc + 1, sevm, inter, .ok post, exc'⟩
        (Exec.Deriv.lt_of_prec prec) post rfl hcode m a f ρ S base
        hcheck'.2 hstack' hframe
      cases hrun with
      | inl run => exact Or.inl (SFunc.Run.dest burn run)
      | inr run =>
        rcases run with ⟨hret, devm', S', exc'', hlt, run, hst, hlen⟩
        exact Or.inr ⟨hret, devm', S', exc'', deriv_lt_trans hlt
          (Exec.Deriv.lt_of_prec prec), SFunc.Run.dest burn run, hst, hlen⟩
    | jump k => sorry
    | callNext k f => sorry
    | ret =>
      cases a with
      | nil => simp [checkNode] at hcheck
      | cons av a' =>
        cases av with
        | const c => simp [checkNode] at hcheck
        | unk => simp [checkNode] at hcheck
        | ret =>
          have hcheck' : byteAt code pc = some (Jinst.toUInt8 .jump) ∧
              a'.length = m := by
            simpa [checkNode] using hcheck
          have h_at : Jinst.At sevm.code pc .jump := by
            apply byteAt_jinst_at
            rw [hcode]
            exact hcheck'.1
          cases S with
          | nil => cases hframe
          | cons t S1 =>
            cases hframe with
            | cons hhead htail =>
              have ht : t = ρ := hhead
              rcases jump_at_exact exc h_at with
                ⟨x, inter, exc', pop, _, _, prec⟩
              have hx : x = ρ := by
                have hpop : devm.stack = x :: inter.stack := by
                  simpa [Stack.Pop, Split] using pop.stack
                rw [hstack] at hpop
                have htx : t = x := by
                  simpa using congrArg List.head? hpop
                exact htx.symm.trans ht
              have hinter : inter.stack = S1 ++ base := by
                have hpop : devm.stack = x :: inter.stack := by
                  simpa [Stack.Pop, Split] using pop.stack
                rw [hstack] at hpop
                simpa [hx] using (congrArg List.tail? hpop).symm
              have hlen : S1.length = m :=
                (List.Forall₂.length_eq htail).symm.trans hcheck'.2
              subst x
              exact Or.inr ⟨by simp, inter, S1, exc',
                Exec.Deriv.lt_of_prec prec, SFunc.Run.ret ρ pop, hinter,
                hlen⟩
    | undefined =>
      have hnone_code : code.getInst pc = none := by
        simpa [checkNode, Option.isNone_iff_eq_none] using hcheck
      have hnone : sevm.code.getInst pc = none := by
        rw [hcode]
        exact hnone_code
      have hstep := Evm.step_invOp (devm := devm) hnone
      cases Exec.halt_inv exc hstep

/-- **The lifting theorem.**  A successful execution of certified bytes from
pc `0` with an empty operand stack is a run of the certified program. -/
theorem lift_sound {code : ByteArray} {c : Cert} (hc : Cert.check code c = true)
    {sevm : Sevm} {pre post : Devm} (hcode : sevm.code = code)
    (hstack : pre.stack = []) (exc : Exec 0 sevm pre (.ok post)) :
    SProg.Run c.prog sevm pre post := by
  sorry

end Blanc.Lift
