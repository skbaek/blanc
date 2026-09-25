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

lemma absNinst_nonpush_eq {n : Ninst} {a : List AVal}
    (hn : ∀ (bs : Bytes) (fits : bs.length ≤ 32), n ≠ .push bs fits) :
    absNinst n a =
      (do
        guard (a.length ≤ 1024)
        let out ← ninstTransfer n (indexPattern a.length)
        out.mapM (readBack a)) := by
  cases n with
  | push bs fits => exact (hn bs fits rfl).elim
  | reg r => rfl
  | exec x => rfl
  | dupn i => rfl
  | swapn i => rfl
  | exchange i => rfl

lemma absNinst_nonpush_spec {n : Ninst} {a a' : List AVal}
    (hn : ∀ (bs : Bytes) (fits : bs.length ≤ 32), n ≠ .push bs fits)
    (h : absNinst n a = some a') :
    a.length ≤ 1024 ∧ ∃ out,
      ninstTransfer n (indexPattern a.length) = some out ∧
      out.mapM (readBack a) = some a' := by
  rw [absNinst_nonpush_eq hn] at h
  by_cases hlen : a.length ≤ 1024
  · cases ht : ninstTransfer n (indexPattern a.length) with
    | none => simp [hlen, ht] at h
    | some out =>
      cases hr : out.mapM (readBack a) with
      | none => simp [hlen, ht, hr] at h
      | some a'' =>
        simp [hlen, ht, hr] at h
        cases h
        exact ⟨hlen, out, by simpa using ht, hr⟩
  · simp [hlen] at h

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

lemma cert_prog_of_entry : ∀ (c : Cert) (k : Nat) (e : Entry),
    c.entries[k]? = some e → ∃ f, c.prog[k]? = some f
  | [], _, _, he => by simp [Cert.entries] at he
  | (e0, f0) :: c, 0, e, he => by
      simp only [Cert.entries, Cert.prog, List.map_cons,
        List.getElem?_cons_zero, Option.some.injEq] at he
      cases he
      exact ⟨f0, by simp [Cert.prog]⟩
  | (e0, f0) :: c, k + 1, e, he => by
      apply cert_prog_of_entry c k e
      simpa [Cert.entries] using he

lemma frameMatches_gotoCompat {ρ : B256} :
    ∀ {a e s}, gotoCompat a e = true → FrameMatches ρ a s →
      FrameMatches ρ e s := by
  intro a
  induction a with
  | nil =>
    intro e s hg hm
    cases e with
    | nil => exact hm
    | cons e es => simp [gotoCompat] at hg
  | cons av a ih =>
    intro e s hg hm
    cases e with
    | nil => simp [gotoCompat] at hg
    | cons ev es =>
      cases hm with
      | cons hhead htail =>
        cases av <;> cases ev <;>
          simp_all [gotoCompat, FrameMatches, AVal.Matches]

lemma ret_mem_of_gotoCompat : ∀ {a e : List AVal},
    gotoCompat a e = true → AVal.ret ∈ e → AVal.ret ∈ a := by
  intro a
  induction a with
  | nil =>
    intro e hg hm
    cases e with
    | nil => simp at hm
    | cons e es => simp [gotoCompat] at hg
  | cons av a ih =>
    intro e hg hm
    cases e with
    | nil => simp [gotoCompat] at hg
    | cons ev es =>
      cases av <;> cases ev <;>
        simp_all [gotoCompat] <;>
        first | exact ih hg.2 hm | exact ih hg hm

lemma frameMatches_callCompat {r ρ : B256} :
    ∀ {a e : List AVal} {s : List B256},
      callCompat r a e = true → FrameMatches ρ a s →
      ∃ sf sr, s = sf ++ sr ∧ FrameMatches r e sf ∧
        FrameMatches ρ (a.drop e.length) sr := by
  intro a
  induction a with
  | nil =>
    intro e s hc hm
    cases e with
    | nil =>
      exact ⟨[], s, by simp, by simp [FrameMatches], by simpa using hm⟩
    | cons ev es => simp [callCompat] at hc
  | cons av a ih =>
    intro e s hc hm
    cases e with
    | nil =>
      exact ⟨[], s, by simp, by simp [FrameMatches], by simpa using hm⟩
    | cons ev es =>
      cases s with
      | nil => cases hm
      | cons w s =>
        cases hm with
        | cons hhead htail =>
          cases av <;> cases ev <;> simp [callCompat] at hc
          all_goals
            have hcall : callCompat r a es = true := by
              first | exact hc.2 | exact hc
            rcases ih hcall htail with ⟨sf, sr, hs, hf, hr⟩
            refine ⟨w :: sf, sr, ?_, ?_, ?_⟩
            · simp [hs]
            · apply List.Forall₂.cons
              · first
                | simpa [AVal.Matches, hc.1] using hhead
                | trivial
              · exact hf
            · simpa [hs] using hr

lemma ret_not_mem_of_findIdx_none {xs : List AVal}
    (h : xs.findIdx? (· == .ret) = none) :
    ∀ x, x ∈ xs → x ≠ AVal.ret := by
  intro x hx
  have hf := (List.findIdx?_eq_none_iff.mp h) x hx
  simpa using hf

lemma frameMatches_unk_length {ρ : B256} : ∀ s : List B256,
    FrameMatches ρ (List.replicate s.length .unk) s := by
  intro s
  induction s with
  | nil => simp [FrameMatches]
  | cons w s ih =>
    change List.Forall₂ (AVal.Matches ρ)
      (.unk :: List.replicate s.length .unk) (w :: s)
    exact List.Forall₂.cons trivial ih

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

lemma ret_mem_of_findIdx {xs : List AVal} {i : Nat}
    (h : xs.findIdx? (· == .ret) = some i) : AVal.ret ∈ xs := by
  have hp := List.of_findIdx?_eq_some h
  cases hx : xs[i]? with
  | none => simp [hx] at hp
  | some a =>
    have ha : a = AVal.ret := by simpa [hx] using hp
    subst a
    exact mem_of_getElem?_eq_some hx

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
  CoveredFork pk.sevm.benvStat.fork →
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
  intro post hpost hcode hfork m a f ρ S base hcheck hstack hframe
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
                        (Exec.Deriv.lt_of_prec prec) post rfl hcode hfork m a' f ρ S1 base
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
                        (Exec.Deriv.lt_of_prec prec) post rfl hcode hfork m a' g ρ S1 base
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
    | branchTo f k =>
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
            cases hk : c.entries[k]? with
            | none => simp [checkNode, hk] at hcheck
            | some e =>
              have hcheck' :
                  (((byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
                    e.pc = t.toNat) ∧ e.rets = m) ∧
                    gotoCompat a' e.frame = true) ∧
                    checkNode code c.entries m (pc + 1) a' f = true := by
                simpa [checkNode, hk] using hcheck
              rcases cert_prog_of_entry c k e hk with ⟨g, hg⟩
              have hentry := cert_check_at hc k e g hk hg
              have h_at : Jinst.At sevm.code pc .jumpi := by
                apply byteAt_jinst_at
                rw [hcode]
                exact hcheck'.1.1.1.1
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
                          have htx : s0 = x := by
                            simpa using congrArg List.head? hpop
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
                          (Exec.Deriv.lt_of_prec prec) post rfl hcode hfork m a' f ρ
                          S1 base hcheck'.2 hinter htail
                        cases hrun with
                        | inl run => exact Or.inl (SFunc.Run.toZero t pop run)
                        | inr run =>
                          rcases run with
                            ⟨hret, devm', S', exc'', hlt, run, hst, hlen⟩
                          exact Or.inr ⟨List.mem_cons_of_mem _
                              (List.mem_cons_of_mem _ hret), devm', S', exc'',
                            deriv_lt_trans hlt (Exec.Deriv.lt_of_prec prec),
                            SFunc.Run.toZero t pop run, hst, hlen⟩
                      · rcases z with ⟨x, y, inter, exc', pop, _, _, hy, prec⟩
                        have hpop := popBurn_two_stack pop
                        rw [hstack] at hpop
                        have hx : x = t := by
                          have htx : s0 = x := by
                            simpa using congrArg List.head? hpop
                          exact htx.symm.trans hs0
                        have hinter : inter.stack = S1 ++ base := by
                          have hpop' : s0 :: s1 :: (S1 ++ base) =
                              x :: y :: inter.stack := by simpa using hpop
                          have htail' : s1 :: (S1 ++ base) = y :: inter.stack :=
                            (List.cons.inj hpop').2
                          exact (List.cons.inj htail').2.symm
                        have hframe' : FrameMatches ρ e.frame S1 :=
                          frameMatches_gotoCompat hcheck'.1.2 htail
                        have hentry' :
                            checkNode code c.entries e.rets t.toNat e.frame g = true := by
                          simpa [hcheck'.1.1.1.2] using hentry
                        subst x
                        have hrun := ih
                          ⟨t.toNat, sevm, inter, .ok post, exc'⟩
                          (Exec.Deriv.lt_of_prec prec) post rfl hcode hfork e.rets
                          e.frame g ρ S1 base hentry' hinter hframe'
                        cases hrun with
                        | inl run => exact Or.inl (SFunc.Run.toSucc t y hy hg pop run)
                        | inr run =>
                          rcases run with
                            ⟨hret, devm', S', exc'', hlt, run, hst, hlen⟩
                          have hret' : AVal.ret ∈ a' :=
                            ret_mem_of_gotoCompat hcheck'.1.2 hret
                          have hlen' : S'.length = m := by
                            simpa [hcheck'.1.1.2] using hlen
                          exact Or.inr ⟨List.mem_cons_of_mem _
                              (List.mem_cons_of_mem _ hret'), devm', S', exc'',
                            deriv_lt_trans hlt (Exec.Deriv.lt_of_prec prec),
                            SFunc.Run.toSucc t y hy hg pop run, hst, hlen'⟩
    | last l =>
      have hbyte : byteAt code pc = some l.toUInt8 := by
        simpa [checkNode] using hcheck
      have h_at : Linst.At sevm.code pc l := by
        apply byteAt_linst_at
        rw [hcode]
        exact hbyte
      exact Or.inl (SFunc.Run.last (Linst.run_of_at exc h_at))
    | next n f =>
      have next_nonpush (n : Ninst) (a' : List AVal) (out : Pattern)
          (hlen : a.length ≤ 1024)
          (htrans : ninstTransfer n (indexPattern a.length) = some out)
          (hread : out.mapM (readBack a) = some a')
          (hchild : checkNode code c.entries m (pc + n.size) a' f = true)
          (h_at : Ninst.At sevm.code pc n) :
          SFunc.Run c.prog sevm devm (.next n f) (.halted post) ∨
          (AVal.ret ∈ a ∧
            ∃ (devm' : Devm) (S' : List B256)
              (exc' : Exec ρ.toNat sevm devm' (.ok post)),
              Exec.Deriv.lt
                  ⟨ρ.toNat, sevm, devm', .ok post, exc'⟩
                  ⟨pc, sevm, devm, .ok post, exc⟩ ∧
              SFunc.Run c.prog sevm devm (.next n f) (.returned devm') ∧
              devm'.stack = S' ++ base ∧ S'.length = m) := by
        rcases Ninst.run_of_at exc h_at with ⟨inter, exc', run, prec⟩
        have hinput :
            Matches
                ((indexPattern a.length).map (label a ρ) ++ base.map some)
                devm.stack := by
          rw [hstack]
          apply matches_append
          · rw [indexPattern_map_label hlen]
            exact frameMatches_matches hframe
          · exact matches_some_map base
        have hmap := ninstTransfer_map (label a ρ) rfl htrans
        have happ := ninstTransfer_append (base.map some) hmap
        have hout := ninstTransfer_run hfork hinput happ run
        rw [mapM_readBack_label hread] at hout
        rcases matches_split hout with ⟨S', below, hsp, hfirst, hbelow⟩
        have hbelow' : below = base := matches_some_map_eq hbelow
        have hinter : inter.stack = S' ++ base := by
          simpa [hbelow'] using hsp
        have hframe' : FrameMatches ρ a' S' := matches_to_frame hfirst
        have hrun := ih
          ⟨pc + n.size, sevm, inter, .ok post, exc'⟩
          (Exec.Deriv.lt_of_prec prec) post rfl hcode hfork m a' f ρ S' base
          hchild hinter hframe'
        cases hrun with
        | inl run' => exact Or.inl (SFunc.Run.next run run')
        | inr run' =>
          rcases run' with ⟨hret, devm', Sret, exc'', hlt, run', hst, hlen'⟩
          have hret' : AVal.ret ∈ a := ret_mem_of_readBack hread hret
          exact Or.inr ⟨hret', devm', Sret, exc'',
            deriv_lt_trans hlt (Exec.Deriv.lt_of_prec prec),
            SFunc.Run.next run run', hst, hlen'⟩
      have next_checked (n : Ninst)
          (hnpush : ∀ (bs : Bytes) (fits : bs.length ≤ 32),
            n ≠ .push bs fits)
          (hcheck :
            (bytesAt code pc (Ninst.toBytes n) = true ∧
              Ninst.pcFree n = true) ∧
            (match absNinst n a with
             | some a' => checkNode code c.entries m (pc + n.size) a' f
             | none => false) = true)
          (h_at : Ninst.At sevm.code pc n) :
          SFunc.Run c.prog sevm devm (.next n f) (.halted post) ∨
          (AVal.ret ∈ a ∧
            ∃ (devm' : Devm) (S' : List B256)
              (exc' : Exec ρ.toNat sevm devm' (.ok post)),
              Exec.Deriv.lt
                  ⟨ρ.toNat, sevm, devm', .ok post, exc'⟩
                  ⟨pc, sevm, devm, .ok post, exc⟩ ∧
              SFunc.Run c.prog sevm devm (.next n f) (.returned devm') ∧
              devm'.stack = S' ++ base ∧ S'.length = m) := by
        have hrest := hcheck.2
        cases ha : absNinst n a with
        | none => simp [ha] at hrest
        | some a' =>
          have hchild : checkNode code c.entries m (pc + n.size) a' f = true := by
            simpa [ha] using hrest
          rcases absNinst_nonpush_spec hnpush ha with
            ⟨hlen, out, htrans, hread⟩
          exact next_nonpush n a' out hlen htrans hread hchild h_at
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
            .ok post, exc'⟩ (Exec.Deriv.lt_of_prec prec) post rfl hcode hfork m
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
      | reg r =>
        simp only [checkNode, Bool.and_eq_true] at hcheck
        have hbyte : bytesAt code pc (Ninst.toBytes (Ninst.reg r)) = true :=
          hcheck.1.1
        have h_at : Ninst.At sevm.code pc (Ninst.reg r) := by
          apply Ninst.at_of_slice
          apply bytesAt_slice (ninst_bytes_ne_nil (Ninst.reg r))
          rw [hcode]
          exact hbyte
        exact next_checked (Ninst.reg r)
          (by intro bs fits h; cases h) hcheck h_at
      | exec x =>
        simp only [checkNode, Bool.and_eq_true] at hcheck
        have h_at : Ninst.At sevm.code pc (Ninst.exec x) := by
          apply Ninst.at_of_slice
          apply bytesAt_slice (ninst_bytes_ne_nil (Ninst.exec x))
          rw [hcode]
          exact hcheck.1.1
        exact next_checked (Ninst.exec x)
          (by intro bs fits h; cases h) hcheck h_at
      | dupn i =>
        simp only [checkNode, Bool.and_eq_true] at hcheck
        have h_at : Ninst.At sevm.code pc (Ninst.dupn i) := by
          apply Ninst.at_of_slice
          apply bytesAt_slice (ninst_bytes_ne_nil (Ninst.dupn i))
          rw [hcode]
          exact hcheck.1.1
        exact next_checked (Ninst.dupn i)
          (by intro bs fits h; cases h) hcheck h_at
      | swapn i =>
        simp only [checkNode, Bool.and_eq_true] at hcheck
        have h_at : Ninst.At sevm.code pc (Ninst.swapn i) := by
          apply Ninst.at_of_slice
          apply bytesAt_slice (ninst_bytes_ne_nil (Ninst.swapn i))
          rw [hcode]
          exact hcheck.1.1
        exact next_checked (Ninst.swapn i)
          (by intro bs fits h; cases h) hcheck h_at
      | exchange i =>
        simp only [checkNode, Bool.and_eq_true] at hcheck
        have h_at : Ninst.At sevm.code pc (Ninst.exchange i) := by
          apply Ninst.at_of_slice
          apply bytesAt_slice (ninst_bytes_ne_nil (Ninst.exchange i))
          rw [hcode]
          exact hcheck.1.1
        exact next_checked (Ninst.exchange i)
          (by intro bs fits h; cases h) hcheck h_at
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
        (Exec.Deriv.lt_of_prec prec) post rfl hcode hfork m a f ρ S base
        hcheck'.2 hstack' hframe
      cases hrun with
      | inl run => exact Or.inl (SFunc.Run.dest burn run)
      | inr run =>
        rcases run with ⟨hret, devm', S', exc'', hlt, run, hst, hlen⟩
        exact Or.inr ⟨hret, devm', S', exc'', deriv_lt_trans hlt
          (Exec.Deriv.lt_of_prec prec), SFunc.Run.dest burn run, hst, hlen⟩
    | jump k =>
      cases a with
      | nil => simp [checkNode] at hcheck
      | cons av a' =>
        cases av with
        | ret => simp [checkNode] at hcheck
        | unk => simp [checkNode] at hcheck
        | const t =>
          cases hk : c.entries[k]? with
          | none => simp [checkNode, hk] at hcheck
          | some e =>
            have hcheck' :
                (((byteAt code pc = some (Jinst.toUInt8 .jump) ∧
                  e.pc = t.toNat) ∧ e.rets = m) ∧
                  gotoCompat a' e.frame = true) := by
              simpa [checkNode, hk] using hcheck
            rcases cert_prog_of_entry c k e hk with ⟨g, hg⟩
            have hentry := cert_check_at hc k e g hk hg
            have h_at : Jinst.At sevm.code pc .jump := by
              apply byteAt_jinst_at
              rw [hcode]
              exact hcheck'.1.1.1
            cases S with
            | nil => cases hframe
            | cons s0 S1 =>
              cases hframe with
              | cons h0 htail =>
                have hs0 : s0 = t := h0
                rcases jump_at_exact exc h_at with
                  ⟨x, inter, exc', pop, _, _, prec⟩
                have hpop := popBurn_one_stack pop
                rw [hstack] at hpop
                have hx : x = t := by
                  have htx : s0 = x := by
                    simpa using congrArg List.head? hpop
                  exact htx.symm.trans hs0
                have hinter : inter.stack = S1 ++ base := by
                  have hpop' : s0 :: (S1 ++ base) = x :: inter.stack := by
                    simpa using hpop
                  exact (List.cons.inj hpop').2.symm
                have hframe' : FrameMatches ρ e.frame S1 :=
                  frameMatches_gotoCompat hcheck'.2 htail
                have hentry' :
                    checkNode code c.entries e.rets t.toNat e.frame g = true := by
                  simpa [hcheck'.1.1.2] using hentry
                subst x
                have hrun := ih
                  ⟨t.toNat, sevm, inter, .ok post, exc'⟩
                  (Exec.Deriv.lt_of_prec prec) post rfl hcode hfork e.rets
                  e.frame g ρ S1 base hentry' hinter hframe'
                cases hrun with
                | inl run => exact Or.inl (SFunc.Run.jump t hg pop run)
                | inr run =>
                  rcases run with
                    ⟨hret, devm', S', exc'', hlt, run, hst, hlen⟩
                  have hret' : AVal.ret ∈ a' :=
                    ret_mem_of_gotoCompat hcheck'.2 hret
                  have hlen' : S'.length = m := by
                    simpa [hcheck'.1.2] using hlen
                  exact Or.inr ⟨List.mem_cons_of_mem _ hret', devm', S', exc'',
                    deriv_lt_trans hlt (Exec.Deriv.lt_of_prec prec),
                    SFunc.Run.jump t hg pop run, hst, hlen'⟩
    | callNext k f =>
      cases a with
      | nil => simp [checkNode] at hcheck
      | cons av a' =>
        cases av with
        | ret => simp [checkNode] at hcheck
        | unk => simp [checkNode] at hcheck
        | const t =>
          cases f with
          | dest d =>
            cases hk : c.entries[k]? with
            | none => simp [checkNode, hk] at hcheck
            | some e =>
              simp [checkNode, hk] at hcheck
              rcases cert_prog_of_entry c k e hk with ⟨g, hg⟩
              have hentry := cert_check_at hc k e g hk hg
              have h_at : Jinst.At sevm.code pc .jump := by
                apply byteAt_jinst_at
                rw [hcode]
                exact hcheck.1.1.1
              cases S with
              | nil => cases hframe
              | cons s0 S1 =>
                cases hframe with
                | cons h0 htail =>
                  have hs0 : s0 = t := h0
                  rcases jump_at_exact exc h_at with
                    ⟨x, inter, exc', pop, _, _, prec⟩
                  have hpop := popBurn_one_stack pop
                  rw [hstack] at hpop
                  have hx : x = t := by
                    have htx : s0 = x := by
                      simpa using congrArg List.head? hpop
                    exact htx.symm.trans hs0
                  have hinter : inter.stack = S1 ++ base := by
                    have hpop' : s0 :: (S1 ++ base) = x :: inter.stack := by
                      simpa using hpop
                    exact (List.cons.inj hpop').2.symm
                  have hentry' :
                      checkNode code c.entries e.rets t.toNat e.frame g = true := by
                    simpa [hcheck.1.1.2] using hentry
                  subst x
                  cases hidx : e.frame.findIdx? (· == .ret) with
                  | none =>
                    have hcall : callCompat 0 a' e.frame = true := by
                      simpa [hidx] using hcheck.2
                    have hret_no : ∀ x, x ∈ e.frame → x ≠ AVal.ret :=
                      ret_not_mem_of_findIdx_none hidx
                    rcases frameMatches_callCompat hcall htail with
                      ⟨Sf, Sr, hsplit, hframee, hframer⟩
                    have hstacke : inter.stack = Sf ++ (Sr ++ base) := by
                      rw [hinter, hsplit]
                      simp [List.append_assoc]
                    have hrun := ih
                      ⟨t.toNat, sevm, inter, .ok post, exc'⟩
                      (Exec.Deriv.lt_of_prec prec) post rfl hcode hfork e.rets
                      e.frame g 0 Sf (Sr ++ base) hentry' hstacke hframee
                    cases hrun with
                    | inl run =>
                      exact Or.inl (SFunc.Run.callHalt t hg pop run)
                    | inr run =>
                      rcases run with ⟨hret, devm', S', exc'', hlt, run, hst, hlen⟩
                      exact (hret_no AVal.ret hret rfl).elim
                  | some i =>
                    cases haidx : a'[i]? with
                    | none =>
                      have hbad := hcheck.2
                      simp [hidx, haidx] at hbad
                    | some av =>
                      cases av with
                      | ret =>
                        have hbad := hcheck.2
                        simp [hidx, haidx] at hbad
                      | unk =>
                        have hbad := hcheck.2
                        simp [hidx, haidx] at hbad
                      | const r =>
                        have hcall : callCompat r a' e.frame = true ∧
                            byteAt code r.toNat = some (Jinst.toUInt8 .jumpdest) ∧
                            checkNode code c.entries m (r.toNat + 1)
                              (List.replicate e.rets .unk ++
                                a'.drop e.frame.length) d = true := by
                          simpa [hidx, haidx, Bool.and_eq_true] using hcheck.2
                        rcases frameMatches_callCompat hcall.1 htail with
                          ⟨Sf, Sr, hsplit, hframee, hframer⟩
                        have hstacke : inter.stack = Sf ++ (Sr ++ base) := by
                          rw [hinter, hsplit]
                          simp [List.append_assoc]
                        have hframee' : FrameMatches r e.frame Sf := hframee
                        have hrun := ih
                          ⟨t.toNat, sevm, inter, .ok post, exc'⟩
                          (Exec.Deriv.lt_of_prec prec) post rfl hcode hfork e.rets
                          e.frame g r Sf (Sr ++ base) hentry' hstacke hframee'
                        cases hrun with
                        | inl run =>
                          exact Or.inl (SFunc.Run.callHalt t hg pop run)
                        | inr run =>
                          rcases run with
                            ⟨hret, devm', Sret, exc'', hlt, run, hst, hlen⟩
                          have hunk : FrameMatches ρ
                              (List.replicate e.rets .unk) Sret := by
                            rw [← hlen]
                            exact frameMatches_unk_length Sret
                          have hcont : FrameMatches ρ
                              (List.replicate e.rets .unk ++
                                a'.drop e.frame.length) (Sret ++ Sr) := by
                            apply matches_to_frame
                            rw [List.map_append]
                            apply matches_append
                            · exact frameMatches_matches hunk
                            · exact frameMatches_matches hframer
                          have hst' : devm'.stack = (Sret ++ Sr) ++ base := by
                            simpa [List.append_assoc] using hst
                          have hlt_call : Exec.Deriv.lt
                              ⟨r.toNat, sevm, devm', .ok post, exc''⟩
                              ⟨pc, sevm, devm, .ok post, exc⟩ := by
                            exact deriv_lt_trans hlt (Exec.Deriv.lt_of_prec prec)
                          have h_atd : Jinst.At sevm.code r.toNat .jumpdest := by
                            apply byteAt_jinst_at
                            rw [hcode]
                            exact hcall.2.1
                          rcases jumpdest_at_exact exc'' h_atd with
                            ⟨inter2, exc2, burn2, _, prec2⟩
                          have hstackd : inter2.stack = (Sret ++ Sr) ++ base := by
                            rw [← burn2.stack, hst']
                          have hlt_dest : Exec.Deriv.lt
                              ⟨r.toNat + 1, sevm, inter2, .ok post, exc2⟩
                              ⟨r.toNat, sevm, devm', .ok post, exc''⟩ :=
                            Exec.Deriv.lt_of_prec prec2
                          have hrun' := ih
                            ⟨r.toNat + 1, sevm, inter2, .ok post, exc2⟩
                            (deriv_lt_trans hlt_dest hlt_call) post rfl hcode hfork m
                            (List.replicate e.rets .unk ++ a'.drop e.frame.length)
                            d ρ (Sret ++ Sr) base hcall.2.2 hstackd hcont
                          cases hrun' with
                          | inl run' =>
                            exact Or.inl (SFunc.Run.callRet t hg pop run
                              (SFunc.Run.dest burn2 run'))
                          | inr run' =>
                            rcases run' with
                              ⟨hret', devm'', S'', exc''', hlt_cont, run', hst'', hlen'⟩
                            have hret_a' : AVal.ret ∈ a' := by
                              rcases List.mem_append.mp hret' with h | h
                              · simp at h
                              · exact List.mem_of_mem_drop h
                            exact Or.inr ⟨List.mem_cons_of_mem _ hret_a', devm'', S'',
                              exc''', deriv_lt_trans hlt_cont
                                (deriv_lt_trans hlt_dest hlt_call),
                              SFunc.Run.callRet t hg pop run
                                (SFunc.Run.dest burn2 run'), hst'', hlen'⟩
          | branch f g => simp [checkNode] at hcheck
          | branchTo f k' => simp [checkNode] at hcheck
          | last l => simp [checkNode] at hcheck
          | next n f => simp [checkNode] at hcheck
          | jump k' => simp [checkNode] at hcheck
          | callNext k' f => simp [checkNode] at hcheck
          | ret => simp [checkNode] at hcheck
          | undefined => simp [checkNode] at hcheck
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
pc `0` is a run of the certified program.  (The top-level frame is empty, so the
initial operand stack is the untouched base of the recursion invariant.) -/
theorem lift_sound {code : ByteArray} {c : Cert} (hc : Cert.check code c = true)
    {sevm : Sevm} {pre post : Devm} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork) (exc : Exec 0 sevm pre (.ok post)) :
    SProg.Run c.prog sevm pre post := by
  cases c with
  | nil => simp [Cert.check] at hc
  | cons p c =>
    rcases p with ⟨e, f⟩
    have hc0 : Cert.check code ((e, f) :: c) = true := hc
    simp [Cert.check] at hc
    have hepc : e.pc = 0 := by simpa using hc.1.1
    have hef : e.frame = [] := by simpa using hc.1.2
    have hf : checkNode code (Cert.entries ((e, f) :: c)) e.rets e.pc e.frame f = true := by
      simpa using hc.2.1
    have hf0 : checkNode code (Cert.entries ((e, f) :: c)) e.rets 0 [] f = true := by
      simpa [hepc, hef] using hf
    have hrun := node_sound hc0 ⟨0, sevm, pre, .ok post, exc⟩
      post rfl hcode hfork e.rets [] f 0 [] pre.stack hf0 (by simp)
      (by simp [FrameMatches])
    refine ⟨f, ?_, ?_⟩
    · simp [Cert.prog]
    · cases hrun with
      | inl run => exact run
      | inr run => simp at run

end Blanc.Lift
