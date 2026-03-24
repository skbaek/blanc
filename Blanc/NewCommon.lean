-- Common.lean : definitions and lemmas generally useful for writing and
-- verifying Blanc programs, including a correctness proof for the Blanc
-- compiler and tactics for automating Blanc program verification.

import Mathlib.Tactic.Have
import Blanc.NewSemantics


def compsize : Func → Nat
  | .last _ => 1
  | .next i p => compsize p + i.toB8L.length
  | .branch p q => compsize p + compsize q + 5
  | .call _ => 4

def table : Nat → List Func → List (Nat × Func)
| _, [] => []
| k, f :: fs => ⟨k, f⟩ :: table (k + compsize f + 1) fs

def Func.compile (l : List (Nat × Func)) (n : Nat) : Func → Option B8L
  | .last o => pure [o.toB8]
  | .next i p => do
    let p_bts ← Func.compile l (n + i.toB8L.length) p
    pure <| Ninst.toB8L i ++ p_bts
  | .branch p q => do
    let pbs ← Func.compile l (n + 4) p
    let loc := n + pbs.length + 4
    guard (loc < 2 ^ 16)
    let qbs ← Func.compile l (loc + 1) q
    pure $
      ([0x61] : B8L) ++
      -- B16.toB8L (Nat.toUInt16 loc) ++
      [(loc >>> 8).toUInt8, loc.toUInt8] ++
      [Jinst.toB8 .jumpi] ++ pbs ++
      [Jinst.toB8 .jumpdest] ++ qbs
  | .call k => do
    let (loc, _) ← l[k]?
    guard (loc < 2 ^ 16)
    pure $
      ([0x61] : B8L) ++
      -- B16.toB8L (Nat.toUInt16 loc) ++
      [(loc >>> 8).toUInt8, loc.toUInt8] ++
      [Jinst.toB8 Jinst.jump]

def Table.compile (l : List (Nat × Func)) : List (Nat × Func) → Option B8L
| [] => pure []
| (n, p) :: nps => do
  let bs ← Func.compile l (n + 1) p
  let bss ← Table.compile l nps
  pure <| [Jinst.toB8 .jumpdest] ++ bs ++ bss

lemma Table.compile_cons_eq_some {l n p l' bs}
    (h : Table.compile l ((n, p) :: l') = some bs) :
    ∃ cp cl',
      Func.compile l (n + 1) p = some cp ∧
      Table.compile l l' = some cl' ∧
      bs = [Jinst.toB8 .jumpdest] ++ cp ++ cl' := by
  rcases of_bind_eq_some h with ⟨cp, h_cp, h'⟩; clear h
  rcases of_bind_eq_some h' with ⟨cl', h_cl', h_eq⟩; clear h'
  simp at h_eq; refine' ⟨cp, cl', h_cp, h_cl', h_eq.symm⟩

def Prog.compile (p : Prog) : Option B8L :=
  let t : List (Nat × Func) := table 0 (p.main :: p.aux)
  Table.compile t t

def subcode (cd : B8L) (k : Nat) : Option B8L → Prop
  | none => False
  | some bs => List.Slice cd k bs

/-----------------------------------------------------

structure Pack : Type where
  (evm : Evm)
  (evm' : Evm)
  (ex : Exec evm (.ok evm'))

abbrev Pack.Pred : Type := Pack → Prop

def Pack.imp (π π' : Pack.Pred) : Pack.Pred := λ pk => π pk → π' pk

infix:70 " →p " => Pack.imp

def Pack.Fa (π : Pack.Pred) : Prop := ∀ pk, π pk

notation "□p" => Pack.Fa

inductive Pack.Rel : Pack → Pack → Prop
  | none {evm : Evm} {n : Ninst} {evm' evm'' : Evm}
    (n_at : n.At evm.code evm.pc)
    (run : Ninst.Run' evm n .none (.ok evm'))
    (ex : Exec evm' (.ok evm'')) :
    Pack.Rel ⟨evm', evm'', ex⟩ ⟨evm, evm'', .nextNoneRec n_at run ex ⟩
  | fst {evm : Evm} {n : Ninst} {revm revm' : Evm} {evm' evm'' : Evm}
    (n_at : n.At evm.code evm.pc)
    (run : Ninst.Run' evm n (.some (revm, .ok revm')) (.ok evm'))
    (rex : Exec revm (.ok revm')) (ex : Exec evm' (.ok evm'')) :
    Pack.Rel ⟨revm, revm', rex⟩ ⟨evm, evm'', .nextSomeRec n_at run rex ex⟩
  | snd {evm : Evm} {n : Ninst} {revm : Evm}
    {rexn : Execution} {evm' evm'' : Evm}
    (n_at : n.At evm.code evm.pc)
    (run : Ninst.Run' evm n (.some (revm, rexn)) (.ok evm'))
    (rex : Exec revm rexn) (ex : Exec evm' (.ok evm'')) :
    Pack.Rel ⟨evm', evm'', ex⟩ ⟨evm, evm'', .nextSomeRec n_at run rex ex⟩
  | jump {evm : Evm} {j : Jinst} {evm' evm'' : Evm}
    (j_at : j.At evm.code evm.pc)
    (run : Jinst.Run' evm j (.ok evm'))
    (ex : Exec evm' (.ok evm'')) :
    Pack.Rel ⟨evm', evm'', ex⟩ ⟨evm, evm'', .jumpRec j_at run ex⟩

inductive Pack.le : Pack → Pack → Prop
  | refl : ∀ p, Pack.le p p
  | step : ∀ p p' p'', Pack.le p p' → Pack.Rel p' p'' → Pack.le p p''

inductive Pack.lt : Pack → Pack → Prop
  | intro {pk pk' pk'' : Pack} :
    Pack.le pk pk' → Pack.Rel pk' pk'' → Pack.lt pk pk''

lemma Pack.lt_of_prec {pk pk' : Pack} (rel : Rel pk pk') : lt pk pk' :=
  .intro (le.refl pk) rel

def Pack.gt (pk pk' : Pack) : Prop := Pack.lt pk' pk

lemma Pack.eq_or_lt_of_le :
  ∀ {p p'}, Pack.le p p' → p = p' ∨ Pack.lt p p' := by
  intros p p'' h0
  rcases h0 with ⟨_, _, p'⟩ | ⟨p', _, h1, h2⟩
  · left; rfl
  · right; refine (.intro h1 h2)

lemma Pack.acc_of_le {pk pk' : Pack}
    (h_le : Pack.le pk pk') (h_acc : Acc Pack.lt pk') : Acc Pack.lt pk := by
  cases Pack.eq_or_lt_of_le h_le with
  | inl h => rw [h]; exact h_acc
  | inr h => exact Acc.inv h_acc h

theorem Pack.lt.well_founded : WellFounded Pack.lt := by

  have foo :=
    @Exec.rec
      ( λ evm exn ex =>
        ∀ (evm' : Evm) (eq : exn = (.ok evm')),
          let ex' : Exec evm (.ok evm') := by
            rw [← eq]; exact ex
          Acc Pack.lt ⟨evm, evm', ex'⟩ )
      (by intro _ _ _ eq; cases eq)
      ( by intro _ _ exn _ _ err _ eq;
           rw [eq] at err
           simp [Except.IsError] at err )
      ( by intro _ _ _ _ _ _ _ _ err _ _ eq
           rw [eq] at err
           simp [Except.IsError] at err )
      ( by intro evm n evm' exn n_at run ex ih
           intro _evm eq _ex
           cases _ex; clear _ex









      )





      sorry
      sorry
      sorry
      sorry



  constructor; intro pk; rcases pk with ⟨evm_0, evm_1, ex_0⟩
  apply @foo evm_0 (.ok evm_1) ex_0 evm_1 rfl

















  --apply @Exec.rec (λ s r cr => Acc Pack.lt ⟨s, r, cr⟩)



#exit
theorem Pack.lt.well_founded : WellFounded Pack.lt := by
  constructor; intro pk; rcases pk with ⟨_, _, cr⟩
  apply @Exec.rec (λ s r cr => Acc Pack.lt ⟨s, r, cr⟩)
  · intro evm get; constructor;
    intro _ h; rcases h with ⟨_, _, _, ⟨_⟩⟩
  · intro _ _ _ _ _ _; constructor;
    intro _ h; rcases h with ⟨_, _, _, ⟨_⟩⟩
  · intro evm n evm' exn' exn get run ex' err acc;
    constructor; intro _ lt
    rcases lt with ⟨le, ⟨_⟩⟩
    apply Pack.acc_of_le le acc
  · intro _ _ _ _ _ _ _ _; constructor;
    intro _ h; rcases h with ⟨_, _, _, ⟨_⟩⟩
  · intro evm n evm' exn' evm'' exn get run ex' ex acc acc'
    constructor; intro _ lt; rcases lt with ⟨le, ⟨_⟩⟩
    · apply Pack.acc_of_le le acc
    · apply Pack.acc_of_le le acc'
  · intro _ _ _ _ _ _; constructor
    intro _ h; rcases h with ⟨_, _, _, ⟨_⟩⟩
  · intro _ _ _ _ _ _ _ _; constructor
    intro _ h; rcases h with ⟨_, _, _, ⟨_⟩⟩
  · intro _ _ _ _ _; constructor
    intro _ h; rcases h with ⟨_, _, _, ⟨_⟩⟩

def carryover (π : Pack.Pred) : Pack.Pred :=
(λ pk => □p (Pack.gt pk →p π)) →p π

def Exec'.strongRec (π : Exec'.Pred) : □p (carryover π) → □p π := by
  intro ih pk
  apply @WellFounded.induction _ Exec'.lt Exec'.lt.well_founded π pk
  clear pk; intro pk ih'
  apply ih
  intro pk' h_gt
  apply ih' _ h_gt
infix:70 " →p " => Exec'.imp

-------------------------------------------------------------------------/

structure Pack : Type where
  (evm : Evm)
  (exn : Execution)
  (ex : Exec evm exn)

abbrev Pack.Pred : Type := Pack → Prop

def Pack.imp (π π' : Pack.Pred) : Pack.Pred := λ pk => π pk → π' pk

infix:70 " →p " => Pack.imp

def Pack.Fa (π : Pack.Pred) : Prop := ∀ pk, π pk

notation "□p" => Pack.Fa

inductive Pack.Rel : Pack → Pack → Prop
  | none {evm : Evm} {n : Ninst} {evm' : Evm} {exn : Execution}
    (n_at : n.At evm.code evm.pc)
    (run : Ninst.Run' evm n .none (.ok evm'))
    (ex : Exec evm' exn) :
    Pack.Rel ⟨evm', exn, ex⟩ ⟨evm, exn, .nextNoneRec n_at run ex⟩
  | fst {evm : Evm} {n : Ninst} {revm : Evm}
    {rexn : Execution} {evm' evm'' : Evm}
    (n_at : n.At evm.code evm.pc)
    (run : Ninst.Run' evm n (.some (revm, rexn)) (.ok evm'))
    (rex : Exec revm rexn) (ex : Exec evm' (.ok evm'')) :
    Pack.Rel ⟨revm, rexn, rex⟩ ⟨evm, .ok evm'', .nextSomeRec n_at run rex ex⟩
  | snd {evm : Evm} {n : Ninst} {revm : Evm}
    {rexn : Execution} {evm' evm'' : Evm}
    (n_at : n.At evm.code evm.pc)
    (run : Ninst.Run' evm n (.some (revm, rexn)) (.ok evm'))
    (rex : Exec revm rexn) (ex : Exec evm' (.ok evm'')) :
    Pack.Rel ⟨evm', .ok evm'', ex⟩ ⟨evm, .ok evm'', .nextSomeRec n_at run rex ex⟩
  | jump {evm : Evm} {j : Jinst} {evm' evm'' : Evm}
    (j_at : j.At evm.code evm.pc)
    (run : Jinst.Run' evm j (.ok evm'))
    (ex : Exec evm' (.ok evm'')) :
    Pack.Rel ⟨evm', .ok evm'', ex⟩ ⟨evm, .ok evm'', .jumpRec j_at run ex⟩

inductive Pack.le : Pack → Pack → Prop
  | refl : ∀ p, Pack.le p p
  | step : ∀ {p p' p''}, Pack.le p p' → Pack.Rel p' p'' → Pack.le p p''

inductive Pack.lt : Pack → Pack → Prop
  | intro {pk pk' pk'' : Pack} :
    Pack.le pk pk' → Pack.Rel pk' pk'' → Pack.lt pk pk''

lemma Pack.lt_of_prec {pk pk' : Pack} (rel : Rel pk pk') : lt pk pk' :=
  .intro (le.refl pk) rel

def Pack.gt (pk pk' : Pack) : Prop := Pack.lt pk' pk

lemma Pack.eq_or_lt_of_le :
  ∀ {p p'}, Pack.le p p' → p = p' ∨ Pack.lt p p' := by
  intros p p'' h0
  rcases h0 with ⟨_, _, _⟩ | ⟨h1, h2⟩
  · left; rfl
  · right; refine (.intro h1 h2)

lemma Pack.acc_of_le {pk pk' : Pack}
    (h_le : Pack.le pk pk') (h_acc : Acc Pack.lt pk') : Acc Pack.lt pk := by
  cases Pack.eq_or_lt_of_le h_le with
  | inl h => rw [h]; exact h_acc
  | inr h => exact Acc.inv h_acc h

theorem Pack.lt.well_founded : WellFounded Pack.lt := by
  constructor; intro pk; rcases pk with ⟨_, _, cr⟩
  apply @Exec.rec (λ s r cr => Acc Pack.lt ⟨s, r, cr⟩)
  · intro evm get; constructor;
    intro _ h; rcases h with ⟨_, ⟨_⟩⟩
  · intro _ _ _ _ _ _; constructor;
    intro _ h; rcases h with ⟨_, ⟨_⟩⟩
  · intro evm n evm' exn' exn get run ex' err acc;
    constructor; intro _ lt
    rcases lt with ⟨le, ⟨_⟩⟩
  · intro _ _ _ _ _ _ _ acc; constructor;
    intro _ h; rcases h with ⟨le, ⟨_⟩⟩;
    apply Pack.acc_of_le le acc
  · intro evm n evm' exn' evm'' exn get run ex' ex acc acc'
    constructor; intro _ lt; rcases lt with ⟨le, ⟨_⟩⟩
    · apply Pack.acc_of_le le acc
    · apply Pack.acc_of_le le acc'
  · intro _ _ _ _ _ _; constructor
    intro _ h; rcases h with ⟨_, ⟨_⟩⟩
  · intro _ _ _ _ _ _ _ acc; constructor
    intro _ h; rcases h with ⟨le, ⟨_⟩⟩
    apply Pack.acc_of_le le acc
  · intro _ _ _ _ _; constructor
    intro _ h; rcases h with ⟨_, ⟨_⟩⟩

def carryover (π : Pack.Pred) : Pack.Pred :=
  (λ pk => □p (Pack.gt pk →p π)) →p π

def Pack.strongRec (π : Pack.Pred) : □p (carryover π) → □p π := by
  intro ih pk
  apply @WellFounded.induction _ Pack.lt Pack.lt.well_founded π pk
  clear pk; intro pk ih'
  apply ih
  intro pk' h_gt
  apply ih' _ h_gt



/-
structure Exec' : Type where
  (evm : Evm)
  (exn : Execution)
  (ex : Exec evm exn)

abbrev Exec'.Pred : Type := Exec' → Prop

def Exec'.imp (π π' : Exec'.Pred) : Exec'.Pred := λ pk => π pk → π' pk

def Exec'.Fa (π : Exec'.Pred) : Prop := ∀ pk, π pk

notation "□p" => Exec'.Fa

inductive Exec'.Rel : Exec' → Exec' → Prop
  | err {evm : Evm} {n : Ninst}
    {evm' : Evm} {exn' : Execution } {exn : Execution}
    (get : n.At evm.code evm.pc)
    (run : Ninst.Run' evm n (.some (evm', exn')) exn)
    (ex : Exec evm' exn') (err : exn.IsError) :
    Exec'.Rel ⟨evm', exn', ex⟩ ⟨evm, exn, .nextSomeErr get run ex err⟩
  | fst {evm : Evm} {n : Ninst} {evm' : Evm}
    {exn' : Execution} {evm'' : Evm} {exn : Execution}
    (get : n.At evm.code evm.pc)
    (run : Ninst.Run' evm n (.some (evm', exn')) (.ok evm''))
    (ex : Exec evm' exn') (ex' : Exec evm'' exn) :
    Exec'.Rel ⟨evm', exn', ex⟩ ⟨evm, exn, .nextSomeRec get run ex ex'⟩
  | snd {evm : Evm} {n : Ninst} {evm' : Evm}
    {exn' : Execution} {evm'' : Evm} {exn : Execution}
    (get : n.At evm.code evm.pc)
    (run : Ninst.Run' evm n (.some (evm', exn')) (.ok evm''))
    (ex : Exec evm' exn') (ex' : Exec evm'' exn) :
    Exec'.Rel ⟨evm'', exn, ex'⟩ ⟨evm, exn, .nextSomeRec get run ex ex'⟩

inductive Exec'.le : Exec' → Exec' → Prop
  | refl : ∀ p, Exec'.le p p
  | step : ∀ p p' p'', Exec'.le p p' → Exec'.Rel p' p'' → Exec'.le p p''

inductive Exec'.lt : Exec' → Exec' → Prop
  | intro {pk pk' pk'' : Exec'} :
    Exec'.le pk pk' → Exec'.Rel pk' pk'' → Exec'.lt pk pk''

lemma Exec'.lt_of_prec {pk pk' : Exec'} (rel : Rel pk pk') : lt pk pk' :=
  .intro (le.refl pk) rel

def Exec'.gt (pk pk' : Exec') : Prop := Exec'.lt pk' pk

lemma Exec'.eq_or_lt_of_le :
  ∀ {p p'}, Exec'.le p p' → p = p' ∨ Exec'.lt p p' := by
  intros p p'' h0
  rcases h0 with ⟨_, _, p'⟩ | ⟨p', _, h1, h2⟩
  · left; rfl
  · right; refine (.intro h1 h2)

lemma Exec'.acc_of_le {pk pk' : Exec'}
    (h_le : Exec'.le pk pk') (h_acc : Acc Exec'.lt pk') : Acc Exec'.lt pk := by
  cases Exec'.eq_or_lt_of_le h_le with
  | inl h => rw [h]; exact h_acc
  | inr h => exact Acc.inv h_acc h

theorem Exec'.lt.well_founded : WellFounded Exec'.lt := by
  constructor; intro pk; rcases pk with ⟨_, _, cr⟩
  apply @Exec.rec (λ s r cr => Acc Exec'.lt ⟨s, r, cr⟩)
  · intro evm get; constructor;
    intro _ h; rcases h with ⟨_, _, _, ⟨_⟩⟩
  · intro _ _ _ _ _ _; constructor;
    intro _ h; rcases h with ⟨_, _, _, ⟨_⟩⟩
  · intro evm n evm' exn' exn get run ex' err acc;
    constructor; intro _ lt
    rcases lt with ⟨le, ⟨_⟩⟩
    apply Exec'.acc_of_le le acc
  · intro _ _ _ _ _ _ _ _; constructor;
    intro _ h; rcases h with ⟨_, _, _, ⟨_⟩⟩
  · intro evm n evm' exn' evm'' exn get run ex' ex acc acc'
    constructor; intro _ lt; rcases lt with ⟨le, ⟨_⟩⟩
    · apply Exec'.acc_of_le le acc
    · apply Exec'.acc_of_le le acc'
  · intro _ _ _ _ _ _; constructor
    intro _ h; rcases h with ⟨_, _, _, ⟨_⟩⟩
  · intro _ _ _ _ _ _ _ _; constructor
    intro _ h; rcases h with ⟨_, _, _, ⟨_⟩⟩
  · intro _ _ _ _ _; constructor
    intro _ h; rcases h with ⟨_, _, _, ⟨_⟩⟩

def carryover (π : Exec'.Pred) : Exec'.Pred :=
(λ pk => □p (Exec'.gt pk →p π)) →p π

def Exec'.strongRec (π : Exec'.Pred) : □p (carryover π) → □p π := by
  intro ih pk
  apply @WellFounded.induction _ Exec'.lt Exec'.lt.well_founded π pk
  clear pk; intro pk ih'
  apply ih
  intro pk' h_gt
  apply ih' _ h_gt
-/

lemma Linst.run_of_at {evm l exn} (ex : Exec evm exn)
    (get : l.At evm.code evm.pc) : Linst.Run' evm l exn := by
  simp [Linst.At] at get
  cases ex
  <;> rename (evm.getInst = _) => get'
  <;> try {cases Eq.trans get.symm get'}
  cases Eq.trans get.symm get'; assumption

lemma ByteArray.toList_eq_toList_data {xs : ByteArray} :
    xs.toList = xs.data.toList := by
  have gen :
      ∀ xs ys : List UInt8,
        toList.loop ⟨⟨xs ++ ys⟩⟩ xs.length xs.reverse = xs ++ ys := by
    intro xs ys;
    induction ys generalizing xs with
      | nil =>
        unfold toList.loop
        rw [if_neg _, List.reverse_reverse, List.append_nil]
        simp [size]
      | cons y ys ih =>
        unfold toList.loop
        have rw : get! ⟨⟨xs ++ y :: ys⟩⟩ xs.length = y := by
          simp [get!]
        have rw' : xs.length + 1 = (xs ++ [y]).length := by simp
        have rw'' : y :: xs.reverse = (xs ++ [y]).reverse := by simp
        rw [if_pos _, rw, List.append_cons, rw', rw'', ih]
        simp [size]
  rcases xs with ⟨⟨xs⟩⟩; apply gen [] xs

lemma ByteArray.of_getElem?_eq_some {xs : ByteArray} {n} {x} :
    xs.toList[n]? = .some x → xs.get! n = x := by
  rw [ByteArray.toList_eq_toList_data]
  simp only [ByteArray.get!, Array.getElem?_toList]
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  intro h; rw [h]; simp

lemma dup_toByte_toRinst? :
  ∀ n, B8.toRinst (Rinst.dup n).toB8 = some (.dup n)
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | 11 => rfl
  | 12 => rfl
  | 13 => rfl
  | 14 => rfl
  | 15 => rfl
  | ⟨n + 16, h⟩ => by
    rw [← Nat.not_le] at h
    cases h (Nat.le_add_left _ _)

lemma swap_toByte_toRinst?
  : ∀ n, B8.toRinst (Rinst.swap n).toB8 = some (.swap n)
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | 11 => rfl
  | 12 => rfl
  | 13 => rfl
  | 14 => rfl
  | 15 => rfl
  | ⟨n + 16, h⟩ => by
    rw [← Nat.not_le] at h
    cases h (Nat.le_add_left _ _)

lemma log_toByte_toRinst? :
  ∀ n, B8.toRinst (Rinst.log n).toB8 = some (.log n)
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | ⟨n + 5, h⟩ => by
    rw [← Nat.not_le] at h
    cases h (Nat.le_add_left _ _)

lemma toB8_toRinst {i : Rinst} : B8.toRinst i.toB8 = some i := by
  cases i <;> try {rfl}
  · apply dup_toByte_toRinst?
  · apply swap_toByte_toRinst?
  · apply log_toByte_toRinst?

lemma Linst.toRinst_toB8_eq_none {l : Linst} : l.toB8.toRinst = .none := by cases l <;> rfl
lemma Linst.toXinst_toB8_eq_none {l : Linst} : l.toB8.toXinst = .none := by cases l <;> rfl
lemma Linst.toJinst_toB8_eq_none {l : Linst} : l.toB8.toJinst = .none := by cases l <;> rfl
lemma Linst.toLinst_toB8_eq_some {l : Linst} : l.toB8.toLinst = .some l := by cases l <;> rfl

lemma Jinst.toRinst_toB8_eq_none {j : Jinst} : j.toB8.toRinst = .none := by cases j <;> rfl
lemma Jinst.toXinst_toB8_eq_none {j : Jinst} : j.toB8.toXinst = .none := by cases j <;> rfl
lemma Jinst.toLinst_toB8_eq_none {j : Jinst} : j.toB8.toLinst = .none := by cases j <;> rfl
lemma Jinst.toJinst_toB8_eq_some {j : Jinst} : j.toB8.toJinst = .some j := by cases j <;> rfl

lemma none_mapRev {ξ υ} {f : ξ → υ} : (Option.none <&> f) = .none := by rfl

lemma none_orElse {ξ} {x : Option ξ} : (Option.none <|> x) = x := by rfl

lemma Linst.getInst_of_slice {evm : Evm} {l : Linst} {xs : B8L}
    (slice : evm.code.toList.Slice evm.pc (l.toB8 :: xs)) :
    l.At evm.code evm.pc := by
  have eq := List.get?_eq_of_slice slice
  simp only [Linst.At, ByteArray.getInst]
  have rw := ByteArray.of_getElem?_eq_some eq
  have lt : evm.pc < evm.code.size := by
    simp only [ByteArray.size, Array.size]
    rcases List.getElem?_eq_some_iff.mp eq with ⟨lt, _⟩
    rw [ByteArray.toList_eq_toList_data] at lt; exact lt
  rw [if_pos lt]
  conv => lhs; arg 1; lhs; rhs; rw [rw]; rfl
  rw [Linst.toRinst_toB8_eq_none, none_mapRev, none_orElse]
  conv => lhs; arg 1; lhs; rhs; rw [rw]; rfl
  rw [Linst.toXinst_toB8_eq_none, none_mapRev, none_orElse]
  conv => lhs; arg 1; lhs; rhs; rw [rw]; rfl
  rw [Linst.toJinst_toB8_eq_none, none_mapRev, none_orElse]
  conv => lhs; arg 1; lhs; rhs; rw [rw]; rfl
  rw [Linst.toLinst_toB8_eq_some]; rfl

lemma Jinst.at_of_slice {code : ByteArray} {pc} {j : Jinst}
    (slice : code.toList.Slice pc [j.toB8]) : Jinst.At code pc j := by
  have eq := List.get?_eq_of_slice slice
  simp only [Jinst.At, ByteArray.getInst]
  have rw := ByteArray.of_getElem?_eq_some eq
  have lt : pc < code.size := by
    simp only [ByteArray.size, Array.size]
    rcases List.getElem?_eq_some_iff.mp eq with ⟨lt, _⟩
    rw [ByteArray.toList_eq_toList_data] at lt; exact lt
  rw [if_pos lt]
  conv => lhs; arg 1; lhs; rhs; rw [rw]; rfl
  rw [Jinst.toRinst_toB8_eq_none, none_mapRev, none_orElse]
  conv => lhs; arg 1; lhs; rhs; rw [rw]; rfl
  rw [Jinst.toXinst_toB8_eq_none, none_mapRev, none_orElse]
  conv => lhs; arg 1; lhs; rhs; rw [rw]; rfl
  rw [Jinst.toJinst_toB8_eq_some]; rfl

lemma at_of_jumpable {code : ByteArray} {pc}
    (jump : jumpable code pc = true) : Jinst.At code pc .jumpdest := by
  unfold jumpable at jump
  split at jump; rename_i h_get
  · simp only [Jinst.At, ByteArray.getInst]
    have lt : pc < code.size := by
      by_contra h; simp only [not_lt] at h
      have h_get0 : code.get! pc = 0 := by
        simp only
          [ByteArray.get!, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
        rw [Array.getElem?_eq_none_iff.mpr h]; rfl
      rw [h_get0] at h_get; cases h_get
    rw [if_pos lt]
    have r_none : B8.toRinst (code.get! pc) = none := by
      rw [h_get]; apply Jinst.toRinst_toB8_eq_none
    have x_none : B8.toXinst (code.get! pc) = none := by
      rw [h_get]; apply Jinst.toXinst_toB8_eq_none
    have j_some : B8.toJinst (code.get! pc) = some .jumpdest := by
      rw [h_get]; apply Jinst.toJinst_toB8_eq_some
    simp only [r_none, x_none, j_some, none_mapRev, none_orElse]
    rfl
  · cases jump

def PushAt (code : ByteArray) (pc : Nat) (xs : B8L) : Prop :=
  ∃ le : xs.length ≤ 32, code.getInst pc = some (.next (.push xs le))

lemma pushAt_of_slice {code : ByteArray} {pc} {xs : B8L}
    (slice : code.toList.Slice pc (pushToB8L xs)) : PushAt code pc xs := sorry

lemma Ninst.getInst_of_slice {evm : Evm} {n : Ninst} :
    evm.code.toList.Slice evm.pc n.toB8L → n.At evm.code evm.pc := by sorry

lemma of_subcode {cd k} :
    ∀ {obs}, subcode cd k obs →
       ∃ bs, obs = some bs ∧ cd.Slice k bs
  | none, h => by cases h
  | some bs, h => ⟨bs, rfl, h⟩

def Ninst.Inv {ξ : Type} (r : Evm → ξ) (n : Ninst) : Prop :=
  ∀ {evm evm'}, Ninst.Run evm n evm' → r evm = r evm'

lemma Ninst.inv_code {n} : Ninst.Inv Evm.code n := by sorry

lemma Ninst.run_of_at {evm n exn}
    (ex : Exec evm exn) (h_at : n.At evm.code evm.pc) :
    ∃ (evm' : Evm) (ex' : Exec evm' exn)
      (rel : Pack.Rel ⟨evm', exn, ex'⟩ ⟨evm, exn, ex⟩),
      evm'.pc = evm.pc + n.toB8L.length ∧ Ninst.Run evm n evm' := sorry

-- lemma Ninst.run_of_at {e s pc i r}
--     (cr : Exec e s pc r) (h_at : Ninst.At e pc i) :
--     ∃ (s' : Desc) (cr' : Exec e s' (pc + i.toB8L.length) r),
--       Ninst.Run e s i s' ∧
--       Exec'.Rel ⟨e, s', pc + i.toB8L.length, r, cr'⟩ ⟨e, s, pc,r, cr⟩ := by

--lemma subcode_compile_branch {e k l p q}
--  (h : subcode e.code k (Func.compile l k (Func.branch p q))) :
--    ∃ loc : Nat,
--      loc < 2 ^ 16 ∧
--      PushAt e k [(loc >>> 8).toUInt8, loc.toUInt8] ∧
--      Jinst.jumpi.At e (k + 3) ∧
--      subcode e.code (k + 4) (Func.compile l (k + 4) p) ∧
--      Jinst.jumpdest.At e loc ∧
--      subcode e.code (loc + 1) (Func.compile l (loc + 1) q) := by


def Evm.getInst' (evm : Evm) (pc : Nat) : Option Inst :=
  ByteArray.getInst evm.code pc

-- #exit
--   if pc < evm.code.size
--   then
--     let b : B8 := evm.code.get! pc
--     (b.toRinst <&> (.next ∘ .reg)) <|>
--     (b.toXinst <&> (.next ∘ .exec)) <|>
--     (b.toJinst <&> .jump) <|>
--     (b.toLinst <&> .last) <|>
--     (
--       let bn := b.toNat
--       if h_bn : 95 ≤ bn ∧ bn ≤ 127 then
--         let bs : B8L := evm.code.sliceD (pc + 1) (bn - 95) 0
--         let h_bs : bs.length ≤ 32 := by
--           simp [bs, ByteArray.length_sliceD, h_bn.right]
--         some <| .next <| .push bs h_bs
--       else
--         none
--     )
--   else
--     some (.last .stop)

lemma Evm.getInst_eq_getInst' {evm : Evm} : evm.getInst = evm.getInst' evm.pc := rfl

-- def Jinst.At' (evm : Evm) (pc : Nat) (j : Jinst) : Prop :=
  -- evm.getInst' pc = some (.jump j)


lemma subcode_compile_branch {evm : Evm} {k l p q}
    (h : subcode evm.code.toList k (Func.compile l k (Func.branch p q))) :
    ∃ loc : Nat,
      loc < 2 ^ 16 ∧
      PushAt evm.code k [(loc >>> 8).toUInt8, loc.toUInt8] ∧
      Jinst.jumpi.At evm.code (k + 3) ∧
      subcode evm.code.toList (k + 4) (Func.compile l (k + 4) p) ∧
      Jinst.jumpdest.At evm.code loc ∧
      subcode evm.code.toList (loc + 1) (Func.compile l (loc + 1) q) := by
  sorry

lemma jumpi_at {evm exn} (ex : Exec evm exn) (h : Jinst.jumpi.At evm.code evm.pc) :
    ( ∃ (x : B256) (evm' : Evm) (ex' : Exec evm' exn),
        evm'.pc = evm.pc + 1 ∧
        Evm.Pop [x, 0] evm evm' ∧
        Pack.Rel ⟨evm', exn, ex'⟩ ⟨evm, exn, ex⟩ ) ∨
    ( ∃ (x y : B256) (evm' : Evm) (ex' : Exec evm' exn),
        evm'.pc = x.toNat ∧
        Evm.Pop [x, y] evm evm' ∧
        jumpable evm.code x.toNat ∧ y ≠ 0 ∧
        Pack.Rel ⟨evm', exn, ex'⟩ ⟨evm, exn, ex⟩ ) := by
  -- rcases Jinst.run_of_at cr h with ⟨s', pc', cr', h_run, h_prec⟩
  -- cases h_run
  -- · left; refine ⟨_, _, asm, asm, h_prec⟩
  -- · right; refine ⟨_, _, _, asm, asm, asm, asm, h_prec⟩
  sorry


lemma Stack.push_cons_pop_cons
    {x y} {xs ys} {s s' s''}
    (h : Stack.Push (x :: xs) s s')
    (h' : Stack.Pop (y :: ys) s' s'') :
    (x = y ∧ ∃ zs, Stack.Push xs s zs ∧ Stack.Pop ys zs s'') := by
  simp [Stack.Push, Split] at h
  simp [Stack.Pop, Split] at h'
  match s' with
  | [] => cases h
  | z :: zs =>
    rw [List.cons_eq_cons] at h
    rw [List.cons_eq_cons] at h'
    refine' ⟨Eq.trans h.left.symm h'.left, zs, h.right, h'.right⟩

lemma Evm.push_cons_pop_cons
    {x y} {xs ys} {s s' s''}
    (h : Evm.Push (x :: xs) s s')
    (g : Evm.Pop (y :: ys) s' s'') :
    (x = y ∧ ∃ st, Evm.Push xs s st ∧ Evm.Pop ys st s'') := by
  rcases Stack.push_cons_pop_cons h.stack g.stack
    with ⟨h_eq, stk, h_push, h_pop⟩

  refine' ⟨
    h_eq,
    {s' with stack := stk},
    {h with stack := h_push},
    {g with stack := h_pop}
  ⟩

def Evm.Equiv (evm evm' : Evm) : Prop :=
  Evm.Rel Evm.Rels.equiv evm evm'

infix:70 " ≅ "  => Evm.Equiv

lemma Evm.push_nil {evm evm'} (h : Evm.Push [] evm evm') : evm ≅ evm' := by
  have h_stk : evm.stack = evm'.stack := h.stack.symm
  exact {h with stack := h_stk}

lemma rel_of_rel_of_equiv {evm evm' evm''} {rs : Evm.Rels}
    (rel : Evm.Rel rs evm evm') (equiv : evm' ≅ evm'') :
    Evm.Rel rs evm evm'' := by
  constructor
  · rw [← equiv.stack]; exact rel.stack
  · rw [← equiv.memory]; exact rel.memory
  · rw [← equiv.code]; exact rel.code
  · rw [← equiv.logs]; exact rel.logs
  · rw [← equiv.msg]; exact rel.msg
  · rw [← equiv.output]; exact rel.output
  · rw [← equiv.returnData]; exact rel.returnData
  · rw [← equiv.error]; exact rel.error

lemma rel_of_equiv_of_rel {evm evm' evm''} {rs : Evm.Rels}
    (equiv : evm ≅ evm') (rel : Evm.Rel rs evm' evm'') :
    Evm.Rel rs evm evm'' := by
  constructor
  · rw [equiv.stack]; exact rel.stack
  · rw [equiv.memory]; exact rel.memory
  · rw [equiv.code]; exact rel.code
  · rw [equiv.logs]; exact rel.logs
  · rw [equiv.msg]; exact rel.msg
  · rw [equiv.output]; exact rel.output
  · rw [equiv.returnData]; exact rel.returnData
  · rw [equiv.error]; exact rel.error


lemma push_of_pushAt {evm bs exn} (cr : Exec evm exn)
    (h_at : PushAt evm.code evm.pc bs) :
    ∃ (evm' : Evm) (cr' : Exec evm' exn),
      evm'.pc = evm.pc + bs.length + 1 ∧
      Evm.Push [B8L.toB256 bs] evm evm' ∧
      Pack.Rel ⟨evm', exn, cr'⟩ ⟨evm, exn, cr⟩ := by
  sorry

-- lemma push_of_pushAt {e s pc bs r} (cr : Exec e s pc r) (h_at :PushAt e pc bs) :
--     ∃ (s' : Desc) (cr' : Exec e s' (pc + bs.length + 1) r),
--       Desc.Push [B8L.toB256 bs] s s' ∧
--       Exec'.Rel ⟨e, s', pc + bs.length + 1, r, cr'⟩ ⟨e, s, pc, r, cr⟩ := by
--   cases cr with
--   | step =>
--     rename Desc => s'; refine' ⟨s', _⟩
--     have h_prec := Exec'.Rel.step asm asm
--     rename Step _ _ _ _ _ => h_step; cases h_step
--     · cases not_pushAt_of_op_at  asm h_at
--     · cases not_pushAt_of_cop_at asm h_at
--     · cases not_pushAt_of_cop_at asm h_at
--     · cases not_pushAt_of_jop_at asm h_at
--     · rename (PushAt e pc _) => h_at'
--       cases pushAt_unique h_at h_at'
--       refine' ⟨_, asm, h_prec⟩
--   | exec =>
--     cases not_pushAt_of_cop_at asm h_at
--   | halt =>
--     rename Halt _ _ _ _ => h_halt; cases h_halt
--     · cases not_pushAt_of_hop_at asm h_at
--     · cases List.not_slice_length h_at.left

lemma Nat.lo_eq (m n : Nat) : m ↾ n = m % (2 ^ n) := rfl
lemma Nat.hi_eq (m n : Nat) : m ↿ n = (m >>> n) <<< n := rfl

lemma B32.ofNat_eq_iff_mod_eq_toNat (a : Nat) (b : B32) :
    a.toB32 = b ↔ a ↾ 32 = b.toNat :=
  UInt32.ofNat_eq_iff_mod_eq_toNat a b

lemma Nat.toB16_toB8 (n : Nat) : n.toB8.toB16 = (n ↾ 8).toB16 := by sorry

lemma Nat.toB32_toB16 (n : Nat) : n.toB16.toB32 = (n ↾ 16).toB32 := by
  have h0 : n.toB16.toB32 = n.toB32 % (2 ^ 16) :=
      (UInt16.toUInt32_eq_mod_65536_iff n.toUInt16 n.toUInt32).mpr
        (UInt32.toUInt16_ofNat' _).symm
  have h1: (n.toB32 % 2 ^ 16).toNat = n ↾ 16 := by
    have rw : B32.toNat (2 ^ 16) = 2 ^ 16 := rfl
    rw [B32.toNat_mod, rw]; clear rw
    rw [toNat_toB32, ← Nat.lo_eq]
    apply Nat.lo_lo_of_ge (by omega)
  have h2 : (n ↾ 16).toB32 = n.toB32 % (2 ^ 16) := by
    apply (B32.ofNat_eq_iff_mod_eq_toNat _ _).mpr
    apply Eq.trans (Nat.lo_lo_of_le (by omega)) h1.symm
  apply Eq.trans h0 h2.symm

lemma Nat.toB64_toB32 (n : Nat) : n.toB32.toB64 = (n ↾ 32).toB64 := by
  have h0 : n.toB32.toB64 = n.toB64 % (2 ^ 32) :=
      (UInt32.toUInt64_eq_mod_4294967296_iff n.toUInt32 n.toUInt64).mpr
        (UInt64.toUInt32_ofNat' _).symm
  have h1: (n.toB64 % 2 ^ 32).toNat = n ↾ 32 := by
    have rw : B64.toNat (2 ^ 32) = 2 ^ 32 := rfl
    rw [B64.toNat_mod, rw]; clear rw
    rw [toNat_toB64, ← Nat.lo_eq]
    apply Nat.lo_lo_of_ge (by omega)
  have h2 : (n ↾ 32).toB64 = n.toB64 % (2 ^ 32) := by
    apply (B64.ofNat_eq_iff_mod_eq_toNat _ _).mpr
    apply Eq.trans (Nat.lo_lo_of_le (by omega)) h1.symm
  apply Eq.trans h0 h2.symm
lemma toNat_toB16 {n : Nat} : n.toB16.toNat = n ↾ 16 := UInt16.toNat_ofNat'

lemma pair_aux (n m : Nat) :
    ((n >>> m ↾ m) ↾ (m + m)) <<< m ↾ (m + m) ||| (n ↾ m) ↾ (m + m) =
      n ↾ (m + m) := by
  rw [Nat.lo_lo_of_le (by omega)]
  rw [Nat.lo_lo_of_le (by omega)]
  apply Eq.trans _ <| high_or_low_eq_self (n ↾ (m + m)) m Nat.lo_lt
  apply congr_arg₂  _ _ (Nat.lo_lo_of_ge (by omega)).symm
  rw [@Nat.lo_add_shr n m m, ← Nat.lo_eq _ m, Nat.lo_lo]; rfl

lemma List.toB16_pair (n : Nat) :
    B8L.toB16 [(n >>> 8).toB8, n.toB8] = n.toB16 := by
  have h : (n >>> 8 ↾ 8).toB16 <<< 8 ||| (n ↾ 8).toB16 = n.toB16 := by
    rw [← B16.toNat_inj, toNat_toB16, B16.toNat_or, toNat_toB16]
    rw [B16.toNat_shiftLeft, toNat_toB16]; apply pair_aux n 8
  simp [B8L.toB16, B8L.pack, ekatD, takeD, reverse, reverseAux, tail, headD]
  rw [Nat.toB16_toB8, Nat.toB16_toB8, h]

lemma B32.toNat_shl (a b : B32) :
    (a <<< b).toNat = a.toNat <<< (b.toNat % 32) ↾ 32 :=
  UInt32.toNat_shiftLeft a b

lemma B64.toNat_shl (a b : B64) :
    (a <<< b).toNat = (a.toNat <<< (b.toNat % 64)) ↾ 64 :=
  UInt64.toNat_shiftLeft a b

def B16.concat (x y : B16) : B32 :=
  x.toB32 <<< 16 ||| y.toB32

def B32.concat (x y : B32) : B64 :=
  x.toB64 <<< 32 ||| y.toB64

lemma Nat.hi_le (a b : Nat) : a ↿ b ≤ a := by
  rw [hi, shiftLeft_eq, shiftRight_eq_div_pow]
  apply Nat.div_mul_le_self

lemma toB32_eq_concat (n : Nat) :
    n.toB32 = B16.concat (n >>> 16).toB16 n.toB16 := by
  rw [← B32.toNat_inj, toNat_toB32]
  simp only [B16.concat, Nat.toB32_toB16]
  rw [B32.toNat_or, B32.toNat_shl, toNat_toB32, toNat_toB32]
  rw [Nat.lo_lo_of_le (by omega), Nat.lo_lo_of_le (by omega)]
  have rw : (B32.toNat 16 % 32) = 16 := rfl
  rw [rw]; clear rw
  have rw : (n >>> 16 ↾ 16) <<< 16 ↾ 32 = (n ↾ 32) ↿ 16 := by
    rw [← Nat.lo_add_shr, ← Nat.hi_eq]
    apply Nat.lo_eq_of_lt
    apply lt_of_le_of_lt (Nat.hi_le _ _) Nat.lo_lt
  rw [rw, ← @Nat.lo_lo_of_ge n 32 16 (by omega)]
  apply (Nat.hi_or_lo _ _).symm

lemma toB64_eq_concat (n : Nat) :
    n.toB64 = B32.concat (n >>> 32).toB32 n.toB32 := by
  rw [← B64.toNat_inj, toNat_toB64]
  simp only [B32.concat, Nat.toB64_toB32]
  rw [B64.toNat_or, B64.toNat_shl, toNat_toB64, toNat_toB64]
  rw [Nat.lo_lo_of_le (by omega), Nat.lo_lo_of_le (by omega)]
  have rw : (B64.toNat 32 % 64) = 32 := rfl
  rw [rw]; clear rw
  have rw : (n >>> 32 ↾ 32) <<< 32 ↾ 64 = (n ↾ 64) ↿ 32 := by
    rw [← Nat.lo_add_shr, ← Nat.hi_eq]
    apply Nat.lo_eq_of_lt
    apply lt_of_le_of_lt (Nat.hi_le _ _) Nat.lo_lt
  rw [rw, ← @Nat.lo_lo_of_ge n 64 32 (by omega)]
  apply (Nat.hi_or_lo _ _).symm

lemma List.toB32_pair (n : Nat) (n_lt : n < 2 ^ 16) :
    B8L.toB32 [(n >>> 8).toB8, n.toB8] = n.toB32 := by
  simp only [ B8L.toB32, B8L.pack, ekatD, takeD,
    reverse, reverseAux, tail, headD, take, drop ]
  apply Eq.trans _ (toB32_eq_concat _).symm
  apply congr_arg₂ _ _ (congr_arg _ _)
  · apply congr_arg (λ x : B32 => x <<< 16) <| congr_arg _ _
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_of_lt (by omega)]; rfl
  · apply List.toB16_pair

lemma List.toB64_pair (n : Nat) (n_lt : n < 2 ^ 16) :
    B8L.toB64 [(n >>> 8).toB8, n.toB8] = n.toB64 := by
  simp only [ B8L.toB64, B8L.pack, ekatD, takeD,
    reverse, reverseAux, tail, headD, take, drop ]
  apply Eq.trans _ (toB64_eq_concat _).symm
  apply congr_arg₂ _ _ (congr_arg _ _)
  · apply congr_arg (λ x : B64 => x <<< 32) <| congr_arg _ _
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_of_lt (by omega)]; rfl
  · apply List.toB32_pair _ n_lt

lemma List.toB128_pair (n : Nat) (n_lt : n < 2 ^ 16):
    B8L.toB128 [(n >>> 8).toUInt8, n.toUInt8] = n.toB128 := by
  apply @Eq.trans _ _ ⟨0, n.toB64⟩
  · apply @Eq.trans _ _ ⟨0, B8L.toB64 [(n >>> 8).toUInt8, n.toUInt8]⟩
    · simp [B8L.toB128, List.ekatD, B8L.pack]
      apply congr_arg₂ _ rfl rfl
    · apply congr_arg₂ _ rfl <| List.toB64_pair _ n_lt
  · simp only [Nat.toB128]; apply congr_arg₂ _ _ rfl
    rw [Nat.shiftRight_eq_zero _ _ (by omega)]; rfl
lemma List.toB256_pair (n : Nat) (n_lt : n < 2 ^ 16):
    B8L.toB256 [(n >>> 8).toUInt8, n.toUInt8] = n.toB256 := by
  apply @Eq.trans _ _ ⟨0, n.toB128⟩
  · apply @Eq.trans _ _ ⟨0, B8L.toB128 [(n >>> 8).toUInt8, n.toUInt8]⟩
    · simp [B8L.toB256, List.ekatD, B8L.pack]
      apply congr_arg₂ _ rfl rfl
    · apply congr_arg₂ _ rfl <| List.toB128_pair _ n_lt
  · simp only [Nat.toB256]; apply congr_arg₂ _ _ rfl
    rw [Nat.shiftRight_eq_zero _ _ (by omega)]; rfl

lemma toNat_toB256 (n : Nat) : n.toB256.toNat = n ↾ 256 := by
  simp only [Nat.toB256, B256.toNat]; rw [toNat_toB128, toNat_toB128]
  apply Nat.or_eq_lo_add

lemma toNat_toB256_of_lt {n : Nat} (h : n < 2 ^ 256) : n.toB256.toNat = n := by
  rw [toNat_toB256, Nat.lo_eq_of_lt h]

lemma Jinst.run_of_at {evm exn o}
    (cr : Exec evm exn) (h_at : Jinst.At evm.code evm.pc o) :
    ∃ (evm' : Evm) (cr' : Exec evm' exn),
      Jinst.Run' evm o (.ok evm') ∧
      Pack.Rel ⟨evm', exn, cr'⟩ ⟨evm, exn, cr⟩ := by
  sorry

class HPrsv (f : Evm → Execution) where
  (prsv : ∀ {evm evm'}, f evm = .ok evm' → evm ≅ evm')

instance {gas} : HPrsv (chargeGas gas) := by
  constructor; intros evm evm' h
  simp only [chargeGas] at h; split at h; {cases h}
  injection h with rw; rw [← rw]
  constructor <;> rfl

instance : HPrsv Evm.incrPc := by
  constructor; intros evm evm' h
  simp only [Evm.incrPc] at h
  injection h with rw; rw [← rw]
  constructor <;> rfl

lemma chargeGas_inv_pc {gas : Nat} {evm evm' : Evm} :
    chargeGas gas evm = .ok evm' → evm.pc = evm'.pc := by
  simp only [chargeGas]; split <;> intro h
  · cases h
  · rw [← Except.ok.inj h]

lemma exec_inv_code {evm evm' : Evm} :
    Exec evm (.ok evm') → evm.code = evm'.code := by
  sorry


lemma Evm.equiv_trans {evm evm' evm''}
    (h₁ : Evm.Equiv evm evm') (h₂ : Evm.Equiv evm' evm'') :
    Evm.Equiv evm evm'' := by
  constructor
  · rw [h₁.stack, h₂.stack]; rfl
  · rw [h₁.memory, h₂.memory]; rfl
  · rw [h₁.code, h₂.code]; rfl
  · rw [h₁.logs, h₂.logs]; rfl
  · rw [h₁.msg, h₂.msg]; rfl
  · rw [h₁.output, h₂.output]; rfl
  · rw [h₁.returnData, h₂.returnData]; rfl
  · rw [h₁.error, h₂.error]; rfl

lemma incrPc_incr_pc {evm evm' : Evm} :
    evm.incrPc = .ok evm' → evm.pc + 1 = evm'.pc := by
  simp only [Evm.incrPc]; intro h; rw [← Except.ok.inj h]

lemma Evm.pop_of_pop {evm evm' : Evm} {x}
    (pop : Evm.pop evm = .ok ⟨x, evm'⟩) : Evm.Pop [x] evm evm' := by
  simp only [Evm.pop] at pop; split at pop; {cases pop}
  injection pop with eq; injection eq with eq eq'
  constructor <;> simp <;> rw [← eq'] <;> try {rfl}
  rename (evm.stack = _) => rw; rw [rw, eq]; rfl

lemma jumpdest_at {evm exn} (cr : Exec evm exn)
    (h : Jinst.At evm.code evm.pc Jinst.jumpdest) :
    ∃ (evm' : Evm) (cr' : Exec evm' exn),
      evm ≅ evm' ∧
      evm'.pc = evm.pc + 1 ∧
      Pack.Rel ⟨evm', exn, cr'⟩ ⟨evm, exn, cr⟩ := by
  rcases Jinst.run_of_at cr h with ⟨evm', exn', h_run, h_prec⟩
  simp only [Jinst.Run', Jinst.run] at h_run

  have eqv : evm ≅ evm' := by
    rcases of_bind_eq_ok h_run with ⟨evm_mid, eq, eq'⟩
    apply @Evm.equiv_trans _ evm_mid
    · apply HPrsv.prsv eq
    · apply HPrsv.prsv eq'
  refine' ⟨evm', exn', eqv, _, h_prec⟩
  rcases of_bind_eq_ok h_run with ⟨evm_gas, eq, eq'⟩
  rw [chargeGas_inv_pc eq, incrPc_incr_pc eq']

lemma Except.of_assert_eq_ok {p : Prop} [Decidable p] {ξ} {x : ξ}
    (h : Except.assert p x = .ok ()) : p := by
  simp [Except.assert] at h; apply h

lemma jump_at {s r} (cr : Exec s r)
    (h : Jinst.At s.code s.pc Jinst.jump) :
    ∃ (x : B256) (s' : Evm) (cr' : Exec s' r),
      s'.pc = x.toNat ∧
      Evm.Pop [x] s s' ∧
      jumpable s.code x.toNat = true ∧
      Pack.Rel ⟨s', r, cr'⟩ ⟨s, r, cr⟩ := by
  rcases Jinst.run_of_at cr h with ⟨s_j, cr_j, h_run, h_prec⟩
  simp only [Jinst.Run', Jinst.run] at h_run
  rcases of_bind_eq_ok h_run with ⟨⟨loc, s'⟩, pop_eq, run'⟩; clear h_run
  rcases of_bind_eq_ok run' with ⟨s'', cg_eq, run''⟩; clear run'
  rcases of_bind_eq_ok run'' with ⟨u, asrt_eq, run'''⟩; clear run''
  have pop := Evm.pop_of_pop pop_eq
  have eqv := (HPrsv.prsv cg_eq)
  injection run''' with rw
  refine' ⟨loc, s_j, cr_j, _, _, _, h_prec⟩
  · rw [← rw]
  · have eqv' : s'' ≅ s_j := by
      rw [← rw]; constructor <;> rfl
    apply rel_of_rel_of_equiv _ eqv'
    apply rel_of_rel_of_equiv pop eqv
  · have hh := Except.of_assert_eq_ok asrt_eq
    rw [pop.code, eqv.code]; apply Except.of_assert_eq_ok asrt_eq

lemma of_guard_eq_some {p : Prop} [hd : Decidable p] {ξ} {ox : Option ξ} {x} :
    (do guard p; ox) = some x → p ∧ ox = some x := by
  intro h
  cases em p with
  | inl hp => simp [hp] at h; constructor <;> assumption
  | inr hp => simp [guard, if_neg hp] at h

lemma subcode_compile_call {code : ByteArray} {l m n}
  (h : subcode code.toList m (Func.compile l m (Func.call n))) :
    ∃ (loc : Nat) (p : Func),
      l[n]? = some (loc, p) ∧
      loc < 2 ^ 16 ∧
      PushAt code m ([(loc >>> 8).toUInt8, loc.toUInt8]) ∧
      Jinst.jump.At code (m + 3) := by
  rcases of_subcode h with ⟨cd, h', h_slice⟩; clear h
  rcases of_bind_eq_some h' with ⟨⟨loc, p⟩, h_get, h⟩; clear h'
  simp at h
  rcases of_guard_eq_some h with ⟨h_lt, h_eq⟩; clear h
  refine' ⟨loc, p, h_get, h_lt, _⟩
  simp at h_eq; rw [← h_eq] at h_slice
  refine' ⟨
    @pushAt_of_slice code m
      [UInt8.ofNat (loc >>> 8), UInt8.ofNat loc]
      (List.slice_prefix h_slice),
    _
  ⟩
  have slice : code.toList.Slice (m + 3) [Jinst.jump.toB8] :=
    @List.slice_suffix _ code.toList m [_ ,_, _] _ h_slice
  apply @Jinst.at_of_slice code (m + 3) .jump slice

lemma Prog.get?_table {m n} {c : List Func} :
    (Prod.snd <$> (table m c)[n]? : Option Func) =
      ((@getElem? (List Func) Nat Func _ _ c n) : Option Func) := by
  induction c generalizing m n with
  | nil => rfl
  | cons p c' ih =>
    cases n with
    | zero => simp [table]
    | succ n => simp [table]; apply ih

lemma List.of_get?_succ_eq_some {X} {l : List X} {k x} :
    l[k + 1]? = some x → ∃ y, l[k]? = some y := by
  induction k generalizing l x with
  | zero =>
    match l with
    | [] => simp
    | [_] => simp
    | (y :: _ :: _) => intro _; refine' ⟨y, rfl⟩
  | succ k ih =>
    match l with
    | [] => simp
    | (_ :: l') =>
      intro h_get; apply ih h_get

lemma table_suffix {c k pfx sfx} (h : pfx <++ (table k c) ++> sfx) :
    ∃ k' c', sfx = table k' c' := by
  induction c generalizing k pfx sfx with
  | nil => refine' ⟨k, [], (List.append_eq_nil_iff.mp h.symm).right⟩
  | cons p ps ih =>
    simp [table] at h
    rcases List.cons_eq_append_iff.mp h with
      ⟨_, h'⟩ | ⟨pfx', _, h'⟩
    · refine ⟨k, p :: ps, h'⟩
    · exact ih h'

lemma Func.length_compile {l k p bs} (h : Func.compile l k p = some bs) :
    bs.length = compsize p := by
  induction p generalizing k bs with
  | branch p q ihp ihq =>
    rcases of_bind_eq_some h with ⟨cp, h_cp, h'⟩; clear h
    rcases of_guard_eq_some h' with ⟨h'', h⟩; clear h' h''
    rcases of_bind_eq_some h with ⟨cq, h_cq, h'⟩; clear h
    simp at h'; rw [← h']
    simp [List.length_append, List.length, compsize]
    rw [ihp h_cp, ihq h_cq]; omega
  | last o => simp [compile] at h; rw [← h]; rfl
  | next o p ih =>
    rcases of_bind_eq_some h with ⟨bs', h, h'⟩;
    simp at h'; rw [← h']
    simp [List.length_append, compsize]
    rw [ih h, Nat.add_comm]
  | call m =>
    rcases of_bind_eq_some h with ⟨⟨_, _⟩, _, h'⟩; clear h
    rcases of_guard_eq_some h' with ⟨h'', h⟩; clear h' h''
    simp at h; rw [← h];
    simp [List.length, compsize]

lemma of_get?_table_eq_some {f fs} {bs} {m n : ℕ} {p : Func}
    (h_eq : some bs = Prog.compile ⟨f, fs⟩)
    (h_get : (table 0 (f :: fs))[m]? = some (n, p)) :
    ∃ lft rgt,
      lft.length = m ∧
      (lft <++ (table 0 (f :: fs)) ++> ((n, p) :: rgt)) ∧
    ∃ pfx sfx,
      pfx.length = n ∧
      (pfx <++ bs ++> sfx) ∧
      (some sfx = Table.compile (table 0 (f :: fs)) ((n, p) :: rgt)) := by
  revert n p h_get
  induction m with
  | zero =>
    intro n p h_get
    simp [table] at h_get
    cases h_get.left; cases h_get.right; clear h_get
    simp only [table]
    refine' ⟨ [], _ , rfl, List.nil_append _, [],
              bs, rfl, (List.nil_append _).symm, _ ⟩
    rw [h_eq]; simp [Prog.compile, table]
  | succ m ih =>
    intro n p h_get
    rcases List.of_get?_succ_eq_some h_get with ⟨⟨k, q⟩, h⟩
    rcases ih h with
      ⟨lft, rgt, h_lft, h_split, pfx, sfx, h_pfx, h_split', h_sfx⟩
    clear ih h
    refine' ⟨lft ++ [(k, q)], _⟩
    have h : ∃ rgt', rgt = (n, p) :: rgt' := by
      have h_sub : m.succ - m = 1 := by omega
      have h_le : List.length lft ≤ Nat.succ m := by
        rw [h_lft]; apply Nat.le_succ
      have heq : (lft ++ (k, q) :: rgt)[m.succ]? = ((k, q) :: rgt)[m.succ - lft.length]? := by
        simp [List.getElem?_append_right, h_le]
      rw [h_split, heq, h_lft, h_sub] at h_get
      match rgt with
      | [] => simp  at h_get
      | _ :: rgt' =>
        simp at h_get
        rw [h_get]; refine ⟨_, rfl⟩
    rcases h with ⟨rgt', h_rgt'⟩
    refine' ⟨rgt', _, _, _⟩
    · simp [List.length, h_lft]
    · simp [Split]; rw [← h_rgt', h_split]
    · rcases Table.compile_cons_eq_some h_sfx.symm with
        ⟨cq, cl, h_cq, h_cl, h_sfx'⟩
      refine' ⟨pfx ++ ([Jinst.jumpdest.toB8] ++ cq), cl, _, _, _⟩
      · have hn : n = k + compsize q + 1 := by
          rcases table_suffix h_split with
            ⟨k', _ | ⟨q', c'⟩, h⟩ <;> simp [table] at h
          rcases h with ⟨⟨⟨_⟩,⟨_⟩⟩, h⟩
          rw [h_rgt'] at h
          cases c' <;> simp [table] at h
          apply h.left.left
        simp [List.length_append, List.length]
        rw [h_pfx, hn, Func.length_compile h_cq]
        omega
      · simp only [Split]; rw [List.append_assoc, ← h_sfx', h_split']
      · rw [← h_cl, ← h_rgt']

lemma subcode_of_get?_eq_some {f fs} {code : ByteArray} {k loc : ℕ} {p : Func}
    (h_eq : some code.toList = Prog.compile ⟨f, fs⟩)
    (h_get : getElem? (table 0 (f :: fs)) k = some ⟨loc, p⟩) :
    Jinst.At code loc Jinst.jumpdest ∧
    subcode code.toList (loc + 1) (Func.compile (table 0 (f :: fs)) (loc + 1) p) := by
  rcases of_get?_table_eq_some h_eq h_get with
    ⟨lft, rgt, _, _, pfx, sfx, h_pfx, h_split', h_sfx⟩
  unfold Jinst.At
  rcases Table.compile_cons_eq_some h_sfx.symm with ⟨bs, bs', h_bs, _, h_sfx'⟩
  have h_slice : List.Slice code.toList loc sfx := by
    rw [← h_pfx, h_split']; apply List.append_slice_suffix
  rw [h_sfx', List.append_assoc] at h_slice
  constructor
  · apply Jinst.at_of_slice
    apply List.slice_prefix h_slice
  · rw [h_bs]; simp [subcode]
    apply List.slice_prefix <| List.slice_suffix h_slice

theorem correct_core (f : Func) (fs : List Func) :
    ∀ (pk : Pack) (p : Func) (tevm : Evm),
      some pk.evm.code.toList = Prog.compile ⟨f, fs⟩ →
      subcode pk.evm.code.toList pk.evm.pc
        (Func.compile (table 0 (f :: fs)) pk.evm.pc p) →
      pk.exn = .ok tevm →
      Func.Run (f :: fs) pk.evm p tevm := by
  apply Pack.strongRec; intro pk ih p tevm eq sc eq_tevm
  match p with
  | .last o =>
    apply Func.Run.last; rw [← eq_tevm]
    apply Linst.run_of_at pk.ex <| Linst.getInst_of_slice sc
  | .next n p =>
    rcases of_subcode sc with ⟨cd, h_eq', h_slice⟩; clear sc
    rcases of_bind_eq_some h_eq' with ⟨cd', h_eq'', h_rw⟩; clear h_eq'
    simp [pure] at h_rw; rw [← h_rw] at h_slice; clear h_rw cd
    have h_at : n.At pk.evm.code pk.evm.pc := by
      apply Ninst.getInst_of_slice; apply List.slice_prefix h_slice
    rcases Ninst.run_of_at pk.ex h_at with ⟨evm', ex', h_prec, h_pc, h_run⟩
    have h_run' : Func.Run (f :: fs) evm' p tevm := by
      apply ih ⟨evm', pk.exn, ex'⟩ (Pack.lt_of_prec h_prec) p
      · simp; rw [← Ninst.inv_code h_run]; apply eq
      · simp; rw [h_pc, h_eq'', ← Ninst.inv_code h_run]
        apply List.slice_suffix h_slice
      · apply eq_tevm
    apply Func.Run.next h_run h_run'
  | .branch p q => sorry
  | .call k =>
    rcases subcode_compile_call sc with ⟨loc, p, h_get, h_loc, h_push, h_jump⟩
    have h_get' : (f :: fs)[k]? = p := by
      rw [← @Prog.get?_table 0 k (f :: fs), h_get]; rfl

    apply Func.Run.call h_get'



    have h :
        ∃ (s' : Evm) (cr' : Exec s' pk.exn),
          s'.pc = pk.evm.pc + 3  ∧
          Evm.Push [loc.toB256] pk.evm s' ∧
          Pack.Rel ⟨s', pk.exn, cr'⟩ pk := by
      sorry


    clear h_push; rcases h with ⟨s, cr, h_pc, h_push, h_prec⟩

    have h_jump' : Jinst.At s.code s.pc Jinst.jump := by
      rw [← h_push.code, h_pc]; apply h_jump
    rcases jump_at cr h_jump' with ⟨x, s', cr', h_pc', h_pop, h, h_prec'⟩
    have h_jumpable : Jinst.At s'.code s'.pc Jinst.jumpdest := by
      rw [← h_pop.code, h_pc']; apply at_of_jumpable h;

    clear h;

    rcases subcode_of_get?_eq_some eq h_get with ⟨h, hp⟩; clear h

    rcases jumpdest_at cr' h_jumpable with ⟨s'', cr'', eqv'', h_pc'', h_prec''⟩


    have h_lt : Pack.lt ⟨s'', pk.exn, cr''⟩ pk := by sorry

    have hh := ih ⟨s'', pk.exn, cr''⟩ h_lt p tevm sorry sorry --hp


















   --  rcases subcode_compile_call h_sub with ⟨loc, p, h_get, h_loc, h_push, h_jump⟩
   --  have h_get' : (f :: fs)[k]? = p := by
   --    rw [← @Prog.get?_table 0 k (f :: fs), h_get]; rfl
   --  apply Func.Run.call h_get'
   --  have h :
   --    ∃ (s' : Desc) (cr' : Exec pk.e s' (pk.pc + 3) pk.r),
   --      Desc.Push [loc.toB256] pk.s s' ∧
   --      Exec'.Rel ⟨pk.e, s', pk.pc + 3, pk.r, cr'⟩ pk := by
   --    rcases push_of_pushAt pk.cr h_push with ⟨s', cr', h, h_prec⟩
   --    rw [List.toB256_pair _ h_loc] at h
   --    refine' ⟨s', cr', h, h_prec⟩
   --  clear h_push; rcases h with ⟨s, cr, h_push, h_prec⟩
   --  rcases jump_at cr h_jump with ⟨x, s', cr', h_pop, h, h_prec'⟩
   --  rcases h with ⟨h_jumpable, h⟩; clear h
   --  rcases subcode_of_get?_eq_some h_eq h_get with ⟨h, hp⟩; clear h
   --  rcases jumpdest_at cr' h_jumpable with ⟨cr'', h_prec''⟩
   --  have h_loc' : loc < 2 ^ 256 := by
   --    apply Nat.lt_trans h_loc
   --    rw [Nat.pow_lt_pow_iff_right] <;> omega
   --  have h : loc = x.toNat ∧ pk.s = s' := by
   --    rcases Desc.push_cons_pop_cons h_push h_pop with ⟨hx, st, h_push', h_pop'⟩
   --    rw [Desc.push_nil h_push', Desc.pop_nil h_pop']
   --    rw [← congrArg B256.toNat hx, toNat_toB256_of_lt h_loc']; simp
   --  rcases h with ⟨h_rw, h_rw'⟩
   --  rw [h_rw']; rw [h_rw] at hp
   --  have h_lt : Exec'.lt ⟨pk.e, s', x.toNat + 1, pk.r, cr''⟩ pk := by
   --    refine' ⟨_, _, h_prec⟩
   --    apply Exec'.le.step _ _ _ _ h_prec'
   --    apply Exec'.le.step _ _ _ _ h_prec''
   --    apply Exec'.le.refl _
   --  apply ih ⟨pk.e, s', x.toNat + 1, pk.r, cr''⟩ h_lt p h_eq hp


  #exit




    /-
    rcases subcode_compile_branch sc with
      ⟨loc, h_loc, h_push, h_jumpi, h_scp, h_jumpdest, h_scq⟩
    have h :
        ∃ (evm' : Evm) (ex' : Exec evm' pk.exn),
          evm'.pc = pk.evm.pc + 3 ∧
          Evm.Push [Nat.toB256 loc] pk.evm evm' ∧
          Pack.Rel ⟨evm', pk.exn, ex'⟩ pk := by
      rcases push_of_pushAt pk.ex h_push
        with ⟨s', cr', h_pc, h, h_prec⟩
      rw [List.toB256_pair _ h_loc] at h
      refine' ⟨s', cr', h_pc, h, h_prec⟩
    rcases h with ⟨s', cr, h_pc', h_push, h_prec⟩
    rw [← h_pc'] at h_jumpi
    simp only [Jinst.At] at h_jumpi
    rw [h_push.code] at h_jumpi
    rcases jumpi_at cr h_jumpi with
        ⟨x, s'', cr', h_pc'', h_pop, h_prec'⟩
      | ⟨x, y, s'', cr', h_pc'', h_pop, h_jmp, hy, h_prec'⟩
    · clear h_jumpi h_scq h_jumpdest
      have h_pop' : Evm.Pop [0] pk.evm s'' := by
        rcases (Evm.push_cons_pop_cons h_push h_pop).right
          with ⟨st, h_push', h_pop'⟩
        exact rel_of_equiv_of_rel (Evm.push_nil h_push') h_pop'
      apply Func.Run.zero h_pop'
      have h_lt : Pack.lt ⟨s'', pk.exn, cr'⟩ pk := by
        apply Pack.lt.intro _ h_prec
        apply Pack.le.step _ h_prec'
        apply Pack.le.refl _
      rw [h_pop'.code] at eq
      have hhh := ih ⟨s'', pk.exn, cr'⟩ h_lt p --eq
      apply ih ⟨s'', pk.exn, cr'⟩ h_lt p tevm eq _ eq_tevm
      simp; rw [h_pop'.code] at h_scp
      rw [h_pc'', h_pc']; apply h_scp
    · clear h_jumpi h_jmp h_scp
      have h_loc' : loc < 2 ^ 256 := by
        apply Nat.lt_trans h_loc
        rw [Nat.pow_lt_pow_iff_right] <;> omega
      have h : x.toNat = loc ∧ Evm.Pop [y] pk.evm s'' := by
        rcases Evm.push_cons_pop_cons h_push h_pop
          with ⟨hx, st, h_push', h_pop'⟩
        constructor
        · rw [← congrArg B256.toNat hx, toNat_toB256_of_lt h_loc']
        · exact rel_of_equiv_of_rel (Evm.push_nil h_push') h_pop'
      rcases h with ⟨hx, h_pop'⟩
      have code_inv : pk.evm.code = s''.code := by
        rw [h_push.code, h_pop.code]
      have h_jumpdest' : Jinst.At s''.code s''.pc Jinst.jumpdest := by
        rw [← code_inv, h_pc'', hx]; exact h_jumpdest
      rcases jumpdest_at cr' h_jumpdest'
        with ⟨s''', cr''', eqv, h_pc''', h_prec'''⟩
      have h_pop_fin : Evm.Pop [y] pk.evm s''' :=
        rel_of_rel_of_equiv h_pop' eqv
      have h_run_fin : Func.Run (f :: fs) s''' q tevm := by
        have eq_compile : some s'''.code.toList = Prog.compile { main := f, aux := fs } := by
          rw [← eqv.code, ← code_inv]; exact eq
        have subcode_q :
            subcode s'''.code.toList s'''.pc (Func.compile (table 0 (f :: fs)) s'''.pc q) := by
          rw [← eqv.code, ← code_inv]; rw [h_pc''', h_pc'', hx]; apply h_scq
        have h_lt : Pack.lt { evm := s''', exn := pk.exn, ex := cr''' } pk :=
          by apply Pack.lt.intro _ h_prec;
             apply Pack.le.step _ h_prec';
             apply Pack.le.step _ h_prec''';
             apply Pack.le.refl
        apply ih ⟨s''', pk.exn, cr'''⟩ h_lt q tevm eq_compile subcode_q eq_tevm
      apply Func.Run.succ hy h_pop_fin h_run_fin
      -/
      sorry







#exit
theorem correct_core (f : Func) (fs : List Func) :
    ∀ (pk : Pack) (p : Func),
      some pk.evm.code.toList = Prog.compile ⟨f, fs⟩ →
      subcode pk.evm.code.toList pk.evm.pc
        (Func.compile (table 0 (f :: fs)) pk.evm.pc p) →
      Func.Run (f :: fs) pk.evm p pk.exn := by
  apply Pack.strongRec; intro ex ih p eq sc
  match p with
  | .last o =>
    exact Func.Run.last <| Linst.run_of_at ex.ex <| Linst.getInst_of_slice sc
  | .next n p =>
    rcases of_subcode sc with ⟨cd, h_eq', h_slice⟩; clear sc
    rcases of_bind_eq_some h_eq' with ⟨cd', h_eq'', h_rw⟩; clear h_eq'
    simp [pure] at h_rw; rw [← h_rw] at h_slice; clear h_rw cd
    have h_at : n.At ex.evm.code ex.evm.pc := by
      apply Ninst.getInst_of_slice; apply List.slice_prefix h_slice
    rcases Ninst.run_of_at ex.ex h_at with ⟨evm', ex', h_prec, h_pc, h_run⟩
    have h_run' : Func.Run (f :: fs) evm' p ex.exn := by
      apply ih ⟨evm', ex.exn, ex'⟩ (Pack.lt_of_prec h_prec) p
      · simp; rw [← Ninst.inv_code h_run]; apply eq
      · simp; rw [h_pc, h_eq'', ← Ninst.inv_code h_run]
        apply List.slice_suffix h_slice
    apply Func.Run.next h_run h_run'
  | .branch p q =>
    rcases subcode_compile_branch sc with
      ⟨loc, h_loc, h_push, h_jumpi, h_scp, h_jumpdest, h_scq⟩
    have h :
        ∃ (evm' : Evm) (ex' : Exec evm' ex.exn),
          evm'.pc = ex.evm.pc + 3 ∧
          Evm.Push [Nat.toB256 loc] ex.evm evm' ∧
          Exec'.Rel ⟨evm', ex.exn, ex'⟩ ex := by
      rcases push_of_pushAt ex.ex h_push
        with ⟨s', cr', h_pc, h, h_prec⟩
      rw [List.toB256_pair _ h_loc] at h
      refine' ⟨s', cr', h_pc, h, h_prec⟩
    rcases h with ⟨s', cr, h_pc', h_push, h_prec⟩
    rw [← h_pc'] at h_jumpi
    simp only [Jinst.At] at h_jumpi
    rw [h_push.code] at h_jumpi
    rcases jumpi_at cr h_jumpi with
        ⟨x, s'', cr', h_pc'', h_pop, h_prec'⟩
      | ⟨x, y, s'', cr', h_pop, h_jmp, hy, h_prec'⟩ --<;> clear h_jumpi
    · clear h_jumpi h_scq h_jumpdest
      have h_pop' : Evm.Pop [0] ex.evm s'' := by
        rcases (Evm.push_cons_pop_cons h_push h_pop).right
          with ⟨st, h_push', h_pop'⟩
        exact rel_of_equiv_of_rel (Evm.push_nil h_push') h_pop'
      apply Func.Run.zero h_pop'
      have h_lt : Exec'.lt ⟨s'', ex.exn, cr'⟩ ex := by
        apply Exec'.lt.intro _ h_prec
        apply Exec'.le.step _ _ _ _ h_prec'
        apply Exec'.le.refl _
      rw [h_pop'.code] at eq
      apply ih ⟨s'', ex.exn, cr'⟩ h_lt p eq
      simp; rw [h_pop'.code] at h_scp
      rw [h_pc'', h_pc']; apply h_scp
    · clear h_jumpi h_jmp h_scp
      have h_loc' : loc < 2 ^ 256 := by
        apply Nat.lt_trans h_loc
        rw [Nat.pow_lt_pow_iff_right] <;> omega
      have h : x.toNat = loc ∧ Evm.Pop [y] ex.evm s'' := by
        rcases Evm.push_cons_pop_cons h_push h_pop
          with ⟨hx, st, h_push', h_pop'⟩
        constructor
        · rw [← congrArg B256.toNat hx, toNat_toB256_of_lt h_loc']
        · exact rel_of_equiv_of_rel (Evm.push_nil h_push') h_pop'
      rcases h with ⟨hx, h_pop'⟩
      have h_run' : Func.Run (f :: fs) s'' q ex.exn := by
        rw [← hx] at h_jumpdest
        rcases jumpdest_at cr' h_jumpdest with ⟨cr'', h_prec''⟩

      #exit
        rw [← hx] at h_jumpdest
        rcases jumpdest_at cr' h_jumpdest with ⟨cr'', h_prec''⟩
        have h_lt : Exec'.lt ⟨pk.e, s'', x.toNat + 1, pk.r, cr''⟩ pk := by
          refine' ⟨_, _, h_prec⟩
          apply Exec'.le.step _ _ _ _ h_prec'
          apply Exec'.le.step _ _ _ _ h_prec''
          apply Exec'.le.refl _
        rw [← hx] at h_scq
        apply ih ⟨pk.e, s'', x.toNat + 1, pk.r, cr''⟩ h_lt q h_eq h_scq
      apply Func.Run.succ hy h_pop' h_run'
