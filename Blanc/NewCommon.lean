-- Common.lean : definitions and lemmas generally useful for writing and
-- verifying Blanc programs, including a correctness proof for the Blanc
-- compiler and tactics for automating Blanc program verification.

import Mathlib.Tactic.Have
import Blanc.NewSemantics

structure Exec' : Type where
  (evm : Evm)
  (exn : Execution)
  (ex : Exec evm exn)

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

abbrev Exec'.Pred : Type := Exec' → Prop

def Exec'.imp (π π' : Exec'.Pred) : Exec'.Pred := λ pk => π pk → π' pk

infix:70 " →p " => Exec'.imp

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
  | intro (pk pk' pk'' : Exec') :
    Exec'.le pk pk' → Exec'.Rel pk' pk'' → Exec'.lt pk pk''

lemma Exec'.lt_of_prec {pk pk' : Exec'} (rel : Rel pk pk') : lt pk pk' :=
  .intro _ _ _ (le.refl pk) rel

def Exec'.gt (pk pk' : Exec') : Prop := Exec'.lt pk' pk

lemma Exec'.eq_or_lt_of_le :
  ∀ {p p'}, Exec'.le p p' → p = p' ∨ Exec'.lt p p' := by
  intros p p'' h0
  rcases h0 with ⟨_, _, p'⟩ | ⟨p', _, h1, h2⟩
  · left; rfl
  · right; refine (.intro _ _ _ h1 h2)

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
    rcases lt with ⟨_, _ , le, ⟨_⟩⟩
    apply Exec'.acc_of_le le acc
  · intro _ _ _ _ _ _ _ _; constructor;
    intro _ h; rcases h with ⟨_, _, _, ⟨_⟩⟩
  · intro evm n evm' exn' evm'' exn get run ex' ex acc acc'
    constructor; intro _ lt; rcases lt with ⟨_, _ , le, ⟨_⟩⟩
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


lemma Linst.toRinst_toB8_eq_none {l : Linst} : l.toB8.toRinst = .none := by
  cases l <;> rfl

lemma Linst.toXinst_toB8_eq_none {l : Linst} : l.toB8.toXinst = .none := by
  cases l <;> rfl

lemma Linst.toJinst_toB8_eq_none {l : Linst} : l.toB8.toJinst = .none := by
  cases l <;> rfl

lemma Linst.toLinst_toB8_eq_some {l : Linst} : l.toB8.toLinst = .some l := by
  cases l <;> rfl

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
    rcases List.getElem?_eq_some_iff.mp eq with ⟨foo, bar⟩
    rw [ByteArray.toList_eq_toList_data] at foo
    apply foo
  rw [if_pos lt]
  conv => lhs; arg 1; lhs; rhs; rw [rw]; rfl
  rw [Linst.toRinst_toB8_eq_none, none_mapRev, none_orElse]
  conv => lhs; arg 1; lhs; rhs; rw [rw]; rfl
  rw [Linst.toXinst_toB8_eq_none, none_mapRev, none_orElse]
  conv => lhs; arg 1; lhs; rhs; rw [rw]; rfl
  rw [Linst.toJinst_toB8_eq_none, none_mapRev, none_orElse]
  conv => lhs; arg 1; lhs; rhs; rw [rw]; rfl
  rw [Linst.toLinst_toB8_eq_some]; rfl

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
      (rel : Exec'.Rel ⟨evm', exn, ex'⟩ ⟨evm, exn, ex⟩),
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

def PushAt (evm : Evm) (pc : Nat) (xs : B8L) : Prop :=
  ∃ le : xs.length ≤ 32, evm.getInst' pc = some (.next (.push xs le))

lemma subcode_compile_branch {evm : Evm} {k l p q}
    (h : subcode evm.code.toList k (Func.compile l k (Func.branch p q))) :
    ∃ loc : Nat,
      loc < 2 ^ 16 ∧
      PushAt evm k [(loc >>> 8).toUInt8, loc.toUInt8] ∧
      Jinst.jumpi.At evm.code (k + 3) ∧
      subcode evm.code.toList (k + 4) (Func.compile l (k + 4) p) ∧
      Jinst.jumpdest.At evm.code loc ∧
      subcode evm.code.toList (loc + 1) (Func.compile l (loc + 1) q) := by
  sorry

lemma jumpi_at {evm exn} (ex : Exec evm exn) (h : Jinst.jumpi.At evm.code evm.pc) :
    ( ∃ (x : B256) (evm' : Evm) (ex' : Exec evm' exn),
        evm'.pc = evm.pc + 1 ∧
        Evm.Pop [x, 0] evm evm' ∧
        Exec'.Rel ⟨evm', exn, ex'⟩ ⟨evm, exn, ex⟩ ) ∨
    ( ∃ (x y : B256) (evm' : Evm) (ex' : Exec evm' exn),
        Evm.Pop [x, y] evm evm' ∧
        --Jumpable e x.toNat ∧ y ≠ 0 ∧
        Exec'.Rel ⟨evm', exn, ex'⟩ ⟨evm, exn, ex⟩ ) := by
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

infix:70 " ≅ "  => Evm.Rel Evm.Rels.eqs

lemma Evm.push_nil {evm evm'} (h : Evm.Push [] evm evm') : evm ≅ evm' := by
  have h_stk : evm.stack = evm'.stack := h.stack.symm
  exact {h with stack := h_stk}

theorem correct_core (f : Func) (fs : List Func) :
    ∀ (pk : Exec') (p : Func),
      some pk.evm.code.toList = Prog.compile ⟨f, fs⟩ →
      subcode pk.evm.code.toList pk.evm.pc
        (Func.compile (table 0 (f :: fs)) pk.evm.pc p) →
      Func.Run (f :: fs) pk.evm p pk.exn := by
  apply Exec'.strongRec; intro ex ih p eq sc
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
      apply ih ⟨evm', ex.exn, ex'⟩ (Exec'.lt_of_prec h_prec) p
      · simp; rw [← Ninst.inv_code h_run]; apply eq
      · simp; rw [h_pc, h_eq'', ← Ninst.inv_code h_run]
        apply List.slice_suffix h_slice
    apply Func.Run.next h_run h_run'
  | .branch p q =>
    rcases subcode_compile_branch sc with
      ⟨loc, h_loc, h_push, h_jumpi, h_scp, h_jumpdest, h_scq⟩
      --⟨loc, h_loc, h_push, h_jumpi, h_scp, h_jumpdest, h_scq⟩
    have h :
        ∃ (evm' : Evm) (ex' : Exec evm' ex.exn),
          evm'.pc = ex.evm.pc + 3 ∧
          Evm.Push [Nat.toB256 loc] ex.evm evm' ∧
          Exec'.Rel ⟨evm', ex.exn, ex'⟩ ex := by
      --rcases push_of_pushAt pk.cr h_push with ⟨s', cr', h, h_prec⟩
      --rw [List.toB256_pair _ h_loc] at h
      --refine' ⟨s', cr', h, h_prec⟩
      sorry
    rcases h with ⟨s', cr, h_pc', h_push, h_prec⟩
    rw [← h_pc'] at h_jumpi
    simp only [Jinst.At] at h_jumpi
    rw [h_push.code] at h_jumpi
    rcases jumpi_at cr h_jumpi with
        ⟨x, s'', cr', h_pc', h_pop, h_prec'⟩
      | ⟨x, y, s'', cr', h_pop, h_jmp, hy, h_prec'⟩ <;> clear h_jumpi
    · clear h_scq h_jumpdest
      have h_pop' : Evm.Pop [0] ex.evm s'' := by
        rcases (Evm.push_cons_pop_cons h_push h_pop).right
          with ⟨st, h_push', h_pop'⟩
        have foo := Evm.push_nil h_push'

        -- rw [Desc.push_nil h_push']; exact h_pop'
      -- apply Func.Run.zero h_pop'
      -- have h_lt : Exec'.lt ⟨pk.e, s'', pk.pc +4, pk.r, cr'⟩ pk := by
      --   refine' ⟨_, _, h_prec⟩
      --   apply Exec'.le.step _ _ _ _ h_prec'
      --   apply Exec'.le.refl _
      -- apply ih ⟨pk.e, s'', pk.pc + 4, pk.r, cr'⟩ h_lt p h_eq h_scp
