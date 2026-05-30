-- Common.lean : definitions and lemmas generally useful for writing and
-- verifying Blanc programs, including a correctness proof for the Blanc
-- compiler and tactics for automating Blanc program verification.

import Mathlib.Tactic.Have
import Blanc.ReSemantics



def Func.toString : Func → String
  | .last o => Linst.toString o ++ " ::."
  | .next o p => o.toString ++ " ::: " ++ p.toString
  | .branch p q => "{" ++ q.toString ++ "} <?> {" ++ p.toString ++ "}"
  | .call _ => "[TAIL]"

instance : Repr Func := ⟨λ p _ => Func.toString p⟩

def Func.stop : Func := .last .stop
def Func.rev : Func := .last .rev
def Func.ret : Func := .last .ret

def Ninst.pushB256 (w : B256) : Ninst :=
  push w.toB8L.sig <|
    le_of_le_of_eq (List.length_dropWhile_le _ _) (B256.length_toB8L _)

abbrev Ninst.add : Ninst := Ninst.reg Rinst.add
abbrev Ninst.mul : Ninst := Ninst.reg Rinst.mul
abbrev Ninst.sub : Ninst := Ninst.reg Rinst.sub
abbrev Ninst.div : Ninst := Ninst.reg Rinst.div
abbrev Ninst.sdiv : Ninst := Ninst.reg Rinst.sdiv
abbrev Ninst.mod : Ninst := Ninst.reg Rinst.mod
abbrev Ninst.smod : Ninst := Ninst.reg Rinst.smod
abbrev Ninst.addmod : Ninst := Ninst.reg Rinst.addmod
abbrev Ninst.mulmod : Ninst := Ninst.reg Rinst.mulmod
abbrev Ninst.exp : Ninst := Ninst.reg Rinst.exp
abbrev Ninst.signextend : Ninst := Ninst.reg Rinst.signextend
abbrev Ninst.lt : Ninst := Ninst.reg Rinst.lt
abbrev Ninst.gt : Ninst := Ninst.reg Rinst.gt
abbrev Ninst.slt : Ninst := Ninst.reg Rinst.slt
abbrev Ninst.sgt : Ninst := Ninst.reg Rinst.sgt
abbrev Ninst.eq : Ninst := Ninst.reg Rinst.eq
abbrev Ninst.iszero : Ninst := Ninst.reg Rinst.iszero
abbrev Ninst.and : Ninst := Ninst.reg Rinst.and
abbrev Ninst.or : Ninst := Ninst.reg Rinst.or
abbrev Ninst.xor : Ninst := Ninst.reg Rinst.xor
abbrev Ninst.not : Ninst := Ninst.reg Rinst.not
abbrev Ninst.byte : Ninst := Ninst.reg Rinst.byte
abbrev Ninst.shr : Ninst := Ninst.reg Rinst.shr
abbrev Ninst.shl : Ninst := Ninst.reg Rinst.shl
abbrev Ninst.sar : Ninst := Ninst.reg Rinst.sar
abbrev Ninst.kec : Ninst := Ninst.reg Rinst.kec
abbrev Ninst.address : Ninst := Ninst.reg Rinst.address
abbrev Ninst.balance : Ninst := Ninst.reg Rinst.balance
abbrev Ninst.origin : Ninst := Ninst.reg Rinst.origin
abbrev Ninst.caller : Ninst := Ninst.reg Rinst.caller
abbrev Ninst.callvalue : Ninst := Ninst.reg Rinst.callvalue
abbrev Ninst.calldataload : Ninst := Ninst.reg Rinst.calldataload
abbrev Ninst.calldatasize : Ninst := Ninst.reg Rinst.calldatasize
abbrev Ninst.calldatacopy : Ninst := Ninst.reg Rinst.calldatacopy
abbrev Ninst.codesize : Ninst := Ninst.reg Rinst.codesize
abbrev Ninst.codecopy : Ninst := Ninst.reg Rinst.codecopy
abbrev Ninst.gasprice : Ninst := Ninst.reg Rinst.gasprice
abbrev Ninst.extcodesize : Ninst := Ninst.reg Rinst.extcodesize
abbrev Ninst.extcodecopy : Ninst := Ninst.reg Rinst.extcodecopy
abbrev Ninst.retdatasize : Ninst := Ninst.reg Rinst.retdatasize
abbrev Ninst.retdatacopy : Ninst := Ninst.reg Rinst.retdatacopy
abbrev Ninst.extcodehash : Ninst := Ninst.reg Rinst.extcodehash
abbrev Ninst.blockhash : Ninst := Ninst.reg Rinst.blockhash
abbrev Ninst.coinbase : Ninst := Ninst.reg Rinst.coinbase
abbrev Ninst.timestamp : Ninst := Ninst.reg Rinst.timestamp
abbrev Ninst.number : Ninst := Ninst.reg Rinst.number
abbrev Ninst.prevrandao : Ninst := Ninst.reg Rinst.prevrandao
abbrev Ninst.gaslimit : Ninst := Ninst.reg Rinst.gaslimit
abbrev Ninst.chainid : Ninst := Ninst.reg Rinst.chainid
abbrev Ninst.selfbalance : Ninst := Ninst.reg Rinst.selfbalance
abbrev Ninst.basefee : Ninst := Ninst.reg Rinst.basefee
abbrev Ninst.blobhash : Ninst := Ninst.reg Rinst.blobhash
abbrev Ninst.blobbasefee : Ninst := Ninst.reg Rinst.blobbasefee
abbrev Ninst.pop : Ninst := Ninst.reg Rinst.pop
abbrev Ninst.mload : Ninst := Ninst.reg Rinst.mload
abbrev Ninst.mstore : Ninst := Ninst.reg Rinst.mstore
abbrev Ninst.mstore8 : Ninst := Ninst.reg Rinst.mstore8
abbrev Ninst.sload : Ninst := Ninst.reg Rinst.sload
abbrev Ninst.sstore : Ninst := Ninst.reg Rinst.sstore
abbrev Ninst.tload : Ninst := Ninst.reg Rinst.tload
abbrev Ninst.tstore : Ninst := Ninst.reg Rinst.tstore
abbrev Ninst.mcopy : Ninst := Ninst.reg Rinst.mcopy
abbrev Ninst.pc : Ninst := Ninst.reg Rinst.pc
abbrev Ninst.msize : Ninst := Ninst.reg Rinst.msize
abbrev Ninst.gas : Ninst := Ninst.reg Rinst.gas
abbrev Ninst.dup (n : Fin 16) : Ninst := Ninst.reg (Rinst.dup n)
abbrev Ninst.swap (n : Fin 16) : Ninst := Ninst.reg (Rinst.swap n)
abbrev Ninst.log (n : Fin 5) : Ninst := Ninst.reg (Rinst.log n)
abbrev Ninst.create : Ninst := Ninst.exec Xinst.create
abbrev Ninst.call : Ninst := Ninst.exec Xinst.call
abbrev Ninst.callcode : Ninst := Ninst.exec Xinst.callcode
abbrev Ninst.delcall : Ninst := Ninst.exec Xinst.delcall
abbrev Ninst.create2 : Ninst := Ninst.exec Xinst.create2
abbrev Ninst.statcall : Ninst := Ninst.exec Xinst.statcall

abbrev Line : Type := List Ninst

infixr:65 " <?> " => λ f g => Func.branch g f
infixr:65 " ::: " => Func.next
postfix:100 " ::. " => Func.last

def prepend : Line → Func → Func
  | [], x => x
  | i :: is, x => i ::: prepend is x

infixr:65 " +++ " => prepend

inductive Line.Run : Env → Desc → Line → Desc → Prop
  | nil : ∀ {e s}, Line.Run e s [] s
  | cons :
    ∀ {e s i s' l s''},
      Ninst.Run e s i s' →
      Line.Run e s' l s'' →
      Line.Run e s (i :: l) s''

open Ninst

def mstoreAt (x : B256) : Line := [pushB256 (x * 32), mstore]

-- assumes : k = # of indexed items (max 3)
-- assumes : Stack = ev_sig :: idx_item_0 ... idx_item_{k-1}
-- assumes : mem[x * 32, (x + y) * 32 - 1] = unindexed data
def logWith (k : Fin 4) (x y : B256) : Line :=
  pushB256 (y * 32) :: pushB256 (x * 32) :: -- x * 32 :: y * 32 :: ev_sig :: idx_item_0 ... idx_item_{k+1}
  log k.succ :: []

-- cdc X Y Z := calldatacopy(X, Y, Z)
-- I.e., look at the calldata, skip its first Y bytes,
-- and copy the next Z bytes into location X of memory.
def cdc (x y z : B256) : Line :=
  pushB256 z :: -- z
  pushB256 y :: -- y :: z
  pushB256 x :: -- x :: y :: z
  calldatacopy :: []

def argCopy (x y z : B256) : Line :=
  cdc (x * 32) ((y * 32) + 4) (z * 32)

def pushList : List B256 → Line := List.map pushB256

def returnMemoryRange (x y : B256) : Func := pushList [y, x] +++ Func.ret

def cdl (x : B256) : Line := [pushB256 x, calldataload]

def arg (k : B256) : Line := cdl ((32 * k) + 4)



-- Push a 256-bit word used for testing address validity.
-- NOT and SHL are used so it takes up only 6 bytes of code,
-- whereas pushing the value directly would take up 32.

def pushAddressMask : Line := [pushB256 0, not, pushB256 (Nat.toB256 160), shl]

-- ( adr -- adr_invalid? )
def checkNonAddress : Line := pushAddressMask ++ [Ninst.and]

-- ( adr -- adr_valid? )
def checkAddress : Line := checkNonAddress ++ [iszero]

def returnTrue : Func :=
  pushB256 1 ::: mstoreAt 0 +++ -- || 1
  pushList [32, 0] +++ -- 0 :: 32 || 1
  Func.ret

abbrev Exec.Pred : Type :=
  ∀ pc sevm devm exc, Exec pc sevm devm exc → Prop

abbrev Prog.Pred : Type :=
  Nat → Sevm → Devm → Prog → Execution → Prop

def Exec.Fa (π : Exec.Pred) : Prop :=
  ∀ e s pc r (ex : Exec e s pc r), π _ _ _ _ ex

def Fortify (π : Exec.Pred) : Exec.Pred :=
  λ _ sevm _ _ exn =>
    (Exec.Fa <| λ _ sevm' _ _ exn' => sevm'.depth < sevm.depth → π _ _ _ _ exn') → π _ _ _ _ exn

lemma Exec.strong_rec (π : Exec.Pred)
  (fa : Exec.Fa (Fortify π)) : Exec.Fa π := by
  intros pc sevm devm exn exc
  apply
    @Nat.strongRecOn
      ( λ depth =>
          ∀ pc_ sevm_ devm_ exc_ (exn_ : Exec pc_ sevm_ devm_ exc_),
            depth = sevm_.depth → π _ _ _ _ exn_)
      sevm.depth
  · intro depth ih pc_ sevm_ devm_ exc_ exn_ eq; apply fa
    intro pc' sevm' devm' exn' exc' lt'; rw [← eq] at lt'
    apply ih sevm'.depth lt' _ _ _ _ _ rfl
  · rfl


/-

lemma frel_of_frel {ξ υ} {x : ξ} {r s : υ → υ → prop} {f g : ξ → υ}
    (h : r (f x) (g x) → s (f x) (g x)) (h' : frel x r f g) : frel x s f g := by
  intro x'; constructor <;> intro hx
  · cases hx; exact h <| (h' x).left rfl
  · exact (h' x').right hx

lemma Stack.of_push_nil {s t : Stack} : Push [] s t → s = t := by
  intro h; simp [Push, Split] at h; rw [h]

lemma Stack.of_diff_nil {r s t : Stack} : Diff r [] s t → Pop r s t := by
  intro h; rcases h with ⟨s', h0, h1⟩; rw [← of_push_nil h1]; apply h0

lemma Stack.of_nth_succ {n w v ws} : Nth (n + 1) w (v :: ws) → Nth n w ws := by
  intro h; cases h; assumption

lemma Stack.nth_append {n w xs ys} : Nth n w xs → Nth n w (xs ++ ys) := by
  revert n; induction xs with
  | nil => intros _ h; cases h
  | cons x xs ih =>
    intros n h; cases n
    · cases h; apply Nth.head
    · apply Nth.tail; apply ih (of_nth_succ h)

lemma Stack.nth_of_prefix {n w x xy} : Nth n w x → (x <<+ xy) → Nth n w xy := by
  intros h0 h1; rcases h1 with ⟨y, h2⟩; rw [h2]; apply nth_append h0

lemma Stack.nth_unique {n x y xs} : Nth n x xs → Nth n y xs → x = y := by
  induction xs generalizing n with
  | nil => intro h; cases h
  | cons x xs ih =>
    intros h h'; cases n
    · cases h; cases h'; rfl
    · apply ih (of_nth_succ h) (of_nth_succ h')

lemma Stack.swapCore_of_swap {n} {xxs yys : Stack} (h : Swap n xxs yys) :
  ∃ x y xs ys, xxs = x :: xs ∧ yys = y :: ys ∧ SwapCore x y n xs ys := by
  cases xxs; cases h; cases yys; cases h; refine ⟨_, _, _, _, rfl, rfl, h⟩

lemma Stack.swapCore_zero {x y s} : SwapCore x y 0 (y :: s) (x :: s) := by simp [SwapCore]
lemma Stack.swapCore_succ {n x y z s s'} :
    SwapCore x z n s s' → SwapCore x z (n + 1) (y :: s) (y :: s') := by simp [SwapCore]

lemma Stack.append_swapCore_append {x y} {n} {xs ys zs} :
    SwapCore x y n xs ys → SwapCore x y n (xs ++ zs) (ys ++ zs) := by
  induction n generalizing xs ys zs <;>
  ( intro h; cases xs; cases h; cases ys; cases h
    simp [SwapCore] at * )
  · apply h
  · rename (∀ _, _) => ih; refine ⟨h.left, ih h.right⟩

lemma Stack.append_swap_append {n} {xs ys zs : Stack} (h0 : Swap n xs ys) :
    Swap n (xs ++ zs) (ys ++ zs) := by
  rcases swapCore_of_swap h0 with ⟨x, y, xs', ys', h1, h2, _⟩
  cases h1; cases h2; simp [Swap] at *
  apply append_swapCore_append h0

lemma Stack.swapCore_unique {n} {x y z} {xs ys zs : Stack} :
    SwapCore x y n xs ys → SwapCore x z n xs zs → y = z ∧ ys = zs := by
  induction n generalizing xs ys zs <;>
  intros h h' <;> cases xs <;> cases ys <;> cases zs <;>
  try {cases h; done} <;> try {cases h'; done} <;>
  rcases h with ⟨h0, h1⟩ <;> rcases h' with ⟨h0', h1'⟩
  · rw [h1.left, ← h1'.left, ← h0, h0', ← h1.right, h1'.right]; simp
  · rename (∀ _, _) => ih
    rcases ih h1 h1' with ⟨ih0, ih1⟩
    rw [ih0, ← h0, h0', ih1]; simp

lemma Stack.swap_unique {n xs ys zs} (h : Swap n xs ys) (h' : Swap n xs zs) : ys = zs := by
  rcases swapCore_of_swap h with ⟨x, y, xs', ys', ⟨_⟩, ⟨_⟩, _⟩
  rcases swapCore_of_swap h' with ⟨x', z, xs'', zs', ⟨_⟩, ⟨_⟩, _⟩
  rcases swapCore_unique h h' with ⟨h, h'⟩; rw [h, h']

lemma Stack.append_dup_append {n : ℕ} {xs ys zs : Stack} :
    Dup n xs ys → Dup n (xs ++ zs) (ys ++ zs) := by
  intro h0; rcases h0 with ⟨x, h0, h1⟩
  refine' ⟨x, _, nth_append h1⟩
  simp [Push, Split] at *
  rw [h0]; rfl

lemma Stack.dup_unique {n : ℕ} {xs ys zs : Stack} :
  Dup n xs ys → Dup n xs zs → ys = zs := by
  intros h0 h1
  rcases h0 with ⟨x, h2, h3⟩
  rcases h1 with ⟨x', h4, h5⟩
  simp [Push, Split] at *
  rw [h2, h4, nth_unique h3 h5]

lemma Stack.split_of_dup {n xs xs' ys ys' zs} :
    Dup n xs xs' →
    Dup n ys ys' →
    (xs <++ ys ++> zs) →
    (xs' <++ ys' ++> zs) := by
  intros h0 h1 h2; apply dup_unique h1
  simp [Split] at h2; rw [h2]
  apply append_dup_append h0

lemma Stack.prefix_of_dup {n xs xs' ys ys'} :
    Dup n xs xs' → Dup n ys ys' → (xs <<+ ys) → (xs' <<+ ys') := by
  intros h0 h1 h2; rcases h2 with ⟨zs, h2⟩;
  refine ⟨zs, split_of_dup h0 h1 h2⟩

lemma Stack.prefix_of_swap {n xs xs' ys ys'} :
    Swap n xs xs' → Swap n ys ys' → (xs <<+ ys) → (xs' <<+ ys') := by
  intros h0 h1 h2
  rcases h2 with ⟨sfx, h3⟩
  refine' ⟨sfx, swap_unique h1 _⟩
  rw [h3]; apply append_swap_append h0

lemma Stack.pref_of_diff {x y xz yz} : Diff x y xz yz → (x <<+ xz) := by
  intro h0; rcases h0 with ⟨z, h1, _⟩; refine ⟨z, h1⟩

lemma Line.of_run_cons {e s i l s''} (h : Line.Run e s (i :: l) s'') :
    ∃ s', i.Run e s s' ∧ Line.Run e s' l s'' := by cases h; refine' ⟨_, asm, asm⟩

lemma run_prepend {c e s l s' p r}
    (h : Line.Run e s l s')
    (h' : Func.Run c e s' p r) :
    Func.Run c e s (l +++ p) r := by
  induction l generalizing s with
  | nil => cases h; exact h'
  | cons i l ih =>
    rcases Line.of_run_cons h with ⟨s', h_run, h_run'⟩
    apply Func.Run.next h_run (ih h_run')

lemma of_run_prepend {c e s r} :
   ∀ p q, Func.Run c e s (p +++ q) r →
   ∃ s', (Line.Run e s p s' ∧ Func.Run c e s' q r)
| [], _, h => ⟨s, cst, h⟩
| (_ :: p), q, (@Func.Run.next c e _ i _ _ _ h h') => by
  let ⟨s', hp, hq⟩ := of_run_prepend p q h'
  refine' ⟨s', Line.Run.cons h hp, hq⟩

lemma opRun_of_instRun {e s s'} {o : Rinst}
    (h : Ninst.Run e s (Ninst.reg o) s') : Rinst.Run e s o s' := by cases h; assumption

lemma of_run_singleton {e s i s'} (h : Line.Run e s [i] s') : Ninst.Run e s i s' := by
  rcases Line.of_run_cons h with ⟨_, _, ⟨_⟩⟩; assumption

lemma of_run_singleton' {e s o s'} (h : Line.Run e s [Ninst.reg o] s') :
    Rinst.Run e s o s' := opRun_of_instRun <| of_run_singleton asm

lemma run_append {e s a s' b s''}
    (h : Line.Run e s a s') (h' : Line.Run e s' b s'') : Line.Run e s (a ++ b) s'' := by
  induction a generalizing s with
  | nil => cases h; exact h'
  | cons i a ih =>
    rw [List.cons_append]
    rcases Line.of_run_cons h with ⟨_, hi, ha⟩
    apply Line.Run.cons hi (ih ha)

lemma of_run_append  {e s} (a) {b s''} (h : Line.Run e s (a ++ b) s'') :
    ∃ s', a.Run e s s' ∧ b.Run e s' s'' := by
  induction a generalizing s with
  | nil => refine' ⟨s, cst, h⟩
  | cons i a ih =>
    rcases Line.of_run_cons h with ⟨s0, hi, h_ab⟩
    rcases ih h_ab with ⟨s1, ha, hb⟩
    refine ⟨s1, Line.Run.cons hi ha, hb⟩

lemma of_run_last {o : Linst} {c e s r} (h : (o ::.).Run c e s r) : o.Run e s r := by
  cases h; assumption

lemma of_run_next {c e} {s : Desc} {i} {p : Func} {r}
    (h : Func.Run c e s (i ::: p) r) :
    ∃ s', (Ninst.Run e s i s' ∧ Func.Run c e s' p r) := by
  cases h; rename Desc => s'; refine ⟨s', asm, asm⟩

lemma of_run_branch {e s r} {p q : Func} (h : Func.Run c e s (q <?> p) r) :
    (∃ s', Desc.Pop [0] s s' ∧ Func.Run c e s' p r) ∨
    (∃ w s', w ≠ 0 ∧ Desc.Pop [w] s s' ∧ Func.Run c e s' q r) := by
  cases h
  · left; refine ⟨_, asm, asm⟩
  · right; refine ⟨_, _, asm, asm, asm⟩

lemma run_pop (e) {x s s'} (h : Desc.Pop [x] s s') : Run e s pop s' :=
  Ninst.Run.reg ⟨x, h⟩

lemma of_run_branch' {c e s r} {p q : Func} (h : Func.Run c e s (q <?> p) r) :
    ([0] <<+ s.stk ∧ Func.Run c e s (pop ::: p) r) ∨
    ((∃ w, w ≠ 0 ∧ [w] <<+ s.stk) ∧ Func.Run c e s (pop ::: q) r) := by
  rcases of_run_branch h with ⟨s', h', h''⟩ | ⟨w, s', hw, h', h''⟩
  · left; refine' ⟨⟨s'.stk, h'.stk⟩, Func.Run.next (run_pop _ h') h''⟩
  · right; refine' ⟨⟨w, hw, s'.stk, h'.stk⟩, Func.Run.next (run_pop _ h') h''⟩

def ValidAdr (w : B256) : Prop := ∃ a : Adr, a.toB256 = w

def validAdr_toB256 (a : Adr) : ValidAdr a.toB256 := ⟨a, rfl⟩

-- theorem toAdr_toB256 (a : Adr) :
--     B256.toAdr (Adr.toB256 a) = a := by
--   simp [Adr.toB256, B256.toAdr]

lemma toB256_toAdr {w : B256} :
    ValidAdr w → w.toAdr.toB256 = w := by
  intro h; rcases h with ⟨a, ha⟩;
  rw [← ha, toAdr_toB256]

def addressMask : B256 := ⟨⟨.max, 0xffffffff00000000⟩, 0⟩

lemma B128.and_eq_and_prod_and (x y : B128) :
    x &&& y = ⟨x.1 &&& y.1, x.2 &&& y.2⟩ := rfl

lemma B256.and_eq_and_prod_and (x y : B256) :
    x &&& y = ⟨x.1 &&& y.1, x.2 &&& y.2⟩ := rfl

lemma B128.zero_and {x : B128} : 0 &&& x = 0 := by
  simp [B128.and_eq_and_prod_and];
  apply Prod.ext <;> simp <;> apply UInt64.zero_and

lemma B64.mask_and_eq_zero (x : B32) :
    (0xffffffff00000000 : B64) &&& x.toUInt64 = 0 := by
  rw [← @UInt32.and_neg_one x, UInt32.toUInt64_and]
  rw [UInt64.and_comm (UInt32.toUInt64 _), ← UInt64.and_assoc]
  apply UInt64.zero_and

lemma validAdr_iff {w : B256} :
    ValidAdr w ↔ addressMask &&& w = 0 := by
  constructor <;> intro h
  · rcases h with ⟨⟨high, mid, low⟩, ⟨_⟩⟩
    simp [Adr.toB256, addressMask]
    rw [B256.and_eq_and_prod_and]
    simp [B128.zero_and]
    rw [B128.and_eq_and_prod_and]
    simp
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply B64.mask_and_eq_zero
    · rfl
  · refine' ⟨w.toAdr, _⟩
    rcases w with ⟨⟨wz, wh⟩, ⟨wm, wl⟩⟩
    have h_wz : wz = 0 := sorry
    simp only [B256.toAdr, Adr.toB256]
    apply Prod.ext <;> simp
    apply Prod.ext <;> simp [h_wz]
    sorry

-- lemma validAdr_iff {w : B256} :
--     ValidAdr w ↔ Bits.and addressMask w = 0 :=
--   ⟨Bits.mask_and_eq_zero _ _ _, Bits.of_mask_and_eq_zero _ _ _⟩

instance {w} : Decidable (ValidAdr w) := by
  apply decidable_of_iff _ validAdr_iff.symm

lemma of_run_branch_rev {e s p r} (h : Func.Run c e s (.rev <?> p) r) :
    ∃ s', Desc.Pop [0] s s' ∧ Func.Run c e s' p r := by
  rcases of_run_branch h with h' | ⟨_, _, _, _, h'⟩
  · apply h'
  · cases of_run_last h'

lemma not_run_prepend_rev {e s l r} : ¬ Func.Run c e s (l +++ Func.rev) r := by
  intro h; rcases of_run_prepend _ _ h with ⟨_, _, h'⟩; cases of_run_last h'

lemma op_run_iff_inst_run {o} : Rinst.Run e s o s' ↔ Ninst.Run e s (Ninst.reg o) s' := by
  constructor
  · apply Ninst.Run.reg
  · apply opRun_of_instRun

lemma of_run_push {e s s' xs p} (h : Ninst.Run e s (push xs p) s') :
    Desc.Push [xs.toB256] s s' := by cases h with | push h => assumption

lemma Vector.ext' {ξ n} (xs ys : Array ξ)
    (hx : xs.size = n) (hy : ys.size = n) (h_eq : xs = ys) :
    Vector.mk xs hx = Vector.mk ys hy := by
  cases h_eq; rfl

lemma B8L.sig_zero_cons (xs) : B8L.sig (0 :: xs) = B8L.sig xs := rfl
lemma B8L.sig_nonzero_cons (x xs) (h : x ≠ 0) : B8L.sig (x :: xs) = x :: xs := by
  simp only [sig]; rw [List.dropWhile_cons_of_neg]; simp [h]

lemma B8L.pack_zero_cons (xs n) : B8L.pack (0 :: xs) n = B8L.pack xs n := by
  simp only [pack, List.ekatD]
  rw [List.reverse_cons', List.takeD_concat]

lemma B8L.pack_sig (xs n) : B8L.pack (B8L.sig xs) n = B8L.pack xs n := by
  induction xs with
  | nil => simp [sig, pack]
  | cons b bs ih =>
    by_cases h : b = 0
    · cases h; rw [sig_zero_cons, pack_zero_cons, ih]
    · rw [sig_nonzero_cons b bs h]

lemma B8L.toB256_sig (bs : B8L) : B8L.toB256 (B8L.sig bs) = bs.toB256 := by
  simp only [B8L.toB256]; rw [B8L.pack_sig]

lemma of_run_pushB256 {e s s' x} (h : Ninst.Run e s (pushB256 x) s') :
    Desc.Push [x] s s' := by
  cases h with
  | push h =>
    rw [B8L.toB256_sig, B256.toB256_toB8L] at h
    apply h

lemma run_pushB256 (e) {s s' x} (h : Desc.Push [x] s s') :
    Ninst.Run e s (pushB256 x) s' := by
  apply Ninst.Run.push
  rw [B8L.toB256_sig, B256.toB256_toB8L]
  apply h

lemma frel_of_sstore {e} {s s' : Desc} {x y xs}:
    Desc.Sstore e s s' → (x :: y :: xs <<+ s.stk) →
    (Frel e.cta (Overwrite x y) s.stor s'.stor) := by
  intros h0 h1
  rcases h0 with ⟨x', y', h2, h3⟩; clear h3
  have h3 : x = x' ∧ y = y' := by
    have h3 := Stack.pref_of_diff h2.stk
    rcases List.of_cons_pref_of_cons_pref h1 h3 with ⟨h4, stk, h5, h6⟩
    rcases List.of_cons_pref_of_cons_pref h5 h6 with ⟨h7, _⟩
    refine ⟨h4, h7⟩
  rw [h3.left, h3.right]; apply h2.stor

lemma of_run_call {e} {s s'} (h : Ninst.Run e s .call s') :
    ( ∃ ep sp r,
        Xinst.Run' e s ep sp .call r s' ∧
        ((∃ (_ : Exec ep sp 0 r), True) ∨ PreRun sp r) ) ∨
    Fail s .call s' := by
  cases h; cases (asm : Xinst.Run _ _ _ _)
  · left; refine ⟨_, _, _, asm, .inl ⟨asm, cst⟩⟩
  · left; refine ⟨_, _, _, asm, .inr asm⟩
  · right; assumption

def Rinst.Inv {ξ : Type} (r : Desc → ξ) (o : Rinst) : Prop :=
  ∀ {e s s'}, Rinst.Run e s o s' → r s = r s'

def Jinst.Inv {ξ : Type} (r : Desc → ξ) (o : Jinst) : Prop :=
  ∀ {e s pc s' pc'}, Jinst.Run e s pc o s' pc' → r s = r s'

def Linst.Inv {ξ : Type} (f : Desc → ξ) (g : Result → ξ) (o : Linst) : Prop :=
  ∀ {e s r}, Linst.Run e s o r → f s = g r

def Ninst.Inv {ξ : Type} (r : Desc → ξ) (i : Ninst) : Prop :=
  ∀ {e s s'}, Ninst.Run e s i s' → r s = r s'

def Line.Inv {ξ : Type} (f : Desc → ξ) (l : Line) : Prop :=
  ∀ {e s s'}, l.Run e s s' → f s = f s'

def Func.Inv {ξ : Type} (f : Desc → ξ) (g : Result → ξ) (p : Func) : Prop :=
  ∀ {c e s r}, Func.Run c e s p r → f s = g r

def RelInv {X Y} (f : X → Y) (r : X → X → Prop) : Prop :=
  ∀ {x x'}, r x x' → f x = f x'

class Rinst.Hinv {ξ : Type} (f : Desc → ξ) (o : Rinst) where (inv : Rinst.Inv f o)
class Linst.Hinv {ξ : Type} (f : Desc → ξ) (g : Result → ξ) (o : Linst) where (inv : Linst.Inv f g o)
class Ninst.Hinv {ξ : Type} (f : Desc → ξ) (i : Ninst) where (inv : Ninst.Inv f i)

lemma fail_inv_bal {o : Xinst} : RelInv Desc.bal (Fail · o ·) := by
  intro s s'
  match o with
  | .create => simp [Fail]; intro _ _ _ h; apply h.bal
  | .call => simp [Fail]; intro _ _ _ _ _ _ _ h; apply h.bal
  | .callcode => simp [Fail]; intro _ _ _ _ _ _ _ h; apply h.bal
  | .delcall => simp [Fail]; intro _ _ _ _ _ _ h; apply h.bal
  | .create2 => simp [Fail]; intro _ _ _ _ h; apply h.bal
  | .statcall => simp [Fail]; intro _ _ _ _ _ _ h; apply h.bal

lemma fail_inv_stor {o : Xinst} : RelInv Desc.stor (Fail · o ·) := by
  intro s s'
  match o with
  | .create => simp [Fail]; intro _ _ _ h; apply h.stor
  | .call => simp [Fail]; intro _ _ _ _ _ _ _ h; apply h.stor
  | .callcode => simp [Fail]; intro _ _ _ _ _ _ _ h; apply h.stor
  | .delcall => simp [Fail]; intro _ _ _ _ _ _ h; apply h.stor
  | .create2 => simp [Fail]; intro _ _ _ _ h; apply h.stor
  | .statcall => simp [Fail]; intro _ _ _ _ _ _ h; apply h.stor

lemma fail_inv_code {o : Xinst} : RelInv Desc.code (Fail · o ·) := by
  intro s s'
  match o with
  | .create => simp [Fail]; intro _ _ _ h; apply h.code
  | .call => simp [Fail]; intro _ _ _ _ _ _ _ h; apply h.code
  | .callcode => simp [Fail]; intro _ _ _ _ _ _ _ h; apply h.code
  | .delcall => simp [Fail]; intro _ _ _ _ _ _ h; apply h.code
  | .create2 => simp [Fail]; intro _ _ _ _ h; apply h.code
  | .statcall => simp [Fail]; intro _ _ _ _ _ _ h; apply h.code

syntax "app_bal" : tactic
macro_rules
  | `(tactic| app_bal) =>  `(tactic| {have h' := Desc.Rel.bal asm; apply h'})

syntax "app_code" : tactic
macro_rules
  | `(tactic| app_code) => `(tactic| {have h' := Desc.Rel.code asm; apply h'})

syntax "app_stor" : tactic
macro_rules
  | `(tactic| app_stor) => `(tactic| {have h' := Desc.Rel.stor asm; rw[h']})

syntax "app_dest" : tactic
macro_rules
  | `(tactic| app_dest) => `(tactic| {have h' := Desc.Rel.dest asm; apply h'})

syntax "app_ret" : tactic
macro_rules
  | `(tactic| app_ret) => `(tactic| {have h' := Desc.Rel.ret asm; apply h'})

syntax "app_mem" : tactic
macro_rules
  | `(tactic| app_mem) => `(tactic| {have h' := Desc.Rel.mem asm; apply h'})

lemma Jinst.inv_bal {o} : Jinst.Inv Desc.bal o := by
  intros e s pc s' pc' h
  cases h <;> try {have h' := Desc.Rel.bal asm; apply h'}; rfl

lemma Jinst.inv_code {o} : Jinst.Inv Desc.code o := by
  intros e s pc s' pc' h
  cases h <;> try {have h' := Desc.Rel.code asm; apply h'}; rfl

lemma Jinst.inv_stor {o} : Jinst.Inv Desc.stor o := by
  intros e s pc s' pc' h
  cases h <;> try {have h' := Desc.Rel.stor asm; apply h'}; rfl

lemma Linst.inv_stor {o} : Linst.Inv Desc.stor Result.stor o := by intros e s r h; cases h <;> rfl
lemma Linst.inv_code {o} : Linst.Inv Desc.code Result.code o := by intros e s r h; cases h <;> rfl

lemma stop_inv_bal : Linst.Inv Desc.bal Result.bal (Linst.stop) := by intros e s r h; cases h; rfl
lemma ret_inv_bal : Linst.Inv Desc.bal Result.bal Linst.ret := by intros e s r h; cases h; rfl

instance {o} : Linst.Hinv Desc.stor Result.stor o := ⟨Linst.inv_stor⟩
instance {o} : Linst.Hinv Desc.code Result.code o := ⟨Linst.inv_code⟩

instance {ξ} {f g}: @Linst.Hinv ξ f g Linst.rev := by constructor; intros e s r h; cases h
instance : Linst.Hinv Desc.bal Result.bal Linst.ret := ⟨ret_inv_bal⟩
instance : Linst.Hinv Desc.bal Result.bal Linst.stop := ⟨stop_inv_bal⟩

syntax "app_bal_rec" : tactic
macro_rules
  | `(tactic| app_bal_rec) =>
    `(tactic| first | app_bal
                    | {rename (_ ∧ _) => h; have h' := h.left; app_bal}
                    | {rename (∃ _, _) => h; rcases h with ⟨_, _⟩; app_bal_rec})

syntax "app_code_rec" : tactic
macro_rules
  | `(tactic| app_code_rec) =>
    `(tactic| first | app_code
                    | {rename (_ ∧ _) => h; have h' := h.left; app_code}
                    | {rename (∃ _, _) => h; rcases h with ⟨_, _⟩; app_code_rec})

syntax "app_stor_rec" : tactic
macro_rules
  | `(tactic| app_stor_rec) =>
    `(tactic| first | app_stor
                    | {rename (_ ∧ _) => h; have h' := h.left; app_stor}
                    | {rename (∃ _, _) => h; rcases h with ⟨_, _⟩; app_stor_rec})

syntax "app_dest_rec" : tactic
macro_rules
  | `(tactic| app_dest_rec) =>
    `(tactic| first | app_dest
                    | {rename (_ ∧ _) => h; have h' := h.left; app_dest}
                    | {rename (∃ _, _) => h; rcases h with ⟨_, _⟩; app_dest_rec})

syntax "app_ret_rec" : tactic
macro_rules
  | `(tactic| app_ret_rec) =>
    `(tactic| first | app_ret
                    | {rename (_ ∧ _) => h; have h' := h.left; app_ret}
                    | {rename (∃ _, _) => h; rcases h with ⟨_, _⟩; app_ret_rec})

syntax "app_mem_rec" : tactic
macro_rules
  | `(tactic| app_mem_rec) =>
    `(tactic| first | app_mem
                    | {rename (_ ∧ _) => h; have h' := h.left; app_mem}
                    | {rename (∃ _, _) => h; rcases h with ⟨_, _⟩; app_mem_rec})

syntax "show_hinv_stor" : tactic
macro_rules
  | `(tactic| show_hinv_stor) =>
    `(tactic| constructor; intros e s s' h; app_stor_rec)

syntax "show_hinv_mem" : tactic
macro_rules
  | `(tactic| show_hinv_mem) =>
    `(tactic| constructor; intros e s s' h; app_mem_rec)

instance : Rinst.Hinv Desc.mem Rinst.add := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.mul := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.sub := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.div := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.sdiv := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.mod := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.smod := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.addmod := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.mulmod := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.exp := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.signextend := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.lt := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.gt := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.slt := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.sgt := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.eq := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.iszero := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.and := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.or := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.xor := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.not := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.byte := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.shr := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.shl := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.sar := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.kec := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.address := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.balance := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.origin := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.caller := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.callvalue := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.calldataload := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.calldatasize := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.codesize := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.gasprice := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.extcodesize := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.retdatasize := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.extcodehash := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.blockhash := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.coinbase := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.timestamp := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.number := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.prevrandao := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.gaslimit := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.chainid := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.selfbalance := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.basefee := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.blobhash := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.blobbasefee := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.pop := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.mload := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.sload := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.sstore := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.tload := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.tstore := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.pc := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.msize := by show_hinv_mem
instance : Rinst.Hinv Desc.mem Rinst.gas := by show_hinv_mem
instance {n} : Rinst.Hinv Desc.mem (Rinst.dup n) := by show_hinv_mem
instance {n} : Rinst.Hinv Desc.mem (Rinst.swap n) := by show_hinv_mem
instance {n} : Rinst.Hinv Desc.mem (Rinst.log n) := by
  match n with
  | ⟨0, _⟩ => show_hinv_mem
  | ⟨1, _⟩ => show_hinv_mem
  | ⟨2, _⟩ => show_hinv_mem
  | ⟨3, _⟩ => show_hinv_mem
  | ⟨4, _⟩ => show_hinv_mem
  | ⟨5, h⟩ => cases (Nat.lt_irrefl _ h)

instance : Rinst.Hinv Desc.stor Rinst.add := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.mul := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.sub := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.div := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.sdiv := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.mod := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.smod := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.addmod := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.mulmod := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.exp := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.signextend := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.lt := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.gt := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.slt := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.sgt := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.eq := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.iszero := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.and := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.or := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.xor := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.not := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.byte := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.shr := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.shl := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.sar := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.kec := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.address := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.balance := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.origin := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.caller := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.callvalue := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.calldataload := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.calldatasize := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.calldatacopy := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.codesize := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.codecopy := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.gasprice := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.extcodesize := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.extcodecopy := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.retdatasize := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.retdatacopy := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.extcodehash := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.blockhash := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.coinbase := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.timestamp := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.number := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.prevrandao := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.gaslimit := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.chainid := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.selfbalance := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.basefee := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.blobhash := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.blobbasefee := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.pop := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.mload := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.mstore := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.mstore8 := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.sload := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.tload := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.pc := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.msize := by show_hinv_stor
instance : Rinst.Hinv Desc.stor Rinst.gas := by show_hinv_stor
instance {n} : Rinst.Hinv Desc.stor (Rinst.dup n) := by show_hinv_stor
instance {n} : Rinst.Hinv Desc.stor (Rinst.swap n) := by show_hinv_stor
instance {n} : Rinst.Hinv Desc.stor (Rinst.log n) := by
  match n with
  | ⟨0, _⟩ => show_hinv_stor
  | ⟨1, _⟩ => show_hinv_stor
  | ⟨2, _⟩ => show_hinv_stor
  | ⟨3, _⟩ => show_hinv_stor
  | ⟨4, _⟩ => show_hinv_stor
  | ⟨5, h⟩ => cases (Nat.lt_irrefl _ h)

lemma Rinst.inv_bal {o} : Rinst.Inv Desc.bal o := by
  intros e s s' h; cases o <;>
  simp [Rinst.Run, Function.swap] at h <;> try {app_bal_rec}
  rename (Fin 5) => n
  match n with
  | ⟨0, _⟩ => app_bal_rec
  | ⟨1, _⟩ => app_bal_rec
  | ⟨2, _⟩ => app_bal_rec
  | ⟨3, _⟩ => app_bal_rec
  | ⟨4, _⟩ => app_bal_rec
  | ⟨5, h⟩ => cases (Nat.lt_irrefl _ h)

lemma Rinst.inv_code {o} : Rinst.Inv Desc.code o := by
  intros e s s' h; cases o <;>
  simp [Rinst.Run, Function.swap] at h <;> try {app_code_rec}
  rename (Fin 5) => n
  match n with
  | ⟨0, _⟩ => app_code_rec
  | ⟨1, _⟩ => app_code_rec
  | ⟨2, _⟩ => app_code_rec
  | ⟨3, _⟩ => app_code_rec
  | ⟨4, _⟩ => app_code_rec
  | ⟨5, h⟩ => cases (Nat.lt_irrefl _ h)

lemma Rinst.inv_stor {e s o s' a}
    (h_run : Rinst.Run e s o s') (h_ne : e.cta ≠ a) : s.stor a = s'.stor a := by
  cases o <;> try {app_stor_rec}
  · rcases h_run with ⟨x, y, h, _⟩
    apply (h.stor a).right h_ne
  · rename (Fin 5) => n
    match n with
    | ⟨0, _⟩ => app_stor_rec
    | ⟨1, _⟩ => app_stor_rec
    | ⟨2, _⟩ => app_stor_rec
    | ⟨3, _⟩ => app_stor_rec
    | ⟨4, _⟩ => app_stor_rec
    | ⟨5, h⟩ => cases (Nat.lt_irrefl _ h)

lemma Rinst.inv_dest {o} : Rinst.Inv Desc.dest o := by
  intros e s s' h; cases o <;>
  simp [Rinst.Run, Function.swap] at h <;> try app_dest_rec
  rename (Fin 5) => n
  match n with
  | ⟨0, _⟩ => app_dest_rec
  | ⟨1, _⟩ => app_dest_rec
  | ⟨2, _⟩ => app_dest_rec
  | ⟨3, _⟩ => app_dest_rec
  | ⟨4, _⟩ => app_dest_rec
  | ⟨5, h⟩ => cases (Nat.lt_irrefl _ h)

lemma Rinst.inv_ret {o} : Rinst.Inv Desc.ret o := by
  intros e s s' h; cases o <;>
  simp [Rinst.Run, Function.swap] at h <;> try app_ret_rec
  rename (Fin 5) => n
  match n with
  | ⟨0, _⟩ => app_ret_rec
  | ⟨1, _⟩ => app_ret_rec
  | ⟨2, _⟩ => app_ret_rec
  | ⟨3, _⟩ => app_ret_rec
  | ⟨4, _⟩ => app_ret_rec
  | ⟨5, h⟩ => cases (Nat.lt_irrefl _ h)

lemma Xinst.prep_inv_code {e s ep sp o r sw}
    (h : Xinst.Run' e s ep sp o r sw) : s.code = sp.code := by
  cases h <;> simp [Desc.prep]

lemma Xinst.code_eq_nil_of_run' {e s ep sp o rx sw}
    (h : Xinst.Run' e s ep sp o rx sw)
    (h' : ¬ o.isCall) : s.code ep.cta = [] := by
  cases h <;> try {apply (h' cst).elim} <;>
  {simp [Env.prep']; assumption}

lemma Xinst.wrap_inv_stor {e s ep sp o r sw}
    (h : Xinst.Run' e s ep sp o r sw) : r.stor = sw.stor := by
  cases h <;> try {simp [Desc.wrap']} <;> {simp [Desc.wrap]}

lemma Xinst.prep_inv_stor {e s ep sp o r sw}
    (h : Xinst.Run' e s ep sp o r sw) : s.stor = sp.stor := by
  cases h <;> simp [Desc.prep]

lemma Xinst.wrap_inv_bal {e s ep sp o r sw}
    (h : Xinst.Run' e s ep sp o r sw) : r.bal = sw.bal := by cases h <;> rfl

lemma Xinst.wrap_inv_code {e s ep sp o r sw}
    (h : Xinst.Run' e s ep sp o r sw) (h' : o.isCall) : r.code = sw.code := by
  cases h' <;> cases h <;> simp [Desc.wrap]

lemma Xinst.wrap_inv_code' {e s ep sp o r sw a}
    (h : Xinst.Run' e s ep sp o r sw) (h' : ep.cta ≠ a) : r.code a = sw.code a := by
  cases h <;> try {simp [Desc.wrap]} <;>
  {rename (Overwrite _ _ _ _) => h_ow; apply (h_ow a).right h'}

lemma Xinst.wrap_inv_code'' {a : Adr} {e s ep sp o r sw}
    (h : Xinst.Run' e s ep sp o r sw) (h' : s.code a ≠ []) :
    r.code a = sw.code a := by
  cases o <;> try {rw [Xinst.wrap_inv_code h cst]} <;>
  {apply Xinst.wrap_inv_code' h; intro hc; apply h'; rw [← hc]; cases h <;> assumption}

lemma Step.inv_code {e : Env} {s : Desc} {pc : ℕ} {s' : Desc} {pc' : ℕ}
    (h_step : Step e s pc s' pc') : s.code = s'.code := by
  cases h_step with
  | reg => exact Rinst.inv_code asm
  | pre =>
    rw [Xinst.prep_inv_code asm]
    apply Eq.trans <| PreRun.code asm
    apply Xinst.wrap_inv_code asm asm
  | fail => rw [fail_inv_code asm]
  | jump => rw [Jinst.inv_code asm]
  | push => rw [(asm : Desc.Push _ _ _).code]

lemma Exec.inv_code {a} :
    ∀ {e s pc r}, Exec e s pc r → s.code a ≠ [] → s.code a = r.code a := by
  apply
    @Exec.rec (λ e s pc r _ => s.code a ≠ [] → s.code a = r.code a)
  · intro e s pc s' pc' r h_step _ ih h_ne
    simp [Step.inv_code h_step] at *; apply ih h_ne
  · intros e s _ ep sp o rx sw r _ h_cr _ _ ih ih' h_ne
    have h0 : s.code = sp.code := Xinst.prep_inv_code h_cr
    have h1 : sp.code a = rx.code a := by
      apply ih; rw [← h0]; apply h_ne
    have h2 : rx.code a = sw.code a := Xinst.wrap_inv_code'' h_cr h_ne
    have h3 : sw.code a = r.code a := by
      apply ih'; rw [← h2, ← h1, ← h0]; exact h_ne
    rw [h0, h1, h2, h3]
  · intros e s pc r h_halt _; cases h_halt
    · rw [Linst.inv_code asm]
    · rfl

lemma Xinst.inv_code {e s o s' a} (h : Xinst.Run e s o s')
    (h_ne : s.code a ≠ []) : s.code a = s'.code a := by
  cases h
  · have h := Xinst.prep_inv_code asm
    rw [h, Exec.inv_code asm _, Xinst.wrap_inv_code'' asm asm]
    rw [← h]; assumption
  · have h := PreRun.code asm
    have h' := Xinst.wrap_inv_code'' asm asm
    rw [Xinst.prep_inv_code asm, h, h']
  · rw [fail_inv_code asm]

lemma Ninst.inv_code {e s i s' a} (h_run : Ninst.Run e s i s')
    (h_ne : s.code a ≠ []) : s.code a = s'.code a := by
  cases h_run
  · rw [Rinst.inv_code asm]
  · rw [Xinst.inv_code asm h_ne]
  · rw [(asm : Desc.Push _ _ _).code]

lemma Line.nil_inv {ξ : Type} {f : Desc → ξ} : Line.Inv f [] := by
  intros e s s' h; cases h; rfl

lemma Line.cons_inv {ξ : Type} {f : Desc → ξ} {i l} :
    Ninst.Inv f i → Line.Inv f l → Line.Inv f (i :: l) := by
  intros h0 h1 e s s'' h2
  rcases Line.of_run_cons h2 with ⟨s', h3, h4⟩
  apply Eq.trans (h0 h3) (h1 h4)

instance {ξ : Type} (f : Desc → ξ) (o : Rinst) [Rinst.Hinv f o] :
    Ninst.Hinv f (Ninst.reg o) := by
  constructor; intros e s s' h
  apply Rinst.Hinv.inv <| opRun_of_instRun h

instance {o : Rinst} : Rinst.Hinv Desc.bal o := ⟨Rinst.inv_bal⟩
instance {o : Rinst} : Rinst.Hinv Desc.code o := ⟨Rinst.inv_code⟩
instance {o : Rinst} : Rinst.Hinv Desc.ret o := ⟨Rinst.inv_ret⟩
instance {o : Rinst} : Rinst.Hinv Desc.dest o := ⟨Rinst.inv_dest⟩

instance {bs h_le} : Ninst.Hinv Desc.bal (Ninst.push bs h_le) := by
  constructor; intros e s s' h
  cases h with | push h => apply h.bal

instance {bs h_le} : Ninst.Hinv Desc.code (Ninst.push bs h_le) := by
  constructor; intros e s s' h
  cases h with | push h => apply h.code

instance {bs h_le} : Ninst.Hinv Desc.stor (Ninst.push bs h_le) := by
  constructor; intros e s s' h
  cases h with | push h => apply h.stor

instance {bs h_le} : Ninst.Hinv Desc.ret (Ninst.push bs h_le) := by
  constructor; intros e s s' h
  cases h with | push h => apply h.ret

instance {bs h_le} : Ninst.Hinv Desc.dest (Ninst.push bs h_le) := by
  constructor; intros e s s' h
  cases h with | push h => apply h.dest

instance {bs h_le} : Ninst.Hinv Desc.mem (Ninst.push bs h_le) := by
  constructor; intros e s s' h
  cases h with | push h => apply h.mem

syntax "show_pushB256_hinv" : tactic
macro_rules
  | `(tactic| show_pushB256_hinv) =>
    `(tactic| constructor; unfold Ninst.pushB256; apply Ninst.Hinv.inv)

instance {x} : Ninst.Hinv Desc.bal (Ninst.pushB256 x) := by
  constructor; unfold Ninst.pushB256; apply Ninst.Hinv.inv

instance {x} : Ninst.Hinv Desc.bal (Ninst.pushB256 x) := by show_pushB256_hinv
instance {x} : Ninst.Hinv Desc.code (Ninst.pushB256 x) := by show_pushB256_hinv
instance {x} : Ninst.Hinv Desc.stor (Ninst.pushB256 x) := by show_pushB256_hinv
instance {x} : Ninst.Hinv Desc.mem (Ninst.pushB256 x) := by show_pushB256_hinv
instance {x} : Ninst.Hinv Desc.ret (Ninst.pushB256 x) := by show_pushB256_hinv
instance {x} : Ninst.Hinv Desc.dest (Ninst.pushB256 x) := by show_pushB256_hinv

open Qq

def Ninst.inv_expr (ξx fx : Lean.Expr) (ix : Q(Ninst)) : Lean.Elab.Tactic.TacticM Lean.Expr := do
  let x ← Lean.Meta.synthInstance <| Lean.mkApp3 q(@Ninst.Hinv) ξx fx ix
  pure <| Lean.mkApp4 q(@Ninst.Hinv.inv) ξx fx ix x

def Linst.inv_expr (ξx fx gx : Lean.Expr) (ox : Q(Linst)) :
    Lean.Elab.Tactic.TacticM Lean.Expr := do
  let x ← Lean.Meta.synthInstance <| Lean.mkApp4 q(@Linst.Hinv) ξx fx gx ox
  pure <| Lean.mkApp5 q(@Linst.Hinv.inv) ξx fx gx ox x

def hopInv : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
  let t ← Lean.Elab.Tactic.getMainTarget
  have t' : Q(Prop) := t
  match t' with
  | ~q(@Linst.Inv $ξx $fx $gx $ox) =>
    let x ← Linst.inv_expr ξx fx gx ox
    Lean.Elab.Tactic.closeMainGoal `tacName x
  | _ => dbg_trace "Not a Linst.Inv goal"

def instInv : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
  let t ← Lean.Elab.Tactic.getMainTarget
  have t' : Q(Prop) := t
  match t' with
  | ~q(@Ninst.Inv $ξx $fx $ix) =>
    let x ← Ninst.inv_expr ξx fx ix
    Lean.Elab.Tactic.closeMainGoal `tacName x
  | _ => dbg_trace "Not a Ninst.Inv goal"

lemma Line.of_inv {ξ : Type} {e s s'} (r : _root_.Desc → ξ) {l : Line} :
  Line.Inv r l → l.Run e s s' → r s = r s' := λ h => h

def line_nil_inv : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Expr.apply <|
    Lean.Expr.const (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "Line") "nil_inv") []

def line_cons_inv : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Expr.apply <|
    Lean.Expr.const (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "Line") "cons_inv") []

partial def line_inv : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
  let t : Q(Prop) ← Lean.Elab.Tactic.getMainTarget
  match t with
  | ~q(@Line.Inv $ξx $fx $lx) =>
    let lx' : Q(Line) ← Lean.Meta.whnf lx
    match lx' with
    | ~q([]) => line_nil_inv
    | _ => line_cons_inv; instInv; line_inv
  | _ => dbg_trace "Not a Line.Inv goal"

elab "line_inv" : tactic => line_inv

lemma Func.of_inv {ξ : Type} {e s r} (f g) {p : Func} :
  @Func.Inv ξ f g p → Func.Run c e s p r → f s = g r := λ h => h

lemma branch_inv {ξ : Type} {f g} {p q}
    (h : Ninst.Inv f Ninst.pop) (hp : Func.Inv f g p) (hq : Func.Inv f g q) :
    @Func.Inv ξ f g (q <?> p) := by
  intros c e s r h_run
  rcases of_run_branch h_run
    with ⟨s', h_pop, h_run⟩ | ⟨w, s', _, h_pop, h_run⟩ <;>
  apply Eq.trans (h <| run_pop e h_pop)
  · apply hp h_run
  · apply hq h_run

lemma next_inv {ξ : Type} {f : _root_.Desc → ξ} {g} {i p}
    (h : Ninst.Inv f i) (h' : Func.Inv f g p) : Func.Inv f g (i ::: p) := by
  intros c e s r h_run
  rcases of_run_next h_run with ⟨s', hi, hp⟩
  rw [h hi, h' hp]

lemma last_inv {ξ} {f g o} (h : Linst.Inv f g o) :
    @Func.Inv ξ f g (Func.last o) := by
  intros c e s r h'; cases h'; apply h asm

lemma prepend_inv {ξ : Type} {f g} {l p} (hl : Line.Inv f l)
    (hp : Func.Inv f g p) : @Func.Inv ξ f g (l +++ p) := by
  intros c e s r h; rcases of_run_prepend _ _ h with ⟨s', hl', hp'⟩
  apply Eq.trans (hl hl') (hp hp')

def Strings.toName : List String → Lean.Name
  | [] => Lean.Name.anonymous
  | s :: ss => Lean.Name.str (Strings.toName ss) s

def Strings.toExpr (l : List String) : Lean.Expr :=
  Lean.Expr.const (Strings.toName l.reverse) []

def String.toExpr (s : String) : Lean.Expr :=
  Strings.toExpr <| String.splitOn s "."

def String.apply (s : String): Lean.Elab.Tactic.TacticM Unit :=
  Lean.Expr.apply <| String.toExpr s

lemma Func.inv_code {c e s p r a} (h : Func.Run c e s p r)
    (h_ne : s.code a ≠ []) : s.code a = r.code a := by
  induction h with
  | zero =>
    rename (_ ≠ _) → _ => ih
    have h := Desc.Rel.code asm
    rw [h , ih _]; rw [← h]; exact h_ne
  | succ =>
    rename (_ ≠ _) → _ => ih
    have h := Desc.Rel.code asm
    rw [h , ih _]; rw [← h]; exact h_ne
  | last => rw [Linst.inv_code asm]
  | next =>
    rename (_ ≠ _) → _ => ih
    have h := Ninst.inv_code asm h_ne
    rw [h, ih _]; rw [← h]; exact h_ne
  | call =>
    rename (_ ≠ _) → _ => ih
    apply ih h_ne

partial def prog_inv : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    let t : Q(Prop) ← Lean.Elab.Tactic.getMainTarget
    match t with
    | ~q(@Func.Inv $ξx $fx $gx $px) =>
      match px with
      | ~q(_ +++ _) => String.apply "prepend_inv"; line_inv; prog_inv
      | _ =>
        let px' : Q(Func) ← Lean.Meta.whnf px
        match px' with
        | ~q(Func.next _ _) => "next_inv".apply; instInv; prog_inv
        | ~q(Func.last _) =>   "last_inv".apply; hopInv
        | ~q(Func.branch _ _) => "branch_inv".apply; instInv; prog_inv; prog_inv
    | _ => dbg_trace "not a Func.Inv goal"

elab "prog_inv" : tactic => prog_inv

def sumBelow (f : Adr → B256) : Nat → Nat
  | 0 => 0
  | n + 1 => sumBelow f n + (f n.toAdr).toNat

def sumBelow_succ {f : Adr → B256} {n} :
    sumBelow f (n + 1) = sumBelow f n + (f n.toAdr).toNat := by
  delta sumBelow; rfl

def sum (f : Adr → B256) : Nat :=
  sumBelow f Adr.max.toNat.succ

def SumNof (f : Adr → B256) : Prop := sum f < 2 ^ 256

lemma le_sumBelow (f : Adr → B256) {k : Adr} {n} (h : k.toNat < n) :
    (f k).toNat ≤ sumBelow f n := by
  induction n with
  | zero => cases Nat.not_lt_zero _ h
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hk | hk
    · apply le_trans (ih hk); simp [sumBelow]
    · simp [sumBelow]
      rw [← hk, toAdr_toNat]; simp

def eq_below (n : Nat) (f g : Adr → B256) : Prop :=
  ∀ k, k.toNat < n → f k = g k

lemma sumBelow_eq_sumBelow_of_eq_below {m n} {f g : Adr → B256}
    (hm : m < 2 ^ 160) (h_le : m ≤ n) (h_eqb : eq_below n f g) :
    sumBelow f m = sumBelow g m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [sumBelow]
    have hm' : m < 2 ^ 160 := Nat.lt_of_succ_lt hm
    rw [ih hm' (Nat.le_of_succ_le h_le), h_eqb m.toAdr]
    rw [Nat.toNat_toAdr, Nat.lo_eq_of_lt hm']
    apply Nat.lt_of_succ_le h_le

lemma Adr.toNat_lt_size (a : Adr) : a.toNat < 2 ^ 160 := by
  rw [← toAdr_toNat a, Nat.toNat_toAdr];
  apply Nat.mod_lt _ (Nat.two_pow_pos _)

lemma eq_below_of_frel {k} {r} {f g : Adr → B256} (h : Frel k r f g) :
    eq_below k.toNat f g := by
  intro x hx; apply (h x).2
  intro h; rw [h] at hx; cases lt_irrefl _ hx

lemma sumBelow_sub_assoc {k : Adr} {v : B256} {n} {f g : Adr → B256}
    (dec : Decrease k v f g) (k_lt_n : k.toNat < n)
    (hv : v ≤ f k) (hn : n ≤ 2 ^ 160) :
    sumBelow f n - v.toNat = sumBelow g n := by
  induction n with
  | zero => cases Nat.not_lt_zero _ k_lt_n
  | succ n ih =>
    simp only [sumBelow];
    rw [Nat.lt_succ_iff_lt_or_eq] at k_lt_n
    rcases k_lt_n with hk | hk
    · have h_ne : k ≠ n.toAdr := by
        intro hc;
        rw [hc, Nat.toNat_toAdr, Nat.lo_eq_of_lt] at hk
        apply lt_irrefl _ hk; apply Nat.lt_of_succ_le hn
      rw [← ih hk (le_trans (Nat.le_succ _) hn), (dec n.toAdr).2 h_ne]
      rw [Nat.sub_add_comm]
      apply le_trans _ <| le_sumBelow f hk
      apply B256.toNat_le_toNat hv
    · have rw : sumBelow g n = sumBelow f n := by
        have hn' : n < 2 ^ 160 := Nat.lt_of_succ_le hn
        have hkn : n ≤ k.toNat := by rw [hk]
        have h_eq := eq_below_of_frel dec
        rw [← sumBelow_eq_sumBelow_of_eq_below hn' hkn h_eq]
      rw [rw]; clear rw
      have rw : n.toAdr = k := by rw [← hk, toAdr_toNat]
      rw [rw]; clear rw
      rw [← (dec k).1 rfl, B256.toNat_sub_eq_of_le _ _ hv]
      rw [Nat.add_sub_assoc (B256.toNat_le_toNat hv)]

lemma sum_sub_assoc {k v} {f g : Adr → B256}
    (dec : Decrease k v f g) (v_le : v ≤ f k) : sum f - v.toNat = sum g :=
  sumBelow_sub_assoc dec (Adr.toNat_lt_size k) v_le (Nat.le_refl _)

lemma le_sum {f : Adr → B256} {k} : (f k).toNat ≤ sum f :=
  le_sumBelow f (Adr.toNat_lt_size k)

lemma sumBelow_add_assoc {k v} {n} {f g : Adr → B256} (inc : Increase k v f g)
    (k_lt : k.toNat < n) (nof : B256.Nof (f k) v) (n_lt : n ≤ 2 ^ 160) :
    sumBelow f n + v.toNat = sumBelow g n := by
  induction n with
  | zero => cases Nat.not_lt_zero _ k_lt
  | succ n ih =>
    simp only [sumBelow];
    rw [Nat.lt_succ_iff_lt_or_eq] at k_lt
    rcases k_lt with hk | hk
    · have h_ne : k ≠ n.toAdr := by
        intro hc; rw [hc, Nat.toNat_toAdr, Nat.lo_eq_of_lt] at hk
        apply lt_irrefl _ hk; apply Nat.lt_of_succ_le n_lt
      rw [← ih hk (le_trans (Nat.le_succ _) n_lt), (inc n.toAdr).2 h_ne]
      omega
    · have rw : sumBelow g n = sumBelow f n := by
        have hn' : n < 2 ^ 160 := Nat.lt_of_succ_le n_lt
        have hkn : n ≤ k.toNat := by rw [hk]
        have h_eq := eq_below_of_frel inc
        rw [← sumBelow_eq_sumBelow_of_eq_below hn' hkn h_eq]
      rw [rw]; clear rw
      have rw : n.toAdr = k := by rw [← hk, toAdr_toNat]
      rw [rw]; clear rw
      rw [← (inc k).1 rfl, B256.toNat_add_eq_of_nof _ _ nof, Nat.add_assoc]

lemma sum_add_assoc {k v} {f g : Adr → B256}
    (inc : Increase k v f g) (nof : B256.Nof (f k) v) :
    sum f + v.toNat = sum g :=
  sumBelow_add_assoc inc
    (Adr.toNat_lt_size _)
    nof
    (Nat.succ_le_of_lt <| Adr.toNat_lt_size _)

lemma add_le_sumBelow (f : Adr → B256) {x y : Adr} {n}
    (x_lt : x.toNat < y.toNat) (y_lt : y.toNat < n) :
    (f x).toNat + (f y).toNat ≤ sumBelow f n := by
  induction n with
  | zero => cases Nat.not_lt_zero _ y_lt
  | succ n ih =>
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ y_lt) with y_lt' | y_eq
    · apply le_trans (ih y_lt' ); simp [sumBelow]
    · rw [sumBelow_succ, ← y_eq, toAdr_toNat]
      apply Nat.add_le_add_right
      apply le_sumBelow _ x_lt

lemma Adr.toNat_inj {x y : Adr} (h : x.toNat = y.toNat) : x = y := by
  rw [← toAdr_toNat x, ← toAdr_toNat y, h]

lemma add_le_sum_of_ne (f : Adr → B256) {x y : Adr} (ne : x ≠ y) :
    (f x).toNat + (f y).toNat ≤ sum f := by
  have hh := toAdr_toNat
  rcases Nat.lt_trichotomy x.toNat y.toNat with x_lt_y | x_eq_y | y_lt_x
  · apply add_le_sumBelow f x_lt_y (Adr.toNat_lt_size y)
  · cases ne <| Adr.toNat_inj x_eq_y
  · rw [Nat.add_comm]
    apply add_le_sumBelow f y_lt_x (Adr.toNat_lt_size x)

lemma transfer_inv_sum {kd ki v} {b d : Adr → B256}
    (hb : SumNof b) (h : Transfer b kd v ki d) : sum b = sum d := by
  rcases h with ⟨h, c, hd, hi⟩
  apply @Eq.trans _ _ (sum c + v.toNat)
  · rw [← sum_sub_assoc hd h, Nat.sub_add_cancel]
    have hh := le_sumBelow
    apply Nat.le_trans (B256.toNat_le_toNat h) le_sum
  · apply @sum_add_assoc ki
    apply frel_of_frel _ hi; intro h_eq; exact h_eq
    by_cases hk : ki = kd
    · rw [hk, ← (hd kd).left rfl]; simp only [B256.Nof]
      rw [B256.toNat_sub_eq_of_le _ _ h, Nat.sub_add_cancel (B256.toNat_le_toNat h)]
      apply B256.toNat_lt
    · rw [← (hd ki).right (Ne.symm hk)]
      apply lt_of_le_of_lt (Nat.le_trans _ <| add_le_sum_of_ne b hk) hb
      apply Nat.add_le_add_left <| B256.toNat_le_toNat h

lemma transfer_inv_nof {kd ki v} {f g : Adr → B256}
    (h : Transfer f kd v ki g) (h' : SumNof f) : SumNof g := by
  simp [SumNof]; rw [← transfer_inv_sum h' h]; apply h'

lemma of_run_dest {e s r} (h : Linst.Run e s Linst.dest r) :
    ∃ a, Transfer s.bal e.cta (s.bal e.cta) a r.bal := by
  cases h with
  | dest x bal bal' h_wup h_stk h_ow hi =>
    refine' ⟨x.toAdr, B256.le_refl _, bal, _, hi⟩
    intro a; constructor <;> intro ha
    · rw [ha, B256.sub_self, (h_ow a).left ha]
    · exact (h_ow a).right ha

lemma Linst.inv_nof {e s o r}
    (h : Linst.Run e s o r) (h_nof : SumNof s.bal) : SumNof r.bal := by
  cases o with
  | stop => cases h; exact h_nof
  | ret => cases h; exact h_nof
  | rev => cases h
  | dest =>
    rcases of_run_dest h with ⟨a, h'⟩
    exact transfer_inv_nof asm h_nof

lemma Linst.inv_sum_bal {e s o r}
    (h : Linst.Run e s o r) (h_nof : SumNof s.bal) : sum s.bal = sum r.bal := by
  cases o with
  | stop => cases h; rfl
  | ret => cases h; rfl
  | rev => cases h
  | dest =>
    rcases of_run_dest h with ⟨a, h'⟩
    exact transfer_inv_sum h_nof h'

lemma Xinst.prep_inv_nof {e s ep sp o r sw}
    (h : Xinst.Run' e s ep sp o r sw) (h_nof : SumNof s.bal) : SumNof sp.bal := by
  cases h <;> try {apply transfer_inv_nof asm h_nof} <;> {apply h_nof}

lemma Xinst.prep_inv_sum_bal {e s ep sp o r sw}
    (h : Xinst.Run' e s ep sp o r sw) (h' : SumNof s.bal) : sum s.bal = sum sp.bal := by
  cases h <;> try {apply transfer_inv_sum asm asm} <;> rfl

lemma Xinst.wrap_inv_nof {e s ep sp o r sw}
    (h : Xinst.Run' e s ep sp o r sw) (h' : SumNof r.bal) : SumNof sw.bal := by
  cases h <;> apply h'

lemma Step.inv_nof {e : Env} {s : Desc} {pc : ℕ} {s' : Desc} {pc' : ℕ}
    (h_nof : SumNof s.bal) (h_step : Step e s pc s' pc') : SumNof s'.bal := by
  cases h_step with
  | reg => rw [← Rinst.inv_bal asm]; exact h_nof
  | pre =>
    apply Xinst.wrap_inv_nof asm
    have h := PreRun.bal asm; rw [← h]
    apply Xinst.prep_inv_nof asm h_nof
  | fail => rw [← fail_inv_bal asm]; exact h_nof
  | jump => rw [← Jinst.inv_bal asm]; exact h_nof
  | push => rw [← (asm : Desc.Push _ _ _).bal]; exact h_nof

lemma Step.inv_sum_bal {e : Env} {s : Desc} {pc : ℕ} {s' : Desc} {pc' : ℕ}
    (h_nof : SumNof s.bal) (h_step : Step e s pc s' pc') : sum s.bal = sum s'.bal := by
  cases h_step with
  | reg => apply congr_arg _ <| Rinst.inv_bal asm
  | pre =>
    rw [Xinst.prep_inv_sum_bal asm h_nof]
    rw [(asm : PreRun _ _).bal, Xinst.wrap_inv_bal asm]
  | fail => rw [fail_inv_bal asm]
  | jump => rw [Jinst.inv_bal asm]
  | push => rw [(asm : Desc.Push _ _ _).bal]

lemma Exec.inv_nof :
    ∀ {e s pc r}, Exec e s pc r → SumNof s.bal → SumNof r.bal := by
  apply @Exec.rec (λ e s pc r _ => SumNof s.bal → SumNof r.bal)
  · intros e s pc s' pc' _ h_step _ ih h_nof
    apply ih <| Step.inv_nof h_nof h_step
  · intros e s _ ep sp o rx sw _ _ h_cr _ _ ih ih' h_nof
    apply ih' <| Xinst.wrap_inv_nof asm <| ih <| Xinst.prep_inv_nof asm h_nof
  · intros e s pc r h_ht h_nof
    cases h_ht
    · apply Linst.inv_nof asm h_nof
    · exact h_nof

lemma Exec.inv_sum_bal :
    ∀ {e s pc r}, Exec e s pc r → SumNof s.bal → sum s.bal = sum r.bal := by
  apply @Exec.rec (λ e s pc r _ => SumNof s.bal → sum s.bal = sum r.bal)
  · intros e s pc s' pc' r h_step _ ih h_nof
    rw [Step.inv_sum_bal h_nof h_step, ih <| Step.inv_nof h_nof h_step]
  · intros e s _ ep sp o rx sw r _ cr h_run _ ih ih' h_nof
    have h_nof' := Xinst.prep_inv_nof asm asm
    have h_nof'' := Xinst.wrap_inv_nof asm <| Exec.inv_nof h_run asm
    rw [Xinst.prep_inv_sum_bal cr h_nof, ih h_nof', Xinst.wrap_inv_bal asm, ih' asm]
  · intros e s pc r h h'; cases h
    · exact Linst.inv_sum_bal asm h'
    · rfl

lemma Xinst.inv_nof {e s o s'}
    (h : Xinst.Run e s o s') (h' : SumNof s.bal) : SumNof s'.bal := by
  cases h
  · apply Xinst.wrap_inv_nof asm <| Exec.inv_nof asm <| Xinst.prep_inv_nof asm h'
  · apply Xinst.wrap_inv_nof asm
    rw [← (asm : PreRun _ _).bal]
    apply Xinst.prep_inv_nof asm h'
  · rw [← fail_inv_bal asm]; exact h'

lemma Ninst.inv_nof {e s} :
    ∀ {i s'}, Ninst.Run e s i s' → SumNof s.bal → SumNof s'.bal := by
  apply @Ninst.Run.rec e s (λ i s' _ => SumNof s.bal → SumNof s'.bal)
  · intros o s' h; simp [Rinst.inv_bal h]
  · intros o s' h; exact Xinst.inv_nof h
  · intros bs _ s' h h'; rw [← h.bal]; exact h'

lemma Func.inv_nof {c e} :
    ∀ {s p r}, Func.Run c e s p r → SumNof s.bal → SumNof r.bal := by
  apply @Func.Run.rec c e (λ s p r _ => SumNof s.bal → SumNof r.bal)
  · intros s s' _ _ r h_pop _ ih h_nof
    rw [← Desc.Rel.bal h_pop] at ih; apply ih h_nof
  · intros s x s' _ _ r _ h_pop _ ih h_nof
    rw [← Desc.Rel.bal h_pop] at ih; apply ih h_nof
  · intros s o r h_run h_nof
    apply Linst.inv_nof h_run h_nof
  · intros s i s' _ _ h_run _ ih h_nof
    apply ih <| Ninst.inv_nof h_run h_nof
  · intro _ _ _ _ _ _; apply id

-/

def pushToB8 (bs : B8L) : B8 := 0x5F + Nat.toUInt8 bs.length
def pushToB8L (bs : B8L) : B8L := pushToB8 bs :: bs

def Xinst.toB8 : Xinst → B8
  | create   => 0xF0
  | call     => 0xF1
  | callcode => 0xF2
  | delcall  => 0xF4
  | create2  => 0xF5
  | statcall => 0xFA

def Ninst.toB8L : Ninst → B8L
  | reg o => [o.toB8]
  | exec o => [o.toB8]
  | push bs _ => pushToB8L bs

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
    let p_bts ← Func.compile l (n + i.size) p
    pure <| Ninst.toB8L i ++ p_bts
  | .branch p q => do
    let pbs ← Func.compile l (n + 4) p
    let loc := n + pbs.length + 4
    guard (loc < 2 ^ 16)
    let qbs ← Func.compile l (loc + 1) q
    pure $
      ([0x61] : B8L) ++
      [(loc >>> 8).toUInt8, loc.toUInt8] ++
      [Jinst.toB8 .jumpi] ++ pbs ++
      [Jinst.toB8 .jumpdest] ++ qbs
  | .call k => do
    let (loc, _) ← l[k]?
    guard (loc < 2 ^ 16)
    pure $
      ([0x61] : B8L) ++
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

lemma of_guard_eq_some {p : Prop} [hd : Decidable p] {ξ} {ox : Option ξ} {x} :
    (do guard p; ox) = some x → p ∧ ox = some x := by
  intro h
  cases em p with
  | inl hp => simp [hp] at h; constructor <;> assumption
  | inr hp => simp [guard, if_neg hp] at h

lemma Prog.compile_ne_nil {p} : Prog.compile p ≠ some [] := by
  simp only [Prog.compile]; intro h
  rcases of_bind_eq_some h with ⟨bs, _, h'⟩; clear h
  rcases of_bind_eq_some h' with ⟨bs', _, h⟩; clear h'; simp at h

def subcode (cd : B8L) (k : Nat) : Option B8L → Prop
  | none => False
  | some bs => List.Slice cd k bs

/-
lemma of_subcode {cd k} :
    ∀ {obs}, subcode cd k obs →
       ∃ bs, obs = some bs ∧ cd.Slice k bs
  | none, h => by cases h
  | some bs, h => ⟨bs, rfl, h⟩

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

lemma toB8_toXinst {o : Xinst} :
  B8.toXinst o.toB8 = some o := by cases o <;> rfl
lemma toB8_toJinst {o : Jinst} :
  B8.toJinst o.toB8 = some o := by cases o <;> rfl
lemma toB8_toLinst {o : Linst} :
  B8.toLinst o.toB8 = some o := by cases o <;> rfl

-/

lemma Rinst.at_unique {e pc o o'} (h : At e pc o) (h' : At e pc o') : o = o' := by
  injection Eq.trans h.symm h' with eq
  injection eq with eq; injection eq with eq

lemma Xinst.at_unique {e pc o o'} (h : At e pc o) (h' : At e pc o') : o = o' := by
  injection Eq.trans h.symm h' with eq
  injection eq with eq; injection eq with eq

lemma Jinst.at_unique {e pc o o'} (h : At e pc o) (h' : At e pc o') : o = o' := by
  injection Eq.trans h.symm h' with eq; injection eq with eq

lemma Linst.at_unique {e pc o o'} (h : At e pc o) (h' : At e pc o') : o = o' := by
  injection Eq.trans h.symm h' with eq; injection eq with eq

lemma Ninst.at_unique {e pc o o'} (h : At e pc o) (h' : At e pc o') : o = o' := by
  injection Eq.trans h.symm h' with eq; injection eq with eq

/-
lemma Nat.toUInt8_inj {a b : Nat} (a_lt : a < 2 ^ 8) (b_lt : b < 2 ^ 8)
    (eq : a.toUInt8 = b.toUInt8) : a = b := by
  rw [← @UInt8.toNat_ofNatLT _ a_lt]
  rw [← @UInt8.toNat_ofNatLT _ b_lt]
  rw [UInt8.ofNatLT_eq_ofNat, UInt8.ofNatLT_eq_ofNat]
  rw [← Nat.toUInt8_eq, ← Nat.toUInt8_eq, eq]

lemma pushAt_unique {e pc bs bs'}
    (h : PushAt e pc bs) (h' : PushAt e pc bs') : bs = bs' := by
  simp [PushAt, pushToB8L, List.slice_cons_iff] at *
  rcases h with ⟨⟨h_head, n, h_tail⟩, h_len⟩
  rcases h' with ⟨⟨h_head', n', h_tail'⟩, h_len'⟩
  have h_eq : bs.length = bs'.length := by
    have h_32 : (32 : Nat) < 2 ^ 8 := by omega
    have h_lt := Nat.lt_of_le_of_lt h_len h_32
    have h_lt' := Nat.lt_of_le_of_lt h_len' h_32
    have h_eq : bs.length.toUInt8 = bs'.length.toUInt8 := by
      have h_eq := Eq.trans h_head.symm h_head'
      simp [pushToB8] at h_eq
      apply h_eq
    apply Nat.toUInt8_inj h_lt h_lt' h_eq
  have h_rw := List.length_slice? h_tail
  have h_rw' := List.length_slice? h_tail'
  rw [h_rw, h_eq] at h_tail
  rw [h_rw'] at h_tail'
  apply Option.some_inj.mp <| .trans h_tail.symm h_tail'

lemma toInstType_toB8_swap (x : Fin 16) :
    (Rinst.swap x).toB8.toInstType = .R := by
  rcases x with ⟨n, h⟩; revert h n
  repeat (rw [Nat.forall_lt_succ_left']; refine' ⟨rfl, _⟩)
  simp

lemma toInstType_toB8_dup (x : Fin 16) :
    (Rinst.dup x).toB8.toInstType = .R := by
  rcases x with ⟨n, h⟩; revert h n
  repeat (rw [Nat.forall_lt_succ_left']; refine' ⟨rfl, _⟩)
  simp

lemma toInstType_toB8_log (x : Fin 5) :
    (Rinst.log x).toB8.toInstType = .R := by
  rcases x with ⟨n, h⟩; revert h n
  repeat (rw [Nat.forall_lt_succ_left']; refine' ⟨rfl, _⟩)
  simp

lemma Rinst.toInstType_toB8 (r : Rinst) : r.toB8.toInstType = .R := by
  cases r <;> try {rfl}
  · apply toInstType_toB8_dup
  · apply toInstType_toB8_swap
  · apply toInstType_toB8_log

lemma Linst.toInstType_toB8 (l : Linst) : l.toB8.toInstType = .L := by
  cases l <;> rfl

lemma Xinst.toInstType_toB8 (x : Xinst) : x.toB8.toInstType = .X := by
  cases x <;> rfl

lemma Jinst.toInstType_toB8 (j : Jinst) : j.toB8.toInstType = .J := by
  cases j <;> rfl

lemma toInstType_pushToB8 {bs : B8L} (h : bs.length ≤ 32) :
    (pushToB8 bs).toInstType = .P := by
  rw [← Nat.lt_succ] at h
  simp only [pushToB8]; revert h
  generalize bs.length = n; revert n
  repeat (rw [Nat.forall_lt_succ_right']; refine' ⟨_, rfl⟩)
  simp

lemma opToByte_ne_copToByte {r : Rinst} {x : Xinst} : r.toB8 ≠ x.toB8 := by
  intro h; have fs := congr_arg B8.toInstType h
  simp [Rinst.toInstType_toB8, Xinst.toInstType_toB8] at fs

lemma opToByte_ne_jopToByte {r : Rinst} {j : Jinst} : r.toB8 ≠ j.toB8 := by
  intro h; have fs := congr_arg B8.toInstType h
  simp [Rinst.toInstType_toB8, Jinst.toInstType_toB8] at fs

lemma opToByte_ne_hopToByte {r : Rinst} {l : Linst} : r.toB8 ≠ l.toB8 := by
  intro h; have fs := congr_arg B8.toInstType h
  simp [Rinst.toInstType_toB8, Linst.toInstType_toB8] at fs

lemma copToByte_ne_jopToByte {o : Xinst} {o' : Jinst} : o.toB8 ≠ o'.toB8 := by
  intro h; have fs := congr_arg B8.toInstType h
  simp [Xinst.toInstType_toB8, Jinst.toInstType_toB8] at fs

lemma jopToByte_ne_hopToByte {o : Jinst} {o' : Linst} : o.toB8 ≠ o'.toB8 := by
  intro h; have fs := congr_arg B8.toInstType h
  simp [Jinst.toInstType_toB8, Linst.toInstType_toB8] at fs

lemma copToByte_ne_hopToByte {o : Xinst} {o' : Linst} : o.toB8 ≠ o'.toB8 := by
  intro h; have fs := congr_arg B8.toInstType h
  simp [Xinst.toInstType_toB8, Linst.toInstType_toB8] at fs

lemma opToByte_ne_pushToByte {o : Rinst} {bs : B8L} (le : bs.length ≤ 32) :
    o.toB8 ≠ pushToB8 bs := by
  intro h; have fs := congr_arg B8.toInstType h
  simp [Rinst.toInstType_toB8, toInstType_pushToB8 le] at fs

lemma copToByte_ne_pushToByte {o : Xinst} {bs : B8L} (le : bs.length ≤ 32) :
    o.toB8 ≠ pushToB8 bs := by
  intro h; have fs := congr_arg B8.toInstType h
  simp [Xinst.toInstType_toB8, toInstType_pushToB8 le] at fs

lemma jopToByte_ne_pushToByte {o : Jinst} {bs : B8L} (le : bs.length ≤ 32) :
    o.toB8 ≠ pushToB8 bs := by
  intro h; have fs := congr_arg B8.toInstType h
  simp [Jinst.toInstType_toB8, toInstType_pushToB8 le] at fs

lemma hopToByte_ne_pushToByte {o : Linst} {bs : B8L} (le : bs.length ≤ 32) :
    o.toB8 ≠ pushToB8 bs := by
  intro h; have fs := congr_arg B8.toInstType h
  simp [Linst.toInstType_toB8, toInstType_pushToB8 le] at fs

lemma not_cop_at_of_op_at {e pc} {o : Rinst} {o' : Xinst} : o.At e pc → ¬ o'.At e pc := by
  intros h h'; cases opToByte_ne_copToByte <| Option.some_inj.mp <| Eq.trans h.symm h'

lemma not_jop_at_of_cop_at {e pc} {o : Xinst} {o' : Jinst} : o.At e pc → ¬ o'.At e pc := by
  intros h h'; cases copToByte_ne_jopToByte <| Option.some_inj.mp <| Eq.trans h.symm h'

lemma not_jop_at_of_op_at {e pc} {o : Rinst} {o' : Jinst} : o.At e pc → ¬ o'.At e pc := by
  intros h h'; cases opToByte_ne_jopToByte <| Option.some_inj.mp <| Eq.trans h.symm h'

lemma not_hop_at_of_op_at {e pc} {o : Rinst} {o' : Linst} : o.At e pc → ¬ o'.At e pc := by
  intros h h'; cases opToByte_ne_hopToByte <| Option.some_inj.mp <| Eq.trans h.symm h'

lemma not_hop_at_of_cop_at {e pc} {o : Xinst} {o' : Linst} : o.At e pc → ¬ o'.At e pc := by
  intros h h'; cases copToByte_ne_hopToByte <| Option.some_inj.mp <| Eq.trans h.symm h'

lemma not_hop_at_of_jop_at {e pc} {o : Jinst} {o' : Linst} : o.At e pc → ¬ o'.At e pc := by
  intros h h'; cases jopToByte_ne_hopToByte <| Option.some_inj.mp <| Eq.trans h.symm h'

lemma not_pushAt_of_op_at {e pc} {o : Rinst} {bs : B8L} :
    o.At e pc → ¬ PushAt e pc bs := by
  intros h h'
  cases opToByte_ne_pushToByte h'.right <| Option.some_inj.mp
     <| .trans h.symm <| List.get?_eq_of_slice h'.left

lemma not_pushAt_of_cop_at {e pc} {o : Xinst} {bs : B8L} :
    o.At e pc → ¬ PushAt e pc bs := by
  intros h h'
  cases copToByte_ne_pushToByte h'.right <| Option.some_inj.mp
     <| .trans h.symm <| List.get?_eq_of_slice h'.left

lemma not_pushAt_of_jop_at {e pc} {o : Jinst} {bs : B8L} :
    o.At e pc → ¬ PushAt e pc bs := by
  intros h h'
  cases jopToByte_ne_pushToByte h'.right <| Option.some_inj.mp
     <| .trans h.symm <| List.get?_eq_of_slice h'.left

lemma not_pushAt_of_hop_at {e pc} {o : Linst} {bs : B8L} : o.At e pc → ¬ PushAt e pc bs := by
  intros h h'
  cases hopToByte_ne_pushToByte h'.right <| Option.some_inj.mp
     <| .trans h.symm <| List.get?_eq_of_slice h'.left

lemma Linst.run_of_at {e s pc o r} (cr : Exec e s pc r) (h_at : Linst.At e pc o) :
    Linst.Run e s o r := by
  cases cr with
  | step =>
    rename Step _ _ _ _ _ => h_step; cases h_step
    · cases not_hop_at_of_op_at asm h_at
    · cases not_hop_at_of_cop_at asm h_at
    · cases not_hop_at_of_cop_at asm h_at
    · cases not_hop_at_of_jop_at asm h_at
    · cases not_pushAt_of_hop_at h_at asm
  | exec => cases not_hop_at_of_cop_at asm h_at
  | halt =>
    rename Halt _ _ _ _ => h_halt; cases h_halt
    · rw [Linst.at_unique h_at asm]; assumption
    · simp [Linst.At] at h_at

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

lemma Desc.push_cons_pop_cons
    {x y} {xs ys} {s s' s''}
    (h : Desc.Push (x :: xs) s s')
    (h' : Desc.Pop (y :: ys) s' s'') :
    (x = y ∧ ∃ st, Desc.Push xs s st ∧ Desc.Pop ys st s'') := by
  rcases h with ⟨_, _, _, h, _, _, _⟩
  rcases h' with ⟨_, _, _, h', _, _, _⟩
  rcases Stack.push_cons_pop_cons h h' with ⟨h_eq, stk, h_push, h_pop⟩
  refine' ⟨
    h_eq,
    ⟨_, _, _, stk, _, _, _⟩,
    ⟨_, _, _, h_push, _, _, _⟩,
    ⟨_, _, _, h_pop,  _, _, _⟩
   ⟩ <;> try {assumption}

lemma Desc.pop_nil {s s'} (h : Desc.Pop [] s s') : s = s' := by
  match s, s', h with
  | ⟨_, _, _, _, _, _, _⟩,
    ⟨_, _, _, _, _, _, _⟩,
    ⟨_, _, _, h, _, _, _⟩ =>
    simp [Rels.dft] at *
    refine' ⟨_, _, _, h, _, _, _⟩ <;> assumption

lemma Desc.push_nil {s s'} (h : Desc.Push [] s s') : s = s' := by
  match s, s', h with
  | ⟨_, _, _, _, _, _, _⟩,
    ⟨_, _, _, _, _, _, _⟩,
    ⟨_, _, _, h, _, _, _⟩ =>
    simp [Stack.Push, Split, Rels.dft] at *
    refine' ⟨_, _, _, h.symm, _, _, _⟩ <;> assumption

lemma Ninst.at_iff_slice {e pc} {i : Ninst} :
    i.At e pc ↔ List.Slice e.code pc i.toB8L := by
  cases i with
  | reg => simp [At, Rinst.At, toB8L, List.slice_iff_get?_eq]
  | exec => simp [At, Xinst.At, toB8L, List.slice_iff_get?_eq]
  | push bs h => simp [At, PushAt, toB8L, h, and_true]

lemma subcode_compile_call {e l m n}
  (h : subcode e.code m (Func.compile l m (Func.call n))) :
    ∃ (loc : Nat) (p : Func),
      l[n]? = some (loc, p) ∧
      loc < 2 ^ 16 ∧
      --PushAt e m (B16.toB8L (Nat.toUInt16 loc)) ∧
      PushAt e m ([(loc >>> 8).toUInt8, loc.toUInt8]) ∧
      Jinst.jump.At e (m + 3) := by
  rcases of_subcode h with ⟨cd, h', h_slice⟩; clear h
  rcases of_bind_eq_some h' with ⟨⟨loc, p⟩, h_get, h⟩; clear h'
  simp at h
  rcases of_guard_eq_some h with ⟨h_lt, h_eq⟩; clear h
  refine' ⟨loc, p, h_get, h_lt, _⟩
  simp at h_eq; rw [← h_eq] at h_slice
  simp only [PushAt, pushToB8L, pushToB8]
  simp only [List.length]
  refine' ⟨⟨List.slice_prefix h_slice, by omega⟩, _⟩
  simp only [Jinst.At]
  have hh := @List.slice_suffix _ _ m [_, _, _] _ h_slice
  simp at hh
  rw [List.slice_iff_get?_eq] at hh
  apply hh

-/



lemma toXinst_toB8 {o : Xinst} :
  B8.toXinst o.toB8 = some o := by cases o <;> rfl
lemma toJinst_toB8 {o : Jinst} :
  B8.toJinst o.toB8 = some o := by cases o <;> rfl
lemma toLinst_toB8 {o : Linst} :
  B8.toLinst o.toB8 = some o := by cases o <;> rfl

lemma toInstType_pushToB8 {bs : B8L} (h : bs.length ≤ 32) :
    (pushToB8 bs).toInstType = .P := by
  rw [← Nat.lt_succ] at h
  simp only [pushToB8]; revert h
  generalize bs.length = n; revert n
  repeat (rw [Nat.forall_lt_succ_right']; refine' ⟨_, rfl⟩)
  simp only [Nat.not_lt_zero, Nat.toUInt8_eq, IsEmpty.forall_iff, implies_true]


lemma toInstType_toB8_swap (x : Fin 16) :
    (Rinst.swap x).toB8.toInstType = .R := by
  rcases x with ⟨n, h⟩; revert h n
  repeat (rw [Nat.forall_lt_succ_left']; refine' ⟨rfl, _⟩)
  simp

lemma toInstType_toB8_dup (x : Fin 16) :
    (Rinst.dup x).toB8.toInstType = .R := by
  rcases x with ⟨n, h⟩; revert h n
  repeat (rw [Nat.forall_lt_succ_left']; refine' ⟨rfl, _⟩)
  simp

lemma toInstType_toB8_log (x : Fin 5) :
    (Rinst.log x).toB8.toInstType = .R := by
  rcases x with ⟨n, h⟩; revert h n
  repeat (rw [Nat.forall_lt_succ_left']; refine' ⟨rfl, _⟩)
  simp

lemma Rinst.toInstType_toB8 (r : Rinst) : r.toB8.toInstType = .R := by
  cases r <;> try {rfl}
  · apply toInstType_toB8_dup
  · apply toInstType_toB8_swap
  · apply toInstType_toB8_log

lemma Linst.toInstType_toB8 (l : Linst) : l.toB8.toInstType = .L := by
  cases l <;> rfl

lemma Xinst.toInstType_toB8 (x : Xinst) : x.toB8.toInstType = .X := by
  cases x <;> rfl

lemma Jinst.toInstType_toB8 (j : Jinst) : j.toB8.toInstType = .J := by
  cases j <;> rfl

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

lemma ByteArray.lt_size_of_getElem?_eq_some {xs : ByteArray} {n} {x}
    (eq : xs.toList[n]? = some x) : n < xs.size := by
  simp only [ByteArray.size, Array.size]
  rcases List.getElem?_eq_some_iff.mp eq with ⟨lt, _⟩
  rw [ByteArray.toList_eq_toList_data] at lt; exact lt

lemma Jinst.at_of_slice {code : ByteArray} {pc : Nat} {j : Jinst} {xs : B8L}
    (slice : code.toList.Slice pc (j.toB8 :: xs)) :
    j.At code pc := by
  have eq := List.get?_eq_of_slice slice
  simp only [Jinst.At, ByteArray.getInst]
  have rw := ByteArray.of_getElem?_eq_some eq
  rw [if_pos (ByteArray.lt_size_of_getElem?_eq_some eq)]
  split <;>
  try { rename (B8.toInstType _ = _) => h
        rw [rw, Jinst.toInstType_toB8] at h; cases h }
  rw [rw, toJinst_toB8]; rfl

lemma Linst.at_of_slice {code : ByteArray} {pc : Nat} {l : Linst} {xs : B8L}
    (slice : code.toList.Slice pc (l.toB8 :: xs)) :
    l.At code pc := by
  have eq := List.get?_eq_of_slice slice
  simp only [Linst.At, ByteArray.getInst]
  have rw := ByteArray.of_getElem?_eq_some eq
  rw [if_pos (ByteArray.lt_size_of_getElem?_eq_some eq)]
  split <;>
  try { rename (B8.toInstType _ = _) => h
        rw [rw, Linst.toInstType_toB8] at h; cases h }
  rw [rw, toLinst_toB8]; rfl

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

lemma Linst.run_of_at {pc sevm devm l exn}
    (cr : Exec pc sevm devm exn)
    (h_at : Linst.At sevm.code pc l) :
    Linst.Run sevm devm l exn := by
    sorry

def PushAt (code : ByteArray) (pc : Nat) (xs : B8L) : Prop :=
  ∃ le : xs.length ≤ 32, code.getInst pc = some (.next (.push xs le))

lemma toB8_toXinst {o : Xinst} : B8.toXinst o.toB8 = some o := by cases o <;> rfl
lemma toB8_toJinst {o : Jinst} : B8.toJinst o.toB8 = some o := by cases o <;> rfl
lemma toB8_toLinst {o : Linst} : B8.toLinst o.toB8 = some o := by cases o <;> rfl

lemma Ninst.push_ext {xs ys : B8L}
    (le : xs.length ≤ 32) (le' : ys.length ≤ 32) (eq : xs = ys) :
    Ninst.push xs le = Ninst.push ys le' := by
  revert le le'; rw [eq]; simp

lemma toNat_pushToB8_eq {xs : B8L} (le : xs.length ≤ 32) :
    (pushToB8 xs).toNat = xs.length + 95:= by
  simp only [pushToB8]; rw [B8.toNat_add, Nat.lo_eq_of_lt] <;>
  {simp only [B8.toNat, UInt8.reduceToNat, UInt8.toNat_ofNat']; omega}

lemma toNat_pushToB8_le {bs : B8L} (le : bs.length ≤ 32) :
    (pushToB8 bs).toNat ≤ 127 := by
  rw [toNat_pushToB8_eq le]; omega

lemma List.sliceD_succ {ξ} (xs : List ξ) (m n : Nat) (d : ξ) :
    xs.sliceD m (n + 1) d = xs.getD m d :: xs.sliceD (m + 1) n d := by
  cases m <;> cases xs <;> simp [List.sliceD, takeD, List.getD, List.drop]

lemma ByteArray.get!_eq_getElem!_toList
    (xs : ByteArray) (i : Nat) : xs.get! i = xs.toList[i]! := by
  simp only [ByteArray.get!]
  rw [List.getElem!_eq_getElem?_getD, Array.getElem!_eq_getD]
  rw [Array.getD_eq_getD_getElem?, ByteArray.toList_eq_toList_data]
  rcases Nat.lt_or_ge i xs.data.size with lt | ge
  · rw [Array.getElem?_eq_getElem lt, List.getElem?_eq_getElem lt]; rfl
  · rw [Array.getElem?_eq_none ge, List.getElem?_eq_none ge]

lemma List.getD_eq_getElem!_of_lt_length {ξ} [Inhabited ξ]
    {xs : List ξ} {i : Nat} {d : ξ} : i < xs.length → xs.getD i d = xs[i]! := by
  intro lt; rw [List.getD_eq_getElem?_getD, List.getElem!_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem lt]; rfl

lemma ByteArray.size_eq_length_toList (xs : ByteArray) :
    xs.size = xs.toList.length := by
  simp only [ByteArray.size, Array.size]
  rw [ByteArray.toList_eq_toList_data]


lemma List.getD_eq_default {ξ} {xs : List ξ} {i : Nat} {d : ξ}
    (le : xs.length ≤ i) : xs.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr le]; rfl

lemma ByteArray.sliceD_eq_replicate (xs : ByteArray) (m n : Nat) (d : B8)
    (le : xs.size ≤ m) : ByteArray.sliceD xs m n d = List.replicate n d := by
  induction n generalizing xs m
  case zero => rfl
  case succ n ih =>
    simp only [ByteArray.sliceD];
    rw [if_neg]; rw [not_lt]; exact le

lemma ByteArray.sliceD_eq (xs : ByteArray) (m n : Nat) (d : B8) :
    ByteArray.sliceD xs m n d = xs.toList.sliceD m n d := by
  induction n generalizing xs m
  case zero => rfl
  case succ n ih =>
    simp only [ByteArray.sliceD]; split
    · rename (_ < _) => lt
      have lt' : m < xs.toList.length := by
        simp only [ByteArray.size] at lt
        rw [ Array.size_eq_length_toList,
             ← ByteArray.toList_eq_toList_data ] at lt
        apply lt
      rw [List.sliceD_succ, ih]
      rw [ByteArray.get!_eq_getElem!_toList]
      rw [List.getD_eq_getElem!_of_lt_length lt']
    · rename (¬ _ < _) => nlt
      rw [not_lt] at nlt
      simp only [List.replicate]
      rw [List.sliceD_succ]
      apply congr_arg₂
      · rw [ByteArray.size_eq_length_toList] at nlt
        rw [List.getD_eq_default nlt]
      · rw [← ih]; rw [ByteArray.sliceD_eq_replicate]; omega

lemma List.drop_eq_of_drop?_eq_some {ξ} {xs ys : List ξ} {m : Nat} :
    xs.drop? m = some ys → xs.drop m = ys := by
  induction m generalizing xs ys
  case zero => simp [List.drop?]
  case succ m ih => cases xs <;> simp [List.drop?]; apply ih

lemma List.takeD_eq_of_take?_eq_some {ξ} {xs ys : List ξ} {m : Nat} {d} :
    xs.take? m = some ys → xs.takeD m d = ys := by
  induction m generalizing xs ys
  case zero => simp [List.take?]
  case succ m ih =>
    cases xs <;> simp [List.take?]
    intro _ eq eq'; cases ys; {cases eq'}
    cases eq'; simp [ih eq]

lemma List.sliceD_eq_of_slice?_eq_some {ξ} {xs ys : List ξ} {m n : Nat} {d} :
    xs.slice? m n = some ys → xs.sliceD m n d = ys := by
  intro eq; simp only [List.slice?] at eq; simp only [List.sliceD]
  rcases of_bind_eq_some eq with ⟨zs, rw, rw'⟩
  rw [drop_eq_of_drop?_eq_some rw, takeD_eq_of_take?_eq_some rw']
lemma pushAt_of_slice {code : ByteArray} {pc} {xs : B8L} (le : xs.length ≤ 32)
    (slice : code.toList.Slice pc (pushToB8L xs)) : PushAt code pc xs := by
  have eq := List.get?_eq_of_slice slice
  have rw := ByteArray.of_getElem?_eq_some eq
  simp only [PushAt, ByteArray.getInst]
  refine' ⟨le, _⟩
  rw [if_pos (ByteArray.lt_size_of_getElem?_eq_some eq)]
  split <;>
  try { rename (B8.toInstType _ = _) => h
        rw [rw, toInstType_pushToB8 le] at h; cases h }
  apply congr_arg; apply congr_arg; apply Ninst.push_ext
  rcases slice with ⟨len, slice⟩
  have rw' : B8.toNat (code.get! pc) - 95 = xs.length := by
    rw [rw, toNat_pushToB8_eq le]; omega
  rw [rw', ByteArray.sliceD_eq]; simp [pushToB8L] at slice
  rw [List.length_slice? slice, List.length_cons] at slice
  apply List.sliceD_eq_of_slice?_eq_some (List.slice?_eq_cons_iff.mp slice).2

lemma Ninst.at_of_slice {code : ByteArray} {pc : Nat} {n : Ninst}
    (slice : code.toList.Slice pc n.toB8L) : n.At code pc := by
  cases n
  case reg r =>
    simp [Ninst.toB8L] at slice
    have eq := List.get?_eq_of_slice slice
    simp only [Ninst.At, ByteArray.getInst]
    have rw := ByteArray.of_getElem?_eq_some eq
    rw [if_pos (ByteArray.lt_size_of_getElem?_eq_some eq)]
    split <;>
    try { rename (B8.toInstType _ = _) => h
          rw [rw, Rinst.toInstType_toB8] at h; cases h }
    rw [rw, toB8_toRinst]; rfl
  case exec x =>
    simp [Ninst.toB8L] at slice
    have eq := List.get?_eq_of_slice slice
    simp only [Ninst.At, ByteArray.getInst]
    have rw := ByteArray.of_getElem?_eq_some eq
    rw [if_pos (ByteArray.lt_size_of_getElem?_eq_some eq)]
    split <;>
    try { rename (B8.toInstType _ = _) => h
          rw [rw, Xinst.toInstType_toB8] at h; cases h }
    rw [rw, toB8_toXinst]; rfl
  case push xs le => apply (pushAt_of_slice le slice).2

lemma two_le_32 : (2 : Nat) ≤ 32 := by omega

lemma of_subcode {cd k} :
    ∀ {obs}, subcode cd k obs →
       ∃ bs, obs = some bs ∧ cd.Slice k bs
  | none, h => by cases h
  | some bs, h => ⟨bs, rfl, h⟩

lemma subcode_compile_branch {code : ByteArray} {k l p q}
  (h : subcode code.toList k (Func.compile l k (Func.branch p q))) :
    ∃ loc : Nat,
      loc < 2 ^ 16 ∧
      Ninst.At code k (.push [(loc >>> 8).toUInt8, loc.toUInt8] two_le_32) ∧
      Jinst.jumpi.At code (k + 3) ∧
      subcode code.toList (k + 4) (Func.compile l (k + 4) p) ∧
      Jinst.jumpdest.At code loc ∧
      subcode code.toList (loc + 1) (Func.compile l (loc + 1) q) := by
  rcases of_subcode h with ⟨cd, h', h_slice⟩; clear h
  rcases of_bind_eq_some h' with ⟨qcd, h_qcd, h⟩; clear h'
  rcases of_guard_eq_some h with ⟨h_loc, h'⟩; clear h
  rcases of_bind_eq_some h' with ⟨pcd, h_pcd, h⟩; clear h'
  rw [← of_pure_eq_some h] at h_slice; clear h cd; rename' h_slice => h
  rw [List.append_assoc, List.append_assoc, List.append_assoc] at h
  let loc : Nat := k + qcd.length + 4
  refine' ⟨loc, h_loc, _⟩
  have pat : At code k (push [(loc >>> 8).toUInt8, loc.toUInt8] two_le_32) := by
    apply @Ninst.at_of_slice code k
    simp only [loc, Ninst.toB8L, pushToB8L, pushToB8]
    apply List.slice_prefix h
  refine' ⟨pat, _⟩; clear pat
  have h' := List.slice_suffix h; clear h
  rw [← List.singleton_append] at h'
  have jat : Jinst.At code (k + 3) Jinst.jumpi := by
    simp [Nat.toUInt8, List.length] at h'
    apply Jinst.at_of_slice (List.slice_prefix h')
  refine' ⟨jat, _⟩; clear jat
  have h := List.slice_suffix h'; clear h'
  rw [Nat.add_assoc] at h; simp [List.length] at h; rw [h_qcd]
  refine' ⟨List.slice_prefix h, _⟩
  have h' := List.slice_suffix h; clear h
  have h_rw : k + 4 + List.length qcd = k + List.length qcd + 4 := by omega
  rw [h_rw, ← List.singleton_append] at h'; simp [loc]; rw [h_pcd]
  refine' ⟨Jinst.at_of_slice (List.slice_prefix h'), List.slice_suffix h'⟩










lemma Prog.get?_table {m n} {c : List Func} :
    (Prod.snd <$> (table m c)[n]? : Option Func) =
      ((@getElem? (List Func) Nat Func _ _ c n) : Option Func) := by
  induction c generalizing m n with
  | nil => rfl
  | cons p c' ih =>
    cases n with
    | zero => simp [table]
    | succ n => simp [table]; apply ih

-- alternative version of Exec which rolls all arguments into a structure.

structure Exec' : Type where
  (pc : Nat)
  (sevm : Sevm)
  (devm : Devm)
  (exn : Execution)
  (exc : Exec pc sevm devm exn)

inductive Exec'.Prec : Exec' → Exec' → Prop
  | none {pc : Nat} {sevm : Sevm} {devm : Devm} {n : Ninst}
    {devm' : Devm} {exn : Execution}
    (nat : n.At sevm.code pc)
    (run : Ninst.Run' pc sevm devm n .none (.ok devm'))
    (exc : Exec (pc + n.size) sevm devm' exn) :
    Exec'.Prec
      ⟨pc + n.size, sevm, devm', exn, exc⟩
      ⟨pc, sevm, devm, exn, .nextNoneRec nat run exc⟩
  | fst
    {pc : Nat} {sevm : Sevm} {devm : Devm} {n : Ninst}
    {pc_ : Nat} {sevm_ : Sevm} {devm_ : Devm} {exn_ : Execution}
    {devm' : Devm}
    {devm'' : Devm}
    (nat : n.At sevm.code pc)
    ( run :
      Ninst.Run' pc sevm devm n
        (.some (⟨pc_, sevm_, devm_⟩, exn_))
        (.ok devm') )
    (exc_ : Exec pc_ sevm_ devm_ exn_)
    (exc : Exec (pc + n.size) sevm devm' (.ok devm'')) :
    Exec'.Prec
      ⟨pc_, sevm_, devm_, exn_, exc_⟩
      ⟨pc, sevm, devm, .ok devm'', .nextSomeRec nat run exc_ exc⟩
  | snd {pc : Nat} {sevm : Sevm} {devm : Devm} {n : Ninst}
    {pc_ : Nat} {sevm_ : Sevm} {devm_ : Devm} {exn_ : Execution}
    {devm' : Devm}
    --{pc'' : Nat}
    {devm'' : Devm}
    (nat : n.At sevm.code pc)
    ( run :
      Ninst.Run' pc sevm devm n
        (.some (⟨pc_, sevm_, devm_⟩, exn_))
        (.ok devm') )
    (exc_ : Exec pc_ sevm_ devm_ exn_)
    (exc : Exec (pc + n.size) sevm devm' (.ok devm'')) :
    Exec'.Prec
      ⟨pc + n.size, sevm, devm', .ok devm'', exc⟩
      ⟨pc, sevm, devm, .ok devm'', .nextSomeRec nat run exc_ exc⟩
  | jump {pc : Nat} {sevm : Sevm} {devm : Devm} {j : Jinst}
    {pc'} {devm' devm'' : Devm}
    (jat : j.At sevm.code pc)
    (run : Jinst.Run ⟨pc, sevm, devm⟩ j (.ok ⟨pc', devm'⟩))
    (exc : Exec pc' sevm devm' (.ok devm'')) :
    Exec'.Prec
      ⟨pc', sevm, devm', .ok devm'', exc⟩
      ⟨pc, sevm, devm, .ok devm'', .jumpRec jat run exc⟩

infix:70 " ≺ " => Exec'.Prec

inductive Exec'.le : Exec' → Exec' → Prop
  | refl : ∀ p, Exec'.le p p
  | step : ∀ {p p' p''}, Exec'.le p p' → p' ≺ p'' → Exec'.le p p''

def Exec'.lt (pk pk'' : Exec') : Prop :=
  ∃ pk' : Exec', Exec'.le pk pk' ∧ Exec'.Prec pk' pk''

lemma Exec'.lt_of_prec {pk pk' : Exec'} (h : pk ≺ pk') : lt pk pk' :=
  ⟨pk, .refl _, h⟩

abbrev Exec'.gt (pk pk' : Exec') : Prop := Exec'.lt pk' pk

lemma Exec'.eq_or_lt_of_le :
  ∀ {p p'}, Exec'.le p p' → p = p' ∨ Exec'.lt p p' := by
  intros p p'' h0; rcases h0 with _ | ⟨le, prec⟩
  · left; rfl
  · right; refine ⟨_, le, prec⟩

lemma Exec'.acc_of_le {pk pk' : Exec'}
    (h_le : Exec'.le pk pk') (h_acc : Acc Exec'.lt pk') : Acc Exec'.lt pk := by
  cases Exec'.eq_or_lt_of_le h_le with
  | inl h => rw [h]; exact h_acc
  | inr h => exact Acc.inv h_acc h

theorem Exec'.lt.well_founded : WellFounded Exec'.lt := by
  constructor;
  intro pk; rcases pk with ⟨_, _, _, _, _⟩
  apply
    @Exec.rec
      (λ pc sevm devm exn exc => Acc Exec'.lt ⟨pc, sevm, devm, exn, exc⟩) <;>
    clear *-
  · intros _ _ _ _; constructor
    intro _ lt; rcases lt with ⟨_, _, ⟨_⟩⟩
  · intro _ _ _ _ _ _ _ _; constructor
    intro _ lt; rcases lt with ⟨_, _, ⟨_⟩⟩
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _
    constructor; intro _ lt
    rcases lt with ⟨_, _, ⟨_⟩⟩
  · intro _ _ _ _ _ _ _ _ _ acc
    constructor; intro _ lt
    rcases lt with ⟨_, le, ⟨_⟩⟩
    exact acc_of_le le acc
  · intro pc sevm devm n pc_ sevm_ devm_ exn_ devm' exn nat run exc_ exc ih ih'
    constructor; intro exc' lt
    rcases lt with ⟨exc'', le, prec⟩
    cases prec
    · apply acc_of_le le ih
    · apply acc_of_le le ih'
  · intro _ _ _ _ _ _ _ _
    constructor; intro _ lt
    rcases lt with ⟨_, _, ⟨_⟩⟩
  · intro pc sevm devm j pc' evm' exn jat run exc ih
    constructor; intro exc' lt
    rcases lt with ⟨exc'', le, prec⟩
    cases prec; apply acc_of_le le ih
  · intro _ _ _ _ _ _ _
    constructor; intro _ lt
    rcases lt with ⟨_, _, ⟨_⟩⟩

abbrev Exec'.Pred : Type := Exec' → Prop

def Exec'.imp (π π' : Exec'.Pred) : Exec'.Pred := λ pk => π pk → π' pk

infix:70 " →p " => Exec'.imp

def Exec'.Fa (π : Exec'.Pred) : Prop := ∀ pk, π pk

notation "□p" => Exec'.Fa

def carryover (π : Exec'.Pred) : Exec'.Pred :=
(λ pk => □p (Exec'.gt pk →p π)) →p π

def Exec'.strongRec (π : Exec'.Pred) : □p (carryover π) → □p π := by
  intro ih pk
  apply @WellFounded.induction _ Exec'.lt Exec'.lt.well_founded π pk
  clear pk; intro pk ih'
  apply ih
  intro pk' h_gt
  apply ih' _ h_gt

def Ninst.of_run'_reg {pc : Nat} {sevm : Sevm} {devm : Devm}
    {r : Rinst} {xl : Xlot} {ex : Execution}
  (run : Ninst.Run' pc sevm devm (.reg r) xl ex) :
  (Rinst.run ⟨pc, sevm, devm⟩ r) = ex := run

--
-- #check Xinst.run
-- def Xinst.of_run'_reg {pc : Nat} {sevm : Sevm} {devm : Devm}
--     {x : Xinst} {xl : Xlot} {ex : Except (String × Devm) (Nat × Devm)}
--   (run : Ninst.Run' pc sevm devm (.exec x) xl ex) :
--   (Xinst.run false sevm devm x).withPc (pc + 1) = ex := run
--
-- #exit
lemma of_withPc_eq_ok {pc : ℕ} {exn : Execution} {pc'} {devm}
    (eq : exn.withPc pc = .ok ⟨pc', devm⟩) : exn = .ok devm ∧ pc = pc' := by
  rcases of_bind_eq_ok eq with ⟨devm', exn_eq, eq'⟩; clear eq
  injection eq' with eq; injection eq with eq rw
  rw [← rw]; refine ⟨exn_eq, eq⟩

lemma Rinst.run_of_at {pc sevm pre r post}
    (exc : Exec pc sevm pre (.ok post)) (rat : Rinst.At sevm.code pc r) :
    ∃ (inter : Devm) (exc' : Exec (pc + 1) sevm inter (.ok post)),
      Rinst.run ⟨pc, sevm, pre⟩ r = .ok inter ∧
      ⟨pc + 1, sevm, inter, .ok post, exc'⟩ ≺
        ⟨pc, sevm, pre, .ok post, exc⟩ := by
  cases exc
  case nextNoneRec n inter nat run exc =>
    have n_eq : n = .reg r := by
      injection Eq.trans nat.symm rat with eq; injection eq
    cases n_eq; refine' ⟨inter, exc, Ninst.of_run'_reg run, _⟩
    apply @Exec'.Prec.none _ _ _ (reg r)
  case nextSomeRec n pc_ sevm_ devm_ exn_ inter exc_ nat run exc =>
    have n_eq : n = .reg r := by
      injection Eq.trans nat.symm rat with eq; injection eq
    cases n_eq; refine' ⟨inter, exc, Ninst.of_run'_reg run, _⟩
    apply @Exec'.Prec.snd _ _ _ (.reg r)

  case jumpRec jat _ _ =>
    injection Eq.trans jat.symm rat with eq; injection eq
  case last _ lat _ =>
    injection Eq.trans lat.symm rat with eq; injection eq

--lemma Ninst.pc_eq_of_run {pc} {sevm} {devm} {n} {xl} {pc'} {devm'}
--    (run : Ninst.Run' pc sevm devm n xl (.ok ⟨pc', devm'⟩)) :
--    pc' = pc + n.toB8L.length := by
--  cases n
--  case reg r =>
--    rw [← (of_withPc_eq_ok run).2]; rfl
--  case exec x =>
--    rcases run with ⟨exn, _, run⟩
--    rw [← (of_withPc_eq_ok run).2]; rfl
--  case push xs le =>
--    rcases of_bind_eq_ok run with ⟨_, _, eq⟩
--    rw [← (of_withPc_eq_ok eq).2]; rfl

lemma Ninst.run_of_at {pc sevm pre n post}
    (exc : Exec pc sevm pre (.ok post))
    (nat : Ninst.At sevm.code pc n) :
    ∃ (inter : Devm)
      (exc' : Exec (pc + n.size) sevm inter (.ok post)),
      Ninst.Run sevm pre n inter ∧
      Exec'.Prec
        ⟨(pc + n.size), sevm, inter, .ok post, exc'⟩
        ⟨pc, sevm, pre, .ok post, exc⟩ := by
  cases exc
  case nextNoneRec n' inter nat' run exc =>

    -- cases Ninst.at_unique nat' nat
    -- rw [Ninst.pc_eq_of_run run] at exc
    -- refine' ⟨inter, exc, ⟨.none, .intro, pc, pc', run⟩, _⟩
    -- have hh := @Exec'.Prec.none pc sevm pre n pc' inter (.ok post) nat run
    sorry
    -- have n_eq : n = .reg r := by
    --   injection Eq.trans nat.symm rat with eq; injection eq
    -- have conj :
    --   Ninst.run false {pc := pc, sta := sevm, dyna := pre} n = .ok ⟨pc', inter⟩ ∧
    --   pc + 1 = pc' := by
    --   rw [n_eq] at run; apply of_withPc_eq_ok (Ninst.of_run'_reg run)
    -- rw [conj.2]; refine' ⟨inter, exc, conj.1, _⟩
    -- apply Exec'.Prec.none
  case nextSomeRec n pc_ sevm_ devm_ exn_ inter exc_ nat run exc =>
    -- have n_eq : n = .reg r := by
    --   injection Eq.trans nat.symm rat with eq; injection eq
    -- have conj :
    --   Rinst.run {pc := pc, sta := sevm, dyna := pre} r = .ok inter ∧
    --   pc + 1 = pc' := by
    --   rw [n_eq] at run; apply of_withPc_eq_ok (Ninst.of_run'_reg run)
    -- rw [conj.2]; refine' ⟨inter, exc, conj.1, _⟩
    -- apply Exec'.Prec.snd
    sorry
  case jumpRec jat _ _ =>
    -- injection Eq.trans jat.symm rat with eq; injection eq
    sorry
  case last _ lat _ =>
    -- injection Eq.trans lat.symm rat with eq; injection eq
    sorry


-- lemma Xinst.run_of_at {pc sevm pre x post}
--     (exc : Exec pc sevm pre (.ok post)) (xat : Xinst.At sevm.code pc x) :
--     ∃ (inter : Devm) (exc' : Exec (pc + 1) sevm inter (.ok post)),
--       Rinst.run ⟨pc, sevm, pre⟩ r = .ok inter ∧
--       ⟨pc + 1, sevm, inter, .ok post, exc'⟩ ≺
--         ⟨pc, sevm, pre, .ok post, exc⟩ := by
--
--     ∃ (inter : Desc) (cr' : Exec e s' (pc + 1) r),
--       Xinst.Run e s o s' ∧
--       Exec'.Rel ⟨e, s', pc + 1, r, cr'⟩ ⟨e, s, pc, r, cr⟩ := by

/-

lemma Xinst.run_of_at {e s pc o r}
    (cr : Exec e s pc r) (h_at : Xinst.At e pc o) :
    ∃ (s' : Desc) (cr' : Exec e s' (pc + 1) r),
      Xinst.Run e s o s' ∧
      Exec'.Rel ⟨e, s', pc + 1, r, cr'⟩ ⟨e, s, pc, r, cr⟩ := by
  cases cr with
  | step =>
    rename Desc => s'; refine' ⟨s', _⟩
    have h_prec := Exec'.Rel.step asm asm
    cases (asm : Step _ _ _ _ _)
    · cases not_cop_at_of_op_at asm h_at
    · rw [Xinst.at_unique h_at asm]
      refine ⟨_, Xinst.Run.pre asm asm asm, h_prec⟩
    · rw [Xinst.at_unique h_at asm]
      refine ⟨asm, Xinst.Run.fail asm, h_prec⟩
    · cases not_jop_at_of_cop_at h_at asm
    · cases not_pushAt_of_cop_at h_at asm
  | exec =>
    cases Xinst.at_unique h_at (asm : Xinst.At _ _ _)
    have h_prec := Exec'.Rel.snd asm asm asm asm
    refine' ⟨_, _, Xinst.Run.exec asm asm, h_prec⟩
  | halt =>
    rename Halt _ _ _ _ => h_halt; cases h_halt
    · cases not_hop_at_of_cop_at h_at asm
    · cases List.get?_length_ne_some h_at

lemma push_of_pushAt {e s pc bs r} (cr : Exec e s pc r) (h_at :PushAt e pc bs) :
    ∃ (s' : Desc) (cr' : Exec e s' (pc + bs.length + 1) r),
      Desc.Push [B8L.toB256 bs] s s' ∧
      Exec'.Rel ⟨e, s', pc + bs.length + 1, r, cr'⟩ ⟨e, s, pc, r, cr⟩ := by
  cases cr with
  | step =>
    rename Desc => s'; refine' ⟨s', _⟩
    have h_prec := Exec'.Rel.step asm asm
    rename Step _ _ _ _ _ => h_step; cases h_step
    · cases not_pushAt_of_op_at  asm h_at
    · cases not_pushAt_of_cop_at asm h_at
    · cases not_pushAt_of_cop_at asm h_at
    · cases not_pushAt_of_jop_at asm h_at
    · rename (PushAt e pc _) => h_at'
      cases pushAt_unique h_at h_at'
      refine' ⟨_, asm, h_prec⟩
  | exec =>
    cases not_pushAt_of_cop_at asm h_at
  | halt =>
    rename Halt _ _ _ _ => h_halt; cases h_halt
    · cases not_pushAt_of_hop_at asm h_at
    · cases List.not_slice_length h_at.left

lemma length_pushToB8L {bs} : (pushToB8L bs).length = bs.length + 1 := by
  simp [pushToB8L]

lemma Ninst.run_of_at {e s pc i r}
    (cr : Exec e s pc r) (h_at : Ninst.At e pc i) :
    ∃ (s' : Desc) (cr' : Exec e s' (pc + i.toB8L.length) r),
      Ninst.Run e s i s' ∧
      Exec'.Rel ⟨e, s', pc + i.toB8L.length, r, cr'⟩ ⟨e, s, pc,r, cr⟩ := by
  cases i with
  | reg o =>
    rcases Rinst.run_of_at cr h_at with ⟨s', cr', h_run, h_prec⟩
    refine' ⟨s', cr', .reg h_run, h_prec⟩
  | exec o =>
    rcases Xinst.run_of_at cr h_at with ⟨s', cr', h_run, h_prec⟩
    refine' ⟨s', cr', .exec h_run, h_prec⟩
  | push bs h =>
    rcases push_of_pushAt cr h_at with ⟨s', cr', h_push, h_prec⟩
    simp [toB8L]; rw [length_pushToB8L, ← Nat.add_assoc]
    refine' ⟨s', _, _, h_prec⟩; exact Ninst.Run.push _ h_push
    -/

-- lemma Jinst.run_of_at {e s pc o r}
--     (cr : Exec e s pc r) (h_at : Jinst.At e pc o) :
--     ∃ (s' : Desc) (pc' : Nat), ∃ (cr' : Exec e s' pc' r),
--       Jinst.Run e s pc o s' pc' ∧
--       Exec'.Rel ⟨e, s', pc', r, cr'⟩ ⟨e, s, pc, r, cr⟩ := by
lemma Jinst.run_of_at {pc sevm pre j post}
    (exc : Exec pc sevm pre (.ok post)) (jat : Jinst.At sevm.code pc j) :
    ∃ (pc' : Nat) (inter : Devm), ∃ (exc' : Exec pc' sevm inter (.ok post)),
      Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩) ∧
      ⟨pc', sevm, inter, .ok post, exc'⟩ ≺ ⟨pc, sevm, pre, .ok post, exc⟩ := by
  cases exc
  case nextNoneRec eq _ _ =>
    injection Eq.trans jat.symm eq with eq; injection eq
  case nextSomeRec eq _ _ =>
    injection Eq.trans jat.symm eq with eq; injection eq
  case jumpRec j' pc' inter jat' run exc' =>
    injection Eq.trans jat.symm jat' with eq; injection eq with rw
    rw [← rw] at run
    refine' ⟨pc', inter, exc', run, Exec'.Prec.jump _ _ _⟩
  case last eq _ =>
    injection Eq.trans jat.symm eq with eq; injection eq


/-

lemma jump_at {e s pc r} (cr : Exec e s pc r) (h : Jinst.At e pc Jinst.jump) :
    ∃ (x : B256) (s' : Desc) (cr' : Exec e s' x.toNat r),
      Desc.Pop [x] s s' ∧
      Jumpable e x.toNat ∧
      Exec'.Rel ⟨e, s', x.toNat, r, cr'⟩ ⟨e, s, pc, r, cr⟩ := by
  rcases Jinst.run_of_at cr h with ⟨s', pc', cr', h_run, h_prec⟩
  cases h_run; refine ⟨_, _, cr', asm, asm, h_prec⟩

lemma jumpi_at {e s pc r} (cr : Exec e s pc r) (h : Jinst.At e pc Jinst.jumpi) :
    ( ∃ (x : B256) (s' : Desc) (cr' : Exec e s' (pc + 1) r),
        Desc.Pop [x, 0] s s' ∧
        Exec'.Rel ⟨e, s', pc + 1, r, cr'⟩ ⟨e, s, pc, r, cr⟩ ) ∨
    ( ∃ (x y : B256) (s' : Desc) (cr' : Exec e s' x.toNat r),
        Desc.Pop [x, y] s s' ∧
        Jumpable e x.toNat ∧ y ≠ 0 ∧
        Exec'.Rel ⟨e, s', x.toNat, r, cr'⟩ ⟨e, s, pc, r, cr⟩ ) := by
  rcases Jinst.run_of_at cr h with ⟨s', pc', cr', h_run, h_prec⟩
  cases h_run
  · left; refine ⟨_, _, asm, asm, h_prec⟩
  · right; refine ⟨_, _, _, asm, asm, asm, asm, h_prec⟩

lemma jumpdest_at {e s pc r} (cr : Exec e s pc r) (h : Jinst.At e pc Jinst.jumpdest) :
    ∃ cr' : Exec e s (pc + 1) r,
      Exec'.Rel ⟨e, s, pc + 1, r, cr'⟩ ⟨e, s, pc, r, cr⟩ := by
  rcases Jinst.run_of_at cr h with ⟨s', pc', cr', h_run, h_prec⟩
  cases h_run; refine ⟨_, h_prec⟩

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

lemma subcode_of_get?_eq_some {f fs} {e : Env} {k loc : ℕ} {p : Func}
    (h_eq : some e.code = Prog.compile ⟨f, fs⟩)
    (h_get : getElem? (table 0 (f :: fs)) k = some ⟨loc, p⟩) :
    Jinst.At e loc Jinst.jumpdest ∧
    subcode e.code (loc + 1) (Func.compile (table 0 (f :: fs)) (loc + 1) p) := by
  rcases of_get?_table_eq_some h_eq h_get with
    ⟨lft, rgt, _, _, pfx, sfx, h_pfx, h_split', h_sfx⟩
  unfold Jinst.At
  rcases Table.compile_cons_eq_some h_sfx.symm with ⟨bs, bs', h_bs, _, h_sfx'⟩
  have h_slice : List.Slice e.code loc sfx := by
    rw [← h_pfx, h_split']; apply List.append_slice_suffix
  rw [h_sfx', List.append_assoc] at h_slice
  constructor
  · rw [← List.slice_iff_get?_eq]
    apply List.slice_prefix h_slice
  · rw [h_bs]; simp [subcode]
    apply List.slice_prefix <| List.slice_suffix h_slice

lemma toUInt16_toNat {x : UInt16} : Nat.toUInt16 x.toNat = x :=
  UInt16.ofNat_toNat

lemma toUInt8_toUInt16 (n : Nat) : n.toUInt16.toUInt8 = n.toUInt8 :=
  UInt16.toUInt8_ofNat' _

-- def B16.toB32 (x : B16) : B32 := UInt16.toUInt32 x
-- def B32.toB64 (x : B32) : B64 := UInt32.toUInt64 x

def B16.concat (x y : B16) : B32 :=
  x.toB32 <<< 16 ||| y.toB32

def B32.concat (x y : B32) : B64 :=
  x.toB64 <<< 32 ||| y.toB64

lemma Nat.toB64_eq (n : Nat) : n.toB64 = n.toUInt64 := rfl

lemma B64.toNat_eq (x : B64) : x.toNat = UInt64.toNat x := rfl

lemma Nat.lo_eq (m n : Nat) : m ↾ n = m % (2 ^ n) := rfl
lemma Nat.hi_eq (m n : Nat) : m ↿ n = (m >>> n) <<< n := rfl

lemma B32.ofNat_eq_iff_mod_eq_toNat (a : Nat) (b : B32) :
    a.toB32 = b ↔ a ↾ 32 = b.toNat :=
  UInt32.ofNat_eq_iff_mod_eq_toNat a b

lemma Nat.toB16_toB8 (n : Nat) : n.toB8.toB16 = (n ↾ 8).toB16 := by
  have h0 : n.toB8.toB16 = n.toB16 % (2 ^ 8) :=
      (UInt8.toUInt16_eq_mod_256_iff n.toUInt8 n.toUInt16).mpr
        (UInt16.toUInt8_ofNat' _).symm
  have h1: (n.toB16 % 2 ^ 8).toNat = n ↾ 8 := by
    have rw : B16.toNat (2 ^ 8) = 2 ^ 8 := rfl
    rw [B16.toNat_mod, rw]; clear rw
    rw [toNat_toB16, ← Nat.lo_eq]
    apply Nat.lo_lo_of_ge (by omega)
  have h2 : (n ↾ 8).toB16 = n.toB16 % (2 ^ 8) := by
    apply (UInt16.ofNat_eq_iff_mod_eq_toNat _ _).mpr
    apply Eq.trans (Nat.lo_lo_of_le (by omega)) h1.symm
  apply Eq.trans h0 h2.symm

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

lemma B64.toNat_shl (a b : B64) :
    (a <<< b).toNat = (a.toNat <<< (b.toNat % 64)) ↾ 64 :=
  UInt64.toNat_shiftLeft a b

lemma B32.toNat_shl (a b : B32) :
    (a <<< b).toNat = a.toNat <<< (b.toNat % 32) ↾ 32 :=
  UInt32.toNat_shiftLeft a b

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

lemma toNat_toB128_of_lt {n : Nat} (h : n < 2 ^ 128) : n.toB128.toNat = n := by
  rw [toNat_toB128, Nat.lo_eq_of_lt h]

lemma toNat_toB256_of_lt {n : Nat} (h : n < 2 ^ 256) : n.toB256.toNat = n := by
  rw [toNat_toB256, Nat.lo_eq_of_lt h]
-/




-- lemma Ninst.run_of_at {e s pc i r}
--     (cr : Exec e s pc r) (h_at : Ninst.At e pc i) :
--     ∃ (s' : Desc) (cr' : Exec e s' (pc + i.toB8L.length) r),
--       Ninst.Run e s i s' ∧
--       Exec'.Rel ⟨e, s', pc + i.toB8L.length, r, cr'⟩ ⟨e, s, pc,r, cr⟩ := by
--   cases i with
--   | reg o =>
--     rcases Rinst.run_of_at cr h_at with ⟨s', cr', h_run, h_prec⟩
--     refine' ⟨s', cr', .reg h_run, h_prec⟩
--   | exec o =>
--     rcases push_of_pushAt cr h_at with ⟨s', cr', h_push, h_prec⟩
--     simp [toB8L]; rw [length_pushToB8L, ← Nat.add_assoc]
--     refine' ⟨s', _, _, h_prec⟩; exact Ninst.Run.push _ h_push

lemma Ninst.size_eq_length_toB8L (n : Ninst) :
    n.size = n.toB8L.length := by sorry

lemma Except.bind_associative
  --{m : Type u → Type v} --{inst✝ : Monad m} [self : LawfulMonad m]
  {ξ υ ζ ω}
  (x : Except ξ υ)
  (f : υ → Except ξ ζ)
  (g : ζ → Except ξ ω) :
  x >>= f >>= g = x >>= fun x ↦ f x >>= g := by
  apply bind_assoc

def Devm.Pop (xs : List B256): Devm → Devm → Prop :=
  Rel {Rels.eq with stack := Stack.Pop xs}

def Devm.PushBurn (xs : List B256): Devm → Devm → Prop :=
  Rel {Devm.Rels.eq with stack := _root_.Stack.Push xs, gasLeft := (· ≥ ·)}

lemma Devm.pushBurn_of_run {x : B256} {pre inter : Devm} {cost : Nat} :
    (chargeGas cost pre >>= fun d => d.push x) = .ok inter →
    Devm.PushBurn [x] pre inter := by
  intro run
  simp only [bind, Except.bind] at run
  split at run; {cases run}
  rename_i d h_charge
  simp only [chargeGas] at h_charge
  split at h_charge
  · cases h_charge
  · rename_i gas h_safe
    injection h_charge with eq_d; subst eq_d
    unfold safeSub at h_safe
    split at h_safe
    · injection h_safe with eq_gas; subst eq_gas
      simp only [Devm.push, Except.assert, bind, Except.bind] at run
      split at run; {cases run}
      injection run with eq_inter; subst eq_inter
      constructor <;> simp [_root_.Stack.Push, Split, Devm.Rels.eq]
    · contradiction

lemma Devm.pop_of_pop {x : B256} {devm devm' : Devm} :
    Devm.pop devm = .ok ⟨x, devm'⟩ → Devm.Pop [x] devm devm' := by
  intro pop
  simp only [Devm.pop] at pop
  split at pop; {cases pop}
  injection pop with eq; injection eq with eq eq'
  constructor <;> simp <;> rw [← eq'] <;> try {rfl}
  rename (devm.stack = _) => rw; rw [rw, eq]; rfl

lemma Devm.burn_of_chargeGas {cost : Nat} {devm devm' : Devm} :
    chargeGas cost devm = .ok devm' → Devm.Burn devm devm' := by
  intro eq
  simp only [chargeGas] at eq
  cases h : safeSub devm.gasLeft cost with
  | none =>
    rw [h] at eq
    cases eq
  | some gas =>
    rw [h] at eq
    injection eq with eq'
    rw [← eq']
    constructor <;> try {rfl}
    revert h
    unfold safeSub
    split
    · intro h
      injection h with h
      simp
      omega
    · intro h
      cases h

lemma Devm.pop_append {xs ys : List B256} {devm devm' devm'' : Devm} :
    Devm.Pop xs devm devm' →
    Devm.Pop ys devm' devm'' →
    Devm.Pop (xs ++ ys) devm devm'' := by
  rintro ⟨_⟩; rename Stack.Pop _ _ _ => pop1
  rintro ⟨_⟩; rename Stack.Pop _ _ _ => pop2
  constructor <;> try {exact Eq.trans asm asm} -- h2_mem
  exact append_split pop1 pop2

lemma Except.of_assert_eq_ok {p : Prop} [inst : Decidable p] {ξ : Type u}
    {x : ξ} {u : Unit} (eq : Except.assert p x = .ok u) : p := by
  by_cases h : p
  · assumption
  · simp [h, assert] at eq

lemma Devm.popBurn_of_pop_of_burn
    {xs devm devm' devm''}
    (pop : Devm.Pop xs devm devm')
    (burn : Devm.Burn devm' devm'') :
    Devm.PopBurn xs devm devm'' := by
  constructor
  · exact burn.stack ▸ pop.stack
  · exact Eq.trans pop.memory burn.memory
  · rw [pop.gasLeft]; exact burn.gasLeft
  · exact Eq.trans pop.logs burn.logs
  · exact Eq.trans pop.refundCounter burn.refundCounter
  · exact Eq.trans pop.output burn.output
  · exact Eq.trans pop.accountsToDelete burn.accountsToDelete
  · exact Eq.trans pop.returnData burn.returnData
  · exact Eq.trans pop.error burn.error
  · exact Eq.trans pop.accessedAddresses burn.accessedAddresses
  · exact Eq.trans pop.accessedStorageKeys burn.accessedStorageKeys
  · exact Eq.trans pop.state burn.state
  · exact Eq.trans pop.transientStorage burn.transientStorage

lemma of_jumpi_run {pc sevm pre pc' inter}
    ( run :
      Jinst.Run
        {pc := pc, sta := sevm, dyna := pre}
        .jumpi (.ok ⟨pc', inter⟩) ) :
    ( ∃ (x : B256) ,
        pc' = pc + 1 ∧
        Devm.PopBurn [x, 0] pre inter ) ∨
    ( ∃ (x y : B256),
        pc' = x.toNat ∧
        Devm.PopBurn [x, y] pre inter ∧
        jumpable sevm.code x.toNat = true ∧
        y ≠ 0 ) := by
  rcases of_bind_eq_ok run with ⟨⟨x, devm1⟩, eq1, run'⟩; clear run
  rcases of_bind_eq_ok run' with ⟨⟨y, devm2⟩, eq2, run⟩; clear run'
  rcases of_bind_eq_ok run with ⟨devm3, eq3, run'⟩; clear run
  split at run'
  · left;
    injection run' with eq; injection eq
    iterate 3 (rename_i eq; cases eq)
    refine' ⟨x, rfl, _⟩
    have pop1 := Devm.pop_of_pop eq1; clear eq1
    have pop2 := Devm.pop_of_pop eq2; clear eq2
    have pop := Devm.pop_append pop1 pop2; clear pop1 pop2
    have burn := Devm.burn_of_chargeGas eq3; clear eq3
    exact Devm.popBurn_of_pop_of_burn pop burn
  · right
    rcases of_bind_eq_ok run' with ⟨u, eq4, run⟩; clear run'
    injection run with eq; injection eq
    iterate 2 (rename_i eq; cases eq)
    refine' ⟨x, y, rfl, _, Except.of_assert_eq_ok eq4, asm⟩
    have pop1 := Devm.pop_of_pop eq1; clear eq1
    have pop2 := Devm.pop_of_pop eq2; clear eq2
    have pop := Devm.pop_append pop1 pop2; clear pop1 pop2
    have burn := Devm.burn_of_chargeGas eq3; clear eq3
    exact Devm.popBurn_of_pop_of_burn pop burn

lemma jumpi_at {pc sevm pre post}
    (exc : Exec pc sevm pre (.ok post))
    (jat : Jinst.At sevm.code pc .jumpi) :
    ( ∃ (x : B256) (inter : Devm)
        (exc' : Exec (pc + 1) sevm inter (.ok post)),
        Devm.PopBurn [x, 0] pre inter ∧
        ⟨pc + 1, sevm, inter, .ok post, exc'⟩ ≺
        ⟨pc, sevm, pre, .ok post, exc⟩ ) ∨
    ( ∃ (x y : B256) (inter : Devm)
        (exc' : Exec x.toNat sevm inter (.ok post)),
        Devm.PopBurn [x, y] pre inter ∧
        jumpable sevm.code x.toNat = true ∧ y ≠ 0 ∧
        ⟨x.toNat, sevm, inter, .ok post, exc'⟩ ≺
          ⟨pc, sevm, pre, .ok post, exc⟩ ) := by
  rcases Jinst.run_of_at exc jat
    with ⟨pc', inter, exc', run, prec⟩
  rcases of_jumpi_run run with
      ⟨x, pc_eq, pb⟩
    | ⟨x, y, pc_eq, pb, jumpable_eq, ne_zero⟩
  · left; cases pc_eq; refine' ⟨x, inter, exc', pb, prec⟩
  · right; cases pc_eq;
    refine' ⟨x, y, inter, exc', pb, jumpable_eq, ne_zero, prec⟩

-- lemma jumpi_at {e s pc r}
--     (cr : Exec e s pc r) (h : Jinst.At e pc Jinst.jumpi) :
--     ( ∃ (x : B256) (s' : Desc) (cr' : Exec e s' (pc + 1) r),
--         Desc.Pop [x, 0] s s' ∧
--         Exec'.Rel ⟨e, s', pc + 1, r, cr'⟩ ⟨e, s, pc, r, cr⟩ ) ∨
--     ( ∃ (x y : B256) (s' : Desc) (cr' : Exec e s' x.toNat r),
--         Desc.Pop [x, y] s s' ∧
--         Jumpable e x.toNat ∧ y ≠ 0 ∧
--         Exec'.Rel ⟨e, s', x.toNat, r, cr'⟩ ⟨e, s, pc, r, cr⟩ ) := by
--   rcases Jinst.run_of_at cr h with ⟨s', pc', cr', h_run, h_prec⟩
--   cases h_run
--   · left; refine ⟨_, _, asm, asm, h_prec⟩
--   · right; refine ⟨_, _, _, asm, asm, asm, asm, h_prec⟩

lemma Exec'.of_exn_eq_ok {pk : Exec'} {devm : Devm}
    (eq : pk.exn = .ok devm) :
    pk = (
      {
        pc := pk.pc,
        sevm := pk.sevm,
        devm := pk.devm,
        exn := .ok devm,
        exc := eq ▸ pk.exc
      } : Exec'
    ) := by
  cases pk; simp at *; apply eq

#check Ninst.at_of_slice
#check PushAt

lemma push_of_pushAt
    {pc sevm pre xs post} (exc : Exec pc sevm pre (.ok post))
    (h_at : PushAt sevm.code pc xs) :
    ∃ (inter : Devm) (exc' : Exec (pc + xs.length + 1) sevm inter (.ok post)),
      Devm.PushBurn [B8L.toB256 xs] pre inter ∧
      ⟨pc + xs.length + 1, sevm, inter, .ok post, exc'⟩ ≺
        ⟨pc, sevm, pre, .ok post, exc⟩ := by
  rcases h_at with ⟨le, h_at⟩
  cases exc
  case nextNoneRec n inter nat run exc =>
    injection Eq.trans nat.symm h_at with eq; injection eq with eq
    cases eq
    refine' ⟨inter, exc, _, .none nat run exc⟩
    exact Devm.pushBurn_of_run run
  case nextSomeRec n pc_ sevm_ devm_ exn_ inter exc_ nat run exc =>
    injection Eq.trans nat.symm h_at with eq; injection eq with eq
    cases eq
    refine' ⟨inter, exc, _, .snd nat run exc_ exc⟩
    exact Devm.pushBurn_of_run run
  case jumpRec j pc' inter jat run exc' =>
    injection Eq.trans jat.symm h_at with eq; injection eq
  case last l lat run =>
    injection Eq.trans lat.symm h_at with eq; injection eq

def Func.Run' (fs : List Func) (sevm : Sevm) (devm : Devm) (f : Func) : Execution → Prop
  | .error _ => True
  | .ok devm' => Func.Run fs sevm devm f devm'

lemma Nat.lo_eq (m n : Nat) : m ↾ n = m % (2 ^ n) := rfl
lemma Nat.hi_eq (m n : Nat) : m ↿ n = (m >>> n) <<< n := rfl

lemma pair_aux (n m : Nat) :
    ((n >>> m ↾ m) ↾ (m + m)) <<< m ↾ (m + m) ||| (n ↾ m) ↾ (m + m) =
      n ↾ (m + m) := by
  rw [Nat.lo_lo_of_le (by omega)]
  rw [Nat.lo_lo_of_le (by omega)]
  apply Eq.trans _ <| high_or_low_eq_self (n ↾ (m + m)) m Nat.lo_lt
  apply congr_arg₂  _ _ (Nat.lo_lo_of_ge (by omega)).symm
  rw [@Nat.lo_add_shr n m m, ← Nat.lo_eq _ m, Nat.lo_lo]; rfl

lemma Nat.toB16_toB8 (n : Nat) : n.toB8.toB16 = (n ↾ 8).toB16 := by
  have h0 : n.toB8.toB16 = n.toB16 % (2 ^ 8) :=
      (UInt8.toUInt16_eq_mod_256_iff n.toUInt8 n.toUInt16).mpr
        (UInt16.toUInt8_ofNat' _).symm
  have h1: (n.toB16 % 2 ^ 8).toNat = n ↾ 8 := by
    have rw : B16.toNat (2 ^ 8) = 2 ^ 8 := rfl
    rw [B16.toNat_mod, rw]; clear rw
    rw [toNat_toB16, ← Nat.lo_eq]
    apply Nat.lo_lo_of_ge (by omega)
  have h2 : (n ↾ 8).toB16 = n.toB16 % (2 ^ 8) := by
    apply (UInt16.ofNat_eq_iff_mod_eq_toNat _ _).mpr
    apply Eq.trans (Nat.lo_lo_of_le (by omega)) h1.symm
  apply Eq.trans h0 h2.symm

lemma List.toB16_pair (n : Nat) :
    B8L.toB16 [(n >>> 8).toB8, n.toB8] = n.toB16 := by
  have h : (n >>> 8 ↾ 8).toB16 <<< 8 ||| (n ↾ 8).toB16 = n.toB16 := by
    rw [← B16.toNat_inj, toNat_toB16, B16.toNat_or, toNat_toB16]
    rw [B16.toNat_shiftLeft, toNat_toB16]; apply pair_aux n 8
  simp [B8L.toB16, B8L.pack, ekatD, takeD, reverse, reverseAux, tail, headD]
  rw [Nat.toB16_toB8, Nat.toB16_toB8, h]

def B16.concat (x y : B16) : B32 :=
  x.toB32 <<< 16 ||| y.toB32

lemma B32.ofNat_eq_iff_mod_eq_toNat (a : Nat) (b : B32) :
    a.toB32 = b ↔ a ↾ 32 = b.toNat :=
  UInt32.ofNat_eq_iff_mod_eq_toNat a b

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

lemma B32.toNat_shl (a b : B32) :
    (a <<< b).toNat = a.toNat <<< (b.toNat % 32) ↾ 32 :=
  UInt32.toNat_shiftLeft a b

lemma B64.toNat_shl (a b : B64) :
    (a <<< b).toNat = (a.toNat <<< (b.toNat % 64)) ↾ 64 :=
  UInt64.toNat_shiftLeft a b

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

lemma List.toB32_pair (n : Nat) (n_lt : n < 2 ^ 16) :
    B8L.toB32 [(n >>> 8).toB8, n.toB8] = n.toB32 := by
  simp only [ B8L.toB32, B8L.pack, ekatD, takeD,
    reverse, reverseAux, tail, headD, take, drop ]
  apply Eq.trans _ (toB32_eq_concat _).symm
  apply congr_arg₂ _ _ (congr_arg _ _)
  · apply congr_arg (λ x : B32 => x <<< 16) <| congr_arg _ _
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_of_lt (by omega)]; rfl
  · apply List.toB16_pair

def B32.concat (x y : B32) : B64 :=
  x.toB64 <<< 32 ||| y.toB64

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

lemma Devm.pushBurn_cons_popBurn_cons
    {x y} {xs ys} {s s' s''}
    (h : Devm.PushBurn (x :: xs) s s')
    (h' : Devm.PopBurn (y :: ys) s' s'') :
    (x = y ∧ ∃ st, Devm.PushBurn xs s st ∧ Devm.PopBurn ys st s'') := by
  rcases h with ⟨h_stack, h_mem, h_gas, h_logs, h_refund, h_out, h_del, h_ret, h_err, h_acc, h_keys, h_state, h_trans⟩
  rcases h' with ⟨h'_stack, h'_mem, h'_gas, h'_logs, h'_refund, h'_out, h'_del, h'_ret, h'_err, h'_acc, h'_keys, h'_state, h'_trans⟩
  have push_pop_stack := Stack.push_cons_pop_cons h_stack h'_stack
  rcases push_pop_stack with ⟨h_eq, stk, h_push, h_pop⟩
  refine' ⟨
    h_eq,
    { s' with stack := stk },
    ⟨h_push, h_mem, h_gas, h_logs, h_refund, h_out, h_del, h_ret, h_err, h_acc, h_keys, h_state, h_trans⟩,
    ⟨h_pop, h'_mem, h'_gas, h'_logs, h'_refund, h'_out, h'_del, h'_ret, h'_err, h'_acc, h'_keys, h'_state, h'_trans⟩
  ⟩

lemma Devm.burn_of_popBurn_nil {s s'} (h : Devm.PopBurn [] s s') :
    Devm.Burn s s' := by
  match s, s', h with
  | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _⟩,
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _⟩,
    ⟨h, _, _, _, _, _, _, _, _, _, _, _, _⟩ =>
    refine' ⟨h, _, _, _, _, _, _, _, _, _, _, _, _⟩ <;> assumption

lemma Devm.burn_of_pushBurn_nil {s s'} (h : Devm.PushBurn [] s s') :
    Devm.Burn s s' := by
  match s, s', h with
  | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _⟩,
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _⟩,
    ⟨h, _, _, _, _, _, _, _, _, _, _, _, _⟩ =>
    refine' ⟨h.symm, _, _, _, _, _, _, _, _, _, _, _, _⟩ <;> assumption

lemma Devm.popBurn_of_burn_of_popBurn {devm devm' devm''} {xs}
    (burn : Devm.Burn devm devm')
    (popBurn : Devm.PopBurn xs devm' devm'') :
    Devm.PopBurn xs devm devm'' := by
  sorry

theorem correct_core (f : Func) (fs : List Func) :
    ∀ (pk : Exec') (p : Func),
      some pk.sevm.code.toList = Prog.compile ⟨f, fs⟩ →
      subcode pk.sevm.code.toList pk.pc (Func.compile (table 0 (f :: fs)) pk.pc p) →
      Func.Run' (f :: fs) pk.sevm pk.devm p pk.exn := by
  apply Exec'.strongRec; intro pk ih p h_eq sub
  rcases pk with ⟨pc, sevm, pre, exn, exc⟩
  simp only
  rcases exn with _ | post; {constructor}
  match p with
  | .last l =>
    exact Func.Run.last <| Linst.run_of_at exc <| Linst.at_of_slice sub
  | .next n p =>
    rcases of_subcode sub with ⟨cd, h_eq', h_slice⟩;
    rcases of_bind_eq_some h_eq' with ⟨cd', h_eq'', h_rw⟩; clear h_eq'
    simp [pure] at h_rw;
    rw [← h_rw] at h_slice;
    clear h_rw cd
    have h_at : Ninst.At sevm.code pc n := by
      apply Ninst.at_of_slice
      apply List.slice_prefix h_slice
    have bar' :
      ∃ inter exc',
        Run sevm pre n inter ∧
        ⟨pc + n.size, sevm, inter, .ok post, exc'⟩ ≺ ⟨pc, sevm, pre, .ok post, exc⟩ := by
      have bar := @Ninst.run_of_at pc sevm pre n post
      apply bar exc h_at
    rcases bar' with ⟨inter, exc', h_run, h_prec⟩
    apply @Func.Run.next (f :: fs) sevm pre n inter p post h_run
    have quz :
      subcode sevm.code.toList (pc + n.size)
        (Func.compile (table 0 (f :: fs)) (pc + n.size) p) := by
      rw [h_eq'']
      simp only [subcode]
      rw [Ninst.size_eq_length_toB8L]
      apply List.slice_suffix h_slice
    apply
      ih ⟨pc + n.size, sevm, inter, .ok post, exc'⟩
        (Exec'.lt_of_prec h_prec)
        p
        h_eq
        quz
  | .branch p q =>
    rcases subcode_compile_branch sub with
      ⟨loc, h_loc, pushAt, h_jumpi, h_scp, h_jumpdest, h_scq⟩

    have h :
        ∃ (devm' : Devm) (exc' : Exec (pc  + 3) sevm devm' (.ok post)),
          Devm.PushBurn [Nat.toB256 loc] pre devm' ∧
          ⟨pc + 3, sevm, devm', .ok post, exc'⟩ ≺ ⟨pc, sevm, pre, .ok post, exc⟩ := by
      simp at pushAt
      rcases push_of_pushAt exc ⟨_, pushAt⟩ with ⟨s', cr', h, h_prec⟩
      rw [List.toB256_pair _ h_loc] at h
      refine' ⟨s', cr', h, h_prec⟩

    rcases h with ⟨devm', exc', pushBurn, h_prec⟩


    rcases jumpi_at exc' h_jumpi with
        ⟨x, devm'', exc'', popBurn, prec⟩
      | ⟨x, y, devm'', exc'', popBurn, jumpable, ne, prec⟩ <;> clear h_jumpi
    · clear h_scq h_jumpdest
      have h_pop' : Devm.PopBurn [0] pre devm'' := by
        rcases (Devm.pushBurn_cons_popBurn_cons pushBurn popBurn).right
          with ⟨st, pushBurn', popBurn'⟩
        have hh := Devm.burn_of_pushBurn_nil pushBurn'




        sorry
      apply Func.Run.zero h_pop'
      have h_lt :
          Exec'.lt
            ⟨pc + 4, sevm, devm'', .ok post, exc''⟩
            ⟨pc, sevm, pre, .ok post, exc⟩ := by
        refine' ⟨_, _, h_prec⟩;
        apply Exec'.le.step _ prec
        apply Exec'.le.refl _
      apply ih ⟨pc + 4, sevm, devm'', .ok post, exc''⟩ h_lt p h_eq h_scp
    · clear ih
      have h_loc' : loc < 2 ^ 256 := by
        apply Nat.lt_trans h_loc
        rw [Nat.pow_lt_pow_iff_right] <;> omega
      have h : x.toNat = loc ∧ Devm.PopBurn [y] pre devm'' := by
        sorry
      rcases h with ⟨hx, popBurn'⟩
      have run : Func.Run (f :: fs) sevm devm'' q post := by sorry
      apply Func.Run.succ ne popBurn' run
  | .call k =>
    sorry




  #exit



      --apply Linst.run_of_at pk.exc <| Linst.at_of_slice sub




    --  rw [← eq_post]; apply Linst.run_of_at pk.exc <| Linst.at_of_slice sub
    --apply Func.Run.last run




-- theorem correct_core (f : Func) (fs : List Func) :
--     ∀ (pk : Exec') (post : Devm) (p : Func),
--       some pk.sevm.code.toList = Prog.compile ⟨f, fs⟩ →
--       subcode pk.sevm.code.toList pk.pc (Func.compile (table 0 (f :: fs)) pk.pc p) →
--       pk.exn = .ok post →
--       Func.Run (f :: fs) pk.sevm pk.devm p post := by
--   apply Exec'.strongRec; intro pk ih post p h_eq sub eq_post
--   match p with
--   | .last l =>
--     have run : Linst.Run pk.sevm pk.devm l (.ok post) := by
--       rw [← eq_post]; apply Linst.run_of_at pk.exc <| Linst.at_of_slice sub
--     apply Func.Run.last run
--   | .next n p =>
--     rcases of_subcode sub with ⟨cd, h_eq', h_slice⟩;
--     rcases of_bind_eq_some h_eq' with ⟨cd', h_eq'', h_rw⟩; clear h_eq'
--     simp [pure] at h_rw;
--     rw [← h_rw] at h_slice;
--     clear h_rw cd
--     have h_at : Ninst.At pk.sevm.code pk.pc n := by
--       apply Ninst.at_of_slice
--       apply List.slice_prefix h_slice
--     have bar' :
--       ∃ inter exc',
--         Run pk.sevm pk.devm n inter ∧
--         ⟨pk.pc + n.size, pk.sevm, inter, pk.exn, exc'⟩ ≺ pk := by
--       have bar := @Ninst.run_of_at pk.pc pk.sevm pk.devm n post
--       rw [← eq_post] at bar; apply bar pk.exc h_at
--     rcases bar' with ⟨inter, exc', h_run, h_prec⟩
--     apply @Func.Run.next (f :: fs) pk.sevm pk.devm n inter p post h_run
--     have quz :
--       subcode pk.sevm.code.toList (pk.pc + n.size)
--         (Func.compile (table 0 (f :: fs)) (pk.pc + n.size) p) := by
--       rw [h_eq'']
--       simp only [subcode]
--       rw [Ninst.size_eq_length_toB8L]
--       apply List.slice_suffix h_slice
--     apply
--       @ih ⟨pk.pc + n.size, pk.sevm, inter, pk.exn, exc'⟩
--         (Exec'.lt_of_prec h_prec)
--         post
--         p
--         h_eq
--         quz
--         eq_post
--   | .branch p q =>
--     rcases subcode_compile_branch sub with
--       ⟨loc, h_loc, h_push, h_jumpi, h_scp, h_jumpdest, h_scq⟩
--     have h :
--         ∃ (devm' : Devm) (exc' : Exec (pk.pc  + 3) pk.sevm devm' (.ok post)), --(pk.pc + 3) pk.r),
--           Devm.Push [Nat.toB256 loc] pk.devm devm' ∧
--           Exec'.Prec ⟨pk.pc + 3, pk.sevm, devm', pk.exn, eq_post ▸ exc'⟩ pk := by
--       sorry
--     rcases h with ⟨devm', exc', h_push, h_prec⟩
--     rcases jumpi_at exc' h_jumpi with
--         ⟨x, devm'', exc'', popBurn, prec⟩
--       | ⟨x, y, devm'', exc'', popBurn, jumpable, ne, prec⟩ <;> clear h_jumpi
--     · clear h_scq h_jumpdest
--
--       have h_pop' : Devm.PopBurn [0] pk.devm devm'' := by sorry
--       apply Func.Run.zero h_pop'
--       have h_lt : Exec'.lt ⟨pk.pc + 4, pk.sevm, devm'', pk.exn, eq_post ▸ exc''⟩ pk := by sorry
--       apply ih ⟨pk.pc + 4, pk.sevm, devm'', pk.exn, eq_post ▸ exc''⟩ h_lt post p h_eq h_scp eq_post
--
--     · clear ih
--       have h_loc' : loc < 2 ^ 256 := by
--         apply Nat.lt_trans h_loc
--         rw [Nat.pow_lt_pow_iff_right] <;> omega
--       have h : x.toNat = loc ∧ Devm.PopBurn [y] pk.devm devm'' := by
--         --rcases Desc.push_cons_pop_cons h_push h_pop
--         --  with ⟨hx, st, h_push', h_pop'⟩
--         --rw [ Desc.push_nil h_push',
--         --     ← congrArg B256.toNat hx,
--         --     toNat_toB256_of_lt h_loc' ]
--         -- refine ⟨rfl, h_pop'⟩
--         sorry
--
--       rcases h with ⟨hx, popBurn'⟩
--       have run : Func.Run (f :: fs) pk.sevm devm'' q post := by sorry
--
--       apply Func.Run.succ ne popBurn' run
--   | .call k => sorry


theorem correct (e : Env) (s : Desc) (p : Prog) (r : Result)
    (cr : Exec e s 0 r) (h : some e.code = p.compile) :
    Prog.Run e s p r := by
  rcases @subcode_of_get?_eq_some p.main p.aux e 0 _ p.main h rfl
    with ⟨h_at, h_sub⟩
  rcases jumpdest_at cr h_at with ⟨cr', h⟩; clear h h_at
  apply correct_core p.main p.aux ⟨e, s, 1, r, cr'⟩ p.main h h_sub

def Prog.At (p : Prog) (ca : Adr)
    (e : Env) (s : Desc) (pc : Nat) : Prop :=
  some (s.code ca) = Prog.compile p ∧
  (e.cta = ca → (some e.code = Prog.compile p ∧ pc = 0))

def Exec.Wkn (ca : Adr) (p : Prog)
    (π : Exec.Pred)
    (e s pc r) (ex : Exec e s pc r) : Prop :=
  p.At ca e s pc → π _ _ _ _ ex

def ForallDeeper (k : Nat) (ε : Exec.Pred) : Prop :=
  ∀ e s pc r (ex : Exec e s pc r), e.exd < k → ε _ _ _ _ ex

def ForallDeeperAt (k : Nat) (ca : Adr) (p : Prog) (ε : Exec.Pred) : Prop :=
  ForallDeeper k (λ e s pc _ ex => p.At ca e s pc → ε _ _ _ _ ex)

lemma Xinst.exd_lt_of_run' {e s ep sp o r sw}
    (h : Xinst.Run' e s ep sp o r sw) : ep.exd < e.exd := by
  cases h <;> {simp [(asm : e.exd = _)]; apply Nat.lt_succ_self}

lemma ctc_eq_of_call {e s ep sp rx sw}
    (h : Xinst.Run' e s ep sp .call rx sw) : ep.code = s.code ep.cta := by
  cases h; simp [Env.prep]

lemma ctc_eq_of_statcall {e s ep sp rx sw}
    (h : Xinst.Run' e s ep sp .statcall rx sw) : ep.code = s.code ep.cta := by
  cases h; simp [Env.prep]

lemma Env.cta_prep_eq {e : Env} {d : Desc}
  {adr adr'} {slc v a n w} :
  (Env.prep e d adr slc adr' v a n w).cta = adr := rfl

lemma call_or_statcall_of_ne {e s ep sp o rx sw}
    (ho : Xinst.isCall o)
    (h_run : Xinst.Run' e s ep sp o rx sw)
    (h_ne : e.cta ≠ ep.cta) : o = .call ∨ o = .statcall := by
  cases h_run
  · cases ho
  · cases ho
  · left; rfl
  · rw [Env.cta_prep_eq] at h_ne
    cases (h_ne rfl)
  · rw [Env.cta_prep_eq] at h_ne
    cases (h_ne rfl)
  · right; rfl

lemma Xinst.rel_inv_code {a} {e s ep sp o rx sw}
    (h_cr : Xinst.Run' e s ep sp o rx sw)
    (h_ne : s.code a ≠ [])
    (h_run : Exec ep sp 0 rx) : s.code a = sw.code a := by
  have h_ne' : sp.code a ≠ List.nil := by
    rw [← Xinst.prep_inv_code h_cr]; exact h_ne
  rw [Xinst.prep_inv_code h_cr, Exec.inv_code h_run h_ne']
  apply Xinst.wrap_inv_code'' h_cr h_ne

lemma combine_prog
    {ε : Exec.Pred}
    {π : Prog.Pred}
    (h_imp : ∀ {e s p r} (ex : Exec e s 0 r), π e s p r → ε _ _ _ _ ex)
    {ca : Adr}
    {p : Prog}
    ( h_inv :
      ∀ {e s r},
        Prog.Run e s p r → e.cta = ca →
        ForallDeeperAt e.exd ca p ε → π e s p r )
    {e : Env} {s : Desc}
    {r : Result} {pc : Nat}
    (h_fa : ForallDeeperAt e.exd ca p ε)
    (h_cond : e.cta = ca → some e.code = Prog.compile p ∧ pc = 0)
    (h_cta : e.cta = ca)
    (ex : Exec e s pc r) :
    ε _ _ _ _ ex := by
  rcases h_cond h_cta with ⟨h_code, ⟨_⟩⟩
  have h_run : Prog.Run e s p r := correct _ _ _ _ ex h_code
  apply h_imp ex <| h_inv h_run h_cta h_fa

lemma lift_core
    (ε : Exec.Pred)
    (π : Prog.Pred)
    (analog : ∀ {e s p r} (ex : Exec e s 0 r), π e s p r → ε _ _ _ _ ex)
    (ca : Adr) (p : Prog)
    ( depth_ind :
      ∀ {e s r},
        Prog.Run e s p r →
        e.cta = ca →
        ForallDeeperAt e.exd ca p ε →
        π e s p r )
    ( step_inv :
      ∀ {e s pc s' pc' r}
        (h : Step e s pc s' pc')
        (ex : Exec e s' pc' r),
        e.cta ≠ ca →
        ε e s' pc' r ex →
        ε e s pc r (.step h ex) )
    ( exec_inv :
      ∀ {e s pc ep sp i r s' r'}
        (h_at : Xinst.At e pc i)
        (h_run : Xinst.Run' e s ep sp i r s')
        (ex : Exec ep sp 0 r)
        (ex' : Exec e s' (pc + 1) r'),
        e.cta ≠ ca →
        ε ep sp 0 r ex →
        ε e s' (pc + 1) r' ex' →
        ε e s pc r' (.exec h_at h_run ex ex') )
    ( halt_inv :
      ∀ {e s pc r} (h : Halt e s pc r),
        e.cta ≠ ca →
        ε e s pc r (.halt h) )
    : Exec.Fa (@Exec.Wkn ca p ε) := by
  apply Exec.strong_rec; apply @Exec.rec (Fortify (Exec.Wkn ca p ε))
  · intro e s pc s' pc' r h_step ex ih ih' h_at
    rcases em (e.cta = ca) with h_eq | h_ne
    · apply combine_prog analog depth_ind ih' h_at.right h_eq
    · clear depth_ind analog
      have h_code_inv : some (s'.code ca) = Prog.compile p := by
        rw [← Step.inv_code h_step, h_at.left]
      have hε : ε e s' pc' r ex :=
        ih ih' ⟨h_code_inv, λ hc => (h_ne hc).elim⟩
      apply step_inv h_step ex h_ne hε
  · intro e s pc ep sp i r s' r' h_at h_run ex ex' ih ih' h_fa h_at'
    have h_comp := h_at'.left
    rcases em (e.cta = ca) with h_eq | h_ne
    · apply combine_prog analog depth_ind h_fa h_at'.right h_eq
    · clear analog depth_ind step_inv
      apply exec_inv h_at h_run ex ex' h_ne
      · apply ih _ ⟨_, _⟩
        . intro e_ s_ pc_ r_ ex_ h_lt; apply h_fa
          apply _root_.lt_trans h_lt <| Xinst.exd_lt_of_run' h_run
        · rw [← Xinst.prep_inv_code h_run, h_comp]
        · intro h_eq; refine' ⟨_, rfl⟩
          by_cases ho : i.isCall
          · rw [← h_eq] at h_ne
            rcases call_or_statcall_of_ne ho h_run h_ne with
              h | h <;> rw [h] at h_run <;> clear h
            · rw [ctc_eq_of_call h_run, h_eq, h_comp]
            · rw [ctc_eq_of_statcall h_run, h_eq, h_comp]
          · rw [← h_eq, Xinst.code_eq_nil_of_run' h_run ho] at h_comp
            cases Prog.compile_ne_nil h_comp.symm
      · apply ih' h_fa ⟨_, λ hc => (h_ne hc).elim⟩
        rw [← h_comp]; simp;
        rw [Xinst.rel_inv_code h_run _ ex]
        intro hc; apply Prog.compile_ne_nil
        rw [← hc]; apply h_comp.symm
  · intro e s pc r h_halt h_fa h_at
    rcases em (e.cta = ca) with h_eq | h_ne
    · exact combine_prog analog depth_ind h_fa h_at.right h_eq (.halt h_halt)
    · exact halt_inv h_halt h_ne

def ForallSubExec (k : Nat) (ca : Adr) (p : Prog)
    (R : Env → Desc → Result → Prop) : Prop :=
  ∀ e s pc r,
    Exec e s pc r →
    e.exd < k →
    p.At ca e s pc →
    R e s r

lemma lift
    (R : Env → Desc → Result → Prop)
    (ca : Adr) -- contract address
    (p : Prog)
    ( depth_ind :
      ∀ {e s r},
        Prog.Run e s p r →
        e.cta = ca →
        ForallSubExec e.exd ca p R →
        R e s r )
    ( step_inv :
      ∀ {e s pc s' pc' r},
        Step e s pc s' pc' →
        Exec e s' pc' r →
        e.cta ≠ ca →
        R e s' r → R e s r )
    ( exec_inv :
      ∀ {e s pc ep sp i r s' r'},
        Xinst.At e pc i →
        Xinst.Run' e s ep sp i r s' →
        Exec ep sp 0 r →
        Exec e s' (pc + 1) r' →
        e.cta ≠ ca →
        R ep sp r → R e s' r' → R e s r' )
    ( halt_inv :
      ∀ {e s pc r},
        Halt e s pc r →
        e.cta ≠ ca →
        R e s r ) :
    ∀ e s pc r,
      Exec e s pc r →
      Prog.At p ca e s pc →
      R e s r := by
  intro e s pc r ex h
  apply
    lift_core
      (λ e s _ r _ => R e s r)
      (λ e s _ r => R e s r)
      (λ _ h => h) ca p
      depth_ind
      step_inv
      exec_inv
      halt_inv
      e s pc r ex h

lemma lift_inv
    (ca : Adr) (p : Prog)
    (σ : Env → Desc → Prop)
    (ρ : Env → Result → Prop)
    ( with_depth_ind :
      ∀ {e s r},
        Prog.Run e s p r →
        e.cta = ca →
        (∀ e' s' pc' r',
           Exec e' s' pc' r' →
           e'.exd < e.exd →
           Prog.At p ca e' s' pc' →
           σ e' s' → ρ e' r') →
        σ e s → ρ e r )
    ( step_inv :
      ∀ {e s pc s' pc'},
        Step e s pc s' pc' →
        e.cta ≠ ca → σ e s → σ e s' )
    ( exec_inv :
      ∀ {e s ep sp o rx sw},
        Xinst.Run' e s ep sp o rx sw →
        e.cta ≠ ca → σ e s →
        (σ ep sp ∧ (ρ ep rx → σ e sw)) )
    ( halt_inv :
      ∀ {e s pc r},
        Halt e s pc r → e.cta ≠ ca →
        σ e s → ρ e r ) :
    ∀ e s pc r,
      Exec e s pc r →
      Prog.At p ca e s pc →
      σ e s → ρ e r := by
  apply @lift (λ e s r => σ e s → ρ e r) ca p with_depth_ind
  · intro e s pc s' pc' r h_step _ h_ne ih --hσ
    apply ih ∘ step_inv h_step h_ne
  · intro e s pc ep sp i r s' r' _ h_run _ _ h_ne ih ih' hσ
    rcases exec_inv h_run h_ne hσ with ⟨hσ', h_imp⟩
    apply ih' <| h_imp <| ih hσ'
  · intro e s pc r h_halt h_ne; exact halt_inv h_halt h_ne

syntax "show_prefix_zero" : tactic
macro_rules
  | `(tactic| show_prefix_zero) =>
    `(tactic| intros h0 h1; apply append_pref h0.stk h1)

syntax "show_prefix_one" : tactic
macro_rules
  | `(tactic| show_prefix_one) =>
    `(tactic| intros h0 h1; rcases h0 with ⟨x', h0⟩;
              rcases h0.stk with ⟨stk, h2, h3⟩; clear h0;
              rcases List.of_cons_pref_of_cons_pref h1 (pref_of_split h2) with ⟨hx, h⟩;
              cases hx; clear h; apply append_pref h3 (of_append_pref h2 h1) )

syntax "show_prefix_two" : tactic
macro_rules
  | `(tactic| show_prefix_two) =>
    `(tactic| intros h0 h1; rcases h0 with ⟨x', y', h0⟩;
              rcases h0.stk with ⟨stk, h2, h3⟩; clear h0;
              rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2) with ⟨hx, hy, h⟩;
              cases hx; cases hy; clear h; apply append_pref h3 (of_append_pref h2 h1) )

lemma prefix_of_not {x xs} {s s' : Desc} :
    Desc.Not s s' → (x :: xs <<+ s.stk) → (~~~ x :: xs <<+ s'.stk) := by show_prefix_one

lemma prefix_of_eq {x y xs} {s s'} :
    Desc.Eq s s' → (x :: y :: xs <<+ s.stk) → ((x =? y) :: xs <<+ s'.stk) := by show_prefix_two

lemma prefix_of_lt {x y xs} {s s'} :
    Desc.Lt s s' → (x :: y :: xs <<+ s.stk) → ((x <? y) :: xs <<+ s'.stk) :=
  by show_prefix_two

lemma prefix_of_gt {x y xs} {s s'} :
    Desc.Gt s s' → (x :: y :: xs <<+ s.stk) → ((x >? y) :: xs <<+ s'.stk) :=
  by show_prefix_two

lemma prefix_of_shl {x y xs} {s s' : Desc} :
    Desc.Shl s s' → (x :: y :: xs <<+ s.stk) → (y <<< x.toNat :: xs <<+ s'.stk) :=
  by show_prefix_two

lemma prefix_of_shr {x y xs} {s s' : Desc} :
    Desc.Shr s s' → (x :: y :: xs <<+ s.stk) → (y >>> x.toNat :: xs <<+ s'.stk) :=
  by show_prefix_two

lemma prefix_of_or {x y xs} {s s' : Desc} :
    Desc.Or s s' → (x :: y :: xs <<+ s.stk) → ((x ||| y) :: xs <<+ s'.stk) :=
  by show_prefix_two

lemma prefix_of_and {x y xs} {s s' : Desc} :
    Desc.And s s' → (x :: y :: xs <<+ s.stk) → ((x &&& y) :: xs <<+ s'.stk) :=
  by show_prefix_two

lemma prefix_of_add {x y xs} {s s' : Desc} :
    Desc.Add s s' → (x :: y :: xs <<+ s.stk) → ((x + y) :: xs <<+ s'.stk) :=
  by show_prefix_two

lemma prefix_of_sub {x y xs} {s s' : Desc} :
    Desc.Sub s s' → (x :: y :: xs <<+ s.stk) → ((x - y) :: xs <<+ s'.stk) :=
  by show_prefix_two

lemma prefix_of_mstore {x y xs} {s s'} :
    Desc.Mstore s s' → (x :: y :: xs <<+ s.stk) → (xs <<+ s'.stk) := by
  intros h_mstore h_pfx
  rcases h_mstore with ⟨x', y', h⟩
  have h_pop := Stack.of_diff_nil h.stk; clear h
  rcases of_cons_cons_pref_of_cons_cons_pref h_pfx (pref_of_split h_pop)
    with ⟨hx, hy, h⟩; clear h
  rw [hx, hy] at h_pfx
  apply @of_append_pref _ _ xs _ _ h_pop h_pfx

lemma prefix_of_sstore {e} {x y xs} {s s' : Desc} :
    Desc.Sstore e s s' → (x :: y :: xs <<+ s.stk) → (xs <<+ s'.stk) := by
  intros h0 h1;
  rcases h0 with ⟨x', y', h4, h5⟩; clear h5
  have h5 : ([x', y'] <++ s.stk ++> s'.stk) := by
    rcases h4.stk with ⟨stk, h7, h8⟩
    rw [List.of_nil_split h8]; apply h7
  clear h4
  rcases split_of_prefix h1 with ⟨sfx, h6⟩
  have h_eq := Eq.trans h5.symm h6; simp at h_eq
  refine ⟨sfx, h_eq.right.right⟩

lemma prefix_of_sload {e x xs} {s s'} :
    Desc.Sload e s s' → (x :: xs <<+ s.stk) →
    (s.stor e.cta x :: xs <<+ s'.stk) :=
  by show_prefix_one

lemma prefix_of_sload' {e x xs} {s s'} :
    Desc.Sload e s s' → (x :: xs <<+ s.stk) →
    ∃ y, (y :: xs <<+ s'.stk) ∧ y = s.stor e.cta x := by
  intros h0 h1; refine ⟨_, prefix_of_sload h0 h1, rfl⟩

lemma prefix_of_push {xs ys} {s s'} :
    Desc.Push xs s s' → (ys <<+ s.stk) → ((xs ++ ys) <<+ s'.stk) :=
  λ h0 h1 => append_pref h0.stk h1

lemma prefix_of_pop {y : B256} {xs} {s s' : Desc} :
    (∃ x, Desc.Pop [x] s s') → (y :: xs <<+ s.stk) → (xs <<+ s'.stk) := by
  intros h h'; rcases h with ⟨x, hx⟩
  have h_eq : y = x :=
    (List.of_cons_pref_of_cons_pref h' (pref_of_split hx.stk)).left
  rw [h_eq] at h'; apply @of_append_pref _ [x] _ _ _ hx.stk h'

lemma prefix_of_iszero {x xs} {s s' : Desc} :
    Desc.Iszero s s' → (x :: xs <<+ s.stk) → ((if x = 0 then 1 else 0) :: xs <<+ s'.stk) :=
  by show_prefix_one

lemma prefix_of_caller {e xs} {s s' : Desc} :
    Desc.Caller e s s' → (xs <<+ s.stk) → (e.cla.toB256 :: xs <<+ s'.stk) :=
  by show_prefix_zero

lemma prefix_of_callvalue {e xs} {s s' : Desc} :
   Desc.Callvalue e s s' → (xs <<+ s.stk) → (e.clv :: xs <<+ s'.stk) :=
 by show_prefix_zero

lemma prefix_of_calldatacopy {e x y z xs} {s s' : Desc} :
    Desc.Calldatacopy e s s' → (x :: y :: z :: xs <<+ s.stk) → (xs <<+ s'.stk) := by
  intros h0 h1;
  simp [Desc.Calldatacopy] at h0
  rcases h0 with ⟨x', y', z', h0⟩
  have h2 := h0.stk; clear h0;
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2)
    with ⟨hx, hy, ws, h, h'⟩
  rcases List.of_cons_pref_of_cons_pref h h' with ⟨hz, _⟩
  rw [hx, hy, hz] at h1; apply of_append_pref h2 h1

lemma Line.spx_scheme {e s' i l xs xs' ys}
    (h : ∀ s0 s1, Ninst.Run e s0 i s1 → (xs <<+ s0.stk) → (xs' <<+ s1.stk))
    (h' : ∀ s : Desc, (xs' <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) :
    ∀ s : Desc, (xs <<+ s.stk) → Line.Run e s (i :: l) s'→ (ys <<+ s'.stk) := by
  intros s h_pfx h_run
  rcases Line.of_run_cons h_run with ⟨s_mid, h_head, h_tail⟩
  apply h' s_mid (h _ _ h_head h_pfx) h_tail

lemma Line.spx_push {e : Env} {s' l bs p xs ys} :
    (∀ s : Desc, (bs.toB256 :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : Desc, (xs <<+ s.stk) → Line.Run e s (push bs p :: l) s'→ (ys <<+ s'.stk)) := by
  intros h_next s h_pfx h_run
  rcases Line.of_run_cons h_run with ⟨s_mid, h_head, h_tail⟩
  apply h_next s_mid _ h_tail
  apply prefix_of_push (of_run_push h_head) h_pfx

lemma Line.spx_pushB256 {e : Env} {s' l x xs ys} :
    (∀ s : Desc, (x :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : Desc, (xs <<+ s.stk) → Line.Run e s (pushB256 x :: l) s'→ (ys <<+ s'.stk)) := by
  intros h_next s h_pfx h_run
  rcases Line.of_run_cons h_run with ⟨s_mid, h_head, h_tail⟩
  apply h_next s_mid _ h_tail
  apply prefix_of_push (of_run_pushB256 h_head) h_pfx

macro "spx_conv" : tactic =>
  `(tactic| conv => ext; ext; rw [← op_run_iff_inst_run]; rfl)

lemma Line.spx_mstore {e : Env} {s' l x y xs ys} :
    (∀ s : Desc, (xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : Desc, (x :: y :: xs <<+ s.stk) → Line.Run e s (mstore :: l) s'→ (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_mstore

lemma Line.spx_sstore {e : Env} {s' l x y xs ys} :
    (∀ s : Desc, (xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : Desc, (x :: y :: xs <<+ s.stk) → Line.Run e s (sstore :: l) s'→ (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_sstore

lemma Line.spx_dup {e s' l xs ys} {n : Fin 16} (x) :
  Stack.Nth n.val x xs →
    (∀ s : Desc, (x :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : Desc, (xs <<+ s.stk) → Line.Run e s (dup n :: l) s' → (ys <<+ s'.stk)) := by
  intro h_nth; apply Line.spx_scheme
  spx_conv; intros s0 s1 h_step
  apply Stack.prefix_of_dup ⟨x, rfl, h_nth⟩ h_step.stk

lemma Line.spx_log (zs : Stack) {e s' l xs ys} {n : Fin 5} :
    zs.length = n.val + 2 →
    (∀ s : Desc, (xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : Desc, (zs ++ xs <<+ s.stk) → Line.Run e s (log n :: l) s' → (ys <<+ s'.stk)) := by
  intro h_len; apply Line.spx_scheme; spx_conv; intros s₀ s₁ h_step h_pfx
  have hh : ∃ zs', zs'.length = n.val + 2 ∧ Stack.Pop zs' s₀.stk s₁.stk := by
    match n with
    | ⟨0, _⟩ =>
      rcases h_step with ⟨x₀, x₁, h⟩
      refine' ⟨[x₀, x₁], rfl, h.stk⟩
    | ⟨1, _⟩ =>
      rcases h_step with ⟨x₀, x₁, x₂, h⟩
      refine' ⟨[x₀, x₁, x₂], rfl, h.stk⟩
    | ⟨2, _⟩ =>
      rcases h_step with ⟨x₀, x₁, x₂, x₃, h⟩
      refine' ⟨[x₀, x₁, x₂, x₃], rfl, h.stk⟩
    | ⟨3, _⟩ =>
      rcases h_step with ⟨x₀, x₁, x₂, x₃, x₄, h⟩
      refine' ⟨[x₀, x₁, x₂, x₃, x₄], rfl, h.stk⟩
    | ⟨4, _⟩ =>
      rcases h_step with ⟨x₀, x₁, x₂, x₃, x₄, x₅, h⟩
      refine' ⟨[x₀, x₁, x₂, x₃, x₄, x₅], rfl, h.stk⟩
    | ⟨5, h⟩ => cases (Nat.lt_irrefl _ h)
  rcases hh with ⟨zs', h_len', h_pop⟩
  have h_zs : (zs <<+ s₀.stk) := @pref_trans _ zs (zs ++ xs) _ ⟨xs, rfl⟩ h_pfx
  have h_zs' : (zs' <<+ s₀.stk) := pref_of_split h_pop
  cases List.pref_unique (Eq.trans h_len h_len'.symm) h_zs h_zs'
  apply of_append_pref h_pop h_pfx

lemma Line.spx_swap (xs') {e s' l xs ys} {n : Fin 16} :
    Stack.Swap n.val xs xs' →
    (∀ s : Desc, (xs' <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : Desc, (xs <<+ s.stk) → Line.Run e s (swap n :: l) s' → (ys <<+ s'.stk)) := by
  intro h_swap; apply Line.spx_scheme;
  spx_conv; intros s0 s1 h_step
  apply Stack.prefix_of_swap h_swap h_step.stk

lemma Line.spx_iszero {e s' l} {x} {xs ys} :
    (∀ s : Desc, ((x =? 0) :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : Desc, (x :: xs <<+ s.stk) → Line.Run e s (iszero :: l) s' → (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_iszero

lemma Line.spx_pop {e : Env} {s' l x xs ys} :
    (∀ s : Desc, (xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : Desc, (x :: xs <<+ s.stk) → Line.Run e s (pop :: l) s'→ (ys <<+ s'.stk)) :=by
  apply Line.spx_scheme; spx_conv; apply prefix_of_pop

lemma Line.spx_eq {e s' l x y xs ys}  :
    (∀ s : Desc, ((x =? y) :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : Desc, (x :: y :: xs <<+ s.stk) → Line.Run e s (eq :: l) s' → (ys <<+ s'.stk)) :=by
  apply Line.spx_scheme; spx_conv; apply prefix_of_eq

lemma Line.spx_lt {e s' l x y xs ys}  :
    (∀ s : Desc, ((x <? y) :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : Desc, (x :: y :: xs <<+ s.stk) → Line.Run e s (lt :: l) s' → (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_lt

lemma Line.spx_gt {e s' l x y xs ys}  :
    (∀ s : Desc, ((x >? y) :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : Desc, (x :: y :: xs <<+ s.stk) → Line.Run e s (gt :: l) s' → (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_gt

lemma Line.spx_sub {e s' l x y xs ys}  :
    (∀ s : Desc, ((x - y) :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : Desc, (x :: y :: xs <<+ s.stk) → Line.Run e s (sub :: l) s' → (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_sub

lemma Line.spx_not {e s' l x xs ys}  :
    (∀ s : Desc, (~~~ x :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : Desc, (x :: xs <<+ s.stk) → Line.Run e s (not :: l) s' → (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_not

lemma Line.spx_or {e s' l x y xs ys}  :
    (∀ s : Desc, ((x ||| y) :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : Desc, (x :: y :: xs <<+ s.stk) → Line.Run e s (or :: l) s' → (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_or

lemma Line.spx_and {e s' l x y xs ys}  :
    (∀ s : Desc, ((x &&& y) :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : Desc, (x :: y :: xs <<+ s.stk) → Line.Run e s (and :: l) s' → (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_and

lemma Line.spx_shl {e s' l} {x y : B256} {xs ys}  :
    (∀ s : Desc, (y <<< x.toNat :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : Desc, (x :: y :: xs <<+ s.stk) → Line.Run e s (shl :: l) s' → (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_shl

lemma Line.spx_shr {e s' l} {x y : B256} {xs ys}  :
    (∀ s : Desc, (y >>> x.toNat :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : Desc, (x :: y :: xs <<+ s.stk) → Line.Run e s (shr :: l) s' → (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_shr

lemma Line.spx_add {e s' l x y xs ys}  :
    (∀ s : Desc, ((x + y) :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : Desc, (x :: y :: xs <<+ s.stk) → Line.Run e s (add :: l) s' → (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_add

lemma Line.spx_caller {e : Env} {s' l xs ys}  :
    (∀ s : Desc, (e.cla.toB256 :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : Desc, (xs <<+ s.stk) → Line.Run e s (caller :: l) s' → (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_caller

lemma Line.spx_callvalue {e : Env} {s' l xs ys}  :
    (∀ s : Desc, (e.clv :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : Desc, (xs <<+ s.stk) → Line.Run e s (callvalue :: l) s' → (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_callvalue

lemma Line.spx_calldatacopy {e : Env} {s' l x y z xs ys}  :
    (∀ s : Desc, (xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : Desc, (x :: y :: z :: xs <<+ s.stk) → Line.Run e s (calldatacopy :: l) s' → (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_calldatacopy

lemma Line.spx_unwrap {e xs} {s' : Desc} :
    ∀ s : Desc, (xs <<+ s.stk) → Line.Run e s [] s' → (xs <<+ s'.stk) := by
  intros _ h0 h1; cases h1; apply h0

syntax "show_nth" : tactic
macro_rules
  | `(tactic| show_nth) =>
    `(tactic| first | apply Stack.Nth.head | (apply Stack.Nth.tail ; show_nth))

partial def show_nth : Lean.Elab.Tactic.TacticM Unit :=
  "Stack.Nth.head".apply <|> (do "Stack.Nth.tail".apply; show_nth)

def show_nth' : Nat → Lean.Elab.Tactic.TacticM Unit
  | 0 => "Stack.Nth.head".apply
  | n +1 => do "Stack.Nth.tail".apply; show_nth' n

def show_swap' : Nat → Lean.Elab.Tactic.TacticM Unit
  | 0 => "Stack.swapCore_zero".apply
  | n + 1 => do "Stack.swapCore_succ".apply; show_swap' n

def fail {ξ} (s : String) : Lean.Elab.Tactic.TacticM ξ := do
  dbg_trace s; failure

def get_swap_core (xx : Q(B256)) : Nat → Q(Stack) → Lean.Elab.Tactic.TacticM (Q(B256) × Q(Stack))
  | 0, ~q($yx :: $lx) => pure (yx, q($xx :: $lx))
  | n + 1, ~q($yx :: $lx) => do
    let (zx, lx') ← get_swap_core xx n lx
    pure (zx, q($yx :: $lx'))
  | _, _ =>fail "get_swap_core : cannot decompose list"

def get_swap (n : Nat) : Q(Stack) → Lean.Elab.Tactic.TacticM Q(Stack)
  | ~q($xx :: $lx) => do
    let (yx, lx') ← get_swap_core xx n lx
    pure q($yx :: $lx')
  | _ => fail "get_swap : cannot decompose list"

def get_take : Nat → Q(Stack) → Lean.Elab.Tactic.TacticM Q(Stack)
  | 0, _ => pure q([])
  | _ + 1, ~q([]) => fail "cannot take from empty list"
  | n + 1, ~q($xx :: $lx) => do
    let lx' ← get_take n lx
    pure q($xx :: $lx')
  | _, _ => fail "get take : cannot decompose list"

partial def line_pref : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
  let t : Q(Prop) ← Lean.Elab.Tactic.getMainTarget
  match t with
  | ~q(∀ s : _root_.Desc, ($px <<+ s.stk) → Line.Run _ s $lx _ → _) =>
    let lx' : Q(Line) ← Lean.Meta.whnf lx
    match lx' with
    | ~q([]) => "Line.spx_unwrap".apply
    | ~q($ix :: _) =>
      match ix with
      | ~q(Ninst.dup $nx) =>
        let n ← unsafe Lean.Meta.evalExpr (Fin 16) q(Fin 16) nx
        "Line.spx_dup".apply; show_nth' n.val
      | ~q(Ninst.log $nx) =>
        let n ← unsafe Lean.Meta.evalExpr (Fin 5) q(Fin 5) nx
        let x ← get_take (n.val + 2) px
        Lean.Expr.apply <| Lean.mkApp "Line.spx_log".toExpr x
        Lean.Elab.Tactic.evalRefl Lean.Syntax.missing
      | ~q(Ninst.swap $nx) =>
        let n ← unsafe Lean.Meta.evalExpr (Fin 16) q(Fin 16) nx
        let x ← get_swap n.val px
        Lean.Expr.apply <| Lean.mkApp "Line.spx_swap".toExpr x
        show_swap' n.val
      | ~q(Ninst.pushB256 _) => "Line.spx_pushB256".apply
      | ~q(Ninst.push _ _) => "Line.spx_push".apply
      | ~q(Ninst.sub) => "Line.spx_sub".apply
      | ~q(Ninst.add) => "Line.spx_add".apply
      | ~q(Ninst.pop) => "Line.spx_pop".apply
      | ~q(Ninst.sstore) => "Line.spx_sstore".apply
      | ~q(Ninst.mstore) => "Line.spx_mstore".apply
      | ~q(Ninst.lt) => "Line.spx_lt".apply
      | ~q(Ninst.gt) => "Line.spx_gt".apply
      | ~q(Ninst.eq) => "Line.spx_eq".apply
      | ~q(Ninst.not) => "Line.spx_not".apply
      | ~q(Ninst.and) => "Line.spx_and".apply
      | ~q(Ninst.or) => "Line.spx_or".apply
      | ~q(Ninst.shl) => "Line.spx_shl".apply
      | ~q(Ninst.shr) => "Line.spx_shr".apply
      | ~q(Ninst.iszero) => "Line.spx_iszero".apply
      | ~q(Ninst.caller) => "Line.spx_caller".apply
      | ~q(Ninst.callvalue) => "Line.spx_callvalue".apply
      | ~q(Ninst.calldatacopy) => "Line.spx_calldatacopy".apply
      | _ => dbg_trace "line_pref : unimplemented inst"; failure
      line_pref
  | _ =>
    dbg_trace "Not a pref goal : "
    dbg_trace t

elab "line_pref" : tactic => line_pref

section

open Lean.Elab.Tactic
open Lean.Parser.Tactic
open Lean.Elab.Term
open Lean
-- open Qq

def breakLineRun : Q(Prop) → TacticM (Expr × Expr × Expr × Expr)
| ~q(Line.Run $e $s $l $s') => pure (e, s, l, s')
| _ => failure

def findDeclWithM (f : LocalDecl → TacticM Bool) : TacticM Lean.LocalDecl := do
  let g : LocalDecl → TacticM (Option LocalDecl) := fun d => do
    if (← f d) then pure (some d) else pure none
  let ctx ← MonadLCtx.getLCtx
  let (some d) ← ctx.findDeclM? g | failure
  pure d

def isLineRun (ld : Lean.LocalDecl) : TacticM Bool := do
  let px : Q(Prop) ← Meta.inferType ld.toExpr
  match px with
  | ~q(Line.Run _ $sx _ $sx') => pure true
  | _ => pure false

def addIfOcc (x : Expr) (ds : List LocalDecl)
    (d : LocalDecl) : Lean.Elab.Tactic.TacticM (List LocalDecl) :=
  withMainContext do
    let t ← instantiateMVars (← Meta.inferType d.toExpr)
    if Expr.occurs x t
    then pure (d :: ds)
    else pure ds

def Lean.FVarId.revert (is : List FVarId) : Lean.Elab.Tactic.TacticM Unit :=
  withMainContext do
    let (_, mvarId) ← (← getMainGoal).revert ⟨is⟩
    replaceMainGoal [mvarId]

def replaceWithBvar (x : Expr) (k : Nat) (e : Expr) : Expr :=
  if BEq.beq x e
  then Expr.bvar k
  else match e with
    | .lam n t b i => .lam n (replaceWithBvar x k t) (replaceWithBvar x (k + 1) b) i
    | .forallE n t b i => .forallE n (replaceWithBvar x k t) (replaceWithBvar x (k + 1) b) i
    | .mdata d b => .mdata d (replaceWithBvar x k b)
    | .app f a => .app (replaceWithBvar x k f) (replaceWithBvar x k a)
    | .proj n i s => .proj n i (replaceWithBvar x k s)
    | .letE n t v b nd =>
      .letE n (replaceWithBvar x k t) (replaceWithBvar x k v) (replaceWithBvar x k b) nd
    | e => e

lemma Line.of_inv_state (motive : (Adr → Storage) → Prop) (e s l s') (h_run : Line.Run e s l s')
    (h_inv : Line.Inv Desc.stor l) (hs' : motive s'.stor) : motive s.stor := by
  rw [Line.of_inv _ h_inv h_run]; exact hs'

def String.toSyntax (s : String) : Lean.Syntax :=
  Lean.Syntax.ident Lean.SourceInfo.none s.toSubstring
    (Lean.Name.str Lean.Name.anonymous s) []

def Strings.intro (ss : List String) : Lean.Elab.Tactic.TacticM Unit := do
  let ids : Lean.TSyntaxArray [`ident, `Lean.Parser.Term.hole] :=
    ⟨ss.map (λ s => {raw := String.toSyntax s})⟩
  let fvars ← liftMetaTacticAux fun mvarId => do
    let (fvars, mvarId) ← mvarId.introN ids.size (ids.map getNameOfIdent').toList
    return (fvars, [mvarId])
  withMainContext do
    for stx in ids, fvar in fvars do
      Lean.Elab.Term.addLocalVarInfo stx (Lean.mkFVar fvar)

elab "lstor" : tactic =>
  withMainContext do
    let d ← findDeclWithM isLineRun
    let (e, s, l, s') ← breakLineRun (← Meta.inferType d.toExpr)
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    let ds ← ctx.foldlM (addIfOcc <| Expr.app q(Desc.stor) s) []
    Lean.FVarId.revert (ds.map LocalDecl.fvarId)
    let g ← Lean.Elab.Tactic.getMainTarget
    let g' := replaceWithBvar (Expr.app q(Desc.stor) s) 0 g
    Expr.apply <|
      Lean.mkApp6 q(Line.of_inv_state)
        (Expr.lam `s q(Adr → Storage) g' BinderInfo.default)
        e s l s' d.toExpr
    line_inv
    Strings.intro (ds.reverse.map (Name.toString ∘ LocalDecl.userName))

def matchingName (x : Lean.Expr) (d : Lean.LocalDecl) :
    Lean.Elab.Tactic.TacticM (Option Lean.Name) := do
  if (← Lean.Meta.isExprDefEq x d.toExpr) -- Check if type equals goal type.
  then return some d.userName -- If equal, success!
  else return none

def subscript_succ_core : List Char → Option (List Char)
| [] => ['₁']
| '₀' :: cs => '₁' :: cs
| '₁' :: cs => '₂' :: cs
| '₂' :: cs => '₃' :: cs
| '₃' :: cs => '₄' :: cs
| '₄' :: cs => '₅' :: cs
| '₅' :: cs => '₆' :: cs
| '₆' :: cs => '₇' :: cs
| '₇' :: cs => '₈' :: cs
| '₈' :: cs => '₉' :: cs
| '₉' :: cs =>
  match subscript_succ_core cs with
  | some cs' => '₀' :: cs'
  | none => none
| _ => none

def subscript_succ (cs : List Char) : Option (List Char) :=
match subscript_succ_core cs.reverse with
| none => none
| some cs' => some cs'.reverse

def findSubscript (x : Lean.Expr) : Lean.Elab.Tactic.TacticM String := do
  Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    let some nm ← ctx.findDeclM? (matchingName x) | failure
    match nm with
    | Lean.Name.str _ s =>
      match s.data with
      | 's' :: cs =>
        match subscript_succ cs with
        | none => failure
        | some cs' => pure ⟨cs'⟩
      | _ => failure
    | _ => failure

open Ninst

lemma branch_elim (φ : Prop) {c e s p q r}
    (hp : ([0] <<+ s.stk) → Func.Run c e s (pop ::: p) r → φ)
    (hq : (∃ w, w ≠ 0 ∧ [w] <<+ s.stk) → Func.Run c e s (pop ::: q) r → φ)
    (h : Func.Run c e s (q <?> p) r) : φ := by
  rcases of_run_branch' h with ⟨h', h''⟩ | ⟨h', h''⟩
  · exact hp h' h''
  · exact hq h' h''

lemma rev_branch_elim (φ : Prop) {e s p r}
    (hp : ([0] <<+ s.stk) → Func.Run c e s (pop ::: p) r → φ)
    (h : Func.Run c e s (.rev <?> p) r) : φ := by
  apply branch_elim φ _ _ h
  · exact hp
  · intros _ h'; cases @not_run_prepend_rev _ _ _ [_] _ h'

lemma branch_elim' {x xs} {e s p q r} (φ : Prop)
    (h : (x :: xs) <<+ s.stk)
    (hp : (x ≠ 0) → Func.Run c e s (pop ::: p) r → φ)
    (hq : (x = 0) → Func.Run c e s (pop ::: q) r → φ) :
    Func.Run c e s (p <?> q) r → φ := by
  apply branch_elim <;> intro h'
  · apply hq; rw [pref_head_unique h h']
  · apply hp; rcases h' with ⟨x', h_ne, h'⟩
    rw [pref_head_unique h h']; exact h_ne

lemma rev_branch_elim' {x xs} {e s p r} (φ : Prop)
    (h : (x :: xs) <<+ s.stk) (h' : (x = 0) → Func.Run c e s (pop ::: p) r → φ) :
    Func.Run c e s (.rev <?> p) r →  φ := by
  apply rev_branch_elim ; intro h''
  apply h' (pref_head_unique h h'')

lemma run_prepend_elim (φ : Prop) (l) {p} {c e} {s : _root_.Desc} {r}
    (h : ∀ s', Line.Run e s l s' → Func.Run c e s' p r → φ)
    (h' : Func.Run c e s (l +++ p) r) : φ := by
  rcases of_run_prepend _ _ h' with ⟨s', hs, hs'⟩; apply h s' hs hs'

lemma run_append_elim (φ : Prop) (l) {l'} {e} {s s'' : _root_.Desc}
    (h : ∀ s', Line.Run e s l s' → Line.Run e s' l' s'' → φ)
    (h' : Line.Run e s (l ++ l') s'') : φ := by
  rcases of_run_append _ h' with ⟨s', hs, hs'⟩; apply h s' hs hs'

elab "pexec" e:term : tactic =>
  withMainContext do
    let x ← elabTermForApply e
    let g : Q(Prop) ← getMainTarget
    match g with
    | ~q(Func.Run _ _ $s _ _ → $c) =>
      let ss ← findSubscript s
      Lean.Expr.apply (Lean.mkApp2 q(@run_prepend_elim) c x)
      Strings.intro ["s" ++ ss, "h" ++ ss]

def Func.take : Nat → Q(Func) → TacticM Q(Line)
| 0, _ => pure q([] : Line)
| n + 1, p => do
  let p' : Q(Func) ← Meta.whnf p
  match p' with
  | ~q(Func.next $i $q) =>
    let x ← Func.take n q
    pure q($i :: $x)
  | _ => failure

elab "pexen" e:num : tactic =>
  withMainContext do
    let n := Lean.TSyntax.getNat e
    let g : Q(Prop) ← getMainTarget
    match g with
    | ~q(Func.Run _ _ $s $p _ → $c) =>
      let ss ← findSubscript s
      let x ← Func.take n p
      Lean.Expr.apply (Lean.mkApp2 q(@run_prepend_elim) c x)
      Strings.intro ["s" ++ ss, "h" ++ ss]

def Line.take : Nat → Q(Line) → TacticM Q(Line)
| 0, _ => pure q([] : Line)
| n + 1, l => do
  let l' : Q(Line) ← Meta.whnf l
  match l' with
  | ~q([]) => failure
  | ~q($i :: $is) =>
    let x ← Line.take n is
    pure q($i :: $x)

elab "lexen" e:num : tactic =>
  withMainContext do
    let n := Lean.TSyntax.getNat e
    let g : Q(Prop) ← getMainTarget
    match g with
    | ~q(Line.Run _ $s $l _ → $c) =>
      let ss ← findSubscript s
      let x ← Line.take n l
      Lean.Expr.apply (Lean.mkApp2 q(@run_append_elim) c x)
      Strings.intro ["s" ++ ss, "h" ++ ss]

elab "lexec" e:term : tactic =>
  withMainContext do
    let x ← elabTermForApply e
    let g : Q(Prop) ← getMainTarget
    match g with
    | ~q(Line.Run _ $s _ _ → $c) =>
      let ss ← findSubscript s
      Lean.Expr.apply (Lean.mkApp2 q(@run_append_elim) c x)
      Strings.intro ["s" ++ ss, "h" ++ ss]

def Lean.FVarId.clear (i : Lean.FVarId) : Lean.Elab.Tactic.TacticM Unit :=
  withMainContext do
    let mvarId ← (← getMainGoal).clear i
    replaceMainGoal [mvarId]

def Lean.FVarId.rvt (i : Lean.FVarId) : TacticM Unit := do
  let (_, mvarId) ← (← getMainGoal).revert #[i] -- (← getFVarIds hs)
  replaceMainGoal [mvarId]

def clear_if (i i' : FVarId) (sx : Expr) (ld : LocalDecl)  : Lean.Elab.Tactic.TacticM Unit := do
  let pre_t ← Meta.inferType ld.toExpr
  let t ← instantiateMVars pre_t
  if (¬ BEq.beq ld.fvarId i ∧ ¬ BEq.beq ld.fvarId i' ∧ Expr.occurs sx t)
  then Lean.FVarId.clear ld.fvarId
  else pure ()

def isPref (x : Lean.Expr) (ld : Lean.LocalDecl) : TacticM Bool := do
  let px : Q(Prop) ← Meta.inferType ld.toExpr
  match px with
  | ~q(_ <<+ (Desc.stk $x')) => pure (← Lean.Meta.isDefEq x x')
  | _ => pure false

def initDescOfRun : Q(Prop) → TacticM Expr
  | ~q(Line.Run _ $sx _ _) => pure sx
  | _ => failure

def Expr.imp (x y : Expr) : Expr := Expr.forallE Name.anonymous x y BinderInfo.default

def mkMotive : Q(Prop) → TacticM Expr
| ~q(($p <<+ (Desc.stk $s₀)) → (Line.Run $e $s₀ $l $s₁) → $φ) => do
  pure <|
    Expr.lam `s q(_root_.Desc)
      ( Expr.imp
          (Expr.app q(λ s : _root_.Desc => $p <<+ s.stk) (Expr.bvar 0))
          (Expr.imp (Expr.app q(λ s : _root_.Desc => Line.Run $e s $l $s₁) (Expr.bvar 1)) φ) )
      BinderInfo.default
| _ => failure

lemma apply_univ {ξ : Type} (φ : ξ → Prop) (x : ξ) (h : ∀ x, φ x) : φ x := h x

elab "lpfx" : tactic =>
  withMainContext do
    let rd ← findDeclWithM isLineRun
    let sx ← initDescOfRun (← Meta.inferType rd.toExpr)
    let pd ← findDeclWithM (isPref sx)
    let sd ← findDeclWithM (λ dd => Meta.isDefEq dd.toExpr sx)
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    ctx.forM (clear_if rd.fvarId pd.fvarId sx)
    Lean.FVarId.rvt rd.fvarId
    Lean.FVarId.rvt pd.fvarId
    let g : Q(Prop) ← getMainTarget
    let m ← mkMotive g
    Expr.apply <| mkApp2 q(@apply_univ _root_.Desc) m sd.toExpr
    line_pref

syntax "linv" : tactic
macro_rules
| `(tactic| linv) =>
  `(tactic| apply Line.of_inv _ _ asm; eta_reduce; line_inv)

def clearIfOcc (sx : Expr) (ld : LocalDecl) : Lean.Elab.Tactic.TacticM Unit := do
  let t' ← instantiateMVars (← Meta.inferType ld.toExpr)
  if Expr.occurs sx t' then ld.fvarId.clear

syntax "cstate" (ppSpace colGt term:max) : tactic
elab_rules : tactic
  | `(tactic| cstate $hs) =>
    Lean.Elab.Tactic.withMainContext do
      let i ← getFVarId hs
      let d ← findDeclWithM (λ d => pure <| BEq.beq d.fvarId i)
      let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
      ctx.forM (clearIfOcc d.toExpr)
      d.fvarId.clear
end

inductive DispatchTree : Type
  | leaf : B256 → Func → DispatchTree
  | fork : DispatchTree → DispatchTree → DispatchTree

open DispatchTree

def DispatchTree.mem : DispatchTree → (B256 × Func) → Prop
  | (leaf w p), wp => wp = (w, p)
  | (fork tl tr), wp => DispatchTree.mem tl wp ∨ DispatchTree.mem tr wp

instance : Membership (B256 × Func) DispatchTree := ⟨DispatchTree.mem⟩

def leftmostFsig : DispatchTree → B256
  | (DispatchTree.leaf w _) => w
  | (DispatchTree.fork t _) => leftmostFsig t

-- given a dispatch tree of functions and their signatures, construct the main program.
-- note it assumes that:
-- (1) the calldata function selector is already at the op of the stack (i.e, it has to be preceded by 'fsig').
-- (2) the functions are ordered in ascending order of their signatures (right is higher)

def dispatchWith (k : Nat) : DispatchTree → Func
  | DispatchTree.leaf w p => pushB256 w ::: eq ::: (p <?> .call k)
  | DispatchTree.fork tl tr =>
    dup 0 :::
    pushB256 (leftmostFsig tr) ::: gt :::
    (dispatchWith k tl <?> dispatchWith k tr)

def dispatch : DispatchTree → Func
  | DispatchTree.leaf w p => pushB256 w ::: eq ::: (p <?> .rev)
  | DispatchTree.fork tl tr =>
    dup 0 :::
    pushB256 (leftmostFsig tr) ::: gt :::
    (dispatch tl <?> dispatch tr)

lemma dispatchWith_inv {c k f} (σ : Env → Desc → Prop) (ρ : Env → Result → Prop)
    (h0 : ∀ {e s x s'}, σ e s → Line.Run e s [pushB256 x, eq, pop] s' → σ e s')
    (h1 : ∀ {e s x s'}, σ e s → Line.Run e s [dup 0, pushB256 x, gt, pop] s' → σ e s')
    (h2 : c[k]? = some f)
    (h3 : ∀ {e s r}, σ e s → Func.Run c e s f r → ρ e r) :
    ∀ t : DispatchTree,
      (∀ {e s r}, ∀ wf ∈ t, σ e s → Func.Run c e s wf.2 r → ρ e r) →
    ∀ (e s r), σ e s → Func.Run c e s (dispatchWith k t) r → ρ e r := by
  intro t; induction t with
  | fork t t' ih ih' =>
    intro htt'
    have ht : ∀ {e s r}, ∀ wp ∈ t, σ e s → Func.Run c e s wp.2 r → ρ e r := by
      intro e s r wp h_in; apply htt' _ <| Or.inl h_in
    have ht' : ∀ {e s r}, ∀ wp ∈ t', σ e s → Func.Run c e s wp.2 r → ρ e r := by
      intro e s r wp h_in; apply htt' _ (Or.inr h_in)
    intro e s r hs; pexen 3; intro h₂
    rcases of_run_branch' h₂ with ⟨_, h⟩ | ⟨_, h⟩ <;>
    (revert h; pexen 1; intro h₃)
    · apply ih' ht' e s₂ r (h1 hs <| run_append h₁ h₂) h₃
    · apply ih ht e s₂ r (h1 hs <| run_append h₁ h₂) h₃
  | leaf w p =>
    intro ht e s r hs; pexen 2; intro h'
    rcases of_run_branch' h' with ⟨_, h⟩ | ⟨_, h⟩ <;>
      (clear h'; revert h; pexen 1; intro h)
    · cases h with
      | @call _ _ f' _ h_eq h_run =>
        have hh := Eq.trans h2.symm h_eq
        simp at hh; cases hh
        apply h3 (h0 hs <| run_append h₁ h₂) h_run
    · apply ht ⟨w, p⟩ cst (h0 hs <| run_append h₁ h₂) h

def shiftRight (w : B256) : Line := [pushB256 w, shr]

def fsig : Line := cdl 0 ++ shiftRight 224

def Func.main (dt : DispatchTree) : Func := fsig +++ dispatch dt
def Func.mainWith (k : Nat) (dt : DispatchTree) : Func := fsig +++ dispatchWith k dt

def isMax : Line := [not, iszero]

syntax "rcases_append" : tactic
macro_rules
| `(tactic| rcases_append) =>
  `(tactic|
    rename Line.Run _ _ _ _ => h_run;
    rcases of_run_append _ h_run with ⟨s', hs', h_run'⟩; clear h_run)

lemma Stack.push_of_cdl {n} {e s s'} :
    Line.Run e s (cdl n) s' → ∃ x, Stack.Push [x] s.stk s'.stk := by
  lexen 1; intro h₂
  have h_push : Push [n] s.stk s₁.stk :=
    (of_run_pushB256 <| of_run_singleton h₁).stk
  rcases (of_run_singleton' h₂) with ⟨_, x, h_diff, _⟩
  rcases h_diff.stk with ⟨stk, h_pop, h_push'⟩
  have h_eq : s.stk = stk :=
    List.append_inj_right (Eq.trans h_push.symm h_pop) rfl
  rw [h_eq]; refine ⟨x, h_push'⟩

lemma Desc.push_of_cdl {e s w s'} (h : Line.Run e s (cdl w) s') :
    ∃ x, Desc.Push [x] s s' := by
  rcases Stack.push_of_cdl h with ⟨x, h'⟩
  refine' ⟨x, _, _, _, h', _, _, _⟩ <;>
  simp only [Desc.Rels.dft] <;>
  apply Line.of_inv _ _ asm <;> line_inv

lemma Desc.of_diff {xs ys} {s s''} (h : Desc.Diff xs ys s s'') :
    ∃ s', Desc.Pop xs s s' ∧ Desc.Push ys s' s'' := by
  rcases h.stk with ⟨stk, h_pop, h_push⟩
  refine' ⟨{s with stk := stk}, _, _⟩
  · refine ⟨rfl, rfl, rfl, h_pop, rfl, rfl, rfl⟩
  · cases h; refine' ⟨asm, asm, asm, h_push, asm, asm, asm⟩

lemma Desc.of_pop_cons {x xs} {s s''} (h : Desc.Pop (x :: xs) s s'') :
    ∃ s', Desc.Pop [x] s s' ∧ Desc.Pop xs s' s'' := by
  rcases List.of_cons_split h.stk with ⟨stk, h_eq, h_split⟩
  refine' ⟨{s with stk := stk}, _, _⟩
  · refine' ⟨rfl, rfl, rfl, h_eq, rfl, rfl, rfl⟩
  · cases h; refine' ⟨asm, asm, asm, h_split, asm, asm, asm⟩

lemma kec_elim {e s s'} (φ : Prop)
    (h : ∀ x, Line.Run e s [pop, pop, pushB256 x] s' → φ)
    (h' : Ninst.Run e s kec s') : φ := by
  rcases opRun_of_instRun h' with ⟨x, y, h_diff⟩
  apply h (s.mem.slice x y).keccak
  rcases Desc.of_diff h_diff with ⟨s₁, h_pop, h_push⟩
  rcases Desc.of_pop_cons h_pop with ⟨s₀, hx, hy⟩
  apply Line.Run.cons <| run_pop e hx
  apply Line.Run.cons <| run_pop e hy
  apply Line.Run.cons (run_pushB256 e h_push) cst

lemma kec_cons_elim {e s l s'} (φ : Prop)
    (h : ∀ x, Line.Run e s (pop :: pop :: pushB256 x :: l) s' → φ) :
    Line.Run e s (kec :: l) s' → φ := by
  lexen 1; apply kec_elim _ _ <| of_run_singleton h₁
  intro x h₂ h₃; apply h x <| run_append h₂ h₃

lemma kec_next_elim {e s p s'} (φ : Prop)
    (h : ∀ x, Func.Run c e s (pop ::: pop ::: pushB256 x ::: p) s' → φ) :
    Func.Run c e s (kec ::: p) s' → φ := by
  pexen 1; apply kec_elim _ _ <| of_run_singleton h₁
  intro x h₂ h₃; apply h x <| run_prepend h₂ h₃

lemma prepend_kec_next_elim {e s} (l) {p r} (φ : Prop)
    (h : ∀ x, Func.Run c e s (l +++ pop ::: pop ::: pushB256 x ::: p) r → φ) :
    Func.Run c e s (l +++ kec ::: p) r → φ := by
  pexec l; apply kec_next_elim
  intro x h'; apply h x <| run_prepend h₁ h'

lemma cdl_append_elim {e s n l r} (φ : Prop)
    (h : ∀ x, Line.Run e s (pushB256 x :: l) r → φ) :
    Line.Run e s (cdl n ++ l) r → φ := by
  lexec (cdl n); intro h₂
  rcases Desc.push_of_cdl h₁ with ⟨x, hp₁⟩
  apply h x <| .cons (run_pushB256 _ hp₁) h₂

lemma cdl_prepend_elim {c e s n p r} (φ : Prop)
    (h : ∀ x, Func.Run c e s (pushB256 x ::: p) r → φ) :
    Func.Run c e s (cdl n +++ p) r → φ := by
  pexec (cdl n); intro h₂
  rcases Desc.push_of_cdl h₁ with ⟨x, hp₁⟩
  apply h x <| .next (run_pushB256 _ hp₁) h₂

lemma sload_elim {e s s'} (φ : Prop)
    (h : ∀ x, Line.Run e s [pop, pushB256 x] s' → φ)
    (h' : Ninst.Run e s sload s') : φ := by
  rcases opRun_of_instRun h' with ⟨x, hx⟩
  rcases Desc.of_diff hx with ⟨s₀, h_pop, h_push⟩
  apply h (s.stor e.cta x);
  apply Line.Run.cons (run_pop e h_pop)
  apply Line.Run.cons (run_pushB256 e h_push) cst

lemma sload_cons_elim {e s l s'} (φ : Prop)
    (h : ∀ x, Line.Run e s (pop :: pushB256 x :: l) s' → φ) :
    Line.Run e s (sload :: l) s' → φ := by
  lexen 1; apply sload_elim _ _ <| of_run_singleton h₁
  intro x h₂ h₃; apply h x <| run_append h₂ h₃

lemma append_sload_cons_elim {e s} (a) {b s'} (φ : Prop)
    (h : ∀ x, Line.Run e s (a ++ pop :: pushB256 x :: b) s' → φ) :
    Line.Run e s (a ++ sload :: b) s' → φ := by
  lexec a; apply sload_cons_elim
  intro x h'; apply h x <| run_append h₁ h'

lemma sload_next_elim {e s p r} (φ : Prop)
    (h : ∀ x, Func.Run c e s (pop ::: pushB256 x ::: p) r → φ) :
    Func.Run c e s (sload ::: p) r → φ := by
  pexen 1; apply sload_elim _ _ <| of_run_singleton h₁
  intro x h₂ h₃; apply h x <| run_prepend h₂ h₃

lemma prepend_sload_next_elim {e s} (l) {p r} (φ : Prop)
    (h : ∀ x, Func.Run c e s (l +++ pop ::: pushB256 x ::: p) r → φ) :
    Func.Run c e s (l +++ sload ::: p) r → φ := by
  pexec l; apply sload_next_elim
  intro x h'; apply h x <| run_prepend h₁ h'

lemma prepend_cdl_prepend_elim {e s} (l) {n p r} (φ : Prop)
    (h : ∀ x, Func.Run c e s (l +++ pushB256 x ::: p) r → φ) :
    Func.Run c e s (l +++ cdl n +++ p) r → φ := by
  pexec l; pexec (cdl n); intro h₃
  rcases Desc.push_of_cdl h₂ with ⟨x, hp₂⟩
  apply h x <| run_prepend h₁ <| .next (run_pushB256 _ hp₂) h₃

lemma of_nof_of_transfer {a b : Adr} {v : B256} {f h : Adr → B256}
    (h_nof : SumNof f) (h_di : Transfer f a v b h) :
    ∃ g, Decrease a v f g ∧ Increase b v g h ∧ B256.Nof (g b) v := by
  rcases h_di with ⟨h_le, g, hd, hi⟩; refine' ⟨g, hd, hi, _⟩
  apply lt_of_le_of_lt _ h_nof
  by_cases h_ab : a = b
  · rw [← (hd b).left h_ab, ← h_ab, B256.toNat_sub_eq_of_le _ _ h_le]
    rw [Nat.sub_add_cancel (B256.toNat_le_toNat h_le)]
    exact le_sum
  · rw [← (hd b).right h_ab, Nat.add_comm]
    apply _root_.le_trans (Nat.add_le_add_right _ _) <| add_le_sum_of_ne f h_ab
    apply B256.toNat_le_toNat h_le

lemma B256.le_add_right {xs ys : B256} (h : B256.Nof xs ys) : xs ≤ xs + ys := by
  rw [B256.le_iff_toNat_le_toNat, B256.toNat_add_eq_of_nof _ _ h]; simp

lemma le_of_increase {k : Adr} {v : B256} {f g : Adr → B256}
    (h : Increase k v f g) (h' : B256.Nof (f k) v) : ∀ k', f k' ≤ g k' := by
  intro k'; by_cases h_eq : k = k'
  · rw [← h_eq]
    have h_rw : f k + v = g k := (h k).left rfl
    rw [← h_rw]; apply B256.le_add_right h'
  · rw [(h k').right h_eq]--apply B256.le_refl

-- lemma Nat.add_div_of_dvd {a b c : Nat} (c_pos : 0 < c) (c_dvd : c ∣ a)  :
--     (a + b) / c = a / c + b / c := by
--   rw [Nat.add_div c_pos, if_neg, Nat.add_zero]
--   rw [not_le, Nat.mod_eq_zero_of_dvd c_dvd, Nat.zero_add]
--   apply Nat.mod_lt _ c_pos
--
-- lemma Nat.add_div_of_dvd_of_lt' {a b c : Nat} (c_dvd : c ∣ a) (b_lt : b < c) :
--     (a + b) / c = a / c := by
--   rw [Nat.add_div_of_dvd (zero_lt_of_lt b_lt) c_dvd]
--   simp [Nat.div_eq_zero_of_lt b_lt]

-- lemma toUInt64_add (a b : Nat) :
--     (a + b).toUInt64 = a.toUInt64 + b.toUInt64 := UInt64.ofNat_add a b

-- lemma toB128_add (a b : Nat) : (a + b).toB128 = a.toB128 + b.toB128 := by
--   simp only [Nat.toB128]
--   rw [Nat.add_div (by omega)]
--   apply congr_arg₂ _ _ <| Eq.trans (UInt64.ofNat_add _ _) rfl
--   simp only [toUInt64_add]
--   apply congr_arg₂ _ rfl
--   have iff :
--       a.toUInt64 + b.toUInt64 < a.toUInt64
--         ↔ 2 ^ 64 ≤ a % 2 ^ 64 + b % 2 ^ 64 := by
--     rw [B64.toNat_overflow, toNat_toUInt64, toNat_toUInt64]
--   by_cases h : a.toUInt64 + b.toUInt64 < a.toUInt64
--   · rw [if_pos h, if_pos (iff.mp h)]; rfl
--   · rw [if_neg h, if_neg (mt iff.mpr h)]; rfl
--
-- lemma toB128_toNat (x : B128) : x.toNat.toB128 = x := by
--   simp only [B128.toNat, Nat.toB128]
--   apply congr_arg₂
--   · rw [Nat.add_div_of_dvd_of_lt' (by omega) (UInt64.toNat_lt_pow _)]
--     rw [Nat.mul_div_cancel _ (by omega)]; apply UInt64.ofNat_toNat
--   · apply Eq.trans (UInt64.ofNat_add _ _)
--     rw [(UInt64.ofNat_eq_iff_mod_eq_toNat (x.1.toNat * 2 ^ 64) 0).mpr _]
--     · simp
--     · rw [Nat.mod_eq_zero_of_dvd (by omega)]; rfl
--
-- lemma B128.toNat_inj (xs ys : B128) (eq : xs.toNat = ys.toNat) : xs = ys := by
--   rw [← toB128_toNat xs, ← toB128_toNat ys, eq]
--
lemma toB128_eq_iff_mod_eq_toNat (a : Nat) (b : B128) :
    a.toB128 = b ↔ a ↾ 128 = b.toNat := by
  constructor <;> intro h
  · rw [← h, toNat_toB128]
  · rw [← B128.toNat_inj, ← h, toNat_toB128]

-- lemma B128.zero_1 : (0 : B128).1 = 0 := rfl
-- lemma B128.zero_2 : (0 : B128).2 = 0 := rfl

-- lemma B128.zero_add (n : B128) : 0 + n = n := by
--   rw [B128.add_eq]; simp [B128.zero_1, B128.zero_2]
--
-- lemma toB256_toNat (x : B256) : x.toNat.toB256 = x := by
--   simp only [B256.toNat, Nat.toB256]
--   apply congr_arg₂
--   · rw [Nat.add_div_of_dvd_of_lt' (by omega) (B128.toNat_lt_size _)]
--     rw [Nat.mul_div_cancel _ (by omega)]; apply toB128_toNat
--   · apply Eq.trans (toB128_add _ _)
--     rw [(toB128_eq_iff_mod_eq_toNat (x.1.toNat * 2 ^ 128) 0).mpr _]
--     · rw [B128.zero_add, toB128_toNat]
--     · rw [Nat.mod_eq_zero_of_dvd (by omega)]; rfl

-- theorem B256.toNat_inj (xs ys : B256) (eq : xs.toNat = ys.toNat) : xs = ys := by
--   rw [← toB256_toNat xs, ← toB256_toNat ys, eq]
--
-- lemma toB256_add (a b : Nat) : (a + b).toB256 = a.toB256 + b.toB256 := by
--   simp only [Nat.toB256]
--   rw [Nat.add_div (by omega)]
--   apply congr_arg₂ _ _ <| Eq.trans (toB128_add _ _) rfl
--   simp only [toB128_add]
--   apply congr_arg₂ _ rfl
--   have iff :
--       a.toB128 + b.toB128 < a.toB128
--         ↔ 2 ^ 128 ≤ a % 2 ^ 128 + b % 2 ^ 128 := by
--     rw [B128.toNat_overflow, toNat_toB128, toNat_toB128]
--   by_cases h : a.toB128 + b.toB128 < a.toB128
--   · rw [if_pos h, if_pos (iff.mp h)]; rfl
--   · rw [if_neg h, if_neg (mt iff.mpr h)]; rfl
--
-- theorem B256.add_comm {xs ys : B256} : xs + ys = ys + xs := by
--   apply B256.toNat_inj
--   rw [B256.toNat_add, B256.toNat_add, Nat.add_comm]
--
-- theorem Adr.toB256_inj {xs ys : Adr} (eq : xs.toB256 = ys.toB256) : xs = ys := by
--   rw [← toAdr_toB256 xs, ← toAdr_toB256 ys, eq]
--
-- theorem B256.sub_add_cancel {x y : B256} : x - y + y = x := by
--   apply B256.toNat_inj
--   simp only [B256.toNat_add, B256.toNat_sub]
--   have x_lt : x.toNat < 2 ^ 256 := B256.toNat_lt_size _
--   have y_lt : y.toNat < 2 ^ 256 := B256.toNat_lt_size _
--   revert x_lt
--   revert y_lt
--   generalize x.toNat = x
--   generalize y.toNat = y
--   intros y_lt x_lt
--   by_cases h : x < y
--   · rw [@Nat.mod_eq_of_lt (2 ^ 256 + x - y) _ (by omega)]
--     rw [Nat.sub_add_cancel (by omega)]
--     rw [Nat.add_mod_left, Nat.mod_eq_of_lt x_lt]
--   · rw [Nat.not_lt] at h
--     rw [Nat.add_sub_assoc h, Nat.add_mod_left]
--     rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
--     apply Nat.sub_add_cancel h
--
