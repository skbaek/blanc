-- Common.lean : definitions and lemmas generally useful for writing and
-- verifying Blanc programs, including a correctness proof for the Blanc
-- compiler and tactics for automating Blanc program verification.

import Blanc.Semantics
import Mathlib.Data.List.Lemmas



def Rinst.toString : Rinst → String
  | add => "ADD"
  | mul => "MUL"
  | sub => "SUB"
  | div => "DIV"
  | sdiv => "SDIV"
  | mod => "MOD"
  | smod => "SMOD"
  | addmod => "ADDMOD"
  | mulmod => "MULMOD"
  | exp => "EXP"
  | signextend => "SIGNEXTEND"
  | lt => "LT"
  | gt => "GT"
  | slt => "SLT"
  | sgt => "SGT"
  | eq => "EQ"
  | iszero => "ISZERO"
  | and => "AND"
  | or => "OR"
  | xor => "XOR"
  | not => "NOT"
  | byte => "BYTE"
  | shr => "SHR"
  | shl => "SHL"
  | sar => "SAR"
  | kec => "KEC"
  | address => "ADDRESS"
  | balance => "BALANCE"
  | origin => "ORIGIN"
  | caller => "CALLER"
  | callvalue => "CALLVALUE"
  | calldataload => "CALLDATALOAD"
  | calldatasize => "CALLDATASIZE"
  | calldatacopy => "CALLDATACOPY"
  | codesize => "CODESIZE"
  | codecopy => "CODECOPY"
  | gasprice => "GASPRICE"
  | extcodesize => "EXTCODESIZE"
  | extcodecopy => "EXTCODECOPY"
  | retdatasize => "RETDATASIZE"
  | retdatacopy => "RETDATACOPY"
  | extcodehash => "EXTCODEHASH"
  | blockhash => "BLOCKHASH"
  | coinbase => "COINBASE"
  | timestamp => "TIMESTAMP"
  | number => "NUMBER"
  | prevrandao => "PREVRANDAO"
  | gaslimit => "GASLIMIT"
  | chainid => "CHAINID"
  | selfbalance => "SELFBALANCE"
  | basefee => "BASEFEE"
  | pop => "POP"
  | mload => "MLOAD"
  | mstore => "MSTORE"
  | mstore8 => "MSTORE8"
  | sload => "SLOAD"
  | sstore => "SSTORE"
  | pc => "PC"
  | msize => "MSIZE"
  | gas => "GAS"
  | dup n => "DUP " ++ n.val.repr
  | swap n => "SWAP " ++ n.val.repr
  | log n => "LOG " ++ n.val.repr
  | invalid => "INVALID"

def Xinst.toString : Xinst → String
  | create => "CREATE"
  | call => "CALL"
  | callcode => "CALLCODE"
  | delcall => "DELEGATECALL"
  | create2 => "CREATE2"
  | statcall => "STATCALL"

def Hinst.toString : Hinst → String
  | .stop => "STOP"
  | .dest => "SELFDESTRUCT"
  | .rev => "REVERT"
  | .ret => "RETURN"

instance : Repr Rinst := ⟨λ o _ => o.toString⟩
instance : Repr Xinst := ⟨λ o _ => o.toString⟩

def Inst.toString : Inst → String
  | reg o => Rinst.toString o
  | exec o => Xinst.toString o
  | push ⟪⟫ _ => "PUSH0"
  | push bs _ => "PUSH" ++ bs.length.repr ++ " " ++ Bytes.toString bs

instance : ToString Inst := ⟨Inst.toString⟩
instance : Repr Inst := ⟨λ i _ => i.toString⟩

def Func.toString : Func → String
  | .last o => Hinst.toString o ++ " ::."
  | .next o p => o.toString ++ " ::: " ++ p.toString
  | .branch p q => "{" ++ q.toString ++ "} <?> {" ++ p.toString ++ "}"
  | .call _ => "[TAIL]"

instance : Repr Func := ⟨λ p _ => Func.toString p⟩

def Char.toHex : Char → Hex
  | '0' => x0
  | '1' => x1
  | '2' => x2
  | '3' => x3
  | '4' => x4
  | '5' => x5
  | '6' => x6
  | '7' => x7
  | '8' => x8
  | '9' => x9
  | 'A' => xA
  | 'B' => xB
  | 'C' => xC
  | 'D' => xD
  | 'E' => xE
  |  _  => xF

def Chars.toRevBits : ∀ n, List Char → Bits (4 * n)
  | 0, _ => ⦃⦄
  | _ + 1, [] => 0
  | n + 1, c :: cs => Chars.toRevBits n cs ++ Char.toHex c

def String.toBits (n) (s : String) : Bits (4 * n) := Chars.toRevBits n s.data.reverse

def String.toWord : String → Word := String.toBits 64

def Func.stop : Func := .last .stop
def Func.rev : Func := .last .rev
def Func.ret : Func := .last .ret

def Inst.pushWord (w : Word) : Inst :=
  Inst.push
    (@Bits.toBytes 32 w).sig
    (le_of_le_of_eq (Bytes.sig_length_le _) (Bits.toBytes_length _))

abbrev Inst.add : Inst := Inst.reg Rinst.add
abbrev Inst.mul : Inst := Inst.reg Rinst.mul
abbrev Inst.sub : Inst := Inst.reg Rinst.sub
abbrev Inst.div : Inst := Inst.reg Rinst.div
abbrev Inst.sdiv : Inst := Inst.reg Rinst.sdiv
abbrev Inst.mod : Inst := Inst.reg Rinst.mod
abbrev Inst.smod : Inst := Inst.reg Rinst.smod
abbrev Inst.addmod : Inst := Inst.reg Rinst.addmod
abbrev Inst.mulmod : Inst := Inst.reg Rinst.mulmod
abbrev Inst.exp : Inst := Inst.reg Rinst.exp
abbrev Inst.signextend : Inst := Inst.reg Rinst.signextend
abbrev Inst.lt : Inst := Inst.reg Rinst.lt
abbrev Inst.gt : Inst := Inst.reg Rinst.gt
abbrev Inst.slt : Inst := Inst.reg Rinst.slt
abbrev Inst.sgt : Inst := Inst.reg Rinst.sgt
abbrev Inst.eq : Inst := Inst.reg Rinst.eq
abbrev Inst.iszero : Inst := Inst.reg Rinst.iszero
abbrev Inst.and : Inst := Inst.reg Rinst.and
abbrev Inst.or : Inst := Inst.reg Rinst.or
abbrev Inst.xor : Inst := Inst.reg Rinst.xor
abbrev Inst.not : Inst := Inst.reg Rinst.not
abbrev Inst.byte : Inst := Inst.reg Rinst.byte
abbrev Inst.shr : Inst := Inst.reg Rinst.shr
abbrev Inst.shl : Inst := Inst.reg Rinst.shl
abbrev Inst.sar : Inst := Inst.reg Rinst.sar
abbrev Inst.kec : Inst := Inst.reg Rinst.kec
abbrev Inst.address : Inst := Inst.reg Rinst.address
abbrev Inst.balance : Inst := Inst.reg Rinst.balance
abbrev Inst.origin : Inst := Inst.reg Rinst.origin
abbrev Inst.caller : Inst := Inst.reg Rinst.caller
abbrev Inst.callvalue : Inst := Inst.reg Rinst.callvalue
abbrev Inst.calldataload : Inst := Inst.reg Rinst.calldataload
abbrev Inst.calldatasize : Inst := Inst.reg Rinst.calldatasize
abbrev Inst.calldatacopy : Inst := Inst.reg Rinst.calldatacopy
abbrev Inst.codesize : Inst := Inst.reg Rinst.codesize
abbrev Inst.codecopy : Inst := Inst.reg Rinst.codecopy
abbrev Inst.gasprice : Inst := Inst.reg Rinst.gasprice
abbrev Inst.extcodesize : Inst := Inst.reg Rinst.extcodesize
abbrev Inst.extcodecopy : Inst := Inst.reg Rinst.extcodecopy
abbrev Inst.retdatasize : Inst := Inst.reg Rinst.retdatasize
abbrev Inst.retdatacopy : Inst := Inst.reg Rinst.retdatacopy
abbrev Inst.extcodehash : Inst := Inst.reg Rinst.extcodehash
abbrev Inst.blockhash : Inst := Inst.reg Rinst.blockhash
abbrev Inst.coinbase : Inst := Inst.reg Rinst.coinbase
abbrev Inst.timestamp : Inst := Inst.reg Rinst.timestamp
abbrev Inst.number : Inst := Inst.reg Rinst.number
abbrev Inst.prevrandao : Inst := Inst.reg Rinst.prevrandao
abbrev Inst.gaslimit : Inst := Inst.reg Rinst.gaslimit
abbrev Inst.chainid : Inst := Inst.reg Rinst.chainid
abbrev Inst.selfbalance : Inst := Inst.reg Rinst.selfbalance
abbrev Inst.basefee : Inst := Inst.reg Rinst.basefee
abbrev Inst.pop : Inst := Inst.reg Rinst.pop
abbrev Inst.mload : Inst := Inst.reg Rinst.mload
abbrev Inst.mstore : Inst := Inst.reg Rinst.mstore
abbrev Inst.mstore8 : Inst := Inst.reg Rinst.mstore8
abbrev Inst.sload : Inst := Inst.reg Rinst.sload
abbrev Inst.sstore : Inst := Inst.reg Rinst.sstore
abbrev Inst.pc : Inst := Inst.reg Rinst.pc
abbrev Inst.msize : Inst := Inst.reg Rinst.msize
abbrev Inst.gas : Inst := Inst.reg Rinst.gas
abbrev Inst.dup (n : Fin 16) : Inst := Inst.reg (Rinst.dup n)
abbrev Inst.swap (n : Fin 16) : Inst := Inst.reg (Rinst.swap n)
abbrev Inst.log (n : Fin 5) : Inst := Inst.reg (Rinst.log n)
abbrev Inst.create : Inst := Inst.exec Xinst.create
abbrev Inst.call : Inst := Inst.exec Xinst.call
abbrev Inst.callcode : Inst := Inst.exec Xinst.callcode
abbrev Inst.delcall : Inst := Inst.exec Xinst.delcall
abbrev Inst.create2 : Inst := Inst.exec Xinst.create2
abbrev Inst.statcall : Inst := Inst.exec Xinst.statcall

abbrev Line : Type := List Inst

def prepend : Line → Func → Func
  | [], x => x
  | i :: is, x => i ::: prepend is x

infixr:65 " +++ " => prepend

inductive Line.Run : Env → State → Line → State → Prop
  | nil : ∀ {e s}, Line.Run e s [] s
  | cons :
    ∀ {e s i s' l s''},
      Inst.Run e s i s' →
      Line.Run e s' l s'' →
      Line.Run e s (i :: l) s''

open Inst

def mstoreAt (x : Word) : Line := [pushWord (x * 32), mstore]

-- assumes : k = # of indexed items (max 3)
-- assumes : Stack = ev_sig :: idx_item_0 ... idx_item_{k-1}
-- assumes : mem[x * 32, (x + y) * 32 - 1] = unindexed data
def logWith (k : Fin 4) (x y : Word) : Line :=
  pushWord (y * 32) :: pushWord (x * 32) :: -- x * 32 :: y * 32 :: ev_sig :: idx_item_0 ... idx_item_{k+1}
  log k.succ :: []

-- cdc X Y Z := calldatacopy(X, Y, Z)
-- I.e., look at the calldata, skip its first Y bytes,
-- and copy the next Z bytes into location X of memory.
def cdc (x y z : Word) : Line :=
  pushWord z :: -- z
  pushWord y :: -- y :: z
  pushWord x :: -- x :: y :: z
  calldatacopy :: []

def argCopy (x y z : Word) : Line :=
  cdc (x * 32) ((y * 32) + 4) (z * 32)

def pushList : List Word → Line := List.map pushWord

def returnMemoryRange (x y : Word) : Func := pushList [y, x] +++ Func.ret

def cdl (x : Word) : Line := [pushWord x, calldataload]

def arg (k : Word) : Line := cdl ((32 * k) + 4)

-- Push a 256-bit word used for testing address validity.
-- NOT and SHL are used so it takes up only 6 bytes of code,
-- whereas pushing the value directly would take up 32.

def Nat.toWord : Nat → Word := Nat.toBits 256

def pushAddressMask : Line := [pushWord 0, not, pushWord (160 : Nat).toWord, shl]

-- ( adr -- adr_invalid? )
def checkNonAddress : Line := pushAddressMask ++ [Inst.and]

-- ( adr -- adr_valid? )
def checkAddress : Line := checkNonAddress ++ [iszero]

def returnTrue : Func :=
  pushWord 1 ::: mstoreAt 0 +++ -- || 1
  pushList [32, 0] +++ -- 0 :: 32 || 1
  Func.ret

abbrev Exec.Pred : Type :=
  ∀ e s pc r, Exec e s pc r → Prop

abbrev Prog.Pred : Type := Env → State → Prog → Result → Prop

def Exec.Fa (π : Exec.Pred) : Prop :=
  ∀ e s pc r (ex : Exec e s pc r), π _ _ _ _ ex

def Fortify (π : Exec.Pred) : Exec.Pred :=
  λ e _ _ _ ex =>
    (Exec.Fa <| λ e' _ _ _ ex' => e'.exd < e.exd → π _ _ _ _ ex') → π _ _ _ _ ex

lemma Exec.strong_rec (π : Exec.Pred)
  (h_fa : Exec.Fa (Fortify π)) : Exec.Fa π := by
  intros e s pc r ex
  apply
    @Nat.strongRecOn
      (λ n => ∀ e_ s_ pc_ r_ (ex_ : Exec e_ s_ pc_ r_), n = e_.exd → π _ _ _ _ ex_)
      e.exd
  · intros n h e_ s_ pc_ r_ ex_ h_eq; apply h_fa
    intros e' s' pc' r' ex' h_lt; rw [← h_eq] at h_lt
    apply h e'.exd h_lt _ _ _ _ ex' rfl
  · rfl

lemma frel_of_frel {ξ υ} {x : ξ} {r s : υ → υ → Prop} {f g : ξ → υ}
    (h : r (f x) (g x) → s (f x) (g x)) (h' : Frel x r f g) : Frel x s f g := by
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
    (h : Inst.Run e s (Inst.reg o) s') : Rinst.Run e s o s' := by cases h; assumption

lemma of_run_singleton {e s i s'} (h : Line.Run e s [i] s') : Inst.Run e s i s' := by
  rcases Line.of_run_cons h with ⟨_, _, ⟨_⟩⟩; assumption

lemma of_run_singleton' {e s o s'} (h : Line.Run e s [Inst.reg o] s') :
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

lemma of_run_last {o : Hinst} {c e s r} (h : (o ::.).Run c e s r) : o.Run e s r := by
  cases h; assumption

lemma of_run_next {c e} {s : State} {i} {p : Func} {r}
    (h : Func.Run c e s (i ::: p) r) :
    ∃ s', (Inst.Run e s i s' ∧ Func.Run c e s' p r) := by
  cases h; rename State => s'; refine ⟨s', asm, asm⟩

lemma of_run_branch {e s r} {p q : Func} (h : Func.Run c e s (q <?> p) r) :
    (∃ s', State.Pop [0] s s' ∧ Func.Run c e s' p r) ∨
    (∃ w s', w ≠ 0 ∧ State.Pop [w] s s' ∧ Func.Run c e s' q r) := by
  cases h
  · left; refine ⟨_, asm, asm⟩
  · right; refine ⟨_, _, asm, asm, asm⟩

lemma run_pop (e) {x s s'} (h : State.Pop [x] s s') : Run e s pop s' :=
  Inst.Run.reg ⟨x, h⟩

lemma of_run_branch' {c e s r} {p q : Func} (h : Func.Run c e s (q <?> p) r) :
    ([0] <<+ s.stk ∧ Func.Run c e s (pop ::: p) r) ∨
    ((∃ w, w ≠ 0 ∧ [w] <<+ s.stk) ∧ Func.Run c e s (pop ::: q) r) := by
  rcases of_run_branch h with ⟨s', h', h''⟩ | ⟨w, s', hw, h', h''⟩
  · left; refine' ⟨⟨s'.stk, h'.stk⟩, Func.Run.next (run_pop _ h') h''⟩
  · right; refine' ⟨⟨w, hw, s'.stk, h'.stk⟩, Func.Run.next (run_pop _ h') h''⟩

lemma of_and_mask_low_eq_zero {m n} :
   ∀ (xs : Bits (m + n)),
     Bits.and (Bits.max m ++ Bits.zero n) xs = 0 →
     ∃ ys : Bits n, (Bits.zero m ++ ys) = xs := by
  induction n generalizing m with
  | zero =>
    simp;
    intros xs h
    refine' ⟨⦃⦄, _⟩
    simp [Bits.zero, Bits.append_nil] at h
    rw [Bits.max_and] at h
    simp [Bits.append_nil]
    apply h.symm
  | succ n ih =>
    -- simp [Nat.add_succ]
    intros xs h;
    cases xs with
    | cons xs x =>
      simp [Bits.zero, Bits.append_cons, Bits.cons_and_cons] at h
      rw [Bits.cons_eq_zero] at h
      rcases ih _ h.left with ⟨ys, h_ys⟩
      refine' ⟨ys +> x, _⟩
      rw [Bits.append_cons, h_ys]

-- the mask 0xffffffffffffffffffffffff0000000000000000000000000000000000000000,
-- for checking that a given word is a valid Ethereum addresses
def addressMask : Word := (@Bits.max 96) ++ (@Bits.zero 160)

lemma shlo_max {m} : Bits.shlo (Bits.max (m + 1)) 0 = Bits.max m +> 0 := by
  induction m with
  | zero => simp [Bits.max, Bits.shlo]
  | succ m ih =>
    simp [Bits.max, Bits.shlo]
    simp [Bits.shlo] at ih
    apply ih

lemma shl_cons_zero {m n} (xs : Bits m) : Bits.shl n (xs +> 0) = Bits.shl n xs +> 0 := by
  induction n generalizing m xs with
  | zero => rfl
  | succ n ih =>
    simp [Bits.shl, Bits.shlo]
    rw [← @ih m (Bits.shlo xs 0)]

lemma max_append_zero_eq_shl_max {m n} :
    (@Bits.max m) ++ (@Bits.zero n) = Bits.shl n (@Bits.max (m + n)) := by
  induction n generalizing m with
  | zero =>
    simp only [Bits.zero, Bits.max, Bits.shl, Bits.append_nil, Nat.add_zero]
  | succ n ih =>
    simp only [Bits.zero, Bits.shl, Bits.append_cons]
    conv => rhs; arg 2; apply shlo_max
    rw [ih, shl_cons_zero]; rfl

lemma addressMask_eq_shl :
    addressMask = Bits.shl (160 : Nat).toWord.toNat (Bits.max 256) := by
  have h_lt : 160 < 2 ^ 256 := by simp
  simp only [Nat.toWord, toBits_toNat _ h_lt, addressMask]
  apply max_append_zero_eq_shl_max

def ValidAddr (w : Word) : Prop := ∃ a : Addr, a.toWord = w

def validAddr_toWord (a : Addr) : ValidAddr a.toWord := ⟨a, rfl⟩

lemma toAddr_toWord_eq {w : Word} :
    ValidAddr w → Addr.toWord (toAddr w) = w := by
  intro h; rcases h with ⟨a, ha⟩; rw [← ha, toWord_toAddr_eq]

lemma of_and_addressMask_eq_zero {w} :
  Bits.and addressMask w = 0 → ValidAddr w := by
  intro h0; simp [addressMask] at h0
  apply @of_and_mask_low_eq_zero 96 160 w h0

lemma and_addressMask_eq_zero {w} :
    ValidAddr w → Bits.and addressMask w = 0 := by
  simp [addressMask]; intro h; rcases h with ⟨a, ha⟩
  rw [← ha]; unfold Addr.toWord
  rw [Bits.append_and_append]
  rw [@Bits.zero_eq_append 96 160]
  rw [Bits.and_comm, Bits.zero_and]
  conv => lhs; arg 2; tactic => apply Bits.zero_and

lemma validAddr_iff {w} :
  ValidAddr w ↔ Bits.and addressMask w = 0 :=
⟨and_addressMask_eq_zero, of_and_addressMask_eq_zero⟩

instance {w} : Decidable (ValidAddr w) := by
  apply decidable_of_iff _ validAddr_iff.symm

lemma of_run_branch_rev {e s p r} (h : Func.Run c e s (.rev <?> p) r) :
    ∃ s', State.Pop [0] s s' ∧ Func.Run c e s' p r := by
  rcases of_run_branch h with h' | ⟨_, _, _, _, h'⟩
  · apply h'
  · cases of_run_last h'

lemma not_run_prepend_rev {e s l r} : ¬ Func.Run c e s (l +++ Func.rev) r := by
  intro h; rcases of_run_prepend _ _ h with ⟨_, _, h'⟩; cases of_run_last h'

lemma op_run_iff_inst_run {o} : Rinst.Run e s o s' ↔ Inst.Run e s (Inst.reg o) s' := by
  constructor
  · apply Inst.Run.reg
  · apply opRun_of_instRun

lemma of_run_push {e s s' xs p} (h : Inst.Run e s (push xs p) s') :
    State.Push [xs.toBits 32] s s' := by cases h with | push h => assumption

lemma of_run_pushWord {e s s' x} (h : Inst.Run e s (pushWord x) s') : State.Push [x] s s' := by
  cases h with | push h => rw [Bytes.sig_toBits, Bits.toBytes_toBits] at h; exact h

lemma run_pushWord (e) {s s' x} (h : State.Push [x] s s') : Inst.Run e s (pushWord x) s' := by
  apply Inst.Run.push; rw [Bytes.sig_toBits, Bits.toBytes_toBits]; exact h

lemma frel_of_sstore {e} {s s' : State} {x y xs}:
    State.Sstore e s s' → (x :: y :: xs <<+ s.stk) →
    (Frel e.cta (Overwrite x y) s.stor s'.stor) := by
  intros h0 h1
  rcases h0 with ⟨x', y', h2, h3⟩; clear h3
  have h3 : x = x' ∧ y = y' := by
    have h3 := Stack.pref_of_diff h2.stk
    rcases List.of_cons_pref_of_cons_pref h1 h3 with ⟨h4, stk, h5, h6⟩
    rcases List.of_cons_pref_of_cons_pref h5 h6 with ⟨h7, _⟩
    refine ⟨h4, h7⟩
  rw [h3.left, h3.right]; apply h2.stor

lemma of_run_call {e} {s s'} (h : Inst.Run e s .call s') :
    ( ∃ ep sp r,
        Xinst.Run' e s ep sp .call r s' ∧
        ((∃ (_ : Exec ep sp 0 r), True) ∨ PreRun sp r) ) ∨
    Fail s .call s' := by
  cases h; cases (asm : Xinst.Run _ _ _ _)
  · left; refine ⟨_, _, _, asm, .inl ⟨asm, cst⟩⟩
  · left; refine ⟨_, _, _, asm, .inr asm⟩
  · right; assumption

def Rinst.Inv {ξ : Type} (r : State → ξ) (o : Rinst) : Prop :=
  ∀ {e s s'}, Rinst.Run e s o s' → r s = r s'

def Jinst.Inv {ξ : Type} (r : State → ξ) (o : Jinst) : Prop :=
  ∀ {e s pc s' pc'}, Jinst.Run e s pc o s' pc' → r s = r s'

def Hinst.Inv {ξ : Type} (f : State → ξ) (g : Result → ξ) (o : Hinst) : Prop :=
  ∀ {e s r}, Hinst.Run e s o r → f s = g r

def Inst.Inv {ξ : Type} (r : State → ξ) (i : Inst) : Prop :=
  ∀ {e s s'}, Inst.Run e s i s' → r s = r s'

def Line.Inv {ξ : Type} (f : State → ξ) (l : Line) : Prop :=
  ∀ {e s s'}, l.Run e s s' → f s = f s'

def Func.Inv {ξ : Type} (f : State → ξ) (g : Result → ξ) (p : Func) : Prop :=
  ∀ {c e s r}, Func.Run c e s p r → f s = g r

def RelInv {X Y} (f : X → Y) (r : X → X → Prop) : Prop :=
  ∀ {x x'}, r x x' → f x = f x'

class Rinst.Hinv {ξ : Type} (f : State → ξ) (o : Rinst) := (inv : Rinst.Inv f o)
class Hinst.Hinv {ξ : Type} (f : State → ξ) (g : Result → ξ) (o : Hinst) := (inv : Hinst.Inv f g o)
class Inst.Hinv {ξ : Type} (f : State → ξ) (i : Inst) := (inv : Inst.Inv f i)

lemma fail_inv_bal {o : Xinst} : RelInv State.bal (Fail · o ·) := by
  intro s s'
  match o with
  | .create => simp [Fail]; intro _ _ _ h; apply h.bal
  | .call => simp [Fail]; intro _ _ _ _ _ _ _ h; apply h.bal
  | .callcode => simp [Fail]; intro _ _ _ _ _ _ _ h; apply h.bal
  | .delcall => simp [Fail]; intro _ _ _ _ _ _ h; apply h.bal
  | .create2 => simp [Fail]; intro _ _ _ _ h; apply h.bal
  | .statcall => simp [Fail]; intro _ _ _ _ _ _ h; apply h.bal

lemma fail_inv_stor {o : Xinst} : RelInv State.stor (Fail · o ·) := by
  intro s s'
  match o with
  | .create => simp [Fail]; intro _ _ _ h; apply h.stor
  | .call => simp [Fail]; intro _ _ _ _ _ _ _ h; apply h.stor
  | .callcode => simp [Fail]; intro _ _ _ _ _ _ _ h; apply h.stor
  | .delcall => simp [Fail]; intro _ _ _ _ _ _ h; apply h.stor
  | .create2 => simp [Fail]; intro _ _ _ _ h; apply h.stor
  | .statcall => simp [Fail]; intro _ _ _ _ _ _ h; apply h.stor

lemma fail_inv_code {o : Xinst} : RelInv State.code (Fail · o ·) := by
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
  | `(tactic| app_bal) =>  `(tactic| {have h' := State.Rel.bal asm; apply h'})

syntax "app_code" : tactic
macro_rules
  | `(tactic| app_code) => `(tactic| {have h' := State.Rel.code asm; apply h'})

syntax "app_stor" : tactic
macro_rules
  | `(tactic| app_stor) => `(tactic| {have h' := State.Rel.stor asm; rw[h']})

syntax "app_dest" : tactic
macro_rules
  | `(tactic| app_dest) => `(tactic| {have h' := State.Rel.dest asm; apply h'})

syntax "app_ret" : tactic
macro_rules
  | `(tactic| app_ret) => `(tactic| {have h' := State.Rel.ret asm; apply h'})

syntax "app_mem" : tactic
macro_rules
  | `(tactic| app_mem) => `(tactic| {have h' := State.Rel.mem asm; apply h'})

lemma Jinst.inv_bal {o} : Jinst.Inv State.bal o := by
  intros e s pc s' pc' h
  cases h <;> try {have h' := State.Rel.bal asm; apply h'}; rfl

lemma Jinst.inv_code {o} : Jinst.Inv State.code o := by
  intros e s pc s' pc' h
  cases h <;> try {have h' := State.Rel.code asm; apply h'}; rfl

lemma Jinst.inv_stor {o} : Jinst.Inv State.stor o := by
  intros e s pc s' pc' h
  cases h <;> try {have h' := State.Rel.stor asm; apply h'}; rfl

lemma Hinst.inv_stor {o} : Hinst.Inv State.stor Result.stor o := by intros e s r h; cases h <;> rfl
lemma Hinst.inv_code {o} : Hinst.Inv State.code Result.code o := by intros e s r h; cases h <;> rfl

lemma stop_inv_bal : Hinst.Inv State.bal Result.bal (Hinst.stop) := by intros e s r h; cases h; rfl
lemma ret_inv_bal : Hinst.Inv State.bal Result.bal Hinst.ret := by intros e s r h; cases h; rfl

instance {o} : Hinst.Hinv State.stor Result.stor o := ⟨Hinst.inv_stor⟩
instance {o} : Hinst.Hinv State.code Result.code o := ⟨Hinst.inv_code⟩

instance {ξ} {f g}: @Hinst.Hinv ξ f g Hinst.rev := by constructor; intros e s r h; cases h
instance : Hinst.Hinv State.bal Result.bal Hinst.ret := ⟨ret_inv_bal⟩
instance : Hinst.Hinv State.bal Result.bal Hinst.stop := ⟨stop_inv_bal⟩

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

instance : Rinst.Hinv State.mem Rinst.add := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.mul := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.sub := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.div := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.sdiv := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.mod := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.smod := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.addmod := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.mulmod := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.exp := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.signextend := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.lt := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.gt := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.slt := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.sgt := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.eq := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.iszero := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.and := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.or := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.xor := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.not := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.byte := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.shr := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.shl := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.sar := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.kec := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.address := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.balance := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.origin := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.caller := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.callvalue := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.calldataload := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.calldatasize := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.codesize := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.gasprice := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.extcodesize := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.retdatasize := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.extcodehash := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.blockhash := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.coinbase := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.timestamp := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.number := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.prevrandao := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.gaslimit := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.chainid := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.selfbalance := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.basefee := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.pop := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.mload := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.sload := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.sstore := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.pc := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.msize := by show_hinv_mem
instance : Rinst.Hinv State.mem Rinst.gas := by show_hinv_mem
instance {n} : Rinst.Hinv State.mem (Rinst.dup n) := by show_hinv_mem
instance {n} : Rinst.Hinv State.mem (Rinst.swap n) := by show_hinv_mem
instance {n} : Rinst.Hinv State.mem (Rinst.log n) := by
  match n with
  | ⟨0, _⟩ => show_hinv_mem
  | ⟨1, _⟩ => show_hinv_mem
  | ⟨2, _⟩ => show_hinv_mem
  | ⟨3, _⟩ => show_hinv_mem
  | ⟨4, _⟩ => show_hinv_mem
  | ⟨5, h⟩ => cases (Nat.lt_irrefl _ h)
instance : Rinst.Hinv State.mem Rinst.invalid := by constructor; intro _ _ _ h; cases h

instance : Rinst.Hinv State.stor Rinst.add := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.mul := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.sub := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.div := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.sdiv := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.mod := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.smod := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.addmod := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.mulmod := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.exp := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.signextend := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.lt := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.gt := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.slt := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.sgt := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.eq := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.iszero := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.and := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.or := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.xor := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.not := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.byte := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.shr := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.shl := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.sar := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.kec := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.address := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.balance := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.origin := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.caller := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.callvalue := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.calldataload := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.calldatasize := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.calldatacopy := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.codesize := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.codecopy := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.gasprice := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.extcodesize := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.extcodecopy := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.retdatasize := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.retdatacopy := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.extcodehash := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.blockhash := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.coinbase := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.timestamp := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.number := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.prevrandao := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.gaslimit := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.chainid := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.selfbalance := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.basefee := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.pop := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.mload := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.mstore := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.mstore8 := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.sload := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.pc := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.msize := by show_hinv_stor
instance : Rinst.Hinv State.stor Rinst.gas := by show_hinv_stor
instance {n} : Rinst.Hinv State.stor (Rinst.dup n) := by show_hinv_stor
instance {n} : Rinst.Hinv State.stor (Rinst.swap n) := by show_hinv_stor
instance {n} : Rinst.Hinv State.stor (Rinst.log n) := by
  match n with
  | ⟨0, _⟩ => show_hinv_stor
  | ⟨1, _⟩ => show_hinv_stor
  | ⟨2, _⟩ => show_hinv_stor
  | ⟨3, _⟩ => show_hinv_stor
  | ⟨4, _⟩ => show_hinv_stor
  | ⟨5, h⟩ => cases (Nat.lt_irrefl _ h)
instance : Rinst.Hinv State.stor Rinst.invalid := by constructor; intro _ _ _ h; cases h

lemma Rinst.inv_bal {o} : Rinst.Inv State.bal o := by
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

lemma Rinst.inv_code {o} : Rinst.Inv State.code o := by
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
  · cases h_run

lemma Rinst.inv_dest {o} : Rinst.Inv State.dest o := by
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

lemma Rinst.inv_ret {o} : Rinst.Inv State.ret o := by
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
  cases h <;> simp [State.prep]

lemma Xinst.code_eq_nil_of_run' {e s ep sp o rx sw}
    (h : Xinst.Run' e s ep sp o rx sw)
    (h' : ¬ o.isCall) : s.code ep.cta = ⟪⟫ := by
  cases h <;> try {apply (h' cst).elim} <;>
  {simp [Env.prep']; assumption}

lemma Xinst.wrap_inv_stor {e s ep sp o r sw}
    (h : Xinst.Run' e s ep sp o r sw) : r.stor = sw.stor := by
  cases h <;> try {simp [State.wrap']} <;> {simp [State.wrap]}

lemma Xinst.prep_inv_stor {e s ep sp o r sw}
    (h : Xinst.Run' e s ep sp o r sw) : s.stor = sp.stor := by
  cases h <;> simp [State.prep]

lemma Xinst.wrap_inv_bal {e s ep sp o r sw}
    (h : Xinst.Run' e s ep sp o r sw) : r.bal = sw.bal := by cases h <;> rfl

lemma Xinst.wrap_inv_code {e s ep sp o r sw}
    (h : Xinst.Run' e s ep sp o r sw) (h' : o.isCall) : r.code = sw.code := by
  cases h' <;> cases h <;> simp [State.wrap]

lemma Xinst.wrap_inv_code' {e s ep sp o r sw a}
    (h : Xinst.Run' e s ep sp o r sw) (h' : ep.cta ≠ a) : r.code a = sw.code a := by
  cases h <;> try {simp [State.wrap]} <;>
  {rename (Overwrite _ _ _ _) => h_ow; apply (h_ow a).right h'}

lemma Xinst.wrap_inv_code'' {a : Addr} {e s ep sp o r sw}
    (h : Xinst.Run' e s ep sp o r sw) (h' : s.code a ≠ ⟪⟫) : r.code a = sw.code a := by
  cases o <;> try {rw [Xinst.wrap_inv_code h cst]} <;>
  {apply Xinst.wrap_inv_code' h; intro hc; apply h'; rw [← hc]; cases h <;> assumption}

lemma Step.inv_code {e : Env} {s : State} {pc : ℕ} {s' : State} {pc' : ℕ}
    (h_step : Step e s pc s' pc') : s.code = s'.code := by
  cases h_step with
  | reg => exact Rinst.inv_code asm
  | pre =>
    rw [Xinst.prep_inv_code asm]
    apply Eq.trans <| PreRun.code asm
    apply Xinst.wrap_inv_code asm asm
  | fail => rw [fail_inv_code asm]
  | jump => rw [Jinst.inv_code asm]
  | push => rw [(asm : State.Push _ _ _).code]

lemma Exec.inv_code {a} :
    ∀ {e s pc r}, Exec e s pc r → s.code a ≠ ⟪⟫ → s.code a = r.code a := by
  apply
    @Exec.rec (λ e s pc r _ => s.code a ≠ ⟪⟫ → s.code a = r.code a)
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
    · rw [Hinst.inv_code asm]
    · rfl

lemma Xinst.inv_code {e s o s' a} (h : Xinst.Run e s o s')
    (h_ne : s.code a ≠ ⟪⟫) : s.code a = s'.code a := by
  cases h
  · have h := Xinst.prep_inv_code asm
    rw [h, Exec.inv_code asm _, Xinst.wrap_inv_code'' asm asm]
    rw [← h]; assumption
  · have h := PreRun.code asm
    have h' := Xinst.wrap_inv_code'' asm asm
    rw [Xinst.prep_inv_code asm, h, h']
  · rw [fail_inv_code asm]

lemma Inst.inv_code {e s i s' a} (h_run : Inst.Run e s i s')
    (h_ne : s.code a ≠ ⟪⟫) : s.code a = s'.code a := by
  cases h_run
  · rw [Rinst.inv_code asm]
  · rw [Xinst.inv_code asm h_ne]
  · rw [(asm : State.Push _ _ _).code]

lemma Line.nil_inv {ξ : Type} {f : State → ξ} : Line.Inv f [] := by
  intros e s s' h; cases h; rfl

lemma Line.cons_inv {ξ : Type} {f : State → ξ} {i l} :
    Inst.Inv f i → Line.Inv f l → Line.Inv f (i :: l) := by
  intros h0 h1 e s s'' h2
  rcases Line.of_run_cons h2 with ⟨s', h3, h4⟩
  apply Eq.trans (h0 h3) (h1 h4)

instance {ξ : Type} (f : State → ξ) (o : Rinst) [Rinst.Hinv f o] :
    Inst.Hinv f (Inst.reg o) := by
  constructor; intros e s s' h
  apply Rinst.Hinv.inv <| opRun_of_instRun h

instance {o : Rinst} : Rinst.Hinv State.bal o := ⟨Rinst.inv_bal⟩
instance {o : Rinst} : Rinst.Hinv State.code o := ⟨Rinst.inv_code⟩
instance {o : Rinst} : Rinst.Hinv State.ret o := ⟨Rinst.inv_ret⟩
instance {o : Rinst} : Rinst.Hinv State.dest o := ⟨Rinst.inv_dest⟩

instance {bs h_le} : Inst.Hinv State.bal (Inst.push bs h_le) := by
  constructor; intros e s s' h
  cases h with | push h => apply h.bal

instance {bs h_le} : Inst.Hinv State.code (Inst.push bs h_le) := by
  constructor; intros e s s' h
  cases h with | push h => apply h.code

instance {bs h_le} : Inst.Hinv State.stor (Inst.push bs h_le) := by
  constructor; intros e s s' h
  cases h with | push h => apply h.stor

instance {bs h_le} : Inst.Hinv State.ret (Inst.push bs h_le) := by
  constructor; intros e s s' h
  cases h with | push h => apply h.ret

instance {bs h_le} : Inst.Hinv State.dest (Inst.push bs h_le) := by
  constructor; intros e s s' h
  cases h with | push h => apply h.dest

instance {bs h_le} : Inst.Hinv State.mem (Inst.push bs h_le) := by
  constructor; intros e s s' h
  cases h with | push h => apply h.mem

syntax "show_pushWord_hinv" : tactic
macro_rules
  | `(tactic| show_pushWord_hinv) =>
    `(tactic| constructor; unfold Inst.pushWord; apply Inst.Hinv.inv)

instance {x} : Inst.Hinv State.bal (Inst.pushWord x) := by
  constructor; unfold Inst.pushWord; apply Inst.Hinv.inv

instance {x} : Inst.Hinv State.bal (Inst.pushWord x) := by show_pushWord_hinv
instance {x} : Inst.Hinv State.code (Inst.pushWord x) := by show_pushWord_hinv
instance {x} : Inst.Hinv State.stor (Inst.pushWord x) := by show_pushWord_hinv
instance {x} : Inst.Hinv State.mem (Inst.pushWord x) := by show_pushWord_hinv
instance {x} : Inst.Hinv State.ret (Inst.pushWord x) := by show_pushWord_hinv
instance {x} : Inst.Hinv State.dest (Inst.pushWord x) := by show_pushWord_hinv

open Qq

def Inst.inv_expr (ξx fx : Lean.Expr) (ix : Q(Inst)) : Lean.Elab.Tactic.TacticM Lean.Expr := do
  let x ← Lean.Meta.synthInstance <| Lean.mkApp3 q(@Inst.Hinv) ξx fx ix
  pure <| Lean.mkApp4 q(@Inst.Hinv.inv) ξx fx ix x

def Hinst.inv_expr (ξx fx gx : Lean.Expr) (ox : Q(Hinst)) :
    Lean.Elab.Tactic.TacticM Lean.Expr := do
  let x ← Lean.Meta.synthInstance <| Lean.mkApp4 q(@Hinst.Hinv) ξx fx gx ox
  pure <| Lean.mkApp5 q(@Hinst.Hinv.inv) ξx fx gx ox x

def hopInv : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
  let t ← Lean.Elab.Tactic.getMainTarget
  have t' : Q(Prop) := t
  match t' with
  | ~q(@Hinst.Inv $ξx $fx $gx $ox) =>
    let x ← Hinst.inv_expr ξx fx gx ox
    Lean.Elab.Tactic.closeMainGoal `tacName x
  | _ => dbg_trace "Not a Hinst.Inv goal"

def instInv : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
  let t ← Lean.Elab.Tactic.getMainTarget
  have t' : Q(Prop) := t
  match t' with
  | ~q(@Inst.Inv $ξx $fx $ix) =>
    let x ← Inst.inv_expr ξx fx ix
    Lean.Elab.Tactic.closeMainGoal `tacName x
  | _ => dbg_trace "Not a Inst.Inv goal"

lemma Line.of_inv {ξ : Type} {e s s'} (r : _root_.State → ξ) {l : Line} :
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
    (h : Inst.Inv f Inst.pop) (hp : Func.Inv f g p) (hq : Func.Inv f g q) :
    @Func.Inv ξ f g (q <?> p) := by
  intros c e s r h_run
  rcases of_run_branch h_run
    with ⟨s', h_pop, h_run⟩ | ⟨w, s', _, h_pop, h_run⟩ <;>
  apply Eq.trans (h <| run_pop e h_pop)
  · apply hp h_run
  · apply hq h_run

lemma next_inv {ξ : Type} {f : _root_.State → ξ} {g} {i p}
    (h : Inst.Inv f i) (h' : Func.Inv f g p) : Func.Inv f g (i ::: p) := by
  intros c e s r h_run
  rcases of_run_next h_run with ⟨s', hi, hp⟩
  rw [h hi, h' hp]

lemma last_inv {ξ} {f g o} (h : Hinst.Inv f g o) :
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
    (h_ne : s.code a ≠ ⟪⟫) : s.code a = r.code a := by
  induction h with
  | zero =>
    rename (_ ≠ _) → _ => ih
    have h := State.Rel.code asm
    rw [h , ih _]; rw [← h]; exact h_ne
  | succ =>
    rename (_ ≠ _) → _ => ih
    have h := State.Rel.code asm
    rw [h , ih _]; rw [← h]; exact h_ne
  | last => rw [Hinst.inv_code asm]
  | next =>
    rename (_ ≠ _) → _ => ih
    have h := Inst.inv_code asm h_ne
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

def comp {n} {ξ} (f : Bits (n + 1) → ξ) (x : Bool) (xs : Bits n) : ξ := f (xs +> x)

@[irreducible] def sum : ∀ {m n}, (Bits m → Bits n) → Nat
| 0, _, f => (f ⦃⦄).toNat
| _ + 1, _, f => sum (comp f 0) + sum (comp f 1)

lemma sum_zero {n} (f : Bits 0 → Bits n) : sum f = (f ⦃⦄).toNat := by delta sum; rfl

lemma sum_succ {m n} (f : Bits (m + 1) → Bits n) :
    sum f = sum (comp f 0) + sum (comp f 1) := by delta sum; rfl

def nof {m n} (f : Bits m → Bits n) : Prop := sum f < 2 ^ n

lemma frel_succ {ξ} {n k b r} {f g : Bits (n + 1) → ξ} (h : Frel (k +> b) r f g) :
    Frel k r (comp f b) (comp g b) ∧ (comp f !b) = (comp g !b) := by
  constructor
  · intro k'; constructor <;> intro h_k'
    · apply (h (k' +> b)).left (by rw [h_k'])
    · apply (h (k' +> b)).right
      intro hc; rw [Bits.cons_eq_cons] at hc
      cases h_k' hc.left
  · apply funext; intro k'
    apply (h (k' +> !b)).right
    intro hc; rw [Bits.cons_eq_cons] at hc
    cases b <;> cases hc.right

lemma sum_succ_with {m n} {f : Bits (m + 1) → Bits n} (b : Bool) :
    sum f = sum (comp f b) + sum (comp f !b) := by
  cases b; apply sum_succ; rw [Nat.add_comm (sum _)]; apply sum_succ

lemma le_sum {m n} {f : Bits m → Bits n} {xs} : (f xs).toNat ≤ sum f := by
  induction m with
  | zero => rw [sum_zero]; cases xs; apply Nat.le_refl
  | succ m ih =>
    match xs with
    | xs +> x =>
      rw [sum_succ]
      rcases Bool.zero_or_one x with h | h <;> cases h
      · apply @le_trans _ _ _ (sum (comp f 0)) _ (@ih (comp f 0) xs) (Nat.le_add_right _ _)
      · apply @le_trans _ _ _ (sum (comp f 1)) _ (@ih (comp f 1) xs) (Nat.le_add_left _ _)

open Bits

lemma sum_sub_assoc {m n k v}
    {f g : Bits m → Bits n}
    (h : Decrease k v f g) (h' : v ≤ f k) :
    sum f - v.toNat = sum g := by
  induction m with
  | zero =>
    simp [sum_zero]; cases k
    rw [← Bits.sub_toNat _ _ h', (h ⦃⦄).left rfl]
  | succ m ih =>
    match k with
    | k +> b =>
      rcases frel_succ h with ⟨h_frel, h_eq⟩
      rw [sum_succ_with b, sum_succ_with b, h_eq]
      have h_le : toNat v ≤ sum (comp f b) := by
        apply Nat.le_trans _ (@le_sum _ _ _ k)
        apply toNat_le_toNat _ _ h'
      conv =>
        lhs;
        rw [ Nat.add_comm, Nat.add_sub_assoc h_le,
             ih h_frel h', Nat.add_comm ]; rfl

lemma sum_add_assoc {m n k v} {f g : Bits m → Bits n}
    (h : Increase k v f g) (h' : NoOverflow (f k) v) :
    sum f + v.toNat = sum g := by
  induction m with
  | zero =>
    cases k; simp [sum_zero]; rw [← Bits.add_toNat _ _ h']
    apply congr_arg _ <| (h ⦃⦄).left nil_eq_nil
  | succ m ih =>
    match k with
    | k +> b =>
      rcases frel_succ h with ⟨h_frel, h_eq⟩
      rw [sum_succ_with b, sum_succ_with b, h_eq]
      conv => lhs; lhs; rw [Nat.add_comm]
      rw [Nat.add_assoc, ih h_frel h', Nat.add_comm]

lemma add_le_sum_of_ne {m n} (f : Bits m → Bits n) {xs ys : Bits m}
    (h : xs ≠ ys) : (f xs).toNat + (f ys).toNat ≤ sum f := by
  induction m with
  | zero => cases h nil_eq_nil
  | succ m ih =>
    match xs, ys with
    | xs +> x, ys +> y =>
      rw [sum_succ];
      rcases Bool.zero_or_one x with h | h <;> cases h <;>
      rcases Bool.zero_or_one y with h | h <;> cases h <;> simp at h
      · apply @Nat.le_trans _ (sum (comp f 0)) _ _ (Nat.le_add_right _ _)
        apply @ih (comp f 0) _ _ h
      · apply Nat.add_le_add (@le_sum _ _ (comp f 0) _) (@le_sum _ _ (comp f 1) _)
      · rw [Nat.add_comm]
        apply Nat.add_le_add (@le_sum _ _ (comp f 0) _) (@le_sum _ _ (comp f 1) _)
      · apply @Nat.le_trans _ (sum (comp f 1)) _ _ (Nat.le_add_left _ _)
        apply @ih (comp f 1) _ _ h

lemma transfer_inv_sum {m n} {kd ki v} {b d : Bits m → Bits n}
    (h' : nof b)
    (h : Transfer b kd v ki d) : sum b = sum d := by
  rcases h with ⟨h, c, hd, hi⟩
  apply @Eq.trans _ _ (sum c + v.toNat)
  · rw [← sum_sub_assoc hd h, Nat.sub_add_cancel]
    apply Nat.le_trans (toNat_le_toNat _ _ h) le_sum
  · apply @sum_add_assoc _ _ ki
    apply frel_of_frel _ hi; intro h_eq; exact h_eq
    by_cases hk : ki = kd
    · rw [hk, ← (hd kd).left rfl]; simp [NoOverflow]
      rw [sub_toNat _ _ h, Nat.sub_add_cancel (toNat_le_toNat _ _ h)]
      apply toNat_lt_pow
    · rw [← (hd ki).right (Ne.symm hk)]
      apply lt_of_le_of_lt (Nat.le_trans _ <| add_le_sum_of_ne b hk) h'
      apply Nat.add_le_add_left <| toNat_le_toNat _ _ h

lemma transfer_inv_nof {m n} {kd ki v} {f g : Bits m → Bits n}
    (h : Transfer f kd v ki g) (h' : nof f) : nof g := by
  simp [nof]; rw [← transfer_inv_sum h' h]; apply h'

lemma of_run_dest {e s r} (h : Hinst.Run e s Hinst.dest r) :
    ∃ a, Transfer s.bal e.cta (s.bal e.cta) a r.bal := by
  cases h with
  | dest x bal bal' h_wup h_stk h_ow hi =>
    refine' ⟨toAddr x, Bits.le_refl, bal, _, hi⟩
    intro a; constructor <;> intro ha
    · rw [ha, Bits.sub_self, (h_ow a).left ha]
    · exact (h_ow a).right ha

lemma Hinst.inv_nof {e s o r}
    (h : Hinst.Run e s o r) (h_nof : nof s.bal) : nof r.bal := by
  cases o with
  | stop => cases h; exact h_nof
  | ret => cases h; exact h_nof
  | rev => cases h
  | dest =>
    rcases of_run_dest h with ⟨a, h'⟩
    exact transfer_inv_nof asm h_nof

lemma Hinst.inv_sum_bal {e s o r}
    (h : Hinst.Run e s o r) (h_nof : nof s.bal) : sum s.bal = sum r.bal := by
  cases o with
  | stop => cases h; rfl
  | ret => cases h; rfl
  | rev => cases h
  | dest =>
    rcases of_run_dest h with ⟨a, h'⟩
    exact transfer_inv_sum h_nof h'

lemma Xinst.prep_inv_nof {e s ep sp o r sw}
    (h : Xinst.Run' e s ep sp o r sw) (h_nof : nof s.bal) : nof sp.bal := by
  cases h <;> try {apply h_nof} <;> apply transfer_inv_nof asm h_nof

lemma Xinst.prep_inv_sum_bal {e s ep sp o r sw}
    (h : Xinst.Run' e s ep sp o r sw) (h' : nof s.bal) : sum s.bal = sum sp.bal := by
  cases h <;> try {rfl} <;> apply transfer_inv_sum asm asm

lemma Xinst.wrap_inv_nof {e s ep sp o r sw}
    (h : Xinst.Run' e s ep sp o r sw) (h' : nof r.bal) : nof sw.bal := by
  cases h <;> apply h'

lemma Step.inv_nof {e : Env} {s : State} {pc : ℕ} {s' : State} {pc' : ℕ}
    (h_nof : nof s.bal) (h_step : Step e s pc s' pc') : nof s'.bal := by
  cases h_step with
  | reg => rw [← Rinst.inv_bal asm]; exact h_nof
  | pre =>
    apply Xinst.wrap_inv_nof asm
    have h := PreRun.bal asm; rw [← h]
    apply Xinst.prep_inv_nof asm h_nof
  | fail => rw [← fail_inv_bal asm]; exact h_nof
  | jump => rw [← Jinst.inv_bal asm]; exact h_nof
  | push => rw [← (asm : State.Push _ _ _).bal]; exact h_nof

lemma Step.inv_sum_bal {e : Env} {s : State} {pc : ℕ} {s' : State} {pc' : ℕ}
    (h_nof : nof s.bal) (h_step : Step e s pc s' pc') : sum s.bal = sum s'.bal := by
  cases h_step with
  | reg => apply congr_arg _ <| Rinst.inv_bal asm
  | pre =>
    rw [Xinst.prep_inv_sum_bal asm h_nof]
    rw [(asm : PreRun _ _).bal, Xinst.wrap_inv_bal asm]
  | fail => rw [fail_inv_bal asm]
  | jump => rw [Jinst.inv_bal asm]
  | push => rw [(asm : State.Push _ _ _).bal]

lemma Exec.inv_nof :
    ∀ {e s pc r}, Exec e s pc r → nof s.bal → nof r.bal := by
  apply @Exec.rec (λ e s pc r _ => nof s.bal → nof r.bal)
  · intros e s pc s' pc' _ h_step _ ih h_nof
    apply ih <| Step.inv_nof h_nof h_step
  · intros e s _ ep sp o rx sw _ _ h_cr _ _ ih ih' h_nof
    apply ih' <| Xinst.wrap_inv_nof asm <| ih <| Xinst.prep_inv_nof asm h_nof
  · intros e s pc r h_ht h_nof
    cases h_ht
    · apply Hinst.inv_nof asm h_nof
    · exact h_nof

lemma Exec.inv_sum_bal :
    ∀ {e s pc r}, Exec e s pc r → nof s.bal → sum s.bal = sum r.bal := by
  apply @Exec.rec (λ e s pc r _ => nof s.bal → sum s.bal = sum r.bal)
  · intros e s pc s' pc' r h_step _ ih h_nof
    rw [Step.inv_sum_bal h_nof h_step, ih <| Step.inv_nof h_nof h_step]
  · intros e s _ ep sp o rx sw r _ cr h_run _ ih ih' h_nof
    have h_nof := Xinst.prep_inv_nof asm asm
    have h_nof' := Xinst.wrap_inv_nof asm <| Exec.inv_nof h_run asm
    rw [Xinst.prep_inv_sum_bal asm asm, ih asm, Xinst.wrap_inv_bal asm, ih' asm]
  · intros e s pc r h h'; cases h
    · exact Hinst.inv_sum_bal asm h'
    · rfl

lemma Xinst.inv_nof {e s o s'}
    (h : Xinst.Run e s o s') (h' : nof s.bal) : nof s'.bal := by
  cases h
  · apply Xinst.wrap_inv_nof asm <| Exec.inv_nof asm <| Xinst.prep_inv_nof asm h'
  · apply Xinst.wrap_inv_nof asm
    rw [← (asm : PreRun _ _).bal]
    apply Xinst.prep_inv_nof asm h'
  · rw [← fail_inv_bal asm]; exact h'

lemma Inst.inv_nof {e s} :
    ∀ {i s'}, Inst.Run e s i s' → nof s.bal → nof s'.bal := by
  apply @Inst.Run.rec e s (λ i s' _ => nof s.bal → nof s'.bal)
  · intros o s' h; simp [Rinst.inv_bal h]
  · intros o s' h; exact Xinst.inv_nof h
  · intros bs _ s' h h'; rw [← h.bal]; exact h'

lemma Func.inv_nof {c e} :
    ∀ {s p r}, Func.Run c e s p r → nof s.bal → nof r.bal := by
  apply @Func.Run.rec c e (λ s p r _ => nof s.bal → nof r.bal)
  · intros s s' _ _ r h_pop _ ih h_nof
    rw [← State.Rel.bal h_pop] at ih; apply ih h_nof
  · intros s x s' _ _ r _ h_pop _ ih h_nof
    rw [← State.Rel.bal h_pop] at ih; apply ih h_nof
  · intros s o r h_run h_nof
    apply Hinst.inv_nof h_run h_nof
  · intros s i s' _ _ h_run _ ih h_nof
    apply ih <| Inst.inv_nof h_run h_nof
  · intro _ _ _ _ _ _; apply id

def compsize : Func → Nat
  | .last _ => 1
  | .next i p => compsize p + i.toBytes.length
  | .branch p q => compsize p + compsize q + 5
  | .call _ => 4

def table : Nat → List Func → List (Nat × Func)
| _, [] => []
| k, f :: fs => ⟨k, f⟩ :: table (k + compsize f + 1) fs

def Func.compile (l : List (Nat × Func)) (n : Nat) : Func → Option Bytes
  | .last o => pure ⟪o.toByte⟫
  | .next o p => do
    let p_bts ← Func.compile l (n + o.toBytes.length) p
    pure <| o.toBytes ++ p_bts
  | .branch p q => do
    let pbs ← Func.compile l (n + 4) p
    let loc := n + pbs.length + 4
    guard (loc < 2 ^ 16)
    let qbs ← Func.compile l (loc + 1) q
    pure $
      ⟪Ox x6 x1⟫ ++
      (@Nat.toBits (8 * 2) loc).toBytes ++
      ⟪Jinst.toByte .jumpi⟫ ++ pbs ++
      ⟪Jinst.toByte .jumpdest⟫ ++ qbs
  | .call k => do
    let (loc, _) ← List.get? l k
    guard (loc < 2 ^ 16)
    pure $
      ⟪Ox x6 x1⟫ ++
      (@Nat.toBits (8 * 2) loc).toBytes ++
      ⟪Jinst.toByte Jinst.jump⟫

def Table.compile (l : List (Nat × Func)) : List (Nat × Func) → Option Bytes
| [] => pure ⟪⟫
| (n, p) :: nps => do
  let bs ← Func.compile l (n + 1) p
  let bss ← Table.compile l nps
  pure <| ⟪Jinst.toByte .jumpdest⟫ ++ bs ++ bss

lemma of_bind_eq_some {ξ υ} {f : Option ξ} {g : ξ → Option υ} {y} :
    f >>= g = some y → ∃ x, f = some x ∧ g x = some y := by
  intro h; cases f with
  | none => cases h
  | some x => refine ⟨x, rfl, h⟩

lemma Table.compile_cons_eq_some {l n p l' bs}
    (h : Table.compile l ((n, p) :: l') = some bs) :
    ∃ cp cl',
      Func.compile l (n + 1) p = some cp ∧
      Table.compile l l' = some cl' ∧
      bs = ⟪Jinst.toByte .jumpdest⟫ ++ cp ++ cl' := by
  rcases of_bind_eq_some h with ⟨cp, h_cp, h'⟩; clear h
  rcases of_bind_eq_some h' with ⟨cl', h_cl', h_eq⟩; clear h'
  simp at h_eq; refine' ⟨cp, cl', h_cp, h_cl', h_eq.symm⟩

def Prog.compile (p : Prog) : Option Bytes :=
  let t : List (Nat × Func) := table 0 (p.main :: p.aux)
  Table.compile t t

lemma of_guard_eq_some {p : Prop} [hd : Decidable p] {ξ} {ox : Option ξ} {x} :
    (do guard p; ox) = some x → p ∧ ox = some x := by
  intro h
  cases em p with
  | inl hp => simp [hp] at h; constructor <;> assumption
  | inr hp => simp [guard, if_neg hp] at h; cases h

lemma of_pure_eq_some {ξ} {x y : ξ} : pure x = some y → x = y := by intro h; cases h; rfl

lemma pushToBytes_ne_nil {bs} : pushToBytes bs ≠ ⟪⟫ := by
  simp [pushToBytes, pushToByte]; intro h
  rw [Bytes.append_eq_nil] at h; cases h.left

lemma Inst.toBytes_ne_nil : ∀ {i : Inst}, i.toBytes ≠ ⟪⟫
  | reg o => by simp [toBytes]
  | exec o => by simp [toBytes]
  | push bs _ => pushToBytes_ne_nil

lemma Bytes.append_ne_nil_of_left_ne_nil {xs ys : Bytes} : xs ≠ ⟪⟫ → xs ++ ys ≠ ⟪⟫ := by
  intros h h'; rw [Bytes.append_eq_nil] at h'; cases h h'.left

lemma Func.compile_ne_nil {l n p} : Func.compile l n p ≠ some ⟪⟫ := by
  induction p with
  | last => simp [compile]
  | next =>
    intros h; rcases of_bind_eq_some h with ⟨bs, _, h⟩; simp at h;
    apply Bytes.append_ne_nil_of_left_ne_nil Inst.toBytes_ne_nil h
  | branch =>
    intro h
    rcases of_bind_eq_some h with ⟨_, _, h'⟩; clear h
    rcases of_guard_eq_some h' with ⟨_, h⟩; clear h'
    rcases of_bind_eq_some h with ⟨bs', hp, h'⟩; clear h
    simp at h'; apply Bytes.append_ne_nil_of_left_ne_nil _ h'
    apply Bytes.append_ne_nil_of_left_ne_nil
    apply Bytes.append_ne_nil_of_left_ne_nil
    apply Bytes.append_ne_nil_of_left_ne_nil
    apply Bytes.append_ne_nil_of_left_ne_nil
    simp
  | call =>
    intro h
    rcases of_bind_eq_some h with ⟨_, _, h'⟩; clear h
    rcases of_guard_eq_some h' with ⟨_, h⟩; clear h'
    simp at h;
    apply Bytes.append_ne_nil_of_left_ne_nil _ h
    apply Bytes.append_ne_nil_of_left_ne_nil
    simp

lemma Prog.compile_ne_nil {p} : Prog.compile p ≠ some ⟪⟫ := by
  simp only [Prog.compile, Table.compile]; intro h
  rcases of_bind_eq_some h with ⟨bs, h_bs, h'⟩; clear h
  rcases of_bind_eq_some h' with ⟨bs', h_bs', h⟩; clear h'; simp at h;
  rw [(Bytes.append_eq_nil.mp <| (Bytes.append_eq_nil.mp h).left).right] at h_bs
  cases Func.compile_ne_nil h_bs

def subcode (cd : Bytes) (k : Nat) : Option Bytes → Prop
  | none => False
  | some scd => slice cd k scd

def of_subcode {cd k} :
    ∀ {ocd}, subcode cd k ocd → ∃ scd, ocd = some scd ∧ slice cd k scd
  | none, h => by cases h
  | some scd, h => ⟨scd, rfl, h⟩

lemma hex0_append_hex1 : ∀ {b : Byte}, Byte.hex0 b ++ Byte.hex1 b = b
  | ⦃_, _, _, _, _, _, _, _⦄ => rfl

def Byte.toRinst : Byte → Rinst
  | ⦃0, 0, 0, 0, 0, 0, 0, 1⦄ => Rinst.add -- 0x01 / 2 / 1 / addition operation.
  | ⦃0, 0, 0, 0, 0, 0, 1, 0⦄ => Rinst.mul -- 0x02 / 2 / 1 / multiplication operation.
  | ⦃0, 0, 0, 0, 0, 0, 1, 1⦄ => Rinst.sub -- 0x03 / 2 / 1 / subtraction operation.
  | ⦃0, 0, 0, 0, 0, 1, 0, 0⦄ => Rinst.div -- 0x04 / 2 / 1 / integer division operation.
  | ⦃0, 0, 0, 0, 0, 1, 0, 1⦄ => Rinst.sdiv -- 0x05 / 2 / 1 / signed integer division operation.
  | ⦃0, 0, 0, 0, 0, 1, 1, 0⦄ => Rinst.mod -- 0x06 / 2 / 1 / modulo operation.
  | ⦃0, 0, 0, 0, 0, 1, 1, 1⦄ => Rinst.smod -- 0x07 / 2 / 1 / signed modulo operation.
  | ⦃0, 0, 0, 0, 1, 0, 0, 0⦄ => Rinst.addmod -- 0x08 / 3 / 1 / modulo addition operation.
  | ⦃0, 0, 0, 0, 1, 0, 0, 1⦄ => Rinst.mulmod -- 0x09 / 3 / 1 / modulo multiplication operation.
  | ⦃0, 0, 0, 0, 1, 0, 1, 0⦄ => Rinst.exp -- 0x0a / 2 / 1 / exponentiation operation.
  | ⦃0, 0, 0, 0, 1, 0, 1, 1⦄ => Rinst.signextend -- 0x0b / 2 / 1 / sign extend operation.
  | ⦃0, 0, 0, 1, 0, 0, 0, 0⦄ => Rinst.lt -- 0x10 / 2 / 1 / less-than comparison.
  | ⦃0, 0, 0, 1, 0, 0, 0, 1⦄ => Rinst.gt -- 0x11 / 2 / 1 / greater-than comparison.
  | ⦃0, 0, 0, 1, 0, 0, 1, 0⦄ => Rinst.slt -- 0x12 / 2 / 1 / signed less-than comparison.
  | ⦃0, 0, 0, 1, 0, 0, 1, 1⦄ => Rinst.sgt -- 0x13 / 2 / 1 / signed greater-than comparison.
  | ⦃0, 0, 0, 1, 0, 1, 0, 0⦄ => Rinst.eq -- 0x14 / 2 / 1 / equality comparison.
  | ⦃0, 0, 0, 1, 0, 1, 0, 1⦄ => Rinst.iszero -- 0x15 / 1 / 1 / tests if the input is zero.
  | ⦃0, 0, 0, 1, 0, 1, 1, 0⦄ => Rinst.and -- 0x16 / 2 / 1 / bitwise and operation.
  | ⦃0, 0, 0, 1, 0, 1, 1, 1⦄ => Rinst.or -- 0x17 / 2 / 1 / bitwise or operation.
  | ⦃0, 0, 0, 1, 1, 0, 0, 0⦄ => Rinst.xor -- 0x18 / 2 / 1 / bitwise xor operation.
  | ⦃0, 0, 0, 1, 1, 0, 0, 1⦄ => Rinst.not -- 0x19 / 1 / 1 / bitwise not operation.
  | ⦃0, 0, 0, 1, 1, 0, 1, 0⦄ => Rinst.byte -- 0x1a / 2 / 1 / retrieve a single byte from a word.
  | ⦃0, 0, 0, 1, 1, 0, 1, 1⦄ => Rinst.shl -- 0x1b / 2 / 1 / logical shift right operation.
  | ⦃0, 0, 0, 1, 1, 1, 0, 0⦄ => Rinst.shr -- 0x1c / 2 / 1 / logical shift left operation.
  | ⦃0, 0, 0, 1, 1, 1, 0, 1⦄ => Rinst.sar -- 0x1d / 2 / 1 / arithmetic (signed) shift right operation.
  | ⦃0, 0, 1, 0, 0, 0, 0, 0⦄ => Rinst.kec -- 0x20 / 2 / 1 / compute Keccak-256 hash.
  | ⦃0, 0, 1, 1, 0, 0, 0, 0⦄ => Rinst.address -- 0x30 / 0 / 1 / Get the address of the currently executing account.
  | ⦃0, 0, 1, 1, 0, 0, 0, 1⦄ => Rinst.balance -- 0x31 / 1 / 1 / Get the balance of the specified account.
  | ⦃0, 0, 1, 1, 0, 0, 1, 0⦄ => Rinst.origin -- 0x32 / 0 / 1 / Get the address that initiated the current transaction.
  | ⦃0, 0, 1, 1, 0, 0, 1, 1⦄ => Rinst.caller -- 0x33 / 0 / 1 / Get the address that directly called the currently executing contract.
  | ⦃0, 0, 1, 1, 0, 1, 0, 0⦄ => Rinst.callvalue -- 0x34 / 0 / 1 / Get the value (in wei) sent with the current transaction.
  | ⦃0, 0, 1, 1, 0, 1, 0, 1⦄ => Rinst.calldataload -- 0x35 / 1 / 1 / Load input data from the current transaction.
  | ⦃0, 0, 1, 1, 0, 1, 1, 0⦄ => Rinst.calldatasize -- 0x36 / 0 / 1 / Get the size of the input data from the current transaction.
  | ⦃0, 0, 1, 1, 0, 1, 1, 1⦄ => Rinst.calldatacopy -- 0x37 / 3 / 0 / Copy input data from the current transaction to memory.
  | ⦃0, 0, 1, 1, 1, 0, 0, 0⦄ => Rinst.codesize -- 0x38 / 0 / 1 / Get the size of the code of the currently executing contract.
  | ⦃0, 0, 1, 1, 1, 0, 0, 1⦄ => Rinst.codecopy -- 0x39 / 3 / 0 / Copy the code of the currently executing contract to memory.
  | ⦃0, 0, 1, 1, 1, 0, 1, 0⦄ => Rinst.gasprice -- 0x3a / 0 / 1 / Get the gas price of the current transaction.
  | ⦃0, 0, 1, 1, 1, 0, 1, 1⦄ => Rinst.extcodesize -- 0x3b / 1 / 1 / Get the size of the code of an external account.
  | ⦃0, 0, 1, 1, 1, 1, 0, 0⦄ => Rinst.extcodecopy -- 0x3c / 4 / 0 / Copy the code of an external account to memory.
  | ⦃0, 0, 1, 1, 1, 1, 0, 1⦄ => Rinst.retdatasize -- 0x3d / 0 / 1 / Get the size of the output data from the previous call.
  | ⦃0, 0, 1, 1, 1, 1, 1, 0⦄ => Rinst.retdatacopy -- 0x3e / 3 / 0 / Copy output data from the previous call to memory.
  | ⦃0, 0, 1, 1, 1, 1, 1, 1⦄ => Rinst.extcodehash -- 0x3f / 1 / 1 / Get the code hash of an external account.
  | ⦃0, 1, 0, 0, 0, 0, 0, 0⦄ => Rinst.blockhash -- 0x40 / 1 / 1 / get the hash of the specified block.
  | ⦃0, 1, 0, 0, 0, 0, 0, 1⦄ => Rinst.coinbase -- 0x41 / 0 / 1 / get the address of the current block's miner.
  | ⦃0, 1, 0, 0, 0, 0, 1, 0⦄ => Rinst.timestamp -- 0x42 / 0 / 1 / get the timestamp of the current block.
  | ⦃0, 1, 0, 0, 0, 0, 1, 1⦄ => Rinst.number -- 0x43 / 0 / 1 / get the current block number.
  | ⦃0, 1, 0, 0, 0, 1, 0, 0⦄ => Rinst.prevrandao -- 0x44 / 0 / 1 / get the difficulty of the current block.
  | ⦃0, 1, 0, 0, 0, 1, 0, 1⦄ => Rinst.gaslimit -- 0x45 / 0 / 1 / get the gas limit of the current block.
  | ⦃0, 1, 0, 0, 0, 1, 1, 0⦄ => Rinst.chainid -- 0x46 / 0 / 1 / get the chain id of the current blockchain.
  | ⦃0, 1, 0, 0, 0, 1, 1, 1⦄ => Rinst.selfbalance -- 0x46 / 0 / 1 / get the chain id of the current blockchain.
  | ⦃0, 1, 0, 0, 1, 0, 0, 0⦄ => Rinst.basefee -- 0x46 / 0 / 1 / get the chain id of the current blockchain.
  | ⦃0, 1, 0, 1, 0, 0, 0, 0⦄ => Rinst.pop -- 0x50 / 1 / 0 / Remove an item from the stack.
  | ⦃0, 1, 0, 1, 0, 0, 0, 1⦄ => Rinst.mload -- 0x51 / 1 / 1 / Load a word from memory.
  | ⦃0, 1, 0, 1, 0, 0, 1, 0⦄ => Rinst.mstore -- 0x52 / 2 / 0 / Store a word in memory.
  | ⦃0, 1, 0, 1, 0, 0, 1, 1⦄ => Rinst.mstore8 -- 0x53 / 2 / 0 / Store a byte in memory.
  | ⦃0, 1, 0, 1, 0, 1, 0, 0⦄ => Rinst.sload -- 0x54 / 1 / 1 / Load a word from storage.
  | ⦃0, 1, 0, 1, 0, 1, 0, 1⦄ => Rinst.sstore -- 0x55 / 2 / 0 / Store a word in storage.
  | ⦃0, 1, 0, 1, 1, 0, 0, 0⦄ => Rinst.pc -- 0x58 / 0 / 1 / Get the current program counter value.
  | ⦃0, 1, 0, 1, 1, 0, 0, 1⦄ => Rinst.msize -- 0x59 / 0 / 1 / Get the size of the memory.
  | ⦃0, 1, 0, 1, 1, 0, 1, 0⦄ => Rinst.gas -- 0x5a / 0 / 1 / Get the amount of remaining gas.
  | ⦃1, 0, 0, 0, b0, b1, b2, b3⦄ => Rinst.dup ⟨Bits.toNat ⦃b0, b1, b2, b3⦄, Bits.toNat_lt_pow _⟩
  | ⦃1, 0, 0, 1, b0, b1, b2, b3⦄ => Rinst.swap ⟨Bits.toNat ⦃b0, b1, b2, b3⦄, Bits.toNat_lt_pow _⟩
  | ⦃1, 0, 1, 0, 0, 0, 0, 0⦄ => Rinst.log 0
  | ⦃1, 0, 1, 0, 0, 0, 0, 1⦄ => Rinst.log 1
  | ⦃1, 0, 1, 0, 0, 0, 1, 0⦄ => Rinst.log 2
  | ⦃1, 0, 1, 0, 0, 0, 1, 1⦄ => Rinst.log 3
  | ⦃1, 0, 1, 0, 0, 1, 0, 0⦄ => Rinst.log 4
  | _ => Rinst.invalid

lemma dup_toByte_toRinst : ∀ n, Byte.toRinst (Rinst.dup n).toByte = Rinst.dup n
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

lemma swap_toByte_toRinst : ∀ n, Byte.toRinst (Rinst.swap n).toByte = Rinst.swap n
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

lemma log_toByte_toRinst : ∀ n, Byte.toRinst (Rinst.log n).toByte = Rinst.log n
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | ⟨n + 5, h⟩ => by
    rw [← Nat.not_le] at h
    cases h (Nat.le_add_left _ _)

lemma toByte_toRinst {o : Rinst} : Byte.toRinst o.toByte = o := by
  cases o <;> try {rfl; done}
  · apply dup_toByte_toRinst
  · apply swap_toByte_toRinst
  · apply log_toByte_toRinst

def Byte.toXinst : Byte → Xinst
  | ⦃1, 1, 1, 1, 0, 0, 0, 0⦄ => Xinst.create
  | ⦃1, 1, 1, 1, 0, 0, 0, 1⦄ => Xinst.call
  | ⦃1, 1, 1, 1, 0, 0, 1, 0⦄ => Xinst.callcode
  | ⦃1, 1, 1, 1, 0, 1, 0, 0⦄ => Xinst.delcall
  | ⦃1, 1, 1, 1, 0, 1, 0, 1⦄ => Xinst.create2
  | _                        => Xinst.statcall

def Byte.toJinst : Byte → Jinst
  | ⦃0, 1, 0, 1, 0, 1, 1, 0⦄ => Jinst.jump
  | ⦃0, 1, 0, 1, 0, 1, 1, 1⦄ => Jinst.jumpi
  | _ => Jinst.jumpdest

def Byte.toHinst : Byte → Hinst
  | ⦃0, 0, 0, 0, 0, 0, 0, 0⦄ => Hinst.stop
  | ⦃1, 1, 1, 1, 0, 0, 1, 1⦄ => Hinst.ret
  | ⦃1, 1, 1, 1, 1, 1, 0, 1⦄ => Hinst.rev
  | _ => Hinst.dest

lemma toByte_toXinst {o : Xinst} :
  Byte.toXinst o.toByte = o := by cases o <;> rfl
lemma toByte_toJinst {o : Jinst} :
  Byte.toJinst o.toByte = o := by cases o <;> rfl
lemma toByte_toHinst {o : Hinst} :
  Byte.toHinst o.toByte = o := by cases o <;> rfl

lemma Rinst.At_unique {e pc o o'} (h : Rinst.At e pc o) (h' : Rinst.At e pc o') : o = o' := by
  rw [← @toByte_toRinst o, ← @toByte_toRinst o', slice_singleton_unique h h']

lemma Xinst.At_unique {e pc o o'} (h : Xinst.At e pc o) (h' : Xinst.At e pc o') : o = o' := by
  rw [← @toByte_toXinst o, ← @toByte_toXinst o', slice_singleton_unique h h']

lemma Jinst.At_unique {e pc o o'} (h : Jinst.At e pc o) (h' : Jinst.At e pc o') : o = o' := by
  rw [← @toByte_toJinst o, ← @toByte_toJinst o', slice_singleton_unique h h']

lemma Hinst.At_unique {e pc o o'} (h : Hinst.At e pc o) (h' : Hinst.At e pc o') : o = o' := by
  rw [← @toByte_toHinst o, ← @toByte_toHinst o', slice_singleton_unique h h']

lemma pushAt_unique {e pc bs bs'} (h : pushAt e pc bs) (h' : pushAt e pc bs') : bs = bs' := by
  have hs := slice_suffix h.left
  have hs' := slice_suffix h'.left
  apply slice_unique _ hs hs'
  rw [ ← @toBits_toNat 8 bs.length (lt_of_le_of_lt h.right (by omega)),
       ← @toBits_toNat 8 bs'.length (lt_of_le_of_lt h'.right (by omega)) ]
  apply congrArg _ <| @Bits.add_left_inj 8 _ _ (Ox x5 xF) _
  apply slice_singleton_unique (slice_prefix h.left) (slice_prefix h'.left)

lemma ox_ne_ox_of_left {lx rx ly ry : Hex} : lx ≠ ly → Ox lx rx ≠ Ox ly ry := by
  simp [Ox]; rw [Bits.append_eq_append_iff]; intros h h'; apply h h'.left

lemma ox_ne_ox_of_right {lx rx ly ry : Hex} : rx ≠ ry → Ox lx rx ≠ Ox ly ry := by
  simp [Ox]; rw [Bits.append_eq_append_iff]; intros h h'; apply h h'.right

syntax "ox_ne_left" : tactic
macro_rules
  | `(tactic| ox_ne_left) => `(tactic| apply ox_ne_ox_of_left; intro hc; cases hc)

syntax "ox_ne_left'" : tactic
macro_rules
  | `(tactic| ox_ne_left') => `(tactic| apply ox_ne_ox_of_left; intro hc; cases hc; done)

syntax "ox_ne_right'" : tactic
macro_rules
  | `(tactic| ox_ne_right') => `(tactic| apply ox_ne_ox_of_right; intro hc; cases hc; done)

syntax "ox_ne" : tactic
macro_rules
  | `(tactic| ox_ne) => `(tactic| first | ox_ne_left' | ox_ne_right')

inductive Rinst.range : Rinst → Prop
  | x0 : ∀ hx, o.toByte = (Ox x0 hx) → Rinst.range o
  | x1 : ∀ hx, o.toByte = (Ox x1 hx) → Rinst.range o
  | x2 : ∀ hx, o.toByte = (Ox x2 hx) → Rinst.range o
  | x3 : ∀ hx, o.toByte = (Ox x3 hx) → Rinst.range o
  | x4 : ∀ hx, o.toByte = (Ox x4 hx) → Rinst.range o
  | x5 : ∀ hx, o.toByte = (Ox x5 hx) → Rinst.range o
  | x8 : ∀ hx, o.toByte = (Ox x8 hx) → Rinst.range o
  | x9 : ∀ hx, o.toByte = (Ox x9 hx) → Rinst.range o
  | xA : ∀ hx, o.toByte = (Ox xA hx) → Rinst.range o
  | xFE : Rinst.range Rinst.invalid

lemma Rinst.range_toByte (o : Rinst) : Rinst.range o := by
  cases o
  repeat {apply Rinst.range.x0; rfl}
  repeat {apply Rinst.range.x1; rfl}
  repeat {apply Rinst.range.x2; rfl}
  repeat {apply Rinst.range.x3; rfl}
  repeat {apply Rinst.range.x4; rfl}
  repeat {apply Rinst.range.x5; rfl}
  repeat {apply Rinst.range.x8; rfl}
  repeat {apply Rinst.range.x9; rfl}
  repeat {apply Rinst.range.xA; rfl}
  apply Rinst.range.xFE

lemma Xinst.toByte_eq_ox (o : Xinst) : ∃ hx, o.toByte = Ox xF hx := by
  cases o <;> refine ⟨_, rfl⟩

lemma opToByte_ne_copToByte {o : Rinst} {o' : Xinst} : o.toByte ≠ o'.toByte := by
  cases Rinst.range_toByte o <;>
  try { apply @Eq.rec Byte _ (λ b h_eq => (b ≠ o'.toByte)) _ _ (Eq.symm (by assumption));
        rcases Xinst.toByte_eq_ox o' with ⟨hx, h_eq⟩; rw [h_eq]; ox_ne_left' }
  cases o' <;> ox_ne

lemma opToByte_ne_jopToByte {o : Rinst} {o' : Jinst} : o.toByte ≠ o'.toByte := by
  cases o <;> cases o' <;> ox_ne

lemma opToByte_ne_hopToByte {o : Rinst} {o' : Hinst} : o.toByte ≠ o'.toByte := by
  cases o <;> cases o' <;> ox_ne

lemma copToByte_ne_jopToByte {o : Xinst} {o' : Jinst} : o.toByte ≠ o'.toByte := by
  cases o <;> cases o' <;> ox_ne

lemma jopToByte_ne_hopToByte {o : Jinst} {o' : Hinst} : o.toByte ≠ o'.toByte := by
  cases o <;> cases o' <;> ox_ne

lemma copToByte_ne_hopToByte {o : Xinst} {o' : Hinst} : o.toByte ≠ o'.toByte := by
  cases o <;> cases o' <;> ox_ne

lemma eq_ox {b : Byte} {hx0 hx1 : Hex} :
    Byte.hex0 b = hx0 → Byte.hex1 b = hx1 → b = Ox hx0 hx1 := by
  intros h0 h1; rw [← @hex0_append_hex1 b, h0, h1]; rfl

syntax "eq_ox_core" : tactic
macro_rules
| `(tactic| eq_ox_core) =>
  `(tactic| rw [Nat.forall_le_succ]; apply Function.swap And.intro; right)

syntax "eq_ox_left" : tactic
macro_rules
| `(tactic| eq_ox_left) => `(tactic| eq_ox_core; left; refine ⟨_, eq_ox rfl rfl⟩)

syntax "eq_ox_right" : tactic
macro_rules
| `(tactic| eq_ox_right) => `(tactic| eq_ox_core; right; refine ⟨_, eq_ox rfl rfl⟩)

lemma pushToByte_eq_aux :
    ∀ n ≤ 32,
      ( Ox x5 xF + n.toByte = Ox x5 xF ∨
        (∃ hx, Ox x5 xF + n.toByte = Ox x6 hx) ∨
        (∃ hx, Ox x5 xF + n.toByte = Ox x7 hx) ) := by
  repeat eq_ox_right; repeat eq_ox_left
  intro m; rw [Nat.le_zero]
  intro h_eq; rw [h_eq]; left; rfl

lemma pushToByte_eq {bs : Bytes} :
    bs.length ≤ 32 →
    ( pushToByte bs = Ox x5 xF ∨
      (∃ hx, pushToByte bs = Ox x6 hx) ∨
      (∃ hx, pushToByte bs = Ox x7 hx) ) :=
  by apply pushToByte_eq_aux

syntax "ne_pushToByte" : tactic
macro_rules
  | `(tactic| ne_pushToByte) =>
    `(tactic| rcases pushToByte_eq (by assumption) with h_eq | ⟨hx, h_eq⟩ | ⟨hx, h_eq⟩ <;> rw [h_eq];
              {ox_ne}; ox_ne_left; ox_ne_left)

lemma opToByte_ne_pushToByte {o : Rinst} {bs : Bytes}
    (h : bs.length ≤ 32) : o.toByte ≠ pushToByte bs := by
  intro h'
  have hc : o.toByte = Ox x5 xF ∨ o.toByte.hex0 = x6 ∨ o.toByte.hex0 = x7 := by
    rw [h']; clear h'
    rcases pushToByte_eq h with h' | ⟨_, h'⟩ | ⟨_, h'⟩ <;> (rw [h']; simp [hex0_eq])
  cases o <;>
  try {simp [Rinst.toByte, hex0_eq] at hc; rcases hc with ⟨⟨_⟩⟩ | ⟨⟨_⟩⟩ | ⟨⟨_⟩⟩; done} <;>
  (
    simp [Rinst.toByte, hex0_eq] at hc;
    rcases hc with h'' | ⟨⟨_⟩⟩ | ⟨⟨_⟩⟩;
    have hc := congr_arg Byte.hex0 h''
    simp [hex0_eq] at hc; cases hc
  )

lemma copToByte_ne_pushToByte {o : Xinst} {bs : Bytes} :
    bs.length ≤ 32 → o.toByte ≠ pushToByte bs := by intro h; cases o <;> ne_pushToByte

lemma jopToByte_ne_pushToByte {o : Jinst} {bs : Bytes} :
    bs.length ≤ 32 → o.toByte ≠ pushToByte bs := by intro h; cases o <;> ne_pushToByte

lemma hopToByte_ne_pushToByte {o : Hinst} {bs : Bytes} :
    bs.length ≤ 32 → o.toByte ≠ pushToByte bs := by intro h; cases o <;> ne_pushToByte

lemma not_cop_at_of_op_at {e pc} {o : Rinst} {o' : Xinst} : o.At e pc → ¬ o'.At e pc := by
  intros h h'; cases opToByte_ne_copToByte <| slice_singleton_unique h h'

lemma not_jop_at_of_cop_at {e pc} {o : Xinst} {o' : Jinst} : o.At e pc → ¬ o'.At e pc := by
  intros h h'; cases copToByte_ne_jopToByte <| slice_singleton_unique h h'

lemma not_jop_at_of_op_at {e pc} {o : Rinst} {o' : Jinst} : o.At e pc → ¬ o'.At e pc := by
  intros h h'; cases opToByte_ne_jopToByte <| slice_singleton_unique h h'

lemma not_hop_at_of_op_at {e pc} {o : Rinst} {o' : Hinst} : o.At e pc → ¬ o'.At e pc := by
  intros h h'; cases opToByte_ne_hopToByte <| slice_singleton_unique h h'

lemma not_hop_at_of_cop_at {e pc} {o : Xinst} {o' : Hinst} : o.At e pc → ¬ o'.At e pc := by
  intros h h'; cases copToByte_ne_hopToByte <| slice_singleton_unique h h'

lemma not_hop_at_of_jop_at {e pc} {o : Jinst} {o' : Hinst} : o.At e pc → ¬ o'.At e pc := by
  intros h h'; cases jopToByte_ne_hopToByte <| slice_singleton_unique h h'

lemma not_pushAt_of_op_at {e pc} {o : Rinst} {bs : Bytes} : o.At e pc → ¬ pushAt e pc bs := by
  intros h h';
  cases opToByte_ne_pushToByte h'.right <| slice_singleton_unique h <| slice_prefix h'.left

lemma not_pushAt_of_cop_at {e pc} {o : Xinst} {bs : Bytes} : o.At e pc → ¬ pushAt e pc bs := by
  intros h h'
  cases copToByte_ne_pushToByte h'.right <| slice_singleton_unique h <| slice_prefix h'.left

lemma not_pushAt_of_jop_at {e pc} {o : Jinst} {bs : Bytes} : o.At e pc → ¬ pushAt e pc bs := by
  intros h h'
  cases jopToByte_ne_pushToByte h'.right <| slice_singleton_unique h <| slice_prefix h'.left

lemma not_pushAt_of_hop_at {e pc} {o : Hinst} {bs : Bytes} : o.At e pc → ¬ pushAt e pc bs := by
  intros h h'
  cases hopToByte_ne_pushToByte h'.right <| slice_singleton_unique h <| slice_prefix h'.left

lemma not_slice_length {xs ys : Bytes} {y} : ¬ slice xs xs.length (ys :> y) := by
  intro h; rcases h with ⟨pfx, sfx, h_split, h_pfx, h_len⟩
  have h_sfx : sfx = ⟪⟫ := by
    have h := congrArg Bytes.length h_split
    rw [Bytes.length_append, h_len] at h
    have h' := Nat.eq_sub_of_add_eq' h.symm; simp at h'
    rw [← Bytes.length_eq_zero, h']
  rw [h_sfx, Bytes.prefix_nil] at h_pfx; cases h_pfx

lemma Hinst.run_of_at {e s pc o r} (cr : Exec e s pc r) (h_at : Hinst.At e pc o) :
    Hinst.Run e s o r := by
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
    · rw [Hinst.At_unique h_at asm]; assumption
    · cases not_slice_length h_at

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

lemma State.push_cons_pop_cons
    {x y} {xs ys} {s s' s''}
    (h : State.Push (x :: xs) s s')
    (h' : State.Pop (y :: ys) s' s'') :
    (x = y ∧ ∃ st, State.Push xs s st ∧ State.Pop ys st s'') := by
  rcases h with ⟨_, _, _, h, _, _, _⟩
  rcases h' with ⟨_, _, _, h', _, _, _⟩
  rcases Stack.push_cons_pop_cons h h' with ⟨h_eq, stk, h_push, h_pop⟩
  refine' ⟨
    h_eq,
    ⟨_, _, _, stk, _, _, _⟩,
    ⟨_, _, _, h_push, _, _, _⟩,
    ⟨_, _, _, h_pop,  _, _, _⟩
   ⟩ <;> try {assumption}

lemma State.pop_nil {s s'} (h : State.Pop [] s s') : s = s' := by
  match s, s', h with
  | ⟨_, _, _, _, _, _, _⟩,
    ⟨_, _, _, _, _, _, _⟩,
    ⟨_, _, _, h, _, _, _⟩ =>
    simp [Stack.Push, Split, Rels.dft] at *
    refine' ⟨_, _, _, h, _, _, _⟩ <;> assumption

lemma State.push_nil {s s'} (h : State.Push [] s s') : s = s' := by
  match s, s', h with
  | ⟨_, _, _, _, _, _, _⟩,
    ⟨_, _, _, _, _, _, _⟩,
    ⟨_, _, _, h, _, _, _⟩ =>
    simp [Stack.Push, Split, Rels.dft] at *
    refine' ⟨_, _, _, h.symm, _, _, _⟩ <;> assumption

lemma Inst.At_iff_slice {e pc i} :
    Inst.At e pc i ↔ slice e.code pc (Inst.toBytes i) := by
  cases i with
  | reg o => apply Iff.refl
  | exec o => apply Iff.refl
  | push bs h =>
    simp [Inst.At, pushAt, Inst.toBytes]
    intro _; exact h

lemma max_toBytes {n} : ∀ {xs : Bits (8 * n)}, xs.toBytes.max ↔ xs = Bits.max _ := by
  induction n with
  | zero =>
    simp [Nat.mul_zero]; intro xs; cases xs
    apply iff_of_true; constructor; rfl
  | succ n ih =>
    simp [Nat.mul_succ]
    intro xs;
    rw [← @Bits.head_append_tail (8 * n) 8 xs, Bits.toBytes_append]
    simp [Bytes.max]; rw [ih, Bits.append_eq_max]; rfl

lemma Bytes.not_max_toBytes {m n : Nat} (h : m.succ < 2 ^ (8 * n)) :
    ¬ Bytes.max (Bits.toBytes (Nat.toBits (8 * n) m)) := by
  rw [max_toBytes]; intro hc
  have h_eq := congrArg Bits.toNat hc
  rw [@toBits_toNat _ _ (lt_trans (Nat.lt_succ_self _) h)] at h_eq
  rw [h_eq, Bits.max_toNat_succ] at h
  cases Nat.lt_irrefl _ h

lemma pow_add_toBytes_toBits {k m n : Nat} : k < 2 ^ (8 * n) →
    (Nat.toBits (8 * (m + n)) k).toBytes.toBits (m + n) =
      (Nat.toBits (8 * n) k).toBytes.toBits (m + n) := by
  induction k with
  | zero =>
    intro _; simp [Nat.toBits]
    rw [Bytes.toBits_eq_zero zero_toBytes_zero]
    rw [Bytes.toBits_eq_zero zero_toBytes_zero]
  | succ k ih =>
    intros h; unfold Nat.toBits
    rw [Bits.toBytes_succ, Bits.toBytes_succ]
    rw [Bytes.toBits_succ (Bytes.not_max_toBytes h)]
    rw [Bytes.toBits_succ (Bytes.not_max_toBytes _)]
    rw [ih (lt_trans (Nat.lt_succ_self _) h)]
    apply Nat.lt_of_lt_of_le h
    rw [Nat.pow_le_pow_iff_right (Nat.lt_succ_self _)]
    rw [Nat.mul_add]; apply Nat.le_add_left

lemma subcode_compile_call {e l m n}
  (h : subcode e.code m (Func.compile l m (Func.call n))) :
    ∃ (loc : Nat) (p : Func),
      List.get? l n = some (loc, p) ∧
      loc < 2 ^ 16 ∧
      pushAt e m (Bits.toBytes (Nat.toBits (8 * 2) loc)) ∧
      Jinst.jump.At e (m + 3) := by
  rcases of_subcode h with ⟨cd, h', h_slice⟩; clear h
  rcases of_bind_eq_some h' with ⟨⟨loc, p⟩, h_get, h⟩; clear h'
  rcases of_guard_eq_some h with ⟨h_lt, h_eq⟩; clear h
  refine' ⟨loc, p, h_get, h_lt, _⟩
  simp at h_eq; rw [← h_eq] at h_slice
  simp only [pushAt, pushToBytes, pushToByte]
  rw [Bits.toBytes_length]
  refine' ⟨⟨slice_prefix h_slice, by omega⟩, _⟩
  simp only [Jinst.At]
  have hh := slice_suffix h_slice
  simp [Bytes.append, Bytes.length, Bytes.length_append, Bits.toBytes_length] at hh
  apply hh

lemma subcode_compile_branch {e k l p q}
  (h : subcode e.code k (Func.compile l k (Func.branch p q))) :
    ∃ loc : Nat,
      loc < 2 ^ 16 ∧
      pushAt e k (Bits.toBytes (Nat.toBits (8 * 2) loc)) ∧
      Jinst.jumpi.At e (k + 3) ∧
      subcode e.code (k + 4) (Func.compile l (k + 4) p) ∧
      Jinst.jumpdest.At e loc ∧
      subcode e.code (loc + 1) (Func.compile l (loc + 1) q) := by
  rcases of_subcode h with ⟨cd, h', h_slice⟩; clear h
  rcases of_bind_eq_some h' with ⟨qcd, h_qcd, h⟩; clear h'
  rcases of_guard_eq_some h with ⟨h_loc, h'⟩; clear h
  rcases of_bind_eq_some h' with ⟨pcd, h_pcd, h⟩; clear h'
  rw [← of_pure_eq_some h] at h_slice; clear h cd; rename' h_slice => h
  rw [Bytes.append_assoc, Bytes.append_assoc, Bytes.append_assoc] at h
  let loc : Nat := k + qcd.length + 4
  refine' ⟨loc, h_loc, _⟩
  simp [pushAt, pushToBytes, pushToByte]
  rw [Bits.toBytes_length]
  refine' ⟨⟨slice_prefix h, by omega⟩, _⟩
  have h' := slice_suffix h; clear h
  simp [Bytes.length_snoc, Bits.toBytes_length] at h'
  refine' ⟨slice_prefix h', _⟩
  have h := slice_suffix h'; clear h'
  rw [Nat.add_assoc] at h; simp [Bytes.length] at h; rw [h_qcd]
  refine' ⟨slice_prefix h, _⟩
  have h' := slice_suffix h; clear h
  rw [Nat.add_assoc, Nat.add_comm 4, ← Nat.add_assoc] at h'
  simp [loc]; rw [h_pcd]
  refine' ⟨slice_prefix h', slice_suffix h'⟩

lemma Prog.get?_table {m n} {c : List Func} :
    Prod.snd <$> List.get? (table m c) n = List.get? c n := by
  induction c generalizing m n with
  | nil => rfl
  | cons p c' ih =>
    cases n with
    | zero => simp [List.get?]
    | succ n => simp only [List.get?]; apply ih

-- alternative version of Exec which rolls
-- all type arguments into a structure.
structure Exec' : Type :=
  (e : Env)
  (s : State)
  (pc : Nat)
  (r : Result)
  (cr : Exec e s pc r)

inductive Exec'.Rel : Exec' → Exec' → Prop
  | step :
    ∀ {e s pc s' pc' r}
      (h_step : Step e s pc s' pc')
      (cr : Exec e s' pc' r),
      Exec'.Rel
        ⟨e, s', pc', r, cr⟩
        ⟨e, s, pc, r, @Exec.step e s pc s' pc' r h_step cr⟩
  | fst :
    ∀ {e s pc ep sp o rw sw r}
      (h_at : Xinst.At e pc o)
      (h_run : Xinst.Run' e s ep sp o rw sw)
      (cr : Exec ep sp 0 rw)
      (cr' : Exec e sw (pc + 1) r),
      Exec'.Rel
        ⟨ep, sp, 0, rw, cr⟩
        ⟨e, s, pc, r, @Exec.exec e s pc ep sp o rw sw r h_at h_run cr cr'⟩
  | snd :
    ∀ {e s pc ep sp o rw sw r}
      (h_at : Xinst.At e pc o)
      (h_run : Xinst.Run' e s ep sp o rw sw)
      (cr : Exec ep sp 0 rw)
      (cr' : Exec e sw (pc + 1) r),
      Exec'.Rel
        ⟨e, sw, pc + 1, r, cr'⟩
        ⟨e, s, pc, r, @Exec.exec e s pc ep sp o rw sw r h_at h_run cr cr'⟩

inductive Exec'.le : Exec' → Exec' → Prop
  | refl : ∀ p, Exec'.le p p
  | step : ∀ p p' p'', Exec'.le p p' → Exec'.Rel p' p'' → Exec'.le p p''

def Exec'.lt (pk pk'' : Exec') : Prop :=
  ∃ pk' : Exec', Exec'.le pk pk' ∧ Exec'.Rel pk' pk''

lemma Exec'.lt_of_prec {pk pk' : Exec'} (h : Rel pk pk') : lt pk pk' :=
  ⟨pk, .refl _, h⟩

def Exec'.gt (pk pk' : Exec') : Prop := Exec'.lt pk' pk

lemma Exec'.eq_or_lt_of_le :
  ∀ {p p'}, Exec'.le p p' → p = p' ∨ Exec'.lt p p' := by
  intros p p'' h0
  rcases h0 with ⟨_, _, p'⟩ | ⟨p', _, h1, h2⟩
  · left; rfl
  · right; refine ⟨p', h1, h2⟩

lemma Exec'.acc_of_le {pk pk' : Exec'}
    (h_le : Exec'.le pk pk') (h_acc : Acc Exec'.lt pk') : Acc Exec'.lt pk := by
  cases Exec'.eq_or_lt_of_le h_le with
  | inl h => rw [h]; exact h_acc
  | inr h => exact Acc.inv h_acc h

theorem Exec'.lt.well_founded : WellFounded Exec'.lt := by
  constructor; intro pk; rcases pk with ⟨_, _, _, _, cr⟩
  apply @Exec.rec (λ e s pc r cr => Acc Exec'.lt ⟨e, s, pc, r, cr⟩)
  · intros _ _ _ _ _ _ _ _ h_acc
    constructor; intro pk h_lt
    rcases h_lt with ⟨pk', h_le, ⟨_⟩⟩;
    apply Exec'.acc_of_le h_le h_acc
  · intro e s pc ep sp o rw sw r h_at h_rel cr cr' h_acc h_acc'
    constructor; intro pk h_lt
    rcases h_lt with ⟨pk', h_le, ⟨_⟩ | ⟨_⟩⟩;
    apply Exec'.acc_of_le h_le h_acc
    apply Exec'.acc_of_le h_le h_acc'
  · intro e s pc r h; constructor; intro pk h_lt
    rcases h_lt with ⟨pk', _, ⟨_⟩⟩

abbrev Exec'.Pred : Type := Exec' → Prop

def Exec'.imp (π π' : Exec'.Pred) : Exec'.Pred := λ pk => π pk → π' pk

infix:70 " →p " => Exec'.imp

def Exec'.Fa (π : Exec'.Pred) : Prop := ∀ pk, π pk

notation "□p" => Exec'.Fa
-- notation "□c" => Exec.Fa

def carryover (π : Exec'.Pred) : Exec'.Pred :=
(λ pk => □p (Exec'.gt pk →p π)) →p π

def Exec'.strongRec (π : Exec'.Pred) : □p (carryover π) → □p π := by
  intro ih pk
  apply @WellFounded.induction _ Exec'.lt Exec'.lt.well_founded π pk
  clear pk; intro pk ih'
  apply ih
  intro pk' h_gt
  apply ih' _ h_gt

lemma Rinst.run_of_at {e s pc o r} (cr : Exec e s pc r) (h_at : Rinst.At e pc o) :
    ∃ (s' : State) (cr' : Exec e s' (pc + 1) r),
      Rinst.Run e s o s' ∧ Exec'.Rel ⟨e, s', pc + 1, r, cr'⟩ ⟨e, s, pc, r, cr⟩ := by
  cases cr with
  | step =>
    rename State => s'; refine' ⟨s', _⟩
    have h_prec := Exec'.Rel.step asm asm
    cases (asm : Step _ _ _ _ _)
    · rw [Rinst.At_unique h_at asm]; refine' ⟨asm, asm, asm⟩
    · cases not_cop_at_of_op_at h_at asm
    · cases not_cop_at_of_op_at h_at asm
    · cases not_jop_at_of_op_at h_at asm
    · cases not_pushAt_of_op_at h_at asm
  | exec => cases not_cop_at_of_op_at h_at asm
  | halt =>
    rename Halt _ _ _ _ => h_halt; cases h_halt
    · cases not_hop_at_of_op_at h_at asm
    · cases not_slice_length h_at

lemma Xinst.run_of_at {e s pc o r}
    (cr : Exec e s pc r) (h_at : Xinst.At e pc o) :
    ∃ (s' : State) (cr' : Exec e s' (pc + 1) r),
      Xinst.Run e s o s' ∧
      Exec'.Rel ⟨e, s', pc + 1, r, cr'⟩ ⟨e, s, pc, r, cr⟩ := by
  cases cr with
  | step =>
    rename State => s'; refine' ⟨s', _⟩
    have h_prec := Exec'.Rel.step asm asm
    cases (asm : Step _ _ _ _ _)
    · cases not_cop_at_of_op_at asm h_at
    · rw [Xinst.At_unique h_at asm]
      refine ⟨_, Xinst.Run.pre asm asm asm, h_prec⟩
    · rw [Xinst.At_unique h_at asm]
      refine ⟨asm, Xinst.Run.fail asm, h_prec⟩
    · cases not_jop_at_of_cop_at h_at asm
    · cases not_pushAt_of_cop_at h_at asm
  | exec =>
    cases Xinst.At_unique h_at (asm : Xinst.At _ _ _)
    have h_prec := Exec'.Rel.snd asm asm asm asm
    refine' ⟨_, _, Xinst.Run.exec asm asm, h_prec⟩
  | halt =>
    rename Halt _ _ _ _ => h_halt; cases h_halt
    · cases not_hop_at_of_cop_at h_at asm
    · cases not_slice_length h_at

lemma push_of_pushAt {e s pc bs r} (cr : Exec e s pc r) (h_at : pushAt e pc bs) :
    ∃ (s' : State) (cr' : Exec e s' (pc + bs.length + 1) r),
      State.Push [Bytes.toBits 32 bs] s s' ∧
      Exec'.Rel ⟨e, s', pc + bs.length + 1, r, cr'⟩ ⟨e, s, pc, r, cr⟩ := by
  cases cr with
  | step =>
    rename State => s'; refine' ⟨s', _⟩
    have h_prec := Exec'.Rel.step asm asm
    rename Step _ _ _ _ _ => h_step; cases h_step
    · cases not_pushAt_of_op_at  asm h_at
    · cases not_pushAt_of_cop_at asm h_at
    · cases not_pushAt_of_cop_at asm h_at
    · cases not_pushAt_of_jop_at asm h_at
    · rename (pushAt e pc _) => h_at'
      cases pushAt_unique h_at h_at'
      refine' ⟨_, asm, h_prec⟩
  | exec =>
    cases not_pushAt_of_cop_at asm h_at
  | halt =>
    rename Halt _ _ _ _ => h_halt; cases h_halt
    · cases not_pushAt_of_hop_at asm h_at
    · cases not_slice_length <| slice_prefix <| And.left asm

lemma length_pushToBytes {bs} : (pushToBytes bs).length = bs.length + 1 := by
  simp [pushToBytes, Bytes.length]
  rw [Bytes.length_append, Nat.add_comm]; rfl

lemma Inst.run_of_at {e s pc i r}
    (cr : Exec e s pc r) (h_at : Inst.At e pc i) :
    ∃ (s' : State) (cr' : Exec e s' (pc + i.toBytes.length) r),
      Inst.Run e s i s' ∧
      Exec'.Rel ⟨e, s', pc + i.toBytes.length, r, cr'⟩ ⟨e, s, pc,r, cr⟩ := by
  cases i with
  | reg o =>
    rcases Rinst.run_of_at cr h_at with ⟨s', cr', h_run, h_prec⟩
    refine' ⟨s', cr', .reg h_run, h_prec⟩
  | exec o =>
    rcases Xinst.run_of_at cr h_at with ⟨s', cr', h_run, h_prec⟩
    refine' ⟨s', cr', .exec h_run, h_prec⟩
  | push bs h =>
    rcases push_of_pushAt cr h_at with ⟨s', cr', h_push, h_prec⟩
    simp [toBytes]; rw [length_pushToBytes, ← Nat.add_assoc]
    refine' ⟨s', _, _, h_prec⟩; exact Inst.Run.push _ h_push

lemma Jinst.run_of_at {e s pc o r} (cr : Exec e s pc r) (h_at : Jinst.At e pc o) :
    ∃ (s' : State) (pc' : Nat), ∃ (cr' : Exec e s' pc' r),
      Jinst.Run e s pc o s' pc' ∧
      Exec'.Rel ⟨e, s', pc', r, cr'⟩ ⟨e, s, pc, r, cr⟩ := by
  cases cr with
  | step =>
    rename State => s'; refine' ⟨s', _⟩
    have h_prec := Exec'.Rel.step asm asm
    rename Step _ _ _ _ _ => h_step; cases h_step
    · cases not_jop_at_of_op_at asm h_at
    · cases not_jop_at_of_cop_at asm h_at
    · cases not_jop_at_of_cop_at asm h_at
    · refine' ⟨_, _, _, h_prec⟩
      rw [Jinst.At_unique h_at asm]
      assumption
    · cases not_pushAt_of_jop_at h_at asm
  | exec => cases not_jop_at_of_cop_at asm h_at
  | halt =>
    rename Halt _ _ _ _ => h_halt; cases h_halt
    · cases not_hop_at_of_jop_at h_at asm
    · cases not_slice_length h_at

lemma jump_at {e s pc r} (cr : Exec e s pc r) (h : Jinst.At e pc Jinst.jump) :
    ∃ (x : Word) (s' : State) (cr' : Exec e s' x.toNat r),
      State.Pop [x] s s' ∧
      Jumpable e x.toNat ∧
      Exec'.Rel ⟨e, s', x.toNat, r, cr'⟩ ⟨e, s, pc, r, cr⟩ := by
  rcases Jinst.run_of_at cr h with ⟨s', pc', cr', h_run, h_prec⟩
  cases h_run; refine ⟨_, _, cr', asm, asm, h_prec⟩

lemma jumpi_at {e s pc r} (cr : Exec e s pc r) (h : Jinst.At e pc Jinst.jumpi) :
    ( ∃ (x : Word) (s' : State) (cr' : Exec e s' (pc + 1) r),
        State.Pop [x, 0] s s' ∧
        Exec'.Rel ⟨e, s', pc + 1, r, cr'⟩ ⟨e, s, pc, r, cr⟩ ) ∨
    ( ∃ (x y : Word) (s' : State) (cr' : Exec e s' x.toNat r),
        State.Pop [x, y] s s' ∧
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
    l.get? (k + 1) = some x → ∃ y, l.get? k = some y := by
  induction k generalizing l x with
  | zero =>
    match l with
    | [] => simp [List.get?]
    | [_] => simp [List.get?]
    | (y :: _ :: _) => intro _; refine' ⟨y, rfl⟩
  | succ k ih =>
    match l with
    | [] => simp [List.get?]
    | (_ :: l') =>
      simp only [List.get?]
      intro h_get; apply ih h_get

lemma table_suffix {c k pfx sfx} (h : pfx <++ (table k c) ++> sfx) :
    ∃ k' c', sfx = table k' c' := by
  induction c generalizing k pfx sfx with
  | nil => refine' ⟨k, [], (List.append_eq_nil.mp h.symm).right⟩
  | cons p ps ih =>
    simp [table] at h
    rcases List.cons_eq_append.mp h with
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
    simp [Bytes.length_append, Bytes.length, compsize, Bytes.append]
    rw [toBytes_length, ihp h_cp, ihq h_cq]; omega
  | last o => simp [compile] at h; rw [← h]; rfl
  | next o p ih =>
    rcases of_bind_eq_some h with ⟨bs', h, h'⟩;
    simp at h'; rw [← h']
    simp [Bytes.length_append, compsize, Bytes.length]
    rw [ih h, Nat.add_comm]
  | call m =>
    rcases of_bind_eq_some h with ⟨⟨_, _⟩, _, h'⟩; clear h
    rcases of_guard_eq_some h' with ⟨h'', h⟩; clear h' h''
    simp at h; rw [← h];
    simp [Bytes.length_append, Bytes.length, compsize, Bytes.append]
    rw [toBytes_length]

lemma of_get?_table_eq_some {f fs} {bs} {m n : ℕ} {p : Func}
    (h_eq : some bs = Prog.compile ⟨f, fs⟩)
    (h_get : List.get? (table 0 (f :: fs)) m = some (n, p)) :
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
    simp [List.get?] at h_get
    cases h_get.left; cases h_get.right; clear h_get
    simp only [table]
    refine' ⟨ [], _ , rfl, List.nil_append _, ⟪⟫,
              bs, rfl, Bytes.nil_append.symm, _ ⟩
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
      rw [h_split, List.get?_append_right h_le, h_lft, h_sub] at h_get
      match rgt with
      | [] => simp [List.get?] at h_get
      | _ :: rgt' =>
        simp [List.get?] at h_get
        rw [h_get]; refine ⟨_, rfl⟩
    rcases h with ⟨rgt', h_rgt'⟩
    refine' ⟨rgt', _, _, _⟩
    · simp [List.length, h_lft]
    · simp [Split]; rw [← h_rgt', h_split]
    · rcases Table.compile_cons_eq_some h_sfx.symm with
        ⟨cq, cl, h_cq, h_cl, h_sfx'⟩
      refine' ⟨pfx ++ (⟪Jinst.jumpdest.toByte⟫ ++ cq), cl, _, _, _⟩
      · have hn : n = k + compsize q + 1 := by
          rcases table_suffix h_split with
            ⟨k', _ | ⟨q', c'⟩, h⟩ <;> simp [table] at h
          rcases h with ⟨⟨⟨_⟩,⟨_⟩⟩, h⟩
          rw [h_rgt'] at h
          cases c' <;> simp [table] at h
          apply h.left.left
        simp [Bytes.length_append, Bytes.length]
        rw [h_pfx, hn, Func.length_compile h_cq]
        omega
      · simp only [Split]; rw [Bytes.append_assoc, ← h_sfx', h_split']
      · rw [← h_cl, ← h_rgt']

lemma subcode_of_get?_eq_some {f fs} {e : Env} {k : ℕ} {p : Func}
    (h_eq : some e.code = Prog.compile ⟨f, fs⟩)
    (h_get : List.get? (table 0 (f :: fs)) m = some (k, p)) :
    Jinst.At e k Jinst.jumpdest ∧
    subcode e.code (k + 1) (Func.compile (table 0 (f :: fs)) (k + 1) p) := by
  rcases of_get?_table_eq_some h_eq h_get with
    ⟨lft, rgt, _, _, pfx, sfx, h_pfx, h_split', h_sfx⟩
  unfold Jinst.At
  rcases Table.compile_cons_eq_some h_sfx.symm with ⟨bs, bs', h_bs, _, h_sfx'⟩
  have h_slice : slice e.code k sfx := by
    rw [← h_pfx, h_split']; apply append_slice_suffix
  rw [h_sfx', Bytes.append_assoc] at h_slice
  refine' ⟨slice_prefix h_slice, _⟩
  rw [h_bs]; simp [subcode]
  apply slice_prefix <| slice_suffix h_slice

theorem correct_core (f : Func) (fs : List Func) :
    ∀ (pk : Exec') (p : Func),
      some pk.e.code = Prog.compile ⟨f, fs⟩ →
      subcode pk.e.code pk.pc (Func.compile (table 0 (f :: fs)) pk.pc p) →
      Func.Run (f :: fs) pk.e pk.s p pk.r := by
  apply Exec'.strongRec; intro pk ih p h_eq h_sub
  match p with
  | .last o =>
    apply Func.Run.last <| Hinst.run_of_at pk.cr h_sub
  | .next i p =>
    rcases of_subcode h_sub with ⟨cd, h_eq', h_slice⟩; clear h_sub
    rcases of_bind_eq_some h_eq' with ⟨cd', h_eq'', h_rw⟩; clear h_eq'
    simp [pure] at h_rw; rw [← h_rw] at h_slice; clear h_rw cd
    have h_at : Inst.At pk.e pk.pc i := by
      rw [Inst.At_iff_slice]; apply slice_prefix h_slice
    rcases Inst.run_of_at pk.cr h_at with ⟨s', cr', h_run, h_prec⟩
    have h_run' : Func.Run (f :: fs) pk.e s' p pk.r := by
      apply ih ⟨pk.e, s', _, pk.r, cr'⟩ (Exec'.lt_of_prec h_prec) p
      · simp; apply h_eq
      · simp; rw [h_eq'']; apply slice_suffix h_slice
    apply Func.Run.next h_run h_run'
  | .branch p q =>
    rcases subcode_compile_branch h_sub with
      ⟨loc, h_loc, h_push, h_jumpi, h_scp, h_jumpdest, h_scq⟩
    have h : ∃ (s' : State) (cr' : Exec pk.e s' (pk.pc + 3) pk.r),
             State.Push [Nat.toBits 256 loc] pk.s s' ∧
             Exec'.Rel ⟨pk.e, s', pk.pc + 3, pk.r, cr'⟩ pk := by
      rcases push_of_pushAt pk.cr h_push with ⟨s', cr', h, h_prec⟩
      rw [← @pow_add_toBytes_toBits loc 30 2 h_loc, Bits.toBytes_toBits] at h
      have h_rw : pk.pc +3 = pk.pc + Bytes.length (Bits.toBytes (Nat.toBits (8 * 2) loc)) + 1 := by
        rw [@toBytes_length 2 (Nat.toBits (8 * 2) loc)]
      rw [h_rw]; refine' ⟨s', cr', h, h_prec⟩
    clear h_push; rcases h with ⟨s', cr, h_push, h_prec⟩
    rcases jumpi_at cr h_jumpi with
        ⟨x, s'', cr', h_pop, h_prec'⟩
      | ⟨x, y, s'', cr', h_pop, h_jmp, hy, h_prec'⟩ <;> clear h_jumpi
    · clear h_scq h_jumpdest
      have h_pop' : State.Pop [0] pk.s s'' := by
        rcases (State.push_cons_pop_cons h_push h_pop).right
          with ⟨st, h_push', h_pop'⟩
        rw [State.push_nil h_push']; exact h_pop'
      apply Func.Run.zero h_pop'
      have h_lt : Exec'.lt ⟨pk.e, s'', pk.pc +4, pk.r, cr'⟩ pk := by
        refine' ⟨_, _, h_prec⟩
        apply Exec'.le.step _ _ _ _ h_prec'
        apply Exec'.le.refl _
      apply ih ⟨pk.e, s'', pk.pc + 4, pk.r, cr'⟩ h_lt p h_eq h_scp
    · clear h_jmp h_scp
      have h_loc' : loc < 2 ^ 256 := by
        apply Nat.lt_trans h_loc
        rw [Nat.pow_lt_pow_iff_right] <;> omega
      have h : x.toNat = loc ∧ State.Pop [y] pk.s s'' := by
        rcases State.push_cons_pop_cons h_push h_pop
          with ⟨hx, st, h_push', h_pop'⟩
        rw [ State.push_nil h_push',
             ← congrArg Bits.toNat hx,
             toBits_toNat loc h_loc' ]
        refine ⟨rfl, h_pop'⟩
      rcases h with ⟨hx, h_pop'⟩
      have h_run' : Func.Run (f :: fs) pk.e s'' q pk.r := by
        rw [← hx] at h_jumpdest
        rcases jumpdest_at cr' h_jumpdest with ⟨cr'', h_prec''⟩
        have h_lt : Exec'.lt ⟨pk.e, s'', toNat x + 1, pk.r, cr''⟩ pk := by
          refine' ⟨_, _, h_prec⟩
          apply Exec'.le.step _ _ _ _ h_prec'
          apply Exec'.le.step _ _ _ _ h_prec''
          apply Exec'.le.refl _
        rw [← hx] at h_scq
        apply ih ⟨pk.e, s'', toNat x + 1, pk.r, cr''⟩ h_lt q h_eq h_scq
      apply Func.Run.succ hy h_pop' h_run'
  | .call k =>
    rcases subcode_compile_call h_sub with ⟨loc, p, h_get, h_loc, h_push, h_jump⟩
    have h_get' : List.get? (f :: fs) k = p := by
      rw [← @Prog.get?_table 0 k (f :: fs), h_get]; rfl
    apply Func.Run.call h_get'
    have h : ∃ (s' : State) (cr' : Exec pk.e s' (pk.pc + 3) pk.r),
             State.Push [Nat.toBits 256 loc] pk.s s' ∧
             Exec'.Rel ⟨pk.e, s', pk.pc + 3, pk.r, cr'⟩ pk := by
      rcases push_of_pushAt pk.cr h_push with ⟨s', cr', h, h_prec⟩
      rw [← @pow_add_toBytes_toBits loc 30 2 h_loc, Bits.toBytes_toBits] at h
      have h_rw : pk.pc + 3 = pk.pc + Bytes.length (Bits.toBytes (Nat.toBits (8 * 2) loc)) + 1 := by
        rw [@toBytes_length 2 (Nat.toBits (8 * 2) loc)]
      rw [h_rw]; refine' ⟨s', cr', h, h_prec⟩
    clear h_push; rcases h with ⟨s, cr, h_push, h_prec⟩
    rcases jump_at cr h_jump with ⟨x, s', cr', h_pop, h, h_prec'⟩
    rcases h with ⟨h_jumpable, h⟩; clear h
    rcases subcode_of_get?_eq_some h_eq h_get with ⟨h, hp⟩; clear h
    rcases jumpdest_at cr' h_jumpable with ⟨cr'', h_prec''⟩
    have h_loc' : loc < 2 ^ 256 := by
      apply Nat.lt_trans h_loc
      rw [Nat.pow_lt_pow_iff_right] <;> omega
    have h : loc = x.toNat ∧ pk.s = s' := by
      rcases State.push_cons_pop_cons h_push h_pop with ⟨hx, st, h_push', h_pop'⟩
      rw [State.push_nil h_push', State.pop_nil h_pop']
      rw [← congrArg Bits.toNat hx, toBits_toNat loc h_loc']; simp
    rcases h with ⟨h_rw, h_rw'⟩
    rw [h_rw']; rw [h_rw] at hp
    have h_lt : Exec'.lt ⟨pk.e, s', toNat x + 1, pk.r, cr''⟩ pk := by
      refine' ⟨_, _, h_prec⟩
      apply Exec'.le.step _ _ _ _ h_prec'
      apply Exec'.le.step _ _ _ _ h_prec''
      apply Exec'.le.refl _
    apply ih ⟨pk.e, s', toNat x + 1, pk.r, cr''⟩ h_lt p h_eq hp

theorem correct (e : Env) (s : State) (p : Prog) (r : Result)
    (cr : Exec e s 0 r) (h : some e.code = p.compile) :
    Prog.Run e s p r := by
  rcases @subcode_of_get?_eq_some 0 p.main p.aux e 0 p.main h rfl
    with ⟨h_at, h_sub⟩
  rcases jumpdest_at cr h_at with ⟨cr', h⟩; clear h h_at
  apply correct_core p.main p.aux ⟨e, s, 1, r, cr'⟩ p.main h h_sub

def Prog.At (p : Prog) (ca : Addr)
    (e : Env) (s : State) (pc : Nat) : Prop :=
  some (s.code ca) = Prog.compile p ∧
  (e.cta = ca → (some e.code = Prog.compile p ∧ pc = 0))

def Exec.Wkn (ca : Addr) (p : Prog)
    (π : Exec.Pred)
    (e s pc r) (ex : Exec e s pc r) : Prop :=
  p.At ca e s pc → π _ _ _ _ ex

def ForallDeeper (k : Nat) (ε : Exec.Pred) : Prop :=
  ∀ e s pc r (ex : Exec e s pc r), e.exd < k → ε _ _ _ _ ex

def ForallDeeperAt (k : Nat) (ca : Addr) (p : Prog) (ε : Exec.Pred) : Prop :=
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

lemma call_or_statcall_of_ne {e s ep sp o rx sw}
    (ho : Xinst.isCall o)
    (h_run : Xinst.Run' e s ep sp o rx sw)
    (h_ne : e.cta ≠ ep.cta) : o = .call ∨ o = .statcall := by
  cases h_run
  · cases ho
  · cases ho
  · left; rfl
  · cases h_ne rfl
  · cases h_ne rfl
  · right; rfl

lemma Xinst.rel_inv_code {a} {e s ep sp o rx sw}
    (h_cr : Xinst.Run' e s ep sp o rx sw)
    (h_ne : s.code a ≠ ⟪⟫)
    (h_run : Exec ep sp 0 rx) : s.code a = sw.code a := by
  have h_ne' : sp.code a ≠ Bytes.nil := by
    rw [← Xinst.prep_inv_code h_cr]; exact h_ne
  rw [Xinst.prep_inv_code h_cr, Exec.inv_code h_run h_ne']
  apply Xinst.wrap_inv_code'' h_cr h_ne

lemma combine_prog
    {ε : Exec.Pred}
    {π : Prog.Pred}
    (h_imp : ∀ {e s p r} (ex : Exec e s 0 r), π e s p r → ε _ _ _ _ ex)
    {ca : Addr}
    {p : Prog}
    ( h_inv :
      ∀ {e s r},
        Prog.Run e s p r → e.cta = ca →
        ForallDeeperAt e.exd ca p ε → π e s p r )
    {e : Env} {s : State}
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
    (ca : Addr) (p : Prog)
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

def ForallSubExec (k : Nat) (ca : Addr) (p : Prog)
    (R : Env → State → Result → Prop) : Prop :=
  ∀ e s pc r,
    Exec e s pc r →
    e.exd < k →
    p.At ca e s pc →
    R e s r

lemma lift
    (R : Env → State → Result → Prop)
    (ca : Addr) -- contract address
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
    (ca : Addr) (p : Prog)
    (σ : Env → State → Prop)
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

lemma prefix_of_not {x xs} {s s' : State} :
    State.Not s s' → (x :: xs <<+ s.stk) → (~ x :: xs <<+ s'.stk) := by show_prefix_one

lemma prefix_of_eq {x y xs} {s s'} :
    State.Eq s s' → (x :: y :: xs <<+ s.stk) → ((x =? y) :: xs <<+ s'.stk) := by show_prefix_two

lemma prefix_of_lt {x y xs} {s s'} :
    State.Lt s s' → (x :: y :: xs <<+ s.stk) → ((x <? y) :: xs <<+ s'.stk) :=
  by show_prefix_two

lemma prefix_of_gt {x y xs} {s s'} :
    State.Gt s s' → (x :: y :: xs <<+ s.stk) → ((x >? y) :: xs <<+ s'.stk) :=
  by show_prefix_two

lemma prefix_of_shl {x y xs} {s s' : State} :
    State.Shl s s' → (x :: y :: xs <<+ s.stk) → (Bits.shl x.toNat y :: xs <<+ s'.stk) :=
  by show_prefix_two

lemma prefix_of_shr {x y xs} {s s' : State} :
    State.Shr s s' → (x :: y :: xs <<+ s.stk) → (Bits.shr x.toNat y :: xs <<+ s'.stk) :=
  by show_prefix_two

lemma prefix_of_or {x y xs} {s s' : State} :
    State.Or s s' → (x :: y :: xs <<+ s.stk) → (Bits.or x y :: xs <<+ s'.stk) :=
  by show_prefix_two

lemma prefix_of_and {x y xs} {s s' : State} :
    State.And s s' → (x :: y :: xs <<+ s.stk) → (Bits.and x y :: xs <<+ s'.stk) :=
  by show_prefix_two

lemma prefix_of_add {x y xs} {s s' : State} :
    State.Add s s' → (x :: y :: xs <<+ s.stk) → ((x + y) :: xs <<+ s'.stk) :=
  by show_prefix_two

lemma prefix_of_sub {x y xs} {s s' : State} :
    State.Sub s s' → (x :: y :: xs <<+ s.stk) → ((x - y) :: xs <<+ s'.stk) :=
  by show_prefix_two

lemma prefix_of_mstore {x y xs} {s s'} :
    State.Mstore s s' → (x :: y :: xs <<+ s.stk) → (xs <<+ s'.stk) := by
  intros h_mstore h_pfx
  rcases h_mstore with ⟨x', y', h⟩
  have h_pop := Stack.of_diff_nil h.stk; clear h
  rcases of_cons_cons_pref_of_cons_cons_pref h_pfx (pref_of_split h_pop)
    with ⟨hx, hy, h⟩; clear h
  rw [hx, hy] at h_pfx
  apply @of_append_pref _ _ xs _ _ h_pop h_pfx

lemma prefix_of_sstore {e} {x y xs} {s s' : State} :
    State.Sstore e s s' → (x :: y :: xs <<+ s.stk) → (xs <<+ s'.stk) := by
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
    State.Sload e s s' → (x :: xs <<+ s.stk) →
    (s.stor e.cta x :: xs <<+ s'.stk) :=
  by show_prefix_one

lemma prefix_of_sload' {e x xs} {s s'} :
    State.Sload e s s' → (x :: xs <<+ s.stk) →
    ∃ y, (y :: xs <<+ s'.stk) ∧ y = s.stor e.cta x := by
  intros h0 h1; refine ⟨_, prefix_of_sload h0 h1, rfl⟩

lemma prefix_of_push {xs ys} {s s'} :
    State.Push xs s s' → (ys <<+ s.stk) → ((xs ++ ys) <<+ s'.stk) :=
  λ h0 h1 => append_pref h0.stk h1

lemma prefix_of_pop {y : Word} {xs} {s s' : State} :
    (∃ x, State.Pop [x] s s') → (y :: xs <<+ s.stk) → (xs <<+ s'.stk) := by
  intros h h'; rcases h with ⟨x, hx⟩
  have h_eq : y = x :=
    (List.of_cons_pref_of_cons_pref h' (pref_of_split hx.stk)).left
  rw [h_eq] at h'; apply @of_append_pref _ [x] _ _ _ hx.stk h'

lemma prefix_of_iszero {x xs} {s s' : State} :
    State.Iszero s s' → (x :: xs <<+ s.stk) → ((if x = 0 then 1 else 0) :: xs <<+ s'.stk) :=
  by show_prefix_one

lemma prefix_of_caller {e xs} {s s' : State} :
    State.Caller e s s' → (xs <<+ s.stk) → (e.cla.toWord :: xs <<+ s'.stk) :=
  by show_prefix_zero

lemma prefix_of_callvalue {e xs} {s s' : State} :
   State.Callvalue e s s' → (xs <<+ s.stk) → (e.clv :: xs <<+ s'.stk) :=
 by show_prefix_zero

lemma prefix_of_calldatacopy {e x y z xs} {s s' : State} :
    State.Calldatacopy e s s' → (x :: y :: z :: xs <<+ s.stk) → (xs <<+ s'.stk) := by
  intros h0 h1; rcases h0 with ⟨x', y', z', sc, h0,_⟩
  have h2 := h0.stk; clear h0;
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2)
    with ⟨hx, hy, ws, h, h'⟩
  rcases List.of_cons_pref_of_cons_pref h h' with ⟨hz, _⟩
  rw [hx, hy, hz] at h1; apply of_append_pref h2 h1

lemma Line.spx_scheme {e s' i l xs xs' ys}
    (h : ∀ s0 s1, Inst.Run e s0 i s1 → (xs <<+ s0.stk) → (xs' <<+ s1.stk))
    (h' : ∀ s : State, (xs' <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) :
    ∀ s : State, (xs <<+ s.stk) → Line.Run e s (i :: l) s'→ (ys <<+ s'.stk) := by
  intros s h_pfx h_run
  rcases Line.of_run_cons h_run with ⟨s_mid, h_head, h_tail⟩
  apply h' s_mid (h _ _ h_head h_pfx) h_tail

lemma Line.spx_push {e : Env} {s' l bs p xs ys} :
    (∀ s : State, (bs.toBits 32 :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : State, (xs <<+ s.stk) → Line.Run e s (push bs p :: l) s'→ (ys <<+ s'.stk)) := by
  intros h_next s h_pfx h_run
  rcases Line.of_run_cons h_run with ⟨s_mid, h_head, h_tail⟩
  apply h_next s_mid _ h_tail
  apply prefix_of_push (of_run_push h_head) h_pfx

lemma Line.spx_pushWord {e : Env} {s' l x xs ys} :
    (∀ s : State, (x :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : State, (xs <<+ s.stk) → Line.Run e s (pushWord x :: l) s'→ (ys <<+ s'.stk)) := by
  intros h_next s h_pfx h_run
  rcases Line.of_run_cons h_run with ⟨s_mid, h_head, h_tail⟩
  apply h_next s_mid _ h_tail
  apply prefix_of_push (of_run_pushWord h_head) h_pfx

macro "spx_conv" : tactic =>
  `(tactic| conv => ext; ext; rw [← op_run_iff_inst_run]; rfl)

lemma Line.spx_mstore {e : Env} {s' l x y xs ys} :
    (∀ s : State, (xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : State, (x :: y :: xs <<+ s.stk) → Line.Run e s (mstore :: l) s'→ (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_mstore

lemma Line.spx_sstore {e : Env} {s' l x y xs ys} :
    (∀ s : State, (xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : State, (x :: y :: xs <<+ s.stk) → Line.Run e s (sstore :: l) s'→ (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_sstore

lemma Line.spx_dup {e s' l xs ys} {n : Fin 16} (x) :
  Stack.Nth n.val x xs →
    (∀ s : State, (x :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : State, (xs <<+ s.stk) → Line.Run e s (dup n :: l) s' → (ys <<+ s'.stk)) := by
  intro h_nth; apply Line.spx_scheme
  spx_conv; intros s0 s1 h_step
  apply Stack.prefix_of_dup ⟨x, rfl, h_nth⟩ h_step.stk

lemma Line.spx_log (zs : Stack) {e s' l xs ys} {n : Fin 5} :
    zs.length = n.val + 2 →
    (∀ s : State, (xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : State, (zs ++ xs <<+ s.stk) → Line.Run e s (log n :: l) s' → (ys <<+ s'.stk)) := by
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
    (∀ s : State, (xs' <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : State, (xs <<+ s.stk) → Line.Run e s (swap n :: l) s' → (ys <<+ s'.stk)) := by
  intro h_swap; apply Line.spx_scheme;
  spx_conv; intros s0 s1 h_step
  apply Stack.prefix_of_swap h_swap h_step.stk

lemma Line.spx_iszero {e s' l} {x} {xs ys} :
    (∀ s : State, ((x =? 0) :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : State, (x :: xs <<+ s.stk) → Line.Run e s (iszero :: l) s' → (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_iszero

lemma Line.spx_pop {e : Env} {s' l x xs ys} :
    (∀ s : State, (xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : State, (x :: xs <<+ s.stk) → Line.Run e s (pop :: l) s'→ (ys <<+ s'.stk)) :=by
  apply Line.spx_scheme; spx_conv; apply prefix_of_pop

lemma Line.spx_eq {e s' l x y xs ys}  :
    (∀ s : State, ((x =? y) :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : State, (x :: y :: xs <<+ s.stk) → Line.Run e s (eq :: l) s' → (ys <<+ s'.stk)) :=by
  apply Line.spx_scheme; spx_conv; apply prefix_of_eq

lemma Line.spx_lt {e s' l x y xs ys}  :
    (∀ s : State, ((x <? y) :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : State, (x :: y :: xs <<+ s.stk) → Line.Run e s (lt :: l) s' → (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_lt

lemma Line.spx_gt {e s' l x y xs ys}  :
    (∀ s : State, ((x >? y) :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : State, (x :: y :: xs <<+ s.stk) → Line.Run e s (gt :: l) s' → (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_gt

lemma Line.spx_sub {e s' l x y xs ys}  :
    (∀ s : State, ((x - y) :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : State, (x :: y :: xs <<+ s.stk) → Line.Run e s (sub :: l) s' → (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_sub

lemma Line.spx_not {e s' l x xs ys}  :
    (∀ s : State, (~ x :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : State, (x :: xs <<+ s.stk) → Line.Run e s (not :: l) s' → (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_not

lemma Line.spx_or {e s' l x y xs ys}  :
    (∀ s : State, (Bits.or x y :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : State, (x :: y :: xs <<+ s.stk) → Line.Run e s (or :: l) s' → (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_or

lemma Line.spx_and {e s' l x y xs ys}  :
    (∀ s : State, (Bits.and x y :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : State, (x :: y :: xs <<+ s.stk) → Line.Run e s (and :: l) s' → (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_and

lemma Line.spx_shl {e s' l} {x y : Word} {xs ys}  :
    (∀ s : State, (Bits.shl x.toNat y :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : State, (x :: y :: xs <<+ s.stk) → Line.Run e s (shl :: l) s' → (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_shl

lemma Line.spx_shr {e s' l} {x y : Word} {xs ys}  :
    (∀ s : State, (Bits.shr x.toNat y :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : State, (x :: y :: xs <<+ s.stk) → Line.Run e s (shr :: l) s' → (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_shr

lemma Line.spx_add {e s' l x y xs ys}  :
    (∀ s : State, ((x + y) :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : State, (x :: y :: xs <<+ s.stk) → Line.Run e s (add :: l) s' → (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_add

lemma Line.spx_caller {e : Env} {s' l xs ys}  :
    (∀ s : State, (e.cla.toWord :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : State, (xs <<+ s.stk) → Line.Run e s (caller :: l) s' → (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_caller

lemma Line.spx_callvalue {e : Env} {s' l xs ys}  :
    (∀ s : State, (e.clv :: xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : State, (xs <<+ s.stk) → Line.Run e s (callvalue :: l) s' → (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_callvalue

lemma Line.spx_calldatacopy {e : Env} {s' l x y z xs ys}  :
    (∀ s : State, (xs <<+ s.stk) → Line.Run e s l s' → (ys <<+ s'.stk)) →
    (∀ s : State, (x :: y :: z :: xs <<+ s.stk) → Line.Run e s (calldatacopy :: l) s' → (ys <<+ s'.stk)) := by
  apply Line.spx_scheme; spx_conv; apply prefix_of_calldatacopy

lemma Line.spx_unwrap {e xs} {s' : State} :
    ∀ s : State, (xs <<+ s.stk) → Line.Run e s [] s' → (xs <<+ s'.stk) := by
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

def appRefl : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.evalRefl Lean.Syntax.missing

def show_swap' : Nat → Lean.Elab.Tactic.TacticM Unit
  | 0 => "Stack.swapCore_zero".apply
  | n + 1 => do "Stack.swapCore_succ".apply; show_swap' n

def fail {ξ} (s : String) : Lean.Elab.Tactic.TacticM ξ := do
  dbg_trace s; failure

def get_swap_core (xx : Q(Word)) : Nat → Q(Stack) → Lean.Elab.Tactic.TacticM (Q(Word) × Q(Stack))
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
  | ~q(∀ s : _root_.State, ($px <<+ s.stk) → Line.Run _ s $lx _ → _) =>
    let lx' : Q(Line) ← Lean.Meta.whnf lx
    match lx' with
    | ~q([]) => "Line.spx_unwrap".apply
    | ~q($ix :: _) =>
      match ix with
      | ~q(Inst.dup $nx) =>
        let n ← unsafe Lean.Meta.evalExpr (Fin 16) q(Fin 16) nx
        "Line.spx_dup".apply; show_nth' n.val
      | ~q(Inst.log $nx) =>
        let n ← unsafe Lean.Meta.evalExpr (Fin 5) q(Fin 5) nx
        let x ← get_take (n.val + 2) px
        Lean.Expr.apply <| Lean.mkApp "Line.spx_log".toExpr x
        Lean.Elab.Tactic.evalRefl Lean.Syntax.missing
        --appRefl
      | ~q(Inst.swap $nx) =>
        let n ← unsafe Lean.Meta.evalExpr (Fin 16) q(Fin 16) nx
        let x ← get_swap n.val px
        Lean.Expr.apply <| Lean.mkApp "Line.spx_swap".toExpr x
        show_swap' n.val
      | ~q(Inst.pushWord _) => "Line.spx_pushWord".apply
      | ~q(Inst.push _ _) => "Line.spx_push".apply
      | ~q(Inst.sub) => "Line.spx_sub".apply
      | ~q(Inst.add) => "Line.spx_add".apply
      | ~q(Inst.pop) => "Line.spx_pop".apply
      | ~q(Inst.sstore) => "Line.spx_sstore".apply
      | ~q(Inst.mstore) => "Line.spx_mstore".apply
      | ~q(Inst.lt) => "Line.spx_lt".apply
      | ~q(Inst.gt) => "Line.spx_gt".apply
      | ~q(Inst.eq) => "Line.spx_eq".apply
      | ~q(Inst.not) => "Line.spx_not".apply
      | ~q(Inst.and) => "Line.spx_and".apply
      | ~q(Inst.or) => "Line.spx_or".apply
      | ~q(Inst.shl) => "Line.spx_shl".apply
      | ~q(Inst.shr) => "Line.spx_shr".apply
      | ~q(Inst.iszero) => "Line.spx_iszero".apply
      | ~q(Inst.caller) => "Line.spx_caller".apply
      | ~q(Inst.callvalue) => "Line.spx_callvalue".apply
      | ~q(Inst.calldatacopy) => "Line.spx_calldatacopy".apply
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
open Qq

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

lemma Line.of_inv_state (motive : (Addr → Storage) → Prop) (e s l s') (h_run : Line.Run e s l s')
    (h_inv : Line.Inv State.stor l) (hs' : motive s'.stor) : motive s.stor := by
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
    let ds ← ctx.foldlM (addIfOcc <| Expr.app q(State.stor) s) []
    Lean.FVarId.revert (ds.map LocalDecl.fvarId)
    let g ← Lean.Elab.Tactic.getMainTarget
    let g' := replaceWithBvar (Expr.app q(State.stor) s) 0 g
    Expr.apply <|
      Lean.mkApp6 q(Line.of_inv_state)
        (Expr.lam `s q(Addr → Storage) g' BinderInfo.default)
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

open Inst

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

lemma run_prepend_elim (φ : Prop) (l) {p} {c e} {s : _root_.State} {r}
    (h : ∀ s', Line.Run e s l s' → Func.Run c e s' p r → φ)
    (h' : Func.Run c e s (l +++ p) r) : φ := by
  rcases of_run_prepend _ _ h' with ⟨s', hs, hs'⟩; apply h s' hs hs'

lemma run_append_elim (φ : Prop) (l) {l'} {e} {s s'' : _root_.State}
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
  | ~q(_ <<+ (State.stk $x')) => pure (← Lean.Meta.isDefEq x x')
  | _ => pure false

def initStateOfRun : Q(Prop) → TacticM Expr
  | ~q(Line.Run _ $sx _ _) => pure sx
  | _ => failure

def Expr.imp (x y : Expr) : Expr := Expr.forallE Name.anonymous x y BinderInfo.default

def mkMotive : Q(Prop) → TacticM Expr
| ~q(($p <<+ (State.stk $s₀)) → (Line.Run $e $s₀ $l $s₁) → $φ) => do
  pure <|
    Expr.lam `s q(_root_.State)
      ( Expr.imp
          (Expr.app q(λ s : _root_.State => $p <<+ s.stk) (Expr.bvar 0))
          (Expr.imp (Expr.app q(λ s : _root_.State => Line.Run $e s $l $s₁) (Expr.bvar 1)) φ) )
      BinderInfo.default
| _ => failure

lemma apply_univ {ξ : Type} (φ : ξ → Prop) (x : ξ) (h : ∀ x, φ x) : φ x := h x

elab "lpfx" : tactic =>
  withMainContext do
    let rd ← findDeclWithM isLineRun
    let sx ← initStateOfRun (← Meta.inferType rd.toExpr)
    let pd ← findDeclWithM (isPref sx)
    let sd ← findDeclWithM (λ dd => Meta.isDefEq dd.toExpr sx)
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    ctx.forM (clear_if rd.fvarId pd.fvarId sx)
    rd.fvarId.rvt
    pd.fvarId.rvt
    let g : Q(Prop) ← getMainTarget
    let m ← mkMotive g
    Expr.apply <| mkApp2 q(@apply_univ _root_.State) m sd.toExpr
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
  | leaf : Word → Func → DispatchTree
  | fork : DispatchTree → DispatchTree → DispatchTree

open DispatchTree

def DispatchTree.mem : DispatchTree → (Word × Func) → Prop
  | (leaf w p), wp => wp = (w, p)
  | (fork tl tr), wp => DispatchTree.mem tl wp ∨ DispatchTree.mem tr wp

instance : Membership (Word × Func) DispatchTree := ⟨DispatchTree.mem⟩

def leftmostFsig : DispatchTree → Word
  | (DispatchTree.leaf w _) => w
  | (DispatchTree.fork t _) => leftmostFsig t

-- given a dispatch tree of functions and their signatures, construct the main program.
-- note it assumes that:
-- (1) the calldata function selector is already at the op of the stack (i.e, it has to be preceded by 'fsig').
-- (2) the functions are ordered in ascending order of their signatures (right is higher)

def dispatch : DispatchTree → Func
  | DispatchTree.leaf w p => pushWord w ::: eq ::: (p <?> .rev)
  | DispatchTree.fork tl tr =>
    dup 0 :::
    pushWord (leftmostFsig tr) ::: gt :::
    (dispatch tl <?> dispatch tr)

lemma dispatch_inv (σ : Env → State → Prop) (ρ : Env → Result → Prop)
    (h0 : ∀ {e s x s'}, σ e s → Line.Run e s [pushWord x, eq, pop] s' → σ e s')
    (h1 : ∀ {e s x s'}, σ e s → Line.Run e s [dup 0, pushWord x, gt, pop] s' → σ e s') :
    ∀ t : DispatchTree,
      (∀ {e s r}, ∀ wp ∈ t, σ e s → Func.Run c e s wp.2 r → ρ e r) →
    ∀ (e s r), σ e s → Func.Run c e s (dispatch t) r → ρ e r := by
  intro t; induction t with
  | fork t t' ih ih' =>
    intro htt'
    have ht : ∀ {e s r}, ∀ wp ∈ t, σ e s → Func.Run c e s wp.2 r → ρ e r := by
      intro e s r wp h_in; apply htt' _ <| Or.inl h_in
    have ht' : ∀ {e s r}, ∀ wp ∈ t', σ e s → Func.Run c e s wp.2 r → ρ e r := by
      intro e s r wp h_in; apply htt' _ (Or.inr h_in)
    intro  e s r hs;
     pexen 3; intro h₂
    rcases of_run_branch' h₂ with ⟨_, h⟩ | ⟨_, h⟩ <;>
    (revert h; pexen 1; intro h₃)
    · apply ih' ht' e s₂ r (h1 hs <| run_append h₁ h₂) h₃
    · apply ih ht e s₂ r (h1 hs <| run_append h₁ h₂) h₃
  | leaf w p =>
    intro ht e s r hs; pexen 2; intro h₂
    rcases of_run_branch' h₂ with ⟨_, h⟩ | ⟨_, h⟩ <;>
    (revert h; pexen 1; intro h₃)
    · rcases h₃ with _ | _ | ⟨⟨_⟩⟩
    · apply ht ⟨w, p⟩ cst (h0 hs <| run_append h₁ h₂) h₃

def shiftRight (w : Word) : Line := [pushWord w, shr]

def fsig : Line := cdl 0 ++ shiftRight 224

def Func.main (dt : DispatchTree) : Func := fsig +++ dispatch dt

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
    (of_run_pushWord <| of_run_singleton h₁).stk
  rcases (of_run_singleton' h₂) with ⟨_, x, h_diff, _⟩
  rcases h_diff.stk with ⟨stk, h_pop, h_push'⟩
  have h_eq : s.stk = stk :=
    List.append_inj_right (Eq.trans h_push.symm h_pop) rfl
  rw [h_eq]; refine ⟨x, h_push'⟩

lemma State.push_of_cdl {e s w s'} (h : Line.Run e s (cdl w) s') :
    ∃ x, State.Push [x] s s' := by
  rcases Stack.push_of_cdl h with ⟨x, h'⟩
  refine' ⟨x, _, _, _, h', _, _, _⟩ <;>
  simp only [State.Rels.dft] <;>
  apply Line.of_inv _ _ asm <;> line_inv

lemma State.of_diff {xs ys} {s s''} (h : State.Diff xs ys s s'') :
    ∃ s', State.Pop xs s s' ∧ State.Push ys s' s'' := by
  rcases h.stk with ⟨stk, h_pop, h_push⟩
  refine' ⟨{s with stk := stk}, _, _⟩
  · refine ⟨rfl, rfl, rfl, h_pop, rfl, rfl, rfl⟩
  · cases h; refine' ⟨asm, asm, asm, h_push, asm, asm, asm⟩

lemma State.of_pop_cons {x xs} {s s''} (h : State.Pop (x :: xs) s s'') :
    ∃ s', State.Pop [x] s s' ∧ State.Pop xs s' s'' := by
  rcases List.of_cons_split h.stk with ⟨stk, h_eq, h_split⟩
  refine' ⟨{s with stk := stk}, _, _⟩
  · refine' ⟨rfl, rfl, rfl, h_eq, rfl, rfl, rfl⟩
  · cases h; refine' ⟨asm, asm, asm, h_split, asm, asm, asm⟩

lemma kec_elim {e s s'} (φ : Prop)
    (h : ∀ x, Line.Run e s [pop, pop, pushWord x] s' → φ)
    (h' : Inst.Run e s kec s') : φ := by
  rcases opRun_of_instRun h' with ⟨x, y, z, h_diff⟩; apply h z
  rcases State.of_diff h_diff with ⟨s₁, h_pop, h_push⟩
  rcases State.of_pop_cons h_pop with ⟨s₀, hx, hy⟩
  apply Line.Run.cons <| run_pop e hx
  apply Line.Run.cons <| run_pop e hy
  apply Line.Run.cons (run_pushWord e h_push) cst

lemma kec_cons_elim {e s l s'} (φ : Prop)
    (h : ∀ x, Line.Run e s (pop :: pop :: pushWord x :: l) s' → φ) :
    Line.Run e s (kec :: l) s' → φ := by
  lexen 1; apply kec_elim _ _ <| of_run_singleton h₁
  intro x h₂ h₃; apply h x <| run_append h₂ h₃

lemma kec_next_elim {e s p s'} (φ : Prop)
    (h : ∀ x, Func.Run c e s (pop ::: pop ::: pushWord x ::: p) s' → φ) :
    Func.Run c e s (kec ::: p) s' → φ := by
  pexen 1; apply kec_elim _ _ <| of_run_singleton h₁
  intro x h₂ h₃; apply h x <| run_prepend h₂ h₃

lemma prepend_kec_next_elim {e s} (l) {p r} (φ : Prop)
    (h : ∀ x, Func.Run c e s (l +++ pop ::: pop ::: pushWord x ::: p) r → φ) :
    Func.Run c e s (l +++ kec ::: p) r → φ := by
  pexec l; apply kec_next_elim
  intro x h'; apply h x <| run_prepend h₁ h'

lemma cdl_append_elim {e s n l r} (φ : Prop)
    (h : ∀ x, Line.Run e s (pushWord x :: l) r → φ) :
    Line.Run e s (cdl n ++ l) r → φ := by
  lexec (cdl n); intro h₂
  rcases State.push_of_cdl h₁ with ⟨x, hp₁⟩
  apply h x <| .cons (run_pushWord _ hp₁) h₂

lemma cdl_prepend_elim {c e s n p r} (φ : Prop)
    (h : ∀ x, Func.Run c e s (pushWord x ::: p) r → φ) :
    Func.Run c e s (cdl n +++ p) r → φ := by
  pexec (cdl n); intro h₂
  rcases State.push_of_cdl h₁ with ⟨x, hp₁⟩
  apply h x <| .next (run_pushWord _ hp₁) h₂

lemma sload_elim {e s s'} (φ : Prop)
    (h : ∀ x, Line.Run e s [pop, pushWord x] s' → φ)
    (h' : Inst.Run e s sload s') : φ := by
  rcases opRun_of_instRun h' with ⟨x, hx⟩
  rcases State.of_diff hx with ⟨s₀, h_pop, h_push⟩
  apply h (s.stor e.cta x);
  apply Line.Run.cons (run_pop e h_pop)
  apply Line.Run.cons (run_pushWord e h_push) cst

lemma sload_cons_elim {e s l s'} (φ : Prop)
    (h : ∀ x, Line.Run e s (pop :: pushWord x :: l) s' → φ) :
    Line.Run e s (sload :: l) s' → φ := by
  lexen 1; apply sload_elim _ _ <| of_run_singleton h₁
  intro x h₂ h₃; apply h x <| run_append h₂ h₃

lemma append_sload_cons_elim {e s} (a) {b s'} (φ : Prop)
    (h : ∀ x, Line.Run e s (a ++ pop :: pushWord x :: b) s' → φ) :
    Line.Run e s (a ++ sload :: b) s' → φ := by
  lexec a; apply sload_cons_elim
  intro x h'; apply h x <| run_append h₁ h'

lemma sload_next_elim {e s p r} (φ : Prop)
    (h : ∀ x, Func.Run c e s (pop ::: pushWord x ::: p) r → φ) :
    Func.Run c e s (sload ::: p) r → φ := by
  pexen 1; apply sload_elim _ _ <| of_run_singleton h₁
  intro x h₂ h₃; apply h x <| run_prepend h₂ h₃

lemma prepend_sload_next_elim {e s} (l) {p r} (φ : Prop)
    (h : ∀ x, Func.Run c e s (l +++ pop ::: pushWord x ::: p) r → φ) :
    Func.Run c e s (l +++ sload ::: p) r → φ := by
  pexec l; apply sload_next_elim
  intro x h'; apply h x <| run_prepend h₁ h'

lemma prepend_cdl_prepend_elim {e s} (l) {n p r} (φ : Prop)
    (h : ∀ x, Func.Run c e s (l +++ pushWord x ::: p) r → φ) :
    Func.Run c e s (l +++ cdl n +++ p) r → φ := by
  pexec l; pexec (cdl n); intro h₃
  rcases State.push_of_cdl h₂ with ⟨x, hp₂⟩
  apply h x <| run_prepend h₁ <| .next (run_pushWord _ hp₂) h₃

lemma of_nof_of_transfer {m n} {a b : Bits m} {v : Bits n} {f h : Bits m → Bits n}
    (h_nof : nof f) (h_di : Transfer f a v b h) :
    ∃ g, Decrease a v f g ∧ Increase b v g h ∧ NoOverflow (g b) v := by
  rcases h_di with ⟨h_le, g, hd, hi⟩; refine' ⟨g, hd, hi, _⟩
  apply lt_of_le_of_lt _ h_nof
  by_cases h_ab : a = b
  · rw [← (hd b).left h_ab, ← h_ab, Bits.sub_toNat _ _ h_le]
    rw [Nat.sub_add_cancel (Bits.toNat_le_toNat _ _ h_le)]
    exact le_sum
  · rw [← (hd b).right h_ab, Nat.add_comm]
    apply _root_.le_trans (Nat.add_le_add_right _ _) <| add_le_sum_of_ne f h_ab
    apply Bits.toNat_le_toNat _ _ h_le

lemma le_of_increase {m n : ℕ} {k : Bits m} {v : Bits n} {f g : Bits m → Bits n}
    (h : Increase k v f g) (h' : NoOverflow (f k) v) : ∀ k', f k' ≤ g k' := by
  intro k'; by_cases h_eq : k = k'
  · rw [← h_eq]
    have h_rw : f k + v = g k := (h k).left rfl
    rw [← h_rw]; apply Bits.le_add_right h'
  · rw [(h k').right h_eq]; apply Bits.le_refl
