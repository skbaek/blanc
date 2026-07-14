-- Common.lean : definitions and lemmas generally useful for writing and
-- verifying Blanc programs, including a correctness proof for the Blanc
-- compiler and tactics for automating Blanc program verification.

import Mathlib.Tactic.Have
import Mathlib.Tactic.Clear_
import Blanc.Semantics



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

inductive Line.Run : Sevm → Devm → Line → Devm → Prop
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
  (h_fa : Exec.Fa (Fortify π)) : Exec.Fa π := by
  intros pc sevm devm exn exc
  apply
    @Nat.strongRecOn
      (λ n => ∀ pc_ sevm_ devm_ exn_ (exc_ : Exec pc_ sevm_ devm_ exn_), n = sevm_.depth → π _ _ _ _ exc_)
      sevm.depth
  · intros n h pc_ sevm_ devm_ exn_ exc_ h_eq; apply h_fa
    intros pc' sevm' devm' exn' exc' h_lt; rw [← h_eq] at h_lt
    apply h sevm'.depth h_lt _ _ _ _ exc' rfl
  · rfl

def sumBelow (f : Adr → B256) : Nat → Nat
  | 0 => 0
  | n + 1 => sumBelow f n + (f n.toAdr).toNat

def sumBelow_succ {f : Adr → B256} {n} :
    sumBelow f (n + 1) = sumBelow f n + (f n.toAdr).toNat := by
  delta sumBelow; rfl

def sum (f : Adr → B256) : Nat :=
  sumBelow f Adr.max.toNat.succ

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
  cases cr
  case invOp eq =>
    simp only [Linst.At] at h_at
    rw [eq] at h_at; cases h_at
  case nextNoneErr nat _ =>
    simp only [Linst.At, Ninst.At] at h_at nat
    rw [nat] at h_at; cases h_at
  case nextSomeErr _ nat _ =>
    simp only [Linst.At, Ninst.At] at h_at nat
    rw [nat] at h_at; cases h_at
  case nextNoneRec nat _ _ =>
    simp only [Linst.At, Ninst.At] at h_at nat
    rw [nat] at h_at; cases h_at
  case nextSomeRec _ nat _ _ =>
    simp only [Linst.At, Ninst.At] at h_at nat
    rw [nat] at h_at; cases h_at
  case jumpErr jat _ =>
    simp only [Linst.At, Jinst.At] at h_at jat
    rw [jat] at h_at; cases h_at
  case jumpRec jat _ _ =>
    simp only [Linst.At, Jinst.At] at h_at jat
    rw [jat] at h_at; cases h_at
  case last lat run =>
    have eq := Linst.at_unique h_at lat
    rw [eq]; exact run

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
    {sevm_ : Sevm} {devm_ : Devm} {exn_ : Execution}
    {devm' : Devm}
    {devm'' : Devm}
    (nat : n.At sevm.code pc)
    ( run :
      Ninst.Run' pc sevm devm n
        (.some ⟨sevm_, devm_, exn_⟩)
        (.ok devm') )
    (exc_ : Exec 0 sevm_ devm_ exn_)
    (exc : Exec (pc + n.size) sevm devm' (.ok devm'')) :
    Exec'.Prec
      ⟨0, sevm_, devm_, exn_, exc_⟩
      ⟨pc, sevm, devm, .ok devm'', .nextSomeRec nat run exc_ exc⟩
  | snd {pc : Nat} {sevm : Sevm} {devm : Devm} {n : Ninst}
    {sevm_ : Sevm} {devm_ : Devm} {exn_ : Execution}
    {devm' : Devm} {devm'' : Devm}
    (nat : n.At sevm.code pc)
    ( run :
      Ninst.Run' pc sevm devm n
        (.some ⟨sevm_, devm_, exn_⟩)
        (.ok devm') )
    (exc_ : Exec 0 sevm_ devm_ exn_)
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
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _
    constructor; intro _ lt
    rcases lt with ⟨_, _, ⟨_⟩⟩
  · intro _ _ _ _ _ _ _ _ _ acc
    constructor; intro _ lt
    rcases lt with ⟨_, le, ⟨_⟩⟩
    exact acc_of_le le acc
  · intro pc sevm devm n sevm_ devm_ exn_ devm' exn nat run exc_ exc ih ih'
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
    {r : Rinst} {ex : Execution}
  (run : Ninst.Run' pc sevm devm (.reg r) .none ex) :
  (Rinst.run ⟨pc, sevm, devm⟩ r) = ex := run

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
  case nextSomeRec n sevm_ devm_ exn_ inter exc_ nat run exc =>
    have n_eq : n = .reg r := by
      injection Eq.trans nat.symm rat with eq; injection eq
    cases n_eq; revert run; simp [Ninst.Run']
  case jumpRec jat _ _ =>
    injection Eq.trans jat.symm rat with eq; injection eq
  case last _ lat _ =>
    injection Eq.trans lat.symm rat with eq; injection eq

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
    injection Eq.trans nat.symm nat' with eq; injection eq with rw
    cases rw
    refine' ⟨inter, exc, ⟨.none, trivial, pc, run⟩, Exec'.Prec.none nat' run exc⟩
  case nextSomeRec n' sevm_ devm_ exn_ inter exc_ nat' run exc =>
    injection Eq.trans nat.symm nat' with eq; injection eq with rw
    cases rw
    refine' ⟨inter, exc, ⟨.some ⟨sevm_, devm_, exn_⟩, ⟨exc_⟩, pc, run⟩, Exec'.Prec.snd nat' run exc_ exc⟩
  case jumpRec jat _ _ =>
    injection Eq.trans nat.symm jat with eq; injection eq
  case last _ lat _ =>
    injection Eq.trans nat.symm lat with eq; injection eq

lemma Ninst.size_eq_length_toB8L (n : Ninst) :
    n.size = n.toB8L.length := by cases n <;> rfl

lemma Except.bind_associative
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
  simp only [chargeGas_def] at h_charge
  split at h_charge
  · cases h_charge
  · rename_i gas h_safe
    injection h_charge with eq_d; subst eq_d
    unfold safeSub at h_safe
    split at h_safe
    · injection h_safe with eq_gas; subst eq_gas
      rw [Devm.push_def] at run
      simp only [Except.assert, bind, Except.bind] at run
      split at run; {cases run}
      injection run with eq_inter; subst eq_inter
      constructor <;> simp [_root_.Stack.Push, Split, Devm.Rels.eq]
    · contradiction

lemma Devm.pop_of_pop {x : B256} {devm devm' : Devm} :
    Devm.pop devm = .ok ⟨x, devm'⟩ → Devm.Pop [x] devm devm' := by
  intro pop
  simp only [Devm.pop_def] at pop
  split at pop; {cases pop}
  injection pop with eq; injection eq with eq eq'
  constructor <;> simp <;> rw [← eq'] <;> try {rfl}
  rename (devm.stack = _) => rw; rw [rw, eq]; rfl

lemma Devm.burn_of_chargeGas {cost : Nat} {devm devm' : Devm} :
    chargeGas cost devm = .ok devm' → Devm.Burn devm devm' := by
  intro eq
  simp only [chargeGas_def] at eq
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
  · exact Eq.trans pop.createdAccounts burn.createdAccounts
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

lemma of_jumpdest_run {pc sevm pre pc' inter}
    ( run :
      Jinst.Run
        {pc := pc, sta := sevm, dyna := pre}
        .jumpdest (.ok ⟨pc', inter⟩) ) :
    pc' = pc + 1 ∧ Devm.Burn pre inter := by
  rcases of_bind_eq_ok run with ⟨devm, eq_charge, eq_ok⟩
  injection eq_ok with eq
  injection eq with eq_pc eq_devm
  cases eq_pc; cases eq_devm
  refine' ⟨rfl, Devm.burn_of_chargeGas eq_charge⟩

lemma jumpdest_at {pc sevm pre post}
    (exc : Exec pc sevm pre (.ok post))
    (jat : Jinst.At sevm.code pc .jumpdest) :
    ∃ (inter : Devm) (exc' : Exec (pc + 1) sevm inter (.ok post)),
      Devm.Burn pre inter ∧
      ⟨pc + 1, sevm, inter, .ok post, exc'⟩ ≺
      ⟨pc, sevm, pre, .ok post, exc⟩ := by
  rcases Jinst.run_of_at exc jat with ⟨pc', inter, exc', run, prec⟩
  rcases of_jumpdest_run run with ⟨eq_pc, burn⟩
  cases eq_pc
  refine' ⟨inter, exc', burn, prec⟩

lemma of_jump_run {pc sevm pre pc' inter}
    ( run :
      Jinst.Run
        {pc := pc, sta := sevm, dyna := pre}
        .jump (.ok ⟨pc', inter⟩) ) :
    ∃ (x : B256),
      pc' = x.toNat ∧
      Devm.PopBurn [x] pre inter ∧
      jumpable sevm.code x.toNat = true := by
  rcases of_bind_eq_ok run with ⟨⟨x, devm1⟩, eq1, run⟩
  rcases of_bind_eq_ok run with ⟨devm2, eq2, run⟩
  rcases of_bind_eq_ok run with ⟨_, eq3, run⟩
  injection run with eq; injection eq with eq_pc eq_devm
  cases eq_pc; cases eq_devm
  refine' ⟨x, rfl, Devm.popBurn_of_pop_of_burn (Devm.pop_of_pop eq1) (Devm.burn_of_chargeGas eq2), Except.of_assert_eq_ok eq3⟩

lemma jump_at {pc sevm pre post}
    (exc : Exec pc sevm pre (.ok post))
    (jat : Jinst.At sevm.code pc .jump) :
    ∃ (x : B256) (inter : Devm) (exc' : Exec x.toNat sevm inter (.ok post)),
      Devm.PopBurn [x] pre inter ∧
      jumpable sevm.code x.toNat = true ∧
      ⟨x.toNat, sevm, inter, .ok post, exc'⟩ ≺
      ⟨pc, sevm, pre, .ok post, exc⟩ := by
  rcases Jinst.run_of_at exc jat with ⟨pc', inter, exc', run, prec⟩
  rcases of_jump_run run with ⟨x, eq_pc, pb, jp⟩
  cases eq_pc
  refine' ⟨x, inter, exc', pb, jp, prec⟩

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
  case nextSomeRec n sevm_ devm_ exn_ inter exc_ nat run exc =>
    injection Eq.trans nat.symm h_at with eq; injection eq with eq
    cases eq
    revert run; simp [Ninst.Run']
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
  rcases h with ⟨h_stack, h_mem, h_gas, h_logs, h_refund, h_out, h_del, h_ret, h_err, h_acc, h_keys, h_state, h_cas, h_trans⟩
  rcases h' with ⟨h'_stack, h'_mem, h'_gas, h'_logs, h'_refund, h'_out, h'_del, h'_ret, h'_err, h'_acc, h'_keys, h'_cas, h'_state, h'_trans⟩
  have push_pop_stack := Stack.push_cons_pop_cons h_stack h'_stack
  rcases push_pop_stack with ⟨h_eq, stk, h_push, h_pop⟩
  refine' ⟨
    h_eq,
    { s' with stack := stk },
    ⟨h_push, h_mem, h_gas, h_logs, h_refund, h_out, h_del, h_ret, h_err, h_acc, h_keys, h_state, h_cas, h_trans⟩,
    ⟨h_pop, h'_mem, h'_gas, h'_logs, h'_refund, h'_out, h'_del, h'_ret, h'_err, h'_acc, h'_keys, h'_cas, h'_state, h'_trans⟩
  ⟩

lemma Devm.burn_of_popBurn_nil {s s'} (h : Devm.PopBurn [] s s') :
    Devm.Burn s s' := by
  match s, s', h with
  | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩,
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩,
    ⟨h, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ =>
    refine' ⟨h, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ <;> assumption

lemma Devm.burn_of_pushBurn_nil {s s'} (h : Devm.PushBurn [] s s') :
    Devm.Burn s s' := by
  match s, s', h with
  | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩,
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩,
    ⟨h, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ =>
    refine' ⟨h.symm, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ <;> assumption

lemma Devm.burn_trans {x y z} (h1 : Devm.Burn x y) (h2 : Devm.Burn y z) : Devm.Burn x z := by
  rcases h1 with ⟨h1_stack, h1_mem, h1_gas, h1_logs, h1_refund, h1_out, h1_del, h1_ret, h1_err, h1_acc, h1_keys, h1_state, h1_cas, h1_trans⟩
  rcases h2 with ⟨h2_stack, h2_mem, h2_gas, h2_logs, h2_refund, h2_out, h2_del, h2_ret, h2_err, h2_acc, h2_keys, h2_state, h2_cas, h2_trans⟩
  refine' ⟨Eq.trans h1_stack h2_stack, Eq.trans h1_mem h2_mem, Nat.le_trans h2_gas h1_gas, Eq.trans h1_logs h2_logs, Eq.trans h1_refund h2_refund, Eq.trans h1_out h2_out, Eq.trans h1_del h2_del, Eq.trans h1_ret h2_ret, Eq.trans h1_err h2_err, Eq.trans h1_acc h2_acc, Eq.trans h1_keys h2_keys, Eq.trans h1_state h2_state, Eq.trans h1_cas h2_cas, Eq.trans h1_trans h2_trans⟩

lemma Devm.popBurn_of_burn_of_popBurn {devm devm' devm''} {xs}
    (burn : Devm.Burn devm devm')
    (popBurn : Devm.PopBurn xs devm' devm'') :
    Devm.PopBurn xs devm devm'' := by
  constructor
  · exact burn.stack ▸ popBurn.stack
  · exact Eq.trans burn.memory popBurn.memory
  · exact Nat.le_trans popBurn.gasLeft burn.gasLeft
  · exact Eq.trans burn.logs popBurn.logs
  · exact Eq.trans burn.refundCounter popBurn.refundCounter
  · exact Eq.trans burn.output popBurn.output
  · exact Eq.trans burn.accountsToDelete popBurn.accountsToDelete
  · exact Eq.trans burn.returnData popBurn.returnData
  · exact Eq.trans burn.error popBurn.error
  · exact Eq.trans burn.accessedAddresses popBurn.accessedAddresses
  · exact Eq.trans burn.accessedStorageKeys popBurn.accessedStorageKeys
  · exact Eq.trans burn.state popBurn.state
  · exact Eq.trans burn.createdAccounts popBurn.createdAccounts
  · exact Eq.trans burn.transientStorage popBurn.transientStorage

lemma Devm.popBurn_of_popBurn_of_pop {devm devm' devm''} {xs}
    (popBurn : Devm.PopBurn xs devm devm')
    (burn : Devm.Burn devm' devm'') :
    Devm.PopBurn xs devm devm'' := by
  constructor
  · exact burn.stack ▸ popBurn.stack
  · exact Eq.trans popBurn.memory burn.memory
  · exact Nat.le_trans burn.gasLeft popBurn.gasLeft
  · exact Eq.trans popBurn.logs burn.logs
  · exact Eq.trans popBurn.refundCounter burn.refundCounter
  · exact Eq.trans popBurn.output burn.output
  · exact Eq.trans popBurn.accountsToDelete burn.accountsToDelete
  · exact Eq.trans popBurn.returnData burn.returnData
  · exact Eq.trans popBurn.error burn.error
  · exact Eq.trans popBurn.accessedAddresses burn.accessedAddresses
  · exact Eq.trans popBurn.accessedStorageKeys burn.accessedStorageKeys
  · exact Eq.trans popBurn.state burn.state
  · exact Eq.trans popBurn.createdAccounts burn.createdAccounts
  · exact Eq.trans popBurn.transientStorage burn.transientStorage

lemma toNat_toB256 (n : Nat) : n.toB256.toNat = n ↾ 256 := by
  simp only [Nat.toB256, B256.toNat]; rw [toNat_toB128, toNat_toB128]
  apply Nat.or_eq_lo_add

lemma toNat_toB128_of_lt {n : Nat} (h : n < 2 ^ 128) : n.toB128.toNat = n := by
  rw [toNat_toB128, Nat.lo_eq_of_lt h]

lemma toNat_toB256_of_lt {n : Nat} (h : n < 2 ^ 256) : n.toB256.toNat = n := by
  rw [toNat_toB256, Nat.lo_eq_of_lt h]

lemma List.of_get?_succ_eq_some {X} {l : List X} {k : ℕ} {x} :
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
    | y :: l' =>
      intro h; simp at h
      rcases ih h with ⟨y', h'⟩
      exact ⟨y', h'⟩

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
    Jinst.jumpdest.At code loc ∧
    subcode code.toList (loc + 1) (Func.compile (table 0 (f :: fs)) (loc + 1) p) := by
  rcases of_get?_table_eq_some h_eq h_get with
    ⟨lft, rgt, _, _, pfx, sfx, h_pfx, h_split', h_sfx⟩
  rcases Table.compile_cons_eq_some h_sfx.symm with ⟨bs, bs', h_bs, _, h_sfx'⟩
  have h_slice : List.Slice code.toList loc sfx := by
    rw [← h_pfx, h_split']; apply List.append_slice_suffix
  rw [h_sfx', List.append_assoc] at h_slice
  constructor
  · apply Jinst.at_of_slice
    apply List.slice_prefix h_slice
  · rw [h_bs]; simp [subcode]
    apply List.slice_prefix <| List.slice_suffix h_slice

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
  have le : ([(loc >>> 8).toUInt8, loc.toUInt8] : B8L).length ≤ 32 := by simp [List.length]
  have h_push_slice : List.Slice code.toList m (Ninst.push [(loc >>> 8).toUInt8, loc.toUInt8] le).toB8L := by
    exact List.slice_prefix h_slice
  have h_jump_slice : List.Slice code.toList (m + 3) [Jinst.jump.toB8] := by
    have hh := @List.slice_suffix _ _ m [_, _, _] _ h_slice
    exact hh
  refine ⟨⟨le, Ninst.at_of_slice h_push_slice⟩, Jinst.at_of_slice h_jump_slice⟩

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
        ∃ (devm' : Devm) (exc' : Exec (pc + 3) sevm devm' (.ok post)),
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
        apply Devm.popBurn_of_burn_of_popBurn _ popBurn'
        apply Devm.burn_of_pushBurn_nil pushBurn'
      apply Func.Run.zero h_pop'
      have h_lt :
          Exec'.lt
            ⟨pc + 4, sevm, devm'', .ok post, exc''⟩
            ⟨pc, sevm, pre, .ok post, exc⟩ := by
        refine' ⟨_, _, h_prec⟩;
        apply Exec'.le.step _ prec
        apply Exec'.le.refl _
      apply ih ⟨pc + 4, sevm, devm'', .ok post, exc''⟩ h_lt p h_eq h_scp
    · clear h_scp
      have h_loc' : loc < 2 ^ 256 := by
        apply Nat.lt_trans h_loc
        rw [Nat.pow_lt_pow_iff_right] <;> omega
      have h : x.toNat = loc ∧ Devm.PopBurn [y] pre devm'' := by
        rcases Devm.pushBurn_cons_popBurn_cons pushBurn popBurn
          with ⟨hx, st, pushBurn', popBurn'⟩
        have h_loc_toNat : loc.toB256.toNat = loc := by
          rw [toNat_toB256, Nat.lo_eq_of_lt h_loc']
        rw [← congrArg B256.toNat hx, h_loc_toNat]
        refine ⟨rfl, Devm.popBurn_of_burn_of_popBurn (Devm.burn_of_pushBurn_nil pushBurn') popBurn'⟩
      rcases h with ⟨hx, popBurn'⟩
      rw [← hx] at h_jumpdest
      rcases jumpdest_at exc'' h_jumpdest with ⟨inter_jd, exc_jd, burn_jd, prec_jd⟩
      have run : Func.Run (f :: fs) sevm inter_jd q post := by
        have h_lt : Exec'.lt ⟨x.toNat + 1, sevm, inter_jd, .ok post, exc_jd⟩ ⟨pc, sevm, pre, .ok post, exc⟩ := by
          refine' ⟨_, _, h_prec⟩
          apply Exec'.le.step _ prec
          apply Exec'.le.step _ prec_jd
          apply Exec'.le.refl _
        rw [← hx] at h_scq
        apply ih ⟨x.toNat + 1, sevm, inter_jd, .ok post, exc_jd⟩ h_lt q h_eq h_scq
      apply Func.Run.succ ne popBurn' burn_jd run
  | .call k =>
    rcases subcode_compile_call sub with ⟨loc, p, h_get, h_loc, pushAt, h_jump⟩
    have h_get' : (f :: fs)[k]? = some p := by
      rw [← @Prog.get?_table 0 k (f :: fs), h_get]; rfl
    have hd :
      ∃ (devm' : Devm) (exc' : Exec (pc + 3) sevm devm' (.ok post)),
        Devm.PushBurn [loc.toB256] pre devm' ∧
        ⟨pc + 3, sevm, devm', .ok post, exc'⟩ ≺ ⟨pc, sevm, pre, .ok post, exc⟩ := by
      rcases push_of_pushAt exc pushAt with ⟨inter, exc', h, h_prec⟩
      rw [List.toB256_pair _ h_loc] at h
      refine' ⟨inter, exc', h, h_prec⟩
    rcases hd with ⟨devm', exc', h_push, h_prec⟩
    rcases jump_at exc' h_jump with ⟨x, devm'', exc'', h_pop, h_jumpable, h_prec'⟩
    rcases subcode_of_get?_eq_some h_eq h_get with ⟨h_jd, hp⟩; clear h_get
    have h_loc' : loc < 2 ^ 256 := by
      apply Nat.lt_trans h_loc
      rw [Nat.pow_lt_pow_iff_right] <;> omega
    have h_rw : loc = x.toNat ∧ Devm.Burn pre devm'' := by
      rcases Devm.pushBurn_cons_popBurn_cons h_push h_pop with ⟨hx, st, pushBurn', popBurn'⟩
      have h_loc_toNat : loc.toB256.toNat = loc := by
        rw [toNat_toB256_of_lt h_loc']
      rw [← congrArg B256.toNat hx, h_loc_toNat]
      have b1 := Devm.burn_of_pushBurn_nil pushBurn'
      have b2 := Devm.burn_of_popBurn_nil popBurn'
      refine ⟨rfl, Devm.burn_trans b1 b2⟩
    rcases h_rw with ⟨h_rw, h_burn⟩
    rw [h_rw] at h_jd
    rcases jumpdest_at exc'' h_jd with ⟨inter_jd, exc''', burn_jd, h_prec''⟩
    rw [h_rw] at hp
    have h_lt : Exec'.lt ⟨x.toNat + 1, sevm, inter_jd, .ok post, exc'''⟩ ⟨pc, sevm, pre, .ok post, exc⟩ := by
      refine' ⟨_, _, h_prec⟩
      apply Exec'.le.step _ h_prec'
      apply Exec'.le.step _ h_prec''
      apply Exec'.le.refl _
    have run : Func.Run (f :: fs) sevm inter_jd p post := by
      apply ih ⟨x.toNat + 1, sevm, inter_jd, .ok post, exc'''⟩ h_lt p h_eq hp
    exact Func.Run.call h_get' (Devm.burn_trans h_burn burn_jd) run

theorem correct (sevm : Sevm) (pre : Devm) (p : Prog) (post : Devm)
    (exc : Exec 0 sevm pre (.ok post))
    (eq : some sevm.code.toList = p.compile) :
    Prog.Run sevm pre p post := by
  rcases @subcode_of_get?_eq_some p.main p.aux sevm.code 0 _ p.main eq rfl
    with ⟨h_at, h_sub⟩
  rcases jumpdest_at exc h_at with ⟨inter, exc', burn, prec⟩;
  apply @Func.Run.call (p.main :: p.aux) sevm pre inter 0 p.main post rfl burn
  apply correct_core p.main p.aux ⟨1, sevm, inter, .ok post, exc'⟩ p.main eq h_sub

def Char.toB8 (c : Char) : B8 := Nat.toUInt8 c.toNat
def String.toB8L (s : String) : B8L := s.data.map Char.toB8
def String.keccak (s : String) : B256 := s.toB8L.keccak

def isMax : Line := [not, iszero]

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

section

open Lean.Elab.Tactic
open Lean.Parser.Tactic
open Lean.Elab.Term
open Lean
open Qq

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

lemma of_run_prepend {c e s r} :
   ∀ p q, Func.Run c e s (p +++ q) r →
   ∃ s', (Line.Run e s p s' ∧ Func.Run c e s' q r)
| [], _, h => ⟨s, cst, h⟩
| (_ :: p), q, (@Func.Run.next c e _ i _ _ _ h h') => by
  let ⟨s', hp, hq⟩ := of_run_prepend p q h'
  refine' ⟨s', Line.Run.cons h hp, hq⟩

lemma run_prepend_elim (φ : Prop) (l) {p} {c e} {s r}
    (h : ∀ s', Line.Run e s l s' → Func.Run c e s' p r → φ)
    (h' : Func.Run c e s (l +++ p) r) : φ := by
  rcases of_run_prepend _ _ h' with ⟨s', hs, hs'⟩; apply h s' hs hs'

lemma Line.of_run_cons {e s i l s''} (h : Line.Run e s (i :: l) s'') :
    ∃ s', i.Run e s s' ∧ Line.Run e s' l s'' := by cases h; refine' ⟨_, asm, asm⟩

lemma of_run_append  {e s} (a) {b s''} (h : Line.Run e s (a ++ b) s'') :
    ∃ s', a.Run e s s' ∧ b.Run e s' s'' := by
  induction a generalizing s with
  | nil => refine' ⟨s, cst, h⟩
  | cons i a ih =>
    rcases Line.of_run_cons h with ⟨s0, hi, h_ab⟩
    rcases ih h_ab with ⟨s1, ha, hb⟩
    refine ⟨s1, Line.Run.cons hi ha, hb⟩

lemma run_append_elim (φ : Prop) (l) {l'} {e} {s s''}
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

def Line.Inv {ξ : Type} (f : Devm → ξ) (l : Line) : Prop :=
  ∀ {e s s'}, l.Run e s s' → f s = f s'

lemma Line.of_inv {ξ : Type} {e s s'} (r : Devm → ξ) {l : Line} :
  Line.Inv r l → l.Run e s s' → r s = r s' := λ h => h

def Ninst.Inv {ξ : Type} (r : Devm → ξ) (i : Ninst) : Prop :=
  ∀ {e s s'}, Ninst.Run e s i s' → r s = r s'

lemma Line.nil_inv {ξ : Type} {f : Devm → ξ} : Line.Inv f [] := by
  intros e s s' h; cases h; rfl

lemma Line.cons_inv {ξ : Type} {f : Devm → ξ} {i l} :
    Ninst.Inv f i → Line.Inv f l → Line.Inv f (i :: l) := by
  intros h0 h1 e s s'' h2
  rcases Line.of_run_cons h2 with ⟨s', h3, h4⟩
  apply Eq.trans (h0 h3) (h1 h4)

class Ninst.Hinv {ξ : Type} (f : Devm → ξ) (i : Ninst) where (inv : Ninst.Inv f i)

def Ninst.inv_expr (ξx fx : Lean.Expr) (ix : Q(Ninst)) : Lean.Elab.Tactic.TacticM Lean.Expr := do
  let x ← Lean.Meta.synthInstance <| Lean.mkApp3 q(@Ninst.Hinv) ξx fx ix
  pure <| Lean.mkApp4 q(@Ninst.Hinv.inv) ξx fx ix x

def instInv : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
  let t ← Lean.Elab.Tactic.getMainTarget
  have t' : Q(Prop) := t
  match t' with
  | ~q(@Ninst.Inv $ξx $fx $ix) =>
    let x ← Ninst.inv_expr ξx fx ix
    Lean.Elab.Tactic.closeMainGoal `tacName x
  | _ => dbg_trace "Not a Ninst.Inv goal"

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


def Strings.toName : List String → Lean.Name
  | [] => Lean.Name.anonymous
  | s :: ss => Lean.Name.str (Strings.toName ss) s

def Strings.toExpr (l : List String) : Lean.Expr :=
  Lean.Expr.const (Strings.toName l.reverse) []

def String.toExpr (s : String) : Lean.Expr :=
  Strings.toExpr <| String.splitOn s "."

def String.apply (s : String): Lean.Elab.Tactic.TacticM Unit :=
  Lean.Expr.apply <| String.toExpr s

def Func.Inv {ξ : Type} (f : Devm → ξ) (g : Devm → ξ) (p : Func) : Prop :=
  ∀ {c sevm s r}, Func.Run c sevm s p r → f s = g r

def Linst.Inv {ξ : Type} (f : Devm → ξ) (g : Devm → ξ) (o : Linst) : Prop :=
  ∀ {e s r}, Linst.Run e s o (.ok r) → f s = g r

class Linst.Hinv {ξ : Type} (f : Devm → ξ) (g : Devm → ξ) (o : Linst) where (inv : Linst.Inv f g o)

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

lemma Devm.Burn.getBal {s s' : Devm} (h : Devm.Burn s s') (a : Adr) : s'.getBal a = s.getBal a := by
  simp [Devm.getBal, Devm.getAcct]; rw [h.state]

lemma Devm.PopBurn.getBal {xs} {s s' : Devm} (h : Devm.PopBurn xs s s') (a : Adr) : s'.getBal a = s.getBal a := by
  simp [Devm.getBal, Devm.getAcct]; rw [h.state]

lemma Func.of_inv {ξ : Type} {e s r} (f g) {p : Func} :
  @Func.Inv ξ f g p → Func.Run c e s p r → f s = g r := λ h => h

lemma last_inv {ξ} {f g o} (h : Linst.Inv f g o) :
    @Func.Inv ξ f g (Func.last o) := by
  intros c e s r h'; cases h'; rename_i hl
  apply h hl

lemma prepend_inv {ξ : Type} {f g} {l p} (hl : Line.Inv f l)
    (hp : Func.Inv f g p) : @Func.Inv ξ f g (l +++ p) := by
  intros c e s r h; rcases of_run_prepend _ _ h with ⟨s', hl', hp'⟩
  apply Eq.trans (hl hl') (hp hp')

lemma of_run_branch {c e s r} {p q : Func} (h : Func.Run c e s (Func.branch p q) r) :
    (∃ s', Devm.PopBurn [0] s s' ∧ Func.Run c e s' p r) ∨
    (∃ w s' s'', w ≠ 0 ∧ Devm.PopBurn [w] s s' ∧ Devm.Burn s' s'' ∧ Func.Run c e s'' q r) := by
  cases h with
  | zero h1 h2 => left; exact ⟨_, h1, h2⟩
  | succ h1 h2 h3 h4 => right; exact ⟨_, _, _, h1, h2, h3, h4⟩

class PopBurn.Inv {ξ} (f : Devm → ξ) : Prop where
  (inv : ∀ {xs s s'}, Devm.PopBurn xs s s' → f s = f s')

class Burn.Inv {ξ} (f : Devm → ξ) : Prop where
  (inv : ∀ {s s'}, Devm.Burn s s' → f s = f s')

instance : PopBurn.Inv Devm.getBal := ⟨by
  intros xs s s' h
  funext a
  exact (Devm.PopBurn.getBal h a).symm
⟩

instance : Burn.Inv Devm.getBal := ⟨by
  intros s s' h
  funext a
  exact (Devm.Burn.getBal h a).symm
⟩

lemma branch_inv {ξ : Type} {f : Devm → ξ} {g} {p q}
    [h_pop : PopBurn.Inv f] [h_burn : Burn.Inv f]
    (hp : Func.Inv f g p) (hq : Func.Inv f g q) :
    @Func.Inv ξ f g (Func.branch p q) := by
  intros c e s r h_run
  rcases of_run_branch h_run with ⟨s', h_pb, h_run⟩ | ⟨w, s', s'', h_ne, h_pb, h_b, h_run⟩
  · rw [h_pop.inv h_pb]
    exact hp h_run
  · rw [h_pop.inv h_pb]
    rw [h_burn.inv h_b]
    exact hq h_run

lemma next_inv {ξ : Type} {f : Devm → ξ} {g} {i p}
    (h : Ninst.Inv f i) (h' : Func.Inv f g p) : Func.Inv f g (i ::: p) := by
  intros c e s r h_run
  cases h_run; rename_i hi hp
  rw [h hi, h' hp]

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
        | ~q(Func.branch _ _) => "branch_inv".apply; prog_inv; prog_inv
        | _ => do
          let pp ← Lean.Meta.ppExpr px'
          Lean.logInfo s!"not matching: {pp}"
    | _ => dbg_trace "not a Func.Inv goal"

elab "prog_inv" : tactic => prog_inv

end

lemma not_run_rev {c e s r} : ¬ Func.Run c e s Func.rev r := by
  intro h
  cases h with
  | last h_run =>
    simp only [Linst.Run, Linst.run] at h_run
    rcases of_bind_eq_ok h_run with ⟨v1, h1, h2⟩
    rcases of_bind_eq_ok h2 with ⟨v2, h3, h4⟩
    rcases of_bind_eq_ok h4 with ⟨v3, h5, h6⟩
    contradiction

lemma of_run_branch_rev {c e s r} {p : Func} (h : Func.Run c e s (.rev <?> p) r) :
    ∃ s', Devm.PopBurn [0] s s' ∧ Func.Run c e s' p r := by
  rcases of_run_branch h with ⟨s', h_pb, h_run⟩ | ⟨w, s', s'', h_ne, h_pb, h_b, h_run⟩
  · exact ⟨s', h_pb, h_run⟩
  · exfalso; exact not_run_rev h_run

lemma dispatchWith_inv {c k f}
    (σ : Sevm → Devm → Prop)
    (ρ : Sevm → Devm → Prop)
    ( h0 :
      ∀ {e s x w s' s''},
        σ e s →
        Line.Run e s [pushB256 x, eq] s' →
        Devm.PopBurn [w] s' s'' →
        σ e s'' )
    ( h1 :
      ∀ {e s x w s' s''},
        σ e s →
        Line.Run e s [dup 0, pushB256 x, gt] s' →
        Devm.PopBurn [w] s' s'' →
        σ e s'' )
    (h2 : c[k]? = some f)
    (h3 : ∀ {e s s' r}, σ e s → Devm.Burn s s' → Func.Run c e s' f r → ρ e r) :
    ∀ t : DispatchTree,
      (∀ {e s r}, ∀ wf ∈ t, σ e s → Func.Run c e s wf.2 r → ρ e r) →
    ∀ (e s r), σ e s → Func.Run c e s (dispatchWith k t) r → ρ e r := by
  intro t
  induction t with
  | fork t t' ih ih' =>
    intro htt' e s r hs
    have ht : ∀ {e s r}, ∀ wp ∈ t, σ e s → Func.Run c e s wp.2 r → ρ e r := by
      intro e s r wp h_in; apply htt' _ (Or.inl h_in)
    have ht' : ∀ {e s r}, ∀ wp ∈ t', σ e s → Func.Run c e s wp.2 r → ρ e r := by
      intro e s r wp h_in; apply htt' _ (Or.inr h_in)
    pexen 3; intro h₂
    rcases of_run_branch h₂ with ⟨s₂, h_pop, h_run'⟩ | ⟨w, s₂, s₃, hw, h_pop, h_burn, h_run'⟩
    · apply ih' ht' e s₂ r (h1 hs h₁ h_pop) h_run'
    · apply ih ht e s₃ r (h1 hs h₁ (Devm.popBurn_of_popBurn_of_pop h_pop h_burn)) h_run'
  | leaf w p =>
    intro htt' e s r hs
    pexen 2; intro h'
    rcases of_run_branch h' with ⟨s₂, h_pop, h_run'⟩ | ⟨w', s₂, s₃, hw', h_pop, h_burn, h_run'⟩
    · cases h_run' with
      | call h_eq_f h_burn' h_run_f =>
        have hh := Eq.trans h2.symm h_eq_f
        injection hh with heq
        subst heq
        apply h3 (h0 hs h₁ h_pop) h_burn' h_run_f
    · apply htt' ⟨w, p⟩ rfl (h0 hs h₁ (Devm.popBurn_of_popBurn_of_pop h_pop h_burn)) h_run'

def shiftRight (w : B256) : Line := [pushB256 w, shr]

def fsig : Line := cdl 0 ++ shiftRight 224

def Func.main (dt : DispatchTree) : Func := fsig +++ dispatch dt
def Func.mainWith (k : Nat) (dt : DispatchTree) : Func := fsig +++ dispatchWith k dt

def ifOk {ε α} (π : α → Prop) : Except ε α → Prop
  | .error _ => True
  | .ok a => π a

def Prog.At (p : Prog) (ca : Adr)
    (pc : Nat) (sevm : Sevm) (devm : Devm) : Prop :=
  some (devm.getCode ca).toList = Prog.compile p ∧
  (sevm.currentTarget = ca → (some sevm.code.toList = Prog.compile p ∧ pc = 0))

def ForallSubExec (k : Nat) (ca : Adr) (p : Prog)
    (R : Sevm → Devm → Devm → Prop) : Prop :=
  ∀ pc sevm devm post,
    Exec pc sevm devm (.ok post) →
    sevm.depth < k →
    p.At ca pc sevm devm →
    R sevm devm post

def Exec.Wkn (ca : Adr) (p : Prog)
    (π : Exec.Pred)
    (pc sevm devm exn) (ex : Exec pc sevm devm exn) : Prop :=
  p.At ca pc sevm devm → π pc sevm devm exn ex

def ForallDeeper (k : Nat) (ε : Exec.Pred) : Prop :=
  ∀ pc sevm devm exn (ex : Exec pc sevm devm exn), sevm.depth < k → ε pc sevm devm exn ex

def ForallDeeperAt (k : Nat) (ca : Adr) (p : Prog) (ε : Exec.Pred) : Prop :=
  ForallDeeper k (fun pc sevm devm exn ex => p.At ca pc sevm devm → ε pc sevm devm exn ex)

lemma State.setBal_getCode (st : State) (adr a : Adr) (val : B256) :
  (st.setBal adr val).getCode a = st.getCode a := by
  dsimp [State.setBal, State.set, State.getCode, State.get]
  split_ifs with h_if
  · by_cases h : compare adr a = Ordering.eq
    · have h2 : adr = a := compare_eq_iff_eq.mp h
      subst h2
      rw [Std.TreeMap.getD_erase]
      split_ifs; try rfl
      · have h3 := congrArg Acct.code h_if
        exact h3.symm
    · rw [Std.TreeMap.getD_erase]
      simp [h]
  · by_cases h : compare adr a = Ordering.eq
    · have h2 : adr = a := compare_eq_iff_eq.mp h
      subst h2
      rw [Std.TreeMap.getD_insert]
      dsimp [Acct.withBal]
      simp
    · rw [Std.TreeMap.getD_insert]
      simp [h]

lemma State.addBal_getCode (st : State) (adr a : Adr) (val : B256) :
  (st.addBal adr val).getCode a = st.getCode a := by
  dsimp [State.addBal]
  exact State.setBal_getCode st adr a (st.bal adr + val)

lemma State.subBal_getCode {st st' : State} {adr a : Adr} {val : B256} (h : st.subBal adr val = some st') :
  st'.getCode a = st.getCode a := by
  dsimp [State.subBal] at h
  split at h
  · contradiction
  · injection h with h2
    subst h2
    exact State.setBal_getCode st adr a (st.bal adr - val)

lemma Benv.addBal_getCode (benv : Benv) (adr a : Adr) (val : B256) :
  (benv.addBal adr val).state.getCode a = benv.state.getCode a := by
  dsimp [Benv.addBal, Benv.withState]
  exact State.addBal_getCode benv.state adr a val

lemma Benv.subBal_getCode {benv benv' : Benv} {adr a : Adr} {val : B256} (h : benv.subBal adr val = some benv') :
  benv'.state.getCode a = benv.state.getCode a := by
  dsimp [Benv.subBal, Option.bind] at h
  split at h
  · contradiction
  · rename_i st' h_sub
    injection h with h2
    subst h2
    dsimp [Benv.withState]
    exact State.subBal_getCode h_sub

/-! The pure footprint theorem is kept before the early code-frame lemmas that
use it.  The outcome-aware variants are developed with `CEffect` below. -/

def Devm.WorldEq (d d' : Devm) : Prop :=
  d.state = d'.state ∧ d.transientStorage = d'.transientStorage

lemma Devm.worldEq_trans : Transitive Devm.WorldEq := by
  rintro d d' d'' ⟨hstate, htransient⟩ ⟨hstate', htransient'⟩
  exact ⟨hstate.trans hstate', htransient.trans htransient'⟩

lemma Devm.worldEq_setMach (d : Devm) (mach : Mach) :
    Devm.WorldEq d (d.setMach mach) := by
  exact ⟨rfl, rfl⟩

lemma liftMachPure_worldEq (core : Mach → Mach) (d : Devm) :
    Devm.WorldEq d (liftMachPure core d) := by
  exact Devm.worldEq_setMach d _

lemma Devm.worldEq_setMachMeta (d : Devm) (view : Mach × Meta) :
    Devm.WorldEq d (d.setMachMeta view) := by
  exact ⟨rfl, rfl⟩

lemma liftMachMetaPure_worldEq
    (core : Mach → Meta → Mach × Meta) (d : Devm) :
    Devm.WorldEq d (liftMachMetaPure core d) := by
  exact Devm.worldEq_setMachMeta d _

lemma addAccessedAddress_worldEq (d : Devm) (a : Adr) :
    Devm.WorldEq d (addAccessedAddress d a) := by
  exact liftMachMetaPure_worldEq _ _

lemma addAccessedStorageKey_worldEq (d : Devm) (a : Adr) (k : B256) :
    Devm.WorldEq d (addAccessedStorageKey d a k) := by
  exact liftMachMetaPure_worldEq _ _

lemma liftMach_worldEq_of_ok {core : Mach → Footprint.Outcome Mach α}
    {d d' : Devm} {x : α} (h : liftMach core d = .ok (x, d')) :
    Devm.WorldEq d d' := by
  unfold liftMach Footprint.liftOutcome at h
  cases hc : core d.mach with
  | error err => simp [hc] at h
  | ok out =>
    simp [hc] at h
    rcases h with ⟨_, rfl⟩
    exact Devm.worldEq_setMach d out.2

lemma liftMach_worldEq_of_error {core : Mach → Footprint.Outcome Mach α}
    {d : Devm} {err : String × Devm} (h : liftMach core d = .error err) :
    Devm.WorldEq d err.2 := by
  unfold liftMach Footprint.liftOutcome at h
  cases hc : core d.mach with
  | error out =>
    simp [hc] at h
    rcases h with ⟨_, rfl⟩
    exact Devm.worldEq_setMach d out.2
  | ok out => simp [hc] at h

lemma liftMachExecution_worldEq_of_ok {core : Mach → Footprint.Outcome Mach Unit}
    {d d' : Devm} (h : liftMachExecution core d = .ok d') :
    Devm.WorldEq d d' := by
  unfold liftMachExecution Footprint.toExecution at h
  split at h
  · cases h
  · rename_i out heq
    cases h
    exact liftMach_worldEq_of_ok heq

lemma liftMachExecution_worldEq_of_error {core : Mach → Footprint.Outcome Mach Unit}
    {d : Devm} {err : String × Devm} (h : liftMachExecution core d = .error err) :
    Devm.WorldEq d err.2 := by
  unfold liftMachExecution Footprint.toExecution at h
  split at h
  · rename_i e heq
    cases h
    exact liftMach_worldEq_of_error heq
  · cases h

lemma chargeGas_worldEq_of_ok {cost : Nat} {d d' : Devm}
    (h : chargeGas cost d = .ok d') : Devm.WorldEq d d' := by
  exact liftMachExecution_worldEq_of_ok (core := Mach.chargeGas cost) h

lemma chargeGas_worldEq_of_error {cost : Nat} {d : Devm} {err : String × Devm}
    (h : chargeGas cost d = .error err) : Devm.WorldEq d err.2 := by
  exact liftMachExecution_worldEq_of_error (core := Mach.chargeGas cost) h

lemma Devm.WorldEq.getCode {d d' : Devm} (h : Devm.WorldEq d d') (a : Adr) :
    d.getCode a = d'.getCode a := by
  unfold Devm.getCode Devm.getAcct
  rw [h.1]

lemma Devm.WorldEq.getBal {d d' : Devm} (h : Devm.WorldEq d d') (a : Adr) :
    d.getBal a = d'.getBal a := by
  unfold Devm.getBal Devm.getAcct
  rw [h.1]

lemma addAccessedAddress_getCode {devm : Devm} {adr a : Adr} :
    (addAccessedAddress devm adr).getCode a = devm.getCode a := by
  exact (addAccessedAddress_worldEq devm adr).getCode a |>.symm

lemma accessDelegation_getCode {devm : Devm} {adr a : Adr} :
    (accessDelegation devm adr).2.2.2.2.getCode a = devm.getCode a := by
  dsimp [accessDelegation]
  split_ifs
  · exact addAccessedAddress_getCode
  · rfl

lemma chargeGas_getCode {devm devm' : Devm} {cost : ℕ} {a : Adr}
    (h : chargeGas cost devm = Except.ok devm') :
    devm'.getCode a = devm.getCode a := by
  exact (chargeGas_worldEq_of_ok h).getCode a |>.symm

lemma Devm.pop_worldEq_of_ok {devm devm' : Devm} {x : B256}
    (h : devm.pop = .ok (x, devm')) : Devm.WorldEq devm devm' := by
  exact liftMach_worldEq_of_ok (core := Mach.pop) h

lemma Devm.pop_worldEq_of_error {devm : Devm} {err : String × Devm}
    (h : devm.pop = .error err) : Devm.WorldEq devm err.2 := by
  exact liftMach_worldEq_of_error (core := Mach.pop) h

lemma Devm.pop_getCode {devm devm' : Devm} {val : B256} {a : Adr}
    (h : devm.pop = Except.ok (val, devm')) : devm'.getCode a = devm.getCode a := by
  exact (Devm.pop_worldEq_of_ok h).getCode a |>.symm

lemma Devm.popToNat_worldEq_of_ok {devm devm' : Devm} {n : Nat}
    (h : devm.popToNat = .ok (n, devm')) : Devm.WorldEq devm devm' := by
  exact liftMach_worldEq_of_ok (core := Mach.popToNat) h

lemma Devm.popToNat_worldEq_of_error {devm : Devm} {err : String × Devm}
    (h : devm.popToNat = .error err) : Devm.WorldEq devm err.2 := by
  exact liftMach_worldEq_of_error (core := Mach.popToNat) h

lemma Devm.popToNat_getCode {devm devm' : Devm} {val : ℕ} {a : Adr}
    (h : devm.popToNat = Except.ok (val, devm')) :
    devm'.getCode a = devm.getCode a := by
  exact (Devm.popToNat_worldEq_of_ok h).getCode a |>.symm

lemma Devm.popToAdr_getCode {devm devm' : Devm} {val : Adr} {a : Adr}
    (h : devm.popToAdr = Except.ok (val, devm')) :
    devm'.getCode a = devm.getCode a := by
  exact (liftMach_worldEq_of_ok (core := Mach.popToAdr) h).getCode a |>.symm

lemma Devm.memExtends_getCode {devm : Devm} {ranges : List (ℕ × ℕ)} {a : Adr} :
    (devm.memExtends ranges).getCode a = devm.getCode a := by
  exact (liftMachPure_worldEq (Mach.memExtends · ranges) devm).getCode a |>.symm

lemma Devm.incrNonce_getCode {devm : Devm} {adr a : Adr} : (devm.incrNonce adr).getCode a = devm.getCode a := by
  dsimp [Devm.incrNonce, Devm.getCode, Devm.getAcct, State.incrNonce, State.set, State.getCode, State.get]
  split_ifs with h_if
  · by_cases h : compare adr a = Ordering.eq
    · have h2 : adr = a := compare_eq_iff_eq.mp h
      subst h2
      rw [Std.TreeMap.getD_erase]
      split_ifs; try rfl
      · have h3 := congrArg Acct.code h_if
        exact h3.symm
    · rw [Std.TreeMap.getD_erase]
      simp [h]
  · by_cases h : compare adr a = Ordering.eq
    · have h2 : adr = a := compare_eq_iff_eq.mp h
      subst h2
      rw [Std.TreeMap.getD_insert]
      simp
    · rw [Std.TreeMap.getD_insert]
      simp [h]

lemma addCreatedAccount_getCode {benv : Benv} {adr a : Adr} : (addCreatedAccount benv adr).state.getCode a = benv.state.getCode a := by
  rfl

lemma Benv.setStor_getCode {benv : Benv} {adr a : Adr} {stor : Stor} : (benv.setStor adr stor).state.getCode a = benv.state.getCode a := by
  dsimp [Benv.setStor, Benv.state, State.setStor, State.set, State.getCode, State.get]
  split_ifs with h_if
  · by_cases h : compare adr a = Ordering.eq
    · have h2 : adr = a := compare_eq_iff_eq.mp h
      subst h2
      rw [Std.TreeMap.getD_erase]
      split_ifs; try rfl
      · have h3 := congrArg Acct.code h_if
        exact h3.symm
    · rw [Std.TreeMap.getD_erase]
      simp [h]
  · by_cases h : compare adr a = Ordering.eq
    · have h2 : adr = a := compare_eq_iff_eq.mp h
      subst h2
      rw [Std.TreeMap.getD_insert]
      simp
    · rw [Std.TreeMap.getD_insert]
      simp [h]

lemma Benv.incrNonce_getCode {benv : Benv} {adr a : Adr} : (benv.incrNonce adr).state.getCode a = benv.state.getCode a := by
  dsimp [Benv.incrNonce, Benv.state, State.incrNonce, State.set, State.getCode, State.get]
  split_ifs with h_if
  · by_cases h : compare adr a = Ordering.eq
    · have h2 : adr = a := compare_eq_iff_eq.mp h
      subst h2
      rw [Std.TreeMap.getD_erase]
      split_ifs; try rfl
      · have h3 := congrArg Acct.code h_if
        exact h3.symm
    · rw [Std.TreeMap.getD_erase]
      simp [h]
  · by_cases h : compare adr a = Ordering.eq
    · have h2 : adr = a := compare_eq_iff_eq.mp h
      subst h2
      rw [Std.TreeMap.getD_insert]
      simp
    · rw [Std.TreeMap.getD_insert]
      simp [h]

/-! The call/create preparation path is not a world frame: child dispatch may
transfer value, and create dispatch may increment nonces or install code.  It
does, however, preserve the code map at the suspended parent boundary. -/

def Devm.CodeFrame (before after : Devm) : Prop :=
  ∀ a : Adr, after.getCode a = before.getCode a

lemma Xinst.prep_codeFrame
    {sevm : Sevm}
    {devm : Devm}
    {sevm_ : Sevm}
    {devm_ : Devm}
    {exn_ res : Execution}
    {x : Xinst}
    (run : Xinst.Run sevm devm x (some (sevm_, devm_, exn_)) res) :
    Devm.CodeFrame devm devm_ := by
  intro adr
  cases x
  case create =>
    dsimp [Xinst.Run] at run
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨endowment, devm1⟩, eq1, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨memoryIndex, devm2⟩, eq2, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨memorySize, devm3⟩, eq3, run⟩; contradiction
    rcases run with ⟨extendCost, hp4, run⟩
    rcases run with ⟨initCodeCost, hp5, run⟩
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨devm4, eq6, run⟩; contradiction
    rcases run with ⟨devm5, hp7, run⟩
    rcases run with ⟨newAddress, hp8, run⟩
    dsimp [GenericCreate] at run
    rcases run with ⟨calldata, hp9, run⟩
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, _, run⟩; contradiction
    rcases run with ⟨devm6, hp10, run⟩
    rcases run with ⟨createMsgGas, hp11, run⟩
    rcases run with ⟨devm7, hp12, run⟩
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, _, run⟩; contradiction
    rcases run with ⟨devm8, hp13, run⟩
    rcases run with ⟨sender, hp14, run⟩
    split_ifs at run with h_sender
    · rcases run with ⟨h_xl, h_ex⟩
      cases h_xl
    · rcases run with ⟨devm9, hp15, run⟩
      split_ifs at run with h_target
      · rcases run with ⟨h_xl, h_ex⟩
        cases h_xl
      · rcases run with ⟨childMsg, hp16, run⟩
        rcases run with ⟨ex', run, _⟩
        dsimp [ProcessCreateMessage] at run
        rcases run with ⟨ex'', run, _⟩
        dsimp [ProcessMessage] at run
        rcases run with ⟨_, _, _, h_contra⟩ | ⟨benv, eq_benv, run⟩; contradiction
        rcases run with ⟨ex''', run, _⟩
        dsimp [ExecuteCode] at run
        dsimp [initEvm] at run
        have h_devm : benv.state.getCode adr = devm.getCode adr := by
          rw [hp16] at eq_benv
          dsimp [processCreateMessage.msg, Msg.benvAfterTransfer, Msg.withBenv, Msg.shouldTransferValue] at eq_benv
          set benv_init := (addCreatedAccount (({ state := devm9.state, createdAccounts := devm9.createdAccounts, stat := sevm.benvStat } : Benv).setStor newAddress Stor.empty) newAddress).incrNonce newAddress
          rcases hp_sub : benv_init.subBal sevm.currentTarget endowment with _ | benv_sub
          · rw [hp_sub] at eq_benv
            simp [Option.toExcept, Bind.bind, Except.bind] at eq_benv
          · rw [hp_sub] at eq_benv
            simp [Option.toExcept, Bind.bind, Except.bind] at eq_benv
            subst eq_benv
            have h1 := Benv.addBal_getCode (a := adr) benv_sub newAddress endowment
            have h2 := Benv.subBal_getCode (a := adr) hp_sub
            have h_benv_init : benv_init.state.getCode adr = devm9.getCode adr := by
              dsimp [benv_init]
              rw [Benv.incrNonce_getCode, addCreatedAccount_getCode, Benv.setStor_getCode]
              rfl
            rw [h_benv_init] at h2
            rw [h1, h2]
            have h15 : devm9.getCode adr = devm8.getCode adr := by subst hp15; exact Devm.incrNonce_getCode
            have h13 : devm8.getCode adr = devm7.getCode adr := by subst hp13; rfl
            have h12 : devm7.getCode adr = devm6.getCode adr := by subst hp12; rfl
            have h10 : devm6.getCode adr = devm5.getCode adr := by subst hp10; exact addAccessedAddress_getCode
            have h7 : devm5.getCode adr = devm4.getCode adr := by subst hp7; exact Devm.memExtends_getCode
            have h6 : devm4.getCode adr = devm3.getCode adr := chargeGas_getCode eq6
            have h3 : devm3.getCode adr = devm2.getCode adr := Devm.popToNat_getCode eq3
            have h2' : devm2.getCode adr = devm1.getCode adr := Devm.popToNat_getCode eq2
            have h1' : devm1.getCode adr = devm.getCode adr := Devm.pop_getCode eq1
            rw [h15, h13, h12, h10, h7, h6, h3, h2', h1']
        rw [hp16] at run
        dsimp [processCreateMessage.msg, Msg.withBenv] at run
        rcases run with ⟨ex'''', h_xl, _⟩
        injection h_xl with h_xl_eq
        injection h_xl_eq with _ h_devm_eq
        injection h_devm_eq with h_devm_eq _
        subst h_devm_eq
        exact h_devm
  case call =>
    dsimp [Xinst.Run] at run
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨gas, devm1⟩, eq1, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨callee, devm2⟩, eq2, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨value, devm3⟩, eq3, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨inputIndex, devm4⟩, eq4, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨inputSize, devm5⟩, eq5, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨outputIndex, devm6⟩, eq6, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨outputSize, devm7⟩, eq7, run⟩; contradiction
    rcases run with ⟨extendCost, hp8, run⟩
    rcases run with ⟨preAccessCost, hp9, run⟩
    rcases run with ⟨devm8, hp10, run⟩
    rcases run with ⟨⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm9⟩, hp11, run⟩
    rcases run with ⟨accessCost, hp12, run⟩
    rcases run with ⟨createCost, hp13, run⟩
    rcases run with ⟨transferCost, hp14, run⟩
    rcases run with ⟨⟨msgCallCost, msgCallStipend⟩, hp15, run⟩
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨devm10, eq16, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, _, run⟩; contradiction
    rcases run with ⟨devm11, hp18, run⟩
    rcases run with ⟨senderBal, hp19, run⟩
    split_ifs at run with h_bal
    · rcases run with ⟨_, _, _, h_contra⟩ | ⟨devm12, eq20, run⟩; contradiction
      rcases run with ⟨h_xl, h_ex⟩
      cases h_xl
    · dsimp [GenericCall] at run
      rcases run with ⟨evm1, hp_evm1, run⟩
      split_ifs at run with h_depth
      · rcases run with ⟨h_xl, _⟩; contradiction
      · rcases run with ⟨calldata, _, run⟩
        rcases run with ⟨childMsg, hp_childMsg, run⟩
        rcases run with ⟨ex', run, _⟩
        dsimp [ProcessMessage] at run
        rcases run with ⟨_, _, _, h_contra⟩ | ⟨benv, eq_benv, run⟩; contradiction
        rcases run with ⟨ex'', run, _⟩
        dsimp [ExecuteCode] at run
        dsimp [initEvm] at run
        have h_devm : benv.state.getCode adr = devm.getCode adr := by
          subst hp_childMsg hp_evm1
          dsimp [Msg.benvAfterTransfer, callMsg, Devm.withReturnData] at eq_benv
          rcases hp_sub : ({ state := devm11.state, createdAccounts := devm11.createdAccounts, stat := sevm.benvStat } : Benv).subBal sevm.currentTarget value with _ | benv_sub
          · simp [hp_sub, Option.toExcept, Bind.bind, Except.bind] at eq_benv
          · simp [hp_sub, Option.toExcept, Bind.bind, Except.bind] at eq_benv
            subst eq_benv
            have h1 := Benv.addBal_getCode benv_sub callee adr value
            have h2 := Benv.subBal_getCode (a := adr) hp_sub
            have h_devm11_state : ({ state := devm11.state, createdAccounts := devm11.createdAccounts, stat := sevm.benvStat } : Benv).state.getCode adr = devm11.getCode adr := rfl
            rw [h_devm11_state] at h2
            rw [h1, h2]
            have h11 : devm11.getCode adr = devm10.getCode adr := by subst hp18; exact Devm.memExtends_getCode
            have h10 : devm10.getCode adr = devm9.getCode adr := chargeGas_getCode eq16
            have h9 : devm9.getCode adr = devm8.getCode adr := by
              have h9' := @accessDelegation_getCode devm8 callee adr
              rw [← hp11] at h9'
              exact h9'
            have h8 : devm8.getCode adr = devm7.getCode adr := by subst hp10; exact addAccessedAddress_getCode
            have h7 : devm7.getCode adr = devm6.getCode adr := Devm.popToNat_getCode eq7
            have h6 : devm6.getCode adr = devm5.getCode adr := Devm.popToNat_getCode eq6
            have h5 : devm5.getCode adr = devm4.getCode adr := Devm.popToNat_getCode eq5
            have h4 : devm4.getCode adr = devm3.getCode adr := Devm.popToNat_getCode eq4
            have h3 : devm3.getCode adr = devm2.getCode adr := Devm.pop_getCode eq3
            have h2' : devm2.getCode adr = devm1.getCode adr := Devm.popToAdr_getCode eq2
            have h1' : devm1.getCode adr = devm.getCode adr := Devm.pop_getCode eq1
            rw [h11, h10, h9, h8, h7, h6, h5, h4, h3, h2', h1']
        subst hp_childMsg
        dsimp [Msg.withBenv, callMsg] at run
        split_ifs at run with h_precomp
        · rcases run with ⟨h_xl, _⟩; cases h_xl
        · rcases run with ⟨ex''', h_xl, _⟩
          injection h_xl with h_xl_eq
          injection h_xl_eq with _ h_devm_eq
          injection h_devm_eq with h_devm_eq _
          subst h_devm_eq
          exact h_devm
  case callcode =>
    dsimp [Xinst.Run] at run
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨gas, devm1⟩, eq1, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨codeAddress, devm2⟩, eq2, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨value, devm3⟩, eq3, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨inputIndex, devm4⟩, eq4, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨inputSize, devm5⟩, eq5, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨outputIndex, devm6⟩, eq6, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨outputSize, devm7⟩, eq7, run⟩; contradiction
    rcases run with ⟨extendCost, hp8, run⟩
    rcases run with ⟨preAccessCost, hp9, run⟩
    rcases run with ⟨devm8, hp10, run⟩
    rcases run with ⟨⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm9⟩, hp11, run⟩
    rcases run with ⟨accessCost, hp12, run⟩
    rcases run with ⟨transferCost, hp13, run⟩
    rcases run with ⟨⟨msgCallCost, msgCallStipend⟩, hp14, run⟩
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨devm10, eq15, run⟩; contradiction
    rcases run with ⟨devm11, hp16, run⟩
    rcases run with ⟨senderBal, hp17, run⟩
    split_ifs at run with h_bal
    · rcases run with ⟨_, _, _, h_contra⟩ | ⟨devm12, eq18, run⟩; contradiction
      rcases run with ⟨h_xl, h_ex⟩
      cases h_xl
    · dsimp [GenericCall] at run
      rcases run with ⟨evm1, hp_evm1, run⟩
      split_ifs at run with h_depth
      · rcases run with ⟨h_xl, _⟩; contradiction
      · rcases run with ⟨calldata, _, run⟩
        rcases run with ⟨childMsg, hp_childMsg, run⟩
        rcases run with ⟨ex', run, _⟩
        dsimp [ProcessMessage] at run
        rcases run with ⟨_, _, _, h_contra⟩ | ⟨benv, eq_benv, run⟩; contradiction
        rcases run with ⟨ex'', run, _⟩
        dsimp [ExecuteCode] at run
        dsimp [initEvm] at run
        have h_devm : benv.state.getCode adr = devm.getCode adr := by
          subst hp_childMsg hp_evm1
          dsimp [Msg.benvAfterTransfer, callMsg, Devm.withReturnData] at eq_benv
          rcases hp_sub : ({ state := devm11.state, createdAccounts := devm11.createdAccounts, stat := sevm.benvStat } : Benv).subBal sevm.currentTarget value with _ | benv_sub
          · simp [hp_sub, Option.toExcept, Bind.bind, Except.bind] at eq_benv
          · simp [hp_sub, Option.toExcept, Bind.bind, Except.bind] at eq_benv
            subst eq_benv
            have h1 := Benv.addBal_getCode benv_sub sevm.currentTarget adr value
            have h2 := Benv.subBal_getCode (a := adr) hp_sub
            have h_devm11_state : ({ state := devm11.state, createdAccounts := devm11.createdAccounts, stat := sevm.benvStat } : Benv).state.getCode adr = devm11.getCode adr := rfl
            rw [h_devm11_state] at h2
            rw [h1, h2]
            have h11 : devm11.getCode adr = devm10.getCode adr := by subst hp16; exact Devm.memExtends_getCode
            have h10 : devm10.getCode adr = devm9.getCode adr := chargeGas_getCode eq15
            have h9 : devm9.getCode adr = devm8.getCode adr := by
              have h9' := @accessDelegation_getCode devm8 codeAddress adr
              rw [← hp11] at h9'
              exact h9'
            have h8 : devm8.getCode adr = devm7.getCode adr := by subst hp10; exact addAccessedAddress_getCode
            have h7 : devm7.getCode adr = devm6.getCode adr := Devm.popToNat_getCode eq7
            have h6 : devm6.getCode adr = devm5.getCode adr := Devm.popToNat_getCode eq6
            have h5 : devm5.getCode adr = devm4.getCode adr := Devm.popToNat_getCode eq5
            have h4 : devm4.getCode adr = devm3.getCode adr := Devm.popToNat_getCode eq4
            have h3 : devm3.getCode adr = devm2.getCode adr := Devm.pop_getCode eq3
            have h2' : devm2.getCode adr = devm1.getCode adr := Devm.popToAdr_getCode eq2
            have h1' : devm1.getCode adr = devm.getCode adr := Devm.pop_getCode eq1
            rw [h11, h10, h9, h8, h7, h6, h5, h4, h3, h2', h1']
        subst hp_childMsg
        dsimp [Msg.withBenv, callMsg] at run
        split_ifs at run with h_precomp
        · rcases run with ⟨h_xl, _⟩; cases h_xl
        · rcases run with ⟨ex''', h_xl, _⟩
          injection h_xl with h_xl_eq
          injection h_xl_eq with _ h_devm_eq
          injection h_devm_eq with h_devm_eq _
          subst h_devm_eq
          exact h_devm
  case delcall =>
    dsimp [Xinst.Run] at run
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨gas, devm1⟩, eq1, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨codeAddress, devm2⟩, eq2, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨inputIndex, devm3⟩, eq3, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨inputSize, devm4⟩, eq4, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨outputIndex, devm5⟩, eq5, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨outputSize, devm6⟩, eq6, run⟩; contradiction
    rcases run with ⟨extendCost, hp7, run⟩
    rcases run with ⟨preAccessCost, hp8, run⟩
    rcases run with ⟨devm7, hp9, run⟩
    rcases run with ⟨⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm8⟩, hp10, run⟩
    rcases run with ⟨accessCost, hp11, run⟩
    rcases run with ⟨⟨msgCallCost, msgCallStipend⟩, hp12, run⟩
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨devm9, eq13, run⟩; contradiction
    rcases run with ⟨devm10, hp14, run⟩
    dsimp [GenericCall] at run
    rcases run with ⟨evm1, hp_evm1, run⟩
    split_ifs at run with h_depth
    · rcases run with ⟨h_xl, _⟩; contradiction
    · rcases run with ⟨calldata, _, run⟩
      rcases run with ⟨childMsg, hp_childMsg, run⟩
      rcases run with ⟨ex', run, _⟩
      dsimp [ProcessMessage] at run
      rcases run with ⟨_, _, _, h_contra⟩ | ⟨benv, eq_benv, run⟩; contradiction
      rcases run with ⟨ex'', run, _⟩
      dsimp [ExecuteCode] at run
      dsimp [initEvm] at run
      have h_devm : benv.state.getCode adr = devm.getCode adr := by
        subst hp_childMsg hp_evm1
        dsimp [Msg.benvAfterTransfer, callMsg, Devm.withReturnData] at eq_benv
        injection eq_benv with eq_benv
        subst eq_benv
        have h_devm10_state : ({ state := devm10.state, createdAccounts := devm10.createdAccounts, stat := sevm.benvStat } : Benv).state.getCode adr = devm10.getCode adr := rfl
        rw [h_devm10_state]
        have h14 : devm10.getCode adr = devm9.getCode adr := by subst hp14; exact Devm.memExtends_getCode
        have h13 : devm9.getCode adr = devm8.getCode adr := chargeGas_getCode eq13
        have h10 : devm8.getCode adr = devm7.getCode adr := by
          have h10' := @accessDelegation_getCode devm7 codeAddress adr
          rw [← hp10] at h10'
          exact h10'
        have h9 : devm7.getCode adr = devm6.getCode adr := by subst hp9; exact addAccessedAddress_getCode
        have h6 : devm6.getCode adr = devm5.getCode adr := Devm.popToNat_getCode eq6
        have h5 : devm5.getCode adr = devm4.getCode adr := Devm.popToNat_getCode eq5
        have h4 : devm4.getCode adr = devm3.getCode adr := Devm.popToNat_getCode eq4
        have h3 : devm3.getCode adr = devm2.getCode adr := Devm.popToNat_getCode eq3
        have h2' : devm2.getCode adr = devm1.getCode adr := Devm.popToAdr_getCode eq2
        have h1' : devm1.getCode adr = devm.getCode adr := Devm.pop_getCode eq1
        rw [h14, h13, h10, h9, h6, h5, h4, h3, h2', h1']
      subst hp_childMsg
      dsimp [Msg.withBenv, callMsg] at run
      split_ifs at run with h_precomp
      · rcases run with ⟨h_xl, _⟩; cases h_xl
      · rcases run with ⟨ex''', h_xl, _⟩
        injection h_xl with h_xl_eq
        injection h_xl_eq with _ h_devm_eq
        injection h_devm_eq with h_devm_eq _
        subst h_devm_eq
        exact h_devm
  case create2 =>
    dsimp [Xinst.Run] at run
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨endowment, devm1⟩, eq1, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨memoryIndex, devm2⟩, eq2, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨memorySize, devm3⟩, eq3, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨salt, devm4⟩, eq4, run⟩; contradiction
    rcases run with ⟨extendCost, hp5, run⟩
    rcases run with ⟨initCodeHashCost, hp6, run⟩
    rcases run with ⟨initCodeCost, hp7, run⟩
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨devm5, eq8, run⟩; contradiction
    rcases run with ⟨devm6, hp9, run⟩
    rcases run with ⟨newAddress, hp10, run⟩
    dsimp [GenericCreate] at run
    rcases run with ⟨calldata, hp11, run⟩
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, _, run⟩; contradiction
    rcases run with ⟨devm7, hp12, run⟩
    rcases run with ⟨createMsgGas, hp13, run⟩
    rcases run with ⟨devm8, hp14, run⟩
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, _, run⟩; contradiction
    rcases run with ⟨devm9, hp15, run⟩
    rcases run with ⟨sender, hp16, run⟩
    split_ifs at run with h_sender
    · rcases run with ⟨h_xl, h_ex⟩
      cases h_xl
    · rcases run with ⟨devm10, hp17, run_inner⟩
      split_ifs at run_inner with h_target
      · rcases run_inner with ⟨h_xl, h_ex⟩
        cases h_xl
      · rcases run_inner with ⟨childMsg, hp18, run_inner⟩
        rcases run_inner with ⟨ex', run_inner, _⟩
        dsimp [ProcessCreateMessage] at run_inner
        rcases run_inner with ⟨ex'', run_inner, _⟩
        dsimp [ProcessMessage] at run_inner
        rcases run_inner with ⟨_, _, _, h_contra⟩ | ⟨benv, eq_benv, run_inner⟩; contradiction
        rcases run_inner with ⟨ex''', run_inner, _⟩
        dsimp [ExecuteCode] at run_inner
        dsimp [initEvm] at run_inner
        have h_devm : benv.state.getCode adr = devm.getCode adr := by
          rw [hp18] at eq_benv
          dsimp [processCreateMessage.msg, Msg.benvAfterTransfer, Msg.withBenv, Msg.shouldTransferValue] at eq_benv
          set benv_init := (addCreatedAccount (({ state := devm10.state, createdAccounts := devm10.createdAccounts, stat := sevm.benvStat } : Benv).setStor newAddress Stor.empty) newAddress).incrNonce newAddress
          rcases hp_sub : benv_init.subBal sevm.currentTarget endowment with _ | benv_sub
          · rw [hp_sub] at eq_benv
            simp [Option.toExcept, Bind.bind, Except.bind] at eq_benv
          · rw [hp_sub] at eq_benv
            simp [Option.toExcept, Bind.bind, Except.bind] at eq_benv
            subst eq_benv
            have h1 := Benv.addBal_getCode (a := adr) benv_sub newAddress endowment
            have h2 := Benv.subBal_getCode (a := adr) hp_sub
            have h_benv_init : benv_init.state.getCode adr = devm10.getCode adr := by
              dsimp [benv_init]
              rw [Benv.incrNonce_getCode, addCreatedAccount_getCode, Benv.setStor_getCode]
              rfl
            rw [h_benv_init] at h2
            rw [h1, h2]
            have h17 : devm10.getCode adr = devm9.getCode adr := by subst hp17; exact Devm.incrNonce_getCode
            have h15 : devm9.getCode adr = devm8.getCode adr := by subst hp15; rfl
            have h14 : devm8.getCode adr = devm7.getCode adr := by subst hp14; rfl
            have h12 : devm7.getCode adr = devm6.getCode adr := by subst hp12; exact addAccessedAddress_getCode
            have h9 : devm6.getCode adr = devm5.getCode adr := by subst hp9; exact Devm.memExtends_getCode
            have h8 : devm5.getCode adr = devm4.getCode adr := chargeGas_getCode eq8
            have h4 : devm4.getCode adr = devm3.getCode adr := Devm.pop_getCode eq4
            have h3 : devm3.getCode adr = devm2.getCode adr := Devm.popToNat_getCode eq3
            have h2' : devm2.getCode adr = devm1.getCode adr := Devm.popToNat_getCode eq2
            have h1' : devm1.getCode adr = devm.getCode adr := Devm.pop_getCode eq1
            rw [h17, h15, h14, h12, h9, h8, h4, h3, h2', h1']
        rw [hp18] at run_inner
        dsimp [processCreateMessage.msg, Msg.withBenv] at run_inner
        rcases run_inner with ⟨ex'''', h_xl, _⟩
        injection h_xl with h_xl_eq
        injection h_xl_eq with _ h_devm_eq
        injection h_devm_eq with h_devm_eq _
        subst h_devm_eq
        exact h_devm
  case statcall =>
    dsimp [Xinst.Run] at run
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨gas, devm1⟩, eq1, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨target, devm2⟩, eq2, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨inputIndex, devm3⟩, eq3, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨inputSize, devm4⟩, eq4, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨outputIndex, devm5⟩, eq5, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨outputSize, devm6⟩, eq6, run⟩; contradiction
    rcases run with ⟨extendCost, hp7, run⟩
    rcases run with ⟨preAccessCost, hp8, run⟩
    rcases run with ⟨devm7, hp9, run⟩
    rcases run with ⟨⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm8⟩, hp10, run⟩
    rcases run with ⟨accessCost, hp11, run⟩
    rcases run with ⟨⟨msgCallCost, msgCallStipend⟩, hp12, run⟩
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨devm9, eq13, run⟩; contradiction
    rcases run with ⟨devm10, hp14, run⟩
    dsimp [GenericCall] at run
    rcases run with ⟨evm1, hp_evm1, run⟩
    split_ifs at run with h_depth
    · rcases run with ⟨h_xl, _⟩; contradiction
    · rcases run with ⟨calldata, _, run⟩
      rcases run with ⟨childMsg, hp_childMsg, run⟩
      rcases run with ⟨ex', run, _⟩
      dsimp [ProcessMessage] at run
      rcases run with ⟨_, _, _, h_contra⟩ | ⟨benv, eq_benv, run⟩; contradiction
      rcases run with ⟨ex'', run, _⟩
      dsimp [ExecuteCode] at run
      dsimp [initEvm] at run
      have h_devm : benv.state.getCode adr = devm.getCode adr := by
        subst hp_childMsg hp_evm1
        dsimp [Msg.benvAfterTransfer, callMsg, Devm.withReturnData] at eq_benv
        rcases hp_sub : ({ state := devm10.state, createdAccounts := devm10.createdAccounts, stat := sevm.benvStat } : Benv).subBal sevm.currentTarget 0 with _ | benv_sub
        · simp [hp_sub, Option.toExcept, Bind.bind, Except.bind] at eq_benv
        · simp [hp_sub, Option.toExcept, Bind.bind, Except.bind] at eq_benv
          subst eq_benv
          have h1 := Benv.addBal_getCode benv_sub target adr 0
          have h2 := Benv.subBal_getCode (a := adr) hp_sub
          have h_devm10_state : ({ state := devm10.state, createdAccounts := devm10.createdAccounts, stat := sevm.benvStat } : Benv).state.getCode adr = devm10.getCode adr := rfl
          rw [h_devm10_state] at h2
          rw [h1, h2]
          have h14 : devm10.getCode adr = devm9.getCode adr := by subst hp14; exact Devm.memExtends_getCode
          have h13 : devm9.getCode adr = devm8.getCode adr := chargeGas_getCode eq13
          have h10 : devm8.getCode adr = devm7.getCode adr := by
            have h10' := @accessDelegation_getCode devm7 target adr
            rw [← hp10] at h10'
            exact h10'
          have h9 : devm7.getCode adr = devm6.getCode adr := by subst hp9; exact addAccessedAddress_getCode
          have h6 : devm6.getCode adr = devm5.getCode adr := Devm.popToNat_getCode eq6
          have h5 : devm5.getCode adr = devm4.getCode adr := Devm.popToNat_getCode eq5
          have h4 : devm4.getCode adr = devm3.getCode adr := Devm.popToNat_getCode eq4
          have h3 : devm3.getCode adr = devm2.getCode adr := Devm.popToNat_getCode eq3
          have h2' : devm2.getCode adr = devm1.getCode adr := Devm.popToAdr_getCode eq2
          have h1' : devm1.getCode adr = devm.getCode adr := Devm.pop_getCode eq1
          rw [h14, h13, h10, h9, h6, h5, h4, h3, h2', h1']
      subst hp_childMsg
      dsimp [Msg.withBenv, callMsg] at run
      split_ifs at run with h_precomp
      · rcases run with ⟨h_xl, _⟩; cases h_xl
      · rcases run with ⟨ex''', h_xl, _⟩
        injection h_xl with h_xl_eq
        injection h_xl_eq with _ h_devm_eq
        injection h_devm_eq with h_devm_eq _
        subst h_devm_eq
        exact h_devm

lemma Xinst.prep_inv_getCode
    {sevm : Sevm}
    {devm : Devm}
    {sevm_ : Sevm}
    {devm_ : Devm}
    {exn_ res : Execution}
    {adr : Adr}
    {x : Xinst}
    (run : Xinst.Run sevm devm x (some (sevm_, devm_, exn_)) res) :
    devm_.getCode adr = devm.getCode adr := by
  exact Xinst.prep_codeFrame run adr

lemma Ninst.prep_inv_getCode
    {pc sevm devm n sevm_ devm_ exn_ res}
    (run : Ninst.Run' pc sevm devm n (.some ⟨sevm_, devm_, exn_⟩) res) (a : Adr)
    : devm_.getCode a = devm.getCode a := by
  cases n
  case push xs _ => revert run; dsimp [Ninst.Run']; exact fun h => h.elim
  case reg r => revert run; dsimp [Ninst.Run']; exact fun h => h.elim
  case exec x => revert run; dsimp [Ninst.Run']; apply Xinst.prep_inv_getCode

/-! The suspended execution source depends essentially on the instruction
family.  Create instructions enter fresh code, ordinary calls consult the
callee's delegation marker, while callcode/delegatecall retain the parent's
current target. -/

lemma Xinst.prep_codeSource
    {sevm : Sevm} {devm : Devm} {sevm_ : Sevm} {devm_ : Devm}
    {exn_ res : Execution} {x : Xinst}
    (run : Xinst.Run sevm devm x (some (sevm_, devm_, exn_)) res) :
    match x with
    | .create => devm.getCode sevm_.currentTarget = .empty
    | .create2 => devm.getCode sevm_.currentTarget = .empty
    | .call =>
      ¬ isValidDelegation (devm.getCode sevm_.currentTarget) →
        sevm_.code = devm.getCode sevm_.currentTarget
    | .statcall =>
      ¬ isValidDelegation (devm.getCode sevm_.currentTarget) →
        sevm_.code = devm.getCode sevm_.currentTarget
    | .callcode => sevm_.currentTarget = sevm.currentTarget
    | .delcall => sevm_.currentTarget = sevm.currentTarget := by
  cases x <;> simp only
  case create =>
    dsimp [Xinst.Run] at run
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨v14, eq14, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨v13, eq13, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨v12, eq12, run⟩; contradiction
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨devm9, eq9, run⟩; contradiction
    rcases run with ⟨devm8, eq8, run⟩
    rcases run with ⟨newAddress, hp_newAddress, run⟩
    dsimp [GenericCreate] at run
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, eq6, run⟩; contradiction
    rcases run with ⟨devm5, eq5, run⟩
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨devm3, eq3, run⟩
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, eq2, run⟩; contradiction
    rcases run with ⟨devm1, eq1, run⟩
    rcases run with ⟨_, _, run⟩
    split_ifs at run with h_sender_bal
    · rcases run with ⟨h_xl, _⟩; cases h_xl
    · rcases run with ⟨devm4, hp_devm4, run⟩
      split_ifs at run with h_target_nonce
      · rcases run with ⟨h_xl, _⟩; cases h_xl
      · rcases run with ⟨childMsg, hp_childMsg, run⟩
        subst hp_childMsg
        rcases run with ⟨ex', run, _⟩
        dsimp [ProcessCreateMessage] at run
        rcases run with ⟨ex_create, run, _⟩
        dsimp [ProcessMessage] at run
        rcases run with ⟨_, _, _, h_contra⟩ | ⟨benv, eq_benv, run⟩; contradiction
        rcases run with ⟨ex'', run, _⟩
        dsimp [ExecuteCode] at run
        dsimp [initEvm] at run
        dsimp [processCreateMessage.msg] at run
        dsimp [Msg.withBenv] at run
        rcases run with ⟨ex''', h_xl, _⟩
        injection h_xl with h_xl_eq
        injection h_xl_eq with h_sevm_eq _
        subst h_sevm_eq
        push_neg at h_target_nonce
        rcases h_target_nonce with ⟨_, h_code_size, _⟩
        have h1 : devm4.getCode newAddress = devm1.getCode newAddress := by subst hp_devm4; exact Devm.incrNonce_getCode
        have h2 : devm1.getCode newAddress = devm3.getCode newAddress := by subst eq1; rfl
        have h3 : devm3.getCode newAddress = devm5.getCode newAddress := by subst eq3; rfl
        have h4 : devm5.getCode newAddress = devm8.getCode newAddress := by subst eq5; exact addAccessedAddress_getCode
        have h5 : devm8.getCode newAddress = devm9.getCode newAddress := by subst eq8; exact Devm.memExtends_getCode
        have h6 : devm9.getCode newAddress = v12.2.getCode newAddress := chargeGas_getCode eq9
        have h7 : v12.2.getCode newAddress = v13.2.getCode newAddress := Devm.popToNat_getCode eq12
        have h8 : v13.2.getCode newAddress = v14.2.getCode newAddress := Devm.popToNat_getCode eq13
        have h9 : v14.2.getCode newAddress = devm.getCode newAddress := Devm.pop_getCode eq14
        have h_devm4 : devm4.getCode newAddress = devm.getCode newAddress := by
          rw [h1, h2, h3, h4, h5, h6, h7, h8, h9]
        have h_size : (devm4.getCode newAddress).size = 0 := h_code_size
        have h_empty' : devm.getCode newAddress = .empty := by
          rw [← h_devm4]
          cases h_code : devm4.getCode newAddress with | mk data =>
          rw [h_code] at h_size
          cases data with | mk l =>
          cases l
          · rfl
          · contradiction
        exact h_empty'
  case call =>
    intro notDel
    dsimp [Xinst.Run] at run
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨v16, eq1, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨callee_tuple, eq2, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨v15, eq3, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨v14, eq4, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨v13, eq5, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨v12, eq6, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨v11, eq7, run⟩; contradiction
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨devm8, hp_devm8, run⟩
    rcases run with ⟨del_res, hp_del_res, run⟩
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, eq8, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, _, run⟩; contradiction
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, run⟩
    split_ifs at run with h_bal
    · rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, _, run⟩; contradiction
      rcases run with ⟨h_xl, _⟩; cases h_xl
    · dsimp [GenericCall] at run
      rcases run with ⟨evm1, hp_evm1, run⟩
      split_ifs at run with h_depth
      · rcases run with ⟨h_xl, _⟩; cases h_xl
      · rcases run with ⟨_, _, run⟩
        rcases run with ⟨childMsg, hp_childMsg, run⟩
        subst hp_childMsg
        rcases run with ⟨ex', run, _⟩
        dsimp [ProcessMessage] at run
        rcases run with ⟨_, _, _, h_contra⟩ | ⟨benv, eq_benv, run⟩; contradiction
        rcases run with ⟨ex'', run, _⟩
        dsimp [ExecuteCode] at run
        dsimp [initEvm] at run
        dsimp [Msg.withBenv, callMsg] at run
        split_ifs at run with h_precomp
        · rcases run with ⟨h_xl, _⟩; cases h_xl
        · rcases run with ⟨ex''', h_xl, _⟩
          injection h_xl with h_xl_eq
          injection h_xl_eq with h_sevm_eq _
          subst h_sevm_eq
          have h_code : del_res.2.2.1 = devm.getCode callee_tuple.1 := by
            subst hp_del_res
            have h1 : devm8.getCode callee_tuple.1 = devm.getCode callee_tuple.1 := by
              subst hp_devm8
              have h2 : v11.2.getCode callee_tuple.1 = v12.2.getCode callee_tuple.1 := Devm.popToNat_getCode eq7
              have h3 : v12.2.getCode callee_tuple.1 = v13.2.getCode callee_tuple.1 := Devm.popToNat_getCode eq6
              have h4 : v13.2.getCode callee_tuple.1 = v14.2.getCode callee_tuple.1 := Devm.popToNat_getCode eq5
              have h5 : v14.2.getCode callee_tuple.1 = v15.2.getCode callee_tuple.1 := Devm.popToNat_getCode eq4
              have h6 : v15.2.getCode callee_tuple.1 = callee_tuple.2.getCode callee_tuple.1 := Devm.pop_getCode eq3
              have h7 : callee_tuple.2.getCode callee_tuple.1 = v16.2.getCode callee_tuple.1 := Devm.popToAdr_getCode eq2
              have h8 : v16.2.getCode callee_tuple.1 = devm.getCode callee_tuple.1 := Devm.pop_getCode eq1
              rw [addAccessedAddress_getCode, h2, h3, h4, h5, h6, h7, h8]
            dsimp [accessDelegation]
            split_ifs with h_del
            · exfalso; apply notDel
              change isValidDelegation (devm8.getCode callee_tuple.1) at h_del
              rw [h1] at h_del
              exact h_del
            · exact h1
          exact h_code
  case callcode =>
    dsimp [Xinst.Run] at run
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, _, run⟩; contradiction
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, _, run⟩; contradiction
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, run⟩
    split_ifs at run with h_bal
    · rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, _, run⟩; contradiction
      rcases run with ⟨h_xl, _⟩; cases h_xl
    · dsimp [GenericCall] at run
      rcases run with ⟨evm1, _, run⟩
      split_ifs at run with h_depth
      · rcases run with ⟨h_xl, _⟩; cases h_xl
      · rcases run with ⟨_, _, run⟩
        rcases run with ⟨childMsg, hp_childMsg, run⟩
        subst hp_childMsg
        rcases run with ⟨ex', run, _⟩
        dsimp [ProcessMessage] at run
        rcases run with ⟨_, _, _, h_contra⟩ | ⟨benv, eq_benv, run⟩; contradiction
        rcases run with ⟨ex'', run, _⟩
        dsimp [ExecuteCode] at run
        dsimp [initEvm] at run
        dsimp [Msg.withBenv, callMsg] at run
        split_ifs at run with h_precomp
        · rcases run with ⟨h_xl, _⟩; cases h_xl
        · rcases run with ⟨ex''', h_xl, _⟩
          injection h_xl with h_xl_eq
          injection h_xl_eq with h_sevm_eq _
          subst h_sevm_eq
          rfl
  case delcall =>
    dsimp [Xinst.Run] at run
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, _, run⟩; contradiction
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, _, run⟩; contradiction
    rcases run with ⟨_, _, run⟩
    dsimp [GenericCall] at run
    rcases run with ⟨evm1, _, run⟩
    split_ifs at run with h_depth
    · rcases run with ⟨h_xl, _⟩; cases h_xl
    · rcases run with ⟨_, _, run⟩
      rcases run with ⟨childMsg, hp_childMsg, run⟩
      subst hp_childMsg
      rcases run with ⟨ex', run, _⟩
      dsimp [ProcessMessage] at run
      rcases run with ⟨_, _, _, h_contra⟩ | ⟨benv, eq_benv, run⟩; contradiction
      rcases run with ⟨ex'', run, _⟩
      dsimp [ExecuteCode] at run
      dsimp [initEvm] at run
      dsimp [Msg.withBenv, callMsg] at run
      split_ifs at run with h_precomp
      · rcases run with ⟨h_xl, _⟩; cases h_xl
      · rcases run with ⟨ex''', h_xl, _⟩
        injection h_xl with h_xl_eq
        injection h_xl_eq with h_sevm_eq _
        subst h_sevm_eq
        rfl
  case create2 =>
    dsimp [Xinst.Run] at run
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨v15, eq15, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨v14, eq14, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨v13, eq13, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨v12, eq12, run⟩; contradiction
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨devm9, eq9, run⟩; contradiction
    rcases run with ⟨devm8, eq8, run⟩
    rcases run with ⟨newAddress, hp_newAddress, run⟩
    dsimp [GenericCreate] at run
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, eq6, run⟩; contradiction
    rcases run with ⟨devm5, eq5, run⟩
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨devm3, eq3, run⟩
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, eq2, run⟩; contradiction
    rcases run with ⟨devm1, eq1, run⟩
    rcases run with ⟨_, _, run⟩
    split_ifs at run with h_sender_bal
    · rcases run with ⟨h_xl, _⟩; cases h_xl
    · rcases run with ⟨devm4, hp_devm4, run⟩
      split_ifs at run with h_target_nonce
      · rcases run with ⟨h_xl, _⟩; cases h_xl
      · rcases run with ⟨childMsg, hp_childMsg, run⟩
        subst hp_childMsg
        rcases run with ⟨ex', run, _⟩
        dsimp [ProcessCreateMessage] at run
        rcases run with ⟨ex_create, run, _⟩
        dsimp [ProcessMessage] at run
        rcases run with ⟨_, _, _, h_contra⟩ | ⟨benv, eq_benv, run⟩; contradiction
        rcases run with ⟨ex'', run, _⟩
        dsimp [ExecuteCode] at run
        dsimp [initEvm] at run
        dsimp [processCreateMessage.msg] at run
        dsimp [Msg.withBenv] at run
        rcases run with ⟨ex''', h_xl, _⟩
        injection h_xl with h_xl_eq
        injection h_xl_eq with h_sevm_eq _
        subst h_sevm_eq
        push_neg at h_target_nonce
        rcases h_target_nonce with ⟨_, h_code_size, _⟩
        have h1 : devm4.getCode newAddress = devm1.getCode newAddress := by subst hp_devm4; exact Devm.incrNonce_getCode
        have h2 : devm1.getCode newAddress = devm3.getCode newAddress := by subst eq1; rfl
        have h3 : devm3.getCode newAddress = devm5.getCode newAddress := by subst eq3; rfl
        have h4 : devm5.getCode newAddress = devm8.getCode newAddress := by subst eq5; exact addAccessedAddress_getCode
        have h5 : devm8.getCode newAddress = devm9.getCode newAddress := by subst eq8; exact Devm.memExtends_getCode
        have h6 : devm9.getCode newAddress = v12.2.getCode newAddress := chargeGas_getCode eq9
        have h7 : v12.2.getCode newAddress = v13.2.getCode newAddress := Devm.pop_getCode eq12
        have h8 : v13.2.getCode newAddress = v14.2.getCode newAddress := Devm.popToNat_getCode eq13
        have h9 : v14.2.getCode newAddress = v15.2.getCode newAddress := Devm.popToNat_getCode eq14
        have h10 : v15.2.getCode newAddress = devm.getCode newAddress := Devm.pop_getCode eq15
        have h_devm4 : devm4.getCode newAddress = devm.getCode newAddress := by
          rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
        have h_size : (devm4.getCode newAddress).size = 0 := h_code_size
        have h_empty' : devm.getCode newAddress = .empty := by
          rw [← h_devm4]
          cases h_code : devm4.getCode newAddress with | mk data =>
          rw [h_code] at h_size
          cases data with | mk l =>
          cases l
          · rfl
          · contradiction
        exact h_empty'
  case statcall =>
    intro notDel
    dsimp [Xinst.Run] at run
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨v15, eq1, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨callee_tuple, eq2, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨v14, eq3, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨v13, eq4, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨v12, eq5, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨v11, eq6, run⟩; contradiction
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨devm8, hp_devm8, run⟩
    rcases run with ⟨del_res, hp_del_res, run⟩
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, run⟩
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, eq8, run⟩; contradiction
    rcases run with ⟨_, _, run⟩
    dsimp [GenericCall] at run
    rcases run with ⟨evm1, hp_evm1, run⟩
    split_ifs at run with h_depth
    · rcases run with ⟨h_xl, _⟩; cases h_xl
    · rcases run with ⟨_, _, run⟩
      rcases run with ⟨childMsg, hp_childMsg, run⟩
      subst hp_childMsg
      rcases run with ⟨ex', run, _⟩
      dsimp [ProcessMessage] at run
      rcases run with ⟨_, _, _, h_contra⟩ | ⟨benv, eq_benv, run⟩; contradiction
      rcases run with ⟨ex'', run, _⟩
      dsimp [ExecuteCode] at run
      dsimp [initEvm] at run
      dsimp [Msg.withBenv, callMsg] at run
      split_ifs at run with h_precomp
      · rcases run with ⟨h_xl, _⟩; cases h_xl
      · rcases run with ⟨ex''', h_xl, _⟩
        injection h_xl with h_xl_eq
        injection h_xl_eq with h_sevm_eq _
        subst h_sevm_eq
        have h_code : del_res.2.2.1 = devm.getCode callee_tuple.1 := by
          subst hp_del_res
          have h1 : devm8.getCode callee_tuple.1 = devm.getCode callee_tuple.1 := by
            subst hp_devm8
            have h2 : v11.2.getCode callee_tuple.1 = v12.2.getCode callee_tuple.1 := Devm.popToNat_getCode eq6
            have h3 : v12.2.getCode callee_tuple.1 = v13.2.getCode callee_tuple.1 := Devm.popToNat_getCode eq5
            have h4 : v13.2.getCode callee_tuple.1 = v14.2.getCode callee_tuple.1 := Devm.popToNat_getCode eq4
            have h5 : v14.2.getCode callee_tuple.1 = callee_tuple.2.getCode callee_tuple.1 := Devm.popToNat_getCode eq3
            have h6 : callee_tuple.2.getCode callee_tuple.1 = v15.2.getCode callee_tuple.1 := Devm.popToAdr_getCode eq2
            have h7 : v15.2.getCode callee_tuple.1 = devm.getCode callee_tuple.1 := Devm.pop_getCode eq1
            rw [addAccessedAddress_getCode, h2, h3, h4, h5, h6, h7]
          dsimp [accessDelegation]
          split_ifs with h_del
          · exfalso; apply notDel
            change isValidDelegation (devm8.getCode callee_tuple.1) at h_del
            rw [h1] at h_del
            exact h_del
          · exact h1
        exact h_code

lemma Xinst.prep_inv_code
    {sevm : Sevm} {devm : Devm} {sevm_ : Sevm} {devm_ : Devm}
    {exn_ res : Execution} {x : Xinst}
    (ne : sevm.currentTarget ≠ sevm_.currentTarget)
    (notEmpty : devm.getCode sevm_.currentTarget ≠ .empty)
    (notDel : ¬ isValidDelegation (devm.getCode sevm_.currentTarget))
    (run : Xinst.Run sevm devm x (some (sevm_, devm_, exn_)) res) :
    sevm_.code = devm.getCode sevm_.currentTarget := by
  have source := Xinst.prep_codeSource run
  cases x
  case create => exact (notEmpty source).elim
  case create2 => exact (notEmpty source).elim
  case call => exact source notDel
  case statcall => exact source notDel
  case callcode => exact (ne source.symm).elim
  case delcall => exact (ne source.symm).elim

lemma Ninst.prep_inv_code
    {pc sevm devm n sevm_ devm_ exn_ res}
    (ne : sevm.currentTarget ≠ sevm_.currentTarget)
    (notEmpty : devm.getCode sevm_.currentTarget ≠ .empty)
    (notDel : ¬ isValidDelegation (devm.getCode sevm_.currentTarget))
    (run : Ninst.Run' pc sevm devm n (.some ⟨sevm_, devm_, exn_⟩) res) :
    sevm_.code = devm.getCode sevm_.currentTarget := by
  cases n
  case push xs _ => revert run; dsimp [Ninst.Run']; exact fun h => h.elim
  case reg r => revert run; dsimp [Ninst.Run']; exact fun h => h.elim
  case exec x =>
    revert run; dsimp [Ninst.Run'];
    apply Xinst.prep_inv_code ne notEmpty notDel

lemma ExecuteCode.depth_eq
    {msg : Msg} {sevm_ devm_ exn_ ex}
    (run : ExecuteCode msg (.some ⟨sevm_, devm_, exn_⟩) ex) :
    sevm_.depth = msg.depth := by
  dsimp [ExecuteCode] at run
  split at run
  · rcases run with ⟨_, h, _⟩
    cases h
    rfl
  · split at run
    · rcases run with ⟨h, _⟩
      contradiction
    · rcases run with ⟨_, h, _⟩
      cases h
      rfl

lemma ProcessMessage.depth_eq
    {msg : Msg} {sevm_ devm_ exn_ ex}
    (run : ProcessMessage msg (.some ⟨sevm_, devm_, exn_⟩) ex) :
    sevm_.depth = msg.depth := by
  dsimp [ProcessMessage] at run
  dsimp [Except.SplitXl] at run
  rcases run with ⟨x, _, _, h⟩ | ⟨benv, _, ex', run, _⟩
  · contradiction
  · have h := ExecuteCode.depth_eq run
    rw [h]
    rfl

lemma ProcessCreateMessage.depth_eq
    {msg : Msg} {sevm_ devm_ exn_ ex}
    (run : ProcessCreateMessage msg (.some ⟨sevm_, devm_, exn_⟩) ex) :
    sevm_.depth = msg.depth := by
  dsimp [ProcessCreateMessage] at run
  rcases run with ⟨ex', run, _⟩
  have h := ProcessMessage.depth_eq run
  rw [h]
  rfl

lemma GenericCall.depth_lt
    {sevm devm msgCallGas value caller currentTarget target
      shouldTransferValue isStatic inputIndex inputSize
      outputIndex outputSize code disablePrecompiles}
    {sevm_ devm_ exn_ ex}
    (run : GenericCall sevm devm msgCallGas value caller currentTarget target
      shouldTransferValue isStatic inputIndex inputSize
      outputIndex outputSize code disablePrecompiles (.some ⟨sevm_, devm_, exn_⟩) ex) :
    sevm_.depth < sevm.depth := by
  dsimp [GenericCall] at run
  rcases run with ⟨evm1, _, run⟩
  split at run
  · exact Option.noConfusion run.1
  rename_i h_depth
  rcases run with ⟨calldata, _, run⟩
  rcases run with ⟨_, rfl, run⟩
  rcases run with ⟨ex', run_process, run_split⟩
  have h := ProcessMessage.depth_eq run_process
  change sevm_.depth = sevm.depth - 1 at h
  omega

lemma GenericCreate.depth_lt
    {sevm devm endowment
      newAddress memoryIndex memorySize}
    {sevm_ devm_ exn_ ex}
    (run : GenericCreate sevm devm endowment
      newAddress memoryIndex memorySize (.some ⟨sevm_, devm_, exn_⟩) ex) :
    sevm_.depth < sevm.depth := by
  dsimp [GenericCreate] at run
  rcases run with ⟨calldata, _, run⟩
  rcases run with ⟨_, _, _, h_none⟩ | ⟨_, _, run⟩
  · contradiction
  rcases run with ⟨devm1, _, run⟩
  rcases run with ⟨createMsgGas, _, run⟩
  rcases run with ⟨devm2, _, run⟩
  rcases run with ⟨_, _, _, h_none⟩ | ⟨_, _, run⟩
  · contradiction
  rcases run with ⟨devm3, _, run⟩
  rcases run with ⟨sender, _, run⟩
  split at run
  · exact Option.noConfusion run.1
  rename_i h_depth
  rcases run with ⟨devm4, _, run⟩
  split at run
  · exact Option.noConfusion run.1
  rename_i h_nonce
  rcases run with ⟨_, rfl, run⟩
  rcases run with ⟨ex', run_process, run_split⟩
  have h := ProcessCreateMessage.depth_eq run_process
  change sevm_.depth = sevm.depth - 1 at h
  omega

lemma Xinst.depth_lt
    {sevm devm x}
    {sevm_ devm_ exn_ ex}
    (run : Xinst.Run sevm devm x (.some ⟨sevm_, devm_, exn_⟩) ex) :
    sevm_.depth < sevm.depth := by
  cases x
  · dsimp [Xinst.Run] at run
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨endowment, devm1⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨memoryIndex, devm2⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨memorySize, devm3⟩, _, run⟩; contradiction
    rcases run with ⟨extendCost, _, run⟩
    rcases run with ⟨initCodeCost, _, run⟩
    rcases run with ⟨_, _, _, h_none⟩ | ⟨devm4, _, run⟩; contradiction
    rcases run with ⟨devm5, _, run⟩
    rcases run with ⟨newAddress, _, run⟩
    exact GenericCreate.depth_lt run
  · dsimp [Xinst.Run] at run
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨gas, devm1⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨callee, devm2⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨value, devm3⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨inputIndex, devm4⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨inputSize, devm5⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨outputIndex, devm6⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨outputSize, devm7⟩, _, run⟩; contradiction
    rcases run with ⟨extendCost, _, run⟩
    rcases run with ⟨preAccessCost, _, run⟩
    rcases run with ⟨devm8, _, run⟩
    rcases run with ⟨⟨disablePrecompiles, _, code, delegatedAccessGasCost, devm9⟩, _, run⟩
    rcases run with ⟨accessCost, _, run⟩
    rcases run with ⟨createCost, _, run⟩
    rcases run with ⟨transferCost, _, run⟩
    rcases run with ⟨⟨msgCallCost, msgCallStipend⟩, _, run⟩
    rcases run with ⟨_, _, _, h_none⟩ | ⟨devm10, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨_, _, run⟩; contradiction
    rcases run with ⟨devm11, _, run⟩
    rcases run with ⟨senderBal, _, run⟩
    split_ifs at run
    · rcases run with ⟨_, _, _, h_none⟩ | ⟨devm12, _, h_none, run⟩
      · contradiction
      · contradiction
    · exact GenericCall.depth_lt run
  · dsimp [Xinst.Run] at run
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨gas, devm1⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨codeAddress, devm2⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨value, devm3⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨inputIndex, devm4⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨inputSize, devm5⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨outputIndex, devm6⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨outputSize, devm7⟩, _, run⟩; contradiction
    rcases run with ⟨extendCost, _, run⟩
    rcases run with ⟨preAccessCost, _, run⟩
    rcases run with ⟨devm8, _, run⟩
    rcases run with ⟨⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm9⟩, _, run⟩
    rcases run with ⟨accessCost, _, run⟩
    rcases run with ⟨transferCost, _, run⟩
    rcases run with ⟨⟨msgCallCost, msgCallStipend⟩, _, run⟩
    rcases run with ⟨_, _, _, h_none⟩ | ⟨devm10, _, run⟩; contradiction
    rcases run with ⟨devm11, _, run⟩
    rcases run with ⟨senderBal, _, run⟩
    split_ifs at run
    · rcases run with ⟨_, _, _, h_none⟩ | ⟨devm12, _, h_none, run⟩
      · contradiction
      · contradiction
    · exact GenericCall.depth_lt run
  · dsimp [Xinst.Run] at run
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨gas, devm1⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨codeAddress, devm2⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨inputIndex, devm3⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨inputSize, devm4⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨outputIndex, devm5⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨outputSize, devm6⟩, _, run⟩; contradiction
    rcases run with ⟨extendCost, _, run⟩
    rcases run with ⟨preAccessCost, _, run⟩
    rcases run with ⟨devm7, _, run⟩
    rcases run with ⟨⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm8⟩, _, run⟩
    rcases run with ⟨accessCost, _, run⟩
    rcases run with ⟨⟨msgCallCost, msgCallStipend⟩, _, run⟩
    rcases run with ⟨_, _, _, h_none⟩ | ⟨devm9, _, run⟩; contradiction
    rcases run with ⟨devm10, _, run⟩
    exact GenericCall.depth_lt run
  · dsimp [Xinst.Run] at run
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨endowment, devm1⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨memoryIndex, devm2⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨memorySize, devm3⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨salt, devm4⟩, _, run⟩; contradiction
    rcases run with ⟨extendCost, _, run⟩
    rcases run with ⟨initCodeHashCost, _, run⟩
    rcases run with ⟨initCodeCost, _, run⟩
    rcases run with ⟨_, _, _, h_none⟩ | ⟨devm5, _, run⟩; contradiction
    rcases run with ⟨devm6, _, run⟩
    rcases run with ⟨newAddress, _, run⟩
    exact GenericCreate.depth_lt run
  · dsimp [Xinst.Run] at run
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨gas, devm1⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨target, devm2⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨inputIndex, devm3⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨inputSize, devm4⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨outputIndex, devm5⟩, _, run⟩; contradiction
    rcases run with ⟨_, _, _, h_none⟩ | ⟨⟨outputSize, devm6⟩, _, run⟩; contradiction
    rcases run with ⟨extendCost, _, run⟩
    rcases run with ⟨preAccessCost, _, run⟩
    rcases run with ⟨devm7, _, run⟩
    rcases run with ⟨⟨disablePrecompiles, _, code, delegatedAccessGasCost, devm8⟩, _, run⟩
    rcases run with ⟨accessCost, _, run⟩
    rcases run with ⟨⟨msgCallCost, msgCallStipend⟩, _, run⟩
    rcases run with ⟨_, _, _, h_none⟩ | ⟨devm9, _, run⟩; contradiction
    rcases run with ⟨devm10, _, run⟩
    exact GenericCall.depth_lt run

lemma Ninst.depth_lt_of_run'_some
    {pc sevm devm n sevm_ devm_ exn_ res}
    (run : Ninst.Run' pc sevm devm n (.some ⟨sevm_, devm_, exn_⟩) res) :
    sevm_.depth < sevm.depth := by
  cases n
  case push xs _ => revert run; dsimp [Ninst.Run']; exact fun h => h.elim
  case reg r => revert run; dsimp [Ninst.Run']; exact fun h => h.elim
  case exec x => revert run; dsimp [Ninst.Run']; intro run; exact Xinst.depth_lt run

lemma Devm.pop_getCode_eq {x devm devm'} (h : Devm.pop devm = .ok ⟨x, devm'⟩) (a : Adr) : devm'.getCode a = devm.getCode a := by
  exact (Devm.pop_worldEq_of_ok h).getCode a |>.symm

lemma chargeGas_getCode_eq {cost devm devm'} (h : chargeGas cost devm = .ok devm') (a : Adr) : devm'.getCode a = devm.getCode a := by
  exact (chargeGas_worldEq_of_ok h).getCode a |>.symm

lemma Devm.push_getCode_eq {v devm devm'} (h : Devm.push v devm = .ok devm') (a : Adr) : devm'.getCode a = devm.getCode a := by
  exact (liftMachExecution_worldEq_of_ok (core := Mach.push v) h).getCode a |>.symm

lemma Devm.popToNat_getCode_eq {devm devm' n} (h : Devm.popToNat devm = .ok ⟨n, devm'⟩) (a : Adr) : devm'.getCode a = devm.getCode a := by
  exact (Devm.popToNat_worldEq_of_ok h).getCode a |>.symm

lemma Devm.popToAdr_getCode_eq {devm devm' adr} (h : Devm.popToAdr devm = .ok ⟨adr, devm'⟩) (a : Adr) : devm'.getCode a = devm.getCode a := by
  exact (liftMach_worldEq_of_ok (core := Mach.popToAdr) h).getCode a |>.symm

lemma Devm.pop_map_snd_getCode_eq {devm devm1 : Devm} (hp : (devm.pop <&> Prod.snd) = .ok devm1) (a : Adr) : devm1.getCode a = devm.getCode a := by
  dsimp [(· <&> ·), Functor.mapRev, Functor.map, Except.map] at hp
  rcases hp2 : devm.pop with _ | ⟨x, devm2⟩
  · simp [hp2] at hp
  · simp [hp2] at hp
    rcases hp with ⟨_, rfl⟩
    exact (Devm.pop_worldEq_of_ok hp2).getCode a |>.symm

lemma Devm.pop_map_snd_getCode_err {devm : Devm} {err : String × Devm} (hp : (devm.pop <&> Prod.snd) = .error err) (a : Adr) : err.2.getCode a = devm.getCode a := by
  dsimp [(· <&> ·), Functor.mapRev, Functor.map, Except.map] at hp
  rcases hp2 : devm.pop with e | ⟨x, devm2⟩
  · simp [hp2] at hp; cases hp
    exact (Devm.pop_worldEq_of_error hp2).getCode a |>.symm
  · simp [hp2] at hp

@[simp] lemma Except.bind_error {α β ε} (e : ε) (f : α → Except ε β) : (Except.error e >>= f) = Except.error e := rfl
@[simp] lemma Except.bind_ok {α β ε} (x : α) (f : α → Except ε β) : (Except.ok x >>= f) = f x := rfl

lemma getCode_eq_of_bind {α ε} {ma : Except ε α} {f : α → Except ε Devm}
    {devm devm' : Devm} {a : Adr}
    (run : (ma >>= f) = .ok devm')
    (getDevm : α → Devm)
    (h_first : ∀ v, ma = .ok v → (getDevm v).getCode a = devm.getCode a)
    (h_rest : ∀ v, ma = .ok v → f v = .ok devm' → devm'.getCode a = (getDevm v).getCode a) :
    devm'.getCode a = devm.getCode a := by
  rcases of_bind_eq_ok run with ⟨v, hm, hf⟩
  rw [h_rest v hm hf, h_first v hm]

lemma pushItem_getCode_eq {x c devm devm'} (h : pushItem x c devm = .ok devm') (a : Adr) : devm'.getCode a = devm.getCode a := by
  exact (liftMachExecution_worldEq_of_ok (core := Mach.pushItem x c) h).getCode a |>.symm

lemma applyUnary_getCode_eq {f : B256 → B256} {cost devm devm'}
    (h : applyUnary f cost devm = .ok devm') (a : Adr) :
    devm'.getCode a = devm.getCode a := by
  exact (liftMachExecution_worldEq_of_ok (core := Mach.applyUnary f cost) h).getCode a |>.symm

lemma applyBinary_getCode_eq {f : B256 → B256 → B256} {cost devm devm'}
    (h : applyBinary f cost devm = .ok devm') (a : Adr) :
    devm'.getCode a = devm.getCode a := by
  exact (liftMachExecution_worldEq_of_ok (core := Mach.applyBinary f cost) h).getCode a |>.symm

lemma getBal_eq_of_bind {α ε} {ma : Except ε α} {f : α → Except ε Devm}
    {devm devm' : Devm} {a : Adr}
    (run : (ma >>= f) = .ok devm')
    (getDevm : α → Devm)
    (h_first : ∀ v, ma = .ok v → (getDevm v).getBal a = devm.getBal a)
    (h_rest : ∀ v, ma = .ok v → f v = .ok devm' → devm'.getBal a = (getDevm v).getBal a) :
    devm'.getBal a = devm.getBal a := by
  rcases of_bind_eq_ok run with ⟨v, hm, hf⟩
  rw [h_rest v hm hf, h_first v hm]

lemma Devm.pop_getBal_eq {x devm devm'} (h : Devm.pop devm = .ok ⟨x, devm'⟩) (a : Adr) : devm'.getBal a = devm.getBal a := by
  exact (Devm.pop_worldEq_of_ok h).getBal a |>.symm

lemma chargeGas_getBal_eq {cost devm devm'} (h : chargeGas cost devm = .ok devm') (a : Adr) : devm'.getBal a = devm.getBal a := by
  exact (chargeGas_worldEq_of_ok h).getBal a |>.symm

lemma Devm.push_getBal_eq {v devm devm'} (h : Devm.push v devm = .ok devm') (a : Adr) : devm'.getBal a = devm.getBal a := by
  exact (liftMachExecution_worldEq_of_ok (core := Mach.push v) h).getBal a |>.symm

lemma Devm.popToAdr_getBal_eq {devm devm' adr} (h : Devm.popToAdr devm = .ok ⟨adr, devm'⟩) (a : Adr) : devm'.getBal a = devm.getBal a := by
  exact (liftMach_worldEq_of_ok (core := Mach.popToAdr) h).getBal a |>.symm

lemma Devm.popToNat_getBal_eq {devm devm' n} (h : Devm.popToNat devm = .ok ⟨n, devm'⟩) (a : Adr) : devm'.getBal a = devm.getBal a := by
  exact (Devm.popToNat_worldEq_of_ok h).getBal a |>.symm


lemma pushItem_getBal_eq {x c devm devm'} (h : pushItem x c devm = .ok devm') (a : Adr) : devm'.getBal a = devm.getBal a := by
  exact (liftMachExecution_worldEq_of_ok (core := Mach.pushItem x c) h).getBal a |>.symm

lemma applyBinary_getBal_eq {f : B256 → B256 → B256} {cost devm devm'}
    (h : applyBinary f cost devm = .ok devm') :
    devm.getBal = devm'.getBal := by
  funext a
  exact (liftMachExecution_worldEq_of_ok (core := Mach.applyBinary f cost) h).getBal a

lemma applyUnary_getBal_eq {f : B256 → B256} {cost devm devm'}
    (h : applyUnary f cost devm = .ok devm') :
    devm.getBal = devm'.getBal := by
  funext a
  exact (liftMachExecution_worldEq_of_ok (core := Mach.applyUnary f cost) h).getBal a

lemma applyTernary_getBal_eq {f : B256 → B256 → B256 → B256} {cost devm devm'}
    (h : applyTernary f cost devm = .ok devm') :
    devm.getBal = devm'.getBal := by
  funext a
  exact (liftMachExecution_worldEq_of_ok (core := Mach.applyTernary f cost) h).getBal a


def Devm.getStor (devm : Devm) (adr : Adr) : Stor :=
  (devm.getAcct adr).stor

lemma Devm.WorldEq.getStor {d d' : Devm} (h : Devm.WorldEq d d') (a : Adr) :
    d.getStor a = d'.getStor a := by
  unfold Devm.getStor Devm.getAcct
  rw [h.1]

lemma Devm.Burn.getStor {s s' : Devm} (h : Devm.Burn s s') (a : Adr) : s'.getStor a = s.getStor a := by
  simp [Devm.getStor, Devm.getAcct]; rw [h.state]

lemma Devm.PopBurn.getStor {xs} {s s' : Devm} (h : Devm.PopBurn xs s s') (a : Adr) : s'.getStor a = s.getStor a := by
  simp [Devm.getStor, Devm.getAcct]; rw [h.state]

instance : PopBurn.Inv Devm.getStor := ⟨by
  intros xs s s' h
  funext a
  exact (Devm.PopBurn.getStor h a).symm
⟩

instance : Burn.Inv Devm.getStor := ⟨by
  intros s s' h
  funext a
  exact (Devm.Burn.getStor h a).symm
⟩

lemma addAccessedAddress_getStor {devm : Devm} {adr : Adr} :
    (addAccessedAddress devm adr).getStor = devm.getStor := by
  funext a
  exact (addAccessedAddress_worldEq devm adr).getStor a |>.symm

lemma addAccessedStorageKey_getStor {devm : Devm} {adr : Adr} {key : B256} :
    (addAccessedStorageKey devm adr key).getStor = devm.getStor := by
  funext a
  exact (addAccessedStorageKey_worldEq devm adr key).getStor a |>.symm

lemma getStor_eq_of_bind {α ε} {ma : Except ε α} {f : α → Except ε Devm}
    {devm devm' : Devm}
    (run : (ma >>= f) = .ok devm')
    (getDevm : α → Devm)
    (h_first : ∀ v, ma = .ok v → devm.getStor = (getDevm v).getStor)
    (h_rest : ∀ v, ma = .ok v → f v = .ok devm' → (getDevm v).getStor = devm'.getStor) :
    devm.getStor = devm'.getStor := by
  rcases of_bind_eq_ok run with ⟨v, hm, hf⟩
  rw [h_first v hm, h_rest v hm hf]

lemma Devm.pop_getStor_eq {x devm devm'} (h : Devm.pop devm = .ok ⟨x, devm'⟩) : devm.getStor = devm'.getStor := by
  funext a
  exact (Devm.pop_worldEq_of_ok h).getStor a

lemma chargeGas_getStor_eq {cost devm devm'} (h : chargeGas cost devm = .ok devm') : devm.getStor = devm'.getStor := by
  funext a
  exact (chargeGas_worldEq_of_ok h).getStor a

lemma Devm.push_getStor_eq {v devm devm'} (h : Devm.push v devm = .ok devm') : devm.getStor = devm'.getStor := by
  funext a
  exact (liftMachExecution_worldEq_of_ok (core := Mach.push v) h).getStor a

lemma Devm.popToAdr_getStor_eq {devm devm' adr} (h : Devm.popToAdr devm = .ok ⟨adr, devm'⟩) : devm.getStor = devm'.getStor := by
  funext a
  exact (liftMach_worldEq_of_ok (core := Mach.popToAdr) h).getStor a

lemma Devm.popToNat_getStor_eq {devm devm' n} (h : Devm.popToNat devm = .ok ⟨n, devm'⟩) : devm.getStor = devm'.getStor := by
  funext a
  exact (Devm.popToNat_worldEq_of_ok h).getStor a

lemma pushItem_getStor_eq {x c devm devm'} (h : pushItem x c devm = .ok devm') : devm.getStor = devm'.getStor := by
  funext a
  exact (liftMachExecution_worldEq_of_ok (core := Mach.pushItem x c) h).getStor a

lemma applyBinary_getStor_eq {f : B256 → B256 → B256} {cost devm devm'}
    (h : applyBinary f cost devm = .ok devm') :
    devm.getStor = devm'.getStor := by
  funext a
  exact (liftMachExecution_worldEq_of_ok (core := Mach.applyBinary f cost) h).getStor a

lemma applyUnary_getStor_eq {f : B256 → B256} {cost devm devm'}
    (h : applyUnary f cost devm = .ok devm') :
    devm.getStor = devm'.getStor := by
  funext a
  exact (liftMachExecution_worldEq_of_ok (core := Mach.applyUnary f cost) h).getStor a

lemma applyTernary_getStor_eq {f : B256 → B256 → B256 → B256} {cost devm devm'}
    (h : applyTernary f cost devm = .ok devm') :
    devm.getStor = devm'.getStor := by
  funext a
  exact (liftMachExecution_worldEq_of_ok (core := Mach.applyTernary f cost) h).getStor a

lemma applyTernary_getCode_eq {f : B256 → B256 → B256 → B256} {cost devm devm'}
    (h : applyTernary f cost devm = .ok devm') (a : Adr) :
    devm'.getCode a = devm.getCode a := by
  exact (liftMachExecution_worldEq_of_ok (core := Mach.applyTernary f cost) h).getCode a |>.symm

lemma setStorVal_inv_getCode {devm : Devm} {adr adr'} {key} {val} :
    (devm.setStorVal adr key val).getCode adr' = devm.getCode adr' := by
  simp [Devm.getCode, Devm.getAcct, Devm.setStorVal]
  unfold State.setStorVal State.get State.set
  dsimp
  split_ifs with h_if
  · by_cases h_cmp : compare adr adr' = Ordering.eq
    · have h : adr = adr' := compare_eq_iff_eq.mp h_cmp
      subst h
      rw [Std.TreeMap.getD_erase]
      simp
      have h2 := congrArg Acct.code h_if
      exact h2.symm
    · rw [Std.TreeMap.getD_erase]
      simp [h_cmp]
  · by_cases h_cmp : compare adr adr' = Ordering.eq
    · have h : adr = adr' := compare_eq_iff_eq.mp h_cmp
      subst h
      rw [Std.TreeMap.getD_insert]
      simp
    · rw [Std.TreeMap.getD_insert]
      simp [h_cmp]

lemma setStorVal_inv_getBal {devm : Devm} {adr adr'} {key} {val} :
    (devm.setStorVal adr key val).getBal adr' = devm.getBal adr' := by
  simp [Devm.getBal, Devm.getAcct, Devm.setStorVal]
  unfold State.setStorVal State.get State.set
  dsimp
  split_ifs with h_if
  · by_cases h_cmp : compare adr adr' = Ordering.eq
    · have h : adr = adr' := compare_eq_iff_eq.mp h_cmp
      subst h
      rw [Std.TreeMap.getD_erase]
      simp
      have h2 := congrArg Acct.bal h_if
      exact h2.symm
    · rw [Std.TreeMap.getD_erase]
      simp [h_cmp]
  · by_cases h_cmp : compare adr adr' = Ordering.eq
    · have h : adr = adr' := compare_eq_iff_eq.mp h_cmp
      subst h
      rw [Std.TreeMap.getD_insert]
      simp
    · rw [Std.TreeMap.getD_insert]
      simp [h_cmp]

lemma sstore_inv_getBal
    {pc sevm devm devm'}
    (run : Rinst.run ⟨pc, sevm, devm⟩ .sstore = .ok devm') (a : Adr) :
    devm'.getBal a = devm.getBal a := by
  simp only [Rinst.run, Rinst.runCore] at run
  refine getBal_eq_of_bind run Prod.snd ?_ ?_
  {intro ⟨x, devm1⟩ hp; exact Devm.pop_getBal_eq hp a}
  clear run
  intro ⟨x, devm1⟩ hp run;
  refine getBal_eq_of_bind run Prod.snd ?_ ?_
  {intro ⟨x, devm1⟩ hp; exact Devm.pop_getBal_eq hp a}
  clear run
  intro ⟨y, devm2⟩ hp run;
  rcases of_bind_eq_ok run with ⟨⟨_⟩, _, run'⟩
  clear run
  refine getBal_eq_of_bind run' Prod.fst ?_ ?_
  · clear run';
    intro ⟨devm', _⟩
    simp only [ite_not, Except.ok.injEq]
    split
    · intro eq; injection eq with eq _; rw [eq]
    · simp [addAccessedStorageKey_def, Devm.withAccessedStorageKeys]
      intro rw _; rw [← rw]; clear rw
      simp [Devm.getBal, Devm.getAcct]
  · clear run';
    intro ⟨devm3, _⟩ eq run; clear eq
    rcases of_bind_eq_ok run with ⟨_, bar, run'⟩;
    clear bar run
    simp only at run'
    refine getBal_eq_of_bind run' id ?_ ?_
    · clear run'
      intro devm4 eq
      injection eq with rw
      rw [← rw]
      simp [Devm.getBal, Devm.getAcct]
    · clear run'
      intro devm4 temp run; clear temp
      refine getBal_eq_of_bind run id ?_ ?_
      {intro devm5 hc; exact chargeGas_getBal_eq hc a}
      clear run
      intro devm5 eq run
      rcases of_bind_eq_ok run with ⟨_, bar, run'⟩;
      clear bar run; injection run' with rw
      rw [← rw]
      apply setStorVal_inv_getBal


lemma sstore_inv_getCode
    {pc sevm devm devm'}
    (run : Rinst.run ⟨pc, sevm, devm⟩ .sstore = .ok devm') (a : Adr) :
    devm'.getCode a = devm.getCode a := by
  simp only [Rinst.run, Rinst.runCore] at run
  refine getCode_eq_of_bind run Prod.snd ?_ ?_
  {intro ⟨x, devm1⟩ hp; exact Devm.pop_getCode_eq hp a}
  clear run
  intro ⟨x, devm1⟩ hp run;
  refine getCode_eq_of_bind run Prod.snd ?_ ?_
  {intro ⟨x, devm1⟩ hp; exact Devm.pop_getCode_eq hp a}
  clear run
  intro ⟨y, devm2⟩ hp run;
  rcases of_bind_eq_ok run with ⟨⟨_⟩, _, run'⟩
  clear run
  refine getCode_eq_of_bind run' Prod.fst ?_ ?_
  · clear run';
    intro ⟨devm', _⟩
    simp only [ite_not, Except.ok.injEq]
    split
    · intro eq; injection eq with eq _; rw [eq]
    · simp [addAccessedStorageKey_def, Devm.withAccessedStorageKeys]
      intro rw _; rw [← rw]; clear rw
      simp [Devm.getCode, Devm.getAcct]
  · clear run';
    intro ⟨devm3, _⟩ eq run; clear eq
    rcases of_bind_eq_ok run with ⟨_, bar, run'⟩;
    clear bar run
    simp only at run'
    refine getCode_eq_of_bind run' id ?_ ?_
    · clear run'
      intro devm4 eq
      injection eq with rw
      rw [← rw]
      simp [Devm.getCode, Devm.getAcct]
    · clear run'
      intro devm4 temp run; clear temp
      refine getCode_eq_of_bind run id ?_ ?_
      {intro devm5 hc; exact chargeGas_getCode_eq hc a}
      clear run
      intro devm5 eq run
      rcases of_bind_eq_ok run with ⟨_, bar, run'⟩;
      clear bar run; injection run' with rw
      rw [← rw]
      apply setStorVal_inv_getCode

lemma Devm.popN_getCode_eq {n : Nat} {devm devm' : Devm} {l : List B256}
    (hp : devm.popN n = Except.ok (l, devm')) (a : Adr) :
    devm'.getCode a = devm.getCode a := by
  exact (liftMach_worldEq_of_ok (core := (Mach.popN · n)) hp).getCode a |>.symm

/-! ## 1. Generic compositional relations -/

namespace CEffect

abbrev Rel (σ : Type) := σ → σ → Prop

def Refines {σ : Type} (R S : Rel σ) : Prop :=
  ∀ ⦃s t⦄, R s t → S s t

def Comp {σ : Type} (R S : Rel σ) : Rel σ :=
  fun s u => ∃ t, R s t ∧ S t u

def Holds {σ : Type} (run effect : Rel σ) : Prop :=
  Refines run effect

def ObsEq {σ α : Type} (obs : σ → α) : Rel σ :=
  fun s t => obs s = obs t

def Stable {σ α : Type} (obs : σ → α) (effect : Rel σ) : Prop :=
  Refines effect (ObsEq obs)

lemma comp_assoc {σ : Type} (R S T : Rel σ) :
    Comp (Comp R S) T = Comp R (Comp S T) := by
  ext s u
  constructor
  · rintro ⟨b, ⟨a, hRa, hSab⟩, hTbu⟩
    exact ⟨a, hRa, b, hSab, hTbu⟩
  · rintro ⟨a, hRa, b, hSab, hTbu⟩
    exact ⟨b, ⟨a, hRa, hSab⟩, hTbu⟩

lemma holds_comp {σ : Type} {run₁ run₂ R S : Rel σ}
    (hR : Holds run₁ R) (hS : Holds run₂ S) :
    Holds (Comp run₁ run₂) (Comp R S) := by
  rintro s t ⟨u, h1, h2⟩
  exact ⟨u, hR h1, hS h2⟩

lemma holds_weaken {σ : Type} {run R S : Rel σ}
    (h : Holds run R) (hweak : Refines R S) : Holds run S := by
  intro s t hrun
  exact hweak (h hrun)

lemma holds_comp_of_transitive {σ : Type} {run₁ run₂ R : Rel σ}
    (htrans : Transitive R)
    (h₁ : Holds run₁ R) (h₂ : Holds run₂ R) :
    Holds (Comp run₁ run₂) R := by
  intro s u hrun
  rcases hrun with ⟨t, hR1, hR2⟩
  exact htrans (h₁ hR1) (h₂ hR2)

lemma reflTransGen_mono {σ : Type} {step effect : Rel σ} {s t : σ}
    (hrefine : Refines step effect)
    (h : Relation.ReflTransGen step s t) :
    Relation.ReflTransGen effect s t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h1 h2 ih => exact Relation.ReflTransGen.tail ih (hrefine h2)

/-
This is the generic “every small step has `R`, hence the whole run has `R`” theorem.
-/
lemma reflTransGen_collapse {σ : Type} {step R : Rel σ} {s t : σ}
    (hrefl : Reflexive R) (htrans : Transitive R)
    (hrefine : Refines step R)
    (h : Relation.ReflTransGen step s t) : R s t := by
  induction h with
  | refl => exact hrefl _
  | tail h_prev h_step ih => exact htrans ih (hrefine h_step)

lemma obsEq_refl_trans {σ α : Type} (obs : σ → α) :
    Reflexive (ObsEq obs) ∧ Transitive (ObsEq obs) := by
  constructor
  · intro x
    rfl
  · intro x y z hxy hyz
    exact Eq.trans hxy hyz

lemma Stable.comp {σ α β : Type} {obs : σ → α} {R : Rel σ}
    (h : Stable obs R) (f : α → β) : Stable (f ∘ obs) R := by
  intro s t hR; exact congrArg f (h hR)

end CEffect

/-! ## 2. Composing the fieldwise `Devm.Rels` already present in Semantics -/

def Devm.Rels.comp (r s : Devm.Rels) : Devm.Rels :=
  {
    stack := CEffect.Comp r.stack s.stack
    memory := CEffect.Comp r.memory s.memory
    gasLeft := CEffect.Comp r.gasLeft s.gasLeft
    logs := CEffect.Comp r.logs s.logs
    refundCounter := CEffect.Comp r.refundCounter s.refundCounter
    output := CEffect.Comp r.output s.output
    accountsToDelete := CEffect.Comp r.accountsToDelete s.accountsToDelete
    returnData := CEffect.Comp r.returnData s.returnData
    error := CEffect.Comp r.error s.error
    accessedAddresses := CEffect.Comp r.accessedAddresses s.accessedAddresses
    accessedStorageKeys := CEffect.Comp r.accessedStorageKeys s.accessedStorageKeys
    state := CEffect.Comp r.state s.state
    createdAccounts := CEffect.Comp r.createdAccounts s.createdAccounts
    transientStorage := CEffect.Comp r.transientStorage s.transientStorage
  }

def Devm.Rels.Refl (r : Devm.Rels) : Prop :=
  Reflexive r.stack ∧ Reflexive r.memory ∧ Reflexive r.gasLeft ∧
  Reflexive r.logs ∧ Reflexive r.refundCounter ∧ Reflexive r.output ∧
  Reflexive r.accountsToDelete ∧ Reflexive r.returnData ∧ Reflexive r.error ∧
  Reflexive r.accessedAddresses ∧ Reflexive r.accessedStorageKeys ∧
  Reflexive r.state ∧ Reflexive r.createdAccounts ∧
  Reflexive r.transientStorage

def Devm.Rels.Trans (r : Devm.Rels) : Prop :=
  Transitive r.stack ∧ Transitive r.memory ∧ Transitive r.gasLeft ∧
  Transitive r.logs ∧ Transitive r.refundCounter ∧ Transitive r.output ∧
  Transitive r.accountsToDelete ∧ Transitive r.returnData ∧ Transitive r.error ∧
  Transitive r.accessedAddresses ∧ Transitive r.accessedStorageKeys ∧
  Transitive r.state ∧ Transitive r.createdAccounts ∧
  Transitive r.transientStorage

lemma Devm.Rel.comp {r s : Devm.Rels} {a b c : Devm}
    (hab : Devm.Rel r a b) (hbc : Devm.Rel s b c) :
    Devm.Rel (Devm.Rels.comp r s) a c := by
  exact {
    stack := ⟨b.stack, hab.stack, hbc.stack⟩
    memory := ⟨b.memory, hab.memory, hbc.memory⟩
    gasLeft := ⟨b.gasLeft, hab.gasLeft, hbc.gasLeft⟩
    logs := ⟨b.logs, hab.logs, hbc.logs⟩
    refundCounter := ⟨b.refundCounter, hab.refundCounter, hbc.refundCounter⟩
    output := ⟨b.output, hab.output, hbc.output⟩
    accountsToDelete := ⟨b.accountsToDelete, hab.accountsToDelete, hbc.accountsToDelete⟩
    returnData := ⟨b.returnData, hab.returnData, hbc.returnData⟩
    error := ⟨b.error, hab.error, hbc.error⟩
    accessedAddresses := ⟨b.accessedAddresses, hab.accessedAddresses, hbc.accessedAddresses⟩
    accessedStorageKeys := ⟨b.accessedStorageKeys, hab.accessedStorageKeys, hbc.accessedStorageKeys⟩
    state := ⟨b.state, hab.state, hbc.state⟩
    createdAccounts := ⟨b.createdAccounts, hab.createdAccounts, hbc.createdAccounts⟩
    transientStorage := ⟨b.transientStorage, hab.transientStorage, hbc.transientStorage⟩
  }

lemma Devm.rel_refl {r : Devm.Rels} (hr : Devm.Rels.Refl r) :
    Reflexive (Devm.Rel r) := by
  intro d
  rcases hr with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  constructor
  · exact h1 _
  · exact h2 _
  · exact h3 _
  · exact h4 _
  · exact h5 _
  · exact h6 _
  · exact h7 _
  · exact h8 _
  · exact h9 _
  · exact h10 _
  · exact h11 _
  · exact h12 _
  · exact h13 _
  · exact h14 _

lemma Devm.rel_trans {r : Devm.Rels} (hr : Devm.Rels.Trans r) :
    Transitive (Devm.Rel r) := by
  intro a b c hab hbc
  constructor
  · exact hr.1 hab.stack hbc.stack
  · exact hr.2.1 hab.memory hbc.memory
  · exact hr.2.2.1 hab.gasLeft hbc.gasLeft
  · exact hr.2.2.2.1 hab.logs hbc.logs
  · exact hr.2.2.2.2.1 hab.refundCounter hbc.refundCounter
  · exact hr.2.2.2.2.2.1 hab.output hbc.output
  · exact hr.2.2.2.2.2.2.1 hab.accountsToDelete hbc.accountsToDelete
  · exact hr.2.2.2.2.2.2.2.1 hab.returnData hbc.returnData
  · exact hr.2.2.2.2.2.2.2.2.1 hab.error hbc.error
  · exact hr.2.2.2.2.2.2.2.2.2.1 hab.accessedAddresses hbc.accessedAddresses
  · exact hr.2.2.2.2.2.2.2.2.2.2.1 hab.accessedStorageKeys hbc.accessedStorageKeys
  · exact hr.2.2.2.2.2.2.2.2.2.2.2.1 hab.state hbc.state
  · exact hr.2.2.2.2.2.2.2.2.2.2.2.2.1 hab.createdAccounts hbc.createdAccounts
  · exact hr.2.2.2.2.2.2.2.2.2.2.2.2.2 hab.transientStorage hbc.transientStorage

def Devm.OnlyGas : Devm → Devm → Prop :=
  Devm.Rel { Devm.Rels.eq with gasLeft := fun _ _ => True }

lemma Devm.onlyGas_stable_state :
    CEffect.Stable Devm.state Devm.OnlyGas := by
  intro x y h
  exact h.state

/-! ## 3. Outcome-aware effects for the EVM semantic layers -/

namespace Outcome

def Rel {σ ε α : Type}
    (errState : ε → σ) (okState : α → σ)
    (R : σ → σ → Prop) (pre : σ) : Except ε α → Prop
  | .error err => R pre (errState err)
  | .ok value => R pre (okState value)

/-
This is the generic weakening rule for both success and error outcomes.
-/
lemma Rel.mono {σ ε α : Type}
    {errState : ε → σ} {okState : α → σ} {R S : σ → σ → Prop}
    {pre : σ} {out : Except ε α}
    (hrefine : CEffect.Refines R S)
    (h : Rel errState okState R pre out) :
    Rel errState okState S pre out := by
  cases out <;> exact hrefine h

end Outcome

def Execution.Rel (R : Devm → Devm → Prop) (pre : Devm) (out : Execution) : Prop :=
  Outcome.Rel Prod.snd id R pre out

lemma outcomeRel_toExecution {R : Devm → Devm → Prop} {pre : Devm}
    {out : Except (String × Devm) (Unit × Devm)}
    (h : Outcome.Rel Prod.snd Prod.snd R pre out) :
    Execution.Rel R pre (Footprint.toExecution out) := by
  cases out <;> exact h

-- The full-frame infrastructure and master regular-instruction theorem are
-- declared here so that the legacy observation lemmas below can be stated as
-- projections of them.

-- Paired projection of the two deletion-relevant sets
def Devm.delSets (d : Devm) : AdrSet × AdrSet :=
  (d.accountsToDelete, d.createdAccounts)


/-! ## Full-frame relations for instruction preservation -/

/-- A Mach-only step may change exactly the three `Mach` fields. -/
def Devm.Rels.machFrame : Devm.Rels :=
  { Devm.Rels.eq with
    stack := fun _ _ => True
    memory := fun _ _ => True
    gasLeft := fun _ _ => True }

/-- A regular instruction may change every field except the world and the two
    deletion-relevant sets. -/
def Devm.Rels.instructionFrame : Devm.Rels :=
  {
    stack := fun _ _ => True
    memory := fun _ _ => True
    gasLeft := fun _ _ => True
    logs := fun _ _ => True
    refundCounter := fun _ _ => True
    output := fun _ _ => True
    accountsToDelete := _root_.Eq
    returnData := fun _ _ => True
    error := fun _ _ => True
    accessedAddresses := fun _ _ => True
    accessedStorageKeys := fun _ _ => True
    state := _root_.Eq
    createdAccounts := _root_.Eq
    transientStorage := _root_.Eq }

abbrev Devm.MachFrame : Devm → Devm → Prop :=
  Devm.Rel Devm.Rels.machFrame

abbrev Devm.InstructionFrame : Devm → Devm → Prop :=
  Devm.Rel Devm.Rels.instructionFrame

/-- The part of `Meta` that an instruction-frame lift must preserve. -/
def Meta.InstructionFrame (a b : Meta) : Prop :=
  a.accountsToDelete = b.accountsToDelete ∧
    a.createdAccounts = b.createdAccounts

lemma Devm.Rels.machFrame_refl : Devm.Rels.Refl Devm.Rels.machFrame := by
  simp [Devm.Rels.Refl, Devm.Rels.machFrame, Devm.Rels.eq, Reflexive]

lemma Devm.Rels.machFrame_trans : Devm.Rels.Trans Devm.Rels.machFrame := by
  simp [Devm.Rels.Trans, Devm.Rels.machFrame, Devm.Rels.eq, Transitive]

lemma Devm.Rels.instructionFrame_refl :
    Devm.Rels.Refl Devm.Rels.instructionFrame := by
  simp [Devm.Rels.Refl, Devm.Rels.instructionFrame, Reflexive]

lemma Devm.Rels.instructionFrame_trans :
    Devm.Rels.Trans Devm.Rels.instructionFrame := by
  simp [Devm.Rels.Trans, Devm.Rels.instructionFrame, Transitive]

lemma Devm.machFrame_refl : Reflexive Devm.MachFrame :=
  Devm.rel_refl Devm.Rels.machFrame_refl

lemma Devm.machFrame_trans : Transitive Devm.MachFrame :=
  Devm.rel_trans Devm.Rels.machFrame_trans

lemma Devm.instructionFrame_refl : Reflexive Devm.InstructionFrame :=
  Devm.rel_refl Devm.Rels.instructionFrame_refl

lemma Devm.instructionFrame_trans : Transitive Devm.InstructionFrame :=
  Devm.rel_trans Devm.Rels.instructionFrame_trans

lemma Devm.machFrame_refines_instructionFrame :
    CEffect.Refines Devm.MachFrame Devm.InstructionFrame := by
  intro d d' h
  exact {
    stack := trivial
    memory := trivial
    gasLeft := trivial
    logs := trivial
    refundCounter := trivial
    output := trivial
    accountsToDelete := h.accountsToDelete
    returnData := trivial
    error := trivial
    accessedAddresses := trivial
    accessedStorageKeys := trivial
    state := h.state
    createdAccounts := h.createdAccounts
    transientStorage := h.transientStorage }

lemma Devm.MachFrame.worldEq {d d' : Devm} (h : Devm.MachFrame d d') :
    Devm.WorldEq d d' :=
  ⟨h.state, h.transientStorage⟩

lemma Devm.MachFrame.getBal {d d' : Devm} (h : Devm.MachFrame d d')
    (a : Adr) : d.getBal a = d'.getBal a :=
  h.worldEq.getBal a

lemma Devm.MachFrame.getStor {d d' : Devm} (h : Devm.MachFrame d d')
    (a : Adr) : d.getStor a = d'.getStor a :=
  h.worldEq.getStor a

lemma Devm.MachFrame.getCode {d d' : Devm} (h : Devm.MachFrame d d')
    (a : Adr) : d.getCode a = d'.getCode a :=
  h.worldEq.getCode a

lemma Devm.MachFrame.delSets {d d' : Devm} (h : Devm.MachFrame d d') :
    d.delSets = d'.delSets :=
  Prod.ext h.accountsToDelete h.createdAccounts

lemma Devm.InstructionFrame.worldEq {d d' : Devm}
    (h : Devm.InstructionFrame d d') : Devm.WorldEq d d' :=
  ⟨h.state, h.transientStorage⟩

lemma Devm.InstructionFrame.getBal {d d' : Devm}
    (h : Devm.InstructionFrame d d') (a : Adr) :
    d.getBal a = d'.getBal a :=
  h.worldEq.getBal a

lemma Devm.InstructionFrame.getStor {d d' : Devm}
    (h : Devm.InstructionFrame d d') (a : Adr) :
    d.getStor a = d'.getStor a :=
  h.worldEq.getStor a

lemma Devm.InstructionFrame.getCode {d d' : Devm}
    (h : Devm.InstructionFrame d d') (a : Adr) :
    d.getCode a = d'.getCode a :=
  h.worldEq.getCode a

lemma Devm.InstructionFrame.delSets {d d' : Devm}
    (h : Devm.InstructionFrame d d') : d.delSets = d'.delSets :=
  Prod.ext h.accountsToDelete h.createdAccounts

lemma Devm.machFrame_setMach (d : Devm) (mach : Mach) :
    Devm.MachFrame d (d.setMach mach) := by
  exact {
    stack := trivial
    memory := trivial
    gasLeft := trivial
    logs := rfl
    refundCounter := rfl
    output := rfl
    accountsToDelete := rfl
    returnData := rfl
    error := rfl
    accessedAddresses := rfl
    accessedStorageKeys := rfl
    state := rfl
    createdAccounts := rfl
    transientStorage := rfl }

lemma Devm.instructionFrame_setMachMeta (d : Devm) (view : Mach × Meta)
    (h : Meta.InstructionFrame d.meta view.2) :
    Devm.InstructionFrame d (d.setMachMeta view) := by
  rcases h with ⟨hdel, hcreated⟩
  exact {
    stack := trivial
    memory := trivial
    gasLeft := trivial
    logs := trivial
    refundCounter := trivial
    output := trivial
    accountsToDelete := hdel
    returnData := trivial
    error := trivial
    accessedAddresses := trivial
    accessedStorageKeys := trivial
    state := rfl
    createdAccounts := hcreated
    transientStorage := rfl }

/-! ### Full-frame lift rules -/

lemma liftMach_machFrame (core : Mach → Footprint.Outcome Mach α) (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.MachFrame d (liftMach core d) := by
  unfold liftMach Footprint.liftOutcome
  cases core d.mach <;> exact Devm.machFrame_setMach d _

lemma liftMachPure_machFrame (core : Mach → Mach) (d : Devm) :
    Devm.MachFrame d (liftMachPure core d) := by
  exact Devm.machFrame_setMach d _

lemma liftMachExecution_machFrame
    (core : Mach → Footprint.Outcome Mach Unit) (d : Devm) :
    Execution.Rel Devm.MachFrame d (liftMachExecution core d) := by
  unfold liftMachExecution
  exact outcomeRel_toExecution (liftMach_machFrame core d)

lemma liftMachMeta_instructionFrame
    (core : Mach → Meta → Footprint.Outcome (Mach × Meta) α) (d : Devm)
    (hcore : Outcome.Rel (fun e => e.2.2) (fun x => x.2.2)
      Meta.InstructionFrame d.meta (core d.mach d.meta)) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame d
      (liftMachMeta core d) := by
  cases h : core d.mach d.meta with
  | error e =>
      rw [h] at hcore
      simpa only [liftMachMeta, Footprint.liftOutcome, h] using
        Devm.instructionFrame_setMachMeta d e.2 hcore
  | ok x =>
      rw [h] at hcore
      simpa only [liftMachMeta, Footprint.liftOutcome, h] using
        Devm.instructionFrame_setMachMeta d x.2 hcore

lemma liftMachMetaPure_instructionFrame
    (core : Mach → Meta → Mach × Meta) (d : Devm)
    (hcore : Meta.InstructionFrame d.meta (core d.mach d.meta).2) :
    Devm.InstructionFrame d (liftMachMetaPure core d) := by
  exact Devm.instructionFrame_setMachMeta d _ hcore

lemma liftMachMetaExecution_instructionFrame
    (core : Mach → Meta → Footprint.Outcome (Mach × Meta) Unit) (d : Devm)
    (hcore : Outcome.Rel (fun e => e.2.2) (fun x => x.2.2)
      Meta.InstructionFrame d.meta (core d.mach d.meta)) :
    Execution.Rel Devm.InstructionFrame d (liftMachMetaExecution core d) := by
  unfold liftMachMetaExecution
  exact outcomeRel_toExecution (liftMachMeta_instructionFrame core d hcore)

lemma liftMachMetaWorld_instructionFrame
    (core : World → Mach → Meta → Footprint.Outcome (Mach × Meta) α)
    (d : Devm)
    (hcore : Outcome.Rel (fun e => e.2.2) (fun x => x.2.2)
      Meta.InstructionFrame d.meta (core d.world d.mach d.meta)) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame d
      (liftMachMetaWorld core d) := by
  exact liftMachMeta_instructionFrame (core d.world) d hcore

lemma liftMachMetaWorldPure_instructionFrame
    (core : World → Mach → Meta → Mach × Meta) (d : Devm)
    (hcore : Meta.InstructionFrame d.meta (core d.world d.mach d.meta).2) :
    Devm.InstructionFrame d (liftMachMetaWorldPure core d) := by
  exact liftMachMetaPure_instructionFrame (core d.world) d hcore

lemma liftMachMetaWorldExecution_instructionFrame
    (core : World → Mach → Meta → Footprint.Outcome (Mach × Meta) Unit)
    (d : Devm)
    (hcore : Outcome.Rel (fun e => e.2.2) (fun x => x.2.2)
      Meta.InstructionFrame d.meta (core d.world d.mach d.meta)) :
    Execution.Rel Devm.InstructionFrame d
      (liftMachMetaWorldExecution core d) := by
  exact liftMachMetaExecution_instructionFrame (core d.world) d hcore

/-! ### Full-frame primitive facts -/

lemma Devm.pop_machFrame (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.MachFrame d (Devm.pop d) := by
  exact liftMach_machFrame Mach.pop d

lemma Devm.pop_instructionFrame (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame d (Devm.pop d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (Devm.pop_machFrame d)

lemma Devm.push_machFrame (x : B256) (d : Devm) :
    Execution.Rel Devm.MachFrame d (Devm.push x d) := by
  exact liftMachExecution_machFrame (Mach.push x) d

lemma Devm.push_instructionFrame (x : B256) (d : Devm) :
    Execution.Rel Devm.InstructionFrame d (Devm.push x d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (Devm.push_machFrame x d)

lemma pushItem_machFrame (x : B256) (cost : Nat) (d : Devm) :
    Execution.Rel Devm.MachFrame d (pushItem x cost d) := by
  exact liftMachExecution_machFrame (Mach.pushItem x cost) d

lemma pushItem_instructionFrame (x : B256) (cost : Nat) (d : Devm) :
    Execution.Rel Devm.InstructionFrame d (pushItem x cost d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (pushItem_machFrame x cost d)

lemma chargeGas_machFrame (cost : Nat) (d : Devm) :
    Execution.Rel Devm.MachFrame d (chargeGas cost d) := by
  exact liftMachExecution_machFrame (Mach.chargeGas cost) d

lemma chargeGas_instructionFrame (cost : Nat) (d : Devm) :
    Execution.Rel Devm.InstructionFrame d (chargeGas cost d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (chargeGas_machFrame cost d)

lemma Devm.popToNat_machFrame (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.MachFrame d (Devm.popToNat d) := by
  exact liftMach_machFrame Mach.popToNat d

lemma Devm.popToNat_instructionFrame (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame d (Devm.popToNat d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (Devm.popToNat_machFrame d)

lemma Devm.popToAdr_machFrame (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.MachFrame d (Devm.popToAdr d) := by
  exact liftMach_machFrame Mach.popToAdr d

lemma Devm.popToAdr_instructionFrame (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame d (Devm.popToAdr d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (Devm.popToAdr_machFrame d)

lemma Devm.popN_machFrame (d : Devm) (n : Nat) :
    Outcome.Rel Prod.snd Prod.snd Devm.MachFrame d (Devm.popN d n) := by
  exact liftMach_machFrame (Mach.popN · n) d

lemma Devm.popN_instructionFrame (d : Devm) (n : Nat) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame d (Devm.popN d n) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (Devm.popN_machFrame d n)

lemma applyUnary_machFrame (f : B256 → B256) (cost : Nat) (d : Devm) :
    Execution.Rel Devm.MachFrame d (applyUnary f cost d) := by
  exact liftMachExecution_machFrame (Mach.applyUnary f cost) d

lemma applyUnary_instructionFrame (f : B256 → B256) (cost : Nat) (d : Devm) :
    Execution.Rel Devm.InstructionFrame d (applyUnary f cost d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (applyUnary_machFrame f cost d)

lemma applyBinary_machFrame (f : B256 → B256 → B256)
    (cost : Nat) (d : Devm) :
    Execution.Rel Devm.MachFrame d (applyBinary f cost d) := by
  exact liftMachExecution_machFrame (Mach.applyBinary f cost) d

lemma applyBinary_instructionFrame (f : B256 → B256 → B256)
    (cost : Nat) (d : Devm) :
    Execution.Rel Devm.InstructionFrame d (applyBinary f cost d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (applyBinary_machFrame f cost d)

lemma applyTernary_machFrame (f : B256 → B256 → B256 → B256)
    (cost : Nat) (d : Devm) :
    Execution.Rel Devm.MachFrame d (applyTernary f cost d) := by
  exact liftMachExecution_machFrame (Mach.applyTernary f cost) d

lemma applyTernary_instructionFrame (f : B256 → B256 → B256 → B256)
    (cost : Nat) (d : Devm) :
    Execution.Rel Devm.InstructionFrame d (applyTernary f cost d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (applyTernary_machFrame f cost d)

lemma Devm.memWrite_machFrame (d : Devm) (idx : Nat) (val : B8L) :
    Devm.MachFrame d (Devm.memWrite d idx val) := by
  exact liftMachPure_machFrame (Mach.memWrite · idx val) d

lemma Devm.memWrite_instructionFrame (d : Devm) (idx : Nat) (val : B8L) :
    Devm.InstructionFrame d (Devm.memWrite d idx val) := by
  exact Devm.machFrame_refines_instructionFrame
    (Devm.memWrite_machFrame d idx val)

lemma Devm.memExtends_machFrame (d : Devm) (ranges : List (Nat × Nat)) :
    Devm.MachFrame d (Devm.memExtends d ranges) := by
  exact liftMachPure_machFrame (Mach.memExtends · ranges) d

lemma Devm.memExtends_instructionFrame (d : Devm)
    (ranges : List (Nat × Nat)) :
    Devm.InstructionFrame d (Devm.memExtends d ranges) := by
  exact Devm.machFrame_refines_instructionFrame
    (Devm.memExtends_machFrame d ranges)

lemma addAccessedAddress_instructionFrame (d : Devm) (a : Adr) :
    Devm.InstructionFrame d (addAccessedAddress d a) := by
  exact liftMachMetaPure_instructionFrame _ d ⟨rfl, rfl⟩

lemma addAccessedStorageKey_instructionFrame
    (d : Devm) (a : Adr) (k : B256) :
    Devm.InstructionFrame d (addAccessedStorageKey d a k) := by
  exact liftMachMetaPure_instructionFrame _ d ⟨rfl, rfl⟩

lemma Devm.addLog_instructionFrame (d : Devm) (log : Log) :
    Devm.InstructionFrame d (Devm.addLog d log) := by
  exact liftMachMetaPure_instructionFrame _ d ⟨rfl, rfl⟩

lemma Devm.memRead_instructionFrame (d : Devm) (index size : Nat) :
    Devm.InstructionFrame d (Devm.memRead d index size).2 := by
  unfold Devm.memRead
  split
  exact {
    stack := trivial
    memory := trivial
    gasLeft := trivial
    logs := trivial
    refundCounter := trivial
    output := trivial
    accountsToDelete := rfl
    returnData := trivial
    error := trivial
    accessedAddresses := trivial
    accessedStorageKeys := trivial
    state := rfl
    createdAccounts := rfl
    transientStorage := rfl }

lemma Rinst.balanceCore_meta_instructionFrame
    (world : World) (mach : Mach) (view : Meta) :
    Outcome.Rel (fun e => e.2.2) (fun x => x.2.2)
      Meta.InstructionFrame view (Rinst.balanceCore world mach view) := by
  cases hpop : mach.pop with
  | error e =>
      simp only [Rinst.balanceCore, hpop]
      exact ⟨rfl, rfl⟩
  | ok out =>
      rcases out with ⟨x, mach'⟩
      simp only [Rinst.balanceCore, hpop]
      by_cases hw : x.toAdr ∈ view.accessedAddresses
      · simp only [hw, if_pos]
        split
        · exact ⟨rfl, rfl⟩
        · split <;> exact ⟨rfl, rfl⟩
      · simp only [hw, if_false]
        split
        · exact ⟨rfl, rfl⟩
        · split <;> exact ⟨rfl, rfl⟩

lemma Rinst.balanceCore_instructionFrame (d : Devm) :
    Execution.Rel Devm.InstructionFrame d
      (liftMachMetaWorldExecution Rinst.balanceCore d) := by
  exact liftMachMetaWorldExecution_instructionFrame Rinst.balanceCore d
    (Rinst.balanceCore_meta_instructionFrame d.world d.mach d.meta)

/-! ### Bind composition for frame relations -/

lemma Outcome.Rel.pure
    {R : Devm → Devm → Prop} (hrefl : Reflexive R) (x : α) (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd R d
      (.ok (x, d) : Except (String × Devm) (α × Devm)) :=
  hrefl d

lemma Execution.Rel.pure
    {R : Devm → Devm → Prop} (hrefl : Reflexive R) (d : Devm) :
    Execution.Rel R d (.ok d) :=
  hrefl d

lemma Outcome.Rel.bind
    {R : Devm → Devm → Prop} (htrans : Transitive R)
    {pre : Devm} {out : Except (String × Devm) (α × Devm)}
    {next : α → Devm → Except (String × Devm) (β × Devm)}
    (hout : Outcome.Rel Prod.snd Prod.snd R pre out)
    (hnext : ∀ x d, Outcome.Rel Prod.snd Prod.snd R d (next x d)) :
    Outcome.Rel Prod.snd Prod.snd R pre
      (out >>= fun x => next x.1 x.2) := by
  cases out with
  | error e => exact hout
  | ok x =>
      cases hn : next x.1 x.2 with
      | error e =>
          have h := hnext x.1 x.2
          rw [hn] at h
          simpa only [Except.bind_ok, hn] using htrans hout h
      | ok y =>
          have h := hnext x.1 x.2
          rw [hn] at h
          simpa only [Except.bind_ok, hn] using htrans hout h

lemma Outcome.Rel.bindExecution
    {R : Devm → Devm → Prop} (htrans : Transitive R)
    {pre : Devm} {out : Except (String × Devm) (α × Devm)}
    {next : α → Devm → Execution}
    (hout : Outcome.Rel Prod.snd Prod.snd R pre out)
    (hnext : ∀ x d, Execution.Rel R d (next x d)) :
    Execution.Rel R pre (out >>= fun x => next x.1 x.2) := by
  cases out with
  | error e => exact hout
  | ok x =>
      cases hn : next x.1 x.2 with
      | error e =>
          have h := hnext x.1 x.2
          rw [hn] at h
          simpa only [Except.bind_ok, hn] using htrans hout h
      | ok d =>
          have h := hnext x.1 x.2
          rw [hn] at h
          simpa only [Except.bind_ok, hn, id_eq] using htrans hout h

lemma Execution.Rel.bind
    {R : Devm → Devm → Prop} (htrans : Transitive R)
    {pre : Devm} {out : Execution} {next : Devm → Execution}
    (hout : Execution.Rel R pre out)
    (hnext : ∀ d, Execution.Rel R d (next d)) :
    Execution.Rel R pre (out >>= next) := by
  cases out with
  | error e => exact hout
  | ok d =>
      cases hn : next d with
      | error e =>
          have h := hnext d
          rw [hn] at h
          simpa only [Except.bind_ok, hn] using htrans hout h
      | ok d' =>
          have h := hnext d
          rw [hn] at h
          simpa only [Except.bind_ok, hn, id_eq] using htrans hout h

lemma Execution.Rel.bindOutcome
    {R : Devm → Devm → Prop} (htrans : Transitive R)
    {pre : Devm} {out : Execution}
    {next : Devm → Except (String × Devm) (α × Devm)}
    (hout : Execution.Rel R pre out)
    (hnext : ∀ d, Outcome.Rel Prod.snd Prod.snd R d (next d)) :
    Outcome.Rel Prod.snd Prod.snd R pre (out >>= next) := by
  cases out with
  | error e => exact hout
  | ok d =>
      cases hn : next d with
      | error e =>
          have h := hnext d
          rw [hn] at h
          simpa only [Except.bind_ok, hn] using htrans hout h
      | ok x =>
          have h := hnext d
          rw [hn] at h
          simpa only [Except.bind_ok, hn] using htrans hout h

/-! ### Step 3 calibration cases -/

lemma Rinst.balance_runCore_instructionFrame
    (pc : Nat) (devm : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame devm
      (Rinst.runCore pc devm sevm .balance) := by
  simpa only [Rinst.runCore] using Rinst.balanceCore_instructionFrame devm

lemma Rinst.blobhash_runCore_instructionFrame
    (pc : Nat) (devm : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame devm
      (Rinst.runCore pc devm sevm .blobhash) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.pop_instructionFrame devm) (next := fun x d =>
      chargeGas gHashopcode d >>=
        Devm.push (sevm.tenvStat.blobVersionedHashes.getD x.toNat 0)) ?_
  intro x d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame gHashopcode d)
  exact Devm.push_instructionFrame _

/-! ## Master regular-instruction frame theorem -/

/-- Equality of the balance/code observations of two world states.  Storage is
    deliberately absent: it is the component written by `SSTORE`. -/
def State.BalCodeEq (a b : _root_.State) : Prop :=
  (fun adr => ((a.get adr).bal, (a.get adr).code)) =
    fun adr => ((b.get adr).bal, (b.get adr).code)

/-- `SSTORE` may change storage in `state`, but preserves balances, code, and
    the other world/frame fields. -/
def Devm.Rels.stateWriteFrame : Devm.Rels :=
  { Devm.Rels.instructionFrame with state := State.BalCodeEq }

/-- `TSTORE` may change `transientStorage`, but preserves the other
    world/frame fields. -/
def Devm.Rels.transientWriteFrame : Devm.Rels :=
  { Devm.Rels.instructionFrame with transientStorage := fun _ _ => True }

abbrev Devm.StateWriteFrame : Devm → Devm → Prop :=
  Devm.Rel Devm.Rels.stateWriteFrame

abbrev Devm.TransientWriteFrame : Devm → Devm → Prop :=
  Devm.Rel Devm.Rels.transientWriteFrame

lemma Devm.Rels.stateWriteFrame_refl :
    Devm.Rels.Refl Devm.Rels.stateWriteFrame := by
  simp [Devm.Rels.Refl, Devm.Rels.stateWriteFrame,
    Devm.Rels.instructionFrame, State.BalCodeEq, Reflexive]

lemma Devm.Rels.stateWriteFrame_trans :
    Devm.Rels.Trans Devm.Rels.stateWriteFrame := by
  simp_all [Devm.Rels.Trans, Devm.Rels.stateWriteFrame,
    Devm.Rels.instructionFrame, State.BalCodeEq, Transitive]

lemma Devm.Rels.transientWriteFrame_refl :
    Devm.Rels.Refl Devm.Rels.transientWriteFrame := by
  simp [Devm.Rels.Refl, Devm.Rels.transientWriteFrame,
    Devm.Rels.instructionFrame, Reflexive]

lemma Devm.Rels.transientWriteFrame_trans :
    Devm.Rels.Trans Devm.Rels.transientWriteFrame := by
  simp [Devm.Rels.Trans, Devm.Rels.transientWriteFrame,
    Devm.Rels.instructionFrame, Transitive]

lemma Devm.stateWriteFrame_refl : Reflexive Devm.StateWriteFrame :=
  Devm.rel_refl Devm.Rels.stateWriteFrame_refl

lemma Devm.stateWriteFrame_trans : Transitive Devm.StateWriteFrame :=
  Devm.rel_trans Devm.Rels.stateWriteFrame_trans

lemma Devm.transientWriteFrame_refl : Reflexive Devm.TransientWriteFrame :=
  Devm.rel_refl Devm.Rels.transientWriteFrame_refl

lemma Devm.transientWriteFrame_trans : Transitive Devm.TransientWriteFrame :=
  Devm.rel_trans Devm.Rels.transientWriteFrame_trans

lemma Devm.instructionFrame_refines_stateWriteFrame :
    CEffect.Refines Devm.InstructionFrame Devm.StateWriteFrame := by
  intro d d' h
  refine { h with state := ?_ }
  change State.BalCodeEq d.state d'.state
  rw [h.state]
  rfl

lemma Devm.instructionFrame_refines_transientWriteFrame :
    CEffect.Refines Devm.InstructionFrame Devm.TransientWriteFrame := by
  intro d d' h
  exact { h with transientStorage := trivial }

lemma Devm.instructionFrame_of_world_eq {d d' : Devm}
    (hdel : d.accountsToDelete = d'.accountsToDelete)
    (hstate : d.state = d'.state)
    (hcreated : d.createdAccounts = d'.createdAccounts)
    (htransient : d.transientStorage = d'.transientStorage) :
    Devm.InstructionFrame d d' := by
  exact {
    stack := trivial
    memory := trivial
    gasLeft := trivial
    logs := trivial
    refundCounter := trivial
    output := trivial
    accountsToDelete := hdel
    returnData := trivial
    error := trivial
    accessedAddresses := trivial
    accessedStorageKeys := trivial
    state := hstate
    createdAccounts := hcreated
    transientStorage := htransient }

lemma popChargePush_instructionFrame (pre : Devm)
    (cost : B256 → Devm → Nat) (value : B256 → Devm → B256) :
    Execution.Rel Devm.InstructionFrame pre (do
      let ⟨x, d⟩ ← pre.pop
      let d ← chargeGas (cost x d) d
      d.push (value x d)) := by
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.pop_instructionFrame pre) (next := fun x d =>
      chargeGas (cost x d) d >>= fun d => Devm.push (value x d) d) ?_
  intro x d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame (cost x d) d)
  intro d'
  exact Devm.push_instructionFrame (value x d') d'

lemma Execution.Rel.trans_left {R : Devm → Devm → Prop}
    (htrans : Transitive R) {a b : Devm} {out : Execution}
    (hab : R a b) (hout : Execution.Rel R b out) :
    Execution.Rel R a out := by
  cases out <;> exact htrans hab hout

lemma pop2ChargePush_instructionFrame (pre : Devm)
    (cost : B256 → B256 → Devm → Nat)
    (value : B256 → B256 → Devm → B256) :
    Execution.Rel Devm.InstructionFrame pre (do
      let ⟨x, d⟩ ← pre.pop
      let ⟨y, d⟩ ← d.pop
      let d ← chargeGas (cost x y d) d
      d.push (value x y d)) := by
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.pop_instructionFrame pre) (next := fun x d => do
      let ⟨y, d⟩ ← d.pop
      let d ← chargeGas (cost x y d) d
      d.push (value x y d)) ?_
  intro x d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.pop_instructionFrame d) (next := fun y d =>
      chargeGas (cost x y d) d >>= fun d => Devm.push (value x y d) d) ?_
  intro y d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame (cost x y d) d)
  intro d'
  exact Devm.push_instructionFrame (value x y d') d'

lemma Rinst.exp_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .exp) := by
  simpa only [Rinst.runCore] using
    (pop2ChargePush_instructionFrame pre
      (fun _ exponent _ => gExp + gExpbyte * exponent.bytecount)
      (fun base exponent _ => B256.bexp base exponent))

lemma Rinst.calldataload_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .calldataload) := by
  simpa only [Rinst.runCore] using
    (popChargePush_instructionFrame pre (fun _ _ => gVerylow)
      (fun start _ => B8L.toB256 <| sevm.data.sliceD start.toNat 32 0))

lemma Rinst.blockhash_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .blockhash) := by
  simpa only [Rinst.runCore] using
    (popChargePush_instructionFrame pre (fun _ _ => gBlockhash)
      (fun blockNumberWord _ =>
        let blockNumber := blockNumberWord.toNat
        let maxBlockNumber := blockNumber + 256
        if sevm.benvStat.number ≤ blockNumber ∨
            maxBlockNumber < sevm.benvStat.number then 0
        else sevm.benvStat.blockHashes.getD
          (sevm.benvStat.blockHashes.length -
            (sevm.benvStat.number - blockNumber)) 0))

lemma Rinst.gas_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .gas) := by
  simp only [Rinst.runCore]
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame gBase pre)
  intro d
  exact Devm.push_instructionFrame d.gasLeft.toB256 d

lemma Rinst.tload_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .tload) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.pop_instructionFrame pre) (next := fun key d =>
      pushItem (d.getTransVal sevm.currentTarget key) gasWarmAccess d) ?_
  intro key d
  exact pushItem_instructionFrame _ _ d

lemma popNat3ChargePure_instructionFrame (pre : Devm)
    (cost : Nat → Nat → Nat → Devm → Nat)
    (finish : Nat → Nat → Nat → Devm → Devm)
    (hfinish : ∀ x y z d, Devm.InstructionFrame d (finish x y z d)) :
    Execution.Rel Devm.InstructionFrame pre (do
      let ⟨x, d⟩ ← pre.popToNat
      let ⟨y, d⟩ ← d.popToNat
      let ⟨z, d⟩ ← d.popToNat
      let d ← chargeGas (cost x y z d) d
      .ok (finish x y z d)) := by
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame pre) (next := fun x d => do
      let ⟨y, d⟩ ← d.popToNat
      let ⟨z, d⟩ ← d.popToNat
      let d ← chargeGas (cost x y z d) d
      .ok (finish x y z d)) ?_
  intro x d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun y d => do
      let ⟨z, d⟩ ← d.popToNat
      let d ← chargeGas (cost x y z d) d
      .ok (finish x y z d)) ?_
  intro y d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun z d =>
      chargeGas (cost x y z d) d >>= fun d => .ok (finish x y z d)) ?_
  intro z d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame (cost x y z d) d)
  intro d'
  exact hfinish x y z d'

lemma popNatPopChargePure_instructionFrame (pre : Devm)
    (cost : Nat → B256 → Devm → Nat)
    (finish : Nat → B256 → Devm → Devm)
    (hfinish : ∀ x y d, Devm.InstructionFrame d (finish x y d)) :
    Execution.Rel Devm.InstructionFrame pre (do
      let ⟨x, d⟩ ← pre.popToNat
      let ⟨y, d⟩ ← d.pop
      let d ← chargeGas (cost x y d) d
      .ok (finish x y d)) := by
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame pre) (next := fun x d => do
      let ⟨y, d⟩ ← d.pop
      let d ← chargeGas (cost x y d) d
      .ok (finish x y d)) ?_
  intro x d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.pop_instructionFrame d) (next := fun y d =>
      chargeGas (cost x y d) d >>= fun d => .ok (finish x y d)) ?_
  intro y d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame (cost x y d) d)
  intro d'
  exact hfinish x y d'

lemma Rinst.calldatacopy_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .calldatacopy) := by
  simpa only [Rinst.runCore] using
    (popNat3ChargePure_instructionFrame pre
      (fun memoryStart _ size d =>
        gVerylow + gasCopy * ceilDiv size 32 + d.extCost [(memoryStart, size)])
      (fun memoryStart dataStart size d =>
        d.memWrite memoryStart (sevm.data.sliceD dataStart size 0))
      (fun memoryStart dataStart size d =>
        Devm.memWrite_instructionFrame d memoryStart
          (sevm.data.sliceD dataStart size 0)))

lemma Rinst.codecopy_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .codecopy) := by
  simpa only [Rinst.runCore] using
    (popNat3ChargePure_instructionFrame pre
      (fun memoryStart _ size d =>
        gVerylow + gasCopy * ceilDiv size 32 + d.extCost [(memoryStart, size)])
      (fun memoryStart codeStart size d =>
        { d with memory := (d.memory.write memoryStart
          (sevm.code.sliceD codeStart size (Linst.toB8 .stop))) })
      (fun _ _ _ _ => Devm.instructionFrame_of_world_eq rfl rfl rfl rfl))

lemma Rinst.mstore_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .mstore) := by
  simpa only [Rinst.runCore] using
    (popNatPopChargePure_instructionFrame pre
      (fun start _ d => gVerylow + d.extCost [(start, 32)])
      (fun start value d => d.memWrite start value.toB8L)
      (fun start value d =>
        Devm.memWrite_instructionFrame d start value.toB8L))

lemma Rinst.mstore8_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .mstore8) := by
  simpa only [Rinst.runCore] using
    (popNatPopChargePure_instructionFrame pre
      (fun start _ d => gVerylow + d.extCost [(start, 1)])
      (fun start value d => d.memWrite start [value.2.2.toUInt8])
      (fun start value d =>
        Devm.memWrite_instructionFrame d start [value.2.2.toUInt8]))

lemma Rinst.mload_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .mload) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame pre) (next := fun start d =>
      chargeGas (gVerylow + d.extCost [(start, 32)]) d >>= fun d =>
        Devm.push (B8L.toB256 (d.memRead start 32).1) (d.memRead start 32).2) ?_
  intro start d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame _ d)
  intro d'
  exact Execution.Rel.trans_left Devm.instructionFrame_trans
    (Devm.memRead_instructionFrame d' start 32)
    (Devm.push_instructionFrame _ (d'.memRead start 32).2)

lemma Rinst.kec_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .kec) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame pre) (next := fun start d => do
      let ⟨size, d⟩ ← d.popToNat
      let d ← chargeGas
        (gKeccak256 + gasKeccak256Word * ceilDiv size 32 +
          d.extCost [(start, size)]) d
      let ⟨arg, d⟩ := d.memRead start size
      d.push arg.keccak) ?_
  intro start d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun size d =>
      chargeGas
        (gKeccak256 + gasKeccak256Word * ceilDiv size 32 +
          d.extCost [(start, size)]) d >>= fun d =>
        Devm.push (d.memRead start size).1.keccak (d.memRead start size).2) ?_
  intro size d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame _ d)
  intro d'
  exact Execution.Rel.trans_left Devm.instructionFrame_trans
    (Devm.memRead_instructionFrame d' start size)
    (Devm.push_instructionFrame _ (d'.memRead start size).2)

lemma Rinst.mcopy_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .mcopy) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame pre) (next := fun destination d => do
      let ⟨source, d⟩ ← d.popToNat
      let ⟨length, d⟩ ← d.popToNat
      let d ← chargeGas (gVerylow + gasCopy * ceilDiv length 32 +
        d.extCost [(source, length), (destination, length)]) d
      .ok ((d.memRead source length).2.memWrite destination
        (d.memRead source length).1)) ?_
  intro destination d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun source d => do
      let ⟨length, d⟩ ← d.popToNat
      let d ← chargeGas (gVerylow + gasCopy * ceilDiv length 32 +
        d.extCost [(source, length), (destination, length)]) d
      .ok ((d.memRead source length).2.memWrite destination
        (d.memRead source length).1)) ?_
  intro source d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun length d =>
      chargeGas (gVerylow + gasCopy * ceilDiv length 32 +
        d.extCost [(source, length), (destination, length)]) d >>= fun d =>
      .ok ((d.memRead source length).2.memWrite destination
        (d.memRead source length).1)) ?_
  intro length d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame _ d)
  intro d'
  exact Devm.instructionFrame_trans
    (Devm.memRead_instructionFrame d' source length)
    (Devm.memWrite_instructionFrame (d'.memRead source length).2 destination
      (d'.memRead source length).1)

lemma popAdrAccessChargePush_instructionFrame (pre : Devm)
    (value : Adr → Devm → B256) :
    Execution.Rel Devm.InstructionFrame pre (do
      let ⟨a, d⟩ ← pre.popToAdr
      let d ← if a ∈ d.accessedAddresses then chargeGas gasWarmAccess d
        else chargeGas gasColdAccountAccess (addAccessedAddress d a)
      d.push (value a d)) := by
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToAdr_instructionFrame pre) (next := fun a d => do
      let d ← if a ∈ d.accessedAddresses then chargeGas gasWarmAccess d
        else chargeGas gasColdAccountAccess (addAccessedAddress d a)
      d.push (value a d)) ?_
  intro a d
  by_cases h : a ∈ d.accessedAddresses
  · simp only [h, if_pos]
    apply Execution.Rel.bind Devm.instructionFrame_trans
      (chargeGas_instructionFrame gasWarmAccess d)
    intro d'
    exact Devm.push_instructionFrame (value a d') d'
  · simp only [h, if_false]
    apply Execution.Rel.bind Devm.instructionFrame_trans
      (Execution.Rel.trans_left Devm.instructionFrame_trans
        (addAccessedAddress_instructionFrame d a)
        (chargeGas_instructionFrame gasColdAccountAccess
          (addAccessedAddress d a)))
    intro d'
    exact Devm.push_instructionFrame (value a d') d'

lemma Rinst.extcodesize_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .extcodesize) := by
  simpa only [Rinst.runCore] using
    (popAdrAccessChargePush_instructionFrame pre
      (fun a d => (d.getCode a).size.toB256))

lemma Rinst.extcodehash_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .extcodehash) := by
  simpa only [Rinst.runCore] using
    (popAdrAccessChargePush_instructionFrame pre (fun a d =>
      let account := d.getAcct a
      if account.Empty then 0
      else ByteArray.keccak 0 account.code.size account.code))

lemma Rinst.sload_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .sload) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.pop_instructionFrame pre) (next := fun key d =>
      if (sevm.currentTarget, key) ∈ d.accessedStorageKeys then
        chargeGas gasWarmAccess d >>= fun d =>
          Devm.push (d.getStorVal sevm.currentTarget key) d
      else chargeGas gasColdSload
        (addAccessedStorageKey d sevm.currentTarget key) >>= fun d =>
          Devm.push (d.getStorVal sevm.currentTarget key) d) ?_
  intro key d
  by_cases h : (sevm.currentTarget, key) ∈ d.accessedStorageKeys
  · simp only [h, if_pos]
    apply Execution.Rel.bind Devm.instructionFrame_trans
      (chargeGas_instructionFrame gasWarmAccess d)
    intro d'
    exact Devm.push_instructionFrame _ d'
  · simp only [h, if_false]
    apply Execution.Rel.bind Devm.instructionFrame_trans
      (Execution.Rel.trans_left Devm.instructionFrame_trans
        (addAccessedStorageKey_instructionFrame d sevm.currentTarget key)
        (chargeGas_instructionFrame gasColdSload
          (addAccessedStorageKey d sevm.currentTarget key)))
    intro d'
    exact Devm.push_instructionFrame _ d'

lemma Rinst.pop_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .pop) := by
  simp only [Rinst.runCore]
  have hp := Devm.pop_instructionFrame pre
  cases h : pre.pop with
  | error e =>
      rw [h] at hp
      simpa [h] using hp
  | ok x =>
      rcases x with ⟨word, d⟩
      rw [h] at hp
      simpa [h] using
        (Execution.Rel.trans_left Devm.instructionFrame_trans hp
          (chargeGas_instructionFrame gBase d))

lemma Rinst.dup_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) (n : Fin 16) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm (.dup n)) := by
  simp only [Rinst.runCore]
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame gVerylow pre)
  intro d
  cases h : d.stack[n]? with
  | none =>
      simp only
      exact Devm.instructionFrame_refl d
  | some word =>
      simp only
      exact Devm.push_instructionFrame word d

lemma Rinst.swap_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) (n : Fin 16) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm (.swap n)) := by
  simp only [Rinst.runCore]
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame gVerylow pre)
  intro d
  cases h : d.stack.swap n with
  | none =>
      simp only
      exact Devm.instructionFrame_refl d
  | some stack =>
      simp only
      exact Devm.instructionFrame_of_world_eq rfl rfl rfl rfl

lemma popNat3Bind_instructionFrame (pre : Devm)
    (next : Nat → Nat → Nat → Devm → Execution)
    (hnext : ∀ x y z d, Execution.Rel Devm.InstructionFrame d
      (next x y z d)) :
    Execution.Rel Devm.InstructionFrame pre (do
      let ⟨x, d⟩ ← pre.popToNat
      let ⟨y, d⟩ ← d.popToNat
      let ⟨z, d⟩ ← d.popToNat
      next x y z d) := by
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame pre) (next := fun x d => do
      let ⟨y, d⟩ ← d.popToNat
      let ⟨z, d⟩ ← d.popToNat
      next x y z d) ?_
  intro x d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun y d => do
      let ⟨z, d⟩ ← d.popToNat
      next x y z d) ?_
  intro y d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := next x y) ?_
  exact hnext x y

lemma popAdrNat3Bind_instructionFrame (pre : Devm)
    (next : Adr → Nat → Nat → Nat → Devm → Execution)
    (hnext : ∀ a x y z d, Execution.Rel Devm.InstructionFrame d
      (next a x y z d)) :
    Execution.Rel Devm.InstructionFrame pre (do
      let ⟨a, d⟩ ← pre.popToAdr
      let ⟨x, d⟩ ← d.popToNat
      let ⟨y, d⟩ ← d.popToNat
      let ⟨z, d⟩ ← d.popToNat
      next a x y z d) := by
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToAdr_instructionFrame pre) (next := fun a d => do
      let ⟨x, d⟩ ← d.popToNat
      let ⟨y, d⟩ ← d.popToNat
      let ⟨z, d⟩ ← d.popToNat
      next a x y z d) ?_
  intro a d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun x d => do
      let ⟨y, d⟩ ← d.popToNat
      let ⟨z, d⟩ ← d.popToNat
      next a x y z d) ?_
  intro x d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun y d => do
      let ⟨z, d⟩ ← d.popToNat
      next a x y z d) ?_
  intro y d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := next a x y) ?_
  exact hnext a x y

lemma Rinst.retdatacopy_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .retdatacopy) := by
  simp only [Rinst.runCore]
  refine popNat3Bind_instructionFrame pre (next := fun memoryStart returnStart size d => do
    let d ← chargeGas
      (gVerylow + gReturnDataCopy * ceilDiv size 32 +
        d.extCost [(memoryStart, size)]) d
    if d.returnData.length < returnStart + size then
      .error ⟨"OutOfBoundsRead", d⟩
    let value := d.returnData.sliceD returnStart size 0
    .ok { d with memory := d.memory.write memoryStart value }) ?_
  intro memoryStart returnStart size d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame
      (gVerylow + gReturnDataCopy * ceilDiv size 32 +
        d.extCost [(memoryStart, size)]) d)
  intro d'
  by_cases h : d'.returnData.length < returnStart + size
  · simp only [h, if_pos]
    exact Devm.instructionFrame_refl d'
  · simp only [h, if_false]
    exact Devm.instructionFrame_of_world_eq rfl rfl rfl rfl

lemma Rinst.extcodecopy_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .extcodecopy) := by
  simp only [Rinst.runCore]
  refine popAdrNat3Bind_instructionFrame pre
    (next := fun a memoryStart codeStart size d =>
      if a ∈ d.accessedAddresses then do
        let d ← chargeGas (gasWarmAccess + gasCopy * ceilDiv size 32 +
          d.extCost [(memoryStart, size)]) d
        let value := (d.getCode a).sliceD codeStart size (Linst.toB8 .stop)
        .ok { d with memory := d.memory.write memoryStart value }
      else do
        let d ← chargeGas
          (gasColdAccountAccess + gasCopy * ceilDiv size 32 +
            d.extCost [(memoryStart, size)]) (addAccessedAddress d a)
        let value := (d.getCode a).sliceD codeStart size (Linst.toB8 .stop)
        .ok { d with memory := d.memory.write memoryStart value }) ?_
  intro a memoryStart codeStart size d
  by_cases h : a ∈ d.accessedAddresses
  · simp only [h, if_pos]
    apply Execution.Rel.bind Devm.instructionFrame_trans
      (chargeGas_instructionFrame
        (gasWarmAccess + gasCopy * ceilDiv size 32 +
          d.extCost [(memoryStart, size)]) d)
    intro d'
    exact Devm.instructionFrame_of_world_eq rfl rfl rfl rfl
  · simp only [h, if_false]
    apply Execution.Rel.bind Devm.instructionFrame_trans
      (Execution.Rel.trans_left Devm.instructionFrame_trans
        (addAccessedAddress_instructionFrame d a)
        (chargeGas_instructionFrame
          (gasColdAccountAccess + gasCopy * ceilDiv size 32 +
            d.extCost [(memoryStart, size)])
          (addAccessedAddress d a)))
    intro d'
    exact Devm.instructionFrame_of_world_eq rfl rfl rfl rfl

lemma Rinst.log_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) (n : Fin 5) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm (.log n)) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame pre) (next := fun memoryStart d => do
      let ⟨size, d⟩ ← d.popToNat
      let ⟨topics, d⟩ ← d.popN n
      let d ← chargeGas
        (gLog + gLogdata * size + gLogtopic * n +
          d.extCost [(memoryStart, size)]) d
      assertDynamic sevm d
      let ⟨data, d⟩ := d.memRead memoryStart size
      .ok (d.addLog ⟨sevm.currentTarget, topics, data⟩)) ?_
  intro memoryStart d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun size d => do
      let ⟨topics, d⟩ ← d.popN n
      let d ← chargeGas
        (gLog + gLogdata * size + gLogtopic * n +
          d.extCost [(memoryStart, size)]) d
      assertDynamic sevm d
      let ⟨data, d⟩ := d.memRead memoryStart size
      .ok (d.addLog ⟨sevm.currentTarget, topics, data⟩)) ?_
  intro size d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popN_instructionFrame d n) (next := fun topics d => do
      let d ← chargeGas
        (gLog + gLogdata * size + gLogtopic * n +
          d.extCost [(memoryStart, size)]) d
      assertDynamic sevm d
      let ⟨data, d⟩ := d.memRead memoryStart size
      .ok (d.addLog ⟨sevm.currentTarget, topics, data⟩)) ?_
  intro topics d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame _ d)
  intro d'
  unfold assertDynamic Except.assert
  split
  · exact Devm.instructionFrame_trans
      (Devm.memRead_instructionFrame d' memoryStart size)
      (Devm.addLog_instructionFrame (d'.memRead memoryStart size).2
        ⟨sevm.currentTarget, topics, (d'.memRead memoryStart size).1⟩)
  · exact Devm.instructionFrame_refl d'

theorem Rinst.runCore_instructionFrame
    (pc : Nat) (sevm : Sevm) (pre : Devm) (r : Rinst)
    (h_not_sstore : r ≠ .sstore) (h_not_tstore : r ≠ .tstore) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm r) := by
  cases r
  all_goals try contradiction
  all_goals try (
    with_reducible first
      | exact Rinst.exp_runCore_instructionFrame pc pre sevm
      | exact Rinst.kec_runCore_instructionFrame pc pre sevm
      | exact Rinst.balance_runCore_instructionFrame pc pre sevm
      | exact Rinst.blobhash_runCore_instructionFrame pc pre sevm
      | exact Rinst.calldataload_runCore_instructionFrame pc pre sevm
      | exact Rinst.calldatacopy_runCore_instructionFrame pc pre sevm
      | exact Rinst.codecopy_runCore_instructionFrame pc pre sevm
      | exact Rinst.extcodesize_runCore_instructionFrame pc pre sevm
      | exact Rinst.extcodecopy_runCore_instructionFrame pc pre sevm
      | exact Rinst.retdatacopy_runCore_instructionFrame pc pre sevm
      | exact Rinst.extcodehash_runCore_instructionFrame pc pre sevm
      | exact Rinst.blockhash_runCore_instructionFrame pc pre sevm
      | exact Rinst.pop_runCore_instructionFrame pc pre sevm
      | exact Rinst.mload_runCore_instructionFrame pc pre sevm
      | exact Rinst.mstore_runCore_instructionFrame pc pre sevm
      | exact Rinst.mstore8_runCore_instructionFrame pc pre sevm
      | exact Rinst.sload_runCore_instructionFrame pc pre sevm
      | exact Rinst.tload_runCore_instructionFrame pc pre sevm
      | exact Rinst.mcopy_runCore_instructionFrame pc pre sevm
      | exact Rinst.gas_runCore_instructionFrame pc pre sevm
      | exact Rinst.dup_runCore_instructionFrame pc pre sevm _
      | exact Rinst.swap_runCore_instructionFrame pc pre sevm _
      | exact Rinst.log_runCore_instructionFrame pc pre sevm _)
  all_goals simp only [Rinst.runCore]
  all_goals with_reducible first
    | exact applyBinary_instructionFrame _ _ pre
    | exact applyTernary_instructionFrame _ _ pre
    | exact applyUnary_instructionFrame _ _ pre
    | exact pushItem_instructionFrame _ _ pre

lemma Devm.stateWriteFrame_of_world_eq {d d' : Devm}
    (hdel : d.accountsToDelete = d'.accountsToDelete)
    (hstate : d.state = d'.state)
    (hcreated : d.createdAccounts = d'.createdAccounts)
    (htransient : d.transientStorage = d'.transientStorage) :
    Devm.StateWriteFrame d d' := by
  exact {
    stack := trivial, memory := trivial, gasLeft := trivial, logs := trivial
    refundCounter := trivial, output := trivial, accountsToDelete := hdel
    returnData := trivial, error := trivial, accessedAddresses := trivial
    accessedStorageKeys := trivial, state := by
      change State.BalCodeEq d.state d'.state
      rw [hstate]
      rfl
    createdAccounts := hcreated, transientStorage := htransient }

/-- The state-writer frame implies the pre-existing `SSTORE` balance fact. -/
lemma Devm.StateWriteFrame.getBal_eq {d d' : Devm}
    (h : Devm.StateWriteFrame d d') (adr : Adr) :
    d.getBal adr = d'.getBal adr := by
  have hstate : State.BalCodeEq d.state d'.state := h.state
  unfold State.BalCodeEq at hstate
  exact congrArg Prod.fst (congrFun hstate adr)

/-- The state-writer frame implies the pre-existing `SSTORE` code fact. -/
lemma Devm.StateWriteFrame.getCode_eq {d d' : Devm}
    (h : Devm.StateWriteFrame d d') (adr : Adr) :
    d.getCode adr = d'.getCode adr := by
  have hstate : State.BalCodeEq d.state d'.state := h.state
  unfold State.BalCodeEq at hstate
  exact congrArg Prod.snd (congrFun hstate adr)

lemma Devm.setStorVal_stateWriteFrame (d : Devm)
    (adr : Adr) (key value : B256) :
    Devm.StateWriteFrame d (d.setStorVal adr key value) := by
  exact {
    stack := trivial, memory := trivial, gasLeft := trivial, logs := trivial
    refundCounter := trivial, output := trivial, accountsToDelete := rfl
    returnData := trivial, error := trivial, accessedAddresses := trivial
    accessedStorageKeys := trivial, state := by
      change State.BalCodeEq d.state (d.setStorVal adr key value).state
      unfold State.BalCodeEq
      funext adr'
      apply Prod.ext
      · change d.getBal adr' = (d.setStorVal adr key value).getBal adr'
        exact setStorVal_inv_getBal.symm
      · change d.getCode adr' = (d.setStorVal adr key value).getCode adr'
        exact setStorVal_inv_getCode.symm
    createdAccounts := rfl, transientStorage := rfl }

lemma Devm.transientWriteFrame_of_world_eq {d d' : Devm}
    (hdel : d.accountsToDelete = d'.accountsToDelete)
    (hstate : d.state = d'.state)
    (hcreated : d.createdAccounts = d'.createdAccounts) :
    Devm.TransientWriteFrame d d' := by
  exact {
    stack := trivial, memory := trivial, gasLeft := trivial, logs := trivial
    refundCounter := trivial, output := trivial, accountsToDelete := hdel
    returnData := trivial, error := trivial, accessedAddresses := trivial
    accessedStorageKeys := trivial, state := hstate
    createdAccounts := hcreated, transientStorage := trivial }

lemma Rinst.tstore_runCore_transientWriteFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.TransientWriteFrame pre
      (Rinst.runCore pc pre sevm .tstore) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.transientWriteFrame_trans
    (Outcome.Rel.mono Devm.instructionFrame_refines_transientWriteFrame
      (Devm.pop_instructionFrame pre)) (next := fun key d => do
        let ⟨value, d⟩ ← d.pop
        let d ← chargeGas gasWarmAccess d
        assertDynamic sevm d
        .ok (d.setTransVal sevm.currentTarget key value)) ?_
  intro key d
  refine Outcome.Rel.bindExecution Devm.transientWriteFrame_trans
    (Outcome.Rel.mono Devm.instructionFrame_refines_transientWriteFrame
      (Devm.pop_instructionFrame d)) (next := fun value d => do
        let d ← chargeGas gasWarmAccess d
        assertDynamic sevm d
        .ok (d.setTransVal sevm.currentTarget key value)) ?_
  intro value d
  apply Execution.Rel.bind Devm.transientWriteFrame_trans
    (Outcome.Rel.mono Devm.instructionFrame_refines_transientWriteFrame
      (chargeGas_instructionFrame gasWarmAccess d))
  intro d'
  unfold assertDynamic Except.assert
  split
  · exact Devm.transientWriteFrame_of_world_eq rfl rfl rfl
  · exact Devm.transientWriteFrame_refl d'

lemma Rinst.sstore_runCore_stateWriteFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.StateWriteFrame pre
      (Rinst.runCore pc pre sevm .sstore) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.stateWriteFrame_trans
    (Outcome.Rel.mono Devm.instructionFrame_refines_stateWriteFrame
      (Devm.pop_instructionFrame pre)) (next := fun key d => do
        let ⟨value, d⟩ ← d.pop
        .assert (gCallStipend < d.gasLeft) ⟨"OutOfGasError", d⟩
        let ct := sevm.currentTarget
        let original := getOrigStorVal sevm ct key
        let current := d.getStorVal ct key
        let ⟨d3, gas2⟩ ← .ok <|
          if ⟨ct, key⟩ ∉ d.accessedStorageKeys then
            (addAccessedStorageKey d ct key, gasColdSload) else (d, 0)
        let gas3 ← .ok <|
          if original = current ∧ current ≠ value then
            if original = 0 then gas2 + gasStorageSet
            else gas2 + (gasStorageUpdate - gasColdSload)
          else gas2 + gasWarmAccess
        let d4 ← .ok <| { d3 with refundCounter :=
          sstore_new_refund_counter value original current d3.refundCounter }
        let d5 ← chargeGas gas3 d4
        assertDynamic sevm d5
        .ok (d5.setStorVal ct key value)) ?_
  intro key d
  refine Outcome.Rel.bindExecution Devm.stateWriteFrame_trans
    (Outcome.Rel.mono Devm.instructionFrame_refines_stateWriteFrame
      (Devm.pop_instructionFrame d)) (next := fun value d => do
        .assert (gCallStipend < d.gasLeft) ⟨"OutOfGasError", d⟩
        let ct := sevm.currentTarget
        let original := getOrigStorVal sevm ct key
        let current := d.getStorVal ct key
        let ⟨d3, gas2⟩ ← .ok <|
          if ⟨ct, key⟩ ∉ d.accessedStorageKeys then
            (addAccessedStorageKey d ct key, gasColdSload) else (d, 0)
        let gas3 ← .ok <|
          if original = current ∧ current ≠ value then
            if original = 0 then gas2 + gasStorageSet
            else gas2 + (gasStorageUpdate - gasColdSload)
          else gas2 + gasWarmAccess
        let d4 ← .ok <| { d3 with refundCounter :=
          sstore_new_refund_counter value original current d3.refundCounter }
        let d5 ← chargeGas gas3 d4
        assertDynamic sevm d5
        .ok (d5.setStorVal ct key value)) ?_
  intro value d
  unfold Except.assert
  dsimp only
  split
  · simp only [Except.bind_ok]
    let d3gas : Devm × Nat :=
      if (sevm.currentTarget, key) ∉ d.accessedStorageKeys then
        (addAccessedStorageKey d sevm.currentTarget key, gasColdSload)
      else (d, 0)
    let gas3 :=
      if getOrigStorVal sevm sevm.currentTarget key =
          d.getStorVal sevm.currentTarget key ∧
          d.getStorVal sevm.currentTarget key ≠ value then
        if getOrigStorVal sevm sevm.currentTarget key = 0 then
          d3gas.2 + gasStorageSet
        else d3gas.2 + (gasStorageUpdate - gasColdSload)
      else d3gas.2 + gasWarmAccess
    let d4 : Devm := { d3gas.1 with refundCounter := (
      sstore_new_refund_counter value
        (getOrigStorVal sevm sevm.currentTarget key)
        (d.getStorVal sevm.currentTarget key) d3gas.1.refundCounter) }
    change Execution.Rel Devm.StateWriteFrame d
      (chargeGas gas3 d4 >>= fun d5 =>
        assertDynamic sevm d5 >>= fun _ =>
          .ok (d5.setStorVal sevm.currentTarget key value))
    have hd4 : Devm.StateWriteFrame d d4 := by
      unfold d4 d3gas
      split <;> exact Devm.stateWriteFrame_of_world_eq rfl rfl rfl rfl
    apply Execution.Rel.bind Devm.stateWriteFrame_trans
      (Execution.Rel.trans_left Devm.stateWriteFrame_trans hd4
        (Outcome.Rel.mono Devm.instructionFrame_refines_stateWriteFrame
          (chargeGas_instructionFrame gas3 d4)))
    intro d5
    unfold assertDynamic Except.assert
    split
    · exact Devm.setStorVal_stateWriteFrame d5 sevm.currentTarget key value
    · exact Devm.stateWriteFrame_refl d5
  · exact Devm.stateWriteFrame_refl d

theorem Rinst.run_instructionFrame
    (pc : Nat) (sevm : Sevm) (pre : Devm) (r : Rinst)
    (h_not_sstore : r ≠ .sstore) (h_not_tstore : r ≠ .tstore) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.run ⟨pc, sevm, pre⟩ r) := by
  exact Rinst.runCore_instructionFrame pc sevm pre r
    h_not_sstore h_not_tstore

lemma Rinst.sstore_run_stateWriteFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.StateWriteFrame pre
      (Rinst.run ⟨pc, sevm, pre⟩ .sstore) := by
  exact Rinst.sstore_runCore_stateWriteFrame pc pre sevm

lemma Rinst.tstore_run_transientWriteFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.TransientWriteFrame pre
      (Rinst.run ⟨pc, sevm, pre⟩ .tstore) := by
  exact Rinst.tstore_runCore_transientWriteFrame pc pre sevm

theorem Jinst.runCore_instructionFrame
    (pc : Nat) (sevm : Sevm) (pre : Devm) (j : Jinst) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame pre
      (Jinst.runCore pc pre sevm j) := by
  cases j <;> simp only [Jinst.runCore]
  case jump =>
    cases hp : pre.pop <;> simp only [Except.bind_error, Except.bind_ok]
    · have h := Devm.pop_instructionFrame pre
      rw [hp] at h
      exact h
    · rename_i x
      rcases x with ⟨dest, d⟩
      cases hg : chargeGas gMid d <;>
          simp only [Except.bind_error, Except.bind_ok]
      · exact Devm.instructionFrame_trans
          (by have h := Devm.pop_instructionFrame pre; rw [hp] at h; exact h)
          (by have h := chargeGas_instructionFrame gMid d; rw [hg] at h; exact h)
      · unfold Except.assert
        split <;> exact Devm.instructionFrame_trans
          (by have h := Devm.pop_instructionFrame pre; rw [hp] at h; exact h)
          (by have h := chargeGas_instructionFrame gMid d; rw [hg] at h; exact h)
  case jumpi =>
    cases hp1 : pre.pop <;> simp only [Except.bind_error, Except.bind_ok]
    · have h := Devm.pop_instructionFrame pre
      rw [hp1] at h
      exact h
    · rename_i x
      rcases x with ⟨dest, d1⟩
      have h1 := Devm.pop_instructionFrame pre
      rw [hp1] at h1
      cases hp2 : d1.pop <;> simp only [Except.bind_error, Except.bind_ok]
      · have h2 := Devm.pop_instructionFrame d1
        rw [hp2] at h2
        exact Devm.instructionFrame_trans h1 h2
      · rename_i y
        rcases y with ⟨cond, d2⟩
        have h2 := Devm.pop_instructionFrame d1
        rw [hp2] at h2
        have h12 := Devm.instructionFrame_trans h1 h2
        cases hg : chargeGas gHigh d2 <;>
            simp only [Except.bind_error, Except.bind_ok]
        · have h3 := chargeGas_instructionFrame gHigh d2
          rw [hg] at h3
          exact Devm.instructionFrame_trans h12 h3
        · rename_i d3
          have h3 := chargeGas_instructionFrame gHigh d2
          rw [hg] at h3
          have h123 := Devm.instructionFrame_trans h12 h3
          split
          · exact h123
          · unfold Except.assert
            split <;> exact h123
  case jumpdest =>
    cases hg : chargeGas gJumpdest pre <;>
        simp only [Except.bind_error, Except.bind_ok]
    · have h := chargeGas_instructionFrame gJumpdest pre
      rw [hg] at h
      exact h
    · have h := chargeGas_instructionFrame gJumpdest pre
      rw [hg] at h
      exact h

theorem Jinst.run_instructionFrame (evm : Evm) (j : Jinst) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame evm.dyna
      (Jinst.run evm j) := by
  exact Jinst.runCore_instructionFrame evm.pc evm.sta evm.dyna j

theorem Linst.run_instructionFrame
    (sevm : Sevm) (pre : Devm) (l : Linst) (h_not_dest : l ≠ .dest) :
    Execution.Rel Devm.InstructionFrame pre (Linst.run sevm pre l) := by
  cases l <;> simp only [Linst.run]
  case stop => exact Devm.instructionFrame_refl pre
  case ret =>
    refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
      (Devm.popToNat_instructionFrame pre)
      (next := fun index d => do
        let ⟨size, d⟩ ← d.popToNat
        let d ← chargeGas (d.extCost [(index, size)]) d
        let ⟨output, d⟩ := d.memRead index size
        .ok {d with output := output}) ?_
    intro index d
    refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
      (Devm.popToNat_instructionFrame d)
      (next := fun size d => do
        let d ← chargeGas (d.extCost [(index, size)]) d
        let ⟨output, d⟩ := d.memRead index size
        .ok {d with output := output}) ?_
    intro size d
    apply Execution.Rel.bind Devm.instructionFrame_trans
      (chargeGas_instructionFrame (d.extCost [(index, size)]) d)
    intro d'
    exact Devm.instructionFrame_trans
      (Devm.memRead_instructionFrame d' index size)
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl)
  case rev =>
    refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
      (Devm.popToNat_instructionFrame pre)
      (next := fun index d => do
        let ⟨size, d⟩ ← d.popToNat
        let d ← chargeGas (d.extCost [(index, size)]) d
        let ⟨output, d⟩ := d.memRead index size
        .error ("Revert", {d with output := output})) ?_
    intro index d
    refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
      (Devm.popToNat_instructionFrame d)
      (next := fun size d => do
        let d ← chargeGas (d.extCost [(index, size)]) d
        let ⟨output, d⟩ := d.memRead index size
        .error ("Revert", {d with output := output})) ?_
    intro size d
    apply Execution.Rel.bind Devm.instructionFrame_trans
      (chargeGas_instructionFrame (d.extCost [(index, size)]) d)
    intro d'
    exact Devm.instructionFrame_trans
      (Devm.memRead_instructionFrame d' index size)
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl)
  case dest => contradiction

lemma Rinst.inv_getCode
    {pc sevm devm r devm'}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = .ok devm') (a : Adr) :
    devm'.getCode a = devm.getCode a := by
  rcases eq_or_ne r .sstore with rfl | hs
  · have hf := Rinst.sstore_run_stateWriteFrame pc devm sevm; rw [run] at hf
    exact (hf.getCode_eq a).symm
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc devm sevm; rw [run] at hf
    simpa only [Devm.getCode, Devm.getAcct] using congrFun (congrArg (fun s => fun a => (s.get a).code) hf.state).symm a
  · have hf := Rinst.run_instructionFrame pc sevm devm r hs ht; rw [run] at hf; exact (hf.getCode a).symm

def Execution.getCode : Execution → Adr → ByteArray
  | Except.error ⟨_, devm⟩, adr => devm.getCode adr
  | Except.ok devm, adr => devm.getCode adr

lemma chargeGas_getCode_gen {cost devm exn} (h : chargeGas cost devm = exn) (a : Adr) : Execution.getCode exn a = devm.getCode a := by
  cases exn with
  | error err => exact (chargeGas_worldEq_of_error h).getCode a |>.symm
  | ok devm' => exact (chargeGas_worldEq_of_ok h).getCode a |>.symm

lemma processCreateMessage.chargeCodeGas_getCode_gen {evm : Devm} {exn : Execution}
    (h : processCreateMessage.chargeCodeGas evm = exn) (a : Adr) :
    Execution.getCode exn a = evm.getCode a := by
  simp only [processCreateMessage.chargeCodeGas] at h
  split at h
  · subst h; rfl
  · dsimp [Bind.bind, Except.bind] at h
    split at h
    · rename_i eq_err; subst h
      have h_charge := chargeGas_getCode_gen eq_err a
      exact h_charge
    · rename_i eq_ok; split at h
      · subst h
        have h_charge := chargeGas_getCode_eq eq_ok a
        exact h_charge
      · subst h
        have h_charge := chargeGas_getCode_eq eq_ok a
        exact h_charge

lemma Devm.push_getCode_gen {v devm} {exn : Execution} (h : Devm.push v devm = exn) (a : Adr) : Execution.getCode exn a = devm.getCode a := by
  subst h
  cases hp : Devm.push v devm with
  | error err =>
    exact (liftMachExecution_worldEq_of_error (core := Mach.push v) hp).getCode a |>.symm
  | ok d =>
    exact (liftMachExecution_worldEq_of_ok (core := Mach.push v) hp).getCode a |>.symm

def Xlot.InvGetCode : Xlot → Prop
  | .none => True
  | .some ⟨_, devm, exn⟩ =>
    ∀ adr,
      (devm.getCode adr).toList ≠ [] →
      devm.getCode adr = exn.getCode adr

lemma applyPrecompResult_getCode (evm : Evm) (res : PrecompResult) (ex : Execution)
    (h_ex : applyPrecompResult evm res = ex) (a : Adr) :
    ex.getCode a = evm.dyna.getCode a := by
  revert h_ex
  cases res <;> (intro h_ex; subst h_ex; rfl)

lemma executePrecomp_inv_getCode (evm : Evm) (adr : Adr) (ex : Execution)
    (h_ex : executePrecomp evm adr = ex) (a : Adr) :
    ex.getCode a = evm.dyna.getCode a := by
  apply applyPrecompResult_getCode evm (precompileRun evm adr) ex h_ex a

def MsgResult.getCode (exn : Except (String × State × AdrSet × Tra) Devm) (a : Adr) : ByteArray :=
  match exn with
  | .ok d => d.getCode a
  | .error ⟨_, state, _, _⟩ => state.getCode a

/-! ## Step 7.2 — message-level code-effect masters

Relational code-preservation over message results.  `CodePreserve` says every
nonempty-code address is left untouched; `CodePreserveExcept w` weakens that by
also excluding the single write target `w` (the freshly-created contract). -/

def MsgResult.CodePreserve (base : State)
    (exn : Except (String × State × AdrSet × Tra) Devm) : Prop :=
  ∀ a : Adr, (base.getCode a).toList ≠ [] → MsgResult.getCode exn a = base.getCode a

def MsgResult.CodePreserveExcept (base : State) (w : Adr)
    (exn : Except (String × State × AdrSet × Tra) Devm) : Prop :=
  ∀ a : Adr, a ≠ w → (base.getCode a).toList ≠ [] →
    MsgResult.getCode exn a = base.getCode a

/-- Relational code-preservation over an `Execution` outcome (used by the
Step 7.3 generic-operation masters): every nonempty-code address of `base` has
the same code in the result, on both the ok and error branches. -/
def Execution.CodePreserve (base : Devm) (exn : Execution) : Prop :=
  ∀ a : Adr, (base.getCode a).toList ≠ [] → Execution.getCode exn a = base.getCode a

/-- Writer leaf: `handleError` reshuffles error payloads into ok results and
selects states, but never installs new code. -/
lemma executeCode.handleError_getCode (exn : Execution) (a : Adr) :
    MsgResult.getCode (executeCode.handleError exn) a = exn.getCode a := by
  cases exn with
  | ok d => rfl
  | error p =>
    rcases p with ⟨err, evm⟩
    dsimp only [executeCode.handleError]
    split
    · rfl
    · split <;> rfl

/-- Writer leaf: rollback installs the selected state, so its code map is that
state's code map. -/
lemma Devm.rollback_getCode (devm : Devm) (st : State) (tra : Tra) (a : Adr) :
    (devm.rollback st tra).getCode a = st.getCode a := rfl

/-- Writer leaf: value transfer changes balances but preserves code. -/
lemma benvAfterTransfer_ok_getCode {msg : Msg} {benv : Benv}
    (h : msg.benvAfterTransfer = .ok benv) (a : Adr) :
    benv.state.getCode a = msg.benv.state.getCode a := by
  dsimp [Msg.benvAfterTransfer, Msg.shouldTransferValue] at h
  split at h
  · cases h_sub : msg.benv.subBal msg.caller msg.value with
    | none => simp [h_sub, Option.toExcept, Bind.bind, Except.bind] at h
    | some benv_sub =>
      simp [h_sub, Option.toExcept, Bind.bind, Except.bind] at h
      subst benv
      rw [Benv.addBal_getCode]
      exact Benv.subBal_getCode h_sub
  · simp only [Except.ok.injEq] at h; subst benv; rfl

/-- Writer leaf: create preparation (nonce bump, created-account marking, empty
storage) preserves code. -/
lemma processCreateMessage.msg_getCode (msg : Msg) (a : Adr) :
    (processCreateMessage.msg msg).benv.state.getCode a = msg.benv.state.getCode a := by
  dsimp [processCreateMessage.msg, Msg.withBenv]
  rw [Benv.incrNonce_getCode, addCreatedAccount_getCode, Benv.setStor_getCode]

/-- Master: `executeCode` preserves the code of every nonempty-code address.
The suspended child's oracle invariant (`inv`) supplies the interpreted-code
case; `handleError_getCode` covers precompile and error selection. -/
lemma ExecuteCode.codePreserve
    {msg : Msg} {xl : Xlot} {exn : Except (String × State × AdrSet × Tra) Devm}
    (inv : xl.InvGetCode)
    (run : ExecuteCode msg xl exn) :
    MsgResult.CodePreserve msg.benv.state exn := by
  intro a ha
  dsimp [ExecuteCode] at run
  split at run
  · rcases run with ⟨ex', h_xl, h_err⟩
    subst h_err
    rw [executeCode.handleError_getCode]
    rw [h_xl] at inv
    dsimp [Xlot.InvGetCode] at inv
    exact (inv a ha).symm
  · next adr eq_some =>
    split at run
    · rcases run with ⟨h_xl, h_err⟩
      subst h_err
      rw [executeCode.handleError_getCode]
      exact executePrecomp_inv_getCode (initEvm msg) adr _ rfl a
    · rcases run with ⟨ex', h_xl, h_err⟩
      subst h_err
      rw [executeCode.handleError_getCode]
      rw [h_xl] at inv
      dsimp [Xlot.InvGetCode] at inv
      exact (inv a ha).symm

lemma ExecuteCode.inv_getCode_gen
    {msg : Msg} {xl : Xlot} {exn : Except (String × State × AdrSet × Tra) Devm}
    (inv : xl.InvGetCode)
    (run : ExecuteCode msg xl exn) :
    ∀ a : Adr,
      (msg.benv.state.getCode a).toList ≠ [] →
      MsgResult.getCode exn a = msg.benv.state.getCode a :=
  ExecuteCode.codePreserve inv run

/-- Master: `processMessage` preserves the code of every nonempty-code address.
Value transfer (`benvAfterTransfer_ok_getCode`) and the failed-transfer
short-circuit only touch balances; the interpreted body is bounded by
`ExecuteCode.codePreserve`; the error path selects a state via rollback
(`Devm.rollback_getCode`). -/
lemma ProcessMessage.codePreserve
    {msg : Msg} {xl : Xlot} {exn : Except (String × State × AdrSet × Tra) Devm}
    (inv : xl.InvGetCode)
    (run : ProcessMessage msg xl exn) :
    MsgResult.CodePreserve msg.benv.state exn := by
  intro a ha
  dsimp [ProcessMessage] at run
  dsimp [Except.SplitXl] at run
  rcases run with ⟨x, h_benv_err, h_exn_err, _⟩ | ⟨benv, h_benv, ex', h_exec, h_ex'⟩
  · rw [h_exn_err]
    dsimp [MsgResult.getCode]
    dsimp [Msg.benvAfterTransfer, Msg.shouldTransferValue] at h_benv_err
    split at h_benv_err
    · cases h_sub : msg.benv.subBal msg.caller msg.value
      · simp [h_sub, Option.toExcept, Bind.bind, Except.bind] at h_benv_err
        subst x
        rfl
      · simp [h_sub, Option.toExcept, Bind.bind, Except.bind] at h_benv_err
    · contradiction
  · have h_benv_code := benvAfterTransfer_ok_getCode h_benv a
    have ha' : ( (msg.withBenv benv).benv.state.getCode a ).toList ≠ [] := by
      dsimp [Msg.withBenv]
      rw [h_benv_code]
      exact ha
    have h_exec_cond := ExecuteCode.codePreserve inv h_exec a ha'
    dsimp [Msg.withBenv] at h_exec_cond
    rw [h_benv_code] at h_exec_cond
    dsimp [Except.Split] at h_ex'
    rcases h_ex' with ⟨x, h_ex'_err, h_exn_err⟩ | ⟨evm, eq_ok, h_if⟩
    · rw [h_exn_err]
      rw [h_ex'_err] at h_exec_cond
      exact h_exec_cond
    · split at h_if
      · rw [← h_if]
        exact Devm.rollback_getCode evm msg.benv.state msg.tenv.transientStorage a
      · rw [← h_if]
        rw [eq_ok] at h_exec_cond
        exact h_exec_cond

lemma ProcessMessage.inv_getCode_gen
    {msg : Msg} {xl : Xlot} {exn : Except (String × State × AdrSet × Tra) Devm}
    (inv : xl.InvGetCode)
    (run : ProcessMessage msg xl exn) :
    ∀ a : Adr,
      (msg.benv.state.getCode a).toList ≠ [] →
      MsgResult.getCode exn a = msg.benv.state.getCode a :=
  ProcessMessage.codePreserve inv run

lemma setCode_getCode {evm : Devm} {a b : Adr} {code : ByteArray} (h : a ≠ b) :
  (evm.setCode a code).getCode b = evm.getCode b := by
  dsimp [Devm.setCode, Devm.getCode, Devm.state, Devm.getAcct, State.setCode, State.set, State.getCode, State.get]
  split_ifs with h_if
  · by_cases hc : compare a b = Ordering.eq
    · exact False.elim (h (compare_eq_iff_eq.mp hc))
    · rw [Std.TreeMap.getD_erase]
      simp [hc]
  · by_cases hc : compare a b = Ordering.eq
    · exact False.elim (h (compare_eq_iff_eq.mp hc))
    · rw [Std.TreeMap.getD_insert]
      simp [hc]

/-- Master: `processCreateMessage` preserves the code of every nonempty-code
address *other than* the create target.  Create preparation
(`processCreateMessage.msg_getCode`) and the interpreted body
(`ProcessMessage.codePreserve`) preserve code; code-gas charging preserves it
(`chargeCodeGas_getCode_gen`); create completion writes only `msg.currentTarget`
through `setCode` (`setCode_getCode`, excluded by `a ≠ msg.currentTarget`); the
halt/error paths select states via rollback (`Devm.rollback_getCode`). -/
lemma ProcessCreateMessage.codePreserve
    {msg : Msg} {xl : Xlot} {exn : Except (String × State × AdrSet × Tra) Devm}
    (inv : xl.InvGetCode)
    (run : ProcessCreateMessage msg xl exn) :
    MsgResult.CodePreserveExcept msg.benv.state msg.currentTarget exn := by
  intro a h_a ha
  have h_benv_code := processCreateMessage.msg_getCode msg a
  have ha' : ((processCreateMessage.msg msg).benv.state.getCode a).toList ≠ [] := by
    rw [h_benv_code]; exact ha
  dsimp [ProcessCreateMessage] at run
  rcases run with ⟨ex', h_exec, h_ex'⟩
  have h_exec_cond := ProcessMessage.codePreserve inv h_exec a ha'
  rw [h_benv_code] at h_exec_cond
  dsimp [Except.Split] at h_ex'
  rcases h_ex' with ⟨x, eq_ex'_err, h_exn_err⟩ | ⟨evm, eq_ok, h_if⟩
  · rw [h_exn_err]
    rw [eq_ex'_err] at h_exec_cond
    exact h_exec_cond
  · split at h_if
    · rename_i h_none
      cases h_charge : processCreateMessage.chargeCodeGas evm with
      | error err =>
        rcases err with ⟨err_msg, err_evm⟩
        rw [h_charge] at h_if
        dsimp at h_if
        split at h_if
        · rename_i h_halt
          rw [← h_if]
          dsimp [processCreateMessage.exceptionalHalt, MsgResult.getCode]
          rfl
        · rw [← h_if]
          dsimp [MsgResult.getCode]
          have h_getCode := processCreateMessage.chargeCodeGas_getCode_gen h_charge a
          change err_evm.state.getCode a = evm.state.getCode a at h_getCode
          rw [h_getCode]
          rw [eq_ok] at h_exec_cond
          exact h_exec_cond
      | ok devm_charge =>
        rw [h_charge] at h_if
        dsimp at h_if
        rw [← h_if]
        dsimp [MsgResult.getCode]
        have h_getCode := processCreateMessage.chargeCodeGas_getCode_gen h_charge a
        dsimp [Execution.getCode] at h_getCode
        rw [setCode_getCode h_a.symm]
        rw [h_getCode]
        rw [eq_ok] at h_exec_cond
        exact h_exec_cond
    · rename_i h_some
      rw [← h_if]
      exact Devm.rollback_getCode evm msg.benv.state msg.tenv.transientStorage a

lemma ProcessCreateMessage.inv_getCode_gen
    {msg : Msg} {xl : Xlot} {exn : Except (String × State × AdrSet × Tra) Devm}
    (inv : xl.InvGetCode)
    (run : ProcessCreateMessage msg xl exn) :
    ∀ a : Adr,
      a ≠ msg.currentTarget →
      (msg.benv.state.getCode a).toList ≠ [] →
      MsgResult.getCode exn a = msg.benv.state.getCode a :=
  ProcessCreateMessage.codePreserve inv run

/-- Master: the whole `GenericCreate` operation preserves the code of every
nonempty-code address.  The world-silent access/gas/return-data prefix and the
`push`/`incrNonce` steps leave code untouched (`Devm.push_getCode_gen`,
`Devm.incrNonce_getCode`); the interpreted child-create body is bounded by the
Step 7.2 master `ProcessCreateMessage.codePreserve` (whose exclusion of the
fresh create `newAddress` is discharged here from the nonempty-code premise,
since the fresh target starts with empty code); child incorporation only
selects between the parent and child worlds. -/
lemma GenericCreate.codePreserve
    {sevm : Sevm} {devm : Devm} {endowment : B256} {newAddress : Adr}
    {memoryIndex memorySize : Nat} {xl : Xlot} {exn : Execution} (inv : xl.InvGetCode)
    (run : GenericCreate sevm devm endowment newAddress memoryIndex memorySize xl exn) :
    Execution.CodePreserve devm exn := by
  dsimp [GenericCreate] at run
  rcases run with ⟨calldata, eq_calldata, run⟩; subst eq_calldata
  rcases run with ⟨x, h_err, eq_err, _⟩ | ⟨_, h_ok, run⟩
  · intro a ha
    rw [eq_err]
    have h : Except.assert (memorySize ≤ maxInitCodeSize) ⟨"OutOfGasError", devm⟩ = Except.error x := h_err
    dsimp [Except.assert] at h
    split at h
    · contradiction
    · injection h with h_eq; subst h_eq
      rfl
  · rcases run with ⟨devm1, eq_devm1, run⟩; subst eq_devm1
    rcases run with ⟨createMsgGas, eq_createMsgGas, run⟩; subst eq_createMsgGas
    rcases run with ⟨devm2, eq_devm2, run⟩; subst eq_devm2
    rcases run with ⟨x, h_err, eq_err, _⟩ | ⟨_, h_ok, run⟩
    · intro a ha
      rw [eq_err]
      dsimp [assertDynamic, Except.assert] at h_err
      split at h_err
      · contradiction
      · injection h_err with h_eq; subst h_eq
        rfl
    · rcases run with ⟨devm3, eq_devm3, run⟩; subst eq_devm3
      rcases run with ⟨sender, eq_sender, run⟩; subst eq_sender
      split at run
      · rcases run with ⟨h_xl, eq_ok⟩
        intro a ha
        rw [← eq_ok]
        exact Devm.push_getCode_gen rfl a
      · rename_i h_if1
        rcases run with ⟨devm4, eq_devm4, run⟩
        split at run
        · rename_i h_if2
          rcases run with ⟨h_xl, eq_ok⟩
          intro a ha
          rw [← eq_ok]
          have h_push : Execution.getCode (devm4.push 0) a = devm4.getCode a := Devm.push_getCode_gen rfl a
          rw [h_push]
          subst eq_devm4
          exact Devm.incrNonce_getCode
        · rename_i h_if2
          rcases run with ⟨childMsg, eq_childMsg, run⟩; subst eq_childMsg
          rcases run with ⟨ex', h_exec, h_ex'⟩
          rcases h_ex' with ⟨x, h_err, eq_err⟩ | ⟨child, h_ok, run⟩
          · intro a ha
            rw [eq_err]
            have h_a_ne : a ≠ newAddress := by
              intro heq
              push_neg at h_if2
              have h_code_size : (devm4.getCode newAddress).size = 0 := h_if2.2.1
              have h_empty : devm4.getCode newAddress = .empty := by
                cases h_code' : devm4.getCode newAddress with | mk data =>
                rw [h_code'] at h_code_size
                cases data with | mk l =>
                cases l
                · rfl
                · contradiction
              have h_devm4 : devm4.getCode newAddress = devm.getCode newAddress := by
                subst eq_devm4; exact Devm.incrNonce_getCode
              rw [heq] at ha
              rw [← h_devm4] at ha
              rw [h_empty] at ha
              have h_empty_toList : ByteArray.empty.toList = [] := by
                unfold ByteArray.toList
                unfold ByteArray.toList.loop
                rfl
              rw [h_empty_toList] at ha
              exact False.elim (ha rfl)
            have h_devm4 : devm4.getCode a = devm.getCode a := by subst eq_devm4; exact Devm.incrNonce_getCode
            have h_goal : (devm4.getCode a).toList ≠ [] := by
              rw [h_devm4]
              exact ha
            have h_exec_cond := ProcessCreateMessage.codePreserve inv h_exec a h_a_ne h_goal
            rcases ex' with err | devm_child
            · dsimp [liftToExecution] at h_err
              injection h_err with h_eq
              subst h_eq
              dsimp [Execution.getCode]
              change MsgResult.getCode (Except.error err) a = devm.getCode a
              rw [h_exec_cond]
              exact h_devm4
            · dsimp [liftToExecution] at h_err
              contradiction
          · intro a ha
            have h_a_ne : a ≠ newAddress := by
              intro heq
              push_neg at h_if2
              have h_code_size : (devm4.getCode newAddress).size = 0 := h_if2.2.1
              have h_empty : devm4.getCode newAddress = .empty := by
                cases h_code' : devm4.getCode newAddress with | mk data =>
                rw [h_code'] at h_code_size
                cases data with | mk l =>
                cases l
                · rfl
                · contradiction
              have h_devm4 : devm4.getCode newAddress = devm.getCode newAddress := by
                subst eq_devm4; exact Devm.incrNonce_getCode
              rw [heq] at ha
              rw [← h_devm4] at ha
              rw [h_empty] at ha
              have h_empty_toList : ByteArray.empty.toList = [] := by
                unfold ByteArray.toList
                unfold ByteArray.toList.loop
                rfl
              rw [h_empty_toList] at ha
              exact False.elim (ha rfl)
            have h_devm4 : devm4.getCode a = devm.getCode a := by subst eq_devm4; exact Devm.incrNonce_getCode
            have h_goal : (devm4.getCode a).toList ≠ [] := by
              rw [h_devm4]
              exact ha
            have h_exec_cond := ProcessCreateMessage.codePreserve inv h_exec a h_a_ne h_goal
            rcases ex' with err | devm_child
            · dsimp [liftToExecution] at h_ok
              contradiction
            · dsimp [liftToExecution] at h_ok
              injection h_ok with h_eq
              symm at h_eq
              subst h_eq
              split at run
              · rename_i h_child_err
                have h_push := Devm.push_getCode_gen run a
                rw [h_push]
                dsimp [incorporateChildOnError]
                change child.getCode a = devm.getCode a
                change child.getCode a = _ at h_exec_cond
                rw [h_exec_cond]
                exact h_devm4
              · rename_i h_child_err
                have h_push := Devm.push_getCode_gen run a
                rw [h_push]
                dsimp [incorporateChildOnSuccess]
                change child.getCode a = devm.getCode a
                change child.getCode a = _ at h_exec_cond
                rw [h_exec_cond]
                exact h_devm4

lemma GenericCreate.inv_getCode_gen
    {sevm : Sevm} {devm : Devm} {endowment : B256} {newAddress : Adr}
    {memoryIndex memorySize : Nat} {xl : Xlot} {exn : Execution} (inv : xl.InvGetCode)
    (run : GenericCreate sevm devm endowment newAddress memoryIndex memorySize xl exn) :
    ∀ (a : Adr),
      (devm.getCode a).toList ≠ [] →
      Execution.getCode exn a = devm.getCode a :=
  GenericCreate.codePreserve inv run

/-- Master: the whole `GenericCall` operation preserves the code of every
nonempty-code address.  The world-silent return-data/memory prefix leaves code
untouched (`Devm.push_getCode_gen`, `liftMachPure_worldEq` for `memWrite`); the
interpreted child body is bounded by the Step 7.2 master
`ProcessMessage.codePreserve`; child incorporation
(`incorporateChildOnError`/`OnSuccess`) only selects between the parent and
child worlds. -/
lemma GenericCall.codePreserve
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {input_index input_size output_index output_size : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {xl : Xlot} {exn : Execution}
    (inv : xl.InvGetCode)
    (run : GenericCall sevm devm gas value caller target codeAddress shouldTransferValue isStaticcall input_index input_size output_index output_size code disablePrecompiles xl exn) :
    Execution.CodePreserve devm exn := by
  dsimp [GenericCall] at run
  rcases run with ⟨evm1, eq_evm1, run⟩; subst eq_evm1
  split at run
  · rcases run with ⟨h_xl, eq_ok⟩
    intro a ha
    exact Devm.push_getCode_gen eq_ok a
  · rcases run with ⟨calldata, eq_calldata, run⟩; subst eq_calldata
    rcases run with ⟨childMsg, eq_childMsg, run⟩; subst eq_childMsg
    rcases run with ⟨ex', h_exec, h_ex'⟩
    rcases h_ex' with ⟨x, h_err, eq_err⟩ | ⟨child, h_ok, run⟩
    · intro a ha
      rw [eq_err]
      have h_exec_cond := ProcessMessage.codePreserve inv h_exec a ha
      rcases ex' with err | child
      · dsimp [liftToExecution] at h_err
        injection h_err with h_eq
        subst h_eq
        dsimp [Execution.getCode]
        change MsgResult.getCode (Except.error err) a = devm.getCode a
        rw [h_exec_cond]
        rfl
      · dsimp [liftToExecution] at h_err
        contradiction
    · intro a ha
      have h_exec_cond := ProcessMessage.codePreserve inv h_exec a ha
      rcases ex' with err | child
      · dsimp [liftToExecution] at h_ok
        contradiction
      · dsimp [liftToExecution] at h_ok
        injection h_ok with h_eq
        symm at h_eq
        subst h_eq
        split at run
        · rename_i h_child_err
          dsimp [Except.Split] at run
          rcases run with ⟨y, h_err, eq_err⟩ | ⟨evm2, h_ok, eq_ok⟩
          · rw [eq_err]
            have h_push := Devm.push_getCode_gen h_err a
            rw [h_push]
            dsimp [incorporateChildOnError]
            change child.getCode a = devm.getCode a
            change child.getCode a = _ at h_exec_cond
            rw [h_exec_cond]
            rfl
          · rw [← eq_ok]
            dsimp [Execution.getCode]
            have h_memWrite : (evm2.memWrite output_index (child.output.take output_size)).getCode a = evm2.getCode a := by
              exact (liftMachPure_worldEq (Mach.memWrite · output_index (child.output.take output_size)) evm2).getCode a |>.symm
            rw [h_memWrite]
            have h_push := Devm.push_getCode_gen h_ok a
            change evm2.getCode a = _ at h_push
            rw [h_push]
            dsimp [incorporateChildOnError]
            change child.getCode a = devm.getCode a
            change child.getCode a = _ at h_exec_cond
            rw [h_exec_cond]
            rfl
        · rename_i h_child_err
          dsimp [Except.Split] at run
          rcases run with ⟨y, h_err, eq_err⟩ | ⟨evm2, h_ok, eq_ok⟩
          · rw [eq_err]
            have h_push := Devm.push_getCode_gen h_err a
            rw [h_push]
            dsimp [incorporateChildOnSuccess]
            change child.getCode a = devm.getCode a
            change child.getCode a = _ at h_exec_cond
            rw [h_exec_cond]
            rfl
          · rw [← eq_ok]
            dsimp [Execution.getCode]
            have h_memWrite : (evm2.memWrite output_index (child.output.take output_size)).getCode a = evm2.getCode a := by
              exact (liftMachPure_worldEq (Mach.memWrite · output_index (child.output.take output_size)) evm2).getCode a |>.symm
            rw [h_memWrite]
            have h_push := Devm.push_getCode_gen h_ok a
            change evm2.getCode a = _ at h_push
            rw [h_push]
            dsimp [incorporateChildOnSuccess]
            change child.getCode a = devm.getCode a
            change child.getCode a = _ at h_exec_cond
            rw [h_exec_cond]
            rfl

lemma GenericCall.inv_getCode_gen
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {input_index input_size output_index output_size : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {xl : Xlot} {exn : Execution}
    (inv : xl.InvGetCode)
    (run : GenericCall sevm devm gas value caller target codeAddress shouldTransferValue isStaticcall input_index input_size output_index output_size code disablePrecompiles xl exn) :
    ∀ a : Adr,
      (devm.getCode a).toList ≠ [] →
      exn.getCode a = devm.getCode a :=
  GenericCall.codePreserve inv run

lemma Devm.pop_getCode_err {err devm} (h : Devm.pop devm = .error err) (a : Adr) : err.2.getCode a = devm.getCode a := by
  exact (Devm.pop_worldEq_of_error h).getCode a |>.symm

lemma chargeGas_getCode_err {cost devm err} (h : chargeGas cost devm = .error err) (a : Adr) : err.2.getCode a = devm.getCode a := by
  exact (chargeGas_worldEq_of_error h).getCode a |>.symm

lemma Devm.push_getCode_err {v devm err} (h : Devm.push v devm = Except.error err) (a : Adr) : err.2.getCode a = devm.getCode a := by
  exact (liftMachExecution_worldEq_of_error (core := Mach.push v) h).getCode a |>.symm

lemma assert_getCode_err {cond : Prop} [Decidable cond] {msg : String} {devm : Devm} {err : String × Devm} (h : Except.assert cond (msg, devm) = Except.error err) (a : Adr) : err.2.getCode a = devm.getCode a := by
  unfold Except.assert at h
  split_ifs at h; try contradiction
  injection h with h1; rw [← h1]

lemma Devm.popToNat_getCode_err {devm err} (h : Devm.popToNat devm = .error err) (a : Adr) : err.2.getCode a = devm.getCode a := by
  exact (Devm.popToNat_worldEq_of_error h).getCode a |>.symm

lemma Devm.popToAdr_getCode_err {devm err} (h : Devm.popToAdr devm = .error err) (a : Adr) : err.2.getCode a = devm.getCode a := by
  exact (liftMach_worldEq_of_error (core := Mach.popToAdr) h).getCode a |>.symm

lemma getCode_err_of_bind {α} {ma : Except (String × Devm) α} {f : α → Execution}
    {devm : Devm} {a : Adr} {err : String × Devm}
    (run : (ma >>= f) = Except.error err)
    (getDevm : α → Devm)
    (h_first_ok : ∀ v, ma = Except.ok v → (getDevm v).getCode a = devm.getCode a)
    (h_first_err : ∀ e, ma = Except.error e → e.2.getCode a = devm.getCode a)
    (h_rest_err : ∀ v, ma = Except.ok v → f v = Except.error err → err.2.getCode a = (getDevm v).getCode a) :
    err.2.getCode a = devm.getCode a := by
  cases h_ma : ma
  case error e =>
    rw [h_ma, Except.bind_error] at run
    injection run with h_eq; subst h_eq
    exact h_first_err _ h_ma
  case ok v =>
    rw [h_ma, Except.bind_ok] at run
    have h1 := h_rest_err v h_ma run
    have h2 := h_first_ok v h_ma
    exact h1.trans h2

lemma Devm.popN_getCode_err {n : Nat} {devm : Devm} {err : String × Devm}
    (hp : devm.popN n = Except.error err) (a : Adr) :
    err.2.getCode a = devm.getCode a := by
  exact (liftMach_worldEq_of_error (core := (Mach.popN · n)) hp).getCode a |>.symm

lemma pushItem_getCode_err {x c devm err} (h : pushItem x c devm = Except.error err) (a : Adr) : err.2.getCode a = devm.getCode a := by
  exact (liftMachExecution_worldEq_of_error (core := Mach.pushItem x c) h).getCode a |>.symm

lemma applyUnary_getCode_err {f : B256 → B256} {cost devm err}
    (h : applyUnary f cost devm = Except.error err) (a : Adr) :
    err.2.getCode a = devm.getCode a := by
  exact (liftMachExecution_worldEq_of_error (core := Mach.applyUnary f cost) h).getCode a |>.symm

lemma applyBinary_getCode_err {f : B256 → B256 → B256} {cost devm err}
    (h : applyBinary f cost devm = Except.error err) (a : Adr) :
    err.2.getCode a = devm.getCode a := by
  exact (liftMachExecution_worldEq_of_error (core := Mach.applyBinary f cost) h).getCode a |>.symm

lemma applyTernary_getCode_err {f : B256 → B256 → B256 → B256} {cost devm err}
    (h : applyTernary f cost devm = Except.error err) (a : Adr) :
    err.2.getCode a = devm.getCode a := by
  exact (liftMachExecution_worldEq_of_error (core := Mach.applyTernary f cost) h).getCode a |>.symm

lemma Rinst.inv_getCode_err
    {pc sevm devm r err}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = Except.error err) (a : Adr) :
    err.2.getCode a = devm.getCode a := by
  rcases eq_or_ne r .sstore with rfl | hs
  · have hf := Rinst.sstore_run_stateWriteFrame pc devm sevm; rw [run] at hf
    exact (Devm.StateWriteFrame.getCode_eq hf a).symm
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc devm sevm; rw [run] at hf
    exact congrFun (congrArg (fun s => fun a => (s.get a).code) hf.state).symm a
  · have hf := Rinst.run_instructionFrame pc sevm devm r hs ht; rw [run] at hf; exact (Devm.InstructionFrame.getCode hf a).symm

lemma Rinst.inv_getCode_gen
    {pc sevm devm r exn}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = exn) (a : Adr)
    (_ne : (devm.getCode a).toList ≠ []) :
    Execution.getCode exn a = devm.getCode a := by
  cases exn <;> first | exact Rinst.inv_getCode_err run a | exact Rinst.inv_getCode run a

lemma Xinst.inv_getCode_gen
    {sevm devm x xl exn}
    (inv : xl.InvGetCode)
    (run : Xinst.Run sevm devm x xl exn) :
    ∀ a : Adr,
      (devm.getCode a).toList ≠ [] →
      exn.getCode a = devm.getCode a := by
  intro a ha
  cases x
  case create =>
    dsimp [Xinst.Run] at run
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨endowment, devm1⟩, eq1, run⟩
    · rw [eq_exn]; exact Devm.pop_getCode_err h_err a
    have hc1 : devm1.getCode a = devm.getCode a := by
      revert eq1; simp only [Devm.pop_def]; split <;> intro eq1
      · contradiction
      · injection eq1 with h1; injection h1 with _ h2; subst h2; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨memoryIndex, devm2⟩, eq2, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans hc1
    have hc2 : devm2.getCode a = devm1.getCode a := Devm.popToNat_getCode_eq eq2 a
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨memorySize, devm3⟩, eq3, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc2.trans hc1)
    have hc3 : devm3.getCode a = devm2.getCode a := Devm.popToNat_getCode_eq eq3 a
    rcases run with ⟨extendCost, hp4, run⟩
    rcases run with ⟨initCodeCost, hp5, run⟩
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨devm4, eq6, run⟩
    · rw [eq_exn]; exact (chargeGas_getCode_err h_err a).trans (hc3.trans (hc2.trans hc1))
    have hc4 : devm4.getCode a = devm3.getCode a := by
      revert eq6; rw [chargeGas_def]; split <;> intro eq6
      · contradiction
      · injection eq6 with h7; subst h7; rfl
    rcases run with ⟨calldata, hp7, run⟩
    rcases run with ⟨newAddress, hp8, run⟩
    have hc5 : calldata.getCode a = devm4.getCode a := by
      subst hp7; dsimp [Devm.getCode, Devm.memExtends_def]; rfl
    have h_code : calldata.getCode a = devm.getCode a := by
      rw [hc5, hc4, hc3, hc2, hc1]
    have ha_calldata : (calldata.getCode a).toList ≠ [] := by
      rw [h_code]
      exact ha
    have h_gen := GenericCreate.inv_getCode_gen inv run a ha_calldata
    rw [h_gen, h_code]
  case call =>
    dsimp [Xinst.Run] at run
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨gas, devm1⟩, eq1, run⟩
    · rw [eq_exn]; exact Devm.pop_getCode_err h_err a
    have hc1 : devm1.getCode a = devm.getCode a := by
      revert eq1; rw [Devm.pop_def]; split <;> intro eq1
      · contradiction
      · injection eq1 with h1; injection h1 with _ h2; subst h2; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨callee, devm2⟩, eq2, run⟩
    · rw [eq_exn]; exact (Devm.popToAdr_getCode_err h_err a).trans hc1
    have hc2 : devm2.getCode a = devm1.getCode a :=
      Devm.popToAdr_getCode_eq eq2 a
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨value, devm3⟩, eq3, run⟩
    · rw [eq_exn]; exact (Devm.pop_getCode_err h_err a).trans (hc2.trans hc1)
    have hc3 : devm3.getCode a = devm2.getCode a := by
      revert eq3; rw [Devm.pop_def]; split <;> intro eq3
      · contradiction
      · injection eq3 with h5; injection h5 with _ h6; subst h6; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨inputIndex, devm4⟩, eq4, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc3.trans (hc2.trans hc1))
    have hc4 : devm4.getCode a = devm3.getCode a := Devm.popToNat_getCode_eq eq4 a
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨inputSize, devm5⟩, eq5, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc4.trans (hc3.trans (hc2.trans hc1)))
    have hc5 : devm5.getCode a = devm4.getCode a := Devm.popToNat_getCode_eq eq5 a
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨outputIndex, devm6⟩, eq6, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1))))
    have hc6 : devm6.getCode a = devm5.getCode a := Devm.popToNat_getCode_eq eq6 a
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨outputSize, devm7⟩, eq7, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc6.trans (hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1)))))
    have hc7 : devm7.getCode a = devm6.getCode a := Devm.popToNat_getCode_eq eq7 a
    rcases run with ⟨extendCost, hp8, run⟩
    rcases run with ⟨preAccessCost, hp9, run⟩
    rcases run with ⟨devm8, hp10, run⟩
    have hc8 : devm8.getCode a = devm7.getCode a := by
      subst hp10; rw [addAccessedAddress_def]; rfl
    rcases run with ⟨⟨disablePrecompiles, _, code, delegatedAccessGasCost, devm9⟩, hp11, run⟩
    have hc9 : devm9.getCode a = devm8.getCode a := by
      have h_acc := @accessDelegation_getCode devm8 callee a
      rw [← hp11] at h_acc
      exact h_acc
    rcases run with ⟨accessCost, hp12, run⟩
    rcases run with ⟨createCost, hp13, run⟩
    rcases run with ⟨transferCost, hp14, run⟩
    rcases run with ⟨⟨msgCallCost, msgCallStipend⟩, hp15, run⟩
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨devm10, eq16, run⟩
    · rw [eq_exn]; exact (chargeGas_getCode_err h_err a).trans (hc9.trans (hc8.trans (hc7.trans (hc6.trans (hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1))))))))
    have hc10 : devm10.getCode a = devm9.getCode a := by
      revert eq16; rw [chargeGas_def]; split <;> intro eq16
      · contradiction
      · injection eq16 with h15; subst h15; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨_, eq17, run⟩
    · rw [eq_exn]; exact (assert_getCode_err h_err a).trans (hc10.trans (hc9.trans (hc8.trans (hc7.trans (hc6.trans (hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1)))))))))
    rcases run with ⟨devm11, hp18, run⟩
    have hc11 : devm11.getCode a = devm10.getCode a := by
      subst hp18; dsimp [Devm.getCode, Devm.memExtends_def]; rfl
    rcases run with ⟨senderBal, hp19, run⟩
    split_ifs at run with h_bal
    · rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨devm12, eq20, h_xl2, h_ex⟩
      · rw [eq_exn]; exact (Devm.push_getCode_err h_err a).trans (hc11.trans (hc10.trans (hc9.trans (hc8.trans (hc7.trans (hc6.trans (hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1))))))))))
      have hc12 : devm12.getCode a = devm11.getCode a :=
        Devm.push_getCode_eq eq20 a
      have hc_final : exn.getCode a = devm12.getCode a := by
        rw [← h_ex]; rfl
      rw [hc_final, hc12, hc11, hc10, hc9, hc8, hc7, hc6, hc5, hc4, hc3, hc2, hc1]
    · have h_code : devm11.getCode a = devm.getCode a := by
        rw [hc11, hc10, hc9, hc8, hc7, hc6, hc5, hc4, hc3, hc2, hc1]
      have ha_11 : (devm11.getCode a).toList ≠ [] := by
        rw [h_code]; exact ha
      have h_gen := GenericCall.inv_getCode_gen inv run a ha_11
      rw [h_gen, h_code]
  case callcode =>
    dsimp [Xinst.Run] at run
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨gas, devm1⟩, eq1, run⟩
    · rw [eq_exn]; exact Devm.pop_getCode_err h_err a
    have hc1 : devm1.getCode a = devm.getCode a := by
      revert eq1; rw [Devm.pop_def]; split <;> intro eq1
      · contradiction
      · injection eq1 with h1; injection h1 with _ h2; subst h2; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨codeAddress, devm2⟩, eq2, run⟩
    · rw [eq_exn]; exact (Devm.popToAdr_getCode_err h_err a).trans hc1
    have hc2 : devm2.getCode a = devm1.getCode a :=
      Devm.popToAdr_getCode_eq eq2 a
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨value, devm3⟩, eq3, run⟩
    · rw [eq_exn]; exact (Devm.pop_getCode_err h_err a).trans (hc2.trans hc1)
    have hc3 : devm3.getCode a = devm2.getCode a := by
      revert eq3; rw [Devm.pop_def]; split <;> intro eq3
      · contradiction
      · injection eq3 with h5; injection h5 with _ h6; subst h6; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨inputIndex, devm4⟩, eq4, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc3.trans (hc2.trans hc1))
    have hc4 : devm4.getCode a = devm3.getCode a := Devm.popToNat_getCode_eq eq4 a
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨inputSize, devm5⟩, eq5, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc4.trans (hc3.trans (hc2.trans hc1)))
    have hc5 : devm5.getCode a = devm4.getCode a := Devm.popToNat_getCode_eq eq5 a
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨outputIndex, devm6⟩, eq6, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1))))
    have hc6 : devm6.getCode a = devm5.getCode a := Devm.popToNat_getCode_eq eq6 a
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨outputSize, devm7⟩, eq7, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc6.trans (hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1)))))
    have hc7 : devm7.getCode a = devm6.getCode a := Devm.popToNat_getCode_eq eq7 a
    rcases run with ⟨extendCost, hp8, run⟩
    rcases run with ⟨preAccessCost, hp9, run⟩
    rcases run with ⟨devm8, hp10, run⟩
    have hc8 : devm8.getCode a = devm7.getCode a := by
      subst hp10; rw [addAccessedAddress_def]; rfl
    rcases run with ⟨⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm9⟩, hp11, run⟩
    have hc9 : devm9.getCode a = devm8.getCode a := by
      have h_acc := @accessDelegation_getCode devm8 codeAddress a
      rw [← hp11] at h_acc
      exact h_acc
    rcases run with ⟨accessCost, hp12, run⟩
    rcases run with ⟨transferCost, hp13, run⟩
    rcases run with ⟨⟨msgCallCost, msgCallStipend⟩, hp14, run⟩
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨devm10, eq15, run⟩
    · rw [eq_exn]; exact (chargeGas_getCode_err h_err a).trans (hc9.trans (hc8.trans (hc7.trans (hc6.trans (hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1))))))))
    have hc10 : devm10.getCode a = devm9.getCode a := by
      revert eq15; rw [chargeGas_def]; split <;> intro eq15
      · contradiction
      · injection eq15 with h15; subst h15; rfl
    rcases run with ⟨devm11, hp16, run⟩
    have hc11 : devm11.getCode a = devm10.getCode a := by
      subst hp16; dsimp [Devm.getCode, Devm.memExtends_def]; rfl
    rcases run with ⟨senderBal, hp17, run⟩
    split_ifs at run with h_bal
    · rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨devm12, eq20, h_xl2, h_ex⟩
      · rw [eq_exn]; exact (Devm.push_getCode_err h_err a).trans (hc11.trans (hc10.trans (hc9.trans (hc8.trans (hc7.trans (hc6.trans (hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1))))))))))
      have hc12 : devm12.getCode a = devm11.getCode a :=
        Devm.push_getCode_eq eq20 a
      have hc_final : exn.getCode a = devm12.getCode a := by
        rw [← h_ex]; rfl
      rw [hc_final, hc12, hc11, hc10, hc9, hc8, hc7, hc6, hc5, hc4, hc3, hc2, hc1]
    · have h_code : devm11.getCode a = devm.getCode a := by
        rw [hc11, hc10, hc9, hc8, hc7, hc6, hc5, hc4, hc3, hc2, hc1]
      have ha_11 : (devm11.getCode a).toList ≠ [] := by
        rw [h_code]; exact ha
      have h_gen := GenericCall.inv_getCode_gen inv run a ha_11
      rw [h_gen, h_code]
  case delcall =>
    dsimp [Xinst.Run] at run
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨gas, devm1⟩, eq1, run⟩
    · rw [eq_exn]; exact Devm.pop_getCode_err h_err a
    have hc1 : devm1.getCode a = devm.getCode a := by
      revert eq1; rw [Devm.pop_def]; split <;> intro eq1
      · contradiction
      · injection eq1 with h1; injection h1 with _ h2; subst h2; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨codeAddress, devm2⟩, eq2, run⟩
    · rw [eq_exn]; exact (Devm.popToAdr_getCode_err h_err a).trans hc1
    have hc2 : devm2.getCode a = devm1.getCode a :=
      Devm.popToAdr_getCode_eq eq2 a
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨inputIndex, devm3⟩, eq3, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc2.trans hc1)
    have hc3 : devm3.getCode a = devm2.getCode a := Devm.popToNat_getCode_eq eq3 a
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨inputSize, devm4⟩, eq4, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc3.trans (hc2.trans hc1))
    have hc4 : devm4.getCode a = devm3.getCode a := Devm.popToNat_getCode_eq eq4 a
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨outputIndex, devm5⟩, eq5, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc4.trans (hc3.trans (hc2.trans hc1)))
    have hc5 : devm5.getCode a = devm4.getCode a := Devm.popToNat_getCode_eq eq5 a
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨outputSize, devm6⟩, eq6, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1))))
    have hc6 : devm6.getCode a = devm5.getCode a := Devm.popToNat_getCode_eq eq6 a
    rcases run with ⟨extendCost, hp7, run⟩
    rcases run with ⟨preAccessCost, hp8, run⟩
    rcases run with ⟨devm7, hp9, run⟩
    have hc7 : devm7.getCode a = devm6.getCode a := by
      subst hp9; rw [addAccessedAddress_def]; rfl
    rcases run with ⟨⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm8⟩, hp10, run⟩
    have hc8 : devm8.getCode a = devm7.getCode a := by
      have h_acc := @accessDelegation_getCode devm7 codeAddress a
      rw [← hp10] at h_acc
      exact h_acc
    rcases run with ⟨accessCost, hp11, run⟩
    rcases run with ⟨⟨msgCallCost, msgCallStipend⟩, hp12, run⟩
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨devm9, eq13, run⟩
    · rw [eq_exn]; exact (chargeGas_getCode_err h_err a).trans (hc8.trans (hc7.trans (hc6.trans (hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1)))))))
    have hc9 : devm9.getCode a = devm8.getCode a := by
      revert eq13; rw [chargeGas_def]; split <;> intro eq13
      · contradiction
      · injection eq13 with h13; subst h13; rfl
    rcases run with ⟨devm10, hp14, run⟩
    have hc10 : devm10.getCode a = devm9.getCode a := by
      subst hp14; dsimp [Devm.getCode, Devm.memExtends_def]; rfl

    have h_code : devm10.getCode a = devm.getCode a := by
      rw [hc10, hc9, hc8, hc7, hc6, hc5, hc4, hc3, hc2, hc1]
    have ha_10 : (devm10.getCode a).toList ≠ [] := by
      rw [h_code]; exact ha
    have h_gen := GenericCall.inv_getCode_gen inv run a ha_10
    rw [h_gen, h_code]
  case create2 =>
    dsimp [Xinst.Run] at run
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨endowment, devm1⟩, eq1, run⟩
    · rw [eq_exn]; exact Devm.pop_getCode_err h_err a
    have hc1 : devm1.getCode a = devm.getCode a := by
      revert eq1; simp only [Devm.pop_def]; split <;> intro eq1
      · contradiction
      · injection eq1 with h1; injection h1 with _ h2; subst h2; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨memoryIndex, devm2⟩, eq2, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans hc1
    have hc2 : devm2.getCode a = devm1.getCode a := Devm.popToNat_getCode_eq eq2 a
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨memorySize, devm3⟩, eq3, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc2.trans hc1)
    have hc3 : devm3.getCode a = devm2.getCode a := Devm.popToNat_getCode_eq eq3 a
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨salt, devm4⟩, eq4, run⟩
    · rw [eq_exn]; exact (Devm.pop_getCode_err h_err a).trans (hc3.trans (hc2.trans hc1))
    have hc4 : devm4.getCode a = devm3.getCode a := by
      revert eq4; simp only [Devm.pop_def]; split <;> intro eq4
      · contradiction
      · injection eq4 with h7; injection h7 with _ h8; subst h8; rfl
    rcases run with ⟨extendCost, hp5, run⟩
    rcases run with ⟨initCodeHashCost, hp6, run⟩
    rcases run with ⟨initCodeCost, hp7, run⟩
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨devm5, eq8, run⟩
    · rw [eq_exn]; exact (chargeGas_getCode_err h_err a).trans (hc4.trans (hc3.trans (hc2.trans hc1)))
    have hc5 : devm5.getCode a = devm4.getCode a := by
      revert eq8; rw [chargeGas_def]; split <;> intro eq8
      · contradiction
      · injection eq8 with h9; subst h9; rfl
    rcases run with ⟨devm6, hp9, run⟩
    have hc6 : devm6.getCode a = devm5.getCode a := by
      subst hp9; dsimp [Devm.getCode, Devm.memExtends_def]; rfl
    rcases run with ⟨newAddress, hp10, run⟩

    have h_code : devm6.getCode a = devm.getCode a := by
      rw [hc6, hc5, hc4, hc3, hc2, hc1]
    have ha_6 : (devm6.getCode a).toList ≠ [] := by
      rw [h_code]; exact ha
    have h_gen := GenericCreate.inv_getCode_gen inv run a ha_6
    rw [h_gen, h_code]
  case statcall =>
    dsimp [Xinst.Run] at run
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨gas, devm1⟩, eq1, run⟩
    · rw [eq_exn]; exact Devm.pop_getCode_err h_err a
    have hc1 : devm1.getCode a = devm.getCode a := by
      revert eq1; rw [Devm.pop_def]; split <;> intro eq1
      · contradiction
      · injection eq1 with h1; injection h1 with _ h2; subst h2; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨target, devm2⟩, eq2, run⟩
    · rw [eq_exn]; exact (Devm.popToAdr_getCode_err h_err a).trans hc1
    have hc2 : devm2.getCode a = devm1.getCode a :=
      Devm.popToAdr_getCode_eq eq2 a
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨inputIndex, devm3⟩, eq3, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc2.trans hc1)
    have hc3 : devm3.getCode a = devm2.getCode a := Devm.popToNat_getCode_eq eq3 a
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨inputSize, devm4⟩, eq4, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc3.trans (hc2.trans hc1))
    have hc4 : devm4.getCode a = devm3.getCode a := Devm.popToNat_getCode_eq eq4 a
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨outputIndex, devm5⟩, eq5, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc4.trans (hc3.trans (hc2.trans hc1)))
    have hc5 : devm5.getCode a = devm4.getCode a := Devm.popToNat_getCode_eq eq5 a
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨outputSize, devm6⟩, eq6, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1))))
    have hc6 : devm6.getCode a = devm5.getCode a := Devm.popToNat_getCode_eq eq6 a
    rcases run with ⟨extendCost, hp7, run⟩
    rcases run with ⟨preAccessCost, hp8, run⟩
    rcases run with ⟨devm7, hp9, run⟩
    have hc7 : devm7.getCode a = devm6.getCode a := by
      subst hp9; rw [addAccessedAddress_def]; rfl
    rcases run with ⟨⟨disablePrecompiles, _, code, delegatedAccessGasCost, devm8⟩, hp10, run⟩
    have hc8 : devm8.getCode a = devm7.getCode a := by
      have h_acc := @accessDelegation_getCode devm7 target a
      rw [← hp10] at h_acc
      exact h_acc
    rcases run with ⟨accessCost, hp11, run⟩
    rcases run with ⟨⟨msgCallCost, msgCallStipend⟩, hp12, run⟩
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨devm9, eq13, run⟩
    · rw [eq_exn]; exact (chargeGas_getCode_err h_err a).trans (hc8.trans (hc7.trans (hc6.trans (hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1)))))))
    have hc9 : devm9.getCode a = devm8.getCode a := by
      revert eq13; rw [chargeGas_def]; split <;> intro eq13
      · contradiction
      · injection eq13 with h13; subst h13; rfl
    rcases run with ⟨devm10, hp14, run⟩
    have hc10 : devm10.getCode a = devm9.getCode a := by
      subst hp14; dsimp [Devm.getCode, Devm.memExtends_def]; rfl

    have h_code : devm10.getCode a = devm.getCode a := by
      rw [hc10, hc9, hc8, hc7, hc6, hc5, hc4, hc3, hc2, hc1]
    have ha_10 : (devm10.getCode a).toList ≠ [] := by
      rw [h_code]; exact ha
    have h_gen := GenericCall.inv_getCode_gen inv run a ha_10
    rw [h_gen, h_code]

lemma Jinst.inv_getCode
    {pc sevm devm j pc' devm'}
    (run : Jinst.Run ⟨pc, sevm, devm⟩ j (.ok ⟨pc', devm'⟩)) (a : Adr) :
    devm'.getCode a = devm.getCode a := by
  have hf := Jinst.run_instructionFrame ⟨pc, sevm, devm⟩ j
  rw [run] at hf
  exact (hf.getCode a).symm

def JumpResult.getCode (ex : Except (String × Devm) (Nat × Devm)) (a : Adr) : ByteArray :=
  match ex with
  | .ok ⟨_, devm⟩ => devm.getCode a
  | .error ⟨_, devm⟩ => devm.getCode a

lemma Jinst.inv_getCode_gen
    {pc sevm devm j ex}
    (run : Jinst.Run ⟨pc, sevm, devm⟩ j ex) :
    ∀ a : Adr, JumpResult.getCode ex a = devm.getCode a := by
  intro a
  have hf := Jinst.run_instructionFrame ⟨pc, sevm, devm⟩ j
  rw [run] at hf
  cases ex <;> exact (hf.getCode a).symm

lemma Linst.dest_inv_getCode {sevm : Sevm} {devm : Devm} {exn : Execution}
    (run : Linst.Run sevm devm .dest exn) :
    ∀ adr : Adr, exn.getCode adr = devm.getCode adr := by
  intro adr
  dsimp [Linst.Run, Linst.run] at run
  revert run
  dsimp [bind, Except.bind]
  cases h1 : devm.popToAdr <;> dsimp
  case error err =>
    intro run; rw [← run]; exact (Devm.popToAdr_getCode_err h1 adr)
  case ok res1 =>
    have h_acc : (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).1.getCode adr = res1.2.getCode adr := by
      split
      · exact addAccessedAddress_getCode
      · rfl
    cases h2 : chargeGas (if ((if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).1.getAcct res1.1).Empty ∧ ¬(res1.2.getAcct sevm.currentTarget).bal = 0 then (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).2 + gasSelfDestructNewAccount else (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).2) (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).1 <;> dsimp
    case error err =>
      intro run; rw [← run]
      change err.2.getCode adr = devm.getCode adr
      exact (chargeGas_getCode_err h2 adr).trans (h_acc.trans (Devm.popToAdr_getCode_eq h1 adr))
    case ok res2 =>
      cases h3 : assertDynamic sevm res2
      case error err =>
        intro run; rw [← run]
        dsimp [assertDynamic, Except.assert] at h3
        split at h3
        · contradiction
        · simp only [Except.error.injEq] at h3; subst h3
          change res2.getCode adr = devm.getCode adr
          exact (chargeGas_getCode_eq h2 adr).trans (h_acc.trans (Devm.popToAdr_getCode_eq h1 adr))
      case ok _ =>
        cases h4 : res2.subBal sevm.currentTarget (res1.2.getAcct sevm.currentTarget).bal <;> dsimp [Option.toExcept]
        case none =>
          intro run; rw [← run]
          change res2.getCode adr = devm.getCode adr
          exact (chargeGas_getCode_eq h2 adr).trans (h_acc.trans (Devm.popToAdr_getCode_eq h1 adr))
        case some res3 =>
          have h_sub : res3.getCode adr = res2.getCode adr := by
            dsimp [Devm.subBal] at h4
            cases h_st : res2.state.subBal sevm.currentTarget (res1.2.getAcct sevm.currentTarget).bal
            case none =>
              rw [h_st] at h4; contradiction
            case some st =>
              rw [h_st] at h4; dsimp at h4
              simp only [Option.some.injEq] at h4; subst h4
              change st.getCode adr = res2.getCode adr
              exact State.subBal_getCode h_st
          by_cases h_if : sevm.currentTarget ∈ (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).createdAccounts
          · simp only [h_if, if_pos]
            intro run; rw [← run]
            change (addAccountToDelete _ _).getCode adr = devm.getCode adr
            have h_add : (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).getCode adr = res3.getCode adr := by
              dsimp [Devm.addBal, Devm.getCode]; exact State.addBal_getCode res3.state _ _ _
            have h_set : ((res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).setBal sevm.currentTarget 0).getCode adr = (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).getCode adr := by
              dsimp [Devm.setBal, Devm.getCode]; exact State.setBal_getCode _ _ _ _
            have h_del : (addAccountToDelete ((res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).setBal sevm.currentTarget 0) sevm.currentTarget).getCode adr = ((res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).setBal sevm.currentTarget 0).getCode adr := by
              rfl
            exact h_del.trans (h_set.trans (h_add.trans (h_sub.trans ((chargeGas_getCode_eq h2 adr).trans (h_acc.trans (Devm.popToAdr_getCode_eq h1 adr))))))
          · simp only [h_if]
            intro run; rw [← run]
            change (res3.addBal _ _).getCode adr = devm.getCode adr
            have h_add : (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).getCode adr = res3.getCode adr := by
              dsimp [Devm.addBal, Devm.getCode]; exact State.addBal_getCode res3.state _ _ _
            exact h_add.trans (h_sub.trans ((chargeGas_getCode_eq h2 adr).trans (h_acc.trans (Devm.popToAdr_getCode_eq h1 adr))))

theorem Linst.run_codeFrame {sevm : Sevm} {devm : Devm} {l : Linst}
    {exn : Execution} (run : Linst.Run sevm devm l exn) :
    Execution.Rel Devm.CodeFrame devm exn := by
  rcases eq_or_ne l .dest with rfl | h_not_dest
  · cases exn <;> exact Linst.dest_inv_getCode run
  · have hf := Linst.run_instructionFrame sevm devm l h_not_dest
    rw [run] at hf
    cases exn <;> exact fun a => (hf.getCode a).symm

lemma Linst.inv_getCode
    {sevm devm l exn}
    (run : Linst.Run sevm devm l exn) :
    ∀ adr : Adr, exn.getCode adr = devm.getCode adr := by
  have hf := Linst.run_codeFrame run
  cases exn <;> exact hf

/-! ## World-preserving footprint lifts -/

lemma Footprint.liftOutcome_worldEq
    (get : Devm → σ) (set : Devm → σ → Devm)
    (core : σ → Footprint.Outcome σ α) (d : Devm)
    (hset : ∀ view, Devm.WorldEq d (set d view)) :
    Outcome.Rel Prod.snd Prod.snd Devm.WorldEq d
      (Footprint.liftOutcome get set core d) := by
  unfold Footprint.liftOutcome
  cases core (get d) <;> exact hset _

lemma liftMach_worldEq (core : Mach → Footprint.Outcome Mach α) (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.WorldEq d (liftMach core d) := by
  unfold liftMach
  exact Footprint.liftOutcome_worldEq _ _ _ _ (Devm.worldEq_setMach d)

lemma liftMachExecution_worldEq
    (core : Mach → Footprint.Outcome Mach Unit) (d : Devm) :
    Execution.Rel Devm.WorldEq d (liftMachExecution core d) := by
  unfold liftMachExecution
  exact outcomeRel_toExecution (liftMach_worldEq core d)

lemma liftMachMeta_worldEq
    (core : Mach → Meta → Footprint.Outcome (Mach × Meta) α) (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.WorldEq d (liftMachMeta core d) := by
  unfold liftMachMeta
  exact Footprint.liftOutcome_worldEq _ _ _ _ (Devm.worldEq_setMachMeta d)

lemma liftMachMetaExecution_worldEq
    (core : Mach → Meta → Footprint.Outcome (Mach × Meta) Unit) (d : Devm) :
    Execution.Rel Devm.WorldEq d (liftMachMetaExecution core d) := by
  unfold liftMachMetaExecution
  exact outcomeRel_toExecution (liftMachMeta_worldEq core d)

lemma liftMachMetaWorldExecution_worldEq
    (core : World → Mach → Meta → Footprint.Outcome (Mach × Meta) Unit)
    (d : Devm) :
    Execution.Rel Devm.WorldEq d (liftMachMetaWorldExecution core d) := by
  exact liftMachMetaExecution_worldEq _ _

/-- `BALANCE` preserves the world because its named core is lifted with
    read-only access to `World`; no account-operation unfolding is needed. -/
lemma Rinst.balance_worldEq (pc : Nat) (sevm : Sevm) (d : Devm) :
    Execution.Rel Devm.WorldEq d (Rinst.runCore pc d sevm .balance) := by
  simpa only [Rinst.runCore] using
    (liftMachMetaWorldExecution_worldEq Rinst.balanceCore d)

def Xlot.Rel (R : Devm → Devm → Prop) : Xlot → Prop
  | .none => True
  | .some ⟨_, pre, out⟩ => Execution.Rel R pre out

def Rinst.Effect (R : Devm → Devm → Prop) (r : Rinst) : Prop :=
  ∀ {pc sevm pre out},
    Rinst.run ⟨pc, sevm, pre⟩ r = out → Execution.Rel R pre out

def Jinst.Effect (R : Devm → Devm → Prop) (j : Jinst) : Prop :=
  ∀ {evm out},
    Jinst.Run evm j out →
      Outcome.Rel Prod.snd Prod.snd R evm.dyna out

def Linst.Effect (R : Devm → Devm → Prop) (l : Linst) : Prop :=
  ∀ {sevm pre out},
    Linst.Run sevm pre l out → Execution.Rel R pre out

def Xinst.EffectGen (R : Devm → Devm → Prop) (x : Xinst) : Prop :=
  ∀ {sevm pre xl out},
    Xlot.Rel R xl → Xinst.Run sevm pre x xl out → Execution.Rel R pre out

def Ninst.EffectGen (R : Devm → Devm → Prop) (n : Ninst) : Prop :=
  ∀ {pc sevm pre xl out},
    Xlot.Rel R xl → Ninst.Run' pc sevm pre n xl out → Execution.Rel R pre out

def Ninst.Effect (R : Devm → Devm → Prop) (n : Ninst) : Prop :=
  ∀ {sevm pre post}, Ninst.Run sevm pre n post → R pre post

def Func.Effect (R : Devm → Devm → Prop) (p : Func) : Prop :=
  ∀ {fs sevm pre post}, Func.Run fs sevm pre p post → R pre post

lemma Ninst.effectGen_reg {R : Devm → Devm → Prop} {r : Rinst}
    (hr : Rinst.Effect R r) : Ninst.EffectGen R (.reg r) := by
  intro pc sevm pre xl out hxl hrun
  cases xl with
  | none => exact hr hrun
  | some val => exact False.elim hrun

lemma Ninst.effectGen_exec {R : Devm → Devm → Prop} {x : Xinst}
    (hx : Xinst.EffectGen R x) : Ninst.EffectGen R (.exec x) := by
  intro pc sevm pre xl out hxl hrun
  exact hx hxl hrun

/-
Future proofs for properties of `Exec` should use this theorem,
instead of repeating an `Exec.rec` traversal.
-/
theorem Exec.effect {R : Devm → Devm → Prop}
    (hrefl : Reflexive R) (htrans : Transitive R)
    (hn : ∀ n, Ninst.EffectGen R n)
    (hj : ∀ j, Jinst.Effect R j)
    (hl : ∀ l, Linst.Effect R l)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : Execution.Rel R pre out := by
  have hcomp : ∀ {a b : Devm} {o : Execution},
      R a b → Execution.Rel R b o → Execution.Rel R a o := by
    intro a b o hab hbo
    cases o <;> exact htrans hab hbo
  induction run with
  | invOp h => exact hrefl _
  | nextNoneErr hAt hRun =>
    exact hn _ (xl := .none) (by trivial) hRun
  | nextSomeErr hAt hRun hExec ih =>
    exact hn _ (xl := .some ⟨_, _, _⟩) ih hRun
  | nextNoneRec hAt hRun hExec ih =>
    exact hcomp (hn _ (xl := .none) (by trivial) hRun) ih
  | nextSomeRec hAt hRun hExecSub hExec ihSub ih =>
    exact hcomp (hn _ (xl := .some ⟨_, _, _⟩) ihSub hRun) ih
  | jumpErr hAt hRun => exact hj _ hRun
  | jumpRec hAt hRun hExec ih =>
    exact hcomp (hj _ hRun) ih
  | last hAt hRun => exact hl _ hRun

lemma Xlot.rel_of_filled {R : Devm → Devm → Prop}
    (hrefl : Reflexive R) (htrans : Transitive R)
    (hn : ∀ n, Ninst.EffectGen R n)
    (hj : ∀ j, Jinst.Effect R j)
    (hl : ∀ l, Linst.Effect R l)
    {xl : Xlot} (hfilled : xl.Filled) : Xlot.Rel R xl := by
  cases xl with
  | none => trivial
  | some tuple =>
    rcases tuple with ⟨sevm, pre, out⟩
    rcases hfilled with ⟨hrun⟩
    exact Exec.effect hrefl htrans hn hj hl hrun

lemma Ninst.effect_of_effectGen {R : Devm → Devm → Prop}
    (hrefl : Reflexive R) (htrans : Transitive R)
    (hn : ∀ n, Ninst.EffectGen R n)
    (hj : ∀ j, Jinst.Effect R j)
    (hl : ∀ l, Linst.Effect R l) :
    ∀ n, Ninst.Effect R n := by
  intro n sevm pre post hrun
  rcases hrun with ⟨xl, hfilled, pc, hrun'⟩
  have hrel := Xlot.rel_of_filled hrefl htrans hn hj hl hfilled
  exact hn n hrel hrun'

theorem Func.effect {R : Devm → Devm → Prop}
    (htrans : Transitive R)
    (hpop : ∀ xs pre post, Devm.PopBurn xs pre post → R pre post)
    (hburn : ∀ pre post, Devm.Burn pre post → R pre post)
    (hn : ∀ n, Ninst.Effect R n)
    (hl : ∀ l, Linst.Effect R l)
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {p : Func}
    (run : Func.Run fs sevm pre p post) : R pre post := by
  induction run with
  | zero pop run' ih =>
    exact htrans (hpop _ _ _ pop) ih
  | succ neq pop burn run' ih =>
    exact htrans (hpop _ _ _ pop) (htrans (hburn _ _ burn) ih)
  | last run' =>
    exact hl _ run'
  | next runi run' ih =>
    exact htrans (hn _ runi) ih
  | call eq burn run' ih =>
    exact htrans (hburn _ _ burn) ih

lemma Ninst.effect_obsEq_iff_inv {α : Type} (obs : Devm → α) (n : Ninst) :
    Ninst.Effect (CEffect.ObsEq obs) n ↔ Ninst.Inv obs n := by
  unfold Ninst.Effect CEffect.ObsEq Ninst.Inv
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-
This bridge is what allows existing program-level frame
proofs to migrate incrementally to the new relational traversal.
-/
lemma Func.effect_obsEq_iff_inv {α : Type} (obs : Devm → α) (p : Func) :
    Func.Effect (CEffect.ObsEq obs) p ↔ Func.Inv obs obs p := by
  exact Iff.rfl

-- Relational form of code preservation: nonempty code is never modified.
def Devm.CodePreserve (pre post : Devm) : Prop :=
  ∀ a : Adr, (pre.getCode a).toList ≠ [] → post.getCode a = pre.getCode a

lemma codePreserve_refl_trans :
    Reflexive Devm.CodePreserve ∧ Transitive Devm.CodePreserve := by
  constructor
  · intro d a _; rfl
  · intro a b c hab hbc adr ha
    have h1 := hab adr ha
    have h2 : (b.getCode adr).toList ≠ [] := by rw [h1]; exact ha
    exact (hbc adr h2).trans h1

lemma Xlot.rel_mono {R S : Devm → Devm → Prop}
    (hRS : CEffect.Refines R S) {xl : Xlot} (h : Xlot.Rel R xl) :
    Xlot.Rel S xl := by
  rcases xl with _ | ⟨sevm, devm, exn⟩
  · trivial
  · exact Outcome.Rel.mono hRS h

lemma Xlot.invGetCode_of_rel {xl : Xlot}
    (h : Xlot.Rel Devm.CodePreserve xl) : xl.InvGetCode := by
  rcases xl with _ | ⟨sevm, devm, exn⟩
  · trivial
  · intro a ha
    cases exn with
    | error e => exact (h a ha).symm
    | ok d => exact (h a ha).symm

lemma Rinst.codePreserve_effect (r : Rinst) :
    Rinst.Effect Devm.CodePreserve r := by
  intro pc sevm pre out hrun
  have h := Rinst.inv_getCode_gen hrun
  cases out <;> exact fun a ha => h a ha

lemma Xinst.codePreserve_effectGen (x : Xinst) :
    Xinst.EffectGen Devm.CodePreserve x := by
  intro sevm pre xl out hxl hrun
  have h := Xinst.inv_getCode_gen (Xlot.invGetCode_of_rel hxl) hrun
  cases out with
  | error e => exact fun a ha => h a ha
  | ok d => exact fun a ha => h a ha

lemma Ninst.push_instructionFrame_effectGen
    {xs : B8L} {hxs : xs.length ≤ 32} :
    Ninst.EffectGen Devm.InstructionFrame (.push xs hxs) := by
  intro pc sevm pre xl out hxl hRun
  cases xl with
  | none =>
      have hf : Execution.Rel Devm.InstructionFrame pre (do
          let d ← chargeGas (if xs = [] then gBase else gVerylow) pre
          d.push xs.toB256) := by
        apply Execution.Rel.bind Devm.instructionFrame_trans
          (chargeGas_instructionFrame
            (if xs = [] then gBase else gVerylow) pre)
        exact Devm.push_instructionFrame xs.toB256
      rw [hRun] at hf
      exact hf
  | some x => exact False.elim hRun

lemma Ninst.push_worldEq_effectGen {xs : B8L} {hxs : xs.length ≤ 32} :
    Ninst.EffectGen Devm.WorldEq (.push xs hxs) := by
  intro pc sevm pre xl out hxl hRun
  cases xl with
  | none =>
      exact Outcome.Rel.mono
        (show CEffect.Refines Devm.InstructionFrame Devm.WorldEq from
          fun _ _ h => h.worldEq)
        (Ninst.push_instructionFrame_effectGen (hxs := hxs) (xl := .none)
          trivial hRun)
  | some x => exact False.elim hRun

lemma Ninst.push_effectGen_of_worldEq {R : Devm → Devm → Prop}
    {xs : B8L} {hxs : xs.length ≤ 32}
    (hWR : CEffect.Refines Devm.WorldEq R) :
    Ninst.EffectGen R (.push xs hxs) := by
  intro pc sevm pre xl out hxl hRun
  cases xl
  · exact Outcome.Rel.mono hWR
      (Ninst.push_worldEq_effectGen (hxs := hxs) (xl := .none) trivial hRun)
  · simp only [Ninst.Run'] at hRun

lemma Ninst.push_effectGen_of_instructionFrame
    {R : Devm → Devm → Prop} {xs : B8L} {hxs : xs.length ≤ 32}
    (hIR : CEffect.Refines Devm.InstructionFrame R) :
    Ninst.EffectGen R (.push xs hxs) := by
  intro pc sevm pre xl out hxl hRun
  cases xl with
  | none =>
      apply Outcome.Rel.mono hIR
      exact Ninst.push_instructionFrame_effectGen (hxs := hxs) (xl := .none)
        trivial hRun
  | some x => exact False.elim hRun

lemma Ninst.push_codePreserve_effectGen {xs : B8L} {hxs : xs.length ≤ 32} :
  Ninst.EffectGen Devm.CodePreserve (.push xs hxs) := by
  exact Ninst.push_effectGen_of_instructionFrame (R := Devm.CodePreserve)
    (fun _ _ hf a _ => (hf.getCode a).symm)

lemma Ninst.codePreserve_effectGen (n : Ninst) :
    Ninst.EffectGen Devm.CodePreserve n := by
  cases n with
  | reg r =>
    exact Ninst.effectGen_reg (Rinst.codePreserve_effect r)
  | exec x =>
    exact Ninst.effectGen_exec (Xinst.codePreserve_effectGen x)
  | push xs hxs =>
    exact Ninst.push_codePreserve_effectGen

lemma Jinst.codePreserve_effect (j : Jinst) :
    Jinst.Effect Devm.CodePreserve j := by
  intro evm out hrun
  have hf := Jinst.run_instructionFrame evm j
  rw [hrun] at hf
  cases out <;> exact fun a _ => (hf.getCode a).symm

lemma Linst.codePreserve_effect (l : Linst) :
    Linst.Effect Devm.CodePreserve l := by
  intro sevm pre out hrun
  have hf := Linst.run_codeFrame hrun
  cases out <;> exact fun a _ => hf a

lemma Exec.inv_getCode {pc} {sevm} {devm} {exn}
    (run : Exec pc sevm devm exn) :
    ∀ a : Adr,
      (devm.getCode a).toList ≠ [] →
      exn.getCode a = devm.getCode a := by
  intro a ha
  have h := Exec.effect codePreserve_refl_trans.1 codePreserve_refl_trans.2
    Ninst.codePreserve_effectGen Jinst.codePreserve_effect
    Linst.codePreserve_effect run
  cases exn with
  | error e => exact h a ha
  | ok d => exact h a ha

lemma not_empty_of_compile {p : Prog} {code : ByteArray} (h : some code.toList = Prog.compile p) : code ≠ .empty := by
  intro hc
  have h_ne : Prog.compile p ≠ some [] := Prog.compile_ne_nil
  rw [←h, hc] at h_ne
  have h_empty_toList : ByteArray.empty.toList = [] := by
    unfold ByteArray.toList
    unfold ByteArray.toList.loop
    rfl
  rw [h_empty_toList] at h_ne
  exact h_ne rfl

lemma not_delegation_of_compile {p : Prog} {code : ByteArray}
    (h : some code.toList = Prog.compile p) : ¬ isValidDelegation code := by
  unfold isValidDelegation
  unfold Prog.compile at h
  unfold table at h
  simp only [Table.compile] at h
  simp only [bind] at h
  symm at h
  rcases of_bind_eq_some h with ⟨bs, h_bs, h'⟩
  rcases of_bind_eq_some h' with ⟨bss, h_bss, h_eq⟩
  injection h_eq with h_eq
  intro h_del
  rcases h_del with ⟨h_size, h_slice⟩
  have h_slice_eq : code.sliceD 0 3 0 = code.toList.sliceD 0 3 0 := ByteArray.sliceD_eq _ _ _ _
  rw [h_slice_eq, ←h_eq, eoaDelegationMarker] at h_slice
  revert h_slice
  simp only [List.sliceD]
  intro h_false
  injection h_false with h_false
  change (91 : B8) = 239 at h_false
  contradiction

lemma lift_core
    (ε : Exec.Pred)
    (π : Sevm → Devm → Devm → Prop)
    ( analog :
      ∀ {sevm pre post}
        (ex : Exec 0 sevm pre (.ok post)),
        π sevm pre post →
        ε 0 sevm pre (.ok post) ex )
    (ca : Adr) (p : Prog)
    ( depth_ind :
      ∀ {sevm pre post},
        Prog.Run sevm pre p post →
        sevm.currentTarget = ca →
        ForallDeeperAt sevm.depth ca p ε →
        π sevm pre post )
    ( errAtTarget :
      ∀ {pc sevm devm err devm'} (ex : Exec pc sevm devm (.error ⟨err, devm'⟩)),
        sevm.currentTarget = ca →
        ε pc sevm devm (.error ⟨err, devm'⟩) ex )
    ( invOp :
      ∀ {pc sevm devm}
        (h_get : sevm.code.getInst pc = none),
        sevm.currentTarget ≠ ca →
        ε pc sevm devm (.error ⟨"InvalidOpcode", devm⟩) (.invOp h_get) )
    ( nextNoneErr :
      ∀ {pc sevm devm n err devm'}
        (h_at : n.At sevm.code pc)
        (h_run : Ninst.Run' pc sevm devm n .none (.error ⟨err, devm'⟩)),
        sevm.currentTarget ≠ ca →
        ε pc sevm devm (.error ⟨err, devm'⟩) (.nextNoneErr h_at h_run) )
    ( nextSomeErr :
      ∀ {pc sevm devm n sevm_ devm_ exn_ err devm'}
        (h_at : n.At sevm.code pc)
        (h_run : Ninst.Run' pc sevm devm n (.some ⟨sevm_, devm_, exn_⟩) (.error ⟨err, devm'⟩))
        (ex_sub : Exec 0 sevm_ devm_ exn_),
        sevm.currentTarget ≠ ca →
        ε 0 sevm_ devm_ exn_ ex_sub →
        ε pc sevm devm (.error ⟨err, devm'⟩) (.nextSomeErr h_at h_run ex_sub) )
    ( nextNoneRec :
      ∀ {pc sevm devm n devm' exn}
        (h_at : n.At sevm.code pc)
        (h_run : Ninst.Run' pc sevm devm n .none (.ok devm'))
        (ex : Exec (pc + n.size) sevm devm' exn),
        sevm.currentTarget ≠ ca →
        ε (pc + n.size) sevm devm' exn ex →
        ε pc sevm devm exn (.nextNoneRec h_at h_run ex) )
    ( nextSomeRec :
      ∀ {pc sevm devm n sevm_ devm_ exn_ devm' exn}
        (h_at : n.At sevm.code pc)
        (h_run : Ninst.Run' pc sevm devm n (.some ⟨sevm_, devm_, exn_⟩) (.ok devm'))
        (ex_sub : Exec 0 sevm_ devm_ exn_)
        (ex : Exec (pc + n.size) sevm devm' exn),
        sevm.currentTarget ≠ ca →
        ε 0 sevm_ devm_ exn_ ex_sub →
        ε (pc + n.size) sevm devm' exn ex →
        ε pc sevm devm exn (.nextSomeRec h_at h_run ex_sub ex) )
    ( jumpErr :
      ∀ {pc sevm devm j err devm'}
        (h_at : j.At sevm.code pc)
        (h_run : Jinst.Run ⟨pc, sevm, devm⟩ j (.error ⟨err, devm'⟩)),
        sevm.currentTarget ≠ ca →
        ε pc sevm devm (.error ⟨err, devm'⟩) (.jumpErr h_at h_run) )
    ( jumpRec :
      ∀ {pc sevm devm j pc' devm' exn}
        (h_at : j.At sevm.code pc)
        (h_run : Jinst.Run ⟨pc, sevm, devm⟩ j (.ok ⟨pc', devm'⟩))
        (ex : Exec pc' sevm devm' exn),
        sevm.currentTarget ≠ ca →
        ε pc' sevm devm' exn ex →
        ε pc sevm devm exn (.jumpRec h_at h_run ex) )
    ( last :
      ∀ {pc sevm devm l exn}
        (h_at : l.At sevm.code pc)
        (h_run : Linst.Run sevm devm l exn),
        sevm.currentTarget ≠ ca →
        ε pc sevm devm exn (.last h_at h_run) )
    : Exec.Fa (Exec.Wkn ca p ε) := by
  apply Exec.strong_rec
  apply @Exec.rec (Fortify (Exec.Wkn ca p ε))
  · intro pc sevm devm h_get h_fa h_at_p
    rcases em (sevm.currentTarget = ca) with h_eq | h_ne
    · exact errAtTarget (.invOp h_get) h_eq
    · exact invOp h_get h_ne
  · intro pc sevm devm n err devm' h_at h_run h_fa h_at_p
    rcases em (sevm.currentTarget = ca) with h_eq | h_ne
    · exact errAtTarget (.nextNoneErr h_at h_run) h_eq
    · exact nextNoneErr h_at h_run h_ne
  · intro pc sevm devm n sevm_ devm_ exn_ err devm' h_at h_run ex_sub ih_sub h_fa h_at_p
    rcases em (sevm.currentTarget = ca) with h_eq | h_ne
    · exact errAtTarget (.nextSomeErr h_at h_run ex_sub) h_eq
    · apply nextSomeErr h_at h_run ex_sub h_ne
      have h_lt : sevm_.depth < sevm.depth := Ninst.depth_lt_of_run'_some h_run
      have h_sub_wkn := h_fa 0 sevm_ devm_ exn_ ex_sub h_lt
      have h1 : some (devm_.getCode ca).toList = Prog.compile p := by
        have h_ne_code : (devm.getCode ca).toList ≠ [] := fun hc => Prog.compile_ne_nil (Eq.trans h_at_p.left.symm (congrArg some hc))
        rw [Ninst.prep_inv_getCode h_run ca]
        exact h_at_p.left
      have h2 : sevm_.currentTarget = ca → some sevm_.code.toList = Prog.compile p ∧ 0 = 0 := by
        intro h_ca
        rw [Ninst.prep_inv_code _ _ _ h_run, h_ca]
        · exact ⟨h_at_p.left, rfl⟩
        · rw [h_ca]; assumption
        · rw [h_ca]; exact not_empty_of_compile h_at_p.left
        · rw [h_ca, ← Ninst.prep_inv_getCode h_run ca]
          exact not_delegation_of_compile h1
      exact h_sub_wkn ⟨h1, h2⟩
  · intro pc sevm devm n devm' exn h_at h_run ex_next ih_next h_fa h_at_p
    rcases em (sevm.currentTarget = ca) with h_eq | h_ne
    · cases exn with
      | error e => exact errAtTarget (.nextNoneRec h_at h_run ex_next) h_eq
      | ok post =>
        have h_pc : pc = 0 := (h_at_p.right h_eq).right
        subst h_pc
        have h_run_prog := correct sevm devm p post (.nextNoneRec h_at h_run ex_next) (h_at_p.right h_eq).left
        have h_fa_deeper : ForallDeeperAt sevm.depth ca p ε := by
          intro pc' sevm' devm' exn' ex' h_lt
          exact h_fa pc' sevm' devm' exn' ex' h_lt
        exact analog (.nextNoneRec h_at h_run ex_next) (depth_ind h_run_prog h_eq h_fa_deeper)
    · have h_ne_code : (devm.getCode ca).toList ≠ [] := fun hc => Prog.compile_ne_nil (Eq.trans h_at_p.left.symm (congrArg some hc))
      have h_inv : devm'.getCode ca = devm.getCode ca :=
        Ninst.codePreserve_effectGen n (xl := .none) trivial h_run ca h_ne_code
      exact
        nextNoneRec h_at h_run ex_next h_ne (ih_next h_fa ⟨by rw [h_inv]; exact h_at_p.left, fun hc => (h_ne hc).elim⟩)
  · intro pc sevm devm n sevm_ devm_ exn_ devm' exn h_at h_run ex_sub ex_next ih_sub ih_next h_fa h_at_p
    rcases em (sevm.currentTarget = ca) with h_eq | h_ne
    · cases exn with
      | error e => exact errAtTarget (.nextSomeRec h_at h_run ex_sub ex_next) h_eq
      | ok post =>
        have h_pc : pc = 0 := (h_at_p.right h_eq).right
        subst h_pc
        have h_run_prog := correct sevm devm p post (.nextSomeRec h_at h_run ex_sub ex_next) (h_at_p.right h_eq).left
        have h_fa_deeper : ForallDeeperAt sevm.depth ca p ε := by
          intro pc' sevm' devm' exn' ex' h_lt
          exact h_fa pc' sevm' devm' exn' ex' h_lt
        exact analog (.nextSomeRec h_at h_run ex_sub ex_next) (depth_ind h_run_prog h_eq h_fa_deeper)
    · apply nextSomeRec h_at h_run ex_sub ex_next h_ne
      · have h_lt : sevm_.depth < sevm.depth := Ninst.depth_lt_of_run'_some h_run
        have h_sub_wkn := h_fa 0 sevm_ devm_ exn_ ex_sub h_lt
        have h1 : some (devm_.getCode ca).toList = Prog.compile p := by
          have h_ne_code : (devm.getCode ca).toList ≠ [] := fun hc => Prog.compile_ne_nil (Eq.trans h_at_p.left.symm (congrArg some hc))
          rw [Ninst.prep_inv_getCode h_run ca]
          exact h_at_p.left
        have h2 : sevm_.currentTarget = ca → some sevm_.code.toList = Prog.compile p ∧ 0 = 0 := by
          intro h_ca
          rw [Ninst.prep_inv_code _ _ _ h_run, h_ca]
          · exact ⟨h_at_p.left, rfl⟩
          · rw [h_ca]; assumption
          · rw [h_ca]; exact not_empty_of_compile h_at_p.left
          · rw [h_ca, ← Ninst.prep_inv_getCode h_run ca]
            exact not_delegation_of_compile h1
        exact h_sub_wkn ⟨h1, h2⟩
      · have h_ne_code : (devm.getCode ca).toList ≠ [] := fun hc => Prog.compile_ne_nil (Eq.trans h_at_p.left.symm (congrArg some hc))
        have hrel : Xlot.Rel Devm.CodePreserve (some ⟨sevm_, devm_, exn_⟩) :=
          Exec.effect codePreserve_refl_trans.1 codePreserve_refl_trans.2
            Ninst.codePreserve_effectGen Jinst.codePreserve_effect
            Linst.codePreserve_effect ex_sub
        have h_inv : devm'.getCode ca = devm.getCode ca :=
          Ninst.codePreserve_effectGen n hrel h_run ca h_ne_code
        exact ih_next h_fa ⟨by rw [h_inv]; exact h_at_p.left, fun hc => (h_ne hc).elim⟩
  · intro pc sevm devm j err devm' h_at h_run h_fa h_at_p
    rcases em (sevm.currentTarget = ca) with h_eq | h_ne
    · exact errAtTarget (.jumpErr h_at h_run) h_eq
    · exact jumpErr h_at h_run h_ne
  · intro pc sevm devm j pc' devm' exn h_at h_run ex_next ih_next h_fa h_at_p
    rcases em (sevm.currentTarget = ca) with h_eq | h_ne
    · cases exn with
      | error e => exact errAtTarget (.jumpRec h_at h_run ex_next) h_eq
      | ok post =>
        have h_pc : pc = 0 := (h_at_p.right h_eq).right
        subst h_pc
        have h_run_prog := correct sevm devm p post (.jumpRec h_at h_run ex_next) (h_at_p.right h_eq).left
        have h_fa_deeper : ForallDeeperAt sevm.depth ca p ε := by
          intro pc' sevm' devm' exn' ex' h_lt
          exact h_fa pc' sevm' devm' exn' ex' h_lt
        exact analog (.jumpRec h_at h_run ex_next) (depth_ind h_run_prog h_eq h_fa_deeper)
    · exact jumpRec h_at h_run ex_next h_ne
        (ih_next h_fa ⟨by rw [Jinst.inv_getCode h_run ca]; exact h_at_p.left, fun hc => (h_ne hc).elim⟩)
  · intro pc sevm devm l exn h_at h_run h_fa h_at_p
    rcases em (sevm.currentTarget = ca) with h_eq | h_ne
    · cases exn with
      | error e => exact errAtTarget (.last h_at h_run) h_eq
      | ok post =>
        have h_pc : pc = 0 := (h_at_p.right h_eq).right
        subst h_pc
        have h_run_prog := correct sevm devm p post (.last h_at h_run) (h_at_p.right h_eq).left
        have h_fa_deeper : ForallDeeperAt sevm.depth ca p ε := by
          intro pc' sevm' devm' exn' ex' h_lt
          exact h_fa pc' sevm' devm' exn' ex' h_lt
        exact analog (.last h_at h_run) (depth_ind h_run_prog h_eq h_fa_deeper)
    · exact last h_at h_run h_ne

lemma lift
    (R : Sevm → Devm → Devm → Prop)
    (ca : Adr) -- contract address
    (p : Prog)
    ( depth_ind :
      ∀ {sevm pre post},
        Prog.Run sevm pre p post →
        sevm.currentTarget = ca →
        ForallSubExec sevm.depth ca p R →
        R sevm pre post )
    ( nextNone :
      ∀ {pc} {sevm} {pre} {n} {inter} {post},
        n.At sevm.code pc →
        Ninst.Run' pc sevm pre n .none (.ok inter) →
        Exec (pc + n.size) sevm inter (.ok post) →
        sevm.currentTarget ≠ ca →
        R sevm inter post →
        R sevm pre post )
    ( nextSome :
      ∀ {pc} {sevm} {pre} {n} {sevm'} {devm'}
        {exn' : Execution} {inter} {post},
        n.At sevm.code pc →
        Ninst.Run' pc sevm pre n
          (.some ⟨sevm', devm', exn'⟩)
          (.ok inter) →
        Exec 0 sevm' devm' exn' →
        Exec (pc + n.size) sevm inter (.ok post) →
        sevm.currentTarget ≠ ca →
        ifOk (R sevm' devm') exn' →
        R sevm inter post →
        R sevm pre post )
    ( jump :
      ∀ {pc} {sevm} {pre} {j} {pc'} {inter} {post},
        j.At sevm.code pc →
        Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩) →
        Exec pc' sevm inter (.ok post) →
        sevm.currentTarget ≠ ca →
        R sevm inter post →
        R sevm pre post )
    ( last :
      ∀ {pc} {sevm} {pre} {l} {post},
        l.At sevm.code pc →
        Linst.Run sevm pre l (.ok post) →
        sevm.currentTarget ≠ ca →
        R sevm pre post ) :
    ∀ pc sevm pre post,
      Exec pc sevm pre (.ok post) →
      Prog.At p ca pc sevm pre →
      R sevm pre post := by
  intro pc sevm pre post h_exc h_at
  refine lift_core (fun _ sevm pre exn _ => ifOk (R sevm pre) exn) R (fun _ h => h) ca p
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ pc sevm pre (.ok post) h_exc h_at
  · intro sevm' pre' post' h_run h_eq h_fa
    apply depth_ind h_run h_eq
    intro pc_ sevm_ devm_ post_ h_exc' h_lt h_at'
    exact h_fa pc_ sevm_ devm_ (.ok post_) h_exc' h_lt h_at'
  · intro pc' sevm' devm' err devm'' ex_err h_eq; exact trivial
  · intro pc' sevm' devm' h_get h_ne; exact trivial
  · intro pc' sevm' devm' n err devm'' h_at' h_run h_ne; exact trivial
  · intro pc' sevm' devm' n sevm_ devm_ exn_ err devm'' h_at' h_run ex_sub h_ne h_ih; exact trivial
  · intro pc' sevm' devm' n devm'' exn h_at' h_run ex h_ne h_ih
    cases exn with
    | error e => exact trivial
    | ok post' => exact nextNone h_at' h_run ex h_ne h_ih
  · intro pc' sevm' devm' n sevm_ devm_ exn_ devm'' exn h_at' h_run ex_sub ex h_ne h_ih_sub h_ih
    cases exn with
    | error e => exact trivial
    | ok post' => exact nextSome h_at' h_run ex_sub ex h_ne h_ih_sub h_ih
  · intro pc' sevm' devm' j err devm'' h_at' h_run h_ne; exact trivial
  · intro pc' sevm' devm' j pc_ devm'' exn h_at' h_run ex h_ne h_ih
    cases exn with
    | error e => exact trivial
    | ok post' => exact jump h_at' h_run ex h_ne h_ih
  · intro pc' sevm' devm' l exn h_at' h_run h_ne
    cases exn with
    | error e => exact trivial
    | ok post' => exact last h_at' h_run h_ne

lemma lift_inv
    (ca : Adr) (p : Prog)
    (σ : Sevm → Devm → Prop)
    (ρ : Sevm → Devm → Prop)
    ( with_depth_ind :
      ∀ {sevm pre post},
        Prog.Run sevm pre p post →
        sevm.currentTarget = ca →
        ( ∀ pc' sevm' pre' post',
            Exec pc' sevm' pre' (.ok post') →
            sevm'.depth < sevm.depth →
            Prog.At p ca pc' sevm' pre' →
            σ sevm' pre' →
            ρ sevm' post' ) →
        σ sevm pre →
        ρ sevm post )
    ( nextNone :
      ∀ {pc} {sevm} {pre} {n} {inter},
        n.At sevm.code pc →
        Ninst.Run' pc sevm pre n .none (.ok inter) →
        sevm.currentTarget ≠ ca →
        σ sevm pre →
        σ sevm inter )
    ( nextSome :
      ∀ {pc} {sevm} {pre} {n} {sevm'} {devm'} {exn'} {inter},
        n.At sevm.code pc →
        Ninst.Run' pc sevm pre n (.some ⟨sevm', devm', exn'⟩) (.ok inter) →
        Exec 0 sevm' devm' exn' →
        sevm.currentTarget ≠ ca →
        σ sevm pre →
        σ sevm' devm' ∧ (ifOk (ρ sevm') exn' → σ sevm inter) )
    ( jump :
      ∀ {pc} {sevm} {pre} {j} {pc'} {inter},
        j.At sevm.code pc →
        Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩) →
        sevm.currentTarget ≠ ca →
        σ sevm pre →
        σ sevm inter )
    ( last :
      ∀ {pc} {sevm} {pre} {l} {post},
        l.At sevm.code pc →
        Linst.Run sevm pre l (.ok post) →
        sevm.currentTarget ≠ ca →
        σ sevm pre →
        ρ sevm post ) :
    ∀ pc sevm devm post,
      Exec pc sevm devm (.ok post) →
      Prog.At p ca pc sevm devm →
      σ sevm devm →
      ρ sevm post := by
  apply @lift (fun sevm pre post => σ sevm pre → ρ sevm post) ca p with_depth_ind
  · intro pc sevm pre n inter post h_at h_run _ h_ne h_ih h_pi
    exact h_ih (nextNone h_at h_run h_ne h_pi)
  · intro pc sevm pre n sevm' devm' exn' inter post h_at h_run ex_sub _ h_ne h_ifOk h_ih h_pi
    rcases nextSome h_at h_run ex_sub h_ne h_pi with ⟨h_pi_sub, h_imp⟩
    apply h_ih; apply h_imp
    cases exn' with
    | error e => exact trivial
    | ok post' => exact h_ifOk h_pi_sub
  · intro pc sevm pre j pc' inter post h_at h_run _ h_ne h_ih h_pi
    exact h_ih (jump h_at h_run h_ne h_pi)
  · intro pc sevm pre l post h_at h_run h_ne h_pi
    exact last h_at h_run h_ne h_pi

syntax "show_prefix_zero" : tactic
macro_rules
  | `(tactic| show_prefix_zero) =>
    `(tactic| intros h0 h1; apply append_pref h0.stack h1)

syntax "show_prefix_one" : tactic
macro_rules
  | `(tactic| show_prefix_one) =>
    `(tactic| intros h0 h1; rcases h0 with ⟨x', h0⟩;
              rcases h0.stack with ⟨stk, h2, h3⟩; clear h0;
              rcases List.of_cons_pref_of_cons_pref h1 (pref_of_split h2) with ⟨hx, h⟩;
              cases hx; clear h; apply append_pref h3 (of_append_pref h2 h1) )

syntax "show_prefix_two" : tactic
macro_rules
  | `(tactic| show_prefix_two) =>
    `(tactic| intros h0 h1; rcases h0 with ⟨x', y', h0⟩;
              rcases h0.stack with ⟨stk, h2, h3⟩; clear h0;
              rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2) with ⟨hx, hy, h⟩;
              cases hx; cases hy; clear h; apply append_pref h3 (of_append_pref h2 h1) )

infix:70 " <? "  => B256.lt_check
infix:70 " >? "  => B256.gt_check
infix:70 " ±<? " => B256.slt_check
infix:70 " ±>? " => B256.sgt_check
infix:70 " =? "  => B256.eq_check

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

def Stack.Diff (xs zs : Stack) (s s'' : Stack) : Prop :=
  ∃ s' : Stack, Stack.Pop xs s s' ∧ Stack.Push zs s' s''

def Stack.SwapCore (x y : B256) : Nat → Stack → Stack → Prop
  | 0, y' :: xs, x' :: xs' => x = x' ∧ y = y' ∧ xs = xs'
  | n + 1, z :: xs, z' :: xs' => z = z' ∧ SwapCore x y n xs xs'
  | _, _, _ => False

def Stack.Swap (n : Nat) : Stack → Stack → Prop
  | x :: xs, y :: xs' => SwapCore x y n xs xs'
  | _, _ => False

inductive Stack.Nth : Nat → B256 → Stack → Prop
  | head : ∀ x xs, Nth 0 x (x :: xs)
  | tail : ∀ m x y xs, Nth m x xs → Nth (m + 1) x (y :: xs)

def Devm.Push (xs : List B256) : Devm → Devm → Prop :=
  Rel {Rels.eq with stack := _root_.Stack.Push xs}

def Devm.DiffBurn (xs ys : List B256) : Devm → Devm → Prop :=
  Rel {Rels.eq with stack := Stack.Diff xs ys, gasLeft := (· ≥ ·)}

lemma Devm.push_of_push {x : B256} {s s' : Devm} (h : Devm.push x s = .ok s') :
    Devm.Push [x] s s' := by
  rw [Devm.push_def] at h
  simp only [Except.assert, bind, Except.bind] at h
  split at h
  · cases h
  · injection h with eq; subst eq
    constructor <;> simp [Devm.Rels.eq, _root_.Stack.Push, Split]

lemma Devm.pushBurn_of_burn_of_push {xs : List B256} {s s' s'' : Devm}
    (burn : Devm.Burn s s') (push : Devm.Push xs s' s'') :
    Devm.PushBurn xs s s'' := by
  constructor
  · exact burn.stack ▸ push.stack
  · exact Eq.trans burn.memory push.memory
  · rw [← push.gasLeft]; exact burn.gasLeft
  · exact Eq.trans burn.logs push.logs
  · exact Eq.trans burn.refundCounter push.refundCounter
  · exact Eq.trans burn.output push.output
  · exact Eq.trans burn.accountsToDelete push.accountsToDelete
  · exact Eq.trans burn.returnData push.returnData
  · exact Eq.trans burn.error push.error
  · exact Eq.trans burn.accessedAddresses push.accessedAddresses
  · exact Eq.trans burn.accessedStorageKeys push.accessedStorageKeys
  · exact Eq.trans burn.state push.state
  · exact Eq.trans burn.createdAccounts push.createdAccounts
  · exact Eq.trans burn.transientStorage push.transientStorage

lemma Devm.diffBurn_of_pop_of_pushBurn {xs ys : List B256} {s s' s'' : Devm}
    (pop : Devm.Pop xs s s') (push : Devm.PushBurn ys s' s'') :
    Devm.DiffBurn xs ys s s'' := by
  constructor
  · exact ⟨s'.stack, pop.stack, push.stack⟩
  · exact Eq.trans pop.memory push.memory
  · rw [pop.gasLeft]; exact push.gasLeft
  · exact Eq.trans pop.logs push.logs
  · exact Eq.trans pop.refundCounter push.refundCounter
  · exact Eq.trans pop.output push.output
  · exact Eq.trans pop.accountsToDelete push.accountsToDelete
  · exact Eq.trans pop.returnData push.returnData
  · exact Eq.trans pop.error push.error
  · exact Eq.trans pop.accessedAddresses push.accessedAddresses
  · exact Eq.trans pop.accessedStorageKeys push.accessedStorageKeys
  · exact Eq.trans pop.state push.state
  · exact Eq.trans pop.createdAccounts push.createdAccounts
  · exact Eq.trans pop.transientStorage push.transientStorage

lemma Devm.pushBurn_of_pushItem {v : B256} {cost : Nat} {s s' : Devm}
    (h : pushItem v cost s = .ok s') : Devm.PushBurn [v] s s' := by
  rw [pushItem_def] at h; exact Devm.pushBurn_of_run h

lemma Devm.diffBurn_of_applyUnary {f : B256 → B256} {cost : Nat} {s s' : Devm}
    (h : applyUnary f cost s = .ok s') :
    ∃ x, Devm.DiffBurn [x] [f x] s s' := by
  rw [applyUnary_def] at h
  rcases of_bind_eq_ok h with ⟨⟨x, s₁⟩, h1, h2⟩
  simp only at h2
  rw [pushItem_def] at h2
  refine ⟨x, Devm.diffBurn_of_pop_of_pushBurn (Devm.pop_of_pop h1) (Devm.pushBurn_of_run h2)⟩

lemma Devm.diffBurn_of_applyBinary {f : B256 → B256 → B256} {cost : Nat} {s s' : Devm}
    (h : applyBinary f cost s = .ok s') :
    ∃ x y, Devm.DiffBurn [x, y] [f x y] s s' := by
  rw [applyBinary_def] at h
  rcases of_bind_eq_ok h with ⟨⟨x, s₁⟩, h1, h'⟩
  rcases of_bind_eq_ok h' with ⟨⟨y, s₂⟩, h2, h3⟩
  simp only at h3
  rw [pushItem_def] at h3
  refine ⟨x, y, Devm.diffBurn_of_pop_of_pushBurn
    (Devm.pop_append (Devm.pop_of_pop h1) (Devm.pop_of_pop h2))
    (Devm.pushBurn_of_run h3)⟩

lemma Devm.pop_of_popToNat {k : Nat} {devm devm' : Devm}
    (h : Devm.popToNat devm = .ok ⟨k, devm'⟩) :
    ∃ x, Devm.Pop [x] devm devm' := by
  rw [Devm.popToNat_def] at h
  dsimp [(· <&> ·), Functor.mapRev, Functor.map, Except.map] at h
  rcases hp : devm.pop with _ | ⟨x, devm1⟩ <;> simp [hp] at h
  rcases h with ⟨_, rfl⟩
  exact ⟨x, Devm.pop_of_pop hp⟩

lemma of_run_reg {e : Sevm} {s s' : Devm} {r : Rinst}
    (h : Ninst.Run e s (Ninst.reg r) s') :
    ∃ pc, Rinst.run ⟨pc, e, s⟩ r = .ok s' := by
  rcases h with ⟨xl, _, pc, run⟩
  cases xl with
  | some _ => cases run
  | none => dsimp [Ninst.Run'] at run; exact ⟨pc, run⟩

lemma of_run_push {e s s' xs p} (h : Ninst.Run e s (push xs p) s') :
    Devm.PushBurn [xs.toB256] s s' := by
  rcases h with ⟨xl, _, pc, run⟩
  cases xl with
  | some _ => cases run
  | none => dsimp [Ninst.Run'] at run; exact Devm.pushBurn_of_run run

lemma of_run_pushB256 {e s s' x} (h : Ninst.Run e s (pushB256 x) s') :
    Devm.PushBurn [x] s s' := by
  have h' := of_run_push h
  rwa [B8L.toB256_sig, B256.toB256_toB8L] at h'

lemma of_run_pop {e : Sevm} {s s' : Devm} (h : Ninst.Run e s pop s') :
    ∃ x, Devm.PopBurn [x] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases of_bind_eq_ok run with ⟨s₁, h1, h2⟩
  simp only [Functor.mapRev, Functor.map, Except.map] at h1
  rcases hp : Devm.pop s with _ | ⟨x, s₂⟩ <;> simp [hp] at h1
  subst h1
  exact ⟨x, Devm.popBurn_of_pop_of_burn (Devm.pop_of_pop hp) (Devm.burn_of_chargeGas h2)⟩

lemma of_run_dup {e : Sevm} {s s' : Devm} {n : Fin 16} (h : Ninst.Run e s (dup n) s') :
    ∃ x, s.stack[n.val]? = some x ∧ Devm.PushBurn [x] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases of_bind_eq_ok run with ⟨s₁, h1, h2⟩
  have hb := Devm.burn_of_chargeGas h1
  split at h2
  · cases h2
  · rename_i x hx
    refine ⟨x, ?_, Devm.pushBurn_of_burn_of_push hb (Devm.push_of_push h2)⟩
    rw [hb.stack]; exact hx

lemma of_run_swap {e : Sevm} {s s' : Devm} {n : Fin 16} (h : Ninst.Run e s (swap n) s') :
    List.swap s.stack n.val = some s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases of_bind_eq_ok run with ⟨s₁, h1, h2⟩
  have hb := Devm.burn_of_chargeGas h1
  split at h2
  · cases h2
  · rename_i stk hstk
    injection h2 with eq; subst eq
    rw [hb.stack]; exact hstk

lemma of_run_caller {e : Sevm} {s s' : Devm} (h : Ninst.Run e s caller s') :
    Devm.PushBurn [e.caller.toB256] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.pushBurn_of_pushItem run

lemma of_run_callvalue {e : Sevm} {s s' : Devm} (h : Ninst.Run e s callvalue s') :
    Devm.PushBurn [e.value] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.pushBurn_of_pushItem run

lemma of_run_mstore {e : Sevm} {s s' : Devm} (h : Ninst.Run e s mstore s') :
    ∃ x y, _root_.Stack.Pop [x, y] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases of_bind_eq_ok run with ⟨⟨i, s₁⟩, h1, run'⟩
  rcases of_bind_eq_ok run' with ⟨⟨v, s₂⟩, h2, run''⟩
  rcases of_bind_eq_ok run'' with ⟨s₃, h3, h4⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x, p1⟩
  have p2 := Devm.pop_of_pop h2
  have hb := Devm.burn_of_chargeGas h3
  injection h4 with eq
  refine ⟨x, v, ?_⟩
  have hp := (Devm.pop_append p1 p2).stack
  rw [← eq]
  rw [show (Devm.memWrite s₃ i v.toB8L).stack = s₃.stack from rfl, ← hb.stack]
  exact hp

lemma Devm.pop_of_popN {n : Nat} {devm devm' : Devm} {l : List B256}
    (hp : devm.popN n = Except.ok (l, devm')) :
    l.length = n ∧ Devm.Pop l devm devm' := by
  induction n generalizing devm l with
  | zero =>
    rw [Devm.popN_def] at hp
    injection hp with eq
    injection eq with eq1 eq2
    subst eq1; subst eq2
    refine ⟨rfl, ?_⟩
    constructor <;> simp [Devm.Rels.eq, _root_.Stack.Pop, Split]
  | succ n ih =>
    rw [Devm.popN_def] at hp
    rcases of_bind_eq_ok hp with ⟨⟨x, devm1⟩, hp1, hp2⟩
    rcases of_bind_eq_ok hp2 with ⟨⟨xs, devm2⟩, hp3, hp4⟩
    injection hp4 with eq
    injection eq with eq1 eq2
    subst eq1; subst eq2
    rcases ih hp3 with ⟨h_len, h_pop⟩
    refine ⟨by simp [h_len], Devm.pop_append (Devm.pop_of_pop hp1) h_pop⟩

lemma of_run_sstore {e : Sevm} {s s' : Devm} (h : Ninst.Run e s sstore s') :
    ∃ x y, _root_.Stack.Pop [x, y] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases of_bind_eq_ok run with ⟨⟨x, s₁⟩, h1, run₁⟩
  rcases of_bind_eq_ok run₁ with ⟨⟨y, s₂⟩, h2, run₂⟩
  rcases of_bind_eq_ok run₂ with ⟨_, h3, run₃⟩
  rcases of_bind_eq_ok run₃ with ⟨⟨s₃, g₂⟩, h4, run₄⟩
  rcases of_bind_eq_ok run₄ with ⟨g₃, h5, run₅⟩
  rcases of_bind_eq_ok run₅ with ⟨s₄, h6, run₆⟩
  rcases of_bind_eq_ok run₆ with ⟨s₅, h7, run₇⟩
  rcases of_bind_eq_ok run₇ with ⟨_, h8, h9⟩
  have hp := (Devm.pop_append (Devm.pop_of_pop h1) (Devm.pop_of_pop h2)).stack
  have hb := Devm.burn_of_chargeGas h7
  have h_s₃ : s₃.stack = s₂.stack := by
    injection h4 with eq
    split at eq <;> (injection eq with eq _; subst eq; rfl)
  have h_s₄ : s₄.stack = s₃.stack := by
    injection h6 with eq; rw [← eq]
  injection h9 with eq
  refine ⟨x, y, ?_⟩
  rw [← eq]
  show _root_.Stack.Pop [x, y] s.stack s₅.stack
  rw [← hb.stack, h_s₄, h_s₃]
  exact hp

lemma of_run_calldatacopy {e : Sevm} {s s' : Devm} (h : Ninst.Run e s calldatacopy s') :
    ∃ x y z, _root_.Stack.Pop [x, y, z] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases of_bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases of_bind_eq_ok run₁ with ⟨⟨di, s₂⟩, h2, run₂⟩
  rcases of_bind_eq_ok run₂ with ⟨⟨sz, s₃⟩, h3, run₃⟩
  rcases of_bind_eq_ok run₃ with ⟨s₄, h4, h5⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x, p1⟩
  rcases Devm.pop_of_popToNat h2 with ⟨y, p2⟩
  rcases Devm.pop_of_popToNat h3 with ⟨z, p3⟩
  have hb := Devm.burn_of_chargeGas h4
  injection h5 with eq
  refine ⟨x, y, z, ?_⟩
  have hp := (Devm.pop_append p1 (Devm.pop_append p2 p3)).stack
  rw [← eq]
  show _root_.Stack.Pop [x, y, z] s.stack s₄.stack
  rw [← hb.stack]
  exact hp

lemma of_run_singleton {e s i s'} (h : Line.Run e s [i] s') : Ninst.Run e s i s' := by
  rcases Line.of_run_cons h with ⟨_, hrun, hnil⟩
  cases hnil; exact hrun

lemma of_run_calldataload {e : Sevm} {s s' : Devm} (h : Ninst.Run e s calldataload s') :
    ∃ x y, _root_.Stack.Diff [x] [y] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases of_bind_eq_ok run with ⟨⟨si, s₁⟩, h1, run₁⟩
  rcases of_bind_eq_ok run₁ with ⟨s₂, h2, run₂⟩
  have hpop := Devm.pop_of_pop h1
  have hb := Devm.burn_of_chargeGas h2
  obtain ⟨val, hpush⟩ : ∃ val, Devm.Push [val] s₂ s' := ⟨_, Devm.push_of_push run₂⟩
  refine ⟨si, val, s₁.stack, hpop.stack, ?_⟩
  rw [show s₁.stack = s₂.stack from hb.stack]
  exact hpush.stack

lemma Devm.memRead_stack (devm : Devm) (i n : Nat) :
    (devm.memRead i n).2.stack = devm.stack := rfl

lemma of_run_kec {e : Sevm} {s s' : Devm} (h : Ninst.Run e s kec s') :
    ∃ x y z, _root_.Stack.Diff [x, y] [z] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases of_bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases of_bind_eq_ok run₁ with ⟨⟨sz, s₂⟩, h2, run₂⟩
  rcases of_bind_eq_ok run₂ with ⟨s₃, h3, run₃⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x, p1⟩
  rcases Devm.pop_of_popToNat h2 with ⟨y, p2⟩
  have hb := Devm.burn_of_chargeGas h3
  obtain ⟨val, hpush⟩ : ∃ val, Devm.Push [val] (s₃.memRead mi sz).2 s' :=
    ⟨_, Devm.push_of_push run₃⟩
  refine ⟨x, y, val, s₂.stack, (Devm.pop_append p1 p2).stack, ?_⟩
  rw [show s₂.stack = s₃.stack from hb.stack, ← Devm.memRead_stack s₃ mi sz]
  exact hpush.stack

lemma of_run_log {e : Sevm} {s s' : Devm} {n : Fin 5} (h : Ninst.Run e s (log n) s') :
    ∃ zs, zs.length = n.val + 2 ∧ _root_.Stack.Pop zs s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases of_bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases of_bind_eq_ok run₁ with ⟨⟨sz, s₂⟩, h2, run₂⟩
  rcases of_bind_eq_ok run₂ with ⟨⟨topics, s₃⟩, h3, run₃⟩
  rcases of_bind_eq_ok run₃ with ⟨s₄, h4, run₄⟩
  rcases of_bind_eq_ok run₄ with ⟨_, h5, run₅⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x, p1⟩
  rcases Devm.pop_of_popToNat h2 with ⟨y, p2⟩
  rcases Devm.pop_of_popN h3 with ⟨h_len, p3⟩
  have hb := Devm.burn_of_chargeGas h4
  rcases h_mem : Devm.memRead s₄ mi sz with ⟨data, s₅⟩
  rw [h_mem] at run₅
  injection run₅ with eq
  have h_s₅ : s₅.stack = s₄.stack := by
    simp only [Devm.memRead] at h_mem
    rcases h_read : s₄.memory.read mi sz with ⟨val, mem⟩
    rw [h_read] at h_mem
    injection h_mem with _ h_devm
    rw [← h_devm]; rfl
  refine ⟨x :: y :: topics, by simp [h_len], ?_⟩
  have hp := (Devm.pop_append p1 (Devm.pop_append p2 p3)).stack
  rw [← eq]
  show _root_.Stack.Pop (x :: y :: topics) s.stack s₅.stack
  rw [h_s₅, ← hb.stack]
  exact hp

lemma Stack.swapCore_of_swap {n} {xxs yys : Stack} (h : Swap n xxs yys) :
    ∃ x y xs ys, xxs = x :: xs ∧ yys = y :: ys ∧ SwapCore x y n xs ys := by
  cases xxs; cases h; cases yys; cases h; refine ⟨_, _, _, _, rfl, rfl, h⟩

lemma Stack.swapCore_zero {x y s} : SwapCore x y 0 (y :: s) (x :: s) := by simp [SwapCore]

lemma Stack.swapCore_succ {n x y z s s'} :
    SwapCore x z n s s' → SwapCore x z (n + 1) (y :: s) (y :: s') := by simp [SwapCore]

lemma Stack.swapCore_getElem_set {x y : B256} {n : Nat} {xs xs' : Stack}
    (h : SwapCore x y n xs xs') (t : Stack) :
    (xs ++ t)[n]? = some y ∧ (xs ++ t).set n x = xs' ++ t := by
  induction n generalizing xs xs' with
  | zero =>
    cases xs; cases h; cases xs'; cases h
    rcases h with ⟨hx, hy, hl⟩
    subst hx; subst hy; subst hl
    constructor <;> rfl
  | succ n ih =>
    cases xs; cases h; cases xs'; cases h
    rcases h with ⟨hz, h⟩
    subst hz
    rcases ih h with ⟨h1, h2⟩
    constructor
    · simpa using h1
    · simp only [List.cons_append, List.set_cons_succ]
      rw [h2]

lemma Stack.prefix_of_swap {n} {xs xs' stk stk' : Stack} :
    Swap n xs xs' → List.swap stk n = some stk' → (xs <<+ stk) → (xs' <<+ stk') := by
  intro h0 h1 h2
  rcases swapCore_of_swap h0 with ⟨x, y, xs₀, ys₀, hxs, hys, hc⟩
  subst hxs; subst hys
  rcases h2 with ⟨t, h2⟩
  rw [show stk = (x :: xs₀) ++ t from h2] at h1
  rcases swapCore_getElem_set hc t with ⟨hget, hset⟩
  simp only [List.cons_append, List.swap, hget, hset] at h1
  injection h1 with h1
  refine ⟨t, ?_⟩
  rw [← h1]
  rfl

lemma Stack.nth_getElem {n : Nat} {x : B256} {xs ys : Stack}
    (h : Nth n x xs) (h' : xs <<+ ys) : ys[n]? = some x := by
  revert h'
  induction h generalizing ys with
  | head z zs =>
    intro h'
    rcases h' with ⟨t, h'⟩
    rw [show ys = (z :: zs) ++ t from h']; rfl
  | tail m z w zs h ih =>
    intro h'
    rcases h' with ⟨t, h'⟩
    rw [show ys = (w :: zs) ++ t from h']
    simp only [List.cons_append, List.getElem?_cons_succ]
    exact ih ⟨t, rfl⟩

lemma prefix_of_diffBurn_one (v : B256 → B256) {x xs} {s s' : Devm} :
    (∃ x', Devm.DiffBurn [x'] [v x'] s s') →
    (x :: xs <<+ s.stack) → (v x :: xs <<+ s'.stack) := by show_prefix_one

lemma prefix_of_diffBurn_two (v : B256 → B256 → B256) {x y xs} {s s' : Devm} :
    (∃ x' y', Devm.DiffBurn [x', y'] [v x' y'] s s') →
    (x :: y :: xs <<+ s.stack) → (v x y :: xs <<+ s'.stack) := by show_prefix_two

lemma prefix_of_not {e} {x xs} {s s' : Devm} :
    Ninst.Run e s not s' → (x :: xs <<+ s.stack) → ((~~~ x) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_one (~~~ ·) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyUnary run

lemma prefix_of_iszero {e} {x xs} {s s' : Devm} :
    Ninst.Run e s iszero s' → (x :: xs <<+ s.stack) → ((x =? 0) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_one (· =? 0) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyUnary run

lemma prefix_of_eq {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s eq s' → (x :: y :: xs <<+ s.stack) → ((x =? y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two B256.eq_check ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_lt {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s lt s' → (x :: y :: xs <<+ s.stack) → ((x <? y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two B256.lt_check ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_gt {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s gt s' → (x :: y :: xs <<+ s.stack) → ((x >? y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two B256.gt_check ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_shl {e} {x y : B256} {xs} {s s' : Devm} :
    Ninst.Run e s shl s' → (x :: y :: xs <<+ s.stack) → (y <<< x.toNat :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two (fun x y => y <<< x.toNat) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_shr {e} {x y : B256} {xs} {s s' : Devm} :
    Ninst.Run e s shr s' → (x :: y :: xs <<+ s.stack) → (y >>> x.toNat :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two (fun x y => y >>> x.toNat) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_or {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s or s' → (x :: y :: xs <<+ s.stack) → ((x ||| y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two B256.or ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_and {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s and s' → (x :: y :: xs <<+ s.stack) → ((x &&& y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two B256.and ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_add {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s add s' → (x :: y :: xs <<+ s.stack) → ((x + y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two (· + ·) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_sub {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s sub s' → (x :: y :: xs <<+ s.stack) → ((x - y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two (· - ·) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_push {xs ys} {s s' : Devm} :
    Devm.PushBurn xs s s' → (ys <<+ s.stack) → ((xs ++ ys) <<+ s'.stack) :=
  λ h0 h1 => append_pref h0.stack h1

lemma prefix_of_pop {y : B256} {xs} {s s' : Devm} :
    (∃ x, Devm.PopBurn [x] s s') → (y :: xs <<+ s.stack) → (xs <<+ s'.stack) := by
  intros h h'; rcases h with ⟨x, hx⟩
  have h_eq : y = x :=
    (List.of_cons_pref_of_cons_pref h' (pref_of_split hx.stack)).left
  rw [h_eq] at h'
  exact of_append_pref hx.stack h'

lemma prefix_of_mstore {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s mstore s' → (x :: y :: xs <<+ s.stack) → (xs <<+ s'.stack) := by
  intros h0 h1
  rcases of_run_mstore h0 with ⟨x', y', h2⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2) with ⟨hx, hy, h⟩
  clear h; rw [hx, hy] at h1
  exact of_append_pref h2 h1

lemma prefix_of_sstore {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s sstore s' → (x :: y :: xs <<+ s.stack) → (xs <<+ s'.stack) := by
  intros h0 h1
  rcases of_run_sstore h0 with ⟨x', y', h2⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2) with ⟨hx, hy, h⟩
  clear h; rw [hx, hy] at h1
  exact of_append_pref h2 h1

lemma prefix_of_calldatacopy {e} {x y z xs} {s s' : Devm} :
    Ninst.Run e s calldatacopy s' → (x :: y :: z :: xs <<+ s.stack) → (xs <<+ s'.stack) := by
  intros h0 h1
  rcases of_run_calldatacopy h0 with ⟨x', y', z', h2⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2)
    with ⟨hx, hy, ws, h, h'⟩
  rcases List.of_cons_pref_of_cons_pref h h' with ⟨hz, _⟩
  rw [hx, hy, hz] at h1
  exact of_append_pref h2 h1

lemma prefix_of_calldataload {e} {x xs} {s s' : Devm} :
    Ninst.Run e s calldataload s' → (x :: xs <<+ s.stack) → ∃ z, z :: xs <<+ s'.stack := by
  intro h0 h1
  rcases of_run_calldataload h0 with ⟨x', y', stk, h2, h3⟩
  have hx : x = x' := (List.of_cons_pref_of_cons_pref h1 (pref_of_split h2)).left
  rw [hx] at h1
  exact ⟨y', append_pref h3 (of_append_pref h2 h1)⟩

lemma prefix_of_kec {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s kec s' → (x :: y :: xs <<+ s.stack) → ∃ z, z :: xs <<+ s'.stack := by
  intro h0 h1
  rcases of_run_kec h0 with ⟨x', y', z', stk, h2, h3⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2) with ⟨hx, hy, h⟩
  clear h; rw [hx, hy] at h1
  exact ⟨z', append_pref h3 (of_append_pref h2 h1)⟩

lemma prefix_of_cdl {e n xs} {s s' : Devm} :
    (xs <<+ s.stack) → Line.Run e s (cdl n) s' → ∃ z, z :: xs <<+ s'.stack := by
  intro h_pfx h_run
  rcases Line.of_run_cons h_run with ⟨s₁, h_push, h_rest⟩
  rcases Line.of_run_cons h_rest with ⟨s₂, h_cdl, h_nil⟩
  cases h_nil
  have h1 : n :: xs <<+ s₁.stack := prefix_of_push (of_run_pushB256 h_push) h_pfx
  exact prefix_of_calldataload h_cdl h1

lemma of_run_sload {e : Sevm} {s s' : Devm} (h : Ninst.Run e s sload s') :
    ∃ x, _root_.Stack.Diff [x] [Devm.getStorVal s e.currentTarget x] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases of_bind_eq_ok run with ⟨⟨key, s₁⟩, h1, run₁⟩
  have hpop := Devm.pop_of_pop h1
  have e1 : s.getStor = s₁.getStor := Devm.pop_getStor_eq h1
  refine ⟨key, s₁.stack, hpop.stack, ?_⟩
  suffices H : ∀ (d : Devm) (c : Nat), s₁.getStor = d.getStor → s₁.stack = d.stack →
      (chargeGas c d >>= fun y => Devm.push (Devm.getStorVal y e.currentTarget key) y) = .ok s' →
      _root_.Stack.Push [Devm.getStorVal s e.currentTarget key] s₁.stack s'.stack by
    split at run₁
    · exact H s₁ gasWarmAccess rfl rfl run₁
    · exact H (addAccessedStorageKey s₁ e.currentTarget key) gasColdSload
        (@addAccessedStorageKey_getStor s₁ e.currentTarget key).symm rfl run₁
  intro d c hgs hst run'
  rcases of_bind_eq_ok run' with ⟨s₂, h2, run₂⟩
  have hpush := Devm.push_of_push run₂
  have hstk : d.stack = s₂.stack := (Devm.burn_of_chargeGas h2).stack
  have e2 : d.getStor = s₂.getStor := chargeGas_getStor_eq h2
  have hval : Devm.getStorVal s₂ e.currentTarget key
      = Devm.getStorVal s e.currentTarget key := by
    show (s₂.getStor e.currentTarget).get key = (s.getStor e.currentTarget).get key
    rw [← e2, ← hgs, ← e1]
  rw [hst, hstk, ← hval]
  exact hpush.stack

lemma prefix_of_sload' {e x xs} {s s' : Devm} :
    Ninst.Run e s sload s' → (x :: xs <<+ s.stack) →
    ∃ y, (y :: xs <<+ s'.stack) ∧ y = Devm.getStorVal s e.currentTarget x := by
  intro h0 h1
  rcases of_run_sload h0 with ⟨x', stk, h2, h3⟩
  have hx : x = x' := (List.of_cons_pref_of_cons_pref h1 (pref_of_split h2)).left
  subst hx
  exact ⟨_, append_pref h3 (of_append_pref h2 h1), rfl⟩

lemma Line.spx_scheme {e s' i l xs xs' ys}
    (h : ∀ s0 s1, Ninst.Run e s0 i s1 → (xs <<+ s0.stack) → (xs' <<+ s1.stack))
    (h' : ∀ s : Devm, (xs' <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) :
    ∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (i :: l) s' → (ys <<+ s'.stack) := by
  intros s h_pfx h_run
  rcases Line.of_run_cons h_run with ⟨s_mid, h_head, h_tail⟩
  apply h' s_mid (h _ _ h_head h_pfx) h_tail

lemma Line.spx_push {e : Sevm} {s' l bs p xs ys} :
    (∀ s : Devm, (bs.toB256 :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (push bs p :: l) s' → (ys <<+ s'.stack)) := by
  intros h_next s h_pfx h_run
  rcases Line.of_run_cons h_run with ⟨s_mid, h_head, h_tail⟩
  apply h_next s_mid _ h_tail
  apply prefix_of_push (of_run_push h_head) h_pfx

lemma Line.spx_pushB256 {e : Sevm} {s' l x xs ys} :
    (∀ s : Devm, (x :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (pushB256 x :: l) s' → (ys <<+ s'.stack)) := by
  intros h_next s h_pfx h_run
  rcases Line.of_run_cons h_run with ⟨s_mid, h_head, h_tail⟩
  apply h_next s_mid _ h_tail
  apply prefix_of_push (of_run_pushB256 h_head) h_pfx

lemma Line.spx_mstore {e : Sevm} {s' l x y xs ys} :
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (mstore :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_mstore

lemma Line.spx_sstore {e : Sevm} {s' l x y xs ys} :
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (sstore :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_sstore

lemma Line.spx_dup {e s' l xs ys} {n : Fin 16} (x) :
    Stack.Nth n.val x xs →
    (∀ s : Devm, (x :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (dup n :: l) s' → (ys <<+ s'.stack)) := by
  intro h_nth; apply Line.spx_scheme
  intros s0 s1 h_step h_pfx
  rcases of_run_dup h_step with ⟨w, h_get, h_pb⟩
  rw [Stack.nth_getElem h_nth h_pfx] at h_get
  injection h_get with h_get
  rw [h_get]
  apply prefix_of_push h_pb h_pfx

lemma Line.spx_log (zs : Stack) {e s' l xs ys} {n : Fin 5} :
    zs.length = n.val + 2 →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (zs ++ xs <<+ s.stack) → Line.Run e s (log n :: l) s' → (ys <<+ s'.stack)) := by
  intro h_len; apply Line.spx_scheme
  intros s₀ s₁ h_step h_pfx
  rcases of_run_log h_step with ⟨zs', h_len', h_pop⟩
  have h_zs : (zs <<+ s₀.stack) := @pref_trans _ zs (zs ++ xs) _ ⟨xs, rfl⟩ h_pfx
  have h_zs' : (zs' <<+ s₀.stack) := pref_of_split h_pop
  cases List.pref_unique (Eq.trans h_len h_len'.symm) h_zs h_zs'
  exact of_append_pref h_pop h_pfx

lemma Line.spx_swap (xs') {e s' l xs ys} {n : Fin 16} :
    Stack.Swap n.val xs xs' →
    (∀ s : Devm, (xs' <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (swap n :: l) s' → (ys <<+ s'.stack)) := by
  intro h_swap; apply Line.spx_scheme
  intros s0 s1 h_step
  exact Stack.prefix_of_swap h_swap (of_run_swap h_step)

lemma Line.spx_iszero {e s' l} {x} {xs ys} :
    (∀ s : Devm, ((x =? 0) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: xs <<+ s.stack) → Line.Run e s (iszero :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_iszero

lemma Line.spx_pop {e : Sevm} {s' l x xs ys} :
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: xs <<+ s.stack) → Line.Run e s (pop :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intros s0 s1 h_step
  exact prefix_of_pop (of_run_pop h_step)

lemma Line.spx_eq {e s' l x y xs ys} :
    (∀ s : Devm, ((x =? y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (eq :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_eq

lemma Line.spx_lt {e s' l x y xs ys} :
    (∀ s : Devm, ((x <? y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (lt :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_lt

lemma Line.spx_gt {e s' l x y xs ys} :
    (∀ s : Devm, ((x >? y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (gt :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_gt

lemma Line.spx_sub {e s' l x y xs ys} :
    (∀ s : Devm, ((x - y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (sub :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_sub

lemma Line.spx_not {e s' l x xs ys} :
    (∀ s : Devm, (~~~ x :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: xs <<+ s.stack) → Line.Run e s (not :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_not

lemma Line.spx_or {e s' l x y xs ys} :
    (∀ s : Devm, ((x ||| y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (or :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_or

lemma Line.spx_and {e s' l x y xs ys} :
    (∀ s : Devm, ((x &&& y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (and :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_and

lemma Line.spx_shl {e s' l} {x y : B256} {xs ys} :
    (∀ s : Devm, (y <<< x.toNat :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (shl :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_shl

lemma Line.spx_shr {e s' l} {x y : B256} {xs ys} :
    (∀ s : Devm, (y >>> x.toNat :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (shr :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_shr

lemma Line.spx_add {e s' l x y xs ys} :
    (∀ s : Devm, ((x + y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (add :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_add

lemma Line.spx_caller {e : Sevm} {s' l xs ys} :
    (∀ s : Devm, (e.caller.toB256 :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (caller :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intros s0 s1 h_step h_pfx
  apply prefix_of_push (of_run_caller h_step) h_pfx

lemma Line.spx_callvalue {e : Sevm} {s' l xs ys} :
    (∀ s : Devm, (e.value :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (callvalue :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intros s0 s1 h_step h_pfx
  apply prefix_of_push (of_run_callvalue h_step) h_pfx

lemma Line.spx_calldatacopy {e : Sevm} {s' l x y z xs ys} :
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: z :: xs <<+ s.stack) → Line.Run e s (calldatacopy :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_calldatacopy

lemma Line.spx_unwrap {e xs} {s' : Devm} :
    ∀ s : Devm, (xs <<+ s.stack) → Line.Run e s [] s' → (xs <<+ s'.stack) := by
  intros _ h0 h1; cases h1; apply h0

lemma apply_univ {ξ : Type} (φ : ξ → Prop) (x : ξ) (h : ∀ x, φ x) : φ x := h x

section

open Lean.Elab.Tactic
open Lean.Parser.Tactic
open Lean.Elab.Term
open Lean
open Qq

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
  | ~q(∀ s : Devm, ($px <<+ s.stack) → Line.Run _ s $lx _ → _) =>
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

def Lean.FVarId.clear (i : Lean.FVarId) : Lean.Elab.Tactic.TacticM Unit :=
  withMainContext do
    let mvarId ← (← getMainGoal).clear i
    replaceMainGoal [mvarId]

def Lean.FVarId.rvt (i : Lean.FVarId) : TacticM Unit := do
  let (_, mvarId) ← (← getMainGoal).revert #[i]
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
  | ~q(_ <<+ (Devm.stack $x')) => pure (← Lean.Meta.isDefEq x x')
  | _ => pure false

def initDescOfRun : Q(Prop) → TacticM Expr
  | ~q(Line.Run _ $sx _ _) => pure sx
  | _ => failure

def Expr.imp (x y : Expr) : Expr := Expr.forallE Name.anonymous x y BinderInfo.default

def mkMotive : Q(Prop) → TacticM Expr
| ~q(($p <<+ (Devm.stack $s₀)) → (Line.Run $e $s₀ $l $s₁) → $φ) => do
  pure <|
    Expr.lam `s q(Devm)
      ( Expr.imp
          (Expr.app q(λ s : Devm => $p <<+ s.stack) (Expr.bvar 0))
          (Expr.imp (Expr.app q(λ s : Devm => Line.Run $e s $l $s₁) (Expr.bvar 1)) φ) )
      BinderInfo.default
| _ => failure

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
    Expr.apply <| mkApp2 q(@apply_univ Devm) m sd.toExpr
    line_pref

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

lemma memRead_getBal_eq {x n : Nat} {devm devm' : Devm} {value : B8L} (h : devm.memRead x n = ⟨value, devm'⟩) (a : Adr) : devm'.getBal a = devm.getBal a := by
  simp only [Devm.memRead] at h
  rcases h_read : devm.memory.read x n with ⟨val, mem⟩
  rw [h_read] at h
  injection h with _ h_devm
  rw [← h_devm]
  rfl

lemma memWrite_getBal_eq {idx : Nat} {val : B8L} {devm : Devm} (a : Adr) : (devm.memWrite idx val).getBal a = devm.getBal a := by
  exact (liftMachPure_worldEq (Mach.memWrite · idx val) devm).getBal a |>.symm

lemma Devm.popN_getBal_eq {n : Nat} {devm devm' : Devm} {l : List B256}
    (hp : devm.popN n = Except.ok (l, devm')) (a : Adr) :
    devm'.getBal a = devm.getBal a := by
  exact (liftMach_worldEq_of_ok (core := (Mach.popN · n)) hp).getBal a |>.symm

def Rinst.Inv {ξ : Type} (f : Devm → ξ) (r : Rinst) : Prop :=
  ∀ {pc sevm pre post}, Rinst.run ⟨pc, sevm, pre⟩ r = (.ok post) → f pre = f post

lemma Rinst.inv_bal {r} : Rinst.Inv Devm.getBal r := by
  intro pc sevm pre post hrun
  rcases eq_or_ne r .sstore with rfl | hs
  · have hf := Rinst.sstore_run_stateWriteFrame pc pre sevm; rw [hrun] at hf; exact funext hf.getBal_eq
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc pre sevm; rw [hrun] at hf
    simpa only [Devm.getBal] using congrArg (fun s => s.bal) hf.state
  · have hf := Rinst.run_instructionFrame pc sevm pre r hs ht; rw [hrun] at hf; exact funext hf.getBal

lemma memRead_getStor_eq {x n : Nat} {devm devm' : Devm} {value : B8L} (h : devm.memRead x n = ⟨value, devm'⟩) : devm'.getStor = devm.getStor := by
  simp only [Devm.memRead] at h
  rcases h_read : devm.memory.read x n with ⟨val, mem⟩
  rw [h_read] at h
  injection h with _ h_devm
  rw [← h_devm]
  rfl

lemma memWrite_getStor_eq {idx : Nat} {val : B8L} {devm : Devm} : (devm.memWrite idx val).getStor = devm.getStor := by
  funext a
  exact (liftMachPure_worldEq (Mach.memWrite · idx val) devm).getStor a |>.symm

lemma Devm.popN_getStor_eq {n : Nat} {devm devm' : Devm} {l : List B256}
    (hp : devm.popN n = Except.ok (l, devm')) :
    devm'.getStor = devm.getStor := by
  funext a
  exact (liftMach_worldEq_of_ok (core := (Mach.popN · n)) hp).getStor a |>.symm

lemma Rinst.inv_stor {r} (h_not_sstore : r ≠ Rinst.sstore) : Rinst.Inv Devm.getStor r := by
  intro pc sevm pre post hrun
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc pre sevm; rw [hrun] at hf
    simpa only [Devm.getStor, Devm.getAcct] using congrArg (fun s => fun a => (s.get a).stor) hf.state
  · have hf := Rinst.run_instructionFrame pc sevm pre r h_not_sstore ht; rw [hrun] at hf
    exact funext hf.getStor

class Rinst.Hinv {ξ : Type} (f : Devm → ξ) (o : Rinst) where (inv : Rinst.Inv f o)

instance {ξ : Type} (f : Devm → ξ) (o : Rinst) [Rinst.Hinv f o] :
    Ninst.Hinv f (Ninst.reg o) := ⟨by
  intros e s s' h
  rcases h with ⟨xl, h_filled, pc, run⟩
  cases xl with
  | some _ => cases run
  | none =>
    dsimp [Ninst.Run'] at run
    exact Rinst.Hinv.inv run
⟩

instance {o : Rinst} : Rinst.Hinv Devm.getBal o := ⟨Rinst.inv_bal⟩

instance {o : Rinst} : Rinst.Hinv Devm.getCode o := ⟨by
  intro pc sevm pre post run
  funext a
  exact (Rinst.inv_getCode run a).symm⟩

syntax "show_hinv_stor" : tactic
macro_rules
  | `(tactic| show_hinv_stor) =>
    `(tactic| exact ⟨Rinst.inv_stor (by intro; contradiction)⟩)

instance : Rinst.Hinv Devm.getStor Rinst.add := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mul := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.sub := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.div := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.sdiv := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mod := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.smod := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.addmod := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mulmod := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.exp := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.signextend := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.lt := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.gt := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.slt := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.sgt := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.eq := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.iszero := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.and := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.or := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.xor := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.not := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.byte := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.shr := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.shl := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.sar := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.kec := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.address := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.balance := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.origin := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.caller := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.callvalue := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.calldataload := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.calldatasize := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.calldatacopy := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.codesize := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.codecopy := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.gasprice := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.extcodesize := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.extcodecopy := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.retdatasize := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.retdatacopy := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.extcodehash := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.blockhash := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.coinbase := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.timestamp := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.number := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.prevrandao := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.gaslimit := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.chainid := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.selfbalance := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.basefee := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.blobhash := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.blobbasefee := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.pop := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mload := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mstore := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mstore8 := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.sload := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.tload := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.tstore := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mcopy := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.pc := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.msize := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.gas := by show_hinv_stor
instance {n} : Rinst.Hinv Devm.getStor (Rinst.dup n) := by show_hinv_stor
instance {n} : Rinst.Hinv Devm.getStor (Rinst.swap n) := by show_hinv_stor
instance {n} : Rinst.Hinv Devm.getStor (Rinst.log n) := by show_hinv_stor


/-! ## §1 AdrSet non-membership helpers -/

namespace AdrSet

theorem not_mem_insert {a b : Adr} {s : AdrSet} (hne : a ≠ b) (hs : a ∉ s) :
    a ∉ s.insert b := by
  simp only [Std.HashSet.mem_insert, not_or]
  exact ⟨by simpa using Ne.symm hne, hs⟩

theorem not_mem_foldl_insert {a : Adr} {l : List Adr} {m : AdrSet}
    (hm : a ∉ m) (hl : a ∉ l) :
    a ∉ l.foldl (fun acc x => acc.insert x) m := by
  induction l generalizing m with
  | nil => simpa using hm
  | cons x xs ih =>
    simp only [List.foldl_cons]
    refine ih (not_mem_insert ?_ hm) (fun h => hl (List.mem_cons_of_mem _ h))
    exact fun h => hl (h ▸ List.mem_cons_self ..)

theorem not_mem_union {a : Adr} {m₁ m₂ : AdrSet} (h₁ : a ∉ m₁) (h₂ : a ∉ m₂) :
    a ∉ m₁.union m₂ := by
  unfold Std.HashSet.union
  rw [Std.HashSet.fold_eq_foldl_toList]
  exact not_mem_foldl_insert h₁ (fun h => h₂ (Std.HashSet.mem_toList.mp h))

theorem not_mem_empty {a : Adr} {c : Nat} :
    a ∉ (Std.HashSet.emptyWithCapacity c : AdrSet) := by
  simp

end AdrSet

/-! ## §2 The NoDel invariant -/

-- rfl-bridge between the Devm-level and State-level code projections.
lemma Devm.getCode_state (d : Devm) (a : Adr) :
    d.getCode a = d.state.getCode a := rfl

-- The frame-level invariant. The `code` conjunct is the fuel for the
-- CREATE collision guards; it is transported by the PROVED getCode ladder,
-- never re-proved here.
structure Devm.NoDel (wa : Adr) (d : Devm) : Prop where
  (atd  : wa ∉ d.accountsToDelete)
  (ca   : wa ∉ d.createdAccounts)
  (code : (d.getCode wa).toList ≠ [])

-- The message-level invariant (a fresh frame starts with atd = ∅,
-- ca = msg.benv.createdAccounts, state = msg.benv.state; see initDevm,
-- elevm Execution.lean:2657).
structure Msg.NoDel (wa : Adr) (msg : Msg) : Prop where
  (ca   : wa ∉ msg.benv.createdAccounts)
  (code : (msg.benv.state.getCode wa).toList ≠ [])

-- Result-level invariants: error payloads carry live atd/ca (handleError
-- can resurrect them into ok results), so they must be covered.
def Execution.NoDel (wa : Adr) : Execution → Prop
  | .ok d => Devm.NoDel wa d
  | .error ⟨_, d⟩ => Devm.NoDel wa d

-- Msg-level results (`processMessage`-shaped): the error payload carries
-- only createdAccounts + state (no atd; consumers merge it via
-- liftToExecution, keeping the parent's atd).
def MsgResult.NoDel (wa : Adr) :
    Except (String × State × AdrSet × Tra) Devm → Prop
  | .ok d => Devm.NoDel wa d
  | .error ⟨_, st, ca, _⟩ => wa ∉ ca ∧ (st.getCode wa).toList ≠ []

-- The sub-execution oracle invariant threaded through the Exec induction
-- (result-shaped like Xlot.InvGetCode, Common.lean:4076; the former
-- Xlot.InvNof mirror in Solvent.lean was replaced by Exec.balance_effect).
def Xlot.InvNoDel (wa : Adr) : Xlot → Prop
  | .none => True
  | .some ⟨_, devm_, exn_⟩ => Devm.NoDel wa devm_ → Execution.NoDel wa exn_

/-! ## §3 Proved transports -/

-- Transport NoDel across a step that moves neither set nor wa's code.
lemma Devm.NoDel.of_eqs {wa : Adr} {d d' : Devm}
    (hs : d.delSets = d'.delSets) (hc : d.getCode wa = d'.getCode wa)
    (h : Devm.NoDel wa d) : Devm.NoDel wa d' := by
  have h1 : d.accountsToDelete = d'.accountsToDelete := congrArg Prod.fst hs
  have h2 : d.createdAccounts = d'.createdAccounts := congrArg Prod.snd hs
  exact ⟨h1 ▸ h.atd, h2 ▸ h.ca, hc ▸ h.code⟩

-- A fresh frame satisfies NoDel (initDevm: atd := ∅, ca := benv.ca).
lemma Msg.NoDel.initDevm {wa : Adr} {msg : Msg}
    (h : Msg.NoDel wa msg) : Devm.NoDel wa (initDevm msg) :=
  ⟨AdrSet.not_mem_empty, h.ca, h.code⟩

-- Rollback keeps atd/ca and installs the given state.
lemma Devm.NoDel.rollback {wa : Adr} {d : Devm} {st : State} {tra : Tra}
    (h_atd : wa ∉ d.accountsToDelete) (h_ca : wa ∉ d.createdAccounts)
    (h_code : (st.getCode wa).toList ≠ []) :
    Devm.NoDel wa (d.rollback st tra) :=
  ⟨h_atd, h_ca, h_code⟩

-- handleError shuffles error payloads into ok results without touching
-- the sets (elevm Execution.lean:2692-2701).
lemma handleError_noDel {wa : Adr} {exn : Execution}
    (h : Execution.NoDel wa exn) :
    MsgResult.NoDel wa (executeCode.handleError exn) := by
  cases exn with
  | ok d => exact h
  | error p =>
    rcases p with ⟨err, d⟩
    have hd : Devm.NoDel wa d := h
    dsimp only [executeCode.handleError]
    split
    · exact ⟨hd.atd, hd.ca, hd.code⟩
    · split
      · exact ⟨hd.atd, hd.ca, hd.code⟩
      · exact ⟨hd.ca, hd.code⟩

/-! ## §4 Plumbing -/

-- The create-guard bridge: an address whose account has size-0 code cannot be the code-bearing wa.
lemma ne_wa_of_code_size_zero {st : State} {wa b : Adr}
    (hwa : (st.getCode wa).toList ≠ []) (hb : (st.get b).code.size = 0) :
    b ≠ wa := by
  intro h
  subst h
  have h_empty : (st.get b).code.toList = [] := by
    unfold ByteArray.toList
    unfold ByteArray.toList.loop
    simp [hb]
  unfold State.getCode at hwa
  rw [h_empty] at hwa
  exact hwa rfl

-- Same bridge via the collision predicate used by `processMessageCall.create`.
lemma ne_wa_of_not_hasCodeOrNonce {st : State} {wa ct : Adr}
    (hwa : (st.getCode wa).toList ≠ [])
    (h : accountHasCodeOrNonce st ct = false) : ct ≠ wa := by
  intro heq
  subst heq
  unfold accountHasCodeOrNonce at h
  rw [Bool.or_eq_false_iff] at h
  have h_empty_not := h.2
  have h_empty : (st.getCode ct).isEmpty = true := by
    simp at h_empty_not
    exact h_empty_not
  have hb : (st.getCode ct).size = 0 := by
    unfold ByteArray.isEmpty at h_empty
    simp at h_empty
    exact h_empty
  have h_empty_list : (st.getCode ct).toList = [] := by
    unfold ByteArray.toList
    unfold ByteArray.toList.loop
    simp [hb]
  rw [h_empty_list] at hwa
  exact hwa rfl

lemma State.get_set_self {w : _root_.State} {a : Adr} {ac : Acct} :
    (w.set a ac).get a = ac := by
  unfold State.set State.get
  split_ifs with h
  · rw [Std.TreeMap.getD_erase]; simp; exact h.symm
  · rw [Std.TreeMap.getD_insert]; simp

lemma State.get_set_ne {w : _root_.State} {a a' : Adr} {ac : Acct} (h : a' ≠ a) :
    (w.set a' ac).get a = w.get a := by
  unfold State.set State.get
  have hc : compare a' a ≠ Ordering.eq := by
    intro hcc; exact h (compare_eq_iff_eq.mp hcc)
  split_ifs with hv
  · rw [Std.TreeMap.getD_erase]; simp [hc]
  · rw [Std.TreeMap.getD_insert]; simp [hc]

lemma State.set_bal {st : _root_.State} {a : Adr} {ac : Acct}
    (h : ac.bal = (st.get a).bal) : (st.set a ac).bal = st.bal := by
  funext b
  by_cases hb : b = a
  · subst hb
    show ((st.set b ac).get b).bal = (st.get b).bal
    rw [State.get_set_self]
    exact h
  · show ((st.set a ac).get b).bal = (st.get b).bal
    rw [State.get_set_ne (fun hc => hb hc.symm)]

lemma State.setStor_bal {st : _root_.State} {a : Adr} {s : Stor} :
    (st.setStor a s).bal = st.bal := State.set_bal rfl

lemma State.incrNonce_bal {st : _root_.State} {a : Adr} :
    (st.incrNonce a).bal = st.bal := State.set_bal rfl

lemma State.setCode_bal {st : _root_.State} {a : Adr} {cd : ByteArray} :
    (st.setCode a cd).bal = st.bal := State.set_bal rfl

lemma Devm.incrNonce_state {d : Devm} {a : Adr} :
    (d.incrNonce a).state = d.state.incrNonce a := rfl

-- The create-seeding step: wa ∉ msg.benv.createdAccounts and code is untouched.
lemma Msg.NoDel.processCreateMessage_msg {wa : Adr} {msg : Msg}
    (h_ct : msg.currentTarget ≠ wa)
    (h : Msg.NoDel wa msg) : Msg.NoDel wa (processCreateMessage.msg msg) := by
  rcases h with ⟨hca, hcode⟩
  refine ⟨?_, ?_⟩
  · show wa ∉ msg.benv.createdAccounts.insert msg.currentTarget
    exact AdrSet.not_mem_insert (Ne.symm h_ct) hca
  · show (((msg.benv.state.setStor msg.currentTarget .empty).incrNonce msg.currentTarget).getCode wa).toList ≠ []
    have h_get : ((msg.benv.state.setStor msg.currentTarget .empty).incrNonce msg.currentTarget).get wa = msg.benv.state.get wa := by
      dsimp only [State.incrNonce, State.setStor]
      rw [State.get_set_ne h_ct, State.get_set_ne h_ct]
    show (((msg.benv.state.setStor msg.currentTarget .empty).incrNonce msg.currentTarget).get wa).code.toList ≠ []
    rw [h_get]
    exact hcode

-- Precompiles never touch the sets or code.
lemma executePrecomp_noDel {wa : Adr} {evm : Evm} {adr : Adr} {exn : Execution}
    (h_ex : executePrecomp evm adr = exn)
    (h : Devm.NoDel wa evm.dyna) : Execution.NoDel wa exn := by
  unfold executePrecomp at h_ex
  revert h_ex
  generalize h_res : precompileRun evm adr = res
  intro h_ex
  subst h_ex
  cases res
  · apply Devm.NoDel.of_eqs (d := evm.dyna)
    · rfl
    · rfl
    · exact h
  · apply Devm.NoDel.of_eqs (d := evm.dyna)
    · rfl
    · rfl
    · exact h


/-! ## §5 Instruction level -/

-- Helper lemmas for the EVM instructions delSets preservation.
lemma delSets_eq_of_bind {α ε} {ma : Except ε α} {f : α → Except ε Devm}
    {devm devm' : Devm}
    (run : (ma >>= f) = .ok devm')
    (getDevm : α → Devm)
    (h_first : ∀ v, ma = .ok v → (getDevm v).delSets = devm.delSets)
    (h_rest : ∀ v, ma = .ok v → f v = .ok devm' → devm'.delSets = (getDevm v).delSets) :
    devm'.delSets = devm.delSets := by
  rcases of_bind_eq_ok run with ⟨v, hm, hf⟩
  rw [h_rest v hm hf, h_first v hm]

lemma liftMach_delSets_of_ok {core : Mach → Footprint.Outcome Mach α}
    {d d' : Devm} {x : α} (h : liftMach core d = .ok (x, d')) :
    d'.delSets = d.delSets := by
  unfold liftMach Footprint.liftOutcome at h
  cases hc : core d.mach with
  | error err => simp [hc] at h
  | ok out =>
    simp [hc] at h
    rcases h with ⟨_, rfl⟩
    rfl

lemma liftMach_delSets_of_error {core : Mach → Footprint.Outcome Mach α}
    {d : Devm} {err : String × Devm} (h : liftMach core d = .error err) :
    err.2.delSets = d.delSets := by
  unfold liftMach Footprint.liftOutcome at h
  cases hc : core d.mach with
  | error out =>
    simp [hc] at h
    rcases h with ⟨_, rfl⟩
    rfl
  | ok out => simp [hc] at h

lemma liftMachExecution_delSets_of_ok {core : Mach → Footprint.Outcome Mach Unit}
    {d d' : Devm} (h : liftMachExecution core d = .ok d') :
    d'.delSets = d.delSets := by
  unfold liftMachExecution Footprint.toExecution at h
  split at h
  · cases h
  · rename_i out heq
    cases h
    exact liftMach_delSets_of_ok heq

lemma liftMachExecution_delSets_of_error {core : Mach → Footprint.Outcome Mach Unit}
    {d : Devm} {err : String × Devm} (h : liftMachExecution core d = .error err) :
    err.2.delSets = d.delSets := by
  unfold liftMachExecution Footprint.toExecution at h
  split at h
  · rename_i e heq
    cases h
    exact liftMach_delSets_of_error heq
  · cases h

lemma Devm.pop_delSets_eq {x devm devm'} (h : Devm.pop devm = .ok ⟨x, devm'⟩) : devm'.delSets = devm.delSets := by
  simp only [Devm.pop_def] at h
  split at h <;> try contradiction
  cases h; rfl

lemma chargeGas_delSets_eq {cost devm devm'} (h : chargeGas cost devm = .ok devm') : devm'.delSets = devm.delSets := by
  simp only [chargeGas_def] at h
  split at h <;> try contradiction
  cases h; rfl

lemma Devm.push_delSets_eq {v devm devm'} (h : Devm.push v devm = .ok devm') : devm'.delSets = devm.delSets := by
  exact liftMachExecution_delSets_of_ok (core := Mach.push v) h

lemma Devm.popToAdr_delSets_eq {devm devm' adr} (h : Devm.popToAdr devm = .ok ⟨adr, devm'⟩) : devm'.delSets = devm.delSets := by
  exact liftMach_delSets_of_ok (core := Mach.popToAdr) h

lemma Devm.popToNat_delSets_eq {devm devm' n} (h : Devm.popToNat devm = .ok ⟨n, devm'⟩) : devm'.delSets = devm.delSets := by
  exact liftMach_delSets_of_ok (core := Mach.popToNat) h

lemma pushItem_delSets_eq {x c devm devm'} (h : pushItem x c devm = .ok devm') : devm'.delSets = devm.delSets := by
  exact liftMachExecution_delSets_of_ok (core := Mach.pushItem x c) h

lemma applyBinary_delSets_eq {f : B256 → B256 → B256} {cost devm devm'}
    (h : applyBinary f cost devm = .ok devm') :
    devm.delSets = devm'.delSets := by
  exact (liftMachExecution_delSets_of_ok (core := Mach.applyBinary f cost) h).symm

lemma applyUnary_delSets_eq {f : B256 → B256} {cost devm devm'}
    (h : applyUnary f cost devm = .ok devm') :
    devm.delSets = devm'.delSets := by
  exact (liftMachExecution_delSets_of_ok (core := Mach.applyUnary f cost) h).symm

lemma applyTernary_delSets_eq {f : B256 → B256 → B256 → B256} {cost devm devm'}
    (h : applyTernary f cost devm = .ok devm') :
    devm.delSets = devm'.delSets := by
  exact (liftMachExecution_delSets_of_ok (core := Mach.applyTernary f cost) h).symm

lemma memRead_delSets_eq {x n : Nat} {devm devm' : Devm} {value : B8L} (h : devm.memRead x n = ⟨value, devm'⟩) : devm'.delSets = devm.delSets := by
  simp only [Devm.memRead] at h
  rcases h_read : devm.memory.read x n with ⟨val, mem⟩
  rw [h_read] at h
  injection h with _ h_devm
  rw [← h_devm]
  rfl

lemma memWrite_delSets_eq {idx : Nat} {val : B8L} {devm : Devm} : (devm.memWrite idx val).delSets = devm.delSets := rfl

lemma Devm.popN_delSets_eq {n : Nat} {devm devm' : Devm} {l : List B256}
    (hp : devm.popN n = Except.ok (l, devm')) :
    devm'.delSets = devm.delSets := by
  exact liftMach_delSets_of_ok (core := (Mach.popN · n)) hp

lemma sstore_inv_delSets
    {pc sevm devm devm'}
    (run : Rinst.run ⟨pc, sevm, devm⟩ .sstore = .ok devm') :
    devm'.delSets = devm.delSets := by
  simp only [Rinst.run, Rinst.runCore] at run
  refine delSets_eq_of_bind run Prod.snd ?_ ?_
  {intro ⟨x, devm1⟩ hp; exact Devm.pop_delSets_eq hp}
  clear run
  intro ⟨x, devm1⟩ hp run;
  refine delSets_eq_of_bind run Prod.snd ?_ ?_
  {intro ⟨x, devm1⟩ hp; exact Devm.pop_delSets_eq hp}
  clear run
  intro ⟨y, devm2⟩ hp run;
  rcases of_bind_eq_ok run with ⟨⟨_⟩, _, run'⟩
  clear run
  refine delSets_eq_of_bind run' Prod.fst ?_ ?_
  · clear run';
    intro ⟨devm', _⟩
    simp only [ite_not, Except.ok.injEq]
    split
    · intro eq; injection eq with eq _; rw [eq]
    · simp [addAccessedStorageKey_def, Devm.withAccessedStorageKeys]
      intro rw _; rw [← rw]; clear rw
      simp [Devm.delSets]
  · clear run';
    intro ⟨devm3, _⟩ eq run; clear eq
    rcases of_bind_eq_ok run with ⟨_, bar, run'⟩;
    clear bar run
    simp only at run'
    refine delSets_eq_of_bind run' id ?_ ?_
    · clear run'
      intro devm4 eq
      injection eq with rw
      rw [← rw]
      simp [Devm.delSets]
    · clear run'
      intro devm4 temp run; clear temp
      refine delSets_eq_of_bind run id ?_ ?_
      {intro devm5 hc; exact (chargeGas_delSets_eq hc).trans rfl}
      clear run
      intro devm5 eq run
      rcases of_bind_eq_ok run with ⟨_, bar, run'⟩;
      clear bar run; injection run' with rw
      rw [← rw]
      rfl

lemma Rinst.inv_delSets {r : Rinst} : Rinst.Inv Devm.delSets r := by
  intro pc sevm pre post hrun
  rcases eq_or_ne r .sstore with rfl | hs
  · have hf := Rinst.sstore_run_stateWriteFrame pc pre sevm; rw [hrun] at hf
    exact Prod.ext hf.accountsToDelete hf.createdAccounts
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc pre sevm; rw [hrun] at hf
    exact Prod.ext hf.accountsToDelete hf.createdAccounts
  · have hf := Rinst.run_instructionFrame pc sevm pre r hs ht; rw [hrun] at hf; exact hf.delSets

lemma Devm.pop_delSets_err {err devm} (h : Devm.pop devm = .error err) : err.2.delSets = devm.delSets := by
  simp only [Devm.pop_def] at h
  split at h <;> try contradiction
  cases h; rfl

lemma chargeGas_delSets_err {cost devm err} (h : chargeGas cost devm = .error err) : err.2.delSets = devm.delSets := by
  simp only [chargeGas_def] at h
  split at h <;> try contradiction
  cases h; rfl

lemma Devm.push_delSets_err {v devm err} (h : Devm.push v devm = Except.error err) : err.2.delSets = devm.delSets := by
  exact liftMachExecution_delSets_of_error (core := Mach.push v) h

lemma assert_delSets_err {cond : Prop} [Decidable cond] {msg : String} {devm : Devm} {err : String × Devm} (h : Except.assert cond (msg, devm) = Except.error err) : err.2.delSets = devm.delSets := by
  unfold Except.assert at h
  split_ifs at h; try contradiction
  injection h with h1; rw [← h1]

lemma Devm.popToNat_delSets_err {devm err} (h : Devm.popToNat devm = .error err) : err.2.delSets = devm.delSets := by
  exact liftMach_delSets_of_error (core := Mach.popToNat) h

lemma Devm.popToAdr_delSets_err {devm err} (h : Devm.popToAdr devm = .error err) : err.2.delSets = devm.delSets := by
  exact liftMach_delSets_of_error (core := Mach.popToAdr) h

lemma delSets_err_of_bind {α} {ma : Except (String × Devm) α} {f : α → Execution}
    {devm : Devm} {err : String × Devm}
    (run : (ma >>= f) = Except.error err)
    (getDevm : α → Devm)
    (h_first_ok : ∀ v, ma = Except.ok v → (getDevm v).delSets = devm.delSets)
    (h_first_err : ∀ e, ma = Except.error e → e.2.delSets = devm.delSets)
    (h_rest_err : ∀ v, ma = Except.ok v → f v = Except.error err → err.2.delSets = (getDevm v).delSets) :
    err.2.delSets = devm.delSets := by
  cases h_ma : ma
  case error e =>
    rw [h_ma, Except.bind_error] at run
    injection run with h_eq; subst h_eq
    exact h_first_err _ h_ma
  case ok v =>
    rw [h_ma, Except.bind_ok] at run
    have h1 := h_rest_err v h_ma run
    have h2 := h_first_ok v h_ma
    exact h1.trans h2

lemma Devm.popN_delSets_err {n : Nat} {devm : Devm} {err : String × Devm}
    (hp : devm.popN n = Except.error err) :
    err.2.delSets = devm.delSets := by
  exact liftMach_delSets_of_error (core := (Mach.popN · n)) hp

lemma Devm.pop_map_snd_delSets_eq {devm devm1 : Devm} (hp : (devm.pop <&> Prod.snd) = .ok devm1) : devm1.delSets = devm.delSets := by
  dsimp [(· <&> ·), Functor.mapRev, Functor.map, Except.map] at hp
  rcases hp2 : devm.pop with _ | ⟨x, devm2⟩
  · simp [hp2] at hp
  · simp [hp2] at hp
    rcases hp with ⟨_, rfl⟩
    exact Devm.pop_delSets_eq hp2

lemma Devm.pop_map_snd_delSets_err {devm : Devm} {err : String × Devm} (hp : (devm.pop <&> Prod.snd) = .error err) : err.2.delSets = devm.delSets := by
  dsimp [(· <&> ·), Functor.mapRev, Functor.map, Except.map] at hp
  rcases hp2 : devm.pop with e | ⟨x, devm2⟩
  · simp [hp2] at hp; cases hp
    simp only [Devm.pop_def] at hp2
    split at hp2 <;> try contradiction
    cases hp2; rfl
  · simp [hp2] at hp

lemma pushItem_delSets_err {x c devm err} (h : pushItem x c devm = Except.error err) : err.2.delSets = devm.delSets := by
  exact liftMachExecution_delSets_of_error (core := Mach.pushItem x c) h

lemma applyUnary_delSets_err {f : B256 → B256} {cost devm err}
    (h : applyUnary f cost devm = Except.error err) :
    err.2.delSets = devm.delSets := by
  exact liftMachExecution_delSets_of_error (core := Mach.applyUnary f cost) h

lemma applyBinary_delSets_err {f : B256 → B256 → B256} {cost devm err}
    (h : applyBinary f cost devm = Except.error err) :
    err.2.delSets = devm.delSets := by
  exact liftMachExecution_delSets_of_error (core := Mach.applyBinary f cost) h

lemma applyTernary_delSets_err {f : B256 → B256 → B256 → B256} {cost devm err}
    (h : applyTernary f cost devm = Except.error err) :
    err.2.delSets = devm.delSets := by
  exact liftMachExecution_delSets_of_error (core := Mach.applyTernary f cost) h

-- Rinst execution preserves delSets on error results.
lemma Rinst.inv_delSets_err {pc : Nat} {sevm : Sevm} {devm : Devm} {r : Rinst}
    {err : String} {devm' : Devm}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = .error ⟨err, devm'⟩) :
    devm'.delSets = devm.delSets := by
  rcases eq_or_ne r .sstore with rfl | hs
  · have hf := Rinst.sstore_run_stateWriteFrame pc devm sevm; rw [run] at hf
    exact (Prod.ext (by simpa only using hf.accountsToDelete) (by simpa only using hf.createdAccounts)).symm
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc devm sevm; rw [run] at hf
    exact (Prod.ext (by simpa only using hf.accountsToDelete) (by simpa only using hf.createdAccounts)).symm
  · have hf := Rinst.run_instructionFrame pc sevm devm r hs ht; rw [run] at hf; exact hf.delSets.symm

lemma Jinst.inv_delSets {pc : Nat} {sevm : Sevm} {devm : Devm} {j : Jinst}
    {pc' : Nat} {devm' : Devm}
    (run : Jinst.Run ⟨pc, sevm, devm⟩ j (.ok ⟨pc', devm'⟩)) :
    devm'.delSets = devm.delSets := by
  have hf := Jinst.run_instructionFrame ⟨pc, sevm, devm⟩ j
  rw [run] at hf
  exact hf.delSets.symm

lemma Jinst.inv_delSets_err {pc : Nat} {sevm : Sevm} {devm : Devm} {j : Jinst}
    {err : String} {devm' : Devm}
    (run : Jinst.Run ⟨pc, sevm, devm⟩ j (.error ⟨err, devm'⟩)) :
    devm'.delSets = devm.delSets := by
  have hf := Jinst.run_instructionFrame ⟨pc, sevm, devm⟩ j
  rw [run] at hf
  exact hf.delSets.symm

-- Halting/terminal instructions (Linst) preserve NoDel.
lemma Linst.dest_inv_noDel {wa : Adr} {sevm : Sevm} {devm : Devm}
    {exn : Execution} (run : Linst.Run sevm devm .dest exn)
    (h : Devm.NoDel wa devm) : Execution.NoDel wa exn := by
  dsimp [Linst.Run, Linst.run] at run
  revert run
  dsimp [bind, Except.bind]
  cases h1 : devm.popToAdr <;> dsimp
  case error err => intro run; rw [← run]; exact Devm.NoDel.of_eqs (Devm.popToAdr_delSets_err h1).symm (Devm.popToAdr_getCode_err h1 wa).symm h
  case ok res1 =>
    have h_acc : (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).1.getCode wa = res1.2.getCode wa := by
      split
      · exact addAccessedAddress_getCode
      · rfl
    have h_acc_ds : (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).1.delSets = res1.2.delSets := by
      split
      · rfl
      · rfl
    cases h2 : chargeGas (if ((if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).1.getAcct res1.1).Empty ∧ ¬(res1.2.getAcct sevm.currentTarget).bal = 0 then (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).2 + gasSelfDestructNewAccount else (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).2) (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).1 <;> dsimp
    case error err => intro run; rw [← run]; exact Devm.NoDel.of_eqs (chargeGas_delSets_err h2).symm (chargeGas_getCode_err h2 wa).symm (Devm.NoDel.of_eqs h_acc_ds.symm h_acc.symm (Devm.NoDel.of_eqs (Devm.popToAdr_delSets_eq h1).symm (Devm.popToAdr_getCode_eq h1 wa).symm h))
    case ok res2 =>
      cases h3 : assertDynamic sevm res2
      case error err =>
        intro run; rw [← run]
        dsimp [assertDynamic, Except.assert] at h3
        split at h3
        · contradiction
        · simp only [Except.error.injEq] at h3; subst h3
          exact Devm.NoDel.of_eqs (chargeGas_delSets_eq h2).symm (chargeGas_getCode_eq h2 wa).symm (Devm.NoDel.of_eqs h_acc_ds.symm h_acc.symm (Devm.NoDel.of_eqs (Devm.popToAdr_delSets_eq h1).symm (Devm.popToAdr_getCode_eq h1 wa).symm h))
      case ok _ =>
        cases h4 : res2.subBal sevm.currentTarget (res1.2.getAcct sevm.currentTarget).bal <;> dsimp [Option.toExcept]
        case none =>
          intro run; rw [← run]
          exact Devm.NoDel.of_eqs (chargeGas_delSets_eq h2).symm (chargeGas_getCode_eq h2 wa).symm (Devm.NoDel.of_eqs h_acc_ds.symm h_acc.symm (Devm.NoDel.of_eqs (Devm.popToAdr_delSets_eq h1).symm (Devm.popToAdr_getCode_eq h1 wa).symm h))
        case some res3 =>
          have hd : Devm.NoDel wa res2 := Devm.NoDel.of_eqs (chargeGas_delSets_eq h2).symm (chargeGas_getCode_eq h2 wa).symm (Devm.NoDel.of_eqs h_acc_ds.symm h_acc.symm (Devm.NoDel.of_eqs (Devm.popToAdr_delSets_eq h1).symm (Devm.popToAdr_getCode_eq h1 wa).symm h))
          have h_sub : res3.getCode wa = res2.getCode wa := by
            dsimp [Devm.subBal] at h4
            cases h_st : res2.state.subBal sevm.currentTarget (res1.2.getAcct sevm.currentTarget).bal
            case none =>
              rw [h_st] at h4; contradiction
            case some st =>
              rw [h_st] at h4; dsimp at h4
              simp only [Option.some.injEq] at h4; subst h4
              change st.getCode wa = res2.getCode wa
              exact State.subBal_getCode h_st
          have h_sub_ds : res3.delSets = res2.delSets := by
            dsimp [Devm.subBal] at h4
            cases h_st : res2.state.subBal sevm.currentTarget (res1.2.getAcct sevm.currentTarget).bal
            case none => rw [h_st] at h4; contradiction
            case some st =>
              rw [h_st] at h4; dsimp at h4
              simp only [Option.some.injEq] at h4; subst h4
              rfl
          have hd3 : Devm.NoDel wa res3 := Devm.NoDel.of_eqs h_sub_ds.symm h_sub.symm hd
          by_cases h_if : sevm.currentTarget ∈ (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).createdAccounts
          · simp only [h_if, if_pos]
            intro run; rw [← run]
            have h_ca_eq : (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).createdAccounts = res3.createdAccounts := rfl
            have h_ca : sevm.currentTarget ∈ res3.createdAccounts := h_ca_eq ▸ h_if
            have h_ne : sevm.currentTarget ≠ wa := by
              intro heq; rw [heq] at h_ca
              exact hd3.ca h_ca
            constructor
            · exact AdrSet.not_mem_insert (Ne.symm h_ne) hd3.atd
            · exact hd3.ca
            · have h_add : (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).getCode wa = res3.getCode wa := by
                dsimp [Devm.addBal, Devm.getCode]; exact State.addBal_getCode res3.state _ _ _
              have h_set : ((res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).setBal sevm.currentTarget 0).getCode wa = (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).getCode wa := by
                dsimp [Devm.setBal, Devm.getCode]; exact State.setBal_getCode _ _ _ _
              have h_code : (addAccountToDelete ((res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).setBal sevm.currentTarget 0) sevm.currentTarget).getCode wa = res3.getCode wa :=
                h_set.trans h_add
              rw [h_code]; exact hd3.code
          · simp only [h_if]
            intro run; rw [← run]
            constructor
            · exact hd3.atd
            · exact hd3.ca
            · have h_add : (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).getCode wa = res3.getCode wa := by
                dsimp [Devm.addBal, Devm.getCode]; exact State.addBal_getCode res3.state _ _ _
              rw [h_add]; exact hd3.code

theorem Linst.run_noDel {wa : Adr} {sevm : Sevm} {devm : Devm}
    {l : Linst} {exn : Execution} (run : Linst.Run sevm devm l exn)
    (h : Devm.NoDel wa devm) : Execution.NoDel wa exn := by
  rcases eq_or_ne l .dest with rfl | h_not_dest
  · exact Linst.dest_inv_noDel run h
  · have hf := Linst.run_instructionFrame sevm devm l h_not_dest
    rw [run] at hf
    cases exn <;> exact Devm.NoDel.of_eqs hf.delSets (hf.getCode wa) h

lemma Linst.inv_noDel {wa : Adr} {sevm : Sevm} {devm : Devm} {l : Linst}
    {exn : Execution}
    (run : Linst.Run sevm devm l exn)
    (h : Devm.NoDel wa devm) : Execution.NoDel wa exn := by
  exact Linst.run_noDel run h

lemma Msg.NoDel.benvAfterTransfer_err {wa : Adr} {msg : Msg}
    {x : String × State × AdrSet × Tra}
    (h_run : msg.benvAfterTransfer = .error x)
    (h : Msg.NoDel wa msg) : wa ∉ x.2.2.1 ∧ (x.2.1.getCode wa).toList ≠ [] := by
  by_cases h_stv : msg.shouldTransferValue = true
  · unfold Msg.benvAfterTransfer at h_run
    rw [if_pos h_stv] at h_run
    cases h_sub : msg.benv.subBal msg.caller msg.value
    · rw [h_sub] at h_run
      simp only [Except.error.injEq, Option.toExcept, Except.bind, bind] at h_run
      subst h_run
      exact ⟨h.ca, h.code⟩
    · rw [h_sub] at h_run
      dsimp [Option.toExcept] at h_run
      contradiction
  · unfold Msg.benvAfterTransfer at h_run
    rw [if_neg h_stv] at h_run
    contradiction

lemma chargeCodeGas_delSets_ok {d d' : Devm}
    (h : processCreateMessage.chargeCodeGas d = .ok d') : d'.delSets = d.delSets := by
  unfold processCreateMessage.chargeCodeGas at h
  dsimp only at h
  split at h
  · cases h
  · rcases of_bind_eq_ok h with ⟨d1, h_charge, h_rest⟩
    split_ifs at h_rest
    cases h_rest
    exact chargeGas_delSets_eq h_charge

lemma chargeCodeGas_delSets_err {d d' : Devm} {err : String}
    (h : processCreateMessage.chargeCodeGas d = .error ⟨err, d'⟩) :
    d'.delSets = d.delSets := by
  unfold processCreateMessage.chargeCodeGas at h
  dsimp only at h
  split at h
  · cases h; rfl
  · rcases hcg : chargeGas _ d with ⟨e, dd⟩ | dd
    · rw [hcg] at h
      dsimp only [Bind.bind, Except.bind] at h
      cases h
      exact chargeGas_delSets_err hcg
    · rw [hcg] at h
      dsimp only [Bind.bind, Except.bind] at h
      split_ifs at h
      cases h; exact chargeGas_delSets_eq hcg

lemma Devm.push_noDel {wa : Adr} {x : B256} {d : Devm} {exn : Execution}
    (heq : Devm.push x d = exn) (h : Devm.NoDel wa d) : Execution.NoDel wa exn := by
  subst heq
  cases hp : Devm.push x d with
  | error err =>
    have hd := Devm.push_delSets_err hp
    refine ⟨?_, ?_, (Devm.push_getCode_err hp wa) ▸ h.code⟩
    · rw [show err.2.accountsToDelete = d.accountsToDelete from congrArg Prod.fst hd]
      exact h.atd
    · rw [show err.2.createdAccounts = d.createdAccounts from congrArg Prod.snd hd]
      exact h.ca
  | ok d' =>
    have hd := Devm.push_delSets_eq hp
    refine ⟨?_, ?_, (Devm.push_getCode_eq hp wa) ▸ h.code⟩
    · rw [show d'.accountsToDelete = d.accountsToDelete from congrArg Prod.fst hd]
      exact h.atd
    · rw [show d'.createdAccounts = d.createdAccounts from congrArg Prod.snd hd]
      exact h.ca

lemma incorporateChildOnError_noDel {wa : Adr} {parent child : Devm} {rd : B8L}
    (hp_atd : wa ∉ parent.accountsToDelete) (hc : Devm.NoDel wa child) :
    Devm.NoDel wa (incorporateChildOnError parent child rd) :=
  ⟨hp_atd, hc.ca, hc.code⟩

lemma incorporateChildOnSuccess_noDel {wa : Adr} {parent child : Devm} {rd : B8L}
    (hp_atd : wa ∉ parent.accountsToDelete) (hc : Devm.NoDel wa child) :
    Devm.NoDel wa (incorporateChildOnSuccess parent child rd) :=
  ⟨AdrSet.not_mem_union hp_atd hc.atd, hc.ca, hc.code⟩

lemma accessDelegation_delSets {d : Devm} {adr : Adr} :
    (accessDelegation d adr).2.2.2.2.delSets = d.delSets := by
  simp only [accessDelegation]; split <;> rfl

lemma Execution.NoDel.error_of {wa : Adr} {d : Devm} {x : String × Devm}
    (hd : Devm.NoDel wa d) (h : x.2 = d) : Execution.NoDel wa (.error x) := by
  obtain ⟨s, d'⟩ := x
  dsimp only at h
  subst h
  exact hd

lemma Devm.pop_err_snd {d : Devm} {x : String × Devm}
    (h : Devm.pop d = .error x) : x.2 = d := by
  simp only [Devm.pop_def] at h
  split at h
  · injection h with h; exact (congrArg Prod.snd h).symm
  · exact absurd h (by simp)

lemma Devm.popToNat_err_snd {d : Devm} {x : String × Devm}
    (h : Devm.popToNat d = .error x) : x.2 = d := by
  rw [Devm.popToNat_def] at h
  dsimp only [(· <&> ·), Functor.mapRev, Functor.map, Except.map] at h
  rcases hp : d.pop with e | ⟨v, d0⟩
  · rw [hp] at h; injection h with h; rw [← h]; exact Devm.pop_err_snd hp
  · rw [hp] at h; exact absurd h (by simp)

lemma Devm.popToAdr_err_snd {d : Devm} {x : String × Devm}
    (h : Devm.popToAdr d = .error x) : x.2 = d := by
  rw [Devm.popToAdr_def] at h
  rcases hp : d.pop with e | ⟨v, d0⟩
  · rw [hp] at h; injection h with h; rw [← h]; exact Devm.pop_err_snd hp
  · rw [hp] at h; exact absurd h (by simp)

lemma chargeGas_err_snd {cost : Nat} {d : Devm} {x : String × Devm}
    (h : chargeGas cost d = .error x) : x.2 = d := by
  simp only [chargeGas_def] at h
  split at h
  · injection h with h; exact (congrArg Prod.snd h).symm
  · exact absurd h (by simp)

lemma Except.assert_err_snd {p : Prop} [Decidable p] {d : Devm} {s : String}
    {x : String × Devm} (h : Except.assert p (⟨s, d⟩ : String × Devm) = .error x) :
    x.2 = d := by
  simp only [Except.assert] at h
  split at h
  · exact absurd h (by simp)
  · injection h with h; exact (congrArg Prod.snd h).symm

lemma Devm.NoDel.pop {wa : Adr} {d d' : Devm} {v : B256}
    (hd : Devm.NoDel wa d) (h : Devm.pop d = .ok ⟨v, d'⟩) : Devm.NoDel wa d' :=
  hd.of_eqs (Devm.pop_delSets_eq h).symm (Devm.pop_getCode h).symm

lemma Devm.NoDel.popToNat {wa : Adr} {d d' : Devm} {n : Nat}
    (hd : Devm.NoDel wa d) (h : Devm.popToNat d = .ok ⟨n, d'⟩) : Devm.NoDel wa d' :=
  hd.of_eqs (Devm.popToNat_delSets_eq h).symm (Devm.popToNat_getCode h).symm

lemma Devm.NoDel.popToAdr {wa : Adr} {d d' : Devm} {a : Adr}
    (hd : Devm.NoDel wa d) (h : Devm.popToAdr d = .ok ⟨a, d'⟩) : Devm.NoDel wa d' :=
  hd.of_eqs (Devm.popToAdr_delSets_eq h).symm (Devm.popToAdr_getCode h).symm

lemma Devm.NoDel.chargeGas {wa : Adr} {d d' : Devm} {cost : Nat}
    (hd : Devm.NoDel wa d) (h : chargeGas cost d = .ok d') : Devm.NoDel wa d' :=
  hd.of_eqs (chargeGas_delSets_eq h).symm (chargeGas_getCode h).symm

lemma Devm.NoDel.memExtends {wa : Adr} {d : Devm} {ranges : List (Nat × Nat)}
    (hd : Devm.NoDel wa d) : Devm.NoDel wa (d.memExtends ranges) := by
  refine hd.of_eqs ?_ Devm.memExtends_getCode.symm
  rfl

lemma Devm.NoDel.addAccessedAddress {wa : Adr} {d : Devm} {a : Adr}
    (hd : Devm.NoDel wa d) : Devm.NoDel wa (_root_.addAccessedAddress d a) := by
  refine hd.of_eqs ?_ addAccessedAddress_getCode.symm
  rfl

lemma Devm.NoDel.incrNonce {wa : Adr} {d : Devm} {a : Adr}
    (hd : Devm.NoDel wa d) : Devm.NoDel wa (d.incrNonce a) := by
  refine hd.of_eqs ?_ Devm.incrNonce_getCode.symm
  rfl

lemma Devm.NoDel.of_accessDelegation {wa : Adr} {d d' : Devm} {adr na : Adr}
    {dp : Bool} {code : ByteArray} {dagc : Nat}
    (hd : Devm.NoDel wa d)
    (h : (dp, na, code, dagc, d') = _root_.accessDelegation d adr) : Devm.NoDel wa d' := by
  have hd' : d' = (_root_.accessDelegation d adr).2.2.2.2 := congrArg (fun q => q.2.2.2.2) h
  refine hd.of_eqs ?_ ?_
  · rw [hd']; exact accessDelegation_delSets.symm
  · rw [hd']; exact accessDelegation_getCode.symm

def Benv.EquivForDelegation (b1 b2 : Benv) : Prop :=
  b2.createdAccounts = b1.createdAccounts ∧
  ∀ a, (b1.state.getCode a).toList ≠ [] → b2.state.getCode a = b1.state.getCode a

lemma Benv.EquivForDelegation_refl (b : Benv) : Benv.EquivForDelegation b b := by
  refine ⟨rfl, fun a _ => rfl⟩

lemma Benv.EquivForDelegation_trans {b1 b2 b3 : Benv} (h12 : Benv.EquivForDelegation b1 b2) (h23 : Benv.EquivForDelegation b2 b3) :
    Benv.EquivForDelegation b1 b3 := by
  rcases h12 with ⟨h1c, h1code⟩
  rcases h23 with ⟨h2c, h2code⟩
  refine ⟨by rw [h2c, h1c], fun a ha => ?_⟩
  have h1 := h1code a ha
  have ha2' : (b2.state.getCode a).toList ≠ [] := by
    rw [h1]
    exact ha
  rw [h2code a ha2', h1]

lemma bind_eq_ok_Except {α β ε : Type} {x : Except ε α} {f : α → Except ε β} {res : β} :
    bind x f = Except.ok res → ∃ a, x = Except.ok a ∧ f a = Except.ok res := by
  intro h
  cases x with
  | error e =>
    dsimp [bind, Except.bind] at h
    contradiction
  | ok a =>
    dsimp [bind, Except.bind] at h
    exact ⟨a, rfl, h⟩

lemma Msg.NoDel.benvAfterTransfer {wa : Adr} {msg : Msg} {benv : Benv}
    (h_run : msg.benvAfterTransfer = .ok benv)
    (h : Msg.NoDel wa msg) : Msg.NoDel wa (msg.withBenv benv) := by
  by_cases h_stv : msg.shouldTransferValue = true
  · unfold Msg.benvAfterTransfer at h_run
    rw [h_stv] at h_run
    simp only [if_true] at h_run
    unfold Benv.subBal at h_run
    rcases h_sub : msg.benv.state.subBal msg.caller msg.value with _ | st_mid
    · rw [h_sub] at h_run
      simp only [Option.toExcept, bind, Option.bind, Except.bind] at h_run
      contradiction
    · rw [h_sub] at h_run
      simp only [Option.toExcept, bind, Option.bind, Except.bind] at h_run
      injection h_run with hB
      have hBc : benv.createdAccounts = msg.benv.createdAccounts := by
        rw [← hB]; rfl
      have h_code_add : benv.state.getCode wa = st_mid.getCode wa := by
        have hBs : benv.state = st_mid.addBal msg.currentTarget msg.value := by
          rw [← hB]; rfl
        rw [hBs]; exact State.addBal_getCode st_mid msg.currentTarget wa msg.value
      have h_code_sub : st_mid.getCode wa = msg.benv.state.getCode wa := by
        exact State.subBal_getCode h_sub
      have h_code : ((msg.withBenv benv).benv.state.getCode wa).toList ≠ [] := by
        change (benv.state.getCode wa).toList ≠ []
        rw [h_code_add, h_code_sub]
        exact h.code
      exact ⟨hBc ▸ h.ca, h_code⟩
  · unfold Msg.benvAfterTransfer at h_run
    rw [if_neg h_stv] at h_run
    have heq : benv = msg.benv := (Except.ok.inj h_run).symm
    subst heq
    exact h


/-! ## 4. Balance-sum relations and primitive state updates -/

def State.balSum (st : _root_.State) : Nat :=
  sum st.bal

def Devm.balSum (d : Devm) : Nat :=
  State.balSum d.state

def State.BalNoninc (pre post : _root_.State) : Prop :=
  State.balSum post ≤ State.balSum pre

def Devm.BalNoninc (pre post : Devm) : Prop :=
  Devm.balSum post ≤ Devm.balSum pre

def State.BalGrowth (allowance : Nat) (pre post : _root_.State) : Prop :=
  State.balSum post ≤ State.balSum pre + allowance

def State.SumNof (st : _root_.State) : Prop :=
  State.balSum st < 2 ^ 256

def Devm.SumNof (d : Devm) : Prop :=
  Devm.balSum d < 2 ^ 256

lemma balNoninc_refl_trans :
    (Reflexive State.BalNoninc ∧ Transitive State.BalNoninc) ∧
    (Reflexive Devm.BalNoninc ∧ Transitive Devm.BalNoninc) := by
  exact ⟨⟨fun _ => Nat.le_refl _, fun _ _ _ h1 h2 => Nat.le_trans h2 h1⟩,
         ⟨fun _ => Nat.le_refl _, fun _ _ _ h1 h2 => Nat.le_trans h2 h1⟩⟩

lemma State.SumNof.of_noninc {pre post : _root_.State}
    (hrel : State.BalNoninc pre post) (hnof : State.SumNof pre) :
    State.SumNof post :=
  Nat.lt_of_le_of_lt hrel hnof

lemma adr_toNat_lt_size_local (a : Adr) : a.toNat < 2 ^ 160 := by
  rw [← toAdr_toNat a, Nat.toNat_toAdr, Nat.lo]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

lemma sumBelow_setBal_eq_local (st : _root_.State) (a : Adr) (v : B256)
    (n : Nat) (hn : n ≤ a.toNat) (hsize : n ≤ 2 ^ 160) :
    sumBelow (fun x => (st.setBal a v).bal x) n =
      sumBelow (fun x => st.bal x) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumBelow_succ, sumBelow_succ]
    rw [ih (Nat.le_of_succ_le hn) (Nat.le_of_succ_le hsize)]
    have hnlt : n < a.toNat := Nat.lt_of_succ_le hn
    have hnsize : n < 2 ^ 160 := Nat.lt_of_succ_le hsize
    have hne : n.toAdr ≠ a := by
      intro heq
      have hnat := congrArg Adr.toNat heq
      rw [Nat.toNat_toAdr, Nat.lo_eq_of_lt hnsize] at hnat
      omega
    have hget : (st.setBal a v).get n.toAdr = st.get n.toAdr :=
      State.get_set_ne hne.symm
    have hbal : (st.setBal a v).bal n.toAdr = st.bal n.toAdr := by
      dsimp [State.bal, State.setBal]
      have hget' : (st.set a ((st.get a).withBal v)).get n.toAdr =
          st.get n.toAdr := by
        simpa [State.setBal] using hget
      rw [hget']
    rw [hbal]

lemma sumBelow_setBal_add_local (st : _root_.State) (a : Adr) (v : B256)
    (n : Nat) (hsize : n ≤ 2 ^ 160) (ha : a.toNat < n) :
    sumBelow (fun x => (st.setBal a v).bal x) n + (st.bal a).toNat =
      sumBelow (fun x => st.bal x) n + v.toNat := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sumBelow_succ, sumBelow_succ]
    have hnsize : n < 2 ^ 160 := Nat.lt_of_succ_le hsize
    rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha_lt | ha_eq
    · have hih := ih (Nat.le_of_succ_le hsize) ha_lt
      have hne : n.toAdr ≠ a := by
        intro heq
        have hnat := congrArg Adr.toNat heq
        rw [Nat.toNat_toAdr, Nat.lo_eq_of_lt hnsize] at hnat
        omega
      have hget : (st.setBal a v).get n.toAdr = st.get n.toAdr :=
        State.get_set_ne hne.symm
      change sumBelow (fun x => (st.setBal a v).bal x) n +
          ((st.setBal a v).get n.toAdr).bal.toNat + (st.bal a).toNat =
        sumBelow (fun x => st.bal x) n + (st.get n.toAdr).bal.toNat + v.toNat
      rw [hget]
      omega
    · have hprefix := sumBelow_setBal_eq_local st a v n
        (Nat.le_of_eq ha_eq.symm) (Nat.le_of_succ_le hsize)
      have haddr : n.toAdr = a := by
        rw [← ha_eq]
        exact toAdr_toNat a
      rw [hprefix, haddr]
      change sumBelow (fun x => st.bal x) n +
          ((st.setBal a v).get a).bal.toNat + (st.bal a).toNat =
        sumBelow (fun x => st.bal x) n + (st.get a).bal.toNat + v.toNat
      dsimp [State.setBal]
      rw [State.get_set_self]
      change sumBelow (fun x => st.bal x) n + v.toNat +
          (st.get a).bal.toNat =
        sumBelow (fun x => st.bal x) n + (st.get a).bal.toNat + v.toNat
      omega


lemma State.balSum_setBal (st : _root_.State) (a : Adr) (v : B256) :
    State.balSum (st.setBal a v) + (st.bal a).toNat =
      State.balSum st + v.toNat := by
  have hmax : Adr.max.toNat.succ = 2 ^ 160 := by decide
  have ha : a.toNat < Adr.max.toNat.succ := by
    rw [hmax]
    exact adr_toNat_lt_size_local a
  simpa [State.balSum, sum] using
    (sumBelow_setBal_add_local st a v Adr.max.toNat.succ
      (by rw [hmax]) ha)

lemma State.balSum_subBal {st mid : _root_.State} {a : Adr} {v : B256}
    (h : st.subBal a v = some mid) :
    State.balSum mid + v.toNat = State.balSum st := by
  unfold State.subBal at h
  split at h
  · contradiction
  · injection h with h_mid
    subst h_mid
    have h_set := State.balSum_setBal st a (st.bal a - v)
    rename_i h_not_lt
    have h_le : v ≤ st.bal a := le_of_not_gt h_not_lt
    have h_le2 : v.toNat ≤ (st.bal a).toNat := B256.toNat_le_toNat h_le
    rw [B256.toNat_sub_eq_of_le _ _ h_le] at h_set
    omega

lemma State.addBal_growth (st : _root_.State) (a : Adr) (v : B256) :
    State.BalGrowth v.toNat st (st.addBal a v) := by
  unfold State.addBal State.BalGrowth
  have h := State.balSum_setBal st a (st.bal a + v)
  rw [B256.toNat_add] at h
  unfold Nat.lo at h
  have h_mod := Nat.mod_le ((st.bal a).toNat + v.toNat) (2^256)
  omega

/- This lemma is the reusable conservation/nonincrease theorem for value transfer,
   including the recipient-overflow case.  -/
lemma State.sub_addBal_noninc {st mid : _root_.State}
    {src dst : Adr} {v : B256}
    (hsub : st.subBal src v = some mid) :
    State.BalNoninc st (mid.addBal dst v) := by
  dsimp [State.BalNoninc]
  have h1 := State.addBal_growth mid dst v
  dsimp [State.BalGrowth] at h1
  have h2 := State.balSum_subBal hsub
  omega

lemma State.setBal_zero_noninc (st : _root_.State) (a : Adr) :
    State.BalNoninc st (st.setBal a 0) := by
  unfold State.BalNoninc
  have h := State.balSum_setBal st a 0
  have hz : ((0 : B256).toNat) = 0 := by decide
  rw [hz, Nat.add_zero] at h
  omega

lemma Devm.balNoninc_of_state {pre post : Devm}
    (h : State.BalNoninc pre.state post.state) : Devm.BalNoninc pre post := by
  exact h

lemma Devm.balNoninc_of_getBal_eq {pre post : Devm}
    (h : post.getBal = pre.getBal) : Devm.BalNoninc pre post := by
  unfold Devm.BalNoninc Devm.balSum State.balSum
  change sum post.getBal ≤ sum pre.getBal
  rw [h]

/-! ## 5. Balance effects of instruction and message semantic units -/

def MessageExecution := Except (String × _root_.State × AdrSet × Tra) Devm

def MessageExecution.state : MessageExecution → _root_.State
  | .ok d => d.state
  | .error ⟨_, st, _, _⟩ => st

def MessageExecution.Rel
    (R : _root_.State → _root_.State → Prop)
    (pre : _root_.State) (out : MessageExecution) : Prop :=
  R pre out.state

def BenvExecution.state : Except (String × _root_.State × AdrSet × Tra) Benv →
    _root_.State
  | .ok benv => benv.state
  | .error ⟨_, st, _, _⟩ => st

/-! Error-side `getBal` frame lemmas, mirroring the generated `*_getCode_err`
family in `Blanc/Common.lean`: every regular-instruction error path leaves
balances unchanged. -/

lemma Devm.pop_map_snd_getBal_eq {devm devm1 : Devm} (hp : (devm.pop <&> Prod.snd) = .ok devm1) (a : Adr) : devm1.getBal a = devm.getBal a := by
  dsimp [(· <&> ·), Functor.mapRev, Functor.map, Except.map] at hp
  rcases hp2 : devm.pop with _ | ⟨x, devm2⟩
  · simp [hp2] at hp
  · simp [hp2] at hp
    rcases hp with ⟨_, rfl⟩
    exact (Devm.pop_worldEq_of_ok hp2).getBal a |>.symm

lemma Devm.pop_map_snd_getBal_err {devm : Devm} {err : String × Devm} (hp : (devm.pop <&> Prod.snd) = .error err) (a : Adr) : err.2.getBal a = devm.getBal a := by
  dsimp [(· <&> ·), Functor.mapRev, Functor.map, Except.map] at hp
  rcases hp2 : devm.pop with e | ⟨x, devm2⟩
  · simp [hp2] at hp; cases hp
    exact (Devm.pop_worldEq_of_error hp2).getBal a |>.symm
  · simp [hp2] at hp

lemma Devm.pop_getBal_err {err devm} (h : Devm.pop devm = .error err) (a : Adr) : err.2.getBal a = devm.getBal a := by
  exact (Devm.pop_worldEq_of_error h).getBal a |>.symm

lemma chargeGas_getBal_err {cost devm err} (h : chargeGas cost devm = .error err) (a : Adr) : err.2.getBal a = devm.getBal a := by
  exact (chargeGas_worldEq_of_error h).getBal a |>.symm

lemma Devm.push_getBal_err {v devm err} (h : Devm.push v devm = Except.error err) (a : Adr) : err.2.getBal a = devm.getBal a := by
  exact (liftMachExecution_worldEq_of_error (core := Mach.push v) h).getBal a |>.symm

lemma assert_getBal_err {cond : Prop} [Decidable cond] {msg : String} {devm : Devm} {err : String × Devm} (h : Except.assert cond (msg, devm) = Except.error err) (a : Adr) : err.2.getBal a = devm.getBal a := by
  unfold Except.assert at h
  split_ifs at h; try contradiction
  injection h with h1; rw [← h1]

lemma Devm.popToNat_getBal_err {devm err} (h : Devm.popToNat devm = .error err) (a : Adr) : err.2.getBal a = devm.getBal a := by
  exact (Devm.popToNat_worldEq_of_error h).getBal a |>.symm

lemma Devm.popToAdr_getBal_err {devm err} (h : Devm.popToAdr devm = .error err) (a : Adr) : err.2.getBal a = devm.getBal a := by
  exact (liftMach_worldEq_of_error (core := Mach.popToAdr) h).getBal a |>.symm

lemma getBal_err_of_bind {α} {ma : Except (String × Devm) α} {f : α → Execution}
    {devm : Devm} {a : Adr} {err : String × Devm}
    (run : (ma >>= f) = Except.error err)
    (getDevm : α → Devm)
    (h_first_ok : ∀ v, ma = Except.ok v → (getDevm v).getBal a = devm.getBal a)
    (h_first_err : ∀ e, ma = Except.error e → e.2.getBal a = devm.getBal a)
    (h_rest_err : ∀ v, ma = Except.ok v → f v = Except.error err → err.2.getBal a = (getDevm v).getBal a) :
    err.2.getBal a = devm.getBal a := by
  cases h_ma : ma
  case error e =>
    rw [h_ma, Except.bind_error] at run
    injection run with h_eq; subst h_eq
    exact h_first_err _ h_ma
  case ok v =>
    rw [h_ma, Except.bind_ok] at run
    have h1 := h_rest_err v h_ma run
    have h2 := h_first_ok v h_ma
    exact h1.trans h2

lemma Devm.popN_getBal_err {n : Nat} {devm : Devm} {err : String × Devm}
    (hp : devm.popN n = Except.error err) (a : Adr) :
    err.2.getBal a = devm.getBal a := by
  exact (liftMach_worldEq_of_error (core := (Mach.popN · n)) hp).getBal a |>.symm

lemma pushItem_getBal_err {x c devm err} (h : pushItem x c devm = Except.error err) (a : Adr) : err.2.getBal a = devm.getBal a := by
  exact (liftMachExecution_worldEq_of_error (core := Mach.pushItem x c) h).getBal a |>.symm

lemma applyUnary_getBal_err {f : B256 → B256} {cost devm err}
    (h : applyUnary f cost devm = Except.error err) (a : Adr) :
    err.2.getBal a = devm.getBal a := by
  exact (liftMachExecution_worldEq_of_error (core := Mach.applyUnary f cost) h).getBal a |>.symm

lemma applyBinary_getBal_err {f : B256 → B256 → B256} {cost devm err}
    (h : applyBinary f cost devm = Except.error err) (a : Adr) :
    err.2.getBal a = devm.getBal a := by
  exact (liftMachExecution_worldEq_of_error (core := Mach.applyBinary f cost) h).getBal a |>.symm

lemma applyTernary_getBal_err {f : B256 → B256 → B256 → B256} {cost devm err}
    (h : applyTernary f cost devm = Except.error err) (a : Adr) :
    err.2.getBal a = devm.getBal a := by
  exact (liftMachExecution_worldEq_of_error (core := Mach.applyTernary f cost) h).getBal a |>.symm

lemma Rinst.inv_getBal_err
    {pc sevm devm r err}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = Except.error err) (a : Adr) :
    err.2.getBal a = devm.getBal a := by
  rcases eq_or_ne r .sstore with rfl | hs
  · have hf := Rinst.sstore_run_stateWriteFrame pc devm sevm; rw [run] at hf
    exact (Devm.StateWriteFrame.getBal_eq hf a).symm
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc devm sevm; rw [run] at hf
    exact congrFun (congrArg (fun s => s.bal) hf.state).symm a
  · have hf := Rinst.run_instructionFrame pc sevm devm r hs ht; rw [run] at hf; exact (hf.getBal a).symm

lemma Rinst.balance_effect (r : Rinst) :
    Rinst.Effect Devm.BalNoninc r := by
  intro pc sevm pre out hrun
  cases out with
  | ok post => exact Devm.balNoninc_of_getBal_eq (Rinst.inv_bal hrun).symm
  | error err => exact Devm.balNoninc_of_getBal_eq (funext fun a => Rinst.inv_getBal_err hrun a)

lemma Jinst.balance_effect (j : Jinst) :
    Jinst.Effect Devm.BalNoninc j := by
  intro evm out hrun
  have hf := Jinst.run_instructionFrame evm j
  rw [hrun] at hf
  cases out <;> exact Devm.balNoninc_of_getBal_eq
    (funext fun a => (hf.getBal a).symm)

lemma Ninst.push_balance_effectGen {xs : B8L} {hxs : xs.length ≤ 32} :
    Ninst.EffectGen Devm.BalNoninc (.push xs hxs) := by
  exact Ninst.push_effectGen_of_instructionFrame (R := Devm.BalNoninc)
    (fun _ _ hf =>
      Devm.balNoninc_of_getBal_eq (funext fun a => (hf.getBal a).symm))

lemma Linst.dest_balance_effect :
    Linst.Effect Devm.BalNoninc .dest := by
  intro sevm pre out run
  dsimp [Linst.Run, Linst.run] at run
  revert run
  dsimp [bind, Except.bind]
  cases h1 : pre.popToAdr <;> dsimp
  case error err =>
    intro run
    rw [← run]
    apply Devm.balNoninc_of_getBal_eq
    rw [Devm.popToAdr_err_snd h1]
  case ok res1 =>
    have hpop : res1.2.getBal = pre.getBal := by
      funext a
      exact Devm.popToAdr_getBal_eq h1 a
    have hacc :
        (if res1.1 ∉ res1.2.accessedAddresses then
            (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess)
          else (res1.2, gasSelfDestruct)).1.getBal = res1.2.getBal := by
      funext a
      split <;> rfl
    cases h2 : chargeGas
        (if ((if res1.1 ∉ res1.2.accessedAddresses then
                    (addAccessedAddress res1.2 res1.1,
                      gasSelfDestruct + gasColdAccountAccess)
                  else (res1.2, gasSelfDestruct)).1.getAcct res1.1).Empty ∧
              ¬(res1.2.getAcct sevm.currentTarget).bal = 0 then
          (if res1.1 ∉ res1.2.accessedAddresses then
                (addAccessedAddress res1.2 res1.1,
                  gasSelfDestruct + gasColdAccountAccess)
              else (res1.2, gasSelfDestruct)).2 + gasSelfDestructNewAccount
        else
          (if res1.1 ∉ res1.2.accessedAddresses then
              (addAccessedAddress res1.2 res1.1,
                gasSelfDestruct + gasColdAccountAccess)
            else (res1.2, gasSelfDestruct)).2)
        (if res1.1 ∉ res1.2.accessedAddresses then
            (addAccessedAddress res1.2 res1.1,
              gasSelfDestruct + gasColdAccountAccess)
          else (res1.2, gasSelfDestruct)).1 <;> dsimp
    case error err =>
      intro run
      rw [← run]
      apply Devm.balNoninc_of_getBal_eq
      rw [chargeGas_err_snd h2]
      exact hacc.trans hpop
    case ok res2 =>
      have hpre : res2.getBal = pre.getBal := by
        funext a
        exact (chargeGas_getBal_eq h2 a).trans
          (congrFun (hacc.trans hpop) a)
      cases h3 : assertDynamic sevm res2
      case error err =>
        intro run
        rw [← run]
        apply Devm.balNoninc_of_getBal_eq
        have herr : err.2 = res2 := by
          dsimp [assertDynamic] at h3
          exact Except.assert_err_snd h3
        rw [herr]
        exact hpre
      case ok _ =>
        cases h4 : res2.subBal sevm.currentTarget
            (res1.2.getAcct sevm.currentTarget).bal <;> dsimp [Option.toExcept]
        case none =>
          intro run
          rw [← run]
          exact Devm.balNoninc_of_getBal_eq hpre
        case some res3 =>
          have hsub : res2.state.subBal sevm.currentTarget
              (res1.2.getAcct sevm.currentTarget).bal = some res3.state := by
            dsimp [Devm.subBal, Option.bind] at h4
            cases hs : res2.state.subBal sevm.currentTarget
                (res1.2.getAcct sevm.currentTarget).bal
            · rw [hs] at h4
              contradiction
            · rw [hs] at h4
              injection h4 with heq
              subst heq
              rfl
          have htransfer : State.BalNoninc pre.state
              (res3.addBal res1.1
                (res1.2.getAcct sevm.currentTarget).bal).state := by
            have ht := State.sub_addBal_noninc (dst := res1.1) hsub
            have hbal : res2.state.bal = pre.state.bal := hpre
            unfold State.BalNoninc State.balSum at ht ⊢
            rw [hbal] at ht
            exact ht
          by_cases hdel : sevm.currentTarget ∈
              (res3.addBal res1.1
                (res1.2.getAcct sevm.currentTarget).bal).createdAccounts
          · simp only [hdel, if_pos]
            intro run
            rw [← run]
            unfold Execution.Rel Outcome.Rel
            apply Devm.balNoninc_of_state
            apply balNoninc_refl_trans.1.2 htransfer
            exact State.setBal_zero_noninc _ _
          · simp only [hdel]
            intro run
            rw [← run]
            unfold Execution.Rel Outcome.Rel
            exact Devm.balNoninc_of_state htransfer

lemma Linst.balance_effect (l : Linst) :
    Linst.Effect Devm.BalNoninc l := by
  rcases eq_or_ne l .dest with rfl | h_not_dest
  · exact Linst.dest_balance_effect
  · intro sevm pre out run
    have hf := Linst.run_instructionFrame sevm pre l h_not_dest
    rw [run] at hf
    cases out <;> exact Devm.balNoninc_of_getBal_eq
      (funext fun a => (hf.getBal a).symm)

lemma Msg.benvAfterTransfer_balance_effect {msg : Msg}
    {out : Except (String × _root_.State × AdrSet × Tra) Benv}
    (h : msg.benvAfterTransfer = out) :
    State.BalNoninc msg.benv.state (BenvExecution.state out) := by
  by_cases h_stv : msg.shouldTransferValue = true
  · unfold Msg.benvAfterTransfer at h
    rw [h_stv] at h
    simp only [if_true] at h
    unfold Benv.subBal at h
    rcases h_sub : msg.benv.state.subBal msg.caller msg.value with _ | st_mid
    · rw [h_sub] at h
      simp only [Option.toExcept, bind, Option.bind, Except.bind] at h
      rw [← h]
      exact Nat.le_refl _
    · rw [h_sub] at h
      simp only [Option.toExcept, bind, Option.bind, Except.bind] at h
      rw [← h]
      change State.BalNoninc msg.benv.state (st_mid.addBal msg.currentTarget msg.value)
      exact State.sub_addBal_noninc h_sub
  · unfold Msg.benvAfterTransfer at h
    rw [if_neg h_stv] at h
    rw [← h]
    exact Nat.le_refl _

lemma processCreateMessage.chargeCodeGas_balance_effect
    {pre : Devm} {out : Execution}
    (h : processCreateMessage.chargeCodeGas pre = out) :
    Execution.Rel Devm.BalNoninc pre out := by
  rcases out with ⟨err, d⟩ | d <;> simp only [Execution.Rel, Outcome.Rel]
  · simp only [processCreateMessage.chargeCodeGas] at h
    split at h
    · simp only [Except.error.injEq] at h
      cases h
      exact balNoninc_refl_trans.2.1 pre
    · dsimp [Bind.bind, Except.bind] at h
      split at h
      · rename_i code neq ex errCharge hCharge
        simp only [Except.error.injEq] at h
        cases h
        have hstate := chargeGas_err_snd hCharge
        change d = pre at hstate
        rw [hstate]
        exact balNoninc_refl_trans.2.1 pre
      · split at h
        · simp only [Except.error.injEq] at h
          cases h
          rename_i code neq ex hSize hCharge
          have hb := Devm.burn_of_chargeGas hCharge
          apply Devm.balNoninc_of_state
          rw [hb.state]
          exact balNoninc_refl_trans.1.1 d.state
        · cases h
  · simp only [id]
    simp only [processCreateMessage.chargeCodeGas] at h
    split at h
    · cases h
    · dsimp [Bind.bind, Except.bind] at h
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i code neq ex hSize hCharge
          simp only [Except.ok.injEq] at h
          cases h
          have hb := Devm.burn_of_chargeGas hSize
          apply Devm.balNoninc_of_state
          rw [hb.state]
          exact balNoninc_refl_trans.1.1 d.state

lemma executePrecomp_balance_effect {evm : Evm} {a : Adr} {out : Execution}
    (h : executePrecomp evm a = out) :
    Execution.Rel Devm.BalNoninc evm.dyna out := by
  subst out
  unfold executePrecomp applyPrecompResult Execution.Rel Outcome.Rel
    Devm.BalNoninc Devm.balSum State.balSum
  cases precompileRun evm a <;> rfl

lemma ProcessMessage.balance_effect {msg : Msg} {xl : Xlot}
    {out : MessageExecution}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (run : ProcessMessage msg xl out) :
    MessageExecution.Rel State.BalNoninc msg.benv.state out := by
  dsimp only [ProcessMessage] at run
  rcases run with ⟨x, hbt, hout, hnone⟩ | ⟨benv, hbt, ex', hec, hsplit⟩
  · have ht := Msg.benvAfterTransfer_balance_effect hbt
    unfold MessageExecution.Rel
    rw [hout]
    exact ht
  · have htransfer := Msg.benvAfterTransfer_balance_effect hbt
    have hexec : State.BalNoninc benv.state (MessageExecution.state ex') := by
      have handle_balance {pre : Devm} {raw : Execution} {handled : MessageExecution}
          (hb : Execution.Rel Devm.BalNoninc pre raw)
          (hh : executeCode.handleError raw = handled) :
          State.BalNoninc pre.state (MessageExecution.state handled) := by
        rcases raw with ⟨err, d⟩ | d
        · simp only [executeCode.handleError] at hh
          split at hh
          · subst handled
            exact hb
          · split at hh
            · subst handled
              exact hb
            · subst handled
              exact hb
        · simp only [executeCode.handleError] at hh
          subst handled
          exact hb
      unfold ExecuteCode at hec
      rcases hca : (msg.withBenv benv).codeAddress with _ | adr
      · rw [hca] at hec
        dsimp only at hec
        rcases hec with ⟨raw, hxl_eq, hh⟩
        rw [hxl_eq] at hxl
        have hinit : (initEvm (msg.withBenv benv)).dyna.state = benv.state := rfl
        rw [← hinit]
        exact handle_balance hxl hh
      · rw [hca] at hec
        dsimp only at hec
        by_cases hpre : adr.isPrecomp
        · rw [if_pos hpre] at hec
          rcases hec with ⟨_, hh⟩
          have hp := executePrecomp_balance_effect
            (h := (rfl : executePrecomp (initEvm (msg.withBenv benv)) adr =
              executePrecomp (initEvm (msg.withBenv benv)) adr))
          have hinit : (initEvm (msg.withBenv benv)).dyna.state = benv.state := rfl
          rw [← hinit]
          exact handle_balance hp hh
        · rw [if_neg hpre] at hec
          rcases hec with ⟨raw, hxl_eq, hh⟩
          rw [hxl_eq] at hxl
          have hinit : (initEvm (msg.withBenv benv)).dyna.state = benv.state := rfl
          rw [← hinit]
          exact handle_balance hxl hh
    rcases hsplit with ⟨x, hex', hout⟩ | ⟨evm, hex', hfinal⟩
    · subst ex'
      subst out
      exact Nat.le_trans hexec htransfer
    · by_cases herr : evm.error.isSome = true
      · rw [if_pos herr] at hfinal
        rw [← hfinal]
        exact balNoninc_refl_trans.1.1 _
      · rw [if_neg herr] at hfinal
        subst ex'
        rw [← hfinal]
        exact Nat.le_trans hexec htransfer

lemma ProcessCreateMessage.balance_effect {msg : Msg} {xl : Xlot}
    {out : MessageExecution}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (run : ProcessCreateMessage msg xl out) :
    MessageExecution.Rel State.BalNoninc msg.benv.state out := by
  dsimp only [ProcessCreateMessage] at run
  rcases run with ⟨ex', run_pm, h_split⟩
  have h_seed : (processCreateMessage.msg msg).benv.state.bal = msg.benv.state.bal := by
    change ((msg.benv.state.setStor msg.currentTarget .empty).incrNonce
      msg.currentTarget).bal = msg.benv.state.bal
    rw [State.incrNonce_bal, State.setStor_bal]
  have h_pm := ProcessMessage.balance_effect hxl run_pm
  unfold MessageExecution.Rel State.BalNoninc State.balSum at h_pm
  rw [h_seed] at h_pm
  dsimp only [Except.Split] at h_split
  rcases h_split with ⟨x, h_ex', h_out⟩ | ⟨evm, h_ex', h_body⟩
  · subst ex'
    subst out
    exact h_pm
  · subst ex'
    by_cases h_err : evm.error.isNone = true
    · rw [if_pos h_err] at h_body
      rcases h_cg : processCreateMessage.chargeCodeGas evm with ⟨err, evm'⟩ | evm'
      · rw [h_cg] at h_body
        dsimp only at h_body
        by_cases h_halt : isExceptionalHalt err
        · rw [if_pos h_halt] at h_body
          rw [← h_body]
          exact balNoninc_refl_trans.1.1 _
        · rw [if_neg h_halt] at h_body
          have h_charge := processCreateMessage.chargeCodeGas_balance_effect h_cg
          unfold Execution.Rel Outcome.Rel Devm.BalNoninc Devm.balSum State.balSum at h_charge
          dsimp only [id] at h_charge
          dsimp only [MessageExecution.state] at h_pm
          rw [← h_body]
          exact Nat.le_trans h_charge h_pm
      · rw [h_cg] at h_body
        dsimp only at h_body
        have h_charge := processCreateMessage.chargeCodeGas_balance_effect h_cg
        unfold Execution.Rel Outcome.Rel Devm.BalNoninc Devm.balSum State.balSum at h_charge
        dsimp only [id] at h_charge
        dsimp only [MessageExecution.state] at h_pm
        rw [← h_body]
        change sum (evm'.state.setCode msg.currentTarget ⟨⟨evm'.output⟩⟩).bal ≤
          sum msg.benv.state.bal
        rw [State.setCode_bal]
        exact Nat.le_trans h_charge h_pm
    · rw [if_neg h_err] at h_body
      rw [← h_body]
      exact balNoninc_refl_trans.1.1 _

lemma GenericCall.balance_effect
    {sevm : Sevm} {pre : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv istat : Bool}
    {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    {xl : Xlot} {out : Execution}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (run : GenericCall sevm pre gas value caller target codeAddress
      stv istat ii is oi os code dp xl out) :
    Execution.Rel Devm.BalNoninc pre out := by
  dsimp only [GenericCall] at run
  rcases run with ⟨evm1, h_evm1, run⟩
  split_ifs at run with h_depth
  · -- depth limit reached : call fails, state unchanged
    rcases run with ⟨_, h_push⟩
    have h_bal : Devm.BalNoninc pre (evm1.withGasLeft (evm1.gasLeft + gas)) := by
      apply Devm.balNoninc_of_state
      rw [h_evm1]
      exact balNoninc_refl_trans.1.1 _
    rcases out with ⟨err, d⟩ | d
    · simp only [Execution.Rel, Outcome.Rel]
      refine balNoninc_refl_trans.2.2 h_bal ?_
      apply Devm.balNoninc_of_getBal_eq
      funext a
      exact Devm.push_getBal_err h_push a
    · simp only [Execution.Rel, Outcome.Rel, id]
      refine balNoninc_refl_trans.2.2 h_bal ?_
      apply Devm.balNoninc_of_state
      rw [← (Devm.push_of_push h_push).state]
      exact balNoninc_refl_trans.1.1 _
  · rcases run with ⟨calldata, _, run⟩
    rcases run with ⟨childMsg, h_cm, run⟩
    rcases run with ⟨ex', run_pm, h_split⟩
    have h_pm := ProcessMessage.balance_effect hxl run_pm
    have h_st : childMsg.benv.state = pre.state := by rw [h_cm, h_evm1]; rfl
    unfold MessageExecution.Rel at h_pm
    rw [h_st] at h_pm
    rcases ex' with ⟨e1, e2, e3, e4⟩ | child
    · dsimp only [liftToExecution] at h_split
      rcases h_split with ⟨x, h_err, h_out⟩ | ⟨c, h_contra, _⟩
      · have hx := Except.error.inj h_err
        subst hx
        rw [h_out]
        simp only [Execution.Rel, Outcome.Rel]
        exact h_pm
      · cases h_contra
    · dsimp only [liftToExecution] at h_split
      rcases h_split with ⟨x, h_contra, _⟩ | ⟨c, h_c, h_body⟩
      · cases h_contra
      have hc := Except.ok.inj h_c
      subst hc
      dsimp only [MessageExecution.state] at h_pm
      by_cases h_err : child.error.isSome = true
      · rw [if_pos h_err] at h_body
        have h_bal : Devm.BalNoninc pre (incorporateChildOnError evm1 child child.output) := by
          apply Devm.balNoninc_of_state
          exact h_pm
        rcases h_body with ⟨e, h_pusherr, h_out⟩ | ⟨evm2, h_push, h_out⟩
        · rw [h_out]
          simp only [Execution.Rel, Outcome.Rel]
          refine balNoninc_refl_trans.2.2 h_bal ?_
          apply Devm.balNoninc_of_getBal_eq
          funext a
          exact Devm.push_getBal_err h_pusherr a
        · rw [← h_out]
          simp only [Execution.Rel, Outcome.Rel, id]
          refine balNoninc_refl_trans.2.2 h_bal ?_
          apply Devm.balNoninc_of_state
          show State.BalNoninc _ evm2.state
          rw [← (Devm.push_of_push h_push).state]
          exact balNoninc_refl_trans.1.1 _
      · rw [if_neg h_err] at h_body
        have h_bal : Devm.BalNoninc pre (incorporateChildOnSuccess evm1 child child.output) := by
          apply Devm.balNoninc_of_state
          exact h_pm
        rcases h_body with ⟨e, h_pusherr, h_out⟩ | ⟨evm2, h_push, h_out⟩
        · rw [h_out]
          simp only [Execution.Rel, Outcome.Rel]
          refine balNoninc_refl_trans.2.2 h_bal ?_
          apply Devm.balNoninc_of_getBal_eq
          funext a
          exact Devm.push_getBal_err h_pusherr a
        · rw [← h_out]
          simp only [Execution.Rel, Outcome.Rel, id]
          refine balNoninc_refl_trans.2.2 h_bal ?_
          apply Devm.balNoninc_of_state
          show State.BalNoninc _ evm2.state
          rw [← (Devm.push_of_push h_push).state]
          exact balNoninc_refl_trans.1.1 _

lemma GenericCreate.balance_effect
    {sevm : Sevm} {pre : Devm} {endowment : B256} {newAddress : Adr}
    {mi ms : Nat} {xl : Xlot} {out : Execution}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (run : GenericCreate sevm pre endowment newAddress mi ms xl out) :
    Execution.Rel Devm.BalNoninc pre out := by
  dsimp only [GenericCreate] at run
  rcases run with ⟨calldata, _, run⟩
  rcases run with ⟨x, h_err, h_out, _⟩ | ⟨_, _, run⟩
  · -- init code size assertion fails : state unchanged
    rw [h_out]
    simp only [Execution.Rel, Outcome.Rel]
    apply Devm.balNoninc_of_getBal_eq
    funext a
    exact assert_getBal_err h_err a
  rcases run with ⟨devm1, h_d1, run⟩
  rcases run with ⟨createMsgGas, _, run⟩
  rcases run with ⟨devm2, h_d2, run⟩
  have h_st1 : devm1.state = pre.state := by rw [h_d1]; rfl
  have h_st2 : devm2.state = devm1.state := by rw [h_d2]
  rcases run with ⟨x, h_err, h_out, _⟩ | ⟨_, _, run⟩
  · -- static context assertion fails : state unchanged
    rw [h_out]
    simp only [Execution.Rel, Outcome.Rel]
    have h_bal2 : Devm.BalNoninc pre devm2 := by
      apply Devm.balNoninc_of_state
      rw [h_st2, h_st1]
      exact balNoninc_refl_trans.1.1 _
    refine balNoninc_refl_trans.2.2 h_bal2 ?_
    apply Devm.balNoninc_of_getBal_eq
    funext a
    dsimp only [assertDynamic] at h_err
    exact assert_getBal_err h_err a
  rcases run with ⟨devm3, h_d3, run⟩
  rcases run with ⟨sender, _, run⟩
  have h_st3 : devm3.state = devm2.state := by rw [h_d3]
  have h_bal3 : Devm.BalNoninc pre devm3 := by
    apply Devm.balNoninc_of_state
    rw [h_st3, h_st2, h_st1]
    exact balNoninc_refl_trans.1.1 _
  split_ifs at run with h_c1
  · -- sender balance/nonce/depth failure : create fails, state unchanged
    rcases run with ⟨_, h_push⟩
    have h_bal : Devm.BalNoninc pre {devm3 with gasLeft := devm3.gasLeft + createMsgGas} := by
      apply Devm.balNoninc_of_state
      show State.BalNoninc pre.state devm3.state
      exact h_bal3
    rcases out with ⟨err, d⟩ | d
    · simp only [Execution.Rel, Outcome.Rel]
      refine balNoninc_refl_trans.2.2 h_bal ?_
      apply Devm.balNoninc_of_getBal_eq
      funext a
      exact Devm.push_getBal_err h_push a
    · simp only [Execution.Rel, Outcome.Rel, id]
      refine balNoninc_refl_trans.2.2 h_bal ?_
      apply Devm.balNoninc_of_state
      rw [← (Devm.push_of_push h_push).state]
      exact balNoninc_refl_trans.1.1 _
  · rcases run with ⟨devm4, h_d4, run⟩
    have h_bal4 : Devm.BalNoninc pre devm4 := by
      unfold Devm.BalNoninc Devm.balSum State.balSum
      rw [h_d4, Devm.incrNonce_state, State.incrNonce_bal, h_st3, h_st2, h_st1]
    split_ifs at run with h_c2
    · -- target account exists : create fails, state unchanged
      rcases run with ⟨_, h_push⟩
      rcases out with ⟨err, d⟩ | d
      · simp only [Execution.Rel, Outcome.Rel]
        refine balNoninc_refl_trans.2.2 h_bal4 ?_
        apply Devm.balNoninc_of_getBal_eq
        funext a
        exact Devm.push_getBal_err h_push a
      · simp only [Execution.Rel, Outcome.Rel, id]
        refine balNoninc_refl_trans.2.2 h_bal4 ?_
        apply Devm.balNoninc_of_state
        rw [← (Devm.push_of_push h_push).state]
        exact balNoninc_refl_trans.1.1 _
    · rcases run with ⟨childMsg, h_cm, run⟩
      rcases run with ⟨ex', run_pcm, h_split⟩
      have h_pcm := ProcessCreateMessage.balance_effect hxl run_pcm
      have h_st : childMsg.benv.state = devm4.state := by rw [h_cm]
      unfold MessageExecution.Rel at h_pcm
      rw [h_st] at h_pcm
      rcases ex' with ⟨e1, e2, e3, e4⟩ | child
      · dsimp only [liftToExecution] at h_split
        rcases h_split with ⟨x, h_err, h_out⟩ | ⟨c, h_contra, _⟩
        · have hx := Except.error.inj h_err
          subst hx
          rw [h_out]
          simp only [Execution.Rel, Outcome.Rel]
          refine balNoninc_refl_trans.2.2 h_bal4 ?_
          apply Devm.balNoninc_of_state
          exact h_pcm
        · cases h_contra
      · dsimp only [liftToExecution] at h_split
        rcases h_split with ⟨x, h_contra, _⟩ | ⟨c, h_c, h_body⟩
        · cases h_contra
        have hc := Except.ok.inj h_c
        subst hc
        dsimp only [MessageExecution.state] at h_pcm
        by_cases h_err : child.error.isSome = true
        · rw [if_pos h_err] at h_body
          have h_bal : Devm.BalNoninc pre (incorporateChildOnError devm4 child child.output) := by
            refine balNoninc_refl_trans.2.2 h_bal4 ?_
            apply Devm.balNoninc_of_state
            exact h_pcm
          rcases out with ⟨err2, d⟩ | d
          · simp only [Execution.Rel, Outcome.Rel]
            refine balNoninc_refl_trans.2.2 h_bal ?_
            apply Devm.balNoninc_of_getBal_eq
            funext a
            exact Devm.push_getBal_err h_body a
          · simp only [Execution.Rel, Outcome.Rel, id]
            refine balNoninc_refl_trans.2.2 h_bal ?_
            apply Devm.balNoninc_of_state
            rw [← (Devm.push_of_push h_body).state]
            exact balNoninc_refl_trans.1.1 _
        · rw [if_neg h_err] at h_body
          have h_bal : Devm.BalNoninc pre (incorporateChildOnSuccess devm4 child []) := by
            refine balNoninc_refl_trans.2.2 h_bal4 ?_
            apply Devm.balNoninc_of_state
            exact h_pcm
          rcases out with ⟨err2, d⟩ | d
          · simp only [Execution.Rel, Outcome.Rel]
            refine balNoninc_refl_trans.2.2 h_bal ?_
            apply Devm.balNoninc_of_getBal_eq
            funext a
            exact Devm.push_getBal_err h_body a
          · simp only [Execution.Rel, Outcome.Rel, id]
            refine balNoninc_refl_trans.2.2 h_bal ?_
            apply Devm.balNoninc_of_state
            rw [← (Devm.push_of_push h_body).state]
            exact balNoninc_refl_trans.1.1 _

lemma Xinst.balance_effectGen (x : Xinst) :
    Xinst.EffectGen Devm.BalNoninc x := by
  intro sevm pre xl out hxl run
  have herr : ∀ {d : Devm} {err : String × Devm},
      (∀ a, d.getBal a = pre.getBal a) →
      (∀ a, err.2.getBal a = d.getBal a) →
      Execution.Rel Devm.BalNoninc pre (Except.error err) := by
    intro d err hg hgb
    simp only [Execution.Rel, Outcome.Rel]
    apply Devm.balNoninc_of_getBal_eq
    funext a
    rw [hgb a, hg a]
  have hok : ∀ {d : Devm} {o : Execution},
      (∀ a, d.getBal a = pre.getBal a) →
      Execution.Rel Devm.BalNoninc d o →
      Execution.Rel Devm.BalNoninc pre o := by
    intro d o hg h
    have hpd : Devm.BalNoninc pre d := Devm.balNoninc_of_getBal_eq (funext hg)
    cases o <;> exact balNoninc_refl_trans.2.2 hpd h
  have h_ad : ∀ (d : Devm) (adr a : Adr),
      (accessDelegation d adr).2.2.2.2.getBal a = d.getBal a := by
    intro d adr a
    dsimp only [accessDelegation]
    split_ifs <;> rfl
  cases x
  case create =>
    dsimp only [Xinst.Run] at run
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨endowment, d1⟩, e1, run⟩
    · rw [h_out]; exact herr (fun _ => rfl) (Devm.pop_getBal_err he)
    have hg1 : ∀ a, d1.getBal a = pre.getBal a := Devm.pop_getBal_eq e1
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨mi, d2⟩, e2, run⟩
    · rw [h_out]; exact herr hg1 (Devm.popToNat_getBal_err he)
    have hg2 : ∀ a, d2.getBal a = pre.getBal a :=
      fun a => (Devm.popToNat_getBal_eq e2 a).trans (hg1 a)
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨ms, d3⟩, e3, run⟩
    · rw [h_out]; exact herr hg2 (Devm.popToNat_getBal_err he)
    have hg3 : ∀ a, d3.getBal a = pre.getBal a :=
      fun a => (Devm.popToNat_getBal_eq e3 a).trans (hg2 a)
    rcases run with ⟨extendCost, _, run⟩
    rcases run with ⟨initCodeCost, _, run⟩
    rcases run with ⟨er, he, h_out, _⟩ | ⟨d4, e4, run⟩
    · rw [h_out]; exact herr hg3 (chargeGas_getBal_err he)
    have hg4 : ∀ a, d4.getBal a = pre.getBal a :=
      fun a => (chargeGas_getBal_eq e4 a).trans (hg3 a)
    rcases run with ⟨d5, h_d5, run⟩
    have hg5 : ∀ a, d5.getBal a = pre.getBal a := by
      intro a; rw [h_d5]; exact hg4 a
    rcases run with ⟨newAddress, _, run⟩
    exact hok hg5 (GenericCreate.balance_effect hxl run)
  case create2 =>
    dsimp only [Xinst.Run] at run
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨endowment, d1⟩, e1, run⟩
    · rw [h_out]; exact herr (fun _ => rfl) (Devm.pop_getBal_err he)
    have hg1 : ∀ a, d1.getBal a = pre.getBal a := Devm.pop_getBal_eq e1
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨mi, d2⟩, e2, run⟩
    · rw [h_out]; exact herr hg1 (Devm.popToNat_getBal_err he)
    have hg2 : ∀ a, d2.getBal a = pre.getBal a :=
      fun a => (Devm.popToNat_getBal_eq e2 a).trans (hg1 a)
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨ms, d3⟩, e3, run⟩
    · rw [h_out]; exact herr hg2 (Devm.popToNat_getBal_err he)
    have hg3 : ∀ a, d3.getBal a = pre.getBal a :=
      fun a => (Devm.popToNat_getBal_eq e3 a).trans (hg2 a)
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨salt, d4⟩, e4, run⟩
    · rw [h_out]; exact herr hg3 (Devm.pop_getBal_err he)
    have hg4 : ∀ a, d4.getBal a = pre.getBal a :=
      fun a => (Devm.pop_getBal_eq e4 a).trans (hg3 a)
    rcases run with ⟨extendCost, _, run⟩
    rcases run with ⟨initCodeHashCost, _, run⟩
    rcases run with ⟨initCodeCost, _, run⟩
    rcases run with ⟨er, he, h_out, _⟩ | ⟨d5, e5, run⟩
    · rw [h_out]; exact herr hg4 (chargeGas_getBal_err he)
    have hg5 : ∀ a, d5.getBal a = pre.getBal a :=
      fun a => (chargeGas_getBal_eq e5 a).trans (hg4 a)
    rcases run with ⟨d6, h_d6, run⟩
    have hg6 : ∀ a, d6.getBal a = pre.getBal a := by
      intro a; rw [h_d6]; exact hg5 a
    rcases run with ⟨newAddress, _, run⟩
    exact hok hg6 (GenericCreate.balance_effect hxl run)
  case call =>
    dsimp only [Xinst.Run] at run
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨gas, d1⟩, e1, run⟩
    · rw [h_out]; exact herr (fun _ => rfl) (Devm.pop_getBal_err he)
    have hg1 : ∀ a, d1.getBal a = pre.getBal a := Devm.pop_getBal_eq e1
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨callee, d2⟩, e2, run⟩
    · rw [h_out]; exact herr hg1 (Devm.popToAdr_getBal_err he)
    have hg2 : ∀ a, d2.getBal a = pre.getBal a :=
      fun a => (Devm.popToAdr_getBal_eq e2 a).trans (hg1 a)
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨value, d3⟩, e3, run⟩
    · rw [h_out]; exact herr hg2 (Devm.pop_getBal_err he)
    have hg3 : ∀ a, d3.getBal a = pre.getBal a :=
      fun a => (Devm.pop_getBal_eq e3 a).trans (hg2 a)
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨ii, d4⟩, e4, run⟩
    · rw [h_out]; exact herr hg3 (Devm.popToNat_getBal_err he)
    have hg4 : ∀ a, d4.getBal a = pre.getBal a :=
      fun a => (Devm.popToNat_getBal_eq e4 a).trans (hg3 a)
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨is, d5⟩, e5, run⟩
    · rw [h_out]; exact herr hg4 (Devm.popToNat_getBal_err he)
    have hg5 : ∀ a, d5.getBal a = pre.getBal a :=
      fun a => (Devm.popToNat_getBal_eq e5 a).trans (hg4 a)
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨oi, d6⟩, e6, run⟩
    · rw [h_out]; exact herr hg5 (Devm.popToNat_getBal_err he)
    have hg6 : ∀ a, d6.getBal a = pre.getBal a :=
      fun a => (Devm.popToNat_getBal_eq e6 a).trans (hg5 a)
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨os, d7⟩, e7, run⟩
    · rw [h_out]; exact herr hg6 (Devm.popToNat_getBal_err he)
    have hg7 : ∀ a, d7.getBal a = pre.getBal a :=
      fun a => (Devm.popToNat_getBal_eq e7 a).trans (hg6 a)
    rcases run with ⟨extendCost, _, run⟩
    rcases run with ⟨preAccessCost, _, run⟩
    rcases run with ⟨d8, h_d8, run⟩
    have hg8 : ∀ a, d8.getBal a = pre.getBal a := by
      intro a; rw [h_d8]; exact hg7 a
    rcases run with ⟨⟨dp, na, code0, dagc, d9⟩, h_d9, run⟩
    have hg9 : ∀ a, d9.getBal a = pre.getBal a := by
      intro a
      have hq := congrArg (fun q => (q.2.2.2.2 : Devm).getBal a) h_d9
      dsimp only at hq
      rw [hq, h_ad]
      exact hg8 a
    rcases run with ⟨accessCost, _, run⟩
    rcases run with ⟨createCost, _, run⟩
    rcases run with ⟨transferCost, _, run⟩
    rcases run with ⟨⟨mcc, mcs⟩, _, run⟩
    rcases run with ⟨er, he, h_out, _⟩ | ⟨d10, e10, run⟩
    · rw [h_out]; exact herr hg9 (chargeGas_getBal_err he)
    have hg10 : ∀ a, d10.getBal a = pre.getBal a :=
      fun a => (chargeGas_getBal_eq e10 a).trans (hg9 a)
    rcases run with ⟨er, he, h_out, _⟩ | ⟨_, _, run⟩
    · rw [h_out]; exact herr hg10 (assert_getBal_err he)
    rcases run with ⟨d11, h_d11, run⟩
    have hg11 : ∀ a, d11.getBal a = pre.getBal a := by
      intro a; rw [h_d11]; exact hg10 a
    rcases run with ⟨senderBal, _, run⟩
    split_ifs at run with h_lt
    · rcases run with ⟨er, he, h_out, _⟩ | ⟨d12, e12, run⟩
      · rw [h_out]; exact herr hg11 (Devm.push_getBal_err he)
      rcases run with ⟨_, h_ex⟩
      rw [← h_ex]
      simp only [Execution.Rel, Outcome.Rel, id]
      apply Devm.balNoninc_of_getBal_eq
      funext a
      exact (Devm.push_getBal_eq e12 a).trans (hg11 a)
    · exact hok hg11 (GenericCall.balance_effect hxl run)
  case callcode =>
    dsimp only [Xinst.Run] at run
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨gas, d1⟩, e1, run⟩
    · rw [h_out]; exact herr (fun _ => rfl) (Devm.pop_getBal_err he)
    have hg1 : ∀ a, d1.getBal a = pre.getBal a := Devm.pop_getBal_eq e1
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨codeAddress, d2⟩, e2, run⟩
    · rw [h_out]; exact herr hg1 (Devm.popToAdr_getBal_err he)
    have hg2 : ∀ a, d2.getBal a = pre.getBal a :=
      fun a => (Devm.popToAdr_getBal_eq e2 a).trans (hg1 a)
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨value, d3⟩, e3, run⟩
    · rw [h_out]; exact herr hg2 (Devm.pop_getBal_err he)
    have hg3 : ∀ a, d3.getBal a = pre.getBal a :=
      fun a => (Devm.pop_getBal_eq e3 a).trans (hg2 a)
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨ii, d4⟩, e4, run⟩
    · rw [h_out]; exact herr hg3 (Devm.popToNat_getBal_err he)
    have hg4 : ∀ a, d4.getBal a = pre.getBal a :=
      fun a => (Devm.popToNat_getBal_eq e4 a).trans (hg3 a)
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨is, d5⟩, e5, run⟩
    · rw [h_out]; exact herr hg4 (Devm.popToNat_getBal_err he)
    have hg5 : ∀ a, d5.getBal a = pre.getBal a :=
      fun a => (Devm.popToNat_getBal_eq e5 a).trans (hg4 a)
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨oi, d6⟩, e6, run⟩
    · rw [h_out]; exact herr hg5 (Devm.popToNat_getBal_err he)
    have hg6 : ∀ a, d6.getBal a = pre.getBal a :=
      fun a => (Devm.popToNat_getBal_eq e6 a).trans (hg5 a)
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨os, d7⟩, e7, run⟩
    · rw [h_out]; exact herr hg6 (Devm.popToNat_getBal_err he)
    have hg7 : ∀ a, d7.getBal a = pre.getBal a :=
      fun a => (Devm.popToNat_getBal_eq e7 a).trans (hg6 a)
    rcases run with ⟨extendCost, _, run⟩
    rcases run with ⟨preAccessCost, _, run⟩
    rcases run with ⟨d8, h_d8, run⟩
    have hg8 : ∀ a, d8.getBal a = pre.getBal a := by
      intro a; rw [h_d8]; exact hg7 a
    rcases run with ⟨⟨dp, na, code0, dagc, d9⟩, h_d9, run⟩
    have hg9 : ∀ a, d9.getBal a = pre.getBal a := by
      intro a
      have hq := congrArg (fun q => (q.2.2.2.2 : Devm).getBal a) h_d9
      dsimp only at hq
      rw [hq, h_ad]
      exact hg8 a
    rcases run with ⟨accessCost, _, run⟩
    rcases run with ⟨transferCost, _, run⟩
    rcases run with ⟨⟨mcc, mcs⟩, _, run⟩
    rcases run with ⟨er, he, h_out, _⟩ | ⟨d10, e10, run⟩
    · rw [h_out]; exact herr hg9 (chargeGas_getBal_err he)
    have hg10 : ∀ a, d10.getBal a = pre.getBal a :=
      fun a => (chargeGas_getBal_eq e10 a).trans (hg9 a)
    rcases run with ⟨d11, h_d11, run⟩
    have hg11 : ∀ a, d11.getBal a = pre.getBal a := by
      intro a; rw [h_d11]; exact hg10 a
    rcases run with ⟨senderBal, _, run⟩
    split_ifs at run with h_lt
    · rcases run with ⟨er, he, h_out, _⟩ | ⟨d12, e12, run⟩
      · rw [h_out]; exact herr hg11 (Devm.push_getBal_err he)
      rcases run with ⟨_, h_ex⟩
      rw [← h_ex]
      simp only [Execution.Rel, Outcome.Rel, id]
      apply Devm.balNoninc_of_getBal_eq
      funext a
      exact (Devm.push_getBal_eq e12 a).trans (hg11 a)
    · exact hok hg11 (GenericCall.balance_effect hxl run)
  case delcall =>
    dsimp only [Xinst.Run] at run
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨gas, d1⟩, e1, run⟩
    · rw [h_out]; exact herr (fun _ => rfl) (Devm.pop_getBal_err he)
    have hg1 : ∀ a, d1.getBal a = pre.getBal a := Devm.pop_getBal_eq e1
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨codeAddress, d2⟩, e2, run⟩
    · rw [h_out]; exact herr hg1 (Devm.popToAdr_getBal_err he)
    have hg2 : ∀ a, d2.getBal a = pre.getBal a :=
      fun a => (Devm.popToAdr_getBal_eq e2 a).trans (hg1 a)
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨ii, d3⟩, e3, run⟩
    · rw [h_out]; exact herr hg2 (Devm.popToNat_getBal_err he)
    have hg3 : ∀ a, d3.getBal a = pre.getBal a :=
      fun a => (Devm.popToNat_getBal_eq e3 a).trans (hg2 a)
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨is, d4⟩, e4, run⟩
    · rw [h_out]; exact herr hg3 (Devm.popToNat_getBal_err he)
    have hg4 : ∀ a, d4.getBal a = pre.getBal a :=
      fun a => (Devm.popToNat_getBal_eq e4 a).trans (hg3 a)
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨oi, d5⟩, e5, run⟩
    · rw [h_out]; exact herr hg4 (Devm.popToNat_getBal_err he)
    have hg5 : ∀ a, d5.getBal a = pre.getBal a :=
      fun a => (Devm.popToNat_getBal_eq e5 a).trans (hg4 a)
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨os, d6⟩, e6, run⟩
    · rw [h_out]; exact herr hg5 (Devm.popToNat_getBal_err he)
    have hg6 : ∀ a, d6.getBal a = pre.getBal a :=
      fun a => (Devm.popToNat_getBal_eq e6 a).trans (hg5 a)
    rcases run with ⟨extendCost, _, run⟩
    rcases run with ⟨preAccessCost, _, run⟩
    rcases run with ⟨d7, h_d7, run⟩
    have hg7 : ∀ a, d7.getBal a = pre.getBal a := by
      intro a; rw [h_d7]; exact hg6 a
    rcases run with ⟨⟨dp, na, code0, dagc, d8⟩, h_d8, run⟩
    have hg8 : ∀ a, d8.getBal a = pre.getBal a := by
      intro a
      have hq := congrArg (fun q => (q.2.2.2.2 : Devm).getBal a) h_d8
      dsimp only at hq
      rw [hq, h_ad]
      exact hg7 a
    rcases run with ⟨accessCost, _, run⟩
    rcases run with ⟨⟨mcc, mcs⟩, _, run⟩
    rcases run with ⟨er, he, h_out, _⟩ | ⟨d9, e9, run⟩
    · rw [h_out]; exact herr hg8 (chargeGas_getBal_err he)
    have hg9 : ∀ a, d9.getBal a = pre.getBal a :=
      fun a => (chargeGas_getBal_eq e9 a).trans (hg8 a)
    rcases run with ⟨d10, h_d10, run⟩
    have hg10 : ∀ a, d10.getBal a = pre.getBal a := by
      intro a; rw [h_d10]; exact hg9 a
    exact hok hg10 (GenericCall.balance_effect hxl run)
  case statcall =>
    dsimp only [Xinst.Run] at run
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨gas, d1⟩, e1, run⟩
    · rw [h_out]; exact herr (fun _ => rfl) (Devm.pop_getBal_err he)
    have hg1 : ∀ a, d1.getBal a = pre.getBal a := Devm.pop_getBal_eq e1
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨target, d2⟩, e2, run⟩
    · rw [h_out]; exact herr hg1 (Devm.popToAdr_getBal_err he)
    have hg2 : ∀ a, d2.getBal a = pre.getBal a :=
      fun a => (Devm.popToAdr_getBal_eq e2 a).trans (hg1 a)
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨ii, d3⟩, e3, run⟩
    · rw [h_out]; exact herr hg2 (Devm.popToNat_getBal_err he)
    have hg3 : ∀ a, d3.getBal a = pre.getBal a :=
      fun a => (Devm.popToNat_getBal_eq e3 a).trans (hg2 a)
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨is, d4⟩, e4, run⟩
    · rw [h_out]; exact herr hg3 (Devm.popToNat_getBal_err he)
    have hg4 : ∀ a, d4.getBal a = pre.getBal a :=
      fun a => (Devm.popToNat_getBal_eq e4 a).trans (hg3 a)
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨oi, d5⟩, e5, run⟩
    · rw [h_out]; exact herr hg4 (Devm.popToNat_getBal_err he)
    have hg5 : ∀ a, d5.getBal a = pre.getBal a :=
      fun a => (Devm.popToNat_getBal_eq e5 a).trans (hg4 a)
    rcases run with ⟨er, he, h_out, _⟩ | ⟨⟨os, d6⟩, e6, run⟩
    · rw [h_out]; exact herr hg5 (Devm.popToNat_getBal_err he)
    have hg6 : ∀ a, d6.getBal a = pre.getBal a :=
      fun a => (Devm.popToNat_getBal_eq e6 a).trans (hg5 a)
    rcases run with ⟨extendCost, _, run⟩
    rcases run with ⟨preAccessCost, _, run⟩
    rcases run with ⟨d7, h_d7, run⟩
    have hg7 : ∀ a, d7.getBal a = pre.getBal a := by
      intro a; rw [h_d7]; exact hg6 a
    rcases run with ⟨⟨dp, na, code0, dagc, d8⟩, h_d8, run⟩
    have hg8 : ∀ a, d8.getBal a = pre.getBal a := by
      intro a
      have hq := congrArg (fun q => (q.2.2.2.2 : Devm).getBal a) h_d8
      dsimp only at hq
      rw [hq, h_ad]
      exact hg7 a
    rcases run with ⟨accessCost, _, run⟩
    rcases run with ⟨⟨mcc, mcs⟩, _, run⟩
    rcases run with ⟨er, he, h_out, _⟩ | ⟨d9, e9, run⟩
    · rw [h_out]; exact herr hg8 (chargeGas_getBal_err he)
    have hg9 : ∀ a, d9.getBal a = pre.getBal a :=
      fun a => (chargeGas_getBal_eq e9 a).trans (hg8 a)
    rcases run with ⟨d10, h_d10, run⟩
    have hg10 : ∀ a, d10.getBal a = pre.getBal a := by
      intro a; rw [h_d10]; exact hg9 a
    exact hok hg10 (GenericCall.balance_effect hxl run)

lemma Ninst.balance_effectGen (n : Ninst) :
    Ninst.EffectGen Devm.BalNoninc n := by
  cases n
  case reg r =>
    apply Ninst.effectGen_reg
    apply Rinst.balance_effect
  case exec x =>
    apply Ninst.effectGen_exec
    apply Xinst.balance_effectGen
  case push xs hxs =>
    apply Ninst.push_balance_effectGen

theorem Exec.balance_effect {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) :
    Execution.Rel Devm.BalNoninc pre out :=
  Exec.effect balNoninc_refl_trans.2.1 balNoninc_refl_trans.2.2 Ninst.balance_effectGen Jinst.balance_effect Linst.balance_effect run

lemma Ninst.balance_effect (n : Ninst) : Ninst.Effect Devm.BalNoninc n := by
  apply Ninst.effect_of_effectGen balNoninc_refl_trans.2.1 balNoninc_refl_trans.2.2
  · exact Ninst.balance_effectGen
  · exact Jinst.balance_effect
  · exact Linst.balance_effect

theorem Func.balance_effect {fs : List Func} {sevm : Sevm}
    {pre post : Devm} {p : Func}
    (run : Func.Run fs sevm pre p post) : Devm.BalNoninc pre post := by
  apply Func.effect (R := Devm.BalNoninc) (htrans := balNoninc_refl_trans.2.2) _ _ Ninst.balance_effect Linst.balance_effect run
  · intro xs pr po hpop
    apply Devm.balNoninc_of_state
    rw [hpop.state]
    exact balNoninc_refl_trans.1.1 _
  · intro pr po hburn
    apply Devm.balNoninc_of_state
    rw [hburn.state]
    exact balNoninc_refl_trans.1.1 _

/-! ## 6. Executable wrappers and the Solvent.lean endpoint -/

lemma Fueled.eq_ok_of_toExcept_eq_ok {ε α : Type} {x : Fueled ε α}
    {default : ε} {a : α} (h : x.toExcept default = .ok a) :
    x = Fueled.ok a := by
  apply Fueled.ext
  unfold Fueled.toExcept at h
  rcases hx : x.run with _ | ex
  · rw [hx] at h
    cases h
  · rw [hx] at h
    change ex = .ok a at h
    change some ex = some (.ok a)
    exact congrArg some h

lemma Xlot.balance_rel_of_good {lim : Nat} {xl : Xlot}
    (hgood : xl.Good lim) :
    Xlot.Rel Devm.BalNoninc xl := by
  rcases xl with _ | ⟨sevm, devm, exn⟩
  · constructor
  · rcases hgood with ⟨lim', _, exec_eq⟩
    rcases of_exec lim' 0 sevm devm exn exec_eq with ⟨exc⟩
    exact Exec.balance_effect exc

lemma processMessage_balance_noninc {msg : Msg} {lim : Nat} {post : Devm}
    (h : processMessage msg lim = Fueled.ok post) :
    State.BalNoninc msg.benv.state post.state := by
  obtain ⟨xl, hgood, hrun⟩ := of_processMessage msg lim (.ok post) h
  have heff := ProcessMessage.balance_effect (Xlot.balance_rel_of_good hgood) hrun
  change State.BalNoninc msg.benv.state post.state at heff
  exact heff

lemma processCreateMessage_balance_noninc
    {msg : Msg} {lim : Nat} {post : Devm}
    (h : processCreateMessage msg lim = Fueled.ok post) :
    State.BalNoninc msg.benv.state post.state := by
  rcases of_processCreateMessage msg lim (.ok post) h with ⟨xl, hgood, hrun⟩
  have hxl : Xlot.Rel Devm.BalNoninc xl := Xlot.balance_rel_of_good hgood
  have heff := ProcessCreateMessage.balance_effect hxl hrun
  exact heff

lemma setDelegationStep_bal_eq {auth : Auth} {msg msg' : Msg} {rc rc' : B256}
    (h : setDelegationStep auth msg rc = .ok ⟨msg', rc'⟩) :
    msg'.benv.state.bal = msg.benv.state.bal := by
  unfold setDelegationStep at h
  dsimp only at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩; rfl
  · split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩; rfl
    · split at h
      · split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, _⟩; rfl
        · cases h
      · split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, _⟩; rfl
        · split at h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩; rfl
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩
            show ((msg.benv.state.setCode _ _).incrNonce _).bal =
              msg.benv.state.bal
            rw [State.incrNonce_bal, State.setCode_bal]

lemma setDelegationLoop_bal_eq {auths : List Auth} {msg msg' : Msg}
    {rc rc' : B256}
    (h : setDelegationLoop auths msg rc = .ok ⟨msg', rc'⟩) :
    msg'.benv.state.bal = msg.benv.state.bal := by
  induction auths generalizing msg rc with
  | nil =>
    unfold setDelegationLoop at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩; rfl
  | cons auth auths ih =>
    unfold setDelegationLoop at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i p h_step
      obtain ⟨msgS, rcS⟩ := p
      exact (ih h).trans (setDelegationStep_bal_eq h_step)

lemma setDelegation_balSum_eq {msg msg' : Msg} {refund : B256}
    (h : setDelegation msg = .ok ⟨msg', refund⟩) :
    State.balSum msg'.benv.state = State.balSum msg.benv.state := by
  unfold setDelegation at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p h_loop
    obtain ⟨msgL, rcL⟩ := p
    have h_bal := setDelegationLoop_bal_eq h_loop
    split at h
    · cases h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩
      unfold State.balSum
      rw [show ({ msgL with
        code := msgL.benv.state.getCode _ } : Msg).benv.state.bal =
          msgL.benv.state.bal from rfl, h_bal]

lemma processMessageCall.call_balance_noninc
    {msg : Msg} {post : _root_.State} {out : MsgCallOutput}
    (h : processMessageCall.call msg = .ok ⟨post, out⟩) :
    State.BalNoninc msg.benv.state post := by
  unfold processMessageCall.call at h
  dsimp only at h
  split at h
  · simp only [bind, Except.bind] at h
    unfold Except.bimap at h
    split at h
    · injection h
    · rename_i evm h_evm
      split at h_evm
      · injection h_evm
      · rename_i evm' h_pm
        simp only [id_eq, Except.ok.injEq] at h_evm
        subst h_evm
        have hbal := processMessage_balance_noninc
          (Fueled.eq_ok_of_toExcept_eq_ok h_pm)
        have hpre : State.BalNoninc msg.benv.state evm'.state := by
          split at hbal <;> exact hbal
        split at h
        · split at h
          · injection h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩
            exact hpre
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, _⟩
          exact hpre
  · rcases h_del : setDelegation msg with ⟨err⟩ | ⟨⟨msgD, val⟩⟩
    · simp only [h_del, bind, Except.bind] at h
      injection h
    · simp only [h_del, bind, Except.bind] at h
      have h_sum := setDelegation_balSum_eq h_del
      unfold Except.bimap at h
      split at h
      · injection h
      · rename_i evm h_evm
        split at h_evm
        · injection h_evm
        · rename_i evm' h_pm
          simp only [id_eq, Except.ok.injEq] at h_evm
          subst h_evm
          have hbal := processMessage_balance_noninc
            (Fueled.eq_ok_of_toExcept_eq_ok h_pm)
          have hpre : State.BalNoninc msg.benv.state evm'.state := by
            have hD : State.BalNoninc msgD.benv.state evm'.state := by
              split at hbal <;> exact hbal
            unfold State.BalNoninc at *
            omega
          split at h
          · split at h
            · injection h
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, _⟩
              exact hpre
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩
            exact hpre

lemma processMessageCall.create_balance_noninc
    {msg : Msg} {post : _root_.State} {out : MsgCallOutput}
    (h : processMessageCall.create msg = .ok ⟨post, out⟩) :
    State.BalNoninc msg.benv.state post := by
  unfold processMessageCall.create at h
  dsimp only at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩
    exact le_refl _
  · simp only [bind, Except.bind] at h
    unfold Except.bimap at h
    split at h
    · injection h
    · rename_i evm h_evm
      split at h_evm
      · injection h_evm
      · rename_i evm' h_pm
        simp only [id_eq, Except.ok.injEq] at h_evm
        subst h_evm
        have hbal := processCreateMessage_balance_noninc
          (Fueled.eq_ok_of_toExcept_eq_ok h_pm)
        split at h
        · split at h
          · injection h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩
            exact hbal
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, _⟩
          exact hbal

lemma processMessageCall_balance_noninc
    {msg : Msg} {post : _root_.State} {out : MsgCallOutput}
    (h : processMessageCall msg = .ok ⟨post, out⟩) :
    State.BalNoninc msg.benv.state post := by
  unfold processMessageCall at h
  split at h
  · exact processMessageCall.create_balance_noninc h
  · exact processMessageCall.call_balance_noninc h

lemma processMessageCall_sum_le
    {msg : Msg} {post : _root_.State} {out : MsgCallOutput}
    (h : processMessageCall msg = .ok ⟨post, out⟩) :
    sum post.bal ≤ sum msg.benv.state.bal := by
  exact processMessageCall_balance_noninc h

lemma processMessageCall_preserves_sumNof
    {msg : Msg} {post : _root_.State} {out : MsgCallOutput}
    (h : processMessageCall msg = .ok ⟨post, out⟩)
    (hnof : State.SumNof msg.benv.state) : State.SumNof post := by
  exact State.SumNof.of_noninc (processMessageCall_balance_noninc h) hnof
