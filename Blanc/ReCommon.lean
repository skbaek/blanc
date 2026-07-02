-- Common.lean : definitions and lemmas generally useful for writing and
-- verifying Blanc programs, including a correctness proof for the Blanc
-- compiler and tactics for automating Blanc program verification.

import Mathlib.Tactic.Have
import Mathlib.Tactic.Clear_
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

lemma Devm.burn_trans {x y z} (h1 : Devm.Burn x y) (h2 : Devm.Burn y z) : Devm.Burn x z := by
  rcases h1 with ⟨h1_stack, h1_mem, h1_gas, h1_logs, h1_refund, h1_out, h1_del, h1_ret, h1_err, h1_acc, h1_keys, h1_state, h1_trans⟩
  rcases h2 with ⟨h2_stack, h2_mem, h2_gas, h2_logs, h2_refund, h2_out, h2_del, h2_ret, h2_err, h2_acc, h2_keys, h2_state, h2_trans⟩
  refine' ⟨Eq.trans h1_stack h2_stack, Eq.trans h1_mem h2_mem, Nat.le_trans h2_gas h1_gas, Eq.trans h1_logs h2_logs, Eq.trans h1_refund h2_refund, Eq.trans h1_out h2_out, Eq.trans h1_del h2_del, Eq.trans h1_ret h2_ret, Eq.trans h1_err h2_err, Eq.trans h1_acc h2_acc, Eq.trans h1_keys h2_keys, Eq.trans h1_state h2_state, Eq.trans h1_trans h2_trans⟩

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
        | _ => dbg_trace "not matching next or last"
    | _ => dbg_trace "not a Func.Inv goal"

elab "prog_inv" : tactic => prog_inv

end

lemma of_run_branch {c e s r} {p q : Func} (h : Func.Run c e s (Func.branch p q) r) :
    (∃ s', Devm.PopBurn [0] s s' ∧ Func.Run c e s' p r) ∨
    (∃ w s' s'', w ≠ 0 ∧ Devm.PopBurn [w] s s' ∧ Devm.Burn s' s'' ∧ Func.Run c e s'' q r) := by
  cases h with
  | zero h1 h2 => left; exact ⟨_, h1, h2⟩
  | succ h1 h2 h3 h4 => right; exact ⟨_, _, _, h1, h2, h3, h4⟩

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
      split_ifs <;> try rfl
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

lemma Devm.pop_getCode {devm devm' : Devm} {val : B256} {a : Adr} (h : devm.pop = Except.ok (val, devm')) : devm'.getCode a = devm.getCode a := by
  dsimp [Devm.pop] at h
  split at h
  · contradiction
  · simp at h; rcases h with ⟨_, rfl⟩; rfl

lemma Devm.popToAdr_getCode {devm devm' : Devm} {val : Adr} {a : Adr} (h : devm.popToAdr = Except.ok (val, devm')) : devm'.getCode a = devm.getCode a := by
  dsimp [Devm.popToAdr, Except.map, Prod.mapFst] at h
  cases h_pop : devm.pop
  · simp [h_pop, Except.bind] at h
  · rename_i val_pop
    simp [h_pop, Except.bind] at h
    rcases val_pop with ⟨v, devm''⟩
    simp at h
    rcases h with ⟨_, rfl⟩
    exact Devm.pop_getCode h_pop

lemma Devm.popToNat_getCode {devm devm' : Devm} {val : ℕ} {a : Adr} (h : devm.popToNat = Except.ok (val, devm')) : devm'.getCode a = devm.getCode a := by
  dsimp [Devm.popToNat, Except.map, Prod.mapFst] at h
  cases h_pop : devm.pop
  · simp [h_pop, Except.bind] at h
  · rename_i val_pop
    simp [h_pop, Except.bind] at h
    rcases val_pop with ⟨v, devm''⟩
    simp at h
    rcases h with ⟨_, rfl⟩
    exact Devm.pop_getCode h_pop

lemma addAccessedAddress_getCode {devm : Devm} {adr a : Adr} : (addAccessedAddress devm adr).getCode a = devm.getCode a := rfl

lemma accessDelegation_getCode {devm : Devm} {adr a : Adr} : (accessDelegation devm adr).2.2.2.2.getCode a = devm.getCode a := by
  dsimp [accessDelegation]
  split_ifs
  · exact addAccessedAddress_getCode
  · rfl

lemma chargeGas_getCode {devm devm' : Devm} {cost : ℕ} {a : Adr} (h : chargeGas cost devm = Except.ok devm') : devm'.getCode a = devm.getCode a := by
  dsimp [chargeGas] at h
  cases h_sub : safeSub devm.gasLeft cost
  · simp [h_sub, Except.bind] at h
  · simp [h_sub, Except.bind] at h; subst h; rfl

lemma Devm.memExtends_getCode {devm : Devm} {ranges : List (ℕ × ℕ)} {a : Adr} : (devm.memExtends ranges).getCode a = devm.getCode a := rfl

lemma Devm.incrNonce_getCode {devm : Devm} {adr a : Adr} : (devm.incrNonce adr).getCode a = devm.getCode a := by
  dsimp [Devm.incrNonce, Devm.getCode, Devm.getAcct, State.incrNonce, State.set, State.getCode, State.get]
  split_ifs with h_if
  · by_cases h : compare adr a = Ordering.eq
    · have h2 : adr = a := compare_eq_iff_eq.mp h
      subst h2
      rw [Std.TreeMap.getD_erase]
      split_ifs <;> try rfl
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
      split_ifs <;> try rfl
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
      split_ifs <;> try rfl
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
          dsimp [Msg.benvAfterTransfer] at eq_benv
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
        dsimp [Msg.withBenv] at run
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
          dsimp [Msg.benvAfterTransfer] at eq_benv
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
        dsimp [Msg.withBenv] at run
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
        dsimp [Msg.benvAfterTransfer] at eq_benv
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
      dsimp [Msg.withBenv] at run
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
        dsimp [Msg.benvAfterTransfer] at eq_benv
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
      dsimp [Msg.withBenv] at run
      split_ifs at run with h_precomp
      · rcases run with ⟨h_xl, _⟩; cases h_xl
      · rcases run with ⟨ex''', h_xl, _⟩
        injection h_xl with h_xl_eq
        injection h_xl_eq with _ h_devm_eq
        injection h_devm_eq with h_devm_eq _
        subst h_devm_eq
        exact h_devm

lemma Ninst.prep_inv_getCode
    {pc sevm devm n sevm_ devm_ exn_ res}
    (run : Ninst.Run' pc sevm devm n (.some ⟨sevm_, devm_, exn_⟩) res) (a : Adr)
    : devm_.getCode a = devm.getCode a := by
  cases n
  case push xs _ => revert run; dsimp [Ninst.Run']; exact fun h => h.elim
  case reg r => revert run; dsimp [Ninst.Run']; exact fun h => h.elim
  case exec x => revert run; dsimp [Ninst.Run']; apply Xinst.prep_inv_getCode

lemma Xinst.prep_inv_code
    {sevm : Sevm} {devm : Devm} {sevm_ : Sevm} {devm_ : Devm}
    {exn_ res : Execution} {x : Xinst}
    (ne : sevm.currentTarget ≠ sevm_.currentTarget)
    (notEmpty : devm.getCode sevm_.currentTarget ≠ .empty)
    (notDel : ¬ isValidDelegation (devm.getCode sevm_.currentTarget))
    (run : Xinst.Run sevm devm x (some (sevm_, devm_, exn_)) res) :
    sevm_.code = devm.getCode sevm_.currentTarget := by
  cases x
  case create =>
    exfalso
    apply notEmpty
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
        dsimp [Msg.withBenv] at run
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
    exfalso
    apply ne
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
        dsimp [Msg.withBenv] at run
        split_ifs at run with h_precomp
        · rcases run with ⟨h_xl, _⟩; cases h_xl
        · rcases run with ⟨ex''', h_xl, _⟩
          injection h_xl with h_xl_eq
          injection h_xl_eq with h_sevm_eq _
          subst h_sevm_eq
          rfl
  case delcall =>
    exfalso
    apply ne
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
      dsimp [Msg.withBenv] at run
      split_ifs at run with h_precomp
      · rcases run with ⟨h_xl, _⟩; cases h_xl
      · rcases run with ⟨ex''', h_xl, _⟩
        injection h_xl with h_xl_eq
        injection h_xl_eq with h_sevm_eq _
        subst h_sevm_eq
        rfl
  case create2 =>
    exfalso
    apply notEmpty
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
      dsimp [Msg.withBenv] at run
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
  simp only [Devm.pop] at h
  split at h <;> try contradiction
  cases h; rfl

lemma chargeGas_getCode_eq {cost devm devm'} (h : chargeGas cost devm = .ok devm') (a : Adr) : devm'.getCode a = devm.getCode a := by
  simp only [chargeGas] at h
  split at h <;> try contradiction
  cases h; rfl

lemma Devm.push_getCode_eq {v devm devm'} (h : Devm.push v devm = .ok devm') (a : Adr) : devm'.getCode a = devm.getCode a := by
  simp only [Devm.push, bind, Except.bind, Except.assert] at h
  split at h <;> try contradiction
  cases h; rfl

lemma Devm.popToNat_getCode_eq {devm devm' n} (h : Devm.popToNat devm = .ok ⟨n, devm'⟩) (a : Adr) : devm'.getCode a = devm.getCode a := by
  dsimp [Devm.popToNat, Functor.map, Except.map] at h
  rcases hp : devm.pop with _ | ⟨x, devm1⟩
  · simp [hp] at h
  · simp [hp] at h
    rcases h with ⟨_, rfl⟩
    exact Devm.pop_getCode_eq hp a

lemma Devm.popToAdr_getCode_eq {devm devm' adr} (h : Devm.popToAdr devm = .ok ⟨adr, devm'⟩) (a : Adr) : devm'.getCode a = devm.getCode a := by
  dsimp [Devm.popToAdr, Functor.map, Except.map] at h
  rcases hp : devm.pop with _ | ⟨x, devm1⟩
  · simp [hp] at h
  · simp [hp] at h
    rcases h with ⟨_, rfl⟩
    exact Devm.pop_getCode_eq hp a

lemma Devm.pop_map_snd_getCode_eq {devm devm1 : Devm} (hp : (devm.pop <&> Prod.snd) = .ok devm1) (a : Adr) : devm1.getCode a = devm.getCode a := by
  dsimp [(· <&> ·), Functor.mapRev, Functor.map, Except.map] at hp
  rcases hp2 : devm.pop with _ | ⟨x, devm2⟩
  · simp [hp2] at hp
  · simp [hp2] at hp
    rcases hp with ⟨_, rfl⟩
    exact Devm.pop_getCode_eq hp2 a

lemma Devm.pop_map_snd_getCode_err {devm : Devm} {err : String × Devm} (hp : (devm.pop <&> Prod.snd) = .error err) (a : Adr) : err.2.getCode a = devm.getCode a := by
  dsimp [(· <&> ·), Functor.mapRev, Functor.map, Except.map] at hp
  rcases hp2 : devm.pop with e | ⟨x, devm2⟩
  · simp [hp2] at hp; cases hp
    simp only [Devm.pop] at hp2
    split at hp2 <;> try contradiction
    cases hp2; rfl
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
  simp only [pushItem] at h
  refine getCode_eq_of_bind h id ?_ ?_
  {intro devm1 hc; exact chargeGas_getCode_eq hc a}
  intro devm1 hc run; exact Devm.push_getCode_eq run a

lemma applyUnary_getCode_eq {f : B256 → B256} {cost devm devm'}
    (h : applyUnary f cost devm = .ok devm') (a : Adr) :
    devm'.getCode a = devm.getCode a := by
  simp only [applyUnary] at h
  refine getCode_eq_of_bind h Prod.snd ?_ ?_
  {intro ⟨x, devm1⟩ hp; exact Devm.pop_getCode_eq hp a}
  intro ⟨x, devm1⟩ hp run; exact pushItem_getCode_eq run a

lemma applyBinary_getCode_eq {f : B256 → B256 → B256} {cost devm devm'}
    (h : applyBinary f cost devm = .ok devm') (a : Adr) :
    devm'.getCode a = devm.getCode a := by
  simp only [applyBinary] at h
  refine getCode_eq_of_bind h Prod.snd ?_ ?_
  {intro ⟨x, devm1⟩ hp; exact Devm.pop_getCode_eq hp a}
  intro ⟨x, devm1⟩ hp run; refine getCode_eq_of_bind run Prod.snd ?_ ?_
  {intro ⟨y, devm2⟩ hp2; exact Devm.pop_getCode_eq hp2 a}
  intro ⟨y, devm2⟩ hp2 run; exact pushItem_getCode_eq run a

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
  simp only [Devm.pop] at h
  split at h <;> try contradiction
  cases h; rfl

lemma chargeGas_getBal_eq {cost devm devm'} (h : chargeGas cost devm = .ok devm') (a : Adr) : devm'.getBal a = devm.getBal a := by
  simp only [chargeGas] at h
  split at h <;> try contradiction
  cases h; rfl

lemma Devm.push_getBal_eq {v devm devm'} (h : Devm.push v devm = .ok devm') (a : Adr) : devm'.getBal a = devm.getBal a := by
  simp only [Devm.push, bind, Except.bind, Except.assert] at h
  split at h <;> try contradiction
  cases h; rfl

lemma pushItem_getBal_eq {x c devm devm'} (h : pushItem x c devm = .ok devm') (a : Adr) : devm'.getBal a = devm.getBal a := by
  simp only [pushItem] at h
  refine getBal_eq_of_bind h id ?_ ?_
  {intro devm1 hc; exact chargeGas_getBal_eq hc a}
  intro devm1 hc run; exact Devm.push_getBal_eq run a

lemma applyBinary_getBal_eq {f : B256 → B256 → B256} {cost devm devm'}
    (h : applyBinary f cost devm = .ok devm') :
    devm.getBal = devm'.getBal := by
  simp only [applyBinary] at h
  apply funext; intro a; apply Eq.symm
  refine getBal_eq_of_bind h Prod.snd ?_ ?_
  {intro ⟨x, devm1⟩ hp; exact Devm.pop_getBal_eq hp a}
  intro ⟨x, devm1⟩ hp run; refine getBal_eq_of_bind run Prod.snd ?_ ?_
  {intro ⟨y, devm2⟩ hp2; exact Devm.pop_getBal_eq hp2 a}
  intro ⟨y, devm2⟩ hp2 run; exact pushItem_getBal_eq run a

lemma applyUnary_getBal_eq {f : B256 → B256} {cost devm devm'}
    (h : applyUnary f cost devm = .ok devm') :
    devm.getBal = devm'.getBal := by
  simp only [applyUnary] at h
  apply funext; intro a; apply Eq.symm
  refine getBal_eq_of_bind h Prod.snd ?_ ?_
  {intro ⟨x, devm1⟩ hp; exact Devm.pop_getBal_eq hp a}
  intro ⟨x, devm1⟩ hp run; exact pushItem_getBal_eq run a

lemma applyTernary_getBal_eq {f : B256 → B256 → B256 → B256} {cost devm devm'}
    (h : applyTernary f cost devm = .ok devm') :
    devm.getBal = devm'.getBal := by
  simp only [applyTernary] at h
  apply funext; intro a; apply Eq.symm
  refine getBal_eq_of_bind h Prod.snd ?_ ?_
  {intro ⟨x, devm1⟩ hp; exact Devm.pop_getBal_eq hp a}
  intro ⟨x, devm1⟩ hp run; refine getBal_eq_of_bind run Prod.snd ?_ ?_
  {intro ⟨y, devm2⟩ hp2; exact Devm.pop_getBal_eq hp2 a}
  intro ⟨y, devm2⟩ hp2 run; refine getBal_eq_of_bind run Prod.snd ?_ ?_
  {intro ⟨z, devm3⟩ hp3; exact Devm.pop_getBal_eq hp3 a}
  intro ⟨z, devm3⟩ hp3 run; exact pushItem_getBal_eq run a


lemma applyTernary_getCode_eq {f : B256 → B256 → B256 → B256} {cost devm devm'}
    (h : applyTernary f cost devm = .ok devm') (a : Adr) :
    devm'.getCode a = devm.getCode a := by
  simp only [applyTernary] at h
  refine getCode_eq_of_bind h Prod.snd ?_ ?_
  {intro ⟨x, devm1⟩ hp; exact Devm.pop_getCode_eq hp a}
  intro ⟨x, devm1⟩ hp run; refine getCode_eq_of_bind run Prod.snd ?_ ?_
  {intro ⟨y, devm2⟩ hp2; exact Devm.pop_getCode_eq hp2 a}
  intro ⟨y, devm2⟩ hp2 run; refine getCode_eq_of_bind run Prod.snd ?_ ?_
  {intro ⟨z, devm3⟩ hp3; exact Devm.pop_getCode_eq hp3 a}
  intro ⟨z, devm3⟩ hp3 run; exact pushItem_getCode_eq run a

lemma getCode_eq_of_SplitXl {ξ α : Type} {e : Except ξ (α × Devm)} {xl : Xlot} {q} {devm devm' : Devm} {a : Adr}
    (h : e.SplitXl xl (.ok devm') q)
    (h_getCode : ∀ y : α × Devm, e = .ok y → y.snd.getCode a = devm.getCode a)
    (h_q : ∀ y : α × Devm, q y → devm'.getCode a = y.snd.getCode a) :
    devm'.getCode a = devm.getCode a := by
  rcases h with ⟨x, h_err, h_contra, _⟩ | ⟨y, h_eq, h_q_y⟩
  · contradiction
  · exact Eq.trans (h_q y h_q_y) (h_getCode y h_eq)

lemma getCode_eq_of_SplitXl_id {ξ : Type} {e : Except ξ Devm} {xl : Xlot} {q} {devm devm' : Devm} {a : Adr}
    (h : e.SplitXl xl (.ok devm') q)
    (h_getCode : ∀ y : Devm, e = .ok y → y.getCode a = devm.getCode a)
    (h_q : ∀ y : Devm, q y → devm'.getCode a = y.getCode a) :
    devm'.getCode a = devm.getCode a := by
  rcases h with ⟨x, h_err, h_contra, _⟩ | ⟨y, h_eq, h_q_y⟩
  · contradiction
  · exact Eq.trans (h_q y h_q_y) (h_getCode y h_eq)

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
    · simp [addAccessedStorageKey, Devm.withAccessedStorageKeys]
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
  induction n generalizing devm devm' l with
  | zero =>
    simp [Devm.popN] at hp
    rcases hp with ⟨_, eq⟩
    rw [eq]
  | succ n ih =>
    simp [Devm.popN] at hp
    rcases of_bind_eq_ok hp with ⟨⟨x, devm1⟩, hp1, hp2⟩
    rcases of_bind_eq_ok hp2 with ⟨⟨xs, devm2⟩, hp3, hp4⟩
    injection hp4 with eq
    injection eq with eq1 eq2
    subst eq2
    have h1 := Devm.pop_getCode_eq hp1 a
    have h2 := ih hp3
    rw [h2, h1]



lemma Rinst.inv_getCode
    {pc sevm devm r devm'}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = .ok devm') (a : Adr)
    (ne : (devm.getCode a).toList ≠ []) :
    devm'.getCode a = devm.getCode a := by
  cases r <;> dsimp [Rinst.run, Rinst.runCore] at run
  case add => apply applyBinary_getCode_eq run
  case mul => apply applyBinary_getCode_eq run
  case sub => apply applyBinary_getCode_eq run
  case div => apply applyBinary_getCode_eq run
  case sdiv => apply applyBinary_getCode_eq run
  case mod => apply applyBinary_getCode_eq run
  case smod => apply applyBinary_getCode_eq run
  case addmod => apply applyTernary_getCode_eq run
  case mulmod => apply applyTernary_getCode_eq run
  case exp =>
    refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.pop_getCode_eq hp a}
    intro ⟨x, devm1⟩ hp run; refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨y, devm2⟩ hp2; exact Devm.pop_getCode_eq hp2 a}
    intro ⟨y, devm2⟩ hp2 run; exact pushItem_getCode_eq run a
  case signextend => apply applyBinary_getCode_eq run
  case lt => apply applyBinary_getCode_eq run
  case gt => apply applyBinary_getCode_eq run
  case slt => apply applyBinary_getCode_eq run
  case sgt => apply applyBinary_getCode_eq run
  case eq => apply applyBinary_getCode_eq run
  case iszero => apply applyUnary_getCode_eq run
  case and => apply applyBinary_getCode_eq run
  case or => apply applyBinary_getCode_eq run
  case xor => apply applyBinary_getCode_eq run
  case not => apply applyUnary_getCode_eq run
  case byte => apply applyBinary_getCode_eq run
  case shr => apply applyBinary_getCode_eq run
  case shl => apply applyBinary_getCode_eq run
  case sar => apply applyBinary_getCode_eq run
  case kec =>
    refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.popToNat_getCode_eq hp a}
    intro ⟨x, devm1⟩ hp run; refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨y, devm2⟩ hp2; exact Devm.popToNat_getCode_eq hp2 a}
    intro ⟨y, devm2⟩ hp2 run;
    refine getCode_eq_of_bind run id ?_ ?_
    {intro devm1 hc; exact chargeGas_getCode_eq hc a}
    intro devm1 hc run; exact Devm.push_getCode_eq run a
  case address => apply pushItem_getCode_eq run
  case balance =>
    refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.pop_getCode_eq hp a}
    intro ⟨x, devm1⟩ hp run; split at run
    · refine getCode_eq_of_bind run id ?_ ?_
      {intro devm2 hc; exact chargeGas_getCode_eq hc a}
      intro devm2 hc run; exact Devm.push_getCode_eq run a
    · refine getCode_eq_of_bind run id ?_ ?_
      {intro devm2 hc; exact chargeGas_getCode_eq hc a}
      intro devm2 hc run; exact Devm.push_getCode_eq run a
  case origin => apply pushItem_getCode_eq run
  case caller => apply pushItem_getCode_eq run
  case callvalue => apply pushItem_getCode_eq run
  case calldataload =>
    refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.pop_getCode_eq hp a}
    intro ⟨x, devm1⟩ hp run; refine getCode_eq_of_bind run id ?_ ?_
    {intro devm2 hc; exact chargeGas_getCode_eq hc a}
    intro devm2 hc run; exact Devm.push_getCode_eq run a
  case calldatasize => apply pushItem_getCode_eq run
  case calldatacopy =>
    refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.popToNat_getCode_eq hp a}
    intro ⟨x, devm1⟩ hp run; refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨y, devm2⟩ hp; exact Devm.popToNat_getCode_eq hp a}
    intro ⟨y, devm2⟩ hp run; refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨z, devm3⟩ hp; exact Devm.popToNat_getCode_eq hp a}
    intro ⟨z, devm3⟩ hp run; refine getCode_eq_of_bind run id ?_ ?_
    {intro devm4 hc; exact chargeGas_getCode_eq hc a}
    intro devm4 hc run; injection run with eq; subst eq; rfl
  case codesize => apply pushItem_getCode_eq run
  case codecopy =>
    refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.popToNat_getCode_eq hp a}
    intro ⟨x, devm1⟩ hp run; refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨y, devm2⟩ hp; exact Devm.popToNat_getCode_eq hp a}
    intro ⟨y, devm2⟩ hp run; refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨z, devm3⟩ hp; exact Devm.popToNat_getCode_eq hp a}
    intro ⟨z, devm3⟩ hp run; refine getCode_eq_of_bind run id ?_ ?_
    {intro devm4 hc; exact chargeGas_getCode_eq hc a}
    intro devm4 hc run; injection run with eq; subst eq; rfl
  case gasprice => apply pushItem_getCode_eq run
  case extcodesize =>
    refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.popToAdr_getCode_eq hp a}
    intro ⟨x, devm1⟩ hp run; split at run
    · refine getCode_eq_of_bind run id ?_ ?_
      {intro devm2 hc; exact chargeGas_getCode_eq hc a}
      intro devm2 hc run; exact Devm.push_getCode_eq run a
    · refine getCode_eq_of_bind run id ?_ ?_
      {intro devm2 hc; exact chargeGas_getCode_eq hc a}
      intro devm2 hc run; exact Devm.push_getCode_eq run a
  case extcodecopy =>
    refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.popToAdr_getCode_eq hp a}
    intro ⟨x, devm1⟩ hp run; refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨y, devm2⟩ hp; exact Devm.popToNat_getCode_eq hp a}
    intro ⟨y, devm2⟩ hp run; refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨z, devm3⟩ hp; exact Devm.popToNat_getCode_eq hp a}
    intro ⟨z, devm3⟩ hp run; refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨w, devm4⟩ hp; exact Devm.popToNat_getCode_eq hp a}
    intro ⟨w, devm4⟩ hp run; split at run
    · refine getCode_eq_of_bind run id ?_ ?_
      {intro devm5 hc; exact chargeGas_getCode_eq hc a}
      intro devm5 hc run; injection run with eq; subst eq; rfl
    · refine getCode_eq_of_bind run id ?_ ?_
      {intro devm5 hc; exact chargeGas_getCode_eq hc a}
      intro devm5 hc run; injection run with eq; subst eq; rfl
  case retdatasize => apply pushItem_getCode_eq run
  case retdatacopy =>
    refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.popToNat_getCode_eq hp a}
    intro ⟨x, devm1⟩ hp run; refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨y, devm2⟩ hp; exact Devm.popToNat_getCode_eq hp a}
    intro ⟨y, devm2⟩ hp run; refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨z, devm3⟩ hp; exact Devm.popToNat_getCode_eq hp a}
    intro ⟨z, devm3⟩ hp run; refine getCode_eq_of_bind run id ?_ ?_
    {intro devm4 hc; exact chargeGas_getCode_eq hc a}
    intro devm4 hc run; split at run
    · cases run
    · injection run with eq; subst eq; rfl
  case extcodehash =>
    refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.popToAdr_getCode_eq hp a}
    intro ⟨x, devm1⟩ hp run; split at run
    · refine getCode_eq_of_bind run id ?_ ?_
      {intro devm2 hc; exact chargeGas_getCode_eq hc a}
      intro devm2 hc run; exact Devm.push_getCode_eq run a
    · refine getCode_eq_of_bind run id ?_ ?_
      {intro devm2 hc; exact chargeGas_getCode_eq hc a}
      intro devm2 hc run; exact Devm.push_getCode_eq run a
  case blockhash =>
    refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.pop_getCode_eq hp a}
    intro ⟨x, devm1⟩ hp run; refine getCode_eq_of_bind run id ?_ ?_
    {intro devm2 hc; exact chargeGas_getCode_eq hc a}
    intro devm2 hc run; exact Devm.push_getCode_eq run a
  case coinbase => apply pushItem_getCode_eq run
  case timestamp => apply pushItem_getCode_eq run
  case number => apply pushItem_getCode_eq run
  case prevrandao => apply pushItem_getCode_eq run
  case gaslimit => apply pushItem_getCode_eq run
  case chainid => apply pushItem_getCode_eq run
  case selfbalance => apply pushItem_getCode_eq run
  case basefee => apply pushItem_getCode_eq run
  case blobhash =>
    refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.pop_getCode_eq hp a}
    intro ⟨x, devm1⟩ hp run; refine getCode_eq_of_bind run id ?_ ?_
    {intro devm2 hc; exact chargeGas_getCode_eq hc a}
    intro devm2 hc run; exact Devm.push_getCode_eq run a
  case blobbasefee => apply pushItem_getCode_eq run
  case pop =>
    refine getCode_eq_of_bind run id ?_ ?_
    {intro devm1 hc; exact Devm.pop_map_snd_getCode_eq hc a}
    intro devm1 hc run; exact chargeGas_getCode_eq run a
  case mload =>
    refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.popToNat_getCode_eq hp a}
    intro ⟨x, devm1⟩ hp run; refine getCode_eq_of_bind run id ?_ ?_
    {intro devm2 hc; exact chargeGas_getCode_eq hc a}
    intro devm2 hc run; exact Devm.push_getCode_eq run a
  case mstore =>
    refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.popToNat_getCode_eq hp a}
    intro ⟨x, devm1⟩ hp run; refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨y, devm2⟩ hp; exact Devm.pop_getCode_eq hp a}
    intro ⟨y, devm2⟩ hp run; refine getCode_eq_of_bind run id ?_ ?_
    {intro devm3 hc; exact chargeGas_getCode_eq hc a}
    intro devm3 hc run; injection run with eq; subst eq; rfl
  case mstore8 =>
    refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.popToNat_getCode_eq hp a}
    intro ⟨x, devm1⟩ hp run; refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨y, devm2⟩ hp; exact Devm.pop_getCode_eq hp a}
    intro ⟨y, devm2⟩ hp run; refine getCode_eq_of_bind run id ?_ ?_
    {intro devm3 hc; exact chargeGas_getCode_eq hc a}
    intro devm3 hc run; injection run with eq; subst eq; rfl
  case sload =>
    refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.pop_getCode_eq hp a}
    intro ⟨x, devm1⟩ hp run; split at run
    · refine getCode_eq_of_bind run id ?_ ?_
      {intro devm2 hc; exact chargeGas_getCode_eq hc a}
      intro devm2 hc run; exact Devm.push_getCode_eq run a
    · refine getCode_eq_of_bind run id ?_ ?_
      {intro devm2 hc; exact chargeGas_getCode_eq hc a}
      intro devm2 hc run; exact Devm.push_getCode_eq run a
  case sstore =>
    have h := @sstore_inv_getCode pc sevm devm devm'
    simp only [Rinst.run, Rinst.runCore] at h
    apply h run _
  case tload =>
    refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.pop_getCode_eq hp a}
    intro ⟨x, devm1⟩ hp run; exact pushItem_getCode_eq run a
  case tstore =>
    refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.pop_getCode_eq hp a}
    intro ⟨x, devm1⟩ hp run; refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨y, devm2⟩ hp; exact Devm.pop_getCode_eq hp a}
    intro ⟨y, devm2⟩ hp run; refine getCode_eq_of_bind run id ?_ ?_
    {intro devm3 hc; exact chargeGas_getCode_eq hc a}
    intro devm3 hc run
    rcases of_bind_eq_ok run with ⟨_, _, run'⟩
    injection run' with rw
    rw [← rw]
    simp [Devm.getCode, Devm.getAcct, Devm.setTransVal]
  case mcopy =>
    refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.popToNat_getCode_eq hp a}
    intro ⟨x, devm1⟩ hp run; refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨y, devm2⟩ hp; exact Devm.popToNat_getCode_eq hp a}
    intro ⟨y, devm2⟩ hp run; refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨z, devm3⟩ hp; exact Devm.popToNat_getCode_eq hp a}
    intro ⟨z, devm3⟩ hp run; refine getCode_eq_of_bind run id ?_ ?_
    {intro devm4 hc; exact chargeGas_getCode_eq hc a}
    intro devm4 hc run; injection run with eq; subst eq; rfl
  case pc => apply pushItem_getCode_eq run
  case msize => apply pushItem_getCode_eq run
  case gas =>
    refine getCode_eq_of_bind run id ?_ ?_
    {intro devm1 hc; exact chargeGas_getCode_eq hc a}
    intro devm1 hc run; exact Devm.push_getCode_eq run a
  case dup =>
    refine getCode_eq_of_bind run id ?_ ?_
    {intro devm1 hc; exact chargeGas_getCode_eq hc a}
    intro devm1 hc run; split at run
    · cases run
    · exact Devm.push_getCode_eq run a
  case swap =>
    refine getCode_eq_of_bind run id ?_ ?_
    {intro devm1 hc; exact chargeGas_getCode_eq hc a}
    intro devm1 hc run; split at run
    · cases run
    · injection run with eq; subst eq; rfl
  case log =>
    refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.popToNat_getCode_eq hp a}
    intro ⟨x, devm1⟩ hp run; refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨y, devm2⟩ hp; exact Devm.popToNat_getCode_eq hp a}
    intro ⟨y, devm2⟩ hp run; refine getCode_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨z, devm3⟩ hp; exact Devm.popN_getCode_eq hp a}
    intro ⟨z, devm3⟩ hp run; refine getCode_eq_of_bind run id ?_ ?_
    {intro devm4 hc; exact chargeGas_getCode_eq hc a}
    intro devm4 hc run
    rcases of_bind_eq_ok run with ⟨_, _, run'⟩
    injection run' with rw
    rw [← rw]
    rfl

def Execution.getCode : Execution → Adr → ByteArray
  | Except.error ⟨_, devm⟩, adr => devm.getCode adr
  | Except.ok devm, adr => devm.getCode adr

lemma chargeGas_getCode_gen {cost devm exn} (h : chargeGas cost devm = exn) (a : Adr) : Execution.getCode exn a = devm.getCode a := by
  simp only [chargeGas] at h
  split at h
  · subst h; rfl
  · subst h; rfl

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
  dsimp [Devm.push, Except.assert] at h
  split at h
  · dsimp [Bind.bind, Except.bind] at h
    rw [← h]
    rfl
  · dsimp [Bind.bind, Except.bind] at h
    rw [← h]
    rfl

def Xlot.InvGetCode : Xlot → Prop
  | .none => True
  | .some ⟨sevm, devm, exn⟩ =>
    ∃ exec : Exec 0 sevm devm exn,
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

lemma ExecuteCode.inv_getCode_cond
    {msg : Msg} {xl : Xlot} {devm'} (inv : xl.InvGetCode)
    (run : ExecuteCode msg xl (.ok devm')) :
    ∀ a : Adr,
      (msg.benv.state.getCode a).toList ≠ [] →
      devm'.getCode a = msg.benv.state.getCode a := by
  dsimp [ExecuteCode] at run
  split at run
  · rename _ => eq_none
    rcases eq_none with ⟨ex', h_xl, h_err⟩
    rw [h_xl] at inv
    dsimp [Xlot.InvGetCode] at inv
    rcases inv with ⟨exec, inv_eq⟩
    cases ex'
    · dsimp [executeCode.handleError] at h_err
      revert h_err; split <;> intro h_err
      · simp only [Except.ok.injEq] at h_err; subst devm'
        intro a ha; exact (inv_eq a ha).symm
      · revert h_err; split <;> intro h_err
        · simp only [Except.ok.injEq] at h_err; subst devm'
          intro a ha; exact (inv_eq a ha).symm
        · contradiction
    · dsimp [executeCode.handleError] at h_err
      simp only [Except.ok.injEq] at h_err; subst devm'
      intro a ha; exact (inv_eq a ha).symm
  · next adr eq_some =>
    split at run
    · rcases run with ⟨h_xl, h_err⟩
      cases h_ex : executePrecomp (initEvm msg) adr with
      | error ex_err =>
        rw [h_ex] at h_err
        dsimp [executeCode.handleError] at h_err
        revert h_err; split <;> intro h_err
        · simp only [Except.ok.injEq] at h_err; subst devm'
          intro a _
          have := executePrecomp_inv_getCode (initEvm msg) adr (Except.error ex_err) h_ex a
          exact this
        · revert h_err; split <;> intro h_err
          · simp only [Except.ok.injEq] at h_err; subst devm'
            intro a _
            have := executePrecomp_inv_getCode (initEvm msg) adr (Except.error ex_err) h_ex a
            exact this
          · contradiction
      | ok ex_ok =>
        rw [h_ex] at h_err
        dsimp [executeCode.handleError] at h_err
        simp only [Except.ok.injEq] at h_err; subst devm'
        intro a _
        have := executePrecomp_inv_getCode (initEvm msg) adr (Except.ok ex_ok) h_ex a
        exact this
    · rcases run with ⟨ex', h_xl, h_err⟩
      rw [h_xl] at inv
      dsimp [Xlot.InvGetCode] at inv
      rcases inv with ⟨exec, inv_eq⟩
      cases ex'
      · dsimp [executeCode.handleError] at h_err
        revert h_err; split <;> intro h_err
        · simp only [Except.ok.injEq] at h_err; subst devm'
          intro a ha; exact (inv_eq a ha).symm
        · revert h_err; split <;> intro h_err
          · simp only [Except.ok.injEq] at h_err; subst devm'
            intro a ha; exact (inv_eq a ha).symm
          · contradiction
      · dsimp [executeCode.handleError] at h_err
        simp only [Except.ok.injEq] at h_err; subst devm'
        intro a ha; exact (inv_eq a ha).symm

def MsgResult.getCode (exn : Except (String × State × AdrSet × Tra) Devm) (a : Adr) : ByteArray :=
  match exn with
  | .ok d => d.getCode a
  | .error ⟨_, state, _, _⟩ => state.getCode a

lemma ExecuteCode.inv_getCode_gen
    {msg : Msg} {xl : Xlot} {exn : Except (String × State × AdrSet × Tra) Devm}
    (inv : xl.InvGetCode)
    (run : ExecuteCode msg xl exn) :
    ∀ a : Adr,
      (msg.benv.state.getCode a).toList ≠ [] →
      MsgResult.getCode exn a = msg.benv.state.getCode a := by
  dsimp [ExecuteCode] at run
  split at run
  · rename _ => eq_none
    rcases eq_none with ⟨ex', h_xl, h_err⟩
    rw [h_xl] at inv
    dsimp [Xlot.InvGetCode] at inv
    rcases inv with ⟨exec, inv_eq⟩
    subst h_err
    cases ex'
    · dsimp [executeCode.handleError]
      split
      · intro a ha; dsimp [MsgResult.getCode]; exact (inv_eq a ha).symm
      · split
        · intro a ha; dsimp [MsgResult.getCode]; exact (inv_eq a ha).symm
        · intro a ha; dsimp [MsgResult.getCode, Execution.getCode, Devm.getCode]; exact (inv_eq a ha).symm
    · intro a ha; dsimp [executeCode.handleError, MsgResult.getCode]; exact (inv_eq a ha).symm
  · next adr eq_some =>
    split at run
    · rcases run with ⟨h_xl, h_err⟩
      cases h_ex : executePrecomp (initEvm msg) adr
      · rename_i ex_err
        rw [h_ex] at h_err
        subst h_err
        dsimp [executeCode.handleError]
        split
        · intro a _
          dsimp [MsgResult.getCode]
          have := executePrecomp_inv_getCode (initEvm msg) adr (Except.error ex_err) h_ex a
          exact this
        · split
          · intro a _
            dsimp [MsgResult.getCode]
            have := executePrecomp_inv_getCode (initEvm msg) adr (Except.error ex_err) h_ex a
            exact this
          · intro a _
            dsimp [MsgResult.getCode, Execution.getCode, Devm.getCode]
            have := executePrecomp_inv_getCode (initEvm msg) adr (Except.error ex_err) h_ex a
            exact this
      · rename_i ex_ok
        rw [h_ex] at h_err
        subst h_err
        dsimp [executeCode.handleError]
        intro a _
        dsimp [MsgResult.getCode]
        have := executePrecomp_inv_getCode (initEvm msg) adr (Except.ok ex_ok) h_ex a
        exact this
    · rcases run with ⟨ex', h_xl, h_err⟩
      rw [h_xl] at inv
      dsimp [Xlot.InvGetCode] at inv
      rcases inv with ⟨exec, inv_eq⟩
      subst h_err
      cases ex'
      · dsimp [executeCode.handleError]
        split
        · intro a ha; dsimp [MsgResult.getCode]; exact (inv_eq a ha).symm
        · split
          · intro a ha; dsimp [MsgResult.getCode]; exact (inv_eq a ha).symm
          · intro a ha; dsimp [MsgResult.getCode, Execution.getCode, Devm.getCode]; exact (inv_eq a ha).symm
      · intro a ha; dsimp [executeCode.handleError, MsgResult.getCode]; exact (inv_eq a ha).symm

lemma ProcessMessage.inv_getCode_cond
    {msg : Msg} {xl : Xlot} {devm'}
    (inv : xl.InvGetCode)
    (run : ProcessMessage msg xl (.ok devm')) :
    ∀ a : Adr,
      (msg.benv.state.getCode a).toList ≠ [] →
      devm'.getCode a = msg.benv.state.getCode a := by
  dsimp [ProcessMessage] at run
  dsimp [Except.SplitXl] at run
  rcases run with ⟨x, _, h_err, _⟩ | ⟨benv, h_benv, ex', h_exec, h_ex'⟩
  · contradiction
  · dsimp [Except.Split] at h_ex'
    rcases h_ex' with ⟨x, _, h_err⟩ | ⟨evm, eq_ok, h_if⟩
    · contradiction
    · subst ex'
      intro a ha
      have h_exec_cond := ExecuteCode.inv_getCode_cond inv h_exec a
      have h_benv_code : benv.state.getCode a = msg.benv.state.getCode a := by
        dsimp [Msg.benvAfterTransfer, Msg.shouldTransferValue] at h_benv
        split at h_benv
        · cases h_sub : msg.benv.subBal msg.caller msg.value
          · simp [h_sub, Option.toExcept, Bind.bind, Except.bind] at h_benv
          · simp [h_sub, Option.toExcept, Bind.bind, Except.bind] at h_benv
            subst benv
            rw [Benv.addBal_getCode]
            exact Benv.subBal_getCode h_sub
        · simp only [Except.ok.injEq] at h_benv; subst benv
          rfl
      split at h_if
      · simp only [Except.ok.injEq] at h_if; subst devm'
        dsimp [Devm.rollback]
        rfl
      · simp only [Except.ok.injEq] at h_if; subst devm'
        dsimp [Msg.withBenv] at h_exec_cond
        rw [h_benv_code] at h_exec_cond
        exact h_exec_cond ha

lemma ProcessMessage.inv_getCode_gen
    {msg : Msg} {xl : Xlot} {exn : Except (String × State × AdrSet × Tra) Devm}
    (inv : xl.InvGetCode)
    (run : ProcessMessage msg xl exn) :
    ∀ a : Adr,
      (msg.benv.state.getCode a).toList ≠ [] →
      MsgResult.getCode exn a = msg.benv.state.getCode a := by
  dsimp [ProcessMessage] at run
  dsimp [Except.SplitXl] at run
  rcases run with ⟨x, h_benv_err, h_exn_err, _⟩ | ⟨benv, h_benv, ex', h_exec, h_ex'⟩
  · intro a _
    rw [h_exn_err]
    dsimp [MsgResult.getCode]
    dsimp [Msg.benvAfterTransfer, Msg.shouldTransferValue] at h_benv_err
    split at h_benv_err
    · cases h_sub : msg.benv.subBal msg.caller msg.value
      · simp [h_sub, Option.toExcept, Bind.bind, Except.bind] at h_benv_err
        subst x
        rfl
      · simp [h_sub, Option.toExcept, Bind.bind, Except.bind] at h_benv_err
    · contradiction
  · intro a ha
    have h_benv_code : benv.state.getCode a = msg.benv.state.getCode a := by
      dsimp [Msg.benvAfterTransfer, Msg.shouldTransferValue] at h_benv
      split at h_benv
      · cases h_sub : msg.benv.subBal msg.caller msg.value
        · simp [h_sub, Option.toExcept, Bind.bind, Except.bind] at h_benv
        · simp [h_sub, Option.toExcept, Bind.bind, Except.bind] at h_benv
          subst benv
          rw [Benv.addBal_getCode]
          exact Benv.subBal_getCode h_sub
      · simp only [Except.ok.injEq] at h_benv; subst benv
        rfl
    have ha' : ( (msg.withBenv benv).benv.state.getCode a ).toList ≠ [] := by
      dsimp [Msg.withBenv]
      rw [h_benv_code]
      exact ha
    have h_exec_cond := ExecuteCode.inv_getCode_gen inv h_exec a ha'
    dsimp [Msg.withBenv] at h_exec_cond
    rw [h_benv_code] at h_exec_cond
    dsimp [Except.Split] at h_ex'
    rcases h_ex' with ⟨x, h_ex'_err, h_exn_err⟩ | ⟨evm, eq_ok, h_if⟩
    · rw [h_exn_err]
      rw [h_ex'_err] at h_exec_cond
      exact h_exec_cond
    · split at h_if
      · rw [← h_if]
        dsimp [MsgResult.getCode, Devm.rollback]
        rfl
      · rw [← h_if]
        rw [eq_ok] at h_exec_cond
        exact h_exec_cond

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

lemma ProcessCreateMessage.inv_getCode_cond
    {msg : Msg} {xl : Xlot} {devm'}
    (inv : xl.InvGetCode)
    (run : ProcessCreateMessage msg xl (.ok devm')) :
    ∀ a : Adr,
      a ≠ msg.currentTarget →
      (msg.benv.state.getCode a).toList ≠ [] →
      devm'.getCode a = msg.benv.state.getCode a := by
  dsimp [ProcessCreateMessage] at run
  rcases run with ⟨ex', h_exec, h_ex'⟩
  dsimp [Except.Split] at h_ex'
  rcases h_ex' with ⟨x, _, h_err⟩ | ⟨evm, eq_ok, h_if⟩
  · contradiction
  · subst ex'
    intro a h_a ha
    have h_exec_cond := ProcessMessage.inv_getCode_cond inv h_exec a
    have h_benv_code : (processCreateMessage.msg msg).benv.state.getCode a = msg.benv.state.getCode a := by
      dsimp [processCreateMessage.msg, Msg.withBenv]
      rw [Benv.incrNonce_getCode, addCreatedAccount_getCode, Benv.setStor_getCode]
    rw [h_benv_code] at h_exec_cond
    have h_exec_cond' := h_exec_cond ha
    split at h_if
    · rename_i h_none
      split at h_if
      · rename_i x_ evm' heq
        simp only [Except.ok.injEq] at h_if; subst devm'
        · dsimp [processCreateMessage.chargeCodeGas] at heq
          split at heq
          · cases heq
          · dsimp [Bind.bind, Except.bind] at heq; split at heq
            · cases heq
            · rename_i devm_charge eq_chargeGas
              split at heq
              · cases heq
              · simp only [Except.ok.injEq] at heq; subst evm'
                have h_charge := chargeGas_getCode_eq eq_chargeGas a
                rw [setCode_getCode h_a.symm, h_charge]
                exact h_exec_cond'
      · rename_i x_ err_ err_evm heq
        split at h_if
        · rename_i h_halt
          simp only [Except.ok.injEq] at h_if; subst devm'
          dsimp [processCreateMessage.exceptionalHalt]
          rfl
        · contradiction
    · rename_i h_some
      simp only [Except.ok.injEq] at h_if; subst devm'
      dsimp [Devm.rollback]
      rfl

lemma ProcessCreateMessage.inv_getCode_gen
    {msg : Msg} {xl : Xlot} {exn : Except (String × State × AdrSet × Tra) Devm}
    (inv : xl.InvGetCode)
    (run : ProcessCreateMessage msg xl exn) :
    ∀ a : Adr,
      a ≠ msg.currentTarget →
      (msg.benv.state.getCode a).toList ≠ [] →
      MsgResult.getCode exn a = msg.benv.state.getCode a := by
  dsimp [ProcessCreateMessage] at run
  rcases run with ⟨ex', h_exec, h_ex'⟩
  dsimp [Except.Split] at h_ex'
  rcases h_ex' with ⟨x, eq_ex'_err, h_exn_err⟩ | ⟨evm, eq_ok, h_if⟩
  · intro a h_a ha
    rw [h_exn_err]
    have h_exec_cond := ProcessMessage.inv_getCode_gen inv h_exec a
    have h_benv_code : (processCreateMessage.msg msg).benv.state.getCode a = msg.benv.state.getCode a := by
      dsimp [processCreateMessage.msg, Msg.withBenv]
      rw [Benv.incrNonce_getCode, addCreatedAccount_getCode, Benv.setStor_getCode]
    rw [h_benv_code] at h_exec_cond
    have h_exec_cond' := h_exec_cond ha
    rw [eq_ex'_err] at h_exec_cond'
    exact h_exec_cond'
  · intro a h_a ha
    have h_exec_cond := ProcessMessage.inv_getCode_gen inv h_exec a
    have h_benv_code : (processCreateMessage.msg msg).benv.state.getCode a = msg.benv.state.getCode a := by
      dsimp [processCreateMessage.msg, Msg.withBenv]
      rw [Benv.incrNonce_getCode, addCreatedAccount_getCode, Benv.setStor_getCode]
    rw [h_benv_code] at h_exec_cond
    have h_exec_cond' := h_exec_cond ha
    split at h_if
    · rename_i h_none
      cases h_charge : processCreateMessage.chargeCodeGas evm
      · rename_i err
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
          rw [eq_ok] at h_exec_cond'
          exact h_exec_cond'
      · rename_i devm_charge
        rw [h_charge] at h_if
        dsimp at h_if
        rw [← h_if]
        dsimp [MsgResult.getCode]
        have h_getCode := processCreateMessage.chargeCodeGas_getCode_gen h_charge a
        dsimp [Execution.getCode] at h_getCode
        rw [setCode_getCode h_a.symm]
        rw [h_getCode]
        rw [eq_ok] at h_exec_cond'
        exact h_exec_cond'
    · rename_i h_some
      rw [← h_if]
      dsimp [MsgResult.getCode, Devm.rollback]
      rfl

lemma GenericCreate.inv_getCode_cond
    {sevm : Sevm} {devm : Devm} {endowment : B256} {newAddress : Adr}
    {memoryIndex memorySize : Nat} {xl : Xlot} {devm'} (inv : xl.InvGetCode)
    (run : GenericCreate sevm devm endowment newAddress memoryIndex memorySize xl (.ok devm')) :
    ∀ (a : Adr),
      (devm.getCode a).toList ≠ [] →
      devm'.getCode a = devm.getCode a := by
  dsimp [GenericCreate] at run
  rcases run with ⟨calldata, eq_calldata, run⟩; subst eq_calldata
  rcases run with ⟨x, h_err, eq_err, _⟩ | ⟨_, h_ok, run⟩
  · contradiction
  · rcases run with ⟨devm1, eq_devm1, run⟩; subst eq_devm1
    rcases run with ⟨createMsgGas, eq_createMsgGas, run⟩; subst eq_createMsgGas
    rcases run with ⟨devm2, eq_devm2, run⟩; subst eq_devm2
    rcases run with ⟨x, h_err, eq_err, _⟩ | ⟨_, h_ok, run⟩
    · contradiction
    · rcases run with ⟨devm3, eq_devm3, run⟩; subst eq_devm3
      rcases run with ⟨sender, eq_sender, run⟩; subst eq_sender
      split at run
      · rcases run with ⟨h_xl, eq_ok⟩
        dsimp [Devm.push, Bind.bind, Except.bind] at eq_ok
        split at eq_ok
        · cases eq_ok
        · simp only [Except.ok.injEq] at eq_ok
          subst devm'
          intro a ha
          rfl
      · rename_i h_if1
        rcases run with ⟨devm4, eq_devm4, run⟩
        split at run
        · rename_i h_if2
          rcases run with ⟨h_xl, eq_ok⟩
          dsimp [Devm.push, Bind.bind, Except.bind] at eq_ok
          split at eq_ok
          · cases eq_ok
          · simp only [Except.ok.injEq] at eq_ok
            subst devm'
            intro a ha
            subst eq_devm4
            exact Devm.incrNonce_getCode
        · rename_i h_if2
          rcases run with ⟨childMsg, eq_childMsg, run⟩; subst eq_childMsg
          rcases run with ⟨ex', h_exec, h_ex'⟩
          rcases h_ex' with ⟨x, h_err, eq_err⟩ | ⟨child, h_ok, run⟩
          · contradiction
          · intro a ha
            rcases ex' with err | devm_child
            · simp [liftToExecution] at h_ok
            · dsimp [liftToExecution] at h_ok
              simp only [Except.ok.injEq] at h_ok
              symm at h_ok
              subst h_ok
              have h_exec_cond := ProcessCreateMessage.inv_getCode_cond inv h_exec a
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
              have h_child_code : child.getCode a = devm4.getCode a := by
                apply h_exec_cond h_a_ne
                have h_devm4 : devm4.getCode a = devm.getCode a := by subst eq_devm4; exact Devm.incrNonce_getCode
                have h_goal : (devm4.getCode a).toList ≠ [] := by
                  rw [h_devm4]
                  exact ha
                exact h_goal
              have h1 : devm4.getCode a = devm.getCode a := by subst eq_devm4; exact Devm.incrNonce_getCode
              split at run
              · rename_i h_child_err
                dsimp [Devm.push, Bind.bind, Except.bind] at run
                split at run
                · cases run
                · simp only [Except.ok.injEq] at run
                  subst devm'
                  rw [← h1, ← h_child_code]
                  dsimp [incorporateChildOnError]
                  rfl
              · rename_i h_child_err
                dsimp [Devm.push, Bind.bind, Except.bind] at run
                split at run
                · cases run
                · simp only [Except.ok.injEq] at run
                  subst devm'
                  rw [← h1, ← h_child_code]
                  dsimp [incorporateChildOnSuccess]
                  rfl

lemma GenericCreate.inv_getCode_gen
    {sevm : Sevm} {devm : Devm} {endowment : B256} {newAddress : Adr}
    {memoryIndex memorySize : Nat} {xl : Xlot} {exn : Execution} (inv : xl.InvGetCode)
    (run : GenericCreate sevm devm endowment newAddress memoryIndex memorySize xl exn) :
    ∀ (a : Adr),
      (devm.getCode a).toList ≠ [] →
      Execution.getCode exn a = devm.getCode a := by
  dsimp [GenericCreate] at run
  rcases run with ⟨calldata, eq_calldata, run⟩; subst eq_calldata
  rcases run with ⟨x, h_err, eq_err, _⟩ | ⟨_, h_ok, run⟩
  · intro a ha
    rw [eq_err]
    have h : Except.assert (memorySize ≤ maxInitcodeSize) ⟨"OutOfGasError", devm⟩ = Except.error x := h_err
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
            have h_exec_cond := ProcessCreateMessage.inv_getCode_gen inv h_exec a h_a_ne h_goal
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
            have h_exec_cond := ProcessCreateMessage.inv_getCode_gen inv h_exec a h_a_ne h_goal
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

lemma GenericCall.inv_getCode_gen
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {input_index input_size output_index output_size : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {xl : Xlot} {exn : Execution}
    (inv : xl.InvGetCode)
    (run : GenericCall sevm devm gas value caller target codeAddress shouldTransferValue isStaticcall input_index input_size output_index output_size code disablePrecompiles xl exn) :
    ∀ a : Adr,
      (devm.getCode a).toList ≠ [] →
      exn.getCode a = devm.getCode a := by
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
      have h_exec_cond := ProcessMessage.inv_getCode_gen inv h_exec a ha
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
      have h_exec_cond := ProcessMessage.inv_getCode_gen inv h_exec a ha
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
            have h_memWrite : (evm2.memWrite output_index (child.output.take output_size)).getCode a = evm2.getCode a := rfl
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
            have h_memWrite : (evm2.memWrite output_index (child.output.take output_size)).getCode a = evm2.getCode a := rfl
            rw [h_memWrite]
            have h_push := Devm.push_getCode_gen h_ok a
            change evm2.getCode a = _ at h_push
            rw [h_push]
            dsimp [incorporateChildOnSuccess]
            change child.getCode a = devm.getCode a
            change child.getCode a = _ at h_exec_cond
            rw [h_exec_cond]
            rfl

lemma GenericCall.inv_getCode_cond
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {input_index input_size output_index output_size : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {xl : Xlot} {devm'}
    (inv : xl.InvGetCode)
    (run : GenericCall sevm devm gas value caller target codeAddress shouldTransferValue isStaticcall input_index input_size output_index output_size code disablePrecompiles xl (.ok devm')) :
    ∀ a : Adr,
      (devm.getCode a).toList ≠ [] →
      devm'.getCode a = devm.getCode a := by
  dsimp [GenericCall] at run
  rcases run with ⟨evm1, eq_evm1, run⟩; subst eq_evm1
  split at run
  · rcases run with ⟨h_xl, eq_ok⟩
    dsimp [Devm.push, Bind.bind, Except.bind] at eq_ok
    split at eq_ok
    · cases eq_ok
    · simp only [Except.ok.injEq] at eq_ok
      subst devm'
      intro a ha
      rfl
  · rename_i h_if
    rcases run with ⟨calldata, eq_calldata, run⟩; subst eq_calldata
    rcases run with ⟨childMsg, eq_childMsg, run⟩; subst eq_childMsg
    rcases run with ⟨ex', h_exec, h_ex'⟩
    rcases h_ex' with ⟨x, h_err, eq_err⟩ | ⟨child, h_ok, run⟩
    · contradiction
    · intro a ha
      rcases ex' with err | devm_child
      · simp [liftToExecution] at h_ok
      · dsimp [liftToExecution] at h_ok
        simp only [Except.ok.injEq] at h_ok
        symm at h_ok
        subst h_ok
        have h_exec_cond := ProcessMessage.inv_getCode_cond inv h_exec a
        have h_child_code : child.getCode a = devm.getCode a := h_exec_cond ha
        split at run
        · rename_i h_child_err
          dsimp [Except.Split] at run
          rcases run with ⟨x, h_err, eq_err⟩ | ⟨evm2, h_ok, eq_ok⟩
          · contradiction
          · simp only [Except.ok.injEq] at eq_ok
            symm at eq_ok
            subst eq_ok
            dsimp [Devm.push, Bind.bind, Except.bind] at h_ok
            split at h_ok
            · cases h_ok
            · simp only [Except.ok.injEq] at h_ok
              symm at h_ok
              subst h_ok
              rw [← h_child_code]
              rfl
        · rename_i h_child_err
          dsimp [Except.Split] at run
          rcases run with ⟨x, h_err, eq_err⟩ | ⟨evm2, h_ok, eq_ok⟩
          · contradiction
          · simp only [Except.ok.injEq] at eq_ok
            symm at eq_ok
            subst eq_ok
            dsimp [Devm.push, Bind.bind, Except.bind] at h_ok
            split at h_ok
            · cases h_ok
            · simp only [Except.ok.injEq] at h_ok
              symm at h_ok
              subst h_ok
              rw [← h_child_code]
              rfl

lemma Xinst.inv_getCode_cond
    {sevm devm x xl devm'}
    (inv : xl.InvGetCode)
    (run : Xinst.Run sevm devm x xl (.ok devm')) :
    ∀ a : Adr,
      (devm.getCode a).toList ≠ [] →
      devm'.getCode a = devm.getCode a := by
  intro a ha
  cases x
  case create =>
    dsimp [Xinst.Run] at run
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨endowment, devm1⟩, eq1, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨memoryIndex, devm2⟩, eq2, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨⟨memorySize, devm3⟩, eq3, run⟩; contradiction
    rcases run with ⟨extendCost, hp4, run⟩
    rcases run with ⟨initCodeCost, hp5, run⟩
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨devm4, eq6, run⟩; contradiction
    rcases run with ⟨calldata, hp7, run⟩
    rcases run with ⟨newAddress, hp8, run⟩
    have hc1 : devm1.getCode a = devm.getCode a := by
      revert eq1; dsimp [Devm.pop]; split <;> intro eq1
      · contradiction
      · injection eq1 with h1; injection h1 with _ h2; subst h2; rfl
    have hc2 : devm2.getCode a = devm1.getCode a := by
      revert eq2; unfold Devm.popToNat Devm.pop; split <;> intro eq2
      · contradiction
      · injection eq2 with h3; injection h3 with _ h4; subst h4; rfl
    have hc3 : devm3.getCode a = devm2.getCode a := by
      revert eq3; unfold Devm.popToNat Devm.pop; split <;> intro eq3
      · contradiction
      · injection eq3 with h5; injection h5 with _ h6; subst h6; rfl
    have hc4 : devm4.getCode a = devm3.getCode a := by
      revert eq6; unfold chargeGas; split <;> intro eq6
      · contradiction
      · injection eq6 with h7; subst h7; rfl
    have hc5 : calldata.getCode a = devm4.getCode a := by
      subst hp7; dsimp [Devm.getCode, Devm.memExtends]; rfl
    have h_code : calldata.getCode a = devm.getCode a := by
      rw [hc5, hc4, hc3, hc2, hc1]
    have ha_calldata : (calldata.getCode a).toList ≠ [] := by
      rw [h_code]
      exact ha
    have h_gen := GenericCreate.inv_getCode_cond inv run a ha_calldata
    rwa [h_code] at h_gen
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
    rcases run with ⟨⟨disablePrecompiles, _, code, delegatedAccessGasCost, devm9⟩, hp11, run⟩
    rcases run with ⟨accessCost, hp12, run⟩
    rcases run with ⟨createCost, hp13, run⟩
    rcases run with ⟨transferCost, hp14, run⟩
    rcases run with ⟨⟨msgCallCost, msgCallStipend⟩, hp15, run⟩
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨devm10, eq16, run⟩; contradiction
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨_, eq17, run⟩; contradiction
    rcases run with ⟨devm11, hp18, run⟩
    rcases run with ⟨senderBal, hp19, run⟩
    have hc1 : devm1.getCode a = devm.getCode a := by
      revert eq1; unfold Devm.pop; split <;> intro eq1
      · contradiction
      · injection eq1 with h1; injection h1 with _ h2; subst h2; rfl
    have hc2 : devm2.getCode a = devm1.getCode a := by
      revert eq2; unfold Devm.popToAdr Devm.pop; split <;> intro eq2
      · contradiction
      · injection eq2 with h3; injection h3 with _ h4; subst h4; rfl
    have hc3 : devm3.getCode a = devm2.getCode a := by
      revert eq3; unfold Devm.pop; split <;> intro eq3
      · contradiction
      · injection eq3 with h5; injection h5 with _ h6; subst h6; rfl
    have hc4 : devm4.getCode a = devm3.getCode a := by
      revert eq4; unfold Devm.popToNat Devm.pop; split <;> intro eq4
      · contradiction
      · injection eq4 with h7; injection h7 with _ h8; subst h8; rfl
    have hc5 : devm5.getCode a = devm4.getCode a := by
      revert eq5; unfold Devm.popToNat Devm.pop; split <;> intro eq5
      · contradiction
      · injection eq5 with h9; injection h9 with _ h10; subst h10; rfl
    have hc6 : devm6.getCode a = devm5.getCode a := by
      revert eq6; unfold Devm.popToNat Devm.pop; split <;> intro eq6
      · contradiction
      · injection eq6 with h11; injection h11 with _ h12; subst h12; rfl
    have hc7 : devm7.getCode a = devm6.getCode a := by
      revert eq7; unfold Devm.popToNat Devm.pop; split <;> intro eq7
      · contradiction
      · injection eq7 with h13; injection h13 with _ h14; subst h14; rfl
    have hc8 : devm8.getCode a = devm7.getCode a := by
      subst hp10; dsimp [addAccessedAddress]; rfl
    have hc9 : devm9.getCode a = devm8.getCode a := by
      have h_acc := @accessDelegation_getCode devm8 callee a
      rw [← hp11] at h_acc
      exact h_acc
    have hc10 : devm10.getCode a = devm9.getCode a := by
      revert eq16; unfold chargeGas; split <;> intro eq16
      · contradiction
      · injection eq16 with h15; subst h15; rfl
    have hc11 : devm11.getCode a = devm10.getCode a := by
      subst hp18; dsimp [Devm.getCode, Devm.memExtends]; rfl
    split_ifs at run with h_bal
    · rcases run with ⟨_, _, _, h_contra⟩ | ⟨devm12, eq20, ⟨h_xl, h_ex⟩⟩; contradiction
      have hc12 : devm12.getCode a = devm11.getCode a := by
        revert eq20; unfold Devm.push Except.assert; dsimp [Bind.bind, Except.bind]; split <;> intro eq20
        · contradiction
        · injection eq20 with h16; subst h16; rfl
      have hc_final : devm'.getCode a = devm12.getCode a := by
        injection h_ex with h_ex2; subst h_ex2; rfl
      rw [hc_final, hc12, hc11, hc10, hc9, hc8, hc7, hc6, hc5, hc4, hc3, hc2, hc1]
    · have h_code : devm11.getCode a = devm.getCode a := by
        rw [hc11, hc10, hc9, hc8, hc7, hc6, hc5, hc4, hc3, hc2, hc1]
      have ha_11 : (devm11.getCode a).toList ≠ [] := by
        rw [h_code]; exact ha
      have h_gen := GenericCall.inv_getCode_cond inv run a ha_11
      rw [h_gen, h_code]
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

    have hc1 : devm1.getCode a = devm.getCode a := by
      revert eq1; unfold Devm.pop; split <;> intro eq1
      · contradiction
      · injection eq1 with h1; injection h1 with _ h2; subst h2; rfl
    have hc2 : devm2.getCode a = devm1.getCode a := by
      revert eq2; unfold Devm.popToAdr Devm.pop; split <;> intro eq2
      · contradiction
      · injection eq2 with h3; injection h3 with _ h4; subst h4; rfl
    have hc3 : devm3.getCode a = devm2.getCode a := by
      revert eq3; unfold Devm.pop; split <;> intro eq3
      · contradiction
      · injection eq3 with h5; injection h5 with _ h6; subst h6; rfl
    have hc4 : devm4.getCode a = devm3.getCode a := by
      revert eq4; unfold Devm.popToNat Devm.pop; split <;> intro eq4
      · contradiction
      · injection eq4 with h7; injection h7 with _ h8; subst h8; rfl
    have hc5 : devm5.getCode a = devm4.getCode a := by
      revert eq5; unfold Devm.popToNat Devm.pop; split <;> intro eq5
      · contradiction
      · injection eq5 with h9; injection h9 with _ h10; subst h10; rfl
    have hc6 : devm6.getCode a = devm5.getCode a := by
      revert eq6; unfold Devm.popToNat Devm.pop; split <;> intro eq6
      · contradiction
      · injection eq6 with h11; injection h11 with _ h12; subst h12; rfl
    have hc7 : devm7.getCode a = devm6.getCode a := by
      revert eq7; unfold Devm.popToNat Devm.pop; split <;> intro eq7
      · contradiction
      · injection eq7 with h13; injection h13 with _ h14; subst h14; rfl
    have hc8 : devm8.getCode a = devm7.getCode a := by
      subst hp10; dsimp [addAccessedAddress]; rfl
    have hc9 : devm9.getCode a = devm8.getCode a := by
      have h_acc := @accessDelegation_getCode devm8 codeAddress a
      rw [← hp11] at h_acc
      exact h_acc
    have hc10 : devm10.getCode a = devm9.getCode a := by
      revert eq15; unfold chargeGas; split <;> intro eq15
      · contradiction
      · injection eq15 with h15; subst h15; rfl
    have hc11 : devm11.getCode a = devm10.getCode a := by
      subst hp16; dsimp [Devm.getCode, Devm.memExtends]; rfl
    split_ifs at run with h_bal
    · rcases run with ⟨_, _, _, h_contra⟩ | ⟨devm12, eq20, ⟨h_xl, h_ex⟩⟩; contradiction
      have hc12 : devm12.getCode a = devm11.getCode a := by
        revert eq20; unfold Devm.push Except.assert; dsimp [Bind.bind, Except.bind]; split <;> intro eq20
        · contradiction
        · injection eq20 with h16; subst h16; rfl
      have hc_final : devm'.getCode a = devm12.getCode a := by
        injection h_ex with h_ex2; subst h_ex2; rfl
      rw [hc_final, hc12, hc11, hc10, hc9, hc8, hc7, hc6, hc5, hc4, hc3, hc2, hc1]
    · have h_code : devm11.getCode a = devm.getCode a := by
        rw [hc11, hc10, hc9, hc8, hc7, hc6, hc5, hc4, hc3, hc2, hc1]
      have ha_11 : (devm11.getCode a).toList ≠ [] := by
        rw [h_code]; exact ha
      have h_gen := GenericCall.inv_getCode_cond inv run a ha_11
      rw [h_gen, h_code]
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

    have hc1 : devm1.getCode a = devm.getCode a := by
      revert eq1; unfold Devm.pop; split <;> intro eq1
      · contradiction
      · injection eq1 with h1; injection h1 with _ h2; subst h2; rfl
    have hc2 : devm2.getCode a = devm1.getCode a := by
      revert eq2; unfold Devm.popToAdr Devm.pop; split <;> intro eq2
      · contradiction
      · injection eq2 with h3; injection h3 with _ h4; subst h4; rfl
    have hc3 : devm3.getCode a = devm2.getCode a := by
      revert eq3; unfold Devm.popToNat Devm.pop; split <;> intro eq3
      · contradiction
      · injection eq3 with h5; injection h5 with _ h6; subst h6; rfl
    have hc4 : devm4.getCode a = devm3.getCode a := by
      revert eq4; unfold Devm.popToNat Devm.pop; split <;> intro eq4
      · contradiction
      · injection eq4 with h7; injection h7 with _ h8; subst h8; rfl
    have hc5 : devm5.getCode a = devm4.getCode a := by
      revert eq5; unfold Devm.popToNat Devm.pop; split <;> intro eq5
      · contradiction
      · injection eq5 with h9; injection h9 with _ h10; subst h10; rfl
    have hc6 : devm6.getCode a = devm5.getCode a := by
      revert eq6; unfold Devm.popToNat Devm.pop; split <;> intro eq6
      · contradiction
      · injection eq6 with h11; injection h11 with _ h12; subst h12; rfl
    have hc7 : devm7.getCode a = devm6.getCode a := by
      subst hp9; dsimp [addAccessedAddress]; rfl
    have hc8 : devm8.getCode a = devm7.getCode a := by
      have h_acc := @accessDelegation_getCode devm7 codeAddress a
      rw [← hp10] at h_acc
      exact h_acc
    have hc9 : devm9.getCode a = devm8.getCode a := by
      revert eq13; unfold chargeGas; split <;> intro eq13
      · contradiction
      · injection eq13 with h13; subst h13; rfl
    have hc10 : devm10.getCode a = devm9.getCode a := by
      subst hp14; dsimp [Devm.getCode, Devm.memExtends]; rfl

    have h_code : devm10.getCode a = devm.getCode a := by
      rw [hc10, hc9, hc8, hc7, hc6, hc5, hc4, hc3, hc2, hc1]
    have ha_10 : (devm10.getCode a).toList ≠ [] := by
      rw [h_code]; exact ha
    have h_gen := GenericCall.inv_getCode_cond inv run a ha_10
    rw [h_gen, h_code]
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

    have hc1 : devm1.getCode a = devm.getCode a := by
      revert eq1; dsimp [Devm.pop]; split <;> intro eq1
      · contradiction
      · injection eq1 with h1; injection h1 with _ h2; subst h2; rfl
    have hc2 : devm2.getCode a = devm1.getCode a := by
      revert eq2; unfold Devm.popToNat Devm.pop; split <;> intro eq2
      · contradiction
      · injection eq2 with h3; injection h3 with _ h4; subst h4; rfl
    have hc3 : devm3.getCode a = devm2.getCode a := by
      revert eq3; unfold Devm.popToNat Devm.pop; split <;> intro eq3
      · contradiction
      · injection eq3 with h5; injection h5 with _ h6; subst h6; rfl
    have hc4 : devm4.getCode a = devm3.getCode a := by
      revert eq4; dsimp [Devm.pop]; split <;> intro eq4
      · contradiction
      · injection eq4 with h7; injection h7 with _ h8; subst h8; rfl
    have hc5 : devm5.getCode a = devm4.getCode a := by
      revert eq8; unfold chargeGas; split <;> intro eq8
      · contradiction
      · injection eq8 with h9; subst h9; rfl
    have hc6 : devm6.getCode a = devm5.getCode a := by
      subst hp9; dsimp [Devm.getCode, Devm.memExtends]; rfl

    have h_code : devm6.getCode a = devm.getCode a := by
      rw [hc6, hc5, hc4, hc3, hc2, hc1]
    have ha_6 : (devm6.getCode a).toList ≠ [] := by
      rw [h_code]; exact ha
    have h_gen := GenericCreate.inv_getCode_cond inv run a ha_6
    rw [h_gen, h_code]
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
    rcases run with ⟨⟨disablePrecompiles, _, code, delegatedAccessGasCost, devm8⟩, hp10, run⟩
    rcases run with ⟨accessCost, hp11, run⟩
    rcases run with ⟨⟨msgCallCost, msgCallStipend⟩, hp12, run⟩
    rcases run with ⟨_, _, _, h_contra⟩ | ⟨devm9, eq13, run⟩; contradiction
    rcases run with ⟨devm10, hp14, run⟩

    have hc1 : devm1.getCode a = devm.getCode a := by
      revert eq1; unfold Devm.pop; split <;> intro eq1
      · contradiction
      · injection eq1 with h1; injection h1 with _ h2; subst h2; rfl
    have hc2 : devm2.getCode a = devm1.getCode a := by
      revert eq2; unfold Devm.popToAdr Devm.pop; split <;> intro eq2
      · contradiction
      · injection eq2 with h3; injection h3 with _ h4; subst h4; rfl
    have hc3 : devm3.getCode a = devm2.getCode a := by
      revert eq3; unfold Devm.popToNat Devm.pop; split <;> intro eq3
      · contradiction
      · injection eq3 with h5; injection h5 with _ h6; subst h6; rfl
    have hc4 : devm4.getCode a = devm3.getCode a := by
      revert eq4; unfold Devm.popToNat Devm.pop; split <;> intro eq4
      · contradiction
      · injection eq4 with h7; injection h7 with _ h8; subst h8; rfl
    have hc5 : devm5.getCode a = devm4.getCode a := by
      revert eq5; unfold Devm.popToNat Devm.pop; split <;> intro eq5
      · contradiction
      · injection eq5 with h9; injection h9 with _ h10; subst h10; rfl
    have hc6 : devm6.getCode a = devm5.getCode a := by
      revert eq6; unfold Devm.popToNat Devm.pop; split <;> intro eq6
      · contradiction
      · injection eq6 with h11; injection h11 with _ h12; subst h12; rfl
    have hc7 : devm7.getCode a = devm6.getCode a := by
      subst hp9; dsimp [addAccessedAddress]; rfl
    have hc8 : devm8.getCode a = devm7.getCode a := by
      have h_acc := @accessDelegation_getCode devm7 target a
      rw [← hp10] at h_acc
      exact h_acc
    have hc9 : devm9.getCode a = devm8.getCode a := by
      revert eq13; unfold chargeGas; split <;> intro eq13
      · contradiction
      · injection eq13 with h13; subst h13; rfl
    have hc10 : devm10.getCode a = devm9.getCode a := by
      subst hp14; dsimp [Devm.getCode, Devm.memExtends]; rfl

    have h_code : devm10.getCode a = devm.getCode a := by
      rw [hc10, hc9, hc8, hc7, hc6, hc5, hc4, hc3, hc2, hc1]
    have ha_10 : (devm10.getCode a).toList ≠ [] := by
      rw [h_code]; exact ha
    have h_gen := GenericCall.inv_getCode_cond inv run a ha_10
    rw [h_gen, h_code]

lemma Devm.pop_getCode_err {err devm} (h : Devm.pop devm = .error err) (a : Adr) : err.2.getCode a = devm.getCode a := by
  simp only [Devm.pop] at h
  split at h <;> try contradiction
  cases h; rfl

lemma chargeGas_getCode_err {cost devm err} (h : chargeGas cost devm = .error err) (a : Adr) : err.2.getCode a = devm.getCode a := by
  simp only [chargeGas] at h
  split at h <;> try contradiction
  cases h; rfl

lemma Devm.push_getCode_err {v devm err} (h : Devm.push v devm = Except.error err) (a : Adr) : err.2.getCode a = devm.getCode a := by
  unfold Devm.push Except.assert at h; dsimp [Bind.bind, Except.bind] at h
  split_ifs at h <;> try contradiction
  injection h with h1; rw [← h1]

lemma assert_getCode_err {cond : Prop} [Decidable cond] {msg : String} {devm : Devm} {err : String × Devm} (h : Except.assert cond (msg, devm) = Except.error err) (a : Adr) : err.2.getCode a = devm.getCode a := by
  unfold Except.assert at h
  split_ifs at h <;> try contradiction
  injection h with h1; rw [← h1]

lemma Devm.popToNat_getCode_err {devm err} (h : Devm.popToNat devm = .error err) (a : Adr) : err.2.getCode a = devm.getCode a := by
  dsimp [Devm.popToNat, Functor.map, Except.map] at h
  rcases hp : devm.pop with err_pop | ⟨x, devm1⟩
  · simp [hp] at h; cases h; exact Devm.pop_getCode_err hp a
  · simp [hp] at h

lemma Devm.popToAdr_getCode_err {devm err} (h : Devm.popToAdr devm = .error err) (a : Adr) : err.2.getCode a = devm.getCode a := by
  dsimp [Devm.popToAdr, Functor.map, Except.map] at h
  rcases hp : devm.pop with err_pop | ⟨x, devm1⟩
  · simp [hp] at h; cases h; exact Devm.pop_getCode_err hp a
  · simp [hp] at h

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
  induction n generalizing devm err with
  | zero => simp [Devm.popN] at hp
  | succ n ih =>
    simp [Devm.popN, bind, Except.bind] at hp
    split at hp
    · rename_i eq_err; injection hp with eq; subst eq
      exact Devm.pop_getCode_err eq_err a
    · rename_i eq_ok; split at hp
      · rename_i eq_err; injection hp with eq; subst eq
        have h1 := ih eq_err
        have h2 := Devm.pop_getCode_eq eq_ok a
        exact h1.trans h2
      · rename_i eq_ok2; injection hp

lemma pushItem_getCode_err {x c devm err} (h : pushItem x c devm = Except.error err) (a : Adr) : err.2.getCode a = devm.getCode a := by
  simp only [pushItem] at h
  refine getCode_err_of_bind h id ?_ ?_ ?_
  · intro devm1 hc; exact chargeGas_getCode_eq hc a
  · intro e hc; exact chargeGas_getCode_err hc a
  · intro devm1 hc run; exact Devm.push_getCode_err run a

lemma applyUnary_getCode_err {f : B256 → B256} {cost devm err}
    (h : applyUnary f cost devm = Except.error err) (a : Adr) :
    err.2.getCode a = devm.getCode a := by
  simp only [applyUnary] at h
  refine getCode_err_of_bind h Prod.snd ?_ ?_ ?_
  · intro ⟨x, devm1⟩ hp; exact Devm.pop_getCode_eq hp a
  · intro e hp; exact Devm.pop_getCode_err hp a
  · intro ⟨x, devm1⟩ hp run; exact pushItem_getCode_err run a

lemma applyBinary_getCode_err {f : B256 → B256 → B256} {cost devm err}
    (h : applyBinary f cost devm = Except.error err) (a : Adr) :
    err.2.getCode a = devm.getCode a := by
  simp only [applyBinary] at h
  refine getCode_err_of_bind h Prod.snd ?_ ?_ ?_
  · intro ⟨x, devm1⟩ hp; exact Devm.pop_getCode_eq hp a
  · intro e hp; exact Devm.pop_getCode_err hp a
  · intro ⟨x, devm1⟩ hp run
    refine getCode_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨y, devm2⟩ hp2; exact Devm.pop_getCode_eq hp2 a
    · intro e hp2; exact Devm.pop_getCode_err hp2 a
    · intro ⟨y, devm2⟩ hp2 run2; exact pushItem_getCode_err run2 a

lemma applyTernary_getCode_err {f : B256 → B256 → B256 → B256} {cost devm err}
    (h : applyTernary f cost devm = Except.error err) (a : Adr) :
    err.2.getCode a = devm.getCode a := by
  simp only [applyTernary] at h
  refine getCode_err_of_bind h Prod.snd ?_ ?_ ?_
  · intro ⟨x, devm1⟩ hp; exact Devm.pop_getCode_eq hp a
  · intro e hp; exact Devm.pop_getCode_err hp a
  · intro ⟨x, devm1⟩ hp run
    refine getCode_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨y, devm2⟩ hp2; exact Devm.pop_getCode_eq hp2 a
    · intro e hp2; exact Devm.pop_getCode_err hp2 a
    · intro ⟨y, devm2⟩ hp2 run2
      refine getCode_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨z, devm3⟩ hp3; exact Devm.pop_getCode_eq hp3 a
      · intro e hp3; exact Devm.pop_getCode_err hp3 a
      · intro ⟨z, devm3⟩ hp3 run3; exact pushItem_getCode_err run3 a

lemma Rinst.inv_getCode_err
    {pc sevm devm r err}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = Except.error err) (a : Adr) :
    err.2.getCode a = devm.getCode a := by
  cases r <;> dsimp [Rinst.run, Rinst.runCore] at run
  case add => apply applyBinary_getCode_err run
  case mul => apply applyBinary_getCode_err run
  case sub => apply applyBinary_getCode_err run
  case div => apply applyBinary_getCode_err run
  case sdiv => apply applyBinary_getCode_err run
  case mod => apply applyBinary_getCode_err run
  case smod => apply applyBinary_getCode_err run
  case addmod => apply applyTernary_getCode_err run
  case mulmod => apply applyTernary_getCode_err run
  case exp =>
    refine getCode_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.pop_getCode_eq hp a
    · intro e hp; exact Devm.pop_getCode_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getCode_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.pop_getCode_eq hp2 a
      · intro e hp2; exact Devm.pop_getCode_err hp2 a
      · intro ⟨y, devm2⟩ hp2 run3; exact pushItem_getCode_err run3 a
  case signextend => apply applyBinary_getCode_err run
  case lt => apply applyBinary_getCode_err run
  case gt => apply applyBinary_getCode_err run
  case slt => apply applyBinary_getCode_err run
  case sgt => apply applyBinary_getCode_err run
  case eq => apply applyBinary_getCode_err run
  case iszero => apply applyUnary_getCode_err run
  case and => apply applyBinary_getCode_err run
  case or => apply applyBinary_getCode_err run
  case xor => apply applyBinary_getCode_err run
  case not => apply applyUnary_getCode_err run
  case byte => apply applyBinary_getCode_err run
  case shr => apply applyBinary_getCode_err run
  case shl => apply applyBinary_getCode_err run
  case sar => apply applyBinary_getCode_err run
  case kec =>
    refine getCode_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_getCode_eq hp a
    · intro e hp; exact Devm.popToNat_getCode_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getCode_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.popToNat_getCode_eq hp2 a
      · intro e hp2; exact Devm.popToNat_getCode_err hp2 a
      · intro ⟨y, devm2⟩ hp2 run3
        refine getCode_err_of_bind run3 id ?_ ?_ ?_
        · intro devm3 hc; exact chargeGas_getCode_eq hc a
        · intro e hc; exact chargeGas_getCode_err hc a
        · intro devm3 hc run4; exact Devm.push_getCode_err run4 a
  case address => apply pushItem_getCode_err run
  case balance =>
    refine getCode_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.pop_getCode_eq hp a
    · intro e hp; exact Devm.pop_getCode_err hp a
    · intro ⟨x, devm1⟩ hp run2; split at run2
      · refine getCode_err_of_bind run2 id ?_ ?_ ?_
        · intro devm2 hc; exact chargeGas_getCode_eq hc a
        · intro e hc; exact chargeGas_getCode_err hc a
        · intro devm2 hc run3; exact Devm.push_getCode_err run3 a
      · refine getCode_err_of_bind run2 id ?_ ?_ ?_
        · intro devm2 hc; exact chargeGas_getCode_eq hc a
        · intro e hc; exact chargeGas_getCode_err hc a
        · intro devm2 hc run3; exact Devm.push_getCode_err run3 a
  case origin => apply pushItem_getCode_err run
  case caller => apply pushItem_getCode_err run
  case callvalue => apply pushItem_getCode_err run
  case calldataload =>
    refine getCode_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.pop_getCode_eq hp a
    · intro e hp; exact Devm.pop_getCode_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getCode_err_of_bind run2 id ?_ ?_ ?_
      · intro devm2 hc; exact chargeGas_getCode_eq hc a
      · intro e hc; exact chargeGas_getCode_err hc a
      · intro devm2 hc run3; exact Devm.push_getCode_err run3 a
  case calldatasize => apply pushItem_getCode_err run
  case calldatacopy =>
    refine getCode_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_getCode_eq hp a
    · intro e hp; exact Devm.popToNat_getCode_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getCode_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.popToNat_getCode_eq hp2 a
      · intro e hp2; exact Devm.popToNat_getCode_err hp2 a
      · intro ⟨y, devm2⟩ hp2 run3
        refine getCode_err_of_bind run3 Prod.snd ?_ ?_ ?_
        · intro ⟨z, devm3⟩ hp3; exact Devm.popToNat_getCode_eq hp3 a
        · intro e hp3; exact Devm.popToNat_getCode_err hp3 a
        · intro ⟨z, devm3⟩ hp3 run4
          refine getCode_err_of_bind run4 id ?_ ?_ ?_
          · intro devm4 hc; exact chargeGas_getCode_eq hc a
          · intro e hc; exact chargeGas_getCode_err hc a
          · intro devm4 hc run5; injection run5
  case codesize => apply pushItem_getCode_err run
  case codecopy =>
    refine getCode_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_getCode_eq hp a
    · intro e hp; exact Devm.popToNat_getCode_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getCode_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.popToNat_getCode_eq hp2 a
      · intro e hp2; exact Devm.popToNat_getCode_err hp2 a
      · intro ⟨y, devm2⟩ hp2 run3
        refine getCode_err_of_bind run3 Prod.snd ?_ ?_ ?_
        · intro ⟨z, devm3⟩ hp3; exact Devm.popToNat_getCode_eq hp3 a
        · intro e hp3; exact Devm.popToNat_getCode_err hp3 a
        · intro ⟨z, devm3⟩ hp3 run4
          refine getCode_err_of_bind run4 id ?_ ?_ ?_
          · intro devm4 hc; exact chargeGas_getCode_eq hc a
          · intro e hc; exact chargeGas_getCode_err hc a
          · intro devm4 hc run5; injection run5
  case gasprice => apply pushItem_getCode_err run
  case extcodesize =>
    refine getCode_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToAdr_getCode_eq hp a
    · intro e hp; exact Devm.popToAdr_getCode_err hp a
    · intro ⟨x, devm1⟩ hp run2; split at run2
      · refine getCode_err_of_bind run2 id ?_ ?_ ?_
        · intro devm2 hc; exact chargeGas_getCode_eq hc a
        · intro e hc; exact chargeGas_getCode_err hc a
        · intro devm2 hc run3; exact Devm.push_getCode_err run3 a
      · refine getCode_err_of_bind run2 id ?_ ?_ ?_
        · intro devm2 hc; exact chargeGas_getCode_eq hc a
        · intro e hc; exact chargeGas_getCode_err hc a
        · intro devm2 hc run3; exact Devm.push_getCode_err run3 a
  case extcodecopy =>
    refine getCode_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToAdr_getCode_eq hp a
    · intro e hp; exact Devm.popToAdr_getCode_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getCode_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.popToNat_getCode_eq hp2 a
      · intro e hp2; exact Devm.popToNat_getCode_err hp2 a
      · intro ⟨y, devm2⟩ hp2 run3
        refine getCode_err_of_bind run3 Prod.snd ?_ ?_ ?_
        · intro ⟨z, devm3⟩ hp3; exact Devm.popToNat_getCode_eq hp3 a
        · intro e hp3; exact Devm.popToNat_getCode_err hp3 a
        · intro ⟨z, devm3⟩ hp3 run4
          refine getCode_err_of_bind run4 Prod.snd ?_ ?_ ?_
          · intro ⟨w, devm4⟩ hp4; exact Devm.popToNat_getCode_eq hp4 a
          · intro e hp4; exact Devm.popToNat_getCode_err hp4 a
          · intro ⟨w, devm4⟩ hp4 run5
            split at run5
            · refine getCode_err_of_bind run5 id ?_ ?_ ?_
              · intro devm5 hc; exact chargeGas_getCode_eq hc a
              · intro e hc; exact chargeGas_getCode_err hc a
              · intro devm5 hc run6; injection run6
            · refine getCode_err_of_bind run5 id ?_ ?_ ?_
              · intro devm5 hc; exact chargeGas_getCode_eq hc a
              · intro e hc; exact chargeGas_getCode_err hc a
              · intro devm5 hc run6; injection run6
  case retdatasize => apply pushItem_getCode_err run
  case retdatacopy =>
    refine getCode_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_getCode_eq hp a
    · intro e hp; exact Devm.popToNat_getCode_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getCode_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.popToNat_getCode_eq hp2 a
      · intro e hp2; exact Devm.popToNat_getCode_err hp2 a
      · intro ⟨y, devm2⟩ hp2 run3
        refine getCode_err_of_bind run3 Prod.snd ?_ ?_ ?_
        · intro ⟨z, devm3⟩ hp3; exact Devm.popToNat_getCode_eq hp3 a
        · intro e hp3; exact Devm.popToNat_getCode_err hp3 a
        · intro ⟨z, devm3⟩ hp3 run4
          refine getCode_err_of_bind run4 id ?_ ?_ ?_
          · intro devm4 hc; exact chargeGas_getCode_eq hc a
          · intro e hc; exact chargeGas_getCode_err hc a
          · intro devm4 hc run5
            split_ifs at run5
            all_goals (try { cases run5; rfl })
            all_goals (try contradiction)
  case extcodehash =>
    refine getCode_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToAdr_getCode_eq hp a
    · intro e hp; exact Devm.popToAdr_getCode_err hp a
    · intro ⟨x, devm1⟩ hp run2; split at run2
      · refine getCode_err_of_bind run2 id ?_ ?_ ?_
        · intro devm2 hc; exact chargeGas_getCode_eq hc a
        · intro e hc; exact chargeGas_getCode_err hc a
        · intro devm2 hc run3; exact Devm.push_getCode_err run3 a
      · refine getCode_err_of_bind run2 id ?_ ?_ ?_
        · intro devm2 hc; exact chargeGas_getCode_eq hc a
        · intro e hc; exact chargeGas_getCode_err hc a
        · intro devm2 hc run3; exact Devm.push_getCode_err run3 a
  case blockhash =>
    refine getCode_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.pop_getCode_eq hp a
    · intro e hp; exact Devm.pop_getCode_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getCode_err_of_bind run2 id ?_ ?_ ?_
      · intro devm2 hc; exact chargeGas_getCode_eq hc a
      · intro e hc; exact chargeGas_getCode_err hc a
      · intro devm2 hc run3; exact Devm.push_getCode_err run3 a
  case coinbase => apply pushItem_getCode_err run
  case timestamp => apply pushItem_getCode_err run
  case number => apply pushItem_getCode_err run
  case prevrandao => apply pushItem_getCode_err run
  case gaslimit => apply pushItem_getCode_err run
  case chainid => apply pushItem_getCode_err run
  case selfbalance => apply pushItem_getCode_err run
  case basefee => apply pushItem_getCode_err run
  case blobhash =>
    refine getCode_err_of_bind run Prod.snd ?_ ?_ ?_
    exact fun ⟨x, devm1⟩ hp => Devm.pop_getCode_eq hp a
    exact fun e hp => Devm.pop_getCode_err hp a
    intro ⟨x, devm1⟩ hp run2
    refine getCode_err_of_bind run2 id ?_ ?_ ?_
    exact fun devm2 hc => chargeGas_getCode_eq hc a
    exact fun e hc => chargeGas_getCode_err hc a
    intro devm2 hc run3; exact Devm.push_getCode_err run3 a
  case blobbasefee => apply pushItem_getCode_err run
  case pop =>
    refine getCode_err_of_bind run id ?_ ?_ ?_
    exact fun devm1 hc => Devm.pop_map_snd_getCode_eq hc a
    exact fun e hc => Devm.pop_map_snd_getCode_err hc a
    intro devm1 hc run2; exact chargeGas_getCode_err run2 a
  case mload =>
    refine getCode_err_of_bind run Prod.snd ?_ ?_ ?_
    exact fun ⟨x, devm1⟩ hp => Devm.popToNat_getCode_eq hp a
    exact fun e hp => Devm.popToNat_getCode_err hp a
    intro ⟨x, devm1⟩ hp run2
    refine getCode_err_of_bind run2 id ?_ ?_ ?_
    exact fun devm2 hc => chargeGas_getCode_eq hc a
    exact fun e hc => chargeGas_getCode_err hc a
    intro devm2 hc run3; exact Devm.push_getCode_err run3 a
  case mstore =>
    refine getCode_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_getCode_eq hp a
    · intro e hp; exact Devm.popToNat_getCode_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getCode_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.pop_getCode_eq hp2 a
      · intro e hp2; exact Devm.pop_getCode_err hp2 a
      · intro ⟨y, devm2⟩ hp2 run3
        refine getCode_err_of_bind run3 id ?_ ?_ ?_
        · intro devm3 hc; exact chargeGas_getCode_eq hc a
        · intro e hc; exact chargeGas_getCode_err hc a
        · intro devm3 hc run4; cases run4
  case mstore8 =>
    refine getCode_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_getCode_eq hp a
    · intro e hp; exact Devm.popToNat_getCode_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getCode_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.pop_getCode_eq hp2 a
      · intro e hp2; exact Devm.pop_getCode_err hp2 a
      · intro ⟨y, devm2⟩ hp2 run3
        refine getCode_err_of_bind run3 id ?_ ?_ ?_
        · intro devm3 hc; exact chargeGas_getCode_eq hc a
        · intro e hc; exact chargeGas_getCode_err hc a
        · intro devm3 hc run4; injection run4
  case sload =>
    refine getCode_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.pop_getCode_eq hp a
    · intro e hp; exact Devm.pop_getCode_err hp a
    · intro ⟨x, devm1⟩ hp run2; split at run2
      · refine getCode_err_of_bind run2 id ?_ ?_ ?_
        · intro devm2 hc; exact chargeGas_getCode_eq hc a
        · intro e hc; exact chargeGas_getCode_err hc a
        · intro devm2 hc run3; exact Devm.push_getCode_err run3 a
      · refine getCode_err_of_bind run2 id ?_ ?_ ?_
        · intro devm2 hc; exact chargeGas_getCode_eq hc a
        · intro e hc; exact chargeGas_getCode_err hc a
        · intro devm2 hc run3; exact Devm.push_getCode_err run3 a
  case sstore =>
    refine getCode_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.pop_getCode_eq hp a
    · intro e hp; exact Devm.pop_getCode_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getCode_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.pop_getCode_eq hp2 a
      · intro e hp2; exact Devm.pop_getCode_err hp2 a
      · intro ⟨y, devm2⟩ hp2 run3
        refine getCode_err_of_bind run3 (fun _ => devm2) ?_ ?_ ?_
        · intro u h_assert; rfl
        · intro e h_assert; exact assert_getCode_err h_assert a
        · intro u h_assert run4
          split_ifs at run4
          all_goals {
            refine getCode_err_of_bind run4 id ?_ ?_ ?_
            · intro devm3 hc; exact chargeGas_getCode_eq hc a
            · intro e hc; exact chargeGas_getCode_err hc a
            · intro devm3 hc run5
              dsimp [assertDynamic, Except.assert] at run5
              split_ifs at run5
              all_goals (try { cases run5; rfl })
              all_goals (try injection run5)
          }
  case pc =>
    refine getCode_err_of_bind run id ?_ ?_ ?_
    · intro devm1 hc; exact chargeGas_getCode_eq hc a
    · intro e hc; exact chargeGas_getCode_err hc a
    · intro devm1 hc run2; exact Devm.push_getCode_err run2 a
  case msize =>
    refine getCode_err_of_bind run id ?_ ?_ ?_
    · intro devm1 hc; exact chargeGas_getCode_eq hc a
    · intro e hc; exact chargeGas_getCode_err hc a
    · intro devm1 hc run2; exact Devm.push_getCode_err run2 a
  case gas =>
    refine getCode_err_of_bind run id ?_ ?_ ?_
    · intro devm1 hc; exact chargeGas_getCode_eq hc a
    · intro e hc; exact chargeGas_getCode_err hc a
    · intro devm1 hc run2; exact Devm.push_getCode_err run2 a
  case tload =>
    refine getCode_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.pop_getCode_eq hp a
    · intro e hp; exact Devm.pop_getCode_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getCode_err_of_bind run2 id ?_ ?_ ?_
      · intro devm2 hc; exact chargeGas_getCode_eq hc a
      · intro e hc; exact chargeGas_getCode_err hc a
      · intro devm2 hc run3; exact Devm.push_getCode_err run3 a
  case tstore =>
    refine getCode_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.pop_getCode_eq hp a
    · intro e hp; exact Devm.pop_getCode_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getCode_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.pop_getCode_eq hp2 a
      · intro e hp2; exact Devm.pop_getCode_err hp2 a
      · intro ⟨y, devm2⟩ hp2 run3
        refine getCode_err_of_bind run3 id ?_ ?_ ?_
        · intro devm3 hc; exact chargeGas_getCode_eq hc a
        · intro e hc; exact chargeGas_getCode_err hc a
        · intro devm3 hc run4
          dsimp [assertDynamic, Except.assert] at run4
          simp only [bind, Except.bind] at run4
          try split_ifs at run4; simp at run4
          rw [← run4]; rfl
  case mcopy =>
    refine getCode_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_getCode_eq hp a
    · intro e hp; exact Devm.popToNat_getCode_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getCode_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.popToNat_getCode_eq hp2 a
      · intro e hp2; exact Devm.popToNat_getCode_err hp2 a
      · intro ⟨y, devm2⟩ hp2 run3
        refine getCode_err_of_bind run3 Prod.snd ?_ ?_ ?_
        · intro ⟨z, devm3⟩ hp3; exact Devm.popToNat_getCode_eq hp3 a
        · intro e hp3; exact Devm.popToNat_getCode_err hp3 a
        · intro ⟨z, devm3⟩ hp3 run4
          refine getCode_err_of_bind run4 id ?_ ?_ ?_
          · intro devm4 hc; exact chargeGas_getCode_eq hc a
          · intro e hc; exact chargeGas_getCode_err hc a
          · intro devm4 hc run5; contradiction
  case dup =>
    refine getCode_err_of_bind run id ?_ ?_ ?_
    · intro devm1 hc; exact chargeGas_getCode_eq hc a
    · intro e hc; exact chargeGas_getCode_err hc a
    · intro devm1 hc run2
      split at run2
      · injection run2 with h_eq; cases h_eq; rfl
      · exact Devm.push_getCode_err run2 a
  case swap =>
    refine getCode_err_of_bind run id ?_ ?_ ?_
    · intro devm1 hc; exact chargeGas_getCode_eq hc a
    · intro e hc; exact chargeGas_getCode_err hc a
    · intro devm1 hc run2
      split at run2
      · injection run2 with h_eq; cases h_eq; rfl
      · contradiction
  case log =>
    refine getCode_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_getCode_eq hp a
    · intro e hp; exact Devm.popToNat_getCode_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getCode_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.popToNat_getCode_eq hp2 a
      · intro e hp2; exact Devm.popToNat_getCode_err hp2 a
      · intro ⟨y, devm2⟩ hp2 run3
        refine getCode_err_of_bind run3 Prod.snd ?_ ?_ ?_
        · intro ⟨z, devm3⟩ hp3; exact Devm.popN_getCode_eq hp3 a
        · intro e hp3; exact Devm.popN_getCode_err hp3 a
        · intro ⟨z, devm3⟩ hp3 run4
          refine getCode_err_of_bind run4 id ?_ ?_ ?_
          · intro devm4 hc; exact chargeGas_getCode_eq hc a
          · intro e hc; exact chargeGas_getCode_err hc a
          · intro devm4 hc run5
            dsimp [assertDynamic, Except.assert] at run5
            simp only [bind, Except.bind] at run5
            try split_ifs at run5; simp at run5
            rw [← run5]; rfl

lemma Rinst.inv_getCode_gen
    {pc sevm devm r exn}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = exn) (a : Adr)
    (ne : (devm.getCode a).toList ≠ []) :
    Execution.getCode exn a = devm.getCode a := by
  cases h_exn : exn
  · exact Rinst.inv_getCode_err (run.trans h_exn) a
  · exact Rinst.inv_getCode (run.trans h_exn) a ne

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
      revert eq1; dsimp [Devm.pop]; split <;> intro eq1
      · contradiction
      · injection eq1 with h1; injection h1 with _ h2; subst h2; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨memoryIndex, devm2⟩, eq2, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans hc1
    have hc2 : devm2.getCode a = devm1.getCode a := by
      revert eq2; unfold Devm.popToNat Devm.pop; split <;> intro eq2
      · contradiction
      · injection eq2 with h3; injection h3 with _ h4; subst h4; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨memorySize, devm3⟩, eq3, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc2.trans hc1)
    have hc3 : devm3.getCode a = devm2.getCode a := by
      revert eq3; unfold Devm.popToNat Devm.pop; split <;> intro eq3
      · contradiction
      · injection eq3 with h5; injection h5 with _ h6; subst h6; rfl
    rcases run with ⟨extendCost, hp4, run⟩
    rcases run with ⟨initCodeCost, hp5, run⟩
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨devm4, eq6, run⟩
    · rw [eq_exn]; exact (chargeGas_getCode_err h_err a).trans (hc3.trans (hc2.trans hc1))
    have hc4 : devm4.getCode a = devm3.getCode a := by
      revert eq6; unfold chargeGas; split <;> intro eq6
      · contradiction
      · injection eq6 with h7; subst h7; rfl
    rcases run with ⟨calldata, hp7, run⟩
    rcases run with ⟨newAddress, hp8, run⟩
    have hc5 : calldata.getCode a = devm4.getCode a := by
      subst hp7; dsimp [Devm.getCode, Devm.memExtends]; rfl
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
      revert eq1; unfold Devm.pop; split <;> intro eq1
      · contradiction
      · injection eq1 with h1; injection h1 with _ h2; subst h2; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨callee, devm2⟩, eq2, run⟩
    · rw [eq_exn]; exact (Devm.popToAdr_getCode_err h_err a).trans hc1
    have hc2 : devm2.getCode a = devm1.getCode a := by
      revert eq2; unfold Devm.popToAdr Devm.pop; split <;> intro eq2
      · contradiction
      · injection eq2 with h3; injection h3 with _ h4; subst h4; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨value, devm3⟩, eq3, run⟩
    · rw [eq_exn]; exact (Devm.pop_getCode_err h_err a).trans (hc2.trans hc1)
    have hc3 : devm3.getCode a = devm2.getCode a := by
      revert eq3; unfold Devm.pop; split <;> intro eq3
      · contradiction
      · injection eq3 with h5; injection h5 with _ h6; subst h6; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨inputIndex, devm4⟩, eq4, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc3.trans (hc2.trans hc1))
    have hc4 : devm4.getCode a = devm3.getCode a := by
      revert eq4; unfold Devm.popToNat Devm.pop; split <;> intro eq4
      · contradiction
      · injection eq4 with h7; injection h7 with _ h8; subst h8; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨inputSize, devm5⟩, eq5, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc4.trans (hc3.trans (hc2.trans hc1)))
    have hc5 : devm5.getCode a = devm4.getCode a := by
      revert eq5; unfold Devm.popToNat Devm.pop; split <;> intro eq5
      · contradiction
      · injection eq5 with h9; injection h9 with _ h10; subst h10; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨outputIndex, devm6⟩, eq6, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1))))
    have hc6 : devm6.getCode a = devm5.getCode a := by
      revert eq6; unfold Devm.popToNat Devm.pop; split <;> intro eq6
      · contradiction
      · injection eq6 with h11; injection h11 with _ h12; subst h12; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨outputSize, devm7⟩, eq7, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc6.trans (hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1)))))
    have hc7 : devm7.getCode a = devm6.getCode a := by
      revert eq7; unfold Devm.popToNat Devm.pop; split <;> intro eq7
      · contradiction
      · injection eq7 with h13; injection h13 with _ h14; subst h14; rfl
    rcases run with ⟨extendCost, hp8, run⟩
    rcases run with ⟨preAccessCost, hp9, run⟩
    rcases run with ⟨devm8, hp10, run⟩
    have hc8 : devm8.getCode a = devm7.getCode a := by
      subst hp10; dsimp [addAccessedAddress]; rfl
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
      revert eq16; unfold chargeGas; split <;> intro eq16
      · contradiction
      · injection eq16 with h15; subst h15; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨_, eq17, run⟩
    · rw [eq_exn]; exact (assert_getCode_err h_err a).trans (hc10.trans (hc9.trans (hc8.trans (hc7.trans (hc6.trans (hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1)))))))))
    rcases run with ⟨devm11, hp18, run⟩
    have hc11 : devm11.getCode a = devm10.getCode a := by
      subst hp18; dsimp [Devm.getCode, Devm.memExtends]; rfl
    rcases run with ⟨senderBal, hp19, run⟩
    split_ifs at run with h_bal
    · rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨devm12, eq20, h_xl2, h_ex⟩
      · rw [eq_exn]; exact (Devm.push_getCode_err h_err a).trans (hc11.trans (hc10.trans (hc9.trans (hc8.trans (hc7.trans (hc6.trans (hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1))))))))))
      have hc12 : devm12.getCode a = devm11.getCode a := by
        revert eq20; unfold Devm.push Except.assert; dsimp [Bind.bind, Except.bind]; split <;> intro eq20
        · contradiction
        · injection eq20 with h16; subst h16; rfl
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
      revert eq1; unfold Devm.pop; split <;> intro eq1
      · contradiction
      · injection eq1 with h1; injection h1 with _ h2; subst h2; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨codeAddress, devm2⟩, eq2, run⟩
    · rw [eq_exn]; exact (Devm.popToAdr_getCode_err h_err a).trans hc1
    have hc2 : devm2.getCode a = devm1.getCode a := by
      revert eq2; unfold Devm.popToAdr Devm.pop; split <;> intro eq2
      · contradiction
      · injection eq2 with h3; injection h3 with _ h4; subst h4; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨value, devm3⟩, eq3, run⟩
    · rw [eq_exn]; exact (Devm.pop_getCode_err h_err a).trans (hc2.trans hc1)
    have hc3 : devm3.getCode a = devm2.getCode a := by
      revert eq3; unfold Devm.pop; split <;> intro eq3
      · contradiction
      · injection eq3 with h5; injection h5 with _ h6; subst h6; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨inputIndex, devm4⟩, eq4, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc3.trans (hc2.trans hc1))
    have hc4 : devm4.getCode a = devm3.getCode a := by
      revert eq4; unfold Devm.popToNat Devm.pop; split <;> intro eq4
      · contradiction
      · injection eq4 with h7; injection h7 with _ h8; subst h8; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨inputSize, devm5⟩, eq5, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc4.trans (hc3.trans (hc2.trans hc1)))
    have hc5 : devm5.getCode a = devm4.getCode a := by
      revert eq5; unfold Devm.popToNat Devm.pop; split <;> intro eq5
      · contradiction
      · injection eq5 with h9; injection h9 with _ h10; subst h10; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨outputIndex, devm6⟩, eq6, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1))))
    have hc6 : devm6.getCode a = devm5.getCode a := by
      revert eq6; unfold Devm.popToNat Devm.pop; split <;> intro eq6
      · contradiction
      · injection eq6 with h11; injection h11 with _ h12; subst h12; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨outputSize, devm7⟩, eq7, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc6.trans (hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1)))))
    have hc7 : devm7.getCode a = devm6.getCode a := by
      revert eq7; unfold Devm.popToNat Devm.pop; split <;> intro eq7
      · contradiction
      · injection eq7 with h13; injection h13 with _ h14; subst h14; rfl
    rcases run with ⟨extendCost, hp8, run⟩
    rcases run with ⟨preAccessCost, hp9, run⟩
    rcases run with ⟨devm8, hp10, run⟩
    have hc8 : devm8.getCode a = devm7.getCode a := by
      subst hp10; dsimp [addAccessedAddress]; rfl
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
      revert eq15; unfold chargeGas; split <;> intro eq15
      · contradiction
      · injection eq15 with h15; subst h15; rfl
    rcases run with ⟨devm11, hp16, run⟩
    have hc11 : devm11.getCode a = devm10.getCode a := by
      subst hp16; dsimp [Devm.getCode, Devm.memExtends]; rfl
    rcases run with ⟨senderBal, hp17, run⟩
    split_ifs at run with h_bal
    · rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨devm12, eq20, h_xl2, h_ex⟩
      · rw [eq_exn]; exact (Devm.push_getCode_err h_err a).trans (hc11.trans (hc10.trans (hc9.trans (hc8.trans (hc7.trans (hc6.trans (hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1))))))))))
      have hc12 : devm12.getCode a = devm11.getCode a := by
        revert eq20; unfold Devm.push Except.assert; dsimp [Bind.bind, Except.bind]; split <;> intro eq20
        · contradiction
        · injection eq20 with h16; subst h16; rfl
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
      revert eq1; unfold Devm.pop; split <;> intro eq1
      · contradiction
      · injection eq1 with h1; injection h1 with _ h2; subst h2; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨codeAddress, devm2⟩, eq2, run⟩
    · rw [eq_exn]; exact (Devm.popToAdr_getCode_err h_err a).trans hc1
    have hc2 : devm2.getCode a = devm1.getCode a := by
      revert eq2; unfold Devm.popToAdr Devm.pop; split <;> intro eq2
      · contradiction
      · injection eq2 with h3; injection h3 with _ h4; subst h4; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨inputIndex, devm3⟩, eq3, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc2.trans hc1)
    have hc3 : devm3.getCode a = devm2.getCode a := by
      revert eq3; unfold Devm.popToNat Devm.pop; split <;> intro eq3
      · contradiction
      · injection eq3 with h5; injection h5 with _ h6; subst h6; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨inputSize, devm4⟩, eq4, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc3.trans (hc2.trans hc1))
    have hc4 : devm4.getCode a = devm3.getCode a := by
      revert eq4; unfold Devm.popToNat Devm.pop; split <;> intro eq4
      · contradiction
      · injection eq4 with h7; injection h7 with _ h8; subst h8; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨outputIndex, devm5⟩, eq5, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc4.trans (hc3.trans (hc2.trans hc1)))
    have hc5 : devm5.getCode a = devm4.getCode a := by
      revert eq5; unfold Devm.popToNat Devm.pop; split <;> intro eq5
      · contradiction
      · injection eq5 with h9; injection h9 with _ h10; subst h10; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨outputSize, devm6⟩, eq6, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1))))
    have hc6 : devm6.getCode a = devm5.getCode a := by
      revert eq6; unfold Devm.popToNat Devm.pop; split <;> intro eq6
      · contradiction
      · injection eq6 with h11; injection h11 with _ h12; subst h12; rfl
    rcases run with ⟨extendCost, hp7, run⟩
    rcases run with ⟨preAccessCost, hp8, run⟩
    rcases run with ⟨devm7, hp9, run⟩
    have hc7 : devm7.getCode a = devm6.getCode a := by
      subst hp9; dsimp [addAccessedAddress]; rfl
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
      revert eq13; unfold chargeGas; split <;> intro eq13
      · contradiction
      · injection eq13 with h13; subst h13; rfl
    rcases run with ⟨devm10, hp14, run⟩
    have hc10 : devm10.getCode a = devm9.getCode a := by
      subst hp14; dsimp [Devm.getCode, Devm.memExtends]; rfl

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
      revert eq1; dsimp [Devm.pop]; split <;> intro eq1
      · contradiction
      · injection eq1 with h1; injection h1 with _ h2; subst h2; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨memoryIndex, devm2⟩, eq2, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans hc1
    have hc2 : devm2.getCode a = devm1.getCode a := by
      revert eq2; unfold Devm.popToNat Devm.pop; split <;> intro eq2
      · contradiction
      · injection eq2 with h3; injection h3 with _ h4; subst h4; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨memorySize, devm3⟩, eq3, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc2.trans hc1)
    have hc3 : devm3.getCode a = devm2.getCode a := by
      revert eq3; unfold Devm.popToNat Devm.pop; split <;> intro eq3
      · contradiction
      · injection eq3 with h5; injection h5 with _ h6; subst h6; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨salt, devm4⟩, eq4, run⟩
    · rw [eq_exn]; exact (Devm.pop_getCode_err h_err a).trans (hc3.trans (hc2.trans hc1))
    have hc4 : devm4.getCode a = devm3.getCode a := by
      revert eq4; dsimp [Devm.pop]; split <;> intro eq4
      · contradiction
      · injection eq4 with h7; injection h7 with _ h8; subst h8; rfl
    rcases run with ⟨extendCost, hp5, run⟩
    rcases run with ⟨initCodeHashCost, hp6, run⟩
    rcases run with ⟨initCodeCost, hp7, run⟩
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨devm5, eq8, run⟩
    · rw [eq_exn]; exact (chargeGas_getCode_err h_err a).trans (hc4.trans (hc3.trans (hc2.trans hc1)))
    have hc5 : devm5.getCode a = devm4.getCode a := by
      revert eq8; unfold chargeGas; split <;> intro eq8
      · contradiction
      · injection eq8 with h9; subst h9; rfl
    rcases run with ⟨devm6, hp9, run⟩
    have hc6 : devm6.getCode a = devm5.getCode a := by
      subst hp9; dsimp [Devm.getCode, Devm.memExtends]; rfl
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
      revert eq1; unfold Devm.pop; split <;> intro eq1
      · contradiction
      · injection eq1 with h1; injection h1 with _ h2; subst h2; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨target, devm2⟩, eq2, run⟩
    · rw [eq_exn]; exact (Devm.popToAdr_getCode_err h_err a).trans hc1
    have hc2 : devm2.getCode a = devm1.getCode a := by
      revert eq2; unfold Devm.popToAdr Devm.pop; split <;> intro eq2
      · contradiction
      · injection eq2 with h3; injection h3 with _ h4; subst h4; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨inputIndex, devm3⟩, eq3, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc2.trans hc1)
    have hc3 : devm3.getCode a = devm2.getCode a := by
      revert eq3; unfold Devm.popToNat Devm.pop; split <;> intro eq3
      · contradiction
      · injection eq3 with h5; injection h5 with _ h6; subst h6; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨inputSize, devm4⟩, eq4, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc3.trans (hc2.trans hc1))
    have hc4 : devm4.getCode a = devm3.getCode a := by
      revert eq4; unfold Devm.popToNat Devm.pop; split <;> intro eq4
      · contradiction
      · injection eq4 with h7; injection h7 with _ h8; subst h8; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨outputIndex, devm5⟩, eq5, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc4.trans (hc3.trans (hc2.trans hc1)))
    have hc5 : devm5.getCode a = devm4.getCode a := by
      revert eq5; unfold Devm.popToNat Devm.pop; split <;> intro eq5
      · contradiction
      · injection eq5 with h9; injection h9 with _ h10; subst h10; rfl
    rcases run with ⟨err, h_err, eq_exn, h_xl⟩ | ⟨⟨outputSize, devm6⟩, eq6, run⟩
    · rw [eq_exn]; exact (Devm.popToNat_getCode_err h_err a).trans (hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1))))
    have hc6 : devm6.getCode a = devm5.getCode a := by
      revert eq6; unfold Devm.popToNat Devm.pop; split <;> intro eq6
      · contradiction
      · injection eq6 with h11; injection h11 with _ h12; subst h12; rfl
    rcases run with ⟨extendCost, hp7, run⟩
    rcases run with ⟨preAccessCost, hp8, run⟩
    rcases run with ⟨devm7, hp9, run⟩
    have hc7 : devm7.getCode a = devm6.getCode a := by
      subst hp9; dsimp [addAccessedAddress]; rfl
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
      revert eq13; unfold chargeGas; split <;> intro eq13
      · contradiction
      · injection eq13 with h13; subst h13; rfl
    rcases run with ⟨devm10, hp14, run⟩
    have hc10 : devm10.getCode a = devm9.getCode a := by
      subst hp14; dsimp [Devm.getCode, Devm.memExtends]; rfl

    have h_code : devm10.getCode a = devm.getCode a := by
      rw [hc10, hc9, hc8, hc7, hc6, hc5, hc4, hc3, hc2, hc1]
    have ha_10 : (devm10.getCode a).toList ≠ [] := by
      rw [h_code]; exact ha
    have h_gen := GenericCall.inv_getCode_gen inv run a ha_10
    rw [h_gen, h_code]

lemma Ninst.inv_getCode_cond
    {pc sevm devm n xl devm'}
    (inv : xl.InvGetCode)
    (run : Ninst.Run' pc sevm devm n xl (.ok devm')) :
    ∀ a : Adr,
      (devm.getCode a).toList ≠ [] →
      devm'.getCode a = devm.getCode a := by
  intro a ha
  cases n <;> dsimp [Ninst.Run'] at run
  case push xs p =>
     rcases xl with _ | _
     · cases hc : chargeGas (if xs = [] then gBase else gVerylow) devm <;> simp [hc, bind, Except.bind] at run
       case ok devm_gas =>
         cases hp : Devm.push xs.toB256 devm_gas <;> simp [hp] at run
         case ok devm_push =>
           subst run
           simp only [chargeGas] at hc; split at hc <;> try contradiction
           simp only [Except.ok.injEq] at hc; subst devm_gas
           simp only [Devm.push, bind, Except.bind, Except.assert] at hp; split at hp <;> try contradiction
           simp only [Except.ok.injEq] at hp; subst devm_push
           rfl
     · cases run
  case reg r =>
    rcases xl with _ | _
    · apply Rinst.inv_getCode run a ha
    · cases run
  case exec x =>
    apply Xinst.inv_getCode_cond inv run a ha

lemma Ninst.inv_getCode_gen
    {pc sevm devm n xl exn}
    (inv : xl.InvGetCode)
    (run : Ninst.Run' pc sevm devm n xl exn) :
    ∀ a : Adr,
      (devm.getCode a).toList ≠ [] →
      exn.getCode a = devm.getCode a := by
  intro a ha
  cases n <;> dsimp [Ninst.Run'] at run
  case push xs p =>
     rcases xl with _ | _
     · cases hc : chargeGas (if xs = [] then gBase else gVerylow) devm <;> simp [hc, bind, Except.bind] at run
       case error err =>
         rw [← run]
         exact chargeGas_getCode_err hc a
       case ok devm_gas =>
         cases hp : Devm.push xs.toB256 devm_gas <;> simp [hp] at run
         case error err =>
           rw [← run]
           have h1 := chargeGas_getCode_eq hc a
           exact (Devm.push_getCode_err hp a).trans h1
         case ok devm_push =>
           subst run
           simp only [chargeGas] at hc; split at hc <;> try contradiction
           simp only [Except.ok.injEq] at hc; subst devm_gas
           simp only [Devm.push, bind, Except.bind, Except.assert] at hp; split at hp <;> try contradiction
           simp only [Except.ok.injEq] at hp; subst devm_push
           rfl
     · cases run
  case reg r =>
    rcases xl with _ | _
    · exact Rinst.inv_getCode_gen run a ha
    · cases run
  case exec x =>
    exact Xinst.inv_getCode_gen inv run a ha

lemma Jinst.inv_getCode
    {pc sevm devm j pc' devm'}
    (run : Jinst.Run ⟨pc, sevm, devm⟩ j (.ok ⟨pc', devm'⟩)) (a : Adr) :
    devm'.getCode a = devm.getCode a := by
  cases h1 : devm.stack
  · cases j
    · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, Except.assert, safeSub, bind, Except.bind] at run
      rw [h1] at run
      dsimp at run
      contradiction
    · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, Except.assert, safeSub, bind, Except.bind] at run
      rw [h1] at run
      dsimp at run
      contradiction
    · by_cases h_gas : gJumpdest ≤ devm.gasLeft
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, bind, Except.bind, safeSub] at run
        rw [h1] at run
        simp only [h_gas, if_pos, Except.ok.injEq, Prod.mk.injEq] at run
        cases run
        subst_vars
        rfl
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, bind, Except.bind, safeSub] at run
        rw [h1] at run
        have h_gas_not : ¬(gJumpdest ≤ devm.gasLeft) := by omega
        simp only [h_gas_not] at run
        try contradiction
  · rename_i x xs
    cases h2 : xs
    · cases j
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, bind, Except.bind, safeSub] at run
        rw [h1] at run
        dsimp at run
        by_cases h_gas : gMid ≤ devm.gasLeft
        · simp only [h_gas, if_pos, Except.ok.injEq, Prod.mk.injEq] at run
          by_cases h_jump : jumpable sevm.code x.toNat = true
          · simp only [h_jump, if_pos, Except.ok.injEq, Prod.mk.injEq] at run
            cases run
            subst_vars
            rfl
          · simp only [h_jump, if_neg, Except.ok.injEq, Prod.mk.injEq] at run
            contradiction
        · have h_gas_not : ¬(gMid ≤ devm.gasLeft) := by omega
          simp only [h_gas_not, if_neg, Except.ok.injEq, Prod.mk.injEq] at run
          contradiction
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, bind, Except.bind, safeSub] at run
        rw [h1] at run
        rw [h2] at run
        dsimp at run
        contradiction
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, bind, Except.bind, safeSub] at run
        rw [h1] at run
        by_cases h_gas : gJumpdest ≤ devm.gasLeft
        · simp only [h_gas, if_pos, Except.ok.injEq, Prod.mk.injEq] at run
          cases run
          subst_vars
          rfl
        · have h_gas_not : ¬(gJumpdest ≤ devm.gasLeft) := by omega
          simp only [h_gas_not, if_neg, Except.ok.injEq, Prod.mk.injEq] at run
          contradiction
    · rename_i x2 xs2
      cases j
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, bind, Except.bind, safeSub] at run
        rw [h1] at run
        dsimp at run
        by_cases h_gas : gMid ≤ devm.gasLeft
        · simp only [h_gas, if_pos, Except.ok.injEq, Prod.mk.injEq] at run
          by_cases h_jump : jumpable sevm.code x.toNat = true
          · simp only [h_jump, if_pos, Except.ok.injEq, Prod.mk.injEq] at run
            cases run
            subst_vars
            rfl
          · simp only [h_jump, if_neg, Except.ok.injEq, Prod.mk.injEq] at run
            contradiction
        · have h_gas_not : ¬(gMid ≤ devm.gasLeft) := by omega
          simp only [h_gas_not, if_neg, Except.ok.injEq, Prod.mk.injEq] at run
          contradiction
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, bind, Except.bind, safeSub] at run
        rw [h1] at run
        rw [h2] at run
        dsimp at run
        by_cases h_gas : gHigh ≤ devm.gasLeft
        · simp only [h_gas, if_pos, Except.ok.injEq, Prod.mk.injEq] at run
          by_cases h_cond : x2 = 0
          · simp only [h_cond, if_pos, Except.ok.injEq, Prod.mk.injEq] at run
            cases run
            subst_vars
            rfl
          · simp only [h_cond, if_neg, Except.ok.injEq, Prod.mk.injEq] at run
            by_cases h_jump : jumpable sevm.code x.toNat = true
            · simp only [h_jump, if_pos, Except.ok.injEq, Prod.mk.injEq] at run
              cases run
              subst_vars
              rfl
            · simp only [h_jump, if_neg, Except.ok.injEq, Prod.mk.injEq] at run
              contradiction
        · have h_gas_not : ¬(gHigh ≤ devm.gasLeft) := by omega
          simp only [h_gas_not, if_neg, Except.ok.injEq, Prod.mk.injEq] at run
          contradiction
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, bind, Except.bind, safeSub] at run
        rw [h1] at run
        by_cases h_gas : gJumpdest ≤ devm.gasLeft
        · simp only [h_gas, if_pos, Except.ok.injEq, Prod.mk.injEq] at run
          cases run
          subst_vars
          rfl
        · have h_gas_not : ¬(gJumpdest ≤ devm.gasLeft) := by omega
          simp only [h_gas_not, if_neg, Except.ok.injEq, Prod.mk.injEq] at run
          contradiction

def JumpResult.getCode (ex : Except (String × Devm) (Nat × Devm)) (a : Adr) : ByteArray :=
  match ex with
  | .ok ⟨_, devm⟩ => devm.getCode a
  | .error ⟨_, devm⟩ => devm.getCode a

lemma Jinst.inv_getCode_gen
    {pc sevm devm j ex}
    (run : Jinst.Run ⟨pc, sevm, devm⟩ j ex) :
    ∀ a : Adr, JumpResult.getCode ex a = devm.getCode a := by
  intro a
  cases h1 : devm.stack
  · cases j
    · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, Except.assert, safeSub, bind, Except.bind] at run
      rw [h1] at run; dsimp at run; cases run; rfl
    · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, Except.assert, safeSub, bind, Except.bind] at run
      rw [h1] at run; dsimp at run; cases run; rfl
    · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, bind, Except.bind, safeSub] at run
      rw [h1] at run
      by_cases h_gas : gJumpdest ≤ devm.gasLeft
      · simp only [h_gas, if_pos] at run; cases run; rfl
      · have h_gas_not : ¬(gJumpdest ≤ devm.gasLeft) := by omega
        simp only [h_gas_not, if_neg] at run; cases run; rfl
  · rename_i x xs
    cases h2 : xs
    · cases j
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, Except.assert, bind, Except.bind, safeSub] at run
        rw [h1] at run; dsimp at run
        by_cases h_gas : gMid ≤ devm.gasLeft
        · simp only [h_gas, if_pos] at run
          by_cases h_jump : jumpable sevm.code x.toNat = true
          · simp only [h_jump, if_pos] at run; cases run; rfl
          · simp only [h_jump, if_neg] at run; cases run; rfl
        · have h_gas_not : ¬(gMid ≤ devm.gasLeft) := by omega
          simp only [h_gas_not, if_neg] at run; cases run; rfl
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, Except.assert, bind, Except.bind, safeSub] at run
        rw [h1] at run; rw [h2] at run; dsimp at run; cases run; rfl
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Except.assert, bind, Except.bind, safeSub] at run
        rw [h1] at run
        by_cases h_gas : gJumpdest ≤ devm.gasLeft
        · simp only [h_gas, if_pos] at run; cases run; rfl
        · have h_gas_not : ¬(gJumpdest ≤ devm.gasLeft) := by omega
          simp only [h_gas_not, if_neg] at run; cases run; rfl
    · rename_i x2 xs2
      cases j
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, Except.assert, bind, Except.bind, safeSub] at run
        rw [h1] at run; dsimp at run
        by_cases h_gas : gMid ≤ devm.gasLeft
        · simp only [h_gas, if_pos] at run
          by_cases h_jump : jumpable sevm.code x.toNat = true
          · simp only [h_jump, if_pos] at run; cases run; rfl
          · simp only [h_jump, if_neg] at run; cases run; rfl
        · have h_gas_not : ¬(gMid ≤ devm.gasLeft) := by omega
          simp only [h_gas_not, if_neg] at run; cases run; rfl
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, Except.assert, bind, Except.bind, safeSub] at run
        rw [h1] at run; rw [h2] at run; dsimp at run
        by_cases h_gas : gHigh ≤ devm.gasLeft
        · simp only [h_gas, if_pos] at run
          by_cases h_cond : x2 = 0
          · simp only [h_cond, if_pos] at run; cases run; rfl
          · simp only [h_cond, if_neg] at run
            by_cases h_jump : jumpable sevm.code x.toNat = true
            · simp only [h_jump, if_pos] at run; cases run; rfl
            · simp only [h_jump, if_neg] at run; cases run; rfl
        · have h_gas_not : ¬(gHigh ≤ devm.gasLeft) := by omega
          simp only [h_gas_not, if_neg] at run; cases run; rfl
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Except.assert, bind, Except.bind, safeSub] at run
        rw [h1] at run
        by_cases h_gas : gJumpdest ≤ devm.gasLeft
        · simp only [h_gas, if_pos] at run; cases run; rfl
        · have h_gas_not : ¬(gJumpdest ≤ devm.gasLeft) := by omega
          simp only [h_gas_not, if_neg] at run; cases run; rfl

lemma Linst.inv_getCode
    {sevm devm l exn}
    (run : Linst.Run sevm devm l exn) :
    ∀ adr : Adr, exn.getCode adr = devm.getCode adr := by
  intro adr
  cases l <;> dsimp [Linst.Run, Linst.run] at run
  case stop => rw [← run]; rfl
  case ret =>
    revert run
    dsimp [bind, Except.bind]
    cases h1 : devm.popToNat <;> dsimp
    case error err =>
      intro run; rw [← run]; exact (Devm.popToNat_getCode_err h1 adr)
    case ok res1 =>
      cases h2 : res1.2.popToNat <;> dsimp
      case error err =>
        intro run; rw [← run]; exact (Devm.popToNat_getCode_err h2 adr).trans (Devm.popToNat_getCode_eq h1 adr)
      case ok res2 =>
        cases h3 : chargeGas (res2.2.extCost [(res1.1, res2.1)]) res2.2 <;> dsimp
        case error err =>
          intro run; rw [← run]; exact (chargeGas_getCode_err h3 adr).trans ((Devm.popToNat_getCode_eq h2 adr).trans (Devm.popToNat_getCode_eq h1 adr))
        case ok res3 =>
          intro run; rw [← run]
          change res3.getCode adr = _
          exact (chargeGas_getCode_eq h3 adr).trans ((Devm.popToNat_getCode_eq h2 adr).trans (Devm.popToNat_getCode_eq h1 adr))
  case rev =>
    revert run
    dsimp [bind, Except.bind]
    cases h1 : devm.popToNat <;> dsimp
    case error err =>
      intro run; rw [← run]; exact (Devm.popToNat_getCode_err h1 adr)
    case ok res1 =>
      cases h2 : res1.2.popToNat <;> dsimp
      case error err =>
        intro run; rw [← run]; exact (Devm.popToNat_getCode_err h2 adr).trans (Devm.popToNat_getCode_eq h1 adr)
      case ok res2 =>
        cases h3 : chargeGas (res2.2.extCost [(res1.1, res2.1)]) res2.2 <;> dsimp
        case error err =>
          intro run; rw [← run]; exact (chargeGas_getCode_err h3 adr).trans ((Devm.popToNat_getCode_eq h2 adr).trans (Devm.popToNat_getCode_eq h1 adr))
        case ok res3 =>
          intro run; rw [← run]
          change res3.getCode adr = _
          exact (chargeGas_getCode_eq h3 adr).trans ((Devm.popToNat_getCode_eq h2 adr).trans (Devm.popToNat_getCode_eq h1 adr))
  case dest =>
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

lemma Exec.inv_getCode {pc} {sevm} {devm} {exn}
    (run : Exec pc sevm devm exn) :
    ∀ a : Adr,
      (devm.getCode a).toList ≠ [] →
      exn.getCode a = devm.getCode a := by
  revert exn devm sevm pc; apply Exec.rec
  · intros; rfl
  · intros _ _ _ _ _ _ _ run adr ne;
    exact Ninst.inv_getCode_gen (xl := .none) trivial run adr ne
  · intros _ _ _ _ _ _ _ _ _ _ run exec ih adr ne;
    exact Ninst.inv_getCode_gen (xl := some _)
            ⟨exec, fun adr hadr => (ih adr hadr).symm⟩ run adr ne
  · intros pc sevm devm n devm' exn hAt run exec ih adr ne
    have h1 := Ninst.inv_getCode_gen (xl := .none) trivial run adr ne
    change devm'.getCode adr = devm.getCode adr at h1
    rw [← h1] at ne; rw [ih adr ne, h1]
  · intros pc sevm devm n sevm_ devm_ exn_ devm' exn hAt run exec_x exec ih_x ih adr ne
    have h1 := Ninst.inv_getCode_gen (xl := some ⟨sevm_, devm_, exn_⟩)
                 ⟨exec_x, fun adr hadr => (ih_x adr hadr).symm⟩ run adr ne
    change devm'.getCode adr = devm.getCode adr at h1
    rw [← h1] at ne; rw [ih adr ne, h1]
  · intros pc sevm devm j err devm' hAt run adr ne
    exact Jinst.inv_getCode_gen run adr
  · intros pc sevm devm j pc' devm' exn hAt run exec ih adr ne
    have h1 := Jinst.inv_getCode_gen run adr
    change devm'.getCode adr = devm.getCode adr at h1
    rw [← h1] at ne; rw [ih adr ne, h1]
  · intro pc sevm devm l exn lat run adr ne
    exact Linst.inv_getCode run adr

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
      have h_inv : devm'.getCode ca = devm.getCode ca := Ninst.inv_getCode_gen (xl := .none) trivial h_run ca h_ne_code
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
        have inv : Xlot.InvGetCode (some ⟨sevm_, devm_, exn_⟩) := ⟨ex_sub, fun adr h => (Exec.inv_getCode ex_sub adr h).symm⟩
        have h_inv : devm'.getCode ca = devm.getCode ca := Ninst.inv_getCode_gen inv h_run ca h_ne_code
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
  · intro pc sevm pre n sevm' devm' exn' inter post h_at h_run _ _ h_ne h_ifOk h_ih h_pi
    rcases nextSome h_at h_run h_ne h_pi with ⟨h_pi_sub, h_imp⟩
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

def Rinst.Inv {ξ : Type} (f : Devm → ξ) (r : Rinst) : Prop :=
  ∀ {pc sevm pre post}, Rinst.run ⟨pc, sevm, pre⟩ r = (.ok post) → f pre = f post

lemma Rinst.inv_bal {r} : Rinst.Inv Devm.getBal r := by
  intros pc sevm pre post; cases r
  case add => exact applyBinary_getBal_eq
  case mul => exact applyBinary_getBal_eq
  case sub => exact applyBinary_getBal_eq
  case div => exact applyBinary_getBal_eq
  case sdiv => exact applyBinary_getBal_eq
  case mod => exact applyBinary_getBal_eq
  case smod => exact applyBinary_getBal_eq
  case signextend => exact applyBinary_getBal_eq
  case lt => exact applyBinary_getBal_eq
  case gt => exact applyBinary_getBal_eq
  case slt => exact applyBinary_getBal_eq
  case sgt => exact applyBinary_getBal_eq
  case eq => exact applyBinary_getBal_eq
  case and => exact applyBinary_getBal_eq
  case or => exact applyBinary_getBal_eq
  case xor => exact applyBinary_getBal_eq
  case byte => intro h; simp only [Rinst.run, Rinst.runCore] at h; exact applyBinary_getBal_eq h
  case shr => intro h; simp only [Rinst.run, Rinst.runCore] at h; exact applyBinary_getBal_eq h
  case shl => intro h; simp only [Rinst.run, Rinst.runCore] at h; exact applyBinary_getBal_eq h
  case sar => intro h; simp only [Rinst.run, Rinst.runCore] at h; exact applyBinary_getBal_eq h
  case addmod => intro h; simp only [Rinst.run, Rinst.runCore] at h; exact applyTernary_getBal_eq h
  case mulmod => intro h; simp only [Rinst.run, Rinst.runCore] at h; exact applyTernary_getBal_eq h
  case iszero => intro h; simp only [Rinst.run, Rinst.runCore] at h; exact applyUnary_getBal_eq h
  case not => intro h; simp only [Rinst.run, Rinst.runCore] at h; exact applyUnary_getBal_eq h
  all_goals sorry
