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
  · exact burn.stack.symm ▸ popBurn.stack
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

lemma Ninst.getCode_eq_of_run'_some
    {pc sevm devm n sevm_ devm_ exn_ res}
    (run : Ninst.Run' pc sevm devm n (.some ⟨sevm_, devm_, exn_⟩) res) (a : Adr) :
    devm_.getCode a = devm.getCode a := by
  cases n
  case push xs lt =>
    contradiction
  case reg r =>
    contradiction
  case exec x =>
    sorry

lemma Ninst.code_eq_of_run'_some
    {pc sevm devm n sevm_ devm_ exn_ res}
    (run : Ninst.Run' pc sevm devm n (.some ⟨sevm_, devm_, exn_⟩) res) :
    sevm_.code = devm.getCode sevm_.currentTarget := by
  cases n
  case push xs lt =>
    contradiction
  case reg r =>
    contradiction
  case exec x =>
    sorry


lemma ExecuteCode.depth_eq
    {msg : Msg} {sevm_ devm_ exn_ ex}
    (run : ExecuteCode msg (.some ⟨sevm_, devm_, exn_⟩) ex) :
    sevm_.depth = msg.depth := by sorry

lemma ProcessMessage.depth_eq
    {msg : Msg} {sevm_ devm_ exn_ ex}
    (run : ProcessMessage msg (.some ⟨sevm_, devm_, exn_⟩) ex) :
    sevm_.depth = msg.depth := by sorry

lemma ProcessCreateMessage.depth_eq
    {msg : Msg} {sevm_ devm_ exn_ ex}
    (run : ProcessCreateMessage msg (.some ⟨sevm_, devm_, exn_⟩) ex) :
    sevm_.depth = msg.depth := by sorry

lemma GenericCall.depth_lt
    {sevm devm msgCallGas value caller currentTarget target
      shouldTransferValue isStatic inputIndex inputSize
      outputIndex outputSize code disablePrecompiles}
    {sevm_ devm_ exn_ ex}
    (run : GenericCall sevm devm msgCallGas value caller currentTarget target
      shouldTransferValue isStatic inputIndex inputSize
      outputIndex outputSize code disablePrecompiles (.some ⟨sevm_, devm_, exn_⟩) ex) :
    sevm_.depth < sevm.depth := by sorry

lemma GenericCreate.depth_lt
    {sevm devm endowment
      newAddress memoryIndex memorySize}
    {sevm_ devm_ exn_ ex}
    (run : GenericCreate sevm devm endowment
      newAddress memoryIndex memorySize (.some ⟨sevm_, devm_, exn_⟩) ex) :
    sevm_.depth < sevm.depth := by sorry

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
    sevm_.depth < sevm.depth := by sorry

lemma Ninst.getCode_eq_of_run'_ok
    {pc sevm devm n xlot devm'}
    (run : Ninst.Run' pc sevm devm n xlot (.ok devm')) (a : Adr) :
    devm'.getCode a = devm.getCode a := by sorry

lemma Jinst.getCode_eq_of_run_ok
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
        simp only [h_gas_not, if_neg, Except.ok.injEq, Prod.mk.injEq] at run
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

lemma lift_core
    (ε : Exec.Pred)
    (π : Sevm → Devm → Devm → Prop)
    (analog : ∀ {sevm pre post} (ex : Exec 0 sevm pre (.ok post)), π sevm pre post → ε 0 sevm pre (.ok post) ex)
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
        rw [Ninst.getCode_eq_of_run'_some h_run ca]
        exact h_at_p.left
      have h2 : sevm_.currentTarget = ca → some sevm_.code.toList = Prog.compile p ∧ 0 = 0 := by
        intro h_ca
        rw [Ninst.code_eq_of_run'_some h_run, h_ca]
        exact ⟨h_at_p.left, rfl⟩
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
    · exact nextNoneRec h_at h_run ex_next h_ne (ih_next h_fa ⟨by rw [Ninst.getCode_eq_of_run'_ok h_run ca]; exact h_at_p.left, fun hc => (h_ne hc).elim⟩)
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
          rw [Ninst.getCode_eq_of_run'_some h_run ca]
          exact h_at_p.left
        have h2 : sevm_.currentTarget = ca → some sevm_.code.toList = Prog.compile p ∧ 0 = 0 := by
          intro h_ca
          rw [Ninst.code_eq_of_run'_some h_run, h_ca]
          exact ⟨h_at_p.left, rfl⟩
        exact h_sub_wkn ⟨h1, h2⟩
      · exact ih_next h_fa ⟨by rw [Ninst.getCode_eq_of_run'_ok h_run ca]; exact h_at_p.left, fun hc => (h_ne hc).elim⟩
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
    · exact jumpRec h_at h_run ex_next h_ne (ih_next h_fa ⟨by rw [Jinst.getCode_eq_of_run_ok h_run ca]; exact h_at_p.left, fun hc => (h_ne hc).elim⟩)
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
    (π : Sevm → Devm → Prop)
    ( with_depth_ind :
      ∀ {sevm pre post},
        Prog.Run sevm pre p post →
        sevm.currentTarget = ca →
        ( ∀ pc' sevm' pre' post',
            Exec pc' sevm' pre' (.ok post') →
            sevm'.depth < sevm.depth →
            Prog.At p ca pc' sevm' pre' →
            π sevm' pre' →
            π sevm' post' ) →
        π sevm pre →
        π sevm post )
    ( nextNone :
      ∀ {pc} {sevm} {pre} {n} {inter},
        n.At sevm.code pc →
        Ninst.Run' pc sevm pre n .none (.ok inter) →
        sevm.currentTarget ≠ ca →
        π sevm pre →
        π sevm inter )
    ( nextSome :
      ∀ {pc} {sevm} {pre} {n} {sevm'} {devm'} {exn'} {inter},
        n.At sevm.code pc →
        Ninst.Run' pc sevm pre n (.some ⟨sevm', devm', exn'⟩) (.ok inter) →
        sevm.currentTarget ≠ ca →
        π sevm pre →
        π sevm' devm' ∧ (ifOk (π sevm') exn' → π sevm inter) )
    ( jump :
      ∀ {pc} {sevm} {pre} {j} {pc'} {inter},
        j.At sevm.code pc →
        Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩) →
        sevm.currentTarget ≠ ca →
        π sevm pre →
        π sevm inter )
    ( last :
      ∀ {pc} {sevm} {pre} {l} {post},
        l.At sevm.code pc →
        Linst.Run sevm pre l (.ok post) →
        sevm.currentTarget ≠ ca →
        π sevm pre →
        π sevm post ) :
    ∀ pc sevm devm post,
      Exec pc sevm devm (.ok post) →
      Prog.At p ca pc sevm devm →
      π sevm devm →
      π sevm post := by
  apply @lift (fun sevm pre post => π sevm pre → π sevm post) ca p with_depth_ind
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

#exit

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
