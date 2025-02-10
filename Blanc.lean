import Lean.Data.Json
import Lean.Data.Json.Parser
import Lean.Data.HashSet
import «Blanc».Weth
import «Blanc».TestParse

@[extern "ecrecover_flag"]
opaque ecrecoverFlag : ByteArray → UInt8 → ByteArray → ByteArray

def ecrecover (h : B256) (v : Bool) (r : B256) (s : B256) : Option Adr :=
  let rsa : ByteArray := ⟨Array.mk (r.toB8L ++ s.toB8L)⟩
  let hsa : ByteArray := ⟨Array.mk h.toB8L⟩
  let ri : UInt8 := if v then 1 else 0
  match (ecrecoverFlag hsa ri rsa).toList with
  | [] => none
  | b :: pa =>
    if b = 0 ∨ pa.length ≠ 20
    then none
    else B8L.toAdr pa

abbrev NTB := Lean.RBMap (List B8) (List B8) (@List.compare _ ⟨B8.compareLows⟩)

def NTB.toStrings (s : NTB) : List String :=
  let kvs := s.toArray.toList
  let kvToStrings : B8L × B8L → List String :=
    λ nb => [s!"{B4L.toHex (nb.fst.map B8.lows)} : {nb.snd.toHex}"]
  fork "NTB" (kvs.map kvToStrings)

def hpAux : B8L → (Option B8 × B8L)
  | [] => ⟨none, []⟩
  | n :: ns =>
    match hpAux ns with
    | ⟨none, bs⟩ => ⟨some n, bs⟩
    | ⟨some m, bs⟩ => ⟨none, ((n <<< 4) ||| m.lows) :: bs⟩

def hp (ns : B8L) (t : Bool) : B8L :=
  match hpAux ns with
  | ⟨none, bs⟩ => (cond t (0x20) 0) :: bs
  | ⟨some n, bs⟩ => ((cond t 0x30 0x10) ||| n.lows) :: bs

def commonPrefixCore : B8L → B8L → B8L
  | [], _ => []
  | _, [] => []
  | n :: ns, n' :: ns' =>
    if n = n' then n :: commonPrefixCore ns ns'
    else []

def commonPrefix (n : B8) (ns : B8L) : List B8L → Option B8L
  | [] => some (n :: ns)
  | ns' :: nss =>
    match commonPrefixCore (n :: ns) ns' with
    | [] => none
    | (n' :: ns'') => commonPrefix n' ns'' nss

def NTB.empty : NTB := Lean.RBMap.empty

def sansPrefix : B8L → B8L → Option B8L
  | [], ns => some ns
  | _, [] => none
  | n :: ns, n' :: ns' =>
    if n = n' then sansPrefix ns ns' else none

def insertSansPrefix (pfx : B8L) (m : NTB) (ns : B8L) (bs : B8L) : Option NTB := do
  (m.insert · bs) <$> sansPrefix pfx ns

def NTB.factor (m : NTB) : Option (B8L × NTB) := do
  let ((n :: ns) :: nss) ← some (m.toList.map Prod.fst) | none
  let pfx ← commonPrefix n ns nss
  let m' ← Lean.RBMap.foldM (insertSansPrefix pfx) NTB.empty m
  some ⟨pfx, m'⟩

structure NTBs : Type where
  (x0 : NTB) (x1 : NTB) (x2 : NTB) (x3 : NTB)
  (x4 : NTB) (x5 : NTB) (x6 : NTB) (x7 : NTB)
  (x8 : NTB) (x9 : NTB) (xA : NTB) (xB : NTB)
  (xC : NTB) (xD : NTB) (xE : NTB) (xF : NTB)

def NTBs.empty : NTBs :=
  ⟨ .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty ⟩

def NTBs.update (js : NTBs) (f : NTB → NTB) (k : B8) : NTBs :=
  match k.toBools with
  | ⟨_, _, _, _, 0, 0, 0, 0⟩ => { js with x0 := f js.x0}
  | ⟨_, _, _, _, 0, 0, 0, 1⟩ => { js with x1 := f js.x1}
  | ⟨_, _, _, _, 0, 0, 1, 0⟩ => { js with x2 := f js.x2}
  | ⟨_, _, _, _, 0, 0, 1, 1⟩ => { js with x3 := f js.x3}
  | ⟨_, _, _, _, 0, 1, 0, 0⟩ => { js with x4 := f js.x4}
  | ⟨_, _, _, _, 0, 1, 0, 1⟩ => { js with x5 := f js.x5}
  | ⟨_, _, _, _, 0, 1, 1, 0⟩ => { js with x6 := f js.x6}
  | ⟨_, _, _, _, 0, 1, 1, 1⟩ => { js with x7 := f js.x7}
  | ⟨_, _, _, _, 1, 0, 0, 0⟩ => { js with x8 := f js.x8}
  | ⟨_, _, _, _, 1, 0, 0, 1⟩ => { js with x9 := f js.x9}
  | ⟨_, _, _, _, 1, 0, 1, 0⟩ => { js with xA := f js.xA}
  | ⟨_, _, _, _, 1, 0, 1, 1⟩ => { js with xB := f js.xB}
  | ⟨_, _, _, _, 1, 1, 0, 0⟩ => { js with xC := f js.xC}
  | ⟨_, _, _, _, 1, 1, 0, 1⟩ => { js with xD := f js.xD}
  | ⟨_, _, _, _, 1, 1, 1, 0⟩ => { js with xE := f js.xE}
  | ⟨_, _, _, _, 1, 1, 1, 1⟩ => { js with xF := f js.xF}

def NTBs.insert (js : NTBs) : B8L → B8L → NTBs
  | [], _ => js
  | n :: ns, bs => js.update (Lean.RBMap.insert · ns bs) n

mutual
  def nodeComp : Nat → NTB → RLP'
    | 0, _ => .b8s []
    | k + 1, j =>
      if j.isEmpty
      then .b8s []
      else let r := structComp k j
           if r.encode.length < 32
           then r
           else .b8s <| r.encode.keccak.toB8L

  def structComp : Nat → NTB → RLP'
    | 0, _ => .b8s []
    | k + 1, j =>
      if j.isEmpty
      -- then .list (.replicate 17 <| .bytes []) -- what should be returned
      then .b8s [] -- what devtools actually return
      else if j.isSingleton
           then match j.toList with
                | [(k, v)] => .list [.b8s (hp k 1), .b8s v]
                | _ => .b8s [] -- unreachable code
           else match j.factor with
                | none =>
                  let js := Lean.RBMap.fold NTBs.insert NTBs.empty j
                  .list [ nodeComp k js.x0, nodeComp k js.x1, nodeComp k js.x2,
                          nodeComp k js.x3, nodeComp k js.x4, nodeComp k js.x5,
                          nodeComp k js.x6, nodeComp k js.x7, nodeComp k js.x8,
                          nodeComp k js.x9, nodeComp k js.xA, nodeComp k js.xB,
                          nodeComp k js.xC, nodeComp k js.xD, nodeComp k js.xE,
                          nodeComp k js.xF, .b8s (j.findD [] []) ]
                | some (pfx, j') => .list [.b8s (hp pfx 0), nodeComp k j']
end

def List.maxD {ξ} [Max ξ] : List ξ → ξ → ξ
  | [], y => y
  | x :: xs, y => maxD xs (max x y)

def NTB.maxKeyLength (j : NTB) : Nat := (j.toList.map (List.length ∘ Prod.fst)).maxD 0

def collapse (j : NTB) : RLP' := structComp (2 * (j.maxKeyLength + 1)) j

def trie (j : NTB) : B256 :=
  let bs := (collapse j).encode
  bs.keccak


def B256.keccak (x : B256) : B256 := B8L.keccak <| x.toB8L
def B256.toRLP (w : B256) : RLP' := .b8s w.toB8L

def B8L.sig (bs : B8L) : B8L := List.dropWhile (· = 0) bs

def Stor.toNTB (s : Stor) : NTB :=
  let f : NTB → B256 → B256 → NTB :=
    λ j k v =>
      j.insert
        k.keccak.toB4s
        ((RLP'.encode <| .b8s <| B8L.sig <| v.toB8L))
  Lean.RBMap.fold f NTB.empty s

def B256.zerocount (x : B256) : Nat → Nat
  | 0 => 0
  | k + 1 => if x = 0 then k + 1 else B256.zerocount (x >>> 8) k

def B256.bytecount (x : B256) : Nat := 32 - (B256.zerocount x 32)

def Acct.toVal (a : Acct) (w : B256) : B8L :=
  RLP'.encode <| .list [
    .b8s a.nonce.toB8L.sig,
    .b8s a.bal.toB8L.sig,
    B256.toRLP w,
    B256.toRLP <| ByteArray.keccak 0 a.code.size a.code
  ]

def toKeyVal (pr : Adr × Acct) : B8L × B8L :=
  let ad := pr.fst
  let ac := pr.snd
  ⟨
    let key' := ad.toB8L.keccak.toB4s
    key',
    let val' :=
      RLP'.encode <| .list [
        .b8s (ac.nonce.toB8L.sig), --a.nonce,
        .b8s (ac.bal.toB8L.sig), --a.bal,
        B256.toRLP (trie ac.stor.toNTB),
        B256.toRLP <| (B8L.keccak ac.code.toList)
      ]
    val'
  ⟩

-- values --

def gHigh : Nat := 10
def gJumpdest : Nat := 1
def gTxcreate : Nat := 32000
def gAccesslistaddress : Nat := 2400
def gAccessliststorage : Nat := 1900
def gInitcodeword : Nat := 2
def gBase : Nat := 2
def gCopy : Nat := 3
def gMemory : Nat := 3
def gKeccak256 : Nat := 30
def gKeccak256Word : Nat := 6
def cMem (a : Nat) := gMemory * a + ((a ^ 2) / 512)
-- def gZero : Nat := 0
def gVerylow : Nat := 3
def gLow : Nat := 5
def gMid : Nat := 8
def gExp : Nat := 10
def gExpbyte : Nat := 50
def gColdSLoad : Nat := 2100
def gSSet : Nat := 20000
def gSReset : Nat := 2900
def rSClear : Nat := 4800
def gTransaction : Nat := 21000

def initCodeCost (cd : B8L) : Nat :=
  gInitcodeword * ((cd.length / 32) + if 32 ∣ cd.length then 0 else 1)

instance {a b : Adr} : Decidable (a = b) := by
  cases a; cases b; simp; apply instDecidableAnd

instance : Hashable Adr := ⟨Adr.low⟩
instance : Hashable (Adr × B256) := ⟨λ x => x.1.low⟩

abbrev AdrSet : Type := @Std.HashSet Adr _ _
abbrev KeySet : Type := @Std.HashSet (Adr × B256) _ _

def Sta : Type := Array B256 × Nat
def Mem : Type := Array B8

structure Acs where
  (dest : List Adr)  -- A_s
  (adrs : AdrSet)    -- A_a
  (keys : KeySet)     -- A_k
  (ref : Nat)         -- A_r
  (logs : List RLP')  -- A_l
  (tchd : AdrSet) -- A_t

structure Var where
  (gas : Nat) -- μ_g
  (pc : Nat)  -- μ_pc
  (ret : B8L) -- μ_o
  (act : Nat) -- μ_i
  -------------------------
  (dest : List Adr)  -- A_s
  (adrs : AdrSet)    -- A_a
  (keys : KeySet)     -- A_k
  (ref : Nat)         -- A_r
  (logs : List RLP')  -- A_l
  (tchd : AdrSet) -- A_t

def Var.toAcs (υ : Var) : Acs :=
  {
    dest := υ.dest
    adrs := υ.adrs
    keys := υ.keys
    ref := υ.ref
    logs := υ.logs
    tchd := υ.tchd
  }


-- μ_i : no need to make it a separate field of Machine,
-- when it is completely determined by Machine.mem
def Mem.msz (μ : Mem) : Nat := ceilDiv μ.size 32

structure Block where
  (baseFee : B256) -- H_f
  (ben : Adr) -- H_c
  (prevRandao : B256) -- H_a
  (gasLimit : B256) -- H_l
  (timestamp : B256) -- H_s
  (number : B256) -- H_s
  (chainId : B256) -- β

structure Con where
  (blk : Block) -- block (YP : H)
  (wor0 : Wor)

  (cta : Adr) -- contract address (YP : I_a)
  (oga : Adr) -- origin address (YP : I_o)
  (gpr : B256) -- gas price (YP : I_p)
  (cld : B8L) -- calldata (YP : I_d)
  (cla : Adr) -- caller Addr (YP : I_s)
  (clv : B256) -- callvalue (YP : I_v)
  (code : ByteArray) -- contract code  (YP : I_b)
  (exd : Nat) -- execution depth (YP : I_e)
  (wup : Bool) -- World-State update permission (YP : I_w)

-- YP says that this type should also have a field for
-- execution environment, but it was omitted since the
-- environment does not change and is already known.
structure Ξ.Result where
  (wor : Option Wor)
  (gas : Nat)
  (acs : Acs)
  (ret : Option B8L)

inductive Inst : Type
  | last : Linst → Inst
  | next : Ninst → Inst
  | jump : Jinst → Inst

lemma List.length_takeD {ξ : Type u} (n : Nat) (xs : List ξ) (x : ξ) :
    (List.takeD n xs x).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [takeD]

def Jinst.toString : Jinst → String
  | .jump => "JUMP"
  | .jumpdest => "JUMPDEST"
  | .jumpi => "JUMPI"

def Inst.toString : Inst → String
  | .next n => n.toString
  | .jump j => j.toString
  | .last l => l.toString

def noPushBefore' (cd : ByteArray) : Nat → Nat → Bool
  | 0, _ => true
  | _, 0 => true
  | k + 1, m + 1 =>
    if k < cd.size
    then let b := cd.get! k
         if (b < (0x7F - m.toUInt8) || 0x7F < b)
         then noPushBefore' cd k m
         else if noPushBefore' cd k 32
              then false
              else noPushBefore' cd k m
    else noPushBefore' cd k m

def noPushBefore (cd : Array B8) : Nat → Nat → Bool
  | 0, _ => true
  | _, 0 => true
  | k + 1, m + 1 =>
    match cd.get? k with
    | none => noPushBefore cd k m
    | some b =>
      if (b < (0x7F - m.toUInt8) || 0x7F < b)
      then noPushBefore cd k m
      else if noPushBefore cd k 32
           then false
           else noPushBefore cd k m


def jumpable' (cd : ByteArray) (k : Nat) : Bool :=
  if cd.get! k = (Jinst.toB8 .jumpdest)
  then noPushBefore' cd k 32
  else false

def jumpable (cd : Array B8) (k : Nat) : Bool :=
  if cd.get? k = some (Jinst.toB8 .jumpdest)
  then noPushBefore cd k 32
  else false

inductive Ninst' : Type
  | reg : Rinst → Ninst'
  | exec : Xinst → Ninst'
  | push : B256 → Nat →  Ninst' --∀ bs : B8L, bs.length ≤ 32 → Ninst'

inductive Inst' : Type
  | last : Linst → Inst'
  | next : Ninst' → Inst'
  | jump : Jinst → Inst'

def getInstAux (cd : ByteArray) (pc len off : Nat) : B8 :=
  if off < len
  then cd.get! ((pc + len) - off)
  else 0

def getInst (υ : Var) (κ : Con)  : Option Inst' :=
  if υ.pc < κ.code.size
  then
    let b : B8 := κ.code.get! υ.pc
    (b.toRinst <&> (.next ∘ .reg)) <|>
    (b.toXinst <&> (.next ∘ .exec)) <|>
    (b.toJinst <&> .jump) <|>
    (b.toLinst <&> .last) <|>
    (
      let bn := b.toNat
      if 95 ≤ bn ∧ bn ≤ 127
      then let len := bn - 95
           let x : B256 :=
             B8s.toB256
               (getInstAux κ.code υ.pc len 31)
               (getInstAux κ.code υ.pc len 30)
               (getInstAux κ.code υ.pc len 29)
               (getInstAux κ.code υ.pc len 28)
               (getInstAux κ.code υ.pc len 27)
               (getInstAux κ.code υ.pc len 26)
               (getInstAux κ.code υ.pc len 25)
               (getInstAux κ.code υ.pc len 24)
               (getInstAux κ.code υ.pc len 23)
               (getInstAux κ.code υ.pc len 22)
               (getInstAux κ.code υ.pc len 21)
               (getInstAux κ.code υ.pc len 20)
               (getInstAux κ.code υ.pc len 19)
               (getInstAux κ.code υ.pc len 18)
               (getInstAux κ.code υ.pc len 17)
               (getInstAux κ.code υ.pc len 16)
               (getInstAux κ.code υ.pc len 15)
               (getInstAux κ.code υ.pc len 14)
               (getInstAux κ.code υ.pc len 13)
               (getInstAux κ.code υ.pc len 12)
               (getInstAux κ.code υ.pc len 11)
               (getInstAux κ.code υ.pc len 10)
               (getInstAux κ.code υ.pc len  9)
               (getInstAux κ.code υ.pc len  8)
               (getInstAux κ.code υ.pc len  7)
               (getInstAux κ.code υ.pc len  6)
               (getInstAux κ.code υ.pc len  5)
               (getInstAux κ.code υ.pc len  4)
               (getInstAux κ.code υ.pc len  3)
               (getInstAux κ.code υ.pc len  2)
               (getInstAux κ.code υ.pc len  1)
               (getInstAux κ.code υ.pc len  0)
           some (.next <| .push x len)
      else none
    )
  else some (.last .stop)


def safeSub {ξ} [Sub ξ] [LE ξ] [@DecidableRel ξ (· ≤ ·)] (x y : ξ) : Option ξ :=
  if y ≤ x then some (x - y) else none

def deductGas (υ : Var) (c : Nat) : Option Nat := safeSub υ.gas c

def Acct.Empty (a : Acct) : Prop :=
  a.code.size = 0 ∧ a.nonce = 0 ∧ a.bal = 0

def Dead (w : Wor) (a : Adr) : Prop :=
  match w.find? a with
  | none => True
  | some x => x.Empty

def Wor.balAt (w : Wor) (a : Adr) : B256 :=
  match w.find? a with
  | none => 0
  | some x => x.bal

def gNewAccount : Nat := 25000
def gCallValue : Nat := 9000
def gCallStipend : Nat := 2300
def gWarmAccess : Nat := 100
def gColdAccountAccess : Nat := 2600
def gSelfdestruct : Nat := 5000
def gLog : Nat := 375
def gLogdata : Nat := 8
def gLogtopic : Nat := 375

instance {w a} : Decidable (Dead w a) := by
  simp [Dead]
  cases (Lean.RBMap.find? w a)
  · simp; apply instDecidableTrue
  · simp [Acct.Empty]; apply instDecidableAnd

def cAAccess (x : Adr) (a : AdrSet) : Nat :=
  if x ∈ a then gWarmAccess else gColdAccountAccess

def except64th (n : Nat) : Nat := n - (n / 64)

def cExtra (ω : Wor) (υ : Var) (t : Adr) (v : B256) : Nat :=
  let cAcc : Nat := cAAccess t υ.adrs
  let cNew : Nat := if (Dead ω t ∧ v ≠ 0) then gNewAccount else 0
  let cXfer : Nat := if v ≠ 0 then gCallValue else 0
  (cAcc + cXfer + cNew)

def cGasCap (ω : Wor) (υ : Var) (g : Nat)
    (memCost : Nat) (t : Adr) (v : B256) : Nat :=
  if (memCost + cExtra ω υ t v) ≤ υ.gas
  then min (except64th (υ.gas - (memCost + cExtra ω υ t v))) g
  else g

def cCallGas (ω : Wor) (υ : Var)
   (g : Nat) (memCost : Nat) (t : Adr) (v : B256) : Nat :=
  if v ≠ 0
  then cGasCap ω υ g memCost t v + gCallStipend
  else cGasCap ω υ g memCost t v

def cCall (ω : Wor) (υ : Var)
    (g : Nat) (memCost : Nat) (t : Adr) (v : B256) : Nat :=
  cGasCap ω υ g memCost t v + cExtra ω υ t v

structure theta.Result : Type where
  (wor : Wor)
  (gas : Nat)
  (acs : Acs)
  (status : Bool)
  (ret : B8L)

def Wor.code (w : Wor) (a : Adr) : ByteArray :=
  match w.find? a with
  | none => ByteArray.mk #[]
  | some x => x.code

def Acct.empty : Acct :=
  {
    nonce := 0
    bal := 0
    stor := .empty
    code := ByteArray.mk #[]
  }

def Sta.init : Sta := ⟨Array.mkArray 1024 (0 : B256), 0⟩

-- need further update for precompiled contracts
def θ.prep
  (ω₀ : Wor)
  (H : Block)
  (ω : Wor)
  (A : Acs)
  (s : Adr)
  (o : Adr)
  (r : Adr)
  (c : Adr)
  (g : Nat)
  (p : Nat)
  (v : B256)
  (v_app : B256)
  (d : B8L)
  (e : Nat)
  (w : Bool) :
  Wor × Sta × Mem × Var × Con :=
  let ω'₁ : Wor :=
    match ω.find? r with
    | none =>
      if v = 0
      then ω
      else ω.insert r {nonce := 0, bal := v, stor := .empty, code := ByteArray.mk #[]}
    | some aᵣ => ω.insert r {aᵣ with bal := aᵣ.bal + v}
  let ω₁ : Wor :=
    match ω'₁.find? s with
    | none =>
      if v = 0
      then ω'₁
      else (dbg_trace "unreachable code : nonzero value calls from empty accounts should never happen" ; ω'₁)
    | some aₛ => ω'₁.insert s {aₛ with bal := aₛ.bal - v}
  let cd : ByteArray := ω.code c
  let κ : Con := {
    wor0 := ω₀
    cta := r, oga := o, gpr := p.toB256, cld := d
    cla := s, clv := v_app, code := cd, blk := H, exd := e, wup := w
  }
  let υ : Var := {
    gas := g, pc := 0, ret := [], act := 0
    dest := A.dest, adrs := A.adrs, keys := A.keys,
    ref := A.ref, logs := A.logs, tchd := A.tchd
  }
  ⟨ω₁, .init, #[], υ, κ⟩

def θ.wrap (wor : Wor) (acs : Acs) (Ξr : Ξ.Result) : theta.Result :=
  let ω_stars : Option Wor := Ξr.wor
  let g_stars : Nat := Ξr.gas
  let A_stars : Acs := Ξr.acs
  let o : Option B8L := Ξr.ret
  let ω' : Wor := ω_stars.getD wor
  let g' : Nat :=
    if ω_stars.isNone ∧ o.isNone
    then (dbg_trace "EXCEPTIONAL HALTING STATE"; 0)
    else g_stars
  let A' : Acs := if ω_stars.isNone then acs else A_stars
  let z : Bool := if ω_stars.isNone then 0 else 1

  -- o' is not from YP, but necessary to cast from 'Option B8L to 'B8L'
  -- (YP is a bit sloppy with types here)
  let o' : B8L := o.getD []
  ⟨ω', g', A', z, o'⟩



def dataGas (cd : B8L) : Nat :=
  let aux : B8 → Nat := fun b => if b = 0 then 4 else 16
  (cd.map aux).sum


def intrinsicGas (Rcv : Option Adr) (cd : B8L) (Ta : List (Adr × List B256)) : Nat :=
  let aux : (Adr × List B256) → Nat :=
    fun | ⟨_, l⟩ => gAccesslistaddress + (gAccessliststorage * l.length)
  dataGas cd +
  Rcv.rec (gTxcreate + initCodeCost cd) (fun _ => 0) +
  gTransaction +
  (Ta.map aux).sum

def Wor.transfer? (wor : Wor) (src : Adr) (clv : B256) (dst : Adr) : Option Wor := do
  let src_acct ← wor.find? src
  let dst_acct ← wor.find? dst
  let new_src_bal ← safeSub src_acct.bal clv
  let wor' := wor.insert src {src_acct with bal := new_src_bal}
  return wor'.insert dst {dst_acct with bal := dst_acct.bal + clv}

-- checkpoint is an 'Option' type because computation of checkpoints
-- may fail for invalid txs. this is *not* the case for any subsequent
-- steps of a tx: once you get to a checkpoint, the tx *always* goes
-- through and yields a new state. i.e., there is no invalid tx that
-- has a checkpoint.
def checkpoint (w : Wor) (ad : Adr) (v : B256) : Option Wor := do
  let ac ← w.find? ad
  let bal' ← safeSub ac.bal v
  some <| w.insert ad {ac with bal := bal', nonce := ac.nonce + 1}

def Adr.toNat (x : Adr) : Nat :=
  x.high.toNat * (2 ^ 128) +
  x.mid.toNat * (2 ^ 64) +
  x.low.toNat

def Nat.toAdr (n : Nat) : Adr :=
  let h := n / (2 ^ 128)
  let r := n % (2 ^ 128)
  let m := r / (2 ^ 64)
  let l := r % (2 ^ 64)
  {
    high := h.toUInt32
    mid  := m.toUInt64
    low  := l.toUInt64
  }

instance {n} : OfNat Adr n := ⟨n.toAdr⟩

-- A^0
def Acs.init : Acs :=
  {
    dest := []
    adrs := .ofList [1, 2, 3, 4, 5, 6, 7, 8, 9] -- precompiled contracts
    keys := .empty
    ref := 0
    logs := []
    tchd := .empty
  }

abbrev AccessList : Type := List (Adr × List B256)

abbrev AccessList.collect (al : AccessList) : KeySet :=
  let addPair : Adr → KeySet → B256 → KeySet :=
    fun a aks k => aks.insert ⟨a, k⟩
  let addElem : KeySet → Adr × List B256 → KeySet :=
    fun aks pr => List.foldl (addPair pr.fst) aks pr.snd
  List.foldl addElem .empty al

def A_star (H : Block) (ST : Adr) (Tt : Option Adr) (TA : AccessList) : Acs :=
  let a : AdrSet :=
    Acs.init.adrs.insertMany
      (Std.HashSet.ofList (ST :: H.ben :: TA.map Prod.fst))
  {
    Acs.init with
    adrs := Tt.rec a (a.insert)
    keys := TA.collect
  }

def Stor.insertNonzero (s : Stor) (k v : B256) : Stor :=
  if v = 0 then s.erase k else s.insert k v

def Sta.pop1 : Sta → Option (B256 × Sta)
  | ⟨xs, n + 1⟩ => do
    let x ← xs.get? n
    some ⟨x, xs, n⟩
  | _ => none

def Sta.pop2 : Sta → Option (B256 × B256 × Sta)
  | ⟨xs, n + 2⟩ => do
    let x ← xs.get? (n + 1)
    let y ← xs.get? n
    some ⟨x, y, xs, n⟩
  | _ => none

def Sta.pop3 : Sta → Option (B256 × B256 × B256 × Sta)
  | ⟨xs, n + 3⟩ => do
    let x ← xs.get? (n + 2)
    let y ← xs.get? (n + 1)
    let z ← xs.get? n
    some ⟨x, y, z, xs, n⟩
  | _ => none

def Sta.pop4 : Sta → Option (B256 × B256 × B256 × B256 × Sta)
  | ⟨xs, n + 4⟩ => do
    let a ← xs.get? (n + 3)
    let b ← xs.get? (n + 2)
    let c ← xs.get? (n + 1)
    let d ← xs.get? n
    some ⟨a, b, c, d, xs, n⟩
  | _ => none

def Sta.pop5 : Sta → Option (B256 × B256 × B256 × B256 × B256 × Sta)
  | ⟨xs, n + 5⟩ => do
    let a ← xs.get? (n + 4)
    let b ← xs.get? (n + 3)
    let c ← xs.get? (n + 2)
    let d ← xs.get? (n + 1)
    let e ← xs.get? n
    some ⟨a, b, c, d, e, xs, n⟩
  | _ => none

def Sta.pop6 : Sta → Option (B256 × B256 × B256 × B256 × B256 × B256 × Sta)
  | ⟨xs, n + 6⟩ => do
    let a ← xs.get? (n + 5)
    let b ← xs.get? (n + 4)
    let c ← xs.get? (n + 3)
    let d ← xs.get? (n + 2)
    let e ← xs.get? (n + 1)
    let f ← xs.get? n
    some ⟨a, b, c, d, e, f, xs, n⟩
  | _ => none

def Sta.pop7 : Sta → Option (B256 × B256 × B256 × B256 × B256 × B256 × B256 × Sta)
  | ⟨xs, n + 7⟩ => do
    let a ← xs.get? (n + 6)
    let b ← xs.get? (n + 5)
    let c ← xs.get? (n + 4)
    let d ← xs.get? (n + 3)
    let e ← xs.get? (n + 2)
    let f ← xs.get? (n + 1)
    let g ← xs.get? n
    some ⟨a, b, c, d, e, f, g, xs, n⟩
  | _ => none

def Sta.push1 : Sta → B256 → Option Sta
  | ⟨xs, n⟩, x => do
    guard (n < 1024)
    some ⟨xs.set! n x, n + 1⟩

def Sta.push2 : Sta → B256 → B256 → Option Sta
  | ⟨xs, n⟩, x, y => do
    guard (n < 1023)
    let xs' := xs.set! n y
    some ⟨xs'.set! (n + 1) x, n + 2⟩

def Sta.push3 : Sta → B256 → B256 → B256 → Option Sta
  | ⟨xs, n⟩, x, y, z => do
    guard (n < 1022)
    let xs' := xs.set! n z
    let xs'' := xs'.set! (n + 1) y
    some ⟨xs''.set! (n + 2) x, n + 3⟩

def Sta.popN (s : Sta ) : Nat → Option (List B256 × Sta)
  | 0 => some ⟨[], s⟩
  | n + 1 => do
    let (x, s') ← s.pop1
    let (xs, s'') ← s'.popN n
    some ⟨x :: xs, s''⟩

def sstoreStep (ω : Wor) (σ : Sta) (υ : Var) (κ : Con) :
    Option (Wor × Sta ×  Var) := do
  let (x, v', σ') ← σ.pop2
  let (a₀ : Acct) ← κ.wor0.find? κ.cta
  let (v₀ : B256) := ((a₀.stor.find? x).getD 0)
  let (a : Acct) ← ω.find? κ.cta
  let (v : B256) := ((a.stor.find? x).getD 0)
  let c₀ : Nat := cond (υ.keys.contains ⟨κ.cta, x⟩) 0 gColdSLoad
  let c₁ : Nat :=
    if v = v' ∨ v₀ ≠ v
    then gWarmAccess
    else if v₀ = 0
         then gSSet
         else gSReset
  let c : Nat := c₀ + c₁
  let rDirtyClear : Int :=
    if v₀ ≠ 0 ∧ v = 0
    then (- rSClear)
    else if v₀ ≠ 0 ∧ v' = 0
         then rSClear
         else 0
  let rDirtyReset : Int :=
    if v₀ = v'
    then if v₀ = 0
         then gSSet - gWarmAccess
         else gSReset - gWarmAccess
    else 0
  let r : Int :=
    if v = v'
    then 0
    else if v₀ = v
         then if v' = 0
              then rSClear
              else 0
         else rDirtyClear + rDirtyReset
  let g' ← safeSub υ.gas c
  let ref' ← (Int.ofNat υ.ref + r).toNat'
  let a' : Acct := {a with stor := a.stor.insertNonzero x v'}

  some
    ⟨
      ω.insert κ.cta a',
      σ',
      {
        υ with
        gas := g'
        pc := υ.pc + 1
        keys := υ.keys.insert ⟨κ.cta, x⟩
        ref := ref'
      }
    ⟩


def memExp (s : Nat) (f l : B256) : Nat :=
  if l = 0
  then s
  else max s (ceilDiv (f.toNat + l.toNat) 32)



def nextState (υ : Var) (cost : Nat)
  (act' : Option Nat := none)
  (ret' : B8L := υ.ret)
  (adrs' : AdrSet := υ.adrs)
  (logs' : List RLP' := υ.logs)
  (keys' : KeySet := υ.keys) : Option Var := do
  --let memCost : Nat := cMem act' - cMem υ.act
  let gas' ←
    match act' with
    | none => deductGas υ cost
    | some k => deductGas υ (cost + (cMem k - cMem υ.act))
  some {
      gas := gas',
      pc := υ.pc + 1,
      ret := ret'
      act := act'.getD υ.act
      dest := υ.dest
      adrs := adrs'
      keys := keys'
      ref := υ.ref
      logs := logs'
      tchd := υ.tchd
    }

def Wor.get (w : Wor) (a : Adr) : Acct := (w.find? a).getD .empty

def Sta.toStringsCore (xs : Array B256) : Nat → List String
  | 0 => []
  | n + 1 => ("0x" ++ (xs.getD n 0).toHex) :: Sta.toStringsCore xs n

def Sta.toStrings : Sta → List String
  | ⟨xs, n⟩ => Sta.toStringsCore xs n

def Sta.toString (s : Sta) : String := String.joinln s.toStrings

def Sta.swap : Sta → Nat → Option Sta
  | ⟨xs, n + 2⟩, k =>
    if n < k
    then none
    else some ⟨xs.swap! (n + 1) (n - k), n + 2⟩
  | _, _ => none

def Sta.dup : Sta → Nat → Option Sta
  | ⟨xs, n⟩, k =>
    if n < k + 1
    then none
    else do let x ← xs.get? (n - (k + 1))
            Sta.push1 ⟨xs, n⟩ x


def pushItem (σ : Sta) (μ : Mem) (υ : Var) (x : B256) (c : Nat) :
    Option (Sta × Mem × Var) := do
  let σ' ← σ.push1 x
  let υ' ← nextState υ c
  some ⟨σ', μ, υ'⟩

def checkRemGas (υ : Var) (cost : Nat) (act' : Nat) : Option Unit := do
  let memCost : Nat := cMem act' - cMem υ.act
  let _ ← deductGas υ (cost + memCost)
  return ()

def applyUnary (σ : Sta) (μ : Mem) (υ : Var) (f : B256 → B256) (cost : Nat) :
    Option (Sta × Mem × Var) := do
  let (x, σ') ← σ.pop1
  let σ'' ← σ'.push1 (f x)
  let υ' ← nextState υ cost
  some ⟨σ'', μ, υ'⟩

def applyBinary (σ : Sta) (μ : Mem) (υ : Var) (f : B256 → B256 → B256) (cost : Nat) :
    Option (Sta × Mem × Var) := do
  let (x, y, σ') ← σ.pop2
  let σ'' ← σ'.push1 (f x y)
  let υ' ← nextState υ cost
  some ⟨σ'', μ, υ'⟩

def applyTernary (σ : Sta) (μ : Mem) (υ : Var) (f : B256 → B256 → B256 → B256) (cost : Nat) :
    Option (Sta × Mem × Var) := do
  let (x, y, z, σ') ← σ.pop3
  let σ'' ← σ'.push1 (f x y z)
  let υ' ← nextState υ cost
  some ⟨σ'', μ, υ'⟩

def B256.toAdr : B256 → Adr
  | ⟨⟨_, x⟩, ⟨y, z⟩⟩ => {high := x.toUInt32, mid := y, low := z}

def Adr.toB256 (a : Adr) : B256 :=
  ⟨⟨0, a.high.toUInt64⟩ , ⟨a.mid, a.low⟩ ⟩

def Rinst.run (ω : Wor) (σ : Sta) (μ : Mem) (υ : Var) (κ : Con) :
    Rinst → Option (Sta × Mem × Var)
  | .address => pushItem σ μ υ κ.cta.toB256 gBase
  | .balance => do
    let (x, σ') ← σ.pop1
    let a := x.toAdr
    let adrs' : AdrSet := υ.adrs.insert a
    let σ'' ← σ'.push1 (ω.get a).bal
    let υ' ← nextState υ (cAAccess a υ.adrs) (adrs' := adrs')
    some ⟨σ'', μ, υ'⟩
  | .origin => pushItem σ μ υ κ.oga.toB256 gBase
  | .caller => pushItem σ μ υ κ.cla.toB256 gBase
  | .callvalue => pushItem σ μ υ κ.clv gBase
  | .calldataload => do
    let (x, σ') ← σ.pop1
    let cd  ← B8L.toB256? (κ.cld.sliceD x.toNat 32 0)
    -- dbg_trace s!"CALLDATA LOADED : {cd.toHex}"
    let σ'' ← σ'.push1 cd
    let υ' ← nextState υ gVerylow
    some ⟨σ'', μ, υ'⟩
  | .calldatasize => pushItem σ μ υ κ.cld.length.toB256 gBase
  | .calldatacopy => do
    let (x, y, z, σ') ← σ.pop3
    let bs : B8L := κ.cld.sliceD y.toNat z.toNat 0
    let υ' ←
      nextState υ
        (gVerylow + (gCopy * ceilDiv z.toNat 32))
        (act' := memExp υ.act x z)
    some ⟨σ', Array.writeX μ x.toNat bs 0, υ'⟩
  | .codesize => pushItem σ μ υ κ.code.size.toB256 gBase
  | .codecopy => do
    let (x, y, z, σ') ← σ.pop3
    let cost := gVerylow + (gCopy * ceilDiv z.toNat 32)
    let υ' ← nextState υ cost (act' := memExp υ.act x z)
    let bs := κ.code.sliceD y.toNat z.toNat (Linst.toB8 .stop)
    some ⟨σ', Array.writeX μ x.toNat bs 0, υ'⟩
  | .gasprice => pushItem σ μ υ κ.gpr gBase
  | .extcodesize => do
    let (x, σ') ← σ.pop1
    let a := x.toAdr
    let adrs' : AdrSet := υ.adrs.insert a
    let σ'' ← σ'.push1 (ω.get a).code.size.toB256
    let υ' ← nextState υ (cAAccess a υ.adrs) (adrs' := adrs')
    some ⟨σ'', μ, υ'⟩
  | .extcodecopy => do
    let (x, y, z, w, σ') ← σ.pop4
    let a := x.toAdr
    let cost := cAAccess x.toAdr υ.adrs + (gCopy * ceilDiv w.toNat 32)
    let adrs' : AdrSet := υ.adrs.insert a
    let υ' ← nextState υ cost (act' := memExp υ.act y w) (adrs' := adrs')
    let cd : ByteArray := (ω.get a).code
    let bs := cd.sliceD z.toNat w.toNat (Linst.toB8 .stop)
    -- dbg_trace s!"EXTCODECOPY SOURCE ADDRESS : {a.toHex}"
    -- dbg_trace s!"EXTCODECOPY VAL : {bs.toHex}"
    some ⟨σ', Array.writeX μ y.toNat bs 0, υ'⟩
  | .retdatasize => pushItem σ μ υ υ.ret.length.toB256 gBase
  | .retdatacopy => do
    let (x, y, z, σ') ← σ.pop3
    let act' := memExp υ.act x z
    let υ' ← nextState υ (gVerylow + (gCopy * (ceilDiv z.toNat 32))) (act' := act')
    let bs ← υ.ret.slice? y.toNat z.toNat
    some ⟨σ', Array.writeX μ x.toNat bs 0, υ'⟩
  | .extcodehash => do
    let (x, σ') ← σ.pop1
    let a := x.toAdr
    let adrs' := υ.adrs.insert a
    let υ' ← nextState υ (cAAccess a υ.adrs) (adrs' := adrs')
    let hash : B256 :=
      if (Dead ω a)
      then 0
      else let cd := (ω.get a).code
           ByteArray.keccak 0 cd.size cd
    let σ'' ← σ'.push1 hash
    some ⟨σ'', μ, υ'⟩
  | .selfbalance => pushItem σ μ υ (ω.get κ.cta).bal gLow
  | .chainid => pushItem σ μ υ κ.blk.chainId gBase
  | .number => pushItem σ μ υ κ.blk.number gBase
  | .timestamp => pushItem σ μ υ κ.blk.timestamp gBase
  | .gaslimit => pushItem σ μ υ κ.blk.gasLimit gBase
  | .prevrandao => pushItem σ μ υ κ.blk.prevRandao gBase
  | .coinbase => pushItem σ μ υ κ.blk.ben.toB256 gBase
  | .msize => pushItem σ μ υ (υ.act * 32).toB256 gBase
  | .mload => do
    let (x, σ') ← σ.pop1
    let act' := memExp υ.act x (32 : Nat).toB256
    let υ' ← nextState υ gVerylow (act' := act')
    let bs : B8L := μ.sliceD x.toNat 32 0
    let y : B256 ← B8L.toB256? bs
    let σ'' ← σ'.push1 y
    some ⟨σ'', μ, υ'⟩
  | .mstore => do
    let (x, y, σ') ← σ.pop2
    let act' := memExp υ.act x (32 : Nat).toB256
    let υ' ← nextState υ gVerylow (act' := act')
    -- dbg_trace s!"MSTORE LOC : {x.toHex}"
    -- dbg_trace s!"MSTORE VAL : {y.toHex}"
    some ⟨σ', Array.writeX μ x.toNat y.toB8L 0, υ'⟩
  | .mstore8 => do
    let (x, y, σ') ← σ.pop2
    let act' := memExp υ.act x 1
    let υ' ← nextState υ gVerylow (act' := act')
    some ⟨σ', Array.writeX μ x.toNat [y.2.2.toUInt8] 0, υ'⟩
  | .gas => pushItem σ μ υ (υ.gas - gBase).toB256 gBase
  | .eq => applyBinary σ μ υ .eq_check gVerylow
  | .lt => applyBinary σ μ υ .lt_check gVerylow
  | .gt => applyBinary σ μ υ .gt_check gVerylow
  | .slt => applyBinary σ μ υ .slt_check gVerylow
  | .sgt => applyBinary σ μ υ .sgt_check gVerylow
  | .iszero => applyUnary σ μ υ (.eq_check · 0) gVerylow
  | .not => applyUnary σ μ υ (~~~ ·) gVerylow
  | .and => applyBinary σ μ υ B256.and gVerylow
  | .or => applyBinary σ μ υ B256.or gVerylow
  | .xor => applyBinary σ μ υ B256.xor gVerylow
  | .signextend => applyBinary σ μ υ B256.signext gLow
  | .pop => do
    let (_, σ') ← σ.pop1
    let υ' ← nextState υ gBase
    some ⟨σ', μ, υ'⟩
  | .byte =>
    applyBinary σ μ υ (λ x y => (List.getD y.toB8L x.toNat 0).toB256) gVerylow
  | .shl => applyBinary σ μ υ (fun x y => y <<< x.toNat) gVerylow
  | .shr => applyBinary σ μ υ (fun x y => y >>> x.toNat) gVerylow
  | .sar => applyBinary σ μ υ (fun x y => B256.sar x.toNat y) gVerylow
  | .kec => do
    let (x, y, σ') ← σ.pop2
    let act' := memExp υ.act x y
    let cost := gKeccak256 + (gKeccak256Word * (ceilDiv y.toNat 32))
    let υ' ← nextState υ cost (act' := act')
    let σ'' ← σ'.push1 <| B8a.keccak x.toNat y.toNat μ
    some ⟨σ'', μ, υ'⟩
  | .sub => applyBinary σ μ υ (· - ·) gVerylow
  | .mul => applyBinary σ μ υ (· * ·) gLow
  | .exp => do
    let (x, y, σ') ← σ.pop2
    let cost := gExp + (gExpbyte * y.bytecount)
    let σ'' ← σ'.push1 (B256.bexp x y)
    let υ' ← nextState υ cost
    some ⟨σ'', μ, υ'⟩
  | .div => applyBinary σ μ υ (· / ·) gLow
  | .sdiv => applyBinary σ μ υ B256.sdiv gLow
  | .mod => applyBinary σ μ υ (· % ·) gLow
  | .smod => applyBinary σ μ υ B256.smod gLow
  | .add => applyBinary σ μ υ (· + ·) gVerylow
  | .addmod => applyTernary σ μ υ B256.addmod gMid
  | .mulmod => applyTernary σ μ υ B256.mulmod gMid
  | .swap n => do
    let σ' ← σ.swap n
    let υ' ← nextState υ gVerylow
    some ⟨σ', μ, υ'⟩
  | .dup n => do
    let σ' ← σ.dup n
    let υ' ← nextState υ gVerylow
    some ⟨σ', μ, υ'⟩
  | .sload => do
    let (x, σ') ← σ.pop1
    let cost : Nat := if υ.keys.contains ⟨κ.cta, x⟩ then gWarmAccess else gColdSLoad
    let ac ← ω.find? κ.cta
    let y := (ac.stor.find? x).getD 0
    let σ'' ← σ'.push1 y
    let υ' ← nextState υ cost (keys' := υ.keys.insert ⟨κ.cta, x⟩)
    some ⟨σ'', μ, υ'⟩
  | .pc => pushItem σ μ υ υ.pc.toB256 gBase
  | .log n => do
    --let (x, y, σ') ← σ.pop2
    let ⟨x :: y :: xs, σ'⟩ ← σ.popN (n + 2) | none
    let act' := memExp υ.act x y
    let cost := gLog + (gLogdata * y.toNat) + (n * gLogtopic)
    checkRemGas υ cost act'
    let bs : B8L := μ.sliceD x.toNat y.toNat 0
    let log : RLP' :=
      .list [
        .b8s κ.cta.toB8L,
        .list (xs.map B256.toRLP),
        .b8s bs
      ]
    let υ' ← nextState υ cost (act' := act') (logs' := log :: υ.logs)
    some ⟨σ', μ, υ'⟩
  | i => dbg_trace s!"UNIMPLEMENTED REGULAR INSTRUCTION EXECUTION : {i.toString}"; none


-- w₀ : the 'checkpoint' world saved at the preparation stage of tx

-- The intended behavior of 'execCore' is identical to the 'X' function of YP,
-- except that it returns 'none' if
--   (1) the VM is *CURRENTLY* (i.e, not at some later point in code) at
--       exceptional halting state due to the code byte that the program counter
--       points to, or
--   (2) recursion limit is reached (which should never happen with correct usage)

def Acct.isEmpty (ac : Acct) : Prop :=
  ac.nonce = 0 ∧
  ac.bal = 0 ∧
  ac.stor.isEmpty = .true ∧
  ac.code.size = 0

instance {ac : Acct} : Decidable ac.isEmpty := instDecidableAnd

def Wor.set (w : Wor) (a : Adr) (ac : Acct) : Wor :=
  if ac.isEmpty then w.erase a else w.insert a ac

def Wor.addBal (w : Wor) (a : Adr) (v : B256) : Wor :=
  let ac := w.get a
  let ac' : Acct := {ac with bal := ac.bal + v}
  w.set a ac'

def Wor.setBal (w : Wor) (a : Adr) (v : B256) : Wor :=
  let ac := w.get a
  let ac' : Acct := {ac with bal := v}
  w.set a ac'

def Jinst.run (σ : Sta) (υ : Var) (κ : Con) :
    Jinst → Option (Sta × Var)
  | .jumpdest => do
    let g' ← safeSub υ.gas gJumpdest
    some ⟨σ, {υ with gas := g', pc := υ.pc + 1}⟩
  | .jump => do
    let (loc, σ') ← σ.pop1
    let g' ← safeSub υ.gas gMid
    if jumpable' κ.code loc.toNat
    then some ⟨σ', {υ with gas := g', pc := loc.toNat}⟩
    else none
  | .jumpi => do
    let (loc, val, σ') ← σ.pop2
    let g' ← safeSub υ.gas gHigh
    if val = 0
    then some ⟨σ', {υ with gas := g', pc := υ.pc + 1}⟩
    else if jumpable' κ.code loc.toNat
         then some ⟨σ', {υ with gas := g', pc := loc.toNat}⟩
         else none

def Ninst'.run (ω : Wor) (σ : Sta) (μ : Mem) (υ : Var) (κ : Con) :
    Ninst' → Option (Wor × Sta × Mem × Var)
  | .push x len => do
    let g' ← safeSub υ.gas (if len = 0 then gBase else gVerylow)
    --let x ← B8L.toB256? <| List.ekatD 32 bs 0
    let σ' ← σ.push1 x
    let υ' := {υ with gas := g', pc := υ.pc + len + 1}
    some ⟨ω, σ', μ, υ'⟩
  | .reg (.sstore) => do
    let ⟨ω', σ', υ'⟩ ← sstoreStep ω σ υ κ --α ε
    some ⟨ω', σ', μ, υ'⟩
  | .reg r => do
    let ⟨μ', σ', α'⟩ ← Rinst.run ω σ μ υ κ r --α ε r
    some ⟨ω, μ', σ', α'⟩
  | .exec e => dbg_trace s!"unimplemented xinst : {e.toString}\n" ; none

def retRun (ω : Wor) (σ : Sta) (μ : Mem) (υ : Var) : Option Ξ.Result := do
  let (rlc, rsz, _) ← σ.pop2
  let act' : Nat := memExp υ.act rlc rsz
  let memCost : Nat := cMem act' - cMem υ.act
  let g' ← safeSub υ.gas memCost
  let r := μ.sliceD rlc.toNat rsz.toNat 0
  some {wor := ω, gas := g', acs := υ.toAcs, ret := r}

def xhs (υ : Var) : Ξ.Result :=
  {wor := none, gas := υ.gas, acs := υ.toAcs, ret := none}

structure theta.Cont : Type where
  (olc : B256)
  (osz : B256)
  (gas : Nat)
  (mem : Array B8)
  (pc : Nat)
  (sta : Sta)
  (act : Nat)

-- Wor × Sta × Mem × Var × Con
def theta.Result.toState (ct : theta.Cont) (tr : theta.Result) :
    Option (Wor × Sta × Mem × Var) := do
  let cpy : B8L := List.take ct.osz.toNat tr.ret
  let xs ← ct.sta.push1 (if tr.status then 1 else 0)
  let υ' : Var := {
    gas := ct.gas + tr.gas
    pc := ct.pc + 1
    ret := tr.ret
    act := ct.act
    dest := tr.acs.dest
    adrs := tr.acs.adrs
    keys := tr.acs.keys
    ref := tr.acs.ref
    logs := tr.acs.logs
    tchd := tr.acs.tchd
  }
  some ⟨tr.wor, xs, Array.writeX ct.mem ct.olc.toNat cpy 0, υ'⟩


@[inline] def Char.isEq (c c' : Char) : Bool := c == c'

@[inline] def Substring.trimLeftChar (s : Substring) (c : Char) : Substring :=
  s.dropWhile (Char.isEq c)

@[inline] def String.trimLeftChar (s : String) (c : Char) : String :=
  (s.toSubstring.trimLeftChar c).toString

def Ninst'.toString : Ninst' → String
  | reg o => Rinst.toString o
  | exec o => Xinst.toString o
  | push _ 0 => "PUSH0"
  | push x len => "PUSH" ++ len.repr ++ " 0x" ++ (x.toHex.trimLeftChar '0')

def Inst'.toString : Inst' → String
  | .next n => n.toString
  | .jump j => j.toString
  | .last l => l.toString

def showLim (lim : Nat) (m : Var) : Option Unit :=
  match lim % 1000000 with
  | 0 => do
    dbg_trace s!"gas : {m.gas}"
    return ()
  | _ => return ()



def showStep (υ : Var) (i : Inst') : Option Unit := do
  -- let b : B8 := κ.code.get! υ.pc
  dbg_trace (
    "{" ++
    s!"\"pc\": {υ.pc}, \"gas\": {υ.gas}, \"inst\": \"{i.toString}\"" ++
    "}"
  )
  return ()

--structure Ξ.Result where
--  (wor : Option Wor)
--  (gas : Nat)
--  (acs : Acs)
--  (ret : Option B8L)


def execSha (ω : Wor) (υ : Var) (κ : Con) : Ξ.Result :=
  let g_r : Nat := 60 + (12 * (ceilDiv κ.cld.length 32))
  match deductGas υ g_r with
  | none => {wor := none, gas := 0, acs := υ.toAcs, ret := some []}
  | some g' =>
    let hash : B256 := B8L.sha256 κ.cld
    {wor := some ω, gas := g', acs := υ.toAcs, ret := some hash.toB8L}

-- the X function of YP, except that the return type is modified to match
-- that of the Ξ function: the machine state (μ) returned by 'X' is never
-- used for anything except for remaining gas, so it is safe to discard the
-- unused information by the time X is returning.
-- This function returns `none` only when either the recursion limit or an
-- unimplemented opcode is reached. returns 'some _' for all other cases.
-- in particular, exceptional halting state should not cause it to return
-- a `none`.
def mkThetaCont (ω : Wor) (σ' : Sta) (μ : Mem) (υ : Var)
    (gas adr ilc isz olc osz : B256) : Option theta.Cont :=  do

  let t : Adr := adr.toAdr
  let act' : Nat := memExp (memExp υ.act ilc isz) olc osz
  let memCost : Nat := cMem act' - cMem υ.act
  let totalCost := (cCall ω υ gas.toNat memCost t 0) + memCost
  let gas' ← safeSub υ.gas totalCost
  some {
    olc := olc
    osz := osz
    gas := gas'
    mem := μ
    pc := υ.pc
    sta := σ'
    act := act'
  }

def exec : Nat → Wor → Sta → Mem → Var → Con → Option Ξ.Result
  | 0, _, _, _, _, _ => none
  | lim + 1, ω, σ, μ, υ, κ  => do
    showLim lim υ
    match getInst υ κ  with
    | none => some <| xhs υ
    | some i => do
      -- dbg_trace s!"remaining gas : {υ.gas}"
      -- showStep υ i
      -- dbg_trace s!"current stack :\n{Sta.toString σ}"
      match i with
      | .next (.exec .delcall) => do
        let (gas, adr, ilc, isz, olc, osz, σ') ← σ.pop6
        let i : B8L := μ.sliceD ilc.toNat isz.toNat 0
        let t : Adr := adr.toAdr
        -- dbg_trace s!"nested delgatecall to address : {t.toHex}"
        let as' : AdrSet := υ.adrs.insert t
        let A' : Acs := {υ.toAcs with adrs := as'}
        let act' : Nat := memExp (memExp υ.act ilc isz) olc osz
        let memCost : Nat := cMem act' - cMem υ.act
        let cg : Nat := cCallGas ω υ gas.toNat memCost t 0
        let totalCost := (cCall ω υ gas.toNat memCost t 0) + memCost
        let (some g') ← (return (safeSub υ.gas totalCost)) | some (xhs υ)
        let bd : theta.Cont :=
          {
            olc := olc
            osz := osz
            gas := g'
            mem := μ
            pc := υ.pc
            sta := σ'
            act := act'
          }
        let ⟨ω?, σ?, μ?, υ?⟩ ←
          if 0 = κ.exd
          then (theta.Result.toState bd ⟨ω, cg, A', 0, []⟩)
          else do let ⟨ω!, σ!, μ!, υ!, κ!⟩ :=
                        θ.prep
                          κ.wor0
                          κ.blk
                          ω
                          A'
                          κ.cla
                          κ.oga
                          κ.cta
                          t
                          cg
                          κ.gpr.toNat
                          0
                          κ.clv
                          i
                          (κ.exd - 1)
                          κ.wup
                  let xr ←
                    match κ!.cta.toNat with
                    | 1 => dbg_trace "unimplemented : precompiled contract 1"; sorry
                    | 2 => execSha ω! υ! κ!
                    | 3 => dbg_trace "unimplemented : precompiled contract 3"; sorry
                    | 4 => dbg_trace "unimplemented : precompiled contract 4"; sorry
                    | 5 => dbg_trace "unimplemented : precompiled contract 5"; sorry
                    | 6 => dbg_trace "unimplemented : precompiled contract 6"; sorry
                    | 7 => dbg_trace "unimplemented : precompiled contract 7"; sorry
                    | 8 => dbg_trace "unimplemented : precompiled contract 8"; sorry
                    | 9 => dbg_trace "unimplemented : precompiled contract 9"; sorry
                    | _ => exec lim ω! σ! μ! υ! κ!
                  let θr := θ.wrap ω! υ!.toAcs xr
                  (theta.Result.toState bd θr)
        exec lim ω? σ? μ? υ? κ
      | .next (.exec .call) => do
        let (gas, adr, clv, ilc, isz, olc, osz, σ') ← σ.pop7
        let t : Adr := adr.toAdr
        -- dbg_trace s!"nested call to address : {t.toHex}"
        let i : B8L := μ.sliceD ilc.toNat isz.toNat 0
        let as' : AdrSet := υ.adrs.insert t
        let A' : Acs := {υ.toAcs with adrs := as'}
        let act' : Nat := memExp (memExp υ.act ilc isz) olc osz
        let memCost : Nat := cMem act' - cMem υ.act
        let cg : Nat := cCallGas ω υ gas.toNat memCost t clv
        let totalCost := (cCall ω υ gas.toNat memCost t clv) + memCost
        let (some g') ← (return (safeSub υ.gas totalCost)) | some (xhs υ)
        let bd : theta.Cont :=
          {
            olc := olc
            osz := osz
            gas := g'
            mem := μ
            pc := υ.pc
            sta := σ'
            act := act'
          }
        let ⟨ω?, σ?, μ?, υ?⟩ ←
          if 0 = κ.exd ∨ (ω.get κ.cta).bal < clv
          then (theta.Result.toState bd ⟨ω, cg, A', 0, []⟩)
          else do let ⟨ω!, σ!, μ!, υ!, κ!⟩ : (Wor × Sta × Mem × Var × Con) :=
                        θ.prep
                          κ.wor0
                          κ.blk
                          ω
                          A'
                          κ.cta
                          κ.oga
                          t
                          t
                          cg
                          κ.gpr.toNat
                          clv
                          clv
                          i
                          (κ.exd - 1)
                          κ.wup
                  let xr ←
                    match κ!.cta.toNat with
                    | 1 => dbg_trace "unimplemented : precompiled contract 1"; sorry
                    | 2 => execSha ω! υ! κ!
                    | 3 => dbg_trace "unimplemented : precompiled contract 3"; sorry
                    | 4 => dbg_trace "unimplemented : precompiled contract 4"; sorry
                    | 5 => dbg_trace "unimplemented : precompiled contract 5"; sorry
                    | 6 => dbg_trace "unimplemented : precompiled contract 6"; sorry
                    | 7 => dbg_trace "unimplemented : precompiled contract 7"; sorry
                    | 8 => dbg_trace "unimplemented : precompiled contract 8"; sorry
                    | 9 => dbg_trace "unimplemented : precompiled contract 9"; sorry
                    | _ => exec lim ω! σ! μ! υ! κ!
                  let θr := θ.wrap ω! υ!.toAcs xr
                  (theta.Result.toState bd θr)
        exec lim ω? σ? μ? υ? κ
      | .next n =>
        match n.run ω σ μ υ κ  with
        | none => some (xhs υ)
        | some ⟨ω', σ', μ', υ'⟩ => exec lim ω' σ' μ' υ' κ --s'.env s'.acr s'.wor s'.mcn
      | .jump j =>
         match j.run σ υ κ with
         | none => some (xhs υ)
         | some ⟨σ', υ'⟩ => exec lim ω σ' μ υ' κ
      | .last .stop => some {wor := ω, gas := υ.gas, acs := υ.toAcs, ret := some []}
      | .last .ret => some <| (retRun ω σ μ υ).getD (xhs υ)
      | .last .dest => do
        let (x, _) ← σ.pop1
        let a := x.toAdr -- recipient
        let cost :=
          gSelfdestruct
          + (if a ∈ υ.adrs then 0 else gColdAccountAccess)
          + ( if Dead ω a ∧ ω.balAt κ.cta ≠ 0
              then gNewAccount
              else 0 )
        let gas' ← deductGas υ cost
        some
          {
            wor :=
              if a = κ.cta
              then ω
              else let v := (ω.get κ.cta).bal
                   let wor' := ω.setBal κ.cta 0
                   wor'.addBal a v
            gas := gas'
            acs :=
              {
                υ.toAcs with
                dest := κ.cta :: υ.dest
                adrs := υ.adrs.insert a
              }
            ret := some []
          }

      | _ => none --dbg_trace s!"unimplemented instruction : {i.toString}"; none

def theta
  -- Extra arguments not mentioned by YP,
  -- but still necessary for correct execution
  (H : Block)
  (ω₀ : Wor)

  -- Arguments specified by YP
  (ω : Wor)
  (A : Acs)
  (s : Adr)
  (o : Adr)
  (r : Adr)
  (c : Adr)
  (g : Nat)
  (p : Nat)
  (v : B256)
  (v_app : B256)
  (d : B8L)
  (e : Nat)
  (w : Bool) :
  Option theta.Result :=
  let ⟨ω?, σ?, μ?, υ?, κ?⟩ := θ.prep ω₀ H ω A s o r c g p v v_app d e w
  match exec g ω? σ? μ? υ? κ? with
  | none => none
  | some xr => some (θ.wrap ω? υ?.toAcs xr)

def publicAddress (hsa : ByteArray) (ri : UInt8) (rsa : ByteArray) : IO Adr :=
  match (ecrecoverFlag hsa ri rsa).toList with
  | [] => IO.throw "Unreachable code : ecrecover should never return empty bytes"
  | b :: pa =>
    if b = 0
    then IO.throw "ecrecover failed"
    else (B8L.toAdr pa).toIO "bytearray to address conversion failed"

structure transact.Result : Type where
  (wor : Wor)
  (gas : Nat)
  (log : B256)
  (sta : Bool)

def eraseIfEmpty (w : Wor) (a : Adr) : Wor := w.set a <| w.get a

def Tx.run
  (blk : Block) (w : Wor) (tx : TxBytesContent)
  (sender : Adr) : IO transact.Result := do

  IO.println s!"block gas limit : 0x{blk.gasLimit.toHex}"
  IO.println s!"tx gas limit    : 0x{tx.gasLimit.toHex}"
  IO.guard (tx.gasLimit ≤ blk.gasLimit) "error : block gas limit < tx gas limit"

  let g : Nat := tx.gasLimit.toNat - intrinsicGas (some tx.receiver) tx.calldata []
  let w ← (checkpoint w sender (tx.gasLimit * tx.gasPrice)).toIO ""

  let tr ←
    (
      theta
        blk
        w w
        (A_star blk sender (some tx.receiver) [])
        sender
        sender
        tx.receiver
        tx.receiver
        g
        tx.gasPrice.toNat
        tx.val
        tx.val
        tx.calldata
        1024
        true
    ).toIO "theta failed"

  let gasLeft : Nat := tr.gas -- g'
  let refundAmount : Nat := tr.acs.ref
  let gasReturn : B256 :=
    Nat.toB256 (gasLeft + min ((tx.gasLimit.toNat - gasLeft) / 5) refundAmount) -- g*
  let gasUsed : B256 := tx.gasLimit - gasReturn
  let valReturn : B256 := gasReturn * tx.gasPrice

  let f : B256 :=
    match tx.type with
      | .two _ tm tf => min tf (tm - blk.baseFee)
      | _ => tx.gasPrice - blk.baseFee

  let w₀ : Wor := tr.wor.addBal sender valReturn
  let w₁ : Wor := w₀.addBal blk.ben (gasUsed * f)
  --let w₂ : Wor := List.foldl Lean.RBMap.erase w₁ tr.acr.dest
  --let w₃ : Wor := List.foldl eraseIfEmpty w₂ tr.acr.tchd.toList
  let w₃ : Wor := List.foldl eraseIfEmpty w₁ tr.acs.tchd.toList

  return {
    wor := w₃,
    gas := gasUsed.toNat
    log := (RLP'.list tr.acs.logs.reverse).encode.keccak
    sta := tr.status
  }


def Test.run (t : Test) : IO Unit := do
  let ⟨tx, hsh⟩ ← decodeTxBytes t.txdata
  let rsa : ByteArray := ⟨Array.mk (tx.r ++ tx.s)⟩
  let hsa : ByteArray := ⟨Array.mk hsh.toB8L⟩
  let ri : UInt8 := Byte.toB8 (if tx.yParity then 1 else 0)
  let sender ← publicAddress hsa ri rsa

  .println "initial world : "
  .println (String.joinln t.world.toStrings)

  let sa₀ ← (t.world.find? sender).toIO "no sender account"

  .guard (tx.nonce = t.nonce) "nonce check 1 : fail"
  .println "nonce check 1 : pass"

  .guard (tx.nonce = sa₀.nonce) "nonce check 2 : fail"
  .println "nonce check 2 : pass"

  .guard (sender = t.sender) "sender check : fail"
  .println "sender check : pass"

  .guard (tx.receiver = t.receiver) "receiver check : fail"
  .println s!"receiver : {tx.receiver.toHex}"

  .guard (tx.gasLimit = t.gasLimit) s!"gas limit check failed. tx.gasLimit : {tx.gasLimit.toHex}, t.gasLimit = {t.gasLimit.toHex}"
  .println "gas limit check : pass"

  .guard (tx.gasPrice = t.gasPrice) "gas price check : fail"
  .println "gas price check : pass"

  .guard (tx.val = t.value) "value check : fail"
  .println "value check : pass"

  .guard (tx.calldata = t.calldata) "calldata check : fail"
  .println "calldata check : pass"

  .println s!"CALLDATA : {tx.calldata.toHex}"

  let rst ←
    Tx.run
      {
        baseFee := t.baseFee,
        ben := t.coinbase
        prevRandao := t.prevRandao
        gasLimit := t.blockGasLimit
        timestamp := t.timestamp
        number := t.number
        chainId := 1
      }
      t.world
      tx
      sender

  .println s!"tx status : {rst.sta}"
  .println "world state after tx :"
  .println (String.joinln rst.wor.toStrings)

  let temp' := (List.map toKeyVal rst.wor.toList)
  let finalNTB : NTB := Lean.RBMap.fromList temp' _
  let root' : B256 := trie finalNTB

  .println s!"computed final root' : {root'.toHex}"
  .println s!"expected final root  : {t.hash.toHex}"

  .guard (root' = t.hash) "state root' check : fail"
  .println "state root' check : pass"

  .guard (rst.log = t.logs) "log hash check : fail"
  .println "log hash check : pass"
  .println "test complete."

def Tests.run : Nat → List Test → IO Unit
  | _, [] => return ()
  | n, t :: ts => do
    .println s!"================ Running test {n} ================"
    t.run
    Tests.run (n + 1) ts

def main : List String → IO Unit
  | [testPath] => do
    let j ← readJsonFile testPath
    let td ← Lean.Json.toTestData j
    let ts ← getTests td
    Tests.run 0 ts
  | [testPath, testNum] => do
    let n ← testNum.toNat?.toIO "error : second argument is not a number"
    let j ← readJsonFile testPath
    let td ← Lean.Json.toTestData j
    let ts ← getTests td
    ((ts.get? n).toIO s!"test #{n} does not exist") >>= Test.run
  | _ => IO.throw "error : invalid arguments"


-- def Bytes.toHexLine (bs : Bytes) : String :=
--   s!"hex\"{bs.toHex}\""
--
-- def WethByteCode : String :=
--   List.foldr
--      (λ s0 s1 => s0 ++ "\n" ++ s1)
--      "" <| List.map Bytes.toHexLine
--         <| List.chunks 31 <| Option.getD weth.compile []
