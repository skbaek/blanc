import Blanc.Lift.Usdc.RecoveryV2
import Blanc.Lift.Usdc.AllowLocality
import Blanc.Lift.Usdc.Slots
import Blanc.Lift.SolcSignedQuery

/-! Actual fresh V2 source prefixes for every registered owner selector. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift

/-- Exactly the four owner routes already enumerated by the write-site table. -/
inductive OwnerOpV2 where
  | permit | approveAuth | increaseAuth | decreaseAuth
  deriving DecidableEq

namespace OwnerOpV2

def selector : OwnerOpV2 → B256
  | .permit => 0xd505accf
  | .approveAuth => 0xe1560fd3
  | .increaseAuth => 0xc237108f
  | .decreaseAuth => 0xb0086095

theorem selectors_eq : [selector .permit, selector .approveAuth,
    selector .increaseAuth, selector .decreaseAuth] = selV2.owners := rfl

def wrapper : OwnerOpV2 → SFunc
  | .permit => ImplV2.t_0bc6_c111
  | .approveAuth => ImplV2.t_0cd7_c103
  | .increaseAuth => ImplV2.t_0b52_c109
  | .decreaseAuth => ImplV2.t_0a9b_c113

def wrapperReject : OwnerOpV2 → SFunc
  | .permit => ImplV2.t_0bd8_c111
  | .approveAuth => ImplV2.t_0cea_c103
  | .increaseAuth => ImplV2.t_0b65_c109
  | .decreaseAuth => ImplV2.t_0aae_c113

def decoder : OwnerOpV2 → SFunc
  | .permit => ImplV2.t_0bdc_c111
  | .approveAuth => ImplV2.t_0cee_c103
  | .increaseAuth => ImplV2.t_0b69_c109
  | .decreaseAuth => ImplV2.t_0ab2_c113

def decodeTag : OwnerOpV2 → UInt8 × UInt8
  | .permit => (0x0b,0xdc)
  | .approveAuth => (0x0c,0xee)
  | .increaseAuth => (0x0b,0x69)
  | .decreaseAuth => (0x0a,0xb2)

def entry : OwnerOpV2 → SFunc
  | .permit => ImplV2.t_3450_c23
  | .approveAuth => ImplV2.t_3761_c14
  | .increaseAuth => ImplV2.t_328f_c21
  | .decreaseAuth => ImplV2.t_3033_c25

def entryTag : OwnerOpV2 → UInt8 × UInt8
  | .permit => (0x34,0x50)
  | .approveAuth => (0x37,0x61)
  | .increaseAuth => (0x32,0x8f)
  | .decreaseAuth => (0x30,0x33)

def entryNumber : OwnerOpV2 → Nat
  | .permit => 23 | .approveAuth => 14 | .increaseAuth => 21 | .decreaseAuth => 25

def returnTree : OwnerOpV2 → SFunc
  | .permit => ImplV2.t_0470_c111
  | .approveAuth => ImplV2.t_0470_c103
  | .increaseAuth => ImplV2.t_0470_c109
  | .decreaseAuth => ImplV2.t_0470_c113

def widthBytes : OwnerOpV2 → Bytes
  | .permit => [0xe0] | _ => [0x01,0x20]

def width (op : OwnerOpV2) : B256 := Bytes.toB256 op.widthBytes

theorem widthLe (op : OwnerOpV2) : op.widthBytes.length ≤ 32 := by cases op <;> decide

def calldataBound : OwnerOpV2 → Nat
  | .permit => 228 | _ => 292

def args (op : OwnerOpV2) (sevm : Sevm) : List B256 :=
  match op with
  | .permit => [Sevm.dataWord sevm 196, Sevm.dataWord sevm 164,
      Sevm.dataWord sevm 132 &&& 255, Sevm.dataWord sevm 100, Sevm.dataWord sevm 68,
      (Sevm.dataWord sevm 36).toAdr.toB256, (Sevm.dataWord sevm 4).toAdr.toB256]
  | _ => [Sevm.dataWord sevm 260, Sevm.dataWord sevm 228,
      Sevm.dataWord sevm 196 &&& 255, Sevm.dataWord sevm 164, Sevm.dataWord sevm 132,
      Sevm.dataWord sevm 100, Sevm.dataWord sevm 68,
      (Sevm.dataWord sevm 36).toAdr.toB256, (Sevm.dataWord sevm 4).toAdr.toB256]

def decoderLine (op : OwnerOpV2) : List Ninst :=
  if op = .permit then SolcSignedQuery.decodeLine op.entryTag.1 op.entryTag.2
  else SolcSignedQuery.decodeAuthorizationLine op.entryTag.1 op.entryTag.2

end OwnerOpV2

private theorem root_ready {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    F.sevm.value = 0 ∧ 4 ≤ F.sevm.data.length.toB256.toNat ∧
      Nonempty (CursorStateAt ImplV2.code ImplV2.cert F ImplV2.t_001a_c0 F.devm []
        (Mem.empty.write 64 (128 : B256).toBytes) []) := by
  have first : CursorStateAt ImplV2.code ImplV2.cert F ImplV2.t_0000_c0
      F.devm [] Mem.empty [] :=
    ⟨F, Cursor.start ImplV2.cert, .refl _, rfl, rfl,
      cursor_start ImplV2.cert_check pc code, rfl, ⟨_, St.self stack memory⟩, rfl⟩
  obtain ⟨guard⟩ := first.lineH ImplV2.cert_check success fork.stateGas
    (SolcSignedQuery.prologue 0 16) rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.prologue,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    SolcSignedQuery.prologue_line
  obtain ⟨taken,⟨entered⟩⟩ := SolcSignedQuery.guardSucc guard ImplV2.cert_check rfl success fork
  have valueZero := eq_zero_of_iszero_ne_zero taken
  obtain ⟨opened⟩ := entered.destH ImplV2.cert_check success fork.stateGas
  obtain ⟨guardSize⟩ := opened.lineH ImplV2.cert_check success fork.stateGas
    (SolcSignedQuery.sizeLine 3 0x4c) rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.sizeLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    SolcSignedQuery.size_line
  obtain ⟨zero, continued⟩ := SolcSignedQuery.guardZero guardSize ImplV2.cert_check rfl success fork
  exact ⟨valueZero, toNat_ge_of_ltCheck_eq_zero zero, continued⟩

private theorem root_selected {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    F.sevm.value = 0 ∧ 4 ≤ F.sevm.data.length.toB256.toNat ∧
      Nonempty (CursorStateAt ImplV2.code ImplV2.cert F
        ((SolcSignedQuery.compareLine .gt 0x8a 0x6d 0xb9 0xc3 0x01 0xbd).foldr
          SFunc.next (.branch ImplV2.t_002b_c0 ImplV2.t_01bd_c0)) F.devm [Sevm.selector F.sevm]
        (Mem.empty.write 64 (128 : B256).toBytes) []) := by
  obtain ⟨valueZero,sizeBound,⟨before⟩⟩ := root_ready pc code stack memory success fork
  obtain ⟨selected⟩ := before.lineH ImplV2.cert_check success fork.stateGas SolcSignedQuery.selectorLine rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.selectorLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    SolcSignedQuery.selector_line
  exact ⟨valueZero,sizeBound,⟨selected⟩⟩

private theorem root_wrapper (op : OwnerOpV2) {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (selector : Sevm.selector F.sevm = op.selector)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    F.sevm.value = 0 ∧ 4 ≤ F.sevm.data.length.toB256.toNat ∧
      Nonempty (CursorStateAt ImplV2.code ImplV2.cert F op.wrapper F.devm [op.selector]
        (Mem.empty.write 64 (128 : B256).toBytes) []) := by
  obtain ⟨valueZero,sizeBound,⟨selected⟩⟩ := root_selected pc code stack memory success fork
  rw [selector] at selected
  refine ⟨valueZero,sizeBound,?_⟩
  cases op with
  | permit =>
    obtain ⟨c0⟩ := SolcSignedQuery.selector_gt_zero selected ImplV2.cert_check (by decide) success fork
    obtain ⟨c1⟩ := SolcSignedQuery.selector_gt_zero c0 ImplV2.cert_check (by decide) success fork
    obtain ⟨c2⟩ := SolcSignedQuery.selector_gt_succ c1 ImplV2.cert_check (by decide) success fork
    obtain ⟨opened3⟩ := c2.destH ImplV2.cert_check success fork.stateGas
    obtain ⟨c3⟩ := SolcSignedQuery.selector_gt_succ opened3 ImplV2.cert_check (by decide) success fork
    obtain ⟨opened4⟩ := c3.destH ImplV2.cert_check success fork.stateGas
    obtain ⟨c4⟩ := SolcSignedQuery.selector_eq_zero opened4 ImplV2.cert_check (by decide) success fork
    obtain ⟨c5⟩ := SolcSignedQuery.selector_eq_zero c4 ImplV2.cert_check (by decide) success fork
    exact SolcSignedQuery.selector_eq_succ c5 ImplV2.cert_check (by decide) rfl success fork

  | approveAuth =>
    obtain ⟨c0⟩ := SolcSignedQuery.selector_gt_zero selected ImplV2.cert_check (by decide) success fork
    obtain ⟨c1⟩ := SolcSignedQuery.selector_gt_zero c0 ImplV2.cert_check (by decide) success fork
    obtain ⟨c2⟩ := SolcSignedQuery.selector_gt_zero c1 ImplV2.cert_check (by decide) success fork
    obtain ⟨c3⟩ := SolcSignedQuery.selector_gt_succ c2 ImplV2.cert_check (by decide) success fork
    obtain ⟨opened4⟩ := c3.destH ImplV2.cert_check success fork.stateGas
    exact SolcSignedQuery.selector_eq_succ opened4 ImplV2.cert_check (by decide) rfl success fork

  | increaseAuth =>
    obtain ⟨c0⟩ := SolcSignedQuery.selector_gt_zero selected ImplV2.cert_check (by decide) success fork
    obtain ⟨c1⟩ := SolcSignedQuery.selector_gt_zero c0 ImplV2.cert_check (by decide) success fork
    obtain ⟨c2⟩ := SolcSignedQuery.selector_gt_succ c1 ImplV2.cert_check (by decide) success fork
    obtain ⟨opened3⟩ := c2.destH ImplV2.cert_check success fork.stateGas
    obtain ⟨c3⟩ := SolcSignedQuery.selector_gt_succ opened3 ImplV2.cert_check (by decide) success fork
    obtain ⟨opened4⟩ := c3.destH ImplV2.cert_check success fork.stateGas
    exact SolcSignedQuery.selector_eq_succ opened4 ImplV2.cert_check (by decide) rfl success fork

  | decreaseAuth =>
    obtain ⟨c0⟩ := SolcSignedQuery.selector_gt_zero selected ImplV2.cert_check (by decide) success fork
    obtain ⟨c1⟩ := SolcSignedQuery.selector_gt_succ c0 ImplV2.cert_check (by decide) success fork
    obtain ⟨opened2⟩ := c1.destH ImplV2.cert_check success fork.stateGas
    obtain ⟨c2⟩ := SolcSignedQuery.selector_gt_zero opened2 ImplV2.cert_check (by decide) success fork
    obtain ⟨c3⟩ := SolcSignedQuery.selector_gt_zero c2 ImplV2.cert_check (by decide) success fork
    obtain ⟨c4⟩ := SolcSignedQuery.selector_eq_zero c3 ImplV2.cert_check (by decide) success fork
    exact SolcSignedQuery.selector_eq_succ c4 ImplV2.cert_check (by decide) rfl success fork

private theorem wrapper_guard (op : OwnerOpV2) {F : Exec.Deriv} {post b : Devm} {M : Mem}
    (cut : CursorStateAt ImplV2.code ImplV2.cert F op.wrapper b [op.selector] M [])
    (sizeBound : 4 ≤ F.sevm.data.length.toB256.toNat)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    op.calldataBound ≤ F.sevm.data.length.toB256.toNat ∧
      Nonempty (CursorStateAt ImplV2.code ImplV2.cert F op.decoder b
        [F.sevm.data.length.toB256 - 4,4,0x470,op.selector] M []) := by
  have shape : op.wrapper = .dest
      ((SolcSignedQuery.wrapperLine 4 0x70 op.widthBytes op.widthLe
        op.decodeTag.1 op.decodeTag.2).foldr SFunc.next (.branch op.wrapperReject op.decoder)) := by
    cases op <;> rfl
  rw [shape] at cut
  obtain ⟨opened⟩ := cut.destH ImplV2.cert_check success fork.stateGas
  obtain ⟨guard⟩ := opened.lineH ImplV2.cert_check success fork.stateGas _ rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.wrapperLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    SolcSignedQuery.wrapper_line
  obtain ⟨taken,accepted⟩ := SolcSignedQuery.guardSucc guard ImplV2.cert_check
    (by cases op <;> rfl) success fork
  have bound := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero taken)
  rw [B256.toNat_sub_eq_of_le _ _ (by
    rw [B256.le_iff_toNat_le_toNat]; exact sizeBound)] at bound
  have expected : op.calldataBound = op.width.toNat + 4 := by cases op <;> rfl
  refine ⟨?_,accepted⟩
  change op.width.toNat ≤ F.sevm.data.length.toB256.toNat - 4 at bound
  rw [expected]
  omega

private theorem decoder_args (op : OwnerOpV2) {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {available : B256}
    (run : Line.Run sevm (St b [available,4,0x470,op.selector] M G) op.decoderLine d) :
    ∃ G', d = St b (Bytes.toB256 [op.entryTag.1,op.entryTag.2] ::
      (op.args sevm ++ [0x470,op.selector])) M G' := by
  cases op with
  | permit => exact SolcSignedQuery.decode_line run
  | approveAuth => exact SolcSignedQuery.decode_authorization_line run
  | increaseAuth => exact SolcSignedQuery.decode_authorization_line run
  | decreaseAuth => exact SolcSignedQuery.decode_authorization_line run

private theorem root_decoded (op : OwnerOpV2) {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (selector : Sevm.selector F.sevm = op.selector)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    F.sevm.value = 0 ∧ op.calldataBound ≤ F.sevm.data.length.toB256.toNat ∧
      Nonempty (CursorStateAt ImplV2.code ImplV2.cert F op.entry F.devm
        (op.args F.sevm ++ [0x470,op.selector])
        (Mem.empty.write 64 (128 : B256).toBytes) [op.returnTree]) := by
  obtain ⟨valueZero,sizeBound,⟨wrapper⟩⟩ := root_wrapper op pc code stack memory selector success fork
  obtain ⟨bound,⟨accepted⟩⟩ := wrapper_guard op wrapper sizeBound success fork
  have shape : op.decoder = .dest
      (op.decoderLine.foldr SFunc.next (.callNext op.entryNumber op.returnTree)) := by
    cases op <;> rfl
  rw [shape] at accepted
  obtain ⟨opened⟩ := accepted.destH ImplV2.cert_check success fork.stateGas
  obtain ⟨decoded⟩ := opened.lineH ImplV2.cert_check success fork.stateGas _ rfl
    (by intro ni member xi same; subst ni
        cases op <;>
          simp only [OwnerOpV2.decoderLine,OwnerOpV2.entryTag,reduceCtorEq,ite_true,ite_false,
            SolcSignedQuery.decodeLine,SolcSignedQuery.decodeAuthorizationLine,
            List.mem_cons,List.not_mem_nil,or_self] at member)
    (decoder_args op)
  exact ⟨valueZero,bound,decoded.callH ImplV2.cert_check success fork.stateGas (by cases op <;> rfl)⟩

namespace OwnerOpV2

def pauseNext : OwnerOpV2 → SFunc
  | .permit => ImplV2.t_34da_c23
  | .approveAuth => ImplV2.t_37eb_c14
  | .increaseAuth => ImplV2.t_3319_c21
  | .decreaseAuth => ImplV2.t_30bd_c25

def pauseReject : OwnerOpV2 → SFunc
  | .permit => ImplV2.t_3474_c23
  | .approveAuth => ImplV2.t_3785_c14
  | .increaseAuth => ImplV2.t_32b3_c21
  | .decreaseAuth => ImplV2.t_3057_c25

def callEntry : OwnerOpV2 → SFunc
  | .permit => ImplV2.t_35dc_c23
  | .approveAuth => ImplV2.t_38ed_c14
  | .increaseAuth => ImplV2.t_341b_c21
  | .decreaseAuth => ImplV2.t_31bf_c25

def pauseTag : OwnerOpV2 → UInt8 × UInt8
  | .permit => (0x34,0xda)
  | .approveAuth => (0x37,0xeb)
  | .increaseAuth => (0x33,0x19)
  | .decreaseAuth => (0x30,0xbd)

def blackEntry (op : OwnerOpV2) (spender : Bool) : SFunc :=
  match op, spender with
  | .permit,false => ImplV2.t_34da_c23
  | .permit,true => ImplV2.t_355b_c23
  | .approveAuth,false => ImplV2.t_37eb_c14
  | .approveAuth,true => ImplV2.t_386c_c14
  | .increaseAuth,false => ImplV2.t_3319_c21
  | .increaseAuth,true => ImplV2.t_339a_c21
  | .decreaseAuth,false => ImplV2.t_30bd_c25
  | .decreaseAuth,true => ImplV2.t_313e_c25

def blackNext (op : OwnerOpV2) (spender : Bool) : SFunc :=
  match op, spender with
  | .permit,false => ImplV2.t_355b_c23
  | .permit,true => ImplV2.t_35dc_c23
  | .approveAuth,false => ImplV2.t_386c_c14
  | .approveAuth,true => ImplV2.t_38ed_c14
  | .increaseAuth,false => ImplV2.t_339a_c21
  | .increaseAuth,true => ImplV2.t_341b_c21
  | .decreaseAuth,false => ImplV2.t_313e_c25
  | .decreaseAuth,true => ImplV2.t_31bf_c25

def blackReject (op : OwnerOpV2) (spender : Bool) : SFunc :=
  match op, spender with
  | .permit,false => ImplV2.t_350b_c23
  | .permit,true => ImplV2.t_358c_c23
  | .approveAuth,false => ImplV2.t_381c_c14
  | .approveAuth,true => ImplV2.t_389d_c14
  | .increaseAuth,false => ImplV2.t_334a_c21
  | .increaseAuth,true => ImplV2.t_33cb_c21
  | .decreaseAuth,false => ImplV2.t_30ee_c25
  | .decreaseAuth,true => ImplV2.t_316f_c25

def blackTag (op : OwnerOpV2) (spender : Bool) : UInt8 × UInt8 :=
  match op,spender with
  | .permit,false => (0x35,0x5b)
  | .permit,true => (0x35,0xdc)
  | .approveAuth,false => (0x38,0x6c)
  | .approveAuth,true => (0x38,0xed)
  | .increaseAuth,false => (0x33,0x9a)
  | .increaseAuth,true => (0x34,0x1b)
  | .decreaseAuth,false => (0x31,0x3e)
  | .decreaseAuth,true => (0x31,0xbf)

def addressDepth : OwnerOpV2 → Fin 15
  | .permit => ⟨6,by decide⟩ | _ => ⟨8,by decide⟩

end OwnerOpV2

private theorem pause_guard (op : OwnerOpV2) {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {S : List B256} {K : List SFunc}
    (cut : CursorStateAt ImplV2.code ImplV2.cert F op.entry b S M K)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    (255 &&& (b.getStorVal F.sevm.currentTarget 1 /
      (0x10000000000000000000000000000000000000000 : B256))) = 0 ∧
    Nonempty (CursorStateAt ImplV2.code ImplV2.cert F op.pauseNext
      (afterSloadH F.sevm b 1) S M K) := by
  have shape : op.entry = .dest ((SolcSignedQuery.pauseLine 1 op.pauseTag.1 op.pauseTag.2).foldr
      SFunc.next (.branch op.pauseReject op.pauseNext)) := by cases op <;> rfl
  rw [shape] at cut
  obtain ⟨opened⟩ := cut.destH ImplV2.cert_check success fork.stateGas
  obtain ⟨guard⟩ := opened.lineH ImplV2.cert_check success fork.stateGas _ rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.pauseLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    (SolcSignedQuery.pause_line fork)
  obtain ⟨taken,accepted⟩ := SolcSignedQuery.guardSucc guard ImplV2.cert_check
    (by cases op <;> rfl) success fork
  exact ⟨eq_zero_of_iszero_ne_zero taken,accepted⟩

private theorem blacklist_guard (op : OwnerOpV2) (spender : Bool)
    {F : Exec.Deriv} {post b : Devm} {M : Mem} {S : List B256} {K : List SFunc}
    (adr : Adr) (source : S[op.addressDepth.val]? = some adr.toB256)
    (cut : CursorStateAt ImplV2.code ImplV2.cert F (op.blackEntry spender) b S M K)
    (ptr : PtrMem 128 96 M)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    (255 &&& b.getStorVal F.sevm.currentTarget (mapSlot adr.toB256 3)) = 0 ∧
    let b' := afterSloadH F.sevm b (mapSlot adr.toB256 3)
    let M' := (M.write 0 adr.toB256.toBytes).write 32 (3 : B256).toBytes
    b'.state = b.state ∧ PtrMem 128 96 M' ∧
      Nonempty (CursorStateAt ImplV2.code ImplV2.cert F (op.blackNext spender) b'
        (adr.toB256 :: S) M' K) := by
  have shape : op.blackEntry spender = .dest
      ((SolcSignedQuery.mappedByteReadLine op.addressDepth 3).foldr SFunc.next
        (.next (.push [op.blackTag spender |>.1,op.blackTag spender |>.2]
          (by simp only [List.length_cons,List.length_nil]; decide))
          (.branch (op.blackReject spender) (op.blackNext spender)))) := by
    cases op <;> cases spender <;> rfl
  rw [shape] at cut
  obtain ⟨opened⟩ := cut.destH ImplV2.cert_check success fork.stateGas
  obtain ⟨read⟩ := opened.lineH ImplV2.cert_check success fork.stateGas _ rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.mappedByteReadLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    (SolcSignedQuery.mapped_byte_read_line source ptr fork)
  obtain ⟨guard⟩ := read.lineH ImplV2.cert_check success fork.stateGas
    [.push [(op.blackTag spender).1,(op.blackTag spender).2]
      (by simp only [List.length_cons,List.length_nil]; decide)] rfl
    (by intro ni member xi same; subst ni
        simp only [List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    (by intro gas d run
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_push step
        cases run
        exact ⟨_,rfl⟩)
  obtain ⟨taken,accepted⟩ := SolcSignedQuery.guardSucc guard ImplV2.cert_check
    (by cases op <;> cases spender <;> rfl) success fork
  refine ⟨eq_zero_of_iszero_ne_zero taken,?_,?_,accepted⟩
  · exact afterSloadH_state _ _ _
  · exact (ptr.write 0 adr.toB256 (.inl (by decide))).write 32 3 (.inl (by decide))

/-- The exact scratch image left by the two address-keyed blacklist reads. -/
def ownerV2GuardMemory (sevm : Sevm) : Mem :=
  let M := Mem.empty.write 64 (128 : B256).toBytes
  let M := (M.write 0 (Sevm.dataWord sevm 4).toAdr.toB256.toBytes).write 32 (3 : B256).toBytes
  (M.write 0 (Sevm.dataWord sevm 36).toAdr.toB256.toBytes).write 32 (3 : B256).toBytes

private theorem root_guarded (op : OwnerOpV2) {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (selector : Sevm.selector F.sevm = op.selector)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    F.sevm.value = 0 ∧ op.calldataBound ≤ F.sevm.data.length.toB256.toNat ∧
    (255 &&& (F.devm.getStorVal F.sevm.currentTarget 1 /
      (0x10000000000000000000000000000000000000000 : B256))) = 0 ∧
    (255 &&& F.devm.getStorVal F.sevm.currentTarget
      (mapSlot (Sevm.dataWord F.sevm 4).toAdr.toB256 3)) = 0 ∧
    (255 &&& F.devm.getStorVal F.sevm.currentTarget
      (mapSlot (Sevm.dataWord F.sevm 36).toAdr.toB256 3)) = 0 ∧
    ∃ b M, b.state = F.devm.state ∧ M = ownerV2GuardMemory F.sevm ∧ PtrMem 128 96 M ∧
      Nonempty (CursorStateAt ImplV2.code ImplV2.cert F op.callEntry b
        ((Sevm.dataWord F.sevm 36).toAdr.toB256 :: (Sevm.dataWord F.sevm 4).toAdr.toB256 ::
          (op.args F.sevm ++ [0x470,op.selector])) M [op.returnTree]) := by
  obtain ⟨valueZero,sizeBound,⟨decoded⟩⟩ := root_decoded op pc code stack memory selector success fork
  obtain ⟨pauseZero,⟨unpaused⟩⟩ := pause_guard op decoded success fork
  have ownerTree : op.pauseNext = op.blackEntry false := by cases op <;> rfl
  rw [ownerTree] at unpaused
  obtain ⟨ownerZero,state1,ptr1,⟨ownerAllowed⟩⟩ := blacklist_guard op false
    (Sevm.dataWord F.sevm 4).toAdr (by cases op <;> rfl) unpaused
    (PtrMem.init 128) success fork
  have spenderTree : op.blackNext false = op.blackEntry true := by cases op <;> rfl
  rw [spenderTree] at ownerAllowed
  obtain ⟨spenderZero,state2,ptr2,⟨spenderAllowed⟩⟩ := blacklist_guard op true
    (Sevm.dataWord F.sevm 36).toAdr (by cases op <;> rfl) ownerAllowed ptr1 success fork
  have state0 : (afterSloadH F.sevm F.devm 1).state = F.devm.state := by
    exact afterSloadH_state _ _ _
  have state01 := state1.trans state0
  have state012 := state2.trans state01
  have ownerRead : (afterSloadH F.sevm F.devm 1).getStorVal F.sevm.currentTarget
      (mapSlot (Sevm.dataWord F.sevm 4).toAdr.toB256 3) =
      F.devm.getStorVal F.sevm.currentTarget (mapSlot (Sevm.dataWord F.sevm 4).toAdr.toB256 3) := by
    unfold Devm.getStorVal Devm.getAcct
    rw [state0]
  have spenderRead : (afterSloadH F.sevm (afterSloadH F.sevm F.devm 1)
      (mapSlot (Sevm.dataWord F.sevm 4).toAdr.toB256 3)).getStorVal F.sevm.currentTarget
      (mapSlot (Sevm.dataWord F.sevm 36).toAdr.toB256 3) =
      F.devm.getStorVal F.sevm.currentTarget (mapSlot (Sevm.dataWord F.sevm 36).toAdr.toB256 3) := by
    unfold Devm.getStorVal Devm.getAcct
    rw [state01]
  rw [ownerRead] at ownerZero
  rw [spenderRead] at spenderZero
  have callTree : op.blackNext true = op.callEntry := by cases op <;> rfl
  rw [callTree] at spenderAllowed
  exact ⟨valueZero,sizeBound,pauseZero,ownerZero,spenderZero,_,_,state012,rfl,ptr2,⟨spenderAllowed⟩⟩

namespace OwnerOpV2

def internalEntry : OwnerOpV2 → SFunc
  | .permit => ImplV2.t_475b_c71
  | .approveAuth => ImplV2.t_4976_c66
  | .increaseAuth => ImplV2.t_4625_c70
  | .decreaseAuth => ImplV2.t_4456_c72

def internalReturn : OwnerOpV2 → SFunc
  | .permit => ImplV2.t_35eb_c23
  | .approveAuth => ImplV2.t_31d0_c14
  | .increaseAuth => ImplV2.t_31d0_c21
  | .decreaseAuth => ImplV2.t_31d0_c25

def internalTag : OwnerOpV2 → UInt8 × UInt8
  | .permit => (0x47,0x5b)
  | .approveAuth => (0x49,0x76)
  | .increaseAuth => (0x46,0x25)
  | .decreaseAuth => (0x44,0x56)

def internalReturnTag : OwnerOpV2 → UInt8 × UInt8
  | .permit => (0x35,0xeb)
  | .approveAuth => (0x31,0xd0)
  | .increaseAuth => (0x31,0xd0)
  | .decreaseAuth => (0x31,0xd0)

def internalNumber : OwnerOpV2 → Nat
  | .permit => 71 | .approveAuth => 66 | .increaseAuth => 70 | .decreaseAuth => 72

def calleeLine (op : OwnerOpV2) : List Ninst :=
  [.push [op.internalReturnTag.1,op.internalReturnTag.2]
      (by simp only [List.length_cons,List.length_nil]; decide)] ++
  List.replicate (if op = .permit then 7 else 9)
    (.reg (.dup (if op = .permit then 9 else 11))) ++
  [.push [op.internalTag.1,op.internalTag.2]
      (by simp only [List.length_cons,List.length_nil]; decide)]

end OwnerOpV2

private theorem callee_args (op : OwnerOpV2) {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    (run : Line.Run sevm (St b
      ((Sevm.dataWord sevm 36).toAdr.toB256 :: (Sevm.dataWord sevm 4).toAdr.toB256 ::
        (op.args sevm ++ [0x470,op.selector])) M G) op.calleeLine d) :
    ∃ G', d = St b (Bytes.toB256 [op.internalTag.1,op.internalTag.2] ::
      (op.args sevm ++ Bytes.toB256 [op.internalReturnTag.1,op.internalReturnTag.2] ::
        (Sevm.dataWord sevm 36).toAdr.toB256 :: (Sevm.dataWord sevm 4).toAdr.toB256 ::
          (op.args sevm ++ [0x470,op.selector]))) M G' := by
  cases op <;>
    (obtain ⟨_,step,run⟩ := Line.of_run_cons run
     obtain ⟨_,rfl⟩ := ri_push step
     repeat
       (obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_dup rfl step)
     obtain ⟨_,step,run⟩ := Line.of_run_cons run
     obtain ⟨_,rfl⟩ := ri_push step
     cases run
     exact ⟨_,rfl⟩)

private theorem enter_internal (op : OwnerOpV2) {F : Exec.Deriv} {post b : Devm} {M : Mem}
    (cut : CursorStateAt ImplV2.code ImplV2.cert F op.callEntry b
      ((Sevm.dataWord F.sevm 36).toAdr.toB256 :: (Sevm.dataWord F.sevm 4).toAdr.toB256 ::
        (op.args F.sevm ++ [0x470,op.selector])) M [op.returnTree])
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    Nonempty (CursorStateAt ImplV2.code ImplV2.cert F op.internalEntry b
      (op.args F.sevm ++ Bytes.toB256 [op.internalReturnTag.1,op.internalReturnTag.2] ::
        (Sevm.dataWord F.sevm 36).toAdr.toB256 :: (Sevm.dataWord F.sevm 4).toAdr.toB256 ::
          (op.args F.sevm ++ [0x470,op.selector])) M [op.internalReturn,op.returnTree]) := by
  have shape : op.callEntry = .dest (op.calleeLine.foldr SFunc.next
      (.callNext op.internalNumber op.internalReturn)) := by cases op <;> rfl
  rw [shape] at cut
  obtain ⟨opened⟩ := cut.destH ImplV2.cert_check success fork.stateGas
  obtain ⟨called⟩ := opened.lineH ImplV2.cert_check success fork.stateGas _ rfl
    (by intro ni member xi same; subst ni
        cases op <;>
          simp only [OwnerOpV2.calleeLine,OwnerOpV2.internalReturnTag,OwnerOpV2.internalTag,
            reduceCtorEq,ite_true,ite_false,List.replicate,List.cons_append,List.nil_append,
            List.mem_cons,List.not_mem_nil,or_self] at member)
    (callee_args op)
  exact called.callH ImplV2.cert_check success fork.stateGas (by cases op <;> rfl)

/-- The actual residual source after47ca has incremented the permit nonce. -/
def ownerV2PermitNonceTail : SFunc :=
  (SolcSignedQuery.bufferHeadLine
    [0x6e,0x71,0xed,0xae,0x12,0xb1,0xb9,0x7f,0x4d,0x1f,0x60,0x37,0x0f,0xef,0x10,0x10,
     0x5f,0xa2,0xfa,0xae,0x01,0x26,0x11,0x4a,0x16,0x9c,0x64,0x84,0x5d,0x61,0x26,0xc9]
    (by decide)).foldr SFunc.next
    (SolcSignedQuery.bufferBodyLine.foldr SFunc.next
      ((SolcSignedQuery.bufferTailLine 15 0x48 0x6d 0x4d 0x2c).foldr SFunc.next
        (.callNext 84 ImplV2.t_486d_c71)))

private theorem permit_nonce_prefix {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {s r v deadline value : B256} {spender owner : Adr} {S : List B256} {K : List SFunc}
    (cut : CursorStateAt ImplV2.code ImplV2.cert F ImplV2.t_475b_c71 b
      (s :: r :: v :: deadline :: value :: spender.toB256 :: owner.toB256 :: S) M K)
    (ptr : PtrMem 128 96 M)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    F.sevm.benvStat.time.toNat ≤ deadline.toNat ∧
    let nonce := b.getStorVal F.sevm.currentTarget (nonceSlot owner)
    let b' := afterSstoreH F.sevm (afterSloadH F.sevm b (nonceSlot owner)) (nonceSlot owner) (nonce + 1)
    let M' := (M.write 0 owner.toB256.toBytes).write 32 (17 : B256).toBytes
    PtrMem 128 96 M' ∧ Nonempty (CursorStateAt ImplV2.code ImplV2.cert F
      ownerV2PermitNonceTail b'
      (nonce ::32::64::owner.toB256::(0xffffffffffffffffffffffffffffffffffffffff : B256)::
        s::r::v::deadline::value::spender.toB256::owner.toB256::S) M' K) := by
  obtain ⟨opened⟩ := cut.destH ImplV2.cert_check success fork.stateGas
  obtain ⟨guard⟩ := opened.lineH ImplV2.cert_check success fork.stateGas
    [.reg .timestamp,.reg (.dup 4),.reg .lt,.reg .iszero,.push [0x47,0xca] (by decide)] rfl
    (by intro ni member xi same; subst ni
        simp only [List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    (by intro gas d run
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_timestamp step
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_dup rfl step
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_lt step
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_iszero step
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_push step
        cases run
        exact ⟨_,rfl⟩)
  obtain ⟨taken,⟨accepted⟩⟩ := SolcSignedQuery.guardSucc guard ImplV2.cert_check rfl success fork
  have bound := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero taken)
  obtain ⟨openedNonce⟩ := accepted.destH ImplV2.cert_check success fork.stateGas
  obtain ⟨updated⟩ := openedNonce.lineH ImplV2.cert_check success fork.stateGas
    (SolcSignedQuery.nonceLine 17) (by rfl)
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.nonceLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    (SolcSignedQuery.nonce_line ptr fork)
  exact ⟨bound,(ptr.write 0 owner.toB256 (.inl (by decide))).write 32 17 (.inl (by decide)),⟨updated⟩⟩

/-- The exact two mapping scratch hashes used by the V2 authorization-state read. -/
def ownerV2AuthCheckMemory (M : Mem) (owner : Adr) (nonce : B256) : Mem :=
  let M := (M.write 0 owner.toB256.toBytes).write 32 (16 : B256).toBytes
  (M.write 0 nonce.toBytes).write 32 (mapSlot owner.toB256 16).toBytes

private def authStateReadLine : List Ninst :=
  [.push [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] (by decide),
   .reg (.dup 2),
   .reg .and,
   .push [0] (by decide),
   .reg (.swap 0),
   .reg (.dup 1),
   .reg .mstore,
   .push [0x10] (by decide),
   .push [0x20] (by decide),
   .reg (.swap 0),
   .reg (.dup 1),
   .reg .mstore,
   .push [0x40] (by decide),
   .reg (.dup 0),
   .reg (.dup 3),
   .reg .keccak256,
   .reg (.dup 4),
   .reg (.dup 4),
   .reg .mstore,
   .reg (.swap 0),
   .reg (.swap 1),
   .reg .mstore,
   .reg (.dup 1),
   .reg .keccak256,
   .reg .sload,
   .push [0xff] (by decide),
   .reg .and,
   .push [2] (by decide),
   .reg (.dup 1),
   .reg .gt,
   .reg .iszero,
   .push [0x4c,0xd2] (by decide)]

private theorem authorization_state {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {nonce : B256} {owner : Adr} {S : List B256} {K : List SFunc}
    (cut : CursorStateAt ImplV2.code ImplV2.cert F ImplV2.t_4c93_c89 b
      (nonce :: owner.toB256 :: S) M K)
    (ptr : PtrMem 128 96 M)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    (255 &&& b.getStorVal F.sevm.currentTarget (authSlot owner nonce)) = 0 ∧
    let b' := afterSloadH F.sevm b (authSlot owner nonce)
    b'.state = b.state ∧ PtrMem 128 96 (ownerV2AuthCheckMemory M owner nonce) ∧
      Nonempty (CursorStateAt ImplV2.code ImplV2.cert F .ret b' S
        (ownerV2AuthCheckMemory M owner nonce) K) := by
  have p1 := (ptr.write 0 owner.toB256 (.inl (by decide))).write 32 16 (.inl (by decide))
  have p2 := (p1.write 0 nonce (.inl (by decide))).write 32 (mapSlot owner.toB256 16) (.inl (by decide))
  have read1 := p1.read_self (i := 0) (sz := 64) (by decide)
  have read2 := p2.read_self (i := 0) (sz := 64) (by decide)
  obtain ⟨opened⟩ := cut.destH ImplV2.cert_check success fork.stateGas
  obtain ⟨guard⟩ := opened.lineH ImplV2.cert_check success fork.stateGas authStateReadLine rfl
    (by intro ni member xi same; subst ni
        simp only [authStateReadLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    (by
      intro gas d run
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_push step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_dup rfl step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,state⟩ := ri_and step
      rw [B256.and_comm,ff20_and_word,toAdr_toB256] at state
      subst state
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_push step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_swap rfl step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_dup rfl step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_mstore step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_push step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_push step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_swap rfl step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_dup rfl step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_mstore step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_push step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_dup rfl step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_dup rfl step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,state⟩ := ri_keccak step
      rw [keccak_scratch] at state
      rw [show (Bytes.toB256 [0]).toNat = 0 from rfl,
        show (Bytes.toB256 [0x20]).toNat = 32 from rfl,
        show (Bytes.toB256 [0x40]).toNat = 64 from rfl,
        show Bytes.toB256 [0x10] = (16 : B256) from rfl, read1] at state
      subst state
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_dup rfl step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_dup rfl step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_mstore step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_swap rfl step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_swap rfl step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_mstore step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_dup rfl step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,state⟩ := ri_keccak step
      rw [keccak_scratch] at state
      rw [show (Bytes.toB256 [0]).toNat = 0 from rfl,
        show (Bytes.toB256 [0x20]).toNat = 32 from rfl,
        show (Bytes.toB256 [0x40]).toNat = 64 from rfl,
        read2] at state
      subst state
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_sloadH fork.bal step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_push step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_and step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_push step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_dup rfl step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_gt step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_iszero step
      obtain ⟨_,step,run⟩ := Line.of_run_cons run
      obtain ⟨_,rfl⟩ := ri_push step
      cases run
      exact ⟨_,rfl⟩)
  obtain ⟨inRange,⟨validEnum⟩⟩ := SolcSignedQuery.guardSucc guard ImplV2.cert_check rfl success fork
  obtain ⟨openedEnum⟩ := validEnum.destH ImplV2.cert_check success fork.stateGas
  obtain ⟨unusedGuard⟩ := openedEnum.lineH ImplV2.cert_check success fork.stateGas
    [.reg .eq,.push [0x4d,0x28] (by decide)] rfl
    (by intro ni member xi same; subst ni
        simp only [List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    (by intro gas d run
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_eq step
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_push step
        cases run
        exact ⟨_,rfl⟩)
  obtain ⟨unused,⟨accepted⟩⟩ := SolcSignedQuery.guardSucc unusedGuard ImplV2.cert_check rfl success fork
  obtain ⟨openedReturn⟩ := accepted.destH ImplV2.cert_check success fork.stateGas
  obtain ⟨returned⟩ := openedReturn.lineH ImplV2.cert_check success fork.stateGas [.reg .pop,.reg .pop] rfl
    (by intro ni member xi same; subst ni
        simp only [List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    (by intro gas d run
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_pop step
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_pop step
        cases run
        exact ⟨_,rfl⟩)
  refine ⟨eq_zero_of_iszero_ne_zero unused,?_,p2,⟨returned⟩⟩
  exact afterSloadH_state _ _ _

namespace OwnerOpV2

def internalStack (op : OwnerOpV2) (sevm : Sevm) : List B256 :=
  op.args sevm ++ Bytes.toB256 [op.internalReturnTag.1,op.internalReturnTag.2] ::
    (Sevm.dataWord sevm 36).toAdr.toB256 :: (Sevm.dataWord sevm 4).toAdr.toB256 ::
      (op.args sevm ++ [0x470,op.selector])

def validationReturn : OwnerOpV2 → SFunc
  | .permit => ImplV2.t_47ca_c71
  | .approveAuth => ImplV2.t_4982_c66
  | .increaseAuth => ImplV2.t_4631_c70
  | .decreaseAuth => ImplV2.t_4462_c72

def validationReturnTag : OwnerOpV2 → UInt8 × UInt8
  | .permit => (0x47,0xca)
  | .approveAuth => (0x49,0x82)
  | .increaseAuth => (0x46,0x31)
  | .decreaseAuth => (0x44,0x62)

def validationLine (op : OwnerOpV2) : List Ninst :=
  [.push [op.validationReturnTag.1,op.validationReturnTag.2]
     (by simp only [List.length_cons,List.length_nil]; decide),
   .reg (.dup 9),.reg (.dup 5),.reg (.dup 8),.reg (.dup 8),.push [0x4d,0x9e] (by decide)]

end OwnerOpV2

private theorem enter_validation (op : OwnerOpV2) (authorization : op ≠ .permit)
    {F : Exec.Deriv} {post b : Devm} {M : Mem}
    (cut : CursorStateAt ImplV2.code ImplV2.cert F op.internalEntry b
      (op.internalStack F.sevm) M [op.internalReturn,op.returnTree])
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    Nonempty (CursorStateAt ImplV2.code ImplV2.cert F ImplV2.t_4d9e_c83 b
      (Sevm.dataWord F.sevm 132 :: Sevm.dataWord F.sevm 100 :: Sevm.dataWord F.sevm 164 ::
        (Sevm.dataWord F.sevm 4).toAdr.toB256 ::
        Bytes.toB256 [op.validationReturnTag.1,op.validationReturnTag.2] :: op.internalStack F.sevm)
      M [op.validationReturn,op.internalReturn,op.returnTree]) := by
  have shape : op.internalEntry = .dest
      (op.validationLine.foldr SFunc.next (.callNext 83 op.validationReturn)) := by
    cases op <;> first | exact (authorization rfl).elim | rfl
  rw [shape] at cut
  obtain ⟨opened⟩ := cut.destH ImplV2.cert_check success fork.stateGas
  obtain ⟨called⟩ := opened.lineH ImplV2.cert_check success fork.stateGas _ rfl
    (by intro ni member xi same; subst ni
        simp only [OwnerOpV2.validationLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    (S' := Bytes.toB256 [0x4d,0x9e] :: Sevm.dataWord F.sevm 132 ::
      Sevm.dataWord F.sevm 100 :: Sevm.dataWord F.sevm 164 ::
      (Sevm.dataWord F.sevm 4).toAdr.toB256 ::
      Bytes.toB256 [op.validationReturnTag.1,op.validationReturnTag.2] :: op.internalStack F.sevm)
    (by intro gas d run
        cases op <;> first
        | exact (authorization rfl).elim
        | obtain ⟨_,step,run⟩ := Line.of_run_cons run
          obtain ⟨_,rfl⟩ := ri_push step
          obtain ⟨_,step,run⟩ := Line.of_run_cons run
          obtain ⟨_,rfl⟩ := ri_dup rfl step
          obtain ⟨_,step,run⟩ := Line.of_run_cons run
          obtain ⟨_,rfl⟩ := ri_dup rfl step
          obtain ⟨_,step,run⟩ := Line.of_run_cons run
          obtain ⟨_,rfl⟩ := ri_dup rfl step
          obtain ⟨_,step,run⟩ := Line.of_run_cons run
          obtain ⟨_,rfl⟩ := ri_dup rfl step
          obtain ⟨_,step,run⟩ := Line.of_run_cons run
          obtain ⟨_,rfl⟩ := ri_push step
          cases run
          exact ⟨_,rfl⟩)
  exact called.callH ImplV2.cert_check success fork.stateGas rfl

private theorem authorization_validity {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {before after nonce ret : B256} {owner : Adr} {S : List B256} {returnTree : SFunc} {K : List SFunc}
    (cut : CursorStateAt ImplV2.code ImplV2.cert F ImplV2.t_4d9e_c83 b
      (before :: after :: nonce :: owner.toB256 :: ret :: S) M (returnTree :: K))
    (ptr : PtrMem 128 96 M)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    after.toNat < F.sevm.benvStat.time.toNat ∧ F.sevm.benvStat.time.toNat < before.toNat ∧
    (255 &&& b.getStorVal F.sevm.currentTarget (authSlot owner nonce)) = 0 ∧
    let b' := afterSloadH F.sevm b (authSlot owner nonce)
    b'.state = b.state ∧ PtrMem 128 96 (ownerV2AuthCheckMemory M owner nonce) ∧
      Nonempty (CursorStateAt ImplV2.code ImplV2.cert F returnTree b' S
        (ownerV2AuthCheckMemory M owner nonce) K) := by
  obtain ⟨opened⟩ := cut.destH ImplV2.cert_check success fork.stateGas
  obtain ⟨afterGuard⟩ := opened.lineH ImplV2.cert_check success fork.stateGas
    [.reg (.dup 1),.reg .timestamp,.reg .gt,.push [0x4d,0xf6] (by decide)] rfl
    (by intro ni member xi same; subst ni
        simp only [List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    (by intro gas d run
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_dup rfl step
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_timestamp step
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_gt step
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_push step
        cases run
        exact ⟨_,rfl⟩)
  obtain ⟨afterTaken,⟨afterAccepted⟩⟩ := SolcSignedQuery.guardSucc afterGuard ImplV2.cert_check rfl success fork
  have afterBound : after.toNat < F.sevm.benvStat.time.toNat := by
    unfold B256.gtCheck at afterTaken
    split at afterTaken
    · exact B256.lt_iff_toNat_lt_toNat.mp ‹_ < _›
    · contradiction
  obtain ⟨openedBefore⟩ := afterAccepted.destH ImplV2.cert_check success fork.stateGas
  obtain ⟨beforeGuard⟩ := openedBefore.lineH ImplV2.cert_check success fork.stateGas
    [.reg (.dup 0),.reg .timestamp,.reg .lt,.push [0x4e,0x4e] (by decide)] rfl
    (by intro ni member xi same; subst ni
        simp only [List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    (by intro gas d run
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_dup rfl step
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_timestamp step
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_lt step
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_push step
        cases run
        exact ⟨_,rfl⟩)
  obtain ⟨beforeTaken,⟨beforeAccepted⟩⟩ := SolcSignedQuery.guardSucc beforeGuard ImplV2.cert_check rfl success fork
  have beforeBound : F.sevm.benvStat.time.toNat < before.toNat := by
    unfold B256.ltCheck at beforeTaken
    split at beforeTaken
    · exact B256.lt_iff_toNat_lt_toNat.mp ‹_ < _›
    · contradiction
  obtain ⟨openedCall⟩ := beforeAccepted.destH ImplV2.cert_check success fork.stateGas
  obtain ⟨call⟩ := openedCall.lineH ImplV2.cert_check success fork.stateGas
    [.push [0x4e,0x58] (by decide),.reg (.dup 4),.reg (.dup 4),.push [0x4c,0x93] (by decide)] rfl
    (by intro ni member xi same; subst ni
        simp only [List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    (by intro gas d run
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_push step
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_dup rfl step
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_dup rfl step
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_push step
        cases run
        exact ⟨_,rfl⟩)
  obtain ⟨called⟩ := call.callH ImplV2.cert_check success fork.stateGas rfl
  obtain ⟨unused,unchanged,ptr',⟨read⟩⟩ := authorization_state called ptr success fork
  obtain ⟨returned⟩ := read.retH ImplV2.cert_check success fork.stateGas
  obtain ⟨openedReturn⟩ := returned.destH ImplV2.cert_check success fork.stateGas
  obtain ⟨done⟩ := openedReturn.lineH ImplV2.cert_check success fork.stateGas
    [.reg .pop,.reg .pop,.reg .pop,.reg .pop] rfl
    (by intro ni member xi same; subst ni
        simp only [List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    (by intro gas d run
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_pop step
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_pop step
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_pop step
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_pop step
        cases run
        exact ⟨_,rfl⟩)
  exact ⟨afterBound,beforeBound,unused,unchanged,ptr',done.retH ImplV2.cert_check success fork.stateGas⟩

namespace OwnerOpV2

def prefixTree (op : OwnerOpV2) : SFunc :=
  if op = .permit then ownerV2PermitNonceTail else op.validationReturn

def prefixMemory (op : OwnerOpV2) (sevm : Sevm) : Mem :=
  if op = .permit then
    ((ownerV2GuardMemory sevm).write 0 (Sevm.dataWord sevm 4).toAdr.toB256.toBytes).write
      32 (17 : B256).toBytes
  else ownerV2AuthCheckMemory (ownerV2GuardMemory sevm) (Sevm.dataWord sevm 4).toAdr
    (Sevm.dataWord sevm 164)

def prefixStack (op : OwnerOpV2) (F : Exec.Deriv) : List B256 :=
  if op = .permit then
    F.devm.getStorVal F.sevm.currentTarget (nonceSlot (Sevm.dataWord F.sevm 4).toAdr) ::
      32::64::(Sevm.dataWord F.sevm 4).toAdr.toB256::
      (0xffffffffffffffffffffffffffffffffffffffff : B256)::op.internalStack F.sevm
  else op.internalStack F.sevm

def prefixState (op : OwnerOpV2) (F : Exec.Deriv) :=
  if op = .permit then
    F.devm.state.setStorVal F.sevm.currentTarget (nonceSlot (Sevm.dataWord F.sevm 4).toAdr)
      (F.devm.getStorVal F.sevm.currentTarget (nonceSlot (Sevm.dataWord F.sevm 4).toAdr) + 1)
  else F.devm.state

def validity (op : OwnerOpV2) (F : Exec.Deriv) : Prop :=
  if op = .permit then F.sevm.benvStat.time.toNat ≤ (Sevm.dataWord F.sevm 100).toNat
  else (Sevm.dataWord F.sevm 100).toNat < F.sevm.benvStat.time.toNat ∧
    F.sevm.benvStat.time.toNat < (Sevm.dataWord F.sevm 132).toNat ∧
    (255 &&& F.devm.getStorVal F.sevm.currentTarget
      (authSlot (Sevm.dataWord F.sevm 4).toAdr (Sevm.dataWord F.sevm 164))) = 0

end OwnerOpV2

/-- Facts derived from the actual source guards, never supplied as endpoint assumptions. -/
structure OwnerPrefixFactsV2 (op : OwnerOpV2) (F : Exec.Deriv) : Prop where
  nonpayable : F.sevm.value = 0
  calldata : op.calldataBound ≤ F.sevm.data.length.toB256.toNat
  unpaused : (255 &&& (F.devm.getStorVal F.sevm.currentTarget 1 /
    (0x10000000000000000000000000000000000000000 : B256))) = 0
  ownerAllowed : (255 &&& F.devm.getStorVal F.sevm.currentTarget
    (mapSlot (Sevm.dataWord F.sevm 4).toAdr.toB256 3)) = 0
  spenderAllowed : (255 &&& F.devm.getStorVal F.sevm.currentTarget
    (mapSlot (Sevm.dataWord F.sevm 36).toAdr.toB256 3)) = 0
  valid : op.validity F

/-- Every registered V2 owner operation reaches its actual struct-construction prefix.
Permit has already incremented nonce17, before the tail's explicit domain-slot15 SLOAD. The other three
operations have completed83/89 validation with no storage write. Hashing, signature
checks and query consumption remain downstream. -/
theorem ownerV2_source_prefix (op : OwnerOpV2) {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (selector : Sevm.selector F.sevm = op.selector)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    OwnerPrefixFactsV2 op F ∧
    ∃ b M, b.state = op.prefixState F ∧ M = op.prefixMemory F.sevm ∧ PtrMem 128 96 M ∧
      Nonempty (CursorStateAt ImplV2.code ImplV2.cert F op.prefixTree b
        (op.prefixStack F) M [op.internalReturn,op.returnTree]) := by
  obtain ⟨valueZero,sizeBound,pauseZero,ownerZero,spenderZero,b,M,state,mem,ptr,⟨guarded⟩⟩ :=
    root_guarded op pc code stack memory selector success fork
  obtain ⟨entered⟩ := enter_internal op guarded success fork
  by_cases permit : op = .permit
  · subst op
    obtain ⟨deadline,ptr',⟨updated⟩⟩ := permit_nonce_prefix entered ptr success fork
    have nonceEq : b.getStorVal F.sevm.currentTarget (nonceSlot (Sevm.dataWord F.sevm 4).toAdr) =
        F.devm.getStorVal F.sevm.currentTarget (nonceSlot (Sevm.dataWord F.sevm 4).toAdr) := by
      unfold Devm.getStorVal Devm.getAcct
      rw [state]
    rw [nonceEq] at updated
    refine ⟨⟨valueZero,sizeBound,pauseZero,ownerZero,spenderZero,deadline⟩,_,_,?_,?_,ptr',⟨updated⟩⟩
    · rw [afterSstoreH_state, afterSloadH_state, state]
      rfl
    · rw [OwnerOpV2.prefixMemory,ite_eq_left rfl]
      exact congrArg (fun m => (m.write 0 (Sevm.dataWord F.sevm 4).toAdr.toB256.toBytes).write
        32 (17 : B256).toBytes) mem
  · obtain ⟨called⟩ := enter_validation op permit entered success fork
    obtain ⟨afterBound,beforeBound,unused,unchanged,ptr',⟨validated⟩⟩ :=
      authorization_validity called ptr success fork
    have readEq : b.getStorVal F.sevm.currentTarget
        (authSlot (Sevm.dataWord F.sevm 4).toAdr (Sevm.dataWord F.sevm 164)) =
        F.devm.getStorVal F.sevm.currentTarget
          (authSlot (Sevm.dataWord F.sevm 4).toAdr (Sevm.dataWord F.sevm 164)) := by
      unfold Devm.getStorVal Devm.getAcct
      rw [state]
    rw [readEq] at unused
    have valid : op.validity F := by
      rw [OwnerOpV2.validity,ite_eq_right permit]
      exact ⟨afterBound,beforeBound,unused⟩
    refine ⟨⟨valueZero,sizeBound,pauseZero,ownerZero,spenderZero,valid⟩,
      afterSloadH F.sevm b (authSlot (Sevm.dataWord F.sevm 4).toAdr (Sevm.dataWord F.sevm 164)),
      _,?_,?_,ptr',?_⟩
    · rw [OwnerOpV2.prefixState,ite_eq_right permit]
      exact unchanged.trans state
    · rw [OwnerOpV2.prefixMemory,ite_eq_right permit]
      exact congrArg (fun m => ownerV2AuthCheckMemory m (Sevm.dataWord F.sevm 4).toAdr
        (Sevm.dataWord F.sevm 164)) mem
    · simp only [OwnerOpV2.prefixTree,OwnerOpV2.prefixStack,ite_eq_right permit]
      exact ⟨validated⟩

/-- Coverage uses the existing certified selector table, including signed decrease. -/
theorem ownerV2_source_prefix_of_owner_selector {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (member : Sevm.selector F.sevm ∈ selV2.owners)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    ∃ op : OwnerOpV2, Sevm.selector F.sevm = op.selector ∧ OwnerPrefixFactsV2 op F ∧
      ∃ b M, b.state = op.prefixState F ∧ M = op.prefixMemory F.sevm ∧ PtrMem 128 96 M ∧
        Nonempty (CursorStateAt ImplV2.code ImplV2.cert F op.prefixTree b
          (op.prefixStack F) M [op.internalReturn,op.returnTree]) := by
  rw [← OwnerOpV2.selectors_eq] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  have chosen : ∃ op : OwnerOpV2, Sevm.selector F.sevm = op.selector := by
    rcases member with permit | approve | increase | decrease
    · exact ⟨.permit,permit⟩
    · exact ⟨.approveAuth,approve⟩
    · exact ⟨.increaseAuth,increase⟩
    · exact ⟨.decreaseAuth,decrease⟩
  obtain ⟨op,selector⟩ := chosen
  exact ⟨op,selector,ownerV2_source_prefix op pc code stack memory selector success fork⟩

namespace OwnerOpV2

/-- Actual PUSH32 instruction words of the four checked constructors. -/
def typeWord : OwnerOpV2 → B256
  | .permit => 0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9
  | .approveAuth => 0x808c10407a796f3ef2c7ea38c0638ea9d2b8a1c63e3ca9e1f56ce84ae59df73c
  | .increaseAuth => 0x424222bb050a1f7f14017232a5671f2680a2d3420f504bd565cf03035c53198a
  | .decreaseAuth => 0xb70559e94cbda91958ebec07f9b65b3b490097c8d25c8dacd71105df1015b6d8

def comparison : OwnerOpV2 → SFunc
  | .permit => ImplV2.t_486d_c71
  | .approveAuth => ImplV2.t_4a15_c66
  | .increaseAuth => ImplV2.t_46c4_c70
  | .decreaseAuth => ImplV2.t_44f5_c72

def comparisonTag : OwnerOpV2 → UInt8 × UInt8
  | .permit => (0x48,0x6d)
  | .approveAuth => (0x4a,0x15)
  | .increaseAuth => (0x46,0xc4)
  | .decreaseAuth => (0x44,0xf5)

def structEnd (op : OwnerOpV2) : B256 := if op = .permit then 352 else 384

def structLength (op : OwnerOpV2) : B256 := if op = .permit then 192 else 224

def recoveryPointer (op : OwnerOpV2) : B256 := 98 + op.structEnd

def recoveryMemorySize (op : OwnerOpV2) : Nat := op.structEnd.toNat + 128

def sWord (op : OwnerOpV2) (sevm : Sevm) : B256 :=
  Sevm.dataWord sevm (if op = .permit then 196 else 260)

def rWord (op : OwnerOpV2) (sevm : Sevm) : B256 :=
  Sevm.dataWord sevm (if op = .permit then 164 else 228)

def vWord (op : OwnerOpV2) (sevm : Sevm) : B256 :=
  Sevm.dataWord sevm (if op = .permit then 132 else 196) &&& 255

/-- The domain read sees the actual prefix storage state, including any nonce-slot collision. -/
def queryDomain (op : OwnerOpV2) (F : Exec.Deriv) : B256 :=
  ((op.prefixState F).get F.sevm.currentTarget).stor.get 15

def structHash (op : OwnerOpV2) (F : Exec.Deriv) : B256 :=
  let owner := (Sevm.dataWord F.sevm 4).toAdr
  let spender := (Sevm.dataWord F.sevm 36).toAdr
  if op = .permit then SolcSignedQuery.sixWordHash op.typeWord owner spender
    (Sevm.dataWord F.sevm 68) (F.devm.getStorVal F.sevm.currentTarget (nonceSlot owner))
    (Sevm.dataWord F.sevm 100)
  else SolcSignedQuery.sevenWordHash op.typeWord owner spender (Sevm.dataWord F.sevm 68)
    (Sevm.dataWord F.sevm 100) (Sevm.dataWord F.sevm 132) (Sevm.dataWord F.sevm 164)

def digest (op : OwnerOpV2) (F : Exec.Deriv) : B256 :=
  ([0x19,0x01] ++ (op.queryDomain F).toBytes ++ (op.structHash F).toBytes : Bytes).keccak

def savedStack (op : OwnerOpV2) (sevm : Sevm) : List B256 := 128 :: op.internalStack sevm

def recoveryStackWith (op : OwnerOpV2) (sevm : Sevm) (digest domain : B256) : List B256 :=
  0 :: op.sWord sevm :: op.rWord sevm :: op.vWord sevm :: digest :: 0x4d93 :: digest ::
    0 :: 128 :: op.sWord sevm :: op.rWord sevm :: op.vWord sevm :: domain ::
    Bytes.toB256 [op.comparisonTag.1,op.comparisonTag.2] :: (Sevm.dataWord sevm 4).toAdr.toB256 ::
    op.savedStack sevm

def recoveryStack (op : OwnerOpV2) (F : Exec.Deriv) : List B256 :=
  op.recoveryStackWith F.sevm (op.digest F) (op.queryDomain F)

def recoveryContinuations (op : OwnerOpV2) : List SFunc :=
  [ImplV2.t_4d93_c84,op.comparison,op.internalReturn,op.returnTree]

end OwnerOpV2

private theorem permit_construct {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {nonce s r v deadline value : B256} {owner spender : Adr} {S : List B256} {K : List SFunc}
    (cut : CursorStateAt ImplV2.code ImplV2.cert F ownerV2PermitNonceTail b
      (nonce :: 32 :: 64 :: owner.toB256 :: (0xffffffffffffffffffffffffffffffffffffffff : B256) ::
        s :: r :: v :: deadline :: value :: spender.toB256 :: owner.toB256 :: S) M K)
    (ptr : PtrMem 128 96 M)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    Nonempty (CursorStateAt ImplV2.code ImplV2.cert F ImplV2.t_4d2c_c84
      (afterSloadH F.sevm b 15)
      (128 :: s :: r :: v :: b.getStorVal F.sevm.currentTarget 15 :: 0x486d :: owner.toB256 ::
        128 :: s :: r :: v :: deadline :: value :: spender.toB256 :: owner.toB256 :: S)
      (SolcSignedQuery.structMemory OwnerOpV2.permit.typeWord M owner spender value nonce deadline)
      (ImplV2.t_486d_c71 :: K)) := by
  obtain ⟨head⟩ := cut.lineH ImplV2.cert_check success fork.stateGas
    (SolcSignedQuery.bufferHeadLine OwnerOpV2.permit.typeWord.toBytes
      (by rw [B256.length_toBytes]))
    rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.bufferHeadLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    (SolcSignedQuery.buffer_head_line ptr)
  rw [B256.toB256_toBytes] at head
  obtain ⟨body⟩ := head.lineH ImplV2.cert_check success fork.stateGas SolcSignedQuery.bufferBodyLine rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.bufferBodyLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    SolcSignedQuery.buffer_body_line
  have ptrHead := (ptr.write 160 OwnerOpV2.permit.typeWord (.inr (by decide))).write
    192 owner.toB256 (.inr (by decide))
  have ptrBody : PtrMem 128 352
      (SolcSignedQuery.structBodyMemory
        (SolcSignedQuery.structHeadMemory OwnerOpV2.permit.typeWord M owner)
        spender value nonce deadline) :=
    (((ptrHead.write 224 spender.toB256 (.inr (by decide))).write 256 value (.inr (by decide))).write
      288 nonce (.inr (by decide))).write 320 deadline (.inr (by decide))
  obtain ⟨tail⟩ := body.lineH ImplV2.cert_check success fork.stateGas
    (SolcSignedQuery.bufferTailLine 15 0x48 0x6d 0x4d 0x2c) rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.bufferTailLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    (SolcSignedQuery.buffer_tail_line ptrBody fork)
  exact tail.callH ImplV2.cert_check success fork.stateGas rfl

private theorem authorization_construct (op : OwnerOpV2) (authorization : op ≠ .permit)
    {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {nonce validBefore validAfter value s r v : B256} {owner spender : Adr}
    {S : List B256} {K : List SFunc}
    (cut : CursorStateAt ImplV2.code ImplV2.cert F op.validationReturn b
      (s :: r :: v :: nonce :: validBefore :: validAfter :: value :: spender.toB256 ::
        owner.toB256 :: S) M K)
    (ptr : PtrMem 128 96 M)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    Nonempty (CursorStateAt ImplV2.code ImplV2.cert F ImplV2.t_4d2c_c84
      (afterSloadH F.sevm b 15)
      (128 :: s :: r :: v :: b.getStorVal F.sevm.currentTarget 15 ::
        Bytes.toB256 [op.comparisonTag.1,op.comparisonTag.2] :: owner.toB256 ::
        128 :: s :: r :: v :: nonce :: validBefore :: validAfter :: value ::
        spender.toB256 :: owner.toB256 :: S)
      (SolcSignedQuery.sevenWordMemory op.typeWord M owner spender value validAfter validBefore nonce)
      (op.comparison :: K)) := by
  have shape : op.validationReturn = .dest
      ((SolcSignedQuery.sevenWordHeadLine op.typeWord.toBytes (by rw [B256.length_toBytes])).foldr SFunc.next
        (SolcSignedQuery.sevenWordBodyLine.foldr SFunc.next
          ((SolcSignedQuery.sevenWordTailLine 15 op.comparisonTag.1 op.comparisonTag.2 0x4d 0x2c).foldr
            SFunc.next (.callNext 84 op.comparison)))) := by
    cases op
    · exact (authorization rfl).elim
    · rfl
    · rfl
    · rfl
  rw [shape] at cut
  obtain ⟨opened⟩ := cut.destH ImplV2.cert_check success fork.stateGas
  obtain ⟨head⟩ := opened.lineH ImplV2.cert_check success fork.stateGas
    (SolcSignedQuery.sevenWordHeadLine op.typeWord.toBytes (by rw [B256.length_toBytes])) rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.sevenWordHeadLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    (SolcSignedQuery.seven_word_head_line ptr)
  rw [B256.toB256_toBytes] at head
  obtain ⟨body⟩ := head.lineH ImplV2.cert_check success fork.stateGas SolcSignedQuery.sevenWordBodyLine rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.sevenWordBodyLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    SolcSignedQuery.seven_word_body_line
  have ptrHead := (ptr.write 160 op.typeWord (.inr (by decide))).write 192 owner.toB256 (.inr (by decide))
  have ptrBody : PtrMem 128 384
      (SolcSignedQuery.sevenWordBodyMemory (SolcSignedQuery.structHeadMemory op.typeWord M owner)
        spender value validAfter validBefore nonce) :=
    ((((ptrHead.write 224 spender.toB256 (.inr (by decide))).write 256 value (.inr (by decide))).write
      288 validAfter (.inr (by decide))).write 320 validBefore (.inr (by decide))).write
      352 nonce (.inr (by decide))
  obtain ⟨tail⟩ := body.lineH ImplV2.cert_check success fork.stateGas
    (SolcSignedQuery.sevenWordTailLine 15 op.comparisonTag.1 op.comparisonTag.2 0x4d 0x2c) rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.sevenWordTailLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    (SolcSignedQuery.seven_word_tail_line ptrBody fork)
  exact tail.callH ImplV2.cert_check success fork.stateGas rfl

private theorem query_call91 {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {p len s r v domain hash ret : B256} {owner : Adr} {S : List B256} {K : List SFunc}
    (cut : CursorStateAt ImplV2.code ImplV2.cert F ImplV2.t_4d2c_c84 b
      (128 :: s :: r :: v :: domain :: ret :: owner.toB256 :: S) M K)
    (layout : p = 352 ∨ p = 384) (ptr : PtrMem p p.toNat M)
    (length : memWord M 128 = len) (fit : 160 + len.toNat ≤ p.toNat)
    (hashRead : (M.read 160 len.toNat).1.keccak = hash)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    let digest := ([0x19,0x01] ++ domain.toBytes ++ hash.toBytes : Bytes).keccak
    Nonempty (CursorStateAt ImplV2.code ImplV2.cert F ImplV2.t_4fbb_c91 b
      (s :: r :: v :: digest :: 0x4d93 :: digest :: 0 :: 128 ::
        s :: r :: v :: domain :: ret :: owner.toB256 :: S)
      (SolcSignedQuery.typedMemoryAt p M domain hash) (ImplV2.t_4d93_c84 :: K)) := by
  obtain ⟨opened⟩ := cut.destH ImplV2.cert_check success fork.stateGas
  obtain ⟨hashed⟩ := opened.lineH ImplV2.cert_check success fork.stateGas SolcSignedQuery.structHashLine rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.structHashLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    (SolcSignedQuery.struct_hash_line_at ptr length fit hashRead)
  obtain ⟨words⟩ := hashed.lineH ImplV2.cert_check success fork.stateGas SolcSignedQuery.typedWordsLine rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.typedWordsLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    (SolcSignedQuery.typed_words_line_at layout ptr)
  obtain ⟨ptrWords,ptrTyped,lengthTyped,bytesTyped⟩ := SolcSignedQuery.typed_memory_facts_at layout ptr
  obtain ⟨sized⟩ := words.lineH ImplV2.cert_check success fork.stateGas SolcSignedQuery.typedLengthLine rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.typedLengthLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    (SolcSignedQuery.typed_length_line_at ptrWords)
  obtain ⟨args⟩ := sized.lineH ImplV2.cert_check success fork.stateGas
    (SolcSignedQuery.typedHashLine 0x4d 0x93 0x4f 0xbb) rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.typedHashLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    (SolcSignedQuery.typed_hash_line_at (p := p) ptrTyped lengthTyped
      (by rcases layout with rfl | rfl <;> decide)
      (by rcases layout with rfl | rfl <;> decide) (congrArg Bytes.keccak bytesTyped))
  exact args.callH ImplV2.cert_check success fork.stateGas rfl

private theorem signature_recovery_cut {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {s r v : B256} {S : List B256} {K : List SFunc}
    (cut : CursorStateAt ImplV2.code ImplV2.cert F ImplV2.t_4fbb_c91 b
      (s :: r :: v :: S) M K)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    ∃ reached : CursorStateAt ImplV2.code ImplV2.cert F ImplV2.t_50a4_c6 b
      (0 :: s :: r :: v :: S) M K, reached.node.pc = 0x50a4 := by
  obtain ⟨opened⟩ := cut.destH ImplV2.cert_check success fork.stateGas
  obtain ⟨low⟩ := opened.lineH ImplV2.cert_check success fork.stateGas
    (SolcSignedQuery.lowSLine 0x50 0x36) rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.lowSLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    SolcSignedQuery.lows_line
  obtain ⟨_,⟨validS⟩⟩ := SolcSignedQuery.guardSucc low ImplV2.cert_check rfl success fork
  obtain ⟨openedV⟩ := validS.destH ImplV2.cert_check success fork.stateGas
  obtain ⟨v27⟩ := openedV.lineH ImplV2.cert_check success fork.stateGas
    (SolcSignedQuery.v27Line 0x50 0x4e) rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.v27Line,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    SolcSignedQuery.v27_line
  have alternatives : ∃ flag, Nonempty (CursorStateAt ImplV2.code ImplV2.cert F
      ImplV2.t_504e_c6 b (flag :: 0 :: s :: r :: v :: S) M K) := by
    by_cases taken : B256.eqCheck (B256.eqCheck (B256.eqCheck 27 (255 &&& v)) 0) 0 ≠ 0
    · exact ⟨_,v27.toSuccH ImplV2.cert_check success fork.stateGas taken rfl⟩
    · have zero := not_not.mp taken
      rw [zero] at v27
      obtain ⟨otherV⟩ := v27.toZeroH ImplV2.cert_check success fork.stateGas
      obtain ⟨v28⟩ := otherV.lineH ImplV2.cert_check success fork.stateGas SolcSignedQuery.v28Line rfl
        (by intro ni member xi same; subst ni
            simp only [SolcSignedQuery.v28Line,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
        SolcSignedQuery.v28_line
      exact ⟨_,⟨v28⟩⟩
  obtain ⟨flag,⟨before⟩⟩ := alternatives
  obtain ⟨opened⟩ := before.destH ImplV2.cert_check success fork.stateGas
  obtain ⟨guard⟩ := opened.lineH ImplV2.cert_check success fork.stateGas
    [.reg .iszero,.push [0x50,0xa4] (by decide)] rfl
    (by intro ni member xi same; subst ni
        simp only [List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    (by intro gas d run
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_iszero step
        obtain ⟨_,step,run⟩ := Line.of_run_cons run
        obtain ⟨_,rfl⟩ := ri_push step
        cases run
        exact ⟨_,rfl⟩)
  obtain ⟨_,reached,actualPc⟩ := SolcSignedQuery.guardSucc_pc guard ImplV2.cert_check rfl success fork
  exact ⟨reached,actualPc⟩

namespace OwnerOpV2

def outerStack (op : OwnerOpV2) (sevm : Sevm) : List B256 :=
  Bytes.toB256 [op.internalReturnTag.1,op.internalReturnTag.2] ::
    (Sevm.dataWord sevm 36).toAdr.toB256 :: (Sevm.dataWord sevm 4).toAdr.toB256 ::
    (op.args sevm ++ [0x470,op.selector])

theorem internalStack_eq (op : OwnerOpV2) (sevm : Sevm) :
    op.internalStack sevm = op.args sevm ++ op.outerStack sevm := rfl

end OwnerOpV2

private theorem constructor_cut (op : OwnerOpV2) {F : Exec.Deriv} {post b : Devm} {M : Mem}
    (cut : CursorStateAt ImplV2.code ImplV2.cert F op.prefixTree b (op.prefixStack F) M
      [op.internalReturn,op.returnTree])
    (ptr : PtrMem 128 96 M)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    ∃ Ms, PtrMem op.structEnd op.structEnd.toNat Ms ∧ memWord Ms 128 = op.structLength ∧
      (Ms.read 160 op.structLength.toNat).1.keccak = op.structHash F ∧
      Nonempty (CursorStateAt ImplV2.code ImplV2.cert F ImplV2.t_4d2c_c84
        (afterSloadH F.sevm b 15)
        (128 :: op.sWord F.sevm :: op.rWord F.sevm :: op.vWord F.sevm ::
          b.getStorVal F.sevm.currentTarget 15 :: Bytes.toB256 [op.comparisonTag.1,op.comparisonTag.2] ::
          (Sevm.dataWord F.sevm 4).toAdr.toB256 :: op.savedStack F.sevm)
        Ms [op.comparison,op.internalReturn,op.returnTree]) := by
  let owner := (Sevm.dataWord F.sevm 4).toAdr
  let spender := (Sevm.dataWord F.sevm 36).toAdr
  by_cases permit : op = .permit
  · subst op
    obtain ⟨constructed⟩ := permit_construct cut ptr success fork
    obtain ⟨ptrStruct,lengthStruct,hashStruct⟩ := SolcSignedQuery.struct_memory_facts
      (tag := OwnerOpV2.permit.typeWord) (owner := owner) (spender := spender)
      (value := Sevm.dataWord F.sevm 68)
      (nonce := F.devm.getStorVal F.sevm.currentTarget (nonceSlot owner))
      (deadline := Sevm.dataWord F.sevm 100) ptr
    generalize image : SolcSignedQuery.structMemory OwnerOpV2.permit.typeWord M owner spender
      (Sevm.dataWord F.sevm 68) (F.devm.getStorVal F.sevm.currentTarget (nonceSlot owner))
      (Sevm.dataWord F.sevm 100) = Ms at constructed ptrStruct lengthStruct hashStruct
    exact ⟨Ms,ptrStruct,lengthStruct,hashStruct,⟨constructed⟩⟩
  · have argsShape : op.args F.sevm =
        [Sevm.dataWord F.sevm 260,Sevm.dataWord F.sevm 228,Sevm.dataWord F.sevm 196 &&& 255,
         Sevm.dataWord F.sevm 164,Sevm.dataWord F.sevm 132,Sevm.dataWord F.sevm 100,
         Sevm.dataWord F.sevm 68,spender.toB256,owner.toB256] := by
      cases op
      · exact (permit rfl).elim
      · rfl
      · rfl
      · rfl
    have stackShape := op.internalStack_eq F.sevm
    rw [argsShape] at stackShape
    rw [OwnerOpV2.prefixTree,ite_eq_right permit,OwnerOpV2.prefixStack,ite_eq_right permit,
      stackShape] at cut
    obtain ⟨constructed⟩ := authorization_construct op permit cut ptr success fork
    obtain ⟨ptrStruct,lengthStruct,hashStruct⟩ := SolcSignedQuery.seven_word_memory_facts
      (tag := op.typeWord) (owner := owner) (spender := spender)
      (value := Sevm.dataWord F.sevm 68) (validAfter := Sevm.dataWord F.sevm 100)
      (validBefore := Sevm.dataWord F.sevm 132) (nonce := Sevm.dataWord F.sevm 164) ptr
    generalize image : SolcSignedQuery.sevenWordMemory op.typeWord M owner spender
      (Sevm.dataWord F.sevm 68) (Sevm.dataWord F.sevm 100) (Sevm.dataWord F.sevm 132)
      (Sevm.dataWord F.sevm 164) = Ms at constructed ptrStruct lengthStruct hashStruct
    refine ⟨Ms,?_,?_,?_,?_⟩
    · rw [OwnerOpV2.structEnd,ite_eq_right permit]
      exact ptrStruct
    · simpa only [OwnerOpV2.structLength,ite_eq_right permit] using lengthStruct
    · rw [OwnerOpV2.structLength,ite_eq_right permit,OwnerOpV2.structHash,ite_eq_right permit]
      exact hashStruct
    · simp only [OwnerOpV2.sWord,OwnerOpV2.rWord,OwnerOpV2.vWord,ite_eq_right permit,
        OwnerOpV2.savedStack,stackShape]
      exact ⟨constructed⟩

/-- Every existing V2 owner selector derives its full actual50a4 query registers and continuations. -/
theorem ownerV2_query_entry (op : OwnerOpV2) {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (selector : Sevm.selector F.sevm = op.selector)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    ∃ (b : Devm) (M : Mem) (R : Exec.Deriv) (κ : Cursor),
      R.pc = 0x50a4 ∧ Exec.Deriv.ExecFreeUntil F R ∧ R.sevm = F.sevm ∧ R.exn = F.exn ∧
      CursorOK ImplV2.code ImplV2.cert R κ ∧ κ.f = ImplV2.t_50a4_c6 ∧
      κ.K.map Cont.f = op.recoveryContinuations ∧
      (∃ G, R.devm = St b (op.recoveryStack F) M G) ∧
      PtrMem op.recoveryPointer op.recoveryMemorySize M ∧ b.getCode 1 = F.devm.getCode 1 ∧
      b.state = op.prefixState F := by
  obtain ⟨_,b,M,state,mem,ptr,⟨before⟩⟩ :=
    ownerV2_source_prefix op pc code stack memory selector success fork
  obtain ⟨Ms,ptrStruct,lengthStruct,hashStruct,⟨constructed⟩⟩ :=
    constructor_cut op before ptr success fork
  have layout : op.structEnd = 352 ∨ op.structEnd = 384 := by
    cases op
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
  have fit : 160 + op.structLength.toNat ≤ op.structEnd.toNat := by cases op <;> decide
  obtain ⟨at91⟩ := query_call91 constructed layout ptrStruct lengthStruct fit hashStruct success fork
  have domainEq : b.getStorVal F.sevm.currentTarget 15 = op.queryDomain F := by
    unfold Devm.getStorVal Devm.getAcct OwnerOpV2.queryDomain
    rw [state]
  have ptrFinal := (SolcSignedQuery.typed_memory_facts_at layout
    (domain := b.getStorVal F.sevm.currentTarget 15) (hash := op.structHash F) ptrStruct).2.1
  rw [domainEq] at at91 ptrFinal
  generalize image : SolcSignedQuery.typedMemoryAt op.structEnd Ms (op.queryDomain F)
    (op.structHash F) = Mt at at91 ptrFinal
  obtain ⟨reached,actualPc⟩ := signature_recovery_cut at91 success fork
  obtain ⟨gas,actualState⟩ := reached.state
  have registers : ∃ G, reached.node.devm = St (afterSloadH F.sevm b 15) (op.recoveryStack F) Mt G :=
    ⟨gas,actualState⟩
  have readState : (afterSloadH F.sevm b 15).state = b.state := by
    exact afterSloadH_state _ _ _
  refine ⟨afterSloadH F.sevm b 15,Mt,reached.node,reached.cursor,actualPc,reached.free,
    reached.sevm_eq,reached.exn_eq,reached.placed,reached.tree,reached.continuations,registers,
    ptrFinal,?_,readState.trans state⟩
  unfold Devm.getCode Devm.getAcct
  rw [readState,state]
  by_cases permit : op = .permit
  · rw [OwnerOpV2.prefixState,ite_eq_left permit]
    exact Devm.setStorVal_getCode F.devm F.sevm.currentTarget
      (nonceSlot (Sevm.dataWord F.sevm 4).toAdr)
      (F.devm.getStorVal F.sevm.currentTarget (nonceSlot (Sevm.dataWord F.sevm 4).toAdr) + 1) 1
  · rw [OwnerOpV2.prefixState,ite_eq_right permit]

namespace OwnerOpV2

def comparisonReject : OwnerOpV2 → SFunc
  | .permit => ImplV2.t_4889_c71
  | .approveAuth => ImplV2.t_4a31_c66
  | .increaseAuth => ImplV2.t_46e0_c70
  | .decreaseAuth => ImplV2.t_4511_c72

def comparisonSuccess : OwnerOpV2 → SFunc
  | .permit => ImplV2.t_48ef_c71
  | .approveAuth => ImplV2.t_4a97_c66
  | .increaseAuth => ImplV2.t_4746_c70
  | .decreaseAuth => ImplV2.t_4577_c72

def comparisonSuccessTag : OwnerOpV2 → UInt8 × UInt8
  | .permit => (0x48,0xef)
  | .approveAuth => (0x4a,0x97)
  | .increaseAuth => (0x47,0x46)
  | .decreaseAuth => (0x45,0x77)

end OwnerOpV2

private theorem owner_comparison (op : OwnerOpV2) {N : Exec.Deriv} {κ : Cursor}
    {post : Devm} {adr : Adr} {owner : B256} {S : List B256}
    (placed : CursorOK ImplV2.code ImplV2.cert N κ) (tree : κ.f = op.comparison)
    (stack : N.devm.stack = adr.toB256 :: owner :: S)
    (success : N.exn = .ok post) (fork : NeutralFork N.sevm.benvStat.fork) :
    owner = adr.toB256 := by
  have first : CursorStateAt ImplV2.code ImplV2.cert N op.comparison N.devm
      (adr.toB256 :: owner :: S) N.devm.memory (κ.K.map Cont.f) :=
    ⟨N,κ,.refl _,rfl,rfl,placed,tree,⟨_,St.self stack rfl⟩,rfl⟩
  have shape : op.comparison = .dest
      ((SolcSignedQuery.maskedOwnerLine op.comparisonSuccessTag.1 op.comparisonSuccessTag.2).foldr
        SFunc.next (.branch op.comparisonReject op.comparisonSuccess)) := by cases op <;> rfl
  rw [shape] at first
  obtain ⟨opened⟩ := first.destH ImplV2.cert_check success fork.stateGas
  obtain ⟨guard⟩ := opened.lineH ImplV2.cert_check success fork.stateGas
    (SolcSignedQuery.maskedOwnerLine op.comparisonSuccessTag.1 op.comparisonSuccessTag.2) rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.maskedOwnerLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    SolcSignedQuery.masked_owner_line
  obtain ⟨equal,_⟩ := SolcSignedQuery.guardSucc guard ImplV2.cert_check
    (by cases op <;> rfl) success fork
  have answerEq : adr.toB256 = owner := by
    unfold B256.eqCheck at equal
    by_contra different
    exact equal (ite_eq_right different)
  exact answerEq.symm

private theorem owner_return (op : OwnerOpV2) {N : Exec.Deriv} {κ : Cursor} {post : Devm}
    {adr : Adr} {digest s r v domain owner : B256} {S : List B256} {K : List SFunc}
    (placed : CursorOK ImplV2.code ImplV2.cert N κ)
    (tree : κ.f = ImplV2.t_4d93_c84)
    (stack : N.devm.stack = adr.toB256 :: digest :: 0 :: 128 :: s :: r :: v :: domain ::
      Bytes.toB256 [op.comparisonTag.1,op.comparisonTag.2] :: owner :: S)
    (continuations : κ.K.map Cont.f = op.comparison :: K)
    (success : N.exn = .ok post) (fork : NeutralFork N.sevm.benvStat.fork) :
    ∃ (Q : Exec.Deriv) (next : Cursor), Exec.Deriv.ExecFreeUntil N Q ∧
      Q.sevm = N.sevm ∧ Q.exn = N.exn ∧ CursorOK ImplV2.code ImplV2.cert Q next ∧
      next.f = op.comparison ∧ next.K.map Cont.f = K ∧
      Q.devm.stack = adr.toB256 :: owner :: S ∧ owner = adr.toB256 := by
  obtain ⟨Q,next,span,sameEnv,sameExn,finalPlaced,callerTree,callerK,returned⟩ :=
    placed.quietReturnH ImplV2.cert_check success fork.stateGas (E := []) (by rfl) (by rfl)
      (by rw [tree]; rfl) (by rw [tree]; rfl) continuations
  rw [tree,St.self stack rfl] at returned
  obtain ⟨gas,state⟩ := SolcSignedQuery.recovery_epilogue returned
  have comparisonStack : Q.devm.stack = adr.toB256 :: owner :: S := by rw [state,St.stack]
  have equal := owner_comparison op finalPlaced callerTree comparisonStack
    (sameExn.trans success) (by rw [sameEnv]; exact fork)
  exact ⟨Q,next,span,sameEnv,sameExn,finalPlaced,callerTree,callerK,comparisonStack,equal⟩

/-- Existing owner-selector coverage produces the actual query/native answer and real owner comparison.
Every native-consumer message/slot/payment/return conjunct is retained. Failed invocations and history
are separate scopes; address1 nondelegation and NeutralFork are the explicit local premises. -/
theorem ownerV2_query_consumed {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (member : Sevm.selector F.sevm ∈ selV2.owners)
    (nodeleg : getDelegatedCodeAddress (F.devm.getCode 1) = none)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    ∃ (op : OwnerOpV2) (R : Exec.Deriv) (call : CallOccurrenceStep R .staticcall)
      (parent child : Devm) (gas : Nat) (N : Exec.Deriv) (returned : Cursor)
      (Q : Exec.Deriv) (next : Cursor),
      let owner := (Sevm.dataWord F.sevm 4).toAdr
      let input := (op.digest F).toBytes ++ (op.vWord F.sevm).toBytes ++
        (op.rWord F.sevm).toBytes ++ (op.sWord F.sevm).toBytes
      let msg := callMsg call.occurrence.node.sevm parent gas 0
        call.occurrence.node.sevm.currentTarget 1 1 true true input
        (call.occurrence.node.devm.getCode 1) false
      Sevm.selector F.sevm = op.selector ∧
      R.pc = 0x50a4 ∧ Exec.Deriv.ExecFreeUntil F R ∧ R.sevm = F.sevm ∧ R.exn = F.exn ∧
      call.occurrence.node.pc = 0x50ef ∧ Exec.Deriv.ExecFreeUntil R call.occurrence.node ∧
      call.occurrence.node.sevm = F.sevm ∧
      Ninst.step ⟨call.occurrence.node.pc,call.occurrence.node.sevm,call.occurrence.node.devm⟩
        (.exec .staticcall) = .spawn (Frame.ofCall msg)
          (Resume.call parent op.recoveryPointer.toNat 32) (call.occurrence.node.pc + 1) ∧
      ProcessMessage msg call.occurrence.slot (.ok child) ∧ call.occurrence.slot = .none ∧
      (Frame.ofCall msg).enter = .done
        ((Frame.ofCall msg).settle (executePrecomp (initEvm (msg.withBenv msg.benv)) 1)) ∧
      gasEcrecover ≤ gas ∧ child.error.isSome = false ∧ child.output = owner.toB256.toBytes ∧
      ecrecoverOutput input = owner.toB256.toBytes ∧ owner ≠ 0 ∧
      call.returned.devm.returnData = owner.toB256.toBytes ∧
      Exec.Deriv.ExecFreeUntil call.returned N ∧ N.exn = R.exn ∧ N.sevm = R.sevm ∧
      CursorOK ImplV2.code ImplV2.cert N returned ∧ returned.f = ImplV2.t_4d93_c84 ∧
      returned.K.map Cont.f = [op.comparison,op.internalReturn,op.returnTree] ∧
      N.devm.stack = owner.toB256 :: op.digest F :: 0 :: 128 ::
        op.sWord F.sevm :: op.rWord F.sevm :: op.vWord F.sevm :: op.queryDomain F ::
        Bytes.toB256 [op.comparisonTag.1,op.comparisonTag.2] :: owner.toB256 :: op.savedStack F.sevm ∧
      Exec.Deriv.ExecFreeUntil N Q ∧ Q.sevm = N.sevm ∧ Q.exn = N.exn ∧
      CursorOK ImplV2.code ImplV2.cert Q next ∧ next.f = op.comparison ∧
      next.K.map Cont.f = [op.internalReturn,op.returnTree] ∧
      Q.devm.stack = owner.toB256 :: owner.toB256 :: op.savedStack F.sevm ∧
      Exec.Deriv.ExecFreeUntil call.returned Q := by
  obtain ⟨op,selector,_⟩ := ownerV2_source_prefix_of_owner_selector pc code stack memory member success fork
  obtain ⟨b,M,R,κ,actualPc,origin,sameEnv,sameExn,placed,tree,continuations,
    ⟨G,state⟩,ptr,code1,_⟩ := ownerV2_query_entry op pc code stack memory selector success fork
  dsimp only [OwnerOpV2.recoveryStack,OwnerOpV2.recoveryStackWith] at state
  obtain ⟨call,parent,child,gas,adr,N,returned,callPc,beforeSpan,spawned,process,emptySlot,
    native,paid,clean,childOutput,output,nonzero,returnData,suffix,suffixExn,suffixEnv,
    finalPlaced,callerTree,callerK,callerStack⟩ :=
    recoveryV2_consumes placed tree actualPc state ptr (by cases op <;> decide)
      (by cases op <;> decide) (by rw [code1]; exact nodeleg) continuations
      (sameExn.trans success) (by rw [sameEnv]; exact fork)
  obtain ⟨Q,next,epilogue,comparisonEnv,comparisonExn,comparisonPlaced,comparisonTree,
    comparisonK,comparisonStack,ownerEq⟩ := owner_return op finalPlaced callerTree callerStack callerK
      ((suffixExn.trans sameExn).trans success) (by rw [suffixEnv,sameEnv]; exact fork)
  have mask : (255 &&& op.vWord F.sevm) = op.vWord F.sevm := by
    unfold OwnerOpV2.vWord
    rw [B256.and_comm,B256.and_idem_right]
  rw [mask] at spawned process native output
  rw [← ownerEq] at childOutput output returnData callerStack comparisonStack
  have ownerAdrEq : (Sevm.dataWord F.sevm 4).toAdr = adr := by
    simpa only [toAdr_toB256] using congrArg B256.toAdr ownerEq
  have ownerNonzero : (Sevm.dataWord F.sevm 4).toAdr ≠ 0 := by
    intro vanished
    exact nonzero (ownerAdrEq.symm.trans vanished)
  exact ⟨op,R,call,parent,child,gas,N,returned,Q,next,selector,actualPc,origin,sameEnv,sameExn,
    callPc,beforeSpan,(Blanc.Exec.Deriv.ParentPrefix.sevm_eq beforeSpan.1).trans sameEnv,
    spawned,process,emptySlot,native,paid,clean,childOutput,output,ownerNonzero,returnData,
    suffix,suffixExn,suffixEnv,finalPlaced,callerTree,callerK,callerStack,
    epilogue,comparisonEnv,comparisonExn,comparisonPlaced,comparisonTree,comparisonK,comparisonStack,
    suffix.trans epilogue⟩

end Blanc.Lift.Usdc
