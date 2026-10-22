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
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    F.sevm.value = 0 ∧ 4 ≤ F.sevm.data.length.toB256.toNat ∧
      Nonempty (CursorStateAt ImplV2.code ImplV2.cert F ImplV2.t_001a_c0 F.devm []
        (Mem.empty.write 64 (128 : B256).toBytes) []) := by
  have first : CursorStateAt ImplV2.code ImplV2.cert F ImplV2.t_0000_c0
      F.devm [] Mem.empty [] :=
    ⟨F, Cursor.start ImplV2.cert, .refl _, rfl, rfl,
      cursor_start ImplV2.cert_check pc code, rfl, ⟨_, St.self stack memory⟩, rfl⟩
  obtain ⟨guard⟩ := first.line ImplV2.cert_check success fork
    (SolcSignedQuery.prologue 0 16) rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.prologue,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    SolcSignedQuery.prologue_line
  obtain ⟨taken,⟨entered⟩⟩ := SolcSignedQuery.guardSucc guard ImplV2.cert_check rfl success fork
  have valueZero := eq_zero_of_iszero_ne_zero taken
  obtain ⟨opened⟩ := entered.dest ImplV2.cert_check success fork
  obtain ⟨guardSize⟩ := opened.line ImplV2.cert_check success fork
    (SolcSignedQuery.sizeLine 3 0x4c) rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.sizeLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    SolcSignedQuery.size_line
  obtain ⟨zero, continued⟩ := SolcSignedQuery.guardZero guardSize ImplV2.cert_check rfl success fork
  exact ⟨valueZero, toNat_ge_of_ltCheck_eq_zero zero, continued⟩

private theorem root_selected {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    F.sevm.value = 0 ∧ 4 ≤ F.sevm.data.length.toB256.toNat ∧
      Nonempty (CursorStateAt ImplV2.code ImplV2.cert F
        ((SolcSignedQuery.compareLine .gt 0x8a 0x6d 0xb9 0xc3 0x01 0xbd).foldr
          SFunc.next (.branch ImplV2.t_002b_c0 ImplV2.t_01bd_c0)) F.devm [Sevm.selector F.sevm]
        (Mem.empty.write 64 (128 : B256).toBytes) []) := by
  obtain ⟨valueZero,sizeBound,⟨before⟩⟩ := root_ready pc code stack memory success fork
  obtain ⟨selected⟩ := before.line ImplV2.cert_check success fork SolcSignedQuery.selectorLine rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.selectorLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    SolcSignedQuery.selector_line
  exact ⟨valueZero,sizeBound,⟨selected⟩⟩

private theorem root_wrapper (op : OwnerOpV2) {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (selector : Sevm.selector F.sevm = op.selector)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
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
    obtain ⟨opened3⟩ := c2.dest ImplV2.cert_check success fork
    obtain ⟨c3⟩ := SolcSignedQuery.selector_gt_succ opened3 ImplV2.cert_check (by decide) success fork
    obtain ⟨opened4⟩ := c3.dest ImplV2.cert_check success fork
    obtain ⟨c4⟩ := SolcSignedQuery.selector_eq_zero opened4 ImplV2.cert_check (by decide) success fork
    obtain ⟨c5⟩ := SolcSignedQuery.selector_eq_zero c4 ImplV2.cert_check (by decide) success fork
    exact SolcSignedQuery.selector_eq_succ c5 ImplV2.cert_check (by decide) rfl success fork

  | approveAuth =>
    obtain ⟨c0⟩ := SolcSignedQuery.selector_gt_zero selected ImplV2.cert_check (by decide) success fork
    obtain ⟨c1⟩ := SolcSignedQuery.selector_gt_zero c0 ImplV2.cert_check (by decide) success fork
    obtain ⟨c2⟩ := SolcSignedQuery.selector_gt_zero c1 ImplV2.cert_check (by decide) success fork
    obtain ⟨c3⟩ := SolcSignedQuery.selector_gt_succ c2 ImplV2.cert_check (by decide) success fork
    obtain ⟨opened4⟩ := c3.dest ImplV2.cert_check success fork
    exact SolcSignedQuery.selector_eq_succ opened4 ImplV2.cert_check (by decide) rfl success fork

  | increaseAuth =>
    obtain ⟨c0⟩ := SolcSignedQuery.selector_gt_zero selected ImplV2.cert_check (by decide) success fork
    obtain ⟨c1⟩ := SolcSignedQuery.selector_gt_zero c0 ImplV2.cert_check (by decide) success fork
    obtain ⟨c2⟩ := SolcSignedQuery.selector_gt_succ c1 ImplV2.cert_check (by decide) success fork
    obtain ⟨opened3⟩ := c2.dest ImplV2.cert_check success fork
    obtain ⟨c3⟩ := SolcSignedQuery.selector_gt_succ opened3 ImplV2.cert_check (by decide) success fork
    obtain ⟨opened4⟩ := c3.dest ImplV2.cert_check success fork
    exact SolcSignedQuery.selector_eq_succ opened4 ImplV2.cert_check (by decide) rfl success fork

  | decreaseAuth =>
    obtain ⟨c0⟩ := SolcSignedQuery.selector_gt_zero selected ImplV2.cert_check (by decide) success fork
    obtain ⟨c1⟩ := SolcSignedQuery.selector_gt_succ c0 ImplV2.cert_check (by decide) success fork
    obtain ⟨opened2⟩ := c1.dest ImplV2.cert_check success fork
    obtain ⟨c2⟩ := SolcSignedQuery.selector_gt_zero opened2 ImplV2.cert_check (by decide) success fork
    obtain ⟨c3⟩ := SolcSignedQuery.selector_gt_zero c2 ImplV2.cert_check (by decide) success fork
    obtain ⟨c4⟩ := SolcSignedQuery.selector_eq_zero c3 ImplV2.cert_check (by decide) success fork
    exact SolcSignedQuery.selector_eq_succ c4 ImplV2.cert_check (by decide) rfl success fork

private theorem wrapper_guard (op : OwnerOpV2) {F : Exec.Deriv} {post b : Devm} {M : Mem}
    (cut : CursorStateAt ImplV2.code ImplV2.cert F op.wrapper b [op.selector] M [])
    (sizeBound : 4 ≤ F.sevm.data.length.toB256.toNat)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    op.calldataBound ≤ F.sevm.data.length.toB256.toNat ∧
      Nonempty (CursorStateAt ImplV2.code ImplV2.cert F op.decoder b
        [F.sevm.data.length.toB256 - 4,4,0x470,op.selector] M []) := by
  have shape : op.wrapper = .dest
      ((SolcSignedQuery.wrapperLine 4 0x70 op.widthBytes op.widthLe
        op.decodeTag.1 op.decodeTag.2).foldr SFunc.next (.branch op.wrapperReject op.decoder)) := by
    cases op <;> rfl
  rw [shape] at cut
  obtain ⟨opened⟩ := cut.dest ImplV2.cert_check success fork
  obtain ⟨guard⟩ := opened.line ImplV2.cert_check success fork _ rfl
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
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
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
  obtain ⟨opened⟩ := accepted.dest ImplV2.cert_check success fork
  obtain ⟨decoded⟩ := opened.line ImplV2.cert_check success fork _ rfl
    (by intro ni member xi same; subst ni
        cases op <;>
          simp only [OwnerOpV2.decoderLine,OwnerOpV2.entryTag,reduceCtorEq,ite_true,ite_false,
            SolcSignedQuery.decodeLine,SolcSignedQuery.decodeAuthorizationLine,
            List.mem_cons,List.not_mem_nil,or_self] at member)
    (decoder_args op)
  exact ⟨valueZero,bound,decoded.call ImplV2.cert_check success fork (by cases op <;> rfl)⟩

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
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    (255 &&& (b.getStorVal F.sevm.currentTarget 1 /
      (0x10000000000000000000000000000000000000000 : B256))) = 0 ∧
    Nonempty (CursorStateAt ImplV2.code ImplV2.cert F op.pauseNext
      (afterSload F.sevm b 1) S M K) := by
  have shape : op.entry = .dest ((SolcSignedQuery.pauseLine 1 op.pauseTag.1 op.pauseTag.2).foldr
      SFunc.next (.branch op.pauseReject op.pauseNext)) := by cases op <;> rfl
  rw [shape] at cut
  obtain ⟨opened⟩ := cut.dest ImplV2.cert_check success fork
  obtain ⟨guard⟩ := opened.line ImplV2.cert_check success fork _ rfl
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
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    (255 &&& b.getStorVal F.sevm.currentTarget (mapSlot adr.toB256 3)) = 0 ∧
    let b' := afterSload F.sevm b (mapSlot adr.toB256 3)
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
  obtain ⟨opened⟩ := cut.dest ImplV2.cert_check success fork
  obtain ⟨read⟩ := opened.line ImplV2.cert_check success fork _ rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.mappedByteReadLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    (SolcSignedQuery.mapped_byte_read_line source ptr fork)
  obtain ⟨guard⟩ := read.line ImplV2.cert_check success fork
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
  · unfold afterSload
    split <;> rfl
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
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
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
  have state0 : (afterSload F.sevm F.devm 1).state = F.devm.state := by
    unfold afterSload
    split <;> rfl
  have state01 := state1.trans state0
  have state012 := state2.trans state01
  have ownerRead : (afterSload F.sevm F.devm 1).getStorVal F.sevm.currentTarget
      (mapSlot (Sevm.dataWord F.sevm 4).toAdr.toB256 3) =
      F.devm.getStorVal F.sevm.currentTarget (mapSlot (Sevm.dataWord F.sevm 4).toAdr.toB256 3) := by
    unfold Devm.getStorVal Devm.getAcct
    rw [state0]
  have spenderRead : (afterSload F.sevm (afterSload F.sevm F.devm 1)
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
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    Nonempty (CursorStateAt ImplV2.code ImplV2.cert F op.internalEntry b
      (op.args F.sevm ++ Bytes.toB256 [op.internalReturnTag.1,op.internalReturnTag.2] ::
        (Sevm.dataWord F.sevm 36).toAdr.toB256 :: (Sevm.dataWord F.sevm 4).toAdr.toB256 ::
          (op.args F.sevm ++ [0x470,op.selector])) M [op.internalReturn,op.returnTree]) := by
  have shape : op.callEntry = .dest (op.calleeLine.foldr SFunc.next
      (.callNext op.internalNumber op.internalReturn)) := by cases op <;> rfl
  rw [shape] at cut
  obtain ⟨opened⟩ := cut.dest ImplV2.cert_check success fork
  obtain ⟨called⟩ := opened.line ImplV2.cert_check success fork _ rfl
    (by intro ni member xi same; subst ni
        cases op <;>
          simp only [OwnerOpV2.calleeLine,OwnerOpV2.internalReturnTag,OwnerOpV2.internalTag,
            reduceCtorEq,ite_true,ite_false,List.replicate,List.cons_append,List.nil_append,
            List.mem_cons,List.not_mem_nil,or_self] at member)
    (callee_args op)
  exact called.call ImplV2.cert_check success fork (by cases op <;> rfl)

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
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    F.sevm.benvStat.time.toNat ≤ deadline.toNat ∧
    let nonce := b.getStorVal F.sevm.currentTarget (nonceSlot owner)
    let b' := afterSstore F.sevm (afterSload F.sevm b (nonceSlot owner)) (nonceSlot owner) (nonce + 1)
    let M' := (M.write 0 owner.toB256.toBytes).write 32 (17 : B256).toBytes
    PtrMem 128 96 M' ∧ Nonempty (CursorStateAt ImplV2.code ImplV2.cert F
      ownerV2PermitNonceTail b'
      (nonce ::32::64::owner.toB256::(0xffffffffffffffffffffffffffffffffffffffff : B256)::
        s::r::v::deadline::value::spender.toB256::owner.toB256::S) M' K) := by
  obtain ⟨opened⟩ := cut.dest ImplV2.cert_check success fork
  obtain ⟨guard⟩ := opened.line ImplV2.cert_check success fork
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
  obtain ⟨openedNonce⟩ := accepted.dest ImplV2.cert_check success fork
  obtain ⟨updated⟩ := openedNonce.line ImplV2.cert_check success fork
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
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    (255 &&& b.getStorVal F.sevm.currentTarget (authSlot owner nonce)) = 0 ∧
    let b' := afterSload F.sevm b (authSlot owner nonce)
    b'.state = b.state ∧ PtrMem 128 96 (ownerV2AuthCheckMemory M owner nonce) ∧
      Nonempty (CursorStateAt ImplV2.code ImplV2.cert F .ret b' S
        (ownerV2AuthCheckMemory M owner nonce) K) := by
  have p1 := (ptr.write 0 owner.toB256 (.inl (by decide))).write 32 16 (.inl (by decide))
  have p2 := (p1.write 0 nonce (.inl (by decide))).write 32 (mapSlot owner.toB256 16) (.inl (by decide))
  have read1 := p1.read_self (i := 0) (sz := 64) (by decide)
  have read2 := p2.read_self (i := 0) (sz := 64) (by decide)
  obtain ⟨opened⟩ := cut.dest ImplV2.cert_check success fork
  obtain ⟨guard⟩ := opened.line ImplV2.cert_check success fork authStateReadLine rfl
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
      obtain ⟨_,rfl⟩ := ri_sload fork step
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
  obtain ⟨openedEnum⟩ := validEnum.dest ImplV2.cert_check success fork
  obtain ⟨unusedGuard⟩ := openedEnum.line ImplV2.cert_check success fork
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
  obtain ⟨openedReturn⟩ := accepted.dest ImplV2.cert_check success fork
  obtain ⟨returned⟩ := openedReturn.line ImplV2.cert_check success fork [.reg .pop,.reg .pop] rfl
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
  unfold afterSload
  split <;> rfl

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
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    Nonempty (CursorStateAt ImplV2.code ImplV2.cert F ImplV2.t_4d9e_c83 b
      (Sevm.dataWord F.sevm 132 :: Sevm.dataWord F.sevm 100 :: Sevm.dataWord F.sevm 164 ::
        (Sevm.dataWord F.sevm 4).toAdr.toB256 ::
        Bytes.toB256 [op.validationReturnTag.1,op.validationReturnTag.2] :: op.internalStack F.sevm)
      M [op.validationReturn,op.internalReturn,op.returnTree]) := by
  have shape : op.internalEntry = .dest
      (op.validationLine.foldr SFunc.next (.callNext 83 op.validationReturn)) := by
    cases op <;> first | contradiction | rfl
  rw [shape] at cut
  obtain ⟨opened⟩ := cut.dest ImplV2.cert_check success fork
  obtain ⟨called⟩ := opened.line ImplV2.cert_check success fork _ rfl
    (by intro ni member xi same; subst ni
        simp only [OwnerOpV2.validationLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    (S' := Bytes.toB256 [0x4d,0x9e] :: Sevm.dataWord F.sevm 132 ::
      Sevm.dataWord F.sevm 100 :: Sevm.dataWord F.sevm 164 ::
      (Sevm.dataWord F.sevm 4).toAdr.toB256 ::
      Bytes.toB256 [op.validationReturnTag.1,op.validationReturnTag.2] :: op.internalStack F.sevm)
    (by intro gas d run
        cases op <;> first
        | contradiction
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
  exact called.call ImplV2.cert_check success fork rfl

private theorem authorization_validity {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {before after nonce ret : B256} {owner : Adr} {S : List B256} {returnTree : SFunc} {K : List SFunc}
    (cut : CursorStateAt ImplV2.code ImplV2.cert F ImplV2.t_4d9e_c83 b
      (before :: after :: nonce :: owner.toB256 :: ret :: S) M (returnTree :: K))
    (ptr : PtrMem 128 96 M)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    after.toNat < F.sevm.benvStat.time.toNat ∧ F.sevm.benvStat.time.toNat < before.toNat ∧
    (255 &&& b.getStorVal F.sevm.currentTarget (authSlot owner nonce)) = 0 ∧
    let b' := afterSload F.sevm b (authSlot owner nonce)
    b'.state = b.state ∧ PtrMem 128 96 (ownerV2AuthCheckMemory M owner nonce) ∧
      Nonempty (CursorStateAt ImplV2.code ImplV2.cert F returnTree b' S
        (ownerV2AuthCheckMemory M owner nonce) K) := by
  obtain ⟨opened⟩ := cut.dest ImplV2.cert_check success fork
  obtain ⟨afterGuard⟩ := opened.line ImplV2.cert_check success fork
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
  obtain ⟨openedBefore⟩ := afterAccepted.dest ImplV2.cert_check success fork
  obtain ⟨beforeGuard⟩ := openedBefore.line ImplV2.cert_check success fork
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
  obtain ⟨openedCall⟩ := beforeAccepted.dest ImplV2.cert_check success fork
  obtain ⟨call⟩ := openedCall.line ImplV2.cert_check success fork
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
  obtain ⟨called⟩ := call.call ImplV2.cert_check success fork rfl
  obtain ⟨unused,unchanged,ptr',⟨read⟩⟩ := authorization_state called ptr success fork
  obtain ⟨returned⟩ := read.ret ImplV2.cert_check success fork
  obtain ⟨openedReturn⟩ := returned.dest ImplV2.cert_check success fork
  obtain ⟨done⟩ := openedReturn.line ImplV2.cert_check success fork
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
  exact ⟨afterBound,beforeBound,unused,unchanged,ptr',done.ret ImplV2.cert_check success fork⟩

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
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
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
    · unfold afterSstore
      split <;>
        (change (afterSload F.sevm b _).state.setStorVal _ _ _ = _
         unfold afterSload
         split <;>
           (change b.state.setStorVal _ _ _ = _
            rw [state]
            rfl))
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
      afterSload F.sevm b (authSlot (Sevm.dataWord F.sevm 4).toAdr (Sevm.dataWord F.sevm 164)),
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
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
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

end Blanc.Lift.Usdc
