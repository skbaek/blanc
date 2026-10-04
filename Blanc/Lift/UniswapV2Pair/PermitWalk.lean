import Blanc.Lift.UniswapV2Pair.ApproveCore
import Blanc.Lift.StaticCallGuard
import Blanc.Lift.InvWalkProvenance
import Blanc.Lift.WordImage
import Blanc.Lift.UniswapV2Pair.Execution

/-! The literal permit body before its recovery call: nonce postincrement, the
EIP-712 struct and digest images, and the 128-byte recovery request. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def permitNonceSlot (owner : Adr) : B256 := mapSlot owner.toB256 4

def permitNonceRead (sevm : Sevm) (b : Devm) (owner : Adr) : B256 :=
  (afterSload sevm b 3).getStorVal sevm.currentTarget (permitNonceSlot owner)

/-- Domain read, nonce read, then the wrapped postincrement store. -/
def permitNonceWorld (sevm : Sevm) (b : Devm) (owner : Adr) : Devm :=
  afterSstore sevm (afterSload sevm (afterSload sevm b 3) (permitNonceSlot owner))
    (permitNonceSlot owner) (permitNonceRead sevm b owner + 1)

def permitNonceMemory (M : Mem) (owner : Adr) : Mem :=
  (M.write 0 owner.toB256.toBytes).write 32 (4 : B256).toBytes

def permitNonceLine : List Ninst := [
  .push [0x03] (by decide),
  .reg .sload,
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg (.dup 0),
  .reg (.dup 9),
  .reg .and,
  .push [0x00] (by decide),
  .reg (.dup 1),
  .reg (.dup 1),
  .reg .mstore,
  .push [0x04] (by decide),
  .push [0x20] (by decide),
  .reg (.swap 0),
  .reg (.dup 1),
  .reg .mstore,
  .push [0x40] (by decide),
  .reg (.dup 0),
  .reg (.dup 3),
  .reg .keccak256,
  .reg (.dup 0),
  .reg .sload,
  .push [0x01] (by decide),
  .reg (.dup 0),
  .reg (.dup 2),
  .reg .add,
  .reg (.swap 0),
  .reg (.swap 2),
  .reg .sstore]

theorem permitNonceMemory_ptr {M : Mem} (mem : PtrMem 128 96 M) (owner : Adr) :
    PtrMem 128 96 (permitNonceMemory M owner) := by
  have a := mem.write 0 owner.toB256 (Or.inl (by decide))
  rw [show memExtSize 96 0 32 = 96 from by decide] at a
  have b := a.write 32 4 (Or.inl (by decide))
  rw [show memExtSize 96 32 32 = 96 from by decide] at b
  exact b

theorem permitNonceMemory_slot (M : Mem) (owner : Adr) :
    ((permitNonceMemory M owner).read 0 64).1.keccak = permitNonceSlot owner := by
  have read := Mem.read_two_word_writes_at_raw M 0 owner.toB256 4
  rw [Nat.zero_add] at read
  exact congrArg Bytes.keccak read

theorem permitNonceLine_inv {sevm : Sevm} {b d : Devm} {R : List B256} {M : Mem}
    {G : Nat} {s r vw dl val spw : B256} {owner : Adr}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : Line.Run sevm (St b (s :: r :: vw :: dl :: val :: spw :: owner.toB256 :: R) M G)
      permitNonceLine d) :
    sevm.isStatic = false ∧ ∃ G', d = St (permitNonceWorld sevm b owner)
      (permitNonceRead sevm b owner :: 1 :: 64 :: 32 :: 0 :: owner.toB256 :: ~~~ addressMask ::
        b.getStorVal sevm.currentTarget 3 ::
        s :: r :: vw :: dl :: val :: spw :: owner.toB256 :: R) (permitNonceMemory M owner) G' := by
  have m1 := permitNonceMemory_ptr mem owner
  dsimp only [permitNonceLine] at run
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_sload fork hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_val (w := owner.toB256)
    (by rw [B256.and_comm]; exact ff20_and_adr owner) (ri_and hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore_nat 0 rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore_nat 32 rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, hd⟩ := ri_keccak hs
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [0x40]).toNat = 64 from rfl,
    show Bytes.toB256 [4] = (4 : B256) from rfl] at hd
  rw [show ((M.write 0 owner.toB256.toBytes).write 32 (4 : B256).toBytes) =
      permitNonceMemory M owner from rfl, permitNonceMemory_slot,
    m1.read_self (by decide : 0 + 64 ≤ 96)] at hd
  subst d
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_sload fork hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run
  have nonstatic := ri_sstore_nonstatic fork hs
  obtain ⟨G', rfl⟩ := ri_sstore fork hs
  cases run
  exact ⟨nonstatic, G', rfl⟩

/-- One hundred fourteen fixed gas besides the three selected storage charges. -/
theorem permitNonceLine_exact {fs : List SFunc} {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G c1 c2 c3 : Nat} {s r vw dl val spw : B256} {owner : Adr}
    {f : SFunc} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (room : R.length ≤ 1000) (nonstatic : sevm.isStatic = false)
    (charge1 : c1 = sloadCost sevm b 3)
    (charge2 : c2 = sloadCost sevm (afterSload sevm b 3) (permitNonceSlot owner))
    (charge3 : c3 = sstoreCost sevm (afterSload sevm (afterSload sevm b 3) (permitNonceSlot owner))
      (permitNonceSlot owner) (permitNonceRead sevm b owner + 1))
    (sentry : gCallStipend < G + c3)
    (body : SFunc.RunExact fs sevm (St (permitNonceWorld sevm b owner)
      (permitNonceRead sevm b owner :: 1 :: 64 :: 32 :: 0 :: owner.toB256 :: ~~~ addressMask ::
        b.getStorVal sevm.currentTarget 3 ::
        s :: r :: vw :: dl :: val :: spw :: owner.toB256 :: R) (permitNonceMemory M owner) G) f o) :
    SFunc.RunExact fs sevm (St b (s :: r :: vw :: dl :: val :: spw :: owner.toB256 :: R) M
      (G + c3 + c2 + c1 + 114)) (permitNonceLine.foldr SFunc.next f) o := by
  have m0 := mem.write 0 owner.toB256 (Or.inl (by decide))
  rw [show memExtSize 96 0 32 = 96 from by decide] at m0
  have m1 := permitNonceMemory_ptr mem owner
  dsimp only [permitNonceLine, List.foldr]
  refine rx_push (w := 3) rfl (by simp only [List.length_cons]; omega) ?_
  rw [show G + c3 + c2 + c1 + 111 = (G + c3 + c2 + 111) + c1 by omega]
  refine rx_sload_selC fork charge1 (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := ~~~ addressMask) ff20_eq (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 9) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := owner.toB256) (by rw [B256.and_comm, ← ff20_eq]; exact ff20_and_adr owner)
    (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) (M' := M.write 0 owner.toB256.toBytes) ?_ rfl ?_
  · rw [St.extCost_eq mem.size]; decide
  refine rx_push (w := 4) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) (M' := permitNonceMemory M owner) ?_ rfl ?_
  · rw [St.extCost_eq m0.size]; decide
  refine rx_push (w := 64) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_dup4 (by simp only [List.length_cons]; omega) ?_
  refine rx_keccak (v := permitNonceSlot owner) (c := 42) ?_ (permitNonceMemory_slot M owner)
    (m1.read_self (by decide)) (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq m1.size]; decide
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  rw [show G + c3 + c2 + 18 = (G + c3 + 18) + c2 by omega]
  refine rx_sload_selC fork charge2 (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_dup3 (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := permitNonceRead sevm b owner + 1) rfl
    (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_swap3 ?_
  exact rx_sstoreC fork charge3 sentry nonstatic body

def permitStructLine : List Ninst := [
  .reg (.dup 2),
  .reg .mload,
  .push [0x6e, 0x71, 0xed, 0xae, 0x12, 0xb1, 0xb9, 0x7f, 0x4d, 0x1f, 0x60, 0x37, 0x0f, 0xef, 0x10, 0x10, 0x5f, 0xa2, 0xfa, 0xae, 0x01, 0x26, 0x11, 0x4a, 0x16, 0x9c, 0x64, 0x84, 0x5d, 0x61, 0x26, 0xc9] (by decide),
  .reg (.dup 1),
  .reg (.dup 6),
  .reg .add,
  .reg .mstore,
  .reg (.dup 0),
  .reg (.dup 4),
  .reg .add,
  .reg (.swap 6),
  .reg (.swap 0),
  .reg (.swap 6),
  .reg .mstore,
  .reg (.swap 5),
  .reg (.dup 13),
  .reg .and,
  .push [0x60] (by decide),
  .reg (.dup 6),
  .reg .add,
  .reg .mstore,
  .push [0x80] (by decide),
  .reg (.dup 5),
  .reg .add,
  .reg (.dup 12),
  .reg (.swap 0),
  .reg .mstore,
  .push [0xa0] (by decide),
  .reg (.dup 5),
  .reg .add,
  .reg (.swap 5),
  .reg (.swap 0),
  .reg (.swap 5),
  .reg .mstore,
  .push [0xc0] (by decide),
  .reg (.dup 0),
  .reg (.dup 5),
  .reg .add,
  .reg (.dup 11),
  .reg (.swap 0),
  .reg .mstore,
  .reg (.dup 1),
  .reg .mload,
  .reg (.dup 0),
  .reg (.dup 6),
  .reg .sub,
  .reg (.swap 0),
  .reg (.swap 1),
  .reg .add,
  .reg (.dup 1),
  .reg .mstore,
  .push [0xe0] (by decide),
  .reg (.dup 5),
  .reg .add,
  .reg (.dup 2),
  .reg .mstore,
  .reg (.dup 0),
  .reg .mload,
  .reg (.swap 0),
  .reg (.dup 3),
  .reg .add,
  .reg .keccak256]

/-- The six ABI words of the EIP-712 struct, the length word and the bumped pointer. -/
def permitStructFields (M : Mem) (owner spender : Adr) (value nonce deadline : B256) : Mem :=
  (((((M.write 160 permitTypehash.toBytes).write 192 owner.toB256.toBytes).write 224
    spender.toB256.toBytes).write 256 value.toBytes).write 288 nonce.toBytes).write 320
    deadline.toBytes

def permitStructMemory (M : Mem) (owner spender : Adr) (value nonce deadline : B256) : Mem :=
  ((permitStructFields M owner spender value nonce deadline).write 128 (192 : B256).toBytes).write
    64 (352 : B256).toBytes

def permitStructImage (img : Bytes) (owner spender : Adr) (value nonce deadline : B256) : Bytes :=
  Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
    (Bytes.writeAt (Bytes.writeAt img 160 permitTypehash.toBytes) 192 owner.toB256.toBytes) 224
    spender.toB256.toBytes) 256 value.toBytes) 288 nonce.toBytes) 320 deadline.toBytes) 128
    (192 : B256).toBytes) 64 (352 : B256).toBytes

/-- The source's inner EIP-712 struct hash at the supplied old nonce. -/
def permitInner (owner spender : Adr) (value nonce deadline : B256) : B256 :=
  (encodeWords [permitTypehash, owner.toB256, spender.toB256, value, nonce, deadline]).keccak

theorem permitStructFields_ptr {M : Mem} (mem : PtrMem 128 96 M) (owner spender : Adr)
    (value nonce deadline : B256) :
    PtrMem 128 352 (permitStructFields M owner spender value nonce deadline) := by
  have a1 := mem.write 160 permitTypehash (Or.inr (by decide))
  rw [show memExtSize 96 160 32 = 192 from by decide] at a1
  have a2 := a1.write 192 owner.toB256 (Or.inr (by decide))
  rw [show memExtSize 192 192 32 = 224 from by decide] at a2
  have a3 := a2.write 224 spender.toB256 (Or.inr (by decide))
  rw [show memExtSize 224 224 32 = 256 from by decide] at a3
  have a4 := a3.write 256 value (Or.inr (by decide))
  rw [show memExtSize 256 256 32 = 288 from by decide] at a4
  have a5 := a4.write 288 nonce (Or.inr (by decide))
  rw [show memExtSize 288 288 32 = 320 from by decide] at a5
  have a6 := a5.write 320 deadline (Or.inr (by decide))
  rw [show memExtSize 320 320 32 = 352 from by decide] at a6
  exact a6

theorem permitStructMemory_ptr {M : Mem} (mem : PtrMem 128 96 M) (owner spender : Adr)
    (value nonce deadline : B256) :
    PtrMem 352 352 (permitStructMemory M owner spender value nonce deadline) := by
  have a7 := (permitStructFields_ptr mem owner spender value nonce deadline).write 128 192
    (Or.inr (by decide))
  rw [show memExtSize 352 128 32 = 352 from by decide] at a7
  unfold permitStructMemory
  exact a7.set

theorem permitStructMemory_reads {M : Mem} {img : Bytes} (wf : Mem.Wf M) (reads : Mem.Reads M img)
    (owner spender : Adr) (value nonce deadline : B256) :
    Mem.Reads (permitStructMemory M owner spender value nonce deadline)
      (permitStructImage img owner spender value nonce deadline) := by
  unfold permitStructMemory permitStructFields permitStructImage
  have w1 := wf.write 160 permitTypehash.toBytes
  have w2 := w1.write 192 owner.toB256.toBytes
  have w3 := w2.write 224 spender.toB256.toBytes
  have w4 := w3.write 256 value.toBytes
  have w5 := w4.write 288 nonce.toBytes
  have w6 := w5.write 320 deadline.toBytes
  have w7 := w6.write 128 (192 : B256).toBytes
  have r1 := reads.write wf 160 permitTypehash.toBytes
  have r2 := r1.write w1 192 owner.toB256.toBytes
  have r3 := r2.write w2 224 spender.toB256.toBytes
  have r4 := r3.write w3 256 value.toBytes
  have r5 := r4.write w4 288 nonce.toBytes
  have r6 := r5.write w5 320 deadline.toBytes
  have r7 := r6.write w6 128 (192 : B256).toBytes
  exact r7.write w7 64 (352 : B256).toBytes

theorem permitStructImage_window (img : Bytes) (owner spender : Adr)
    (value nonce deadline : B256) :
    (permitStructImage img owner spender value nonce deadline).sliceD 160 192 0 =
      encodeWords [permitTypehash, owner.toB256, spender.toB256, value, nonce, deadline] := by
  unfold permitStructImage
  rw [Bytes.sliceD_writeAt_word_after _ 64 160 192 _ (by decide),
    Bytes.sliceD_writeAt_word_after _ 128 160 192 _ (by decide),
    Bytes.sliceD_writeAt_word_last _ 160 160 320 192 _ rfl rfl,
    Bytes.sliceD_writeAt_word_last _ 160 128 288 160 _ rfl rfl,
    Bytes.sliceD_writeAt_word_last _ 160 96 256 128 _ rfl rfl,
    Bytes.sliceD_writeAt_word_last _ 160 64 224 96 _ rfl rfl,
    Bytes.sliceD_writeAt_word_last _ 160 32 192 64 _ rfl rfl,
    Bytes.sliceD_writeAt_word_last _ 160 0 160 32 _ rfl rfl]
  rw [show List.sliceD img 160 0 0 = [] from rfl, List.nil_append]
  simp only [encodeWords, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_assoc]

theorem permitStructImage_length (img : Bytes) (owner spender : Adr)
    (value nonce deadline : B256) :
    Bytes.toB256 ((permitStructImage img owner spender value nonce deadline).sliceD 128 32 0) =
      192 := by
  unfold permitStructImage
  rw [Bytes.sliceD_writeAt_word_after _ 64 128 32 _ (by decide), sliceD_word_same,
    B256.toB256_toBytes]

theorem permitStructLine_inv {sevm : Sevm} {b d : Devm} {R : List B256} {A : Mem}
    {img : Bytes} {G : Nat} {s r vw dl val nonce dom : B256} {owner spender : Adr}
    (mem : PtrMem 128 96 A) (reads : Mem.Reads A img)
    (run : Line.Run sevm (St b (nonce :: 1 :: 64 :: 32 :: 0 :: owner.toB256 :: ~~~ addressMask :: dom ::
        s :: r :: vw :: dl :: val :: spender.toB256 :: owner.toB256 :: R) A G) permitStructLine d) :
    ∃ G', d = St b (permitInner owner spender val nonce dl :: 64 :: 32 :: 0 :: 128 :: 1 :: dom ::
        s :: r :: vw :: dl :: val :: spender.toB256 :: owner.toB256 :: R)
      (permitStructMemory A owner spender val nonce dl) G' := by
  have read0 : Bytes.toB256 (A.read 64 32).1 = 128 := mem.word
  have same0 : (A.read 64 32).2 = A := mem.read_self (by decide)
  have a6 := permitStructFields_ptr mem owner spender val nonce dl
  have read6 : Bytes.toB256 ((permitStructFields A owner spender val nonce dl).read 64 32).1 =
    128 := a6.word
  have same6 : ((permitStructFields A owner spender val nonce dl).read 64 32).2 =
    permitStructFields A owner spender val nonce dl := a6.read_self (by decide)
  have mB := permitStructMemory_ptr mem owner spender val nonce dl
  have rB := permitStructMemory_reads mem.wf reads owner spender val nonce dl
  have readB : Bytes.toB256 ((permitStructMemory A owner spender val nonce dl).read 128 32).1 =
      192 := by
    rw [rB.read]; exact permitStructImage_length img owner spender val nonce dl
  have sameB : ((permitStructMemory A owner spender val nonce dl).read 128 32).2 =
    permitStructMemory A owner spender val nonce dl := mB.read_self (by decide)
  have windowB : ((permitStructMemory A owner spender val nonce dl).read 160 192).1.keccak =
      permitInner owner spender val nonce dl := by
    rw [rB.read, permitStructImage_window]; rfl
  have sameB2 : ((permitStructMemory A owner spender val nonce dl).read 160 192).2 =
    permitStructMemory A owner spender val nonce dl := mB.read_self (by decide)
  dsimp only [permitStructFields] at read6 same6
  dsimp only [permitStructMemory, permitStructFields] at readB sameB windowB sameB2
  dsimp only [permitStructLine] at run
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, hd⟩ := ri_mload hs
  rw [show (64 : B256).toNat = 64 from rfl, read0, same0] at hd; subst d
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := permitTypehash) rfl (ri_push hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := 160) (by decide) (ri_add hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore_nat 160 rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := 192) (by decide) (ri_add hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore_nat 192 rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := spender.toB256)
    (by rw [and_mask_word, toAdr_toB256]) (ri_and hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := 224) (by decide) (ri_add hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore_nat 224 rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := 256) (by decide) (ri_add hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore_nat 256 rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := 288) (by decide) (ri_add hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore_nat 288 rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := 320) (by decide) (ri_add hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore_nat 320 rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, hd⟩ := ri_mload hs
  rw [show (64 : B256).toNat = 64 from rfl, read6, same6] at hd; subst d
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := 0) (B256.sub_self _) (ri_sub hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := 192) (by decide) (ri_add hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore_nat 128 rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := 352) (by decide) (ri_add hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore_nat 64 rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, hd⟩ := ri_mload hs
  rw [show (128 : B256).toNat = 128 from rfl, readB, sameB] at hd; subst d
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := 160) (by decide) (ri_add hs)
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, hd⟩ := ri_keccak hs
  rw [show (160 : B256).toNat = 160 from rfl, show (192 : B256).toNat = 192 from rfl,
    windowB, sameB2] at hd; subst d
  cases run
  exact ⟨_, rfl⟩

/-- The struct image costs two hundred seventy-three gas, with every expansion
from 96 to 352 bytes paid at its actual store. -/
theorem permitStructLine_exact {fs : List SFunc} {sevm : Sevm} {b : Devm} {R : List B256}
    {A : Mem} {img : Bytes} {G : Nat} {s r vw dl val nonce dom : B256} {owner spender : Adr}
    {f : SFunc} {o : Outcome}
    (mem : PtrMem 128 96 A) (reads : Mem.Reads A img) (room : R.length ≤ 1000)
    (body : SFunc.RunExact fs sevm (St b (permitInner owner spender val nonce dl :: 64 :: 32 :: 0 :: 128 :: 1 :: dom ::
        s :: r :: vw :: dl :: val :: spender.toB256 :: owner.toB256 :: R)
      (permitStructMemory A owner spender val nonce dl) G) f o) :
    SFunc.RunExact fs sevm (St b (nonce :: 1 :: 64 :: 32 :: 0 :: owner.toB256 :: ~~~ addressMask :: dom ::
        s :: r :: vw :: dl :: val :: spender.toB256 :: owner.toB256 :: R) A (G + 273))
      (permitStructLine.foldr SFunc.next f) o := by
  have read0 : Bytes.toB256 (A.read 64 32).1 = 128 := mem.word
  have same0 : (A.read 64 32).2 = A := mem.read_self (by decide)
  have a6 := permitStructFields_ptr mem owner spender val nonce dl
  have read6 : Bytes.toB256 ((permitStructFields A owner spender val nonce dl).read 64 32).1 =
    128 := a6.word
  have same6 : ((permitStructFields A owner spender val nonce dl).read 64 32).2 =
    permitStructFields A owner spender val nonce dl := a6.read_self (by decide)
  have mB := permitStructMemory_ptr mem owner spender val nonce dl
  have rB := permitStructMemory_reads mem.wf reads owner spender val nonce dl
  have readB : Bytes.toB256 ((permitStructMemory A owner spender val nonce dl).read 128 32).1 =
      192 := by
    rw [rB.read]; exact permitStructImage_length img owner spender val nonce dl
  have sameB : ((permitStructMemory A owner spender val nonce dl).read 128 32).2 =
    permitStructMemory A owner spender val nonce dl := mB.read_self (by decide)
  have windowB : ((permitStructMemory A owner spender val nonce dl).read 160 192).1.keccak =
      permitInner owner spender val nonce dl := by
    rw [rB.read, permitStructImage_window]; rfl
  have sameB2 : ((permitStructMemory A owner spender val nonce dl).read 160 192).2 =
    permitStructMemory A owner spender val nonce dl := mB.read_self (by decide)
  have a1 := mem.write 160 permitTypehash (Or.inr (by decide))
  rw [show memExtSize 96 160 32 = 192 from by decide] at a1
  have a2 := a1.write 192 owner.toB256 (Or.inr (by decide))
  rw [show memExtSize 192 192 32 = 224 from by decide] at a2
  have a3 := a2.write 224 spender.toB256 (Or.inr (by decide))
  rw [show memExtSize 224 224 32 = 256 from by decide] at a3
  have a4 := a3.write 256 val (Or.inr (by decide))
  rw [show memExtSize 256 256 32 = 288 from by decide] at a4
  have a5 := a4.write 288 nonce (Or.inr (by decide))
  rw [show memExtSize 288 288 32 = 320 from by decide] at a5
  have a7 := a6.write 128 192 (Or.inr (by decide))
  rw [show memExtSize 352 128 32 = 352 from by decide] at a7
  dsimp only [permitStructLine, List.foldr]
  refine rx_dup (n := 2) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_mload (i := 64) (v := 128) (c := 3) (by rw [St.extCost_eq mem.size]; decide)
    mem.word (mem.read_self (by decide)) (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := permitTypehash) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 6) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 160) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 12) (M' := A.write 160 permitTypehash.toBytes) (by rw [St.extCost_eq mem.size]; decide) rfl ?_
  refine rx_dup (n := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 192) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 6) rfl ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_swap (n := 6) rfl ?_
  refine rx_mstore (c := 6) (M' := (A.write 160 permitTypehash.toBytes).write 192 owner.toB256.toBytes) (by rw [St.extCost_eq a1.size]; decide) rfl ?_
  refine rx_swap (n := 5) rfl ?_
  refine rx_dup (n := 13) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_and (v := spender.toB256) (by rw [and_mask_word, toAdr_toB256]) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_push (w := 96) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 6) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_add' (v := 224) (by decide) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_mstore (c := 6) (M' := ((A.write 160 permitTypehash.toBytes).write 192 owner.toB256.toBytes).write 224 spender.toB256.toBytes) (by rw [St.extCost_eq a2.size]; decide) rfl ?_
  refine rx_push (w := 128) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 5) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_add' (v := 256) (by decide) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 12) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_mstore (c := 6) (M' := (((A.write 160 permitTypehash.toBytes).write 192 owner.toB256.toBytes).write 224 spender.toB256.toBytes).write 256 val.toBytes) (by rw [St.extCost_eq a3.size]; decide) rfl ?_
  refine rx_push (w := 160) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 5) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_add' (v := 288) (by decide) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_swap (n := 5) rfl ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_swap (n := 5) rfl ?_
  refine rx_mstore (c := 6) (M' := ((((A.write 160 permitTypehash.toBytes).write 192 owner.toB256.toBytes).write 224 spender.toB256.toBytes).write 256 val.toBytes).write 288 nonce.toBytes) (by rw [St.extCost_eq a4.size]; decide) rfl ?_
  refine rx_push (w := 192) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 0) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 5) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_add' (v := 320) (by decide) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 11) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_mstore (c := 6) (M' := permitStructFields A owner spender val nonce dl) (by rw [St.extCost_eq a5.size]; decide) rfl ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_mload (i := 64) (v := 128) (c := 3) (by rw [St.extCost_eq a6.size]; decide)
    a6.word (a6.read_self (by decide)) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 0) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 6) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_sub' (v := 0) (B256.sub_self _) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_swap (n := 1) rfl ?_
  refine rx_add' (v := 192) (by decide) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_mstore (c := 3) (M' := (permitStructFields A owner spender val nonce dl).write 128 (192 : B256).toBytes) (by rw [St.extCost_eq a6.size]; decide) rfl ?_
  refine rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 5) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_add' (v := 352) (by decide) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 2) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_mstore (c := 3) (M' := permitStructMemory A owner spender val nonce dl) (by rw [St.extCost_eq a7.size]; decide) rfl ?_
  refine rx_dup (n := 0) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_mload (i := 128) (v := 192) (c := 3) (by rw [St.extCost_eq mB.size]; decide)
    readB sameB (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_dup (n := 3) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_add' (v := 160) (by decide) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_keccak (v := permitInner owner spender val nonce dl) (c := 66)
    (by rw [St.extCost_eq mB.size]; decide) windowB sameB2 (by simp only [List.length_cons, List.length_set]; omega) ?_
  exact body

def permitDigestLine : List Ninst := [
  .push [0x19, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide),
  .push [0x01, 0x00] (by decide),
  .reg (.dup 6),
  .reg .add,
  .reg .mstore,
  .push [0x01, 0x02] (by decide),
  .reg (.dup 5),
  .reg .add,
  .reg (.swap 6),
  .reg (.swap 0),
  .reg (.swap 6),
  .reg .mstore,
  .push [0x01, 0x22] (by decide),
  .reg (.dup 0),
  .reg (.dup 5),
  .reg .add,
  .reg (.swap 6),
  .reg (.swap 0),
  .reg (.swap 6),
  .reg .mstore,
  .reg (.dup 0),
  .reg .mload,
  .reg (.dup 0),
  .reg (.dup 5),
  .reg .sub,
  .reg (.swap 0),
  .reg (.swap 6),
  .reg .add,
  .reg (.dup 6),
  .reg .mstore,
  .push [0x01, 0x42] (by decide),
  .reg (.dup 4),
  .reg .add,
  .reg (.dup 0),
  .reg (.dup 2),
  .reg .mstore,
  .reg (.dup 6),
  .reg .mload,
  .reg (.swap 6),
  .reg (.dup 3),
  .reg .add,
  .reg (.swap 6),
  .reg (.swap 0),
  .reg (.swap 6),
  .reg .keccak256]

def permitPrefixWord : B256 := Bytes.toB256 [0x19, 0x01, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The packed `0x1901 ‖ domain ‖ inner` digest the source signs. -/
def permitDigestOf (dom inner : B256) : B256 :=
  Bytes.keccak ([0x19, 0x01] ++ dom.toBytes ++ inner.toBytes)

/-- Overlapping packed image, its length word, and the bumped pointer. -/
def permitDigestMemory (M : Mem) (dom inner : B256) : Mem :=
  ((((M.write 384 permitPrefixWord.toBytes).write 386 dom.toBytes).write 418 inner.toBytes).write
    352 (66 : B256).toBytes).write 64 (450 : B256).toBytes

def permitDigestImage (img : Bytes) (dom inner : B256) : Bytes :=
  Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 384
    permitPrefixWord.toBytes) 386 dom.toBytes) 418 inner.toBytes) 352 (66 : B256).toBytes) 64
    (450 : B256).toBytes

theorem permitDigestMemory_ptr {M : Mem} (mem : PtrMem 352 352 M) (dom inner : B256) :
    PtrMem 450 480 (permitDigestMemory M dom inner) := by
  have a1 := mem.write 384 permitPrefixWord (Or.inr (by decide))
  rw [show memExtSize 352 384 32 = 416 from by decide] at a1
  have a2 := a1.write 386 dom (Or.inr (by decide))
  rw [show memExtSize 416 386 32 = 448 from by decide] at a2
  have a3 := a2.write 418 inner (Or.inr (by decide))
  rw [show memExtSize 448 418 32 = 480 from by decide] at a3
  have a4 := a3.write 352 66 (Or.inr (by decide))
  rw [show memExtSize 480 352 32 = 480 from by decide] at a4
  unfold permitDigestMemory
  exact a4.set

theorem permitDigestMemory_reads {M : Mem} {img : Bytes} (wf : Mem.Wf M) (reads : Mem.Reads M img)
    (dom inner : B256) :
    Mem.Reads (permitDigestMemory M dom inner) (permitDigestImage img dom inner) := by
  unfold permitDigestMemory permitDigestImage
  have w1 := wf.write 384 permitPrefixWord.toBytes
  have w2 := w1.write 386 dom.toBytes
  have w3 := w2.write 418 inner.toBytes
  have w4 := w3.write 352 (66 : B256).toBytes
  have r1 := reads.write wf 384 permitPrefixWord.toBytes
  have r2 := r1.write w1 386 dom.toBytes
  have r3 := r2.write w2 418 inner.toBytes
  have r4 := r3.write w3 352 (66 : B256).toBytes
  exact r4.write w4 64 (450 : B256).toBytes

theorem permitDigestImage_window (img : Bytes) (dom inner : B256) :
    (permitDigestImage img dom inner).sliceD 384 66 0 =
      [0x19, 0x01] ++ dom.toBytes ++ inner.toBytes := by
  unfold permitDigestImage
  rw [Bytes.sliceD_writeAt_word_after _ 64 384 66 _ (by decide),
    Bytes.sliceD_writeAt_word_after _ 352 384 66 _ (by decide),
    Bytes.sliceD_writeAt_word_last _ 384 34 418 66 _ rfl rfl,
    Bytes.sliceD_writeAt_word_last _ 384 2 386 34 _ rfl rfl,
    Bytes.sliceD_writeAt_inside _ _ 384 384 2 (Nat.le_refl _)
      (by rw [B256.length_toBytes]; decide)]
  rfl

theorem permitDigestImage_length (img : Bytes) (dom inner : B256) :
    Bytes.toB256 ((permitDigestImage img dom inner).sliceD 352 32 0) = 66 := by
  unfold permitDigestImage
  rw [Bytes.sliceD_writeAt_word_after _ 64 352 32 _ (by decide), sliceD_word_same,
    B256.toB256_toBytes]

theorem permitDigestLine_inv {sevm : Sevm} {b d : Devm} {Z : List B256} {B : Mem}
    {img : Bytes} {G : Nat} {inner dom : B256}
    (mem : PtrMem 352 352 B) (reads : Mem.Reads B img)
    (run : Line.Run sevm (St b (inner :: 64 :: 32 :: 0 :: 128 :: 1 :: dom :: Z) B G) permitDigestLine d) :
    ∃ G', d = St b (permitDigestOf dom inner :: 64 :: 32 :: 0 :: 128 :: 1 :: 450 :: Z) (permitDigestMemory B dom inner) G' := by
  have m1 := mem.write 384 permitPrefixWord (Or.inr (by decide))
  rw [show memExtSize 352 384 32 = 416 from by decide] at m1
  have m2 := m1.write 386 dom (Or.inr (by decide))
  rw [show memExtSize 416 386 32 = 448 from by decide] at m2
  have a3 := m2.write 418 inner (Or.inr (by decide))
  rw [show memExtSize 448 418 32 = 480 from by decide] at a3
  have read3 : Bytes.toB256 ((((B.write 384 permitPrefixWord.toBytes).write 386 dom.toBytes).write
      418 inner.toBytes).read 64 32).1 = 352 := a3.word
  have same3 : ((((B.write 384 permitPrefixWord.toBytes).write 386 dom.toBytes).write
      418 inner.toBytes).read 64 32).2 =
      ((B.write 384 permitPrefixWord.toBytes).write 386 dom.toBytes).write 418 inner.toBytes :=
    a3.read_self (by decide)
  have mC := permitDigestMemory_ptr mem dom inner
  have rC := permitDigestMemory_reads mem.wf reads dom inner
  have readC : Bytes.toB256 ((permitDigestMemory B dom inner).read 352 32).1 = 66 := by
    rw [rC.read]; exact permitDigestImage_length img dom inner
  have sameC : ((permitDigestMemory B dom inner).read 352 32).2 = permitDigestMemory B dom inner :=
    mC.read_self (by decide)
  have windowC : ((permitDigestMemory B dom inner).read 384 66).1.keccak = permitDigestOf dom inner := by
    rw [rC.read, permitDigestImage_window]; rfl
  have sameC2 : ((permitDigestMemory B dom inner).read 384 66).2 = permitDigestMemory B dom inner :=
    mC.read_self (by decide)
  dsimp only [permitDigestMemory] at readC sameC windowC sameC2
  dsimp only [permitDigestLine] at run
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := permitPrefixWord) rfl (ri_push hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := 384) (by decide) (ri_add hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore_nat 384 rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := 386) (by decide) (ri_add hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore_nat 386 rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := 418) (by decide) (ri_add hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore_nat 418 rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, hd⟩ := ri_mload hs
  rw [show (64 : B256).toNat = 64 from rfl, read3, same3] at hd; subst d
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_sub hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := 66) (by decide) (ri_add hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore_nat 352 rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := 450) (by decide) (ri_add hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore_nat 64 rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, hd⟩ := ri_mload hs
  rw [show (352 : B256).toNat = 352 from rfl, readC, sameC] at hd; subst d
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := 384) (by decide) (ri_add hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, hd⟩ := ri_keccak hs
  rw [show (384 : B256).toNat = 384 from rfl, show (66 : B256).toNat = 66 from rfl,
    windowC, sameC2] at hd; subst d
  cases run
  exact ⟨_, rfl⟩

/-- The packed digest image costs one hundred ninety-two gas, expanding to 480 bytes. -/
theorem permitDigestLine_exact {fs : List SFunc} {sevm : Sevm} {b : Devm} {Z : List B256}
    {B : Mem} {img : Bytes} {G : Nat} {inner dom : B256} {f : SFunc} {o : Outcome}
    (mem : PtrMem 352 352 B) (reads : Mem.Reads B img) (room : Z.length ≤ 1008)
    (body : SFunc.RunExact fs sevm (St b (permitDigestOf dom inner :: 64 :: 32 :: 0 :: 128 :: 1 :: 450 :: Z) (permitDigestMemory B dom inner) G) f o) :
    SFunc.RunExact fs sevm (St b (inner :: 64 :: 32 :: 0 :: 128 :: 1 :: dom :: Z) B (G + 192))
      (permitDigestLine.foldr SFunc.next f) o := by
  have m1 := mem.write 384 permitPrefixWord (Or.inr (by decide))
  rw [show memExtSize 352 384 32 = 416 from by decide] at m1
  have m2 := m1.write 386 dom (Or.inr (by decide))
  rw [show memExtSize 416 386 32 = 448 from by decide] at m2
  have a3 := m2.write 418 inner (Or.inr (by decide))
  rw [show memExtSize 448 418 32 = 480 from by decide] at a3
  have read3 : Bytes.toB256 ((((B.write 384 permitPrefixWord.toBytes).write 386 dom.toBytes).write
      418 inner.toBytes).read 64 32).1 = 352 := a3.word
  have same3 : ((((B.write 384 permitPrefixWord.toBytes).write 386 dom.toBytes).write
      418 inner.toBytes).read 64 32).2 =
      ((B.write 384 permitPrefixWord.toBytes).write 386 dom.toBytes).write 418 inner.toBytes :=
    a3.read_self (by decide)
  have mC := permitDigestMemory_ptr mem dom inner
  have rC := permitDigestMemory_reads mem.wf reads dom inner
  have readC : Bytes.toB256 ((permitDigestMemory B dom inner).read 352 32).1 = 66 := by
    rw [rC.read]; exact permitDigestImage_length img dom inner
  have sameC : ((permitDigestMemory B dom inner).read 352 32).2 = permitDigestMemory B dom inner :=
    mC.read_self (by decide)
  have windowC : ((permitDigestMemory B dom inner).read 384 66).1.keccak = permitDigestOf dom inner := by
    rw [rC.read, permitDigestImage_window]; rfl
  have sameC2 : ((permitDigestMemory B dom inner).read 384 66).2 = permitDigestMemory B dom inner :=
    mC.read_self (by decide)
  have a1 := m1
  have a2 := m2
  have a4 := a3.write 352 66 (Or.inr (by decide))
  rw [show memExtSize 480 352 32 = 480 from by decide] at a4
  dsimp only [permitDigestLine, List.foldr]
  refine rx_push (w := permitPrefixWord) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 256) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 6) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 384) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 9) (M' := B.write 384 permitPrefixWord.toBytes) (by rw [St.extCost_eq mem.size]; decide) rfl ?_
  refine rx_push (w := 258) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 5) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 386) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 6) rfl ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_swap (n := 6) rfl ?_
  refine rx_mstore (c := 6) (M' := (B.write 384 permitPrefixWord.toBytes).write 386 dom.toBytes) (by rw [St.extCost_eq a1.size]; decide) rfl ?_
  refine rx_push (w := 290) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 0) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 5) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_add' (v := 418) (by decide) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_swap (n := 6) rfl ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_swap (n := 6) rfl ?_
  refine rx_mstore (c := 6) (M' := ((B.write 384 permitPrefixWord.toBytes).write 386 dom.toBytes).write 418 inner.toBytes) (by rw [St.extCost_eq a2.size]; decide) rfl ?_
  refine rx_dup (n := 0) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_mload (i := 64) (v := 352) (c := 3) (by rw [St.extCost_eq a3.size]; decide)
    a3.word (a3.read_self (by decide)) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 0) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 5) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_sub' (v := 128 - 352) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_swap (n := 6) rfl ?_
  refine rx_add' (v := 66) (by decide) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 6) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_mstore (c := 3) (M' := (((B.write 384 permitPrefixWord.toBytes).write 386 dom.toBytes).write 418 inner.toBytes).write 352 (66 : B256).toBytes) (by rw [St.extCost_eq a3.size]; decide) rfl ?_
  refine rx_push (w := 322) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_add' (v := 450) (by decide) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 0) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 2) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_mstore (c := 3) (M' := permitDigestMemory B dom inner) (by rw [St.extCost_eq a4.size]; decide) rfl ?_
  refine rx_dup (n := 6) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_mload (i := 352) (v := 66) (c := 3) (by rw [St.extCost_eq mC.size]; decide)
    readC sameC (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_swap (n := 6) rfl ?_
  refine rx_dup (n := 3) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_add' (v := 384) (by decide) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_swap (n := 6) rfl ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_swap (n := 6) rfl ?_
  refine rx_keccak (v := permitDigestOf dom inner) (c := 48)
    (by rw [St.extCost_eq mC.size]; decide) windowC sameC2 (by simp only [List.length_cons, List.length_set]; omega) ?_
  exact body

def permitRequestLine : List Ninst := [
  .reg (.swap 5),
  .reg (.dup 3),
  .reg (.swap 0),
  .reg .mstore,
  .push [0x01, 0x62] (by decide),
  .reg (.dup 4),
  .reg .add,
  .reg (.dup 0),
  .reg (.dup 2),
  .reg .mstore,
  .reg (.dup 6),
  .reg (.swap 0),
  .reg .mstore,
  .push [0xff] (by decide),
  .reg (.dup 9),
  .reg .and,
  .push [0x01, 0x82] (by decide),
  .reg (.dup 5),
  .reg .add,
  .reg .mstore,
  .push [0x01, 0xa2] (by decide),
  .reg (.dup 4),
  .reg .add,
  .reg (.dup 8),
  .reg (.swap 0),
  .reg .mstore,
  .push [0x01, 0xc2] (by decide),
  .reg (.dup 4),
  .reg .add,
  .reg (.dup 7),
  .reg (.swap 0),
  .reg .mstore,
  .reg .mload,
  .reg (.swap 1),
  .reg (.swap 3),
  .reg (.swap 2),
  .push [0x01, 0xe2] (by decide),
  .reg (.dup 0),
  .reg (.dup 2),
  .reg .add,
  .reg (.swap 3),
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xe0] (by decide),
  .reg (.dup 1),
  .reg .add,
  .reg (.swap 2),
  .reg (.dup 1),
  .reg (.swap 0),
  .reg .sub,
  .reg (.swap 0),
  .reg (.swap 1),
  .reg .add,
  .reg (.swap 0),
  .reg (.dup 5)]

/-- Zeroed output word, bumped pointer, and the four ABI words of the recovery request. -/
def permitRequestMemory (M : Mem) (digest : B256) (v : UInt8) (r s : B256) : Mem :=
  (((((M.write 450 (0 : B256).toBytes).write 64 (482 : B256).toBytes).write 482 digest.toBytes).write
    514 v.toB256.toBytes).write 546 r.toBytes).write 578 s.toBytes

def permitRequestImage (img : Bytes) (digest : B256) (v : UInt8) (r s : B256) : Bytes :=
  Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img
    450 (0 : B256).toBytes) 64 (482 : B256).toBytes) 482 digest.toBytes) 514 v.toB256.toBytes)
    546 r.toBytes) 578 s.toBytes

theorem permitRequestMemory_ptr {M : Mem} (mem : PtrMem 450 480 M) (digest : B256) (v : UInt8)
    (r s : B256) : PtrMem 482 640 (permitRequestMemory M digest v r s) := by
  have b1 := mem.write 450 0 (Or.inr (by decide))
  rw [show memExtSize 480 450 32 = 512 from by decide] at b1
  have b2 : PtrMem 482 512 ((M.write 450 (0 : B256).toBytes).write 64 (482 : B256).toBytes) := b1.set
  have b3 := b2.write 482 digest (Or.inr (by decide))
  rw [show memExtSize 512 482 32 = 544 from by decide] at b3
  have b4 := b3.write 514 v.toB256 (Or.inr (by decide))
  rw [show memExtSize 544 514 32 = 576 from by decide] at b4
  have b5 := b4.write 546 r (Or.inr (by decide))
  rw [show memExtSize 576 546 32 = 608 from by decide] at b5
  have b6 := b5.write 578 s (Or.inr (by decide))
  rw [show memExtSize 608 578 32 = 640 from by decide] at b6
  exact b6

theorem permitRequestMemory_reads {M : Mem} {img : Bytes} (wf : Mem.Wf M) (reads : Mem.Reads M img)
    (digest : B256) (v : UInt8) (r s : B256) :
    Mem.Reads (permitRequestMemory M digest v r s) (permitRequestImage img digest v r s) := by
  unfold permitRequestMemory permitRequestImage
  have w1 := wf.write 450 (0 : B256).toBytes
  have w2 := w1.write 64 (482 : B256).toBytes
  have w3 := w2.write 482 digest.toBytes
  have w4 := w3.write 514 v.toB256.toBytes
  have w5 := w4.write 546 r.toBytes
  have r1 := reads.write wf 450 (0 : B256).toBytes
  have r2 := r1.write w1 64 (482 : B256).toBytes
  have r3 := r2.write w2 482 digest.toBytes
  have r4 := r3.write w3 514 v.toB256.toBytes
  have r5 := r4.write w4 546 r.toBytes
  exact r5.write w5 578 s.toBytes

/-- The literal 128-byte input window is exactly the source recovery calldata. -/
theorem permitRequestImage_window (img : Bytes) (digest : B256) (v : UInt8) (r s : B256) :
    (permitRequestImage img digest v r s).sliceD 482 128 0 =
      ExternalOperation.encode (.recover digest v r s) := by
  unfold permitRequestImage
  rw [Bytes.sliceD_writeAt_word_last _ 482 96 578 128 _ rfl rfl,
    Bytes.sliceD_writeAt_word_last _ 482 64 546 96 _ rfl rfl,
    Bytes.sliceD_writeAt_word_last _ 482 32 514 64 _ rfl rfl,
    Bytes.sliceD_writeAt_word_last _ 482 0 482 32 _ rfl rfl,
    show List.sliceD (Bytes.writeAt (Bytes.writeAt img 450 (0 : B256).toBytes) 64
      (482 : B256).toBytes) 482 0 0 = [] from rfl, List.nil_append]
  simp only [ExternalOperation.encode, encodeWords, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc]

theorem permitRequestLine_inv {sevm : Sevm} {b d : Devm} {Z : List B256} {C : Mem}
    {G : Nat} {digest s r : B256} {v : UInt8}
    (mem : PtrMem 450 480 C)
    (run : Line.Run sevm (St b (digest :: 64 :: 32 :: 0 :: 128 :: 1 :: 450 :: s :: r :: v.toB256 :: Z) C G) permitRequestLine d) :
    ∃ G', d = St b (1 :: 482 :: 128 :: 450 :: 32 :: 610 :: 1 :: 0 :: digest :: s :: r :: v.toB256 :: Z) (permitRequestMemory C digest v r s) G' := by
  have mD := permitRequestMemory_ptr mem digest v r s
  have readD : Bytes.toB256 ((permitRequestMemory C digest v r s).read 64 32).1 = 482 := mD.word
  have sameD : ((permitRequestMemory C digest v r s).read 64 32).2 =
    permitRequestMemory C digest v r s := mD.read_self (by decide)
  dsimp only [permitRequestMemory] at readD sameD
  dsimp only [permitRequestLine] at run
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore_nat 450 rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := 482) (by decide) (ri_add hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore_nat 64 rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore_nat 482 rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := v.toB256) (UInt8.toB256_and_ff v) (ri_and hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := 514) (by decide) (ri_add hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore_nat 514 rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := 546) (by decide) (ri_add hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore_nat 546 rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := 578) (by decide) (ri_add hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore_nat 578 rfl hs
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, hd⟩ := ri_mload hs
  rw [show (64 : B256).toNat = 64 from rfl, readD, sameD] at hd; subst d
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := 610) (by decide) (ri_add hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := 450) (by decide) (ri_add hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_sub hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_val (w := 128) (by decide) (ri_add hs)
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  cases run
  exact ⟨_, rfl⟩

/-- The recovery request costs one hundred seventy-four gas, expanding to 640 bytes. -/
theorem permitRequestLine_exact {fs : List SFunc} {sevm : Sevm} {b : Devm} {Z : List B256}
    {C : Mem} {G : Nat} {digest s r : B256} {v : UInt8} {f : SFunc} {o : Outcome}
    (mem : PtrMem 450 480 C) (room : Z.length ≤ 1008)
    (body : SFunc.RunExact fs sevm (St b (1 :: 482 :: 128 :: 450 :: 32 :: 610 :: 1 :: 0 :: digest :: s :: r :: v.toB256 :: Z) (permitRequestMemory C digest v r s) G) f o) :
    SFunc.RunExact fs sevm (St b (digest :: 64 :: 32 :: 0 :: 128 :: 1 :: 450 :: s :: r :: v.toB256 :: Z) C (G + 174))
      (permitRequestLine.foldr SFunc.next f) o := by
  have mD := permitRequestMemory_ptr mem digest v r s
  have readD : Bytes.toB256 ((permitRequestMemory C digest v r s).read 64 32).1 = 482 := mD.word
  have sameD : ((permitRequestMemory C digest v r s).read 64 32).2 =
    permitRequestMemory C digest v r s := mD.read_self (by decide)
  have b1 := mem.write 450 0 (Or.inr (by decide))
  rw [show memExtSize 480 450 32 = 512 from by decide] at b1
  have b2 : PtrMem 482 512 ((C.write 450 (0 : B256).toBytes).write 64 (482 : B256).toBytes) := b1.set
  have b3 := b2.write 482 digest (Or.inr (by decide))
  rw [show memExtSize 512 482 32 = 544 from by decide] at b3
  have b4 := b3.write 514 v.toB256 (Or.inr (by decide))
  rw [show memExtSize 544 514 32 = 576 from by decide] at b4
  have b5 := b4.write 546 r (Or.inr (by decide))
  rw [show memExtSize 576 546 32 = 608 from by decide] at b5
  dsimp only [permitRequestLine, List.foldr]
  refine rx_swap (n := 5) rfl ?_
  refine rx_dup (n := 3) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_mstore (c := 6) (M' := C.write 450 (0 : B256).toBytes) (by rw [St.extCost_eq mem.size]; decide) rfl ?_
  refine rx_push (w := 354) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_add' (v := 482) (by decide) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 0) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 2) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_mstore (c := 3) (M' := (C.write 450 (0 : B256).toBytes).write 64 (482 : B256).toBytes) (by rw [St.extCost_eq b1.size]; decide) rfl ?_
  refine rx_dup (n := 6) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_mstore (c := 6) (M' := ((C.write 450 (0 : B256).toBytes).write 64 (482 : B256).toBytes).write 482 digest.toBytes) (by rw [St.extCost_eq b2.size]; decide) rfl ?_
  refine rx_push (w := 255) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 9) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_and (v := v.toB256) (UInt8.toB256_and_ff v) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_push (w := 386) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 5) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_add' (v := 514) (by decide) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_mstore (c := 6) (M' := (((C.write 450 (0 : B256).toBytes).write 64 (482 : B256).toBytes).write 482 digest.toBytes).write 514 v.toB256.toBytes) (by rw [St.extCost_eq b3.size]; decide) rfl ?_
  refine rx_push (w := 418) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_add' (v := 546) (by decide) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 8) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_mstore (c := 6) (M' := ((((C.write 450 (0 : B256).toBytes).write 64 (482 : B256).toBytes).write 482 digest.toBytes).write 514 v.toB256.toBytes).write 546 r.toBytes) (by rw [St.extCost_eq b4.size]; decide) rfl ?_
  refine rx_push (w := 450) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_add' (v := 578) (by decide) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 7) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_mstore (c := 6) (M' := permitRequestMemory C digest v r s) (by rw [St.extCost_eq b5.size]; decide) rfl ?_
  refine rx_mload (i := 64) (v := 482) (c := 3) (by rw [St.extCost_eq mD.size]; decide)
    mD.word (mD.read_self (by decide)) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_swap (n := 1) rfl ?_
  refine rx_swap (n := 3) rfl ?_
  refine rx_swap (n := 2) rfl ?_
  refine rx_push (w := 482) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 0) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 2) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_add' (v := 610) (by decide) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_swap (n := 3) rfl ?_
  refine rx_push (w := 115792089237316195423570985008687907853269984665640564039457584007913129639904) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_add' (v := 450) (by decide) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_swap (n := 2) rfl ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_sub' (v := 128 - 482) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_swap (n := 1) rfl ?_
  refine rx_add' (v := 128) (by decide) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_dup (n := 5) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  exact body

end Blanc.Lift.UniswapV2Pair
