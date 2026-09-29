import Blanc.Lift.Curve3Crv.Creation.Cert
import Blanc.Lift.Vyper
import Blanc.Lift.PackedSha
import Blanc.Lift.WalkSteps
import Blanc.Lift.Deploy

/-!
# The 3Crv LP token constructor, walked

A gas-exact synthetic run (`SFunc.RunExact`) of the lifted Vyper 0.2.4 constructor of the 3Crv
LP token's creation input (`Creation/Cert.lean`), with the recorded constructor arguments
(name `"Curve.fi DAI/USDC/USDT"`, symbol `"3Crv"`, decimals 18, supply 0) appended to the code.
The constructor

* stores Vyper's five clamp constants in memory and copies its four argument words from the
  code (entry 0);
* copies the two strings, bounds-checks them (against call data, which is empty in a creation
  frame) and the decimals, and computes `supply · 10^decimals = 0` with its overflow check;
* stores `name` and `symbol` through Vyper's string store loop (`vyStoreHead`,
  `vyStoreLoopTree`, `Blanc/Lift/Vyper.lean`; entries 3 and 4 are the loop heads) at the hashed
  bases `keccak(0)` and `keccak(1)` (kept symbolic);
* stores `decimals`, `balanceOf[caller] = 0`, `total_supply = 0`, `minter = caller`, logs
  `Transfer(0, caller, 0)`, and returns the runtime through the deploy tail after the runtime
  (entry 5).

Gas is exact; the start gas is only bounded below.
-/

namespace Blanc.Lift.Curve3Crv.Creation

open Jaune

/-- The lifted constructor program. -/
abbrev prog : List SFunc := Cert.prog cert

/-- The frame facts the walk needs of the creation frame. -/
structure CtorFrame (sevm : Sevm) : Prop where
  fork : CoveredFork sevm.benvStat.fork
  static : sevm.isStatic = false

/-! ## The loops' shapes -/

theorem t_0162_c0_eq : t_0162_c0 =
    vyStoreLoopTree 0x01 0x75 0x01 0x97 0x01 0x62 1 3 t_0197_c1 := rfl
theorem prog_3 : prog[3]? = some (vyStoreLoopTree 0x01 0x75 0x01 0x97 0x01 0x62 1 3 t_0197_c1) :=
  rfl
theorem prog_1 : prog[1]? = some t_0197_c1 := rfl
theorem t_01bc_c1_eq : t_01bc_c1 =
    vyStoreLoopTree 0x01 0xcf 0x01 0xf1 0x01 0xbc 2 4 t_01f1_c2 := rfl
theorem prog_4 : prog[4]? = some (vyStoreLoopTree 0x01 0xcf 0x01 0xf1 0x01 0xbc 2 4 t_01f1_c2) :=
  rfl
theorem t_0197_c1_eq : t_0197_c1 = .dest (.next (.reg .pop) (.next (.reg .pop) (.next (.reg .pop)
    (.next (.reg .pop) (.next (.reg .pop) (.next (.reg .pop)
      (vyStoreHead 0x02 0x40 0x01 0x02 t_01bc_c1))))))) := rfl

/-! ## The string store loops -/

/-- A string store's memory after the head: the slot index at `0xc0`, the counter `0` at
`0x120`. -/
def headMem (M : Mem) (sl : UInt8) : Mem :=
  (M.write 0xc0 (Bytes.toB256 [sl]).toBytes).write 0x120 (Nat.toB256 0).toBytes

/-- The data base of the string at slot `sl`. -/
def strBase (sl : UInt8) : B256 := (Bytes.toB256 [sl]).toBytes.keccak

/-- The memory after `n` loop passes. -/
def loopMem (M : Mem) (sl : UInt8) : Nat → Mem
  | 0 => headMem M sl
  | i + 1 => (loopMem M sl i).write 0x120 (Nat.toB256 (i + 1)).toBytes

/-- The word pass `i` stores. -/
def loopWord (M : Mem) (sl : UInt8) (src : Nat) (i : Nat) : B256 :=
  Bytes.toB256 ((loopMem M sl i).read (src + 32 * i) 32).1

/-- The world after `n` loop passes. -/
def loopWorld (sevm : Sevm) (b : Devm) (M : Mem) (sl : UInt8) (src : Nat) : Nat → Devm
  | 0 => b
  | i + 1 => afterSstore sevm (loopWorld sevm b M sl src i) (strBase sl + Nat.toB256 i)
      (loopWord M sl src i)

/-- The charge of pass `i`'s `SSTORE`. -/
def loopCost (sevm : Sevm) (b : Devm) (M : Mem) (sl : UInt8) (src : Nat) (i : Nat) : Nat :=
  sstoreCost sevm (loopWorld sevm b M sl src i) (strBase sl + Nat.toB256 i) (loopWord M sl src i)

theorem loopMem_size {M : Mem} {sl : UInt8} (hs : M.size = 704) :
    ∀ i, (loopMem M sl i).size = 704
  | 0 => by
    unfold loopMem headMem
    rw [Mem.size_write_of_le (by rw [B256.length_toBytes, Mem.size_write_of_le
      (by rw [B256.length_toBytes, hs]; omega), hs]; omega),
      Mem.size_write_of_le (by rw [B256.length_toBytes, hs]; omega), hs]
  | i + 1 => by
    unfold loopMem
    rw [Mem.size_write_of_le (by rw [B256.length_toBytes, loopMem_size hs i]; omega),
      loopMem_size hs i]

theorem loopMem_wf {M : Mem} {sl : UInt8} (hwf : Mem.Wf M) : ∀ i, Mem.Wf (loopMem M sl i)
  | 0 => (hwf.write _ _).write _ _
  | i + 1 => (loopMem_wf hwf i).write _ _

theorem loopMem_ctr {M : Mem} {sl : UInt8} (hwf : Mem.Wf M) :
    ∀ i, ((loopMem M sl i).read 0x120 32).1 = (Nat.toB256 i).toBytes
  | 0 => Mem.read_write_word_of_wf (hwf.write _ _) _ _
  | i + 1 => Mem.read_write_word_of_wf (loopMem_wf hwf i) _ _

/-- **Storing `name`** (22 bytes at `0x1c0`, loop cap 3): the head, two passes (the length word
and the data word) and the exit test, then entry 1. -/
theorem storeName {sevm : Sevm} (fr : CtorFrame sevm) {b : Devm} {M : Mem}
    (hs : M.size = 704) (hwf : Mem.Wf M)
    (hlen : Bytes.toB256 (M.read 0x1c0 32).1 = Nat.toB256 22) {X : Nat}
    (hX : gCallStipend < X) {o : Outcome}
    (k : SFunc.RunExact prog sevm
      (St (loopWorld sevm b M 0x00 0x1c0 2)
        (vyStoreStack (Bytes.toB256 [0x03] + Nat.toB256 0)
          (Bytes.toB256 (M.read 0x1c0 32).1 + Bytes.toB256 [0x20]) (strBase 0x00)
          (Bytes.toB256 [0x01, 0xc0]) [Bytes.toB256 [0x01, 0xc0]])
        (loopMem M 0x00 2) X) t_0197_c1 o) :
    SFunc.RunExact prog sevm
      (St b [] M (X + 48 + 117 + loopCost sevm b M 0x00 0x1c0 1 + 117 +
        loopCost sevm b M 0x00 0x1c0 0 + 90))
      (vyStoreHead 0x01 0xc0 0x00 0x03 t_0162_c0) o := by
  have hlp : (Bytes.toB256 (M.read 0x1c0 32).1 + Bytes.toB256 [0x20]).toNat = 54 := by
    rw [hlen]; decide
  refine rx_vyStoreHead (sn := 0x1c0) (by simp) hs (by decide) (by decide) hwf (by decide)
    (by decide) (by decide) ?_
  rw [t_0162_c0_eq]
  refine rx_vyStoreStep (i := 0) fr.fork fr.static (by simp) (by rw [hlp]; omega) (by decide)
    (loopMem_size hs 0) (by decide) (by decide) (by decide) (by decide) (by decide)
    (loopMem_ctr hwf 0) (by unfold gCallStipend at hX ⊢; omega) prog_3 ?_
  refine rx_vyStoreStep (i := 1) fr.fork fr.static (by simp) (by rw [hlp]; omega) (by decide)
    (loopMem_size hs 1) (by decide) (by decide) (by decide) (by decide) (by decide)
    (loopMem_ctr hwf 1) (by unfold gCallStipend at hX ⊢; omega) prog_3 ?_
  exact rx_vyStoreExit (i := 2) (by simp) (by rw [hlp]; omega) (by decide) (loopMem_size hs 2)
    (by decide) (by decide) (loopMem_ctr hwf 2) prog_1 k

/-- **Storing `symbol`** (4 bytes at `0x240`, loop cap 2): entry 1 drops the name loop's six
words, then the head and two passes, the second falling through into entry 2's tree. -/
theorem storeSymbol {sevm : Sevm} (fr : CtorFrame sevm) {b : Devm} {M : Mem}
    (hs : M.size = 704) (hwf : Mem.Wf M)
    (hlen : Bytes.toB256 (M.read 0x240 32).1 = Nat.toB256 4) {x1 x2 x3 x4 x5 x6 : B256}
    {X : Nat} (hX : gCallStipend < X) {o : Outcome}
    (k : SFunc.RunExact prog sevm
      (St (loopWorld sevm b M 0x01 0x240 2)
        (vyStoreStack (Bytes.toB256 [0x02] + Nat.toB256 0)
          (Bytes.toB256 (M.read 0x240 32).1 + Bytes.toB256 [0x20]) (strBase 0x01)
          (Bytes.toB256 [0x02, 0x40]) [Bytes.toB256 [0x02, 0x40]])
        (loopMem M 0x01 2) X) t_01f1_c2 o) :
    SFunc.RunExact prog sevm
      (St b [x1, x2, x3, x4, x5, x6] M (X + 117 + loopCost sevm b M 0x01 0x240 1 + 117 +
        loopCost sevm b M 0x01 0x240 0 + 90 + 13))
      t_0197_c1 o := by
  have hlp : (Bytes.toB256 (M.read 0x240 32).1 + Bytes.toB256 [0x20]).toNat = 36 := by
    rw [hlen]; decide
  rw [t_0197_c1_eq]
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_vyStoreHead (sn := 0x240) (by simp) hs (by decide) (by decide) hwf (by decide)
    (by decide) (by decide) ?_
  rw [t_01bc_c1_eq]
  refine rx_vyStoreStep (i := 0) fr.fork fr.static (by simp) (by rw [hlp]; omega) (by decide)
    (loopMem_size hs 0) (by decide) (by decide) (by decide) (by decide) (by decide)
    (loopMem_ctr hwf 0) (by unfold gCallStipend at hX ⊢; omega) prog_4 ?_
  exact rx_vyStoreLast (i := 1) fr.fork fr.static (by simp) (by rw [hlp]; omega) (by decide)
    (loopMem_size hs 1) (by decide) (by decide) (by decide) (by decide) (by decide)
    (loopMem_ctr hwf 1) (by unfold gCallStipend at hX ⊢; omega) k

/-! ## The tail: the scalar slots, the event, the runtime -/

/-- `balanceOf[a]`'s slot as the constructor hashes it: `keccak(3 ‖ a)`. -/
def balSlotOf (a : B256) : B256 := ((3 : B256).toBytes ++ a.toBytes).keccak

/-- `Transfer(address,address,uint256)`. -/
def transferTopic : B256 := Bytes.toB256 [0xdd, 0xf2, 0x52, 0xad, 0x1b, 0xe2, 0xc8, 0x9b, 0x69,
  0xc2, 0xb0, 0x68, 0xfc, 0x37, 0x8d, 0xaa, 0x95, 0x2b, 0xa7, 0xf1, 0x63, 0xc4, 0xa1, 0x16, 0x28,
  0xf5, 0x5a, 0x4d, 0xf5, 0x23, 0xb3, 0xef]

/-- The tail's memory states: the key words for the balance hash, then the event data. -/
def tailMem1 (M : Mem) (c : B256) : Mem := (M.write 0xe0 c.toBytes).write 0xc0 (3 : B256).toBytes
def tailMem2 (M : Mem) (c : B256) : Mem := (tailMem1 M c).write 0x2c0 (0 : B256).toBytes

/-- The window the deploy tail returns: the creation input's bytes `[595, 595 + 2276)`. -/
def runtimeWindow : Bytes := code.sliceD 595 2276 (Linst.toUInt8 .stop)

theorem runtimeWindow_length : runtimeWindow.length = 2276 := ByteArray.length_sliceD _ _ _ _

def tailMem3 (M : Mem) (c : B256) : Mem := (tailMem2 M c).write 0 runtimeWindow

/-- The tail's worlds. -/
def tw4 (sevm : Sevm) (b : Devm) : Devm := afterSstore sevm b 2 18
def tw5 (sevm : Sevm) (b : Devm) : Devm :=
  afterSstore sevm (tw4 sevm b) (balSlotOf sevm.caller.toB256) 0
def tw6 (sevm : Sevm) (b : Devm) : Devm := afterSstore sevm (tw5 sevm b) 5 0
def tw7 (sevm : Sevm) (b : Devm) : Devm := afterSstore sevm (tw6 sevm b) 6 sevm.caller.toB256
def tw8 (sevm : Sevm) (b : Devm) (M : Mem) : Devm :=
  (tw7 sevm b).addLog ⟨sevm.currentTarget, [transferTopic, 0, sevm.caller.toB256],
    ((tailMem2 M sevm.caller.toB256).read 0x2c0 32).1⟩

/-- The tail's exact cost from the world `b`. -/
def tailCost (sevm : Sevm) (b : Devm) : Nat :=
  2200 + sstoreCost sevm (tw6 sevm b) 6 sevm.caller.toB256 + 5 +
    sstoreCost sevm (tw5 sevm b) 5 0 + 9 +
    sstoreCost sevm (tw4 sevm b) (balSlotOf sevm.caller.toB256) 0 + 71 +
    sstoreCost sevm b 2 18 + 22

/-- **The tail** (entry 2 after the symbol loop, then entry 5): decimals, `balanceOf[caller]`,
`total_supply`, `minter`, the `Transfer` event, and the deploy tail's `CODECOPY`/`RETURN` of the
runtime. -/
theorem tail {sevm : Sevm} (fr : CtorFrame sevm) (hcode : sevm.code = code) {b : Devm} {M : Mem}
    (hs : M.size = 704) (hwf : Mem.Wf M)
    (hdec : Bytes.toB256 (M.read 0x180 32).1 = 18) (hsup : Bytes.toB256 (M.read 0x2a0 32).1 = 0)
    {x1 x2 x3 x4 x5 x6 : B256} {G : Nat} (hG : gCallStipend < G) :
    SFunc.RunExact prog sevm (St b [x1, x2, x3, x4, x5, x6] M (G + tailCost sevm b)) t_01f1_c2
      (.halted (returnPost (St (tw8 sevm b M) [Nat.toB256 0, Nat.toB256 2276]
        (tailMem3 M sevm.caller.toB256) G) (Nat.toB256 0) (Nat.toB256 2276) [])) := by
  have hs1 : (M.write 0xe0 sevm.caller.toB256.toBytes).size = 704 := by
    rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hs]; omega), hs]
  have hs2 : (tailMem1 M sevm.caller.toB256).size = 704 := by
    rw [tailMem1, Mem.size_write_of_le (by rw [B256.length_toBytes, hs1]; omega), hs1]
  have hwf2 : Mem.Wf (tailMem1 M sevm.caller.toB256) := (hwf.write _ _).write _ _
  have hs3 : (tailMem2 M sevm.caller.toB256).size = 736 := by
    rw [tailMem2, Mem.size_write_word_aligned (by rw [hs2]) (by decide), hs2]; rfl
  have hs4 : (tailMem3 M sevm.caller.toB256).size = 2304 := by
    rw [tailMem3, Mem.size_write_of_size hs3 (by decide) runtimeWindow_length]; decide
  have hread1 : ((M.write 0xe0 sevm.caller.toB256.toBytes).read 0x2a0 32).1 = (M.read 0x2a0 32).1 :=
    Mem.read_write_disjoint hwf _ _ (by rw [B256.length_toBytes]; omega)
  have hsup2 : Bytes.toB256 ((tailMem1 M sevm.caller.toB256).read 0x2a0 32).1 = 0 := by
    rw [tailMem1, Mem.read_write_disjoint (hwf.write _ _) _ _
      (by rw [B256.length_toBytes]; omega), hread1, hsup]
  have hkey : ((tailMem1 M sevm.caller.toB256).read 0xc0 64).1 = (3 : B256).toBytes ++ sevm.caller.toB256.toBytes := by
    have hr := ((Mem.reads_data M).write hwf 0xe0 sevm.caller.toB256.toBytes).write (hwf.write _ _) 0xc0
      (3 : B256).toBytes
    rw [tailMem1, hr.read, show (64 : Nat) = 32 + 32 from rfl, List.sliceD_split,
      sliceD_word_same, Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]),
      sliceD_word_same]
  have hc0 : (Bytes.toB256 [0xc0]).toNat = 0xc0 := by decide
  rw [show G + tailCost sevm b = G + 2200 + sstoreCost sevm (tw6 sevm b) 6 sevm.caller.toB256 + 5 +
    sstoreCost sevm (tw5 sevm b) 5 0 + 9 +
    sstoreCost sevm (tw4 sevm b) (balSlotOf sevm.caller.toB256) 0 + 71 + sstoreCost sevm b 2 18 + 22 by
      unfold tailCost; omega]
  unfold t_01f1_c2
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_push (w := 0x180) (by decide) (by simp) ?_
  refine rx_mload (c := 3) (v := 18) (charge_covered hs (by decide) (by decide)) hdec
    (read_covered hs (by decide) (by decide)) (by simp) ?_
  refine rx_push (w := 2) (by decide) (by simp) ?_
  refine rx_sstore fr.fork (by unfold gCallStipend at hG ⊢; omega) fr.static ?_
  refine rx_push (w := 0x2a0) (by decide) (by simp) ?_
  refine rx_mload (c := 3) (v := 0) (charge_covered hs (by decide) (by decide)) hsup
    (read_covered hs (by decide) (by decide)) (by simp) ?_
  refine rx_push (w := 3) (by decide) (by simp) ?_
  refine rx_caller (by simp) ?_
  refine rx_push (w := 0xe0) (by decide) (by simp) ?_
  refine rx_mstore (c := 3) (M' := M.write 0xe0 sevm.caller.toB256.toBytes) (charge_covered hs (by decide)
    (by decide)) rfl ?_
  refine rx_push (w := 0xc0) (by decide) (by simp) ?_
  refine rx_mstore (c := 3) (M' := tailMem1 M sevm.caller.toB256) (charge_covered hs1 (by decide) (by decide))
    rfl ?_
  refine rx_push (w := 0x40) (by decide) (by simp) ?_
  refine rx_push (w := 0xc0) (by decide) (by simp) ?_
  refine rx_keccak (c := 42) (v := balSlotOf sevm.caller.toB256) ?_
    (by show Bytes.keccak ((tailMem1 M sevm.caller.toB256).read 0xc0 64).1 = _; rw [hkey]; rfl)
    ?_ (by simp) ?_
  · rw [St.extCost_eq hs2]; decide
  · show Mem.extend (tailMem1 M sevm.caller.toB256) (B256.toNat 192) (B256.toNat 64) = _
    unfold Mem.extend
    generalize tailMem1 M sevm.caller.toB256 = T at hs2 ⊢
    cases T with
    | mk d sz =>
      simp only at hs2
      subst hs2
      rw [show memExtSize 704 (B256.toNat 192) (B256.toNat 64) = 704 by decide]
  refine rx_sstore fr.fork (by unfold gCallStipend at hG ⊢; omega) fr.static ?_
  refine rx_push (w := 0x2a0) (by decide) (by simp) ?_
  refine rx_mload (c := 3) (v := 0) (charge_covered hs2 (by decide) (by decide)) hsup2
    (read_covered hs2 (by decide) (by decide)) (by simp) ?_
  refine rx_push (w := 5) (by decide) (by simp) ?_
  refine rx_sstore fr.fork (by unfold gCallStipend at hG ⊢; omega) fr.static ?_
  refine rx_caller (by simp) ?_
  refine rx_push (w := 6) (by decide) (by simp) ?_
  refine rx_sstore fr.fork (by unfold gCallStipend at hG ⊢; omega) fr.static ?_
  refine rx_push (w := 0x2a0) (by decide) (by simp) ?_
  refine rx_mload (c := 3) (v := 0) (charge_covered hs2 (by decide) (by decide)) hsup2
    (read_covered hs2 (by decide) (by decide)) (by simp) ?_
  refine rx_push (w := 0x2c0) (by decide) (by simp) ?_
  refine rx_mstore (c := 7) (M' := tailMem2 M sevm.caller.toB256) ?_ rfl ?_
  · rw [St.extCost_eq hs2]; decide
  refine rx_caller (by simp) ?_
  refine rx_push (w := 0) (by decide) (by simp) ?_
  refine rx_push (w := transferTopic) rfl (by simp) ?_
  refine rx_push (w := 0x20) (by decide) (by simp) ?_
  refine rx_push (w := 0x2c0) (by decide) (by simp) ?_
  refine rx_log3 (c := 1756) fr.static ?_ rfl (read_covered hs3 (by decide) (by decide)) ?_
  · rw [St.extCost_eq hs3]; decide
  refine rx_push rfl (by simp) ?_
  refine rx_jump (j := 5) rfl ?_
  unfold t_0b37_c5
  refine rx_dest ?_
  refine rx_push (w := 0x253) (by decide) (by simp) ?_
  refine rx_push (w := 0xb37) (by decide) (by simp) ?_
  refine rx_sub' (v := Nat.toB256 2276) (by decide) (by simp) ?_
  refine rx_push (w := 0x253) (by decide) (by simp) ?_
  refine rx_push (w := Nat.toB256 0) (by decide) (by simp) ?_
  refine rx_codecopy (c := 375) (M' := tailMem3 M sevm.caller.toB256) ?_ ?_ ?_
  · rw [St.extCost_eq hs3]; decide
  · rw [hcode]; rfl
  refine rx_push (w := 0x253) (by decide) (by simp) ?_
  refine rx_push (w := 0xb37) (by decide) (by simp) ?_
  refine rx_sub' (v := Nat.toB256 2276) (by decide) (by simp) ?_
  refine rx_push (w := Nat.toB256 0) (by decide) (by simp) ?_
  refine rx_return_any rfl ?_
  rw [St.extCost_eq hs4]; decide

/-! ## The prefix: clamp constants, arguments, checks -/

/-- Vyper's clamp constants, stored at `0x20 … 0xa0`. -/
def clamp1 : B256 := Bytes.toB256 [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
def clamp2 : B256 := Bytes.toB256 [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
def clamp3 : B256 := Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
def clamp4 : B256 := Bytes.toB256 [0x01, 0x2a, 0x05, 0xf1, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfd, 0xab, 0xf4, 0x1c, 0x00]
def clamp5 : B256 := Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe, 0xd5, 0xfa, 0x0e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

def mA1 : Mem := Mem.empty.write 32 clamp1.toBytes
def mA2 : Mem := mA1.write 64 clamp2.toBytes
def mA3 : Mem := mA2.write 96 clamp3.toBytes
def mA4 : Mem := mA3.write 128 clamp4.toBytes
def mA5 : Mem := mA4.write 160 clamp5.toBytes
def mA6 : Mem := mA5.write 320 (code.sliceD 2895 128 (Linst.toUInt8 .stop))
def mA7 : Mem := mA6.write 192 (code.sliceD 2895 32 (Linst.toUInt8 .stop))
def mA8 : Mem := mA7.write 448 (code.sliceD 3023 96 (Linst.toUInt8 .stop))
def mA9 : Mem := mA8.write 192 (code.sliceD 2895 32 (Linst.toUInt8 .stop))
def mB1 : Mem := mA9.write 192 (code.sliceD 2927 32 (Linst.toUInt8 .stop))
def mB2 : Mem := mB1.write 576 (code.sliceD 3087 64 (Linst.toUInt8 .stop))
def mB3 : Mem := mB2.write 192 (code.sliceD 2927 32 (Linst.toUInt8 .stop))
def mB4 : Mem := mB3.write 672 (0 : B256).toBytes

theorem sliceD_len (a len : Nat) : (code.sliceD a len (Linst.toUInt8 .stop)).length = len :=
  ByteArray.length_sliceD _ _ _ _

theorem wfA9 : Mem.Wf mA9 :=
  (((((((((Mem.wf_empty.write _ _).write _ _).write _ _).write _ _).write _ _).write _ _).write
    _ _).write _ _).write _ _)
theorem wfA5 : Mem.Wf mA5 := ((((Mem.wf_empty.write _ _).write _ _).write _ _).write _ _).write _ _
theorem wfA6 : Mem.Wf mA6 := wfA5.write _ _
theorem wfA7 : Mem.Wf mA7 := wfA6.write _ _
theorem wfA8 : Mem.Wf mA8 := wfA7.write _ _
theorem wfB1 : Mem.Wf mB1 := wfA9.write _ _
theorem wfB2 : Mem.Wf mB2 := wfB1.write _ _
theorem wfB3 : Mem.Wf mB3 := wfB2.write _ _
theorem mB4_wf : Mem.Wf mB4 := wfB3.write _ _

theorem mA1_size : mA1.size = 64 := by
  rw [mA1, Mem.size_write_of_size (n := 0) rfl (by decide) (B256.length_toBytes _)]; decide
theorem mA2_size : mA2.size = 96 := by
  rw [mA2, Mem.size_write_of_size mA1_size (by decide) (B256.length_toBytes _)]; decide
theorem mA3_size : mA3.size = 128 := by
  rw [mA3, Mem.size_write_of_size mA2_size (by decide) (B256.length_toBytes _)]; decide
theorem mA4_size : mA4.size = 160 := by
  rw [mA4, Mem.size_write_of_size mA3_size (by decide) (B256.length_toBytes _)]; decide
theorem mA5_size : mA5.size = 192 := by
  rw [mA5, Mem.size_write_of_size mA4_size (by decide) (B256.length_toBytes _)]; decide
theorem mA6_size : mA6.size = 448 := by
  rw [mA6, Mem.size_write_of_size mA5_size (by decide) (sliceD_len _ _)]; decide
theorem mA7_size : mA7.size = 448 := by
  rw [mA7, Mem.size_write_of_size mA6_size (by decide) (sliceD_len _ _)]; decide
theorem mA8_size : mA8.size = 544 := by
  rw [mA8, Mem.size_write_of_size mA7_size (by decide) (sliceD_len _ _)]; decide
theorem mA9_size : mA9.size = 544 := by
  rw [mA9, Mem.size_write_of_size mA8_size (by decide) (sliceD_len _ _)]; decide
theorem mB1_size : mB1.size = 544 := by
  rw [mB1, Mem.size_write_of_size mA9_size (by decide) (sliceD_len _ _)]; decide
theorem mB2_size : mB2.size = 640 := by
  rw [mB2, Mem.size_write_of_size mB1_size (by decide) (sliceD_len _ _)]; decide
theorem mB3_size : mB3.size = 640 := by
  rw [mB3, Mem.size_write_of_size mB2_size (by decide) (sliceD_len _ _)]; decide
theorem mB4_size : mB4.size = 704 := by
  rw [mB4, Mem.size_write_of_size mB3_size (by decide) (B256.length_toBytes _)]; decide

/-- A read inside a written window reads the written bytes. -/
theorem read_write_inside {M : Mem} (hwf : Mem.Wf M) {n : Nat} {xs : Bytes} {a len : Nat}
    (h1 : n ≤ a) (h2 : a + len ≤ n + xs.length) :
    ((M.write n xs).read a len).1 = xs.sliceD (a - n) len 0 := by
  rw [((Mem.reads_data M).write hwf n xs).read]
  exact Bytes.sliceD_writeAt_inside _ _ _ _ _ h1 h2

/-- A code window, read through `toList` (the kernel-cheap form). -/
theorem code_slice (a len : Nat) :
    code.sliceD a len (Linst.toUInt8 .stop) = code.data.toList.sliceD a len 0 := by
  rw [ByteArray.sliceD_eq, ByteArray.toList_eq_toList_data]; rfl

theorem arg0_word : Bytes.toB256 ((code.sliceD 2895 32 (Linst.toUInt8 .stop)).sliceD 0 32 0) = 0x80 := by
  rw [code_slice]; decide +kernel
theorem arg1_word : Bytes.toB256 ((code.sliceD 2927 32 (Linst.toUInt8 .stop)).sliceD 0 32 0) = 0xc0 := by
  rw [code_slice]; decide +kernel
theorem decimals_word :
    Bytes.toB256 ((code.sliceD 2895 128 (Linst.toUInt8 .stop)).sliceD 64 32 0) = 18 := by
  rw [code_slice]; decide +kernel
theorem supply_word :
    Bytes.toB256 ((code.sliceD 2895 128 (Linst.toUInt8 .stop)).sliceD 96 32 0) = 0 := by
  rw [code_slice]; decide +kernel
theorem nameLen_word :
    Bytes.toB256 ((code.sliceD 3023 96 (Linst.toUInt8 .stop)).sliceD 0 32 0) = Nat.toB256 22 := by
  rw [code_slice]; decide +kernel
theorem symbolLen_word :
    Bytes.toB256 ((code.sliceD 3087 64 (Linst.toUInt8 .stop)).sliceD 0 32 0) = Nat.toB256 4 := by
  rw [code_slice]; decide +kernel

theorem mA7_arg0 : Bytes.toB256 (mA7.read 192 32).1 = 0x80 := by
  rw [mA7, read_write_inside wfA6 (le_refl _) (by rw [sliceD_len])]; exact arg0_word
theorem mA9_arg0 : Bytes.toB256 (mA9.read 192 32).1 = 0x80 := by
  rw [mA9, read_write_inside wfA8 (le_refl _) (by rw [sliceD_len])]; exact arg0_word
theorem mB1_arg1 : Bytes.toB256 (mB1.read 192 32).1 = 0xc0 := by
  rw [mB1, read_write_inside wfA9 (le_refl _) (by rw [sliceD_len])]; exact arg1_word
theorem mB3_arg1 : Bytes.toB256 (mB3.read 192 32).1 = 0xc0 := by
  rw [mB3, read_write_inside wfB2 (le_refl _) (by rw [sliceD_len])]; exact arg1_word

/-- The argument words at `0x180` (decimals) and `0x1a0` (supply), read through the later writes
back to the first argument copy. -/
theorem mA9_args {a : Nat} (h1 : 320 ≤ a) (h2 : a + 32 ≤ 448) :
    (mA9.read a 32).1 = (code.sliceD 2895 128 (Linst.toUInt8 .stop)).sliceD (a - 320) 32 0 := by
  rw [mA9, Mem.read_write_disjoint wfA8 _ _ (by rw [sliceD_len]; omega), mA8,
    Mem.read_write_disjoint wfA7 _ _ (by rw [sliceD_len]; omega), mA7,
    Mem.read_write_disjoint wfA6 _ _ (by rw [sliceD_len]; omega), mA6,
    read_write_inside wfA5 h1 (by rw [sliceD_len]; omega)]
theorem mB3_args {a : Nat} (h1 : 320 ≤ a) (h2 : a + 32 ≤ 448) :
    (mB3.read a 32).1 = (code.sliceD 2895 128 (Linst.toUInt8 .stop)).sliceD (a - 320) 32 0 := by
  rw [mB3, Mem.read_write_disjoint wfB2 _ _ (by rw [sliceD_len]; omega), mB2,
    Mem.read_write_disjoint wfB1 _ _ (by rw [sliceD_len]; omega), mB1,
    Mem.read_write_disjoint wfA9 _ _ (by rw [sliceD_len]; omega), mA9_args h1 h2]
theorem mB3_supply : Bytes.toB256 (mB3.read 416 32).1 = 0 := by
  rw [mB3_args (by decide) (by decide)]; exact supply_word
theorem mB3_decimals : Bytes.toB256 (mB3.read 384 32).1 = 18 := by
  rw [mB3_args (by decide) (by decide)]; exact decimals_word
theorem mB4_decimals : Bytes.toB256 (mB4.read 0x180 32).1 = 18 := by
  rw [mB4, Mem.read_write_disjoint wfB3 _ _ (by rw [B256.length_toBytes]; omega)]
  exact mB3_decimals
theorem mB4_supply : Bytes.toB256 (mB4.read 0x2a0 32).1 = 0 := by
  rw [mB4, Mem.read_write_word_of_wf wfB3, B256.toB256_toBytes]
theorem mB4_nameLen : Bytes.toB256 (mB4.read 0x1c0 32).1 = Nat.toB256 22 := by
  rw [mB4, Mem.read_write_disjoint wfB3 _ _ (by rw [B256.length_toBytes]; omega), mB3,
    Mem.read_write_disjoint wfB2 _ _ (by rw [sliceD_len]; omega), mB2,
    Mem.read_write_disjoint wfB1 _ _ (by rw [sliceD_len]; omega), mB1,
    Mem.read_write_disjoint wfA9 _ _ (by rw [sliceD_len]; omega), mA9,
    Mem.read_write_disjoint wfA8 _ _ (by rw [sliceD_len]; omega), mA8,
    read_write_inside wfA7 (le_refl _) (by rw [sliceD_len]; omega)]
  exact nameLen_word
theorem mB4_symbolLen : Bytes.toB256 (mB4.read 0x240 32).1 = Nat.toB256 4 := by
  rw [mB4, Mem.read_write_disjoint wfB3 _ _ (by rw [B256.length_toBytes]; omega), mB3,
    Mem.read_write_disjoint wfB2 _ _ (by rw [sliceD_len]; omega), mB2,
    read_write_inside wfB1 (le_refl _) (by rw [sliceD_len]; omega)]
  exact symbolLen_word

/-- **The prefix, first part** (entry 0 through the `CALLVALUE` check and the name argument's
copy and bounds check): 236 gas, the memory `mA9`. -/
theorem segA {sevm : Sevm} (hcode : sevm.code = code) (hvalue : sevm.value = 0)
    (hdata : sevm.data = []) {b : Devm} {X : Nat} {o : Outcome}
    (k : SFunc.RunExact prog sevm (St b [] mA9 X) t_00d2_c0 o) :
    SFunc.RunExact prog sevm (St b [] Mem.empty (X + 236)) t_0000_c0 o := by
  have hcd : ∀ x : B256, Sevm.dataWord sevm x = 0 := fun x => by
    unfold Sevm.dataWord
    rw [hdata]
    show Bytes.toB256 (List.takeD 32 (List.drop x.toNat []) 0) = 0
    rw [List.drop_nil]
    decide
  unfold t_0000_c0
  refine rx_push (w := clamp1) rfl (by simp) ?_
  refine rx_push (w := 0x20) (by decide) (by simp) ?_
  refine rx_mstore (c := 9) (M' := mA1) ?_ rfl ?_
  · rw [St.extCost_eq (show Mem.empty.size = 0 from rfl)]; decide
  refine rx_push (w := clamp2) rfl (by simp) ?_
  refine rx_push (w := 0x40) (by decide) (by simp) ?_
  refine rx_mstore (c := 6) (M' := mA2) ?_ rfl ?_
  · rw [St.extCost_eq mA1_size]; decide
  refine rx_push (w := clamp3) rfl (by simp) ?_
  refine rx_push (w := 0x60) (by decide) (by simp) ?_
  refine rx_mstore (c := 6) (M' := mA3) ?_ rfl ?_
  · rw [St.extCost_eq mA2_size]; decide
  refine rx_push (w := clamp4) rfl (by simp) ?_
  refine rx_push (w := 0x80) (by decide) (by simp) ?_
  refine rx_mstore (c := 6) (M' := mA4) ?_ rfl ?_
  · rw [St.extCost_eq mA3_size]; decide
  refine rx_push (w := clamp5) rfl (by simp) ?_
  refine rx_push (w := 0xa0) (by decide) (by simp) ?_
  refine rx_mstore (c := 6) (M' := mA5) ?_ rfl ?_
  · rw [St.extCost_eq mA4_size]; decide
  refine rx_push (w := 0x80) (by decide) (by simp) ?_
  refine rx_push (w := 0xb4f) (by decide) (by simp) ?_
  refine rx_push (w := 0x140) (by decide) (by simp) ?_
  refine rx_codecopy (c := 39) (M' := mA6) ?_ (by rw [hcode]; rfl) ?_
  · rw [St.extCost_eq mA5_size]; decide
  refine rx_callvalue (by simp) ?_
  rw [hvalue]
  refine rx_iszero (v := 1) (by decide) (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_00a1_c0
  refine rx_dest ?_
  refine rx_push (w := 0x60) (by decide) (by simp) ?_
  refine rx_push (w := 0x20) (by decide) (by simp) ?_
  refine rx_push (w := 0xb4f) (by decide) (by simp) ?_
  refine rx_push (w := 0xc0) (by decide) (by simp) ?_
  refine rx_codecopy (c := 6) (M' := mA7) ?_ (by rw [hcode]; rfl) ?_
  · rw [St.extCost_eq mA6_size]; decide
  refine rx_push (w := 0xc0) (by decide) (by simp) ?_
  refine rx_mload (c := 3) (v := 0x80) ?_ mA7_arg0 (read_covered mA7_size (by decide) (by decide))
    (by simp) ?_
  · rw [St.extCost_eq mA7_size]; decide
  refine rx_push (w := 0xb4f) (by decide) (by simp) ?_
  refine rx_add' (v := 0xbcf) (by decide) (by simp) ?_
  refine rx_push (w := 0x1c0) (by decide) (by simp) ?_
  refine rx_codecopy (c := 21) (M' := mA8) ?_ (by rw [hcode]; rfl) ?_
  · rw [St.extCost_eq mA7_size]; decide
  refine rx_push (w := 0x40) (by decide) (by simp) ?_
  refine rx_push (w := 0x20) (by decide) (by simp) ?_
  refine rx_push (w := 0xb4f) (by decide) (by simp) ?_
  refine rx_push (w := 0xc0) (by decide) (by simp) ?_
  refine rx_codecopy (c := 6) (M' := mA9) ?_ (by rw [hcode]; rfl) ?_
  · rw [St.extCost_eq mA8_size]; decide
  refine rx_push (w := 0xc0) (by decide) (by simp) ?_
  refine rx_mload (c := 3) (v := 0x80) ?_ mA9_arg0 (read_covered mA9_size (by decide) (by decide))
    (by simp) ?_
  · rw [St.extCost_eq mA9_size]; decide
  refine rx_push (w := 4) (by decide) (by simp) ?_
  refine rx_add' (v := 0x84) (by decide) (by simp) ?_
  refine rx_calldataload (by simp) ?_
  rw [hcd]
  refine rx_gt (v := 0) (by decide) (by simp) ?_
  refine rx_iszero (v := 1) (by decide) (by simp) ?_
  refine rx_push rfl (by simp) ?_
  exact rx_branch_succ (by decide) k

/-- **The prefix, second part** (entry 0's tree from `0xd2`: the symbol argument's copy and
bounds check, the decimals check, `supply · 10^decimals` with its overflow check, and the
product's store at `0x2a0`): 299 gas, the memory `mB4`, up to the name's store head. -/
theorem segB {sevm : Sevm} (hcode : sevm.code = code) (hdata : sevm.data = []) {b : Devm}
    {X : Nat} {o : Outcome}
    (k : SFunc.RunExact prog sevm (St b [] mB4 X) (vyStoreHead 0x01 0xc0 0x00 0x03 t_0162_c0) o) :
    SFunc.RunExact prog sevm (St b [] mA9 (X + 299)) t_00d2_c0 o := by
  have hcd : ∀ x : B256, Sevm.dataWord sevm x = 0 := fun x => by
    unfold Sevm.dataWord
    rw [hdata]
    show Bytes.toB256 (List.takeD 32 (List.drop x.toNat []) 0) = 0
    rw [List.drop_nil]
    decide
  unfold t_00d2_c0
  refine rx_dest ?_
  refine rx_push (w := 0x40) (by decide) (by simp) ?_
  refine rx_push (w := 0x20) (by decide) (by simp) ?_
  refine rx_push (w := 0x20) (by decide) (by simp) ?_
  refine rx_push (w := 0xb4f) (by decide) (by simp) ?_
  refine rx_add' (v := 0xb6f) (by decide) (by simp) ?_
  refine rx_push (w := 0xc0) (by decide) (by simp) ?_
  refine rx_codecopy (c := 6) (M' := mB1) ?_ (by rw [hcode]; rfl) ?_
  · rw [St.extCost_eq mA9_size]; decide
  refine rx_push (w := 0xc0) (by decide) (by simp) ?_
  refine rx_mload (c := 3) (v := 0xc0) ?_ mB1_arg1 (read_covered mB1_size (by decide) (by decide))
    (by simp) ?_
  · rw [St.extCost_eq mB1_size]; decide
  refine rx_push (w := 0xb4f) (by decide) (by simp) ?_
  refine rx_add' (v := 0xc0f) (by decide) (by simp) ?_
  refine rx_push (w := 0x240) (by decide) (by simp) ?_
  refine rx_codecopy (c := 18) (M' := mB2) ?_ (by rw [hcode]; rfl) ?_
  · rw [St.extCost_eq mB1_size]; decide
  refine rx_push (w := 0x20) (by decide) (by simp) ?_
  refine rx_push (w := 0x20) (by decide) (by simp) ?_
  refine rx_push (w := 0x20) (by decide) (by simp) ?_
  refine rx_push (w := 0xb4f) (by decide) (by simp) ?_
  refine rx_add' (v := 0xb6f) (by decide) (by simp) ?_
  refine rx_push (w := 0xc0) (by decide) (by simp) ?_
  refine rx_codecopy (c := 6) (M' := mB3) ?_ (by rw [hcode]; rfl) ?_
  · rw [St.extCost_eq mB2_size]; decide
  refine rx_push (w := 0xc0) (by decide) (by simp) ?_
  refine rx_mload (c := 3) (v := 0xc0) ?_ mB3_arg1 (read_covered mB3_size (by decide) (by decide))
    (by simp) ?_
  · rw [St.extCost_eq mB3_size]; decide
  refine rx_push (w := 4) (by decide) (by simp) ?_
  refine rx_add' (v := 0xc4) (by decide) (by simp) ?_
  refine rx_calldataload (by simp) ?_
  rw [hcd]
  refine rx_gt (v := 0) (by decide) (by simp) ?_
  refine rx_iszero (v := 1) (by decide) (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0109_c0
  refine rx_dest ?_
  refine rx_push (w := 0x1a0) (by decide) (by simp) ?_
  refine rx_mload (c := 3) (v := 0) ?_ mB3_supply (read_covered mB3_size (by decide) (by decide))
    (by simp) ?_
  · rw [St.extCost_eq mB3_size]; decide
  refine rx_push (w := 0x4e) (by decide) (by simp) ?_
  refine rx_push (w := 0x180) (by decide) (by simp) ?_
  refine rx_mload (c := 3) (v := 18) ?_ mB3_decimals (read_covered mB3_size (by decide) (by decide))
    (by simp) ?_
  · rw [St.extCost_eq mB3_size]; decide
  refine rx_lt (v := 1) (by decide) (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_011d_c0
  refine rx_dest ?_
  refine rx_push (w := 0x180) (by decide) (by simp) ?_
  refine rx_mload (c := 3) (v := 18) ?_ mB3_decimals (read_covered mB3_size (by decide) (by decide))
    (by simp) ?_
  · rw [St.extCost_eq mB3_size]; decide
  refine rx_push (w := 10) (by decide) (by simp) ?_
  refine rx_exp' (c := 60) (by decide) (by simp) ?_
  refine rx_dup (n := 0) rfl (by simp) ?_
  refine rx_dup (n := 2) rfl (by simp) ?_
  refine rx_mul (v := 0) (by decide +kernel) (by simp) ?_
  refine rx_dup (n := 2) rfl (by simp) ?_
  refine rx_iszero (v := 1) (by decide) (by simp) ?_
  refine rx_dup (n := 2) rfl (by simp) ?_
  refine rx_dup (n := 4) rfl (by simp) ?_
  refine rx_dup (n := 3) rfl (by simp) ?_
  refine rx_div (v := 0) (by decide) (by simp) ?_
  refine rx_eq (v := 0) (by decide +kernel) (by simp) ?_
  refine rx_or (v := 1) (by decide) (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0138_c0
  refine rx_dest ?_
  refine rx_dup (n := 0) rfl (by simp) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_push (w := 0x2a0) (by decide) (by simp) ?_
  refine rx_mstore (c := 9) (M' := mB4) ?_ rfl k
  rw [St.extCost_eq mB3_size]; decide

/-! ## The whole constructor -/

/-- Reads away from the loop's scratch words (`0xc0`, `0x120`) see the memory before the loop. -/
theorem loopMem_read_other {M : Mem} (hwf : Mem.Wf M) {sl : UInt8} {a : Nat}
    (ha : 0x140 ≤ a) : ∀ i, ((loopMem M sl i).read a 32).1 = (M.read a 32).1
  | 0 => by
    unfold loopMem headMem
    rw [Mem.read_write_disjoint (hwf.write _ _) _ _ (by rw [B256.length_toBytes]; omega),
      Mem.read_write_disjoint hwf _ _ (by rw [B256.length_toBytes]; omega)]
  | i + 1 => by
    unfold loopMem
    rw [Mem.read_write_disjoint (loopMem_wf hwf i) _ _ (by rw [B256.length_toBytes]; omega),
      loopMem_read_other hwf ha i]

theorem loopWorld_error {sevm : Sevm} {b : Devm} {M : Mem} {sl : UInt8} {src : Nat} :
    ∀ i, (loopWorld sevm b M sl src i).error = b.error
  | 0 => rfl
  | i + 1 => by rw [loopWorld, afterSstore_error, loopWorld_error i]

theorem loopWorld_stor2 {sevm : Sevm} {b : Devm} {M : Mem} {sl : UInt8} {src : Nat} :
    Devm.getStor (loopWorld sevm b M sl src 2) sevm.currentTarget =
      ((Devm.getStor b sevm.currentTarget).set (strBase sl + Nat.toB256 0) (loopWord M sl src 0)).set
        (strBase sl + Nat.toB256 1) (loopWord M sl src 1) := by
  simp only [loopWorld, afterSstore_getStor_self]

/-- The name and symbol stores' memories. -/
def memName : Mem := loopMem mB4 0x00 2
def memSymbol : Mem := loopMem memName 0x01 2

theorem memName_size : memName.size = 704 := loopMem_size mB4_size 2
theorem memName_wf : Mem.Wf memName := loopMem_wf mB4_wf 2
theorem memSymbol_size : memSymbol.size = 704 := loopMem_size memName_size 2
theorem memSymbol_wf : Mem.Wf memSymbol := loopMem_wf memName_wf 2

/-- The worlds after the name and symbol stores. -/
def worldName (sevm : Sevm) (b : Devm) : Devm := loopWorld sevm b mB4 0x00 0x1c0 2
def worldSymbol (sevm : Sevm) (b : Devm) : Devm :=
  loopWorld sevm (worldName sevm b) memName 0x01 0x240 2

/-- The constructor's exact cost from the world `b`. -/
def ctorCost (sevm : Sevm) (b : Devm) : Nat :=
  tailCost sevm (worldSymbol sevm b) + 117 +
    loopCost sevm (worldName sevm b) memName 0x01 0x240 1 + 117 +
    loopCost sevm (worldName sevm b) memName 0x01 0x240 0 + 90 + 13 + 48 + 117 +
    loopCost sevm b mB4 0x00 0x1c0 1 + 117 + loopCost sevm b mB4 0x00 0x1c0 0 + 90 + 299 + 236

theorem ctorCost_le (sevm : Sevm) (b : Devm) : ctorCost sevm b ≤ 200000 := by
  have hs : ∀ (b : Devm) (k v : B256), sstoreCost sevm b k v ≤ 22100 := fun b k v =>
    le_trans (sstoreCost_le sevm b k v) (by decide)
  unfold ctorCost tailCost loopCost
  have := hs (worldSymbol sevm b) 2 18
  have := hs (tw4 sevm (worldSymbol sevm b)) (balSlotOf sevm.caller.toB256) 0
  have := hs (tw5 sevm (worldSymbol sevm b)) 5 0
  have := hs (tw6 sevm (worldSymbol sevm b)) 6 sevm.caller.toB256
  have := hs (loopWorld sevm (worldName sevm b) memName 0x01 0x240 1) (strBase 0x01 + Nat.toB256 1)
    (loopWord memName 0x01 0x240 1)
  have := hs (loopWorld sevm (worldName sevm b) memName 0x01 0x240 0) (strBase 0x01 + Nat.toB256 0)
    (loopWord memName 0x01 0x240 0)
  have := hs (loopWorld sevm b mB4 0x00 0x1c0 1) (strBase 0x00 + Nat.toB256 1)
    (loopWord mB4 0x00 0x1c0 1)
  have := hs (loopWorld sevm b mB4 0x00 0x1c0 0) (strBase 0x00 + Nat.toB256 0)
    (loopWord mB4 0x00 0x1c0 0)
  omega

/-- **The 3Crv constructor, gas-exact**: from a fresh creation frame (zero call value, empty
call data) with an empty stack and memory and `G + ctorCost` gas, the lifted constructor halts
with `G` gas left, returning the runtime window, with the world's error unchanged. -/
theorem ctor_run {sevm : Sevm} (fr : CtorFrame sevm) (hcode : sevm.code = code)
    (hvalue : sevm.value = 0) (hdata : sevm.data = []) {b : Devm} {G : Nat} (hG : 2300 < G) :
    SProg.RunExact prog sevm (St b [] Mem.empty (G + ctorCost sevm b))
      (returnPost (St (tw8 sevm (worldSymbol sevm b) memSymbol)
        [Nat.toB256 0, Nat.toB256 2276] (tailMem3 memSymbol sevm.caller.toB256) G)
        (Nat.toB256 0) (Nat.toB256 2276) []) := by
  refine ⟨t_0000_c0, rfl, ?_⟩
  have hX : gCallStipend < G := hG
  rw [show G + ctorCost sevm b = G + tailCost sevm (worldSymbol sevm b) + 117 +
    loopCost sevm (worldName sevm b) memName 0x01 0x240 1 + 117 +
    loopCost sevm (worldName sevm b) memName 0x01 0x240 0 + 90 + 13 + 48 + 117 +
    loopCost sevm b mB4 0x00 0x1c0 1 + 117 + loopCost sevm b mB4 0x00 0x1c0 0 + 90 + 299 + 236
    by unfold ctorCost; omega]
  refine segA hcode hvalue hdata (segB hcode hdata ?_)
  refine storeName fr mB4_size mB4_wf mB4_nameLen (by omega) ?_
  refine storeSymbol fr memName_size memName_wf ?_ (by omega) ?_
  · rw [memName, loopMem_read_other mB4_wf (by decide)]; exact mB4_symbolLen
  refine tail fr hcode memSymbol_size memSymbol_wf ?_ ?_ hX
  · rw [memSymbol, loopMem_read_other memName_wf (by decide), memName,
      loopMem_read_other mB4_wf (by decide)]
    exact mB4_decimals
  · rw [memSymbol, loopMem_read_other memName_wf (by decide), memName,
      loopMem_read_other mB4_wf (by decide)]
    exact mB4_supply

theorem tailMem2_wf {M : Mem} (hwf : Mem.Wf M) (c : B256) : Mem.Wf (tailMem2 M c) :=
  ((hwf.write _ _).write _ _).write _ _

/-- The returned window, over any well-formed memory (stated over a variable memory so that
nothing evaluates a concrete image). -/
theorem tailMem3_read {M : Mem} (hwf : Mem.Wf M) (c : B256) :
    ((tailMem3 M c).read 0 2276).1 = runtimeWindow := by
  have hr : Mem.Reads (tailMem3 M c) (Bytes.writeAt (tailMem2 M c).data.toList 0 runtimeWindow) :=
    (Mem.reads_data _).write (tailMem2_wf hwf c) 0 _
  rw [hr.read]
  have := Bytes.sliceD_writeAt (tailMem2 M c).data.toList runtimeWindow 0
  rwa [runtimeWindow_length] at this

/-- **The 3Crv constructor, with its halting state's facts**: output the runtime window, the
world's error, the tail's storage, `G` gas left. -/
theorem ctor_run_facts {sevm : Sevm} (fr : CtorFrame sevm) (hcode : sevm.code = code)
    (hvalue : sevm.value = 0) (hdata : sevm.data = []) {b : Devm} {G : Nat} (hG : 2300 < G) :
    ∃ post, SProg.RunExact prog sevm (St b [] Mem.empty (G + ctorCost sevm b)) post ∧
      post.output = runtimeWindow ∧ post.error = b.error ∧
      Devm.getStor post sevm.currentTarget =
        Devm.getStor (tw8 sevm (worldSymbol sevm b) memSymbol) sevm.currentTarget ∧
      post.gasLeft = G := by
  obtain ⟨p1, p2, p3, p4⟩ := returnPost_facts (St (tw8 sevm (worldSymbol sevm b) memSymbol)
    [Nat.toB256 0, Nat.toB256 2276] (tailMem3 memSymbol sevm.caller.toB256) G) (Nat.toB256 0)
    (Nat.toB256 2276) []
  refine ⟨_, ctor_run fr hcode hvalue hdata hG, ?_, ?_, ?_, p4⟩
  · rw [p1, St.memory, toNat_toB256' (show 2276 < 2 ^ 256 by decide),
      toNat_toB256' (show 0 < 2 ^ 256 by decide)]
    exact tailMem3_read memSymbol_wf _
  · rw [p2, St_error]
    simp only [tw8, Devm.addLog_error, tw7, tw6, tw5, tw4, afterSstore_error, worldSymbol,
      loopWorld_error, worldName]
  · rw [p3, St_getStor]

end Blanc.Lift.Curve3Crv.Creation
