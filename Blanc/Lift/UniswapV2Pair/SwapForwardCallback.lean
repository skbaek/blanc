import Blanc.Lift.UniswapV2Pair.SwapForwardTransfer
import Blanc.Lift.UniswapV2Pair.SwapCallback

/-! Forward (gas-exact) conditional `uniswapV2Call` callback of the swap body
(`t_08e1_c4..t_09c3_c5`), the mirror of `swapCallback_inv`: empty data skips it; otherwise
the body builds the model's callback calldata at the free pointer, checks the recipient's code
and makes the actual `CALL`, whose callee frame is a forward-environment premise. The memory
charge is closed in the pointer, the entry memory size and the data length. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The whole charge of a memory access of `l` bytes at `j` over memory of size `s`, beyond
the base cost: the expansion to `memExtSize s j l`. -/
def swapMemExpand (s j l : Nat) : Nat :=
  calculateMemoryGasCost (memExtSize s j l) - calculateMemoryGasCost s

private theorem swapFwdCb_gas {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256}
    {M : Mem} {G G' : Nat} {f : SFunc} {o : Outcome} (h : G = G')
    (k : SFunc.RunExact fs sevm (St b S M G') f o) :
    SFunc.RunExact fs sevm (St b S M G) f o := h ▸ k

/-- `MSTORE` of a word above the free-pointer slot, threading the free-pointer carrier. -/
private theorem swapFwd_mstore {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256}
    {M : Mem} {G s j : Nat} {q i v : B256} {f : SFunc} {o : Outcome}
    (hj : i.toNat = j) (mem : PtrMem q s M) (miss : 96 ≤ j)
    (k : PtrMem q (memExtSize s j 32) (M.write j v.toBytes) →
      SFunc.RunExact fs sevm (St b S (M.write j v.toBytes) G) f o) :
    SFunc.RunExact fs sevm (St b (i :: v :: S) M (G + (3 + swapMemExpand s j 32)))
      (.next (.reg .mstore) f) o := by
  have next := mem.write_bytes j v.toBytes (Or.inr miss)
  rw [B256.length_toBytes] at next
  refine rx_mstore ?_ (by rw [hj]) (k next)
  simp only [Devm.extCost, St, Devm.memory_setMach, memExtsSize, hj, mem.size, swapMemExpand]
  rfl

/-- `CALLDATACOPY` above the free-pointer slot, threading the free-pointer carrier. -/
private theorem swapFwd_calldatacopy {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {S : List B256} {M : Mem} {G s j : Nat} {q di si sz : B256} {f : SFunc} {o : Outcome}
    (hj : di.toNat = j) (mem : PtrMem q s M) (miss : 96 ≤ j)
    (k : PtrMem q (memExtSize s j sz.toNat) (M.write j (sevm.data.sliceD si.toNat sz.toNat 0)) →
      SFunc.RunExact fs sevm
        (St b S (M.write j (sevm.data.sliceD si.toNat sz.toNat 0)) G) f o) :
    SFunc.RunExact fs sevm (St b (di :: si :: sz :: S) M
        (G + (3 + gasCopy * ceilDiv sz.toNat 32 + swapMemExpand s j sz.toNat)))
      (.next (.reg .calldatacopy) f) o := by
  have next := mem.write_bytes j (sevm.data.sliceD si.toNat sz.toNat 0) (Or.inr miss)
  rw [List.length_sliceD] at next
  refine rx_calldatacopy ?_ (by rw [hj]) (k next)
  simp only [Devm.extCost, St, Devm.memory_setMach, memExtsSize, hj, mem.size, swapMemExpand]
  rfl

/-- `MLOAD` of the free-pointer word: 3 gas, no expansion. -/
private theorem swapFwd_mload64 {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256}
    {M : Mem} {G s : Nat} {q : B256} {f : SFunc} {o : Outcome}
    (mem : PtrMem q s M) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (q :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (Bytes.toB256 [64] :: S) M (G + 3)) (.next (.reg .mload) f) o := by
  have fit : 64 + 32 ≤ s := by have := mem.ge; omega
  refine rx_mload ?_ mem.word (mem.read_self fit) hroom k
  simp only [Devm.extCost, St, Devm.memory_setMach, memExtsSize,
    show (Bytes.toB256 [64]).toNat = 64 from rfl, mem.size, memExtSize_of_le mem.n32 fit,
    Nat.sub_self]
  rfl

/-- Straight-line forward steps of the callback build. -/
macro "sfc_rx" : tactic => `(tactic| first
  | apply rx_dest
  | apply rx_push rfl (by simp only [List.length_cons]; omega)
  | apply rx_dup rfl (by simp only [List.length_cons]; omega)
  | (apply rx_swap rfl; dsimp only [List.set])
  | apply rx_pop
  | apply rx_and rfl (by simp only [List.length_cons]; omega)
  | apply rx_add (by simp only [List.length_cons]; omega)
  | apply rx_sub (by simp only [List.length_cons]; omega)
  | apply rx_shl rfl (by simp only [List.length_cons]; omega)
  | apply rx_not rfl (by simp only [List.length_cons]; omega)
  | apply rx_caller (by simp only [List.length_cons]; omega)
  | apply rx_iszero rfl (by simp only [List.length_cons]; omega))

/-- The callback's calldata memory: the eight ordered writes at the free pointer `q`. -/
abbrev swapCallbackMemOf (sevm : Sevm) (M : Mem) (q a0 a1 len start : B256) : Mem :=
  swapCallbackMem M q.toNat swapCallbackSelectorWord sevm.caller.toB256 a0 a1 len
    (sevm.data.sliceD start.toNat len.toNat 0)

/-- The primitive data of the actual callback `CALL`: the recipient has code, the call step
from the built calldata (after the code check warmed the recipient), its success flag and its
residual gas. -/
structure SwapCallbackCallForward (sevm : Sevm) (b : Devm) (L : List B256) (M : Mem)
    (q toWord a0 a1 len start : B256) (callGas G : Nat) (d : Devm) : Prop where
  code : (b.getCode ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toAdr).size.toB256 ≠ 0
  call : Ninst.RunCompiled sevm
    (St (temporalAccountAccessBase b ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toAdr)
      (callGas.toB256 :: ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord) :: 0 :: q ::
        (swapCallbackEnd q len - q) :: q :: 0 :: swapCallbackEnd q len :: 0x10d1e85c ::
        ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord) :: L)
      (swapCallbackMemOf sevm M q a0 a1 len start) callGas) (.exec .call) d
  success : d.stack = 1 :: swapCallbackEnd q len :: 0x10d1e85c ::
    ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord) :: L
  gas : d.gasLeft = G + 31

/-- The callback arm's charge up to its `CALL` state, closed in the recipient's access, the
entry memory size `n`, the free pointer `q` and the data length `l`: 334 gas of straight-line
code and stores, the recipient's warm/cold `EXTCODESIZE` access, the data copy, and the memory
expansions of the eight ordered calldata writes. -/
def swapCallbackGas (b : Devm) (target : Adr) (n q l : Nat) : Nat :=
  let s1 := memExtSize n q 32
  let s2 := memExtSize s1 (q + 4) 32
  let s3 := memExtSize s2 (q + 36) 32
  let s4 := memExtSize s3 (q + 68) 32
  let s5 := memExtSize s4 (q + 100) 32
  let s6 := memExtSize s5 (q + 132) 32
  let s7 := memExtSize s6 (q + 164) l
  temporalAccountAccessCost b target + swapMemExpand n q 32 + swapMemExpand s1 (q + 4) 32 +
    swapMemExpand s2 (q + 36) 32 + swapMemExpand s3 (q + 68) 32 + swapMemExpand s4 (q + 100) 32 +
    swapMemExpand s5 (q + 132) 32 + swapMemExpand s6 (q + 164) l +
    swapMemExpand s7 (q + 164 + l) 32 + gasCopy * ceilDiv l 32 + 334

theorem swapFwdCallback_call {sevm : Sevm} {b d : Devm} {R : List B256} {M : Mem}
    {n G cg : Nat} {q t1 t0 r1 r0 len start toWord a1 a0 ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (room : R.length ≤ 980)
    (mem : PtrMem q n M) (lower : 128 ≤ q.toNat) (upper : q.toNat < 2 ^ 163)
    (short : len.toNat ≤ 2 ^ 32) (nonzero : len ≠ 0)
    (env : SwapCallbackCallForward sevm b
      (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R) M
      q toWord a0 a1 len start cg G d)
    (cont : SFunc.RunExact cert.prog sevm
      (St d (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R)
        d.memory G) t_09c3_c5 o) :
    SFunc.RunExact cert.prog sevm
      (St b (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R) M
        (cg + swapCallbackGas b ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toAdr
          n q.toNat len.toNat)) t_08e1_c4 o := by
  have a4 : (4 + q).toNat = q.toNat + 4 := by
    rw [B256.toNat_add, show (4 : B256).toNat = 4 from rfl, Nat.lo_eq_of_lt (by omega), Nat.add_comm]
  have a36 : (32 + (4 + q)).toNat = q.toNat + 36 := by
    rw [B256.toNat_add, a4, show (32 : B256).toNat = 32 from rfl, Nat.lo_eq_of_lt (by omega)]
    omega
  have a68 : (32 + (32 + (4 + q))).toNat = q.toNat + 68 := by
    rw [B256.toNat_add, a36, show (32 : B256).toNat = 32 from rfl, Nat.lo_eq_of_lt (by omega)]
    omega
  have a100 : (32 + (32 + (32 + (4 + q)))).toNat = q.toNat + 100 := by
    rw [B256.toNat_add, a68, show (32 : B256).toNat = 32 from rfl, Nat.lo_eq_of_lt (by omega)]
    omega
  have a132 : (32 + (32 + (32 + (32 + (4 + q))))).toNat = q.toNat + 132 := by
    rw [B256.toNat_add, a100, show (32 : B256).toNat = 32 from rfl, Nat.lo_eq_of_lt (by omega)]
    omega
  have a164 : (32 + (32 + (32 + (32 + (32 + (4 + q)))))).toNat = q.toNat + 164 := by
    rw [B256.toNat_add, a132, show (32 : B256).toNat = 32 from rfl, Nat.lo_eq_of_lt (by omega)]
    omega
  have aend : (32 + (32 + (32 + (32 + (32 + (4 + q))))) + len).toNat =
      q.toNat + 164 + len.toNat := by
    rw [B256.toNat_add, a164, Nat.lo_eq_of_lt (by omega)]
  have v128 : 32 + (32 + (32 + (32 + (4 + q)))) - (4 + q) = (128 : B256) := by
    apply B256.toNat_inj
    rw [B256.toNat_sub_eq_of_le _ _ (B256.le_of_toNat_le_toNat (by rw [a132, a4]; omega)), a132, a4,
      show (128 : B256).toNat = 128 from rfl]
    omega
  dsimp only [swapCallbackGas]
  generalize hs1 : memExtSize n q.toNat 32 = s1
  generalize hs2 : memExtSize s1 (q.toNat + 4) 32 = s2
  generalize hs3 : memExtSize s2 (q.toNat + 36) 32 = s3
  generalize hs4 : memExtSize s3 (q.toNat + 68) 32 = s4
  generalize hs5 : memExtSize s4 (q.toNat + 100) 32 = s5
  generalize hs6 : memExtSize s5 (q.toNat + 132) 32 = s6
  generalize hs7 : memExtSize s6 (q.toNat + 164) len.toNat = s7
  rw [show (0xffffffffffffffffffffffffffffffffffffffff : B256) = Bytes.toB256 [255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] from rfl]
  unfold t_08e1_c4
  apply swapFwdCb_gas (G' := (cg + temporalAccountAccessCost b (Bytes.toB256 [255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] &&& toWord).toAdr +
    swapMemExpand s1 (q.toNat + 4) 32 + swapMemExpand s2 (q.toNat + 36) 32 +
    swapMemExpand s3 (q.toNat + 68) 32 + swapMemExpand s4 (q.toNat + 100) 32 +
    swapMemExpand s5 (q.toNat + 132) 32 + swapMemExpand s6 (q.toNat + 164) len.toNat +
    swapMemExpand s7 (q.toNat + 164 + len.toNat) 32 + gasCopy * ceilDiv len.toNat 32 + 261) +
    (3 + swapMemExpand n q.toNat 32) + 70) (by omega)
  sfc_rx; sfc_rx; sfc_rx; sfc_rx
  rw [show B256.eqCheck len 0 = 0 by simp only [B256.eqCheck, nonzero, ite_false]]
  apply rx_branchTo_zero
  unfold t_08e8_c4
  repeat sfc_rx
  refine swapFwd_mload64 mem (by simp only [List.length_cons]; omega) ?_
  repeat sfc_rx
  rw [show (Bytes.toB256 [255, 255, 255, 255] &&& Bytes.toB256 [16, 209, 232, 92]) <<<
    (Bytes.toB256 [224]).toNat = swapCallbackSelectorWord from by decide]
  refine swapFwd_mstore rfl mem (by omega) (fun mem1 => ?_)
  rw [hs1] at mem1
  repeat sfc_rx
  rw [show Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] &&& (Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] &&& sevm.caller.toB256) = sevm.caller.toB256 from by
    rw [ff20_and_word sevm.caller.toB256, toAdr_toB256, ff20_and_word, toAdr_toB256]]
  try rw [show Bytes.toB256 [4] = (4 : B256) from rfl]
  try rw [show Bytes.toB256 [32] = (32 : B256) from rfl]
  apply swapFwdCb_gas (G' := (cg + temporalAccountAccessCost b (Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] &&& toWord).toAdr + swapMemExpand s2 (q.toNat + 36) 32 + swapMemExpand s3 (q.toNat + 68) 32 + swapMemExpand s4 (q.toNat + 100) 32 + swapMemExpand s5 (q.toNat + 132) 32 + swapMemExpand s6 (q.toNat + 164) len.toNat + swapMemExpand s7 (q.toNat + 164 + len.toNat) 32 + gasCopy * ceilDiv len.toNat 32 + 231) + (3 + swapMemExpand s1 (q.toNat + 4) 32)) (by omega)
  refine swapFwd_mstore (j := q.toNat + 4) a4 mem1 (by omega) (fun mem2 => ?_)
  rw [hs2] at mem2
  repeat sfc_rx
  try rw [show Bytes.toB256 [4] = (4 : B256) from rfl]
  try rw [show Bytes.toB256 [32] = (32 : B256) from rfl]
  apply swapFwdCb_gas (G' := (cg + temporalAccountAccessCost b (Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] &&& toWord).toAdr + swapMemExpand s3 (q.toNat + 68) 32 + swapMemExpand s4 (q.toNat + 100) 32 + swapMemExpand s5 (q.toNat + 132) 32 + swapMemExpand s6 (q.toNat + 164) len.toNat + swapMemExpand s7 (q.toNat + 164 + len.toNat) 32 + gasCopy * ceilDiv len.toNat 32 + 216) + (3 + swapMemExpand s2 (q.toNat + 36) 32)) (by omega)
  refine swapFwd_mstore (j := q.toNat + 36) a36 mem2 (by omega) (fun mem3 => ?_)
  rw [hs3] at mem3
  repeat sfc_rx
  try rw [show Bytes.toB256 [4] = (4 : B256) from rfl]
  try rw [show Bytes.toB256 [32] = (32 : B256) from rfl]
  apply swapFwdCb_gas (G' := (cg + temporalAccountAccessCost b (Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] &&& toWord).toAdr + swapMemExpand s4 (q.toNat + 100) 32 + swapMemExpand s5 (q.toNat + 132) 32 + swapMemExpand s6 (q.toNat + 164) len.toNat + swapMemExpand s7 (q.toNat + 164 + len.toNat) 32 + gasCopy * ceilDiv len.toNat 32 + 201) + (3 + swapMemExpand s3 (q.toNat + 68) 32)) (by omega)
  refine swapFwd_mstore (j := q.toNat + 68) a68 mem3 (by omega) (fun mem4 => ?_)
  rw [hs4] at mem4
  repeat sfc_rx
  try rw [show Bytes.toB256 [4] = (4 : B256) from rfl]
  try rw [show Bytes.toB256 [32] = (32 : B256) from rfl]
  rw [v128]
  apply swapFwdCb_gas (G' := (cg + temporalAccountAccessCost b (Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] &&& toWord).toAdr + swapMemExpand s5 (q.toNat + 132) 32 + swapMemExpand s6 (q.toNat + 164) len.toNat + swapMemExpand s7 (q.toNat + 164 + len.toNat) 32 + gasCopy * ceilDiv len.toNat 32 + 171) + (3 + swapMemExpand s4 (q.toNat + 100) 32)) (by omega)
  refine swapFwd_mstore (j := q.toNat + 100) a100 mem4 (by omega) (fun mem5 => ?_)
  rw [hs5] at mem5
  repeat sfc_rx
  try rw [show Bytes.toB256 [4] = (4 : B256) from rfl]
  try rw [show Bytes.toB256 [32] = (32 : B256) from rfl]
  apply swapFwdCb_gas (G' := (cg + temporalAccountAccessCost b (Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] &&& toWord).toAdr + swapMemExpand s6 (q.toNat + 164) len.toNat + swapMemExpand s7 (q.toNat + 164 + len.toNat) 32 + gasCopy * ceilDiv len.toNat 32 + 153) + (3 + swapMemExpand s5 (q.toNat + 132) 32)) (by omega)
  refine swapFwd_mstore (j := q.toNat + 132) a132 mem5 (by omega) (fun mem6 => ?_)
  rw [hs6] at mem6
  repeat sfc_rx
  try rw [show Bytes.toB256 [4] = (4 : B256) from rfl]
  try rw [show Bytes.toB256 [32] = (32 : B256) from rfl]
  apply swapFwdCb_gas (G' := (cg + temporalAccountAccessCost b (Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] &&& toWord).toAdr + swapMemExpand s7 (q.toNat + 164 + len.toNat) 32 + 130) + (3 + gasCopy * ceilDiv len.toNat 32 + swapMemExpand s6 (q.toNat + 164) len.toNat)) (by omega)
  refine swapFwd_calldatacopy (j := q.toNat + 164) a164 mem6 (by omega) (fun mem7 => ?_)
  rw [hs7] at mem7
  repeat sfc_rx
  try rw [show Bytes.toB256 [4] = (4 : B256) from rfl]
  try rw [show Bytes.toB256 [32] = (32 : B256) from rfl]
  apply swapFwdCb_gas (G' := (cg + temporalAccountAccessCost b (Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] &&& toWord).toAdr + 115) + (3 + swapMemExpand s7 (q.toNat + 164 + len.toNat) 32)) (by omega)
  refine swapFwd_mstore (j := q.toNat + 164 + len.toNat) aend mem7 (by omega) (fun mem8 => ?_)
  repeat sfc_rx
  refine swapFwd_mload64 mem8 (by simp only [List.length_cons]; omega) ?_
  repeat sfc_rx
  apply swapFwdCb_gas (G' := (cg + 27) + temporalAccountAccessCost b (Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] &&& toWord).toAdr) (by omega)
  apply rx_extcodesize fork (by simp only [List.length_cons]; omega)
  repeat sfc_rx
  refine rx_branch_succ ?_ ?_
  · have code := env.code
    rw [show (0xffffffffffffffffffffffffffffffffffffffff : B256) = Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] from rfl] at code
    intro h
    apply code
    by_cases z : (b.getCode (Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] &&& toWord).toAdr).size.toB256 = 0
    · exact z
    · simp only [B256.eqCheck, z, ite_false, ite_true] at h
      exact absurd h (by decide)
  unfold t_09aa_c4
  sfc_rx; sfc_rx
  apply rx_gas (by simp only [List.length_cons]; omega)
  have memEq : ((((((((M.write q.toNat swapCallbackSelectorWord.toBytes).write (q.toNat + 4)
      sevm.caller.toB256.toBytes).write (q.toNat + 36) a0.toBytes).write (q.toNat + 68)
      a1.toBytes).write (q.toNat + 100) (B256.toBytes 128)).write (q.toNat + 132) len.toBytes).write
      (q.toNat + 164) (List.sliceD sevm.data start.toNat len.toNat 0)).write
      (q.toNat + 164 + len.toNat) (Bytes.toB256 [0]).toBytes) =
      swapCallbackMemOf sevm M q a0 a1 len start := by
    simp only [swapCallbackMemOf, swapCallbackMem, List.length_sliceD]
    rfl
  rw [memEq, show Bytes.toB256 [0] = (0 : B256) from rfl,
    show Bytes.toB256 [31] = (31 : B256) from rfl,
    show Bytes.toB256 [16, 209, 232, 92] = (0x10d1e85c : B256) from rfl,
    show Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] = (0xffffffffffffffffffffffffffffffffffffffff : B256) from rfl]
  refine SFunc.RunExact.next env.call ?_
  rw [St.self env.success rfl, env.gas]
  sfc_rx; sfc_rx; sfc_rx; sfc_rx
  refine rx_branch_succ (by decide) ?_
  unfold t_09be_c4
  sfc_rx; sfc_rx; sfc_rx; sfc_rx; sfc_rx
  exact cont

/-- The callback skipped (`data.length = 0`): 20 gas, straight to the join. -/
theorem swapFwdCallback_skip {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat}
    {t1 t0 r1 r0 len start toWord a1 a0 ρ : B256} {o : Outcome} (room : R.length ≤ 980)
    (zero : len = 0)
    (cont : SFunc.RunExact cert.prog sevm
      (St b (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R) M G)
      t_09c3_c5 o) :
    SFunc.RunExact cert.prog sevm
      (St b (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R) M
        (G + 20)) t_08e1_c4 o := by
  subst zero
  unfold t_08e1_c4
  sfc_rx; sfc_rx; sfc_rx; sfc_rx
  exact rx_branchTo_succ (by decide) (show cert.prog[5]? = some t_09c3_c5 from rfl) cont

/-- The actual callback `CALL` leaves a free-pointer carrier at the same pointer and the
caller's output buffer. -/
theorem SwapCallbackCallForward.post {sevm : Sevm} {b d : Devm} {L : List B256} {M : Mem}
    {n : Nat} {q toWord a0 a1 len start : B256} {callGas G : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem q n M) (lower : 128 ≤ q.toNat)
    (env : SwapCallbackCallForward sevm b L M q toWord a0 a1 len start callGas G d) :
    (∃ n', PtrMem q n' d.memory) ∧ d.output = b.output := by
  have raw : Ninst.Run sevm
      (St (temporalAccountAccessBase b ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toAdr)
        (callGas.toB256 :: ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord) :: 0 :: q ::
          (swapCallbackEnd q len - q) :: q :: 0 :: swapCallbackEnd q len :: 0x10d1e85c ::
          ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord) :: L)
        (swapCallbackMemOf sevm M q a0 a1 len start) callGas) (.exec .call) d := by
    obtain ⟨xl, filled, step⟩ := env.call
    exact ⟨xl, filled, 0, step 0⟩
  obtain ⟨flag, postState⟩ := ri_call_post fork raw
  have flagOne : flag = 1 := (List.cons.inj (postState.stack.symm.trans env.success)).1
  have settled := postState.settled (by rw [flagOne]; decide)
  obtain ⟨m', mcb⟩ := swapCallbackMem_ptr mem (by omega : 96 ≤ q.toNat) swapCallbackSelectorWord
    sevm.caller.toB256 a0 a1 len (sevm.data.sliceD start.toNat len.toNat 0)
  have mcb' : PtrMem q m' (swapCallbackMemOf sevm M q a0 a1 len start) := mcb
  have extends2 : ∀ (W : Mem) (i1 k1 i2 k2 : Nat),
      (W.extends [(i1, k1), (i2, k2)]).write i2 [] = ((W.read i1 k1).2.read i2 k2).2 :=
    fun _ _ _ _ _ => rfl
  refine ⟨?_, settled.2.trans ?_⟩
  · rw [settled.1, show (0 : B256).toNat = 0 from rfl, List.take_zero]
    generalize swapCallbackMemOf sevm M q a0 a1 len start = W at mcb'
    rw [extends2]
    exact ⟨_, (mcb'.extend _ _).extend _ _⟩
  · unfold temporalAccountAccessBase
    split <;> rfl

end Blanc.Lift.UniswapV2Pair
