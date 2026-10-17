import Blanc.Composition.UniswapV2PairWeth9LegsSkim

/-!
# Skim's second WETH9 query with WETH9 = token1 (C4(b), U8b2)

`SkimForwardEnv.qenv1` is skim's second `balanceOf(pair)` query, staged at the pointer the first
transfer moved over `skimRequestMemory`.  That memory is the swap's `swapBalanceRequest` over the
first transfer's memory widened to the free-pointer word (`skimRequestMemory_eq`), so the query is
the generic read leg (`skimWethRead1`).  Code-only: WETH9's code at `token1` after X's transfer and
the reserve1 load; nothing is assumed of X's transfer callee beyond the memory facts the row already
derives from its record (`skimTransferLayout`).
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair

/-- Skim's second request is the swap's balance request over the memory widened to the
free-pointer word. -/
theorem skimRequestMemory_eq {X : Mem} {p : B256} {n : Nat} (pair : Adr) (mem : PtrMem p n X)
    (low : 96 ≤ p.toNat) (high : p.toNat + 1024 < 2 ^ 256) :
    skimRequestMemory X p pair = swapBalanceRequest (X.read 64 32).2 p pair := by
  have p4 : (p + 4).toNat = p.toNat + 4 :=
    B256.toNat_add_eq_of_nof _ _ (by change p.toNat + 4 < 2 ^ 256; omega)
  have hY := ((mem.extend 64 32).write p.toNat balanceOfSelectorWord (Or.inr low)).write
    (p + 4).toNat pair.toB256 (Or.inr (by rw [p4]; omega))
  unfold skimRequestMemory swapBalanceRequest
  change ((((X.read 64 32).2.write p.toNat balanceOfSelectorWord.toBytes).write
    (p + 4).toNat pair.toB256.toBytes).read 64 32).2 = _
  generalize hYdef : (((X.read 64 32).2.write p.toNat balanceOfSelectorWord.toBytes).write
    (p + 4).toNat pair.toB256.toBytes) = Y at hY
  obtain ⟨data, size⟩ := Y
  have h32 := hY.n32
  have hge := hY.ge
  rw [← hY.size] at h32 hge
  change (⟨data, memExtSize size 64 32⟩ : Mem) = ⟨data, size⟩
  rw [memExtSize_of_le h32 (by omega)]

/-- The masked `token1` word skim's second query stages. -/
abbrev skimT1 (sevm : Sevm) (b : Devm) : B256 :=
  Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& skimToken1 sevm b

theorem skimT1_eq (sevm : Sevm) (b : Devm) : skimT1 sevm b = (skimToken1 sevm b).toAdr.toB256 := by
  unfold skimT1
  rw [B256.and_comm, show Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] = ~~~ addressMask from by decide,
    and_mask_word]

theorem swapTokenWord_skimT1 (sevm : Sevm) (b : Devm) : swapTokenWord (skimT1 sevm b) = skimT1 sevm b := by
  rw [skimT1_eq, swapTokenWord_adr]

section Read1

variable (sevm : Sevm) (b qd0 dt0 : Devm) (callGasT1 : Nat)

/-- The first transfer's memory, which skim's second request widens. -/
def skimRead1Base : Mem :=
  swapTransferMemory (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
    128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b) (skimToWord sevm)
    dt0.returnData

/-- The pointer the first transfer moved. -/
def skimRead1Ptr : B256 := swapMovedPointer 128 dt0.returnData

/-- The words under the second query's request words. -/
def skimRead1Stack : List B256 :=
  skimReserve1Word (dt0.getStorVal sevm.currentTarget 8) :: 0x1a26 ::
    skimToWord sevm :: skimToken1 sevm b :: 0x1aca :: skimToken1 sevm b ::
    skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77]

/-- What skim needs left after its second query: the second transfer's staging and call gas
(`qenv1`'s `tailGas + 64`). -/
def skimRead1Need (qd1 : Devm) : Nat :=
  callGasT1 + safeTransferPreCharge (((skimRequestMemory (skimRead1Base sevm b qd0 dt0)
      (skimRead1Ptr dt0) sevm.currentTarget).extends
      [((skimRead1Ptr dt0).toNat, 36), ((skimRead1Ptr dt0).toNat, 32)]).write
      (skimRead1Ptr dt0).toNat (qd1.returnData.take 32)).size (skimRead1Ptr dt0) + 12 + 80 + 64

end Read1

/-- **Skim's second `balanceOf(pair)` query when WETH9 is `token1`**, over the first query's and
X's transfer's results: its result and the call gas WETH9's code determines, given the second
transfer's call gas `callGasT1`. -/
noncomputable def skimWethRead1 (sevm : Sevm) (b qd0 dt0 : Devm) (callGasT1 : Nat) : Devm × Nat :=
  wethReadLeg sevm (afterSload sevm dt0 8) (skimRead1Stack sevm b dt0)
    ((skimRead1Base sevm b qd0 dt0).read 64 32).2 (skimRead1Ptr dt0) (skimT1 sevm b)
    (skimRead1Need sevm b qd0 dt0 callGasT1)

theorem skimRead1Need_gasFree (sevm : Sevm) (b qd0 dt0 : Devm) (callGasT1 : Nat) (d : Devm)
    (x : Nat) :
    skimRead1Need sevm b qd0 dt0 callGasT1 (d.withGasLeft x) =
      skimRead1Need sevm b qd0 dt0 callGasT1 d := rfl

/-- **Skim's second WETH9 read (WETH9 = token1), frame level.**  With the first transfer's memory
facts (`skimTransferLayout` derives them from X's transfer record), WETH9's code at the masked
`token1` after the reserve1 load, not a precompile, call depth left, the call gas a word, and room
for WETH9's view: `skimWethRead1` meets `SkimForwardEnv.code1` and `qenv1`, and replies with the
pair's WETH9 balance there.  Code-only. -/
theorem skimWethRead1_spec {sevm : Sevm} {b qd0 dt0 : Devm} {callGasT1 n : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (depth : sevm.depth ≠ 0)
    (mem : PtrMem (skimRead1Ptr dt0) n (skimRead1Base sevm b qd0 dt0))
    (lower : 128 ≤ (skimRead1Ptr dt0).toNat) (width : (skimRead1Ptr dt0).toNat + 1024 < 2 ^ 256)
    (wethCode : (afterSload sevm dt0 8).state.getCode (skimT1 sevm b).toAdr = Weth9.code)
    (notPrecompile : sevm.benvStat.rules.isPrecomp (skimT1 sevm b).toAdr = false)
    (fits : (skimWethRead1 sevm b qd0 dt0 callGasT1).2 < 2 ^ 256)
    (room : balUsed sevm (afterSload sevm dt0 8) (skimRead1Stack sevm b dt0)
        ((skimRead1Base sevm b qd0 dt0).read 64 32).2 (skimRead1Ptr dt0) (skimT1 sevm b) ≤
      except64th (skimRead1Need sevm b qd0 dt0 callGasT1 (wethBalanceSkel sevm (afterSload sevm dt0 8)
          (skimRead1Stack sevm b dt0) ((skimRead1Base sevm b qd0 dt0).read 64 32).2
          (skimRead1Ptr dt0) (skimT1 sevm b)) +
        balUsed sevm (afterSload sevm dt0 8) (skimRead1Stack sevm b dt0)
          ((skimRead1Base sevm b qd0 dt0).read 64 32).2 (skimRead1Ptr dt0) (skimT1 sevm b))) :
    ((afterSload sevm dt0 8).getCode (skimT1 sevm b).toAdr).size.toB256 ≠ 0 ∧
    SkimQueryEnv sevm (temporalAccountAccessBase (afterSload sevm dt0 8) (skimT1 sevm b).toAdr)
      (skimRequestMemory (skimRead1Base sevm b qd0 dt0) (skimRead1Ptr dt0) sevm.currentTarget)
      (skimRead1Ptr dt0) (skimT1 sevm b)
      (((skimRead1Ptr dt0) + 36) :: 0x70a08231 :: skimT1 sevm b :: skimRead1Stack sevm b dt0)
      (skimWethRead1 sevm b qd0 dt0 callGasT1).1 (skimWethRead1 sevm b qd0 dt0 callGasT1).2
      (callGasT1 + safeTransferPreCharge (((skimRequestMemory (skimRead1Base sevm b qd0 dt0)
          (skimRead1Ptr dt0) sevm.currentTarget).extends
          [((skimRead1Ptr dt0).toNat, 36), ((skimRead1Ptr dt0).toNat, 32)]).write
          (skimRead1Ptr dt0).toNat ((skimWethRead1 sevm b qd0 dt0 callGasT1).1.returnData.take 32)).size
        (skimRead1Ptr dt0) + 12 + 80) ∧
    (skimWethRead1 sevm b qd0 dt0 callGasT1).1.returnData =
      ((afterSload sevm dt0 8).getStorVal (skimT1 sevm b).toAdr
        (Weth9.balSlot sevm.currentTarget)).toBytes := by
  have htok : balTok (skimT1 sevm b) = (skimT1 sevm b).toAdr := by
    unfold balTok; rw [swapTokenWord_skimT1]
  obtain ⟨hrun, hstk, hret, hgas⟩ := wethReadLeg_spec (sevm := sevm) (B := afterSload sevm dt0 8)
    (S := skimRead1Stack sevm b dt0) (M := ((skimRead1Base sevm b qd0 dt0).read 64 32).2)
    (p := skimRead1Ptr dt0) (t := skimT1 sevm b) (need := skimRead1Need sevm b qd0 dt0 callGasT1)
    (skimRead1Need_gasFree sevm b qd0 dt0 callGasT1) fork (by rw [htok]; exact wethCode) depth
    (by rw [htok]; exact notPrecompile)
    (by simp only [skimRead1Stack, List.length_cons, List.length_nil]; omega)
    (mem.wf.extend 64 32) (by omega) fits room
  have hstate : balCallState sevm (afterSload sevm dt0 8) (skimRead1Stack sevm b dt0)
      ((skimRead1Base sevm b qd0 dt0).read 64 32).2 (skimRead1Ptr dt0) (skimT1 sevm b)
      (skimWethRead1 sevm b qd0 dt0 callGasT1).2 =
      St (temporalAccountAccessBase (afterSload sevm dt0 8) (skimT1 sevm b).toAdr)
        ((skimWethRead1 sevm b qd0 dt0 callGasT1).2.toB256 :: skimT1 sevm b :: skimRead1Ptr dt0 ::
          36 :: skimRead1Ptr dt0 :: 32 :: ((skimRead1Ptr dt0) + 36) :: 0x70a08231 ::
          skimT1 sevm b :: skimRead1Stack sevm b dt0)
        (skimRequestMemory (skimRead1Base sevm b qd0 dt0) (skimRead1Ptr dt0) sevm.currentTarget)
        (skimWethRead1 sevm b qd0 dt0 callGasT1).2 := by
    unfold balCallState balRest
    rw [htok, swapTokenWord_skimT1, skimRequestMemory_eq sevm.currentTarget mem (by omega) width]
  have hrun' : Ninst.RunCompiled sevm (balCallState sevm (afterSload sevm dt0 8)
      (skimRead1Stack sevm b dt0) ((skimRead1Base sevm b qd0 dt0).read 64 32).2 (skimRead1Ptr dt0)
      (skimT1 sevm b) (skimWethRead1 sevm b qd0 dt0 callGasT1).2) (.exec .staticcall)
      (skimWethRead1 sevm b qd0 dt0 callGasT1).1 := hrun
  rw [hstate] at hrun'
  rw [htok] at hret
  have hret' : (skimWethRead1 sevm b qd0 dt0 callGasT1).1.returnData =
      ((afterSload sevm dt0 8).getStorVal (skimT1 sevm b).toAdr
        (Weth9.balSlot sevm.currentTarget)).toBytes := hret
  have hstk' : (skimWethRead1 sevm b qd0 dt0 callGasT1).1.stack =
      1 :: balRest (skimRead1Stack sevm b dt0) (skimRead1Ptr dt0) (skimT1 sevm b) := hstk
  have hcode : ((afterSload sevm dt0 8).getCode (skimT1 sevm b).toAdr).size.toB256 ≠ 0 :=
    weth9_code_nonzero wethCode
  refine ⟨hcode, ⟨by rw [temporalAccountAccessBase_getCode]; exact hcode, hrun', ?_,
    by rw [hret']; exact toBytes_long _, hgas⟩, hret'⟩
  rw [hstk']
  unfold balRest
  rw [swapTokenWord_skimT1]

end Blanc.Composition.UniswapV2PairWeth9Joint
