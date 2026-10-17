import Blanc.Composition.UniswapV2PairWeth9LegsBurn1
import Blanc.Composition.UniswapV2PairWeth9LegsSkimRead1

/-!
# Skim's WETH9 `transfer` leg with WETH9 = token1 (C4(b), U8e)

With WETH9 as `token1`, Skim pays the other token `X = token0` first (`SkimForwardEnv.tenv0`, an
arbitrary callee record from the first query's result `qd0` to `dt0`), then queries WETH9
(`qenv1`, the read leg `skimWethRead1`, result `qd1`) and pays WETH9 at `qd1` (`tenv1`).
`skimWethLeg1` is that last `CALL` as WETH9's deployed code determines it; `skimWethLeg1_spec` is its
frame-level spec with WETH9's premises read at `qd1`.

`skimWethLeg1_of_read` composes it over the read leg's own result and discharges every WETH9 premise
from the world `qd0` the X transfer is staged over: X's transfer is crossed by the X-leg quiescence
(`xleg_transfer`: WETH9's code persists and the Pair's WETH9 balance word does not drop), the read
writes nothing and replies with that balance, and the amount (answer − reserve1) is covered when the
reserve1 word Skim loads after X's transfer is at most the Pair's WETH9 balance at `qd0` (C3's bound,
given that X's child leaves the locked Pair's reserve slot alone).  The staged memory is laid out from
X's record (`skimTransferLayout`).  None of the premises mentions WETH9's answers.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair
open Blanc.Composition.UniswapV2PairWeth9XLeg (CallChildFresh wethRunKeys pairRunKeys)

theorem skimToken1_mask (sevm : Sevm) (b : Devm) :
    (tokenMask (skimToken1 sevm b)).toAdr = (skimToken1 sevm b).toAdr := by
  unfold skimToken1
  rw [tokenMask_toAdr, toAdr_toB256]

theorem skimT1_toAdr (sevm : Sevm) (b : Devm) : (skimT1 sevm b).toAdr = (skimToken1 sevm b).toAdr := by
  rw [skimT1_eq, toAdr_toB256]

/-! ## The transfer leg -/

/-- The memory the WETH9 `transfer` is staged over: the second request with the second reply
written in. -/
def skimLeg1Mem (sevm : Sevm) (b qd0 dt0 qd1 : Devm) : Mem :=
  ((skimRequestMemory (skimRead1Base sevm b qd0 dt0) (skimRead1Ptr dt0) sevm.currentTarget).extends
    [((skimRead1Ptr dt0).toNat, 36), ((skimRead1Ptr dt0).toNat, 32)]).write
    (skimRead1Ptr dt0).toNat (qd1.returnData.take 32)

/-- The second transfer's amount: the second answer less the reserve1 word loaded after X's
transfer. -/
def skimLeg1Amount (sevm : Sevm) (dt0 qd1 : Devm) : B256 :=
  Bytes.toB256 (qd1.returnData.take 32) - skimReserve1Word (dt0.getStorVal sevm.currentTarget 8)

/-- The residual the record ties the second transfer to (`tenv1`'s `G`), read off its result `d`. -/
def skimLeg1Next (sevm : Sevm) (g : Nat) (d : Devm) : Nat := g + sstoreCost sevm d 12 1 + 22

/-- The gas-free skeleton of the WETH9 `transfer` CALL's result. -/
def skimLeg1Skel (sevm : Sevm) (b qd0 dt0 qd1 : Devm) : Devm :=
  wethTransferSkel sevm qd1 (skimLegStack sevm b) (skimLeg1Mem sevm b qd0 dt0 qd1) (skimRead1Ptr dt0)
    (skimLeg1Amount sevm dt0 qd1) (skimToWord sevm) (skimToken1 sevm b) 0x1aca

/-- What skim needs left after the WETH9 `transfer` CALL, read on the skeleton. -/
def skimLeg1Need (sevm : Sevm) (b qd0 dt0 qd1 : Devm) (g : Nat) : Nat :=
  skimLeg1Next sevm g (skimLeg1Skel sevm b qd0 dt0 qd1) +
    safeTransferPostCharge (skimLeg1Mem sevm b qd0 dt0 qd1).size (skimRead1Ptr dt0)
      (skimLeg1Skel sevm b qd0 dt0 qd1).returnData

/-- WETH9's charge for the leg's child frame. -/
def skimLeg1Used (sevm : Sevm) (b qd0 dt0 qd1 : Devm) : Nat :=
  xferUsed sevm qd1 (skimLegStack sevm b) (skimLeg1Mem sevm b qd0 dt0 qd1) (skimRead1Ptr dt0)
    (skimLeg1Amount sevm dt0 qd1) (skimToWord sevm) (skimToken1 sevm b) 0x1aca

/-- The `CALL`'s own charges. -/
def skimLeg1Charge (sevm : Sevm) (b qd0 dt0 qd1 : Devm) : Nat :=
  xferAcc qd1 (skimToken1 sevm b) +
    xferExt qd1 (skimLegStack sevm b) (skimLeg1Mem sevm b qd0 dt0 qd1) (skimRead1Ptr dt0)
      (skimLeg1Amount sevm dt0 qd1) (skimToWord sevm) (skimToken1 sevm b) 0x1aca +
    skimLeg1Used sevm b qd0 dt0 qd1

/-- **Skim's WETH9 `transfer` leg (token1 = WETH9)**, over the second query's result `qd1`: the
`CALL` result and the `CALL` state's gas that WETH9's deployed code determines, given the residual
`g` after the unlock. -/
noncomputable def skimWethLeg1 (sevm : Sevm) (b qd0 dt0 qd1 : Devm) (g : Nat) : Devm × Nat :=
  (wethTransferCall sevm qd1 (skimLegStack sevm b) (skimLeg1Mem sevm b qd0 dt0 qd1)
      (skimRead1Ptr dt0) (skimLeg1Amount sevm dt0 qd1) (skimToWord sevm) (skimToken1 sevm b) 0x1aca
      (skimLeg1Need sevm b qd0 dt0 qd1 g + skimLeg1Charge sevm b qd0 dt0 qd1),
    skimLeg1Need sevm b qd0 dt0 qd1 g + skimLeg1Charge sevm b qd0 dt0 qd1)

theorem skimLeg1Next_withGasLeft (sevm : Sevm) (g : Nat) (d : Devm) (x : Nat) :
    skimLeg1Next sevm g (d.withGasLeft x) = skimLeg1Next sevm g d := rfl

/-- **Skim's WETH9 `transfer` leg's spec, token1 = WETH9 (frame level).**  Over the second query's
result `qd1`: WETH9's code at `token1` there, not a precompile, the frame mutable, call depth left,
the staged memory well formed with the pointer's bounds, the pair's WETH9 balance at `qd1` covering
the amount, the leg's call gas a word, and room for WETH9's `transfer` under the 63/64 rule with its
`SSTORE` sentry.  Then `skimWethLeg1` is the transfer record `SkimForwardEnv.tenv1` asks for. -/
theorem skimWethLeg1_spec {sevm : Sevm} {b qd0 dt0 qd1 : Devm} {g : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (nonstatic : sevm.isStatic = false)
    (depth : sevm.depth ≠ 0)
    (wethCode : qd1.state.getCode (skimToken1 sevm b).toAdr = Weth9.code)
    (notPrecompile : sevm.benvStat.rules.isPrecomp (skimToken1 sevm b).toAdr = false)
    (wf : Mem.Wf (skimLeg1Mem sevm b qd0 dt0 qd1)) (lower : 128 ≤ (skimRead1Ptr dt0).toNat)
    (width : (skimRead1Ptr dt0).toNat + 164 < 2 ^ 256)
    (balance : skimLeg1Amount sevm dt0 qd1 ≤
      qd1.getStorVal (skimToken1 sevm b).toAdr (Weth9.balSlot sevm.currentTarget))
    (fits : (skimWethLeg1 sevm b qd0 dt0 qd1 g).2 < 2 ^ 256)
    (room : skimLeg1Used sevm b qd0 dt0 qd1 + gCallStipend ≤
      except64th (skimLeg1Need sevm b qd0 dt0 qd1 g + skimLeg1Used sevm b qd0 dt0 qd1)) :
    SwapTransferCallForward sevm qd1 (skimLegStack sevm b) (skimLeg1Mem sevm b qd0 dt0 qd1)
      (skimLeg1Mem sevm b qd0 dt0 qd1).size (skimRead1Ptr dt0) (skimLeg1Amount sevm dt0 qd1)
      (skimToWord sevm) (skimToken1 sevm b) 0x1aca (skimWethLeg1 sevm b qd0 dt0 qd1 g).2
      (skimLeg1Next sevm g (skimWethLeg1 sevm b qd0 dt0 qd1 g).1)
      (skimWethLeg1 sevm b qd0 dt0 qd1 g).1 := by
  have spec := wethTransferCall_spec (sevm := sevm) (W := qd1) (L := skimLegStack sevm b)
    (M := skimLeg1Mem sevm b qd0 dt0 qd1) (p := skimRead1Ptr dt0)
    (amount := skimLeg1Amount sevm dt0 qd1) (toWord := skimToWord sevm) (token := skimToken1 sevm b)
    (rho := 0x1aca) (cg := skimLeg1Need sevm b qd0 dt0 qd1 g + skimLeg1Charge sevm b qd0 dt0 qd1) fork
    (by rw [skimToken1_mask]; exact wethCode) nonstatic depth
    (by rw [skimToken1_mask]; exact notPrecompile)
    (by simp only [skimLegStack, List.length_cons, List.length_nil]; omega)
    wf lower width (by rw [skimToken1_mask]; exact balance) fits
    (by unfold skimLeg1Charge; omega)
    (by
      have e : skimLeg1Need sevm b qd0 dt0 qd1 g + skimLeg1Charge sevm b qd0 dt0 qd1 -
          xferExt qd1 (skimLegStack sevm b) (skimLeg1Mem sevm b qd0 dt0 qd1) (skimRead1Ptr dt0)
            (skimLeg1Amount sevm dt0 qd1) (skimToWord sevm) (skimToken1 sevm b) 0x1aca -
          xferAcc qd1 (skimToken1 sevm b) =
          skimLeg1Need sevm b qd0 dt0 qd1 g + skimLeg1Used sevm b qd0 dt0 qd1 := by
        unfold skimLeg1Charge; omega
      rw [e]
      exact room)
  obtain ⟨hrun, hstk, hret, hgas⟩ := spec
  have hskel : wethTransferCall sevm qd1 (skimLegStack sevm b) (skimLeg1Mem sevm b qd0 dt0 qd1)
      (skimRead1Ptr dt0) (skimLeg1Amount sevm dt0 qd1) (skimToWord sevm) (skimToken1 sevm b) 0x1aca
      (skimLeg1Need sevm b qd0 dt0 qd1 g + skimLeg1Charge sevm b qd0 dt0 qd1) =
      (skimLeg1Skel sevm b qd0 dt0 qd1).withGasLeft _ :=
    wethTransferCallAt_eq _ _ _ _ _ _ _ _ _ _ _ _ _
  have hret' : (skimWethLeg1 sevm b qd0 dt0 qd1 g).1.returnData = B256.toBytes 1 := hret
  refine ⟨hrun, hstk, Or.inr (by rw [hret']; exact one_reply_accepted), ?_⟩
  change (wethTransferCall sevm qd1 (skimLegStack sevm b) (skimLeg1Mem sevm b qd0 dt0 qd1)
      (skimRead1Ptr dt0) (skimLeg1Amount sevm dt0 qd1) (skimToWord sevm) (skimToken1 sevm b) 0x1aca
      (skimLeg1Need sevm b qd0 dt0 qd1 g + skimLeg1Charge sevm b qd0 dt0 qd1)).gasLeft =
    skimLeg1Next sevm g (wethTransferCall sevm qd1 (skimLegStack sevm b)
      (skimLeg1Mem sevm b qd0 dt0 qd1) (skimRead1Ptr dt0) (skimLeg1Amount sevm dt0 qd1)
      (skimToWord sevm) (skimToken1 sevm b) 0x1aca
      (skimLeg1Need sevm b qd0 dt0 qd1 g + skimLeg1Charge sevm b qd0 dt0 qd1)) +
    safeTransferPostCharge (skimLeg1Mem sevm b qd0 dt0 qd1).size (skimRead1Ptr dt0)
      (wethTransferCall sevm qd1 (skimLegStack sevm b) (skimLeg1Mem sevm b qd0 dt0 qd1)
        (skimRead1Ptr dt0) (skimLeg1Amount sevm dt0 qd1) (skimToWord sevm) (skimToken1 sevm b)
        0x1aca (skimLeg1Need sevm b qd0 dt0 qd1 g + skimLeg1Charge sevm b qd0 dt0 qd1)).returnData
  rw [hgas]
  conv => rhs; rw [hskel, skimLeg1Next_withGasLeft, withGasLeft_returnData]
  have hn : skimLeg1Need sevm b qd0 dt0 qd1 g =
      skimLeg1Next sevm g (skimLeg1Skel sevm b qd0 dt0 qd1) +
        safeTransferPostCharge (skimLeg1Mem sevm b qd0 dt0 qd1).size (skimRead1Ptr dt0)
          (skimLeg1Skel sevm b qd0 dt0 qd1).returnData := rfl
  rw [← hn]
  unfold skimLeg1Charge skimLeg1Used
  omega

/-! ## After X's transfer and the second query -/

/-- **Skim's WETH9 legs after the other token's transfer (WETH9 = token1).**  Given X's transfer
record (`SkimForwardEnv.tenv0`'s shape) from the first query's result `qd0` to `dt0`, and at `qd0`:
WETH9's code and footprint over `U` with the Pair tracked, the Pair's WETH9 allowances zero, the Pair
runtime with a locked model state, the factory runtime at that state's factory, `pair ≠ 0`, the ether
supply a word; the two tokens distinct and the Pair not WETH9; HASH-T over the keys X's child
touches; and the reserve1 word Skim loads after X's transfer at most the Pair's WETH9 balance at
`qd0`.  Then, with `qd1` the read leg `skimWethRead1`'s own result, the read meets `qenv1` and
`skimWethLeg1` is the `tenv1` record. -/
theorem skimWethLeg1_of_read {sevm : Sevm} {b qd0 dt0 : Devm} {callGasT0 G0 callGasT1 g : Nat}
    {weth : Adr} {U : Weth9.Key → Prop} {K : WriterKey → Prop} {stL : UniswapV2Pair.State}
    (fork : CoveredFork sevm.benvStat.fork) (nonstatic : sevm.isStatic = false)
    (depth : sevm.depth ≠ 0)
    (tenv0 : SwapTransferCallForward sevm qd0 (skimLegStack sevm b) (skimLegMem sevm qd0)
      (skimLegMem sevm qd0).size 128 (skimLegAmount sevm b qd0) (skimToWord sevm)
      (skimToken0 sevm b) 0x1a2b callGasT0 G0 dt0)
    (token1 : (skimToken1 sevm b).toAdr = weth)
    (distinct : (skimToken0 sevm b).toAdr ≠ weth) (apart : sevm.currentTarget ≠ weth)
    (wethCode : qd0.state.getCode weth = Weth9.code)
    (foot : Weth9.FootInv U (qd0.state.getStor weth) (qd0.state.bal weth))
    (tracked : U (.bal sevm.currentTarget))
    (zero : ∀ g, Weth9Token.weth9Book.allow (Weth9.ledger U (qd0.state.getStor weth))
      sevm.currentTarget g = 0)
    (pairCode : qd0.state.getCode sevm.currentTarget = UniswapV2Pair.code)
    (rep : WriterRep K (qd0.state.getStor sevm.currentTarget) stL) (locked : stL.unlocked ≠ 1)
    (factoryCode : qd0.state.getCode stL.factory = UniswapV2Factory.code)
    (pairNonzero : sevm.currentTarget ≠ 0) (bound : sum qd0.state.bal < 2 ^ 256)
    (cover : skimReserve1Word (dt0.getStorVal sevm.currentTarget 8) ≤
      qd0.getStorVal weth (Weth9.balSlot sevm.currentTarget))
    (wethFresh : CallChildFresh sevm
      (xferCallState qd0 (skimLegStack sevm b) (skimLegMem sevm qd0) 128 (skimLegAmount sevm b qd0)
        (skimToWord sevm) (skimToken0 sevm b) 0x1a2b callGasT0)
      fun D => Weth9.KeysFresh U (wethRunKeys weth D))
    (pairFresh : CallChildFresh sevm
      (xferCallState qd0 (skimLegStack sevm b) (skimLegMem sevm qd0) 128 (skimLegAmount sevm b qd0)
        (skimToWord sevm) (skimToken0 sevm b) 0x1a2b callGasT0)
      fun D => WriterFreshKeys K (pairRunKeys sevm.currentTarget D))
    (notPrecompile : sevm.benvStat.rules.isPrecomp weth = false)
    (fitsRead : (skimWethRead1 sevm b qd0 dt0 callGasT1).2 < 2 ^ 256)
    (roomRead : balUsed sevm (afterSload sevm dt0 8) (skimRead1Stack sevm b dt0)
        ((skimRead1Base sevm b qd0 dt0).read 64 32).2 (skimRead1Ptr dt0) (skimT1 sevm b) ≤
      except64th (skimRead1Need sevm b qd0 dt0 callGasT1 (wethBalanceSkel sevm (afterSload sevm dt0 8)
          (skimRead1Stack sevm b dt0) ((skimRead1Base sevm b qd0 dt0).read 64 32).2
          (skimRead1Ptr dt0) (skimT1 sevm b)) +
        balUsed sevm (afterSload sevm dt0 8) (skimRead1Stack sevm b dt0)
          ((skimRead1Base sevm b qd0 dt0).read 64 32).2 (skimRead1Ptr dt0) (skimT1 sevm b)))
    (fits : (skimWethLeg1 sevm b qd0 dt0 (skimWethRead1 sevm b qd0 dt0 callGasT1).1 g).2 < 2 ^ 256)
    (room : skimLeg1Used sevm b qd0 dt0 (skimWethRead1 sevm b qd0 dt0 callGasT1).1 + gCallStipend ≤
      except64th (skimLeg1Need sevm b qd0 dt0 (skimWethRead1 sevm b qd0 dt0 callGasT1).1 g +
        skimLeg1Used sevm b qd0 dt0 (skimWethRead1 sevm b qd0 dt0 callGasT1).1)) :
    (((afterSload sevm dt0 8).getCode (skimT1 sevm b).toAdr).size.toB256 ≠ 0 ∧
      SkimQueryEnv sevm (temporalAccountAccessBase (afterSload sevm dt0 8) (skimT1 sevm b).toAdr)
        (skimRequestMemory (skimRead1Base sevm b qd0 dt0) (skimRead1Ptr dt0) sevm.currentTarget)
        (skimRead1Ptr dt0) (skimT1 sevm b)
        (((skimRead1Ptr dt0) + 36) :: 0x70a08231 :: skimT1 sevm b :: skimRead1Stack sevm b dt0)
        (skimWethRead1 sevm b qd0 dt0 callGasT1).1 (skimWethRead1 sevm b qd0 dt0 callGasT1).2
        (callGasT1 + safeTransferPreCharge (((skimRequestMemory (skimRead1Base sevm b qd0 dt0)
            (skimRead1Ptr dt0) sevm.currentTarget).extends
            [((skimRead1Ptr dt0).toNat, 36), ((skimRead1Ptr dt0).toNat, 32)]).write
            (skimRead1Ptr dt0).toNat
            ((skimWethRead1 sevm b qd0 dt0 callGasT1).1.returnData.take 32)).size
          (skimRead1Ptr dt0) + 12 + 80)) ∧
    SwapTransferCallForward sevm (skimWethRead1 sevm b qd0 dt0 callGasT1).1 (skimLegStack sevm b)
      (skimLeg1Mem sevm b qd0 dt0 (skimWethRead1 sevm b qd0 dt0 callGasT1).1)
      (skimLeg1Mem sevm b qd0 dt0 (skimWethRead1 sevm b qd0 dt0 callGasT1).1).size
      (skimRead1Ptr dt0) (skimLeg1Amount sevm dt0 (skimWethRead1 sevm b qd0 dt0 callGasT1).1)
      (skimToWord sevm) (skimToken1 sevm b) 0x1aca
      (skimWethLeg1 sevm b qd0 dt0 (skimWethRead1 sevm b qd0 dt0 callGasT1).1 g).2
      (skimLeg1Next sevm g (skimWethLeg1 sevm b qd0 dt0 (skimWethRead1 sevm b qd0 dt0 callGasT1).1 g).1)
      (skimWethLeg1 sevm b qd0 dt0 (skimWethRead1 sevm b qd0 dt0 callGasT1).1 g).1 := by
  have sloadState : (afterSload sevm dt0 8).state = dt0.state := by
    unfold afterSload
    split <;> rfl
  -- X's transfer
  have callee : (tokenMask (skimToken0 sevm b)).toAdr ≠ weth := by
    rw [skimToken0_mask]; exact distinct
  obtain ⟨codeDt0, balLe⟩ := xleg_transfer fork tenv0 callee apart wethCode foot tracked zero
    pairCode rep locked factoryCode pairNonzero bound wethFresh pairFresh
  -- the memory after X's transfer
  have req0 := balanceRequestMemory_ptr getterInitMemory_ptr sevm.currentTarget
  have hs1 : memExtSize 96 128 32 = 160 := by decide
  have hs2 : memExtSize 160 132 32 = 192 := by decide
  rw [hs1, hs2] at req0
  have reply0 := balanceReplyMemory_ptr qd0.returnData req0
  have memN0 : PtrMem 128 (skimLegMem sevm qd0).size (skimLegMem sevm qd0) := by
    unfold skimLegMem
    rw [reply0.size]
    exact reply0
  obtain ⟨⟨n', memT⟩, -, lowerT, widthT, -⟩ :=
    skimTransferLayout (k := 161) fork
      (by simp only [skimLegStack, List.length_cons, List.length_nil]; omega)
      memN0 skimReply0_sentinel (by decide) (by decide) (by decide) tenv0
  change 128 ≤ (skimRead1Ptr dt0).toNat at lowerT
  change (skimRead1Ptr dt0).toNat + 1024 < 2 ^ 256 at widthT
  -- the read
  have token1' : (skimT1 sevm b).toAdr = weth := by rw [skimT1_toAdr, token1]
  have sloadCode : (afterSload sevm dt0 8).state.getCode (skimT1 sevm b).toAdr = Weth9.code := by
    rw [sloadState, token1']
    exact codeDt0
  obtain ⟨code1, qenv1, reply⟩ := skimWethRead1_spec (callGasT1 := callGasT1) fork depth memT
    lowerT widthT sloadCode (by rw [token1']; exact notPrecompile) fitsRead roomRead
  refine ⟨⟨code1, qenv1⟩, ?_⟩
  -- the transfer
  have qd1State : (skimWethRead1 sevm b qd0 dt0 callGasT1).1.state = dt0.state := by
    unfold skimWethRead1
    rw [wethReadLeg_state, sloadState]
  have storage : (skimWethRead1 sevm b qd0 dt0 callGasT1).1.getStorVal weth
      (Weth9.balSlot sevm.currentTarget) =
      (afterSload sevm dt0 8).getStorVal weth (Weth9.balSlot sevm.currentTarget) := by
    unfold skimWethRead1
    rw [wethReadLeg_getStorVal]
  have sloadStor : (afterSload sevm dt0 8).getStorVal weth (Weth9.balSlot sevm.currentTarget) =
      dt0.getStorVal weth (Weth9.balSlot sevm.currentTarget) := by
    unfold Devm.getStorVal Devm.getAcct
    rw [sloadState]
  rw [token1'] at reply
  have balance := skim_amount_le_balance
    (reserve := skimReserve1Word (dt0.getStorVal sevm.currentTarget 8)) reply storage
    (by
      rw [sloadStor]
      exact B256.le_iff_toNat_le_toNat.mpr (Nat.le_trans (B256.le_iff_toNat_le_toNat.mp cover)
        (B256.le_iff_toNat_le_toNat.mp balLe)))
  rw [← token1] at balance notPrecompile codeDt0
  have wfMem : Mem.Wf (skimLeg1Mem sevm b qd0 dt0 (skimWethRead1 sevm b qd0 dt0 callGasT1).1) := by
    have memT' : PtrMem (skimRead1Ptr dt0) n' (skimRead1Base sevm b qd0 dt0) := memT
    unfold skimLeg1Mem
    rw [skimRequestMemory_eq sevm.currentTarget memT' (by omega) widthT]
    exact (((memT'.wf.extend 64 32).write _ _).write _ _).extends _ |>.write _ _
  exact skimWethLeg1_spec fork nonstatic depth (by rw [qd1State]; exact codeDt0) notPrecompile
    wfMem lowerT (by omega) balance fits room

end Blanc.Composition.UniswapV2PairWeth9Joint
