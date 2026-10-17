import Blanc.Composition.UniswapV2PairWeth9LegsBurnRead
import Blanc.Lift.UniswapV2Pair.SkimForwardAccept
import Blanc.Lift.AccountAccessState

/-!
# The skim row's WETH9 legs with WETH9 = token0 (C4(b), U8b2)

`pair_history_skim_live` takes Skim's callees as `SkimForwardEnv`.  With WETH9 as `token0`:

* the first `balanceOf(pair)` query (`qenv0`, `SkimQueryEnv` shaped) is the generic read leg at
  the fixed pointer `128` (`skimWethRead0`), code-only;
* the first transfer (`tenv0`, `SwapTransferCallForward` shaped, amount = answer − reserve0) is the
  WETH9 `transfer` `CALL` over the query's result (`skimWethLeg0`).  WETH9 pays first, so no other
  token's leg precedes it.

The transfer's one non-frame premise, `answer − reserve0 ≤` the pair's WETH9 balance at the query's
result, reduces for the read leg's own result to `reserve0 ≤` the pair's WETH9 balance at the
query's world (`skimWethLeg0_of_read`): the query leaves storage unchanged and replies with that
balance.  The history row feeds it from C3 (the ghost at the `skimBalance0` suspension).
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair

/-! ## The read leg leaves storage unchanged -/

theorem callChildPost_state (P c : Devm) (oi os : Nat) :
    (callChildPost P c oi os).state = c.state := rfl

theorem weth9BalancePost_state (s : Sevm) (pre : Devm) (G : Nat) :
    (weth9BalancePost s pre G).state = pre.state := by
  simp only [weth9BalancePost, wordTailPost, Devm.withOutput_state, Devm.memRead_state, St,
    Devm.setMach_state]
  unfold afterSload
  split <;> rfl

theorem staticcallSpawnMsg_state (sevm : Sevm) (P : Devm) (f : Nat) (c d : Adr) (ii is : Nat)
    (code : ByteArray) (dp : Bool) :
    (initDevm (staticcallSpawnMsg sevm P f c d ii is code dp)).state = P.state := rfl

/-- The read leg's result carries its world's state: a `balanceOf` view writes nothing. -/
theorem wethReadLeg_state (sevm : Sevm) (B : Devm) (S : List B256) (M : Mem) (p t : B256)
    (need : Devm → Nat) : (wethReadLeg sevm B S M p t need).1.state = B.state := by
  unfold wethReadLeg wethBalanceCall wethBalanceCallAt balMsg
  rw [callChildPost_state, weth9BalancePost_state, staticcallSpawnMsg_state]
  unfold balParent balWarm balPopped
  rw [callSpawnParent_state, addAccessedAddress_setMach_state, temporalAccountAccessBase_state]

theorem wethReadLeg_getStorVal (sevm : Sevm) (B : Devm) (S : List B256) (M : Mem) (p t : B256)
    (need : Devm → Nat) (a : Adr) (k : B256) :
    (wethReadLeg sevm B S M p t need).1.getStorVal a k = B.getStorVal a k := by
  unfold Devm.getStorVal Devm.getAcct
  rw [wethReadLeg_state]

theorem skimToken0_mask (sevm : Sevm) (b : Devm) :
    (tokenMask (skimToken0 sevm b)).toAdr = (skimToken0 sevm b).toAdr := by
  unfold skimToken0
  rw [tokenMask_toAdr, toAdr_toB256]

/-! ## The first query (WETH9 = token0) -/

section Read0

variable (sevm : Sevm) (b : Devm) (callGasT0 : Nat)

/-- The words under the first query's request words. -/
def skimRead0Stack : List B256 :=
  skimReserve0 sevm b :: 0x1a26 :: skimToWord sevm :: skimToken0 sevm b :: 0x1a2b ::
    skimToken1 sevm b :: skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77]

/-- What skim needs left after its first query: the first transfer's staging and call gas
(`qenv0`'s `tailGas + 64`). -/
def skimRead0Need (d : Devm) : Nat :=
  callGasT0 + safeTransferPreCharge
    (balanceReplyMemory getterInitMemory sevm.currentTarget d.returnData).size 128 + 12 + 80 + 64

end Read0

/-- **Skim's first `balanceOf(pair)` query when WETH9 is `token0`**: its result and the call gas
WETH9's code determines, given the first transfer's call gas `callGasT0`. -/
noncomputable def skimWethRead0 (sevm : Sevm) (b : Devm) (callGasT0 : Nat) : Devm × Nat :=
  wethReadLeg sevm (skimCachedWorld sevm b) (skimRead0Stack sevm b) getterInitMemory 128
    (skimToken0 sevm b) (skimRead0Need sevm callGasT0)

theorem skimRead0Need_gasFree (sevm : Sevm) (callGasT0 : Nat) (d : Devm) (x : Nat) :
    skimRead0Need sevm callGasT0 (d.withGasLeft x) = skimRead0Need sevm callGasT0 d := rfl

/-- **Skim's first WETH9 read (WETH9 = token0), frame level.**  WETH9's code at the cached `token0`
in the world after the lock and the cache loads, not a precompile, call depth left, the call gas a
word, and room for WETH9's view: `skimWethRead0` meets `SkimForwardEnv.code0` and `qenv0`, and
replies with the pair's WETH9 balance there.  Code-only. -/
theorem skimWethRead0_spec {sevm : Sevm} {b : Devm} {callGasT0 : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (depth : sevm.depth ≠ 0)
    (wethCode : (skimCachedWorld sevm b).state.getCode (skimToken0 sevm b).toAdr = Weth9.code)
    (notPrecompile : sevm.benvStat.rules.isPrecomp (skimToken0 sevm b).toAdr = false)
    (fits : (skimWethRead0 sevm b callGasT0).2 < 2 ^ 256)
    (room : balUsed sevm (skimCachedWorld sevm b) (skimRead0Stack sevm b) getterInitMemory 128
        (skimToken0 sevm b) ≤
      except64th (skimRead0Need sevm callGasT0 (wethBalanceSkel sevm (skimCachedWorld sevm b)
          (skimRead0Stack sevm b) getterInitMemory 128 (skimToken0 sevm b)) +
        balUsed sevm (skimCachedWorld sevm b) (skimRead0Stack sevm b) getterInitMemory 128
          (skimToken0 sevm b))) :
    ((skimCachedWorld sevm b).getCode (skimToken0 sevm b).toAdr).size.toB256 ≠ 0 ∧
    SkimQueryEnv sevm (temporalAccountAccessBase (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr)
      (balanceRequestMemory getterInitMemory sevm.currentTarget) 128 (skimToken0 sevm b)
      (164 :: 0x70a08231 :: skimToken0 sevm b :: skimReserve0 sevm b :: 0x1a26 ::
        skimToWord sevm :: skimToken0 sevm b :: 0x1a2b :: skimToken1 sevm b ::
        skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77])
      (skimWethRead0 sevm b callGasT0).1 (skimWethRead0 sevm b callGasT0).2
      (callGasT0 + safeTransferPreCharge (balanceReplyMemory getterInitMemory sevm.currentTarget
        (skimWethRead0 sevm b callGasT0).1.returnData).size 128 + 12 + 80) ∧
    (skimWethRead0 sevm b callGasT0).1.returnData =
      ((skimCachedWorld sevm b).getStorVal (skimToken0 sevm b).toAdr
        (Weth9.balSlot sevm.currentTarget)).toBytes := by
  obtain ⟨hcode, hrun, hstk, hgas, hlong, hret⟩ := wethReadLeg128_spec (sevm := sevm)
    (B := skimCachedWorld sevm b) (S := skimRead0Stack sevm b) (M := getterInitMemory)
    (t := skimToken0 sevm b) (need := skimRead0Need sevm callGasT0) (swapTokenWord_adr _)
    (skimRead0Need_gasFree sevm callGasT0) fork wethCode depth notPrecompile
    (by simp only [skimRead0Stack, List.length_cons, List.length_nil]; omega)
    getterInitMemory_ptr.wf fits room
  refine ⟨hcode, ⟨?_, hrun, hstk, hlong, hgas⟩, hret⟩
  rw [temporalAccountAccessBase_getCode]
  exact hcode

/-! ## The first transfer (WETH9 = token0) -/

section Leg0

variable (sevm : Sevm) (b qd0 : Devm) (callGasQ1 : Nat)

/-- The words under skim's transfer operands. -/
def skimLegStack : List B256 :=
  skimToken1 sevm b :: skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77]

/-- The memory the first transfer is staged over (the first reply written in). -/
def skimLegMem : Mem := balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData

/-- The first transfer's amount: the first answer less the cached reserve0. -/
def skimLegAmount : B256 := Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b

/-- The residual the record ties the first transfer to (`tenv0`'s `G`): the reserve1 load, the
second request's staging and the second query's call gas, read off the transfer's result `dt0`. -/
def skimLeg0Next (dt0 : Devm) : Nat :=
  ((callGasQ1 + 5) +
    sloadCost sevm dt0 8 +
    swapStoreCost
      (swapTransferMemory (skimLegMem sevm qd0) 128 (skimLegAmount sevm b qd0) (skimToWord sevm)
        dt0.returnData).size
      (swapMovedPointer 128 dt0.returnData).toNat +
    swapStoreCost
      (memExtSize
        (swapTransferMemory (skimLegMem sevm qd0) 128 (skimLegAmount sevm b qd0) (skimToWord sevm)
          dt0.returnData).size
        (swapMovedPointer 128 dt0.returnData).toNat 32)
      ((swapMovedPointer 128 dt0.returnData) + 4).toNat +
    temporalAccountAccessCost (afterSload sevm dt0 8)
      ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
        skimToken1 sevm b)).toAdr + 171)

/-- The gas-free skeleton of the WETH9 `transfer` CALL's result. -/
def skimLeg0Skel : Devm :=
  wethTransferSkel sevm qd0 (skimLegStack sevm b) (skimLegMem sevm qd0) 128
    (skimLegAmount sevm b qd0) (skimToWord sevm) (skimToken0 sevm b) 0x1a2b

/-- What skim needs left after the WETH9 `transfer` CALL, read on the skeleton. -/
def skimLeg0Need : Nat :=
  skimLeg0Next sevm b qd0 callGasQ1 (skimLeg0Skel sevm b qd0) +
    safeTransferPostCharge (skimLegMem sevm qd0).size 128 (skimLeg0Skel sevm b qd0).returnData

/-- WETH9's charge for the leg's child frame. -/
def skimLeg0Used : Nat :=
  xferUsed sevm qd0 (skimLegStack sevm b) (skimLegMem sevm qd0) 128 (skimLegAmount sevm b qd0)
    (skimToWord sevm) (skimToken0 sevm b) 0x1a2b

/-- The `CALL`'s own charges. -/
def skimLeg0Charge : Nat :=
  xferAcc qd0 (skimToken0 sevm b) +
    xferExt qd0 (skimLegStack sevm b) (skimLegMem sevm qd0) 128 (skimLegAmount sevm b qd0)
      (skimToWord sevm) (skimToken0 sevm b) 0x1a2b +
    skimLeg0Used sevm b qd0

end Leg0

/-- **Skim's WETH9 `transfer` leg (token0 = WETH9)**, over the first query's result `qd0`: the
`CALL` result and the `CALL` state's gas that WETH9's deployed code determines, given the second
query's call gas `callGasQ1`. -/
noncomputable def skimWethLeg0 (sevm : Sevm) (b qd0 : Devm) (callGasQ1 : Nat) : Devm × Nat :=
  (wethTransferCall sevm qd0 (skimLegStack sevm b) (skimLegMem sevm qd0) 128
      (skimLegAmount sevm b qd0) (skimToWord sevm) (skimToken0 sevm b) 0x1a2b
      (skimLeg0Need sevm b qd0 callGasQ1 + skimLeg0Charge sevm b qd0),
    skimLeg0Need sevm b qd0 callGasQ1 + skimLeg0Charge sevm b qd0)

theorem skimLeg0Next_withGasLeft (sevm : Sevm) (b qd0 : Devm) (callGasQ1 : Nat) (d : Devm)
    (x : Nat) :
    skimLeg0Next sevm b qd0 callGasQ1 (d.withGasLeft x) = skimLeg0Next sevm b qd0 callGasQ1 d := by
  unfold skimLeg0Next Devm.withGasLeft
  rw [afterSload_setMach]
  rfl

/-- **Skim's WETH9 `transfer` leg's spec, token0 = WETH9 (frame level).**  Over the first query's
result `qd0`: WETH9's code at `token0` there, not a precompile, the frame mutable, call depth left,
the pair's WETH9 balance at `qd0` covering the amount (answer − reserve0), the leg's call gas a word,
and room for WETH9's `transfer` under the 63/64 rule with its `SSTORE` sentry.  Then `skimWethLeg0`
is the transfer record `SkimForwardEnv.tenv0` asks for. -/
theorem skimWethLeg0_spec {sevm : Sevm} {b qd0 : Devm} {callGasQ1 : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (nonstatic : sevm.isStatic = false)
    (depth : sevm.depth ≠ 0)
    (wethCode : qd0.state.getCode (skimToken0 sevm b).toAdr = Weth9.code)
    (notPrecompile : sevm.benvStat.rules.isPrecomp (skimToken0 sevm b).toAdr = false)
    (balance : Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b ≤
      qd0.getStorVal (skimToken0 sevm b).toAdr (Weth9.balSlot sevm.currentTarget))
    (fits : (skimWethLeg0 sevm b qd0 callGasQ1).2 < 2 ^ 256)
    (room : skimLeg0Used sevm b qd0 + gCallStipend ≤
      except64th (skimLeg0Need sevm b qd0 callGasQ1 + skimLeg0Used sevm b qd0)) :
    SwapTransferCallForward sevm qd0
      (skimToken1 sevm b :: skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77])
      (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
      ((balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData).size)
      128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
      (skimToWord sevm) (skimToken0 sevm b) 0x1a2b (skimWethLeg0 sevm b qd0 callGasQ1).2
      (skimLeg0Next sevm b qd0 callGasQ1 (skimWethLeg0 sevm b qd0 callGasQ1).1)
      (skimWethLeg0 sevm b qd0 callGasQ1).1 := by
  have spec := wethTransferCall_spec (sevm := sevm) (W := qd0) (L := skimLegStack sevm b)
    (M := skimLegMem sevm qd0) (p := 128) (amount := skimLegAmount sevm b qd0)
    (toWord := skimToWord sevm) (token := skimToken0 sevm b) (rho := 0x1a2b)
    (cg := skimLeg0Need sevm b qd0 callGasQ1 + skimLeg0Charge sevm b qd0) fork
    (by rw [skimToken0_mask]; exact wethCode) nonstatic depth
    (by rw [skimToken0_mask]; exact notPrecompile)
    (by simp only [skimLegStack, List.length_cons, List.length_nil]; omega)
    (burnMem1_wf sevm qd0) (by decide) (by decide)
    (by rw [skimToken0_mask]; exact balance) fits
    (by unfold skimLeg0Charge; omega)
    (by
      have e : skimLeg0Need sevm b qd0 callGasQ1 + skimLeg0Charge sevm b qd0 -
          xferExt qd0 (skimLegStack sevm b) (skimLegMem sevm qd0) 128 (skimLegAmount sevm b qd0)
            (skimToWord sevm) (skimToken0 sevm b) 0x1a2b -
          xferAcc qd0 (skimToken0 sevm b) =
          skimLeg0Need sevm b qd0 callGasQ1 + skimLeg0Used sevm b qd0 := by
        unfold skimLeg0Charge; omega
      rw [e]
      exact room)
  obtain ⟨hrun, hstk, hret, hgas⟩ := spec
  have hskel : wethTransferCall sevm qd0 (skimLegStack sevm b) (skimLegMem sevm qd0) 128
      (skimLegAmount sevm b qd0) (skimToWord sevm) (skimToken0 sevm b) 0x1a2b
      (skimLeg0Need sevm b qd0 callGasQ1 + skimLeg0Charge sevm b qd0) =
      (skimLeg0Skel sevm b qd0).withGasLeft _ :=
    wethTransferCallAt_eq _ _ _ _ _ _ _ _ _ _ _ _ _
  have hret' : (skimWethLeg0 sevm b qd0 callGasQ1).1.returnData = B256.toBytes 1 := hret
  refine ⟨hrun, hstk, Or.inr (by rw [hret']; exact one_reply_accepted), ?_⟩
  change (wethTransferCall sevm qd0 (skimLegStack sevm b) (skimLegMem sevm qd0) 128
      (skimLegAmount sevm b qd0) (skimToWord sevm) (skimToken0 sevm b) 0x1a2b
      (skimLeg0Need sevm b qd0 callGasQ1 + skimLeg0Charge sevm b qd0)).gasLeft =
    skimLeg0Next sevm b qd0 callGasQ1 (wethTransferCall sevm qd0 (skimLegStack sevm b)
      (skimLegMem sevm qd0) 128 (skimLegAmount sevm b qd0) (skimToWord sevm) (skimToken0 sevm b)
      0x1a2b (skimLeg0Need sevm b qd0 callGasQ1 + skimLeg0Charge sevm b qd0)) +
    safeTransferPostCharge (skimLegMem sevm qd0).size 128
      (wethTransferCall sevm qd0 (skimLegStack sevm b) (skimLegMem sevm qd0) 128
        (skimLegAmount sevm b qd0) (skimToWord sevm) (skimToken0 sevm b) 0x1a2b
        (skimLeg0Need sevm b qd0 callGasQ1 + skimLeg0Charge sevm b qd0)).returnData
  rw [hgas]
  conv => rhs; rw [hskel, skimLeg0Next_withGasLeft, withGasLeft_returnData]
  have hn : skimLeg0Need sevm b qd0 callGasQ1 =
      skimLeg0Next sevm b qd0 callGasQ1 (skimLeg0Skel sevm b qd0) +
        safeTransferPostCharge (skimLegMem sevm qd0).size 128
          (skimLeg0Skel sevm b qd0).returnData := rfl
  rw [← hn]
  unfold skimLeg0Charge skimLeg0Used
  omega

/-! ## amount ≤ balance -/

/-- **Skim's transfer amount is covered when the reserve is.**  For the first query's result `qd0`
of the read leg over the world `B` (`qd0`'s storage is `B`'s, and its reply is the pair's WETH9
balance word `v` at `B`), `reserve ≤ v` gives `answer − reserve ≤` the pair's WETH9 balance at `qd0`,
the transfer leg's `balance` premise.  C3 supplies `reserve ≤ v` at the `skimBalance0` suspension. -/
theorem skim_amount_le_balance {qd0 B : Devm} {a : Adr} {k reserve : B256}
    (reply : qd0.returnData = (B.getStorVal a k).toBytes)
    (storage : qd0.getStorVal a k = B.getStorVal a k)
    (cover : reserve ≤ B.getStorVal a k) :
    Bytes.toB256 (qd0.returnData.take 32) - reserve ≤ qd0.getStorVal a k := by
  rw [reply, toB256_take_toBytes, storage, B256.le_iff_toNat_le_toNat,
    B256.toNat_sub_eq_of_le _ _ cover]
  exact Nat.sub_le _ _

/-- **Skim's WETH9 legs composed (WETH9 = token0).**  With `qd0` the read leg's own result, the
transfer's premises at `qd0` reduce to the world the query is staged over: WETH9's code there, and
the cached reserve0 at most the pair's WETH9 balance there (C3's bound).  Then `skimWethLeg0` over
`skimWethRead0` is the `tenv0` record. -/
theorem skimWethLeg0_of_read {sevm : Sevm} {b : Devm} {callGasT0 callGasQ1 : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (nonstatic : sevm.isStatic = false)
    (depth : sevm.depth ≠ 0)
    (wethCode : (skimCachedWorld sevm b).state.getCode (skimToken0 sevm b).toAdr = Weth9.code)
    (notPrecompile : sevm.benvStat.rules.isPrecomp (skimToken0 sevm b).toAdr = false)
    (cover : skimReserve0 sevm b ≤
      (skimCachedWorld sevm b).getStorVal (skimToken0 sevm b).toAdr (Weth9.balSlot sevm.currentTarget))
    (fitsRead : (skimWethRead0 sevm b callGasT0).2 < 2 ^ 256)
    (roomRead : balUsed sevm (skimCachedWorld sevm b) (skimRead0Stack sevm b) getterInitMemory 128
        (skimToken0 sevm b) ≤
      except64th (skimRead0Need sevm callGasT0 (wethBalanceSkel sevm (skimCachedWorld sevm b)
          (skimRead0Stack sevm b) getterInitMemory 128 (skimToken0 sevm b)) +
        balUsed sevm (skimCachedWorld sevm b) (skimRead0Stack sevm b) getterInitMemory 128
          (skimToken0 sevm b)))
    (fits : (skimWethLeg0 sevm b (skimWethRead0 sevm b callGasT0).1 callGasQ1).2 < 2 ^ 256)
    (room : skimLeg0Used sevm b (skimWethRead0 sevm b callGasT0).1 + gCallStipend ≤
      except64th (skimLeg0Need sevm b (skimWethRead0 sevm b callGasT0).1 callGasQ1 +
        skimLeg0Used sevm b (skimWethRead0 sevm b callGasT0).1)) :
    SwapTransferCallForward sevm (skimWethRead0 sevm b callGasT0).1
      (skimToken1 sevm b :: skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77])
      (balanceReplyMemory getterInitMemory sevm.currentTarget
        (skimWethRead0 sevm b callGasT0).1.returnData)
      ((balanceReplyMemory getterInitMemory sevm.currentTarget
        (skimWethRead0 sevm b callGasT0).1.returnData).size)
      128 (Bytes.toB256 ((skimWethRead0 sevm b callGasT0).1.returnData.take 32) - skimReserve0 sevm b)
      (skimToWord sevm) (skimToken0 sevm b) 0x1a2b
      (skimWethLeg0 sevm b (skimWethRead0 sevm b callGasT0).1 callGasQ1).2
      (skimLeg0Next sevm b (skimWethRead0 sevm b callGasT0).1 callGasQ1
        (skimWethLeg0 sevm b (skimWethRead0 sevm b callGasT0).1 callGasQ1).1)
      (skimWethLeg0 sevm b (skimWethRead0 sevm b callGasT0).1 callGasQ1).1 := by
  have hret := (skimWethRead0_spec fork depth wethCode notPrecompile fitsRead roomRead).2.2
  refine skimWethLeg0_spec fork nonstatic depth ?_ notPrecompile
    (skim_amount_le_balance hret (wethReadLeg_getStorVal _ _ _ _ _ _ _ _ _) cover) fits room
  unfold skimWethRead0
  rw [wethReadLeg_state]
  exact wethCode

end Blanc.Composition.UniswapV2PairWeth9Joint
