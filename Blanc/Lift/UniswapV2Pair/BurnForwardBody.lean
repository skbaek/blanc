import Blanc.Lift.UniswapV2Pair.BurnForwardSuffix
import Blanc.Lift.UniswapV2Pair.BurnPricingWalk
import Blanc.Lift.UniswapV2Pair.BurnFrameWalk
import Blanc.Lift.UniswapV2Pair.BurnFeeTransfers
import Blanc.Lift.UniswapV2Pair.MintPrefixWalk
import Blanc.Lift.UniswapV2Pair.MintForwardAccept

/-!
# Forward Burn body and pc-zero schedule

The forward (gas-exact) Burn callee from its entry `t_13f5_c37` to its return: lock and reserve
prefix, both initial `balanceOf(pair)` requests and reads, the factory `feeTo` call and `_mintFee`
(`burnFeeForward_exact`), pricing and the LP burn (`burnPricing_exact`), and the suffix
(`burnBack_exact`); then the ABI wrapper, the pc-zero guards, `lift_exact`, and the source frame
(`burnRaw_source_authentic`).  Every callee is a forward-environment premise (ENV class).
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The first initial site's decoder: the answer word replaces the returned length. -/
theorem burnInitialDecode_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {lengthWord : B256} {out : Bytes} {o : Outcome}
    (site : BurnInitialBalanceSite) (mem : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget))
    (wf : Mem.Wf M) (long : 32 ≤ out.length) (room : R.length ≤ 1022)
    (body : SFunc.RunExact cert.prog sevm
      (St b (Bytes.toB256 (out.take 32) :: R)
        (balanceReplyMemory M sevm.currentTarget out) G) site.afterDecodeTree o) :
    SFunc.RunExact cert.prog sevm
      (St b (lengthWord :: 128 :: R) (balanceReplyMemory M sevm.currentTarget out) (G + 6))
      site.decodeTree o := by
  have shape : site.decodeTree = .dest (.next (.reg .pop)
      (.next (.reg .mload) site.afterDecodeTree)) := by cases site <;> rfl
  rw [shape]
  apply rx_dest
  apply rx_pop
  apply rx_mload (i := 128) (v := Bytes.toB256 (out.take 32)) (c := 3)
    (by rw [St.extCost_eq (balanceReplyMemory_ptr out mem).size]; decide)
    (balanceReplyMemory_word wf sevm.currentTarget out long)
    ((balanceReplyMemory_ptr out mem).read_self (by decide)) (by omega)
  exact body

/-- Every fee branch's post is an `St` over its own zero-gas world. -/
theorem feeBranchPost_St {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {K w r0 r1 : B256} {G : Nat} :
    feeBranchPost sevm b R M K w r0 r1 G =
      St (feeBranchPost sevm b R M K w r0 r1 0) (feeOnWord w :: R)
        (feeBranchPost sevm b R M K w r0 r1 0).memory G := by
  unfold feeBranchPost
  split
  · simp only [St, Devm.setMach_setMach, Devm.stateGas_setMach, Devm.memory_setMach]
  · unfold feeOnPost
    split
    · simp only [St, Devm.setMach_setMach, Devm.stateGas_setMach, Devm.memory_setMach]
    · split
      · unfold feeGrowthPost feeLiquidityPost
        split
        · simp only [St, Devm.setMach_setMach, Devm.stateGas_setMach, Devm.memory_setMach]
        · simp only [lpMintPost, lpMintSupplyPost, lpMintCreditPost, St, Devm.setMach_setMach, Devm.stateGas_setMach, Devm.memory_setMach]
      · simp only [St, Devm.setMach_setMach, Devm.stateGas_setMach, Devm.memory_setMach]

/-! ## Worlds and words of the prefix -/

/-- The 160-bit address mask. -/
abbrev burnAddrMask : B256 := 0xffffffffffffffffffffffffffffffffffffffff

/-- The world after the lock and the reserve cache. -/
def burnReservedWorld (sevm : Sevm) (b : Devm) : Devm :=
  afterSload sevm (burnLockedWorld sevm b) 8

/-- The cached reserves. -/
def burnR0 (sevm : Sevm) (b : Devm) : B256 :=
  reserve0Read ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8)

def burnR1 (sevm : Sevm) (b : Devm) : B256 :=
  reserve1Read ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8)

/-- The cached token words. -/
def burnT0 (sevm : Sevm) (b : Devm) : B256 :=
  burnAddrMask &&& (burnReservedWorld sevm b).getStorVal sevm.currentTarget 6

def burnT1 (sevm : Sevm) (b : Devm) : B256 :=
  burnAddrMask &&& (afterSload sevm (burnReservedWorld sevm b) 6).getStorVal sevm.currentTarget 7

/-- The world at the first initial `STATICCALL`. -/
def burnCall0World (sevm : Sevm) (b : Devm) : Devm :=
  temporalAccountAccessBase (burnTokensWorld sevm (burnReservedWorld sevm b)) (burnT0 sevm b).toAdr

/-- The world at the second initial `STATICCALL`. -/
def burnCall1World (sevm : Sevm) (b d0 : Devm) : Devm :=
  temporalAccountAccessBase d0 (burnT1 sevm b &&& burnAddrMask).toAdr

/-- The recipient word the ABI wrapper passes. -/
def burnRecipientWord (sevm : Sevm) : B256 := (Sevm.dataWord sevm 4).toAdr.toB256

/-- The callee's locals below the request staging, over the wrapper tail `R`. -/
def burnInitLocals (sevm : Sevm) (b : Devm) (R : List B256) : List B256 :=
  burnR1 sevm b :: burnR0 sevm b :: 0 :: 0 :: burnRecipientWord sevm :: 0x053d :: R

/-- The memory after the first initial reply. -/
def burnMem1 (sevm : Sevm) (d0 : Devm) : Mem :=
  balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData

/-- The memory after the second initial reply. -/
def burnMem2 (sevm : Sevm) (d0 d1 : Devm) : Mem :=
  balanceReplyMemory (burnMem1 sevm d0) sevm.currentTarget d1.returnData

/-- The first initial answer. -/
def burnB0 (d0 : Devm) : B256 := Bytes.toB256 (d0.returnData.take 32)

/-- The gas the first initial callee forwards over its pre-call charges, given the gas `G` at the
second initial `STATICCALL`. -/
def burnInitialGas0 (sevm : Sevm) (b : Devm) (callGas0 : Nat) : Nat :=
  callGas0 + 5 + sloadCost sevm (burnReservedWorld sevm b) 6 +
    sloadCost sevm (afterSload sevm (burnReservedWorld sevm b) 6) 7 +
    temporalAccountAccessCost (burnTokensWorld sevm (burnReservedWorld sevm b))
      (burnT0 sevm b).toAdr + 184

/-- The gas the second request stages after the first answer. -/
def burnInitialGas1 (sevm : Sevm) (b d0 : Devm) (callGas1 : Nat) : Nat :=
  callGas1 + 5 + temporalAccountAccessCost d0 (burnT1 sevm b &&& burnAddrMask).toAdr + 140 + 6

/-- **The initial calls' primitive data**: the lock and reserve charges, both initial
`balanceOf(pair)` `STATICCALL`s from their actual staged states with success, a word of reply and
the gas each returns (`T1 + 64` for the second, `T1` the gas the fee caller needs). -/
structure BurnInitialCallee (sevm : Sevm) (b d0 d1 : Devm) (R : List B256) (T1 : Nat) where
  callGas0 : Nat
  callGas1 : Nat
  lockLoad : Nat
  lockStore : Nat
  reserveLoad : Nat
  loadEq : lockLoad = sloadCost sevm b 12
  storeEq : lockStore = sstoreCost sevm (afterSload sevm b 12) 12 0
  reserveEq : reserveLoad = sloadCost sevm (burnLockedWorld sevm b) 8
  sentry : gCallStipend < burnInitialGas0 sevm b callGas0 + reserveLoad + 87 + lockStore
  code0 : ((burnTokensWorld sevm (burnReservedWorld sevm b)).getCode
    (burnT0 sevm b).toAdr).size.toB256 ≠ 0
  call0 : Ninst.RunCompiled sevm
    (St (burnCall0World sevm b) (callGas0.toB256 :: burnT0 sevm b :: 128 :: 36 :: 128 :: 32 ::
      164 :: 0x70a08231 :: burnT0 sevm b :: 0 :: burnT1 sevm b :: burnT0 sevm b ::
      burnInitLocals sevm b R)
      (balanceRequestMemory getterInitMemory sevm.currentTarget) callGas0) (.exec .staticcall) d0
  success0 : d0.stack = 1 :: 164 :: 0x70a08231 :: burnT0 sevm b :: 0 :: burnT1 sevm b ::
    burnT0 sevm b :: burnInitLocals sevm b R
  long0 : 32 ≤ d0.returnData.length
  returnedGas0 : d0.gasLeft = burnInitialGas1 sevm b d0 callGas1 + 64
  code1 : (d0.getCode (burnT1 sevm b &&& burnAddrMask).toAdr).size.toB256 ≠ 0
  call1 : Ninst.RunCompiled sevm
    (St (burnCall1World sevm b d0) (callGas1.toB256 :: (burnT1 sevm b &&& burnAddrMask) ::
      128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 :: (burnT1 sevm b &&& burnAddrMask) :: 0 ::
      burnB0 d0 :: burnT1 sevm b :: burnT0 sevm b :: burnInitLocals sevm b R)
      (balanceRequestMemory (burnMem1 sevm d0) sevm.currentTarget) callGas1) (.exec .staticcall) d1
  success1 : d1.stack = 1 :: 164 :: 0x70a08231 :: (burnT1 sevm b &&& burnAddrMask) :: 0 ::
    burnB0 d0 :: burnT1 sevm b :: burnT0 sevm b :: burnInitLocals sevm b R
  long1 : 32 ≤ d1.returnData.length
  returnedGas1 : d1.gasLeft = T1 + 64

/-- The callee's entry gas. -/
def BurnInitialCallee.gas {sevm : Sevm} {b d0 d1 : Devm} {R : List B256} {T1 : Nat}
    (c : BurnInitialCallee sevm b d0 d1 R T1) : Nat :=
  burnInitialGas0 sevm b c.callGas0 + c.reserveLoad + 100 + c.lockStore + c.lockLoad + 29

/-- **Forward initial prefix**: from the callee entry, the lock, the reserve cache, both initial
`balanceOf(pair)` requests and reads, to the fee caller `t_15c3_c37`. -/
theorem burnInitial_exact {sevm : Sevm} {b d0 d1 : Devm} {R : List B256} {T1 : Nat} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (room : R.length ≤ 980)
    (unlocked : b.getStorVal sevm.currentTarget 12 = 1) (nonstatic : sevm.isStatic = false)
    (c : BurnInitialCallee sevm b d0 d1 R T1)
    (body : SFunc.RunExact cert.prog sevm
      (St d1 (d1.returnData.length.toB256 :: 128 :: 0 :: burnB0 d0 :: burnT1 sevm b ::
        burnT0 sevm b :: burnInitLocals sevm b R) (burnMem2 sevm d0 d1) T1) t_15c3_c37 o) :
    SFunc.RunExact cert.prog sevm
      (St b (burnRecipientWord sevm :: 0x053d :: R) getterInitMemory c.gas) t_13f5_c37 o := by
  have req0 := balanceRequestMemory_ptr getterInitMemory_ptr sevm.currentTarget
  have reply0 := balanceReplyMemory_ptr d0.returnData req0
  have req1 := balanceRequestMemory_ptr reply0 sevm.currentTarget
  have bound0 := Blanc.Lift.ReturnDataBound.staticcall_returnData_length_lt
    (by obtain ⟨xl, filled, step⟩ := c.call0; exact ⟨xl, filled, 0, step 0⟩) fork
  have bound1 := Blanc.Lift.ReturnDataBound.staticcall_returnData_length_lt
    (by obtain ⟨xl, filled, step⟩ := c.call1; exact ⟨xl, filled, 0, step 0⟩) fork
  have read1 := burnInitialBalanceRead_exact (z := 0) .second fork req1
    (by simp only [burnInitLocals, List.length_cons]; omega) c.call1 c.success1 c.returnedGas1
    bound1 c.long1 body
  have request1 := burnInitialSecondRequest_exact (G := c.callGas1 + 5) fork reply0
    (by omega) c.code1 read1
  have decode0 := burnInitialDecode_exact (lengthWord := d0.returnData.length.toB256) .first req0
    getterInitMemory_ptr.wf c.long0 (by simp only [List.length_cons]; omega)
    request1
  have read0 := burnInitialBalanceRead_exact (z := 0) .first fork req0
    (by simp only [burnInitLocals, List.length_cons]; omega) c.call0 c.success0 c.returnedGas0
    bound0 c.long0 decode0
  have request0 := burnInitialFirstRequest_exact
    (timestamp := reserveTimestampRead ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8))
    (R := R) fork getterInitMemory_ptr (by omega) c.code0 read0
  have prefix_ := burnReservePrefix_exact (R := R) fork (by omega) unlocked
    nonstatic c.loadEq c.storeEq c.reserveEq c.sentry request0
  exact prefix_

/-! ## Fee and pricing -/

/-- The LP burn's post is an `St` over its own zero-gas world. -/
theorem lpBurnPost_St {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {fromWord value : B256} {G : Nat} :
    lpBurnPost sevm b R M fromWord value G =
      St (lpBurnPost sevm b R M fromWord value 0) R (lpBurnPost sevm b R M fromWord value 0).memory G := by
  simp only [lpBurnPost, lpBurnBalancePost, lpBurnSupplyPost, St, Devm.setMach_setMach, Devm.stateGas_setMach, Devm.memory_setMach]

/-- `feeMintBranchGas` over a kLast word `K` instead of a model state. -/
def feeBranchGasAt (sevm : Sevm) (b : Devm) (K w r0 r1 : B256) (G : Nat) : Nat :=
  G + feeBranchCharge sevm b K w r0 r1
    (lpMintSourceCharge sevm (afterSload sevm b 0))
    (lpMintSupplyCharge sevm (afterSload sevm b 0)
      (feeGrowthLiquidity sevm b (feeLastRoot K) (feeReserveRoot r0 r1)))
    (lpMintRecipientLoadCharge sevm (afterSload sevm b 0) w
      (feeGrowthLiquidity sevm b (feeLastRoot K) (feeReserveRoot r0 r1)))
    (lpMintCreditCharge sevm (afterSload sevm b 0) w
      (feeGrowthLiquidity sevm b (feeLastRoot K) (feeReserveRoot r0 r1)))

theorem feeMintBranchGas_at {st : State} {sevm : Sevm} {b : Devm} {w r0 r1 : B256} {G : Nat} :
    feeMintBranchGas st sevm b w r0 r1 G = feeBranchGasAt sevm b st.kLast w r0 r1 G := rfl

/-- The fee branch's residual sentries over a kLast word `K` (`FeeMintStoreConditions` without
its mutability part, which follows from the frame). -/
structure FeeSentriesAt (sevm : Sevm) (b : Devm) (K w r0 r1 : B256) (G : Nat) : Prop where
  clearSentry : w.toAdr.toB256 = 0 → K ≠ 0 →
    gCallStipend < G + sstoreCost sevm b 11 0 + 23
  supplySentry : w.toAdr.toB256 ≠ 0 → K ≠ 0 → feeLastRoot K < feeReserveRoot r0 r1 →
    feeGrowthLiquidity sevm b (feeLastRoot K) (feeReserveRoot r0 r1) ≠ 0 →
      lpMintSupplySentry sevm (afterSload sevm b 0) w
        (feeGrowthLiquidity sevm b (feeLastRoot K) (feeReserveRoot r0 r1)) (G + 47)
  creditSentry : w.toAdr.toB256 ≠ 0 → K ≠ 0 → feeLastRoot K < feeReserveRoot r0 r1 →
    feeGrowthLiquidity sevm b (feeLastRoot K) (feeReserveRoot r0 r1) ≠ 0 →
      lpMintCreditSentry sevm (afterSload sevm b 0) w
        (feeGrowthLiquidity sevm b (feeLastRoot K) (feeReserveRoot r0 r1)) (G + 47)

/-- The fee caller's locals. -/
def burnFeeLocalsAt (sevm : Sevm) (d1 : Devm) (M : Mem) (b0 t1 t0 r1 r0 toWord extρ : B256)
    (R : List B256) : List B256 :=
  burnFeeLocals (feeBurnLiquidity sevm d1) (feeBurnBalance1 M) b0 t1 t0 r1 r0 toWord extρ R

/-- The fee branch's post world (zero gas) over the factory's answer. -/
def burnFeeWorld (sevm : Sevm) (d1 dF : Devm) (M : Mem) (b0 t1 t0 r1 r0 toWord extρ : B256)
    (R : List B256) : Devm :=
  feeBranchPost sevm (feeKLastWorld sevm dF) (burnFeeLocalsAt sevm d1 M b0 t1 t0 r1 r0 toWord extρ R)
    (feeReplyMemory (feeBurnMemory M sevm.currentTarget) dF.returnData) (feeKLastWord sevm dF)
    (Bytes.toB256 (dF.returnData.take 32)) r0 r1 0

/-- The supply word pricing reads. -/
def burnSupplyAt (sevm : Sevm) (d1 dF : Devm) (M : Mem) (b0 t1 t0 r1 r0 toWord extρ : B256)
    (R : List B256) : B256 :=
  (burnFeeWorld sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R).getStorVal sevm.currentTarget 0

/-- The suffix words after pricing. -/
def burnPricedWords (sevm : Sevm) (d1 dF : Devm) (M : Mem) (b0 t1 t0 r1 r0 toWord extρ : B256)
    (R : List B256) : BurnSuffixWords where
  supply := burnSupplyAt sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R
  feeFlag := feeOnWord (Bytes.toB256 (dF.returnData.take 32))
  liquidity := feeBurnLiquidity sevm d1
  balance1 := feeBurnBalance1 M
  balance0 := b0
  token1 := t1
  token0 := t0
  reserve1 := r1
  reserve0 := r0
  amount1 := (feeBurnLiquidity sevm d1 * feeBurnBalance1 M) /
    burnSupplyAt sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R
  amount0 := (feeBurnLiquidity sevm d1 * b0) / burnSupplyAt sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R
  recipient := toWord
  ret := extρ

/-- The world after pricing and the LP burn (zero gas). -/
def burnPricedWorld (sevm : Sevm) (d1 dF : Devm) (M : Mem) (b0 t1 t0 r1 r0 toWord extρ : B256)
    (R : List B256) : Devm :=
  lpBurnPost sevm (afterSload sevm (burnFeeWorld sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R) 0)
    ((burnPricedWords sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R).locals (feeBurnBalance1 M) b0 R)
    (burnFeeWorld sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R).memory sevm.currentTarget.toB256
    (feeBurnLiquidity sevm d1) 0

/-- The gas pricing needs over the suffix's entry gas `Gp`. -/
def burnFeeResidual (sevm : Sevm) (d1 dF : Devm) (M : Mem) (b0 t1 t0 r1 r0 toWord extρ : B256)
    (R : List B256) (Gp : Nat) : Nat :=
  burnPricingGas sevm (burnFeeWorld sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R)
    (feeBurnLiquidity sevm d1) (feeBurnBalance1 M) b0 Gp

/-- **The factory call's and pricing's primitive data**: the `feeTo` `STATICCALL` from its staged
state with success, a word of reply and its returned gas over the fee branch and pricing, the fee
branch's sentries and the LP burn's two store sentries. -/
structure BurnFeeCallee (sevm : Sevm) (d1 dF : Devm) (M : Mem)
    (b0 t1 t0 r1 r0 toWord extρ : B256) (R : List B256) (Gp : Nat) where
  factoryGas : Nat
  code : ((feeFactoryLoadWorld sevm (feeBurnWorld sevm d1)).getCode
    (feeFactoryWord sevm (feeBurnWorld sevm d1)).toAdr).size.toB256 ≠ 0
  call : Ninst.RunCompiled sevm
    (St (feeFactoryCallWorld sevm (feeBurnWorld sevm d1))
      (factoryGas.toB256 :: feeFactoryWord sevm (feeBurnWorld sevm d1) :: 128 :: 4 :: 128 :: 32 ::
        132 :: 0x017e7e58 :: feeFactoryWord sevm (feeBurnWorld sevm d1) :: 0 :: 0 :: r1 :: r0 ::
        0x15e2 :: burnFeeLocalsAt sevm d1 M b0 t1 t0 r1 r0 toWord extρ R)
      (feeRequestMemory (feeBurnMemory M sevm.currentTarget)) factoryGas) (.exec .staticcall) dF
  success : dF.stack = 1 :: 132 :: 0x017e7e58 :: feeFactoryWord sevm (feeBurnWorld sevm d1) ::
    0 :: 0 :: r1 :: r0 :: 0x15e2 :: burnFeeLocalsAt sevm d1 M b0 t1 t0 r1 r0 toWord extρ R
  width : 32 ≤ dF.returnData.length
  returnedGas : dF.gasLeft = feeBranchGasAt sevm (feeKLastWorld sevm dF) (feeKLastWord sevm dF)
    (Bytes.toB256 (dF.returnData.take 32)) r0 r1
    (burnFeeResidual sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R Gp) + sloadCost sevm dF 11 + 120
  sentries : FeeSentriesAt sevm (feeKLastWorld sevm dF) (feeKLastWord sevm dF)
    (Bytes.toB256 (dF.returnData.take 32)) r0 r1
    (burnFeeResidual sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R Gp)
  balanceSentry : lpBurnBalanceSentry sevm
    (afterSload sevm (burnFeeWorld sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R) 0)
    sevm.currentTarget.toB256 (feeBurnLiquidity sevm d1) Gp
  supplySentry : lpBurnSupplySentry sevm
    (afterSload sevm (burnFeeWorld sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R) 0)
    sevm.currentTarget.toB256 (feeBurnLiquidity sevm d1) Gp

/-- The fee caller's entry gas. -/
def BurnFeeCallee.gas {sevm : Sevm} {d1 dF : Devm} {M : Mem} {b0 t1 t0 r1 r0 toWord extρ : B256}
    {R : List B256} {Gp : Nat} (c : BurnFeeCallee sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R Gp) :
    Nat :=
  feeMintEntryGas sevm (feeBurnWorld sevm d1) c.factoryGas +
    sloadCost sevm d1 (transferBalanceSlot sevm.currentTarget) + 105

/-- **Forward fee and pricing** (`t_15c3_c37` to `t_168d_c13`): the factory call, `_mintFee` and
the LP burn, under the locked state's representation, the fee mint the model accepts at the
factory's actual answer, and the burn pricing and LP debit it accepts. -/
theorem burnFeePricing_exact {K : WriterKey → Prop} {st post : State} {fee : FeeResult}
    {events : List Event} {amount0 amount1 : Nat}
    {sevm : Sevm} {d1 dF : Devm} {M : Mem} {b0 t1 t0 r1 r0 toWord extρ : B256} {R : List B256}
    {Gp : Nat} {len discarded : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M) (room : R.length ≤ 990)
    (rep : WriterRep K (d1.getStor sevm.currentTarget) st)
    (tracked : K (.balance sevm.currentTarget)) (nonstatic : sevm.isStatic = false)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (c : BurnFeeCallee sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R Gp)
    (accepted : mintFee st (Bytes.toB256 (dF.returnData.take 32)).toAdr r0.toNat r1.toNat = .ok fee)
    (fresh : FeeMintFresh K st sevm (feeKLastWorld sevm dF) (Bytes.toB256 (dF.returnData.take 32))
      r0 r1)
    (priced : burnAmounts (st.balanceOf sevm.currentTarget) b0 (feeBurnBalance1 M)
      fee.state.totalSupply = .ok (amount0, amount1))
    (positive0 : 0 < amount0) (positive1 : 0 < amount1)
    (burned : fee.state.burnLP sevm.currentTarget (st.balanceOf sevm.currentTarget) =
      .ok (post, events)) :
    (burnPricedWords sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R).amount0 ≠ 0 ∧
    (burnPricedWords sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R).amount1 ≠ 0 ∧
    ∀ o, SFunc.RunExact cert.prog sevm
      (St (burnPricedWorld sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R)
        ((burnPricedWords sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R).locals (feeBurnBalance1 M) b0 R)
        (burnPricedWorld sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R).memory Gp) t_168d_c13 o →
    SFunc.RunExact cert.prog sevm
      (St d1 (len :: 128 :: discarded :: b0 :: t1 :: t0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
        M c.gas) t_15c3_c37 o := by
  let FL := burnFeeLocalsAt sevm d1 M b0 t1 t0 r1 r0 toWord extρ R
  let w := Bytes.toB256 (dF.returnData.take 32)
  let GF := burnFeeResidual sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R Gp
  have rep' : WriterRep K ((feeBurnWorld sevm d1).getStor sevm.currentTarget) st := by
    simpa only [feeBurnWorld, afterSload_getStor] using rep
  have postCall := feeFactoryCompiled_post fork c.call c.success
  have postRep := rep'.fee_factory_post postCall
  have last : feeKLastWord sevm dF = st.kLast := by
    rcases postRep.fixed with ⟨_, _, _, _, _, _, _, _, _, _, lastWord, _⟩
    change (dF.getStor sevm.currentTarget).get 11 = st.kLast
    simpa only [feeKLastWorld, afterSload_getStor] using lastWord
  have sentries := c.sentries
  have returnedGas := c.returnedGas
  rw [last] at sentries returnedGas
  have input : FeeMintForwardInput K st sevm (feeBurnWorld sevm d1) dF FL
      (feeBurnMemory M sevm.currentTarget) r1 r0 0x15e2 GF c.factoryGas fee :=
    ⟨fork, feeBurnMemory_ptr mem sevm.currentTarget, rep', bound0, bound1,
      by simp only [FL, burnFeeLocalsAt, burnFeeLocals, List.length_cons]; omega,
      c.code, c.call, c.success, c.width, accepted, fresh,
      ⟨⟨fun _ _ => nonstatic, fun _ _ _ _ => nonstatic⟩, sentries.clearSentry,
        sentries.supplySentry, sentries.creditSentry⟩,
      by rw [returnedGas]; rfl⟩
  have feeMem : PtrMem 128 192 (feeReplyMemory (feeBurnMemory M sevm.currentTarget) dF.returnData) :=
    feeReplyMemory_ptr dF.returnData (feeRequestMemory_ptr (feeBurnMemory_ptr mem sevm.currentTarget))
  have machine := mintFeePost_machine (sevm := sevm) (b := feeKLastWorld sevm dF) (R := FL)
    (K := feeKLastWord sevm dF) (w := w) (r0 := r0) (r1 := r1) (G := 0) feeMem
  obtain ⟨_, source, feeEq⟩ := input.exact
  have cached := input.rep.selected (.balance sevm.currentTarget) tracked
  simp only [feeBurnWorld, afterSload_getStor] at cached
  change feeBurnLiquidity sevm d1 = st.balanceOf sevm.currentTarget at cached
  let bF0 := burnFeeWorld sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R
  have startEq : feeMintSourcePost st sevm dF FL (feeBurnMemory M sevm.currentTarget) r0 r1 GF =
      St bF0 (feeOnWord w :: FL) bF0.memory GF := by
    unfold feeMintSourcePost
    rw [← last, feeBranchPost_St]
    rfl
  have repF : WriterRep (feeBranchSourceKeys K st sevm (feeKLastWorld sevm dF) w r0 r1)
      (bF0.getStor sevm.currentTarget) fee.state := by
    have h := source.2.1
    rw [feeEq, ← last, feeBranchPost_St, St_getStor] at h
    exact h
  have trackedAfter : (feeBranchSourceKeys K st sevm (feeKLastWorld sevm dF) w r0 r1)
      (.balance sevm.currentTarget) := by
    unfold feeBranchSourceKeys
    split
    · exact tracked
    · split
      · exact tracked
      · split
        · split
          · exact tracked
          · exact Or.inl tracked
        · exact tracked
  have freshF : WriterFreshKeys (feeBranchSourceKeys K st sevm (feeKLastWorld sevm dF) w r0 r1)
      (lpMintTouched sevm.currentTarget) := by
    apply Blanc.SlotFootprint.FreshKeys.of_universe repF.inj repF.apart (fun _ h => h)
    intro k member
    have eq := List.mem_singleton.mp (show k ∈ [WriterKey.balance sevm.currentTarget] from member)
    subst k
    exact trackedAfter
  have supplyEq : bF0.getStorVal sevm.currentTarget 0 = fee.state.totalSupply := repF.fixed.1
  have priced' : burnAmounts (feeBurnLiquidity sevm d1) b0 (feeBurnBalance1 M)
      (bF0.getStorVal sevm.currentTarget 0) = .ok (amount0, amount1) := by
    rw [cached, supplyEq]
    exact priced
  have burned' : fee.state.burnLP sevm.currentTarget (feeBurnLiquidity sevm d1) =
      .ok (post, events) := by
    rw [cached]
    exact burned
  have values := (burnPricing_source_inv priced').2.2.2
  have nonzero0 : (burnPricedWords sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R).amount0 ≠ 0 := by
    intro zero
    have h := congrArg Prod.fst values
    change amount0 = ((feeBurnLiquidity sevm d1 * b0) / bF0.getStorVal sevm.currentTarget 0).toNat at h
    change (feeBurnLiquidity sevm d1 * b0) / bF0.getStorVal sevm.currentTarget 0 = 0 at zero
    rw [zero, B256.toNat_zero] at h
    omega
  have nonzero1 : (burnPricedWords sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R).amount1 ≠ 0 := by
    intro zero
    have h := congrArg Prod.snd values
    change amount1 =
      ((feeBurnLiquidity sevm d1 * feeBurnBalance1 M) / bF0.getStorVal sevm.currentTarget 0).toNat at h
    change (feeBurnLiquidity sevm d1 * feeBurnBalance1 M) / bF0.getStorVal sevm.currentTarget 0 = 0
      at zero
    rw [zero, B256.toNat_zero] at h
    omega
  refine ⟨nonzero0, nonzero1, fun o body => ?_⟩
  refine (feeBurn_source_caller_exact (len := len) (discarded := discarded) mem tracked input
    ?_).2.1
  have cont : SFunc.RunExactCut cert.prog sevm []
      (lpBurnPost sevm (afterSload sevm bF0 0)
        (burnPricedLocals (bF0.getStorVal sevm.currentTarget 0) (feeOnWord w)
          (feeBurnLiquidity sevm d1) (feeBurnBalance1 M) b0 t1 t0 r1 r0
          ((feeBurnLiquidity sevm d1 * feeBurnBalance1 M) / bF0.getStorVal sevm.currentTarget 0)
          ((feeBurnLiquidity sevm d1 * b0) / bF0.getStorVal sevm.currentTarget 0) toWord extρ R)
        bF0.memory sevm.currentTarget.toB256 (feeBurnLiquidity sevm d1) Gp) t_168d_c13 (.done o) := by
    apply SFunc.runExact_iff_runExactCut_nil.mp
    rw [lpBurnPost_St]
    exact body
  have pricing := burnPricing_exact (C := []) fork machine.2 repF freshF priced' positive0 positive1
    burned' nonstatic c.balanceSentry c.supplySentry (by omega) cont
  show SFunc.RunExact cert.prog sevm
    (feeMintSourcePost st sevm dF FL (feeBurnMemory M sevm.currentTarget) r0 r1 GF) t_15e2_c37 o
  rw [startEq]
  exact SFunc.runExact_iff_runExactCut_nil.mpr pricing.1

/-! ## The whole callee and the pc-zero schedule -/

/-- The world after Burn's pricing, over the callees' results. -/
@[irreducible] def burnBodyWorld (sevm : Sevm) (b d0 d1 dF : Devm) : Devm :=
  burnPricedWorld sevm d1 dF (burnMem2 sevm d0 d1) (burnB0 d0) (burnT1 sevm b) (burnT0 sevm b)
    (burnR1 sevm b) (burnR0 sevm b) (burnRecipientWord sevm) 0x053d [0x89afcb44]

theorem burnBodyWorld_def {sevm : Sevm} {b d0 d1 dF : Devm} :
    burnBodyWorld sevm b d0 d1 dF =
      burnPricedWorld sevm d1 dF (burnMem2 sevm d0 d1) (burnB0 d0) (burnT1 sevm b) (burnT0 sevm b)
        (burnR1 sevm b) (burnR0 sevm b) (burnRecipientWord sevm) 0x053d [0x89afcb44] := by
  unfold burnBodyWorld
  rfl

/-- The suffix words after Burn's pricing, over the callees' results. -/
def burnBodyWords (sevm : Sevm) (b d0 d1 dF : Devm) : BurnSuffixWords :=
  burnPricedWords sevm d1 dF (burnMem2 sevm d0 d1) (burnB0 d0) (burnT1 sevm b) (burnT0 sevm b)
    (burnR1 sevm b) (burnR0 sevm b) (burnRecipientWord sevm) 0x053d [0x89afcb44]

/-- **The callee-only Burn environment**: the two initial `balanceOf(pair)` `STATICCALL`s, the
factory `feeTo` `STATICCALL`, both transfer `CALL`s and both final `balanceOf(pair)` `STATICCALL`s,
each from its actual staged state with its success, reply and returned gas, with the lock, reserve,
fee-branch, LP-burn, update, checkpoint and unlock charges and sentries, ending at residual `g`. No
model acceptance fact and no successful run is part of it. -/
structure BurnForwardEnv (pre : Nat → B256 → Nat) (post : Nat → B256 → Bytes → Nat)
    (sevm : Sevm) (b : Devm) (g : Nat) where
  d0 : Devm
  d1 : Devm
  dF : Devm
  back : BurnBackForwardEnv pre post sevm (burnBodyWorld sevm b d0 d1 dF)
    (burnBodyWorld sevm b d0 d1 dF).memory 128 (burnBodyWords sevm b d0 d1 dF) [0x89afcb44] (g + 64)
  fee : BurnFeeCallee sevm d1 dF (burnMem2 sevm d0 d1) (burnB0 d0) (burnT1 sevm b) (burnT0 sevm b)
    (burnR1 sevm b) (burnR0 sevm b) (burnRecipientWord sevm) 0x053d [0x89afcb44] back.gas
  initial : BurnInitialCallee sevm b d0 d1 [0x89afcb44] fee.gas

/-- The pc-zero gas. -/
def BurnForwardEnv.gas {pre : Nat → B256 → Nat} {post : Nat → B256 → Bytes → Nat}
    {sevm : Sevm} {b : Devm} {g : Nat} (env : BurnForwardEnv pre post sevm b g) : Nat :=
  env.initial.gas + 249

/-- The halted world: the suffix's world with both amounts returned at the moved pointer. -/
def BurnForwardEnv.post {pre : Nat → B256 → Nat} {post : Nat → B256 → Bytes → Nat}
    {sevm : Sevm} {b : Devm} {g : Nat} (env : BurnForwardEnv pre post sevm b g) : Devm :=
  burnReturnPost env.back.post [0x89afcb44] env.back.memory
    (burnSuffixPtr 128 env.back.d0 env.back.d1) (burnBodyWords sevm b env.d0 env.d1 env.dF).amount0
    (burnBodyWords sevm b env.d0 env.d1 env.dF).amount1 g

/-- The factory's answer, both initial answers and both final answers. -/
def BurnForwardEnv.feeTo {pre : Nat → B256 → Nat} {post : Nat → B256 → Bytes → Nat}
    {sevm : Sevm} {b : Devm} {g : Nat} (env : BurnForwardEnv pre post sevm b g) : Adr :=
  (Bytes.toB256 (env.dF.returnData.take 32)).toAdr

def BurnForwardEnv.balance0 {pre : Nat → B256 → Nat} {post : Nat → B256 → Bytes → Nat}
    {sevm : Sevm} {b : Devm} {g : Nat} (env : BurnForwardEnv pre post sevm b g) : B256 :=
  Bytes.toB256 (env.d0.returnData.take 32)

def BurnForwardEnv.balance1 {pre : Nat → B256 → Nat} {post : Nat → B256 → Bytes → Nat}
    {sevm : Sevm} {b : Devm} {g : Nat} (env : BurnForwardEnv pre post sevm b g) : B256 :=
  Bytes.toB256 (env.d1.returnData.take 32)

def BurnForwardEnv.final0 {pre : Nat → B256 → Nat} {post : Nat → B256 → Bytes → Nat}
    {sevm : Sevm} {b : Devm} {g : Nat} (env : BurnForwardEnv pre post sevm b g) : B256 :=
  Bytes.toB256 (env.back.e0.returnData.take 32)

def BurnForwardEnv.final1 {pre : Nat → B256 → Nat} {post : Nat → B256 → Bytes → Nat}
    {sevm : Sevm} {b : Devm} {g : Nat} (env : BurnForwardEnv pre post sevm b g) : B256 :=
  Bytes.toB256 (env.back.e1.returnData.take 32)

/-- The primitive guards of a successful Burn at the callees' actual answers, over the entry
state `st` the frame's storage represents: the lock is open, the frame is mutable, the fee mint the
model accepts at the locked state and the factory's answer (with HASH-T freshness of its LP row),
the burn pricing and LP debit it accepts at the initial answers, and both final answers fit
`uint112`. -/
structure BurnForwardGuards (K : WriterKey → Prop) (st : State) (sevm : Sevm) (b : Devm)
    (d0 d1 dF e0 e1 : Devm) : Prop where
  unlocked : st.unlocked = 1
  nonstatic : sevm.isStatic = false
  feeAccepted : ∃ fee, mintFee { st with unlocked := 0 } (Bytes.toB256 (dF.returnData.take 32)).toAdr
      (burnR0 sevm b).toNat (burnR1 sevm b).toNat = .ok fee ∧
    ∃ amount0 amount1 post events,
      burnAmounts (st.balanceOf sevm.currentTarget) (burnB0 d0)
        (feeBurnBalance1 (burnMem2 sevm d0 d1)) fee.state.totalSupply = .ok (amount0, amount1) ∧
      0 < amount0 ∧ 0 < amount1 ∧
      fee.state.burnLP sevm.currentTarget (st.balanceOf sevm.currentTarget) = .ok (post, events)
  fresh : FeeMintFresh K { st with unlocked := 0 } sevm (feeKLastWorld sevm dF)
    (Bytes.toB256 (dF.returnData.take 32)) (burnR0 sevm b) (burnR1 sevm b)
  bound0 : (Bytes.toB256 (e0.returnData.take 32)).toNat < 2 ^ 112
  bound1 : (Bytes.toB256 (e1.returnData.take 32)).toNat < 2 ^ 112

/-- Both cached reserves fit `uint112`. -/
theorem burnR_bounds (sevm : Sevm) (b : Devm) :
    (burnR0 sevm b).toNat < 2 ^ 112 ∧ (burnR1 sevm b).toNat < 2 ^ 112 := by
  constructor
  · unfold burnR0 reserve0Read
    rw [show reserveMask112 = (2 ^ 112 - 1 : Nat).toB256 from rfl,
      PackedWord.lowMask_toNat _ (by decide : 112 ≤ 256)]
    exact Nat.mod_lt _ (by decide)
  · unfold burnR1 reserve1Read
    rw [show reserveMask112 = (2 ^ 112 - 1 : Nat).toB256 from rfl,
      PackedWord.lowMask_toNat _ (by decide : 112 ≤ 256)]
    exact Nat.mod_lt _ (by decide)

/-- **Forward Burn from pc zero.** From the nonpayable, size, ABI-length and selector guards, the
entry storage representing `st` with the Pair's LP row tracked, the callee-only environment and the
primitive guards at its actual answers, the original bytes run from pc zero with exact initial gas
`env.gas` and halt with both amounts returned and residual `g`.
CROSS-HOST: conditional on `SwapSafeTransferForward`. -/
theorem burnPc0_exact {K : WriterKey → Prop} {st : State}
    {pre : Nat → B256 → Nat} {post : Nat → B256 → Bytes → Nat}
    {sevm : Sevm} {b : Devm} {g : Nat}
    (helper : SwapSafeTransferForward pre post)
    (fork : CoveredFork sevm.benvStat.fork) (value : sevm.value = 0)
    (size : (4 : B256) ≤ sevm.data.length.toB256)
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (tracked : K (.balance sevm.currentTarget))
    (env : BurnForwardEnv pre post sevm b g)
    (guards : BurnForwardGuards K st sevm b env.d0 env.d1 env.dF env.back.e0 env.back.e1) :
    SFunc.RunExact cert.prog sevm (St b [] Mem.empty env.gas) t_0000_c0 (.halted env.post) := by
  obtain ⟨unlocked, nonstatic, ⟨fee, feeAccepted, amount0, amount1, burnPost, events, priced,
    positive0, positive1, burned⟩, fresh, final0, final1⟩ := guards
  have unlockedRaw : b.getStorVal sevm.currentTarget 12 = 1 :=
    rep.fixed.2.2.2.2.2.2.2.2.2.2.2.trans unlocked
  obtain ⟨bound0, bound1⟩ := burnR_bounds sevm b
  have stor0 := compiled_staticcall_stor fork env.initial.call0
  have stor1 := compiled_staticcall_stor fork env.initial.call1
  have d1Rep : WriterRep K (env.d1.getStor sevm.currentTarget) { st with unlocked := 0 } := by
    have same : env.d1.getStor sevm.currentTarget =
        (burnLockedWorld sevm b).getStor sevm.currentTarget :=
      calc env.d1.getStor sevm.currentTarget
          = (burnCall1World sevm b env.d0).getStor sevm.currentTarget := stor1 _
        _ = env.d0.getStor sevm.currentTarget := by
          simp only [burnCall1World, Devm.getStor, Devm.getAcct, temporalAccountAccessBase_state]
        _ = (burnCall0World sevm b).getStor sevm.currentTarget := stor0 _
        _ = (burnTokensWorld sevm (burnReservedWorld sevm b)).getStor sevm.currentTarget := by
          simp only [burnCall0World, Devm.getStor, Devm.getAcct, temporalAccountAccessBase_state]
        _ = (burnLockedWorld sevm b).getStor sevm.currentTarget := by
          rw [burnTokensWorld, afterSload_getStor, afterSload_getStor, burnReservedWorld,
            afterSload_getStor]
    rw [same]
    exact rep.burn_locked_world
  have req0 := balanceRequestMemory_ptr getterInitMemory_ptr sevm.currentTarget
  have reply0 := balanceReplyMemory_ptr env.d0.returnData req0
  have reply1 : PtrMem 128 192 (burnMem2 sevm env.d0 env.d1) :=
    balanceReplyMemory_ptr env.d1.returnData (balanceRequestMemory_ptr reply0 sevm.currentTarget)
  obtain ⟨nonzero0, nonzero1, feeRun⟩ := burnFeePricing_exact (len := env.d1.returnData.length.toB256)
    (discarded := 0) fork reply1 (by decide) d1Rep tracked nonstatic bound0 bound1 env.fee
    feeAccepted fresh priced positive0 positive1 burned
  have feeMem : PtrMem 128 192
      (feeReplyMemory (feeBurnMemory (burnMem2 sevm env.d0 env.d1) sevm.currentTarget)
        env.dF.returnData) :=
    feeReplyMemory_ptr env.dF.returnData (feeRequestMemory_ptr (feeBurnMemory_ptr reply1 sevm.currentTarget))
  have feeMachine := mintFeePost_machine (sevm := sevm) (b := feeKLastWorld sevm env.dF)
    (R := burnFeeLocalsAt sevm env.d1 (burnMem2 sevm env.d0 env.d1) (burnB0 env.d0) (burnT1 sevm b)
      (burnT0 sevm b) (burnR1 sevm b) (burnR0 sevm b) (burnRecipientWord sevm) 0x053d [0x89afcb44])
    (K := feeKLastWord sevm env.dF) (w := Bytes.toB256 (env.dF.returnData.take 32))
    (r0 := burnR0 sevm b) (r1 := burnR1 sevm b) (G := 0) feeMem
  have pricedMem : PtrMem 128 192 (burnBodyWorld sevm b env.d0 env.d1 env.dF).memory := by
    have image := lpMintMemory_ptr (lpMintScratch_ptr feeMachine.2 sevm.currentTarget.toB256)
      sevm.currentTarget.toB256 (feeBurnLiquidity sevm env.d1)
    rw [burnBodyWorld_def]
    simpa only [burnPricedWorld, burnFeeWorld, lpBurnPost, lpBurnBalancePost, lpBurnSupplyPost,
      St.memory, lpMintMemory] using image
  have pricedSentinel : memWord (burnBodyWorld sevm b env.d0 env.d1 env.dF).memory 96 = 0 := by
    rw [burnBodyWorld_def]
    exact (burnLP_sentinel feeMachine.2.wf).trans ((burnFeePost_sentinel feeMem.wf).trans
      ((burnFeeReply_sentinel (feeBurnMemory_ptr reply1 sevm.currentTarget).wf _).trans
      ((burnFeeScratch_sentinel reply1.wf sevm.currentTarget).trans
      ((burnBalanceReply_sentinel reply0.wf sevm.currentTarget _).trans
      ((burnBalanceReply_sentinel getterInitMemory_ptr.wf sevm.currentTarget _).trans
        burnEntryMemory_sentinel)))))
  obtain ⟨⟨n, memE, covered⟩, lower2, upper2, backRun⟩ := burnBack_exact helper fork pricedMem
    pricedSentinel (by decide) (by decide) nonzero0 nonzero1 (by decide) nonstatic env.back
    final0 final1
  have callee := burnInitial_exact fork (by decide) unlockedRaw nonstatic env.initial
    (feeRun _ (by rw [← burnBodyWorld_def]; exact backRun))
  have width : (burnSuffixPtr 128 env.back.d0 env.back.d1).toNat + 260 < 2 ^ 256 := by
    have : 2 ^ 163 + 260 < 2 ^ 256 := by decide
    omega
  have tail := burnAbiReturn_exact (sevm := sevm) (b := env.back.post) (G := g) (R := [0x89afcb44])
    (amount0 := (burnBodyWords sevm b env.d0 env.d1 env.dF).amount0)
    (amount1 := (burnBodyWords sevm b env.d0 env.d1 env.dF).amount1) memE lower2 width covered (by decide)
  have abi := burnAbi_exact guard callee tail
  rw [show env.initial.gas + 63 = (env.initial.gas + 20) + 43 by omega] at abi
  exact burnDispatch_exact value size selector abi

/-- **Burn forward schedule from pc zero.** From the nonpayable, size, ABI-length and selector
guards, the entry storage representing `current.state` with the Pair's LP row tracked, the
callee-only environment and the primitive guards at its actual answers, a successful pc-zero run of
the original bytes EXISTS with exact initial gas `env.gas`, halting with both amounts returned and
residual `g`.  That same run is the authenticated raw Burn frame (`burnRaw_source_authentic`) under
HASH-T over any universe holding its own trace and frames.
CROSS-HOST: conditional on `SwapSafeTransferForward`. -/
theorem burn_bytecode_forward_consumes {K : WriterKey → Prop} {current : Checkpoint}
    {pre : Nat → B256 → Nat} {post : Nat → B256 → Bytes → Nat}
    {sevm : Sevm} {b : Devm} {g : Nat}
    (invocation : List Nat) (helper : SwapSafeTransferForward pre post)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (tracked : K (.balance sevm.currentTarget))
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (env : BurnForwardEnv pre post sevm b g)
    (guards : BurnForwardGuards K current.state sevm b env.d0 env.d1 env.dF env.back.e0
      env.back.e1) :
    ∃ run : Exec 0 sevm (St b [] Mem.empty env.gas) (.ok env.post),
      ∀ {U : WriterKey → Prop}, WriterInj U → WriterApart U → (∀ k, K k → U k) →
        (∀ k ∈ mintTraceKeys ⟨0, sevm, St b [] Mem.empty env.gas, .ok env.post, run⟩, U k) →
        (∀ F ∈ Exec.rawFrameRoots run,
          F.sevm.currentTarget = sevm.currentTarget → LockedGood U F) →
        (∀ F ∈ Exec.rawFrameRoots run, F.sevm.currentTarget = sevm.currentTarget →
          ∀ k ∈ staticViewDecodedKeys F.sevm, U k) →
        BurnEntryAuthenticFinished U K current
          ⟨0, sevm, St b [] Mem.empty env.gas, .ok env.post, run⟩ b (.halted env.post)
          invocation := by
  obtain ⟨run⟩ := lift_exact cert_check jumps_ok codeEq fork
    ⟨t_0000_c0, rfl, burnPc0_exact helper fork value size guard selector rep tracked env guards⟩
  exact ⟨run, fun inj apart sub trace good staticGood =>
    burnRaw_source_authentic invocation codeEq fork selector rep tracked run inj apart sub trace
      sem image installed good staticGood⟩

end Blanc.Lift.UniswapV2Pair
