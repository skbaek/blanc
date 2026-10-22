import Blanc.Lift.Curve3Pool.RemoveLiquidityExactFrame
import Blanc.Lift.Curve3Pool.ExchangeExactLive
import Blanc.Lift.Curve3Pool.AddLiquidityExactFrame
import Blanc.Lift.Curve3Pool.RemoveLiquidityImbalanceExactFrame
import Blanc.Lift.Curve3Pool.OneCoinExactFrame

/-!
# `exchange` and `add_liquidity` across the static initial gas

The schedules of `remove_liquidity`, `remove_liquidity_imbalance` and `remove_liquidity_one_coin`
carry their own static-gas transports. Here: `exExactCost_withStaticGas` and
`alExactCost_withStaticGas` (the closed costs read no static gas, with the call data `P` and the
words fixed), `ALExactPremises.withStaticGas` (the same data `P`, each profile transported with
its functions unchanged), and the words the two frame theorems pin determine the cost
(`xpWords_unique`, `alExactCost_words_eq`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-! ## The closed costs read no static gas

Each stage function of `exExactCost` and `alExactCost` (and their bases, memories and successors)
is unchanged by the frame's static initial gas, with every other argument fixed; each is proved
by unfolding one level over its children's transports. -/

section StaticGas

theorem exPreLockBase_withStaticGas (sevm : Sevm) (F : Nat) (b : Devm) :
    exPreLockBase {sevm with gas := F} b =
      exPreLockBase sevm b := by
  simp only [exPreLockBase, afterSload_withStaticGas, afterSstore_withStaticGas]

theorem exPreCost_withStaticGas (sevm : Sevm) (F : Nat) (b : Devm) :
    exPreCost {sevm with gas := F} b =
      exPreCost sevm b := by
  simp only [exPreCost, exPreLockBase_withStaticGas, sloadCost_withStaticGas,
    sstoreCost_withStaticGas, afterSload_withStaticGas, afterSstore_withStaticGas]

theorem exPreBase_withStaticGas (sevm : Sevm) (F : Nat) (b : Devm) :
    exPreBase {sevm with gas := F} b =
      exPreBase sevm b := by
  simp only [exPreBase, exPreLockBase_withStaticGas, afterSload_withStaticGas]

theorem exI_withStaticGas (sevm : Sevm) (F : Nat) :
    exI {sevm with gas := F} =
      exI sevm := by
  simp only [exI, dataWord_withStaticGas]

theorem exHeadCost_withStaticGas (sevm : Sevm) (F : Nat) (pre : Devm) :
    exHeadCost {sevm with gas := F} pre =
      exHeadCost sevm pre := by
  simp only [exHeadCost, exPreCost_withStaticGas, exPreBase_withStaticGas, exI_withStaticGas,
    sloadCost_withStaticGas]

theorem exBalIn_withStaticGas (M : Mem) (sevm : Sevm) (F : Nat) (o : Nat) :
    exBalIn M {sevm with gas := F} o =
      exBalIn M sevm o := by
  simp only [exBalIn]

theorem exPullN1_withStaticGas (sevm : Sevm) (F : Nat) (n : Devm) (M : Mem) :
    exPullN1 {sevm with gas := F} n M =
      exPullN1 sevm n M := by
  simp only [exPullN1, identityCallNext_withStaticGas]

theorem exPullM2_withStaticGas (M : Mem) (sevm : Sevm) (F : Nat) :
    exPullM2 M {sevm with gas := F} =
      exPullM2 M sevm := by
  simp only [exPullM2, dataWord_withStaticGas]

theorem exPullN2_withStaticGas (sevm : Sevm) (F : Nat) (n : Devm) (M : Mem) :
    exPullN2 {sevm with gas := F} n M =
      exPullN2 sevm n M := by
  simp only [exPullN2, exPullN1_withStaticGas, exPullM2_withStaticGas,
    identityCallNext_withStaticGas]

theorem exPullI2_withStaticGas (M : Mem) (sevm : Sevm) (F : Nat) :
    exPullI2 M {sevm with gas := F} =
      exPullI2 M sevm := by
  simp only [exPullI2, exPullM2_withStaticGas]

theorem exPullNext_withStaticGas (sevm : Sevm) (F : Nat) (n : Devm) (M : Mem) (plN : Devm → List B256 → Mem → Devm) :
    exPullNext {sevm with gas := F} n M plN =
      exPullNext sevm n M plN := by
  simp only [exPullNext, exPullN2_withStaticGas, exPullI2_withStaticGas]

theorem exPullCost_withStaticGas (sevm : Sevm) (F : Nat) (n : Devm) (M : Mem) (c0 : Nat) (plD : Devm → List B256 → Mem → Nat) (plN : Devm → List B256 → Mem → Devm) :
    exPullCost {sevm with gas := F} n M c0 plD plN =
      exPullCost sevm n M c0 plD plN := by
  simp only [exPullCost, exPullN2_withStaticGas, exPullI2_withStaticGas,
    exPullNext_withStaticGas]

theorem exBal1Next_withStaticGas (sevm : Sevm) (F : Nat) (n : Devm) (M : Mem) (bN : Devm → List B256 → Mem → Devm) :
    exBal1Next {sevm with gas := F} n M bN =
      exBal1Next sevm n M bN := by
  simp only [exBal1Next, exBalIn_withStaticGas]

theorem exBal1Mem_withStaticGas (sevm : Sevm) (F : Nat) (n : Devm) (M : Mem) (B1 : B256) (bN : Devm → List B256 → Mem → Devm) :
    exBal1Mem {sevm with gas := F} n M B1 bN =
      exBal1Mem sevm n M B1 bN := by
  simp only [exBal1Mem, exBalIn_withStaticGas, exBal1Next_withStaticGas]

theorem exPullTail_withStaticGas (sevm : Sevm) (F : Nat) (n : Devm) (M : Mem) (plN : Devm → List B256 → Mem → Devm) :
    exPullTail {sevm with gas := F} n M plN =
      exPullTail sevm n M plN := by
  simp only [exPullTail, exPullNext_withStaticGas, rawTailBaseNext_withStaticGas]

theorem exPullMem_withStaticGas (sevm : Sevm) (F : Nat) (n : Devm) (M : Mem) (plN : Devm → List B256 → Mem → Devm) :
    exPullMem {sevm with gas := F} n M plN =
      exPullMem sevm n M plN := by
  simp only [exPullMem, exPullNext_withStaticGas]

theorem exFeeMidCost_withStaticGas (sevm : Sevm) (F : Nat) (n : Devm) (M : Mem) (B1 : B256) (bD1 : Devm → List B256 → Mem → Nat) (bN1 : Devm → List B256 → Mem → Devm) (plD : Devm → List B256 → Mem → Nat) (plN : Devm → List B256 → Mem → Devm) (bD2 : Devm → List B256 → Mem → Nat) :
    exFeeMidCost {sevm with gas := F} n M B1 bD1 bN1 plD plN bD2 =
      exFeeMidCost sevm n M B1 bD1 bN1 plD plN bD2 := by
  simp only [exFeeMidCost, exBalIn_withStaticGas, exPullCost_withStaticGas,
    exBal1Next_withStaticGas, exBal1Mem_withStaticGas, exPullTail_withStaticGas,
    exPullMem_withStaticGas]

theorem exN2_withStaticGas (sevm : Sevm) (F : Nat) (pre : Devm) :
    exN2 {sevm with gas := F} pre =
      exN2 sevm pre := by
  simp only [exN2, exPreBase_withStaticGas, exI_withStaticGas, afterSload_withStaticGas]

theorem exM0_withStaticGas (sevm : Sevm) (F : Nat) :
    exM0 {sevm with gas := F} =
      exM0 sevm := by
  simp only [exM0, dataWord_withStaticGas]

theorem exZ_withStaticGas (sevm : Sevm) (F : Nat) (o : Nat) :
    exZ {sevm with gas := F} o =
      exZ sevm o := by
  simp only [exZ, dataWord_withStaticGas]

theorem exDx_withStaticGas (sevm : Sevm) (F : Nat) :
    exDx {sevm with gas := F} =
      exDx sevm := by
  simp only [exDx, dataWord_withStaticGas]

theorem exM2_withStaticGas (sevm : Sevm) (F : Nat) (pre : Devm) (x0 : B256) (x1 : B256) (x2 : B256) :
    exM2 {sevm with gas := F} pre x0 x1 x2 =
      exM2 sevm pre x0 x1 x2 := by
  simp only [exM2, exM0_withStaticGas, exZ_withStaticGas, exDx_withStaticGas, exI_withStaticGas]

theorem aGas_withStaticGas (sevm : Sevm) (F : Nat) (b : Devm) :
    aGas {sevm with gas := F} b =
      aGas sevm b := by
  simp only [aGas, sloadCost_withStaticGas, afterSload_withStaticGas]

theorem costGetY_withStaticGas (sevm : Sevm) (F : Nat) (b : Devm) (amp : Nat) (i : Nat) (j : Nat) (x : Nat) (x0 : Nat) (x1 : Nat) (x2 : Nat) :
    costGetY {sevm with gas := F} b amp i j x x0 x1 x2 =
      costGetY sevm b amp i j x x0 x1 x2 := by
  simp only [costGetY, aGas_withStaticGas]

theorem exJ_withStaticGas (sevm : Sevm) (F : Nat) :
    exJ {sevm with gas := F} =
      exJ sevm := by
  simp only [exJ, dataWord_withStaticGas]

theorem exXw_withStaticGas (sevm : Sevm) (F : Nat) (X : Nat → B256) (D : B256) :
    exXw {sevm with gas := F} X D =
      exXw sevm X D := by
  simp only [exXw, exI_withStaticGas]

theorem exStoreCost_withStaticGas (sevm : Sevm) (F : Nat) (b : Devm) (vi : B256) (vj : B256) :
    exStoreCost {sevm with gas := F} b vi vj =
      exStoreCost sevm b vi vj := by
  simp only [exStoreCost, sloadCost_withStaticGas, sstoreCost_withStaticGas,
    afterSload_withStaticGas, dataWord_withStaticGas, afterSstore_withStaticGas]

theorem exVi_withStaticGas (sevm : Sevm) (F : Nat) (B : Nat → B256) (D : B256) :
    exVi {sevm with gas := F} B D =
      exVi sevm B D := by
  simp only [exVi, exI_withStaticGas]

theorem exVj_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (B : Nat → B256) (dyFee : B256) (dyOut : B256) :
    exVj {sevm with gas := F} σ B dyFee dyOut =
      exVj sevm σ B dyFee dyOut := by
  simp only [exVj, exJ_withStaticGas]

theorem exPushIn_withStaticGas (sevm : Sevm) (F : Nat) (n : Devm) :
    exPushIn {sevm with gas := F} n =
      exPushIn sevm n := by
  simp only [exPushIn, afterSload_withStaticGas, dataWord_withStaticGas]

theorem exPushNext_withStaticGas (sevm : Sevm) (F : Nat) (n : Devm) (M : Mem) (pN : Devm → List B256 → Mem → Devm) :
    exPushNext {sevm with gas := F} n M pN =
      exPushNext sevm n M pN := by
  simp only [exPushNext, exPushIn_withStaticGas]

theorem exPushCost_withStaticGas (sevm : Sevm) (F : Nat) (n : Devm) (M : Mem) (pD : Devm → List B256 → Mem → Nat) (pN : Devm → List B256 → Mem → Devm) :
    exPushCost {sevm with gas := F} n M pD pN =
      exPushCost sevm n M pD pN := by
  simp only [exPushCost, exPushIn_withStaticGas, exPushNext_withStaticGas,
    sloadCost_withStaticGas, dataWord_withStaticGas, sstoreCost_withStaticGas,
    rawTailBaseNext_withStaticGas]

theorem exStoreBase_withStaticGas (sevm : Sevm) (F : Nat) (b : Devm) (vi : B256) (vj : B256) :
    exStoreBase {sevm with gas := F} b vi vj =
      exStoreBase sevm b vi vj := by
  simp only [exStoreBase, afterSstore_withStaticGas, afterSload_withStaticGas,
    dataWord_withStaticGas]

theorem exStoreM1_withStaticGas (M : Mem) (sevm : Sevm) (F : Nat) (fee : B256) (af : B256) :
    exStoreM1 M {sevm with gas := F} fee af =
      exStoreM1 M sevm fee af := by
  simp only [exStoreM1, exJ_withStaticGas]

theorem exTailN1_withStaticGas (sevm : Sevm) (F : Nat) (n : Devm) (M : Mem) (σ : Stor) (B : Nat → B256) (D : B256) (dyFee : B256) (dyOut : B256) :
    exTailN1 {sevm with gas := F} n M σ B D dyFee dyOut =
      exTailN1 sevm n M σ B D dyFee dyOut := by
  simp only [exTailN1, exStoreBase_withStaticGas, exVi_withStaticGas, exVj_withStaticGas,
    exStoreM1_withStaticGas, identityCallNext_withStaticGas]

theorem exStoreI1_withStaticGas (M : Mem) (sevm : Sevm) (F : Nat) (fee : B256) (af : B256) :
    exStoreI1 M {sevm with gas := F} fee af =
      exStoreI1 M sevm fee af := by
  simp only [exStoreI1, exStoreM1_withStaticGas]

theorem exStoreM2_withStaticGas (M : Mem) (sevm : Sevm) (F : Nat) (fee : B256) (af : B256) (dy : B256) :
    exStoreM2 M {sevm with gas := F} fee af dy =
      exStoreM2 M sevm fee af dy := by
  simp only [exStoreM2, exStoreI1_withStaticGas]

theorem exTailN2_withStaticGas (sevm : Sevm) (F : Nat) (n : Devm) (M : Mem) (σ : Stor) (B : Nat → B256) (D : B256) (dyFee : B256) (dyOut : B256) :
    exTailN2 {sevm with gas := F} n M σ B D dyFee dyOut =
      exTailN2 sevm n M σ B D dyFee dyOut := by
  simp only [exTailN2, exTailN1_withStaticGas, exStoreM2_withStaticGas,
    identityCallNext_withStaticGas]

theorem exStoreI2_withStaticGas (M : Mem) (sevm : Sevm) (F : Nat) (fee : B256) (af : B256) (dy : B256) :
    exStoreI2 M {sevm with gas := F} fee af dy =
      exStoreI2 M sevm fee af dy := by
  simp only [exStoreI2, exStoreM2_withStaticGas]

theorem exTailCost_withStaticGas (sevm : Sevm) (F : Nat) (n : Devm) (M : Mem) (σ : Stor) (B : Nat → B256) (D : B256) (dyFee : B256) (dyOut : B256) (pD : Devm → List B256 → Mem → Nat) (pN : Devm → List B256 → Mem → Devm) :
    exTailCost {sevm with gas := F} n M σ B D dyFee dyOut pD pN =
      exTailCost sevm n M σ B D dyFee dyOut pD pN := by
  simp only [exTailCost, exStoreCost_withStaticGas, exVi_withStaticGas, exVj_withStaticGas,
    exPushCost_withStaticGas, exTailN2_withStaticGas, exStoreI2_withStaticGas]

theorem exYArgs_withStaticGas (M : Mem) (sevm : Sevm) (F : Nat) (xw : B256) (x0 : B256) (x1 : B256) (x2 : B256) :
    exYArgs M {sevm with gas := F} xw x0 x1 x2 =
      exYArgs M sevm xw x0 x1 x2 := by
  simp only [exYArgs, exI_withStaticGas, exJ_withStaticGas]

theorem exYMem_withStaticGas (M : Mem) (sevm : Sevm) (F : Nat) (xw : B256) (x0 : B256) (x1 : B256) (x2 : B256) (v : Nat) (w : Nat → B256) :
    exYMem M {sevm with gas := F} xw x0 x1 x2 v w =
      exYMem M sevm xw x0 x1 x2 v w := by
  simp only [exYMem, exYArgs_withStaticGas]

theorem exBackYMem_withStaticGas (sevm : Sevm) (F : Nat) (M : Mem) (X : Nat → B256) (D : B256) (v : Nat) :
    exBackYMem {sevm with gas := F} M X D v =
      exBackYMem sevm M X D v := by
  simp only [exBackYMem, exYMem_withStaticGas, exXw_withStaticGas]

theorem exBackDyMem_withStaticGas (sevm : Sevm) (F : Nat) (M : Mem) (σ : Stor) (X : Nat → B256) (D : B256) (v : Nat) :
    exBackDyMem {sevm with gas := F} M σ X D v =
      exBackDyMem sevm M σ X D v := by
  simp only [exBackDyMem, exBackYMem_withStaticGas, exJ_withStaticGas]

theorem exBackCost_withStaticGas (sevm : Sevm) (F : Nat) (n : Devm) (M : Mem) (c0 : Nat) (σ : Stor) (B : Nat → B256) (X : Nat → B256) (D : B256) (amp : Nat) (v : Nat) (pD : Devm → List B256 → Mem → Nat) (pN : Devm → List B256 → Mem → Devm) :
    exBackCost {sevm with gas := F} n M c0 σ B X D amp v pD pN =
      exBackCost sevm n M c0 σ B X D amp v pD pN := by
  simp only [exBackCost, costGetY_withStaticGas, exI_withStaticGas, exJ_withStaticGas,
    exXw_withStaticGas, exTailCost_withStaticGas, exBackDyMem_withStaticGas,
    sloadCost_withStaticGas, aBase_withStaticGas, afterSload_withStaticGas]

theorem exBal2Next_withStaticGas (sevm : Sevm) (F : Nat) (n : Devm) (M : Mem) (bN : Devm → List B256 → Mem → Devm) :
    exBal2Next {sevm with gas := F} n M bN =
      exBal2Next sevm n M bN := by
  simp only [exBal2Next, exBalIn_withStaticGas]

theorem exBal2Mem_withStaticGas (sevm : Sevm) (F : Nat) (n : Devm) (M : Mem) (B1 : B256) (B2 : B256) (bN : Devm → List B256 → Mem → Devm) :
    exBal2Mem {sevm with gas := F} n M B1 B2 bN =
      exBal2Mem sevm n M B1 B2 bN := by
  simp only [exBal2Mem, exBalIn_withStaticGas, exBal2Next_withStaticGas]

theorem exFeeBackCost_withStaticGas (sevm : Sevm) (F : Nat) (pre : Devm) (P : ExchangeExactCalls) (x0 : B256) (x1 : B256) (x2 : B256) (B1 : B256) (B2 : B256) (amp : Nat) (v : Nat) :
    exFeeBackCost {sevm with gas := F} pre P x0 x1 x2 B1 B2 amp v =
      exFeeBackCost sevm pre P x0 x1 x2 B1 B2 amp v := by
  simp only [exFeeBackCost, exBackCost_withStaticGas, exBal2Next_withStaticGas,
    exPullTail_withStaticGas, exBal1Next_withStaticGas, exN2_withStaticGas, exM2_withStaticGas,
    exBal1Mem_withStaticGas, exPullMem_withStaticGas, exBal2Mem_withStaticGas]

theorem exNoFeeBackCost_withStaticGas (sevm : Sevm) (F : Nat) (pre : Devm) (P : ExchangeExactCalls) (x0 : B256) (x1 : B256) (x2 : B256) (amp : Nat) (v : Nat) :
    exNoFeeBackCost {sevm with gas := F} pre P x0 x1 x2 amp v =
      exNoFeeBackCost sevm pre P x0 x1 x2 amp v := by
  simp only [exNoFeeBackCost, exBackCost_withStaticGas, exPullTail_withStaticGas,
    exN2_withStaticGas, exM2_withStaticGas, exPullMem_withStaticGas, exDx_withStaticGas]

theorem exExactCost_withStaticGas (sevm : Sevm) (F : Nat) (pre : Devm) (P : ExchangeExactCalls) (x0 : B256) (x1 : B256) (x2 : B256) (B1 : B256) (B2 : B256) (amp : Nat) (v : Nat) :
    exExactCost {sevm with gas := F} pre P x0 x1 x2 B1 B2 amp v =
      exExactCost sevm pre P x0 x1 x2 B1 B2 amp v := by
  simp only [exExactCost, exHeadCost_withStaticGas, exI_withStaticGas,
    exFeeMidCost_withStaticGas, exN2_withStaticGas, exM2_withStaticGas,
    exFeeBackCost_withStaticGas, exPullCost_withStaticGas, exNoFeeBackCost_withStaticGas]

theorem alPreBaseA_withStaticGas (sevm : Sevm) (F : Nat) (b : Devm) :
    alPreBaseA {sevm with gas := F} b =
      alPreBaseA sevm b := by
  simp only [alPreBaseA, afterSload_withStaticGas, afterSstore_withStaticGas]

theorem alPreCost1_withStaticGas (sevm : Sevm) (F : Nat) (b : Devm) :
    alPreCost1 {sevm with gas := F} b =
      alPreCost1 sevm b := by
  simp only [alPreCost1, aGas_withStaticGas, alPreBaseA_withStaticGas, sloadCost_withStaticGas,
    sstoreCost_withStaticGas, afterSload_withStaticGas, afterSstore_withStaticGas,
    aBase_withStaticGas]

theorem alSupBase_withStaticGas (sevm : Sevm) (F : Nat) (b : Devm) :
    alSupBase {sevm with gas := F} b =
      alSupBase sevm b := by
  simp only [alSupBase, alPreBaseA_withStaticGas, afterSload_withStaticGas, aBase_withStaticGas]

theorem aMemNext_withStaticGas (sevm : Sevm) (F : Nat) (b : Devm) (M : Mem) (ret : B256) (w : B256) :
    aMemNext {sevm with gas := F} b M ret w =
      aMemNext sevm b M ret w := by
  simp only [aMemNext]

theorem alSupMem_withStaticGas (sevm : Sevm) (F : Nat) (b : Devm) (M : Mem) (σ : Stor) (amp : Nat) :
    alSupMem {sevm with gas := F} b M σ amp =
      alSupMem sevm b M σ amp := by
  simp only [alSupMem, aMemNext_withStaticGas, alPreBaseA_withStaticGas]

theorem alMv_withStaticGas (sevm : Sevm) (F : Nat) :
    alMv {sevm with gas := F} =
      alMv sevm := by
  simp only [alMv, dataWord_withStaticGas]

theorem alPreCost2_withStaticGas (sevm : Sevm) (F : Nat) (d : Devm) :
    alPreCost2 {sevm with gas := F} d =
      alPreCost2 sevm d := by
  simp only [alPreCost2, sloadCost_withStaticGas, afterSload_withStaticGas]

theorem alSupNext_withStaticGas (sevm : Sevm) (F : Nat) (pre : Devm) (P : ALExactCalls) (amp : Nat) :
    alSupNext {sevm with gas := F} pre P amp =
      alSupNext sevm pre P amp := by
  simp only [alSupNext, alSupBase_withStaticGas, alSupMem_withStaticGas, alMv_withStaticGas]

theorem alFrontCost_withStaticGas (sevm : Sevm) (F : Nat) (pre : Devm) (P : ALExactCalls) (amp : Nat) :
    alFrontCost {sevm with gas := F} pre P amp =
      alFrontCost sevm pre P amp := by
  simp only [alFrontCost, alPreCost1_withStaticGas, alSupBase_withStaticGas,
    alSupMem_withStaticGas, alMv_withStaticGas, alPreCost2_withStaticGas,
    alSupNext_withStaticGas]

theorem alAmt_withStaticGas (sevm : Sevm) (F : Nat) (i : Nat) :
    alAmt {sevm with gas := F} i =
      alAmt sevm i := by
  simp only [alAmt, dataWord_withStaticGas]

theorem alHeadCost_withStaticGas (sevm : Sevm) (F : Nat) (b : Devm) (i : Nat) (T : B256) :
    alHeadCost {sevm with gas := F} b i T =
      alHeadCost sevm b i T := by
  simp only [alHeadCost, sloadCost_withStaticGas]

theorem alHeadCostX_withStaticGas (sevm : Sevm) (F : Nat) (n : Devm) (k : Nat) (T : B256) :
    alHeadCostX {sevm with gas := F} n k T =
      alHeadCostX sevm n k T := by
  simp only [alHeadCostX, alHeadCost_withStaticGas, sloadCost_withStaticGas]

theorem alSkipCost_withStaticGas (sevm : Sevm) (F : Nat) (n : Devm) (k : Nat) (T : B256) :
    alSkipCost {sevm with gas := F} n k T =
      alSkipCost sevm n k T := by
  simp only [alSkipCost, alHeadCostX_withStaticGas]

theorem alHB_withStaticGas (sevm : Sevm) (F : Nat) (n : Devm) (k : Nat) :
    alHB {sevm with gas := F} n k =
      alHB sevm n k := by
  simp only [alHB, afterSload_withStaticGas]

theorem alBalMem_withStaticGas (sevm : Sevm) (F : Nat) (M : Mem) (o : Nat) :
    alBalMem {sevm with gas := F} M o =
      alBalMem sevm M o := by
  simp only [alBalMem]

theorem alHeadMem_withStaticGas (sevm : Sevm) (F : Nat) (M : Mem) (σ : Stor) (i : Nat) :
    alHeadMem {sevm with gas := F} M σ i =
      alHeadMem sevm M σ i := by
  simp only [alHeadMem, dataWord_withStaticGas]

theorem alFeeMemB_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (m : Mem) :
    alFeeMemB {sevm with gas := F} σ m =
      alFeeMemB sevm σ m := by
  simp only [alFeeMemB, alBalMem_withStaticGas, alHeadMem_withStaticGas]

theorem alPullId1_withStaticGas (sevm : Sevm) (F : Nat) (b : Devm) (S : List B256) (M : Mem) :
    alPullId1 {sevm with gas := F} b S M =
      alPullId1 sevm b S M := by
  simp only [alPullId1, identityCallNext_withStaticGas]

theorem alPullMem2_withStaticGas (sevm : Sevm) (F : Nat) (M : Mem) (i : Nat) :
    alPullMem2 {sevm with gas := F} M i =
      alPullMem2 sevm M i := by
  simp only [alPullMem2, dataWord_withStaticGas]

theorem alPullId2_withStaticGas (sevm : Sevm) (F : Nat) (b : Devm) (S : List B256) (M : Mem) (i : Nat) :
    alPullId2 {sevm with gas := F} b S M i =
      alPullId2 sevm b S M i := by
  simp only [alPullId2, alPullId1_withStaticGas, alPullMem2_withStaticGas,
    identityCallNext_withStaticGas]

theorem alFeeCallB_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (P : ALExactCalls) (n : Devm) (m : Mem) :
    alFeeCallB {sevm with gas := F} σ P n m =
      alFeeCallB sevm σ P n m := by
  simp only [alFeeCallB, alHB_withStaticGas, alFeeMemB_withStaticGas]

theorem alFeeMemP_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (P : ALExactCalls) (n : Devm) (m : Mem) (B1 : B256) :
    alFeeMemP {sevm with gas := F} σ P n m B1 =
      alFeeMemP sevm σ P n m B1 := by
  simp only [alFeeMemP, alFeeMemB_withStaticGas, alFeeCallB_withStaticGas]

theorem alPullMemC_withStaticGas (sevm : Sevm) (F : Nat) (M : Mem) (i : Nat) :
    alPullMemC {sevm with gas := F} M i =
      alPullMemC sevm M i := by
  simp only [alPullMemC, alPullMem2_withStaticGas]

theorem alFeeCallP_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (P : ALExactCalls) (n : Devm) (m : Mem) (B1 : B256) :
    alFeeCallP {sevm with gas := F} σ P n m B1 =
      alFeeCallP sevm σ P n m B1 := by
  simp only [alFeeCallP, alPullId2_withStaticGas, alFeeCallB_withStaticGas,
    alFeeMemP_withStaticGas, alPullMemC_withStaticGas]

theorem alFeeLen_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (P : ALExactCalls) (n : Devm) (m : Mem) (B1 : B256) :
    alFeeLen {sevm with gas := F} σ P n m B1 =
      alFeeLen sevm σ P n m B1 := by
  simp only [alFeeLen, alFeeCallP_withStaticGas]

theorem alFeeBaseR_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (P : ALExactCalls) (n : Devm) (m : Mem) (B1 : B256) :
    alFeeBaseR {sevm with gas := F} σ P n m B1 =
      alFeeBaseR sevm σ P n m B1 := by
  simp only [alFeeBaseR, alFeeCallP_withStaticGas, rawTailBaseNext_withStaticGas]

theorem alFeeMemR_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (P : ALExactCalls) (n : Devm) (m : Mem) (B1 : B256) :
    alFeeMemR {sevm with gas := F} σ P n m B1 =
      alFeeMemR sevm σ P n m B1 := by
  simp only [alFeeMemR, alFeeCallP_withStaticGas, alFeeLen_withStaticGas]

theorem alFeeMemA_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (P : ALExactCalls) (n : Devm) (m : Mem) (B1 : B256) :
    alFeeMemA {sevm with gas := F} σ P n m B1 =
      alFeeMemA sevm σ P n m B1 := by
  simp only [alFeeMemA, alBalMem_withStaticGas, alFeeMemR_withStaticGas]

theorem alFeeCost_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (P : ALExactCalls) (n : Devm) (m : Mem) (B1 : B256) (T : B256) (p : Bool) :
    alFeeCost {sevm with gas := F} σ P n m B1 T p =
      alFeeCost sevm σ P n m B1 T p := by
  simp only [alFeeCost, alHeadCostX_withStaticGas, alHB_withStaticGas, alFeeMemB_withStaticGas,
    alPullId2_withStaticGas, alFeeCallB_withStaticGas, alFeeMemP_withStaticGas,
    alPullMemC_withStaticGas, alFeeLen_withStaticGas, alFeeBaseR_withStaticGas,
    alFeeMemA_withStaticGas]

theorem alPlainCall_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (P : ALExactCalls) (n : Devm) (m : Mem) (k : Nat) :
    alPlainCall {sevm with gas := F} σ P n m k =
      alPlainCall sevm σ P n m k := by
  simp only [alPlainCall, alPullId2_withStaticGas, alHB_withStaticGas, alHeadMem_withStaticGas,
    alPullMemC_withStaticGas]

theorem alPlainLen_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (P : ALExactCalls) (n : Devm) (m : Mem) (k : Nat) :
    alPlainLen {sevm with gas := F} σ P n m k =
      alPlainLen sevm σ P n m k := by
  simp only [alPlainLen, alPlainCall_withStaticGas]

theorem alPlainCost_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (P : ALExactCalls) (n : Devm) (m : Mem) (k : Nat) (T : B256) (p : Bool) :
    alPlainCost {sevm with gas := F} σ P n m k T p =
      alPlainCost sevm σ P n m k T p := by
  simp only [alPlainCost, alHeadCostX_withStaticGas, alPullId2_withStaticGas, alHB_withStaticGas,
    alHeadMem_withStaticGas, alPullMemC_withStaticGas, alPlainLen_withStaticGas]

theorem alItCost_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (P : ALExactCalls) (n : Devm) (m : Mem) (k : Nat) (B1 : B256) (T : B256) (p : Bool) :
    alItCost {sevm with gas := F} σ P n m k B1 T p =
      alItCost sevm σ P n m k B1 T p := by
  simp only [alItCost, alAmt_withStaticGas, alSkipCost_withStaticGas, alFeeCost_withStaticGas,
    alPlainCost_withStaticGas]

theorem alFeeBase_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (P : ALExactCalls) (n : Devm) (m : Mem) (B1 : B256) :
    alFeeBase {sevm with gas := F} σ P n m B1 =
      alFeeBase sevm σ P n m B1 := by
  simp only [alFeeBase, alFeeBaseR_withStaticGas, alFeeMemA_withStaticGas]

theorem alPlainBase_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (P : ALExactCalls) (n : Devm) (m : Mem) (k : Nat) :
    alPlainBase {sevm with gas := F} σ P n m k =
      alPlainBase sevm σ P n m k := by
  simp only [alPlainBase, alPlainCall_withStaticGas, rawTailBaseNext_withStaticGas]

theorem alItBase_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (P : ALExactCalls) (n : Devm) (m : Mem) (k : Nat) (B1 : B256) :
    alItBase {sevm with gas := F} σ P n m k B1 =
      alItBase sevm σ P n m k B1 := by
  simp only [alItBase, alAmt_withStaticGas, alHB_withStaticGas, alFeeBase_withStaticGas,
    alPlainBase_withStaticGas]

theorem alLN1_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (P : ALExactCalls) (n : Devm) (m : Mem) (B1 : B256) (old : Nat → B256) :
    alLN1 {sevm with gas := F} σ P n m B1 old =
      alLN1 sevm σ P n m B1 old := by
  simp only [alLN1, alItBase_withStaticGas]

theorem alSkipMem_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (m : Mem) (k : Nat) (old : Nat → B256) :
    alSkipMem {sevm with gas := F} σ m k old =
      alSkipMem sevm σ m k old := by
  simp only [alSkipMem, alHeadMem_withStaticGas, alAmt_withStaticGas]

theorem alFeeMem_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (P : ALExactCalls) (n : Devm) (m : Mem) (B1 : B256) (B2 : B256) (old : Nat → B256) :
    alFeeMem {sevm with gas := F} σ P n m B1 B2 old =
      alFeeMem sevm σ P n m B1 B2 old := by
  simp only [alFeeMem, alFeeMemA_withStaticGas, alFeeBase_withStaticGas]

theorem alPlainMem_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (P : ALExactCalls) (n : Devm) (m : Mem) (k : Nat) (old : Nat → B256) :
    alPlainMem {sevm with gas := F} σ P n m k old =
      alPlainMem sevm σ P n m k old := by
  simp only [alPlainMem, alPlainCall_withStaticGas, alPlainLen_withStaticGas,
    alAmt_withStaticGas]

theorem alItMem_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (P : ALExactCalls) (n : Devm) (m : Mem) (k : Nat) (B1 : B256) (B2 : B256) (old : Nat → B256) :
    alItMem {sevm with gas := F} σ P n m k B1 B2 old =
      alItMem sevm σ P n m k B1 B2 old := by
  simp only [alItMem, alAmt_withStaticGas, alSkipMem_withStaticGas, alFeeMem_withStaticGas,
    alPlainMem_withStaticGas]

theorem alLM1_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (P : ALExactCalls) (n : Devm) (m : Mem) (B1 : B256) (B2 : B256) (old : Nat → B256) :
    alLM1 {sevm with gas := F} σ P n m B1 B2 old =
      alLM1 sevm σ P n m B1 B2 old := by
  simp only [alLM1, alItMem_withStaticGas]

theorem alLN2_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (P : ALExactCalls) (n : Devm) (m : Mem) (B1 : B256) (B2 : B256) (old : Nat → B256) :
    alLN2 {sevm with gas := F} σ P n m B1 B2 old =
      alLN2 sevm σ P n m B1 B2 old := by
  simp only [alLN2, alItBase_withStaticGas, alLN1_withStaticGas, alLM1_withStaticGas]

theorem alLM2_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (P : ALExactCalls) (n : Devm) (m : Mem) (B1 : B256) (B2 : B256) (old : Nat → B256) :
    alLM2 {sevm with gas := F} σ P n m B1 B2 old =
      alLM2 sevm σ P n m B1 B2 old := by
  simp only [alLM2, alItMem_withStaticGas, alLN1_withStaticGas, alLM1_withStaticGas]

theorem alLoopCost_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (P : ALExactCalls) (n : Devm) (m : Mem) (B1 : B256) (B2 : B256) (T : B256) (old : Nat → B256) :
    alLoopCost {sevm with gas := F} σ P n m B1 B2 T old =
      alLoopCost sevm σ P n m B1 B2 T old := by
  simp only [alLoopCost, alItCost_withStaticGas, alLN1_withStaticGas, alLM1_withStaticGas,
    alAmt_withStaticGas, alLN2_withStaticGas, alLM2_withStaticGas]

theorem alPreBase2_withStaticGas (sevm : Sevm) (F : Nat) (d : Devm) :
    alPreBase2 {sevm with gas := F} d =
      alPreBase2 sevm d := by
  simp only [alPreBase2, afterSload_withStaticGas]

theorem alFN1_withStaticGas (sevm : Sevm) (F : Nat) (pre : Devm) (P : ALExactCalls) (amp : Nat) :
    alFN1 {sevm with gas := F} pre P amp =
      alFN1 sevm pre P amp := by
  simp only [alFN1, alPreBase2_withStaticGas, alSupNext_withStaticGas]

theorem alFM1_withStaticGas (sevm : Sevm) (F : Nat) (pre : Devm) (P : ALExactCalls) (amp : Nat) (T : B256) :
    alFM1 {sevm with gas := F} pre P amp T =
      alFM1 sevm pre P amp T := by
  simp only [alFM1, alSupMem_withStaticGas, alMv_withStaticGas, alSupNext_withStaticGas]

theorem alStore0Cost_withStaticGas (sevm : Sevm) (F : Nat) (b : Devm) (n : Nat → B256) :
    alStore0Cost {sevm with gas := F} b n =
      alStore0Cost sevm b n := by
  simp only [alStore0Cost, sstoreCost_withStaticGas, afterSstore_withStaticGas]

theorem alMintMem_withStaticGas (sevm : Sevm) (F : Nat) (M : Mem) (mint : B256) :
    alMintMem {sevm with gas := F} M mint =
      alMintMem sevm M mint := by
  simp only [alMintMem]

theorem alTailCost_withStaticGas (sevm : Sevm) (F : Nat) (P : ALExactCalls) (n : Devm) (M : Mem) (mint : B256) :
    alTailCost {sevm with gas := F} P n M mint =
      alTailCost sevm P n M mint := by
  simp only [alTailCost, alMintMem_withStaticGas, sloadCost_withStaticGas,
    afterSload_withStaticGas, sstoreCost_withStaticGas]

theorem alStore0Base_withStaticGas (sevm : Sevm) (F : Nat) (b : Devm) (n : Nat → B256) :
    alStore0Base {sevm with gas := F} b n =
      alStore0Base sevm b n := by
  simp only [alStore0Base, afterSstore_withStaticGas]

theorem alBack0Cost_withStaticGas (sevm : Sevm) (F : Nat) (P : ALExactCalls) (n : Devm) (M : Mem) (c0 : Nat) (A : B256) (nv : Nat → B256) (xb : V3) (v1 : Nat) :
    alBack0Cost {sevm with gas := F} P n M c0 A nv xb v1 =
      alBack0Cost sevm P n M c0 A nv xb v1 := by
  simp only [alBack0Cost, alStore0Cost_withStaticGas, alTailCost_withStaticGas,
    alStore0Base_withStaticGas]

theorem alLN3_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (P : ALExactCalls) (n : Devm) (m : Mem) (B1 : B256) (B2 : B256) (old : Nat → B256) :
    alLN3 {sevm with gas := F} σ P n m B1 B2 old =
      alLN3 sevm σ P n m B1 B2 old := by
  simp only [alLN3, alItBase_withStaticGas, alLN2_withStaticGas, alLM2_withStaticGas]

theorem alLM3_withStaticGas (sevm : Sevm) (F : Nat) (σ : Stor) (P : ALExactCalls) (n : Devm) (m : Mem) (B1 : B256) (B2 : B256) (old : Nat → B256) :
    alLM3 {sevm with gas := F} σ P n m B1 B2 old =
      alLM3 sevm σ P n m B1 B2 old := by
  simp only [alLM3, alItMem_withStaticGas, alLN2_withStaticGas, alLM2_withStaticGas]

theorem alD1c0_withStaticGas (sevm : Sevm) (F : Nat) :
    alD1c0 {sevm with gas := F} =
      alD1c0 sevm := by
  simp only [alD1c0, alAmt_withStaticGas]

theorem alCr2_withStaticGas (sevm : Sevm) (F : Nat) (B1 : B256) (B2 : B256) :
    alCr2 {sevm with gas := F} B1 B2 =
      alCr2 sevm B1 B2 := by
  simp only [alCr2, alAmt_withStaticGas]

theorem alLiveNew_withStaticGas (sevm : Sevm) (F : Nat) (old : Nat → B256) (B1 : B256) (B2 : B256) (a : Nat) :
    alLiveNew {sevm with gas := F} old B1 B2 a =
      alLiveNew sevm old B1 B2 a := by
  simp only [alLiveNew, alAmt_withStaticGas, alCr2_withStaticGas]

/-- `alLiveNew` as a function of the coin index. -/
theorem alLiveNew_fun_withStaticGas (sevm : Sevm) (F : Nat) (old : Nat → B256) (B1 B2 : B256) :
    alLiveNew {sevm with gas := F} old B1 B2 = alLiveNew sevm old B1 B2 :=
  funext (alLiveNew_withStaticGas sevm F old B1 B2)

theorem alExactCost0_withStaticGas (sevm : Sevm) (F : Nat) (pre : Devm) (P : ALExactCalls) (amp : Nat) (B1 : B256) (B2 : B256) (xb : V3) (v1 : Nat) :
    alExactCost0 {sevm with gas := F} pre P amp B1 B2 xb v1 =
      alExactCost0 sevm pre P amp B1 B2 xb v1 := by
  simp only [alLiveNew_fun_withStaticGas, alExactCost0, alFrontCost_withStaticGas, alLoopCost_withStaticGas,
    alFN1_withStaticGas, alFM1_withStaticGas, alBack0Cost_withStaticGas, alLN3_withStaticGas,
    alLM3_withStaticGas, alD1c0_withStaticGas]

theorem alFM0_withStaticGas (sevm : Sevm) (F : Nat) (pre : Devm) (P : ALExactCalls) (amp : Nat) (T : B256) (xa : V3) (v0 : Nat) :
    alFM0 {sevm with gas := F} pre P amp T xa v0 =
      alFM0 sevm pre P amp T xa v0 := by
  simp only [alFM0, alFM1_withStaticGas]

theorem alFeeLoopCost_withStaticGas (sevm : Sevm) (F : Nat) (n : Devm) (D0 : B256) (D1 : B256) (old : Nat → B256) (nv : Nat → B256) (s0 : B256) (s1 : B256) (s2 : B256) :
    alFeeLoopCost {sevm with gas := F} n D0 D1 old nv s0 s1 s2 =
      alFeeLoopCost sevm n D0 D1 old nv s0 s1 s2 := by
  simp only [alFeeLoopCost, sstoreCost_withStaticGas, afterSstore_withStaticGas]

theorem alFeeLoopBase_withStaticGas (sevm : Sevm) (F : Nat) (n : Devm) (s0 : B256) (s1 : B256) (s2 : B256) :
    alFeeLoopBase {sevm with gas := F} n s0 s1 s2 =
      alFeeLoopBase sevm n s0 s1 s2 := by
  simp only [alFeeLoopBase, afterSstore_withStaticGas]

theorem alBack1Cost_withStaticGas (sevm : Sevm) (F : Nat) (P : ALExactCalls) (n : Devm) (M : Mem) (c0 : Nat) (A : B256) (D0 : B256) (T : B256) (old : Nat → B256) (nv : Nat → B256) (xb : V3) (xc : V3) (v1 : Nat) (v2 : Nat) (f0 : B256) (f1 : B256) (f2 : B256) (s0 : B256) (s1 : B256) (s2 : B256) (x0 : B256) (x1 : B256) (x2 : B256) :
    alBack1Cost {sevm with gas := F} P n M c0 A D0 T old nv xb xc v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2 =
      alBack1Cost sevm P n M c0 A D0 T old nv xb xc v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2 := by
  simp only [alBack1Cost, alFeeLoopCost_withStaticGas, alTailCost_withStaticGas,
    alFeeLoopBase_withStaticGas]

theorem alExactCost1_withStaticGas (sevm : Sevm) (F : Nat) (pre : Devm) (P : ALExactCalls) (amp : Nat) (T : B256) (B1 : B256) (B2 : B256) (xa : V3) (xb : V3) (xc : V3) (v0 : Nat) (v1 : Nat) (v2 : Nat) (f0 : B256) (f1 : B256) (f2 : B256) (s0 : B256) (s1 : B256) (s2 : B256) (x0 : B256) (x1 : B256) (x2 : B256) :
    alExactCost1 {sevm with gas := F} pre P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2 =
      alExactCost1 sevm pre P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2 := by
  simp only [alLiveNew_fun_withStaticGas, alExactCost1, alFrontCost_withStaticGas, alLoopCost_withStaticGas,
    alFN1_withStaticGas, alFM0_withStaticGas, alBack1Cost_withStaticGas, alLN3_withStaticGas,
    alLM3_withStaticGas, alD1c0_withStaticGas]

theorem alExactCost_withStaticGas (sevm : Sevm) (F : Nat) (pre : Devm) (P : ALExactCalls) (amp : Nat) (T : B256) (B1 : B256) (B2 : B256) (xa : V3) (xb : V3) (xc : V3) (v0 : Nat) (v1 : Nat) (v2 : Nat) (f0 : B256) (f1 : B256) (f2 : B256) (s0 : B256) (s1 : B256) (s2 : B256) (x0 : B256) (x1 : B256) (x2 : B256) :
    alExactCost {sevm with gas := F} pre P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2 =
      alExactCost sevm pre P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2 := by
  simp only [alExactCost, alExactCost0_withStaticGas, alExactCost1_withStaticGas]

end StaticGas

/-- `add_liquidity`'s exact premises survive a change of static initial gas, with the same
data `P`. -/
theorem ALExactPremises.withStaticGas {sevm : Sevm} {σ : Stor} {T B1 B2 mint : B256}
    {W : Nat → Devm → Prop} {U : Nat} {P : ALExactCalls}
    (h : ALExactPremises sevm σ T B1 B2 mint W U P) (F : Nat) :
    ALExactPremises {sevm with gas := F} σ T B1 B2 mint W U P :=
  ⟨h.supply.withStaticGas F, fun k hk hz => (h.pull k hk hz).withStaticGas F,
    fun hz => (h.balB hz).withStaticGas F, fun hz => (h.balA hz).withStaticGas F,
    h.mint.withStaticGas F⟩

/-! ## The pinned words are unique -/

/-- `remove_liquidity_imbalance`'s word pinning reads no static gas. -/
theorem RliWordsPin.ofStaticGas {sevm : Sevm} {F : Nat} {pre : Devm} {s : State} {w : RliWords}
    (h : RliWordsPin {sevm with gas := F} pre s w) : RliWordsPin sevm pre s w := h

/-- Three words a checked `_xp` answer pins, as `toNat`s, are unique. -/
theorem xpWords_unique {X : Option V3} {x0 x1 x2 y0 y1 y2 : B256}
    (h : X = some ⟨x0.toNat, x1.toNat, x2.toNat⟩) (h' : X = some ⟨y0.toNat, y1.toNat, y2.toNat⟩) :
    x0 = y0 ∧ x1 = y1 ∧ x2 = y2 := by
  have e := Option.some.inj (h.symm.trans h')
  simp only [V3.mk.injEq] at e
  exact ⟨B256.toNat_inj _ _ e.1, B256.toNat_inj _ _ e.2.1, B256.toNat_inj _ _ e.2.2⟩

/-- **`add_liquidity`'s closed cost is pinned by the model's checks**: two witnesses of
`addLiquidity_live_exact`'s checks give the same `alExactCost` (on a first deposit it reads only
`amp`, `xb` and `v1`; on a positive supply every word is pinned). -/
theorem alExactCost_words_eq {sevm : Sevm} {pre : Devm} {P : ALExactCalls} {T B1 B2 : B256}
    {A : Option Nat} {XA XB : Option V3} {F AF n0 n1 n2 b0 b1 b2 : B256}
    {amp v0 v1 v2 amp' v0' v1' v2' : Nat} {xa xb xc xa' xb' xc' : V3}
    {f0 f1 f2 s0 s1 s2 x0 x1 x2 f0' f1' f2' s0' s1' s2' x0' x1' x2' : B256}
    (hA : A = some amp) (hXb : XB = some xb) (hD1 : getDChk xb.get amp 1 = some v1)
    (hT : T ≠ 0 → XA = some xa ∧ getDChk xa.get amp 1 = some v0 ∧
      RliFeeIter F AF (Nat.toB256 v0) (Nat.toB256 v1) b0 n0 f0 s0 x0 ∧
      RliFeeIter F AF (Nat.toB256 v0) (Nat.toB256 v1) b1 n1 f1 s1 x1 ∧
      RliFeeIter F AF (Nat.toB256 v0) (Nat.toB256 v1) b2 n2 f2 s2 x2 ∧
      xpChk ⟨x0.toNat, x1.toNat, x2.toNat⟩ = some xc ∧ getDChk xc.get amp 1 = some v2)
    (hA' : A = some amp') (hXb' : XB = some xb') (hD1' : getDChk xb'.get amp' 1 = some v1')
    (hT' : T ≠ 0 → XA = some xa' ∧ getDChk xa'.get amp' 1 = some v0' ∧
      RliFeeIter F AF (Nat.toB256 v0') (Nat.toB256 v1') b0 n0 f0' s0' x0' ∧
      RliFeeIter F AF (Nat.toB256 v0') (Nat.toB256 v1') b1 n1 f1' s1' x1' ∧
      RliFeeIter F AF (Nat.toB256 v0') (Nat.toB256 v1') b2 n2 f2' s2' x2' ∧
      xpChk ⟨x0'.toNat, x1'.toNat, x2'.toNat⟩ = some xc' ∧ getDChk xc'.get amp' 1 = some v2') :
    alExactCost sevm pre P amp' T B1 B2 xa' xb' xc' v0' v1' v2' f0' f1' f2' s0' s1' s2' x0' x1'
      x2' = alExactCost sevm pre P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2 := by
  obtain rfl : amp = amp' := Option.some.inj (hA.symm.trans hA')
  obtain rfl : xb = xb' := Option.some.inj (hXb.symm.trans hXb')
  obtain rfl : v1 = v1' := Option.some.inj (hD1.symm.trans hD1')
  by_cases hT0 : T = 0
  · unfold alExactCost
    rw [ite_eq_left hT0, ite_eq_left hT0]
  · obtain ⟨hXa, hD0, i0, i1, i2, hXc, hD2⟩ := hT hT0
    obtain ⟨hXa', hD0', i0', i1', i2', hXc', hD2'⟩ := hT' hT0
    obtain rfl : xa = xa' := Option.some.inj (hXa.symm.trans hXa')
    obtain rfl : v0 = v0' := Option.some.inj (hD0.symm.trans hD0')
    obtain ⟨rfl, rfl, rfl⟩ := i0.unique i0'
    obtain ⟨rfl, rfl, rfl⟩ := i1.unique i1'
    obtain ⟨rfl, rfl, rfl⟩ := i2.unique i2'
    obtain rfl : xc = xc' := Option.some.inj (hXc.symm.trans hXc')
    obtain rfl : v2 = v2' := Option.some.inj (hD2.symm.trans hD2')
    rfl

end Blanc.Lift.Curve3Pool
