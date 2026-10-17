import Blanc.Composition.UsdcTokenLive

namespace Blanc.Composition.UsdcLive

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc

theorem childXferCost_gasField (s : Sevm) (pre : Devm) (f : Nat) :
    childXferCost { s with gas := f } pre = childXferCost s pre := rfl

section GasField

variable (s : Sevm) (f : Nat)

theorem p8W_gas (b : Devm) (ret : B256) (S : List B256) (M : Mem) :
    (p8W { s with gas := f } b ret S M).1 = (p8W s b ret S M).1 := by
  unfold p8W; rfl

theorem p14W_gas (b : Devm) (ret : B256) (S : List B256) (M : Mem) :
    (p14W { s with gas := f } b ret S M).1 = (p14W s b ret S M).1 := by
  unfold p14W; rfl

theorem p31W_gas (b : Devm) (ret : B256) (S : List B256) (M : Mem) :
    (p31W { s with gas := f } b ret S M).1 = (p31W s b ret S M).1 := by
  unfold p31W; rfl

theorem p22W_gas (b : Devm) (ret : B256) (S : List B256) (M : Mem) :
    (p22W { s with gas := f } b ret S M).1 = (p22W s b ret S M).1 := by
  unfold p22W; simp only [p8W_gas, p31W_gas]; rfl

theorem proxyPreW_gas (b : Devm) (sel : B256) :
    (proxyPreW { s with gas := f } b sel).1 = (proxyPreW s b sel).1 := by
  unfold proxyPreW; simp only [p22W_gas, p14W_gas]; rfl

theorem dTailW_gas (D : Devm) (R : List B256) (M : Mem) (w : B256) :
    (dTailW { s with gas := f } D R M w).1 = (dTailW s D R M w).1 := by
  unfold dTailW; rfl

theorem proxyXferCost_gasField (pre : Devm) :
    proxyXferCost { s with gas := f } pre = proxyXferCost s pre := by
  unfold proxyXferCost
  rw [proxyPreW_gas]
  exact congrArg _ (congrArg (· + _) (congrArg (· + _) (congrArg (· + _) (dTailW_gas s f _ _ _ _))))

end GasField

theorem St_withGasLeft (b : Devm) (g : Nat) (S : List B256) (M : Mem) (G : Nat) :
    St (b.withGasLeft g) S M G = St b S M G := rfl

theorem St_reframe (b : Devm) (S : List B256) (M : Mem) (G : Nat) :
    St b S M G = (St b S M 0).withGasLeft G := rfl

theorem withOutput_withGasLeft (d : Devm) (o : Bytes) (g : Nat) :
    (d.withGasLeft g).withOutput o = (d.withOutput o).withGasLeft g := rfl

theorem implXferPost_gasField (s : Sevm) (b : Devm) (f G : Nat) :
    implXferPost { s with gas := f } b G = implXferPost s b G := by
  simp only [implXferPost, e93Post, e93Debited, e37Pre, implXferMem, e93Mem, xTo, xVal,
    UniswapV2PairWeth9Joint.afterSload_gasField, UniswapV2PairWeth9Joint.afterSstore_gasField,
    UniswapV2PairWeth9Joint.dataWord_gasField]

theorem implXferPost_reframe (s : Sevm) (b : Devm) (G : Nat) :
    implXferPost s b G = (implXferPost s b 0).withGasLeft G := by
  unfold implXferPost
  rw [St.memRead_snd, St.memRead_snd, St_reframe _ _ _ G, withOutput_withGasLeft]

theorem dParent_reframe (s : Sevm) (pre : Devm) (Y : Nat) :
    dParent s pre Y = (dParent s pre 0).withGasLeft (Y - (dFwd s pre Y + dAcc s pre + dExt s pre)) := by
  unfold dParent dWarm dPop
  rw [St_reframe _ _ _ Y]
  rfl

theorem frameY_gasField (s : Sevm) (pre : Devm) (f X : Nat) :
    frameY { s with gas := f } pre X = frameY s pre X := by
  exact congrArg (fun t => X + t + dAcc s pre + dExt s pre + childXferCost s pre)
    (dTailW_gas s f (dParent s pre 0) (pRest s pre) (dParent s pre 0).memory xferWord)

theorem proxyXferPost_gasField (s : Sevm) (pre : Devm) (f X : Nat) :
    proxyXferPost { s with gas := f } pre X = proxyXferPost s pre X := by
  unfold proxyXferPost frameChild
  rw [frameY_gasField]
  rfl

theorem proxyXferPost_reframe (s : Sevm) (pre : Devm) (X : Nat) :
    proxyXferPost s pre X = (proxyXferPost s pre 0).withGasLeft X := by
  unfold proxyXferPost frameChild proxyPost
  rw [dMsg_sevm s pre (frameY s pre X), dMsg_sevm s pre (frameY s pre 0), implXferPost_gasField,
    implXferPost_gasField, implXferPost_reframe _ _ (dFwd s pre (frameY s pre X) - _),
    implXferPost_reframe _ _ (dFwd s pre (frameY s pre 0) - _), dParent_reframe s pre (frameY s pre X),
    dParent_reframe s pre (frameY s pre 0), UniswapV2PairWeth9Joint.callChildPost_withGasLeft,
    UniswapV2PairWeth9Joint.callChildPost_withGasLeft, St_withGasLeft, St_withGasLeft,
    St.memRead_snd, St.memRead_snd, St_reframe _ _ _ X, withOutput_withGasLeft]
  simp only [implXferPost_gasField]
  rfl

end Blanc.Composition.UsdcLive
