import Blanc.Composition.Curve3Pool3CrvWorld
import Blanc.Lift.Curve3Pool.LivePremises
import Blanc.Lift.ExactWalkCallChild
import Blanc.Lift.MutableCallPost
import Blanc.Lift.VyperNonreentrantDeployed.Token20.RunTransferFrom

/-!
# U9(b): the coins' answers to the pool's `CALL`s, from the synthetic token's code

The pool's `exchange` calls coin `i`'s `transferFrom(msg.sender, self, dx)` and coin `j`'s
`transfer(msg.sender, dy)` (`CoinPullOkAt`, `CoinPushOkAt`, `Lift/Curve3Pool/LivePremises.lean`).
In the closed instance both coins run the synthetic token `Token20`
(`VyperNonreentrantDeployed.Token20`), and these premises are discharged here from its code:
the `CALL` crosses into a child frame whose message the parent builds
(`Ninst.runCompiled_call_zero_child`), and the child is the token's gas-exact run
(`transferFrom_runExact`, `transfer_runExact`) lifted to an execution (`lift_exact`).

* `cc_cross`: a value-`0` `CALL` from a pool call site into an undelegated, non-precompile callee
  whose child message runs cleanly resumes in `callChildPost` (the call/forward split computed);
* `cc_post`: what the resumed parent shows the caller (`MutableCallPost`, flag `1`, gas used at
  most the access, the expansion and the child's charge).

The answers are the token's code, not premises: no hypothesis here mentions what the callee
returns.
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift

/-! ## The crossing, at a pool call site -/

section Cross

variable (sevm : Sevm) (b : Devm) (S : List B256) (M : Mem) (G : Nat) (t ii is oi : B256)

/-- The expansion charge of the call's two windows. -/
def ccExt : Nat :=
  (St b S M G).extCost [⟨ii.toNat, is.toNat⟩, ⟨oi.toNat, (0x20 : B256).toNat⟩]

/-- The callee's access charge. -/
def ccAcc : Nat := accessCost t.toAdr (St b S M G).accessedAddresses + 0

/-- The gas forwarded to the child (all but one 64th of what is left). -/
def ccFwd : Nat := except64th (G - ccExt b S M G ii is oi - ccAcc b S M G t)

/-- The popped call state with the callee warmed. -/
def ccWarm : Devm := addAccessedAddress (St b S M G) t.toAdr

/-- The parent the child returns to. -/
def ccParent : Devm :=
  callSpawnParent (ccWarm b S M G t)
    (ccFwd b S M G t ii is oi + ccAcc b S M G t + ccExt b S M G ii is oi)
    ii.toNat is.toNat oi.toNat (0x20 : B256).toNat

/-- The child message. -/
def ccMsg : Msg :=
  valueCallSpawnMsg sevm (ccParent b S M G t ii is oi) (ccFwd b S M G t ii is oi) 0 t.toAdr
    t.toAdr ii.toNat is.toNat (b.state.getCode t.toAdr) false

/-- The resumed parent, from the child's post `cpost`. -/
def ccPost (cpost : Devm) : Devm :=
  callChildPost (ccParent b S M G t ii is oi) cpost oi.toNat (0x20 : B256).toNat

end Cross

theorem cc_fwd_le (b : Devm) (S : List B256) (M : Mem) (G : Nat) (t ii is oi : B256) :
    ccFwd b S M G t ii is oi ≤ G - ccExt b S M G ii is oi - ccAcc b S M G t := by
  unfold ccFwd except64th
  omega

/-- **The `CALL` crossing at a pool call site** (see the module note). -/
theorem cc_cross {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {t ii is oi : B256} {cpost : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hdel : getDelegatedCodeAddress (b.state.getCode t.toAdr) = none)
    (hdepth : sevm.depth ≠ 0) (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false)
    (hroom : S.length < 1024) (hG : G < 2 ^ 256)
    (hcharge : ccAcc b S M G t + ccExt b S M G ii is oi ≤ G)
    (hexec : exec (initEvm (ccMsg sevm b S M G t ii is oi)) = .ok cpost)
    (herr : cpost.error = none) :
    Ninst.RunCompiled sevm (St b (Nat.toB256 G :: t :: 0 :: ii :: is :: oi :: 0x20 :: S) M G)
      (.exec .call) (ccPost b S M G t ii is oi cpost) := by
  have hfwd := cc_fwd_le b S M G t ii is oi
  have hsplit : calculateMsgCallGas 0 (Nat.toB256 G).toNat (ccWarm b S M G t).gasLeft
      (ccExt b S M G ii is oi) (ccAcc b S M G t) =
      ⟨ccFwd b S M G t ii is oi + ccAcc b S M G t, ccFwd b S M G t ii is oi⟩ := by
    rw [B256.toNat_toB256_of_lt hG]
    change calculateMsgCallGas 0 G G _ _ = _
    unfold calculateMsgCallGas
    simp only [show ¬ G < ccAcc b S M G t + ccExt b S M G ii is oi from by omega, ↓reduceIte]
    rw [Nat.min_eq_right (by unfold except64th; omega), Nat.add_zero]
    rfl
  exact Ninst.runCompiled_call_zero_child (stmid := (ccWarm b S M G t).state.setBal
      sevm.currentTarget ((ccWarm b S M G t).state.bal sevm.currentTarget - 0))
    hfork rfl rfl
    (by
      unfold accessDelegation
      have hs : ∀ m, (addAccessedAddress ((St b (Nat.toB256 G :: t :: 0 :: ii :: is :: oi :: 0x20 ::
          S) M G).setMach m) t.toAdr).state = b.state := fun _ => rfl
      simp only [hs, hdel]
      rfl)
    rfl hsplit
    (by change _ ≤ G; omega) hdepth hprec hroom
    (by
      unfold State.subBal
      simp only [show ¬ (ccWarm b S M G t).state.bal sevm.currentTarget < 0 from
        B256.not_lt.mpr (B256.zero_le _), ↓reduceIte])
    (by simp only [callChildMsg, ite_true]; exact hexec) herr

end Blanc.Composition.Curve3Pool3CrvInstance
