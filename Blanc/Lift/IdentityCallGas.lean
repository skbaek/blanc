import Blanc.Lift.IdentityCall
import Blanc.ForwardStorageAccess

/-!
# A failed identity copy that forwarded all gas leaves none

Vyper 0.2.x builds `concat()` results with `CALL(gas(), 4, 0, …)` and does not always test the
flag (the selector copy of a `raw_call` payload is popped unchecked). When the forwarded gas is
the frame's whole remaining gas, the call can only fail at a nonzero depth by running the
precompile out of gas, which needs fewer than its charge forwarded (63/64 of what is left after
the access and expansion charges), and the caller keeps the other 64th, which is then zero.

`ri_call_identity_gas_fail`: such a step that pushed `0`, at a nonzero depth, leaves no gas, so
the frame cannot continue past it. Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- **A failed identity child**, for a value-0 message: it was forwarded less than its charge,
and returns no gas. -/
theorem processMessage_identity_error
    {parent child : Devm} {gas : Nat} {calldata : Bytes} {stv st : Bool}
    {code : ByteArray} {xl : Xlot}
    (hpre : decide (sevm.benvStat.rules.isPrecomp 4) = true)
    (hpm : ProcessMessage
      (callMsg sevm parent gas 0 sevm.currentTarget 4 4 stv st calldata code false) xl
        (.ok child))
    (herr : child.error.isSome = true) :
    child.gasLeft = 0 ∧ gas < idCost calldata.length := by
  obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp hpm
  unfold FrameBody at hbody
  rw [Msg.benvAfterTransfer_of_value_zero (by rfl)] at hbody
  have hca : ((callMsg sevm parent gas 0 sevm.currentTarget 4 4 stv st calldata code false).withBenv
      (callMsg sevm parent gas 0 sevm.currentTarget 4 4 stv st calldata code false).benv).codeAddress =
        some 4 := rfl
  rcases of_executeCode_someCode hca hbody with hpc | hinterp
  · have hexec := hpc.2.2
    change executeCode.handleErrorWith _ (applyPrecompResult _ (executeId _)) = r0 at hexec
    unfold executeId PrecompResult.chargeGas at hexec
    dsimp only at hexec
    split at hexec
    · simp only [applyPrecompResult, executeCode.handleErrorWith] at hexec
      split at hexec <;>
        simp only [executeCode.handleError, executeCode.handleErrorAmsterdam] at hexec
      all_goals
        rw [← hexec] at hset
        unfold processMessage.settle at hset
        simp only [bind, Except.bind, Option.isSome] at hset
        injection hset with hchild
        subst child
        simp only [Devm.withGasLeft, Devm.withOutput, initEvm, initDevm] at herr
        cases herr
    · rename_i hgas
      simp only [applyPrecompResult, executeCode.handleErrorWith] at hexec
      split at hexec <;>
        simp only [executeCode.handleError, executeCode.handleErrorAmsterdam] at hexec
      all_goals
        rw [← hexec] at hset
        unfold processMessage.settle at hset
        simp only [bind, Except.bind, Option.isSome] at hset
        injection hset with hchild
        subst child
        refine ⟨rfl, ?_⟩
        exact Nat.lt_of_not_le hgas
  · exact False.elim (hinterp.1 hpre)

/-- A `CALL` resumption with a failed child gives the parent back the child's gas. -/
theorem Resume.call_gasLeft_error {parent child sf : Devm} {oi os : Nat}
    (h : (Resume.call parent oi os).run (.ok child) = .ok sf) (he : child.error.isSome = true) :
    sf.gasLeft = parent.gasLeft + child.gasLeft := by
  unfold Resume.run liftToExecution at h
  simp only [bind, Except.bind, he, ↓reduceIte] at h
  rcases hp : (incorporateChildOnError parent child child.output).push 0 with _ | d' <;>
    rw [hp] at h
  · cases h
  · cases h
    rw [Devm.eq_of_push_ok hp]
    rfl

theorem ri_call_identity_gas_fail {ii is oi os : B256} {d : Devm} (hid : IdReady sevm b)
    (hdepth : 0 < sevm.depth) (hG : G < 2 ^ 256) (his : is.toNat ≤ 32)
    (h : Ninst.Run sevm (St b (Nat.toB256 G :: 4 :: 0 :: ii :: is :: oi :: os :: S) M G)
      (.exec .call) d)
    (h0 : d.stack = 0 :: S) : d.gasLeft = 0 := by
  have hfork := hid.fork
  rcases h with ⟨xl, h_fill, pc, h_run⟩
  simp only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.step,
    Bind.bind, Except.bind, hfork.rules_stateGas_none] at h_run
  rw [show (St b (Nat.toB256 G :: 4 :: 0 :: ii :: is :: oi :: os :: S) M G).pop =
    .ok (Nat.toB256 G, St b (4 :: 0 :: ii :: is :: oi :: os :: S) M G) from rfl] at h_run
  simp only at h_run
  rw [show (St b (4 :: 0 :: ii :: is :: oi :: os :: S) M G).popToAdr =
    .ok ((4 : Adr), St b (0 :: ii :: is :: oi :: os :: S) M G) from rfl] at h_run
  simp only at h_run
  rw [show (St b (0 :: ii :: is :: oi :: os :: S) M G).pop =
    .ok (0, St b (ii :: is :: oi :: os :: S) M G) from rfl] at h_run
  simp only at h_run
  rw [show (St b (ii :: is :: oi :: os :: S) M G).popToNat =
    .ok (ii.toNat, St b (is :: oi :: os :: S) M G) from rfl] at h_run
  simp only at h_run
  rw [show (St b (is :: oi :: os :: S) M G).popToNat =
    .ok (is.toNat, St b (oi :: os :: S) M G) from rfl] at h_run
  simp only at h_run
  rw [show (St b (oi :: os :: S) M G).popToNat =
    .ok (oi.toNat, St b (os :: S) M G) from rfl] at h_run
  simp only at h_run
  rw [show (St b (os :: S) M G).popToNat =
    .ok (os.toNat, St b S M G) from rfl] at h_run
  simp only at h_run
  have hAD : sevm.benvStat.rules.gas.accessDelegation (addAccessedAddress (St b S M G) 4) 4 =
      ⟨false, 4, b.getCode 4, 0, addAccessedAddress (St b S M G) 4⟩ := by
    unfold GasSchedule.accessDelegation
    simp only [show (addAccessedAddress (St b S M G) 4).state.getCode 4 = b.getCode 4 from rfl,
      hid.nodeleg]
  have hA : addAccessedAddress (St b S M G) 4 = St b S M G :=
    addAccessedAddress_eq_self_of_mem hid.warm
  rw [hAD, hA] at h_run
  simp only [or_true, ↓reduceIte, Except.assert] at h_run
  have hbal : ∀ x : B256, ¬ x < 0 := fun x hx => by
    rw [B256.lt_iff_toNat_lt_toNat] at hx; exact Nat.not_lt_zero _ hx
  split at h_run
  · cases XStep.run_ofExcept_error h_run
  rename_i v hcharge
  simp only [hbal, ↓reduceIte] at h_run
  have hdep : sevm.depth ≠ 0 := Nat.pos_iff_ne_zero.mp hdepth
  have hcost := Devm.gasLeft_of_chargeGas hcharge
  simp only [St.gasLeft, B256.toNat_toB256_of_lt hG] at hcost h_run
  unfold calculateMsgCallGas at hcost h_run
  simp only [show B256.toNat (0 : B256) = 0 from rfl, ↓reduceIte] at hcost h_run
  split_ifs at hcost h_run with hlt
  · dsimp only at hcost
    omega
  dsimp only at hcost h_run
  simp only [pure, Except.pure, XStep.ofExcept, genericCall.step, hdep, ite_false,
    XStep.Run] at h_run
  rcases h_run with ⟨ex', run_pm₀, h_split⟩
  rcases ex' with err' | child
  · cases Resume.call_run_error h_split.symm
  have hsplit := h_split.symm
  have hstk := Resume.call_stack_flag hsplit
  have herr : child.error.isSome = true := by
    cases e : child.error.isSome with
    | true => rfl
    | false =>
      rw [e] at hstk
      rw [h0] at hstk
      exact absurd (List.cons.inj hstk).1 (by decide)
  obtain ⟨Gv, rfl⟩ : ∃ Gv, v = St b S M Gv :=
    ⟨_, Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas hcharge)⟩
  set ext := (St b S M G).extCost [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] with hext
  set acc := sevm.benvStat.rules.gas.accessCost 4 (St b S M G).accessedAddresses + 0 + 0 + 0
    with hacc
  set P := ((St b S M Gv).memExtends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData
    [] with hP
  have hcd : Array.sliceD P.memory.data ii.toNat is.toNat 0 = (M.read ii.toNat is.toNat).1 := rfl
  rw [hcd] at run_pm₀
  have pm : ProcessMessage (callMsg sevm P (min G (except64th (G - ext - acc))) 0
      sevm.currentTarget 4 4 true false (M.read ii.toNat is.toNat).1 (b.getCode 4) false) xl
      (.ok child) := by
    simpa only [ProcessMessage, add_zero] using run_pm₀
  obtain ⟨hcg, hlow⟩ := processMessage_identity_error hid.pre pm herr
  rw [Resume.call_gasLeft_error hsplit herr, hcg]
  have hlen : (M.read ii.toNat is.toNat).1.length = is.toNat := by
    show (Array.sliceD M.data ii.toNat is.toNat 0).length = is.toNat
    rw [Array.sliceD_eq_map, List.length_map, List.length_range]
  rw [hlen] at hlow
  have hid18 : idCost is.toNat ≤ 18 := by
    unfold idCost ceilDiv
    split <;> omega
  show Gv + 0 = 0
  simp only [St.gasLeft] at hcost
  unfold except64th at hcost hlow
  omega

/-- A `POP` needs gas. -/
theorem gasLeft_of_run_pop {d d' : Devm} (h : Ninst.Run sevm d (.reg .pop) d') :
    0 < d.gasLeft := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases e : d.pop with _ | ⟨x, d1⟩ <;> rw [e] at run
  · cases run
  · have h1 : d.gasLeft = d1.gasLeft := Devm.gasLeft_of_pop e
    have h2 := Devm.gasLeft_of_chargeGas run
    rw [h1, h2]
    show 0 < d'.gasLeft + 2
    omega

/-! ## Identity readiness across storage steps -/

theorem IdReady.afterSload {b : Devm} (h : IdReady sevm b) (k : B256) :
    IdReady sevm (afterSload sevm b k) :=
  ⟨by rw [afterSload_getCode]; exact h.nodeleg,
    by rw [afterSload_accessedAddresses]; exact h.warm, h.pre, h.fork⟩

theorem IdReady.afterSstore {b : Devm} (h : IdReady sevm b) (k v : B256) :
    IdReady sevm (afterSstore sevm b k v) :=
  ⟨by rw [afterSstore_getCode]; exact h.nodeleg,
    by rw [afterSstore_accessedAddresses]; exact h.warm, h.pre, h.fork⟩

end Blanc.Lift
