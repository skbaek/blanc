import Blanc.Lift.IdentityCallGas
import Blanc.Lift.HistStaticCall
import Blanc.Lift.HistAccessWalkFacts
import Blanc.HistoricalFork

/-!
# The identity precompile under a frame's actual rules

`IdReady` fixes `CoveredFork`.  `IdReadyH` keeps its readiness facts and asks only for no state gas
from the rules: the flat access regime leaves the accessed set alone, and disabled delegation
resolves the target's own code, so with `4` warm and undelegated every regime reaches the same
machine and differs only in its charge.  Warmth holds on every regime (`prepareMessage` warms
precompiles unconditionally).  Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- The identity precompile premises of a frame, under the frame's actual rules. -/
structure IdReadyH (sevm : Sevm) (b : Devm) : Prop where
  nodeleg : getDelegatedCodeAddress (b.getCode 4) = none
  warm : (4 : Adr) ∈ b.accessedAddresses
  pre : decide (sevm.benvStat.rules.isPrecomp 4) = true
  stateGas : sevm.benvStat.rules.stateGas = none

theorem IdReady.toH {sevm : Sevm} {b : Devm} (h : IdReady sevm b) : IdReadyH sevm b :=
  ⟨h.nodeleg, h.warm, h.pre, h.fork.rules_stateGas_none⟩

theorem IdReadyH.of_rel {sevm : Sevm} {b b' : Devm} (h : IdReadyH sevm b) (hr : BaseRel b b') :
    IdReadyH sevm b' :=
  ⟨by rw [hr.code]; exact h.nodeleg, by rw [hr.addrs]; exact h.warm, h.pre, h.stateGas⟩

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- Whichever delegation flag the rules select, `4` resolves to its own code without delegation. -/
theorem IdReadyH.delegation (hid : IdReadyH sevm b) (D : Devm) (hD : D.state = b.state) :
    sevm.benvStat.rules.accessDelegation D 4 = ⟨false, 4, b.getCode 4, 0, D⟩ := by
  have code : D.state.getCode 4 = b.getCode 4 := by rw [hD]; rfl
  cases hdel : sevm.benvStat.rules.delegationEnabled with
  | false =>
    rw [ForkRules.accessDelegation_disabled hdel, code]
  | true =>
    rw [ForkRules.accessDelegation_enabled hdel]
    unfold GasSchedule.accessDelegation
    simp only [code, hid.nodeleg]

theorem IdReadyH.afterSloadH {b : Devm} (h : IdReadyH sevm b) (k : B256) :
    IdReadyH sevm (afterSloadH sevm b k) :=
  ⟨by rw [afterSloadH_getCode]; exact h.nodeleg, by
    have e := afterSloadH_accessedAddresses sevm b k
    rw [e]; exact h.warm, h.pre, h.stateGas⟩

theorem processMessage_identity_cleanH
    {sevm : Sevm} {parent child : Devm} {gas : Nat} {calldata : Bytes} {stv st : Bool}
    {code : ByteArray} {xl : Xlot}
    (hpre : decide (sevm.benvStat.rules.isPrecomp 4) = true)
    (hpm : ProcessMessage
      (callMsg sevm parent gas 0 sevm.currentTarget 4 4 stv st calldata code false) xl
        (.ok child))
    (hclean : child.error.isSome = false) (hsg : sevm.benvStat.rules.stateGas = none) :
    child.output = calldata ∧ child.state = parent.state ∧
      child.accessedAddresses = parent.accessedAddresses ∧
      child.accessedStorageKeys = parent.accessedStorageKeys ∧ child.logs = [] ∧
      child.createdAccounts = parent.createdAccounts ∧ idCost calldata.length ≤ gas ∧
      child.refundCounter = 0 := by
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
        refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, hgas, ?_⟩
        all_goals
          simp only [initEvm, initDevm, Devm.withOutput_logs, Devm.withOutput_refundCounter]
          dsimp only [Devm.withGasLeft, Devm.setMach, Devm.logs, Devm.refundCounter, liftMachPure]
          try split
          all_goals first
            | rfl
            | (rename_i heq
               exact absurd (heq.symm.trans hsg)
                 (by simp only [reduceCtorEq, not_false_eq_true]))
    · simp only [applyPrecompResult, executeCode.handleErrorWith] at hexec
      split at hexec <;>
        simp only [executeCode.handleError, executeCode.handleErrorAmsterdam] at hexec
      all_goals
        rw [← hexec] at hset
        unfold processMessage.settle at hset
        simp only [bind, Except.bind, Option.isSome] at hset
        injection hset with hchild
        subst child
        change true = false at hclean
        contradiction
  · exact False.elim (hinterp.1 hpre)


theorem ri_call_identityH {g ii is oi os : B256} {d : Devm} (hid : IdReadyH sevm b)
    (h : Ninst.Run sevm (St b (g :: 4 :: 0 :: ii :: is :: oi :: os :: S) M G) (.exec .call) d) :
    d.stack = 0 :: S ∨
      ∃ b' G', ShaCallPost b b' (M.read ii.toNat is.toNat).1 ∧
        d = St b' (1 :: S) ((M.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write
          oi.toNat ((M.read ii.toNat is.toNat).1.take os.toNat)) G' := by
  rcases h with ⟨xl, h_fill, pc, h_run⟩
  simp only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.step,
    Bind.bind, Except.bind, hid.stateGas] at h_run
  rw [show (St b (g :: 4 :: 0 :: ii :: is :: oi :: os :: S) M G).pop =
    .ok (g, St b (4 :: 0 :: ii :: is :: oi :: os :: S) M G) from rfl] at h_run
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
  have hA : addAccessedAddress (St b S M G) 4 = St b S M G :=
    addAccessedAddress_eq_self_of_mem hid.warm
  cases hacc0 : sevm.benvStat.rules.access <;> simp only [hacc0] at h_run
  case' flat gf => skip
  all_goals try rw [hA] at h_run
  all_goals rw [hid.delegation (St b S M G) rfl] at h_run
  all_goals (
    simp only [or_true, ↓reduceIte, Except.assert] at h_run
    have hbal : ∀ x : B256, ¬ x < 0 := fun x hx => by
      rw [B256.lt_iff_toNat_lt_toNat] at hx; exact Nat.not_lt_zero _ hx
    split at h_run
    · cases XStep.run_ofExcept_error h_run
    rename_i v hcharge
    simp only [hbal, ↓reduceIte] at h_run
    obtain ⟨Gv, rfl⟩ : ∃ Gv, v = St b S M Gv :=
      ⟨_, Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas hcharge)⟩
    by_cases hdepth : sevm.depth = 0
    · left
      simp only [pure, Except.pure, XStep.ofExcept, genericCall.step, hdepth, ite_true] at h_run
      simp only [bind, Except.bind] at h_run
      split at h_run
      · simp only [XStep.Run, ExceptT.stM_eq, reduceCtorEq, and_false] at h_run
      · rename_i d' hp
        split at hp
        · cases hp
        · rename_i d'' hpush
          cases hp
          simp only [XStep.Run, Except.ok.injEq] at h_run
          rw [h_run.2, Devm.eq_of_push_ok hpush]
          rfl
    simp only [pure, Except.pure, XStep.ofExcept, genericCall.step, hdepth, ite_false] at h_run
    simp only [XStep.Run] at h_run
    rcases h_run with ⟨ex', run_pm₀, h_split⟩
    rcases ex' with err' | child
    · cases Resume.call_run_error h_split.symm
    have hsplit := h_split.symm
    have hstk := Resume.call_stack_flag hsplit
    by_cases herr : child.error.isSome
    · left
      simp only [herr, ↓reduceIte] at hstk
      exact hstk
    right
    have hclean : child.error.isSome = false := by simpa only [Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none, Bool.not_eq_true] using herr
    simp only [hclean, Bool.false_eq_true, ↓reduceIte] at hstk
    set P := ((St b S M Gv).memExtends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData
      [] with hP
    have hcd : Array.sliceD P.memory.data ii.toNat is.toNat 0 = (M.read ii.toNat is.toNat).1 := rfl
    rw [hcd] at run_pm₀
    obtain ⟨gas, pm⟩ : ∃ gas, ProcessMessage (callMsg sevm P gas 0 sevm.currentTarget 4 4 true false
        (M.read ii.toNat is.toNat).1 (b.getCode 4) false) xl (.ok child) :=
      ⟨_, by simpa only [ProcessMessage, St.gasLeft, add_zero] using run_pm₀⟩
    obtain ⟨hout, hcst, hca, hck, hcl, hcc, -, hcr⟩ :=
      processMessage_identity_cleanH hid.pre pm hclean hid.stateGas
    obtain ⟨hra, hrk, hre, hrc, hrr⟩ := Resume.call_ok_meta hsplit hclean
    have hlogs := Resume.call_logs hsplit
    simp only [hclean, Bool.false_eq_true, ↓reduceIte, hcl, List.append_nil] at hlogs
    have hmem := Resume.call_memory hsplit
    rw [hout] at hmem
    have hst := Resume.call_state hsplit
    refine ⟨d, d.gasLeft, ⟨fun a => ?_, fun a => ?_, ?_, ?_, hlogs,
      (Resume.call_output hsplit).trans rfl, hre, (Resume.call_returnData hsplit).trans hout,
      hrc.trans (hcc.trans rfl), by rw [hrr, hcr, Int.add_zero]; rfl⟩, St.self hstk hmem⟩
    · exact getStor_eq_of_state_eq (hst.trans hcst) a
    · exact getCode_eq_of_state_eq (hst.trans hcst) a
    · rw [hra, hca, hashSet_union_self]; rfl
    · rw [hrk, hck, hashSet_union_self]; rfl)

theorem ri_call_identity_gas_failH {ii is oi os : B256} {d : Devm} (hid : IdReadyH sevm b)
    (hdepth : 0 < sevm.depth) (hG : G < 2 ^ 256) (his : is.toNat ≤ 32)
    (h : Ninst.Run sevm (St b (Nat.toB256 G :: 4 :: 0 :: ii :: is :: oi :: os :: S) M G)
      (.exec .call) d)
    (h0 : d.stack = 0 :: S) : d.gasLeft = 0 := by
  rcases h with ⟨xl, h_fill, pc, h_run⟩
  simp only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.step,
    Bind.bind, Except.bind, hid.stateGas] at h_run
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
  have hA : addAccessedAddress (St b S M G) 4 = St b S M G :=
    addAccessedAddress_eq_self_of_mem hid.warm
  cases hacc0 : sevm.benvStat.rules.access <;> simp only [hacc0] at h_run
  case' flat gf => skip
  all_goals try rw [hA] at h_run
  all_goals rw [hid.delegation (St b S M G) rfl] at h_run
  all_goals (
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
    simp only [Nat.add_zero] at hcost run_pm₀
    first
    | set acc := gf.call with hacc
    | set acc := sevm.benvStat.rules.gas.accessCost 4 (St b S M G).accessedAddresses with hacc
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
    omega)

end Blanc.Lift
