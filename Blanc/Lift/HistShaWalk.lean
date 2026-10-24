import Blanc.Lift.InvWalkSha
import Blanc.Lift.ExactWalkCutOps
import Blanc.StaticPrecompileMessage

/-!
# Historical SHA-256 `STATICCALL` inversion kit

The exact-walk SHA kit (`Blanc/Lift/InvWalkSha.lean`, `ShaReady` in
`Blanc/Lift/ExactWalkCutOps.lean`) takes `CoveredFork`, which fixes the
EIP-2929 access schedule and enabled delegation. This module proves the same
steps from the rule facts a historical frame carries:

* `ShaReadyH` — the SHA-256 precompile premises with `stateGas = none` and
  `bal = none` in place of the fork (`ShaReadyH.of_eq`, `ShaReady.toH`);
* `meta_of_processMessage_sha256_64_clean_noStateGas` — the clean-child
  meta projection over `stateGas = none` alone;
* `ri_staticcall_shaH` — `STATICCALL` of SHA-256 over a 64-byte window,
  cased once on the access schedule and the delegation flag to a single
  prefix form, then the modern tail verbatim;
* `ri_staticcall_shaH_covered` — the out-and-back check recovering the
  modern statement on a covered fork.

`hnodeleg` is used only in the enabled-delegation branch and `hwarm` only in
the EIP-2929 branch; both stay unconditional in the modern argument order so
the Beacon copies become identifier renames. Gas is existential, so pricing
never appears in any conclusion.

Contract-neutral: no contract name in any statement.
-/

namespace Blanc.Lift

open Jaune

/-! ## The historical SHA-256 precompile premises -/

/-- The SHA-256 precompile premises a historical frame's world carries:
address 2 undelegated and warm, a precompile of the rules, no state gas and
no access list. -/
structure ShaReadyH (sevm : Sevm) (b : Devm) : Prop where
  nodeleg : getDelegatedCodeAddress (b.getCode 2) = none
  warm : (2 : Adr) ∈ b.accessedAddresses
  pre : decide (sevm.benvStat.rules.isPrecomp 2) = true
  sg : sevm.benvStat.rules.stateGas = none
  bal : sevm.benvStat.rules.bal = none

theorem ShaReadyH.of_eq {sevm : Sevm} {b b' : Devm} (h : ShaReadyH sevm b)
    (hc : ∀ a, b'.getCode a = b.getCode a) (ha : b'.accessedAddresses = b.accessedAddresses) :
    ShaReadyH sevm b' :=
  ⟨by rw [hc]; exact h.nodeleg, by rw [ha]; exact h.warm, h.pre, h.sg, h.bal⟩

theorem ShaReady.toH {sevm : Sevm} {b : Devm} (h : ShaReady sevm b)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hbal : sevm.benvStat.rules.bal = none) : ShaReadyH sevm b :=
  ⟨h.nodeleg, h.warm, h.pre, hsg, hbal⟩

/-! ## The clean-child meta projection without state gas -/

/-- A clean 64-byte SHA-256 child keeps the parent's access sets and created-account set and
logs nothing, over `rules.stateGas = none` alone. -/
theorem meta_of_processMessage_sha256_64_clean_noStateGas
    {sevm : Sevm} {parent child : Devm} {gas : Nat} {calldata : Bytes}
    {code : ByteArray} {xl : Xlot}
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hlen : calldata.length = 64)
    (hpm : ProcessMessage
      (callMsg sevm parent gas 0 sevm.currentTarget 2 2 true true
        calldata code false) xl (.ok child))
    (hclean : child.error.isSome = false)
    (hsg : sevm.benvStat.rules.stateGas = none) :
    child.accessedAddresses = parent.accessedAddresses ∧
      child.accessedStorageKeys = parent.accessedStorageKeys ∧ child.logs = [] ∧
        child.createdAccounts = parent.createdAccounts ∧ child.refundCounter = 0 := by
  have hgas : 84 ≤ gas :=
    gasSha25664_le_of_processMessage_clean hpre hlen hpm hclean
  obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp hpm
  unfold FrameBody at hbody
  rcases hbt :
      (callMsg sevm parent gas 0 sevm.currentTarget 2 2 true true
        calldata code false).benvAfterTransfer with e | benv <;>
    rw [hbt] at hbody
  · rw [hbody.2] at hset
    unfold processMessage.settle at hset
    cases hset
  · rw [Msg.benvAfterTransfer_of_value_zero (by rfl)] at hbt
    cases hbt
    have hca :
        ((callMsg sevm parent gas 0 sevm.currentTarget 2 2 true true
          calldata code false).withBenv (callMsg sevm parent gas 0 sevm.currentTarget 2 2 true
            true calldata code false).benv).codeAddress =
          some 2 := rfl
    rcases of_executeCode_someCode hca hbody with hpc | hinterp
    · have hexec := hpc.2.2
      rw [executePrecomp_two_of_length_64 (by
        change calldata.length = 64
        exact hlen) (by
        change 84 ≤ gas
        exact hgas)] at hexec
      simp only [applyPrecompResult, executeCode.handleErrorWith] at hexec
      split at hexec <;>
        simp only [executeCode.handleError,
          executeCode.handleErrorAmsterdam] at hexec
      all_goals
        rw [← hexec] at hset
        unfold processMessage.settle at hset
        simp only [bind, Except.bind, Option.isSome] at hset
        injection hset with hchild
        subst child
        refine ⟨rfl, rfl, ?_, rfl, ?_⟩
        all_goals
          simp only [initEvm, initDevm]
          dsimp only [Devm.withGasLeft, Devm.setMach, Devm.logs, Devm.refundCounter, liftMachPure]
          try split
          all_goals first
            | rfl
            | (rename_i heq
               exact absurd (heq.symm.trans hsg) (by simp only [reduceCtorEq, not_false_eq_true]))
    · exact False.elim (hinterp.1 hpre)

/-! ## `STATICCALL` of SHA-256 over a historical frame -/

/-- **The charged tail of a SHA-256 `STATICCALL`.**  Once the six operands are popped and the
access and delegation prefix has been normalised (address 2 warm and undelegated, so the base
`St b S M G` is unchanged and the call code is `b.getCode 2`), the step is fixed up to the
access charge `c`: it either pushed `0`, or pushed `1` over a `ShaCallPost`-extension of `b` with
the digest written over the output window. -/
theorem ri_staticcall_sha_of_charge {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem}
    {G : Nat} {g ii oi : B256} {d : Devm} {xl : Xlot} (c : Nat)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (h_run : (XStep.ofExcept (Except.bind
      (chargeGas ((calculateMsgCallGas 0 g.toNat (St b S M G).gasLeft
          ((St b S M G).extCost [(ii.toNat, 64), (oi.toNat, 32)]) c).1 +
        (St b S M G).extCost [(ii.toNat, 64), (oi.toNat, 32)]) (St b S M G))
      (fun v => pure (genericCall.step sevm (v.memExtends [(ii.toNat, 64), (oi.toNat, 32)])
        (calculateMsgCallGas 0 g.toNat (St b S M G).gasLeft
          ((St b S M G).extCost [(ii.toNat, 64), (oi.toNat, 32)]) c).2
        0 sevm.currentTarget 2 2 true true ii.toNat 64 oi.toNat 32 (b.getCode 2) false)))).Run
      xl (.ok d)) :
    d.stack = 0 :: S ∨
      ∃ b' G', ShaCallPost b b' (Bytes.sha256 (M.read ii.toNat 64).1).toBytes ∧
        d = St b' (1 :: S) ((M.extends [⟨ii.toNat, 64⟩, ⟨oi.toNat, 32⟩]).write oi.toNat
          (Bytes.sha256 (M.read ii.toNat 64).1).toBytes) G' := by
  simp only [Except.bind] at h_run
  split at h_run
  · cases XStep.run_ofExcept_error h_run
  rename_i v hcharge
  by_cases hdepth : sevm.depth = 0
  · left
    simp only [pure, Except.pure, XStep.ofExcept, genericCall.step, hdepth, ite_true] at h_run
    obtain ⟨Gv, rfl⟩ : ∃ Gv, v = St b S M Gv :=
      ⟨_, Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas hcharge)⟩
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
  obtain ⟨Gv, rfl⟩ : ∃ Gv, v = St b S M Gv :=
    ⟨_, Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas hcharge)⟩
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
  set P := ((St b S M Gv).memExtends [(ii.toNat, 64), (oi.toNat, 32)]).withReturnData [] with hP
  have hcd : Array.sliceD P.memory.data ii.toNat 64 0 = (M.read ii.toNat 64).1 := rfl
  rw [hcd] at run_pm₀
  obtain ⟨gas, pm⟩ : ∃ gas, ProcessMessage (callMsg sevm P gas 0 sevm.currentTarget 2 2 true true
      (M.read ii.toNat 64).1 (b.getCode 2) false) xl (.ok child) :=
    ⟨_, by simpa only [ProcessMessage, St.gasLeft, add_zero] using run_pm₀⟩
  have hlen : (M.read ii.toNat 64).1.length = 64 := by
    rw [← hcd, Array.sliceD_eq_map, List.length_map, List.length_range]
  have hout := output_of_processMessage_sha256_64_clean hpre hlen pm hclean
  have hstor := stor_of_processMessage_staticPrecomp hpre pm
  have hcode := code_of_processMessage_staticPrecomp hpre pm
  obtain ⟨hca, hck, hcl, hcc, hcr⟩ :=
    meta_of_processMessage_sha256_64_clean_noStateGas hpre hlen pm hclean hsg
  obtain ⟨hra, hrk, hre, hrc, hrr⟩ := Resume.call_ok_meta hsplit hclean
  have hlogs := Resume.call_logs hsplit
  simp only [hclean, Bool.false_eq_true, ↓reduceIte, hcl, List.append_nil] at hlogs
  have hmem := Resume.call_memory hsplit
  rw [hout, List.take_of_length_le (by rw [B256.length_toBytes])] at hmem
  have hst := Resume.call_state hsplit
  refine ⟨d, d.gasLeft, ⟨fun a => ?_, fun a => ?_, ?_, ?_, hlogs, (Resume.call_output hsplit).trans rfl, hre,
    (Resume.call_returnData hsplit).trans hout, hrc.trans (hcc.trans rfl),
    by rw [hrr, hcr, Int.add_zero]; rfl⟩, St.self hstk hmem⟩
  · exact (getStor_eq_of_state_eq hst a).trans (hstor a)
  · exact (getCode_eq_of_state_eq hst a).trans (hcode a)
  · rw [hra, hca, hashSet_union_self]; rfl
  · rw [hrk, hck, hashSet_union_self]; rfl

/-- **`STATICCALL` of the SHA-256 precompile, inverted, over a historical frame.**  Over a
64-byte input window at `ii` and a 32-byte output window at `oi`, with address 2 warm,
undelegated and a precompile of rules without state gas: a successful step either pushed the
failure flag `0`, or pushed `1` over a base `b'` that `ShaCallPost`-extends `b` with the digest
as return data, with the digest written over the (extended) output window. The access schedule
and the delegation flag are cased, never assumed: each of the four branches normalises to
`ri_staticcall_sha_of_charge`. -/
theorem ri_staticcall_shaH {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {g ii oi : B256} {d : Devm}
    (hnodeleg : getDelegatedCodeAddress (b.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ b.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (h : Ninst.Run sevm (St b (g :: 2 :: ii :: 64 :: oi :: 32 :: S) M G) (.exec .staticcall) d) :
    d.stack = 0 :: S ∨
      ∃ b' G', ShaCallPost b b' (Bytes.sha256 (M.read ii.toNat 64).1).toBytes ∧
        d = St b' (1 :: S) ((M.extends [⟨ii.toNat, 64⟩, ⟨oi.toNat, 32⟩]).write oi.toNat
          (Bytes.sha256 (M.read ii.toNat 64).1).toBytes) G' := by
  rcases h with ⟨xl, h_fill, pc, h_run⟩
  have hA : addAccessedAddress (St b S M G) 2 = St b S M G :=
    addAccessedAddress_eq_self_of_mem hwarm
  have hAD : sevm.benvStat.rules.gas.accessDelegation (St b S M G) 2 =
      ⟨false, 2, b.getCode 2, 0, St b S M G⟩ := by
    unfold GasSchedule.accessDelegation
    simp only [show (St b S M G).state.getCode 2 = b.getCode 2 from rfl, hnodeleg]
  simp only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.step, hsg,
    show (St b (g :: 2 :: ii :: 64 :: oi :: 32 :: S) M G).pop =
      .ok (g, St b (2 :: ii :: 64 :: oi :: 32 :: S) M G) from rfl,
    show (St b (2 :: ii :: 64 :: oi :: 32 :: S) M G).popToAdr =
      .ok ((2 : Adr), St b (ii :: 64 :: oi :: 32 :: S) M G) from rfl,
    show (St b (ii :: 64 :: oi :: 32 :: S) M G).popToNat =
      .ok (ii.toNat, St b (64 :: oi :: 32 :: S) M G) from rfl,
    show (St b (64 :: oi :: 32 :: S) M G).popToNat =
      .ok (64, St b (oi :: 32 :: S) M G) from rfl,
    show (St b (oi :: 32 :: S) M G).popToNat =
      .ok (oi.toNat, St b (32 :: S) M G) from rfl,
    show (St b (32 :: S) M G).popToNat = .ok (32, St b S M G) from rfl,
    Bind.bind, Except.bind] at h_run
  -- the four access/delegation branches normalise to one charged form
  cases hacc : sevm.benvStat.rules.access <;>
    cases hdel : sevm.benvStat.rules.delegationEnabled <;>
    simp only [hacc] at h_run
  all_goals
    first
      | simp only [ForkRules.accessDelegation_disabled hdel, hA] at h_run
      | simp only [ForkRules.accessDelegation_enabled hdel, hA, hAD] at h_run
    exact ri_staticcall_sha_of_charge _ hpre hsg h_run

/-- `ri_staticcall_shaH` recovers the modern `ri_staticcall_sha` statement on a covered fork. -/
theorem ri_staticcall_shaH_covered {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {g ii oi : B256} {d : Devm}
    (hnodeleg : getDelegatedCodeAddress (b.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ b.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hfork : CoveredFork sevm.benvStat.fork)
    (h : Ninst.Run sevm (St b (g :: 2 :: ii :: 64 :: oi :: 32 :: S) M G) (.exec .staticcall) d) :
    d.stack = 0 :: S ∨
      ∃ b' G', ShaCallPost b b' (Bytes.sha256 (M.read ii.toNat 64).1).toBytes ∧
        d = St b' (1 :: S) ((M.extends [⟨ii.toNat, 64⟩, ⟨oi.toNat, 32⟩]).write oi.toNat
          (Bytes.sha256 (M.read ii.toNat 64).1).toBytes) G' :=
  ri_staticcall_shaH hnodeleg hwarm hpre hfork.rules_stateGas_none h

end Blanc.Lift
