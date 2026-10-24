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
  prefix form, then the charged tail `ri_staticcall_sha_of_charge`;
* `ric_shaCallH`, `ric_copy_shaH`, `ric_pack_shaH` — the solc packed-SHA site
  (call, copy and pack) over the same premises;
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

/-! ## The solc packed-SHA site over a historical frame -/

section CopyH

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {r : Seg}
  {R : List B256} {M : Mem} {G : Nat} {e0 e1 r0 r1 : UInt8} {k : Nat} {X T : SFunc}

/-- **The precompile call and its two checks, inverted, over a historical frame.**  From the stack the merge leaves,
with the free pointer `d` (word-aligned, past the scratch words) and memory covering the input
window: the call succeeded (its failure arm is `noOk`; the size check cannot fail), the digest of the 64 bytes at `d`
was written at `d`, and control passes to `T` with the returned size and `d` on the stack. -/
theorem ric_shaCallH {img : Bytes} {n d : Nat} {x1 x3 x4 : B256} {c0 c1 v0 v1 : UInt8}
    {fail1 fail2 : SFunc}
    (hf1 : fail1.noOk = true)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = n) (hn : n % 32 = 0)
    (hdn : d + 64 ≤ n) (hd96 : 96 ≤ d) (hd32 : d % 32 = 0) (hdb : d + 64 < 2 ^ 256)
    (hfp : img.sliceD 64 32 0 = (Nat.toB256 d).toBytes)
    (hnodeleg : getDelegatedCodeAddress (b.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ b.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (run : SFunc.RunCut fs sevm C
      (St b (Bytes.toB256 [0x20] :: Nat.toB256 64 :: x1 :: Nat.toB256 d :: x3 :: x4 :: 2 :: R)
        M G) (shaCallTree c0 c1 v0 v1 fail1 fail2 T) r) :
    ∃ b' G', ShaCallPost b b' (Bytes.sha256 (M.read d 64).1).toBytes ∧
      SFunc.RunCut fs sevm C (St b' (Nat.toB256 32 :: Nat.toB256 d :: R)
        (M.write d (Bytes.sha256 (M.read d 64).1).toBytes) G') T r := by
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  have hd : (Nat.toB256 d).toNat = d := toNat_toB256' (by omega)
  unfold shaCallTree at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_mload s1
  rw [h40, read_word hr 64 hfp, read_covered hs hn (by omega)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨w, G18, rfl⟩ := ri_gas s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  have e64 : Nat.toB256 d + Nat.toB256 64 - Nat.toB256 d = 64 := by
    rw [toB256_add_toB256 hdb, toB256_sub_toB256 (by omega) hdb, show d + 64 - d = 64 by omega]
    decide
  have e32 : Bytes.toB256 [32] = 32 := by decide
  have s1' : Ninst.Run sevm (St b (w :: 2 :: Nat.toB256 d :: 64 :: Nat.toB256 d :: 32 ::
      (Nat.toB256 d + Nat.toB256 64) :: 2 :: R) M G18) (.exec .staticcall) d1 := by
    rw [← e64, ← e32]; exact s1
  clear s1
  have hcov : M.extends [⟨d, 64⟩, ⟨d, 32⟩] = M :=
    Mem.extends_covered (by rw [hs]; exact memExtsSize_two_covered hn (by omega) (by omega))
  rcases ri_staticcall_shaH hnodeleg hwarm hpre hsg s1' with hfail | ⟨b', G19, hpost, rfl⟩
  · -- the failure flag: the first check's arm
    rw [St.self hfail rfl] at run
    obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_iszero s2
    obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_dup rfl s2
    obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_iszero s2
    obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_push s2
    rw [show B256.eqCheck (B256.eqCheck (0 : B256) 0) 0 = 0 by decide] at run
    rcases ric_branch run with ⟨-, G24, run⟩ | ⟨hw, -⟩
    · exact (run.false_of_noOk hf1).elim
    · exact absurd rfl hw
  rw [hd, hcov] at run
  rw [hd] at hpost
  set sha := (Bytes.sha256 (M.read d 64).1).toBytes with hsha
  have hr' : Mem.Reads (M.write d sha) (Bytes.writeAt img d sha) := hr.write hwf d sha
  have hs' : (M.write d sha).size = n := by
    rw [hsha, Mem.size_write_word_aligned (by omega) hd32]; omega
  have hfp' : (Bytes.writeAt img d sha).sliceD 64 32 0 = (Nat.toB256 d).toBytes := by
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hfp]
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_iszero s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_dup rfl s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_iszero s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_push s2
  rw [show B256.eqCheck (B256.eqCheck (1 : B256) 0) 0 = 1 by decide] at run
  rcases ric_branch run with ⟨hw, -⟩ | ⟨-, G24, run⟩
  · exact absurd hw (by decide)
  obtain ⟨G25, run⟩ := ric_dest run
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_pop s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G27, rfl⟩ := ri_pop s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G28, rfl⟩ := ri_pop s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G29, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_mload s2
  rw [h40, read_word hr' 64 hfp', read_covered hs' hn (by omega)] at run
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G31, rfl⟩ := ri_returndatasize s2
  rw [hpost.returnData, B256.length_toBytes] at run
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G32, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G33, rfl⟩ := ri_dup rfl s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G34, rfl⟩ := ri_lt s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G35, rfl⟩ := ri_iszero s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G36, rfl⟩ := ri_push s2
  have hlt : B256.ltCheck (Nat.toB256 32) (Bytes.toB256 [0x20]) = 0 := by
    rw [show Bytes.toB256 [0x20] = Nat.toB256 32 by decide, lt_toB256 (by norm_num only) (by norm_num only)]
    simp only [lt_self_iff_false, ↓reduceIte]
  rw [hlt, show B256.eqCheck (0 : B256) 0 = 1 by decide] at run
  rcases ric_branch run with ⟨hw, -⟩ | ⟨-, G37, run⟩
  · exact absurd hw (by decide)
  exact ⟨b', G37, hpost, run⟩

/-- **Copy, merge and call, inverted, over a historical frame** (the converse of `copy_sha_gen`): from the copy loop's
head with the two words `w1`, `w2` at `s` and `s + 0x20` to be copied to the free pointer
`d = s + 0x40`, every successful cut run makes the two copy passes, the merge and the
precompile call, and continues with `T` over a base that `ShaCallPost`-extends `b` with the
digest `sha256 (w1 ‖ w2)`, memory reading as `shaImg img d w1 w2` of size `max n (d + 0x60)`,
and the returned size and `d` on the stack.  The head's own exit `X` is never taken. -/
theorem ric_copy_shaH {img : Bytes} {n s d : Nat} {w1 w2 x1 x3 x4 : B256}
    {c0 c1 v0 v1 : UInt8} {fail1 fail2 : SFunc}
    (hk : fs[k]? = some (mcpyTree e0 e1 r0 r1 k
      (mergeTree (shaCallTree c0 c1 v0 v1 fail1 fail2 T))))
    (hkC : k ∉ C) (hf1 : fail1.noOk = true)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = n) (hn : n % 32 = 0)
    (hdn : d ≤ n) (hsd : s + 64 = d) (hd32 : d % 32 = 0) (hd96 : 96 ≤ s)
    (hdb : n + 1000 < 2 ^ 256) (hfp : img.sliceD 64 32 0 = (Nat.toB256 d).toBytes)
    (hw1 : img.sliceD s 32 0 = w1.toBytes) (hw2 : img.sliceD (s + 32) 32 0 = w2.toBytes)
    (hnodeleg : getDelegatedCodeAddress (b.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ b.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (run : SFunc.RunCut fs sevm C
      (St b (Nat.toB256 s :: Nat.toB256 d :: Nat.toB256 64 :: Nat.toB256 64 :: x1 ::
        Nat.toB256 d :: x3 :: x4 :: 2 :: R) M G) (mcpyTree e0 e1 r0 r1 k X) r) :
    ∃ b' M' G', ShaCallPost b b' (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes ∧
      Mem.Wf M' ∧ Mem.Reads M' (shaImg img d w1 w2) ∧ M'.size = max n (d + 96) ∧
      SFunc.RunCut fs sevm C (St b' (Nat.toB256 32 :: Nat.toB256 d :: R) M' G') T r := by
  set n1 := max n (d + 32) with hn1
  set n2 := max n (d + 64) with hn2
  set n3 := max n (d + 96) with hn3
  have hw1' : (M.read s 32).1 = w1.toBytes := by rw [hr.read, hw1]
  set M5 := M.write d (M.read s 32).1 with hM5
  have hwf5 : Mem.Wf M5 := hwf.write _ _
  have hr5 : Mem.Reads M5 (Bytes.writeAt img d w1.toBytes) := by
    rw [hM5, hw1']; exact hr.write hwf _ _
  have hs5 : M5.size = n1 := by
    rw [hM5, hw1', Mem.size_write_word_aligned (by omega) (by omega)]; omega
  have hw2' : (M5.read (s + 32) 32).1 = w2.toBytes := by
    rw [hr5.read, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hw2]
  set M6 := M5.write (d + 32) (M5.read (s + 32) 32).1 with hM6
  have hwf6 : Mem.Wf M6 := hwf5.write _ _
  have hr6 : Mem.Reads M6 (copyImg2 img d w1 w2) := by
    rw [hM6, hw2']; exact hr5.write hwf5 _ _
  have hs6 : M6.size = n2 := by
    rw [hM6, hw2', Mem.size_write_word_aligned (by omega) (by omega)]; omega
  set M7 := (M6.read (d + 64) 32).2.write (d + 64) (M6.read (d + 64) 32).1 with hM7
  have hs6' : (M6.read (d + 64) 32).2.size = n3 := by
    rw [read_ext_size hs6 (by omega) (by omega)]; omega
  have hwf7 : Mem.Wf M7 := (hwf6.extend _ _).write _ _
  have hr7 : Mem.Reads M7 (copyImg2 img d w1 w2) := by
    rw [hM7, hr6.read]
    exact Mem.Reads.write_self (hwf6.extend _ _) (hr6.extend _ _) _
  have hs7 : M7.size = n3 := by
    rw [hM7, ← toBytes_read, Mem.size_write_word_aligned (by omega) (by omega), hs6']; omega
  have hin : (M7.read d 64).1 = w1.toBytes ++ w2.toBytes := by
    rw [hr7.read, copyImg2_input]
  have hw7 : (copyImg2 img d w1 w2).sliceD 64 32 0 = (Nat.toB256 d).toBytes := by
    rw [copyImg2_word64 (by omega), hfp]
  -- the two copy passes and the exit test
  obtain ⟨G1, run⟩ := ric_mcpy_iter (s := s) (d := d) (l := 64) (n := n) (by omega) (by omega)
    hs hn (by omega) (by omega) (by omega) hk hkC run
  rw [show (64 : Nat) - 32 = 32 from rfl] at run
  obtain ⟨G2, run⟩ := ric_mcpy_iter (s := s + 32) (d := d + 32) (l := 32) (n := n1) (by omega)
    (by omega) hs5 (by omega) (by omega) (by omega) (by omega) hk hkC run
  rw [show (32 : Nat) - 32 = 0 from rfl, show s + 32 + 32 = s + 64 by omega,
    show d + 32 + 32 = d + 64 by omega] at run
  obtain ⟨G3, run⟩ := ric_mcpy_exit (s := s + 64) (d := d + 64) (l := 0) (by omega) run
  -- the merge
  obtain ⟨G4, run⟩ := ric_merge0 (s := s + 64) (d := d + 64) (n := n2) hs6 (by omega) (by omega)
    (by omega) (by omega) run
  -- the call
  obtain ⟨b', G5, hpost, run⟩ := ric_shaCallH (img := copyImg2 img d w1 w2) (n := n3) hf1 hwf7
    hr7 hs7 (by omega) (by omega) (by omega) hd32 (by omega) hw7 hnodeleg hwarm hpre hsg
    run
  rw [hin] at hpost run
  exact ⟨b', _, G5, hpost, hwf7.write _ _, hr7.write hwf7 d _,
    by rw [Mem.size_write_word_aligned (by omega) (by omega), hs7]; omega, run⟩

end CopyH

section PackH

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {r : Seg}
  {R : List B256} {M : Mem} {G : Nat} {e0 e1 r0 r1 : UInt8} {k : Nat} {X T : SFunc}

/-- **Pack two words, copy, merge and call, inverted, over a historical frame** (the converse of `packed_sha_pair`):
from `bw :: a :: 2` over the free pointer `f`, every successful cut run stores `a`, `bw` at
`f + 0x20`, `f + 0x40` with the length at `f` and the free pointer `f + 0x60`, then makes the
copy site of `ric_copy_shaH`, continuing with `T` over the digest `sha256 (a ‖ bw)`. -/
theorem ric_pack_shaH {img : Bytes} {n f : Nat} {a bw : B256}
    {c0 c1 v0 v1 : UInt8} {fail1 fail2 : SFunc}
    (hk : fs[k]? = some (mcpyTree e0 e1 r0 r1 k
      (mergeTree (shaCallTree c0 c1 v0 v1 fail1 fail2 T))))
    (hkC : k ∉ C) (hf1 : fail1.noOk = true)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = n) (hn : n % 32 = 0)
    (h96 : 96 ≤ n) (hnf : n ≤ f + 96) (hf32 : f % 32 = 0) (hf96 : 96 ≤ f)
    (hfb : f + 2000 < 2 ^ 256) (hfp : img.sliceD 64 32 0 = (Nat.toB256 f).toBytes)
    (hnodeleg : getDelegatedCodeAddress (b.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ b.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (run : SFunc.RunCut fs sevm C (St b (bw :: a :: 2 :: R) M G)
      (pack2Tree (mcpyTree e0 e1 r0 r1 k X)) r) :
    ∃ b' M' G', ShaCallPost b b' (Bytes.sha256 (a.toBytes ++ bw.toBytes)).toBytes ∧
      Mem.Wf M' ∧ Mem.Reads M' (shaImg (packImg img f a bw) (f + 96) a bw) ∧
      M'.size = f + 192 ∧
      SFunc.RunCut fs sevm C (St b' (Nat.toB256 32 :: Nat.toB256 (f + 96) :: R) M' G') T r := by
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  have tf : (Nat.toB256 f).toNat = f := toNat_toB256' (by omega)
  have tf32 : (Nat.toB256 (f + 32)).toNat = f + 32 := toNat_toB256' (by omega)
  have tf64 : (Nat.toB256 (f + 64)).toNat = f + 64 := toNat_toB256' (by omega)
  set M1 := M.write (f + 32) a.toBytes with hM1
  set M2 := M1.write (f + 64) bw.toBytes with hM2
  set M3 := M2.write f (Nat.toB256 64).toBytes with hM3
  set M4 := M3.write 64 (Nat.toB256 (f + 96)).toBytes with hM4
  have hs1 : M1.size = max n (f + 64) := by
    rw [hM1, Mem.size_write_word_aligned (by omega) (by omega)]; omega
  have hs2 : M2.size = f + 96 := by
    rw [hM2, Mem.size_write_word_aligned (by omega) (by omega)]; omega
  have hs3 : M3.size = f + 96 := by
    rw [hM3, Mem.size_write_word_aligned (by omega) (by omega)]; omega
  have hs4 : M4.size = f + 96 := by
    rw [hM4, Mem.size_write_word_aligned (by omega) (by omega)]; omega
  have hwf1 : Mem.Wf M1 := hwf.write _ _
  have hwf2 : Mem.Wf M2 := hwf1.write _ _
  have hwf3 : Mem.Wf M3 := hwf2.write _ _
  have hwf4 : Mem.Wf M4 := hwf3.write _ _
  have hr1 := hr.write hwf (f + 32) a.toBytes
  have hr2 := hr1.write hwf1 (f + 64) bw.toBytes
  have hr3 := hr2.write hwf2 f (Nat.toB256 64).toBytes
  have hr4 : Mem.Reads M4 (packImg img f a bw) := hr3.write hwf3 64 _
  have hfp2 : (Bytes.writeAt (Bytes.writeAt img (f + 32) a.toBytes) (f + 64)
      bw.toBytes).sliceD 64 32 0 = (Nat.toB256 f).toBytes := by
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hfp]
  unfold pack2Tree at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h40, read_word hr 64 hfp, read_covered hs hn (by omega)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 (f + 32))
    (push20_add (by omega)) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [tf32, ← hM1] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 (f + 64))
    (push20_add' rfl (by omega)) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [tf64, ← hM2] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 (f + 96))
    (push20_add' rfl (by omega)) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h40, read_word hr2 64 hfp2, read_covered hs2 (by omega) (by omega)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 96)
    (sub_toB256' (by omega) (by omega) (by omega)) (ri_sub s1)
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 64)
    (by decide) (ri_sub s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [tf, ← hM3] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [h40, ← hM4] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h40, read_word hr4 64 (packImg_word64 hf96), read_covered hs4 (by omega) (by omega)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [tf, read_word hr4 f (packImg_len hf96), read_covered hs4 (by omega) (by omega)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 (f + 32))
    (push20_add (by omega)) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨b', M', G', hpost, hwf', hr', hs', run⟩ := ric_copy_shaH (s := f + 32) (d := f + 96)
    (n := f + 96) hk hkC hf1 hwf4 hr4 hs4 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (packImg_word64 hf96) (packImg_a hf96)
    (by rw [show f + 32 + 32 = f + 64 by omega]; exact packImg_b hf96)
    hnodeleg hwarm hpre hsg run
  exact ⟨b', M', G', hpost, hwf', hr', by rw [hs']; omega, run⟩

end PackH

end Blanc.Lift
