import Blanc.Lift.VyperArraySlot
import Blanc.Lift.InvWalkSha
import Blanc.Lift.MutableCallPost

/-!
# A value-0 `CALL` of the identity precompile

Vyper 0.2.x copies byte arrays (`concat`, the `raw_call` result) with a value-0 `CALL` to the
identity precompile at address 4: `CALL(gas, 4, 0, ii, is, oi, os)`.  Over a world where
address 4 is warm, undelegated and an enabled precompile (`IdReady`), a successful step either
pushed `0` (the depth limit, or an underfunded child), or pushed `1`, wrote (a prefix of) the
input window over the output window and made the input the return data, leaving storage, code,
access sets, logs, output and error unchanged (`ShaCallPost`, the precompile-neutral world
relation of `ExactWalkCutOps.lean`).

* `processMessage_identity_clean`: what a clean identity child is, for either call kind;
* `ri_call_identity`: the inversion of the step;
* `call_identity_step` (`Ninst.RunCompiled`) / `rxc_call_identity`: the forward step from a stack
  whose gas operand is the frame's whole remaining gas (the `GAS; CALL` idiom), at cost
  `100 + 15 + 3·⌈is/32⌉ + memExp` (warm access, the precompile's charge, the memory expansion
  of the two windows); the 63/64 forwarding returns every unspent unit.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- The identity precompile premises a frame's world carries. -/
structure IdReady (sevm : Sevm) (b : Devm) : Prop where
  nodeleg : getDelegatedCodeAddress (b.getCode 4) = none
  warm : (4 : Adr) ∈ b.accessedAddresses
  pre : decide (sevm.benvStat.rules.isPrecomp 4) = true
  fork : CoveredFork sevm.benvStat.fork

theorem IdReady.of_rel {sevm : Sevm} {b b' : Devm} (h : IdReady sevm b) (hr : BaseRel b b') :
    IdReady sevm b' :=
  ⟨by rw [hr.code]; exact h.nodeleg, by rw [hr.addrs]; exact h.warm, h.pre, h.fork⟩

/-- The identity precompile's charge on `n` input bytes. -/
def idCost (n : Nat) : Nat := 15 + 3 * ceilDiv n 32

/-- **A clean identity child**, for a value-0 message of either kind: it returned its calldata,
kept the parent's world and access sets, logged nothing, and was funded. -/
theorem processMessage_identity_clean
    {sevm : Sevm} {parent child : Devm} {gas : Nat} {calldata : Bytes} {stv st : Bool}
    {code : ByteArray} {xl : Xlot}
    (hpre : decide (sevm.benvStat.rules.isPrecomp 4) = true)
    (hpm : ProcessMessage
      (callMsg sevm parent gas 0 sevm.currentTarget 4 4 stv st calldata code false) xl
        (.ok child))
    (hclean : child.error.isSome = false) (hfork : CoveredFork sevm.benvStat.fork) :
    child.output = calldata ∧ child.state = parent.state ∧
      child.accessedAddresses = parent.accessedAddresses ∧
      child.accessedStorageKeys = parent.accessedStorageKeys ∧ child.logs = [] ∧
      child.createdAccounts = parent.createdAccounts ∧ idCost calldata.length ≤ gas := by
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
        refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, hgas⟩
        simp only [initEvm, initDevm, Devm.withOutput_logs]
        dsimp only [Devm.withGasLeft, Devm.setMach, Devm.logs, liftMachPure]
        split
        · rfl
        · rename_i heq
          exact absurd (heq.symm.trans hfork.rules_stateGas_none)
            (by simp only [reduceCtorEq, not_false_eq_true])
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

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- **A value-0 `CALL` of the identity precompile, inverted.**  A successful step either pushed
`0`, or pushed `1` over a base `b'` that `ShaCallPost`-extends `b` with the input window as
return data, the input written (truncated to `os`) over the extended output window. -/
theorem ri_call_identity {g ii is oi os : B256} {d : Devm} (hid : IdReady sevm b)
    (h : Ninst.Run sevm (St b (g :: 4 :: 0 :: ii :: is :: oi :: os :: S) M G) (.exec .call) d) :
    d.stack = 0 :: S ∨
      ∃ b' G', ShaCallPost b b' (M.read ii.toNat is.toNat).1 ∧
        d = St b' (1 :: S) ((M.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write
          oi.toNat ((M.read ii.toNat is.toNat).1.take os.toNat)) G' := by
  have hfork := hid.fork
  rcases h with ⟨xl, h_fill, pc, h_run⟩
  simp only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.step,
    Bind.bind, Except.bind, hfork.rules_stateGas_none] at h_run
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
  obtain ⟨hout, hcst, hca, hck, hcl, hcc, -⟩ :=
    processMessage_identity_clean hid.pre pm hclean hfork
  obtain ⟨hra, hrk, hre, hrc⟩ := Resume.call_ok_meta hsplit hclean
  have hlogs := Resume.call_logs hsplit
  simp only [hclean, Bool.false_eq_true, ↓reduceIte, hcl, List.append_nil] at hlogs
  have hmem := Resume.call_memory hsplit
  rw [hout] at hmem
  have hst := Resume.call_state hsplit
  refine ⟨d, d.gasLeft, ⟨fun a => ?_, fun a => ?_, ?_, ?_, hlogs,
    (Resume.call_output hsplit).trans rfl, hre, (Resume.call_returnData hsplit).trans hout,
    hrc.trans (hcc.trans rfl)⟩, St.self hstk hmem⟩
  · exact getStor_eq_of_state_eq (hst.trans hcst) a
  · exact getCode_eq_of_state_eq (hst.trans hcst) a
  · rw [hra, hca, hashSet_union_self]; rfl
  · rw [hrk, hck, hashSet_union_self]; rfl

/-- **A value-0 `CALL` of the identity precompile, forward**, from the `GAS; CALL` stack (the gas
operand is the whole remaining gas `G`): the step succeeds, pushes `1`, writes the input window
(truncated to `os`) over the extended output window, makes the input the return data, and costs
`100 + ext + idCost is` (warm access, the expansion charge `ext` of the two windows, the
precompile's charge).  `hfund` keeps the 63/64-forwarded gas above the precompile's charge. -/
theorem call_identity_step {g ii is oi os : B256} {ext : Nat} (hid : IdReady sevm b)
    (hdepth : sevm.depth ≠ 0) (hg : g = Nat.toB256 G)
    (hext : (St b S M G).extCost [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] = ext)
    (hfund : 100 + ext + 64 * idCost is.toNat ≤ G) (hbound : G < 2 ^ 256)
    (hroom : S.length < 1024) :
    ∃ b', ShaCallPost b b' (M.read ii.toNat is.toNat).1 ∧
      Ninst.RunCompiled sevm (St b (g :: 4 :: 0 :: ii :: is :: oi :: os :: S) M G) (.exec .call)
        (St b' (1 :: S) ((M.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write oi.toNat
          ((M.read ii.toNat is.toNat).1.take os.toNat)) (G - (100 + ext + idCost is.toNat))) := by
  subst hg
  have hfork := hid.fork
  set devm := St b (Nat.toB256 G :: 4 :: 0 :: ii :: is :: oi :: os :: S) M G with hdevm
  have hbase : devm.setMach ⟨S, devm.memory, devm.gasLeft, devm.stateGas⟩ = St b S M G := rfl
  have hd0 : addAccessedAddress (St b S M G) 4 = St b S M G :=
    addAccessedAddress_eq_self_of_mem hid.warm
  have hdel : accessDelegation (addAccessedAddress
      (devm.setMach ⟨S, devm.memory, devm.gasLeft, devm.stateGas⟩) (4 : B256).toAdr)
      (4 : B256).toAdr = ⟨false, 4, b.getCode 4, 0, St b S M G⟩ := by
    rw [hbase, show (4 : B256).toAdr = 4 from rfl]
    unfold accessDelegation
    simp only [hd0, show (St b S M G).state.getCode 4 = b.getCode 4 from rfl, hid.nodeleg]
  have hacc : accessCost (4 : B256).toAdr
      (devm.setMach ⟨S, devm.memory, devm.gasLeft, devm.stateGas⟩).accessedAddresses + 0 =
        gasWarmAccess := by
    rw [hbase, show (4 : B256).toAdr = 4 from rfl]
    unfold accessCost
    rw [ite_eq_left (show (4 : Adr) ∈ (St b S M G).accessedAddresses from hid.warm)]
    rfl
  obtain ⟨mcc, mcs, hsplit⟩ : ∃ mcc mcs,
      calculateMsgCallGas 0 (Nat.toB256 G).toNat (St b S M G).gasLeft ext gasWarmAccess =
        ⟨mcc, mcs⟩ := ⟨_, _, rfl⟩
  obtain ⟨hmcs, hcross, hgasout⟩ :
      idCost is.toNat ≤ mcs ∧ mcc + ext ≤ G ∧
        G - (mcc + ext) + (mcs - idCost is.toNat) = G - (100 + ext + idCost is.toNat) := by
    have hGnat : (Nat.toB256 G).toNat = G := B256.toNat_toB256_of_lt hbound
    rw [show (St b S M G).gasLeft = G from rfl] at hsplit
    unfold calculateMsgCallGas at hsplit
    rw [hGnat, ite_eq_right (by simp only [gasWarmAccess]; omega)] at hsplit
    simp only [gasWarmAccess] at hsplit
    have hmin : min G (except64th (G - ext - 100)) = except64th (G - ext - 100) := by
      have h1 : except64th (G - ext - 100) ≤ G := by unfold except64th; omega
      rw [Nat.min_eq_right h1]
    rw [hmin] at hsplit
    have h1 : except64th (G - ext - 100) + 100 = mcc := congrArg Prod.fst hsplit
    have h2 : except64th (G - ext - 100) + 0 = mcs := congrArg Prod.snd hsplit
    unfold except64th at h1 h2
    exact ⟨by omega, by omega, by omega⟩
  let p := callSpawnParent (St b S M G) (mcc + ext) ii.toNat is.toNat oi.toNat os.toNat
  let msg := callSpawnMsg sevm p mcs 4 4 ii.toNat is.toNat (b.getCode 4) false
  have hbt : msg.benvAfterTransfer = .ok msg.benv := Msg.benvAfterTransfer_of_value_zero rfl
  have hpre' : (!((msg.withBenv msg.benv).disablePrecompiles) &&
      decide ((msg.withBenv msg.benv).benv.stat.rules.isPrecomp 4)) = true := by
    change decide (sevm.benvStat.rules.isPrecomp 4) = true
    exact hid.pre
  let cev := initEvm (msg.withBenv msg.benv)
  have hlen : cev.sta.data.length = is.toNat := by
    change (p.memory.data.sliceD ii.toNat is.toNat 0).length = is.toNat
    rw [Array.sliceD_eq_map, List.length_map, List.length_range]
  let child := (cev.dyna.withGasLeft (cev.dyna.gasLeft - idCost is.toNat)).withOutput cev.sta.data
  have hexec : executePrecomp cev 4 = .ok child := by
    change applyPrecompResult cev (executeId cev) = _
    unfold executeId PrecompResult.chargeGas
    dsimp only
    rw [hlen, ite_eq_left (show 15 + 3 * ceilDiv is.toNat 32 ≤ cev.dyna.gasLeft from hmcs)]
    rfl
  have henter : (Frame.ofCall msg).enter = .done ((Frame.ofCall msg).settle (.ok child)) := by
    rw [Frame.enter_eq_done_executePrecomp (f := Frame.ofCall msg) hbt rfl hpre']
    exact congrArg _ (congrArg _ hexec)
  have hsettle : (Frame.ofCall msg).settle (.ok child) = .ok child := by
    rw [Frame.settle_eq_settleMsg_handleErrorWith, executeCode.handleErrorWith_ok]
    simp only [Frame.settleMsg, Frame.ofCall, Bool.false_eq_true, ↓reduceIte,
      processMessage.settle, initEvm, initDevm, Msg.withBenv_gas, Msg.withBenv_stat_rules,
      Except.bind_ok, ite_eq_right_iff, Except.ok.injEq, child, cev]
    intro h
    cases h
  have hproom : p.stack.length < 1024 := hroom
  let post := (((incorporateChildOnSuccess p child child.output).setMach
      ⟨1 :: p.stack, p.memory, p.gasLeft + child.gasLeft, p.stateGas⟩).memWrite
        oi.toNat (child.output.take os.toNat))
  have hres : Resume.run (.call p oi.toNat os.toNat) ((Frame.ofCall msg).settle (.ok child)) =
      .ok post := by
    rw [hsettle, Resume.run_call_ok (by rfl) hproom]
    rfl
  have hrun : Ninst.ChildlessRunCompiled sevm devm (.exec .call) post :=
    Ninst.childlessRunCompiled_exec_doneFrame
      (Xinst.step_call_zero_value_spawn hfork rfl (by exact hext) hdel hacc hsplit
        (by rw [show (St b S M G).gasLeft = G from rfl]; exact hcross) hdepth) henter hres
  have hcevdata : cev.sta.data = (M.read ii.toNat is.toNat).1 := rfl
  have hchildState : child.state = b.state := rfl
  refine ⟨post, ⟨fun a => ?_, fun a => ?_, ?_, ?_, ?_, rfl, rfl, hcevdata, rfl⟩, ?_⟩
  · change (child.state.get a).stor = (b.state.get a).stor
    rw [hchildState]
  · change child.state.getCode a = b.state.getCode a
    rw [hchildState]
  · change p.accessedAddresses.union child.accessedAddresses = b.accessedAddresses
    change b.accessedAddresses.union b.accessedAddresses = b.accessedAddresses
    rw [hashSet_union_self]
  · change p.accessedStorageKeys.union child.accessedStorageKeys = b.accessedStorageKeys
    change b.accessedStorageKeys.union b.accessedStorageKeys = b.accessedStorageKeys
    rw [hashSet_union_self]
  · change p.logs ++ child.logs = b.logs
    have hsg : sevm.benvStat.rules.stateGas = none := hfork.rules_stateGas_none
    have hsg' : msg.benv.stat.rules.stateGas = none := hsg
    have hcl : child.logs = [] := by
      change cev.dyna.logs = []
      dsimp only [cev, initEvm, initDevm, Msg.withBenv_gas, Msg.withBenv_stat_rules]
      rw [hsg']
      rfl
    rw [hcl, List.append_nil]
    rfl
  · have e : post = St post (1 :: S) ((M.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write
        oi.toNat ((M.read ii.toNat is.toNat).1.take os.toNat)) post.gasLeft := St.self rfl rfl
    have hg : post.gasLeft = G - (100 + ext + idCost is.toNat) := by
      change p.gasLeft + child.gasLeft = _
      change G - (mcc + ext) + (mcs - idCost is.toNat) = _
      exact hgasout
    rw [hg] at e
    rw [← e]
    exact hrun.toRunCompiled

/-- `call_identity_step` as a walk step of an exact cut run. -/
theorem rxc_call_identity {fs : List SFunc} {C : List Nat} {f : SFunc} {r : Seg}
    {g ii is oi os : B256} {ext : Nat} (hid : IdReady sevm b)
    (hdepth : sevm.depth ≠ 0) (hg : g = Nat.toB256 G)
    (hext : (St b S M G).extCost [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] = ext)
    (hfund : 100 + ext + 64 * idCost is.toNat ≤ G) (hbound : G < 2 ^ 256)
    (hroom : S.length < 1024)
    (k : ∀ b', ShaCallPost b b' (M.read ii.toNat is.toNat).1 →
      SFunc.RunExactCut fs sevm C
        (St b' (1 :: S) ((M.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write oi.toNat
          ((M.read ii.toNat is.toNat).1.take os.toNat)) (G - (100 + ext + idCost is.toNat))) f r) :
    SFunc.RunExactCut fs sevm C (St b (g :: 4 :: 0 :: ii :: is :: oi :: os :: S) M G)
      (.next (.exec .call) f) r := by
  obtain ⟨b', hpost, hrun⟩ := call_identity_step hid hdepth hg hext hfund hbound hroom
  exact .next hrun (k b' hpost)

end Blanc.Lift
