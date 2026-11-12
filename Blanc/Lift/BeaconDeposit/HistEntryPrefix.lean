import Batteries.Tactic.OpenPrivate
import Blanc.Lift.BeaconDeposit.HistDeployment
import Blanc.ExecutionInOwnCode
import Blanc.ExecutionAccountingPositionalHistory
import Blanc.Lift.Quiet

namespace Blanc.Lift.BeaconDeposit

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

open private beacon_coreIn from Blanc.Lift.BeaconDeposit.HistCommittedHistory

private theorem classification_ownSpawns (ca : Adr) : OwnSpawnsIn ca code := by
  intro root node x pc installed _ hsg chain instruction
  exact Or.inr (Or.inl (parentPrefix_exec_staticcallH pc installed hsg chain instruction))

private theorem classification_admitted {B : BlockChain} (d : BeaconDeploymentTo B) :
    d.trace.FrameAdmitted Creation.depositAddress beaconEntry := by
  let historical := (d.dc.step d.first).append d.tail
  have initial : beaconSpec.StateInv Creation.depositAddress d.D.state :=
    ⟨by rw [d.deployed.1]; rfl, trivial, ⟨[], d.deployed.2⟩⟩
  have rewards := historical.rewardCreditsFunded BodyStageCapabilities.historical
  obtain ⟨left, atPrague, emptyPrague⟩ := configuredHistoryIn_environment historical
    (d.anchors.historicalOpenings d.dc d.first d.tail)
    (fun p _ => d.anchors.historicalPragueNoAuthorityAt d.dc d.first d.tail p.1)
    d.checkpointEmpty (d.anchors.historicalPragueNoAuthorityAt d.dc d.first d.tail 2)
    d.historicalNoFrame rewards initial
  have codePrague := ContractSpecSem.StateInv.getCode_eq_of_image (C := code) rfl atPrague
  have avoid := d.modern.systemCreateAvoid d.anchors.pragueInstalled d.modernSystemNoAuthority
  have right := beaconEntry_of_env d.modern d.modern.frameAdmitted_calldata
    (system_of_installed d.modern d.anchors.pragueInstalled d.modernSystemNoAuthority
      avoid.2 codePrague) emptyPrague d.modernNoAuthority d.modernNoFrame
  rw [d.trace.frameAdmitted_iff_rawFrames]
  intro root member target
  change root ∈ (historical.append d.modern.toHistForkIn).rawFrames at member
  rw [ConfiguredHistoryTraceIn.rawFrames_append,
    ConfiguredHistoryTrace.toHistForkIn_rawFrames] at member
  rcases List.mem_append.mp member with member | member
  · exact (historical.frameAdmitted_iff_rawFrames _ _).mp left root member target
  · exact (d.modern.frameAdmitted_iff_rawFrames _ _).mp right root member target

private theorem classification_frame_facts {B : BlockChain} (d : BeaconDeploymentTo B)
    (idx : Nat) (fr : Exec.Frame) (hlookup : d.trace.settledFrames[idx]? = some fr)
    (target : fr.sevm.currentTarget = depositContractAddress) :
    fr.pc = 0 ∧ HistFork fr.sevm.benvStat.fork ∧ fr.sevm.code = code ∧
    Exec.FreshEntry fr.sevm fr.pre ∧ fr.sevm.data.length < 2 ^ 256 ∧
    ShaReadyRules fr.sevm fr.pre := by
  have member : fr ∈ d.trace.settledFrames := List.mem_of_getElem? hlookup
  have atCreation : fr.sevm.currentTarget = Creation.depositAddress := target
  have installed : some (d.D.state.getCode Creation.depositAddress).toList = beaconSem.image := by
    rw [d.deployed.1]; rfl
  have own := d.trace.settled_ownCodeIn beaconSem Creation.depositAddress
    beaconInstalledCertH.nonempty beaconInstalledCertH.notDelegation
    (classification_ownSpawns Creation.depositAddress) BodyStageCapabilities.historical
    (d.trace.rewardCreditsFunded BodyStageCapabilities.historical) installed
    beaconInstalledCertH.runtimeSafety rfl fr member
  have raw := d.trace.mem_rawFrames_of_mem_settledFrames fr member
  have ready := (d.trace.frameAdmitted_iff_rawFrames _ _).mp
    (classification_admitted d) _ raw atCreation
  have fresh := (d.trace.frameAdmitted_iff_rawFrames _ _).mp
    (d.trace.freshFrameAdmitted Creation.depositAddress) _ raw atCreation
  refine ⟨own.2.1, own.2.2.1, own.2.2.2.2 atCreation, fresh, ready.1, ?_⟩
  exact ⟨fun _ => ready.2.1, ready.2.2, isPrecomp_two_hist own.2.2.1,
    own.2.2.2.1, own.2.2.1.bal_none⟩

/-! ## Refined certificate pinning address `2` at every `STATICCALL` -/

private def staticTwoNode (es : List Entry) : List AVal → SFunc → Bool
  | a, .next (.exec .staticcall) f =>
    (match a with
     | _ :: .const c :: _ :: _ :: _ :: _ :: _ => c == 2
     | _ => false) &&
    match absNinst (.exec .staticcall) a with
    | some a' => staticTwoNode es a' f
    | none => false
  | a, .next n f =>
    match absNinst n a with
    | some a' => staticTwoNode es a' f
    | none => true
  | a, .dest f => staticTwoNode es a f
  | _ :: _ :: a', .branchTo f _ => staticTwoNode es a' f
  | _ :: _ :: a', .branch f g => staticTwoNode es a' f && staticTwoNode es a' g
  | _ :: a', .callNext k f =>
    match es[k]? with
    | some e => staticTwoNode es (List.replicate e.rets .unk ++ a'.drop e.frame.length) f
    | none => true
  | a, .pcAt p f => staticTwoNode es (.const (Nat.toB256 p) :: a) f
  | _, _ => true

private def cert2Slots : Nat → List Nat
  | 12 | 16 | 20 | 22 | 27 | 28 | 30 => [8]
  | 14 | 17 => [8, 9]
  | 15 | 19 => [8, 10]
  | 18 => [10, 12]
  | 29 => [10]
  | _ => []

private def cert2 : Cert :=
  cert.zipIdx.map fun ((e, f), i) =>
    ({ e with frame := e.frame.zipIdx.map fun (v, j) =>
        if j ∈ cert2Slots i then .const 2 else v }, f)

private theorem cert2_fast_left :
    ((cert2.take 18).all fun (e, f) =>
      checkNodeT code 13 codeTries.bytes cert2.entries e.rets e.pc e.frame f &&
      staticTwoNode cert2.entries e.frame f) = true := by
  decide +kernel

private theorem cert2_fast_right :
    ((cert2.drop 18).all fun (e, f) =>
      checkNodeT code 13 codeTries.bytes cert2.entries e.rets e.pc e.frame f &&
      staticTwoNode cert2.entries e.frame f) = true := by
  decide +kernel

private theorem cert2_all_fast :
    (cert2.all fun (e, f) =>
      checkNodeT code 13 codeTries.bytes cert2.entries e.rets e.pc e.frame f &&
      staticTwoNode cert2.entries e.frame f) = true := by
  rw [← List.take_append_drop 18 cert2, List.all_append, Bool.and_eq_true]
  exact ⟨cert2_fast_left, cert2_fast_right⟩

private theorem cert2_check : Cert.check code cert2 = true := by
  unfold Cert.check
  rw [Bool.and_eq_true]
  refine ⟨by decide +kernel, List.all_eq_true.mpr ?_⟩
  intro ⟨e, f⟩ hp
  have hfast := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp cert2_all_fast (e, f) hp)
  dsimp only
  rw [← checkNodeT_eq codeTries]
  exact hfast.1

private theorem cert2_entry_staticTwo {k : Nat} {e : Entry} {g : SFunc}
    (he : cert2.entries[k]? = some e) (hg : cert2.prog[k]? = some g) :
    staticTwoNode cert2.entries e.frame g = true := by
  have hk : k < cert2.length := by
    have hlt := (List.getElem?_eq_some_iff.mp he).1
    simpa only [Cert.entries, List.length_map] using hlt
  have he' : cert2.entries[k]? = some (cert2[k]).1 := by
    simp only [Cert.entries, List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some]
  have hg' : cert2.prog[k]? = some (cert2[k]).2 := by
    simp only [Cert.prog, List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some]
  have ee := Option.some.inj (he.symm.trans he')
  have eg := Option.some.inj (hg.symm.trans hg')
  have hmem : cert2[k] ∈ cert2 := List.getElem_mem hk
  have hfast := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp cert2_all_fast cert2[k] hmem)
  rw [ee, eg]
  exact hfast.2

private def CursorStaticTwo (κ : Cursor) : Prop :=
  staticTwoNode cert2.entries κ.a κ.f = true ∧
    ∀ k ∈ κ.K, staticTwoNode cert2.entries (List.replicate k.rets .unk ++ k.a) k.f = true

private theorem CursorStaticTwo.step {before after : Cursor}
    (step : SStep cert2 before after) (holds : CursorStaticTwo before) :
    CursorStaticTwo after := by
  obtain ⟨hf, hK⟩ := holds
  cases step with
  | @next n f pc a a' m K hn =>
      refine ⟨?_, hK⟩
      cases n with
      | exec x =>
          cases x with
          | staticcall =>
              simp only [staticTwoNode, hn, Bool.and_eq_true] at hf
              exact hf.2
          | _ =>
              simp only [staticTwoNode, hn] at hf
              exact hf
      | _ =>
          simp only [staticTwoNode, hn] at hf
          exact hf
  | dest | pcAt =>
      exact ⟨hf, hK⟩
  | toZero =>
      simp only [staticTwoNode] at hf
      exact ⟨hf, hK⟩
  | zero =>
      simp only [staticTwoNode, Bool.and_eq_true] at hf
      exact ⟨hf.1, hK⟩
  | succ =>
      simp only [staticTwoNode, Bool.and_eq_true] at hf
      exact ⟨hf.2, hK⟩
  | toSucc he hg | jump he hg =>
      exact ⟨cert2_entry_staticTwo he hg, hK⟩
  | call κc he hg hcf hca _ hcr =>
      refine ⟨cert2_entry_staticTwo he hg, fun k hk => ?_⟩
      rcases List.mem_cons.mp hk with rfl | hk
      · rw [hcr, hca, hcf]
        simp only [staticTwoNode, he] at hf
        exact hf
      · exact hK k hk
  | ret =>
      exact ⟨hK _ List.mem_cons_self, fun k hk => hK k (List.mem_cons_of_mem _ hk)⟩

private theorem CursorStaticTwo.of_reach {κ : Cursor}
    (reach : Relation.ReflTransGen (SStep cert2) (Cursor.start cert2) κ) :
    CursorStaticTwo κ := by
  induction reach with
  | refl =>
      refine ⟨?_, fun _ h => ?_⟩
      · have hmem : cert2[0]'(by decide) ∈ cert2 := List.getElem_mem (by decide)
        exact ((Bool.and_eq_true _ _).mp
          (List.all_eq_true.mp cert2_all_fast (cert2[0]'(by decide)) hmem)).2
      · have hstart : (Cursor.start cert2).K = [] := rfl
        rw [hstart] at h
        cases h
  | tail _ step ih => exact ih.step step

private theorem parentPrefix_staticcall_target_two_any {root node : Exec.Deriv}
    (hpc : root.pc = 0) (image : root.sevm.code = code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (hat : Ninst.At node.sevm.code node.pc (.exec .staticcall)) :
    ∃ g ii size oi outSize rest,
      node.devm.stack = g :: (2 : B256) :: ii :: size :: oi :: outSize :: rest := by
  obtain ⟨κ, reach, ok⟩ := cursor_of_parentPrefix_noStateGas cert2_check hpc image hsg chain
  have holds := (CursorStaticTwo.of_reach reach).1
  obtain ⟨gTree, htree, -⟩ := ok.tree_of_exec hat
  rw [htree] at holds
  simp only [staticTwoNode, Bool.and_eq_true] at holds
  have hhead := holds.1
  rcases ha : κ.a with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | ⟨v5, arest⟩⟩⟩⟩⟩⟩ <;>
    rw [ha] at hhead
  any_goals simp only [Bool.false_eq_true] at hhead
  cases v1 with
  | unk => simp only [Bool.false_eq_true] at hhead
  | ret => simp only [Bool.false_eq_true] at hhead
  | const c =>
      have hc : c = 2 := beq_iff_eq.mp hhead
      subst hc
      obtain ⟨S, rest, hstack, hfm, -⟩ := ok.stack
      rw [ha] at hfm
      rcases hfm with _ | @⟨_, b0, _, _, _, _ | @⟨_, b1, _, _, hm1,
        _ | @⟨_, b2, _, _, _, _ | @⟨_, b3, _, _, _, _ | @⟨_, b4, _, _, _,
        _ | @⟨_, b5, _, l2, _, _⟩⟩⟩⟩⟩⟩
      change b1 = 2 at hm1
      subst hm1
      refine ⟨b0, b2, b3, b4, b5, l2 ++ rest, ?_⟩
      simpa only [List.cons_append] using hstack

/-- Every same-frame `STATICCALL` of a historical Beacon frame targets precompile `2`. -/
theorem parentPrefix_staticcall_target_twoH
    {sevm : Sevm} {pre post : Devm} {node : Exec.Deriv}
    (run : Exec 0 sevm pre (.ok post)) (image : sevm.code = code)
    (fork : HistFork sevm.benvStat.fork)
    (_fresh : Exec.FreshEntry sevm pre) (_sha : ShaReadyRules sevm pre)
    (chain : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ node)
    (hat : Ninst.At node.sevm.code node.pc (.exec .staticcall)) :
    ∃ g ii size oi outSize rest,
      node.devm.stack = g :: (2 : B256) :: ii :: size :: oi :: outSize :: rest :=
  parentPrefix_staticcall_target_two_any (root := ⟨0, sevm, pre, .ok post, run⟩)
    rfl image fork.stateGas_none chain hat

/-! ## No retained child frame is entered below a Beacon frame -/

private theorem staticcall_none_getCode_two {pc : Nat} {sevm : Sevm} {pre post : Devm}
    {g ii size oi outSize : B256} {rest : Stack}
    (hstack : pre.stack = g :: (2 : B256) :: ii :: size :: oi :: outSize :: rest)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hnodeleg : sevm.benvStat.rules.delegationEnabled = true →
      getDelegatedCodeAddress (pre.getCode 2) = none)
    (hrun : Ninst.StepRun pc sevm pre (.exec .staticcall) .none (.ok post)) :
    post.getCode 2 = pre.getCode 2 := by
  have hp : (g :: (2 : B256) :: ii :: size :: oi :: outSize :: rest) <<+ pre.stack := by
    rw [hstack]
    simpa only [List.append_nil] using
      (pref_append (g :: (2 : B256) :: ii :: size :: oi :: outSize :: rest) [])
  have hfill : Xlot.Filled .none := trivial
  have toAdrTwo : ((2 : B256).toAdr) = (2 : Adr) := by decide
  rcases of_step_staticcall_val_with_depth_frame_causeH hp hfill hrun hsg with
    ⟨_, hworld, _⟩ |
    ⟨parent, child, dp, na, code0, avail, _, _, hst, _, _, _, hdel, _, hpm, _, _, hsf, _⟩
  · exact (hworld.getCode 2).symm
  · rw [toAdrTwo] at hdel hpm
    have hna : na = 2 ∧ dp = false := by
      unfold CallCodeH at hdel
      split at hdel
      · rename_i hd
        rcases hdel with ⟨_, hna, _, hdp⟩ | ⟨d, hsome, _⟩
        · exact ⟨hna, hdp⟩
        · rw [hnodeleg hd] at hsome
          cases hsome
      · exact ⟨hdel.1, hdel.2.2⟩
    rcases hna with ⟨rfl, rfl⟩
    exact (getCode_eq_of_state_eq hsf 2).trans
      ((code_of_processMessage_staticPrecomp hpre hpm 2).trans (getCode_eq_of_state_eq hst 2))

private theorem step_cont_getCode_two {root : Exec.Deriv} {pc pc' : Nat}
    {sevm : Sevm} {pre post : Devm} {next : Exec pc' sevm post root.exn}
    (hpc : root.pc = 0) (image : root.sevm.code = code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (hpre : decide (root.sevm.benvStat.rules.isPrecomp 2) = true)
    (hnodeleg : root.sevm.benvStat.rules.delegationEnabled = true →
      getDelegatedCodeAddress (pre.getCode 2) = none)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post)
    (chain : Exec.Deriv.ParentPrefix root ⟨pc, sevm, pre, root.exn, .cont step next⟩) :
    post.getCode 2 = pre.getCode 2 := by
  have hsevm : sevm = root.sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  cases decoded : Evm.getInst ⟨pc, sevm, pre⟩ with
  | none =>
      unfold Evm.step at step
      rw [decoded] at step
      cases step
  | some instruction =>
      cases instruction with
      | last l =>
          rw [Evm.step_last decoded] at step
          cases step
      | jump j =>
          rw [Evm.step_jump decoded] at step
          cases jumpEq : Jinst.run ⟨pc, sevm, pre⟩ j with
          | error _ => rw [jumpEq] at step; cases step
          | ok pair =>
              rcases pair with ⟨_, _⟩
              rw [jumpEq] at step
              cases step
              have frame := Jinst.run_instructionFrame ⟨pc, sevm, pre⟩ j
              rw [jumpEq] at frame
              have frame' : Devm.InstructionFrame pre post := frame
              exact (frame'.getCode 2).symm
      | next inst =>
          have nstep : Ninst.step ⟨pc, sevm, pre⟩ inst = .cont pc' post := by
            rw [← Evm.step_next decoded]
            exact step
          have pcEq : pc' = pc + inst.size := Ninst.step_cont_pc nstep
          subst pc'
          have nrun : Ninst.StepRun pc sevm pre inst .none (.ok post) := by
            unfold Ninst.StepRun
            rw [nstep]
            exact ⟨rfl, rfl⟩
          cases inst with
          | push bytes bound =>
              exact (congrFun (Ninst.Hinv.inv (f := Devm.getCode)
                (show Ninst.Run sevm pre (.push bytes bound) post from ⟨.none, trivial, pc, nrun⟩)) 2).symm
          | dupn imm =>
              have hfr : Devm.InstructionFrame pre post :=
                Ninst.dupn_instructionFrame_effectRec (xl := .none) trivial nrun
              exact (hfr.getCode 2).symm
          | swapn imm =>
              have hfr : Devm.InstructionFrame pre post :=
                Ninst.swapn_instructionFrame_effectRec (xl := .none) trivial nrun
              exact (hfr.getCode 2).symm
          | exchange imm =>
              have hfr : Devm.InstructionFrame pre post :=
                Ninst.exchange_instructionFrame_effectRec (xl := .none) trivial nrun
              exact (hfr.getCode 2).symm
          | reg r =>
              have rrun : Rinst.run ⟨pc, sevm, pre⟩ r = .ok post :=
                (Step.run_ofExecution.mp nrun).2.symm
              exact (Rinst.run_code_created rrun 2).1
          | exec x =>
              have hat : Ninst.At sevm.code pc (.exec x) := decoded
              have hx : x = .staticcall :=
                parentPrefix_exec_staticcallH hpc image hsg chain hat
              subst hx
              obtain ⟨g, ii, size, oi, outSize, rest, hstack⟩ :=
                parentPrefix_staticcall_target_two_any hpc image hsg chain hat
              have hsg' : sevm.benvStat.rules.stateGas = none := by rw [hsevm]; exact hsg
              have hpre' : decide (sevm.benvStat.rules.isPrecomp 2) = true := by rw [hsevm]; exact hpre
              have hnd' : sevm.benvStat.rules.delegationEnabled = true →
                  getDelegatedCodeAddress (pre.getCode 2) = none := fun hd =>
                hnodeleg (by rw [← hsevm]; exact hd)
              exact staticcall_none_getCode_two hstack hsg' hpre' hnd' nrun

private theorem genericCall_staticPrecomp_not_run
    {sevm : Sevm} {devm : Devm} {gas ii isz oi osz : Nat} {code0 : ByteArray}
    {frame : Jaune.Frame} {rsm : Resume} {cevm : Evm}
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hspawn : genericCall.step sevm devm gas 0 sevm.currentTarget 2 2 true true
      ii isz oi osz code0 false = .spawn frame rsm)
    (henter : frame.enter = .run cevm) : False := by
  unfold genericCall.step at hspawn
  split at hspawn
  · simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at hspawn
    repeat' split at hspawn
    all_goals simp only [XStep.ofExcept, reduceCtorEq] at hspawn
  · simp only [XStep.spawn.injEq] at hspawn
    obtain ⟨rfl, -⟩ := hspawn
    let cmsg := callMsg sevm (devm.withReturnData []) gas 0 sevm.currentTarget 2 2 true true
      (Array.sliceD devm.memory.data ii isz 0) code0 false
    change (Frame.ofCall cmsg).enter = .run cevm at henter
    unfold Frame.enter at henter
    dsimp only [Frame.ofCall] at henter
    rcases hbt : cmsg.benvAfterTransfer with e | benv <;> rw [hbt] at henter
    · cases henter
    · have hval : cmsg.value = 0 := rfl
      have hbenv := benvAfterTransfer_eq_of_not_transfer (fun h => h.2 hval) hbt
      subst hbenv
      unfold executeCode.enter at henter
      simp only [cmsg, Msg.withBenv, callMsg, Bool.not_false, Bool.true_and, hpre, ↓reduceIte] at henter
      cases henter

private theorem spawn_staticcall_not_run {sevm : Sevm} {pre : Devm} {frame : Jaune.Frame}
    {rsm : Resume} {cevm : Evm} {g ii size oi outSize : B256} {rest : Stack}
    (hstack : pre.stack = g :: (2 : B256) :: ii :: size :: oi :: outSize :: rest)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hnodeleg : sevm.benvStat.rules.delegationEnabled = true →
      getDelegatedCodeAddress (pre.getCode 2) = none)
    (hspawn : Xinst.step sevm pre .staticcall = .spawn frame rsm)
    (henter : frame.enter = .run cevm) : False := by
  have hp : (g :: (2 : B256) :: ii :: size :: oi :: outSize :: rest) <<+ pre.stack := by
    rw [hstack]
    simpa only [List.append_nil] using
      (pref_append (g :: (2 : B256) :: ii :: size :: oi :: outSize :: rest) [])
  simp only [Xinst.step, Bind.bind, Except.bind] at hspawn
  rw [hsg] at hspawn
  rcases eq1 : Devm.pop pre with _ | ⟨gas1, devm1⟩ <;> simp only [eq1] at hspawn
  · simp only [XStep.ofExcept, reduceCtorEq] at hspawn
  have f1 := Devm.pop_of_pop eq1
  have e1 := f1.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e1
  rw [e1] at hp
  have hv1 : g = gas1 := pref_head_unique hp (pref_append [gas1] devm1.stack)
  subst hv1
  replace hp := cons_pref_cons_inv hp
  rcases eq2 : Devm.popToAdr devm1 with _ | ⟨target, devm2⟩ <;> simp only [eq2] at hspawn
  · simp only [XStep.ofExcept, reduceCtorEq] at hspawn
  rcases Devm.pop_of_popToAdr eq2 with ⟨x2, hx2, h_pop2⟩
  have f2 := Devm.pop_of_pop h_pop2
  have e2 := f2.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e2
  rw [e2] at hp
  have hv2 : (2 : B256) = x2 := pref_head_unique hp (pref_append [x2] devm2.stack)
  subst hv2
  have ht2 : target = (2 : Adr) := by
    rw [← hx2]
    decide
  subst ht2
  rcases eq3 : Devm.popToNat devm2 with _ | ⟨inputIndex, devm3⟩ <;> simp only [eq3] at hspawn
  · simp only [XStep.ofExcept, reduceCtorEq] at hspawn
  have f3 := (Devm.pop_of_popToNat_val eq3).choose_spec.1
  rcases eq4 : Devm.popToNat devm3 with _ | ⟨inputSize, devm4⟩ <;> simp only [eq4] at hspawn
  · simp only [XStep.ofExcept, reduceCtorEq] at hspawn
  have f4 := (Devm.pop_of_popToNat_val eq4).choose_spec.1
  rcases eq5 : Devm.popToNat devm4 with _ | ⟨outputIndex, devm5⟩ <;> simp only [eq5] at hspawn
  · simp only [XStep.ofExcept, reduceCtorEq] at hspawn
  have f5 := (Devm.pop_of_popToNat_val eq5).choose_spec.1
  rcases eq6 : Devm.popToNat devm5 with _ | ⟨outputSize, devm6⟩ <;> simp only [eq6] at hspawn
  · simp only [XStep.ofExcept, reduceCtorEq] at hspawn
  have f6 := (Devm.pop_of_popToNat_val eq6).choose_spec.1
  have h_st6 : pre.state = devm6.state :=
    (f1.state).trans ((f2.state).trans ((f3.state).trans
      ((f4.state).trans ((f5.state).trans f6.state))))
  have hdel_solve : ∀ {D D' : Devm} {dp : Bool} {na : Adr} {code0 : ByteArray} {dagc : Nat},
      sevm.benvStat.rules.accessDelegation D 2 = (dp, na, code0, dagc, D') →
      D.state = devm6.state →
      na = 2 ∧ dp = false := by
    intro D D' dp na code0 dagc hp10 hD
    have hdel := callCodeH_of_accessDelegation (hD.trans h_st6.symm) hp10
    unfold CallCodeH at hdel
    split at hdel
    · rename_i hd
      rcases hdel with ⟨_, hna, _, hdp⟩ | ⟨d, hsome, _⟩
      · exact ⟨hna, hdp⟩
      · rw [hnodeleg hd] at hsome
        cases hsome
    · exact ⟨hdel.1, hdel.2.2⟩
  rcases hac : sevm.benvStat.rules.access with gflat | _
  swap
  · simp only [hac] at hspawn
    rcases hp10 : sevm.benvStat.rules.accessDelegation (addAccessedAddress devm6 2) 2 with
      ⟨dp, na, code0, dagc, devm8⟩
    simp only [hp10] at hspawn
    obtain ⟨rfl, rfl⟩ := hdel_solve hp10 rfl
    split at hspawn
    · simp only [XStep.ofExcept, reduceCtorEq] at hspawn
    simp only [Pure.pure, Except.pure, XStep.ofExcept] at hspawn
    exact genericCall_staticPrecomp_not_run hpre hspawn henter
  · simp only [hac] at hspawn
    rcases hp10 : sevm.benvStat.rules.accessDelegation devm6 2 with ⟨dp, na, code0, dagc, devm8⟩
    simp only [hp10] at hspawn
    obtain ⟨rfl, rfl⟩ := hdel_solve hp10 rfl
    split at hspawn
    · simp only [XStep.ofExcept, reduceCtorEq] at hspawn
    simp only [Pure.pure, Except.pure, XStep.ofExcept] at hspawn
    exact genericCall_staticPrecomp_not_run hpre hspawn henter

/-- Every historical Beacon frame executes all external calls synchronously at precompile `2`,
so its retained descendant frame list is empty. -/
theorem target_descendantFrames_nilH
    {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (image : sevm.code = code)
    (fork : HistFork sevm.benvStat.fork)
    (_fresh : Exec.FreshEntry sevm pre) (sha : ShaReadyRules sevm pre) :
    Exec.descendantFrames run = [] := by
  suffices h : ∀ {pc : Nat} {s : Sevm} {d : Devm} {out : Execution} (r : Exec pc s d out),
      Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ ⟨pc, s, d, out, r⟩ →
      d.getCode 2 = pre.getCode 2 →
      Exec.descendantFrames r = [] from
    h run (.refl _) rfl
  intro pc s d out r
  induction r with
  | halt _ => intros; simp only [Exec.descendantFrames]
  | doneErr _ _ _ => intros; simp only [Exec.descendantFrames]
  | runErr _ _ _ _ => intros; simp only [Exec.descendantFrames]
  | @cont nodePc nodeSevm nodePre nextPc nodePost nodeOut step next ih =>
      intro chain hcode2
      have hexn : nodeOut = .ok post := Exec.Deriv.ParentPrefix.exn_eq chain
      subst hexn
      have hnext : nodePost.getCode 2 = nodePre.getCode 2 :=
        step_cont_getCode_two (root := ⟨0, sevm, pre, .ok post, run⟩)
          rfl image fork.stateGas_none sha.pre
          (fun hd => by rw [hcode2]; exact sha.nodeleg hd) step chain
      simpa only [Exec.descendantFrames] using
        ih (chain.snoc (.cont step next)) (hnext.trans hcode2)
  | @doneOk nodePc nodeSevm nodePre frame rsm nextPc raw inter out step enter resume next ih =>
      intro chain hcode2
      have hsevm : nodeSevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
      obtain ⟨x, instruction, spawn, _⟩ := Evm.step_spawn_inv step
      have hx : x = .staticcall :=
        parentPrefix_exec_staticcallH
          (root := ⟨0, sevm, pre, .ok post, run⟩) rfl image fork.stateGas_none chain instruction
      subst hx
      obtain ⟨g, ii, size, oi, outSize, rest, hstack⟩ :=
        parentPrefix_staticcall_target_two_any
          (root := ⟨0, sevm, pre, .ok post, run⟩) rfl image fork.stateGas_none chain instruction
      have nrun : Ninst.StepRun nodePc nodeSevm nodePre (.exec .staticcall) .none (.ok inter) := by
        unfold Ninst.StepRun
        rw [Evm.step_next instruction] at step
        rw [step]
        exact ⟨_, RunFrame.of_done enter, resume.symm⟩
      have hsg' : nodeSevm.benvStat.rules.stateGas = none := by
        rw [hsevm]; exact fork.stateGas_none
      have hpre' : decide (nodeSevm.benvStat.rules.isPrecomp 2) = true := by
        rw [hsevm]; exact sha.pre
      have hnd' : nodeSevm.benvStat.rules.delegationEnabled = true →
          getDelegatedCodeAddress (nodePre.getCode 2) = none := fun hd => by
        rw [hcode2]; exact sha.nodeleg (by rw [← hsevm]; exact hd)
      have hinter := staticcall_none_getCode_two hstack hsg' hpre' hnd' nrun
      simpa only [Exec.descendantFrames] using
        ih (chain.snoc (.doneOk step enter resume next)) (hinter.trans hcode2)
  | @runOk nodePc nodeSevm nodePre frame rsm nextPc cevm raw inter final
      step enter child resume next _ _ =>
      intro chain hcode2
      have hsevm : nodeSevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
      obtain ⟨x, instruction, spawn, _⟩ := Evm.step_spawn_inv step
      have hx : x = .staticcall :=
        parentPrefix_exec_staticcallH
          (root := ⟨0, sevm, pre, .ok post, run⟩) rfl image fork.stateGas_none chain instruction
      subst hx
      obtain ⟨g, ii, size, oi, outSize, rest, hstack⟩ :=
        parentPrefix_staticcall_target_two_any
          (root := ⟨0, sevm, pre, .ok post, run⟩) rfl image fork.stateGas_none chain instruction
      have hsg' : nodeSevm.benvStat.rules.stateGas = none := by
        rw [hsevm]; exact fork.stateGas_none
      have hpre' : decide (nodeSevm.benvStat.rules.isPrecomp 2) = true := by
        rw [hsevm]; exact sha.pre
      have hnd' : nodeSevm.benvStat.rules.delegationEnabled = true →
          getDelegatedCodeAddress (nodePre.getCode 2) = none := fun hd => by
        rw [hcode2]; exact sha.nodeleg (by rw [← hsevm]; exact hd)
      exact (spawn_staticcall_not_run hstack hsg' hpre' hnd' spawn enter).elim

/-! ## Positional history ladder and exact indexed entry invariant -/

private def solAccGet (g : B256 → B256) : BeaconDeposit.Acc :=
  { branch := fun height => if height < 32 then g (solBranchSlot height) else 0
    count := (g solCountSlot).toNat }

private def SolInvGet (g : B256 → B256) (history : List B256) : Prop :=
  (∀ height, height < 32 → g (solZeroHashSlot height) = BeaconDeposit.zeroHash Bytes.sha256 height) ∧
    BeaconDeposit.Inv Bytes.sha256 (solAccGet g) history

private def DepositWordReplay (g1 : B256 → B256) (nodes : List B256) (g2 : B256 → B256) : Prop :=
  ∀ history, SolInvGet g1 history → SolInvGet g2 (history ++ nodes)

private theorem DepositWordReplay.nil (g : B256 → B256) : DepositWordReplay g [] g := by
  intro history invariant
  simpa only [List.append_nil] using invariant

private theorem DepositWordReplay.append {g1 g2 g3 : B256 → B256} {xs ys : List B256}
    (first : DepositWordReplay g1 xs g2) (second : DepositWordReplay g2 ys g3) :
    DepositWordReplay g1 (xs ++ ys) g3 := by
  intro history invariant
  simpa only [List.append_assoc] using second _ (first _ invariant)

private def depositWordCarrier (ca : Adr) : ReplayCarrier ca where
  readsStorage := true
  Snap := B256 → B256
  Step := B256
  Tag := Unit
  Replay := DepositWordReplay
  ofState state := (state.getStor ca).get
  frameEntry _ state := (state.getStor ca).get
  nil := DepositWordReplay.nil
  silent := fun storage _ => congrArg Stor.get (storage rfl)
  credit := by
    intro _ _ _ _ storage _ _
    exact ⟨[], by rw [congrArg Stor.get storage]; exact DepositWordReplay.nil _⟩
  entry_eq_ofState := by
    intro _ _ caller_ne _ transfer sum_nof
    exact congrArg Stor.get (benvAfterTransfer_getStor_eq_of_safe transfer sum_nof
      (fun transfers _ => Or.inl (caller_ne transfers)))

private def depositWordObservation (ca : Adr) : ReplayObservation (depositWordCarrier ca) where
  O := B256
  obs := id
  obs_nil := rfl
  obs_append := fun _ _ => rfl
  frameObs := committedFrameNodes ca
  credit := by
    intro _ _ _ _ storage _ _
    refine ⟨[], ?_, rfl⟩
    dsimp only [depositWordCarrier]
    rw [congrArg Stor.get storage]
    exact DepositWordReplay.nil _

private theorem beaconWord_coreIn (ca : Adr) :
    Exec.Fa (Exec.WknSem ca beaconSem
      (fun pc s d e _ => Exec.CoreAccountingIn HistFork ca beaconSem beaconFrameEntryRules
        (depositWordCarrier ca) (depositWordObservation ca) pc s d e)) := by
  intro pc sevm pre out run hat
  have hcore := beacon_coreIn ca pc sevm pre out run hat
  intro run' committed fork installed admitted
  exact hcore run' committed fork installed admitted

private def beaconOpaque (ca : Adr) (f : Exec.Frame) : Prop :=
  f.sevm.currentTarget = ca ∧ f.sevm.isStatic = false

private theorem beacon_positionalIn (ca : Adr) :
    Exec.Fa (Exec.WknSem ca beaconSem
      (fun pc s d e _ => Exec.PositionalAccountingIn HistFork ca beaconSem beaconFrameEntryRules
        (depositWordCarrier ca) (depositWordObservation ca) (beaconOpaque ca) pc s d e)) := by
  apply Exec.positionalAccountingIn (F := HistFork)
    (fun hf => hf.stateGas_none)
    (fun _ _ => rfl)
    (fun h => funext h)
    (fun frame foreign => by
      change committedFrameNodes ca frame = []
      simp only [committedFrameNodes, ite_eq_right foreign])
    DepositWordReplay.append
    (fun _ hop => hop.1)
    (beaconWord_coreIn ca)
  intro sevm pre post hcode target _ run committed fork _ admitted _
    before f after split _
  rw [Exec.committedFrames, dite_eq_left committed] at split
  cases before with
  | nil =>
      obtain ⟨rfl, -⟩ := List.cons.inj split
      exact ⟨[], DepositWordReplay.nil _, rfl⟩
  | cons P rest =>
      rw [List.cons_append] at split
      obtain ⟨_, hdesc⟩ := List.cons.inj split
      obtain ⟨fresh, _, nodeleg, warm⟩ := admitted.root target
      have sha : ShaReadyRules sevm pre :=
        ⟨nodeleg, warm, isPrecomp_two_hist fork, fork.stateGas_none, fork.bal_none⟩
      have hnil := target_descendantFrames_nilH run hcode fork fresh sha
      rw [hnil] at hdesc
      exact (List.append_ne_nil_of_right_ne_nil rest (List.cons_ne_nil f after) hdesc.symm).elim

private def indexedAccountingLadderAdmittedIn (ca : Adr) :
    AccountingLadderAdmittedIn HistFork beaconSpec ca beaconFrameEntryRules where
  carrier := framesCarrier (depositCarrier ca) (depositObservation ca) (beaconOpaque ca)
  append := framesCarrier_append DepositReplay.append
  tag := fun _ _ => ()
  preserves := beaconSpec_preservesAdmittedIn_of_rules ca
  view := framesObservation (depositCarrier ca) (depositObservation ca) (beaconOpaque ca)
  root := by
    intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed
      admitted ready _ fork bound
    obtain ⟨installed, entryBound⟩ :=
      Blanc.Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
    exact framesRoot
      ((beacon_coreIn ca pc sevm pre out run installed
        run committed fork installed admitted).2 entryBound)
      (fun before f after split noOpaque =>
        beacon_positionalIn ca pc sevm pre out run installed
          run committed fork installed admitted entryBound before f after split noOpaque)

/-- Every settled frame targeting the Beacon deposit contract after actual Muir deployment
starts at pc `0` on `HistFork` with installed `code`, fresh entry, bounded calldata,
`ShaReadyRules`, and `SolInv` for the exact prefix of committed deposit nodes before `idx`. -/
theorem BeaconDeploymentTo.classification_inputs
    {B : BlockChain} (d : BeaconDeploymentTo B) (idx : Nat) (fr : Exec.Frame)
    (hlookup : d.trace.settledFrames[idx]? = some fr)
    (target : fr.sevm.currentTarget = depositContractAddress) :
    fr.pc = 0 ∧ HistFork fr.sevm.benvStat.fork ∧ fr.sevm.code = code ∧
    Exec.FreshEntry fr.sevm fr.pre ∧ fr.sevm.data.length < 2 ^ 256 ∧
    ShaReadyRules fr.sevm fr.pre ∧
    SolInv (fr.pre.getStor depositContractAddress)
      ((d.trace.settledFrames.take idx).flatMap
        (committedFrameNodes depositContractAddress)) := by
  obtain ⟨hpc, hfork, hcode, hfresh, hcalldata, hsha⟩ :=
    classification_frame_facts d idx fr hlookup target
  refine ⟨hpc, hfork, hcode, hfresh, hcalldata, hsha, ?_⟩
  let ca := Creation.depositAddress
  have initial : beaconSpec.StateInv ca d.D.state :=
    ⟨by rw [d.deployed.1]; rfl, trivial, ⟨[], d.deployed.2⟩⟩
  have admittedEntry := classification_admitted d
  have admittedRules : d.trace.FrameAdmitted ca beaconEntryRules := by
    rw [d.trace.frameAdmitted_iff_rawFrames] at admittedEntry ⊢
    intro root member htarget
    exact beaconEntry_toRules (admittedEntry root member htarget)
  obtain ⟨frameSteps, frameReplay, frameObserved⟩ :=
    (indexedAccountingLadderAdmittedIn ca).configuredHistoryIn d.trace
      ((d.trace.freshFrameAdmitted ca).and admittedRules) BodyStageCapabilities.historical
      (d.trace.rewardCreditsFunded BodyStageCapabilities.historical)
      initial beaconInstalledCertH.runtimeSafety rfl
  have posAt := (framesCarrier_read frameReplay frameObserved).2
  have hlt : idx < d.trace.settledFrames.length := (List.getElem?_eq_some_iff.mp hlookup).1
  have hget : d.trace.settledFrames[idx] = fr :=
    Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans hlookup)
  have hsplit : d.trace.settledFrames =
      d.trace.settledFrames.take idx ++ fr :: d.trace.settledFrames.drop (idx + 1) := by
    conv_lhs => rw [← List.take_append_drop idx d.trace.settledFrames]
    rw [List.drop_eq_getElem_cons hlt, hget]
  have hnoOpaque : Exec.NoOpaqueAbove (beaconOpaque ca)
      (d.trace.settledFrames.take idx) fr := by
    intro b A m n hbefore hdesc hop
    have hmemTake : A ∈ d.trace.settledFrames.take idx := by
      rw [hbefore]
      exact List.mem_append_right _ List.mem_cons_self
    have hmem : A ∈ d.trace.settledFrames := List.mem_of_mem_take hmemTake
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
    obtain ⟨hApc, hAfork, hAcode, hAfresh, _, hAsha⟩ :=
      classification_frame_facts d j A hj hop.1
    rcases A with ⟨Apc, Asevm, Apre, Aout, Arun, Acomm⟩
    cases Aout with
    | error _ => simp only [Execution.commits, Bool.false_eq_true] at Acomm
    | ok Apost =>
        dsimp only at hApc hAfork hAcode hAfresh hAsha hdesc
        subst hApc
        have hnil := target_descendantFrames_nilH Arun hAcode hAfork hAfresh hAsha
        rw [hnil] at hdesc
        exact List.append_ne_nil_of_right_ne_nil m (List.cons_ne_nil fr n) hdesc.symm
  obtain ⟨steps, replay, observed⟩ := posAt _ fr _ hsplit hnoOpaque
  change DepositReplay (d.D.state.getStor ca) steps (fr.pre.getStor ca) at replay
  change steps = (d.trace.settledFrames.take idx).flatMap (committedFrameNodes ca) at observed
  rw [observed] at replay
  have hinv := replay [] d.deployed.2
  rw [List.nil_append] at hinv
  exact hinv

end Blanc.Lift.BeaconDeposit
