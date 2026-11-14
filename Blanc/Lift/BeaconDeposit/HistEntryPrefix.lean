import Batteries.Tactic.OpenPrivate
import Blanc.Lift.BeaconDeposit.HistDeployment
import Blanc.ExecutionInOwnCode
import Blanc.ExecutionAccountingPositionalHistory
import Blanc.Lift.Quiet
import Blanc.Lift.CertifiedOperands
import Blanc.Lift.CursorCuts
import Blanc.Lift.StaticPrecompileCall

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

/-! ## Checked certificate pinning address `2` at every `STATICCALL` -/

private def observeStaticTwo : Xinst → List AVal → Bool
  | .staticcall, _ :: .const c :: _ :: _ :: _ :: _ :: _ => c == 2
  | .staticcall, _ => false
  | _, _ => true

private theorem cert_operands_left :
    ((cert.take 18).all fun (e, f) =>
      f.execOperandsSatisfy cert.entries observeStaticTwo e.frame) = true := by
  decide +kernel

private theorem cert_operands_right :
    ((cert.drop 18).all fun (e, f) =>
      f.execOperandsSatisfy cert.entries observeStaticTwo e.frame) = true := by
  decide +kernel

private theorem cert_operands : cert.execOperandsSatisfy observeStaticTwo = true := by
  unfold Cert.execOperandsSatisfy
  rw [← List.take_append_drop 18 cert, List.all_append, Bool.and_eq_true]
  exact ⟨cert_operands_left, cert_operands_right⟩


private theorem parentPrefix_staticcall_target_two_any {root node : Exec.Deriv}
    (hpc : root.pc = 0) (image : root.sevm.code = code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (hat : Ninst.At node.sevm.code node.pc (.exec .staticcall)) :
    ∃ g ii size oi outSize rest,
      node.devm.stack = g :: (2 : B256) :: ii :: size :: oi :: outSize :: rest := by
  obtain ⟨κ, reach, ok⟩ := cursor_of_parentPrefix_noStateGas cert_check hpc image hsg chain
  have holds := Cursor.execOperandsSatisfy_of_reachable cert_check cert_operands reach
  have observed := ok.execOperandsSatisfy holds hat
  have known : κ.a[1]? = some (.const (2 : B256)) := by
    rcases ha : κ.a with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | ⟨v5, arest⟩⟩⟩⟩⟩⟩ <;>
      rw [ha] at observed
    any_goals simp only [observeStaticTwo, Bool.false_eq_true] at observed
    cases v1 with
    | unk => simp only [Bool.false_eq_true] at observed
    | ret => simp only [Bool.false_eq_true] at observed
    | const c =>
        have same : c = 2 := beq_iff_eq.mp observed
        subst c
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero]
  have actual := ok.stack_getElem?_const known
  obtain ⟨tail, tree, -⟩ := ok.tree_of_exec hat
  obtain ⟨g, target, ii, size, oi, outSize, rest, stack⟩ := cursor_staticcall_operands ok tree
  rw [stack] at actual
  have same : target = 2 := Option.some.inj actual
  subst target
  exact ⟨g, ii, size, oi, outSize, rest, stack⟩

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
  have target : (2 : B256).toAdr = (2 : Adr) := by decide
  apply staticcall_none_getCode_of_precompile hstack hsg
  · simpa only [target] using hpre
  · simpa only [target] using hnodeleg
  · exact hrun

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

private theorem spawn_staticcall_not_run {sevm : Sevm} {pre : Devm} {frame : Jaune.Frame}
    {rsm : Resume} {cevm : Evm} {g ii size oi outSize : B256} {rest : Stack}
    (hstack : pre.stack = g :: (2 : B256) :: ii :: size :: oi :: outSize :: rest)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hnodeleg : sevm.benvStat.rules.delegationEnabled = true →
      getDelegatedCodeAddress (pre.getCode 2) = none)
    (hspawn : Xinst.step sevm pre .staticcall = .spawn frame rsm)
    (henter : frame.enter = .run cevm) : False := by
  have target : (2 : B256).toAdr = (2 : Adr) := by decide
  apply staticcall_spawn_not_run_of_precompile hstack hsg
  · simpa only [target] using hpre
  · simpa only [target] using hnodeleg
  · exact hspawn
  · exact henter

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
