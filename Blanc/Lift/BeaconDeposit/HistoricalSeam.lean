import Blanc.Lift.BeaconDeposit.HistBeaconEnv
import Blanc.Lift.BeaconDeposit.BeaconEnv
import Blanc.ExecutionHistoryInSystemOpenings
import Blanc.ExecutionHistoryInCreateAvoid

/-! Exact historical/modern Beacon seams. The generic join is independent of
concrete anchor identities, so an empty historical prefix recovers the modern
headline. The mainnet specialization interprets only the eight adopted external
observations; it does not authenticate consensus or construct deployment to D. -/

namespace Blanc.Lift.BeaconDeposit

open Jaune Blanc.ExecutionTrace

/-- The modern extractor is unchanged by viewing that same retained trace historically. -/
theorem committedNodesIn_toHistForkIn {ca : Adr} {cfg : ChainConfig}
    {P B : BlockChain} (modern : ConfiguredHistoryTrace cfg P B) :
    committedNodesIn ca modern.toHistForkIn = committedNodes ca modern := by
  simp only [committedNodesIn, committedNodes, ConfiguredHistoryTrace.toHistForkIn_settledFrames]

/-- Exact chronological extraction across an actual historical/modern cut. -/
theorem committedNodesIn_historicalModern {ca : Adr} {cfg : ChainConfig}
    {D P B : BlockChain} (historical : ConfiguredHistoryTraceIn HistFork cfg D P)
    (modern : ConfiguredHistoryTrace cfg P B) :
    committedNodesIn ca (historical.append modern.toHistForkIn) =
      committedNodesIn ca historical ++ committedNodes ca modern := by
  rw [committedNodesIn_append, committedNodesIn_toHistForkIn]

/-- `configuredHistory_solInv_sys` with its system-frame exclusion derived: no frame can
CREATE at an installed system contract, because the present code collides. -/
theorem configuredHistory_solInv_sys_present {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initialHistory : List B256}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (systemInstalled : SystemCodeInstalled checkpoint.state)
    (systemNoAuthority : ∀ p ∈ systemContracts, trace.NoAuthorityAt p.1)
    (checkpointEmpty : checkpoint.state.getCode 2 = ByteArray.empty)
    (noAuthority : trace.NoAuthorityAt 2)
    (noFrame : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ 2)
    (installed : checkpoint.state.getCode ca = code)
    (invariant : SolInv (checkpoint.state.getStor ca) initialHistory) :
    SolInv (future.state.getStor ca) (initialHistory ++ committedNodes ca trace) :=
  configuredHistory_solInv_sys trace systemInstalled systemNoAuthority
    (trace.systemCreateAvoid systemInstalled systemNoAuthority).2 checkpointEmpty noAuthority
    noFrame installed invariant

section Join

variable {ca : Adr} {cfg : ChainConfig} {D P B : BlockChain} {initialHistory : List B256}
    (historical : ConfiguredHistoryTraceIn HistFork cfg D P)
    (modern : ConfiguredHistoryTrace cfg P B)
    (openings : historical.SystemCodeAtOpenings)
    (pragueInstalled : SystemCodeInstalled P.state)
    (historicalSystemNoAuthority : ∀ p ∈ systemContracts, historical.PragueNoAuthorityAt p.1)
    (checkpointEmpty : D.state.getCode 2 = ByteArray.empty)
    (historicalNoAuthority : historical.PragueNoAuthorityAt 2)
    (historicalNoFrame : ∀ root ∈ historical.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ (2 : Adr))
    (rewards : historical.RewardCreditsFunded)
    (modernSystemNoAuthority : ∀ p ∈ systemContracts, modern.NoAuthorityAt p.1)
    (modernNoAuthority : modern.NoAuthorityAt 2)
    (modernNoFrame : ∀ root ∈ modern.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ (2 : Adr))
    (installed : D.state.getCode ca = code)
    (invariant : SolInv (D.state.getStor ca) initialHistory)

include openings pragueInstalled historicalSystemNoAuthority checkpointEmpty historicalNoAuthority
  historicalNoFrame rewards modernSystemNoAuthority
  modernNoAuthority modernNoFrame installed invariant

/-- The historical replay and unchanged modern replay join at their actual shared state. -/
theorem historicalModern_solInv :
    SolInv (B.state.getStor ca)
      (initialHistory ++ (committedNodesIn ca historical ++ committedNodes ca modern)) := by
  have initial : beaconSpec.StateInv ca D.state :=
    ⟨by rw [installed]; rfl, trivial, ⟨initialHistory, invariant⟩⟩
  obtain ⟨-, atPrague, pragueEmpty⟩ := configuredHistoryIn_environment historical openings
    historicalSystemNoAuthority checkpointEmpty historicalNoAuthority
    historicalNoFrame rewards initial
  have pragueCode := ContractSpecSem.StateInv.getCode_eq_of_image (C := code) rfl atPrague
  have left : DepositReplay (D.state.getStor ca) (committedNodesIn ca historical)
      (P.state.getStor ca) := fun history inv =>
    configuredHistoryIn_solInv historical openings historicalSystemNoAuthority checkpointEmpty
      historicalNoAuthority historicalNoFrame rewards installed inv
  have right : DepositReplay (P.state.getStor ca) (committedNodes ca modern)
      (B.state.getStor ca) := fun history inv =>
    configuredHistory_solInv_sys_present modern pragueInstalled modernSystemNoAuthority
      pragueEmpty modernNoAuthority modernNoFrame pragueCode inv
  exact DepositReplay.append left right initialHistory invariant

/-- Whole-span form observes exactly the actual appended retained trace. -/
theorem historicalModern_wholeSpan_solInv :
    SolInv (B.state.getStor ca)
      (initialHistory ++ committedNodesIn ca (historical.append modern.toHistForkIn)) := by
  rw [committedNodesIn_historicalModern]
  exact historicalModern_solInv historical modern openings pragueInstalled
    historicalSystemNoAuthority checkpointEmpty historicalNoAuthority
    historicalNoFrame rewards modernSystemNoAuthority modernNoAuthority
    modernNoFrame installed invariant

end Join

/-- An honest empty-prefix specialization: its premises are the unchanged modern ones,
plus the ordinary witnesses needed to form the retained reflexive prefix. -/
theorem historicalModern_solInv_refl {ca : Adr} {cfg : ChainConfig} {P B : BlockChain}
    {initialHistory : List B256} (modern : ConfiguredHistoryTrace cfg P B)
    (hcfg : cfg.Valid) (hctx : P.ValidContext) (hid : cfg.chainId = P.chainId)
    (systemInstalled : SystemCodeInstalled P.state)
    (systemNoAuthority : ∀ p ∈ systemContracts, modern.NoAuthorityAt p.1)
    (systemNoFrame : ∀ p ∈ systemContracts, ∀ root ∈ modern.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1)
    (checkpointEmpty : P.state.getCode 2 = ByteArray.empty)
    (noAuthority : modern.NoAuthorityAt 2)
    (noFrame : ∀ root ∈ modern.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ (2 : Adr))
    (installed : P.state.getCode ca = code)
    (invariant : SolInv (P.state.getStor ca) initialHistory) :
    SolInv (B.state.getStor ca) (initialHistory ++ committedNodesIn ca
      ((ConfiguredHistoryTraceIn.refl (F := HistFork) hcfg hctx hid).append modern.toHistForkIn)) := by
  rw [committedNodesIn_historicalModern]
  change SolInv _ (initialHistory ++ ([] ++ committedNodes ca modern))
  exact configuredHistory_solInv_sys modern systemInstalled systemNoAuthority systemNoFrame
    checkpointEmpty noAuthority noFrame installed invariant

/-- Local interpretation of exactly the adopted D/C/P checkpoint and installed-code
observations (Plans 0e09e208; payload SHA-256 8a3839f2…fddf3a). Header identities
bind the actual retained traces. Code equalities are explicit external premises;
no full state, state-trie authentication, deployment or consensus is inferred. -/
structure HistoricalSeamAnchors (D C P : BlockChain) (firstCancun : Block) : Prop where
  dTip : ∃ tip, D.blocks.getLast? = some tip ∧ tip.header.number = 11052984 ∧
    tip.header.timestamp = 1602667372 ∧
    tip.header.hash = 0x44bca881b07a6a09f83b130798072441705d9a665c5ac8bdf2f39a3cdf3bee29 ∧
    tip.header.stateRoot = 0xdcd2103f6da66b5694974355877768940a2904eb58432a0b28353171f0e89ce7
  cTip : ∃ tip, C.blocks.getLast? = some tip ∧ tip.header.number = 19426586 ∧
    tip.header.timestamp = 1710338123 ∧
    tip.header.hash = 0xdb672c41cfd47c84ddb478ffde5a09b76964f77dceca0e62bdf719c965d73e7f ∧
    tip.header.stateRoot = 0x33e670fd10cbfcc83ac2ccd320628a0c9f675eff1d77c090d4dc709c329a0fdc
  pTip : ∃ tip, P.blocks.getLast? = some tip ∧ tip.header.number = 22431083 ∧
    tip.header.timestamp = 1746612299 ∧
    tip.header.hash = 0x28fb2c1d988435955e569451c6ad772f7fb5e61cddd7463c7b60e933ed5ff237 ∧
    tip.header.stateRoot = 0xab350e0fe349aef68947ede26295f8946c34ce3af5e3ec76f4b26ddeef29c0e3
  firstNumber : firstCancun.header.number = 19426587
  firstTimestamp : firstCancun.header.timestamp = 1710338135
  firstHash : firstCancun.header.hash =
    0xf8e2f40d98fe5862bc947c8c83d34799c50fb344d7445d020a8a946d891b62ee
  firstParent : firstCancun.header.parentHash =
    0xdb672c41cfd47c84ddb478ffde5a09b76964f77dceca0e62bdf719c965d73e7f
  firstStateRoot : firstCancun.header.stateRoot =
    0xbd33ab68095087d81beb810b3f5d0b16050b3f798ae3978e440bab048dd78992
  beaconAtC : C.state.getCode beaconRootsAddress = beaconRootsCode
  beaconAtP : P.state.getCode beaconRootsAddress = beaconRootsCode
  historyAtP : P.state.getCode historyStorageAddress = historyStorageCode
  withdrawalAtP : P.state.getCode withdrawalRequestPredeployAddress = withdrawalRequestCode
  consolidationAtP : P.state.getCode consolidationRequestPredeployAddress = consolidationRequestCode

/-- The four adopted P observations supply the unchanged modern installation input. -/
theorem HistoricalSeamAnchors.pragueInstalled {D C P : BlockChain} {firstCancun : Block}
    (anchors : HistoricalSeamAnchors D C P firstCancun) : SystemCodeInstalled P.state := by
  intro p member
  simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact anchors.beaconAtP
  · exact anchors.historyAtP
  · exact anchors.withdrawalAtP
  · exact anchors.consolidationAtP

/-- The adopted D/C/P anchors and the first Cancun block select the actual eras of the
historical span: pre-Cancun on `D → C`, Cancun on the first block and on `C1 → P`. -/
theorem HistoricalSeamAnchors.historicalForks
    {D C C1 P : BlockChain}
    (dc : ConfiguredHistoryTraceIn HistFork mainnetChainConfig D C)
    (first : ConfiguredBlockTraceIn HistFork mainnetChainConfig C C1)
    (tail : ConfiguredHistoryTraceIn HistFork mainnetChainConfig C1 P)
    (anchors : HistoricalSeamAnchors D C P first.block) :
    dc.ForksSatisfy PreCancun ∧ first.fork = .cancun ∧
      tail.ForksSatisfy (fun f => f = .cancun) := by
  obtain ⟨d, dLast, dNumber, dTime, -, -⟩ := anchors.dTip
  obtain ⟨c, cLast, cNumber, cTime, -, -⟩ := anchors.cTip
  obtain ⟨p, pLast, pNumber, pTime, -, -⟩ := anchors.pTip
  have dFork : mainnetChainConfig.forkAt d.header.number d.header.timestamp = .ok .muirGlacier := by
    rw [dNumber, dTime]; decide +kernel
  have cFork : mainnetChainConfig.forkAt c.header.number c.header.timestamp = .ok .shanghai := by
    rw [cNumber, cTime]; decide +kernel
  have pFork : mainnetChainConfig.forkAt p.header.number p.header.timestamp = .ok .cancun := by
    rw [pNumber, pTime]; decide +kernel
  have firstLookup : mainnetChainConfig.forkAt first.block.header.number
      first.block.header.timestamp = .ok .cancun := by
    rw [anchors.firstNumber, anchors.firstTimestamp]; decide +kernel
  have firstFork : first.fork = .cancun := Except.ok.inj (first.forkAt.symm.trans firstLookup)
  have dcForks : dc.ForksSatisfy PreCancun :=
    (dc.forksSatisfy_between dLast dFork cLast cFork).mono (by
      intro f bounded
      cases f <;> simp only [Fork.index] at bounded <;> first | decide | omega)
  have c1Last : C1.blocks.getLast? = some first.block :=
    (congrArg (fun chain : BlockChain => chain.blocks.getLast?) first.postEq).trans
      (appendBlock_getLast? _ _)
  have tailForks : tail.ForksSatisfy (fun f => f = .cancun) :=
    (tail.forksSatisfy_between c1Last firstLookup pLast pFork).mono (by
      intro f bounded
      cases f <;> simp only [Fork.index] at bounded <;> first | rfl | omega)
  exact ⟨dcForks, firstFork, tailForks⟩

/-- The whole historical span is pre-Prague, so it needs no authority exclusion. -/
theorem HistoricalSeamAnchors.historicalPragueNoAuthorityAt
    {D C C1 P : BlockChain}
    (dc : ConfiguredHistoryTraceIn HistFork mainnetChainConfig D C)
    (first : ConfiguredBlockTraceIn HistFork mainnetChainConfig C C1)
    (tail : ConfiguredHistoryTraceIn HistFork mainnetChainConfig C1 P)
    (anchors : HistoricalSeamAnchors D C P first.block) (a : Adr) :
    ((dc.step first).append tail).PragueNoAuthorityAt a := by
  obtain ⟨dcForks, firstFork, tailForks⟩ := anchors.historicalForks dc first tail
  apply ConfiguredHistoryTraceIn.pragueNoAuthorityAt_of_prePrague
  rw [ConfiguredHistoryTraceIn.ForksSatisfy_append]
  refine ⟨⟨dcForks.mono (fun _ h => h.toPrePrague), ?_⟩,
    tailForks.mono (fun f h => by rw [h]; decide)⟩
  rw [firstFork]
  decide

/-- The actual pre-Cancun prefix and Cancun step/tail obtain their opening code
from the C anchor, with no system installation at D and no per-block input. No frame
exclusion is needed: the present beacon-roots code makes CREATE at it collide. -/
theorem HistoricalSeamAnchors.historicalOpenings
    {D C C1 P : BlockChain}
    (dc : ConfiguredHistoryTraceIn HistFork mainnetChainConfig D C)
    (first : ConfiguredBlockTraceIn HistFork mainnetChainConfig C C1)
    (tail : ConfiguredHistoryTraceIn HistFork mainnetChainConfig C1 P)
    (anchors : HistoricalSeamAnchors D C P first.block) :
    ((dc.step first).append tail).SystemCodeAtOpenings := by
  obtain ⟨dcForks, firstFork, tailForks⟩ := anchors.historicalForks dc first tail
  have dcOpen := dc.systemCodeAtOpenings_of_preCancun dcForks
  have firstOpening : first.SystemCodeAtOpening := by
    intro q member
    rw [HistFork.installedAt_beacon_of_cancun first.forkIn firstFork] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst q
    exact anchors.beaconAtC
  have facts := systemContracts_facts _ beaconRoots_mem_systemContracts
  have hC : CancunOnwards first.fork := by rw [firstFork]; decide
  have hdis : first.fork.ruleSet.delegationEnabled = false ∨
      ∀ p ∈ first.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
        recoverAuthority auth = .ok authority → authority ≠ beaconRootsAddress :=
    Or.inl (first.forkIn.delegationDisabled_of_prePrague (by rw [firstFork]; decide))
  have avoidFirst := first.createAvoid_of_cancunOnwards BodyStageCapabilities.historical
    first.forkIn hC hdis anchors.beaconAtC facts.2.2 facts.2.1
  have c1Code := first.codeAt_keep_of_cancunOnwards BodyStageCapabilities.historical
    first.forkIn hC hdis avoidFirst anchors.beaconAtC facts.2.2 facts.2.1
  have tailOpen := (tail.systemCodeAtOpenings_of_cancun_present tailForks c1Code).1
  exact (ConfiguredHistoryTraceIn.SystemCodeAtOpenings_append _ _).mpr
    ⟨⟨dcOpen, firstOpening⟩, tailOpen⟩

section Anchored

variable {ca : Adr} {D C C1 P B : BlockChain} {initialHistory : List B256}
    (dc : ConfiguredHistoryTraceIn HistFork mainnetChainConfig D C)
    (first : ConfiguredBlockTraceIn HistFork mainnetChainConfig C C1)
    (tail : ConfiguredHistoryTraceIn HistFork mainnetChainConfig C1 P)
    (modern : ConfiguredHistoryTrace mainnetChainConfig P B)
    (anchors : HistoricalSeamAnchors D C P first.block)
    (checkpointEmpty : D.state.getCode 2 = ByteArray.empty)
    (historicalNoFrame : ∀ root ∈ ((dc.step first).append tail).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ (2 : Adr))
    (rewards : ((dc.step first).append tail).RewardCreditsFunded)
    (modernSystemNoAuthority : ∀ p ∈ systemContracts, modern.NoAuthorityAt p.1)
    (modernNoAuthority : modern.NoAuthorityAt 2)
    (modernNoFrame : ∀ root ∈ modern.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ (2 : Adr))
    (installed : D.state.getCode ca = code)
    (invariant : SolInv (D.state.getStor ca) initialHistory)

include anchors checkpointEmpty historicalNoFrame rewards
  modernSystemNoAuthority modernNoAuthority modernNoFrame installed invariant

/-- D→C, the actual adopted first Cancun step, the remaining Cancun tail to P,
and unchanged modern P→B compose with no system-code premise at D and no
unexplained per-block installation premise. The span is pre-Prague, so it needs no
authority exclusion. Initial history and order are retained. -/
theorem historicalSeam_solInv :
    SolInv (B.state.getStor ca) (initialHistory ++
      (committedNodesIn ca ((dc.step first).append tail) ++ committedNodes ca modern)) :=
  historicalModern_solInv ((dc.step first).append tail) modern
    (anchors.historicalOpenings dc first tail)
    anchors.pragueInstalled (fun p _ => anchors.historicalPragueNoAuthorityAt dc first tail p.1)
    checkpointEmpty (anchors.historicalPragueNoAuthorityAt dc first tail 2)
    historicalNoFrame rewards modernSystemNoAuthority modernNoAuthority modernNoFrame installed
  invariant

/-- The final invariant observes exactly one actual chronological D→B retained trace. -/
theorem historicalSeam_wholeSpan_solInv :
    SolInv (B.state.getStor ca) (initialHistory ++ committedNodesIn ca
      (((dc.step first).append tail).append modern.toHistForkIn)) := by
  rw [committedNodesIn_historicalModern]
  exact historicalSeam_solInv dc first tail modern anchors checkpointEmpty historicalNoFrame rewards
    modernSystemNoAuthority modernNoAuthority modernNoFrame installed invariant

/-- The count is the length of precisely the ordered historical-plus-modern extraction. -/
theorem historicalSeam_count :
    (B.state.getStor ca).get solCountSlot = Nat.toB256
      (initialHistory ++ (committedNodesIn ca ((dc.step first).append tail) ++
        committedNodes ca modern)).length ∧
      (initialHistory ++ (committedNodesIn ca ((dc.step first).append tail) ++
        committedNodes ca modern)).length < 2 ^ 32 :=
  solCount_eq_of_solInv (historicalSeam_solInv dc first tail modern anchors
    checkpointEmpty historicalNoFrame rewards modernSystemNoAuthority
    modernNoAuthority modernNoFrame installed invariant)

/-- The mixed root belongs to that same exact ordered extraction. -/
theorem historicalSeam_root :
    BeaconDeposit.Acc.root Bytes.sha256 (solAcc (B.state.getStor ca)) =
      BeaconDeposit.mixedRootOf Bytes.sha256 (initialHistory ++
        (committedNodesIn ca ((dc.step first).append tail) ++ committedNodes ca modern)) :=
  BeaconDeposit.root_correct _ _ _ (historicalSeam_solInv dc first tail modern anchors
    checkpointEmpty historicalNoFrame rewards modernSystemNoAuthority
    modernNoAuthority modernNoFrame installed invariant).2

end Anchored

end Blanc.Lift.BeaconDeposit
