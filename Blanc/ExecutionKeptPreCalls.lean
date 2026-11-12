import Batteries.Tactic.OpenPrivate
import Blanc.ExecutionKeptClean
import Blanc.ExecutionKeptConfigured
import Blanc.LadderReached
import Blanc.SystemCallForward
import Blanc.SystemContracts

/-!
# Kept-history pre-execution system calls, header links, and random access

A kept block opens with two pre-execution system calls (`beaconRootsCall` at `beaconRootsAddress` and
`historyStorageCall` at `historyStorageAddress`), runs its decoded transactions from `b.run.preState`, and ends with the
request pass. Existing caller-exclusion lemmas (`BodyRoots.caller_ne`, `KeptHistory.caller_ne`) exclude those two
pre-execution targets because each has its own unchecked system call in `PreRoots`.

This module bridges that gap for contract-neutral kept steps and kept histories:

* `KeptChain.stor_eq`: a `KeptChain` of storage-preserving frames leaves storage unchanged;
* `covered_system_root`: on a covered fork, any clean `systemTransactionMessage` to a canonical system contract keeps
  exact single-frame root `[f]` at that target with `f.sevm.caller = systemAddress`, `f.sevm.data = data`, and exact
  pre/post storage links;
* `KeptStep.header_links`, `KeptStep.lastBlockHash`, `KeptStep.parentBeaconRoot`: header validation links (`parentHash`,
  `number = parent.number + 1`, strict `timestamp` increase, `post.blocks.getLast? = some b.block`) and the exact bytes
  `beaconRootsCall` and `historyStorageCall` pass;
* `KeptStep.beaconRoots_frames`, `KeptStep.beaconRoots_stor`, `KeptStep.history_pre`,
  `KeptStep.historyStorage_frames`, `KeptStep.historyStorage_stor`: decompose `b.keptAt` at each pre-execution system
  contract into its single system-caller pre-call frame and non-system `EntryIn` frames across `b.run.preState` and
  `post.state`;
* `KeptHistory.split_at`, `KeptHistory.tip_getLast?`, `KeptHistory.prev_header`, `KeptHistory.number_add`,
  `KeptHistory.timestamp_lt`: random-access block splitting, consecutive block numbers, and strict timestamp monotonicity
  along a `KeptHistory`.
-/

namespace Blanc

open Jaune ExecutionTrace

open private runFrame_cases from Blanc.ExecutionKeptTop
open private withdrawalsPass_getCode withdrawalsPass_getStor historyData_fits from Blanc.ExecutionKeptChain

/-! ## Storage chains and covered system roots -/

/-- A `KeptChain` whose frames each leave storage at `a` unchanged equates its endpoints. -/
theorem KeptChain.stor_eq {a : Adr} {s t : Stor} {fs : List Exec.Frame}
    (h : KeptChain a s fs t) (same : ∀ f ∈ fs, Devm.getStor f.post a = Devm.getStor f.pre a) :
    t = s := by
  induction h with
  | nil => rfl
  | cons starts rest ih =>
      have hhead := same _ List.mem_cons_self
      exact (ih fun x hx => same x (List.mem_cons_of_mem _ hx)).trans (hhead.trans starts)

private theorem keptChain_nil_eq {a : Adr} {s t : Stor} (h : KeptChain a s [] t) : s = t := by
  cases h
  rfl

/-- **A covered-fork system message to a canonical system contract is one kept root.** On a covered fork, with the
canonical code installed at `a` and `out.error = none`, `systemTransactionMessage benv a data` commits one root `[f]` at
`a`, with `f.sevm.caller = systemAddress`, `f.sevm.benvStat = benv.beginTransaction.stat`, `f.sevm.data = data`, and
pre/post storage equal to `benv.state.getStor a` and `post.getStor a`. -/
theorem covered_system_root {benv : Benv} {a : Adr} {C : ByteArray} {data : Bytes} {post : State}
    {out : MsgCallOutput} {rs : List Root}
    (fork : CoveredFork benv.stat.fork) (member : (a, C) ∈ systemContracts)
    (installed : benv.state.getCode a = C) (noError : out.error = none)
    (roots : MessageRoots (systemTransactionMessage benv a data) post out rs) :
    ∃ f, rs.flatMap (Root.keptAt a) = [f] ∧ f.sevm.caller = systemAddress ∧
      f.sevm.benvStat = benv.beginTransaction.stat ∧ f.sevm.data = data ∧
      Devm.getStor f.pre a = benv.state.getStor a ∧
      Devm.getStor f.post a = post.getStor a := by
  obtain ⟨-, hndel, hne⟩ := systemContracts_facts (a, C) member
  have hsg : (systemTransactionMessage benv a data).benv.stat.rules.stateGas = none :=
    fork.rules_stateGas_none
  have hcode : (systemTransactionMessage benv a data).code = C := installed
  have hnd : getDelegatedCodeAddress C = none := systemContracts_nondelegated member
  have hdel : messageCallDelegation (systemTransactionMessage benv a data) =
      .ok (systemTransactionMessage benv a data, 0) := by
    unfold messageCallDelegation processMessageCall.legacyAuthorization
    have hauths : (systemTransactionMessage benv a data).tenv.stat.auths = [] := rfl
    simp only [hauths, List.isEmpty_nil, Bool.or_true, ↓reduceIte]
  have hres : messageCallExecutionMessage (systemTransactionMessage benv a data) =
      systemTransactionMessage benv a data := by
    unfold messageCallExecutionMessage Msg.resolveCodeDelegation
    have hnone : (systemTransactionMessage benv a data).benv.stat.rules.delegatedCodeAddress
        (systemTransactionMessage benv a data).code = none := by
      simp only [ForkRules.delegatedCodeAddress, hcode, hnd, ite_self]
    rw [hnone]
  have hm := roots.1
  unfold processMessageCall at hm
  simp only [show (systemTransactionMessage benv a data).target.isNone = false from rfl, Bool.false_eq_true,
    ↓reduceIte] at hm
  unfold processMessageCall.call at hm
  rw [hsg] at hm
  dsimp only at hm
  obtain ⟨⟨d, refund⟩, hd, body⟩ := Except.bind_eq_ok hm
  have hd' : messageCallDelegation (systemTransactionMessage benv a data) = .ok (d, refund) := hd
  rw [hdel] at hd'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hd')
  obtain ⟨evm, hevm, tail⟩ := Except.bind_eq_ok body
  have core : processMessage (messageCallExecutionMessage (systemTransactionMessage benv a data)) = .ok evm :=
    Except.bimap_id_eq_ok hevm
  rw [hres] at core
  have herr : out.error = evm.error := by
    split at tail
    · obtain ⟨_, _, output⟩ := Except.bind_eq_ok tail
      rw [← (Prod.mk.inj (Except.ok.inj output)).2]
    · rw [← (Prod.mk.inj (Except.ok.inj tail)).2]
  have hentry : messageEntry (systemTransactionMessage benv a data) =
      enteredFrame (Frame.ofCall (systemTransactionMessage benv a data)) := by
    unfold messageEntry legacyEntry
    rw [hsg]
    dsimp only
    rw [hdel]
    simp only [show (systemTransactionMessage benv a data).target.isNone = false from rfl, Bool.false_eq_true,
      ↓reduceIte]
    rw [hres]
  have notPrecompile : ¬ benv.stat.rules.isPrecomp a := systemContracts_not_precompile member fork
  obtain ⟨benv', ht, cases⟩ := runFrame_cases (f := Frame.ofCall (systemTransactionMessage benv a data)) core
  have hb : benv' = benv.beginTransaction := (Except.ok.inj ht).symm
  subst hb
  rcases cases with ⟨-, adr, -, hca, hp⟩ | ⟨hsome, hs⟩
  · obtain rfl : a = adr := Option.some.inj hca
    have hp' : (!false && decide (benv.stat.rules.isPrecomp a)) = true := hp
    rw [decide_eq_false notPrecompile] at hp'
    exact absurd hp' (by decide)
  · have hmap := roots.2
    rw [hentry, hsome] at hmap
    cases rs with
    | nil => cases hmap
    | cons r tail =>
        simp only [Option.toList_some, List.map_cons, List.cons.injEq, Prod.mk.injEq, List.map_eq_nil_iff] at hmap
        obtain ⟨⟨hf, he⟩, rfl⟩ := hmap
        have mem : r ∈ [r] := List.mem_singleton.mpr rfl
        have hraw := (roots.mem_entry mem).2
        have settles : Frame.settlementCommits r.frame r.raw = true := by
          unfold Frame.settlementCommits
          rw [← hraw, he, hf, hs]
          dsimp only
          rw [← herr, noError]
          rfl
        obtain ⟨hcaller, here, hdyn, hdata⟩ := roots.entry_routing mem
        have keep : Root.keptAt a r =
            [Exec.Frame.ofRun r.run (Frame.raw_commits_of_settlementCommits settles)] := by
          rw [Root.keptAt, dite_eq_left settles, ite_eq_left (show r.evm.sta.currentTarget = a from here)]
        have flat : [r].flatMap (Root.keptAt a) =
            [Exec.Frame.ofRun r.run (Frame.raw_commits_of_settlementCommits settles)] := by
          rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, keep]
        have hc : (benv.state.getCode a).toList ≠ [] := by rw [installed]; exact hne
        have hdl : ¬ isValidDelegation (benv.state.getCode a) := by rw [installed]; exact hndel
        refine ⟨_, flat, hcaller,
          (show (Exec.Frame.ofRun r.run (Frame.raw_commits_of_settlementCommits settles)).sevm.benvStat =
              benv.beginTransaction.stat from hdyn),
          hdata, (roots.entry_kept mem hc hdl).2, ?_⟩
        have chain := (roots.chain (a := a) hc hdl).1
        rw [flat] at chain
        cases chain with
        | cons starts rest => exact keptChain_nil_eq rest

/-- The actual two pre-call results identify the retained pre-output. -/
theorem PreRoots.output_of_calls {benv : Benv} {st beacon history : State}
    {bal beaconBal historyBal : BalBuilder} {rs : List Root}
    (roots : PreRoots benv st bal rs)
    (beaconRun : beaconRootsCall benv.stat.rules benv = .ok (beacon, beaconBal))
    (historyRun : historyStorageCall benv.stat.rules (benv.withState beacon) beaconBal =
      .ok (history, historyBal)) : st = history ∧ bal = historyBal := by
  obtain ⟨beacon', beaconBal', _, _, first, _, second, _, _⟩ := roots
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (first.symm.trans beaconRun))
  exact Prod.mk.inj (Except.ok.inj (second.symm.trans historyRun))

/-! ## Header links and pre-call inputs on one kept step -/

/-- When `chain.blocks.getLast? = some tip`, the last entry of `getLast256BlockHashes chain` is `tip.header.hash`. -/
theorem getLast256BlockHashes_getLast? {chain : BlockChain} {tip : Block}
    (htip : chain.blocks.getLast? = some tip) :
    (getLast256BlockHashes chain).getLast? = some tip.header.hash := by
  obtain ⟨xs, hxs⟩ := List.getLast?_eq_some_iff.mp htip
  have hrev : chain.blocks.reverse.take 255 = tip :: xs.reverse.take 254 := by
    rw [hxs, List.reverse_append, List.reverse_singleton, List.singleton_append]
    rfl
  rw [getLast256BlockHashes_eq hrev, List.getLast?_concat]

private theorem keptFork_requests_not_ring {fork : Fork} (h : KeptFork fork) :
    ∀ p ∈ fork.ruleSet.requests, p.2 ≠ beaconRootsAddress ∧ p.2 ≠ historyStorageAddress := by
  rcases h with covered | rfl
  · have hreq : fork.ruleSet.requests = pragueRequests := covered.requests_eq
    rw [hreq]
    decide
  · decide

namespace KeptStep

variable {cfg : ChainConfig} {b : KeptBlock} {post : BlockChain}

/-- **Header links of a kept step.** The parent tip exists, `parentHash` is its header hash, `number` increments by `1`,
`timestamp` strictly increases, and `b.block` becomes the post-chain's tip. -/
theorem header_links (h : KeptStep cfg b post) :
    ∃ parent, b.parent.blocks.getLast? = some parent ∧
      b.block.header.parentHash = parent.header.hash ∧
      b.block.header.number = parent.header.number + 1 ∧
      parent.header.timestamp < b.block.header.timestamp ∧
      post.blocks.getLast? = some b.block := by
  obtain ⟨f, hf, hs, ⟨parent, hlast, hlt⟩, hnew⟩ := stateTransitionUsing_reachedStep h.transition
  obtain rfl : f = b.fork := Except.ok.inj (hf.symm.trans h.forkAt)
  obtain ⟨hvh, -, -⟩ := stateTransitionCoreE_eq_ok (stateTransitionScheduledE_eq_ok_iff.mp hs)
  obtain ⟨hph, hnum⟩ := validateHeader_links hlast hvh
  exact ⟨parent, hlast, hph, hnum, hlt, hnew⟩

/-- **The last block hash a kept step's environment exposes** is `b.block.header.parentHash`, and `historyData b.benv`
is its 32 bytes. -/
theorem lastBlockHash (h : KeptStep cfg b post) :
    b.benv.stat.blockHashes.getLast? = some b.block.header.parentHash ∧
      historyData b.benv = b.block.header.parentHash.toBytes := by
  obtain ⟨parent, hlast, hph, -, -, -⟩ := h.header_links
  have hbh : b.benv.stat.blockHashes.getLast? = some b.block.header.parentHash := by
    change (getLast256BlockHashes b.parent).getLast? = some b.block.header.parentHash
    rw [getLast256BlockHashes_getLast? hlast, hph]
  refine ⟨hbh, ?_⟩
  unfold historyData
  rw [hbh]

/-- The beacon-root word in `b.benv.stat` is `b.block.header.parentBeaconBlockRoot.getD 0`. -/
theorem parentBeaconRoot (b : KeptBlock) :
    b.benv.stat.parentBeaconBlockRoot = b.block.header.parentBeaconBlockRoot.getD 0 := rfl

/-- On a kept fork, the header carries `parentBeaconBlockRoot = some root` with `b.benv.stat.parentBeaconBlockRoot = root`. -/
theorem parentBeaconRoot_some (h : KeptStep cfg b post) :
    ∃ root, b.block.header.parentBeaconBlockRoot = some root ∧ b.benv.stat.parentBeaconBlockRoot = root := by
  obtain ⟨f, hf, hs, -, -⟩ := stateTransitionUsing_reachedStep h.transition
  obtain rfl : f = b.fork := Except.ok.inj (hf.symm.trans h.forkAt)
  obtain ⟨hvh, -, -⟩ := stateTransitionCoreE_eq_ok (stateTransitionScheduledE_eq_ok_iff.mp hs)
  unfold validateHeader at hvh
  obtain ⟨_, hshape, -⟩ := Except.bind_eq_ok hvh
  have hon : b.fork.ruleSet.header.parentBeaconBlockRoot = true := by
    rcases h.kept with covered | hamst
    · exact covered.cases (motive := fun f => f.ruleSet.header.parentBeaconBlockRoot = true) rfl rfl rfl rfl
    · rw [hamst]; rfl
  unfold checkHeaderShape at hshape
  obtain ⟨_, _, hshape⟩ := Except.bind_eq_ok hshape
  obtain ⟨_, _, hshape⟩ := Except.bind_eq_ok hshape
  obtain ⟨_, _, hshape⟩ := Except.bind_eq_ok hshape
  obtain ⟨_, _, hshape⟩ := Except.bind_eq_ok hshape
  rw [hon] at hshape
  unfold checkHeaderFieldPresence at hshape
  cases hpb : b.block.header.parentBeaconBlockRoot with
  | none =>
      simp only [hpb, Option.isSome_none, ne_eq, Bool.false_eq_true, not_false_eq_true, ↓reduceIte,
        reduceCtorEq] at hshape
  | some root =>
      exact ⟨root, rfl, by simp only [KeptBlock.benv, initBenv, initBenvStat, hpb, Option.getD_some]⟩

/-! ## Post-pre-call caller exclusion at `beaconRootsAddress` and `historyStorageAddress` -/

/-- Every frame a kept step keeps at `a ∈ {beaconRootsAddress, historyStorageAddress}` during transactions or the
request pass has `caller ≠ systemAddress`, and `post.state.getCode systemAddress` stays empty. -/
private theorem postPre_caller_ne (h : KeptStep cfg b post) {a : Adr}
    (ha : a = beaconRootsAddress ∨ a = historyStorageAddress)
    (emptyPre : b.run.preState.getCode systemAddress = ByteArray.empty)
    (senders : NoSenderAt systemAddress b.run.senders)
    (authorities : NoAuthorityAt systemAddress b.run.senders)
    (avoidTxs : NoCreateAt systemAddress b.run.txRoots)
    (avoidReq : NoCreateAt systemAddress (requestRootsOf b.run.requests)) :
    (∀ f ∈ (b.run.txRoots ++ requestRootsOf b.run.requests).flatMap (Root.keptAt a),
      f.sevm.caller ≠ systemAddress) ∧
      post.state.getCode systemAddress = ByteArray.empty := by
  have hrules : KeptRules b.benv.stat.rules := h.kept.rules
  obtain ⟨st, out, pass, final, -⟩ := h.body.stages
  obtain ⟨decoded, -, roots⟩ := h.body.transactions
  have empty₂ := roots.empty_stays emptyPre authorities avoidTxs
  have empty₃ : (b.run.txEnv.withState
      (withdrawalsPass b.benv.stat.rules b.run.txEnv b.run.txOut b.block.wds).1).state.getCode systemAddress =
      ByteArray.empty := (withdrawalsPass_getCode _ _ _ _ systemAddress).trans empty₂
  have reqNe := pass.caller_ne (a := a) empty₃ avoidReq
  have hon : b.benv.stat.rules.header.requestsHash = true := h.kept.requestsHash
  have hcontracts := h.body.contracts_eq hon
  have htargetNe : ∀ s ∈ b.run.requests, s.target ≠ a := by
    intro s hs
    have hmem : (s.type, s.target) ∈ b.fork.ruleSet.requests := by
      change (s.type, s.target) ∈ b.benv.stat.rules.requests
      rw [hcontracts]
      exact List.mem_map_of_mem hs
    have hboth := keptFork_requests_not_ring h.kept _ hmem
    rcases ha with rfl | rfl
    · exact hboth.1
    · exact hboth.2
  refine ⟨fun f hf => ?_, ?_⟩
  · rw [List.flatMap_append, List.mem_append] at hf
    rcases hf with hf | hf
    · exact roots.caller_ne emptyPre senders authorities avoidTxs f hf
    · unfold requestRootsOf at hf
      rw [List.mem_flatMap] at hf
      obtain ⟨r, hr, hfr⟩ := hf
      rw [List.mem_flatMap] at hr
      obtain ⟨s, hs, hrs⟩ := hr
      exact reqNe s hs (htargetNe s hs) f (List.mem_flatMap.mpr ⟨r, hrs, hfr⟩)
  · rw [final hrules.noRewards]
    exact pass.empty_stays empty₃ avoidReq

/-- Storage chain across the transactions, withdrawals, and request pass of a kept step. -/
private theorem postPre_chain (h : KeptStep cfg b post) {a : Adr} {C : ByteArray}
    (codePre : b.run.preState.getCode a = C) (hc : C.toList ≠ []) (hd : ¬ isValidDelegation C) :
    KeptChain a (b.run.preState.getStor a)
      ((b.run.txRoots ++ requestRootsOf b.run.requests).flatMap (Root.keptAt a)) (post.state.getStor a) ∧
      post.state.getCode a = C := by
  have hrules : KeptRules b.benv.stat.rules := h.kept.rules
  obtain ⟨st, out, pass, final, -⟩ := h.body.stages
  obtain ⟨decoded, -, roots⟩ := h.body.transactions
  have hcPre : (b.run.preState.getCode a).toList ≠ [] := by rw [codePre]; exact hc
  have hdPre : ¬ isValidDelegation (b.run.preState.getCode a) := by rw [codePre]; exact hd
  obtain ⟨chain₂, code₂⟩ := roots.chain hrules (a := a) hcPre hdPre AdrSet.not_mem_empty
  simp only [Benv.withState] at chain₂ code₂
  have codeT : b.run.txEnv.state.getCode a = C := code₂.trans codePre
  have hcT : (b.run.txEnv.state.getCode a).toList ≠ [] := by rw [codeT]; exact hc
  have hcode := withdrawalsPass_getCode b.benv.stat.rules b.run.txEnv b.run.txOut b.block.wds a
  obtain ⟨chain₃, code₃⟩ := pass.chain (a := a)
    (by simpa only [Benv.withState, hcode] using hcT)
    (by simpa only [Benv.withState, hcode, codeT] using hd)
  have hstor := withdrawalsPass_getStor b.benv.stat.rules b.run.txEnv b.run.txOut b.block.wds hcT
  simp only [Benv.withState] at chain₃ code₃
  rw [hstor] at chain₃
  rw [hcode] at code₃
  rw [final hrules.noRewards, List.flatMap_append]
  exact ⟨chain₂.append chain₃, code₃.trans codeT⟩

/-! ## Beacon-roots pre-call extraction (`beaconRootsAddress`) -/

/-- **Beacon-roots frame decomposition on a covered kept step.** Given the unchecked system call's result `stBeacon`
(with `outBeacon.error = none`), `b.keptAt beaconRootsAddress` starts with the single system-caller frame `f` taking
`b.parent.state.getStor beaconRootsAddress` to `stBeacon.getStor beaconRootsAddress`, followed by `mid` (up to
`b.run.preState`) and `after` (up to `post.state`), every frame of `mid ++ after` having `EntryIn` and
`caller ≠ systemAddress`. -/
theorem beaconRoots_frames (h : KeptStep cfg b post) (fork : CoveredFork b.fork)
    (code : b.parent.state.getCode beaconRootsAddress = beaconRootsCode)
    (empty : b.parent.state.getCode systemAddress = ByteArray.empty)
    (senders : NoSenderAt systemAddress b.run.senders)
    (authorities : NoAuthorityAt systemAddress b.run.senders)
    (avoid : NoCreateAt systemAddress b.run.roots)
    {stBeacon : State} {outBeacon : MsgCallOutput}
    (hcall : processUncheckedSystemTransaction b.benv beaconRootsAddress
      b.benv.stat.parentBeaconBlockRoot.toBytes = .ok (stBeacon, outBeacon))
    (hclean : outBeacon.error = none) :
    post.state.getCode beaconRootsAddress = beaconRootsCode ∧
      post.state.getCode systemAddress = ByteArray.empty ∧
      ∃ f mid after,
        b.keptAt beaconRootsAddress = f :: (mid ++ after) ∧
        Exec.Frame.EntryIn beaconRootsAddress beaconRootsCode b.benv.stat f ∧
        f.sevm.caller = systemAddress ∧
        f.sevm.data = b.benv.stat.parentBeaconBlockRoot.toBytes ∧
        Devm.getStor f.pre beaconRootsAddress = b.parent.state.getStor beaconRootsAddress ∧
        Devm.getStor f.post beaconRootsAddress = stBeacon.getStor beaconRootsAddress ∧
        KeptChain beaconRootsAddress (stBeacon.getStor beaconRootsAddress) mid
          (b.run.preState.getStor beaconRootsAddress) ∧
        KeptChain beaconRootsAddress (b.run.preState.getStor beaconRootsAddress) after
          (post.state.getStor beaconRootsAddress) ∧
        ∀ g ∈ mid ++ after,
          Exec.Frame.EntryIn beaconRootsAddress beaconRootsCode b.benv.stat g ∧
          g.sevm.caller ≠ systemAddress := by
  have hmem : (beaconRootsAddress, beaconRootsCode) ∈ systemContracts := by
    simp only [systemContracts, List.mem_cons, true_or]
  obtain ⟨-, hdC, hcC⟩ := systemContracts_facts _ hmem
  have hon : b.benv.stat.rules.sys.beaconRoots = true :=
    fork.cases (motive := fun f => f.ruleSet.sys.beaconRoots = true) rfl rfl rfl rfl
  have hbal : b.benv.stat.rules.bal = none := fork.rules_bal_none
  obtain ⟨beacon, beaconBal, beaconRoots, historyRoots, hb, cb, -, ch, hpreEq⟩ := h.body.pre
  have hb' : beaconRootsCall b.benv.stat.rules b.benv = .ok (stBeacon, {}) := by
    unfold beaconRootsCall
    rw [ite_eq_left hon]
    simp only [Except.mapError, hcall, bind, Except.bind, BalBuilder.incorporateSystem, hbal]
  have hstB : beacon = stBeacon := (Prod.mk.inj (Except.ok.inj (hb.symm.trans hb'))).1
  subst hstB
  unfold PreCall at cb
  rw [ite_eq_left hon] at cb
  obtain ⟨out', rootsB⟩ := cb
  have houtEq : out' = outBeacon := (Prod.mk.inj (Except.ok.inj (rootsB.1.symm.trans hcall))).2
  subst houtEq
  obtain ⟨f, hflatB, hcaller, -, hdata, hpreS, hpostS⟩ :=
    covered_system_root (show CoveredFork b.benv.stat.fork from fork) hmem
      (show b.benv.state.getCode beaconRootsAddress = beaconRootsCode from code) hclean rootsB
  have avoidPre : NoCreateAt systemAddress b.run.preRoots := avoid.left.left
  have avoidTxs : NoCreateAt systemAddress b.run.txRoots := avoid.left.right
  have avoidReq : NoCreateAt systemAddress (requestRootsOf b.run.requests) := avoid.right
  rw [hpreEq] at avoidPre
  have emptyEnv : b.benv.state.getCode systemAddress = ByteArray.empty := empty
  have empty₁ := (show PreCall b.benv.stat.rules.sys.beaconRoots b.benv beaconRootsAddress
      b.benv.stat.parentBeaconBlockRoot.toBytes beacon beaconRoots by
    unfold PreCall; rw [ite_eq_left hon]; exact ⟨out', rootsB⟩).empty_stays emptyEnv avoidPre.left
  have emptyPre := ch.empty_stays empty₁ avoidPre.right
  have code₁ : beacon.getCode beaconRootsAddress = beaconRootsCode :=
    (rootsB.chain
      (by change (b.parent.state.getCode beaconRootsAddress).toList ≠ []; rw [code]; exact hcC)
      (by change ¬ isValidDelegation (b.parent.state.getCode beaconRootsAddress); rw [code]; exact hdC)).2.trans code
  obtain ⟨chainMid, codePre⟩ := ch.chain (a := beaconRootsAddress)
    (by change (beacon.getCode beaconRootsAddress).toList ≠ []; rw [code₁]; exact hcC)
    (by change ¬ isValidDelegation (beacon.getCode beaconRootsAddress); rw [code₁]; exact hdC)
  simp only [Benv.withState] at chainMid codePre
  have codePre' : b.run.preState.getCode beaconRootsAddress = beaconRootsCode := codePre.trans code₁
  obtain ⟨chainAfter, codePost⟩ := h.postPre_chain codePre' hcC hdC
  obtain ⟨afterCaller, emptyPost⟩ := h.postPre_caller_ne (.inl rfl) emptyPre senders authorities avoidTxs avoidReq
  have midCaller := ch.caller_ne (a := beaconRootsAddress) empty₁ avoidPre.right (by decide)
  have allEntries := h.body.entry_in h.kept.rules code hcC hdC AdrSet.not_mem_empty h.data_fits
  have hkeptEq : b.keptAt beaconRootsAddress =
      f :: (historyRoots.flatMap (Root.keptAt beaconRootsAddress) ++
        (b.run.txRoots ++ requestRootsOf b.run.requests).flatMap (Root.keptAt beaconRootsAddress)) := by
    unfold KeptBlock.keptAt BodyRun.roots
    rw [hpreEq, List.append_assoc, List.append_assoc, List.flatMap_append, hflatB,
      List.singleton_append, List.flatMap_append]
  have hfMem : f ∈ b.keptAt beaconRootsAddress := by
    rw [hkeptEq]
    exact List.mem_cons_self
  refine ⟨codePost, emptyPost, f, historyRoots.flatMap (Root.keptAt beaconRootsAddress),
    (b.run.txRoots ++ requestRootsOf b.run.requests).flatMap (Root.keptAt beaconRootsAddress),
    hkeptEq, allEntries f hfMem, hcaller, hdata, hpreS, hpostS, chainMid, chainAfter, ?_⟩
  intro g hg
  have hgMem : g ∈ b.keptAt beaconRootsAddress := by
    rw [hkeptEq]
    exact List.mem_cons_of_mem _ hg
  refine ⟨allEntries g hgMem, ?_⟩
  rcases List.mem_append.mp hg with hg | hg
  · exact midCaller g hg
  · exact afterCaller g hg

/-- **Beacon-roots storage corollary on a covered kept step.** When every non-system `EntryIn` frame at
`beaconRootsAddress` leaves its storage unchanged, both `b.run.preState` and `post.state` hold `stBeacon`'s storage at
`beaconRootsAddress`. -/
theorem beaconRoots_stor (h : KeptStep cfg b post) (fork : CoveredFork b.fork)
    (code : b.parent.state.getCode beaconRootsAddress = beaconRootsCode)
    (empty : b.parent.state.getCode systemAddress = ByteArray.empty)
    (senders : NoSenderAt systemAddress b.run.senders)
    (authorities : NoAuthorityAt systemAddress b.run.senders)
    (avoid : NoCreateAt systemAddress b.run.roots)
    {stBeacon : State} {outBeacon : MsgCallOutput}
    (hcall : processUncheckedSystemTransaction b.benv beaconRootsAddress
      b.benv.stat.parentBeaconBlockRoot.toBytes = .ok (stBeacon, outBeacon))
    (hclean : outBeacon.error = none)
    (readSilent : ∀ g, Exec.Frame.EntryIn beaconRootsAddress beaconRootsCode b.benv.stat g →
      g.sevm.caller ≠ systemAddress →
      Devm.getStor g.post beaconRootsAddress = Devm.getStor g.pre beaconRootsAddress) :
    post.state.getCode beaconRootsAddress = beaconRootsCode ∧
      post.state.getCode systemAddress = ByteArray.empty ∧
      b.run.preState.getStor beaconRootsAddress = stBeacon.getStor beaconRootsAddress ∧
      post.state.getStor beaconRootsAddress = stBeacon.getStor beaconRootsAddress := by
  obtain ⟨hcodeP, hemptyP, f, mid, after, -, -, -, -, -, -, cMid, cAfter, hframes⟩ :=
    h.beaconRoots_frames fork code empty senders authorities avoid hcall hclean
  have hmid : b.run.preState.getStor beaconRootsAddress = stBeacon.getStor beaconRootsAddress :=
    cMid.stor_eq fun g hg =>
      let ⟨he, hc⟩ := hframes g (List.mem_append_left _ hg)
      readSilent g he hc
  have hafter : post.state.getStor beaconRootsAddress = b.run.preState.getStor beaconRootsAddress :=
    cAfter.stor_eq fun g hg =>
      let ⟨he, hc⟩ := hframes g (List.mem_append_right _ hg)
      readSilent g he hc
  exact ⟨hcodeP, hemptyP, hmid, hafter.trans hmid⟩

/-! ## History-storage pre-call extraction (`historyStorageAddress`) -/

/-- **The intermediate state before `historyStorageCall`**, with `historyStorageCode` preserved, `systemAddress` empty,
and a `KeptChain` of non-system `EntryIn` frames from `b.parent.state` to `beacon`. -/
theorem history_pre (h : KeptStep cfg b post)
    (code : b.parent.state.getCode historyStorageAddress = historyStorageCode)
    (empty : b.parent.state.getCode systemAddress = ByteArray.empty)
    (avoid : NoCreateAt systemAddress b.run.roots) :
    ∃ beacon beaconBal beaconRoots historyRoots,
      beaconRootsCall b.benv.stat.rules b.benv = .ok (beacon, beaconBal) ∧
      historyStorageCall b.benv.stat.rules (b.benv.withState beacon) beaconBal =
        .ok (b.run.preState, b.run.preBal) ∧
      PreCall b.benv.stat.rules.sys.historyStorage (b.benv.withState beacon) historyStorageAddress
        b.block.header.parentHash.toBytes b.run.preState historyRoots ∧
      b.run.preRoots = beaconRoots ++ historyRoots ∧
      beacon.getCode historyStorageAddress = historyStorageCode ∧
      beacon.getCode systemAddress = ByteArray.empty ∧
      KeptChain historyStorageAddress (b.parent.state.getStor historyStorageAddress)
        (beaconRoots.flatMap (Root.keptAt historyStorageAddress)) (beacon.getStor historyStorageAddress) ∧
      ∀ g ∈ beaconRoots.flatMap (Root.keptAt historyStorageAddress),
        Exec.Frame.EntryIn historyStorageAddress historyStorageCode b.benv.stat g ∧
        g.sevm.caller ≠ systemAddress := by
  have hmem : (historyStorageAddress, historyStorageCode) ∈ systemContracts := by
    simp only [systemContracts, List.mem_cons, true_or, or_true]
  obtain ⟨-, hdC, hcC⟩ := systemContracts_facts _ hmem
  obtain ⟨beacon, beaconBal, beaconRoots, historyRoots, hb, cb, hh, ch, hpreEq⟩ := h.body.pre
  have hdata := h.lastBlockHash.2
  rw [hdata] at ch
  have avoidPre : NoCreateAt systemAddress b.run.preRoots := avoid.left.left
  rw [hpreEq] at avoidPre
  have codeEnv : b.benv.state.getCode historyStorageAddress = historyStorageCode := code
  have emptyEnv : b.benv.state.getCode systemAddress = ByteArray.empty := empty
  obtain ⟨chainB, codeB⟩ := cb.chain (a := historyStorageAddress)
    (by rw [codeEnv]; exact hcC) (by rw [codeEnv]; exact hdC)
  have emptyB := cb.empty_stays emptyEnv avoidPre.left
  have callerB := cb.caller_ne (a := historyStorageAddress) emptyEnv avoidPre.left (by decide)
  have entryB := cb.entry_in codeEnv hcC hdC (by rw [B256.length_toBytes]; decide)
  exact ⟨beacon, beaconBal, beaconRoots, historyRoots, hb, hh, ch, hpreEq,
    codeB.trans codeEnv, emptyB, chainB, fun g hg => ⟨entryB g hg, callerB g hg⟩⟩

/-- **History-storage frame decomposition on a covered kept step.** Given `beacon` from `history_pre` and the unchecked
system call's result `(stHist, outHist)` on `b.block.header.parentHash.toBytes`, `b.run.preState = stHist` and
`b.keptAt historyStorageAddress` splits as `before ++ f :: after`, with `f` the single system-caller frame and every
frame in `before ++ after` having `EntryIn` and `caller ≠ systemAddress`. -/
theorem historyStorage_frames (h : KeptStep cfg b post) (fork : CoveredFork b.fork)
    (code : b.parent.state.getCode historyStorageAddress = historyStorageCode)
    (senders : NoSenderAt systemAddress b.run.senders)
    (authorities : NoAuthorityAt systemAddress b.run.senders)
    (avoid : NoCreateAt systemAddress b.run.roots)
    {beacon stHist : State} {beaconBal : BalBuilder} {beaconRoots historyRoots : List Root}
    {outHist : MsgCallOutput}
    (hh : historyStorageCall b.benv.stat.rules (b.benv.withState beacon) beaconBal =
      .ok (b.run.preState, b.run.preBal))
    (ch : PreCall b.benv.stat.rules.sys.historyStorage (b.benv.withState beacon) historyStorageAddress
      b.block.header.parentHash.toBytes b.run.preState historyRoots)
    (hpreEq : b.run.preRoots = beaconRoots ++ historyRoots)
    (codeB : beacon.getCode historyStorageAddress = historyStorageCode)
    (emptyB : beacon.getCode systemAddress = ByteArray.empty)
    (chainB : KeptChain historyStorageAddress (b.parent.state.getStor historyStorageAddress)
      (beaconRoots.flatMap (Root.keptAt historyStorageAddress)) (beacon.getStor historyStorageAddress))
    (beforeFacts : ∀ g ∈ beaconRoots.flatMap (Root.keptAt historyStorageAddress),
      Exec.Frame.EntryIn historyStorageAddress historyStorageCode b.benv.stat g ∧
      g.sevm.caller ≠ systemAddress)
    (hcall : processUncheckedSystemTransaction (b.benv.withState beacon) historyStorageAddress
      b.block.header.parentHash.toBytes = .ok (stHist, outHist))
    (hclean : outHist.error = none) :
    b.run.preState = stHist ∧
      post.state.getCode historyStorageAddress = historyStorageCode ∧
      post.state.getCode systemAddress = ByteArray.empty ∧
      ∃ before f after,
        b.keptAt historyStorageAddress = before ++ f :: after ∧
        KeptChain historyStorageAddress (b.parent.state.getStor historyStorageAddress) before
          (beacon.getStor historyStorageAddress) ∧
        Exec.Frame.EntryIn historyStorageAddress historyStorageCode b.benv.stat f ∧
        f.sevm.caller = systemAddress ∧
        f.sevm.data = b.block.header.parentHash.toBytes ∧
        Devm.getStor f.pre historyStorageAddress = beacon.getStor historyStorageAddress ∧
        Devm.getStor f.post historyStorageAddress = stHist.getStor historyStorageAddress ∧
        KeptChain historyStorageAddress (b.run.preState.getStor historyStorageAddress) after
          (post.state.getStor historyStorageAddress) ∧
        ∀ g ∈ before ++ after,
          Exec.Frame.EntryIn historyStorageAddress historyStorageCode b.benv.stat g ∧
          g.sevm.caller ≠ systemAddress := by
  have hmem : (historyStorageAddress, historyStorageCode) ∈ systemContracts := by
    simp only [systemContracts, List.mem_cons, true_or, or_true]
  obtain ⟨-, hdC, hcC⟩ := systemContracts_facts _ hmem
  have hon : b.benv.stat.rules.sys.historyStorage = true :=
    fork.cases (motive := fun f => f.ruleSet.sys.historyStorage = true) rfl rfl rfl rfl
  have hbal : b.benv.stat.rules.bal = none := fork.rules_bal_none
  have hlast : (b.benv.withState beacon).stat.blockHashes.getLast? = some b.block.header.parentHash :=
    h.lastBlockHash.1
  have hh' : historyStorageCall b.benv.stat.rules (b.benv.withState beacon) beaconBal = .ok (stHist, beaconBal) := by
    unfold historyStorageCall
    rw [ite_eq_left hon]
    simp only [hlast, Option.toExcept, Except.mapError, hcall, bind, Except.bind,
      BalBuilder.incorporateSystem, hbal]
  have hpreState : b.run.preState = stHist := (Prod.mk.inj (Except.ok.inj (hh.symm.trans hh'))).1
  unfold PreCall at ch
  rw [ite_eq_left hon] at ch
  obtain ⟨out', rootsH⟩ := ch
  rw [hpreState] at rootsH
  have houtEq : out' = outHist := (Prod.mk.inj (Except.ok.inj (rootsH.1.symm.trans hcall))).2
  subst houtEq
  obtain ⟨f, hflatH, hcaller, -, hdata, hpreS, hpostS⟩ :=
    covered_system_root (show CoveredFork (b.benv.withState beacon).stat.fork from fork) hmem
      (show (b.benv.withState beacon).state.getCode historyStorageAddress = historyStorageCode from codeB)
      hclean rootsH
  have avoidPre : NoCreateAt systemAddress b.run.preRoots := avoid.left.left
  have avoidTxs : NoCreateAt systemAddress b.run.txRoots := avoid.left.right
  have avoidReq : NoCreateAt systemAddress (requestRootsOf b.run.requests) := avoid.right
  rw [hpreEq] at avoidPre
  have emptyPre : b.run.preState.getCode systemAddress = ByteArray.empty := by
    rw [hpreState]
    exact (show PreCall b.benv.stat.rules.sys.historyStorage (b.benv.withState beacon) historyStorageAddress
        b.block.header.parentHash.toBytes stHist historyRoots by
      unfold PreCall; rw [ite_eq_left hon]; exact ⟨out', rootsH⟩).empty_stays
      (show (b.benv.withState beacon).state.getCode systemAddress = ByteArray.empty from emptyB) avoidPre.right
  have codePre : b.run.preState.getCode historyStorageAddress = historyStorageCode := by
    rw [hpreState]
    exact (rootsH.chain
      (by change (beacon.getCode historyStorageAddress).toList ≠ []; rw [codeB]; exact hcC)
      (by change ¬ isValidDelegation (beacon.getCode historyStorageAddress); rw [codeB]; exact hdC)).2.trans codeB
  obtain ⟨chainAfter, codePost⟩ := h.postPre_chain codePre hcC hdC
  obtain ⟨afterCaller, emptyPost⟩ := h.postPre_caller_ne (.inr rfl) emptyPre senders authorities avoidTxs avoidReq
  have allEntries := h.body.entry_in h.kept.rules code hcC hdC AdrSet.not_mem_empty h.data_fits
  have hkeptEq : b.keptAt historyStorageAddress =
      beaconRoots.flatMap (Root.keptAt historyStorageAddress) ++
        f :: ((b.run.txRoots ++ requestRootsOf b.run.requests).flatMap (Root.keptAt historyStorageAddress)) := by
    unfold KeptBlock.keptAt BodyRun.roots
    rw [hpreEq, List.append_assoc, List.append_assoc, List.flatMap_append, List.flatMap_append,
      hflatH, List.singleton_append]
  have hfMem : f ∈ b.keptAt historyStorageAddress := by
    rw [hkeptEq]
    exact List.mem_append_right _ List.mem_cons_self
  refine ⟨hpreState, codePost, emptyPost,
    beaconRoots.flatMap (Root.keptAt historyStorageAddress), f,
    (b.run.txRoots ++ requestRootsOf b.run.requests).flatMap (Root.keptAt historyStorageAddress),
    hkeptEq, chainB, allEntries f hfMem, hcaller, hdata, hpreS, hpostS, chainAfter, ?_⟩
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact beforeFacts g hg
  · have hgMem : g ∈ b.keptAt historyStorageAddress := by
      rw [hkeptEq]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hg)
    exact ⟨allEntries g hgMem, afterCaller g hg⟩

/-- **History-storage storage corollary on a covered kept step.** When every non-system `EntryIn` frame at
`historyStorageAddress` leaves its storage unchanged, `beacon` holds `b.parent.state`'s storage at
`historyStorageAddress`, and both `b.run.preState` and `post.state` hold `stHist`'s storage there. -/
theorem historyStorage_stor (h : KeptStep cfg b post) (fork : CoveredFork b.fork)
    (code : b.parent.state.getCode historyStorageAddress = historyStorageCode)
    (empty : b.parent.state.getCode systemAddress = ByteArray.empty)
    (senders : NoSenderAt systemAddress b.run.senders)
    (authorities : NoAuthorityAt systemAddress b.run.senders)
    (avoid : NoCreateAt systemAddress b.run.roots)
    (readSilent : ∀ g, Exec.Frame.EntryIn historyStorageAddress historyStorageCode b.benv.stat g →
      g.sevm.caller ≠ systemAddress →
      Devm.getStor g.post historyStorageAddress = Devm.getStor g.pre historyStorageAddress)
    (callStep : ∀ {beacon : State}, beacon.getCode historyStorageAddress = historyStorageCode →
      beacon.getStor historyStorageAddress = b.parent.state.getStor historyStorageAddress →
      ∃ stHist outHist,
        processUncheckedSystemTransaction (b.benv.withState beacon) historyStorageAddress
          b.block.header.parentHash.toBytes = .ok (stHist, outHist) ∧
        outHist.error = none ∧
        stHist.getStor historyStorageAddress =
          (b.parent.state.getStor historyStorageAddress).set
            ((b.block.header.number.toB256 - 1) % 0x1fff) b.block.header.parentHash) :
    post.state.getCode historyStorageAddress = historyStorageCode ∧
      post.state.getCode systemAddress = ByteArray.empty ∧
      b.run.preState.getStor historyStorageAddress =
        (b.parent.state.getStor historyStorageAddress).set
          ((b.block.header.number.toB256 - 1) % 0x1fff) b.block.header.parentHash ∧
      post.state.getStor historyStorageAddress =
        (b.parent.state.getStor historyStorageAddress).set
          ((b.block.header.number.toB256 - 1) % 0x1fff) b.block.header.parentHash := by
  obtain ⟨beacon, beaconBal, beaconRoots, historyRoots, _, hh, ch, hpreEq, codeB, emptyB, chainB, beforeFacts⟩ :=
    h.history_pre code empty avoid
  have hstorB : beacon.getStor historyStorageAddress = b.parent.state.getStor historyStorageAddress :=
    chainB.stor_eq fun g hg =>
      let ⟨he, hc⟩ := beforeFacts g hg
      readSilent g he hc
  obtain ⟨stHist, outHist, hcall, hclean, hwrite⟩ := callStep codeB hstorB
  obtain ⟨hpreEqS, hcodeP, hemptyP, before, f, after, -, -, -, -, -, -, -, cAfter, hframes⟩ :=
    h.historyStorage_frames fork code senders authorities avoid hh ch hpreEq codeB emptyB chainB beforeFacts
      hcall hclean
  have hafter : post.state.getStor historyStorageAddress = b.run.preState.getStor historyStorageAddress :=
    cAfter.stor_eq fun g hg =>
      let ⟨he, hc⟩ := hframes g (List.mem_append_right _ hg)
      readSilent g he hc
  have hpreStor : b.run.preState.getStor historyStorageAddress =
      (b.parent.state.getStor historyStorageAddress).set
        ((b.block.header.number.toB256 - 1) % 0x1fff) b.block.header.parentHash := by
    rw [hpreEqS, hwrite]
  exact ⟨hcodeP, hemptyP, hpreStor, hafter.trans hpreStor⟩

end KeptStep

/-! ## KeptHistory splitting, tip links, consecutive numbers, and strict timestamps -/

namespace KeptHistory

variable {cfg : ChainConfig} {start post : BlockChain} {blocks : List KeptBlock}

/-- Split a `KeptHistory` across an append `xs ++ ys`. -/
theorem append_inv {xs ys : List KeptBlock} (h : KeptHistory cfg start (xs ++ ys) post) :
    ∃ mid, KeptHistory cfg start xs mid ∧ KeptHistory cfg mid ys post := by
  induction ys using List.reverseRecOn generalizing post with
  | nil =>
      rw [List.append_nil] at h
      exact ⟨post, h, .refl⟩
  | append_singleton ys b ih =>
      rw [← List.append_assoc] at h
      obtain ⟨prior, step⟩ := snoc_inv h
      obtain ⟨mid, hxs, hys⟩ := ih prior
      exact ⟨mid, hxs, .step hys step⟩

/-- Split a `KeptHistory` at block `b` (`blocks = pre ++ b :: rest`). -/
theorem split_cons {pre rest : List KeptBlock} {b : KeptBlock}
    (h : KeptHistory cfg start (pre ++ b :: rest) post) :
    ∃ next, KeptHistory cfg start pre b.parent ∧ KeptStep cfg b next ∧ KeptHistory cfg next rest post := by
  have heq : pre ++ b :: rest = (pre ++ [b]) ++ rest := by simp only [List.append_assoc, List.singleton_append]
  rw [heq] at h
  obtain ⟨next, hpreB, hrest⟩ := append_inv h
  obtain ⟨hpre, hstep⟩ := snoc_inv hpreB
  exact ⟨next, hpre, hstep, hrest⟩

/-- Random-access split of a `KeptHistory` at `blocks[i]? = some b`. -/
theorem split_at {i : Nat} {b : KeptBlock} (h : KeptHistory cfg start blocks post)
    (hi : blocks[i]? = some b) :
    ∃ next, KeptHistory cfg start (blocks.take i) b.parent ∧ KeptStep cfg b next ∧
      KeptHistory cfg next (blocks.drop (i + 1)) post := by
  have hsplit : blocks = blocks.take i ++ b :: blocks.drop (i + 1) := by
    have hlt : i < blocks.length := (List.getElem?_eq_some_iff.mp hi).1
    have hget : blocks[i] = b := Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans hi)
    conv_lhs => rw [← List.take_append_drop i blocks, List.drop_eq_getElem_cons hlt, hget]
  rw [hsplit] at h
  exact split_cons h

/-- The post-chain tip of `blocks ++ [b]` is `b.block`. -/
theorem tip_snoc {xs : List KeptBlock} {b : KeptBlock}
    (h : KeptHistory cfg start (xs ++ [b]) post) :
    post.blocks.getLast? = some b.block := by
  obtain ⟨-, step⟩ := snoc_inv h
  obtain ⟨_, -, -, -, -, hnew⟩ := step.header_links
  exact hnew

/-- **Previous block of block `i` in a `KeptHistory`.** At `i = 0`, `b.parent = start`, so `b` links to `start`'s tip;
at `i = k + 1`, `b.parent`'s tip is `blocks[k].block`, so `b.block.header.parentHash = blocks[k].block.header.hash`,
`b.block.header.number = blocks[k].block.header.number + 1`, and
`blocks[k].block.header.timestamp < b.block.header.timestamp`. -/
theorem prev_block_zero {b : KeptBlock} (h : KeptHistory cfg start blocks post)
    (h0 : blocks[0]? = some b) :
    b.parent = start ∧
      ∃ tip, start.blocks.getLast? = some tip ∧
        b.block.header.parentHash = tip.header.hash ∧
        b.block.header.number = tip.header.number + 1 ∧
        tip.header.timestamp < b.block.header.timestamp := by
  obtain ⟨next, hpre, step, -⟩ := h.split_at h0
  rw [List.take_zero] at hpre
  have hpar : b.parent = start := nil_inv hpre
  obtain ⟨tip, hlast, hph, hnum, hlt, -⟩ := step.header_links
  rw [hpar] at hlast
  exact ⟨hpar, tip, hlast, hph, hnum, hlt⟩

/-- Adjacent blocks `k` and `k + 1` in a `KeptHistory` satisfy `parentHash = prev.hash`, `number = prev.number + 1`,
and `prev.timestamp < curr.timestamp`. -/
theorem step_adj {k : Nat} {prev curr : KeptBlock} (h : KeptHistory cfg start blocks post)
    (hp : blocks[k]? = some prev) (hc : blocks[k + 1]? = some curr) :
    curr.parent.blocks.getLast? = some prev.block ∧
      curr.block.header.parentHash = prev.block.header.hash ∧
      curr.block.header.number = prev.block.header.number + 1 ∧
      prev.block.header.timestamp < curr.block.header.timestamp := by
  obtain ⟨_, htake, step, -⟩ := h.split_at hc
  rw [List.take_add_one, hp, Option.toList_some] at htake
  have htip := tip_snoc htake
  obtain ⟨parent, hlast, hph, hnum, hlt, -⟩ := step.header_links
  rw [htip] at hlast
  cases hlast
  exact ⟨htip, hph, hnum, hlt⟩

/-- **Consecutive block numbers across a `KeptHistory`.** For `i ≤ j`, block `j`'s number is block `i`'s plus `j - i`. -/
theorem number_add (h : KeptHistory cfg start blocks post) :
    ∀ {i j : Nat} {bi bj : KeptBlock}, i ≤ j →
      blocks[i]? = some bi → blocks[j]? = some bj →
      bj.block.header.number = bi.block.header.number + (j - i) := by
  intro i j
  obtain ⟨d, hd⟩ : ∃ d, j = i + d ∨ j < i :=
    if hij : i ≤ j then ⟨j - i, .inl (Nat.add_sub_of_le hij).symm⟩ else ⟨0, .inr (Nat.lt_of_not_le hij)⟩
  rcases hd with rfl | hlt
  · induction d with
    | zero =>
        intro bi bj _ hi hj
        rw [Nat.add_zero] at hj
        rw [Nat.add_zero, Nat.sub_self, Nat.add_zero]
        obtain rfl : bj = bi := Option.some.inj (hj.symm.trans hi)
        rfl
    | succ d ih =>
        intro bi bj _ hi hj
        have hlt : i + d < blocks.length := by
          have := (List.getElem?_eq_some_iff.mp hj).1
          omega
        have hmid : blocks[i + d]? = some blocks[i + d] := List.getElem?_eq_getElem hlt
        have prevEq := ih (Nat.le_add_right i d) hi hmid
        have adj := (h.step_adj hmid (by simpa only [Nat.add_assoc] using hj)).2.2.1
        omega
  · intro _ _ hij
    omega

/-- **Strict timestamp monotonicity across a `KeptHistory`.** For `i < j`, block `i`'s timestamp is strictly less than
block `j`'s. -/
theorem timestamp_lt (h : KeptHistory cfg start blocks post) :
    ∀ {i j : Nat} {bi bj : KeptBlock}, i < j →
      blocks[i]? = some bi → blocks[j]? = some bj →
      bi.block.header.timestamp < bj.block.header.timestamp := by
  intro i j bi bj hij hi hj
  obtain ⟨d, rfl⟩ : ∃ d, j = i + 1 + d := ⟨j - (i + 1), by omega⟩
  induction d generalizing bj with
  | zero =>
      rw [Nat.add_zero] at hj
      exact (h.step_adj hi hj).2.2.2
  | succ d ih =>
      have hlt : i + 1 + d < blocks.length := by
        have := (List.getElem?_eq_some_iff.mp hj).1
        omega
      have hmid : blocks[i + 1 + d]? = some blocks[i + 1 + d] := List.getElem?_eq_getElem hlt
      exact Nat.lt_trans (ih (by omega) hmid) (h.step_adj hmid (by simpa only [Nat.add_assoc] using hj)).2.2.2

end KeptHistory

end Blanc
