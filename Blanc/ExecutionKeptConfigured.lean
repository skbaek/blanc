import Blanc.ExecDeterminism
import Blanc.ExecutionKeptChain
import Blanc.ExecutionTraceCodeAt
import Blanc.ExecutionTraceCallerExclusion

/-!
# Configured histories as kept histories, and the kept carrier's uniqueness

A covered-fork configured history (`ConfiguredHistoryTrace`, the carrier of the request-contract libraries before
Amsterdam) is a kept history (`KeptHistory`, which also reaches Amsterdam) over the same blocks, at the same forks, with
the same block outputs and the same final chain.

* `ConfiguredBlockTrace.kept` and `ConfiguredHistoryTrace.kept`: the kept blocks of a configured block and history, and
  `ConfiguredBlockTrace.keptStep`, `ConfiguredHistoryTrace.keptHistory`: they form a kept step and a kept history. The
  parent, block, fork and output of each kept block are the configured block's, by definition.
* `KeptHistory.append`: a kept history followed by a kept history from its end is one kept history, so a configured
  prefix spliced with later kept steps (at Amsterdam, say) is a kept history (`ConfiguredHistoryTrace.splice`).
* `KeptStep.unique` and `KeptHistory.unique`: the kept carrier is determined by the chain it starts from and the
  blocks it applies. Two kept histories with the same blocks have the same kept blocks (forks, outputs, stages and
  roots, hence the same kept frames at every account) and the same end. So anything read off the kept blocks, a
  contract's submissions or emissions for instance, does not depend on which derivation produced them.
* `ConfiguredHistoryTrace.kept_noAuthority`, `ConfiguredHistoryTrace.kept_noSender`: the configured history's
  authorization and sender premises (`ConfiguredHistoryTrace.NoAuthorityAt`, `ConfiguredHistoryTrace.NoSenderAt`) give
  the kept blocks' ones, block by block.
-/

namespace Blanc

open Jaune ExecutionTrace

/-! ## Uniqueness, root by root -/

private theorem Root.eq_of {r r' : Root} (hf : r.frame = r'.frame) (he : r.evm = r'.evm) (hr : r.raw = r'.raw) :
    r = r' := by
  obtain ⟨f, e, raw, run⟩ := r
  obtain ⟨f', e', raw', run'⟩ := r'
  dsimp only at hf he hr
  subst hf he hr
  rw [Subsingleton.elim run run']

private theorem roots_eq : ∀ {rs rs' : List Root},
    rs.map (fun r => (r.frame, r.evm)) = rs'.map (fun r => (r.frame, r.evm)) →
    (∀ r ∈ rs, exec r.evm = r.raw) → (∀ r ∈ rs', exec r.evm = r.raw) → rs = rs'
  | [], [], _, _, _ => rfl
  | [], _ :: _, e, _, _ => by simp only [List.map_nil, List.map_cons, reduceCtorEq] at e
  | _ :: _, [], e, _, _ => by simp only [List.map_nil, List.map_cons, reduceCtorEq] at e
  | r :: rs, r' :: rs', e, h, h' => by
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at e
      obtain ⟨⟨hf, he⟩, et⟩ := e
      have hr : r.raw = r'.raw := by
        rw [← h r List.mem_cons_self, ← h' r' List.mem_cons_self, he]
      rw [Root.eq_of hf he hr,
        roots_eq et (fun x hx => h x (List.mem_cons_of_mem _ hx)) (fun x hx => h' x (List.mem_cons_of_mem _ hx))]

/-- A message determines its roots. -/
theorem MessageRoots.unique {msg : Msg} {state state' : State} {out out' : MsgCallOutput} {rs rs' : List Root}
    (h : MessageRoots msg state out rs) (h' : MessageRoots msg state' out' rs') : rs = rs' :=
  roots_eq (h.2.trans h'.2.symm) (fun _ hr => (h.mem_entry hr).2) (fun _ hr => (h'.mem_entry hr).2)

/-- A message that enters a halting machine away from an address keeps no frames there. -/
theorem MessageRoots.keptAt_nil_of_entry_halt
    {msg : Msg} {state : State} {out : MsgCallOutput} {rs : List Root}
    {frame : Frame} {evm : Evm} {raw : Execution} {a : Adr}
    (roots : MessageRoots msg state out rs)
    (entry : messageEntry msg = some (frame,evm))
    (stop : Evm.step evm = .halt raw) (away : evm.sta.currentTarget ≠ a) :
    rs.flatMap (Root.keptAt a) = [] := by
  let r : Root := ⟨frame,evm,raw,.halt stop⟩
  have selected : MessageRoots msg state out [r] := ⟨roots.1,by rw [entry]; rfl⟩
  rw [roots.unique selected]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
  unfold Root.keptAt
  split
  · change Exec.keptAt a (.halt stop) = []
    rw [Exec.keptAt]
  · rfl

/-- A transaction determines its post-state, output, sender and roots. -/
theorem TransactionRoots.unique {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {state state' : State}
    {bout₁ bout₂ : BlockOutput} {sender sender' : Adr} {rs rs' : List Root}
    (h : TransactionRoots benv bout tx index state bout₁ sender rs)
    (h' : TransactionRoots benv bout tx index state' bout₂ sender' rs') :
    state = state' ∧ bout₁ = bout₂ ∧ sender = sender' ∧ rs = rs' := by
  have e := h.1.symm.trans h'.1
  simp only [Except.ok.injEq, Prod.mk.injEq] at e
  obtain ⟨msg, _, _, hmsg, roots⟩ := h.2
  obtain ⟨msg', _, _, hmsg', roots'⟩ := h'.2
  rw [hmsg] at hmsg'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hmsg'
  obtain ⟨rfl, rfl⟩ := hmsg'
  exact ⟨e.1, e.2, rfl, roots.unique roots'⟩

/-- A transaction list determines its end, its senders and its roots. -/
theorem TransactionsRoots.unique {txis : List (Nat × Tx)} {benv final final' : Benv}
    {bout finalOut finalOut' : BlockOutput} {txs txs' : List (Adr × Tx)} {rs rs' : List Root}
    (h : TransactionsRoots txis benv bout final finalOut txs rs)
    (h' : TransactionsRoots txis benv bout final' finalOut' txs' rs') :
    final = final' ∧ finalOut = finalOut' ∧ txs = txs' ∧ rs = rs' := by
  induction h generalizing final' finalOut' txs' rs' with
  | nil => cases h'; exact ⟨rfl, rfl, rfl, rfl⟩
  | cons head _ ih =>
      cases h' with
      | cons head' tail' =>
          obtain ⟨rfl, rfl, rfl, rfl⟩ := head.unique head'
          obtain ⟨rfl, rfl, rfl, rfl⟩ := ih tail'
          exact ⟨rfl, rfl, rfl, rfl⟩

/-- A transaction list's senders list its transactions, in order. -/
theorem TransactionsRoots.map_snd {txis : List (Nat × Tx)} {benv final : Benv} {bout finalOut : BlockOutput}
    {txs : List (Adr × Tx)} {rs : List Root} (h : TransactionsRoots txis benv bout final finalOut txs rs) :
    txs.map Prod.snd = txis.map Prod.snd := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, ih]

/-- A request fold determines its end, its bytes, its access list and its steps. -/
theorem RequestRoots.unique {idx : Nat} {contracts : List (UInt8 × Adr)} {benv : Benv} {acc acc₁ acc₂ : List Bytes}
    {bal bal₁ bal₂ : BalBuilder} {final final' : State} {steps steps' : List RequestStep}
    (h : RequestRoots idx contracts benv acc bal final acc₁ bal₁ steps)
    (h' : RequestRoots idx contracts benv acc bal final' acc₂ bal₂ steps') :
    final = final' ∧ acc₁ = acc₂ ∧ bal₁ = bal₂ ∧ steps = steps' := by
  induction h generalizing final' acc₂ bal₂ steps' with
  | nil => cases h'; exact ⟨rfl, rfl, rfl, rfl⟩
  | cons hcall roots _ ih =>
      cases h' with
      | cons hcall' roots' tail' =>
          have e := hcall.symm.trans hcall'
          simp only [Except.ok.injEq, Prod.mk.injEq] at e
          obtain ⟨rfl, rfl⟩ := e
          obtain rfl := roots.unique roots'
          obtain ⟨rfl, rfl, rfl, rfl⟩ := ih tail'
          exact ⟨rfl, rfl, rfl, rfl⟩

private theorem PreCall.unique {on : Bool} {benv : Benv} {target : Adr} {data : Bytes} {st st' : State}
    {rs rs' : List Root} (h : PreCall on benv target data st rs) (h' : PreCall on benv target data st' rs') :
    st = st' ∧ rs = rs' := by
  unfold PreCall at h h'
  split at h
  · rename_i on
    rw [ite_eq_left on] at h'
    obtain ⟨_, hm⟩ := h
    obtain ⟨_, hm'⟩ := h'
    have e := hm.1.symm.trans hm'.1
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    exact ⟨e.1, hm.unique hm'⟩
  · rename_i off
    rw [ite_eq_right off] at h'
    exact ⟨h.1.trans h'.1.symm, h.2.trans h'.2.symm⟩

private theorem PreRoots.unique {benv : Benv} {st st' : State} {bal bal' : BalBuilder} {rs rs' : List Root}
    (h : PreRoots benv st bal rs) (h' : PreRoots benv st' bal' rs') : st = st' ∧ bal = bal' ∧ rs = rs' := by
  obtain ⟨beacon, beaconBal, beaconRoots, historyRoots, hb, cb, hh, ch, rfl⟩ := h
  obtain ⟨beacon', beaconBal', beaconRoots', historyRoots', hb', cb', hh', ch', rfl⟩ := h'
  have e := hb.symm.trans hb'
  simp only [Except.ok.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨-, rfl⟩ := cb.unique cb'
  have e := hh.symm.trans hh'
  simp only [Except.ok.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨-, rfl⟩ := ch.unique ch'
  exact ⟨rfl, rfl, rfl⟩

private theorem RequestPass.unique {benv : Benv} {bout out out' : BlockOutput} {st st' : State}
    {steps steps' : List RequestStep} (h : RequestPass benv bout st out steps) (h' : RequestPass benv bout st' out' steps') :
    st = st' ∧ out = out' ∧ steps = steps' := by
  unfold RequestPass at h h'
  split at h
  · rename_i on
    rw [ite_eq_left on] at h'
    obtain ⟨deposits, acc, bal, hp, roots, rfl⟩ := h
    obtain ⟨deposits', acc', bal', hp', roots', rfl⟩ := h'
    rw [hp] at hp'
    obtain rfl := Except.ok.inj hp'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := roots.unique roots'
    exact ⟨rfl, rfl, rfl⟩
  · rename_i off
    rw [ite_eq_right off] at h'
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨rfl, rfl, rfl⟩ := h'
    exact ⟨rfl, rfl, rfl⟩

/-- A body determines its post-state, its output and its stages. -/
theorem BodyRoots.unique {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header} {wds : List Withdrawal}
    {state state' : State} {bout bout' : BlockOutput} {run run' : BodyRun}
    (h : BodyRoots benv txs ommers wds state bout run) (h' : BodyRoots benv txs ommers wds state' bout' run') :
    state = state' ∧ bout = bout' ∧ run = run' := by
  have e := h.applied.symm.trans h'.applied
  simp only [Except.ok.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨preState, preBal, preRoots, txEnv, txOut, senders, txRoots, requests⟩ := run
  obtain ⟨preState', preBal', preRoots', txEnv', txOut', senders', txRoots', requests'⟩ := run'
  obtain ⟨rfl, rfl, rfl⟩ := h.pre.unique h'.pre
  obtain ⟨decoded, hd, troots⟩ := h.transactions
  obtain ⟨decoded', hd', troots'⟩ := h'.transactions
  rw [hd] at hd'
  obtain rfl := Except.ok.inj hd'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := troots.unique troots'
  obtain ⟨_, _, pass⟩ := h.requests
  obtain ⟨_, _, pass'⟩ := h'.requests
  obtain ⟨-, -, rfl⟩ := pass.unique pass'
  exact ⟨rfl, rfl, rfl⟩

/-- **A kept step is determined by its parent chain and its block**: the fork, the output, the stages and roots, and
the post chain. -/
theorem KeptStep.unique {cfg : ChainConfig} {b b' : KeptBlock} {post post' : BlockChain} (h : KeptStep cfg b post)
    (h' : KeptStep cfg b' post') (parent : b.parent = b'.parent) (block : b.block = b'.block) :
    b = b' ∧ post = post' := by
  obtain ⟨parent₀, block₀, fork, output, run⟩ := b
  obtain ⟨parent₁, block₁, fork', output', run'⟩ := b'
  dsimp only at parent block
  subst parent block
  have ep := h.transition.symm.trans h'.transition
  obtain rfl := Except.ok.inj ep
  have ef := h.forkAt.symm.trans h'.forkAt
  obtain rfl := Except.ok.inj ef
  obtain ⟨-, rfl, rfl⟩ := h.body.unique h'.body
  exact ⟨rfl, rfl⟩

/-! ## Kept histories: inversion, uniqueness, append -/

namespace KeptHistory

variable {cfg : ChainConfig} {start : BlockChain}

theorem nil_inv {post : BlockChain} (h : KeptHistory cfg start [] post) : post = start := by
  generalize e : ([] : List KeptBlock) = l at h
  cases h with
  | refl => rfl
  | step => simp only [List.nil_eq, List.append_eq_nil_iff, List.cons_ne_self, and_false] at e

theorem snoc_inv {blocks : List KeptBlock} {b : KeptBlock} {post : BlockChain}
    (h : KeptHistory cfg start (blocks ++ [b]) post) : KeptHistory cfg start blocks b.parent ∧ KeptStep cfg b post := by
  generalize e : blocks ++ [b] = l at h
  cases h with
  | refl => simp only [List.append_eq_nil_iff, List.cons_ne_self, and_false] at e
  | step prior step =>
      obtain ⟨hblocks, hb⟩ := List.append_inj' e rfl
      subst hblocks
      obtain rfl := List.head_eq_of_cons_eq hb
      exact ⟨prior, step⟩

/-- **A kept history is determined by its start and its blocks**: two kept histories from one chain applying the same
blocks have the same kept blocks, so the same forks, outputs and kept frames, and end on the same chain. -/
theorem unique {blocks blocks' : List KeptBlock} {post post' : BlockChain} (h : KeptHistory cfg start blocks post)
    (h' : KeptHistory cfg start blocks' post') (same : blocks.map KeptBlock.block = blocks'.map KeptBlock.block) :
    blocks = blocks' ∧ post = post' := by
  induction h generalizing blocks' post' with
  | refl =>
      obtain rfl := List.map_eq_nil_iff.mp same.symm
      exact ⟨rfl, (nil_inv h').symm⟩
  | @step blocks b post prior step ih =>
      rcases List.eq_nil_or_concat blocks' with rfl | ⟨xs, b', rfl⟩
      · simp only [List.map_append, List.map_cons, List.map_nil, List.append_eq_nil_iff, List.cons_ne_self,
          and_false] at same
      · rw [List.concat_eq_append] at same h' ⊢
        simp only [List.map_append, List.map_cons, List.map_nil] at same
        obtain ⟨same, e⟩ := List.append_inj' same rfl
        obtain ⟨prior', step'⟩ := snoc_inv h'
        obtain ⟨rfl, hp⟩ := ih prior' same
        obtain ⟨rfl, rfl⟩ := step.unique step' hp (List.head_eq_of_cons_eq e)
        exact ⟨rfl, rfl⟩

/-- **Kept histories compose**: one from `start` to `mid`, then one from `mid`, is one from `start`. -/
theorem append {mid post : BlockChain} {xs ys : List KeptBlock} (first : KeptHistory cfg start xs mid)
    (second : KeptHistory cfg mid ys post) : KeptHistory cfg start (xs ++ ys) post := by
  induction second with
  | refl => rw [List.append_nil]; exact first
  | step _ step ih =>
      rw [← List.append_assoc]
      exact .step ih step

end KeptHistory

/-! ## Configured histories as kept histories -/

namespace ExecutionTrace

variable {cfg : ChainConfig}

/-- The kept block of a configured block: its parent chain, block, fork and output, with the stages of its body. -/
noncomputable def ConfiguredBlockTrace.kept {pre post : BlockChain} (t : ConfiguredBlockTrace cfg pre post) :
    KeptBlock where
  parent := pre
  block := t.block
  fork := t.fork
  output := t.blockOutput
  run := (exists_bodyRoots t.bodyRun).choose

/-- **A configured block is a kept step**, ending on the same chain. -/
theorem ConfiguredBlockTrace.keptStep {pre post : BlockChain} (t : ConfiguredBlockTrace cfg pre post) :
    KeptStep cfg t.kept post where
  transition := t.transition
  forkAt := t.forkAt
  kept := .inl t.covered
  body := by
    have hstate : post.state = t.bodyState := congrArg BlockChain.state t.postEq
    rw [hstate]
    exact (exists_bodyRoots t.bodyRun).choose_spec

/-- The kept blocks of a configured history, in order. -/
noncomputable def ConfiguredHistoryTrace.kept {checkpoint : BlockChain} :
    {future : BlockChain} → ConfiguredHistoryTrace cfg checkpoint future → List KeptBlock
  | _, .refl _ _ _ => []
  | _, .step prior block => prior.kept ++ [block.kept]

/-- The blocks a configured history applies, in order. -/
def ConfiguredHistoryTrace.blocks {checkpoint : BlockChain} :
    {future : BlockChain} → ConfiguredHistoryTrace cfg checkpoint future → List Block
  | _, .refl _ _ _ => []
  | _, .step prior block => prior.blocks ++ [block.block]

/-- **A configured history is a kept history**, from the same checkpoint to the same chain. -/
theorem ConfiguredHistoryTrace.keptHistory {checkpoint future : BlockChain}
    (t : ConfiguredHistoryTrace cfg checkpoint future) : KeptHistory cfg checkpoint t.kept future := by
  induction t with
  | refl => exact .refl
  | step _ block ih => exact .step ih block.keptStep

/-- The kept history applies the configured history's blocks. -/
theorem ConfiguredHistoryTrace.kept_blocks {checkpoint future : BlockChain}
    (t : ConfiguredHistoryTrace cfg checkpoint future) : t.kept.map KeptBlock.block = t.blocks := by
  induction t with
  | refl => rfl
  | step _ _ ih =>
      simp only [ConfiguredHistoryTrace.kept, ConfiguredHistoryTrace.blocks, List.map_append, List.map_cons,
        List.map_nil, ih]
      rfl

/-- Every block of the kept history is at a covered fork. -/
theorem ConfiguredHistoryTrace.kept_covered {checkpoint future : BlockChain}
    (t : ConfiguredHistoryTrace cfg checkpoint future) : ∀ b ∈ t.kept, CoveredFork b.fork := by
  induction t with
  | refl => exact fun _ hb => absurd hb List.not_mem_nil
  | step _ block ih =>
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact ih b hb
      · rw [List.mem_singleton.mp hb]
        exact block.covered

/-- **Every kept history over a configured history's blocks is its kept history**: the kept blocks, so their forks,
outputs and kept frames, are the configured blocks', whichever derivation produced them. -/
theorem ConfiguredHistoryTrace.kept_unique {checkpoint future post : BlockChain}
    (t : ConfiguredHistoryTrace cfg checkpoint future) {blocks : List KeptBlock}
    (h : KeptHistory cfg checkpoint blocks post) (same : blocks.map KeptBlock.block = t.blocks) :
    blocks = t.kept ∧ post = future :=
  h.unique t.keptHistory (same.trans t.kept_blocks.symm)

/-- **The splice.** A configured history to `mid`, followed by a kept history from `mid` (Amsterdam steps, say), is one
kept history whose blocks are the configured history's kept blocks, all at covered forks, followed by the later ones. -/
theorem ConfiguredHistoryTrace.splice {checkpoint mid post : BlockChain} (t : ConfiguredHistoryTrace cfg checkpoint mid)
    {ys : List KeptBlock} (later : KeptHistory cfg mid ys post) : KeptHistory cfg checkpoint (t.kept ++ ys) post :=
  t.keptHistory.append later

/-- The sender `transactionMessage` returns is the one `checkTransaction` returned. -/
private theorem transactionMessage_checked {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {sender : Adr}
    {msg : Msg} (h : transactionMessage benv bout tx index = .ok (sender, msg)) :
    ∃ price hashes blob, checkTransaction benv.beginTransaction (transactionPreludeBout bout tx index) tx =
      .ok (sender, price, hashes, blob) := by
  unfold transactionMessage at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨_, _⟩, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨sender', price, hashes, blob⟩, hc, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨price, hashes, blob, hc⟩

/-- Along one transaction list, a retained trace and kept roots name the same senders. -/
private theorem noSender_of_trace {a : Adr} : ∀ {txis : List (Nat × Tx)} {benv final final' : Benv}
    {bout finalOut finalOut' : BlockOutput} {txs : List (Adr × Tx)} {rs : List Root}
    (t : ApplyTransactionsTrace txis benv bout final finalOut),
    TransactionsRoots txis benv bout final' finalOut' txs rs → t.NoSenderAt a → NoSenderAt a txs
  | _, _, _, _, _, _, _, _, _, .nil _ _, h, _ => by
      cases h
      exact fun _ hp => absurd hp List.not_mem_nil
  | _, _, _, _, _, _, _, _, _, .cons head tail, h, hs => by
      cases h with
      | cons roots rest =>
          have e := head.result.symm.trans roots.1
          simp only [Except.ok.injEq, Prod.mk.injEq] at e
          obtain ⟨rfl, rfl⟩ := e
          obtain ⟨_, _, _, hmsg, -⟩ := roots.2
          obtain ⟨_, _, _, hc⟩ := transactionMessage_checked hmsg
          have es := head.checked.symm.trans hc
          simp only [Except.ok.injEq, Prod.mk.injEq] at es
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · rw [← es.1]
            exact hs.1
          · exact noSender_of_trace tail rest hs.2 p hp

/-- On a covered fork, the kept stages' transactions open where the retained body trace's do. -/
private theorem BodyRoots.txStart {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput} {run : BodyRun}
    {state' : State} {bout' : BlockOutput}
    (h : BodyRoots benv txs ommers wds state bout run) (trace : AppliedBodyTrace benv txs ommers wds state' bout')
    (fork : CoveredFork benv.stat.fork) :
    run.preState = trace.historyState ∧ ({BlockOutput.init with bal := run.preBal} : BlockOutput) = .init := by
  have hbal : benv.stat.rules.bal = none := fork.rules_bal_none
  have hbeacon : benv.stat.rules.sys.beaconRoots = true :=
    fork.cases (motive := fun f => f.ruleSet.sys.beaconRoots = true) rfl rfl rfl rfl
  have hhistory : benv.stat.rules.sys.historyStorage = true :=
    fork.cases (motive := fun f => f.ruleSet.sys.historyStorage = true) rfl rfl rfl rfl
  obtain ⟨beacon, beaconBal, -, -, hb, -, hh, -, -⟩ := h.pre
  simp only [beaconRootsCall, hbeacon, ↓reduceIte, BalBuilder.incorporateSystem, hbal] at hb
  obtain ⟨⟨st, out⟩, hrun, hb⟩ := Except.bind_eq_ok hb
  simp only [Except.ok.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  rw [Except.mapError_eq_ok_iff] at hrun
  have e := hrun.symm.trans trace.beacon.run
  simp only [Except.ok.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, -⟩ := e
  simp only [historyStorageCall, hhistory, ↓reduceIte, BalBuilder.incorporateSystem, hbal] at hh
  obtain ⟨lastHash, hlast, hh⟩ := Except.bind_eq_ok hh
  obtain ⟨⟨st', out'⟩, hrun', hh⟩ := Except.bind_eq_ok hh
  simp only [Except.ok.injEq, Prod.mk.injEq] at hh
  obtain ⟨hpre, hpreBal⟩ := hh
  have el := hlast.symm.trans trace.lastHashRun
  obtain rfl := Except.ok.inj el
  rw [Except.mapError_eq_ok_iff] at hrun'
  have e' := hrun'.symm.trans trace.history.run
  simp only [Except.ok.injEq, Prod.mk.injEq] at e'
  refine ⟨hpre.symm.trans e'.1, ?_⟩
  rw [← hpreBal]
  rfl

/-- The checked senders of a configured block's transactions are its kept block's. -/
theorem ConfiguredBlockTrace.kept_noSender {pre post : BlockChain} (t : ConfiguredBlockTrace cfg pre post) {a : Adr}
    (h : t.bodyTrace.transactions.NoSenderAt a) : Blanc.NoSenderAt a t.kept.run.senders := by
  have body := t.keptStep.body
  obtain ⟨decoded, hd, roots⟩ := body.transactions
  have same : decoded = t.bodyTrace.decodedTxs := Except.ok.inj (hd.symm.trans t.bodyTrace.decodeRun)
  subst same
  obtain ⟨hstate, hout⟩ := BodyRoots.txStart (show BodyRoots (initBenv t.fork pre t.block.header) t.block.txs
    t.block.ommers t.block.wds post.state t.blockOutput t.kept.run from body) t.bodyTrace t.covered
  rw [hstate, hout] at roots
  exact noSender_of_trace t.bodyTrace.transactions roots h

/-- **No transaction is sent by `a`, on the kept blocks**, when none is on the configured history. -/
theorem ConfiguredHistoryTrace.kept_noSender {checkpoint future : BlockChain}
    (t : ConfiguredHistoryTrace cfg checkpoint future) {a : Adr} (h : t.NoSenderAt a) :
    ∀ b ∈ t.kept, Blanc.NoSenderAt a b.run.senders := by
  induction t with
  | refl => exact fun _ hb => absurd hb List.not_mem_nil
  | step _ block ih =>
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact ih h.1 b hb
      · rw [List.mem_singleton.mp hb]
        exact block.kept_noSender h.2

/-- The authorizations of a configured block's checked transactions are its kept block's. -/
theorem ConfiguredBlockTrace.kept_noAuthority {pre post : BlockChain} (t : ConfiguredBlockTrace cfg pre post)
    {a : Adr} (h : ∀ p ∈ t.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
      recoverAuthority auth = .ok authority → authority ≠ a) :
    Blanc.NoAuthorityAt a t.kept.run.senders := by
  obtain ⟨decoded, hd, roots⟩ := t.keptStep.body.transactions
  have same : decoded = t.bodyTrace.decodedTxs := Except.ok.inj (hd.symm.trans t.bodyTrace.decodeRun)
  subst same
  intro p hp auth hauth heq
  have hm : p.2 ∈ t.bodyTrace.decodedTxs.putIndex.map Prod.snd := by
    rw [← roots.map_snd]
    exact List.mem_map_of_mem hp
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hm
  exact h q hq auth (hqe ▸ hauth) a heq rfl

/-- **No authorization recovers to `a`, on the kept blocks**, when none does on the configured history. -/
theorem ConfiguredHistoryTrace.kept_noAuthority {checkpoint future : BlockChain}
    (t : ConfiguredHistoryTrace cfg checkpoint future) {a : Adr} (h : t.NoAuthorityAt a) :
    ∀ b ∈ t.kept, Blanc.NoAuthorityAt a b.run.senders := by
  induction t with
  | refl => exact fun _ hb => absurd hb List.not_mem_nil
  | step _ block ih =>
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact ih h.1 b hb
      · rw [List.mem_singleton.mp hb]
        exact block.kept_noAuthority h.2

end ExecutionTrace

end Blanc
