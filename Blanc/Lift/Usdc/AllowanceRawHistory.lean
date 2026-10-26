import Blanc.Lift.Usdc.ProxyContextCodes
import Blanc.Lift.Usdc.AllowLocalitySstore
import Blanc.Lift.Usdc.AllowLocalityV2_2

/-!
# The Pair's USDC allowance rows along an In-history

With the proxy runtime at `P` at the checkpoint and the codes run in `P`'s storage
context bounded at every raw node (`UsdcNodeCodes`, discharged by
`ConfiguredHistoryTraceIn.usdc_nodeCodes` in `ProxyContextCodes.lean`), every raw node and
the future see `P`'s cells through the history's raw chronology
(`rawNode_cellProvenance`, `cellProv_post`). This module classifies each raw successful
`SSTORE` at a tracked allowance row of the Pair and lifts the class to the history.

* `rawWrite_allowClass`: at a node of a raw frame running a certified implementation
  runtime, a write at a tracked row meets a root site of its write-site annotation
  (`ws_reach_start_noStateGas`, any eventual frame outcome), so it is non-increasing
  or its frame is one of the law's exceptions (`allow_class_of_wsObs`).
* `ConfiguredHistoryTraceIn.usdc_rawRowWrite`: every such write in the history, attributed
  to its raw frame at `P`: the library never writes (`Lib.cert_sstoreFree`), the proxy
  runtime writes no tracked row (`ProxyRowsApart`, stated), and the four implementation
  runtimes obey the law under the frame-local `RowSep` (`UsdcRowSep`, stated).
* `ConfiguredHistoryTraceIn.usdc_rowChange_attributed`: a tracked row that differs between
  checkpoint and future was last given its future word by an attributed raw write.
* `ConfiguredHistoryTraceIn.usdc_pairAllowance_noIncrease`: with no exception frame at
  `P` (`UsdcAllowException`), every tracked row of the Pair is at most its checkpoint
  word at every raw node and at the future.

The exceptions are read at the selector level of the raw frame (`AllowedFrame` of the
version's table: the Pair as caller of the caller-keyed entry points, the Pair named by
calldata word 4 of the owner-keyed entry points, the initializers), because a raw frame
may not succeed; the native-answer reading of V2/V2_1 owner frames
(`OldUsdcNativePairAnswer`) needs the frame's success.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace

/-- The library runtime has no `SSTORE` node. -/
theorem Lib.cert_sstoreFree :
    ∀ f ∈ Lib.cert.prog, f.nodesSatisfy (fun n _ => n != .reg .sstore) = true := by
  decide +kernel

/-- The raw recognizer's node decodes `SSTORE` with the write's key and value on top. -/
theorem successfulSstore?_decoded {m : Exec.Deriv} {w : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? m = some w) :
    Ninst.At m.sevm.code m.pc (.reg .sstore) ∧ ∃ rest, m.devm.stack = w.key :: w.value :: rest :=
  Exec.Deriv.successfulSstore?_decoded found

/-- **The allowance law at a raw `SSTORE`.** At a node of a frame entered at pc `0` without
state gas and running a certified code with a write-site annotation whose root sites the table
accepts, a write at a tracked Pair allowance row is non-increasing or in an allowed frame,
whatever the frame's eventual outcome. -/
theorem rawWrite_allowClass {G m : Exec.Deriv} (hpc : G.pc = 0)
    (hsg : G.sevm.benvStat.rules.stateGas = none) (chain : Exec.Deriv.ParentPrefix G m)
    {code : ByteArray} {c : Cert} {ann : List WAnn} {t : SelTable} {pair : Adr} {Tr : Adr → Prop}
    (hc : Cert.check code c = true) (hw : wsCert c ann = true) (hcode : G.sevm.code = code)
    (hsel : t.selT.known = true) (hok : (wsRoot ann).all (allowSiteOk t) = true)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ann) (WriteSite.Env.root G.sevm))
    {w : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? m = some w)
    (tracked : ∃ g, Tr g ∧ allowSlot pair g = w.key) :
    AllowedFrame t pair (WriteSite.Env.root G.sevm) ∨
      w.value.toNat ≤ (m.devm.getStorVal m.sevm.currentTarget w.key).toNat := by
  obtain ⟨decoded, rest, stack⟩ := successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ := reach_of_parentPrefix_noStateGas hc hpc hcode hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have obs := ws_reach_start_noStateGas (fun h => StepIn.toRun h) hw hsg reach tree
  have hsevm := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [hsevm]
  exact allow_class_of_wsObs hsel hok sep obs stack tracked

/-- The library runtime never writes. -/
theorem lib_no_sstore_node {G m : Exec.Deriv} (hpc : G.pc = 0)
    (hsg : G.sevm.benvStat.rules.stateGas = none) (chain : Exec.Deriv.ParentPrefix G m)
    (hcode : G.sevm.code = Lib.code) {w : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? m = some w) : False := by
  obtain ⟨decoded, -⟩ := successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ := reach_of_parentPrefix_noStateGas Lib.cert_check hpc hcode hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have holds := (Reach.nodesSatisfy Lib.cert_sstoreFree reach).1
  change κ.f.nodesSatisfy _ = true at holds
  rw [tree] at holds
  simp only [SFunc.nodesSatisfy, bne_self_eq_false, Bool.false_and, Bool.false_eq_true] at holds

/-! ## Premises about the Pair's rows -/

/-- **The proxy runtime writes no tracked row (stated).** Its write sites are its two fixed
slots (`implSlot`, `adminSlot`); this premise states that no successful `SSTORE` the proxy
runtime executes at `P` among `nodes` lands on a tracked Pair allowance row. -/
def ProxyRowsApart (P pair : Adr) (Tr : Adr → Prop) (nodes : List Exec.Deriv) : Prop :=
  ∀ m ∈ nodes, m.sevm.currentTarget = P → m.sevm.code = Proxy.code →
    ∀ w : Exec.StorageWrite, Exec.Deriv.successfulSstore? m = some w →
      ¬ ∃ g, Tr g ∧ allowSlot pair g = w.key

/-- **Frame-local row separation (stated).** The `RowSep` premise of the allowance law at
every raw frame at `P` running an implementation runtime. -/
def UsdcRowSep (P pair : Adr) (Tr : Adr → Prop) (frames : List Exec.Deriv) : Prop :=
  ∀ G ∈ frames, G.sevm.currentTarget = P →
    (G.sevm.code = ImplV1.code → RowSep 10 pair.toB256 (AllowKey Tr)
      (wsRoot ImplV1Ws.implWsAnn) (WriteSite.Env.root G.sevm)) ∧
    (G.sevm.code = ImplV2.code → RowSep 10 pair.toB256 (AllowKey Tr)
      (wsRoot ImplV2Ws.implWsAnn) (WriteSite.Env.root G.sevm)) ∧
    (G.sevm.code = ImplV2_1.code → RowSep 10 pair.toB256 (AllowKey Tr)
      (wsRoot ImplV2_1Ws.implWsAnn) (WriteSite.Env.root G.sevm)) ∧
    (G.sevm.code = Impl.code → RowSep 10 pair.toB256 (AllowKey Tr)
      (wsRoot ImplWs.implWsAnn) (WriteSite.Env.root G.sevm))

/-- **The law's exception frames.** A frame running an implementation runtime whose
selector-observed environment is one of its version's exceptions for the Pair. -/
def UsdcAllowException (pair : Adr) (G : Exec.Deriv) : Prop :=
  (G.sevm.code = ImplV1.code ∧ AllowedFrame selV1 pair (WriteSite.Env.root G.sevm)) ∨
    (G.sevm.code = ImplV2.code ∧ AllowedFrame selV2 pair (WriteSite.Env.root G.sevm)) ∨
    (G.sevm.code = ImplV2_1.code ∧ AllowedFrame selV2_1 pair (WriteSite.Env.root G.sevm)) ∨
    (G.sevm.code = Impl.code ∧ AllowedFrame selV2_2 pair (WriteSite.Env.root G.sevm))

/-- The caller- and owner-keyed part of `AllowedFrame`: the Pair as caller of a caller-keyed
entry point, or the Pair named by calldata word 4 of an owner-keyed one. -/
def PairAllowedFrame (t : SelTable) (pair : Adr) (ε : WriteSite.Env) : Prop :=
  (t.selT.eval ε ∈ t.callers ∧ ε.caller.toAdr = pair) ∨
    (t.selT.eval ε ∈ t.owners ∧ ((Term.cd (.const 4)).eval ε).toAdr = pair)

/-- **The Pair's own exception frames**: `UsdcAllowException` without the initializers. -/
def UsdcPairException (pair : Adr) (G : Exec.Deriv) : Prop :=
  (G.sevm.code = ImplV1.code ∧ PairAllowedFrame selV1 pair (WriteSite.Env.root G.sevm)) ∨
    (G.sevm.code = ImplV2.code ∧ PairAllowedFrame selV2 pair (WriteSite.Env.root G.sevm)) ∨
    (G.sevm.code = ImplV2_1.code ∧ PairAllowedFrame selV2_1 pair (WriteSite.Env.root G.sevm)) ∨
    (G.sevm.code = Impl.code ∧ PairAllowedFrame selV2_2 pair (WriteSite.Env.root G.sevm))

/-- **The initializer frames**: a frame running an implementation runtime under one of its
version's initializer selectors (V1 `initialize`; V2 and V2_1 `initialize`, `initializeV2`;
V2_2 `initialize`, `initializeV2`, `initializeV2_2`). V2_1's and V2_2's `initializeV2_1` is
no exception of the law (`selV2_1`, `selV2_2`). -/
def UsdcInitFrame (G : Exec.Deriv) : Prop :=
  (G.sevm.code = ImplV1.code ∧ selV1.selT.eval (WriteSite.Env.root G.sevm) ∈ selV1.inits) ∨
    (G.sevm.code = ImplV2.code ∧ selV2.selT.eval (WriteSite.Env.root G.sevm) ∈ selV2.inits) ∨
    (G.sevm.code = ImplV2_1.code ∧
      selV2_1.selT.eval (WriteSite.Env.root G.sevm) ∈ selV2_1.inits) ∨
    (G.sevm.code = Impl.code ∧ selV2_2.selT.eval (WriteSite.Env.root G.sevm) ∈ selV2_2.inits)

theorem usdcAllowException_split {pair : Adr} {G : Exec.Deriv}
    (h : UsdcAllowException pair G) : UsdcPairException pair G ∨ UsdcInitFrame G := by
  rcases h with ⟨c, a | a | a⟩ | ⟨c, a | a | a⟩ | ⟨c, a | a | a⟩ | ⟨c, a | a | a⟩
  · exact .inl (.inl ⟨c, .inl a⟩)
  · exact .inl (.inl ⟨c, .inr a⟩)
  · exact .inr (.inl ⟨c, a⟩)
  · exact .inl (.inr (.inl ⟨c, .inl a⟩))
  · exact .inl (.inr (.inl ⟨c, .inr a⟩))
  · exact .inr (.inr (.inl ⟨c, a⟩))
  · exact .inl (.inr (.inr (.inl ⟨c, .inl a⟩)))
  · exact .inl (.inr (.inr (.inl ⟨c, .inr a⟩)))
  · exact .inr (.inr (.inr (.inl ⟨c, a⟩)))
  · exact .inl (.inr (.inr (.inr ⟨c, .inl a⟩)))
  · exact .inl (.inr (.inr (.inr ⟨c, .inr a⟩)))
  · exact .inr (.inr (.inr (.inr ⟨c, a⟩)))

/-- **Initializer writes at the Pair's rows (stated, node level).** At every raw node of an
initializer frame at `P`, a successful `SSTORE` at a tracked Pair row does not raise it. The
initializers' writes are fixed slots, literal zero or payload keys of their decoded strings or
arrays; with those keys apart from the tracked rows this is what the prefix walks give at
every node of the frame, whatever its outcome (`ConfiguredHistoryTraceIn.initRowWritesNonInc`
in `InitRowsHistory.lean`, from `InitRowsApart`). -/
def InitRowWritesNonInc (P pair : Adr) (Tr : Adr → Prop) (frames : List Exec.Deriv) : Prop :=
  ∀ G ∈ frames, G.sevm.currentTarget = P → UsdcInitFrame G →
    ∀ m, Exec.Deriv.ParentPrefix G m → ∀ w : Exec.StorageWrite,
      Exec.Deriv.successfulSstore? m = some w → (∃ g, Tr g ∧ allowSlot pair g = w.key) →
        w.value.toNat ≤ ((m.devm.getStor P).get w.key).toNat

/-- **No Pair exception frame above a tracked-row write (stated, node level).** For every
raw node `m` with a successful `SSTORE` in `P`'s storage at a tracked Pair row, no raw frame at
`P` that `m` descends from is a Pair exception frame (`UsdcPairException`). Junk frames that
name the Pair (a reverting `permit(pair, …)`, say) but reach no such write are unconstrained. -/
def NoPairExceptionWrites (P pair : Adr) (Tr : Adr → Prop) (frames nodes : List Exec.Deriv) :
    Prop :=
  ∀ m ∈ nodes, ∀ w : Exec.StorageWrite, Exec.Deriv.successfulSstore? m = some w →
    w.owner = P → (∃ g, Tr g ∧ allowSlot pair g = w.key) →
      ∀ G ∈ frames, Exec.Deriv.ParentPrefix G m → G.sevm.currentTarget = P →
        ¬ UsdcPairException pair G

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {P : Adr} {pair : Adr} {Tr : Adr → Prop}

/-- **Every raw write at a tracked row, attributed and classified.** A successful raw
`SSTORE` at `(P, k)` for a tracked Pair row `k` lies in a raw frame at `P` that is an
exception frame, or the write does not raise the row above its word at the write's node. -/
theorem ConfiguredHistoryTraceIn.usdc_rawRowWrite
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (codes : UsdcNodeCodes P history.rawNodes)
    (proxyApart : ProxyRowsApart P pair Tr history.rawNodes)
    (rowSep : UsdcRowSep P pair Tr history.rawFrames)
    {m : Exec.Deriv} (hm : m ∈ history.rawNodes) {w : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? m = some w) (owner : w.owner = P)
    (tracked : ∃ g, Tr g ∧ allowSlot pair g = w.key) :
    ∃ G ∈ history.rawFrames, Exec.Deriv.ParentPrefix G m ∧ G.sevm.currentTarget = P ∧
      (UsdcAllowException pair G ∨
        w.value.toNat ≤ ((m.devm.getStor P).get w.key).toNat) := by
  have target : m.sevm.currentTarget = P :=
    (successfulSstore?_node_owner found).2.symm.trans owner
  obtain ⟨G, hG, chain⟩ := (history.mem_rawNodes_iff_rawFrame_parentPrefix m).mp hm
  have hsevm := Exec.Deriv.ParentPrefix.sevm_eq chain
  have gTarget : G.sevm.currentTarget = P := by rw [← hsevm]; exact target
  refine ⟨G, hG, chain, gTarget, ?_⟩
  obtain ⟨hpc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities G hG
  have fam := codes m hm target
  rw [hsevm] at fam
  obtain ⟨s1, s2, s21, s22⟩ := rowSep G hG gTarget
  have nonInc : w.value.toNat ≤ (m.devm.getStorVal m.sevm.currentTarget w.key).toNat →
      w.value.toNat ≤ ((m.devm.getStor P).get w.key).toNat := by
    rw [target]; exact id
  rcases fam with h | h | h | h | h | h
  · exact absurd tracked (proxyApart m hm target (by rw [hsevm]; exact h) w found)
  · exact (rawWrite_allowClass hpc hsg chain ImplV1.cert_check implV1_wsCert h (by decide)
      implV1_allowSitesOk (s1 h) found tracked).imp (fun a => .inl ⟨h, a⟩) nonInc
  · exact (rawWrite_allowClass hpc hsg chain ImplV2.cert_check implV2_wsCert h (by decide)
      implV2_allowSitesOk (s2 h) found tracked).imp (fun a => .inr (.inl ⟨h, a⟩)) nonInc
  · exact (rawWrite_allowClass hpc hsg chain ImplV2_1.cert_check implV2_1_wsCert h (by decide)
      implV2_1_allowSitesOk (s21 h) found tracked).imp (fun a => .inr (.inr (.inl ⟨h, a⟩)))
      nonInc
  · exact (rawWrite_allowClass hpc hsg chain Impl.cert_check impl_wsCert h (by decide)
      implV2_2_allowSitesOk (s22 h) found tracked).imp (fun a => .inr (.inr (.inr ⟨h, a⟩)))
      nonInc
  · exact (lib_no_sstore_node hpc hsg chain h found).elim

/-- **A changed row's last word comes from an attributed raw write.** If `P`'s cell `k`
differs between checkpoint and future, some raw node wrote the future word there, in a raw
frame at `P`. -/
theorem ConfiguredHistoryTraceIn.usdc_rowChange_attributed
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (proxy : checkpoint.state.getCode P = Proxy.code) (codes : UsdcNodeCodes P history.rawNodes)
    (k : B256)
    (changed : (future.state.getStor P).get k ≠ (checkpoint.state.getStor P).get k) :
    ∃ (b₁ b₂ : List Exec.Deriv) (m G : Exec.Deriv) (w : Exec.StorageWrite),
      history.rawNodes = b₁ ++ m :: b₂ ∧ G ∈ history.rawFrames ∧
      Exec.Deriv.ParentPrefix G m ∧ G.sevm.currentTarget = P ∧
      Exec.Deriv.successfulSstore? m = some w ∧ w.owner = P ∧ w.key = k ∧
      w.value = (future.state.getStor P).get k := by
  have proxyFam : UsdcContextCode Proxy.code := Or.inl rfl
  have safe := usdc_safeRawFrames history capabilities (codes.frames history)
  obtain ⟨cell, -⟩ := history.cellProv_post proxyFam.not_delegation proxyFam.ne_nil
    capabilities k proxy safe
  rcases cell with same | ⟨b₁, b₂, m, w, split, found, owner, key, value⟩
  · exact absurd same changed
  · have hm : m ∈ history.rawNodes := by rw [split]; exact List.mem_append_right _ List.mem_cons_self
    obtain ⟨G, hG, chain⟩ := (history.mem_rawNodes_iff_rawFrame_parentPrefix m).mp hm
    have target : m.sevm.currentTarget = P :=
      (successfulSstore?_node_owner found).2.symm.trans owner
    refine ⟨b₁, b₂, m, G, w, split, hG, chain, ?_, found, owner, key, value⟩
    rw [← Exec.Deriv.ParentPrefix.sevm_eq chain]; exact target

/-- **P1 over the actual history.** With no Pair exception frame at `P` above a write at a
tracked row (`NoPairExceptionWrites`) and the initializers' writes at the tracked rows
non-increasing (`InitRowWritesNonInc`), every tracked allowance row of the Pair is at most its
checkpoint word at every raw node of the history and at the future. -/
theorem ConfiguredHistoryTraceIn.usdc_pairAllowance_noIncrease
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (proxy : checkpoint.state.getCode P = Proxy.code) (codes : UsdcNodeCodes P history.rawNodes)
    (proxyApart : ProxyRowsApart P pair Tr history.rawNodes)
    (rowSep : UsdcRowSep P pair Tr history.rawFrames)
    (noPairException : NoPairExceptionWrites P pair Tr history.rawFrames history.rawNodes)
    (initRows : InitRowWritesNonInc P pair Tr history.rawFrames)
    {k : B256} (tracked : ∃ g, Tr g ∧ allowSlot pair g = k) :
    (∀ n ∈ history.rawNodes,
        ((n.devm.getStor P).get k).toNat ≤ ((checkpoint.state.getStor P).get k).toNat) ∧
      ((future.state.getStor P).get k).toNat ≤ ((checkpoint.state.getStor P).get k).toNat := by
  have proxyFam : UsdcContextCode Proxy.code := Or.inl rfl
  -- a write at the row does not exceed the row at its node
  have writeLe : ∀ m ∈ history.rawNodes, ∀ w : Exec.StorageWrite,
      Exec.Deriv.successfulSstore? m = some w → w.owner = P → w.key = k →
      w.value.toNat ≤ ((m.devm.getStor P).get k).toNat := by
    intro m hm w found owner key
    obtain ⟨G, hG, chain, gTarget, cls⟩ := ConfiguredHistoryTraceIn.usdc_rawRowWrite history
      capabilities codes proxyApart rowSep hm found owner (key ▸ tracked)
    rw [← key]
    rcases cls with exc | le
    · rcases usdcAllowException_split exc with pairExc | init
      · exact (noPairException m hm w found owner (key ▸ tracked) G hG chain gTarget
          pairExc).elim
      · exact initRows G hG gTarget init m chain w found (key ▸ tracked)
    · exact le
  have nodes : ∀ n ∈ history.rawNodes,
      ((n.devm.getStor P).get k).toNat ≤ ((checkpoint.state.getStor P).get k).toNat := by
    refine List.forall_mem_of_positional fun before n after split ih => ?_
    have sub : ∀ m ∈ before, m ∈ history.rawNodes := fun m hm => by
      rw [split]; exact List.mem_append_left _ hm
    exact history.rawNode_cellInv capabilities proxyFam.not_delegation proxyFam.ne_nil proxy
      (Inv := fun v => v.toNat ≤ ((checkpoint.state.getStor P).get k).toNat) (Nat.le_refl _) split
      (fun m hm => codes.safe history capabilities m (sub m hm))
      (fun m hm w found owner key =>
        (writeLe m (sub m hm) w found owner key).trans (ih m hm))
  refine ⟨nodes, ?_⟩
  have safe := usdc_safeRawFrames history capabilities (codes.frames history)
  obtain ⟨cell, -⟩ := history.cellProv_post proxyFam.not_delegation proxyFam.ne_nil
    capabilities k proxy safe
  rcases cell with same | ⟨b₁, b₂, m, w, split, found, owner, key, value⟩
  · rw [same]
  · have hm : m ∈ history.rawNodes := by rw [split]; exact List.mem_append_right _ List.mem_cons_self
    rw [← value]
    exact (writeLe m hm w found owner key).trans (nodes m hm)

end History

end Blanc.Lift.Usdc
