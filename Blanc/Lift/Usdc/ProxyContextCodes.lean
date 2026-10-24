import Blanc.ExecutionInRawNodeOrigin
import Blanc.ExecutionHistoryCellProvenance
import Blanc.Lift.Usdc.ProxyReachH
import Blanc.Lift.Usdc.ProxySafeFrames
import Blanc.Lift.Usdc.HistoryFamilyProxy

/-!
# The codes that run in the USDC proxy's storage context, along an In-history

`usdc_safeRawFrames` and `rawFrame_proxyCode` (`ProxySafeFrames.lean`) take
`codes`: every raw frame in the proxy `P`'s storage context runs one of the six
USDC codes (`UsdcContextCode`). This module proves that premise
(`ConfiguredHistoryTraceIn.usdc_contextCodes`) by strong induction on the
position of a node in the history's raw chronology (`rawNodes`), and restates the
two consumers without it (`usdc_safeRawFrames_of_world`,
`rawFrame_proxyCode_of_world`).

The world (`UsdcContextWorld P W s`): `P` holds the proxy runtime; `W` lists
implementation and library accounts with their runtimes (`UsdcImplCode`), none
of them `P`; whenever `W` lists a V2_2 runtime it also lists the library at
`usdcLib`; and `P`'s implementation slot names an account of `W`. All of this is
required at the checkpoint (an account deployed after the checkpoint is outside
this statement).

The two history premises about the implementation slot:

* `UpgradesWithin P W nodes`: every successful `SSTORE` that the proxy runtime
  itself executes at `(P, implSlot)` stores a word naming an account of `W`.
  Which values the admin installs through `upgradeTo`/`upgradeToAndCall` is not
  a code fact; this premise states it at the proxy's own write.
* `ImplSlotApart P nodes`: no implementation or library frame in `P`'s context
  executes a successful `SSTORE` at `(P, implSlot)` (a frame-local key
  separation: their write sites are solc storage slots, constant or hashed).

At a node `n` (`CtxOK P W n`): a frame in `P`'s context runs the proxy runtime
or a runtime of `W`, and a frame in the context of an account of `W` runs a
runtime of `W`. Each node is reached (`ConfiguredHistoryTraceIn.rawNodes_origin`)
as a message root running its target's code, the code at `P` or at an account of
`W` (`rawNode_cellProvenance` with safety of the earlier nodes, which the
induction hypothesis gives through the certificates), as a successor of an
earlier node of its frame, or as a child of an earlier node `m`. A child at
another target runs the callee's installed code; a child in `m`'s own context
is a `CALL`/`STATICCALL` back into it, or a `DELEGATECALL`: from the proxy
runtime its address operand is `P`'s implementation word (`proxy_nodeH`), which
names an account of `W` (`rawNode_cellInv` with the two premises), and from the
V2_2 runtime it is `usdcLib` (`implExecKindH`). The other four runtimes decode
only `CALL`/`STATICCALL` (`*.cert_callOnly`).
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-! ## Code facts -/

theorem ImplV1.cert_callOnly : ImplV1.cert.callOnly = true := by decide +kernel
theorem ImplV2.cert_callOnly : ImplV2.cert.callOnly = true := by decide +kernel
theorem ImplV2_1.cert_callOnly : ImplV2_1.cert.callOnly = true := by decide +kernel
theorem Lib.cert_callOnly : Lib.cert.callOnly = true := by decide +kernel

theorem ImplV1.code_not_delegation : ¬ isValidDelegation ImplV1.code := by decide +kernel
theorem ImplV2.code_not_delegation : ¬ isValidDelegation ImplV2.code := by decide +kernel
theorem ImplV2_1.code_not_delegation : ¬ isValidDelegation ImplV2_1.code := by decide +kernel
theorem Impl.code_not_delegation : ¬ isValidDelegation Impl.code := by decide +kernel
theorem Lib.code_not_delegation : ¬ isValidDelegation Lib.code := by decide +kernel

theorem ImplV1.code_size_pos : 0 < ImplV1.code.size := by decide +kernel
theorem ImplV2.code_size_pos : 0 < ImplV2.code.size := by decide +kernel
theorem ImplV2_1.code_size_pos : 0 < ImplV2_1.code.size := by decide +kernel
theorem Impl.code_size_pos : 0 < Impl.code.size := by decide +kernel
theorem Lib.code_size_pos : 0 < Lib.code.size := by decide +kernel
theorem Proxy.code_size_pos : 0 < Proxy.code.size := by decide +kernel

theorem proxy_ne_implV1 : Proxy.code ≠ ImplV1.code := fun h =>
  absurd (congrArg ByteArray.size h) (by decide +kernel)
theorem proxy_ne_implV2 : Proxy.code ≠ ImplV2.code := fun h =>
  absurd (congrArg ByteArray.size h) (by decide +kernel)
theorem proxy_ne_implV2_1 : Proxy.code ≠ ImplV2_1.code := fun h =>
  absurd (congrArg ByteArray.size h) (by decide +kernel)

/-- The implementation and library runtimes. -/
def UsdcImplCode (C : ByteArray) : Prop :=
  C = ImplV1.code ∨ C = ImplV2.code ∨ C = ImplV2_1.code ∨ C = Impl.code ∨ C = Lib.code

theorem UsdcImplCode.context {C : ByteArray} (h : UsdcImplCode C) : UsdcContextCode C :=
  Or.inr h

theorem UsdcImplCode.ne_proxy {C : ByteArray} (h : UsdcImplCode C) : C ≠ Proxy.code := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact fun e => proxy_ne_implV1 e.symm
  · exact fun e => proxy_ne_implV2 e.symm
  · exact fun e => proxy_ne_implV2_1 e.symm
  · exact fun e => proxy_ne_impl e.symm
  · exact lib_ne_proxy

private theorem toList_ne_nil_of_size {c : ByteArray} (h : 0 < c.size) : c.toList ≠ [] :=
  List.ne_nil_of_length_pos (ByteArray.size_eq_length_toList c ▸ h)

theorem UsdcContextCode.ne_nil {C : ByteArray} (h : UsdcContextCode C) : C.toList ≠ [] := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact toList_ne_nil_of_size Proxy.code_size_pos
  · exact toList_ne_nil_of_size ImplV1.code_size_pos
  · exact toList_ne_nil_of_size ImplV2.code_size_pos
  · exact toList_ne_nil_of_size ImplV2_1.code_size_pos
  · exact toList_ne_nil_of_size Impl.code_size_pos
  · exact toList_ne_nil_of_size Lib.code_size_pos

theorem UsdcContextCode.not_delegation {C : ByteArray} (h : UsdcContextCode C) :
    ¬ isValidDelegation C := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Proxy.code_not_delegation
  · exact ImplV1.code_not_delegation
  · exact ImplV2.code_not_delegation
  · exact ImplV2_1.code_not_delegation
  · exact Impl.code_not_delegation
  · exact Lib.code_not_delegation

theorem UsdcContextCode.ne_empty {C : ByteArray} (h : UsdcContextCode C) : C ≠ .empty := by
  rintro rfl
  exact h.ne_nil ByteArray.toList_empty

/-- `impl_exec_kind` without a covered fork: a V2_2 node decodes `CALL`, or
`DELEGATECALL` whose address operand is the library's. -/
theorem implExecKindH {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (codeEq : sevm.code = Impl.code) (hsg : sevm.benvStat.rules.stateGas = none)
    {N : Exec.Deriv} (chain : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N) {x : Xinst}
    (hat : Ninst.At N.sevm.code N.pc (.exec x)) :
    x = .call ∨ (x = .delegatecall ∧ ∀ (g a : B256) (rest : List B256),
      N.devm.stack = g :: a :: rest → a = usdcLib.toB256) := by
  obtain ⟨κ, reach, ok⟩ := cursor_of_parentPrefix_noStateGas certL_check
    (F := ⟨0, sevm, pre, out, run⟩) rfl codeEq hsg chain
  have kind := ok.execsSatisfy (Cursor.execsSatisfy_of_reachable impl_kinds reach) hat
  have hP := ok.framesSat_exec
    (Cursor.framesSat_of_reachable certL_framesSat certL_framesSat_head reach) hat
  cases x with
  | call => exact .inl rfl
  | delegatecall =>
      simp only [implP, beq_iff_eq] at hP
      refine .inr ⟨rfl, fun g a rest hs => ?_⟩
      have hw := ok.stack_const hP
      rw [hs] at hw
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hw
      exact hw
  | _ => simp only [implKinds, reduceCtorEq, beq_iff_eq, Bool.or_eq_true, or_self] at kind

/-- **What a node of a USDC frame spawns by.** At a node `m` of a frame `G` running a
USDC code from pc `0` without state gas, a decoded external instruction is `CALL`,
`STATICCALL`, or `DELEGATECALL` whose address operand is the frame target's
implementation word (proxy runtime) or `usdcLib` (V2_2 runtime). -/
theorem usdc_exec_kind {G m : Exec.Deriv} (hpc : G.pc = 0)
    (hsg : G.sevm.benvStat.rules.stateGas = none) (bal : G.sevm.benvStat.rules.bal = none)
    (chain : Exec.Deriv.ParentPrefix G m) (hfam : UsdcContextCode G.sevm.code) {x : Xinst}
    (hat : Ninst.At m.sevm.code m.pc (.exec x)) :
    x = .call ∨ x = .staticcall ∨
      (x = .delegatecall ∧
        ((G.sevm.code = Proxy.code ∧ ∀ (g w : B256) (rest : List B256),
            m.devm.stack = g :: w :: rest →
              w = m.devm.getStorVal G.sevm.currentTarget implSlot) ∨
          (G.sevm.code = Impl.code ∧ ∀ (g w : B256) (rest : List B256),
            m.devm.stack = g :: w :: rest → w = usdcLib.toB256))) := by
  rcases G with ⟨pc, sevm, pre, out, run⟩
  dsimp only at hpc hsg bal hfam ⊢
  subst hpc
  have callOnly : ∀ {C : ByteArray} {c : Cert}, Cert.check C c = true → c.callOnly = true →
      sevm.code = C → x = .call ∨ x = .staticcall := fun hc hco hcode =>
    call_or_staticcall_of_parentPrefix_noStateGas hc hco (F := ⟨0, sevm, pre, out, run⟩)
      rfl hcode hsg chain hat
  rcases hfam with h | h | h | h | h | h
  · obtain ⟨f, K, ⟨rfl, hd⟩ | ⟨rfl, -⟩⟩ := Proxy.proxy_nodeH run h hsg bal chain hat
    · refine .inr (.inr ⟨rfl, .inl ⟨h, fun g w rest hs => ?_⟩⟩)
      obtain ⟨-, b', g', S, M, G', rest', hb, -, hdev⟩ := hd
      have hstack := congrArg Devm.stack hdev
      simp only [St.stack] at hstack
      rw [hs] at hstack
      simp only [List.cons.injEq] at hstack
      rw [hstack.2.1]
      show _ = Devm.getStorVal m.devm _ _
      have hstate : m.devm.state = pre.state := by
        show m.devm.state = _
        have := congrArg Devm.state hdev
        exact this.trans hb
      exact (Proxy.getStorVal_of_state hstate _ _).symm
    · exact .inl rfl
  · exact (callOnly ImplV1.cert_check ImplV1.cert_callOnly h).imp id .inl
  · exact (callOnly ImplV2.cert_check ImplV2.cert_callOnly h).imp id .inl
  · exact (callOnly ImplV2_1.cert_check ImplV2_1.cert_callOnly h).imp id .inl
  · rcases implExecKindH run h hsg chain hat with rfl | ⟨rfl, hw⟩
    · exact .inl rfl
    · exact .inr (.inr ⟨rfl, .inr ⟨h, hw⟩⟩)
  · exact (callOnly Lib.cert_check Lib.cert_callOnly h).imp id .inl

/-! ## The world and the premises -/

/-- The accounts whose code may run in the proxy's storage context, at a state `s`: the
proxy runtime at `P`, implementation and library runtimes at the accounts of `W`
(none of them `P`), the library at `usdcLib` whenever a V2_2 runtime is listed, and
`P`'s implementation slot naming an account of `W`. -/
structure UsdcContextWorld (P : Adr) (W : List (Adr × ByteArray)) (s : State) : Prop where
  proxy : s.getCode P = Proxy.code
  impls : ∀ e ∈ W, UsdcImplCode e.2 ∧ s.getCode e.1 = e.2
  apart : ∀ e ∈ W, e.1 ≠ P
  lib : ∀ e ∈ W, e.2 = Impl.code → (usdcLib, Lib.code) ∈ W
  slot : ∃ e ∈ W, ((s.getStor P).get implSlot).toAdr = e.1

/-- **The admin's upgrades (stated).** Every successful `SSTORE` the proxy runtime itself
executes at `(P, implSlot)` among `nodes` stores a word naming an account of `W`. -/
def UpgradesWithin (P : Adr) (W : List (Adr × ByteArray)) (nodes : List Exec.Deriv) : Prop :=
  ∀ m ∈ nodes, m.sevm.currentTarget = P → m.sevm.code = Proxy.code →
    ∀ w : Exec.StorageWrite, Exec.Deriv.successfulSstore? m = some w → w.key = implSlot →
      ∃ e ∈ W, w.value.toAdr = e.1

/-- **Implementation-slot apartness (stated).** No frame in `P`'s context running a code
other than the proxy runtime executes a successful `SSTORE` at `(P, implSlot)` among
`nodes`. -/
def ImplSlotApart (P : Adr) (nodes : List Exec.Deriv) : Prop :=
  ∀ m ∈ nodes, m.sevm.currentTarget = P → m.sevm.code ≠ Proxy.code →
    ∀ w : Exec.StorageWrite, Exec.Deriv.successfulSstore? m = some w → w.key ≠ implSlot

/-- The node invariant: a frame in `P`'s context runs the proxy runtime or a runtime of
`W`; a frame in the context of an account of `W` runs a runtime of `W`. -/
def CtxOK (P : Adr) (W : List (Adr × ByteArray)) (n : Exec.Deriv) : Prop :=
  (n.sevm.currentTarget = P → n.sevm.code = Proxy.code ∨ ∃ e ∈ W, n.sevm.code = e.2) ∧
    ∀ e ∈ W, n.sevm.currentTarget = e.1 → ∃ e' ∈ W, n.sevm.code = e'.2

theorem CtxOK.of_sevm {P : Adr} {W : List (Adr × ByteArray)} {m n : Exec.Deriv}
    (h : CtxOK P W m) (he : m.sevm = n.sevm) : CtxOK P W n := by
  unfold CtxOK at h ⊢
  rw [← he]
  exact h

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {P : Adr} {W : List (Adr × ByteArray)}

/-- A node of a listed context runs a USDC code. -/
theorem CtxOK.context (world : UsdcContextWorld P W checkpoint.state) {n : Exec.Deriv}
    (h : CtxOK P W n) {a : Adr} (ha : a = P ∨ ∃ e ∈ W, a = e.1)
    (target : n.sevm.currentTarget = a) : UsdcContextCode n.sevm.code := by
  rcases ha with rfl | ⟨e, he, rfl⟩
  · rcases h.1 target with hc | ⟨e, he, hc⟩
    · exact Or.inl hc
    · rw [hc]; exact (world.impls e he).1.context
  · obtain ⟨e', he', hc⟩ := h.2 e he target
    rw [hc]; exact (world.impls e' he').1.context

/-- Earlier nodes satisfying the invariant are safe at every listed account. -/
theorem safe_of_ctxOK (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (world : UsdcContextWorld P W checkpoint.state)
    {pre : List Exec.Deriv} (sub : ∀ m ∈ pre, m ∈ history.rawNodes)
    (ok : ∀ m ∈ pre, CtxOK P W m) {a : Adr} (ha : a = P ∨ ∃ e ∈ W, a = e.1) :
    ∀ m ∈ pre, m.sevm.currentTarget = a → ¬ Linst.At m.sevm.code m.pc .selfdestruct := by
  intro m hm target
  obtain ⟨G, hG, chain⟩ := (history.mem_rawNodes_iff_rawFrame_parentPrefix m).mp (sub m hm)
  have hsevm := Exec.Deriv.ParentPrefix.sevm_eq chain
  have facts := history.rawFrame_entryFacts capabilities G hG
  have fam := (ok m hm).context world ha target
  rw [hsevm] at fam
  obtain ⟨c, hc, noSD⟩ := usdcContextCode_certified _ fam
  exact Lift.not_selfdestruct_of_parentPrefix_noStateGas hc noSD facts.1 rfl facts.2.2.1 chain

/-- At a node whose earlier nodes satisfy the invariant, `P` and the accounts of `W` hold
their checkpoint runtimes, and `P`'s implementation word names an account of `W`. -/
theorem world_at (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (world : UsdcContextWorld P W checkpoint.state)
    (upgrades : UpgradesWithin P W history.rawNodes) (apartSlot : ImplSlotApart P history.rawNodes)
    {pre post : List Exec.Deriv} {x : Exec.Deriv} (split : history.rawNodes = pre ++ x :: post)
    (ok : ∀ m ∈ pre, CtxOK P W m) :
    x.devm.getCode P = Proxy.code ∧ (∀ e ∈ W, x.devm.getCode e.1 = e.2) ∧
      ∃ e ∈ W, ((x.devm.getStor P).get implSlot).toAdr = e.1 := by
  have sub : ∀ m ∈ pre, m ∈ history.rawNodes := fun m hm => by
    rw [split]; exact List.mem_append_left _ hm
  have proxyFam : UsdcContextCode Proxy.code := Or.inl rfl
  refine ⟨(history.rawNode_cellProvenance capabilities proxyFam.not_delegation proxyFam.ne_nil
      world.proxy 0 split (safe_of_ctxOK history capabilities world sub ok (.inl rfl))).1,
    fun e he => ?_, ?_⟩
  · have fam := (world.impls e he).1.context
    exact (history.rawNode_cellProvenance capabilities fam.not_delegation fam.ne_nil
      (world.impls e he).2 0 split
      (safe_of_ctxOK history capabilities world sub ok (.inr ⟨e, he, rfl⟩))).1
  · refine history.rawNode_cellInv capabilities proxyFam.not_delegation proxyFam.ne_nil
      world.proxy (Inv := fun v => ∃ e ∈ W, v.toAdr = e.1) world.slot split
      (safe_of_ctxOK history capabilities world sub ok (.inl rfl)) ?_
    intro m hm w found owner key
    have target : m.sevm.currentTarget = P :=
      ((successfulSstore?_node_owner found).2.symm.trans owner)
    by_cases hcode : m.sevm.code = Proxy.code
    · exact upgrades m (sub m hm) target hcode w found key
    · exact absurd key (apartSlot m (sub m hm) target hcode w found)

/-- The codes a frame in context `a` may run. -/
def Allowed (P : Adr) (W : List (Adr × ByteArray)) (a : Adr) (C : ByteArray) : Prop :=
  (a = P → C = Proxy.code ∨ ∃ e ∈ W, C = e.2) ∧ (a ≠ P → ∃ e ∈ W, C = e.2)

theorem allowed_of_mem {a : Adr} {e : Adr × ByteArray} (he : e ∈ W) : Allowed P W a e.2 :=
  ⟨fun _ => .inr ⟨e, he, rfl⟩, fun _ => ⟨e, he, rfl⟩⟩

theorem allowed_installed (world : UsdcContextWorld P W checkpoint.state) {d : Devm}
    (hP : d.getCode P = Proxy.code) (hW : ∀ e ∈ W, d.getCode e.1 = e.2) {a : Adr}
    (ha : a = P ∨ ∃ e ∈ W, a = e.1) : Allowed P W a (d.getCode a) := by
  rcases ha with rfl | ⟨e, he, rfl⟩
  · exact ⟨fun _ => .inl hP, fun h => (h rfl).elim⟩
  · rw [hW e he]; exact allowed_of_mem he

theorem allowed_installed_context (world : UsdcContextWorld P W checkpoint.state) {d : Devm}
    (hP : d.getCode P = Proxy.code) (hW : ∀ e ∈ W, d.getCode e.1 = e.2) {a : Adr}
    (ha : a = P ∨ ∃ e ∈ W, a = e.1) : UsdcContextCode (d.getCode a) := by
  rcases ha with rfl | ⟨e, he, rfl⟩
  · rw [hP]; exact Or.inl rfl
  · rw [hW e he]; exact (world.impls e he).1.context

theorem CtxOK.allowed (world : UsdcContextWorld P W checkpoint.state) {m : Exec.Deriv}
    (h : CtxOK P W m) {a : Adr} (ha : a = P ∨ ∃ e ∈ W, a = e.1)
    (target : m.sevm.currentTarget = a) : Allowed P W a m.sevm.code := by
  rcases ha with rfl | ⟨e, he, rfl⟩
  · exact ⟨fun _ => h.1 target, fun h' => (h' rfl).elim⟩
  · obtain ⟨e', he', hc⟩ := h.2 e he target
    exact ⟨fun h' => .inr ⟨e', he', hc⟩, fun _ => ⟨e', he', hc⟩⟩

/-- A node running the proxy runtime in a listed context is at `P`; one running another
code runs a runtime of `W`. -/
theorem CtxOK.code_cases (world : UsdcContextWorld P W checkpoint.state) {m : Exec.Deriv}
    (h : CtxOK P W m) {a : Adr} (ha : a = P ∨ ∃ e ∈ W, a = e.1)
    (target : m.sevm.currentTarget = a) :
    (m.sevm.code = Proxy.code ∧ a = P) ∨ ∃ e ∈ W, m.sevm.code = e.2 := by
  rcases ha with rfl | ⟨e, he, rfl⟩
  · rcases h.1 target with hc | hc
    · exact .inl ⟨hc, rfl⟩
    · exact .inr hc
  · exact .inr (h.2 e he target)

theorem CtxOK.of_allowed (world : UsdcContextWorld P W checkpoint.state) {n : Exec.Deriv}
    (h : ∀ a, (a = P ∨ ∃ e ∈ W, a = e.1) → n.sevm.currentTarget = a →
      Allowed P W a n.sevm.code) : CtxOK P W n :=
  ⟨fun target => (h P (.inl rfl) target).1 rfl, fun e he target =>
    (h e.1 (.inr ⟨e, he, rfl⟩) target).2 (world.apart e he)⟩

/-- One induction step: the invariant at `n` from the invariant at every earlier node. -/
theorem ctxOK_step (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    (world : UsdcContextWorld P W checkpoint.state)
    (upgrades : UpgradesWithin P W history.rawNodes) (apartSlot : ImplSlotApart P history.rawNodes)
    {before after : List Exec.Deriv} {n : Exec.Deriv}
    (split : history.rawNodes = before ++ n :: after) (ok : ∀ m ∈ before, CtxOK P W m) :
    CtxOK P W n := by
  refine CtxOK.of_allowed world fun a ha target => ?_
  rcases history.rawNodes_origin before n after split with root | ⟨m, hm, he⟩ | ⟨m, hm, hspawn⟩
  · -- a message root runs the code installed at its target
    obtain ⟨hP, hW, -⟩ := world_at history capabilities world upgrades apartSlot split ok
    have fam := allowed_installed_context world hP hW ha
    rw [root a target fam.ne_nil fam.not_delegation]
    exact allowed_installed world hP hW ha
  · -- a successor of an earlier node of its frame
    rw [← he] at target ⊢
    exact (ok m hm).allowed world ha target
  · -- the root of a frame an earlier node spawned
    obtain ⟨b₁, b₂, hb⟩ := List.append_of_mem hm
    have split' : history.rawNodes = b₁ ++ m :: (b₂ ++ n :: after) := by
      rw [split, hb]; simp only [List.append_assoc, List.cons_append]
    have ok' : ∀ m' ∈ b₁, CtxOK P W m' := fun m' hm' => ok m' (by
      rw [hb]; exact List.mem_append_left _ hm')
    obtain ⟨hP, hW, hslot⟩ := world_at history capabilities world upgrades apartSlot split' ok'
    obtain ⟨f, rsm, pc', cevm, hs, henter, -, hsta, -⟩ := hspawn
    have childTarget : n.sevm.currentTarget = f.inner.currentTarget := by
      rw [← hsta]; exact Frame.enter_run_currentTarget henter
    have childCode : n.sevm.code = f.inner.code := by
      rw [← hsta]; exact Frame.enter_run_code henter
    have famA := allowed_installed_context world hP hW ha
    by_cases hsame : m.sevm.currentTarget = a
    · obtain ⟨x, hat, hx, -⟩ := Evm.step_spawn_inv hs
      have mMem : m ∈ history.rawNodes := by rw [split]; exact List.mem_append_left _ hm
      obtain ⟨G, hG, chain⟩ := (history.mem_rawNodes_iff_rawFrame_parentPrefix m).mp mMem
      have hsevm := Exec.Deriv.ParentPrefix.sevm_eq chain
      have facts := history.rawFrame_entryFacts capabilities G hG
      have fam := (ok m hm).context world ha hsame
      rw [hsevm] at fam
      rcases usdc_exec_kind facts.1 facts.2.2.1 (bal facts.2.1) chain fam hat with
        hcall | hcall | ⟨rfl, hdel⟩
      · rw [childCode, Xinst.step_directCall_spawn_code (.inl hcall) hx
          (by rw [← childTarget, target]; exact famA.not_delegation),
          ← childTarget, target]
        exact allowed_installed world hP hW ha
      · rw [childCode, Xinst.step_directCall_spawn_code (.inr hcall) hx
          (by rw [← childTarget, target]; exact famA.not_delegation),
          ← childTarget, target]
        exact allowed_installed world hP hW ha
      · obtain ⟨g, w, rest, hstack⟩ := Xinst.step_delegatecall_spawn_stack hx
        have cases := (ok m hm).code_cases world ha hsame
        rw [hsevm] at cases
        rcases hdel with ⟨hproxy, hw⟩ | ⟨himpl, hw⟩
        · -- the proxy forwards to the account its implementation word names
          have hwP : w = m.devm.getStorVal P implSlot := by
            rw [hw g w rest hstack, ← hsevm, hsame]
            rcases cases with ⟨-, rfl⟩ | ⟨e, he, hc⟩
            · rfl
            · exact absurd (hc.symm.trans hproxy) (world.impls e he).1.ne_proxy
          obtain ⟨e, he, hname⟩ := hslot
          have hcodeE : m.devm.getCode w.toAdr = e.2 := by
            rw [hwP]; exact (hname ▸ hW e he :)
          rw [childCode, Xinst.step_delegatecall_spawn_code hx hstack
            (by rw [hcodeE]; exact (world.impls e he).1.context.not_delegation), hcodeE]
          exact allowed_of_mem he
        · -- the V2_2 runtime forwards to the library
          have libMem : (usdcLib, Lib.code) ∈ W := by
            rcases cases with ⟨hc, -⟩ | ⟨e, he, hc⟩
            · exact absurd (hc.symm.trans himpl) proxy_ne_impl
            · exact world.lib e he (hc.symm.trans himpl)
          have hcodeL : m.devm.getCode w.toAdr = Lib.code := by
            rw [hw g w rest hstack, toAdr_toB256]; exact hW _ libMem
          rw [childCode, Xinst.step_delegatecall_spawn_code hx hstack
            (by rw [hcodeL]; exact Lib.code_not_delegation), hcodeL]
          exact allowed_of_mem libMem
    · -- a child at another target runs the callee's installed code
      have hcode := (Evm.step_spawn_child hs henter).2.2
        (by rw [hsta, target]; exact hsame)
        (by rw [hsta, target]; exact famA.ne_empty)
        (by rw [hsta, target]; exact famA.not_delegation)
      rw [hsta, target] at hcode
      rw [hcode]
      exact allowed_installed world hP hW ha

/-- **The codes run in the proxy's storage context**, at every raw node of the history. -/
theorem ConfiguredHistoryTraceIn.usdc_ctxOK
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    (world : UsdcContextWorld P W checkpoint.state)
    (upgrades : UpgradesWithin P W history.rawNodes) (apartSlot : ImplSlotApart P history.rawNodes) :
    ∀ n ∈ history.rawNodes, CtxOK P W n := by
  suffices h : ∀ k before n after, history.rawNodes = before ++ n :: after →
      before.length = k → CtxOK P W n by
    intro n hn
    obtain ⟨before, after, split⟩ := List.append_of_mem hn
    exact h _ before n after split rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro before n after split hlen
    refine ctxOK_step history capabilities bal world upgrades apartSlot split fun m hm => ?_
    obtain ⟨b₁, b₂, hb⟩ := List.append_of_mem hm
    refine ih b₁.length ?_ b₁ m (b₂ ++ n :: after) ?_ rfl
    · rw [← hlen, hb]; simp only [List.length_append, List.length_cons]; omega
    · rw [split, hb]; simp only [List.append_assoc, List.cons_append]

/-- **`codes` discharged.** Every raw frame in the proxy's storage context runs a USDC
code. -/
theorem ConfiguredHistoryTraceIn.usdc_contextCodes
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    (world : UsdcContextWorld P W checkpoint.state)
    (upgrades : UpgradesWithin P W history.rawNodes) (apartSlot : ImplSlotApart P history.rawNodes) :
    ∀ G ∈ history.rawFrames, G.sevm.currentTarget = P → UsdcContextCode G.sevm.code := by
  intro G hG target
  have hmem : G ∈ history.rawNodes := by
    refine history.rawNodes_of_mem_rawFrames G hG G ?_
    rcases G with ⟨pc, sevm, pre, out, run⟩
    exact Exec.mem_rawNodes_self run
  exact (ConfiguredHistoryTraceIn.usdc_ctxOK history capabilities bal world upgrades apartSlot G hmem).context world
    (.inl rfl) target

/-- **Raw safety at the proxy** from the world and the two implementation-slot premises. -/
theorem usdc_safeRawFrames_of_world (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    (world : UsdcContextWorld P W checkpoint.state)
    (upgrades : UpgradesWithin P W history.rawNodes) (apartSlot : ImplSlotApart P history.rawNodes) :
    SafeRawFrames P history.rawFrames :=
  usdc_safeRawFrames history capabilities
    (ConfiguredHistoryTraceIn.usdc_contextCodes history capabilities bal world upgrades apartSlot)

/-- **The proxy runtime at every raw frame** from the world and the two
implementation-slot premises. -/
theorem rawFrame_proxyCode_of_world (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    (world : UsdcContextWorld P W checkpoint.state)
    (upgrades : UpgradesWithin P W history.rawNodes) (apartSlot : ImplSlotApart P history.rawNodes) :
    ∀ R ∈ history.rawFrames, R.devm.getCode P = Proxy.code :=
  rawFrame_proxyCode history capabilities world.proxy
    (ConfiguredHistoryTraceIn.usdc_contextCodes history capabilities bal world upgrades apartSlot)

end History

end Blanc.Lift.Usdc
