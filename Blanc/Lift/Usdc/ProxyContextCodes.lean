import Blanc.ExecutionInRawNodeOriginFrom
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

The world (`UsdcDeployedWorld history.BoundaryAt P W checkpoint.state`): `P`
holds the proxy runtime at the checkpoint; each entry of `W` is an
implementation or library account with its runtime (`UsdcImplCode`), none of
them `P`, and a committed boundary of the history after its deployment
(`BoundaryAt e.base e.pre`) with the runtime installed there (stated). An entry
is active at a raw position once the position's prefix extends `e.pre`
(`UsdcDeployedEntry.Active`). Whenever `W` lists a V2_2 runtime it also lists
the library at `usdcLib`, active no later; and `P`'s implementation slot at the
checkpoint names an entry active from the checkpoint.

The two history premises about the implementation slot:

* `UpgradesWithinFrom P W nodes`: every successful `SSTORE` that the proxy
  runtime itself executes at `(P, implSlot)` stores a word naming an entry of
  `W` active at that write. Which values the admin installs through
  `upgradeTo`/`upgradeToAndCall` is not a code fact; this premise states it at
  the proxy's own write.
* `ImplSlotApart P nodes`: no implementation or library frame in `P`'s context
  executes a successful `SSTORE` at `(P, implSlot)` (a frame-local key
  separation: their write sites are solc storage slots, constant or hashed).

At a node `n` after the raw prefix `before` (`CtxAt P W before n`): a frame in
`P`'s context runs the proxy runtime or the runtime of an entry active at
`before`, and a frame in the context of an entry active at `before` runs the
runtime of an entry active there. The proof is a strong induction on positions
(`List.forall_split_of_positional`). For a context listed from a boundary
(the checkpoint for `P`, `e.pre` for an entry `e`), the node is reached from
nodes after that boundary (`ConfiguredHistoryTraceIn.BoundaryAt.rawOrigin`): as
a message root running its target's code (`rawNode_cellProvenance_from` at that
boundary, with safety of the nodes between, which the induction hypothesis gives
through the certificates), as a successor of an earlier node of its frame, or
as a child of an earlier node `m`. A child at another target runs the callee's
installed code; a child in `m`'s own context is a `CALL`/`STATICCALL` back into
it, or a `DELEGATECALL`: from the proxy runtime its address operand is `P`'s
implementation word (`proxy_nodeH`), which names an active entry
(`rawNode_cellInv_from` with the two premises), and from the V2_2 runtime it is
`usdcLib` (`implExecKindH`). The other four runtimes decode only
`CALL`/`STATICCALL` (`*.cert_callOnly`). Constructor frames of the entries lie
before their boundaries and are not constrained.
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

/-! ## The deployed world and the premises -/

/-- An implementation or library account with the raw prefix `pre` of a committed boundary
after its deployment, the world `base` there, and its runtime `code`. -/
structure UsdcDeployedEntry where
  adr : Adr
  code : ByteArray
  base : State
  pre : List Exec.Deriv

/-- `e` is active at a raw position whose prefix is `before`. -/
def UsdcDeployedEntry.Active (e : UsdcDeployedEntry) (before : List Exec.Deriv) : Prop :=
  ∃ mid, before = e.pre ++ mid

theorem UsdcDeployedEntry.Active.append {e : UsdcDeployedEntry} {before : List Exec.Deriv}
    (h : e.Active before) (more : List Exec.Deriv) : e.Active (before ++ more) := by
  obtain ⟨mid, rfl⟩ := h
  exact ⟨mid ++ more, List.append_assoc _ _ _⟩

theorem UsdcDeployedEntry.Active.nil {e : UsdcDeployedEntry} (h : e.pre = [])
    (before : List Exec.Deriv) : e.Active before :=
  ⟨before, by rw [h, List.nil_append]⟩

theorem UsdcDeployedEntry.Active.trans {l e : UsdcDeployedEntry} {before : List Exec.Deriv}
    (hl : l.Active e.pre) (he : e.Active before) : l.Active before := by
  obtain ⟨mid, hmid⟩ := he
  rw [hmid]
  exact hl.append mid

/-- **The deployed code family (stated, positional).** `Bd s pre` is the boundary predicate
of the cell provenance from a boundary (`history.BoundaryAt`). The proxy runtime is at `P`
at the checkpoint; every account of `W` (implementations, library) carries a boundary after
its deployment with its runtime installed there; no account of `W` is `P`; a V2_2 runtime's
library account is listed and active no later than it; and `P`'s implementation slot names an
account of `W` active from the checkpoint. Constructor frames of the accounts of `W` lie
before their boundaries and are constrained by nothing here. -/
structure UsdcDeployedWorld (Bd : State → List Exec.Deriv → Prop) (P : Adr)
    (W : List UsdcDeployedEntry) (checkpoint : State) : Prop where
  proxy : checkpoint.getCode P = Proxy.code
  boundary : ∀ e ∈ W, Bd e.base e.pre
  installed : ∀ e ∈ W, e.base.getCode e.adr = e.code
  impls : ∀ e ∈ W, UsdcImplCode e.code
  apart : ∀ e ∈ W, e.adr ≠ P
  lib : ∀ e ∈ W, e.code = Impl.code →
    ∃ l ∈ W, l.adr = usdcLib ∧ l.code = Lib.code ∧ l.Active e.pre
  slot : ∃ e ∈ W, e.pre = [] ∧ ((checkpoint.getStor P).get implSlot).toAdr = e.adr

/-- **Positional upgrades (consumed form).** A proxy-runtime write to `P`'s implementation
slot at split `b₁ ++ m :: b₂` names an account of `W` active at `b₁`. -/
def UpgradesWithinFrom (P : Adr) (W : List UsdcDeployedEntry) (nodes : List Exec.Deriv) :
    Prop :=
  ∀ b₁ m b₂, nodes = b₁ ++ m :: b₂ → m.sevm.currentTarget = P → m.sevm.code = Proxy.code →
    ∀ w : Exec.StorageWrite, Exec.Deriv.successfulSstore? m = some w → w.key = implSlot →
      ∃ e ∈ W, e.Active b₁ ∧ w.value.toAdr = e.adr

/-- **Implementation-slot apartness (stated).** No frame in `P`'s context running a code
other than the proxy runtime executes a successful `SSTORE` at `(P, implSlot)` among
`nodes`. -/
def ImplSlotApart (P : Adr) (nodes : List Exec.Deriv) : Prop :=
  ∀ m ∈ nodes, m.sevm.currentTarget = P → m.sevm.code ≠ Proxy.code →
    ∀ w : Exec.StorageWrite, Exec.Deriv.successfulSstore? m = some w → w.key ≠ implSlot

/-- Local implementation-slot separation only when the original node runs one of
the five certified implementation/library runtimes. The positional code proof
supplies this recognition; no conclusion about arbitrary delegated code is assumed. -/
def KnownImplSlotApart (P : Adr) (nodes : List Exec.Deriv) : Prop :=
  ∀ m ∈ nodes, m.sevm.currentTarget = P → UsdcImplCode m.sevm.code →
    ∀ w : Exec.StorageWrite, Exec.Deriv.successfulSstore? m = some w → w.key ≠ implSlot

theorem ImplSlotApart.known {P : Adr} {nodes : List Exec.Deriv}
    (apart : ImplSlotApart P nodes) : KnownImplSlotApart P nodes := by
  intro m member target code w found
  exact apart m member target code.ne_proxy w found

/-- The listed contexts at a position: `P`, and the accounts of `W` active there. -/
def CtxAdr (P : Adr) (W : List UsdcDeployedEntry) (before : List Exec.Deriv) (a : Adr) :
    Prop :=
  a = P ∨ ∃ e ∈ W, e.Active before ∧ a = e.adr

/-- The codes allowed at a position: the proxy runtime at `P`, or the runtime of an account
of `W` active there. -/
def AllowedAt (P : Adr) (W : List UsdcDeployedEntry) (before : List Exec.Deriv) (a : Adr)
    (C : ByteArray) : Prop :=
  (a = P ∧ C = Proxy.code) ∨ ∃ e ∈ W, e.Active before ∧ C = e.code

/-- **The node invariant at a position**: a node in a listed context runs an allowed code. -/
def CtxAt (P : Adr) (W : List UsdcDeployedEntry) (before : List Exec.Deriv)
    (n : Exec.Deriv) : Prop :=
  ∀ a, CtxAdr P W before a → n.sevm.currentTarget = a → AllowedAt P W before a n.sevm.code

/-- **The codes run in `P`'s context at the nodes** (the consumed form). -/
def UsdcNodeCodes (P : Adr) (nodes : List Exec.Deriv) : Prop :=
  ∀ n ∈ nodes, n.sevm.currentTarget = P → UsdcContextCode n.sevm.code

theorem AllowedAt.mono {P : Adr} {W : List UsdcDeployedEntry} {b : List Exec.Deriv} {a : Adr}
    {C : ByteArray} (h : AllowedAt P W b a C) (more : List Exec.Deriv) :
    AllowedAt P W (b ++ more) a C := by
  rcases h with h | ⟨e, he, act, hc⟩
  · exact .inl h
  · exact .inr ⟨e, he, act.append more, hc⟩

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {P : Adr} {W : List UsdcDeployedEntry}

theorem AllowedAt.context {Bd : State → List Exec.Deriv → Prop}
    (world : UsdcDeployedWorld Bd P W checkpoint.state) {b : List Exec.Deriv} {a : Adr}
    {C : ByteArray} (h : AllowedAt P W b a C) : UsdcContextCode C := by
  rcases h with ⟨-, rfl⟩ | ⟨e, he, -, rfl⟩
  · exact Or.inl rfl
  · exact (world.impls e he).context

/-- A raw node running a USDC code never executes `SELFDESTRUCT`. -/
theorem not_selfdestruct_of_usdc (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {m : Exec.Deriv} (hm : m ∈ history.rawNodes)
    (fam : UsdcContextCode m.sevm.code) : ¬ Linst.At m.sevm.code m.pc .selfdestruct := by
  obtain ⟨G, hG, chain⟩ := (history.mem_rawNodes_iff_rawFrame_parentPrefix m).mp hm
  have hsevm := Exec.Deriv.ParentPrefix.sevm_eq chain
  have facts := history.rawFrame_entryFacts capabilities G hG
  rw [hsevm] at fam
  obtain ⟨c, hc, noSD⟩ := usdcContextCode_certified _ fam
  exact Lift.not_selfdestruct_of_parentPrefix_noStateGas hc noSD facts.1 rfl facts.2.2.1 chain

/-- Node codes at `P` make the nodes safe at `P`. -/
theorem UsdcNodeCodes.safe (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (codes : UsdcNodeCodes P history.rawNodes) :
    ∀ m ∈ history.rawNodes, m.sevm.currentTarget = P →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct := fun m hm target =>
  not_selfdestruct_of_usdc history capabilities hm (codes m hm target)

/-- Node codes at `P` give the frame codes at `P`. -/
theorem UsdcNodeCodes.frames (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (codes : UsdcNodeCodes P history.rawNodes) :
    ∀ G ∈ history.rawFrames, G.sevm.currentTarget = P → UsdcContextCode G.sevm.code := by
  intro G hG target
  have hmem : G ∈ history.rawNodes := by
    refine history.rawNodes_of_mem_rawFrames G hG G ?_
    rcases G with ⟨pc, sevm, pre, out, run⟩
    exact Exec.mem_rawNodes_self run
  exact codes G hmem target

/-- The nodes after a base `q` up to a position are safe at a context listed at every
position after `q`. -/
theorem safe_from (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (world : UsdcDeployedWorld history.BoundaryAt P W checkpoint.state)
    {q mid post : List Exec.Deriv} {x : Exec.Deriv}
    (split : history.rawNodes = q ++ mid ++ x :: post)
    (ok : ∀ b₁ m b₂, q ++ mid = b₁ ++ m :: b₂ → CtxAt P W b₁ m) {a : Adr}
    (hctx : ∀ mid₁, CtxAdr P W (q ++ mid₁) a) :
    ∀ m ∈ mid, m.sevm.currentTarget = a → ¬ Linst.At m.sevm.code m.pc .selfdestruct := by
  intro m hm target
  obtain ⟨mid₁, mid₂, hb⟩ := List.append_of_mem hm
  have okm := ok (q ++ mid₁) m mid₂ (by rw [hb, List.append_assoc])
  have hmem : m ∈ history.rawNodes := by
    rw [split, hb]
    exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_append_right _ List.mem_cons_self))
  exact not_selfdestruct_of_usdc history capabilities hmem
    ((okm a (hctx mid₁) target).context world)

/-- At a node whose earlier positions satisfy the invariant, `P` holds the proxy runtime,
every account of `W` active there holds its runtime, and `P`'s implementation word names an
account of `W` active there. -/
theorem world_at_of_knownApart (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (world : UsdcDeployedWorld history.BoundaryAt P W checkpoint.state)
    (upgrades : UpgradesWithinFrom P W history.rawNodes) (apartSlot : KnownImplSlotApart P history.rawNodes)
    {b post : List Exec.Deriv} {x : Exec.Deriv} (split : history.rawNodes = b ++ x :: post)
    (ok : ∀ b₁ m b₂, b = b₁ ++ m :: b₂ → CtxAt P W b₁ m) :
    x.devm.getCode P = Proxy.code ∧ (∀ e ∈ W, e.Active b → x.devm.getCode e.adr = e.code) ∧
      ∃ e ∈ W, e.Active b ∧ ((x.devm.getStor P).get implSlot).toAdr = e.adr := by
  have proxyFam : UsdcContextCode Proxy.code := Or.inl rfl
  have split0 : history.rawNodes = [] ++ b ++ x :: post := by rw [List.nil_append]; exact split
  have ok0 : ∀ b₁ m b₂, [] ++ b = b₁ ++ m :: b₂ → CtxAt P W b₁ m := fun b₁ m b₂ h =>
    ok b₁ m b₂ (by rw [List.nil_append] at h; exact h)
  have safeP := safe_from history capabilities world split0 ok0 (a := P) fun _ => .inl rfl
  refine ⟨(history.rawNode_cellProvenance_from capabilities proxyFam.not_delegation
      proxyFam.ne_nil history.boundaryAt_checkpoint world.proxy 0 split0 safeP).1,
    fun e he act => ?_, ?_⟩
  · obtain ⟨mid, hmid⟩ := act
    have fam := (world.impls e he).context
    have splitE : history.rawNodes = e.pre ++ mid ++ x :: post := by rw [split, hmid]
    have okE : ∀ b₁ m b₂, e.pre ++ mid = b₁ ++ m :: b₂ → CtxAt P W b₁ m := fun b₁ m b₂ h =>
      ok b₁ m b₂ (by rw [hmid]; exact h)
    exact (history.rawNode_cellProvenance_from capabilities fam.not_delegation fam.ne_nil
      (world.boundary e he) (world.installed e he) 0 splitE
      (safe_from history capabilities world splitE okE
        fun mid₁ => .inr ⟨e, he, ⟨mid₁, rfl⟩, rfl⟩)).1
  · obtain ⟨e₀, he₀, hpre₀, hname₀⟩ := world.slot
    have sub : ∀ m ∈ b, m ∈ history.rawNodes := fun m hm => by
      rw [split]; exact List.mem_append_left _ hm
    have inv := history.rawNode_cellInv_from capabilities proxyFam.not_delegation
      proxyFam.ne_nil history.boundaryAt_checkpoint world.proxy
      (Inv := fun v => ∃ e ∈ W, e.Active b ∧ v.toAdr = e.adr)
      ⟨e₀, he₀, UsdcDeployedEntry.Active.nil hpre₀ b, hname₀⟩ split0 safeP ?_
    · exact inv
    intro m hm w found owner key
    have target : m.sevm.currentTarget = P :=
      ((successfulSstore?_node_owner found).2.symm.trans owner)
    by_cases hcode : m.sevm.code = Proxy.code
    · obtain ⟨b₁, b₂, hb⟩ := List.append_of_mem hm
      have splitM : history.rawNodes = b₁ ++ m :: (b₂ ++ x :: post) := by
        rw [split, hb]; simp only [List.append_assoc, List.cons_append]
      obtain ⟨e, he, act, hname⟩ := upgrades b₁ m (b₂ ++ x :: post) splitM target hcode w found key
      refine ⟨e, he, ?_, hname⟩
      rw [hb]
      exact act.append _
    · obtain ⟨b₁, b₂, hb⟩ := List.append_of_mem hm
      have family := (ok b₁ m b₂ hb P (.inl rfl) target).context world
      exact absurd key (apartSlot m (sub m hm) target (family.resolve_left hcode) w found)

/-- Compatibility form with the original all-nonproxy slot-separation premise. -/
theorem world_at (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (world : UsdcDeployedWorld history.BoundaryAt P W checkpoint.state)
    (upgrades : UpgradesWithinFrom P W history.rawNodes) (apartSlot : ImplSlotApart P history.rawNodes)
    {b post : List Exec.Deriv} {x : Exec.Deriv} (split : history.rawNodes = b ++ x :: post)
    (ok : ∀ b₁ m b₂, b = b₁ ++ m :: b₂ → CtxAt P W b₁ m) :
    x.devm.getCode P = Proxy.code ∧ (∀ e ∈ W, e.Active b → x.devm.getCode e.adr = e.code) ∧
      ∃ e ∈ W, e.Active b ∧ ((x.devm.getStor P).get implSlot).toAdr = e.adr := by
  exact world_at_of_knownApart history capabilities world upgrades apartSlot.known split ok

/-- The active library of a running V2_2 implementation holds its actual installed code. -/
theorem UsdcDeployedWorld.active_library_code
    {Bd : State → List Exec.Deriv → Prop} {P a : Adr} {W : List UsdcDeployedEntry}
    {checkpoint : State} {before : List Exec.Deriv} {C : ByteArray} {d : Devm}
    (world : UsdcDeployedWorld Bd P W checkpoint)
    (allowed : AllowedAt P W before a C) (impl : C = Impl.code)
    (installed : ∀ e ∈ W, e.Active before → d.getCode e.adr = e.code) :
    ∃ l ∈ W, l.adr = usdcLib ∧ l.code = Lib.code ∧ l.Active before ∧
      d.getCode usdcLib = Lib.code := by
  obtain ⟨l, hl, ladr, lcode, lact⟩ : ∃ l ∈ W, l.adr = usdcLib ∧ l.code = Lib.code ∧
      l.Active before := by
    rcases allowed with ⟨-, hc⟩ | ⟨e, he, act, hc⟩
    · exact absurd (hc.symm.trans impl) proxy_ne_impl
    · obtain ⟨l, hl, ladr, lcode, lact⟩ := world.lib e he (hc.symm.trans impl)
      exact ⟨l, hl, ladr, lcode, lact.trans act⟩
  refine ⟨l, hl, ladr, lcode, lact, ?_⟩
  rw [← ladr, ← lcode]
  exact installed l hl lact

/-- The code installed at a listed context is allowed there and is a USDC code. -/
theorem installed_allowed {Bd : State → List Exec.Deriv → Prop}
    (world : UsdcDeployedWorld Bd P W checkpoint.state) {b : List Exec.Deriv} {d : Devm}
    (hP : d.getCode P = Proxy.code) (hW : ∀ e ∈ W, e.Active b → d.getCode e.adr = e.code)
    {a : Adr} (ha : CtxAdr P W b a) :
    AllowedAt P W b a (d.getCode a) ∧ UsdcContextCode (d.getCode a) := by
  have allowed : AllowedAt P W b a (d.getCode a) := by
    rcases ha with rfl | ⟨e, he, act, rfl⟩
    · exact .inl ⟨rfl, hP⟩
    · exact .inr ⟨e, he, act, hW e he act⟩
  exact ⟨allowed, allowed.context world⟩

/-- One induction step, at one context: a node after a base `q` at a context listed at every
position after `q` runs an allowed code, from the invariant at every earlier position. -/
theorem ctxAt_step_of_knownApart (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    (world : UsdcDeployedWorld history.BoundaryAt P W checkpoint.state)
    (upgrades : UpgradesWithinFrom P W history.rawNodes) (apartSlot : KnownImplSlotApart P history.rawNodes)
    {s : State} {q mid after : List Exec.Deriv} {n : Exec.Deriv} (base : history.BoundaryAt s q)
    {a : Adr} (hctx : ∀ mid₁, CtxAdr P W (q ++ mid₁) a)
    (split : history.rawNodes = q ++ mid ++ n :: after)
    (ok : ∀ b₁ m b₂, q ++ mid = b₁ ++ m :: b₂ → CtxAt P W b₁ m)
    (target : n.sevm.currentTarget = a) : AllowedAt P W (q ++ mid) a n.sevm.code := by
  rcases base.rawOrigin split with root | ⟨m, hm, he⟩ | ⟨m, hm, hspawn⟩
  · -- a message root runs the code installed at its target
    obtain ⟨hP, hW, -⟩ := world_at_of_knownApart history capabilities world upgrades apartSlot
      (by rw [split, List.append_assoc]) ok
    have inst := installed_allowed world hP hW (hctx mid)
    rw [root a target inst.2.ne_nil inst.2.not_delegation]
    exact inst.1
  · -- a successor of an earlier node of its frame
    obtain ⟨mid₁, mid₂, hb⟩ := List.append_of_mem hm
    have okm := ok (q ++ mid₁) m mid₂ (by rw [hb, List.append_assoc])
    rw [← he] at target ⊢
    have := (okm a (hctx mid₁) target).mono (m :: mid₂)
    rwa [List.append_assoc, ← hb] at this
  · -- the root of a frame an earlier node spawned
    obtain ⟨mid₁, mid₂, hb⟩ := List.append_of_mem hm
    have posEq : q ++ mid = (q ++ mid₁) ++ m :: mid₂ := by rw [hb, List.append_assoc]
    have mono : ∀ {C : ByteArray}, AllowedAt P W (q ++ mid₁) a C →
        AllowedAt P W (q ++ mid) a C := fun h => by
      rw [posEq]; exact h.mono _
    have split' : history.rawNodes = (q ++ mid₁) ++ m :: (mid₂ ++ n :: after) := by
      rw [split, posEq]; simp only [List.append_assoc, List.cons_append]
    have ok' : ∀ b₁ m' b₂, q ++ mid₁ = b₁ ++ m' :: b₂ → CtxAt P W b₁ m' :=
      fun b₁ m' b₂ h => ok b₁ m' (b₂ ++ m :: mid₂) (by
        rw [posEq, h]; simp only [List.append_assoc, List.cons_append])
    obtain ⟨hP, hW, hslot⟩ := world_at_of_knownApart history capabilities world upgrades apartSlot split' ok'
    obtain ⟨f, rsm, pc', cevm, hs, henter, -, hsta, -⟩ := hspawn
    have childTarget : n.sevm.currentTarget = f.inner.currentTarget := by
      rw [← hsta]; exact Frame.enter_run_currentTarget henter
    have childCode : n.sevm.code = f.inner.code := by
      rw [← hsta]; exact Frame.enter_run_code henter
    have instA := installed_allowed world hP hW (hctx mid₁)
    by_cases hsame : m.sevm.currentTarget = a
    · obtain ⟨x, hat, hx, -⟩ := Evm.step_spawn_inv hs
      have mMem : m ∈ history.rawNodes := by
        rw [split']; exact List.mem_append_right _ List.mem_cons_self
      obtain ⟨G, hG, chain⟩ := (history.mem_rawNodes_iff_rawFrame_parentPrefix m).mp mMem
      have hsevm := Exec.Deriv.ParentPrefix.sevm_eq chain
      have facts := history.rawFrame_entryFacts capabilities G hG
      have allowedM := ok (q ++ mid₁) m mid₂ posEq a (hctx mid₁) hsame
      have fam := allowedM.context world
      rw [hsevm] at fam
      rcases usdc_exec_kind facts.1 facts.2.2.1 (bal facts.2.1) chain fam hat with
        hcall | hcall | ⟨rfl, hdel⟩
      · rw [childCode, Xinst.step_directCall_spawn_code (.inl hcall) hx
          (by rw [← childTarget, target]; exact instA.2.not_delegation),
          ← childTarget, target]
        exact mono instA.1
      · rw [childCode, Xinst.step_directCall_spawn_code (.inr hcall) hx
          (by rw [← childTarget, target]; exact instA.2.not_delegation),
          ← childTarget, target]
        exact mono instA.1
      · obtain ⟨g, w, rest, hstack⟩ := Xinst.step_delegatecall_spawn_stack hx
        rw [← hsevm] at hdel
        rcases hdel with ⟨hproxy, hw⟩ | ⟨himpl, hw⟩
        · -- the proxy forwards to the account its implementation word names
          have hwP : w = m.devm.getStorVal P implSlot := by
            rw [hw g w rest hstack, hsame]
            rcases allowedM with ⟨rfl, -⟩ | ⟨e, he, -, hc⟩
            · rfl
            · exact absurd (hc.symm.trans hproxy) (world.impls e he).ne_proxy
          obtain ⟨e, he, act, hname⟩ := hslot
          have hcodeE : m.devm.getCode w.toAdr = e.code := by
            rw [hwP]; exact (hname ▸ hW e he act :)
          rw [childCode, Xinst.step_delegatecall_spawn_code hx hstack
            (by rw [hcodeE]; exact (world.impls e he).context.not_delegation), hcodeE]
          exact mono (.inr ⟨e, he, act, rfl⟩)
        · -- the V2_2 runtime forwards to the library
          obtain ⟨l, hl, ladr, lcode, lact, libCode⟩ :=
            world.active_library_code allowedM himpl hW
          have hcodeL : m.devm.getCode w.toAdr = Lib.code := by
            rw [hw g w rest hstack, toAdr_toB256]
            exact libCode
          rw [childCode, Xinst.step_delegatecall_spawn_code hx hstack
            (by rw [hcodeL]; exact Lib.code_not_delegation), hcodeL, ← lcode]
          exact mono (.inr ⟨l, hl, lact, rfl⟩)
    · -- a child at another target runs the callee's installed code
      have hcode := (Evm.step_spawn_child hs henter).2.2
        (by rw [hsta, target]; exact hsame)
        (by rw [hsta, target]; exact instA.2.ne_empty)
        (by rw [hsta, target]; exact instA.2.not_delegation)
      rw [hsta, target] at hcode
      rw [hcode]
      exact mono instA.1

/-- Compatibility form with the original all-nonproxy slot-separation premise. -/
theorem ctxAt_step (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    (world : UsdcDeployedWorld history.BoundaryAt P W checkpoint.state)
    (upgrades : UpgradesWithinFrom P W history.rawNodes) (apartSlot : ImplSlotApart P history.rawNodes)
    {s : State} {q mid after : List Exec.Deriv} {n : Exec.Deriv} (base : history.BoundaryAt s q)
    {a : Adr} (hctx : ∀ mid₁, CtxAdr P W (q ++ mid₁) a)
    (split : history.rawNodes = q ++ mid ++ n :: after)
    (ok : ∀ b₁ m b₂, q ++ mid = b₁ ++ m :: b₂ → CtxAt P W b₁ m)
    (target : n.sevm.currentTarget = a) : AllowedAt P W (q ++ mid) a n.sevm.code := by
  exact ctxAt_step_of_knownApart history capabilities bal world upgrades apartSlot.known base hctx split ok target

/-- **The codes run in the listed contexts**, at every position of the history. -/
theorem ConfiguredHistoryTraceIn.usdc_ctxAt_of_knownApart
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    (world : UsdcDeployedWorld history.BoundaryAt P W checkpoint.state)
    (upgrades : UpgradesWithinFrom P W history.rawNodes) (apartSlot : KnownImplSlotApart P history.rawNodes) :
    ∀ before n after, history.rawNodes = before ++ n :: after → CtxAt P W before n := by
  refine List.forall_split_of_positional fun before n after split ok a ha target => ?_
  rcases ha with rfl | ⟨e, he, ⟨mid, hmid⟩, rfl⟩
  · have := ctxAt_step_of_knownApart history capabilities bal world upgrades apartSlot
      history.boundaryAt_checkpoint (q := []) (fun _ => .inl rfl)
      (by rw [List.nil_append]; exact split) (fun b₁ m b₂ h => ok b₁ m b₂ h) target
    rwa [List.nil_append] at this
  · subst hmid
    exact ctxAt_step_of_knownApart history capabilities bal world upgrades apartSlot (world.boundary e he)
      (fun mid₁ => .inr ⟨e, he, ⟨mid₁, rfl⟩, rfl⟩) split ok target

/-- Compatibility form with the original all-nonproxy slot-separation premise. -/
theorem ConfiguredHistoryTraceIn.usdc_ctxAt
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    (world : UsdcDeployedWorld history.BoundaryAt P W checkpoint.state)
    (upgrades : UpgradesWithinFrom P W history.rawNodes) (apartSlot : ImplSlotApart P history.rawNodes) :
    ∀ before n after, history.rawNodes = before ++ n :: after → CtxAt P W before n := by
  exact ConfiguredHistoryTraceIn.usdc_ctxAt_of_knownApart history capabilities bal world upgrades apartSlot.known

/-- The original all-nonproxy premise follows from separation for known runtimes.
Recognition comes from the positional induction, so this does not assume the
node-code conclusion in order to establish the implementation-slot invariant. -/
theorem ConfiguredHistoryTraceIn.implSlotApart_of_knownCodes
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    (world : UsdcDeployedWorld history.BoundaryAt P W checkpoint.state)
    (upgrades : UpgradesWithinFrom P W history.rawNodes)
    (apart : KnownImplSlotApart P history.rawNodes) : ImplSlotApart P history.rawNodes := by
  have contexts := ConfiguredHistoryTraceIn.usdc_ctxAt_of_knownApart
    history capabilities bal world upgrades apart
  intro m member target nonproxy w found
  obtain ⟨before, after, split⟩ := List.append_of_mem member
  have family := (contexts before m after split P (.inl rfl) target).context world
  exact apart m member target (family.resolve_left nonproxy) w found

/-- **The node codes at `P`.** Every raw node in the proxy's storage context runs a USDC
code. -/
theorem ConfiguredHistoryTraceIn.usdc_nodeCodes
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    (world : UsdcDeployedWorld history.BoundaryAt P W checkpoint.state)
    (upgrades : UpgradesWithinFrom P W history.rawNodes) (apartSlot : ImplSlotApart P history.rawNodes) :
    UsdcNodeCodes P history.rawNodes := by
  intro n hn target
  obtain ⟨before, after, split⟩ := List.append_of_mem hn
  exact (ConfiguredHistoryTraceIn.usdc_ctxAt history capabilities bal world upgrades apartSlot
    before n after split P (.inl rfl) target).context world

/-- **`codes` discharged.** Every raw frame in the proxy's storage context runs a USDC
code. -/
theorem ConfiguredHistoryTraceIn.usdc_contextCodes
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    (world : UsdcDeployedWorld history.BoundaryAt P W checkpoint.state)
    (upgrades : UpgradesWithinFrom P W history.rawNodes) (apartSlot : ImplSlotApart P history.rawNodes) :
    ∀ G ∈ history.rawFrames, G.sevm.currentTarget = P → UsdcContextCode G.sevm.code :=
  (ConfiguredHistoryTraceIn.usdc_nodeCodes history capabilities bal world upgrades
    apartSlot).frames history

/-- **Raw safety at the proxy** from the deployed world and the two implementation-slot
premises. -/
theorem usdc_safeRawFrames_of_world (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    (world : UsdcDeployedWorld history.BoundaryAt P W checkpoint.state)
    (upgrades : UpgradesWithinFrom P W history.rawNodes) (apartSlot : ImplSlotApart P history.rawNodes) :
    SafeRawFrames P history.rawFrames :=
  usdc_safeRawFrames history capabilities
    (ConfiguredHistoryTraceIn.usdc_contextCodes history capabilities bal world upgrades apartSlot)

/-- **The proxy runtime at every raw frame** from the deployed world and the two
implementation-slot premises. -/
theorem rawFrame_proxyCode_of_world (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    (world : UsdcDeployedWorld history.BoundaryAt P W checkpoint.state)
    (upgrades : UpgradesWithinFrom P W history.rawNodes) (apartSlot : ImplSlotApart P history.rawNodes) :
    ∀ R ∈ history.rawFrames, R.devm.getCode P = Proxy.code :=
  rawFrame_proxyCode history capabilities world.proxy
    (ConfiguredHistoryTraceIn.usdc_contextCodes history capabilities bal world upgrades apartSlot)

end History

end Blanc.Lift.Usdc
