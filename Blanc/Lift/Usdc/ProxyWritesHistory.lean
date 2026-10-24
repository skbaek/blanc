import Blanc.Lift.Usdc.ProxySstoreH
import Blanc.Lift.Usdc.AllowanceRawHistory

/-!
# The proxy runtime's own writes along an In-history

`proxy_sstoreNodeH` (`ProxySstoreH.lean`) names the key of every `SSTORE` the proxy
runtime reaches. Lifted to the raw nodes of a `ConfiguredHistoryTraceIn`, it discharges
two history premises of the Pair allowance law:

* `ProxyRowsApart` (`AllowanceRawHistory.lean`) from the two-constant separation
  `ProxySlotsApart`: no tracked Pair row is the implementation or admin slot.
* `UpgradesWithin` (`ProxyContextCodes.lean`) from `AdminUpgradesWithin`: an
  implementation-slot write of the proxy runtime stores `upgradeArg` under the
  `upgradeTo`/`upgradeToAndCall` selector for a caller equal to the frame's entry admin
  word, so it suffices that every such admin upgrade frame names an account of `W`.
  Which addresses the admin installs is a fact about the history, stated here per frame.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- **Two-constant separation (stated).** No tracked Pair allowance row is the proxy's
implementation slot or admin slot. -/
def ProxySlotsApart (pair : Adr) (Tr : Adr → Prop) : Prop :=
  ∀ g, Tr g → allowSlot pair g ≠ implSlot ∧ allowSlot pair g ≠ adminSlot

/-- **The admin's upgrades (stated).** Every raw proxy frame at `P` under the `upgradeTo` or
`upgradeToAndCall` selector whose caller is the admin word of its entry state names an account
of `W` by its upgrade argument. -/
def AdminUpgradesWithin (P : Adr) (W : List (Adr × ByteArray)) (frames : List Exec.Deriv) :
    Prop :=
  ∀ G ∈ frames, G.sevm.currentTarget = P → G.sevm.code = Proxy.code →
    (Proxy.dispatchWord G.sevm = Proxy.upgradeToWord ∨
      Proxy.dispatchWord G.sevm = Proxy.upgradeToAndCallWord) →
    G.sevm.caller = (G.devm.getStorVal P adminSlot).toAdr →
    ∃ e ∈ W, (Proxy.upgradeArg G.sevm).toAdr = e.1

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {P : Adr} {W : List (Adr × ByteArray)} {pair : Adr} {Tr : Adr → Prop}

/-- A successful raw `SSTORE` of the proxy runtime at `P`: its frame, and the key/value
classification of `proxy_sstoreNodeH`. -/
theorem ConfiguredHistoryTraceIn.proxy_rawWrite
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {m : Exec.Deriv} (hm : m ∈ history.rawNodes) (target : m.sevm.currentTarget = P)
    (code : m.sevm.code = Proxy.code) {w : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? m = some w) :
    ∃ G ∈ history.rawFrames, Exec.Deriv.ParentPrefix G m ∧ G.sevm.currentTarget = P ∧
      G.sevm.code = Proxy.code ∧
      (w.key = adminSlot ∨
        (w.key = implSlot ∧ w.value = Proxy.upgradeArg G.sevm ∧
          (Proxy.dispatchWord G.sevm = Proxy.upgradeToWord ∨
            Proxy.dispatchWord G.sevm = Proxy.upgradeToAndCallWord) ∧
          G.sevm.caller = (G.devm.getStorVal P adminSlot).toAdr)) := by
  obtain ⟨G, hG, chain⟩ := (history.mem_rawNodes_iff_rawFrame_parentPrefix m).mp hm
  have hsevm := Exec.Deriv.ParentPrefix.sevm_eq chain
  obtain ⟨hpc, hfork, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities G hG
  obtain ⟨decoded, rest, stack⟩ := successfulSstore?_decoded found
  have gTarget : G.sevm.currentTarget = P := by rw [← hsevm]; exact target
  have gCode : G.sevm.code = Proxy.code := by rw [← hsevm]; exact code
  refine ⟨G, hG, chain, gTarget, gCode, ?_⟩
  rcases G with ⟨pc, sevm, pre, out, run⟩
  dsimp only at hpc hfork hsg gTarget gCode chain ⊢
  subst hpc
  rcases Proxy.proxy_sstoreNodeH run gCode hsg (bal hfork) chain decoded with
    ⟨rest', hs⟩ | ⟨rest', hs, sel, adm⟩
  · rw [stack] at hs
    exact .inl (List.cons.inj hs).1
  · rw [stack] at hs
    obtain ⟨hk, hv⟩ := List.cons_eq_cons.mp hs
    refine .inr ⟨hk, (List.cons.inj hv).1, sel, ?_⟩
    rw [adm, gTarget]

/-- **`ProxyRowsApart` from the two-constant separation.** -/
theorem ConfiguredHistoryTraceIn.proxyRowsApart
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    (apart : ProxySlotsApart pair Tr) :
    ProxyRowsApart P pair Tr history.rawNodes := by
  intro m hm target code w found ⟨g, hg, key⟩
  obtain ⟨_, _, _, _, _, cls⟩ :=
    ConfiguredHistoryTraceIn.proxy_rawWrite history capabilities bal hm target code found
  rcases cls with admin | ⟨impl, -⟩
  · exact (apart g hg).2 (key.trans admin)
  · exact (apart g hg).1 (key.trans impl)

/-- **`UpgradesWithin` from the admin's upgrades.** -/
theorem ConfiguredHistoryTraceIn.upgradesWithin
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    (admin : AdminUpgradesWithin P W history.rawFrames) :
    UpgradesWithin P W history.rawNodes := by
  intro m hm target code w found key
  obtain ⟨G, hG, -, gTarget, gCode, cls⟩ :=
    ConfiguredHistoryTraceIn.proxy_rawWrite history capabilities bal hm target code found
  rcases cls with adminKey | ⟨-, value, sel, caller⟩
  · exact absurd (adminKey.symm.trans key) (by decide)
  · rw [value]
    exact admin G hG gTarget gCode sel caller

/-! ## Positional form, for accounts deployed after the checkpoint

With a base at a committed boundary per account (the shape of the drafted
`ConfiguredHistoryTraceIn.BoundaryAt s pre`, which the cell provenance from a boundary
consumes), an account of `W` is active at a raw position once the position's prefix extends
its boundary prefix. The positional upgrade premise names an account active before the
write. -/

/-- An account of the code family with the raw prefix `pre` of its activation boundary. -/
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

/-- **The deployed code family (stated, positional).** `Bd s pre` is the boundary predicate
the cell provenance from a boundary takes (`history.BoundaryAt`); the proxy is fixed at the
checkpoint, and every account of `W` (implementations, library) carries the boundary after
its deployment, with its runtime installed there. Constructor frames of those accounts lie
before their boundaries and are constrained by nothing here. -/
structure UsdcDeployedWorld (Bd : State → List Exec.Deriv → Prop) (P : Adr)
    (W : List UsdcDeployedEntry) (checkpoint : State) : Prop where
  proxy : checkpoint.getCode P = Proxy.code
  boundary : ∀ e ∈ W, Bd e.base e.pre
  installed : ∀ e ∈ W, e.base.getCode e.adr = e.code
  impls : ∀ e ∈ W, UsdcImplCode e.code
  apart : ∀ e ∈ W, e.adr ≠ P
  lib : ∀ e ∈ W, e.code = Impl.code →
    ∃ l ∈ W, l.adr = usdcLib ∧ l.code = Lib.code ∧ ∃ mid, e.pre = l.pre ++ mid
  slot : ∃ e ∈ W, e.pre = [] ∧ ((checkpoint.getStor P).get implSlot).toAdr = e.adr

/-- **Positional upgrades (consumed form).** A proxy-runtime write to `P`'s implementation
slot at split `b₁ ++ m :: b₂` names an account of `W` active at `b₁`. -/
def UpgradesWithinFrom (P : Adr) (W : List UsdcDeployedEntry) (nodes : List Exec.Deriv) :
    Prop :=
  ∀ b₁ m b₂, nodes = b₁ ++ m :: b₂ → m.sevm.currentTarget = P → m.sevm.code = Proxy.code →
    ∀ w : Exec.StorageWrite, Exec.Deriv.successfulSstore? m = some w → w.key = implSlot →
      ∃ e ∈ W, e.Active b₁ ∧ w.value.toAdr = e.adr

/-- **The admin's upgrades, positional (stated).** An admin upgrade frame of the proxy at `P`
that writes at split `b₁ ++ m :: b₂` names by its upgrade argument an account of `W` active
at `b₁`: the admin installs only deployed accounts. -/
def AdminUpgradesWithinFrom (P : Adr) (W : List UsdcDeployedEntry)
    (frames nodes : List Exec.Deriv) : Prop :=
  ∀ b₁ m b₂, nodes = b₁ ++ m :: b₂ → ∀ G ∈ frames, Exec.Deriv.ParentPrefix G m →
    G.sevm.currentTarget = P → G.sevm.code = Proxy.code →
    (Proxy.dispatchWord G.sevm = Proxy.upgradeToWord ∨
      Proxy.dispatchWord G.sevm = Proxy.upgradeToAndCallWord) →
    G.sevm.caller = (G.devm.getStorVal P adminSlot).toAdr →
    ∃ e ∈ W, e.Active b₁ ∧ (Proxy.upgradeArg G.sevm).toAdr = e.adr

/-- **`UpgradesWithinFrom` from the positional admin upgrades.** -/
theorem ConfiguredHistoryTraceIn.upgradesWithinFrom
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {W : List UsdcDeployedEntry}
    (admin : AdminUpgradesWithinFrom P W history.rawFrames history.rawNodes) :
    UpgradesWithinFrom P W history.rawNodes := by
  intro b₁ m b₂ split target code w found key
  have hm : m ∈ history.rawNodes := by
    rw [split]; exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨G, hG, chain, gTarget, gCode, cls⟩ :=
    ConfiguredHistoryTraceIn.proxy_rawWrite history capabilities bal hm target code found
  rcases cls with adminKey | ⟨-, value, sel, caller⟩
  · exact absurd (adminKey.symm.trans key) (by decide)
  · rw [value]
    exact admin b₁ m b₂ split G hG chain gTarget gCode sel caller

end History

end Blanc.Lift.Usdc
