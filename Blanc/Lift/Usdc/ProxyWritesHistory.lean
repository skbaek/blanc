import Blanc.Lift.Usdc.ProxySstoreH
import Blanc.Lift.Usdc.AllowanceRawHistory

/-!
# The proxy runtime's own writes along an In-history

`proxy_sstoreNodeH` (`ProxySstoreH.lean`) names the key of every `SSTORE` the proxy
runtime reaches. Lifted to the raw nodes of a `ConfiguredHistoryTraceIn`, it discharges
two history premises of the Pair allowance law:

* `ProxyRowsApart` (`AllowanceRawHistory.lean`) from the two-constant separation
  `ProxySlotsApart`: no tracked Pair row is the implementation or admin slot.
* `UpgradesWithinFrom` (`ProxyContextCodes.lean`) from `AdminUpgradesWithinFrom`: an
  implementation-slot write of the proxy runtime stores `upgradeArg` under the
  `upgradeTo`/`upgradeToAndCall` selector for a caller equal to the frame's entry admin
  word, so it suffices that every such admin upgrade frame names an account of `W` active
  at the write. Which addresses the admin installs is a fact about the history, stated here
  per frame.

`usdc_pairAllowance_noIncrease_deployed` is the Pair allowance law over the deployed world
(`UsdcDeployedWorld` at the history's boundaries) with both premises discharged.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- **Two-constant separation (stated).** No tracked Pair allowance row is the proxy's
implementation slot or admin slot. -/
def ProxySlotsApart (pair : Adr) (Tr : Adr → Prop) : Prop :=
  ∀ g, Tr g → allowSlot pair g ≠ implSlot ∧ allowSlot pair g ≠ adminSlot

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {P : Adr} {W : List UsdcDeployedEntry} {pair : Adr} {Tr : Adr → Prop}

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

/-- **The admin's upgrades, positional (stated).** An admin upgrade frame of the proxy at `P`
with a successful `SSTORE` at `(P, implSlot)` at split `b₁ ++ m :: b₂` names by its upgrade
argument an account of `W` active at `b₁`: the admin installs only deployed accounts. Upgrade
attempts that write no implementation slot (reverted ones, say) are unconstrained. -/
def AdminUpgradesWithinFrom (P : Adr) (W : List UsdcDeployedEntry)
    (frames nodes : List Exec.Deriv) : Prop :=
  ∀ b₁ m b₂, nodes = b₁ ++ m :: b₂ → ∀ w : Exec.StorageWrite,
    Exec.Deriv.successfulSstore? m = some w → w.owner = P → w.key = implSlot →
    ∀ G ∈ frames, Exec.Deriv.ParentPrefix G m →
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
    exact admin b₁ m b₂ split w found ((successfulSstore?_node_owner found).2.trans target) key G
      hG chain gTarget gCode sel caller

/-- **P1 over the deployed world.** Every tracked allowance row of the Pair is at most its
checkpoint word at every raw node and at the future, with the implementation and library
accounts active from their own deployment boundaries, the proxy's own writes discharged
(`ProxySlotsApart`, `AdminUpgradesWithinFrom`), and the remaining premises of
`usdc_pairAllowance_noIncrease`. -/
theorem ConfiguredHistoryTraceIn.usdc_pairAllowance_noIncrease_deployed
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    (world : UsdcDeployedWorld history.BoundaryAt P W checkpoint.state)
    (admin : AdminUpgradesWithinFrom P W history.rawFrames history.rawNodes)
    (apartSlot : ImplSlotApart P history.rawNodes)
    (slotsApart : ProxySlotsApart pair Tr)
    (rowSep : UsdcRowSep P pair Tr history.rawFrames)
    (noPairException : NoPairExceptionWrites P pair Tr history.rawFrames history.rawNodes)
    (initRows : InitRowWritesNonInc P pair Tr history.rawFrames)
    {k : B256} (tracked : ∃ g, Tr g ∧ allowSlot pair g = k) :
    (∀ n ∈ history.rawNodes,
        ((n.devm.getStor P).get k).toNat ≤ ((checkpoint.state.getStor P).get k).toNat) ∧
      ((future.state.getStor P).get k).toNat ≤ ((checkpoint.state.getStor P).get k).toNat :=
  ConfiguredHistoryTraceIn.usdc_pairAllowance_noIncrease history capabilities world.proxy
    (ConfiguredHistoryTraceIn.usdc_nodeCodes history capabilities bal world
      (ConfiguredHistoryTraceIn.upgradesWithinFrom history capabilities bal admin) apartSlot)
    (ConfiguredHistoryTraceIn.proxyRowsApart history capabilities bal slotsApart) rowSep
    noPairException initRows tracked

end History

end Blanc.Lift.Usdc
