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

/-- Check the actual raw chronology, including writes in subsequently reverted
frames. A matching proxy implementation-slot write must name an entry whose
original boundary prefix ends no later than this write. Prefix identity is
supplied separately by the history's boundary proof, never inferred from length.
No governance row, timestamp guess, or receipt filter changes the population. -/
def checkUpgradesWithinFrom (P : Adr) (W : List UsdcDeployedEntry)
    (nodes : List Exec.Deriv) : Bool :=
  nodes.zipIdx.all fun (m, position) =>
    if m.sevm.currentTarget = P ∧ m.sevm.code = Proxy.code then
      match Exec.Deriv.successfulSstore? m with
      | none => true
      | some w => if w.key = implSlot then
          W.any fun e => decide (e.pre.length ≤ position ∧ w.value.toAdr = e.adr)
        else true
    else true

/-- The executable raw-position check supplies the existing upgrade premise.
Every listed prefix must belong to this same chronology; equal lengths alone
are insufficient. The history adapter below obtains this from actual boundaries. -/
theorem upgradesWithinFrom_of_check {P : Adr} {W : List UsdcDeployedEntry}
    {nodes : List Exec.Deriv}
    (prefixes : ∀ e ∈ W, e.pre.IsPrefix nodes)
    (checked : checkUpgradesWithinFrom P W nodes = true) :
    UpgradesWithinFrom P W nodes := by
  intro before m after split target code w found key
  have member : (m, before.length) ∈ nodes.zipIdx := by
    apply List.mk_mem_zipIdx_iff_getElem?.mpr
    rw [split, List.getElem?_append_right (Nat.le_refl _)]
    simp only [Nat.sub_self, List.getElem?_cons_zero]
  have row := List.all_eq_true.mp checked (m, before.length) member
  simp only [target, code, and_self, ite_true, found, key] at row
  obtain ⟨e, inWorld, ready⟩ := List.any_eq_true.mp row
  have facts := of_decide_eq_true ready
  obtain ⟨rest, eq⟩ := List.prefix_of_prefix_length_le (prefixes e inWorld)
    (show before.IsPrefix nodes from ⟨m :: after, split.symm⟩) facts.1
  exact ⟨e, inWorld, ⟨rest, eq.symm⟩, facts.2⟩

/-- Every positional upgrade witness passes the check. Thus, with original
boundary prefixes, the check is equivalent to the consumed premise rather than
a stronger governance or no-upgrade restriction. -/
theorem checkUpgradesWithinFrom_of_upgrades {P : Adr} {W : List UsdcDeployedEntry}
    {nodes : List Exec.Deriv} (upgrades : UpgradesWithinFrom P W nodes) :
    checkUpgradesWithinFrom P W nodes = true := by
  apply List.all_eq_true.mpr
  rintro ⟨m, position⟩ member
  dsimp only
  by_cases relevant : m.sevm.currentTarget = P ∧ m.sevm.code = Proxy.code
  · simp only [relevant, and_self, ite_true]
    cases found : Exec.Deriv.successfulSstore? m with
    | none => rfl
    | some w =>
      by_cases key : w.key = implSlot
      · simp only [key, ite_true]
        obtain ⟨lt, atNode⟩ := List.getElem?_eq_some_iff.mp
          (List.mk_mem_zipIdx_iff_getElem?.mp member)
        have split : nodes = nodes.take position ++ m :: nodes.drop (position + 1) := by
          conv_lhs => rw [← List.take_append_drop position nodes]
          rw [List.drop_eq_getElem_cons lt, atNode]
        obtain ⟨e, inWorld, ⟨rest, active⟩, address⟩ := upgrades _ _ _ split
          relevant.1 relevant.2 w found key
        apply List.any_eq_true.mpr
        refine ⟨e, inWorld, decide_eq_true ?_⟩
        refine ⟨?_, address⟩
        have lengths := congrArg List.length active
        simp only [List.length_take, List.length_append] at lengths
        omega
      · simp only [key, ite_false]
  · simp only [relevant, ite_false]

/-- Bind the finite upgrade check to the existing deployed world's original
committed boundaries. Check truth and installed code remain explicit inputs. -/
theorem ConfiguredHistoryTraceIn.upgradesWithinFrom_of_check
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (world : UsdcDeployedWorld history.BoundaryAt P W checkpoint.state)
    (checked : checkUpgradesWithinFrom P W history.rawNodes = true) :
    UpgradesWithinFrom P W history.rawNodes := by
  apply Blanc.Lift.Usdc.upgradesWithinFrom_of_check (checked := checked)
  intro e member
  obtain ⟨rest, eq⟩ := ConfiguredHistoryTraceIn.BoundaryAt.prefix (world.boundary e member)
  exact ⟨rest, eq.symm⟩

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
