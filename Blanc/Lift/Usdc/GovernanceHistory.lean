import Blanc.Lift.Usdc.ProxyWritesHistory
import Blanc.Lift.Usdc.ProxyForward
import Blanc.Lift.Usdc.Governance

/-!
# Retained F2′ governance and a separate raw upgrade obligation

The user-adopted D→B governance input (Plans `54aea9f9`,
`evidence/jaune-historical-forks-v1/wsl-usdc-h4a-20261020/proposed-contract.lean`)
quantifies the actual settlement-retained entries. `UsdcGovernanceF2primeOn`
preserves that predicate: an entry whose caller is its pre-state admin and
whose selector is `upgradeTo`, `upgradeToAndCall` or `changeAdmin` must match
one of nine exact actor/value/calldata rows. Historical consumers must pass
`history.settledFrames`. There is no `upgradeToAndCall` or initializer row;
other selectors remain unconstrained. No time, order or occurrence is asserted.

`UsdcGovernanceF2primeAtImplWrites` is a separate conditional obligation over
caller-supplied derivation lists. The existing raw-history theorem applies it
to `rawFrames` and `rawNodes`, including rolled-back implementation writes.
That raw instance is NOT implied by the adopted retained-frame predicate.
The names and signatures are retained for compatibility; neither this theorem
nor the executable raw upgrade checker establishes the missing raw premise.

`ConfiguredHistoryTraceIn.adminUpgradesWithinFrom_of_f2prime` derives
`AdminUpgradesWithinFrom` from that explicit raw obligation and the additional
`UpgradeTargetsDeployedFirst` condition. F2′ supplies neither deployment order
nor installation at a chosen earlier boundary. The proxy's `isContract` guard
only establishes code at the upgrade, not at an earlier committed boundary;
a transaction may create an implementation and then upgrade to it.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

namespace F2prime

def longTermAdmin : Adr := 0x807a96288a1a408dbc13de2b1d087d10356395d2
def upgraderV2 : Adr := 0xed24bd79a3f2ba4325e9c553164e299c65e272fc
def upgraderV2_1 : Adr := 0xd13689e8da0ed95b55100e27b7dbc95c03b5259b
def upgraderV2_2 : Adr := 0x9999fa87f5a1d1c64e7c709838b92006ab0cc1ad
def implementationV2 : Adr := 0xb7277a6e95992041568d9391d09d0122023778a2
def implementationV2_1 : Adr := 0xa2327a938febf5fec13bacfb16ae10ecbc4cbdcf
def implementationV2_2 : Adr := 0x43506849d7c04f9138d1a2050bbf3a0c054402dd

/-- Actor, selector, address argument: the nine F2′ shapes. -/
def adminInputShapes : List (Adr × B256 × Adr) :=
  [ (longTermAdmin, 0x8f283970, upgraderV2),
    (upgraderV2, 0x3659cfe6, implementationV2),
    (upgraderV2, 0x8f283970, longTermAdmin),
    (longTermAdmin, 0x8f283970, upgraderV2_1),
    (upgraderV2_1, 0x3659cfe6, implementationV2_1),
    (upgraderV2_1, 0x8f283970, longTermAdmin),
    (longTermAdmin, 0x8f283970, upgraderV2_2),
    (upgraderV2_2, 0x3659cfe6, implementationV2_2),
    (upgraderV2_2, 0x8f283970, longTermAdmin) ]

/-- Four selector bytes followed by exactly one canonical 32-byte ABI address word. -/
def adminCallData (selector : B256) (argument : Adr) : Bytes :=
  selector.toBytes.drop 28 ++ argument.toB256.toBytes

/-- A message that is one of the nine rows: its caller, zero value and entire calldata. -/
def AllowedAdminAsk (s : Sevm) : Prop :=
  ∃ actor selector argument,
    (actor, selector, argument) ∈ adminInputShapes ∧
    s.caller = actor ∧ s.value = 0 ∧ s.data = adminCallData selector argument

/-- The implementations an F2′ `upgradeTo` row installs. -/
def upgradeTargets : List Adr := [implementationV2, implementationV2_1, implementationV2_2]

/-- Decoding the nine rows: each has the selector of its literal, so none is
`upgradeToAndCall`, and an `upgradeTo` row's masked address word names one of the three
implementations. -/
theorem rows_decoded : ∀ r ∈ adminInputShapes,
    Bytes.toB256 ((adminCallData r.2.1 r.2.2).sliceD 0 32 0) >>> 224 = r.2.1 ∧
      r.2.1 ≠ 0x4f1ef286 ∧ (r.2.1 = 0x8f283970 ∨ r.2.1 = 0x3659cfe6) ∧
      (r.2.1 = 0x3659cfe6 →
        r.2.2 ∈ upgradeTargets ∧
        (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
          Bytes.toB256 ((adminCallData r.2.1 r.2.2).sliceD 4 32 0)).toAdr = r.2.2) := by
  decide +kernel

end F2prime

open F2prime

/-- The adopted F2′ predicate over actual settlement-retained frames. Historical
consumers pass the original D→B history's `settledFrames`, never raw frames or
a selected subset. Nonadmin calls and other selectors are unconstrained. -/
def UsdcGovernanceF2primeOn (P : Adr) (frames : List Exec.Frame) : Prop :=
  ∀ G ∈ frames, Blanc.Lift.Token.IsEntry P G →
    G.sevm.caller = adminOf G.pre.state P →
    Blanc.Sevm.selector G.sevm ∈ [0x3659cfe6, 0x4f1ef286, 0x8f283970] →
    AllowedAdminAsk G.sevm

/-- A separate implementation-write obligation over derivation lists. At each
successful implementation-slot write, a proxy parent frame with its entry
admin as caller and an upgrade selector must match an allowed row. When used
with raw history lists this also restricts discarded subtrees, and is not a
consequence of the adopted retained F2′ predicate. -/
def UsdcGovernanceF2primeAtImplWrites (P : Adr) (frames nodes : List Exec.Deriv) : Prop :=
  ∀ m ∈ nodes, ∀ w : Exec.StorageWrite, Exec.Deriv.successfulSstore? m = some w →
    w.owner = P → w.key = implSlot →
    ∀ G ∈ frames, Exec.Deriv.ParentPrefix G m →
    G.sevm.currentTarget = P → G.sevm.code = Proxy.code →
    G.sevm.caller = adminOf G.devm.state P →
    Blanc.Sevm.selector G.sevm ∈ [0x3659cfe6, 0x4f1ef286] →
    AllowedAdminAsk G.sevm

/-- **Each F2′ upgrade target is deployed before it is installed (stated).** For each
implementation an F2′ `upgradeTo` row names, `W` lists an account at that address, and no
successful `SSTORE` among the raw nodes before that account's boundary stores that address at
`(P, implSlot)`. -/
def UpgradeTargetsDeployedFirst (P : Adr) (W : List UsdcDeployedEntry) : Prop :=
  ∀ impl ∈ upgradeTargets, ∃ e ∈ W, e.adr = impl ∧
    ∀ m ∈ e.pre, ∀ w : Exec.StorageWrite, Exec.Deriv.successfulSstore? m = some w →
      w.owner = P → w.key = implSlot → w.value.toAdr ≠ impl

/-- An allowed row whose dispatch word is an upgrade selector is an `upgradeTo` row: its
upgrade argument names one of the three implementations. -/
theorem AllowedAdminAsk.upgradeArg {s : Sevm} (allowed : AllowedAdminAsk s)
    (sel : Proxy.dispatchWord s = Proxy.upgradeToWord ∨
      Proxy.dispatchWord s = Proxy.upgradeToAndCallWord) :
    ∃ impl ∈ upgradeTargets, (Proxy.upgradeArg s).toAdr = impl := by
  obtain ⟨actor, selector, argument, mem, -, -, data⟩ := allowed
  obtain ⟨hsel, notCall, -, upgrade⟩ := rows_decoded _ mem
  dsimp only at hsel notCall upgrade
  have hselector : Blanc.Sevm.selector s = selector := by
    unfold Blanc.Sevm.selector Blanc.Sevm.dataWord
    rw [data]
    exact hsel
  have isUpgrade : selector = 0x3659cfe6 := by
    rcases sel with h | h
    · rw [dispatchWord_eq_selector, hselector] at h
      rw [h]
      decide
    · rw [dispatchWord_eq_selector, hselector] at h
      exact absurd (h.trans (by decide)) notCall
  obtain ⟨target, arg⟩ := upgrade isUpgrade
  have harg : (Proxy.upgradeArg s).toAdr = argument := by
    unfold Proxy.upgradeArg Blanc.Sevm.dataWord
    rw [data]
    exact arg
  exact ⟨argument, target, harg⟩

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {P : Adr} {W : List UsdcDeployedEntry}

/-- Approved retained-frame F2′ classifies the value of an actual retained
proxy implementation write. The parent is the original committed frame, so
its entry state supplies the admin tested by the proxy; discarded frames need
no governance premise. The node's actual code-address provenance is explicit. -/
theorem ConfiguredHistoryTraceIn.retained_proxyUpgrade_target_of_f2prime_with_code
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    (governance : UsdcGovernanceF2primeOn P history.settledFrames)
    {R : Exec.Frame} (member : R ∈ history.settledRoots)
    {N : Exec.Deriv} (retained : N ∈ Exec.retainedNodes R.run)
    (target : N.sevm.currentTarget = P) (code : N.sevm.code = Proxy.code)
    (address : N.sevm.codeAddress = some P)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? N = some write)
    (key : write.key = implSlot) :
    write.value.toAdr ∈ upgradeTargets ∧
      (N.devm.getCode write.value.toAdr).toList ≠ [] := by
  obtain ⟨G, frameMem, chain⟩ :=
    (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix R.run N).mp retained
  have settled : G ∈ history.settledFrames := by
    rw [history.settledFrames_eq]
    exact List.mem_flatMap.mpr ⟨R, member, frameMem⟩
  have sameSevm := Exec.Deriv.ParentPrefix.sevm_eq chain
  change N.sevm = G.sevm at sameSevm
  have entry : Blanc.Lift.Token.IsEntry P G := by
    constructor
    · rw [← sameSevm]; exact target
    · rw [← sameSevm]; exact address
  have frameCode : G.sevm.code = Proxy.code := by rw [← sameSevm]; exact code
  obtain ⟨pcZero, forkIn, hsg, _, _⟩ := history.rawFrame_entryFacts capabilities
    (Exec.Frame.rootDeriv G) (history.mem_rawFrames_of_mem_settledFrames G settled)
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  have classified : (∃ rest, N.devm.stack = adminSlot :: rest) ∨
      ∃ rest, N.devm.stack = implSlot :: Proxy.upgradeArg G.sevm :: rest ∧
        (Proxy.dispatchWord G.sevm = Proxy.upgradeToWord ∨
          Proxy.dispatchWord G.sevm = Proxy.upgradeToAndCallWord) ∧
        G.sevm.caller = (G.pre.getStorVal G.sevm.currentTarget adminSlot).toAdr ∧
        (N.devm.getCode (Proxy.upgradeArg G.sevm).toAdr).toList ≠ [] := by
    rcases G with ⟨pc, sevm, pre, out, run, committed⟩
    dsimp only [Exec.Frame.rootDeriv] at pcZero chain
    subst pc
    exact Proxy.proxy_sstoreNodeH_with_code run frameCode hsg (bal forkIn) chain decoded
  rcases classified with ⟨_, admin⟩ | ⟨_, impl, selector, caller, nonempty⟩
  · have sameKey := (List.cons.inj (stack.symm.trans admin)).1
    rw [key] at sameKey
    exact absurd sameKey (by decide)
  · have value := (List.cons.inj (List.cons.inj (stack.symm.trans impl)).2).1
    have admin : G.sevm.caller = adminOf G.pre.state P := by
      rw [entry.1] at caller
      exact caller
    have selMem : Blanc.Sevm.selector G.sevm ∈ [0x3659cfe6, 0x4f1ef286, 0x8f283970] := by
      rcases selector with h | h
      · rw [dispatchWord_eq_selector] at h
        rw [h]
        decide
      · rw [dispatchWord_eq_selector] at h
        rw [h]
        decide
    obtain ⟨impl, inTargets, arg⟩ :=
      AllowedAdminAsk.upgradeArg (governance G settled entry admin selMem) selector
    refine ⟨?_, ?_⟩
    · rw [value, arg]
      exact inTargets
    · rw [value]
      exact nonempty

/-- Target-only compatibility projection of the retained upgrade theorem.
The stronger result also retains the target code observed at the write. -/
theorem ConfiguredHistoryTraceIn.retained_proxyUpgrade_target_of_f2prime
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    (governance : UsdcGovernanceF2primeOn P history.settledFrames)
    {R : Exec.Frame} (member : R ∈ history.settledRoots)
    {N : Exec.Deriv} (retained : N ∈ Exec.retainedNodes R.run)
    (target : N.sevm.currentTarget = P) (code : N.sevm.code = Proxy.code)
    (address : N.sevm.codeAddress = some P)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? N = some write)
    (key : write.key = implSlot) : write.value.toAdr ∈ upgradeTargets := by
  exact (ConfiguredHistoryTraceIn.retained_proxyUpgrade_target_of_f2prime_with_code
    history capabilities bal governance member retained target code address found key).1

/-- Conditional raw upgrade classification from the explicit raw governance
obligation and deployment-before-upgrade ordering. The theorem name is kept
for compatibility; approved retained-frame F2′ alone does not supply its
`governance` argument. -/
theorem ConfiguredHistoryTraceIn.adminUpgradesWithinFrom_of_f2prime
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    (world : UsdcDeployedWorld history.BoundaryAt P W checkpoint.state)
    (governance : UsdcGovernanceF2primeAtImplWrites P history.rawFrames history.rawNodes)
    (deployedFirst : UpgradeTargetsDeployedFirst P W) :
    AdminUpgradesWithinFrom P W history.rawFrames history.rawNodes := by
  intro b₁ m b₂ split w found owner key G hG chain target code sel caller
  have hsevm := Exec.Deriv.ParentPrefix.sevm_eq chain
  have hm : m ∈ history.rawNodes := by
    rw [split]; exact List.mem_append_right _ List.mem_cons_self
  have selMem : Blanc.Sevm.selector G.sevm ∈ [0x3659cfe6, 0x4f1ef286] := by
    rcases sel with h | h
    · rw [dispatchWord_eq_selector] at h
      rw [h]
      decide
    · rw [dispatchWord_eq_selector] at h
      rw [h]
      decide
  have allowed := governance m hm w found owner key G hG chain target code caller selMem
  obtain ⟨impl, implMem, hImpl⟩ := AllowedAdminAsk.upgradeArg allowed sel
  -- The written value is `G`'s upgrade argument.
  have mTarget : m.sevm.currentTarget = P := by rw [hsevm]; exact target
  have mCode : m.sevm.code = Proxy.code := by rw [hsevm]; exact code
  obtain ⟨G', -, chain', -, -, cls⟩ :=
    ConfiguredHistoryTraceIn.proxy_rawWrite history capabilities bal hm mTarget mCode found
  have value : w.value.toAdr = impl := by
    rcases cls with adminKey | ⟨-, hv, -, -⟩
    · exact absurd (adminKey.symm.trans key) (by decide)
    · rw [hv, ← Exec.Deriv.ParentPrefix.sevm_eq chain', hsevm]
      exact hImpl
  obtain ⟨e, he, adr, noWrite⟩ := deployedFirst impl implMem
  refine ⟨e, he, ?_, by rw [hImpl, adr]⟩
  obtain ⟨rest, hnodes⟩ := ConfiguredHistoryTraceIn.BoundaryAt.prefix (world.boundary e he)
  rw [split] at hnodes
  rcases List.append_eq_append_iff.mp hnodes.symm with ⟨a', hb, -⟩ | ⟨c', hpre, hd⟩
  · exact ⟨a', hb⟩
  · cases c' with
    | nil => exact ⟨[], by rw [hpre, List.append_nil, List.append_nil]⟩
    | cons x c'' =>
        have hx : m = x := (List.cons.inj hd).1
        have mPre : m ∈ e.pre := by
          rw [hpre, hx]; exact List.mem_append_right _ List.mem_cons_self
        exact absurd value (noWrite m mPre w found owner key)

end History

end Blanc.Lift.Usdc
