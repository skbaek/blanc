import Blanc.Lift.Usdc.ProxyWritesHistory
import Blanc.Lift.Usdc.ProxyForward
import Blanc.Lift.Usdc.Governance

/-!
# The F2′ governance rows give the admin's upgrades along an In-history

F2′ (the user-adopted post-Pair governance input; Plans `54aea9f9`,
`evidence/jaune-historical-forks-v1/wsl-usdc-h4a-20261020/proposed-contract.lean`) restricts
what the proxy's admin may send: at every proxy entry of the D→B history whose caller is the
admin word of the entry's own pre-state and whose selector is `upgradeTo`, `upgradeToAndCall`
or `changeAdmin`, the caller, the zero value and the whole calldata are one of nine exact rows
(`F2prime.adminInputShapes`). For each of V2, V2_1 and V2_2 the rows are: long-term admin to
that version's upgrader by `changeAdmin`, the upgrader to that implementation by `upgradeTo`,
and the upgrader back to the long-term admin by `changeAdmin`. There is no `upgradeToAndCall`
row and no initializer row. The row literals are copied unchanged from the proposal.

`UsdcGovernanceF2primeEntries P frames` states F2′ over the proxy entries among `frames`: the
frames at `P` running the proxy runtime. Along a history it is applied to `rawFrames`, every
frame the history enters, retained or rolled back.

`ConfiguredHistoryTraceIn.adminUpgradesWithinFrom_of_f2prime` derives the headline premise
`AdminUpgradesWithinFrom` (`ProxyWritesHistory.lean`) from F2′ and one ordering fact,
`UpgradeTargetsDeployedFirst`: each of the three implementations F2′ may install has an
account in `W`, and no successful `SSTORE` before that account's boundary stores its address
at `(P, implSlot)`. F2′ names no time, so the order of a deployment and the upgrade to it is
not a consequence of F2′; it is stated here.
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

/-- **F2′ over proxy entries (stated; user-adopted D→B governance input).** Every frame of
`frames` at `P` running the proxy runtime, whose caller is the admin word of its own pre-state
and whose selector is `upgradeTo`, `upgradeToAndCall` or `changeAdmin`, is one of the nine
rows. Non-admin callers and other selectors are unconstrained. -/
def UsdcGovernanceF2primeEntries (P : Adr) (frames : List Exec.Deriv) : Prop :=
  ∀ G ∈ frames, G.sevm.currentTarget = P → G.sevm.code = Proxy.code →
    G.sevm.caller = adminOf G.devm.state P →
    Blanc.Sevm.selector G.sevm ∈ [0x3659cfe6, 0x4f1ef286, 0x8f283970] →
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

/-- **The admin's upgrades from F2′.** Along an In-history over the deployed world, F2′ over
the history's proxy entries and the deployment-before-upgrade order of the three F2′
implementations give `AdminUpgradesWithinFrom`. -/
theorem ConfiguredHistoryTraceIn.adminUpgradesWithinFrom_of_f2prime
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    (world : UsdcDeployedWorld history.BoundaryAt P W checkpoint.state)
    (governance : UsdcGovernanceF2primeEntries P history.rawFrames)
    (deployedFirst : UpgradeTargetsDeployedFirst P W) :
    AdminUpgradesWithinFrom P W history.rawFrames history.rawNodes := by
  intro b₁ m b₂ split w found owner key G hG chain target code sel caller
  have hsevm := Exec.Deriv.ParentPrefix.sevm_eq chain
  have selMem : Blanc.Sevm.selector G.sevm ∈ [0x3659cfe6, 0x4f1ef286, 0x8f283970] := by
    rcases sel with h | h
    · rw [dispatchWord_eq_selector] at h
      rw [h]
      decide
    · rw [dispatchWord_eq_selector] at h
      rw [h]
      decide
  have allowed := governance G hG target code caller selMem
  obtain ⟨impl, implMem, hImpl⟩ := AllowedAdminAsk.upgradeArg allowed sel
  -- The written value is `G`'s upgrade argument.
  have hm : m ∈ history.rawNodes := by
    rw [split]; exact List.mem_append_right _ List.mem_cons_self
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
