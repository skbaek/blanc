import Blanc.ExecutionSafeRawFramesCodes
import Blanc.Lift.Usdc.AllowLocalitySstore
import Blanc.Lift.Usdc.HistorySlotsCore
import Blanc.Lift.Usdc.Proxy.Check
import Blanc.Lift.Usdc.Lib.Check

/-!
# Raw-frame safety and code continuity at the USDC proxy

The codes that run in the proxy `P`'s storage context are the proxy runtime, the four
implementation runtimes reached through `_delegate`'s `DELEGATECALL` (V1, V2, V2_1, V2_2) and
the library V2_2 reaches by `DELEGATECALL` (`UsdcContextCode`). Each has a checked certificate
without SELFDESTRUCT terminals (`*.cert_noSelfdestruct`), so a history whose raw frames in `P`'s
context run only these codes is safe at `P` (`usdc_safeRawFrames`, through
`ConfiguredHistoryTraceIn.safeRawFrames_of_codes`), and the proxy runtime installed at the
checkpoint is the code at `P` at every raw and settled frame (`rawFrame_proxyCode`,
`settled_proxyCode`, through `rawFrames_codeImage_of_codes`).

That code fact discharges the owner-code premise of the attributed-`SSTORE` allowance classes
at the proxy (`retainedSstore_implV*_allowClass_proxy`).

The `codes` premise (which code each raw frame in `P`'s context runs) depends on the
implementation slot's values along the history and on what the admin installs there, which no
certificate decides. `ProxyContextCodes.lean` proves it from the accounts installed at their
deployment boundaries and two stated implementation-slot premises
(`usdc_safeRawFrames_of_world`, `rawFrame_proxyCode_of_world`).
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace

/-- The codes that run in the proxy's storage context along USDC's history. -/
def UsdcContextCode (C : ByteArray) : Prop :=
  C = Proxy.code ∨ C = ImplV1.code ∨ C = ImplV2.code ∨ C = ImplV2_1.code ∨ C = Impl.code ∨
    C = Lib.code

theorem Proxy.cert_noSelfdestruct : Proxy.cert.noSelfdestruct = true := by
  decide +kernel

theorem ImplV1.cert_noSelfdestruct : ImplV1.cert.noSelfdestruct = true := by
  decide +kernel

theorem ImplV2.cert_noSelfdestruct : ImplV2.cert.noSelfdestruct = true := by
  decide +kernel

theorem ImplV2_1.cert_noSelfdestruct : ImplV2_1.cert.noSelfdestruct = true := by
  decide +kernel

theorem Impl.cert_noSelfdestruct : Impl.cert.noSelfdestruct = true := by
  decide +kernel

theorem Lib.cert_noSelfdestruct : Lib.cert.noSelfdestruct = true := by
  decide +kernel

/-- The proxy runtime is no EIP-7702 delegation designator. -/
theorem Proxy.code_not_delegation : ¬ isValidDelegation Proxy.code := by
  decide +kernel

/-- Every code of the proxy's context has a checked SELFDESTRUCT-free certificate. -/
theorem usdcContextCode_certified (C : ByteArray) (h : UsdcContextCode C) :
    ∃ c : Cert, Cert.check C c = true ∧ c.noSelfdestruct = true := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, Proxy.cert_check, Proxy.cert_noSelfdestruct⟩
  · exact ⟨_, ImplV1.cert_check, ImplV1.cert_noSelfdestruct⟩
  · exact ⟨_, ImplV2.cert_check, ImplV2.cert_noSelfdestruct⟩
  · exact ⟨_, ImplV2_1.cert_check, ImplV2_1.cert_noSelfdestruct⟩
  · exact ⟨_, Impl.cert_check, Impl.cert_noSelfdestruct⟩
  · exact ⟨_, Lib.cert_check, Lib.cert_noSelfdestruct⟩

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {P : Adr} {pair : Adr} {Tr : Adr → Prop}

/-- **Raw safety at the proxy**, from the codes run in its storage context. -/
theorem usdc_safeRawFrames (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (codes : ∀ G ∈ history.rawFrames, G.sevm.currentTarget = P →
      UsdcContextCode G.sevm.code) :
    SafeRawFrames P history.rawFrames :=
  history.safeRawFrames_of_codes usdcContextCode_certified capabilities codes

/-- **The proxy runtime at every raw frame.** -/
theorem rawFrame_proxyCode (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (installed : checkpoint.state.getCode P = Proxy.code)
    (codes : ∀ G ∈ history.rawFrames, G.sevm.currentTarget = P →
      UsdcContextCode G.sevm.code) :
    ∀ R ∈ history.rawFrames, R.devm.getCode P = Proxy.code :=
  history.rawFrames_codeImage_of_codes usdcContextCode_certified Proxy.code_not_delegation
    proxy_nonempty capabilities installed codes

/-- **The proxy runtime at every settled frame.** -/
theorem settled_proxyCode (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (installed : checkpoint.state.getCode P = Proxy.code)
    (codes : ∀ G ∈ history.rawFrames, G.sevm.currentTarget = P →
      UsdcContextCode G.sevm.code) :
    ∀ f ∈ history.settledFrames, f.pre.getCode P = Proxy.code :=
  history.settled_codeImage_of_codes usdcContextCode_certified Proxy.code_not_delegation
    proxy_nonempty capabilities installed codes

/-- The owner-code premise of the attributed-write theorems at the proxy. -/
theorem rawFrame_proxyCode_ne_nil (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (installed : checkpoint.state.getCode P = Proxy.code)
    (codes : ∀ G ∈ history.rawFrames, G.sevm.currentTarget = P →
      UsdcContextCode G.sevm.code)
    (R : Exec.Deriv) (member : R ∈ history.rawFrames) :
    (R.devm.getCode P).toList ≠ [] := by
  rw [rawFrame_proxyCode history capabilities installed codes R member]
  exact proxy_nonempty

/-- **V1 at the attributed write at the proxy**: `retainedSstore_implV1_allowClass` with its
owner-code premise discharged by proxy code continuity. -/
theorem ConfiguredHistoryTraceIn.retainedSstore_implV1_allowClass_proxy
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (installed : checkpoint.state.getCode P = Proxy.code)
    (codes : ∀ G ∈ history.rawFrames, G.sevm.currentTarget = P →
      UsdcContextCode G.sevm.code)
    {R : Exec.Deriv} (member : R ∈ history.rawFrames)
    (committed : Execution.commits R.exn = true) {key : B256}
    (changed : (Devm.getStor R.devm P).get key ≠
      (Devm.getStor (Execution.committedPost R.exn committed) P).get key) :
    ∃ (write : Exec.SuccessfulSstoreOccurrence R) (frame : Exec.Frame),
      write.Retained ∧ write.storageOwner = P ∧ write.key = key ∧
      write.value = (Devm.getStor (Execution.committedPost R.exn committed) P).get key ∧
      write.IsLastRetained ∧
      frame ∈ Exec.committedFrames R.exc ∧
      Blanc.Exec.Frame.rootDeriv frame ∈ history.rawFrames ∧
      Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv frame) write.occurrence.node ∧
      frame.sevm.currentTarget = P ∧
      (frame.sevm.code = ImplV1.code →
        RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplV1Ws.implWsAnn)
          (WriteSite.Env.root frame.sevm) →
        (∃ g, Tr g ∧ allowSlot pair g = key) →
        ((selV1T.eval (WriteSite.Env.root frame.sevm) ∈ selV1.callers ∧
            frame.sevm.caller = pair) ∨
          selV1T.eval (WriteSite.Env.root frame.sevm) ∈ selV1.inits) ∨
        write.value.toNat ≤ (write.occurrence.node.devm.getStorVal P key).toNat) :=
  ConfiguredHistoryTraceIn.retainedSstore_implV1_allowClass history capabilities member committed
    (rawFrame_proxyCode_ne_nil history capabilities installed codes R member) changed

/-- **V2 at the attributed write at the proxy**: `retainedSstore_implV2_allowClass` with its
owner-code premise discharged by proxy code continuity. -/
theorem ConfiguredHistoryTraceIn.retainedSstore_implV2_allowClass_proxy
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (installed : checkpoint.state.getCode P = Proxy.code)
    (codes : ∀ G ∈ history.rawFrames, G.sevm.currentTarget = P →
      UsdcContextCode G.sevm.code)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {R : Exec.Deriv} (member : R ∈ history.rawFrames)
    (committed : Execution.commits R.exn = true) {key : B256}
    (changed : (Devm.getStor R.devm P).get key ≠
      (Devm.getStor (Execution.committedPost R.exn committed) P).get key) :
    ∃ (write : Exec.SuccessfulSstoreOccurrence R) (frame : Exec.Frame),
      write.Retained ∧ write.storageOwner = P ∧ write.key = key ∧
      write.value = (Devm.getStor (Execution.committedPost R.exn committed) P).get key ∧
      write.IsLastRetained ∧
      frame ∈ Exec.committedFrames R.exc ∧
      Blanc.Exec.Frame.rootDeriv frame ∈ history.rawFrames ∧
      Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv frame) write.occurrence.node ∧
      frame.sevm.currentTarget = P ∧
      (frame.sevm.code = ImplV2.code →
        getDelegatedCodeAddress (frame.pre.getCode 1) = none →
        RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplV2Ws.implWsAnn)
          (WriteSite.Env.root frame.sevm) →
        (∃ g, Tr g ∧ allowSlot pair g = key) →
        ((Sevm.selector frame.sevm ∈ selV2.callers ∧ frame.sevm.caller = pair) ∨
          Sevm.selector frame.sevm ∈ selV2.inits ∨
          OldUsdcNativePairAnswer (Blanc.Exec.Frame.rootDeriv frame) pair) ∨
        write.value.toNat ≤ (write.occurrence.node.devm.getStorVal P key).toNat) :=
  ConfiguredHistoryTraceIn.retainedSstore_implV2_allowClass history capabilities bal member committed
    (rawFrame_proxyCode_ne_nil history capabilities installed codes R member) changed

/-- **V2_1 at the attributed write at the proxy**: `retainedSstore_implV2_1_allowClass` with its
owner-code premise discharged by proxy code continuity. -/
theorem ConfiguredHistoryTraceIn.retainedSstore_implV2_1_allowClass_proxy
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (installed : checkpoint.state.getCode P = Proxy.code)
    (codes : ∀ G ∈ history.rawFrames, G.sevm.currentTarget = P →
      UsdcContextCode G.sevm.code)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {R : Exec.Deriv} (member : R ∈ history.rawFrames)
    (committed : Execution.commits R.exn = true) {key : B256}
    (changed : (Devm.getStor R.devm P).get key ≠
      (Devm.getStor (Execution.committedPost R.exn committed) P).get key) :
    ∃ (write : Exec.SuccessfulSstoreOccurrence R) (frame : Exec.Frame),
      write.Retained ∧ write.storageOwner = P ∧ write.key = key ∧
      write.value = (Devm.getStor (Execution.committedPost R.exn committed) P).get key ∧
      write.IsLastRetained ∧
      frame ∈ Exec.committedFrames R.exc ∧
      Blanc.Exec.Frame.rootDeriv frame ∈ history.rawFrames ∧
      Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv frame) write.occurrence.node ∧
      frame.sevm.currentTarget = P ∧
      (frame.sevm.code = ImplV2_1.code →
        getDelegatedCodeAddress (frame.pre.getCode 1) = none →
        RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplV2_1Ws.implWsAnn)
          (WriteSite.Env.root frame.sevm) →
        (∃ g, Tr g ∧ allowSlot pair g = key) →
        ((Sevm.selector frame.sevm ∈ selV2_1.callers ∧ frame.sevm.caller = pair) ∨
          Sevm.selector frame.sevm ∈ selV2_1.inits ∨
          OldUsdcNativePairAnswer (Blanc.Exec.Frame.rootDeriv frame) pair) ∨
        write.value.toNat ≤ (write.occurrence.node.devm.getStorVal P key).toNat) :=
  ConfiguredHistoryTraceIn.retainedSstore_implV2_1_allowClass history capabilities bal member committed
    (rawFrame_proxyCode_ne_nil history capabilities installed codes R member) changed

/-- **V2_2 at the attributed write at the proxy**: `retainedSstore_implV2_2_allowClass` with its
owner-code premise discharged by proxy code continuity. -/
theorem ConfiguredHistoryTraceIn.retainedSstore_implV2_2_allowClass_proxy
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (installed : checkpoint.state.getCode P = Proxy.code)
    (codes : ∀ G ∈ history.rawFrames, G.sevm.currentTarget = P →
      UsdcContextCode G.sevm.code)
    {R : Exec.Deriv} (member : R ∈ history.rawFrames)
    (committed : Execution.commits R.exn = true) {key : B256}
    (changed : (Devm.getStor R.devm P).get key ≠
      (Devm.getStor (Execution.committedPost R.exn committed) P).get key) :
    ∃ (write : Exec.SuccessfulSstoreOccurrence R) (frame : Exec.Frame),
      write.Retained ∧ write.storageOwner = P ∧ write.key = key ∧
      write.value = (Devm.getStor (Execution.committedPost R.exn committed) P).get key ∧
      write.IsLastRetained ∧
      frame ∈ Exec.committedFrames R.exc ∧
      Blanc.Exec.Frame.rootDeriv frame ∈ history.rawFrames ∧
      Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv frame) write.occurrence.node ∧
      frame.sevm.currentTarget = P ∧
      (frame.sevm.code = Impl.code →
        RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplWs.implWsAnn)
          (WriteSite.Env.root frame.sevm) →
        (∃ g, Tr g ∧ allowSlot pair g = key) →
        ((Sevm.selector frame.sevm ∈ selV2_2.callers ∧ frame.sevm.caller = pair) ∨
          Sevm.selector frame.sevm ∈ selV2_2.inits ∨
          (Sevm.selector frame.sevm ∈ selV2_2.owners ∧
            (Sevm.dataWord frame.sevm 4).toAdr = pair)) ∨
        write.value.toNat ≤ (write.occurrence.node.devm.getStorVal P key).toNat) :=
  ConfiguredHistoryTraceIn.retainedSstore_implV2_2_allowClass history capabilities member committed
    (rawFrame_proxyCode_ne_nil history capabilities installed codes R member) changed


end History

end Blanc.Lift.Usdc
