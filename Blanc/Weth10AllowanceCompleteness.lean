import Blanc.Weth10Attribution
import Blanc.Weth10HolderFlowWriteCompleteness

/-!
Allowance-region access completeness for the compiled WETH10 runtime.

This module states the H2 obligations of `weth10-redeem-future-v2`: every
committed `SSTORE` and `SLOAD` whose executed key lies in the tagged
allowance region, inside an authentic exact WETH10 frame at any EVM-admitted
depth, is the frame's single classified allowance visit — the
`approve`/`approveAndCall` store, the store behind `permitRecover`'s
recovered-signer equality, the finite-allowance decrement shared by
`transferFrom`/`withdrawFrom`, `flashSettle`'s post-callback arms, or the
`allowance` view's read — with the exact raw owner/spender words recorded by
`frameAllowanceEvent`.

The occurrence definitions mirror `Exec.Frame.BalanceSstoreOccurrence`: the
machine states, recursive slot, executed key, and moved word are indices into
the retained `Exec` derivation, so classification cannot be replaced by an
endpoint storage comparison.  Region membership is the executed key's tag
bits, so foreign lookalike slots and non-allowance regions cannot masquerade
as allowance activity, and the authentic-context premise excludes
delegatecall-as-library execution exactly as in the balance development.
-/

namespace Blanc

open Jaune

namespace Weth10

/-- An actual proof-indexed `SSTORE` whose executed key is in the tagged
allowance region. -/
def Exec.Frame.AllowanceSstoreOccurrence
    (dp : DeployParams) (ca : Adr) (frame : Exec.Frame)
    (stepPre stepPost : Devm) (slot : Xlot)
    (key value : B256) : Prop :=
  frame.NinstOccurrence dp ca (.reg .sstore) stepPre stepPost slot ∧
    InRegion .allowance key ∧
    ∃ tail : Stack, key :: value :: tail <<+ stepPre.stack

/-- An actual proof-indexed `SLOAD` whose executed key is in the tagged
allowance region; `value` is the word the load pushed. -/
def Exec.Frame.AllowanceSloadOccurrence
    (dp : DeployParams) (ca : Adr) (frame : Exec.Frame)
    (stepPre stepPost : Devm) (slot : Xlot)
    (key value : B256) : Prop :=
  frame.NinstOccurrence dp ca (.reg .sload) stepPre stepPost slot ∧
    InRegion .allowance key ∧
    ∃ tail : Stack,
      key :: tail <<+ stepPre.stack ∧ value :: tail <<+ stepPost.stack

/-- An allowance-region write is classified when the enclosing frame's
single allowance visit writes exactly this key and word. -/
def Exec.Frame.AllowanceSstoreClassification
    (_dp : DeployParams) (_ca : Adr) (frame : Exec.Frame)
    (key value : B256) (event : AllowanceEvent) : Prop :=
  frameAllowanceEvent frame.sevm frame.pre frame.post = some event ∧
    event.key = key ∧
    event.visit.written? = some value

/-- An allowance-region read is classified when the enclosing frame's single
allowance visit reads exactly this key and word. -/
def Exec.Frame.AllowanceSloadClassification
    (_dp : DeployParams) (_ca : Adr) (frame : Exec.Frame)
    (key value : B256) (event : AllowanceEvent) : Prop :=
  frameAllowanceEvent frame.sevm frame.pre frame.post = some event ∧
    event.key = key ∧
    event.visit.read? = some value

/-- The local compiled-program write obligation: every actual
allowance-region `SSTORE` occurrence in an authentic exact WETH10 frame is
the frame's classified allowance visit. -/
def CompiledAllowanceSstoreReverseComplete
    (dp : DeployParams) (ca : Adr) : Prop :=
  ∀ (frame : Exec.Frame), frame.AuthenticContext dp ca →
    ∀ (stepPre stepPost : Devm) (slot : Xlot) (key value : B256),
      frame.AllowanceSstoreOccurrence dp ca stepPre stepPost slot
        key value →
      ∃ event : AllowanceEvent,
        frame.AllowanceSstoreClassification dp ca key value event

/-- The local compiled-program read obligation: every actual
allowance-region `SLOAD` occurrence in an authentic exact WETH10 frame is
the frame's classified allowance visit. -/
def CompiledAllowanceSloadReverseComplete
    (dp : DeployParams) (ca : Adr) : Prop :=
  ∀ (frame : Exec.Frame), frame.AuthenticContext dp ca →
    ∀ (stepPre stepPost : Devm) (slot : Xlot) (key value : B256),
      frame.AllowanceSloadOccurrence dp ca stepPre stepPost slot
        key value →
      ∃ event : AllowanceEvent,
        frame.AllowanceSloadClassification dp ca key value event

end Weth10

end Blanc
