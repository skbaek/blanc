import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame2

/-!
V- witness, frame 0: the top-level message call `P.remove_liquidity(200, [0, 0], A)` from
caller `A`, value 0, 30,000,000 gas, Prague, from the explicit pre-state `world0` (Plans
`reports/vminus-preflight-v1.md` section 2), entered the way Jaune's `Frame.enter` enters
a message call (EELS `process_message_call` on a hand-built `Message`, as the preflight
ran it: empty accessed sets, `should_transfer_value` set).

The proxy `P` (45 bytes) runs eleven childless steps to its `DELEGATECALL` at pc 31
(`prefix0`), whose spawn is computed on the shadows (`dcallPrep`).  The frame it spawns
enters with exactly frame 1's machine `⟨0, sevm1, pre1⟩` (`e1_eq`): frame 1 is re-rooted at
its real spawn with no change to any downstream literal.  The resume, the ten-step tail and
the `RETURN` are kernel checks over a free child with frame 1's gas and output
(`childObs`), so frame 1 is not re-run.

Kernel only (every theorem here is a closed evaluation); the proofs that use them live in
`Top`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Top

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree

/-! ### The top-level message -/

/-- The block environment: Prague, the pre-state as the transaction's original state, every
other field Jaune's default (chain id 0, block number 0, timestamp 0, zero fees). -/
def benvStat0 : BenvStat := { (default : BenvStat) with origState := world0 }

/-- **The top-level message call**: `A` calls `P` with `remove_liquidity(200, [0, 0], A)`,
value 0, 30,000,000 gas, at Jaune depth 1024 (EELS depth 0), with empty accessed sets, over
the pre-state `world0`. -/
def msg0 : Msg where
  benv := ⟨world0, .emptyWithCapacity, benvStat0⟩
  tenv := default
  caller := attackerAddress
  target := some proxyAddress
  currentTarget := proxyAddress
  gas := 30000000
  value := 0
  data := removeCalldata
  codeAddress := some proxyAddress
  code := proxyCode
  depth := 1024
  shouldTransferValue := true
  isStatic := false
  accessedAddresses := .emptyWithCapacity
  accessedStorageKeys := .emptyWithCapacity
  disablePrecompiles := false

/-- The top-level frame. -/
def f0 : Frame := Frame.ofCall msg0

/-- The account shadow after the (zero) value transfer of the top-level message. -/
def acs00 : AcctShadow := acsTransfer msg0 acs0

/-- The machine the top-level frame enters with. -/
def e0 : Evm := match frameEnterS f0 acs0 with | .run e => e | .done _ => default

theorem e0_eq : frameEnterS f0 acs0 = .run e0 := by kernel_rfl

/-! ### Frame 0: the proxy up to its `DELEGATECALL` -/

/-- The proxy at its `DELEGATECALL` (pc 31): the calldata copied to memory, the seven call
words on the stack, 54 gas burned. -/
def e0_31 : Evm :=
  ⟨31, e0.sta, e0.dyna.setMach
    ⟨[(29999946 : Nat).toB256, implementationAddress.toB256, 0, (132 : Nat).toB256, 0, 0, 0],
      Mem.empty.write 0 e0.sta.data, 29999946, e0.dyna.stateGas⟩⟩

theorem prefix0 : stepN 11 e0 = some e0_31 := by kernel_rfl

/-- The proxy's `DELEGATECALL` up to its spawn (nothing is warm: the address shadow is
empty). -/
def cp1 : CallPrep := (dcallPrep e0_31.sta e0_31.dyna [] acs00).getD noPrep

theorem cp1_eq : dcallPrep e0_31.sta e0_31.dyna [] acs00 = some cp1 := by kernel_rfl

/-- **Frame 1 at its real spawn.**  The frame the proxy's `DELEGATECALL` spawns enters with
exactly frame 1's machine: `sevm1` (caller `A`, storage owner `P`, the implementation's
code, the calldata, gas 29,528,638, depth 1023) and `pre1` (the world `world0`, the
implementation warm). -/
theorem e1_eq : frameEnterS cp1.f acs00 = .run ⟨0, sevm1, pre1⟩ := by kernel_rfl

/-! ### Frame 0 after its child -/

/-- The proxy resumed from a settled child `d`. -/
def d02 (d : Devm) : Devm := (resumeCallB cp1.p cp1.oi cp1.os (.ok d)).getD default

/-- The proxy at its `RETURN` (pc 44). -/
def e0_44 (d : Devm) : Evm := (stepN 10 ⟨32, e0.sta, d02 d⟩).getD default

/-- The proxy's halted machine. -/
def post0F (d : Devm) : Devm :=
  match Evm.step (e0_44 d) with
  | .halt (.ok d') => d'
  | _ => default

/-- Frame 1's settled machine as the proxy's child, its observed parts as literals. -/
abbrev obsChild1 (d : Devm) : Devm := childObs 29372882 (word 100 ++ word 100) d

theorem resume0_eq : ∀ d : Devm,
    resumeCallB cp1.p cp1.oi cp1.os (.ok (obsChild1 d)) = some (d02 (obsChild1 d)) := by
  kernel_forall_rfl

theorem tail0_eq : ∀ d : Devm,
    stepN 10 ⟨32, e0.sta, d02 (obsChild1 d)⟩ = some (e0_44 (obsChild1 d)) := by
  kernel_forall_rfl

theorem return0_eq : ∀ d : Devm,
    Evm.step (e0_44 (obsChild1 d)) = .halt (.ok (post0F (obsChild1 d))) := by
  kernel_forall_rfl

/-- The top-level frame's gas at its `RETURN` (the EELS trace: 29,841,551), its return data
(the child's) and its success. -/
theorem post0_obs : ∀ d : Devm,
    ((post0F (obsChild1 d)).gasLeft, (post0F (obsChild1 d)).output.map UInt8.toNat,
      (post0F (obsChild1 d)).error.isNone) =
    (29841551, (word 100 ++ word 100).map UInt8.toNat, true) := by
  kernel_forall_rfl

theorem post0_keep : ∀ d : Devm, (post0F (obsChild1 d)).state = (d02 (obsChild1 d)).state := by
  kernel_forall_rfl

/-- Static facts of the top-level frame's machine and the spawn (closed evaluations). -/
theorem e0_facts : (e0.pc, e0.sta.code, e0.sta.data, e0.sta.benvStat.fork) =
    (0, proxyCode, removeCalldata, .prague) := by kernel_rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Top
