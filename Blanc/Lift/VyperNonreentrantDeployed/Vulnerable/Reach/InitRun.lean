import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.InitSetup
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Check
import Blanc.Lift.WitnessSpawn

/-!
# V− setup, message 3: the kernel run of `initialize` through the proxy

Prague kernel decisions (closed evaluations; do not open this file in the language server).
The frames of message 3, outermost first:

* the forwarder `fwdCode` at `proxyAddr`: 11 steps to its `DELEGATECALL` (pc 31), which spawns
  the implementation frame; after it, 10 steps and `RETURN` (pc 44);
* the implementation frame (storage owner `proxyAddr`, code `Vulnerable.code`, calldata
  `initCall`): 663 steps of the registered 0x6326 certificate (`wrun`) from its entry to its
  `STOP`. Its four `CALL`s of the identity precompile (address 4, the string concatenations of
  `name` and `symbol`) are run by the interpreter (`callStep`).

`runI` is the observation of the implementation frame's halt: its gas, empty output, success,
its single log, and its final storage and account shadows. The storage shadow is the twelve
writes of `initWrites` (newest first) over the start shadow `stor2`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable (cert t_0000_c0)

/-- The account shadow after message 3's (zero) value transfer. -/
def acs3 : AcctShadow := acsTransfer msg3 acs2

/-- The forwarder at its `DELEGATECALL` (pc 31). -/
def e3_31 : Evm := (stepN 11 e3).getD default

/-- An unused default preparation. -/
def noPrepI : CallPrep := ⟨Frame.ofCall default, default, 0, 0, []⟩

/-- The forwarder's `DELEGATECALL` up to its spawn. -/
def cpI : CallPrep := (dcallPrep e3_31.sta e3_31.dyna [] acs3).getD noPrepI

/-- The implementation frame's entry machine. -/
def eI : Evm := match frameEnterS cpI.f acs3 with | .run e => e | .done _ => default

/-- The implementation frame's program: the registered certificate's. -/
abbrev fsI : List SFunc := Cert.prog cert

/-- The implementation frame's start configuration. -/
def cI0 : Cfg := ⟨eI.dyna, t_0000_c0, [], [], cpI.adrs, stor2, acsTransfer cpI.f.inner acs3⟩

/-- The storage `initialize` writes at the proxy, newest first: `symbol` ("-f", length 2 at slot
21, data at 22), `name` ("Curve.fi Factory Pool: ", length 23 at slot 17, data at 18),
`factory` (5) `:= creator`, `fee` (10) `:= 0`, `future_A` (12) and `initial_A` (11) `:= 10000`,
`rate_multipliers[1]` (16), `coins[1]` (7) `:= tokenAddr`, `rate_multipliers[0]` (15),
`coins[0]` (6) `:= ethCoin`. -/
def initWrites : StorShadow :=
  [((proxyAddr, 22), 20534296586854382678417119990996247571837989427425521718122903977259886968832),
   ((proxyAddr, 21), 2),
   ((proxyAddr, 18), 30512471952670789164122273054066300063710012785238889216544515826871133274112),
   ((proxyAddr, 17), 23),
   ((proxyAddr, 5), creator.toNat.toB256),
   ((proxyAddr, 10), 0),
   ((proxyAddr, 12), 10000),
   ((proxyAddr, 11), 10000),
   ((proxyAddr, 16), 1000000000000000000),
   ((proxyAddr, 7), tokenAddr.toNat.toB256),
   ((proxyAddr, 15), 1000000000000000000),
   ((proxyAddr, 6), ethCoin.toNat.toB256)]

/-- The account entries the implementation frame's four precompile `CALL`s prepend (the
identity precompile and the proxy, each restating its view). -/
def precompAcs : AcctShadow :=
  [((4 : Adr), ⟨0, 0, .empty, .empty⟩), (proxyAddr, ⟨1, 0, .empty, fwdCode⟩),
   ((4 : Adr), ⟨0, 0, .empty, .empty⟩), (proxyAddr, ⟨1, 0, .empty, fwdCode⟩),
   ((4 : Adr), ⟨0, 0, .empty, .empty⟩), (proxyAddr, ⟨1, 0, .empty, fwdCode⟩),
   ((4 : Adr), ⟨0, 0, .empty, .empty⟩), (proxyAddr, ⟨1, 0, .empty, fwdCode⟩)]

/-- What the implementation frame's halt shows: gas, output, success, its log count, and the
final storage and account shadows. -/
def obsI : Res → Option (Nat × List Nat × Bool × Nat × StorShadow × AcctShadow)
  | .done (.halted d) cl =>
    some (d.gasLeft, d.output.map UInt8.toNat, d.error.isNone, d.logs.length, cl.stor, cl.acs)
  | _ => none

/-- **The implementation frame, run.** 663 steps from its entry to its `STOP`: 729,444 gas
left, no output, no error, one log (`Transfer(0, proxy, 0)`), the twelve writes at the proxy
over the start storage, and no account changed. -/
theorem runI :
    obsI (wrun fsI eI.sta 663 cI0) =
      some (729444, [], true, 1, initWrites ++ stor2, precompAcs ++ acs3) := by
  kernel_rfl

/-- The implementation frame's settled machine, as its parent sees it. -/
abbrev obsChildI (d : Devm) : Devm := childObs 729444 [] d

/-- The forwarder resumed from its settled child. -/
def dP2 (d : Devm) : Devm := (resumeCallB cpI.p cpI.oi cpI.os (.ok d)).getD default

/-- The forwarder at its `RETURN` (pc 44). -/
def e3_44 (d : Devm) : Evm := (stepN 10 ⟨32, e3.sta, dP2 d⟩).getD default

/-- The forwarder's halted machine. -/
def post3F (d : Devm) : Devm :=
  match Evm.step (e3_44 d) with
  | .halt (.ok d') => d'
  | _ => default

theorem prefix3 : stepN 11 e3 = some e3_31 := by kernel_rfl

theorem cpI_eq : dcallPrep e3_31.sta e3_31.dyna [] acs3 = some cpI := by kernel_rfl

theorem eI_eq : frameEnterS cpI.f acs3 = .run eI := by kernel_rfl

theorem resumeI_eq : ∀ d : Devm,
    resumeCallB cpI.p cpI.oi cpI.os (.ok (obsChildI d)) = some (dP2 (obsChildI d)) := by
  kernel_forall_rfl

theorem tailI_eq : ∀ d : Devm,
    stepN 10 ⟨32, e3.sta, dP2 (obsChildI d)⟩ = some (e3_44 (obsChildI d)) := by
  kernel_forall_rfl

theorem returnI_eq : ∀ d : Devm,
    Evm.step (e3_44 (obsChildI d)) = .halt (.ok (post3F (obsChildI d))) := by
  kernel_forall_rfl

/-- The forwarder's gas at its `RETURN` (744,993 of 1,000,000), its (empty) return data and
its success. -/
theorem post3_obs : ∀ d : Devm,
    ((post3F (obsChildI d)).gasLeft, (post3F (obsChildI d)).output.map UInt8.toNat,
      (post3F (obsChildI d)).error.isNone) = (744993, [], true) := by
  kernel_forall_rfl

theorem post3_keep : ∀ d : Devm,
    (post3F (obsChildI d)).state = (dP2 (obsChildI d)).state := by
  kernel_forall_rfl

/-- Static facts of the machines and the spawn (closed evaluations). -/
theorem static3 :
    (e3.pc, e3.sta.code, e3.sta.currentTarget, e3.sta.benvStat.fork,
      e3.sta.benvStat.excessBlobGas) = (0, fwdCode, proxyAddr, .prague, 0) ∧
    e3_31.pc = 31 ∧ e3_31.sta = e3.sta ∧ e3_31.dyna.state = e3.dyna.state ∧
    e3_31.dyna.accessedAddresses = e3.dyna.accessedAddresses ∧
    e3_31.dyna.accessedStorageKeys = e3.dyna.accessedStorageKeys ∧
    (eI.pc, eI.sta.code, eI.sta.currentTarget, eI.sta.caller, eI.sta.data) =
      (0, Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code, proxyAddr, creator, initCall) ∧
    cpI.f.inner.codeAddress = some implAddr ∧ cpI.adrs = [implAddr] ∧
    acsTransfer cpI.f.inner acs3 = acs3 := by
  kernel_rfl_and

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach
