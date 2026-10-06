import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init.Run

/-!
# V+ setup message 4: the kernel run of `set_oracle(0, 0)` through the clone

As `Run.lean`, over the closed world `world3` that message 3 settles to (`(dI world2).state`,
described by `acs0` and `storInit`), at Prague (kernel decisions: do not open this file in the
language server).  Step counts from the Lean interpreter, agreeing with an
EELS trace of the same message.

* `top`, the forwarder: 11 steps to its `DELEGATECALL`, 10 steps and `RETURN` after its child;
* `B`, the implementation in the clone's storage: 278 steps to `STOP` (pc 11492), through the
  `originator == msg.sender` check (`SLOAD` of slot `0x0e`) and the two `SSTORE`s of
  `oracle_method := 0` (pc 0x2cde, slot `0x0d`) and `originator := 0` (pc 0x2ce3, slot `0x0e`).
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach

/-- The world `initialize` settles to, as a closed term. -/
def world3 : State := (dI world2).state

/-- The kernel's top-level frame over the input world `W` (Prague). -/
def fO (W : State) : Frame := Frame.ofCall (callMsg .prague W oracleCall 100000)

def eO (W : State) : Evm := runOr (frameEnterS (fO W) acs0)
def cO (W : State) : PCfg := childCfg (eO W) (fO W) [] [] storInit acs0
def cO1 (W : State) : PCfg := cfgOr (cO W) (pwalkH .refuse fwdTries (eO W).sta okAny 11 (cO W))
def cpO (W : State) : CallPrep :=
  prepOr (dcallPrep (eO W).sta (cO1 W).devm (cO1 W).adrs (cO1 W).acs)
def eOB (W : State) : Evm := runOr (frameEnterS (cpO W).f (cO1 W).acs)
def cOB0 (W : State) : PCfg :=
  childCfg (eOB W) (cpO W).f (cO1 W).keys (cpO W).adrs (cO1 W).stor (cO1 W).acs
def cOB1 (W : State) : PCfg :=
  cfgOr (cOB0 W) (pwalkH (.avoid 0) codeTries (eOB W).sta okAny 278 (cOB0 W))
def dOB (W : State) : Devm := haltOf (pwalkH (.avoid 0) codeTries (eOB W).sta okAny 1 (cOB1 W))
def dO2 (W : State) : Devm := resumeOr (cpO W) (dOB W)
def cO2 (W : State) : PCfg :=
  ⟨(cO1 W).pc + 1, dO2 W, (cO1 W).keys ++ (cOB1 W).keys, (cpO W).adrs ++ (cOB1 W).adrs,
    (cOB1 W).stor, (cOB1 W).acs⟩
def cO3 (W : State) : PCfg :=
  cfgOr (cO2 W) (pwalkH .refuse fwdTries (eO W).sta okAny 10 (cO2 W))
def dO (W : State) : Devm := haltOf (pwalkH .refuse fwdTries (eO W).sta okAny 1 (cO3 W))

/-- **The world's storage after `set_oracle(0, 0)`**: `storInit` with the originator (slot
`0x0e`) cleared; `oracle_method` (slot `0x0d`) is written 0 and holds nothing. -/
def storOracle : StorShadow :=
  [((proxyAddr, 0x17), domainSeparator),
   ((proxyAddr, 0x13), leftWord symbolBytes),
   ((proxyAddr, 0x12), (2 : Nat).toB256),
   ((proxyAddr, 0x10), leftWord nameBytes),
   ((proxyAddr, 0x0f), (23 : Nat).toB256),
   ((proxyAddr, 0x1b), timeV2),
   ((proxyAddr, 0x19), packedPrices),
   ((proxyAddr, 0x1a), (866 : Nat).toB256),
   ((proxyAddr, 0x01), creator.toNat.toB256),
   ((proxyAddr, 0x0a), (100 : Nat).toB256),
   ((proxyAddr, 0x09), (100 : Nat).toB256),
   ((proxyAddr, 0x03), tokenAddr.toNat.toB256),
   ((proxyAddr, 0x02), ethSentinel.toB256),
   ((implAddr, 1), 1)]

theorem oracleFactsA :
    frameEnterS (fO world3) acs0 = .run (eO world3) ∧
    ((eO world3).pc, (eO world3).sta.currentTarget, (eO world3).sta.code, (eO world3).sta.benvStat.fork,
      (eO world3).sta.benvStat.excessBlobGas) =
      (0, proxyAddr, Blanc.forwarderCode Blanc.curvePlainImpl847e, .prague, 0) ∧
    pwalkH .refuse fwdTries (eO world3).sta okAny 11 (cO world3) = .cont (cO1 world3) ∧
    (cO1 world3).pc = 31 ∧
    decodeT 6 fwdTries.bytes 31 = some (.next (.exec .delegatecall)) ∧
    dcallPrep (eO world3).sta (cO1 world3).devm (cO1 world3).adrs (cO1 world3).acs = some (cpO world3) ∧
    frameEnterS (cpO world3).f (cO1 world3).acs = .run (eOB world3) ∧
    ((eOB world3).pc, (eOB world3).sta.currentTarget, (eOB world3).sta.code) = (0, proxyAddr, code) ∧
    (cpO world3).f.inner.codeAddress = some implAddr ∧
    pwalkH (.avoid 0) codeTries (eOB world3).sta okAny 278 (cOB0 world3) = .cont (cOB1 world3) ∧
    pwalkH (.avoid 0) codeTries (eOB world3).sta okAny 1 (cOB1 world3) = .halt (.ok (dOB world3)) ∧
    (dOB world3).error = none ∧
    resumeCallB (cpO world3).p (cpO world3).oi (cpO world3).os (.ok (dOB world3)) = some (dO2 world3) ∧
    pwalkH .refuse fwdTries (eO world3).sta okAny 10 (cO2 world3) = .cont (cO3 world3) ∧
    pwalkH .refuse fwdTries (eO world3).sta okAny 1 (cO3 world3) = .halt (.ok (dO world3)) ∧
    (dO world3).error = none ∧ (dO world3).gasLeft = 89070 ∧ (dO world3).refundCounter = 4800 := by
  kernel_rfl_and

theorem oracleFactsC :
    canonS (cO3 world3).stor = storOracle ∧
    (cO3 world3).acs.map Prod.fst =
      [proxyAddr, creator, creator, proxyAddr, implAddr] ∧
    lookupA (cO3 world3).acs proxyAddr = lookupA acs0 proxyAddr ∧
    lookupA (cO3 world3).acs creator = lookupA acs0 creator ∧
    lookupA (cO3 world3).acs implAddr = lookupA acs0 implAddr := by
  kernel_rfl_and

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init
