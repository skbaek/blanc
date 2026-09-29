import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2.Setup

/-!
# V+ committing witness: the kernel run

The frames of the run, as configurations of the node-exposing walks of `Blanc/Lift/NodeWalk.lean`
(kernel decisions: do not open this file in the language server).  The step counts are
printed by the Lean interpreter (`#eval` over the walks, in a scratch file) and decided here,
in two `kernel_rfl_and` batches, each one kernel check that evaluates every boundary once.

The tree of frames, outermost first:

* `top`, the forwarder `fwdCode` at the pool address (11 steps to its `DELEGATECALL`, then 10
  steps and `RETURN` after its child);
* `B`, the pool body (`code`, storage owner the pool address): 174 steps to the
  `remove_liquidity` body start `0x1bae`; 57 steps to the `STATICCALL` of
  `coins[1].balanceOf(self)` (pc 13178); 151 steps to the ETH `CALL` of pc 7427 (100 wei to
  `X`); 119 steps to the `CALL` of pc 7488 (`coins[1].transfer`, no value); 125 steps and
  `RETURN`.  Every walk holds the hash policy `.avoid 0`; the one `KECCAK256` it executes
  (the `balanceOf[S]` slot) leaves a digest other than the lock slot;
* `bal` and `xfer`, the coin frames of the `STATICCALL` and the transfer (`Receiver.code`
  called without value: 8 steps and `RETURN` of the word 1);
* `rcv`, the receiver frame `X` called with the 100 wei (14 steps to its `CALL` of the pool
  through the forwarder, then 1 step and `STOP`);
* `cb`, the forwarder frame the receiver calls (11 steps to its `DELEGATECALL`; 9 steps and
  `REVERT` after its failed child);
* `re`, the reentrant pool frame (`code`, called with `add_liquidity`'s selector and zero
  arguments while the lock is held): 26 steps to the lock check at pc 0x53, 6 steps to the
  landing pad 0x477e, 3 steps and `REVERT`; no node is at a guarded body start.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun

/-- A walk configuration or a default. -/
def cfgOr (d : PCfg) : PRes → PCfg
  | .cont c => c
  | _ => d

/-- The halted machine of a walk result (a default for a walk that did not halt). -/
def haltOf : PRes → Devm
  | .halt (.ok d) => d
  | .halt (.error (_, d)) => d
  | _ => default

/-- No pc check. -/
def okAny : Nat → Bool := fun _ => true
/-- Not at a release `SSTORE`. -/
def okNoRel : Nat → Bool := fun pc => !lockReleasePcs.contains pc
/-- Not at a guarded body start. -/
def okNoBody : Nat → Bool := fun pc => !lockBodies.contains pc

/-- The prepared call of a `.some` preparation, or a default. -/
def prepOr : Option CallPrep → CallPrep
  | some cp => cp
  | none => ⟨frameTop, default, 0, 0, []⟩

/-- The entry machine of a frame entry, or a default. -/
def runOr : FrameEntry → Evm
  | .run e => e
  | .done _ => default

/-- The machine a call child settles to. -/
def settleOr (f : Frame) (ex : Execution) : Devm :=
  match f.settle ex with
  | .ok d => d
  | .error _ => default

/-- The parent's machine after a call child settled to `d`. -/
def resumeOr (cp : CallPrep) (d : Devm) : Devm := (resumeCallB cp.p cp.oi cp.os (.ok d)).getD default

/-- The calldata of the receiver's reentry attempt: `add_liquidity(uint256[2],uint256)`'s
selector, then three zero words. -/
def reentryCall : Bytes := [0x0b, 0x4c, 0x7e, 0x4d] ++ List.replicate 96 0

/-! ### The forwarder frame up to its `DELEGATECALL` -/

def cTop1 : PCfg := cfgOr cTop (pwalkH .refuse fwdTries eTop.sta okAny 11 cTop)
def cpTop : CallPrep := prepOr (dcallPrep eTop.sta cTop1.devm cTop1.adrs cTop1.acs)
/-- The pool body frame's entry machine. -/
def eB : Evm := runOr (frameEnterS cpTop.f cTop1.acs)

/-! ### The pool body up to its `STATICCALL` -/

def cB0 : PCfg := childCfg eB cpTop.f cTop1.keys cpTop.adrs cTop1.stor cTop1.acs
def cB1 : PCfg := cfgOr cB0 (pwalkH (.avoid 0) codeTries eB.sta okAny 174 cB0)
def cB2 : PCfg := cfgOr cB0 (pwalkH (.avoid 0) codeTries eB.sta okNoRel 57 cB1)
def cpBal : CallPrep := prepOr (scallPrep eB.sta cB2.devm cB2.adrs cB2.acs)
/-- The coin frame's entry machine. -/
def eBal : Evm := runOr (frameEnterS cpBal.f cB2.acs)

/-! ### The coin frame -/

def cBal0 : PCfg := childCfg eBal cpBal.f cB2.keys cpBal.adrs cB2.stor cB2.acs
def cBal1 : PCfg := cfgOr cBal0 (pwalkH .refuse receiverTries eBal.sta okAny 8 cBal0)
/-- The coin frame's halted machine. -/
def dBal : Devm := haltOf (pwalkH .refuse receiverTries eBal.sta okAny 1 cBal1)

/-! ### The pool body after the coin, up to its ETH `CALL` -/

def dB3 : Devm := resumeOr cpBal dBal
def cB3 : PCfg :=
  ⟨cB2.pc + 1, dB3, cB2.keys ++ cBal1.keys, cpBal.adrs ++ cBal1.adrs, cBal1.stor, cBal1.acs⟩
def cB4 : PCfg := cfgOr cB0 (pwalkH (.avoid 0) codeTries eB.sta okNoRel 151 cB3)
def cpEth : CallPrep := prepOr (callPrepP eB.sta cB4)
/-- The receiver frame's entry machine. -/
def eRcv : Evm := runOr (frameEnterS cpEth.f cB4.acs)

/-! ### The receiver frame, up to its `CALL` of the pool -/

def cRcv0 : PCfg := childCfg eRcv cpEth.f cB4.keys cpEth.adrs cB4.stor cB4.acs
def cRcv1 : PCfg := cfgOr cRcv0 (pwalkH .refuse receiverTries eRcv.sta okAny 14 cRcv0)
def cpCb : CallPrep := prepOr (callPrepP eRcv.sta cRcv1)
/-- The callback forwarder frame's entry machine. -/
def eCb : Evm := runOr (frameEnterS cpCb.f cRcv1.acs)

/-! ### The callback forwarder frame, up to its `DELEGATECALL` -/

def cCb0 : PCfg := childCfg eCb cpCb.f cRcv1.keys cpCb.adrs cRcv1.stor cRcv1.acs
def cCb1 : PCfg := cfgOr cCb0 (pwalkH .refuse fwdTries eCb.sta okAny 11 cCb0)
def cpRe : CallPrep := prepOr (dcallPrep eCb.sta cCb1.devm cCb1.adrs cCb1.acs)
/-- The reentrant pool frame's entry machine. -/
def eRe : Evm := runOr (frameEnterS cpRe.f cCb1.acs)

/-! ### The reentrant pool frame: the lock check, and `REVERT` -/

def cRe0 : PCfg := childCfg eRe cpRe.f cCb1.keys cpRe.adrs cCb1.stor cCb1.acs
def cRe1 : PCfg := cfgOr cRe0 (pwalkH (.avoid 0) codeTries eRe.sta okNoBody 26 cRe0)
def cRe2 : PCfg := cfgOr cRe0 (pwalkH (.avoid 0) codeTries eRe.sta okNoBody 6 cRe1)
/-- The reentrant frame's halted machine. -/
def dRe : Devm := haltOf (pwalkH (.avoid 0) codeTries eRe.sta okNoBody 4 cRe2)

/-! ### The callback forwarder after its failed child -/

def dCb2 : Devm := resumeOr cpRe (settleOr cpRe.f (.error (.revert, dRe)))
def cCb2 : PCfg := ⟨cCb1.pc + 1, dCb2, cCb1.keys, cpRe.adrs, cCb1.stor, cCb1.acs⟩
def cCb3 : PCfg := cfgOr cCb2 (pwalkH .refuse fwdTries eCb.sta okAny 9 cCb2)
/-- The callback forwarder's halted machine. -/
def dCb : Devm := haltOf (pwalkH .refuse fwdTries eCb.sta okAny 1 cCb3)

/-! ### The receiver after its failed call, and `STOP` -/

def dRcv2 : Devm := resumeOr cpCb (settleOr cpCb.f (.error (.revert, dCb)))
def cRcv2 : PCfg := ⟨cRcv1.pc + 1, dRcv2, cRcv1.keys, cpCb.adrs, cRcv1.stor, cRcv1.acs⟩
def cRcv3 : PCfg := cfgOr cRcv2 (pwalkH .refuse receiverTries eRcv.sta okAny 1 cRcv2)
/-- The receiver frame's halted machine. -/
def dRcv : Devm := haltOf (pwalkH .refuse receiverTries eRcv.sta okAny 1 cRcv3)

/-! ### The pool body after the receiver, up to its transfer `CALL` -/

def dB5 : Devm := resumeOr cpEth dRcv
def cB5 : PCfg :=
  ⟨cB4.pc + 1, dB5, cB4.keys ++ cRcv3.keys, cpEth.adrs ++ cRcv3.adrs, cRcv3.stor, cRcv3.acs⟩
def cB6 : PCfg := cfgOr cB0 (pwalkH (.avoid 0) codeTries eB.sta okAny 119 cB5)
def cpXf : CallPrep := prepOr (callPrepP eB.sta cB6)
/-- The transfer coin frame's entry machine. -/
def eXf : Evm := runOr (frameEnterS cpXf.f cB6.acs)

/-! ### The transfer coin frame -/

def cXf0 : PCfg := childCfg eXf cpXf.f cB6.keys cpXf.adrs cB6.stor cB6.acs
def cXf1 : PCfg := cfgOr cXf0 (pwalkH .refuse receiverTries eXf.sta okAny 8 cXf0)
/-- The transfer coin frame's halted machine. -/
def dXf : Devm := haltOf (pwalkH .refuse receiverTries eXf.sta okAny 1 cXf1)

/-! ### The pool body after the transfer, and `RETURN` -/

def dB7 : Devm := resumeOr cpXf dXf
def cB7 : PCfg :=
  ⟨cB6.pc + 1, dB7, cB6.keys ++ cXf1.keys, cpXf.adrs ++ cXf1.adrs, cXf1.stor, cXf1.acs⟩
def cB8 : PCfg := cfgOr cB0 (pwalkH (.avoid 0) codeTries eB.sta okAny 125 cB7)
/-- The pool body's halted machine. -/
def dB : Devm := haltOf (pwalkH (.avoid 0) codeTries eB.sta okAny 1 cB8)

/-! ### The forwarder after the pool body, and `RETURN` -/

def dTop2 : Devm := resumeOr cpTop dB
def cTop2 : PCfg :=
  ⟨cTop1.pc + 1, dTop2, cTop1.keys ++ cB8.keys, cpTop.adrs ++ cB8.adrs, cB8.stor, cB8.acs⟩
def cTop3 : PCfg := cfgOr cTop2 (pwalkH .refuse fwdTries eTop.sta okAny 10 cTop2)
/-- The top-level frame's halted machine. -/
def dTop : Devm := haltOf (pwalkH .refuse fwdTries eTop.sta okAny 1 cTop3)

/-! ## The kernel decisions -/

/-- The forwarder and the pool body up to the ETH `CALL`, and the receiver's entry. -/
theorem runFactsA :
    -- the forwarder frame: 11 steps to its `DELEGATECALL`, which spawns the pool body
    pwalkH .refuse fwdTries eTop.sta okAny 11 cTop = .cont cTop1 ∧
    cTop1.pc = 31 ∧
    decodeT 6 fwdTries.bytes 31 = some (.next (.exec .delegatecall)) ∧
    dcallPrep eTop.sta cTop1.devm cTop1.adrs cTop1.acs = some cpTop ∧
    frameEnterS cpTop.f cTop1.acs = .run eB ∧
    (eB.pc, eB.sta.currentTarget, eB.sta.code, eB.sta.data, eB.sta.benvStat.fork) =
      (0, proxyAddress, code, removeCall, .prague) ∧
    -- the pool body: the body start, the `STATICCALL` of `balanceOf`
    pwalkH (.avoid 0) codeTries eB.sta okAny 174 cB0 = .cont cB1 ∧
    cB1.pc = 0x1bae ∧
    pwalkH (.avoid 0) codeTries eB.sta okNoRel 57 cB1 = .cont cB2 ∧
    cB2.pc = 13178 ∧
    decodeT 15 codeTries.bytes 13178 = some (.next (.exec .staticcall)) ∧
    scallPrep eB.sta cB2.devm cB2.adrs cB2.acs = some cpBal ∧
    frameEnterS cpBal.f cB2.acs = .run eBal ∧
    (eBal.pc, eBal.sta.currentTarget, eBal.sta.code) = (0, receiverAddress, Receiver.code) ∧
    -- the coin frame returns the word 1
    pwalkH .refuse receiverTries eBal.sta okAny 8 cBal0 = .cont cBal1 ∧
    pwalkH .refuse receiverTries eBal.sta okAny 1 cBal1 = .halt (.ok dBal) ∧
    dBal.error = none ∧
    -- the pool body after the coin: the ETH `CALL`
    resumeCallB cpBal.p cpBal.oi cpBal.os (.ok dBal) = some dB3 ∧
    pwalkH (.avoid 0) codeTries eB.sta okNoRel 151 cB3 = .cont cB4 ∧
    cB4.pc = 7427 ∧
    decodeT 15 codeTries.bytes 7427 = some (.next (.exec .call)) ∧
    callPrepP eB.sta cB4 = some cpEth ∧
    frameEnterS cpEth.f cB4.acs = .run eRcv ∧
    (eRcv.pc, eRcv.sta.currentTarget, eRcv.sta.code, eRcv.sta.value.toNat, eRcv.sta.caller) =
      (0, receiverAddress, Receiver.code, 100, proxyAddress) := by
  kernel_rfl_and

/-- The receiver, the callback forwarder and the reentrant pool frame. -/
theorem runFactsB :
    -- the receiver frame: 14 steps to its `CALL` of the pool forwarder
    pwalkH .refuse receiverTries eRcv.sta okAny 14 cRcv0 = .cont cRcv1 ∧
    cRcv1.pc = 83 ∧
    decodeT 7 receiverTries.bytes 83 = some (.next (.exec .call)) ∧
    callPrepP eRcv.sta cRcv1 = some cpCb ∧
    frameEnterS cpCb.f cRcv1.acs = .run eCb ∧
    (eCb.pc, eCb.sta.currentTarget, eCb.sta.code, eCb.sta.value.toNat) =
      (0, proxyAddress, fwdCode, 0) ∧
    -- the callback forwarder: 11 steps to its `DELEGATECALL`
    pwalkH .refuse fwdTries eCb.sta okAny 11 cCb0 = .cont cCb1 ∧
    cCb1.pc = 31 ∧
    decodeT 6 fwdTries.bytes 31 = some (.next (.exec .delegatecall)) ∧
    dcallPrep eCb.sta cCb1.devm cCb1.adrs cCb1.acs = some cpRe ∧
    frameEnterS cpRe.f cCb1.acs = .run eRe ∧
    (eRe.pc, eRe.sta.currentTarget, eRe.sta.code, eRe.sta.data) =
      (0, proxyAddress, code, reentryCall) ∧
    -- the reentrant frame: the lock check, the landing pad, `REVERT`
    pwalkH (.avoid 0) codeTries eRe.sta okNoBody 26 cRe0 = .cont cRe1 ∧
    cRe1.pc = 0x53 ∧
    pwalkH (.avoid 0) codeTries eRe.sta okNoBody 6 cRe1 = .cont cRe2 ∧
    cRe2.pc = 0x477e ∧
    pwalkH (.avoid 0) codeTries eRe.sta okNoBody 4 cRe2 = .halt (.error (.revert, dRe)) ∧
    -- the callback forwarder after its failed child
    cpRe.f.settle (.error (.revert, dRe)) = .ok (settleOr cpRe.f (.error (.revert, dRe))) ∧
    resumeCallB cpRe.p cpRe.oi cpRe.os (.ok (settleOr cpRe.f (.error (.revert, dRe)))) =
      some dCb2 ∧
    pwalkH .refuse fwdTries eCb.sta okAny 9 cCb2 = .cont cCb3 ∧
    pwalkH .refuse fwdTries eCb.sta okAny 1 cCb3 = .halt (.error (.revert, dCb)) ∧
    -- the receiver after its failed call
    cpCb.f.settle (.error (.revert, dCb)) = .ok (settleOr cpCb.f (.error (.revert, dCb))) ∧
    resumeCallB cpCb.p cpCb.oi cpCb.os (.ok (settleOr cpCb.f (.error (.revert, dCb)))) =
      some dRcv2 ∧
    pwalkH .refuse receiverTries eRcv.sta okAny 1 cRcv2 = .cont cRcv3 ∧
    pwalkH .refuse receiverTries eRcv.sta okAny 1 cRcv3 = .halt (.ok dRcv) ∧
    dRcv.error = none := by
  kernel_rfl_and

/-- The pool body after the receiver: the transfer, `RETURN`; the forwarder's tail. -/
theorem runFactsC :
    resumeCallB cpEth.p cpEth.oi cpEth.os (.ok dRcv) = some dB5 ∧
    pwalkH (.avoid 0) codeTries eB.sta okAny 119 cB5 = .cont cB6 ∧
    cB6.pc = 7488 ∧
    decodeT 15 codeTries.bytes 7488 = some (.next (.exec .call)) ∧
    callPrepP eB.sta cB6 = some cpXf ∧
    frameEnterS cpXf.f cB6.acs = .run eXf ∧
    (eXf.pc, eXf.sta.currentTarget, eXf.sta.code, eXf.sta.value.toNat) =
      (0, receiverAddress, Receiver.code, 0) ∧
    pwalkH .refuse receiverTries eXf.sta okAny 8 cXf0 = .cont cXf1 ∧
    pwalkH .refuse receiverTries eXf.sta okAny 1 cXf1 = .halt (.ok dXf) ∧
    dXf.error = none ∧
    resumeCallB cpXf.p cpXf.oi cpXf.os (.ok dXf) = some dB7 ∧
    pwalkH (.avoid 0) codeTries eB.sta okAny 125 cB7 = .cont cB8 ∧
    pwalkH (.avoid 0) codeTries eB.sta okAny 1 cB8 = .halt (.ok dB) ∧
    dB.error = none ∧
    resumeCallB cpTop.p cpTop.oi cpTop.os (.ok dB) = some dTop2 ∧
    pwalkH .refuse fwdTries eTop.sta okAny 10 cTop2 = .cont cTop3 ∧
    pwalkH .refuse fwdTries eTop.sta okAny 1 cTop3 = .halt (.ok dTop) := by
  kernel_rfl_and

/-- The forwarder's entry, and the pre- and post-state the shadows show. -/
theorem runFactsD :
    (eTop.pc, eTop.sta.currentTarget, eTop.sta.code, eTop.sta.benvStat.fork) =
      (0, proxyAddress, fwdCode, .prague) ∧
    (lookupA cTop.acs proxyAddress).code = fwdCode ∧
    (lookupA cTop.acs curvePlainImpl847e).code = code ∧
    (lookupA cTop3.acs proxyAddress).bal.toNat = 900 ∧
    (lookupA cTop3.acs receiverAddress).bal.toNat = 100 ∧
    lookupS cTop3.stor proxyAddress 0 = (3 : Nat).toB256 ∧
    (lookupA cTop.acs proxyAddress).bal.toNat = 1000 ∧
    (lookupA cTop.acs receiverAddress).bal.toNat = 0 ∧
    lookupS cTop.stor proxyAddress 0 = (3 : Nat).toB256 := by
  kernel_rfl_and

/-- **Control: the hash policy bites in this run.**  The last walk of the pool body executes one
`KECCAK256` (pc 7612, the digest is `balanceSlot`); the same walk under the policy `.avoid
balanceSlot` is stuck, where `runFactsC` shows it continues under `.avoid 0`. -/
theorem hashControl_bites :
    pwalkH (.avoid balanceSlot) codeTries eB.sta okAny 125 cB7 = .stuck := by
  kernel_rfl_and

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2
