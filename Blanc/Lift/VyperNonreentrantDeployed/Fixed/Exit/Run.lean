import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund.Add
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2.Run

/-!
# V+ V5: the kernel run of `remove_liquidity(200, [0, 0], R)` from the funded checkpoint

The frames of the call over the closed checkpoint world `world8` (what `add_liquidity` settles
to), the original state replaced by `origOf storAdd` (kernel decisions: do not open this file in
the language server).  The step counts agree with an EELS trace of the same message
(Plans evidence `v3v5/eels_v3v5_sim.py`); outermost first:

* `top`, the forwarder at the clone: 11 steps to its `DELEGATECALL`, 10 steps and `RETURN`;
* `B`, the pool body (`code` in the clone's storage): 174 steps to the `remove_liquidity` body
  start `0x1bae` (the lock set by the `SSTORE` at 0x1bad); 57 steps to the `STATICCALL` of
  `T.balanceOf(P)` (pc 13178); 151 steps to the ETH `CALL` of pc 7427 (100 wei to `R`); 119 steps
  to the `CALL` of `T.transfer(R, 100)` (pc 7488); 125 steps and `RETURN`.  No release `SSTORE`
  lies between the body start and the ETH `CALL`;
* `bal` (29 steps and `RETURN`) and `xfer` (53 steps and `RETURN` of the word 1): the token;
* `rcv`, the receiver `R` called with the 100 wei: 17 steps to its `CALL` of the clone (pc 86,
  `add_liquidity([100, 0], 0)` with the 100 wei), then `POP` and `STOP` after its failure;
* `cb`, the clone's forwarder the receiver calls: 11 steps to its `DELEGATECALL`, 9 steps and
  `REVERT` after its failed child;
* `re`, the reentrant pool frame: 26 steps to the lock check (pc 0x53), 6 steps to the revert
  pad 0x477e, 4 steps and `REVERT`; no node is at a guarded body start.

Every pool walk holds the hash policy `.avoid 0`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2 (okNoRel okNoBody settleOr)

/-- The funded checkpoint, as the closed world `add_liquidity` settles to. -/
@[irreducible] def world8 : State := dD.state

/-- The cheap original state of the V5 call. -/
def O8 : State := origOf storAdd

/-- The calldata of the receiver's reentry attempt: `add_liquidity([100, 0], 0)`. -/
def reentryData : Bytes := [0x0b, 0x4c, 0x7e, 0x4d] ++ Witness.word 100 ++ Witness.word 0 ++
  Witness.word 0

def fTop : Frame := Frame.ofCall (kCall world8 O8 proxyAddr fwd removeCall 1000000 0)

/-! ### The forwarder frame up to its `DELEGATECALL` -/

def eTop : Evm := runOr (frameEnterS fTop acsAdd)
def cTop : PCfg := childCfg eTop fTop [] [] storAdd acsAdd
def cTop1 : PCfg := cfgOr cTop (pwalkH .refuse fwdTries eTop.sta okAny 11 cTop)
def cpTop : CallPrep := prepOr (dcallPrep eTop.sta cTop1.devm cTop1.adrs cTop1.acs)

/-! ### The pool body up to its `STATICCALL` -/

def eB : Evm := runOr (frameEnterS cpTop.f cTop1.acs)
def cB0 : PCfg := childCfg eB cpTop.f cTop1.keys cpTop.adrs cTop1.stor cTop1.acs
def cB1 : PCfg := cfgOr cB0 (pwalkH (.avoid 0) codeTries eB.sta okAny 174 cB0)
def cB2 : PCfg := cfgOr cB0 (pwalkH (.avoid 0) codeTries eB.sta okNoRel 57 cB1)
def cpBal : CallPrep := prepOr (scallPrep eB.sta cB2.devm cB2.adrs cB2.acs)

/-! ### The token answering `balanceOf(P)` -/

def eBal : Evm := runOr (frameEnterS cpBal.f cB2.acs)
def cBal0 : PCfg := childCfg eBal cpBal.f cB2.keys cpBal.adrs cB2.stor cB2.acs
def cBal1 : PCfg := cfgOr cBal0 (pwalkH (.avoid 0) tokenTries eBal.sta okAny 29 cBal0)
def dBal : Devm := haltOf (pwalkH (.avoid 0) tokenTries eBal.sta okAny 1 cBal1)

/-! ### The pool body up to its ETH `CALL` -/

def dB3 : Devm := resumeOr cpBal dBal
def cB3 : PCfg :=
  ⟨cB2.pc + 1, dB3, cB2.keys ++ cBal1.keys, cpBal.adrs ++ cBal1.adrs, cBal1.stor, cBal1.acs⟩
def cB4 : PCfg := cfgOr cB0 (pwalkH (.avoid 0) codeTries eB.sta okNoRel 151 cB3)
def cpEth : CallPrep := prepOr (callPrepP eB.sta cB4)

/-! ### The receiver, up to its `CALL` of the clone -/

def eRcv : Evm := runOr (frameEnterS cpEth.f cB4.acs)
def cRcv0 : PCfg := childCfg eRcv cpEth.f cB4.keys cpEth.adrs cB4.stor cB4.acs
def cRcv1 : PCfg := cfgOr cRcv0 (pwalkH .refuse recvTries eRcv.sta okAny 17 cRcv0)
def cpCb : CallPrep := prepOr (callPrepP eRcv.sta cRcv1)

/-! ### The callback forwarder, up to its `DELEGATECALL` -/

def eCb : Evm := runOr (frameEnterS cpCb.f cRcv1.acs)
def cCb0 : PCfg := childCfg eCb cpCb.f cRcv1.keys cpCb.adrs cRcv1.stor cRcv1.acs
def cCb1 : PCfg := cfgOr cCb0 (pwalkH .refuse fwdTries eCb.sta okAny 11 cCb0)
def cpRe : CallPrep := prepOr (dcallPrep eCb.sta cCb1.devm cCb1.adrs cCb1.acs)

/-! ### The reentrant pool frame: the lock check, and `REVERT` -/

def eRe : Evm := runOr (frameEnterS cpRe.f cCb1.acs)
def cRe0 : PCfg := childCfg eRe cpRe.f cCb1.keys cpRe.adrs cCb1.stor cCb1.acs
def cRe1 : PCfg := cfgOr cRe0 (pwalkH (.avoid 0) codeTries eRe.sta okNoBody 26 cRe0)
def cRe2 : PCfg := cfgOr cRe0 (pwalkH (.avoid 0) codeTries eRe.sta okNoBody 6 cRe1)
def dRe : Devm := haltOf (pwalkH (.avoid 0) codeTries eRe.sta okNoBody 4 cRe2)

/-! ### The callback forwarder after its failed child -/

def dCb2 : Devm := resumeOr cpRe (settleOr cpRe.f (.error (.revert, dRe)))
def cCb2 : PCfg := ⟨cCb1.pc + 1, dCb2, cCb1.keys, cpRe.adrs, cCb1.stor, cCb1.acs⟩
def cCb3 : PCfg := cfgOr cCb2 (pwalkH .refuse fwdTries eCb.sta okAny 9 cCb2)
def dCb : Devm := haltOf (pwalkH .refuse fwdTries eCb.sta okAny 1 cCb3)

/-! ### The receiver after its failed call, and `STOP` -/

def dRcv2 : Devm := resumeOr cpCb (settleOr cpCb.f (.error (.revert, dCb)))
def cRcv2 : PCfg := ⟨cRcv1.pc + 1, dRcv2, cRcv1.keys, cpCb.adrs, cRcv1.stor, cRcv1.acs⟩
def cRcv3 : PCfg := cfgOr cRcv2 (pwalkH .refuse recvTries eRcv.sta okAny 1 cRcv2)
def dRcv : Devm := haltOf (pwalkH .refuse recvTries eRcv.sta okAny 1 cRcv3)

/-! ### The pool body after the receiver, up to the token's `transfer` -/

def dB5 : Devm := resumeOr cpEth dRcv
def cB5 : PCfg :=
  ⟨cB4.pc + 1, dB5, cB4.keys ++ cRcv3.keys, cpEth.adrs ++ cRcv3.adrs, cRcv3.stor, cRcv3.acs⟩
def cB6 : PCfg := cfgOr cB0 (pwalkH (.avoid 0) codeTries eB.sta okAny 119 cB5)
def cpXf : CallPrep := prepOr (callPrepP eB.sta cB6)

/-! ### The token's `transfer(R, 100)` -/

def eXf : Evm := runOr (frameEnterS cpXf.f cB6.acs)
def cXf0 : PCfg := childCfg eXf cpXf.f cB6.keys cpXf.adrs cB6.stor cB6.acs
def cXf1 : PCfg := cfgOr cXf0 (pwalkH (.avoid 0) tokenTries eXf.sta okAny 53 cXf0)
def dXf : Devm := haltOf (pwalkH (.avoid 0) tokenTries eXf.sta okAny 1 cXf1)

/-! ### The pool body after the token, and `RETURN` -/

def dB7 : Devm := resumeOr cpXf dXf
def cB7 : PCfg :=
  ⟨cB6.pc + 1, dB7, cB6.keys ++ cXf1.keys, cpXf.adrs ++ cXf1.adrs, cXf1.stor, cXf1.acs⟩
def cB8 : PCfg := cfgOr cB0 (pwalkH (.avoid 0) codeTries eB.sta okAny 125 cB7)
def dB : Devm := haltOf (pwalkH (.avoid 0) codeTries eB.sta okAny 1 cB8)

/-! ### The forwarder after the pool body, and `RETURN` -/

def dTop2 : Devm := resumeOr cpTop dB
def cTop2 : PCfg :=
  ⟨cTop1.pc + 1, dTop2, cTop1.keys ++ cB8.keys, cpTop.adrs ++ cB8.adrs, cB8.stor, cB8.acs⟩
def cTop3 : PCfg := cfgOr cTop2 (pwalkH .refuse fwdTries eTop.sta okAny 10 cTop2)
def dTop : Devm := haltOf (pwalkH .refuse fwdTries eTop.sta okAny 1 cTop3)

/-! ## The world the run leaves -/

/-- **The storage after `remove_liquidity`**, newest write first: the lock released, supply
1800, the creator's 1800 liquidity tokens, the token's balances of `R` (100) and `P` (900); then
the creator's 999,000 tokens and the clean pool. -/
def storExit : StorShadow :=
  [((proxyAddr, 0), 3), ((proxyAddr, 0x16), 1800), ((proxyAddr, lpSlot creator), 1800),
   ((tokenAddr, receiverAddr.toB256), 100), ((tokenAddr, proxyAddr.toB256), 900),
   ((tokenAddr, creator.toB256), 999000)] ++ storOracle

/-- The accounts after `remove_liquidity`: 100 wei moved from the clone to `R`. -/
def acctsExit : List (Adr × Acct) :=
  [(implAddr, implAccount), (proxyAddr, { proxyAccount with bal := 900 }),
   (creator, { creatorAccount with bal := creatorFunds - 1000 }), (tokenAddr, tokenAccount),
   (receiverAddr, { receiverAccount with bal := 100 })]

def acsExit : AcctShadow := acctShadowOf acctsExit

/-! ## The kernel decisions -/

theorem exitFacts :
    -- the forwarder frame: 11 steps to its `DELEGATECALL`, which spawns the pool body
    frameEnterS fTop acsAdd = .run eTop ∧
    (eTop.pc, eTop.sta.currentTarget, eTop.sta.code, eTop.sta.benvStat.fork,
      eTop.sta.benvStat.excessBlobGas) = (0, proxyAddr, fwd, .prague, 0) ∧
    pwalkH .refuse fwdTries eTop.sta okAny 11 cTop = .cont cTop1 ∧
    cTop1.pc = 31 ∧
    decodeT 6 fwdTries.bytes 31 = some (.next (.exec .delegatecall)) ∧
    dcallPrep eTop.sta cTop1.devm cTop1.adrs cTop1.acs = some cpTop ∧
    frameEnterS cpTop.f cTop1.acs = .run eB ∧
    (eB.pc, eB.sta.currentTarget, eB.sta.code, eB.sta.data) = (0, proxyAddr, code, removeCall) ∧
    cpTop.f.inner.codeAddress = some implAddr ∧
    -- the pool body: the body start, the `STATICCALL` of `balanceOf`
    pwalkH (.avoid 0) codeTries eB.sta okAny 174 cB0 = .cont cB1 ∧
    cB1.pc = 0x1bae ∧
    pwalkH (.avoid 0) codeTries eB.sta okNoRel 57 cB1 = .cont cB2 ∧
    cB2.pc = 13178 ∧
    decodeT 15 codeTries.bytes 13178 = some (.next (.exec .staticcall)) ∧
    scallPrep eB.sta cB2.devm cB2.adrs cB2.acs = some cpBal ∧
    cpBal.f.inner.codeAddress = some tokenAddr ∧
    frameEnterS cpBal.f cB2.acs = .run eBal ∧
    (eBal.pc, eBal.sta.currentTarget, eBal.sta.code) =
      (0, tokenAddr, Blanc.Lift.VyperNonreentrantDeployed.Token20.code) ∧
    pwalkH (.avoid 0) tokenTries eBal.sta okAny 29 cBal0 = .cont cBal1 ∧
    pwalkH (.avoid 0) tokenTries eBal.sta okAny 1 cBal1 = .halt (.ok dBal) ∧
    dBal.error = none ∧
    resumeCallB cpBal.p cpBal.oi cpBal.os (.ok dBal) = some dB3 ∧
    -- the ETH `CALL` to the receiver
    pwalkH (.avoid 0) codeTries eB.sta okNoRel 151 cB3 = .cont cB4 ∧
    cB4.pc = 7427 ∧
    decodeT 15 codeTries.bytes 7427 = some (.next (.exec .call)) ∧
    callPrepP eB.sta cB4 = some cpEth ∧
    cpEth.f.inner.codeAddress = some receiverAddr ∧
    frameEnterS cpEth.f cB4.acs = .run eRcv ∧
    (eRcv.pc, eRcv.sta.currentTarget, eRcv.sta.code, eRcv.sta.value.toNat, eRcv.sta.caller) =
      (0, receiverAddr, Blanc.Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.code, 100,
        proxyAddr) ∧
    -- the receiver: 17 steps to its `CALL` of the clone
    pwalkH .refuse recvTries eRcv.sta okAny 17 cRcv0 = .cont cRcv1 ∧
    cRcv1.pc = 86 ∧
    decodeT 7 recvTries.bytes 86 = some (.next (.exec .call)) ∧
    callPrepP eRcv.sta cRcv1 = some cpCb ∧
    cpCb.f.inner.codeAddress = some proxyAddr ∧
    frameEnterS cpCb.f cRcv1.acs = .run eCb ∧
    (eCb.pc, eCb.sta.currentTarget, eCb.sta.code, eCb.sta.value.toNat) = (0, proxyAddr, fwd, 100) ∧
    -- the callback forwarder: 11 steps to its `DELEGATECALL`
    pwalkH .refuse fwdTries eCb.sta okAny 11 cCb0 = .cont cCb1 ∧
    cCb1.pc = 31 ∧
    dcallPrep eCb.sta cCb1.devm cCb1.adrs cCb1.acs = some cpRe ∧
    cpRe.f.inner.codeAddress = some implAddr ∧
    frameEnterS cpRe.f cCb1.acs = .run eRe ∧
    (eRe.pc, eRe.sta.currentTarget, eRe.sta.code, eRe.sta.data) =
      (0, proxyAddr, code, reentryData) ∧
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
    pwalkH .refuse recvTries eRcv.sta okAny 1 cRcv2 = .cont cRcv3 ∧
    pwalkH .refuse recvTries eRcv.sta okAny 1 cRcv3 = .halt (.ok dRcv) ∧
    dRcv.error = none ∧
    -- the pool body after the receiver: the token's `transfer`
    resumeCallB cpEth.p cpEth.oi cpEth.os (.ok dRcv) = some dB5 ∧
    pwalkH (.avoid 0) codeTries eB.sta okAny 119 cB5 = .cont cB6 ∧
    cB6.pc = 7488 ∧
    decodeT 15 codeTries.bytes 7488 = some (.next (.exec .call)) ∧
    callPrepP eB.sta cB6 = some cpXf ∧
    cpXf.f.inner.codeAddress = some tokenAddr ∧
    frameEnterS cpXf.f cB6.acs = .run eXf ∧
    (eXf.pc, eXf.sta.currentTarget, eXf.sta.code, eXf.sta.value.toNat) =
      (0, tokenAddr, Blanc.Lift.VyperNonreentrantDeployed.Token20.code, 0) ∧
    pwalkH (.avoid 0) tokenTries eXf.sta okAny 53 cXf0 = .cont cXf1 ∧
    pwalkH (.avoid 0) tokenTries eXf.sta okAny 1 cXf1 = .halt (.ok dXf) ∧
    dXf.error = none ∧
    resumeCallB cpXf.p cpXf.oi cpXf.os (.ok dXf) = some dB7 ∧
    -- `RETURN`, and the forwarder's tail
    pwalkH (.avoid 0) codeTries eB.sta okAny 125 cB7 = .cont cB8 ∧
    pwalkH (.avoid 0) codeTries eB.sta okAny 1 cB8 = .halt (.ok dB) ∧
    dB.error = none ∧
    resumeCallB cpTop.p cpTop.oi cpTop.os (.ok dB) = some dTop2 ∧
    pwalkH .refuse fwdTries eTop.sta okAny 10 cTop2 = .cont cTop3 ∧
    pwalkH .refuse fwdTries eTop.sta okAny 1 cTop3 = .halt (.ok dTop) ∧
    dTop.error = none ∧ dTop.gasLeft = 920078 ∧ dTop.refundCounter = 2800 ∧
    -- the shadows the run leaves
    canonS cTop3.stor = canonS storExit ∧
    (cTop3.acs.map Prod.fst ++ acsExit.map Prod.fst).map (lookupA cTop3.acs) =
      (cTop3.acs.map Prod.fst ++ acsExit.map Prod.fst).map (lookupA acsExit) := by
  kernel_rfl_and

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit
