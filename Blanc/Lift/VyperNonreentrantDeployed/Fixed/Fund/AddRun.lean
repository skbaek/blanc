import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund.Approve

/-!
# V+ message 8: the kernel run of the first `add_liquidity([1000, 1000], 0)`

The frames of the call, as configurations of the node-exposing walks, over the closed world
`world7` that `approve` settles to, with the original state replaced by `origOf stor7`
(kernel decisions: do not open this file in the language server).  The step counts agree with
an EELS trace of the same message (Plans evidence `v3v5/eels_v3v5_sim.py`):

* `D`, the forwarder at the clone (1000 wei): 11 steps to its `DELEGATECALL`, then 10 steps and
  `RETURN` after its child;
* `DB`, the implementation in the clone's storage: 121 steps (the lock set at pc 0x61, `_A()`,
  `SELFBALANCE`) to the `STATICCALL` of `T.balanceOf(P)` (pc 13178); after it, 1269 steps
  (`_stored_rates` with `originator = 0`: no oracle call; two `get_D`s; the first-deposit mint
  `D1 = 2000`) to the `CALL` of `T.transferFrom(creator, P, 1000)` (pc 1273); after it 122 steps
  (`balanceOf[creator] += 2000` at `keccak256(20 ‖ creator)`, `totalSupply := 2000`, the lock
  release at pc 0x61c) and `RETURN`;
* `Bal`, the token answering `balanceOf(P)` (29 steps and `RETURN` of the word 0);
* `Tf`, the token's `transferFrom` (85 steps and `RETURN` of the word 1): it lowers the
  allowance to 0 and moves 1000 from the creator to `P`.

Every pool walk holds the hash policy `.avoid 0`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init

/-- The world `approve` settles to. -/
@[irreducible] def world7 : State := dA.state

/-- The cheap original state of message 8. -/
def O7 : State := origOf stor7

/-- The kernel's root frame of message 8. -/
def fD : Frame := Frame.ofCall (kCall world7 O7 proxyAddr fwd addCall 1000000 1000)

/-! ### The forwarder frame up to its `DELEGATECALL` -/

def eD : Evm := runOr (frameEnterS fD acs6)
def cD : PCfg := childCfg eD fD [] [] stor7 acs6
def cD1 : PCfg := cfgOr cD (pwalkH .refuse fwdTries eD.sta okAny 11 cD)
def cpD : CallPrep := prepOr (dcallPrep eD.sta cD1.devm cD1.adrs cD1.acs)

/-! ### The pool body up to the `STATICCALL` of `balanceOf` -/

def eDB : Evm := runOr (frameEnterS cpD.f cD1.acs)
def cDB0 : PCfg := childCfg eDB cpD.f cD1.keys cpD.adrs cD1.stor cD1.acs
def cDB1 : PCfg := cfgOr cDB0 (pwalkH (.avoid 0) codeTries eDB.sta okAny 121 cDB0)
def cpBal : CallPrep := prepOr (scallPrep eDB.sta cDB1.devm cDB1.adrs cDB1.acs)

/-! ### The token answering `balanceOf(P)` -/

def eBal : Evm := runOr (frameEnterS cpBal.f cDB1.acs)
def cBal0 : PCfg := childCfg eBal cpBal.f cDB1.keys cpBal.adrs cDB1.stor cDB1.acs
def cBal1 : PCfg := cfgOr cBal0 (pwalkH (.avoid 0) tokenTries eBal.sta okAny 29 cBal0)
def dBal : Devm := haltOf (pwalkH (.avoid 0) tokenTries eBal.sta okAny 1 cBal1)

/-! ### The pool body up to the `CALL` of `transferFrom` -/

def dDB2 : Devm := resumeOr cpBal dBal
def cDB2 : PCfg :=
  ⟨cDB1.pc + 1, dDB2, cDB1.keys ++ cBal1.keys, cpBal.adrs ++ cBal1.adrs, cBal1.stor, cBal1.acs⟩
def cDB3 : PCfg := cfgOr cDB0 (pwalkH (.avoid 0) codeTries eDB.sta okAny 1269 cDB2)
def cpTf : CallPrep := prepOr (callPrepP eDB.sta cDB3)

/-! ### The token's `transferFrom` -/

def eTf : Evm := runOr (frameEnterS cpTf.f cDB3.acs)
def cTf0 : PCfg := childCfg eTf cpTf.f cDB3.keys cpTf.adrs cDB3.stor cDB3.acs
def cTf1 : PCfg := cfgOr cTf0 (pwalkH (.avoid 0) tokenTries eTf.sta okAny 85 cTf0)
def dTf : Devm := haltOf (pwalkH (.avoid 0) tokenTries eTf.sta okAny 1 cTf1)

/-! ### The pool body after the token, the mint, and `RETURN` -/

def dDB4 : Devm := resumeOr cpTf dTf
def cDB4 : PCfg :=
  ⟨cDB3.pc + 1, dDB4, cDB3.keys ++ cTf1.keys, cpTf.adrs ++ cTf1.adrs, cTf1.stor, cTf1.acs⟩
def cDB5 : PCfg := cfgOr cDB0 (pwalkH (.avoid 0) codeTries eDB.sta okAny 122 cDB4)
def dDB : Devm := haltOf (pwalkH (.avoid 0) codeTries eDB.sta okAny 1 cDB5)

/-! ### The forwarder after the pool body, and `RETURN` -/

def dD2 : Devm := resumeOr cpD dDB
def cD2 : PCfg :=
  ⟨cD1.pc + 1, dD2, cD1.keys ++ cDB5.keys, cpD.adrs ++ cDB5.adrs, cDB5.stor, cDB5.acs⟩
def cD3 : PCfg := cfgOr cD2 (pwalkH .refuse fwdTries eD.sta okAny 10 cD2)
def dD : Devm := haltOf (pwalkH .refuse fwdTries eD.sta okAny 1 cD3)

/-! ## The world the run leaves -/

/-- The pool's liquidity-balance slot of `h`: `keccak256(pad32(20) ‖ pad32(h))` (`balanceOf` is
the source's field at slot 20). -/
def lpSlot (h : Adr) : B256 := mapSlot (20 : B256) h.toB256

/-- **The storage after `add_liquidity`**, newest write first: the lock released (3), the
supply 2000 (slot `0x16`), the creator's 2000 liquidity tokens, the token's balances of `P`
(1000) and of the creator (999,000); then the clean pool.  The allowance was lowered to 0. -/
def storAdd : StorShadow :=
  [((proxyAddr, 0), 3), ((proxyAddr, 0x16), 2000), ((proxyAddr, lpSlot creator), 2000),
   ((tokenAddr, proxyAddr.toB256), 1000), ((tokenAddr, creator.toB256), 999000)] ++ storOracle

/-- The accounts after `add_liquidity`: 1000 wei moved from the creator to the clone. -/
def acctsAdd : List (Adr × Acct) :=
  [(implAddr, implAccount), (proxyAddr, { proxyAccount with bal := 1000 }),
   (creator, { creatorAccount with bal := creatorFunds - 1000 }), (tokenAddr, tokenAccount),
   (receiverAddr, receiverAccount)]

def acsAdd : AcctShadow := acctShadowOf acctsAdd

/-! ## The kernel decisions -/

theorem addFacts :
    -- the forwarder to its `DELEGATECALL`, and the pool body's entry
    frameEnterS fD acs6 = .run eD ∧
    (eD.pc, eD.sta.currentTarget, eD.sta.code, eD.sta.benvStat.fork,
      eD.sta.benvStat.excessBlobGas) = (0, proxyAddr, fwd, .prague, 0) ∧
    pwalkH .refuse fwdTries eD.sta okAny 11 cD = .cont cD1 ∧
    cD1.pc = 31 ∧
    decodeT 6 fwdTries.bytes 31 = some (.next (.exec .delegatecall)) ∧
    dcallPrep eD.sta cD1.devm cD1.adrs cD1.acs = some cpD ∧
    frameEnterS cpD.f cD1.acs = .run eDB ∧
    (eDB.pc, eDB.sta.currentTarget, eDB.sta.code) = (0, proxyAddr, code) ∧
    cpD.f.inner.codeAddress = some implAddr ∧
    -- the pool body to the `STATICCALL` of `balanceOf`
    pwalkH (.avoid 0) codeTries eDB.sta okAny 121 cDB0 = .cont cDB1 ∧
    cDB1.pc = 13178 ∧
    decodeT 15 codeTries.bytes 13178 = some (.next (.exec .staticcall)) ∧
    scallPrep eDB.sta cDB1.devm cDB1.adrs cDB1.acs = some cpBal ∧
    cpBal.f.inner.codeAddress = some tokenAddr ∧
    frameEnterS cpBal.f cDB1.acs = .run eBal ∧
    (eBal.pc, eBal.sta.currentTarget, eBal.sta.code) =
      (0, tokenAddr, Blanc.Lift.VyperNonreentrantDeployed.Token20.code) ∧
    pwalkH (.avoid 0) tokenTries eBal.sta okAny 29 cBal0 = .cont cBal1 ∧
    pwalkH (.avoid 0) tokenTries eBal.sta okAny 1 cBal1 = .halt (.ok dBal) ∧
    dBal.error = none ∧
    resumeCallB cpBal.p cpBal.oi cpBal.os (.ok dBal) = some dDB2 ∧
    -- the pool body to the `CALL` of `transferFrom`
    pwalkH (.avoid 0) codeTries eDB.sta okAny 1269 cDB2 = .cont cDB3 ∧
    cDB3.pc = 1273 ∧
    decodeT 15 codeTries.bytes 1273 = some (.next (.exec .call)) ∧
    callPrepP eDB.sta cDB3 = some cpTf ∧
    cpTf.f.inner.codeAddress = some tokenAddr ∧
    frameEnterS cpTf.f cDB3.acs = .run eTf ∧
    (eTf.pc, eTf.sta.currentTarget, eTf.sta.code, eTf.sta.value.toNat) =
      (0, tokenAddr, Blanc.Lift.VyperNonreentrantDeployed.Token20.code, 0) ∧
    pwalkH (.avoid 0) tokenTries eTf.sta okAny 85 cTf0 = .cont cTf1 ∧
    pwalkH (.avoid 0) tokenTries eTf.sta okAny 1 cTf1 = .halt (.ok dTf) ∧
    dTf.error = none ∧
    resumeCallB cpTf.p cpTf.oi cpTf.os (.ok dTf) = some dDB4 ∧
    -- the mint and `RETURN`
    pwalkH (.avoid 0) codeTries eDB.sta okAny 122 cDB4 = .cont cDB5 ∧
    pwalkH (.avoid 0) codeTries eDB.sta okAny 1 cDB5 = .halt (.ok dDB) ∧
    dDB.error = none ∧
    -- the forwarder's tail
    resumeCallB cpD.p cpD.oi cpD.os (.ok dDB) = some dD2 ∧
    pwalkH .refuse fwdTries eD.sta okAny 10 cD2 = .cont cD3 ∧
    pwalkH .refuse fwdTries eD.sta okAny 1 cD3 = .halt (.ok dD) ∧
    dD.error = none ∧ dD.gasLeft = 871140 ∧ dD.refundCounter = 4800 ∧
    -- the shadows the run leaves
    canonS cD3.stor = canonS storAdd ∧
    (cD3.acs.map Prod.fst ++ acsAdd.map Prod.fst).map (lookupA cD3.acs) =
      (cD3.acs.map Prod.fst ++ acsAdd.map Prod.fst).map (lookupA acsAdd) ∧
    lpSlot creator =
      (66137768575171327046773413134821529148712368753860433062216994293256264992817 :
        Nat).toB256 := by
  kernel_rfl_and

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund
