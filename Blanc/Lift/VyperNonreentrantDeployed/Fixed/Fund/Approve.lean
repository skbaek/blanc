import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund.Create
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund.Root

/-! # V+ message 7: `T.approve(P, 1000)` from the creator

The token frame is the root frame: 46 steps and `RETURN` of the word 1 (an EELS trace of the
same message agrees: 47 instructions, 77,697 gas left).  It stores
`allowance[creator][P] := 1000` at `allowSlot creator P = keccak256(pad32(creator) ‖ pad32(P))`.
The kernel facts are evaluated over `kCall world6 (origOf stor5) …` (kernel decisions: do not
open the facts in the language server) and transported by `leaf_root_re`. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init

/-- The cheap original state of message 7. -/
def O6 : State := origOf stor5

/-- The kernel's root frame of message 7. -/
def fA : Frame :=
  Frame.ofCall (kCall world6 O6 tokenAddr Blanc.Lift.VyperNonreentrantDeployed.Token20.code
    approveCall 100000 0)

def eA : Evm := runOr (frameEnterS fA acs6)
def cA : PCfg := childCfg eA fA [] [] stor5 acs6
def cA1 : PCfg := cfgOr cA (pwalkH (.avoid 0) tokenTries eA.sta okAny 46 cA)
def dA : Devm := haltOf (pwalkH (.avoid 0) tokenTries eA.sta okAny 1 cA1)

/-- `allowance[creator][P]`'s slot. -/
abbrev allowCP : B256 := Blanc.Lift.VyperNonreentrantDeployed.Token20.allowSlot creator proxyAddr

/-- The storage after message 7: the allowance, then `stor5`. -/
def stor7 : StorShadow := ((tokenAddr, allowCP), 1000) :: stor5

theorem approveFacts :
    frameEnterS fA acs6 = .run eA ∧
    (eA.pc, eA.sta.code, eA.sta.benvStat.fork, eA.sta.benvStat.excessBlobGas) =
      (0, Blanc.Lift.VyperNonreentrantDeployed.Token20.code, .prague, 0) ∧
    pwalkH (.avoid 0) tokenTries eA.sta okAny 46 cA = .cont cA1 ∧
    pwalkH (.avoid 0) tokenTries eA.sta okAny 1 cA1 = .halt (.ok dA) ∧
    dA.error = none ∧ dA.gasLeft = 77697 ∧ dA.refundCounter = 0 ∧
    canonS cA1.stor = canonS stor7 ∧
    (cA1.acs.map Prod.fst ++ acs6.map Prod.fst).map (lookupA cA1.acs) =
      (cA1.acs.map Prod.fst ++ acs6.map Prod.fst).map (lookupA acs6) ∧
    allowCP = (12548522795301110246656688538152381717102323405992693462683694671337620262864 :
      Nat).toB256 := by
  kernel_rfl_and

attribute [local irreducible] eA cA1 dA

/-- **Message 7, `T.approve(P, 1000)`**, every covered fork, from `world6`: it settles to the
closed machine `dA` with 77,697 of its 100,000 gas left and no refund; the world keeps every
account view and holds the storage `stor7` (the allowance `allowance[creator][P] = 1000` added). -/
theorem approve_run (g : Fork) (hg : CoveredFork g) (hW : WorldIs world6 acs6 stor5) :
    processMessage (approveMsg g world6) = .ok dA ∧ dA.error = none ∧ dA.gasLeft = 77697 ∧
      dA.refundCounter = 0 ∧ WorldIs dA.state acs6 stor7 := by
  obtain ⟨he, hst, w1, w2, hdT, hgas, hrc, hcanon, hkeys, -⟩ := approveFacts
  have hO : OrigAgree world6 O6 := origAgree_origOf hW.2
  obtain ⟨hmsg, hca⟩ := leaf_root_re hg tokenTries (.avoid 0) (by decide) hW hO he hst w1 w2 hdT
  refine ⟨hmsg, hdT, hgas, hrc, fun a => ?_, fun a k => ?_⟩
  · rw [hca.2.2.2 a]; exact lookupA_eq_of_map hkeys a
  · rw [hca.2.2.1 a k]; exact lookupS_eq_of_canonS hcanon a k

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund
