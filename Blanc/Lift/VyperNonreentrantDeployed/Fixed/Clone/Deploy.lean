import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Clone.Check
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Clone.Walk
import Blanc.TransactionForward

/-! # Synthetic CREATE of an EIP-1167 clone of `0x847e`

A zero-value CREATE message whose code is the **synthetic** clone creation input
(`Clone/Input.lean`) succeeds on every covered fork with exact gas, installs exactly
`Blanc.forwarderCode curvePlainImpl847e` at its target with empty storage, and changes no other
account. Message execution only; this is not the historical Curve factory. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Clone

open Jaune Blanc.Lift

/-- The clone account after creation: nonce incremented, balance kept, storage empty, the
forwarder to `0x847e` installed. -/
def cloneAcct (W : State) (P : Adr) : Acct where
  nonce := (W.get P).nonce + 1
  bal := (W.get P).bal
  stor := Stor.empty
  code := Blanc.forwarderCode Blanc.curvePlainImpl847e

theorem forwarder_code :
    (⟨⟨forwarder⟩⟩ : ByteArray) = Blanc.forwarderCode Blanc.curvePlainImpl847e := rfl

/-- **Synthetic clone CREATE**: 28 gas of copier and 9000 of code deposit. -/
theorem create_clone (msg : Msg) (hfork : CoveredFork msg.benv.stat.fork)
    (haddress : msg.codeAddress = none) (hcode : msg.code = cloneCreationCode)
    (hvalue : msg.value = 0) (hgas : 9028 ≤ msg.gas) :
    ∃ post, processCreateMessage msg = .ok post ∧ post.error = none ∧
      post.gasLeft = msg.gas - 28 - 9000 ∧
      post.state.get msg.currentTarget = cloneAcct msg.benv.state msg.currentTarget ∧
      ∀ a, a ≠ msg.currentTarget → post.state.get a = msg.benv.state.get a := by
  obtain ⟨benv, htransfer⟩ :=
    benvAfterTransfer_exists_zero (msg := processCreateMessage.msg msg) hvalue
  let sevm := initSevm (createSeed msg benv)
  let b := initDevm (createSeed msg benv)
  let G := msg.gas - 28
  have hrun := clone_run sevm b G hcode rfl
  have hpre : St b [] Mem.empty (G + 28) = b :=
    pre_eq_St rfl rfl (Nat.sub_add_cancel (Nat.le_trans (by decide) hgas))
  rw [hpre] at hrun
  have facts := clonePost_facts b G
  have hprefix : (clonePost b G).output.head? ≠ some 0xEF := by
    rw [facts.1, forwarder_head]
    decide
  have hdeposit : (clonePost b G).output.length * gasCodeDeposit ≤ (clonePost b G).gasLeft := by
    rw [facts.1, forwarder_length, facts.2.2.2]
    change 9000 ≤ msg.gas - 28
    omega
  have hmax : (clonePost b G).output.length ≤ msg.benv.stat.rules.code.maxCodeSize := by
    rw [facts.1, forwarder_length]
    exact CoveredFork.cases (motive := fun f => 45 ≤ (Fork.ruleSet f).code.maxCodeSize)
      hfork (by decide) (by decide) (by decide) (by decide)
  have hpost := liftCreate_post cert_check jumps_ok msg haddress hcode hfork htransfer hrun
    (facts.2.1.trans rfl) hprefix hdeposit hmax
  have pf := liftCreatePost_facts msg.currentTarget (clonePost b G)
  refine ⟨_, hpost, pf.1.trans (facts.2.1.trans rfl), ?_, ?_, ?_⟩
  · rw [pf.2.1, facts.2.2.2, facts.1, forwarder_length]
    rfl
  · rw [pf.2.2.1, facts.2.2.1, facts.1, forwarder_code]
    change ({ benv.state.get msg.currentTarget with code := _ } : Acct) = _
    rw [processCreateMessage_msg_afterTransfer_get hvalue htransfer, if_pos rfl]
    unfold cloneAcct
    rfl
  · intro a ha
    rw [pf.2.2.2 a ha, facts.2.2.1]
    exact (processCreateMessage_msg_afterTransfer_get hvalue htransfer a).trans (if_neg ha)

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Clone
