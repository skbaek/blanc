import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Creation.Check
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Creation.Walk
import Blanc.SystemCallForward

/-! # Exact CREATE of the 0x847e implementation

A zero-value CREATE message whose code is the preserved creation input succeeds on every
covered fork, installs exactly the registered runtime `Fixed.code` at its target, leaves the
target's storage `Stor.empty.set 1 1` (the constructor's `factory := 1`), and changes no other
account. The settled world is stated account by account against the message's input world, so
a following message can start from it. Message execution only: no historical inclusion, sender
nonce or signature claim. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Creation

open Jaune Blanc.Lift

/-- The selected charge of the constructor's `SSTORE(1, 1)` on the freshly cleared target:
cold unless the message pre-warmed `(target, 1)`, valued against the block-original slot. -/
def implSstoreGas (msg : Msg) : Nat :=
  (if (⟨msg.currentTarget, 1⟩ : Adr × B256) ∈ msg.accessedStorageKeys then 0
    else gasColdSload) +
  sstoreValueCost ((msg.benv.stat.origState.get msg.currentTarget).stor.get 1) 0 1

/-- The implementation account after creation: nonce incremented, balance kept, storage
`factory := 1` only, the registered runtime installed. -/
def implAcct (W : State) (I : Adr) : Acct where
  nonce := (W.get I).nonce + 1
  bal := (W.get I).bal
  stor := Stor.empty.set 1 1
  code := Blanc.Lift.VyperNonreentrantDeployed.Fixed.code

theorem runtime_code : (⟨⟨runtime⟩⟩ : ByteArray) = Blanc.Lift.VyperNonreentrantDeployed.Fixed.code :=
  have eta : ∀ b : ByteArray, (⟨⟨b.data.toList⟩⟩ : ByteArray) = b := fun b => by
    cases b
    rfl
  eta _

/-- Code deposit of the 18,320-byte runtime. -/
theorem runtime_deposit : runtime.length * gasCodeDeposit = 3664000 := by
  rw [runtime_length]
  rfl

/-- **Exact implementation CREATE.** -/
theorem create_impl (msg : Msg) (hfork : CoveredFork msg.benv.stat.fork)
    (haddress : msg.codeAddress = none) (hcode : msg.code = creationCode)
    (hstatic : msg.isStatic = false) (hvalue : msg.value = 0) (hgas : 3690218 ≤ msg.gas) :
    ∃ post, processCreateMessage msg = .ok post ∧ post.error = none ∧
      post.gasLeft = msg.gas - (4118 + implSstoreGas msg) - 3664000 ∧
      post.state.get msg.currentTarget = implAcct msg.benv.state msg.currentTarget ∧
      ∀ a, a ≠ msg.currentTarget → post.state.get a = msg.benv.state.get a := by
  obtain ⟨benv, htransfer⟩ :=
    benvAfterTransfer_exists_zero (msg := processCreateMessage.msg msg) hvalue
  let sevm := initSevm (createSeed msg benv)
  let b := initDevm (createSeed msg benv)
  let G := msg.gas - constructorGas sevm b
  have hstat : sevm.benvStat = msg.benv.stat := by
    change benv.stat = (processCreateMessage.msg msg).benv.stat
    exact benvAfterTransfer_stat htransfer
  have hempty : b.getStor sevm.currentTarget = Stor.empty := by
    change benv.state.getStor msg.currentTarget = Stor.empty
    rw [benvAfterTransfer_ok_getStor htransfer, processCreateMessage_msg_getStor_currentTarget]
  have hsc : sstoreCost sevm b 1 1 = implSstoreGas msg := by
    unfold sstoreCost implSstoreGas getOrigStorVal getOrigAcct
    rw [hstat]
    have hcur : b.getStorVal sevm.currentTarget 1 = 0 := by
      unfold Devm.getStorVal
      change (b.getStor sevm.currentTarget).get 1 = 0
      rw [hempty]
      rfl
    rw [hcur]
    rfl
  have hcg : constructorGas sevm b = 4118 + implSstoreGas msg := by
    rw [constructorGas, hsc]
  have hcost : constructorGas sevm b ≤ msg.gas :=
    Nat.le_trans (constructorGas_le sevm b) (Nat.le_trans (by decide) hgas)
  have hremaining : 3664000 ≤ G := by
    apply Nat.le_sub_of_add_le
    exact Nat.le_trans (Nat.add_le_add_left (constructorGas_le sevm b) 3664000)
      (Nat.le_trans (by decide) hgas)
  have hsentry : gCallStipend < G := Nat.lt_of_lt_of_le (by decide) hremaining
  have hrun := constructor_run sevm b G (hstat ▸ hfork) hstatic hcode hvalue hsentry
  have hpre : St b [] Mem.empty (G + constructorGas sevm b) = b :=
    pre_eq_St rfl rfl (Nat.sub_add_cancel hcost)
  rw [hpre] at hrun
  have facts := constructorPost_facts sevm b G
  have herror : (constructorPost sevm b G).error = none := facts.2.1.trans rfl
  have hprefix : (constructorPost sevm b G).output.head? ≠ some 0xEF := by
    rw [facts.1, runtime_head]
    decide
  have hdeposit : (constructorPost sevm b G).output.length * gasCodeDeposit ≤
      (constructorPost sevm b G).gasLeft := by
    rw [facts.1, runtime_deposit, facts.2.2.2.2]
    exact hremaining
  have hmax : (constructorPost sevm b G).output.length ≤
      msg.benv.stat.rules.code.maxCodeSize := by
    rw [facts.1, runtime_length]
    exact CoveredFork.cases (motive := fun f => 18320 ≤ (Fork.ruleSet f).code.maxCodeSize)
      hfork (by decide) (by decide) (by decide) (by decide)
  have hpost := liftCreate_post cert_check jumps_ok msg haddress hcode hfork htransfer hrun
    herror hprefix hdeposit hmax
  have pf := liftCreatePost_facts msg.currentTarget (constructorPost sevm b G)
  have hraw : (constructorPost sevm b G).state = benv.state.setStorVal msg.currentTarget 1 1 := by
    rw [facts.2.2.1, afterSstore_state]
    rfl
  refine ⟨_, hpost, pf.1.trans herror, ?_, ?_, ?_⟩
  · rw [pf.2.1, facts.2.2.2.2, facts.1, runtime_deposit]
    show msg.gas - constructorGas sevm b - 3664000 = _
    rw [hcg]
  · rw [pf.2.2.1, hraw, facts.1]
    unfold State.setStorVal
    rw [State.get_set_self, processCreateMessage_msg_afterTransfer_get hvalue htransfer,
      if_pos rfl, runtime_code]
    unfold implAcct
    rfl
  · intro a ha
    rw [pf.2.2.2 a ha, hraw, State.get_setStorVal_ne _ _ _ (Ne.symm ha),
      processCreateMessage_msg_afterTransfer_get hvalue htransfer, if_neg ha]

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Creation
