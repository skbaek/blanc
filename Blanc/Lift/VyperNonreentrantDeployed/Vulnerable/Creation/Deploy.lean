import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Creation.Check
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Creation.Walk
import Blanc.Lift.CreateEntry
import Blanc.SystemCallForward

/-! # Exact CREATE of the 0x6326 implementation

A zero-value CREATE message whose code is the preserved creation input succeeds on every
covered fork, installs exactly the registered runtime `Vulnerable.code` at its target, leaves the
target's storage `Stor.empty.set 10 31337` (the constructor's `fee := 31337`), and changes no
other account. The settled world is also stated as an explicit term of the input world
(`CreateEntry.entryState`), so a following message can start from it and evaluate it. Message
execution only: no historical inclusion, sender nonce or signature claim. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Creation

open Jaune Blanc.Lift

/-- The selected charge of the constructor's `SSTORE(10, 31337)` on the freshly cleared target:
cold unless the message pre-warmed `(target, 10)`, valued against the selected zero
original (the CREATE target is always in the entry machine's created accounts). -/
def implSstoreGas (msg : Msg) : Nat :=
  (if (⟨msg.currentTarget, 10⟩ : Adr × B256) ∈ msg.accessedStorageKeys then 0
    else gasColdSload) +
  sstoreValueCost 0 0 31337

/-- The implementation account after creation: nonce incremented, balance kept, storage
`fee := 31337` only, the registered runtime installed. -/
def implAcct (W : State) (I : Adr) : Acct where
  nonce := (W.get I).nonce + 1
  bal := (W.get I).bal
  stor := Stor.empty.set 10 31337
  code := Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code

/-- The installed runtime is nonempty (its size is the constructor-output length). -/
theorem installed_code_size_ne_zero :
    Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code.size ≠ 0 := by
  have h : Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code.size = runtime.length := rfl
  rw [h, runtime_length]
  decide

/-- An account carrying the installed runtime is never empty. -/
theorem installed_not_empty {ac : Acct}
    (hcode : ac.code = Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code) :
    ¬ ac.Empty := by
  intro h
  exact installed_code_size_ne_zero (hcode ▸ h.1)

theorem runtime_code :
    (⟨⟨runtime⟩⟩ : ByteArray) = Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code :=
  (fun (c : ByteArray) => show (⟨⟨c.data.toList⟩⟩ : ByteArray) = c by cases c; rfl) _

/-- Code deposit of the 17,535-byte runtime. -/
theorem runtime_deposit : runtime.length * gasCodeDeposit = 3507000 := by
  rw [runtime_length]
  rfl

/-- **Exact implementation CREATE.** -/
theorem create_impl (msg : Msg) (hfork : CoveredFork msg.benv.stat.fork)
    (haddress : msg.codeAddress = none) (hcode : msg.code = creationCode)
    (hstatic : msg.isStatic = false) (hvalue : msg.value = 0)
    (hstv : msg.shouldTransferValue = true) (hgas : 3533022 ≤ msg.gas) :
    ∃ post, processCreateMessage msg = .ok post ∧ post.error = none ∧
      post.gasLeft = msg.gas - (3922 + implSstoreGas msg) - 3507000 ∧
      post.state.get msg.currentTarget = implAcct msg.benv.state msg.currentTarget ∧
      (∀ a, a ≠ msg.currentTarget → post.state.get a = msg.benv.state.get a) ∧
      post.state = ((CreateEntry.entryState msg.benv.state msg.caller msg.currentTarget).setStorVal
        msg.currentTarget 10 31337).setCode msg.currentTarget
          Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code := by
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
    rw [benvAfterTransfer_ok_getStor htransfer _ (Or.inl hvalue),
      processCreateMessage_msg_getStor_currentTarget]
  have h0 : (processCreateMessage.msg msg).benvAfterTransfer =
      .ok (processCreateMessage.msg msg).benv :=
    Msg.benvAfterTransfer_of_value_zero (show (processCreateMessage.msg msg).value = 0 from hvalue)
  have hbenv_eq : benv = (processCreateMessage.msg msg).benv :=
    Except.ok.inj (htransfer.symm.trans h0)
  have hmem : sevm.currentTarget ∈ b.createdAccounts := by
    have h1 : b.createdAccounts = benv.createdAccounts := rfl
    rw [h1, hbenv_eq]
    show msg.currentTarget ∈ (processCreateMessage.msg msg).benv.createdAccounts
    unfold processCreateMessage.msg addCreatedAccount
    show msg.currentTarget ∈ (msg.benv.createdAccounts.insert msg.currentTarget)
    exact Std.HashSet.mem_insert_self
  have hsc : sstoreCost sevm b 10 31337 = implSstoreGas msg := by
    have horig0 : b.getOrigStorVal sevm sevm.currentTarget 10 = 0 := by
      unfold Devm.getOrigStorVal
      rw [ite_eq_left hmem]
    have hcur : b.getStorVal sevm.currentTarget 10 = 0 := by
      unfold Devm.getStorVal
      change (b.getStor sevm.currentTarget).get 10 = 0
      rw [hempty]
      rfl
    have hkeys : b.accessedStorageKeys = msg.accessedStorageKeys := rfl
    have hct : sevm.currentTarget = msg.currentTarget := rfl
    unfold sstoreCost implSstoreGas
    rw [horig0, hcur, hct, hkeys]
  have hcg : constructorGas sevm b = 3922 + implSstoreGas msg := by
    rw [constructorGas, hsc]
  have hcost : constructorGas sevm b ≤ msg.gas :=
    Nat.le_trans (constructorGas_le sevm b) (Nat.le_trans (by decide) hgas)
  have hremaining : 3507000 ≤ G := by
    apply Nat.le_sub_of_add_le
    exact Nat.le_trans (Nat.add_le_add_left (constructorGas_le sevm b) 3507000)
      (Nat.le_trans (by decide) hgas)
  have hsentry : gCallStipend < G := Nat.lt_of_lt_of_le (by decide) hremaining
  have hrun := constructor_run sevm b G (hstat ▸ hfork) hstatic hcode hsentry
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
    rw [facts.1, runtime_deposit, facts.2.2.2]
    exact hremaining
  have hmax : (constructorPost sevm b G).output.length ≤
      msg.benv.stat.rules.code.maxCodeSize := by
    rw [facts.1, runtime_length]
    exact CoveredFork.cases (motive := fun f => 17535 ≤ (Fork.ruleSet f).code.maxCodeSize)
      hfork (by decide) (by decide) (by decide) (by decide)
  have hpost := liftCreate_post cert_check jumps_ok msg haddress hcode hfork htransfer hrun
    herror hprefix hdeposit hmax
  have pf := liftCreatePost_facts msg.currentTarget (constructorPost sevm b G)
  have hraw : (constructorPost sevm b G).state =
      benv.state.setStorVal msg.currentTarget 10 31337 := by
    rw [facts.2.2.1, afterSstore_state]
    rfl
  refine ⟨_, hpost, pf.1.trans herror, ?_, ?_, ?_, ?_⟩
  · rw [pf.2.1, facts.2.2.2, facts.1, runtime_deposit]
    show msg.gas - constructorGas sevm b - 3507000 = _
    rw [hcg]
  · rw [pf.2.2.1, hraw, facts.1]
    unfold State.setStorVal
    rw [State.get_set_self, processCreateMessage_msg_afterTransfer_get hvalue htransfer,
      if_pos rfl, runtime_code]
    unfold implAcct
    apply Acct.ext
    · simp only [Acct.clearIfEmpty_nonce]
    · simp only [Acct.clearIfEmpty_bal]
    · simp only [Acct.clearIfEmpty_stor]
      split
      · rename_i h
        exact absurd h (installed_not_empty (by rfl))
      · rfl
    · simp only [Acct.clearIfEmpty_code]
  · intro a ha
    rw [pf.2.2.2 a ha, hraw, State.get_setStorVal_ne _ _ _ (Ne.symm ha),
      processCreateMessage_msg_afterTransfer_get hvalue htransfer, if_neg ha]
  · rw [CreateEntry.liftCreatePost_state, hraw, facts.1, runtime_code,
      CreateEntry.entry_state hvalue hstv htransfer]

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Creation
