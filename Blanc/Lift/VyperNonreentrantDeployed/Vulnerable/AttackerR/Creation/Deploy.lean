import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.AttackerR.Creation.Check
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.AttackerR.Check
import Blanc.Lift.Deploy
import Blanc.Lift.ExactWalkCutOps
import Blanc.Lift.CreateEntry
import Blanc.BytesWrite

/-! # Exact CREATE of the reachable V− attacker

A zero-value CREATE message whose code is the synthetic attacker creation input (a 9-byte copier
and the registered 186-byte `AttackerR` runtime) succeeds on every covered fork, installs exactly
that runtime at its target with empty storage, for 52 gas of execution and 37,200 of code
deposit, and changes no other account. The settled world is also an explicit term of the input
world. Message execution only. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.AttackerR.Creation

open Jaune Blanc.Lift

/-- The registered runtime's bytes. -/
abbrev runtime : List UInt8 := Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.AttackerR.code.data.toList

theorem runtime_length : runtime.length = 186 := by decide +kernel

theorem runtime_ne_nil : runtime ≠ [] :=
  List.ne_nil_of_length_pos (by rw [runtime_length]; decide)

theorem runtime_head : runtime.head? = some 0x60 := by decide +kernel

/-- **The copy window is the registered runtime**: `creation[9, 195)` is `AttackerR.code`. -/
theorem runtime_window : creationCode.sliceD 9 186 0 = runtime := by
  rw [ByteArray.sliceD_eq, creationCode, ByteArray.toList_eq_toList_data, List.toList_toArray]
  have hp : copier.length = 9 := rfl
  rw [← hp, ← runtime_length]
  simpa only [List.append_nil] using Bytes.sliceD_append_middle copier runtime []

def ctorMemory : Mem := Mem.empty.write 0 runtime

theorem ctorMemory_size : ctorMemory.size = 192 := by
  rw [ctorMemory, Mem.size_write_of_size rfl (by decide) runtime_length]
  rfl

theorem ctorMemory_read : (ctorMemory.read 0 186).1 = runtime := by
  rw [← runtime_length]
  exact Mem.read_write_zero Mem.empty runtime_ne_nil

/-- The state the copier returns from. -/
def ctorPost (b : Devm) (G : Nat) : Devm :=
  returnPost (St b [0, 186] ctorMemory G) 0 186 []

theorem codecopy_charge (b : Devm) (S : List B256) (G : Nat) :
    gVerylow + gasCopy * ceilDiv (186 : B256).toNat 32 +
      (St b ((0 : B256) :: 9 :: 186 :: S) Mem.empty (G + 39)).extCost [⟨0, 186⟩] = 39 := by
  rw [St.extCost_eq rfl]
  rfl

theorem return_charge (b : Devm) (G : Nat) :
    (St b [0, 186] ctorMemory G).extCost [⟨0, 186⟩] = 0 := by
  rw [St.extCost_eq ctorMemory_size]
  rfl

theorem ctorPost_facts (b : Devm) (G : Nat) :
    (ctorPost b G).output = runtime ∧ (ctorPost b G).error = b.error ∧
    (ctorPost b G).state = b.state ∧ (ctorPost b G).gasLeft = G := by
  have h := returnPost_facts (St b [0, 186] ctorMemory G) 0 186 []
  refine ⟨?_, h.2.1, rfl, h.2.2.2⟩
  unfold ctorPost
  rw [h.1]
  have e0 : (0 : B256).toNat = 0 := rfl
  have e1 : (186 : B256).toNat = 186 := rfl
  rw [St.memory, e0, e1]
  exact ctorMemory_read

abbrev prog : List SFunc := cert.prog

theorem jumps_ok : Cert.jumpsOk code cert = true := by
  decide +kernel

/-- The copier: `PUSH1 186`, `RETURNDATASIZE` (zero in a fresh frame), `DUP2`, `PUSH1 9`,
`RETURNDATASIZE`, `CODECOPY(0, 9, 186)`, `RETURN(0, 186)`; 52 gas. -/
theorem ctor_run (sevm : Sevm) (b : Devm) (G : Nat) (hcode : sevm.code = creationCode)
    (hrd : b.returnData = []) :
    SProg.RunExact prog sevm (St b [] Mem.empty (G + 52)) (ctorPost b G) := by
  refine ⟨t_0000_c0, rfl, ?_⟩
  have hgas : G + 52 = (((((G + 39) + 2) + 3) + 3) + 2) + 3 := by omega
  have hz : b.returnData.length.toB256 = 0 := by rw [hrd]; rfl
  rw [hgas]
  unfold t_0000_c0
  refine rx_push (w := (186 : B256)) rfl (by decide) ?_
  refine rx_returndatasize (by decide) ?_
  rw [hz]
  refine rx_dup (n := 1) (w := 186) rfl (by decide) ?_
  refine rx_push (w := (9 : B256)) rfl (by decide) ?_
  refine rx_returndatasize (by decide) ?_
  rw [hz]
  refine rx_codecopy (c := 39) (M' := ctorMemory) ?_ ?_ ?_
  · exact codecopy_charge _ _ _
  · rw [hcode]
    change Mem.empty.write 0 (creationCode.sliceD 9 186 0) = ctorMemory
    rw [runtime_window]
    rfl
  · exact rx_return_any rfl (return_charge _ _)

/-- The attacker account after creation: nonce incremented, balance kept, storage empty, the
registered runtime installed. -/
def attackerAcct (W : State) (A : Adr) : Acct where
  nonce := (W.get A).nonce + 1
  bal := (W.get A).bal
  stor := Stor.empty
  code := Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.AttackerR.code

theorem runtime_code :
    (⟨⟨runtime⟩⟩ : ByteArray) = Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.AttackerR.code :=
  (fun (c : ByteArray) => show (⟨⟨c.data.toList⟩⟩ : ByteArray) = c by cases c; rfl) _

/-- **Exact attacker CREATE.** -/
theorem create_attacker (msg : Msg) (hfork : CoveredFork msg.benv.stat.fork)
    (haddress : msg.codeAddress = none) (hcode : msg.code = creationCode)
    (hvalue : msg.value = 0) (hstv : msg.shouldTransferValue = true) (hgas : 37252 ≤ msg.gas) :
    ∃ post, processCreateMessage msg = .ok post ∧ post.error = none ∧
      post.gasLeft = msg.gas - 52 - 37200 ∧
      post.state.get msg.currentTarget = attackerAcct msg.benv.state msg.currentTarget ∧
      (∀ a, a ≠ msg.currentTarget → post.state.get a = msg.benv.state.get a) ∧
      post.state = (CreateEntry.entryState msg.benv.state msg.caller msg.currentTarget).setCode
        msg.currentTarget Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.AttackerR.code := by
  obtain ⟨benv, htransfer⟩ :=
    benvAfterTransfer_exists_zero (msg := processCreateMessage.msg msg) hvalue
  let sevm := initSevm (createSeed msg benv)
  let b := initDevm (createSeed msg benv)
  let G := msg.gas - 52
  have hrun := ctor_run sevm b G hcode rfl
  have hpre : St b [] Mem.empty (G + 52) = b :=
    pre_eq_St rfl rfl (Nat.sub_add_cancel (Nat.le_trans (by decide) hgas))
  rw [hpre] at hrun
  have facts := ctorPost_facts b G
  have hprefix : (ctorPost b G).output.head? ≠ some 0xEF := by
    rw [facts.1, runtime_head]
    decide
  have hdeposit : (ctorPost b G).output.length * gasCodeDeposit ≤ (ctorPost b G).gasLeft := by
    rw [facts.1, runtime_length, facts.2.2.2]
    change 37200 ≤ msg.gas - 52
    omega
  have hmax : (ctorPost b G).output.length ≤ msg.benv.stat.rules.code.maxCodeSize := by
    rw [facts.1, runtime_length]
    exact CoveredFork.cases (motive := fun f => 186 ≤ (Fork.ruleSet f).code.maxCodeSize)
      hfork (by decide) (by decide) (by decide) (by decide)
  have hpost := liftCreate_post cert_check jumps_ok msg haddress hcode hfork htransfer hrun
    (facts.2.1.trans rfl) hprefix hdeposit hmax
  have pf := liftCreatePost_facts msg.currentTarget (ctorPost b G)
  refine ⟨_, hpost, pf.1.trans (facts.2.1.trans rfl), ?_, ?_, ?_, ?_⟩
  · rw [pf.2.1, facts.2.2.2, facts.1, runtime_length]
    rfl
  · rw [pf.2.2.1, facts.2.2.1, facts.1]
    change ({ benv.state.get msg.currentTarget with code := _ } : Acct) = _
    rw [processCreateMessage_msg_afterTransfer_get hvalue htransfer, if_pos rfl, runtime_code]
    rfl
  · intro a ha
    rw [pf.2.2.2 a ha, facts.2.2.1]
    exact (processCreateMessage_msg_afterTransfer_get hvalue htransfer a).trans (if_neg ha)
  · rw [CreateEntry.liftCreatePost_state, facts.2.2.1, facts.1, runtime_code]
    exact congrArg (fun W => State.setCode W msg.currentTarget
      Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.AttackerR.code)
      (CreateEntry.entry_state hvalue hstv htransfer)

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.AttackerR.Creation
