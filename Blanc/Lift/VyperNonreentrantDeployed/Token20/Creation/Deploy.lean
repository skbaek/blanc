import Blanc.Lift.VyperNonreentrantDeployed.Token20.Creation.Check
import Blanc.Lift.VyperNonreentrantDeployed.Token20.Check
import Blanc.Lift.Deploy
import Blanc.Lift.Vyper
import Blanc.Lift.WalkSteps
import Blanc.Lift.ExactWalkCutOps
import Blanc.Lift.CreateEntry
import Blanc.BytesWrite
import Blanc.SystemCallForward

/-! # Exact CREATE of the shared token fixture

A zero-value CREATE message whose code is the synthetic token creation input succeeds on every
covered fork: its constructor stores `balanceOf[caller] := 10^6` (slot `balSlot caller`) and
returns the registered 299-byte `Token20` runtime, which is installed at the target with exactly
that one storage entry. No other account changes. The settled world is also an explicit term of
the input world (`CreateEntry.entryState`). Message execution only: no historical inclusion. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Token20.Creation

open Jaune Blanc.Lift

/-- The registered runtime's bytes. -/
abbrev runtime : List UInt8 := Blanc.Lift.VyperNonreentrantDeployed.Token20.code.data.toList

theorem runtime_length : runtime.length = 299 := by decide +kernel

theorem runtime_ne_nil : runtime ≠ [] :=
  List.ne_nil_of_length_pos (by rw [runtime_length]; decide)

theorem runtime_head : runtime.head? = some 0x60 := by decide +kernel

/-- **The copy window is the registered runtime**: `creation[16, 16 + 299)` is `Token20.code`. -/
theorem runtime_window : creationCode.sliceD 16 299 0 = runtime := by
  rw [ByteArray.sliceD_eq, creationCode, ByteArray.toList_eq_toList_data, List.toList_toArray]
  have hp : ctorPrefix.length = 16 := rfl
  rw [← hp, ← runtime_length]
  simpa only [List.append_nil] using Bytes.sliceD_append_middle ctorPrefix runtime []

def ctorMemory : Mem := Mem.empty.write 0 runtime

theorem ctorMemory_size : ctorMemory.size = 320 := by
  rw [ctorMemory, Mem.size_write_of_size rfl (by decide) runtime_length]
  rfl

theorem ctorMemory_read : (ctorMemory.read 0 299).1 = runtime := by
  rw [← runtime_length]
  exact Mem.read_write_zero Mem.empty runtime_ne_nil

/-- The constructor's mint: `balanceOf[caller] := 10^6`. -/
abbrev mintKey (sevm : Sevm) : B256 := sevm.caller.toB256

/-- The state the constructor returns from: the mint stored, the runtime in memory. -/
def ctorPost (sevm : Sevm) (b : Devm) (G : Nat) : Devm :=
  returnPost (St (afterSstore sevm b (mintKey sevm) 1000000) [0, 299] ctorMemory G) 0 299 []

/-- The constructor's exact charge: 81 for its nine non-`SSTORE` instructions (the `CODECOPY` of
ten words with its memory expansion is 63) plus the selected `SSTORE`. -/
def ctorGas (sevm : Sevm) (b : Devm) : Nat := 81 + sstoreCost sevm b (mintKey sevm) 1000000

theorem codecopy_charge (b : Devm) (S : List B256) (G : Nat) :
    gVerylow + gasCopy * ceilDiv (299 : B256).toNat 32 +
      (St b ((0 : B256) :: 16 :: 299 :: S) Mem.empty (G + 63)).extCost [⟨0, 299⟩] = 63 := by
  rw [St.extCost_eq rfl]
  rfl

theorem return_charge (b : Devm) (G : Nat) :
    (St b [0, 299] ctorMemory G).extCost [⟨0, 299⟩] = 0 := by
  rw [St.extCost_eq ctorMemory_size]
  rfl

theorem afterSstore_returnData (sevm : Sevm) (b : Devm) (k v : B256) :
    (afterSstore sevm b k v).returnData = b.returnData := by
  unfold afterSstore; split <;> rfl

theorem ctorPost_facts (sevm : Sevm) (b : Devm) (G : Nat) :
    (ctorPost sevm b G).output = runtime ∧
    (ctorPost sevm b G).error = b.error ∧
    (ctorPost sevm b G).state = b.state.setStorVal sevm.currentTarget (mintKey sevm) 1000000 ∧
    (ctorPost sevm b G).gasLeft = G := by
  have h := returnPost_facts
    (St (afterSstore sevm b (mintKey sevm) 1000000) [0, 299] ctorMemory G) 0 299 []
  refine ⟨?_, h.2.1.trans (Blanc.afterSstore_error sevm b _ _), ?_, h.2.2.2⟩
  · unfold ctorPost
    rw [h.1]
    have e0 : (0 : B256).toNat = 0 := rfl
    have e1 : (299 : B256).toNat = 299 := rfl
    rw [St.memory, e0, e1]
    exact ctorMemory_read
  · exact Blanc.afterSstore_state sevm b _ _

theorem ctorGas_le (sevm : Sevm) (b : Devm) : ctorGas sevm b ≤ 22181 :=
  Nat.add_le_add_left (le_trans (sstoreCost_le sevm b _ _)
    (show gasColdSload + gasStorageSet ≤ 22100 by decide)) 81

abbrev prog : List SFunc := cert.prog

theorem jumps_ok : Cert.jumpsOk code cert = true := by
  decide +kernel

/-- The constructor: `PUSH3 10^6`, `CALLER`, `SSTORE`, `PUSH2 299`, `RETURNDATASIZE` (zero),
`DUP2`, `PUSH1 16`, `RETURNDATASIZE`, `CODECOPY(0, 16, 299)`, `RETURN(0, 299)`. -/
theorem ctor_run (sevm : Sevm) (b : Devm) (G : Nat)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hcode : sevm.code = creationCode) (hrd : b.returnData = []) (hsentry : gCallStipend < G) :
    SProg.RunExact prog sevm (St b [] Mem.empty (G + ctorGas sevm b)) (ctorPost sevm b G) := by
  refine ⟨t_0000_c0, rfl, ?_⟩
  have hgas : G + ctorGas sevm b =
      (((((((((G + 63) + 2) + 3) + 3) + 2) + 3) + sstoreCost sevm b (mintKey sevm) 1000000)
        + 2) + 3) := by
    unfold ctorGas
    omega
  have hz : (afterSstore sevm b (mintKey sevm) 1000000).returnData.length.toB256 = 0 := by
    rw [afterSstore_returnData, hrd]; rfl
  rw [hgas]
  unfold t_0000_c0
  refine rx_push (w := (1000000 : B256)) rfl (by decide) ?_
  refine rx_caller (by decide) ?_
  refine rx_sstore hfork ?_ hstatic ?_
  · apply Nat.lt_of_lt_of_le hsentry
    omega
  · refine rx_push (w := (299 : B256)) rfl (by decide) ?_
    refine rx_returndatasize (by decide) ?_
    rw [hz]
    refine rx_dup (n := 1) (w := 299) rfl (by decide) ?_
    refine rx_push (w := (16 : B256)) rfl (by decide) ?_
    refine rx_returndatasize (by decide) ?_
    rw [hz]
    refine rx_codecopy (c := 63) (M' := ctorMemory) ?_ ?_ ?_
    · exact codecopy_charge _ _ _
    · rw [hcode]
      change Mem.empty.write 0 (creationCode.sliceD 16 299 0) = ctorMemory
      rw [runtime_window]
      rfl
    · exact rx_return_any rfl (return_charge _ _)

/-- The selected charge of the constructor's mint on the freshly cleared target: cold unless
the message pre-warmed `(target, caller)`, valued against the block-original slot. -/
def mintSstoreGas (msg : Msg) : Nat :=
  (if (⟨msg.currentTarget, msg.caller.toB256⟩ : Adr × B256) ∈ msg.accessedStorageKeys then 0
    else gasColdSload) +
  sstoreValueCost ((msg.benv.stat.origState.get msg.currentTarget).stor.get msg.caller.toB256) 0
    1000000

/-- The token account after creation: nonce incremented, balance kept, storage the mint only,
the registered runtime installed. -/
def tokenAcct (W : State) (T creator : Adr) : Acct where
  nonce := (W.get T).nonce + 1
  bal := (W.get T).bal
  stor := Stor.empty.set creator.toB256 1000000
  code := Blanc.Lift.VyperNonreentrantDeployed.Token20.code

theorem runtime_code :
    (⟨⟨runtime⟩⟩ : ByteArray) = Blanc.Lift.VyperNonreentrantDeployed.Token20.code :=
  (fun (c : ByteArray) => show (⟨⟨c.data.toList⟩⟩ : ByteArray) = c by cases c; rfl) _

theorem runtime_deposit : runtime.length * gasCodeDeposit = 59800 := by
  rw [runtime_length]
  rfl

/-- **Exact token CREATE.** -/
theorem create_token (msg : Msg) (hfork : CoveredFork msg.benv.stat.fork)
    (haddress : msg.codeAddress = none) (hcode : msg.code = creationCode)
    (hstatic : msg.isStatic = false) (hvalue : msg.value = 0)
    (hstv : msg.shouldTransferValue = true) (hgas : 82000 ≤ msg.gas) :
    ∃ post, processCreateMessage msg = .ok post ∧ post.error = none ∧
      post.gasLeft = msg.gas - (81 + mintSstoreGas msg) - 59800 ∧
      post.state.get msg.currentTarget = tokenAcct msg.benv.state msg.currentTarget msg.caller ∧
      (∀ a, a ≠ msg.currentTarget → post.state.get a = msg.benv.state.get a) ∧
      post.state = ((CreateEntry.entryState msg.benv.state msg.caller msg.currentTarget).setStorVal
        msg.currentTarget msg.caller.toB256 1000000).setCode msg.currentTarget
          Blanc.Lift.VyperNonreentrantDeployed.Token20.code := by
  obtain ⟨benv, htransfer⟩ :=
    benvAfterTransfer_exists_zero (msg := processCreateMessage.msg msg) hvalue
  let sevm := initSevm (createSeed msg benv)
  let b := initDevm (createSeed msg benv)
  let G := msg.gas - ctorGas sevm b
  have hstat : sevm.benvStat = msg.benv.stat := by
    change benv.stat = (processCreateMessage.msg msg).benv.stat
    exact benvAfterTransfer_stat htransfer
  have hempty : b.getStor sevm.currentTarget = Stor.empty := by
    change benv.state.getStor msg.currentTarget = Stor.empty
    rw [benvAfterTransfer_ok_getStor htransfer, processCreateMessage_msg_getStor_currentTarget]
  have hsc : sstoreCost sevm b (mintKey sevm) 1000000 = mintSstoreGas msg := by
    unfold sstoreCost mintSstoreGas getOrigStorVal getOrigAcct
    rw [hstat]
    have hcur : b.getStorVal sevm.currentTarget (mintKey sevm) = 0 := by
      unfold Devm.getStorVal
      change (b.getStor sevm.currentTarget).get _ = 0
      rw [hempty]
      rfl
    rw [hcur]
    rfl
  have hcg : ctorGas sevm b = 81 + mintSstoreGas msg := by
    rw [ctorGas, hsc]
  have hcost : ctorGas sevm b ≤ msg.gas :=
    Nat.le_trans (ctorGas_le sevm b) (Nat.le_trans (by decide) hgas)
  have hremaining : 59800 ≤ G := by
    apply Nat.le_sub_of_add_le
    exact Nat.le_trans (Nat.add_le_add_left (ctorGas_le sevm b) 59800)
      (Nat.le_trans (by decide) hgas)
  have hsentry : gCallStipend < G := Nat.lt_of_lt_of_le (by decide) hremaining
  have hrun := ctor_run sevm b G (hstat ▸ hfork) hstatic hcode rfl hsentry
  have hpre : St b [] Mem.empty (G + ctorGas sevm b) = b :=
    pre_eq_St rfl rfl (Nat.sub_add_cancel hcost)
  rw [hpre] at hrun
  have facts := ctorPost_facts sevm b G
  have herror : (ctorPost sevm b G).error = none := facts.2.1.trans rfl
  have hprefix : (ctorPost sevm b G).output.head? ≠ some 0xEF := by
    rw [facts.1, runtime_head]
    decide
  have hdeposit : (ctorPost sevm b G).output.length * gasCodeDeposit ≤
      (ctorPost sevm b G).gasLeft := by
    rw [facts.1, runtime_deposit, facts.2.2.2]
    exact hremaining
  have hmax : (ctorPost sevm b G).output.length ≤ msg.benv.stat.rules.code.maxCodeSize := by
    rw [facts.1, runtime_length]
    exact CoveredFork.cases (motive := fun f => 299 ≤ (Fork.ruleSet f).code.maxCodeSize)
      hfork (by decide) (by decide) (by decide) (by decide)
  have hpost := liftCreate_post cert_check jumps_ok msg haddress hcode hfork htransfer hrun
    herror hprefix hdeposit hmax
  have pf := liftCreatePost_facts msg.currentTarget (ctorPost sevm b G)
  have hraw : (ctorPost sevm b G).state =
      benv.state.setStorVal msg.currentTarget msg.caller.toB256 1000000 := facts.2.2.1
  refine ⟨_, hpost, pf.1.trans herror, ?_, ?_, ?_, ?_⟩
  · rw [pf.2.1, facts.2.2.2, facts.1, runtime_deposit]
    show msg.gas - ctorGas sevm b - 59800 = _
    rw [hcg]
  · rw [pf.2.2.1, hraw, facts.1]
    unfold State.setStorVal
    rw [State.get_set_self, processCreateMessage_msg_afterTransfer_get hvalue htransfer,
      if_pos rfl, runtime_code]
    unfold tokenAcct
    rfl
  · intro a ha
    rw [pf.2.2.2 a ha, hraw, State.get_setStorVal_ne _ _ _ (Ne.symm ha),
      processCreateMessage_msg_afterTransfer_get hvalue htransfer, if_neg ha]
  · rw [CreateEntry.liftCreatePost_state, hraw, facts.1, runtime_code,
      CreateEntry.entry_state hvalue hstv htransfer]

end Blanc.Lift.VyperNonreentrantDeployed.Token20.Creation
