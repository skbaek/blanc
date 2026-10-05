import Blanc.OwnerDiscipline
import Blanc.Lift.Deploy
import Blanc.Lift.CreationOps
import Blanc.Lift.ExactWalkOps
import Blanc.BytesWrite
import Blanc.TransactionForward
import Blanc.Lift.CreateEntry

/-! # Creation of an EIP-1167 clone by a 9-byte copier, for any implementation

`creationCode I` is a 9-byte copier `602d3d8160093d39f3` followed by the 45-byte EIP-1167
forwarder `Blanc.forwarderCode I`. Run as a zero-value CREATE, the copier returns the forwarder,
so the target gets exactly `forwarderCode I` with empty storage, for 28 gas of execution and
9000 of code deposit.

This is a modeled creation harness, not any historical factory: a consumer that registers such an
input must label it synthetic. The certificate of the copier is the producer's; `create` takes its
check for the consumer's input (`Cert.check (creationCode I) copierCert = true`, decided by the
registered generated `Check.lean`), so nothing here trusts the producer. -/

namespace Blanc.Lift.Clone1167

open Jaune Blanc.Lift

/-- `PUSH1 45 RETURNDATASIZE DUP2 PUSH1 9 RETURNDATASIZE CODECOPY RETURN`: copy
`code[9, 54)` to memory 0 and return it. -/
def copier : List UInt8 := [0x60, 0x2d, 0x3d, 0x81, 0x60, 0x09, 0x3d, 0x39, 0xf3]

/-- The clone creation input for implementation `I`. -/
def creationCode (I : Adr) : ByteArray :=
  ⟨(copier ++ (Blanc.forwarderCode I).data.toList).toArray⟩

/-- The copier's single straight-line node, as the lift producer emits it. -/
def copierFunc : SFunc := (.next (.push [0x2d] (by decide)) (.next (.reg .returndatasize)
  (.next (.reg (.dup 1)) (.next (.push [0x09] (by decide)) (.next (.reg .returndatasize)
  (.next (.reg .codecopy) (.last .return_)))))))

/-- The copier's certificate: one entry at pc 0. -/
def copierCert : Cert := [(⟨0x0, [], 0⟩, copierFunc)]

/-- The forwarder runtime's bytes. -/
abbrev forwarder (I : Adr) : List UInt8 := (Blanc.forwarderCode I).data.toList

theorem forwarder_length (I : Adr) : (forwarder I).length = 45 := rfl

theorem forwarder_head (I : Adr) : (forwarder I).head? = some 0x36 := rfl

/-- **The copy window is the forwarder to `I`**: `creationCode I [9, 54)`. -/
theorem forwarder_window (I : Adr) : (creationCode I).sliceD 9 45 0 = forwarder I := by
  rw [ByteArray.sliceD_eq, creationCode, ByteArray.toList_eq_toList_data,
    List.toList_toArray]
  have hp : copier.length = 9 := rfl
  rw [← hp, ← forwarder_length I]
  simpa only [List.append_nil] using Bytes.sliceD_append_middle copier (forwarder I) []

/-- The copier's memory once it has copied the forwarder. -/
def memory (I : Adr) : Mem := Mem.empty.write 0 (forwarder I)

theorem memory_size (I : Adr) : (memory I).size = 64 := by
  rw [memory, Mem.size_write_of_size rfl (by decide) (forwarder_length I)]
  rfl

theorem memory_read (I : Adr) : ((memory I).read 0 45).1 = forwarder I := by
  rw [← forwarder_length I]
  exact Mem.read_write_zero Mem.empty
    (List.ne_nil_of_length_pos (by rw [forwarder_length]; decide))

/-- The state the copier returns from. -/
def post (I : Adr) (b : Devm) (G : Nat) : Devm :=
  returnPost (St b [0, 45] (memory I) G) 0 45 []

/-- The copier's `CODECOPY(0, 9, 45)` costs 15 into fresh memory, whatever lies below. -/
theorem codecopy_charge (b : Devm) (S : List B256) (G : Nat) :
    gVerylow + gasCopy * ceilDiv (45 : B256).toNat 32 +
      (St b ((0 : B256) :: 9 :: 45 :: S) Mem.empty (G + 15)).extCost [⟨0, 45⟩] = 15 := by
  rw [St.extCost_eq rfl]
  rfl

theorem return_charge (I : Adr) (b : Devm) (G : Nat) :
    (St b [0, 45] (memory I) G).extCost [⟨0, 45⟩] = 0 := by
  rw [St.extCost_eq (memory_size I)]
  rfl

theorem post_facts (I : Adr) (b : Devm) (G : Nat) :
    (post I b G).output = forwarder I ∧ (post I b G).error = b.error ∧
    (post I b G).state = b.state ∧ (post I b G).gasLeft = G := by
  have h := returnPost_facts (St b [0, 45] (memory I) G) 0 45 []
  refine ⟨?_, h.2.1, rfl, h.2.2.2⟩
  unfold post
  rw [h.1]
  have e0 : (0 : B256).toNat = 0 := rfl
  have e1 : (45 : B256).toNat = 45 := rfl
  rw [St.memory, e0, e1]
  exact memory_read I

theorem jumps_ok (code : ByteArray) : Cert.jumpsOk code copierCert = true := by
  rfl

/-- The copier: `PUSH1 45`, `RETURNDATASIZE` (zero in a fresh frame), `DUP2`, `PUSH1 9`,
`RETURNDATASIZE`, `CODECOPY(0, 9, 45)`, `RETURN(0, 45)`; 28 gas. -/
theorem run (I : Adr) (sevm : Sevm) (b : Devm) (G : Nat) (hcode : sevm.code = creationCode I)
    (hrd : b.returnData = []) :
    SProg.RunExact copierCert.prog sevm (St b [] Mem.empty (G + 28)) (post I b G) := by
  refine ⟨copierFunc, rfl, ?_⟩
  have hgas : G + 28 = (((((G + 15) + 2) + 3) + 3) + 2) + 3 := by omega
  have hz : b.returnData.length.toB256 = 0 := by rw [hrd]; rfl
  rw [hgas]
  unfold copierFunc
  refine rx_push (w := (45 : B256)) rfl (by decide) ?_
  refine rx_returndatasize (by decide) ?_
  rw [hz]
  refine rx_dup (n := 1) (w := 45) rfl (by decide) ?_
  refine rx_push (w := (9 : B256)) rfl (by decide) ?_
  refine rx_returndatasize (by decide) ?_
  rw [hz]
  refine rx_codecopy (c := 15) (M' := memory I) ?_ ?_ ?_
  · exact codecopy_charge _ _ _
  · rw [hcode]
    change Mem.empty.write 0 ((creationCode I).sliceD 9 45 0) = memory I
    rw [forwarder_window]
    rfl
  · exact rx_return_any rfl (return_charge I _ _)

/-- The clone account after creation: nonce incremented, balance kept, storage empty, the
forwarder to `I` installed. -/
def cloneAcct (I : Adr) (W : State) (P : Adr) : Acct where
  nonce := (W.get P).nonce + 1
  bal := (W.get P).bal
  stor := Stor.empty
  code := Blanc.forwarderCode I

/-- **Clone CREATE, any implementation**: given the certificate check of the consumer's
registered input, a zero-value CREATE of `creationCode I` succeeds on every covered fork, leaves
`msg.gas - 28 - 9000`, installs `forwarderCode I` with empty storage at its target and changes no
other account. -/
theorem create (I : Adr) {c : Cert} (hc : c = copierCert)
    (hcheck : Cert.check (creationCode I) c = true) (msg : Msg)
    (hfork : CoveredFork msg.benv.stat.fork) (haddress : msg.codeAddress = none)
    (hcode : msg.code = creationCode I) (hvalue : msg.value = 0)
    (hstv : msg.shouldTransferValue = true) (hgas : 9028 ≤ msg.gas) :
    ∃ post, processCreateMessage msg = .ok post ∧ post.error = none ∧
      post.gasLeft = msg.gas - 28 - 9000 ∧
      post.state.get msg.currentTarget = cloneAcct I msg.benv.state msg.currentTarget ∧
      (∀ a, a ≠ msg.currentTarget → post.state.get a = msg.benv.state.get a) ∧
      post.state = (CreateEntry.entryState msg.benv.state msg.caller msg.currentTarget).setCode
        msg.currentTarget (Blanc.forwarderCode I) := by
  subst hc
  obtain ⟨benv, htransfer⟩ :=
    benvAfterTransfer_exists_zero (msg := processCreateMessage.msg msg) hvalue
  let sevm := initSevm (createSeed msg benv)
  let b := initDevm (createSeed msg benv)
  let G := msg.gas - 28
  have hrun := run I sevm b G hcode rfl
  have hpre : St b [] Mem.empty (G + 28) = b :=
    pre_eq_St rfl rfl (Nat.sub_add_cancel (Nat.le_trans (by decide) hgas))
  rw [hpre] at hrun
  have facts := post_facts I b G
  have hprefix : (Clone1167.post I b G).output.head? ≠ some 0xEF := by
    rw [facts.1, forwarder_head]
    decide
  have hdeposit : (Clone1167.post I b G).output.length * gasCodeDeposit ≤
      (Clone1167.post I b G).gasLeft := by
    rw [facts.1, forwarder_length, facts.2.2.2]
    change 9000 ≤ msg.gas - 28
    omega
  have hmax : (Clone1167.post I b G).output.length ≤ msg.benv.stat.rules.code.maxCodeSize := by
    rw [facts.1, forwarder_length]
    exact CoveredFork.cases (motive := fun f => 45 ≤ (Fork.ruleSet f).code.maxCodeSize)
      hfork (by decide) (by decide) (by decide) (by decide)
  have hpost := liftCreate_post hcheck (jumps_ok _) msg haddress hcode hfork htransfer hrun
    (facts.2.1.trans rfl) hprefix hdeposit hmax
  have pf := liftCreatePost_facts msg.currentTarget (Clone1167.post I b G)
  refine ⟨_, hpost, pf.1.trans (facts.2.1.trans rfl), ?_, ?_, ?_, ?_⟩
  · rw [pf.2.1, facts.2.2.2, facts.1, forwarder_length]
    rfl
  · rw [pf.2.2.1, facts.2.2.1, facts.1]
    change ({ benv.state.get msg.currentTarget with code := _ } : Acct) = _
    rw [processCreateMessage_msg_afterTransfer_get hvalue htransfer, if_pos rfl]
    rfl
  · intro a ha
    rw [pf.2.2.2 a ha, facts.2.2.1]
    exact (processCreateMessage_msg_afterTransfer_get hvalue htransfer a).trans (if_neg ha)
  · rw [CreateEntry.liftCreatePost_state, facts.2.2.1, facts.1]
    exact congrArg (fun W => State.setCode W msg.currentTarget (Blanc.forwarderCode I))
      (CreateEntry.entry_state hvalue hstv htransfer)

end Blanc.Lift.Clone1167
