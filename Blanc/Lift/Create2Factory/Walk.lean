import Blanc.Lift.Create2Factory.Jumps
import Blanc.Lift.HistCreate
import Blanc.Lift.CreationOps
import Blanc.BytesWrite
import Blanc.DeploymentTouch

/-!
# The deterministic CREATE2 factory, as a walked message

A contract-neutral walk of the factory's 69 bytes on a non-static zero-value message whose calldata
is a salt followed by init code. The child creation is the consumer's: `factory_message` hands it
the actual child message and asks only that creating from it succeeds. Nothing here mentions the
contract being created.
-/

namespace Blanc.Lift.Create2Factory

open Jaune Blanc.Lift

local macro "room" : tactic => `(tactic| (simp only [List.length_cons, List.length_nil]; omega))

/-- The factory's Ethereum mainnet address. -/
def factoryAddress : Adr := 0x4e59b44847b379578588920ca78fbf26c0b4956c

abbrev prog : List SFunc := cert.prog

/-- The factory's first word, two's-complement `-32`. -/
def negWord : B256 := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0

/-- The factory's calldata copy of the init code. -/
def copied (init : Bytes) : Mem := Mem.empty.write 0 init

/-- Everything the factory charges before the child's grant, at a covered fork, for `n` bytes of
init code: the plain steps, the calldata copy with its memory expansion, and `CREATE2`. -/
def overhead (n : Nat) : Nat :=
  34 + (3 + gasCopy * ceilDiv n 32 + calculateMemoryGasCost (memExtSize 0 0 n)) +
    (32000 + gasKeccak256Word * ceilDiv n 32 + gasInitCodeWordCost * ceilDiv n 32)

/-- The factory's steps after a successful child: DUP1, ISZERO twice, PUSH1, JUMPI, JUMPDEST, DUP1,
DUP3, MSTORE, three POPs and two PUSH1s. -/
def tailCost : Nat := 44

section Memory

variable {init : Bytes}

theorem copied_size :
    (copied init).size = memExtSize 0 0 init.length :=
  Mem.size_write_of_size rfl (by decide) rfl

theorem copied_aligned : (copied init).size % 32 = 0 := by
  rw [copied_size]
  exact memExtSize_mod_32 (by decide)

theorem length_le_copied_size (hne : init ≠ []) : init.length ≤ (copied init).size := by
  have h := Mem.write_end_le_size Mem.empty 0 hne
  rw [Nat.zero_add] at h
  exact h

/-- The window `CREATE2` reads is the init code, whatever the extension. -/
theorem create2InitCode_copied (hne : init ≠ []) {n : B256} (hn : n.toNat = init.length) :
    create2InitCode (copied init) 0 n = init := by
  have h := Mem.read_write_zero Mem.empty hne
  change (copied init).data.sliceD 0 n.toNat 0 = init
  rw [hn]
  exact h

end Memory

/-- The whole factory walk over a successful child, stated for the machine state it starts from. -/
theorem factory_run {sevm : Sevm} {b : Devm} {salt n : B256} {init : Bytes} {G : Nat} {child : Devm}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hcreate2 : sevm.benvStat.rules.op.create2 = true)
    (hmax : sevm.benvStat.rules.creation.initCodeLimit = true →
      n.toNat ≤ sevm.benvStat.rules.code.maxInitCodeSize)
    (hstatic : sevm.isStatic = false)
    (hdata : sevm.data = salt.toBytes ++ init)
    (hvalue : sevm.value = 0)
    (hn : n.toNat = init.length) (hlen : 32 ≤ init.length)
    (hadd : (salt.toBytes ++ init).length.toB256 + negWord = n)
    (hnonce : (b.state.get sevm.currentTarget).nonce ≠ UInt64.max)
    (hdepth : sevm.depth ≠ 0)
    (hfresh : Create2TargetNoCollision
      (create2Prepared sevm b [0, n] (copied init) G 0 n
        (create2NewAddress sevm.currentTarget salt init))
      (create2NewAddress sevm.currentTarget salt init))
    (hchild : processCreateMessage (createMsg sevm
        (create2Prepared sevm b [0, n] (copied init) G 0 n
          (create2NewAddress sevm.currentTarget salt init))
        (except64th G) 0 (create2NewAddress sevm.currentTarget salt init) init) = .ok child)
    (herror : child.error = none)
    (haddr : (create2NewAddress sevm.currentTarget salt init).toB256 ≠ 0)
    (htail : tailCost ≤ G - except64th G) :
    ∃ raw, SProg.RunExact prog sevm
        (St b [] Mem.empty (G + create2ChargeH sevm (copied init) 0 n + 2 + 3 + 3 + 3 + 3 +
          (3 + gasCopy * ceilDiv n.toNat 32 + calculateMemoryGasCost (memExtSize 0 0 n.toNat)) +
          3 + 3 + 3 + 3 + 3 + 2 + 3)) raw ∧
      raw.error = b.error ∧ raw.state = child.state := by
  have hne : init ≠ [] := by
    intro h
    rw [h] at hlen
    exact absurd hlen (by decide)
  have hinit := create2InitCode_copied hne hn
  have hstep := create2_runCompiledH_of_nonce_code (sevm := sevm) (b := b) (S := [0, n])
    (M := copied init) (G := G) (v := 0) (i := 0) (sz := n) (salt := salt) (child := child)
    hsg hcreate2 hmax hstatic (B256.not_lt.mpr (B256.zero_le _)) hnonce hdepth
    (by rw [hinit]; exact hfresh) (by rw [hinit]; exact hchild) herror (by room)
  rw [hinit] at hstep
  let addr := create2NewAddress sevm.currentTarget salt init
  let b2 := incorporateChildOnSuccess
    (create2Prepared sevm b [0, n] (copied init) G 0 n addr) child []
  let M2 := (copied init).extends [⟨(0 : B256).toNat, n.toNat⟩]
  let M3 := M2.write 0 addr.toB256.toBytes
  let G3 := (G - except64th G + child.gasLeft) - tailCost
  have haligned : (copied init).size % 32 = 0 := copied_aligned
  have hcover : n.toNat ≤ (copied init).size := hn ▸ length_le_copied_size hne
  have hM2size : M2.size = (copied init).size :=
    memExtSize_of_le haligned (by show 0 + n.toNat ≤ _; rw [Nat.zero_add]; exact hcover)
  have h32 : 32 ≤ (copied init).size := hlen.trans (length_le_copied_size hne)
  have hM3size : M3.size = (copied init).size := by
    have h : (M2.write 0 addr.toB256.toBytes).size = memExtSize M2.size 0 32 :=
      Mem.size_write_of_size rfl (by rw [hM2size]; exact haligned) (B256.length_toBytes _)
    rw [hM2size] at h
    exact h.trans (memExtSize_of_le haligned (by omega))
  have hpost : create2Post (create2Prepared sevm b [0, n] (copied init) G 0 n addr) child addr =
      St b2 [addr.toB256, 0, n] M2 (G3 + 3 + 3 + 2 + 2 + 2 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3) := by
    have hgas : G3 + 3 + 3 + 2 + 2 + 2 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 =
        G - except64th G + child.gasLeft := by
      have h : 44 ≤ G - except64th G := htail
      show (G - except64th G + child.gasLeft) - 44 + _ + _ + _ + _ + _ + _ + _ + _ + _ + _ + _ + _ + _ + _ = _
      omega
    rw [hgas]
    rfl
  refine ⟨returnPost (St b2 [12, 20] M3 G3) 12 20 [], ⟨t_0000_c0, rfl, ?_⟩, rfl, rfl⟩
  unfold t_0000_c0
  refine rx_push (w := negWord) (by decide) (by room) ?_
  refine rx_calldatasize (by room) ?_
  rw [hdata]
  refine rx_add' hadd (by room) ?_
  refine rx_push (w := 0) (by decide) (by room) ?_
  refine rx_dup (n := 1) rfl (by room) ?_
  refine rx_push (w := 32) (by decide) (by room) ?_
  refine rx_dup (n := 2) rfl (by room) ?_
  refine rx_calldatacopy (M' := copied init) ?_ ?_ ?_
  · rw [St.extCost_eq rfl]
    rfl
  · have hs : (salt.toBytes ++ init).sliceD 32 init.length 0 = init := by
      have h := Bytes.sliceD_append_middle salt.toBytes init []
      rw [List.append_nil, B256.length_toBytes] at h
      exact h
    rw [hdata]
    change Mem.empty.write 0 ((salt.toBytes ++ init).sliceD 32 n.toNat 0) = _
    rw [hn, hs]
    rfl
  refine rx_dup (n := 0) rfl (by room) ?_
  refine rx_calldataload (by room) ?_
  have hword : Sevm.dataWord sevm 0 = salt := by
    have h := Bytes.sliceD_append_middle [] salt.toBytes init
    rw [List.nil_append, B256.length_toBytes] at h
    unfold Sevm.dataWord
    rw [hdata]
    exact (congrArg Bytes.toB256 h).trans (B256.toB256_toBytes _)
  rw [hword]
  refine rx_dup (n := 2) rfl (by room) ?_
  refine rx_dup (n := 2) rfl (by room) ?_
  refine rx_callvalue (by room) ?_
  rw [hvalue]
  refine .next hstep ?_
  rw [hpost]
  refine rx_dup (n := 0) rfl (by room) ?_
  refine rx_iszero (v := 0) (ite_eq_right haddr) (by room) ?_
  refine rx_iszero (v := 1) (by decide) (by room) ?_
  refine rx_push (w := 0x39) (by decide) (by room) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0039_c0
  refine rx_dest ?_
  refine rx_dup (n := 0) rfl (by room) ?_
  refine rx_dup (n := 2) rfl (by room) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · rw [St.extCost_eq hM2size, memExtSize_of_le haligned (by show 0 + 32 ≤ _; omega), Nat.sub_self]
    rfl
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_push (w := 20) (by decide) (by room) ?_
  refine rx_push (w := 12) (by decide) (by room) ?_
  refine rx_return_any rfl ?_
  change (St b2 [12, 20] M3 G3).extCost [⟨(12 : B256).toNat, (20 : B256).toNat⟩] = 0
  rw [St.extCost_eq hM3size, memExtSize_of_le haligned (by show 12 + 20 ≤ _; omega), Nat.sub_self]

/-- What the covered forks' rules give the factory walk. -/
theorem covered_rules {s : BenvStat} (hfork : CoveredFork s.fork) :
    s.rules.op.create2 = true ∧ s.rules.creation.initCodeLimit = true ∧
      s.rules.gas.createAccess = 32000 ∧ s.rules.code.maxInitCodeSize = 49152 ∧
      ¬ s.rules.isPrecomp factoryAddress :=
  hfork.cases
    (motive := fun f => (Fork.ruleSet f).op.create2 = true ∧
      (Fork.ruleSet f).creation.initCodeLimit = true ∧
      (Fork.ruleSet f).gas.createAccess = 32000 ∧ (Fork.ruleSet f).code.maxInitCodeSize = 49152 ∧
      ¬ (Fork.ruleSet f).isPrecomp factoryAddress)
    ⟨rfl, rfl, rfl, rfl, by decide⟩ ⟨rfl, rfl, rfl, rfl, by decide⟩
    ⟨rfl, rfl, rfl, rfl, by decide⟩ ⟨rfl, rfl, rfl, rfl, by decide⟩

/-- Input identification of a factory message: the factory's code running at its address, on a
non-static zero-value message whose calldata is `salt` then `init`. No creation outcome is here. -/
structure FactoryMessage (msg : Msg) (salt : B256) (init : Bytes) : Prop where
  currentTarget : msg.currentTarget = factoryAddress
  code : msg.code = Blanc.Lift.Create2Factory.code
  codeAddress : msg.codeAddress = some factoryAddress
  data : msg.data = salt.toBytes ++ init
  value : msg.value = 0
  isStatic : msg.isStatic = false
  depth : msg.depth ≠ 0
  nonce : (msg.benv.state.get factoryAddress).nonce ≠ UInt64.max

/-- What the factory guarantees of the child creation message it builds. -/
structure ChildMessage (cm : Msg) (init : Bytes) (addr : Adr) (parent : Msg) : Prop where
  codeAddress : cm.codeAddress = none
  code : cm.code = ⟨⟨init⟩⟩
  currentTarget : cm.currentTarget = addr
  isStatic : cm.isStatic = false
  value : cm.value = 0
  stat : cm.benv.stat = parent.benv.stat
  nonce : (cm.benv.state.get addr).nonce = 0

/-- **The factory message.** If creating from the child message succeeds with `P`, the factory
message succeeds with the child's world. The target's freshness is the actual collision check's
input; its code, storage and nonce afterwards are `P`'s, proved by the consumer. -/
theorem factory_message {msg : Msg} {salt n : B256} {init : Bytes} {P : Devm → Prop} {need : Nat}
    (h : FactoryMessage msg salt init)
    (hfork : CoveredFork msg.benv.stat.fork)
    (hn : n.toNat = init.length) (hlen : 32 ≤ init.length) (hmax : init.length ≤ 49152)
    (hadd : (salt.toBytes ++ init).length.toB256 + negWord = n)
    (hne : create2NewAddress factoryAddress salt init ≠ factoryAddress)
    (hnz : (create2NewAddress factoryAddress salt init).toB256 ≠ 0)
    (hnonce0 : (msg.benv.state.get (create2NewAddress factoryAddress salt init)).nonce = 0)
    (hcode0 : (msg.benv.state.get (create2NewAddress factoryAddress salt init)).code.size = 0)
    (hgas : overhead init.length + 2816 ≤ msg.gas)
    (hneed : need ≤ except64th (msg.gas - overhead init.length))
    (ctor : ∀ cm, ChildMessage cm init (create2NewAddress factoryAddress salt init) msg →
      need ≤ cm.gas → ∃ child, processCreateMessage cm = .ok child ∧ child.error = none ∧ P child) :
    ∃ post child, processMessage msg = .ok post ∧ post.error = none ∧
      post.state = child.state ∧ P child := by
  have hsg : msg.benv.stat.rules.stateGas = none := hfork.rules_stateGas_none
  obtain ⟨hc2, hlim, hacc, hmaxRule, hnp⟩ := covered_rules hfork
  obtain ⟨G, hG⟩ : ∃ G, G = msg.gas - overhead init.length := ⟨_, rfl⟩
  rw [← hG] at hneed
  have hctS : (initSevm msg).currentTarget = factoryAddress := h.currentTarget
  have haddrEq : create2NewAddress (initSevm msg).currentTarget salt init =
      create2NewAddress factoryAddress salt init := by rw [hctS]
  have hget : (create2Prepared (initSevm msg) (initDevm msg) [0, n] (copied init) G 0 n
      (create2NewAddress factoryAddress salt init)).state.get
        (create2NewAddress factoryAddress salt init) =
      msg.benv.state.get (create2NewAddress factoryAddress salt init) := by
    change (msg.benv.state.incrNonce (initSevm msg).currentTarget).get _ = _
    rw [hctS]
    unfold State.incrNonce
    exact State.setAccount_get_ne _ (Ne.symm hne) _
  have hchildNonce : ((create2Prepared (initSevm msg) (initDevm msg) [0, n] (copied init) G 0 n
      (create2NewAddress factoryAddress salt init)).state.get
        (create2NewAddress factoryAddress salt init)).nonce = 0 := by
    rw [hget]
    exact hnonce0
  obtain ⟨child, hchild, herror, hP⟩ := ctor
    (createMsg (initSevm msg)
      (create2Prepared (initSevm msg) (initDevm msg) [0, n] (copied init) G 0 n
        (create2NewAddress factoryAddress salt init))
      (except64th G) 0 (create2NewAddress factoryAddress salt init) init)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, hchildNonce⟩ hneed
  have htail : tailCost ≤ G - except64th G := by
    unfold tailCost except64th
    omega
  obtain ⟨raw, hrun, herr, hstate⟩ := factory_run (sevm := initSevm msg) (b := initDevm msg)
    (salt := salt) (n := n) (init := init) (G := G) (child := child)
    hsg hc2 (fun _ => by
      change n.toNat ≤ msg.benv.stat.rules.code.maxInitCodeSize
      rw [hn, hmaxRule]
      exact hmax) h.isStatic h.data h.value hn hlen hadd
    (by rw [hctS]; exact h.nonce) h.depth
    (by
      rw [haddrEq]
      exact ⟨by rw [hget]; exact hnonce0, by rw [hget]; exact hcode0⟩)
    (by rw [haddrEq]; exact hchild) herror (by rw [haddrEq]; exact hnz) htail
  have hne0 : init ≠ [] := by
    intro hnil
    rw [hnil] at hlen
    exact absurd hlen (by decide)
  have hcharge : create2ChargeH (initSevm msg) (copied init) 0 n =
      32000 + gasKeccak256Word * ceilDiv init.length 32 +
        gasInitCodeWordCost * ceilDiv init.length 32 := by
    have hmem : memExtsSize (copied init).size [⟨(0 : B256).toNat, n.toNat⟩] = (copied init).size :=
      memExtSize_of_le copied_aligned (by
        show 0 + n.toNat ≤ _
        rw [Nat.zero_add, hn]
        exact length_le_copied_size hne0)
    unfold create2ChargeH
    rw [hmem, Nat.sub_self, hn]
    change msg.benv.stat.rules.gas.createAccess + _ + 0 +
      (if msg.benv.stat.rules.creation.initCodeLimit = true then _ else 0) = _
    rw [hacc, hlim, ite_eq_left rfl, Nat.add_zero]
  have htotal : G + create2ChargeH (initSevm msg) (copied init) 0 n + 2 + 3 + 3 + 3 + 3 +
      (3 + gasCopy * ceilDiv n.toNat 32 + calculateMemoryGasCost (memExtSize 0 0 n.toNat)) +
      3 + 3 + 3 + 3 + 3 + 2 + 3 = msg.gas := by
    rw [hcharge, hn, hG]
    unfold overhead at hgas ⊢
    omega
  have hpre : St (initDevm msg) [] Mem.empty
      (G + create2ChargeH (initSevm msg) (copied init) 0 n + 2 + 3 + 3 + 3 + 3 +
        (3 + gasCopy * ceilDiv n.toNat 32 + calculateMemoryGasCost (memExtSize 0 0 n.toNat)) +
        3 + 3 + 3 + 3 + 3 + 2 + 3) = initDevm msg := by
    rw [htotal]
    exact (St.self rfl rfl).symm
  rw [hpre] at hrun
  obtain ⟨exc⟩ := lift_exact_noStateGas cert_check jumps_ok (sevm := initSevm msg) h.code hsg hrun
  have hexec : exec (initEvm msg) = .ok raw := (exec_iff_exec_eq _ _ _ _).mp ⟨exc⟩
  have hrawError : raw.error = none := herr
  refine ⟨raw.recordTouch msg.benv.stat.rules true msg.currentTarget, child, ?_,
    (Devm.recordTouch_error raw _ _ _).trans hrawError,
    (Devm.recordTouch_state raw _ _ _).trans hstate, hP⟩
  rw [MessageExecution.processMessage_eq_settle_exec_afterTransfer_of_notPrecompile msg msg.benv
    factoryAddress (Msg.benvAfterTransfer_of_value_zero h.value) h.codeAddress hnp]
  change (Frame.ofCall msg).settle (exec (initEvm msg)) = _
  rw [hexec]
  simp only [Frame.settle, Frame.settleMsg, Frame.ofCall, executeCode.handleErrorWith_ok,
    Bool.false_eq_true, ↓reduceIte, processMessage.settle, Except.bind_ok,
    hrawError, Option.isSome_none]

/-- **A factory deployment.** The factory message installs what its child creation installs, at the
computed address, with nonce one. Code, storage and nonce come from the consumer's checked creation;
the premises on the target are the actual collision check's. -/
theorem factory_install {msg : Msg} {salt n : B256} {init : Bytes} {addr : Adr} {runtime : ByteArray}
    {stor : Stor} {need : Nat}
    (h : FactoryMessage msg salt init)
    (hfork : CoveredFork msg.benv.stat.fork)
    (hn : n.toNat = init.length) (hlen : 32 ≤ init.length) (hmax : init.length ≤ 49152)
    (hadd : (salt.toBytes ++ init).length.toB256 + negWord = n)
    (haddr : create2NewAddress factoryAddress salt init = addr)
    (hne : addr ≠ factoryAddress) (hnz : addr.toB256 ≠ 0)
    (hnonce0 : (msg.benv.state.get addr).nonce = 0)
    (hcode0 : (msg.benv.state.get addr).code.size = 0)
    (hgas : overhead init.length + 2816 ≤ msg.gas)
    (hneed : need ≤ except64th (msg.gas - overhead init.length))
    (create : ∀ cm, ChildMessage cm init addr msg → need ≤ cm.gas →
      ∃ post, processCreateMessage cm = .ok post ∧ post.error = none ∧
        post.getCode cm.currentTarget = runtime ∧ post.getStor cm.currentTarget = stor ∧
        (post.state.get cm.currentTarget).nonce = (cm.benv.state.get cm.currentTarget).nonce + 1) :
    ∃ post, processMessage msg = .ok post ∧ post.error = none ∧
      post.state.getCode addr = runtime ∧ post.state.getStor addr = stor ∧
      post.state.getNonce addr = 1 := by
  subst haddr
  obtain ⟨post, child, hmsg, herror, hstate, hcodeP, hstorP, hnonceP⟩ :=
    factory_message (msg := msg) (salt := salt) (n := n) (init := init)
      (P := fun child => child.state.getCode (create2NewAddress factoryAddress salt init) = runtime ∧
        child.state.getStor (create2NewAddress factoryAddress salt init) = stor ∧
        child.state.getNonce (create2NewAddress factoryAddress salt init) = 1)
      (need := need) h hfork hn hlen hmax hadd hne hnz hnonce0 hcode0 hgas hneed
      (fun cm hcm hcmgas => by
        obtain ⟨child, hchild, herr, hc, hs, hnonce⟩ := create cm hcm hcmgas
        rw [hcm.currentTarget] at hc hs hnonce
        exact ⟨child, hchild, herr, hc, hs, by
          change (child.state.get _).nonce = 1
          rw [hnonce, hcm.nonce]
          rfl⟩)
  exact ⟨post, hmsg, herror, by rw [hstate]; exact hcodeP, by rw [hstate]; exact hstorP,
    by rw [hstate]; exact hnonceP⟩

end Blanc.Lift.Create2Factory
