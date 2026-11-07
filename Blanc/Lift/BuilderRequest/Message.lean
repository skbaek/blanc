import Blanc.Lift.BuilderRequest.UserFrameAmsterdam
import Blanc.Lift.SystemCallAmsterdam

/-!
# The builder contracts' direct messages under Amsterdam

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

`Submissions` is what the top-level path needs of a builder contract's submission, and each contract gives it.
`Submissions.message_ok` takes one direct message through `processMessageCall`, on any state-gas meter, an empty
reservoir included: post state, logs in order (the EIP-7708 transfer log `initDevm` seeded, then the frame's
`LOG0`), and gas. `Submissions.message_inverse` is the converse: every successful direct message at the code is a
submission or a fee read. Direct calls only: no nested frames here, no history, and no statement about what other
transactions did.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune

/-- Amsterdam's state-gas record. -/
local notation "A" => amsterdamStateGasRules

/-- `Fresh` passes through a machine-register replacement. -/
theorem _root_.Blanc.Lift.Fresh.st {sevm : Sevm} {d : Devm} {ks : List B256} {grant used n : Nat}
    (r : Fresh sevm d ks grant used n) (S : List B256) (M : Mem) (G : Nat) :
    Fresh sevm (St d S M G) ks grant used n :=
  ⟨r.error, r.refund, r.deleted, r.clean, r.drawn, r.ledger, r.committed, r.budget⟩

/-- One store at an untouched slot: `Fresh` goes on, with the rest of the keys, and it repays no spill. -/
theorem _root_.Blanc.Lift.Fresh.step {sevm : Sevm} {d : Devm} {k : B256} {ks : List B256} {grant used n : Nat}
    (r : Fresh sevm d (k :: ks) grant used n) (nodup : (k :: ks).Nodup) (v : B256) :
    (∃ used', Fresh sevm (afterSstoreA A sevm d k v) ks grant used' n) ∧ ks.Nodup ∧
      sstoreRepayA A sevm d k v = 0 :=
  ⟨⟨_, r.sstore (List.nodup_cons.mp nodup).1 v⟩, (List.nodup_cons.mp nodup).2,
    Fresh.repay_zero v (r.clean k List.mem_cons_self)⟩

/-- The bound one store puts on what it takes from `gasLeft`: execution gas and at most one `STORAGE_SET` of
state gas. -/
theorem writeCharge_le (sevm : Sevm) (b : Devm) (k x : B256) :
    (amsterdamSteps sevm).writeCharge b k x ≤ (gasColdSload + amsterdamStateGasRules.storageWrite) + amsterdamStateGasRules.storageSet := by
  show sstoreCostA A sevm b k x + sstoreSpillA A sevm b k x ≤ _
  have hc := sstoreCostA_le A sevm b k x
  have hs := sstoreChargeA_le A sevm b k x
  have : sstoreSpillA A sevm b k x ≤ sstoreChargeA A sevm b k x := Nat.sub_le _ _
  omega

theorem sloadCost_le (sevm : Sevm) (b : Devm) (k : B256) : sloadCost sevm b k ≤ gasColdSload := by
  unfold sloadCost
  have : gasWarmAccess ≤ gasColdSload := by decide
  split <;> omega

/-- The quoted excess, from the contract's storage: `slot0 + max(0, count - target)`. -/
def storageExcess (target : B256) (σ : Stor) : B256 := targetExcess target (σ.get 0) (σ.get 1)

/-- What a builder contract's submission gives the top-level path, under Amsterdam. -/
structure Submissions extends UserFrames where
  nonempty : code.isEmpty = false
  undelegated : getDelegatedCodeAddress code = none
  /-- The calldata length of a submission. -/
  len : Nat
  /-- The per-block target of the fee. -/
  target : B256
  /-- The number of `SSTORE`s a submission makes. -/
  stores : Nat
  /-- The number of `SLOAD`s a submission makes. -/
  loads : Nat
  /-- A submission's fixed regular gas, beside its fee loop, `SLOAD`s and `SSTORE`s: opcodes, memory, the log. -/
  fixed : Nat
  /-- What the guards accept: from the calldata, the value and the quoted fee. -/
  Admit : Bytes → B256 → B256 → Prop
  /-- The machine a submission leaves. -/
  Post : Sevm → Devm → Mem → Nat → Devm
  /-- All a submission takes from `gasLeft`. -/
  Gas : Sevm → Devm → Mem → Nat → Nat
  /-- What its stores return to `gasLeft`. -/
  Repay : Sevm → Devm → Mem → Nat
  /-- Its `LOG0`. -/
  log : Sevm → Log
  /-- The world it leaves, stated at the account level over the state it ran on. -/
  world : Sevm → State → State
  /-- The slots it writes, in order, at tail word `t`. -/
  keys : B256 → List B256
  exec : ∀ {s : Sevm} {b : Devm} {M : Mem} {G n : Nat} {out : B256}, s.code = code →
    s.benvStat.fork = .amsterdam → s.caller ≠ systemAddress → s.data.length = len → s.isStatic = false →
    gCallStipend < G → b.getStorVal s.currentTarget 0 ≠ B256.max →
    WordFakeExponential.Run (storedExcess target s b) 17 1 17 0 n out →
    Admit s.data s.value (out / (17 : B256)) →
    Nonempty (Exec 0 s (St b [] M (G + Gas s b M n)) (.ok (Post s b M (G + Repay s b M))))
  fresh : ∀ {s : Sevm} {b : Devm} {M : Mem} {G grant used : Nat}, s.benvStat.fork = .amsterdam →
    Fresh s b (keys (b.getStorVal s.currentTarget 3)) grant used stores →
    (keys (b.getStorVal s.currentTarget 3)).Nodup →
    (∃ used', Fresh s (Post s b M G) [] grant used' stores) ∧ Repay s b M = 0
  keys_length : ∀ t, (keys t).length = stores
  nodup : ∀ t : B256, t.toNat < 2 ^ 253 → (keys t).Nodup
  gasLeft : ∀ {s : Sevm} {b : Devm} {M : Mem} {G : Nat}, (Post s b M G).gasLeft = G
  state : ∀ {s : Sevm} {b : Devm} {M : Mem} {G : Nat}, s.benvStat.fork = .amsterdam →
    (Post s b M G).state = world s b.state
  logs : ∀ {s : Sevm} {b : Devm} {G : Nat}, s.benvStat.fork = .amsterdam → s.data.length = len →
    (Post s b .empty G).logs = b.logs ++ [log s]
  gas_le : ∀ (s : Sevm) (b : Devm) (n : Nat),
    Gas s b .empty n ≤ fixed + 87 * n + loads * gasColdSload +
      stores * (gasColdSload + amsterdamStateGasRules.storageWrite) + stores * amsterdamStateGasRules.storageSet

namespace Submissions

variable (c : Submissions)

/-- A submission's bound on what it takes from `gasLeft`, split: regular gas, state gas excluded. `n` is the fee
recurrence's iteration count. -/
def regularBound (n : Nat) : Nat :=
  c.fixed + 87 * n + c.loads * gasColdSload + c.stores * (gasColdSload + amsterdamStateGasRules.storageWrite)

/-- A submission's bound on state gas. -/
def stateBound : Nat := c.stores * amsterdamStateGasRules.storageSet

theorem gas_le_bound (s : Sevm) (b : Devm) (n : Nat) :
    c.Gas s b .empty n ≤ c.regularBound n + c.stateBound := c.gas_le s b n

end Submissions

variable {M : Msg} {benv : Benv}

/-- The entry transfer keeps the transaction's created accounts. -/
theorem benvAfterTransfer_createdAccounts (entry : M.benvAfterTransfer = .ok benv) :
    benv.createdAccounts = M.benv.createdAccounts := by
  unfold Msg.benvAfterTransfer at entry
  split at entry
  · rcases Except.bind_eq_ok entry with ⟨b, hb, hok⟩
    cases hok
    unfold Option.toExcept at hb
    split at hb
    · cases hb
    · cases hb
      rename_i w hw
      unfold Benv.subBal at hw
      rcases Option.bind_eq_some_iff.mp hw with ⟨st, hst, hb2⟩
      cases hb2
      rfl
  · cases entry
    rfl

/-- An account whose code is nonempty keeps its storage through the entry transfer. -/
theorem entry_stor {code : ByteArray} (installed : M.benv.state.getCode M.currentTarget = code)
    (hnonempty : code.isEmpty = false) (entry : M.benvAfterTransfer = .ok benv) :
    benv.state.getStor M.currentTarget = M.benv.state.getStor M.currentTarget := by
  refine benvAfterTransfer_ok_getStor entry _ (Or.inr (Or.inr ?_))
  intro h
  have hcode : (M.benv.state.get M.currentTarget).code = code := installed
  rw [hcode] at h
  have : code.isEmpty = true := by
    simp only [ByteArray.isEmpty, h]
    rfl
  rw [this] at hnonempty
  cases hnonempty

namespace Submissions

variable (c : Submissions)

/-- The frame's static environment at a message to the code. -/
local notation "S" => userSevm M c.code benv

/-- The frame's entry machine. -/
local notation "E" => userEntry M benv

/-- The entry machine keeps the frame `Fresh`, when the target was not created in this transaction and its storage
is its storage at the transaction's start. -/
theorem entry_fresh {code : ByteArray} (hnew : M.currentTarget ∉ M.benv.createdAccounts)
    (origin : (M.benv.stat.origState.get M.currentTarget).stor = (M.benv.state.get M.currentTarget).stor)
    (installed : M.benv.state.getCode M.currentTarget = code) (hnonempty : code.isEmpty = false)
    (entry : M.benvAfterTransfer = .ok benv) (inherited : M.inheritedDeletions.toList = []) (n : Nat)
    (keys : List B256) (hlen : keys.length = n) :
    Fresh (userSevm M code benv) (userEntry M benv) keys M.stateGasGrant 0 n where
  error := systemCallBase_error M
  refund := by
    show 0 ≤ (systemCallBase M).refundCounter
    rw [systemCallBase_refundCounter]
  deleted := by
    show (systemCallBase M).accountsToDelete.toList = []
    unfold systemCallBase Devm.balReadAccount
    dsimp only
    by_cases h : M.benv.stat.rules.bal.isSome = true <;> simp only [h, ↓reduceIte] <;> exact inherited
  clean := fun k _ => by
    have hstat : benv.stat = M.benv.stat := benvAfterTransfer_stat entry
    have hcreated := benvAfterTransfer_createdAccounts entry
    have hstor := entry_stor installed hnonempty entry
    show (if M.currentTarget ∈ (userEntry M benv).createdAccounts then (0 : B256)
      else ((benv.stat.origState.get M.currentTarget).stor).get k) =
        ((benv.state.get M.currentTarget).stor).get k
    have hc : (userEntry M benv).createdAccounts = benv.createdAccounts := rfl
    rw [hc, hcreated, ite_eq_right hnew, hstat, origin]
    exact (congrArg (Stor.get · k) hstor).symm
  drawn := Nat.le_refl _
  ledger := rfl
  committed := rfl
  budget := by rw [hlen]; simp only [Nat.zero_add, Nat.le_refl]

/-- **A direct submission under Amsterdam, on any state-gas meter.** A message to the code at a non-system caller,
non-static, with no authorizations and non-delegated code, where the value moved (`entry`), carrying the submission's
length, slot 0 off the inhibitor, and the guards' `Admit` at the fee the recurrence quotes (`out / 17`) from the
contract's storage. `G` is what remains of the message's gas after the submission's charge, more than the 2300 the
last `SSTORE`'s sentry asks; `noAlias` says no record slot lands on the count or the tail, which holds for any tail below
`2^253`. Then the call returns the stated world, over the state after the value moved. Its logs are the frame's start
logs, under EIP-7708 the transfer log (`initDevm_logs_transfer`), and then the frame's `LOG0`. Regular gas left is exactly
`G`. State gas used is `used`, at most `stateBound`. -/
theorem message_ok {G n : Nat} {out : B256} (hfork : M.benv.stat.fork = .amsterdam)
    (hauth : M.tenv.stat.auths.isEmpty = true) (htarget : M.target.isNone = false)
    (installed : M.benv.state.getCode M.currentTarget = c.code)
    (hprecomp : ¬ amsterdamRules.isPrecomp M.currentTarget) (entry : M.benvAfterTransfer = .ok benv)
    (hnew : M.currentTarget ∉ M.benv.createdAccounts)
    (origin : (M.benv.stat.origState.get M.currentTarget).stor = (M.benv.state.get M.currentTarget).stor)
    (inherited : M.inheritedDeletions.toList = [])
    (caller : M.caller ≠ systemAddress) (hlen : M.data.length = c.len) (dynamic : M.isStatic = false)
    (stipend : gCallStipend < G) (hgas : M.gas = G + c.Gas S E .empty n)
    (off : (M.benv.state.getStor M.currentTarget).get 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storageExcess c.target (M.benv.state.getStor M.currentTarget)) 17 1 17 0 n out)
    (admit : c.Admit M.data M.value (out / (17 : B256)))
    (noAlias : ((M.benv.state.getStor M.currentTarget).get 3).toNat < 2 ^ 253) :
    ∃ used, used ≤ c.stateBound ∧
      processMessageCall M = .ok (c.world S benv.state, systemCallOutputA M (c.Post S E .empty G)) ∧
      (c.Post S E .empty G).logs = (initDevm M).logs ++ [c.log S] ∧
      (c.Post S E .empty G).gasLeft = G ∧
      (systemCallOutputA M (c.Post S E .empty G)).stateGasUsed = Int.ofNat used ∧
      (c.Post S E .empty G).stateGas.left ≤ M.stateGasGrant ∧
      (c.Post S E .empty G).accountsToDelete.toList = [] := by
  have hstat : benv.stat = M.benv.stat := benvAfterTransfer_stat entry
  have hsfork : (S).benvStat.fork = .amsterdam := by
    show benv.stat.fork = _
    rw [hstat]
    exact hfork
  have hstor := entry_stor installed c.nonempty entry
  have read : ∀ k, (E).getStorVal M.currentTarget k = (M.benv.state.getStor M.currentTarget).get k := fun k => by
    show (benv.state.getStor M.currentTarget).get k = _
    rw [hstor]
  have hkeys : (c.keys ((E).getStorVal (S).currentTarget 3)).Nodup :=
    c.nodup _ (by
      show ((E).getStorVal M.currentTarget 3).toNat < _
      rw [read]
      exact noAlias)
  have r0 := entry_fresh (n := c.stores) hnew origin installed c.nonempty entry inherited
    (c.keys ((E).getStorVal (S).currentTarget 3)) (c.keys_length _)
  obtain ⟨⟨used, r⟩, hrepay⟩ := c.fresh (M := .empty) (G := G) hsfork r0 hkeys
  have hrun := c.exec (s := S) (b := E) (M := .empty) (G := G) (n := n) (out := out) rfl hsfork caller hlen
    dynamic stipend
    (by
      show (E).getStorVal M.currentTarget 0 ≠ _
      rw [read]
      exact off)
    (by
      have : storedExcess c.target S E = storageExcess c.target (M.benv.state.getStor M.currentTarget) := by
        show targetExcess _ ((E).getStorVal M.currentTarget 0) ((E).getStorVal M.currentTarget 1) = _
        rw [read, read]
        rfl
      rw [this]
      exact wordRun)
    admit
  rw [hrepay, Nat.add_zero] at hrun
  have hSt : St (E) [] .empty (G + c.Gas S E .empty n) = E := by
    rw [← hgas]
    exact (St.self rfl rfl).symm
  rw [hSt] at hrun
  have hexec := (exec_iff_exec_eq _ _ _ _).mp hrun
  have hcall := processMessageCall_ok hfork hauth htarget installed c.nonempty c.undelegated hprecomp entry
    hexec r.error r.refund
  rw [c.state hsfork] at hcall
  have hbudget := r.budget
  simp only [List.length_nil, Nat.zero_mul, Nat.add_zero] at hbudget
  refine ⟨used, hbudget, hcall, ?_, c.gasLeft, ?_, r.drawn, r.deleted⟩
  · have hlogs := c.logs (s := S) (b := E) (G := G) hsfork hlen
    refine hlogs.trans ?_
    have : (E).logs = (initDevm M).logs := by
      show (systemCallBase M).logs = _
      unfold systemCallBase Devm.balReadAccount
      dsimp only
      by_cases h : M.benv.stat.rules.bal.isSome = true <;> simp only [h, ↓reduceIte] <;> rfl
    rw [this]
  · have hledger := r.ledger
    have hcommitted := r.committed
    show Int.ofNat M.stateGasGrant - Int.ofNat (c.Post S E .empty G).stateGas.left +
      Int.ofNat (c.Post S E .empty G).stateGas.spilled +
      Int.ofNat (c.Post S E .empty G).stateGas.committedSpill = _
    rw [hcommitted]
    simp only [Int.ofNat_eq_natCast]
    omega

/-- **The inverse at message level.** Every successful direct message at the code under Amsterdam, at a non-system
caller with no authorizations, is a submission or a fee read. "Successful" means the message's output carries no error.
The transfer has succeeded (`entry`). -/
theorem message_inverse {post : State} {out : MsgCallOutput} (hfork : M.benv.stat.fork = .amsterdam)
    (hauth : M.tenv.stat.auths.isEmpty = true) (htarget : M.target.isNone = false)
    (installed : M.benv.state.getCode M.currentTarget = c.code)
    (hprecomp : ¬ amsterdamRules.isPrecomp M.currentTarget) (entry : M.benvAfterTransfer = .ok benv)
    (caller : M.caller ≠ systemAddress) (lengthBound : M.data.length < 2 ^ 256)
    (call : processMessageCall M = .ok (post, out)) (ok : out.error = none) :
    ∃ frame, post = frame.state ∧ out = systemCallOutputA M frame ∧
      c.Frame (amsterdamSteps S) E frame := by
  obtain ⟨frame, run, -, hpost, hout⟩ := processMessageCall_inv hfork hauth htarget installed c.nonempty
    c.undelegated hprecomp entry call ok
  have hstat : benv.stat = M.benv.stat := benvAfterTransfer_stat entry
  have hsfork : (S).benvStat.fork = .amsterdam := by
    show benv.stat.fork = _
    rw [hstat]
    exact hfork
  obtain ⟨hexec⟩ := (exec_iff_exec_eq _ _ _ _).mpr run
  exact ⟨frame, hpost, hout, UserFrames.exec_user_frame_amsterdam c.toUserFrames rfl hsfork rfl
    (by
      show (Mem.empty).size % 32 = 0
      rfl)
    Mem.wf_empty lengthBound caller hexec⟩

end Submissions

end Blanc.Lift.BuilderRequest
