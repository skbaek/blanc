import Blanc.Lift.WithdrawalRequest.FloodWalk
import Blanc.Lift.FloodLooper.Jumps
import Blanc.Lift.ExactWalkCutOps

/-!
# The flood looper's whole run: exactly `k` committed submissions

The loop at the looper's entry 1 (pc `0x7`) is walked one iteration at a time
as an exact cut run (`SFunc.RunExactCut … [1]`), each iteration a committed
fee-1 submission through `flood_call`; `SFunc.RunExactCut.iterate` assembles
the `k` iterations and the exit to `STOP`, symbolically in `k`.  The setup at
entry 0 copies the payload and enters the loop; `lift_exact` turns the run
into the looper's `exec`.
-/

namespace Blanc.Lift.WithdrawalRequest.FloodWalk

open Jaune Blanc.Lift

/-! ## The model image after `i` submissions -/

/-- The EIP model state after `i` submissions of `entry` from `σ0`. -/
def floodState (σ0 : Blanc.WithdrawalRequest.State) (entry : Blanc.WithdrawalRequest.Entry) :
    Nat → Blanc.WithdrawalRequest.State
  | 0 => σ0
  | i + 1 => Blanc.WithdrawalRequest.submit (floodState σ0 entry i) entry

theorem floodState_fields (σ0 : Blanc.WithdrawalRequest.State)
    (entry : Blanc.WithdrawalRequest.Entry) (i : Nat) :
    (floodState σ0 entry i).excess = σ0.excess ∧
    (floodState σ0 entry i).count = σ0.count + i ∧
    (floodState σ0 entry i).tail = σ0.tail + i := by
  induction i with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ i ih =>
    refine ⟨ih.1, ?_, ?_⟩
    · change (floodState σ0 entry i).count + 1 = _
      rw [ih.2.1, Nat.add_assoc]
    · change (floodState σ0 entry i).tail + 1 = _
      rw [ih.2.2, Nat.add_assoc]

/-! ## The looper's environment and loop invariant -/

/-- What the looper frame needs of its environment: a covered fork, a dynamic non-outermost
frame, calldata `k ‖ payload` from the entry, a distinct non-system looper address, an
active predeploy at excess zero whose model leaves room for `k` more submissions, and the
transaction-original count and tail words equal to the model's. -/
structure FloodEnv (sevm : Sevm) (k : Nat) (entry : Blanc.WithdrawalRequest.Entry)
    (σ0 : Blanc.WithdrawalRequest.State) : Prop where
  fork : CoveredFork sevm.benvStat.fork
  static : sevm.isStatic = false
  depth : sevm.depth ≠ 0
  data : sevm.data = calldata (Nat.toB256 k) (Blanc.WithdrawalRequest.submissionPayload entry)
  caller : entry.caller = sevm.currentTarget
  user : sevm.currentTarget ≠ systemAddress
  self : sevm.currentTarget ≠ withdrawalRequestPredeployAddress
  excess : σ0.excess = 0
  countLt : σ0.count + k < 2 ^ 256
  tailLt : Blanc.WithdrawalRequest.queueBase (σ0.tail + k) + 2 < 2 ^ 256
  origCount : getOrigStorVal sevm withdrawalRequestPredeployAddress 1 = σ0.count.toB256
  origTail : getOrigStorVal sevm withdrawalRequestPredeployAddress 3 = σ0.tail.toB256

/-- The gas the loop still needs at the head of iteration `i`. -/
def floodReserve (k i : Nat) : Nat :=
  (k - i) * 87706 + (if i = 0 then 39800 else 0) + 247934

/-- The state at the head of iteration `i`: code installed, storage representing the model
after `i` submissions, `i` wei paid, error unchanged, `i` logs appended, and the reserve. -/
structure FloodInv (sevm : Sevm) (k : Nat) (entry : Blanc.WithdrawalRequest.Entry)
    (σ0 : Blanc.WithdrawalRequest.State) (bal0 : Nat) (logs0 : List Log)
    (err0 : Option SettledHalt) (i : Nat) (base : Devm) (G : Nat) : Prop where
  code : base.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode
  rep : Blanc.WithdrawalRequest.RepresentsStorage
    (base.getStor withdrawalRequestPredeployAddress).get (floodState σ0 entry i)
  bal : (base.getBal sevm.currentTarget).toNat + i = bal0
  err : base.error = err0
  logs : base.logs = logs0 ++ List.replicate i
    ⟨withdrawalRequestPredeployAddress, [], Blanc.WithdrawalRequest.submissionLog entry⟩
  gasLt : G < 2 ^ 256
  reserve : floodReserve k i ≤ G

theorem floodState_bounds {sevm : Sevm} {k : Nat} {entry : Blanc.WithdrawalRequest.Entry}
    {σ0 : Blanc.WithdrawalRequest.State} (env : FloodEnv sevm k entry σ0) {i : Nat} (hi : i < k) :
    SubmissionBounds (floodState σ0 entry i) := by
  have f := floodState_fields σ0 entry i
  have tl := env.tailLt
  have cl := env.countLt
  unfold Blanc.WithdrawalRequest.queueBase at tl
  refine ⟨?_, ?_⟩
  · rw [f.2.1]; omega
  · unfold Blanc.WithdrawalRequest.queueBase
    rw [f.2.2]; omega

private theorem toB256_ne_of_lt {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) (h : a ≠ b) :
    a.toB256 ≠ b.toB256 := by
  intro e
  have := congrArg B256.toNat e
  rw [B256.toNat_toB256_of_lt ha, B256.toNat_toB256_of_lt hb] at this
  exact h this

/-- After the first submission both metadata slots are dirty: each value charge is warm. -/
theorem metaValueGas_flood {sevm : Sevm} {k : Nat} {entry : Blanc.WithdrawalRequest.Entry}
    {σ0 : Blanc.WithdrawalRequest.State} (env : FloodEnv sevm k entry σ0) {i : Nat} (hi : i < k) :
    metaValueGas sevm (floodState σ0 entry i) ≤ if i = 0 then 40000 else 200 := by
  have f := floodState_fields σ0 entry i
  have a := sstoreValueCost_le (getOrigStorVal sevm withdrawalRequestPredeployAddress 1)
    (floodState σ0 entry i).count.toB256 (1 + (floodState σ0 entry i).count.toB256)
  have b := sstoreValueCost_le (getOrigStorVal sevm withdrawalRequestPredeployAddress 3)
    (floodState σ0 entry i).tail.toB256 (1 + (floodState σ0 entry i).tail.toB256)
  unfold metaValueGas
  split
  · simp only [gasStorageSet] at a b
    omega
  · rename_i hi0
    have tl := env.tailLt
    have cl := env.countLt
    unfold Blanc.WithdrawalRequest.queueBase at tl
    rw [env.origCount, env.origTail, f.2.1, f.2.2,
      sstoreValueCost_of_ne (toB256_ne_of_lt (by omega) (by omega) (by omega)),
      sstoreValueCost_of_ne (toB256_ne_of_lt (by omega) (by omega) (by omega))]
    decide

/-- The predeploy address the looper pushes. -/
theorem looper_callee :
    (Bytes.toB256 [0x00, 0x00, 0x09, 0x61, 0xef, 0x48, 0x0e, 0xb5, 0x5e, 0x80, 0xd1, 0x9a,
      0xd8, 0x35, 0x79, 0xa6, 0x4c, 0x00, 0x70, 0x02]).toAdr = withdrawalRequestPredeployAddress :=
  rfl

/-- The calldata's first word is the iteration count. -/
theorem looper_count {sevm : Sevm} {k : Nat} {entry : Blanc.WithdrawalRequest.Entry}
    {σ0 : Blanc.WithdrawalRequest.State} (env : FloodEnv sevm k entry σ0) :
    Sevm.dataWord sevm 0 = Nat.toB256 k := by
  unfold Sevm.dataWord
  rw [env.data]
  exact calldata_word

/-- The reserve shrinks by at most one iteration's charge. -/
private theorem reserve_step {k i G0 G2 m : Nat} (hi : i < k)
    (hres : floodReserve k i ≤ G0 + 42) (hge : G0 ≤ G2 + 19 + 87445 + m)
    (hm : m ≤ if i = 0 then 40000 else 200) : floodReserve k (i + 1) ≤ G2 := by
  unfold floodReserve at hres ⊢
  have hk : k - i = (k - (i + 1)) + 1 := by omega
  rw [hk, Nat.add_mul, Nat.one_mul] at hres
  simp only [Nat.succ_ne_zero, ite_false, Nat.add_zero]
  generalize (k - (i + 1)) * 87706 = x at hres ⊢
  by_cases h0 : i = 0
  · simp only [h0, ite_true] at hres hm
    omega
  · simp only [h0, ite_false] at hres hm
    omega

/-- **One loop iteration.**  From the loop head at iteration `i < k`, the looper's tree cut
at its own entry runs through one committed submission back to the head with the counter
`i + 1`, keeping the invariant. -/
theorem flood_iter {sevm : Sevm} {k : Nat} {entry : Blanc.WithdrawalRequest.Entry}
    {σ0 : Blanc.WithdrawalRequest.State} {bal0 : Nat} {logs0 : List Log}
    {err0 : Option SettledHalt} (env : FloodEnv sevm k entry σ0) {i : Nat} (hi : i < k)
    {base : Devm} {G : Nat} (inv : FloodInv sevm k entry σ0 bal0 logs0 err0 i base G)
    (hbal0 : k ≤ bal0) :
    ∃ base' G', SFunc.RunExactCut prog sevm [1]
        (St base [Nat.toB256 i] (payloadMem (Blanc.WithdrawalRequest.submissionPayload entry)) G)
        Blanc.Lift.FloodLooper.t_0007_c1
        (.at 1 (St base' [Nat.toB256 (i + 1)]
          (payloadMem (Blanc.WithdrawalRequest.submissionPayload entry)) G')) ∧
      FloodInv sevm k entry σ0 bal0 logs0 err0 (i + 1) base' G' := by
  have hres := inv.reserve
  have hmeta := metaValueGas_flood env hi
  have hGlt := inv.gasLt
  obtain ⟨G0, rfl⟩ : ∃ G0, G = G0 + 42 := ⟨G - 42, by unfold floodReserve at hres; omega⟩
  have hbal : 1 ≤ (base.getBal sevm.currentTarget).toNat := by have := inv.bal; omega
  have hcall : 247892 ≤ G0 := by
    unfold floodReserve at hres
    split at hres <;> omega
  obtain ⟨post, G', run, hle, hge, hcode, hrep, hbal', herr, hlogs⟩ :=
    flood_call (S := [Nat.toB256 i]) (Gc := G0) env.fork env.static env.depth env.caller
      env.user env.self looper_callee inv.code inv.rep
      (by rw [(floodState_fields σ0 entry i).1]; exact env.excess) (floodState_bounds env hi)
      hbal (by simp only [List.length_cons, List.length_nil]; omega) (by omega) hcall
  have hd : (if i = 0 then 40000 else 200) ≤ 40000 := by split <;> decide
  have hcl := env.countLt
  obtain ⟨G2, rfl⟩ : ∃ G2, G' = G2 + 19 := ⟨G' - 19, by omega⟩
  refine ⟨post, G2, ?_, ?_⟩
  · unfold Blanc.Lift.FloodLooper.t_0007_c1
    refine rxc_dest ?_
    refine rxc_dup (n := 0) (w := Nat.toB256 i) rfl (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rxc_push0 (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rxc_calldataload (by simp only [List.length_cons, List.length_nil]; omega) ?_
    rw [looper_count env]
    refine rxc_eq (v := 0) ?_ (by simp only [List.length_cons, List.length_nil]; omega) ?_
    · have hne := toB256_ne_of_lt (a := k) (b := i) (by omega) (by omega) (by omega)
      unfold B256.eqCheck
      simp only [hne, ite_false]
    refine rxc_push rfl (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rxc_branch_zero ?_
    unfold Blanc.Lift.FloodLooper.t_000f_c1
    refine rxc_push0 (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rxc_push0 (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rxc_push (w := 56) (by decide) (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rxc_push0 (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rxc_push (w := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rxc_push rfl (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rxc_gas (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine .next run ?_
    refine rxc_pop ?_
    refine rxc_push rfl (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rxc_add' (one_add_toB256 (by omega)) (by simp only [List.length_nil]; omega) ?_
    refine rxc_push rfl (by simp only [List.length_cons, List.length_nil]; omega) ?_
    exact rxc_jumpCut (by decide)
  · refine ⟨hcode, hrep, ?_, ?_, ?_, ?_, ?_⟩
    · have := inv.bal
      omega
    · rw [herr]; exact inv.err
    · rw [hlogs, inv.logs, List.replicate_succ', List.append_assoc]
    · omega
    · exact reserve_step hi hres hge hmeta

/-- What the run leaves at `STOP` after `k` submissions. -/
def FloodDone (sevm : Sevm) (k : Nat) (entry : Blanc.WithdrawalRequest.Entry)
    (σ0 : Blanc.WithdrawalRequest.State) (bal0 : Nat) (logs0 : List Log)
    (err0 : Option SettledHalt) (post : Devm) : Prop :=
  post.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode ∧
  Blanc.WithdrawalRequest.RepresentsStorage
    (post.getStor withdrawalRequestPredeployAddress).get (floodState σ0 entry k) ∧
  (post.getBal sevm.currentTarget).toNat + k = bal0 ∧
  post.error = err0 ∧
  post.logs = logs0 ++ List.replicate k
    ⟨withdrawalRequestPredeployAddress, [], Blanc.WithdrawalRequest.submissionLog entry⟩

/-- **The exit.**  At `i = k` the head's comparison succeeds and the looper stops. -/
theorem flood_exit {sevm : Sevm} {k : Nat} {entry : Blanc.WithdrawalRequest.Entry}
    {σ0 : Blanc.WithdrawalRequest.State} {bal0 : Nat} {logs0 : List Log}
    {err0 : Option SettledHalt} (env : FloodEnv sevm k entry σ0) {base : Devm} {G : Nat}
    (inv : FloodInv sevm k entry σ0 bal0 logs0 err0 k base G) :
    ∃ post, SFunc.RunExactCut prog sevm [1]
        (St base [Nat.toB256 k] (payloadMem (Blanc.WithdrawalRequest.submissionPayload entry)) G)
        Blanc.Lift.FloodLooper.t_0007_c1 (.done (.halted post)) ∧
      FloodDone sevm k entry σ0 bal0 logs0 err0 post := by
  have hres := inv.reserve
  obtain ⟨G0, rfl⟩ : ∃ G0, G = G0 + 26 := ⟨G - 26, by unfold floodReserve at hres; omega⟩
  refine ⟨St base [Nat.toB256 k] (payloadMem (Blanc.WithdrawalRequest.submissionPayload entry))
    G0, ?_, inv.code, inv.rep, inv.bal, inv.err, inv.logs⟩
  unfold Blanc.Lift.FloodLooper.t_0007_c1
  refine rxc_dest ?_
  refine rxc_dup (n := 0) (w := Nat.toB256 k) rfl
    (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rxc_push0 (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rxc_calldataload (by simp only [List.length_cons, List.length_nil]; omega) ?_
  rw [looper_count env]
  refine rxc_eq (v := 1) ?_ (by simp only [List.length_cons, List.length_nil]; omega) ?_
  · unfold B256.eqCheck
    simp only [ite_true]
  refine rxc_push rfl (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rxc_branch_succ (by decide) ?_
  unfold Blanc.Lift.FloodLooper.t_0034_c1
  refine rxc_dest ?_
  exact .last rfl

/-- **The loop.**  From the head of iteration 0 the looper's tree, uncut, runs all `k`
iterations and stops. -/
theorem flood_loop {sevm : Sevm} {k : Nat} {entry : Blanc.WithdrawalRequest.Entry}
    {σ0 : Blanc.WithdrawalRequest.State} {bal0 : Nat} {logs0 : List Log}
    {err0 : Option SettledHalt} (env : FloodEnv sevm k entry σ0) (hbal0 : k ≤ bal0)
    {base : Devm} {G : Nat} (inv : FloodInv sevm k entry σ0 bal0 logs0 err0 0 base G) :
    ∃ post, SFunc.RunExactCut prog sevm []
        (St base [Nat.toB256 0] (payloadMem (Blanc.WithdrawalRequest.submissionPayload entry)) G)
        Blanc.Lift.FloodLooper.t_0007_c1 (.done (.halted post)) ∧
      FloodDone sevm k entry σ0 bal0 logs0 err0 post := by
  have loop := SFunc.RunExactCut.iterate (fs := prog) (sevm := sevm) (C := []) (k := 1)
    prog_head (by simp only [List.not_mem_nil, not_false_eq_true])
    (fun i devm => ∃ base G, devm = St base [Nat.toB256 i]
      (payloadMem (Blanc.WithdrawalRequest.submissionPayload entry)) G ∧
      FloodInv sevm k entry σ0 bal0 logs0 err0 i base G) k
    (fun r => ∃ post, r = .done (.halted post) ∧ FloodDone sevm k entry σ0 bal0 logs0 err0 post)
    (by
      rintro i hi devm ⟨base, G, rfl, inv⟩
      obtain ⟨base', G', run, inv'⟩ := flood_iter env hi inv hbal0
      exact ⟨_, run, base', G', rfl, inv'⟩)
    (by
      rintro devm ⟨base, G, rfl, inv⟩
      obtain ⟨post, run, done⟩ := flood_exit env inv
      refine ⟨_, run, fun d h => Seg.noConfusion h, post, rfl, done⟩)
    _ ⟨base, G, rfl, inv⟩
  obtain ⟨r, run, post, rfl, done⟩ := loop
  exact ⟨post, run, done⟩

/-- Entry 0 inlines a copy of the loop head; it is the loop head. -/
theorem t_0007_eq : Blanc.Lift.FloodLooper.t_0007_c0 = Blanc.Lift.FloodLooper.t_0007_c1 := rfl

/-- The gas the whole looper run needs: setup plus the loop's reserve. -/
def floodGas (k : Nat) : Nat := floodReserve k 0 + 25

/-- **The looper frame, lifted.**  A frame running the looper code from an empty stack and
memory, with enough gas, halts at `STOP` after exactly `k` committed submissions. -/
theorem flood_frame {sevm : Sevm} {k : Nat} {entry : Blanc.WithdrawalRequest.Entry}
    {σ0 : Blanc.WithdrawalRequest.State} (env : FloodEnv sevm k entry σ0)
    (hcode : sevm.code = Blanc.Lift.FloodLooper.code) {pre : Devm}
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (hinstalled : pre.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    (hrep : Blanc.WithdrawalRequest.RepresentsStorage
      (pre.getStor withdrawalRequestPredeployAddress).get σ0)
    (hbal : k ≤ (pre.getBal sevm.currentTarget).toNat)
    (hgas : floodGas k ≤ pre.gasLeft) (hlt : pre.gasLeft < 2 ^ 256) :
    ∃ post, Nonempty (Exec 0 sevm pre (.ok post)) ∧
      FloodDone sevm k entry σ0 (pre.getBal sevm.currentTarget).toNat pre.logs pre.error post := by
  obtain ⟨G, hG⟩ : ∃ G, G + 25 = pre.gasLeft := ⟨pre.gasLeft - 25, by unfold floodGas at hgas; omega⟩
  have hpre := pre_eq_St hstack hmem hG
  have inv : FloodInv sevm k entry σ0 (pre.getBal sevm.currentTarget).toNat pre.logs pre.error 0
      pre G := by
    refine ⟨hinstalled, hrep, rfl, rfl, ?_, by omega, by unfold floodGas at hgas; omega⟩
    rw [List.replicate_zero, List.append_nil]
  obtain ⟨post, loop, done⟩ := flood_loop env hbal inv
  refine ⟨post, lift_exact Blanc.Lift.FloodLooper.cert_check Blanc.Lift.FloodLooper.jumps_ok
    hcode env.fork ⟨Blanc.Lift.FloodLooper.t_0000_c0, prog_root, ?_⟩, done⟩
  rw [← hpre]
  apply SFunc.runExact_iff_runExactCut_nil.mpr
  unfold Blanc.Lift.FloodLooper.t_0000_c0
  refine rxc_push (w := 56) (by decide) (by simp only [List.length_nil]; omega) ?_
  refine rxc_push (w := 32) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rxc_push0 (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rxc_calldatacopy (c := 15) (M' := payloadMem (Blanc.WithdrawalRequest.submissionPayload
    entry)) ?_ ?_ ?_
  · have h0 : (0 : B256).toNat = 0 := rfl
    have h56 : (56 : B256).toNat = 56 := rfl
    rw [h0, h56, St.extCost_eq (n := 0) rfl]
    rfl
  · have h0 : (0 : B256).toNat = 0 := rfl
    have h32 : (32 : B256).toNat = 32 := rfl
    have h56 : (56 : B256).toNat = 56 := rfl
    rw [h0, h32, h56, env.data,
      calldata_payload (Blanc.WithdrawalRequest.submissionPayload_length entry)]
    rfl
  refine rxc_push0 (by simp only [List.length_nil]; omega) ?_
  rw [t_0007_eq]
  exact loop

/-- The refutation witness's flood (`k = 2895`) fits a `2^28` transaction gas limit with a
megagas left for intrinsic charges. -/
theorem floodGas_2895 : floodGas 2895 + 2 ^ 20 ≤ 2 ^ 28 := by
  unfold floodGas floodReserve
  decide

/-- **The flood looper makes exactly `k` committed fee-1 submissions.**  A message running
the looper code with calldata `k ‖ payload` (`FloodEnv`), into a world where the withdrawal
predeploy is installed with storage representing an active model state `σ0` at excess zero,
the looper holds at least `k` wei and the gas is at least `floodGas k`, executes without
error.  Its committed effects: the predeploy storage represents `σ0` after `k` submissions of
`entry` (the looper as caller, the payload's pubkey and amount), the looper paid exactly `k`
wei, and the frame's logs are exactly the `k` submission logs. -/
theorem flood_exec {msg : Msg} {k : Nat} {entry : Blanc.WithdrawalRequest.Entry}
    {σ0 : Blanc.WithdrawalRequest.State} (env : FloodEnv (initSevm msg) k entry σ0)
    (hcode : msg.code = Blanc.Lift.FloodLooper.code)
    (hinstalled : msg.benv.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode)
    (hrep : Blanc.WithdrawalRequest.RepresentsStorage
      (msg.benv.state.getStor withdrawalRequestPredeployAddress).get σ0)
    (hbal : k ≤ (msg.benv.state.bal msg.currentTarget).toNat)
    (hgas : floodGas k ≤ msg.gas) (hlt : msg.gas < 2 ^ 256) :
    ∃ post, exec (initEvm msg) = .ok post ∧ post.error = none ∧
      post.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode ∧
      Blanc.WithdrawalRequest.RepresentsStorage
        (post.getStor withdrawalRequestPredeployAddress).get (floodState σ0 entry k) ∧
      (post.getBal msg.currentTarget).toNat + k = (msg.benv.state.bal msg.currentTarget).toNat ∧
      post.logs = List.replicate k
        ⟨withdrawalRequestPredeployAddress, [], Blanc.WithdrawalRequest.submissionLog entry⟩ := by
  have hlog0 : (initDevm msg).logs = [] := by
    change (match msg.benv.stat.rules.stateGas with
      | none => []
      | some _ => _) = []
    have hsg : msg.benv.stat.rules.stateGas = none := CoveredFork.rules_stateGas_none env.fork
    rw [hsg]
  obtain ⟨post, run, code, rep, bal, err, logs⟩ := flood_frame env hcode (pre := initDevm msg)
    rfl rfl hinstalled hrep hbal hgas hlt
  obtain ⟨run⟩ := run
  refine ⟨post, (exec_iff_exec_eq 0 (initSevm msg) (initDevm msg) _).mp ⟨run⟩, err, code, rep,
    bal, ?_⟩
  rw [logs, hlog0, List.nil_append]

end Blanc.Lift.WithdrawalRequest.FloodWalk
