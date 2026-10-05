import Blanc.Lift.Weth9.LiveApprove

namespace Blanc.Lift.Weth9

open Jaune Blanc.Lift

/-- The memory image the `deposit` body leaves. -/
def depMem (M : Mem) (C v : B256) : Mem :=
  ((M.write 0 C.toBytes).write 32 (3 : B256).toBytes).write 96 v.toBytes

/-- The `deposit` body (entry 1, `0x0440`), from the stack `return, …`: `balanceOf[caller] += callvalue`
(the slot's `SLOAD` and `SSTORE`) and the `Deposit` event.  `104` gas before the `SLOAD`, `16` between it
and the `SSTORE`, `1456` after it (`1381` for the `LOG2`, one word of expansion included). -/
theorem deposit_body {sevm : Sevm} {b : Devm} {G : Nat} {S : List B256} {M : Mem} {ret : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hM : FpMem 96 M) (hroom : S.length < 1000)
    (hsentry : gCallStipend < G + 1456 +
      sstoreCost sevm (afterSload sevm b (balSlot sevm.caller)) (balSlot sevm.caller)
        (b.getStorVal sevm.currentTarget (balSlot sevm.caller) + sevm.value)) :
    ∃ b', SFunc.RunExact prog sevm (St b (ret :: S) M
      (G + 1456 + sstoreCost sevm (afterSload sevm b (balSlot sevm.caller)) (balSlot sevm.caller)
        (b.getStorVal sevm.currentTarget (balSlot sevm.caller) + sevm.value) + 16 +
        sloadCost sevm b (balSlot sevm.caller) + 104)) t_0440_c1
      (.returned (St b' S (depMem M sevm.caller.toB256 sevm.value) G)) ∧ b'.output = b.output := by
  refine ⟨?b', ?run, ?out⟩
  case run =>
    rdest
    refine rx_callvalue (by rroom) ?_
    rpush
    rpush
    refine rx_caller (by rroom) ?_
    rmask
    rmask
    rdup
    rmst 0
    rpush
    radd
    rswap
    rdup
    rmst 32
    rpush
    radd
    rpush
    rkec
    rpush
    rdup
    rdup
    rsload
    refine rx_add (by rroom) ?_
    rswap
    rpop
    rpop
    rdup
    rswap
    rsstore
    rpop
    refine rx_caller (by rroom) ?_
    rmask
    rpush
    refine rx_callvalue (by rroom) ?_
    rpush
    rmld
    rdup
    rdup
    rdup
    refine rx_mstoreOut (by assumption) (by decide) (fun _ => ?_)
    rpush
    radd
    rswap
    rpop
    rpop
    rpush
    rmld
    rdup
    rswap
    rsub
    rswap
    rlog2
    exact rx_ret
  case out =>
    have h : ∀ (d : Devm) (L : Log), (d.addLog L).output = d.output := fun _ _ => rfl
    rw [h]; simp only [afterSstore_output, afterSload_output]

/-- A payable entry (the `deposit()` wrapper and the fallback): two pushes, the call into the body,
a `STOP`.  `15` gas before the body, `1` after it. -/
theorem deposit_wrap {sevm : Sevm} {b : Devm} {G : Nat} {S : List B256} {T : SFunc}
    {c0 c1 : UInt8} {le1 : [c0, c1].length ≤ 32} {le2 : [0x04, 0x40].length ≤ 32}
    (hT : T = .dest (.next (.push [c0, c1] le1) (.next (.push [0x04, 0x40] le2)
      (.callNext 1 (.dest (.last .stop))))))
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hroom : S.length < 1000)
    (hsentry : gCallStipend < G + 1 + 1456 +
      sstoreCost sevm (afterSload sevm b (balSlot sevm.caller)) (balSlot sevm.caller)
        (b.getStorVal sevm.currentTarget (balSlot sevm.caller) + sevm.value)) :
    ∃ post, SFunc.RunExact prog sevm (St b S memFp
      (G + 1 + 1456 + sstoreCost sevm (afterSload sevm b (balSlot sevm.caller))
        (balSlot sevm.caller) (b.getStorVal sevm.currentTarget (balSlot sevm.caller) + sevm.value)
        + 16 + sloadCost sevm b (balSlot sevm.caller) + 104 + 15)) T (.halted post) ∧
      post.gasLeft = G ∧ post.output = b.output := by
  subst hT
  obtain ⟨b', hbody, hout⟩ := deposit_body (S := S) (ret := Bytes.toB256 [c0, c1]) (G := G + 1)
    hfork hstatic fp_memFp hroom hsentry
  refine ⟨?post, ?run, ?gas, ?out⟩
  case run =>
    rdest
    rpush
    rpush
    refine rx_callRet (j := 1) rfl hbody ?_
    rdest
    exact rx_stop
  case gas => rfl
  case out => exact hout

/-- The eleven selectors of the deployed WETH9's dispatcher. -/
def weth9Sels : List B256 :=
  [0x06fdde03, 0x095ea7b3, 0x18160ddd, 0x23b872dd, 0x2e1a7d4d, 0x313ce567, 0x70a08231, 0x95d89b41,
    0xa9059cbb, 0xd0e30db0, 0xdd62ed3e]

/-- WETH9's `deposit()` selector. -/
abbrev dpSel : B256 := selector "deposit" []

theorem dpSel_eq : dpSel = 0xd0e30db0 := by decide +kernel

/-- The dispatcher path to `deposit()`: eight non-matching comparisons after the head's, then the
match at the tenth, jumping to entry 19.  282 gas. -/
theorem dispatch_deposit {sevm : Sevm} {b : Devm} {g : Nat} {o : Outcome}
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = 0xd0e30db0)
    (k : SFunc.RunExact prog sevm (St b [Sevm.selector sevm] memFp g) t_03ca_c19 o) :
    SFunc.RunExact prog sevm (St b [] Mem.empty (g + 282)) t_0000_c0 o := by
  refine dispatch_head h_len h_len' (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  exact cmp_hit (j := 19) (by rw [hsel]; decide) rfl k

/-- Calldata shorter than four bytes goes to the fallback: `mstore(0x40, 0x60)`, the length test, the
jump.  39 gas. -/
theorem dispatch_short {sevm : Sevm} {b : Devm} {g : Nat} {o : Outcome}
    (h_short : sevm.data.length.toB256 < 4)
    (k : SFunc.RunExact prog sevm (St b [] memFp g) t_00af_c0 o) :
    SFunc.RunExact prog sevm (St b [] Mem.empty (g + 39)) t_0000_c0 o := by
  refine rx_push (w := 0x60) (by decide) (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  refine rx_push (w := 0x40) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.one_lt_ofNat]) ?_
  refine rx_mstore (c := 12) (M' := memFp) ?_ rfl ?_
  · rw [St.extCost_eq (n := 0) rfl]; decide
  refine rx_push (w := 4) (by decide) (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  refine rx_calldatasize (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.one_lt_ofNat]) ?_
  refine rx_lt (v := 1) ?_ (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  · simp only [B256.ltCheck, h_short, ↓reduceIte]
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  exact rx_branch_succ (by decide) k

/-- Calldata of four bytes or more whose selector matches no comparison: all eleven miss and the
last falls through to the fallback.  304 gas. -/
theorem dispatch_miss {sevm : Sevm} {b : Devm} {g : Nat} {o : Outcome}
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (hmiss : ∀ x ∈ weth9Sels, Sevm.selector sevm ≠ x)
    (k : SFunc.RunExact prog sevm (St b [Sevm.selector sevm] memFp g) t_00af_c0 o) :
    SFunc.RunExact prog sevm (St b [] Mem.empty (g + 304)) t_0000_c0 o := by
  have h : ∀ x ∈ weth9Sels, x ≠ Sevm.selector sevm := fun x hx h' => hmiss x hx h'.symm
  simp only [weth9Sels, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine dispatch_head h_len h_len' h1 ?_
  refine cmp_miss h2 ?_
  refine cmp_miss h3 ?_
  refine cmp_miss h4 ?_
  refine cmp_miss h5 ?_
  refine cmp_miss h6 ?_
  refine cmp_miss h7 ?_
  refine cmp_miss h8 ?_
  refine cmp_miss h9 ?_
  refine cmp_miss h10 ?_
  exact cmp_miss h11 k

/-- The `SLOAD` of `balanceOf[caller]` a deposit does: `gasWarmAccess` if the slot is accessed,
`gasColdSload` otherwise. -/
def depositLoad (sevm : Sevm) (pre : Devm) : Nat := sloadCost sevm pre (balSlot sevm.caller)

/-- The `SSTORE` of `balanceOf[caller] += callvalue`, after that `SLOAD` has warmed the slot: no cold
surcharge, `gasStorageSet` for a first write over a zero original, `gasStorageUpdate - gasColdSload`
for a first change of a nonzero one, `gasWarmAccess` otherwise (a zero deposit is a no-op write). -/
def depositStore (sevm : Sevm) (pre : Devm) : Nat :=
  sstoreCost sevm (afterSload sevm pre (balSlot sevm.caller)) (balSlot sevm.caller)
    (pre.getStorVal sevm.currentTarget (balSlot sevm.caller) + sevm.value)

/-- **What a `deposit()` call costs**: the dispatcher (282), the wrapper (15 + 1), the body (104 + 16 +
1456) and the storage charges. -/
def depositGas (sevm : Sevm) (pre : Devm) : Nat :=
  1874 + depositLoad sevm pre + depositStore sevm pre

/-- **What a payable-fallback call with calldata shorter than four bytes costs**: the head (39), the
wrapper (15 + 1), the body. -/
def fallbackShortGas (sevm : Sevm) (pre : Devm) : Nat :=
  1631 + depositLoad sevm pre + depositStore sevm pre

/-- **What a payable-fallback call with no matching selector costs**: the eleven misses (304), the
wrapper (15 + 1), the body. -/
def fallbackGas (sevm : Sevm) (pre : Devm) : Nat :=
  1896 + depositLoad sevm pre + depositStore sevm pre

/-- A frame entering `deposit()` (any callvalue) succeeds at exactly `depositGas`. -/
theorem weth9_deposit_runExact {sevm : Sevm} {pre : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (h_static : sevm.isStatic = false)
    (h_sel : Sevm.selector sevm = dpSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (h_gas : pre.gasLeft = G + depositGas sevm pre)
    (h_sentry : gCallStipend < G + 1457 + depositStore sevm pre) :
    ∃ post, SProg.RunExact prog sevm pre post ∧ post.gasLeft = G ∧ post.output = pre.output := by
  have hsel : Sevm.selector sevm = 0xd0e30db0 := h_sel.trans dpSel_eq
  have hg : G + 1 + 1456 + sstoreCost sevm (afterSload sevm pre (balSlot sevm.caller))
      (balSlot sevm.caller) (pre.getStorVal sevm.currentTarget (balSlot sevm.caller) + sevm.value)
      + 16 + sloadCost sevm pre (balSlot sevm.caller) + 104 + 15 + 282 = pre.gasLeft := by
    rw [h_gas]; unfold depositGas depositLoad depositStore
    generalize sstoreCost sevm (afterSload sevm pre (balSlot sevm.caller)) (balSlot sevm.caller)
      (pre.getStorVal sevm.currentTarget (balSlot sevm.caller) + sevm.value) = s
    generalize sloadCost sevm pre (balSlot sevm.caller) = l
    omega
  have hs : gCallStipend < G + 1 + 1456 + sstoreCost sevm
      (afterSload sevm pre (balSlot sevm.caller)) (balSlot sevm.caller)
      (pre.getStorVal sevm.currentTarget (balSlot sevm.caller) + sevm.value) := by
    have := h_sentry
    unfold depositStore at this
    have e : gCallStipend = 2300 := rfl
    rw [e] at this ⊢
    generalize sstoreCost sevm (afterSload sevm pre (balSlot sevm.caller)) (balSlot sevm.caller)
      (pre.getStorVal sevm.currentTarget (balSlot sevm.caller) + sevm.value) = s at this ⊢
    omega
  obtain ⟨post, hrun, hpg, hpo⟩ := deposit_wrap (T := t_03ca_c19) (S := [Sevm.selector sevm])
    (G := G) (b := pre) rfl hfork h_static (by simp only [List.length_cons, List.length_nil,
      zero_add, Nat.one_lt_ofNat]) hs
  refine ⟨post, ⟨_, rfl, ?_⟩, hpg, hpo⟩
  have h0 := dispatch_deposit (b := pre) h_len h_len' hsel hrun
  rw [pre_eq_St h_stack h_mem hg] at h0
  exact h0

/-- A frame with calldata shorter than four bytes enters the payable fallback and succeeds at exactly
`fallbackShortGas`. -/
theorem weth9_fallback_short_runExact {sevm : Sevm} {pre : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (h_static : sevm.isStatic = false)
    (h_short : sevm.data.length.toB256 < 4)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (h_gas : pre.gasLeft = G + fallbackShortGas sevm pre)
    (h_sentry : gCallStipend < G + 1457 + depositStore sevm pre) :
    ∃ post, SProg.RunExact prog sevm pre post ∧ post.gasLeft = G ∧ post.output = pre.output := by
  have hg : G + 1 + 1456 + sstoreCost sevm (afterSload sevm pre (balSlot sevm.caller))
      (balSlot sevm.caller) (pre.getStorVal sevm.currentTarget (balSlot sevm.caller) + sevm.value)
      + 16 + sloadCost sevm pre (balSlot sevm.caller) + 104 + 15 + 39 = pre.gasLeft := by
    rw [h_gas]; unfold fallbackShortGas depositLoad depositStore
    generalize sstoreCost sevm (afterSload sevm pre (balSlot sevm.caller)) (balSlot sevm.caller)
      (pre.getStorVal sevm.currentTarget (balSlot sevm.caller) + sevm.value) = s
    generalize sloadCost sevm pre (balSlot sevm.caller) = l
    omega
  have hs : gCallStipend < G + 1 + 1456 + sstoreCost sevm
      (afterSload sevm pre (balSlot sevm.caller)) (balSlot sevm.caller)
      (pre.getStorVal sevm.currentTarget (balSlot sevm.caller) + sevm.value) := by
    have := h_sentry
    unfold depositStore at this
    have e : gCallStipend = 2300 := rfl
    rw [e] at this ⊢
    generalize sstoreCost sevm (afterSload sevm pre (balSlot sevm.caller)) (balSlot sevm.caller)
      (pre.getStorVal sevm.currentTarget (balSlot sevm.caller) + sevm.value) = s at this ⊢
    omega
  obtain ⟨post, hrun, hpg, hpo⟩ := deposit_wrap (T := t_00af_c0) (S := [])
    (G := G) (b := pre) rfl hfork h_static (by simp only [List.length_nil, Nat.ofNat_pos]) hs
  refine ⟨post, ⟨_, rfl, ?_⟩, hpg, hpo⟩
  have h0 := dispatch_short (b := pre) h_short hrun
  rw [pre_eq_St h_stack h_mem hg] at h0
  exact h0

/-- A frame whose selector matches none of the eleven enters the payable fallback and succeeds at
exactly `fallbackGas`. -/
theorem weth9_fallback_runExact {sevm : Sevm} {pre : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (h_static : sevm.isStatic = false)
    (hmiss : ∀ x ∈ weth9Sels, Sevm.selector sevm ≠ x)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (h_gas : pre.gasLeft = G + fallbackGas sevm pre)
    (h_sentry : gCallStipend < G + 1457 + depositStore sevm pre) :
    ∃ post, SProg.RunExact prog sevm pre post ∧ post.gasLeft = G ∧ post.output = pre.output := by
  have hg : G + 1 + 1456 + sstoreCost sevm (afterSload sevm pre (balSlot sevm.caller))
      (balSlot sevm.caller) (pre.getStorVal sevm.currentTarget (balSlot sevm.caller) + sevm.value)
      + 16 + sloadCost sevm pre (balSlot sevm.caller) + 104 + 15 + 304 = pre.gasLeft := by
    rw [h_gas]; unfold fallbackGas depositLoad depositStore
    generalize sstoreCost sevm (afterSload sevm pre (balSlot sevm.caller)) (balSlot sevm.caller)
      (pre.getStorVal sevm.currentTarget (balSlot sevm.caller) + sevm.value) = s
    generalize sloadCost sevm pre (balSlot sevm.caller) = l
    omega
  have hs : gCallStipend < G + 1 + 1456 + sstoreCost sevm
      (afterSload sevm pre (balSlot sevm.caller)) (balSlot sevm.caller)
      (pre.getStorVal sevm.currentTarget (balSlot sevm.caller) + sevm.value) := by
    have := h_sentry
    unfold depositStore at this
    have e : gCallStipend = 2300 := rfl
    rw [e] at this ⊢
    generalize sstoreCost sevm (afterSload sevm pre (balSlot sevm.caller)) (balSlot sevm.caller)
      (pre.getStorVal sevm.currentTarget (balSlot sevm.caller) + sevm.value) = s at this ⊢
    omega
  obtain ⟨post, hrun, hpg, hpo⟩ := deposit_wrap (T := t_00af_c0) (S := [Sevm.selector sevm])
    (G := G) (b := pre) rfl hfork h_static (by simp only [List.length_cons, List.length_nil,
      zero_add, Nat.one_lt_ofNat]) hs
  refine ⟨post, ⟨_, rfl, ?_⟩, hpg, hpo⟩
  have h0 := dispatch_miss (b := pre) h_len h_len' hmiss hrun
  rw [pre_eq_St h_stack h_mem hg] at h0
  exact h0

end Blanc.Lift.Weth9
