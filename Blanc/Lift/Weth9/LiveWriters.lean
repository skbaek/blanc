import Blanc.Lift.Weth9.Effects
import Blanc.Lift.Weth9.LiveWithdraw
import Blanc.Lift.Weth9.LiveTransfer

/-!
# The deployed WETH9's writers are live, gas-exact

For each writer of the deployed runtime — `approve`, `deposit` (and the payable fallback), `transfer`,
`transferFrom` (three allowance cases) and `withdraw` — a successful **execution** of the deployed
bytes from a fresh frame with an explicit gas cost, ending in the storage the model says.  The runs are
the gas-exact synthetic runs of `LiveApprove`/`LiveDeposit`/`LiveTransfer`/`LiveWithdraw`, made real
executions by `exec_of_runExact`; the storage effect of every writer but `withdraw` is
`weth9_frame_effect` on the same run, and `withdraw`'s is read off its own run.

Costs are explicit sums over the dispatcher, the wrappers, the bodies and the storage/account charges
(`sloadCost`, `sstoreCost`, `callNet`: warm/cold per key and account), each `≥` its fixed part; the
gas premise `pre.gasLeft = G + cost` leaves `G` at the end.  The EIP-2200 sentry of the last `SSTORE`
(more than `gCallStipend` gas then) is implied by the bound on `G` each theorem states.
-/

namespace Blanc.Lift.Weth9

open Jaune Blanc Blanc.Lift

/-- Calldata of at least four bytes is not the fallback's short call. -/
theorem not_shortCall {sevm : Sevm} (h_len : 4 ≤ sevm.data.length)
    (h_len' : sevm.data.length < 2 ^ 256) : ¬ shortCall sevm := by
  unfold shortCall
  intro h
  have h1 := B256.toNat_lt_toNat h
  rw [B256.toNat_toB256_of_lt h_len'] at h1
  have h4 : (4 : B256).toNat = 4 := rfl
  omega

/-- The storage effect of a successful run that decodes as the non-withdraw writer `c`. -/
theorem writer_effect {sevm : Sevm} {pre post : Devm} {c : Call}
    (hfork : CoveredFork sevm.benvStat.fork) (hrun : SProg.RunExact prog sevm pre post)
    (hdec : decodeCall sevm = some c) (hnw : ∀ who w, c ≠ .withdraw who w) :
    c.stor (Devm.getStor pre sevm.currentTarget) = some (Devm.getStor post sevm.currentTarget) := by
  obtain ⟨f, hf, run⟩ := hrun
  rcases weth9_frame_effect (P := Ninst.Run) (fun h => h) hfork ⟨f, hf, run.toRun⟩ with
    ⟨hn, -⟩ | ⟨c', hc', -, hst⟩ | ⟨who, w, hw, -⟩
  · rw [hdec] at hn; cases hn
  · rw [hdec] at hc'; cases hc'; exact hst
  · rw [hdec] at hw; cases hw; exact absurd rfl (hnw _ _)

/-- **`approve(guy, wad)` is live, gas-exact.**  A fresh frame (empty stack and memory) calling
`approve` with no value, not static, at gas `G + approveGas` with `380 ≤ G`, succeeds ending at gas `G`
with `true` returned, and writes `allowance[caller][guy] := wad`. -/
theorem weth9_approve_live {sevm : Sevm} {pre : Devm} {G : Nat}
    (h_code : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (h_static : sevm.isStatic = false) (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = apSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (h_gas : pre.gasLeft = G + approveGas sevm pre) (hG : 380 ≤ G) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧ post.gasLeft = G ∧
      post.output = (1 : B256).toBytes ∧
      Devm.getStor post sevm.currentTarget = (Devm.getStor pre sevm.currentTarget).set
        (allowSlot sevm.caller (Sevm.dataWord sevm 4).toAdr) (Sevm.dataWord sevm 36) := by
  have hsent : gCallStipend + 399 < pre.gasLeft := by
    rw [h_gas]; unfold approveGas
    generalize sstoreCost sevm pre (allowSlot sevm.caller (Sevm.dataWord sevm 4).toAdr)
      (Sevm.dataWord sevm 36) = s
    have e : gCallStipend = 2300 := rfl
    omega
  obtain ⟨post, hrun, hg, ho⟩ := weth9_approve_runExact hfork h_static h_value h_sel h_len h_len'
    h_stack h_mem h_gas hsent
  have hdec : decodeCall sevm = some (.approve sevm.caller (Sevm.dataWord sevm 4).toAdr
      (Sevm.dataWord sevm 36)) := by
    have hs : Sevm.selector sevm = 0x095ea7b3 := h_sel.trans apSel_eq
    unfold decodeCall
    simp (config := {decide := true}) [not_shortCall h_len h_len', hs]
  have heff := writer_effect hfork hrun hdec (by intro who w h; cases h)
  simp only [Call.stor, Option.some.injEq] at heff
  exact ⟨post, (exec_iff_exec_eq 0 sevm pre (.ok post)).mp (exec_of_runExact h_code hfork hrun), hg,
    ho, heff.symm⟩


theorem weth9Sels_eq : weth9Sels = linkSels := linkSels_eq.symm

/-- **`deposit()` is live, gas-exact.**  Any callvalue: a fresh frame calling `deposit()` at gas
`G + depositGas` with `844 ≤ G` succeeds ending at gas `G` and credits the caller. -/
theorem weth9_deposit_live {sevm : Sevm} {pre : Devm} {G : Nat}
    (h_code : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (h_static : sevm.isStatic = false) (h_sel : Sevm.selector sevm = dpSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (h_gas : pre.gasLeft = G + depositGas sevm pre) (hG : 844 ≤ G) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧ post.gasLeft = G ∧ post.output = pre.output ∧
      Devm.getStor post sevm.currentTarget = (Devm.getStor pre sevm.currentTarget).set
        (balSlot sevm.caller)
        ((Devm.getStor pre sevm.currentTarget).get (balSlot sevm.caller) + sevm.value) := by
  have hs : gCallStipend < G + 1457 + depositStore sevm pre := by
    have e : gCallStipend = 2300 := rfl
    omega
  obtain ⟨post, hrun, hg, ho⟩ := weth9_deposit_runExact hfork h_static h_sel h_len h_len' h_stack
    h_mem h_gas hs
  have hdec : decodeCall sevm = some (.deposit sevm.caller sevm.value) := by
    have hs' : Sevm.selector sevm = 0xd0e30db0 := h_sel.trans dpSel_eq
    unfold decodeCall
    simp (config := {decide := true}) [not_shortCall h_len h_len', hs']
  have heff := writer_effect hfork hrun hdec (by intro who w h; cases h)
  simp only [Call.stor, Option.some.injEq] at heff
  exact ⟨post, (exec_iff_exec_eq 0 sevm pre (.ok post)).mp (exec_of_runExact h_code hfork hrun), hg,
    ho, heff.symm⟩

/-- **The payable fallback, calldata shorter than four bytes, is live, gas-exact.** -/
theorem weth9_fallback_short_live {sevm : Sevm} {pre : Devm} {G : Nat}
    (h_code : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (h_static : sevm.isStatic = false) (h_short : shortCall sevm)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (h_gas : pre.gasLeft = G + fallbackShortGas sevm pre) (hG : 844 ≤ G) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧ post.gasLeft = G ∧ post.output = pre.output ∧
      Devm.getStor post sevm.currentTarget = (Devm.getStor pre sevm.currentTarget).set
        (balSlot sevm.caller)
        ((Devm.getStor pre sevm.currentTarget).get (balSlot sevm.caller) + sevm.value) := by
  have hs : gCallStipend < G + 1457 + depositStore sevm pre := by
    have e : gCallStipend = 2300 := rfl
    omega
  obtain ⟨post, hrun, hg, ho⟩ := weth9_fallback_short_runExact hfork h_static h_short h_stack
    h_mem h_gas hs
  have hdec : decodeCall sevm = some (.deposit sevm.caller sevm.value) := by
    unfold decodeCall
    simp [h_short]
  have heff := writer_effect hfork hrun hdec (by intro who w h; cases h)
  simp only [Call.stor, Option.some.injEq] at heff
  exact ⟨post, (exec_iff_exec_eq 0 sevm pre (.ok post)).mp (exec_of_runExact h_code hfork hrun), hg,
    ho, heff.symm⟩

/-- **The payable fallback, no selector matching, is live, gas-exact.** -/
theorem weth9_fallback_live {sevm : Sevm} {pre : Devm} {G : Nat}
    (h_code : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (h_static : sevm.isStatic = false)
    (hmiss : ∀ x ∈ weth9Sels, Sevm.selector sevm ≠ x)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (h_gas : pre.gasLeft = G + fallbackGas sevm pre) (hG : 844 ≤ G) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧ post.gasLeft = G ∧ post.output = pre.output ∧
      Devm.getStor post sevm.currentTarget = (Devm.getStor pre sevm.currentTarget).set
        (balSlot sevm.caller)
        ((Devm.getStor pre sevm.currentTarget).get (balSlot sevm.caller) + sevm.value) := by
  have hs : gCallStipend < G + 1457 + depositStore sevm pre := by
    have e : gCallStipend = 2300 := rfl
    omega
  obtain ⟨post, hrun, hg, ho⟩ := weth9_fallback_runExact hfork h_static hmiss h_len h_len' h_stack
    h_mem h_gas hs
  have hdec : decodeCall sevm = some (.deposit sevm.caller sevm.value) :=
    decode_miss (Or.inr (fun l hl heq =>
      hmiss _ (by rw [weth9Sels_eq]; exact mem_linkSels.mpr ⟨l, hl, rfl⟩) heq))
  have heff := writer_effect hfork hrun hdec (by intro who w h; cases h)
  simp only [Call.stor, Option.some.injEq] at heff
  exact ⟨post, (exec_iff_exec_eq 0 sevm pre (.ok post)).mp (exec_of_runExact h_code hfork hrun), hg,
    ho, heff.symm⟩


/-- **`transferFrom(src, dst, wad)` is live, gas-exact, when the caller is `src`.**  With
`wad ≤ balanceOf[src]`, at gas `G + transferFromGasSelf` with `377 ≤ G` the call succeeds ending at gas
`G` with `true` returned and the storage effect `xferStorStep` (no allowance touched). -/
theorem weth9_transferFrom_self_live {sevm : Sevm} {pre : Devm} {G : Nat}
    (h_code : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (h_static : sevm.isStatic = false) (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = tfSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (hcs : sevm.caller = (Sevm.dataWord sevm 4).toAdr)
    (hle : Sevm.dataWord sevm 68 ≤
      pre.getStorVal sevm.currentTarget (balSlot (Sevm.dataWord sevm 4).toAdr))
    (h_gas : pre.gasLeft = G + transferFromGasSelf sevm pre) (hG : 377 ≤ G) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧ post.gasLeft = G ∧
      post.output = (1 : B256).toBytes ∧
      xferStorStep (Devm.getStor pre sevm.currentTarget) sevm.caller (Sevm.dataWord sevm 4).toAdr
        (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68) =
        some (Devm.getStor post sevm.currentTarget) := by
  obtain ⟨post, hrun, hg, ho⟩ := weth9_transferFrom_self_runExact hfork h_static h_value h_sel h_len
    h_len' h_stack h_mem hcs hle h_gas
    (Nat.lt_add_right _ (by unfold gCallStipend; omega))
  have hdec : decodeCall sevm = some (.transferFrom sevm.caller (Sevm.dataWord sevm 4).toAdr
      (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68)) := by
    have hs : Sevm.selector sevm = 0x23b872dd := h_sel.trans tfSel_eq
    unfold decodeCall
    simp (config := {decide := true}) [not_shortCall h_len h_len', hs]
  have heff := writer_effect hfork hrun hdec (by intro who w h; cases h)
  simp only [Call.stor] at heff
  exact ⟨post, (exec_iff_exec_eq 0 sevm pre (.ok post)).mp (exec_of_runExact h_code hfork hrun), hg,
    ho, heff⟩

/-- **`transferFrom(src, dst, wad)` is live, gas-exact, when the caller is not `src` and the allowance
is the maximal word** (the sentinel: read, not debited). -/
theorem weth9_transferFrom_max_live {sevm : Sevm} {pre : Devm} {G : Nat}
    (h_code : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (h_static : sevm.isStatic = false) (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = tfSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (hcs : sevm.caller ≠ (Sevm.dataWord sevm 4).toAdr)
    (hle : Sevm.dataWord sevm 68 ≤
      pre.getStorVal sevm.currentTarget (balSlot (Sevm.dataWord sevm 4).toAdr))
    (hmax : pre.getStorVal sevm.currentTarget
      (allowSlot (Sevm.dataWord sevm 4).toAdr sevm.caller) = B256.max)
    (h_gas : pre.gasLeft = G + transferFromGasMax sevm pre) (hG : 377 ≤ G) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧ post.gasLeft = G ∧
      post.output = (1 : B256).toBytes ∧
      xferStorStep (Devm.getStor pre sevm.currentTarget) sevm.caller (Sevm.dataWord sevm 4).toAdr
        (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68) =
        some (Devm.getStor post sevm.currentTarget) := by
  obtain ⟨post, hrun, hg, ho⟩ := weth9_transferFrom_max_runExact hfork h_static h_value h_sel h_len
    h_len' h_stack h_mem hcs hle hmax h_gas
    (Nat.lt_add_right _ (by unfold gCallStipend; omega))
  have hdec : decodeCall sevm = some (.transferFrom sevm.caller (Sevm.dataWord sevm 4).toAdr
      (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68)) := by
    have hs : Sevm.selector sevm = 0x23b872dd := h_sel.trans tfSel_eq
    unfold decodeCall
    simp (config := {decide := true}) [not_shortCall h_len h_len', hs]
  have heff := writer_effect hfork hrun hdec (by intro who w h; cases h)
  simp only [Call.stor] at heff
  exact ⟨post, (exec_iff_exec_eq 0 sevm pre (.ok post)).mp (exec_of_runExact h_code hfork hrun), hg,
    ho, heff⟩

/-- **`transferFrom(src, dst, wad)` is live, gas-exact, when the caller is not `src`, the allowance is
not the maximal word and covers `wad`** (checked and debited). -/
theorem weth9_transferFrom_allow_live {sevm : Sevm} {pre : Devm} {G : Nat}
    (h_code : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (h_static : sevm.isStatic = false) (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = tfSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (hcs : sevm.caller ≠ (Sevm.dataWord sevm 4).toAdr)
    (hle : Sevm.dataWord sevm 68 ≤
      pre.getStorVal sevm.currentTarget (balSlot (Sevm.dataWord sevm 4).toAdr))
    (hmax : pre.getStorVal sevm.currentTarget
      (allowSlot (Sevm.dataWord sevm 4).toAdr sevm.caller) ≠ B256.max)
    (hal : Sevm.dataWord sevm 68 ≤ pre.getStorVal sevm.currentTarget
      (allowSlot (Sevm.dataWord sevm 4).toAdr sevm.caller))
    (h_gas : pre.gasLeft = G + transferFromGasAllow sevm pre) (hG : 377 ≤ G) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧ post.gasLeft = G ∧
      post.output = (1 : B256).toBytes ∧
      xferStorStep (Devm.getStor pre sevm.currentTarget) sevm.caller (Sevm.dataWord sevm 4).toAdr
        (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68) =
        some (Devm.getStor post sevm.currentTarget) := by
  obtain ⟨post, hrun, hg, ho⟩ := weth9_transferFrom_allow_runExact hfork h_static h_value h_sel
    h_len h_len' h_stack h_mem hcs hle hmax hal h_gas
    (Nat.lt_add_right _ (by unfold gCallStipend; omega))
  have hdec : decodeCall sevm = some (.transferFrom sevm.caller (Sevm.dataWord sevm 4).toAdr
      (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68)) := by
    have hs : Sevm.selector sevm = 0x23b872dd := h_sel.trans tfSel_eq
    unfold decodeCall
    simp (config := {decide := true}) [not_shortCall h_len h_len', hs]
  have heff := writer_effect hfork hrun hdec (by intro who w h; cases h)
  simp only [Call.stor] at heff
  exact ⟨post, (exec_iff_exec_eq 0 sevm pre (.ok post)).mp (exec_of_runExact h_code hfork hrun), hg,
    ho, heff⟩

/-- **`transfer(dst, wad)` is live, gas-exact.**  With `wad ≤ balanceOf[caller]`, at gas
`G + transferGas` with `353 ≤ G` the call succeeds ending at gas `G` with `true` returned; the storage
effect is that of `transferFrom(caller, dst, wad)` by the caller. -/
theorem weth9_transfer_live {sevm : Sevm} {pre : Devm} {G : Nat}
    (h_code : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (h_static : sevm.isStatic = false) (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = trSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (hle : Sevm.dataWord sevm 36 ≤ pre.getStorVal sevm.currentTarget (balSlot sevm.caller))
    (h_gas : pre.gasLeft = G + transferGas sevm pre) (hG : 353 ≤ G) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧ post.gasLeft = G ∧
      post.output = (1 : B256).toBytes ∧
      xferStorStep (Devm.getStor pre sevm.currentTarget) sevm.caller sevm.caller
        (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36) =
        some (Devm.getStor post sevm.currentTarget) := by
  obtain ⟨post, hrun, hg, ho⟩ := weth9_transfer_runExact hfork h_static h_value h_sel h_len h_len'
    h_stack h_mem hle h_gas (Nat.lt_add_right _ (by unfold gCallStipend; omega))
  have hdec : decodeCall sevm = some (.transfer sevm.caller (Sevm.dataWord sevm 4).toAdr
      (Sevm.dataWord sevm 36)) := by
    have hs : Sevm.selector sevm = 0xa9059cbb := h_sel.trans trSel_eq
    unfold decodeCall
    simp (config := {decide := true}) [not_shortCall h_len h_len', hs]
  have heff := writer_effect hfork hrun hdec (by intro who w h; cases h)
  simp only [Call.stor] at heff
  exact ⟨post, (exec_iff_exec_eq 0 sevm pre (.ok post)).mp (exec_of_runExact h_code hfork hrun), hg,
    ho, heff⟩

theorem callNet_ge (b : Devm) (a : Adr) : 6800 ≤ callNet b a := by
  unfold callNet accessCost
  have e : gasCallValue = 9000 := rfl
  have e' : gCallStipend = 2300 := rfl
  have e2 : gasWarmAccess = 100 := rfl
  have e3 : gasColdAccountAccess = 2600 := rfl
  split_ifs <;> omega

/-- **`withdraw(wad)` to an externally owned account is live, gas-exact.**  With `0 < wad ≤
balanceOf[caller]`, a caller without code that is no precompile, the contract holding the ether and the
frame not the outermost, at gas `G + withdrawGas` with `811 ≤ G` the call succeeds ending at gas `G`;
it debits the caller's balance slot and no other storage, and returns nothing. -/
theorem weth9_withdraw_live {sevm : Sevm} {pre : Devm} {G : Nat}
    (h_code : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (h_static : sevm.isStatic = false) (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = wdSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty) (h_depth : sevm.depth ≠ 0)
    (hwad : Sevm.dataWord sevm 4 ≠ 0)
    (hle : Sevm.dataWord sevm 4 ≤ pre.getStorVal sevm.currentTarget (balSlot sevm.caller))
    (h_eoa : (pre.getCode sevm.caller).size = 0)
    (h_prec : sevm.benvStat.rules.isPrecomp sevm.caller = false)
    (h_eth : ¬ (pre.getAcct sevm.currentTarget).bal < Sevm.dataWord sevm 4)
    (h_gas : pre.gasLeft = G + withdrawGas sevm pre) (hG : 811 ≤ G) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧ post.gasLeft = G ∧ post.output = pre.output ∧
      Devm.getStor post sevm.currentTarget = (Devm.getStor pre sevm.currentTarget).set
        (balSlot sevm.caller)
        (pre.getStorVal sevm.currentTarget (balSlot sevm.caller) - Sevm.dataWord sevm 4) ∧
      ∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor pre a := by
  have hcn := callNet_ge pre sevm.caller
  obtain ⟨post, hrun, hg, ho, hs1, hs2⟩ := weth9_withdraw_runExact hfork h_static h_value h_sel h_len
    h_len' h_stack h_mem h_depth hwad hle h_eoa h_prec h_eth h_gas
    (by
      have e : gCallStipend = 2300 := rfl
      generalize callNet pre sevm.caller = x at hcn ⊢
      generalize sstoreCost sevm (wB2 sevm pre) (balSlot sevm.caller)
        (wV sevm pre (Sevm.dataWord sevm 4)) = y
      omega)
    (by have e : gCallStipend = 2300 := rfl; omega)
  exact ⟨post, (exec_iff_exec_eq 0 sevm pre (.ok post)).mp (exec_of_runExact h_code hfork hrun), hg,
    ho, hs1, hs2⟩

end Blanc.Lift.Weth9
