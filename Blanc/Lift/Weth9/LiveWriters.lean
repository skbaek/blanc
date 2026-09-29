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


/-! ## From the model's acceptance to the storage-level premises -/

/-- **A call the model accepts at the tracked keys has a storage effect**: the model's `require`s at the
tracked words are the runtime's at the stored words. -/
theorem Call.stor_ne_none_of_step {K : Key → Prop} {s : Stor} {c : Call} {l' : Ledger}
    (hkeys : ∀ k ∈ c.keys, K k) (h : (ledger K s).step c = some l') :
    c.stor s ≠ none := by
  cases c with
  | deposit who v => simp [Call.stor]
  | approve who g w => simp [Call.stor]
  | withdraw who w =>
    have hw : K (.bal who) := hkeys _ (by simp [Call.keys])
    have hb : (ledger K s).bal who = s.get (balSlot who) := tracked_self hw
    rw [Ledger.step_withdraw, hb] at h
    by_cases hlt : s.get (balSlot who) < w
    · simp [hlt] at h
    · simp [Call.stor, hlt]
  | transfer who dst w =>
    have hw : K (.bal who) := hkeys _ (by simp [Call.keys])
    have hb : (ledger K s).bal who = s.get (balSlot who) := tracked_self hw
    rw [Ledger.step_transfer] at h
    unfold Ledger.transferFrom at h
    rw [hb] at h
    by_cases hlt : s.get (balSlot who) < w
    · simp [hlt] at h
    · simp [Call.stor, xferStorStep, hlt]
  | transferFrom who src dst w =>
    have hsrc : K (.bal src) := hkeys _ (by simp [Call.keys])
    have hal : K (.allow src who) := hkeys _ (by simp [Call.keys])
    have hb : (ledger K s).bal src = s.get (balSlot src) := tracked_self hsrc
    have ha : (ledger K s).allow src who = s.get (allowSlot src who) := trackedAllow_self hal
    rw [Ledger.step_transferFrom] at h
    unfold Ledger.transferFrom at h
    rw [hb, ha] at h
    by_cases hlt : s.get (balSlot src) < w
    · simp [hlt] at h
    · simp only [hlt, ↓reduceIte] at h
      by_cases hc : src ≠ who ∧ s.get (allowSlot src who) ≠ B256.max
      · have hc' : src ≠ who ∧ s.get (allowSlot src who) ≠ maxAllowance := hc
        simp only [hc'.1, ne_eq, not_false_eq_true, hc'.2, and_self, ↓reduceIte] at h
        by_cases hl2 : s.get (allowSlot src who) < w
        · simp [hl2] at h
        · simp [Call.stor, xferStorStep, hlt, hc, hl2]
      · simp [Call.stor, xferStorStep, hlt, hc]


/-- What `xferStorStep` succeeding says about the words it reads. -/
theorem xferStorStep_ok {s s' : Stor} {who src dst : Adr} {wad : B256}
    (h : xferStorStep s who src dst wad = some s') :
    wad ≤ s.get (balSlot src) ∧
      (src = who ∨ s.get (allowSlot src who) = B256.max ∨ wad ≤ s.get (allowSlot src who)) := by
  unfold xferStorStep at h
  by_cases hlt : s.get (balSlot src) < wad
  · simp [hlt] at h
  · refine ⟨B256.not_lt.mp hlt, ?_⟩
    simp only [hlt, ↓reduceIte] at h
    by_cases hc : src ≠ who ∧ s.get (allowSlot src who) ≠ B256.max
    · simp only [hc.1, ne_eq, not_false_eq_true, hc.2, and_self, ↓reduceIte] at h
      by_cases hl2 : s.get (allowSlot src who) < wad
      · simp [hl2] at h
      · exact Or.inr (Or.inr (B256.not_lt.mp hl2))
    · by_cases hs : src = who
      · exact Or.inl hs
      · exact Or.inr (Or.inl (by
          by_contra hne
          exact hc ⟨hs, hne⟩))

/-- **What `transferFrom(src, dst, wad)` costs**, by the allowance case the caller is in. -/
def transferFromGas (sevm : Sevm) (pre : Devm) : Nat :=
  if sevm.caller = (Sevm.dataWord sevm 4).toAdr then transferFromGasSelf sevm pre
  else if pre.getStorVal sevm.currentTarget (allowSlot (Sevm.dataWord sevm 4).toAdr sevm.caller) =
      B256.max then transferFromGasMax sevm pre
  else transferFromGasAllow sevm pre

/-- **`transferFrom(src, dst, wad)` is live, gas-exact, whenever its storage effect exists** (the
runtime's `require`s: `wad ≤ balanceOf[src]` and, unless the caller is `src` or the allowance is the
maximal word, `wad ≤ allowance`), at `transferFromGas`.  The three cases of the code are one theorem. -/
theorem weth9_transferFrom_live {sevm : Sevm} {pre : Devm} {G : Nat} {s' : Stor}
    (h_code : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (h_static : sevm.isStatic = false) (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = tfSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (hok : xferStorStep (Devm.getStor pre sevm.currentTarget) sevm.caller
      (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68) = some s')
    (h_gas : pre.gasLeft = G + transferFromGas sevm pre) (hG : 377 ≤ G) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧ post.gasLeft = G ∧
      post.output = (1 : B256).toBytes ∧
      xferStorStep (Devm.getStor pre sevm.currentTarget) sevm.caller (Sevm.dataWord sevm 4).toAdr
        (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68) =
        some (Devm.getStor post sevm.currentTarget) := by
  obtain ⟨hle, hcases⟩ := xferStorStep_ok hok
  have hle' : Sevm.dataWord sevm 68 ≤
      pre.getStorVal sevm.currentTarget (balSlot (Sevm.dataWord sevm 4).toAdr) := hle
  unfold transferFromGas at h_gas
  by_cases hcs : sevm.caller = (Sevm.dataWord sevm 4).toAdr
  · simp only [hcs, ↓reduceIte] at h_gas
    exact weth9_transferFrom_self_live h_code hfork h_static h_value h_sel h_len h_len' h_stack h_mem
      hcs hle' h_gas hG
  · simp only [hcs, ↓reduceIte] at h_gas
    by_cases hmax : pre.getStorVal sevm.currentTarget
        (allowSlot (Sevm.dataWord sevm 4).toAdr sevm.caller) = B256.max
    · simp only [hmax, ↓reduceIte] at h_gas
      exact weth9_transferFrom_max_live h_code hfork h_static h_value h_sel h_len h_len' h_stack
        h_mem hcs hle' hmax h_gas hG
    · simp only [hmax, ↓reduceIte] at h_gas
      have hal : Sevm.dataWord sevm 68 ≤ pre.getStorVal sevm.currentTarget
          (allowSlot (Sevm.dataWord sevm 4).toAdr sevm.caller) := by
        rcases hcases with h | h | h
        · exact absurd h.symm hcs
        · exact absurd h hmax
        · exact h
      exact weth9_transferFrom_allow_live h_code hfork h_static h_value h_sel h_len h_len' h_stack
        h_mem hcs hle' hmax hal h_gas hG


theorem accessCost_ge (a : Adr) (s : AdrSet) : 100 ≤ accessCost a s := by
  unfold accessCost
  have e2 : gasWarmAccess = 100 := rfl
  have e3 : gasColdAccountAccess = 2600 := rfl
  split_ifs <;> omega

/-- **`withdraw(0)` to an externally owned account is live, gas-exact** (`643 ≤ G`). -/
theorem weth9_withdraw_zero_live {sevm : Sevm} {pre : Devm} {G : Nat}
    (h_code : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (h_static : sevm.isStatic = false) (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = wdSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty) (h_depth : sevm.depth ≠ 0)
    (hw0 : Sevm.dataWord sevm 4 = 0)
    (h_eoa : (pre.getCode sevm.caller).size = 0)
    (h_prec : sevm.benvStat.rules.isPrecomp sevm.caller = false)
    (h_gas : pre.gasLeft = G + withdrawZeroGas sevm pre) (hG : 643 ≤ G) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧ post.gasLeft = G ∧ post.output = pre.output ∧
      Devm.getStor post sevm.currentTarget = (Devm.getStor pre sevm.currentTarget).set
        (balSlot sevm.caller)
        (pre.getStorVal sevm.currentTarget (balSlot sevm.caller) - Sevm.dataWord sevm 4) ∧
      ∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor pre a := by
  have hac := accessCost_ge sevm.caller pre.accessedAddresses
  obtain ⟨post, hrun, hg, ho, hs1, hs2⟩ := weth9_withdraw_zero_runExact hfork h_static h_value h_sel
    h_len h_len' h_stack h_mem h_depth hw0 h_eoa h_prec h_gas
    (by
      have e : gCallStipend = 2300 := rfl
      generalize accessCost sevm.caller pre.accessedAddresses = x at hac ⊢
      generalize sstoreCost sevm (wB2 sevm pre) (balSlot sevm.caller)
        (wV sevm pre (Sevm.dataWord sevm 4)) = y
      omega)
  exact ⟨post, (exec_iff_exec_eq 0 sevm pre (.ok post)).mp (exec_of_runExact h_code hfork hrun), hg,
    ho, hs1, hs2⟩


/-- **`withdraw(wad)` to an externally owned account is live, gas-exact, for every `wad`** (`811 ≤ G`),
at the cost of its case. -/
def withdrawAnyGas (sevm : Sevm) (pre : Devm) : Nat :=
  if Sevm.dataWord sevm 4 = 0 then withdrawZeroGas sevm pre else withdrawGas sevm pre

theorem weth9_withdraw_any_live {sevm : Sevm} {pre : Devm} {G : Nat}
    (h_code : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (h_static : sevm.isStatic = false) (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = wdSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty) (h_depth : sevm.depth ≠ 0)
    (hle : Sevm.dataWord sevm 4 ≤ pre.getStorVal sevm.currentTarget (balSlot sevm.caller))
    (h_eoa : (pre.getCode sevm.caller).size = 0)
    (h_prec : sevm.benvStat.rules.isPrecomp sevm.caller = false)
    (h_eth : ¬ (pre.getAcct sevm.currentTarget).bal < Sevm.dataWord sevm 4)
    (h_gas : pre.gasLeft = G + withdrawAnyGas sevm pre) (hG : 811 ≤ G) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧ post.gasLeft = G ∧ post.output = pre.output ∧
      Devm.getStor post sevm.currentTarget = (Devm.getStor pre sevm.currentTarget).set
        (balSlot sevm.caller)
        (pre.getStorVal sevm.currentTarget (balSlot sevm.caller) - Sevm.dataWord sevm 4) ∧
      ∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor pre a := by
  unfold withdrawAnyGas at h_gas
  by_cases hw : Sevm.dataWord sevm 4 = 0
  · simp only [hw, ↓reduceIte] at h_gas
    exact weth9_withdraw_zero_live h_code hfork h_static h_value h_sel h_len h_len' h_stack h_mem
      h_depth hw h_eoa h_prec h_gas (by omega)
  · simp only [hw, ↓reduceIte] at h_gas
    exact weth9_withdraw_live h_code hfork h_static h_value h_sel h_len h_len' h_stack h_mem h_depth
      hw hle h_eoa h_prec h_eth h_gas hG


/-! ## Withdrawing to a contract

The recipient may have code.  Its run is then the callee's business, so `SendOk` is the premise: the
`CALL` the body makes to the caller, entered at gas `X ≥ Xmin` from the state the debit leaves, succeeds
(stack `1`, memory kept), leaves at least `1489` gas (the rest of the body needs `1488`, and the wrapper
one more), and changes no storage of the contract.  Everything else — the dispatcher, the checks, the debit,
the event — is proved as for an externally owned account. -/

/-- The callee premise for a send of `wad` to the caller, from the state `pre`. -/
def SendOk (sevm : Sevm) (pre : Devm) (wad sel : B256) (Xmin : Nat) : Prop :=
  ∀ X, Xmin ≤ X → ∃ post : Devm, ∃ r : Nat, 1489 ≤ r ∧
    Ninst.RunCompiled sevm
      (St (wB3 sevm pre wad) (0 :: sevm.caller.toB256 :: wad :: 96 :: (96 - 96) :: 96 :: 0 :: 96 ::
        wad :: 0 :: sevm.caller.toB256 :: wad :: Bytes.toB256 [2, 100] :: [sel])
        (scratchW (scratchW memFp sevm.caller.toB256 3) sevm.caller.toB256 3) X) (.exec .call) post ∧
    post = St post (1 :: 96 :: wad :: 0 :: sevm.caller.toB256 :: wad :: Bytes.toB256 [2, 100] :: [sel])
      (scratchW (scratchW memFp sevm.caller.toB256 3) sevm.caller.toB256 3) r ∧
    Devm.getStor post sevm.currentTarget = Devm.getStor (wB3 sevm pre wad) sevm.currentTarget ∧
    post.output = (wB3 sevm pre wad).output

/-- The gas `withdraw` spends before the `CALL` (`X` is what is left at it): the dispatcher, the wrapper,
the body up to the send, and the balance charges. -/
def withdrawSendPre (sevm : Sevm) (pre : Devm) : Nat :=
  551 + sloadCost sevm pre (balSlot sevm.caller) +
    sloadCost sevm (wB1 sevm pre) (balSlot sevm.caller) +
    sstoreCost sevm (wB2 sevm pre) (balSlot sevm.caller) (wV sevm pre (Sevm.dataWord sevm 4))

/-- **`withdraw(wad)` to a contract that answers the send is live** (`wad ≠ 0`, `wad ≤ balanceOf[caller]`):
given `SendOk`, at call-entry gas `X ≥ Xmin` the deployed code executes `withdraw` to success; the frame
ends with `r - 1489` gas, `r` the gas the callee's run leaves at the call, debiting the caller's balance
slot; nothing is claimed of other accounts' storage (the callee's is its own business). -/
theorem weth9_withdraw_send_live {sevm : Sevm} {pre : Devm} {X Xmin : Nat}
    (h_code : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (h_static : sevm.isStatic = false) (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = wdSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (hwad : Sevm.dataWord sevm 4 ≠ 0)
    (hle : Sevm.dataWord sevm 4 ≤ pre.getStorVal sevm.currentTarget (balSlot sevm.caller))
    (hsend : SendOk sevm pre (Sevm.dataWord sevm 4) (Sevm.selector sevm) Xmin) (hX : Xmin ≤ X)
    (h_gas : pre.gasLeft = X + withdrawSendPre sevm pre)
    (h_sentry : gCallStipend < X + 69 +
      sstoreCost sevm (wB2 sevm pre) (balSlot sevm.caller) (wV sevm pre (Sevm.dataWord sevm 4))) :
    ∃ post r, exec ⟨0, sevm, pre⟩ = .ok post ∧ 1489 ≤ r ∧ post.gasLeft + 1489 = r ∧
      post.output = pre.output ∧
      Devm.getStor post sevm.currentTarget = (Devm.getStor pre sevm.currentTarget).set
        (balSlot sevm.caller)
        (pre.getStorVal sevm.currentTarget (balSlot sevm.caller) - Sevm.dataWord sevm 4) := by
  have hsel : Sevm.selector sevm = 0x2e1a7d4d := h_sel.trans wdSel_eq
  obtain ⟨cp, r, hr, hrun, hSt, hstor, hout⟩ := hsend X hX
  obtain ⟨G, rfl⟩ : ∃ G, r = G + 1489 := ⟨r - 1489, by omega⟩
  have hSt' : cp = St cp (1 :: 96 :: Sevm.dataWord sevm 4 :: 0 :: sevm.caller.toB256 ::
      Sevm.dataWord sevm 4 :: Bytes.toB256 [2, 100] :: [Sevm.selector sevm])
      (scratchW (scratchW memFp sevm.caller.toB256 3) sevm.caller.toB256 3) (G + 1 + 1488) := hSt
  obtain ⟨cp', hQ, hbody⟩ := withdraw_body_send (sevm := sevm) (b := pre) (G := G + 1) (X := X)
    (S := [Sevm.selector sevm]) (M := memFp) (wad := Sevm.dataWord sevm 4)
    (ret := Bytes.toB256 [2, 100]) (cH := sloadCost sevm pre (balSlot sevm.caller))
    (c2 := sloadCost sevm (wB1 sevm pre) (balSlot sevm.caller))
    (cS := sstoreCost sevm (wB2 sevm pre) (balSlot sevm.caller) (wV sevm pre (Sevm.dataWord sevm 4)))
    (Q := fun p => Devm.getStor p sevm.currentTarget =
        Devm.getStor (wB3 sevm pre (Sevm.dataWord sevm 4)) sevm.currentTarget ∧
      p.output = (wB3 sevm pre (Sevm.dataWord sevm 4)).output)
    hfork h_static fp_memFp (by simp) hwad hle rfl rfl rfl h_sentry
    ⟨cp, hrun, hSt', hstor, hout⟩
  have hg : X + 69 + sstoreCost sevm (wB2 sevm pre) (balSlot sevm.caller)
      (wV sevm pre (Sevm.dataWord sevm 4)) + 16 + sloadCost sevm (wB1 sevm pre) (balSlot sevm.caller) +
      130 + sloadCost sevm pre (balSlot sevm.caller) + 96 + 68 + 172 = pre.gasLeft := by
    rw [h_gas]; unfold withdrawSendPre; omega
  obtain ⟨postW, hw, hpe⟩ := withdraw_wrapper (sevm := sevm) (b := pre) (G := G) (X := _)
    (sel := Sevm.selector sevm) h_value hbody
  have hrunP : SProg.RunExact prog sevm pre postW := by
    refine ⟨_, rfl, ?_⟩
    have h0 := dispatch_withdraw (b := pre) h_len h_len' hsel hw
    rw [pre_eq_St h_stack h_mem hg] at h0
    exact h0
  refine ⟨postW, G + 1489, (exec_iff_exec_eq 0 sevm pre (.ok postW)).mp
    (exec_of_runExact h_code hfork hrunP), by omega, ?_, ?_, ?_⟩
  · rw [hpe]; rfl
  · rw [hpe]
    show cp'.output = pre.output
    rw [hQ.2]
    simp [wB3, wB2, wB1]
  · rw [hpe]
    show Devm.getStor cp' sevm.currentTarget = _
    rw [hQ.1]
    simp [wB3, wB2, wB1, wV, getStorVal_afterSload]


/-- **A worked cost**: `approve` of a nonzero amount over a cold, never-written allowance slot costs
`2320` plus the cold surcharge `2100` plus the storage-set charge `20000`. -/
theorem approveGas_cold_set {sevm : Sevm} {pre : Devm}
    (hcold : (⟨sevm.currentTarget, allowSlot sevm.caller (Sevm.dataWord sevm 4).toAdr⟩ :
      Adr × B256) ∉ pre.accessedStorageKeys)
    (horig : getOrigStorVal sevm sevm.currentTarget
      (allowSlot sevm.caller (Sevm.dataWord sevm 4).toAdr) = 0)
    (hcur : pre.getStorVal sevm.currentTarget
      (allowSlot sevm.caller (Sevm.dataWord sevm 4).toAdr) = 0)
    (hw : Sevm.dataWord sevm 36 ≠ 0) : approveGas sevm pre = 24420 := by
  unfold approveGas sstoreCost sstoreValueCost
  simp only [hcold, horig, hcur, ite_false]
  simp [Ne.symm hw]
  decide

end Blanc.Lift.Weth9
