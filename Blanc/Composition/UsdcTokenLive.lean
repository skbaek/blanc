import Blanc.Composition.UniswapV2PairUsdcWeth9LegsFacts
import Blanc.Lift.Token.TransferLiveBudget

/-!
# USDC's budget-aware transfer liveness (U9a)

`usdcTransferLive P U : TransferLiveBudget P (usdcBookS P).toBook`, from the gas-exact proxy frame
of `transfer` (`proxy_xfer_run`): the proxy's prefix, its `DELEGATECALL` into the implementation's
`transfer` frame under the 63/64 rule, and the delegate tail.  `cost` is the frame's exact charge
`proxyXferCost`; `budget` adds what the child needs past the 63/64 cut.  The post world is the
child's: its storage at the proxy is `transfer`'s debit and credit (`frame_transfer`), which keeps
the footprint facts (`FootCore`), and no code changes.
-/

namespace Blanc.Composition.UsdcToken

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc Blanc.Lift.Token Blanc.SlotFootprint
  Blanc.Composition.UsdcLive

/-- **The footprint facts a USDC `transfer` frame uses**: the tracked keys' slots injective and
apart from the fixed slots, and the ledger good.  `FootInv` without its support half; the history
delivers it at the end (`usdc_history_end_core`), and a transfer keeps it. -/
structure FootCore (U : Key → Prop) (s : Stor) : Prop where
  inj : SlotFootprint.Inj Key.slot U
  apart : SlotFootprint.Apart Key.slot fixedSlots U
  good : (ledger U s).Good

/-- A write at a tracked key's slot keeps `FootCore`. -/
theorem FootCore.set_key {U : Key → Prop} {s : Stor} (h : FootCore U s) {k : Key} (hk : U k)
    (w : B256) : FootCore U (s.set k.slot w) := by
  have off : ∀ x ∈ fixedSlots, (s.set k.slot w).get x = s.get x := fun x hx =>
    Stor.get_set_ne _ (fun e => h.apart k hk (by rw [e]; exact hx)) w
  exact ⟨h.inj, h.apart, ledger_good_congr h.good (off 8 (by decide)) (off 18 (by decide))⟩

/-- The state conditions a USDC `transfer` from `src` to `dst` of `v` needs at a world. -/
def UsdcTransferOk (l : Usdc.Ledger) (src dst : Adr) (v : Nat) : Prop :=
  l.paused = false ∧ l.frozen src = false ∧ l.frozen dst = false ∧ src ≠ 0 ∧ dst ≠ 0 ∧
    l.bal dst + v < 2 ^ 255

/-- The gas a USDC `transfer` frame needs: its exact charge, plus what keeps the child's need after
the proxy's 63/64 cut. -/
noncomputable def usdcXferBudget (sevm : Sevm) (pre : Devm) : Nat :=
  proxyXferCost sevm pre + (childXferCost sevm pre + 415) / 63 + 416

theorem dI_eq {sevm : Sevm} {pre : Devm}
    (slot : (Devm.getStor pre sevm.currentTarget).get implSlot = usdcImpl.toB256) :
    dI sevm pre = usdcImpl := by
  show ((afterSload sevm pre pKA).getStorVal sevm.currentTarget pKI).toAdr = usdcImpl
  rw [gsv, Blanc.afterSload_getStor, pKI_eq, slot, Jaune.toAdr_toB256]

theorem pBase_state (sevm : Sevm) (pre : Devm) : (pBase sevm pre).state = pre.state := by
  unfold pBase
  rw [Blanc.Lift.NodeWalk.afterSload_state, Blanc.Lift.NodeWalk.afterSload_state]

/-- **The USDC `transfer` frame, end to end.** -/
theorem usdc_transfer_live {P : Adr} {U : Key → Prop} {sevm : Sevm} {pre : Devm} {G : Nat}
    {dst : Adr} {v : Nat} (htarget : sevm.currentTarget = P)
    (hcode : sevm.code = pre.state.getCode P) (hkeys : ∀ k ∈ frameKeys sevm, U k)
    (hlen : sevm.data.length < 2 ^ 256) (hadm : sevm.caller ≠ adminOf pre.state P)
    (hok : ∀ dst v, usdcOp sevm = .transfer dst v →
      UsdcTransferOk (ledger U (pre.state.getStor P)) sevm.caller dst v)
    (fork : CoveredFork sevm.benvStat.fork) (hvalue : sevm.value = 0)
    (hstatic : sevm.isStatic = false) (inst : UsdcInstalled P pre.state)
    (finv : FootCore U (pre.state.getStor P)) (hop : usdcOp sevm = .transfer dst v)
    (hbal : v ≤ (ledger U (pre.state.getStor P)).bal sevm.caller)
    (hbud : usdcXferBudget sevm pre ≤ G) (hG : G < 2 ^ 256) (depth : sevm.depth ≠ 0) :
    ∃ post, Nonempty (Exec 0 sevm (St pre [] Mem.empty G) (.ok post)) ∧
      post.gasLeft + proxyXferCost sevm pre = G ∧ post.output = (Nat.toB256 1).toBytes ∧
      (UsdcInstalled P post.state ∧ FootCore U (post.state.getStor P)) ∧
      (dst ≠ sevm.caller → (ledger U (post.state.getStor P)).bal sevm.caller + v =
        (ledger U (pre.state.getStor P)).bal sevm.caller) ∧
      post = proxyXferPost sevm pre (G - proxyXferCost sevm pre) := by
  have ok := hok dst v hop
  obtain ⟨len, sel, rfl, rfl⟩ := usdcOp_transfer_words hop
  subst htarget
  obtain ⟨p0, fc, fd, c0, d0, hb⟩ := ok
  have dec := decodeCall_transfer sel len hvalue
  have kc : U (.bal sevm.caller) :=
    hkeys _ (keys_sub_frameKeys dec _ (by simp only [Call.keys, List.mem_cons, true_or]))
  have kd : U (.bal (Sevm.dataWord sevm 4).toAdr) := hkeys _ (keys_sub_frameKeys dec _
    (by simp only [Call.keys, List.mem_cons, List.not_mem_nil, or_false, or_true]))
  rw [ledger_frozen kc] at fc
  rw [ledger_frozen kd] at fd
  rw [ledger_bal kd] at hb
  rw [ledger_bal kc] at hbal
  have hne : (Sevm.dataWord sevm 4).toAdr ≠ sevm.caller →
      balSlot (Sevm.dataWord sevm 4).toAdr ≠ balSlot sevm.caller := fun h e =>
    h (Key.bal.inj (finv.inj _ _ kd kc e))
  have pf := proxyFacts_of (sevm := sevm) (pre := pre) (by omega) hlen sel hadm
  have xf := xferFacts_of (sevm := sevm) (pre := pre) hvalue len hlen sel p0 fc fd c0 d0 hbal hb hne
  have hdI := dI_eq (sevm := sevm) (pre := pre) inst.slot
  have hcodeI : (pBase sevm pre).state.getCode (dI sevm pre) = Impl.code := by
    rw [pBase_state, hdI]; exact Blanc.ExecutionTrace.bytes_eq_of_image inst.impl
  have hprec : sevm.benvStat.rules.isPrecomp (dI sevm pre) = false := by
    rw [hdI]
    exact propext ⟨fun h => (impl_not_precompile fork h).elim, fun h => (Bool.false_ne_true h).elim⟩
  have hfwd : childXferCost sevm pre + 415 ≤
      dFwd sevm pre (frameY sevm pre (G - proxyXferCost sevm pre)) := by
    unfold usdcXferBudget at hbud
    unfold dFwd frameY except64th
    omega
  have hY : frameY sevm pre (G - proxyXferCost sevm pre) < 2 ^ 256 := by
    unfold usdcXferBudget at hbud
    unfold frameY
    unfold proxyXferCost at hbud ⊢
    omega
  have run := proxy_xfer_run fork hstatic depth hlen pf xf hcodeI hprec hfwd hY
  generalize hpost : proxyXferPost sevm pre (G - proxyXferCost sevm pre) = post at run
  have hgas : post.gasLeft = G - proxyXferCost sevm pre := by rw [← hpost, proxyPost_gasLeft]
  have hout : post.output = (Nat.toB256 1).toBytes := by rw [← hpost, proxyPost_output]; rfl
  have hstate : post.state = (frameChild sevm pre (G - proxyXferCost sevm pre)).state := by
    rw [← hpost, proxyPost_state]
  have hstor := frameChild_stor (X := G - proxyXferCost sevm pre) fork hstatic hlen sel xf hcodeI hfwd
  have hcodeP : sevm.code = Proxy.code := hcode.trans (code_of_at (d := pre) inst.proxy)
  have hle : proxyXferCost sevm pre ≤ G := by unfold usdcXferBudget at hbud; omega
  rw [Nat.sub_add_cancel hle] at run
  obtain ⟨exec⟩ := lift_exact Proxy.cert_check Proxy.jumps_ok hcodeP fork ⟨_, rfl, run⟩
  have keep : Devm.CodePreserve (St pre [] Mem.empty G) post :=
    Exec.effect codePreserve_refl_trans.1 codePreserve_refl_trans.2 Ninst.codePreserve_effectRec
      Jinst.codePreserve_effect Linst.codePreserve_effect exec
  have hps : post.state.getStor sevm.currentTarget = creditStor (debitStor
      (pre.state.getStor sevm.currentTarget) sevm.caller (Sevm.dataWord sevm 36).toNat)
      (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toNat := by
    rw [hstate]; exact hstor
  have hP : pre.state.getCode sevm.currentTarget = Proxy.code := code_of_at (d := pre) inst.proxy
  have hI : pre.state.getCode usdcImpl = Impl.code := Blanc.ExecutionTrace.bytes_eq_of_image inst.impl
  have hL : pre.state.getCode usdcLib = Lib.code := Blanc.ExecutionTrace.bytes_eq_of_image inst.lib
  have kP : post.state.getCode sevm.currentTarget = pre.state.getCode sevm.currentTarget :=
    keep _ (by change (pre.state.getCode _).toList ≠ []; rw [hP]; exact proxy_nonempty)
  have kI : post.state.getCode usdcImpl = pre.state.getCode usdcImpl :=
    keep _ (by change (pre.state.getCode _).toList ≠ []; rw [hI]; exact implSem.ne_nil rfl)
  have kL : post.state.getCode usdcLib = pre.state.getCode usdcLib :=
    keep _ (by change (pre.state.getCode _).toList ≠ []; rw [hL]; exact lib_toList_ne_nil)
  refine ⟨post, ⟨exec⟩, by omega, hout, ⟨⟨?_, ?_, ?_, ?_, inst.implApart, inst.libApart⟩, ?_⟩, ?_, rfl⟩
  · rw [kP]; exact inst.proxy
  · rw [kI]; exact inst.impl
  · rw [kL]; exact inst.lib
  · rw [hps]
    unfold creditStor debitStor
    rw [get_set_off (y := balSlot _) (x := implSlot) (finv.apart _ kd) (by decide),
      get_set_off (y := balSlot _) (x := implSlot) (finv.apart _ kc) (by decide)]
    exact inst.slot
  · rw [hps]
    unfold creditStor debitStor
    exact (finv.set_key kc _).set_key kd _
  · intro hne'
    have lt : balanceBits ((pre.state.getStor sevm.currentTarget).get (balSlot sevm.caller)) -
        (Sevm.dataWord sevm 36).toNat < 2 ^ 255 := by
      have := Nat.mod_lt ((pre.state.getStor sevm.currentTarget).get (balSlot sevm.caller)).toNat
        (Nat.two_pow_pos 255)
      unfold balanceBits at hbal ⊢; omega
    rw [hps, ledger_bal kc, ledger_bal kc]
    unfold creditStor debitStor
    rw [Stor.get_set_ne _ (hne hne'), Stor.get_set_self, balanceBits_toB256 lt]
    omega

/-- **USDC's budget-aware transfer liveness** (U9a, from the proxy→implementation exact walk of
`transfer`).  `cost` is the frame's exact charge, `budget` adds the child's need past the 63/64 cut. -/
noncomputable def usdcTransferLive (P : Adr) (U : Key → Prop) :
    TransferLiveBudget P (usdcBookS P).toBook where
  WorldOk w := UsdcInstalled P w ∧ FootCore U (w.getStor P)
  FrameOk sevm w := (∀ k ∈ frameKeys sevm, U k) ∧ sevm.data.length < 2 ^ 256 ∧
    sevm.caller ≠ adminOf w P ∧
    ∀ dst v, usdcOp sevm = .transfer dst v → UsdcTransferOk (ledger U (w.getStor P)) sevm.caller dst v
  ledgerAt w := ledger U (w.getStor P)
  cost := proxyXferCost
  budget := usdcXferBudget
  cost_le sevm pre := by unfold usdcXferBudget; omega
  live := by
    intro sevm pre G dst v htarget _ hcode ⟨hkeys, hlen, hadm, hok⟩ fork hvalue hstatic _
      ⟨inst, finv⟩ hop hbal hbud hG depth
    obtain ⟨post, run, hgas, hout, world, hbal', -⟩ := usdc_transfer_live htarget hcode hkeys hlen hadm
      hok fork hvalue hstatic inst finv hop hbal hbud hG depth
    exact ⟨post, run, hgas, hout, world, hbal'⟩

end Blanc.Composition.UsdcToken
