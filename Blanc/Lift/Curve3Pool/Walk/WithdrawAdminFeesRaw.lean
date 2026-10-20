import Blanc.Lift.Curve3Pool.Walk.WithdrawAdminFeesX
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquiditySafe

/-!
# `withdraw_admin_fees`: the raw effect on the actual derivation

`wdx_push` composes the transfer segments of `WithdrawAdminFeesX` (`wdx_xfer_stage`,
`wdx_xfer_payload`, `wdx_xfer_copy`, `wdx_xfer_call`, `wdx_xfer_tail`) from the excess test to
the loop tail; `wdx_iter` adds the `balanceOf` segment (`wdx_iter_static`) in front: one
iteration consumes one static child and, when the answer exceeds the recorded balance, one
`transfer` child. `xa_withdraw` runs the dispatcher, the guards and three iterations to `STOP`;
`withdrawAdminFees_raw` reads the model's step and the raw effect off it, under the per-child
keep premises (`PoolCallsKeep`, children keep the code at `4`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

theorem wdx_lit3 : Bytes.toB256 [3] = 3 := by decide
theorem wdx_lit140 : Bytes.toB256 [1, 0x40] = 0x140 := by decide

/-- **The excess transfer** (`0x4dfc → 0x4f3c`): the excess `feesW` of coin `k` (word `coin`)
goes to the caller with one `transfer` child whose reply passes `RawCallOk`; the pool's
storage, output and code are kept and the frame's logs gained the child's. -/
theorem wdx_push {sevm : Sevm} {post d : Devm} {L : List Exec.Frame} {M : Mem} {img : Bytes}
    {G : Nat} (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (k : Fin 3) (feesW coin : B256) (hdepth : 0 < sevm.depth) (hid : IdReady sevm d)
    (hpc : d.getCode sevm.currentTarget ≠ .empty)
    (hcoinW : (d.getStor sevm.currentTarget).get (coinSlot k) = coin)
    (hcoin : ¬ sevm.benvStat.rules.isPrecomp coin.toAdr) (hK : RlKeep sevm L)
    (hctrR : Region img 0x140 (Nat.toB256 ↑k).toBytes) (hcoinR : Region img 0x160 coin.toBytes)
    (hfeesR : Region img 0x180 feesW.toBytes) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : XAt sevm post 0x4dfc
      (St d [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M G) L) :
    ∃ (p : Exec.Frame) (L' : List Exec.Frame) (d' : Devm) (M' : Mem) (img' : Bytes) (G' : Nat),
      L = p :: L' ∧ p.sevm.currentTarget = coin.toAdr ∧
      p.sevm.data = transferSel ++ sevm.caller.toB256.toBytes ++ feesW.toBytes ∧
      p.sevm.value = 0 ∧ p.sevm.isStatic = sevm.isStatic ∧ RawCallOk p.post.output ∧
      (∀ x, (d'.getStor sevm.currentTarget).get x = (d.getStor sevm.currentTarget).get x) ∧
      d'.logs = d.logs ++ p.post.logs ∧ d'.output = d.output ∧
      d'.getCode sevm.currentTarget = d.getCode sevm.currentTarget ∧ IdReady sevm d' ∧
      Region img' 0x140 (Nat.toB256 ↑k).toBytes ∧ Mem.Reads M' img' ∧ Mem.Wf M' ∧
      XAt sevm post 0x4f3c
        (St d' [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M' G') L' := by
  obtain ⟨d1, M1, img1, G1, hd1, hctr1, hlen1, hcoin1, hfees1, hsel1, hR1, hW1, h⟩ :=
    wdx_xfer_stage hcode k feesW hdepth hid hctrR (by rw [hcoinW]; exact hcoinR) hfeesR hR hW h
  rw [hcoinW] at hcoin1
  obtain ⟨M2, img2, G2, hR2, hW2, hctr2, hcoin2, hdata2, h⟩ :=
    wdx_xfer_payload hcode k coin feesW hctr1 hcoin1 hfees1 hlen1 hsel1 hR1 hW1 h
  obtain ⟨b3, M3, img3, G3, hb3, hR3, hW3, hctr3, hcoin3, hdata3, h⟩ :=
    wdx_xfer_copy hcode k coin feesW (hid.of_rel hd1) hctr2 hcoin2 hdata2 hR2 hW2 h
  obtain ⟨p, L', d2, G4, rfl, hc, ⟨hkp, h4p⟩, hR4, hW4, hrd4, h⟩ :=
    wdx_xfer_call hcode hfork coin feesW hcoin3 hdata3 hR3 hW3 hcoin hK h
  have hrel : BaseRel d b3 := hd1.trans hb3
  have hpc3 : b3.getCode sevm.currentTarget ≠ .empty := by rw [hrel.code]; exact hpc
  have hid3 : IdReady sevm b3 := hid.of_rel hrel
  have hid2 : IdReady sevm d2 :=
    ⟨by rw [hc.codePost, h4p, hc.codePre]; exact hid3.nodeleg, hc.warm _ hid3.warm, hid.pre,
      hid.fork⟩
  rw [wdx_lit3, wdx_lit140] at h
  obtain ⟨hok, b6, M6, img6, G6, hb6, hR6, hW6, hk6, h⟩ :=
    wdx_xfer_tail hcode hid2 hR4 hW4 hrd4 h
  rw [← wdx_lit3, ← wdx_lit140] at h
  refine ⟨p, L', b6, M6, img6, G6, rfl, hc.target, hc.data, hc.value, hc.isStatic,
    hc.output ▸ hok, fun x => ?_, ?_, ?_, ?_, hid2.of_rel hb6,
    Region.of_word (hk6 _ _ (Region.word hctr3) (by omega) (by omega)), hR6, hW6, h⟩
  · rw [hb6.stor, hc.storPost _ hpc3 x, hkp x, hc.storPre _ hpc3, hrel.stor]
  · rw [hb6.logs, hc.logs, hrel.logs]
  · rw [hb6.output, hc.outputKeep, hrel.output]
  · rw [hb6.code, hc.code _ hpc3, hrel.code]

/-- The answer word of a `balanceOf` child. -/
abbrev wdAns (c : Exec.Frame) : B256 := Bytes.toB256 (c.post.output.take 32)

/-- **The transfer children of one iteration**: none when the answer `ansW` equals the recorded
balance `recW`; otherwise one `transfer(msg.sender, ansW - recW)` to the coin `coin`, value `0`,
its reply passing `RawCallOk`. -/
def WdPush (sevm : Sevm) (coin ansW recW : B256) : List Exec.Frame → Prop
  | [] => ansW = recW
  | [p] => ansW ≠ recW ∧ p.sevm.currentTarget = coin.toAdr ∧
      p.sevm.data = transferSel ++ sevm.caller.toB256.toBytes ++ (ansW - recW).toBytes ∧
      p.sevm.value = 0 ∧ p.sevm.isStatic = sevm.isStatic ∧ RawCallOk p.post.output
  | _ :: _ :: _ => False

/-- **One iteration's children** over the storage `σ`: coin `k`'s `balanceOf(self)` child `c`
(static, a word back, no logs), its answer at least the recorded balance, and the transfer
children `Lp`. -/
structure WdKids (sevm : Sevm) (σ : Stor) (k : Fin 3) (c : Exec.Frame) (Lp : List Exec.Frame) :
    Prop where
  target : c.sevm.currentTarget = (σ.get (coinSlot k)).toAdr
  data : c.sevm.data = balanceOfData sevm.currentTarget
  static : c.sevm.isStatic = true
  len : 32 ≤ c.post.output.length
  logs : c.post.logs = []
  le : (σ.get (balanceSlot k)).toNat ≤ (wdAns c).toNat
  push : WdPush sevm (σ.get (coinSlot k)) (wdAns c) (σ.get (balanceSlot k)) Lp

/-- **One `withdraw_admin_fees` iteration** (`0x4d5e → 0x4f3c`): coin `k`'s `balanceOf`, then
the excess transfer when there is one. -/
theorem wdx_iter {sevm : Sevm} {post d : Devm} {L : List Exec.Frame} {M : Mem} {img : Bytes}
    {G : Nat} (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (k : Fin 3) (hid : IdReady sevm d) (hpc : d.getCode sevm.currentTarget ≠ .empty)
    (hkeep : RlKeep sevm L)
    (hctrR : Region img 0x140 (Nat.toB256 ↑k).toBytes) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hcoinK : ¬ sevm.benvStat.rules.isPrecomp
      (((d.getStor sevm.currentTarget).get (coinSlot k)).toAdr))
    (h : XAt sevm post 0x4d5e
      (St d [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M G) L) :
    ∃ (c : Exec.Frame) (Lp L' : List Exec.Frame) (d' : Devm) (M' : Mem) (img' : Bytes) (G' : Nat),
      L = c :: (Lp ++ L') ∧ WdKids sevm (d.getStor sevm.currentTarget) k c Lp ∧
      (∀ x, (d'.getStor sevm.currentTarget).get x = (d.getStor sevm.currentTarget).get x) ∧
      d'.logs = d.logs ++ Lp.flatMap (fun p => p.post.logs) ∧ d'.output = d.output ∧
      d'.getCode sevm.currentTarget = d.getCode sevm.currentTarget ∧ IdReady sevm d' ∧
      Region img' 0x140 (Nat.toB256 ↑k).toBytes ∧ Mem.Reads M' img' ∧ Mem.Wf M' ∧
      XAt sevm post 0x4f3c
        (St d' [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M' G') L' := by
  obtain ⟨c, out, L1, d1, M1, img1, G1, ansW, recW, rfl, htgt, hdata, hstat, hout, hlen, hclogs,
    hans, hrec, hle, hst1, hl1, ho1, hdepth, hid1, hcd1, hctr1, hcoin1, hfees1, hR1, hW1, hbr⟩ :=
    wdx_iter_static hcode hfork k hid hpc hkeep hctrR hR hW hcoinK h
  subst hout
  have hrec' : recW = (d.getStor sevm.currentTarget).get (balanceSlot k) := by rw [hrec, hst1]
  have hans' : ansW = wdAns c := hans
  subst hrec' hans'
  rcases hbr with ⟨heq, h⟩ | ⟨hne, h⟩
  · refine ⟨c, [], L1, d1, M1, img1, G1, rfl, ⟨htgt, hdata, hstat, hlen, hclogs, hle, heq⟩,
      fun x => by rw [hst1], by rw [hl1, List.flatMap_nil, List.append_nil], ho1, hcd1, hid1,
      hctr1, hR1, hW1, h⟩
  · have hpc1 : d1.getCode sevm.currentTarget ≠ .empty := by rw [hcd1]; exact hpc
    obtain ⟨p, L2, d2, M2, img2, G2, rfl, hpt, hpd, hpv, hps, hpok, hs2, hl2, ho2, hc2, hid2,
      hctr2, hR2, hW2, h⟩ :=
      wdx_push hcode hfork k _ ((d.getStor sevm.currentTarget).get (coinSlot k)) hdepth hid1
        hpc1 (by rw [hst1]) hcoinK hkeep.tail hctr1 hcoin1 hfees1 hR1 hW1 h
    refine ⟨c, [p], L2, d2, M2, img2, G2, rfl,
      ⟨htgt, hdata, hstat, hlen, hclogs, hle, hne, hpt, hpd, hpv, hps, hpok⟩,
      fun x => by rw [hs2, hst1], ?_, by rw [ho2, ho1], by rw [hc2, hcd1], hid2, hctr2, hR2,
      hW2, h⟩
    rw [hl2, hl1, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem WdKids.congr {sevm : Sevm} {σ σ' : Stor} {k : Fin 3} {c : Exec.Frame}
    {Lp : List Exec.Frame} (h : WdKids sevm σ k c Lp) (he : ∀ x, σ.get x = σ'.get x) :
    WdKids sevm σ' k c Lp := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨by rw [← he]; exact h1, h2, h3, h4, h5, by rw [← he]; exact h6,
    by rw [← he, ← he]; exact h7⟩

theorem wdx_keep_drop {sevm : Sevm} {c : Exec.Frame} {Lp L : List Exec.Frame}
    (h : RlKeep sevm (c :: (Lp ++ L))) : RlKeep sevm L :=
  fun c' hc' => h c' (List.mem_cons_of_mem _ (List.mem_append_right _ hc'))

/-- **The `withdraw_admin_fees` frame**: from the frame's start, past the dispatcher and the
guards (no value, the caller is the owner), three iterations ran (`WdKids` over the entry
storage for coins `0, 1, 2`) and the frame halted at `STOP` with the pool's storage, output
and code kept and the transfer children's logs appended. -/
theorem xa_withdraw {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selWithdrawAdminFees)
    (hid : IdReady sevm b) (hpc : b.getCode sevm.currentTarget ≠ .empty)
    (hkeep : RlKeep sevm L)
    (hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
      (((b.getStor sevm.currentTarget).get (coinSlot k)).toAdr))
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    sevm.value = 0 ∧ sevm.caller.toB256 = (b.getStor sevm.currentTarget).get ownerSlot ∧
    ∃ (c0 c1 c2 : Exec.Frame) (Lp0 Lp1 Lp2 : List Exec.Frame),
      L = c0 :: (Lp0 ++ c1 :: (Lp1 ++ c2 :: Lp2)) ∧
      WdKids sevm (b.getStor sevm.currentTarget) 0 c0 Lp0 ∧
      WdKids sevm (b.getStor sevm.currentTarget) 1 c1 Lp1 ∧
      WdKids sevm (b.getStor sevm.currentTarget) 2 c2 Lp2 ∧
      (∀ x, (post.getStor sevm.currentTarget).get x = (b.getStor sevm.currentTarget).get x) ∧
      post.logs = b.logs ++ Lp0.flatMap (fun p => p.post.logs) ++
        Lp1.flatMap (fun p => p.post.logs) ++ Lp2.flatMap (fun p => p.post.logs) ∧
      post.output = b.output := by
  obtain ⟨G1, h⟩ := wdx_disp_to_3040 hcode hlen hcd hsel h
  obtain ⟨G2, h⟩ := wdx_disp_to_test hcode hsel h
  obtain ⟨G3, h⟩ := wdx_to_withdraw hcode hsel h
  obtain ⟨G4, h⟩ := wdx_disp_to_body hcode hsel h
  obtain ⟨hval, hown, G5, M5, img5, hW5, hR5, hctr5, h⟩ := wdx_guards hcode hfork h
  refine ⟨hval, hown, ?_⟩
  have hs0 : ∀ x, ((afterSload sevm b ownerSlot).getStor sevm.currentTarget).get x =
      (b.getStor sevm.currentTarget).get x := fun x => by rw [afterSload_getStor]
  have hpc0 : (afterSload sevm b ownerSlot).getCode sevm.currentTarget ≠ .empty := by
    rw [afterSload_getCode]; exact hpc
  -- iteration 0
  obtain ⟨c0, Lp0, L1, d1, M1, img1, G6, rfl, hk0, hs1, hl1, ho1, hc1, hid1, hctr1, hR1, hW1, h⟩ :=
    wdx_iter hcode hfork 0 (hid.afterSload _) hpc0 hkeep hctr5 hR5 hW5
      (by rw [hs0]; exact hcoin 0) h
  have hkeep1 := wdx_keep_drop hkeep
  rcases wdx_tail hcode 0 (by omega) hctr1 hR1 hW1 h with backArm | exitArm
  swap
  · obtain ⟨hdone, _, _⟩ := exitArm
    omega
  obtain ⟨-, G7, M7, img7, hctr7, hR7, hW7, h⟩ := backArm
  have hs1' : ∀ x, (d1.getStor sevm.currentTarget).get x = (b.getStor sevm.currentTarget).get x :=
    fun x => by rw [hs1, hs0]
  have hpc1 : d1.getCode sevm.currentTarget ≠ .empty := by rw [hc1]; exact hpc0
  -- iteration 1
  obtain ⟨c1, Lp1, L2, d2, M2, img2, G8, rfl, hk1, hs2, hl2, ho2, hc2, hid2, hctr2, hR2, hW2, h⟩ :=
    wdx_iter hcode hfork 1 hid1 hpc1 hkeep1 hctr7 hR7 hW7 (by rw [hs1']; exact hcoin 1) h
  have hkeep2 := wdx_keep_drop hkeep1
  rcases wdx_tail hcode 1 (by omega) hctr2 hR2 hW2 h with backArm | exitArm
  swap
  · obtain ⟨hdone, _, _⟩ := exitArm
    omega
  obtain ⟨-, G9, M9, img9, hctr9, hR9, hW9, h⟩ := backArm
  have hs2' : ∀ x, (d2.getStor sevm.currentTarget).get x = (b.getStor sevm.currentTarget).get x :=
    fun x => by rw [hs2, hs1']
  have hpc2 : d2.getCode sevm.currentTarget ≠ .empty := by rw [hc2]; exact hpc1
  -- iteration 2
  obtain ⟨c2, Lp2, L3, d3, M3, img3, G10, rfl, hk2, hs3, hl3, ho3, -, -, hctr3, hR3, hW3, h⟩ :=
    wdx_iter hcode hfork 2 hid2 hpc2 hkeep2 hctr9 hR9 hW9 (by rw [hs2']; exact hcoin 2) h
  rcases wdx_tail hcode 2 (by omega) hctr3 hR3 hW3 h with backArm | exitArm
  · obtain ⟨hback, _⟩ := backArm
    omega
  obtain ⟨-, M4, G11, h⟩ := exitArm
  obtain ⟨hrun, hLfin⟩ := xa_halt (l := .stop) (atL hcode (by kernel_rfl)) h
  simp only [Linst.Run, Linst.run] at hrun
  injection hrun with hpost
  subst hLfin
  refine ⟨c0, c1, c2, Lp0, Lp1, Lp2, by rw [List.append_nil], hk0.congr hs0, hk1.congr hs1',
    hk2.congr hs2', fun x => ?_, ?_, ?_⟩
  · rw [← hpost]
    show (d3.getStor sevm.currentTarget).get x = _
    rw [hs3, hs2']
  · rw [← hpost]
    show d3.logs = _
    rw [hl3, hl2, hl1, afterSload_logs]
  · rw [← hpost]
    show d3.output = _
    rw [ho3, ho2, ho1, afterSload_output]

/-! ## The model -/

/-- **The model's `withdraw_admin_fees`** when the caller is the owner and every coin answered
`w k`, at least its recorded balance, accepting its transfer whenever the excess is positive. -/
theorem withdrawAdminFees_eq {s : State} {e : Env} {w : Fin 3 → Nat}
    (hown : e.caller = s.owner) (hw : ∀ k, (e.coin k).balPre = some (w k))
    (hle : ∀ k, s.balances.get k ≤ w k)
    (hok : ∀ k, s.balances.get k < w k → (e.coin k).pushOk = true) :
    withdrawAdminFees s e = some ⟨s, none, [], pushCalls e.caller
      ⟨w 0 - s.balances.get 0, w 1 - s.balances.get 1, w 2 - s.balances.get 2⟩⟩ := by
  have hc : ∀ k : Fin 3, (chkSub (w k) (s.balances.get k)).bind (fun x =>
      if x > 0 then (if (e.coin k).pushOk = true then some () else none).bind (fun _ => some x)
      else some x) = some (w k - s.balances.get k) := by
    intro k
    rw [chkSub, ite_eq_left (hle k), Option.bind_some]
    by_cases hp : w k - s.balances.get k > 0
    · rw [ite_eq_left hp, ite_eq_left (hok k (by omega)), Option.bind_some]
    · rw [ite_eq_right hp]
  simp only [withdrawAdminFees, req, hown, ite_true, V3.ofFnM, hw,
    Option.bind_eq_bind, Option.bind_some, hc]

/-- `pushCalls` over three amounts, coin by coin. -/
theorem wd_pushCalls (caller a b c : Nat) : pushCalls caller ⟨a, b, c⟩ =
    (if a ≠ 0 then [ExtCall.push 0 caller a] else []) ++
    (if b ≠ 0 then [ExtCall.push 1 caller b] else []) ++
    (if c ≠ 0 then [ExtCall.push 2 caller c] else []) := by
  unfold pushCalls
  by_cases h0 : a ≠ 0 <;> by_cases h1 : b ≠ 0 <;> by_cases h2 : c ≠ 0 <;>
    simp only [List.filterMap_cons, List.filterMap_nil, V3.get, Fin.isValue, Fin.val_zero,
      Fin.val_one, Fin.val_two, Nat.reduceEqDiff, ne_eq, h0, h1, h2, not_false_eq_true,
      ↓reduceIte, List.nil_append, List.cons_append, List.append_nil]

/-- Case analysis over the three coins. -/
theorem wd_fin3 {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ k, P k := by
  intro ⟨k, hk⟩
  match k, hk with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2
  | n + 3, hk => exact absurd hk (by omega)

/-- Coin `k`'s frame among `c0, c1, c2`. -/
def wdPick (c0 c1 c2 : Exec.Frame) (k : Fin 3) : Exec.Frame :=
  if k.val = 0 then c0 else if k.val = 1 then c1 else c2

/-- **The environment a `withdraw_admin_fees` frame observed** over its entry storage `σ`: coin
`k`'s `balanceOf(self)` answer from its child, its transfer accepted exactly when the answer
exceeded the recorded balance. -/
def wdEnv (sevm : Sevm) (σ : Stor) (c0 c1 c2 : Exec.Frame) : Env :=
  { quietEnv sevm with
    coin := fun k => ⟨some (answerWord (wdPick c0 c1 c2 k).post.output), none, false,
      decide (wdAns (wdPick c0 c1 c2 k) ≠ σ.get (balanceSlot k))⟩ }

/-- **One coin's children witness its answers.** -/
theorem wd_coinObs {D : Exec.Deriv} {k : Fin 3} {c : Exec.Frame} {Lp : List Exec.Frame} {n : Nat}
    (hk : WdKids D.sevm (entryStor D) k c Lp) (hn : (children D)[n]? = some c)
    (hLp : ∀ p ∈ Lp, p ∈ children D) :
    CoinObsOf D k ⟨some (answerWord c.post.output), none, false,
      decide (wdAns c ≠ (entryStor D).get (balanceSlot k))⟩ := by
  refine ⟨fun w hw => ?_, fun w hw => (by cases hw), fun h => (by cases h), fun h => ?_⟩
  · cases hw
    exact Or.inr ⟨n, c, hn, hk.target, hk.data, hk.len, rfl⟩
  · have hne : wdAns c ≠ (entryStor D).get (balanceSlot k) := of_decide_eq_true h
    have hp := hk.push
    cases Lp with
    | nil => exact absurd hp hne
    | cons p t =>
      cases t with
      | nil =>
        obtain ⟨-, ht, hd, -, -, hok⟩ := hp
        refine Or.inr ⟨p, hLp p List.mem_cons_self, ht, ?_, hok⟩
        rw [hd, List.append_assoc]
        exact List.take_left' rfl
      | cons _ _ => exact hp.elim

/-- **One coin's state-changing calls** are the model's push of its excess. -/
theorem wd_calls_coin {D : Exec.Deriv} {k : Fin 3} {c : Exec.Frame} {Lp : List Exec.Frame}
    (hk : WdKids D.sevm (entryStor D) k c Lp) (hs : D.sevm.isStatic = false)
    (hcoin : ¬ D.sevm.benvStat.rules.isPrecomp (coinAdr D k)) :
    (c :: Lp).filterMap (fun c => if c.sevm.isStatic then none else
        some (⟨c.sevm.currentTarget, c.sevm.data, c.sevm.value⟩ : CallReq)) =
      ((if (wdAns c).toNat - ((entryStor D).get (balanceSlot k)).toNat ≠ 0 then
          [ExtCall.push k D.sevm.caller.toB256.toNat
            ((wdAns c).toNat - ((entryStor D).get (balanceSlot k)).toNat)] else []).map
        (encodeCall D.sevm.currentTarget (coinAdr D) (tokenAdr D))).filter
        (fun r => framed D r.target) := by
  rw [List.filterMap_cons, hk.static, ite_eq_left rfl]
  have hp := hk.push
  cases Lp with
  | nil =>
    have hz : (wdAns c).toNat - ((entryStor D).get (balanceSlot k)).toNat = 0 := by
      rw [show wdAns c = (entryStor D).get (balanceSlot k) from hp, Nat.sub_self]
    rw [hz, ite_eq_right (fun h => h rfl), List.filterMap_nil, List.map_nil, List.filter_nil]
  | cons p t =>
    cases t with
    | nil =>
      obtain ⟨hne, ht, hd, hv, hps, -⟩ := hp
      have hle' : (entryStor D).get (balanceSlot k) ≤ wdAns c := B256.le_iff_toNat_le_toNat.mpr hk.le
      have hsub := B256.toNat_sub_eq_of_le _ _ hle'
      have hnz : (wdAns c).toNat - ((entryStor D).get (balanceSlot k)).toNat ≠ 0 := by
        intro h0
        exact hne (B256.toNat_inj _ _ (by have := hk.le; omega))
      rw [ite_eq_left hnz, ← hsub]
      have hcoin' : ¬ D.sevm.benvStat.rules.isPrecomp
          ((entryStor D).get (coinSlot k)).toAdr := hcoin
      simp only [List.filterMap_cons, List.filterMap_nil, hps, hs, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.map_nil, encodeCall, List.filter_cons, List.filter_nil, framed,
        coinAdr, decide_eq_false hcoin', Bool.not_false, Bool.true_or, ht, hd, hv, word_toNat]
    | cons _ _ => exact hp.elim

/-! ## Safety -/

/-- **Safety of `withdraw_admin_fees`.** A successful frame of the pool's runtime on the
`withdraw_admin_fees` selector, entered at a `Checkpoint` with empty stack and memory, under the
frame premises (no coin is a precompile; the pool's code is nonempty; the identity precompile is
ready; every direct child keeps the pool's storage, `PoolCallsKeep`, and the code at `4`),
computed the model's step on the decoded call in the environment `wdEnv` it observed, with the
raw effect Spec states. -/
theorem withdrawAdminFees_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selWithdrawAdminFees)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
    (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre)
    (hkeep : PoolCallsKeep ⟨0, sevm, pre, .ok post, exc⟩)
    (hidk : ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨hval, hown, c0, c1, c2, Lp0, Lp1, Lp2, hL, hk0, hk1, hk2, hstorF, hlogsF, houtF⟩ :=
    xa_withdraw hcode hfork hlen hcd hsel hid hpc (RlKeep.of_pool hkeep hidk) hcoin hx
  have hdec : decodeCall sevm = .withdrawAdminFees := decodeCall_at (k := 20) rfl hsel hlen
  have hchildren : children ⟨0, sevm, pre, .ok post, exc⟩ =
      c0 :: (Lp0 ++ c1 :: (Lp1 ++ c2 :: Lp2)) := hL
  have hbal : ∀ k, s.balances.get k = ((pre.getStor sevm.currentTarget).get (balanceSlot k)).toNat :=
    fun k => (hck.abs.balances k).symm
  have hle : ∀ k, s.balances.get k ≤
      (wdAns (wdPick c0 c1 c2 k)).toNat := by
    refine wd_fin3 ?_ ?_ ?_
    · rw [hbal]; exact hk0.le
    · rw [hbal]; exact hk1.le
    · rw [hbal]; exact hk2.le
  have hok : ∀ k, s.balances.get k < (wdAns (wdPick c0 c1 c2 k)).toNat →
      ((wdEnv sevm (pre.getStor sevm.currentTarget) c0 c1 c2).coin k).pushOk = true := by
    intro k hlt
    refine decide_eq_true (fun he => ?_)
    rw [hbal, he] at hlt
    exact Nat.lt_irrefl _ hlt
  have hown' : (wdEnv sevm (pre.getStor sevm.currentTarget) c0 c1 c2).caller = s.owner := by
    show sevm.caller.toB256.toNat = s.owner
    rw [hown]
    exact hck.abs.owner
  have hv' : (wdEnv sevm (pre.getStor sevm.currentTarget) c0 c1 c2).value = 0 := by
    show sevm.value.toNat = 0
    rw [hval]; rfl
  have hstep := withdrawAdminFees_eq hown' (fun k => rfl) hle hok
  rw [hbal 0, hbal 1, hbal 2] at hstep
  refine ⟨wdEnv sevm (pre.getStor sevm.currentTarget) c0 c1 c2, ⟨s, none, [],
    pushCalls sevm.caller.toB256.toNat
      ⟨(wdAns c0).toNat - ((pre.getStor sevm.currentTarget).get (balanceSlot 0)).toNat,
        (wdAns c1).toNat - ((pre.getStor sevm.currentTarget).get (balanceSlot 1)).toNat,
        (wdAns c2).toNat - ((pre.getStor sevm.currentTarget).get (balanceSlot 2)).toNat⟩⟩,
    ?step, ?raw⟩
  case step =>
    rw [hdec]
    show (if _ = 0 then _ else none) = _
    rw [ite_eq_left hv']
    exact hstep
  case raw =>
    have hmem0 : ∀ p ∈ Lp0, p ∈ children ⟨0, sevm, pre, .ok post, exc⟩ := fun p hp => by
      rw [hchildren]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hp)
    have hmem1 : ∀ p ∈ Lp1, p ∈ children ⟨0, sevm, pre, .ok post, exc⟩ := fun p hp => by
      rw [hchildren]
      exact List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_append_left _ hp)))
    have hmem2 : ∀ p ∈ Lp2, p ∈ children ⟨0, sevm, pre, .ok post, exc⟩ := fun p hp => by
      rw [hchildren]
      exact List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ hp))))
    have hn1 : (children ⟨0, sevm, pre, .ok post, exc⟩)[Lp0.length + 1]? = some c1 := by
      rw [hchildren, List.getElem?_cons_succ, List.getElem?_append_right (Nat.le_refl _),
        Nat.sub_self, List.getElem?_cons_zero]
    have hn2 : (children ⟨0, sevm, pre, .ok post, exc⟩)[Lp0.length + 1 + Lp1.length + 1]? =
        some c2 := by
      rw [hchildren, List.getElem?_cons_succ, List.getElem?_append_right (by omega),
        show Lp0.length + 1 + Lp1.length - Lp0.length = Lp1.length + 1 by omega,
        List.getElem?_cons_succ, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero]
    refine ⟨?env, ?stor, ?logs, ?output, ?calls⟩
    case env =>
      refine ⟨rfl, rfl, rfl, wd_fin3 ?_ ?_ ?_, fun T h => (by cases h), fun h => (by cases h),
        fun h => (by cases h)⟩
      · exact wd_coinObs hk0 (n := 0) (by rw [hchildren]; rfl) hmem0
      · exact wd_coinObs hk1 hn1 hmem1
      · exact wd_coinObs hk2 hn2 hmem2
    case stor =>
      show StorEffect (decodeCall sevm) (pre.getStor sevm.currentTarget)
        (post.getStor sevm.currentTarget) s
      rw [hdec]
      exact ⟨fun x _ => hstorF x, fun f hf => nomatch hf⟩
    case logs =>
      rw [hlogsF, hchildren]
      simp only [List.flatMap_cons, List.flatMap_append, hk0.logs, hk1.logs, hk2.logs,
        List.nil_append, List.map_nil, List.append_nil, List.append_assoc]
    case output =>
      rw [houtF]
      rfl
    case calls =>
      intro hs
      replace hs : sevm.isStatic = false := hs
      have hsplit : c0 :: (Lp0 ++ c1 :: (Lp1 ++ c2 :: Lp2)) =
          (c0 :: Lp0) ++ (c1 :: Lp1) ++ (c2 :: Lp2) := by
        simp only [List.cons_append, List.append_assoc]
      rw [CallsOf, modelCalls, hchildren, hsplit, wd_pushCalls, List.filterMap_append,
        List.filterMap_append, List.map_append, List.map_append, List.filter_append,
        List.filter_append, wd_calls_coin (D := ⟨0, sevm, pre, .ok post, exc⟩) hk0 hs (hcoin 0),
        wd_calls_coin (D := ⟨0, sevm, pre, .ok post, exc⟩) hk1 hs (hcoin 1),
        wd_calls_coin (D := ⟨0, sevm, pre, .ok post, exc⟩) hk2 hs (hcoin 2)]
      rfl

end Blanc.Lift.Curve3Pool
