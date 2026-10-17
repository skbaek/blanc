import Blanc.Lift.Curve3Pool.Walk.Dispatch
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidityPre
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidityPost

/-!
# `remove_liquidity`: the whole frame on the actual derivation

`xa_removeLiquidity` composes the dispatcher (`Dispatch.lean`), the guarded prologue with the
`totalSupply` read (`RemoveLiquidityPre.lean`), three loop iterations
(`RemoveLiquidityLoop.lean`) and the burn, event and lock clear (`RemoveLiquidityPost.lean`):
from the frame's entry with the `remove_liquidity` selector, a successful frame has exactly five
direct children (`totalSupply`, the three `transfer`s, `burnFrom`), the machine-word checks the
model makes, and the pool's storage, logs and output as the model's step leaves them.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-! ## Slot separation -/

theorem three_cases {i : Nat} (hi : i < 3) : i = 0 ∨ i = 1 ∨ i = 2 := by omega

theorem bal_ne_lock {i : Nat} (hi : i < 3) : lockSlot ≠ balancesBase + Nat.toB256 i := by
  rcases three_cases hi with rfl | rfl | rfl <;> decide

theorem coin_ne_lock {i : Nat} (hi : i < 3) : lockSlot ≠ coinsBase + Nat.toB256 i := by
  rcases three_cases hi with rfl | rfl | rfl <;> decide

theorem bal_ne_token {i : Nat} (hi : i < 3) : balancesBase + Nat.toB256 i ≠ tokenSlot := by
  rcases three_cases hi with rfl | rfl | rfl <;> decide

theorem bal_ne_coin {i j : Nat} (hi : i < 3) (hj : j < 3) :
    balancesBase + Nat.toB256 i ≠ coinsBase + Nat.toB256 j := by
  rcases three_cases hi with rfl | rfl | rfl <;> rcases three_cases hj with rfl | rfl | rfl <;>
    decide

theorem bal_ne_bal {i j : Nat} (hi : i < 3) (hj : j < 3) (hij : i ≠ j) :
    balancesBase + Nat.toB256 i ≠ balancesBase + Nat.toB256 j := by
  rcases three_cases hi with rfl | rfl | rfl <;> rcases three_cases hj with rfl | rfl | rfl <;>
    first | exact absurd rfl hij | decide

/-! ## One transfer, as the frame saw it -/

/-- Iteration `i` with `balances[i] = B`, `coins[i] = C` and supply word `T`: the checks the
loop made and its `transfer` child `c`. -/
structure RLPush (sevm : Sevm) (B C T : B256) (i : Nat) (c : Exec.Frame) : Prop where
  mul : B * rlAmt sevm / B = rlAmt sevm ∨ B = 0
  supply : T ≠ 0
  min : ¬ B * rlAmt sevm / T < rlMin sevm i
  le : ¬ B < B * rlAmt sevm / T
  target : c.sevm.currentTarget = C.toAdr
  data : c.sevm.data = transferSel ++ sevm.caller.toB256.toBytes ++ (B * rlAmt sevm / T).toBytes
  value : c.sevm.value = 0
  static : c.sevm.isStatic = sevm.isStatic
  ok : RawCallOk c.post.output

/-- **One iteration**, over the balance and coin words it reads. -/
theorem xa_rl_step {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {i : Nat} {B C T : B256} {a : Nat → B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hi : i < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hL : LoopImg img i T a)
    (hB : (b.getStor sevm.currentTarget).get (balancesBase + Nat.toB256 i) = B)
    (hC : (b.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i) = C)
    (hpc : b.getCode sevm.currentTarget ≠ .empty)
    (hid : IdReady sevm b) (hdepth : 0 < sevm.depth)
    (hcoin : ¬ sevm.benvStat.rules.isPrecomp C.toAdr)
    (hK : CallKeeps sevm C)
    (h : XAt sevm post 0x2cdb (St b [3, 0x2a0] M G) L) :
    ∃ c L' b' M' img' G', L = c :: L' ∧ RLPush sevm B C T i c ∧
      (∀ x, (b'.getStor sevm.currentTarget).get x =
        ((b.getStor sevm.currentTarget).set (balancesBase + Nat.toB256 i)
          (B - B * rlAmt sevm / T)).get x) ∧
      b'.logs = b.logs ++ c.post.logs ∧ b'.output = b.output ∧
      b'.getCode sevm.currentTarget = b.getCode sevm.currentTarget ∧ IdReady sevm b' ∧
      Mem.Reads M' img' ∧ Mem.Wf M' ∧
      LoopImg img' (i + 1) T (Function.update a i (B * rlAmt sevm / T)) ∧
      XAt sevm post (if i + 1 = 3 then 0x2f7b else 0x2cdb) (St b' [3, 0x2a0] M' G') L' := by
  subst hB hC
  obtain ⟨hmul, hT0, hmin, hle, c, L', b', M', img', G', rfl, htgt, hdata, hval, hst, hok, hs, hl,
    ho, hcd, hidb, hR', hW', hL', h'⟩ :=
    xa_rl_iter (σ := b.getStor sevm.currentTarget) hcode hfork hi hR hW hL (fun _ => rfl) hpc hid
      hdepth hcoin hK h
  exact ⟨c, L', b', M', img', G', rfl, ⟨hmul, hT0, hmin, hle, htgt, hdata, hval, hst, hok⟩, hs, hl,
    ho, hcd, hidb, hR', hW', hL', h'⟩


/-! ## The frame -/

/-- The supply word the `totalSupply` child returned. -/
abbrev rlSupply (c : Exec.Frame) : B256 := Bytes.toB256 (c.post.output.take 32)

/-- The withdrawn amount of coin `i` from the entry storage `σ` and the supply word `T`. -/
abbrev rlOut (sevm : Sevm) (σ : Stor) (T : B256) (i : Nat) : B256 := balAt σ i * rlAmt sevm / T

/-- The `RemoveLiquidity` topic word. -/
abbrev rlTopic : B256 := Bytes.toB256 [0xa4, 0x9d, 0x4c, 0xf0, 0x26, 0x56, 0xae, 0xbf, 0x8c, 0x77,
  0x1f, 0x5a, 0x85, 0x85, 0x63, 0x8a, 0x2a, 0x15, 0xee, 0x6c, 0x97, 0xcf, 0x72, 0x05, 0xd4, 0x20,
  0x8e, 0xd7, 0xc1, 0xdf, 0x25, 0x2d]

/-- **The `remove_liquidity` frame.** From the frame's entry with the `remove_liquidity`
selector, a successful frame found the lock clear and no value, and its direct children are
exactly `totalSupply` (static, a word returned), the three `transfer`s of iteration `0, 1, 2`
(`RLPush`) and `burnFrom(msg.sender, _amount)` (a word returned); `total_supply ≥ _amount`; the
pool's storage is the entry storage with the three balances lowered; the frame logged its
children's logs and then `RemoveLiquidity`; the output is the entry output. -/
theorem xa_removeLiquidity {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidity)
    (htok : ¬ sevm.benvStat.rules.isPrecomp ((b.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (hcoin : ∀ i, i < 3 →
      ¬ sevm.benvStat.rules.isPrecomp (coinAt (b.getStor sevm.currentTarget) i).toAdr)
    (hpc : b.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm b)
    (hck : ∀ i, i < 3 → CallKeeps sevm (coinAt (b.getStor sevm.currentTarget) i))
    (hsk : StaticKeeps sevm ((b.getStor sevm.currentTarget).get tokenSlot))
    (htk : CallKeeps sevm ((b.getStor sevm.currentTarget).get tokenSlot))
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    (b.getStor sevm.currentTarget).get lockSlot = 0 ∧ sevm.value = 0 ∧
    ∃ c0 c1 c2 c3 c4, L = [c0, c1, c2, c3, c4] ∧
      c0.sevm.currentTarget = ((b.getStor sevm.currentTarget).get tokenSlot).toAdr ∧
      c0.sevm.data = totalSupplyData ∧ c0.sevm.isStatic = true ∧
      32 ≤ c0.post.output.length ∧ c0.post.logs = [] ∧
      RLPush sevm (balAt (b.getStor sevm.currentTarget) 0) (coinAt (b.getStor sevm.currentTarget) 0)
        (rlSupply c0) 0 c1 ∧
      RLPush sevm (balAt (b.getStor sevm.currentTarget) 1) (coinAt (b.getStor sevm.currentTarget) 1)
        (rlSupply c0) 1 c2 ∧
      RLPush sevm (balAt (b.getStor sevm.currentTarget) 2) (coinAt (b.getStor sevm.currentTarget) 2)
        (rlSupply c0) 2 c3 ∧
      ¬ rlSupply c0 < rlAmt sevm ∧
      c4.sevm.currentTarget = ((b.getStor sevm.currentTarget).get tokenSlot).toAdr ∧
      c4.sevm.data = burnFromSel ++ sevm.caller.toB256.toBytes ++ (rlAmt sevm).toBytes ∧
      c4.sevm.value = 0 ∧ c4.sevm.isStatic = sevm.isStatic ∧ 32 ≤ c4.post.output.length ∧
      (∀ x, (post.getStor sevm.currentTarget).get x =
        ((((b.getStor sevm.currentTarget).set (balancesBase + Nat.toB256 0)
          (balAt (b.getStor sevm.currentTarget) 0 -
            rlOut sevm (b.getStor sevm.currentTarget) (rlSupply c0) 0)).set
          (balancesBase + Nat.toB256 1) (balAt (b.getStor sevm.currentTarget) 1 -
            rlOut sevm (b.getStor sevm.currentTarget) (rlSupply c0) 1)).set
          (balancesBase + Nat.toB256 2) (balAt (b.getStor sevm.currentTarget) 2 -
            rlOut sevm (b.getStor sevm.currentTarget) (rlSupply c0) 2)).get x) ∧
      post.logs = b.logs ++ (c1.post.logs ++ c2.post.logs ++ c3.post.logs ++ c4.post.logs) ++
        [⟨sevm.currentTarget, [rlTopic, sevm.caller.toB256],
          (rlOut sevm (b.getStor sevm.currentTarget) (rlSupply c0) 0).toBytes ++
          (rlOut sevm (b.getStor sevm.currentTarget) (rlSupply c0) 1).toBytes ++
          (rlOut sevm (b.getStor sevm.currentTarget) (rlSupply c0) 2).toBytes ++
          (0 : B256).toBytes ++ (0 : B256).toBytes ++ (0 : B256).toBytes ++
          (rlSupply c0 - rlAmt sevm).toBytes⟩] ∧
      post.output = b.output := by
  obtain ⟨G1, h⟩ := xa_dispatch_removeLiquidity hcode hlen hcd hsel h
  obtain ⟨hlock, hval, c0, L0, b1, M1, G1, img1, rfl, hdepth, h0t, h0d, h0s, h0l, h0g, -,
    -, hs1, -, hl1, ho1, hacc1, h41, hcd1, hR, hW, hT, hz, hctr, h⟩ :=
    xa_rl_pre hcode hfork hcd (vyMem_reads Mem.wf_empty Mem.reads_empty _)
      (vyMem_wf Mem.wf_empty _) htok hsk h
  refine ⟨hlock, hval, ?_⟩
  have hL0 : LoopImg img1 0 (rlSupply c0) (fun _ => 0) := ⟨hctr, hT, hz⟩
  have hpc1 : b1.getCode sevm.currentTarget ≠ .empty := by rw [hcd1 _ hpc]; exact hpc
  have hid1 : IdReady sevm b1 :=
    ⟨by rw [h41]; exact hid.nodeleg,
      hacc1 _ hid.warm, hid.pre, hid.fork⟩
  clear hT hz hctr
  -- iteration 0
  obtain ⟨c1, L1, b2, M2, img2, G2, rfl, hp1, hs2, hl2, ho2, hcd2, hid2, hR, hW, hL1, h⟩ :=
    xa_rl_step (B := balAt (b.getStor sevm.currentTarget) 0)
      (C := coinAt (b.getStor sevm.currentTarget) 0) hcode hfork (by decide) hR hW hL0
      (by rw [hs1, Stor.get_set_ne _ (bal_ne_lock (by decide))])
      (by rw [hs1, Stor.get_set_ne _ (coin_ne_lock (by decide))])
      hpc1 hid1 hdepth (hcoin 0 (by decide)) (hck 0 (by decide)) h
  rw [show (if 0 + 1 = 3 then (0x2f7b : Nat) else 0x2cdb) = 0x2cdb from rfl] at h
  -- iteration 1
  obtain ⟨c2, L2, b3, M3, img3, G3, rfl, hp2, hs3, hl3, ho3, hcd3, hid3, hR, hW, hL2, h⟩ :=
    xa_rl_step (B := balAt (b.getStor sevm.currentTarget) 1)
      (C := coinAt (b.getStor sevm.currentTarget) 1) hcode hfork (by decide) hR hW hL1
      (by rw [hs2, Stor.get_set_ne _ (bal_ne_bal (i := 0) (j := 1) (by decide) (by decide)
            (by decide)), hs1, Stor.get_set_ne _ (bal_ne_lock (by decide))])
      (by rw [hs2, Stor.get_set_ne _ (bal_ne_coin (i := 0) (j := 1) (by decide) (by decide)), hs1,
            Stor.get_set_ne _ (coin_ne_lock (by decide))])
      (by rw [hcd2]; exact hpc1) hid2 hdepth (hcoin 1 (by decide))
      (hck 1 (by decide)) h
  rw [show (if 1 + 1 = 3 then (0x2f7b : Nat) else 0x2cdb) = 0x2cdb from rfl] at h
  -- iteration 2
  obtain ⟨c3, L3, b4, M4, img4, G4, rfl, hp3, hs4, hl4, ho4, hcd4, hid4, hR, hW, hL3, h⟩ :=
    xa_rl_step (B := balAt (b.getStor sevm.currentTarget) 2)
      (C := coinAt (b.getStor sevm.currentTarget) 2) hcode hfork (by decide) hR hW hL2
      (by rw [hs3, Stor.get_set_ne _ (bal_ne_bal (i := 1) (j := 2) (by decide) (by decide)
            (by decide)), hs2, Stor.get_set_ne _ (bal_ne_bal (i := 0) (j := 2) (by decide)
            (by decide) (by decide)), hs1, Stor.get_set_ne _ (bal_ne_lock (by decide))])
      (by rw [hs3, Stor.get_set_ne _ (bal_ne_coin (i := 1) (j := 2) (by decide) (by decide)), hs2,
            Stor.get_set_ne _ (bal_ne_coin (i := 0) (j := 2) (by decide) (by decide)), hs1,
            Stor.get_set_ne _ (coin_ne_lock (by decide))])
      (by rw [hcd3, hcd2]; exact hpc1) hid3 hdepth (hcoin 2 (by decide))
      (hck 2 (by decide)) h
  rw [show (if 2 + 1 = 3 then (0x2f7b : Nat) else 0x2cdb) = 0x2f7b from rfl] at h
  -- after the loop
  have htw : (b4.getStor sevm.currentTarget).get tokenSlot =
      (b.getStor sevm.currentTarget).get tokenSlot := by
    rw [hs4, Stor.get_set_ne _ (bal_ne_token (by decide)), hs3,
      Stor.get_set_ne _ (bal_ne_token (by decide)), hs2, Stor.get_set_ne _ (bal_ne_token (by decide)),
      hs1, Stor.get_set_ne _ lock_ne_token]
  obtain ⟨hTa, c4, d, rfl, hc4, hlen4, hdk, hsP, hlP, hoP⟩ :=
    xa_rl_post hcode hfork hR hW hL3.supply hL3.amt htw htok (htw ▸ htk) h
  have hd4 : ∀ y, (d.getStor sevm.currentTarget).get y = (b4.getStor sevm.currentTarget).get y :=
    fun y => by rw [hdk]
  refine ⟨c0, c1, c2, c3, c4, rfl, h0t, h0d, h0s, h0l, h0g, hp1, hp2, hp3, hTa, hc4.target,
    hc4.data, hc4.value, hc4.isStatic, hlen4, ?_, ?_, ?_⟩
  · intro x
    simp only [hsP, Stor.get_set_ite, hd4, hs4, hs3, hs2, hs1, Nat.reduceAdd]
    by_cases hx : lockSlot = x
    · subst hx
      simp only [↓reduceIte, (bal_ne_lock (i := 0) (by decide)).symm,
        (bal_ne_lock (i := 1) (by decide)).symm, (bal_ne_lock (i := 2) (by decide)).symm, hlock]
    · simp only [hx, ↓reduceIte]
  · rw [hlP, hc4.logs, hl4, hl3, hl2, hl1]
    simp only [List.append_assoc]
    rfl
  · rw [hoP, hc4.outputKeep, ho4, ho3, ho2, ho1]

end Blanc.Lift.Curve3Pool
