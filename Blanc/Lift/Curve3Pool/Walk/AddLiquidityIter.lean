import Blanc.Lift.Curve3Pool.Walk.AddLiquidityPull2

/-!
# `add_liquidity`'s pull loop: one iteration

`xa_al_pullTx` composes the `transferFrom` part of an iteration (payload, `CALL`, `raw_call`
test, coin `2`'s second `balanceOf`, new balance, counter); `xa_al_pullIter` the whole iteration.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

theorem AlPullImg.mono {img img' : Bytes} {i : Nat} {F AF A T D0 : B256} {old nv : Nat → B256}
    (h : AlPullImg img i F AF A T D0 old nv)
    (P : ∀ o w, WordAt img o w → o + 32 ≤ 0x4e0 → WordAt img' o w) :
    AlPullImg img' i F AF A T D0 old nv where
  m0 := ⟨P _ _ h.m0.f0 (by decide), P _ _ h.m0.f1 (by decide), P _ _ h.m0.f2 (by decide),
    P _ _ h.m0.fee (by decide), P _ _ h.m0.adm (by decide), P _ _ h.m0.amp (by decide),
    P _ _ h.m0.supply (by decide), P _ _ h.m0.d0 (by decide), P _ _ h.m0.o0 (by decide),
    P _ _ h.m0.o1 (by decide), P _ _ h.m0.o2 (by decide)⟩
  ctr := P _ _ h.ctr (by decide)
  n0 := P _ _ h.n0 (by decide)
  n1 := P _ _ h.n1 (by decide)
  n2 := P _ _ h.n2 (by decide)

/-- A `balanceOf(self)` reply child of coin `C`. -/
structure AlBal (sevm : Sevm) (C : B256) (c : Exec.Frame) : Prop where
  target : c.sevm.currentTarget = C.toAdr
  data : c.sevm.data = balanceOfData sevm.currentTarget
  static : c.sevm.isStatic = true
  len : 32 ≤ c.post.output.length
  logs : c.post.logs = []

/-- The `transferFrom` child of coin `C` for `amounts[i]`. -/
structure AlPull (sevm : Sevm) (C : B256) (i : Nat) (c : Exec.Frame) : Prop where
  target : c.sevm.currentTarget = C.toAdr
  data : c.sevm.data = transferFromSel ++ sevm.caller.toB256.toBytes ++
    sevm.currentTarget.toB256.toBytes ++ (alAmt sevm i).toBytes
  value : c.sevm.value = 0
  static : c.sevm.isStatic = sevm.isStatic
  ok : RawCallOk c.post.output

theorem AlStatic.idReady {sevm : Sevm} {b d : Devm} {t : Adr} {input : Bytes} {c : Exec.Frame}
    (h : AlStatic sevm b d t input c) (hid : IdReady sevm b) : IdReady sevm d :=
  ⟨by rw [h.code4]; exact hid.nodeleg, h.acc _ hid.warm, hid.pre, hid.fork⟩

theorem AlStatic.bal {sevm : Sevm} {b d : Devm} {C : B256} {c : Exec.Frame}
    (h : AlStatic sevm b d C.toAdr (balanceOfData sevm.currentTarget) c) : AlBal sevm C c :=
  ⟨h.target, h.data, h.static, h.len, h.clogs⟩

/-- **The `transferFrom` part of an iteration** (`0x110d` → the loop head or its exit). -/
theorem xa_al_pullTx {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {σ : Stor} {i : Nat} {v F AF A T D0 : B256} {old nv : Nat → B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hi : i < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (hm : AlPullImg img i F AF A T D0 old nv) (hv : WordAt img 0x4e0 v)
    (hC : WordAt img 0x500 (coinAt σ i))
    (hst : ∀ x, (b.getStor sevm.currentTarget).get x = σ.get x)
    (hpc : b.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm b) (hdepth : 0 < sevm.depth)
    (hcoin : ¬ sevm.benvStat.rules.isPrecomp (coinAt σ i).toAdr)
    (hK : CallKeeps sevm (coinAt σ i)) (hSK : StaticKeeps sevm (coinAt σ i))
    (h : XAt sevm post 0x110d (St b [3, 0x4c0] M G) L) :
    ∃ (c : Exec.Frame) (Lr L' : List Exec.Frame) (b' : Devm) (M' : Mem) (img' : Bytes) (G' : Nat)
      (cr : B256), L = c :: (Lr ++ L') ∧ AlPull sevm (coinAt σ i) i c ∧
      ((i ≠ 2 ∧ Lr = [] ∧ cr = v) ∨
        (i = 2 ∧ ∃ c1, Lr = [c1] ∧ AlBal sevm (coinAt σ i) c1 ∧
          ¬ Bytes.toB256 (c1.post.output.take 32) < v ∧
          cr = Bytes.toB256 (c1.post.output.take 32) - v)) ∧
      ¬ old i + cr < old i ∧
      (∀ x, (b'.getStor sevm.currentTarget).get x = σ.get x) ∧
      b'.logs = b.logs ++ c.post.logs ∧ b'.output = b.output ∧
      b'.getCode sevm.currentTarget = b.getCode sevm.currentTarget ∧ IdReady sevm b' ∧
      Mem.Reads M' img' ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
      AlPullImg img' (i + 1) F AF A T D0 old (Function.update nv i (old i + cr)) ∧
      XAt sevm post (if i + 1 = 3 then 0x1333 else 0x105d) (St b' [3, 0x4c0] M' G') L' := by
  obtain ⟨c, L3, b3, d, G3, rfl, hb3, hc, ⟨hkc, hidc⟩, ⟨img3, hR3, hW3, hA3, hrd, hctr3, P3⟩, h3⟩ :=
    xa_al_pl3 hcode hfork hi hid hdepth hR hW hA hm.ctr hC hcoin hpc hK h
  have hpc3 : b3.getCode sevm.currentTarget ≠ .empty := by rw [hb3.code]; exact hpc
  have hid3 := hid.of_rel hb3
  have hidd : IdReady sevm d :=
    ⟨by rw [hc.codePost, hidc, hc.codePre]; exact hid3.nodeleg, hc.warm _ hid3.warm, hid.pre,
      hid.fork⟩
  replace h3 := xa_jumpdestAt (pc' := 0x11e7) (atJ hcode (by kernel_rfl)) (by rfl) h3
  obtain ⟨_, h3⟩ := h3
  obtain ⟨hok, b6, M6, img6, G6, hb6, hR6, hW6, hA6, P6, h6⟩ :=
    xa_al_pl4 hcode hidd hR3 hW3 hA3 hrd h3
  have P36 : ∀ o w, WordAt img o w → o + 32 ≤ 0x5c0 → WordAt img6 o w := fun o w hw ho =>
    P6 o w (P3 o w hw (by omega)) (by omega) (by omega)
  have hst6 : ∀ x, (b6.getStor sevm.currentTarget).get x = σ.get x := by
    intro x
    rw [hb6.stor, hc.storPost _ hpc3 x, hkc x, hc.storPre _ hpc3, hb3.stor, hst]
  have hl6 : b6.logs = b.logs ++ c.post.logs := by rw [hb6.logs, hc.logs, hb3.logs]
  have ho6 : b6.output = b.output := by rw [hb6.output, hc.outputKeep, hb3.output]
  have hcd6 : b6.getCode sevm.currentTarget = b.getCode sevm.currentTarget := by
    rw [hb6.code, hc.code _ hpc3, hb3.code]
  have hid6 := hidd.of_rel hb6
  have hpull : AlPull sevm (coinAt σ i) i c :=
    ⟨hc.target, hc.data, hc.value, hc.isStatic, hc.output ▸ hok⟩
  rcases xa_al_pl5 hcode hfork hi hR6 hW6 hA6 (P36 _ _ hm.ctr (by decide)) (P36 _ _ hv (by decide))
      (P36 _ _ hC (by decide)) hcoin hSK h6 with
    ⟨hi2, M7, G7, hR7, hW7, hA7, h7⟩ |
    ⟨hi2, c1, L4, d2, M7, img7, G7, rfl, hs1, hge, hR7, hW7, hA7, P7, hw7, h7⟩
  · obtain ⟨hadd, M8, img8, G8, hR8, hW8, hA8, hP8, h8⟩ := xa_al_pl6 hcode hi hR7 hW7 hA7
      (hm.mono fun o w hw ho => P36 o w hw (by omega)) (P36 _ _ hv (by decide)) h7
    exact ⟨c, [], L3, b6, M8, img8, G8, v, rfl, hpull, .inl ⟨hi2, rfl, rfl⟩, hadd, hst6, hl6,
      ho6, hcd6, hid6, hR8, hW8, hA8, hP8, h8⟩
  · obtain ⟨hadd, M8, img8, G8, hR8, hW8, hA8, hP8, h8⟩ := xa_al_pl6 hcode hi hR7 hW7 hA7
      (hm.mono fun o w hw ho => P7 o w (P36 o w hw (by omega)) (by omega) (by omega)) hw7 h7
    refine ⟨c, [c1], L4, d2, M8, img8, G8, _, rfl, hpull, .inr ⟨hi2, c1, rfl, hs1.bal, hge, rfl⟩,
      hadd, ?_, ?_, ?_, ?_, hs1.idReady hid6, hR8, hW8, hA8, hP8, h8⟩
    · intro x; rw [hs1.stor, hst6]
    · rw [hs1.logs, hl6]
    · rw [hs1.out, ho6]
    · rw [← hcd6]; exact hs1.codeK _ (by rw [hcd6]; exact hpc)

/-- The reply word of a child. -/
abbrev alWord (c : Exec.Frame) : B256 := Bytes.toB256 (c.post.output.take 32)

/-- Iteration `i`'s children and the amount it credited: none for a zero amount, the
`transferFrom` for coins `0, 1`, and for coin `2` the `transferFrom` between two `balanceOf`s,
crediting their (checked) difference. -/
def AlPullKids (sevm : Sevm) (C : B256) (i : Nat) (amt : B256) (Lc : List Exec.Frame) (cr : B256) :
    Prop :=
  (amt = 0 ∧ Lc = [] ∧ cr = 0) ∨
  (amt ≠ 0 ∧ i ≠ 2 ∧ ∃ c, Lc = [c] ∧ AlPull sevm C i c ∧ cr = amt) ∨
  (amt ≠ 0 ∧ i = 2 ∧ ∃ c0 c c1, Lc = [c0, c, c1] ∧ AlBal sevm C c0 ∧ AlPull sevm C i c ∧
    AlBal sevm C c1 ∧ ¬ alWord c1 < alWord c0 ∧ cr = alWord c1 - alWord c0)

/-- **One pull iteration** (`0x105d` → the loop head or its exit). -/
theorem xa_al_pullIter {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {σ : Stor} {i : Nat} {F AF A T D0 : B256} {old nv : Nat → B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hi : i < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (hm : AlPullImg img i F AF A T D0 old nv)
    (hst : ∀ x, (b.getStor sevm.currentTarget).get x = σ.get x)
    (hpc : b.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm b) (hdepth : 0 < sevm.depth)
    (hcoin : ¬ sevm.benvStat.rules.isPrecomp (coinAt σ i).toAdr)
    (hK : CallKeeps sevm (coinAt σ i)) (hSK : StaticKeeps sevm (coinAt σ i))
    (h : XAt sevm post 0x105d (St b [3, 0x4c0] M G) L) :
    (T = 0 → 0 < (alAmt sevm i).toNat) ∧
    ∃ (Lc L' : List Exec.Frame) (b' : Devm) (M' : Mem) (img' : Bytes) (G' : Nat) (cr : B256),
      L = Lc ++ L' ∧ AlPullKids sevm (coinAt σ i) i (alAmt sevm i) Lc cr ∧
      ¬ old i + cr < old i ∧
      (∀ x, (b'.getStor sevm.currentTarget).get x = σ.get x) ∧
      b'.logs = b.logs ++ Lc.flatMap (fun c => c.post.logs) ∧ b'.output = b.output ∧
      b'.getCode sevm.currentTarget = b.getCode sevm.currentTarget ∧ IdReady sevm b' ∧
      Mem.Reads M' img' ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
      AlPullImg img' (i + 1) F AF A T D0 old (Function.update nv i (old i + cr)) ∧
      XAt sevm post (if i + 1 = 3 then 0x1333 else 0x105d) (St b' [3, 0x4c0] M' G') L' := by
  obtain ⟨M1, img1, G1, hR1, hW1, hA1, hm1, hv1, hC1, hT0, h1⟩ :=
    xa_al_pl1 hcode hfork hi hst hR hW hA hm h
  refine ⟨hT0, ?_⟩
  have hst1 : ∀ x, ((afterSload sevm b (coinsBase + Nat.toB256 i)).getStor
      sevm.currentTarget).get x = σ.get x := by
    intro x; rw [afterSload_getStor, hst]
  have hpc1 : (afterSload sevm b (coinsBase + Nat.toB256 i)).getCode sevm.currentTarget ≠ .empty := by
    rw [afterSload_getCode]; exact hpc
  have hid1 := hid.afterSload (coinsBase + Nat.toB256 i)
  rcases xa_al_pl2 hcode hfork hi hR1 hW1 hA1 hm1.ctr hv1 hC1 hcoin hSK h1 with
    ⟨hv0, M2, G2, hR2, hW2, hA2, h2⟩ | ⟨hv0, hi2, M2, G2, hR2, hW2, hA2, h2⟩ |
    ⟨hv0, hi2, c0, L2, d0, M2, img2, G2, rfl, hs0, hR2, hW2, hA2, P2, hw2, h2⟩
  · obtain ⟨hadd, M8, img8, G8, hR8, hW8, hA8, hP8, h8⟩ := xa_al_pl6 hcode hi hR2 hW2 hA2 hm1 hv1 h2
    refine ⟨[], L, _, M8, img8, G8, _, rfl, .inl ⟨hv0, rfl, hv0⟩, hadd, hst1, ?_, ?_, ?_, hid1,
      hR8, hW8, hA8, hP8, h8⟩
    · rw [afterSload_logs, List.flatMap_nil, List.append_nil]
    · rw [afterSload_output]
    · rw [afterSload_getCode]
  · obtain ⟨c, Lr, L', b', M8, img8, G8, cr, rfl, hpull, hcase, hadd, hst8, hl8, ho8, hcd8, hid8,
      hR8, hW8, hA8, hP8, h8⟩ := xa_al_pullTx hcode hfork hi hR2 hW2 hA2 hm1 hv1 hC1 hst1 hpc1 hid1
      hdepth hcoin hK hSK h2
    rcases hcase with ⟨-, rfl, rfl⟩ | ⟨hi2', -⟩
    · refine ⟨[c], L', b', M8, img8, G8, _, rfl, .inr (.inl ⟨hv0, hi2, c, rfl, hpull, rfl⟩), hadd,
        hst8, ?_, ?_, ?_, hid8, hR8, hW8, hA8, hP8, h8⟩
      · rw [hl8, afterSload_logs, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      · rw [ho8, afterSload_output]
      · rw [hcd8, afterSload_getCode]
    · exact absurd hi2' hi2
  · have hst0 : ∀ x, (d0.getStor sevm.currentTarget).get x = σ.get x := by
      intro x; rw [hs0.stor, hst1]
    have hpc0 : d0.getCode sevm.currentTarget ≠ .empty := by rw [hs0.codeK _ hpc1]; exact hpc1
    obtain ⟨c, Lr, L', b', M8, img8, G8, cr, rfl, hpull, hcase, hadd, hst8, hl8, ho8, hcd8, hid8,
      hR8, hW8, hA8, hP8, h8⟩ := xa_al_pullTx hcode hfork hi hR2 hW2 hA2
      (hm1.mono fun o w hw ho => P2 o w hw (by omega) (by omega)) hw2
      (P2 _ _ hC1 (by decide) (by decide)) hst0 hpc0 (hs0.idReady hid1) hdepth hcoin hK hSK h2
    rcases hcase with ⟨hi2', -⟩ | ⟨-, c1, rfl, hb1, hge, rfl⟩
    · exact absurd hi2 hi2'
    · refine ⟨[c0, c, c1], L', b', M8, img8, G8, _, rfl,
        .inr (.inr ⟨hv0, hi2, c0, c, c1, rfl, hs0.bal, hpull, hb1, hge, rfl⟩), hadd, hst8, ?_, ?_,
        ?_, hid8, hR8, hW8, hA8, hP8, h8⟩
      · rw [hl8, hs0.logs, afterSload_logs, List.flatMap_cons, List.flatMap_cons, List.flatMap_cons,
          List.flatMap_nil, hs0.clogs, hb1.logs, List.nil_append, List.append_nil, List.append_nil]
      · rw [ho8, hs0.out, afterSload_output]
      · rw [hcd8, hs0.codeK _ hpc1, afterSload_getCode]

end Blanc.Lift.Curve3Pool
