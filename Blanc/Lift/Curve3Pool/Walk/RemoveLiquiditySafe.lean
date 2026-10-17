import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidity
import Blanc.Lift.Curve3Pool.Spec

/-!
# `remove_liquidity`: the raw effect

`removeLiquidity_raw`: a successful frame of the pool on the `remove_liquidity` selector, from a
`Checkpoint` at entry and the frame premises, has the model's step on the decoded call and the
`RawEffect` Spec states, with the environment read off its children (`totalSupply`'s reply, the
three `transfer`s' `RawCallOk`, `burnFrom`'s word). `Refine.rawEffect_refines` takes it from
there.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-! ## Words and numbers -/

/-- Vyper's checked product (`x * y / x == y or x == 0`) did not wrap. -/
theorem mul_check_toNat {x y : B256} (h : x * y / x = y ∨ x = 0) :
    x.toNat * y.toNat < 2 ^ 256 := by
  rcases h with h | h
  · by_cases hx : x = 0
    · rw [hx, show (0 : B256).toNat = 0 from rfl, Nat.zero_mul]; exact Nat.two_pow_pos _
    · have e := congrArg B256.toNat h
      rw [B256.toNat_div hx, B256.toNat_mul] at e
      unfold Nat.lo at e
      have hq := Nat.div_mul_le_self (x.toNat * y.toNat % 2 ^ 256) x.toNat
      rw [e] at hq
      have hm := Nat.mod_le (x.toNat * y.toNat) (2 ^ 256)
      have hl := Nat.mod_lt (x.toNat * y.toNat) (Nat.two_pow_pos 256)
      have : x.toNat * y.toNat % 2 ^ 256 = x.toNat * y.toNat := by
        apply Nat.le_antisymm hm
        rw [Nat.mul_comm] at hq; exact hq
      omega
  · rw [h, show (0 : B256).toNat = 0 from rfl, Nat.zero_mul]; exact Nat.two_pow_pos _

/-! ## The model's step -/

/-- **The model's `remove_liquidity`** when every check passes. -/
theorem removeLiquidity_eq {s : State} {e : Env} {amt T : Nat} {m : V3}
    (hT : e.supply = some T) (hT0 : T ≠ 0)
    (hmul : ∀ k : Fin 3, s.balances.get k * amt < 2 ^ 256)
    (hmin : ∀ k : Fin 3, m.get k ≤ s.balances.get k * amt / T)
    (hle : ∀ k : Fin 3, s.balances.get k * amt / T ≤ s.balances.get k)
    (hpush : ∀ k : Fin 3, (e.coin k).pushOk = true) (hburn : e.burnOk = true) (hTa : amt ≤ T) :
    removeLiquidity s e amt m = some ⟨{ s with balances :=
        ⟨s.balances.v0 - s.balances.v0 * amt / T, s.balances.v1 - s.balances.v1 * amt / T,
          s.balances.v2 - s.balances.v2 * amt / T⟩ }, none,
      [.removeLiquidity e.caller
        ⟨s.balances.v0 * amt / T, s.balances.v1 * amt / T, s.balances.v2 * amt / T⟩ V3.zero
        (T - amt)],
      [.push 0 e.caller (s.balances.v0 * amt / T), .push 1 e.caller (s.balances.v1 * amt / T),
        .push 2 e.caller (s.balances.v2 * amt / T), .burn e.caller amt]⟩ := by
  have m0 := hmul 0
  have m1 := hmul 1
  have m2 := hmul 2
  have n0 := hmin 0
  have n1 := hmin 1
  have n2 := hmin 2
  have l0 := hle 0
  have l1 := hle 1
  have l2 := hle 2
  have p0 := hpush 0
  have p1 := hpush 1
  have p2 := hpush 2
  simp only [V3.get, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceEqDiff,
    ↓reduceIte] at m0 m1 m2 n0 n1 n2 l0 l1 l2
  simp only [removeLiquidity, hT, V3.ofFnM, V3.get, chkMul, chkDiv, chkSub, req, wordSize, p0, p1,
    p2, hburn, ↓reduceIte]
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceEqDiff, ↓reduceIte, m0,
    m1, m2, hT0, ge_iff_le, n0, n1, n2, l0, l1, l2, hTa, Option.bind_eq_bind, Option.bind_some]

/-! ## Machine words as the model's numbers -/

theorem word_toNat (x : B256) : word x.toNat = x.toBytes := by
  unfold word; rw [toB256_toNat]

/-- An unwrapped checked quotient's number. -/
theorem rlOut_toNat {B A T : B256} (hm : B.toNat * A.toNat < 2 ^ 256) (hT : T ≠ 0) :
    (B * A / T).toNat = B.toNat * A.toNat / T.toNat := by
  rw [B256.toNat_div hT, B256.toNat_mul]
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt hm]

theorem toNat_ne_zero {T : B256} (hT : T ≠ 0) : T.toNat ≠ 0 := fun h =>
  hT (B256.toNat_inj _ _ (by rw [h]; rfl))

theorem toNat_le_of_not_lt {x y : B256} (h : ¬ x < y) : y.toNat ≤ x.toNat := by
  rw [B256.lt_iff_toNat_lt_toNat] at h; omega

/-- `XAt` over equal states. -/
theorem XAt.of_eq {sevm : Sevm} {post : Devm} {pc : Nat} {d d' : Devm} {L : List Exec.Frame}
    (e : d = d') (h : XAt sevm post pc d L) : XAt sevm post pc d' L := e ▸ h

/-- The environment a `remove_liquidity` frame observed: the supply word `T`, every coin's
`transfer` and the `burnFrom` accepted, no balance read, no pull, no mint. -/
def rlEnv (sevm : Sevm) (T : B256) : Env :=
  ⟨sevm.benvStat.time.toNat, sevm.caller.toB256.toNat, sevm.value.toNat,
    fun _ => ⟨none, none, false, true⟩, some T.toNat, false, true⟩

/-- An iteration's checks, as numbers. -/
theorem RLPush.nat {sevm : Sevm} {B C T : B256} {i : Nat} {c : Exec.Frame}
    (h : RLPush sevm B C T i c) :
    B.toNat * (rlAmt sevm).toNat < 2 ^ 256 ∧
      (B * rlAmt sevm / T).toNat = B.toNat * (rlAmt sevm).toNat / T.toNat ∧
      (rlMin sevm i).toNat ≤ B.toNat * (rlAmt sevm).toNat / T.toNat ∧
      B.toNat * (rlAmt sevm).toNat / T.toNat ≤ B.toNat := by
  have hm := mul_check_toNat h.mul
  have hv := rlOut_toNat hm h.supply
  refine ⟨hm, hv, ?_, ?_⟩
  · rw [← hv]; exact toNat_le_of_not_lt h.min
  · rw [← hv]; exact toNat_le_of_not_lt h.le

/-- **Safety of `remove_liquidity`.** A successful frame of the pool's runtime on the
`remove_liquidity` selector, entered at a `Checkpoint` with empty stack and memory, under the
frame premises (the coins and 3Crv are not precompiles; the pool's code is nonempty; the identity
precompile is ready; each child keeps the pool's storage and address 4's code), computed the
model's step on the decoded call in the environment `rlEnv` it observed, with the raw effect
Spec states. -/
theorem removeLiquidity_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidity)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (hcoin : ∀ k : Fin 3,
      ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
    (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre)
    (hkeep : PoolCallsKeep ⟨0, sevm, pre, .ok post, exc⟩)
    (hidk : ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨hlock, hval, c0, c1, c2, c3, c4, hL, h0t, h0d, h0s, h0l, h0g, hp0, hp1, hp2, hTa, h4t,
    h4d, h4v, h4s, h4l, hstorF, hlogsF, houtF⟩ :=
    xa_removeLiquidity hcode hfork hlen hcd hsel htok (fun i hi => hcoin ⟨i, hi⟩) hpc hid hkeep
      hidk hx
  have hdec : decodeCall sevm = .removeLiquidity (arg sevm 0) (argV3 sevm 1) :=
    decodeCall_at (k := 7) rfl hsel hlen
  -- the model's numbers
  have hA : arg sevm 0 = (rlAmt sevm).toNat := by
    unfold arg Sevm.argWord
    rw [show (32 * (0 : B256) + 4 : B256) = Bytes.toB256 [4] by decide]
  have hM0 : (argV3 sevm 1).get 0 = (rlMin sevm 0).toNat := by
    show (Sevm.dataWord sevm (32 * 1 + 4)).toNat = _
    rw [show (32 * 1 + 4 : B256) = Bytes.toB256 [32] * Nat.toB256 0 + Bytes.toB256 [36] by decide]
  have hM1 : (argV3 sevm 1).get 1 = (rlMin sevm 1).toNat := by
    show (Sevm.dataWord sevm (32 * (1 + 1) + 4)).toNat = _
    rw [show (32 * (1 + 1) + 4 : B256) = Bytes.toB256 [32] * Nat.toB256 1 + Bytes.toB256 [36]
      by decide]
  have hM2 : (argV3 sevm 1).get 2 = (rlMin sevm 2).toNat := by
    show (Sevm.dataWord sevm (32 * (1 + 2) + 4)).toNat = _
    rw [show (32 * (1 + 2) + 4 : B256) = Bytes.toB256 [32] * Nat.toB256 2 + Bytes.toB256 [36]
      by decide]
  obtain ⟨m0, v0, n0, l0⟩ := hp0.nat
  obtain ⟨m1, v1, n1, l1⟩ := hp1.nat
  obtain ⟨m2, v2, n2, l2⟩ := hp2.nat
  have hT0 := toNat_ne_zero hp0.supply
  have hTa' := toNat_le_of_not_lt hTa
  have hb : ∀ k : Fin 3, s.balances.get k = (balAt (pre.getStor sevm.currentTarget) k).toNat :=
    fun k => (hck.abs.balances k).symm
  have hrl := removeLiquidity_eq (s := s) (e := rlEnv sevm (rlSupply c0)) (amt := arg sevm 0)
    (m := argV3 sevm 1) (T := (rlSupply c0).toNat) rfl hT0
    (fun k => by
      rw [hb, hA]
      match k with
      | 0 => exact m0
      | 1 => exact m1
      | 2 => exact m2)
    (fun k => by
      rw [hb, hA]
      match k with
      | 0 => rw [hM0]; exact n0
      | 1 => rw [hM1]; exact n1
      | 2 => rw [hM2]; exact n2)
    (fun k => by
      rw [hb, hA]
      match k with
      | 0 => exact l0
      | 1 => exact l1
      | 2 => exact l2)
    (fun _ => rfl) rfl (by rw [hA]; exact hTa')
  refine ⟨rlEnv sevm (rlSupply c0), ?o, ?step, ?raw⟩
  case step =>
    rw [hdec]
    show (if (rlEnv sevm (rlSupply c0)).value = 0 then _ else none) = _
    rw [show (rlEnv sevm (rlSupply c0)).value = 0 by rw [rlEnv, hval]; rfl]
    exact hrl
  case raw =>
    have hmem1 : c1 ∈ children ⟨0, sevm, pre, .ok post, exc⟩ := by
      rw [hL]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    have hmem2 : c2 ∈ children ⟨0, sevm, pre, .ok post, exc⟩ := by
      rw [hL]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have hmem3 : c3 ∈ children ⟨0, sevm, pre, .ok post, exc⟩ := by
      rw [hL]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
    have hmem4 : c4 ∈ children ⟨0, sevm, pre, .ok post, exc⟩ := by
      rw [hL]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
    have htake : ∀ {X Y : Bytes}, (transferSel ++ X ++ Y).take 4 = transferSel :=
      fun {X Y} => by rw [List.append_assoc]; exact List.take_left' rfl
    have hb0 : s.balances.v0 = (balAt (pre.getStor sevm.currentTarget) 0).toNat := hb 0
    have hb1 : s.balances.v1 = (balAt (pre.getStor sevm.currentTarget) 1).toNat := hb 1
    have hb2 : s.balances.v2 = (balAt (pre.getStor sevm.currentTarget) 2).toNat := hb 2
    have hw0 : word (s.balances.v0 * arg sevm 0 / (rlSupply c0).toNat) =
        (rlOut sevm (pre.getStor sevm.currentTarget) (rlSupply c0) 0).toBytes := by
      rw [hb0, hA, ← v0, word_toNat]
    have hw1 : word (s.balances.v1 * arg sevm 0 / (rlSupply c0).toNat) =
        (rlOut sevm (pre.getStor sevm.currentTarget) (rlSupply c0) 1).toBytes := by
      rw [hb1, hA, ← v1, word_toNat]
    have hw2 : word (s.balances.v2 * arg sevm 0 / (rlSupply c0).toNat) =
        (rlOut sevm (pre.getStor sevm.currentTarget) (rlSupply c0) 2).toBytes := by
      rw [hb2, hA, ← v2, word_toNat]
    refine ⟨?env, ?stor, ?logs, ?output, ?calls⟩
    case env =>
      refine ⟨rfl, rfl, rfl, fun k => ?_, ?_, fun h => (by cases h), fun _ => Or.inr ?_⟩
      · refine ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun h => (by cases h),
          fun _ => Or.inr ?_⟩
        match k with
        | 0 => exact ⟨c1, hmem1, hp0.target, by rw [hp0.data]; exact htake, hp0.ok⟩
        | 1 => exact ⟨c2, hmem2, hp1.target, by rw [hp1.data]; exact htake, hp1.ok⟩
        | 2 => exact ⟨c3, hmem3, hp2.target, by rw [hp2.data]; exact htake, hp2.ok⟩
      · intro T' h
        cases h
        exact Or.inr ⟨0, c0, by rw [hL]; rfl, h0t, h0d, h0l, rfl⟩
      · exact ⟨c4, hmem4, h4t, by rw [h4d, List.append_assoc]; exact List.take_left' rfl, h4l⟩
    case stor =>
      have hs0 : (balAt (pre.getStor sevm.currentTarget) 0 -
          rlOut sevm (pre.getStor sevm.currentTarget) (rlSupply c0) 0).toNat =
          s.balances.v0 - s.balances.v0 * arg sevm 0 / (rlSupply c0).toNat := by
        rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr (by rw [v0]; exact l0)),
          v0, hb0, hA]
      have hs1 : (balAt (pre.getStor sevm.currentTarget) 1 -
          rlOut sevm (pre.getStor sevm.currentTarget) (rlSupply c0) 1).toNat =
          s.balances.v1 - s.balances.v1 * arg sevm 0 / (rlSupply c0).toNat := by
        rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr (by rw [v1]; exact l1)),
          v1, hb1, hA]
      have hs2 : (balAt (pre.getStor sevm.currentTarget) 2 -
          rlOut sevm (pre.getStor sevm.currentTarget) (rlSupply c0) 2).toNat =
          s.balances.v2 - s.balances.v2 * arg sevm 0 / (rlSupply c0).toNat := by
        rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr (by rw [v2]; exact l2)),
          v2, hb2, hA]
      rw [hdec]
      refine ⟨fun x hx => ?_, fun f hf => ?_⟩
      · have e0 : balancesBase + Nat.toB256 0 ≠ x := hx (.bal 0) (List.mem_cons_self ..)
        have e1 : balancesBase + Nat.toB256 1 ≠ x :=
          hx (.bal 1) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        have e2 : balancesBase + Nat.toB256 2 ≠ x :=
          hx (.bal 2) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        rw [hstorF x, Stor.get_set_ne _ e2, Stor.get_set_ne _ e1, Stor.get_set_ne _ e0]
        rfl
      · have hf' : f = .bal 0 ∨ f = .bal 1 ∨ f = .bal 2 := by
          simpa only [footprint, balFlds, List.mem_cons, List.not_mem_nil, or_false] using hf
        rcases hf' with rfl | rfl | rfl
        · show ((post.getStor sevm.currentTarget).get (balancesBase + Nat.toB256 0)).toNat = _
          rw [hstorF, Stor.get_set_ne _ (bal_ne_bal (i := 2) (j := 0) (by decide) (by decide)
            (by decide)), Stor.get_set_ne _ (bal_ne_bal (i := 1) (j := 0) (by decide) (by decide)
            (by decide)), Stor.get_set_self, hs0]
          rfl
        · show ((post.getStor sevm.currentTarget).get (balancesBase + Nat.toB256 1)).toNat = _
          rw [hstorF, Stor.get_set_ne _ (bal_ne_bal (i := 2) (j := 1) (by decide) (by decide)
            (by decide)), Stor.get_set_self, hs1]
          rfl
        · show ((post.getStor sevm.currentTarget).get (balancesBase + Nat.toB256 2)).toNat = _
          rw [hstorF, Stor.get_set_self, hs2]
          rfl
    case logs =>
      clear hrl hx hkeep hidk hstorF hmem1 hmem2 hmem3 hmem4 htake
      have hwT : word ((rlSupply c0).toNat - arg sevm 0) = (rlSupply c0 - rlAmt sevm).toBytes := by
        rw [hA, ← B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr hTa'), word_toNat]
      have hw00 : word 0 = (0 : B256).toBytes := rfl
      have htop : topicRemoveLiquidity = rlTopic := by decide
      have hev : eventLog sevm.currentTarget (Event.removeLiquidity (rlEnv sevm (rlSupply c0)).caller
          ⟨s.balances.v0 * arg sevm 0 / (rlSupply c0).toNat,
            s.balances.v1 * arg sevm 0 / (rlSupply c0).toNat,
            s.balances.v2 * arg sevm 0 / (rlSupply c0).toNat⟩ V3.zero
          ((rlSupply c0).toNat - arg sevm 0)) =
          ⟨sevm.currentTarget, [rlTopic, sevm.caller.toB256],
            (rlOut sevm (pre.getStor sevm.currentTarget) (rlSupply c0) 0).toBytes ++
            (rlOut sevm (pre.getStor sevm.currentTarget) (rlSupply c0) 1).toBytes ++
            (rlOut sevm (pre.getStor sevm.currentTarget) (rlSupply c0) 2).toBytes ++
            (0 : B256).toBytes ++ (0 : B256).toBytes ++ (0 : B256).toBytes ++
            (rlSupply c0 - rlAmt sevm).toBytes⟩ := by
        simp only [eventLog, wordsV3, V3.zero, hw0, hw1, hw2, hwT, hw00, htop, rlEnv, toB256_toNat,
          List.append_assoc]
      rw [hlogsF, show children ⟨0, sevm, pre, .ok post, exc⟩ = [c0, c1, c2, c3, c4] from hL]
      show _ = _ ++ _ ++ [eventLog sevm.currentTarget _]
      rw [hev]
      simp only [List.flatMap_cons, List.flatMap_nil, h0g, List.nil_append, List.append_nil,
        List.append_assoc]
    case output => rw [houtF]; rfl
    case calls =>
      intro hs
      replace hs : sevm.isStatic = false := hs
      clear * - hs hL h0s hp0 hp1 hp2 h4t h4d h4v h4s hcoin htok hw0 hw1 hw2 hA
      have hwA : word (arg sevm 0) = (rlAmt sevm).toBytes := by rw [hA, word_toNat]
      have hwC : word (rlEnv sevm (rlSupply c0)).caller = sevm.caller.toB256.toBytes :=
        word_toNat _
      rw [CallsOf, modelCalls, show children ⟨0, sevm, pre, .ok post, exc⟩ = [c0, c1, c2, c3, c4]
        from hL]
      simp only [List.filterMap_cons, List.filterMap_nil, h0s, hp0.static, hp1.static, hp2.static,
        h4s, hs, ↓reduceIte, Bool.false_eq_true, List.map_cons, List.map_nil, encodeCall,
        List.filter_cons, List.filter_nil, framed, coinAdr, tokenAdr, entryStor,
        decide_eq_false (hcoin 0), decide_eq_false (hcoin 1), decide_eq_false (hcoin 2),
        decide_eq_false htok, Bool.not_false, Bool.true_or, hp0.target, hp1.target, hp2.target,
        h4t, hp0.data, hp1.data, hp2.data, h4d, hp0.value, hp1.value, hp2.value, h4v, hw0, hw1,
        hw2, hwA, hwC]
      rfl

end Blanc.Lift.Curve3Pool
