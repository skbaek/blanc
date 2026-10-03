import Blanc.Lift.UniswapV2Pair.LPBurnSource
import Blanc.Lift.UniswapV2Pair.FeeMintArithmetic

/-! Literal burn pricing uses cached pre-fee liquidity and the post-fee supply. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def burnPricedLocals (supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256)
    (R : List B256) : List B256 :=
  supply :: f :: L :: b1 :: b0 :: token1 :: token0 :: r1 :: r0 :: amount1 :: amount0 :: toWord :: extρ :: R

/-- The actual caller burns cached L, retaining the original relation and literal continuation. -/
theorem burnLP_caller_inv {K : WriterKey → Prop} {st : State}
    {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (lpMintTouched sevm.currentTarget))
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M G)
      t_1683_c13 r) :
    ∃ burnGas residual,
      SFunc.RunP P cert.prog sevm
        (St b (L :: sevm.currentTarget.toB256 :: 0x168d ::
          burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M burnGas)
        t_2992_c63 (.returned (lpBurnPost sevm b
          (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
          M sevm.currentTarget.toB256 L residual)) ∧
      LPBurnSourceResult K st sevm b
        (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
        M sevm.currentTarget.toB256 L residual ∧ sevm.isStatic = false ∧
      SFunc.RunCutP P cert.prog sevm C (lpBurnPost sevm b
        (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
        M sevm.currentTarget.toB256 L residual) t_168d_c13 r := by
  have h := run
  unfold t_1683_c13 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_push (project hd)
  rw [show Bytes.toB256 [0x16, 0x8d] = (0x168d : B256) from rfl] at eq
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  have address := of_run_address (project hd)
  have stack : d.stack = sevm.currentTarget.toB256 :: 0x168d ::
      burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R :=
    address.stack
  have eq := St.of_stackRel address
  rw [stack] at eq
  rw [eq] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_dup (w := L) rfl (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_push (project hd)
  rw [show Bytes.toB256 [0x29, 0x92] = (0x2992 : B256) from rfl] at eq
  subst d
  cases h with
  | callRet d lookup pop callee continuation =>
    change some t_2992_c63 = _ at lookup
    cases lookup
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    rw [eq] at callee
    have freshWord : WriterFreshKeys K (lpMintTouched sevm.currentTarget.toB256.toAdr) := by
      simpa only [toAdr_toB256] using fresh
    obtain ⟨nonstatic, residual, result, source⟩ :=
      lpBurn63_source_inv fork mem rep freshWord (callee.mono project)
    cases result
    exact ⟨_, residual, callee, source, nonstatic, continuation⟩
  | callHalt d lookup pop callee =>
    change some t_2992_c63 = _ at lookup
    cases lookup
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    rw [eq] at callee
    obtain ⟨_, _, _, residual, result⟩ := lpBurn63_inv fork mem (callee.mono project)
    cases result

/-- The literal caller prefix is abstract over callee gas and its returned world. -/
private theorem burnLP_prefix_exact {sevm : Sevm} {b d : Devm} {R : List B256} {M : Mem}
    {gas : Nat} {C : List Nat} {r : Seg}
    {supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256}
    (room : R.length ≤ 1001)
    (callee : SFunc.RunExact cert.prog sevm
      (St b (L :: sevm.currentTarget.toB256 :: 0x168d ::
        burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M gas)
      t_2992_c63 (.returned d))
    (continuation : SFunc.RunExactCut cert.prog sevm C d t_168d_c13 r) :
    SFunc.RunExactCut cert.prog sevm C
      (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
        M (gas + 20)) t_1683_c13 r := by
  unfold t_1683_c13
  refine rxc_dest ?_
  refine rxc_push (w := 0x168d) rfl (by simp only [burnPricedLocals, List.length_cons]; omega) ?_
  refine .next (Ninst.runCompiled_pushItem
    (G := gas + 14) (cost := gBase)
    (by rintro ⟨⟩) rfl rfl (by simp only [St.stack, burnPricedLocals, List.length_cons]; omega)) ?_
  change SFunc.RunExactCut cert.prog sevm C
    (St b (sevm.currentTarget.toB256 :: 0x168d ::
      burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
      M (gas + 14)) _ r
  refine rxc_dup (n := 4) rfl (by simp only [burnPricedLocals, List.length_cons]; omega) ?_
  refine rxc_push (w := 0x2992) rfl (by simp only [burnPricedLocals, List.length_cons]; omega) ?_
  exact rxc_callRet (g := t_2992_c63) rfl callee continuation

/-- Exact finite LP burn is consumed by the real20gas caller prefix at1683. -/
theorem burnLP_caller_exact {K : WriterKey → Prop} {st post : State} {events : List Event}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (lpMintTouched sevm.currentTarget))
    (accepted : st.burnLP sevm.currentTarget L = .ok (post, events))
    (nonstatic : sevm.isStatic = false)
    (balanceSentry : lpBurnBalanceSentry sevm b sevm.currentTarget.toB256 L G)
    (supplySentry : lpBurnSupplySentry sevm b sevm.currentTarget.toB256 L G)
    (room : R.length ≤ 1001)
    (continuation : SFunc.RunExactCut cert.prog sevm C (lpBurnPost sevm b
      (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
      M sevm.currentTarget.toB256 L G) t_168d_c13 r) :
    SFunc.RunExactCut cert.prog sevm C
      (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
        M (lpBurnGas sevm b sevm.currentTarget.toB256 L G + 20)) t_1683_c13 r ∧
    LPBurnSourceResult K st sevm b
      (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
      M sevm.currentTarget.toB256 L G := by
  have freshWord : WriterFreshKeys K (lpMintTouched sevm.currentTarget.toB256.toAdr) := by
    simpa only [toAdr_toB256] using fresh
  have acceptedWord : st.burnLP sevm.currentTarget.toB256.toAdr L = .ok (post, events) := by
    simpa only [toAdr_toB256] using accepted
  have burn := lpBurn63_source_exact
    (R := burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
    (ρ := 0x168d) fork mem rep freshWord acceptedWord nonstatic balanceSentry supplySentry
    (by simp only [burnPricedLocals, List.length_cons]; omega)
  exact ⟨burnLP_prefix_exact room burn.1 continuation, burn.2.1⟩

/-- The literal positive-output guard cannot select its reverting arm. -/
private theorem burnGuard_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg} {flag : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (run : SFunc.RunCutP P cert.prog sevm C (St b (flag :: S) M G) t_162e_c13 r) :
    flag ≠ 0 ∧ ∃ residual,
      SFunc.RunCutP P cert.prog sevm C (St b S M residual) t_1683_c13 r := by
  have h := run
  unfold t_162e_c13 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_push (project hd)
  rw [show Bytes.toB256 [0x16, 0x83] = (0x1683 : B256) from rfl] at eq
  subst d
  rcases ric_branchP h with ⟨_, _, fail⟩ | ⟨positive, residual, tail⟩
  · exact (fail.false_of_noOk (by decide : t_1633_c13.noOk = true)).elim
  · exact ⟨positive, residual, tail⟩

/-- The actual DIV and short-circuit guard derive both positive payout words. -/
private theorem burnSecondPayment_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {product1 supply f L b1 b0 token1 token0 r1 r0 amount0 toWord extρ : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d') (notCut : 13 ∉ C)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (product1 :: supply :: burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 0 amount0 toWord extρ R) M G)
      t_161b_c37 r) :
    0 < amount0.toNat ∧ 0 < (product1 / supply).toNat ∧ ∃ residual,
      SFunc.RunCutP P cert.prog sevm C
        (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
          (product1 / supply) amount0 toWord extρ R) M residual) t_1683_c13 r := by
  have h := run
  unfold t_161b_c37 at h
  dsimp only [burnPricedLocals] at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_div (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_swap rfl (project hd)
  subst d
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_pop (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_push (project hd)
  rw [show Bytes.toB256 [0] = (0 : B256) from rfl] at eq
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_dup (w := amount0) rfl (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_gt (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_dup rfl (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_iszero (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_push (project hd)
  rw [show Bytes.toB256 [0x16, 0x2e] = (0x162e : B256) from rfl] at eq
  subst d
  by_cases zero0 : B256.gtCheck amount0 0 = 0
  · rw [zero0, show B256.eqCheck 0 0 = (1 : B256) from by decide] at h
    cases h with
    | toZero d pop tail =>
      obtain ⟨_, bad, _⟩ := St.of_pop2 pop
      exact ((by decide : (1 : B256) ≠ 0) bad).elim
    | toSuccCut d w nonzero cut pop => exact (notCut cut).elim
    | toSucc d w nonzero nc lookup pop tail =>
      change some t_162e_c13 = _ at lookup
      cases lookup
      obtain ⟨_, _, eq⟩ := St.of_pop2 pop
      rw [eq] at tail
      have bad := (burnGuard_inv project tail).1
      exact (bad rfl).elim
  · have iz : B256.eqCheck (B256.gtCheck amount0 0) 0 = 0 := ite_eq_right zero0
    rw [iz] at h
    have positive0 : 0 < amount0.toNat := by
      have word : (0 : B256) < amount0 := by
        by_contra bad
        simp only [B256.gtCheck, ite_eq_right bad] at zero0
        exact zero0 True.intro
      rw [B256.lt_iff_toNat_lt_toNat] at word
      exact word
    cases h with
    | toSuccCut d w nonzero cut pop => exact (notCut cut).elim
    | toSucc d w nonzero nc lookup pop tail =>
      obtain ⟨_, rfl, _⟩ := St.of_pop2 pop
      exact (nonzero rfl).elim
    | toZero d pop tail =>
      obtain ⟨_, _, eq⟩ := St.of_pop2 pop
      rw [eq] at tail
      unfold t_1629_c37 at tail
      obtain ⟨d, hd, tail⟩ := ric_nextP tail
      obtain ⟨_, eq⟩ := ri_pop (project hd)
      subst d
      obtain ⟨d, hd, tail⟩ := ric_nextP tail
      obtain ⟨_, eq⟩ := ri_push (project hd)
      rw [show Bytes.toB256 [0] = (0 : B256) from rfl] at eq
      subst d
      obtain ⟨d, hd, tail⟩ := ric_nextP tail
      obtain ⟨_, eq⟩ := ri_dup (w := product1 / supply) rfl (project hd)
      subst d
      obtain ⟨d, hd, tail⟩ := ric_nextP tail
      obtain ⟨_, eq⟩ := ri_gt (project hd)
      subst d
      obtain ⟨positive, residual, continuation⟩ := burnGuard_inv project tail
      have positive1 : 0 < (product1 / supply).toNat := by
        have word : (0 : B256) < product1 / supply := by
          by_contra bad
          simp only [B256.gtCheck, ite_eq_right bad] at positive
          exact positive rfl
        rw [B256.lt_iff_toNat_lt_toNat] at word
        exact word
      exact ⟨positive0, positive1, residual, continuation⟩

/-- The second literal supply test rules out division by zero before pricing. -/
private theorem burnSecondSupply_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {product1 supply f L b1 b0 token1 token0 r1 r0 amount0 toWord extρ : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d') (notCut : 13 ∉ C)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (product1 :: supply :: burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 0 amount0 toWord extρ R) M G)
      t_1614_c37 r) :
    supply ≠ 0 ∧ 0 < amount0.toNat ∧ 0 < (product1 / supply).toNat ∧ ∃ residual,
      SFunc.RunCutP P cert.prog sevm C
        (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
          (product1 / supply) amount0 toWord extρ R) M residual) t_1683_c13 r := by
  have h := run
  unfold t_1614_c37 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_dup (w := supply) rfl (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_push (project hd)
  rw [show Bytes.toB256 [0x16, 0x1b] = (0x161b : B256) from rfl] at eq
  subst d
  rcases ric_branchP h with ⟨_, _, failed⟩ | ⟨nonzero, _, body⟩
  · exact (failed.false_of_noOk (by decide : t_161a_c37.noOk = true)).elim
  · exact ⟨nonzero, burnSecondPayment_inv project notCut body⟩

/-- First payout division and the actual second checked multiplication call. -/
private theorem burnFirstPayment_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {product0 supply f L b1 b0 token1 token0 r1 r0 toWord extρ : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d') (notCut : 13 ∉ C)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (product0 :: supply :: burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 0 0 toWord extρ R) M G)
      t_1600_c37 r) :
    B256.Nofm L b1 ∧ supply ≠ 0 ∧ 0 < (product0 / supply).toNat ∧
      0 < ((L * b1) / supply).toNat ∧ ∃ residual,
      SFunc.RunCutP P cert.prog sevm C
        (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
          ((L * b1) / supply) (product0 / supply) toWord extρ R) M residual) t_1683_c13 r := by
  have h := run
  unfold t_1600_c37 at h
  dsimp only [burnPricedLocals] at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_div (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_swap rfl (project hd)
  subst d
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_pop (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_dup (w := supply) rfl (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_push (project hd)
  rw [show Bytes.toB256 [0x16, 0x14] = (0x1614 : B256) from rfl] at eq
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_dup (w := L) rfl (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_dup (w := b1) rfl (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_push (project hd)
  rw [show Bytes.toB256 [0xff, 0xff, 0xff, 0xff] = (0xffffffff : B256) from rfl] at eq
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_push (project hd)
  rw [show Bytes.toB256 [0x21, 0xe8] = (0x21e8 : B256) from rfl] at eq
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_and (project hd)
  rw [show (0x21e8 : B256) &&& 0xffffffff = 0x21e8 from by decide] at eq
  subst d
  cases h with
  | callRet d lookup pop callee continuation =>
    change some t_21e8_c58 = _ at lookup
    cases lookup
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    rw [eq] at callee
    obtain ⟨nowrap, residual, returned⟩ := mul58_inv (callee.mono project)
    cases returned
    exact ⟨nowrap, burnSecondSupply_inv project notCut continuation⟩
  | callHalt d lookup pop callee =>
    change some t_21e8_c58 = _ at lookup
    cases lookup
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    rw [eq] at callee
    obtain ⟨_, residual, returned⟩ := mul58_inv (callee.mono project)
    cases returned

/-- The first literal supply test and first payout division retain the original relation. -/
private theorem burnFirstSupply_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {product0 supply f L b1 b0 token1 token0 r1 r0 toWord extρ : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d') (notCut : 13 ∉ C)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (product0 :: supply :: burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 0 0 toWord extρ R) M G)
      t_15f9_c37 r) :
    B256.Nofm L b1 ∧ supply ≠ 0 ∧ 0 < (product0 / supply).toNat ∧
      0 < ((L * b1) / supply).toNat ∧ ∃ residual,
      SFunc.RunCutP P cert.prog sevm C
        (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
          ((L * b1) / supply) (product0 / supply) toWord extρ R) M residual) t_1683_c13 r := by
  have h := run
  unfold t_15f9_c37 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_dup (w := supply) rfl (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_push (project hd)
  rw [show Bytes.toB256 [0x16, 0x00] = (0x1600 : B256) from rfl] at eq
  subst d
  rcases ric_branchP h with ⟨_, _, failed⟩ | ⟨nonzero, _, body⟩
  · exact (failed.false_of_noOk (by decide : t_15ff_c37.noOk = true)).elim
  · exact burnFirstPayment_inv project notCut body

/-- Post-fee slot0 is read once; both products use the unchanged cached pre-fee L. -/
private theorem burnPricingWords_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {f L b1 b0 token1 token0 r1 r0 toWord extρ : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (fork : CoveredFork sevm.benvStat.fork) (notCut : 13 ∉ C)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (f :: 0 :: L :: b1 :: b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R) M G)
      t_15e2_c37 r) :
    let supply := b.getStorVal sevm.currentTarget 0
    B256.Nofm L b0 ∧ B256.Nofm L b1 ∧ supply ≠ 0 ∧
      0 < ((L * b0) / supply).toNat ∧ 0 < ((L * b1) / supply).toNat ∧ ∃ residual,
      SFunc.RunCutP P cert.prog sevm C
        (St (afterSload sevm b 0)
          (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
            ((L * b1) / supply) ((L * b0) / supply) toWord extρ R) M residual) t_1683_c13 r := by
  have h := run
  unfold t_15e2_c37 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_push (project hd)
  rw [show Bytes.toB256 [0] = (0 : B256) from rfl] at eq
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_sload fork (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_swap rfl (project hd)
  subst d
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_swap rfl (project hd)
  subst d
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_pop (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_dup rfl (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_push (project hd)
  rw [show Bytes.toB256 [0x15, 0xf9] = (0x15f9 : B256) from rfl] at eq
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_dup (w := L) rfl (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_dup (w := b0) rfl (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_push (project hd)
  rw [show Bytes.toB256 [0xff, 0xff, 0xff, 0xff] = (0xffffffff : B256) from rfl] at eq
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_push (project hd)
  rw [show Bytes.toB256 [0x21, 0xe8] = (0x21e8 : B256) from rfl] at eq
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_and (project hd)
  rw [show (0x21e8 : B256) &&& 0xffffffff = 0x21e8 from by decide] at eq
  subst d
  cases h with
  | callRet d lookup pop callee continuation =>
    change some t_21e8_c58 = _ at lookup
    cases lookup
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    rw [eq] at callee
    obtain ⟨nowrap, residual, returned⟩ := mul58_inv (callee.mono project)
    cases returned
    exact ⟨nowrap, burnFirstSupply_inv project notCut continuation⟩
  | callHalt d lookup pop callee =>
    change some t_21e8_c58 = _ at lookup
    cases lookup
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    rw [eq] at callee
    obtain ⟨_, residual, returned⟩ := mul58_inv (callee.mono project)
    cases returned

/-- Source burn pricing is derived from the actual two no-wrap products and divisor. -/
private theorem burnPricing_source_accept {L b0 b1 supply : B256}
    (product0 : B256.Nofm L b0) (product1 : B256.Nofm L b1) (nonzero : supply ≠ 0) :
    burnAmounts L b0 b1 supply =
      .ok (((L * b0) / supply).toNat, ((L * b1) / supply).toNat) := by
  change L.toNat * b0.toNat < 2 ^ 256 at product0
  change L.toNat * b1.toNat < 2 ^ 256 at product1
  rw [burnAmounts, ite_eq_left product0, ite_eq_right nonzero, ite_eq_left product1]
  rw [B256.toNat_div nonzero, B256.toNat_div nonzero,
    B256.toNat_mul_eq_of_nofm product0, B256.toNat_mul_eq_of_nofm product1]
  rfl

/-- Successful actual15e2 pricing derives finite source acceptance and the original LP63 continuation. -/
theorem burnPricing_inv {K : WriterKey → Prop} {st : State}
    {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {f L b1 b0 token1 token0 r1 r0 toWord extρ : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (fork : CoveredFork sevm.benvStat.fork) (notCut : 13 ∉ C) (mem : PtrMem 128 192 M)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (lpMintTouched sevm.currentTarget))
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (f :: 0 :: L :: b1 :: b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R) M G)
      t_15e2_c37 r) :
    let supply := b.getStorVal sevm.currentTarget 0
    let locals := burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
      ((L * b1) / supply) ((L * b0) / supply) toWord extρ R
    B256.Nofm L b0 ∧ B256.Nofm L b1 ∧ supply ≠ 0 ∧ supply = st.totalSupply ∧
    burnAmounts L b0 b1 supply =
      .ok (((L * b0) / supply).toNat, ((L * b1) / supply).toNat) ∧
    0 < ((L * b0) / supply).toNat ∧ 0 < ((L * b1) / supply).toNat ∧
    sevm.isStatic = false ∧ ∃ burnGas residual,
      SFunc.RunP P cert.prog sevm
        (St (afterSload sevm b 0) (L :: sevm.currentTarget.toB256 :: 0x168d :: locals) M burnGas)
        t_2992_c63 (.returned (lpBurnPost sevm (afterSload sevm b 0) locals
          M sevm.currentTarget.toB256 L residual)) ∧
      LPBurnSourceResult K st sevm (afterSload sevm b 0) locals M sevm.currentTarget.toB256 L residual ∧
      SFunc.RunCutP P cert.prog sevm C (lpBurnPost sevm (afterSload sevm b 0) locals
        M sevm.currentTarget.toB256 L residual) t_168d_c13 r := by
  obtain ⟨product0, product1, nonzero, positive0, positive1, gas, priced⟩ :=
    burnPricingWords_inv project fork notCut run
  have readRep : WriterRep K ((afterSload sevm b 0).getStor sevm.currentTarget) st := by
    simpa only [afterSload_getStor] using rep
  obtain ⟨burnGas, residual, callee, source, nonstatic, continuation⟩ :=
    burnLP_caller_inv project fork mem readRep fresh priced
  exact ⟨product0, product1, nonzero, rep.fixed.1,
    burnPricing_source_accept product0 product1 nonzero, positive0, positive1, nonstatic,
    burnGas, residual, callee, source, continuation⟩

/-- The actual output guard costs14gas on its successful arm. -/
private theorem burnGuard_exact {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem}
    {G : Nat} {C : List Nat} {r : Seg} {flag : B256}
    (nonzero : flag ≠ 0) (room : S.length ≤ 1022)
    (continuation : SFunc.RunExactCut cert.prog sevm C (St b S M G) t_1683_c13 r) :
    SFunc.RunExactCut cert.prog sevm C (St b (flag :: S) M (G + 14)) t_162e_c13 r := by
  unfold t_162e_c13
  refine rxc_dest ?_
  refine rxc_push (w := 0x1683) rfl (by simp only [List.length_cons]; omega) ?_
  exact rxc_branch_succ nonzero continuation

/-- Exact second division and both positive-output tests, including the real short circuit. -/
private theorem burnSecondPayment_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {C : List Nat} {r : Seg}
    {product1 supply f L b1 b0 token1 token0 r1 r0 amount0 toWord extρ : B256}
    (positive0 : 0 < amount0.toNat) (positive1 : 0 < (product1 / supply).toNat)
    (room : R.length ≤ 1001)
    (continuation : SFunc.RunExactCut cert.prog sevm C
      (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
        (product1 / supply) amount0 toWord extρ R) M G) t_1683_c13 r) :
    SFunc.RunExactCut cert.prog sevm C
      (St b (product1 :: supply :: burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
        0 amount0 toWord extρ R) M (G + 64)) t_161b_c37 r := by
  have word0 : (0 : B256) < amount0 := B256.lt_iff_toNat_lt_toNat.mpr positive0
  have word1 : (0 : B256) < product1 / supply := B256.lt_iff_toNat_lt_toNat.mpr positive1
  unfold t_161b_c37
  dsimp only [burnPricedLocals] at continuation ⊢
  refine rxc_dest ?_
  refine rxc_div rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_swap rfl ?_
  dsimp only [List.set]
  refine rxc_pop ?_
  refine rxc_push (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (w := amount0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_binary (rr := .gt) (fn := B256.gtCheck) (c := gVerylow)
    (by rintro ⟨⟩) (fun _ => rfl) (v := 1) (ite_eq_left word0)
    (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (w := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_iszero (v := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rxc_push (w := 0x162e) rfl (by simp only [List.length_cons]; omega) ?_
  refine .toZero 0x162e popBurnBy_St2 ?_
  unfold t_1629_c37
  refine rxc_pop ?_
  refine rxc_push (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (w := product1 / supply) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_binary (rr := .gt) (fn := B256.gtCheck) (c := gVerylow)
    (by rintro ⟨⟩) (fun _ => rfl) (v := 1) (ite_eq_left word1)
    (by simp only [List.length_cons]; omega) ?_
  exact burnGuard_exact (by decide : (1 : B256) ≠ 0)
    (by simp only [List.length_cons]; omega) continuation

/-- Exact second denominator check consumes the successful division-and-guard path. -/
private theorem burnSecondSupply_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {C : List Nat} {r : Seg}
    {product1 supply f L b1 b0 token1 token0 r1 r0 amount0 toWord extρ : B256}
    (nonzero : supply ≠ 0) (positive0 : 0 < amount0.toNat)
    (positive1 : 0 < (product1 / supply).toNat) (room : R.length ≤ 1001)
    (continuation : SFunc.RunExactCut cert.prog sevm C
      (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
        (product1 / supply) amount0 toWord extρ R) M G) t_1683_c13 r) :
    SFunc.RunExactCut cert.prog sevm C
      (St b (product1 :: supply :: burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
        0 amount0 toWord extρ R) M (G + 81)) t_1614_c37 r := by
  unfold t_1614_c37
  refine rxc_dest ?_
  refine rxc_dup (w := supply) rfl (by simp only [burnPricedLocals, List.length_cons]; omega) ?_
  refine rxc_push (w := 0x161b) rfl (by simp only [burnPricedLocals, List.length_cons]; omega) ?_
  refine rxc_branch_succ nonzero ?_
  exact burnSecondPayment_exact positive0 positive1 room continuation

/-- Exact first division and literal second mul58 call, with its selected shortcut charge. -/
private theorem burnFirstPayment_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {C : List Nat} {r : Seg}
    {product0 supply f L b1 b0 token1 token0 r1 r0 toWord extρ : B256}
    (product1 : B256.Nofm L b1) (nonzero : supply ≠ 0)
    (positive0 : 0 < (product0 / supply).toNat)
    (positive1 : 0 < ((L * b1) / supply).toNat) (room : R.length ≤ 1001)
    (continuation : SFunc.RunExactCut cert.prog sevm C
      (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
        ((L * b1) / supply) (product0 / supply) toWord extρ R) M G) t_1683_c13 r) :
    SFunc.RunExactCut cert.prog sevm C
      (St b (product0 :: supply :: burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
        0 0 toWord extρ R) M (G + 81 + mul58Charge b1 + 40)) t_1600_c37 r := by
  have second := burnSecondSupply_exact nonzero positive0 positive1 room continuation
  have callee := mul58_exact (sevm := sevm) (b := b) (M := M)
    (R := supply :: burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
      0 (product0 / supply) toWord extρ R) (G := G + 81) (ρ := 0x1614) product1
    (by simp only [burnPricedLocals, List.length_cons]; omega)
  unfold t_1600_c37
  dsimp only [burnPricedLocals]
  refine rxc_dest ?_
  refine rxc_div rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_swap rfl ?_
  dsimp only [List.set]
  refine rxc_pop ?_
  refine rxc_dup (w := supply) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_push (w := 0x1614) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (w := L) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (w := b1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_push (w := 0xffffffff) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_push (w := 0x21e8) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_and (v := 0x21e8) (by decide) (by simp only [List.length_cons]; omega) ?_
  exact rxc_callRet (g := t_21e8_c58) rfl callee second

/-- Exact first denominator test composes the entire remaining pricing arithmetic. -/
private theorem burnFirstSupply_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {C : List Nat} {r : Seg}
    {product0 supply f L b1 b0 token1 token0 r1 r0 toWord extρ : B256}
    (product1 : B256.Nofm L b1) (nonzero : supply ≠ 0)
    (positive0 : 0 < (product0 / supply).toNat)
    (positive1 : 0 < ((L * b1) / supply).toNat) (room : R.length ≤ 1001)
    (continuation : SFunc.RunExactCut cert.prog sevm C
      (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
        ((L * b1) / supply) (product0 / supply) toWord extρ R) M G) t_1683_c13 r) :
    SFunc.RunExactCut cert.prog sevm C
      (St b (product0 :: supply :: burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
        0 0 toWord extρ R) M (G + 81 + mul58Charge b1 + 57)) t_15f9_c37 r := by
  unfold t_15f9_c37
  refine rxc_dest ?_
  refine rxc_dup (w := supply) rfl (by simp only [burnPricedLocals, List.length_cons]; omega) ?_
  refine rxc_push (w := 0x1600) rfl (by simp only [burnPricedLocals, List.length_cons]; omega) ?_
  refine rxc_branch_succ nonzero ?_
  exact burnFirstPayment_exact product1 nonzero positive0 positive1 room continuation

/-- Exact post-fee supply read and first mul58 call consume the full pricing arithmetic. -/
private theorem burnPricingWords_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {C : List Nat} {r : Seg}
    {f L b1 b0 token1 token0 r1 r0 toWord extρ : B256}
    (fork : CoveredFork sevm.benvStat.fork)
    (product0 : B256.Nofm L b0) (product1 : B256.Nofm L b1)
    (nonzero : b.getStorVal sevm.currentTarget 0 ≠ 0)
    (positive0 : 0 < ((L * b0) / b.getStorVal sevm.currentTarget 0).toNat)
    (positive1 : 0 < ((L * b1) / b.getStorVal sevm.currentTarget 0).toNat)
    (room : R.length ≤ 1001)
    (continuation : SFunc.RunExactCut cert.prog sevm C
      (St (afterSload sevm b 0)
        (burnPricedLocals (b.getStorVal sevm.currentTarget 0) f L b1 b0 token1 token0 r1 r0
          ((L * b1) / b.getStorVal sevm.currentTarget 0)
          ((L * b0) / b.getStorVal sevm.currentTarget 0) toWord extρ R) M G) t_1683_c13 r) :
    SFunc.RunExactCut cert.prog sevm C
      (St b (f :: 0 :: L :: b1 :: b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
        M (G + 81 + mul58Charge b1 + 57 + mul58Charge b0 + 37 + sloadCost sevm b 0 + 4))
      t_15e2_c37 r := by
  have first := burnFirstSupply_exact product1 nonzero positive0 positive1 room continuation
  have callee := mul58_exact (sevm := sevm) (M := M)
    (b := afterSload sevm b 0)
    (R := b.getStorVal sevm.currentTarget 0 ::
      burnPricedLocals (b.getStorVal sevm.currentTarget 0) f L b1 b0 token1 token0 r1 r0
        0 0 toWord extρ R)
    (G := G + 81 + mul58Charge b1 + 57) (ρ := 0x15f9) product0
    (by simp only [burnPricedLocals, List.length_cons]; omega)
  unfold t_15e2_c37
  refine rxc_dest ?_
  refine rxc_push (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_sload_sel fork (by simp only [List.length_cons]; omega) ?_
  refine rxc_swap rfl ?_
  dsimp only [List.set]
  refine rxc_swap rfl ?_
  dsimp only [List.set]
  refine rxc_pop ?_
  refine rxc_dup (w := b.getStorVal sevm.currentTarget 0) rfl
    (by simp only [List.length_cons]; omega) ?_
  refine rxc_push (w := 0x15f9) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (w := L) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (w := b0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_push (w := 0xffffffff) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_push (w := 0x21e8) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_and (v := 0x21e8) (by decide) (by simp only [List.length_cons]; omega) ?_
  exact rxc_callRet (g := t_21e8_c58) rfl callee first

/-- Accepted source pricing supplies exactly the actual checked products and divisor. -/
private theorem burnPricing_source_inv {L b0 b1 supply : B256} {amount0 amount1 : Nat}
    (accepted : burnAmounts L b0 b1 supply = .ok (amount0, amount1)) :
    B256.Nofm L b0 ∧ B256.Nofm L b1 ∧ supply ≠ 0 ∧
      (amount0, amount1) = (((L * b0) / supply).toNat, ((L * b1) / supply).toNat) := by
  have priced := accepted
  unfold burnAmounts at accepted
  by_cases product0 : L.toNat * b0.toNat < 2 ^ 256
  · rw [ite_eq_left product0] at accepted
    by_cases zeroSupply : supply = 0
    · rw [ite_eq_left zeroSupply] at accepted
      cases accepted
    · rw [ite_eq_right zeroSupply] at accepted
      by_cases product1 : L.toNat * b1.toNat < 2 ^ 256
      · have words := burnPricing_source_accept product0 product1 zeroSupply
        rw [priced] at words
        exact ⟨product0, product1, zeroSupply, Except.ok.inj words⟩
      · rw [ite_eq_right product1] at accepted
        cases accepted
  · rw [ite_eq_right product0] at accepted
    cases accepted

/-- Pricing199gas, two selected checked-mul charges, one supply read and the sequential LP debit. -/
def burnPricingGas (sevm : Sevm) (b : Devm) (L b1 b0 : B256) (G : Nat) : Nat :=
  lpBurnGas sevm (afterSload sevm b 0) sevm.currentTarget.toB256 L G +
    sloadCost sevm b 0 + mul58Charge b0 + mul58Charge b1 + 199

/-- Exact finite source pricing constructs the whole15e2→168d path and the physical LP debit. -/
theorem burnPricing_exact {K : WriterKey → Prop} {st post : State} {events : List Event}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {f L b1 b0 token1 token0 r1 r0 toWord extρ : B256} {amount0 amount1 : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (lpMintTouched sevm.currentTarget))
    (priced : burnAmounts L b0 b1 (b.getStorVal sevm.currentTarget 0) = .ok (amount0, amount1))
    (positive0 : 0 < amount0) (positive1 : 0 < amount1)
    (accepted : st.burnLP sevm.currentTarget L = .ok (post, events))
    (nonstatic : sevm.isStatic = false)
    (balanceSentry : lpBurnBalanceSentry sevm (afterSload sevm b 0) sevm.currentTarget.toB256 L G)
    (supplySentry : lpBurnSupplySentry sevm (afterSload sevm b 0) sevm.currentTarget.toB256 L G)
    (room : R.length ≤ 1001)
    (continuation : SFunc.RunExactCut cert.prog sevm C (lpBurnPost sevm (afterSload sevm b 0)
      (burnPricedLocals (b.getStorVal sevm.currentTarget 0) f L b1 b0 token1 token0 r1 r0
        ((L * b1) / b.getStorVal sevm.currentTarget 0)
        ((L * b0) / b.getStorVal sevm.currentTarget 0) toWord extρ R)
      M sevm.currentTarget.toB256 L G) t_168d_c13 r) :
    SFunc.RunExactCut cert.prog sevm C
      (St b (f :: 0 :: L :: b1 :: b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
        M (burnPricingGas sevm b L b1 b0 G)) t_15e2_c37 r ∧
    LPBurnSourceResult K st sevm (afterSload sevm b 0)
      (burnPricedLocals (b.getStorVal sevm.currentTarget 0) f L b1 b0 token1 token0 r1 r0
        ((L * b1) / b.getStorVal sevm.currentTarget 0)
        ((L * b0) / b.getStorVal sevm.currentTarget 0) toWord extρ R)
      M sevm.currentTarget.toB256 L G ∧
    b.getStorVal sevm.currentTarget 0 = st.totalSupply ∧
    amount0 = ((L * b0) / b.getStorVal sevm.currentTarget 0).toNat ∧
    amount1 = ((L * b1) / b.getStorVal sevm.currentTarget 0).toNat := by
  obtain ⟨product0, product1, nonzero, values⟩ := burnPricing_source_inv priced
  have value0 : amount0 = ((L * b0) / b.getStorVal sevm.currentTarget 0).toNat :=
    congrArg Prod.fst values
  have value1 : amount1 = ((L * b1) / b.getStorVal sevm.currentTarget 0).toNat :=
    congrArg Prod.snd values
  have readRep : WriterRep K ((afterSload sevm b 0).getStor sevm.currentTarget) st := by
    simpa only [afterSload_getStor] using rep
  have burn := burnLP_caller_exact fork mem readRep fresh accepted nonstatic
    balanceSentry supplySentry room continuation
  have pricing := burnPricingWords_exact fork product0 product1 nonzero
    (value0 ▸ positive0) (value1 ▸ positive1) room burn.1
  have cost :
      lpBurnGas sevm (afterSload sevm b 0) sevm.currentTarget.toB256 L G + 20 + 81 +
        mul58Charge b1 + 57 + mul58Charge b0 + 37 + sloadCost sevm b 0 + 4 =
      burnPricingGas sevm b L b1 b0 G := by
    unfold burnPricingGas
    omega
  rw [cost] at pricing
  exact ⟨pricing, burn.2, rep.fixed.1, value0, value1⟩

end Blanc.Lift.UniswapV2Pair
