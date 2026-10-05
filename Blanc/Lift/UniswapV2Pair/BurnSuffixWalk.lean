import Blanc.Lift.UniswapV2Pair.BurnBalanceWalk
import Blanc.Lift.UniswapV2Pair.UpdateSource

/-! Literal Burn reserve-update, fee checkpoint, event and unlock continuations. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The literal Burn continuation replaces cached balance1 and invokes the
shared update with both actual answers. Its original relation and caller tail
survive, and the event stores preserve the moved free-memory pointer. -/
theorem burnUpdate_caller_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat} {M : Mem} {G n : Nat}
    {p supply f L b1 b0 balance1 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256}
    {seg : Seg}
    (project : ∀ {e d i d'}, P e d i d' → Ninst.Run e d i d')
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (low : 96 ≤ p.toNat) (high : p.toNat + 64 < 2 ^ 256)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (balance1 :: burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
        amount1 amount0 toWord extρ R) M G) BurnFinalBalanceSite.second.afterDecodeTree seg) :
    b0.toNat < 2 ^ 112 ∧ balance1.toNat < 2 ^ 112 ∧ sevm.isStatic = false ∧
    ∃ callGas tailGas,
      let locals := burnPricedLocals supply f L balance1 b0 token1 token0 r1 r0
        amount1 amount0 toWord extρ R
      let post := updateWorld sevm b r0 r1 b0 balance1
      let N := updateMemoryAt sevm b M p r0 r1 b0 balance1
      SFunc.RunP P cert.prog sevm
        (St b (r1 :: r0 :: balance1 :: b0 :: 0x17e5 :: locals) M callGas) t_22e0_c60
        (.returned (St post locals N tailGas)) ∧
      PtrMem p (memExtSize (memExtSize n p.toNat 32) (p + 32).toNat 32) N ∧
      SFunc.RunCutP P cert.prog sevm C (St post locals N tailGas) t_17e5_c13 seg := by
  have h := run
  unfold BurnFinalBalanceSite.afterDecodeTree BurnFinalBalanceSite.decodeTree t_17d5_c13 at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  cases h with
  | callRet d lookup pop callee continuation =>
    change some t_22e0_c60 = _ at lookup
    cases lookup
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    rw [eq] at callee
    change SFunc.RunP P cert.prog sevm
      (St b (r1 :: r0 :: balance1 :: b0 :: 0x17e5 ::
        burnPricedLocals supply f L balance1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
        M _) t_22e0_c60 _ at callee
    obtain ⟨bound0, bound1, mutable, gas, returned⟩ :=
      update_inv_at fork mem low high (callee.mono project)
    cases returned
    have layout := updateSyncMemoryAt_layout
      (packed := updateFinalPackedWord sevm b r0 r1 b0 balance1) mem low high
    exact ⟨bound0, bound1, mutable, _, gas, callee, layout.1, continuation⟩
  | callHalt d lookup pop callee =>
    change some t_22e0_c60 = _ at lookup
    cases lookup
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    rw [eq] at callee
    obtain ⟨_, _, _, _, returned⟩ := update_inv_at fork mem low high (callee.mono project)
    cases returned

/-- Fee-on Burn reads the current packed reserves for its actual kLast write. -/
def burnKLastStorePost (sevm : Sevm) (b : Devm) : Devm :=
  afterSstore sevm (afterSload sevm b 8) 11
    (reserve0Read (b.getStorVal sevm.currentTarget 8) *
      reserve1Read (b.getStorVal sevm.currentTarget 8))

private theorem burnKLast_store_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256} {seg : Seg}
    (project : ∀ {e d i d'}, P e d i d' → Ninst.Run e d i d')
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
        amount1 amount0 toWord extρ R) M G) t_17ec_c13 seg) :
    sevm.isStatic = false ∧ ∃ gas, SFunc.RunCutP P cert.prog sevm C
      (St (burnKLastStorePost sevm b)
        (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
        M gas) t_1827_c14 seg := by
  have h := run
  unfold t_17ec_c13 at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_sload fork (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_and (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_div (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_and (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, eq⟩ := ri_and (project hd)
  change d = St (afterSload sevm b 8)
    (((0x21e8 : B256) &&& 0xffffffff) :: reserve1Read (b.getStorVal sevm.currentTarget 8) ::
      reserve0Read (b.getStorVal sevm.currentTarget 8) :: 0x1823 ::
      burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M _ at eq
  rw [show (0x21e8 : B256) &&& 0xffffffff = 0x21e8 from by decide] at eq
  subst d
  cases h with
  | callRet d lookup pop callee continuation =>
    change some t_21e8_c58 = _ at lookup
    cases lookup
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    rw [eq] at callee
    obtain ⟨_, gas, returned⟩ := mul58_inv (callee.mono project)
    cases returned
    unfold t_1823_c13 at continuation
    obtain ⟨_, h⟩ := ric_destP continuation
    obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
    obtain ⟨d, hd, h⟩ := ric_nextP h
    have mutable := ri_sstore_nonstatic fork (project hd)
    obtain ⟨_, rfl⟩ := ri_sstore fork (project hd)
    exact ⟨mutable, _, h⟩
  | callHalt d lookup pop callee =>
    change some t_21e8_c58 = _ at lookup
    cases lookup
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    rw [eq] at callee
    obtain ⟨_, _, returned⟩ := mul58_inv (callee.mono project)
    cases returned

/-- The actual fee flag selects the current-reserve kLast store or skips it. -/
def burnKLastPost (sevm : Sevm) (b : Devm) (feeFlag : B256) : Devm :=
  if feeFlag = 0 then b else burnKLastStorePost sevm b

/-- Both real Burn fee branches reach the event with the same retained relation
and memory; only the fee-on branch reads slot8 and stores its product in slot11. -/
theorem burnKLast_caller_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256} {seg : Seg}
    (project : ∀ {e d i d'}, P e d i d' → Ninst.Run e d i d')
    (fork : CoveredFork sevm.benvStat.fork) (notCut : 14 ∉ C)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
        amount1 amount0 toWord extρ R) M G) t_17e5_c13 seg) :
    (f ≠ 0 → sevm.isStatic = false) ∧ ∃ gas, SFunc.RunCutP P cert.prog sevm C
      (St (burnKLastPost sevm b f)
        (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
        M gas) t_1827_c14 seg := by
  have h := run
  unfold t_17e5_c13 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_iszero (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  change SFunc.RunCutP P cert.prog sevm C
    (St b (0x1827 :: B256.eqCheck f 0 ::
      burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M _)
    (.branchTo t_17ec_c13 14) seg at h
  cases h with
  | toZero d pop continuation =>
    obtain ⟨_, flag, eq⟩ := St.of_pop2 pop
    have fee : f ≠ 0 := by
      intro zero
      rw [zero] at flag
      exact (by decide : B256.eqCheck (0 : B256) 0 ≠ 0) flag
    rw [eq] at continuation
    obtain ⟨mutable, gas, tail⟩ := burnKLast_store_inv project fork continuation
    refine ⟨fun _ => mutable, gas, ?_⟩
    simpa only [burnKLastPost, fee, ite_false] using tail
  | toSuccCut _ _ _ hit _ => exact absurd hit notCut
  | toSucc d w nonzero miss lookup pop continuation =>
    change some t_1827_c14 = _ at lookup
    cases lookup
    obtain ⟨_, flag, eq⟩ := St.of_pop2 pop
    have fee : f = 0 := eq_zero_of_iszero_ne_zero (flag ▸ nonzero)
    rw [eq] at continuation
    rw [burnKLastPost, ite_eq_left fee]
    exact ⟨fun on => False.elim (on fee), _, continuation⟩

def burnEventTopic : B256 :=
  0xdccd412f0b1252819cb1fd330b93224ca42612892bb3f4f789976e6d81936496

def burnEventMemory (M : Mem) (p amount0 amount1 : B256) : Mem :=
  (M.write p.toNat amount0.toBytes).write (p + 32).toNat amount1.toBytes

def burnEventPost (sevm : Sevm) (b : Devm) (toWord amount0 amount1 : B256) : Devm :=
  b.addLog ⟨sevm.currentTarget,
    [burnEventTopic, sevm.caller.toB256, toWord &&& 0xffffffffffffffffffffffffffffffffffffffff],
    amount0.toBytes ++ amount1.toBytes⟩

def burnUnlockPost (sevm : Sevm) (b : Devm) (toWord amount0 amount1 : B256) : Devm :=
  afterSstore sevm (burnEventPost sevm b toWord amount0 amount1) 12 1

/-- The literal Burn LOG3 and unlock return the two priced amounts, with exact
emitter, caller/recipient topics, complete memory image and retained pointer. -/
theorem burnEvent_unlock_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat} {M : Mem} {G n : Nat}
    {p supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256} {seg : Seg}
    (project : ∀ {e d i d'}, P e d i d' → Ninst.Run e d i d')
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (low : 96 ≤ p.toNat) (high : p.toNat + 64 < 2 ^ 256)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
        amount1 amount0 toWord extρ R) M G) t_1827_c14 seg) :
    sevm.isStatic = false ∧ ∃ gas,
      seg = .done (.returned (St (burnUnlockPost sevm b toWord amount0 amount1)
        (amount1 :: amount0 :: R) (burnEventMemory M p amount0 amount1) gas)) ∧
      PtrMem p (memExtSize (memExtSize n p.toNat 32) (p + 32).toNat 32)
        (burnEventMemory M p amount0 amount1) ∧
      p.toNat + 64 ≤ memExtSize (memExtSize n p.toNat 32) (p + 32).toNat 32 := by
  have p32Nat : (p + 32).toNat = p.toNat + 32 := by
    rw [B256.toNat_add_eq_of_nof p 32 (by change p.toNat + 32 < 2 ^ 256; omega)]
    rfl
  have m1 := mem.write p.toNat amount0 (Or.inr low)
  have m2 := m1.write (p + 32).toNat amount1 (Or.inr (by omega))
  have covered : p.toNat + 64 ≤
      memExtSize (memExtSize n p.toNat 32) (p + 32).toNat 32 := by
    have h := (Mem.memWord_write_word (M.write p.toNat amount0.toBytes) (p + 32).toNat amount1).2
    rw [m2.size] at h
    omega
  have h := run
  unfold t_1827_c14 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, eq⟩ := ri_mload (project hd)
  simp only [show Bytes.toB256 [0x40] = (64 : B256) from rfl,
    show (64 : B256).toNat = 64 from rfl,
    mem.read_self (i := 64) (sz := 32) (by have := mem.ge; omega),
    show Bytes.toB256 (M.read 64 32).1 = p from mem.word] at eq
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_mstore (project hd)
  clear * - h m2 covered p32Nat project fork
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, eq⟩ := ri_add (project hd)
  simp only [show Bytes.toB256 [0x20] = (32 : B256) from rfl] at eq
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_mstore (project hd)
  clear * - h m2 covered p32Nat project fork
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, eq⟩ := ri_mload (project hd)
  simp only [show (64 : B256).toNat = 64 from rfl,
    m2.read_self (i := 64) (sz := 32) (by have := m2.ge; omega),
    show Bytes.toB256 (((M.write p.toNat amount0.toBytes).write (p + 32).toNat amount1.toBytes).read
      64 32).1 = p from m2.word] at eq
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_and (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_caller (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, eq⟩ := ri_sub (project hd)
  simp only [B256.sub_self] at eq
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, eq⟩ := ri_add (project hd)
  simp only [show (64 : B256) + 0 = 64 from by decide] at eq
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, eq⟩ := ri_log3 (project hd)
  simp only [show (64 : B256).toNat = 64 from rfl, m2.read_self covered] at eq
  simp only [p32Nat, Mem.read_two_word_writes_at_raw] at eq
  rw [← p32Nat] at eq
  subst d
  clear * - h m2 covered project fork
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h
  have mutable := ri_sstore_nonstatic fork (project hd)
  obtain ⟨_, rfl⟩ := ri_sstore fork (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  cases h with
  | @ret _ out d pop =>
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    simp only [List.set_cons_zero, show Bytes.toB256 [12] = (12 : B256) from rfl,
      show Bytes.toB256 [1] = (1 : B256) from rfl] at eq
    change _ = St (burnUnlockPost sevm b toWord amount0 amount1)
      (amount1 :: amount0 :: R) (burnEventMemory M p amount0 amount1) _ at eq
    refine ⟨mutable, out.gasLeft, ?_, m2, covered⟩
    exact congrArg (fun x => Seg.done (Outcome.returned x)) eq

/-- Exact actual Burn world after the two final decoded balances: reserve and
oracle update, the fee-selected kLast write, Burn log, and unlock. -/
def burnSuffixPost (sevm : Sevm) (b : Devm) (old0 old1 balance0 balance1 feeFlag
    toWord amount0 amount1 : B256) : Devm :=
  burnUnlockPost sevm (burnKLastPost sevm
    (updateWorld sevm b old0 old1 balance0 balance1) feeFlag) toWord amount0 amount1

def burnSuffixMemory (sevm : Sevm) (b : Devm) (M : Mem) (p old0 old1 balance0 balance1
    amount0 amount1 : B256) : Mem :=
  burnEventMemory (updateMemoryAt sevm b M p old0 old1 balance0 balance1) p amount0 amount1

/-- Same-execution Burn suffix: neither update acceptance nor its returned world
is assumed. Both uint112 bounds, mutability and the complete result follow from
literal successful continuations. The actual update call retains P. -/
theorem burnSuffix_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat} {M : Mem} {G n : Nat}
    {p supply f L b1 b0 balance1 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256}
    {seg : Seg}
    (project : ∀ {e d i d'}, P e d i d' → Ninst.Run e d i d')
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (low : 96 ≤ p.toNat) (high : p.toNat + 64 < 2 ^ 256) (notCut : 14 ∉ C)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (balance1 :: burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
        amount1 amount0 toWord extρ R) M G) BurnFinalBalanceSite.second.afterDecodeTree seg) :
    b0.toNat < 2 ^ 112 ∧ balance1.toNat < 2 ^ 112 ∧ sevm.isStatic = false ∧
    ∃ callGas updateGas gas,
      let locals := burnPricedLocals supply f L balance1 b0 token1 token0 r1 r0
        amount1 amount0 toWord extρ R
      let N := updateMemoryAt sevm b M p r0 r1 b0 balance1
      SFunc.RunP P cert.prog sevm
        (St b (r1 :: r0 :: balance1 :: b0 :: 0x17e5 :: locals) M callGas) t_22e0_c60
        (.returned (St (updateWorld sevm b r0 r1 b0 balance1) locals N updateGas)) ∧
      seg = .done (.returned (St
        (burnSuffixPost sevm b r0 r1 b0 balance1 f toWord amount0 amount1)
        (amount1 :: amount0 :: R)
        (burnSuffixMemory sevm b M p r0 r1 b0 balance1 amount0 amount1) gas)) ∧
      PtrMem p
        (memExtSize (memExtSize (memExtSize (memExtSize n p.toNat 32) (p + 32).toNat 32)
          p.toNat 32) (p + 32).toNat 32)
        (burnSuffixMemory sevm b M p r0 r1 b0 balance1 amount0 amount1) ∧
      p.toNat + 64 ≤
        memExtSize (memExtSize (memExtSize (memExtSize n p.toNat 32) (p + 32).toNat 32)
          p.toNat 32) (p + 32).toNat 32 := by
  obtain ⟨bound0, bound1, mutable, callGas, updateGas, callee, updateMem, tail⟩ :=
    burnUpdate_caller_inv project fork mem low high run
  obtain ⟨_, feeGas, eventRun⟩ := burnKLast_caller_inv project fork notCut tail
  obtain ⟨_, gas, returned, eventMem, covered⟩ :=
    burnEvent_unlock_inv project fork updateMem low high eventRun
  exact ⟨bound0, bound1, mutable, callGas, updateGas, gas, callee, returned, eventMem, covered⟩

/-- The actual public Burn wrapper encodes amount0 then amount1 at the retained
pointer and returns all64bytes. Its exact terminal occurrence remains available
for complete frame projections; storage and logs match its incoming world. -/
theorem burnAbi_return_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat} {M : Mem} {G n : Nat}
    {p amount1 amount0 : B256} {seg : Seg}
    (project : ∀ {e d i d'}, P e d i d' → Ninst.Run e d i d')
    (mem : PtrMem p n M) (low : 96 ≤ p.toNat) (high : p.toNat + 64 < 2 ^ 256)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (amount1 :: amount0 :: R) M G) t_053d_c83 seg) :
    ∃ gas d, seg = .done (.halted d) ∧
      Linst.Run sevm (St b (p :: 64 :: R) (burnEventMemory M p amount0 amount1) gas)
        .return_ (.ok d) ∧
      d.output = amount0.toBytes ++ amount1.toBytes ∧
      (∀ a, Devm.getStor d a = Devm.getStor b a) ∧ d.logs = b.logs := by
  have p32Nat : (p + 32).toNat = p.toNat + 32 := by
    rw [B256.toNat_add_eq_of_nof p 32 (by change p.toNat + 32 < 2 ^ 256; omega)]
    rfl
  have m1 := mem.write p.toNat amount0 (Or.inr low)
  have m2 := m1.write (p + 32).toNat amount1 (Or.inr (by omega))
  have covered : p.toNat + 64 ≤
      memExtSize (memExtSize n p.toNat 32) (p + 32).toNat 32 := by
    have h := (Mem.memWord_write_word (M.write p.toNat amount0.toBytes) (p + 32).toNat amount1).2
    rw [m2.size] at h
    omega
  have h := run
  unfold t_053d_c83 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, eq⟩ := ri_mload (project hd)
  simp only [show Bytes.toB256 [0x40] = (64 : B256) from rfl,
    show (64 : B256).toNat = 64 from rfl,
    mem.read_self (i := 64) (sz := 32) (by have := mem.ge; omega),
    show Bytes.toB256 (M.read 64 32).1 = p from mem.word] at eq
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_mstore (project hd)
  clear * - h m2 covered p32Nat project
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, eq⟩ := ri_add (project hd)
  simp only [show Bytes.toB256 [0x20] = (32 : B256) from rfl] at eq
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_mstore (project hd)
  clear * - h m2 covered p32Nat project
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, eq⟩ := ri_mload (project hd)
  simp only [show (64 : B256).toNat = 64 from rfl,
    m2.read_self (i := 64) (sz := 32) (by have := m2.ge; omega),
    show Bytes.toB256 (((M.write p.toNat amount0.toBytes).write (p + 32).toNat amount1.toBytes).read
      64 32).1 = p from m2.word] at eq
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, eq⟩ := ri_sub (project hd)
  simp only [B256.sub_self] at eq
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, eq⟩ := ri_add (project hd)
  simp only [show (0 : B256) + 64 = 64 from by decide] at eq
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  cases h with
  | last terminal =>
    change Linst.Run sevm (St b (p :: 64 :: R)
      (burnEventMemory M p amount0 amount1) _) .return_ (.ok _) at terminal
    obtain ⟨out, stor, logs⟩ := ri_return terminal
    simp only [burnEventMemory, show (64 : B256).toNat = 64 from rfl,
      p32Nat, Mem.read_two_word_writes_at_raw] at out
    exact ⟨_, _, rfl, terminal, out, stor, logs⟩

end Blanc.Lift.UniswapV2Pair
