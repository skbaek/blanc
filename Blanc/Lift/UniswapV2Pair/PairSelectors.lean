import Blanc.Lift.UniswapV2Pair.StaticViewClassify

/-! Actual successful calls to the certified Pair runtime, in any context, reach one of its
twenty-seven published selectors; the fallback and short calldata revert. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The twenty-seven published Pair selectors, in dispatcher order. -/
def pairSelectors : List B256 :=
  [0xd21220a7, 0xd505accf, 0xdd62ed3e, 0xfff6cae9, 0xba9a7a56, 0xbc25cf77, 0xc45a0155,
   0x7ecebe00, 0x89afcb44, 0x95d89b41, 0xa9059cbb, 0x6a627842, 0x70a08231, 0x7464fc3d,
   0x3644e515, 0x485cc955, 0x5909c0d5, 0x5a3d5493, 0x23b872dd, 0x30adf81f, 0x313ce567,
   0x095ea7b3, 0x0dfe1681, 0x18160ddd, 0x022c0d9f, 0x06fdde03, 0x0902f1ac]

theorem pairSelector_of_hit {x s : B256} (hit : ¬ B256.eqCheck x s = 0)
    (mem : x ∈ pairSelectors) : s ∈ pairSelectors := by
  have equal : x = s := by
    by_contra different
    exact hit (by simp only [B256.eqCheck, different, ite_false])
  exact equal ▸ mem

/-- The dispatcher admits only the published selectors. -/
theorem pair_selector_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
    (run : SFunc.Run cert.prog sevm (St b [] M G) t_001a_c0 o) :
    Blanc.Sevm.selector sevm ∈ pairSelectors := by
  have h := run.cut
  unfold t_001a_c0 at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_calldataload hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_shr hd
  simp only [show Bytes.toB256 [0x00] = (0 : B256) from rfl,
    show Bytes.toB256 [0xe0] = (224 : B256) from rfl,
    show (224 : B256).toNat = 224 from rfl] at hd
  subst d
  obtain ⟨_, h⟩ := ric_cmp_gt h
  split at h
  next less =>
    unfold t_002b_c0 at h
    obtain ⟨_, h⟩ := ric_cmp_gt h
    split at h
    next less =>
      unfold t_0036_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      split at h
      next less =>
        unfold t_0041_c0 at h
        obtain ⟨_, h⟩ := ric_cmp_eq (g := t_05da_c75) (by decide) rfl h
        split at h
        next miss =>
          unfold t_004c_c0 at h
          obtain ⟨_, h⟩ := ric_cmp_eq (g := t_05e2_c76) (by decide) rfl h
          split at h
          next miss =>
            unfold t_0057_c0 at h
            obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0640_c77) (by decide) rfl h
            split at h
            next miss =>
              unfold t_0062_c0 at h
              obtain ⟨_, h⟩ := ric_cmp_eq (g := t_067b_c78) (by decide) rfl h
              split at h
              next miss =>
                unfold t_006d_c0 at h
                obtain ⟨_, _, h⟩ := ric_next h
                cases (SFunc.RunCut.uncut h) with
                | jump _ lookup _ body =>
                    rw [show cert.prog[32]? = some t_01b9_c32 from rfl] at lookup
                    cases lookup
                    have impossible := SFunc.Run.cut body
                    change SFunc.RunCut cert.prog sevm [] _ (.dest t_000c_c0) (.done o) at impossible
                    obtain ⟨_, impossible⟩ := ric_dest impossible
                    exact (getter_zeroRevert_impossible impossible).elim
              next hit =>
                exact pairSelector_of_hit hit (by decide)
            next hit =>
              exact pairSelector_of_hit hit (by decide)
          next hit =>
            exact pairSelector_of_hit hit (by decide)
        next hit =>
          exact pairSelector_of_hit hit (by decide)
      next greater =>
        unfold t_0071_c0 at h
        obtain ⟨_, h⟩ := ric_dest h
        obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0597_c79) (by decide) rfl h
        split at h
        next miss =>
          unfold t_007d_c0 at h
          obtain ⟨_, h⟩ := ric_cmp_eq (g := t_059f_c80) (by decide) rfl h
          split at h
          next miss =>
            unfold t_0088_c0 at h
            obtain ⟨_, h⟩ := ric_cmp_eq (g := t_05d2_c81) (by decide) rfl h
            split at h
            next miss =>
              unfold t_0093_c0 at h
              obtain ⟨_, _, h⟩ := ric_next h
              cases (SFunc.RunCut.uncut h) with
              | jump _ lookup _ body =>
                  rw [show cert.prog[32]? = some t_01b9_c32 from rfl] at lookup
                  cases lookup
                  have impossible := SFunc.Run.cut body
                  change SFunc.RunCut cert.prog sevm [] _ (.dest t_000c_c0) (.done o) at impossible
                  obtain ⟨_, impossible⟩ := ric_dest impossible
                  exact (getter_zeroRevert_impossible impossible).elim
            next hit =>
              exact pairSelector_of_hit hit (by decide)
          next hit =>
            exact pairSelector_of_hit hit (by decide)
        next hit =>
          exact pairSelector_of_hit hit (by decide)
    next greater =>
      unfold t_0097_c0 at h
      obtain ⟨_, h⟩ := ric_dest h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      split at h
      next less =>
        unfold t_00a3_c0 at h
        obtain ⟨_, h⟩ := ric_cmp_eq (g := t_04d7_c82) (by decide) rfl h
        split at h
        next miss =>
          unfold t_00ae_c0 at h
          obtain ⟨_, h⟩ := ric_cmp_eq (g := t_050a_c83) (by decide) rfl h
          split at h
          next miss =>
            unfold t_00b9_c0 at h
            obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0556_c84) (by decide) rfl h
            split at h
            next miss =>
              unfold t_00c4_c0 at h
              obtain ⟨_, h⟩ := ric_cmp_eq (g := t_055e_c85) (by decide) rfl h
              split at h
              next miss =>
                unfold t_00cf_c0 at h
                obtain ⟨_, _, h⟩ := ric_next h
                cases (SFunc.RunCut.uncut h) with
                | jump _ lookup _ body =>
                    rw [show cert.prog[32]? = some t_01b9_c32 from rfl] at lookup
                    cases lookup
                    have impossible := SFunc.Run.cut body
                    change SFunc.RunCut cert.prog sevm [] _ (.dest t_000c_c0) (.done o) at impossible
                    obtain ⟨_, impossible⟩ := ric_dest impossible
                    exact (getter_zeroRevert_impossible impossible).elim
              next hit =>
                exact pairSelector_of_hit hit (by decide)
            next hit =>
              exact pairSelector_of_hit hit (by decide)
          next hit =>
            exact pairSelector_of_hit hit (by decide)
        next hit =>
          exact pairSelector_of_hit hit (by decide)
      next greater =>
        unfold t_00d3_c0 at h
        obtain ⟨_, h⟩ := ric_dest h
        obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0469_c86) (by decide) rfl h
        split at h
        next miss =>
          unfold t_00df_c0 at h
          obtain ⟨_, h⟩ := ric_cmp_eq (g := t_049c_c87) (by decide) rfl h
          split at h
          next miss =>
            unfold t_00ea_c0 at h
            obtain ⟨_, h⟩ := ric_cmp_eq (g := t_04cf_c88) (by decide) rfl h
            split at h
            next miss =>
              unfold t_00f5_c0 at h
              obtain ⟨_, _, h⟩ := ric_next h
              cases (SFunc.RunCut.uncut h) with
              | jump _ lookup _ body =>
                  rw [show cert.prog[32]? = some t_01b9_c32 from rfl] at lookup
                  cases lookup
                  have impossible := SFunc.Run.cut body
                  change SFunc.RunCut cert.prog sevm [] _ (.dest t_000c_c0) (.done o) at impossible
                  obtain ⟨_, impossible⟩ := ric_dest impossible
                  exact (getter_zeroRevert_impossible impossible).elim
            next hit =>
              exact pairSelector_of_hit hit (by decide)
          next hit =>
            exact pairSelector_of_hit hit (by decide)
        next hit =>
          exact pairSelector_of_hit hit (by decide)
  next greater =>
    unfold t_00f9_c0 at h
    obtain ⟨_, h⟩ := ric_dest h
    obtain ⟨_, h⟩ := ric_cmp_gt h
    split at h
    next less =>
      unfold t_0105_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      split at h
      next less =>
        unfold t_0110_c0 at h
        obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0416_c89) (by decide) rfl h
        split at h
        next miss =>
          unfold t_011b_c0 at h
          obtain ⟨_, h⟩ := ric_cmp_eq (g := t_041e_c90) (by decide) rfl h
          split at h
          next miss =>
            unfold t_0126_c0 at h
            obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0459_c91) (by decide) rfl h
            split at h
            next miss =>
              unfold t_0131_c0 at h
              obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0461_c92) (by decide) rfl h
              split at h
              next miss =>
                unfold t_013c_c0 at h
                obtain ⟨_, _, h⟩ := ric_next h
                cases (SFunc.RunCut.uncut h) with
                | jump _ lookup _ body =>
                    rw [show cert.prog[32]? = some t_01b9_c32 from rfl] at lookup
                    cases lookup
                    have impossible := SFunc.Run.cut body
                    change SFunc.RunCut cert.prog sevm [] _ (.dest t_000c_c0) (.done o) at impossible
                    obtain ⟨_, impossible⟩ := ric_dest impossible
                    exact (getter_zeroRevert_impossible impossible).elim
              next hit =>
                exact pairSelector_of_hit hit (by decide)
            next hit =>
              exact pairSelector_of_hit hit (by decide)
          next hit =>
            exact pairSelector_of_hit hit (by decide)
        next hit =>
          exact pairSelector_of_hit hit (by decide)
      next greater =>
        unfold t_0140_c0 at h
        obtain ⟨_, h⟩ := ric_dest h
        obtain ⟨_, h⟩ := ric_cmp_eq (g := t_03ad_c93) (by decide) rfl h
        split at h
        next miss =>
          unfold t_014c_c0 at h
          obtain ⟨_, h⟩ := ric_cmp_eq (g := t_03f0_c94) (by decide) rfl h
          split at h
          next miss =>
            unfold t_0157_c0 at h
            obtain ⟨_, h⟩ := ric_cmp_eq (g := t_03f8_c95) (by decide) rfl h
            split at h
            next miss =>
              unfold t_0162_c0 at h
              obtain ⟨_, _, h⟩ := ric_next h
              cases (SFunc.RunCut.uncut h) with
              | jump _ lookup _ body =>
                  rw [show cert.prog[32]? = some t_01b9_c32 from rfl] at lookup
                  cases lookup
                  have impossible := SFunc.Run.cut body
                  change SFunc.RunCut cert.prog sevm [] _ (.dest t_000c_c0) (.done o) at impossible
                  obtain ⟨_, impossible⟩ := ric_dest impossible
                  exact (getter_zeroRevert_impossible impossible).elim
            next hit =>
              exact pairSelector_of_hit hit (by decide)
          next hit =>
            exact pairSelector_of_hit hit (by decide)
        next hit =>
          exact pairSelector_of_hit hit (by decide)
    next greater =>
      unfold t_0166_c0 at h
      obtain ⟨_, h⟩ := ric_dest h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      split at h
      next less =>
        unfold t_0172_c0 at h
        obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0315_c96) (by decide) rfl h
        split at h
        next miss =>
          unfold t_017d_c0 at h
          obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0362_c97) (by decide) rfl h
          split at h
          next miss =>
            unfold t_0188_c0 at h
            obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0393_c98) (by decide) rfl h
            split at h
            next miss =>
              unfold t_0193_c0 at h
              obtain ⟨_, _, h⟩ := ric_next h
              cases (SFunc.RunCut.uncut h) with
              | jump _ lookup _ body =>
                  rw [show cert.prog[32]? = some t_01b9_c32 from rfl] at lookup
                  cases lookup
                  have impossible := SFunc.Run.cut body
                  change SFunc.RunCut cert.prog sevm [] _ (.dest t_000c_c0) (.done o) at impossible
                  obtain ⟨_, impossible⟩ := ric_dest impossible
                  exact (getter_zeroRevert_impossible impossible).elim
            next hit =>
              exact pairSelector_of_hit hit (by decide)
          next hit =>
            exact pairSelector_of_hit hit (by decide)
        next hit =>
          exact pairSelector_of_hit hit (by decide)
      next greater =>
        unfold t_0197_c0 at h
        obtain ⟨_, h⟩ := ric_dest h
        obtain ⟨_, h⟩ := ric_cmp_eq (g := t_01be_c99) (by decide) rfl h
        split at h
        next miss =>
          unfold t_01a3_c0 at h
          obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0259_c100) (by decide) rfl h
          split at h
          next miss =>
            unfold t_01ae_c0 at h
            obtain ⟨_, h⟩ := ric_cmp_eq (g := t_02d6_c101) (by decide) rfl h
            split at h
            next miss =>
              unfold t_01b9_c0 at h
              obtain ⟨_, h⟩ := ric_dest h
              obtain ⟨_, _, h⟩ := ric_next h
              obtain ⟨_, _, h⟩ := ric_next h
              exact (ric_revert h).elim
            next hit =>
              exact pairSelector_of_hit hit (by decide)
          next hit =>
            exact pairSelector_of_hit hit (by decide)
        next hit =>
          exact pairSelector_of_hit hit (by decide)

/-- Every successful raw run at the Pair code carries a published selector. -/
theorem pair_bytecode_selector_inv {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Blanc.Sevm.selector sevm ∈ pairSelectors := by
  obtain ⟨f, entry, run⟩ := lift_sound cert_check codeEq fork run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨_, _, _, run⟩ := getter_guards_inv run
  exact pair_selector_inv run

end Blanc.Lift.UniswapV2Pair
