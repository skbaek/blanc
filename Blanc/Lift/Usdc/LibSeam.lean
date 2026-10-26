import Blanc.Lift.Usdc.LibReject

/-!
# F6: the library seam (`LibRejects`, `lib_rejects_pair`)

The shape the implementation side consumes (design `fp-checker.md`, Appendix A §F6, verbatim):
a successful library frame whose calldata word at byte `4` names the Pair returns at least one
word, the first of which is zero (`false`).

`LibRejects` is `Blanc.Lift.Usdc.LibRejects`, as frozen.  The frozen theorem name
`lib_rejects_pair` is already taken in `Blanc.Lift.Usdc` by U7a's library lemma
(`Blanc/Lift/Usdc/LibReject.lean`, a different signature that this module does not change), so the
seam theorem lives one namespace down, as `Blanc.Lift.Usdc.LibSeam.lib_rejects_pair`; its
statement is the frozen one.  It is an adapter: the fresh machine is the walk state
`St pre [] Mem.empty pre.gasLeft`, the calldata word is `Sevm.dataWord sevm 4`, and a 32-byte
zero prefix reads as the word `0`.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift

/-- The library never accepts the Pair: a successful library frame (code `Lib.code`) whose
calldata word at byte `4` names `pair`, where `pair` holds the Pair's runtime and is no
precompile, returns at least one word, the first of which is zero (`false`). -/
def LibRejects (pair : Adr) : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm}, Exec 0 sevm pre (.ok post) → sevm.code = Lib.code →
    CoveredFork sevm.benvStat.fork → pre.memory = Mem.empty → pre.stack = [] →
    Bytes.toB256 (sevm.data.sliceD 4 32 0) = pair.toB256 →
    pre.getCode pair = UniswapV2Pair.code → ¬ sevm.benvStat.rules.isPrecomp pair →
    32 ≤ post.output.length ∧ Bytes.toB256 (post.output.takeD 32 0) = 0

/-- The library's rejection seam under the actual rules of a neutral fork. -/
def LibRejectsH (pair : Adr) : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm}, Exec 0 sevm pre (.ok post) → sevm.code = Lib.code →
    NeutralFork sevm.benvStat.fork → pre.memory = Mem.empty → pre.stack = [] →
    Bytes.toB256 (sevm.data.sliceD 4 32 0) = pair.toB256 →
    pre.getCode pair = UniswapV2Pair.code → ¬ sevm.benvStat.rules.isPrecomp pair →
    32 ≤ post.output.length ∧ Bytes.toB256 (post.output.takeD 32 0) = 0

/-- Rejection for actual children sharing this environment's block context. -/
def LibRejectsAt (pair : Adr) (sevm : Sevm) : Prop :=
  ∀ {child : Sevm} {pre post : Devm}, child.benvStat = sevm.benvStat →
    Exec 0 child pre (.ok post) → child.code = Lib.code →
    pre.memory = Mem.empty → pre.stack = [] →
    Bytes.toB256 (child.data.sliceD 4 32 0) = pair.toB256 →
    pre.getCode pair = UniswapV2Pair.code → ¬ child.benvStat.rules.isPrecomp pair →
    32 ≤ post.output.length ∧ Bytes.toB256 (post.output.takeD 32 0) = 0

/-- Restrict modern rejection through an actual child's block-context equality. -/
theorem LibRejects.at_of_covered {pair : Adr} {sevm : Sevm}
    (rejects : LibRejects pair) (fork : CoveredFork sevm.benvStat.fork) :
    LibRejectsAt pair sevm := by
  intro child pre post stat run code hmem hstack hword hpair notPre
  have childFork : CoveredFork child.benvStat.fork := by rw [stat]; exact fork
  exact rejects run code childFork hmem hstack hword hpair notPre

/-- Restrict historical rejection through the same actual block-context equality. -/
theorem LibRejectsH.at_of_neutral {pair : Adr} {sevm : Sevm}
    (rejects : LibRejectsH pair) (fork : NeutralFork sevm.benvStat.fork) :
    LibRejectsAt pair sevm := by
  intro child pre post stat run code hmem hstack hword hpair notPre
  have childFork : NeutralFork child.benvStat.fork := by rw [stat]; exact fork
  exact rejects run code childFork hmem hstack hword hpair notPre

namespace LibSeam

private theorem rejects_of_raw {F : Fork → Prop} {pair : Adr}
    (rejects : ∀ {sevm : Sevm} {b post : Devm} {G : Nat},
      Exec 0 sevm (St b [] Mem.empty G) (.ok post) → sevm.code = Lib.code →
      F sevm.benvStat.fork →
      b.getCode (Sevm.dataWord sevm 4).toAdr = UniswapV2Pair.code →
      ¬ sevm.benvStat.rules.isPrecomp (Sevm.dataWord sevm 4).toAdr →
      32 ≤ post.output.length ∧ post.output.take 32 = List.replicate 32 0) :
    ∀ {sevm : Sevm} {pre post : Devm}, Exec 0 sevm pre (.ok post) →
      sevm.code = Lib.code → F sevm.benvStat.fork →
      pre.memory = Mem.empty → pre.stack = [] →
      Bytes.toB256 (sevm.data.sliceD 4 32 0) = pair.toB256 →
      pre.getCode pair = UniswapV2Pair.code → ¬ sevm.benvStat.rules.isPrecomp pair →
      32 ≤ post.output.length ∧ Bytes.toB256 (post.output.takeD 32 0) = 0 := by
  intro sevm pre post run code fork hmem hstack hword hpair notPre
  have hdw : (Sevm.dataWord sevm 4).toAdr = pair := by
    rw [Sevm.dataWord, show (4 : B256).toNat = 4 from rfl, hword, toAdr_toB256]
  rw [St.self hstack hmem] at run
  obtain ⟨hlen, htake⟩ := rejects run code fork
    (by rw [hdw]; exact hpair) (by rw [hdw]; exact notPre)
  refine ⟨hlen, ?_⟩
  rw [List.takeD_eq_take _ hlen, htake]
  decide

/-- U7a's library lemma, in the seam's shape (amendment A11: the Pair-silence
hypothesis `hsilent`, discharged in composition). -/
theorem lib_rejects_pair {pair : Adr}
    (hsilent : NoStaticAnswer UniswapV2Pair.code 0x1626ba7e) : LibRejects pair :=
  rejects_of_raw (F := CoveredFork)
    (fun run code fork hcode notPre =>
      Usdc.lib_rejects_pair run code fork hcode notPre hsilent)

/-- The historical raw rejection theorem, in the same fresh-frame seam shape. -/
theorem lib_rejects_pairH {pair : Adr}
    (hsilent : NoStaticAnswerH UniswapV2Pair.code 0x1626ba7e) : LibRejectsH pair :=
  rejects_of_raw (F := NeutralFork)
    (fun run code fork hcode notPre =>
      Usdc.lib_rejects_pairH run code fork hcode notPre hsilent)

end LibSeam

end Blanc.Lift.Usdc
