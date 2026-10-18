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

namespace LibSeam

/-- U7a's library lemma, in the seam's shape (amendment A11: the Pair-silence
hypothesis `hsilent`, discharged in composition). -/
theorem lib_rejects_pair {pair : Adr}
    (hsilent : NoStaticAnswer UniswapV2Pair.code 0x1626ba7e) : LibRejects pair := by
  intro sevm pre post run code fork hmem hstack hword hpair notPre
  have hdw : (Sevm.dataWord sevm 4).toAdr = pair := by
    rw [Sevm.dataWord, show (4 : B256).toNat = 4 from rfl, hword, toAdr_toB256]
  rw [St.self hstack hmem] at run
  obtain ⟨hlen, htake⟩ := Usdc.lib_rejects_pair run code fork
    (by rw [hdw]; exact hpair) (by rw [hdw]; exact notPre) hsilent
  refine ⟨hlen, ?_⟩
  rw [List.takeD_eq_take _ hlen, htake]
  decide

end LibSeam

end Blanc.Lift.Usdc
