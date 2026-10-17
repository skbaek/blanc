import Blanc.Composition.UniswapV2PairWeth9LegsSync
import Blanc.Lift.UniswapV2Pair.MintForwardAccept

/-!
# C4(b): WETH9's account across the Pair's own steps (U8d)

The WETH9 legs of a C4(b) row are stated at the world the Pair stages each call over; the history
supplies WETH9's code and the Pair's words at the frame's pre-state.  This module carries them:

* `runCompiled_codePreserve` — any compiled step, child included, keeps every nonempty code;
* `WethKeeps w pre post` — `post` has `pre`'s code and storage at `w`, closed under the Pair's own
  `SLOAD`/`SSTORE` (at a target other than `w`), logs, machine and access-set updates, and under a
  compiled `STATICCALL` (which writes no storage).
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair

/-- **A compiled step keeps every nonempty code**, the child's run included. -/
theorem runCompiled_codePreserve {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (run : Ninst.RunCompiled sevm pre n post) : Devm.CodePreserve pre post := by
  obtain ⟨xl, filled, step⟩ := run
  exact Ninst.effect_of_effectRec codePreserve_refl_trans.1 codePreserve_refl_trans.2
    Ninst.codePreserve_effectRec Jinst.codePreserve_effect Linst.codePreserve_effect n
    ⟨xl, filled, 0, step 0⟩

/-- `post` has `pre`'s code and storage at `w`. -/
def WethKeeps (w : Adr) (pre post : Devm) : Prop :=
  post.getCode w = pre.getCode w ∧ post.getStor w = pre.getStor w

namespace WethKeeps

variable {w : Adr}

theorem refl (d : Devm) : WethKeeps w d d := ⟨rfl, rfl⟩

theorem trans {a b c : Devm} (h : WethKeeps w a b) (h' : WethKeeps w b c) : WethKeeps w a c :=
  ⟨h'.1.trans h.1, h'.2.trans h.2⟩

theorem getStorVal {a b : Devm} (h : WethKeeps w a b) (k : B256) :
    b.getStorVal w k = a.getStorVal w k := by
  change (b.getStor w).get k = (a.getStor w).get k
  rw [h.2]

theorem afterSload (sevm : Sevm) (b : Devm) (k : B256) :
    WethKeeps w b (Blanc.afterSload sevm b k) :=
  ⟨afterSload_getCode sevm b k w, afterSload_getStor sevm b k w⟩

theorem afterSstore {sevm : Sevm} (ne : sevm.currentTarget ≠ w) (b : Devm) (k v : B256) :
    WethKeeps w b (Blanc.afterSstore sevm b k v) :=
  ⟨afterSstore_getCode sevm b k v w, afterSstore_getStor_ne sevm b k v w ne⟩

theorem addLog (b : Devm) (l : Log) : WethKeeps w b (b.addLog l) := ⟨rfl, rfl⟩

theorem ofSt (b : Devm) (S : List B256) (M : Mem) (g : Nat) :
    WethKeeps w b (St b S M g) := ⟨rfl, rfl⟩

theorem access (b : Devm) (a : Adr) : WethKeeps w b (temporalAccountAccessBase b a) := by
  unfold temporalAccountAccessBase
  split
  · exact refl b
  · exact ⟨rfl, rfl⟩

/-- A compiled `STATICCALL` writes no storage and keeps WETH9's nonempty code. -/
theorem staticcall {sevm : Sevm} {b d : Devm} {S : List B256} {M : Mem} {G : Nat}
    {g t ii is oi os : B256} (fork : CoveredFork sevm.benvStat.fork)
    (call : Ninst.RunCompiled sevm (St b (g :: t :: ii :: is :: oi :: os :: S) M G)
      (.exec .staticcall) d)
    (nonempty : (b.getCode w).toList ≠ []) : WethKeeps w b d :=
  ⟨runCompiled_codePreserve call w nonempty, compiled_staticcall_stor fork call w⟩

end WethKeeps

theorem temporalAccountAccessBase_getStor (b : Devm) (a x : Adr) :
    Devm.getStor (temporalAccountAccessBase b a) x = Devm.getStor b x :=
  (WethKeeps.access (w := x) b a).2

theorem weth9_code_toList_ne {d : Devm} {a : Adr} (h : d.getCode a = Weth9.code) :
    (d.getCode a).toList ≠ [] := by
  rw [h]
  exact Weth9.weth9Sem.ne_nil rfl

end Blanc.Composition.UniswapV2PairWeth9Joint
