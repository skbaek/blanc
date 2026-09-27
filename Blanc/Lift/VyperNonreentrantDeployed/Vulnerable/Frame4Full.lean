import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame4ChunkA
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame4ChunkB

/-!
V- witness, frame 4 whole (the reentrant `add_liquidity`, 4,505 steps from its real spawn,
halting by `RETURN` with the EELS gas and return data, no error, and the shadows
`keys4`/`adrs4`/`storA`/`acsA`), from its two kernel chunks: the first chunk reaches the boundary
configuration (its machine and shadows as `chunkA` states them), which is `cfgB` at that
configuration's own world and bookkeeping, and the second chunk runs from there over any
world and bookkeeping (`chunkB`).
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree

open Jaune Blanc.Lift Blanc.Lift.Witness
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1

/-- A configuration with the first chunk's observation is `cfgB` at its own world and
bookkeeping. -/
theorem cfgB_of_obsB {c : Cfg} (h : obsB (.cont c) = obsBEELS) :
    c = cfgB c.devm.meta c.devm.world := by
  rcases c with ⟨⟨mach, m, w⟩, f, K, keys, adrs, stor, acs⟩
  simp only [obsB, obsBEELS, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hm, hf, hK, hk, ha, hs, hc, hrc, ho, hrd, he⟩ := h
  subst hm hf hK hk ha hs hc
  rcases m with ⟨_, _, _, _, _, _, _, _, _, _, _⟩
  simp only [Devm.refundCounter, Devm.output, Devm.returnData, Devm.error] at hrc ho hrd he
  subst hrc ho hrd he
  rfl

/-- **Frame 4 whole, from the chunks.** -/
theorem frame4_kernel : obs4 r4 = obs4EELS := by
  have hA := chunkA
  unfold r4
  rw [show (4505 : Nat) = 2625 + 1880 from rfl, wrun_add]
  generalize wrun fs1 e4.sta 2625 c4 = r at hA ⊢
  rcases r with c | _ | _
  · rw [cfgB_of_obsB hA]
    exact chunkB _ _
  · simp [obsB, obsBEELS] at hA
  · simp [obsB, obsBEELS] at hA

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree
