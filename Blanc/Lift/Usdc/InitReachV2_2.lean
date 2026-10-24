import Blanc.Lift.Usdc.InitReach
import Blanc.Lift.Usdc.Impl.Cert

/-!
# FiatTokenV2_2's `initializeV2` on a prefix reach

Shape equations (`rfl`) placing the FiatTokenV2_2 code's trees at the shared shapes of
`Blanc/Lift/Usdc/InitReach.lean` and `Blanc/Lift/ReachSolcStringStore.lean`, and the walk
from entry `0`: every `SSTORE` a FiatTokenV2_2 frame reaches under `initializeV2` writes a key of
`KeysInitV2` or zero, whatever the frame's outcome (`initV2_reach`).
-/

namespace Blanc.Lift.Usdc.InitReachV2_2

open Jaune Blanc Blanc.Lift

/-- The `string storage = string calldata` helper (entry `74`). -/
def τ : StrTags := ⟨(0x55, 0xaa), (0x55, 0x3b), (0x55, 0xbc), (0x55, 0x47), (0x55, 0xd7),
  (0x55, 0xd8), 14, 105, 82, 108⟩

theorem helper_eq : Impl.cert.prog[74]? = some (StrStoreCd.helper τ) := rfl

theorem entries : StrStoreCd.Entries τ Impl.cert.prog := ⟨rfl, rfl, rfl, rfl⟩

/-- The `initializeV2(string)` wrapper (entry `133`). -/
def ω : CdWrapTags := ⟨(0x04, 0x89), (0x0f, 0xd8), (0x0f, 0xf3), (0x10, 0x05), (0x10, 0x27),
  (0x37, 0x44), 25⟩

theorem wrap_eq : Impl.cert.prog[133]? = some (CdStrWrap.wrapper ω) := rfl

/-- The shared part of `initializeV2`'s body. -/
def ν : V2Tags := ⟨(0x37, 0x86), (0x55, 0x4b), (0x37, 0xfb), (0x4c, 0x29), 74, 75⟩

/-- The domain-separator helper holds no `SSTORE`. -/
theorem freeDom : SstoreFreeSet Impl.cert.prog [75, 77] = true := by decide

theorem body_eq : Impl.cert.prog[25]? = some (InitV2Check.body (0x37, 0x71) (0x37, 0x7a) 5
    (InitV2Tail.tree ν)) := rfl

theorem join_eq : Impl.cert.prog[5]? = some (InitV2Check.join (0x37, 0x7a) (InitV2Tail.tree ν)) := rfl

/-- The dispatcher's comparison tree. -/
def selTree : SFunc :=
  .next (.reg (.dup 0)) (.next (.push [0x84, 0x56, 0xcb, 0x59] (by decide)) (.next (.reg .gt)
    (.next (.push [0x01, 0xd3] (by decide)) (.branch Impl.t_002b_c0 Impl.t_01d3_c0))))

theorem root_eq : Impl.t_0000_c0 = dispatch06 (0x00, 0x10) (0x03, 0x6d) selTree := rfl

theorem route_initV2 : selTree.selWalk 0xd608ea64 =
    .inl (Bytes.toB256 [0xd6, 0x08, 0xea, 0x64], 133) := by
  decide +kernel

variable {P : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {T : Conf}

/-- **FiatTokenV2_2 `initializeV2` on a prefix reach.** A reach of the FiatTokenV2_2 code from entry `0`, with
empty stack and the `initializeV2` selector, to an `SSTORE` stops at a write of `KeysInitV2`
or of zero. -/
theorem initV2_reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (sel : selWord sevm = 0xd608ea64) {d : Devm} {M : Mem} {G : Nat}
    (run : Reach P Impl.cert.prog sevm ⟨St d [] M G, Impl.t_0000_c0, []⟩ T)
    (hT : AtSstore T) : InitStore (KeysInitV2 sevm) T := by
  rw [root_eq] at run
  obtain ⟨g, b, M', G', hg, run⟩ := dispatch06_reach erase sel route_initV2 run hT
  rw [wrap_eq] at hg
  cases hg
  obtain ⟨b', M'', G'', T', inside, hT', rfl, lenB, offB⟩ :=
    CdStrWrap.reach erase body_eq run hT
  have small : 36 + CdStrWrap.cdOff sevm + CdStrWrap.cdLen sevm + 32 ≤ 2 ^ 34 := by omega
  have bound : 36 + CdStrWrap.cdOff sevm + CdStrWrap.cdLen sevm + 32 ≤ 2 ^ 256 :=
    small.trans (Nat.pow_le_pow_right (by decide) (by decide))
  refine InitStore.below.mpr (InitV2Check.reach erase join_eq ?_ inside hT')
  intro d' M₁ G₁ tail
  exact InitV2Tail.reach erase entries helper_eq freeDom (by decide) rfl bound tail hT'

end Blanc.Lift.Usdc.InitReachV2_2
