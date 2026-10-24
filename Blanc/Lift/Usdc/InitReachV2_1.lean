import Blanc.Lift.Usdc.InitReach
import Blanc.Lift.Usdc.ImplV2_1.Cert

/-!
# FiatTokenV2_1's `initializeV2` on a prefix reach

Shape equations (`rfl`) placing the FiatTokenV2_1 code's trees at the shared shapes of
`Blanc/Lift/Usdc/InitReach.lean` and `Blanc/Lift/ReachSolcStringStore.lean`, and the walk
from entry `0`: every `SSTORE` a FiatTokenV2_1 frame reaches under `initializeV2` writes a key of
`KeysInitV2` or zero, whatever the frame's outcome (`initV2_reach`).
-/

namespace Blanc.Lift.Usdc.InitReachV2_1

open Jaune Blanc Blanc.Lift

/-- The `string storage = string calldata` helper (entry `64`). -/
def τ : StrTags := ⟨(0x4e, 0x2d), (0x4d, 0xbe), (0x4e, 0x3f), (0x4d, 0xca), (0x4e, 0x5a),
  (0x4e, 0x5b), 9, 80, 66, 81⟩

theorem helper_eq : ImplV2_1.cert.prog[64]? = some (StrStoreCd.helper τ) := rfl

theorem entries : StrStoreCd.Entries τ ImplV2_1.cert.prog := ⟨rfl, rfl, rfl, rfl⟩

/-- The `initializeV2(string)` wrapper (entry `104`). -/
def ω : CdWrapTags := ⟨(0x04, 0x52), (0x0b, 0x77), (0x0b, 0x92), (0x0b, 0xa4), (0x0b, 0xc6),
  (0x32, 0x38), 19⟩

theorem wrap_eq : ImplV2_1.cert.prog[104]? = some (CdStrWrap.wrapper ω) := rfl

/-- The shared part of `initializeV2`'s body. -/
def ν : V2Tags := ⟨(0x32, 0x7a), (0x4d, 0xce), (0x32, 0xef), (0x42, 0xb5), 64, 65⟩

/-- The domain-separator helper holds no `SSTORE`. -/
theorem freeDom : SstoreFreeSet ImplV2_1.cert.prog [65] = true := by decide

theorem body_eq : ImplV2_1.cert.prog[19]? = some (InitV2Check.body (0x32, 0x65) (0x32, 0x6e) 5
    (InitV2Tail.tree ν)) := rfl

theorem join_eq : ImplV2_1.cert.prog[5]? = some (InitV2Check.join (0x32, 0x6e) (InitV2Tail.tree ν)) := rfl

/-- The dispatcher's comparison tree. -/
def selTree : SFunc :=
  .next (.reg (.dup 0)) (.next (.push [0x7f, 0x2e, 0xec, 0xc3] (by decide)) (.next (.reg .gt)
    (.next (.push [0x01, 0xb2] (by decide)) (.branch ImplV2_1.t_002b_c0 ImplV2_1.t_01b2_c0))))

theorem root_eq : ImplV2_1.t_0000_c0 = dispatch06 (0x00, 0x10) (0x03, 0x36) selTree := rfl

theorem route_initV2 : selTree.selWalk 0xd608ea64 =
    .inl (Bytes.toB256 [0xd6, 0x08, 0xea, 0x64], 104) := by
  decide +kernel

variable {P : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {T : Conf}

/-- **FiatTokenV2_1 `initializeV2` on a prefix reach.** A reach of the FiatTokenV2_1 code from entry `0`, with
empty stack and the `initializeV2` selector, to an `SSTORE` stops at a write of `KeysInitV2`
or of zero. -/
theorem initV2_reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (sel : selWord sevm = 0xd608ea64) {d : Devm} {M : Mem} {G : Nat}
    (run : Reach P ImplV2_1.cert.prog sevm ⟨St d [] M G, ImplV2_1.t_0000_c0, []⟩ T)
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

end Blanc.Lift.Usdc.InitReachV2_1
