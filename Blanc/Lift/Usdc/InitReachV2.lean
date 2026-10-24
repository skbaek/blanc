import Blanc.Lift.Usdc.InitReach
import Blanc.Lift.Usdc.ImplV2.Cert

/-!
# FiatTokenV2's initializers on a prefix reach

Shape equations (`rfl`) placing the V2 code's trees at the shared shapes of
`Blanc/Lift/Usdc/InitReach.lean` and `Blanc/Lift/ReachSolcStringStore.lean`, and the walks
from entry `0`: every `SSTORE` a V2 frame reaches under `initializeV2` writes a key of
`KeysInitV2` or zero, whatever the frame's outcome (`initV2_reach`).
-/

namespace Blanc.Lift.Usdc.InitReachV2

open Jaune Blanc Blanc.Lift

/-- The `string storage = string calldata` helper (entry `68`). -/
def τ : StrTags := ⟨(0x54, 0xa4), (0x54, 0x35), (0x54, 0xb6), (0x54, 0x41), (0x54, 0xd1),
  (0x54, 0xd2), 8, 86, 64, 82⟩

theorem helper_eq : ImplV2.cert.prog[68]? = some (StrStoreCd.helper τ) := rfl

theorem entries : StrStoreCd.Entries τ ImplV2.cert.prog := ⟨rfl, rfl, rfl, rfl⟩

/-- The `initializeV2(string)` wrapper (entry `106`). -/
def ω : CdWrapTags := ⟨(0x04, 0x70), (0x0c, 0x3a), (0x0c, 0x55), (0x0c, 0x67), (0x0c, 0x89),
  (0x35, 0xf6), 18⟩

theorem wrap_eq : ImplV2.cert.prog[106]? = some (CdStrWrap.wrapper ω) := rfl

/-- The shared part of `initializeV2`'s body. -/
def ν : V2Tags := ⟨(0x36, 0x5e), (0x54, 0x45), (0x36, 0xd3), (0x49, 0x04), 68, 69⟩

theorem tail_eq : ImplV2.t_3652_c18 = InitV2Tail.tree ν := rfl

/-- The domain-separator helper (entry `69`) holds no `SSTORE`. -/
theorem free69 : SstoreFreeSet ImplV2.cert.prog [69] = true := by decide

/-- The dispatcher's comparison tree. -/
def selTree : SFunc :=
  .next (.reg (.dup 0)) (.next (.push [0x8a, 0x6d, 0xb9, 0xc3] (by decide)) (.next (.reg .gt)
    (.next (.push [0x01, 0xbd] (by decide)) (.branch ImplV2.t_002b_c0 ImplV2.t_01bd_c0))))

theorem root_eq : ImplV2.t_0000_c0 = dispatch06 (0x00, 0x10) (0x03, 0x4c) selTree := rfl

theorem route_initV2 : selTree.selWalk 0xd608ea64 =
    .inl (Bytes.toB256 [0xd6, 0x08, 0xea, 0x64], 106) := by
  decide +kernel

variable {P : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {T : Conf}

theorem body_reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {b : Devm} {r : B256} {S : List B256} {M : Mem} {G : Nat}
    (bound : 36 + CdStrWrap.cdOff sevm + CdStrWrap.cdLen sevm + 32 ≤ 2 ^ 256)
    (run : Reach P ImplV2.cert.prog sevm ⟨St b ((CdStrWrap.cdLen sevm).toB256 ::
      (36 + CdStrWrap.cdOff sevm).toB256 :: r :: S) M G, ImplV2.t_35f6_c18, []⟩ T)
    (hT : AtSstore T) : InitStore (KeysInitV2 sevm) T := by
  unfold ImplV2.t_35f6_c18 at run
  rsd
  rsx
  rsload
  iterate 4 rsx
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide) (fun _ h => by cases h)).elim
  rw [tail_eq] at run
  exact InitV2Tail.reach erase entries helper_eq free69 (List.mem_singleton.mpr rfl) rfl bound
    run hT

/-- **V2 `initializeV2` on a prefix reach.** A reach of the V2 code from entry `0`, with empty
stack and the `initializeV2` selector, to an `SSTORE` stops at a write of `KeysInitV2` or of
zero. -/
theorem initV2_reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (sel : selWord sevm = 0xd608ea64) {d : Devm} {M : Mem} {G : Nat}
    (run : Reach P ImplV2.cert.prog sevm ⟨St d [] M G, ImplV2.t_0000_c0, []⟩ T)
    (hT : AtSstore T) : InitStore (KeysInitV2 sevm) T := by
  rw [root_eq] at run
  obtain ⟨g, b, M', G', hg, run⟩ := dispatch06_reach erase sel route_initV2 run hT
  rw [wrap_eq] at hg
  cases hg
  obtain ⟨b', M'', G'', T', inside, hT', rfl, lenB, offB⟩ :=
    CdStrWrap.reach erase (show ImplV2.cert.prog[18]? = some ImplV2.t_35f6_c18 from rfl) run hT
  have small : 36 + CdStrWrap.cdOff sevm + CdStrWrap.cdLen sevm + 32 ≤ 2 ^ 34 := by omega
  exact InitStore.below.mpr (body_reach erase
    (small.trans (Nat.pow_le_pow_right (by decide) (by decide))) inside hT')

end Blanc.Lift.Usdc.InitReachV2
