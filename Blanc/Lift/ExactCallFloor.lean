import Blanc.Lift.ExactCallProfile
import Blanc.Lift.StaticGasTransport

/-!
# Exact call profiles at a call's true floor

`ExactCallProfile` is parametric in its admission `Ready`. `CallWindowReady` admits a call on one constant
`U ≤ G`, which charges every call the worst case of every world. `FloorReady` admits it on what the call
actually leaves: `debit b S M + K ≤ G`, that is, at least `K` gas after the call has been paid for. A caller
knows its own continuation's cost, so it can discharge this at the site, however small the gas it was given.

`U` keeps its reading, a bound on the debit; here it admits nothing.
-/

namespace Blanc.Lift

open Jaune

/-- Admission at the floor: the call leaves at least `K`. -/
def FloorReady (W : Devm → Prop) (data : Bytes) (K : Nat) (debit : Devm → List B256 → Mem → Nat)
    (ii is : B256) (b : Devm) (S : List B256) (M : Mem) (G : Nat) : Prop :=
  W b ∧ debit b S M + K ≤ G ∧ G < 2 ^ 256 ∧ (M.read ii.toNat is.toNat).1 = data ∧ S.length < 1024

/-- `StaticWordCallProfile` admitted at the floor. -/
def StaticWordFloorProfile (sevm : Sevm) (W W' : Devm → Prop) (t : B256) (data : Bytes) (A : B256)
    (U K : Nat) (ii is oi : B256) (debit : Devm → List B256 → Mem → Nat)
    (next : Devm → List B256 → Mem → Devm) : Prop :=
  ExactCallProfile sevm (.exec .staticcall) (allGasStaticCallEntry t ii is oi 0x20)
    (FloorReady W data K debit ii is)
    (fun b S M d => ∃ out, StaticCallPost b d S M ii is oi 0x20 1 out ∧
      32 ≤ out.length ∧ out.length < 2 ^ 256 ∧ Bytes.toB256 (out.take 32) = A ∧
      W' d ∧ (IdReady sevm b → IdReady sevm d)) U debit next

/-- `MutableCallProfile` admitted at the floor. -/
def MutableFloorProfile (sevm : Sevm) (W W' : Devm → Prop) (t : B256) (data : Bytes)
    (ok : Bytes → Prop) (U K : Nat) (ii is oi : B256) (debit : Devm → List B256 → Mem → Nat)
    (next : Devm → List B256 → Mem → Devm) : Prop :=
  ExactCallProfile sevm (.exec .call) (allGasZeroCallEntry t ii is oi 0x20)
    (FloorReady W data K debit ii is)
    (fun b S M d => MutableCallPost b d S M ii is oi 0x20 1 ∧ ok d.returnData ∧
      d.returnData.length < 2 ^ 256 ∧
      d.getStor sevm.currentTarget = b.getStor sevm.currentTarget ∧ W' d ∧
      (IdReady sevm b → IdReady sevm d)) U debit next

/-- Retain a static floor profile's functions across the static initial gas. -/
theorem StaticWordFloorProfile.withStaticGas {s : Sevm} {W W' : Devm → Prop} {t A : B256} {data : Bytes}
    {U K : Nat} {ii is oi : B256} {debit : Devm → List B256 → Mem → Nat}
    {next : Devm → List B256 → Mem → Devm}
    (h : StaticWordFloorProfile s W W' t data A U K ii is oi debit next) (F : Nat) :
    StaticWordFloorProfile {s with gas := F} W W' t data A U K ii is oi debit next := by
  refine ⟨h.entry_gas, h.congr, ?_⟩
  intro b S M G hready
  obtain ⟨hc, d, hrun, hgas, hnext, out, hpost, hlen, hlt, hA, hW', hid⟩ := h.sound b S M G hready
  exact ⟨hc, d, ninstRunCompiled_withStaticGas hrun F, hgas, hnext, out, hpost, hlen, hlt, hA, hW',
    fun hb => (hid (hb.withStaticGas s.gas)).withStaticGas F⟩

/-- Retain a mutable floor profile's functions across the static initial gas. -/
theorem MutableFloorProfile.withStaticGas {s : Sevm} {W W' : Devm → Prop} {t : B256} {data : Bytes}
    {ok : Bytes → Prop} {U K : Nat} {ii is oi : B256} {debit : Devm → List B256 → Mem → Nat}
    {next : Devm → List B256 → Mem → Devm}
    (h : MutableFloorProfile s W W' t data ok U K ii is oi debit next) (F : Nat) :
    MutableFloorProfile {s with gas := F} W W' t data ok U K ii is oi debit next := by
  refine ⟨h.entry_gas, h.congr, ?_⟩
  intro b S M G hready
  obtain ⟨hc, d, hrun, hgas, hnext, hpost, hok, hlt, hstor, hW', hid⟩ := h.sound b S M G hready
  exact ⟨hc, d, ninstRunCompiled_withStaticGas hrun F, hgas, hnext, hpost, hok, hlt, hstor, hW',
    fun hb => (hid (hb.withStaticGas s.gas)).withStaticGas F⟩

end Blanc.Lift
