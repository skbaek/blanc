import Blanc.GasErasure
import Blanc.Lift.RunEx
import Blanc.Lift.StaticCall
import Blanc.Lift.MutableCallPost

/-!
# Exact, gas-stable profiles for one external call

The debit and canonical successor are supplied before the call's input gas. The successor is
stable on every machine column except execution gas, including returndata and later-priced world
state. `U` is an admission threshold and debit bound; it is not itself a consumed charge.

This interface describes one instruction and its callee. It assumes no execution or cost of the
caller continuation. The continuation helpers retain both the debit equation and the canonical
successor, so an exact caller walk can price its later operations at a gas-independent world.
-/

namespace Blanc.Lift

open Jaune

/-- One call's independently supplied charge and gas-stable successor. -/
structure ExactCallProfile (sevm : Sevm) (op : Ninst)
    (entry : Devm → List B256 → Mem → Nat → Devm)
    (Ready : Devm → List B256 → Mem → Nat → Prop)
    (After : Devm → List B256 → Mem → Devm → Prop) (U : Nat)
    (debit : Devm → List B256 → Mem → Nat)
    (next : Devm → List B256 → Mem → Devm) : Prop where
  entry_gas : ∀ b S M G, (entry b S M G).gasLeft = G
  congr : ∀ {b b'} S M, Devm.EqModGas b b' →
    debit b S M = debit b' S M ∧ Devm.EqModGas (next b S M) (next b' S M)
  sound : ∀ b S M G, Ready b S M G → debit b S M ≤ U ∧ ∃ d,
    Ninst.RunCompiled sevm (entry b S M G) op d ∧
    G = d.gasLeft + debit b S M ∧ Devm.EqModGas d (next b S M) ∧ After b S M d

namespace ExactCallProfile

variable {sevm : Sevm} {op : Ninst}
  {entry : Devm → List B256 → Mem → Nat → Devm}
  {Ready : Devm → List B256 → Mem → Nat → Prop}
  {After : Devm → List B256 → Mem → Devm → Prop} {U : Nat}
  {debit : Devm → List B256 → Mem → Nat} {next : Devm → List B256 → Mem → Devm}
  {fs : List SFunc} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {f : SFunc}

/-- Prepend the call, retaining its exact debit and canonical successor for a fixed outcome. -/
theorem runExact (hp : ExactCallProfile sevm op entry Ready After U debit next)
    (hready : Ready b S M G) {r : Outcome}
    (k : ∀ d, After b S M d → G = d.gasLeft + debit b S M →
      Devm.EqModGas d (next b S M) → SFunc.RunExact fs sevm d f r) :
    SFunc.RunExact fs sevm (entry b S M G) (.next op f) r := by
  obtain ⟨_, d, hrun, hgas, hnext, hafter⟩ := hp.sound b S M G hready
  exact .next hrun (k d hafter hgas hnext)

/-- Prepend the call to a continuation whose eventual outcome may depend on the reply. -/
theorem runEx (hp : ExactCallProfile sevm op entry Ready After U debit next)
    (hready : Ready b S M G) {Q : Outcome → Prop}
    (k : ∀ d, After b S M d → G = d.gasLeft + debit b S M →
      Devm.EqModGas d (next b S M) → SFunc.RunEx fs sevm d f Q) :
    SFunc.RunEx fs sevm (entry b S M G) (.next op f) Q := by
  obtain ⟨_, d, hrun, hgas, hnext, hafter⟩ := hp.sound b S M G hready
  obtain ⟨r, hr, hq⟩ := k d hafter hgas hnext
  exact ⟨r, .next hrun hr, hq⟩

/-- Residual form: entering with `R + debit` leaves exactly `R` for the continuation.
Headroom remains an independent `Ready` obligation. -/
theorem runExact_residual (hp : ExactCallProfile sevm op entry Ready After U debit next)
    {R : Nat} (hready : Ready b S M (R + debit b S M)) {r : Outcome}
    (k : ∀ d, After b S M d → d.gasLeft = R →
      Devm.EqModGas d (next b S M) → SFunc.RunExact fs sevm d f r) :
    SFunc.RunExact fs sevm (entry b S M (R + debit b S M)) (.next op f) r := by
  apply hp.runExact hready
  intro d hafter hgas hnext
  exact k d hafter (by omega) hnext

end ExactCallProfile

/-- An all-gas `STATICCALL` entry at the given input and output windows. -/
def allGasStaticCallEntry (t ii is oi os : B256) (b : Devm) (S : List B256) (M : Mem)
    (G : Nat) : Devm :=
  St b (Nat.toB256 G :: t :: ii :: is :: oi :: os :: S) M G

/-- An all-gas, zero-value `CALL` entry at the given input and output windows. -/
def allGasZeroCallEntry (t ii is oi os : B256) (b : Devm) (S : List B256) (M : Mem)
    (G : Nat) : Devm :=
  St b (Nat.toB256 G :: t :: 0 :: ii :: is :: oi :: os :: S) M G

/-- Admission for one call window, including the room needed for its result flag. -/
def CallWindowReady (W : Devm → Prop) (data : Bytes) (U : Nat) (ii is : B256)
    (b : Devm) (S : List B256) (M : Mem) (G : Nat) : Prop :=
  W b ∧ U ≤ G ∧ G < 2 ^ 256 ∧ (M.read ii.toNat is.toNat).1 = data ∧ S.length < 1024

/-- A static word reply with a fixed debit and canonical successor, at one call window. -/
def StaticWordCallProfile (sevm : Sevm) (W W' : Devm → Prop) (t : B256) (data : Bytes)
    (A : B256) (U : Nat) (ii is oi : B256)
    (debit : Devm → List B256 → Mem → Nat) (next : Devm → List B256 → Mem → Devm) : Prop :=
  ExactCallProfile sevm (.exec .staticcall) (allGasStaticCallEntry t ii is oi 0x20)
    (CallWindowReady W data U ii is)
    (fun b S M d => ∃ out, StaticCallPost b d S M ii is oi 0x20 1 out ∧
      32 ≤ out.length ∧ out.length < 2 ^ 256 ∧ Bytes.toB256 (out.take 32) = A ∧
      W' d ∧ (IdReady sevm b → IdReady sevm d)) U debit next

/-- A successful zero-value mutable call with a fixed debit and canonical successor.
The owner account's storage is preserved; the callee may change the external world. -/
def MutableCallProfile (sevm : Sevm) (W W' : Devm → Prop) (t : B256) (data : Bytes)
    (ok : Bytes → Prop) (U : Nat) (ii is oi : B256)
    (debit : Devm → List B256 → Mem → Nat) (next : Devm → List B256 → Mem → Devm) : Prop :=
  ExactCallProfile sevm (.exec .call) (allGasZeroCallEntry t ii is oi 0x20)
    (CallWindowReady W data U ii is)
    (fun b S M d => MutableCallPost b d S M ii is oi 0x20 1 ∧ ok d.returnData ∧
      d.returnData.length < 2 ^ 256 ∧
      d.getStor sevm.currentTarget = b.getStor sevm.currentTarget ∧ W' d ∧
      (IdReady sevm b → IdReady sevm d)) U debit next

end Blanc.Lift
