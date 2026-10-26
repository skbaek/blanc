import Blanc.Lift.SolcStoragePayload
import Blanc.Lift.SolcStorageClear
import Blanc.Lift.Sound
import Blanc.Lift.Usdc.ImplV1.Cert

/-!
# Actual V1 `initialize` memory-payload instantiation (component)

Concrete leaf over the shared template in `Blanc.Lift.SolcStoragePayload`.
Actual source (verified by native read of `Blanc/Lift/Usdc/ImplV1/Cert.lean`):

* head `t_2edd_c52` at `k = 52`, `back = [0x2e, 0xdd]`, `exit = [0x2e, 0xf8]`:
  `dest; dup2; dup1; gt; iszero; push exit; branch body tail`;
* body `t_2ee6_c52`: `dup2; mload; dup2; sstore; swap1; push [0x20]; add;
  swap1; swap0; push [0x01]; add; swap0; push back; jump 52`;
* exit `t_2ef8_c52 = dest t_2ef9_c7`;
* tail `t_2ef9_c7`: `dest; pop; swap0; pop; push [0x2f, 0x06]; swap1; swap0;
  push [0x2f, 0x0a]; callNext 42` with continuation
  `t_2f06_c7 = dest; pop; swap0; ret`.

Proved in this leaf (no premises invented):

* real tail `RunCutP` exit certificate over the seven-instruction prefix
  before `callNext 42`, reusing accepted
  `SolcStorageClear.legacyRunP_zeroStores_noExec` (same-`P` erasure) on
  `head 50` / return `51` with helper `42`'s three-instruction prefix;
* public head-`52` `RunP (PotStep (StepIn R))` strengthening with original
  same-`P` plus bounded-key-or-zero/no-`exec` observations, with `count`
  from the exact `fin`/`p` and stack `fin :: base :: p.toB256 :: rest`;
* corollary lifting an original `StepIn` run via existing
  `FreePtr.SFunc.RunP.withPot` (actual initial `Pot`, `stateGas = none`) and
  projecting back to `StepIn`.

Scope limits (stated, not assumed away): `base` is arbitrary (no hash
assumption; exact hash producer belongs to the next unit); the actual
wrapper / init-profile / history producer is explicitly open.
-/

namespace Blanc.Lift.Usdc.OldInitializerV1Payload

open Jaune Blanc Blanc.Lift
open SolcStoragePayload
open ImplV1

/-- Actual loop table index of the V1 payload head. -/
def k52 : Nat := 52

/-- Actual back-edge bytes of the V1 payload loop. -/
def back52 : Bytes := [0x2e, 0xdd]

/-- Actual exit bytes of the V1 payload loop. -/
def exit52 : Bytes := [0x2e, 0xf8]

/-- Table entry 52 is the shared-template head over the actual bytes/tail:
`t_2edd_c52` is `dest; dup2; dup1; gt; iszero; push [0x2e, 0xf8];
branch t_2ee6_c52 t_2ef8_c52` and `t_2ee6_c52` is the template body. -/
theorem entry52 : (Cert.prog cert)[k52]?
    = some (head back52 exit52 (by decide) (by decide) k52 t_2ef8_c52) := by
  have h : (Cert.prog cert)[k52]? = some t_2edd_c52 := rfl
  rw [h]
  rfl

/-- Table entry 50 is the legacy zero-loop head: `t_2f10_c50` is
`dest; dup0; dup2; gt; iszero; push [0x2f, 0x28];
branch t_2f19_c50 t_2f28_c50`, i.e. `legacyHead` over back `[0x2f, 0x10]`
with exit through 51. -/
theorem entry50 : (Cert.prog cert)[50]?
    = some (SolcStorageClear.legacyHead [0x2f, 0x10] [0x2f, 0x28]
      (by decide) (by decide) 50 51) := by
  have h : (Cert.prog cert)[50]? = some t_2f10_c50 := rfl
  rw [h]
  rfl

/-- Table entry 51 is the shared legacy return: `t_2f2c_c51` is
`dest; swap0; ret`. -/
theorem retEntry51 : (Cert.prog cert)[51]? = some SolcStorageClear.legacyRet := by
  have h : (Cert.prog cert)[51]? = some t_2f2c_c51 := rfl
  rw [h]
  rfl

/-- Helper 42 executes only literal-zero stores and no external calls. Its
three-instruction prefix reaches a comparison head whose storing arm writes
`0` (`push [0x00]; dup1; push [0x00]; swap0; sstore`, value proved `0` from
the staged stack) and routes through table entries 50/51, closed by the
accepted legacy clearing run; its exit arm returns through entry 51. -/
theorem helper42_zeroStores
    {P : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s : Sevm} {d : Devm} {n : Ninst} {d' : Devm},
      P s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {pre : Devm} {out : Outcome}
    (run : SFunc.RunP P (Cert.prog cert) sevm pre t_2f0a_c42 out) :
    SFunc.RunP (fun s d n d' => P s d n d' ∧
      (n = .reg .sstore → ∀ key value rest, d.stack = key :: value :: rest → value = 0) ∧
      ∀ x, n ≠ .exec x)
      (Cert.prog cert) sevm pre t_2f0a_c42 out := by
  unfold t_2f0a_c42 at run ⊢
  cases run with
  | dest burn run =>
    refine SFunc.RunP.dest burn ?_
    cases run with
    | next push1 run =>
      refine SFunc.RunP.next ⟨push1, (by intro impossible; cases impossible),
        (by intro x impossible; cases impossible)⟩ ?_
      cases run with
      | next swap1 run =>
        refine SFunc.RunP.next ⟨swap1, (by intro impossible; cases impossible),
          (by intro x impossible; cases impossible)⟩ ?_
        cases run with
        | next swap0 run =>
          refine SFunc.RunP.next ⟨swap0, (by intro impossible; cases impossible),
            (by intro x impossible; cases impossible)⟩ ?_
          exact SolcStorageClear.legacyRunP_zeroStores_noExec
            erase entry50 retEntry51 (by decide) run

/-- The actual exit tail `t_2ef8_c52 = dest t_2ef9_c7` always finishes and
carries same-`P` bounded-key-or-zero/no-`exec` observations: seven prefix
instructions, the `callNext 42` callee (uncut `RunP`, closed by
`helper42_zeroStores` and weakened to the enriched shape), then the
`t_2f06_c7 = dest; pop; swap0; ret` continuation. -/
theorem exitCert52
    {R : Exec.Deriv} {sevm : Sevm} {fin base0 : B256} {p : Nat}
    {d : Devm} {sg : Seg}
    (run : SFunc.RunCutP (FreePtr.PotStep (StepIn R)) (Cert.prog cert) sevm
      [k52] d t_2ef8_c52 sg) :
    ∃ o, sg = Seg.done o ∧
      SFunc.RunP (Enriched (FreePtr.PotStep (StepIn R)) fin base0 p)
        (Cert.prog cert) sevm d t_2ef8_c52 o := by
  have erase : ∀ {s : Sevm} {d : Devm} {n : Ninst} {d' : Devm},
      FreePtr.PotStep (StepIn R) s d n d' → Ninst.Run s d n d' :=
    fun h => StepIn.toRun h.1
  have weak : ∀ {s d n d'},
      (fun s d n d' => FreePtr.PotStep (StepIn R) s d n d' ∧
        (n = .reg .sstore → ∀ key value rest,
          d.stack = key :: value :: rest → value = 0) ∧
        ∀ x, n ≠ .exec x) s d n d' →
      Enriched (FreePtr.PotStep (StepIn R)) fin base0 p s d n d' := by
    intro s d n d' h
    refine ⟨h.1, ?_, h.2.2⟩
    intro store key value rest stack
    exact Or.inl (h.2.1 store key value rest stack)
  cases sg with
  | «at» index middle =>
    unfold t_2ef8_c52 t_2ef9_c7 at run
    cases run with
    | dest burn run =>
      cases run with
      | dest burn2 run =>
        iterate 7
          obtain ⟨next, step, run⟩ := ric_nextP run
        cases run with
        | callRet dest lookup pop callee rest =>
          unfold t_2f06_c7 at rest
          cases rest with
          | dest burn rest =>
            iterate 2
              obtain ⟨next, step, rest⟩ := ric_nextP rest
            cases rest
  | done out =>
    refine ⟨out, rfl, ?_⟩
    unfold t_2ef8_c52 t_2ef9_c7 at run ⊢
    cases run with
    | dest burn run =>
      refine SFunc.RunP.dest burn ?_
      cases run with
      | dest burn2 run =>
        refine SFunc.RunP.dest burn2 ?_
        iterate 7
          obtain ⟨next, step, run⟩ := ric_nextP run
          refine SFunc.RunP.next ⟨step, (by intro impossible; cases impossible),
            (by intro x impossible; cases impossible)⟩ ?_
        cases run with
        | callHalt dest lookup pop callee =>
          rw [show (Cert.prog cert)[42]? = some t_2f0a_c42 from rfl] at lookup
          cases lookup
          exact SFunc.RunP.callHalt dest rfl pop
            (SFunc.RunP.mono weak (helper42_zeroStores erase callee))
        | callRet dest lookup pop callee rest =>
          rw [show (Cert.prog cert)[42]? = some t_2f0a_c42 from rfl] at lookup
          cases lookup
          refine SFunc.RunP.callRet dest rfl pop
            (SFunc.RunP.mono weak (helper42_zeroStores erase callee)) ?_
          unfold t_2f06_c7 at rest ⊢
          cases rest with
          | dest burn rest =>
            refine SFunc.RunP.dest burn ?_
            iterate 2
              obtain ⟨next, step, rest⟩ := ric_nextP rest
              refine SFunc.RunP.next ⟨step, (by intro impossible; cases impossible),
                (by intro x impossible; cases impossible)⟩ ?_
            cases rest with
            | ret dest pop =>
              exact SFunc.RunP.ret dest pop

/-- Actual head-52 `RunP (PotStep (StepIn R))` strengthening: same pre-state
and outcome, every store literal-zero or at a bounded modular payload key,
no external calls. `count` comes from the exact `fin`/`p`; `base` stays
arbitrary (no hash assumption). The exact hash/wrapper/init-profile/history
producer is explicitly outside this component. -/
theorem head52_strengthen
    {R : Exec.Deriv} {sevm : Sevm} {pre : Devm} {out : Outcome}
    {fin base : B256} {p : Nat} {rest : List B256}
    (hstack : pre.stack = fin :: base :: p.toB256 :: rest)
    (hp : p < 2 ^ 256)
    (run : SFunc.RunP (FreePtr.PotStep (StepIn R)) (Cert.prog cert) sevm pre
      t_2edd_c52 out) :
    SFunc.RunP (Enriched (FreePtr.PotStep (StepIn R)) fin base p)
      (Cert.prog cert) sevm pre t_2edd_c52 out := by
  have erase : ∀ {s : Sevm} {d : Devm} {n : Ninst} {d' : Devm},
      FreePtr.PotStep (StepIn R) s d n d' → Ninst.Run s d n d' :=
    fun h => StepIn.toRun h.1
  have eraseInner : ∀ {s : Sevm} {d : Devm} {n : Ninst} {d' : Devm},
      StepIn R s d n d' → Ninst.Run s d n d' :=
    fun h => StepIn.toRun h
  have h0 : Inv fin base p rest 0 pre := by
    refine ⟨Nat.zero_le _, by simpa only [Nat.mul_zero, Nat.add_zero] using hp, ?_⟩
    have zeroWord : (0 : Nat).toB256 = (0 : B256) := rfl
    simpa only [zeroWord, Nat.mul_zero, Nat.add_zero, B256.add_zero] using hstack
  exact runP_enriched (P := FreePtr.PotStep (StepIn R)) erase
    (readWindow_potStep (P := StepIn R) eraseInner) entry52
    exitCert52 h0 run

/-- Original `StepIn` corollary: from an actual `StepIn` run at bounded
potential (`stateGas = none`, initial `Pot`), the same head-52 run is
strengthened and projected back to the original `StepIn` relation with the
store observations. -/
theorem head52_stepIn
    {R : Exec.Deriv} {sevm : Sevm} {pre : Devm} {out : Outcome}
    {fin base : B256} {p : Nat} {rest : List B256}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hstack : pre.stack = fin :: base :: p.toB256 :: rest)
    (hp : p < 2 ^ 256) (pot : FreePtr.Pot pre)
    (run : SFunc.RunP (StepIn R) (Cert.prog cert) sevm pre
      t_2edd_c52 out) :
    SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧
      StoreObs fin base p s d n ∧ ∀ x, n ≠ Ninst.exec x)
      (Cert.prog cert) sevm pre t_2edd_c52 out := by
  obtain ⟨runP, -⟩ := FreePtr.SFunc.RunP.withPot (fun h => StepIn.toRun h) hsg run pot
  refine SFunc.RunP.mono ?_ (head52_strengthen hstack hp runP)
  intro s d n d' h
  exact ⟨h.1.1, h.2.1, h.2.2⟩

end Blanc.Lift.Usdc.OldInitializerV1Payload
