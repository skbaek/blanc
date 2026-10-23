import Blanc.Lift.InvWalkWorld
import Blanc.ForwardStorageAccess

/-!
# Access-schedule-generic inversion steps for historical forks

The exact-walk kit's world steps (`ri_sload`, ...) take `CoveredFork` and name the EIP-2929
successor `afterSload`. A historical fork may instead use flat access pricing (Istanbul and
Muir Glacier), where `SLOAD` neither warms the slot nor records it. This module states the
successor under the actual access schedule and inverts the step from the two rule facts it
reads, `rules.bal = none` and the access schedule itself; no fork list is assumed.

* `afterSloadH` — `afterSload` under EIP-2929, the base unchanged under flat access;
  `afterSloadH_of_eip2929`, `afterSloadH_getStor`, `afterSloadH_logs`;
* `ri_sloadH` — `SLOAD`, inverted, under `rules.bal = none` only.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- The successor base of a successful `SLOAD` under the frame's actual access schedule. -/
def afterSloadH (sevm : Sevm) (base : Devm) (key : B256) : Devm :=
  match sevm.benvStat.rules.access with
  | .eip2929 => afterSload sevm base key
  | .flat _ => base

theorem afterSloadH_of_eip2929 {sevm : Sevm} {base : Devm} {key : B256}
    (access : sevm.benvStat.rules.access = .eip2929) :
    afterSloadH sevm base key = afterSload sevm base key := by
  unfold afterSloadH
  rw [access]

theorem afterSloadH_getStor (sevm : Sevm) (base : Devm) (key : B256) (address : Adr) :
    Devm.getStor (afterSloadH sevm base key) address = Devm.getStor base address := by
  unfold afterSloadH
  split
  · exact afterSload_getStor sevm base key address
  · rfl

theorem afterSloadH_logs (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSloadH sevm base key).logs = base.logs := by
  unfold afterSloadH
  split
  · exact afterSload_logs sevm base key
  · rfl

section World

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- `SLOAD`, inverted under the actual access schedule: the successor is over `afterSloadH`,
with the stored value pushed. Only `rules.bal = none` is assumed. -/
theorem ri_sloadH {k : B256} {d : Devm} (bal : sevm.benvStat.rules.bal = none)
    (h : Ninst.Run sevm (St b (k :: S) M G) (.reg .sload) d) :
    ∃ G', d = St (afterSloadH sevm b k) (b.getStorVal sevm.currentTarget k :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  cases access : sevm.benvStat.rules.access with
  | eip2929 =>
    rw [afterSloadH_of_eip2929 access]
    simp only [Rinst.run, Rinst.runCore, Devm.balReadStorage_of_bal_none bal, access] at run
    rw [show (St b (k :: S) M G).pop = .ok (k, St b S M G) from rfl] at run
    simp only [Except.bind_ok] at run
    by_cases hw : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ b.accessedStorageKeys
    · simp only [St.accessedStorageKeys, hw, ite_true] at run
      rcases Except.bind_eq_ok run with ⟨s1, h1, h2⟩
      have e2 := Devm.eq_of_push_ok h2
      subst e2
      have e1 := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas h1)
      rw [e1]
      refine ⟨s1.gasLeft, ?_⟩
      simp only [afterSload, hw, ite_true]
      rfl
    · simp only [St.accessedStorageKeys, hw, ite_false] at run
      rcases Except.bind_eq_ok run with ⟨s1, h1, h2⟩
      have e2 := Devm.eq_of_push_ok h2
      subst e2
      have e1 := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas h1)
      rw [e1]
      refine ⟨s1.gasLeft, ?_⟩
      simp only [afterSload, hw, ite_false]
      rfl
  | flat g =>
    simp only [Rinst.run, Rinst.runCore, Devm.balReadStorage_of_bal_none bal, access] at run
    rw [show (St b (k :: S) M G).pop = .ok (k, St b S M G) from rfl] at run
    simp only [Except.bind_ok] at run
    rcases Except.bind_eq_ok run with ⟨s1, h1, h2⟩
    have e2 := Devm.eq_of_push_ok h2
    subst e2
    have e1 := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas h1)
    rw [e1]
    refine ⟨s1.gasLeft, ?_⟩
    simp only [afterSloadH, access]
    rfl

end World

end Blanc.Lift
