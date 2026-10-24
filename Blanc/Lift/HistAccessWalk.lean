import Blanc.Lift.InvWalkWorld
import Blanc.Lift.CodeSizeWalk
import Blanc.Lift.WalkSteps
import Blanc.ForwardStorageAccess

/-!
# Access-schedule-generic inversion steps for historical forks

The exact-walk kit's world steps (`ri_sload`, ...) take `CoveredFork` and name the EIP-2929
successor `afterSload`. A historical fork may instead use flat access pricing (Istanbul and
Muir Glacier), where `SLOAD` neither warms the slot nor records it. This module states the
successor under the actual access schedule and inverts the step from the two rule facts it
reads, `rules.bal = none` and the access schedule itself; no fork list is assumed.

* `afterSloadH` — `afterSload` under EIP-2929, the base unchanged under flat access;
  `afterSloadH_of_eip2929`, `afterSloadH_getStor`, `afterSloadH_logs`, `afterSloadH_output`,
  `getStorVal_afterSloadH`, `getStorVal_afterStoreH`, `getStor_afterStoreH`,
  `getStor_afterStore_neH`, `logs_afterStoreH`, and the storage-walk steps
  `StorStep.sloadH`/`StorStep.sstoreH`;
* `ri_sloadH` — `SLOAD`, inverted, under `rules.bal = none` only;
* `afterSstoreH` — the `SSTORE` successor under the actual access schedule and refund regime
  (`sstoreRefundH`: legacy, flat net-metered `sstoreFlatRefundCounter`, or EIP-2929
  `sstoreNewRefundCounter`), equal to `afterSstore` under EIP-2929 net metering
  (`afterSstoreH_of_eip2929`), with its storage/log/output/... projections;
  `ri_sstoreH` (`rules.stateGas = none`, `rules.bal = none`), `ri_sstore_nonstaticH`
  (`rules.stateGas = none`), and `ri_sstoreH_covered` recovering the modern successor;
* `accountAccessH`/`extcodesizeCostH` — the `EXTCODESIZE` account-warming image and charge
  under the actual access and gas schedules; `ri_extcodesizeH`, `extcodesizeH_runCompiled`,
  `rx_extcodesizeH` (`rules.bal = none`), and `_covered` forms recovering the modern
  `ri_extcodesize`/`rx_extcodesize` statements.

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


/-- The refund counter after one `SSTORE` under the frame's actual refund regime: the legacy
schedule without net metering, the flat net-metered schedule (EIP-1283/EIP-2200) under flat
access, and the EIP-2929 one otherwise. -/
def sstoreRefundH (rules : ForkRules) (new_value original_value current_value : B256)
    (rc : Int) : Int :=
  match rules.sstore.netMetering, rules.access with
  | false, _ => sstoreLegacyRefundCounter rules.gas new_value original_value current_value rc
  | true, .flat g =>
    sstoreFlatRefundCounter rules.gas g.sload new_value original_value current_value rc
  | true, .eip2929 =>
    sstoreNewRefundCounter rules.gas new_value original_value current_value rc

/-- The access-set image of one `SSTORE`/`SLOAD` key under the frame's actual access schedule:
warmed under EIP-2929, untouched under flat access. -/
def storageAccessH (sevm : Sevm) (devm : Devm) (key : B256) : Devm :=
  match sevm.benvStat.rules.access with
  | .flat _ => devm
  | .eip2929 =>
    if (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈ devm.accessedStorageKeys then devm
    else addAccessedStorageKey devm sevm.currentTarget key

/-- The successor base of a successful `SSTORE` under the frame's actual access schedule and
refund regime (`stateGas = none` lane). -/
def afterSstoreH (sevm : Sevm) (devm : Devm) (key value : B256) : Devm :=
  ((storageAccessH sevm devm key).withRefundCounter
      (sstoreRefundH sevm.benvStat.rules value
        (devm.getOrigStorVal sevm sevm.currentTarget key)
        (devm.getStorVal sevm.currentTarget key) devm.refundCounter)).setStorVal
    sevm.currentTarget key value

theorem afterSstoreH_of_eip2929 {sevm : Sevm} {devm : Devm} {key value : B256}
    (access : sevm.benvStat.rules.access = .eip2929)
    (netMetering : sevm.benvStat.rules.sstore.netMetering = true) :
    afterSstoreH sevm devm key value = afterSstore sevm devm key value := by
  unfold afterSstoreH afterSstore storageAccessH sstoreRefundH
  rw [access, netMetering]

/-- The access image of a key carries no storage, code, log or output change. -/
private theorem storageAccessH_state (sevm : Sevm) (devm : Devm) (key : B256) :
    (storageAccessH sevm devm key).state = devm.state ∧
      (storageAccessH sevm devm key).logs = devm.logs ∧
      (storageAccessH sevm devm key).output = devm.output ∧
      (storageAccessH sevm devm key).error = devm.error ∧
      (storageAccessH sevm devm key).createdAccounts = devm.createdAccounts ∧
      (storageAccessH sevm devm key).accessedAddresses = devm.accessedAddresses ∧
      (storageAccessH sevm devm key).accountsToDelete = devm.accountsToDelete ∧
      (storageAccessH sevm devm key).stateGas = devm.stateGas := by
  unfold storageAccessH
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem afterSstoreH_getStor_self (sevm : Sevm) (base : Devm) (key value : B256) :
    Devm.getStor (afterSstoreH sevm base key value) sevm.currentTarget =
      (Devm.getStor base sevm.currentTarget).set key value := by
  unfold afterSstoreH
  rw [setStorVal_getStor_self, Devm.withRefundCounter_getStor]
  unfold Devm.getStor Devm.getAcct
  rw [(storageAccessH_state sevm base key).1]

theorem afterSstoreH_getStor_ne (sevm : Sevm) (base : Devm) (key value : B256) (address : Adr)
    (haddress : sevm.currentTarget ≠ address) :
    Devm.getStor (afterSstoreH sevm base key value) address = Devm.getStor base address := by
  unfold afterSstoreH
  rw [setStorVal_getStor_ne haddress, Devm.withRefundCounter_getStor]
  unfold Devm.getStor Devm.getAcct
  rw [(storageAccessH_state sevm base key).1]

theorem afterSstoreH_logs (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstoreH sevm base key value).logs = base.logs :=
  (storageAccessH_state sevm base key).2.1

theorem afterSstoreH_output (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstoreH sevm base key value).output = base.output :=
  (storageAccessH_state sevm base key).2.2.1

theorem afterSstoreH_error (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstoreH sevm base key value).error = base.error :=
  (storageAccessH_state sevm base key).2.2.2.1

theorem afterSstoreH_createdAccounts (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstoreH sevm base key value).createdAccounts = base.createdAccounts :=
  (storageAccessH_state sevm base key).2.2.2.2.1

theorem afterSstoreH_accessedAddresses (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstoreH sevm base key value).accessedAddresses = base.accessedAddresses :=
  (storageAccessH_state sevm base key).2.2.2.2.2.1

theorem afterSstoreH_stateGas (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstoreH sevm base key value).stateGas = base.stateGas :=
  (storageAccessH_state sevm base key).2.2.2.2.2.2.2

theorem afterSstoreH_refundCounter (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstoreH sevm base key value).refundCounter =
      sstoreRefundH sevm.benvStat.rules value
        (base.getOrigStorVal sevm sevm.currentTarget key)
        (base.getStorVal sevm.currentTarget key) base.refundCounter := rfl

/-- `afterSstoreH` commutes with replacement of the machine registers. -/
theorem afterSstoreH_setMach {sevm : Sevm} {base : Devm} {mach : Mach} {key value : B256} :
    afterSstoreH sevm (base.setMach mach) key value =
      (afterSstoreH sevm base key value).setMach mach := by
  unfold afterSstoreH storageAccessH
  split
  · rfl
  · by_cases warm : (sevm.currentTarget, key) ∈ base.accessedStorageKeys
    · simp only [Devm.setMach_accessedStorageKeys, warm, ite_true]
      rfl
    · simp only [Devm.setMach_accessedStorageKeys, warm, ite_false]
      rfl

/-- `afterSloadH` commutes with replacement of the machine registers. -/
theorem afterSloadH_setMach {sevm : Sevm} {base : Devm} {mach : Mach} {key : B256} :
    afterSloadH sevm (base.setMach mach) key = (afterSloadH sevm base key).setMach mach := by
  unfold afterSloadH
  split
  · exact afterSload_setMach
  · rfl

theorem afterSloadH_stateGas (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSloadH sevm base key).stateGas = base.stateGas := by
  unfold afterSloadH
  split
  · simp only [afterSload_stateGas]
  · rfl

theorem afterSloadH_output (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSloadH sevm base key).output = base.output := by
  unfold afterSloadH
  split
  · exact afterSload_output sevm base key
  · rfl

theorem getStorVal_afterSloadH {sevm : Sevm} {b : Devm} {k : B256} {a : Adr} {x : B256} :
    (afterSloadH sevm b k).getStorVal a x = b.getStorVal a x := by
  show (Devm.getStor _ _).get _ = (Devm.getStor _ _).get _
  rw [afterSloadH_getStor]

theorem getStorVal_afterStoreH {sevm : Sevm} {b : Devm} {k v key : B256} :
    (afterSstoreH sevm (afterSloadH sevm b k) k v).getStorVal sevm.currentTarget key =
      ((Devm.getStor b sevm.currentTarget).set k v).get key := by
  show (Devm.getStor _ _).get _ = _
  rw [afterSstoreH_getStor_self, afterSloadH_getStor]

theorem getStor_afterStoreH {sevm : Sevm} {b : Devm} {k v : B256} :
    Devm.getStor (afterSstoreH sevm (afterSloadH sevm b k) k v) sevm.currentTarget =
      (Devm.getStor b sevm.currentTarget).set k v := by
  rw [afterSstoreH_getStor_self, afterSloadH_getStor]

theorem getStor_afterStore_neH {sevm : Sevm} {b : Devm} {k v : B256} {a : Adr}
    (ha : a ≠ sevm.currentTarget) :
    Devm.getStor (afterSstoreH sevm (afterSloadH sevm b k) k v) a = Devm.getStor b a := by
  rw [afterSstoreH_getStor_ne _ _ _ _ _ (Ne.symm ha), afterSloadH_getStor]

theorem logs_afterStoreH {sevm : Sevm} {b : Devm} {k v : B256} :
    (afterSstoreH sevm (afterSloadH sevm b k) k v).logs = b.logs := by
  rw [afterSstoreH_logs, afterSloadH_logs]

/-- `StorStep.sload` under the actual access schedule. -/
theorem StorStep.sloadH {sevm : Sevm} {b b' : Devm} {s : Stor} (h : StorStep sevm b b' s)
    (k : B256) : StorStep sevm b (afterSloadH sevm b' k) s :=
  ⟨by rw [afterSloadH_getStor, h.self],
   fun a ha => by rw [afterSloadH_getStor, h.other a ha],
   by rw [afterSloadH_logs, h.logs]⟩

/-- `StorStep.sstore` under the actual access schedule and refund regime. -/
theorem StorStep.sstoreH {sevm : Sevm} {b b' : Devm} {s : Stor} (h : StorStep sevm b b' s)
    (k v : B256) : StorStep sevm b (afterSstoreH sevm b' k v) (s.set k v) :=
  ⟨by rw [afterSstoreH_getStor_self, h.self],
   fun a ha => by rw [afterSstoreH_getStor_ne _ _ _ _ _ (Ne.symm ha), h.other a ha],
   by rw [afterSstoreH_logs, h.logs]⟩

/-! ## Account access (`EXTCODESIZE`) -/

/-- The successor base of an account access under the frame's actual access schedule: the
EIP-2929 warming image, or the base unchanged under flat access. -/
def accountAccessH (sevm : Sevm) (base : Devm) (a : Adr) : Devm :=
  match sevm.benvStat.rules.access with
  | .eip2929 => temporalAccountAccessBase base a
  | .flat _ => base

/-- The charge of one `EXTCODESIZE` under the frame's actual access schedule and gas schedule. -/
def extcodesizeCostH (sevm : Sevm) (base : Devm) (a : Adr) : Nat :=
  match sevm.benvStat.rules.access with
  | .eip2929 =>
    (if a ∈ base.accessedAddresses then gasWarmAccess
      else sevm.benvStat.rules.gas.coldAccountAccess) +
      sevm.benvStat.rules.gas.codeReadSurcharge
  | .flat g => g.extCode + sevm.benvStat.rules.gas.codeReadSurcharge

theorem accountAccessH_of_eip2929 {sevm : Sevm} {base : Devm} {a : Adr}
    (access : sevm.benvStat.rules.access = .eip2929) :
    accountAccessH sevm base a = temporalAccountAccessBase base a := by
  unfold accountAccessH
  rw [access]

theorem extcodesizeCostH_of_covered {sevm : Sevm} {base : Devm} {a : Adr}
    (hfork : CoveredFork sevm.benvStat.fork) :
    extcodesizeCostH sevm base a = temporalAccountAccessCost base a := by
  unfold extcodesizeCostH temporalAccountAccessCost
  rw [hfork.rules_access, hfork.rules_codeReadSurcharge, hfork.rules_coldAccountAccess,
    Nat.add_zero]

theorem accountAccessH_state (sevm : Sevm) (base : Devm) (a : Adr) :
    (accountAccessH sevm base a).state = base.state := by
  unfold accountAccessH
  split
  · exact temporalAccountAccessBase_state base a
  · rfl

theorem accountAccessH_logs (sevm : Sevm) (base : Devm) (a : Adr) :
    (accountAccessH sevm base a).logs = base.logs := by
  unfold accountAccessH
  split
  · exact temporalAccountAccessBase_logs base a
  · rfl

theorem accountAccessH_output (sevm : Sevm) (base : Devm) (a : Adr) :
    (accountAccessH sevm base a).output = base.output := by
  unfold accountAccessH
  split
  · exact temporalAccountAccessBase_output base a
  · rfl

theorem accountAccessH_getStor (sevm : Sevm) (base : Devm) (a address : Adr) :
    Devm.getStor (accountAccessH sevm base a) address = Devm.getStor base address := by
  unfold Devm.getStor Devm.getAcct
  rw [accountAccessH_state]

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

/-- `SSTORE`, inverted under the actual access schedule and refund regime: the successor is over
`afterSstoreH`. Only `rules.stateGas = none` and `rules.bal = none` are assumed. -/
theorem ri_sstoreH {k v : B256} {d : Devm} (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (h : Ninst.Run sevm (St b (k :: v :: S) M G) (.reg .sstore) d) :
    ∃ G', d = St (afterSstoreH sevm b k v) S M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  rcases hss : sevm.benvStat.rules.sstore with ⟨nm, ss⟩
  cases access : sevm.benvStat.rules.access <;> cases nm <;> cases ss <;>
  · simp only [Rinst.run, Rinst.runCore, stateGas, hss, access,
      Devm.balReadStorage_of_bal_none bal, Devm.balReadAccount_of_bal_none bal] at run
    rw [show (St b (k :: v :: S) M G).pop = .ok (k, St b (v :: S) M G) from rfl] at run
    simp only [Except.bind_ok] at run
    rw [show (St b (v :: S) M G).pop = .ok (v, St b S M G) from rfl] at run
    simp only [Except.bind_ok] at run
    rcases Except.bind_eq_ok run with ⟨_, -, run₃⟩
    rcases Except.bind_eq_ok run₃ with ⟨s₅, h7, run₇⟩
    rcases Except.bind_eq_ok run₇ with ⟨_, -, h9⟩
    cases h9
    have e5 := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas h7)
    refine ⟨s₅.gasLeft, ?_⟩
    rw [e5]
    unfold afterSstoreH storageAccessH sstoreRefundH
    simp only [access, hss]
    first
    | rfl
    | by_cases hw : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ b.accessedStorageKeys
      · simp only [St.accessedStorageKeys, hw, not_true_eq_false, ite_false, ite_true]
        rfl
      · simp only [St.accessedStorageKeys, hw, not_false_eq_true, ite_false, ite_true]
        rfl

/-- `ri_sstoreH` recovers the modern `ri_sstore` successor on a covered fork. -/
theorem ri_sstoreH_covered {k v : B256} {d : Devm} (hfork : CoveredFork sevm.benvStat.fork)
    (h : Ninst.Run sevm (St b (k :: v :: S) M G) (.reg .sstore) d) :
    ∃ G', d = St (afterSstore sevm b k v) S M G' := by
  rw [← afterSstoreH_of_eip2929 hfork.rules_access
    (by rw [hfork.rules_sstore])]
  exact ri_sstoreH hfork.rules_stateGas_none hfork.rules_bal_none h

/-- A successful `SSTORE` runs in a non-static frame, under `rules.stateGas = none` alone:
both legacy-lane bodies end with `assertDynamic` before their only successful exit. -/
theorem ri_sstore_nonstaticH {k v : B256} {d : Devm}
    (stateGas : sevm.benvStat.rules.stateGas = none)
    (h : Ninst.Run sevm (St b (k :: v :: S) M G) (.reg .sstore) d) :
    sevm.isStatic = false := by
  cases hs : sevm.isStatic with
  | false => rfl
  | true =>
    exfalso
    rcases of_run_reg h with ⟨pc, run⟩
    rcases hss : sevm.benvStat.rules.sstore with ⟨nm, ss⟩
    cases access : sevm.benvStat.rules.access <;> cases nm <;> cases ss <;>
    · simp only [Rinst.run, Rinst.runCore, stateGas, hss, access] at run
      rw [show (St b (k :: v :: S) M G).pop = .ok (k, St b (v :: S) M G) from rfl] at run
      simp only [Except.bind_ok] at run
      rw [show (St b (v :: S) M G).pop = .ok (v, St b S M G) from rfl] at run
      simp only [Except.bind_ok] at run
      rcases Except.bind_eq_ok run with ⟨_, -, run₃⟩
      rcases Except.bind_eq_ok run₃ with ⟨_, -, run₇⟩
      simp only [bind, Except.bind, assertDynamic, Except.assert, hs, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at run₇

/-- `EXTCODESIZE`, inverted under the actual access schedule: the successor is over
`accountAccessH`. Only `rules.bal = none` is assumed; the charge stays existential. -/
theorem ri_extcodesizeH {x : B256} {d : Devm} (bal : sevm.benvStat.rules.bal = none)
    (h : Ninst.Run sevm (St b (x :: S) M G) (.reg .extcodesize) d) :
    ∃ G', d = St (accountAccessH sevm b x.toAdr)
      ((b.getCode x.toAdr).size.toB256 :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore, Devm.balReadAccount_of_bal_none bal] at run
  rw [show (St b (x :: S) M G).popToAdr = .ok (x.toAdr, St b S M G) from rfl] at run
  simp only [Except.bind_ok] at run
  rw [show (St b S M G).accessedAddresses = b.accessedAddresses from rfl] at run
  unfold accountAccessH
  cases access : sevm.benvStat.rules.access with
  | eip2929 =>
    simp only [access] at run ⊢
    by_cases hw : x.toAdr ∈ b.accessedAddresses
    · simp only [hw, ite_true] at run
      rcases Except.bind_eq_ok run with ⟨s1, h1, h2⟩
      have e2 := Devm.eq_of_push_ok h2
      subst e2
      have e1 := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas h1)
      rw [e1]
      refine ⟨s1.gasLeft, ?_⟩
      simp only [temporalAccountAccessBase, hw, ite_true]
      rfl
    · simp only [hw, ite_false] at run
      rcases Except.bind_eq_ok run with ⟨s1, h1, h2⟩
      have e2 := Devm.eq_of_push_ok h2
      subst e2
      have e1 := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas h1)
      rw [e1]
      refine ⟨s1.gasLeft, ?_⟩
      simp only [temporalAccountAccessBase, hw, ite_false]
      rfl
  | flat g =>
    simp only [access] at run ⊢
    rcases Except.bind_eq_ok run with ⟨s1, h1, h2⟩
    have e2 := Devm.eq_of_push_ok h2
    subst e2
    have e1 := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas h1)
    rw [e1]
    exact ⟨s1.gasLeft, rfl⟩

/-- `ri_extcodesizeH` recovers the modern `ri_extcodesize` on a covered fork. -/
theorem ri_extcodesizeH_covered {x : B256} {d : Devm} (hfork : CoveredFork sevm.benvStat.fork)
    (h : Ninst.Run sevm (St b (x :: S) M G) (.reg .extcodesize) d) :
    ∃ G', d = St (temporalAccountAccessBase b x.toAdr)
      ((b.getCode x.toAdr).size.toB256 :: S) M G' := by
  rw [← accountAccessH_of_eip2929 hfork.rules_access]
  exact ri_extcodesizeH hfork.rules_bal_none h

/-- Exact `EXTCODESIZE` step under the actual access and gas schedules. -/
theorem extcodesizeH_runCompiled {x : B256} (bal : sevm.benvStat.rules.bal = none)
    (hroom : S.length < 1024) :
    Ninst.RunCompiled sevm (St b (x :: S) M (G + extcodesizeCostH sevm b x.toAdr))
      (.reg .extcodesize)
      (St (accountAccessH sevm b x.toAdr) ((b.getCode x.toAdr).size.toB256 :: S) M G) := by
  refine Ninst.runCompiled_reg (by rintro ⟨⟩) ?_
  simp only [Rinst.runCore, Devm.balReadAccount_of_bal_none bal]
  rw [show (St b (x :: S) M (G + extcodesizeCostH sevm b x.toAdr)).popToAdr =
    .ok (x.toAdr, St b S M (G + extcodesizeCostH sevm b x.toAdr)) from rfl]
  simp only [Except.bind_ok]
  rw [show (St b S M (G + extcodesizeCostH sevm b x.toAdr)).accessedAddresses =
    b.accessedAddresses from rfl]
  unfold accountAccessH extcodesizeCostH
  cases access : sevm.benvStat.rules.access with
  | eip2929 =>
    by_cases hw : x.toAdr ∈ b.accessedAddresses
    · simp only [hw, ite_true, temporalAccountAccessBase]
      rw [chargeGas_eq_ok (cost := gasWarmAccess + sevm.benvStat.rules.gas.codeReadSurcharge)
        (devm := St b S M (G + (gasWarmAccess + sevm.benvStat.rules.gas.codeReadSurcharge)))
        (Nat.le_add_left _ _)]
      simp only [bind, Except.bind]
      rw [Devm.push_eq_ok]
      · simp only [St, Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach,
        Devm.gasLeft_setMach, Devm.stateGas_setMach, Devm.getCode_setMach, Nat.add_sub_cancel]
      · exact hroom
    · simp only [hw, ite_false, temporalAccountAccessBase]
      rw [chargeGas_eq_ok (cost := sevm.benvStat.rules.gas.coldAccountAccess +
          sevm.benvStat.rules.gas.codeReadSurcharge)
        (devm := addAccessedAddress (St b S M (G + (sevm.benvStat.rules.gas.coldAccountAccess +
          sevm.benvStat.rules.gas.codeReadSurcharge))) x.toAdr)
        (Nat.le_add_left _ _)]
      simp only [bind, Except.bind]
      have hadd : ∀ g, addAccessedAddress (St b S M g) x.toAdr =
          (addAccessedAddress b x.toAdr).setMach ⟨S, M, g, b.stateGas⟩ := fun _ => rfl
      rw [Devm.push_eq_ok]
      · rw [hadd]
        simp only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach,
          Devm.gasLeft_setMach, Devm.stateGas_setMach, Devm.getCode_setMach, Nat.add_sub_cancel]
        rfl
      · exact hroom
  | flat g =>
    dsimp only
    rw [chargeGas_eq_ok (cost := g.extCode + sevm.benvStat.rules.gas.codeReadSurcharge)
      (devm := St b S M (G + (g.extCode + sevm.benvStat.rules.gas.codeReadSurcharge)))
      (Nat.le_add_left _ _)]
    simp only [bind, Except.bind]
    rw [Devm.push_eq_ok]
    · simp only [St, Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach,
        Devm.gasLeft_setMach, Devm.stateGas_setMach, Devm.getCode_setMach, Nat.add_sub_cancel]
    · exact hroom

/-- `EXTCODESIZE`, forward, with the actual charge and continuation. -/
theorem rx_extcodesizeH {fs : List SFunc} {x : B256} {f : SFunc} {o : Outcome}
    (bal : sevm.benvStat.rules.bal = none) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm
      (St (accountAccessH sevm b x.toAdr) ((b.getCode x.toAdr).size.toB256 :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: S) M (G + extcodesizeCostH sevm b x.toAdr))
      (.next (.reg .extcodesize) f) o :=
  .next (extcodesizeH_runCompiled bal hroom) k

/-- `rx_extcodesizeH` recovers the modern `rx_extcodesize` on a covered fork. -/
theorem rx_extcodesizeH_covered {fs : List SFunc} {x : B256} {f : SFunc} {o : Outcome}
    (hfork : CoveredFork sevm.benvStat.fork) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm
      (St (temporalAccountAccessBase b x.toAdr)
        ((b.getCode x.toAdr).size.toB256 :: S) M G) f o) :
    SFunc.RunExact fs sevm
      (St b (x :: S) M (G + temporalAccountAccessCost b x.toAdr))
      (.next (.reg .extcodesize) f) o := by
  rw [← extcodesizeCostH_of_covered hfork]
  rw [← accountAccessH_of_eip2929 hfork.rules_access] at k
  exact rx_extcodesizeH hfork.rules_bal_none hroom k

end World

end Blanc.Lift
