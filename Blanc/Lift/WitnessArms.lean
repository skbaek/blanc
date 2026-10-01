import Blanc.Lift.Exact
import Blanc.Forward
import Blanc.ForwardCall
import Blanc.ConcreteRun

/-!
# Executable witnesses: the interpreter and its instruction arms

The kernel-evaluable interpreter `wrun` of `Blanc.Lift.Witness` and everything it
executes: the accessed-set bookkeeping (`AccKeep`, `ninstAccKeeps`), kernel-cheap
memory writes (`memWriteB`), the storage and account shadows,
the per-instruction arms (`sloadStep`, `sstoreStep`, `mstoreStep`, `calldatacopyStep`,
`keccakStep`, `logStep`, `callStep`) and the `CALL` preparation `callPrep`, with
`wstep`, `wrun` and the chunk composition `wrun_add`/`wrun_add_cont`.  The soundness
theorems are in `Blanc/Lift/Witness.lean`.  Nothing here is contract-specific.
-/

namespace Blanc.Lift.Witness

open Jaune Blanc.Lift

/-! ## Instructions that keep the accessed sets -/

/-- `d'` has `d`'s accessed addresses, accessed storage keys and world state. -/
def AccKeep (d d' : Devm) : Prop :=
  d'.accessedAddresses = d.accessedAddresses ∧ d'.accessedStorageKeys = d.accessedStorageKeys ∧
    d'.state = d.state

theorem AccKeep.refl (d : Devm) : AccKeep d d := ⟨rfl, rfl, rfl⟩

theorem AccKeep.trans {d d' d'' : Devm} (h1 : AccKeep d d') (h2 : AccKeep d' d'') :
    AccKeep d d'' := ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

theorem AccKeep.setMach (d : Devm) (m : Mach) : AccKeep d (d.setMach m) := ⟨rfl, rfl, rfl⟩

theorem accKeep_pop {d d' : Devm} {x : B256} (h : Devm.pop d = .ok ⟨x, d'⟩) : AccKeep d d' :=
  ⟨(Devm.pop_of_pop h).accessedAddresses.symm, (Devm.pop_of_pop h).accessedStorageKeys.symm, (Devm.pop_of_pop h).state.symm⟩

theorem accKeep_popToNat {d d' : Devm} {k : Nat} (h : Devm.popToNat d = .ok ⟨k, d'⟩) :
    AccKeep d d' := by
  obtain ⟨_, hp⟩ := Devm.pop_of_popToNat h
  exact ⟨hp.accessedAddresses.symm, hp.accessedStorageKeys.symm, hp.state.symm⟩

theorem accKeep_chargeGas {d d' : Devm} {c : Nat} (h : chargeGas c d = .ok d') : AccKeep d d' :=
  ⟨(Devm.burn_of_chargeGas h).accessedAddresses.symm,
    (Devm.burn_of_chargeGas h).accessedStorageKeys.symm, (Devm.burn_of_chargeGas h).state.symm⟩

theorem accKeep_push {d d' : Devm} {x : B256} (h : Devm.push x d = .ok d') : AccKeep d d' :=
  ⟨(Devm.push_of_push h).accessedAddresses.symm, (Devm.push_of_push h).accessedStorageKeys.symm, (Devm.push_of_push h).state.symm⟩

theorem accKeep_memRead (d : Devm) (i n : Nat) : AccKeep d (d.memRead i n).2 := ⟨rfl, rfl, rfl⟩

theorem accKeep_pushItem {d d' : Devm} {x : B256} {c : Nat} (h : pushItem x c d = .ok d') :
    AccKeep d d' := by
  rw [pushItem_def] at h
  exact ⟨(Devm.pushBurn_of_run h).accessedAddresses.symm,
    (Devm.pushBurn_of_run h).accessedStorageKeys.symm, (Devm.pushBurn_of_run h).state.symm⟩

/-- The regular instructions the interpreter runs through Jaune's step: none
of them reads or writes an accessed set. -/
def rinstAccKeeps : Rinst → Bool
  | .add | .mul | .sub | .div | .sdiv | .mod | .smod | .signextend | .lt | .gt | .slt | .sgt
  | .eq | .and | .or | .xor | .byte | .shl | .shr | .sar | .iszero | .not
  | .address | .origin | .caller | .callvalue | .calldatasize | .codesize | .gasprice
  | .returndatasize | .coinbase | .timestamp | .number | .prevrandao | .gaslimit | .chainid
  | .basefee | .blobbasefee | .msize | .gas | .exp
  | .keccak256 | .calldataload | .calldatacopy | .pop | .mload | .mstore | .dup _ | .swap _
  | .log _ => true
  | _ => false

theorem rinstAccKeeps_run {pc : Nat} {sevm : Sevm} {devm devm' : Devm} {r : Rinst}
    (hr : rinstAccKeeps r = true) (h : Rinst.runCore pc devm sevm r = .ok devm') :
    AccKeep devm devm' := by
  cases r <;> simp only [rinstAccKeeps, Bool.false_eq_true] at hr <;> simp only [Rinst.runCore] at h
  case add | mul | sub | div | sdiv | mod | smod | signextend | lt | gt | slt | sgt | eq
      | and | or | xor | byte | shl | shr | sar =>
    obtain ⟨_, _, hd⟩ := Devm.diffBurn_of_applyBinary h
    exact ⟨hd.accessedAddresses.symm, hd.accessedStorageKeys.symm, hd.state.symm⟩
  case iszero | not =>
    obtain ⟨_, hd⟩ := Devm.diffBurn_of_applyUnary h
    exact ⟨hd.accessedAddresses.symm, hd.accessedStorageKeys.symm, hd.state.symm⟩
  case address | origin | caller | callvalue | calldatasize | codesize | gasprice
      | returndatasize | coinbase | timestamp | number | prevrandao | gaslimit | chainid
      | basefee | blobbasefee | msize =>
    exact accKeep_pushItem h
  case gas =>
    obtain ⟨d1, h1, h2⟩ := Except.bind_eq_ok h
    exact (accKeep_chargeGas h1).trans (accKeep_push h2)
  case exp =>
    obtain ⟨⟨x, d1⟩, h1, e1⟩ := Except.bind_eq_ok h
    obtain ⟨⟨y, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
    obtain ⟨d3, h3, h4⟩ := Except.bind_eq_ok e2
    exact (accKeep_pop h1).trans ((accKeep_pop h2).trans ((accKeep_chargeGas h3).trans
      (accKeep_push h4)))
  case keccak256 =>
    obtain ⟨⟨i, d1⟩, h1, h'⟩ := Except.bind_eq_ok h
    obtain ⟨⟨n, d2⟩, h2, h''⟩ := Except.bind_eq_ok h'
    obtain ⟨d3, h3, h4⟩ := Except.bind_eq_ok h''
    exact (accKeep_popToNat h1).trans ((accKeep_popToNat h2).trans
      ((accKeep_chargeGas h3).trans ((accKeep_memRead d3 i n).trans (accKeep_push h4))))
  case calldataload =>
    obtain ⟨⟨x, d1⟩, h1, h'⟩ := Except.bind_eq_ok h
    obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h'
    exact (accKeep_pop h1).trans ((accKeep_chargeGas h2).trans (accKeep_push h3))
  case calldatacopy =>
    obtain ⟨⟨i, d1⟩, h1, e1⟩ := Except.bind_eq_ok h
    obtain ⟨⟨j, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
    obtain ⟨⟨n, d3⟩, h3, e3⟩ := Except.bind_eq_ok e2
    obtain ⟨d4, h4, h5⟩ := Except.bind_eq_ok e3
    cases h5
    exact (accKeep_popToNat h1).trans ((accKeep_popToNat h2).trans
      ((accKeep_popToNat h3).trans ((accKeep_chargeGas h4).trans ⟨rfl, rfl, rfl⟩)))
  case pop =>
    cases hp : devm.pop with
    | error e => simp only [ExceptT.stM_eq, hp, Except.map_error, Except.bind_error,
      reduceCtorEq] at h
    | ok r =>
      obtain ⟨x, d1⟩ := r
      simp only [hp] at h
      exact (accKeep_pop hp).trans (accKeep_chargeGas h)
  case mload =>
    obtain ⟨⟨i, d1⟩, h1, h'⟩ := Except.bind_eq_ok h
    obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h'
    exact (accKeep_popToNat h1).trans ((accKeep_chargeGas h2).trans
      ((accKeep_memRead d2 i 32).trans (accKeep_push h3)))
  case mstore =>
    obtain ⟨⟨i, d1⟩, h1, e1⟩ := Except.bind_eq_ok h
    obtain ⟨⟨v, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
    obtain ⟨d3, h3, h4⟩ := Except.bind_eq_ok e2
    cases h4
    exact (accKeep_popToNat h1).trans ((accKeep_pop h2).trans
      ((accKeep_chargeGas h3).trans ⟨rfl, rfl, rfl⟩))
  case dup =>
    obtain ⟨d1, h1, h2⟩ := Except.bind_eq_ok h
    split at h2
    · cases h2
    · exact (accKeep_chargeGas h1).trans (accKeep_push h2)
  case swap =>
    obtain ⟨d1, h1, h2⟩ := Except.bind_eq_ok h
    split at h2
    · cases h2
    · cases h2
      exact (accKeep_chargeGas h1).trans ⟨rfl, rfl, rfl⟩
  case log n =>
    obtain ⟨⟨mi, d1⟩, h1, e1⟩ := Except.bind_eq_ok h
    obtain ⟨⟨sz, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
    obtain ⟨⟨tp, d3⟩, h3, e3⟩ := Except.bind_eq_ok e2
    obtain ⟨d4, h4, e4⟩ := Except.bind_eq_ok e3
    obtain ⟨_, h5, h6⟩ := Except.bind_eq_ok e4
    cases h6
    have hk3 : AccKeep d2 d3 :=
      ⟨(Devm.pop_of_popN h3).2.accessedAddresses.symm,
        (Devm.pop_of_popN h3).2.accessedStorageKeys.symm, (Devm.pop_of_popN h3).2.state.symm⟩
    exact (accKeep_popToNat h1).trans ((accKeep_popToNat h2).trans (hk3.trans
      ((accKeep_chargeGas h4).trans ⟨rfl, rfl, rfl⟩)))

/-- Every `PUSH`, `DUP`, `SWAP` and the regular instructions of `rinstAccKeeps`. -/
def ninstAccKeeps : Ninst → Bool
  | .reg r => rinstAccKeeps r
  | .push _ _ => true
  | _ => false

theorem ninstAccKeeps_step {sevm : Sevm} {devm devm' : Devm} {n : Ninst} {pc pc' : Nat}
    (hn : ninstAccKeeps n = true) (h : Ninst.step ⟨pc, sevm, devm⟩ n = .cont pc' devm') :
    AccKeep devm devm' := by
  cases n with
  | push bs fits =>
    rw [Ninst.step_push] at h
    unfold Step.ofExecution at h
    split at h
    · cases h
    · cases h
      rename_i hd
      obtain ⟨d1, h1, h2⟩ := Except.bind_eq_ok hd
      exact (accKeep_chargeGas h1).trans (accKeep_push h2)
  | reg r =>
    rw [Ninst.step_reg] at h
    unfold Step.ofExecution at h
    split at h
    · cases h
    · cases h
      rename_i hd
      exact rinstAccKeeps_run hn hd
  | exec _ => simp only [ninstAccKeeps, Bool.false_eq_true] at hn
  | dupn _ => simp only [ninstAccKeeps, Bool.false_eq_true] at hn
  | swapn _ => simp only [ninstAccKeeps, Bool.false_eq_true] at hn
  | exchange _ => simp only [ninstAccKeeps, Bool.false_eq_true] at hn

theorem pcFree_of_ninstAccKeeps {n : Ninst} (hn : ninstAccKeeps n = true) : Ninst.pcFree n = true := by
  cases n with
  | reg r => cases r <;> simp_all only [ninstAccKeeps, rinstAccKeeps, Ninst.pcFree, Bool.false_eq_true]
  | _ => rfl

/-! ## Kernel-cheap memory writes

Jaune's `Mem.write` grows memory with `Array.copyD` (a fold of `setIfInBounds`,
quadratic under kernel evaluation, and every later read re-forces it).  `memWriteB`
pads by appending zeros instead and is equal to it (`mem_write_eq_B`). -/

/-- `Array.copyD xs (Array.replicate m 0)`, as an append. -/
def padTo (xs : Array UInt8) (m : Nat) : Array UInt8 :=
  ⟨(xs.toList ++ List.replicate (m - xs.size) 0).take m⟩

theorem copyD_replicate_eq_padTo (xs : Array UInt8) (m : Nat) :
    Array.copyD xs (Array.replicate m 0) = padTo xs m := by
  apply Array.ext
  · rw [Array.size_copyD]; simp only [Array.size_replicate, padTo, List.size_toArray,
    List.length_take, List.length_append, Array.length_toList, List.length_replicate, left_eq_inf]; omega
  · intro i h1 h2
    rw [Array.size_copyD, Array.size_replicate] at h1
    have e1 : (Array.copyD xs (Array.replicate m 0))[i] =
        (Array.copyD xs (Array.replicate m 0)).getD i 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem]; rfl
    rw [e1]
    by_cases hi : i < xs.size
    · rw [Array.getD_copyD_of_lt _ _ _ _ hi (by simpa only [Array.size_replicate] using h1)]
      simp [padTo, List.getElem_take, List.getElem_append_left (by simpa using hi : i < xs.toList.length),
        Array.getD_eq_getD_getElem?, hi]
    · rw [Array.getD_copyD_of_size_le _ _ _ _ (by omega)]
      simp only [padTo, List.getElem_toArray, List.getElem_take]
      rw [List.getElem_append_right (by simp only [Array.length_toList]; omega)]
      simp only [Array.getD_eq_getD_getElem?, Array.size_replicate, h1, getElem?_pos,
        Array.getElem_replicate, Option.getD_some, Array.length_toList, List.getElem_replicate]

/-- `Array.writeD` within bounds, as one splice (a single level for later reads). -/
def spliceD (a : Array UInt8) (n : Nat) (xs : Bytes) : Array UInt8 :=
  ⟨a.toList.take n ++ xs ++ a.toList.drop (n + xs.length)⟩

theorem writeD_eq_spliceD (a : Array UInt8) (n : Nat) (xs : Bytes) (h : n + xs.length ≤ a.size) :
    Array.writeD a n xs = spliceD a n xs := by
  apply Array.ext
  · rw [Array.size_writeD]; simp [spliceD]; omega
  · intro i h1 h2
    rw [Array.size_writeD] at h1
    have e1 : (Array.writeD a n xs)[i] = (Array.writeD a n xs).getD i 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem]; rfl
    rw [e1, Array.getD_writeD 0 xs a n i h]
    simp only [spliceD, List.getElem_toArray]
    by_cases hi : i < n
    · simp only [show ¬(n ≤ i ∧ i < n + xs.length) from by omega, ↓reduceIte]
      rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]
      simp [Array.getD_eq_getD_getElem?, h1]
    · by_cases hj : i < n + xs.length
      · simp only [show n ≤ i ∧ i < n + xs.length from ⟨by omega, hj⟩, and_self, ↓reduceIte]
        rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i - n < xs.length),
          Nat.min_eq_left (by omega : n ≤ a.size)]
      · simp only [show ¬(n ≤ i ∧ i < n + xs.length) from by omega, ↓reduceIte]
        rw [List.getElem_append_right (by simp; omega)]
        simp [Array.getD_eq_getD_getElem?, h1, Nat.min_eq_left (by omega : n ≤ a.size)]
        congr 1; omega

theorem padTo_size (xs : Array UInt8) (m : Nat) : (padTo xs m).size = m := by
  simp only [padTo, List.size_toArray, List.length_take, List.length_append, Array.length_toList,
    List.length_replicate, inf_eq_left]; omega

theorem ceil32_ge (n : Nat) : n ≤ ceil32 n := by
  unfold ceil32; split <;> omega

/-- `Mem.write` with `padTo` for the growth and one splice for the write. -/
def memWriteB (μ : Mem) (n : Nat) : Bytes → Mem
  | [] => μ
  | xs@(_ :: _) =>
    if n + xs.length ≤ μ.size then
      if n + xs.length ≤ μ.data.size then ⟨spliceD μ.data n xs, μ.size⟩
      else ⟨spliceD (padTo μ.data (n + xs.length)) n xs, μ.size⟩
    else
      ⟨spliceD (padTo μ.data (ceil32 (n + xs.length))) n xs, ceil32 (n + xs.length)⟩

theorem mem_write_eq_B (μ : Mem) (n : Nat) (xs : Bytes) : μ.write n xs = memWriteB μ n xs := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    simp only [Mem.write, memWriteB, copyD_replicate_eq_padTo]
    split
    · split
      · rename_i h; rw [writeD_eq_spliceD _ _ _ h]
      · rw [writeD_eq_spliceD _ _ _ (by rw [padTo_size])]
    · rw [writeD_eq_spliceD _ _ _ (by rw [padTo_size]; exact ceil32_ge _)]

/-! ## The interpreter -/

/-- A storage shadow: `((address, key), value)` writes, newest first. -/
abbrev StorShadow := List ((Adr × B256) × B256)

/-- The value the shadow holds at `(a, k)` (zero when it holds none). -/
def lookupS : StorShadow → Adr → B256 → B256
  | [], _, _ => 0
  | ((a', k'), v) :: l, a, k => if a' = a ∧ k' = k then v else lookupS l a k

/-- Persistent storage of `a` at `k` in a world state. -/
def storOf (st : State) (a : Adr) (k : B256) : B256 := (st.get a).stor.get k

/-- An account with its storage dropped: what the account shadow records. -/
def acctView (ac : Acct) : Acct := { ac with stor := .empty }

/-- An account shadow: `(address, account view)` entries, newest first. -/
abbrev AcctShadow := List (Adr × Acct)

/-- The account the shadow holds at `a` (`Acct.nil` when it holds none). -/
def lookupA : AcctShadow → Adr → Acct
  | [], _ => .nil
  | (a', ac) :: l, a => if a' = a then ac else lookupA l a

/-- The shadow after setting `a`'s balance to `v`. -/
def acsSetBal (acs : AcctShadow) (a : Adr) (v : B256) : AcctShadow :=
  (a, (lookupA acs a).withBal v) :: acs

/-- The world's account views agree with an account shadow. -/
def AcctAgree (st : State) (acs : AcctShadow) : Prop :=
  ∀ a, acctView (st.get a) = lookupA acs a

theorem acctView_get_set (st : State) (a b : Adr) (ac : Acct) :
    acctView ((State.set st a ac).get b) = if a = b then acctView ac else acctView (st.get b) := by
  by_cases h : a = b
  · subst h; rw [State.get_set_self]; simp only [↓reduceIte]
  · rw [State.get_set_ne _ h]; simp only [h, ↓reduceIte]

theorem acctAgree_set {st : State} {acs : AcctShadow} (h : AcctAgree st acs) (a : Adr)
    (ac : Acct) : AcctAgree (State.set st a ac) ((a, acctView ac) :: acs) := by
  intro b
  rw [acctView_get_set]
  simp only [lookupA]
  split
  · rfl
  · exact h b

/-- A storage write keeps every account view. -/
theorem acctView_setStorVal (w : State) (adr : Adr) (k v : B256) (b : Adr) :
    acctView ((State.setStorVal w adr k v).get b) = acctView (w.get b) := by
  unfold State.setStorVal
  rw [acctView_get_set]
  split
  · subst_vars; rfl
  · rfl

theorem acctAgree_setStorVal {w : State} {acs : AcctShadow} (h : AcctAgree w acs)
    (adr : Adr) (k v : B256) : AcctAgree (State.setStorVal w adr k v) acs := by
  intro b; rw [acctView_setStorVal]; exact h b



/-- An interpreter configuration: the machine state, the node to run, the
continuations of the pending internal calls (innermost first), list shadows of
the accessed storage keys and accessed addresses, a shadow of the world's
persistent storage and one of its accounts (storage dropped).  The interpreter
reads storage and accounts only from the shadows, so the world state itself is
never inspected: after a code child returns it is the child's, supplied rather
than computed. -/
structure Cfg where
  devm : Devm
  f : SFunc
  K : List SFunc
  keys : List (Adr × B256)
  adrs : List Adr
  stor : StorShadow
  acs : AcctShadow

/-- One interpreter step: a next configuration, a final outcome, or stuck. -/
inductive Res
  | cont : Cfg → Res
  /-- The outcome, with the configuration whose step produced it (its shadows
  describe the final state). -/
  | done : Outcome → Cfg → Res
  | stuck : Res

/-- `devm` with `cost` burned and its stack replaced by `s`. -/
def mach' (devm : Devm) (s : List B256) (cost : Nat) : Devm :=
  devm.setMach ⟨s, devm.memory, devm.gasLeft - cost, devm.stateGas⟩

/-- `SLOAD` at a key the shadow decides warm or cold (`Ninst.runCompiled_sload_*`). -/
def sloadStep (sevm : Sevm) (c : Cfg) (g : SFunc) : Option Cfg :=
  match c.devm.stack with
  | k :: s =>
    let ct := sevm.currentTarget
    let v := lookupS c.stor ct k
    if sevm.benvStat.rules.stateGas.isNone ∧ s.length < 1024 then
      if (ct, k) ∈ c.keys then
        if gasWarmAccess ≤ c.devm.gasLeft then
          some ⟨mach' c.devm (v :: s) gasWarmAccess, g, c.K, c.keys, c.adrs, c.stor, c.acs⟩
        else none
      else if gasColdSload ≤ c.devm.gasLeft then
        some ⟨(addAccessedStorageKey c.devm ct k).setMach
            ⟨v :: s, c.devm.memory, c.devm.gasLeft - gasColdSload, c.devm.stateGas⟩,
          g, c.K, (ct, k) :: c.keys, c.adrs, c.stor, c.acs⟩
      else none
    else none
  | _ => none

/-- `SSTORE` at a key the shadow decides warm or cold (`Ninst.runCompiled_sstore_*`). -/
def sstoreStep (sevm : Sevm) (c : Cfg) (g : SFunc) : Option Cfg :=
  match c.devm.stack with
  | k :: v :: s =>
    let ct := sevm.currentTarget
    let orig := getOrigStorVal sevm ct k
    let cur := lookupS c.stor ct k
    let rc := sstoreNewRefundCounter sevm.benvStat.rules.gas v orig cur c.devm.refundCounter
    if sevm.benvStat.rules.stateGas.isNone ∧ gCallStipend < c.devm.gasLeft ∧
        sevm.isStatic = false then
      if (ct, k) ∈ c.keys then
        let cost := sstoreValueCost orig cur v
        if cost ≤ c.devm.gasLeft then
          some ⟨(Devm.setStorVal (c.devm.withRefundCounter rc) ct k v).setMach
              ⟨s, c.devm.memory, c.devm.gasLeft - cost, c.devm.stateGas⟩, g, c.K, c.keys, c.adrs,
              ((ct, k), v) :: c.stor, c.acs⟩
        else none
      else
        let cost := gasColdSload + sstoreValueCost orig cur v
        if cost ≤ c.devm.gasLeft then
          some ⟨(Devm.setStorVal ((addAccessedStorageKey c.devm ct k).withRefundCounter rc) ct k v).setMach
              ⟨s, c.devm.memory, c.devm.gasLeft - cost, c.devm.stateGas⟩, g, c.K, (ct, k) :: c.keys, c.adrs,
              ((ct, k), v) :: c.stor, c.acs⟩
        else none
    else none
  | _ => none

/-- `MSTORE` through `memWriteB` (`Ninst.runCompiled_mstore`). -/
def mstoreStep (c : Cfg) (g : SFunc) : Option Cfg :=
  match c.devm.stack with
  | i :: v :: s =>
    let cost := gVerylow + c.devm.extCost [⟨i.toNat, 32⟩]
    if cost ≤ c.devm.gasLeft then
      some ⟨c.devm.setMach ⟨s, memWriteB c.devm.memory i.toNat v.toBytes, c.devm.gasLeft - cost,
        c.devm.stateGas⟩, g, c.K, c.keys, c.adrs, c.stor, c.acs⟩
    else none
  | _ => none

/-- `Array.sliceD` (one `getD`, hence one walk from the head, per byte) as `List.sliceD`
(one `drop` and one `take`). -/
theorem array_sliceD_eq_list (xs : Array UInt8) (m n : Nat) :
    Array.sliceD xs m n 0 = List.sliceD xs.toList m n 0 := by
  rw [Array.sliceD_eq_map, List.sliceD_eq_map]
  apply List.map_congr_left
  intro j _
  simp only [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-- `MLOAD` reading memory through `List.sliceD` (`Ninst.runCompiled_mload_of`). -/
def mloadStep (c : Cfg) (g : SFunc) : Option Cfg :=
  match c.devm.stack with
  | i :: s =>
    let cost := gVerylow + c.devm.extCost [⟨i.toNat, 32⟩]
    if cost ≤ c.devm.gasLeft ∧ s.length < 1024 then
      some ⟨c.devm.setMach ⟨Bytes.toB256 (List.sliceD c.devm.memory.data.toList i.toNat 32 0) :: s,
        c.devm.memory.extend i.toNat 32, c.devm.gasLeft - cost, c.devm.stateGas⟩, g, c.K, c.keys, c.adrs, c.stor, c.acs⟩
    else none
  | _ => none

/-- `CALLDATACOPY` through `memWriteB` (`Ninst.runCompiled_calldatacopy_of`). -/
def calldatacopyStep (sevm : Sevm) (c : Cfg) (g : SFunc) : Option Cfg :=
  match c.devm.stack with
  | di :: si :: sz :: s =>
    let cost := gVerylow + gasCopy * ceilDiv sz.toNat 32 + c.devm.extCost [⟨di.toNat, sz.toNat⟩]
    if cost ≤ c.devm.gasLeft then
      some ⟨c.devm.setMach ⟨s, memWriteB c.devm.memory di.toNat (sevm.data.sliceD si.toNat sz.toNat 0),
        c.devm.gasLeft - cost, c.devm.stateGas⟩, g, c.K, c.keys, c.adrs, c.stor, c.acs⟩
    else none
  | _ => none

/-- `KECCAK256` reading memory through `List.sliceD` (`Ninst.runCompiled_keccak256_of`). -/
def keccakStep (c : Cfg) (g : SFunc) : Option Cfg :=
  match c.devm.stack with
  | i :: sz :: s =>
    let cost := gKeccak256 + gasKeccak256Word * ceilDiv sz.toNat 32 +
      c.devm.extCost [⟨i.toNat, sz.toNat⟩]
    if cost ≤ c.devm.gasLeft ∧ s.length < 1024 then
      some ⟨c.devm.setMach ⟨Bytes.keccak (List.sliceD c.devm.memory.data.toList i.toNat sz.toNat 0) :: s,
        c.devm.memory.extend i.toNat sz.toNat, c.devm.gasLeft - cost, c.devm.stateGas⟩,
        g, c.K, c.keys, c.adrs, c.stor, c.acs⟩
    else none
  | _ => none

/-- `LOG n` reading memory through `List.sliceD` (`Ninst.runCompiled_log_of`). -/
def logStep (sevm : Sevm) (n : Fin 5) (c : Cfg) (g : SFunc) : Option Cfg :=
  match c.devm.stack with
  | i :: sz :: rest =>
    let cost := gLog + gLogdata * sz.toNat + gLogtopic * n.val + c.devm.extCost [⟨i.toNat, sz.toNat⟩]
    if n.val ≤ rest.length ∧ sevm.isStatic = false ∧ cost ≤ c.devm.gasLeft then
      some ⟨(c.devm.addLog ⟨sevm.currentTarget, rest.take n.val,
          List.sliceD c.devm.memory.data.toList i.toNat sz.toNat 0⟩).setMach
        ⟨rest.drop n.val, c.devm.memory.extend i.toNat sz.toNat, c.devm.gasLeft - cost,
          c.devm.stateGas⟩, g, c.K, c.keys, c.adrs, c.stor, c.acs⟩
    else none
  | _ => none

/-! ## `CALL`

The `.call` arm of `Xinst.step` is stuck under kernel evaluation in two places:
the warm/cold charge (`accessCost` tests `Std.HashSet` membership) and the value
transfer in `Frame.enter` (`State.set`).  `callPrep` computes the arm up to its
spawn with the charge decided on the address shadow, and `frameEnterB` is
`Frame.enter` through `benvAfterTransferB`; both are proved equal to Jaune's
(`callPrep_spec`, `frame_enter_eq_B`), by way of the forward lemmas of
`Blanc/ForwardCall.lean`.  A precompile child answers synchronously and is run
by the interpreter; a code child's result is supplied as data together with
its `Exec` derivation (`callRun_cont`).  Delegated (EIP-7702) callees are not
covered: the interpreter is stuck there. -/

/-- Prague's `accessCost`, warm/cold decided on the address shadow. -/
def accessCostL (x : Adr) (l : List Adr) : Nat :=
  if x ∈ l then gasWarmAccess else gasColdAccountAccess

theorem accessCost_eq_L {x : Adr} {s : AdrSet} {l : List Adr} (h : ∀ a, a ∈ s ↔ a ∈ l) :
    accessCost x s = accessCostL x l := by
  unfold accessCost accessCostL
  simp only [h x]

theorem acctAgree_setBal {st : State} {acs : AcctShadow} (h : AcctAgree st acs) (a : Adr)
    (v : B256) : AcctAgree (State.setBal st a v) (acsSetBal acs a v) := by
  intro b
  unfold State.setBal acsSetBal
  rw [acctView_get_set]
  simp only [lookupA]
  split
  · subst_vars
    rw [← h]; rfl
  · exact h b

/-- `Msg.benvAfterTransfer` with the transfer written through `State.setBal`. -/
def benvAfterTransferB (msg : Msg) : Except (EvmError × State × AdrSet × Tra) Benv :=
  if msg.shouldTransferValue then
    if msg.benv.state.bal msg.caller < msg.value then
      .error ⟨.internal (.assertion .none), msg.benv.state, msg.benv.createdAccounts,
        msg.tenv.transientStorage⟩
    else
      let st1 := State.setBal msg.benv.state msg.caller (msg.benv.state.bal msg.caller - msg.value)
      .ok ((msg.benv.withState st1).withState
        (State.setBal st1 msg.currentTarget (st1.bal msg.currentTarget + msg.value)))
  else .ok msg.benv

theorem benvAfterTransfer_eq_B (msg : Msg) : msg.benvAfterTransfer = benvAfterTransferB msg := by
  unfold Msg.benvAfterTransfer benvAfterTransferB
  by_cases ht : msg.shouldTransferValue = true
  · simp only [ht, ↓reduceIte]
    by_cases hb : msg.benv.state.bal msg.caller < msg.value
    · simp only [Option.toExcept, Benv.subBal, State.subBal, hb, ↓reduceIte, Option.bind_eq_bind,
      Option.bind_none, Except.bind_error]
    · simp only [Option.toExcept, Benv.subBal, State.subBal, hb, ↓reduceIte, Option.bind_eq_bind,
      Option.bind_some, Benv.addBal, State.addBal, Except.bind_ok, Except.ok.injEq]
      rfl
  · simp only [ht, Bool.false_eq_true, ↓reduceIte]

/-- `Frame.enter` through `benvAfterTransferB`. -/
def frameEnterB (f : Frame) : FrameEntry :=
  match benvAfterTransferB f.inner with
  | .error e => .done (f.settleMsg (.error e))
  | .ok benv =>
    match executeCode.enter (f.inner.withBenv benv) with
    | .inl evm => .run evm
    | .inr raw => .done (f.settle raw)

theorem frame_enter_eq_B (f : Frame) : f.enter = frameEnterB f := by
  unfold Frame.enter frameEnterB
  rw [benvAfterTransfer_eq_B]
  rfl

/-- `benvAfterTransferB` with the balances read from an account shadow, so that
the transfer test never inspects the world state. -/
def benvAfterTransferS (msg : Msg) (acs : AcctShadow) :
    Except (EvmError × State × AdrSet × Tra) Benv :=
  if msg.shouldTransferValue then
    if (lookupA acs msg.caller).bal < msg.value then
      .error ⟨.internal (.assertion .none), msg.benv.state, msg.benv.createdAccounts,
        msg.tenv.transientStorage⟩
    else
      let st1 := State.setBal msg.benv.state msg.caller ((lookupA acs msg.caller).bal - msg.value)
      let bt := (lookupA (acsSetBal acs msg.caller ((lookupA acs msg.caller).bal - msg.value))
        msg.currentTarget).bal
      .ok ((msg.benv.withState st1).withState (State.setBal st1 msg.currentTarget (bt + msg.value)))
  else .ok msg.benv

/-- The account shadow after a value transfer. -/
def acsTransfer (msg : Msg) (acs : AcctShadow) : AcctShadow :=
  if msg.shouldTransferValue then
    let acs1 := acsSetBal acs msg.caller ((lookupA acs msg.caller).bal - msg.value)
    acsSetBal acs1 msg.currentTarget ((lookupA acs1 msg.currentTarget).bal + msg.value)
  else acs

theorem bal_eq_lookupA {st : State} {acs : AcctShadow} (h : AcctAgree st acs) (a : Adr) :
    st.bal a = (lookupA acs a).bal := by
  rw [← h a]; rfl

theorem benvAfterTransfer_eq_S {msg : Msg} {acs : AcctShadow} (h : AcctAgree msg.benv.state acs) :
    benvAfterTransferB msg = benvAfterTransferS msg acs := by
  unfold benvAfterTransferB benvAfterTransferS
  rw [bal_eq_lookupA h msg.caller]
  split
  · split
    · rfl
    · dsimp only
      rw [bal_eq_lookupA (acctAgree_setBal h _ _) msg.currentTarget]
  · rfl

theorem acctAgree_transfer {msg : Msg} {acs : AcctShadow} {benv : Benv}
    (h : AcctAgree msg.benv.state acs) (ht : benvAfterTransferS msg acs = .ok benv) :
    AcctAgree benv.state (acsTransfer msg acs) := by
  unfold benvAfterTransferS at ht
  unfold acsTransfer
  split at ht
  · rename_i hsv
    simp only [hsv, ↓reduceIte]
    split at ht
    · cases ht
    · cases ht
      exact acctAgree_setBal (acctAgree_setBal h _ _) _ _
  · rename_i hsv
    cases ht
    simp only [hsv, Bool.false_eq_true, ↓reduceIte]
    exact h

/-- `Frame.enter` through `benvAfterTransferS`. -/
def frameEnterS (f : Frame) (acs : AcctShadow) : FrameEntry :=
  match benvAfterTransferS f.inner acs with
  | .error e => .done (f.settleMsg (.error e))
  | .ok benv =>
    match executeCode.enter (f.inner.withBenv benv) with
    | .inl evm => .run evm
    | .inr raw => .done (f.settle raw)

theorem frameEnterB_eq_S {f : Frame} {acs : AcctShadow} (h : AcctAgree f.inner.benv.state acs) :
    frameEnterB f = frameEnterS f acs := by
  unfold frameEnterB frameEnterS
  rw [benvAfterTransfer_eq_S h]

/-- `Devm.memWrite` through `memWriteB`. -/
def devmMemWriteB (d : Devm) (i : Nat) (xs : Bytes) : Devm :=
  d.setMach {d.mach with memory := memWriteB d.memory i xs}

theorem devm_memWrite_eq_B (d : Devm) (i : Nat) (xs : Bytes) :
    d.memWrite i xs = devmMemWriteB d i xs := by
  unfold Devm.memWrite liftMachPure Mach.memWrite devmMemWriteB
  rw [← mem_write_eq_B]; rfl

/-- `Resume.run (.call p oi os)` on a settled child, through `devmMemWriteB`. -/
def resumeCallB (p : Devm) (oi os : Nat) :
    Except (EvmError × State × AdrSet × Tra) Devm → Option Devm
  | .error _ => none
  | .ok child =>
    if child.error.isSome then
      match (incorporateChildOnError p child child.output).push 0 with
      | .ok e2 => some (devmMemWriteB e2 oi (child.output.take os))
      | .error _ => none
    else
      match (incorporateChildOnSuccess p child child.output).push 1 with
      | .ok e2 => some (devmMemWriteB e2 oi (child.output.take os))
      | .error _ => none

theorem resumeCallB_sound {p d : Devm} {oi os : Nat}
    {r : Except (EvmError × State × AdrSet × Tra) Devm} (h : resumeCallB p oi os r = some d) :
    Resume.run (.call p oi os) r = .ok d := by
  rcases r with e | child
  · simp only [resumeCallB, reduceCtorEq] at h
  · simp only [resumeCallB] at h
    simp only [Resume.run, liftToExecution, bind, Except.bind]
    split at h
    · rename_i he
      simp only [he, ↓reduceIte]
      split at h
      · rename_i e2 h2
        cases h; rw [h2]; simp only [devm_memWrite_eq_B]
      · cases h
    · rename_i he
      simp only [he, Bool.false_eq_true, ↓reduceIte]
      split at h
      · rename_i e2 h2
        cases h; rw [h2]; simp only [devm_memWrite_eq_B]
      · cases h

theorem resumeCallB_state {p d child : Devm} {oi os : Nat}
    (h : resumeCallB p oi os (.ok child) = some d) : d.state = child.state := by
  simp only [resumeCallB] at h
  split at h
  · split at h
    · rename_i e2 h2
      cases h
      exact (Devm.push_of_push h2).state.symm
    · cases h
  · split at h
    · rename_i e2 h2
      cases h
      exact (Devm.push_of_push h2).state.symm
    · cases h

/-- The accessed sets after the resume: the parent's, and on success the child's. -/
theorem resumeCallB_acc {p d child : Devm} {oi os : Nat}
    (h : resumeCallB p oi os (.ok child) = some d) :
    (∀ a, a ∈ d.accessedAddresses ↔
      a ∈ p.accessedAddresses ∨ (child.error.isSome = false ∧ a ∈ child.accessedAddresses)) ∧
    (∀ k, k ∈ d.accessedStorageKeys ↔
      k ∈ p.accessedStorageKeys ∨ (child.error.isSome = false ∧ k ∈ child.accessedStorageKeys)) := by
  simp only [resumeCallB] at h
  split at h
  · rename_i he
    split at h
    · rename_i e2 h2
      cases h
      have hp := Devm.push_of_push h2
      refine ⟨fun a => ?_, fun k => ?_⟩
      · show a ∈ e2.accessedAddresses ↔ _
        rw [← hp.accessedAddresses]; simp only [he, incorporateChildOnError, Std.HashSet.union_eq, Bool.true_eq_false, false_and, or_false]; rfl
      · show k ∈ e2.accessedStorageKeys ↔ _
        rw [← hp.accessedStorageKeys]; simp only [he, incorporateChildOnError, Std.HashSet.union_eq, Bool.true_eq_false, false_and, or_false]; rfl
    · cases h
  · rename_i he
    split at h
    · rename_i e2 h2
      cases h
      have hp := Devm.push_of_push h2
      refine ⟨fun a => ?_, fun k => ?_⟩
      · show a ∈ e2.accessedAddresses ↔ _
        rw [← hp.accessedAddresses]
        simp only [Bool.not_eq_true] at he
        exact Std.HashSet.mem_union_iff.trans (by simp only [he, Std.HashSet.contains_iff_mem, true_and]; exact Iff.rfl)
      · show k ∈ e2.accessedStorageKeys ↔ _
        rw [← hp.accessedStorageKeys]
        simp only [Bool.not_eq_true] at he
        exact Std.HashSet.mem_union_iff.trans (by simp only [he, Std.HashSet.contains_iff_mem, true_and]; exact Iff.rfl)
    · cases h

/-- The new-account charge of a value-bearing `CALL`. -/
def createCostL (d : Devm) (a : Adr) : Nat := if ¬ (d.getAcct a).Empty then 0 else gNewAccount

/-- `createCostL` read from the account shadow. -/
def createCostS (acs : AcctShadow) (a : Adr) : Nat :=
  if ¬ (lookupA acs a).Empty then 0 else gNewAccount

/-- A `CALL` computed up to its spawn: the child frame, the suspended parent, the
output window, and the parent's address shadow (the callee added). -/
structure CallPrep where
  f : Frame
  p : Devm
  oi : Nat
  os : Nat
  adrs : List Adr

/-- The `.call` arm of `Xinst.step` up to its spawn, warm/cold on the shadow
(`Xinst.step_call_zero_value_spawn`, `Xinst.step_call_nonzero_spawn`).  The callee's
code, its emptiness and the sender's balance come from the account shadow; the child
message carries the shadow's code (equal to the world's under `Agree`). -/
def callPrep (sevm : Sevm) (c : Cfg) : Option CallPrep :=
  match c.devm.stack with
  | gw :: cw :: vw :: iiw :: isw :: oiw :: osw :: s =>
    if decide (CoveredFork sevm.benvStat.fork) ∧ sevm.depth ≠ 0 then
      let d0 := c.devm.setMach ⟨s, c.devm.memory, c.devm.gasLeft, c.devm.stateGas⟩
      let ext := d0.extCost [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]
      let callee := cw.toAdr
      let dA := addAccessedAddress d0 callee
      let code := (lookupA c.acs callee).code
      match getDelegatedCodeAddress code with
      | some _ => none
      | none =>
        let acc := accessCostL callee c.adrs
        if vw = 0 then
          let r := calculateMsgCallGas 0 gw.toNat dA.gasLeft ext acc
          if r.1 + ext ≤ dA.gasLeft then
            let p := callSpawnParent dA (r.1 + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat
            some ⟨Frame.ofCall (callSpawnMsg sevm p r.2 callee callee iiw.toNat isw.toNat code false),
              p, oiw.toNat, osw.toNat, callee :: c.adrs⟩
          else none
        else
          let create := createCostS c.acs callee
          let r := calculateMsgCallGas vw.toNat gw.toNat dA.gasLeft ext (acc + create + gasCallValue)
          if r.1 + ext ≤ dA.gasLeft ∧ sevm.isStatic = false ∧
              ¬ (lookupA c.acs sevm.currentTarget).bal < vw then
            let p := callSpawnParent dA (r.1 + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat
            some ⟨Frame.ofCall (valueCallSpawnMsg sevm p r.2 vw callee callee iiw.toNat isw.toNat
                code false), p, oiw.toNat, osw.toNat, callee :: c.adrs⟩
          else none
    else none
  | _ => none

theorem callPrep_spec {sevm : Sevm} {c : Cfg} {cp : CallPrep} (h : callPrep sevm c = some cp)
    (hA : ∀ a, a ∈ c.devm.accessedAddresses ↔ a ∈ c.adrs) (hC : AcctAgree c.devm.state c.acs) :
    Xinst.step sevm c.devm .call = .spawn cp.f (.call cp.p cp.oi cp.os) ∧
      (∀ a, a ∈ cp.p.accessedAddresses ↔ a ∈ cp.adrs) ∧
      cp.p.accessedStorageKeys = c.devm.accessedStorageKeys ∧
      cp.f.isCreate = false ∧ cp.f.inner.accessedAddresses = cp.p.accessedAddresses ∧
      cp.f.inner.accessedStorageKeys = cp.p.accessedStorageKeys ∧
      cp.f.inner.benv.stat.rules.stateGas = none ∧ cp.f.inner.benv.state = c.devm.state := by
  rcases c with ⟨devm, f, K, keys, adrs, stor, acs⟩
  simp only [callPrep] at h
  split at h
  · rename_i gw cw vw iiw isw oiw osw s hs
    have hcode : (lookupA acs cw.toAdr).code = (addAccessedAddress
        (devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩) cw.toAdr).state.getCode
        cw.toAdr := (congrArg Acct.code (hC cw.toAdr)).symm
    have hbal : (lookupA acs sevm.currentTarget).bal = ((addAccessedAddress
        (devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩) cw.toAdr).getAcct
        sevm.currentTarget).bal := (congrArg Acct.bal (hC sevm.currentTarget)).symm
    have hcre : createCostS acs cw.toAdr = createCostL (addAccessedAddress
        (devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩) cw.toAdr) cw.toAdr := by
      unfold createCostS createCostL
      rw [← hC cw.toAdr]; rfl
    simp only [hcode, hbal, hcre] at h
    split at h
    · rename_i hcond
      obtain ⟨hfork, hdepth⟩ := hcond
      have hfork' : CoveredFork sevm.benvStat.fork := of_decide_eq_true hfork
      split at h
      · cases h
      · rename_i hdel
        have hdel' : accessDelegation
            (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩)
              cw.toAdr) cw.toAdr =
            ⟨false, cw.toAdr, (addAccessedAddress
              (devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩) cw.toAdr).state.getCode
              cw.toAdr, 0,
              addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩)
                cw.toAdr⟩ := by
          unfold accessDelegation
          simp only at hdel ⊢
          rw [hdel]
        have hacc : accessCost cw.toAdr
            (devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩).accessedAddresses + 0 =
            accessCostL cw.toAdr adrs := by
          rw [Nat.add_zero]; exact accessCost_eq_L hA
        have hins : ∀ a, a ∈ (addAccessedAddress
            (devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩) cw.toAdr).accessedAddresses ↔
            a ∈ cw.toAdr :: adrs := by
          intro a
          show a ∈ devm.accessedAddresses.insert cw.toAdr ↔ _
          rw [Std.HashSet.mem_insert, List.mem_cons, hA a, beq_iff_eq]
          constructor <;> rintro (h | h) <;> first | exact .inl h.symm | exact .inr h
        have hsg := hfork'.rules_stateGas_none
        split at h
        · rename_i hv
          subst hv
          split at h
          · rename_i hgas
            cases h
            exact ⟨Xinst.step_call_zero_value_spawn hfork' hs rfl hdel' hacc rfl hgas hdepth,
              hins, rfl, rfl, rfl, rfl, hsg, rfl⟩
          · cases h
        · rename_i hv
          split at h
          · rename_i hc
            obtain ⟨hgas, hstatic, hsender⟩ := hc
            cases h
            exact ⟨Xinst.step_call_nonzero_spawn hfork' hs hv rfl hdel' hacc rfl rfl hgas hstatic
              hsender hdepth, hins, rfl, rfl, rfl, rfl, hsg, rfl⟩
          · cases h
    · cases h
  · cases h

theorem storOf_setBal (st : State) (b : Adr) (v : B256) (a : Adr) (k : B256) :
    storOf (State.setBal st b v) a k = storOf st a k := by
  unfold storOf State.setBal
  by_cases h : b = a
  · subst h; rw [State.get_set_self]; rfl
  · rw [State.get_set_ne _ h]

/-- A value transfer moves balances only. -/
theorem benvAfterTransferB_stor {m : Msg} {benv : Benv} (h : benvAfterTransferB m = .ok benv) :
    ∀ a k, storOf benv.state a k = storOf m.benv.state a k := by
  intro a k
  unfold benvAfterTransferB at h
  split at h
  · split at h
    · cases h
    · cases h
      show storOf (State.setBal _ _ _) a k = _
      rw [storOf_setBal, storOf_setBal]
  · cases h; rfl

/-- A precompile child leaves the accessed sets it was given, and the storage. -/
theorem frameEnterB_done_acc {f : Frame} {child : Devm} (hf : f.isCreate = false)
    (hsg : f.inner.benv.stat.rules.stateGas = none)
    (h : frameEnterB f = .done (.ok child)) :
    child.accessedAddresses = f.inner.accessedAddresses ∧
      child.accessedStorageKeys = f.inner.accessedStorageKeys ∧
      ∀ a k, storOf child.state a k = storOf f.inner.benv.state a k := by
  unfold frameEnterB at h
  split at h
  · simp only [Frame.settleMsg, hf, Bool.false_eq_true, ↓reduceIte, processMessage.settle, bind,
    Except.bind, FrameEntry.done.injEq, reduceCtorEq] at h
  · rename_i benv hb
    split at h
    · cases h
    · rename_i raw he
      simp only [FrameEntry.done.injEq] at h
      unfold executeCode.enter at he
      split at he
      · cases he
      · rename_i adr _
        split at he
        · simp only [Sum.inr.injEq] at he
          subst he
          simp only [Frame.settle, Frame.settleMsg, hf, Bool.false_eq_true, ↓reduceIte,
            executeCode.handleErrorWith, Msg.withBenv, hsg] at h
          unfold executePrecomp applyPrecompResult at h
          split at h
          · rename_i m cost _
            cases m <;>
              simp only [processMessage.settle, bind, Except.bind, executeCode.handleError, reduceCtorEq] at h <;>
              (try split at h) <;> (try cases h) <;>
              first | exact ⟨rfl, rfl, fun _ _ => rfl⟩ | exact ⟨rfl, rfl, benvAfterTransferB_stor hb⟩
          · simp only [processMessage.settle, bind, Except.bind, executeCode.handleError] at h
            split at h <;> cases h <;>
              first | exact ⟨rfl, rfl, fun _ _ => rfl⟩ | exact ⟨rfl, rfl, benvAfterTransferB_stor hb⟩
        · cases he

/-- A precompile child that succeeds ends in the world the value transfer made. -/
theorem frameEnterB_done_ok_state {f : Frame} {child : Devm} (hf : f.isCreate = false)
    (hsg : f.inner.benv.stat.rules.stateGas = none)
    (h : frameEnterB f = .done (.ok child)) (hce : child.error.isSome = false) :
    ∃ benv, benvAfterTransferB f.inner = .ok benv ∧ child.state = benv.state := by
  unfold frameEnterB at h
  split at h
  · simp only [Frame.settleMsg, hf, Bool.false_eq_true, ↓reduceIte, processMessage.settle, bind,
    Except.bind, FrameEntry.done.injEq, reduceCtorEq] at h
  · rename_i benv hb
    refine ⟨benv, hb, ?_⟩
    split at h
    · cases h
    · rename_i raw he
      simp only [FrameEntry.done.injEq] at h
      unfold executeCode.enter at he
      split at he
      · cases he
      · rename_i adr _
        split at he
        · simp only [Sum.inr.injEq] at he
          subst he
          simp only [Frame.settle, Frame.settleMsg, hf, Bool.false_eq_true, ↓reduceIte,
            executeCode.handleErrorWith, Msg.withBenv, hsg] at h
          unfold executePrecomp applyPrecompResult at h
          split at h
          · rename_i m cost _
            cases m <;>
              simp only [processMessage.settle, bind, Except.bind, executeCode.handleError, reduceCtorEq] at h <;>
              (try split at h) <;> (try cases h) <;> first | rfl | (exfalso; simp_all only [Msg.withBenv_stat_rules,
                Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Devm.error, Devm.rollback,
                Devm.setWorld, Bool.true_eq_false])
          · simp only [processMessage.settle, bind, Except.bind, executeCode.handleError] at h
            split at h <;> cases h <;> first | rfl | (exfalso; simp_all only [Msg.withBenv_stat_rules,
              Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Devm.error, Devm.rollback,
              Devm.setWorld, Bool.true_eq_false])
        · cases he

/-- A frame whose entry is the same under every covered fork: its code address is neither
`MODEXP` (0x05, EIP-7823/7883 change it) nor `P256VERIFY` (0x100, a precompile from Osaka).
The interpreter's synchronous precompile children are restricted to such frames, so that a
run of `wrun` is unchanged by the fork (`Blanc.Lift.NodeWalk.wrun_withFork`). -/
def frameEntryForkFree (f : Frame) : Bool :=
  match f.inner.codeAddress with
  | some a => a != 5 && a != 0x100
  | none => true

/-- A `CALL` whose child answers synchronously (a precompile) and succeeds, run to
the parent's resumed state; the account shadow takes the value transfer.  A call into
`MODEXP` or `P256VERIFY` (`frameEntryForkFree`) is not run: those two precompiles are the
only ones whose behaviour depends on the covered fork, and a run that avoids them holds under
every covered fork. -/
def callStep (sevm : Sevm) (c : Cfg) (g : SFunc) : Option Cfg :=
  match callPrep sevm c with
  | some cp =>
    match frameEnterS cp.f c.acs with
    | .done (.ok child) =>
      if child.error.isSome = false ∧ frameEntryForkFree cp.f = true then
        match resumeCallB cp.p cp.oi cp.os (.ok child) with
        | some d => some ⟨d, g, c.K, c.keys, cp.adrs, c.stor, acsTransfer cp.f.inner c.acs⟩
        | none => none
      else none
    | _ => none
  | none => none

/-- One node of the certificate tree. -/
def wstep (fs : List SFunc) (sevm : Sevm) (c : Cfg) : Res :=
  match c.f with
  | .dest g =>
    if gJumpdest ≤ c.devm.gasLeft then .cont ⟨mach' c.devm c.devm.stack gJumpdest, g, c.K, c.keys, c.adrs, c.stor, c.acs⟩
    else .stuck
  | .jump k =>
    match c.devm.stack, fs[k]? with
    | _ :: s, some g =>
      if gMid ≤ c.devm.gasLeft then .cont ⟨mach' c.devm s gMid, g, c.K, c.keys, c.adrs, c.stor, c.acs⟩ else .stuck
    | _, _ => .stuck
  | .branch f g =>
    match c.devm.stack with
    | _ :: w :: s =>
      if gHigh ≤ c.devm.gasLeft then
        .cont ⟨mach' c.devm s gHigh, if w = 0 then f else g, c.K, c.keys, c.adrs, c.stor, c.acs⟩
      else .stuck
    | _ => .stuck
  | .branchTo f k =>
    match c.devm.stack with
    | _ :: w :: s =>
      if gHigh ≤ c.devm.gasLeft then
        if w = 0 then .cont ⟨mach' c.devm s gHigh, f, c.K, c.keys, c.adrs, c.stor, c.acs⟩
        else match fs[k]? with
          | some g => .cont ⟨mach' c.devm s gHigh, g, c.K, c.keys, c.adrs, c.stor, c.acs⟩
          | none => .stuck
      else .stuck
    | _ => .stuck
  | .callNext k f =>
    match c.devm.stack, fs[k]? with
    | _ :: s, some g =>
      if gMid ≤ c.devm.gasLeft then .cont ⟨mach' c.devm s gMid, g, f :: c.K, c.keys, c.adrs, c.stor, c.acs⟩ else .stuck
    | _, _ => .stuck
  | .ret =>
    match c.devm.stack with
    | _ :: s =>
      if gMid ≤ c.devm.gasLeft then
        match c.K with
        | [] => .done (.returned (mach' c.devm s gMid)) c
        | g :: K => .cont ⟨mach' c.devm s gMid, g, K, c.keys, c.adrs, c.stor, c.acs⟩
      else .stuck
    | _ => .stuck
  | .pcAt p g =>
    match Ninst.step ⟨p, sevm, c.devm⟩ (.reg .pc) with
    | .cont _ d => .cont ⟨d, g, c.K, c.keys, c.adrs, c.stor, c.acs⟩
    | _ => .stuck
  | .last .selfdestruct => .stuck
  | .last l =>
    match l.run sevm c.devm with
    | .ok d => .done (.halted d) c
    | _ => .stuck
  | .next n g =>
    match n with
    | .reg .sload => match sloadStep sevm c g with | some c' => .cont c' | none => .stuck
    | .reg .sstore => match sstoreStep sevm c g with | some c' => .cont c' | none => .stuck
    | .reg .mstore => match mstoreStep c g with | some c' => .cont c' | none => .stuck
    | .reg .mload => match mloadStep c g with | some c' => .cont c' | none => .stuck
    | .reg .calldatacopy => match calldatacopyStep sevm c g with | some c' => .cont c' | none => .stuck
    | .reg .keccak256 => match keccakStep c g with | some c' => .cont c' | none => .stuck
    | .reg (.log k) => match logStep sevm k c g with | some c' => .cont c' | none => .stuck
    | .exec .call => match callStep sevm c g with | some c' => .cont c' | none => .stuck
    | n =>
      if ninstAccKeeps n then
        match Ninst.step ⟨0, sevm, c.devm⟩ n with
        | .cont _ d => .cont ⟨d, g, c.K, c.keys, c.adrs, c.stor, c.acs⟩
        | _ => .stuck
      else .stuck
  | .undefined => .stuck

/-- At most `n` steps: the configuration reached, or the outcome. -/
def wrun (fs : List SFunc) (sevm : Sevm) : Nat → Cfg → Res
  | 0, c => .cont c
  | n + 1, c =>
    match wstep fs sevm c with
    | .cont c' => wrun fs sevm n c'
    | r => r

/-- Composition of runs: running `n + m` steps is running `n` steps, then `m`
steps from the intermediate configuration if it continued. -/
theorem wrun_add (fs : List SFunc) (sevm : Sevm) :
    ∀ (n m : Nat) (c : Cfg),
      wrun fs sevm (n + m) c =
        match wrun fs sevm n c with
        | .cont c' => wrun fs sevm m c'
        | r => r
  | 0, m, c => by simp only [zero_add, wrun]
  | n + 1, m, c => by
    simp only [Nat.succ_add, wrun]
    cases h : wstep fs sevm c with
    | cont c' => exact wrun_add fs sevm n m c'
    | done o => rfl
    | stuck => rfl

/-- Step composition when the first chunk continues. -/
theorem wrun_add_cont {fs : List SFunc} {sevm : Sevm} {n m : Nat} {c c' : Cfg} {r : Res}
    (h1 : wrun fs sevm n c = .cont c') (h2 : wrun fs sevm m c' = r) :
    wrun fs sevm (n + m) c = r := by
  rw [wrun_add, h1]
  exact h2

end Blanc.Lift.Witness
