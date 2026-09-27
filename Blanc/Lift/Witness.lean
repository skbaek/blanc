import Blanc.Lift.Exact
import Blanc.Forward
import Blanc.ForwardCall

/-!
# Executable witnesses for lifted certificates

`lift_exactM` turns an `SProg.RunExact` over a checked certificate into a Jaune
`Exec`.  This module produces such a run for a *concrete* start state by
kernel evaluation of a small interpreter, `wrun`, over the certificate's own
tree.  The tree carries each instruction already decoded, so the interpreter
never reads the runtime bytes (no `ByteArray` code reads, no `jumpable`);
jumps are `fs[k]?` lookups.

Each node is executed by Jaune's own `Ninst.step`, except where Jaune's step
tests warm/cold access (`SLOAD`, `SSTORE`): `Std.HashSet` membership does not
reduce in the kernel (its bucket index goes through the opaque
`System.Platform.numBits`).  There the interpreter decides membership on a
list shadow of the accessed-key set and takes the post-state from the
forward lemmas `Ninst.runCompiled_sload_warm`/`_cold` and
`Ninst.runCompiled_sstore_warm`/`_cold`; the shadow agrees with the set
(`Agree`) because every other executed instruction keeps the accessed sets
(`ninstAccKeeps_run`).  The resulting states still carry Jaune's own
`HashSet.insert` terms; the kernel builds them but never inspects them.

`wrun_sound` is the one soundness theorem: a successful evaluation gives the
continuation-stack form `RunK` of `SFunc.RunExact`, and a run that halts from
entry `0` with an empty stack is `SProg.RunExact`.  Chunks compose through
`wrun_chain`.  Nothing here is contract-specific.
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
  cases r <;> simp [rinstAccKeeps] at hr <;> simp only [Rinst.runCore] at h
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
    | error e => simp [hp] at h
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
  | exec _ => simp [ninstAccKeeps] at hn
  | dupn _ => simp [ninstAccKeeps] at hn
  | swapn _ => simp [ninstAccKeeps] at hn
  | exchange _ => simp [ninstAccKeeps] at hn

theorem pcFree_of_ninstAccKeeps {n : Ninst} (hn : ninstAccKeeps n = true) : Ninst.pcFree n = true := by
  cases n with
  | reg r => cases r <;> simp_all [ninstAccKeeps, rinstAccKeeps, Ninst.pcFree]
  | _ => rfl

/-! ## Kernel-reducible state writes

Jaune's `State.set` tests `ac = .nil` through an instance built by `rw` (a `propext`
cast), which the kernel cannot reduce, so every state write (`SSTORE`, a value
transfer) is stuck under kernel evaluation.  `State.setB` tests the same condition
with a `Bool` and is equal to it (`State.set_eq_setB`). -/

/-- `ac = .nil`, decided by a `Bool`. -/
def acctNilB (ac : Acct) : Bool :=
  ac.nonce == 0 && ac.bal == 0 && ac.stor.isEmpty && ac.code.size == 0

theorem acctNilB_iff (ac : Acct) : acctNilB ac = true ↔ ac = .nil := by
  rcases ac with ⟨n, b, s, ⟨c⟩⟩
  simp only [acctNilB, Acct.nil, Bool.and_eq_true, beq_iff_eq, Acct.mk.injEq]
  constructor
  · rintro ⟨⟨⟨hn, hb⟩, hs⟩, hc⟩
    refine ⟨hn, hb, Std.TreeMap.eq_empty_of_isEmpty hs, ?_⟩
    simp only [ByteArray.size] at hc
    rw [Array.size_eq_zero_iff.mp hc]
  · rintro ⟨hn, hb, hs, hc⟩
    subst hs
    refine ⟨⟨⟨hn, hb⟩, rfl⟩, ?_⟩
    rw [hc]; rfl

/-- `State.set` with a kernel-reducible test. -/
def stateSetB (w : State) (a : Adr) (ac : Acct) : State :=
  if acctNilB ac then w.erase a else w.insert a ac

theorem state_set_eq_setB (w : State) (a : Adr) (ac : Acct) : w.set a ac = stateSetB w a ac := by
  unfold State.set stateSetB
  by_cases h : ac = .nil
  · simp only [h, ↓reduceIte, (acctNilB_iff Acct.nil).mpr rfl]
  · have h' : acctNilB ac = false := by
      cases hb : acctNilB ac
      · rfl
      · exact absurd ((acctNilB_iff ac).mp hb) h
    simp only [h, h', ↓reduceIte, Bool.false_eq_true]

/-- `State.setStorVal` through `stateSetB`. -/
def stateSetStorValB (w : State) (adr : Adr) (key val : B256) : State :=
  let acct : Acct := w.get adr
  stateSetB w adr {acct with stor := acct.stor.set key val}

theorem state_setStorVal_eq_B (w : State) (adr : Adr) (key val : B256) :
    w.setStorVal adr key val = stateSetStorValB w adr key val := by
  unfold State.setStorVal stateSetStorValB
  exact state_set_eq_setB _ _ _

/-- `Devm.setStorVal` through `stateSetB`. -/
def devmSetStorValB (devm : Devm) (adr : Adr) (key val : B256) : Devm :=
  devm.withState (stateSetStorValB devm.state adr key val)

theorem devm_setStorVal_eq_B (devm : Devm) (adr : Adr) (key val : B256) :
    devm.setStorVal adr key val = devmSetStorValB devm adr key val := by
  unfold Devm.setStorVal devmSetStorValB
  rw [state_setStorVal_eq_B]

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
  · rw [Array.size_copyD]; simp [padTo]; omega
  · intro i h1 h2
    rw [Array.size_copyD, Array.size_replicate] at h1
    have e1 : (Array.copyD xs (Array.replicate m 0))[i] =
        (Array.copyD xs (Array.replicate m 0)).getD i 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem]; rfl
    rw [e1]
    by_cases hi : i < xs.size
    · rw [Array.getD_copyD_of_lt _ _ _ _ hi (by simpa using h1)]
      simp [padTo, List.getElem_take, List.getElem_append_left (by simpa using hi : i < xs.toList.length),
        Array.getD_eq_getD_getElem?, hi]
    · rw [Array.getD_copyD_of_size_le _ _ _ _ (by omega)]
      simp only [padTo, List.getElem_toArray, List.getElem_take]
      rw [List.getElem_append_right (by simp; omega)]
      simp [Array.getD_eq_getD_getElem?, h1]

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
  simp [padTo]; omega

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


/-- An interpreter configuration: the machine state, the node to run, the
continuations of the pending internal calls (innermost first), list shadows of
the accessed storage keys and accessed addresses, and a shadow of the world's
persistent storage.  The interpreter reads storage only from the shadow, so the
world state itself is never inspected. -/
structure Cfg where
  devm : Devm
  f : SFunc
  K : List SFunc
  keys : List (Adr × B256)
  adrs : List Adr
  stor : StorShadow

/-- One interpreter step: a next configuration, a final outcome, or stuck. -/
inductive Res
  | cont : Cfg → Res
  | done : Outcome → Res
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
          some ⟨mach' c.devm (v :: s) gasWarmAccess, g, c.K, c.keys, c.adrs, c.stor⟩
        else none
      else if gasColdSload ≤ c.devm.gasLeft then
        some ⟨(addAccessedStorageKey c.devm ct k).setMach
            ⟨v :: s, c.devm.memory, c.devm.gasLeft - gasColdSload, c.devm.stateGas⟩,
          g, c.K, (ct, k) :: c.keys, c.adrs, c.stor⟩
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
          some ⟨(devmSetStorValB (c.devm.withRefundCounter rc) ct k v).setMach
              ⟨s, c.devm.memory, c.devm.gasLeft - cost, c.devm.stateGas⟩, g, c.K, c.keys, c.adrs,
              ((ct, k), v) :: c.stor⟩
        else none
      else
        let cost := gasColdSload + sstoreValueCost orig cur v
        if cost ≤ c.devm.gasLeft then
          some ⟨(devmSetStorValB ((addAccessedStorageKey c.devm ct k).withRefundCounter rc) ct k v).setMach
              ⟨s, c.devm.memory, c.devm.gasLeft - cost, c.devm.stateGas⟩, g, c.K, (ct, k) :: c.keys, c.adrs,
              ((ct, k), v) :: c.stor⟩
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
        c.devm.stateGas⟩, g, c.K, c.keys, c.adrs, c.stor⟩
    else none
  | _ => none

/-- `Array.sliceD` (one `getD`, hence one walk from the head, per byte) as `List.sliceD`
(one `drop` and one `take`). -/
theorem array_sliceD_eq_list (xs : Array UInt8) (m n : Nat) :
    Array.sliceD xs m n 0 = List.sliceD xs.toList m n 0 := by
  rw [Array.sliceD_eq_map, List.sliceD_eq_map]
  apply List.map_congr_left
  intro j _
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- `MLOAD` reading memory through `List.sliceD` (`Ninst.runCompiled_mload_of`). -/
def mloadStep (c : Cfg) (g : SFunc) : Option Cfg :=
  match c.devm.stack with
  | i :: s =>
    let cost := gVerylow + c.devm.extCost [⟨i.toNat, 32⟩]
    if cost ≤ c.devm.gasLeft ∧ s.length < 1024 then
      some ⟨c.devm.setMach ⟨Bytes.toB256 (List.sliceD c.devm.memory.data.toList i.toNat 32 0) :: s,
        c.devm.memory.extend i.toNat 32, c.devm.gasLeft - cost, c.devm.stateGas⟩, g, c.K, c.keys, c.adrs, c.stor⟩
    else none
  | _ => none

/-- `CALLDATACOPY` through `memWriteB` (`Ninst.runCompiled_calldatacopy_of`). -/
def calldatacopyStep (sevm : Sevm) (c : Cfg) (g : SFunc) : Option Cfg :=
  match c.devm.stack with
  | di :: si :: sz :: s =>
    let cost := gVerylow + gasCopy * ceilDiv sz.toNat 32 + c.devm.extCost [⟨di.toNat, sz.toNat⟩]
    if cost ≤ c.devm.gasLeft then
      some ⟨c.devm.setMach ⟨s, memWriteB c.devm.memory di.toNat (sevm.data.sliceD si.toNat sz.toNat 0),
        c.devm.gasLeft - cost, c.devm.stateGas⟩, g, c.K, c.keys, c.adrs, c.stor⟩
    else none
  | _ => none

/-! ## `CALL`

The `.call` arm of `Xinst.step` is stuck under kernel evaluation in two places:
the warm/cold charge (`accessCost` tests `Std.HashSet` membership) and the value
transfer in `Frame.enter` (`State.set`).  `callPrep` computes the arm up to its
spawn with the charge decided on the address shadow, and `frameEnterB` is
`Frame.enter` through `stateSetB`; both are proved equal to Jaune's
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

/-- `State.setBal` through `stateSetB`. -/
def stateSetBalB (st : State) (a : Adr) (v : B256) : State :=
  stateSetB st a ((st.get a).withBal v)

theorem state_setBal_eq_B (st : State) (a : Adr) (v : B256) :
    st.setBal a v = stateSetBalB st a v :=
  state_set_eq_setB _ _ _

/-- `Msg.benvAfterTransfer` through `stateSetB`. -/
def benvAfterTransferB (msg : Msg) : Except (EvmError × State × AdrSet × Tra) Benv :=
  if msg.shouldTransferValue then
    if msg.benv.state.bal msg.caller < msg.value then
      .error ⟨.internal (.assertion .none), msg.benv.state, msg.benv.createdAccounts,
        msg.tenv.transientStorage⟩
    else
      let st1 := stateSetBalB msg.benv.state msg.caller (msg.benv.state.bal msg.caller - msg.value)
      .ok ((msg.benv.withState st1).withState
        (stateSetBalB st1 msg.currentTarget (st1.bal msg.currentTarget + msg.value)))
  else .ok msg.benv

theorem benvAfterTransfer_eq_B (msg : Msg) : msg.benvAfterTransfer = benvAfterTransferB msg := by
  unfold Msg.benvAfterTransfer benvAfterTransferB
  by_cases ht : msg.shouldTransferValue = true
  · simp only [ht, ↓reduceIte]
    by_cases hb : msg.benv.state.bal msg.caller < msg.value
    · simp [hb, Benv.subBal, State.subBal, Option.toExcept]
    · simp [hb, Benv.subBal, State.subBal, Option.toExcept, Benv.addBal, State.addBal,
        state_setBal_eq_B]
      rfl
  · simp [ht]

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
  · simp [resumeCallB] at h
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
        rw [← hp.accessedAddresses]; simp [he, incorporateChildOnError]; rfl
      · show k ∈ e2.accessedStorageKeys ↔ _
        rw [← hp.accessedStorageKeys]; simp [he, incorporateChildOnError]; rfl
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
        exact Std.HashSet.mem_union_iff.trans (by simp [he]; exact Iff.rfl)
      · show k ∈ e2.accessedStorageKeys ↔ _
        rw [← hp.accessedStorageKeys]
        simp only [Bool.not_eq_true] at he
        exact Std.HashSet.mem_union_iff.trans (by simp [he]; exact Iff.rfl)
    · cases h

/-- The new-account charge of a value-bearing `CALL`. -/
def createCostL (d : Devm) (a : Adr) : Nat := if ¬ (d.getAcct a).Empty then 0 else gNewAccount

/-- A `CALL` computed up to its spawn: the child frame, the suspended parent, the
output window, and the parent's address shadow (the callee added). -/
structure CallPrep where
  f : Frame
  p : Devm
  oi : Nat
  os : Nat
  adrs : List Adr

/-- The `.call` arm of `Xinst.step` up to its spawn, warm/cold on the shadow
(`Xinst.step_call_zero_value_spawn`, `Xinst.step_call_nonzero_spawn`). -/
def callPrep (sevm : Sevm) (c : Cfg) : Option CallPrep :=
  match c.devm.stack with
  | gw :: cw :: vw :: iiw :: isw :: oiw :: osw :: s =>
    if decide (CoveredFork sevm.benvStat.fork) ∧ sevm.depth ≠ 0 then
      let d0 := c.devm.setMach ⟨s, c.devm.memory, c.devm.gasLeft, c.devm.stateGas⟩
      let ext := d0.extCost [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]
      let callee := cw.toAdr
      let dA := addAccessedAddress d0 callee
      let code := dA.state.getCode callee
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
          let create := createCostL dA callee
          let r := calculateMsgCallGas vw.toNat gw.toNat dA.gasLeft ext (acc + create + gasCallValue)
          if r.1 + ext ≤ dA.gasLeft ∧ sevm.isStatic = false ∧
              ¬ (dA.getAcct sevm.currentTarget).bal < vw then
            let p := callSpawnParent dA (r.1 + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat
            some ⟨Frame.ofCall (valueCallSpawnMsg sevm p r.2 vw callee callee iiw.toNat isw.toNat
                code false), p, oiw.toNat, osw.toNat, callee :: c.adrs⟩
          else none
    else none
  | _ => none

theorem callPrep_spec {sevm : Sevm} {c : Cfg} {cp : CallPrep} (h : callPrep sevm c = some cp)
    (hA : ∀ a, a ∈ c.devm.accessedAddresses ↔ a ∈ c.adrs) :
    Xinst.step sevm c.devm .call = .spawn cp.f (.call cp.p cp.oi cp.os) ∧
      (∀ a, a ∈ cp.p.accessedAddresses ↔ a ∈ cp.adrs) ∧
      cp.p.accessedStorageKeys = c.devm.accessedStorageKeys ∧
      cp.f.isCreate = false ∧ cp.f.inner.accessedAddresses = cp.p.accessedAddresses ∧
      cp.f.inner.accessedStorageKeys = cp.p.accessedStorageKeys ∧
      cp.f.inner.benv.stat.rules.stateGas = none ∧ cp.f.inner.benv.state = c.devm.state := by
  rcases c with ⟨devm, f, K, keys, adrs, stor⟩
  simp only [callPrep] at h
  split at h
  · rename_i gw cw vw iiw isw oiw osw s hs
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

theorem stateSetBalB_stor (st : State) (b : Adr) (v : B256) (a : Adr) (k : B256) :
    storOf (stateSetBalB st b v) a k = storOf st a k := by
  rw [← state_setBal_eq_B]
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
      show storOf (stateSetBalB _ _ _) a k = _
      rw [stateSetBalB_stor, stateSetBalB_stor]
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
  · simp [Frame.settleMsg, hf, processMessage.settle, bind, Except.bind] at h
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
              simp [executeCode.handleError, processMessage.settle, bind, Except.bind] at h <;>
              (try split at h) <;> (try cases h) <;>
              first | exact ⟨rfl, rfl, fun _ _ => rfl⟩ | exact ⟨rfl, rfl, benvAfterTransferB_stor hb⟩
          · simp [executeCode.handleError, processMessage.settle, bind, Except.bind] at h
            split at h <;> cases h <;>
              first | exact ⟨rfl, rfl, fun _ _ => rfl⟩ | exact ⟨rfl, rfl, benvAfterTransferB_stor hb⟩
        · cases he

/-- A `CALL` whose child answers synchronously (a precompile), run to the
parent's resumed state. -/
def callStep (sevm : Sevm) (c : Cfg) (g : SFunc) : Option Cfg :=
  match callPrep sevm c with
  | some cp =>
    match frameEnterB cp.f with
    | .done r =>
      match resumeCallB cp.p cp.oi cp.os r with
      | some d => some ⟨d, g, c.K, c.keys, cp.adrs, c.stor⟩
      | none => none
    | .run _ => none
  | none => none

/-- One node of the certificate tree. -/
def wstep (fs : List SFunc) (sevm : Sevm) (c : Cfg) : Res :=
  match c.f with
  | .dest g =>
    if gJumpdest ≤ c.devm.gasLeft then .cont ⟨mach' c.devm c.devm.stack gJumpdest, g, c.K, c.keys, c.adrs, c.stor⟩
    else .stuck
  | .jump k =>
    match c.devm.stack, fs[k]? with
    | _ :: s, some g =>
      if gMid ≤ c.devm.gasLeft then .cont ⟨mach' c.devm s gMid, g, c.K, c.keys, c.adrs, c.stor⟩ else .stuck
    | _, _ => .stuck
  | .branch f g =>
    match c.devm.stack with
    | _ :: w :: s =>
      if gHigh ≤ c.devm.gasLeft then
        .cont ⟨mach' c.devm s gHigh, if w = 0 then f else g, c.K, c.keys, c.adrs, c.stor⟩
      else .stuck
    | _ => .stuck
  | .branchTo f k =>
    match c.devm.stack with
    | _ :: w :: s =>
      if gHigh ≤ c.devm.gasLeft then
        if w = 0 then .cont ⟨mach' c.devm s gHigh, f, c.K, c.keys, c.adrs, c.stor⟩
        else match fs[k]? with
          | some g => .cont ⟨mach' c.devm s gHigh, g, c.K, c.keys, c.adrs, c.stor⟩
          | none => .stuck
      else .stuck
    | _ => .stuck
  | .callNext k f =>
    match c.devm.stack, fs[k]? with
    | _ :: s, some g =>
      if gMid ≤ c.devm.gasLeft then .cont ⟨mach' c.devm s gMid, g, f :: c.K, c.keys, c.adrs, c.stor⟩ else .stuck
    | _, _ => .stuck
  | .ret =>
    match c.devm.stack with
    | _ :: s =>
      if gMid ≤ c.devm.gasLeft then
        match c.K with
        | [] => .done (.returned (mach' c.devm s gMid))
        | g :: K => .cont ⟨mach' c.devm s gMid, g, K, c.keys, c.adrs, c.stor⟩
      else .stuck
    | _ => .stuck
  | .pcAt p g =>
    match Ninst.step ⟨p, sevm, c.devm⟩ (.reg .pc) with
    | .cont _ d => .cont ⟨d, g, c.K, c.keys, c.adrs, c.stor⟩
    | _ => .stuck
  | .last l =>
    match l.run sevm c.devm with
    | .ok d => .done (.halted d)
    | _ => .stuck
  | .next n g =>
    match n with
    | .reg .sload => match sloadStep sevm c g with | some c' => .cont c' | none => .stuck
    | .reg .sstore => match sstoreStep sevm c g with | some c' => .cont c' | none => .stuck
    | .reg .mstore => match mstoreStep c g with | some c' => .cont c' | none => .stuck
    | .reg .mload => match mloadStep c g with | some c' => .cont c' | none => .stuck
    | .reg .calldatacopy => match calldatacopyStep sevm c g with | some c' => .cont c' | none => .stuck
    | .exec .call => match callStep sevm c g with | some c' => .cont c' | none => .stuck
    | n =>
      if ninstAccKeeps n then
        match Ninst.step ⟨0, sevm, c.devm⟩ n with
        | .cont _ d => .cont ⟨d, g, c.K, c.keys, c.adrs, c.stor⟩
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
  | 0, m, c => by simp [wrun]
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


/-! ## Soundness -/

/-- `SFunc.RunExact` with a stack of pending internal-call continuations:
the current callee returns into the first, or the whole frame halts. -/
def RunK (fs : List SFunc) (sevm : Sevm) : Devm → SFunc → List SFunc → Outcome → Prop
  | devm, f, [], o => SFunc.RunExact fs sevm devm f o
  | devm, f, g :: K, o =>
    (∃ d, SFunc.RunExact fs sevm devm f (.returned d) ∧ RunK fs sevm d g K o) ∨
      (∃ d, o = .halted d ∧ SFunc.RunExact fs sevm devm f (.halted d))

/-- The shadows are the accessed-key and accessed-address sets and the world's storage. -/
def Agree (c : Cfg) : Prop :=
  (∀ x, x ∈ c.devm.accessedStorageKeys ↔ x ∈ c.keys) ∧
    (∀ a, a ∈ c.devm.accessedAddresses ↔ a ∈ c.adrs) ∧
    (∀ a k, storOf c.devm.state a k = lookupS c.stor a k)

theorem RunK.lift {fs : List SFunc} {sevm : Sevm} {devm devm' : Devm} {f f' : SFunc}
    (h : ∀ o, SFunc.RunExact fs sevm devm' f' o → SFunc.RunExact fs sevm devm f o) :
    ∀ {K o}, RunK fs sevm devm' f' K o → RunK fs sevm devm f K o
  | [], _, r => h _ r
  | _ :: _, _, .inl ⟨d, r, rest⟩ => .inl ⟨d, h _ r, rest⟩
  | _ :: _, _, .inr ⟨d, ho, r⟩ => .inr ⟨d, ho, h _ r⟩

theorem RunK.halted {fs : List SFunc} {sevm : Sevm} {devm d : Devm} {f : SFunc}
    (h : SFunc.RunExact fs sevm devm f (.halted d)) : ∀ {K}, RunK fs sevm devm f K (.halted d)
  | [] => h
  | _ :: _ => .inr ⟨d, rfl, h⟩

theorem popBurnBy1 {devm : Devm} {x : B256} {s : List B256} {cost : Nat}
    (hs : devm.stack = x :: s) (hg : cost ≤ devm.gasLeft) :
    Devm.PopBurnBy [x] cost devm (mach' devm s cost) :=
  Devm.popBurnBy_setMach hs (by omega)

theorem popBurnBy2 {devm : Devm} {x w : B256} {s : List B256} {cost : Nat}
    (hs : devm.stack = x :: w :: s) (hg : cost ≤ devm.gasLeft) :
    Devm.PopBurnBy [x, w] cost devm (mach' devm s cost) :=
  { stack := hs, memory := rfl, gasLeft := by simp [mach']; omega,
    logs := rfl, refundCounter := rfl, output := rfl, accountsToDelete := rfl,
    returnData := rfl, error := rfl, accessedAddresses := rfl,
    accessedStorageKeys := rfl, state := rfl, createdAccounts := rfl,
    transientStorage := rfl, stateGas := rfl, accountReads := rfl,
    storageReads := rfl }

/-- A step to a configuration: agreement is kept, and a run from the new
configuration is a run from the old one. -/
def StepOk (fs : List SFunc) (sevm : Sevm) (c c' : Cfg) : Prop :=
  (Agree c → Agree c') ∧ ∀ o, Agree c → RunK fs sevm c'.devm c'.f c'.K o → RunK fs sevm c.devm c.f c.K o

theorem StepOk.same {fs : List SFunc} {sevm : Sevm} {c c' : Cfg} (hk : c'.keys = c.keys)
    (hA : c'.adrs = c.adrs) (hS : c'.stor = c.stor) (ha : AccKeep c.devm c'.devm) (hK : c'.K = c.K)
    (h : ∀ o, SFunc.RunExact fs sevm c'.devm c'.f o → SFunc.RunExact fs sevm c.devm c.f o) :
    StepOk fs sevm c c' := by
  refine ⟨fun hc => ⟨fun x => ?_, fun a => ?_, fun a k => ?_⟩, fun o _ r => ?_⟩
  · rw [ha.2.1, hk]; exact hc.1 x
  · rw [ha.1, hA]; exact hc.2.1 a
  · rw [ha.2.2, hS]; exact hc.2.2 a k
  · rw [hK] at r; exact RunK.lift h r

theorem pc_step_accKeep {sevm : Sevm} {devm d : Devm} {p q : Nat}
    (h : Ninst.step ⟨p, sevm, devm⟩ (.reg .pc) = .cont q d) : AccKeep devm d := by
  rw [Ninst.step_reg] at h
  unfold Step.ofExecution at h
  split at h
  · cases h
  · cases h
    rename_i hd
    exact accKeep_pushItem hd

theorem keys_addAccessedStorageKey (d : Devm) (a : Adr) (k : B256) :
    (addAccessedStorageKey d a k).accessedStorageKeys = d.accessedStorageKeys.insert (a, k) := rfl

theorem agree_insert {d : Devm} {keys : List (Adr × B256)} {a : Adr} {k : B256}
    (hc : ∀ x, x ∈ d.accessedStorageKeys ↔ x ∈ keys) :
    ∀ x, x ∈ (addAccessedStorageKey d a k).accessedStorageKeys ↔ x ∈ (a, k) :: keys := by
  intro x
  rw [keys_addAccessedStorageKey, Std.HashSet.mem_insert, List.mem_cons, hc x, beq_iff_eq]
  constructor <;> rintro (h | h) <;> first | exact .inl h.symm | exact .inr h

theorem StepOk.of {fs : List SFunc} {sevm : Sevm} {c c' : Cfg} (hk : Agree c → Agree c')
    (hK : c'.K = c.K)
    (h : Agree c → ∀ o, SFunc.RunExact fs sevm c'.devm c'.f o → SFunc.RunExact fs sevm c.devm c.f o) :
    StepOk fs sevm c c' := by
  refine ⟨hk, fun o hc r => ?_⟩
  rw [hK] at r; exact RunK.lift (h hc) r

theorem storOf_setStorVal (st : State) (ct a : Adr) (k k' v : B256) :
    storOf (st.setStorVal ct k v) a k' = if ct = a ∧ k = k' then v else storOf st a k' := by
  unfold storOf State.setStorVal
  by_cases h : ct = a
  · subst h; rw [State.get_set_self]; simp only [true_and]; exact Stor.get_set_ite _ _ _ _
  · rw [State.get_set_ne _ h]; simp [h]

/-- A storage-empty state agrees with the empty storage shadow `[]`. -/
theorem storAgree_nil {st : State} (h : ∀ a k, storOf st a k = 0) :
    ∀ a k, storOf st a k = lookupS [] a k := by
  intro a k
  rw [h a k]
  rfl

theorem storOf_empty (a : Adr) (k : B256) : storOf (default : State) a k = 0 := rfl

/-- Setting an account with empty storage preserves storage-emptiness. -/
theorem storOf_set_empty (st : State) (p a : Adr) (ac : Acct) (k : B256)
    (h_st : storOf st a k = 0) (h_ac : ac.stor.get k = 0) :
    storOf (st.set p ac) a k = 0 := by
  unfold storOf
  by_cases h : p = a
  · subst h; rw [State.get_set_self]; exact h_ac
  · rw [State.get_set_ne _ h]; exact h_st

/-- Setting an account with empty storage via `stateSetB` preserves storage-emptiness. -/
theorem storOf_stateSetB_empty (st : State) (p a : Adr) (ac : Acct) (k : B256)
    (h_st : storOf st a k = 0) (h_ac : ac.stor.get k = 0) :
    storOf (stateSetB st p ac) a k = 0 := by
  rw [← state_set_eq_setB]
  exact storOf_set_empty st p a ac k h_st h_ac

/-- Writing `(ct, k, v)` into a state (via `stateSetStorValB`) and prepending to the shadow
preserves storage agreement. -/
theorem storOf_stateSetStorValB {st : State} {l : StorShadow} {ct : Adr} {k v : B256}
    (h : ∀ a k, storOf st a k = lookupS l a k) :
    ∀ a k', storOf (stateSetStorValB st ct k v) a k' = lookupS (((ct, k), v) :: l) a k' := by
  intro a k'
  rw [← state_setStorVal_eq_B]
  rw [storOf_setStorVal]
  simp only [lookupS]
  split
  · rfl
  · exact h a k'

/-- A storage write moves the storage shadow by one entry. -/
theorem storOf_sstore {d : Devm} {l : StorShadow} {ct : Adr} {k v : B256}
    (h : ∀ a k, storOf d.state a k = lookupS l a k) :
    ∀ a k', storOf (devmSetStorValB d ct k v).state a k' = lookupS (((ct, k), v) :: l) a k' :=
  storOf_stateSetStorValB h

/-- Apply a list of storage writes to a world state, in order. -/
def stateFoldStor (st : State) (writes : List ((Adr × B256) × B256)) : State :=
  writes.foldl (fun s ((a, k), v) => stateSetStorValB s a k v) st

/-- Storage shadow constructed by folding writes (newest first). -/
def storShadowOf (writes : List ((Adr × B256) × B256)) : StorShadow :=
  writes.foldl (fun s w => w :: s) []

/-- Agreement accumulator induction over a list of writes. -/
theorem storOf_foldl_writes (writes : List ((Adr × B256) × B256)) :
    ∀ (st : State) (s : StorShadow),
      (∀ a k, storOf st a k = lookupS s a k) →
      ∀ a k, storOf (writes.foldl (fun st ((a, k), v) => stateSetStorValB st a k v) st) a k =
             lookupS (writes.foldl (fun s w => w :: s) s) a k := by
  induction writes with
  | nil =>
    intro st s h a k
    exact h a k
  | cons w ws ih =>
    intro st s h a k
    rcases w with ⟨⟨ct, key⟩, val⟩
    simp only [List.foldl_cons]
    apply ih
    exact storOf_stateSetStorValB h

/-- Agreement for a state built by folding a list of writes from an empty-storage base,
with the shadow built from the same list. -/
theorem storOf_stateFoldStor (writes : List ((Adr × B256) × B256)) {st : State}
    (h : ∀ a k, storOf st a k = 0) :
    ∀ a k, storOf (stateFoldStor st writes) a k = lookupS (storShadowOf writes) a k :=
  storOf_foldl_writes writes st [] (storAgree_nil h)


theorem sloadStep_cont {fs : List SFunc} {sevm : Sevm} {c c' : Cfg} {g : SFunc}
    (h : sloadStep sevm c g = some c') (hf : c.f = .next (.reg .sload) g) :
    StepOk fs sevm c c' := by
  rcases c with ⟨devm, f, K, keys, adrs, stor⟩
  simp only at hf; subst hf
  simp only [sloadStep] at h
  split at h
  · rename_i k s hs
    split at h
    · rename_i hcond
      obtain ⟨hleg, hroom⟩ := hcond
      have hleg' : sevm.benvStat.rules.stateGas = none := Option.isNone_iff_eq_none.mp hleg
      split at h
      · rename_i hw
        split at h
        · rename_i hgas
          cases h
          exact StepOk.of (fun hc => hc) rfl fun hc o r =>
            .next (Ninst.runCompiled_sload_warm hleg' hs ((hc.1 _).mpr hw) (hc.2.2 _ _)
              (G := devm.gasLeft - gasWarmAccess) (by show devm.gasLeft = _; omega) hroom) r
        · cases h
      · rename_i hw
        split at h
        · rename_i hgas
          cases h
          exact StepOk.of (fun hc => ⟨agree_insert hc.1, hc.2.1, hc.2.2⟩) rfl fun hc o r =>
            .next (Ninst.runCompiled_sload_cold hleg' hs (fun hm => hw ((hc.1 _).mp hm)) (hc.2.2 _ _)
              (G := devm.gasLeft - gasColdSload) (by show devm.gasLeft = _; omega) hroom) r
        · cases h
    · cases h
  · cases h

theorem sstoreStep_cont {fs : List SFunc} {sevm : Sevm} {c c' : Cfg} {g : SFunc}
    (h : sstoreStep sevm c g = some c') (hf : c.f = .next (.reg .sstore) g) :
    StepOk fs sevm c c' := by
  rcases c with ⟨devm, f, K, keys, adrs, stor⟩
  simp only at hf; subst hf
  simp only [sstoreStep] at h
  split at h
  · rename_i k v s hs
    split at h
    · rename_i hcond
      obtain ⟨hleg, hsentry, hstatic⟩ := hcond
      have hleg' : sevm.benvStat.rules.stateGas = none := Option.isNone_iff_eq_none.mp hleg
      split at h
      · rename_i hw
        split at h
        · rename_i hgas
          cases h
          refine StepOk.of (fun hc => ⟨hc.1, hc.2.1, storOf_sstore hc.2.2⟩) rfl fun hc o r => .next ?_ r
          have hcur : devm.getStorVal sevm.currentTarget k = lookupS stor sevm.currentTarget k :=
            hc.2.2 _ _
          have h := Ninst.runCompiled_sstore_warm hleg' hs ((hc.1 _).mpr hw) hsentry hstatic
            (congrArg (fun x => sstoreValueCost (getOrigStorVal sevm sevm.currentTarget k) x v) hcur)
            (congrArg (fun x => sstoreNewRefundCounter sevm.benvStat.rules.gas v
              (getOrigStorVal sevm sevm.currentTarget k) x devm.refundCounter) hcur)
            (G := devm.gasLeft - _) (by exact (Nat.sub_add_cancel hgas).symm)
          rwa [devm_setStorVal_eq_B] at h
        · cases h
      · rename_i hw
        split at h
        · rename_i hgas
          cases h
          refine StepOk.of (fun hc => ⟨agree_insert hc.1, hc.2.1, storOf_sstore hc.2.2⟩) rfl
            fun hc o r => .next ?_ r
          have hcur : devm.getStorVal sevm.currentTarget k = lookupS stor sevm.currentTarget k :=
            hc.2.2 _ _
          have h := Ninst.runCompiled_sstore_cold hleg' hs (fun hm => hw ((hc.1 _).mp hm)) hsentry
            hstatic
            (congrArg (fun x => gasColdSload + sstoreValueCost (getOrigStorVal sevm sevm.currentTarget k) x v)
              hcur)
            (congrArg (fun x => sstoreNewRefundCounter sevm.benvStat.rules.gas v
              (getOrigStorVal sevm sevm.currentTarget k) x devm.refundCounter) hcur)
            (G := devm.gasLeft - _) (by exact (Nat.sub_add_cancel hgas).symm)
          rwa [devm_setStorVal_eq_B] at h
        · cases h
    · cases h
  · cases h

theorem generic_cont {fs : List SFunc} {sevm : Sevm} {c : Cfg} {n : Ninst} {g : SFunc}
    {q : Nat} {d : Devm} (hn : ninstAccKeeps n = true)
    (hstep : Ninst.step ⟨0, sevm, c.devm⟩ n = .cont q d) (hf : c.f = .next n g) :
    StepOk fs sevm c ⟨d, g, c.K, c.keys, c.adrs, c.stor⟩ := by
  have hk := ninstAccKeeps_step hn hstep
  refine StepOk.of (fun hc => ⟨fun x => ?_, fun a => ?_, fun a k => ?_⟩) rfl fun _ o r => ?_
  · show x ∈ d.accessedStorageKeys ↔ x ∈ c.keys
    rw [hk.2.1]; exact hc.1 x
  · show a ∈ d.accessedAddresses ↔ a ∈ c.adrs
    rw [hk.1]; exact hc.2.1 a
  · show storOf d.state a k = lookupS c.stor a k
    rw [hk.2.2]; exact hc.2.2 a k
  · rw [hf]
    exact .next (Ninst.runCompiled_of_run (pcFree_of_ninstAccKeeps hn)
      ⟨.none, trivial, 0, by simp [Ninst.StepRun, hstep, Step.Run]⟩) r

theorem mstoreStep_cont {fs : List SFunc} {sevm : Sevm} {c c' : Cfg} {g : SFunc}
    (h : mstoreStep c g = some c') (hf : c.f = .next (.reg .mstore) g) :
    StepOk fs sevm c c' := by
  rcases c with ⟨devm, f, K, keys, adrs, stor⟩
  simp only at hf; subst hf
  simp only [mstoreStep] at h
  split at h
  · rename_i i v s hs
    split at h
    · rename_i hgas
      cases h
      exact StepOk.same rfl rfl rfl (AccKeep.setMach _ _) rfl fun o r =>
        .next (Ninst.runCompiled_mstore hs (by exact (Nat.sub_add_cancel hgas).symm)
          (mem_write_eq_B _ _ _)) r
    · cases h
  · cases h

theorem mloadStep_cont {fs : List SFunc} {sevm : Sevm} {c c' : Cfg} {g : SFunc}
    (h : mloadStep c g = some c') (hf : c.f = .next (.reg .mload) g) :
    StepOk fs sevm c c' := by
  rcases c with ⟨devm, f, K, keys, adrs, stor⟩
  simp only at hf; subst hf
  simp only [mloadStep] at h
  split at h
  · rename_i i s hs
    split at h
    · rename_i hc
      obtain ⟨hgas, hroom⟩ := hc
      cases h
      exact StepOk.same rfl rfl rfl (AccKeep.setMach _ _) rfl fun o r =>
        .next (Ninst.runCompiled_mload_of hs rfl
          (by simp only [Mem.read, array_sliceD_eq_list]) rfl
          (by exact (Nat.sub_add_cancel hgas).symm) hroom) r
    · cases h
  · cases h

theorem calldatacopyStep_cont {fs : List SFunc} {sevm : Sevm} {c c' : Cfg} {g : SFunc}
    (h : calldatacopyStep sevm c g = some c') (hf : c.f = .next (.reg .calldatacopy) g) :
    StepOk fs sevm c c' := by
  rcases c with ⟨devm, f, K, keys, adrs, stor⟩
  simp only at hf; subst hf
  simp only [calldatacopyStep] at h
  split at h
  · rename_i di si sz s hs
    split at h
    · rename_i hgas
      cases h
      exact StepOk.same rfl rfl rfl (AccKeep.setMach _ _) rfl fun o r =>
        .next (Ninst.runCompiled_calldatacopy_of hs rfl (mem_write_eq_B _ _ _)
          (by exact (Nat.sub_add_cancel hgas).symm)) r
    · cases h
  · cases h

theorem callStep_cont {fs : List SFunc} {sevm : Sevm} {c c' : Cfg} {g : SFunc}
    (h : callStep sevm c g = some c') (hf : c.f = .next (.exec .call) g) :
    StepOk fs sevm c c' := by
  simp only [callStep] at h
  split at h
  · rename_i cp hp
    split at h
    · rename_i r he
      split at h
      · rename_i d hr
        cases h
        refine StepOk.of ?_ rfl ?_
        · intro hc
          obtain ⟨_, hpa, hpk, hcr, hia, hik, hsg, hst⟩ := callPrep_spec hp hc.2.1
          rcases r with e | child
          · simp [resumeCallB] at hr
          obtain ⟨hda, hdk⟩ := resumeCallB_acc hr
          obtain ⟨hca, hck, hcs⟩ := frameEnterB_done_acc hcr hsg he
          refine ⟨fun x => ?_, fun a => ?_, fun a k => ?_⟩
          · show x ∈ d.accessedStorageKeys ↔ x ∈ c.keys
            rw [hdk x, hck, hik, hpk, hc.1 x]
            exact ⟨fun h => h.elim id (·.2), .inl⟩
          · show a ∈ d.accessedAddresses ↔ a ∈ cp.adrs
            rw [hda a, hca, hia, hpa a]
            exact ⟨fun h => h.elim id (·.2), .inl⟩
          · show storOf d.state a k = lookupS c.stor a k
            rw [resumeCallB_state hr, hcs, hst]; exact hc.2.2 a k
        · intro hc o r'
          obtain ⟨hstep, -⟩ := callPrep_spec hp hc.2.1
          rw [hf]
          exact .next (Ninst.runCompiled_exec_doneFrame hstep (by rw [frame_enter_eq_B]; exact he)
            (resumeCallB_sound hr)) r'
      · cases h
    · cases h
  · cases h

/-- **A `CALL` into code.**  The child's execution `raw` is supplied with its
`Exec` derivation from the machine the frame enters with; a successful child
contributes its accessed sets, given as shadows `ckeys`/`cadrs`. -/
theorem callRun_cont {fs : List SFunc} {sevm : Sevm} {c : Cfg} {g : SFunc} {cp : CallPrep}
    {cevm : Evm} {raw : Execution} {child d : Devm}
    {ckeys : List (Adr × B256)} {cadrs : List Adr} {cstor : StorShadow}
    (hf : c.f = .next (.exec .call) g) (hp : callPrep sevm c = some cp)
    (he : frameEnterB cp.f = .run cevm) (hx : Nonempty (Exec cevm.pc cevm.sta cevm.dyna raw))
    (hs : cp.f.settle raw = .ok child) (hce : child.error.isSome = false)
    (hr : resumeCallB cp.p cp.oi cp.os (.ok child) = some d)
    (hca : ∀ a, a ∈ child.accessedAddresses ↔ a ∈ cadrs)
    (hck : ∀ k, k ∈ child.accessedStorageKeys ↔ k ∈ ckeys)
    (hcs : ∀ a k, storOf child.state a k = lookupS cstor a k) :
    StepOk fs sevm c ⟨d, g, c.K, c.keys ++ ckeys, cp.adrs ++ cadrs, cstor⟩ := by
  refine StepOk.of ?_ rfl ?_
  · intro hc
    obtain ⟨_, hpa, hpk, -⟩ := callPrep_spec hp hc.2.1
    obtain ⟨hda, hdk⟩ := resumeCallB_acc hr
    refine ⟨fun x => ?_, fun a => ?_, fun a k => ?_⟩
    · show x ∈ d.accessedStorageKeys ↔ x ∈ c.keys ++ ckeys
      rw [hdk x, hce, hpk, hc.1 x, hck x, List.mem_append]
      simp
    · show a ∈ d.accessedAddresses ↔ a ∈ cp.adrs ++ cadrs
      rw [hda a, hce, hpa a, hca a, List.mem_append]
      simp
    · show storOf d.state a k = lookupS cstor a k
      rw [resumeCallB_state hr]; exact hcs a k
  · intro hc o r'
    obtain ⟨hstep, -⟩ := callPrep_spec hp hc.2.1
    rw [hf]
    refine .next ⟨.some ⟨cevm, raw⟩, hx, fun pc => ?_⟩ r'
    apply XStep.run_toStep.mpr
    show XStep.Run (Xinst.step sevm c.devm .call) _ _
    rw [hstep]
    refine ⟨_, RunFrame.of_run (by rw [frame_enter_eq_B]; exact he), ?_⟩
    rw [hs]; exact (resumeCallB_sound hr).symm

theorem wstep_cont {fs : List SFunc} {sevm : Sevm} {c c' : Cfg}
    (h : wstep fs sevm c = .cont c') : StepOk fs sevm c c' := by
  rcases c with ⟨devm, f, K, keys, adrs, stor⟩
  cases f with
  | dest g =>
    simp only [wstep] at h
    split at h
    · cases h
      refine StepOk.same rfl rfl rfl (AccKeep.setMach _ _) rfl fun o r => .dest ?_ r
      exact Devm.burnBy_setMach (by assumption)
    · cases h
  | jump k =>
    simp only [wstep] at h
    split at h
    · rename_i d s g hs hg
      split at h
      · cases h
        exact StepOk.same rfl rfl rfl (AccKeep.setMach _ _) rfl fun o r =>
          .jump d hg (popBurnBy1 hs (by assumption)) r
      · cases h
    · cases h
  | branch f g =>
    simp only [wstep] at h
    split at h
    · rename_i d w s hs
      split at h
      · cases h
        refine StepOk.same rfl rfl rfl (AccKeep.setMach _ _) rfl fun o r => ?_
        by_cases hw : w = 0
        · subst hw; simp only [ite_true] at r
          exact .zero d (popBurnBy2 hs (by assumption)) r
        · simp only [hw, ite_false] at r
          exact .succ d w hw (popBurnBy2 hs (by assumption)) r
      · cases h
    · cases h
  | branchTo f k =>
    simp only [wstep] at h
    split at h
    · rename_i d w s hs
      split at h
      · rename_i hgas
        split at h
        · rename_i hw
          cases h; subst hw
          exact StepOk.same rfl rfl rfl (AccKeep.setMach _ _) rfl fun o r =>
            .toZero d (popBurnBy2 hs hgas) r
        · rename_i hw
          split at h
          · rename_i g hg
            cases h
            exact StepOk.same rfl rfl rfl (AccKeep.setMach _ _) rfl fun o r =>
              .toSucc d w hw hg (popBurnBy2 hs hgas) r
          · cases h
      · cases h
    · cases h
  | callNext k f =>
    simp only [wstep] at h
    split at h
    · rename_i d s g hs hg
      split at h
      · rename_i hgas
        cases h
        refine ⟨fun hc => hc, fun o _ r => ?_⟩
        have hpop := popBurnBy1 (cost := gMid) hs hgas
        rcases r with ⟨d1, r1, rest⟩ | ⟨d1, rfl, r1⟩
        · cases K with
          | nil => exact .callRet d hg hpop r1 rest
          | cons h' K =>
            rcases rest with ⟨d2, r2, rest⟩ | ⟨d2, rfl, r2⟩
            · exact .inl ⟨d2, .callRet d hg hpop r1 r2, rest⟩
            · exact .inr ⟨d2, rfl, .callRet d hg hpop r1 r2⟩
        · exact RunK.halted (.callHalt d hg hpop r1)
      · cases h
    · cases h
  | ret =>
    simp only [wstep] at h
    split at h
    · rename_i d s hs
      split at h
      · rename_i hgas
        split at h
        · cases h
        · rename_i g K' _
          cases h
          refine ⟨fun hc => hc, fun o _ r => ?_⟩
          exact .inl ⟨_, .ret d (popBurnBy1 hs hgas), r⟩
      · cases h
    · cases h
  | pcAt p g =>
    simp only [wstep] at h
    split at h
    · rename_i q d hstep
      cases h
      refine StepOk.same rfl rfl rfl (pc_step_accKeep hstep) rfl fun o r => .pcAt ?_ r
      simp [Ninst.StepRun, hstep, Step.Run]
    · cases h
  | last l =>
    simp only [wstep] at h
    split at h <;> cases h
  | undefined => simp [wstep] at h
  | next n g =>
    simp only [wstep] at h
    split at h
    · split at h
      · cases h; exact sloadStep_cont (by assumption) rfl
      · cases h
    · split at h
      · cases h; exact sstoreStep_cont (by assumption) rfl
      · cases h
    · split at h
      · cases h; exact mstoreStep_cont (by assumption) rfl
      · cases h
    · split at h
      · cases h; exact mloadStep_cont (by assumption) rfl
      · cases h
    · split at h
      · cases h; exact calldatacopyStep_cont (by assumption) rfl
      · cases h
    · split at h
      · cases h; exact callStep_cont (by assumption) rfl
      · cases h
    · split at h
      · rename_i hn
        split at h
        · rename_i q d hstep
          cases h
          exact generic_cont hn hstep rfl
        · cases h
      · cases h

theorem wstep_done {fs : List SFunc} {sevm : Sevm} {c : Cfg} {o : Outcome}
    (h : wstep fs sevm c = .done o) : RunK fs sevm c.devm c.f c.K o := by
  rcases c with ⟨devm, f, K, keys, adrs, stor⟩
  cases f with
  | ret =>
    simp only [wstep] at h
    split at h
    · rename_i d s hs
      split at h
      · rename_i hgas
        split at h
        · cases h
          exact SFunc.RunExact.ret d (popBurnBy1 hs hgas)
        · cases h
      · cases h
    · cases h
  | last l =>
    simp only [wstep] at h
    split at h
    · rename_i d hd
      cases h
      exact RunK.halted (.last hd)
    · cases h
  | next n g =>
    simp only [wstep] at h
    split at h
    · split at h <;> cases h
    · split at h <;> cases h
    · split at h <;> cases h
    · split at h <;> cases h
    · split at h <;> cases h
    · split at h <;> cases h
    · split at h
      · split at h <;> cases h
      · cases h
  | dest g => simp only [wstep] at h; split at h <;> cases h
  | jump k => simp only [wstep] at h; split at h <;> (try split at h) <;> cases h
  | branch f g => simp only [wstep] at h; split at h <;> (try split at h) <;> cases h
  | branchTo f k =>
    simp only [wstep] at h; split at h <;> (try split at h) <;> (try split at h) <;>
      (try split at h) <;> cases h
  | callNext k f => simp only [wstep] at h; split at h <;> (try split at h) <;> cases h
  | pcAt p g => simp only [wstep] at h; split at h <;> cases h
  | undefined => simp [wstep] at h

/-- A chunk of `n` steps to a configuration. -/
theorem wrun_cont {fs : List SFunc} {sevm : Sevm} :
    ∀ {n : Nat} {c c' : Cfg}, wrun fs sevm n c = .cont c' → StepOk fs sevm c c'
  | 0, c, c', h => by
    simp only [wrun, Res.cont.injEq] at h; subst h
    exact ⟨id, fun _ _ r => r⟩
  | n + 1, c, c', h => by
    simp only [wrun] at h
    split at h
    · rename_i c1 h1
      have s1 := wstep_cont h1
      have s2 := wrun_cont h
      exact ⟨fun hc => s2.1 (s1.1 hc), fun o hc r => s1.2 o hc (s2.2 o (s1.1 hc) r)⟩
    · rename_i r hr
      exact absurd h (hr _)

/-- A chunk of at most `n` steps to an outcome. -/
theorem wrun_done {fs : List SFunc} {sevm : Sevm} :
    ∀ {n : Nat} {c : Cfg} {o : Outcome}, wrun fs sevm n c = .done o → Agree c →
      RunK fs sevm c.devm c.f c.K o
  | 0, c, o, h, _ => by simp [wrun] at h
  | n + 1, c, o, h, hc => by
    simp only [wrun] at h
    split at h
    · rename_i c1 h1
      have s1 := wstep_cont h1
      exact s1.2 o hc (wrun_done h (s1.1 hc))
    · exact wstep_done h

/-- **The witness engine.**  A frame whose interpreter run from entry `0`
halts is a gas-exact run of the certificate's program. -/
theorem wrun_exact {fs : List SFunc} {sevm : Sevm} {pre post : Devm} {f0 : SFunc}
    {keys : List (Adr × B256)} {adrs : List Adr} {stor : StorShadow} {n : Nat}
    (h0 : fs[0]? = some f0) (hagree : Agree ⟨pre, f0, [], keys, adrs, stor⟩)
    (h : wrun fs sevm n ⟨pre, f0, [], keys, adrs, stor⟩ = .done (.halted post)) :
    SProg.RunExact fs sevm pre post :=
  ⟨f0, h0, wrun_done h hagree⟩

end Blanc.Lift.Witness
