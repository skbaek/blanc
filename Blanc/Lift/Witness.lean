import Blanc.Lift.Exact
import Blanc.Forward

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

/-- `d'` has `d`'s accessed addresses and accessed storage keys. -/
def AccKeep (d d' : Devm) : Prop :=
  d'.accessedAddresses = d.accessedAddresses ∧ d'.accessedStorageKeys = d.accessedStorageKeys

theorem AccKeep.refl (d : Devm) : AccKeep d d := ⟨rfl, rfl⟩

theorem AccKeep.trans {d d' d'' : Devm} (h1 : AccKeep d d') (h2 : AccKeep d' d'') :
    AccKeep d d'' := ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem AccKeep.setMach (d : Devm) (m : Mach) : AccKeep d (d.setMach m) := ⟨rfl, rfl⟩

theorem accKeep_pop {d d' : Devm} {x : B256} (h : Devm.pop d = .ok ⟨x, d'⟩) : AccKeep d d' :=
  ⟨(Devm.pop_of_pop h).accessedAddresses.symm, (Devm.pop_of_pop h).accessedStorageKeys.symm⟩

theorem accKeep_popToNat {d d' : Devm} {k : Nat} (h : Devm.popToNat d = .ok ⟨k, d'⟩) :
    AccKeep d d' := by
  obtain ⟨_, hp⟩ := Devm.pop_of_popToNat h
  exact ⟨hp.accessedAddresses.symm, hp.accessedStorageKeys.symm⟩

theorem accKeep_chargeGas {d d' : Devm} {c : Nat} (h : chargeGas c d = .ok d') : AccKeep d d' :=
  ⟨(Devm.burn_of_chargeGas h).accessedAddresses.symm,
    (Devm.burn_of_chargeGas h).accessedStorageKeys.symm⟩

theorem accKeep_push {d d' : Devm} {x : B256} (h : Devm.push x d = .ok d') : AccKeep d d' :=
  ⟨(Devm.push_of_push h).accessedAddresses.symm, (Devm.push_of_push h).accessedStorageKeys.symm⟩

theorem accKeep_memRead (d : Devm) (i n : Nat) : AccKeep d (d.memRead i n).2 := ⟨rfl, rfl⟩

theorem accKeep_pushItem {d d' : Devm} {x : B256} {c : Nat} (h : pushItem x c d = .ok d') :
    AccKeep d d' := by
  rw [pushItem_def] at h
  exact ⟨(Devm.pushBurn_of_run h).accessedAddresses.symm,
    (Devm.pushBurn_of_run h).accessedStorageKeys.symm⟩

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
    exact ⟨hd.accessedAddresses.symm, hd.accessedStorageKeys.symm⟩
  case iszero | not =>
    obtain ⟨_, hd⟩ := Devm.diffBurn_of_applyUnary h
    exact ⟨hd.accessedAddresses.symm, hd.accessedStorageKeys.symm⟩
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
      ((accKeep_popToNat h3).trans ((accKeep_chargeGas h4).trans ⟨rfl, rfl⟩)))
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
      ((accKeep_chargeGas h3).trans ⟨rfl, rfl⟩))
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
      exact (accKeep_chargeGas h1).trans ⟨rfl, rfl⟩
  case log n =>
    obtain ⟨⟨mi, d1⟩, h1, e1⟩ := Except.bind_eq_ok h
    obtain ⟨⟨sz, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
    obtain ⟨⟨tp, d3⟩, h3, e3⟩ := Except.bind_eq_ok e2
    obtain ⟨d4, h4, e4⟩ := Except.bind_eq_ok e3
    obtain ⟨_, h5, h6⟩ := Except.bind_eq_ok e4
    cases h6
    have hk3 : AccKeep d2 d3 :=
      ⟨(Devm.pop_of_popN h3).2.accessedAddresses.symm,
        (Devm.pop_of_popN h3).2.accessedStorageKeys.symm⟩
    exact (accKeep_popToNat h1).trans ((accKeep_popToNat h2).trans (hk3.trans
      ((accKeep_chargeGas h4).trans ⟨rfl, rfl⟩)))

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

/-- An interpreter configuration: the machine state, the node to run, the
continuations of the pending internal calls (innermost first), and a list
shadow of the accessed storage keys. -/
structure Cfg where
  devm : Devm
  f : SFunc
  K : List SFunc
  keys : List (Adr × B256)

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
    let v := c.devm.getStorVal ct k
    if sevm.benvStat.rules.stateGas.isNone ∧ s.length < 1024 then
      if (ct, k) ∈ c.keys then
        if gasWarmAccess ≤ c.devm.gasLeft then
          some ⟨mach' c.devm (v :: s) gasWarmAccess, g, c.K, c.keys⟩
        else none
      else if gasColdSload ≤ c.devm.gasLeft then
        some ⟨(addAccessedStorageKey c.devm ct k).setMach
            ⟨v :: s, c.devm.memory, c.devm.gasLeft - gasColdSload, c.devm.stateGas⟩,
          g, c.K, (ct, k) :: c.keys⟩
      else none
    else none
  | _ => none

/-- `SSTORE` at a key the shadow decides warm or cold (`Ninst.runCompiled_sstore_*`). -/
def sstoreStep (sevm : Sevm) (c : Cfg) (g : SFunc) : Option Cfg :=
  match c.devm.stack with
  | k :: v :: s =>
    let ct := sevm.currentTarget
    let orig := getOrigStorVal sevm ct k
    let cur := c.devm.getStorVal ct k
    let rc := sstoreNewRefundCounter sevm.benvStat.rules.gas v orig cur c.devm.refundCounter
    if sevm.benvStat.rules.stateGas.isNone ∧ gCallStipend < c.devm.gasLeft ∧
        sevm.isStatic = false then
      if (ct, k) ∈ c.keys then
        let cost := sstoreValueCost orig cur v
        if cost ≤ c.devm.gasLeft then
          some ⟨(devmSetStorValB (c.devm.withRefundCounter rc) ct k v).setMach
              ⟨s, c.devm.memory, c.devm.gasLeft - cost, c.devm.stateGas⟩, g, c.K, c.keys⟩
        else none
      else
        let cost := gasColdSload + sstoreValueCost orig cur v
        if cost ≤ c.devm.gasLeft then
          some ⟨(devmSetStorValB ((addAccessedStorageKey c.devm ct k).withRefundCounter rc) ct k v).setMach
              ⟨s, c.devm.memory, c.devm.gasLeft - cost, c.devm.stateGas⟩, g, c.K, (ct, k) :: c.keys⟩
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
        c.devm.stateGas⟩, g, c.K, c.keys⟩
    else none
  | _ => none

/-- `CALLDATACOPY` through `memWriteB` (`Ninst.runCompiled_calldatacopy_of`). -/
def calldatacopyStep (sevm : Sevm) (c : Cfg) (g : SFunc) : Option Cfg :=
  match c.devm.stack with
  | di :: si :: sz :: s =>
    let cost := gVerylow + gasCopy * ceilDiv sz.toNat 32 + c.devm.extCost [⟨di.toNat, sz.toNat⟩]
    if cost ≤ c.devm.gasLeft then
      some ⟨c.devm.setMach ⟨s, memWriteB c.devm.memory di.toNat (sevm.data.sliceD si.toNat sz.toNat 0),
        c.devm.gasLeft - cost, c.devm.stateGas⟩, g, c.K, c.keys⟩
    else none
  | _ => none

/-- One node of the certificate tree. -/
def wstep (fs : List SFunc) (sevm : Sevm) (c : Cfg) : Res :=
  match c.f with
  | .dest g =>
    if gJumpdest ≤ c.devm.gasLeft then .cont ⟨mach' c.devm c.devm.stack gJumpdest, g, c.K, c.keys⟩
    else .stuck
  | .jump k =>
    match c.devm.stack, fs[k]? with
    | _ :: s, some g =>
      if gMid ≤ c.devm.gasLeft then .cont ⟨mach' c.devm s gMid, g, c.K, c.keys⟩ else .stuck
    | _, _ => .stuck
  | .branch f g =>
    match c.devm.stack with
    | _ :: w :: s =>
      if gHigh ≤ c.devm.gasLeft then
        .cont ⟨mach' c.devm s gHigh, if w = 0 then f else g, c.K, c.keys⟩
      else .stuck
    | _ => .stuck
  | .branchTo f k =>
    match c.devm.stack with
    | _ :: w :: s =>
      if gHigh ≤ c.devm.gasLeft then
        if w = 0 then .cont ⟨mach' c.devm s gHigh, f, c.K, c.keys⟩
        else match fs[k]? with
          | some g => .cont ⟨mach' c.devm s gHigh, g, c.K, c.keys⟩
          | none => .stuck
      else .stuck
    | _ => .stuck
  | .callNext k f =>
    match c.devm.stack, fs[k]? with
    | _ :: s, some g =>
      if gMid ≤ c.devm.gasLeft then .cont ⟨mach' c.devm s gMid, g, f :: c.K, c.keys⟩ else .stuck
    | _, _ => .stuck
  | .ret =>
    match c.devm.stack with
    | _ :: s =>
      if gMid ≤ c.devm.gasLeft then
        match c.K with
        | [] => .done (.returned (mach' c.devm s gMid))
        | g :: K => .cont ⟨mach' c.devm s gMid, g, K, c.keys⟩
      else .stuck
    | _ => .stuck
  | .pcAt p g =>
    match Ninst.step ⟨p, sevm, c.devm⟩ (.reg .pc) with
    | .cont _ d => .cont ⟨d, g, c.K, c.keys⟩
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
    | .reg .calldatacopy => match calldatacopyStep sevm c g with | some c' => .cont c' | none => .stuck
    | n =>
      if ninstAccKeeps n then
        match Ninst.step ⟨0, sevm, c.devm⟩ n with
        | .cont _ d => .cont ⟨d, g, c.K, c.keys⟩
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

/-! ## Soundness -/

/-- `SFunc.RunExact` with a stack of pending internal-call continuations:
the current callee returns into the first, or the whole frame halts. -/
def RunK (fs : List SFunc) (sevm : Sevm) : Devm → SFunc → List SFunc → Outcome → Prop
  | devm, f, [], o => SFunc.RunExact fs sevm devm f o
  | devm, f, g :: K, o =>
    (∃ d, SFunc.RunExact fs sevm devm f (.returned d) ∧ RunK fs sevm d g K o) ∨
      (∃ d, o = .halted d ∧ SFunc.RunExact fs sevm devm f (.halted d))

/-- The shadow is the accessed-key set. -/
def Agree (c : Cfg) : Prop := ∀ x, x ∈ c.devm.accessedStorageKeys ↔ x ∈ c.keys

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
    (ha : AccKeep c.devm c'.devm) (hK : c'.K = c.K)
    (h : ∀ o, SFunc.RunExact fs sevm c'.devm c'.f o → SFunc.RunExact fs sevm c.devm c.f o) :
    StepOk fs sevm c c' := by
  refine ⟨fun hc x => ?_, fun o _ r => ?_⟩
  · rw [ha.2, hk]; exact hc x
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

theorem sloadStep_cont {fs : List SFunc} {sevm : Sevm} {c c' : Cfg} {g : SFunc}
    (h : sloadStep sevm c g = some c') (hf : c.f = .next (.reg .sload) g) :
    StepOk fs sevm c c' := by
  rcases c with ⟨devm, f, K, keys⟩
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
            .next (Ninst.runCompiled_sload_warm hleg' hs ((hc _).mpr hw) rfl
              (G := devm.gasLeft - gasWarmAccess) (by show devm.gasLeft = _; omega) hroom) r
        · cases h
      · rename_i hw
        split at h
        · rename_i hgas
          cases h
          exact StepOk.of (fun hc => agree_insert hc) rfl fun hc o r =>
            .next (Ninst.runCompiled_sload_cold hleg' hs (fun hm => hw ((hc _).mp hm)) rfl
              (G := devm.gasLeft - gasColdSload) (by show devm.gasLeft = _; omega) hroom) r
        · cases h
    · cases h
  · cases h

theorem sstoreStep_cont {fs : List SFunc} {sevm : Sevm} {c c' : Cfg} {g : SFunc}
    (h : sstoreStep sevm c g = some c') (hf : c.f = .next (.reg .sstore) g) :
    StepOk fs sevm c c' := by
  rcases c with ⟨devm, f, K, keys⟩
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
          refine StepOk.of (fun hc => hc) rfl fun hc o r => .next ?_ r
          have h := Ninst.runCompiled_sstore_warm hleg' hs ((hc _).mpr hw) hsentry hstatic rfl rfl
            (G := devm.gasLeft - _) (by exact (Nat.sub_add_cancel hgas).symm)
          rwa [devm_setStorVal_eq_B] at h
        · cases h
      · rename_i hw
        split at h
        · rename_i hgas
          cases h
          refine StepOk.of (fun hc => agree_insert hc) rfl fun hc o r => .next ?_ r
          have h := Ninst.runCompiled_sstore_cold hleg' hs (fun hm => hw ((hc _).mp hm)) hsentry
            hstatic rfl rfl (G := devm.gasLeft - _) (by exact (Nat.sub_add_cancel hgas).symm)
          rwa [devm_setStorVal_eq_B] at h
        · cases h
    · cases h
  · cases h

theorem generic_cont {fs : List SFunc} {sevm : Sevm} {c : Cfg} {n : Ninst} {g : SFunc}
    {q : Nat} {d : Devm} (hn : ninstAccKeeps n = true)
    (hstep : Ninst.step ⟨0, sevm, c.devm⟩ n = .cont q d) (hf : c.f = .next n g) :
    StepOk fs sevm c ⟨d, g, c.K, c.keys⟩ := by
  have hk := ninstAccKeeps_step hn hstep
  refine StepOk.of (fun hc x => ?_) rfl fun _ o r => ?_
  · show x ∈ d.accessedStorageKeys ↔ x ∈ c.keys
    rw [hk.2]; exact hc x
  · rw [hf]
    exact .next (Ninst.runCompiled_of_run (pcFree_of_ninstAccKeeps hn)
      ⟨.none, trivial, 0, by simp [Ninst.StepRun, hstep, Step.Run]⟩) r

theorem mstoreStep_cont {fs : List SFunc} {sevm : Sevm} {c c' : Cfg} {g : SFunc}
    (h : mstoreStep c g = some c') (hf : c.f = .next (.reg .mstore) g) :
    StepOk fs sevm c c' := by
  rcases c with ⟨devm, f, K, keys⟩
  simp only at hf; subst hf
  simp only [mstoreStep] at h
  split at h
  · rename_i i v s hs
    split at h
    · rename_i hgas
      cases h
      exact StepOk.same rfl (AccKeep.setMach _ _) rfl fun o r =>
        .next (Ninst.runCompiled_mstore hs (by exact (Nat.sub_add_cancel hgas).symm)
          (mem_write_eq_B _ _ _)) r
    · cases h
  · cases h

theorem calldatacopyStep_cont {fs : List SFunc} {sevm : Sevm} {c c' : Cfg} {g : SFunc}
    (h : calldatacopyStep sevm c g = some c') (hf : c.f = .next (.reg .calldatacopy) g) :
    StepOk fs sevm c c' := by
  rcases c with ⟨devm, f, K, keys⟩
  simp only at hf; subst hf
  simp only [calldatacopyStep] at h
  split at h
  · rename_i di si sz s hs
    split at h
    · rename_i hgas
      cases h
      exact StepOk.same rfl (AccKeep.setMach _ _) rfl fun o r =>
        .next (Ninst.runCompiled_calldatacopy_of hs rfl (mem_write_eq_B _ _ _)
          (by exact (Nat.sub_add_cancel hgas).symm)) r
    · cases h
  · cases h

theorem wstep_cont {fs : List SFunc} {sevm : Sevm} {c c' : Cfg}
    (h : wstep fs sevm c = .cont c') : StepOk fs sevm c c' := by
  rcases c with ⟨devm, f, K, keys⟩
  cases f with
  | dest g =>
    simp only [wstep] at h
    split at h
    · cases h
      refine StepOk.same rfl (AccKeep.setMach _ _) rfl fun o r => .dest ?_ r
      exact Devm.burnBy_setMach (by assumption)
    · cases h
  | jump k =>
    simp only [wstep] at h
    split at h
    · rename_i d s g hs hg
      split at h
      · cases h
        exact StepOk.same rfl (AccKeep.setMach _ _) rfl fun o r =>
          .jump d hg (popBurnBy1 hs (by assumption)) r
      · cases h
    · cases h
  | branch f g =>
    simp only [wstep] at h
    split at h
    · rename_i d w s hs
      split at h
      · cases h
        refine StepOk.same rfl (AccKeep.setMach _ _) rfl fun o r => ?_
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
          exact StepOk.same rfl (AccKeep.setMach _ _) rfl fun o r =>
            .toZero d (popBurnBy2 hs hgas) r
        · rename_i hw
          split at h
          · rename_i g hg
            cases h
            exact StepOk.same rfl (AccKeep.setMach _ _) rfl fun o r =>
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
        refine ⟨fun hc x => hc x, fun o _ r => ?_⟩
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
          refine ⟨fun hc x => hc x, fun o _ r => ?_⟩
          exact .inl ⟨_, .ret d (popBurnBy1 hs hgas), r⟩
      · cases h
    · cases h
  | pcAt p g =>
    simp only [wstep] at h
    split at h
    · rename_i q d hstep
      cases h
      refine StepOk.same rfl (pc_step_accKeep hstep) rfl fun o r => .pcAt ?_ r
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
      · cases h; exact calldatacopyStep_cont (by assumption) rfl
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
  rcases c with ⟨devm, f, K, keys⟩
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
    {keys : List (Adr × B256)} {n : Nat} (h0 : fs[0]? = some f0)
    (hagree : ∀ x, x ∈ pre.accessedStorageKeys ↔ x ∈ keys)
    (h : wrun fs sevm n ⟨pre, f0, [], keys⟩ = .done (.halted post)) :
    SProg.RunExact fs sevm pre post :=
  ⟨f0, h0, wrun_done h hagree⟩

end Blanc.Lift.Witness
