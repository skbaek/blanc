import Blanc.Lift.SystemExecution.BeaconRoots.AmsterdamProbe
import Blanc.Lift.BuilderRequest.Deposit.Cert
import Blanc.Lift.ExactWalkOps
import Blanc.Lift.ExactWalkCutOps
import Blanc.Lift.ExactWalkSolc
import Blanc.Lift.CreationOps

/-!
# W1b probe, step 3: the deposit builder's drain under Amsterdam

Probe only (`blanc-eip8282-builder-requests-v1`, W1b); does not land. One exact iteration of the
certified queue body (six `SLOAD`s, nine word and eight byte memory writes, the back-edge), and the
bounded loop by induction, under `fork = .amsterdam`. No queue representation premise is used.
-/

namespace Blanc.Lift.BuilderRequest.AmsterdamProbe

open Jaune
open Blanc.Lift
open Blanc.Lift.BuilderRequest.Deposit

/-! ## `SLOAD` under Amsterdam -/

/-- The successor base of one `SLOAD` under EIP-2929 access with the EIP-7928 read record. Hoist
debt: the record is a no-op under `bal = none`, so this is the fork-uniform `afterSload`. -/
def afterSloadA (sevm : Sevm) (b : Devm) (key : B256) : Devm :=
  (afterSload sevm b key).balReadStorage sevm.benvStat.rules sevm.currentTarget key

theorem afterSloadA_stateGas (sevm : Sevm) (b : Devm) (key : B256) :
    (afterSloadA sevm b key).stateGas = b.stateGas := by
  unfold afterSloadA afterSload
  split <;> rfl

/-- One exact `SLOAD`, from the access schedule alone: no `stateGas` or `CoveredFork` premise. -/
theorem runCompiled_sloadA {sevm : Sevm} {b : Devm} {key : B256} {stack : List B256} {memory : Mem}
    {G : Nat} (hacc : sevm.benvStat.rules.access = .eip2929) (hroom : stack.length < 1024) :
    Ninst.RunCompiled sevm (St b (key :: stack) memory (G + sloadCost sevm b key)) (.reg .sload)
      (St (afterSloadA sevm b key) (b.getStorVal sevm.currentTarget key :: stack) memory G) := by
  refine Ninst.runCompiled_reg (by rintro ⟨⟩) ?_
  have hpop : (St b (key :: stack) memory (G + sloadCost sevm b key)).pop =
      .ok (key, St b stack memory (G + sloadCost sevm b key)) := rfl
  simp only [Rinst.runCore, hacc, bind, Except.bind]
  rw [hpop]
  simp only [bind, Except.bind, St.accessedStorageKeys]
  by_cases hw : (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈ b.accessedStorageKeys
  · simp only [hw, ↓reduceIte, sloadCost]
    rw [chargeGas_eq_ok (by show gasWarmAccess ≤ G + gasWarmAccess; omega)]
    simp only [bind, Except.bind]
    rw [Devm.push_eq_ok (by exact hroom)]
    have hg : (St b stack memory (G + gasWarmAccess)).gasLeft - gasWarmAccess = G :=
      Nat.add_sub_cancel _ _
    simp only [afterSloadA, afterSload, hw, ↓reduceIte, hg]
    rfl
  · simp only [hw, ↓reduceIte, sloadCost]
    rw [chargeGas_eq_ok (by show gasColdSload ≤ G + gasColdSload; omega)]
    simp only [bind, Except.bind]
    rw [Devm.push_eq_ok (by exact hroom)]
    have hg : (addAccessedStorageKey (St b stack memory (G + gasColdSload)) sevm.currentTarget
        key).gasLeft - gasColdSload = G := Nat.add_sub_cancel _ _
    simp only [afterSloadA, afterSload, hw, ↓reduceIte, hg]
    rfl

theorem rx_sloadA {fs : List SFunc} {sevm : Sevm} {b : Devm} {f : SFunc} {oc : Outcome}
    {S : List B256} {M : Mem} {G : Nat} {k' : B256}
    (hacc : sevm.benvStat.rules.access = .eip2929) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm
      (St (afterSloadA sevm b k') (b.getStorVal sevm.currentTarget k' :: S) M G) f oc) :
    SFunc.RunExact fs sevm (St b (k' :: S) M (G + sloadCost sevm b k')) (.next (.reg .sload) f) oc :=
  .next (runCompiled_sloadA hacc hroom) k

/-- The rule facts Amsterdam gives this walk. -/
theorem amsterdam_access {s : BenvStat} (h : s.fork = .amsterdam) :
    s.rules.access = .eip2929 := by
  show (Fork.ruleSet s.fork).access = _
  rw [h]; rfl

theorem amsterdam_shifts {s : BenvStat} (h : s.fork = .amsterdam) :
    s.rules.op.shifts = true := by
  show (Fork.ruleSet s.fork).op.shifts = _
  rw [h]; rfl

/-! ## Segments of the certified body, generic in the continuation -/

/-- The expansion-inclusive charge of one memory write. -/
def chg (M : Mem) (o : B256) (n : Nat) : Nat :=
  gVerylow + (calculateMemoryGasCost (memExtSize M.size o.toNat n) - calculateMemoryGasCost M.size)

section seg

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {f : SFunc} {oc : Outcome} {M : Mem} {G : Nat}

/-- `DUP2 PUSH1 k ADD SLOAD DUP2 MSTORE PUSH1 0x20 ADD`: read one record word, store it, advance. -/
theorem seg_word {k : UInt8} {kv o key : B256} {T : List B256} {le1 le2}
    (hacc : sevm.benvStat.rules.access = .eip2929) (hk : Bytes.toB256 [k] = kv)
    (hroom : T.length ≤ 1000)
    (next : SFunc.RunExact fs sevm
      (St (afterSloadA sevm b (kv + key)) (((32 : B256) + o) :: key :: T)
        (M.write o.toNat (b.getStorVal sevm.currentTarget (kv + key)).toBytes) G) f oc) :
    SFunc.RunExact fs sevm
      (St b (o :: key :: T) M (G + 18 + chg M o 32 + sloadCost sevm b (kv + key)))
      (.next (.reg (.dup 1)) (.next (.push [k] le1) (.next (.reg .add) (.next (.reg .sload)
        (.next (.reg (.dup 1)) (.next (.reg .mstore) (.next (.push [0x20] le2)
          (.next (.reg .add) f)))))))) oc := by
  have e : G + 18 + chg M o 32 + sloadCost sevm b (kv + key) =
      G + 3 + 3 + chg M o 32 + 3 + sloadCost sevm b (kv + key) + 3 + 3 + 3 := by omega
  rw [e]
  apply rx_dup2 (by rroom)
  apply rx_push hk (by rroom)
  apply rx_add' rfl (by rroom)
  apply rx_sloadA hacc (by rroom)
  apply rx_dup2 (by rroom)
  apply rx_mstore (Devm.extCost_add_of_size rfl rfl) rfl
  apply rx_push (w := (32 : B256)) (by decide) (by rroom)
  apply rx_add' rfl (by rroom)
  exact next

/-- `DUP2 SLOAD DUP2 MSTORE PUSH1 0x20 ADD`: the first word, at the key itself. -/
theorem seg_word0 {o key : B256} {T : List B256} {le2}
    (hacc : sevm.benvStat.rules.access = .eip2929) (hroom : T.length ≤ 1000)
    (next : SFunc.RunExact fs sevm
      (St (afterSloadA sevm b key) (((32 : B256) + o) :: key :: T)
        (M.write o.toNat (b.getStorVal sevm.currentTarget key).toBytes) G) f oc) :
    SFunc.RunExact fs sevm
      (St b (o :: key :: T) M (G + 12 + chg M o 32 + sloadCost sevm b key))
      (.next (.reg (.dup 1)) (.next (.reg .sload) (.next (.reg (.dup 1)) (.next (.reg .mstore)
        (.next (.push [0x20] le2) (.next (.reg .add) f)))))) oc := by
  have e : G + 12 + chg M o 32 + sloadCost sevm b key =
      G + 3 + 3 + chg M o 32 + 3 + sloadCost sevm b key + 3 := by omega
  rw [e]
  apply rx_dup2 (by rroom)
  apply rx_sloadA hacc (by rroom)
  apply rx_dup2 (by rroom)
  apply rx_mstore (Devm.extCost_add_of_size rfl rfl) rfl
  apply rx_push (w := (32 : B256)) (by decide) (by rroom)
  apply rx_add' rfl (by rroom)
  exact next

/-- `DUP2 PUSH1 2 ADD SLOAD DUP1 DUP3 MSTORE PUSH1 0x40 SHR PUSH8 mask AND`: the packed word, stored
whole, with its amount split out. -/
theorem seg_packed {o key mask : B256} {T : List B256} {xs : Bytes} {x : UInt8} {le1 le2 le3}
    (hacc : sevm.benvStat.rules.access = .eip2929)
    (hsh : sevm.benvStat.rules.op.shifts = true) (hmask : Bytes.toB256 (x :: xs) = mask)
    (hroom : T.length ≤ 1000)
    (next : SFunc.RunExact fs sevm
      (St (afterSloadA sevm b ((2 : B256) + key))
        ((mask &&& (b.getStorVal sevm.currentTarget ((2 : B256) + key) >>> 64)) :: o :: key :: T)
        (M.write o.toNat (b.getStorVal sevm.currentTarget ((2 : B256) + key)).toBytes) G) f oc) :
    SFunc.RunExact fs sevm
      (St b (o :: key :: T) M (G + 27 + chg M o 32 + sloadCost sevm b ((2 : B256) + key)))
      (.next (.reg (.dup 1)) (.next (.push [0x02] le1) (.next (.reg .add) (.next (.reg .sload)
        (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .mstore)
          (.next (.push [0x40] le2) (.next (.reg .shr) (.next (.push (x :: xs) le3)
            (.next (.reg .and) f))))))))))) oc := by
  have e : G + 27 + chg M o 32 + sloadCost sevm b ((2 : B256) + key) =
      G + 3 + 3 + 3 + 3 + chg M o 32 + 3 + 3 + sloadCost sevm b ((2 : B256) + key) + 3 + 3 + 3 := by
    omega
  rw [e]
  apply rx_dup2 (by rroom)
  apply rx_push (w := (2 : B256)) (by decide) (by rroom)
  apply rx_add' rfl (by rroom)
  apply rx_sloadA hacc (by rroom)
  apply rx_dup1 (by rroom)
  apply rx_dup3 (by rroom)
  apply rx_mstore (Devm.extCost_add_of_size rfl rfl) rfl
  apply rx_push (w := (64 : B256)) (by decide) (by rroom)
  apply rx_shr (v := b.getStorVal sevm.currentTarget ((2 : B256) + key) >>> 64) (by rfl) hsh (by rroom)
  apply rx_push hmask (by rroom)
  apply rx_and rfl (by rroom)
  exact next

/-- `DUP2 PUSH1 s SHR DUP2 PUSH1 n ADD MSTORE8`: one little-endian amount byte. -/
theorem seg_byte {s n : UInt8} {sn : Nat} {nv p a : B256} {T : List B256} {le1 le2}
    (hsh : sevm.benvStat.rules.op.shifts = true)
    (hs : (Bytes.toB256 [s]).toNat = sn) (hn : Bytes.toB256 [n] = nv)
    (hroom : T.length ≤ 1000)
    (next : SFunc.RunExact fs sevm
      (St b (p :: a :: T) (M.write (nv + p).toNat [(a >>> sn).2.2.toUInt8]) G) f oc) :
    SFunc.RunExact fs sevm (St b (p :: a :: T) M (G + 18 + chg M (nv + p) 1))
      (.next (.reg (.dup 1)) (.next (.push [s] le1) (.next (.reg .shr) (.next (.reg (.dup 1))
        (.next (.push [n] le2) (.next (.reg .add) (.next (.reg .mstore8) f))))))) oc := by
  have e : G + 18 + chg M (nv + p) 1 = G + chg M (nv + p) 1 + 3 + 3 + 3 + 3 + 3 + 3 := by omega
  rw [e]
  apply rx_dup2 (by rroom)
  apply rx_push rfl (by rroom)
  apply rx_shr (v := a >>> sn) (by rw [hs]) hsh (by rroom)
  apply rx_dup2 (by rroom)
  apply rx_push hn (by rroom)
  apply rx_add' rfl (by rroom)
  apply rx_mstore8 (Devm.extCost_add_of_size rfl rfl) rfl
  exact next

/-- `MSTORE8 PUSH1 0x20 ADD`: the amount's low byte, then the next word's offset. -/
theorem seg_low {p a o key : B256} {T : List B256} {le}
    (hroom : T.length ≤ 1000)
    (next : SFunc.RunExact fs sevm
      (St b (((32 : B256) + o) :: key :: T) (M.write p.toNat [a.2.2.toUInt8]) G) f oc) :
    SFunc.RunExact fs sevm (St b (p :: a :: o :: key :: T) M (G + 6 + chg M p 1))
      (.next (.reg .mstore8) (.next (.push [0x20] le) (.next (.reg .add) f))) oc := by
  have e : G + 6 + chg M p 1 = G + 3 + 3 + chg M p 1 := by omega
  rw [e]
  apply rx_mstore8 (Devm.extCost_add_of_size rfl rfl) rfl
  apply rx_push (w := (32 : B256)) (by decide) (by rroom)
  apply rx_add' rfl (by rroom)
  exact next

/-- `SWAP1 PUSH1 5 ADD SLOAD SWAP1 MSTORE`: the last word, which consumes the key. -/
theorem seg_word5 {o key : B256} {T : List B256} {le}
    (hacc : sevm.benvStat.rules.access = .eip2929) (hroom : T.length ≤ 1000)
    (next : SFunc.RunExact fs sevm
      (St (afterSloadA sevm b ((5 : B256) + key)) T
        (M.write o.toNat (b.getStorVal sevm.currentTarget ((5 : B256) + key)).toBytes) G) f oc) :
    SFunc.RunExact fs sevm
      (St b (o :: key :: T) M (G + 12 + chg M o 32 + sloadCost sevm b ((5 : B256) + key)))
      (.next (.reg (.swap 0)) (.next (.push [0x05] le) (.next (.reg .add) (.next (.reg .sload)
        (.next (.reg (.swap 0)) (.next (.reg .mstore) f)))))) oc := by
  have e : G + 12 + chg M o 32 + sloadCost sevm b ((5 : B256) + key) =
      G + chg M o 32 + 3 + sloadCost sevm b ((5 : B256) + key) + 3 + 3 + 3 := by omega
  rw [e]
  apply rx_swap1
  apply rx_push (w := (5 : B256)) (by decide) (by rroom)
  apply rx_add' rfl (by rroom)
  apply rx_sloadA hacc (by rroom)
  apply rx_swap1
  apply rx_mstore (Devm.extCost_add_of_size rfl rfl) rfl
  exact next

/-- `DUP2 PUSH1 0x10 ADD`: the amount's byte pointer. -/
theorem seg_ptr {o a : B256} {T : List B256} {le}
    (hroom : T.length ≤ 1000)
    (next : SFunc.RunExact fs sevm (St b (((16 : B256) + o) :: a :: o :: T) M G) f oc) :
    SFunc.RunExact fs sevm (St b (a :: o :: T) M (G + 9))
      (.next (.reg (.dup 1)) (.next (.push [0x10] le) (.next (.reg .add) f))) oc := by
  have e : G + 9 = G + 3 + 3 + 3 := by omega
  rw [e]
  apply rx_dup2 (by rroom)
  apply rx_push (w := (16 : B256)) (by decide) (by rroom)
  apply rx_add' rfl (by rroom)
  exact next

end seg

/-! ## One iteration: the record's reads, writes and charges in execution order -/

section body

variable (sevm : Sevm) (base : Devm) (head index : B256) (M : Mem)

def dKey : B256 := (4 : B256) + (6 : B256) * (index + head)
def dOff : B256 := (184 : B256) * index

def dB1 : Devm := afterSloadA sevm base (dKey head index)
def dB2 : Devm := afterSloadA sevm (dB1 sevm base head index) ((1 : B256) + dKey head index)
def dB3 : Devm := afterSloadA sevm (dB2 sevm base head index) ((2 : B256) + dKey head index)
def dB4 : Devm := afterSloadA sevm (dB3 sevm base head index) ((3 : B256) + dKey head index)
def dB5 : Devm := afterSloadA sevm (dB4 sevm base head index) ((4 : B256) + dKey head index)
/-- The base after the iteration's six reads. -/
def dB6 : Devm := afterSloadA sevm (dB5 sevm base head index) ((5 : B256) + dKey head index)

def dW0 : B256 := base.getStorVal sevm.currentTarget (dKey head index)
def dW1 : B256 := (dB1 sevm base head index).getStorVal sevm.currentTarget
  ((1 : B256) + dKey head index)
def dW2 : B256 := (dB2 sevm base head index).getStorVal sevm.currentTarget
  ((2 : B256) + dKey head index)
def dW3 : B256 := (dB3 sevm base head index).getStorVal sevm.currentTarget
  ((3 : B256) + dKey head index)
def dW4 : B256 := (dB4 sevm base head index).getStorVal sevm.currentTarget
  ((4 : B256) + dKey head index)
def dW5 : B256 := (dB5 sevm base head index).getStorVal sevm.currentTarget
  ((5 : B256) + dKey head index)

def dMask : B256 := Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
def dAmt : B256 := dMask &&& (dW2 sevm base head index >>> 64)

def dO1 : B256 := (32 : B256) + dOff index
def dO2 : B256 := (32 : B256) + dO1 index
def dP : B256 := (16 : B256) + dO2 index
def dO3 : B256 := (32 : B256) + dO2 index
def dO4 : B256 := (32 : B256) + dO3 index
def dO5 : B256 := (32 : B256) + dO4 index

def dM1 : Mem := M.write (dOff index).toNat (dW0 sevm base head index).toBytes
def dM2 : Mem := (dM1 sevm base head index M).write (dO1 index).toNat (dW1 sevm base head index).toBytes
def dM3 : Mem := (dM2 sevm base head index M).write (dO2 index).toNat (dW2 sevm base head index).toBytes
def dAt (n : B256) : B256 := n + dP index
def dByte (sn : Nat) : UInt8 := (dAmt sevm base head index >>> sn).2.2.toUInt8
def dM4 : Mem := (dM3 sevm base head index M).write (dAt index 7).toNat [dByte sevm base head index 56]
def dM5 : Mem := (dM4 sevm base head index M).write (dAt index 6).toNat [dByte sevm base head index 48]
def dM6 : Mem := (dM5 sevm base head index M).write (dAt index 5).toNat [dByte sevm base head index 40]
def dM7 : Mem := (dM6 sevm base head index M).write (dAt index 4).toNat [dByte sevm base head index 32]
def dM8 : Mem := (dM7 sevm base head index M).write (dAt index 3).toNat [dByte sevm base head index 24]
def dM9 : Mem := (dM8 sevm base head index M).write (dAt index 2).toNat [dByte sevm base head index 16]
def dM10 : Mem := (dM9 sevm base head index M).write (dAt index 1).toNat [dByte sevm base head index 8]
def dM11 : Mem := (dM10 sevm base head index M).write (dP index).toNat
  [(dAmt sevm base head index).2.2.toUInt8]
def dM12 : Mem := (dM11 sevm base head index M).write (dO3 index).toNat (dW3 sevm base head index).toBytes
def dM13 : Mem := (dM12 sevm base head index M).write (dO4 index).toNat (dW4 sevm base head index).toBytes
/-- Memory after the iteration's fourteen writes. -/
def dM14 : Mem := (dM13 sevm base head index M).write (dO5 index).toNat (dW5 sevm base head index).toBytes

/-- The iteration's gas: 34 + 12 + 18 + 27 + 9 + 7 * 18 + 6 + 18 + 18 + 12 + 17 fixed, and the
selected charges. Gas against the rule record: `sloadCost` and `chg`. -/
def dGas : Nat :=
  297 +
  sloadCost sevm base (dKey head index) +
  sloadCost sevm (dB1 sevm base head index) ((1 : B256) + dKey head index) +
  sloadCost sevm (dB2 sevm base head index) ((2 : B256) + dKey head index) +
  sloadCost sevm (dB3 sevm base head index) ((3 : B256) + dKey head index) +
  sloadCost sevm (dB4 sevm base head index) ((4 : B256) + dKey head index) +
  sloadCost sevm (dB5 sevm base head index) ((5 : B256) + dKey head index) +
  chg M (dOff index) 32 +
  chg (dM1 sevm base head index M) (dO1 index) 32 +
  chg (dM2 sevm base head index M) (dO2 index) 32 +
  chg (dM3 sevm base head index M) (dAt index 7) 1 +
  chg (dM4 sevm base head index M) (dAt index 6) 1 +
  chg (dM5 sevm base head index M) (dAt index 5) 1 +
  chg (dM6 sevm base head index M) (dAt index 4) 1 +
  chg (dM7 sevm base head index M) (dAt index 3) 1 +
  chg (dM8 sevm base head index M) (dAt index 2) 1 +
  chg (dM9 sevm base head index M) (dAt index 1) 1 +
  chg (dM10 sevm base head index M) (dP index) 1 +
  chg (dM11 sevm base head index M) (dO3 index) 32 +
  chg (dM12 sevm base head index M) (dO4 index) 32 +
  chg (dM13 sevm base head index M) (dO5 index) 32

end body

/-- The prefix: compute the record's key and memory offset. -/
theorem seg_start {fs : List SFunc} {sevm : Sevm} {b : Devm} {f : SFunc} {oc : Outcome} {M : Mem}
    {G : Nat} {i c h t : B256} {le1 le2 le3}
    (next : SFunc.RunExact fs sevm
      (St b [dOff i, dKey h i, i, c, h, t] M G) f oc) :
    SFunc.RunExact fs sevm (St b [i, c, h, t] M (G + 34))
      (.next (.reg (.dup 2)) (.next (.reg (.dup 1)) (.next (.reg .add) (.next (.push [0x06] le1)
        (.next (.reg .mul) (.next (.push [0x04] le2) (.next (.reg .add) (.next (.reg (.dup 1))
          (.next (.push [0xb8] le3) (.next (.reg .mul) f)))))))))) oc := by
  have e : G + 34 = G + 5 + 3 + 3 + 3 + 3 + 5 + 3 + 3 + 3 + 3 := by omega
  rw [e]
  apply rx_dup3 (by rroom)
  apply rx_dup2 (by rroom)
  apply rx_add' rfl (by rroom)
  apply rx_push (w := (6 : B256)) (by decide) (by rroom)
  apply rx_mul rfl (by rroom)
  apply rx_push (w := (4 : B256)) (by decide) (by rroom)
  apply rx_add' rfl (by rroom)
  apply rx_dup2 (by rroom)
  apply rx_push (w := (184 : B256)) (by decide) (by rroom)
  apply rx_mul rfl (by rroom)
  exact next

/-- **One exact iteration of the deposit builder's certified drain under Amsterdam**, ending on the
loop's back-edge. Any storage, any memory. -/
theorem drainBody_exact {sevm : Sevm} {base : Devm} {M : Mem} {gas : Nat} {i c h t : B256}
    {oc : Outcome} (hfork : sevm.benvStat.fork = .amsterdam)
    (next : SFunc.RunExact cert.prog sevm
      (St (dB6 sevm base h i) [(1 : B256) + i, c, h, t] (dM14 sevm base h i M) gas)
      t_0133_c7 oc) :
    SFunc.RunExact cert.prog sevm (St base [i, c, h, t] M (gas + dGas sevm base h i M))
      t_013b_c2 oc := by
  have hacc := amsterdam_access (s := sevm.benvStat) hfork
  have hsh := amsterdam_shifts (s := sevm.benvStat) hfork
  -- The back-edge: `PUSH1 1 ADD PUSH2 0x133 JUMP`.
  have s17 : SFunc.RunExact cert.prog sevm
      (St (dB6 sevm base h i) [i, c, h, t] (dM14 sevm base h i M) (gas + 17))
      (.next (.push [0x01] (by decide)) (.next (.reg .add) (.next (.push [0x01, 0x33] (by decide))
        (.jump 7)))) oc := by
    have e : gas + 17 = gas + 8 + 3 + 3 + 3 := by omega
    rw [e]
    apply rx_push (w := (1 : B256)) (by decide) (by rroom)
    apply rx_add' rfl (by rroom)
    apply rx_push rfl (by rroom)
    exact rx_jump rfl next
  have s5 := seg_word5 (M := dM13 sevm base h i M) (b := dB5 sevm base h i) (o := dO5 i)
    (key := dKey h i) (T := [i, c, h, t]) (le := by decide) hacc (by rroom) s17
  have s4 := seg_word (k := 0x04) (kv := 4) (M := dM12 sevm base h i M) (b := dB4 sevm base h i) (o := dO4 i)
    (key := dKey h i) (T := [i, c, h, t]) (le1 := by decide) (le2 := by decide) hacc
    (by decide) (by rroom) s5
  have s3 := seg_word (k := 0x03) (kv := 3) (M := dM11 sevm base h i M) (b := dB3 sevm base h i) (o := dO3 i)
    (key := dKey h i) (T := [i, c, h, t]) (le1 := by decide) (le2 := by decide) hacc
    (by decide) (by rroom) s4
  have low := seg_low (M := dM10 sevm base h i M) (b := dB3 sevm base h i) (p := dP i)
    (a := dAmt sevm base h i) (o := dO2 i) (key := dKey h i) (T := [i, c, h, t])
    (le := by decide) (by rroom) s3
  have b1 := seg_byte (s := 0x08) (n := 0x01) (sn := 8) (nv := 1) (M := dM9 sevm base h i M)
    (b := dB3 sevm base h i) (p := dP i) (a := dAmt sevm base h i)
    (T := [dO2 i, dKey h i, i, c, h, t]) (le1 := by decide) (le2 := by decide) hsh (by decide)
    (by decide) (by rroom) low
  have b2 := seg_byte (s := 0x10) (n := 0x02) (sn := 16) (nv := 2) (M := dM8 sevm base h i M)
    (b := dB3 sevm base h i) (p := dP i) (a := dAmt sevm base h i)
    (T := [dO2 i, dKey h i, i, c, h, t]) (le1 := by decide) (le2 := by decide) hsh (by decide)
    (by decide) (by rroom) b1
  have b3 := seg_byte (s := 0x18) (n := 0x03) (sn := 24) (nv := 3) (M := dM7 sevm base h i M)
    (b := dB3 sevm base h i) (p := dP i) (a := dAmt sevm base h i)
    (T := [dO2 i, dKey h i, i, c, h, t]) (le1 := by decide) (le2 := by decide) hsh (by decide)
    (by decide) (by rroom) b2
  have b4 := seg_byte (s := 0x20) (n := 0x04) (sn := 32) (nv := 4) (M := dM6 sevm base h i M)
    (b := dB3 sevm base h i) (p := dP i) (a := dAmt sevm base h i)
    (T := [dO2 i, dKey h i, i, c, h, t]) (le1 := by decide) (le2 := by decide) hsh (by decide)
    (by decide) (by rroom) b3
  have b5 := seg_byte (s := 0x28) (n := 0x05) (sn := 40) (nv := 5) (M := dM5 sevm base h i M)
    (b := dB3 sevm base h i) (p := dP i) (a := dAmt sevm base h i)
    (T := [dO2 i, dKey h i, i, c, h, t]) (le1 := by decide) (le2 := by decide) hsh (by decide)
    (by decide) (by rroom) b4
  have b6 := seg_byte (s := 0x30) (n := 0x06) (sn := 48) (nv := 6) (M := dM4 sevm base h i M)
    (b := dB3 sevm base h i) (p := dP i) (a := dAmt sevm base h i)
    (T := [dO2 i, dKey h i, i, c, h, t]) (le1 := by decide) (le2 := by decide) hsh (by decide)
    (by decide) (by rroom) b5
  have b7 := seg_byte (s := 0x38) (n := 0x07) (sn := 56) (nv := 7) (M := dM3 sevm base h i M)
    (b := dB3 sevm base h i) (p := dP i) (a := dAmt sevm base h i)
    (T := [dO2 i, dKey h i, i, c, h, t]) (le1 := by decide) (le2 := by decide) hsh (by decide)
    (by decide) (by rroom) b6
  have ptr := seg_ptr (M := dM3 sevm base h i M) (b := dB3 sevm base h i) (o := dO2 i)
    (a := dAmt sevm base h i) (T := [dKey h i, i, c, h, t]) (le := by decide) (by rroom) b7
  have pk := seg_packed (M := dM2 sevm base h i M) (b := dB2 sevm base h i) (o := dO2 i)
    (key := dKey h i) (mask := dMask) (T := [i, c, h, t]) (x := 0xff)
    (xs := [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff])
    (le1 := by decide) (le2 := by decide) (le3 := by decide) hacc hsh rfl (by rroom) ptr
  have w1 := seg_word (k := 0x01) (kv := 1) (M := dM1 sevm base h i M) (b := dB1 sevm base h i) (o := dO1 i)
    (key := dKey h i) (T := [i, c, h, t]) (le1 := by decide) (le2 := by decide) hacc
    (by decide) (by rroom) pk
  have w0 := seg_word0 (M := M) (b := base) (o := dOff i)
    (key := dKey h i) (T := [i, c, h, t]) (le2 := by decide) hacc (by rroom) w1
  have st := seg_start (le1 := by decide) (le2 := by decide) (le3 := by decide) w0
  have e : ∀ g, gas + dGas sevm base h i M = g →
      SFunc.RunExact cert.prog sevm (St base [i, c, h, t] M g) t_013b_c2 oc →
      SFunc.RunExact cert.prog sevm (St base [i, c, h, t] M (gas + dGas sevm base h i M))
        t_013b_c2 oc := fun _ hg r => hg ▸ r
  refine e _ ?_ st
  simp only [dGas, dAt]
  omega

end Blanc.Lift.BuilderRequest.AmsterdamProbe
