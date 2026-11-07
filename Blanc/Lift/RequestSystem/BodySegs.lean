import Blanc.Lift.AmsterdamWalk
import Blanc.Lift.ExactWalkOps
import Blanc.Lift.ExactWalkCutOps
import Blanc.Lift.ExactWalkSolc
import Blanc.Lift.CreationOps
import Blanc.MemoryStageGas

/-!
# The segments a request contract's record body is made of

Each record body computes its key and offset, then reads a slot and writes a window, word by word, and
some recode an amount little-endian byte by byte. These are those segments as exact steps under Amsterdam,
at any storage and any memory, each with its expansion-inclusive charge `chg`.
-/

namespace Blanc.Lift.RequestSystem

open Jaune

/-- The expansion-inclusive charge of one memory write. -/
def chg (M : Mem) (o : B256) (n : Nat) : Nat :=
  gVerylow + (calculateMemoryGasCost (memExtSize M.size o.toNat n) - calculateMemoryGasCost M.size)

section seg

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {f : SFunc} {oc : Outcome} {M : Mem} {G : Nat}

/-- `DUP2 PUSH1 k ADD SLOAD DUP2 MSTORE PUSH1 0x20 ADD`: read one record word, store it, advance. -/
theorem seg_word {k : UInt8} {kv o key v : B256} {T : List B256} {le1 le2}
    (hacc : sevm.benvStat.rules.access = .eip2929) (hk : Bytes.toB256 [k] = kv)
    (hroom : T.length ≤ 1000) (hv : b.getStorVal sevm.currentTarget (kv + key) = v)
    (next : SFunc.RunExact fs sevm
      (St (afterSloadA sevm b (kv + key)) (((32 : B256) + o) :: key :: T)
        (M.write o.toNat v.toBytes) G) f oc) :
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
  apply rx_sloadV hacc (by rroom) hv
  apply rx_dup2 (by rroom)
  apply rx_mstore (Devm.extCost_add_of_size rfl rfl) rfl
  apply rx_push (w := (32 : B256)) (by decide) (by rroom)
  apply rx_add' rfl (by rroom)
  exact next

/-- `DUP2 SLOAD DUP2 MSTORE PUSH1 0x20 ADD`: the first word, at the key itself. -/
theorem seg_word0 {o key v : B256} {T : List B256} {le2}
    (hacc : sevm.benvStat.rules.access = .eip2929) (hroom : T.length ≤ 1000)
    (hv : b.getStorVal sevm.currentTarget key = v)
    (next : SFunc.RunExact fs sevm
      (St (afterSloadA sevm b key) (((32 : B256) + o) :: key :: T)
        (M.write o.toNat v.toBytes) G) f oc) :
    SFunc.RunExact fs sevm
      (St b (o :: key :: T) M (G + 12 + chg M o 32 + sloadCost sevm b key))
      (.next (.reg (.dup 1)) (.next (.reg .sload) (.next (.reg (.dup 1)) (.next (.reg .mstore)
        (.next (.push [0x20] le2) (.next (.reg .add) f)))))) oc := by
  have e : G + 12 + chg M o 32 + sloadCost sevm b key =
      G + 3 + 3 + chg M o 32 + 3 + sloadCost sevm b key + 3 := by omega
  rw [e]
  apply rx_dup2 (by rroom)
  apply rx_sloadV hacc (by rroom) hv
  apply rx_dup2 (by rroom)
  apply rx_mstore (Devm.extCost_add_of_size rfl rfl) rfl
  apply rx_push (w := (32 : B256)) (by decide) (by rroom)
  apply rx_add' rfl (by rroom)
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

/-- `SWAP1 PUSH1 k ADD SLOAD SWAP1 MSTORE`: a record's last word, which consumes the key. -/
theorem seg_last {k : UInt8} {kv o key v : B256} {T : List B256} {le}
    (hacc : sevm.benvStat.rules.access = .eip2929) (hk : Bytes.toB256 [k] = kv)
    (hroom : T.length ≤ 1000) (hv : b.getStorVal sevm.currentTarget (kv + key) = v)
    (next : SFunc.RunExact fs sevm
      (St (afterSloadA sevm b (kv + key)) T (M.write o.toNat v.toBytes) G) f oc) :
    SFunc.RunExact fs sevm
      (St b (o :: key :: T) M (G + 12 + chg M o 32 + sloadCost sevm b (kv + key)))
      (.next (.reg (.swap 0)) (.next (.push [k] le) (.next (.reg .add) (.next (.reg .sload)
        (.next (.reg (.swap 0)) (.next (.reg .mstore) f)))))) oc := by
  have e : G + 12 + chg M o 32 + sloadCost sevm b (kv + key) =
      G + chg M o 32 + 3 + sloadCost sevm b (kv + key) + 3 + 3 + 3 := by omega
  rw [e]
  apply rx_swap1
  apply rx_push hk (by rroom)
  apply rx_add' rfl (by rroom)
  apply rx_sloadV hacc (by rroom) hv
  apply rx_swap1
  apply rx_mstore (Devm.extCost_add_of_size rfl rfl) rfl
  exact next

/-- `DUP2 SLOAD PUSH1 0x60 SHL DUP2 MSTORE PUSH1 0x14 ADD`: the source address, shifted to the top of its
word, and the next write 20 bytes on. -/
theorem seg_source {o key v : B256} {T : List B256} {le1 le2}
    (hacc : sevm.benvStat.rules.access = .eip2929) (hsh : sevm.benvStat.rules.op.shifts = true)
    (hroom : T.length ≤ 1000) (hv : b.getStorVal sevm.currentTarget key = v)
    (next : SFunc.RunExact fs sevm
      (St (afterSloadA sevm b key) (((20 : B256) + o) :: key :: T)
        (M.write o.toNat (v <<< 96).toBytes) G) f oc) :
    SFunc.RunExact fs sevm
      (St b (o :: key :: T) M (G + 18 + chg M o 32 + sloadCost sevm b key))
      (.next (.reg (.dup 1)) (.next (.reg .sload) (.next (.push [0x60] le1) (.next (.reg .shl)
        (.next (.reg (.dup 1)) (.next (.reg .mstore) (.next (.push [0x14] le2)
          (.next (.reg .add) f)))))))) oc := by
  have e : G + 18 + chg M o 32 + sloadCost sevm b key =
      G + 3 + 3 + chg M o 32 + 3 + 3 + 3 + sloadCost sevm b key + 3 := by omega
  rw [e]
  apply rx_dup2 (by rroom)
  apply rx_sloadV hacc (by rroom) hv
  apply rx_push (w := (96 : B256)) (by decide) (by rroom)
  apply rx_shl (v := v <<< 96) (by rfl) hsh (by rroom)
  apply rx_dup2 (by rroom)
  apply rx_mstore (Devm.extCost_add_of_size rfl rfl) rfl
  apply rx_push (w := (20 : B256)) (by decide) (by rroom)
  apply rx_add' rfl (by rroom)
  exact next

/-- `DUP3 DUP2 ADD PUSH1 w MUL PUSH1 4 ADD DUP2 PUSH1 l MUL`: a record's key at width `w` and its memory
offset at length `l`. -/
theorem seg_start {w l : UInt8} {wv lv i c h t : B256} {le1 le2 le3}
    (hw : Bytes.toB256 [w] = wv) (hl : Bytes.toB256 [l] = lv)
    (next : SFunc.RunExact fs sevm
      (St b [lv * i, (4 : B256) + wv * (i + h), i, c, h, t] M G) f oc) :
    SFunc.RunExact fs sevm (St b [i, c, h, t] M (G + 34))
      (.next (.reg (.dup 2)) (.next (.reg (.dup 1)) (.next (.reg .add) (.next (.push [w] le1)
        (.next (.reg .mul) (.next (.push [0x04] le2) (.next (.reg .add) (.next (.reg (.dup 1))
          (.next (.push [l] le3) (.next (.reg .mul) f)))))))))) oc := by
  have e : G + 34 = G + 5 + 3 + 3 + 3 + 3 + 5 + 3 + 3 + 3 + 3 := by omega
  rw [e]
  apply rx_dup3 (by rroom)
  apply rx_dup2 (by rroom)
  apply rx_add' rfl (by rroom)
  apply rx_push hw (by rroom)
  apply rx_mul rfl (by rroom)
  apply rx_push (w := (4 : B256)) (by decide) (by rroom)
  apply rx_add' rfl (by rroom)
  apply rx_dup2 (by rroom)
  apply rx_push hl (by rroom)
  apply rx_mul rfl (by rroom)
  exact next

end seg

end Blanc.Lift.RequestSystem
