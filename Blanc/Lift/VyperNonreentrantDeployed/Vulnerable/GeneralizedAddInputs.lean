import Blanc.Lift.WitnessMapping
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolReRun3
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame4ChunkB

/-! A connected recipient-dependent mapping read/write cut of the add frame.
Only the selected forty instructions are generalized here. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.GeneralizedAddInputs

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.WitnessMapping
open Blanc.Lift.VyperNonreentrantDeployed

/-- The exact continuation immediately after the first mapping SSTORE. -/
def mintRest : SFunc := match t_0744_c4 with
  | .next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ f)))))))) => f
  | _ => .undefined

def mintMemory (M : Mem) (A : Adr) : Mem :=
  ((M.write 544 (2106 : B256).toBytes).write 224 A.toB256.toBytes).write 192 (24 : B256).toBytes

def mintEntry (b : Devm) (M : Mem) (G : Nat) (S : List B256) (K : List SFunc)
    (keys : List (Adr × B256)) (adrs : List Adr) (stor : StorShadow) (acs : AcctShadow) : Cfg :=
  ⟨St b (106 :: 2000 :: 544 :: S) M (G + 5155), t_071a_c4, K, keys, adrs, stor, acs⟩

def mintPost (s : Sevm) (b : Devm) (M : Mem) (G : Nat) (A : Adr) (S : List B256)
    (K : List SFunc) (keys : List (Adr × B256)) (adrs : List Adr)
    (stor : StorShadow) (acs : AcctShadow) : Cfg :=
  let h := mapSlot 24 A.toB256
  ⟨St ((addAccessedStorageKey b s.currentTarget h).setStorVal s.currentTarget h 2106)
      (h :: S) (mintMemory M A) G,
    mintRest, K, (s.currentTarget, h) :: keys, adrs, ((s.currentTarget, h), 2106) :: stor, acs⟩

def mintRead : SFunc :=
  .next (.reg (.dup 0)) (.next (.reg .sload) (.next (.push [2, 224] (by decide))
    (.next (.reg .mload) (.next (.reg (.dup 1)) (.next (.reg (.dup 1))
    (.next (.reg (.dup 3)) (.next (.reg .add) (.next (.reg .lt)
    (.next (.push [68, 122] (by decide)) (.branch t_0744_c4 t_447a_c4))))))))))

private theorem mint_prefix (s : Sevm) (b : Devm) (M : Mem) (G : Nat) (A : Adr)
    (S : List B256) (K : List SFunc) (keys : List (Adr × B256)) (adrs : List Adr)
    (stor : StorShadow) (acs : AcctShadow)
    (hroom : S.length + 7 < 1024) (hsize : M.size = 1120)
    (hreadA : Bytes.toB256 ((M.write 544 (2106 : B256).toBytes).read 320 32).1 = A.toB256) :
    wrun (Cert.prog cert) s 13 (mintEntry b M G S K keys adrs stor acs) =
      .cont (slotEntry b (M.write 544 (2106 : B256).toBytes) (G + 5059)
        24 A.toB256 S mintRead K keys adrs stor acs) := by
  have hs : (M.write 544 (2106 : B256).toBytes).size = 1120 := by
    rw [Mem.size_write_word_at, hsize, ite_eq_left (by decide)]
  have hc0 := Devm.extCost_zero_of_le (devm := b) (S := S) (G := 0)
    (i := 544) (sz := 32) (by rw [hsize]) (by rw [hsize]; decide)
  have hc1 := Devm.extCost_zero_of_le (devm := b) (S := S) (G := 0)
    (N := M.write 544 (2106 : B256).toBytes) (i := 320) (sz := 32)
    (by rw [hs]) (by rw [hs]; decide)
  simp only [Devm.extCost, Devm.memory_setMach] at hc0 hc1
  have hm : (M.write 544 (2106 : B256).toBytes).extend 320 32 =
      M.write 544 (2106 : B256).toBytes :=
    Mem.read_snd_eq_self (memExtSize_of_le (by rw [hs]) (by rw [hs]; decide))
  simp only [Mem.read, array_sliceD_eq_list] at hreadA
  have hw24 : Bytes.toB256 [24] = 24 := rfl
  have hw320 : Bytes.toB256 [1, 64] = 320 := rfl
  have hn544 : (544 : B256).toNat = 544 := rfl
  have hn320 : (320 : B256).toNat = 320 := rfl
  have hadd : (2000 : B256) + 106 = 2106 := by decide
  have hgstore : 3 ≤ G + 5155 - 3 - 3 - 3 - 3 - 2 - 3 - 2 - 3 := by omega
  have hgload : 3 ≤ G + 5155 - 3 - 3 - 3 - 3 - 2 - 3 - 2 - 3 - 3 - 2 - 3 - 3 ∧ S.length + 1 < 1024 := by constructor <;> omega
  have hgas : G + 5155 - 3 - 3 - 3 - 3 - 2 - 3 - 2 - 3 - 3 - 2 - 3 - 3 - 3 = G + 5059 + 60 := by omega
  have hf1 : ((1 : Fin 16) : Nat) = 1 := rfl
  have hf2 : ((2 : Fin 16) : Nat) = 2 := rfl
  simp only [mintEntry, slotEntry]
  iterate 13
    rw [wrun]
    simp (disch := simp only [Devm.gasLeft, Devm.stack, Devm.setMach, List.length_cons]; clear hreadA hs hc0 hc1 hm hadd hsize hw24 hw320 hn544 hn320; first | omega | constructor <;> omega) only
      [wstep, t_071a_c4, ninstAccKeeps, rinstAccKeeps, Ninst.step_reg, Ninst.step_push,
      Rinst.run, Rinst.runCore, St, Devm.setMach, Devm.gasLeft, Devm.stack,
      Devm.memory, Devm.stateGas, Devm.pop_def, chargeGas_eq_ok, Devm.push_eq_ok,
      Devm.withStack, applyBinary_def, pushItem_def, Jaune.List.swap,
      Fin.getElem?_fin, Fin.val_zero,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.set_cons_zero,
      gBase, gVerylow, bind, Except.bind, Except.map_ok, Option.bind_some, Step.ofExecution,
      List.length_cons, List.length_nil, List.cons_ne_nil, Nat.reduceAdd, Nat.zero_add,
      ite_true, ite_false, and_true, mstoreStep, mloadStep, Devm.extCost,
      hgstore, hgload, hf1, hf2, hw24, hw320, hn544, hn320, hc0, hc1, hm, hreadA, hadd, ← mem_write_eq_B]
  simp only [wrun, vySlot, mintRead, hgas]

private theorem mint_tail (s : Sevm) (b : Devm) (M : Mem) (G : Nat) (A : Adr)
    (S : List B256) (K : List SFunc) (keys : List (Adr × B256)) (adrs : List Adr)
    (stor : StorShadow) (acs : AcctShadow)
    (hroom : S.length + 7 < 1024) (hsize : M.size = 1120)
    (hreadV : Bytes.toB256 ((mintMemory M A).read 736 32).1 = 106)
    (hcur : lookupS stor s.currentTarget (mapSlot 24 A.toB256) = 2000)
    (horig : getOrigStorVal s s.currentTarget (mapSlot 24 A.toB256) = 2000)
    (hcold : (s.currentTarget, mapSlot 24 A.toB256) ∉ keys)
    (hstateGas : s.benvStat.rules.stateGas = none) (hstatic : s.isStatic = false) :
    wrun (Cert.prog cert) s 20
      (slotPost b (M.write 544 (2106 : B256).toBytes) (G + 5059)
        24 A.toB256 S mintRead K keys adrs stor acs) =
      .cont (mintPost s b M G A S K keys adrs stor acs) := by
  have hs : (mintMemory M A).size = 1120 := by
    simp only [mintMemory]
    rw [Mem.size_write_word_at, Mem.size_write_word_at, Mem.size_write_word_at, hsize]
    decide
  have hc := Devm.extCost_zero_of_le (devm := b) (S := S) (G := 0)
    (N := mintMemory M A) (i := 736) (sz := 32) (by rw [hs]) (by rw [hs]; decide)
  simp only [Devm.extCost, Devm.memory_setMach] at hc
  have hm : (mintMemory M A).extend 736 32 = mintMemory M A :=
    Mem.read_snd_eq_self (memExtSize_of_le (by rw [hs]) (by rw [hs]; decide))
  simp only [Mem.read, array_sliceD_eq_list] at hreadV
  have hf1 : ((1 : Fin 16) : Nat) = 1 := rfl
  have hf2 : ((2 : Fin 16) : Nat) = 2 := rfl
  have hf3 : ((3 : Fin 16) : Nat) = 3 := rfl
  have hw736 : Bytes.toB256 [2, 224] = 736 := rfl
  have hn736 : (736 : B256).toNat = 736 := rfl
  have hwDest : Bytes.toB256 [68, 122] = 17530 := rfl
  have hadd : (2000 : B256) + 106 = 2106 := by decide
  have hadd' : (106 : B256) + 2000 = 2106 := by decide
  have hlt : B256.ltCheck 2106 2000 = 0 := by decide
  have hne : (2000 : B256) ≠ 2106 := by decide
  have hz0 : (2000 : B256) ≠ 0 := by decide
  have hz1 : (2106 : B256) ≠ 0 := by decide
  have hsload : s.benvStat.rules.stateGas.isNone ∧ (mapSlot 24 A.toB256 :: S).length < 1024 := by
    simp only [hstateGas, Option.isNone_none, List.length_cons, true_and]
    omega
  have hr1 : S.length + 1 < 1024 := by omega
  have hgasload : 2100 ≤ G + 5059 - 3 := by omega
  have hbranch : 10 ≤ G + 5059 - 3 - 2100 - 3 - 3 - 3 - 3 - 3 - 3 - 3 - 3 := by omega
  have hmload : 3 ≤ G + 5059 - 3 - 2100 - 3 ∧ S.length + 1 + 1 < 1024 := by
    constructor <;> omega
  change wrun (Cert.prog cert) s 20
    ⟨St b (mapSlot 24 A.toB256 :: S) (mintMemory M A) (G + 5059),
      mintRead, K, keys, adrs, stor, acs⟩ = .cont (mintPost s b M G A S K keys adrs stor acs)
  iterate 19
    rw [wrun]
    simp (disch := simp only [Devm.gasLeft, Devm.stack, Devm.setMach, List.length_cons]; clear hreadV hs hc hm hcur horig hcold hsize hw736 hn736 hwDest hadd hadd' hlt hne hz0 hz1 hsload hstateGas hstatic hf1 hf2 hf3; first | omega | constructor <;> omega) only
      [wstep, mach', mintRead, t_0744_c4, ninstAccKeeps, rinstAccKeeps,
      Ninst.step_reg, Ninst.step_push, Rinst.run, Rinst.runCore,
      St, Devm.setMach, Devm.gasLeft, Devm.stack, Devm.memory, Devm.stateGas,
      Devm.pop_def, chargeGas_eq_ok, Devm.push_eq_ok, Devm.withStack,
      applyBinary_def, pushItem_def, Jaune.List.swap, Fin.getElem?_fin,
      Fin.val_zero, hf1, hf2, hf3, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.set_cons_zero, gBase, gVerylow, gHigh,
      gasColdSload, gasWarmAccess, bind, Except.bind, Except.map_ok,
      Option.bind_some, Step.ofExecution, List.length_cons, List.length_nil,
      List.cons_ne_nil, Nat.reduceAdd, Nat.zero_add, ite_true, ite_false,
      sloadStep, mloadStep, Devm.extCost, hc, hm, hreadV,
      hw736, hn736, hwDest, hadd, hlt,
      hbranch, hr1, hgasload, hmload, hcur, hcold, hstateGas,
      Option.isNone_none, and_self]
  have hg : G + 5059 - 3 - 2100 - 3 - 3 - 3 - 3 - 3 - 3 - 3 - 3 - 10 - 3 - 3 - 3 - 3 - 2 - 3 - 2 - 3 = G + 2900 := by omega
  have hsent : 2300 < G + 2900 := by omega
  have hpay : 2900 ≤ G + 2900 := by omega
  have hfinal : G + 2900 - 2900 = G := Nat.add_sub_cancel G 2900
  have hrc (r : Int) : sstoreNewRefundCounter s.benvStat.rules.gas 2106 2000 2000 r = r := by
    simp only [sstoreNewRefundCounter, ne_eq, hne, hz0, hz1, not_false_eq_true, ite_self, ite_false, and_false]
  simp only [hg]
  rw [wrun]
  simp only [wstep, sstoreStep, St, Devm.setMach, Devm.gasLeft, Devm.stack,
    Devm.memory, Devm.stateGas, hcur, horig, hstateGas, hstatic, Option.isNone_none,
    gCallStipend, hsent, List.mem_cons, and_self, true_or,
    sstoreValueCost, ne_eq, hne, hz0, not_false_eq_true, hrc, gasStorageUpdate, gasColdSload, Nat.reduceSub,
    hpay, hfinal, ite_true, ite_false, wrun, mintPost, mintRest,
    Devm.withRefundCounter, Devm.refundCounter, addAccessedStorageKey, Devm.setStorVal]
  rfl

/-- Symbolic owner and recipient: the address-dependent hash is actually read,
the overflow guard passes, and the exact selected SSTORE is executed.
All read/warm/original facts are local input facts, not cut-success premises. -/
theorem mint_cut (s : Sevm) (b : Devm) (M : Mem) (G : Nat) (A : Adr)
    (S : List B256) (K : List SFunc) (keys : List (Adr × B256)) (adrs : List Adr)
    (stor : StorShadow) (acs : AcctShadow)
    (hroom : S.length + 7 < 1024) (hsize : M.size = 1120)
    (hreadA : Bytes.toB256 ((M.write 544 (2106 : B256).toBytes).read 320 32).1 = A.toB256)
    (hreadV : Bytes.toB256 ((mintMemory M A).read 736 32).1 = 106)
    (hcur : lookupS stor s.currentTarget (mapSlot 24 A.toB256) = 2000)
    (horig : getOrigStorVal s s.currentTarget (mapSlot 24 A.toB256) = 2000)
    (hcold : (s.currentTarget, mapSlot 24 A.toB256) ∉ keys)
    (hstateGas : s.benvStat.rules.stateGas = none) (hstatic : s.isStatic = false) :
    wrun (Cert.prog cert) s 40 (mintEntry b M G S K keys adrs stor acs) =
      .cont (mintPost s b M G A S K keys adrs stor acs) := by
  have hp := mint_prefix s b M G A S K keys adrs stor acs hroom hsize hreadA
  have hs : (M.write 544 (2106 : B256).toBytes).size = 1120 := by
    rw [Mem.size_write_word_at, hsize, ite_eq_left (by decide)]
  have hh := slot_run (Cert.prog cert) s b (M.write 544 (2106 : B256).toBytes)
    (G + 5059) 24 A.toB256 S mintRead K keys adrs stor acs
    (by omega) (by rw [hs]; decide) (by rw [hs])
  have ht := mint_tail s b M G A S K keys adrs stor acs hroom hsize hreadV
    hcur horig hcold hstateGas hstatic
  exact wrun_add_cont hp (wrun_add_cont hh ht)

/-- Finite local inputs consumed by the connected theorem. The successful
execution is derived from these observations, not stored in this predicate. -/
def mintObs (s : Sevm) (A : Adr) : Res → Bool
  | .cont c =>
    decide (c.devm.stack = 106 :: 2000 :: 544 :: c.devm.stack.drop 3) &&
    decide (5155 ≤ c.devm.gasLeft) &&
    decide ((c.devm.stack.drop 3).length + 7 < 1024) &&
    decide (c.devm.memory.size = 1120) &&
    decide (Bytes.toB256 ((c.devm.memory.write 544 (2106 : B256).toBytes).read 320 32).1 = A.toB256) &&
    decide (Bytes.toB256 ((mintMemory c.devm.memory A).read 736 32).1 = 106) &&
    decide (lookupS c.stor s.currentTarget (mapSlot 24 A.toB256) = 2000) &&
    decide (getOrigStorVal s s.currentTarget (mapSlot 24 A.toB256) = 2000) &&
    decide ((s.currentTarget, mapSlot 24 A.toB256) ∉ c.keys) &&
    s.benvStat.rules.stateGas.isNone && !s.isStatic
  | _ => false

/-- The same symbolic theorem consumes each concrete prefix's finite inputs. -/
theorem mint_from_obs (s : Sevm) (c : Cfg) (A : Adr)
    (hnode : c.f = t_071a_c4) (h : mintObs s A (.cont c) = true) :
    wrun (Cert.prog cert) s 40 c =
      .cont (mintPost s c.devm c.devm.memory (c.devm.gasLeft - 5155) A
        (c.devm.stack.drop 3) c.K c.keys c.adrs c.stor c.acs) := by
  simp only [mintObs, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hstack, hgas⟩, hroom⟩, hsize⟩, hreadA⟩, hreadV⟩, hcur⟩, horig⟩, hcold⟩, hstate⟩, hstatic⟩
  have hstateGas : s.benvStat.rules.stateGas = none := by
    cases he : s.benvStat.rules.stateGas with
    | none => rfl
    | some v => simp only [he, Option.isNone_some, Bool.false_eq_true] at hstate
  have hstatic0 : s.isStatic = false := by
    cases he : s.isStatic with
    | false => rfl
    | true => simp only [he, Bool.not_true, Bool.false_eq_true] at hstatic
  have hm : St c.devm c.devm.stack c.devm.memory c.devm.gasLeft = c.devm := by
    cases c.devm
    rfl
  have hshape : mintEntry c.devm c.devm.memory (c.devm.gasLeft - 5155)
      (c.devm.stack.drop 3) c.K c.keys c.adrs c.stor c.acs = c := by
    unfold mintEntry
    rw [Nat.sub_add_cancel hgas, ← hstack, hm, ← hnode]
  have hr := mint_cut s c.devm c.devm.memory (c.devm.gasLeft - 5155) A
    (c.devm.stack.drop 3) c.K c.keys c.adrs c.stor c.acs hroom hsize hreadA hreadV
    hcur horig hcold hstateGas hstatic0
  rw [hshape] at hr
  exact hr

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.GeneralizedAddInputs
