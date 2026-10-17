import Blanc.Composition.UniswapV2PairWeth9CapstoneKeySlots
import Blanc.Composition.UniswapV2PairWeth9W0
import Blanc.Lift.Weth9.FootHistory
import Blanc.Lift.UniswapV2Pair.PairHistory
import Blanc.Lift.Weth9.ClosedDeployment

/-!
# Both HASH-T premises of the closed history, discharged

`history_fresh`: for a configured history whose raw frames are frames at system addresses around
`tx1`'s frames (all at `X`) and the raw roots of one run of `tx2`'s swap frame, the keys WETH9's raw
frames touch are fresh against `W0`'s WETH9 rows, and the rows the Pair's raw frames select are fresh
against `W0`'s Pair rows.  Both by inclusion in a finite universe whose slots the kernel separated
(`UniswapV2PairWeth9CapstoneKeySlots`).
-/

namespace Blanc.Composition.UniswapV2PairWeth9Capstone

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.ExecutionTrace
  Blanc.Composition.UniswapV2PairWeth9Instance Blanc.Lift.FiniteCheckpoint
open Blanc.Lift.Weth9.ClosedInstance (systemAddresses)

theorem mem_of_all {α : Type} [DecidableEq α] {L U : List α}
    (h : L.all (fun x => decide (x ∈ U)) = true) {x : α} (hx : x ∈ L) : x ∈ U :=
  of_decide_eq_true (List.all_eq_true.mp h x hx)

theorem systemAddresses_ne {a r : Adr} (ha : a ∈ systemAddresses)
    (hr : r = weth ∨ r = pair) : a ≠ r := by
  simp only [systemAddresses, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases hr with rfl | rfl <;> rcases ha with rfl | rfl | rfl | rfl <;> decide +kernel

/-- Every raw frame of the closed history: at a system address, at `X`, the swap root, or one of
the swap's three callees. -/
theorem history_roots_cases {cfg : ChainConfig} {checkpoint future : BlockChain}
    {trace : ConfiguredHistoryTrace cfg checkpoint future}
    {t1raw sysRaw sysRaw' : List Exec.Deriv} {sevm : Sevm} {b : Devm} {G : Nat} {out : Execution}
    {run : Exec 0 sevm (St b [] Mem.empty G) out}
    (frames : trace.rawFrames = sysRaw ++ t1raw ++ Exec.rawFrameRoots run ++ sysRaw')
    (sys : ∀ r ∈ sysRaw ++ sysRaw', r.sevm.currentTarget ∈ systemAddresses)
    (one : ∀ d ∈ t1raw, d.sevm.currentTarget = tokenX)
    (callees : ∀ d ∈ Exec.rawFrameDescendants run, Tx2Callee d) :
    ∀ D ∈ trace.rawFrames, D.sevm.currentTarget ∈ systemAddresses ∨
      D.sevm.currentTarget = tokenX ∨ D = ⟨0, sevm, St b [] Mem.empty G, out, run⟩ ∨ Tx2Callee D := by
  intro D member
  rw [frames] at member
  simp only [List.mem_append] at member
  rcases member with ((hs | h1) | h2) | hs'
  · exact Or.inl (sys D (List.mem_append_left _ hs))
  · exact Or.inr (Or.inl (one D h1))
  · simp only [Exec.rawFrameRoots, List.mem_cons] at h2
    rcases h2 with rfl | hd
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (callees D hd)))
  · exact Or.inl (sys D (List.mem_append_right _ hs'))

theorem Tx2Callee.target_ne_pair {d : Exec.Deriv} (c : Tx2Callee d) : d.sevm.currentTarget ≠ pair := by
  rcases c with ⟨-, -, ⟨t, -⟩ | ⟨t, -⟩ | ⟨t, -⟩⟩ <;> rw [t] <;> decide +kernel

/-- **WETH9's HASH-T premise for the closed history.** -/
theorem history_wethFresh {cfg : ChainConfig} {checkpoint future : BlockChain}
    {trace : ConfiguredHistoryTrace cfg checkpoint future}
    (cases : ∀ D ∈ trace.rawFrames, D.sevm.currentTarget ∈ systemAddresses ∨
      D.sevm.currentTarget = tokenX ∨ D.sevm.currentTarget = pair ∨ Tx2Callee D) :
    Weth9.KeysFresh (rowKeys w0WethRows) (Weth9.historyTouchedKeys weth trace) := by
  have touched : ∀ k ∈ Weth9.historyTouchedKeys weth trace, k ∈ wethUniverse := by
    intro k hk
    obtain ⟨D, member, inD⟩ := List.mem_flatMap.mp hk
    by_cases target : D.sevm.currentTarget = weth
    · rw [ite_eq_left target] at inD
      rcases cases D member with hs | hx | hp | ⟨-, caller, ⟨-, data, -⟩ | ⟨tx, -⟩ | ⟨-, data, -⟩⟩
      · exact absurd target (systemAddresses_ne hs (Or.inl rfl))
      · rw [hx] at target; exact absurd target (by decide +kernel)
      · rw [hp] at target; exact absurd target (by decide +kernel)
      · rw [transfer_frameKeys caller data] at inD
        exact mem_of_all (by decide +kernel) inD
      · rw [tx] at target; exact absurd target (by decide +kernel)
      · rw [balance_frameKeys caller data] at inD
        exact mem_of_all (by decide +kernel) inD
    · rw [ite_eq_right target] at inD
      cases inD
  refine SlotFootprint.FreshKeys.of_universe (U := fun k => k ∈ wethUniverse)
    (fun k k' hk hk' same => List.inj_on_of_nodup_map wethUniverse_slots_nodup hk hk' same)
    (fun k hk => of_decide_eq_true (List.all_eq_true.mp wethUniverse_slots_apart k hk))
    (fun k hk => ?_) touched
  change k ∈ w0WethRows.map Prod.fst at hk
  exact mem_of_all (by decide +kernel) hk

theorem mintReplyRow_mem_of_word {out : Bytes} {w : Nat}
    (word : Bytes.toB256 (out.take 32) = Nat.toB256 w)
    (mem : WriterKey.balance (Nat.toB256 w).toAdr ∈ pairUniverse) : mintReplyRow out ∈ pairUniverse := by
  unfold mintReplyRow
  rw [word]
  exact mem

/-- **The Pair's HASH-T premise for the closed history.** -/
theorem history_pairFresh {cfg : ChainConfig} {checkpoint future : BlockChain}
    {trace : ConfiguredHistoryTrace cfg checkpoint future} {sevm : Sevm} {b : Devm} {G : Nat}
    {out : Execution} {run : Exec 0 sevm (St b [] Mem.empty G) out}
    (h : Tx2Frame sevm (St b [] Mem.empty G))
    (cases : ∀ D ∈ trace.rawFrames, D.sevm.currentTarget ∈ systemAddresses ∨
      D.sevm.currentTarget = tokenX ∨ D = ⟨0, sevm, St b [] Mem.empty G, out, run⟩ ∨ Tx2Callee D) :
    WriterFreshKeys (pairKeys w0PairRows) (pairHistoryTouchedKeys pair trace) := by
  obtain ⟨⟨P, outEq, outNil⟩, callees⟩ := tx2_swap_raw h run
  subst outEq
  have touched : ∀ k ∈ pairHistoryTouchedKeys pair trace, k ∈ pairUniverse := by
    intro k hk
    obtain ⟨D, member, inD⟩ := List.mem_flatMap.mp hk
    by_cases target : D.sevm.currentTarget = pair
    · rw [ite_eq_left target] at inD
      rcases cases D member with hs | hx | rfl | callee
      · exact absurd target (systemAddresses_ne hs (Or.inr rfl))
      · rw [hx] at target; exact absurd target (by decide +kernel)
      · obtain ⟨F, memF, inF⟩ := List.mem_flatMap.mp inD
        change F ∈ Exec.rawFrameRoots run at memF
        have rootOrCallee : F = ⟨0, sevm, St b [] Mem.empty G, .ok P, run⟩ ∨ Tx2Callee F := by
          simp only [Exec.rawFrameRoots, List.mem_cons] at memF
          rcases memF with rfl | hd
          · exact Or.inl rfl
          · exact Or.inr (callees F hd)
        by_cases same : F.sevm.currentTarget = sevm.currentTarget
        · rw [ite_eq_left same] at inF
          rcases rootOrCallee with rfl | callee
          · unfold pairFrameKeys at inF
            rw [swap_pairDecoded h.data, h.target] at inF
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at inF
            rcases inF with (rfl | rfl) | rfl | reply
            · exact mem_of_all (L := [WriterKey.balance 0]) (by decide +kernel) (List.mem_singleton_self _)
            · exact mem_of_all (L := [WriterKey.balance 0]) (by decide +kernel) (List.mem_singleton_self _)
            · exact mem_of_all (L := [WriterKey.balance pair]) (by decide +kernel) (List.mem_singleton_self _)
            · unfold mintFeeReplyKeys at reply
              rcases List.mem_append.mp reply with fromRoots | fromPrecompiles
              · obtain ⟨F', memF', eqF'⟩ := List.mem_filterMap.mp fromRoots
                change F' ∈ Exec.rawFrameRoots run at memF'
                simp only [Exec.rawFrameRoots, List.mem_cons] at memF'
                rcases memF' with rfl | hd
                · obtain rfl := Option.some.inj eqF'
                  rw [outNil]
                  exact mem_of_all (L := [mintReplyRow []]) (by decide +kernel) (List.mem_singleton_self _)
                · obtain ⟨-, -, ⟨-, -, cd, exn, output⟩ | ⟨-, cd, exn, word⟩ | ⟨-, -, cd, exn, word⟩⟩ :=
                    callees F' hd
                  · rw [exn] at eqF'
                    obtain rfl := Option.some.inj eqF'
                    rw [output]
                    exact mem_of_all (L := [mintReplyRow (Nat.toB256 1).toBytes]) (by decide +kernel)
                      (List.mem_singleton_self _)
                  · rw [exn] at eqF'
                    obtain rfl := Option.some.inj eqF'
                    exact mintReplyRow_mem_of_word word (by decide +kernel)
                  · rw [exn] at eqF'
                    obtain rfl := Option.some.inj eqF'
                    exact mintReplyRow_mem_of_word word (by decide +kernel)
              · change k ∈ precompileRunAddresses.filterMap (fun adr =>
                  (precompileAnswer (ExternalOperation.encode .feeTo) sevm.benvStat.rules.modexp
                    adr).map mintReplyRow) at fromPrecompiles
                rw [rules_bpo2 h.fork, feeTo_precompileRows] at fromPrecompiles
                exact mem_of_all feeToRows_sub fromPrecompiles
          · exact absurd (same.trans h.target) callee.target_ne_pair
        · rw [ite_eq_right same] at inF
          cases inF
      · exact absurd target callee.target_ne_pair
    · rw [ite_eq_right target] at inD
      cases inD
  refine SlotFootprint.FreshKeys.of_universe (U := fun k => k ∈ pairUniverse)
    (fun k k' hk hk' same => List.inj_on_of_nodup_map pairUniverse_slots_nodup hk hk' same)
    (fun k hk => of_decide_eq_true (List.all_eq_true.mp pairUniverse_slots_apart k hk))
    (fun k hk => ?_) touched
  change k ∈ (slotRows w0PairRows).map Prod.fst at hk
  rw [slotRows_keys] at hk
  exact mem_of_all (by decide +kernel) hk

end Blanc.Composition.UniswapV2PairWeth9Capstone
