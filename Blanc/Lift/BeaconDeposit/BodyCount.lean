import Blanc.Lift.BeaconDeposit.BodySpec

/-!
# Body segment 6: the root check, the cap guard and the count increment

From `0x0ea6` (tree `t_0ea6_c20`, the node in memory) to the insertion loop's head
(pc `0x0f6e`, tree `t_0f6e_c20`: the head's first pass, inlined in entry 20).
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

-- SEGMENT: countBump
/-- **Segment 6 (`0x0ea6 → 0x0f6e`, trees `t_0ea6_c20`, `t_0f02_c20`, `t_0f60_c20`, ending at
`t_0f6e_c20`).**  The node is loaded from `0x3a0` and compared with `deposit_data_root` (`EQ`,
the `JUMPI` jumps over the revert); `SLOAD 0x20` (warm) and the cap guard
`0xffffffff > count`; `SLOAD 0x20` again, `1 + count` stored back (`SSTORE`, warm key), and the
loop's height `0` pushed.  Memory is untouched.  281 gas and the `SSTORE`.

Proof sketch.  Straight-line `rx_*` steps: `rx_mload` (no expansion), `rx_eq` with `hroot`,
`rx_branch_succ`, twice `rx_sload_warm`, `rx_gt` with `hcap`, and the `SSTORE` through
`Ninst.runCompiled_sstore_selected_setMach` (sentry `hsentry`: the gas left after the
`SSTORE` is `G + 3`).  The post base is exactly `afterSstore`; memory is `M`. -/
theorem body_countBump {sevm : Sevm} {b : Devm} {sel rt sP wP pP a pkR sR nd : B256} {G : Nat}
    {M : Mem}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hwarm : (⟨sevm.currentTarget, solCountSlot⟩ : Adr × B256) ∈ b.accessedStorageKeys)
    (hroot : nd = rt)
    (hcap : (b.getStorVal sevm.currentTarget solCountSlot).toNat < 2 ^ 32 - 1)
    (hsentry : gCallStipend < G + 3 +
      sstoreCost sevm b solCountSlot (1 + b.getStorVal sevm.currentTarget solCountSlot))
    (hM : BodyMem M 1024 0x3a0 [(0x3a0, nd.toBytes)]) :
    ∃ b' M', Keep (afterSstore sevm b solCountSlot
        (1 + b.getStorVal sevm.currentTarget solCountSlot)) b' ∧
      BodyMem M' 1024 0x3a0 [] ∧
      ∀ o, SFunc.RunExact prog sevm
          (St b' [0, 1 + b.getStorVal sevm.currentTarget solCountSlot, nd, sR, pkR, 0x80, a, rt,
            96, sP, 32, wP, 48, pP, 0x01b8, sel] M' G) t_0f6e_c20 o →
        SFunc.RunExact prog sevm
          (St b [0x20, 0x3a0, 0, sR, pkR, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M
            (G + (281 + sstoreCost sevm b solCountSlot
              (1 + b.getStorVal sevm.currentTarget solCountSlot)))) t_0ea6_c20 o := by
  obtain ⟨hwf, hs, img, hr, hfp, hf⟩ := hM
  set w := b.getStorVal sevm.currentTarget solCountSlot
  have hnd : img.sliceD 928 32 0 = nd.toBytes := by
    have := hf (928, nd.toBytes) (by simp only [List.mem_cons, List.not_mem_nil, or_false])
    rwa [B256.length_toBytes] at this
  have hleg := hfork.rules_stateGas_none
  have hgt : B256.gtCheck (Bytes.toB256 [0xff, 0xff, 0xff, 0xff]) w = 1 := by
    rw [B256.gtCheck, ite_eq_left]
    show w < _
    rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0xff, 0xff, 0xff, 0xff]).toNat =
      2 ^ 32 - 1 from rfl]
    exact hcap
  refine ⟨_, M, Keep.refl _, ⟨hwf, hs, img, hr, hfp, by simp only [List.not_mem_nil,
    IsEmpty.forall_iff, implies_true]⟩, fun o k => ?_⟩
  rw [show G + (281 + sstoreCost sevm b solCountSlot (1 + w)) =
    ((G + 3) + sstoreCost sevm b solCountSlot (1 + w)) + 278 by omega]
  unfold t_0ea6_c20
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_mload (c := 3) (v := nd) ?_ ?_ ?_ (by simp only [List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  · rw [St.extCost_eq hs, show (928 : B256).toNat = 928 from rfl,
      memExtSize_of_le (by decide) (by decide)]
    rfl
  · rw [show (928 : B256).toNat = 928 from rfl, hr.read, hnd, B256.toB256_toBytes]
  · rw [show (928 : B256).toNat = 928 from rfl]
    exact Mem.read_snd_eq_self (by rw [hs]; exact memExtSize_of_le (by decide) (by decide))
  refine rx_swap1 ?_
  refine rx_pop ?_
  refine rx_dup (n := 5) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_eq (v := 1) (by rw [hroot]; simp only [B256.eqCheck, ↓reduceIte]) (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0f02_c20
  refine rx_dest ?_
  refine rx_push (w := solCountSlot) (by decide) (by simp only [List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_sload_warm hleg hwarm (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_gt hgt (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0f60_c20
  refine rx_dest ?_
  refine rx_push (w := solCountSlot) (by decide) (by simp only [List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup (n := 0) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_sload_warm hleg hwarm (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push (w := 1) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_add (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_dup (n := 1) rfl (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
    List.set_cons_zero, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_swap (n := 0) rfl ?_
  refine .next (Ninst.runCompiled_sstore_selected_setMach hfork (by omega) hstatic) ?_
  dsimp only [List.set]
  rw [← afterSstore_stateGas (sevm := sevm) (devm := b) (key := solCountSlot) (value := 1 + w)]
  refine rx_push (w := 0) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  exact k

end Blanc.Lift.BeaconDeposit
