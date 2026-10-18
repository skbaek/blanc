import Blanc.Lift.Curve3Crv.Exec
import Blanc.StorageAccessGas

/-!
# 3Crv: the body costs as bounds (goal amendment §13)

The liveness form `BodyLive` (`Spec.lean`) states a body's exact cost behind an existential, so
nothing public bounds it uniformly over worlds.  A caller that must budget the call for every world
it admits (the pool's 3Crv call premises, `Curve3Pool/LivePremises.lean`) needs the bound.  This
file exposes the cost each existing walk already chooses, as a bound, for the three bodies the pool
calls; no existing statement changes.

* `BodyLiveLe sevm b f r U` (`Spec.lean`): `BodyLive` with the cost at most `U`
  (`BodyLiveLe.live` forgets it);
* `live_totalSupply_le`: `totalSupply()`, `34 + sloadCost ≤ 34 + 2100`;
* `live_mint_le`, `live_burnFrom_le` (`LiveBodies.lean`, beside `live_mint` and `live_burnFrom`,
  which they imply): `2119` (`2107`) gas of fixed charges, three `SLOAD`s and two `SSTORE`s, each
  at most a cold access (`sloadCost_le`) or a cold fresh set (`sstoreCost_le`);
* `c3crv_exec_le`: the dispatcher's `dispatchGas k` on top, as a real execution of the deployed
  runtime.  Unlike `c3crv_exec` it asks no `isStatic = false`: the bound is the body's, and a
  `totalSupply()` body runs in a static frame.

The `mint` and `burnFrom` bounds are the walks of `live_mint` and `live_burnFrom`, which conclude
`BodyLiveLe` and forget the bound there; this file keeps `totalSupply()` and the dispatcher lift.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune

section

variable {sevm : Sevm} {b : Devm}

local notation "stor₀" => Devm.getStor b sevm.currentTarget

/-- `totalSupply()` costs at most `34 + 2100`: 34 gas and the `SLOAD` of slot 5. -/
theorem live_totalSupply_le (hfork : CoveredFork sevm.benvStat.fork) {r : Raw}
    (hr : rawTotalSupply sevm stor₀ = some r) :
    BodyLiveLe sevm b t_0240_c0 r (34 + 2100) := by
  unfold rawTotalSupply at hr
  split_ifs at hr with hv
  cases hr
  have hcost := Blanc.sloadCost_le sevm b vySupplySlot
  have hcs : gasColdSload = 2100 := rfl
  refine ⟨34 + sloadCost sevm b vySupplySlot, by omega, fun G _ => ?_⟩
  have hsz := vyMem_empty_size (Sevm.dataWord sevm 0)
  obtain ⟨post, hrun, hg, hl⟩ := word_tail (b := b) hfork (vyMem_wf Mem.wf_empty _)
    (vyMem_reads Mem.wf_empty Mem.reads_empty _) (by rw [hsz]; omega) (by rw [hsz]) vySupplySlot G
  refine ⟨post, ?_, hg, hl⟩
  unfold entrySt t_0240_c0
  rw [show G + (34 + sloadCost sevm b vySupplySlot) =
    G + 3 + 3 + 3 + 3 + sloadCost sevm b vySupplySlot + 3 + 1 + 10 + 3 + 3 + 2 by omega]
  refine rx_callvalue (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  rw [hv]
  refine rx_iszero (v := 1) (by simp only [B256.eqCheck, ↓reduceIte])
    (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.one_lt_ofNat]) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_024a_c0
  refine rx_dest ?_
  refine rx_push (w := vySupplySlot) rfl (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  exact hrun

end

/-- **A bounded body is a real execution of the deployed runtime within its bound plus the
dispatcher's** (`c3crv_exec` with the cost bounded; no `isStatic` premise). -/
theorem c3crv_exec_le {sevm : Sevm} {pre : Devm} {k : Nat} {f : SFunc} {r : Raw} {U : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hf : bodies[k]? = some f) (hk : sels[k]? = some (Sevm.selector sevm))
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hb : BodyLiveLe sevm pre f r U) :
    ∃ c ≤ U + dispatchGas k, ∀ G, gCallStipend < G → ∃ post,
      Nonempty (Exec 0 sevm (St pre [] Mem.empty (G + c)) (.ok post)) ∧ post.gasLeft = G ∧
        Lands sevm pre post r := by
  obtain ⟨c, hcU, hc⟩ := hb
  refine ⟨c + dispatchGas k, by omega, fun G hG => ?_⟩
  obtain ⟨post, hrun, hg, hl⟩ := hc G hG
  have hd := live_dispatch hf hk rfl hlen hcd hrun
  rw [← Nat.add_assoc]
  exact ⟨post, exec_of_runExact hcode hfork ⟨_, rfl, hd⟩, hg, hl⟩

end Blanc.Lift.Curve3Crv
