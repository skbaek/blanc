import Blanc.Lift.Vyper
import Blanc.Lift.RunEx
import Blanc.ConcreteRun

/-!
# A Vyper selector dispatcher, forward and gas-exact, by evaluation

The forward twin of `Blanc/Lift/VyperDispatchWalk.lean`, over a lifted program's trees: after
the prologue (`vyMem Mem.empty w`), a Vyper 0.2 dispatcher is a chain of trees

* tests `PUSH4 c PUSH1 0 MLOAD EQ ISZERO PUSH2 _ JUMPI` (`.branch hit miss`, 28 gas either way),
* always-taken skips `PUSH1 0 ISZERO PUSH2 _ JUMPI` (`.branch _ next`, 19 gas),
* `JUMPDEST`s (`.dest`, 1 gas).

`SFunc.vyFwd σ n t` evaluates that chain for the selector `σ`: the tree it reaches (the hit arm
of the first test of `σ`, or the first tree of neither shape) and the gas spent on the way.  For a
concrete program the kernel computes both (`kernel_rfl`), and `rx_vyFwd`/`rxe_vyFwd` turn a run
of the reached tree into a run of the chain's head with exactly that much more gas.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- The tree the dispatcher chain from `t` hands the selector `σ`, within `n` steps, and the
gas spent reaching it. -/
def SFunc.vyFwd (σ : B256) : Nat → SFunc → SFunc × Nat
  | 0, t => (t, 0)
  | n + 1, .dest t => ((SFunc.vyFwd σ n t).1, (SFunc.vyFwd σ n t).2 + 1)
  | n + 1, t@(.next (.push [c0, c1, c2, c3] _) (.next (.push [z] _) (.next (.reg .mload)
      (.next (.reg .eq) (.next (.reg .iszero) (.next (.push [_, _] _) (.branch f g))))))) =>
      if z = 0 then
        if Bytes.toB256 [c0, c1, c2, c3] = σ then (f, 28)
        else ((SFunc.vyFwd σ n g).1, (SFunc.vyFwd σ n g).2 + 28)
      else (t, 0)
  | n + 1, t@(.next (.push [z] _) (.next (.reg .iszero) (.next (.push [_, _] _)
      (.branch _ g)))) =>
      if z = 0 then ((SFunc.vyFwd σ n g).1, (SFunc.vyFwd σ n g).2 + 19) else (t, 0)
  | _ + 1, t => (t, 0)

section Fwd

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {o : Outcome}

local notation "Mv" => vyMem Mem.empty (Sevm.dataWord sevm 0)

/-- `MLOAD` at offset `0` of the prologue's memory reads the selector and keeps the memory. -/
theorem vyMem_mload_selector :
    Bytes.toB256 ((Mv).read (Bytes.toB256 [0x00]).toNat 32).1 = Sevm.selector sevm ∧
      ((Mv).read (Bytes.toB256 [0x00]).toNat 32).2 = Mv := by
  have h0 : (Bytes.toB256 [0x00]).toNat = 0 := by decide
  rw [h0, (vyMem_reads Mem.wf_empty Mem.reads_empty _).read, vyImg_selector]
  exact ⟨rfl, read_covered (vyMem_empty_size _) (by decide) (by decide)⟩

/-- **The chain, forward**: a run of the tree the chain hands the frame's selector is a run of
the chain's head, for the chain's gas more. -/
theorem rx_vyFwd {σ : B256} (hσ : Sevm.selector sevm = σ) (hS : S.length + 1 < 1024)
    (n : Nat) (t : SFunc) {G : Nat}
    (k : SFunc.RunExact fs sevm (St b S Mv G) (SFunc.vyFwd σ n t).1 o) :
    SFunc.RunExact fs sevm (St b S Mv (G + (SFunc.vyFwd σ n t).2)) t o := by
  obtain ⟨hs, hM⟩ := vyMem_mload_selector (sevm := sevm)
  have step : ∀ {c0 c1 c2 c3 h l : UInt8} {l1 l2 l3} {f g : SFunc} {v : B256} {G' : Nat},
      B256.eqCheck (B256.eqCheck (Sevm.selector sevm) (Bytes.toB256 [c0, c1, c2, c3])) 0 = v →
      SFunc.RunExact fs sevm (St b (Bytes.toB256 [h, l] :: v :: S) Mv G') (.branch f g) o →
      SFunc.RunExact fs sevm (St b S Mv (G' + 18))
        (.next (.push [c0, c1, c2, c3] l1) (.next (.push [0] l2) (.next (.reg .mload)
          (.next (.reg .eq) (.next (.reg .iszero) (.next (.push [h, l] l3)
          (.branch f g))))))) o := by
    intro c0 c1 c2 c3 h l l1 l2 l3 f g v G' hv k'
    rw [show G' + 18 = G' + 3 + 3 + 3 + 3 + 3 + 3 by omega]
    refine rx_push rfl (by omega) ?_
    refine rx_push rfl (by simp only [List.length_cons]; omega) ?_
    refine rx_mload (c := 3) ?_ hs hM (by simp only [List.length_cons]; omega) ?_
    · rw [St, Devm.extCost_zero_of_le (by rw [vyMem_empty_size]) (by
        rw [vyMem_empty_size]; decide)]; rfl
    refine rx_eq rfl (by omega) ?_
    refine rx_iszero hv (by omega) ?_
    exact rx_push rfl (by simp only [List.length_cons]; omega) k'
  fun_induction SFunc.vyFwd σ n t generalizing G with
  | case1 => exact k
  | case2 n t ih =>
      rw [← Nat.add_assoc]
      exact rx_dest (ih k)
  | case3 n c0 c1 c2 c3 =>
      rename_i hc _
      subst hc
      rw [show G + 28 = G + 10 + 18 by omega]
      exact step (v := 0) (by simp only [B256.eqCheck, hσ, ↓reduceIte,
        ite_eq_right_iff, imp_self]) (rx_branch_zero k)
  | case4 n c0 c1 c2 c3 =>
      rename_i g hc _ ih
      have hne : Sevm.selector sevm ≠ Bytes.toB256 [c0, c1, c2, c3] :=
        fun e => hc (e.symm.trans hσ)
      rw [← Nat.add_assoc, show G + (SFunc.vyFwd σ n g).2 + 28 =
        G + (SFunc.vyFwd σ n g).2 + 10 + 18 by omega]
      exact step (v := 1) (by simp only [B256.eqCheck, hne, ↓reduceIte])
        (rx_branch_succ (by decide) (ih k))
  | case5 => exact k
  | case6 n =>
      rename_i g _ ih
      rw [← Nat.add_assoc, show G + (SFunc.vyFwd σ n g).2 + 19 =
        G + (SFunc.vyFwd σ n g).2 + 10 + 3 + 3 + 3 by omega]
      refine rx_push rfl (by omega) ?_
      refine rx_iszero rfl (by omega) ?_
      refine rx_push rfl (by simp only [List.length_cons]; omega) ?_
      exact rx_branch_succ (by decide) (ih k)
  | case7 => exact k
  | case8 => exact k

/-- `rx_vyFwd` to some outcome. -/
theorem rxe_vyFwd {σ : B256} (hσ : Sevm.selector sevm = σ) (hS : S.length + 1 < 1024)
    (n : Nat) (t : SFunc) {G : Nat} {Q : Outcome → Prop}
    (k : SFunc.RunEx fs sevm (St b S Mv G) (SFunc.vyFwd σ n t).1 Q) :
    SFunc.RunEx fs sevm (St b S Mv (G + (SFunc.vyFwd σ n t).2)) t Q :=
  let ⟨r, hr, hq⟩ := k; ⟨r, rx_vyFwd hσ hS n t hr, hq⟩

end Fwd

end Blanc.Lift
