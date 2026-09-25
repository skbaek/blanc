import Blanc.Lift.BalSilent
import Blanc.Lift.Weth9.Contract
import Blanc.Lift.Weth9.Deposit
import Blanc.Lift.Weth9.Withdraw
import Blanc.Lift.Weth9.Approve
import Blanc.Lift.Weth9.TransferFrom

/-!
# WETH9 frame soundness

The whole WETH9 frame, assembled from the function specifications by the
dispatcher Hoare lemma (`SFunc.Run.hoare_single_call_with_gotos`) at
`Φ₀ := weth9Spec.Pre ca sevm` and `Φ₁ := weth9Spec.Post ca sevm`:

* entry `0` dispatches by goto into the selector wrappers `18–28` and calls
  entry `1` (deposit) on the fallback path;
* the view wrappers `18, 21, 22, 23, 26, 28` are state-silent;
* wrapper `19` calls deposit (`deposit_effect`, `deposit_solvent`);
* wrapper `24` calls withdraw (`withdraw_post`, with the deeper-frame
  hypothesis);
* wrappers `20, 25, 27` (transfer, transferFrom, approve) have solvency specs
  (`transfer_wrapper_solvent`, `transferFrom_wrapper_solvent`,
  `approve_wrapper_solvent`); the side condition `SumNof` of `Post` follows
  because their trees are balance-silent (`SFunc.Run.getBal_of_balSilent`).

The approve and transferFrom wrappers carry the local collision premise
`AllowAdmitted sevm` of this frame, and so does `frame_post`; it is the only
qualification, and no global keccak assumption appears.  Its necessity is the
O4 control `approve_collision_control` (`Approve.lean`): an admitted collision
lets an approve run end insolvent.

**Not reached here: the admitted ladder.**  `ContractSpecSem.SoundAdmitted`
hands the frame a deeper-frame hypothesis only for child derivations that are
themselves `Exec.FrameAdmitted`.  `frame_post` needs that hypothesis at the
`CALL` of `withdraw`, whose child derivation comes from the lifted run's
`Ninst.Run` witness; nothing links it to the concrete root derivation, whose
raw frame roots carry the admission (the lifted run forgets the derivation,
and even the pc of each step).  So `frame_post` takes the `Sound`-shaped
hypothesis, and `SoundAdmitted`/`PreservesAdmitted` for `weth9Spec` wait on a
derivation-carrying lift: `node_sound` extended so every `CALL` child of the
lifted run is a raw frame root of the concrete derivation.
-/

namespace Blanc.Lift.Weth9

open Jaune
open Blanc
open Blanc.Lift

private instance : Inhabited SFunc := ⟨.undefined⟩

/-- The view wrappers and their silent callees form a state-silent set. -/
theorem viewWrappers_silent :
    SilentSet prog (silentSet ++ [18, 21, 22, 23, 26, 28]) = true := by
  decide +kernel

/-- The transfer, transferFrom and approve wrappers, their bodies and their
gotos form a balance-silent set. -/
theorem tokenWrappers_balSilent :
    BalSilentSet prog (silentSet ++ [3, 9, 11, 20, 25, 27]) = true := by
  decide +kernel

theorem wrapper19_shape :
    (match prog[19]? with
      | some g => g.silentCalls silentSet 1 && g.callRefs.all (· ∈ [1])
      | none => false) = true := by
  decide +kernel

theorem wrapper24_shape :
    (match prog[24]? with
      | some g => g.silentCalls silentSet 1 && g.callRefs.all (· ∈ [8])
      | none => false) = true := by
  decide +kernel

theorem entry0_lookup : prog[0]? = some t_0000_c0 := by
  simp [prog, Cert.prog, cert]

private theorem hzero {j : Nat} {g : SFunc} (hj : j ∈ silentSet)
    (hjg : prog[j]? = some g) : g.silentCalls silentSet 0 = true := by
  have h := (List.all_eq_true.mp silentSet_no_calls) j hj
  rw [hjg] at h
  exact h

private theorem closed_of {P : SFunc → Bool} {S : List Nat}
    (hS : (S.all fun k => match prog[k]? with
      | some g => P g && g.refs.all (· ∈ S)
      | none => false) = true)
    {k : Nat} {g : SFunc} (hk : k ∈ S) (hg : prog[k]? = some g) :
    P g = true ∧ g.refs.all (· ∈ S) = true := by
  have h := (List.all_eq_true.mp hS) k hk
  rw [hg] at h
  simpa using h

section Frame

variable {sevm : Sevm}

private theorem stable0 {d d' : Devm} (hs : d.state = d'.state)
    (h : weth9Spec.Pre sevm.currentTarget sevm d) :
    weth9Spec.Pre sevm.currentTarget sevm d' :=
  h.state_eq hs.symm

private theorem stable1 {d d' : Devm} (hs : d.state = d'.state)
    (h : weth9Spec.Post sevm.currentTarget sevm d) :
    weth9Spec.Post sevm.currentTarget sevm d' :=
  ContractSpecSem.Post.of_state_eq h hs.symm

/-- A solvency conclusion over a balance-preserving run is the frame
postcondition. -/
private theorem post_of_solvent {d o : Devm}
    (hpre : weth9Spec.Pre sevm.currentTarget sevm d) (hbal : o.getBal = d.getBal)
    (h : Solvent (Devm.getStor o sevm.currentTarget) 0 (o.getBal sevm.currentTarget)) :
    weth9Spec.Post sevm.currentTarget sevm o :=
  ⟨hbal ▸ hpre.side, h⟩

/-- Deposit (entry 1) as a callee: `Pre` to `Post`. -/
theorem deposit_post {d : Devm} {o : Outcome} {g : SFunc}
    (hfork : CoveredFork sevm.benvStat.fork) (hg : prog[1]? = some g)
    (hpre : weth9Spec.Pre sevm.currentTarget sevm d)
    (run : SFunc.Run prog sevm d g o) :
    weth9Spec.Post sevm.currentTarget sevm (Outcome.devm o) :=
  post_of_solvent hpre (Weth9.deposit_effect hg hfork run).2
    (Weth9.deposit_solvent hg hfork run (hpre.inv.left rfl))

/-- **The WETH9 frame postcondition.**  Every run of the lifted program from a
frame precondition ends in the frame postcondition, given the frame's local
collision premise and the deeper-frame hypothesis in the form
`ContractSpecSem.Sound` supplies it (for the re-entrant `CALL` of
`withdraw`). -/
theorem frame_post {pre post : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hrun : SProg.Run prog sevm pre post)
    (hadm : AllowAdmitted sevm)
    (ih : ∀ pc' sevm' pre' post',
        Exec pc' sevm' pre' (.ok post') →
        sevm'.depth < sevm.depth →
        CodeSem.At weth9Spec.sem sevm.currentTarget pc' sevm' pre' →
        CoveredFork sevm'.benvStat.fork →
        weth9Spec.PreWf sevm.currentTarget sevm' pre' →
        weth9Spec.Post sevm.currentTarget sevm' post')
    (hpre : weth9Spec.Pre sevm.currentTarget sevm pre) :
    weth9Spec.Post sevm.currentTarget sevm post := by
  obtain ⟨f, hf, run⟩ := hrun
  rw [entry0_lookup] at hf
  cases hf
  have hsc : t_0000_c0.silentCallsWith silentSet wrapperSet 1 = true :=
    entry0_silentCalls
  refine SFunc.Run.hoare_single_call_with_gotos (K := [1])
    (Φ₀ := weth9Spec.Pre sevm.currentTarget sevm)
    (Φ₁ := weth9Spec.Post sevm.currentTarget sevm)
    silentSet_closed hzero (fun _ h => ContractSpecSem.post_of_pre h)
    stable0 stable1 ?_ ?_ hsc entry0_callRefs run hpre
  · intro k g hk hg d o hd r
    simp only [List.mem_singleton] at hk
    subst hk
    exact deposit_post hfork hg hd r
  · intro k g hk hg d o hd r
    simp only [wrapperSet, List.mem_cons, List.not_mem_nil, or_false] at hk
    -- the state-silent view wrappers
    have silentCase : k ∈ [18, 21, 22, 23, 26, 28] →
        weth9Spec.Post sevm.currentTarget sevm (Outcome.devm o) := by
      intro hk'
      obtain ⟨hs, hr⟩ := closed_of (P := SFunc.silent) viewWrappers_silent
        (List.mem_append_right _ hk') hg
      exact stable1 (SFunc.Run.state_of_silent viewWrappers_silent hs hr r).symm
        (ContractSpecSem.post_of_pre hd)
    -- the balance-silent token wrappers
    have balOf : k ∈ [20, 25, 27] → (Outcome.devm o).getBal = d.getBal := by
      intro hk'
      obtain ⟨hs, hr⟩ := closed_of (P := SFunc.balSilent) tokenWrappers_balSilent
        (List.mem_append_right _ (by simp at hk' ⊢; omega)) hg
      exact SFunc.Run.getBal_of_balSilent tokenWrappers_balSilent hs hr r
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact silentCase (by simp)
    · -- 19: deposit wrapper
      have hshape := wrapper19_shape
      rw [hg] at hshape
      simp only [Bool.and_eq_true] at hshape
      have h1 : prog[1]? = some t_0440_c1 := by simp [prog, Cert.prog, cert]
      exact SFunc.Run.hoare_wrapper silentSet_closed hzero
        (fun _ h => ContractSpecSem.post_of_pre h) stable0 stable1 h1
        (fun hd' r' => deposit_post hfork h1 hd' r') hshape.1 hshape.2 r hd
    · -- 20: transfer wrapper
      exact post_of_solvent hd (balOf (by simp))
        (Weth9.transfer_wrapper_solvent hg (hd.inv.left rfl) r)
    · exact silentCase (by simp)
    · exact silentCase (by simp)
    · exact silentCase (by simp)
    · -- 24: withdraw wrapper
      have hshape := wrapper24_shape
      rw [hg] at hshape
      simp only [Bool.and_eq_true] at hshape
      have h8 : prog[8]? = some t_09d9_c8 := by simp [prog, Cert.prog, cert]
      exact SFunc.Run.hoare_wrapper silentSet_closed hzero
        (fun _ h => ContractSpecSem.post_of_pre h) stable0 stable1 h8
        (fun hd' r' => Weth9.withdraw_post (c := weth9Spec)
          (fun h hle => Weth9.solvent_withdraw_step h hle) hfork rfl ih h8 r' hd')
        hshape.1 hshape.2 r hd
    · -- 25: transferFrom wrapper
      exact post_of_solvent hd (balOf (by simp))
        (Weth9.transferFrom_wrapper_solvent hg hadm (hd.inv.left rfl) r)
    · exact silentCase (by simp)
    · -- 27: approve wrapper
      exact post_of_solvent hd (balOf (by simp))
        (approve_wrapper_solvent hg hadm (hd.inv.left rfl) r)
    · exact silentCase (by simp)

end Frame

end Blanc.Lift.Weth9
