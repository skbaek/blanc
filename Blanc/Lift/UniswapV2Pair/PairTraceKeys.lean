import Blanc.Lift.UniswapV2Pair.FeeMintSource
import Blanc.Lift.UniswapV2Pair.StaticViewSource
import Blanc.Lift.PrecompileAnswer
import Blanc.Lift.InvWalkProvenance

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def mintReplyRow (out : Bytes) : WriterKey := .balance (Bytes.toB256 (out.take 32)).toAdr

noncomputable def mintFeeReplyKeys (root : Exec.Deriv) : List WriterKey :=
  (Exec.rawFrameRoots root.exc).filterMap (fun F =>
    match F.exn with
    | .ok d => some (mintReplyRow d.output)
    | .error _ => none) ++
  precompileRunAddresses.filterMap (fun adr =>
    (precompileAnswer (ExternalOperation.encode .feeTo) root.sevm.benvStat.rules.modexp
      adr).map mintReplyRow)

noncomputable def mintTraceKeys (root : Exec.Deriv) : List WriterKey :=
  ((Exec.rawFrameRoots root.exc).flatMap fun F =>
    if F.sevm.currentTarget = root.sevm.currentTarget then staticViewDecodedKeys F.sevm else []) ++
  (lpMintTouched (0 : B256).toAdr ++ lpMintTouched (Sevm.dataWord root.sevm 4).toAdr) ++
  mintFeeReplyKeys root

theorem mintTraceKeys_frame {root : Exec.Deriv} {F : Exec.Deriv}
    (member : F ∈ Exec.rawFrameRoots root.exc)
    (target : F.sevm.currentTarget = root.sevm.currentTarget) :
    ∀ k ∈ staticViewDecodedKeys F.sevm, k ∈ mintTraceKeys root := by
  intro k touched
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨F, member, ?_⟩))
  rw [ite_eq_left target]
  exact touched

theorem mintTraceKeys_rows (root : Exec.Deriv) :
    .balance (0 : B256).toAdr ∈ mintTraceKeys root ∧
    .balance (Sevm.dataWord root.sevm 4).toAdr ∈ mintTraceKeys root := by
  refine ⟨?_, ?_⟩ <;>
    simp only [mintTraceKeys, lpMintTouched, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, true_or, or_true]

theorem mint_feeReply_mem {root : Exec.Deriv} {w d : Devm} {g t oi os : B256} {S : List B256}
    {M : Mem} {c : Nat} (fork : CoveredFork root.sevm.benvStat.fork) (wf : Mem.Wf M)
    (call : Blanc.Lift.StepIn root root.sevm
      (St w (g :: t :: 128 :: 4 :: oi :: os :: S) (feeRequestMemory M) c) (.exec .staticcall) d)
    (flag : ∃ f rest, d.stack = f :: rest ∧ f ≠ 0) :
    mintReplyRow d.returnData ∈ mintTraceKeys root := by
  refine List.mem_append_right _ ?_
  obtain ⟨xl, inRoots, pc, stepRun⟩ := call
  have filled : Xlot.Filled xl := by
    cases xl with
    | none => trivial
    | some p =>
      obtain ⟨evm, exn⟩ := p
      obtain ⟨e, _⟩ := inRoots
      exact ⟨e⟩
  rcases of_step_staticcall_val_with_depth_frame_cause (g := g) (t := t) (ii := 128) (is := 4)
      (oi := oi) (os := os) (xs := S) (by simpa only [St.stack, List.append_nil] using
        (pref_append (g :: t :: 128 :: 4 :: oi :: os :: S) [])) filled stepRun fork with
      ⟨failed, _⟩ | ⟨parent, child, dp, na, code, avail, _, _, _, _, _, _, _, _,
        process, clean, _, _, returned, _, _, _⟩
  · obtain ⟨f, rest, flagStack, nonzero⟩ := flag
    rw [flagStack] at failed
    exact (nonzero (pref_head_unique failed (pref_append [f] rest)).symm).elim
  · rw [returned]
    rcases Blanc.Lift.ProcessMessage.ok_output process clean with
      ⟨_, adr, listed, answer⟩ | ⟨evm, raw, slot, rawEq⟩
    · refine List.mem_append_right _ (List.mem_filterMap.mpr ⟨adr, listed, ?_⟩)
      have request :
          ((St w (g :: t :: 128 :: 4 :: oi :: os :: S) (feeRequestMemory M) c).memory.read
          (128 : B256).toNat (4 : B256).toNat).1 = ExternalOperation.encode .feeTo :=
        feeRequestMemory_read wf
      change precompileAnswer ((St w (g :: t :: 128 :: 4 :: oi :: os :: S) (feeRequestMemory M)
        c).memory.read (128 : B256).toNat (4 : B256).toNat).1 root.sevm.benvStat.rules.modexp adr =
        some child.output at answer
      rw [request] at answer
      rw [answer]
      rfl
    · subst slot
      subst rawEq
      obtain ⟨childRun, roots⟩ := inRoots
      refine List.mem_append_left _ (List.mem_filterMap.mpr
        ⟨⟨evm.pc, evm.sta, evm.dyna, .ok child, childRun⟩, roots _ List.mem_cons_self, rfl⟩)

end Blanc.Lift.UniswapV2Pair
