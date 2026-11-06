import Blanc.Lift.DaiFrames
import Blanc.Lift.HistStaticCall

/-!
# DAI: a committed `permit` logs `Approval` with its holder

`frame_permit_logs`: a successful `permit(holder, spender, …)` frame logs `Approval(holder, spender, _)`.
So a reader who finds no `Approval` log with the holder as owner may conclude no `permit` naming it committed.
-/

namespace Blanc.Lift.Dai

open Jaune Blanc Blanc.Lift

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- The `Approval(address,address,uint256)` topic. -/
def approvalTopic : B256 := 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925

/-- `permit`'s internal entries: none halts the frame. -/
def permitCallees : List Nat := [6, 7, 18]

theorem permitCallees_noHalt : NoHaltSet cert.prog permitCallees = true := by decide +kernel

/-- **Tree `0x1706` of entry 7**: the allowance write and the `Approval` log. -/
theorem e7_log {w z dg s r v al ex no sp ho ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (h : SFunc.RunCut cert.prog sevm []
      (St b (w :: z :: dg :: s :: r :: v :: al :: ex :: no :: sp :: ho :: ret :: S) M G) t_1706_c7 (Seg.done o)) :
    ∃ (b₀ : Devm) (data : Bytes) (M' : Mem) (G' : Nat), o = .returned (St
      (Devm.addLog b₀ ⟨sevm.currentTarget, [approvalTopic, ho.toAdr.toB256, sp.toAdr.toB256], data⟩) S M' G') := by
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  simp only [ff20_and_word] at e
  have topic : Bytes.toB256 [0x8c, 0x5b, 0xe1, 0xe5, 0xeb, 0xec, 0x7d, 0x5b, 0xd1, 0x4f, 0x71, 0x42, 0x7d, 0x1e,
      0x84, 0xf3, 0xdd, 0x03, 0x14, 0xc0, 0xf7, 0xb2, 0x29, 0x1e, 0x5b, 0x20, 0x0a, 0xc8, 0xc7, 0xc3, 0xb9, 0x25] =
      approvalTopic := by decide
  rw [topic] at e
  exact ⟨_, _, _, _, Seg.done.inj e⟩

/-- **Tree `0x15a2` of entry 6**: the expiry and nonce checks, then the log tail. -/
theorem e6_log {c dg s r v al ex no sp ho ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (h : SFunc.RunCut cert.prog sevm []
      (St b (c :: dg :: s :: r :: v :: al :: ex :: no :: sp :: ho :: ret :: S) M G) t_15a2_c6 (Seg.done o)) :
    ∃ (b₀ : Devm) (data : Bytes) (M' : Mem) (G' : Nat), o = .returned (St
      (Devm.addLog b₀ ⟨sevm.currentTarget, [approvalTopic, ho.toAdr.toB256, sp.toAdr.toB256], data⟩) S M' G') := by
  iterate 2 ustep h
  ibranch h c1
  iterate 35 ustep h
  ibranch h c2
  iterate 4 ustep h
  have h' := ric_branch h
  clear h
  rcases h' with ⟨-, _, h⟩ | ⟨-, _, h⟩
  · iterate 3 ustep h
    exact e7_log fork h
  · iterate 2 ustep h
    exact e7_log fork h

/-- **Entry 18, `permit`'s body.** -/
theorem e18_log {s r v al ex no sp ho ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (s :: r :: v :: al :: ex :: no :: sp :: ho :: ret :: S) M G)
      t_12bf_c18 o) :
    ∃ (b₀ : Devm) (data : Bytes) (M' : Mem) (G' : Nat), o = .returned (St
      (Devm.addLog b₀ ⟨sevm.currentTarget, [approvalTopic, ho.toAdr.toB256, sp.toAdr.toB256], data⟩) S M' G') := by
  have h := run.cut
  clear run
  iterate 6 ustep h
  have h' := ric_next h
  clear h
  obtain ⟨_, hd, h⟩ := h'
  obtain ⟨_, e⟩ := ri_shl hd
  subst e
  clear hd
  iterate 133 ustep h
  ibranch h c1
  iterate 60 ustep h
  ugas h
  have h' := ric_next h
  clear h
  obtain ⟨_, hd, h⟩ := h'
  obtain ⟨flag, out, hpost, -⟩ := ri_staticcallH fork.stateGas_none hd
  rw [hpost.eq_St] at h
  clear hd hpost
  iterate 4 ustep h
  ibranch h c2
  iterate 16 ustep h
  ibranch h c3
  iterate 6 ustep h
  ubranchTo h c4
  · iterate 2 ustep h
    have h' := ric_next h
    clear h
    obtain ⟨_, hd, h⟩ := h'
    obtain ⟨_, e⟩ := ri_timestamp hd
    subst e
    clear hd
    iterate 2 ustep h
    exact e6_log fork h
  · exact e6_log fork h

/-- **A committed `permit` logs `Approval` with its holder.** -/
theorem frame_permit_logs {post : Devm} (fork : HistFork sevm.benvStat.fork)
    (sel : Blanc.Sevm.selector sevm = 0x8fcbaf0c)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    ∃ l ∈ post.logs, l.address = sevm.currentTarget ∧
      l.topics.take 2 = [approvalTopic, (Sevm.dataWord sevm 4).toAdr.toB256] := by
  have h := run.cut
  clear run
  uhead h sel
  repeat ustep h
  ibranch h c1
  repeat ustep h
  have h' := ric_callR (k := 18) (g := t_12bf_c18) rfl
    (fun hh => SFunc.RunP.not_halted_entry permitCallees_noHalt
      (by decide : 18 ∈ permitCallees) rfl hh rfl) h
  clear h
  obtain ⟨_, _, hc, h⟩ := h'
  obtain ⟨b₀, data, M', G', e⟩ := e18_log fork hc
  cases e
  clear hc
  repeat ustep h
  cases ric_stop h
  refine ⟨_, List.mem_append_right _ List.mem_cons_self, rfl, ?_⟩
  simp only [ff20_and_word, toAdr_toB256, lit4, List.take_succ_cons, List.take_zero]

end Blanc.Lift.Dai
