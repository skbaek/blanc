import Blanc.Composition.Weth9TokenOutputsWalk

/-!
# WETH9 output inversion: `transfer`

Every successful run of the deployed WETH9 selecting `transfer(address,uint256)` answers `true`.
The body is walked forgetting memory contents (only the free-memory pointer `0x60` is carried),
storage and hashed slots; the stack, and so the answer word, is tracked exactly.
-/

namespace Blanc.Composition.Weth9Token

open Jaune Blanc Blanc.Lift Blanc.Lift.Weth9

/-! ## Forgetful steps -/

section Forget

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G n : Nat} {f : SFunc} {r : Seg} {p : B256}

/-- `MSTORE` outside the pointer word, forgetting memory but the pointer. -/
theorem ric_mstoreF {i v : B256} (hM : PtrMem p n M) (miss : i.toNat + 32 ≤ 64 ∨ 96 ≤ i.toNat)
    (run : SFunc.RunCut fs sevm C (St b (i :: v :: S) M G) (.next (.reg .mstore) f) r) :
    ∃ M' n' G', PtrMem p n' M' ∧ SFunc.RunCut fs sevm C (St b S M' G') f r := by
  obtain ⟨d, hd, h⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_mstore hd
  exact ⟨_, _, _, hM.write _ v miss, h⟩

/-- `KECCAK256`, forgetting the digest and memory but the pointer. -/
theorem ric_keccakF {i sz : B256} (hM : PtrMem p n M)
    (run : SFunc.RunCut fs sevm C (St b (i :: sz :: S) M G) (.next (.reg .keccak256) f) r) :
    ∃ x M' n' G', PtrMem p n' M' ∧ SFunc.RunCut fs sevm C (St b (x :: S) M' G') f r := by
  obtain ⟨d, hd, h⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_keccak hd
  exact ⟨_, _, _, _, hM.extend _ _, h⟩

/-- `MLOAD` of the pointer word. -/
theorem ric_mloadF {i : B256} (hM : PtrMem p n M) (hi : i.toNat = 64)
    (run : SFunc.RunCut fs sevm C (St b (i :: S) M G) (.next (.reg .mload) f) r) :
    ∃ G', SFunc.RunCut fs sevm C (St b (p :: S) M G') f r := by
  obtain ⟨d, hd, h⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_mload hd
  rw [hi, hM.read_self (by have := hM.ge; omega)] at h
  have w : Bytes.toB256 (M.read 64 32).1 = p := hM.word
  rw [w] at h
  exact ⟨_, h⟩

/-- `LOG3`, forgetting the base and memory but the pointer. -/
theorem ric_log3F {i sz t1 t2 t3 : B256} (hM : PtrMem p n M)
    (run : SFunc.RunCut fs sevm C (St b (i :: sz :: t1 :: t2 :: t3 :: S) M G)
      (.next (.reg (.log 3)) f) r) :
    ∃ b' M' n' G', PtrMem p n' M' ∧ SFunc.RunCut fs sevm C (St b' S M' G') f r := by
  obtain ⟨d, hd, h⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_log3 hd
  exact ⟨_, _, _, _, hM.extend _ _, h⟩

/-- `SLOAD`, forgetting the base and the value. -/
theorem ric_sloadF {k : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCut fs sevm C (St b (k :: S) M G) (.next (.reg .sload) f) r) :
    ∃ b' x G', SFunc.RunCut fs sevm C (St b' (x :: S) M G') f r := by
  obtain ⟨d, hd, h⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sload hfork hd
  exact ⟨_, _, _, h⟩

/-- `SSTORE`, forgetting the base. -/
theorem ric_sstoreF {k v : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCut fs sevm C (St b (k :: v :: S) M G) (.next (.reg .sstore) f) r) :
    ∃ b' G', SFunc.RunCut fs sevm C (St b' S M G') f r := by
  obtain ⟨d, hd, h⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sstore hfork hd
  exact ⟨_, _, h⟩

end Forget

set_option hygiene false in
/-- One step of a forgetful walk over the run `h`, the pointer fact `hM` and the fork `hfork`
(hygiene off: these names are fixed). -/
macro "ivf" : tactic => `(tactic| first
  | (obtain ⟨_, _, _, hM', h'⟩ := ric_mstoreF hM (by decide) h; clear h hM; rename' h' => h, hM' => hM)
  | (obtain ⟨_, _, _, _, hM', h'⟩ := ric_keccakF hM h; clear h hM; rename' h' => h, hM' => hM)
  | (obtain ⟨_, h'⟩ := ric_mloadF hM (by decide) h; clear h; rename' h' => h)
  | (obtain ⟨_, _, _, _, hM', h'⟩ := ric_log3F hM h; clear h hM; rename' h' => h, hM' => hM)
  | (obtain ⟨_, _, _, h'⟩ := ric_sloadF hfork h; clear h; rename' h' => h)
  | (obtain ⟨_, _, h'⟩ := ric_sstoreF hfork h; clear h; rename' h' => h)
  | iv)

section Transfer

variable {fs : List SFunc} {sevm : Sevm}

/-- The `transferFrom` body's tail (entry `0x08cf`), inverted: the two balance updates and the
`Transfer` event leave `true` above the caller's stack and keep the pointer. -/
theorem xfer_tail_inv {b : Devm} {x wad dst src ret : B256} {S : List B256} {M : Mem} {n G : Nat}
    {r : Seg} (hfork : CoveredFork sevm.benvStat.fork) (hM : PtrMem 0x60 n M)
    (run : SFunc.RunCut fs sevm [] (St b (x :: wad :: dst :: src :: ret :: S) M G) t_08cf_c9 r) :
    ∃ b' M' n' G', PtrMem 0x60 n' M' ∧ r = .done (.returned (St b' (1 :: S) M' G')) := by
  have h := run
  clear run
  unfold t_08cf_c9 at h
  repeat ivf
  obtain ⟨G', hG⟩ := ric_ret (S := Bytes.toB256 [0x01] :: S) h
  exact ⟨_, _, _, G', hM, hG⟩

/-- A self-comparison's double negation is nonzero, and so is its triple negation's zero test. -/
theorem eqc_self_not_not (z : B256) : B256.eqCheck (B256.eqCheck (B256.eqCheck z z) 0) 0 ≠ 0 := by
  simp only [B256.eqCheck, ↓reduceIte]
  decide

/-- The `transferFrom` body (entry `0x068c`) entered with `src` the caller, inverted: the balance
check and the skipped allowance test lead to the tail, which answers `true`. -/
theorem xfer_body_self_inv {b : Devm} {wad dst ret : B256} {S : List B256} {M : Mem} {n G : Nat}
    {o : Outcome} (hfork : CoveredFork sevm.benvStat.fork) (hM : PtrMem 0x60 n M)
    (run : SFunc.Run fs sevm (St b (wad :: dst :: sevm.caller.toB256 :: ret :: S) M G) t_068c_c9 o) :
    ∃ b' M' n' G', PtrMem 0x60 n' M' ∧ o = .returned (St b' (1 :: S) M' G') := by
  have h := SFunc.Run.cut run
  clear run
  unfold t_068c_c9 at h
  repeat ivf
  rcases ric_branch h with ⟨-, _, h⟩ | ⟨-, _, h⟩
  · unfold t_06d8_c9 at h
    iv; iv
    exact (ric_revert h).elim
  · unfold t_06dc_c9 at h
    repeat ivf
    rcases ric_branch h with ⟨hz, _, h⟩ | ⟨-, _, h⟩
    · exact absurd hz (eqc_self_not_not _)
    · unfold t_07b4_c9 at h
      repeat ivf
      rcases ric_branch h with ⟨hz, _, h⟩ | ⟨-, _, h⟩
      · exact absurd hz (eqc_self_not_not _)
      · obtain ⟨b', M', n', G', hM', hG⟩ := xfer_tail_inv hfork hM h
        exact ⟨b', M', n', G', hM', Seg.done.inj hG⟩

theorem prog_get_3 : prog[3]? = some t_0bce_c3 := by
  simp only [prog, Cert.prog, cert, List.map_cons, List.map_nil, List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, Nat.reduceLT, getElem?_pos, List.getElem_cons_succ,
    List.getElem_cons_zero]

theorem prog_get_9 : prog[9]? = some t_068c_c9 := by
  simp only [prog, Cert.prog, cert, List.map_cons, List.map_nil, List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, Nat.reduceLT, getElem?_pos, List.getElem_cons_succ,
    List.getElem_cons_zero]

theorem prog_get_20 : prog[20]? = some t_0370_c20 := by
  simp only [prog, Cert.prog, cert, List.map_cons, List.map_nil, List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, Nat.reduceLT, getElem?_pos, List.getElem_cons_succ,
    List.getElem_cons_zero]

/-- The `transfer` inner entry (entry 3, `0x0bce`), inverted: `transferFrom(msg.sender, dst, wad)`
returns `true` above the stack below its return tag. -/
theorem transfer_inner_inv {b : Devm} {w1 w2 r0 : B256} {R : List B256} {M : Mem} {n G : Nat}
    {o : Outcome} (hfork : CoveredFork sevm.benvStat.fork) (hM : PtrMem 0x60 n M)
    (run : SFunc.Run prog sevm (St b (w1 :: w2 :: r0 :: R) M G) t_0bce_c3 o) :
    ∃ b' M' n' G', PtrMem 0x60 n' M' ∧ o = .returned (St b' (1 :: R) M' G') := by
  have h := SFunc.Run.cut run
  clear run
  unfold t_0bce_c3 at h
  repeat iv
  obtain ⟨_, hc⟩ := ric_call prog_get_9 h
  rcases hc with ⟨D, hcal, h⟩ | ⟨D, hcal, -⟩
  · obtain ⟨b', M', n', G', hM', hD⟩ := xfer_body_self_inv hfork hM hcal
    cases hD
    unfold t_0bdb_c3 at h
    repeat iv
    obtain ⟨G'', hG⟩ := ric_ret (S := Bytes.toB256 [0x01] :: R) h
    exact ⟨_, _, _, G'', hM', Seg.done.inj hG⟩
  · obtain ⟨_, _, _, _, -, hD⟩ := xfer_body_self_inv hfork hM hcal
    cases hD

/-- The boolean ABI tail at `0x3b0`, inverted: it returns the word's normalized truth value. -/
theorem bool_tail_inv {b : Devm} {v : B256} {R : List B256} {M : Mem} {n G : Nat} {o : Outcome}
    (hM : PtrMem 0x60 n M) (run : SFunc.Run fs sevm (St b (v :: R) M G) t_03b0_c20 o) :
    ∃ D, o = .halted D ∧
      D.output = (B256.eqCheck (B256.eqCheck (B256.eqCheck (B256.eqCheck v 0) 0) 0) 0).toBytes := by
  have h := SFunc.Run.cut run
  clear run
  unfold t_03b0_c20 at h
  iv; iv; iv
  have e64 : (Bytes.toB256 [0x40]).toNat = 64 := rfl
  have r1 : (M.read 64 32).2 = M := hM.read_self (by have := hM.ge; omega)
  have w1 : Bytes.toB256 (M.read 64 32).1 = 0x60 := hM.word
  rw [e64, r1, w1] at h
  iv; iv; iv; iv; iv; iv; iv; iv; iv; iv; iv; iv; iv; iv; iv
  have hM2 := hM.write 96 (B256.eqCheck (B256.eqCheck (B256.eqCheck (B256.eqCheck v 0) 0) 0) 0)
    (.inr (le_refl _))
  have r2 := hM2.read_self (i := 64) (sz := 32) (by have := hM2.ge; omega)
  have w2 := hM2.word
  unfold memWord at w2
  rw [e64, show (0x60 : B256).toNat = 96 from rfl, r2, w2] at h
  iv; iv; iv; iv
  cases h with
  | last hr =>
    obtain ⟨hout, -, -⟩ := ri_return (S := R) hr
    refine ⟨_, rfl, ?_⟩
    rw [hout, show (Bytes.toB256 [0x20] + 96 - 96 : B256).toNat = 32 from by decide]
    exact Mem.read_write_word_of_wf hM.wf _ _

/-- The `transfer` wrapper at `0x370`, entered from the dispatcher, inverted: the frame halts
answering `true`. -/
theorem transfer_wrapper_inv {pre post : Devm} {G : Nat} (hfork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run prog sevm (St pre [Sevm.selector sevm] memFp G) t_0370_c20 (.halted post)) :
    post.output = (Nat.toB256 1).toBytes := by
  have h := SFunc.Run.cut run
  clear run
  unfold t_0370_c20 at h
  iv; iv; iv; iv
  rcases ric_branch h with ⟨-, _, h⟩ | ⟨-, _, h⟩
  · unfold t_0377_c20 at h
    iv; iv
    exact (ric_revert h).elim
  · unfold t_037b_c20 at h
    repeat iv
    obtain ⟨_, hc⟩ := ric_call prog_get_3 h
    rcases hc with ⟨D, hcal, h⟩ | ⟨D, hcal, -⟩
    · obtain ⟨b', M', n', G', hM', hD⟩ := transfer_inner_inv hfork memFp_ptr hcal
      cases hD
      obtain ⟨D, hD, hout⟩ := bool_tail_inv hM' h.uncut
      cases hD
      rw [hout]
      rfl
    · obtain ⟨_, _, _, _, -, hD⟩ := transfer_inner_inv hfork memFp_ptr hcal
      cases hD

/-- **Universal `transfer` output.**  Every successful run of the deployed WETH9 — at any gas, static
or not — whose calldata selects `transfer(address,uint256)` answers `true`. -/
theorem weth9_transfer_output {pre post : Devm} {G : Nat} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork) (hshort : ¬ shortCall sevm)
    (hsel : Sevm.selector sevm = 0xa9059cbb)
    (run : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)) :
    post.output = (Nat.toB256 1).toBytes := by
  rcases weth9_entry_cut hshort (exec_lift hcode hfork run) with ⟨l, hl, hs, g, G', hg, k⟩ | hne
  · rw [hsel] at hs
    simp only [links, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd hs (by decide)
      | (rw [prog_get_20] at hg
         cases hg
         exact transfer_wrapper_inv hfork k)
  · have hm : links[8] ∈ links := List.getElem_mem (by decide)
    exact (hne _ hm (hsel.trans (by decide))).elim

end Transfer

/-! ## Through the book's decoder -/

section Op

variable {sevm : Sevm}

theorem decodeCall_transfer {w d : Adr} {x : B256} (h : decodeCall sevm = some (.transfer w d x)) :
    ¬ shortCall sevm ∧ Sevm.selector sevm = 0xa9059cbb := by
  unfold decodeCall at h
  split_ifs at h with h1 h2 h3 <;> first | exact ⟨h1, h3⟩ | cases h

/-- **`balanceOf` answer** (input to `Core.balanceAnswer`): a successful WETH9 frame whose decoded
message is `balanceOf h` answers `h`'s balance slot in its pre-state, whatever its gas and
staticness. -/
theorem weth9Op_balanceOf_output {pre post : Devm} {G : Nat} {h : Adr} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork) (hop : weth9Op sevm = .balanceOf h)
    (run : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)) :
    post.output = (pre.getStorVal sevm.currentTarget (balSlot h)).toBytes := by
  unfold weth9Op at hop
  split_ifs at hop with hc
  · cases hop
    exact weth9_balanceOf_output hcode hfork hc.1 hc.2 run
  · revert hop
    split <;> (try split) <;> intro hop <;> cases hop

/-- **`transfer` answer** (input to `Core.transferAnswer`): a successful WETH9 frame whose decoded
message is `transfer dst v` answers `true`, whatever its gas and staticness. -/
theorem weth9Op_transfer_output {pre post : Devm} {G : Nat} {dst : Adr} {v : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hop : weth9Op sevm = .transfer dst v)
    (run : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)) :
    post.output = (Nat.toB256 1).toBytes := by
  unfold weth9Op at hop
  by_cases hc : ¬ shortCall sevm ∧ Sevm.selector sevm = 0x70a08231
  · rw [ite_eq_left hc] at hop
    cases hop
  · rw [ite_eq_right hc] at hop
    revert hop
    split
    · split <;> intro hop <;> cases hop
    · rename_i hd
      intro _
      obtain ⟨hshort, hsel⟩ := decodeCall_transfer hd
      exact weth9_transfer_output hcode hfork hshort hsel run
    all_goals intro hop; cases hop

end Op

end Blanc.Composition.Weth9Token
