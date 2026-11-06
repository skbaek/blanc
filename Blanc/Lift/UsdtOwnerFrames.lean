import Blanc.Lift.UsdtFrames
import Blanc.Lift.WriteSiteStep

/-!
# USDT: the owner's entry at the `top` write sites, and what the frame laws leave of a slot

The certificate cannot name the slot of USDT's four `top` balance writes, since its terms have no `SLOAD`.
The walks of `UsdtFrames` do: `transfer`'s and `transferFrom`'s fee credit (`moveStor`), `issue` (`issueStor`)
and `redeem` (`redeemStor`) write `balances[ownerOf …]`, with the owner word read at the write. This
module says that word is the owner's at the frame's entry:

* `moveStor_top`, `issueStor_top`, `redeemStor_top`: each `top` slot is `balSlot (ownerOf σ)`, for `σ` the
  storage at entry, given that the balance writes before it miss slot `0`;
* `moveStor_get_ne`, `issueStor_get_ne`, `redeemStor_get_ne`, `spendStor_get_ne`: any other slot keeps its word;
* `moveStor_source`: a move lowers its source's entry by at most `v`, whoever else it pays;
* `frame_balanceOf_output`: `balanceOf`'s answer is the entry it names.
-/

namespace Blanc.Lift.Usdt

open Jaune Blanc Blanc.Lift

variable {σ : Stor} {src dst : Adr} {v f k : B256}

theorem ownerOf_set {j x : B256} (hj : j ≠ 0) : ownerOf (σ.set j x) = ownerOf σ := by
  unfold ownerOf
  rw [Stor.get_set_ne _ hj]

/-- The owner word the fee credit reads is the entry's, when the two entries written first miss slot `0`. -/
theorem moveStor_owner (hs : balSlot src ≠ 0) (hd : balSlot dst ≠ 0) :
    ownerOf (credit (debit σ src v) dst (v - f)) = ownerOf σ := by
  unfold credit debit
  rw [ownerOf_set hd, ownerOf_set hs]

/-- **The `top` site of `transfer` and `transferFrom` is the owner's entry.** -/
theorem moveStor_top (hs : balSlot src ≠ 0) (hd : balSlot dst ≠ 0) (hf : f ≠ 0) :
    moveStor σ src dst v f =
      credit (credit (debit σ src v) dst (v - f)) (ownerOf σ) f := by
  unfold moveStor
  rw [ite_eq_right hf, moveStor_owner hs hd]

/-- **The `top` site of `issue` is the owner's entry**, read at entry. -/
theorem issueStor_top (a : B256) :
    issueStor σ a = (σ.set (balSlot (ownerOf σ)) (σ.get (balSlot (ownerOf σ)) + a)).set 1
      ((σ.set (balSlot (ownerOf σ)) (σ.get (balSlot (ownerOf σ)) + a)).get 1 + a) := rfl

/-- **The `top` site of `redeem` is the owner's entry**: the supply write before it misses slot `0`. -/
theorem redeemStor_top (a : B256) :
    redeemStor σ a = (σ.set 1 (σ.get 1 - a)).set (balSlot (ownerOf σ))
      ((σ.set 1 (σ.get 1 - a)).get (balSlot (ownerOf σ)) - a) := by
  unfold redeemStor
  rw [ownerOf_set (by decide)]

/-- Every slot but the three a move writes keeps its word. -/
theorem moveStor_get_ne (hs : balSlot src ≠ 0) (hd : balSlot dst ≠ 0) (k1 : balSlot src ≠ k)
    (k2 : balSlot dst ≠ k) (k3 : balSlot (ownerOf σ) ≠ k) :
    (moveStor σ src dst v f).get k = σ.get k := by
  have base : (credit (debit σ src v) dst (v - f)).get k = σ.get k := by
    unfold credit debit
    rw [Stor.get_set_ne _ k2, Stor.get_set_ne _ k1]
  unfold moveStor
  split
  · exact base
  · rw [moveStor_owner hs hd]
    unfold credit
    rw [Stor.get_set_ne _ k3]
    exact base

theorem issueStor_get_ne {a : B256} (k1 : (1 : B256) ≠ k) (k2 : balSlot (ownerOf σ) ≠ k) :
    (issueStor σ a).get k = σ.get k := by
  unfold issueStor
  rw [Stor.get_set_ne _ k1, Stor.get_set_ne _ k2]

theorem redeemStor_get_ne {a : B256} (k1 : (1 : B256) ≠ k) (k2 : balSlot (ownerOf σ) ≠ k) :
    (redeemStor σ a).get k = σ.get k := by
  rw [redeemStor_top, Stor.get_set_ne _ k2, Stor.get_set_ne _ k1]

theorem spendStor_get_ne {o s : Adr} (hk : allowSlot o s ≠ k) : (spendStor σ o s v).get k = σ.get k := by
  unfold spendStor
  split
  · rfl
  · exact Stor.get_set_ne _ hk _

/-- **A move lowers its source's entry by at most `v`**, whatever the fee and whoever it pays. -/
theorem moveStor_source (ok : MoveOk σ src dst v f) :
    (σ.get (balSlot src)).toNat ≤ ((moveStor σ src dst v f).get (balSlot src)).toNat + v.toNat := by
  have h0 : ((debit σ src v).get (balSlot src)).toNat = (σ.get (balSlot src)).toNat - v.toNat := by
    unfold debit
    rw [Stor.get_set_self, WriteSite.B256.toNat_sub_of_le ok.debit_le]
  have h2 : ((debit σ src v).get (balSlot src)).toNat ≤
      ((credit (debit σ src v) dst (v - f)).get (balSlot src)).toNat :=
    set_get_ge (by exact ok.credit_lt) rfl
  have h3 : ((debit σ src v).get (balSlot src)).toNat ≤
      ((moveStor σ src dst v f).get (balSlot src)).toNat := by
    unfold moveStor
    split
    · exact h2
    · rename_i hf
      exact h2.trans (set_get_ge (σ := credit (debit σ src v) dst (v - f)) (ok.owner_lt hf) rfl)
  have := ok.debit_le
  omega

/-! ## `balanceOf`'s answer -/

section Output

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- **Entry 57, `BasicToken.balanceOf(a)`**, with the memory it leaves: only the scratch words move. -/
theorem e57_out {a ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (run : SFunc.Run cert.prog sevm (St b (a :: ret :: S) M G) t_2652_c57 o) :
    ∃ b' M' G', o = .returned (St b' ((Devm.getStor b sevm.currentTarget).get (balSlot a.toAdr) :: S) M' G') ∧
      Devm.getStor b' = Devm.getStor b ∧ Mem.Wf M' ∧ (M'.read 64 32).1 = (M.read 64 32).1 := by
  have h := run.cut
  clear run
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  cases e
  simp only [keccak_u, ff20_and_word, toAdr_toB256, lit2, gsv, balSlot]
  refine ⟨_, _, _, rfl, funext fun x => afterSloadH_getStor _ _ _ x, by uwf, ?_⟩
  rw [memRead_snd_fst, Mem.read_write_word_disjoint (wf.write _ _) _ _ (.inl (by decide +kernel)),
    Mem.read_write_word_disjoint wf _ _ (.inl (by decide +kernel))]

/-- **Entry 33, `TetherToken.balanceOf(a)`, not deprecated**, with the memory it leaves. -/
theorem e33_out {a ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (hdep : flag20 ((Devm.getStor b sevm.currentTarget).get 10) = 0)
    (run : SFunc.Run cert.prog sevm (St b (a :: ret :: S) M G) t_1239_c33 o) :
    ∃ b' M' G', o = .returned (St b' ((Devm.getStor b sevm.currentTarget).get (balSlot a.toAdr) :: S) M' G') ∧
      Devm.getStor b' = Devm.getStor b ∧ Mem.Wf M' ∧ (M'.read 64 32).1 = (M.read 64 32).1 := by
  have h := run.cut
  clear run
  repeat ustep h
  unorm h
  rw [lit10] at h
  have h' := ric_branch h
  clear h
  rcases h' with ⟨c3, _, h⟩ | ⟨c3, _, h⟩
  · exfalso
    rw [show (Bytes.toB256 [255] &&& (Devm.getStor b sevm.currentTarget).get 10 /
      B256.bexp (Bytes.toB256 [1, 0]) (Bytes.toB256 [20])) = 0 from hdep] at c3
    exact absurd c3 (by decide)
  repeat ustep h
  ucall h hc 57 t_2652_c57
  obtain ⟨B, MB, GB, e, sB, wB, rB⟩ := e57_out fork wf hc
  cases e
  clear hc
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  cases e
  simp only [afterSloadH_getStor] at sB ⊢
  have sB' := funext fun x => (congrFun sB x).trans (afterSloadH_getStor _ _ _ x)
  exact ⟨_, _, _, rfl, sB', wB, rB⟩

/-- **The `balanceOf(a)` frame of TetherToken, not deprecated, answers `a`'s entry.** -/
theorem frame_balanceOf_output {post : Devm} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (sel : Blanc.Sevm.selector sevm = 0x70a08231)
    (hdep : flag20 ((Devm.getStor b sevm.currentTarget).get 10) = 0)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    post.output = ((Devm.getStor b sevm.currentTarget).get (balSlot (Sevm.dataWord sevm 4).toAdr)).toBytes := by
  have h := run.cut
  clear run
  iterate 7 ustep h
  ibranch h c0
  iterate 7 ustep h
  rw [legacy_selector_word, sel] at h
  repeat udisp h
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ucall h hc 33 t_1239_c33
  obtain ⟨B, MB, GB, e, sB, wB, rB⟩ := e33_out fork (by uwf) hdep hc
  cases e
  clear hc
  repeat ustep h
  have fp : (MB.read (Bytes.toB256 [64]).toNat 32).1 = (Bytes.toB256 [96]).toBytes := by
    rw [show (Bytes.toB256 [64]).toNat = 64 by decide +kernel, rB,
      show (Bytes.toB256 [64]).toNat = 64 by decide +kernel]
    exact Mem.read_write_word_of_wf wf 64 _
  rw [fp] at h
  simp only [ff20_and_word, toAdr_toB256, lit4] at h
  generalize (Devm.getStor b sevm.currentTarget).get (balSlot (Sevm.dataWord sevm 4).toAdr) = v at h ⊢
  have w96 : (Bytes.toB256 [96]).toBytes.toB256 = Bytes.toB256 [96] := by decide +kernel
  have l96 : (Bytes.toB256 [96]).toNat = 96 := by decide +kernel
  rw [w96, l96] at h
  have wN : Mem.Wf (MB.read (Bytes.toB256 [64]).toNat 32).2 := by uwf
  have r2 : (((MB.read (Bytes.toB256 [64]).toNat 32).2.write 96 v.toBytes).read
      (Bytes.toB256 [64]).toNat 32).1 = (Bytes.toB256 [96]).toBytes := by
    rw [Mem.read_write_word_disjoint wN 96 v (.inr (by decide +kernel)), memRead_snd_fst, fp]
  rw [r2, w96] at h
  cases h with
  | last hl =>
    rw [(ri_return hl).1, memRead_snd_fst, l96,
      show (Bytes.toB256 [32] + Bytes.toB256 [96] - Bytes.toB256 [96]).toNat = 32 by decide +kernel]
    exact Mem.read_write_word_of_wf wN 96 v

end Output

end Blanc.Lift.Usdt
