import Blanc.Lift.Curve3Pool.Walk.DispatchQuiet
import Blanc.Lift.Quiet
import Blanc.StaticStorage

/-!
# The dispatcher's fall-through, and static frames

`pool_other_fails`: a successful frame of the pool's runtime never decodes to `.other`. Short
calldata (`< 4` bytes) jumps from the prologue's length test to the shared `REVERT` at `0x52c9`;
a selector that misses every test runs the 38 skips (`DispatchQuiet`'s `dq_*` chain and
`dq_skip_1ec0cdc1` below for the last, `future_owner`, test) into the same `REVERT`.

`pool_static_noEffect`: a successful, committing static frame whose target carries code keeps every
account's storage and the log list (generic: `Exec.getStor_committedPost_eq_of_static`,
`Exec.logs_eq_of_static_ok`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **The shared fall-through `REVERT`** at `0x52c9` (`JUMPDEST; PUSH1 0; PUSH1 0; REVERT`)
never succeeds. -/
theorem fb_revert {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {S : List B256} {M : Mem}
    {G : Nat} (hcode : sevm.code = code) (h : XAt sevm post 0x52c9 (St b S M G) L) : False := by
  xjd 0x52ca
  xs 0x52cc (.push [0x00] (by decide)) ri_push
  xs 0x52ce (.push [0x00] (by decide)) ri_push
  xrevert

/-- **Short calldata reverts**: the prologue's length test jumps to the fall-through. -/
theorem fb_short {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code) (hlen : sevm.data.length < 4) (hcd : sevm.data.length < 2 ^ 256)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) : False := by
  xs 0x2 (.push [0x04] (by decide)) ri_push
  xs 0x3 (.reg .calldatasize) ri_calldatasize
  xs 0x4 (.reg .lt) ri_lt
  xs 0x5 (.reg .iszero) ri_iszero
  xs 0x8 (.push [0x00, 0x0d] (by decide)) ri_push
  xji 0x9 0xd hw
  · xs 0xc (.push [0x52, 0xc9] (by decide)) ri_push
    xjmp 0x52c9
    exact fb_revert hcode h
  · apply ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hcd,
      show (Bytes.toB256 [4]).toNat = 4 by decide]
    exact hlen

/-- **The last test misses** (`future_owner`, `0x52a2`): the dispatcher falls to the shared
`REVERT`. -/
theorem fb_skip_1ec0cdc1 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x52a2 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0x1ec0cdc1) : False := by
  xs 0x52a7 (.push [0x1e, 0xc0, 0xcd, 0xc1] (by decide)) ri_push
  xs 0x52a9 (.push [0x00] (by decide)) ri_push
  xs 0x52aa (.reg .mload) ri_mload_vy0
  xs 0x52ab (.reg .eq) ri_eq
  xs 0x52ac (.reg .iszero) ri_iszero
  xs 0x52af (.push [0x52, 0xc8] (by decide)) ri_push
  xji 0x52b0 0x52c8 hw
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x52c9
  exact fb_revert hcode h

/-- **A selector missing every test reverts**: the 38 skips run into the shared `REVERT`. -/
theorem fb_miss {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hmiss : ∀ s ∈ sels, Sevm.selector sevm ≠ s)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) : False := by
  have hm : ∀ k (hk : k < 38), Sevm.selector sevm ≠ sels[k] :=
    fun k hk => hmiss _ (List.getElem_mem (by rw [sels_length]; exact hk))
  obtain ⟨G1, h⟩ := dq_to_3040 hcode hlen hcd h (hm 0 (by decide)) (hm 1 (by decide))
    (hm 2 (by decide)) (hm 3 (by decide)) (hm 4 (by decide)) (hm 5 (by decide))
    (hm 6 (by decide)) (hm 7 (by decide))
  obtain ⟨G2, h⟩ := dq_to_499b hcode h (hm 8 (by decide)) (hm 9 (by decide)) (hm 10 (by decide))
    (hm 11 (by decide)) (hm 12 (by decide))
  obtain ⟨G3, h⟩ := dq_skip_5b5a1467 hcode h (hm 13 (by decide))
  obtain ⟨G4, h⟩ := dq_skip_4f12fe97 hcode h (hm 14 (by decide))
  obtain ⟨G5, h⟩ := dq_skip_226840fb hcode h (hm 15 (by decide))
  obtain ⟨G6, h⟩ := dq_skip_6b441a40 hcode h (hm 16 (by decide))
  obtain ⟨G7, h⟩ := dq_skip_6a1c05ae hcode h (hm 17 (by decide))
  obtain ⟨G8, h⟩ := dq_skip_86fbf193 hcode h (hm 18 (by decide))
  obtain ⟨G9, h⟩ := dq_skip_e2e7d264 hcode h (hm 19 (by decide))
  obtain ⟨G10, h⟩ := dq_skip_30c54085 hcode h (hm 20 (by decide))
  obtain ⟨G11, h⟩ := dq_skip_524c3901 hcode h (hm 21 (by decide))
  obtain ⟨G12, h⟩ := dq_skip_e3698853 hcode h (hm 22 (by decide))
  obtain ⟨G13, h⟩ := dq_skip_3046f972 hcode h (hm 23 (by decide))
  obtain ⟨G14, h⟩ := dq_skip_c6610657 hcode h (hm 24 (by decide))
  obtain ⟨G15, h⟩ := dq_skip_4903b0d1 hcode h (hm 25 (by decide))
  obtain ⟨G16, h⟩ := dq_skip_ddca3f43 hcode h (hm 26 (by decide))
  obtain ⟨G17, h⟩ := dq_skip_fee3f7f9 hcode h (hm 27 (by decide))
  obtain ⟨G18, h⟩ := dq_skip_8da5cb5b hcode h (hm 28 (by decide))
  obtain ⟨G19, h⟩ := dq_skip_5409491a hcode h (hm 29 (by decide))
  obtain ⟨G20, h⟩ := dq_skip_b4b577ad hcode h (hm 30 (by decide))
  obtain ⟨G21, h⟩ := dq_skip_2081066c hcode h (hm 31 (by decide))
  obtain ⟨G22, h⟩ := dq_skip_14052288 hcode h (hm 32 (by decide))
  obtain ⟨G23, h⟩ := dq_skip_405e28f8 hcode h (hm 33 (by decide))
  obtain ⟨G24, h⟩ := dq_skip_e0a0b586 hcode h (hm 34 (by decide))
  obtain ⟨G25, h⟩ := dq_skip_58680d0b hcode h (hm 35 (by decide))
  obtain ⟨G26, h⟩ := dq_skip_e3824462 hcode h (hm 36 (by decide))
  exact fb_skip_1ec0cdc1 hcode h (hm 37 (by decide))

/-- `decodeCall` gives `.other` only for short calldata or a selector missing every test. -/
theorem decodeCall_other {sevm : Sevm} (h : decodeCall sevm = .other) :
    sevm.data.length < 4 ∨ (4 ≤ sevm.data.length ∧ ∀ s ∈ sels, Sevm.selector sevm ≠ s) := by
  by_cases hlen : sevm.data.length < 4
  · exact Or.inl hlen
  refine Or.inr ⟨by omega, ?_⟩
  cases hf : sels.findIdx? (· = Sevm.selector sevm) with
  | none =>
    intro s hs he
    have := List.findIdx?_eq_none_iff.mp hf s hs
    rw [he] at this
    exact absurd (decide_eq_true rfl) (by rw [this]; decide)
  | some k =>
    exfalso
    have hk : k < 38 := by
      have := List.findIdx?_eq_some_iff_getElem.mp hf
      obtain ⟨hk, -⟩ := this
      rwa [sels_length] at hk
    have hc : callAt sevm k = .other := by
      rw [decodeCall, ite_eq_right hlen, hf] at h
      exact h
    match k, hk, hc with
    | k + 38, hk, _ => omega

/-- **Fallback: a selector miss or short calldata never succeeds.** A successful frame of the
pool's runtime, entered with empty stack and memory, decodes to a named call. -/
theorem pool_other_fails {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post)) (hcode : sevm.code = code)
    (hcd : sevm.data.length < 2 ^ 256) (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (hgas : pre.gasMeasure < 2 ^ 256) : decodeCall sevm ≠ .other := by
  intro hoth
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  rcases decodeCall_other hoth with hshort | ⟨hlen, hmiss⟩
  · exact fb_short hcode hshort hcd hx
  · exact fb_miss hcode hlen hcd hmiss hx

/-- **Static frames have no effect**: a successful, committing (`post.error = none`) static
frame on a covered fork whose target carries code keeps every account's storage and the log
list. -/
theorem pool_static_noEffect {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post)) (hs : sevm.isStatic = true)
    (hfork : CoveredFork sevm.benvStat.fork) (hpc : pre.getCode sevm.currentTarget ≠ .empty)
    (hcommit : post.error = none) :
    post.logs = pre.logs ∧ ∀ a, post.getStor a = pre.getStor a :=
  ⟨Exec.logs_eq_of_static_ok exc hs hfork post rfl, fun a => congrFun
    (Exec.getStor_committedPost_eq_of_static exc hs (by simp only [Execution.commits, hcommit,
      Option.isNone_none]) hfork
      (.inl (State.Protected.of_code_ne_nil (ByteArray.toList_ne_nil_of_ne_empty hpc)))) a⟩

end Blanc.Lift.Curve3Pool
