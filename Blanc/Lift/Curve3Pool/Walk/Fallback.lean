import Blanc.Lift.Curve3Pool.Walk.Dispatch
import Blanc.Lift.Quiet
import Blanc.StaticStorage

/-!
# The dispatcher's fall-through, and static frames

`pool_other_fails`: a successful frame of the pool's runtime never decodes to `.other`. Short
calldata (`< 4` bytes) jumps from the prologue's length test to the shared `REVERT` at `0x52c9`;
a selector that misses every test runs the 38 skips (`xa_dispatch_miss`, walked by evaluation)
into the same `REVERT`.

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
  · apply B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hcd,
      show (Bytes.toB256 [4]).toNat = 4 by decide]
    exact hlen

/-- **A selector missing every test reverts**: the 38 skips run into the shared `REVERT`. -/
theorem fb_miss {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hmiss : ∀ s ∈ sels, Sevm.selector sevm ≠ s)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) : False := by
  obtain ⟨_, h⟩ := xa_dispatch_miss hcode hlen hcd hmiss h
  exact fb_revert hcode h

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

/-- **Static frames write no storage and emit no logs**: a successful, committing
(`post.error = none`) static frame on a covered fork whose target carries code writes no
storage at any address (`post.getStor a = pre.getStor a` for every `a`) and emits no logs
(`post.logs = pre.logs`). -/
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
