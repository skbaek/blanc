import Blanc.Lift.Usdc.Proxy.Check
import Blanc.Lift.Usdc.Constants
import Blanc.Lift.ReachWalk
import Blanc.Lift.InvWalkOps
import Blanc.Lift.WalkSteps
import Blanc.Lift.ExactLeaf
import Blanc.AddressSlotProofs

/-!
# Walking the proxy certificate (C2b)

The prefix and big-step walks over the generated proxy certificate (`Proxy.cert`) that the proxy
frame theorems (`ProxyForward.lean`) use.  Certificate-driven: every step is the inversion of the
checked tree's node (`rr_*` over a prefix reach, `rpw_*` over a big-step run, `ri_*` for the
instruction), never an unfolding of the bytes.

* The step kit (contract-neutral, hoist candidates): `ri_address`, `ri_dup_any`, `rr_branchTo`,
  the big-step node inversions `rpw_*`, `St.self'`.
* The internal getters: `_admin()` (entry 8) returns the admin word, `_implementation()`
  (entry 14) the implementation word; `_willFallback()` (entry 22) returns only for a caller
  other than the admin word (`willFallback_ret`).
-/

namespace Blanc.Lift

open Jaune Blanc

section Kit

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm} {b : Devm}
  {S : List B256} {M : Mem} {G : Nat} {f g : SFunc} {o : Outcome} {K : List SFunc} {T : Conf}

/-- Every machine is its own walk state. -/
theorem St.self' (d : Devm) : d = St d d.stack d.memory d.gasLeft := St.self rfl rfl

/-- `ADDRESS`, inverted. -/
theorem ri_address {d : Devm}
    (h : Ninst.Run sevm (St b S M G) (.reg .address) d) :
    ∃ G', d = St b (sevm.currentTarget.toB256 :: S) M G' := by
  have hp := of_run_address h
  have hs : d.stack = sevm.currentTarget.toB256 :: S := by
    have := hp.stack
    simpa only [Stack.Push, Split, St.stack, List.cons_append, List.nil_append] using this
  have e := St.of_stackRel hp
  rw [hs] at e
  exact ⟨_, e⟩

/-- `DUP n` over a stack whose `n`-th word is not named. -/
theorem ri_dup_any {n : Fin 16} {d : Devm}
    (h : Ninst.Run sevm (St b S M G) (.reg (.dup n)) d) :
    ∃ w, S[n.val]? = some w ∧ ∃ G', d = St b (w :: S) M G' := by
  obtain ⟨x, hx, -⟩ := of_run_dup h
  simp only [St.stack] at hx
  exact ⟨x, hx, ri_dup hx h⟩

theorem rr_branchTo {k : Nat} {dd w : B256}
    (run : Reach P fs sevm ⟨St b (dd :: w :: S) M G, .branchTo f k, K⟩ T) (hT : AtExec T) :
    (w = 0 ∧ ∃ G', Reach P fs sevm ⟨St b S M G', f, K⟩ T) ∨
      (w ≠ 0 ∧ ∃ g G', fs[k]? = some g ∧ Reach P fs sevm ⟨St b S M G', g, K⟩ T) := by
  rcases Reach.branchTo run hT with ⟨t, d', pop, rest⟩ | ⟨t, w0, g, d', hw, hk, pop, rest⟩
  · obtain ⟨-, hw, e⟩ := St.of_pop2 pop
    exact .inl ⟨hw, _, e ▸ rest⟩
  · obtain ⟨-, hw', e⟩ := St.of_pop2 pop
    exact .inr ⟨hw' ▸ hw, g, _, hk, e ▸ rest⟩

theorem rr_jump {k : Nat} {dd : B256}
    (run : Reach P fs sevm ⟨St b (dd :: S) M G, .jump k, K⟩ T) (hT : AtExec T) :
    ∃ g G', fs[k]? = some g ∧ Reach P fs sevm ⟨St b S M G', g, K⟩ T := by
  obtain ⟨t, g, d', hk, pop, rest⟩ := Reach.jump run hT
  exact ⟨g, _, hk, (St.of_pop1 pop).2 ▸ rest⟩

/-! ### Big-step node inversions -/

theorem rpw_next {n : Ninst} {d : Devm} (run : SFunc.RunP P fs sevm d (.next n f) o) :
    ∃ d', P sevm d n d' ∧ SFunc.RunP P fs sevm d' f o := by
  cases run with
  | next h k => exact ⟨_, h, k⟩

theorem rpw_dest (run : SFunc.RunP P fs sevm (St b S M G) (.dest f) o) :
    ∃ G', SFunc.RunP P fs sevm (St b S M G') f o := by
  cases run with
  | dest h k => exact ⟨_, (St.of_burn h) ▸ k⟩

theorem rpw_branch {dd w : B256}
    (run : SFunc.RunP P fs sevm (St b (dd :: w :: S) M G) (.branch f g) o) :
    (w = 0 ∧ ∃ G', SFunc.RunP P fs sevm (St b S M G') f o) ∨
      (w ≠ 0 ∧ ∃ G', SFunc.RunP P fs sevm (St b S M G') g o) := by
  cases run with
  | zero d0 h k =>
      obtain ⟨-, hw, e⟩ := St.of_pop2 h
      exact .inl ⟨hw, _, e ▸ k⟩
  | succ d0 w0 hw h k =>
      obtain ⟨-, hw', e⟩ := St.of_pop2 h
      exact .inr ⟨hw' ▸ hw, _, e ▸ k⟩

/-- An internal call in a returning run: the callee returns, then the continuation runs. -/
theorem rpw_callRet {k : Nat} {dd : B256} {D : Devm} (hk : fs[k]? = some g)
    (run : SFunc.RunP P fs sevm (St b (dd :: S) M G) (.callNext k f) (.returned D)) :
    ∃ G' D', SFunc.RunP P fs sevm (St b S M G') g (.returned D') ∧
      SFunc.RunP P fs sevm D' f (.returned D) := by
  cases run with
  | callRet d0 hk' h hr k =>
      rw [hk] at hk'
      cases hk'
      exact ⟨_, _, (St.of_pop1 h).2 ▸ hr, k⟩

theorem rpw_ret {dd : B256} {D : Devm}
    (run : SFunc.RunP P fs sevm (St b (dd :: S) M G) .ret (.returned D)) :
    ∃ G', D = St b S M G' := by
  cases run with
  | ret d0 h => exact ⟨_, (St.of_pop1 h).2⟩

/-- No returning run of a halting tree: no `.ret` and no reference. -/
def SFunc.haltsOnly : SFunc → Bool
  | .next _ f => f.haltsOnly
  | .dest f => f.haltsOnly
  | .branch f g => f.haltsOnly && g.haltsOnly
  | .last _ => true
  | .undefined => true
  | _ => false

theorem SFunc.RunP.not_returned_of_haltsOnly {d D : Devm}
    (run : SFunc.RunP P fs sevm d f (.returned D)) (h : f.haltsOnly = true) : False := by
  generalize ho : Outcome.returned D = o at run
  induction run with
  | zero _ _ _ ih => simp only [SFunc.haltsOnly, Bool.and_eq_true] at h; exact ih h.1 ho
  | succ _ _ _ _ _ ih => simp only [SFunc.haltsOnly, Bool.and_eq_true] at h; exact ih h.2 ho
  | next _ _ ih => exact ih h ho
  | dest _ _ ih => exact ih h ho
  | last _ => cases ho
  | _ => simp only [SFunc.haltsOnly, Bool.false_eq_true] at h

end Kit

end Blanc.Lift

namespace Blanc.Lift.Usdc.Proxy

open Jaune Blanc Blanc.Lift

/-- The proxy program. -/
abbrev prog : List SFunc := cert.prog

theorem adminSlot_word : Bytes.toB256 [0x01] * Bytes.toB256 [0x10, 0xd6, 0xa5, 0x4a, 0x47, 0x54,
    0xc8, 0x86, 0x9d, 0x68, 0x86, 0xb5, 0xf5, 0xd7, 0xfb, 0xfa, 0x5b, 0x45, 0x22, 0x23, 0x7e, 0xa5,
    0xc6, 0x0d, 0x11, 0xbc, 0x4e, 0x7a, 0x1f, 0xf9, 0x39, 0x0b] = adminSlot := by
  decide +kernel

theorem implSlot_word : Bytes.toB256 [0x01] * Bytes.toB256 [0x70, 0x50, 0xc9, 0xe0, 0xf4, 0xca,
    0x76, 0x9c, 0x69, 0xbd, 0x3a, 0x8e, 0xf7, 0x40, 0xbc, 0x37, 0x93, 0x4f, 0x8e, 0x2c, 0x03, 0x6e,
    0x5a, 0x72, 0x3f, 0xd8, 0xee, 0x04, 0x8e, 0xd3, 0xf8, 0xc3] = implSlot := by
  decide +kernel

theorem iszero_ne {x : B256} (h : B256.eqCheck x 0 ≠ 0) : x = 0 := by
  unfold B256.eqCheck at h
  split at h
  · assumption
  · exact (h rfl).elim

theorem eqCheck_eq_zero {x y : B256} (h : B256.eqCheck x y = 0) : x ≠ y := by
  intro hxy
  unfold B256.eqCheck at h
  split at h
  · exact absurd h (by decide)
  · contradiction

theorem eqCheck_ne_zero {x y : B256} (h : B256.eqCheck x y ≠ 0) : x = y := by
  unfold B256.eqCheck at h
  split at h
  · assumption
  · exact (h rfl).elim

theorem iszero_eq_zero {x : B256} (h : B256.eqCheck x 0 = 0) : x ≠ 0 := eqCheck_eq_zero h

theorem ff20_caller (a : Adr) :
    Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& a.toB256 = a.toB256 := by
  rw [ff20_and_word, toAdr_toB256]

/-- The masked comparison of the caller with a word decides the caller's equality with the word's
address. -/
theorem masked_eq_iff (a : Adr) (v : B256) :
    (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& a.toB256 =
     Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& v) ↔ a = v.toAdr := by
  rw [ff20_caller, ff20_and_word]
  constructor
  · intro h
    have := congrArg B256.toAdr h
    rwa [toAdr_toB256, toAdr_toB256] at this
  · intro h
    rw [h]

section Getters

variable {P : Sevm → Devm → Ninst → Devm → Prop} (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
  {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

include hP

/-- `_admin()`: the admin word, after one storage read. -/
theorem admin_ret (hfork : CoveredFork sevm.benvStat.fork) {r : B256} {D : Devm}
    (run : SFunc.RunP P prog sevm (St b (r :: S) M G) t_06a8_c8 (.returned D)) :
    ∃ G', D = St (afterSload sevm b adminSlot)
      (b.getStorVal sevm.currentTarget adminSlot :: S) M G' := by
  unfold t_06a8_c8 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_mul (hP s)
  rw [adminSlot_word] at run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_sload hfork (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  exact rpw_ret run

/-- `_implementation()`: the implementation word, after one storage read. -/
theorem impl_ret (hfork : CoveredFork sevm.benvStat.fork) {r : B256} {D : Devm}
    (run : SFunc.RunP P prog sevm (St b (r :: S) M G) t_0651_c14 (.returned D)) :
    ∃ G', D = St (afterSload sevm b implSlot)
      (b.getStorVal sevm.currentTarget implSlot :: S) M G' := by
  unfold t_0651_c14 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_mul (hP s)
  rw [implSlot_word] at run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_sload hfork (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  exact rpw_ret run

/-- `_willFallback()` returns only for a caller other than the admin word. -/
theorem willFallback_ret (hfork : CoveredFork sevm.benvStat.fork) {r : B256} {D : Devm}
    (run : SFunc.RunP P prog sevm (St b (r :: S) M G) t_0576_c22 (.returned D)) :
    sevm.caller ≠ (b.getStorVal sevm.currentTarget adminSlot).toAdr ∧
      ∃ G', D = St (afterSload sevm b adminSlot) S M G' := by
  unfold t_0576_c22 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D1, callee, run⟩ := rpw_callRet (k := 8) rfl run
  obtain ⟨_, rfl⟩ := admin_ret hP hfork callee
  unfold t_057e_c22 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_caller (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_eq (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rpw_branch run with ⟨-, _, run⟩ | ⟨hc, _, run⟩
  · exact (SFunc.RunP.not_returned_of_haltsOnly run (by decide)).elim
  refine ⟨fun h => eqCheck_eq_zero (iszero_ne (iszero_eq_zero (iszero_ne hc))) ((masked_eq_iff _ _).mpr h), ?_⟩
  unfold t_0647_c22 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D2, callee, run⟩ := rpw_callRet (k := 31) rfl run
  unfold t_0777_c31 at callee
  obtain ⟨_, callee⟩ := rpw_dest callee
  obtain ⟨_, rfl⟩ := rpw_ret callee
  unfold t_064f_c22 at run
  obtain ⟨_, run⟩ := rpw_dest run
  exact rpw_ret run

end Getters

end Blanc.Lift.Usdc.Proxy

namespace Blanc.Lift.Usdc.Proxy

open Jaune Blanc Blanc.Lift

/-- The `_fallback()` body, one copy per caller context: `_willFallback()`, then
`_delegate(_implementation())`, entered at the delegate copy `d`. -/
def fbTree (d : Nat) : SFunc :=
  .dest (.next (.push [0x02, 0x01] (by decide)) (.next (.push [0x05, 0x76] (by decide))
    (.callNext 22 (.dest (.next (.push [0x02, 0x11] (by decide)) (.next (.push [0x02, 0x0c] (by decide))
      (.next (.push [0x06, 0x51] (by decide)) (.callNext 14 (.dest (.next (.push [0x06, 0x82] (by decide))
        (.jump d)))))))))))

theorem fb_6 : t_01f9_c6 = fbTree 23 := rfl
theorem fb_7 : t_01f9_c7 = fbTree 24 := rfl
theorem fb_11 : t_01f9_c11 = fbTree 26 := rfl
theorem fb_13 : t_01f9_c13 = fbTree 27 := rfl
theorem fb_16 : t_01f9_c16 = fbTree 28 := rfl
theorem fb_19 : t_01f9_c19 = fbTree 29 := rfl
theorem fb_21 : t_01f9_c21 = fbTree 30 := rfl

/-- Every delegate copy is the same tree. -/
theorem dl_24 : t_0682_c24 = t_0682_c23 := rfl
theorem dl_26 : t_0682_c26 = t_0682_c23 := rfl
theorem dl_27 : t_0682_c27 = t_0682_c23 := rfl
theorem dl_28 : t_0682_c28 = t_0682_c23 := rfl
theorem dl_29 : t_0682_c29 = t_0682_c23 := rfl
theorem dl_30 : t_0682_c30 = t_0682_c23 := rfl

/-- The getters and `_willFallback()` make no external call. -/
def getterEntries : List Nat := [8, 14, 22, 31]

theorem getters_execFree : ExecFreeSet prog getterEntries = true := by decide

section Fallback

variable {P : Sevm → Devm → Ninst → Devm → Prop} (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
  {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}

include hP

/-- **The fallback reaches only its `DELEGATECALL`.**  A prefix reach from a `_fallback()` copy to
an external instruction passes `_willFallback()` (so the caller is not the admin word) and stops at
the `DELEGATECALL` of `_delegate`, whose operands are the remaining gas, the implementation word,
and the input window `[0, calldatasize)` that `CALLDATACOPY` has just filled with the calldata. -/
theorem fallback_reach (hfork : CoveredFork sevm.benvStat.fork) {d : Nat}
    (hd : prog[d]? = some t_0682_c23)
    (run : Reach P prog sevm ⟨St b S M G, fbTree d, K⟩ T) (hT : AtExec T) :
    sevm.caller ≠ (b.getStorVal sevm.currentTarget adminSlot).toAdr ∧
      ∃ (g : B256) (rest : SFunc) (G' : Nat), T = ⟨St (afterSload sevm (afterSload sevm b adminSlot) implSlot)
        (g :: b.getStorVal sevm.currentTarget implSlot :: 0 :: sevm.data.length.toB256 :: 0 :: 0 ::
          b.getStorVal sevm.currentTarget implSlot :: Bytes.toB256 [0x02, 0x11] :: S)
        (M.write 0 (sevm.data.sliceD 0 sevm.data.length.toB256.toNat 0)) G',
        .next (.exec .delegatecall) rest, K⟩ := by
  unfold fbTree at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D, callee, run⟩ := rr_callOver getters_execFree (k := 22) rfl (by decide) run hT
  obtain ⟨notAdmin, _, rfl⟩ := willFallback_ret hP hfork callee
  refine ⟨notAdmin, ?_⟩
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D, callee, run⟩ := rr_callOver getters_execFree (k := 14) rfl (by decide) run hT
  obtain ⟨_, rfl⟩ := impl_ret hP hfork callee
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨g, _, hg, run⟩ := rr_jump run hT
  rw [hd] at hg
  cases hg
  unfold t_0682_c23 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatacopy (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨w, _, rfl⟩ := ri_gas (hP s)
  rcases Reach.exec run with rfl | ⟨_, -, run⟩
  · exact ⟨w, _, _, by rw [getStorVal_afterSload]; rfl⟩
  · obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    rcases Reach.branch run hT with ⟨_, _, -, run⟩ | ⟨_, _, _, -, -, run⟩
    · unfold t_069f_c23 at run
      obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
      obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
      exact (Reach.not_last run hT).elim
    · unfold t_06a3_c23 at run
      obtain ⟨_, -, run⟩ := Reach.dest run hT
      obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
      obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
      exact (Reach.not_last run hT).elim

end Fallback

end Blanc.Lift.Usdc.Proxy
