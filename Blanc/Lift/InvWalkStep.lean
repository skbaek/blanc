import Blanc.Lift.InvWalkWorld
import Blanc.Lift.WalkSteps
import Blanc.AddressSlotProofs
import Blanc.ForwardStorageAccess
import Blanc.Lift.MapSlot

/-!
# A one-lemma inversion step, and the inversion helpers of solc walks

`stepX` computes the successor walk state `St b' S' M'` of the straight-line instructions an
inversion walk crosses (stack, memory, the selected `SLOAD`/`SSTORE` bases, `LOG3`), and
`ri_stepX` inverts any of them at once; the `istep` tactic runs one such step (or a `JUMPDEST`)
of a cut run, so a straight-line segment is `repeat istep h`.  `ibranch` crosses a conditional
jump whose other arm only reverts (`SFunc.noOk`).  `ric_callR` enters an internal callee that
cannot halt; `SFunc.noExit`/`NoExitSet` with `SFunc.RunP.false_of_noExit` close an arm that can
only revert through loops and gotos (a solc error-message copy).  `ret_named` names a returned
state by its storage.  The word facts read solc's comparison flags, mapping-slot scratch
writes, address masks and SafeMath guards as natural-number facts.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune Blanc

/-- The successor of a straight-line instruction over the walk state `St b S M G`, when the
instruction is one of the forms below: base, stack and memory. -/
def stepX (sevm : Sevm) : Ninst → Devm → List B256 → Mem → Option (Devm × List B256 × Mem)
  | .push xs _, b, S, M => some (b, xs.toB256 :: S, M)
  | .reg (.dup n), b, S, M => S[n.val]?.map fun w => (b, w :: S, M)
  | .reg (.swap n), b, S, M => (Jaune.List.swap S n.val).map fun S' => (b, S', M)
  | .reg .pop, b, _ :: S, M => some (b, S, M)
  | .reg .and, b, x :: y :: S, M => some (b, (x &&& y) :: S, M)
  | .reg .or, b, x :: y :: S, M => some (b, (x ||| y) :: S, M)
  | .reg .add, b, x :: y :: S, M => some (b, (x + y) :: S, M)
  | .reg .sub, b, x :: y :: S, M => some (b, (x - y) :: S, M)
  | .reg .div, b, x :: y :: S, M => some (b, (x / y) :: S, M)
  | .reg .eq, b, x :: y :: S, M => some (b, B256.eqCheck x y :: S, M)
  | .reg .lt, b, x :: y :: S, M => some (b, B256.ltCheck x y :: S, M)
  | .reg .gt, b, x :: y :: S, M => some (b, B256.gtCheck x y :: S, M)
  | .reg .shr, b, x :: y :: S, M => some (b, (y >>> x.toNat) :: S, M)
  | .reg .iszero, b, x :: S, M => some (b, B256.eqCheck x 0 :: S, M)
  | .reg .not, b, x :: S, M => some (b, (~~~ x) :: S, M)
  | .reg .caller, b, S, M => some (b, sevm.caller.toB256 :: S, M)
  | .reg .callvalue, b, S, M => some (b, sevm.value :: S, M)
  | .reg .calldatasize, b, S, M => some (b, sevm.data.length.toB256 :: S, M)
  | .reg .calldataload, b, x :: S, M => some (b, Sevm.dataWord sevm x :: S, M)
  | .reg .mload, b, i :: S, M =>
      some (b, Bytes.toB256 (M.read i.toNat 32).1 :: S, (M.read i.toNat 32).2)
  | .reg .mstore, b, i :: v :: S, M => some (b, S, M.write i.toNat v.toBytes)
  | .reg .codecopy, b, di :: ci :: sz :: S, M =>
      some (b, S, M.write di.toNat (sevm.code.sliceD ci.toNat sz.toNat (Linst.toUInt8 .stop)))
  | .reg .keccak256, b, i :: sz :: S, M =>
      some (b, (M.read i.toNat sz.toNat).1.keccak :: S, (M.read i.toNat sz.toNat).2)
  | .reg .sload, b, k :: S, M =>
      some (afterSload sevm b k, b.getStorVal sevm.currentTarget k :: S, M)
  | .reg .sstore, b, k :: v :: S, M => some (afterSstore sevm b k v, S, M)
  | .reg (.log 3), b, i :: sz :: t1 :: t2 :: t3 :: S, M =>
      some (b.addLog ⟨sevm.currentTarget, [t1, t2, t3], (M.read i.toNat sz.toNat).1⟩, S,
        (M.read i.toNat sz.toNat).2)
  | _, _, _, _ => none

theorem ri_stepX {sevm : Sevm} {b b' d : Devm} {S S' : List B256} {M M' : Mem} {G : Nat}
    {n : Ninst} (fork : CoveredFork sevm.benvStat.fork)
    (h : Ninst.Run sevm (St b S M G) n d) (hs : stepX sevm n b S M = some (b', S', M')) :
    ∃ G', d = St b' S' M' G' := by
  unfold stepX at hs
  split at hs
  · cases hs; exact ri_push h
  · rename_i n
    rcases hget : S[n.val]? with _ | w <;> rw [hget] at hs <;> cases hs
    exact ri_dup hget h
  · rename_i n
    rcases hsw : Jaune.List.swap S n.val with _ | T <;> rw [hsw] at hs <;> cases hs
    exact ri_swap hsw h
  · cases hs; exact ri_pop h
  · cases hs; exact ri_and h
  · cases hs; exact ri_or h
  · cases hs; exact ri_add h
  · cases hs; exact ri_sub h
  · cases hs; exact ri_div h
  · cases hs; exact ri_eq h
  · cases hs; exact ri_lt h
  · cases hs; exact ri_gt h
  · cases hs; exact ri_shr h
  · cases hs; exact ri_iszero h
  · cases hs; exact ri_not h
  · cases hs; exact ri_caller h
  · cases hs; exact ri_callvalue h
  · cases hs; exact ri_calldatasize h
  · cases hs; exact ri_calldataload h
  · cases hs; exact ri_mload h
  · cases hs; exact ri_mstore h
  · cases hs; exact ri_codecopy h
  · cases hs; exact ri_keccak h
  · cases hs; exact ri_sload fork h
  · cases hs; exact ri_sstore fork h
  · cases hs; exact ri_log3 h
  · cases hs

macro "istep " h:ident : tactic => `(tactic|
  first
  | (have h' := ric_dest $h; clear $h; obtain ⟨_, $h:ident⟩ := h')
  | (have h' := ric_next $h; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
     obtain ⟨_, e⟩ := ri_stepX ‹CoveredFork _› hd rfl
     try dsimp only [List.set, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at e
     subst e; clear hd))

/-- A solc mapping slot from its scratch writes (`mstore(0, key)`, `mstore(32, base)`,
`keccak256(0, 64)`), with the pushed offsets as the code has them. -/
theorem keccak_scratch (μ : Mem) (key base : B256) :
    (((μ.write (Bytes.toB256 [0]).toNat key.toBytes).write (Bytes.toB256 [32]).toNat
      base.toBytes).read (Bytes.toB256 [0]).toNat (Bytes.toB256 [64]).toNat).1.keccak =
      Blanc.Lift.mapSlot key base := by
  have e := Mem.read_two_word_writes_at_raw μ 0 key base
  exact congrArg Bytes.keccak e

theorem keccak_scratch' (μ : Mem) (key base : B256) :
    (((μ.write (Bytes.toB256 [32]).toNat base.toBytes).write (Bytes.toB256 [0]).toNat
      key.toBytes).read (Bytes.toB256 [0]).toNat (Bytes.toB256 [64]).toNat).1.keccak =
      Blanc.Lift.mapSlot key base := by
  have e := Mem.read_two_word_writes_at_raw_right_first μ 0 key base
  exact congrArg Bytes.keccak e


/-- An internal call to a callee that cannot halt the frame returns into its continuation. -/
theorem ric_callR {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256}
    {M : Mem} {G : Nat} {f g : SFunc} {r : Seg} {k : Nat} {dd : B256}
    (hk : fs[k]? = some g) (nh : ∀ {d D}, ¬ SFunc.Run fs sevm d g (.halted D))
    (run : SFunc.RunCut fs sevm C (St b (dd :: S) M G) (.callNext k f) r) :
    ∃ G' D, SFunc.Run fs sevm (St b S M G') g (.returned D) ∧ SFunc.RunCut fs sevm C D f r := by
  rcases ric_call hk run with ⟨G', ⟨D, h1, h2⟩ | ⟨D, h1, _⟩⟩
  · exact ⟨G', D, h1, h2⟩
  · exact (nh h1).elim


/-- Trees with no exit at all: only `REVERT`/`undefined` terminals, no return. -/
def SFunc.noExit : SFunc → Bool
  | .branch f g => f.noExit && g.noExit
  | .branchTo f _ => f.noExit
  | .last l => l == .revert
  | .next _ f => f.noExit
  | .dest f => f.noExit
  | .jump _ => true
  | .callNext _ f => f.noExit
  | .ret => false
  | .pcAt _ f => f.noExit
  | .undefined => true

/-- `S` is closed under the entries referenced by its members, and none of them exits. -/
def NoExitSet (fs : List SFunc) (S : List Nat) : Bool :=
  S.all fun k => match fs[k]? with
    | some g => g.noExit && g.refs.all (· ∈ S)
    | none => false

/-- A tree in a `NoExitSet` has no run at all (it can only revert). -/
theorem SFunc.RunP.false_of_noExit {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {S : List Nat} (hS : NoExitSet fs S = true)
    {sevm : Sevm} {devm : Devm} {f : SFunc} {o : Outcome}
    (hf : f.noExit = true) (hrefs : f.refs.all (· ∈ S) = true)
    (run : SFunc.RunP P fs sevm devm f o) : False := by
  have closed : ∀ {k g}, k ∈ S → fs[k]? = some g →
      g.noExit = true ∧ g.refs.all (· ∈ S) = true := by
    intro k g hk hget
    have h := (List.all_eq_true.mp hS) k hk
    rw [hget] at h
    simpa only [List.all_eq_true, decide_eq_true_eq, Bool.and_eq_true] using h
  induction run with
  | zero d pop run ih =>
      simp only [SFunc.noExit, Bool.and_eq_true] at hf
      simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at hrefs
      exact ih hf.1 hrefs.1
  | succ d w hnz pop run ih =>
      simp only [SFunc.noExit, Bool.and_eq_true] at hf
      simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at hrefs
      exact ih hf.2 hrefs.2
  | toZero d pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      exact ih hf hrefs.2
  | toSucc d w hnz lookup pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have ht := closed (of_decide_eq_true hrefs.1) lookup
      exact ih ht.1 ht.2
  | last hrun =>
      rename_i l
      simp only [SFunc.noExit] at hf
      have : l = .revert := by
        revert hf
        cases l <;> decide
      subst this
      exact Linst.not_run_revert_ok hrun
  | next hrun run ih => exact ih hf hrefs
  | dest burn run ih => exact ih hf hrefs
  | jump d lookup pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have ht := closed (of_decide_eq_true hrefs.1) lookup
      exact ih ht.1 ht.2
  | ret => simp only [SFunc.noExit, Bool.false_eq_true] at hf
  | callHalt d lookup pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have ht := closed (of_decide_eq_true hrefs.1) lookup
      exact ih ht.1 ht.2
  | callRet d lookup pop run tail ihRun ihTail =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      simp only [SFunc.noExit] at hf
      exact ihTail hf hrefs.2
  | pcAt _ _ run ih =>
      simp only [SFunc.noExit] at hf
      simp only [SFunc.refs] at hrefs
      exact ih hf hrefs

/-- Name a returned state by its storage only. -/
theorem ret_named {o : Outcome} {B : Devm} {S : List B256} {M : Mem} {G : Nat}
    (e : Seg.done o = Seg.done (.returned (St B S M G))) :
    ∃ b' M' G', o = .returned (St b' S M' G') ∧ Devm.getStor b' = Devm.getStor B :=
  ⟨B, M, G, Seg.done.inj e, rfl⟩

/-- A conditional jump of a cut run: the arm that reverts closes, the other is kept with its
condition. -/
macro "ibranch " h:ident c:ident : tactic => `(tactic|
  (have h' := ric_branch $h; clear $h; rcases h' with ⟨$c, _, $h⟩ | ⟨$c, _, $h⟩ <;>
    try (exact (SFunc.RunCutP.false_of_noOk $h (by decide)).elim)))


/-! ## Word facts of the comparison flags -/

/-- A word whose shift by 255 is not `1` is below `2 ^ 255` (its top bit is clear). -/
theorem toNat_lt_of_shr_ne_one {w : B256} (h : w >>> 255 ≠ 1) : w.toNat < 2 ^ 255 := by
  have hw := B256.toNat_eq w
  have h1 := B128.toNat_eq w.1
  have bl := B128.toNat_lt (x := w.2)
  have bhl := UInt64.toNat_lt w.1.2
  have bhh := UInt64.toNat_lt w.1.1
  by_contra c
  apply h
  have top : 2 ^ 63 ≤ w.1.1.toNat := by
    by_contra c'
    have : w.1.toNat < 2 ^ 127 := by omega
    omega
  rcases w with ⟨⟨hh, hl⟩, ⟨lh, ll⟩⟩
  have e : B256.shiftRight (⟨⟨hh, hl⟩, ⟨lh, ll⟩⟩ : B256) 255 =
      (⟨⟨0, 0⟩, ⟨0, hh >>> 63⟩⟩ : B256) := rfl
  have one : hh >>> 63 = 1 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_shiftRight]
    change hh.toNat >>> 63 = 1
    rw [Nat.shiftRight_eq_div_pow]
    change 2 ^ 63 ≤ hh.toNat at top
    change hh.toNat < 2 ^ 64 at bhh
    omega
  change B256.shiftRight (⟨⟨hh, hl⟩, ⟨lh, ll⟩⟩ : B256) 255 = 1
  rw [e, one]
  rfl



theorem ne_zero_of_iszero_eq {c : B256} (h : B256.eqCheck c 0 = 0) : c ≠ 0 := by
  intro e
  rw [e] at h
  exact absurd h (by decide)

/-- SafeMath `add`'s guard `!(x + y < y)`: no wrap, the word sum is the natural sum. -/
theorem add_nof_of_ltCheck {x y : B256} (h : B256.ltCheck (x + y) y = 0) :
    x.toNat + y.toNat < 2 ^ 256 ∧ (x + y).toNat = x.toNat + y.toNat := by
  have h1 := toNat_ge_of_ltCheck_eq_zero h
  rw [B256.toNat_add] at h1 ⊢
  have hx := B256.toNat_lt x
  have hy := B256.toNat_lt y
  unfold Nat.lo at h1 ⊢
  by_cases o : x.toNat + y.toNat < 2 ^ 256
  · exact ⟨o, Nat.mod_eq_of_lt o⟩
  · exfalso
    have e : (x.toNat + y.toNat) % 2 ^ 256 = x.toNat + y.toNat - 2 ^ 256 := by
      rw [Nat.mod_eq_sub_mod (Nat.le_of_not_lt o), Nat.mod_eq_of_lt (by omega)]
    omega


theorem ne_of_eqCheck_eq_zero {x y : B256} (h : B256.eqCheck x y = 0) : x ≠ y := by
  intro e
  unfold B256.eqCheck at h
  simp only [e, ↓reduceIte] at h
  exact absurd h (by decide)


theorem le_of_gt_check {x y : B256} (h : B256.eqCheck (B256.gtCheck x y) 0 ≠ 0) :
    x.toNat ≤ y.toNat :=
  toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero h)

theorem word_ff20 (x : B256) :
    (x &&& Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) = x.toAdr.toB256 := by
  rw [B256.and_comm]
  exact ff20_and_word x


theorem sub_word {a x : B256} (h : x.toNat ≤ a.toNat) :
    a - x = Nat.toB256 (a.toNat - x.toNat) := by
  rw [← toB256_toNat (a - x), B256.toNat_sub_eq_of_le a x (B256.le_iff_toNat_le_toNat.mpr h)]

theorem add_word {x a : B256} (h : x.toNat + a.toNat < 2 ^ 256) :
    x + a = Nat.toB256 (x.toNat + a.toNat) := by
  rw [← toB256_toNat (x + a), B256.toNat_add, Nat.lo, Nat.mod_eq_of_lt h]


theorem adr_ne_zero_of_mask {z : B256}
    (h : (z &&& Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) ≠ 0) : z.toAdr ≠ 0 := by
  rw [word_ff20] at h
  intro e
  apply h
  rw [e]
  rfl

theorem getStorVal_of_getStor {b b' : Devm} (h : Devm.getStor b' = Devm.getStor b) :
    b'.getStorVal = b.getStorVal := by
  funext a k
  show (Devm.getStor b' a).get k = (Devm.getStor b a).get k
  rw [h]

theorem gsv (b : Devm) (a : Adr) (k : B256) : b.getStorVal a k = (Devm.getStor b a).get k := rfl


end Blanc.Lift
