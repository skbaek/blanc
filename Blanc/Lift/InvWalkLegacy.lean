import Blanc.Lift.InvWalkStep
import Blanc.Lift.InvWalkDispatch
import Blanc.Lift.AccumulatedWalk
import Blanc.Lift.CodeSizeWalk
import Blanc.Lift.MutableCallPost

/-!
# Inversion walks of old-solc frames

The step, branch and normalization tactics shared by the inversion walks of pre-0.5 solc runtimes:
`EXP`-based packed reads, `MUL`, `div`-and-mask selector extraction, mapping hashes whose offsets
are `ADD`-chained literals, and memory a storage walk never reads back.  Nothing here names a
contract.
-/

namespace Blanc.Lift

open Jaune Blanc

/-- A straight-line step: `istep`, or the `EXP`/`MUL` steps it does not cover, or an unconditional
goto. -/
macro "ustep " h:ident : tactic => `(tactic|
  first
  | istep $h
  | (have h' := ric_next $h; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
     obtain ⟨_, e⟩ := ri_exp hd
     subst e; clear hd)
  | (have h' := ric_next $h; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
     obtain ⟨_, e⟩ := ri_mul hd
     subst e; clear hd)
  | (have h' := ric_jump List.not_mem_nil rfl $h; clear $h; obtain ⟨_, $h:ident⟩ := h'))

/-- A `LOG1` step of a storage walk: the log's data is forgotten, the storage kept. -/
theorem ric_log1_keep {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {i sz t : B256}
    {S : List B256} {M : Mem} {G : Nat} {f : SFunc} {r : Seg}
    (run : SFunc.RunCut fs sevm C (St b (i :: sz :: t :: S) M G) (.next (.reg (.log 1)) f) r) :
    ∃ b' M' G', SFunc.RunCut fs sevm C (St b' S M' G') f r ∧ Devm.getStor b' = Devm.getStor b := by
  obtain ⟨_, hd, h⟩ := ric_next run
  obtain ⟨G', e⟩ := ri_log1 hd
  subst e
  exact ⟨_, _, G', h, by simp only [Devm.addLog_getStor]⟩

/-- A `CALL` step: the run across it, and the continuation from the state it left, its stack the
result flag over `S`. -/
theorem ric_call_step {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm}
    {g c v ii is oi os : B256} {S : List B256} {M : Mem} {G : Nat} {f : SFunc} {r : Seg}
    (hfork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCut fs sevm C (St b (g :: c :: v :: ii :: is :: oi :: os :: S) M G)
      (.next (.exec .call) f) r) :
    ∃ d flag M' G', Ninst.Run sevm (St b (g :: c :: v :: ii :: is :: oi :: os :: S) M G) (.exec .call) d ∧
      SFunc.RunCut fs sevm C (St d (flag :: S) M' G') f r := by
  obtain ⟨d, hd, h⟩ := ric_next run
  obtain ⟨flag, hp⟩ := ri_call_post hfork hd
  refine ⟨d, flag, d.memory, d.gasLeft, hd, ?_⟩
  rwa [St.self hp.stack rfl] at h

/-- An `EXTCODESIZE` step. -/
macro "ucodesize " h:ident : tactic => `(tactic|
  (have h' := ric_next $h; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
   obtain ⟨_, e⟩ := ri_extcodesize ‹CoveredFork _› hd
   subst e; clear hd))

/-- A `GAS` step. -/
macro "ugas " h:ident : tactic => `(tactic|
  (have h' := ric_next $h; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
   obtain ⟨_, _, e⟩ := ri_gas hd
   subst e; clear hd))

/-- A conditional goto whose target stays in the walk: both arms are kept. -/
macro "ubranchTo " h:ident c:ident : tactic => `(tactic|
  (have h' := ric_branchTo List.not_mem_nil rfl $h; clear $h
   rcases h' with ⟨$c, _, $h⟩ | ⟨$c, _, $h⟩))

/-- One comparison of a linear or binary-search dispatcher on a known selector. -/
macro "udisp " h:ident : tactic => `(tactic| first
  | (have h' := ric_cmp_gt $h; clear $h; obtain ⟨_, $h:ident⟩ := h'
     first
     | (rw [if_pos (by decide)] at $h:ident)
     | (rw [if_neg (by decide)] at $h:ident))
  | (have h' := ric_cmp_eq List.not_mem_nil rfl $h; clear $h; obtain ⟨_, $h:ident⟩ := h'
     first
     | (rw [if_pos (by decide)] at $h:ident)
     | (rw [if_neg (by decide)] at $h:ident))
  | (have h' := ric_dest $h; clear $h; obtain ⟨_, $h:ident⟩ := h'))

/-- solc 0.5's selector extraction. -/
theorem shr_selector_word (sevm : Sevm) :
    Sevm.dataWord sevm (Bytes.toB256 [0]) >>> (Bytes.toB256 [0xe0]).toNat = Blanc.Sevm.selector sevm :=
  rfl

theorem zero_of_iszero3 {a : B256} (h : B256.eqCheck (B256.eqCheck (B256.eqCheck a 0) 0) 0 ≠ 0) :
    a = 0 := by
  by_cases h0 : a = 0
  · exact h0
  · exfalso
    apply h
    simp only [B256.eqCheck, h0, ↓reduceIte]
    decide

theorem eq_of_iszero2 {x y : B256} (h : B256.eqCheck (B256.eqCheck x y) 0 = 0) : x = y := by
  by_contra hne
  simp only [B256.eqCheck, hne, ↓reduceIte] at h
  exact absurd h (by decide)

theorem ne_of_iszero3 {x y : B256}
    (h : B256.eqCheck (B256.eqCheck (B256.eqCheck x y) 0) 0 = 0) : x ≠ y := by
  rintro rfl
  simp only [B256.eqCheck, ↓reduceIte] at h
  exact absurd h (by decide)

theorem eq_of_iszero3 {x y : B256}
    (h : B256.eqCheck (B256.eqCheck (B256.eqCheck x y) 0) 0 ≠ 0) : x = y := by
  by_contra hne
  apply h
  simp only [B256.eqCheck, hne, ↓reduceIte]
  decide

theorem eq_zero_of_iszero_lit {y : B256}
    (c : B256.eqCheck (B256.eqCheck y (Bytes.toB256 [0])) 0 = 0) : y = 0 := by
  have h0 : Bytes.toB256 [0] = 0 := by decide
  rw [h0] at c
  by_contra hne
  simp only [B256.eqCheck, hne, ↓reduceIte] at c
  exact absurd c (by decide)

theorem keccak_u (μ : Mem) (key base : B256) :
    (((μ.write (Bytes.toB256 [0]).toNat key.toBytes).write (Bytes.toB256 [32] + Bytes.toB256 [0]).toNat
      base.toBytes).read (Bytes.toB256 [0]).toNat
        (Bytes.toB256 [32] + (Bytes.toB256 [32] + Bytes.toB256 [0])).toNat).1.keccak =
      mapSlot key base := by
  rw [show (Bytes.toB256 [32] + Bytes.toB256 [0]).toNat = (Bytes.toB256 [32]).toNat by decide,
    show (Bytes.toB256 [32] + (Bytes.toB256 [32] + Bytes.toB256 [0])).toNat =
      (Bytes.toB256 [64]).toNat by decide]
  exact keccak_scratch μ key base

/-- A packed read at byte offset `0`: the division by `0x100 ^ 0` is the word. -/
theorem div_bexp_zero (x : B256) :
    x / B256.bexp (Bytes.toB256 [1, 0]) (Bytes.toB256 [0]) = x := by
  rw [show B256.bexp (Bytes.toB256 [1, 0]) (Bytes.toB256 [0]) = 1 by decide]
  apply B256.toNat_inj
  rw [B256.toNat_div (by decide)]
  exact Nat.div_one _

theorem lit0 : Bytes.toB256 [0] = 0 := by decide

/-- A successful `STOP` halt keeps the base's storage. -/
theorem ric_stop_keeps {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b post : Devm}
    {S : List B256} {M : Mem} {G : Nat}
    (run : SFunc.RunCut fs sevm C (St b S M G) (.last .stop) (.done (.halted post))) :
    Devm.getStor post = Devm.getStor b := by
  cases run with
  | last hl =>
    simp only [Linst.Run, Linst.run, Except.ok.injEq] at hl
    subst hl
    rfl

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- Generalize the memory of the walk state of cut run `h`: a storage walk reads only the words its
hashes already left on the stack. -/
elab "umem " h:ident : tactic => withMainContext do
  let d ← getLocalDeclFromUserName h.getId
  let ty ← instantiateMVars d.type
  let some st := ty.find? (fun x => x.isAppOfArity ``Blanc.Lift.St 4)
    | throwError "umem: no walk state"
  let ms ← Term.exprToSyntax (st.getArg! 2)
  let mn := mkIdent (← mkFreshUserName `M)
  evalTactic (← `(tactic| generalize $ms = $mn:ident at $h:ident))

/-- solc's selector extraction, `div(calldataload(0), 2^224) & 0xffffffff`, is `Sevm.selector`'s
`>>> 224`. -/
theorem legacy_selector_word (sevm : Sevm) :
    (Bytes.toB256 [0xff, 0xff, 0xff, 0xff] &&& Sevm.dataWord sevm (Bytes.toB256 [0x00]) /
      Bytes.toB256 [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) = Blanc.Sevm.selector sevm := by
  unfold Blanc.Sevm.selector
  rw [show Bytes.toB256 [0x00] = (0 : B256) from by decide]
  generalize Sevm.dataWord sevm 0 = x
  have hP : (Bytes.toB256 [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00]).toNat = 2 ^ 224 := by decide
  have hm : (Bytes.toB256 [0xff, 0xff, 0xff, 0xff]).toNat = 2 ^ 32 - 1 := by decide
  have hP0 : Bytes.toB256 [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00] ≠ 0 := by decide
  apply B256.toNat_inj
  rw [B256.toNat_and, B256.toNat_div hP0, hP, hm, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
  rcases x with ⟨⟨x3, x2⟩, lo⟩
  have h1 : B256.shiftRight ((x3, x2), lo) 224 = ((0 : B128), B128.shiftRight (x3, x2) 96) := by
    simp only [B256.shiftRight, OfNat.ofNat_ne_zero, ↓reduceIte, Nat.reduceLT, Nat.reduceSub]; rfl
  have h2 : B128.shiftRight (x3, x2) 96 = ((0 : UInt64), x3 >>> (32 : UInt64)) := by
    simp only [B128.shiftRight]; rfl
  change B256.toNat ((x3, x2), lo) / 2 ^ 224 % 2 ^ 32 = B256.toNat (B256.shiftRight ((x3, x2), lo) 224)
  rw [h1, h2]
  have e1 : B256.toNat ((x3, x2), lo) = B128.toNat (x3, x2) * 2 ^ 128 + lo.toNat :=
    B256.toNat_eq _
  have e2 : B128.toNat (x3, x2) = x3.toNat * 2 ^ 64 + x2.toNat := B128.toNat_eq _
  have e3 : B256.toNat ((0 : B128), ((0 : UInt64), x3 >>> (32 : UInt64))) =
      B128.toNat (0 : B128) * 2 ^ 128 + B128.toNat ((0 : UInt64), x3 >>> (32 : UInt64)) :=
    B256.toNat_eq _
  have e4 : B128.toNat ((0 : UInt64), x3 >>> (32 : UInt64)) =
      (0 : UInt64).toNat * 2 ^ 64 + (x3 >>> (32 : UInt64)).toNat := B128.toNat_eq _
  have e5 : (x3 >>> (32 : UInt64)).toNat = x3.toNat / 2 ^ 32 := by
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
  have h3 := UInt64.toNat_lt x3
  have h2' := UInt64.toNat_lt x2
  have hlo := B128.toNat_lt (x := lo)
  simp only [B128.toNat_zero, UInt64.toNat_zero] at h3 h2' e3 e4
  omega

end Blanc.Lift
