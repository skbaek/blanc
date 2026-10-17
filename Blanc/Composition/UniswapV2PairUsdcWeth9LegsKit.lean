import Blanc.Lift.ExactWalkSolc
import Blanc.Lift.ExactWalkCallChild
import Blanc.Lift.ExactWalkOps
import Blanc.Lift.ExactWalkCutOps
import Blanc.Lift.WalkSteps
import Blanc.Lift.InvWalkStep

/-!
# A cost-accumulating forward walk kit (U9a)

The gas-exact walk kit of `Blanc/Lift/ExactWalk.lean` states each step backwards with a numeral
charge, so a walk's total charge must be written out beforehand.  The USDC runs (a proxy frame
forwarding to a 23 KB implementation) are too long for that.  Here the charge is left to
unification: a walk proves `SFunc.RunExact … (St b S M (G + c)) …` with `c` a metavariable, and
every step (`rk`) splits it as `k + c'`, the step's own charge `k` first.  The finished walk has
assigned `c`; stating the walk as a subtype `{c // …}` makes that charge a definition (its value is
the walk's assignment, so it reduces by `rfl`).

Also here: `FpM`, the solc free-pointer memory invariant with any pointer value (`FpMem` is its
`0x60` instance), and its forward steps for the solc 0.6 layout (pointer `0x80`, result word at
`0x80`).

Nothing here mentions a contract (hoist candidates for `Blanc/Lift/`).
-/

namespace Blanc.Composition.UsdcLive

open Jaune Blanc Blanc.Lift

section Acc

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  {f g : SFunc} {o : Outcome}

/-- Split an accumulated charge: the head step's charge `k`, the rest `c`. -/
theorem rk {k c : Nat} (h : SFunc.RunExact fs sevm (St b S M (G + c + k)) f o) :
    SFunc.RunExact fs sevm (St b S M (G + (k + c))) f o := by
  rwa [Nat.add_comm k c, ← Nat.add_assoc]

/-- The end of an accumulated walk: no charge left. -/
theorem rk0 (h : SFunc.RunExact fs sevm (St b S M G) f o) :
    SFunc.RunExact fs sevm (St b S M (G + 0)) f o := h

/-- A `JUMPI` that falls through, its flag shown zero. -/
theorem rx_branch_zero' {d w : B256} (hw : w = 0) (k : SFunc.RunExact fs sevm (St b S M G) f o) :
    SFunc.RunExact fs sevm (St b (d :: w :: S) M (G + 10)) (.branch f g) o := by
  subst hw; exact rx_branch_zero k

theorem rx_branchTo_zero' {d w : B256} {j : Nat} (hw : w = 0)
    (k : SFunc.RunExact fs sevm (St b S M G) f o) :
    SFunc.RunExact fs sevm (St b (d :: w :: S) M (G + 10)) (.branchTo f j) o := by
  subst hw; exact rx_branchTo_zero k

end Acc

/-! ## Comparison flags from arithmetic facts -/

theorem gtCheck_zero_of_toNat_le {x y : B256} (h : x.toNat ≤ y.toNat) : B256.gtCheck x y = 0 := by
  have : ¬ y < x := by rw [B256.lt_iff_toNat_lt_toNat]; omega
  simp only [B256.gtCheck, gt_iff_lt, this, ↓reduceIte]

theorem ltCheck_add_zero {x y : B256} (h : x.toNat + y.toNat < 2 ^ 256) :
    B256.ltCheck (x + y) y = 0 := by
  have e : (x + y).toNat = x.toNat + y.toNat := B256.toNat_add_eq_of_nof x y h
  have : ¬ x + y < y := by rw [B256.lt_iff_toNat_lt_toNat, e]; omega
  simp only [B256.ltCheck, this, ↓reduceIte]

/-! ## The free-pointer memory, any pointer -/

/-- A solc memory image: `n` bytes, word-aligned, at least the three scratch/pointer words, with the
free-memory pointer word (`0x40`) holding `fp`. -/
structure FpM (fp : B256) (n : Nat) (M : Mem) : Prop where
  size : M.size = n
  n32 : n % 32 = 0
  ge : 96 ≤ n
  wf : Mem.Wf M
  reads : ∃ bs, Mem.Reads M bs ∧ bs.sliceD 64 32 0 = fp.toBytes

theorem FpM.init (fp : B256) : FpM fp 96 (Mem.empty.write 64 fp.toBytes) := by
  refine ⟨?_, by decide, le_refl _, Mem.wf_empty.write _ _,
    ⟨_, Mem.reads_empty.write Mem.wf_empty 64 _, sliceD_word_same _ _ _⟩⟩
  rw [Mem.size_write_word_at]; rfl

theorem FpM.write {fp : B256} {n : Nat} {M : Mem} (h : FpM fp n M) (i : Nat) (v : B256)
    (hi : i + 32 ≤ n) (hd : i + 32 ≤ 64 ∨ 96 ≤ i) : FpM fp n (M.write i v.toBytes) := by
  obtain ⟨bs, hr, hf⟩ := h.reads
  refine ⟨Mem.size_write_word_of_le h.size hi, h.n32, h.ge, h.wf.write _ _,
    ⟨Bytes.writeAt bs i v.toBytes, hr.write h.wf i _, ?_⟩⟩
  rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by omega)]
  exact hf

/-- The first word written at `0x80` over the three-word image grows it to five words. -/
theorem FpM.write_out {fp : B256} {M : Mem} (h : FpM fp 96 M) (v : B256) :
    FpM fp 160 (M.write 128 v.toBytes) := by
  obtain ⟨bs, hr, hf⟩ := h.reads
  refine ⟨?_, by decide, by decide, h.wf.write _ _,
    ⟨Bytes.writeAt bs 128 v.toBytes, hr.write h.wf 128 _, ?_⟩⟩
  · rw [Mem.size_write_word_at, h.size]; decide
  · rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by omega)]
    exact hf

theorem FpM.fp {fp : B256} {n : Nat} {M : Mem} (h : FpM fp n M) :
    (M.read 64 32).1 = fp.toBytes := by
  obtain ⟨bs, hr, hf⟩ := h.reads
  rw [hr.read]; exact hf

theorem FpM.read_self {fp : B256} {n : Nat} {M : Mem} (h : FpM fp n M) {i sz : Nat}
    (hw : i + sz ≤ n) : (M.read i sz).2 = M :=
  Mem.read_snd_eq_self (by rw [h.size]; exact memExtSize_of_le h.n32 hw)

theorem FpM.readback {fp : B256} {n : Nat} {M : Mem} (h : FpM fp n M) (i : Nat) (v : B256) :
    ((M.write i v.toBytes).read i 32).1 = v.toBytes := by
  obtain ⟨bs, hr, -⟩ := h.reads
  rw [(hr.write h.wf i v.toBytes).read, sliceD_word_same]

theorem FpM.extCost {fp : B256} {n : Nat} {M : Mem} (h : FpM fp n M) {b : Devm} {S : List B256}
    {G i sz : Nat} (hw : i + sz ≤ n) : (St b S M G).extCost [⟨i, sz⟩] = 0 :=
  Devm.extCost_zero_of_le (by rw [h.size]; exact h.n32) (by rw [h.size]; exact hw)

section MemSteps

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  {f : SFunc} {o : Outcome} {n : Nat} {fp : B256}

/-- The prologue's `mstore(0x40, fp)` on the empty image. -/
theorem rx_mstoreInit {i v : B256} (hM : M = Mem.empty) (hi : i.toNat = 64)
    (k : SFunc.RunExact fs sevm (St b S (Mem.empty.write 64 v.toBytes) G) f o) :
    SFunc.RunExact fs sevm (St b (i :: v :: S) M (G + 12)) (.next (.reg .mstore) f) o := by
  subst hM
  refine rx_mstore (c := 12) ?_ (by rw [hi]) k
  rw [hi, St.extCost_eq (n := 0) rfl]; decide

/-- `CALLDATACOPY` with its charge read off the image size (no gas in the charge term). -/
theorem rx_calldatacopyK {di si sz : B256}
    (k : SFunc.RunExact fs sevm
      (St b S (M.write di.toNat (sevm.data.sliceD si.toNat sz.toNat 0)) G) f o) :
    SFunc.RunExact fs sevm (St b (di :: si :: sz :: S) M (G + (gVerylow + gasCopy * ceilDiv sz.toNat 32
      + (St b (di :: si :: sz :: S) M 0).extCost [⟨di.toNat, sz.toNat⟩])))
      (.next (.reg .calldatacopy) f) o :=
  rx_calldatacopy rfl rfl k

/-- `RETURNDATACOPY` with its charge read off the image size. -/
theorem rx_returndatacopyK {di ri sz : B256} (hb : ri.toNat + sz.toNat ≤ b.returnData.length)
    (k : SFunc.RunExact fs sevm
      (St b S (M.write di.toNat (b.returnData.sliceD ri.toNat sz.toNat 0)) G) f o) :
    SFunc.RunExact fs sevm (St b (di :: ri :: sz :: S) M (G + (gVerylow + gReturnDataCopy *
      ceilDiv sz.toNat 32 + (St b (di :: ri :: sz :: S) M 0).extCost [⟨di.toNat, sz.toNat⟩])))
      (.next (.reg .returndatacopy) f) o :=
  .next (Ninst.runCompiled_returndatacopy_of (devm := St b (di :: ri :: sz :: S) M _) (G := G) rfl rfl
    hb rfl rfl) k

/-- `MSTORE` of a word inside the image, off the pointer word. -/
theorem rx_mstoreP {i v : B256} {i0 : Nat} (hM : FpM fp n M) (hi : i.toNat = i0)
    (hin : i0 + 32 ≤ n) (hd : i0 + 32 ≤ 64 ∨ 96 ≤ i0)
    (k : SFunc.RunExact fs sevm (St b S (M.write i0 v.toBytes) G) f o) :
    SFunc.RunExact fs sevm (St b (i :: v :: S) M (G + 3)) (.next (.reg .mstore) f) o := by
  refine rx_mstore (c := 3) ?_ (by rw [hi]) (by rw [hi] at *; exact k)
  rw [hi, hM.extCost (by omega)]; rfl

/-- `MSTORE` of the first word at `0x80`: two words of expansion. -/
theorem rx_mstoreP80 {i v : B256} (hM : FpM fp 96 M) (hi : i.toNat = 128)
    (k : SFunc.RunExact fs sevm (St b S (M.write 128 v.toBytes) G) f o) :
    SFunc.RunExact fs sevm (St b (i :: v :: S) M (G + 9)) (.next (.reg .mstore) f) o := by
  refine rx_mstore (c := 9) ?_ (by rw [hi]) (by rw [hi] at *; exact k)
  rw [hi, St.extCost_eq hM.size]; decide

/-- `MLOAD` of the pointer word. -/
theorem rx_mloadP {i : B256} (hM : FpM fp n M) (hi : i.toNat = 64) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (fp :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (i :: S) M (G + 3)) (.next (.reg .mload) f) o := by
  refine rx_mload (c := 3) ?_ ?_ ?_ hroom k
  · rw [hi, hM.extCost (by have := hM.ge; omega)]; rfl
  · rw [hi, hM.fp, B256.toB256_toBytes]
  · rw [hi]; exact hM.read_self (by have := hM.ge; omega)

/-- `KECCAK256` of the two scratch words. -/
theorem rx_keccakP {M0 : Mem} {a c i sz : B256}
    (hM0 : M = (M0.write 0 a.toBytes).write 32 c.toBytes) (hM : FpM fp n M) (hi : i.toNat = 0)
    (hsz : sz.toNat = 64) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (mapSlot a c :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (i :: sz :: S) M (G + 42)) (.next (.reg .keccak256) f) o := by
  subst hM0
  refine rx_keccak (c := 42) ?_ ?_ ?_ hroom k
  · rw [hi, hsz, hM.extCost (by have := hM.ge; omega)]; decide
  · rw [hi, hsz, scratch_read]; rfl
  · rw [hi, hsz]; exact hM.read_self (by have := hM.ge; omega)

/-- `LOG3` of the word just written at `0x80`, inside a five-word image. -/
theorem rx_log3P {M0 : Mem} {v i sz t1 t2 t3 : B256} {n0 : Nat} (hstatic : sevm.isStatic = false)
    (hM1 : M = M0.write 128 v.toBytes) (hM0 : FpM fp n0 M0) (hM : FpM fp 160 M) (hi : i.toNat = 128)
    (hsz : sz.toNat = 32)
    (k : SFunc.RunExact fs sevm
      (St (b.addLog ⟨sevm.currentTarget, [t1, t2, t3], v.toBytes⟩) S M G) f o) :
    SFunc.RunExact fs sevm (St b (i :: sz :: t1 :: t2 :: t3 :: S) M (G + 1756))
      (.next (.reg (.log 3)) f) o := by
  subst hM1
  refine rx_log3 (c := 1756) hstatic ?_ ?_ ?_ k
  · rw [hi, hsz, hM.extCost (by omega)]; decide
  · rw [hi, hsz]; exact hM0.readback 128 v
  · rw [hi, hsz]; exact hM.read_self (by omega)

/-- `RETURN` of the word just written at `0x80`, inside a five-word image. -/
theorem rx_returnP {M1 : Mem} {v i sz : B256} {n0 : Nat} (hM1 : M = M1.write 128 v.toBytes)
    (hM0 : FpM fp n0 M1) (hM : FpM fp 160 M) (hi : i.toNat = 128) (hsz : sz.toNat = 32) :
    SFunc.RunExact fs sevm (St b (i :: sz :: S) M G) (.last .return_)
      (.halted (((St b S M G).memRead i.toNat sz.toNat).2.withOutput v.toBytes)) := by
  subst hM1
  refine rx_return ?_ ?_
  · rw [hi, hsz]; exact hM.extCost (by omega)
  · rw [hi, hsz]; exact hM0.readback 128 v

end MemSteps

/-! ## Calls to separately walked callees -/

section CallK

variable {fs : List SFunc} {sevm : Sevm} {b b' : Devm} {S S' : List B256} {M M' : Mem} {G : Nat}
  {f g : SFunc} {o : Outcome}

/-- An internal call to a callee whose walk is a lemma for every remaining gas `X`: the callee's
charge `c` joins the accumulated charge. -/
theorem rx_callK {d : B256} {j c c' : Nat} (hj : fs[j]? = some g)
    (hc : ∀ X, SFunc.RunExact fs sevm (St b S M (X + c)) g (.returned (St b' S' M' X)))
    (k : SFunc.RunExact fs sevm (St b' S' M' (G + c')) f o) :
    SFunc.RunExact fs sevm (St b (d :: S) M (G + (8 + (c + c')))) (.callNext j f) o := by
  have h := rx_callRet (d := d) hj (hc (G + c')) k
  rwa [show G + c' + c + 8 = G + (8 + (c + c')) by omega] at h

/-- `rx_callK` for a callee that needs `T` gas left after it returns (its `SSTORE` sentries). -/
theorem rx_callKT {d : B256} {j c c' T : Nat} (hj : fs[j]? = some g)
    (hc : ∀ X, T ≤ X → SFunc.RunExact fs sevm (St b S M (X + c)) g (.returned (St b' S' M' X)))
    (k : SFunc.RunExact fs sevm (St b' S' M' (G + c')) f o) (hT : T ≤ G + c') :
    SFunc.RunExact fs sevm (St b (d :: S) M (G + (8 + (c + c')))) (.callNext j f) o :=
  by
  have h := rx_callRet (d := d) hj (hc (G + c') hT) k
  rwa [show G + c' + c + 8 = G + (8 + (c + c')) by omega] at h

/-- A callee's return closing its walk: nothing is charged after it. -/
theorem rx_retK {d : B256} :
    SFunc.RunExact fs sevm (St b (d :: S) M (G + (8 + 0))) .ret (.returned (St b S M G)) :=
  rx_ret

end CallK

/-! ## The walk tactics -/

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- Unfold the tree of a `SFunc.RunExact` goal to its head constructor (a branch target or entry
tree is a constant). -/
elab "xunfold" : tactic => withMainContext do
  let tgt := (← instantiateMVars (← getMainTarget)).cleanupAnnotations
  match tgt.getAppFnArgs with
  | (``Blanc.Lift.SFunc.RunExact, #[fs, sevm, d, f, o]) =>
      let f' ← whnfD f
      unless f' == f do
        let g ← (← getMainGoal).replaceTargetDefEq
          (mkAppN (.const ``Blanc.Lift.SFunc.RunExact []) #[fs, sevm, d, f', o])
        replaceMainGoal [g]
  | _ => pure ()

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- A proof of `FpM fp n M` for a concrete image `M` built by word writes from a hypothesis or from
the prologue's pointer write, by recursion on the image. -/
private partial def fpProof (M : Expr) : TacticM Expr := do
  for d in (← getLCtx) do
    unless d.isImplementationDetail do
      let ty ← instantiateMVars d.type
      if ty.isAppOfArity ``FpM 3 then
        if ← withReducible (isDefEq ty.appArg! M) then return d.toExpr
  match (← whnfR M).getAppFnArgs with
  | (``Jaune.Mem.write, #[M0, i, bs]) =>
    let v := bs.appArg!
    if M0.isConstOf ``Jaune.Mem.empty then
      return ← mkAppM ``FpM.init #[v]
    let h0 ← fpProof M0
    let ty ← instantiateMVars (← inferType h0)
    let n := ty.appFn!.appArg!
    if (← isDefEq n (mkNatLit 96)) && (← isDefEq i (mkNatLit 128)) then
      return ← mkAppM ``FpM.write_out #[h0, v]
    let side (t : Expr) : TacticM Expr := do
      let g ← mkFreshExprMVar t
      let gs ← Tactic.run g.mvarId! (evalTactic (← `(tactic| first | decide | omega)))
      unless gs.isEmpty do throwError "fpProof: side goal {t}"
      instantiateMVars g
    let hi ← side (← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[i, mkNatLit 32], n])
    let hd ← side (mkOr (← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[i, mkNatLit 32], mkNatLit 64])
      (← mkAppM ``LE.le #[mkNatLit 96, i]))
    mkAppM ``FpM.write #[h0, i, v, hi, hd]
  | _ => throwError "fpProof: not a word-write image {M}"

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- The free-pointer invariant of a concrete image built from the prologue's pointer write by word
writes (or a hypothesis). -/
elab "xfp" : tactic => withMainContext do
  let tgt := (← instantiateMVars (← getMainTarget)).cleanupAnnotations
  unless tgt.isAppOfArity ``FpM 3 do throwError "xfp: not an FpM goal"
  let p ← fpProof tgt.appArg!
  closeMainGoalUsing `xfp fun ty _ => do
    unless ← isDefEq (← inferType p) ty do throwError "xfp: proof does not fit: {← inferType p} vs {ty}"
    return p

/-- Stack room on a concrete stack. -/
macro "xroom" : tactic =>
  `(tactic| (first | decide | (simp only [List.length_cons, List.length_nil]; omega) | omega))

open Jaune Blanc Blanc.Lift in
theorem getStorVal_afterSstore_self (sevm : Sevm) (d : Devm) (key value k : B256) :
    (afterSstore sevm d key value).getStorVal sevm.currentTarget k =
      ((Devm.getStor d sevm.currentTarget).set key value).get k := by
  show (Devm.getStor _ _).get _ = _
  rw [afterSstore_getStor_self]

/-- The storage-read normal form the walks' facts are stated in. -/
macro "xnorm" : tactic => `(tactic| simp (config := { failIfUnchanged := false }) only [Blanc.Lift.getStorVal_afterSload, Blanc.ff20_and_word,
  Blanc.Lift.word_ff20, Jaune.toAdr_toB256, getStorVal_afterSstore_self, Blanc.afterSload_getStor])

/-- A branch flag decided: by evaluation, a hypothesis, or a rewrite with the hypotheses. -/
macro "xbr" : tactic => `(tactic| (first
  | decide | with_reducible assumption
  | (simp only [*]; done) | (simp only [*]; decide)
  | (xnorm
     first | with_reducible assumption | (simp only [*]; done) | (simp only [*]; decide))))

open _root_.Lean _root_.Lean.Meta in
/-- The step tactic for a tree head (`none`: an internal call or a halting leaf, left to the
caller). -/
private def stepTac (f : Expr) : MetaM (Option (TSyntax `tactic)) := do
  match f.getAppFnArgs with
  | (``Blanc.Lift.SFunc.dest, _) => return some (← `(tactic| (apply rk; refine rx_dest ?_)))
  | (``Blanc.Lift.SFunc.jump, _) => return some (← `(tactic| (apply rk; refine rx_jump rfl ?_)))
  | (``Blanc.Lift.SFunc.ret, _) => return some (← `(tactic| exact rx_retK))
  | (``Blanc.Lift.SFunc.branch, _) => return some (← `(tactic| first
      | (apply rk; refine rx_branch_succ (by xbr) ?_)
      | (apply rk; refine rx_branch_zero' (by xbr) ?_)))
  | (``Blanc.Lift.SFunc.branchTo, _) => return some (← `(tactic| first
      | (apply rk; refine rx_branchTo_succ (by xbr) rfl ?_)
      | (apply rk; refine rx_branchTo_zero' (by xbr) ?_)))
  | (``Blanc.Lift.SFunc.next, #[n, _]) =>
    match n.getAppFnArgs with
    | (``Jaune.Ninst.push, _) => return some (← `(tactic| (apply rk; refine rx_push rfl (by xroom) ?_)))
    | (``Jaune.Ninst.reg, #[r]) =>
      match r.getAppFn.constName? with
      | some ``Jaune.Rinst.dup => return some (← `(tactic| (apply rk; refine rx_dup rfl (by xroom) ?_)))
      | some ``Jaune.Rinst.swap =>
          return some (← `(tactic| (apply rk; refine rx_swap rfl ?_; try dsimp only [List.set])))
      | some ``Jaune.Rinst.pop => return some (← `(tactic| (apply rk; refine rx_pop ?_)))
      | some ``Jaune.Rinst.add => return some (← `(tactic| (apply rk; refine rx_add (by xroom) ?_)))
      | some ``Jaune.Rinst.sub => return some (← `(tactic| (apply rk; refine rx_sub (by xroom) ?_)))
      | some ``Jaune.Rinst.and => return some (← `(tactic| (apply rk; refine rx_and rfl (by xroom) ?_)))
      | some ``Jaune.Rinst.or => return some (← `(tactic| (apply rk; refine rx_or rfl (by xroom) ?_)))
      | some ``Jaune.Rinst.eq => return some (← `(tactic| (apply rk; refine rx_eq rfl (by xroom) ?_)))
      | some ``Jaune.Rinst.lt => return some (← `(tactic| (apply rk; refine rx_lt rfl (by xroom) ?_)))
      | some ``Jaune.Rinst.gt => return some (← `(tactic| (apply rk; refine rx_gt rfl (by xroom) ?_)))
      | some ``Jaune.Rinst.iszero =>
          return some (← `(tactic| (apply rk; refine rx_iszero rfl (by xroom) ?_)))
      | some ``Jaune.Rinst.not => return some (← `(tactic| (apply rk; refine rx_not rfl (by xroom) ?_)))
      | some ``Jaune.Rinst.shr => return some (← `(tactic| (apply rk; refine rx_shr rfl (by xroom) ?_)))
      | some ``Jaune.Rinst.shl => return some (← `(tactic| (apply rk; refine rx_shl rfl (by xroom) ?_)))
      | some ``Jaune.Rinst.div => return some (← `(tactic| (apply rk; refine rx_div rfl (by xroom) ?_)))
      | some ``Jaune.Rinst.mul => return some (← `(tactic| (apply rk; refine rx_mul rfl (by xroom) ?_)))
      | some ``Jaune.Rinst.caller =>
          return some (← `(tactic| (apply rk; refine rx_caller (by xroom) ?_)))
      | some ``Jaune.Rinst.callvalue =>
          return some (← `(tactic| (apply rk; refine rx_callvalue (by xroom) ?_)))
      | some ``Jaune.Rinst.calldatasize =>
          return some (← `(tactic| (apply rk; refine rx_calldatasize (by xroom) ?_)))
      | some ``Jaune.Rinst.calldataload =>
          return some (← `(tactic| (apply rk; refine rx_calldataload (by xroom) ?_)))
      | some ``Jaune.Rinst.mstore => return some (← `(tactic| first
          | (apply rk; refine rx_mstoreInit (by with_reducible rfl) (by decide) ?_)
          | (apply rk; refine rx_mstoreP (i0 := 0) (by xfp) (by decide) (by first | decide | omega) (by decide) ?_)
          | (apply rk; refine rx_mstoreP (i0 := 32) (by xfp) (by decide) (by first | decide | omega) (by decide) ?_)
          | (apply rk; refine rx_mstoreP (i0 := 128) (by xfp) (by decide) (by first | decide | omega) (by decide) ?_)
          | (apply rk; refine rx_mstoreP80 (by xfp) (by decide) ?_)))
      | some ``Jaune.Rinst.mload =>
          return some (← `(tactic| (apply rk; refine rx_mloadP (by xfp) (by decide) (by xroom) ?_)))
      | some ``Jaune.Rinst.keccak256 => return some (← `(tactic|
          (apply rk; refine rx_keccakP (by with_reducible rfl) (by xfp) (by decide) (by decide)
            (by xroom) ?_)))
      | some ``Jaune.Rinst.gas => return some (← `(tactic| (apply rk; refine rx_gas (by xroom) ?_)))
      | some ``Jaune.Rinst.calldatacopy => return some (← `(tactic|
          (apply rk; refine rx_calldatacopyK ?_)))
      | some ``Jaune.Rinst.sload => return some (← `(tactic|
          (apply rk; refine rx_sload_sel (by with_reducible assumption) (by xroom) ?_)))
      | some ``Jaune.Rinst.sstore => return some (← `(tactic|
          (apply rk; refine rx_sstore (by with_reducible assumption) ?_ (by with_reducible assumption) ?_;
           rotate_left)))
      | some ``Jaune.Rinst.log => return some (← `(tactic|
          (apply rk; refine rx_log3P (by with_reducible assumption) (by with_reducible rfl) (by xfp)
            (by xfp) (by decide) (by decide) ?_)))
      | _ => return none
    | _ => return none
  | _ => return none

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- One accumulated forward step, chosen by the head of the tree: a straight-line instruction, a
jump destination, a jump, a branch whose flag `xbr` decides, or a callee's return.  An internal call
(`rx_callK` with the callee's walk lemma) and a halting leaf are left to the caller. -/
elab "xs" : tactic => withMainContext do
  evalTactic (← `(tactic| xunfold))
  let tgt := (← instantiateMVars (← getMainTarget)).cleanupAnnotations
  match tgt.getAppFnArgs with
  | (``Blanc.Lift.SFunc.RunExact, #[_, _, _, f, _]) =>
      match ← stepTac f with
      | some t => evalTactic t
      | none => throwError "xs: no step for this tree head"
  | _ => throwError "xs: not a walk goal {tgt}"

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic in
/-- `xs` until it fails, as a loop (a `repeat` nests one macro level per step). -/
elab "xrun" : tactic => do
  let mut i := 0
  while i < 100000 do
    let ok ← (do evalTactic (← `(tactic| xs)); pure true) <|> pure false
    if !ok then break
    i := i + 1

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic in
/-- At most `n` steps of `xs` (for locating a walk's stopping point). -/
elab "xrunN " n:num : tactic => do
  let mut i := 0
  while i < n.getNat do
    let ok ← (do evalTactic (← `(tactic| xs)); pure true) <|> pure false
    if !ok then break
    i := i + 1

end Blanc.Composition.UsdcLive

namespace Blanc.Composition.UsdcLive

/-- An internal call through a callee walk `w` (a subtype whose value is the callee's charge). -/
macro "xcall " w:term : tactic =>
  `(tactic| (refine' rx_callK (hj := by rfl) (hc := $w) ?_; rotate_left))

end Blanc.Composition.UsdcLive

namespace Blanc.Composition.UsdcLive

/-- `x.toNat ≤ y.toNat` from a hypothesis `gtCheck x y = 0` (after normalizing reads). -/
macro "xle" : tactic => `(tactic| (try xnorm) <;> first
  | with_reducible assumption
  | exact Blanc.Lift.toNat_le_of_gtCheck_eq_zero (by with_reducible assumption))

end Blanc.Composition.UsdcLive

namespace Blanc.Composition.UsdcLive

/-- `xcall` for a callee with a gas threshold: the threshold goal is left last. -/
macro "xcallT " w:term : tactic =>
  `(tactic| (refine' rx_callKT (hj := by rfl) (hc := $w) ?_ ?_; rotate_left))

end Blanc.Composition.UsdcLive

namespace Blanc.Composition.UsdcLive

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- The callee walk `w sevm b e₁ … e_k S M` instantiated at the goal's state (base `b`, the `k`
words under the return address, the rest `S`, memory `M`), as syntax. -/
private def calleeAt (w : Ident) (k : Nat) : TacticM (TSyntax `term) := do
  let tgt := (← instantiateMVars (← getMainTarget)).cleanupAnnotations
  let args := tgt.getAppArgs
  unless args.size == 5 do throwError "xcallM: not a walk goal"
  let sevm := args[1]!
  let st := args[2]!
  let stArgs := st.getAppArgs
  unless st.isAppOfArity ``Blanc.Lift.St 4 do throwError "xcallM: state is not `St`"
  let b := stArgs[0]!
  let M := stArgs[2]!
  -- drop the return address pushed by the call
  let mut l := stArgs[1]!.getAppArgs[2]!
  let mut es : Array Expr := #[]
  for _ in [0:k] do
    es := es.push l.getAppArgs[1]!
    l := l.getAppArgs[2]!
  let mut stx ← `($w $(← Term.exprToSyntax sevm) $(← Term.exprToSyntax b))
  for e in es do
    stx ← `($stx $(← Term.exprToSyntax e))
  stx ← `($stx $(← Term.exprToSyntax l) $(← Term.exprToSyntax M))
  return stx

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- An internal call to callee walk `w` taking `k` words and the extra arguments `as` (after the
memory; `_` for an image size), then the property's hypotheses `hs`. -/
elab "xcallM " w:ident k:num " [" as:term:max* "] " hs:(ppSpace colGt term:max)* : tactic => withMainContext do
  let c ← calleeAt w k.getNat
  let mut t ← `($c $as*)
  t ← `(($t).2 $hs*)
  evalTactic (← `(tactic| (refine' rx_callK (hj := by rfl) (hc := $t) ?_; rotate_left)))

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- `xcallM` for a callee with a gas threshold. -/
elab "xcallMT " w:ident k:num " [" as:term:max* "] " hs:(ppSpace colGt term:max)* : tactic => withMainContext do
  let c ← calleeAt w k.getNat
  let mut t ← `($c $as*)
  t ← `(($t).2 $hs*)
  evalTactic (← `(tactic| (refine' rx_callKT (hj := by rfl) (hc := $t) ?_ ?_; rotate_left)))

end Blanc.Composition.UsdcLive

namespace Blanc.Composition.UsdcLive

open Jaune Blanc Blanc.Lift

/-- A `DELEGATECALL` to a non-precompile code address whose entered child halts cleanly resumes in
`callChildPost`: the delegate sibling of `Ninst.runCompiled_call_zero_child` (no value moves). -/
lemma Ninst.runCompiled_delegatecall_child {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat} {cpost : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_stk : devm.stack = gw :: cw :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft) (h_depth : sevm.depth ≠ 0)
    (h_nonprecompile : sevm.benvStat.rules.isPrecomp dadr = false)
    (h_room : s.length < 1024)
    (h_exec : exec (initEvm (delegatecallSpawnMsg sevm
      (callSpawnParent d1 (mcc + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat)
      mcs dadr iiw.toNat isw.toNat code dp)) = .ok cpost)
    (h_error : cpost.error = none) :
    Ninst.RunCompiled sevm devm (.exec .delegatecall)
      (callChildPost (callSpawnParent d1 (mcc + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat)
        cpost oiw.toNat osw.toNat) := by
  let p := callSpawnParent d1 (mcc + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat
  let msg := delegatecallSpawnMsg sevm p mcs dadr iiw.toNat isw.toNat code dp
  have hbt : msg.benvAfterTransfer = .ok msg.benv := by
    unfold Msg.benvAfterTransfer
    simp only [msg, delegatecallSpawnMsg, callMsg, Bool.false_eq_true, false_and, ↓reduceIte]
  have henter : (Frame.ofCall msg).enter = .run (initEvm (msg.withBenv msg.benv)) := by
    apply Frame.enter_run_of_nonprecompile hbt
    · rfl
    · change sevm.benvStat.rules.isPrecomp dadr = false
      exact h_nonprecompile
  have hexec : exec (initEvm (msg.withBenv msg.benv)) = .ok cpost := by
    simpa only [msg, p, delegatecallSpawnMsg, callMsg, Msg.withBenv] using h_exec
  have hsettle : (Frame.ofCall msg).settle (exec (initEvm (msg.withBenv msg.benv))) = .ok cpost := by
    rw [hexec, Frame.settle_eq_settleMsg_handleErrorWith, executeCode.handleErrorWith_ok]
    simp only [Frame.ofCall, Frame.settleMsg, processMessage.settle, h_error,
      Option.isSome_none, Bool.false_eq_true, ite_false, bind, Except.bind]
  have hdi := accessDelegation_inv h_del
  have hpstack : p.stack.length < 1024 := by
    change d1.stack.length < 1024
    rw [hdi.1]
    exact h_room
  have hres : Resume.run (.call p oiw.toNat osw.toNat)
      ((Frame.ofCall msg).settle (exec (initEvm (msg.withBenv msg.benv)))) =
        .ok (callChildPost p cpost oiw.toNat osw.toNat) := by
    rw [hsettle, Resume.run_call_ok (by rw [h_error]; rfl) hpstack]
    rfl
  exact Ninst.runCompiled_delegatecall hfork h_stk h_ext h_del h_acc h_split h_gas h_depth
    henter hres

end Blanc.Composition.UsdcLive
