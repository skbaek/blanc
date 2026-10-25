import Blanc.Lift.ReachWalkSstore
import Blanc.Lift.CursorTreeNinst
import Blanc.Lift.SolcStoragePayload
import Blanc.Lift.SolcStorageClear
import Blanc.Lift.SolcStorageReturn
import Blanc.Lift.WalkSteps
import Blanc.Lift.VyperCallee
import Blanc.Lift.SelectorRoute
import Blanc.Lift.InvWalkStep

/-!
# Storage loops on a prefix reach to an `SSTORE`

The reach twins of the solc storage-string loop templates
(`Blanc/Lift/SolcStoragePayload.lean`, `Blanc/Lift/SolcStorageClear.lean`): a reach
that enters a loop head and stops at an `SSTORE` either stops at the loop's own store,
whose key or value the loop invariant names, or leaves the loop through its exit with the
invariant at the exit. The frame may end in any outcome.

* `stepR`, `ri_stepR` and the tactics `rsx`, `rsd`, `rsw`: one straight-line step of a
  reach to an `SSTORE` over the walk state `St b S M G` (no fork premise: storage
  instructions are stepped with `ri_sload_any`/`ri_sstore_any`).
* `reach_loop_measure`: a loop pass that either concludes or re-enters the head with a
  smaller measure concludes.
* `bodyR`, `headB`, `headJ`: the payload copy loop over a read instruction (`MLOAD` or
  `CALLDATALOAD`), with its exit inline (`branch`) or through a goto (`branchTo`);
  `SolcStoragePayload.head` is `headB` over `MLOAD`. `payloadB_reach`, `payloadJ_reach`:
  a store of the loop writes `base + j` for `j < count fin p`.
* `clear_reach`, `legacyClear_reach`: a store of either clearing layout writes zero, and
  neither returns into an empty stack.

Contract-neutral.
-/

namespace Blanc.Lift

open Jaune Blanc

-- Structural equality of synthetic trees, so a shape equation over a whole certificate entry
-- is a kernel decision.
deriving instance DecidableEq for SFunc

/-! ## One straight-line step -/

/-- The successor stack and memory of a straight-line, storage-free instruction over the
walk state; the base is unchanged. -/
def stepR (sevm : Sevm) : Ninst → List B256 → Mem → Option (List B256 × Mem)
  | .push xs _, S, M => some (xs.toB256 :: S, M)
  | .reg (.dup n), S, M => S[n.val]?.map fun w => (w :: S, M)
  | .reg (.swap n), S, M => (Jaune.List.swap S n.val).map fun S' => (S', M)
  | .reg .pop, _ :: S, M => some (S, M)
  | .reg .and, x :: y :: S, M => some ((x &&& y) :: S, M)
  | .reg .or, x :: y :: S, M => some ((x ||| y) :: S, M)
  | .reg .xor, x :: y :: S, M => some ((x ^^^ y) :: S, M)
  | .reg .add, x :: y :: S, M => some ((x + y) :: S, M)
  | .reg .sub, x :: y :: S, M => some ((x - y) :: S, M)
  | .reg .mul, x :: y :: S, M => some ((x * y) :: S, M)
  | .reg .div, x :: y :: S, M => some ((x / y) :: S, M)
  | .reg .mod, x :: y :: S, M => some ((x % y) :: S, M)
  | .reg .exp, x :: y :: S, M => some (B256.bexp x y :: S, M)
  | .reg .eq, x :: y :: S, M => some (B256.eqCheck x y :: S, M)
  | .reg .lt, x :: y :: S, M => some (B256.ltCheck x y :: S, M)
  | .reg .gt, x :: y :: S, M => some (B256.gtCheck x y :: S, M)
  | .reg .shr, x :: y :: S, M => some ((y >>> x.toNat) :: S, M)
  | .reg .shl, x :: y :: S, M => some ((y <<< x.toNat) :: S, M)
  | .reg .iszero, x :: S, M => some (B256.eqCheck x 0 :: S, M)
  | .reg .not, x :: S, M => some ((~~~ x) :: S, M)
  | .reg .caller, S, M => some (sevm.caller.toB256 :: S, M)
  | .reg .callvalue, S, M => some (sevm.value :: S, M)
  | .reg .address, S, M => some (sevm.currentTarget.toB256 :: S, M)
  | .reg .calldatasize, S, M => some (sevm.data.length.toB256 :: S, M)
  | .reg .calldataload, x :: S, M => some (Sevm.dataWord sevm x :: S, M)
  | .reg .mload, i :: S, M =>
      some (Bytes.toB256 (M.read i.toNat 32).1 :: S, (M.read i.toNat 32).2)
  | .reg .mstore, i :: v :: S, M => some (S, M.write i.toNat v.toBytes)
  | .reg .keccak256, i :: sz :: S, M =>
      some ((M.read i.toNat sz.toNat).1.keccak :: S, (M.read i.toNat sz.toNat).2)
  | .reg .calldatacopy, di :: si :: sz :: S, M =>
      some (S, M.write di.toNat (sevm.data.sliceD si.toNat sz.toNat 0))
  | .reg .codecopy, di :: ci :: sz :: S, M =>
      some (S, M.write di.toNat (sevm.code.sliceD ci.toNat sz.toNat (Linst.toUInt8 .stop)))
  | _, _, _ => none

theorem ri_stepR {sevm : Sevm} {b d : Devm} {S S' : List B256} {M M' : Mem} {G : Nat}
    {n : Ninst} (h : Ninst.Run sevm (St b S M G) n d) (hs : stepR sevm n S M = some (S', M')) :
    ∃ G', d = St b S' M' G' := by
  unfold stepR at hs
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
  · cases hs; exact ri_xor h
  · cases hs; exact ri_add h
  · cases hs; exact ri_sub h
  · cases hs; exact ri_mul h
  · cases hs; exact ri_div h
  · cases hs; exact ri_mod h
  · cases hs; exact ri_exp h
  · cases hs; exact ri_eq h
  · cases hs; exact ri_lt h
  · cases hs; exact ri_gt h
  · cases hs; exact ri_shr h
  · cases hs; exact ri_shl h
  · cases hs; exact ri_iszero h
  · cases hs; exact ri_not h
  · cases hs; exact ri_caller h
  · cases hs; exact ri_callvalue h
  · cases hs; exact ri_address h
  · cases hs; exact ri_calldatasize h
  · cases hs; exact ri_calldataload h
  · cases hs; exact ri_mload h
  · cases hs; exact ri_mstore h
  · cases hs; exact ri_keccak h
  · cases hs; exact ri_calldatacopy h
  · cases hs; exact ri_codecopy h
  · cases hs

set_option hygiene false in
/-- One straight-line step of `run : Reach … ⟨St b S M G, .next n f, K⟩ T` toward
`hT : AtSstore T`, with `erase` turning the step relation into `Ninst.Run`. -/
macro "rsx" : tactic => `(tactic| (
  have hnext := rs_next run hT
  clear run
  obtain ⟨_, hstep, run⟩ := hnext
  obtain ⟨_, e⟩ := ri_stepR (erase hstep) rfl
  try dsimp only [List.set, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at e
  subst e
  clear hstep))

set_option hygiene false in
/-- A `JUMPDEST` of a reach to an `SSTORE` over the walk state. -/
macro "rsd" : tactic => `(tactic| (
  have hnext := rs_dest run hT
  clear run
  obtain ⟨_, run⟩ := hnext))

set_option hygiene false in
/-- `rsd` or `rsx`. -/
macro "rsw" : tactic => `(tactic| first | rsd | rsx)

set_option hygiene false in
/-- One step of a reach to an `SSTORE` taken without inverting it: the next machine is
unnamed and re-read as its own walk state (`St.self'`). -/
macro "rsk" : tactic => `(tactic| (
  have hnext := rs_next run hT
  clear run
  obtain ⟨d', -, run⟩ := hnext
  rw [St.self' d'] at run))

set_option hygiene false in
/-- An `SLOAD` of a reach to an `SSTORE`: the loaded word is unnamed. -/
macro "rsld" : tactic => `(tactic| (
  have hnext := rs_next run hT
  clear run
  obtain ⟨_, hstep, run⟩ := hnext
  obtain ⟨_, _, _, e⟩ := SolcStorageReturn.ri_sload_any (erase hstep)
  subst e
  clear hstep))

set_option hygiene false in
/-- `rsd`, `rsx` or `rsld`: any step `stepR` or `SLOAD` names. -/
macro "rsa" : tactic => `(tactic| first | rsd | rsx | rsld)

/-! ## Calls and returns over the walk state -/

section CallRet

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}
  {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}

/-- A `.ret` on a reach to an `SSTORE` pops the return tag into the innermost pending
continuation. -/
theorem rs_ret {t : B256} (run : Reach P fs sevm ⟨St b (t :: S) M G, .ret, K⟩ T)
    (hT : AtSstore T) :
    ∃ f K' b' M' G', K = f :: K' ∧ Reach P fs sevm ⟨St b' S M' G', f, K'⟩ T := by
  rcases Relation.ReflTransGen.cases_head run with rfl | ⟨c, step, rest⟩
  · obtain ⟨f', hx⟩ := hT
    cases hx
  · cases step with
    | ret t' pop =>
      obtain ⟨-, e⟩ := St.of_pop1 pop
      exact ⟨_, _, _, _, _, rfl, e ▸ rest⟩

/-- `rs_ret`, keeping the memory. -/
theorem rs_retM {t : B256} (run : Reach P fs sevm ⟨St b (t :: S) M G, .ret, K⟩ T)
    (hT : AtSstore T) :
    ∃ f K' b' G', K = f :: K' ∧ Reach P fs sevm ⟨St b' S M G', f, K'⟩ T := by
  rcases Relation.ReflTransGen.cases_head run with rfl | ⟨c, step, rest⟩
  · obtain ⟨f', hx⟩ := hT
    cases hx
  · cases step with
    | ret t' pop =>
      obtain ⟨-, e⟩ := St.of_pop1 pop
      exact ⟨_, _, _, _, rfl, e ▸ rest⟩

/-- A `callNext` on a reach to an `SSTORE` enters the callee with its continuation pending. -/
theorem rs_callIn {k : Nat} {f : SFunc} {t : B256}
    (run : Reach P fs sevm ⟨St b (t :: S) M G, .callNext k f, K⟩ T) (hT : AtSstore T) :
    ∃ g G', fs[k]? = some g ∧ Reach P fs sevm ⟨St b S M G', g, f :: K⟩ T := by
  rcases Relation.ReflTransGen.cases_head run with rfl | ⟨c, step, rest⟩
  · obtain ⟨f', hx⟩ := hT
    cases hx
  · cases step with
    | call t' hk pop =>
      obtain ⟨-, e⟩ := St.of_pop1 pop
      exact ⟨_, _, hk, e ▸ rest⟩

/-- A `callNext` into an `SSTORE`-free callee on a reach to an `SSTORE`, from any machine:
the callee returns and the reach continues from the continuation. -/
theorem rs_callOverAny {E : List Nat} (hE : SstoreFreeSet fs E = true) {k : Nat} {f g : SFunc}
    {d : Devm} (hk : fs[k]? = some g) (hkE : k ∈ E)
    (run : Reach P fs sevm ⟨d, .callNext k f, K⟩ T) (hT : AtSstore T) :
    ∃ D, Reach P fs sevm ⟨D, f, K⟩ T := by
  obtain ⟨t, g', d', hk', pop, inside | ⟨D, -, rest⟩⟩ := Reach.callS run hT
  · rw [hk] at hk'
    cases hk'
    obtain ⟨T', r', rfl⟩ := inside
    exact (Reach.false_of_sstoreFree hE r' hT (SstoreFreeSet.lookup hE hkE hk)
      (fun _ h => by cases h)).elim
  · exact ⟨D, rest⟩

end CallRet

/-! ## A solc dispatcher on a reach to an `SSTORE` -/

section Dispatch

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}
  {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf} {σ : B256}

theorem rs_cmp_gt (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {c0 c1 c2 c3 d0 d1 : UInt8} {l1 l2} {f g : SFunc}
    (run : Reach P fs sevm ⟨St b (σ :: S) M G,
      .next (.reg (.dup 0)) (.next (.push [c0, c1, c2, c3] l1)
      (.next (.reg .gt) (.next (.push [d0, d1] l2) (.branch f g)))), K⟩ T)
    (hT : AtSstore T) :
    ∃ G', Reach P fs sevm ⟨St b (σ :: S) M G',
      if B256.gtCheck (Bytes.toB256 [c0, c1, c2, c3]) σ = 0 then f else g, K⟩ T := by
  iterate 4 rsx
  rcases rs_branch run hT with ⟨zero, G', h⟩ | ⟨nonzero, G', h⟩
  · rw [ite_eq_left zero]
    exact ⟨G', h⟩
  · rw [ite_eq_right nonzero]
    exact ⟨G', h⟩

theorem rs_cmp_eq_either (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {c0 c1 c2 c3 d0 d1 : UInt8} {l1 l2} {f : SFunc} {j : Nat}
    (run : Reach P fs sevm ⟨St b (σ :: S) M G,
      .next (.reg (.dup 0)) (.next (.push [c0, c1, c2, c3] l1)
      (.next (.reg .eq) (.next (.push [d0, d1] l2) (.branchTo f j)))), K⟩ T)
    (hT : AtSstore T) :
    (B256.eqCheck (Bytes.toB256 [c0, c1, c2, c3]) σ = 0 ∧
        ∃ G', Reach P fs sevm ⟨St b (σ :: S) M G', f, K⟩ T) ∨
      (B256.eqCheck (Bytes.toB256 [c0, c1, c2, c3]) σ ≠ 0 ∧
        ∃ g G', fs[j]? = some g ∧ Reach P fs sevm ⟨St b (σ :: S) M G', g, K⟩ T) := by
  iterate 4 rsx
  rcases rs_branchTo run hT with ⟨zero, G', h⟩ | ⟨nonzero, g, G', hg, h⟩
  · exact .inl ⟨zero, G', h⟩
  · exact .inr ⟨nonzero, g, G', hg, h⟩

/-- **A reach to an `SSTORE` at the goto of the dispatcher's walk.** The selector word is the
constant compared, and the reach continues from the goto's entry. -/
theorem Reach.selWalk_inlS (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {c : B256}
    {f : SFunc} {j : Nat} (hw : f.selWalk σ = .inl (c, j))
    (run : Reach P fs sevm ⟨St b (σ :: S) M G, f, K⟩ T) (hT : AtSstore T) :
    σ = c ∧ ∃ g G', fs[j]? = some g ∧ Reach P fs sevm ⟨St b (σ :: S) M G', g, K⟩ T := by
  fun_induction SFunc.selWalk σ f generalizing G with
  | case1 f ih =>
      obtain ⟨G', r⟩ := rs_dest run hT
      exact ih hw r
  | case2 c0 c1 c2 c3 _ _ _ _ f g h ih =>
      obtain ⟨G', r⟩ := rs_cmp_gt erase run hT
      rw [ite_eq_left h] at r
      exact ih hw r
  | case3 c0 c1 c2 c3 _ _ _ _ f g h ih =>
      obtain ⟨G', r⟩ := rs_cmp_gt erase run hT
      rw [ite_eq_right h] at r
      exact ih hw r
  | case4 c0 c1 c2 c3 _ _ _ _ f j h ih =>
      rcases rs_cmp_eq_either erase run hT with ⟨-, G', r⟩ | ⟨ne, -⟩
      · exact ih hw r
      · exact absurd h ne
  | case5 c0 c1 c2 c3 _ _ _ _ f j h =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Sum.inl.inj hw)
      rcases rs_cmp_eq_either erase run hT with ⟨zero, -⟩ | ⟨ne, r⟩
      · exact absurd zero h
      · exact ⟨(eq_of_eqCheck_ne ne).symm, r⟩
  | case6 => cases hw

end Dispatch

/-! ## Scratch hashes -/

/-- solc's mapping slot from its two scratch words, with the offsets as any closed words of the
right value: `mstore(0, key); mstore(32, base); keccak256(0, 64)`. -/
theorem mapSlot_scratch (μ : Mem) (key base : B256) {o0 o1 o2 n : B256} (h0 : o0.toNat = 0)
    (h1 : o1.toNat = 32) (h2 : o2.toNat = 0) (hn : n.toNat = 64) :
    (((μ.write o0.toNat key.toBytes).write o1.toNat base.toBytes).read o2.toNat n.toNat).1.keccak =
      mapSlot key base := by
  have h := keccak_scratch μ key base
  rw [show (Bytes.toB256 [0]).toNat = 0 by decide, show (Bytes.toB256 [32]).toNat = 32 by decide,
    show (Bytes.toB256 [64]).toNat = 64 by decide] at h
  rw [h0, h1, h2, hn]
  exact h

/-! ## Loops by a measure -/

section Loop

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}

/-- **A loop by a measure.** If every pass from the head under `I` either concludes `Q` or
re-enters the head under `I` with a smaller measure, every reach from the head under `I`
concludes `Q`. -/
theorem reach_loop_measure {head : SFunc} {K : List SFunc} {T : Conf} {Q : Prop}
    (I : Devm → Prop) (μ : Devm → Nat)
    (pass : ∀ d, I d → Reach P fs sevm ⟨d, head, K⟩ T →
      Q ∨ ∃ d', I d' ∧ μ d' < μ d ∧ Reach P fs sevm ⟨d', head, K⟩ T) :
    ∀ d, I d → Reach P fs sevm ⟨d, head, K⟩ T → Q := by
  intro d
  induction h : μ d using Nat.strong_induction_on generalizing d with
  | _ n ih =>
    intro hI run
    rcases pass d hI run with q | ⟨d', hI', lt, run'⟩
    · exact q
    · exact ih (μ d') (h ▸ lt) d' rfl hI' run'

/-- **A loop by a bounded index.** If every pass from the head under `I i` either concludes
`Q` or re-enters the head under `I (i + 1)`, and `I i` bounds `i` by `N`, every reach from
the head under some `I i` concludes `Q`. -/
theorem reach_loop_index {head : SFunc} {K : List SFunc} {T : Conf} {Q : Prop}
    (I : Nat → Devm → Prop) (N : Nat) (hN : ∀ i d, I i d → i ≤ N)
    (pass : ∀ i d, I i d → Reach P fs sevm ⟨d, head, K⟩ T →
      Q ∨ ∃ d', I (i + 1) d' ∧ Reach P fs sevm ⟨d', head, K⟩ T) :
    ∀ i d, I i d → Reach P fs sevm ⟨d, head, K⟩ T → Q := by
  intro i
  induction h : N - i using Nat.strong_induction_on generalizing i with
  | _ n ih =>
    intro d hI run
    rcases pass i d hI run with q | ⟨d', hI', run'⟩
    · exact q
    · have hle := hN (i + 1) d' hI'
      exact ih (N - (i + 1)) (by omega) (i + 1) rfl d' hI' run'

end Loop

/-! ## Memory potential along a reach -/

/-- **A reach from a state of bounded potential records it at every step.** -/
theorem Reach.withPot {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {fs : List SFunc} {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none)
    {a T : Conf} (h : Reach P fs sevm a T) (pot : FreePtr.Pot a.d) :
    Reach (FreePtr.PotStep P) fs sevm a T ∧ FreePtr.Pot T.d := by
  induction h with
  | refl => exact ⟨.refl, pot⟩
  | tail _ step ih =>
    obtain ⟨r, p⟩ := ih
    cases step with
    | next hp =>
      have p' := FreePtr.Pot.step hsg (hP hp) p
      exact ⟨.tail r (.next ⟨hp, p, p'⟩), p'⟩
    | dest hb => exact ⟨.tail r (.dest hb), FreePtr.Pot.burn hb p⟩
    | zero t h => exact ⟨.tail r (.zero t h), FreePtr.Pot.popBurn h p⟩
    | succ t w hw h => exact ⟨.tail r (.succ t w hw h), FreePtr.Pot.popBurn h p⟩
    | toZero t h => exact ⟨.tail r (.toZero t h), FreePtr.Pot.popBurn h p⟩
    | toSucc t w hw hk h => exact ⟨.tail r (.toSucc t w hw hk h), FreePtr.Pot.popBurn h p⟩
    | jump t hk h => exact ⟨.tail r (.jump t hk h), FreePtr.Pot.popBurn h p⟩
    | call t hk h => exact ⟨.tail r (.call t hk h), FreePtr.Pot.popBurn h p⟩
    | ret t h => exact ⟨.tail r (.ret t h), FreePtr.Pot.popBurn h p⟩
    | pcAt hp hr =>
      have p' := FreePtr.Pot.step hsg (hP hp) p
      exact ⟨.tail r (.pcAt ⟨hp, p, p'⟩ hr), p'⟩

/-- **A raw `SSTORE` node of a certified frame, as a reach under the potential.** A node `N`
under a frame `R` entered at pc `0` of certified bytes, without state gas, with empty stack and
memory and gas below `2 ^ 256`, at an `SSTORE` is the end of a `PotStep (StepIn R)` reach from
the entry tree over the entry walk state, at an `SSTORE`, holding `N`'s machine. -/
theorem Reach.sstoreNode_pot {code : ByteArray} {c : Cert} (hc : Cert.check code c = true)
    {R N : Exec.Deriv} (hpc : R.pc = 0) (hcode : R.sevm.code = code)
    (hsg : R.sevm.benvStat.rules.stateGas = none) (stack : R.devm.stack = [])
    (memory : R.devm.memory = Mem.empty) (gas : R.devm.gasMeasure < 2 ^ 256)
    (chain : Exec.Deriv.ParentPrefix R N) (hat : Ninst.At N.sevm.code N.pc (.reg .sstore)) :
    ∃ T, Reach (FreePtr.PotStep (StepIn R)) c.prog R.sevm
      ⟨St R.devm [] Mem.empty R.devm.gasLeft, (Cursor.start c).f, []⟩ T ∧ AtSstore T ∧
      T.d = N.devm := by
  obtain ⟨κ, reach, ok⟩ := reach_of_parentPrefix_noStateGas hc hpc hcode hsg chain
  obtain ⟨g, hf, -⟩ := ok.tree_of_sstore hat
  have pot : FreePtr.Pot R.devm := by
    unfold FreePtr.Pot
    rw [memory]
    exact gas
  obtain ⟨r, -⟩ := Reach.withPot (fun h => StepIn.toRun h) hsg reach pot
  have hK : (Cursor.start c).K = [] := by
    unfold Cursor.start
    split <;> rfl
  have e : (Cursor.start c).conf R.devm =
      ⟨St R.devm [] Mem.empty R.devm.gasLeft, (Cursor.start c).f, []⟩ := by
    rw [← stack, ← memory, ← St.self' R.devm]
    simp only [Cursor.conf, hK, List.map_nil]
  rw [e] at r
  exact ⟨_, r, ⟨g, hf⟩, rfl⟩

/-! ## The payload copy loop -/

namespace ReachPayload

open SolcStoragePayload (count Inv)

/-- The copy iteration over the read instruction `rd`: read the cursor's word, store it at
the key, advance cursor and key, jump back to entry `k`. -/
def bodyR (rd : Ninst) (back : Bytes) (bound : back.length ≤ 32) (k : Nat) : SFunc :=
  .next (.reg (.dup 2)) (.next rd
    (.next (.reg (.dup 2)) (.next (.reg .sstore)
      (.next (.reg (.swap 1)) (.next (.push [0x20] (by decide))
        (.next (.reg .add) (.next (.reg (.swap 1))
          (.next (.reg (.swap 0)) (.next (.push [0x01] (by decide))
            (.next (.reg .add) (.next (.reg (.swap 0))
              (.next (.push back bound) (.jump k)))))))))))))

/-- The loop head with its exit inline. -/
def headB (rd : Ninst) (back exit : Bytes) (backBound : back.length ≤ 32)
    (exitBound : exit.length ≤ 32) (k : Nat) (tail : SFunc) : SFunc :=
  .dest (.next (.reg (.dup 2)) (.next (.reg (.dup 1)) (.next (.reg .gt)
    (.next (.reg .iszero) (.next (.push exit exitBound)
      (.branch (bodyR rd back backBound k) tail))))))

/-- The loop head with its exit through a goto to entry `j`. -/
def headJ (rd : Ninst) (back exit : Bytes) (backBound : back.length ≤ 32)
    (exitBound : exit.length ≤ 32) (k j : Nat) : SFunc :=
  .dest (.next (.reg (.dup 2)) (.next (.reg (.dup 1)) (.next (.reg .gt)
    (.next (.reg .iszero) (.next (.push exit exitBound)
      (.branchTo (bodyR rd back backBound k) j))))))

theorem head_eq_headB {back exit : Bytes} {bb : back.length ≤ 32} {eb : exit.length ≤ 32}
    {k : Nat} {tail : SFunc} :
    SolcStoragePayload.head back exit bb eb k tail = headB (.reg .mload) back exit bb eb k tail :=
  rfl

theorem key_succ (base0 : B256) {i : Nat} (hi : i + 1 < 2 ^ 256) :
    Bytes.toB256 [0x01] + (base0 + i.toB256) = base0 + (i + 1).toB256 := by
  apply B256.toNat_inj
  rw [B256.toNat_add, B256.toNat_add, B256.toNat_add,
    B256.toNat_toB256_of_lt (by omega : i < 2 ^ 256),
    B256.toNat_toB256_of_lt hi,
    show (Bytes.toB256 [0x01]).toNat = 1 from rfl,
    Nat.add_comm 1, Nat.lo_add_lo]
  congr 1

theorem cursor_succ {p i : Nat} (h : p + 32 * i + 32 < 2 ^ 256) :
    Bytes.toB256 [0x20] + (p + 32 * i).toB256 = (p + 32 * (i + 1)).toB256 := by
  have heq : p + 32 * (i + 1) = p + 32 * i + 32 := by omega
  rw [heq, B256.add_comm]
  exact toB256_add_0x20 h

/-- What a reach to an `SSTORE` concludes inside the copy loop: the store's key is
`base0 + j` for an iteration `j < count fin p`. -/
def PayloadAt (fin base0 : B256) (p : Nat) (T : Conf) : Prop :=
  ∃ j v S, j < count fin p ∧ T.d.stack = (base0 + j.toB256) :: v :: S

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}
  {rd : Ninst} {back : Bytes} {bound : back.length ≤ 32} {k : Nat}
  {fin base0 : B256} {p : Nat} {rest : List B256} {K : List SFunc} {T : Conf}

/-- One copy iteration on a reach: it stops at its store, whose key is the iteration's, or
returns to the head with the next invariant. `rdStep` reads one word in place of the cursor;
`win` leaves room for the next cursor whenever the cursor is below `fin`. -/
theorem body_reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (hrd : rd ≠ .reg .sstore)
    (rdStep : ∀ {b : Devm} {S : List B256} {M : Mem} {G : Nat} {d : Devm} {c : B256},
      P sevm (St b (c :: S) M G) rd d →
        ∃ v b' M' G', d = St b' (v :: S) M' G' ∧ SolcStorageReturn.Keeps M M')
    (win : ∀ {b : Devm} {S : List B256} {M : Mem} {G : Nat} {d : Devm} {c : B256},
      P sevm (St b (c :: S) M G) rd d → c.toNat < fin.toNat → c.toNat + 32 < 2 ^ 256)
    {H : SFunc} (entry : fs[k]? = some H)
    {i : Nat} (hlt : i < count fin p) (hnow : p + 32 * i < 2 ^ 256)
    (hcur : p + 32 * i < fin.toNat)
    {b : Devm} {M : Mem} {G : Nat}
    (run : Reach P fs sevm ⟨St b (fin :: (base0 + i.toB256) :: ((p + 32 * i).toB256) :: rest)
      M G, bodyR rd back bound k, K⟩ T) (hT : AtSstore T) :
    PayloadAt fin base0 p T ∨
      ∃ d', Inv fin base0 p rest (i + 1) d' ∧ SolcStorageReturn.Keeps M d'.memory ∧
        Reach P fs sevm ⟨d', H, K⟩ T := by
  unfold bodyR at run
  rsx
  obtain ⟨_, hstep, run⟩ := rs_next run hT hrd
  have hwin := win hstep (by rw [B256.toNat_toB256_of_lt hnow]; exact hcur)
  rw [B256.toNat_toB256_of_lt hnow] at hwin
  obtain ⟨v, b', M', G', rfl, hkeep⟩ := rdStep hstep
  clear hstep
  rsx
  rcases Reach.sstoreS run with rfl | ⟨_, hstep, run⟩
  · exact .inl ⟨i, v, _, hlt, rfl⟩
  obtain ⟨_, _, e⟩ := SolcStorageReturn.ri_sstore_any (erase hstep)
  subst e
  clear hstep
  iterate 9 rsx
  obtain ⟨g, _, hg, run⟩ := rs_jump run hT
  rw [entry] at hg
  cases hg
  refine .inr ⟨St _ _ _ _, ⟨?_, ?_, ?_⟩, hkeep, run⟩
  · unfold count at hlt ⊢; omega
  · omega
  · simp only [St.stack]
    rw [key_succ base0 (by omega), cursor_succ hwin]

/-- `MLOAD` as the copy loop's read, under the potential: one word in place of the cursor,
with room for the next cursor. -/
theorem mload_rdStep (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {d : Devm} {c : B256}
    (h : FreePtr.PotStep P sevm (St b (c :: S) M G) (.reg .mload) d) :
    ∃ v b' M' G', d = St b' (v :: S) M' G' ∧ SolcStorageReturn.Keeps M M' := by
  obtain ⟨G', rfl⟩ := ri_mload (erase h.1)
  exact ⟨_, _, _, _, rfl, SolcStorageReturn.Keeps.read _ _ _⟩

theorem mload_win (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {d : Devm} {c : B256}
    (h : FreePtr.PotStep P sevm (St b (c :: S) M G) (.reg .mload) d) (_ : c.toNat < fin.toNat) :
    c.toNat + 32 < 2 ^ 256 :=
  SolcStoragePayload.readWindow_of_potStep erase rfl h

/-- `CALLDATALOAD` as the copy loop's read: one word in place of the cursor; the room for
the next cursor comes from the end word. -/
theorem cdload_rdStep (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {d : Devm} {c : B256}
    (h : P sevm (St b (c :: S) M G) (.reg .calldataload) d) :
    ∃ v b' M' G', d = St b' (v :: S) M' G' ∧ SolcStorageReturn.Keeps M M' := by
  obtain ⟨G', rfl⟩ := ri_calldataload (erase h)
  exact ⟨_, _, _, _, rfl, SolcStorageReturn.Keeps.refl _⟩

theorem cdload_win (hfin : fin.toNat + 32 ≤ 2 ^ 256)
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {d : Devm} {c : B256}
    (_ : P sevm (St b (c :: S) M G) (.reg .calldataload) d) (hc : c.toNat < fin.toNat) :
    c.toNat + 32 < 2 ^ 256 := by
  omega

/-- The exit test of the head: the store arm has the cursor below `fin`, the exit arm has
`count fin p ≤ i`. -/
theorem flag_store {i : Nat} (hnow : p + 32 * i < 2 ^ 256)
    (hw : B256.eqCheck (B256.gtCheck fin (p + 32 * i).toB256) 0 = 0) :
    p + 32 * i < fin.toNat ∧ i < count fin p := by
  have h := gtCheck_iszero_eq hw
  rw [B256.toNat_toB256_of_lt hnow] at h
  exact ⟨h, by unfold count; omega⟩

theorem flag_exit {i : Nat} (hnow : p + 32 * i < 2 ^ 256)
    (hw : B256.eqCheck (B256.gtCheck fin (p + 32 * i).toB256) 0 ≠ 0) : count fin p ≤ i := by
  have h0 : B256.gtCheck fin (p + 32 * i).toB256 = 0 := by
    unfold B256.eqCheck at hw
    split at hw
    · assumption
    · exact (hw rfl).elim
  have hle : ¬ (p + 32 * i).toB256 < fin := by
    intro hl
    unfold B256.gtCheck at h0
    simp only [gt_iff_lt, hl, ↓reduceIte] at h0
    exact absurd h0 (by decide)
  rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hnow] at hle
  unfold count
  omega

/-- **The copy loop with its exit inline, on a reach to an `SSTORE`.** From the head under
the loop invariant, the reach stops at a store of the loop (`PayloadAt`) or leaves through
the inline exit `tail` at the last iteration. -/
theorem payloadB_reach_exact (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (hrd : rd ≠ .reg .sstore)
    (rdStep : ∀ {b : Devm} {S : List B256} {M : Mem} {G : Nat} {d : Devm} {c : B256},
      P sevm (St b (c :: S) M G) rd d →
        ∃ v b' M' G', d = St b' (v :: S) M' G' ∧ SolcStorageReturn.Keeps M M')
    (win : ∀ {b : Devm} {S : List B256} {M : Mem} {G : Nat} {d : Devm} {c : B256},
      P sevm (St b (c :: S) M G) rd d → c.toNat < fin.toNat → c.toNat + 32 < 2 ^ 256)
    {exit : Bytes} {ebound : exit.length ≤ 32} {tail : SFunc}
    (entry : fs[k]? = some (headB rd back exit bound ebound k tail))
    {i : Nat} {d : Devm} (hinv : Inv fin base0 p rest i d)
    (run : Reach P fs sevm ⟨d, headB rd back exit bound ebound k tail, K⟩ T)
    (hT : AtSstore T) :
    PayloadAt fin base0 p T ∨
      ∃ i b M G, i = count fin p ∧ SolcStorageReturn.Keeps d.memory M ∧
        Reach P fs sevm ⟨St b (fin :: (base0 + i.toB256) ::
        ((p + 32 * i).toB256) :: rest) M G, tail, K⟩ T := by
  refine reach_loop_index (fun i d' => Inv fin base0 p rest i d' ∧
    SolcStorageReturn.Keeps d.memory d'.memory) (count fin p) (fun i d h => h.1.1) ?_ i d
    ⟨hinv, SolcStorageReturn.Keeps.refl _⟩ run
  intro i d' ⟨hinv, hk0⟩ run
  obtain ⟨hle, hnow, hstack⟩ := hinv
  rw [St.self' d', hstack] at run
  unfold headB at run
  rsd
  iterate 5 rsx
  rcases rs_branch run hT with ⟨hw, _, run⟩ | ⟨hw, _, run⟩
  · obtain ⟨hcur, hlt⟩ := flag_store hnow hw
    rcases body_reach erase hrd rdStep win entry hlt hnow hcur run hT with h | ⟨e, he, hk, run⟩
    · exact .inl (.inl h)
    · exact .inr ⟨e, ⟨he, hk0.trans hk⟩, run⟩
  · exact .inl (.inr ⟨i, _, _, _, Nat.le_antisymm hle (flag_exit hnow hw), hk0, run⟩)

theorem payloadB_reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (hrd : rd ≠ .reg .sstore)
    (rdStep : ∀ {b : Devm} {S : List B256} {M : Mem} {G : Nat} {d : Devm} {c : B256},
      P sevm (St b (c :: S) M G) rd d →
        ∃ v b' M' G', d = St b' (v :: S) M' G' ∧ SolcStorageReturn.Keeps M M')
    (win : ∀ {b : Devm} {S : List B256} {M : Mem} {G : Nat} {d : Devm} {c : B256},
      P sevm (St b (c :: S) M G) rd d → c.toNat < fin.toNat → c.toNat + 32 < 2 ^ 256)
    {exit : Bytes} {ebound : exit.length ≤ 32} {tail : SFunc}
    (entry : fs[k]? = some (headB rd back exit bound ebound k tail))
    {i : Nat} {d : Devm} (hinv : Inv fin base0 p rest i d)
    (run : Reach P fs sevm ⟨d, headB rd back exit bound ebound k tail, K⟩ T)
    (hT : AtSstore T) :
    PayloadAt fin base0 p T ∨
      ∃ i b M G, count fin p ≤ i ∧ SolcStorageReturn.Keeps d.memory M ∧
        Reach P fs sevm ⟨St b (fin :: (base0 + i.toB256) ::
        ((p + 32 * i).toB256) :: rest) M G, tail, K⟩ T := by
  rcases payloadB_reach_exact erase hrd rdStep win entry hinv run hT with h |
      ⟨i, b, M, G, hi, hk, run⟩
  · exact .inl h
  · exact .inr ⟨i, b, M, G, hi.symm.le, hk, run⟩

/-- **The copy loop with its exit through a goto, on a reach to an `SSTORE`.** As
`payloadB_reach`, leaving through entry `j`. -/
theorem payloadJ_reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (hrd : rd ≠ .reg .sstore)
    (rdStep : ∀ {b : Devm} {S : List B256} {M : Mem} {G : Nat} {d : Devm} {c : B256},
      P sevm (St b (c :: S) M G) rd d →
        ∃ v b' M' G', d = St b' (v :: S) M' G' ∧ SolcStorageReturn.Keeps M M')
    (win : ∀ {b : Devm} {S : List B256} {M : Mem} {G : Nat} {d : Devm} {c : B256},
      P sevm (St b (c :: S) M G) rd d → c.toNat < fin.toNat → c.toNat + 32 < 2 ^ 256)
    {exit : Bytes} {ebound : exit.length ≤ 32} {j : Nat}
    (entry : fs[k]? = some (headJ rd back exit bound ebound k j))
    {i : Nat} {d : Devm} (hinv : Inv fin base0 p rest i d)
    (run : Reach P fs sevm ⟨d, headJ rd back exit bound ebound k j, K⟩ T)
    (hT : AtSstore T) :
    PayloadAt fin base0 p T ∨
      ∃ i g b M G, count fin p ≤ i ∧ fs[j]? = some g ∧ SolcStorageReturn.Keeps d.memory M ∧
        Reach P fs sevm ⟨St b (fin ::
        (base0 + i.toB256) :: ((p + 32 * i).toB256) :: rest) M G, g, K⟩ T := by
  refine reach_loop_index (fun i d' => Inv fin base0 p rest i d' ∧
    SolcStorageReturn.Keeps d.memory d'.memory) (count fin p) (fun i d h => h.1.1) ?_ i d
    ⟨hinv, SolcStorageReturn.Keeps.refl _⟩ run
  intro i d' ⟨hinv, hk0⟩ run
  obtain ⟨-, hnow, hstack⟩ := hinv
  rw [St.self' d', hstack] at run
  unfold headJ at run
  rsd
  iterate 5 rsx
  rcases rs_branchTo run hT with ⟨hw, _, run⟩ | ⟨hw, g, _, hg, run⟩
  · obtain ⟨hcur, hlt⟩ := flag_store hnow hw
    rcases body_reach erase hrd rdStep win entry hlt hnow hcur run hT with h | ⟨e, he, hk, run⟩
    · exact .inl (.inl h)
    · exact .inr ⟨e, ⟨he, hk0.trans hk⟩, run⟩
  · exact .inl (.inr ⟨i, g, _, _, _, flag_exit hnow hw, hg, hk0, run⟩)

end ReachPayload

/-! ## The clearing loops -/

namespace ReachClear

/-- A reach to an `SSTORE` stopped at a store of literal zero. -/
def ZeroAt (T : Conf) : Prop := ∃ x S, T.d.stack = x :: 0 :: S

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}
  {back exit : Bytes} {backBound : back.length ≤ 32} {exitBound : exit.length ≤ 32}
  {k : Nat} {K : List SFunc} {T : Conf}

/-- The clearing measure: the keys left below the end word. -/
def gap (e : B256) (d : Devm) : Nat := e.toNat - (d.stack.headD 0).toNat

theorem key_next {key e : B256} (h : key.toNat < e.toNat) :
    (Bytes.toB256 [0x01] + key).toNat = key.toNat + 1 := by
  rw [B256.toNat_add, show (Bytes.toB256 [0x01]).toNat = 1 from rfl,
    Nat.lo_eq_of_lt (by have := B256.toNat_lt (x := e); omega)]
  omega

/-- **The compact clearing loop on a reach to an `SSTORE`.** From the head with the key on
top of the end word, the reach stops at a zero store of the loop, or returns from the loop
into a pending continuation. -/
theorem clear_reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (entry : fs[k]? = some (SolcStorageClear.head back exit backBound exitBound k))
    {e t : B256} {S : List B256} {d : Devm} {key : B256} (hstack : d.stack = key :: e :: t :: S)
    (run : Reach P fs sevm ⟨d, SolcStorageClear.head back exit backBound exitBound k, K⟩ T)
    (hT : AtSstore T) :
    ZeroAt T ∨ ∃ f K' b' G', K = f :: K' ∧ Reach P fs sevm ⟨St b' (e :: S) d.memory G', f, K'⟩ T := by
  refine reach_loop_measure (fun d' => (∃ key, d'.stack = key :: e :: t :: S) ∧
    d'.memory = d.memory) (gap e) ?_ d ⟨⟨key, hstack⟩, rfl⟩ run
  intro d' ⟨⟨key, hstack⟩, hmem⟩ run
  rw [← hmem]
  rw [St.self' d', hstack] at run
  unfold SolcStorageClear.head at run
  rsd
  iterate 5 rsx
  rcases rs_branch run hT with ⟨hw, _, run⟩ | ⟨hw, _, run⟩
  · have hlt := gtCheck_iszero_eq hw
    unfold SolcStorageClear.body at run
    iterate 2 rsx
    rcases Reach.sstoreS run with rfl | ⟨_, hstep, run⟩
    · exact .inl (.inl ⟨_, _, by rw [St.stack, show Bytes.toB256 [0x00] = (0 : B256) by decide]⟩)
    obtain ⟨_, _, e'⟩ := SolcStorageReturn.ri_sstore_any (erase hstep)
    subst e'
    clear hstep
    unfold SolcStorageClear.tail at run
    iterate 3 rsx
    obtain ⟨g, _, hg, run⟩ := rs_jump run hT
    rw [entry] at hg
    cases hg
    refine .inr ⟨St _ _ _ _, ⟨⟨_, rfl⟩, rfl⟩, ?_, run⟩
    unfold gap
    simp only [St.stack, List.headD_cons]
    rw [hstack, key_next hlt]
    simp only [List.headD_cons]
    omega
  · unfold SolcStorageClear.exitTree at run
    rsd
    iterate 2 rsx
    obtain ⟨f, K', b', G', hK, rest⟩ := rs_retM run hT
    exact .inl (.inr ⟨f, K', b', G', hK, rest⟩)

/-- The legacy clearing loop reaches a zero store whose key is at least the
initial key and strictly below the exact end word, or returns into the same
pending continuation. -/
theorem legacyClear_reach_range (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {j : Nat} (entry : fs[k]? = some (SolcStorageClear.legacyHead back exit backBound exitBound k j))
    (retEntry : fs[j]? = some SolcStorageClear.legacyRet)
    {e t u : B256} {S : List B256} {d : Devm} {key : B256}
    (hstack : d.stack = key :: e :: t :: u :: S)
    (run : Reach P fs sevm ⟨d, SolcStorageClear.legacyHead back exit backBound exitBound k j, K⟩ T)
    (hT : AtSstore T) :
    (∃ current rest, T.d.stack = current :: 0 :: rest ∧
      key.toNat ≤ current.toNat ∧ current.toNat < e.toNat) ∨
      ∃ f K' b' G', K = f :: K' ∧ Reach P fs sevm ⟨St b' (e :: S) d.memory G', f, K'⟩ T := by
  refine reach_loop_measure (fun d' => (∃ current,
    d'.stack = current :: e :: t :: u :: S ∧ key.toNat ≤ current.toNat) ∧
    d'.memory = d.memory) (gap e) ?_ d ⟨⟨key, hstack, le_refl _⟩, rfl⟩ run
  intro d' ⟨⟨current, hstack, lower⟩, hmem⟩ run
  rw [← hmem]
  rw [St.self' d', hstack] at run
  unfold SolcStorageClear.legacyHead at run
  rsd
  iterate 5 rsx
  rcases rs_branch run hT with ⟨hw, _, run⟩ | ⟨hw, _, run⟩
  · have hlt := gtCheck_iszero_eq hw
    unfold SolcStorageClear.legacyBody at run
    iterate 4 rsx
    rcases Reach.sstoreS run with rfl | ⟨_, hstep, run⟩
    · exact .inl (.inl ⟨current, _, by
        rw [St.stack, show Bytes.toB256 [0x00] = (0 : B256) by decide], lower, hlt⟩)
    obtain ⟨_, _, e'⟩ := SolcStorageReturn.ri_sstore_any (erase hstep)
    subst e'
    clear hstep
    unfold SolcStorageClear.legacyStoreTail at run
    iterate 4 rsx
    obtain ⟨g, _, hg, run⟩ := rs_jump run hT
    rw [entry] at hg
    cases hg
    refine .inr ⟨St _ _ _ _, ⟨⟨_, rfl, ?_⟩, rfl⟩, ?_, run⟩
    · rw [key_next hlt]
      omega
    · unfold gap
      simp only [St.stack, List.headD_cons]
      rw [hstack, key_next hlt]
      simp only [List.headD_cons]
      omega
  · unfold SolcStorageClear.legacyExit at run
    rsd
    iterate 2 rsx
    obtain ⟨g, _, hg, run⟩ := rs_jump run hT
    rw [retEntry] at hg
    cases hg
    unfold SolcStorageClear.legacyRet at run
    rsd
    rsx
    obtain ⟨f, K', b', G', hK, rest⟩ := rs_retM run hT
    exact .inl (.inr ⟨f, K', b', G', hK, rest⟩)

/-- **The legacy clearing loop on a reach to an `SSTORE`.** As `clear_reach`, for the
layout whose exit jumps through the shared return entry `j`. -/
theorem legacyClear_reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {j : Nat} (entry : fs[k]? = some (SolcStorageClear.legacyHead back exit backBound exitBound k j))
    (retEntry : fs[j]? = some SolcStorageClear.legacyRet)
    {e t u : B256} {S : List B256} {d : Devm} {key : B256}
    (hstack : d.stack = key :: e :: t :: u :: S)
    (run : Reach P fs sevm ⟨d, SolcStorageClear.legacyHead back exit backBound exitBound k j, K⟩ T)
    (hT : AtSstore T) :
    ZeroAt T ∨ ∃ f K' b' G', K = f :: K' ∧ Reach P fs sevm ⟨St b' (e :: S) d.memory G', f, K'⟩ T := by
  rcases legacyClear_reach_range erase entry retEntry hstack run hT with
    ⟨current, rest, stack, -, -⟩ | continuation
  · exact .inl ⟨current, rest, stack⟩
  · exact .inr continuation

end ReachClear

end Blanc.Lift
