import Blanc.AddressSlotProofs
import Blanc.LadderBase
import Blanc.Lift.SolcStorageClear
import Blanc.Lift.SolcStoragePayload
import Blanc.Lift.RunPWalk
import Blanc.Lift.InvWalkOps

/-!
# Returning runs of solc storage templates, and run rebuilding

Contract-neutral companions to `Blanc.Lift.SolcStorageClear` and
`Blanc.Lift.SolcStoragePayload`, which classify the stores of the legacy
clearing loop and of the memory-to-storage payload loop. A caller that
continues after such a helper also needs what the helper *returns*; this
module derives it from the actual runs, with no fork, gas or memory
well-formedness premise.

* `ownerInit`, `ownerInit_effects`: the packed owner initializer writes slot zero
  from the low 160 bits of the owner operand and returns with unchanged memory
  and foreign-account storage, independently of the selected fork.
* `sload_memory`, `sstore_memory`: a successful `SLOAD`/`SSTORE` keeps memory
  exactly (any fork); `ri_sload_any`, `ri_sstore_any` invert them over the walk
  state with the world left existential.
* `qdest`, `qbranch`, `qbranchTo`: rebuild a run under a stronger step
  relation `Q` through a jumpdest or a branch, given the arm rebuilds.
* `runCutP_done`: a cut run that finished is an ordinary run.
* `Keeps`: memory keeps every byte and does not shrink.
* `legacyRunP_returned`: a returning legacy clearing run from
  `cur :: e :: a :: r :: rest` returns `e :: rest` with the same memory.
* `payload_exit`: any payload-loop run reaches its exit tail with the same
  stack tail under kept memory.

Worked use: `Blanc/Lift/Usdc/OldInitializerV1Callee.lean`.
-/

namespace Blanc.Lift.SolcStorageReturn

open Jaune Blanc Blanc.Lift

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

theorem sload_memory {d d' : Devm} (h : Ninst.Run sevm d (.reg .sload) d') :
    d'.memory = d.memory := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  obtain ⟨⟨x, d1⟩, h1, e1⟩ := Except.bind_eq_ok run
  have m1 := (Devm.pop_of_pop h1).memory
  cases access : sevm.benvStat.rules.access with
  | eip2929 =>
    simp only [access] at e1
    split at e1
    · obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok e1
      exact ((Devm.push_of_push h3).memory.symm.trans
        (Devm.burn_of_chargeGas h2).memory.symm).trans m1.symm
    · obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok e1
      exact ((Devm.push_of_push h3).memory.symm.trans
        (Devm.burn_of_chargeGas h2).memory.symm).trans m1.symm
  | flat gas =>
    simp only [access] at e1
    obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok e1
    exact ((Devm.push_of_push h3).memory.symm.trans
      (Devm.burn_of_chargeGas h2).memory.symm).trans m1.symm

theorem sstore_memory {d d' : Devm} (h : Ninst.Run sevm d (.reg .sstore) d') :
    d'.memory = d.memory := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  split at run
  · split at run
    · obtain ⟨⟨x, d1⟩, h1, e1⟩ := Except.bind_eq_ok run
      obtain ⟨⟨y, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
      obtain ⟨_, _, e3⟩ := Except.bind_eq_ok e2
      obtain ⟨⟨d3, g⟩, h4, e4⟩ := Except.bind_eq_ok e3
      obtain ⟨g3, h5, e5⟩ := Except.bind_eq_ok e4
      obtain ⟨d4, h6, e6⟩ := Except.bind_eq_ok e5
      obtain ⟨d5, h7, e7⟩ := Except.bind_eq_ok e6
      obtain ⟨_, _, h9⟩ := Except.bind_eq_ok e7
      cases h9
      have m3 : d3.memory = d2.memory := by
        injection h4 with eq
        split at eq <;> (injection eq with eq _; subst eq; rfl)
      have m4 : d4.memory = d3.memory := by
        injection h6 with eq; rw [← eq]; rfl
      show d5.memory = d.memory
      rw [← (Devm.burn_of_chargeGas h7).memory, m4, m3, ← (Devm.pop_of_pop h2).memory,
        ← (Devm.pop_of_pop h1).memory]
    · obtain ⟨⟨x, d1⟩, h1, e1⟩ := Except.bind_eq_ok run
      obtain ⟨⟨y, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
      obtain ⟨_, _, e3⟩ := Except.bind_eq_ok e2
      obtain ⟨⟨d3, g⟩, h4, e4⟩ := Except.bind_eq_ok e3
      obtain ⟨g3, h5, e5⟩ := Except.bind_eq_ok e4
      obtain ⟨d4, h6, e6⟩ := Except.bind_eq_ok e5
      obtain ⟨d5, h7, e7⟩ := Except.bind_eq_ok e6
      obtain ⟨_, _, h9⟩ := Except.bind_eq_ok e7
      cases h9
      have m3 : d3.memory = d2.memory := by
        injection h4 with eq
        cases access : sevm.benvStat.rules.access with
        | flat gas =>
            simp only [access] at eq
            injection eq with eq _
            subst eq
            rfl
        | eip2929 =>
            simp only [access] at eq
            split at eq <;> (injection eq with eq _; subst eq; rfl)
      have m4 : d4.memory = d3.memory := by
        injection h6 with eq; rw [← eq]; rfl
      show d5.memory = d.memory
      rw [← (Devm.burn_of_chargeGas h7).memory, m4, m3, ← (Devm.pop_of_pop h2).memory,
        ← (Devm.pop_of_pop h1).memory]
  · obtain ⟨_, _, e0⟩ := Except.bind_eq_ok run
    obtain ⟨⟨x, d1⟩, h1, e1⟩ := Except.bind_eq_ok e0
    obtain ⟨⟨y, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
    obtain ⟨_, _, e3⟩ := Except.bind_eq_ok e2
    obtain ⟨d3, hchg, e4⟩ := Except.bind_eq_ok e3
    obtain ⟨d4, hstg, h9⟩ := Except.bind_eq_ok e4
    cases h9
    have mc := (Devm.burn_of_chargeGas hchg).memory
    have ms := Devm.chargeStateGas_memory hstg
    show d4.memory = d.memory
    rw [ms, ← mc]
    have e1 : ∀ (a : Nat) (d : Devm), (Devm.creditStateGasRefund a d).memory = d.memory :=
      fun _ _ => rfl
    have e2 : ∀ (r : Int) (d : Devm), (d.withRefundCounter r).memory = d.memory :=
      fun _ _ => rfl
    have e3 : ∀ (rl : ForkRules) (a : Adr) (k : B256) (d : Devm),
        (Devm.balReadStorage rl a k d).memory = d.memory := fun _ _ _ _ => rfl
    have e4 : ∀ (d : Devm) (a : Adr) (k : B256),
        (addAccessedStorageKey d a k).memory = d.memory := fun _ _ _ => rfl
    rw [e1, e2, e3]
    split
    · rw [e4, ← (Devm.pop_of_pop h2).memory, ← (Devm.pop_of_pop h1).memory]
    · rw [← (Devm.pop_of_pop h2).memory, ← (Devm.pop_of_pop h1).memory]

theorem ri_sload_any {k : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (k :: S) M G) (.reg .sload) d) :
    ∃ b' v G', d = St b' (v :: S) M G' := by
  obtain ⟨x, s1, hpop, hpush⟩ := of_run_sload h
  simp only [Stack.Pop, Stack.Push, Split, St.stack, List.cons_append, List.nil_append,
    List.cons.injEq] at hpop hpush
  obtain ⟨rfl, rfl⟩ := hpop
  exact ⟨_, _, _, St.self hpush (sload_memory h)⟩

theorem ri_sstore_any {k v : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (k :: v :: S) M G) (.reg .sstore) d) :
    ∃ b' G', d = St b' S M G' := by
  obtain ⟨x, y, hpop⟩ := of_run_sstore h
  simp only [Stack.Pop, Split, St.stack, List.cons_append, List.nil_append,
    List.cons.injEq] at hpop
  obtain ⟨rfl, rfl, hpost⟩ := hpop
  exact ⟨_, _, St.self hpost.symm (sstore_memory h)⟩

variable {P : Sevm → Devm → Ninst → Devm → Prop}

section Rebuild

variable {Q : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {f g : SFunc}
  {o : Outcome}

theorem qdest (run : SFunc.RunP P fs sevm (St b S M G) (.dest f) o)
    (k : ∀ G', SFunc.RunP P fs sevm (St b S M G') f o → SFunc.RunP Q fs sevm (St b S M G') f o) :
    SFunc.RunP Q fs sevm (St b S M G) (.dest f) o := by
  cases run with
  | dest burn run =>
    have e := St.of_burn burn
    rw [e] at run burn
    exact .dest burn (k _ run)

theorem qbranch {dd w : B256}
    (run : SFunc.RunP P fs sevm (St b (dd :: w :: S) M G) (.branch f g) o)
    (k0 : ∀ G', w = 0 → SFunc.RunP P fs sevm (St b S M G') f o →
      SFunc.RunP Q fs sevm (St b S M G') f o)
    (k1 : ∀ G', w ≠ 0 → SFunc.RunP P fs sevm (St b S M G') g o →
      SFunc.RunP Q fs sevm (St b S M G') g o) :
    SFunc.RunP Q fs sevm (St b (dd :: w :: S) M G) (.branch f g) o := by
  cases run with
  | zero d0 pop run =>
    obtain ⟨-, hw, e⟩ := St.of_pop2 pop
    rw [e] at run pop
    exact .zero d0 pop (k0 _ hw run)
  | succ d0 w0 hne pop run =>
    obtain ⟨-, hw, e⟩ := St.of_pop2 pop
    rw [e] at run pop
    subst hw
    exact .succ d0 w hne pop (k1 _ hne run)

theorem qbranchTo {dd w : B256} {kk : Nat}
    (run : SFunc.RunP P fs sevm (St b (dd :: w :: S) M G) (.branchTo f kk) o)
    (k0 : ∀ G', w = 0 → SFunc.RunP P fs sevm (St b S M G') f o →
      SFunc.RunP Q fs sevm (St b S M G') f o)
    (k1 : ∀ G' g, w ≠ 0 → fs[kk]? = some g → SFunc.RunP P fs sevm (St b S M G') g o →
      SFunc.RunP Q fs sevm (St b S M G') g o) :
    SFunc.RunP Q fs sevm (St b (dd :: w :: S) M G) (.branchTo f kk) o := by
  cases run with
  | toZero d0 pop run =>
    obtain ⟨-, hw, e⟩ := St.of_pop2 pop
    rw [e] at run pop
    exact .toZero d0 pop (k0 _ hw run)
  | toSucc d0 w0 hne get pop run =>
    obtain ⟨-, hw, e⟩ := St.of_pop2 pop
    rw [e] at run pop
    subst hw
    exact .toSucc d0 w hne get pop (k1 _ _ hne get run)

end Rebuild
set_option hygiene false in
/-- One cut-run step inverted with `t`. -/
local macro "cs " t:term : tactic => `(tactic| (
  have step := ric_nextP cut
  clear cut
  obtain ⟨_, w, cut⟩ := step
  obtain ⟨_, rfl⟩ := $t (erase w)
  clear w
  try dsimp only [List.set, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at cut))

section Legacy

open SolcStorageClear

variable {fs : List SFunc} {back exit : Bytes} {backBound : back.length ≤ 32}
  {exitBound : exit.length ≤ 32} {k j : Nat}

/-- A returning run of the legacy clearing loop from `cur :: e :: a :: r :: rest`
returns `e :: rest` with the same memory (the exit drops the cursor and the
jump word `a`, the return entry drops the return word `r`). -/
theorem legacyRunP_returned
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (entry : fs[k]? = some (legacyHead back exit backBound exitBound k j))
    (retEntry : fs[j]? = some legacyRet) (jk : j ≠ k)
    {cur e a r : B256} {rest : List B256} {D : Devm}
    (run : SFunc.RunP P fs sevm (St b (cur :: e :: a :: r :: rest) M G)
      (legacyHead back exit backBound exitBound k j) (.returned D)) :
    ∃ b' G', D = St b' (e :: rest) M G' := by
  let I : Devm → Prop := fun d => ∃ c b' G', d = St b' (c :: e :: a :: r :: rest) M G'
  let Q : Outcome → Prop := fun o => ∀ D, o = .returned D → ∃ b' G', D = St b' (e :: rest) M G'
  refine SFunc.RunP.loop entry I Q ?_ _ _ ⟨cur, b, G, rfl⟩ run D rfl
  intro d hI sg cut
  obtain ⟨c, b1, G1, rfl⟩ := hI
  unfold legacyHead at cut
  obtain ⟨_, cut⟩ := ric_destP cut
  cs ri_dup rfl
  cs ri_dup rfl
  cs ri_gt
  cs ri_iszero
  cs ri_push
  rcases ric_branchP cut with ⟨-, _, cut⟩ | ⟨-, _, cut⟩
  · unfold legacyBody legacyStoreTail at cut
    cs ri_push
    cs ri_dup rfl
    cs ri_push
    cs ri_swap rfl
    have step := ric_nextP cut
    clear cut
    obtain ⟨_, w, cut⟩ := step
    obtain ⟨_, _, rfl⟩ := ri_sstore_any (erase w)
    clear w
    cs ri_pop
    cs ri_push
    cs ri_add
    cs ri_push
    cases cut with
    | jumpCut d0 _ pop =>
      exact ⟨_, _, _, (St.of_pop1 pop).2⟩
    | jump _ nc _ _ _ => exact (nc (List.mem_singleton.mpr rfl)).elim
  · unfold legacyExit at cut
    obtain ⟨_, cut⟩ := ric_destP cut
    cs ri_pop
    cs ri_swap rfl
    cases cut with
    | jumpCut _ mem _ => exact (jk (List.mem_singleton.mp mem)).elim
    | jump d0 _ get pop cut =>
      cases Option.some.inj (get.symm.trans retEntry)
      rw [(St.of_pop1 pop).2] at cut
      unfold legacyRet at cut
      obtain ⟨_, cut⟩ := ric_destP cut
      cs ri_swap rfl
      cases cut with
      | ret d1 pop =>
        intro D hD
        cases hD
        exact ⟨_, _, (St.of_pop1 pop).2⟩

end Legacy
/-- A cut run that finished never stopped at a cut: it is an ordinary run. -/
theorem runCutP_done {fs : List SFunc} {C : List Nat} {d : Devm} {f : SFunc} {o : Outcome}
    (run : SFunc.RunCutP P fs sevm C d f (.done o)) : SFunc.RunP P fs sevm d f o := by
  generalize hs : Seg.done o = sg at run
  induction run with
  | zero d0 pop _ ih => exact .zero d0 pop (ih hs)
  | succ d0 w hw pop _ ih => exact .succ d0 w hw pop (ih hs)
  | toZero d0 pop _ ih => exact .toZero d0 pop (ih hs)
  | toSuccCut => cases hs
  | toSucc d0 w hw _ get pop _ ih => exact .toSucc d0 w hw get pop (ih hs)
  | last h => cases hs; exact .last h
  | next h _ ih => exact .next h (ih hs)
  | dest h _ ih => exact .dest h (ih hs)
  | jumpCut => cases hs
  | jump d0 _ get pop _ ih => exact .jump d0 get pop (ih hs)
  | ret d0 pop => cases hs; exact .ret d0 pop
  | callHalt d0 get pop callee => cases hs; exact .callHalt d0 get pop callee
  | callRet d0 get pop callee _ ih => exact .callRet d0 get pop callee (ih hs)
  | pcAt h hpc _ ih => exact .pcAt h hpc (ih hs)

/-- Memory `M'` keeps every byte of `M` and is no smaller. -/
def Keeps (M M' : Mem) : Prop := M'.data = M.data ∧ M.size ≤ M'.size

theorem Keeps.refl (M : Mem) : Keeps M M := ⟨rfl, le_refl _⟩

theorem Keeps.trans {M1 M2 M3 : Mem} (h1 : Keeps M1 M2) (h2 : Keeps M2 M3) : Keeps M1 M3 :=
  ⟨h2.1.trans h1.1, le_trans h1.2 h2.2⟩

theorem Keeps.read (M : Mem) (i n : Nat) : Keeps M (M.read i n).2 :=
  ⟨rfl, memExtSize_ge _ _ _⟩

section Payload

open SolcStoragePayload

variable {fs : List SFunc} {back exit : Bytes} {bound : back.length ≤ 32}
  {ebound : exit.length ≤ 32} {k : Nat} {tail : SFunc}

/-- Any run of the payload loop from `x :: y :: z :: rest` reaches its exit
tail from a state with the same `rest` under kept memory. -/
theorem payload_exit
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (entry : fs[k]? = some (head back exit bound ebound k tail))
    (tailDone : ∀ {d sg}, SFunc.RunCutP P fs sevm [k] d tail sg → ∃ o, sg = .done o)
    {x y z : B256} {rest : List B256} {o : Outcome}
    (run : SFunc.RunP P fs sevm (St b (x :: y :: z :: rest) M G)
      (head back exit bound ebound k tail) o) :
    ∃ x' y' z' b' M' G', Keeps M M' ∧
      SFunc.RunP P fs sevm (St b' (x' :: y' :: z' :: rest) M' G') tail o := by
  let I : Devm → Prop := fun d => ∃ x y z b' M' G', Keeps M M' ∧
    d = St b' (x :: y :: z :: rest) M' G'
  let Q : Outcome → Prop := fun o => ∃ x' y' z' b' M' G', Keeps M M' ∧
    SFunc.RunP P fs sevm (St b' (x' :: y' :: z' :: rest) M' G') tail o
  refine SFunc.RunP.loop entry I Q ?_ _ _ ⟨x, y, z, b, M, G, Keeps.refl M, rfl⟩ run
  intro d hI sg cut
  obtain ⟨x, y, z, b1, M1, G1, keep, rfl⟩ := hI
  unfold head at cut
  obtain ⟨_, cut⟩ := ric_destP cut
  cs ri_dup rfl
  cs ri_dup rfl
  cs ri_gt
  cs ri_iszero
  cs ri_push
  rcases ric_branchP cut with ⟨-, _, cut⟩ | ⟨-, _, cut⟩
  · unfold body at cut
    cs ri_dup rfl
    cs ri_mload
    cs ri_dup rfl
    have step := ric_nextP cut
    clear cut
    obtain ⟨_, w, cut⟩ := step
    obtain ⟨_, _, rfl⟩ := ri_sstore_any (erase w)
    clear w
    cs ri_swap rfl
    cs ri_push
    cs ri_add
    cs ri_swap rfl
    cs ri_swap rfl
    cs ri_push
    cs ri_add
    cs ri_swap rfl
    cs ri_push
    cases cut with
    | jumpCut d0 _ pop =>
      exact ⟨_, _, _, _, _, _, keep.trans (Keeps.read _ _ _), (St.of_pop1 pop).2⟩
    | jump _ nc _ _ _ => exact (nc (List.mem_singleton.mpr rfl)).elim
  · obtain ⟨o', rfl⟩ := tailDone cut
    exact ⟨_, _, _, _, _, _, keep, runCutP_done cut⟩

end Payload
/-- Solidity's packed owner-field initializer, including its internal return. -/
def ownerInit : SFunc := (.dest (.next (.push [0x00] (by decide)) (.next (.reg (.dup 0)) (.next (.reg .sload) (.next (.push [0x01] (by decide)) (.next (.push [0x01] (by decide)) (.next (.push [0xa0] (by decide)) (.next (.reg .shl) (.next (.reg .sub) (.next (.reg .not) (.next (.reg .and) (.next (.push [0x01] (by decide)) (.next (.push [0x01] (by decide)) (.next (.push [0xa0] (by decide)) (.next (.reg .shl) (.next (.reg .sub) (.next (.reg (.swap 2)) (.next (.reg (.swap 0)) (.next (.reg (.swap 2)) (.next (.reg .and) (.next (.reg (.swap 1)) (.next (.reg (.swap 0)) (.next (.reg (.swap 1)) (.next (.reg .or) (.next (.reg (.swap 0)) (.next (.reg .sstore) .ret))))))))))))))))))))))))))

/-- A successful initializer writes exactly the packed address, drops both the
owner operand and internal return word, and preserves memory and foreign storage.
The owner operand may have arbitrary upper bits; the executed mask removes them. -/
theorem ownerInit_effects
    {fs : List SFunc} {sevm : Sevm} {b post : Devm} {owner returnPC : B256}
    {S : List B256} {M : Mem} {G : Nat}
    (run : SFunc.Run fs sevm (St b (owner :: returnPC :: S) M G)
      ownerInit (.returned post)) :
    post.stack = S ∧ post.memory = M ∧
      post.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set 0
        (addressSlotWriteWord (b.getStorVal sevm.currentTarget 0) owner.toAdr.toB256) ∧
      (∀ a, a ≠ sevm.currentTarget → post.getStor a = b.getStor a) := by
  have run := run.cut
  unfold ownerInit at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (n := 0) rfl step
  obtain ⟨loaded, load, run⟩ := ric_next run
  have storage : loaded.getStor = b.getStor := (Ninst.Hinv.inv (f := Devm.getStor) load).symm
  have memory : loaded.memory = M := SolcStorageReturn.sload_memory load
  obtain ⟨key, tail, popped, pushed⟩ := of_run_sload load
  simp only [Stack.Pop, Stack.Push, Split, St.stack, List.cons_append, List.nil_append,
    List.cons.injEq] at popped pushed
  obtain ⟨rfl, rfl⟩ := popped
  rw [St.self pushed memory] at run
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_shl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, e⟩ := ri_sub step
  change _ = St loaded ((~~~ addressMask) :: b.getStorVal sevm.currentTarget 0 ::
    0 :: owner :: returnPC :: S) M _ at e
  subst e
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, e⟩ := ri_not step
  change _ = St loaded (addressMask :: b.getStorVal sevm.currentTarget 0 ::
    0 :: owner :: returnPC :: S) M _ at e
  subst e
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_shl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, e⟩ := ri_sub step
  change _ = St loaded ((~~~ addressMask) ::
    (addressMask &&& b.getStorVal sevm.currentTarget 0) :: 0 :: owner :: returnPC :: S) M _ at e
  subst e
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, e⟩ := ri_and step
  rw [show (~~~ addressMask) &&& owner = owner.toAdr.toB256 from
    addressSlotReadWord_eq_toAdr_toB256 owner] at e
  subst e
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, e⟩ := ri_or step
  rw [B256.or_comm] at e
  change _ = St loaded (addressSlotWriteWord (b.getStorVal sevm.currentTarget 0)
    owner.toAdr.toB256 :: 0 :: returnPC :: S) M _ at e
  subst e
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨written, store, run⟩ := ric_next run
  have effect := sstore_getStor_set (xs := []) store (by exact ⟨_, rfl⟩)
  have foreign : ∀ a, a ≠ sevm.currentTarget → written.getStor a = b.getStor a := by
    intro a different
    obtain ⟨pc, regular⟩ := of_run_reg store
    exact (sstore_preserves_getStor_ne regular different.symm).trans (congrFun storage a)
  obtain ⟨b', G', e⟩ := SolcStorageReturn.ri_sstore_any store
  rw [e] at run effect foreign
  obtain ⟨_, returned⟩ := ric_ret run
  simp only [Seg.done.injEq, Outcome.returned.injEq] at returned
  subst post
  exact ⟨rfl, rfl, effect.trans (congrArg (fun s => s.set 0
    (addressSlotWriteWord (b.getStorVal sevm.currentTarget 0) owner.toAdr.toB256))
      (congrFun storage sevm.currentTarget)), foreign⟩

end Blanc.Lift.SolcStorageReturn
