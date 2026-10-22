import Blanc.Lift.WriteSiteLocality
import Blanc.Lift.Quiet

/-!
# Zero preservation from checked write locality

An actual SSTORE satisfying `GuardObs K False` preserves zero on the demanded
slots. The lifted-run fold must separately consume actual external-step and
terminal preservation laws; locality alone says nothing about child effects.
These are storage induction tools, with no contract, hash or signature premise.
-/

namespace Blanc.Lift.WriteSite

open Jaune

/-- The demanded physical storage cells of account `a` read zero. -/
def ZeroSlots (K : B256 → Prop) (a : Adr) (d : Devm) : Prop :=
  ∀ x, K x → d.getStorVal a x = 0

/-- Exact storage equality transports a zero seed. -/
theorem ZeroSlots.of_getStor_eq {K : B256 → Prop} {a : Adr} {pre post : Devm}
    (zero : ZeroSlots K a pre) (storage : post.getStor a = pre.getStor a) :
    ZeroSlots K a post := by
  intro x tracked
  change (post.getStor a).get x = 0
  rw [storage]
  exact zero x tracked

/-- An actual non-increasing SSTORE preserves all demanded zero cells,
including those distinct from the written slot. No fork or hash law is needed. -/
theorem GuardObs.sstore_zero {K : B256 → Prop} {sevm : Sevm} {pre post : Devm}
    (obs : GuardObs K False sevm pre (.reg .sstore))
    (run : Ninst.Run sevm pre (.reg .sstore) post)
    (zero : ZeroSlots K sevm.currentTarget pre) : ZeroSlots K sevm.currentTarget post := by
  obtain ⟨key, value, popped⟩ := of_run_sstore run
  have stack : pre.stack = key :: value :: post.stack := popped
  have effect := sstore_getStor_set (xs := []) run ⟨post.stack, popped⟩
  intro probe tracked
  change (post.getStor sevm.currentTarget).get probe = 0
  rw [effect, Stor.get_set_ite]
  by_cases hit : key = probe
  · rw [ite_eq_left hit]
    have keyTracked : K key := by rw [hit]; exact tracked
    rcases obs rfl key value post.stack stack keyTracked with impossible | nonInc
    · exact impossible.elim
    · apply B256.toNat_inj
      rw [B256.toNat_zero]
      have bounded : value.toNat ≤ 0 := by
        simpa only [zero key keyTracked, B256.toNat_zero] using nonInc
      exact Nat.eq_zero_of_le_zero bounded
  · rw [ite_eq_right hit]
    exact zero probe tracked

/-- Zero across one actual instruction. The external arm consumes its exact
filled recursive slot and real `Xinst.Run`; locality does not prove its effect. -/
theorem GuardObs.step_zero {K : B256 → Prop} {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (fork : CoveredFork sevm.benvStat.fork) (obs : GuardObs K False sevm pre n)
    (run : Ninst.Run sevm pre n post)
    (child : ∀ {x : Xinst} {xl : Xlot}, n = .exec x → xl.Filled →
      Xinst.Run sevm pre x xl (.ok post) →
      ZeroSlots K sevm.currentTarget pre → ZeroSlots K sevm.currentTarget post)
    (zero : ZeroSlots K sevm.currentTarget pre) : ZeroSlots K sevm.currentTarget post := by
  cases n with
  | exec x =>
      obtain ⟨xl, filled, pc, step⟩ := run
      simp only [Ninst.StepRun, Ninst.step_exec] at step
      exact child rfl filled (XStep.run_toStep.mp step) zero
  | reg r =>
      by_cases store : r = .sstore
      · subst r
        exact obs.sstore_zero run zero
      · obtain ⟨pc, regular⟩ := of_run_reg run
        exact zero.of_getStor_eq (congrFun (Rinst.preserves_stor store regular) _).symm
  | push bytes bound =>
      exact zero.of_getStor_eq (congrFun (Ninst.world_of_quiet fork rfl run).1 _)
  | dupn imm =>
      exact zero.of_getStor_eq (congrFun (Ninst.world_of_quiet fork rfl run).1 _)
  | swapn imm =>
      exact zero.of_getStor_eq (congrFun (Ninst.world_of_quiet fork rfl run).1 _)
  | exchange imm =>
      exact zero.of_getStor_eq (congrFun (Ninst.world_of_quiet fork rfl run).1 _)

/-- A non-SELFDESTRUCT terminal preserves the zero seed by its actual world
semantics. A consumer reaching SELFDESTRUCT must supply that separate law. -/
theorem terminal_zero {K : B256 → Prop} {a : Adr} {sevm : Sevm} {pre post : Devm} {l : Linst}
    (terminal : l ≠ .selfdestruct) (run : Linst.Run sevm pre l (.ok post))
    (zero : ZeroSlots K a pre) : ZeroSlots K a post :=
  zero.of_getStor_eq (congrFun (Linst.world_of_ok terminal run).1 a)

/-- Fold zero preservation through the actual lifted derivation, including
callee returns and continuations. External and terminal laws concern their
real one-step executions; neither is a whole-run endpoint premise. They must
be discharged by the eventual runtime/history consumer. -/
theorem runP_zero {K : B256 → Prop} {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} (fork : CoveredFork sevm.benvStat.fork)
    (steps : ∀ {d n d'}, P sevm d n d' → Ninst.Run sevm d n d')
    (observations : ∀ {d n d'}, P sevm d n d' → GuardObs K False sevm d n)
    (children : ∀ {d d' x xl}, P sevm d (.exec x) d' → xl.Filled →
      Xinst.Run sevm d x xl (.ok d') →
      ZeroSlots K sevm.currentTarget d → ZeroSlots K sevm.currentTarget d')
    (terminals : ∀ {d d' l}, Linst.Run sevm d l (.ok d') →
      ZeroSlots K sevm.currentTarget d → ZeroSlots K sevm.currentTarget d') :
    ∀ {d f out}, SFunc.RunP P fs sevm d f out → ZeroSlots K sevm.currentTarget d →
      ZeroSlots K sevm.currentTarget (Outcome.devm out) := by
  have stepZero : ∀ {d n d'}, P sevm d n d' →
      ZeroSlots K sevm.currentTarget d → ZeroSlots K sevm.currentTarget d' := by
    intro d n d' step zero
    refine (observations step).step_zero fork (steps step) ?_ zero
    intro x xl instruction filled run
    subst n
    exact children step filled run
  intro d f out run
  induction run with
  | zero _ popped _ ih =>
      intro seed
      exact ih (seed.of_getStor_eq (popped.getStor _))
  | succ _ _ _ popped _ ih =>
      intro seed
      exact ih (seed.of_getStor_eq (popped.getStor _))
  | toZero _ popped _ ih =>
      intro seed
      exact ih (seed.of_getStor_eq (popped.getStor _))
  | toSucc _ _ _ _ popped _ ih =>
      intro seed
      exact ih (seed.of_getStor_eq (popped.getStor _))
  | last run =>
      exact terminals run
  | next step _ ih =>
      intro seed
      exact ih (stepZero step seed)
  | dest burn _ ih =>
      intro seed
      exact ih (seed.of_getStor_eq (Blanc.Devm.Burn.getStor burn _))
  | jump _ _ popped _ ih =>
      intro seed
      exact ih (seed.of_getStor_eq (popped.getStor _))
  | ret _ popped =>
      intro seed
      exact seed.of_getStor_eq (popped.getStor _)
  | callHalt _ _ popped _ ih =>
      intro seed
      exact ih (seed.of_getStor_eq (popped.getStor _))
  | callRet _ _ popped _ _ ihCall ihTail =>
      intro seed
      exact ihTail (ihCall (seed.of_getStor_eq (popped.getStor _)))
  | pcAt step _ _ ih =>
      intro seed
      exact ih (stepZero step seed)

/-- Entry zero's whole-program form of `runP_zero`, for an actual halted run. -/
theorem progRunP_zero {K : B256 → Prop} {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {pre post : Devm}
    (fork : CoveredFork sevm.benvStat.fork)
    (steps : ∀ {d n d'}, P sevm d n d' → Ninst.Run sevm d n d')
    (observations : ∀ {d n d'}, P sevm d n d' → GuardObs K False sevm d n)
    (children : ∀ {d d' x xl}, P sevm d (.exec x) d' → xl.Filled →
      Xinst.Run sevm d x xl (.ok d') →
      ZeroSlots K sevm.currentTarget d → ZeroSlots K sevm.currentTarget d')
    (terminals : ∀ {d d' l}, Linst.Run sevm d l (.ok d') →
      ZeroSlots K sevm.currentTarget d → ZeroSlots K sevm.currentTarget d')
    (run : SProg.RunP P fs sevm pre post) (zero : ZeroSlots K sevm.currentTarget pre) :
    ZeroSlots K sevm.currentTarget post := by
  obtain ⟨f, _, actual⟩ := run
  exact runP_zero fork steps observations children terminals actual zero

end Blanc.Lift.WriteSite
