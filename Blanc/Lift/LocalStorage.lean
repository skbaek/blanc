import Blanc.Lift.Quiet

/-!
# Storage-local synthetic trees

`SFunc.quiet` (`Quiet.lean`) excludes `SSTORE` and `LOG`, so it fits views only. A writer
whose only external call is `STATICCALL` may still store and log, but every `SSTORE` writes
the executing account and a static child cannot write storage anywhere. `SFunc.storLocal` is
that property (among the calls only `STATICCALL`, no `SELFDESTRUCT` terminal),
`StorLocalSet` its closure over entries, and `SFunc.Run.foreignStor_of_storLocal` the frame
theorem: a run keeps the complete storage of every account other than the executing one.

Nothing here mentions a contract.
-/

namespace Jaune

/-- A nonterminal instruction that can write storage only in the executing account: every
instruction except the calls and creations other than `STATICCALL`. -/
def Ninst.storLocal : Ninst → Bool
  | .exec x => x == .staticcall
  | _ => true

end Jaune

namespace Blanc.Lift

open Jaune

/-- A storage-local step keeps every foreign account's storage map. -/
theorem Ninst.foreignStor_of_storLocal {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (hfork : CoveredFork sevm.benvStat.fork) (hn : n.storLocal = true)
    (run : Ninst.Run sevm pre n post) {a : Adr} (foreign : sevm.currentTarget ≠ a) :
    Devm.getStor post a = Devm.getStor pre a := by
  cases n with
  | exec x =>
      have hx : x = .staticcall := by
        simpa only [Ninst.storLocal, beq_iff_eq] using hn
      subst hx
      exact (congrFun (Ninst.staticcall_inv_getStor_exact hfork run) a).symm
  | reg r =>
      rcases of_run_reg run with ⟨pc, rrun⟩
      by_cases store : r = .sstore
      · subst store
        exact sstore_preserves_getStor_ne rrun foreign
      · exact (congrFun (Rinst.preserves_stor store rrun) a).symm
  | push bytes bound =>
      exact congrFun (Ninst.world_of_quiet hfork rfl run).1 a
  | dupn imm =>
      exact congrFun (Ninst.world_of_quiet hfork rfl run).1 a
  | swapn imm =>
      exact congrFun (Ninst.world_of_quiet hfork rfl run).1 a
  | exchange imm =>
      exact congrFun (Ninst.world_of_quiet hfork rfl run).1 a

/-- A synthetic tree whose instructions are storage-local and whose terminals are not
`SELFDESTRUCT`. -/
def SFunc.storLocal : SFunc → Bool
  | .branch f g => f.storLocal && g.storLocal
  | .branchTo f _ => f.storLocal
  | .last l => l != .selfdestruct
  | .next n f => n.storLocal && f.storLocal
  | .dest f => f.storLocal
  | .jump _ => true
  | .callNext _ f => f.storLocal
  | .ret => true
  | .pcAt _ f => f.storLocal
  | .undefined => true

/-- `S` is closed under the entries referenced by its members, and all of them are
storage-local. -/
def StorLocalSet (fs : List SFunc) (S : List Nat) : Bool :=
  S.all fun k => match fs[k]? with
    | some g => g.storLocal && g.refs.all (· ∈ S)
    | none => false

/-- **The storage-local frame theorem**: a run of a storage-local tree whose gotos and calls
stay in a `StorLocalSet` keeps the storage map of every account other than the executing one. -/
theorem SFunc.Run.foreignStor_of_storLocal {fs : List SFunc} {S : List Nat}
    (hS : StorLocalSet fs S = true) {sevm : Sevm} (hfork : CoveredFork sevm.benvStat.fork)
    {devm : Devm} {f : SFunc} {o : Outcome}
    (hf : f.storLocal = true) (hrefs : f.refs.all (· ∈ S) = true)
    (run : SFunc.Run fs sevm devm f o) {a : Adr} (foreign : sevm.currentTarget ≠ a) :
    Devm.getStor (Outcome.devm o) a = Devm.getStor devm a := by
  have closed : ∀ {k g}, k ∈ S → fs[k]? = some g →
      g.storLocal = true ∧ g.refs.all (· ∈ S) = true := by
    intro k g hk hget
    have h := (List.all_eq_true.mp hS) k hk
    rw [hget] at h
    simpa only [Bool.and_eq_true] using h
  have pop : ∀ {ws : List B256} {x y : Devm}, Devm.PopBurn ws x y →
      Devm.getStor y a = Devm.getStor x a := fun h => congrFun (PopBurn.world h).1 a
  induction run with
  | zero d popped run ih =>
      simp only [SFunc.storLocal, Bool.and_eq_true] at hf
      simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at hrefs
      exact (ih hf.1 hrefs.1).trans (pop popped)
  | succ d w hnz popped run ih =>
      simp only [SFunc.storLocal, Bool.and_eq_true] at hf
      simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at hrefs
      exact (ih hf.2 hrefs.2).trans (pop popped)
  | toZero d popped run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      exact (ih hf hrefs.2).trans (pop popped)
  | toSucc d w hnz lookup popped run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have ht := closed (of_decide_eq_true hrefs.1) lookup
      exact (ih ht.1 ht.2).trans (pop popped)
  | @last _ _ l hrun =>
      have terminal : l ≠ Linst.selfdestruct := by
        simpa only [SFunc.storLocal, bne_iff_ne, ne_eq] using hf
      exact congrFun (Linst.world_of_ok terminal hrun).1 a
  | next hrun run ih =>
      simp only [SFunc.storLocal, Bool.and_eq_true] at hf
      exact (ih hf.2 hrefs).trans (Ninst.foreignStor_of_storLocal hfork hf.1 hrun foreign)
  | dest burn run ih =>
      exact (ih hf hrefs).trans (congrFun (Burn.world burn).1 a)
  | jump d lookup popped run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have ht := closed (of_decide_eq_true hrefs.1) lookup
      exact (ih ht.1 ht.2).trans (pop popped)
  | ret d popped =>
      exact pop popped
  | callHalt d lookup popped run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have ht := closed (of_decide_eq_true hrefs.1) lookup
      exact (ih ht.1 ht.2).trans (pop popped)
  | callRet d lookup popped run tail ihRun ihTail =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have ht := closed (of_decide_eq_true hrefs.1) lookup
      simp only [SFunc.storLocal] at hf
      exact (ihTail hf hrefs.2).trans ((ihRun ht.1 ht.2).trans (pop popped))
  | pcAt hrun _ run ih =>
      simp only [SFunc.storLocal] at hf
      simp only [SFunc.refs] at hrefs
      exact (ih hf hrefs).trans
        (congrFun (Ninst.world_of_quiet (n := .reg .pc) hfork rfl hrun).1 a)

end Blanc.Lift
