import Blanc.Lift.RequestSystem.Output

/-!
# What a request system frame touches and returns, in any context

`sysState_getElem_ne` and `sysState_getElem_congr` are the account-level facts behind non-interference: a
call's post state differs from its pre state only at its own address, and what it leaves there depends only
on what was there. `SysPath.frame_exec` is the frame walk as an execution, for any `Sevm` with the system
caller, not only the request phase's message. `SysOutput.drained_length` reads a drain's length from any
storage.
-/

namespace Blanc.Lift.RequestSystem

open Jaune

/-! ## Accounts -/

theorem setStorVal_getElem_congr {w w' : State} {a : Adr} (h : w[a]? = w'[a]?) (k v : B256) :
    (w.setStorVal a k v)[a]? = (w'.setStorVal a k v)[a]? := by
  have hget : w.get a = w'.get a := by
    rw [State.get_eq_getD, State.get_eq_getD, h]
  have hex : AccountExists w a ↔ AccountExists w' a := by
    simp only [AccountExists, h]
  unfold State.setStorVal
  dsimp only
  rw [hget]
  by_cases he : AccountExists w a
  · rw [ite_eq_left he, ite_eq_left (hex.mp he), State.getElem?_setPresent, State.getElem?_setPresent,
      ite_eq_left rfl, ite_eq_left rfl]
  · rw [ite_eq_right he, ite_eq_right (fun c => he (hex.mpr c)), State.getElem?_set, State.getElem?_set,
      ite_eq_left rfl, ite_eq_left rfl]

/-- A request system call leaves every other account exactly as it was, present or absent. -/
theorem sysState_getElem_ne (p : SysShape) (σ : State) {a x : Adr} (h : a ≠ x) :
    (sysState p σ a)[x]? = σ[x]? := by
  simp only [sysState]
  split <;> simp only [State.getElem?_setStorVal_ne _ h]

/-- What a request system call leaves at its own address depends only on what was there. -/
theorem sysState_getElem_congr (p : SysShape) {σ σ' : State} {a : Adr} (h : σ[a]? = σ'[a]?) :
    (sysState p σ a)[a]? = (sysState p σ' a)[a]? := by
  have hget : σ.get a = σ'.get a := by
    rw [State.get_eq_getD, State.get_eq_getD, h]
  have hstor : σ.getStor a = σ'.getStor a := congrArg Acct.stor hget
  simp only [sysState, hstor]
  have c := fun {w w' : State} (e : w[a]? = w'[a]?) k v => setStorVal_getElem_congr e k v
  split <;> exact c (c (by first | exact c (c h _ _) _ _ | exact c h _ _) _ _) _ _

theorem sysState_getStor_other (p : SysShape) (σ : State) {a x : Adr} (h : a ≠ x) :
    (sysState p σ a).getStor x = σ.getStor x := by
  have hget : (sysState p σ a).get x = σ.get x := by
    rw [State.get_eq_getD, State.get_eq_getD, sysState_getElem_ne p σ h]
  exact congrArg Acct.stor hget

/-! ## A fold of calls -/

/-- The state after a list of contracts' calls, one after another, with each address's shape from `shape`. -/
def sysFold (shape : Adr → SysShape) (l : List (UInt8 × Adr)) (σ : State) : State :=
  l.foldl (fun w e => sysState (shape e.2) w e.2) σ

theorem sysFold_cons (shape : Adr → SysShape) (e : UInt8 × Adr) (l : List (UInt8 × Adr)) (σ : State) :
    sysFold shape (e :: l) σ = sysFold shape l (sysState (shape e.2) σ e.2) := by
  simp only [sysFold, List.foldl_cons]

/-- `runRequestContracts` over any list whose calls all return `sysState` ends in `sysFold`, for `Inv` a property of
the state each call needs and keeps. -/
theorem run_sysFold (shape : Adr → SysShape) (Inv : State → Prop)
    (hinv : ∀ (w : State) (a : Adr), Inv w → Inv (sysState (shape a) w a))
    {L : List (UInt8 × Adr)}
    (hcall : ∀ (w : Benv), w.stat.fork = .amsterdam → Inv w.state → ∀ e ∈ L,
      ∃ out, processCheckedSystemTransaction w e.2 [] = .ok (sysState (shape e.2) w.state e.2, out))
    {l : List (UInt8 × Adr)} (hl : ∀ e ∈ l, e ∈ L) {benv : Benv} (hfork : benv.stat.fork = .amsterdam)
    (hi : Inv benv.state) (idx : Nat) (acc : List Bytes) (bal : BalBuilder) :
    ∃ acc' bal', runRequestContracts idx l benv acc bal = .ok (sysFold shape l benv.state, acc', bal') := by
  induction l generalizing benv acc bal with
  | nil => exact ⟨acc, bal, by simp only [runRequestContracts, sysFold, List.foldl_nil]⟩
  | cons e rest ih =>
    obtain ⟨ty, a⟩ := e
    obtain ⟨out, c⟩ : ∃ out, processCheckedSystemTransaction benv a [] =
        .ok (sysState (shape a) benv.state a, out) := hcall benv hfork hi (ty, a) (hl _ (List.mem_cons_self ..))
    have hi' := hinv benv.state a hi
    rw [runRequestContracts_step c, sysFold_cons]
    generalize sysState (shape a) benv.state a = X at hi' ⊢
    exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) (benv := benv.withState X) hfork hi' _ _

/-- An address's final account is its own call's result, wherever in the list that call falls, given the list's
addresses are distinct. -/
theorem sysFold_getElem (shape : Adr → SysShape) {l : List (UInt8 × Adr)} (hn : (l.map Prod.snd).Nodup)
    (σ : State) (x : Adr) :
    (sysFold shape l σ)[x]? = if x ∈ l.map Prod.snd then (sysState (shape x) σ x)[x]? else σ[x]? := by
  induction l generalizing σ with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    rw [sysFold_cons, ih hn.2]
    by_cases hx : x ∈ rest.map Prod.snd
    · have hne : e.2 ≠ x := fun eq => hn.1 (eq ▸ hx)
      rw [ite_eq_left hx, ite_eq_left (by simp only [List.map_cons, List.mem_cons]; exact Or.inr hx)]
      exact sysState_getElem_congr _ (sysState_getElem_ne _ _ hne)
    · rw [ite_eq_right hx]
      by_cases hex : e.2 = x
      · subst hex
        rw [ite_eq_left (by simp only [List.map_cons, List.mem_cons, true_or])]
      · rw [ite_eq_right (by simp only [List.map_cons, List.mem_cons, not_or]; exact ⟨fun c => hex c.symm, hx⟩)]
        exact sysState_getElem_ne _ _ hex

/-! ## The frame, in any context -/

namespace SysPath

/-- **The frame walk as an execution**, at any `Sevm` whose caller is the system address and at any base
that is `Ready`: nothing here requires the request phase's message. -/
theorem frame_exec (k : SysPath) {sevm : Sevm} {b : Devm} {G : Nat} (hcode : sevm.code = k.code)
    (hfork : sevm.benvStat.fork = .amsterdam) (hstatic : sevm.isStatic = false)
    (hcaller : sevm.caller = systemAddress) (hdata : sevm.data = [])
    (r : Ready sevm b [2, 3, 0, 1]) (hG : gCallStipend < G) :
    Nonempty (Exec 0 sevm (St b [] .empty (G + k.frameCost sevm b)) (.ok (k.framePost sevm b G))) :=
  lift_exact_noExec k.check k.jumps hcode k.noExec ⟨_, k.root, k.frame_run hfork hstatic hcaller hdata r hG⟩

end SysPath

namespace SysOutput

variable {k : SysPath} {m : SysMemory k} (o : SysOutput k m)

include o in
/-- A frame's return bytes depend only on the executing account's storage: any frame at `target` returns
what the checked system call on the same state returns. -/
theorem framePost_output_eq_callPost (sevm : Sevm) (b : Devm) (G : Nat) (benv : Benv) {target : Adr}
    (hstate : b.state = benv.state) (htarget : sevm.currentTarget = target) :
    (k.framePost sevm b G).output = (SysPath.callPost k benv target).output := by
  have hrd : SysPath.rd sevm b = fun key => (benv.state.getStor target).get key := by
    funext key
    rw [← htarget]
    exact SysPath.getStorVal_of_state hstate key
  rw [o.framePost_output, o.callPost_output]
  simp only [SysPath.count, hrd]

/-- One record's returned bytes, by length. -/
theorem record_length (rd : B256 → B256) (h : B256) {i : Nat} (hi : i < k.capN) :
    (o.record rd h i.toB256).length = m.lenN := by
  have e := congrArg List.length (o.extend rd h i [] hi)
  rw [List.length_append, List.length_sliceD, List.length_sliceD, Nat.mul_add, Nat.mul_one] at e
  omega

/-- The first `n` records' returned bytes, by length. -/
theorem drained_length (rd : B256 → B256) (h : B256) {n : Nat} (hn : n ≤ k.capN) :
    (o.drained rd h n).length = m.lenN * n := by
  induction n with
  | zero => simp only [drained, List.range_zero, List.flatMap_nil, List.length_nil, Nat.mul_zero]
  | succ n ih =>
    rw [drained_succ, List.length_append, ih (by omega), o.record_length rd h (by omega), Nat.mul_add,
      Nat.mul_one]

include o in
/-- **A call's return length, from any storage**: the record size times the records drained, with that
count at most the cap. -/
theorem callPost_output_length (benv : Benv) (target : Adr) :
    (SysPath.callPost k benv target).output.length =
        m.lenN * (drainCount k.shape.cap.word ((benv.state.getStor target).get 2)
          ((benv.state.getStor target).get 3)).toNat ∧
      (drainCount k.shape.cap.word ((benv.state.getStor target).get 2)
        ((benv.state.getStor target).get 3)).toNat ≤ k.capN := by
  have hle : (drainCount k.shape.cap.word ((benv.state.getStor target).get 2)
      ((benv.state.getStor target).get 3)).toNat ≤ k.capN := by
    rw [← k.cap_word]
    exact SysPath.drainCount_le _ _ _
  rw [o.callPost_output]
  exact ⟨o.drained_length _ _ hle, hle⟩

end SysOutput

end Blanc.Lift.RequestSystem
