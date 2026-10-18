import Blanc.Lift.WriteSiteJoin
import Blanc.Lift.WriteSiteObs
import Blanc.Lift.FreePtrSound

/-!
# W4: soundness of the write-site checker

Goal `usdc-neversigner-freepointer-v1`, design `ws-checker.md` §6 row W4.  The big-step
induction (`ws_run`) over `SFunc.RunP`: the checker state holds of the machine (`WSt.Sat`) above
an untouched base, steps go through `wstep_sound`, branch arms through `refine_sound`, gotos
through `popped_sound`/`compat_sat`, returns through `retOk_sound`, callee entries through
`param_sat`, callee sites through `callNext_obs` and call continuations through `resume_sound`.
A callee runs in its own environment (`Env.callee`, its entry words); its steps are re-read in the
caller's through the call's site coverage.  A `callNext` whose callee frame holds no return marker
leaves its continuation unchecked; such a callee never returns
(`SFunc.RunP.not_returned_of_noRet`).  Bytes-free and contract-neutral.
-/

namespace Blanc.Lift.WriteSite

open Jaune AbstractStackSafety Blanc.Lift.SymTransfer
open Blanc.Lift.FreePtr (cert_at gotoCompat_length transfer_length_mono mapM_length foldTop_length)

/-! ## The certificate's entries -/

theorem wsCert_at {c : Cert} {ann : List WAnn} (hw : wsCert c ann = true) {k : Nat} {e : Entry}
    {g : SFunc} (hk : c[k]? = some (e, g)) :
    ∃ A, ann[k]? = some A ∧ wsNode c.entries ann A.ret e.frame A.entry g = true := by
  simp only [wsCert, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hw
  obtain ⟨⟨hlen, -⟩, hall⟩ := hw
  have hkc : k < c.length := (List.getElem?_eq_some_iff.mp hk).1
  have hka : k < ann.length := hlen ▸ hkc
  refine ⟨ann[k], List.getElem?_eq_getElem hka, ?_⟩
  have hmem : ((e, g), ann[k]) ∈ c.zip ann := by
    rw [List.mem_iff_getElem?]
    refine ⟨k, ?_⟩
    rw [List.getElem?_zip_eq_some]
    exact ⟨hk, List.getElem?_eq_getElem hka⟩
  exact hall _ hmem

/-! ## Inverting the walk's arms -/

section Inv

variable {es : List Entry} {ann : List WAnn} {R : WRet} {σ : WSt} {a : List AVal}

theorem wsNode_branch_inv {f g : SFunc} (h : wsNode es ann R a σ (.branch f g) = true) :
    ∃ x y a' x' c kv, a = x :: y :: a' ∧ σ.kv = x' :: c :: kv ∧
      wsNode es ann R a' (refine σ c kv true) f = true ∧
      wsNode es ann R a' (refine σ c kv false) g = true := by
  simp only [wsNode] at h
  split at h
  · simp only [Bool.and_eq_true] at h
    exact ⟨_, _, _, _, _, _, rfl, ‹_›, h.1, h.2⟩
  · cases h

theorem wsNode_branchTo_inv {f : SFunc} {k : Nat}
    (h : wsNode es ann R a σ (.branchTo f k) = true) :
    ∃ x y a' x' c kv e A, a = x :: y :: a' ∧ σ.kv = x' :: c :: kv ∧ es[k]? = some e ∧
      ann[k]? = some A ∧ gotoCompat a' e.frame = true ∧
      wsNode es ann R a' (refine σ c kv true) f = true ∧
      gotoOk e (refine σ c kv false) A = true ∧ retLe A.ret R = true := by
  simp only [wsNode] at h
  split at h
  · simp only [Bool.and_eq_true] at h
    exact ⟨_, _, _, _, _, _, _, _, rfl, ‹_›, ‹_›, ‹_›, h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  · cases h

theorem wsNode_jump_inv {k : Nat} (h : wsNode es ann R a σ (.jump k) = true) :
    ∃ x a' x' kv e A, a = x :: a' ∧ σ.kv = x' :: kv ∧ es[k]? = some e ∧ ann[k]? = some A ∧
      gotoCompat a' e.frame = true ∧ gotoOk e (popped σ kv) A = true ∧ retLe A.ret R = true := by
  simp only [wsNode] at h
  split at h
  · simp only [Bool.and_eq_true] at h
    exact ⟨_, _, _, _, _, _, rfl, ‹_›, ‹_›, ‹_›, h.1.1, h.1.2, h.2⟩
  · cases h

theorem wsNode_ret_inv (h : wsNode es ann R a σ .ret = true) :
    ∃ a' x' kv, a = .ret :: a' ∧ σ.kv = x' :: kv ∧ retOk σ kv R = true := by
  simp only [wsNode] at h
  split at h
  · exact ⟨_, _, _, rfl, ‹_›, h⟩
  · cases h

theorem wsNode_next_inv {n : Ninst} {f : SFunc} (h : wsNode es ann R a σ (.next n f) = true) :
    ∃ a' σ', absNinst n a = some a' ∧ wstep R n σ = some σ' ∧ wsNode es ann R a' σ' f = true := by
  simp only [wsNode] at h
  split at h
  · exact ⟨_, _, ‹_›, ‹_›, h⟩
  · cases h

theorem wsNode_callNext_inv {k : Nat} {f : SFunc}
    (h : wsNode es ann R a σ (.callNext k f) = true) :
    ∃ t a' x' kv e A, a = .const t :: a' ∧ σ.kv = x' :: kv ∧ es[k]? = some e ∧
      ann[k]? = some A ∧ e.frame.length ≤ kv.length ∧ A.entry = WSt.param e.frame.length ∧
      A.ret.prov.length = e.rets ∧
      (R.keeps = true → A.ret.keeps = true) ∧
      A.ret.sites.all (fun s => R.sites.any
        (·.covers (instSite ((kv.take e.frame.length).map σ.provOf) σ.guards s))) = true ∧
      ∀ i, e.frame.findIdx? (· == .ret) = some i →
        wsNode es ann R (List.replicate e.rets .unk ++ a'.drop e.frame.length)
          (resume σ (kv.take e.frame.length) (kv.drop e.frame.length) A.ret e.rets) f = true := by
  simp only [wsNode] at h
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
    refine ⟨_, _, _, _, _, _, rfl, ‹_›, ‹_›, ‹_›, h0, h1, h2, fun hk => ?_, h4, fun i hi => ?_⟩
    · rw [hk] at h3
      simpa only [Bool.not_true, Bool.false_or] using h3
    · rw [hi] at h5
      simp only at h5
      split at h5
      · exact h5
      · cases h5
  · cases h

end Inv

/-- The write-site walk has `checkNode`'s return discipline. -/
theorem wsNode_retClosed {c : Cert} {ann : List WAnn} (hw : wsCert c ann = true) :
    RetClosed c.entries c.prog (fun a f => ∃ R σ, wsNode c.entries ann R a σ f = true) where
  entry he hg := by
    obtain ⟨A, -, h⟩ := wsCert_at hw (cert_at he hg)
    exact ⟨_, _, h⟩
  next := by
    rintro a n f ⟨R, σ, h⟩
    obtain ⟨a', σ', ha, -, h⟩ := wsNode_next_inv h
    exact ⟨a', ha, R, σ', h⟩
  dest := by
    rintro a f ⟨R, σ, h⟩
    exact ⟨R, σ, h⟩
  branch := by
    rintro a f g ⟨R, σ, h⟩
    obtain ⟨x, y, a', -, c, kv, rfl, -, h1, h2⟩ := wsNode_branch_inv h
    exact ⟨x, y, a', rfl, ⟨R, _, h1⟩, ⟨R, _, h2⟩⟩
  branchTo := by
    rintro a f k ⟨R, σ, h⟩
    obtain ⟨x, y, a', -, c, kv, e, A, rfl, -, he, -, hg, h1, -⟩ := wsNode_branchTo_inv h
    exact ⟨x, y, a', e, rfl, he, hg, R, _, h1⟩
  jump := by
    rintro a k ⟨R, σ, h⟩
    obtain ⟨x, a', -, kv, e, A, rfl, -, he, -, hg, -⟩ := wsNode_jump_inv h
    exact ⟨x, a', e, rfl, he, hg⟩
  callNext := by
    rintro a k f ⟨R, σ, h⟩
    obtain ⟨t, a', -, kv, e, A, rfl, -, he, -, -, -, -, -, -, hk⟩ := wsNode_callNext_inv h
    exact ⟨_, a', e, rfl, he, fun i hi => ⟨R, _, hk i hi⟩⟩
  ret := by
    rintro a ⟨R, σ, h⟩
    obtain ⟨a', -, -, rfl, -⟩ := wsNode_ret_inv h
    exact ⟨a', rfl⟩
  pcAt := by
    rintro a p f ⟨R, σ, h⟩
    simp only [wsNode] at h
    cases h

/-! ## Machine facts the induction needs -/

theorem popBurn_getStor {xs : List B256} {d d' : Devm} (hp : Devm.PopBurn xs d d') (a : Adr) :
    Devm.getStor d' a = Devm.getStor d a := by
  show (d'.state.get a).stor = (d.state.get a).stor
  rw [hp.state]

theorem burn_getStor {d d' : Devm} (burn : Devm.Burn d d') (a : Adr) :
    Devm.getStor d' a = Devm.getStor d a := by
  show (d'.state.get a).stor = (d.state.get a).stor
  rw [burn.state]

theorem WSt.Sat.burn {ε : Env} {sevm : Sevm} {σ : WSt} {d d' : Devm} {rest : List B256}
    (burn : Devm.Burn d d') (h : σ.Sat ε sevm d rest) : σ.Sat ε sevm d' rest := by
  obtain ⟨ν, S, hS, h⟩ := h
  exact ⟨ν, S, by rw [← burn.stack]; exact hS, h.of_keep (.of_eq burn.memory) (burn_getStor burn _)⟩

/-- A `PUSH` that runs finds room on the stack. -/
theorem push_stack_lt {sevm : Sevm} {d d' : Devm} {bs : Bytes} {fits : bs.length ≤ 32}
    (run : Ninst.Run sevm d (.push bs fits) d') : d.stack.length < 1024 := by
  have h := Ninst.run_push_eq run
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i d1 hc
  have hs : d1.stack = d.stack := by
    simp only [chargeGas_def] at hc
    split at hc
    · cases hc
    · rename_i gas _
      injection hc with e
      subst e
      rfl
  rw [Devm.push_def] at h
  simp only [Except.assert, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i hif
    rw [← hs]
    by_contra hn
    simp only [hn, ↓reduceIte, reduceCtorEq] at hif

/-- **The checker frame never outgrows the abstract stack**, and stays within the stack limit
for a step `wstep_sound` accepts. -/
theorem wstep_length {R : WRet} {n : Ninst} {σ σ' : WSt} {a a' : List AVal} {sevm : Sevm}
    {d d' : Devm} {S rest : List B256} (hw : wstep R n σ = some σ') (ha : absNinst n a = some a')
    (hlen : σ.kv.length ≤ a.length) (hS : d.stack = S ++ rest) (hSl : S.length = σ.kv.length)
    (run : Ninst.Run sevm d n d') : σ.kv.length ≤ 1024 ∧ σ'.kv.length ≤ a'.length := by
  by_cases hpush : ∃ bs fits, n = .push bs fits
  · obtain ⟨bs, fits, rfl⟩ := hpush
    simp only [wstep, Option.some.injEq] at hw
    simp only [absNinst, Option.some.injEq] at ha
    subst hw ha
    have hlt := push_stack_lt run
    rw [hS, List.length_append, hSl] at hlt
    refine ⟨by omega, ?_⟩
    show σ.kv.length + 1 ≤ a.length + 1
    omega
  · have hn : ∀ bs fits, n ≠ .push bs fits := fun bs fits he => hpush ⟨bs, fits, he⟩
    obtain ⟨hlenA, outA, a0, hA, hr0, rfl⟩ := absNinst_nonpush_spec hn ha
    obtain ⟨out, kv', -, -, -, -, ho, -, -, -, hm, rfl, -⟩ := wstep_nonpush hn hw
    refine ⟨le_trans hlen hlenA, ?_⟩
    show kv'.length ≤ _
    rw [mapM_length hm, foldTop_length, mapM_length hr0]
    exact transfer_length_mono ho hA hlen

/-- A keeping summary's accepted step keeps the executing account's storage. -/
theorem wstep_keeps {R : WRet} {n : Ninst} {σ σ' : WSt} {sevm : Sevm} {d d' : Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (hw : wstep R n σ = some σ') (hk : R.keeps = true)
    (run : Ninst.Run sevm d n d') : Devm.getStor d' = Devm.getStor d := by
  by_cases hpush : ∃ bs fits, n = .push bs fits
  · obtain ⟨bs, fits, rfl⟩ := hpush
    exact Ninst.Run.getStor_push run
  · have hn : ∀ bs fits, n ≠ .push bs fits := fun bs fits he => hpush ⟨bs, fits, he⟩
    obtain ⟨out, -, -, -, -, -, ho, -, hkeep, -⟩ := wstep_nonpush hn hw
    rw [hk, Bool.true_and] at hkeep
    exact getStor_of_writesStor hfork ho hkeep run

/-- A run under a step relation is a run under any relation it implies at the run's frame. -/
theorem _root_.Blanc.Lift.SFunc.RunP.mono_at {P Q : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc}
    {sevm : Sevm} (hPQ : ∀ {d n d'}, P sevm d n d' → Q sevm d n d') {devm : Devm} {f : SFunc}
    {o : Outcome} (run : SFunc.RunP P fs sevm devm f o) : SFunc.RunP Q fs sevm devm f o := by
  induction run with
  | zero d pop _ ih => exact .zero d pop ih
  | succ d w hnz pop _ ih => exact .succ d w hnz pop ih
  | toZero d pop _ ih => exact .toZero d pop ih
  | toSucc d w hnz lookup pop _ ih => exact .toSucc d w hnz lookup pop ih
  | last h => exact .last h
  | next h _ ih => exact .next (hPQ h) ih
  | dest burn _ ih => exact .dest burn ih
  | jump d lookup pop _ ih => exact .jump d lookup pop ih
  | ret d pop => exact .ret d pop
  | callHalt d lookup pop _ ih => exact .callHalt d lookup pop ih
  | callRet d lookup pop _ _ ihRun ihTail => exact .callRet d lookup pop ihRun ihTail
  | pcAt h hpc _ ih => exact .pcAt (hPQ h) hpc ih

theorem compat_kv_length {σ A : WSt} (h : compat σ A = true) : σ.kv.length = A.kv.length := by
  unfold compat at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.1.1.1.1.1.1

/-- **A callee's entry**: after the destination pop, the callee's frame words are the caller's
named words below the destination, and the callee's parameter state holds of them in the callee's
environment. -/
theorem call_entry {ε : Env} {sevm : Sevm} {ν : Nat → B256} {σ : WSt} {S rest : List B256}
    {d d' : Devm} {x' : Nat} {kv : List Nat} {dw : B256} {n : Nat}
    (h : σ.Holds ε sevm ν S d) (hS : d.stack = S ++ rest) (hkv : σ.kv = x' :: kv)
    (pop : Devm.PopBurn [dw] d d') (hn : n ≤ kv.length) :
    (WSt.param n).Sat (ε.callee ((kv.take n).map ν)) sevm d' ((kv.drop n).map ν ++ rest) := by
  have h1 := popBurn_stack pop
  rw [hS, forall₂_eq_map h.kv, hkv] at h1
  simp only [List.map_cons, List.cons_append, List.nil_append, List.cons.injEq] at h1
  have hd : d'.stack = (kv.take n).map ν ++ ((kv.drop n).map ν ++ rest) := by
    rw [← h1.2, ← List.append_assoc, ← List.map_append, List.take_append_drop]
  have hW : ((kv.take n).map ν).length = n := by
    rw [List.length_map, List.length_take]
    exact Nat.min_eq_left hn
  have := param_sat (ε := ε) (sevm := sevm) hd
  rwa [hW] at this

/-- A callee's steps, observed against its summary in its environment, are observed against the
caller's summary in the caller's environment, through the call's site coverage. -/
theorem callee_steps {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {ε : Env}
    {sevm : Sevm} {ν : Nat → B256} {σ : WSt} {S : List B256} {d d₀ : Devm} {g : SFunc}
    {o : Outcome} {A R : WRet} {cw : List Nat} (h : σ.Holds ε sevm ν S d)
    (hall : A.sites.all (fun s => R.sites.any (·.covers (instSite (cw.map σ.provOf) σ.guards s))) =
      true)
    (run : SFunc.RunP (WsStep A.sites (ε.callee (cw.map ν)) P) fs sevm d₀ g o) :
    SFunc.RunP (WsStep R.sites ε P) fs sevm d₀ g o :=
  run.mono_at fun ⟨hp, hobs⟩ =>
    ⟨hp, fun hn x v rs hs => callNext_obs h hall (hobs hn x v rs hs)⟩

theorem param_kv_length (n : Nat) : (WSt.param n).kv.length = n := by
  show ((List.range n).map (· + 1)).length = n
  rw [List.length_map, List.length_range]

/-! ## Gotos: summaries below the jumper's, and tail calls -/

/-- An entry-word-free term reads the same in two environments of one frame. -/
theorem Term.eval_argFree {ε ε' : Env} (hc : ε'.caller = ε.caller) (hs : ε'.self = ε.self)
    (hd : ε'.data = ε.data) : ∀ {t : Term}, t.argFree = true → t.eval ε' = t.eval ε
  | .top, _ => rfl
  | .caller, _ => hc
  | .self, _ => hs
  | .const _, _ => rfl
  | .arg _, h => by cases h
  | .cd t, h => by
    simp only [Term.argFree] at h
    simp only [Term.eval]
    rw [Term.eval_argFree hc hs hd h, hd]
  | .op2 o a b, h => by
    simp only [Term.argFree, Bool.and_eq_true] at h
    simp only [Term.eval]
    rw [Term.eval_argFree hc hs hd h.1, Term.eval_argFree hc hs hd h.2]
  | .kecc a b, h => by
    simp only [Term.argFree, Bool.and_eq_true] at h
    simp only [Term.eval]
    rw [Term.eval_argFree hc hs hd h.1, Term.eval_argFree hc hs hd h.2]
  | .kecc1 t, h => by
    simp only [Term.argFree] at h
    simp only [Term.eval]
    rw [Term.eval_argFree hc hs hd h]

theorem Term.den_callee {ε : Env} {W : List B256} {t : Term} {w : B256} (ht : t.argFree = true)
    (h : t.Den (ε.callee W) w) : t.Den ε w := fun hk => by
  rw [h hk]
  exact Term.eval_argFree (ε := ε) (ε' := ε.callee W) rfl rfl rfl ht

/-- A tail call's steps, observed against an entry-word-free summary in the callee environment,
are observed against it in the caller's. -/
theorem argFree_steps {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {ε : Env}
    {W : List B256} {sevm : Sevm} {d₀ : Devm} {g : SFunc} {o : Outcome} {A : WRet}
    (hA : A.argFree = true) (run : SFunc.RunP (WsStep A.sites (ε.callee W) P) fs sevm d₀ g o) :
    SFunc.RunP (WsStep A.sites ε P) fs sevm d₀ g o := by
  simp only [WRet.argFree, Bool.and_eq_true, List.all_eq_true] at hA
  refine run.mono_at fun ⟨hp, hobs⟩ => ⟨hp, fun hn x v rs hst => ?_⟩
  obtain ⟨s, hs, hslot, hg, hni⟩ := hobs hn x v rs hst
  obtain ⟨hsl, hgs⟩ := hA.2 s hs
  exact ⟨s, hs, Term.den_callee hsl hslot,
    fun g' hm => Term.den_callee (hgs g' hm) (hg g' hm), hni⟩

/-- Steps observed against a goto target's summary are observed against the jumper's. -/
theorem retLe_steps {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {ε : Env}
    {sevm : Sevm} {d₀ : Devm} {g : SFunc} {o : Outcome} {A R : WRet} (hle : retLe A R = true)
    (run : SFunc.RunP (WsStep A.sites ε P) fs sevm d₀ g o) :
    SFunc.RunP (WsStep R.sites ε P) fs sevm d₀ g o := by
  simp only [retLe, Bool.and_eq_true, List.all_eq_true] at hle
  exact run.mono_at fun ⟨hp, hobs⟩ => ⟨hp, fun hn x v rs hs => by
    obtain ⟨s, hs', ho⟩ := hobs hn x v rs hs
    exact Site.Obs.of_any (hle.2 s hs') ho⟩

/-! ## The big-step induction -/

/-- What a return establishes: the returned words above the untouched base meet the summary,
and a keeping summary left the executing account's storage as it was at `d`. -/
def RetObs (ε : Env) (sevm : Sevm) (R : WRet) (rest : List B256) (d d'' : Devm) : Prop :=
  (∃ Wr, d''.stack = Wr ++ rest ∧ R.Holds ε Wr) ∧
    (R.keeps = true → Devm.getStor d'' sevm.currentTarget = Devm.getStor d sevm.currentTarget)

/-- A return meeting a goto target's summary meets the jumper's. -/
theorem RetObs.of_retLe {ε : Env} {sevm : Sevm} {A R : WRet} {rest : List B256} {d d'' : Devm}
    (hle : retLe A R = true) (h : RetObs ε sevm A rest d d'') : RetObs ε sevm R rest d d'' := by
  simp only [retLe, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at hle
  obtain ⟨⟨⟨hp, hl⟩, hk⟩, -⟩ := hle
  obtain ⟨⟨Wr, hd, hR⟩, hst⟩ := h
  refine ⟨⟨Wr, hd, ?_⟩, fun hkR => hst ?_⟩
  · unfold WRet.Holds at hR ⊢
    rw [← hp, ← hl]
    exact hR
  · rcases hk with hk | hk
    · rw [hk] at hkR; cases hkR
    · exact hk

/-- A return meeting an entry-word-free summary in the callee environment meets it in the
caller's. -/
theorem RetObs.of_callee {ε : Env} {W : List B256} {sevm : Sevm} {A : WRet} {rest : List B256}
    {d d'' : Devm} (hA : A.argFree = true) (h : RetObs (ε.callee W) sevm A rest d d'') :
    RetObs ε sevm A rest d d'' := by
  simp only [WRet.argFree, Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff] at hA
  obtain ⟨⟨Wr, hd, hl, hprov, -⟩, hst⟩ := h
  refine ⟨⟨Wr, hd, hl, fun j t w ht hw => Term.den_callee (hA.1.2 t (List.mem_of_getElem? ht))
    (hprov j t w ht hw), ?_⟩, hst⟩
  rw [hA.1.1]
  intro p hp
  cases hp

/-- **A tail call's entry**: a state of exactly `n` frame words above `rest` makes the callee's
parameter state hold in the callee environment of those words. -/
theorem tail_entry {ε : Env} {sevm : Sevm} {σ : WSt} {d : Devm} {rest : List B256} {n : Nat}
    (h : σ.Sat ε sevm d rest) (hn : σ.kv.length = n) :
    ∃ W, (WSt.param n).Sat (ε.callee W) sevm d rest := by
  obtain ⟨ν, S, hS, hh⟩ := h
  have hl : S.length = n := by rw [← hn]; exact (List.Forall₂.length_eq hh.kv).symm
  refine ⟨S, ?_⟩
  have := param_sat (ε := ε) (sevm := sevm) hS
  rwa [hl] at this

/-- **An accepted goto is sound**: the target's walk, run from the goto's state, observes the
jumper's summary and returns meeting it. -/
theorem goto_run {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {ε : Env}
    {sevm : Sevm} {d₀ : Devm} {g : SFunc} {o : Outcome} {e : Entry} {σ : WSt} {A : WAnn}
    {R : WRet} {rest : List B256} (hgo : gotoOk e σ A = true) (hle : retLe A.ret R = true)
    (sat : σ.Sat ε sevm d₀ rest)
    (ih : ∀ {ε' : Env}, ε'.caller = ε.caller → ε'.self = ε.self → ε'.data = ε.data →
      A.entry.Sat ε' sevm d₀ rest →
      SFunc.RunP (WsStep A.ret.sites ε' P) fs sevm d₀ g o ∧
        ∀ d'', o = .returned d'' → RetObs ε' sevm A.ret rest d₀ d'') :
    SFunc.RunP (WsStep R.sites ε P) fs sevm d₀ g o ∧
      ∀ d'', o = .returned d'' → RetObs ε sevm R rest d₀ d'' := by
  unfold gotoOk at hgo
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hgo
  rcases hgo with hc | ⟨⟨hA, hent⟩, hn⟩
  · obtain ⟨r1, r2⟩ := ih rfl rfl rfl (compat_sat hc sat)
    exact ⟨retLe_steps hle r1, fun d'' ho => (r2 d'' ho).of_retLe hle⟩
  · obtain ⟨W, sat'⟩ := tail_entry sat hn
    rw [← hent] at sat'
    obtain ⟨r1, r2⟩ := ih (ε' := ε.callee W) rfl rfl rfl sat'
    exact ⟨retLe_steps hle (argFree_steps hA r1),
      fun d'' ho => ((r2 d'' ho).of_callee hA).of_retLe hle⟩

theorem gotoOk_len {e : Entry} {σ : WSt} {A : WAnn} (h : gotoOk e σ A = true)
    (hl : σ.kv.length ≤ e.frame.length) : A.entry.kv.length ≤ e.frame.length := by
  unfold gotoOk at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with hc | ⟨⟨-, hent⟩, -⟩
  · rw [← compat_kv_length hc]; exact hl
  · rw [hent, param_kv_length]

theorem RetObs.stor {ε : Env} {sevm : Sevm} {R : WRet} {rest : List B256} {d d' d'' : Devm}
    (h : RetObs ε sevm R rest d' d'')
    (hs : R.keeps = true →
      Devm.getStor d' sevm.currentTarget = Devm.getStor d sevm.currentTarget) :
    RetObs ε sevm R rest d d'' :=
  ⟨h.1, fun hk => (h.2 hk).trans (hs hk)⟩

/-- **The recursion.**  A run of a tree the walk accepts under summary `R`, from a machine the
walk's state describes in the environment `ε` of the frame, is a run under `WsStep R.sites ε`;
if it returns, the summary holds of the result above the same untouched base. -/
theorem ws_run {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {c : Cert} {ann : List WAnn} (hw : wsCert c ann = true)
    {sevm : Sevm} (hfork : CoveredFork sevm.benvStat.fork) {d : Devm} {f : SFunc} {o : Outcome}
    (run : SFunc.RunP P c.prog sevm d f o) :
    ∀ {a : List AVal} {σ : WSt} {R : WRet} {ε : Env} {rest : List B256},
      wsNode c.entries ann R a σ f = true → σ.kv.length ≤ a.length → ε.Frame sevm →
      σ.Sat ε sevm d rest →
      SFunc.RunP (WsStep R.sites ε P) c.prog sevm d f o ∧
        ∀ d'', o = .returned d'' → RetObs ε sevm R rest d d'' := by
  induction run with
  | zero dw pop _ ih =>
    intro a σ R ε rest hn hlen hε ⟨ν, S, hS, h⟩
    obtain ⟨x, y, a', x', c', kv, rfl, hkv, h1, -⟩ := wsNode_branch_inv hn
    have hl : kv.length ≤ a'.length := by
      rw [hkv] at hlen; simp only [List.length_cons] at hlen; omega
    obtain ⟨r1, r2⟩ := ih h1 hl hε
      (refine_sound h hS hkv pop (fun _ => rfl) (fun h => by cases h))
    exact ⟨.zero dw pop r1, fun d'' ho => (r2 d'' ho).stor fun _ => popBurn_getStor pop _⟩
  | succ dw w hw pop _ ih =>
    intro a σ R ε rest hn hlen hε ⟨ν, S, hS, h⟩
    obtain ⟨x, y, a', x', c', kv, rfl, hkv, -, h2⟩ := wsNode_branch_inv hn
    have hl : kv.length ≤ a'.length := by
      rw [hkv] at hlen; simp only [List.length_cons] at hlen; omega
    obtain ⟨r1, r2⟩ := ih h2 hl hε
      (refine_sound h hS hkv pop (fun h => by cases h) (fun _ => hw))
    exact ⟨.succ dw w hw pop r1, fun d'' ho => (r2 d'' ho).stor fun _ => popBurn_getStor pop _⟩
  | toZero dw pop _ ih =>
    intro a σ R ε rest hn hlen hε ⟨ν, S, hS, h⟩
    obtain ⟨x, y, a', x', c', kv, e, A, rfl, hkv, -, -, -, h1, -, -⟩ := wsNode_branchTo_inv hn
    have hl : kv.length ≤ a'.length := by
      rw [hkv] at hlen; simp only [List.length_cons] at hlen; omega
    obtain ⟨r1, r2⟩ := ih h1 hl hε
      (refine_sound h hS hkv pop (fun _ => rfl) (fun h => by cases h))
    exact ⟨.toZero dw pop r1, fun d'' ho => (r2 d'' ho).stor fun _ => popBurn_getStor pop _⟩
  | toSucc dw w hnz hk pop _ ih =>
    intro a σ R ε rest hn hlen hε ⟨ν, S, hS, h⟩
    obtain ⟨x, y, a', x', c', kv, e, A, rfl, hkv, he, hA, hgo, -, hcA, hR⟩ :=
      wsNode_branchTo_inv hn
    obtain ⟨A', hA', hnode⟩ := wsCert_at hw (cert_at he hk)
    rw [hA] at hA'
    cases hA'
    have hl : A.entry.kv.length ≤ e.frame.length := by
      refine gotoOk_len hcA ?_
      rw [← gotoCompat_length hgo]
      rw [hkv] at hlen; simp only [List.length_cons] at hlen
      show kv.length ≤ _
      omega
    obtain ⟨r1, r2⟩ := goto_run hcA hR
      (refine_sound h hS hkv pop (fun h => by cases h) (fun _ => hnz))
      (fun hc hs hd sat => ih hnode hl ⟨hc.trans hε.1, hs.trans hε.2.1, hd.trans hε.2.2⟩ sat)
    exact ⟨.toSucc dw w hnz hk pop r1, fun d'' ho => (r2 d'' ho).stor fun _ => popBurn_getStor pop _⟩
  | last h =>
    intro a σ R ε rest _ _ _ _
    exact ⟨.last h, fun _ ho => by cases ho⟩
  | next h _ ih =>
    intro a σ R ε rest hn hlen hε ⟨ν, S, hS, hh⟩
    obtain ⟨a', σ', ha, hs, hn'⟩ := wsNode_next_inv hn
    have hrun := hP h
    obtain ⟨hl1024, hl⟩ := wstep_length hs ha hlen hS (List.Forall₂.length_eq hh.kv).symm hrun
    obtain ⟨sat', hobs, -⟩ := wstep_sound hfork hε hh hS hl1024 hs hrun
    obtain ⟨r1, r2⟩ := ih hn' hl hε sat'
    exact ⟨.next ⟨h, hobs⟩ r1, fun d'' ho => (r2 d'' ho).stor fun hk =>
      congrFun (wstep_keeps hfork hs hk hrun) _⟩
  | dest burn _ ih =>
    intro a σ R ε rest hn hlen hε sat
    obtain ⟨r1, r2⟩ := ih hn hlen hε (sat.burn burn)
    exact ⟨.dest burn r1, fun d'' ho => (r2 d'' ho).stor fun _ => burn_getStor burn _⟩
  | jump dw hk pop _ ih =>
    intro a σ R ε rest hn hlen hε ⟨ν, S, hS, h⟩
    obtain ⟨x, a', x', kv, e, A, rfl, hkv, he, hA, hgo, hcA, hR⟩ := wsNode_jump_inv hn
    obtain ⟨A', hA', hnode⟩ := wsCert_at hw (cert_at he hk)
    rw [hA] at hA'
    cases hA'
    have hl : A.entry.kv.length ≤ e.frame.length := by
      refine gotoOk_len hcA ?_
      rw [← gotoCompat_length hgo]
      rw [hkv] at hlen; simp only [List.length_cons] at hlen
      show kv.length ≤ _
      omega
    obtain ⟨r1, r2⟩ := goto_run hcA hR (popped_sound h hS hkv pop)
      (fun hc hs hd sat => ih hnode hl ⟨hc.trans hε.1, hs.trans hε.2.1, hd.trans hε.2.2⟩ sat)
    exact ⟨.jump dw hk pop r1, fun d'' ho => (r2 d'' ho).stor fun _ => popBurn_getStor pop _⟩
  | ret dw pop =>
    intro a σ R ε rest hn hlen hε ⟨ν, S, hS, h⟩
    obtain ⟨a', x', kv, rfl, hkv, hr⟩ := wsNode_ret_inv hn
    obtain ⟨hst, hR⟩ := retOk_sound h hS hkv pop hr
    refine ⟨.ret dw pop, fun d'' ho => ?_⟩
    cases ho
    exact ⟨⟨_, hst, hR⟩, fun _ => popBurn_getStor pop _⟩
  | callHalt dw hk pop runC ih =>
    intro a σ R ε rest hn hlen hε ⟨ν, S, hS, h⟩
    obtain ⟨t, a', x', kv, e, A, rfl, hkv, he, hA, hdp, hent, -, -, hall, -⟩ :=
      wsNode_callNext_inv hn
    obtain ⟨A', hA', hnode⟩ := wsCert_at hw (cert_at he hk)
    rw [hA] at hA'
    cases hA'
    have sat := call_entry h hS hkv pop hdp
    rw [← hent] at sat
    have hl : A.entry.kv.length ≤ e.frame.length := by rw [hent, param_kv_length]
    obtain ⟨r1, -⟩ := ih hnode hl hε.callee sat
    exact ⟨.callHalt dw hk pop (callee_steps h hall r1), fun _ ho => by cases ho⟩
  | callRet dw hk pop runC _ ihC ihK =>
    intro a σ R ε rest hn hlen hε ⟨ν, S, hS, h⟩
    obtain ⟨t, a', x', kv, e, A, rfl, hkv, he, hA, hdp, hent, hrets, hkeeps, hall, hcont⟩ :=
      wsNode_callNext_inv hn
    obtain ⟨A', hA', hnode⟩ := wsCert_at hw (cert_at he hk)
    rw [hA] at hA'
    cases hA'
    have sat := call_entry h hS hkv pop hdp
    rw [← hent] at sat
    have hl : A.entry.kv.length ≤ e.frame.length := by rw [hent, param_kv_length]
    obtain ⟨r1, r2⟩ := ihC hnode hl hε.callee sat
    obtain ⟨⟨Wr, hd, hR⟩, hst⟩ := r2 _ rfl
    cases hidx : e.frame.findIdx? (· == .ret) with
    | none => exact (runC.not_returned_of_noRet (wsNode_retClosed hw) he hk hidx).elim
    | some i =>
      have hstor : A.ret.keeps = true →
          Devm.getStor _ sevm.currentTarget = Devm.getStor _ sevm.currentTarget :=
        fun hk' => (hst hk').trans (popBurn_getStor pop _)
      have sat' := resume_sound (rets := e.rets) h
        (fun s hs => by rw [hkv]; exact List.mem_cons_of_mem _ (List.mem_of_mem_take hs))
        (fun s hs => by rw [hkv]; exact List.mem_cons_of_mem _ (List.mem_of_mem_drop hs))
        hR (hR.1.trans hrets) hd hstor
      have hl' : (resume σ (kv.take e.frame.length) (kv.drop e.frame.length) A.ret e.rets).kv.length ≤
          (List.replicate e.rets AVal.unk ++ a'.drop e.frame.length).length := by
        rw [hkv] at hlen
        show ((List.range e.rets).map _ ++ kv.drop e.frame.length).length ≤ _
        simp only [List.length_append, List.length_map, List.length_range, List.length_drop,
          List.length_replicate, List.length_cons] at hlen ⊢
        omega
      obtain ⟨r3, r4⟩ := ihK (hcont i hidx) hl' hε sat'
      exact ⟨.callRet dw hk pop (callee_steps h hall r1) r3, fun d'' ho =>
        (r4 d'' ho).stor fun hk' => hstor (hkeeps hk')⟩
  | pcAt _ _ _ _ =>
    intro a σ R ε rest hn _ _ _
    simp only [wsNode] at hn
    cases hn

/-! ## The frozen statements -/

/-- **Soundness of the write-site checker** (tree level, no bytes): every run of entry `0` of an
accepted certificate executes only `SSTORE`s that meet a root site, read in the frame's root
environment. -/
theorem wsRun_sound {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {c : Cert} {ann : List WAnn} (hw : wsCert c ann = true)
    {sevm : Sevm} (hfork : CoveredFork sevm.benvStat.fork) {pre post : Devm}
    (run : SProg.RunP P c.prog sevm pre post) :
    SProg.RunP (WsStep (wsRoot ann) (Env.root sevm) P) c.prog sevm pre post := by
  obtain ⟨f, hf0, r⟩ := run
  have hc0 : ∃ e, c[0]? = some (e, f) := by
    simp only [Cert.prog, List.getElem?_map] at hf0
    cases h : c[0]? with
    | none => rw [h] at hf0; cases hf0
    | some p =>
      rw [h] at hf0
      cases hf0
      exact ⟨p.1, rfl⟩
  obtain ⟨e, hc0⟩ := hc0
  obtain ⟨A, hA, hnode⟩ := wsCert_at hw hc0
  have hinit : A.entry = WSt.init := by
    simp only [wsCert, Bool.and_eq_true, beq_iff_eq] at hw
    have h := hw.1.2
    rw [hA] at h
    exact Option.some.inj h
  have hroot : wsRoot ann = A.ret.sites := by
    simp only [wsRoot, hA, Option.map_some, Option.getD_some]
  rw [hinit] at hnode
  rw [hroot]
  exact ⟨f, hf0, (ws_run hP hw hfork r hnode (Nat.zero_le _) (Env.root_frame sevm)
    (init_sat sevm pre)).1⟩

/-- **The walk-facing lifting theorem**: a successful frame of certified bytes is a run of the
certified program whose steps sit in the derivation and whose `SSTORE`s meet a root site. -/
theorem lift_sound_ws {code : ByteArray} {c : Cert} {ann : List WAnn}
    (hc : Cert.check code c = true) (hw : wsCert c ann = true)
    {sevm : Sevm} {pre post : Devm} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork) (exc : Exec 0 sevm pre (.ok post)) :
    SProg.RunP (WsStep (wsRoot ann) (Env.root sevm) (StepIn ⟨0, sevm, pre, .ok post, exc⟩))
      c.prog sevm pre post := by
  exact wsRun_sound (fun h => StepIn.toRun h) hw hfork (lift_sound_in hc hcode hfork exc)

end Blanc.Lift.WriteSite
