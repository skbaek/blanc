import Blanc.Lift.WriteSiteSound

/-!
# Prefix soundness of the write-site checker

`ws_run_noStateGas` (`Blanc/Lift/WriteSiteSound.lean`) is a big-step statement: a whole
`SFunc.RunP` of a tree the write-site walk accepts is a run whose `SSTORE` steps meet the
summary's sites.  This module states the same observation at every configuration a synthetic
prefix reaches (`Reach`, `Blanc/Lift/Reach.lean`): `ws_reach_noStateGas` — a configuration
reached from entry `0` that is about to run `SSTORE` meets a root site (`WsObs`, read in the
frame's root environment).  The prefix may stop anywhere, so it applies to the gas-exact reach a
cursor gives at an actual node, whatever the frame's outcome.

The invariant `WsConf` holds of a configuration level by level: the current function's walk
state holds of the machine (`WSt.Sat`) above an untouched base, a keeping summary has written
no storage since the function's entry, the summary's sites lift to the root's, and each pending
continuation resumes soundly from any return that meets the summary (`resume_sound`), provided
the callee's frame carries a return marker (a frame without one never reaches `.ret`).  The
steps are those of `ws_run_noStateGas`: `wstep_sound_noStateGas`, `refine_sound`,
`popped_sound`, `compat_sat`/`tail_entry` for gotos, `call_entry`/`callNext_obs` for callee
entries, `retOk_sound` for returns.  Bytes-free and contract-neutral.
-/

namespace Blanc.Lift.WriteSite

open Jaune AbstractStackSafety Blanc.Lift.SymTransfer
open Blanc.Lift.FreePtr (cert_at gotoCompat_length)

/-- **A run transformer is a step transformer.**  A map from `P`-runs to `Q`-runs of every
program turns one `P` step into a `Q` step (apply it to the one-step program
`next n (last stop)`).  So a locality law stated over whole runs (`SProg.RunP.mono` of a
pointwise implication) applies at a single step. -/
theorem _root_.Blanc.Lift.SProg.RunP.point {P Q : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm}
    (hmono : ∀ {fs : List SFunc} {pre post : Devm},
      SProg.RunP P fs sevm pre post → SProg.RunP Q fs sevm pre post)
    {d d' : Devm} {n : Ninst} (h : P sevm d n d') : Q sevm d n d' := by
  obtain ⟨f, hf, r⟩ := hmono (fs := [.next n (.last .stop)]) (pre := d) (post := d')
    ⟨_, rfl, .next h (.last rfl)⟩
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
  subst hf
  cases r with
  | next hq hl =>
    cases hl with
    | last hr =>
      have he : _ = _ := hr
      simp only [Linst.run, Except.ok.injEq] at he
      subst he
      exact hq

/-- **An accepted `SSTORE` meets a site of the summary**, read over the machine state before the
step; no successor state is needed. -/
theorem wstep_sstore_obs {R : WRet} {σ σ' : WSt} {ε : Env} {sevm : Sevm} {ν : Nat → B256}
    {S rest : List B256} {d : Devm} (h : σ.Holds ε sevm ν S d) (hS : d.stack = S ++ rest)
    (hw : wstep R (.reg .sstore) σ = some σ') :
    ∀ x v rs, d.stack = x :: v :: rs → ∃ s ∈ R.sites, s.Obs ε sevm d x v := by
  intro x v rs hs
  obtain ⟨out, kv', sl, cl, ul, el, ho, -, -, hcov, -⟩ :=
    wstep_nonpush (fun bs fits he => by cases he) hw
  match hkv : σ.kv with
  | [] => rw [hkv] at ho; cases ho
  | [k] => rw [hkv] at ho; cases ho
  | k :: v' :: t => exact Site.Obs.of_any (hcov k v' t rfl hkv) (siteOf_obs h hkv hS hs)

section Conf

variable (es : List Entry) (ann : List WAnn) (sevm : Sevm) (Top : Devm → B256 → B256 → Prop)

/-- One function level of a configuration at machine state `d` with tree `f`: the walk state
holds of `d`, a keeping summary has kept the executing account's storage since the level's
entry `d₀`, the summary's sites lift to `Top`, a frame holding the return marker makes `live`
true, and `C live` holds of the returns that meet the summary. -/
def WsLevel (d : Devm) (f : SFunc) (C : Prop → (Devm → Prop) → Prop) : Prop :=
  ∃ (a : List AVal) (σ : WSt) (R : WRet) (ε : Env) (rest : List B256) (d₀ : Devm) (live : Prop),
    wsNode es ann R a σ f = true ∧ σ.kv.length ≤ a.length ∧ ε.Frame sevm ∧
    σ.Sat ε sevm d rest ∧
    (R.keeps = true → Devm.getStor d sevm.currentTarget = Devm.getStor d₀ sevm.currentTarget) ∧
    (∀ d' x v, (∃ s ∈ R.sites, s.Obs ε sevm d' x v) → Top d' x v) ∧
    (AVal.ret ∈ a → live) ∧ C live (RetObs ε sevm R rest d₀)

/-- The invariant of a configuration `⟨d, f, K⟩`: its current level holds, and every pending
continuation of `K` resumes into the invariant from a return of a live level. -/
def WsConf : List SFunc → Devm → SFunc → Prop
  | [], d, f => WsLevel es ann sevm Top d f fun _ _ => True
  | f' :: K, d, f =>
    WsLevel es ann sevm Top d f fun live Q => live → ∀ d', Q d' → WsConf K d' f'

/-- What a level's returns owe its pending continuations. -/
def WsCont : List SFunc → Prop → (Devm → Prop) → Prop
  | [] => fun _ _ => True
  | f' :: K => fun live Q => live → ∀ d', Q d' → WsConf es ann sevm Top K d' f'

theorem wsConf_def (K : List SFunc) (d : Devm) (f : SFunc) :
    WsConf es ann sevm Top K d f = WsLevel es ann sevm Top d f (WsCont es ann sevm Top K) := by
  cases K <;> rfl

theorem WsCont.anti {K : List SFunc} {live : Prop} {Q Q' : Devm → Prop}
    (hQ : ∀ d, Q' d → Q d) (h : WsCont es ann sevm Top K live Q) :
    WsCont es ann sevm Top K live Q' := by
  cases K with
  | nil => trivial
  | cons f' K => exact fun hl d hd => h hl d (hQ d hd)

end Conf

section Steps

variable {es : List Entry} {ann : List WAnn} {sevm : Sevm} {Top : Devm → B256 → B256 → Prop}

/-- **A goto enters its target's level**: from the goto's state, the target's walk holds at its
declared frame, its summary's sites lift through the jumper's, and its returns meet the
jumper's summary. -/
theorem wsLevel_goto {C : Prop → (Devm → Prop) → Prop}
    (hC : ∀ {live : Prop} {Q Q' : Devm → Prop}, (∀ d, Q' d → Q d) → C live Q → C live Q')
    {e : Entry} {σ : WSt} {A : WAnn} {R : WRet} {ε : Env} {rest : List B256} {d d₀ : Devm}
    {g : SFunc} {live : Prop} (hgo : gotoOk e σ A = true) (hle : retLe A.ret R = true)
    (sat : σ.Sat ε sevm d rest) (hnode : wsNode es ann A.ret e.frame A.entry g = true)
    (hl : A.entry.kv.length ≤ e.frame.length) (hε : ε.Frame sevm)
    (hkeep : R.keeps = true →
      Devm.getStor d sevm.currentTarget = Devm.getStor d₀ sevm.currentTarget)
    (hlift : ∀ d' x v, (∃ s ∈ R.sites, s.Obs ε sevm d' x v) → Top d' x v)
    (hlive : AVal.ret ∈ e.frame → live) (hcont : C live (RetObs ε sevm R rest d₀)) :
    WsLevel es ann sevm Top d g C := by
  have hsites : ∀ {ε' : Env} {d' : Devm} {x v : B256}, (∃ s ∈ A.ret.sites, s.Obs ε' sevm d' x v) →
      ∃ s ∈ R.sites, s.Obs ε' sevm d' x v := by
    intro ε' d' x v ⟨s, hs, ho⟩
    simp only [retLe, Bool.and_eq_true, List.all_eq_true] at hle
    exact Site.Obs.of_any (hle.2 s hs) ho
  unfold gotoOk at hgo
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hgo
  rcases hgo with hc | ⟨⟨hA, hent⟩, hn⟩
  · refine ⟨e.frame, A.entry, A.ret, ε, rest, d, live, hnode, hl, hε, compat_sat hc sat,
      fun _ => rfl, fun d' x v ho => hlift d' x v (hsites ho), hlive, hC ?_ hcont⟩
    intro d'' r
    exact (r.of_retLe hle).stor hkeep
  · obtain ⟨W, sat'⟩ := tail_entry sat hn
    rw [← hent] at sat'
    refine ⟨e.frame, A.entry, A.ret, ε.callee W, rest, d, live, hnode, hl, hε.callee, sat',
      fun _ => rfl, fun d' x v ho => hlift d' x v (hsites ?_), hlive, hC ?_ hcont⟩
    · have hA' := hA
      simp only [WRet.argFree, Bool.and_eq_true, List.all_eq_true] at hA'
      obtain ⟨s, hs, hslot, hg, hni⟩ := ho
      obtain ⟨hsl, hgs⟩ := hA'.2 s hs
      exact ⟨s, hs, Term.den_callee hsl hslot, fun g' hm => Term.den_callee (hgs g' hm) (hg g' hm),
        hni⟩
    · intro d'' r
      exact ((r.of_callee hA).of_retLe hle).stor hkeep

/-- **One synthetic step preserves the invariant.** -/
theorem wsConf_step {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {c : Cert} (hw : wsCert c ann = true)
    (hfork : sevm.benvStat.rules.stateGas = none) {a b : Conf}
    (step : ConfStep P c.prog sevm a b) (h : WsConf c.entries ann sevm Top a.K a.d a.f) :
    WsConf c.entries ann sevm Top b.K b.d b.f := by
  have hanti : ∀ {K : List SFunc} {live : Prop} {Q Q' : Devm → Prop}, (∀ d, Q' d → Q d) →
      WsCont c.entries ann sevm Top K live Q → WsCont c.entries ann sevm Top K live Q' :=
    fun hQ h => WsCont.anti _ _ _ _ hQ h
  cases step with
  | @next d d' n f K hp =>
    rw [wsConf_def] at h ⊢
    obtain ⟨a, σ, R, ε, rest, d₀, live, hn, hlen, hε, ⟨ν, S, hS, hh⟩, hkeep, hlift, hlive, hC⟩ := h
    obtain ⟨a', σ', ha, hs, hn'⟩ := wsNode_next_inv hn
    have hrun := hP hp
    obtain ⟨hl1024, hl⟩ := wstep_length hs ha hlen hS (List.Forall₂.length_eq hh.kv).symm hrun
    obtain ⟨sat', -, -⟩ := wstep_sound_noStateGas hfork hε hh hS hl1024 hs hrun
    exact ⟨a', σ', R, ε, rest, d₀, live, hn', hl, hε, sat',
      fun hk => (congrFun (wstep_keeps_noStateGas hfork hs hk hrun) _).trans (hkeep hk), hlift,
      fun hm => hlive (Cursor.ret_mem_of_absNinst ha hm), hC⟩
  | @dest d d' f K burn =>
    rw [wsConf_def] at h ⊢
    obtain ⟨a, σ, R, ε, rest, d₀, live, hn, hlen, hε, sat, hkeep, hlift, hlive, hC⟩ := h
    exact ⟨a, σ, R, ε, rest, d₀, live, hn, hlen, hε, sat.burn burn,
      fun hk => (burn_getStor burn _).trans (hkeep hk), hlift, hlive, hC⟩
  | @zero d d' f g K dw pop =>
    rw [wsConf_def] at h ⊢
    obtain ⟨a, σ, R, ε, rest, d₀, live, hn, hlen, hε, ⟨ν, S, hS, hh⟩, hkeep, hlift, hlive, hC⟩ := h
    obtain ⟨x, y, a', x', c', kv, rfl, hkv, h1, -⟩ := wsNode_branch_inv hn
    have hl : kv.length ≤ a'.length := by
      rw [hkv] at hlen; simp only [List.length_cons] at hlen; omega
    exact ⟨a', _, R, ε, rest, d₀, live, h1, hl, hε,
      refine_sound hh hS hkv pop (fun _ => rfl) (fun h => by cases h),
      fun hk => (popBurn_getStor pop _).trans (hkeep hk), hlift,
      fun hm => hlive (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)), hC⟩
  | @succ d d' f g K dw w hnz pop =>
    rw [wsConf_def] at h ⊢
    obtain ⟨a, σ, R, ε, rest, d₀, live, hn, hlen, hε, ⟨ν, S, hS, hh⟩, hkeep, hlift, hlive, hC⟩ := h
    obtain ⟨x, y, a', x', c', kv, rfl, hkv, -, h2⟩ := wsNode_branch_inv hn
    have hl : kv.length ≤ a'.length := by
      rw [hkv] at hlen; simp only [List.length_cons] at hlen; omega
    exact ⟨a', _, R, ε, rest, d₀, live, h2, hl, hε,
      refine_sound hh hS hkv pop (fun h => by cases h) (fun _ => hnz),
      fun hk => (popBurn_getStor pop _).trans (hkeep hk), hlift,
      fun hm => hlive (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)), hC⟩
  | @toZero d d' f k K dw pop =>
    rw [wsConf_def] at h ⊢
    obtain ⟨a, σ, R, ε, rest, d₀, live, hn, hlen, hε, ⟨ν, S, hS, hh⟩, hkeep, hlift, hlive, hC⟩ := h
    obtain ⟨x, y, a', x', c', kv, e, A, rfl, hkv, -, -, -, h1, -, -⟩ := wsNode_branchTo_inv hn
    have hl : kv.length ≤ a'.length := by
      rw [hkv] at hlen; simp only [List.length_cons] at hlen; omega
    exact ⟨a', _, R, ε, rest, d₀, live, h1, hl, hε,
      refine_sound hh hS hkv pop (fun _ => rfl) (fun h => by cases h),
      fun hk => (popBurn_getStor pop _).trans (hkeep hk), hlift,
      fun hm => hlive (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)), hC⟩
  | @toSucc d d' f g k K dw w hnz hk pop =>
    rw [wsConf_def] at h ⊢
    obtain ⟨a, σ, R, ε, rest, d₀, live, hn, hlen, hε, ⟨ν, S, hS, hh⟩, hkeep, hlift, hlive, hC⟩ := h
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
    exact wsLevel_goto (C := WsCont c.entries ann sevm Top K) hanti hcA hR
      (refine_sound hh hS hkv pop (fun h => by cases h) (fun _ => hnz)) hnode hl hε
      (fun hk => (popBurn_getStor pop _).trans (hkeep hk)) hlift
      (fun hm => hlive (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (ret_mem_of_gotoCompat hgo hm)))) hC
  | @jump d d' g k K dw hk pop =>
    rw [wsConf_def] at h ⊢
    obtain ⟨a, σ, R, ε, rest, d₀, live, hn, hlen, hε, ⟨ν, S, hS, hh⟩, hkeep, hlift, hlive, hC⟩ := h
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
    exact wsLevel_goto (C := WsCont c.entries ann sevm Top K) hanti hcA hR (popped_sound hh hS hkv pop) hnode hl hε
      (fun hk => (popBurn_getStor pop _).trans (hkeep hk)) hlift
      (fun hm => hlive (List.mem_cons_of_mem _ (ret_mem_of_gotoCompat hgo hm))) hC
  | @call d d' f g k K dw hk pop =>
    rw [wsConf_def] at h
    rw [wsConf_def]
    obtain ⟨a, σ, R, ε, rest, d₀, live, hn, hlen, hε, ⟨ν, S, hS, hh⟩, hkeep, hlift, hlive, hC⟩ := h
    obtain ⟨t, a', x', kv, e, A, rfl, hkv, he, hA, hdp, hent, hrets, hkeeps, hall, hcont⟩ :=
      wsNode_callNext_inv hn
    obtain ⟨A', hA', hnode⟩ := wsCert_at hw (cert_at he hk)
    rw [hA] at hA'
    cases hA'
    have sat := call_entry hh hS hkv pop hdp
    rw [← hent] at sat
    have hl : A.entry.kv.length ≤ e.frame.length := by rw [hent, param_kv_length]
    refine ⟨e.frame, A.entry, A.ret, _, _, d', ∃ i, e.frame.findIdx? (· == .ret) = some i,
      hnode, hl, hε.callee, sat, fun _ => rfl,
      fun d'' x v ho => hlift d'' x v (callNext_obs hh hall ho), ?_, ?_⟩
    · intro hm
      cases hidx : e.frame.findIdx? (· == .ret) with
      | none => exact absurd rfl (ret_not_mem_of_findIdx_none hidx _ hm)
      | some i => exact ⟨i, rfl⟩
    · rintro ⟨i, hidx⟩ d'' ⟨⟨Wr, hd, hR⟩, hst⟩
      rw [wsConf_def]
      have hstor : A.ret.keeps = true →
          Devm.getStor d'' sevm.currentTarget = Devm.getStor d sevm.currentTarget :=
        fun hk' => (hst hk').trans (popBurn_getStor pop _)
      have sat' := resume_sound (rets := e.rets) hh
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
      exact ⟨_, _, R, ε, rest, d₀, live, hcont i hidx, hl', hε, sat',
        fun hk' => (hstor (hkeeps hk')).trans (hkeep hk'), hlift,
        fun hm => hlive (List.mem_cons_of_mem _ ((List.mem_append.mp hm).elim
          (fun hr => absurd (List.eq_of_mem_replicate hr) (by decide)) List.mem_of_mem_drop)), hC⟩
  | @ret d d' f K dw pop =>
    rw [wsConf_def] at h
    obtain ⟨a, σ, R, ε, rest, d₀, live, hn, hlen, hε, ⟨ν, S, hS, hh⟩, hkeep, hlift, hlive, hC⟩ := h
    obtain ⟨a', x', kv, rfl, hkv, hr⟩ := wsNode_ret_inv hn
    obtain ⟨hst, hR⟩ := retOk_sound hh hS hkv pop hr
    exact hC (hlive List.mem_cons_self) d'
      ⟨⟨_, hst, hR⟩, fun hk => (popBurn_getStor pop _).trans (hkeep hk)⟩
  | pcAt hp hr =>
    rw [wsConf_def] at h
    obtain ⟨a, σ, R, ε, rest, d₀, live, hn, -⟩ := h
    simp only [wsNode] at hn
    cases hn

end Steps

/-- **Prefix soundness of the write-site checker.**  Every configuration a synthetic prefix
reaches from entry `0` of an accepted certificate, on a fork without state gas, that is about to
run `SSTORE` meets a root site, read in the frame's root environment: the prefix form of
`wsRun_sound_noStateGas`. -/
theorem ws_reach_noStateGas {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {c : Cert} {ann : List WAnn} (hw : wsCert c ann = true)
    {sevm : Sevm} (hfork : sevm.benvStat.rules.stateGas = none) {pre : Devm} {f : SFunc}
    (hf0 : c.prog[0]? = some f) {T : Conf} (reach : Reach P c.prog sevm ⟨pre, f, []⟩ T)
    {g : SFunc} (tree : T.f = .next (.reg .sstore) g) :
    WsObs (wsRoot ann) (Env.root sevm) sevm T.d (.reg .sstore) := by
  let Top : Devm → B256 → B256 → Prop := fun d x v =>
    ∃ s ∈ wsRoot ann, s.Obs (Env.root sevm) sevm d x v
  have h0 : WsConf c.entries ann sevm Top [] pre f := by
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
    refine ⟨e.frame, WSt.init, A.ret, Env.root sevm, pre.stack, pre, True, hnode,
      Nat.zero_le _, Env.root_frame sevm, init_sat sevm pre, fun _ => rfl, ?_,
      fun _ => trivial, trivial⟩
    intro d x v ho
    show ∃ s ∈ wsRoot ann, _
    rw [hroot]
    exact ho
  have hall : ∀ {T' : Conf}, Reach P c.prog sevm ⟨pre, f, []⟩ T' →
      WsConf c.entries ann sevm Top T'.K T'.d T'.f := by
    intro T' r
    induction r with
    | refl => exact h0
    | tail _ step ih => exact wsConf_step hP hw hfork step ih
  have hT := hall reach
  rw [tree, wsConf_def] at hT
  obtain ⟨a, σ, R, ε, rest, d₀, live, hn, -, -, ⟨ν, S, hS, hh⟩, -, hlift, -⟩ := hT
  obtain ⟨a', σ', -, hs, -⟩ := wsNode_next_inv hn
  intro _ x v rs hst
  exact hlift _ x v (wstep_sstore_obs hh hS hs x v rs hst)

/-- `ws_reach_noStateGas` from the cursor's start configuration (`Cursor.start`). -/
theorem ws_reach_start_noStateGas {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {c : Cert} {ann : List WAnn} (hw : wsCert c ann = true)
    {sevm : Sevm} (hfork : sevm.benvStat.rules.stateGas = none) {pre : Devm} {T : Conf}
    (reach : Reach P c.prog sevm ((Cursor.start c).conf pre) T)
    {g : SFunc} (tree : T.f = .next (.reg .sstore) g) :
    WsObs (wsRoot ann) (Env.root sevm) sevm T.d (.reg .sstore) := by
  cases c with
  | nil =>
    rcases Relation.ReflTransGen.cases_head reach with rfl | ⟨b, step, -⟩
    · cases tree
    · cases step
  | cons p c =>
    exact ws_reach_noStateGas hP hw hfork (f := p.2) rfl reach tree

end Blanc.Lift.WriteSite
