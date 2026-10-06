import Blanc.Lift.NodeWalkOrig

/-!
# The original state, agreed on the accessed keys only

`Blanc/Lift/NodeWalkOrig.lean` transports a certificate run (`wrun`, `childRun`) between two
transaction-original states that hold the same storage **everywhere** (`OrigAgree`).  A
kernel-checked run over every world that agrees with a checkpoint on finitely many entries
(`Blanc/Lift/ShadowTail.lean`) has no such agreement: the world's original storage is free
outside the checkpoint's keys.  This module needs agreement only on the keys the run itself
records as accessed (`OrigAgreeOn O O' D`):

* `wrun_keys`: a run only adds accessed keys (`wstep_keys`), and every `SSTORE` records its
  key (`sstoreStep_key_mem`);
* `wrun_withOrig_keys`, `childRun_withOrig_keys`: a certificate run (resp. a code child's run)
  is unchanged under an original state that agrees on the keys its final configuration records
  as accessed (`resKeys`): the `SSTORE` charge is the only reader of the original state, and it
  reads only the key it stores to.

Nothing here is contract-specific.
-/

namespace Blanc.Lift.Witness

open Jaune Blanc.Lift Blanc.Lift.NodeWalk

/-! ## The original state, agreed on the accessed keys only -/

/-- The storage keys a result's shadow records as accessed (none for a stuck run). -/
def resKeys : Res → List (Adr × B256)
  | .cont c => c.keys
  | .done _ c => c.keys
  | .stuck => []

/-- Two original states holding the same storage at the keys `D`. -/
def OrigAgreeOn (O O' : State) (D : List (Adr × B256)) : Prop :=
  ∀ x ∈ D, (O.get x.1).stor.get x.2 = (O'.get x.1).stor.get x.2

variable {s : Sevm} {O : State}

theorem sloadStep_keys {c c' : Cfg} {g : SFunc} (h : sloadStep s c g = some c') :
    ∀ x ∈ c.keys, x ∈ c'.keys := by
  unfold sloadStep at h
  split at h
  · dsimp only at h
    split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;>
      first | exact fun x hx => hx | exact fun x hx => List.mem_cons_of_mem _ hx
  · cases h

theorem sstoreStep_keys {c c' : Cfg} {g : SFunc} (h : sstoreStep s c g = some c') :
    ∀ x ∈ c.keys, x ∈ c'.keys := by
  unfold sstoreStep at h
  split at h
  · dsimp only at h
    split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;>
      first | exact fun x hx => hx | exact fun x hx => List.mem_cons_of_mem _ hx
  · cases h

/-- A successful `SSTORE` records its key as accessed. -/
theorem sstoreStep_key_mem {c c' : Cfg} {g : SFunc} (h : sstoreStep s c g = some c') :
    ∀ k v rest, c.devm.stack = k :: v :: rest → (s.currentTarget, k) ∈ c'.keys := by
  intro k v rest hs
  unfold sstoreStep at h
  rw [hs] at h
  dsimp only at h
  split_ifs at h with h1 h2 h3 h4 <;> simp only [Option.some.injEq] at h <;> subst h
  · exact h2
  · exact List.mem_cons_self

/-- An `SSTORE` under a changed original state that agrees at its key is unchanged. -/
theorem sstoreStep_withOrig_key {c c' : Cfg} {g : SFunc}
    (h : sstoreStep (s.withOrig O) c g = some c')
    (hO : ∀ k v rest, c.devm.stack = k :: v :: rest →
      (O.get s.currentTarget).stor.get k = (s.benvStat.origState.get s.currentTarget).stor.get k) :
    sstoreStep s c g = some c' := by
  unfold sstoreStep at h ⊢
  revert h hO
  generalize c.devm.stack = st
  rcases st with _ | ⟨k, _ | ⟨v, rest⟩⟩
  · intro h; cases h
  · intro h; cases h
  · intro h hO
    have e : getOrigStorVal (s.withOrig O) (s.withOrig O).currentTarget k =
        getOrigStorVal s s.currentTarget k := hO k v rest rfl
    simp only [e] at h
    exact h

theorem mstoreStep_keys {c c' : Cfg} {g : SFunc} (h : mstoreStep c g = some c') :
    c'.keys = c.keys := by
  unfold mstoreStep at h; split at h
  · dsimp only at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h; rfl
  · cases h

theorem mloadStep_keys {c c' : Cfg} {g : SFunc} (h : mloadStep c g = some c') :
    c'.keys = c.keys := by
  unfold mloadStep at h; split at h
  · dsimp only at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h; rfl
  · cases h

theorem calldatacopyStep_keys {c c' : Cfg} {g : SFunc} (h : calldatacopyStep s c g = some c') :
    c'.keys = c.keys := by
  unfold calldatacopyStep at h; split at h
  · dsimp only at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h; rfl
  · cases h

theorem keccakStep_keys {c c' : Cfg} {g : SFunc} (h : keccakStep c g = some c') :
    c'.keys = c.keys := by
  unfold keccakStep at h; split at h
  · dsimp only at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h; rfl
  · cases h

theorem logStep_keys {k} {c c' : Cfg} {g : SFunc} (h : logStep s k c g = some c') :
    c'.keys = c.keys := by
  unfold logStep at h; split at h
  · dsimp only at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h; rfl
  · cases h

theorem callStep_keys {c c' : Cfg} {g : SFunc} (h : callStep s c g = some c') :
    c'.keys = c.keys := by
  unfold callStep at h
  split at h
  · split at h
    · split_ifs at h
      split at h
      · cases h; rfl
      · cases h
    · cases h
  · cases h

/-- **An interpreter step only adds accessed keys.** -/
theorem wstep_keys {fs : List SFunc} {c c' : Cfg} (h : wstep fs s c = .cont c') :
    ∀ x ∈ c.keys, x ∈ c'.keys := by
  intro x hx
  rcases c with ⟨d, f, K, keys, adrs, stor, acs⟩
  cases f with
  | next n g =>
    cases n with
    | reg r =>
      cases r <;> simp only [wstep] at h <;>
        first
        | (split at h <;> first
            | (cases h; done)
            | (rename_i c'' hc; cases h
               first
               | exact sloadStep_keys hc x hx
               | exact sstoreStep_keys hc x hx
               | (rw [mstoreStep_keys hc]; exact hx)
               | (rw [mloadStep_keys hc]; exact hx)
               | (rw [calldatacopyStep_keys hc]; exact hx)
               | (rw [keccakStep_keys hc]; exact hx)
               | (rw [logStep_keys hc]; exact hx)))
        | (split_ifs at h <;> (try split at h) <;> cases h <;> exact hx)
        | (cases h)
    | exec e =>
      cases e <;> simp only [wstep] at h <;>
        first
        | (split at h <;> first
            | (cases h; done)
            | (rename_i c'' hc; cases h; rw [callStep_keys hc]; exact hx))
        | (simp only [ninstAccKeeps, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h)
        | (split_ifs at h <;> (try split at h) <;> cases h <;> exact hx)
    | _ =>
      simp only [wstep] at h
      split_ifs at h <;> (try split at h) <;> cases h <;> exact hx
  | last l =>
    cases l <;> simp only [wstep] at h <;>
      (repeat' (first | split at h | split_ifs at h)) <;> cases h
  | dest g | jump k | branch g1 g2 | branchTo g k | callNext k g | ret | pcAt p g | undefined =>
    simp only [wstep] at h
    repeat' (first | split at h | split_ifs at h)
    all_goals first | (cases h; done) | (cases h; exact hx)


/-- A step that halts carries its own configuration. -/
theorem wstep_done_cfg {fs : List SFunc} {c c0 : Cfg} {o : Outcome}
    (h : wstep fs s c = .done o c0) : c0 = c := by
  rcases c with ⟨d, f, K, keys, adrs, stor, acs⟩
  cases f with
  | next n g =>
    cases n with
    | reg r =>
      cases r <;> simp only [wstep] at h <;>
        (repeat' (first | split at h | split_ifs at h)) <;> cases h
    | exec e =>
      cases e <;> simp only [wstep] at h <;>
        (repeat' (first | split at h | split_ifs at h)) <;> cases h
    | _ =>
      simp only [wstep] at h
      repeat' (first | split at h | split_ifs at h)
      all_goals cases h
  | last l =>
    cases l <;> simp only [wstep] at h <;>
      (repeat' (first | split at h | split_ifs at h)) <;> first | (cases h; done) | (cases h; rfl)
  | dest g | jump k | branch g1 g2 | branchTo g k | callNext k g | ret | pcAt p g | undefined =>
    simp only [wstep] at h
    repeat' (first | split at h | split_ifs at h)
    all_goals first | (cases h; done) | (cases h; rfl)

/-- **A run only adds accessed keys.** -/
theorem wrun_keys {fs : List SFunc} : ∀ (n : Nat) (c : Cfg), wrun fs s n c ≠ .stuck →
    ∀ x ∈ c.keys, x ∈ resKeys (wrun fs s n c)
  | 0, _, _, _, hx => hx
  | n + 1, c, hs, x, hx => by
    simp only [wrun] at hs ⊢
    generalize hw : wstep fs s c = r at hs ⊢
    rcases r with c' | ⟨o, c0⟩ | _
    · exact wrun_keys n c' hs x (wstep_keys hw x hx)
    · rw [wstep_done_cfg hw]; exact hx
    · exact absurd rfl hs

theorem wstep_sstore {fs : List SFunc} {c : Cfg} {g : SFunc} (hf : c.f = .next (.reg .sstore) g) :
    wstep fs s c = match sstoreStep s c g with | some c' => .cont c' | none => .stuck := by
  rcases c with ⟨d, f, K, keys, adrs, stor, acs⟩
  simp only at hf
  subst hf
  rfl

/-- One step under a changed original state, when its `SSTORE` (if it is one) is unchanged. -/
theorem wstep_withOrig_of (fs : List SFunc) {c : Cfg}
    (hO : ∀ g, c.f = .next (.reg .sstore) g → sstoreStep (s.withOrig O) c g = sstoreStep s c g) :
    wstep fs (s.withOrig O) c = wstep fs s c := by
  rcases c with ⟨d, f, K, keys, adrs, stor, acs⟩
  cases f with
  | dest _ => rfl
  | jump _ => rfl
  | branch _ _ => rfl
  | branchTo _ _ => rfl
  | callNext _ _ => rfl
  | ret => rfl
  | undefined => rfl
  | pcAt p k =>
    simp only [wstep, ninst_step_reg_withOrig p d (by decide : Rinst.pc ≠ .sstore)]
  | last l =>
    cases l <;> simp only [wstep, linst_run_withOrig]
  | next n k =>
    cases n with
    | push xs h => rfl
    | dupn _ => rfl
    | swapn _ => rfl
    | exchange _ => rfl
    | exec x =>
      cases x <;> simp only [wstep, callStep_withOrig, ninstAccKeeps, Bool.false_eq_true, ↓reduceIte]
    | reg r =>
      by_cases hs : r = .sstore
      · subst hs; simp only [wstep, hO k rfl]
      · cases r <;> first
          | exact absurd rfl hs
          | rfl
          | simp only [wstep, ninst_step_reg_withOrig _ _ hs]

/-- **A certificate run is unchanged under an original state that agrees on the keys the run
records as accessed.**  Every `SSTORE` records its key (`sstoreStep_key_mem`) and keys are only
added (`wrun_keys`), so agreement on the final configuration's keys covers every original value
the run's charges read. -/
theorem wrun_withOrig_keys (fs : List SFunc) : ∀ (n : Nat) (c : Cfg),
    wrun fs (s.withOrig O) n c ≠ .stuck →
    OrigAgreeOn O s.benvStat.origState (resKeys (wrun fs (s.withOrig O) n c)) →
    wrun fs s n c = wrun fs (s.withOrig O) n c
  | 0, _, _, _ => rfl
  | n + 1, c, hs, hO => by
    simp only [wrun] at hs hO ⊢
    by_cases hss : ∃ g, c.f = .next (.reg .sstore) g
    · obtain ⟨g, hf⟩ := hss
      rw [wstep_sstore hf] at hs hO ⊢
      rw [wstep_sstore hf]
      generalize hw : sstoreStep (s.withOrig O) c g = r at hs hO ⊢
      rcases r with _ | c'
      · exact absurd rfl hs
      · dsimp only at hs hO ⊢
        have hk : ∀ k v rest, c.devm.stack = k :: v :: rest →
            (O.get s.currentTarget).stor.get k =
              (s.benvStat.origState.get s.currentTarget).stor.get k := fun k v rest hst =>
          hO _ (wrun_keys n c' hs _ (sstoreStep_key_mem hw k v rest hst))
        rw [sstoreStep_withOrig_key hw hk]
        exact wrun_withOrig_keys fs n c' hs hO
    · have hO' : ∀ g, c.f = .next (.reg .sstore) g →
          sstoreStep (s.withOrig O) c g = sstoreStep s c g := fun g hf => absurd ⟨g, hf⟩ hss
      rw [wstep_withOrig_of fs hO'] at hs hO ⊢
      generalize wstep fs s c = r at hs hO ⊢
      rcases r with c' | _ | _
      · exact wrun_withOrig_keys fs n c' hs hO
      · rfl
      · rfl

/-- **A code child's run is unchanged** under an original state agreeing on the keys its
halting configuration records. -/
theorem childRun_withOrig_keys (fs : List SFunc) (code : ByteArray) (n : Nat) (c : Cfg)
    (hs : childRun fs code (s.withOrig O) n c ≠ .stuck)
    (hO : OrigAgreeOn O s.benvStat.origState (resKeys (childRun fs code (s.withOrig O) n c))) :
    childRun fs code s n c = childRun fs code (s.withOrig O) n c := by
  unfold childRun at hs hO ⊢
  rcases hf0 : fs[0]? with _ | f0
  · rfl
  · simp only [hf0] at hs hO ⊢
    rw [childStart_withOrig] at hs hO ⊢
    rcases hcs : childStart s c f0 with _ | ⟨e, cc⟩
    · rfl
    · have hst := childStart_stat hcs
      simp only [hcs, Option.map_some] at hs hO ⊢
      have h1 : (e.withOrig O).sta = e.sta.withOrig O := rfl
      rw [h1] at hs hO ⊢
      have h2 : (e.sta.withOrig O).benvStat.fork = e.sta.benvStat.fork := rfl
      have h3 : (e.sta.withOrig O).code = e.sta.code := rfl
      rw [h2, h3] at hs hO ⊢
      split
      · rename_i hc
        rw [if_pos hc] at hs hO
        rw [← hst] at hO
        exact wrun_withOrig_keys fs n cc hs hO
      · rfl

end Blanc.Lift.Witness
