import Lean
import Blanc.Composition.Corpus.Proofs.RingHistory
import Blanc.Composition.Corpus.Proofs.RingTotality
import Blanc.Corpus.Freeze.BeaconRoots
import Blanc.Corpus.Freeze.HistoryStorage
import Blanc.JointFeed
import JauneConsensus.Facts.SlotEpochFrames
import JauneConsensus.Facts.AnchorInvCorpus

/-!
# Ring-contract retention and joint-consensus `S8`/`S9` proofs (`pcc-wave2-rh`)

Proves the positive `S8` and `S9` cells for EIP-4788 (`R`) and EIP-2935 (`H`):
* `r_s8_slot : R_S8_slot`
* `r_s9 : R_S9`
* `h_s8 : H_S8`
* `h_s9 : H_S9`
* `h_s9_joint : H_S9_joint`
-/

namespace Blanc.Composition.Corpus.Proofs.RingJointRetention

open Jaune JauneConsensus ExecutionTrace
open Blanc.Corpus.Freeze

/-! ## Word and modular-arithmetic helpers -/

private theorem ring_ne_zero : (0x1fff : B256) ≠ 0 := by
  intro h
  have h1 : (0x1fff : B256).toNat = (0 : B256).toNat := congrArg B256.toNat h
  have h2 : (0x1fff : B256).toNat = 8191 := rfl
  have h3 : (0 : B256).toNat = 0 := rfl
  omega

private theorem ring_toNat : (0x1fff : B256).toNat = 8191 := rfl

private theorem nat_toB256_sub_one (n : Nat) (hpos : 0 < n) (hn : n < 2 ^ 256) :
    n.toB256 - 1 = (n - 1).toB256 := by
  apply B256.toNat_inj
  have h1le : (1 : B256) ≤ n.toB256 := by
    rw [B256.le_iff_toNat_le_toNat, B256.toNat_one, B256.toNat_toB256_of_lt hn]
    exact hpos
  rw [B256.toNat_sub_eq_of_le n.toB256 1 h1le, B256.toNat_toB256_of_lt hn,
    B256.toNat_one, B256.toNat_toB256_of_lt (by omega)]

private theorem no_small_factor_8191 :
    ∀ k : Nat, k < 91 → 2 ≤ k → 8191 % k ≠ 0 := by
  decide

private theorem coprime_8191_of_not_dvd {d : Nat} (hndvd : ¬ 8191 ∣ d) :
    Nat.Coprime d 8191 := by
  unfold Nat.Coprime
  by_contra hne
  set g := Nat.gcd d 8191
  have hgd : g ∣ d := Nat.gcd_dvd_left d 8191
  have hg8 : g ∣ 8191 := Nat.gcd_dvd_right d 8191
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right d (by omega)
  have hg_ge2 : 2 ≤ g := by omega
  by_cases hg_lt : g < 91
  · exact no_small_factor_8191 g hg_lt hg_ge2 (Nat.mod_eq_zero_of_dvd hg8)
  · obtain ⟨q, hq⟩ := hg8
    have hq_pos : 0 < q := by
      rcases q with _ | q
      · simp only [Nat.mul_zero] at hq; omega
      · exact Nat.succ_pos q
    have hq_lt : q < 91 := by
      by_contra hge
      have : 91 * 91 ≤ g * q := Nat.mul_le_mul (by omega) (by omega)
      omega
    rcases Nat.eq_or_lt_of_le hq_pos with hq1 | hq2
    · rw [← hq1, Nat.mul_one] at hq
      exact hndvd (hq ▸ hgd)
    · exact no_small_factor_8191 q hq_lt hq2
        (Nat.mod_eq_zero_of_dvd ⟨g, by rw [Nat.mul_comm, hq]⟩)

private theorem b256_mod_ring_toNat (x : B256) :
    (x % ring).toNat = x.toNat % 8191 := by
  have hring : ring = 0x1fff := rfl
  rw [hring, B256.toNat_mod ring_ne_zero, ring_toNat]

private theorem root_time_ne (a b : B256) : BeaconRoots.rootKey a ≠ BeaconRoots.timeKey b := by
  unfold BeaconRoots.rootKey BeaconRoots.timeKey
  intro h
  have h1 := congrArg B256.toNat h
  have ha : (a % ring).toNat < 8191 := by
    rw [b256_mod_ring_toNat]
    exact Nat.mod_lt a.toNat (by omega)
  have hb : (b % ring).toNat < 8191 := by
    rw [b256_mod_ring_toNat]
    exact Nat.mod_lt b.toNat (by omega)
  have hring : ring.toNat = 8191 := ring_toNat
  rw [B256.toNat_add, hring] at h1
  rw [Nat.lo_eq_of_lt (by omega)] at h1
  omega

/-! ## `JointRun` prefix / kept-history helpers -/

private theorem jointRun_step_in_kept {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {a : Adr} {C : ByteArray} {checkpoint : BlockChain} {anchor final : JointState P}
    (v : Corpus.Freeze.RingJoint cfg ccfg bls a C checkpoint anchor final)
    {k : Nat} (hk : k < v.run.steps.length) :
    ∃ preSteps : List KeptBlock,
      let st := v.run.steps[k]'hk
      KeptHistory cfg checkpoint (v.pre.kept ++ preSteps) st.pre.exec ∧
      KeptStep cfg st.keptBlock st.post.exec ∧
      CoveredFork st.keptBlock.fork ∧
      NoCreateAt systemAddress st.keptBlock.run.roots ∧
      (∀ b ∈ v.pre.kept ++ preSteps, CoveredFork b.fork) ∧
      HistoryClean (v.pre.kept ++ preSteps) := by
  have hhist := (v.run.toExec v.pre).keptHistory
  have hcov := (v.run.toExec v.pre).kept_covered
  have hget : (v.run.toExec v.pre).kept[v.pre.kept.length + k]? =
      some (v.run.steps[k]'hk).keptBlock :=
    v.run.kept_getElem? v.pre (List.getElem?_eq_getElem hk)
  obtain ⟨_, hpre, _, _⟩ := hhist.split_at hget
  rw [v.run.kept_take_add v.pre k] at hpre
  have htake_sub : ∀ b ∈ v.pre.kept ++ (v.run.steps.take k).map JointRunStep.keptBlock,
      b ∈ (v.run.toExec v.pre).kept := by
    intro b hb
    rw [← v.run.kept_take_add v.pre k] at hb; exact List.mem_of_mem_take hb
  have hst_mem : (v.run.steps[k]'hk).keptBlock ∈ (v.run.toExec v.pre).kept := by
    rw [v.run.kept_toExec v.pre]; exact List.mem_append_right _ (List.mem_map_of_mem (List.getElem_mem hk))
  have hclean := v.clean
  refine ⟨(v.run.steps.take k).map JointRunStep.keptBlock, hpre, (v.run.steps[k]'hk).keptBlock_step,
    hcov _ hst_mem, hclean.creates _ hst_mem, fun b hb => hcov b (htake_sub b hb),
    ⟨fun b hb => hclean.senders b (htake_sub b hb), fun b hb => hclean.authorities b (htake_sub b hb),
      fun b hb => hclean.creates b (htake_sub b hb)⟩⟩

private theorem jointRun_first_pre {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} (run : JointRun cfg ccfg bls s₀ s) (h : 0 < run.steps.length) :
    (run.steps[0]'h).pre = s₀ := by
  have hl := congrArg (·[0]?) run.steps_linked
  rw [List.getElem?_append_left (by simp only [List.length_map]; exact h), List.getElem?_map,
    List.getElem?_eq_getElem h] at hl
  simp only [Option.map_some, List.getElem?_cons_zero, Option.some.injEq] at hl; exact hl

private theorem jointRun_step_link {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} (run : JointRun cfg ccfg bls s₀ s) {k : Nat}
    (hk : k + 1 < run.steps.length) :
    (run.steps[k]'(Nat.lt_of_succ_lt hk)).post = (run.steps[k + 1]'hk).pre := by
  have hl := congrArg (·[k + 1]?) run.steps_linked
  rw [List.getElem?_append_left (by simp only [List.length_map]; exact hk), List.getElem?_map,
    List.getElem?_eq_getElem hk, List.getElem?_cons_succ, List.getElem?_map,
    List.getElem?_eq_getElem (Nat.lt_of_succ_lt hk)] at hl
  simp only [Option.map_some, Option.some.injEq] at hl; exact hl.symm

private theorem jointBlockInput_parent_root {P : Preset} {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {s s' : JointState P} {b : AnySignedBlock P}
    (h : jointStep cfg ccfg bls s b = .ok s') :
    ∃ st : BeaconState P b.1, jointBlockInput ccfg bls s b = .ok st ∧
      b.2.message.parent_root = Ssz.hashTreeRoot st.latest_block_header := by
  obtain ⟨st, hin, _, hp⟩ := jointStep_processBlock h
  refine ⟨st, hin, ?_⟩
  unfold processBlock processBlockWith at hp
  cases hhdr : processBlockHeader st b.2.message with
  | error e => rw [hhdr] at hp; cases hp
  | ok s1 =>
    unfold processBlockHeader at hhdr
    iterate 4 obtain ⟨_, _, hhdr⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hhdr
    obtain ⟨_, hpr, _⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hhdr
    exact beq_iff_eq.mp (require_eq_ok_iff.mp hpr)

private theorem stateTransition_slot_lt {P : Preset} {f : CFork} {ctx : Ctx}
    {s s' : BeaconState P f} {sb : SignedBeaconBlock P f}
    (h : JauneConsensus.stateTransition ctx s sb = .ok s') : s.slot < sb.message.slot := by
  unfold JauneConsensus.stateTransition JauneConsensus.stateTransitionWith at h
  dsimp only at h
  obtain ⟨_, hs, _⟩ := Jaune.Except.bind_eq_ok h
  unfold JauneConsensus.processSlotsWith at hs
  obtain ⟨_, hreq, _⟩ := Jaune.Except.bind_eq_ok hs
  exact of_decide_eq_true (require_eq_ok_iff.mp hreq)

/-! ## `R_S9` -/

private theorem filledHeaderRoot_eq_jaune {P : Preset} {f : CFork} (s : BeaconState P f) :
    BeaconRoots.filledHeaderRoot s = JauneConsensus.Facts.filledHeaderRoot s := by
  unfold BeaconRoots.filledHeaderRoot JauneConsensus.Facts.filledHeaderRoot JauneConsensus.Facts.filledHeader
  by_cases hz : s.latest_block_header.state_root = 0
  · rw [ite_eq_left hz, ite_eq_left ((JauneConsensus.Facts.b256_beq_eq_true_iff _ _).mpr hz)]
  · rw [ite_eq_right hz, ite_eq_right (by rw [(JauneConsensus.Facts.b256_beq_eq_false_iff _ _).mpr hz]; exact Bool.false_ne_true)]

theorem r_s9 : BeaconRoots.R_S9 := by
  intro P cfg ccfg bls checkpoint anchor final v
  refine ⟨?_, ?_, ?_⟩
  · intro st hst
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hst
    obtain ⟨preSteps, hpre, hstep, hcov_st, havoid_st, hcov_pre, hclean_pre⟩ := jointRun_step_in_kept v hk
    have hpre_state := Blanc.Corpus.Proofs.RingHistory.R.history hpre hcov_pre v.code v.systemEmpty hclean_pre
    have hclean_st : v.run.steps[k].keptBlock ∈ (v.run.toExec v.pre).kept := by
      rw [v.run.kept_toExec v.pre]; exact List.mem_append_right _ (List.mem_map_of_mem (List.getElem_mem hk))
    have hstep_r := Blanc.Corpus.Proofs.RingHistory.R.step
      hstep hcov_st hpre_state.1 hpre_state.2.1 (v.clean.senders _ hclean_st) (v.clean.authorities _ hclean_st) havoid_st
    have hstor := hstep_r.2.2
    unfold BeaconRoots.blockWrite at hstor
    rw [JointRunStep.keptBlock_timestamp, JointRunStep.keptBlock_parentBeaconBlockRoot] at hstor
    dsimp only at hstor
    have hkeyT : BeaconRoots.write (Corpus.Freeze.storOf (v.run.steps[k]'hk).pre.exec.state BeaconRoots.addr)
        (Corpus.Freeze.stepTime (v.run.steps[k]'hk)) (v.run.steps[k]'hk).block.2.message.parent_root
        (BeaconRoots.timeKey (Corpus.Freeze.stepTime (v.run.steps[k]'hk))) =
        Corpus.Freeze.stepTime (v.run.steps[k]'hk) := by
      unfold BeaconRoots.write; rw [ite_eq_right (root_time_ne _ _).symm, ite_eq_left rfl]
    have hkeyR : BeaconRoots.write (Corpus.Freeze.storOf (v.run.steps[k]'hk).pre.exec.state BeaconRoots.addr)
        (Corpus.Freeze.stepTime (v.run.steps[k]'hk)) (v.run.steps[k]'hk).block.2.message.parent_root
        (BeaconRoots.rootKey (Corpus.Freeze.stepTime (v.run.steps[k]'hk))) =
        (v.run.steps[k]'hk).block.2.message.parent_root := by
      unfold BeaconRoots.write; rw [ite_eq_left rfl]
    have p1 := (congrFun hstor _).trans hkeyT
    have p2 := (congrFun hstor _).trans hkeyR
    refine ⟨p1, p2, fun hnz => ?_⟩
    unfold BeaconRoots.read; rw [p1, p2]
    simp only [hnz, ne_eq, not_false_eq_true, and_self, ite_true]
  · intro hpos
    have hstep0 : jointStep cfg ccfg bls (v.run.steps[0]'hpos).pre (v.run.steps[0]'hpos).block =
        .ok (v.run.steps[0]'hpos).post := v.run.steps_jointStep (List.getElem?_eq_getElem hpos)
    rw [jointRun_first_pre v.run hpos] at hstep0
    have hbin := jointBlockInput_parent_root hstep0
    rcases anchor with ⟨fs, beacon, exec⟩
    rcases hblk : (v.run.steps[0]'hpos).block with ⟨fb, sb⟩
    dsimp only at ⊢; rw [hblk] at hstep0 hbin ⊢; dsimp only at hbin ⊢
    cases fs <;> cases fb
    all_goals try (unfold jointStep at hstep0; cases hstep0)
    · refine ⟨hbin, ?_⟩
      obtain ⟨hslot_lt, _, _, _, _, _, hst, _⟩ := JauneConsensus.jointStep_electra_ok_iff.mp hstep0
      refine ⟨stateTransition_slot_lt hst, hslot_lt, fun h => ?_⟩
      rw [filledHeaderRoot_eq_jaune]; exact (JauneConsensus.Facts.jointStep_electra_parent_root h hstep0).2
    · refine ⟨hbin, ?_⟩
      obtain ⟨forkSlot, hfk, hle1, hle2, hcases⟩ := JauneConsensus.Facts.jointStep_cross_parent_root hstep0
      unfold BeaconRoots.FirstStepAnchorRoot; dsimp only; rw [← hfk]
      rcases hcases with ⟨hlt1, hfill⟩ | ⟨heq1, heq2, hpar⟩ | ⟨heq1, hlt2, upg, hup, hfill⟩
      · refine .inl ⟨hlt1, hle2, fun hguard => ?_⟩
        rw [filledHeaderRoot_eq_jaune]
        exact hfill (by
          rcases hguard with ⟨h1, _⟩ | h2
          · exact .inl (by omega)
          · exact .inr h2)
      · exact .inr (.inl ⟨congrArg U64.toNat heq1, congrArg U64.toNat heq2, hpar⟩)
      · refine .inr (.inr ⟨congrArg U64.toNat heq1, hlt2, upg, hup, fun hguard => ?_⟩)
        rw [filledHeaderRoot_eq_jaune]; refine hfill ?_
        rcases hguard with h1 | h2
        · have hfk1 : forkSlot.toNat = beacon.slot.toNat := congrArg U64.toNat heq1.symm
          have hslot_up : upg.slot.toNat = beacon.slot.toNat := by
            rw [(JauneConsensus.Facts.upgradeToFulu_cpres_and_frame ccfg hup).2.2.2.1]
          exact .inl (by omega)
        · exact .inr h2
    · refine ⟨hbin, ?_⟩
      obtain ⟨_, _, _, _, _, hst, _⟩ := JauneConsensus.jointStep_fulu_ok_iff.mp hstep0
      refine ⟨stateTransition_slot_lt hst, fun h => ?_⟩
      rw [filledHeaderRoot_eq_jaune]; exact (JauneConsensus.Facts.jointStep_fulu_parent_root h hstep0).2
  · intro k hk
    let prev := v.run.steps[k]'(Nat.lt_of_succ_lt hk); let curr := v.run.steps[k + 1]'hk
    have hsprev : jointStep cfg ccfg bls prev.pre prev.block = .ok prev.post :=
      v.run.steps_jointStep (List.getElem?_eq_getElem (Nat.lt_of_succ_lt hk))
    have hscurr : jointStep cfg ccfg bls curr.pre curr.block = .ok curr.post :=
      v.run.steps_jointStep (List.getElem?_eq_getElem hk)
    rw [← jointRun_step_link v.run hk] at hscurr
    exact ⟨jointBlockInput_parent_root hscurr, fun hcond =>
      (JauneConsensus.Facts.jointStep_consecutive_parent_root hsprev hscurr hcond).2⟩

/-! ## `R_S8_slot`: `genesis_time` preservation, slot-time formula, and slot-window retention -/

def GenEq {P : Preset} {f : CFork} (s s' : BeaconState P f) : Prop := s'.genesis_time = s.genesis_time
private theorem GenEq.refl {P : Preset} {f : CFork} (s : BeaconState P f) : GenEq s s := rfl
private theorem GenEq.trans {P : Preset} {f : CFork} {a b c : BeaconState P f}
    (h1 : GenEq a b) (h2 : GenEq b c) : GenEq a c := Eq.trans h2 h1
private theorem okT_gen {P : Preset} {f : CFork} {γ : Type} {s s1 : BeaconState P f}
    {g : γ → BeaconState P f} {c : M γ} (hp : GenEq s s1)
    (h : JauneConsensus.Facts.Ok c (fun r => GenEq s1 (g r))) :
    JauneConsensus.Facts.Ok c (fun r => GenEq s (g r)) := fun a ha => hp.trans (h a ha)
private theorem list_forIn_gen_proj {P : Preset} {f : CFork} {α β : Type} (π : β → BeaconState P f)
    {xs : List α} {init out : β} {body : α → β → M (ForInStep β)}
    (hb : ∀ a b, JauneConsensus.Facts.Ok (body a b) (fun r => GenEq (π b) (π r.value)))
    (h : forIn xs init body = .ok out) : GenEq (π init) (π out) :=
  JauneConsensus.Facts.list_forIn_rel (fun a b => GenEq (π a) (π b))
    (fun _ => rfl) (fun _ _ _ h1 h2 => h1.trans h2) body (fun a b r hr => hb a b r hr) xs init out h
private theorem array_forIn_gen_proj {P : Preset} {f : CFork} {α β : Type} (π : β → BeaconState P f)
    {xs : Array α} {init out : β} {body : α → β → M (ForInStep β)}
    (hb : ∀ a b, JauneConsensus.Facts.Ok (body a b) (fun r => GenEq (π b) (π r.value)))
    (h : forIn xs init body = .ok out) : GenEq (π init) (π out) := by
  rw [← Array.forIn_toList] at h; exact list_forIn_gen_proj π hb h
private theorem range_forIn_gen_proj {P : Preset} {f : CFork} {β : Type} (π : β → BeaconState P f)
    {xs : Std.Legacy.Range} {init out : β} {body : Nat → β → M (ForInStep β)}
    (hb : ∀ a b, JauneConsensus.Facts.Ok (body a b) (fun r => GenEq (π b) (π r.value)))
    (h : forIn xs init body = .ok out) : GenEq (π init) (π out) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h; exact list_forIn_gen_proj π hb h

section GenMeta
open _root_.Lean _root_.Lean.Meta _root_.Lean.Elab _root_.Lean.Elab.Tactic

private def okPartsG? (e : Expr) : Option (Expr × Expr × Expr) :=
  if e.isAppOfArity ``JauneConsensus.Facts.Ok 3 then some (e.getArg! 0, e.getArg! 1, e.getArg! 2) else none

private def genParts (α Q : Expr) : MetaM (Expr × Expr) :=
  withLocalDeclD `r α fun r => do
    let qr := (mkApp Q r).headBeta
    unless qr.isAppOfArity ``GenEq 4 do throwError "post-condition is not `GenEq _ _`"
    let A := qr.getArg! 2
    if A.containsFVar r.fvarId! then throwError "post-condition base depends on the result"
    pure (A, ← mkLambdaFVars #[r] (qr.getArg! 3))

private def mkPostG (α σ g : Expr) : MetaM Expr := do
  let post ← withLocalDeclD `r α fun r => do mkLambdaFVars #[r] (← mkAppM ``GenEq #[σ, (mkApp g r).headBeta])
  pure post.eta

private def isJpNameG (n : Name) : Bool := n.eraseMacroScopes == `__do_jp

private def findStateG : Nat → Expr → Expr → MetaM (Option Expr)
  | 0, _, _ => pure none
  | fuel + 1, x, T => do
    let T ← whnfR T
    if T.getAppFn.isConstOf ``BeaconState then return some x
    if T.isAppOfArity ``Prod 2 then
      if let some e ← findStateG fuel (← mkAppM ``Prod.fst #[x]) (T.getArg! 0) then return some e
      return ← findStateG fuel (← mkAppM ``Prod.snd #[x]) (T.getArg! 1)
    return none

elab "jp_intro_g" : tactic => withMainContext do
  let g ← getMainGoal; let t ← instantiateMVars (← g.getType)
  let some (α, c, Q) := okPartsG? t | throwError "jp_intro_g"
  let .letE n ty v b _ := c.headBeta | throwError "jp_intro_g"
  unless isJpNameG n do throwError "jp_intro_g"
  let (A, gf) ← genParts α Q; let stTy ← inferType A
  let mkH (jp : Expr) : MetaM Expr := forallTelescope ty fun ys _ => do
    let mut σ := A
    for y in ys do
      if let some stExpr ← findStateG 8 y (← inferType y) then
        if ← isDefEq (← inferType stExpr) stTy then σ := stExpr
    mkForallFVars ys (mkAppN t.getAppFn #[α, (mkAppN jp ys).headBeta, ← mkPostG α σ gf])
  let hk ← mkFreshExprSyntheticOpaqueMVar (← mkH v) `jp_body
  let heTy ← withLocalDeclD n ty fun jp => do
    withLocalDeclD `hjp (← mkH jp) fun _ => mkForallFVars #[jp, ‹_›] (mkAppN t.getAppFn #[α, b.instantiate1 jp, Q])
  let he ← mkFreshExprSyntheticOpaqueMVar heTy `jp_rest
  g.assign (mkApp2 he v hk)
  let (_, hkG) ← hk.mvarId!.intros; let (_, heG) ← he.mvarId!.introN 2
  replaceMainGoal [hkG, heG]

elab "jp_call_g" : tactic => withMainContext do
  let g ← getMainGoal; let t ← instantiateMVars (← g.getType)
  let some (α, c, Q) := okPartsG? t | throwError "jp_call_g"
  let c := c.headBeta; let fn := c.getAppFn
  unless fn.isFVar do throwError "jp_call_g"
  let (A, _) ← genParts α Q
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isForall do continue
    let r : Option MVarId ← try
        let (mvs, _, body) ← forallMetaTelescope ty
        let some (_, c', post) := okPartsG? body | throwError "not Ok"
        unless c'.getAppFn == fn && (← isDefEq c' c) do throwError "mismatch"
        let (σ, _) ← genParts α (← instantiateMVars post)
        let hp ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``GenEq #[A, σ]) `jp_gen
        let pf ← mkAppM ``okT_gen #[hp, mkAppN d.toExpr mvs]
        unless ← isDefEq (← inferType pf) t do throwError "type differs"
        g.assign (← instantiateMVars pf); pure (some hp.mvarId!)
      catch _ => pure none
    if let some hpG := r then replaceMainGoal [hpG]; return
  throwError "jp_call_g"

elab "loop_gen " h:ident : tactic => withMainContext do
  let g ← getMainGoal; let t ← instantiateMVars (← g.getType)
  let some (α, c, Q) := okPartsG? t | throwError "loop_gen"
  let d ← getLocalDeclFromUserName h.getId
  let some (_, lhs, rhs) := (← instantiateMVars d.type).eq? | throwError "loop_gen"
  unless lhs.getAppFn.isConstOf ``ForIn.forIn && lhs.getAppNumArgs ≥ 3 && rhs.isAppOfArity ``Except.ok 3 do
    throwError "loop_gen"
  let n := lhs.getAppNumArgs; let xs := lhs.getArg! (n - 3); let init := lhs.getArg! (n - 2); let body := lhs.getArg! (n - 1)
  let ρ ← whnfR (← inferType xs)
  let lem ← if ρ.isAppOf ``List then pure ``list_forIn_gen_proj
    else if ρ.isAppOf ``Array then pure ``array_forIn_gen_proj
    else if ρ.isConstOf ``Std.Legacy.Range then pure ``range_forIn_gen_proj
    else throwError "loop_gen"
  let β ← inferType init
  let π ← withLocalDeclD `x β fun x => do
    let some e ← findStateG 8 x β | throwError "loop_gen"
    mkLambdaFVars #[x] e
  let (A, gf) ← genParts α Q; let stepTy ← mkAppM ``ForInStep #[β]
  let hbTy ← forallTelescope (← inferType body) fun as _ => do
    let #[_, b] := as | throwError "loop_gen"
    let post ← withLocalDeclD `r stepTy fun r => do
      mkLambdaFVars #[r] (← mkAppM ``GenEq #[π.beta #[b], π.beta #[← mkAppM ``ForInStep.value #[r]]])
    mkForallFVars as (mkAppN t.getAppFn #[stepTy, (mkAppN body as).headBeta, post])
  let hb ← mkFreshExprSyntheticOpaqueMVar hbTy `loop_body
  let hp ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``GenEq #[A, π.beta #[init]]) `loop_pre
  let rest ← mkFreshExprSyntheticOpaqueMVar (mkAppN t.getAppFn #[α, c, ← mkPostG α (π.beta #[rhs.appArg!]) gf]) `loop_rest
  let full ← mkAppM ``okT_gen #[← mkAppM ``GenEq.trans #[hp, ← mkAppM lem #[π, hb, d.toExpr]], rest]
  unless ← isDefEq (← inferType full) t do throwError "loop_gen"
  g.assign full; let (_, hbG) ← hb.mvarId!.introN 2
  replaceMainGoal [hp.mvarId!, hbG, rest.mvarId!]

elab "let_beta_head_g" : tactic => withMainContext do
  let g ← getMainGoal; let t ← instantiateMVars (← g.getType)
  let some (α, c, Q) := okPartsG? t | throwError "not Ok"
  let c' := c.headBeta
  if let .letE n _ v b _ := c' then
    if !isJpNameG n then replaceMainGoal [← g.change (mkAppN t.getAppFn #[α, b.instantiate1 v, Q])]; return
  if c'.isAppOfArity ``letFun 4 then
    replaceMainGoal [← g.change (mkAppN t.getAppFn #[α, (mkApp (c'.getArg! 3) (c'.getArg! 2)).headBeta, Q])]; return
  if c != c' then replaceMainGoal [← g.change (mkAppN t.getAppFn #[α, c', Q])]; return
  throwError "not let/beta"

elab "is_small_g " x:ident : tactic => withMainContext do
  let t ← whnfR (← instantiateMVars (← getLocalDeclFromUserName x.getId).type)
  unless t.getAppFn.isConstOf ``Option || t.getAppFn.isConstOf ``Prod || t.getAppFn.isConstOf ``Bool do throwError "not small"

end GenMeta

syntax "gen_of " ident : tactic
syntax "gen_close" : tactic
macro_rules | `(tactic| gen_close) => `(tactic| first | with_reducible exact GenEq.refl _ | rfl | (unfold GenEq; split <;> rfl))
syntax "gstep" : tactic
macro_rules | `(tactic| gstep) => `(tactic| first
  | jp_intro_g | let_beta_head_g | (jp_call_g; gen_close)
  | with_reducible exact JauneConsensus.Facts.ok_head | with_reducible exact JauneConsensus.Facts.ok_throw
  | with_reducible exact JauneConsensus.Facts.ok_throw_bind
  | with_reducible exact JauneConsensus.Facts.ok_pure (GenEq.refl _)
  | (dsimp only; exact JauneConsensus.Facts.ok_pure (GenEq.refl _))
  | (refine JauneConsensus.Facts.ok_pure ?_; try dsimp -zeta only [ForInStep.value]; gen_close)
  | exact JauneConsensus.Facts.ok_of fun _ hh => by gen_of hh
  | (refine JauneConsensus.Facts.ok_of fun _ hh => ?_; (have h2 := by gen_of hh); exact GenEq.trans (by gen_close) h2)
  | with_reducible apply JauneConsensus.Facts.ok_bind_ite
  | (with_reducible apply JauneConsensus.Facts.ok_bind; intro _ hx; loop_gen hx; gen_close)
  | (with_reducible apply JauneConsensus.Facts.ok_bind; intro _ hx
     first | (refine okT_gen (GenEq.trans ?_ (by gen_of hx)) ?_; gen_close) | skip)
  | (with_reducible apply JauneConsensus.Facts.ok_ite <;> intro _)
  | (with_reducible apply JauneConsensus.Facts.ok_dite <;> intro _)
  | (set_option simprocs false in dsimp -zeta only)
  | (rename_i x _; is_small_g x; cases x; all_goals (set_option simprocs false in dsimp -zeta only))
  | split)

private theorem increaseBalance_gen {P : Preset} {f : CFork} {s s' : BeaconState P f}
    {i : ValidatorIndex} {d : Gwei} (h : increaseBalance s i d = .ok s') : GenEq s s' := by
  revert s' h; show JauneConsensus.Facts.Ok (increaseBalance s i d) (GenEq s); unfold increaseBalance; repeat gstep
private theorem decreaseBalance_gen {P : Preset} {f : CFork} {s s' : BeaconState P f}
    {i : ValidatorIndex} {d : Gwei} (h : decreaseBalance s i d = .ok s') : GenEq s s' := by
  revert s' h; show JauneConsensus.Facts.Ok (decreaseBalance s i d) (GenEq s); unfold decreaseBalance; repeat gstep
private theorem exitChurn_gen {P : Preset} {f : CFork} (cfg : Config) {s : BeaconState P f} {b : Gwei}
    {p : BeaconState P f × Epoch} (h : computeExitEpochAndUpdateChurn cfg s b = .ok p) : GenEq s p.1 := by
  unfold computeExitEpochAndUpdateChurn at h; simp only [bind, Except.bind, pure, Except.pure] at h
  (repeat' split at h); all_goals first | (cases h; rfl) | cases h
private theorem setPendingDeposits_gen {P : Preset} {f : CFork} {s s' : BeaconState P f}
    {l : SszList PendingDeposit P.PENDING_DEPOSITS_LIMIT} (h : s.setPendingDeposits l = .ok s') : GenEq s s' := by
  revert s' h; show JauneConsensus.Facts.Ok (s.setPendingDeposits l) (GenEq s); unfold BeaconState.setPendingDeposits; repeat gstep
private theorem setPendingPartialWithdrawals_gen {P : Preset} {f : CFork} {s s' : BeaconState P f}
    {l : SszList PendingPartialWithdrawal P.PENDING_PARTIAL_WITHDRAWALS_LIMIT} (h : s.setPendingPartialWithdrawals l = .ok s') : GenEq s s' := by
  revert s' h; show JauneConsensus.Facts.Ok (s.setPendingPartialWithdrawals l) (GenEq s); unfold BeaconState.setPendingPartialWithdrawals; repeat gstep
private theorem setPendingConsolidations_gen {P : Preset} {f : CFork} {s s' : BeaconState P f}
    {l : SszList PendingConsolidation P.PENDING_CONSOLIDATIONS_LIMIT} (h : s.setPendingConsolidations l = .ok s') : GenEq s s' := by
  revert s' h; show JauneConsensus.Facts.Ok (s.setPendingConsolidations l) (GenEq s); unfold BeaconState.setPendingConsolidations; repeat gstep
private theorem setProposerLookahead_gen {P : Preset} {f : CFork} {s s' : BeaconState P f}
    {l : SszVector ValidatorIndex ((P.MIN_SEED_LOOKAHEAD + 1) * P.SLOTS_PER_EPOCH)} (h : s.setProposerLookahead l = .ok s') : GenEq s s' := by
  revert s' h; show JauneConsensus.Facts.Ok (s.setProposerLookahead l) (GenEq s); unfold BeaconState.setProposerLookahead; repeat gstep
private theorem setDepositBalanceToConsume_gen {P : Preset} {f : CFork} {s s' : BeaconState P f}
    {x : Gwei} (h : s.setDepositBalanceToConsume x = .ok s') : GenEq s s' := by
  revert s' h; show JauneConsensus.Facts.Ok (s.setDepositBalanceToConsume x) (GenEq s); unfold BeaconState.setDepositBalanceToConsume; repeat gstep
private theorem setConsolidationBalanceToConsume_gen {P : Preset} {f : CFork} {s s' : BeaconState P f}
    {x : Gwei} (h : s.setConsolidationBalanceToConsume x = .ok s') : GenEq s s' := by
  revert s' h; show JauneConsensus.Facts.Ok (s.setConsolidationBalanceToConsume x) (GenEq s); unfold BeaconState.setConsolidationBalanceToConsume; repeat gstep
private theorem addValidatorToRegistry_gen {P : Preset} {f : CFork} {s s' : BeaconState P f}
    {pk : BLSPubkey} {wc : Bytes32} {amt : U64} (h : addValidatorToRegistry s pk wc amt = .ok s') : GenEq s s' := by
  revert s' h; show JauneConsensus.Facts.Ok (addValidatorToRegistry s pk wc amt) (GenEq s); unfold addValidatorToRegistry; repeat gstep

macro_rules | `(tactic| gen_of $h) => `(tactic| with_reducible exact increaseBalance_gen $h)
macro_rules | `(tactic| gen_of $h) => `(tactic| with_reducible exact decreaseBalance_gen $h)
macro_rules | `(tactic| gen_of $h) => `(tactic| with_reducible exact exitChurn_gen _ $h)
macro_rules | `(tactic| gen_of $h) => `(tactic| with_reducible exact setPendingDeposits_gen $h)
macro_rules | `(tactic| gen_of $h) => `(tactic| with_reducible exact setPendingPartialWithdrawals_gen $h)
macro_rules | `(tactic| gen_of $h) => `(tactic| with_reducible exact setPendingConsolidations_gen $h)
macro_rules | `(tactic| gen_of $h) => `(tactic| with_reducible exact setProposerLookahead_gen $h)
macro_rules | `(tactic| gen_of $h) => `(tactic| with_reducible exact setDepositBalanceToConsume_gen $h)
macro_rules | `(tactic| gen_of $h) => `(tactic| with_reducible exact setConsolidationBalanceToConsume_gen $h)
macro_rules | `(tactic| gen_of $h) => `(tactic| with_reducible exact addValidatorToRegistry_gen $h)

private theorem initiateValidatorExit_gen {P : Preset} {f : CFork} (cfg : Config)
    {s s' : BeaconState P f} {idx : ValidatorIndex} (h : initiateValidatorExit cfg s idx = .ok s') : GenEq s s' := by
  unfold initiateValidatorExit at h; obtain ⟨_, _, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h; dsimp only at h
  split at h
  · cases h; rfl
  · split at h
    · obtain ⟨⟨st1, q⟩, hq, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
      iterate 3 obtain ⟨_, _, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
      cases h; exact exitChurn_gen cfg hq
    · iterate 4 obtain ⟨_, _, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
      split at h
      · obtain ⟨_, _, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
        obtain ⟨⟨st1, q'⟩, hq', h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
        cases hq'
        (iterate 3 obtain ⟨_, _, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h)
        cases h; rfl
      · obtain ⟨⟨st1, q'⟩, hq', h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
        cases hq'
        (iterate 3 obtain ⟨_, _, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h)
        cases h; rfl

macro_rules | `(tactic| gen_of $h) => `(tactic| with_reducible exact initiateValidatorExit_gen _ $h)

private theorem slashValidator_gen {P : Preset} {f : CFork} (cfg : Config) {s s' : BeaconState P f}
    {idx : ValidatorIndex} {wb : Option ValidatorIndex} (h : slashValidator cfg s idx wb = .ok s') : GenEq s s' := by
  revert s' h; show JauneConsensus.Facts.Ok (slashValidator cfg s idx wb) (GenEq s); unfold slashValidator; repeat gstep
private theorem queueExcessActiveBalance_gen {P : Preset} {f : CFork} {s s' : BeaconState P f}
    {idx : ValidatorIndex} (h : queueExcessActiveBalance s idx = .ok s') : GenEq s s' := by
  revert s' h; show JauneConsensus.Facts.Ok (queueExcessActiveBalance s idx) (GenEq s); unfold queueExcessActiveBalance; repeat gstep
macro_rules | `(tactic| gen_of $h) => `(tactic| with_reducible exact slashValidator_gen _ $h)
macro_rules | `(tactic| gen_of $h) => `(tactic| with_reducible exact queueExcessActiveBalance_gen $h)
private theorem switchToCompoundingValidator_gen {P : Preset} {f : CFork} {s s' : BeaconState P f}
    {idx : ValidatorIndex} (h : switchToCompoundingValidator s idx = .ok s') : GenEq s s' := by
  revert s' h; show JauneConsensus.Facts.Ok (switchToCompoundingValidator s idx) (GenEq s); unfold switchToCompoundingValidator; repeat gstep
macro_rules | `(tactic| gen_of $h) => `(tactic| with_reducible exact switchToCompoundingValidator_gen $h)
private theorem weighJustificationAndFinalization_gen {P : Preset} {f : CFork} {s s' : BeaconState P f}
    {t p c : Gwei} (h : weighJustificationAndFinalization s t p c = .ok s') : GenEq s s' := by
  revert s' h; show JauneConsensus.Facts.Ok (weighJustificationAndFinalization s t p c) (GenEq s); unfold weighJustificationAndFinalization; repeat gstep
macro_rules | `(tactic| gen_of $h) => `(tactic| with_reducible exact weighJustificationAndFinalization_gen $h)

private theorem foldlM_gen {P : Preset} {f : CFork} {α : Type}
    {step : BeaconState P f → α → M (BeaconState P f)} (hstep : ∀ s a s', step s a = .ok s' → GenEq s s') :
    ∀ (xs : List α) {s s' : BeaconState P f}, List.foldlM step s xs = .ok s' → GenEq s s'
  | [], s, s', h => by cases h; rfl
  | x :: xs, s, s', h => by
    rw [List.foldlM_cons] at h; obtain ⟨mid, h1, h2⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
    exact (hstep s x mid h1).trans (foldlM_gen hstep xs h2)

private theorem applyPendingDeposit_gen {P : Preset} {f : CFork} (ctx : Ctx) {s s' : BeaconState P f}
    {d : PendingDeposit} (h : applyPendingDeposit ctx s d = .ok s') : GenEq s s' := by
  revert s' h; show JauneConsensus.Facts.Ok (applyPendingDeposit ctx s d) (GenEq s); unfold applyPendingDeposit; repeat gstep

private theorem processPendingDeposits_gen {P : Preset} {f : CFork} (ctx : Ctx)
    {s s' : BeaconState P f} (h : processPendingDeposits ctx s = .ok s') : GenEq s s' := by
  rw [JauneConsensus.Facts.processPendingDeposits_eq] at h; dsimp only at h
  iterate 8 obtain ⟨_, _, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  obtain ⟨out, hloop, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  obtain ⟨_, applied, _, _, _, hfold, _, _, _⟩ := JauneConsensus.Facts.pendingDepositsLoop_fate _ _ _ hloop
  have g1 : GenEq s out.2.2.2.2 := foldlM_gen (fun _ _ _ ha => applyPendingDeposit_gen ctx ha) applied hfold
  obtain ⟨_, _, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  obtain ⟨st1, hst1, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  have g3 : GenEq st1 s' := by
    split at h
    · obtain ⟨_, _, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h; exact setDepositBalanceToConsume_gen h
    · exact setDepositBalanceToConsume_gen h
  exact g1.trans ((setPendingDeposits_gen hst1).trans g3)

private theorem processEpoch_gen {P : Preset} {f : CFork} (ctx : Ctx) (hf : f.atLeast .electra = true)
    {s s' : BeaconState P f} (h : processEpoch ctx s = .ok s') : GenEq s s' := by
  have g1 : ∀ {a b : BeaconState P f}, processJustificationAndFinalization ctx.cfg a = .ok b → GenEq a b := fun {a b} hab => by
    revert b hab; show JauneConsensus.Facts.Ok (processJustificationAndFinalization ctx.cfg a) (GenEq a); unfold processJustificationAndFinalization; repeat gstep
  have g2 : ∀ {a b : BeaconState P f}, processInactivityUpdates ctx.cfg a = .ok b → GenEq a b := fun {a b} hab => by
    revert b hab; show JauneConsensus.Facts.Ok (processInactivityUpdates ctx.cfg a) (GenEq a); unfold processInactivityUpdates; repeat gstep
  have g3 : ∀ {a b : BeaconState P f}, processRewardsAndPenalties ctx.cfg a = .ok b → GenEq a b := fun {a b} hab => by
    revert b hab; show JauneConsensus.Facts.Ok (processRewardsAndPenalties ctx.cfg a) (GenEq a); unfold processRewardsAndPenalties; repeat gstep
  have g4 : ∀ {a b : BeaconState P f}, processRegistryUpdates ctx.cfg a = .ok b → GenEq a b := fun {a b} hab => by
    unfold processRegistryUpdates at hab; rw [ite_eq_left hf] at hab
    revert b hab; show JauneConsensus.Facts.Ok (processRegistryUpdatesElectra ctx.cfg a) (GenEq a); unfold processRegistryUpdatesElectra; repeat gstep
  have g5 : ∀ {a b : BeaconState P f}, processSlashings ctx.cfg a = .ok b → GenEq a b := fun {a b} hab => by
    revert b hab; show JauneConsensus.Facts.Ok (processSlashings ctx.cfg a) (GenEq a); unfold processSlashings; repeat gstep
  have g6 : ∀ {a b : BeaconState P f}, processEth1DataReset ctx.cfg a = .ok b → GenEq a b := fun {a b} hab => by
    revert b hab; show JauneConsensus.Facts.Ok (processEth1DataReset ctx.cfg a) (GenEq a); unfold processEth1DataReset; repeat gstep
  have g8 : ∀ {a b : BeaconState P f}, processPendingConsolidations ctx.cfg a = .ok b → GenEq a b := fun {a b} hab => by
    revert b hab; show JauneConsensus.Facts.Ok (processPendingConsolidations ctx.cfg a) (GenEq a); unfold processPendingConsolidations; repeat gstep
  have g9 : ∀ {a b : BeaconState P f}, processEffectiveBalanceUpdates ctx.cfg a = .ok b → GenEq a b := fun {a b} hab => by
    unfold processEffectiveBalanceUpdates at hab
    (iterate 8 obtain ⟨_, _, hab⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hab); cases hab; rfl
  have g10 : ∀ {a b : BeaconState P f}, processSlashingsReset ctx.cfg a = .ok b → GenEq a b := fun {a b} hab => by
    unfold processSlashingsReset at hab
    (iterate 5 obtain ⟨_, _, hab⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hab); cases hab; rfl
  have g11 : ∀ {a b : BeaconState P f}, processRandaoMixesReset ctx.cfg a = .ok b → GenEq a b := fun {a b} hab => by
    unfold processRandaoMixesReset at hab
    (iterate 6 obtain ⟨_, _, hab⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hab); cases hab; rfl
  have g12 : ∀ {a b : BeaconState P f}, processHistoricalSummariesUpdate ctx.cfg a = .ok b → GenEq a b := fun {a b} hab => by
    unfold processHistoricalSummariesUpdate at hab
    (iterate 4 obtain ⟨_, _, hab⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hab)
    split at hab; · obtain ⟨_, _, hab⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hab; cases hab; rfl
    · cases hab; rfl
  have g13 : ∀ {a b : BeaconState P f}, processParticipationFlagUpdates ctx.cfg a = .ok b → GenEq a b := fun {a b} hab => by
    unfold processParticipationFlagUpdates at hab
    obtain ⟨_, _, hab⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hab; cases hab; rfl
  have g14 : ∀ {a b : BeaconState P f}, processSyncCommitteeUpdates ctx a = .ok b → GenEq a b := fun {a b} hab => by
    unfold processSyncCommitteeUpdates at hab
    (iterate 4 obtain ⟨_, _, hab⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hab)
    split at hab; · obtain ⟨_, _, hab⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hab; cases hab; rfl
    · cases hab; rfl
  have g15 : ∀ {a b : BeaconState P f}, processProposerLookahead ctx.cfg a = .ok b → GenEq a b := fun {a b} hab => by
    unfold processProposerLookahead at hab
    (iterate 9 obtain ⟨_, _, hab⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hab)
    exact setProposerLookahead_gen hab
  unfold processEpoch at h
  dsimp only at h
  obtain ⟨s1, h1, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  obtain ⟨s2, h2, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  obtain ⟨s3, h3, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  obtain ⟨s4, h4, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  obtain ⟨s5, h5, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  obtain ⟨s6, h6, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  simp only [hf, ↓reduceIte] at h
  obtain ⟨m, hm1, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  obtain ⟨s7, h7, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  have h7' : GenEq s6 s7 := (processPendingDeposits_gen ctx hm1).trans (g8 h7)
  obtain ⟨s8, h8, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  obtain ⟨s9, h9, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  obtain ⟨s10, h10, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  obtain ⟨s11, h11, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  obtain ⟨s12, h12, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  obtain ⟨s13, h13, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  have h14 : GenEq s13 s' := by split at h; exact g15 h; cases h; rfl
  exact (g1 h1).trans ((g2 h2).trans ((g3 h3).trans ((g4 h4).trans ((g5 h5).trans
    ((g6 h6).trans (h7'.trans ((g9 h8).trans ((g10 h9).trans ((g11 h10).trans
    ((g12 h11).trans ((g13 h12).trans ((g14 h13).trans h14))))))))))))

macro_rules | `(tactic| gen_of $h) => `(tactic| with_reducible exact processEpoch_gen _ (by decide) $h)

private theorem processSlot_gen {P : Preset} {f : CFork} {s s' : BeaconState P f}
    (h : processSlot s = .ok s') : GenEq s s' := by
  revert s' h; show JauneConsensus.Facts.Ok (processSlot s) (GenEq s); unfold processSlot; repeat gstep

macro_rules | `(tactic| gen_of $h) => `(tactic| with_reducible exact processSlot_gen $h)

private theorem processSlots_gen {P : Preset} {f : CFork} (ctx : Ctx) (hf : f.atLeast .electra = true)
    {s s' : BeaconState P f} {slot : Slot}
    (h : JauneConsensus.processSlots ctx s slot = .ok s') : GenEq s s' := by
  unfold JauneConsensus.processSlots JauneConsensus.processSlotsWith at h
  obtain ⟨_, _, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  set_option simprocs false in dsimp only at h
  obtain ⟨_, h, hpure⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  cases hpure
  exact range_forIn_gen_proj id (fun _ st r hr => by
    obtain ⟨st1, hst1, hr⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hr
    obtain ⟨_, _, hr⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hr
    obtain ⟨_, _, hr⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hr
    have g1 := processSlot_gen hst1
    split at hr
    · obtain ⟨st2, hst2, hr⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hr
      cases hr; exact g1.trans ((processEpoch_gen ctx hf hst2).trans (rfl : GenEq st2 _))
    · cases hr; exact g1) h

private theorem consolidationChurn_gen {P : Preset} {f : CFork} (cfg : Config) {s : BeaconState P f} {b : Gwei}
    {p : BeaconState P f × Epoch} (h : computeConsolidationEpochAndUpdateChurn cfg s b = .ok p) : GenEq s p.1 := by
  obtain ⟨_, _, hr⟩ := JauneConsensus.Facts.computeConsolidationEpoch_frame h
  rw [hr]; rfl

macro_rules | `(tactic| gen_of $h) => `(tactic| with_reducible exact consolidationChurn_gen _ $h)

private theorem processProposerSlashing_gen {P : Preset} {f : CFork} (ctx : Ctx)
    {s s' : BeaconState P f} {ps : ProposerSlashing} (h : processProposerSlashing ctx s ps = .ok s') : GenEq s s' := by
  revert s' h; show JauneConsensus.Facts.Ok (processProposerSlashing ctx s ps) (GenEq s); unfold processProposerSlashing; repeat gstep

private theorem processAttesterSlashing_gen {P : Preset} {f : CFork} (ctx : Ctx)
    {s s' : BeaconState P f} {a : AttesterSlashing P f} (h : processAttesterSlashing ctx s a = .ok s') : GenEq s s' := by
  revert s' h; show JauneConsensus.Facts.Ok (processAttesterSlashing ctx s a) (GenEq s); unfold processAttesterSlashing; repeat gstep

private theorem processAttestation_gen {P : Preset} {f : CFork} (ctx : Ctx)
    {s s' : BeaconState P f} {a : Attestation P f} (h : processAttestation ctx s a = .ok s') : GenEq s s' := by
  revert s' h; show JauneConsensus.Facts.Ok (processAttestation ctx s a) (GenEq s); unfold processAttestation; repeat gstep

private theorem processDeposit_gen {P : Preset} {f : CFork} (ctx : Ctx)
    {s s' : BeaconState P f} {d : Deposit} (h : processDeposit ctx s d = .ok s') : GenEq s s' := by
  revert s' h; show JauneConsensus.Facts.Ok (processDeposit ctx s d) (GenEq s); unfold processDeposit applyDeposit; repeat gstep

private theorem processVoluntaryExit_gen {P : Preset} {f : CFork} (ctx : Ctx)
    {s s' : BeaconState P f} {ve : SignedVoluntaryExit} (h : processVoluntaryExit ctx s ve = .ok s') : GenEq s s' := by
  revert s' h; show JauneConsensus.Facts.Ok (processVoluntaryExit ctx s ve) (GenEq s); unfold processVoluntaryExit; repeat gstep

private theorem processBlsToExecutionChange_gen {P : Preset} {f : CFork} (ctx : Ctx)
    {s s' : BeaconState P f} {bl : SignedBLSToExecutionChange} (h : processBlsToExecutionChange ctx s bl = .ok s') : GenEq s s' := by
  revert s' h; show JauneConsensus.Facts.Ok (processBlsToExecutionChange ctx s bl) (GenEq s); unfold processBlsToExecutionChange; repeat gstep

private theorem processDepositRequest_gen {P : Preset} {f : CFork}
    {s s' : BeaconState P f} {dr : DepositRequest} (h : processDepositRequest s dr = .ok s') : GenEq s s' := by
  unfold processDepositRequest at h
  set_option simprocs false in dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
    split at h
    · obtain ⟨s1, hs1, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
      obtain ⟨_, _, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
      obtain ⟨_, _, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
      have hs1' : GenEq s s1 := by
        unfold BeaconState.setDepositRequestsStartIndex at hs1
        obtain ⟨_, _, hs1⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hs1
        cases hs1; rfl
      exact hs1'.trans (setPendingDeposits_gen h)
    · obtain ⟨_, _, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
      obtain ⟨_, _, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
      exact setPendingDeposits_gen h
  · obtain ⟨_, _, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
    exact setPendingDeposits_gen h

private theorem processWithdrawalRequest_gen {P : Preset} {f : CFork} (cfg : Config)
    {s s' : BeaconState P f} {wr : WithdrawalRequest} (h : processWithdrawalRequest cfg s wr = .ok s') : GenEq s s' := by
  revert s' h; show JauneConsensus.Facts.Ok (processWithdrawalRequest cfg s wr) (GenEq s); unfold processWithdrawalRequest; repeat gstep

private theorem processConsolidationRequest_gen {P : Preset} {f : CFork} (cfg : Config)
    {s s' : BeaconState P f} {cr : ConsolidationRequest} (h : processConsolidationRequest cfg s cr = .ok s') : GenEq s s' := by
  revert s' h; show JauneConsensus.Facts.Ok (processConsolidationRequest cfg s cr) (GenEq s); unfold processConsolidationRequest; repeat gstep

private theorem processOperations_gen {P : Preset} {f : CFork} (ctx : Ctx) (hf : f.atLeast .electra = true)
    {s s' : BeaconState P f} {body : BeaconBlockBody P f} (h : processOperations ctx s body = .ok s') : GenEq s s' := by
  rw [JauneConsensus.Facts.processOperations_split_all ctx s body hf] at h
  obtain ⟨s1, h1, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  obtain ⟨s2, h2, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  obtain ⟨s3, h3, h4⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  have hpre : ∀ {a b : BeaconState P f}, JauneConsensus.Facts.preDeposits ctx a body = .ok b → GenEq a b := by
    intro a b hp
    have hbody : ∀ {s0 : BeaconState P f},
        (do let mut st := s0
            for op in body.proposer_slashings.toArray do st ← processProposerSlashing ctx st op
            for op in body.attester_slashings.toArray do st ← processAttesterSlashing ctx st op
            for op in body.attestations.toArray do st ← processAttestation ctx st op
            for op in body.deposits.toArray do st ← processDeposit ctx st op
            for op in body.voluntary_exits.toArray do st ← processVoluntaryExit ctx st op
            for op in body.bls_to_execution_changes.toArray do st ← processBlsToExecutionChange ctx st op
            pure st : M (BeaconState P f)) = .ok b → GenEq s0 b := by
      intro s0 hb
      simp only [JauneConsensus.Facts.forArr_yield] at hb
      obtain ⟨r1, e1, hb⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hb
      obtain ⟨r2, e2, hb⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hb
      obtain ⟨r3, e3, hb⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hb
      obtain ⟨r4, e4, hb⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hb
      obtain ⟨r5, e5, hb⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hb
      obtain ⟨r6, e6, hpure⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hb
      cases hpure
      exact (foldlM_gen (fun _ _ _ => processProposerSlashing_gen ctx) _ e1).trans
        ((foldlM_gen (fun _ _ _ => processAttesterSlashing_gen ctx) _ e2).trans
        ((foldlM_gen (fun _ _ _ => processAttestation_gen ctx) _ e3).trans
        ((foldlM_gen (fun _ _ _ => processDeposit_gen ctx) _ e4).trans
        ((foldlM_gen (fun _ _ _ => processVoluntaryExit_gen ctx) _ e5).trans
        (foldlM_gen (fun _ _ _ => processBlsToExecutionChange_gen ctx) _ e6)))))
    unfold JauneConsensus.Facts.preDeposits at hp
    split at hp
    · obtain ⟨_, _, hp⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hp; exact hbody hp
    · simp only [hf, Bool.not_true, Bool.false_eq_true, ite_false] at hp
      obtain ⟨startIndex, _, hp⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hp
      by_cases hlim : a.eth1_deposit_index <
          (if a.eth1_data.deposit_count < startIndex then a.eth1_data.deposit_count else startIndex)
      · rw [ite_eq_left hlim] at hp
        obtain ⟨_, _, hp⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hp
        obtain ⟨_, _, hp⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hp
        exact hbody hp
      · rw [ite_eq_right hlim] at hp
        obtain ⟨_, _, hp⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hp
        exact hbody hp
  have g1 := hpre h1
  have g2 := foldlM_gen (fun _ _ _ => processDepositRequest_gen) _ h2
  have g3 := foldlM_gen (fun _ _ _ => processWithdrawalRequest_gen ctx.cfg) _ h3
  have g4 := foldlM_gen (fun _ _ _ => processConsolidationRequest_gen ctx.cfg) _ h4
  exact g1.trans (g2.trans (g3.trans g4))

private theorem processBlockHeader_gen {P : Preset} {f : CFork} {s s' : BeaconState P f}
    {blk : BeaconBlock P f} (h : processBlockHeader s blk = .ok s') : GenEq s s' := by
  revert s' h; show JauneConsensus.Facts.Ok (processBlockHeader s blk) (GenEq s)
  unfold processBlockHeader; repeat gstep

private theorem processExecutionPayload_gen_and_time {P : Preset} {f : CFork} (ctx : Ctx)
    {a b : BeaconState P f} {bd : BeaconBlockBody P f}
    (hab : processExecutionPayload ctx a bd = .ok b) :
    GenEq a b ∧ computeTimeAtSlotOf ctx.cfg a.genesis_time a.slot = .ok bd.execution_payload.timestamp := by
  unfold processExecutionPayload at hab
  (iterate 4 obtain ⟨_, _, hab⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hab)
  obtain ⟨t, ht, hab⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hab
  obtain ⟨_, hreqt, hab⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hab
  have hteq : bd.execution_payload.timestamp = t := beq_iff_eq.mp (require_eq_ok_iff.mp hreqt)
  have g3 : GenEq a b := by
    simp only [bind, Except.bind, pure, Except.pure, require] at hab
    (repeat' split at hab); all_goals first | (cases hab; rfl) | cases hab
  refine ⟨g3, ?_⟩
  unfold computeTimeAtSlot at ht; rw [hteq]; exact ht

private theorem processBlock_gen_and_time {P : Preset} {f : CFork} (ctx : Ctx)
    (hf : f.atLeast .electra = true) {s s' : BeaconState P f} {blk : BeaconBlock P f}
    (h : processBlock ctx s blk = .ok s') :
    GenEq s s' ∧
      computeTimeAtSlotOf ctx.cfg s.genesis_time blk.slot =
        .ok blk.body.execution_payload.timestamp := by
  have gw : ∀ {a b : BeaconState P f} {pl : ExecutionPayload P}, JauneConsensus.processWithdrawals a pl = .ok b → GenEq a b := fun {a b pl} hab => by
    revert b hab; show JauneConsensus.Facts.Ok (JauneConsensus.processWithdrawals a pl) (GenEq a); unfold JauneConsensus.processWithdrawals; repeat gstep
  have gr : ∀ {a b : BeaconState P f} {bd : BeaconBlockBody P f}, processRandao ctx a bd = .ok b → GenEq a b := fun {a b bd} hab => by
    revert b hab; show JauneConsensus.Facts.Ok (processRandao ctx a bd) (GenEq a); unfold processRandao; repeat gstep
  have ge : ∀ {a b : BeaconState P f} {bd : BeaconBlockBody P f}, processEth1Data a bd = .ok b → GenEq a b := fun {a b bd} hab => by
    revert b hab; show JauneConsensus.Facts.Ok (processEth1Data a bd) (GenEq a); unfold processEth1Data; repeat gstep
  have gs : ∀ {a b : BeaconState P f} {sa : SyncAggregate P}, processSyncAggregate ctx a sa = .ok b → GenEq a b := fun {a b sa} hab => by
    unfold processSyncAggregate at hab
    set_option simprocs false in dsimp only at hab
    have htail : ∀ {m : M (Array U64)} {bits : Array Bool} {r1 r2 : U64},
        (do let ci ← m
            let mut st := a
            for (idx, bit) in ci.zip bits do
              if bit then
                st ← increaseBalance st idx r1
                st ← increaseBalance st (← getBeaconProposerIndex st) r2
              else st ← decreaseBalance st idx r1
            pure st : M (BeaconState P f)) = .ok b → GenEq a b := by
      intro m bits r1 r2 ht
      obtain ⟨_, _, ht⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp ht
      obtain ⟨s', hs', ht⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp ht
      cases ht
      exact array_forIn_gen_proj id (fun ⟨idx, bit⟩ s r hr => by
        dsimp only at hr; split at hr
        · obtain ⟨s1, hs1, hr⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hr
          obtain ⟨_, _, hr⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hr
          obtain ⟨s2, hs2, hr⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hr
          cases hr; exact (increaseBalance_gen hs1).trans (increaseBalance_gen hs2)
        · obtain ⟨s1, hs1, hr⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hr
          cases hr; exact decreaseBalance_gen hs1) hs'
    split at hab
    · iterate 23 obtain ⟨_, _, hab⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hab
      exact htail hab
    · split at hab
      · iterate 26 obtain ⟨_, _, hab⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hab
        exact htail hab
      · iterate 23 obtain ⟨_, _, hab⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hab
        exact htail hab
  unfold processBlock processBlockWith at h
  obtain ⟨s1, h1, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  obtain ⟨s2, h2, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  obtain ⟨s3, h3, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  obtain ⟨s4, h4, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  obtain ⟨s5, h5, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  obtain ⟨s6, h6, h7⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  have ⟨_, hslot1, _, _, _⟩ := JauneConsensus.Facts.processBlockHeader_corpusPres h1
  have hslot_blk : s1.slot = blk.slot := by
    unfold processBlockHeader at h1
    obtain ⟨_, hreq, _⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h1
    exact hslot1.trans (beq_iff_eq.mp (require_eq_ok_iff.mp hreq)).symm
  have g1 := processBlockHeader_gen h1
  have hslot2 : s2.slot = s1.slot := (JauneConsensus.Facts.processWithdrawals_csub h2).slot_eq
  have g2 := gw h2
  have ⟨g3, htime⟩ := processExecutionPayload_gen_and_time ctx h3
  have g4 := gr h4
  have g5 := ge h5
  have g6 := processOperations_gen ctx hf h6
  have g7 := gs h7
  refine ⟨g1.trans (g2.trans (g3.trans (g4.trans (g5.trans (g6.trans g7))))), ?_⟩
  rw [g1.trans g2] at htime
  rw [← hslot_blk, ← hslot2]
  exact htime

private theorem stateTransition_gen_and_time {P : Preset} {f : CFork} (ctx : Ctx)
    (hf : f.atLeast .electra = true) {s s' : BeaconState P f} {sb : SignedBeaconBlock P f}
    (h : JauneConsensus.stateTransition ctx s sb = .ok s') :
    GenEq s s' ∧
      computeTimeAtSlotOf ctx.cfg s.genesis_time sb.message.slot =
        .ok sb.message.body.execution_payload.timestamp := by
  unfold JauneConsensus.stateTransition JauneConsensus.stateTransitionWith at h
  dsimp only at h
  obtain ⟨s1, hs1, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  have g1 := processSlots_gen ctx hf hs1
  obtain ⟨_, _, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  obtain ⟨s2, hb, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  have ⟨g2, htime⟩ := processBlock_gen_and_time ctx hf hb
  obtain ⟨_, _, h⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp h
  cases h
  rw [g1] at htime
  exact ⟨g1.trans g2, htime⟩

private theorem jointStep_gen_and_time {P : Preset} {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {s s' : JointState P} {b : AnySignedBlock P}
    (h : jointStep cfg ccfg bls s b = .ok s') :
    s'.beacon.genesis_time = s.beacon.genesis_time ∧
      computeTimeAtSlotOf ccfg s.beacon.genesis_time b.2.message.slot =
        .ok b.2.message.body.execution_payload.timestamp := by
  rcases s with ⟨fs, beacon, exec⟩
  rcases b with ⟨fb, sb⟩
  cases fs <;> cases fb
  all_goals try (unfold jointStep at h; cases h)
  · obtain ⟨_, _, beacon', exec', _, _, hst, rfl⟩ :=
      JauneConsensus.jointStep_electra_ok_iff.mp h
    exact stateTransition_gen_and_time _ (by decide) hst
  · obtain ⟨_, _, _, forkSlot, beacon1, beacon2, beacon', exec', _, hps, hup, _, _, hst, rfl⟩ :=
      JauneConsensus.jointStep_cross_ok_iff.mp h
    have g1 : beacon1.genesis_time = beacon.genesis_time := by
      split at hps
      · exact processSlots_gen _ (by decide) hps
      · cases hps; rfl
    have g2 : beacon2.genesis_time = beacon1.genesis_time := by
      unfold upgradeToFulu at hup
      simp only [bind, Except.bind, pure, Except.pure] at hup
      repeat' split at hup
      all_goals first | (cases hup; rfl) | cases hup
    have ⟨g3, htime⟩ : beacon'.genesis_time = beacon2.genesis_time ∧
        computeTimeAtSlotOf ccfg beacon2.genesis_time sb.message.slot =
          .ok sb.message.body.execution_payload.timestamp := by
      split at hst
      · obtain ⟨_, _, hst⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hst
        obtain ⟨_, _, hst⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hst
        obtain ⟨s', hb, hst⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hst
        obtain ⟨_, _, hst⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hst
        cases hst
        exact processBlock_gen_and_time _ (by decide) hb
      · exact stateTransition_gen_and_time _ (by decide) hst
    rw [g2, g1] at htime
    exact ⟨g3.trans (g2.trans g1), htime⟩
  · obtain ⟨_, beacon', exec', _, _, hst, rfl⟩ :=
      JauneConsensus.jointStep_fulu_ok_iff.mp h
    exact stateTransition_gen_and_time _ (by decide) hst

private theorem jointRun_step_genesis {P : Preset} {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {anchor final : JointState P} (run : JointRun cfg ccfg bls anchor final)
    {k : Nat} (hk : k < run.steps.length) :
    (run.steps[k]'hk).pre.beacon.genesis_time = anchor.beacon.genesis_time := by
  induction k with
  | zero =>
    rw [jointRun_first_pre run hk]
  | succ k ih =>
    have hk' : k < run.steps.length := Nat.lt_of_succ_lt hk
    have hstep := run.steps_jointStep (List.getElem?_eq_getElem hk')
    have hlink := jointRun_step_link run hk
    rw [← hlink]
    exact (jointStep_gen_and_time hstep).1.trans (ih hk')

private noncomputable def genesisMsOf (gen : U64) : Nat :=
  match secondsToMilliseconds gen with
  | .ok gms => gms.toNat
  | .error _ => 0

private theorem computeTimeAtSlotOf_nat {ccfg : Config} {gen slot t : U64}
    (hwhole : ccfg.SLOT_DURATION_MS % 1000 = 0)
    (ht : computeTimeAtSlotOf ccfg gen slot = .ok t) :
    t.toNat = genesisMsOf gen / 1000 + (ccfg.SLOT_DURATION_MS / 1000) * slot.toNat := by
  unfold computeTimeAtSlotOf at ht
  obtain ⟨gms, hgms, ht⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp ht
  obtain ⟨tms, hcms, hms⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp ht
  unfold millisecondsToSeconds at hms
  obtain ⟨th, hth, hdiv⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hms
  unfold computeTimeAtSlotMs at hcms
  obtain ⟨sd, hsd, hcms⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hcms
  obtain ⟨mulv, hmul, hadd⟩ := JauneConsensus.Facts.bind_eq_ok_iff.mp hcms
  have hms_eq : t.toNat = tms.toNat / 1000 := by rw [U64.toNat_div? hdiv, U64.toNat_ofNat? hth]
  have hcm_eq : tms.toNat = gms.toNat + mulv.toNat := U64.toNat_add? hadd
  have hmul_eq : mulv.toNat = slot.toNat * ccfg.SLOT_DURATION_MS := by rw [U64.toNat_mul? hmul, U64.toNat_ofNat? hsd]
  have hgms_eq : gms.toNat = genesisMsOf gen := by unfold genesisMsOf; rw [hgms]
  have hsd_mul : ccfg.SLOT_DURATION_MS = 1000 * (ccfg.SLOT_DURATION_MS / 1000) := by omega
  rw [hms_eq, hcm_eq, hmul_eq, hgms_eq]
  conv_lhs => rw [hsd_mul, ← Nat.mul_assoc, Nat.mul_comm slot.toNat 1000, Nat.mul_assoc]
  rw [Nat.add_mul_div_left _ _ (by omega), Nat.mul_comm]

theorem r_s8_slot : BeaconRoots.R_S8_slot := by
  intro P cfg ccfg bls checkpoint anchor final v whole coprime i hi hslot
  let execRun := v.run.toExec v.pre
  have r3 := Blanc.Corpus.Proofs.RingHistory.R.r_s3 execRun.keptHistory execRun.kept_covered v.code v.systemEmpty v.clean
  let k := v.pre.kept.length + i
  have hk : k < execRun.kept.length := by change k < (v.run.toExec v.pre).kept.length; rw [v.run.kept_length v.pre]; omega
  have hget_i : execRun.kept[k]'hk = (v.run.steps[i]'hi).keptBlock := by
    have hg := v.run.kept_getElem? v.pre (List.getElem?_eq_getElem hi)
    change execRun.kept[k]? = some (v.run.steps[i]'hi).keptBlock at hg
    rw [List.getElem?_eq_getElem hk] at hg; exact Option.some.inj hg
  have hpos_i : 0 < (Corpus.Freeze.stepTime (v.run.steps[i]'hi)).toNat := by
    obtain ⟨_, _, _, _, hlt, _⟩ := (v.run.steps[i]'hi).keptBlock_step.header_links
    have hts := (v.run.steps[i]'hi).keptBlock_timestamp; unfold Corpus.Freeze.stepTime
    rw [← hts, B256.toNat_toB256_of_lt (by have := (v.run.steps[i]'hi).block.2.message.body.execution_payload.timestamp.toNat_lt; rw [← hts] at this; omega)]
    omega
  have hnz_i : (BeaconRoots.blockWrite (execRun.kept[k]'hk)).1 ≠ 0 := by
    rw [hget_i]; unfold BeaconRoots.blockWrite; rw [JointRunStep.keptBlock_timestamp]
    intro h0; have := congrArg B256.toNat h0
    change (Corpus.Freeze.stepTime (v.run.steps[i]'hi)).toNat = (0 : B256).toNat at this; rw [B256.toNat_zero] at this; omega
  have hread := r3.2 k hk hnz_i (fun m hm hkm => ?_)
  · rw [hget_i] at hread; unfold BeaconRoots.blockWrite at hread
    rw [JointRunStep.keptBlock_timestamp, JointRunStep.keptBlock_parentBeaconBlockRoot] at hread; exact hread
  · have hm_ge : v.pre.kept.length ≤ m := by omega
    let j := m - v.pre.kept.length
    have hj : j < v.run.steps.length := by have hm_len : m < (v.run.toExec v.pre).kept.length := hm; rw [v.run.kept_length v.pre] at hm_len; omega
    have hij : i < j := by omega
    have hm_eq : v.pre.kept.length + j = m := by omega
    have hget_j : execRun.kept[m]'hm = (v.run.steps[j]'hj).keptBlock := by
      have hg := v.run.kept_getElem? v.pre (List.getElem?_eq_getElem hj)
      change (v.run.toExec v.pre).kept[v.pre.kept.length + j]? = some (v.run.steps[j]'hj).keptBlock at hg
      change (v.run.toExec v.pre).kept[m]'hm = (v.run.steps[j]'hj).keptBlock
      rw [hm_eq, List.getElem?_eq_getElem hm] at hg; exact Option.some.inj hg
    rw [hget_i, hget_j]; unfold BeaconRoots.blockWrite; rw [JointRunStep.keptBlock_timestamp, JointRunStep.keptBlock_timestamp]
    have hlt_ts : (v.run.steps[i]'hi).keptBlock.block.header.timestamp < (v.run.steps[j]'hj).keptBlock.block.header.timestamp := by
      have hts := execRun.keptHistory.timestamp_lt (by omega : k < m) (List.getElem?_eq_getElem hk) (List.getElem?_eq_getElem hm)
      rw [hget_i, hget_j] at hts; exact hts
    have ht_i := (jointStep_gen_and_time (v.run.steps_jointStep (List.getElem?_eq_getElem hi))).2
    have ht_j := (jointStep_gen_and_time (v.run.steps_jointStep (List.getElem?_eq_getElem hj))).2
    rw [jointRun_step_genesis v.run hi] at ht_i; rw [jointRun_step_genesis v.run hj] at ht_j
    have hti_eq := computeTimeAtSlotOf_nat whole ht_i; have htj_eq := computeTimeAtSlotOf_nat whole ht_j
    let d := ccfg.SLOT_DURATION_MS / 1000
    have hd_pos : 0 < d := Nat.pos_of_ne_zero fun hdz => coprime (by rw [show ccfg.SLOT_DURATION_MS / 1000 = 0 from hdz]; exact Nat.dvd_zero 8191)
    have hti_lt : (v.run.steps[i]'hi).block.2.message.body.execution_payload.timestamp.toNat <
        (v.run.steps[j]'hj).block.2.message.body.execution_payload.timestamp.toNat := by
      rw [← (v.run.steps[i]'hi).keptBlock_timestamp, ← (v.run.steps[j]'hj).keptBlock_timestamp]; exact hlt_ts
    have hslot_lt : (v.run.steps[i]'hi).block.2.message.slot.toNat < (v.run.steps[j]'hj).block.2.message.slot.toNat := by
      rw [hti_eq, htj_eq] at hti_lt
      exact Nat.lt_of_mul_lt_mul_left (a := ccfg.SLOT_DURATION_MS / 1000) (by omega)
    have hslot_hi : (v.run.steps[j]'hj).block.2.message.slot.toNat < (v.run.steps[i]'hi).block.2.message.slot.toNat + 8191 := hslot j hj hij
    have hcop : Nat.Coprime d 8191 := coprime_8191_of_not_dvd coprime
    intro hsame; have h1 := congrArg B256.toNat hsame
    unfold BeaconRoots.timeKey at h1; rw [b256_mod_ring_toNat, b256_mod_ring_toNat] at h1
    have htime_i_lt : (v.run.steps[i]'hi).block.2.message.body.execution_payload.timestamp.toNat < 2 ^ 256 :=
      Nat.lt_trans (v.run.steps[i]'hi).block.2.message.body.execution_payload.timestamp.toNat_lt (by decide)
    have htime_j_lt : (v.run.steps[j]'hj).block.2.message.body.execution_payload.timestamp.toNat < 2 ^ 256 :=
      Nat.lt_trans (v.run.steps[j]'hj).block.2.message.body.execution_payload.timestamp.toNat_lt (by decide)
    change (Nat.toB256 (v.run.steps[j]'hj).block.2.message.body.execution_payload.timestamp.toNat).toNat % 8191 =
      (Nat.toB256 (v.run.steps[i]'hi).block.2.message.body.execution_payload.timestamp.toNat).toNat % 8191 at h1
    rw [B256.toNat_toB256_of_lt htime_j_lt, B256.toNat_toB256_of_lt htime_i_lt, htj_eq, hti_eq] at h1
    have hdiff_eq : (genesisMsOf anchor.beacon.genesis_time / 1000 + d * (v.run.steps[j]'hj).block.2.message.slot.toNat) -
        (genesisMsOf anchor.beacon.genesis_time / 1000 + d * (v.run.steps[i]'hi).block.2.message.slot.toNat) =
        d * ((v.run.steps[j]'hj).block.2.message.slot.toNat - (v.run.steps[i]'hi).block.2.message.slot.toNat) := by
      rw [Nat.add_sub_add_left, ← Nat.mul_sub_left_distrib]
    have hdvd_diff : 8191 ∣ (genesisMsOf anchor.beacon.genesis_time / 1000 + d * (v.run.steps[j]'hj).block.2.message.slot.toNat) -
        (genesisMsOf anchor.beacon.genesis_time / 1000 + d * (v.run.steps[i]'hi).block.2.message.slot.toNat) := by
      have hmul_le : d * (v.run.steps[i]'hi).block.2.message.slot.toNat ≤ d * (v.run.steps[j]'hj).block.2.message.slot.toNat :=
        Nat.mul_le_mul_left d (Nat.le_of_lt hslot_lt)
      exact (Nat.modEq_iff_dvd' (by omega)).mp h1.symm
    rw [hdiff_eq] at hdvd_diff
    have hdvd_s : 8191 ∣ (v.run.steps[j]'hj).block.2.message.slot.toNat - (v.run.steps[i]'hi).block.2.message.slot.toNat :=
      hcop.symm.dvd_of_dvd_mul_left hdvd_diff
    exact absurd (Nat.le_of_dvd (by omega) hdvd_s) (by omega)

/-! ## `H_S8`, `H_S9`, `H_S9_joint` -/

private theorem history_read_silent {b : KeptBlock} (fork : CoveredFork b.fork) (g : Exec.Frame)
    (entry : Exec.Frame.EntryIn historyStorageAddress historyStorageCode b.benv.stat g)
    (nonSystem : g.sevm.caller ≠ systemAddress) :
    Devm.getStor g.post historyStorageAddress = Devm.getStor g.pre historyStorageAddress := by
  rcases g with ⟨pc, sevm, pre, out, run, committed⟩
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    obtain ⟨_, entry⟩ := entry; have hpc : pc = 0 := entry.pc; subst hpc
    have hfork : CoveredFork sevm.benvStat.fork := by rw [entry.benvStat]; exact fork
    exact congrArg (fun s : State => s.getStor historyStorageAddress)
      (Blanc.Lift.HistoryStorage.exec_read_frame entry.code hfork entry.stack entry.dataLength nonSystem run).2.2.2.2.1

private theorem history_step_pre {cfg : ChainConfig} {b : KeptBlock} {post : BlockChain}
    (step : KeptStep cfg b post) (fork : CoveredFork b.fork)
    (code : b.parent.state.getCode historyStorageAddress = historyStorageCode)
    (empty : b.parent.state.getCode systemAddress = ByteArray.empty)
    (senders : NoSenderAt systemAddress b.run.senders)
    (authorities : NoAuthorityAt systemAddress b.run.senders)
    (avoid : NoCreateAt systemAddress b.run.roots) :
    Corpus.Freeze.storOf b.run.preState historyStorageAddress =
      HistoryStorage.write (Corpus.Freeze.storOf b.parent.state historyStorageAddress)
        (HistoryStorage.blockWrite b).1 (HistoryStorage.blockWrite b).2 := by
  have hcall : ∀ {beacon : State}, beacon.getCode historyStorageAddress = historyStorageCode →
      beacon.getStor historyStorageAddress = b.parent.state.getStor historyStorageAddress →
      ∃ stHist outHist,
        processUncheckedSystemTransaction (b.benv.withState beacon) historyStorageAddress
          b.block.header.parentHash.toBytes = .ok (stHist, outHist) ∧ outHist.error = none ∧
        stHist.getStor historyStorageAddress =
          (b.parent.state.getStor historyStorageAddress).set
            ((b.block.header.number.toB256 - 1) % 0x1fff) b.block.header.parentHash := by
    intro beacon hcode hstor
    have call := Blanc.Lift.SystemExecution.HistoryStorage.processUncheckedSystemTransaction_historyStorage
      (benv := b.benv.withState beacon) fork hcode step.lastBlockHash.1
    refine ⟨_, _, call.1, rfl, ?_⟩
    have value : Blanc.Lift.SystemExecution.HistoryStorage.systemValue (b.benv.withState beacon) = b.block.header.parentHash := by
      apply dataWord_of_append (pre := []) (post := []) rfl
      change (b.benv.stat.blockHashes.getLast?.getD 0).toBytes = _; rw [step.lastBlockHash.1]; rfl
    rw [call.2.1, value, State.getStor_setStorVal_self]
    change (beacon.getStor historyStorageAddress).set ((b.block.header.number.toB256 - 1) % 0x1fff) b.block.header.parentHash = _
    rw [hstor]
  have hpre_stor := (step.historyStorage_stor fork code empty senders authorities avoid
    (fun g he hc => history_read_silent fork g he hc) hcall).2.2.1
  funext k; change (b.run.preState.getStor historyStorageAddress).get k = _
  rw [hpre_stor, Stor.get_set_ite]
  unfold Corpus.Freeze.storOf HistoryStorage.write HistoryStorage.blockWrite HistoryStorage.key
  have hring : ring = 0x1fff := rfl; rw [hring]; simp only [eq_comm]

private theorem history_key_ne {a b : Nat} (ha : 0 < a) (hlt : a < b) (hdiff : b - a < 8191)
    (hb : b < 2 ^ 256) :
    HistoryStorage.key b.toB256 ≠ HistoryStorage.key a.toB256 := by
  unfold HistoryStorage.key
  rw [nat_toB256_sub_one b (by omega) hb, nat_toB256_sub_one a ha (by omega)]
  intro h
  have h1 := congrArg B256.toNat h
  rw [b256_mod_ring_toNat, b256_mod_ring_toNat,
    B256.toNat_toB256_of_lt (by omega), B256.toNat_toB256_of_lt (by omega)] at h1
  omega

private theorem history_writeAll_append (s : B256 → B256) (xs ys : List (B256 × B256)) :
    HistoryStorage.writeAll s (xs ++ ys) =
      HistoryStorage.writeAll (HistoryStorage.writeAll s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨N, v⟩
    exact ih (HistoryStorage.write s N v)

private theorem history_writeAll_lookup (s : B256 → B256) (xs : List (B256 × B256))
    (N v : B256) (ys : List (B256 × B256))
    (hother : ∀ p ∈ ys, HistoryStorage.key p.1 ≠ HistoryStorage.key N) :
    HistoryStorage.writeAll s (xs ++ (N, v) :: ys) (HistoryStorage.key N) = v := by
  have hstep : ∀ (acc : B256 → B256) (zs : List (B256 × B256)),
      (∀ p ∈ zs, HistoryStorage.key p.1 ≠ HistoryStorage.key N) →
      HistoryStorage.writeAll acc zs (HistoryStorage.key N) = acc (HistoryStorage.key N) := by
    intro acc zs hz
    induction zs generalizing acc with
    | nil => rfl
    | cons z zs ih =>
      unfold HistoryStorage.writeAll
      rw [ih _ (fun p hp => hz p (List.mem_cons_of_mem _ hp))]
      unfold HistoryStorage.write; rw [ite_eq_right (hz z List.mem_cons_self).symm]
  rw [history_writeAll_append]
  change HistoryStorage.writeAll (HistoryStorage.write (HistoryStorage.writeAll s xs) N v) ys (HistoryStorage.key N) = v
  rw [hstep _ ys hother]; unfold HistoryStorage.write; rw [ite_eq_left rfl]

theorem h_s8 : HistoryStorage.H_S8 := by
  refine ⟨?_, fun s N q hwin => ?_⟩
  · intro cfg start stop blocks history covered code systemEmpty clean i hi hfit
    refine ⟨?_, ?_⟩
    · intro j hj hij hle
      have hbi_pos : 0 < blocks[i].block.header.number := by
        obtain ⟨_, tip, _, _, h0, _⟩ := history.prev_block_zero (List.getElem?_eq_getElem (by omega : 0 < blocks.length))
        have hi0 := history.number_add (Nat.zero_le i) (List.getElem?_eq_getElem (by omega : 0 < blocks.length)) (List.getElem?_eq_getElem hi)
        omega
      have hji := history.number_add hij (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj)
      have hj_lt : blocks[j].block.header.number < 2 ^ 256 := by omega
      have hi_lt : blocks[i].block.header.number < 2 ^ 256 := by omega
      have hbj_pos : 0 < blocks[j].block.header.number := by omega
      have hwin : HistoryStorage.InWindow blocks[j].block.header.number.toB256 (blocks[i].block.header.number - 1).toB256 := by
        unfold HistoryStorage.InWindow; rw [nat_toB256_sub_one _ hbj_pos hj_lt]
        have hle_sub : (blocks[i].block.header.number - 1).toB256 ≤ blocks[j].block.header.number.toB256 := by
          rw [B256.le_iff_toNat_le_toNat, B256.toNat_toB256_of_lt (by omega), B256.toNat_toB256_of_lt hj_lt]; omega
        rw [B256.toNat_sub_eq_of_le _ _ hle_sub, B256.toNat_toB256_of_lt (by omega), B256.toNat_toB256_of_lt (by omega), B256.toNat_toB256_of_lt hj_lt]
        omega
      unfold HistoryStorage.read; rw [ite_eq_left hwin]; apply congrArg some
      obtain ⟨_, hpre_j, step_j, _⟩ := history.split_at (List.getElem?_eq_getElem hj)
      have hpre_state := Blanc.Corpus.Proofs.RingHistory.H.history hpre_j (fun b hb => covered b (List.mem_of_mem_take hb)) code systemEmpty
        ⟨fun b hb => clean.senders b (List.mem_of_mem_take hb), fun b hb => clean.authorities b (List.mem_of_mem_take hb), fun b hb => clean.creates b (List.mem_of_mem_take hb)⟩
      have hstep_j := history_step_pre step_j (covered _ (List.getElem_mem hj)) hpre_state.1 hpre_state.2.1
        (clean.senders _ (List.getElem_mem hj)) (clean.authorities _ (List.getElem_mem hj)) (clean.creates _ (List.getElem_mem hj))
      have hstor_j1 : Corpus.Freeze.storOf blocks[j].run.preState HistoryStorage.addr =
          HistoryStorage.writeAll (Corpus.Freeze.storOf start.state HistoryStorage.addr) ((blocks.take (j + 1)).map HistoryStorage.blockWrite) := by
        rw [hstep_j, hpre_state.2.2, List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.map_append, List.map_singleton, history_writeAll_append]
        rfl
      rw [hstor_j1]
      have hi_take : i < (blocks.take (j + 1)).length := by rw [List.length_take]; omega
      have hsplit_take : blocks.take (j + 1) = (blocks.take (j + 1)).take i ++ blocks[i] :: (blocks.take (j + 1)).drop (i + 1) := by
        have hs1 := List.take_append_drop i (blocks.take (j + 1))
        rw [List.drop_eq_getElem_cons hi_take, List.getElem_take] at hs1; exact hs1.symm
      rw [hsplit_take, List.map_append, List.map_cons]
      have hkey_i : (blocks[i].block.header.number - 1).toB256 % ring = HistoryStorage.key (HistoryStorage.blockWrite blocks[i]).1 := by
        unfold HistoryStorage.key HistoryStorage.blockWrite; rw [nat_toB256_sub_one _ hbi_pos hi_lt]
      rw [hkey_i]
      apply history_writeAll_lookup
      intro p hp
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
      obtain ⟨t, ht, hbt⟩ := List.mem_iff_getElem.mp hb
      have hlen_drop : ((blocks.take (j + 1)).drop (i + 1)).length = min (j + 1) blocks.length - (i + 1) := by rw [List.length_drop, List.length_take]
      have hk_lt : i + 1 + t < j + 1 := by omega
      have hk_len : i + 1 + t < blocks.length := by omega
      rw [← hbt, List.getElem_drop, List.getElem_take]
      unfold HistoryStorage.blockWrite
      have hki := history.number_add (by omega : i ≤ i + 1 + t) (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hk_len)
      have hkj := history.number_add (by omega : i + 1 + t ≤ j) (List.getElem?_eq_getElem hk_len) (List.getElem?_eq_getElem hj)
      exact history_key_ne hbi_pos (by omega) (by omega) (by omega)
    · intro s m hm1 hm2
      unfold HistoryStorage.read
      refine ite_eq_right (fun ⟨_, hup⟩ => ?_)
      have hle_sub : (blocks[i].block.header.number - 1).toB256 ≤ m.toB256 := by
        rw [B256.le_iff_toNat_le_toNat, B256.toNat_toB256_of_lt (by omega), B256.toNat_toB256_of_lt hm2]; omega
      rw [B256.toNat_sub_eq_of_le _ _ hle_sub, B256.toNat_toB256_of_lt hm2, B256.toNat_toB256_of_lt (by omega)] at hup; omega
  · unfold HistoryStorage.read; exact ite_eq_left hwin

theorem h_s9 : HistoryStorage.H_S9 := by
  intro cfg start stop blocks history covered code systemEmpty clean i hi hfit
  have hs8 := h_s8.1 history covered code systemEmpty clean i hi hfit
  cases i with
  | zero =>
    obtain ⟨_, tip, hlast, hph, hnum, _⟩ := history.prev_block_zero (List.getElem?_eq_getElem hi)
    refine ⟨tip.header, ?_, hnum.symm, fun j hj hij hle => ?_⟩
    · unfold HistoryStorage.prevHeader; rw [ite_eq_left rfl, hlast]; rfl
    · have heq : tip.header.number = blocks[0].block.header.number - 1 := by omega
      rw [heq, ← hph]; exact hs8.1 j hj hij (by omega)
  | succ k =>
    have hk : k < blocks.length := Nat.lt_of_succ_lt hi
    obtain ⟨_, hph, hnum, _⟩ := history.step_adj (List.getElem?_eq_getElem hk) (List.getElem?_eq_getElem hi)
    refine ⟨blocks[k].block.header, ?_, hnum.symm, fun j hj hij hle => ?_⟩
    · unfold HistoryStorage.prevHeader; rw [ite_eq_right (Nat.succ_ne_zero k), Nat.add_sub_cancel, List.getElem?_eq_getElem hk]; rfl
    · have heq : blocks[k].block.header.number = blocks[k + 1].block.header.number - 1 := by omega
      rw [heq, ← hph]; exact hs8.1 j hj hij (by omega)

theorem h_s9_joint : HistoryStorage.H_S9_joint := by
  intro P cfg ccfg bls checkpoint anchor final v st hst
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hst
  obtain ⟨preSteps, hpre, hstep, hcov_st, havoid_st, hcov_pre, hclean_pre⟩ := jointRun_step_in_kept v hk
  have hpre_state := Blanc.Corpus.Proofs.RingHistory.H.history hpre hcov_pre v.code v.systemEmpty hclean_pre
  have hclean_st : v.run.steps[k].keptBlock ∈ (v.run.toExec v.pre).kept := by
    rw [v.run.kept_toExec v.pre]; exact List.mem_append_right _ (List.mem_map_of_mem (List.getElem_mem hk))
  have hstep_h := Blanc.Corpus.Proofs.RingHistory.H.step hstep hcov_st hpre_state.1 hpre_state.2.1
    (v.clean.senders _ hclean_st) (v.clean.authorities _ hclean_st) havoid_st
  have hph := JauneConsensus.Facts.jointStep_execution_payload_hashes (v.run.steps_jointStep (List.getElem?_eq_getElem hk))
  have hstor := hstep_h.2.2
  unfold HistoryStorage.blockWrite at hstor
  rw [JointRunStep.keptBlock_number, JointRunStep.keptBlock_parentHash] at hstor
  have hkeyW : HistoryStorage.write (Corpus.Freeze.storOf (v.run.steps[k]'hk).pre.exec.state HistoryStorage.addr)
      ((Corpus.Freeze.stepNumber (v.run.steps[k]'hk)).toB256)
      (v.run.steps[k]'hk).block.2.message.body.execution_payload.parent_hash
      (HistoryStorage.key (Corpus.Freeze.stepNumber (v.run.steps[k]'hk)).toB256) =
      (v.run.steps[k]'hk).block.2.message.body.execution_payload.parent_hash := by
    unfold HistoryStorage.write; rw [ite_eq_left rfl]
  exact (congrFun hstor _).trans (hkeyW.trans hph.1)

end Blanc.Composition.Corpus.Proofs.RingJointRetention
