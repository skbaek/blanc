import Blanc.Lift.FreePtrMem
import Blanc.Lift.ReturnDataKeep

/-!
# One step of the free-pointer walk is sound (F3c, step half)

The frozen observation `FpObs`/`FpStep` (design `fp-checker.md`, Appendix A §F3) and the
per-instruction soundness of `fstep` that `fpRun_sound` (`Blanc/Lift/FreePtrSound.lean`) cites at
every `.next` node:

* `FpInv ν σ d rest`: the checker state `σ` describes the machine `d` under the symbol valuation
  `ν`: `σ.kv` names the words above the untouched `rest`, the facts hold, and `σ.fp` names the
  free-pointer word (`FpWord`, F3b);
* `fstep_sound`: an accepted step keeps the invariant under a one-point update of `ν` at the fresh
  symbol, records the observation `FpObs`, and keeps the checker's frame no longer than the
  abstract stack `checkNode` tracks beside it (the bound that admits `transfer_val`).

Everything below the step is F3a's (`opFacts_sound`, `transfer_val`) and F3b's (`memEff_fpWord`,
`memEff_touched`, `memEff_obs`, `memEff_mload_top`).  Contract-neutral.
-/

namespace Blanc.Lift.FreePtr

open Jaune AbstractStackSafety Blanc.Lift.SymTransfer

/-- A good free-pointer value. -/
def FpGood (w : B256) : Prop := fpLo ≤ w.toNat ∧ w.toNat ≤ fpCap

/-- What a step observes: an `MLOAD` of offset `0x40` reads a good free pointer. -/
def FpObs (d : Devm) (n : Ninst) : Prop :=
  n = .reg .mload → d.stack.head? = some 64 → FpGood (memWord d.memory 64)

/-- A step relation that also records the free-pointer observation. -/
def FpStep (P : Sevm → Devm → Ninst → Devm → Prop) : Sevm → Devm → Ninst → Devm → Prop :=
  fun s d n d' => P s d n d' ∧ FpObs d n

/-- The checker state `σ` describes the machine `d` under `ν`, above the untouched `rest`; a
return-data fact bounds the current return-data buffer. -/
def FpInv (ν : Nat → B256) (σ : FSt) (d : Devm) (rest : List B256) : Prop :=
  ∃ S, d.stack = S ++ rest ∧ List.Forall₂ (fun s w => ν s = w) σ.kv S ∧ AllHold ν σ.facts ∧
    FpWord ν σ.fp d.memory ∧ ∀ h, Fact.rdsLe h ∈ σ.facts → d.returnData.length ≤ h

theorem FpWord.congr {ν ν' : Nat → B256} {fp : Option Nat} {μ : Mem}
    (h : ∀ s, fp = some s → ν' s = ν s) (hw : FpWord ν fp μ) : FpWord ν' fp μ := by
  intro s hs
  rw [h s hs]
  exact hw s hs

private theorem upd_ne {ν : Nat → B256} {r s : Nat} {w : B256} (h : s ≠ r) :
    Function.update ν r w s = ν s :=
  Function.update_of_ne h w ν

/-! ## Lengths: the checker frame never outgrows the abstract stack -/

private theorem mapM_length {α β : Type} {g : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM g = some l' → l'.length = l.length
  | [], l', h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    rfl
  | x :: l, l', h => by
    rw [List.mapM_cons] at h
    cases hx : g x with
    | none => simp only [hx, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at h
    | some y =>
      cases hl : l.mapM g with
      | none => simp only [hx, hl, Option.bind_eq_bind, Option.bind_some, Option.bind_none,
        reduceCtorEq] at h
      | some l2 =>
        simp only [hx, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        simp only [List.length_cons, mapM_length hl]

private theorem indexPattern_add (k m : Nat) :
    indexPattern (k + m) =
      indexPattern k ++ (List.range m).map (fun i => some (Nat.toB256 (k + i))) := by
  simp only [indexPattern, List.range_add, List.map_append, List.map_map]
  rfl

/-- A transfer over a longer index pattern returns a no shorter pattern. -/
theorem transfer_length_mono {n : Ninst} {k m : Nat} {o o' : Pattern}
    (h1 : ninstTransfer n (indexPattern k) = some o)
    (h2 : ninstTransfer n (indexPattern m) = some o') (hkm : k ≤ m) : o.length ≤ o'.length := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkm
  rw [indexPattern_add, ninstTransfer_append _ h1] at h2
  cases h2
  simp only [List.length_append]
  omega

private theorem foldTop_length (c : Option B256) (a : List AVal) :
    (foldTop c a).length = a.length := by
  cases c <;> cases a <;> rfl

/-! ## Unfolding `fstep` -/

/-- The non-push arm of `fstep`, unfolded: the result symbol `r'` is the fresh symbol, except at
the free-pointer `MLOAD`, where it is the pointer's own symbol. -/
theorem fstep_nonpush {n : Ninst} {σ σ' : FSt}
    (hn : ∀ (bs : Bytes) (fits : bs.length ≤ 32), n ≠ .push bs fits)
    (h : fstep n σ = some σ') :
    ∃ out fp' gas kv' r', ninstTransfer n (indexPattern σ.kv.length) = some out ∧
      out.count none ≤ 1 ∧ memEff σ.facts σ.fp n σ.kv = some (fp', gas) ∧
      out.mapM (fun l => match l with
        | none => some r' | some j => σ.kv[j.toNat]?) = some kv' ∧
      (r' = freshSym σ.kv σ.facts σ.fp ∨
        (n = .reg .mload ∧ ∃ x kt, σ.kv = x :: kt ∧ constOf σ.facts x = some 64 ∧
          r' = fp'.getD (freshSym σ.kv σ.facts σ.fp))) ∧
      σ' = ⟨kv', closeLive kv' fp' (opFacts σ.facts n σ.kv (freshSym σ.kv σ.facts σ.fp) ++
        rdsEff σ.facts n (freshSym σ.kv σ.facts σ.fp) ++ gas ++ rdsKeep n σ.facts), fp'⟩ := by
  have e : fstep n σ = (do
      let out ← ninstTransfer n (indexPattern σ.kv.length)
      guard (out.count none ≤ 1)
      let r := freshSym σ.kv σ.facts σ.fp
      let (fp', gas) ← memEff σ.facts σ.fp n σ.kv
      let r' := match (generalizing := false) n, σ.kv with
        | .reg .mload, a :: _ => if constOf σ.facts a = some 64 then fp'.getD r else r
        | _, _ => r
      let kv' ← out.mapM (fun l => match l with
        | none => some r'
        | some j => σ.kv[j.toNat]?)
      some (⟨kv', closeLive kv' fp'
        (opFacts σ.facts n σ.kv r ++ rdsEff σ.facts n r ++ gas ++ rdsKeep n σ.facts), fp'⟩ : FSt)) := by
    cases n with
    | push bs fits => exact (hn bs fits rfl).elim
    | _ => rfl
  rw [e] at h
  cases ho : ninstTransfer n (indexPattern σ.kv.length) with
  | none => simp only [ho, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at h
  | some out =>
    by_cases hc : out.count none ≤ 1
    · cases he : memEff σ.facts σ.fp n σ.kv with
      | none => simp only [ho, he, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none,
        reduceCtorEq] at h
      | some p =>
        obtain ⟨fp', gas⟩ := p
        simp only [ho, hc, he, guard_true, Option.bind_eq_bind, Option.bind_some] at h
        generalize hr' : (match (generalizing := false) n, σ.kv with
          | .reg .mload, a :: _ =>
            if constOf σ.facts a = some 64 then fp'.getD (freshSym σ.kv σ.facts σ.fp)
            else freshSym σ.kv σ.facts σ.fp
          | _, _ => freshSym σ.kv σ.facts σ.fp) = r' at h
        cases hm : out.mapM (fun l => match l with
            | none => some r' | some j => σ.kv[j.toNat]?) with
        | none => simp only [hm, Option.pure_def, Option.bind_some, Option.bind_none,
          reduceCtorEq] at h
        | some kv' =>
          simp only [hm, Option.pure_def, Option.bind_some, Option.some.injEq] at h
          refine ⟨out, fp', gas, kv', r', rfl, hc, rfl, hm, ?_, h.symm⟩
          subst hr'
          split
          · rename_i x kt hkv
            split
            · exact Or.inr ⟨rfl, x, kt, hkv, ‹_›, rfl⟩
            · exact Or.inl rfl
          · exact Or.inl rfl
    · simp only [ho, hc, guard_false, Option.bind_eq_bind, Option.bind_some,
        Option.failure_eq_none, Option.bind_none, reduceCtorEq] at h

/-! ## The computed result sits on top -/

private theorem binary_head {p out : Pattern} (h : binaryTransfer p = some out) :
    ∃ o, out = none :: o := by
  unfold binaryTransfer at h
  split at h
  · exact ⟨_, (Option.some.inj h).symm⟩
  · cases h

private theorem unary_head {p out : Pattern} (h : unaryTransfer p = some out) :
    ∃ o, out = none :: o := by
  unfold unaryTransfer at h
  split at h
  · exact ⟨_, (Option.some.inj h).symm⟩
  · cases h

/-- The instructions with fact rules push their one computed result on top. -/
theorem opFacts_out_head {fs : List Fact} {kv : List Nat} {n : Ninst} {r : Nat} {p out : Pattern}
    (hne : opFacts fs n kv r ≠ []) (hout : ninstTransfer n p = some out) :
    ∃ o, out = none :: o := by
  cases n with
  | reg rr =>
    cases rr
    all_goals try (exfalso; apply hne; simp only [opFacts]; done)
    all_goals
      simp only [ninstTransfer, liftRegularTransfer, regularTransfer] at hout
      first
        | exact binary_head hout
        | exact unary_head hout
        | cases hout
  | _ => exact (hne (by simp only [opFacts])).elim

theorem mload_out_head {p out : Pattern} (hout : ninstTransfer (.reg .mload) p = some out) :
    ∃ o, out = none :: o := by
  simp only [ninstTransfer, liftRegularTransfer, regularTransfer] at hout
  exact unary_head hout

theorem rds_out_head {p out : Pattern}
    (hout : ninstTransfer (.reg .returndatasize) p = some out) : ∃ o, out = none :: o := by
  simp only [ninstTransfer, liftRegularTransfer, Option.some.injEq] at hout
  exact ⟨_, hout.symm⟩

/-- Relabelling the computed result: a list named through the fresh label `r` is named through
`r'` too when the two name the same word. -/
private theorem mapM_relabel {kv : List Nat} {r r' : Nat} {ν : Nat → B256} (hrr : ν r' = ν r) :
    ∀ {out : Pattern} {kv' kv'' : List Nat} {S' : List B256},
      out.mapM (fun l => match l with | none => some r' | some j => kv[j.toNat]?) = some kv' →
      out.mapM (fun l => match l with | none => some r | some j => kv[j.toNat]?) = some kv'' →
      List.Forall₂ (fun s x => ν s = x) kv'' S' → List.Forall₂ (fun s x => ν s = x) kv' S'
  | [], kv', kv'', S', h1, h2, hS => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h1 h2
    subst h1 h2
    exact hS
  | l :: out, kv', kv'', S', h1, h2, hS => by
    rw [List.mapM_cons] at h1 h2
    cases ht1 : out.mapM (fun l => match l with | none => some r' | some j => kv[j.toNat]?) with
    | none => cases l <;> simp only [ht1, Option.pure_def, Option.bind_eq_bind, Option.bind_none,
        Option.bind_fun_none, reduceCtorEq] at h1
    | some k1 =>
      cases ht2 : out.mapM (fun l => match l with | none => some r | some j => kv[j.toNat]?) with
      | none => cases l <;> simp only [ht2, Option.pure_def, Option.bind_eq_bind, Option.bind_none,
          Option.bind_fun_none, reduceCtorEq] at h2
      | some k2 =>
        cases l with
        | none =>
          simp only [ht1, ht2, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
            Option.some.injEq] at h1 h2
          subst h1 h2
          cases hS with
          | cons h0 hr => exact .cons (by rw [hrr]; exact h0) (mapM_relabel hrr ht1 ht2 hr)
        | some j =>
          cases hs : kv[j.toNat]? with
          | none => simp only [hs, Option.pure_def, Option.bind_eq_bind, Option.bind_none,
              reduceCtorEq] at h1
          | some s =>
            simp only [hs, ht1, ht2, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
              Option.some.injEq] at h1 h2
            subst h1 h2
            cases hS with
            | cons h0 hr => exact .cons h0 (mapM_relabel hrr ht1 ht2 hr)

private theorem mapM_fresh_exists {kv : List Nat} {r r' : Nat} :
    ∀ {out : Pattern} {kv' : List Nat},
      out.mapM (fun l => match l with | none => some r' | some j => kv[j.toNat]?) = some kv' →
      ∃ kv'', out.mapM (fun l => match l with | none => some r | some j => kv[j.toNat]?) = some kv''
  | [], _, _ => ⟨[], rfl⟩
  | l :: out, kv', h => by
    rw [List.mapM_cons] at h
    cases ht : out.mapM (fun l => match l with | none => some r' | some j => kv[j.toNat]?) with
    | none => cases l <;> simp only [ht, Option.pure_def, Option.bind_eq_bind, Option.bind_none,
        Option.bind_fun_none, reduceCtorEq] at h
    | some k1 =>
      obtain ⟨k2, h2⟩ := mapM_fresh_exists ht
      cases l with
      | none => exact ⟨r :: k2, by rw [List.mapM_cons, h2]; rfl⟩
      | some j =>
        cases hs : kv[j.toNat]? with
        | none => simp only [hs, Option.pure_def, Option.bind_eq_bind, Option.bind_none,
            reduceCtorEq] at h
        | some s => exact ⟨s :: k2, by rw [List.mapM_cons, h2]; simp only [hs]; rfl⟩

/-! ## The return-data facts -/

theorem rdsLe_not_mem_opFacts {fs : List Fact} {n : Ninst} {xs : List Nat} {r h : Nat} :
    Fact.rdsLe h ∉ opFacts fs n xs r := by
  intro hm
  unfold opFacts at hm
  split at hm <;> (try split at hm) <;>
    simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at hm

theorem rdsLe_not_mem_rdsEff {fs : List Fact} {n : Ninst} {r h : Nat} :
    Fact.rdsLe h ∉ rdsEff fs n r := by
  intro hm
  unfold rdsEff at hm
  split at hm <;> simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_false] at hm

theorem rdsLe_not_mem_touched {fs : List Fact} {a len h : Nat} :
    Fact.rdsLe h ∉ touched fs a len := by
  intro hm
  obtain ⟨t, -, ht⟩ := List.mem_map.mp hm
  cases ht

private theorem gas_shape {fs : List Fact} {fp fp' : Option Nat} {n : Ninst} {kv : List Nat}
    {gas : List Fact} (he : memEff fs fp n kv = some (fp', gas)) :
    gas = [] ∨ ∃ a len, gas = touched fs a len := by
  unfold memEff at he
  split at he <;> (repeat' split at he) <;> (try cases he) <;>
    first
      | exact Or.inl rfl
      | exact Or.inr ⟨_, _, rfl⟩

theorem rdsLe_not_mem_gas {fs : List Fact} {fp fp' : Option Nat} {n : Ninst} {kv : List Nat}
    {gas : List Fact} {h : Nat} (he : memEff fs fp n kv = some (fp', gas)) :
    Fact.rdsLe h ∉ gas := by
  rcases gas_shape he with rfl | ⟨a, len, rfl⟩
  · exact fun hm => nomatch hm
  · exact rdsLe_not_mem_touched

private theorem rdsLe_not_mem_filter {fs : List Fact} {h : Nat} :
    Fact.rdsLe h ∉ fs.filter (! ·.isRds) := by
  intro hm
  have := (List.mem_filter.mp hm).2
  simp only [Fact.isRds, Bool.not_true, Bool.false_eq_true] at this

theorem rdsOf_mem {fs : List Fact} {h : Nat} (hr : rdsOf fs = some h) : Fact.rdsLe h ∈ fs := by
  obtain ⟨f, hf, hfh⟩ := List.exists_of_findSome?_eq_some hr
  cases f <;> simp only [reduceCtorEq, Option.some.injEq] at hfh
  subst hfh
  exact hf

/-- The return-data fact a step keeps or installs bounds the return data after the step: a
regular step keeps the buffer, a `CALL` leaves it below `2 ^ 160` (Jaune
`call_returnData_length_lt_two_pow_160`, under the memory potential `Pot`). -/
theorem rdsKeep_sound {fs : List Fact} {n : Ninst} {p out : Pattern} {sevm : Sevm} {d d' : Devm}
    {h : Nat} (hfork : CoveredFork sevm.benvStat.fork) (ho : ninstTransfer n p = some out)
    (run : Ninst.Run sevm d n d') (pot : Pot d)
    (hrd : ∀ h, Fact.rdsLe h ∈ fs → d.returnData.length ≤ h) (hm : Fact.rdsLe h ∈ rdsKeep n fs) :
    d'.returnData.length ≤ h := by
  cases n with
  | push _ _ => cases ho
  | dupn _ => cases ho
  | swapn _ => cases ho
  | exchange _ => cases ho
  | reg r =>
    rw [ReturnDataKeep.Ninst.Run.reg_returnData hfork.rules_stateGas_none run]
    exact hrd h hm
  | exec x =>
    cases x
    case call =>
      rcases List.mem_cons.mp hm with hm | hm
      · cases hm
        have := call_returnData_length_lt_two_pow_160 run hfork.rules_stateGas_none pot
        unfold memCap
        omega
      · exact absurd hm rdsLe_not_mem_filter
    all_goals exact absurd hm rdsLe_not_mem_filter

/-! ## One step -/

/-- **One accepted step of the free-pointer walk is sound.**  If `σ` describes `d` under `ν`
above `rest`, the checker accepts `n` (`fstep`, beside `absNinst` on the abstract stack `a`, no
shorter than the checker frame), and the step runs with bounded potential before and after, then
the step observes a good free pointer at a free-pointer read, the frame stays no longer than the
abstract stack, and `σ'` describes `d'` above the same `rest` under an updated valuation. -/
theorem fstep_sound {ν : Nat → B256} {σ σ' : FSt} {n : Ninst} {a a' : List AVal} {sevm : Sevm}
    {d d' : Devm} {rest : List B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hs : fstep n σ = some σ') (ha : absNinst n a = some a') (hlen : σ.kv.length ≤ a.length)
    (inv : FpInv ν σ d rest) (run : Ninst.Run sevm d n d') (pot : Pot d) (pot' : Pot d') :
    FpObs d n ∧ σ'.kv.length ≤ a'.length ∧ ∃ ν', FpInv ν' σ' d' rest := by
  obtain ⟨S, hst, hS, hf, hw, hrd⟩ := inv
  by_cases hpush : ∃ (bs : Bytes) (fits : bs.length ≤ 32), n = .push bs fits
  · obtain ⟨bs, fits, rfl⟩ := hpush
    simp only [fstep, Option.some.injEq] at hs
    simp only [absNinst, Option.some.injEq] at ha
    subst hs ha
    have hp := of_run_push run
    have hst' : d'.stack = Bytes.toB256 bs :: d.stack := by
      have := hp.stack
      simpa only [Stack.Push, Split, List.singleton_append] using this
    have hmem : d'.memory = d.memory := hp.memory.symm
    let r := freshSym σ.kv σ.facts σ.fp
    have hr : r ∉ σ.kv := fun h => Nat.lt_irrefl _ (lt_freshSym_kv h)
    refine ⟨(fun h => by cases h), (by simp only [List.length_cons]; omega),
      Function.update ν r (Bytes.toB256 bs), Bytes.toB256 bs :: S, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hst', hst]; rfl
    · exact .cons (Function.update_self _ _ _) (forall₂_update_of_not_mem hr hS)
    · intro f hm
      rcases List.mem_cons.mp hm with rfl | hm
      · show _ ≤ (Function.update ν r _ r).toNat ∧ (Function.update ν r _ r).toNat ≤ _
        simp only [Function.update_self, Nat.le_refl, and_self]
      · exact AllHold.update freshSym_not_mem_syms hf f hm
    · rw [hmem]
      exact hw.congr fun s hs' => upd_ne (Nat.ne_of_lt (lt_freshSym_fp hs'))
    · intro hh hm
      rcases List.mem_cons.mp hm with hm | hm
      · cases hm
      · rw [← hp.returnData]
        exact hrd hh hm
  · have hn : ∀ (bs : Bytes) (fits : bs.length ≤ 32), n ≠ .push bs fits :=
      fun bs fits he => hpush ⟨bs, fits, he⟩
    obtain ⟨hlenA, outA, a0, hA, hr0, rfl⟩ := absNinst_nonpush_spec hn ha
    obtain ⟨out, fp', gas, kv', r', ho, hc, he, hm, hr', rfl⟩ := fstep_nonpush hn hs
    have hlenk : σ.kv.length ≤ 1024 := le_trans hlen hlenA
    let r := freshSym σ.kv σ.facts σ.fp
    have hr : r ∉ σ.kv := fun h => Nat.lt_irrefl _ (lt_freshSym_kv h)
    obtain ⟨kv'', hm''⟩ := mapM_fresh_exists (r := r) hm
    obtain ⟨S', w, hst', hS''⟩ := transfer_val hfork ho hlenk hc hm'' hr hS hst run
    let ν' := Function.update ν r w
    have hνS : List.Forall₂ (fun s x => ν' s = x) σ.kv S := forall₂_update_of_not_mem hr hS
    have hνf : AllHold ν' σ.facts := AllHold.update freshSym_not_mem_syms hf
    have hνw : FpWord ν' σ.fp d.memory := hw.congr fun s hs' =>
      upd_ne (Nat.ne_of_lt (lt_freshSym_fp hs'))
    -- the computed result's word, when the transfer pushes one
    have htop : ∀ o, out = none :: o → d'.stack.head? = some w := by
      intro o ho'
      subst ho'
      rw [List.mapM_cons] at hm''
      cases hk : o.mapM (fun l => match l with | none => some r | some j => σ.kv[j.toNat]?) with
      | none => simp only [hk, Option.pure_def, Option.bind_eq_bind, Option.bind_none,
          Option.bind_fun_none, reduceCtorEq] at hm''
      | some k2 =>
        simp only [hk, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
          Option.some.injEq] at hm''
        subst hm''
        cases hS'' with
        | cons h0 _ =>
          rw [hst', ← h0]
          simp only [Function.update_self, List.cons_append, List.head?_cons]
    have hrr : ν' r' = ν' r := by
      rcases hr' with rfl | ⟨rfl, x, kt, hkv, hcx, rfl⟩
      · rfl
      · obtain ⟨Sx, hSx⟩ : ∃ Sx, S = ν' x :: Sx := by
          rw [hkv] at hνS
          cases hνS with
          | cons h0 _ => exact ⟨_, by rw [h0]⟩
        rw [hkv] at he
        have hstx : d.stack = ν' x :: (Sx ++ rest) := by rw [hst, hSx]; rfl
        obtain ⟨s, hfs, hd'⟩ := memEff_mload_top hcx he hνf hstx hνw run
        obtain ⟨o, rfl⟩ := mload_out_head ho
        have h1 := htop o rfl
        rw [hd'] at h1
        rw [hfs, Option.getD_some]
        show ν' s = ν' r
        rw [Option.some.inj h1]
        exact (Function.update_self r w ν).symm
    refine ⟨?_, ?_, ν', S', hst', mapM_relabel hrr hm hm'' hS'', ?_, ?_, ?_⟩
    · intro hmload h64
      subst hmload
      exact memEff_obs he hf hS hst hw h64
    · rw [mapM_length hm, foldTop_length, mapM_length hr0]
      exact transfer_length_mono ho hA hlen
    · refine AllHold.closeLive _ _
        (AllHold.append (AllHold.append (AllHold.append ?_ ?_) ?_) ?_)
      · by_cases hne : opFacts σ.facts n σ.kv r = []
        · rw [hne]
          exact fun _ h => nomatch h
        · obtain ⟨o, ho'⟩ := opFacts_out_head hne ho
          exact opFacts_sound hf hr hS hst run (htop o ho')
            (fun _ => Nat.le_of_lt pot.size_lt)
      · unfold rdsEff
        split
        · rename_i hh hrds
          intro f hmf
          simp only [List.mem_singleton] at hmf
          subst hmf
          obtain ⟨o, ho'⟩ := rds_out_head ho
          have hv := htop o ho'
          have hst2 : d'.stack = d.returnData.length.toB256 :: d.stack := by
            simpa only [Stack.Push, Split, List.singleton_append] using
              (of_run_returndatasize_val run).stack
          rw [hst2] at hv
          simp only [List.head?_cons, Option.some.injEq] at hv
          show _ ≤ (ν' r).toNat ∧ (ν' r).toNat ≤ hh
          rw [show ν' r = w from Function.update_self _ _ _, ← hv, B256.toNat_toB256, Nat.lo_eq]
          exact ⟨Nat.zero_le _, Nat.le_trans (Nat.mod_le _ _) (hrd hh (rdsOf_mem hrds))⟩
        · exact fun _ h => nomatch h
      · exact memEff_touched ho he hνf hνS hst run pot'
      · intro f hmf
        unfold rdsKeep at hmf
        split at hmf
        · rcases List.mem_cons.mp hmf with rfl | hmf
          · trivial
          · exact hνf f (List.mem_of_mem_filter hmf)
        · exact hνf f (List.mem_of_mem_filter hmf)
        · exact hνf f hmf
    · exact memEff_fpWord hfork ho he hνf hνS hst hνw run
    · intro hh hmf
      rcases List.mem_append.mp (closeLive_sub hmf) with hmf | hmf
      · rcases List.mem_append.mp hmf with hmf | hmf
        · rcases List.mem_append.mp hmf with hmf | hmf
          · exact absurd hmf rdsLe_not_mem_opFacts
          · exact absurd hmf rdsLe_not_mem_rdsEff
        · exact absurd hmf (rdsLe_not_mem_gas he)
      · exact rdsKeep_sound hfork ho run pot hrd hmf

end Blanc.Lift.FreePtr
