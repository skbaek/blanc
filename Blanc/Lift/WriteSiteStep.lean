import Blanc.Lift.WriteSiteTerm
import Blanc.Lift.FreePtrFacts
import Blanc.Lift.MemWrites
import Blanc.Lift.StepTops

/-!
# W3: one step or one join of the write-site checker is sound
-/

namespace Blanc.Lift.WriteSite

open Jaune AbstractStackSafety Blanc.Lift.SymTransfer
open Blanc.Lift.FreePtr (Fact AllHold)

/-! ## The meaning of an abstract state -/

/-- `ε`'s frame constants are those of the frame `sevm` (its entry words are free). -/
def Env.Frame (ε : Env) (sevm : Sevm) : Prop :=
  ε.caller = sevm.caller.toB256 ∧ ε.self = sevm.currentTarget.toB256 ∧ ε.data = sevm.data

theorem Env.root_frame (sevm : Sevm) : (Env.root sevm).Frame sevm := ⟨rfl, rfl, rfl⟩

/-- **The meaning of an abstract write-site state** under the symbol valuation `ν`, in the
environment `ε` of the frame `sevm`: `σ.kv` names the frame words `S`, `σ.args` the entry words,
the facts hold, each recorded term reads its symbol's word, each recorded memory word is in
memory, each `cur` symbol is the current value of its slot and each `ub` symbol is below it, each
recorded `EQ` result compares two words its terms read, and every guard holds. -/
structure WSt.Holds (ε : Env) (sevm : Sevm) (ν : Nat → B256) (σ : WSt) (S : List B256)
    (d : Devm) : Prop where
  kv : List.Forall₂ (fun s w => ν s = w) σ.kv S
  args : σ.args.map ν = ε.args
  facts : AllHold ν σ.facts
  prov : ∀ p ∈ σ.prov, p.2.Den ε (ν p.1)
  mem : ∀ p ∈ σ.mem, p.1 + 32 ≤ d.memory.size ∧ memWord d.memory p.1 = ν p.2
  cur : ∀ p ∈ σ.cur, d.getStorVal sevm.currentTarget (p.2.eval ε) = ν p.1
  ub : ∀ p ∈ σ.ub, (ν p.1).toNat ≤ (d.getStorVal sevm.currentTarget (p.2.eval ε)).toNat
  eqs : ∀ e ∈ σ.eqs, ∃ a b, ν e.1 = B256.eqCheck a b ∧ e.2.1.Den ε a ∧ e.2.2.Den ε b
  guards : ∀ g ∈ σ.guards, g.1.Den ε g.2

/-- The machine state `d` sits in the abstract state `σ`: its stack is `σ`'s frame words above
`rest`, under some valuation. -/
def WSt.Sat (ε : Env) (sevm : Sevm) (σ : WSt) (d : Devm) (rest : List B256) : Prop :=
  ∃ ν S, d.stack = S ++ rest ∧ σ.Holds ε sevm ν S d

section Meaning

variable {ε : Env} {sevm : Sevm} {ν ν' : Nat → B256} {σ : WSt} {S : List B256} {d : Devm}

theorem lookup_mem {β : Type} : ∀ {l : List (Nat × β)} {a : Nat} {b : β},
    l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp only [List.lookup, reduceCtorEq] at h
  | (k, c) :: l, a, b, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hk
      cases h
      rw [beq_iff_eq.mp hk]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem h)

theorem WSt.Holds.provOf (h : σ.Holds ε sevm ν S d) (s : Nat) : (σ.provOf s).Den ε (ν s) := by
  unfold WSt.provOf
  cases hl : σ.prov.lookup s with
  | none => intro hk; exact absurd hk Bool.false_ne_true
  | some t => exact h.prov _ (lookup_mem hl)

theorem WSt.Holds.constOf (h : σ.Holds ε sevm ν S d) {s c : Nat} (hc : σ.constOf s = some c) :
    (ν s).toNat = c := by
  unfold WSt.constOf at hc
  have hd := h.provOf s
  split at hc
  · rename_i k hk
    cases hc
    rw [hk] at hd
    rw [hd rfl]
    rfl
  · cases hc

theorem WSt.Holds.prune (h : σ.Holds ε sevm ν S d) : σ.prune.Holds ε sevm ν S d where
  kv := h.kv
  args := h.args
  facts := h.facts.filter _
  prov := fun p hp => h.prov p (List.mem_of_mem_filter hp)
  mem := h.mem
  cur := h.cur
  ub := h.ub
  eqs := fun e he => h.eqs e (List.mem_of_mem_filter he)
  guards := h.guards

theorem WSt.lt_fresh {s : Nat} (hs : s ∈ σ.syms) : s < σ.fresh :=
  Nat.lt_succ_of_le (le_foldr_max hs)

private theorem forall₂_congr' {ν ν' : Nat → B256} :
    ∀ {l : List Nat} {S : List B256}, (∀ s ∈ l, ν' s = ν s) →
      List.Forall₂ (fun s w => ν s = w) l S → List.Forall₂ (fun s w => ν' s = w) l S
  | [], [], _, _ => .nil
  | s :: _, _ :: _, hl, .cons h0 hr =>
    .cons (by rw [hl s List.mem_cons_self]; exact h0)
      (forall₂_congr' (fun t ht => hl t (List.mem_cons_of_mem _ ht)) hr)

/-- **A state's meaning depends only on its own symbols**, all below `σ.fresh`. -/
theorem WSt.Holds.agree (h : σ.Holds ε sevm ν S d) (hag : ∀ s, s < σ.fresh → ν' s = ν s) :
    σ.Holds ε sevm ν' S d := by
  have hs : ∀ s ∈ σ.syms, ν' s = ν s := fun s hs => hag s (WSt.lt_fresh hs)
  simp only [WSt.syms, List.mem_append, List.mem_flatMap, List.mem_map] at hs
  refine ⟨forall₂_congr' (fun s hm => hs s (.inl (.inl (.inl (.inl (.inl (.inl (.inl (hm))))))))) h.kv,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.guards⟩
  · rw [← h.args]
    exact List.map_congr_left fun s hm => hs s (.inl (.inl (.inl (.inl (.inl (.inl (.inr hm)))))))
  · exact fun f hf => FreePtr.Fact.holds_congr (fun s hm =>
      (hs s (.inl (.inl (.inl (.inl (.inl (.inr ⟨f, hf, hm⟩))))))).symm) (h.facts f hf)
  · intro p hp
    rw [hs p.1 (.inl (.inl (.inl (.inl (.inr ⟨p, hp, rfl⟩)))))]
    exact h.prov p hp
  · intro p hp
    rw [hs p.2 (.inl (.inl (.inl (.inr ⟨p, hp, rfl⟩))))]
    exact h.mem p hp
  · intro p hp
    rw [hs p.1 (.inl (.inl (.inr ⟨p, hp, rfl⟩)))]
    exact h.cur p hp
  · intro p hp
    rw [hs p.1 (.inl (.inr ⟨p, hp, rfl⟩))]
    exact h.ub p hp
  · intro e he
    rw [hs e.1 (.inr ⟨e, he, rfl⟩)]
    exact h.eqs e he

end Meaning

/-! ## Write sites -/

/-- **A site holds of an `SSTORE` of `v` at slot `x`**, read in `ε` over the machine state `d`
before the step: the slot is what the site's term says, its guards hold, and a non-increasing
site does not increase the slot.  `WsObs sites ε sevm d n` is `n = .reg .sstore → ∀ x v rest,
d.stack = x :: v :: rest → ∃ s ∈ sites, s.Obs ε sevm d x v`. -/
def Site.Obs (ε : Env) (sevm : Sevm) (d : Devm) (x v : B256) (s : Site) : Prop :=
  s.slot.Den ε x ∧ (∀ g ∈ s.guards, g.1.Den ε g.2) ∧
    (s.nonInc = true → v.toNat ≤ (d.getStorVal sevm.currentTarget x).toNat)

section Sites

variable {ε : Env} {sevm : Sevm} {d : Devm} {x v : B256}

/-- A covering site holds whenever the covered one does. -/
theorem Site.Obs.of_covers {s o : Site} (hc : s.covers o = true) (ho : o.Obs ε sevm d x v) :
    s.Obs ε sevm d x v := by
  simp only [Site.covers, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true,
    List.contains_iff_mem, Bool.not_eq_true', Bool.or_eq_true] at hc
  obtain ⟨⟨hslot, hg⟩, hn⟩ := hc
  refine ⟨?_, fun g hm => ho.2.1 g (hg g hm), fun h1 => ho.2.2 ?_⟩
  · rcases hslot with h | h
    · rw [h]; intro hk; exact absurd hk Bool.false_ne_true
    · rw [h]; exact ho.1
  · rcases hn with h | h
    · rw [h] at h1; cases h1
    · exact h

/-- An observed site covered by one of `sites` gives a site of `sites` that holds. -/
theorem Site.Obs.of_any {sites : List Site} {o : Site} (hc : sites.any (·.covers o) = true)
    (ho : o.Obs ε sevm d x v) : ∃ s ∈ sites, s.Obs ε sevm d x v := by
  obtain ⟨s, hs, hcs⟩ := List.any_eq_true.mp hc
  exact ⟨s, hs, ho.of_covers hcs⟩

theorem Term.known_of_subst {pa : List Term} :
    ∀ {t : Term}, (t.subst pa).known = true → t.known = true
  | .top, h => h
  | .caller, _ => rfl
  | .self, _ => rfl
  | .const _, _ => rfl
  | .arg _, _ => rfl
  | .cd t, h => Term.known_of_subst (t := t) (mkCd_eq h).1
  | .op2 _ a b, h => by
    obtain ⟨ha, hb⟩ := mkOp2_known h
    show (a.known && b.known) = true
    rw [Term.known_of_subst ha, Term.known_of_subst hb]; rfl
  | .kecc a b, h => by
    obtain ⟨ha, hb, -⟩ := mkKecc_eq h
    show (a.known && b.known) = true
    rw [Term.known_of_subst ha, Term.known_of_subst hb]; rfl
  | .kecc1 t, h => Term.known_of_subst (t := t) (mkKecc1_eq h).1

/-- **Instantiation carries meaning outward**: what a callee term says of a word in the callee's
environment, its instantiation says in the caller's (the converse of `Term.den_subst`). -/
theorem Term.den_subst_of_den {ε ε' : Env} {pa : List Term} {t : Term} {w : B256}
    (hglob : ε'.caller = ε.caller ∧ ε'.self = ε.self ∧ ε'.data = ε.data)
    (hpa : ∀ (i : Nat) (u : Term), pa[i]? = some u → u.known = true → ε'.args[i]? = some (u.eval ε))
    (h : t.Den ε' w) : (t.subst pa).Den ε w := fun hk => by
  rw [h (Term.known_of_subst hk), Term.eval_subst hglob hpa t hk]

/-- **A callee site holding in the callee's environment gives its instantiation holding in the
caller's**, given the caller's guards. -/
theorem instSite_obs {ε' : Env} {pa : List Term} {gs : List (Term × B256)} {s : Site}
    (hglob : ε'.caller = ε.caller ∧ ε'.self = ε.self ∧ ε'.data = ε.data)
    (hpa : ∀ (i : Nat) (u : Term), pa[i]? = some u → u.known = true → ε'.args[i]? = some (u.eval ε))
    (hgs : ∀ g ∈ gs, g.1.Den ε g.2) (h : s.Obs ε' sevm d x v) :
    (instSite pa gs s).Obs ε sevm d x v := by
  refine ⟨Term.den_subst_of_den hglob hpa h.1, fun g hg => ?_, h.2.2⟩
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp (List.mem_of_mem_filter hg)
    exact Term.den_subst_of_den hglob hpa (h.2.1 g' hg')
  · exact hgs g hg

/-- The two top frame words of a state holding over `d`. -/
theorem WSt.Holds.top2 {ν : Nat → B256} {σ : WSt} {S rest rs : List B256} {k v' : Nat}
    {t : List Nat} (h : σ.Holds ε sevm ν S d) (hkv : σ.kv = k :: v' :: t)
    (hS : d.stack = S ++ rest) (hs : d.stack = x :: v :: rs) : x = ν k ∧ v = ν v' := by
  have hk := h.kv
  rw [hkv] at hk
  cases hk with
  | cons e0 hk =>
    cases hk with
    | cons e1 _ =>
      rw [hS, List.cons_append, List.cons_append] at hs
      simp only [List.cons.injEq] at hs
      exact ⟨by rw [← hs.1, ← e0], by rw [← hs.2.1, ← e1]⟩

/-- **The site an `SSTORE` observes holds** of the executed write. -/
theorem siteOf_obs {ν : Nat → B256} {σ : WSt} {S rest rs : List B256} {k v' : Nat}
    {t : List Nat} (h : σ.Holds ε sevm ν S d) (hkv : σ.kv = k :: v' :: t)
    (hS : d.stack = S ++ rest) (hs : d.stack = x :: v :: rs) :
    (siteOf σ k v').Obs ε sevm d x v := by
  obtain ⟨rfl, rfl⟩ := h.top2 hkv hS hs
  refine ⟨h.provOf k, h.guards, fun hn => ?_⟩
  simp only [siteOf, Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true,
    beq_iff_eq] at hn
  obtain ⟨hk, hn⟩ := hn
  have hx : ν k = (σ.provOf k).eval ε := h.provOf k hk
  rw [hx]
  rcases hn with (hu | hc) | ⟨p, hp, hT, he⟩
  · exact h.ub (v', σ.provOf k) hu
  · rw [h.cur (v', σ.provOf k) hc]
  · have hle := FreePtr.entails_sound h.facts he
    have hc := h.cur p hp
    rw [hT] at hc
    rw [hc]
    exact hle

end Sites


/-! ## The memory map -/

section Memory

variable {ν : Nat → B256} {mem : List (Nat × Nat)} {μ μ' : Mem}

/-- The memory map's meaning (`WSt.Holds.mem`). -/
def MemHolds (ν : Nat → B256) (mem : List (Nat × Nat)) (μ : Mem) : Prop :=
  ∀ p ∈ mem, p.1 + 32 ≤ μ.size ∧ memWord μ p.1 = ν p.2

/-- The words ending at or below an untouched prefix survive (`memBelow`).  Memory is indexed by
naturals, so a write whose window starts at or above `b` never reaches below `b`, whether or not
the window crosses `2 ^ 256`: no gas argument is needed (`Mem.WritesAt.agreeBelow`). -/
theorem memBelow_holds {b : Nat} (hm : MemHolds ν mem μ) (hag : Mem.AgreeBelow μ μ' b) :
    MemHolds ν (memBelow mem b) μ' := by
  intro p hp
  simp only [memBelow, List.mem_filter, decide_eq_true_eq] at hp
  obtain ⟨hp, hb⟩ := hp
  obtain ⟨hsz, hw⟩ := hm p hp
  refine ⟨le_trans hsz hag.1, ?_⟩
  rw [memWord_congr (μ := μ) (fun j hj => hag.2 _ (by omega) (by omega))]
  exact hw

/-- The words a write's window misses survive (`memKillS`). -/
theorem memKillS_holds {lo hi : Nat} (hm : MemHolds ν mem μ) (hag : Mem.AgreeOutside μ μ' lo hi) :
    MemHolds ν (memKillS mem lo hi) μ' := by
  intro p hp
  simp only [memKillS, List.mem_filter, Bool.or_eq_true, decide_eq_true_eq] at hp
  obtain ⟨hp, hout⟩ := hp
  obtain ⟨hsz, hw⟩ := hm p hp
  refine ⟨le_trans hsz hag.1, ?_⟩
  rw [memWord_congr (μ := μ) (fun j hj => hag.2 _ (by omega) (by omega))]
  exact hw

theorem MemHolds.keep {d d' : Devm} (hm : MemHolds ν mem d.memory) (hk : MemKeep d d') :
    MemHolds ν mem d'.memory := by
  intro p hp
  obtain ⟨hsz, hw⟩ := hm p hp
  refine ⟨le_trans hsz hk.2, ?_⟩
  rw [memWord_congr (μ := d.memory) (fun j _ => by rw [hk.1])]
  exact hw

end Memory

theorem forall₂_eq_map {ν : Nat → B256} :
    ∀ {kv : List Nat} {S : List B256}, List.Forall₂ (fun s w => ν s = w) kv S → S = kv.map ν
  | [], [], _ => rfl
  | _ :: _, _ :: _, .cons h0 hr => by rw [List.map_cons, ← h0, ← forall₂_eq_map hr]

/-- **The memory map after a step** (`memEff`): a constant `MSTORE` records its word; every
write whose offset the facts bound from below keeps the words ending below that bound; every
other instruction keeps memory or forgets the map. -/
theorem memEff_sound {ε : Env} {sevm : Sevm} {ν : Nat → B256} {σ : WSt} {S rest : List B256}
    {d d' : Devm} {n : Ninst} (hfork : CoveredFork sevm.benvStat.fork)
    (h : σ.Holds ε sevm ν S d) (hS : d.stack = S ++ rest) (run : Ninst.Run sevm d n d')
    (hcc : n ≠ .exec .callcode) : MemHolds ν (memEff σ n) d'.memory := by
  have hst : d.stack = σ.kv.map ν ++ rest := by rw [hS, forall₂_eq_map h.kv]
  have hm : MemHolds ν σ.mem d.memory := h.mem
  have hget : ∀ {i s : Nat}, σ.kv[i]? = some s → d.stack[i]? = some (ν s) := fun {i s} hi => by
    rw [hst, List.getElem?_append_left (by rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hi).1),
      List.getElem?_map, hi]
    rfl
  unfold memEff
  split
  · rename_i a v t hkv
    have hs : d.stack = ν a :: ν v :: (t.map ν ++ rest) := by
      rw [hst, hkv]; rfl
    have hmem := mstore_run_memory run hs
    dsimp only
    split
    · rename_i o ho
      rw [hmem, h.constOf ho]
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨(Mem.memWord_write_word _ _ _).2, (Mem.memWord_write_word _ _ _).1⟩
      · have hag := Mem.write_agree d.memory o (ν v).toBytes
        rw [B256.length_toBytes] at hag
        exact memKillS_holds hm hag p hp
    · rw [hmem]
      exact memBelow_holds hm ((Mem.WritesAt.write _ _ _).agreeBelow.mono (FreePtr.lo_le h.facts a))
  · rename_i a b t hkv
    have hs : d.stack = ν a :: ν b :: (t.map ν ++ rest) := by
      rw [hst, hkv]; rfl
    have hmem := mstore8_run_memory run hs
    dsimp only
    split
    · rename_i o ho
      rw [hmem, h.constOf ho]
      exact memKillS_holds hm (Mem.write_agree d.memory o [(ν b).2.2.toUInt8])
    · rw [hmem]
      exact memBelow_holds hm ((Mem.WritesAt.write _ _ _).agreeBelow.mono (FreePtr.lo_le h.facts a))
  · rename_i dd t hkv
    have h0 : d.stack.head? = some (ν dd) := by
      rw [List.head?_eq_getElem?]
      exact hget (by rw [hkv]; rfl)
    exact memBelow_holds hm ((calldatacopy_run_writesAt run h0).agreeBelow.mono
      (FreePtr.lo_le h.facts dd))
  · rename_i dd t hkv
    have h0 : d.stack.head? = some (ν dd) := by
      rw [List.head?_eq_getElem?]
      exact hget (by rw [hkv]; rfl)
    exact memBelow_holds hm ((codecopy_run_writesAt run h0).agreeBelow.mono
      (FreePtr.lo_le h.facts dd))
  · rename_i dd t hkv
    have h0 : d.stack.head? = some (ν dd) := by
      rw [List.head?_eq_getElem?]
      exact hget (by rw [hkv]; rfl)
    exact memBelow_holds hm ((returndatacopy_run_writesAt run h0).agreeBelow.mono
      (FreePtr.lo_le h.facts dd))
  · rename_i dd t hkv
    have h0 : d.stack.head? = some (ν dd) := by
      rw [List.head?_eq_getElem?]
      exact hget (by rw [hkv]; rfl)
    exact memBelow_holds hm ((mcopy_run_writesAt run h0).agreeBelow.mono
      (FreePtr.lo_le h.facts dd))
  · rename_i ad dd t hkv
    exact memBelow_holds hm ((extcodecopy_run_writesAt run
      (hget (by rw [hkv]; rfl))).agreeBelow.mono (FreePtr.lo_le h.facts dd))
  · rename_i h4 h3 h2 h1 h0 o t hkv
    exact memBelow_holds hm ((call_run_writesAt hfork run
      (hget (by rw [hkv]; rfl))).agreeBelow.mono (FreePtr.lo_le h.facts o))
  · exact absurd rfl hcc
  · rename_i h3 h2 h1 h0 o t hkv
    exact memBelow_holds hm ((delegatecall_run_writesAt hfork run
      (hget (by rw [hkv]; rfl))).agreeBelow.mono (FreePtr.lo_le h.facts o))
  · rename_i h3 h2 h1 h0 o t hkv
    exact memBelow_holds hm ((staticcall_run_writesAt hfork run
      (hget (by rw [hkv]; rfl))).agreeBelow.mono (FreePtr.lo_le h.facts o))
  · dsimp only
    split
    · rename_i hk
      exact hm.keep (ninstMemKeeps_run hk run)
    · intro p hp
      cases hp

/-! ## Provenance terms of fresh results -/

theorem Array.sliceD_add {ξ : Type} (xs : Array ξ) (m a : Nat) (dflt : ξ) :
    ∀ b, xs.sliceD m (a + b) dflt = xs.sliceD m a dflt ++ xs.sliceD (m + a) b dflt
  | 0 => by
    rw [Nat.add_zero, Array.sliceD_eq_map xs (m + a) 0, List.range_zero, List.map_nil,
      List.append_nil]
  | b + 1 => by
    rw [← Nat.add_assoc, Array.sliceD_eq_map, List.range_succ, List.map_append,
      ← Array.sliceD_eq_map, Array.sliceD_add xs m a dflt b, Array.sliceD_eq_map xs (m + a) (b + 1),
      List.range_succ, List.map_append, ← Array.sliceD_eq_map, List.append_assoc, List.map_cons,
      List.map_cons, List.map_nil, List.map_nil, Nat.add_assoc]

/-- The 64 bytes at `o` are the two memory words at `o` and `o + 32`. -/
theorem sliceD_64 (μ : Mem) (o : Nat) :
    μ.data.sliceD o 64 0 = (memWord μ o).toBytes ++ (memWord μ (o + 32)).toBytes := by
  rw [show (64 : Nat) = 32 + 32 from rfl, Array.sliceD_add]
  have hl : ∀ i, (μ.data.sliceD i 32 0).length = 32 := fun i => by
    rw [Array.sliceD_eq_map, List.length_map, List.length_range]
  unfold memWord Mem.read
  rw [Bytes.toBytes_toB256_of_length (hl o), Bytes.toBytes_toB256_of_length (hl (o + 32))]

/-- The binary operations a term records compute what the instruction pushes. -/
theorem run_op2_top {sevm : Sevm} {d d' : Devm} {r : Rinst} {o : Op2} {x y : B256}
    {rest : List B256} (ho : Op2.ofRinst r = some o) (run : Ninst.Run sevm d (.reg r) d')
    (hs : d.stack = x :: y :: rest) : d'.stack = o.eval x y :: rest := by
  match r, ho with
  | .add, rfl => exact run_add_top run hs
  | .sub, rfl => exact run_sub_top run hs
  | .mul, rfl => exact run_mul_top run hs
  | .div, rfl => exact run_div_top run hs
  | .and, rfl => exact run_and_top run hs
  | .or, rfl => exact run_or_top run hs
  | .shl, rfl => exact run_shl_top run hs
  | .shr, rfl => exact run_shr_top run hs
  | .exp, rfl => exact run_exp_top run hs

/-- **The term `provEff` records for a fresh result reads the word the step pushes.** -/
theorem provEff_sound {ε : Env} {sevm : Sevm} {ν : Nat → B256} {σ : WSt} {S rest : List B256}
    {d d' : Devm} {n : Ninst} (hε : ε.Frame sevm) (h : σ.Holds ε sevm ν S d)
    (hS : d.stack = S ++ rest) (run : Ninst.Run sevm d n d') {w : B256} {rs : List B256}
    (htop : d'.stack = w :: rs) : (provEff σ n).Den ε w := by
  have hst : d.stack = σ.kv.map ν ++ rest := by rw [hS, forall₂_eq_map h.kv]
  unfold provEff
  split
  · rw [run_caller_top run] at htop
    intro _
    rw [← (List.cons.inj htop).1]
    exact hε.1.symm
  · rw [run_address_top run] at htop
    intro _
    rw [← (List.cons.inj htop).1]
    exact hε.2.1.symm
  · rename_i x t hkv
    intro hk
    obtain ⟨hk, he⟩ := mkCd_eq hk
    rw [he]
    have hs : d.stack = ν x :: (t.map ν ++ rest) := by rw [hst, hkv]; rfl
    rw [run_calldataload_top run hs] at htop
    rw [← (List.cons.inj htop).1, h.provOf x hk]
    show _ = Bytes.toB256 (ε.data.sliceD _ 32 0)
    rw [hε.2.2]
  · rename_i x t hkv
    have hs : d.stack = ν x :: (t.map ν ++ rest) := by rw [hst, hkv]; rfl
    rw [run_not_top run hs] at htop
    split
    · rename_i c hc
      intro _
      have hx := h.provOf x
      rw [hc] at hx
      rw [← (List.cons.inj htop).1, hx rfl]
      rfl
    · intro hk; exact absurd hk Bool.false_ne_true
  · rename_i o l t hkv
    have hs : d.stack = ν o :: ν l :: (t.map ν ++ rest) := by rw [hst, hkv]; rfl
    rw [run_keccak256_top run hs] at htop
    have hw := (List.cons.inj htop).1
    split
    · rename_i o' ho hl
      rw [h.constOf ho, h.constOf hl] at hw
      split
      · rename_i s0 s1 h0 h1
        intro hk
        obtain ⟨hk0, hk1, he⟩ := mkKecc_eq hk
        rw [he]
        have m0 := (h.mem _ (lookup_mem h0)).2
        have m1 := (h.mem _ (lookup_mem h1)).2
        rw [← hw, sliceD_64, m0, m1]
        show _ = mapSlot _ _
        rw [← h.provOf s0 hk0, ← h.provOf s1 hk1]
        rfl
      · intro hk; exact absurd hk Bool.false_ne_true
    · rename_i o' ho hl
      rw [h.constOf ho, h.constOf hl] at hw
      split
      · rename_i s0 h0
        intro hk
        obtain ⟨hk0, he⟩ := mkKecc1_eq hk
        rw [he]
        have m0 := (h.mem _ (lookup_mem h0)).2
        rw [← hw]
        show _ = ((Term.eval ε (σ.provOf s0)).toBytes).keccak
        rw [← h.provOf s0 hk0, ← m0]
        unfold memWord Mem.read
        rw [Bytes.toBytes_toB256_of_length (by rw [Array.sliceD_eq_map, List.length_map,
          List.length_range])]
      · intro hk; exact absurd hk Bool.false_ne_true
    · intro hk; exact absurd hk Bool.false_ne_true
  · rename_i r x y t _ _ _ _ _ hkv
    have hs : d.stack = ν x :: ν y :: (t.map ν ++ rest) := by rw [hst, hkv]; rfl
    split
    · rename_i o ho
      rw [run_op2_top ho run hs] at htop
      intro hk
      obtain ⟨hx, hy⟩ := mkOp2_known hk
      rw [← (List.cons.inj htop).1, mkOp2_eval ε o hx hy, ← h.provOf x hx, ← h.provOf y hy]
    · intro hk; exact absurd hk Bool.false_ne_true
  · intro hk; exact absurd hk Bool.false_ne_true

/-! ## The one fresh result sits on top -/

/-- The regular instructions whose recorded result the checker names: each pushes one computed
word on top. -/
def pushesTop (r : Rinst) : Bool :=
  r matches .add | .sub | .mul | .div | .and | .or | .shl | .shr | .exp | .lt | .gt | .eq
    | .iszero | .caller | .address | .calldataload | .not | .keccak256 | .sload

theorem pushesTop_head {r : Rinst} {p out : Pattern} (hr : pushesTop r = true)
    (hout : ninstTransfer (.reg r) p = some out) : ∃ o, out = none :: o := by
  cases r <;> simp only [pushesTop, Bool.false_eq_true] at hr <;>
    simp only [ninstTransfer, liftRegularTransfer, regularTransfer, binaryTransfer,
      unaryTransfer] at hout
  all_goals first
    | exact ⟨_, (Option.some.inj hout).symm⟩
    | (split at hout <;> simp only [Option.some.injEq, reduceCtorEq] at hout
       exact ⟨_, hout.symm⟩)

theorem opFacts_pushesTop {fs : List Fact} {kv : List Nat} {n : Ninst} {r : Nat}
    (hne : FreePtr.opFacts fs n kv r ≠ []) :
    ∃ q, n = .reg q ∧ (pushesTop q = true ∨ q = .msize) := by
  cases n with
  | reg q =>
    refine ⟨q, rfl, ?_⟩
    cases q <;> first | exact .inl rfl | exact .inr rfl |
      exact (hne (by simp only [FreePtr.opFacts])).elim
  | _ => exact (hne (by simp only [FreePtr.opFacts])).elim

theorem provEff_pushesTop {σ : WSt} {n : Ninst} (hk : (provEff σ n).known = true) :
    ∃ q, n = .reg q ∧ pushesTop q = true := by
  unfold provEff at hk
  split at hk
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · rename_i q _ _ _ _ _ _ _ _ _
    split at hk
    · rename_i o ho
      refine ⟨q, rfl, ?_⟩
      cases q <;> simp only [Op2.ofRinst, reduceCtorEq] at ho <;> rfl
    · exact absurd hk Bool.false_ne_true
  · exact absurd hk Bool.false_ne_true

/-- The word under the fresh symbol of a transfer whose output starts with the fresh result is
the top word after the step. -/
theorem fresh_top {ν : Nat → B256} {r : Nat} {w : B256} {o : Pattern} {kv kv' : List Nat}
    {S' rest : List B256} {d' : Devm}
    (hm : (none :: o).mapM (fun l => match l with | none => some r | some j => kv[j.toNat]?) =
      some kv')
    (hf : List.Forall₂ (fun s x => Function.update ν r w s = x) kv' S')
    (hst : d'.stack = S' ++ rest) : ∃ rs, d'.stack = w :: rs := by
  rw [List.mapM_cons] at hm
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some] at hm
  cases ht : o.mapM (fun l => match l with | none => some r | some j => kv[j.toNat]?) with
  | none => simp only [ht, Option.bind_none, reduceCtorEq] at hm
  | some kt =>
    simp only [ht, Option.bind_some, Option.some.injEq] at hm
    subst hm
    cases hf with
    | cons h0 _ =>
      rw [Function.update_self] at h0
      subst h0
      exact ⟨_, by rw [hst]; rfl⟩

theorem B256.toNat_sub_of_le {x y : B256} (h : y.toNat ≤ x.toNat) :
    (x - y).toNat = x.toNat - y.toNat := by
  rw [B256.toNat_sub, Nat.lo, Nat.add_sub_mod_eq_sub (B256.toNat_lt x) h]

/-- Two readings of one transfer that differ only in the fresh symbol. -/
theorem mapM_swap {kv : List Nat} {r s : Nat} :
    ∀ {out : Pattern} {b : List Nat},
      out.mapM (fun l => match l with | none => some s | some j => kv[j.toNat]?) = some b →
      ∃ a, out.mapM (fun l => match l with | none => some r | some j => kv[j.toNat]?) = some a ∧
        List.Forall₂ (fun x y => x = y ∨ (x = r ∧ y = s)) a b
  | [], b, hb => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hb
    exact ⟨[], rfl, by rw [← hb]; exact .nil⟩
  | l :: out, b, hb => by
    rw [List.mapM_cons] at hb ⊢
    simp only [Option.pure_def, Option.bind_eq_bind] at hb ⊢
    cases ht : out.mapM (fun l => match l with | none => some s | some j => kv[j.toNat]?) with
    | none => cases l <;> simp only [ht, Option.bind_none, Option.bind_fun_none,
        reduceCtorEq] at hb
    | some bt =>
      obtain ⟨at', ha, hab⟩ := mapM_swap ht
      cases l with
      | none =>
        simp only [ht, Option.bind_some, Option.some.injEq] at hb
        subst hb
        exact ⟨r :: at', by simp only [ha, Option.bind_some], .cons (.inr ⟨rfl, rfl⟩) hab⟩
      | some j =>
        cases hj : kv[j.toNat]? with
        | none => simp only [hj, Option.bind_none, reduceCtorEq] at hb
        | some y =>
          simp only [hj, ht, Option.bind_some, Option.some.injEq] at hb
          subst hb
          exact ⟨y :: at', by simp only [hj, ha, Option.bind_some], .cons (.inl rfl) hab⟩

theorem sloadName_some {σ : WSt} {n : Ninst} {s : Nat} (h : sloadName σ n = some s) :
    n = .reg .sload ∧ ∃ k t, σ.kv = k :: t ∧ (σ.provOf k).known = true ∧
      (s, σ.provOf k) ∈ σ.cur := by
  unfold sloadName at h
  split at h
  · rename_i k t hkv
    dsimp only at h
    split at h
    · rename_i hk
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
      have hm := List.mem_of_find?_eq_some hp
      have he := List.find?_some hp
      simp only [beq_iff_eq] at he
      refine ⟨rfl, k, t, hkv, hk, ?_⟩
      rw [← he]
      exact hm
    · cases h
  · cases h

/-- A step that keeps memory and the executing account's storage keeps a state's meaning. -/
theorem WSt.Holds.of_keep {ε : Env} {sevm : Sevm} {ν : Nat → B256} {σ : WSt} {S : List B256}
    {d d' : Devm} (h : σ.Holds ε sevm ν S d) (hk : MemKeep d d')
    (hst : Devm.getStor d' sevm.currentTarget = Devm.getStor d sevm.currentTarget) :
    σ.Holds ε sevm ν S d' where
  kv := h.kv
  args := h.args
  facts := h.facts
  prov := h.prov
  mem := MemHolds.keep h.mem hk
  cur := fun p hp => by
    show (Devm.getStor d' _).get _ = _
    rw [hst]
    exact h.cur p hp
  ub := fun p hp => by
    show _ ≤ ((Devm.getStor d' _).get _).toNat
    rw [hst]
    exact h.ub p hp
  eqs := h.eqs
  guards := h.guards

/-- A step `wstep` accepts that does not write storage keeps it. -/
theorem getStor_of_writesStor {sevm : Sevm} {d d' : Devm} {n : Ninst} {p out : Pattern}
    (hfork : CoveredFork sevm.benvStat.fork) (ho : ninstTransfer n p = some out)
    (hn : n.writesStor = false) (run : Ninst.Run sevm d n d') :
    Devm.getStor d' = Devm.getStor d := by
  cases n with
  | reg q =>
    refine Ninst.Run.getStor_of_storKeep hfork (.inl ⟨q, rfl, fun hq => ?_⟩) run
    subst hq
    cases hn
  | exec x =>
    have : x = .staticcall := by
      simpa only [Ninst.writesStor, bne_eq_false_iff_eq] using hn
    subst this
    exact Ninst.Run.getStor_of_storKeep hfork (.inr rfl) run
  | push bs fits => simp only [ninstTransfer, reduceCtorEq] at ho
  | dupn _ => simp only [ninstTransfer, reduceCtorEq] at ho
  | swapn _ => simp only [ninstTransfer, reduceCtorEq] at ho
  | exchange _ => simp only [ninstTransfer, reduceCtorEq] at ho

private theorem list_shape {α : Type} (l : List α) :
    l = [] ∨ (∃ k, l = [k]) ∨ ∃ k v t, l = k :: v :: t := by
  rcases l with _ | ⟨k, _ | ⟨v, t⟩⟩
  · exact .inl rfl
  · exact .inr (.inl ⟨k, rfl⟩)
  · exact .inr (.inr ⟨k, v, t, rfl⟩)

private theorem of_guard {p : Prop} [Decidable p] {u : Unit}
    (h : (guard p : Option Unit) = some u) : p := by
  by_contra hp
  simp only [guard, hp, ite_false, Option.failure_eq_none, reduceCtorEq] at h

/-- What `wstep` does on a non-push instruction, with its four instruction-specific lists named
and characterised (so that consumers never unfold `wstep`). -/
theorem wstep_nonpush {R : WRet} {n : Ninst} {σ σ' : WSt}
    (hn : ∀ (bs : Bytes) (fits : bs.length ≤ 32), n ≠ .push bs fits)
    (h : wstep R n σ = some σ') :
    ∃ (out : Pattern) (kv' : List Nat) (sl : List Fact) (cl ul : List (Nat × Term))
      (el : List (Nat × Term × Term)),
      ninstTransfer n (indexPattern σ.kv.length) = some out ∧ out.count none ≤ 1 ∧
      (R.keeps && n.writesStor) = false ∧
      (∀ k v t, n = .reg .sstore → σ.kv = k :: v :: t →
        R.sites.any (·.covers (siteOf σ k v)) = true) ∧
      out.mapM (fun l => match l with
        | none => some ((sloadName σ n).getD σ.fresh)
        | some j => σ.kv[j.toNat]?) = some kv' ∧
      σ' = WSt.prune {
        kv := kv', args := σ.args,
        facts := sl ++ FreePtr.opFacts σ.facts n σ.kv σ.fresh ++ σ.facts,
        prov := (if (provEff σ n).known && decide ((sloadName σ n).getD σ.fresh = σ.fresh) then
          [(σ.fresh, provEff σ n)] else []) ++ σ.prov,
        mem := memEff σ n,
        cur := cl ++ (if !n.writesStor then σ.cur else []),
        ub := ul ++ (if !n.writesStor then σ.ub else []),
        eqs := el ++ σ.eqs,
        guards := σ.guards } ∧
      (sl = [] ∨ ∃ x y t, n = .reg .sub ∧ σ.kv = x :: y :: t ∧
        FreePtr.entails σ.facts (.le y x) = true ∧ sl = [.le σ.fresh x]) ∧
      (cl = [] ∨ ∃ k t, n = .reg .sload ∧ σ.kv = k :: t ∧ (σ.provOf k).known = true ∧
        (sloadName σ n).getD σ.fresh = σ.fresh ∧ cl = [(σ.fresh, σ.provOf k)]) ∧
      (ul = [] ∨ ∃ x y t, n = .reg .sub ∧ σ.kv = x :: y :: t ∧
        FreePtr.entails σ.facts (.le y x) = true ∧
        ul = (σ.cur ++ σ.ub).filterMap fun p => if p.1 = x then some (σ.fresh, p.2) else none) ∧
      (el = [] ∨ ∃ x y t, n = .reg .eq ∧ σ.kv = x :: y :: t ∧
        el = [(σ.fresh, σ.provOf x, σ.provOf y)]) := by
  cases n
  case push bs fits => exact (hn bs fits rfl).elim
  all_goals unfold wstep at h; dsimp only at h
  all_goals try
    (simp only [ninstTransfer, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at h; done)
  case reg a =>
    cases a
    all_goals try dsimp only at h
    case sstore =>
      rcases list_shape σ.kv with hkv | ⟨k, hkv⟩ | ⟨k, v, t, hkv⟩
      all_goals rw [hkv] at h; dsimp only at h; rw [← hkv] at h
      · simp only [Option.bind_eq_bind] at h
        obtain ⟨out, ho, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u1, hg1, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u2, hg2, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨kv', hm, h⟩ := Option.bind_eq_some_iff.mp h
        exact ⟨out, kv', _, _, _, _, ho, of_guard hg1,
          (by simpa only [Bool.not_eq_true'] using of_guard hg2), (fun _ _ _ _ h' => by rw [hkv] at h'; cases h'), hm,
          (Option.some.inj h).symm, .inl rfl, .inl rfl, .inl rfl, .inl rfl⟩
      · simp only [Option.bind_eq_bind] at h
        obtain ⟨out, ho, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u1, hg1, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u2, hg2, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨kv', hm, h⟩ := Option.bind_eq_some_iff.mp h
        exact ⟨out, kv', _, _, _, _, ho, of_guard hg1,
          (by simpa only [Bool.not_eq_true'] using of_guard hg2), (fun _ _ _ _ h' => by rw [hkv] at h'; cases h'), hm,
          (Option.some.inj h).symm, .inl rfl, .inl rfl, .inl rfl, .inl rfl⟩
      · simp only [Option.bind_eq_bind] at h
        obtain ⟨out, ho, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u1, hg1, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u2, hg2, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u3, hg3, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨kv', hm, h⟩ := Option.bind_eq_some_iff.mp h
        exact ⟨out, kv', _, _, _, _, ho, of_guard hg1,
          (by simpa only [Bool.not_eq_true'] using of_guard hg2), (fun k' v' t' _ h' => by
            rw [hkv] at h'
            injection h' with e1 h'
            injection h' with e2
            subst e1 e2
            exact of_guard hg3), hm,
          (Option.some.inj h).symm, .inl rfl, .inl rfl, .inl rfl, .inl rfl⟩
    case sub =>
      rcases list_shape σ.kv with hkv | ⟨k, hkv⟩ | ⟨x, y, t, hkv⟩
      all_goals rw [hkv] at h; dsimp only at h; rw [← hkv] at h
      · simp only [Option.bind_eq_bind] at h
        obtain ⟨out, ho, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u1, hg1, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u2, hg2, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨kv', hm, h⟩ := Option.bind_eq_some_iff.mp h
        exact ⟨out, kv', _, _, _, _, ho, of_guard hg1,
          (by simpa only [Bool.not_eq_true'] using of_guard hg2), (fun _ _ _ hN => by cases hN), hm,
          (Option.some.inj h).symm, .inl rfl, .inl rfl, .inl rfl, .inl rfl⟩
      · simp only [Option.bind_eq_bind] at h
        obtain ⟨out, ho, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u1, hg1, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u2, hg2, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨kv', hm, h⟩ := Option.bind_eq_some_iff.mp h
        exact ⟨out, kv', _, _, _, _, ho, of_guard hg1,
          (by simpa only [Bool.not_eq_true'] using of_guard hg2), (fun _ _ _ hN => by cases hN), hm,
          (Option.some.inj h).symm, .inl rfl, .inl rfl, .inl rfl, .inl rfl⟩
      · simp only [Option.bind_eq_bind] at h
        obtain ⟨out, ho, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u1, hg1, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u2, hg2, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨kv', hm, h⟩ := Option.bind_eq_some_iff.mp h
        exact ⟨out, kv', _, _, _, _, ho, of_guard hg1,
          (by simpa only [Bool.not_eq_true'] using of_guard hg2), (fun _ _ _ hN => by cases hN), hm,
          (Option.some.inj h).symm, (by split; exact .inr ⟨x, y, t, rfl, hkv, by assumption, rfl⟩; exact .inl rfl), .inl rfl,
          (by split; exact .inr ⟨x, y, t, rfl, hkv, by assumption, rfl⟩; exact .inl rfl), .inl rfl⟩
    case sload =>
      rcases list_shape σ.kv with hkv | ⟨k, hkv⟩ | ⟨k, v, t, hkv⟩
      all_goals rw [hkv] at h; dsimp only at h; rw [← hkv] at h
      · simp only [Option.bind_eq_bind] at h
        obtain ⟨out, ho, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u1, hg1, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u2, hg2, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨kv', hm, h⟩ := Option.bind_eq_some_iff.mp h
        exact ⟨out, kv', _, _, _, _, ho, of_guard hg1,
          (by simpa only [Bool.not_eq_true'] using of_guard hg2), (fun _ _ _ hN => by cases hN), hm,
          (Option.some.inj h).symm, .inl rfl, .inl rfl, .inl rfl, .inl rfl⟩
      · simp only [Option.bind_eq_bind] at h
        obtain ⟨out, ho, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u1, hg1, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u2, hg2, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨kv', hm, h⟩ := Option.bind_eq_some_iff.mp h
        exact ⟨out, kv', _, _, _, _, ho, of_guard hg1,
          (by simpa only [Bool.not_eq_true'] using of_guard hg2), (fun _ _ _ hN => by cases hN), hm,
          (Option.some.inj h).symm, .inl rfl, (by
            split
            · rename_i hb
              exact .inr ⟨k, [], rfl, hkv, (Bool.and_eq_true_iff.mp hb).1,
                of_decide_eq_true (Bool.and_eq_true_iff.mp hb).2, rfl⟩
            · exact .inl rfl), .inl rfl, .inl rfl⟩
      · simp only [Option.bind_eq_bind] at h
        obtain ⟨out, ho, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u1, hg1, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u2, hg2, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨kv', hm, h⟩ := Option.bind_eq_some_iff.mp h
        exact ⟨out, kv', _, _, _, _, ho, of_guard hg1,
          (by simpa only [Bool.not_eq_true'] using of_guard hg2), (fun _ _ _ hN => by cases hN), hm,
          (Option.some.inj h).symm, .inl rfl, (by
            split
            · rename_i hb
              exact .inr ⟨k, v :: t, rfl, hkv, (Bool.and_eq_true_iff.mp hb).1,
                of_decide_eq_true (Bool.and_eq_true_iff.mp hb).2, rfl⟩
            · exact .inl rfl), .inl rfl, .inl rfl⟩
    case eq =>
      rcases list_shape σ.kv with hkv | ⟨k, hkv⟩ | ⟨x, y, t, hkv⟩
      all_goals rw [hkv] at h; dsimp only at h; rw [← hkv] at h
      · simp only [Option.bind_eq_bind] at h
        obtain ⟨out, ho, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u1, hg1, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u2, hg2, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨kv', hm, h⟩ := Option.bind_eq_some_iff.mp h
        exact ⟨out, kv', _, _, _, _, ho, of_guard hg1,
          (by simpa only [Bool.not_eq_true'] using of_guard hg2), (fun _ _ _ hN => by cases hN), hm,
          (Option.some.inj h).symm, .inl rfl, .inl rfl, .inl rfl, .inl rfl⟩
      · simp only [Option.bind_eq_bind] at h
        obtain ⟨out, ho, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u1, hg1, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u2, hg2, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨kv', hm, h⟩ := Option.bind_eq_some_iff.mp h
        exact ⟨out, kv', _, _, _, _, ho, of_guard hg1,
          (by simpa only [Bool.not_eq_true'] using of_guard hg2), (fun _ _ _ hN => by cases hN), hm,
          (Option.some.inj h).symm, .inl rfl, .inl rfl, .inl rfl, .inl rfl⟩
      · simp only [Option.bind_eq_bind] at h
        obtain ⟨out, ho, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u1, hg1, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u2, hg2, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨kv', hm, h⟩ := Option.bind_eq_some_iff.mp h
        exact ⟨out, kv', _, _, _, _, ho, of_guard hg1,
          (by simpa only [Bool.not_eq_true'] using of_guard hg2), (fun _ _ _ hN => by cases hN), hm,
          (Option.some.inj h).symm, .inl rfl, .inl rfl, .inl rfl, .inr ⟨x, y, t, rfl, hkv, rfl⟩⟩
    all_goals
      simp only [Option.bind_eq_bind] at h
      obtain ⟨out, ho, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨u1, hg1, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨u2, hg2, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨kv', hm, h⟩ := Option.bind_eq_some_iff.mp h
      exact ⟨out, kv', _, _, _, _, ho, of_guard hg1,
        (by simpa only [Bool.not_eq_true'] using of_guard hg2), fun _ _ _ hN => (by cases hN), hm,
        (Option.some.inj h).symm, .inl rfl, .inl rfl, .inl rfl, .inl rfl⟩
  case exec a =>
    simp only [Option.bind_eq_bind] at h
    obtain ⟨out, ho, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨u1, hg1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨u2, hg2, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨kv', hm, h⟩ := Option.bind_eq_some_iff.mp h
    exact ⟨out, kv', _, _, _, _, ho, of_guard hg1,
      (by simpa only [Bool.not_eq_true'] using of_guard hg2), fun _ _ _ hN => (by cases hN), hm,
      (Option.some.inj h).symm, .inl rfl, .inl rfl, .inl rfl, .inl rfl⟩

theorem forall₂_swap {ρ : Nat → B256} {r s : Nat} (hs : ρ s = ρ r) :
    ∀ {a b : List Nat} {S : List B256}, List.Forall₂ (fun x w => ρ x = w) a S →
      List.Forall₂ (fun x y => x = y ∨ (x = r ∧ y = s)) a b →
      List.Forall₂ (fun x w => ρ x = w) b S
  | [], [], [], _, _ => .nil
  | _ :: _, _ :: _, _ :: _, .cons h0 hr, .cons e hab => by
    refine .cons ?_ (forall₂_swap hs hr hab)
    rcases e with rfl | ⟨rfl, rfl⟩
    · exact h0
    · rw [hs]; exact h0

/-! ## One step -/

/-- **One accepted non-jump step is sound.**  If the abstract state `σ` holds of the machine
state `d` (frame words `S` above `rest`) and `wstep R n σ` accepts with `σ'`, then after the
step `d → d'` the state `σ'` holds of `d'` above the same `rest`; an `SSTORE` meets a site of the
current function's summary `R` (`Site.Obs`, read in `ε` before the step: the frozen `WsObs`
body); and a keeping summary's step writes no storage. -/
theorem wstep_sound {R : WRet} {n : Ninst} {σ σ' : WSt} {ε : Env} {sevm : Sevm}
    {ν : Nat → B256} {S rest : List B256} {d d' : Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (hε : ε.Frame sevm)
    (h : σ.Holds ε sevm ν S d) (hS : d.stack = S ++ rest) (hlen : σ.kv.length ≤ 1024)
    (hw : wstep R n σ = some σ') (run : Ninst.Run sevm d n d') :
    σ'.Sat ε sevm d' rest ∧
      (n = .reg .sstore → ∀ x v rs, d.stack = x :: v :: rs →
        ∃ s ∈ R.sites, s.Obs ε sevm d x v) ∧
      (R.keeps = true → n.writesStor = false) := by
  have hfr : ∀ s, s < σ.fresh → s ≠ σ.fresh := fun s hs he => Nat.lt_irrefl _ (he ▸ hs)
  have hagree : ∀ {w : B256} s, s < σ.fresh → Function.update ν σ.fresh w s = ν s :=
    fun s hs => Function.update_of_ne (hfr s hs) _ _
  by_cases hpush : ∃ bs fits, n = .push bs fits
  · obtain ⟨bs, fits, rfl⟩ := hpush
    simp only [wstep, Option.some.injEq] at hw
    subst hw
    have hA := (h.agree (ν' := Function.update ν σ.fresh (Bytes.toB256 bs)) hagree).of_keep
      (ninstMemKeeps_run rfl run) (by rw [Ninst.Run.getStor_push run])
    refine ⟨⟨Function.update ν σ.fresh (Bytes.toB256 bs), Bytes.toB256 bs :: S,
      by rw [push_run_stack run, hS]; rfl, WSt.Holds.prune ?_⟩,
      fun he => (by cases he), fun _ => rfl⟩
    refine ⟨.cons (Function.update_self _ _ _) hA.kv, hA.args, ?_, ?_, hA.mem, hA.cur, hA.ub,
      hA.eqs, hA.guards⟩
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · show _ ≤ (Function.update ν _ _ _).toNat ∧ (Function.update ν _ _ _).toNat ≤ _
        rw [Function.update_self]
        exact ⟨Nat.le_refl _, Nat.le_refl _⟩
      · exact hA.facts f hf
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · intro _
        exact Function.update_self _ _ _
      · exact hA.prov p hp
  have hn : ∀ bs fits, n ≠ .push bs fits := fun bs fits he => hpush ⟨bs, fits, he⟩
  obtain ⟨out, kv', sl, cl, ul, el, ho, hc, hkeep, hcov, hm, rfl, hsl, hcl, hul, hel⟩ :=
    wstep_nonpush hn hw
  have hst : d.stack = σ.kv.map ν ++ rest := by rw [hS, forall₂_eq_map h.kv]
  have hr : σ.fresh ∉ σ.kv := fun hm => Nat.lt_irrefl _ (WSt.lt_fresh (by
    simp only [WSt.syms, List.mem_append]; exact .inl (.inl (.inl (.inl (.inl (.inl (.inl hm))))))))
  obtain ⟨kv'', hm'', hswap⟩ := mapM_swap (r := σ.fresh) hm
  obtain ⟨S', w, hst', hf⟩ := transfer_val hfork ho hlen hc hm'' hr h.kv hS run
  -- the fresh result is the top word whenever the transfer pushes it
  have htop : ∀ q, n = .reg q → pushesTop q = true → ∃ rs, d'.stack = w :: rs := by
    intro q hq hpq
    subst hq
    obtain ⟨o, rfl⟩ := pushesTop_head hpq ho
    exact fresh_top hm'' hf hst'
  have hA : σ.Holds ε sevm (Function.update ν σ.fresh w) S d := h.agree hagree
  have hkeepS : n.writesStor = false →
      Devm.getStor d' sevm.currentTarget = Devm.getStor d sevm.currentTarget := fun hws => by
    rw [getStor_of_writesStor hfork ho hws run]
  have hcc : n ≠ .exec .callcode := fun he => by subst he; simp only [ninstTransfer, reduceCtorEq] at ho
  refine ⟨⟨Function.update ν σ.fresh w, S', hst', WSt.Holds.prune ?_⟩, ?_, ?_⟩
  rotate_left
  · intro hss x v rs hs
    subst hss
    rcases list_shape σ.kv with hkv | ⟨k, hkv⟩ | ⟨k, v', t, hkv⟩
    · rw [hkv] at ho; cases ho
    · rw [hkv] at ho; cases ho
    · exact Site.Obs.of_any (hcov k v' t rfl hkv) (siteOf_obs h hkv hS hs)
  · intro hk
    rw [hk, Bool.true_and] at hkeep
    exact hkeep
  -- the state after the step
  clear hw hpush hn hcov hkeep
  have hsv : ∀ s, sloadName σ n = some s → ν s = w := by
    intro s hs
    obtain ⟨rfl, k, t, hkv, hk, hmem⟩ := sloadName_some hs
    obtain ⟨rs, hrs⟩ := htop _ rfl rfl
    have hsl : d.stack = ν k :: (t.map ν ++ rest) := by rw [hst, hkv]; rfl
    rw [run_sload_top run hsl, List.cons.injEq] at hrs
    rw [← hrs.1, h.provOf k hk, h.cur _ hmem]
  have hfresh : ∀ s, s ∈ σ.syms → Function.update ν σ.fresh w s = ν s :=
    fun s hs => hagree s (WSt.lt_fresh hs)
  have hkvs : ∀ s ∈ σ.kv, s ∈ σ.syms := fun s hs => by
    simp only [WSt.syms, List.mem_append]
    exact .inl (.inl (.inl (.inl (.inl (.inl (.inl hs))))))
  refine ⟨?_, hA.args, ?_, ?_, ?_, ?_, ?_, ?_, h.guards⟩
  · -- frame words
    refine forall₂_swap ?_ hf hswap
    cases hs : sloadName σ n with
    | none => rfl
    | some s =>
      rw [Function.update_self, Option.getD_some]
      obtain ⟨-, k, t, -, -, hmem⟩ := sloadName_some hs
      have hsy : s ∈ σ.syms := by
        simp only [WSt.syms, List.mem_append, List.mem_map]
        exact .inl (.inl (.inr ⟨_, hmem, rfl⟩))
      rw [hfresh s hsy, hsv s hs]
  · -- facts
    refine FreePtr.AllHold.append (FreePtr.AllHold.append ?_ ?_) hA.facts
    · rcases hsl with rfl | ⟨x, y, t, rfl, hkv, he, rfl⟩
      · intro f hf; cases hf
      · intro f hf
        rw [List.mem_singleton] at hf
        subst hf
        have hs2 : d.stack = ν x :: ν y :: (t.map ν ++ rest) := by rw [hst, hkv]; rfl
        obtain ⟨rs, hrs⟩ := htop _ rfl rfl
        rw [run_sub_top run hs2, List.cons.injEq] at hrs
        have hyx : (ν y).toNat ≤ (ν x).toNat := FreePtr.entails_sound h.facts he
        show (Function.update ν σ.fresh w σ.fresh).toNat ≤ (Function.update ν σ.fresh w x).toNat
        rw [Function.update_self, hfresh x (hkvs x (by rw [hkv]; exact List.mem_cons_self)),
          ← hrs.1, B256.toNat_sub_of_le hyx]
        exact Nat.sub_le _ _
    · by_cases hne : FreePtr.opFacts σ.facts n σ.kv σ.fresh = []
      · rw [hne]; intro f hf; cases hf
      · obtain ⟨q, rfl, hq⟩ := opFacts_pushesTop hne
        rcases hq with hq | rfl
        · obtain ⟨rs, hrs⟩ := htop q rfl hq
          exact FreePtr.opFacts_sound h.facts hr h.kv hS run (by rw [hrs]; rfl)
            (fun he => by cases he; exact absurd hq (by decide))
        · simp only [ninstTransfer, liftRegularTransfer, regularTransfer, reduceCtorEq] at ho
  · -- provenance
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · split at hp
      · rename_i hcond
        rw [List.mem_singleton] at hp
        subst hp
        obtain ⟨hk, -⟩ := Bool.and_eq_true_iff.mp hcond
        obtain ⟨q, rfl, hq⟩ := provEff_pushesTop hk
        obtain ⟨rs, hrs⟩ := htop q rfl hq
        show (provEff σ _).Den ε (Function.update ν σ.fresh w σ.fresh)
        rw [Function.update_self]
        exact provEff_sound hε h hS run hrs
      · cases hp
    · exact hA.prov p hp
  · -- memory
    exact memEff_sound hfork hA hS run hcc
  · -- current slot values
    intro p hp
    rcases List.mem_append.mp hp with hp1 | hp2
    · rcases hcl with rfl | ⟨k, t, rfl, hkv, hk, -, rfl⟩
      · cases hp1
      · rw [List.mem_singleton] at hp1
        subst hp1
        obtain ⟨rs, hrs⟩ := htop _ rfl rfl
        have hs1 : d.stack = ν k :: (t.map ν ++ rest) := by rw [hst, hkv]; rfl
        rw [run_sload_top run hs1, List.cons.injEq] at hrs
        show (Devm.getStor d' _).get _ = Function.update ν σ.fresh w σ.fresh
        rw [hkeepS rfl, Function.update_self, ← hrs.1, h.provOf k hk]
        rfl
    · split at hp2
      · rename_i hws
        show (Devm.getStor d' _).get _ = _
        rw [hkeepS (by simpa only [Bool.not_eq_true'] using hws)]
        exact hA.cur p hp2
      · cases hp2
  · -- slot upper bounds
    intro p hp
    rcases List.mem_append.mp hp with hp1 | hp2
    · rcases hul with rfl | ⟨x, y, t, rfl, hkv, he, rfl⟩
      · cases hp1
      · obtain ⟨q', hq', hpq⟩ := List.mem_filterMap.mp hp1
        split at hpq
        · rename_i hx
          cases hpq
          have hs2 : d.stack = ν x :: ν y :: (t.map ν ++ rest) := by rw [hst, hkv]; rfl
          obtain ⟨rs, hrs⟩ := htop _ rfl rfl
          rw [run_sub_top run hs2, List.cons.injEq] at hrs
          have hyx : (ν y).toNat ≤ (ν x).toNat := FreePtr.entails_sound h.facts he
          have hxs : (ν x).toNat ≤ (d.getStorVal sevm.currentTarget (q'.2.eval ε)).toNat := by
            rw [← hx]
            rcases List.mem_append.mp hq' with hc | hu
            · rw [← h.cur q' hc]
            · exact h.ub q' hu
          show (Function.update ν σ.fresh w σ.fresh).toNat ≤ ((Devm.getStor d' _).get _).toNat
          rw [hkeepS rfl, Function.update_self, ← hrs.1, B256.toNat_sub_of_le hyx]
          exact le_trans (Nat.sub_le _ _) hxs
        · cases hpq
    · split at hp2
      · rename_i hws
        show _ ≤ ((Devm.getStor d' _).get _).toNat
        rw [hkeepS (by simpa only [Bool.not_eq_true'] using hws)]
        exact hA.ub p hp2
      · cases hp2
  · -- equality results
    intro e he
    rcases List.mem_append.mp he with he1 | he2
    · rcases hel with rfl | ⟨x, y, t, rfl, hkv, rfl⟩
      · cases he1
      · rw [List.mem_singleton] at he1
        subst he1
        have hs2 : d.stack = ν x :: ν y :: (t.map ν ++ rest) := by rw [hst, hkv]; rfl
        obtain ⟨rs, hrs⟩ := htop _ rfl rfl
        rw [run_eq_top run hs2, List.cons.injEq] at hrs
        exact ⟨ν x, ν y, by rw [Function.update_self, ← hrs.1], h.provOf x, h.provOf y⟩
    · exact hA.eqs e he2


end Blanc.Lift.WriteSite
