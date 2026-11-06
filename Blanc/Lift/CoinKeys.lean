import Blanc.Lift.BalanceLocality
import Blanc.Lift.ExactWalk
import Blanc.Lift.Sound
import Blanc.Lift.RunPWalk

/-!
# The keys a coin's frames name, for any certified code

The helpers every coin's locality proof needs over its hash premise, parametric in the site list, the bases and the
selector term:

* `CoinKeysFreshWith`: `CoinKeysFresh` with further listed keys (the slots a code's sites cannot name);
* `site_key_mem`, `map_key_mem`, `row_key_mem`: a guarded site of the frame's selector names its key;
* `FreshKeys`-level facts over any key list: `map_inj`, `map_ne_raw`, `map_ne_row`;
* `caller_eval`, `cd_eval`, `addr_eval`: reading the terms in a frame's environment;
* `CoinKeysFreshWith.restrict`: down to fewer sites, or to `CoinKeysFresh`;
* `run_of_frame`: a committed frame's run through its certificate.

Contract-neutral.
-/

namespace Blanc.Lift

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift.WriteSite

/-- The keys `CoinKeysFresh` speaks of, and `extra`. -/
noncomputable abbrev coinKeysWith (extra : List CoinKey) (sites : List Site) (balBase allowBase : B256) (h : Adr)
    (frames : List Exec.Frame) : List CoinKey :=
  extra ++ (heldKeys balBase allowBase h frames ++ frames.flatMap fun F => frameSiteKeys sites (Env.root F.sevm))

/-- **Hash freshness at a coin, over further listed keys.** -/
def CoinKeysFreshWith (extra : List CoinKey) (sites : List Site) (balBase allowBase : B256) (h : Adr)
    (frames : List Exec.Frame) : Prop :=
  SlotFootprint.FreshKeys CoinKey.slot [] (fun _ => False) (coinKeysWith extra sites balBase allowBase h frames)

/-- A selector term reads the frame's selector. -/
def SelEval (selT : Term) : Prop := ∀ e : Sevm, selT.eval (Env.root e) = Blanc.Sevm.selector e

theorem caller_eval (e : Sevm) : (Term.caller.eval (Env.root e)).toAdr.toB256 = e.caller.toB256 := by
  change (e.caller.toB256).toAdr.toB256 = _
  rw [toAdr_toB256]

theorem cd_eval (e : Sevm) (i : B256) : (Term.cd (.const i)).eval (Env.root e) = Sevm.dataWord e i := rfl

variable {sites : List Site} {balBase allowBase : B256} {h : Adr} {frames : List Exec.Frame} {extra : List CoinKey}

/-- A site of the frame's selector names its key. -/
theorem site_key_mem {selT : Term} (ev : SelEval selT) {F : Exec.Frame} (hF : F ∈ frames) {slot : Term} {sel : B256}
    {ni : Bool} (hs : (⟨slot, [(selT, sel)], ni⟩ : Site) ∈ sites) (hk : slot.known = true)
    (hsel : Blanc.Sevm.selector F.sevm = sel) :
    termKey (Env.root F.sevm) slot ∈ coinKeysWith extra sites balBase allowBase h frames :=
  List.mem_append_right _ (CoinKeysFresh.site_mem (sites := sites) hF hs (by
    intro g hg known
    simp only [List.mem_singleton] at hg
    subst hg
    exact hsel.symm.trans (ev _).symm) hk)

/-- A mapping site of the frame's selector names its key. -/
theorem map_key_mem {selT : Term} (ev : SelEval selT) {F : Exec.Frame} (hF : F ∈ frames) {key : Term} {b sel : B256}
    {ni : Bool} (hs : (⟨.kecc (.op2 .and key addrMaskT) (.const b), [(selT, sel)], ni⟩ : Site) ∈ sites)
    (hk : key.known = true) (hsel : Blanc.Sevm.selector F.sevm = sel) :
    CoinKey.map b (key.eval (Env.root F.sevm)).toAdr.toB256 ∈
      coinKeysWith extra sites balBase allowBase h frames := by
  have := site_key_mem (extra := extra) (balBase := balBase) (allowBase := allowBase) (h := h) ev hF hs
    (by simp only [Term.known, hk, Bool.and_self, addrMaskT]) hsel
  simpa only [termKey, addrMaskT_eval] using this

/-- A two-level site of the frame's selector names its key. -/
theorem row_key_mem {selT : Term} (ev : SelEval selT) {F : Exec.Frame} (hF : F ∈ frames) {o k : Term} {b sel : B256}
    {ni : Bool}
    (hs : (⟨.kecc (.op2 .and k addrMaskT) (.kecc (.op2 .and o addrMaskT) (.const b)), [(selT, sel)], ni⟩ : Site) ∈ sites)
    (ho : o.known = true) (hk : k.known = true) (hsel : Blanc.Sevm.selector F.sevm = sel) :
    CoinKey.row b (o.eval (Env.root F.sevm)).toAdr.toB256 (k.eval (Env.root F.sevm)).toAdr.toB256 ∈
      coinKeysWith extra sites balBase allowBase h frames := by
  have := site_key_mem (extra := extra) (balBase := balBase) (allowBase := allowBase) (h := h) ev hF hs
    (by simp only [Term.known, ho, hk, Bool.and_self, addrMaskT]) hsel
  simpa only [termKey, addrMaskT_eval] using this

theorem held_mem : CoinKey.map balBase h.toB256 ∈ coinKeysWith extra sites balBase allowBase h frames :=
  List.mem_append_right _ (CoinKeysFresh.held_mem (sites := sites) (frames := frames))

theorem frame_row_mem {F : Exec.Frame} (hF : F ∈ frames) :
    CoinKey.row allowBase h.toB256 F.sevm.caller.toB256 ∈ coinKeysWith extra sites balBase allowBase h frames :=
  List.mem_append_right _ (CoinKeysFresh.row_mem (sites := sites) hF)

section Fresh

variable {L : List CoinKey}

/-- Two listed entries of one mapping on one slot are one entry. -/
theorem map_inj (keys : SlotFootprint.FreshKeys CoinKey.slot [] (fun _ => False) L) {b : B256} {a c : Adr}
    (ma : CoinKey.map b a.toB256 ∈ L) (mc : CoinKey.map b c.toB256 ∈ L)
    (eq : mapSlot a.toB256 b = mapSlot c.toB256 b) : a = c := by
  have := keys.2 _ ma _ mc eq
  injection this with _ e
  exact Adr.toB256_inj e

/-- A listed entry is on no listed word's slot. -/
theorem map_ne_raw (keys : SlotFootprint.FreshKeys CoinKey.slot [] (fun _ => False) L) {b x : B256} {a : B256}
    (ma : CoinKey.map b a ∈ L) (mx : CoinKey.raw x ∈ L) : mapSlot a b ≠ x := fun eq => by
  have := keys.2 _ ma _ mx eq
  cases this

/-- A listed entry is on no listed row's slot. -/
theorem map_ne_row (keys : SlotFootprint.FreshKeys CoinKey.slot [] (fun _ => False) L) {b b' o k a : B256}
    (ma : CoinKey.map b a ∈ L) (mr : CoinKey.row b' o k ∈ L) : mapSlot a b ≠ rowSlot b' o k := fun eq => by
  have := keys.2 _ ma _ mr eq
  cases this

/-- A listed word is on no listed row's slot. -/
theorem raw_ne_row (keys : SlotFootprint.FreshKeys CoinKey.slot [] (fun _ => False) L) {b' o k x : B256}
    (mx : CoinKey.raw x ∈ L) (mr : CoinKey.row b' o k ∈ L) : x ≠ rowSlot b' o k := fun eq => by
  have := keys.2 _ mx _ mr eq
  cases this

end Fresh

/-- Fresh over a list, fresh over any list inside it. -/
theorem freshKeys_mono {L L' : List CoinKey} (sub : ∀ k ∈ L', k ∈ L)
    (keys : SlotFootprint.FreshKeys CoinKey.slot [] (fun _ => False) L) :
    SlotFootprint.FreshKeys CoinKey.slot [] (fun _ => False) L' :=
  ⟨fun k hk => keys.1 k (sub k hk), fun a ha b hb => keys.2 a (sub a ha) b (sub b hb)⟩

/-- Down to `CoinKeysFresh` over fewer sites. -/
theorem CoinKeysFreshWith.restrict {sites' : List Site} (keys : CoinKeysFreshWith extra sites balBase allowBase h frames)
    (sub : ∀ s ∈ sites', s ∈ sites) : CoinKeysFresh sites' balBase allowBase h frames := by
  refine freshKeys_mono ?_ keys
  intro k hk
  refine List.mem_append_right _ ?_
  rcases List.mem_append.mp hk with held | site
  · exact List.mem_append_left _ held
  · refine List.mem_append_right _ ?_
    obtain ⟨F, hF, mem⟩ := List.mem_flatMap.mp site
    refine List.mem_flatMap.mpr ⟨F, hF, ?_⟩
    unfold frameSiteKeys at mem ⊢
    obtain ⟨s, hs, e⟩ := List.mem_filterMap.mp mem
    exact List.mem_filterMap.mpr ⟨s, sub s hs, e⟩

/-- A known site of the frame's selector and another shape misses the holder's entry. -/
theorem slot_apart {selT : Term} (ev : SelEval selT) (keys : CoinKeysFresh sites balBase allowBase h frames)
    {F : Exec.Frame} (hF : F ∈ frames) {slot : Term} {sel : B256} {ni : Bool}
    (hs : (⟨slot, [(selT, sel)], ni⟩ : Site) ∈ sites) (hk : slot.known = true)
    (none : mappingKey? balBase slot = none) (hsel : Blanc.Sevm.selector F.sevm = sel) :
    slot.eval (Env.root F.sevm) ≠ mapSlot h.toB256 balBase :=
  slot_ne_of_keys keys hF hs (by
    intro g hg known
    simp only [List.mem_singleton] at hg
    subst hg
    exact hsel.symm.trans (ev _).symm) hk none

/-- The caller's listed entry on the holder's slot is the holder's. -/
theorem bal_caller_eq {selT : Term} (ev : SelEval selT) (keys : CoinKeysFresh sites balBase allowBase h frames)
    {F : Exec.Frame} (hF : F ∈ frames) {sel : B256} {ni : Bool}
    (hs : (⟨.kecc (.op2 .and .caller addrMaskT) (.const balBase), [(selT, sel)], ni⟩ : Site) ∈ sites)
    (hsel : Blanc.Sevm.selector F.sevm = sel) :
    mapSlot F.sevm.caller.toB256 balBase = mapSlot h.toB256 balBase → F.sevm.caller = h := by
  have mem := map_key_mem (extra := []) (balBase := balBase) (allowBase := allowBase) (h := h) ev hF (key := .caller) hs rfl hsel
  rw [caller_eval] at mem
  exact map_inj keys mem (held_mem (extra := []))

/-- A calldata address's listed entry on the holder's slot is the holder's. -/
theorem bal_cd_eq {selT : Term} (ev : SelEval selT) (keys : CoinKeysFresh sites balBase allowBase h frames)
    {F : Exec.Frame} (hF : F ∈ frames) {i sel : B256} {ni : Bool}
    (hs : (⟨.kecc (.op2 .and (.cd (.const i)) addrMaskT) (.const balBase), [(selT, sel)], ni⟩ : Site) ∈ sites)
    (hsel : Blanc.Sevm.selector F.sevm = sel) :
    mapSlot (Sevm.dataWord F.sevm i).toAdr.toB256 balBase = mapSlot h.toB256 balBase →
      (Sevm.dataWord F.sevm i).toAdr = h := by
  have mem := map_key_mem (extra := []) (balBase := balBase) (allowBase := allowBase) (h := h) ev hF (key := .cd (.const i)) hs rfl hsel
  rw [cd_eval] at mem
  exact map_inj keys mem (held_mem (extra := []))

/-- **A committed frame's run through its certificate**, on a lane without state gas. -/
theorem run_of_frame {code : ByteArray} {c : Cert} {f0 : SFunc} (checked : Cert.check code c = true)
    (root : c.prog[0]? = some f0) {F : Exec.Frame} (pc : F.pc = 0) (hcode : F.sevm.code = code)
    (hsg : F.sevm.benvStat.rules.stateGas = none) :
    SFunc.Run c.prog F.sevm (St F.pre F.pre.stack F.pre.memory F.pre.gasLeft) f0 (.halted F.post) := by
  obtain ⟨fpc, sevm, pre, out, run, committed⟩ := F
  dsimp only at pc hcode hsg
  subst pc
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    obtain ⟨f, hf0, hrun⟩ := lift_sound_noStateGas checked hcode hsg run
    obtain rfl : f = f0 := Option.some.inj (hf0.symm.trans root)
    rw [St.self' pre] at hrun
    exact hrun

end Blanc.Lift
