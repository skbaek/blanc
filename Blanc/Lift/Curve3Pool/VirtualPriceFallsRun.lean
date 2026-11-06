import Blanc.Lift.NodeWalkPrecomp
import Blanc.Lift.NodeWalkOrig
import Blanc.Lift.KernelNat
import Blanc.Lift.HistAccessWalk

/-!
# Whole-call kernel runs between literal boundaries

`Blanc/Lift/NodeWalk.lean` gives a pc-level walk whose every step is the real `Evm.step`, and
`Blanc/Lift/WitnessBoundary.lean` the method of deciding a long run as chunks between printed
literal boundaries, each chunk its own declaration so the kernel's caches do not outlive it.  This
module applies that method to a whole call with its child frames, over the node walk:

* `xStep`: a step under flat access pricing (the rules up to Muir Glacier): `PC` by Jaune's own step
  (Vyper 0.2.4's internal calls read it), `SLOAD`, `SSTORE`, `EXTCODESIZE` over the shadows, the rest
  as the node walk runs them; `prepX` the call-family preparations under the same rules;
* `XB`, `XB.cfg`, `xObs`: a boundary (pc, machine, refund counter, output, return data, the shadows)
  over a free world and free bookkeeping, and a configuration decided against it; `cfg_of_xObs`
  says a configuration so decided is the boundary's at its own world and bookkeeping;
* `RunsB s A x z`: from every machine at boundary `x` the frame `s` runs to a successful halt at
  boundary `z`, under every original state with the same storage as `s`'s (evaluated under a cheap
  closed original state, used under the real one, `Blanc/Lift/NodeWalkOrig.lean`);
* `RunsB.walk`, `.halt`, `.call`, `.done`: its composition from chunk facts, whose hypotheses are
  closed kernel decisions and whose proofs evaluate nothing;
* `exec_of_runsB`: a top-level message's `exec`.

Nothing here is contract-specific.  The account shadow `A` is fixed along a run: no frame in scope
moves value or creates an account.
-/

namespace Blanc.Lift.Curve3Pool.VirtualPriceFalls

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.KernelNat

/-! ## The step -/

/-- The hash policy of `pstepH`, unused here: this development claims nothing of a digest. -/
abbrev xPol : HashPol := .avoid 0

/-- `SLOAD` under flat access, its value from the storage shadow. -/
def xSload (s : Sevm) (c : PCfg) : PRes :=
  match c.devm.stack, s.benvStat.rules.access with
  | k :: st, .flat g =>
    if s.benvStat.rules.stateGas.isNone ∧ st.length < 1024 ∧ g.sload ≤ c.devm.gasLeft then
      .cont { c with
        pc := c.pc + 1
        devm := c.devm.setMach ⟨lookupS c.stor s.currentTarget k :: st, c.devm.memory,
          c.devm.gasLeft - g.sload, c.devm.stateGas⟩ }
    else .stuck
  | _, _ => .stuck

/-- `SSTORE` under flat access, its current value from the storage shadow, its original value through
`origReadK`. -/
def xSstore (s : Sevm) (c : PCfg) : PRes :=
  match c.devm.stack, s.benvStat.rules.access with
  | k :: v :: st, .flat _ =>
    let ct := s.currentTarget
    let orig := origReadK c.devm s ct k
    let cur := lookupS c.stor ct k
    let cost := sstoreRegimeGasCost s.benvStat.rules.sstore s.benvStat.rules.access 0 v orig cur
    let rc := sstoreRefundH s.benvStat.rules v orig cur c.devm.refundCounter
    if s.benvStat.rules.stateGas.isNone ∧ s.isStatic = false ∧ cost ≤ c.devm.gasLeft ∧
        (s.benvStat.rules.sstore.stipendSentry = true → gCallStipend < c.devm.gasLeft) then
      .cont ⟨c.pc + 1,
        (Devm.setStorVal (c.devm.withRefundCounter rc) ct k v).setMach
          ⟨st, c.devm.memory, c.devm.gasLeft - cost, c.devm.stateGas⟩,
        c.keys, c.adrs, ((ct, k), v) :: c.stor, c.acs⟩
    else .stuck
  | _, _ => .stuck

/-- `EXTCODESIZE` under flat access, the code from the account shadow. -/
def xExtcodesize (s : Sevm) (c : PCfg) : PRes :=
  match c.devm.stack, s.benvStat.rules.access with
  | x :: st, .flat g =>
    let cost := g.extCode + s.benvStat.rules.gas.codeReadSurcharge
    if s.benvStat.rules.bal.isNone ∧ st.length < 1024 ∧ cost ≤ c.devm.gasLeft then
      .cont { c with
        pc := c.pc + 1
        devm := c.devm.setMach ⟨(lookupA c.acs x.toAdr).code.size.toB256 :: st, c.devm.memory,
          c.devm.gasLeft - cost, c.devm.stateGas⟩ }
    else .stuck
  | _, _ => .stuck

/-- One walk step under flat access: `PC` by Jaune's own step, the three world-reading instructions
over the shadows, the rest as the node walk runs them. -/
def xStep {code : ByteArray} {d : Nat} (T : CodeTries code d) (s : Sevm) (c : PCfg) : PRes :=
  match decodeT d T.bytes c.pc with
  | some (.next (.reg .pc)) =>
    match Ninst.step ⟨c.pc, s, c.devm⟩ (.reg .pc) with
    | .cont pc' d' => .cont { c with pc := pc', devm := d' }
    | _ => .stuck
  | some (.next (.reg .sload)) => xSload s c
  | some (.next (.reg .sstore)) => xSstore s c
  | some (.next (.reg .extcodesize)) => xExtcodesize s c
  | _ => pstepH xPol T s c

/-- At most `n` steps. -/
def xWalkN {code : ByteArray} {d : Nat} (T : CodeTries code d) (s : Sevm) : Nat → PCfg → PRes
  | 0, c => .cont c
  | n + 1, c =>
    match xStep T s c with
    | .cont c' => xWalkN T s n c'
    | r => r

/-- `PC` keeps the accessed sets and the world. -/
theorem pc_step_accKeep {pc pc' : Nat} {s : Sevm} {d d' : Devm}
    (h : Ninst.step ⟨pc, s, d⟩ (.reg .pc) = .cont pc' d') : AccKeep d d' := by
  simp only [Ninst.step, Rinst.run, Rinst.runCore] at h
  cases hp : pushItem (Nat.toB256 pc) gBase d with
  | error e => rw [hp] at h; cases h
  | ok d1 =>
    rw [hp] at h
    cases h
    exact accKeep_pushItem hp

theorem devm_setMach_self {b : Devm} {S : List B256} (h : b.stack = S) :
    b.setMach ⟨S, b.memory, b.gasLeft, b.stateGas⟩ = b := by
  subst h; rfl

theorem xSload_cont {s : Sevm} {c c' : PCfg} (hag : PAgree c) (h : xSload s c = .cont c') :
    Ninst.step ⟨c.pc, s, c.devm⟩ (.reg .sload) = .cont c'.pc c'.devm ∧ PAgree c' := by
  unfold xSload at h
  split at h
  · rename_i k st g hs hacc
    split at h
    · rename_i hc
      obtain ⟨hsg, hroom, hgas⟩ := hc
      cases h
      have hval : c.devm.getStorVal s.currentTarget k = lookupS c.stor s.currentTarget k :=
        hag.2.2.1 _ _
      have hrc := Ninst.runCompiled_sload_selectedH (sevm := s) (base := c.devm) (key := k)
        (stack := st) (memory := c.devm.memory) (G := c.devm.gasLeft - g.sload)
        (Option.isNone_iff_eq_none.mp hsg) hval hroom
      have hcost : sloadCostH s c.devm k = g.sload := by
        unfold sloadCostH; rw [hacc]
      have hafter : afterSloadH s c.devm k = c.devm := by
        unfold afterSloadH; rw [hacc]
      rw [hcost, Nat.sub_add_cancel hgas, hafter, devm_setMach_self hs] at hrc
      refine ⟨ninst_step_of_runCompiled (fun x hx => by cases hx) hrc c.pc, ?_⟩
      exact agree_accKeep hag ⟨rfl, rfl, rfl⟩
    · cases h
  · cases h

theorem xExtcodesize_cont {s : Sevm} {c c' : PCfg} (hag : PAgree c)
    (h : xExtcodesize s c = .cont c') :
    Ninst.step ⟨c.pc, s, c.devm⟩ (.reg .extcodesize) = .cont c'.pc c'.devm ∧ PAgree c' := by
  unfold xExtcodesize at h
  split at h
  · rename_i x st g hs hacc
    dsimp only at h
    split at h
    · rename_i hc
      obtain ⟨hbal, hroom, hgas⟩ := hc
      cases h
      have hcode : c.devm.getCode x.toAdr = (lookupA c.acs x.toAdr).code := by
        have e := congrArg Acct.code (hag.2.2.2 x.toAdr)
        exact e
      have hrc := extcodesizeH_runCompiled (sevm := s) (b := c.devm) (x := x) (S := st)
        (M := c.devm.memory) (G := c.devm.gasLeft - (g.extCode + s.benvStat.rules.gas.codeReadSurcharge))
        (Option.isNone_iff_eq_none.mp hbal) hroom
      have hcost : extcodesizeCostH s c.devm x.toAdr =
          g.extCode + s.benvStat.rules.gas.codeReadSurcharge := by
        unfold extcodesizeCostH; rw [hacc]
      have hafter : accountAccessH s c.devm x.toAdr = c.devm := by
        unfold accountAccessH; rw [hacc]
      rw [hcost, Nat.sub_add_cancel hgas, hafter, hcode] at hrc
      unfold St at hrc
      rw [devm_setMach_self hs] at hrc
      refine ⟨ninst_step_of_runCompiled (fun y hy => by cases hy) hrc c.pc, ?_⟩
      exact agree_accKeep hag ⟨rfl, rfl, rfl⟩
    · cases h
  · cases h

theorem xSstore_cont {s : Sevm} {c c' : PCfg} (hag : PAgree c) (h : xSstore s c = .cont c') :
    Ninst.step ⟨c.pc, s, c.devm⟩ (.reg .sstore) = .cont c'.pc c'.devm ∧ PAgree c' := by
  unfold xSstore at h
  split at h
  · rename_i k v st a hs hacc
    dsimp only at h
    rw [origReadK_eq] at h
    split at h
    · rename_i hc
      obtain ⟨hsg, hstatic, hgas, hsentry⟩ := hc
      cases h
      have hcur : c.devm.getStorVal s.currentTarget k = lookupS c.stor s.currentTarget k :=
        hag.2.2.1 _ _
      have hcost : sstoreCostH s c.devm k v = sstoreRegimeGasCost s.benvStat.rules.sstore
          s.benvStat.rules.access 0 v (c.devm.getOrigStorVal s s.currentTarget k)
          (lookupS c.stor s.currentTarget k) := by
        unfold sstoreCostH storageAccessCostH
        rw [hcur, hacc]
      have hafter : afterSstoreH s c.devm k v =
          Devm.setStorVal (c.devm.withRefundCounter (sstoreRefundH s.benvStat.rules v
            (c.devm.getOrigStorVal s s.currentTarget k) (lookupS c.stor s.currentTarget k)
            c.devm.refundCounter)) s.currentTarget k v := by
        unfold afterSstoreH storageAccessH
        rw [hcur, hacc]
      have hrc := Ninst.runCompiled_sstore_selectedH (sevm := s) (base := c.devm) (key := k)
        (value := v) (stack := st) (memory := c.devm.memory)
        (G := c.devm.gasLeft - sstoreCostH s c.devm k v) (Option.isNone_iff_eq_none.mp hsg)
        (fun hss => by rw [Nat.sub_add_cancel (by rw [hcost]; exact hgas)]; exact hsentry hss)
        hstatic
      rw [Nat.sub_add_cancel (by rw [hcost]; exact hgas), devm_setMach_self hs, hafter, hcost] at hrc
      refine ⟨ninst_step_of_runCompiled (fun y hy => by cases hy) hrc c.pc, ?_⟩
      exact ⟨hag.1, hag.2.1, storOf_sstore hag.2.2.1, acctAgree_setStorVal hag.2.2.2 _ _ _⟩
    · cases h
  · cases h

theorem xStep_cont {code : ByteArray} {dd : Nat} (T : CodeTries code dd) {s : Sevm}
    (hcode : s.code = code) {c c' : PCfg} (hag : PAgree c) (h : xStep T s c = .cont c') :
    Evm.step ⟨c.pc, s, c.devm⟩ = .cont c'.pc c'.devm ∧ PAgree c' := by
  unfold xStep at h
  split at h
  · rename_i hdec
    have hat : Ninst.At s.code c.pc (.reg .pc) := by rw [hcode]; exact decodeT_sound T hdec
    split at h
    · rename_i pc' d' hs
      cases h
      exact ⟨by rw [Evm.step_next hat]; exact hs, agree_accKeep hag (pc_step_accKeep hs)⟩
    · cases h
  · rename_i hdec
    have hat : Ninst.At s.code c.pc (.reg .sload) := by rw [hcode]; exact decodeT_sound T hdec
    obtain ⟨h1, h2⟩ := xSload_cont hag h
    exact ⟨by rw [Evm.step_next hat]; exact h1, h2⟩
  · rename_i hdec
    have hat : Ninst.At s.code c.pc (.reg .sstore) := by rw [hcode]; exact decodeT_sound T hdec
    obtain ⟨h1, h2⟩ := xSstore_cont hag h
    exact ⟨by rw [Evm.step_next hat]; exact h1, h2⟩
  · rename_i hdec
    have hat : Ninst.At s.code c.pc (.reg .extcodesize) := by rw [hcode]; exact decodeT_sound T hdec
    obtain ⟨h1, h2⟩ := xExtcodesize_cont hag h
    exact ⟨by rw [Evm.step_next hat]; exact h1, h2⟩
  · obtain ⟨h1, h2, -⟩ := pstepH_cont T hcode hag h
    exact ⟨h1, h2⟩

theorem xSload_not_halt {s : Sevm} {c : PCfg} {ex : Execution} : xSload s c ≠ .halt ex := by
  unfold xSload; split
  · split <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  · simp only [ne_eq, reduceCtorEq, not_false_eq_true]

theorem xSstore_not_halt {s : Sevm} {c : PCfg} {ex : Execution} : xSstore s c ≠ .halt ex := by
  unfold xSstore; split
  · dsimp only; split <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  · simp only [ne_eq, reduceCtorEq, not_false_eq_true]

theorem xExtcodesize_not_halt {s : Sevm} {c : PCfg} {ex : Execution} :
    xExtcodesize s c ≠ .halt ex := by
  unfold xExtcodesize; split
  · dsimp only; split <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  · simp only [ne_eq, reduceCtorEq, not_false_eq_true]

theorem xStep_halt {code : ByteArray} {dd : Nat} (T : CodeTries code dd) {s : Sevm}
    (hcode : s.code = code) {c : PCfg} {ex : Execution} (h : xStep T s c = .halt ex) :
    Evm.step ⟨c.pc, s, c.devm⟩ = .halt ex ∧ pstepH xPol T s c = .halt ex := by
  unfold xStep at h
  split at h
  · split at h <;> cases h
  · exact absurd h xSload_not_halt
  · exact absurd h xSstore_not_halt
  · exact absurd h xExtcodesize_not_halt
  · exact ⟨(pstepH_halt T hcode h).1, h⟩

theorem xSload_withOrig (s : Sevm) (O : State) (c : PCfg) : xSload (s.withOrig O) c = xSload s c :=
  rfl

theorem xExtcodesize_withOrig (s : Sevm) (O : State) (c : PCfg) :
    xExtcodesize (s.withOrig O) c = xExtcodesize s c := rfl

theorem xSstore_withOrig {s : Sevm} {O : State} (hO : OrigAgree O s.benvStat.origState) (c : PCfg) :
    xSstore (s.withOrig O) c = xSstore s c := by
  unfold xSstore
  have ho : ∀ k, origReadK c.devm (s.withOrig O) (s.withOrig O).currentTarget k =
      origReadK c.devm s s.currentTarget k := fun k => by
    rw [origReadK_eq, origReadK_eq]
    exact Blanc.Devm.getOrigStorVal_withOrig_of_eq _ _ _ (hO _ _)
  show (match c.devm.stack, s.benvStat.rules.access with
    | k :: v :: st, .flat _ => _
    | _, _ => _) = _
  simp only [ho]
  rfl

theorem xStep_withOrig {s : Sevm} {O : State} (hO : OrigAgree O s.benvStat.origState)
    {code : ByteArray} {dd : Nat} (T : CodeTries code dd) (c : PCfg) :
    xStep T (s.withOrig O) c = xStep T s c := by
  unfold xStep
  split
  · rw [ninst_step_reg_withOrig c.pc c.devm (r := .pc) (by decide)]
  · rfl
  · exact xSstore_withOrig hO c
  · rfl
  · exact pstepH_withOrig hO xPol T c

theorem xWalkN_withOrig {s : Sevm} {O : State} (hO : OrigAgree O s.benvStat.origState)
    {code : ByteArray} {dd : Nat} (T : CodeTries code dd) :
    ∀ n c, xWalkN T (s.withOrig O) n c = xWalkN T s n c
  | 0, _ => rfl
  | n + 1, c => by
    simp only [xWalkN, xStep_withOrig hO, xWalkN_withOrig hO T n]

theorem xWalkN_cont {code : ByteArray} {dd : Nat} (T : CodeTries code dd) {s : Sevm}
    (hcode : s.code = code) :
    ∀ (n : Nat) (c c' : PCfg), PAgree c → xWalkN T s n c = .cont c' →
      PAgree c' ∧ ∀ ex, Nonempty (Exec c'.pc s c'.devm ex) → Nonempty (Exec c.pc s c.devm ex)
  | 0, c, c', hag, h => by
    simp only [xWalkN, PRes.cont.injEq] at h
    subst h
    exact ⟨hag, fun _ d => d⟩
  | n + 1, c, c', hag, h => by
    simp only [xWalkN] at h
    cases h1 : xStep T s c with
    | stuck => rw [h1] at h; cases h
    | halt ex => rw [h1] at h; cases h
    | cont c1 =>
      rw [h1] at h
      obtain ⟨hs, hag1⟩ := xStep_cont T hcode hag h1
      obtain ⟨hag', back⟩ := xWalkN_cont T hcode n c1 c' hag1 h
      exact ⟨hag', fun ex d => (back ex d).elim fun r => ⟨Exec.cont hs r⟩⟩

/-! ## Boundaries -/

/-- `l` followed by the members of `l'` it lacks. -/
def mergeL {α : Type} [DecidableEq α] (l l' : List α) : List α :=
  l ++ l'.filter fun x => !(l.contains x)

theorem mem_mergeL {α : Type} [DecidableEq α] (l l' : List α) (x : α) :
    x ∈ mergeL l l' ↔ x ∈ l ++ l' := by
  simp only [mergeL, List.mem_append, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.contains_eq_mem, decide_eq_false_iff_not]
  by_cases h : x ∈ l <;> simp only [h, true_or, false_or, not_true_eq_false, and_false,
    not_false_eq_true, and_true]

/-- What a boundary fixes of a configuration. -/
structure XB where
  pc : Nat
  stack : List B256
  mem : Mem
  gas : Nat
  rc : Int
  out : Bytes
  rd : Bytes
  keys : List (Adr × B256)
  adrs : List Adr
  stor : StorShadow

/-- The configuration at boundary `x`, over free bookkeeping and a free world; no account created
(`SSTORE` reads that set, `origReadK`), no error, no state gas. -/
def XB.cfg (A : AcctShadow) (x : XB) (m : Meta) (w : World) : PCfg :=
  ⟨x.pc, ⟨⟨x.stack, x.mem, x.gas, .zero⟩,
    { m with refundCounter := x.rc, output := x.out, returnData := x.rd, error := none,
             createdAccounts := .emptyWithCapacity }, w⟩,
    x.keys, x.adrs, x.stor, A⟩

/-- What the boundary decision shows when it passes. -/
abbrev XObs := Bool × AcctShadow × AdrSet

/-- The passing observation. -/
abbrev xOk (A : AcctShadow) : XObs := (true, A, .emptyWithCapacity)

/-- A configuration decided against boundary `y`: machine and shadows by `decide`, so the kernel
evaluates them, numbers by `natEqW`, whose values are closed only after evaluation; the account shadow and the empty created set as terms. -/
def xObs (y : XB) (c : PCfg) : XObs :=
  (natEqW c.pc y.pc && decide (c.devm.mach.stack = y.stack) &&
    decide (c.devm.mach.memory.data.toList = y.mem.data.toList) &&
    natEqW c.devm.mach.memory.size y.mem.size && natEqW c.devm.mach.gasLeft y.gas &&
    decide (c.devm.mach.stateGas = .zero) && decide (c.keys = y.keys) &&
    decide (c.adrs = y.adrs) && decide (c.stor = y.stor) && decide (c.devm.refundCounter = y.rc) &&
    decide (c.devm.output = y.out) && decide (c.devm.returnData = y.rd) && c.devm.error.isNone,
    c.acs, c.devm.createdAccounts)

/-- A configuration decided at `y` is `y`'s at its own bookkeeping and world. -/
theorem cfg_of_xObs {y : XB} {A : AcctShadow} {c : PCfg} (h : xObs y c = xOk A) :
    c = y.cfg A c.devm.meta c.devm.world := by
  rcases y with ⟨pc, s, ⟨data, size⟩, g, rc, out, rd, keys, adrs, stor⟩
  rcases c with ⟨pc', ⟨⟨s', ⟨data', size'⟩, g', sg'⟩, m, w⟩, keys', adrs', stor', acs'⟩
  simp only [xObs, xOk, Prod.mk.injEq, Bool.and_eq_true, natEqW_eq, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hp, hs, hd, hsz, hg, hsg, hk, ha, hst, hrc, ho, hrd, he, hc, hcr⟩ := h
  have hd' : data' = data := Array.toList_inj.mp hd
  subst hp hs hd' hsz hg hsg hk ha hst hc
  rcases m with ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩
  simp only [Devm.refundCounter, Devm.output, Devm.returnData, Devm.error,
    Option.isNone_iff_eq_none, Devm.createdAccounts] at hrc ho hrd he hcr
  subst hrc ho hrd he hcr
  rfl

/-! ## Runs -/

/-- From every machine at `x` that its shadows describe, under every original state with the storage
of `s`'s, the frame runs to a successful halt at `z`, whose shadows describe it. -/
def RunsB (s : Sevm) (A : AcctShadow) (x z : XB) : Prop :=
  ∀ m w, PAgree (x.cfg A m w) → ∀ O, OrigAgree O s.benvStat.origState →
    ∃ m' w', Nonempty (Exec x.pc (s.withOrig O) (x.cfg A m w).devm (.ok (z.cfg A m' w').devm)) ∧
      PAgree (z.cfg A m' w')

/-- A walk chunk's decision. -/
def walkObs {code : ByteArray} {d : Nat} (T : CodeTries code d) (s : Sevm) (A : AcctShadow)
    (x y : XB) (n : Nat) (m : Meta) (w : World) : Option XObs :=
  match xWalkN T s n (x.cfg A m w) with
  | .cont c => some (xObs y c)
  | _ => none

theorem RunsB.walk {code : ByteArray} {d : Nat} (T : CodeTries code d) {s : Sevm} {A : AcctShadow}
    {x y z : XB} {n : Nat} (hcode : s.code = code)
    (hw : ∀ m w, walkObs T s A x y n m w = some (xOk A)) (r : RunsB s A y z) : RunsB s A x z := by
  intro m w hag O hO
  have hw' := hw m w
  unfold walkObs at hw'
  split at hw'
  · rename_i c1 h1
    have ho := cfg_of_xObs (Option.some.inj hw')
    obtain ⟨hag1, back⟩ := xWalkN_cont T hcode n _ c1 hag h1
    rw [ho] at hag1
    obtain ⟨m', w', hx, hag'⟩ := r _ _ hag1 O hO
    refine ⟨m', w', ?_, hag'⟩
    have h1O : xWalkN T (s.withOrig O) n (x.cfg A m w) = .cont c1 := by
      rw [xWalkN_withOrig hO, h1]
    obtain ⟨-, backO⟩ := xWalkN_cont T (by rw [Sevm.withOrig_code]; exact hcode) n _ c1 hag h1O
    refine backO _ ?_
    have hpc : c1.pc = y.pc := congrArg PCfg.pc ho
    have hd : c1.devm = (y.cfg A c1.devm.meta c1.devm.world).devm := congrArg PCfg.devm ho
    rw [hpc, hd]
    exact hx
  · simp only [reduceCtorEq] at hw'

/-- A halting step's decision: `z` is the halted machine, the shadows unchanged. -/
def haltObs {code : ByteArray} {d : Nat} (T : CodeTries code d) (s : Sevm) (A : AcctShadow)
    (x z : XB) (m : Meta) (w : World) : Option XObs :=
  let c := x.cfg A m w
  match xStep T s c with
  | .halt (.ok d') => some (xObs z ⟨z.pc, d', c.keys, c.adrs, c.stor, c.acs⟩)
  | _ => none

theorem RunsB.halt {code : ByteArray} {d : Nat} (T : CodeTries code d) {s : Sevm} {A : AcctShadow}
    {x z : XB} (hcode : s.code = code)
    (hh : ∀ m w, haltObs T s A x z m w = some (xOk A)) : RunsB s A x z := by
  intro m w hag O hO
  have hh' := hh m w
  unfold haltObs at hh'
  dsimp only at hh'
  split at hh'
  · rename_i d' h1
    have ho := cfg_of_xObs (Option.some.inj hh')
    obtain ⟨hstep, hp⟩ := xStep_halt T hcode h1
    have hca := halt_ok_childAgree T hag hp
    refine ⟨d'.meta, d'.world, ?_, ?_⟩
    · have hd : (z.cfg A d'.meta d'.world).devm = d' := (congrArg PCfg.devm ho).symm
      rw [hd]
      have h1O : xStep T (s.withOrig O) (x.cfg A m w) = .halt (.ok d') := by
        rw [xStep_withOrig hO]; exact h1
      exact ⟨Exec.halt (xStep_halt T (by rw [Sevm.withOrig_code]; exact hcode) h1O).1⟩
    · rw [← ho]
      exact ⟨hca.2.1, hca.1, hca.2.2.1, hca.2.2.2⟩
  · simp only [reduceCtorEq] at hh'

/-! ## Calls -/

/-- A call's flat base charge, where the rules are flat access, no state gas and no delegation, and
the frame may call. -/
def flatCall (s : Sevm) : Option Nat :=
  if s.benvStat.rules.stateGas.isNone ∧ s.benvStat.rules.delegationEnabled = false ∧ s.depth ≠ 0 then
    match s.benvStat.rules.access with
    | .flat g => some g.call
    | .eip2929 => none
  else none

/-- The stack below a call-family instruction's operands and its charges under flat access. -/
def flatSplit (d : Devm) (st : List B256) (gw iiw isw oiw osw : B256) (n : Nat) :
    Devm × Nat × Nat :=
  let d0 := d.setMach ⟨st, d.memory, d.gasLeft, d.stateGas⟩
  let ext := d0.extCost [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]
  let r := calculateMsgCallGas 0 gw.toNat d0.gasLeft ext n
  (d0, r.1 + ext, r.2)

/-- The preparation of a call-family instruction under flat access, zero value for `CALL`: the world's
code comes from the account shadow, and the accessed sets are untouched. -/
def prepX (s : Sevm) (c : PCfg) : Xinst → Option CallPrep
  | .staticcall =>
    match c.devm.stack, flatCall s with
    | gw :: tw :: iiw :: isw :: oiw :: osw :: st, some n =>
      let r := flatSplit c.devm st gw iiw isw oiw osw n
      if r.2.1 ≤ r.1.gasLeft then
        let p := callSpawnParent r.1 r.2.1 iiw.toNat isw.toNat oiw.toNat osw.toNat
        some ⟨Frame.ofCall (staticcallSpawnMsg s p r.2.2 tw.toAdr tw.toAdr iiw.toNat isw.toNat
          (lookupA c.acs tw.toAdr).code false), p, oiw.toNat, osw.toNat, c.adrs⟩
      else none
    | _, _ => none
  | .call =>
    match c.devm.stack, flatCall s with
    | gw :: cw :: vw :: iiw :: isw :: oiw :: osw :: st, some n =>
      let r := flatSplit c.devm st gw iiw isw oiw osw n
      if vw = 0 ∧ r.2.1 ≤ r.1.gasLeft then
        let p := callSpawnParent r.1 r.2.1 iiw.toNat isw.toNat oiw.toNat osw.toNat
        some ⟨Frame.ofCall (callSpawnMsg s p r.2.2 cw.toAdr cw.toAdr iiw.toNat isw.toNat
          (lookupA c.acs cw.toAdr).code false), p, oiw.toNat, osw.toNat, c.adrs⟩
      else none
    | _, _ => none
  | .delegatecall =>
    match c.devm.stack, flatCall s with
    | gw :: cw :: iiw :: isw :: oiw :: osw :: st, some n =>
      let r := flatSplit c.devm st gw iiw isw oiw osw n
      if r.2.1 ≤ r.1.gasLeft then
        let p := callSpawnParent r.1 r.2.1 iiw.toNat isw.toNat oiw.toNat osw.toNat
        some ⟨Frame.ofCall (delegatecallSpawnMsg s p r.2.2 cw.toAdr iiw.toNat isw.toNat
          (lookupA c.acs cw.toAdr).code false), p, oiw.toNat, osw.toNat, c.adrs⟩
      else none
    | _, _ => none
  | _ => none

theorem flatCall_withOrig (s : Sevm) (O : State) : flatCall (s.withOrig O) = flatCall s := rfl

theorem prepX_withOrig (s : Sevm) (O : State) (c : PCfg) (i : Xinst) :
    prepX (s.withOrig O) c i = (prepX s c i).map (·.withOrig O) := by
  cases i <;> simp only [prepX, Option.map_none, flatCall_withOrig]
  all_goals
    split
    · simp only [apply_ite (Option.map _), Option.map_none, Option.map_some]
      rfl
    · rfl

theorem flatCall_facts {s : Sevm} {n : Nat} (h : flatCall s = some n) :
    s.benvStat.rules.stateGas = none ∧ s.benvStat.rules.delegationEnabled = false ∧ s.depth ≠ 0 ∧
      ∃ g, s.benvStat.rules.access = .flat g ∧ g.call = n := by
  unfold flatCall at h
  split at h
  · rename_i hc
    obtain ⟨h1, h2, h3⟩ := hc
    split at h
    · rename_i g hg
      exact ⟨Option.isNone_iff_eq_none.mp h1, h2, h3, g, hg, Option.some.inj h⟩
    · cases h
  · cases h

theorem xinst_static_spawn {s : Sevm} {d : Devm} {gw tw iiw isw oiw osw : B256} {st : List B256}
    {n : Nat} (hf : flatCall s = some n) (hs : d.stack = gw :: tw :: iiw :: isw :: oiw :: osw :: st)
    (hg : (flatSplit d st gw iiw isw oiw osw n).2.1 ≤ (flatSplit d st gw iiw isw oiw osw n).1.gasLeft)
    {code : ByteArray}
    (hcode : (flatSplit d st gw iiw isw oiw osw n).1.state.getCode tw.toAdr = code) :
    let r := flatSplit d st gw iiw isw oiw osw n
    let p := callSpawnParent r.1 r.2.1 iiw.toNat isw.toNat oiw.toNat osw.toNat
    Xinst.step s d .staticcall =
      .spawn (Frame.ofCall (staticcallSpawnMsg s p r.2.2 tw.toAdr tw.toAdr iiw.toNat isw.toNat code false))
        (.call p oiw.toNat osw.toNat) := by
  obtain ⟨hsg, hdel, hdep, g, hacc, hgc⟩ := flatCall_facts hf
  subst hgc
  subst hcode
  simp only [Xinst.step, hsg, hacc, ForkRules.accessDelegation, hdel, Bool.false_eq_true, ↓reduceIte]
  rw [Devm.pop_eq_ok hs]
  simp only [bind, Except.bind]
  rw [Devm.popToAdr_eq_ok
    (devm := d.setMach ⟨tw :: iiw :: isw :: oiw :: osw :: st, d.memory, d.gasLeft, d.stateGas⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach, Devm.stateGas_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := d.setMach ⟨iiw :: isw :: oiw :: osw :: st, d.memory, d.gasLeft, d.stateGas⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach, Devm.stateGas_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := d.setMach ⟨isw :: oiw :: osw :: st, d.memory, d.gasLeft, d.stateGas⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach, Devm.stateGas_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := d.setMach ⟨oiw :: osw :: st, d.memory, d.gasLeft, d.stateGas⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach, Devm.stateGas_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := d.setMach ⟨osw :: st, d.memory, d.gasLeft, d.stateGas⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach, Devm.stateGas_setMach]
  simp only [Nat.add_zero]
  have hg' : (calculateMsgCallGas 0 gw.toNat d.gasLeft
      ((d.setMach ⟨st, d.memory, d.gasLeft, d.stateGas⟩).extCost
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]) g.call).1 +
      (d.setMach ⟨st, d.memory, d.gasLeft, d.stateGas⟩).extCost
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] ≤
      (d.setMach ⟨st, d.memory, d.gasLeft, d.stateGas⟩).gasLeft := hg
  rw [chargeGas_eq_ok hg']
  refine Eq.trans (b := genericCall.step s ((flatSplit d st gw iiw isw oiw osw g.call).1.setMach
      ⟨st, d.memory, d.gasLeft - (flatSplit d st gw iiw isw oiw osw g.call).2.1, d.stateGas⟩ |>.memExtends
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩])
      (flatSplit d st gw iiw isw oiw osw g.call).2.2 0 s.currentTarget tw.toAdr tw.toAdr true true
      iiw.toNat isw.toNat oiw.toNat osw.toNat
      ((flatSplit d st gw iiw isw oiw osw g.call).1.state.getCode tw.toAdr) false) ?_ ?_
  · rfl
  · rw [genericCall.step_spawn hdep]
    rfl

theorem xinst_delegate_spawn {s : Sevm} {d : Devm} {gw cw iiw isw oiw osw : B256} {st : List B256}
    {n : Nat} (hf : flatCall s = some n) (hs : d.stack = gw :: cw :: iiw :: isw :: oiw :: osw :: st)
    (hg : (flatSplit d st gw iiw isw oiw osw n).2.1 ≤ (flatSplit d st gw iiw isw oiw osw n).1.gasLeft)
    {code : ByteArray}
    (hcode : (flatSplit d st gw iiw isw oiw osw n).1.state.getCode cw.toAdr = code) :
    let r := flatSplit d st gw iiw isw oiw osw n
    let p := callSpawnParent r.1 r.2.1 iiw.toNat isw.toNat oiw.toNat osw.toNat
    Xinst.step s d .delegatecall =
      .spawn (Frame.ofCall (delegatecallSpawnMsg s p r.2.2 cw.toAdr iiw.toNat isw.toNat code false))
        (.call p oiw.toNat osw.toNat) := by
  obtain ⟨hsg, hdel, hdep, g, hacc, hgc⟩ := flatCall_facts hf
  subst hgc
  subst hcode
  simp only [Xinst.step, hsg, hacc, ForkRules.accessDelegation, hdel, Bool.false_eq_true, ↓reduceIte]
  rw [Devm.pop_eq_ok hs]
  simp only [bind, Except.bind]
  rw [Devm.popToAdr_eq_ok
    (devm := d.setMach ⟨cw :: iiw :: isw :: oiw :: osw :: st, d.memory, d.gasLeft, d.stateGas⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach, Devm.stateGas_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := d.setMach ⟨iiw :: isw :: oiw :: osw :: st, d.memory, d.gasLeft, d.stateGas⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach, Devm.stateGas_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := d.setMach ⟨isw :: oiw :: osw :: st, d.memory, d.gasLeft, d.stateGas⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach, Devm.stateGas_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := d.setMach ⟨oiw :: osw :: st, d.memory, d.gasLeft, d.stateGas⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach, Devm.stateGas_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := d.setMach ⟨osw :: st, d.memory, d.gasLeft, d.stateGas⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach, Devm.stateGas_setMach]
  simp only [Nat.add_zero]
  have hg' : (calculateMsgCallGas 0 gw.toNat d.gasLeft
      ((d.setMach ⟨st, d.memory, d.gasLeft, d.stateGas⟩).extCost
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]) g.call).1 +
      (d.setMach ⟨st, d.memory, d.gasLeft, d.stateGas⟩).extCost
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] ≤
      (d.setMach ⟨st, d.memory, d.gasLeft, d.stateGas⟩).gasLeft := hg
  rw [chargeGas_eq_ok hg']
  refine Eq.trans (b := genericCall.step s ((flatSplit d st gw iiw isw oiw osw g.call).1.setMach
      ⟨st, d.memory, d.gasLeft - (flatSplit d st gw iiw isw oiw osw g.call).2.1, d.stateGas⟩ |>.memExtends
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩])
      (flatSplit d st gw iiw isw oiw osw g.call).2.2 s.value s.caller s.currentTarget cw.toAdr false false
      iiw.toNat isw.toNat oiw.toNat osw.toNat
      ((flatSplit d st gw iiw isw oiw osw g.call).1.state.getCode cw.toAdr) false) ?_ ?_
  · rfl
  · rw [genericCall.step_spawn hdep]
    rfl

theorem xinst_call_spawn {s : Sevm} {d : Devm} {gw cw iiw isw oiw osw : B256} {st : List B256}
    {n : Nat} (hf : flatCall s = some n)
    (hs : d.stack = gw :: cw :: 0 :: iiw :: isw :: oiw :: osw :: st)
    (hg : (flatSplit d st gw iiw isw oiw osw n).2.1 ≤ (flatSplit d st gw iiw isw oiw osw n).1.gasLeft)
    {code : ByteArray}
    (hcode : (flatSplit d st gw iiw isw oiw osw n).1.state.getCode cw.toAdr = code) :
    let r := flatSplit d st gw iiw isw oiw osw n
    let p := callSpawnParent r.1 r.2.1 iiw.toNat isw.toNat oiw.toNat osw.toNat
    Xinst.step s d .call =
      .spawn (Frame.ofCall (callSpawnMsg s p r.2.2 cw.toAdr cw.toAdr iiw.toNat isw.toNat code false))
        (.call p oiw.toNat osw.toNat) := by
  obtain ⟨hsg, hdel, hdep, g, hacc, hgc⟩ := flatCall_facts hf
  subst hgc
  subst hcode
  simp only [Xinst.step, hsg, hacc, ForkRules.accessDelegation, hdel, Bool.false_eq_true, ↓reduceIte]
  rw [Devm.pop_eq_ok hs]
  simp only [bind, Except.bind]
  rw [Devm.popToAdr_eq_ok
    (devm := d.setMach ⟨cw :: 0 :: iiw :: isw :: oiw :: osw :: st, d.memory, d.gasLeft, d.stateGas⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach, Devm.stateGas_setMach]
  rw [Devm.pop_eq_ok
    (devm := d.setMach ⟨0 :: iiw :: isw :: oiw :: osw :: st, d.memory, d.gasLeft, d.stateGas⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach, Devm.stateGas_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := d.setMach ⟨iiw :: isw :: oiw :: osw :: st, d.memory, d.gasLeft, d.stateGas⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach, Devm.stateGas_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := d.setMach ⟨isw :: oiw :: osw :: st, d.memory, d.gasLeft, d.stateGas⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach, Devm.stateGas_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := d.setMach ⟨oiw :: osw :: st, d.memory, d.gasLeft, d.stateGas⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach, Devm.stateGas_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := d.setMach ⟨osw :: st, d.memory, d.gasLeft, d.stateGas⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach, Devm.stateGas_setMach]
  simp only [show ((0 : B256).toNat) = 0 from rfl, or_true, ↓reduceIte, Nat.add_zero]
  have hg' : (calculateMsgCallGas 0 gw.toNat d.gasLeft
      ((d.setMach ⟨st, d.memory, d.gasLeft, d.stateGas⟩).extCost
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]) g.call).1 +
      (d.setMach ⟨st, d.memory, d.gasLeft, d.stateGas⟩).extCost
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] ≤
      (d.setMach ⟨st, d.memory, d.gasLeft, d.stateGas⟩).gasLeft := hg
  rw [chargeGas_eq_ok hg']
  simp only [Except.assert, or_true, ↓reduceIte, Bool.not_eq_true']
  rw [ite_eq_right (by
    rw [B256.lt_iff_toNat_lt_toNat]
    exact Nat.not_lt.mpr (Nat.zero_le _))]
  refine Eq.trans (b := genericCall.step s ((flatSplit d st gw iiw isw oiw osw g.call).1.setMach
      ⟨st, d.memory, d.gasLeft - (flatSplit d st gw iiw isw oiw osw g.call).2.1, d.stateGas⟩ |>.memExtends
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩])
      (flatSplit d st gw iiw isw oiw osw g.call).2.2 0 s.currentTarget cw.toAdr cw.toAdr true false
      iiw.toNat isw.toNat oiw.toNat osw.toNat
      ((flatSplit d st gw iiw isw oiw osw g.call).1.state.getCode cw.toAdr) false) ?_ ?_
  · rfl
  · rw [genericCall.step_spawn hdep]
    rfl

/-- What a call-family instruction's preparation gives at an agreeing configuration. -/
theorem prepX_facts {s : Sevm} {c : PCfg} {cp : CallPrep} {i : Xinst} (hag : PAgree c)
    (hp : prepX s c i = some cp) :
    Xinst.step s c.devm i = .spawn cp.f (.call cp.p cp.oi cp.os) ∧ PrepFacts c cp := by
  have hsgn : ∀ {n}, flatCall s = some n → s.benvStat.rules.stateGas = none :=
    fun h => (flatCall_facts h).1
  have hc : ∀ a, (lookupA c.acs a).code = c.devm.state.getCode a := fun a => by
    have e := congrArg Acct.code (hag.2.2.2 a)
    exact e.symm
  cases i <;> simp only [prepX, reduceCtorEq] at hp
  · split at hp
    · rename_i gw cw vw iiw isw oiw osw st n hs hf
      split at hp
      · rename_i hcond
        obtain ⟨hv, hg⟩ := hcond
        subst hv
        cases hp
        exact ⟨xinst_call_spawn hf hs hg (hc cw.toAdr).symm, ⟨hag.2.1, rfl, rfl, rfl, rfl, hsgn hf, rfl⟩⟩
      · cases hp
    · cases hp
  · split at hp
    · rename_i gw cw iiw isw oiw osw st n hs hf
      split at hp
      · rename_i hg
        cases hp
        exact ⟨xinst_delegate_spawn hf hs hg (hc cw.toAdr).symm, ⟨hag.2.1, rfl, rfl, rfl, rfl, hsgn hf, rfl⟩⟩
      · cases hp
    · cases hp
  · split at hp
    · rename_i gw cw iiw isw oiw osw st n hs hf
      split at hp
      · rename_i hg
        cases hp
        exact ⟨xinst_static_spawn hf hs hg (hc cw.toAdr).symm, ⟨hag.2.1, rfl, rfl, rfl, rfl, hsgn hf, rfl⟩⟩
      · cases hp
    · cases hp

/-- The same at the frame's original state changed to `O`. -/
theorem prepX_core {code : ByteArray} {d : Nat} (T : CodeTries code d) {s : Sevm} {O : State}
    (hcode : s.code = code) {c : PCfg} {cp : CallPrep} {i : Xinst} (hag : PAgree c)
    (hdec : decodeT d T.bytes c.pc = some (.next (.exec i))) (hp : prepX s c i = some cp) :
    Evm.step ⟨c.pc, s.withOrig O, c.devm⟩ =
        .spawn (cp.withOrig O).f (.call (cp.withOrig O).p (cp.withOrig O).oi (cp.withOrig O).os)
          (c.pc + 1) ∧
      PrepFacts c (cp.withOrig O) := by
  have hat : Ninst.At (s.withOrig O).code c.pc (.exec i) := by
    rw [Sevm.withOrig_code, hcode]; exact decodeT_sound T hdec
  have hpO : prepX (s.withOrig O) c i = some (cp.withOrig O) := by
    rw [prepX_withOrig, hp]; rfl
  obtain ⟨hstep, hF⟩ := prepX_facts hag hpO
  refine ⟨?_, hF⟩
  rw [Evm.step_next hat]
  simp only [Ninst.step, hstep]
  rfl

/-- A call chunk's decision before its child: the instruction, the preparation, the frame's entry,
the child's start boundary and static machine.  The
child's gas is compared by `natEqW`: as a term, the kernel expands a large literal. -/
def spawnObs {code : ByteArray} {d : Nat} (T : CodeTries code d) (s : Sevm) (A : AcctShadow)
    (x cx : XB) (sc : Sevm) (m : Meta) (w : World) : Option (XObs × Nat × Sevm × Bool) :=
  let c := x.cfg A m w
  match decodeT d T.bytes c.pc with
  | some (.next (.exec i)) =>
    match prepX s c i with
    | none => none
    | some cp =>
      match frameEnterS cp.f c.acs with
      | .run e =>
        some (xObs cx (childCfg e cp.f c.keys cp.adrs c.stor c.acs), e.pc,
          { e.sta with gas := sc.gas }, natEqW e.sta.gas sc.gas)
      | .done _ => none
  | _ => none

/-- A call chunk's decision after its child: the parent's resume at boundary `y`, from any machine
at the child's end boundary `zc`. -/
def resumeObsC {code : ByteArray} {d : Nat} (T : CodeTries code d) (s : Sevm) (A : AcctShadow)
    (c : PCfg) (zc y : XB) (m' : Meta) (w' : World) : Option XObs :=
  match decodeT d T.bytes c.pc with
  | some (.next (.exec i)) =>
    match prepX s c i with
    | none => none
    | some cp =>
      match resumeCallB cp.p cp.oi cp.os (.ok (zc.cfg A m' w').devm) with
      | some d' =>
        some (xObs y ⟨c.pc + 1, d', mergeL c.keys zc.keys, mergeL cp.adrs zc.adrs, zc.stor, A⟩)
      | none => none
  | _ => none

/-- The shadows of a resumed parent, with its lists merged rather than appended. -/
theorem pagree_mergeL {c : PCfg} {cp : CallPrep} {d' : Devm} {zk : List (Adr × B256)}
    {za : List Adr} {zs : StorShadow} {A : AcctShadow}
    (h : PAgree ⟨c.pc + 1, d', c.keys ++ zk, cp.adrs ++ za, zs, A⟩) :
    PAgree ⟨c.pc + 1, d', mergeL c.keys zk, mergeL cp.adrs za, zs, A⟩ :=
  ⟨fun k => (h.1 k).trans (mem_mergeL _ _ _).symm,
    fun a => (h.2.1 a).trans (mem_mergeL _ _ _).symm, h.2.2.1, h.2.2.2⟩

/-- A successful call frame settles to its result with the touch recorded. -/
theorem frame_settle_touch {f : Frame} {post : Devm} (hcr : f.isCreate = false)
    (hsg : f.inner.benv.stat.rules.stateGas = none) (he : post.error = none) :
    f.settle (.ok post) = .ok (post.recordTouch f.inner.benv.stat.rules true f.inner.currentTarget) := by
  simp only [Frame.settle, Frame.settleMsg, hcr, Bool.false_eq_true, ↓reduceIte,
    processMessage.settle, bind, Except.bind, executeCode.handleErrorWith, hsg,
    executeCode.handleError, he, Option.isSome_none]

/-- Recording a touch moves only free bookkeeping: the machine stays at its boundary. -/
theorem cfg_recordTouch (z : XB) (A : AcctShadow) (m : Meta) (w : World) (R : ForkRules) (b : Bool)
    (t : Adr) :
    (z.cfg A ((z.cfg A m w).devm.recordTouch R b t).meta w).devm =
      (z.cfg A m w).devm.recordTouch R b t := rfl

/-- **A call into a code child.**  The child's run `rc` is its own composition from its boundary
`cx` to `zc`, over a static machine `sc` with the parent's block environment. -/
theorem RunsB.call {code : ByteArray} {d : Nat} (T : CodeTries code d) {s sc : Sevm}
    {A : AcctShadow} {x cx zc y z : XB} (hcode : s.code = code)
    (hstat : sc.benvStat = s.benvStat)
    (hsp : ∀ m w, spawnObs T s A x cx sc m w = some (xOk A, 0, sc, true))
    (rc : RunsB sc A cx zc)
    (hres : ∀ m w m' w', resumeObsC T s A (x.cfg A m w) zc y m' w' = some (xOk A))
    (r : RunsB s A y z) : RunsB s A x z := by
  intro m w hag O hO
  have hsp' := hsp m w
  unfold spawnObs at hsp'
  dsimp only at hsp'
  generalize hc : x.cfg A m w = c at hag hsp'
  split at hsp'
  · rename_i i hdec
    split at hsp'
    · simp only [reduceCtorEq] at hsp'
    · rename_i cp hp
      split at hsp'
      · rename_i e he
        simp only [Option.some.injEq, Prod.mk.injEq] at hsp'
        obtain ⟨hob, hpc, hsta', hgas⟩ := hsp'
        have hsta : e.sta = sc := by
          have hg : e.sta.gas = sc.gas := eq_of_natEqW hgas
          rw [← hsta']
          generalize e.sta = t at hg
          rw [← hg]
        obtain ⟨hstep, hF⟩ := prepX_core T (O := O) hcode hag hdec hp
        have heO : frameEnterS (cp.withOrig O).f c.acs = .run (e.withOrig O) :=
          frameEnterS_withOrig he
        have hC : AcctAgree (cp.withOrig O).f.inner.benv.state c.acs := by
          rw [hF.state]; exact hag.2.2.2
        have hent : (cp.withOrig O).f.enter = .run (e.withOrig O) := by
          rw [frame_enter_eq_B, frameEnterB_eq_S hC]; exact heO
        have hagc : PAgree (childCfg e cp.f c.keys cp.adrs c.stor c.acs) :=
          (frameStart_agree (f := (cp.withOrig O).f) (keys := c.keys) (adrs := cp.adrs)
            (stor := c.stor) .undefined heO
            (fun y => by rw [hF.entryKeys, hF.keys]; exact hag.1 y)
            (fun a => by rw [hF.entryAdrs]; exact hF.adrs a)
            (fun a k => by rw [hF.state]; exact hag.2.2.1 a k)
            (by rw [hF.state]; exact hag.2.2.2) :
            PAgree (childCfg (e.withOrig O) (cp.withOrig O).f c.keys cp.adrs c.stor c.acs))
        have ho := cfg_of_xObs hob
        generalize hcc : childCfg e cp.f c.keys cp.adrs c.stor c.acs = cc at hagc hob ho
        rw [ho] at hagc
        have hO' : OrigAgree O sc.benvStat.origState := by rw [hstat]; exact hO
        obtain ⟨m1, w1, hx1, hag1⟩ := rc _ _ hagc O hO'
        have hdcc : (cx.cfg A cc.devm.meta cc.devm.world).devm = e.dyna := by
          rw [← ho, ← hcc]; rfl
        have hpcc : cx.pc = e.pc := by
          have : cc.pc = cx.pc := congrArg PCfg.pc ho
          rw [← this, ← hcc]; rfl
        rw [hdcc, hpcc] at hx1
        -- the child's derivation at the machine it was entered with
        have hxe : Nonempty (Exec (e.withOrig O).pc (e.withOrig O).sta (e.withOrig O).dyna
            (.ok (zc.cfg A m1 w1).devm)) := by
          have hs : (e.withOrig O).sta = sc.withOrig O := by
            show e.sta.withOrig O = _
            rw [hsta]
          rw [hs]
          exact hx1
        -- the parent resumes
        have hce : (zc.cfg A m1 w1).devm.error = none := rfl
        generalize hR : (cp.withOrig O).f.inner.benv.stat.rules = R
        generalize hT : (cp.withOrig O).f.inner.currentTarget = t
        have hset : (cp.withOrig O).f.settle (.ok (zc.cfg A m1 w1).devm) =
            .ok ((zc.cfg A m1 w1).devm.recordTouch R true t) := by
          rw [← hR, ← hT]
          exact frame_settle_touch hF.create hF.stateGas hce
        generalize hm2 : ((zc.cfg A m1 w1).devm.recordTouch R true t).meta = m2
        have hd2 : (zc.cfg A m2 w1).devm = (zc.cfg A m1 w1).devm.recordTouch R true t := by
          rw [← hm2]; exact cfg_recordTouch zc A m1 w1 R true t
        have hag1' : PAgree (zc.cfg A m2 w1) := by
          subst hm2
          exact hag1
        have hres' := hres m w m2 w1
        rw [hc] at hres'
        unfold resumeObsC at hres'
        rw [hdec] at hres'
        simp only [hp] at hres'
        split at hres'
        · rename_i d' hr
          have ho2 := cfg_of_xObs (Option.some.inj hres')
          have hagr : PAgree ⟨c.pc + 1, d', mergeL c.keys zc.keys, mergeL cp.adrs zc.adrs, zc.stor,
              A⟩ := pagree_mergeL (resume_agree_ok_of (cp := cp.withOrig O) hag hF rfl
            (childAgree_of_pagree hag1') hr)
          rw [ho2] at hagr
          obtain ⟨m3, w3, hx2, hag2⟩ := r _ _ hagr O hO
          refine ⟨m3, w3, ?_, hag2⟩
          have hpy : y.pc = c.pc + 1 := (congrArg PCfg.pc ho2).symm
          have hdy : (y.cfg A d'.meta d'.world).devm = d' := by
            have := congrArg PCfg.devm ho2
            exact this.symm
          have hrs : Resume.run (.call (cp.withOrig O).p (cp.withOrig O).oi (cp.withOrig O).os)
              ((cp.withOrig O).f.settle (.ok (zc.cfg A m1 w1).devm)) = .ok d' := by
            rw [hset, ← hd2]; exact resumeCallB_sound hr
          rw [hpy, hdy] at hx2
          have hxpc : x.pc = c.pc := by rw [← hc]; rfl
          rw [hxpc]
          obtain ⟨rch⟩ := hxe
          obtain ⟨rest⟩ := hx2
          exact ⟨Exec.runOk hstep hent rch hrs rest⟩
        · simp only [reduceCtorEq] at hres'
      · simp only [reduceCtorEq] at hsp'
  · simp only [reduceCtorEq] at hsp'

/-! ## Precompile calls -/

/-- A precompile call's decision: the instruction, the preparation, the entry's synchronous answer
and the resume at boundary `y`; also the call's value and whether the answer is an error. -/
def doneObsC {code : ByteArray} {d : Nat} (T : CodeTries code d) (s : Sevm) (c : PCfg) (y : XB) :
    Option (XObs × B256 × Bool) :=
  match decodeT d T.bytes c.pc with
  | some (.next (.exec i)) =>
    match prepX s c i with
    | none => none
    | some cp =>
      match frameEnterS cp.f c.acs with
      | .done (.ok ch) =>
        match resumeCallB cp.p cp.oi cp.os (.ok ch) with
        | some d' =>
          some (xObs y ⟨c.pc + 1, d', c.keys, cp.adrs, c.stor, c.acs⟩, cp.f.inner.value,
            ch.error.isSome)
        | none => none
      | _ => none
  | _ => none

/-- The shadows after a successful zero-value precompile call: as `staticcall_done_node`, for any
call-family preparation. -/
theorem done_agree {c : PCfg} {cp : CallPrep} {child d : Devm} (hag : PAgree c)
    (hF : PrepFacts c cp) (hv : cp.f.inner.value = 0)
    (he : frameEnterS cp.f c.acs = .done (.ok child)) (hce : child.error.isSome = false)
    (hr : resumeCallB cp.p cp.oi cp.os (.ok child) = some d) :
    cp.f.enter = .done (.ok child) ∧ PAgree ⟨c.pc + 1, d, c.keys, cp.adrs, c.stor, c.acs⟩ := by
  have hC : AcctAgree cp.f.inner.benv.state c.acs := by rw [hF.state]; exact hag.2.2.2
  have heB : frameEnterB cp.f = .done (.ok child) := by rw [frameEnterB_eq_S hC]; exact he
  refine ⟨by rw [frame_enter_eq_B]; exact heB, ?_⟩
  obtain ⟨hda, hdk⟩ := resumeCallB_acc hr
  obtain ⟨hca, hck⟩ := frameEnterB_done_acc hF.create hF.stateGas heB
  obtain ⟨benv, hb, hcst⟩ := frameEnterB_done_ok_state hF.create hF.stateGas heB hce
  rw [benvAfterTransfer_eq_S hC] at hb
  have hb' := hb
  simp only [benvAfterTransferS, hv, ne_eq, not_true_eq_false, and_false, ite_false,
    Except.ok.injEq] at hb'
  refine ⟨fun y => ?_, fun a => ?_, fun a k => ?_, fun a => ?_⟩
  · show y ∈ d.accessedStorageKeys ↔ y ∈ c.keys
    rw [hdk y, hck, hF.entryKeys, hF.keys]
    exact ⟨fun h => (h.elim id (·.2)) |> (hag.1 y).mp, fun h => .inl ((hag.1 y).mpr h)⟩
  · show a ∈ d.accessedAddresses ↔ a ∈ cp.adrs
    rw [hda a, hca, hF.entryAdrs, hF.adrs a]
    exact ⟨fun h => h.elim id (·.2), .inl⟩
  · show storOf d.state a k = lookupS c.stor a k
    rw [resumeCallB_state hr, hcst, ← hb', hF.state]
    exact hag.2.2.1 a k
  · show acctView (d.state.get a) = lookupA c.acs a
    rw [resumeCallB_state hr, hcst, ← hb', hF.state]
    exact hag.2.2.2 a

/-- **A zero-value call answered synchronously** (Vyper's identity-precompile copies). -/
theorem RunsB.done {code : ByteArray} {d : Nat} (T : CodeTries code d) {s : Sevm}
    {A : AcctShadow} {x y z : XB} (hcode : s.code = code)
    (hd : ∀ m w, doneObsC T s (x.cfg A m w) y = some (xOk A, 0, false))
    (r : RunsB s A y z) : RunsB s A x z := by
  intro m w hag O hO
  have hd' := hd m w
  generalize hc : x.cfg A m w = c at hag hd'
  unfold doneObsC at hd'
  split at hd'
  · rename_i i hdec
    split at hd'
    · simp only [reduceCtorEq] at hd'
    · rename_i cp hp
      split at hd'
      · rename_i ch he
        split at hd'
        · rename_i d' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at hd'
          obtain ⟨hob, hv, hce⟩ := hd'
          obtain ⟨hstep, hF⟩ := prepX_core T (O := O) hcode hag hdec hp
          have heO : frameEnterS (cp.withOrig O).f c.acs = .done (.ok ch) :=
            (frameEnterS_withOrig_eq (O := O) cp.f c.acs).trans (by rw [he]; rfl)
          obtain ⟨hent, hagr'⟩ := done_agree (cp := cp.withOrig O) hag hF hv heO hce hr
          have hagr : PAgree ⟨c.pc + 1, d', c.keys, cp.adrs, c.stor, c.acs⟩ := hagr'
          have ho2 := cfg_of_xObs hob
          rw [ho2] at hagr
          have hdy : (y.cfg A d'.meta d'.world).devm = d' := (congrArg PCfg.devm ho2).symm
          have hpy : y.pc = c.pc + 1 := (congrArg PCfg.pc ho2).symm
          obtain ⟨m2, w2, hx2, hag2⟩ := r _ _ hagr O hO
          refine ⟨m2, w2, ?_, hag2⟩
          rw [hpy, hdy] at hx2
          have hxpc : x.pc = c.pc := by rw [← hc]; rfl
          rw [hxpc]
          obtain ⟨rest⟩ := hx2
          exact ⟨Exec.doneOk hstep hent (resumeCallB_sound hr) rest⟩
        · simp only [reduceCtorEq] at hd'
      · simp only [reduceCtorEq] at hd'
  · simp only [reduceCtorEq] at hd'

/-! ## A top-level message -/

/-- **A top-level message's run.**  A message whose static machine is `s` under an original state
`O` with `s`'s storage, whose start configuration decides at `x` with the given shadows, runs by
`exec` to `z`. -/
theorem exec_of_runsB {m : Msg} {s : Sevm} {A : AcctShadow} {x z : XB} {O : State}
    (hs : initSevm m = s.withOrig O) (hO : OrigAgree O s.benvStat.origState) (hx : x.pc = 0)
    (hob : xObs x ⟨0, initDevm m, x.keys, x.adrs, x.stor, A⟩ = xOk A)
    (hag : PAgree ⟨0, initDevm m, x.keys, x.adrs, x.stor, A⟩) (r : RunsB s A x z) :
    ∃ m' w', exec (initEvm m) = .ok (z.cfg A m' w').devm ∧ PAgree (z.cfg A m' w') := by
  have ho := cfg_of_xObs hob
  have hd : (x.cfg A (initDevm m).meta (initDevm m).world).devm = initDevm m :=
    (congrArg PCfg.devm ho).symm
  rw [ho] at hag
  obtain ⟨m', w', hxe, hag'⟩ := r _ _ hag _ hO
  refine ⟨m', w', ?_, hag'⟩
  rw [hd, hx, ← hs] at hxe
  exact (exec_iff_exec_eq _ _ _ _).mp hxe

/-- Bytes of a number, big-endian, in `len` bytes. -/
def bytesBE : Nat → Nat → List UInt8 → List UInt8
  | 0, _, acc => acc
  | k + 1, n, acc => bytesBE k (n / 256) (UInt8.ofNat (n % 256) :: acc)

/-- A memory literal: `len` bytes of data, big-endian in `n`, of the given size. -/
def memHex (size len n : Nat) : Mem := ⟨⟨bytesBE len n []⟩, size⟩

end Blanc.Lift.Curve3Pool.VirtualPriceFalls
