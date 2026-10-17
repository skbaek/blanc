import Blanc.Lift.Curve3Pool.Walk.Kit
import Blanc.Lift.InvWalkCallNext

/-!
# `exchange`: the frame save and restore around `get_y`, on the actual derivation

Before calling `get_y`, `exchange` pushes its whole frame `[0x140, 0x7e0)` (53 words) on the
stack with a counted loop (`0x2754`, counter word `0x7e0`), and after the call pops it back with
the mirror loop (`0x27d9`, counting down to `0x140`). On the actual derivation each loop is an
induction over the words left:

* `xa_ex_save`: from counter `p` with `k + 1` words left, the walk reaches the exit `0x2777`
  with the words `p, p + 32, …` pushed (`exSaved`, the last on top) and memory changed only at
  the counter word;
* `xa_ex_restore`: from counter `0x140 + 32 k` with `exSaved w 0x140 (k + 1)` on the stack, the
  walk reaches `0x27fd` with those words written back at `0x140, …, 0x140 + 32 k` and memory
  otherwise kept below `0x140`, between the frame's top and the counter, and from `0x800`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The `k` words of `w` from offset `p` up, as a frame save leaves them on the stack (the
highest offset on top). -/
def exSaved (w : Nat → B256) (p : Nat) : Nat → List B256
  | 0 => []
  | k + 1 => exSaved w (p + 32) k ++ [w p]

theorem exSaved_succ (w : Nat → B256) (k : Nat) :
    ∀ p, exSaved w p (k + 1) = w (p + 32 * k) :: exSaved w p k := by
  induction k with
  | zero => intro p; rfl
  | succ k ih =>
    intro p
    show exSaved w (p + 32) (k + 1) ++ [w p] = _
    rw [ih (p + 32)]
    show _ = w (p + 32 * (k + 1)) :: (exSaved w (p + 32) k ++ [w p])
    rw [show p + 32 + 32 * k = p + 32 * (k + 1) by ring]
    rfl

theorem ex_add32 {p : Nat} (hp : p + 32 < 2 ^ 256) :
    Nat.toB256 p + Bytes.toB256 [0x20] = Nat.toB256 (p + 32) := by
  apply B256.toNat_inj
  rw [B256.toNat_add, B256.toNat_toB256_of_lt (by omega), B256.toNat_toB256_of_lt hp,
    show (Bytes.toB256 [0x20]).toNat = 32 by decide, Nat.lo, Nat.mod_eq_of_lt hp]

theorem ex_sub32 {p : Nat} (hp : 32 ≤ p) (hp' : p < 2 ^ 256) :
    Nat.toB256 p - Bytes.toB256 [0x20] = Nat.toB256 (p - 32) := by
  apply B256.toNat_inj
  rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr (by
      rw [B256.toNat_toB256_of_lt hp', show (Bytes.toB256 [0x20]).toNat = 32 by decide]; exact hp)),
    B256.toNat_toB256_of_lt hp', B256.toNat_toB256_of_lt (by omega),
    show (Bytes.toB256 [0x20]).toNat = 32 by decide]

theorem ex_ltCheck {p q : Nat} (hp : p < 2 ^ 256) (hq : q < 2 ^ 256) :
    (B256.ltCheck (Nat.toB256 p) (Nat.toB256 q) = 0 ↔ ¬ p < q) := by
  constructor
  · intro h hlt
    exact ltCheck_ne_zero_of_lt (by
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hp, B256.toNat_toB256_of_lt hq]
      exact hlt) h
  · intro h
    exact ltCheck_eq_zero_of_le (by
      rw [B256.toNat_toB256_of_lt hp, B256.toNat_toB256_of_lt hq]; omega)

/-- **`PC` on the actual derivation** pushes the instruction's own pc (`xa_next` forgets it). -/
theorem xa_ex_pc {sevm : Sevm} {post : Devm} {pc : Nat} {L : List Exec.Frame} {b : Devm}
    {S : List B256} {M : Mem} {G : Nat} (hat : Ninst.At sevm.code pc (.reg .pc))
    (h : XAt sevm post pc (St b S M G) L) :
    ∃ G', XAt sevm post (pc + 1) (St b (Nat.toB256 pc :: S) M G') L := by
  have hstep : Evm.step ⟨pc, sevm, St b S M G⟩ = Ninst.step ⟨pc, sevm, St b S M G⟩ (.reg .pc) :=
    Evm.step_next hat
  obtain ⟨exc, hL, hg⟩ := h
  cases exc with
  | halt h => cases Ninst.step_ne_halt_ok (hstep.symm.trans h)
  | cont h next =>
    rename_i d'
    have hs := hstep.symm.trans h
    cases Ninst.step_cont_pc hs
    have hrun : Ninst.StepRun pc sevm (St b S M G) (.reg .pc) .none (.ok d') := by
      simp only [Ninst.StepRun, hs, Step.Run]
      exact ⟨trivial, trivial⟩
    have hp := Devm.pushBurn_of_pushItem (pushItem_of_stepRun_pc hrun)
    have hst : _ := hp.stack
    simp only [Stack.Push, Split, St.stack, List.cons_append, List.nil_append] at hst
    have e := St.of_stackRel hp
    rw [hst] at e
    have hx : XAt sevm post (pc + 1) d' L := ⟨next, hL, lt_trans (gas_cont h) hg⟩
    rw [e] at hx
    exact ⟨_, hx⟩
  | doneOk h _ _ _ =>
    obtain ⟨x, hx, -⟩ := Ninst.step_spawn_inv (hstep.symm.trans h)
    cases hx
  | runOk h _ _ _ _ =>
    obtain ⟨x, hx, -⟩ := Ninst.step_spawn_inv (hstep.symm.trans h)
    cases hx

set_option hygiene false in
/-- A `PC` at the walk's pc, landing at `pc'`. -/
macro "xpc " pc:term:max : tactic => `(tactic| (
  replace h := xa_ex_pc (atN hcode (by kernel_rfl)) h
  obtain ⟨_, h⟩ := h
  change XAt sevm post $pc _ _ at h))

/-- An `MLOAD` over the image carrier also leaves the memory's logical size word-aligned
(an expansion by a nonzero width always rounds the size up to a multiple of 32). -/
theorem ri_mload_imgAl {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {img : Bytes}
    {d : Devm} {i : B256} {o : Nat} (ho : i.toNat = o) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : Ninst.Run sevm (St b (i :: S) M G) (.reg .mload) d) :
    ∃ M' G', d = St b (Bytes.toB256 (img.sliceD o 32 0) :: S) M' G' ∧
      Mem.Reads M' img ∧ Mem.Wf M' ∧ M'.size % 32 = 0 := by
  subst ho
  obtain ⟨G', rfl⟩ := ri_mload h
  refine ⟨M.extend i.toNat 32, G', by rw [Mem.Reads.read hR]; rfl, Mem.Reads.extend hR _ _,
    Mem.Wf.extend hW _ _, ?_⟩
  show memExtSize M.size _ 32 % 32 = 0
  unfold memExtSize
  rw [if_neg (by decide)]
  exact Nat.mul_mod_right _ _

/-- **A value-0 identity `CALL` at depth `0`** fails without a child: it pushed `0` over the same
base and the same memory bytes. -/
theorem ri_call_identity_depth0 {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {g ii is oi os : B256} {d : Devm} (hid : IdReady sevm b) (hdepth : sevm.depth = 0)
    (h : Ninst.Run sevm (St b (g :: 4 :: 0 :: ii :: is :: oi :: os :: S) M G) (.exec .call) d) :
    ∃ G', d = St (b.withReturnData []) (0 :: S)
      (M.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]) G' := by
  have hfork := hid.fork
  rcases h with ⟨xl, h_fill, pc, h_run⟩
  simp only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.step,
    Bind.bind, Except.bind, hfork.rules_stateGas_none] at h_run
  rw [show (St b (g :: 4 :: 0 :: ii :: is :: oi :: os :: S) M G).pop =
    .ok (g, St b (4 :: 0 :: ii :: is :: oi :: os :: S) M G) from rfl] at h_run
  simp only at h_run
  rw [show (St b (4 :: 0 :: ii :: is :: oi :: os :: S) M G).popToAdr =
    .ok ((4 : Adr), St b (0 :: ii :: is :: oi :: os :: S) M G) from rfl] at h_run
  simp only at h_run
  rw [show (St b (0 :: ii :: is :: oi :: os :: S) M G).pop =
    .ok (0, St b (ii :: is :: oi :: os :: S) M G) from rfl] at h_run
  simp only at h_run
  rw [show (St b (ii :: is :: oi :: os :: S) M G).popToNat =
    .ok (ii.toNat, St b (is :: oi :: os :: S) M G) from rfl] at h_run
  simp only at h_run
  rw [show (St b (is :: oi :: os :: S) M G).popToNat =
    .ok (is.toNat, St b (oi :: os :: S) M G) from rfl] at h_run
  simp only at h_run
  rw [show (St b (oi :: os :: S) M G).popToNat =
    .ok (oi.toNat, St b (os :: S) M G) from rfl] at h_run
  simp only at h_run
  rw [show (St b (os :: S) M G).popToNat =
    .ok (os.toNat, St b S M G) from rfl] at h_run
  simp only at h_run
  have hAD : sevm.benvStat.rules.gas.accessDelegation (addAccessedAddress (St b S M G) 4) 4 =
      ⟨false, 4, b.getCode 4, 0, addAccessedAddress (St b S M G) 4⟩ := by
    unfold GasSchedule.accessDelegation
    simp only [show (addAccessedAddress (St b S M G) 4).state.getCode 4 = b.getCode 4 from rfl,
      hid.nodeleg]
  have hA : addAccessedAddress (St b S M G) 4 = St b S M G :=
    addAccessedAddress_eq_self_of_mem hid.warm
  rw [hAD, hA] at h_run
  simp only [or_true, ↓reduceIte, Except.assert] at h_run
  have hbal : ∀ x : B256, ¬ x < 0 := fun x hx => by
    rw [B256.lt_iff_toNat_lt_toNat] at hx; exact Nat.not_lt_zero _ hx
  split at h_run
  · cases XStep.run_ofExcept_error h_run
  rename_i v hcharge
  simp only [hbal, ↓reduceIte] at h_run
  obtain ⟨Gv, rfl⟩ : ∃ Gv, v = St b S M Gv :=
    ⟨_, Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas hcharge)⟩
  simp only [pure, Except.pure, XStep.ofExcept, genericCall.step, hdepth, ite_true] at h_run
  simp only [bind, Except.bind] at h_run
  split at h_run
  · simp only [XStep.Run, ExceptT.stM_eq, reduceCtorEq, and_false] at h_run
  · rename_i d' hp
    split at hp
    · cases hp
    · rename_i d'' hpush
      cases hp
      simp only [XStep.Run, Except.ok.injEq] at h_run
      rw [h_run.2, Devm.eq_of_push_ok hpush]
      exact ⟨_, rfl⟩

theorem BaseRel.withReturnData (b : Devm) (rd : Bytes) : BaseRel b (b.withReturnData rd) :=
  ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl⟩

/-- **An identity copy at depth `0`**, on the actual derivation: it pushed `0` over the same
base (up to the return data) and the same memory image. -/
theorem xa_identity_depth0 {sevm : Sevm} {post : Devm} {pc pc' : Nat} {L : List Exec.Frame}
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {img : Bytes} {g ii is oi os : B256}
    (hid : IdReady sevm b) (hdepth : sevm.depth = 0) (hat : Ninst.At sevm.code pc (.exec .call))
    (hpc : pc + 1 = pc') (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : XAt sevm post pc (St b (g :: 4 :: 0 :: ii :: is :: oi :: os :: S) M G) L) :
    ∃ L' M' G', XAt sevm post pc' (St (b.withReturnData []) (0 :: S) M' G') L' ∧
      Mem.Reads M' img ∧ Mem.Wf M' := by
  subst hpc
  obtain ⟨d, s, L', h, -⟩ := xa_call hid.fork hat rfl h
  obtain ⟨G', rfl⟩ := ri_call_identity_depth0 hid hdepth s
  exact ⟨L', _, G', h, Mem.Reads.extends _ hR, Mem.Wf.extends _ hW⟩

/-- One iteration of the frame save at counter `p`. -/
theorem xa_ex_saveStep {sevm : Sevm} {post : Devm} {L : List Exec.Frame} {b : Devm}
    {S : List B256} {M : Mem} {img : Bytes} {G p : Nat} {v : B256} (hcode : sevm.code = code)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hp : p + 32 ≤ 0x7e0)
    (hctr : WordAt img 0x7e0 (Nat.toB256 p)) (hv : WordAt img p v)
    (h : XAt sevm post 0x2754 (St b S M G) L) :
    ∃ M' G', Mem.Reads M' (Bytes.writeAt img 0x7e0 (Nat.toB256 (p + 32)).toBytes) ∧ Mem.Wf M' ∧
      XAt sevm post (if p + 32 = 0x7e0 then 0x2777 else 0x2754) (St b (v :: S) M' G') L := by
  xjd 0x2755
  xs 0x2758 (.push [0x07, 0xe0] (by decide)) ri_push
  xmo 0x2759 (.reg .mload) (ri_mload_imgAt (o := 0x7e0) rfl)
  rw [hctr.read] at h
  xmo 0x275a (.reg .mload) ri_mload_img
  rw [B256.toNat_toB256_of_lt (by omega), hv.read] at h
  xs 0x275c (.push [0x20] (by decide)) ri_push
  xs 0x275f (.push [0x07, 0xe0] (by decide)) ri_push
  xmo 0x2760 (.reg .mload) (ri_mload_imgAt (o := 0x7e0) rfl)
  rw [hctr.read] at h
  xs 0x2761 (.reg .add) ri_add
  rw [ex_add32 (by omega)] at h
  xs 0x2764 (.push [0x07, 0xe0] (by decide)) ri_push
  xmo 0x2765 (.reg .mstore) (ri_mstore_imgAt (o := 0x7e0) rfl)
  xs 0x2768 (.push [0x07, 0xe0] (by decide)) ri_push
  xs 0x276b (.push [0x07, 0xe0] (by decide)) ri_push
  xmo 0x276c (.reg .mload) (ri_mload_imgAt (o := 0x7e0) rfl)
  rw [(WordAt.write_self _ _ _).read] at h
  xs 0x276d (.reg .lt) ri_lt
  xs 0x276e (.reg .iszero) ri_iszero
  xs 0x2771 (.push [0x27, 0x76] (by decide)) ri_push
  xji 0x2772 0x2776 hw
  · have hlt : p + 32 < 0x7e0 := by
      have e := eqCheck_eq_zero hw
      by_contra hn
      exact e ((ex_ltCheck (q := 0x7e0) (by omega) (by decide)).mpr hn)
    xs 0x2775 (.push [0x27, 0x54] (by decide)) ri_push
    xjmp 0x2754
    rw [if_neg (by omega)]
    exact ⟨_, _, hR, hW, h⟩
  · have hge : ¬ p + 32 < 0x7e0 := (ex_ltCheck (q := 0x7e0) (by omega) (by decide)).mp
      (eqCheck_ne_zero_eq hw)
    xjd 0x2777
    rw [if_pos (by omega)]
    exact ⟨_, _, hR, hW, h⟩

/-- **The frame save** (`0x2754` → `0x2777`). -/
theorem xa_ex_save {sevm : Sevm} {post : Devm} {L : List Exec.Frame} (hcode : sevm.code = code)
    (w : Nat → B256) (k : Nat) :
    ∀ {b : Devm} {S : List B256} {M : Mem} {img : Bytes} {G p : Nat},
    Mem.Reads M img → Mem.Wf M → p + 32 * (k + 1) = 0x7e0 →
    WordAt img 0x7e0 (Nat.toB256 p) → (∀ m, m < k + 1 → WordAt img (p + 32 * m) (w (p + 32 * m))) →
    XAt sevm post 0x2754 (St b S M G) L →
    ∃ M' img' G', Mem.Reads M' img' ∧ Mem.Wf M' ∧
      (∀ o v, WordAt img o v → o + 32 ≤ 0x7e0 ∨ 0x800 ≤ o → WordAt img' o v) ∧
      XAt sevm post 0x2777 (St b (exSaved w p (k + 1) ++ S) M' G') L := by
  induction k with
  | zero =>
    intro b S M img G p hR hW hp hctr hws h
    have hv := hws 0 (by omega)
    rw [Nat.mul_zero, Nat.add_zero] at hv
    obtain ⟨M', G', hR', hW', h'⟩ := xa_ex_saveStep hcode hR hW (by omega) hctr hv h
    rw [if_pos (by omega)] at h'
    exact ⟨M', _, G', hR', hW', fun o v hov ho => hov.write_other (by
      simp only [B256.length_toBytes]; omega), h'⟩
  | succ k ih =>
    intro b S M img G p hR hW hp hctr hws h
    have hv := hws 0 (by omega)
    rw [Nat.mul_zero, Nat.add_zero] at hv
    obtain ⟨M1, G1, hR1, hW1, h1⟩ := xa_ex_saveStep hcode hR hW (by omega) hctr hv h
    rw [if_neg (by omega)] at h1
    obtain ⟨M2, img2, G2, hR2, hW2, hk2, h2⟩ := ih (p := p + 32) hR1 hW1 (by omega)
      (WordAt.write_self _ _ _) (fun m hm => by
        have e := hws (m + 1) (by omega)
        rw [show p + 32 * (m + 1) = p + 32 + 32 * m by ring] at e
        exact e.write_other (by simp only [B256.length_toBytes]; omega)) h1
    refine ⟨M2, img2, G2, hR2, hW2, fun o v hov ho => hk2 o v (hov.write_other (by
      simp only [B256.length_toBytes]; omega)) ho, ?_⟩
    rw [show exSaved w p (k + 1 + 1) = exSaved w (p + 32) (k + 1) ++ [w p] from rfl,
      List.append_assoc]
    exact h2

/-- One iteration of the frame restore at counter `q`. -/
theorem xa_ex_restoreStep {sevm : Sevm} {post : Devm} {L : List Exec.Frame} {b : Devm}
    {S : List B256} {M : Mem} {img : Bytes} {G q : Nat} {v : B256} (hcode : sevm.code = code)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hq : 0x140 ≤ q) (hq' : q + 32 ≤ 0x7e0)
    (hctr : WordAt img 0x7e0 (Nat.toB256 q))
    (h : XAt sevm post 0x27d9 (St b (v :: S) M G) L) :
    ∃ M' G', Mem.Reads M' (Bytes.writeAt (Bytes.writeAt img q v.toBytes) 0x7e0
        (Nat.toB256 (q - 32)).toBytes) ∧ Mem.Wf M' ∧
      XAt sevm post (if q < 0x160 then 0x27fd else 0x27d9) (St b S M' G') L := by
  xjd 0x27da
  xs 0x27dd (.push [0x07, 0xe0] (by decide)) ri_push
  xmo 0x27de (.reg .mload) (ri_mload_imgAt (o := 0x7e0) rfl)
  rw [hctr.read] at h
  xmo 0x27df (.reg .mstore) (ri_mstore_imgAt (o := q) (B256.toNat_toB256_of_lt (by omega)))
  have hctr1 : WordAt (Bytes.writeAt img q v.toBytes) 0x7e0 (Nat.toB256 q) :=
    hctr.write_other (by simp only [B256.length_toBytes]; omega)
  xs 0x27e1 (.push [0x20] (by decide)) ri_push
  xs 0x27e4 (.push [0x07, 0xe0] (by decide)) ri_push
  xmo 0x27e5 (.reg .mload) (ri_mload_imgAt (o := 0x7e0) rfl)
  rw [hctr1.read] at h
  xs 0x27e6 (.reg .sub) ri_sub
  rw [ex_sub32 (by omega) (by omega)] at h
  xs 0x27e9 (.push [0x07, 0xe0] (by decide)) ri_push
  xmo 0x27ea (.reg .mstore) (ri_mstore_imgAt (o := 0x7e0) rfl)
  xs 0x27ed (.push [0x01, 0x40] (by decide)) ri_push
  xs 0x27f0 (.push [0x07, 0xe0] (by decide)) ri_push
  xmo 0x27f1 (.reg .mload) (ri_mload_imgAt (o := 0x7e0) rfl)
  rw [(WordAt.write_self _ _ _).read] at h
  xs 0x27f2 (.reg .lt) ri_lt
  xs 0x27f3 (.reg .iszero) ri_iszero
  xs 0x27f4 (.reg .iszero) ri_iszero
  xs 0x27f7 (.push [0x27, 0xfc] (by decide)) ri_push
  xji 0x27f8 0x27fc hw
  · have hge : ¬ q - 32 < 0x140 := (ex_ltCheck (q := 0x140) (by omega) (by decide)).mp
      (eqCheck_ne_zero_eq (eqCheck_eq_zero hw))
    xs 0x27fb (.push [0x27, 0xd9] (by decide)) ri_push
    xjmp 0x27d9
    rw [if_neg (by omega)]
    exact ⟨_, _, hR, hW, h⟩
  · have hlt : q - 32 < 0x140 := by
      have e := eqCheck_eq_zero (eqCheck_ne_zero_eq hw)
      by_contra hn
      exact e ((ex_ltCheck (q := 0x140) (by omega) (by decide)).mpr hn)
    xjd 0x27fd
    rw [if_pos (by omega)]
    exact ⟨_, _, hR, hW, h⟩

/-- **The frame restore** (`0x27d9` → `0x27fd`). -/
theorem xa_ex_restore {sevm : Sevm} {post : Devm} {L : List Exec.Frame} (hcode : sevm.code = code)
    (w : Nat → B256) (k : Nat) :
    ∀ {b : Devm} {S : List B256} {M : Mem} {img : Bytes} {G : Nat},
    Mem.Reads M img → Mem.Wf M → 0x140 + 32 * (k + 1) ≤ 0x7e0 →
    WordAt img 0x7e0 (Nat.toB256 (0x140 + 32 * k)) →
    XAt sevm post 0x27d9 (St b (exSaved w 0x140 (k + 1) ++ S) M G) L →
    ∃ M' img' G', Mem.Reads M' img' ∧ Mem.Wf M' ∧
      (∀ m, m < k + 1 → WordAt img' (0x140 + 32 * m) (w (0x140 + 32 * m))) ∧
      (∀ o v, WordAt img o v →
        o + 32 ≤ 0x140 ∨ (0x140 + 32 * (k + 1) ≤ o ∧ o + 32 ≤ 0x7e0) ∨ 0x800 ≤ o →
        WordAt img' o v) ∧
      XAt sevm post 0x27fd (St b S M' G') L := by
  induction k with
  | zero =>
    intro b S M img G hR hW hk hctr h
    obtain ⟨M', G', hR', hW', h'⟩ := xa_ex_restoreStep hcode hR hW (v := w 0x140) (by omega)
      (by omega) hctr h
    rw [if_pos (by decide)] at h'
    refine ⟨M', _, G', hR', hW', fun m hm => ?_, fun o v hov ho => ?_, h'⟩
    · obtain rfl : m = 0 := by omega
      exact (WordAt.write_self _ _ _).write_other (by simp only [B256.length_toBytes]; omega)
    · exact (hov.write_other (by simp only [B256.length_toBytes]; omega)).write_other
        (by simp only [B256.length_toBytes]; omega)
  | succ k ih =>
    intro b S M img G hR hW hk hctr h
    rw [exSaved_succ, List.cons_append] at h
    obtain ⟨M1, G1, hR1, hW1, h1⟩ := xa_ex_restoreStep hcode hR hW (by omega) (by omega) hctr h
    rw [if_neg (by omega)] at h1
    obtain ⟨M2, img2, G2, hR2, hW2, hm2, hk2, h2⟩ := ih hR1 hW1 (by omega)
      (by rw [show 0x140 + 32 * (k + 1) - 32 = 0x140 + 32 * k by omega]
          exact WordAt.write_self _ _ _) h1
    refine ⟨M2, img2, G2, hR2, hW2, fun m hm => ?_, fun o v hov ho => ?_, h2⟩
    · by_cases e : m = k + 1
      · subst e
        exact hk2 _ _ ((WordAt.write_self _ _ _).write_other
          (by simp only [B256.length_toBytes]; omega)) (.inr (.inl ⟨by omega, by omega⟩))
      · exact hm2 m (by omega)
    · exact hk2 o v ((hov.write_other (by simp only [B256.length_toBytes]; omega)).write_other
        (by simp only [B256.length_toBytes]; omega)) (by omega)

end Blanc.Lift.Curve3Pool
