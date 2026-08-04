-- Solvent.lean : proof of solvency for WETH implementation


import Blanc.CommonProofs
import Blanc.Weth
import Blanc.Ladder
import Std.Data.TreeMap.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Blanc

open Jaune

def Stor.rest (s : Stor) : Adr → B256 := s.get ∘ Adr.toB256

-- sum of all WETH balances, provided that s is the storage of WETH contract
def wbsum (s : Stor) : Nat := sum (Stor.rest s)

def Stor.Solvent (s : Stor) (v : B256) (b : B256) : Prop :=
  wbsum s + v.toNat ≤ b.toNat

def State.Solvent (w : State) (a : Adr) : Prop :=
  Stor.Solvent (w.getStor a) 0 (w.bal a)

def Devm.PreSolvent (devm : Devm) (a : Adr) (sevm : Sevm) : Prop :=
  (sevm.currentTarget = a → Stor.Solvent (Devm.getStor devm a) sevm.value (devm.getBal a)) ∧
  (sevm.currentTarget ≠ a → Stor.Solvent (Devm.getStor devm a) 0 (devm.getBal a))

def Devm.PostSolvent (devm : Devm) (a : Adr) : Prop :=
  Stor.Solvent (Devm.getStor devm a) 0 (devm.getBal a)

lemma solvent_of_same_stor {s s' : Stor} {v : B256} {b b' : B256} :
    Stor.Solvent s v b → s = s' → b = b' → Stor.Solvent s' v b' := by
  intros h0 h1 h2; rw [h1, h2] at h0; exact h0

lemma solvent_zero_of_solvent {s : Stor} {v : B256} {b : B256}
    (h : Stor.Solvent s v b) : Stor.Solvent s 0 b := by
  simp [Stor.Solvent] at h
  simp [Stor.Solvent, B256.toNat_zero]
  omega

structure Precond (wa : Adr) (sevm : Sevm) (devm : Devm) : Prop where
  (code : some (devm.getCode wa).toList = Prog.compile weth)
  (nof : sum devm.getBal < 2 ^ 256)
  (solvent : Devm.PreSolvent devm wa sevm)

structure Postcond (wa : Adr) (sevm : Sevm) (devm : Devm) : Prop where
  (nof : sum devm.getBal < 2 ^ 256)
  (solvent : Devm.PostSolvent devm wa)


-- The WETH invariant on a bare world state, as it stands between
-- transactions and blocks (no active call frame).
structure State.Inv (wa : Adr) (w : Jaune.State) : Prop where
  (code : some (w.getCode wa).toList = Prog.compile weth)
  (nof : Blanc.SumNof w.bal)
  (solvent : State.Solvent w wa)

/-! ## Instance 1 — WETH

Every slot is discharged from a lemma that already exists in `Solvent.lean`,
or from the arithmetic those lemmas' own proofs already perform.  No new proof
content: this is repackaging. -/

/-- `Stor.Solvent` in the record's argument order — it already is. -/
def wethSpec : ContractSpec where
  prog := weth
  Inv := Stor.Solvent
  Side := SumNof
  inv_forget := solvent_zero_of_solvent
  inv_mono := by
    intro s v b b' h hle
    unfold Stor.Solvent at h ⊢; omega
  inv_recv := by
    intro s v b b' h heq
    unfold Stor.Solvent at h ⊢
    rw [B256.toNat_zero] at h; omega
  side_le := by
    intro f g h hle
    unfold SumNof at h ⊢; omega
  side_transfer := by
    intro st st' caller callee wad h_sub h_side
    have h_nof : sum st.bal < 2 ^ 256 := h_side
    rcases of_state_transfer (callee := callee) h_sub h_nof with ⟨-, -, h_sum, -, -, -⟩
    show sum _ < 2 ^ 256
    rw [h_sum]; exact h_nof
  side_addBal := by
    intro w a val h_bound _
    show sum _ < 2 ^ 256
    rw [sum_addBal_eq w a val h_bound]; omega
  inv_transfer := by
    intro st st' caller callee ca wad v h_sub h_ne h_side h_inv
    have h_nof : sum st.bal < 2 ^ 256 := h_side
    rcases of_state_transfer (callee := callee) h_sub h_nof with
      ⟨h_t_stor, -, -, h_t_le, -, -⟩
    have h_mid : st'.bal ca = st.bal ca := by
      rcases State.of_subBal h_sub with ⟨-, h_st'⟩
      rw [h_st']
      show ((st.setBal caller _).get ca).bal = (st.get ca).bal
      rw [State.setBal_get_ne h_ne]
    have h_stor : (st'.addBal callee wad).getStor ca = st.getStor ca := h_t_stor ca
    have h_ge : (st.bal ca).toNat ≤ ((st'.addBal callee wad).bal ca).toNat := by
      by_cases h_eq : callee = ca
      · have h_add : (st'.addBal callee wad).bal ca = st.bal ca + wad := by
          rw [h_eq]
          show ((st'.setBal ca (st'.bal ca + wad)).get ca).bal = _
          rw [State.setBal_get_self]
          show st'.bal ca + wad = _
          rw [h_mid]
        rw [h_add]
        have h_le_wad : wad.toNat ≤ (st.bal caller).toNat := B256.toNat_le_toNat h_t_le
        have h_two : (st.bal ca).toNat + (st.bal caller).toNat ≤ sum st.bal :=
          add_le_sum_of_ne st.bal (fun hc => h_ne hc.symm)
        have h_nof' : B256.Nof (st.bal ca) wad := by unfold B256.Nof; omega
        rw [B256.toNat_add_eq_of_nof _ _ h_nof']
        omega
      · have h_other : (st'.addBal callee wad).bal ca = st.bal ca := by
          show ((st'.setBal callee _).get ca).bal = _
          rw [State.setBal_get_ne h_eq]
          exact h_mid
        rw [h_other]
    rw [h_stor]
    unfold Stor.Solvent at h_inv ⊢
    omega
  inv_recv_transfer := by
    intro st st' caller ca wad h_sub h_ne h_side h_inv
    have h_nof : sum st.bal < 2 ^ 256 := h_side
    rcases of_state_transfer (callee := ca) h_sub h_nof with ⟨h_t_stor, -, -, -, -, -⟩
    have h_stor : (st'.addBal ca wad).getStor ca = st.getStor ca := h_t_stor ca
    have h_bal : ((st'.addBal ca wad).bal ca).toNat = (st.bal ca).toNat + wad.toNat :=
      of_transfer_bal_target h_sub h_ne h_nof
    rw [h_stor]
    unfold Stor.Solvent at h_inv ⊢
    rw [B256.toNat_zero] at h_inv
    omega
  inv_addBal := by
    intro w ca a val v h_bound _ h_inv
    have h_nof_a : B256.Nof (w.bal a) val := by
      unfold B256.Nof; have := @le_sum w.bal a; omega
    have h_stor : (w.addBal a val).getStor ca = w.getStor ca := by
      show ((w.setBal a _).get ca).stor = (w.get ca).stor
      rw [State.setBal_get_stor]
    have h_ge : (w.bal ca).toNat ≤ ((w.addBal a val).bal ca).toNat := by
      by_cases h_eq : a = ca
      · subst h_eq
        show (w.bal a).toNat ≤ ((w.setBal a (w.bal a + val)).get a).bal.toNat
        rw [State.setBal_get_self]
        change (w.bal a).toNat ≤ (w.bal a + val).toNat
        rw [B256.toNat_add_eq_of_nof _ _ h_nof_a]; omega
      · show (w.bal ca).toNat ≤ ((w.setBal a _).get ca).bal.toNat
        rw [State.setBal_get_ne h_eq]; exact Nat.le_refl _
    rw [h_stor]
    unfold Stor.Solvent at h_inv ⊢
    omega

/-! ### The record reproduces the WETH bundles exactly

These three bridges are the evidence that `ContractSpec` is the interface the
existing statements consume: each generic bundle is interderivable with the
WETH-specific one it is meant to replace, field by field, with no side
conditions. -/

theorem wethSpec_pre_iff {ca : Adr} {sevm : Sevm} {devm : Devm} :
    wethSpec.Pre ca sevm devm ↔ Precond ca sevm devm :=
  ⟨fun h => ⟨h.code, h.side, h.inv⟩, fun h => ⟨h.code, h.nof, h.solvent⟩⟩

theorem wethSpec_post_iff {ca : Adr} {sevm : Sevm} {devm : Devm} :
    wethSpec.Post ca sevm devm ↔ Postcond ca sevm devm :=
  ⟨fun h => ⟨h.side, h.inv⟩, fun h => ⟨h.nof, h.solvent⟩⟩

theorem wethSpec_stateInv_iff {ca : Adr} {w : Jaune.State} :
    wethSpec.StateInv ca w ↔ State.Inv ca w :=
  ⟨fun h => ⟨h.code, h.side, h.inv⟩, fun h => ⟨h.code, h.nof, h.solvent⟩⟩

/-! The same three facts as equations between predicates.  They are what lets an
audited WETH theorem be stated exactly as before and proved by instantiating
its generic parent: `simpa only [...] using ContractSpec.foo wethSpec ...`. -/

theorem wethSpec_prog_eq : wethSpec.prog = weth := rfl

theorem wethSpec_pre_eq : wethSpec.Pre = Precond := by
  funext ca sevm devm; exact propext wethSpec_pre_iff

theorem wethSpec_post_eq : wethSpec.Post = Postcond := by
  funext ca sevm devm; exact propext wethSpec_post_iff

theorem wethSpec_stateInv_eq : wethSpec.StateInv = State.Inv := by
  funext ca w; exact propext wethSpec_stateInv_iff

/-! ### WETH instances of the hoisted frame-level ladder

Each is the corresponding `ContractSpec` lemma at `wethSpec`, transported by the
bridges above.  Only the ones the WETH-specific material below still consumes
remain; the rest moved up with their consumers. -/

lemma Precond.state_eq {wa sevm devm devm'}
    (h_pc : Precond wa sevm devm) (h_eq : devm'.state = devm.state) :
    Precond wa sevm devm' :=
  wethSpec_pre_iff.mp ((wethSpec_pre_iff.mpr h_pc).state_eq h_eq)



lemma Line.preserves_solvent {e e' s l s' a}
    (h_bal : Line.Inv Devm.getBal l) (h_stor : Line.Inv Devm.getStor l)
    (h_sv : Devm.PreSolvent s a e) (h_run : Line.Run e' s l s') : Devm.PreSolvent s' a e := by
  unfold Devm.PreSolvent; rw [← h_bal h_run, ← h_stor h_run]; exact h_sv



syntax "simple_solvent" : tactic
set_option hygiene false in
macro_rules
| `(tactic| simple_solvent) =>
  `(tactic| revert h_sv; simp [Devm.PostSolvent, Devm.PreSolvent]; intro h_sv;
            apply solvent_zero_of_solvent;
            apply solvent_of_same_stor h_sv <;>
            apply congr_fun <| Func.of_inv _ _ (by func_inv) run )

lemma name_preserves_solvent {sevm : Sevm} {s r : Devm}
    (run : Func.Run (weth.main :: weth.aux) sevm s name r)
    (h_sv : Devm.PreSolvent s sevm.currentTarget sevm) :
    Devm.PostSolvent r sevm.currentTarget := by simple_solvent

lemma approve_preserves_bal : Func.Inv Devm.getBal Devm.getBal approve := by func_inv

def ValidAdr (w : B256) : Prop := ∃ a : Adr, a.toB256 = w

theorem validAdr_toB256 (a : Adr) : ValidAdr a.toB256 := ⟨a, rfl⟩

lemma toB256_toAdr {w : B256} :
    ValidAdr w → w.toAdr.toB256 = w := by
  intro h; rcases h with ⟨a, ha⟩;
  rw [← ha, toAdr_toB256]

lemma cons_pref_cons_inv {α} {x : α} {xs ys : List α} (h : (x :: xs) <<+ (x :: ys)) : xs <<+ ys := by
  rcases h with ⟨zs, h⟩
  injection h with _ h_tail
  exact ⟨zs, h_tail⟩

open Lean.Elab.Tactic
open Lean.Parser.Tactic
open Lean.Elab.Term
open Lean
open Qq
open Jaune.Ninst Ninst

def Line.take : Nat → Q(Line) → TacticM Q(Line)
| 0, _ => pure q([] : Line)
| n + 1, l => do
  let l' : Q(Line) ← Lean.Meta.whnf l
  match l' with
  | ~q([]) => failure
  | ~q($i :: $is) =>
    let x ← Line.take n is
    pure q($i :: $x)
  | _ => failure

elab "line_execute" e:num : tactic =>
  withMainContext do
    let n := Lean.TSyntax.getNat e
    let g : Q(Prop) ← getMainTarget
    match g with
    | ~q(Line.Run _ $s $l _ → $c) =>
      let ss ← findSubscript s
      let x ← Line.take n l
      Lean.Expr.apply (Lean.mkApp2 q(@run_append_elim) c x)
      Strings.intro ["s" ++ ss, "h" ++ ss]
    | _ => throwError "unexpected goal for line_execute"

elab "line_execute_with" e:term : tactic =>
  withMainContext do
    let x ← elabTermForApply e
    let g : Q(Prop) ← getMainTarget
    match g with
    | ~q(Line.Run _ $s _ _ → $c) =>
      let ss ← findSubscript s
      Lean.Expr.apply (Lean.mkApp2 q(@run_append_elim) c x)
      Strings.intro ["s" ++ ss, "h" ++ ss]
    | _ => throwError "unexpected goal for line_execute_with"

def addressMask : B256 := ⟨⟨.max, 0xffffffff00000000⟩, 0⟩

lemma B128.and_eq_and_prod_and (x y : B128) :
    x &&& y = ⟨x.1 &&& y.1, x.2 &&& y.2⟩ := rfl

lemma B256.and_eq_and_prod_and (x y : B256) :
    x &&& y = ⟨x.1 &&& y.1, x.2 &&& y.2⟩ := rfl

lemma B128.zero_and {x : B128} : 0 &&& x = 0 := by
  simp [B128.and_eq_and_prod_and]
  apply Prod.ext <;> change (0 : UInt64) &&& _ = 0 <;> apply UInt64.zero_and

lemma UInt64.mask_and_eq_zero (x : UInt32) :
    (0xffffffff00000000 : UInt64) &&& x.toUInt64 = 0 := by
  rw [← @UInt32.and_neg_one x, UInt32.toUInt64_and]
  rw [UInt64.and_comm (UInt32.toUInt64 _), ← UInt64.and_assoc]
  apply UInt64.zero_and

lemma UInt64.toUInt32_toUInt64_eq_of_highMask_and_eq_zero {x : UInt64}
    (h : (0xffffffff00000000 : UInt64) &&& x = 0) :
    x.toUInt32.toUInt64 = x := by
  apply UInt64.toBitVec_inj.mp
  simp only [UInt32.toBitVec_toUInt64, UInt64.toBitVec_toUInt32]
  apply BitVec.eq_of_getElem_eq_iff.mpr
  intro i hi
  rw [BitVec.getElem_setWidth]
  by_cases hi32 : i < 32
  · rw [BitVec.getLsbD_eq_getElem hi32, BitVec.getElem_setWidth,
      BitVec.getLsbD_eq_getElem (by omega)]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]
    have hb := congrArg UInt64.toBitVec h
    rw [UInt64.toBitVec_and, UInt64.toBitVec_zero] at hb
    have hb_i := congrArg (fun v : BitVec 64 => v[i]) hb
    simp only [BitVec.getElem_and hi, BitVec.getElem_zero hi] at hb_i
    have hmask : ((0xffffffff00000000 : UInt64).toBitVec)[i] = true := by
      change (((-1 : UInt64) <<< 32).toBitVec)[i] = true
      rw [UInt64.toBitVec_shiftLeft, BitVec.getElem_shiftLeft' hi]
      simp [hi32]
      change (BitVec.allOnes 64)[i - 32] = true
      rw [BitVec.getElem_eq_testBit_toNat _ _ (by omega), BitVec.toNat_allOnes]
      rw [Nat.testBit_two_pow_sub_succ (x := 0) (by norm_num)]
      have hi64 : i - 32 < 64 := by omega
      simp [hi64]
    rw [hmask] at hb_i
    exact hb_i.symm

lemma validAdr_iff {w : B256} :
    ValidAdr w ↔ addressMask &&& w = 0 := by
  constructor <;> intro h
  · rcases h with ⟨⟨a32, a128⟩, ⟨_⟩⟩
    simp [Adr.toB256, addressMask]
    rw [B256.and_eq_and_prod_and]
    simp [B128.zero_and]
    rw [B128.and_eq_and_prod_and]
    simp
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply UInt64.mask_and_eq_zero
    · rfl
  · refine' ⟨w.toAdr, _⟩
    rcases w with ⟨⟨wz, wh⟩, wl⟩
    simp only [addressMask, B256.and_eq_and_prod_and, B128.and_eq_and_prod_and] at h
    have hz := congrArg (fun x : B256 => x.1.1) h
    have hm := congrArg (fun x : B256 => x.1.2) h
    change UInt64.max &&& wz = 0 at hz
    change (0xffffffff00000000 : UInt64) &&& wh = 0 at hm
    have h_wz : wz = 0 := by
      simp only [UInt64.max] at hz
      change (-1 : UInt64) &&& wz = 0 at hz
      simpa using hz
    have h_wh : wh.toUInt32.toUInt64 = wh := by
      exact UInt64.toUInt32_toUInt64_eq_of_highMask_and_eq_zero hm
    simp only [B256.toAdr, Adr.toB256, h_wz, h_wh]

lemma addressMask_eq_shl :
    addressMask = (~~~ (0 : B256)) <<< (160 : Nat).toB256.toNat := by
  rw [B256.toNat_toB256, Nat.lo_eq_of_lt (by omega)]; rfl

lemma of_push_addressMask {e : Sevm} {s s' : Devm} {xs}
    (h_pfx : xs <<+ s.stack) (h_run : Line.Run e s pushAddressMask s') :
    (addressMask :: xs <<+ s'.stack) := by
  rw [addressMask_eq_shl]
  revert s; simp only [pushAddressMask]; line_prefix

lemma of_check_non_address {e : Sevm} {s s' : Devm} {x xs}
    (h_pfx : x :: xs <<+ s.stack) (h_run : Line.Run e s checkNonAddress s') :
    ∃ y, (y :: xs <<+ s'.stack) ∧ (y = 0 ↔ ValidAdr x) := by
  rename' s' => s''
  rcases of_run_append _ h_run with ⟨sm, h_push, h_and⟩; clear h_run
  have h_pfx' := of_push_addressMask h_pfx h_push; clear h_pfx h_push s
  have h_pfx2 : (addressMask &&& x) :: xs <<+ s''.stack := by
    revert h_and; revert sm; line_prefix
  refine ⟨_, h_pfx2, Iff.symm validAdr_iff⟩

lemma of_check_address {e : Sevm} {s s' : Devm} {x xs} :
    (x :: xs <<+ s.stack) →
    Line.Run e s checkAddress s' →
    ∃ y, (y :: xs <<+ s'.stack) ∧ (y = 0 ↔ ¬ ValidAdr x) := by
  rename' s' => s''; intros h_pfx h_run
  rcases of_run_append _ h_run with ⟨sm, hs', h_run'⟩; clear h_run
  rcases of_check_non_address h_pfx hs' with ⟨y, h_pfx', h_iff⟩; clear h_pfx hs' s
  have h_pfx2 : ((y =? 0) :: xs <<+ s''.stack) := by
    revert h_run'; revert sm; line_prefix
  refine' ⟨_, h_pfx2, _⟩; rw [← h_iff]
  apply Ne.ite_eq_right_iff <| Ne.symm B256.zero_ne_one

lemma of_prepApprove {sevm : Sevm} {s s' : Devm} :
    Line.Run sevm s prepApprove s' →
    ∃ vx x y, ([vx, x, y] <<+ s'.stack) ∧ (vx = 0 ↔ ¬ ValidAdr x) := by
  line_execute 7
  have hp₀ : [] <<+ s₁.stack := nil_pref
  clear_state s
  line_execute 2
  rcases prefix_of_cdl hp₀ h₂ with ⟨wad, hp₁⟩
  clear_state s₁
  line_execute 2
  have hp₂ : [0, 64, wad] <<+ s₃.stack := by generalize_line_prefix
  clear_state s₂
  line_execute 1
  rcases prefix_of_kec (of_run_singleton h₄) hp₂ with ⟨hash, hp₃⟩
  clear_state s₃
  line_execute 1
  have hp₄ : [hash, hash, wad] <<+ s₅.stack := by generalize_line_prefix
  clear_state s₄
  intro h
  rcases of_check_address hp₄ h with ⟨vx, h_vx, h_iff⟩
  refine ⟨vx, hash, wad, h_vx, h_iff⟩



lemma setStorVal_getStor_self {devm : Devm} {adr : Adr} {key val : B256} :
    Devm.getStor (devm.setStorVal adr key val) adr = (Devm.getStor devm adr).set key val := by
  simp only [Devm.getStor, Devm.getAcct, Devm.setStorVal, Devm.withState,
    Devm.setWorld, State.setStorVal]
  simp only [Devm.state, State.get_set_self]

lemma sstore_getStor_setStorVal {sevm : Sevm} {s s' : Devm} {x xs}
    (h_run : Ninst.Run sevm s Blanc.Ninst.sstore s') (hx : x :: xs <<+ s.stack) :
    ∃ v, Devm.getStor s' sevm.currentTarget = (Devm.getStor s sevm.currentTarget).set x v := by
  rcases of_run_reg h_run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨key, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨val, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨_, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨⟨s₃, g₂⟩, h4, run₄⟩
  rcases Except.bind_eq_ok run₄ with ⟨g₃, h5, run₅⟩
  rcases Except.bind_eq_ok run₅ with ⟨s₄, h6, run₆⟩
  rcases Except.bind_eq_ok run₆ with ⟨s₅, h7, run₇⟩
  rcases Except.bind_eq_ok run₇ with ⟨_, h8, h9⟩
  have hkx : x = key :=
    (List.of_cons_pref_of_cons_pref hx (pref_of_split (Devm.pop_of_pop h1).stack)).left
  have e1 : Devm.getStor s = Devm.getStor s₁ := Devm.pop_getStor_eq h1
  have e2 : Devm.getStor s₁ = Devm.getStor s₂ := Devm.pop_getStor_eq h2
  have e4 : Devm.getStor s₂ = Devm.getStor s₃ := by
    split at h4 <;> (injection h4 with eq; injection eq with eq _; subst eq)
    · exact addAccessedStorageKey_getStor.symm
    · rfl
  have e6 : Devm.getStor s₃ = Devm.getStor s₄ := by
    injection h6 with eq; rw [← eq]; rfl
  have e7 : Devm.getStor s₄ = Devm.getStor s₅ := chargeGas_getStor_eq h7
  have E : Devm.getStor s = Devm.getStor s₅ := e1.trans (e2.trans (e4.trans (e6.trans e7)))
  injection h9 with eq
  refine ⟨val, ?_⟩
  rw [← eq, setStorVal_getStor_self, hkx, E]

lemma sstore_preserves_stor_rest {x xs} {sevm : Sevm} {s s' : Devm} :
  ¬ ValidAdr x →
  (x :: xs <<+ s.stack) →
  Ninst.Run sevm s Blanc.Ninst.sstore s' →
  (Stor.rest (Devm.getStor s sevm.currentTarget)) = (Stor.rest (Devm.getStor s' sevm.currentTarget)) := by
  intro h_nv h_pfx h_run
  rcases sstore_getStor_setStorVal h_run h_pfx with ⟨v, h_set⟩
  rw [h_set]
  funext a
  have hne : a.toB256 ≠ x := fun hc => h_nv ⟨a, hc⟩
  simp only [Stor.rest, Function.comp_apply]
  rw [Stor.get_set_ne _ hne.symm]

lemma sstore_getStor_set {sevm : Sevm} {s s' : Devm} {x y xs}
    (h_run : Ninst.Run sevm s Blanc.Ninst.sstore s') (hx : x :: y :: xs <<+ s.stack) :
    Devm.getStor s' sevm.currentTarget = (Devm.getStor s sevm.currentTarget).set x y := by
  rcases of_run_reg h_run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨key, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨val, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨_, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨⟨s₃, g₂⟩, h4, run₄⟩
  rcases Except.bind_eq_ok run₄ with ⟨g₃, h5, run₅⟩
  rcases Except.bind_eq_ok run₅ with ⟨s₄, h6, run₆⟩
  rcases Except.bind_eq_ok run₆ with ⟨s₅, h7, run₇⟩
  rcases Except.bind_eq_ok run₇ with ⟨_, h8, h9⟩
  have hs : s.stack = key :: s₁.stack := (Devm.pop_of_pop h1).stack
  have hs2 : s₁.stack = val :: s₂.stack := (Devm.pop_of_pop h2).stack
  have hxy : x = key ∧ y = val := by
    rw [hs, hs2] at hx
    rcases hx with ⟨sfx, heq⟩
    injection heq with hk hrest
    injection hrest with hv _
    exact ⟨hk.symm, hv.symm⟩
  have e1 : Devm.getStor s = Devm.getStor s₁ := Devm.pop_getStor_eq h1
  have e2 : Devm.getStor s₁ = Devm.getStor s₂ := Devm.pop_getStor_eq h2
  have e4 : Devm.getStor s₂ = Devm.getStor s₃ := by
    split at h4 <;> (injection h4 with eq; injection eq with eq _; subst eq)
    · exact addAccessedStorageKey_getStor.symm
    · rfl
  have e6 : Devm.getStor s₃ = Devm.getStor s₄ := by
    injection h6 with eq; rw [← eq]; rfl
  have e7 : Devm.getStor s₄ = Devm.getStor s₅ := chargeGas_getStor_eq h7
  have E : Devm.getStor s = Devm.getStor s₅ := e1.trans (e2.trans (e4.trans (e6.trans e7)))
  injection h9 with eq
  rw [← eq, setStorVal_getStor_self, hxy.left, hxy.right, E]

syntax "invariance" : tactic
macro_rules
| `(tactic| invariance) =>
  `(tactic| first | apply Line.of_inv _ _ (by assumption); line_inv
                  | apply Func.of_inv _ _ _ (by assumption); func_inv)

lemma of_run_next {fs sevm devm i f devm''}
    (h : Func.Run fs sevm devm (Func.next i f) devm'') :
    ∃ devm', Ninst.Run sevm devm i devm' ∧ Func.Run fs sevm devm' f devm'' := by
  cases h with
  | next h1 h2 => exact ⟨_, h1, h2⟩

lemma of_withdrawLoadCheck {sevm : Sevm} {s s' : Devm}
    (h : Line.Run sevm s withdrawLoadCheck s') :
    s.getBal = s'.getBal ∧
    Devm.getStor s = Devm.getStor s' ∧
    s.getCode = s'.getCode ∧
    ∃ wad cbal, ([cbal <? wad, cbal, wad, wad] <<+ s'.stack) ∧
      (cbal = Devm.getStorVal s' sevm.currentTarget sevm.caller.toB256) := by
  refine ⟨by invariance, by invariance, by invariance, ?_⟩
  revert h
  line_execute 2
  rcases prefix_of_cdl nil_pref h₁ with ⟨wad, hp₁⟩
  clear_state s
  line_execute 2
  have hp₂ : [sevm.caller.toB256, wad, wad] <<+ s₂.stack := by generalize_line_prefix
  clear_state s₁
  line_execute 1
  rcases prefix_of_sload (of_run_singleton h₃) hp₂ with ⟨cbal, hp₃, h_cbal⟩
  have hstor3 : Devm.getStorVal s₂ sevm.currentTarget sevm.caller.toB256
              = Devm.getStorVal s₃ sevm.currentTarget sevm.caller.toB256 := by
    show (Devm.getStor s₂ _).get _ = (Devm.getStor s₃ _).get _
    rw [Line.of_inv Devm.getStor (by line_inv) h₃]
  rw [hstor3] at h_cbal
  clear_state s₂
  intro h₄
  have hp₄ : [cbal <? wad, cbal, wad, wad] <<+ s'.stack := by generalize_line_prefix
  have hstor4 : Devm.getStorVal s₃ sevm.currentTarget sevm.caller.toB256
              = Devm.getStorVal s' sevm.currentTarget sevm.caller.toB256 := by
    show (Devm.getStor s₃ _).get _ = (Devm.getStor s' _).get _
    rw [Line.of_inv Devm.getStor (by line_inv) h₄]
  rw [hstor4] at h_cbal
  exact ⟨wad, cbal, hp₄, h_cbal⟩

lemma approve_preserves_wbal {sevm : Sevm} {s r : Devm}
    (run : Func.Run (weth.main :: weth.aux) sevm s approve r) :
    (Stor.rest (Devm.getStor s sevm.currentTarget)) = (Stor.rest (Devm.getStor r sevm.currentTarget)) := by
  rcases of_run_prepend (arg 0 ++ checkNonAddress) _ run
    with ⟨s0, h_s0, h_run'⟩; clear run
  have h_s0_stor_eq : Devm.getStor s = Devm.getStor s0 := by invariance
  have h_s0_stor : Devm.getStor s sevm.currentTarget = Devm.getStor s0 sevm.currentTarget :=
    congr_fun h_s0_stor_eq sevm.currentTarget
  rw [h_s0_stor]; clear h_s0_stor h_s0_stor_eq h_s0 s
  rcases of_run_branch_rev h_run' with ⟨s1, h_pop, h_run⟩; clear h_run'
  have h_s1_stor : Devm.getStor s0 sevm.currentTarget = Devm.getStor s1 sevm.currentTarget :=
    (Devm.PopBurn.getStor h_pop sevm.currentTarget).symm
  rw [h_s1_stor]; clear h_s1_stor h_pop s0
  rcases of_run_prepend prepApprove _ h_run
    with ⟨s2, h_s2, h_run'⟩; clear h_run
  rcases of_prepApprove h_s2
    with ⟨hash_valid, hash, wad, h_s2_stk, h_iff⟩
  have h_s2_stor_eq : Devm.getStor s1 = Devm.getStor s2 := by invariance
  have h_s2_stor : Devm.getStor s1 sevm.currentTarget = Devm.getStor s2 sevm.currentTarget :=
    congr_fun h_s2_stor_eq sevm.currentTarget
  rw [h_s2_stor]; clear h_s2_stor h_s2_stor_eq h_s2 s1
  rcases of_run_branch_rev h_run' with ⟨s3, h_pop, h_run⟩; clear h_run'
  have h_hv_eq_zero : hash_valid = 0 := by
    have h_pop_stk := h_pop.stack
    simp [Stack.Pop, Split] at h_pop_stk
    have h_s2_pref : [0] <<+ s2.stack := by
      rw [h_pop_stk]
      exact pref_append _ _
    exact pref_head_unique h_s2_stk h_s2_pref
  rw [h_hv_eq_zero] at h_s2_stk
  simp [h_hv_eq_zero] at h_iff
  clear h_hv_eq_zero hash_valid
  have h_s3_stk : [hash, wad] <<+ s3.stack := by
    have h_pop_stk := h_pop.stack
    simp [Stack.Pop, Split] at h_pop_stk
    rw [h_pop_stk] at h_s2_stk
    exact cons_pref_cons_inv h_s2_stk
  clear h_s2_stk
  have h_s3_stor : Devm.getStor s2 sevm.currentTarget = Devm.getStor s3 sevm.currentTarget :=
    (Devm.PopBurn.getStor h_pop sevm.currentTarget).symm
  rw [h_s3_stor]; clear h_s3_stor h_pop s2
  rcases of_run_next h_run with ⟨s4, h_sstore, h_run'⟩; clear h_run
  have hh := sstore_preserves_stor_rest h_iff h_s3_stk h_sstore
  have h_r_stor_eq : Devm.getStor s4 = Devm.getStor r := by
    apply Func.of_inv Devm.getStor Devm.getStor _ h_run'
    func_inv
  have h_r_stor : Devm.getStor s4 sevm.currentTarget = Devm.getStor r sevm.currentTarget :=
    congr_fun h_r_stor_eq sevm.currentTarget
  rw [← h_r_stor]
  apply hh

lemma result_solvent_of_state_solvent {sevm : Sevm} {s r : Devm}
    (h_wbsum : (Stor.rest (Devm.getStor s sevm.currentTarget)) = (Stor.rest (Devm.getStor r sevm.currentTarget)))
    (h_bal : s.getBal sevm.currentTarget = r.getBal sevm.currentTarget)
    (h_solvent : Devm.PreSolvent s sevm.currentTarget sevm) :
    Devm.PostSolvent r sevm.currentTarget := by
  unfold Devm.PostSolvent Stor.Solvent
  rw [B256.toNat_zero, Nat.add_zero]
  have h_sv' := h_solvent.left rfl
  unfold Stor.Solvent at h_sv'
  rw [← h_bal]
  have h_wbsum_eq : wbsum (Devm.getStor s sevm.currentTarget) = wbsum (Devm.getStor r sevm.currentTarget) := by
    simp [wbsum, h_wbsum]
  rw [← h_wbsum_eq]
  omega

lemma approve_preserves_solvent {sevm : Sevm} {s r : Devm}
    (run : Func.Run (weth.main :: weth.aux) sevm s approve r)
    (h_sv : Devm.PreSolvent s sevm.currentTarget sevm) :
    Devm.PostSolvent r sevm.currentTarget := by
  have h_bal_fun := Func.of_inv Devm.getBal Devm.getBal approve_preserves_bal run
  have h_bal := congr_fun h_bal_fun sevm.currentTarget
  exact result_solvent_of_state_solvent (approve_preserves_wbal run) h_bal h_sv

lemma totalSupply_preserves_solvent {sevm : Sevm} {s r : Devm}
    (run : Func.Run (weth.main :: weth.aux) sevm s totalSupply r)
    (h_sv : Devm.PreSolvent s sevm.currentTarget sevm) :
    Devm.PostSolvent r sevm.currentTarget := by simple_solvent


lemma deposit_preserves_bal : Func.Inv Devm.getBal Devm.getBal deposit := by func_inv

lemma wbsum_after_deposit {sevm : Sevm} {s r : Devm}
    (h_nof : wbsum (Devm.getStor s sevm.currentTarget) + sevm.value.toNat < 2 ^ 256)
    (run : Func.Run (weth.main :: weth.aux) sevm s deposit r) :
    wbsum (Devm.getStor s sevm.currentTarget) + sevm.value.toNat = wbsum (Devm.getStor r sevm.currentTarget) := by
  unfold deposit at run
  rcases of_run_next run with ⟨s1, h_caller, run1⟩
  rcases of_run_next run1 with ⟨s2, h_sload, run2⟩
  rcases of_run_next run2 with ⟨s3, h_callvalue, run3⟩
  rcases of_run_next run3 with ⟨s4, h_add, run4⟩
  rcases of_run_next run4 with ⟨s5, h_caller2, run5⟩
  rcases of_run_next run5 with ⟨s6, h_sstore, run6⟩
  have hp0 : [] <<+ s.stack := nil_pref
  have hp1 : [sevm.caller.toB256] <<+ s1.stack := prefix_of_push (of_run_caller h_caller) hp0
  have hs1 : Devm.getStor s = Devm.getStor s1 := Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons h_caller Line.Run.nil)

  rcases prefix_of_sload h_sload hp1 with ⟨cbal, hp2, hcbal⟩
  have hs2 : Devm.getStor s1 = Devm.getStor s2 := Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons h_sload Line.Run.nil)

  have hp3 : [sevm.value, cbal] <<+ s3.stack := prefix_of_push (of_run_callvalue h_callvalue) hp2
  have hs3 : Devm.getStor s2 = Devm.getStor s3 := Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons h_callvalue Line.Run.nil)

  have hp4 : [sevm.value + cbal] <<+ s4.stack := prefix_of_add h_add hp3
  have hs4 : Devm.getStor s3 = Devm.getStor s4 := Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons h_add Line.Run.nil)

  have hp5 : [sevm.caller.toB256, sevm.value + cbal] <<+ s5.stack := prefix_of_push (of_run_caller h_caller2) hp4
  have hs5 : Devm.getStor s4 = Devm.getStor s5 := Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons h_caller2 Line.Run.nil)

  have hs_eq : Devm.getStor s = Devm.getStor s5 := by rw [hs1, hs2, hs3, hs4, hs5]
  have hcbal' : cbal = (Devm.getStor s5 sevm.currentTarget).get sevm.caller.toB256 := by
    rw [hcbal]; show (Devm.getStor s1 sevm.currentTarget).get sevm.caller.toB256 = _
    rw [hs2, hs3, hs4, hs5]

  have h_set : Devm.getStor s6 sevm.currentTarget = (Devm.getStor s5 sevm.currentTarget).set sevm.caller.toB256 (sevm.value + cbal) :=
    sstore_getStor_set h_sstore hp5

  have hs6 : Devm.getStor s6 = Devm.getStor r := by apply Func.of_inv _ _ _ run6; func_inv

  have h_incr : Increase sevm.caller sevm.value (Stor.rest (Devm.getStor s5 sevm.currentTarget)) (Stor.rest (Devm.getStor s6 sevm.currentTarget)) := by
    intro a
    constructor
    · intro h_eq
      simp [Stor.rest, ← h_eq, h_set, Stor.get_set_self]
      rw [← hcbal', B256.add_comm]
    · intro h_neq
      simp [Stor.rest, h_set]
      exact (Stor.get_set_ne _ (fun hc => h_neq (Adr.toB256_inj hc)) _).symm

  have h_nof' : B256.Nof ((Stor.rest (Devm.getStor s5 sevm.currentTarget)) sevm.caller) sevm.value := by
    simp only [B256.Nof]
    apply lt_of_le_of_lt _ h_nof
    rw [hs_eq, Nat.add_le_add_iff_right]
    apply le_sum

  rw [hs_eq, ← hs6]
  exact sum_add_assoc h_incr h_nof'

lemma deposit_preserves_solvent {sevm : Sevm} {s r : Devm}
    (run : Func.Run (weth.main :: weth.aux) sevm s deposit r)
    (h_sv : Devm.PreSolvent s sevm.currentTarget sevm) :
    Devm.PostSolvent r sevm.currentTarget := by
  unfold Devm.PostSolvent
  unfold Stor.Solvent
  rw [B256.toNat_zero]
  have h_bal : s.getBal = r.getBal := Func.of_inv _ _ deposit_preserves_bal run
  rw [← h_bal]
  have h_sv' : wbsum (Devm.getStor s sevm.currentTarget) + sevm.value.toNat ≤ (s.getBal sevm.currentTarget).toNat := by
    have h := h_sv.left rfl
    unfold Stor.Solvent at h
    exact h
  have h_lt : wbsum (Devm.getStor s sevm.currentTarget) + sevm.value.toNat < 2 ^ 256 := by
    apply lt_of_le_of_lt h_sv'
    apply B256.toNat_lt
  rw [← wbsum_after_deposit h_lt run]
  rw [Nat.add_zero]
  exact h_sv'


lemma incrAt_of_incrWbal {sevm : Sevm} {s s' : Devm} {wad dst} (h_dst : ValidAdr dst)
    (h_run : Line.Run sevm s incrWbal s') (h_stk : [wad, dst] <<+ s.stack) :
    Increase dst.toAdr wad (Stor.rest (Devm.getStor s sevm.currentTarget)) (Stor.rest (Devm.getStor s' sevm.currentTarget)) := by
  simp only [incrWbal] at h_run
  rcases of_run_append [dup 1, sload, add, swap 0] h_run with ⟨sm, h_pre, h_post⟩
  clear h_run
  have h_stor : Devm.getStor s = Devm.getStor sm := Line.of_inv Devm.getStor (by line_inv) h_pre
  -- decompose the prefix line to track the stack
  rcases Line.of_run_cons h_pre with ⟨s1, r_dup, h1⟩
  rcases Line.of_run_cons h1 with ⟨s2, r_sload, h2⟩
  rcases Line.of_run_cons h2 with ⟨s3, r_add, h3⟩
  rcases Line.of_run_cons h3 with ⟨s4, r_swap, h4⟩
  cases h4
  clear h1 h2 h3 h_pre
  -- dup 1 : push element at index 1 (= dst)
  rcases of_run_dup r_dup with ⟨x, hx, pb_dup⟩
  have hx_dst : x = dst := by
    have h_nth : Stack.Nth 1 dst [wad, dst] :=
      Stack.Nth.tail 0 dst wad [dst] (Stack.Nth.head dst [])
    have h_get : s.stack[(1 : Fin 16).val]? = some dst := Stack.nth_getElem h_nth h_stk
    rw [h_get] at hx; injection hx with hx; exact hx.symm
  subst x
  have hp1 : [dst, wad, dst] <<+ s1.stack := prefix_of_push pb_dup h_stk
  -- sload : pop dst, push its stored value
  rcases prefix_of_sload r_sload hp1 with ⟨dbal, hp2, h_dbal⟩
  -- add : dbal + wad
  have hp3 : (dbal + wad) :: [dst] <<+ s3.stack := prefix_of_add r_add hp2
  -- swap 0 : [dst, dbal + wad]
  have h_swap : Stack.Swap (0 : Fin 16).val [dbal + wad, dst] [dst, dbal + wad] :=
    Stack.swapCore_zero
  have hp4 : [dst, dbal + wad] <<+ sm.stack :=
    Stack.prefix_of_swap h_swap (of_run_swap r_swap) hp3
  -- sstore
  rcases Line.of_run_cons h_post with ⟨s5, r_sstore, h5⟩
  cases h5
  have h_set : Devm.getStor s' sevm.currentTarget
      = (Devm.getStor sm sevm.currentTarget).set dst (dbal + wad) :=
    sstore_getStor_set r_sstore hp4
  -- dbal = value at dst in s's storage
  have hs1 : Devm.getStor s = Devm.getStor s1 :=
    Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r_dup Line.Run.nil)
  have h_dbal' : dbal = (Devm.getStor s sevm.currentTarget).get dst := by
    rw [h_dbal]; show (Devm.getStor s1 sevm.currentTarget).get dst = _; rw [hs1]
  -- assemble the Increase
  intro a
  constructor
  · intro h_eq
    subst h_eq
    simp only [Stor.rest, Function.comp_apply]
    rw [toB256_toAdr h_dst, h_set, Stor.get_set_self, ← h_dbal']
  · intro h_ne
    simp only [Stor.rest, Function.comp_apply]
    rw [h_set]
    have h_key_ne : a.toB256 ≠ dst := by
      intro hc; apply h_ne; rw [← toAdr_toB256 a, hc]
    rw [Stor.get_set_ne _ h_key_ne.symm, h_stor]

lemma of_transferFromUpdateSbal {sevm : Sevm} {s₀ sₙ : Devm} {sbal wad src}
    (h_src : ValidAdr src) (h_sbal : sbal = (Devm.getStor s₀ sevm.currentTarget).get src)
    (h_le : wad ≤ sbal) (hp₀ : [sbal, wad, wad, src] <<+ s₀.stack) :
    Line.Run sevm s₀ transferFromUpdateSbal sₙ →
    ( Decrease src.toAdr wad (Stor.rest (Devm.getStor s₀ sevm.currentTarget)) (Stor.rest (Devm.getStor sₙ sevm.currentTarget)) ∧
      wad ≤ Stor.rest (Devm.getStor s₀ sevm.currentTarget) src.toAdr ) := by
  intro h_run
  simp only [transferFromUpdateSbal] at h_run
  rcases of_run_append [sub, dup 2] h_run with ⟨sm, h_pre, h_post⟩
  clear h_run
  have h_stor : Devm.getStor s₀ = Devm.getStor sm := Line.of_inv Devm.getStor (by line_inv) h_pre
  rcases Line.of_run_cons h_pre with ⟨s1, r_sub, h1⟩
  rcases Line.of_run_cons h1 with ⟨s2, r_dup, h2⟩
  cases h2
  clear h1 h_pre
  -- sub : [sbal - wad, wad, src]
  have hp1 : (sbal - wad) :: [wad, src] <<+ s1.stack := prefix_of_sub r_sub hp₀
  -- dup 2 : push element at index 2 (= src)
  rcases of_run_dup r_dup with ⟨x, hx, pb_dup⟩
  have hx_src : x = src := by
    have h_nth : Stack.Nth 2 src [sbal - wad, wad, src] :=
      Stack.Nth.tail 1 src (sbal - wad) [wad, src]
        (Stack.Nth.tail 0 src wad [src] (Stack.Nth.head src []))
    have h_get : s1.stack[(2 : Fin 16).val]? = some src := Stack.nth_getElem h_nth hp1
    rw [h_get] at hx; injection hx with hx; exact hx.symm
  subst x
  have hp2 : [src, sbal - wad, wad, src] <<+ sm.stack := prefix_of_push pb_dup hp1
  -- sstore
  rcases Line.of_run_cons h_post with ⟨s3, r_sstore, h3⟩
  cases h3
  have h_set : Devm.getStor sₙ sevm.currentTarget
      = (Devm.getStor sm sevm.currentTarget).set src (sbal - wad) :=
    sstore_getStor_set r_sstore hp2
  constructor
  · intro a
    constructor
    · intro h_eq
      subst h_eq
      simp only [Stor.rest, Function.comp_apply]
      rw [toB256_toAdr h_src, h_set, Stor.get_set_self, ← h_sbal]
    · intro h_ne
      simp only [Stor.rest, Function.comp_apply]
      rw [h_set]
      have h_key_ne : a.toB256 ≠ src := by
        intro hc; apply h_ne; rw [← toAdr_toB256 a, hc]
      rw [Stor.get_set_ne _ h_key_ne.symm, h_stor]
  · simp only [Stor.rest, Function.comp_apply]
    rw [toB256_toAdr h_src, ← h_sbal]; exact h_le

lemma updateAllowance_preserves_stor_rest {fs : List Func} {sevm : Sevm} {s r : Devm} {wad dst}
    (hs : [wad, dst] <<+ s.stack)
    (h_run : Func.Run fs sevm s updateAllowance r) :
    (Stor.rest (Devm.getStor s sevm.currentTarget)) = (Stor.rest (Devm.getStor r sevm.currentTarget)) := by
  rcases of_run_prepend [caller, dup 2, eq] _ h_run with ⟨s0, h_s0, h_run0⟩
  clear h_run
  rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) h_s0) sevm.currentTarget]
  rcases of_run_branch h_run0 with
    ⟨s1, h_pop, h_runP⟩ | ⟨w, s1, s2, h_ne, h_pop, h_burn, h_runQ⟩
  · -- update path
    -- pop the `(dst =? caller)` flag (= 0, since this is the update branch)
    have hs0 : [dst =? Adr.toB256 sevm.caller, wad, dst] <<+ s0.stack := by generalize_line_prefix
    have hp0 := h_pop.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp0
    rw [hp0] at hs0
    have hs1 : [wad, dst] <<+ s1.stack := by
      have hflag : (dst =? Adr.toB256 sevm.caller) = 0 :=
        pref_head_unique hs0 (pref_append [0] s1.stack)
      rw [hflag] at hs0; exact cons_pref_cons_inv hs0
    rw [(Devm.PopBurn.getStor h_pop sevm.currentTarget).symm]
    clear hs0 hp0 h_pop h_s0 h_run0 hs
    -- segment 1 : swap 0 :: mstoreAt 0  ( wad dst -- wad )
    rcases of_run_prepend (swap 0 :: mstoreAt 0) _ h_runP with ⟨sA, hA, h_runP⟩
    have hsA : [wad] <<+ sA.stack := by generalize_line_prefix
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hA) sevm.currentTarget]
    clear hA hs1
    -- segment 2 : caller  ( wad -- caller wad )
    rcases of_run_next h_runP with ⟨sB, rB, h_runP⟩
    have hsB : [Adr.toB256 sevm.caller, wad] <<+ sB.stack :=
      prefix_of_push (of_run_caller rB) hsA
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons rB Line.Run.nil)) sevm.currentTarget]
    clear rB hsA
    -- segment 3 : mstoreAt 1  ( caller wad -- wad )
    rcases of_run_prepend (mstoreAt 1) _ h_runP with ⟨sC, hC, h_runP⟩
    have hsC : [wad] <<+ sC.stack := by generalize_line_prefix
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hC) sevm.currentTarget]
    clear hC hsB
    -- segment 4 : pushList [64, 0]  ( wad -- 0 64 wad )
    rcases of_run_prepend (pushList [64, 0]) _ h_runP with ⟨sD, hD, h_runP⟩
    have hsD : [0, 64, wad] <<+ sD.stack := by generalize_line_prefix
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hD) sevm.currentTarget]
    clear hD hsC
    -- segment 5 : kec  ( 0 64 wad -- hash wad )
    rcases of_run_next h_runP with ⟨sE, rE, h_runP⟩
    rcases prefix_of_kec rE hsD with ⟨hash, hsE⟩
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons rE Line.Run.nil)) sevm.currentTarget]
    clear rE hsD
    -- segment 6 : swap 0  ( hash wad -- wad hash )
    rcases of_run_next h_runP with ⟨sF, rF, h_runP⟩
    have h_swapF : Stack.Swap (0 : Fin 16).val [hash, wad] [wad, hash] :=
      Stack.swapCore_zero
    have hsF : [wad, hash] <<+ sF.stack :=
      Stack.prefix_of_swap h_swapF (of_run_swap rF) hsE
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons rF Line.Run.nil)) sevm.currentTarget]
    clear rF hsE
    -- segment 7 : dup 1  ( wad hash -- hash wad hash )
    rcases of_run_next h_runP with ⟨sG1, rG1, h_runP⟩
    rcases of_run_dup rG1 with ⟨y, hy, pbG1⟩
    have hy_hash : y = hash := by
      have h_nth : Stack.Nth 1 hash [wad, hash] :=
        Stack.Nth.tail 0 hash wad [hash] (Stack.Nth.head hash [])
      have h_get : sF.stack[(1 : Fin 16).val]? = some hash := Stack.nth_getElem h_nth hsF
      rw [h_get] at hy; injection hy with hy; exact hy.symm
    subst y
    have hsG1 : [hash, wad, hash] <<+ sG1.stack := prefix_of_push pbG1 hsF
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons rG1 Line.Run.nil)) sevm.currentTarget]
    clear rG1 pbG1 hsF
    -- segment 8 : checkAddress  ( hash wad hash -- va(hash) wad hash )
    rcases of_run_prepend checkAddress _ h_runP with ⟨sG, hG, h_runP⟩
    rcases of_check_address hsG1 hG with ⟨va, hsG, h_iff⟩
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hG) sevm.currentTarget]
    clear hG hsG1
    -- rev-branch : checkAddress guarantees `hash` is not a valid address
    rcases of_run_branch_rev h_runP with ⟨sH, h_popH, h_runP⟩
    have hpH := h_popH.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpH
    rw [hpH] at hsG
    have hva0 : va = 0 := pref_head_unique hsG (pref_append [0] sH.stack)
    have hnva : ¬ ValidAdr hash := h_iff.mp hva0
    rw [hva0] at hsG
    have hsH : [wad, hash] <<+ sH.stack := cons_pref_cons_inv hsG
    rw [(Devm.PopBurn.getStor h_popH sevm.currentTarget).symm]
    clear hsG hpH h_popH h_iff hva0
    -- dup 1  ( wad hash -- hash wad hash )
    rcases of_run_next h_runP with ⟨sI, rI, h_runP⟩
    rcases of_run_dup rI with ⟨y, hyI, pbI⟩
    have hyI' : y = hash := by
      have h_nth : Stack.Nth 1 hash [wad, hash] :=
        Stack.Nth.tail 0 hash wad [hash] (Stack.Nth.head hash [])
      have h_get : sH.stack[(1 : Fin 16).val]? = some hash := Stack.nth_getElem h_nth hsH
      rw [h_get] at hyI; injection hyI with hyI; exact hyI.symm
    subst y
    have hsI : [hash, wad, hash] <<+ sI.stack := prefix_of_push pbI hsH
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons rI Line.Run.nil)) sevm.currentTarget]
    clear rI pbI hsH
    -- sload  ( hash wad hash -- amnt wad hash )
    rcases of_run_next h_runP with ⟨sJ, rJ, h_runP⟩
    rcases prefix_of_sload rJ hsI with ⟨amnt, hsJ, _⟩
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons rJ Line.Run.nil)) sevm.currentTarget]
    clear rJ hsI
    -- dup 0  ( amnt wad hash -- amnt amnt wad hash )
    rcases of_run_next h_runP with ⟨sK, rK, h_runP⟩
    rcases of_run_dup rK with ⟨y, hyK, pbK⟩
    have hyK' : y = amnt := by
      have h_nth : Stack.Nth 0 amnt [amnt, wad, hash] := Stack.Nth.head amnt [wad, hash]
      have h_get : sJ.stack[(0 : Fin 16).val]? = some amnt := Stack.nth_getElem h_nth hsJ
      rw [h_get] at hyK; injection hyK with hyK; exact hyK.symm
    subst y
    have hsK : [amnt, amnt, wad, hash] <<+ sK.stack := prefix_of_push pbK hsJ
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons rK Line.Run.nil)) sevm.currentTarget]
    clear rK pbK hsJ
    -- isMax = [not, iszero]  ( amnt amnt wad hash -- flag amnt wad hash )
    rcases of_run_prepend isMax _ h_runP with ⟨sL, hL, h_runP⟩
    rcases Line.of_run_cons hL with ⟨sK', rNot, hL'⟩
    rcases Line.of_run_cons hL' with ⟨sK'', rIsz, hLnil⟩
    cases hLnil
    have hsL0 : (~~~ amnt) :: [amnt, wad, hash] <<+ sK'.stack := prefix_of_not rNot hsK
    have hsL : ((~~~ amnt) =? 0) :: [amnt, wad, hash] <<+ sL.stack := prefix_of_iszero rIsz hsL0
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hL) sevm.currentTarget]
    clear hL rNot rIsz hsK hsL0
    -- returnTrue-branch : early-return when allowance is infinite
    rcases of_run_branch h_runP with
      ⟨sM, h_popM, h_runP⟩ | ⟨w2, sM, sM2, h_ne2, h_popM, h_burnM, h_runQ2⟩
    · -- continue path
      have hpM := h_popM.stack
      simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpM
      rw [hpM] at hsL
      have hflagM : ((~~~ amnt) =? 0) = 0 := pref_head_unique hsL (pref_append [0] sM.stack)
      rw [hflagM] at hsL
      have hsM : [amnt, wad, hash] <<+ sM.stack := cons_pref_cons_inv hsL
      rw [(Devm.PopBurn.getStor h_popM sevm.currentTarget).symm]
      clear hsL hpM h_popM hflagM
      -- dup 1  ( amnt wad hash -- wad amnt wad hash )
      rcases of_run_next h_runP with ⟨sN1, rN1, h_runP⟩
      rcases of_run_dup rN1 with ⟨y, hyN1, pbN1⟩
      have hyN1' : y = wad := by
        have h_nth : Stack.Nth 1 wad [amnt, wad, hash] :=
          Stack.Nth.tail 0 wad amnt [wad, hash] (Stack.Nth.head wad [hash])
        have h_get : sM.stack[(1 : Fin 16).val]? = some wad := Stack.nth_getElem h_nth hsM
        rw [h_get] at hyN1; injection hyN1 with hyN1; exact hyN1.symm
      subst y
      have hsN1 : [wad, amnt, wad, hash] <<+ sN1.stack := prefix_of_push pbN1 hsM
      rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons rN1 Line.Run.nil)) sevm.currentTarget]
      clear rN1 pbN1 hsM
      -- dup 1  ( wad amnt wad hash -- amnt wad amnt wad hash )
      rcases of_run_next h_runP with ⟨sN2, rN2, h_runP⟩
      rcases of_run_dup rN2 with ⟨y, hyN2, pbN2⟩
      have hyN2' : y = amnt := by
        have h_nth : Stack.Nth 1 amnt [wad, amnt, wad, hash] :=
          Stack.Nth.tail 0 amnt wad [amnt, wad, hash] (Stack.Nth.head amnt [wad, hash])
        have h_get : sN1.stack[(1 : Fin 16).val]? = some amnt := Stack.nth_getElem h_nth hsN1
        rw [h_get] at hyN2; injection hyN2 with hyN2; exact hyN2.symm
      subst y
      have hsN2 : [amnt, wad, amnt, wad, hash] <<+ sN2.stack := prefix_of_push pbN2 hsN1
      rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons rN2 Line.Run.nil)) sevm.currentTarget]
      clear rN2 pbN2 hsN1
      -- lt  ( amnt wad amnt wad hash -- (amnt<?wad) amnt wad hash )
      rcases of_run_next h_runP with ⟨sN, rN, h_runP⟩
      have hsN : (amnt <? wad) :: [amnt, wad, hash] <<+ sN.stack := prefix_of_lt rN hsN2
      rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons rN Line.Run.nil)) sevm.currentTarget]
      clear rN hsN2
      -- rev-branch : guarantees allowance ≥ wad
      rcases of_run_branch_rev h_runP with ⟨sO, h_popO, h_runP⟩
      have hpO := h_popO.stack
      simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpO
      rw [hpO] at hsN
      have hflagO : (amnt <? wad) = 0 := pref_head_unique hsN (pref_append [0] sO.stack)
      rw [hflagO] at hsN
      have hsO : [amnt, wad, hash] <<+ sO.stack := cons_pref_cons_inv hsN
      rw [(Devm.PopBurn.getStor h_popO sevm.currentTarget).symm]
      clear hsN hpO h_popO hflagO
      -- sub  ( amnt wad hash -- (amnt-wad) hash )
      rcases of_run_next h_runP with ⟨sP, rP, h_runP⟩
      have hsP : (amnt - wad) :: [hash] <<+ sP.stack := prefix_of_sub rP hsO
      rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons rP Line.Run.nil)) sevm.currentTarget]
      clear rP hsO
      -- swap 0  ( (amnt-wad) hash -- hash (amnt-wad) )
      rcases of_run_next h_runP with ⟨sQ, rQ, h_runP⟩
      have h_swapQ : Stack.Swap (0 : Fin 16).val [amnt - wad, hash] [hash, amnt - wad] :=
        Stack.swapCore_zero
      have hsQ : [hash, amnt - wad] <<+ sQ.stack :=
        Stack.prefix_of_swap h_swapQ (of_run_swap rQ) hsP
      rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons rQ Line.Run.nil)) sevm.currentTarget]
      clear rQ hsP
      -- sstore  ( key `hash` is not a valid address, so `.rest` is unchanged )
      rcases of_run_next h_runP with ⟨sR, rR, h_runP⟩
      rw [sstore_preserves_stor_rest hnva hsQ rR]
      -- returnTrue
      rw [congr_fun (Func.of_inv Devm.getStor Devm.getStor (by func_inv) h_runP)
        sevm.currentTarget]
    · -- early return (allowance infinite) : `returnTrue` preserves storage
      rw [← Devm.PopBurn.getStor h_popM sevm.currentTarget,
          ← Devm.Burn.getStor h_burnM sevm.currentTarget,
          congr_fun (Func.of_inv Devm.getStor Devm.getStor (by func_inv) h_runQ2)
            sevm.currentTarget]
  · -- early return : `returnTrue` preserves storage
    have h_eq : Devm.getStor s0 sevm.currentTarget = Devm.getStor r sevm.currentTarget := by
      rw [← Devm.PopBurn.getStor h_pop sevm.currentTarget,
          ← Devm.Burn.getStor h_burn sevm.currentTarget,
          congr_fun (Func.of_inv Devm.getStor Devm.getStor (by func_inv) h_runQ)
            sevm.currentTarget]
    rw [h_eq]

lemma transfer_of_transferFrom {fs : List Func} {sevm : Sevm} {s r : Devm} :
    Func.Run fs sevm s transferFrom r →
    ∃ (x : B256) (a a' : Adr),
      Transfer (Stor.rest (Devm.getStor s sevm.currentTarget)) a x a'
        (Stor.rest (Devm.getStor r sevm.currentTarget)) := by
  intro h_run
  simp only [transferFrom] at h_run
  -- arg 0 : push src
  rcases of_run_prepend (arg 0) _ h_run with ⟨a1, h1, h_run⟩
  rcases prefix_of_cdl nil_pref h1 with ⟨src, hs1⟩
  have hg : Devm.getStor s = Devm.getStor a1 := Line.of_inv Devm.getStor (by line_inv) h1
  clear h1
  -- dup 0 : [src, src]
  rcases of_run_next h_run with ⟨a2, r2, h_run⟩
  rcases of_run_dup r2 with ⟨y, hy2, pb2⟩
  have hy2' : y = src := by
    have h_get : a1.stack[(0 : Fin 16).val]? = some src :=
      Stack.nth_getElem (Stack.Nth.head src []) hs1
    rw [h_get] at hy2; injection hy2 with hy2; exact hy2.symm
  subst y
  have hs2 : [src, src] <<+ a2.stack := prefix_of_push pb2 hs1
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r2 Line.Run.nil))
  clear r2 pb2 hs1
  -- checkNonAddress
  rcases of_run_prepend checkNonAddress _ h_run with ⟨a3, h3, h_run⟩
  rcases of_check_non_address hs2 h3 with ⟨na_src, hs3, h_src_iff⟩
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h3)
  clear h3 hs2
  -- rev-branch : src is a valid address
  rcases of_run_branch_rev h_run with ⟨a4, hp4, h_run⟩
  have hp4s := hp4.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp4s
  rw [hp4s] at hs3
  have h_src : ValidAdr src := h_src_iff.mp (pref_head_unique hs3 (pref_append [0] a4.stack))
  rw [pref_head_unique hs3 (pref_append [0] a4.stack)] at hs3
  have hs4 : [src] <<+ a4.stack := cons_pref_cons_inv hs3
  have hg := hg.trans (funext (fun a => (Devm.PopBurn.getStor hp4 a).symm))
  clear hs3 hp4s hp4 h_src_iff
  -- arg 2 : push wad
  rcases of_run_prepend (arg 2) _ h_run with ⟨a5, h5, h_run⟩
  rcases prefix_of_cdl hs4 h5 with ⟨wad, hs5⟩
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h5)
  clear h5 hs4
  -- dup 0 : [wad, wad, src]
  rcases of_run_next h_run with ⟨a6, r6, h_run⟩
  rcases of_run_dup r6 with ⟨y, hy6, pb6⟩
  have hy6' : y = wad := by
    have h_get : a5.stack[(0 : Fin 16).val]? = some wad :=
      Stack.nth_getElem (Stack.Nth.head wad [src]) hs5
    rw [h_get] at hy6; injection hy6 with hy6; exact hy6.symm
  subst y
  have hs6 : [wad, wad, src] <<+ a6.stack := prefix_of_push pb6 hs5
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r6 Line.Run.nil))
  clear r6 pb6 hs5
  -- dup 2 : [src, wad, wad, src]
  rcases of_run_next h_run with ⟨a7, r7, h_run⟩
  rcases of_run_dup r7 with ⟨y, hy7, pb7⟩
  have hy7' : y = src := by
    have h_get : a6.stack[(2 : Fin 16).val]? = some src :=
      Stack.nth_getElem
        (Stack.Nth.tail 1 src wad [wad, src]
          (Stack.Nth.tail 0 src wad [src] (Stack.Nth.head src []))) hs6
    rw [h_get] at hy7; injection hy7 with hy7; exact hy7.symm
  subst y
  have hs7 : [src, wad, wad, src] <<+ a7.stack := prefix_of_push pb7 hs6
  have hg7 : Devm.getStor s = Devm.getStor a7 :=
    hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r7 Line.Run.nil))
  clear r7 pb7 hs6
  -- sload : [sbal, wad, wad, src]
  rcases of_run_next h_run with ⟨a8, r8, h_run⟩
  rcases prefix_of_sload r8 hs7 with ⟨sbal, hs8, h_sbal⟩
  have hg := hg7.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r8 Line.Run.nil))
  clear r8 hs7
  -- dup 1 : [wad, sbal, wad, wad, src]
  rcases of_run_next h_run with ⟨a9, r9, h_run⟩
  rcases of_run_dup r9 with ⟨y, hy9, pb9⟩
  have hy9' : y = wad := by
    have h_get : a8.stack[(1 : Fin 16).val]? = some wad :=
      Stack.nth_getElem
        (Stack.Nth.tail 0 wad sbal [wad, wad, src] (Stack.Nth.head wad [wad, src])) hs8
    rw [h_get] at hy9; injection hy9 with hy9; exact hy9.symm
  subst y
  have hs9 : [wad, sbal, wad, wad, src] <<+ a9.stack := prefix_of_push pb9 hs8
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r9 Line.Run.nil))
  clear r9 pb9 hs8
  -- dup 1 : [sbal, wad, sbal, wad, wad, src]
  rcases of_run_next h_run with ⟨a10, r10, h_run⟩
  rcases of_run_dup r10 with ⟨y, hy10, pb10⟩
  have hy10' : y = sbal := by
    have h_get : a9.stack[(1 : Fin 16).val]? = some sbal :=
      Stack.nth_getElem
        (Stack.Nth.tail 0 sbal wad [sbal, wad, wad, src] (Stack.Nth.head sbal [wad, wad, src])) hs9
    rw [h_get] at hy10; injection hy10 with hy10; exact hy10.symm
  subst y
  have hs10 : [sbal, wad, sbal, wad, wad, src] <<+ a10.stack := prefix_of_push pb10 hs9
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r10 Line.Run.nil))
  clear r10 pb10 hs9
  -- lt : [(sbal <? wad), sbal, wad, wad, src]
  rcases of_run_next h_run with ⟨a11, r11, h_run⟩
  have hs11 : (sbal <? wad) :: [sbal, wad, wad, src] <<+ a11.stack := prefix_of_lt r11 hs10
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r11 Line.Run.nil))
  clear r11 hs10
  -- rev-branch : source balance ≥ wad
  rcases of_run_branch_rev h_run with ⟨a12, hp12, h_run⟩
  have hp12s := hp12.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp12s
  rw [hp12s] at hs11
  have h_ltflag : (sbal <? wad) = 0 := pref_head_unique hs11 (pref_append [0] a12.stack)
  have h_le : wad ≤ sbal := by
    rw [← B256.not_lt]; intro hlt
    rw [B256.ltCheck, if_pos hlt] at h_ltflag
    exact B256.zero_ne_one h_ltflag.symm
  rw [h_ltflag] at hs11
  have hs12 : [sbal, wad, wad, src] <<+ a12.stack := cons_pref_cons_inv hs11
  have hg12 : Devm.getStor s = Devm.getStor a12 :=
    hg.trans (funext (fun a => (Devm.PopBurn.getStor hp12 a).symm))
  clear hs11 hp12s hp12 h_ltflag
  -- transferFromUpdateSbal : decrease source balance
  rcases of_run_prepend transferFromUpdateSbal _ h_run with ⟨a13, h13, h_run⟩
  have h_sbal' : sbal = (Devm.getStor a12 sevm.currentTarget).get src := by
    rw [h_sbal]
    show (Devm.getStor a7 sevm.currentTarget).get src = _
    rw [congr_fun (hg7.symm.trans hg12) sevm.currentTarget]
  rcases of_transferFromUpdateSbal h_src h_sbal' h_le hs12 h13 with ⟨h_dec, h_le'⟩
  have hs13 : [wad, src] <<+ a13.stack := by generalize_line_prefix
  clear h13 hs12 h_sbal h_sbal' h_le
  -- arg 1 : push dst
  rcases of_run_prepend (arg 1) _ h_run with ⟨a14, h14, h_run⟩
  rcases prefix_of_cdl hs13 h14 with ⟨dst, hs14⟩
  have hg' : Devm.getStor a13 = Devm.getStor a14 := Line.of_inv Devm.getStor (by line_inv) h14
  clear h14 hs13
  -- dup 0 : [dst, dst, wad, src]
  rcases of_run_next h_run with ⟨a15, r15, h_run⟩
  rcases of_run_dup r15 with ⟨y, hy15, pb15⟩
  have hy15' : y = dst := by
    have h_get : a14.stack[(0 : Fin 16).val]? = some dst :=
      Stack.nth_getElem (Stack.Nth.head dst [wad, src]) hs14
    rw [h_get] at hy15; injection hy15 with hy15; exact hy15.symm
  subst y
  have hs15 : [dst, dst, wad, src] <<+ a15.stack := prefix_of_push pb15 hs14
  have hg' := hg'.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r15 Line.Run.nil))
  clear r15 pb15 hs14
  -- checkNonAddress
  rcases of_run_prepend checkNonAddress _ h_run with ⟨a16, h16, h_run⟩
  rcases of_check_non_address hs15 h16 with ⟨na_dst, hs16, h_dst_iff⟩
  have hg' := hg'.trans (Line.of_inv Devm.getStor (by line_inv) h16)
  clear h16 hs15
  -- rev-branch : dst is a valid address
  rcases of_run_branch_rev h_run with ⟨a17, hp17, h_run⟩
  have hp17s := hp17.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp17s
  rw [hp17s] at hs16
  have h_dst : ValidAdr dst := h_dst_iff.mp (pref_head_unique hs16 (pref_append [0] a17.stack))
  rw [pref_head_unique hs16 (pref_append [0] a17.stack)] at hs16
  have hs17 : [dst, wad, src] <<+ a17.stack := cons_pref_cons_inv hs16
  have hg' := hg'.trans (funext (fun a => (Devm.PopBurn.getStor hp17 a).symm))
  clear hs16 hp17s hp17 h_dst_iff
  -- dup 0 : [dst, dst, wad, src]
  rcases of_run_next h_run with ⟨a18, r18, h_run⟩
  rcases of_run_dup r18 with ⟨y, hy18, pb18⟩
  have hy18' : y = dst := by
    have h_get : a17.stack[(0 : Fin 16).val]? = some dst :=
      Stack.nth_getElem (Stack.Nth.head dst [wad, src]) hs17
    rw [h_get] at hy18; injection hy18 with hy18; exact hy18.symm
  subst y
  have hs18 : [dst, dst, wad, src] <<+ a18.stack := prefix_of_push pb18 hs17
  have hg' := hg'.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r18 Line.Run.nil))
  clear r18 pb18 hs17
  -- dup 2 : [wad, dst, dst, wad, src]
  rcases of_run_next h_run with ⟨a19, r19, h_run⟩
  rcases of_run_dup r19 with ⟨y, hy19, pb19⟩
  have hy19' : y = wad := by
    have h_get : a18.stack[(2 : Fin 16).val]? = some wad :=
      Stack.nth_getElem
        (Stack.Nth.tail 1 wad dst [dst, wad, src]
          (Stack.Nth.tail 0 wad dst [wad, src] (Stack.Nth.head wad [src]))) hs18
    rw [h_get] at hy19; injection hy19 with hy19; exact hy19.symm
  subst y
  have hs19 : [wad, dst, dst, wad, src] <<+ a19.stack := prefix_of_push pb19 hs18
  have hg19 : Devm.getStor a13 = Devm.getStor a19 :=
    hg'.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r19 Line.Run.nil))
  clear r19 pb19 hs18
  -- incrWbal : increase destination balance
  rcases of_run_prepend incrWbal _ h_run with ⟨a20, h20, h_run⟩
  have h_incr : Increase dst.toAdr wad (Stor.rest (Devm.getStor a19 sevm.currentTarget))
      (Stor.rest (Devm.getStor a20 sevm.currentTarget)) :=
    incrAt_of_incrWbal h_dst h20 (pref_trans ⟨[dst, wad, src], rfl⟩ hs19)
  have hs20 : [dst, wad, src] <<+ a20.stack := by
    rcases of_run_append [dup 1, sload, add, swap 0] h20 with ⟨am, ham, hend⟩
    rcases Line.of_run_cons ham with ⟨b1, rd1, ham⟩
    rcases Line.of_run_cons ham with ⟨b2, rsl, ham⟩
    rcases Line.of_run_cons ham with ⟨b3, radd, ham⟩
    rcases Line.of_run_cons ham with ⟨b4, rsw, ham⟩
    cases ham
    rcases Line.of_run_cons hend with ⟨a20', r_sstore, hend⟩
    cases hend
    rcases of_run_dup rd1 with ⟨y, hy, pb⟩
    have hyd : y = dst := by
      have h_get : a19.stack[(1 : Fin 16).val]? = some dst :=
        Stack.nth_getElem
          (Stack.Nth.tail 0 dst wad [dst, dst, wad, src] (Stack.Nth.head dst [dst, wad, src])) hs19
      rw [h_get] at hy; injection hy with hy; exact hy.symm
    subst y
    have hb1 : [dst, wad, dst, dst, wad, src] <<+ b1.stack := prefix_of_push pb hs19
    rcases prefix_of_sload rsl hb1 with ⟨dbal, hb2, _⟩
    have hb3 : (dbal + wad) :: [dst, dst, wad, src] <<+ b3.stack := prefix_of_add radd hb2
    have h_swap : Stack.Swap (0 : Fin 16).val
        [dbal + wad, dst, dst, wad, src] [dst, dbal + wad, dst, wad, src] := Stack.swapCore_zero
    have hb4 : [dst, dbal + wad, dst, wad, src] <<+ am.stack :=
      Stack.prefix_of_swap h_swap (of_run_swap rsw) hb3
    exact prefix_of_sstore r_sstore hb4
  clear h20 hs19
  -- transferFromLog : does not touch storage
  rcases of_run_prepend transferFromLog _ h_run with ⟨a21, h21, h_run⟩
  have hs21 : [wad, src] <<+ a21.stack := by generalize_line_prefix
  have hg_log : Devm.getStor a20 = Devm.getStor a21 := Line.of_inv Devm.getStor (by line_inv) h21
  clear h21
  -- updateAllowance : preserves the WETH balance storage
  have h_ua : (Stor.rest (Devm.getStor a21 sevm.currentTarget)) = (Stor.rest (Devm.getStor r sevm.currentTarget)) :=
    updateAllowance_preserves_stor_rest hs21 h_run
  -- assemble the Transfer
  refine ⟨wad, src.toAdr, dst.toAdr, ?_, (Stor.rest (Devm.getStor a13 sevm.currentTarget)), ?_, ?_⟩
  · rw [congr_fun hg12 sevm.currentTarget]; exact h_le'
  · rw [congr_fun hg12 sevm.currentTarget]; exact h_dec
  · rw [congr_fun hg19 sevm.currentTarget, ← h_ua, ← congr_fun hg_log sevm.currentTarget]
    exact h_incr

lemma nof_of_solvent {sevm : Sevm} {s : Devm} {a}
    (h : Devm.PreSolvent s a sevm) : SumNof (Stor.rest (Devm.getStor s a)) := by
  apply lt_of_le_of_lt _ (B256.toNat_lt (s.getBal a))
  unfold Devm.PreSolvent at h
  by_cases h' : sevm.currentTarget = a
  · have hh := h.left h'; unfold Stor.Solvent wbsum at hh
    apply le_trans (Nat.le_add_right _ _) hh
  · have hh := h.right h'; unfold Stor.Solvent wbsum at hh
    apply le_trans (Nat.le_add_right _ _) hh

lemma result_solvent_of_wbsum_eq {sevm : Sevm} {s r : Devm}
    (h_sv : Devm.PreSolvent s sevm.currentTarget sevm)
    (h_sum : wbsum (Devm.getStor s sevm.currentTarget) = wbsum (Devm.getStor r sevm.currentTarget))
    (h_bal : s.getBal sevm.currentTarget = r.getBal sevm.currentTarget) :
    Devm.PostSolvent r sevm.currentTarget := by
  unfold Devm.PostSolvent Stor.Solvent
  rw [B256.toNat_zero, Nat.add_zero]
  have h_sv' := h_sv.left rfl
  unfold Stor.Solvent at h_sv'
  rw [← h_bal, ← h_sum]
  omega

lemma transferFrom_preserves_bal : Func.Inv Devm.getBal Devm.getBal transferFrom := by func_inv

lemma transferFrom_preserves_solvent {sevm : Sevm} {s r : Devm}
    (run : Func.Run (weth.main :: weth.aux) sevm s transferFrom r)
    (h_sv : Devm.PreSolvent s sevm.currentTarget sevm) :
    Devm.PostSolvent r sevm.currentTarget := by
  rcases transfer_of_transferFrom run with ⟨x, a, a', h_di⟩
  refine result_solvent_of_wbsum_eq h_sv ?_ ?_
  · exact transfer_preserves_sum (nof_of_solvent h_sv) h_di
  · exact congr_fun (Func.of_inv Devm.getBal Devm.getBal transferFrom_preserves_bal run)
      sevm.currentTarget

lemma precond_of_precond {wa : Adr} {sevm : Sevm} {s s' : Devm}
    (h : Precond wa sevm s) (h_bal : s.getBal = s'.getBal)
    (h_stor : Devm.getStor s = Devm.getStor s') (h_code : s.getCode = s'.getCode) :
    Precond wa sevm s' := by
  refine' ⟨_, _, _⟩
  · rw [← congr_fun h_code wa]; exact h.code
  · rw [← h_bal]; exact h.nof
  · unfold Devm.PreSolvent
    rw [← congr_fun h_stor wa, ← congr_fun h_bal wa]; exact h.solvent

lemma solvent_of_withdraw_update_bal {sevm : Sevm} {s s' : Devm} {cbal wad}
    (h_pc : Precond sevm.currentTarget sevm s)
    (h_stk : [cbal, wad, wad] <<+ s.stack)
    (h_cbal : cbal = Devm.getStorVal s sevm.currentTarget sevm.caller.toB256)
    (h_le : wad ≤ cbal)
    (h_run : Line.Run sevm s [Blanc.Ninst.sub, Blanc.Ninst.caller, Blanc.Ninst.sstore] s') :
    wad ≤ s'.getBal sevm.currentTarget ∧
    Stor.Solvent (Devm.getStor s' sevm.currentTarget) 0 (s'.getBal sevm.currentTarget - wad) := by
  have h_cbal' : (Devm.getStor s sevm.currentTarget).get sevm.caller.toB256 = cbal := h_cbal.symm
  have h_bal : s.getBal = s'.getBal := Line.of_inv Devm.getBal (by line_inv) h_run
  rcases Line.of_run_cons h_run with ⟨s₁, r_sub, h1⟩
  rcases Line.of_run_cons h1 with ⟨s₂, r_caller, h2⟩
  rcases Line.of_run_cons h2 with ⟨s₃, r_sstore, h3⟩
  cases h3
  clear h_run h1 h2
  -- sub : [cbal - wad, wad]
  have hp1 : (cbal - wad) :: [wad] <<+ s₁.stack := prefix_of_sub r_sub h_stk
  -- caller : [caller, cbal - wad, wad]
  have hp2 : [sevm.caller.toB256, cbal - wad, wad] <<+ s₂.stack :=
    prefix_of_push (of_run_caller r_caller) hp1
  -- sub and caller do not touch storage
  have h_stor : Devm.getStor s = Devm.getStor s₂ :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons r_sub (Line.Run.cons r_caller Line.Run.nil))
  -- sstore : set caller's WETH balance to cbal - wad
  have h_set : Devm.getStor s' sevm.currentTarget
      = (Devm.getStor s₂ sevm.currentTarget).set sevm.caller.toB256 (cbal - wad) :=
    sstore_getStor_set r_sstore hp2
  have h_dec : Decrease sevm.caller wad
      (Stor.rest (Devm.getStor s sevm.currentTarget)) (Stor.rest (Devm.getStor s' sevm.currentTarget)) := by
    intro a
    constructor
    · intro h_eq; subst h_eq
      simp only [Stor.rest, Function.comp_apply]
      rw [h_set, Stor.get_set_self, h_cbal']
    · intro h_ne
      simp only [Stor.rest, Function.comp_apply]
      rw [h_set]
      have h_key_ne : a.toB256 ≠ sevm.caller.toB256 := by
        intro hc; apply h_ne
        rw [← toAdr_toB256 a, hc, toAdr_toB256]
      rw [Stor.get_set_ne _ h_key_ne.symm, h_stor]
  have h_le_rest : wad ≤ (Stor.rest (Devm.getStor s sevm.currentTarget)) sevm.caller := by
    simp only [Stor.rest, Function.comp_apply]
    rw [h_cbal']; exact h_le
  have h_eq : wbsum (Devm.getStor s sevm.currentTarget) - wad.toNat
      = wbsum (Devm.getStor s' sevm.currentTarget) := sum_sub_assoc h_dec h_le_rest
  have h_le' : wad.toNat ≤ wbsum (Devm.getStor s sevm.currentTarget) := by
    apply le_trans (B256.toNat_le_toNat h_le)
    have h := @le_sum (Stor.rest (Devm.getStor s sevm.currentTarget)) sevm.caller
    simp only [Stor.rest, Function.comp_apply] at h
    rw [h_cbal'] at h
    exact h
  have h_solv := h_pc.solvent.left rfl
  unfold Stor.Solvent at h_solv
  have h_le_bal : wad.toNat ≤ (s.getBal sevm.currentTarget).toNat := by omega
  have h_le_bal' : wad ≤ s'.getBal sevm.currentTarget := by
    rw [← congr_fun h_bal sevm.currentTarget]
    exact B256.le_of_toNat_le_toNat h_le_bal
  refine' ⟨h_le_bal', _⟩
  unfold Stor.Solvent
  rw [B256.toNat_zero, Nat.add_zero, ← congr_fun h_bal sevm.currentTarget]
  rw [B256.toNat_sub_eq_of_le _ _ (B256.le_of_toNat_le_toNat h_le_bal), ← h_eq]
  omega


-- already solvent with `wad` subtracted from the balance
lemma solvent_of_state_eq {sf s₁ : Devm} {ct : Adr} {wad : B256}
    (h_state : sf.state = s₁.state)
    (h_le : wad ≤ s₁.getBal ct)
    (h_sv : Stor.Solvent (Devm.getStor s₁ ct) 0 (s₁.getBal ct - wad)) :
    Stor.Solvent (Devm.getStor sf ct) 0 (sf.getBal ct) := by
  rw [getStor_eq_of_state_eq h_state, getBal_eq_of_state_eq h_state]
  unfold Stor.Solvent at *
  rw [B256.toNat_sub_eq_of_le _ _ h_le] at h_sv
  omega


lemma of_send_to_caller {sevm : Sevm} {s sf : Devm} {wad}
    (ih : Exec.InvDepth sevm.depth sevm.currentTarget weth
      (Precond sevm.currentTarget) (Postcond sevm.currentTarget))
    (hp : [wad] <<+ s.stack)
    (h_code : some (s.getCode sevm.currentTarget).toList = Prog.compile weth)
    (h_nof : sum s.getBal < 2 ^ 256)
    (h_le : wad ≤ s.getBal sevm.currentTarget)
    (h_sv : Stor.Solvent (Devm.getStor s sevm.currentTarget) 0 (s.getBal sevm.currentTarget - wad)) :
    Line.Run sevm s sendToCaller sf →
    Stor.Solvent (Devm.getStor sf sevm.currentTarget) 0 (sf.getBal sevm.currentTarget) := by
  line_execute 7
  have hs₁ : [0, sevm.caller.toB256, wad, 0, 0, 0, 0] <<+ s₁.stack := by
    generalize_line_prefix
  -- transport the hypotheses to s₁
  have h_bal₁ : s.getBal = s₁.getBal := Line.of_inv Devm.getBal (by line_inv) h₁
  have h_stor₁ : Devm.getStor s = Devm.getStor s₁ := Line.of_inv Devm.getStor (by line_inv) h₁
  have h_code₁ : s.getCode = s₁.getCode := Line.of_inv Devm.getCode (by line_inv) h₁
  rw [h_bal₁] at h_nof
  rw [congr_fun h_bal₁ sevm.currentTarget] at h_le h_sv
  rw [congr_fun h_stor₁ sevm.currentTarget] at h_sv
  rw [congr_fun h_code₁ sevm.currentTarget] at h_code
  clear h_bal₁ h_stor₁ h_code₁ h₁ hp s
  -- the call instruction
  intro h₂
  rcases of_run_singleton h₂ with ⟨xl, h_fill, pc, h_run⟩
  simp only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.step,
    Bind.bind, Except.bind, Except.assert] at h_run
  -- pop gas
  rcases eq1 : Devm.pop s₁ with _ | ⟨gas, devm1⟩ <;> simp only [eq1] at h_run
  · cases XStep.run_ofExcept_error h_run
  have e1 := (Devm.pop_of_pop eq1).stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e1
  rw [e1] at hs₁
  have h_gas : (0 : B256) = gas :=
    pref_head_unique hs₁ (pref_append [gas] devm1.stack)
  subst h_gas
  have hs₂ : [sevm.caller.toB256, wad, 0, 0, 0, 0] <<+ devm1.stack := cons_pref_cons_inv hs₁
  -- pop callee
  rcases eq2 : Devm.popToAdr devm1 with _ | ⟨callee, devm2⟩ <;> simp only [eq2] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToAdr eq2 with ⟨x, hx, h_pop2⟩
  have e2 := (Devm.pop_of_pop h_pop2).stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e2
  rw [e2] at hs₂
  have h_x : sevm.caller.toB256 = x := pref_head_unique hs₂ (pref_append [x] devm2.stack)
  subst h_x
  rw [toAdr_toB256] at hx
  subst hx
  have hs₃ : [wad, 0, 0, 0, 0] <<+ devm2.stack := cons_pref_cons_inv hs₂
  -- pop value
  rcases eq3 : Devm.pop devm2 with _ | ⟨value, devm3⟩ <;> simp only [eq3] at h_run
  · cases XStep.run_ofExcept_error h_run
  have e3 := (Devm.pop_of_pop eq3).stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e3
  rw [e3] at hs₃
  have h_wad : wad = value := pref_head_unique hs₃ (pref_append [value] devm3.stack)
  subst h_wad
  -- pop the four indices/sizes
  rcases eq4 : Devm.popToNat devm3 with _ | ⟨inputIndex, devm4⟩ <;> simp only [eq4] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases eq5 : Devm.popToNat devm4 with _ | ⟨inputSize, devm5⟩ <;> simp only [eq5] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases eq6 : Devm.popToNat devm5 with _ | ⟨outputIndex, devm6⟩ <;> simp only [eq6] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases eq7 : Devm.popToNat devm6 with _ | ⟨outputSize, devm7⟩ <;> simp only [eq7] at h_run
  · cases XStep.run_ofExcept_error h_run
  -- state is unchanged by the seven pops
  rcases Devm.pop_of_popToNat eq4 with ⟨_, h_pop4⟩
  rcases Devm.pop_of_popToNat eq5 with ⟨_, h_pop5⟩
  rcases Devm.pop_of_popToNat eq6 with ⟨_, h_pop6⟩
  rcases Devm.pop_of_popToNat eq7 with ⟨_, h_pop7⟩
  have h_st7 : s₁.state = devm7.state :=
    ((Devm.pop_of_pop eq1).state).trans
      (((Devm.pop_of_pop h_pop2).state).trans
        (((Devm.pop_of_pop eq3).state).trans
          ((h_pop4.state).trans
            ((h_pop5.state).trans ((h_pop6.state).trans h_pop7.state)))))
  clear e1 e2 e3 hs₁ hs₂ hs₃ eq1 eq2 eq3 eq4 eq5 eq6 eq7
  clear h_pop2 h_pop4 h_pop5 h_pop6 h_pop7 h₂
  -- delegation resolution
  rcases hp11 : accessDelegation (addAccessedAddress devm7 sevm.caller) sevm.caller with
    ⟨dp, na, code0, dagc, devm9⟩
  simp only [hp11] at h_run
  have h_code0 :
      code0 = (accessDelegation (addAccessedAddress devm7 sevm.caller) sevm.caller).2.2.1 := by
    rw [hp11]
  have h_st9 : devm9.state = devm7.state := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).state) hp11
    dsimp at h
    rw [← h, accessDelegation_state]
    rfl
  -- charge the call gas
  split at h_run
  · cases XStep.run_ofExcept_error h_run
  rename_i devm10 eq16
  have h_st10 : devm9.state = devm10.state := (Devm.burn_of_chargeGas eq16).state
  have h_st11 :
      (devm10.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).state
        = s₁.state := by
    show devm10.state = s₁.state
    rw [← h_st10, h_st9, ← h_st7]
  have h_st_devm7 : devm7.state = s₁.state := h_st7.symm
  clear h_st10 h_st9 h_st7 eq16
  -- static-context assertion
  split at h_run
  case h_1 => cases XStep.run_ofExcept_error h_run
  case h_2 =>
  split at h_run
  · -- insufficient balance : call fails, state unchanged
    split at h_run
    case h_1 => cases XStep.run_ofExcept_error h_run
    case h_2 =>
    rename_i devm12 eq20
    apply solvent_of_state_eq _ h_le h_sv
    have h_ex := Except.ok.inj h_run.2
    rw [h_ex]
    show devm12.state = s₁.state
    rw [← (Devm.push_of_push eq20).state]
    exact h_st11
  · -- balance is sufficient : the call goes through
    simp only [genericCall.step] at h_run
    split at h_run
    · -- depth limit reached : call fails, state unchanged
      simp only [Bind.bind, Except.bind] at h_run
      split at h_run
      case h_1 => cases XStep.run_ofExcept_error h_run
      case h_2 =>
      rename_i devm12 h_push
      apply solvent_of_state_eq _ h_le h_sv
      have h_ex := Except.ok.inj h_run.2
      rw [h_ex]
      show devm12.state = s₁.state
      rw [← (Devm.push_of_push h_push).state]
      exact h_st11
    · -- the call is executed
      simp only [XStep.Run] at h_run
      rcases h_run with ⟨ex', run_pm₀, h_split⟩
      -- name the child message and keep only the projections we need
      obtain ⟨childMsg, run_pm, hc_stv, hc_state, hc_caller, hc_value, hc_ct,
          hc_ca, hc_code, hc_depth⟩ :
          ∃ m : Msg, ProcessMessage m xl ex' ∧
            m.shouldTransferValue = true ∧ m.benv.state = s₁.state ∧
            m.caller = sevm.currentTarget ∧ m.value = wad ∧
            m.currentTarget = sevm.caller ∧ m.codeAddress = some sevm.caller ∧
            m.code = code0 ∧ m.depth = sevm.depth - 1 :=
        ⟨_, run_pm₀, rfl, h_st11, rfl, rfl, rfl, rfl, rfl, rfl⟩
      clear run_pm₀
      -- resolve the outer split : the sub-message result must be ok
      rcases ex' with err' | child
      · cases Resume.call_run_error h_split.symm
      have h_sf_state : sf.state = child.state :=
        Resume.call_state h_split.symm
      -- unpack the process-message run
      obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp run_pm
      unfold FrameBody at hbody
      rcases eq_bt : childMsg.benvAfterTransfer with e | benv' <;>
        rw [eq_bt] at hbody
      · rw [hbody.2, processMessage.settle_error] at hset
        cases hset
      have run_ec : ExecuteCode (childMsg.withBenv benv') xl r0 := hbody
      -- the value transfer performed before the sub-message run
      rcases of_benvAfterTransfer hc_stv eq_bt with ⟨st_mid, h_sub, hB⟩
      rw [hc_state, hc_caller, hc_value] at h_sub
      have h_nof' : sum s₁.state.bal < 2 ^ 256 := h_nof
      rcases of_state_transfer (callee := sevm.caller) h_sub h_nof' with
        ⟨h_t_stor, h_t_code, h_t_sum, h_t_le, h_t_self, h_t_ne⟩
      have hBs : benv'.state = st_mid.addBal sevm.caller wad := by
        rw [hB, hc_ct, hc_value]; rfl
      -- resolve the inner split : either rollback or a clean sub-message result
      rcases r0 with x | evm2
      · rw [processMessage.settle_error] at hset
        cases hset
      unfold processMessage.settle at hset
      dsimp only [bind, Except.bind] at hset
      by_cases h_err2 : evm2.error.isSome = true
      · -- sub-message failed : state rolled back to the pre-transfer state
        rw [if_pos h_err2] at hset
        have h_if := Except.ok.inj hset.symm
        apply solvent_of_state_eq _ h_le h_sv
        rw [h_sf_state, ← h_if]
        show childMsg.benv.state = s₁.state
        exact hc_state
      -- sub-message succeeded
      rw [if_neg h_err2] at hset
      have h_if := (Except.ok.inj hset.symm).symm
      subst h_if
      have h_wb_ca : (childMsg.withBenv benv').codeAddress = some sevm.caller := hc_ca
      rcases of_executeCode_someCode h_wb_ca run_ec with
        ⟨h_prec, h_xl_none, h_he⟩ | ⟨h_prec, ex''', h_xl_some, h_he⟩
      · -- callee is a precompile : no sub-execution, only the transfer
        have h_child_state : child.state = benv'.state := by
          have h := state_of_executePrecomp_ok h_he h_err2
          rw [h]; rfl
        have h_stor_eq : Devm.getStor sf sevm.currentTarget = Devm.getStor s₁ sevm.currentTarget := by
          show (sf.state.get sevm.currentTarget).stor = (s₁.state.get sevm.currentTarget).stor
          rw [h_sf_state, h_child_state, hBs]
          exact h_t_stor sevm.currentTarget
        have h_bal_eq : sf.getBal sevm.currentTarget = benv'.state.bal sevm.currentTarget := by
          show (sf.state.get sevm.currentTarget).bal = (benv'.state.get sevm.currentTarget).bal
          rw [h_sf_state, h_child_state]
        rw [h_stor_eq, h_bal_eq, hBs]
        by_cases h_callee : sevm.caller = sevm.currentTarget
        · rw [h_t_self h_callee]
          unfold Stor.Solvent at h_sv ⊢
          rw [B256.toNat_sub_eq_of_le _ _ h_le] at h_sv
          have h_defeq : (s₁.state.bal sevm.currentTarget).toNat = (s₁.getBal sevm.currentTarget).toNat := rfl
          omega
        · rw [h_t_ne h_callee]
          exact h_sv
      · -- callee is a regular account : a sub-execution takes place
        rw [h_xl_some] at h_fill
        dsimp only [Xlot.Filled] at h_fill
        rcases ex''' with ⟨err3, d3⟩ | child3
        · -- sub-execution error : contradicts the clean sub-message result
          rcases of_handleError_err h_he with ⟨evm4, h_ok4, h_some4, _⟩ | ⟨e, h_err4⟩
          · have h_ok4 := Except.ok.inj h_ok4
            rw [← h_ok4] at h_some4
            exact absurd h_some4 h_err2
          · cases h_err4
        -- clean sub-execution : apply the induction hypothesis
        simp only [executeCode.handleError] at h_he
        have h_he := (Except.ok.inj h_he).symm
        subst h_he
        obtain ⟨ex_sub⟩ := h_fill
        -- abbreviations for the sub-message's initial sevm/devm
        have h_sd_state : (initDevm (childMsg.withBenv benv')).state = benv'.state := rfl
        have h_ss_ct : (initSevm (childMsg.withBenv benv')).currentTarget = sevm.caller := hc_ct
        -- code at the target is the WETH code
        have h_code_at :
            some ((initDevm (childMsg.withBenv benv')).getCode sevm.currentTarget).toList
              = weth.compile := by
          show some ((initDevm (childMsg.withBenv benv')).state.get sevm.currentTarget).code.toList
            = weth.compile
          rw [h_sd_state, hBs, h_t_code sevm.currentTarget]
          exact h_code
        -- the target program invariant for the sub-execution
        have h_at : Prog.At weth sevm.currentTarget 0
            (initSevm (childMsg.withBenv benv')) (initDevm (childMsg.withBenv benv')) := by
          refine ⟨h_code_at, ?_⟩
          intro h_eq_ct
          rw [h_ss_ct] at h_eq_ct
          refine ⟨?_, rfl⟩
          show some (initSevm (childMsg.withBenv benv')).code.toList = weth.compile
          have h_code_c : (initSevm (childMsg.withBenv benv')).code = code0 := hc_code
          rw [h_code_c, h_code0]
          have h_ad : (addAccessedAddress devm7 sevm.caller).state.getCode sevm.caller
              = s₁.getCode sevm.currentTarget := by
            show devm7.state.getCode sevm.caller = s₁.getCode sevm.currentTarget
            rw [h_st_devm7, h_eq_ct]; rfl
          have h_notdel : ¬ isValidDelegation
              ((addAccessedAddress devm7 sevm.caller).state.getCode sevm.caller) := by
            rw [h_ad]; exact not_delegation_of_compile h_code
          rw [accessDelegation_code_of_not h_notdel, h_ad]
          exact h_code
        -- the depth of the sub-execution is strictly smaller
        have h_depth_lt : (initSevm (childMsg.withBenv benv')).depth < sevm.depth := by
          have h_dep : (initSevm (childMsg.withBenv benv')).depth = sevm.depth - 1 := hc_depth
          rw [h_dep]; omega
        -- the precondition holds for the sub-message
        have h_gs : Devm.getStor (initDevm (childMsg.withBenv benv')) sevm.currentTarget
            = Devm.getStor s₁ sevm.currentTarget := by
          show ((initDevm (childMsg.withBenv benv')).state.get sevm.currentTarget).stor
            = (s₁.state.get sevm.currentTarget).stor
          rw [h_sd_state, hBs, h_t_stor sevm.currentTarget]
        have h_precond : Precond sevm.currentTarget
            (initSevm (childMsg.withBenv benv')) (initDevm (childMsg.withBenv benv')) := by
          refine ⟨h_code_at, ?_, ?_⟩
          · -- nof
            have h_gb_fun : (initDevm (childMsg.withBenv benv')).getBal = benv'.state.bal := by
              funext a
              show ((initDevm (childMsg.withBenv benv')).state.get a).bal = (benv'.state.get a).bal
              rw [h_sd_state]
            rw [h_gb_fun, hBs, h_t_sum]; exact h_nof
          · -- PreSolvent
            refine ⟨?_, ?_⟩
            · intro h_eq
              rw [h_ss_ct] at h_eq
              have h_gv : (initSevm (childMsg.withBenv benv')).value = wad := hc_value
              rw [h_gs, h_gv]
              have h_gb : (initDevm (childMsg.withBenv benv')).getBal sevm.currentTarget
                  = s₁.getBal sevm.currentTarget := by
                show ((initDevm (childMsg.withBenv benv')).state.get sevm.currentTarget).bal
                  = (s₁.state.get sevm.currentTarget).bal
                rw [h_sd_state, hBs]
                show (st_mid.addBal sevm.caller wad).bal sevm.currentTarget
                  = (s₁.state.get sevm.currentTarget).bal
                rw [h_t_self h_eq]; rfl
              rw [h_gb]
              unfold Stor.Solvent at h_sv ⊢
              rw [B256.toNat_zero, Nat.add_zero] at h_sv
              rw [B256.toNat_sub_eq_of_le _ _ h_le] at h_sv
              have := B256.toNat_le_toNat h_le
              omega
            · intro h_ne
              rw [h_ss_ct] at h_ne
              rw [h_gs]
              have h_gb : (initDevm (childMsg.withBenv benv')).getBal sevm.currentTarget
                  = s₁.getBal sevm.currentTarget - wad := by
                show ((initDevm (childMsg.withBenv benv')).state.get sevm.currentTarget).bal
                  = s₁.getBal sevm.currentTarget - wad
                rw [h_sd_state, hBs]
                show (st_mid.addBal sevm.caller wad).bal sevm.currentTarget
                  = s₁.getBal sevm.currentTarget - wad
                rw [h_t_ne h_ne]; rfl
              rw [h_gb]; exact h_sv
        -- apply the induction hypothesis
        have hpost : Postcond sevm.currentTarget (initSevm (childMsg.withBenv benv')) child :=
          ih 0 (initSevm (childMsg.withBenv benv')) (initDevm (childMsg.withBenv benv'))
            (.ok child) ex_sub h_depth_lt h_at h_precond
        rw [getStor_eq_of_state_eq h_sf_state sevm.currentTarget,
            getBal_eq_of_state_eq h_sf_state sevm.currentTarget]
        exact hpost.solvent

lemma withdraw_preserves_solvent {sevm : Sevm} {s r : Devm}
    (cond : Precond sevm.currentTarget sevm s)
    (ih : Exec.InvDepth sevm.depth sevm.currentTarget weth (Precond sevm.currentTarget) (Postcond sevm.currentTarget))
    (run : Func.Run (weth.main :: weth.aux) sevm s withdraw r) :
    Devm.PostSolvent r sevm.currentTarget := by
  revert run
  func_execute_with withdrawLoadCheck
  rcases of_withdrawLoadCheck h₁ with ⟨h_bal, h_stor, h_code, wad, cbal, hp₁, h_cbal⟩
  have cond₁ : Precond sevm.currentTarget sevm s₁ :=
    precond_of_precond cond h_bal h_stor h_code
  clear cond h₁ h_bal h_stor h_code
  intro h_run
  -- rev-branch : the caller's WETH balance must cover the withdrawal
  rcases of_run_branch_rev h_run with ⟨s₂, h_pop, h_run'⟩
  have hp2s := h_pop.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp2s
  rw [hp2s] at hp₁
  have h_ltflag : (cbal <? wad) = 0 := pref_head_unique hp₁ (pref_append [0] s₂.stack)
  have h_wad : wad ≤ cbal := by
    rw [← B256.not_lt]; intro hlt
    rw [B256.ltCheck, if_pos hlt] at h_ltflag
    exact B256.zero_ne_one h_ltflag.symm
  rw [h_ltflag] at hp₁
  have hp₂ : [cbal, wad, wad] <<+ s₂.stack := cons_pref_cons_inv hp₁
  have cond₂ : Precond sevm.currentTarget sevm s₂ :=
    Precond.state_eq cond₁ h_pop.state.symm
  have h_cbal₂ : cbal = Devm.getStorVal s₂ sevm.currentTarget sevm.caller.toB256 := by
    rw [h_cbal]
    show (Devm.getStor s₁ sevm.currentTarget).get sevm.caller.toB256
      = (Devm.getStor s₂ sevm.currentTarget).get sevm.caller.toB256
    rw [Devm.PopBurn.getStor h_pop sevm.currentTarget]
  clear h_cbal hp₁ hp2s h_ltflag cond₁ h_run
  -- update the caller's WETH balance in storage
  revert h_run'
  func_execute 3
  rcases solvent_of_withdraw_update_bal cond₂ hp₂ h_cbal₂ h_wad h₃ with ⟨h_le, h_sv⟩
  have h_code₃ : some (s₃.getCode sevm.currentTarget).toList = Prog.compile weth := by
    rw [← congr_fun (Line.of_inv Devm.getCode (by line_inv) h₃) sevm.currentTarget]
    exact cond₂.code
  have h_nof₃ : sum s₃.getBal < 2 ^ 256 := by
    rw [← Line.of_inv Devm.getBal (by line_inv) h₃]
    exact cond₂.nof
  have hp₃ : [wad] <<+ s₃.stack := by generalize_line_prefix
  -- send the withdrawn amount to the caller
  func_execute_with sendToCaller
  intro h₅
  unfold Devm.PostSolvent
  rw [← congr_fun (Func.of_inv Devm.getStor Devm.getStor (by func_inv) h₅) sevm.currentTarget]
  rw [← congr_fun (Func.of_inv Devm.getBal Devm.getBal (by func_inv) h₅) sevm.currentTarget]
  exact of_send_to_caller ih hp₃ h_code₃ h_nof₃ h_le h_sv h₄

lemma decimals_preserves_solvent {sevm : Sevm} {s r : Devm}
    (run : Func.Run (weth.main :: weth.aux) sevm s decimals r)
    (h_sv : Devm.PreSolvent s sevm.currentTarget sevm) :
    Devm.PostSolvent r sevm.currentTarget := by simple_solvent

lemma balanceOf_preserves_solvent {sevm : Sevm} {s r : Devm}
    (run : Func.Run (weth.main :: weth.aux) sevm s balanceOf r)
    (h_sv : Devm.PreSolvent s sevm.currentTarget sevm) :
    Devm.PostSolvent r sevm.currentTarget := by simple_solvent

lemma symbol_preserves_solvent {sevm : Sevm} {s r : Devm}
    (run : Func.Run (weth.main :: weth.aux) sevm s symbol r)
    (h_sv : Devm.PreSolvent s sevm.currentTarget sevm) :
    Devm.PostSolvent r sevm.currentTarget := by simple_solvent

lemma transfer_preserves_bal : Func.Inv Devm.getBal Devm.getBal transfer := by func_inv

lemma of_transferTestDst {sevm : Sevm} {s s' : Devm} :
    Line.Run sevm s transferTestDst s' →
    ∃ na_dst dst,
      ([na_dst, dst] <<+ s'.stack) ∧
      (na_dst = 0 ↔ ValidAdr dst) := by
  simp only [transferTestDst]
  line_execute_with (arg 0)
  rcases prefix_of_cdl nil_pref h₁ with ⟨dst, hp₁⟩
  clear h₁
  line_execute 1
  have hp₂ : [dst, dst] <<+ s₂.stack := by generalize_line_prefix
  clear hp₁ h₂
  intro h
  rcases of_check_non_address hp₂ h with ⟨na_dst, h_pfx, h_iff⟩
  exact ⟨_, _, h_pfx, h_iff⟩

lemma of_transferTestLt {sevm : Sevm} {s s' : Devm} {dst}
    (h_stk : [dst] <<+ s.stack) :
    Line.Run sevm s transferTestLt s' →
    ∃ lt? caller wad,
      ([lt?, caller, Devm.getStorVal s' sevm.currentTarget caller - wad, wad, dst] <<+ s'.stack) ∧
      (lt? = 0 ↔ wad ≤ Devm.getStorVal s' sevm.currentTarget caller) ∧
      ValidAdr caller := by
  simp only [transferTestLt]
  -- arg 1 : push wad
  line_execute_with (arg 1)
  rcases prefix_of_cdl h_stk h₁ with ⟨wad, hp₁⟩
  clear h₁
  -- caller, dup 0 : [caller, caller, wad, dst]
  line_execute 2
  have hp₂ : [sevm.caller.toB256, sevm.caller.toB256, wad, dst] <<+ s₂.stack := by generalize_line_prefix
  clear h₂
  -- sload : [cbal, caller, wad, dst]
  line_execute 1
  rcases prefix_of_sload (of_run_singleton h₃) hp₂ with ⟨cbal, hp₃, h_cbal⟩
  have hstor23 : Devm.getStor s₂ = Devm.getStor s₃ := Line.of_inv Devm.getStor (by line_inv) h₃
  clear h₃
  -- swap 0, dup 2, dup 0, dup 3, sub, swap 2, lt :
  --   [cbal <? wad, caller, cbal - wad, wad, dst]
  intro h₄
  have hp₄ : [cbal <? wad, sevm.caller.toB256, cbal - wad, wad, dst] <<+ s'.stack := by generalize_line_prefix
  have hstor34 : Devm.getStor s₃ = Devm.getStor s' := Line.of_inv Devm.getStor (by line_inv) h₄
  have h_cbal' : cbal = Devm.getStorVal s' sevm.currentTarget sevm.caller.toB256 := by
    rw [h_cbal]
    show (Devm.getStor s₂ _).get _ = (Devm.getStor s' _).get _
    rw [hstor23, hstor34]
  refine ⟨cbal <? wad, sevm.caller.toB256, wad, ?_, ?_, validAdr_toB256 sevm.caller⟩
  · rw [← h_cbal']; exact hp₄
  · rw [← h_cbal', B256.ltCheck, Ne.ite_eq_right_iff B256.zero_ne_one.symm, B256.not_lt]

lemma transfer_of_transfer {fs : List Func} {sevm : Sevm} {s r : Devm} :
    Func.Run fs sevm s transfer r →
    ∃ (x : B256) (a a' : Adr),
      Transfer (Stor.rest (Devm.getStor s sevm.currentTarget)) a x a'
        (Stor.rest (Devm.getStor r sevm.currentTarget)) := by
  intro h_run
  simp only [transfer] at h_run
  -- transferTestDst : [dst_invalid?, dst]
  rcases of_run_prepend transferTestDst _ h_run with ⟨s1, h1, h_run⟩
  rcases of_transferTestDst h1 with ⟨dst_invalid, dst, hp1, h_dst⟩
  have hg1 : Devm.getStor s = Devm.getStor s1 := Line.of_inv Devm.getStor (by line_inv) h1
  clear h1
  -- rev-branch : dst is a valid address
  rcases of_run_branch_rev h_run with ⟨s2, hp2b, h_run⟩
  have hp2bs := hp2b.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp2bs
  rw [hp2bs] at hp1
  have h_dst_valid : ValidAdr dst := h_dst.mp (pref_head_unique hp1 (pref_append [0] s2.stack))
  rw [pref_head_unique hp1 (pref_append [0] s2.stack)] at hp1
  have hp2 : [dst] <<+ s2.stack := cons_pref_cons_inv hp1
  have hg2 : Devm.getStor s = Devm.getStor s2 :=
    hg1.trans (funext (fun a => (Devm.PopBurn.getStor hp2b a).symm))
  clear hp1 hp2bs hp2b h_dst
  -- transferTestLt : [lt?, caller, cbal - wad, wad, dst]
  rcases of_run_prepend transferTestLt _ h_run with ⟨s3, h3, h_run⟩
  rcases of_transferTestLt hp2 h3 with ⟨lt?, caller, wad, hp3, h_le, h_caller⟩
  have hg3 : Devm.getStor s = Devm.getStor s3 :=
    hg2.trans (Line.of_inv Devm.getStor (by line_inv) h3)
  clear h3 hp2
  -- rev-branch : wad ≤ caller balance
  rcases of_run_branch_rev h_run with ⟨s4, hp4b, h_run⟩
  have hp4bs := hp4b.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp4bs
  rw [hp4bs] at hp3
  have h_lt0 : lt? = 0 := pref_head_unique hp3 (pref_append [0] s4.stack)
  have h_le' : wad ≤ Devm.getStorVal s3 sevm.currentTarget caller := h_le.mp h_lt0
  rw [h_lt0] at hp3
  have hp4 : [caller, Devm.getStorVal s3 sevm.currentTarget caller - wad, wad, dst] <<+ s4.stack :=
    cons_pref_cons_inv hp3
  have hg4 : Devm.getStor s = Devm.getStor s4 :=
    hg3.trans (funext (fun a => (Devm.PopBurn.getStor hp4b a).symm))
  clear hp3 hp4bs hp4b h_le h_lt0
  -- transferCore : sstore ::: incrWbal +++ logTransfer +++ returnTrue
  simp only [transferCore] at h_run
  -- sstore : set caller's WETH balance to cbal - wad
  rcases of_run_next h_run with ⟨s5, r5, h_run⟩
  have h_set : Devm.getStor s5 sevm.currentTarget
      = (Devm.getStor s4 sevm.currentTarget).set caller
          (Devm.getStorVal s3 sevm.currentTarget caller - wad) :=
    sstore_getStor_set r5 hp4
  have hp5 : [wad, dst] <<+ s5.stack := prefix_of_sstore r5 hp4
  clear hp4
  -- incrWbal : increase destination balance
  rcases of_run_prepend incrWbal _ h_run with ⟨s6, h6, h_run⟩
  have h_incr : Increase dst.toAdr wad (Stor.rest (Devm.getStor s5 sevm.currentTarget))
      (Stor.rest (Devm.getStor s6 sevm.currentTarget)) :=
    incrAt_of_incrWbal h_dst_valid h6 hp5
  -- logTransfer, returnTrue : do not touch storage
  have h_rest : Devm.getStor s6 sevm.currentTarget = Devm.getStor r sevm.currentTarget :=
    congr_fun (Func.of_inv Devm.getStor Devm.getStor (by func_inv) h_run) sevm.currentTarget
  -- assemble the Transfer
  refine ⟨wad, caller.toAdr, dst.toAdr, ?_, (Stor.rest (Devm.getStor s5 sevm.currentTarget)), ?_, ?_⟩
  · show wad ≤ (Stor.rest (Devm.getStor s sevm.currentTarget)) caller.toAdr
    simp only [Stor.rest, Function.comp_apply]
    rw [toB256_toAdr h_caller, congr_fun hg3 sevm.currentTarget]
    exact h_le'
  · intro a
    constructor
    · intro h_eq; subst h_eq
      simp only [Stor.rest, Function.comp_apply]
      rw [toB256_toAdr h_caller, h_set, Stor.get_set_self, congr_fun hg3 sevm.currentTarget]
      rfl
    · intro h_ne
      simp only [Stor.rest, Function.comp_apply]
      rw [h_set]
      have h_key_ne : a.toB256 ≠ caller := by
        intro hc; apply h_ne; rw [← toAdr_toB256 a, hc]
      rw [Stor.get_set_ne _ h_key_ne.symm, congr_fun hg4 sevm.currentTarget]
  · rw [← h_rest]; exact h_incr

lemma transfer_preserves_solvent {sevm : Sevm} {s r : Devm}
    (run : Func.Run (weth.main :: weth.aux) sevm s transfer r)
    (h_sv : Devm.PreSolvent s sevm.currentTarget sevm) :
    Devm.PostSolvent r sevm.currentTarget := by
  rcases transfer_of_transfer run with ⟨x, a, a', h_di⟩
  refine result_solvent_of_wbsum_eq h_sv ?_ ?_
  · exact transfer_preserves_sum (nof_of_solvent h_sv) h_di
  · exact congr_fun (Func.of_inv Devm.getBal Devm.getBal transfer_preserves_bal run)
      sevm.currentTarget

lemma allowance_preserves_solvent {sevm : Sevm} {s r : Devm}
    (run : Func.Run (weth.main :: weth.aux) sevm s allowance r)
    (h_sv : Devm.PreSolvent s sevm.currentTarget sevm) :
    Devm.PostSolvent r sevm.currentTarget := by simple_solvent


lemma sum_getBal_state {d : Devm} : sum d.getBal = sum d.state.bal := by
  have h : d.getBal = d.state.bal := funext (fun _ => rfl)
  rw [h]


lemma Exec.preserves_nof {pc : Nat} {sevm : Sevm} {devm : Devm} {exn : Execution}
    (run : Exec pc sevm devm exn) :
    ∀ r : Devm, exn = .ok r →
      sum devm.getBal < 2 ^ 256 → sum r.getBal < 2 ^ 256 := by
  intro r h_eq h_nof
  subst h_eq
  exact Nat.lt_of_le_of_lt (Exec.balance_effect run) h_nof

lemma Xinst.preserves_nof {sevm : Sevm} {s r : Devm} {x : Xinst} {xl : Xlot}
    (h : Xinst.Run sevm s x xl (.ok r)) (h_nof : sum s.getBal < 2 ^ 256)
    (h_fill : xl.Filled) :
    sum r.getBal < 2 ^ 256 := by
  have hxl : Xlot.Rel Devm.BalNoninc xl :=
    Xlot.rel_of_filled balNoninc_refl_trans.2.1 balNoninc_refl_trans.2.2
      Ninst.balance_effectRec Jinst.balance_effect Linst.balance_effect h_fill
  exact Nat.lt_of_le_of_lt (Xinst.balance_effectRec x hxl h) h_nof

lemma Ninst.preserves_nof {sevm : Sevm} {s r : Devm} {i : Ninst}
    (h : Ninst.Run sevm s i r) (h_nof : sum s.getBal < 2 ^ 256) :
    sum r.getBal < 2 ^ 256 :=
  Nat.lt_of_le_of_lt (Ninst.balance_effect i h) h_nof

lemma Func.preserves_nof {c : List Func} {sevm : Sevm} {s r : Devm} {f : Func}
    (run : Func.Run c sevm s f r) (h_nof : sum s.getBal < 2 ^ 256) :
    sum r.getBal < 2 ^ 256 :=
  Nat.lt_of_le_of_lt (Func.balance_effect run) h_nof

lemma run_preserves_cond (f : Func)
    ( h_solv :
      ∀ {sevm : Sevm} {s r : Devm},
        Func.Run (weth.main :: weth.aux) sevm s f r →
        Devm.PreSolvent s sevm.currentTarget sevm →
        Devm.PostSolvent r sevm.currentTarget ) :
    ∀ {sevm : Sevm} {s r : Devm},
      Func.Run (weth.main :: weth.aux) sevm s f r →
      Precond sevm.currentTarget sevm s →
      Postcond sevm.currentTarget sevm r := by
  intro sevm s r run cond
  constructor
  · apply Func.preserves_nof run cond.nof
  · apply h_solv run cond.solvent

lemma weth_inv {sevm : Sevm} {s r}
    (cond : Precond sevm.currentTarget sevm s)
    ( ih :
      Exec.InvDepth sevm.depth sevm.currentTarget weth
        (Precond sevm.currentTarget)
        (Postcond sevm.currentTarget) ) :
    Func.Run (weth.main :: weth.aux) sevm s (Func.call 0) r →
    Postcond sevm.currentTarget sevm r := by
  -- unwrap the initial `call 0` (this part does not exist in original proof in Solvent.lean)
  intro run; cases run
  rename (_ = _) => eq
  rename (Func.Run _ _ _ _ _) => run
  rename (Devm.Burn _ _) => burn
  rename Devm => s₀
  cases eq
  have cond₀ : Precond sevm.currentTarget sevm s₀ :=
    Precond.state_eq cond burn.state.symm
  clear cond burn s
  revert run
  func_execute_with fsig
  have cond₁ : Precond sevm.currentTarget sevm s₁ := by
    refine' ⟨_, _, _⟩
    · rw [← Line.of_inv Devm.getCode (by line_inv) h₁]; exact cond₀.code
    · rw [← Line.of_inv Devm.getBal (by line_inv) h₁]; exact cond₀.nof
    · apply Line.preserves_solvent _ _ cond₀.solvent h₁ <;> line_inv
  clear cond₀
  clear h₁
  clear s₀
  intro temp
  apply
    ( @dispatchWith_inv
      (weth.main :: weth.aux) 1 deposit
      (λ e s =>
         Precond e.currentTarget e s ∧
         Exec.InvDepth e.depth e.currentTarget weth (Precond e.currentTarget) (Postcond e.currentTarget) )
      (λ e r => Postcond e.currentTarget e r)
      ?_ ?_ rfl ?_ wethTree ?_ sevm s₁ r ⟨cond₁, ih⟩ temp )
    <;> clear temp cond₁ ih r s₁ sevm
  · intro e s x w s' s'' ⟨h_cond, h_ih⟩ h_run h_pop
    refine' ⟨_, h_ih⟩
    have h_run_state : s.state = s'.state := Line.of_inv Devm.state (by line_inv) h_run
    rcases h_pop with ⟨_, _, _, _, _, _, _, _, _, _, _, h_pop_state, _⟩
    apply Precond.state_eq h_cond
    exact h_pop_state.symm.trans h_run_state.symm
  · intro e s x w s' s'' ⟨h_cond, h_ih⟩ h_run h_pop
    refine' ⟨_, h_ih⟩
    have h_run_state : s.state = s'.state := Line.of_inv Devm.state (by line_inv) h_run
    rcases h_pop with ⟨_, _, _, _, _, _, _, _, _, _, _, h_pop_state, _⟩
    apply Precond.state_eq h_cond
    exact h_pop_state.symm.trans h_run_state.symm
  · intro e s s' r ⟨cond, ih⟩ burn run
    have cond' : Precond e.currentTarget e s' := Precond.state_eq cond burn.state.symm
    have r_cond : Postcond e.currentTarget e r :=
      run_preserves_cond deposit deposit_preserves_solvent run cond'
    exact r_cond
  · intro e s r wf h_mem ⟨cond, ih⟩ h_run
    -- Tree membership to list membership, so the ten obligations below are read
    -- off `wethFuncs` in its own order rather than off `build 10`'s split
    -- arithmetic (10 -> 5+5, 5 -> 3+2, 3 -> 2+1, 2 -> 1+1), which the old
    -- nesting transcribed by hand and which breaks on an eleventh function.
    -- `wethFuncs ≠ []` holds by delta — it is a literal list. Do not reach for
    -- `decide` here: deciding anything about these leaves forces the
    -- `String.keccak` behind every `selector` and blows `maxRecDepth`.
    have h_list : wf ∈ wethFuncs :=
      DispatchTree.mem_of_mem_ofSorted (List.cons_ne_nil _ _) h_mem
    simp only [wethFuncs, List.mem_cons, List.not_mem_nil, or_false] at h_list
    rcases h_list with h | h | h | h | h | h | h | h | h | h <;>
      (cases h)
    · apply run_preserves_cond name name_preserves_solvent h_run cond
    · apply run_preserves_cond approve approve_preserves_solvent h_run cond
    · apply run_preserves_cond totalSupply totalSupply_preserves_solvent h_run cond
    · apply run_preserves_cond transferFrom transferFrom_preserves_solvent h_run cond
    · constructor
      · apply Func.preserves_nof h_run cond.nof
      · apply withdraw_preserves_solvent cond ih h_run
    · apply run_preserves_cond decimals decimals_preserves_solvent h_run cond
    · apply run_preserves_cond balanceOf balanceOf_preserves_solvent h_run cond
    · apply run_preserves_cond symbol symbol_preserves_solvent h_run cond
    · apply run_preserves_cond transfer transfer_preserves_solvent h_run cond
    · apply run_preserves_cond allowance allowance_preserves_solvent h_run cond





-- started after a balance transfer from a non-WETH sender


-- nonempty code is unchanged by a (sub-)execution








/-- WETH's own frame-level obligation — the one input `ContractSpec.preserves_inv`
cannot supply.  This is the original first bullet of `weth_preserves_solvent`,
unchanged. -/
theorem wethSpec_sound (wa : Adr) : wethSpec.Sound wa := by
  simp only [ContractSpec.Sound, wethSpec_prog_eq, wethSpec_pre_eq, wethSpec_post_eq]
  intro sevm pre post run eq; rw [← eq]
  dsimp [Prog.Run] at run
  intro ih cond; apply weth_inv cond _ run
  intro pc' sevm' devm' exn'
  cases exn'; {simp only [ifOk, implies_true]}
  apply ih

theorem wethSpec_preserves (wa : Adr) : wethSpec.Preserves wa :=
  wethSpec.preserves_inv wa (wethSpec_sound wa)

theorem weth_preserves_solvent (wa : Adr) :
    ∀ sevm pre post,
      Exec 0 sevm pre (.ok post)  →
      (sevm.currentTarget = wa → some sevm.code.toList = Prog.compile weth) →
      Precond wa sevm pre →
      Postcond wa sevm post := by
  simpa only [ContractSpec.Preserves, wethSpec_prog_eq, wethSpec_pre_eq, wethSpec_post_eq]
    using wethSpec_preserves wa
-- Counterpart of `weth_preserves_solvent` for the total executable `exec`.  With
-- sufficiency proved in Jaune there is no fuel to quantify away: the
-- hypothesis is a plain equation about the interpreter.
theorem exec_preserves_solvent (wa : Adr)
    (sevm : Sevm) (pre post : Devm)
    (h_run : exec ⟨0, sevm, pre⟩ = .ok post)
    (h_code : sevm.currentTarget = wa → some sevm.code.toList = Prog.compile weth)
    (h_pc : Precond wa sevm pre) : Postcond wa sevm post := by
  exact wethSpec_post_iff.mp
    (wethSpec.exec_preserves_inv wa (wethSpec_preserves wa) sevm pre post h_run h_code
      (wethSpec_pre_iff.mpr h_pc))

/-! ### Bridge to the frame-level invariant

The descent from the message-call layer to `exec_preserves_solvent` — through
`prepareMessage`, the interpreter loop and `processMessageCall.{call,create}` —
is contract-generic and lives in `Blanc/Ladder.lean`
(`ContractSpec.processMessageCall_preserves_inv` and the transaction- and
block-level rungs above it).  Each of those rungs consumes the frame-level
result as a `c.Preserves ca` hypothesis; for WETH that hypothesis is
`wethSpec_preserves`, and the instances below are what feed it in. -/

/-- The block-level state transition, at WETH.  The generic parent
(`ContractSpec.stateTransitionWith_preserves_inv`) never asks which rules it is
running, because solvency is a statement about how value moves and no fork rule
moves value; every named-fork and configured-chain theorem below is an instance
of it. -/
theorem stateTransitionWith_preserves_solvent (wa : Adr) (rules : ForkRules)
    (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransitionWith rules ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : State.Inv wa ch.state) : State.Inv wa ch'.state :=
  wethSpec_stateInv_iff.mp
    (ContractSpec.stateTransitionWith_preserves_inv wa (wethSpec_preserves wa)
      rules ch ch' block h_run h_wds (wethSpec_stateInv_iff.mpr h_inv))
-- At an explicitly named fork: resolving the rules is the only extra step, and
-- a fork whose rules this build does not implement never reaches the
-- transition at all.

-- On a configured chain the block's own timestamp picks the rules. The result
-- holds whichever ones it picks, so a chain that crosses an activation is not
-- a new case: no fork in the schedule can break solvency, and neither can the
-- boundary between two of them.
theorem stateTransitionUsing_preserves_solvent (wa : Adr) (cfg : ChainConfig)
    (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransitionUsing cfg ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : State.Inv wa ch.state) : State.Inv wa ch'.state :=
  wethSpec_stateInv_iff.mp
    (ContractSpec.stateTransitionUsing_preserves_inv wa (wethSpec_preserves wa)
      cfg ch ch' block h_run h_wds (wethSpec_stateInv_iff.mpr h_inv))

-- Prague is the `rules := pragueRules` instance. The statement is unchanged,
-- and `stateTransition` is *definitionally* `stateTransitionWith pragueRules`,
-- so the instance is the whole proof.
theorem stateTransition_preserves_solvent (wa : Adr)
    (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransition ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : State.Inv wa ch.state) : State.Inv wa ch'.state :=
  wethSpec_stateInv_iff.mp
    (ContractSpec.stateTransition_preserves_inv wa (wethSpec_preserves wa)
      ch ch' block h_run h_wds (wethSpec_stateInv_iff.mpr h_inv))

-- Chain-level induction over a configured chain : no sequence of valid blocks
-- can break WETH solvency, whatever schedule the chain follows and whichever
-- activations that sequence crosses.  `BlockChain.ReachUsing` is unchanged and
-- now lives in `Blanc/Ladder.lean`.
theorem chainUsing_preserves_solvent (wa : Adr) (cfg : ChainConfig)
    (ch ch' : BlockChain) (h_reach : BlockChain.ReachUsing cfg ch ch')
    (h_inv : State.Inv wa ch.state) : State.Inv wa ch'.state :=
  wethSpec_stateInv_iff.mp
    (ContractSpec.chainUsing_preserves_inv wa (wethSpec_preserves wa)
      cfg ch ch' h_reach (wethSpec_stateInv_iff.mpr h_inv))

-- Chain-level induction corollary : no sequence of valid blocks can break
-- WETH solvency.
theorem chain_preserves_solvent (wa : Adr) (ch ch' : BlockChain)
    (h_reach : BlockChain.Reach ch ch')
    (h_inv : State.Inv wa ch.state) : State.Inv wa ch'.state :=
  wethSpec_stateInv_iff.mp
    (ContractSpec.chain_preserves_inv wa (wethSpec_preserves wa)
      ch ch' h_reach (wethSpec_stateInv_iff.mpr h_inv))

-- Bonus level : preservation through RLP decoding and block hash checks,
-- again under any fork's rules.
theorem addBlockToChainWith_preserves_solvent (wa : Adr) (rules : ForkRules)
    (ch ch' : BlockChain) (rlp : Bytes)
    (h_run : addBlockToChainWith rules ch rlp = .ok (.inl ch'))
    (h_wds : ∀ block hash, rlpToBlock rlp = .ok ⟨block, hash⟩ →
      sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : State.Inv wa ch.state) : State.Inv wa ch'.state :=
  wethSpec_stateInv_iff.mp
    (ContractSpec.addBlockToChainWith_preserves_inv wa (wethSpec_preserves wa)
      rules ch ch' rlp h_run h_wds (wethSpec_stateInv_iff.mpr h_inv))

-- Block import at an explicitly named fork.

-- Block import on a configured chain validates the schedule and chain identity
-- before decoding. Once decoding supplies the timestamp, the configured core
-- selects the rules and delegates to the same canonical import used above, so
-- the general rules-explicit theorem applies whichever activation is current.
theorem addBlockToChainUsing_preserves_solvent (wa : Adr) (cfg : ChainConfig)
    (ch ch' : BlockChain) (rlp : Bytes)
    (h_run : addBlockToChainUsing cfg ch rlp = .ok (.inl ch'))
    (h_wds : ∀ block hash, rlpToBlock rlp = .ok ⟨block, hash⟩ →
      sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : State.Inv wa ch.state) : State.Inv wa ch'.state :=
  wethSpec_stateInv_iff.mp
    (ContractSpec.addBlockToChainUsing_preserves_inv wa (wethSpec_preserves wa)
      cfg ch ch' rlp h_run h_wds (wethSpec_stateInv_iff.mpr h_inv))

-- Prague is the `rules := pragueRules` instance here too; the statement is
-- unchanged.
theorem addBlockToChain_preserves_solvent (wa : Adr)
    (ch ch' : BlockChain) (rlp : Bytes)
    (h_run : addBlockToChain ch rlp = .ok (.inl ch'))
    (h_wds : ∀ block hash, rlpToBlock rlp = .ok ⟨block, hash⟩ →
      sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : State.Inv wa ch.state) : State.Inv wa ch'.state :=
  addBlockToChainWith_preserves_solvent wa pragueRules ch ch' rlp h_run h_wds h_inv

end Blanc
