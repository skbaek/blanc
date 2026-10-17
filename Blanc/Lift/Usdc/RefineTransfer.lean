import Blanc.Lift.Usdc.RefineTransferDecode

/-!
# U6d: the whole-frame step law of USDC's transfer and allowance family

`implStepLaw_famTransfer : ImplStepLaw famTransfer`.  A successful implementation frame whose
message decodes to `transfer`, `transferFrom`, `approve`, `increaseAllowance` or
`decreaseAllowance` runs its selector's wrapper (`RefineTransferDispatch.lean`, from the
certificate walks of `RefineTransferCallees.lean`), so its storage at the proxy is the walk's;
read through the footprint ledger (`FootprintLedger.lean`) that storage is the book's step on the
message.  The frame decodes no external instruction (`family_noExec`), so the node clause holds
vacuously.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.SlotFootprint Impl

/-! ## Ledger reads of the walks' storage -/

theorem balanceBits_toB256 {n : Nat} (h : n < 2 ^ 255) : balanceBits (Nat.toB256 n) = n := by
  unfold balanceBits
  rw [B256.toNat_toB256_of_lt (by omega), Nat.mod_eq_of_lt h]

theorem frozenBit_toB256 {n : Nat} (h : n < 2 ^ 255) : frozenBit (Nat.toB256 n) = false := by
  unfold frozenBit
  rw [B256.toNat_toB256_of_lt (by omega), decide_eq_false_iff_not, Nat.not_le]
  exact h

section Ledger

variable {U : Key → Prop} {σ : Stor} (inj : Inj Key.slot U) (apart : Apart Key.slot fixedSlots U)
include inj apart

theorem ledger_debit {a : Adr} {v : Nat} (hk : U (.bal a))
    (fr : frozenBit (σ.get (balSlot a)) = false) (hv : v ≤ balanceBits (σ.get (balSlot a))) :
    ledger U (debitStor σ a v) = (ledger U σ).setBal a ((ledger U σ).bal a - v) := by
  have lt : balanceBits (σ.get (balSlot a)) - v < 2 ^ 255 := by
    have := Nat.mod_lt (σ.get (balSlot a)).toNat (Nat.two_pow_pos 255)
    unfold balanceBits at hv ⊢
    omega
  unfold debitStor
  rw [ledger_set_bal inj apart hk, Ledger.setWord_eq_setBal, balanceBits_toB256 lt,
    ledger_bal hk]
  rw [frozenBit_toB256 lt, ledger_frozen hk, fr]

theorem ledger_credit {a : Adr} {v : Nat} (hk : U (.bal a))
    (fr : frozenBit (σ.get (balSlot a)) = false)
    (hb : balanceBits (σ.get (balSlot a)) + v ≤ 2 ^ 255 - 1) :
    ledger U (creditStor σ a v) = (ledger U σ).setBal a ((ledger U σ).bal a + v) := by
  have lt : balanceBits (σ.get (balSlot a)) + v < 2 ^ 255 := by omega
  unfold creditStor
  rw [ledger_set_bal inj apart hk, Ledger.setWord_eq_setBal, balanceBits_toB256 lt,
    ledger_bal hk]
  rw [frozenBit_toB256 lt, ledger_frozen hk, fr]

theorem ledger_allow_toB256 {o s : Adr} {n : Nat} (hk : U (.allow o s)) (hn : n < 2 ^ 256) :
    ledger U (σ.set (allowSlot o s) (Nat.toB256 n)) = (ledger U σ).setAllow o s n := by
  rw [ledger_set_allow inj apart hk, B256.toNat_toB256_of_lt hn]

/-- **The walk's balance move is the model's `move`.** -/
theorem ledger_move {a d : Adr} {v : Nat} (ha : U (.bal a)) (hd : U (.bal d)) (a0 : a ≠ 0)
    (d0 : d ≠ 0) (fa : frozenBit (σ.get (balSlot a)) = false)
    (hv : v ≤ balanceBits (σ.get (balSlot a)))
    (fd : frozenBit ((debitStor σ a v).get (balSlot d)) = false)
    (hb : balanceBits ((debitStor σ a v).get (balSlot d)) + v ≤ 2 ^ 255 - 1) :
    (ledger U σ).move a d v = some (ledger U (creditStor (debitStor σ a v) d v)) := by
  have b1 : (ledger U σ).bal a = balanceBits (σ.get (balSlot a)) := ledger_bal ha
  have f1 : (ledger U σ).frozen a = frozenBit (σ.get (balSlot a)) := ledger_frozen ha
  have lt : balanceBits (σ.get (balSlot a)) < 2 ^ 255 :=
    Nat.mod_lt (σ.get (balSlot a)).toNat (Nat.two_pow_pos 255)
  have db := ledger_debit inj apart ha fa hv
  have b2 : (ledger U (debitStor σ a v)).bal d = balanceBits ((debitStor σ a v).get (balSlot d)) :=
    ledger_bal hd
  have f2 : (ledger U (debitStor σ a v)).frozen d = frozenBit ((debitStor σ a v).get (balSlot d)) :=
    ledger_frozen hd
  have g1 : ¬ (a = 0 ∨ d = 0 ∨ (ledger U σ).bal a < v) := by
    rw [b1]
    rintro (h | h | h)
    · exact a0 h
    · exact d0 h
    · omega
  have g2 : ¬ (2 ^ 255 ≤ (ledger U σ).bal a - v ∨ (ledger U σ).frozen a = true) := by
    rw [b1, f1, fa]
    rintro (h | h)
    · omega
    · cases h
  have g3 : ¬ (2 ^ 255 ≤ (ledger U (debitStor σ a v)).bal d + v ∨
      (ledger U (debitStor σ a v)).frozen d = true) := by
    rw [b2, f2, fd]
    rintro (h | h)
    · omega
    · cases h
  unfold Ledger.move
  rw [ite_eq_right g1, Ledger.setBalance, ite_eq_right g2, Option.bind_some, ← db,
    Ledger.setBalance, ite_eq_right g3, ledger_credit inj apart hd fd hb, b2]

end Ledger

/-! ## The step law -/

theorem get_set_off {y x : B256} (hy : y ∉ fixedSlots) (hx : x ∈ fixedSlots) (σ : Stor)
    (w : B256) : (σ.set y w).get x = σ.get x :=
  Stor.get_set_ne σ (fun e => hy (by rw [e]; exact hx)) w

/-- **ImplStepLaw for `transfer`, `transferFrom`, `approve`, `increaseAllowance` and
`decreaseAllowance`** (U6d). -/
theorem implStepLaw_famTransfer : ImplStepLaw famTransfer := by
  intro P U sevm pre post run codeEq tgt codeAddr fork nonstatic inj apart keys lib notAdmin c dec
    fam
  subst tgt
  have hrun : SFunc.Run cert.prog sevm (St pre pre.stack pre.memory pre.gasLeft) t_0000_c0
      (.halted post) := by
    obtain ⟨f, hf, r⟩ := lift_sound cert_check codeEq fork run
    rw [show cert.prog[0]? = some t_0000_c0 from rfl] at hf
    cases hf
    rw [← St.self rfl rfl]
    exact r
  have tk : ∀ k ∈ c.keys sevm.caller, U k := fun k h => keys k (keys_sub_frameKeys dec k h)
  have stepEq : (usdcBookS sevm.currentTarget).step
      (ledger U (pre.state.getStor sevm.currentTarget)) sevm =
      (ledger U (pre.state.getStor sevm.currentTarget)).step sevm.currentTarget sevm.caller c := by
    have na : ¬ sevm.caller = (ledger U (pre.state.getStor sevm.currentTarget)).admin := notAdmin
    simp only [usdcBookS, na, dec, ↓reduceIte]
  have node : ∀ (sel : Sevm.selector sevm ∈ famSelectors),
      ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
        ∀ x, Ninst.At N.sevm.code N.pc (.exec x) →
          x = .delegatecall ∧ ((ledger U (pre.state.getStor sevm.currentTarget)).Good →
            (ledger U (N.devm.state.getStor sevm.currentTarget)).Good) ∧
          (N.devm.state.getStor sevm.currentTarget).get implSlot =
            (pre.state.getStor sevm.currentTarget).get implSlot ∧
          (N.devm.state.getStor sevm.currentTarget).get adminSlot =
            (pre.state.getStor sevm.currentTarget).get adminSlot :=
    fun sel N hN x hx => absurd hx (family_noExec run codeEq fork sel N hN x)
  rw [stepEq]
  cases c <;> simp only [famTransfer] at fam
  · rename_i dst v
    obtain ⟨sel, rfl, rfl⟩ := decode_transfer dec
    obtain ⟨p0, fdst, c0, d0, hv, fc, fd, hb, sp⟩ := frame_transfer fork sel hrun
    have hs : Devm.getStor pre = pre.state.getStor := rfl
    rw [hs] at p0 fdst hv fc fd hb
    clear hrun stepEq
    have kc : U (.bal sevm.caller) := tk _ (by simp only [Call.keys, List.mem_cons, true_or])
    have kd : U (.bal (Sevm.dataWord sevm 4).toAdr) :=
      tk _ (by simp only [Call.keys, List.mem_cons, List.not_mem_nil, or_false, or_true])
    have sp' : post.state.getStor sevm.currentTarget = creditStor (debitStor
        (pre.state.getStor sevm.currentTarget) sevm.caller (Sevm.dataWord sevm 36).toNat)
        (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toNat := sp
    have g : ¬ ((ledger U (pre.state.getStor sevm.currentTarget)).paused = true ∨
        (ledger U (pre.state.getStor sevm.currentTarget)).frozen sevm.caller = true ∨
        (ledger U (pre.state.getStor sevm.currentTarget)).frozen
          (Sevm.dataWord sevm 4).toAdr = true) := by
      rw [ledger_frozen kc, ledger_frozen kd]
      change ¬ (flag20 _ = true ∨ _) 
      rw [p0, fc, fdst]
      simp only [Bool.false_eq_true, or_self, not_false_eq_true]
    refine ⟨?_, ?_, ?_, node (by simp only [famSelectors, sel, List.mem_cons, true_or])⟩
    · simp only [Ledger.step]
      rw [ite_eq_right g]
      exact (ledger_move inj apart kc kd c0 d0 fc hv fd hb).trans (by rw [sp'])
    · rw [sp']
      unfold creditStor debitStor
      rw [get_set_off (y := balSlot _) (x := implSlot) (apart _ kd) (by decide),
        get_set_off (y := balSlot _) (x := implSlot) (apart _ kc) (by decide)]
    · rw [sp']
      unfold creditStor debitStor
      rw [get_set_off (y := balSlot _) (x := adminSlot) (apart _ kd) (by decide),
        get_set_off (y := balSlot _) (x := adminSlot) (apart _ kc) (by decide)]
  · rename_i src dst v
    obtain ⟨sel, rfl, rfl, rfl⟩ := decode_transferFrom dec
    obtain ⟨p0, fcl, fs, fdst, a1, s0, d0, hv, fd, hb, a2, sp⟩ := frame_transferFrom fork sel hrun
    have hs : Devm.getStor pre = pre.state.getStor := rfl
    rw [hs] at p0 fcl fs fdst a1 hv fd hb a2 sp
    clear hrun stepEq
    have kc : U (.bal sevm.caller) := tk _ (by simp only [Call.keys, List.mem_cons, true_or])
    have ks : U (.bal (Sevm.dataWord sevm 4).toAdr) :=
      tk _ (by simp only [Call.keys, List.mem_cons, true_or, or_true])
    have kd : U (.bal (Sevm.dataWord sevm 36).toAdr) :=
      tk _ (by simp only [Call.keys, List.mem_cons, true_or, or_true])
    have ka : U (.allow (Sevm.dataWord sevm 4).toAdr sevm.caller) :=
      tk _ (by simp only [Call.keys, List.mem_cons, List.not_mem_nil, or_false, or_true])
    have sp' : post.state.getStor sevm.currentTarget = _ := sp
    have g : ¬ ((ledger U (pre.state.getStor sevm.currentTarget)).paused = true ∨
        (ledger U (pre.state.getStor sevm.currentTarget)).frozen sevm.caller = true ∨
        (ledger U (pre.state.getStor sevm.currentTarget)).frozen
          (Sevm.dataWord sevm 4).toAdr = true ∨
        (ledger U (pre.state.getStor sevm.currentTarget)).frozen
          (Sevm.dataWord sevm 36).toAdr = true ∨
        (ledger U (pre.state.getStor sevm.currentTarget)).allow (Sevm.dataWord sevm 4).toAdr
          sevm.caller < (Sevm.dataWord sevm 68).toNat) := by
      rw [ledger_frozen kc, ledger_frozen ks, ledger_frozen kd, ledger_allow ka]
      change ¬ (flag20 _ = true ∨ _)
      rw [p0, fcl, fs, fdst]
      simp only [Bool.false_eq_true, false_or, Nat.not_lt]
      exact a1
    refine ⟨?_, ?_, ?_, node (by simp only [famSelectors, sel, List.mem_cons, true_or, or_true])⟩
    · simp only [Ledger.step]
      rw [ite_eq_right g, ledger_move inj apart ks kd s0 d0 fs hv fd hb, Option.map_some,
        ledger_allow ka]
      have lt := B256.toNat_lt ((creditStor (debitStor (pre.state.getStor sevm.currentTarget)
        (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 68).toNat) (Sevm.dataWord sevm 36).toAdr
        (Sevm.dataWord sevm 68).toNat).get (allowSlot (Sevm.dataWord sevm 4).toAdr sevm.caller))
      rw [← ledger_allow_toB256 inj apart ka (by omega)]
      exact congrArg some (congrArg (ledger U) sp'.symm)
    · rw [sp']
      unfold creditStor debitStor
      rw [get_set_off (y := allowSlot _ _) (x := implSlot) (apart _ ka) (by decide),
        get_set_off (y := balSlot _) (x := implSlot) (apart _ kd) (by decide),
        get_set_off (y := balSlot _) (x := implSlot) (apart _ ks) (by decide)]
    · rw [sp']
      unfold creditStor debitStor
      rw [get_set_off (y := allowSlot _ _) (x := adminSlot) (apart _ ka) (by decide),
        get_set_off (y := balSlot _) (x := adminSlot) (apart _ kd) (by decide),
        get_set_off (y := balSlot _) (x := adminSlot) (apart _ ks) (by decide)]
  · rename_i sx v
    obtain ⟨sel, rfl, rfl⟩ := decode_approve dec
    obtain ⟨p0, c0, s0, sp⟩ := frame_approve fork sel hrun
    have hs : Devm.getStor pre = pre.state.getStor := rfl
    rw [hs] at p0 sp
    clear hrun stepEq
    have ka : U (.allow sevm.caller (Sevm.dataWord sevm 4).toAdr) :=
      tk _ (by simp only [Call.keys, List.mem_cons, true_or])
    have sp' : post.state.getStor sevm.currentTarget = _ := sp
    have hp : (ledger U (pre.state.getStor sevm.currentTarget)).paused = false := p0
    refine ⟨?_, ?_, ?_, node (by simp only [famSelectors, sel, List.mem_cons, true_or, or_true])⟩
    · simp only [Ledger.step, Ledger.approveOf]
      rw [hp, ite_eq_right (by simp only [Bool.false_eq_true, not_false_eq_true])]
      rw [ite_eq_right (by rintro (h | h); exact c0 h; exact s0 h)]
      rw [sp']
      exact congrArg some (ledger_set_allow inj apart ka _).symm
    · rw [sp', get_set_off (y := allowSlot _ _) (x := implSlot) (apart _ ka) (by decide)]
    · rw [sp', get_set_off (y := allowSlot _ _) (x := adminSlot) (apart _ ka) (by decide)]
  · rename_i sx v
    obtain ⟨sel, rfl, rfl⟩ := decode_increaseAllowance dec
    obtain ⟨p0, c0, s0, a1, sp⟩ := frame_increaseAllowance fork sel hrun
    have hs : Devm.getStor pre = pre.state.getStor := rfl
    rw [hs] at p0 a1 sp
    clear hrun stepEq
    have ka : U (.allow sevm.caller (Sevm.dataWord sevm 4).toAdr) :=
      tk _ (by simp only [Call.keys, List.mem_cons, true_or])
    have sp' : post.state.getStor sevm.currentTarget = _ := sp
    have hp : (ledger U (pre.state.getStor sevm.currentTarget)).paused = false := p0
    refine ⟨?_, ?_, ?_, node (by simp only [famSelectors, sel, List.mem_cons, true_or, or_true])⟩
    · simp only [Ledger.step, Ledger.approveOf]
      rw [ledger_allow ka, hp, ite_eq_right (by
        simp only [Bool.false_eq_true, false_or, Nat.not_le]; exact a1)]
      rw [ite_eq_right (by rintro (h | h); exact c0 h; exact s0 h)]
      rw [sp']
      exact congrArg some (ledger_allow_toB256 inj apart ka a1).symm
    · rw [sp', get_set_off (y := allowSlot _ _) (x := implSlot) (apart _ ka) (by decide)]
    · rw [sp', get_set_off (y := allowSlot _ _) (x := adminSlot) (apart _ ka) (by decide)]
  · rename_i sx v
    obtain ⟨sel, rfl, rfl⟩ := decode_decreaseAllowance dec
    obtain ⟨p0, c0, s0, a1, sp⟩ := frame_decreaseAllowance fork sel hrun
    have hs : Devm.getStor pre = pre.state.getStor := rfl
    rw [hs] at p0 a1 sp
    clear hrun stepEq
    have ka : U (.allow sevm.caller (Sevm.dataWord sevm 4).toAdr) :=
      tk _ (by simp only [Call.keys, List.mem_cons, true_or])
    have sp' : post.state.getStor sevm.currentTarget = _ := sp
    have hp : (ledger U (pre.state.getStor sevm.currentTarget)).paused = false := p0
    refine ⟨?_, ?_, ?_, node (by simp only [famSelectors, sel, List.mem_cons, true_or, or_true])⟩
    · simp only [Ledger.step, Ledger.approveOf]
      rw [ledger_allow ka, hp, ite_eq_right (by
        simp only [Bool.false_eq_true, false_or, Nat.not_lt]; exact a1)]
      rw [ite_eq_right (by rintro (h | h); exact c0 h; exact s0 h)]
      rw [sp']
      exact congrArg some (ledger_allow_toB256 inj apart ka (by have := B256.toNat_lt ((pre.state.getStor
        sevm.currentTarget).get (allowSlot sevm.caller (Sevm.dataWord sevm 4).toAdr)); omega)).symm
    · rw [sp', get_set_off (y := allowSlot _ _) (x := implSlot) (apart _ ka) (by decide)]
    · rw [sp', get_set_off (y := allowSlot _ _) (x := adminSlot) (apart _ ka) (by decide)]


end Blanc.Lift.Usdc
