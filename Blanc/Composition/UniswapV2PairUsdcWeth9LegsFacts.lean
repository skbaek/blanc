import Blanc.Composition.UniswapV2PairUsdcWeth9LegsFrame
import Blanc.Lift.Usdc.HistorySlotsCore

/-!
# The branch facts of the USDC `transfer` frame from ledger conditions (U9a)

`ProxyFacts` and `XferFacts` are the word forms the walks meet; here they come from the natural
conditions: the frame decodes to `transfer(dst, v)`, the caller is not the admin word, and the
ledger the footprint reads is unpaused, neither party is frozen or zero, the caller holds `v`, and
the destination's balance stays below `2 ^ 255`.
-/

namespace Blanc.Composition.UsdcLive

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc Blanc.Lift.Token Blanc.SlotFootprint

theorem pKA_eq : pKA = adminSlot := by decide
theorem pKI_eq : pKI = implSlot := by decide

/-- A `transfer` ask is long enough, carries the selector, and its arguments are the words. -/
theorem usdcOp_transfer_words {e : Sevm} {dst : Adr} {v : Nat} (op : usdcOp e = .transfer dst v) :
    68 ≤ e.data.length ∧ Blanc.Sevm.selector e = 0xa9059cbb ∧ dst = (Sevm.dataWord e 4).toAdr ∧
      v = (Sevm.dataWord e 36).toNat := by
  by_cases bal : 36 ≤ e.data.length ∧ Blanc.Sevm.selector e = 0x70a08231
  · unfold usdcOp at op
    rw [ite_eq_left bal] at op
    cases op
  · by_cases xfer : 68 ≤ e.data.length ∧ Blanc.Sevm.selector e = 0xa9059cbb
    · unfold usdcOp at op
      rw [ite_eq_right bal, ite_eq_left xfer] at op
      obtain ⟨rfl, rfl⟩ := Op.transfer.inj op
      exact ⟨xfer.1, xfer.2, rfl, rfl⟩
    · unfold usdcOp at op
      rw [ite_eq_right bal, ite_eq_right xfer] at op
      split at op <;> cases op

theorem ltCheck_zero_of_le {x y : B256} (h : y.toNat ≤ x.toNat) : B256.ltCheck x y = 0 := by
  have : ¬ x < y := by rw [B256.lt_iff_toNat_lt_toNat]; omega
  simp only [B256.ltCheck, this, ↓reduceIte]

theorem short_of_len {n : Nat} (h4 : 4 ≤ n) (hn : n < 2 ^ 256) :
    B256.ltCheck (Nat.toB256 n) (Bytes.toB256 [4]) = 0 :=
  ltCheck_zero_of_le (by rw [B256.toNat_toB256_of_lt hn]; exact h4)

theorem args_of_len {n : Nat} (h : 68 ≤ n) (hn : n < 2 ^ 256) :
    B256.ltCheck (Nat.toB256 n - Bytes.toB256 [4]) (Bytes.toB256 [64]) = 0 := by
  have h4 : (Bytes.toB256 [4]).toNat = 4 := by decide
  have le : Bytes.toB256 [4] ≤ Nat.toB256 n := by
    apply B256.not_lt.mp
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hn, h4]
    omega
  apply ltCheck_zero_of_le
  rw [B256.toNat_sub_eq_of_le _ _ le, B256.toNat_toB256_of_lt hn, h4]
  have h64 : (Bytes.toB256 [64]).toNat = 64 := by decide
  rw [h64]
  omega

/-- `whenNotPaused`'s word from an unpaused flag. -/
theorem paused_word {w : B256} (h : flag20 w = false) :
    (Bytes.toB256 [255] &&& w / Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0]) = 0 := by
  apply B256.toNat_inj
  have d0 : Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ≠ 0 := by
    decide
  have dn : (Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]).toNat =
    2 ^ 160 := by decide
  have fn : (Bytes.toB256 [255]).toNat = 2 ^ 8 - 1 := by decide
  rw [Blanc.B256.toNat_and, B256.toNat_div d0, dn, fn, Nat.and_comm,
    Nat.and_two_pow_sub_one_eq_mod, B256.toNat_zero]
  unfold flag20 at h
  rw [decide_eq_false_iff_not, not_not] at h
  exact h

/-- `_isBlacklisted`'s test from a clear blacklist bit. -/
theorem free_word {w : B256} (h : frozenBit w = false) :
    B256.eqCheck (Bytes.toB256 [1]) (w >>> (Bytes.toB256 [255]).toNat) = 0 := by
  unfold frozenBit at h
  rw [decide_eq_false_iff_not, Nat.not_le] at h
  have z : w >>> (Bytes.toB256 [255]).toNat = 0 := by
    apply B256.toNat_inj
    rw [lit255, toNat_shr255, B256.toNat_zero]
    exact Nat.div_eq_of_lt h
  rw [z]
  decide

theorem frozenBit_of_lt {w : B256} (h : w.toNat < 2 ^ 255) : frozenBit w = false := by
  unfold frozenBit
  rw [decide_eq_false_iff_not, Nat.not_le]
  exact h

theorem balanceBits_of_lt {w : B256} (h : w.toNat < 2 ^ 255) : balanceBits w = w.toNat := by
  unfold balanceBits
  exact Nat.mod_eq_of_lt h

theorem kC_eq (sevm : Sevm) : kC sevm = balSlot sevm.caller := by
  unfold kC balSlot
  rw [lit9]

theorem xTo_toAdr (sevm : Sevm) : (xTo sevm).toAdr = (Sevm.dataWord sevm 4).toAdr := by
  unfold xTo
  rw [Blanc.Lift.word_ff20, Jaune.toAdr_toB256]
  rfl

theorem kT_eq (sevm : Sevm) : kT (xTo sevm) = balSlot (Sevm.dataWord sevm 4).toAdr := by
  unfold kT balSlot
  rw [lit9, xTo_toAdr]

theorem xVal_eq (sevm : Sevm) : xVal sevm = Sevm.dataWord sevm 36 := by
  unfold xVal
  rw [lit36]

local notation "m20" => Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
local notation "l255" => Bytes.toB256 [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

theorem eqCheck_ne {x y : B256} (h : x ≠ y) : B256.eqCheck x y = 0 := by
  simp only [B256.eqCheck, h, ↓reduceIte]

theorem adr_toB256_ne_zero {a : Adr} (h : a ≠ 0) : a.toB256 ≠ 0 := fun e =>
  h (Adr.toB256_inj (e.trans (by decide)))

/-- **The proxy's branch facts** for a `transfer` call by a caller other than the admin word. -/
theorem proxyFacts_of {sevm : Sevm} {pre : Devm} (len : 4 ≤ sevm.data.length)
    (hlen : sevm.data.length < 2 ^ 256) (sel : Blanc.Sevm.selector sevm = 0xa9059cbb)
    (adm : sevm.caller ≠ ((Devm.getStor pre sevm.currentTarget).get adminSlot).toAdr) :
    ProxyFacts sevm pre 0xa9059cbb := by
  refine ⟨short_of_len len hlen, (dispatchWord_eq_selector sevm).trans sel, by decide, by decide,
    by decide, by decide, by decide, ?_⟩
  apply eqCheck_ne
  rw [Blanc.ff20_and_word, Blanc.ff20_and_word, Jaune.toAdr_toB256, gsv, pKA_eq]
  intro e
  exact adm (Adr.toB256_inj e)

/-- **The implementation's branch facts** for `transfer(dst, v)` from the guards on the storage. -/
theorem xferFacts_of {sevm : Sevm} {pre : Devm} (value : sevm.value = 0)
    (len : 68 ≤ sevm.data.length) (hlen : sevm.data.length < 2 ^ 256)
    (sel : Blanc.Sevm.selector sevm = 0xa9059cbb)
    (p0 : flag20 ((Devm.getStor pre sevm.currentTarget).get 1) = false)
    (fc : frozenBit ((Devm.getStor pre sevm.currentTarget).get (balSlot sevm.caller)) = false)
    (fd : frozenBit ((Devm.getStor pre sevm.currentTarget).get
      (balSlot (Sevm.dataWord sevm 4).toAdr)) = false)
    (c0 : sevm.caller ≠ 0) (d0 : (Sevm.dataWord sevm 4).toAdr ≠ 0)
    (hv : (Sevm.dataWord sevm 36).toNat ≤
      balanceBits ((Devm.getStor pre sevm.currentTarget).get (balSlot sevm.caller)))
    (hb : balanceBits ((Devm.getStor pre sevm.currentTarget).get
      (balSlot (Sevm.dataWord sevm 4).toAdr)) + (Sevm.dataWord sevm 36).toNat < 2 ^ 255)
    (hne : (Sevm.dataWord sevm 4).toAdr ≠ sevm.caller →
      balSlot (Sevm.dataWord sevm 4).toAdr ≠ balSlot sevm.caller) :
    XferFacts sevm pre := by
  have h4 : 4 ≤ sevm.data.length := by omega
  have l1 : Bytes.toB256 [1] = 1 := lit1
  have hD : (l255 &&& (Devm.getStor pre sevm.currentTarget).get (balSlot sevm.caller)) -
      Sevm.dataWord sevm 36 = Nat.toB256
        (balanceBits ((Devm.getStor pre sevm.currentTarget).get (balSlot sevm.caller)) -
          (Sevm.dataWord sevm 36).toNat) := by
    have le : Sevm.dataWord sevm 36 ≤
        l255 &&& (Devm.getStor pre sevm.currentTarget).get (balSlot sevm.caller) := by
      apply B256.not_lt.mp
      rw [B256.lt_iff_toNat_lt_toNat, l255_and_toNat]
      omega
    apply B256.toNat_inj
    rw [B256.toNat_sub_eq_of_le _ _ le, l255_and_toNat, B256.toNat_toB256_of_lt (by
      have := Nat.mod_lt ((Devm.getStor pre sevm.currentTarget).get (balSlot sevm.caller)).toNat
        (Nat.two_pow_pos 255)
      unfold balanceBits; omega)]
  have bc : balanceBits ((Devm.getStor pre sevm.currentTarget).get (balSlot sevm.caller)) < 2 ^ 255 :=
    Nat.mod_lt _ (Nat.two_pow_pos 255)
  have dlt : (Nat.toB256 (balanceBits ((Devm.getStor pre sevm.currentTarget).get
      (balSlot sevm.caller)) - (Sevm.dataWord sevm 36).toNat)).toNat <
      2 ^ 255 := by
    rw [B256.toNat_toB256_of_lt (by omega)]; omega
  refine ⟨value, short_of_len h4 hlen, args_of_len len hlen, sel, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [gsv]; exact paused_word p0
  · rw [gsv, kC_eq, l1, ← l1]; exact free_word fc
  · rw [gsv, kT_eq, l1, ← l1]; exact free_word fd
  · exact adr_toB256_ne_zero c0
  · rw [xTo_toAdr]; exact adr_toB256_ne_zero d0
  · apply B256.gtCheck_eq_zero_of_toNat_le
    rw [xVal_eq, gsv, kC_eq, l255_and_toNat]; exact hv
  · rw [xVal_eq, gsv, kC_eq, kT_eq, hD, l255_and_toNat]
    by_cases e : (Sevm.dataWord sevm 4).toAdr = sevm.caller
    · rw [e, Stor.get_set_self, balanceBits_of_lt dlt, B256.toNat_toB256_of_lt (by omega)]
      omega
    · rw [Stor.get_set_ne _ (hne e).symm]; omega
  · rw [gsv, kC_eq, kT_eq, xVal_eq, hD, l1, ← l1]
    apply free_word
    by_cases e : (Sevm.dataWord sevm 4).toAdr = sevm.caller
    · rw [e, Stor.get_set_self]; exact frozenBit_of_lt dlt
    · rw [Stor.get_set_ne _ (hne e).symm]; exact fd

/-- **The child's storage at the proxy is `transfer`'s debit and credit** (`frame_transfer`, on the
child's execution). -/
theorem frameChild_stor {sevm : Sevm} {pre : Devm} {X : Nat} (fork : CoveredFork sevm.benvStat.fork)
    (static : sevm.isStatic = false) (hlen : sevm.data.length < 2 ^ 256)
    (sel : Blanc.Sevm.selector sevm = 0xa9059cbb) (xf : XferFacts sevm pre)
    (hcode : (pBase sevm pre).state.getCode (dI sevm pre) = Impl.code)
    (hfwd : childXferCost sevm pre + 415 ≤ dFwd sevm pre (frameY sevm pre X)) :
    Devm.getStor (frameChild sevm pre X) sevm.currentTarget =
      creditStor (debitStor (Devm.getStor pre sevm.currentTarget) sevm.caller
        (Sevm.dataWord sevm 36).toNat) (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toNat := by
  have hd := dMsg_data sevm pre (frameY sevm pre X) hlen
  have hexec := child_xfer_exec (sevm := sevm) (b := pre) (Y := frameY sevm pre X) fork static hcode
    (xf.transport rfl hd rfl rfl (fun a => by
      show Devm.getStor (pBase sevm pre) a = _
      rw [Blanc.afterSload_getStor, Blanc.afterSload_getStor])) hfwd
  obtain ⟨run⟩ := (exec_iff_exec_eq _ _ _ _).mpr hexec
  have fork' : CoveredFork (initSevm (dMsg sevm pre (frameY sevm pre X))).benvStat.fork := fork
  obtain ⟨f, hf, r⟩ := lift_sound Impl.cert_check hcode fork' run
  rw [show Impl.cert.prog[0]? = some Impl.t_0000_c0 from rfl] at hf
  cases hf
  rw [St.self (d := initDevm (dMsg sevm pre (frameY sevm pre X))) rfl rfl] at r
  have hw : Sevm.dataWord (initSevm (dMsg sevm pre (frameY sevm pre X))) = Sevm.dataWord sevm := by
    funext i; unfold Sevm.dataWord; rw [hd]
  have sel' : Blanc.Sevm.selector (initSevm (dMsg sevm pre (frameY sevm pre X))) = 0xa9059cbb := by
    unfold Blanc.Sevm.selector; rw [hw]; exact sel
  have h := (frame_transfer fork' sel' r).2.2.2.2.2.2.2.2
  rw [hw] at h
  have hs : ∀ a, Devm.getStor (initDevm (dMsg sevm pre (frameY sevm pre X))) a =
      Devm.getStor pre a := fun a => by
    show Devm.getStor (pBase sevm pre) a = _
    rw [Blanc.afterSload_getStor, Blanc.afterSload_getStor]
  rw [hs] at h
  exact h

end Blanc.Composition.UsdcLive
