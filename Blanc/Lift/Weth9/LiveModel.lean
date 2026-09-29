import Blanc.Lift.Weth9.LiveWriters

/-!
# The deployed WETH9's writers realise the model's step, gas-exact

The frame-level liveness of `LiveWriters.lean` from the footprint invariant.  A footprint `FootInv K`
of the pre-storage over the tracked keys `K`, the freshness of the call's own keys (`KeysFresh`, so the
call's keys extend the footprint: `Key.extend K c.keys`), and the model's acceptance of the call at the
extended footprint (`(ledger K' stor).step c = some l'`, the model's `require`s at the tracked words:
`balanceOf[caller] ≥ wad`, the allowance cases of `transferFrom`) give:

* the deployed code executes the writer to success at exactly its cost (`LiveWriters.lean`), and
* the storage it leaves reads, at the extended footprint, as the model's next ledger `l'`.

For `withdraw` the footprint also supplies the ether: a tracked balance is backed by the contract's
balance (`FootInv.balance_le`), so the send `wad ≤ balanceOf[caller]` is covered.
-/

namespace Blanc.Lift.Weth9

open Jaune Blanc Blanc.Lift

/-- The `approve` call a frame decodes. -/
def apCall (sevm : Sevm) : Call :=
  .approve sevm.caller (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36)

/-- The `deposit` call a frame decodes. -/
def dpCall (sevm : Sevm) : Call := .deposit sevm.caller sevm.value

/-- The `transfer` call a frame decodes. -/
def trCall (sevm : Sevm) : Call :=
  .transfer sevm.caller (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36)

/-- The `transferFrom` call a frame decodes. -/
def tfCall (sevm : Sevm) : Call :=
  .transferFrom sevm.caller (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr
    (Sevm.dataWord sevm 68)

/-- The `withdraw` call a frame decodes. -/
def wdCall (sevm : Sevm) : Call := .withdraw sevm.caller (Sevm.dataWord sevm 4)

/-- **A storage effect of an accepted call is the model's next ledger** at the extended footprint. -/
theorem model_ledger {K : Key → Prop} {s s' : Stor} {b : B256} {c : Call} {l' : Ledger}
    (hinv : FootInv K s b) (hfresh : KeysFresh K c.keys) (hstor : c.stor s = some s')
    (hok : (ledger (Key.extend K c.keys) s).step c = some l') :
    ledger (Key.extend K c.keys) s' = l' := by
  have h := Call.stor_ledger (hinv.extend hfresh).inj (fun k hk => Or.inr hk) hstor
  rw [hok] at h
  exact (Option.some.inj h).symm

/-- **`approve` realises the model's step, gas-exact.** -/
theorem weth9_approve_model_live {sevm : Sevm} {pre : Devm} {G : Nat} {K : Key → Prop} {l' : Ledger}
    (h_code : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (h_static : sevm.isStatic = false) (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = apSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (hinv : FootInv K (Devm.getStor pre sevm.currentTarget) (pre.getBal sevm.currentTarget))
    (hfresh : KeysFresh K (apCall sevm).keys)
    (hok : (ledger (Key.extend K (apCall sevm).keys) (Devm.getStor pre sevm.currentTarget)).step
      (apCall sevm) = some l')
    (h_gas : pre.gasLeft = G + approveGas sevm pre) (hG : 380 ≤ G) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧ post.gasLeft = G ∧
      post.output = (1 : B256).toBytes ∧
      ledger (Key.extend K (apCall sevm).keys) (Devm.getStor post sevm.currentTarget) = l' := by
  obtain ⟨post, hex, hg, ho, hst⟩ := weth9_approve_live h_code hfork h_static h_value h_sel h_len
    h_len' h_stack h_mem h_gas hG
  refine ⟨post, hex, hg, ho, model_ledger hinv hfresh ?_ hok⟩
  simp only [apCall, Call.stor, hst]

/-- **`deposit()` realises the model's step, gas-exact.** -/
theorem weth9_deposit_model_live {sevm : Sevm} {pre : Devm} {G : Nat} {K : Key → Prop} {l' : Ledger}
    (h_code : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (h_static : sevm.isStatic = false) (h_sel : Sevm.selector sevm = dpSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (hinv : FootInv K (Devm.getStor pre sevm.currentTarget) (pre.getBal sevm.currentTarget))
    (hfresh : KeysFresh K (dpCall sevm).keys)
    (hok : (ledger (Key.extend K (dpCall sevm).keys) (Devm.getStor pre sevm.currentTarget)).step
      (dpCall sevm) = some l')
    (h_gas : pre.gasLeft = G + depositGas sevm pre) (hG : 844 ≤ G) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧ post.gasLeft = G ∧ post.output = pre.output ∧
      ledger (Key.extend K (dpCall sevm).keys) (Devm.getStor post sevm.currentTarget) = l' := by
  obtain ⟨post, hex, hg, ho, hst⟩ := weth9_deposit_live h_code hfork h_static h_sel h_len h_len'
    h_stack h_mem h_gas hG
  refine ⟨post, hex, hg, ho, model_ledger hinv hfresh ?_ hok⟩
  simp only [dpCall, Call.stor, hst]

/-- **`transfer` realises the model's step, gas-exact.** -/
theorem weth9_transfer_model_live {sevm : Sevm} {pre : Devm} {G : Nat} {K : Key → Prop} {l' : Ledger}
    (h_code : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (h_static : sevm.isStatic = false) (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = trSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (hinv : FootInv K (Devm.getStor pre sevm.currentTarget) (pre.getBal sevm.currentTarget))
    (hfresh : KeysFresh K (trCall sevm).keys)
    (hok : (ledger (Key.extend K (trCall sevm).keys) (Devm.getStor pre sevm.currentTarget)).step
      (trCall sevm) = some l')
    (h_gas : pre.gasLeft = G + transferGas sevm pre) (hG : 353 ≤ G) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧ post.gasLeft = G ∧
      post.output = (1 : B256).toBytes ∧
      ledger (Key.extend K (trCall sevm).keys) (Devm.getStor post sevm.currentTarget) = l' := by
  obtain ⟨s', hs'⟩ := Option.ne_none_iff_exists'.mp
    (Call.stor_ne_none_of_step (fun k hk => Or.inr hk) hok)
  have hs'' : xferStorStep (Devm.getStor pre sevm.currentTarget) sevm.caller sevm.caller
      (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36) = some s' := hs'
  have hle : Sevm.dataWord sevm 36 ≤
      pre.getStorVal sevm.currentTarget (balSlot sevm.caller) := (xferStorStep_ok hs'').1
  obtain ⟨post, hex, hg, ho, hst⟩ := weth9_transfer_live h_code hfork h_static h_value h_sel h_len
    h_len' h_stack h_mem hle h_gas hG
  refine ⟨post, hex, hg, ho, model_ledger hinv hfresh ?_ hok⟩
  simpa only [trCall, Call.stor] using hst

/-- **`transferFrom` realises the model's step, gas-exact**: the three allowance cases are one theorem,
at `transferFromGas`. -/
theorem weth9_transferFrom_model_live {sevm : Sevm} {pre : Devm} {G : Nat} {K : Key → Prop}
    {l' : Ledger}
    (h_code : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (h_static : sevm.isStatic = false) (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = tfSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (hinv : FootInv K (Devm.getStor pre sevm.currentTarget) (pre.getBal sevm.currentTarget))
    (hfresh : KeysFresh K (tfCall sevm).keys)
    (hok : (ledger (Key.extend K (tfCall sevm).keys) (Devm.getStor pre sevm.currentTarget)).step
      (tfCall sevm) = some l')
    (h_gas : pre.gasLeft = G + transferFromGas sevm pre) (hG : 377 ≤ G) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧ post.gasLeft = G ∧
      post.output = (1 : B256).toBytes ∧
      ledger (Key.extend K (tfCall sevm).keys) (Devm.getStor post sevm.currentTarget) = l' := by
  obtain ⟨s', hs'⟩ := Option.ne_none_iff_exists'.mp
    (Call.stor_ne_none_of_step (fun k hk => Or.inr hk) hok)
  have hs'' : xferStorStep (Devm.getStor pre sevm.currentTarget) sevm.caller
      (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68) =
      some s' := hs'
  obtain ⟨post, hex, hg, ho, hst⟩ := weth9_transferFrom_live h_code hfork h_static h_value h_sel
    h_len h_len' h_stack h_mem hs'' h_gas hG
  refine ⟨post, hex, hg, ho, model_ledger hinv hfresh ?_ hok⟩
  simpa only [tfCall, Call.stor] using hst

/-- **`withdraw` to an externally owned account realises the model's step, gas-exact.**  The footprint
backs the send: the caller's tracked balance is covered by the contract's ether. -/
theorem weth9_withdraw_model_live {sevm : Sevm} {pre : Devm} {G : Nat} {K : Key → Prop} {l' : Ledger}
    (h_code : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (h_static : sevm.isStatic = false) (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = wdSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty) (h_depth : sevm.depth ≠ 0)
    (h_eoa : (pre.getCode sevm.caller).size = 0)
    (h_prec : sevm.benvStat.rules.isPrecomp sevm.caller = false)
    (hinv : FootInv K (Devm.getStor pre sevm.currentTarget) (pre.getBal sevm.currentTarget))
    (hfresh : KeysFresh K (wdCall sevm).keys)
    (hok : (ledger (Key.extend K (wdCall sevm).keys) (Devm.getStor pre sevm.currentTarget)).step
      (wdCall sevm) = some l')
    (h_gas : pre.gasLeft = G + withdrawAnyGas sevm pre) (hG : 811 ≤ G) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧ post.gasLeft = G ∧ post.output = pre.output ∧
      ledger (Key.extend K (wdCall sevm).keys) (Devm.getStor post sevm.currentTarget) = l' := by
  obtain ⟨s', hs'⟩ := Option.ne_none_iff_exists'.mp
    (Call.stor_ne_none_of_step (fun k hk => Or.inr hk) hok)
  have hnlt : ¬ (Devm.getStor pre sevm.currentTarget).get (balSlot sevm.caller) <
      Sevm.dataWord sevm 4 := by
    intro hlt
    simp [wdCall, Call.stor, hlt] at hs'
  have hle : Sevm.dataWord sevm 4 ≤ pre.getStorVal sevm.currentTarget (balSlot sevm.caller) :=
    B256.not_lt.mp hnlt
  have hbk : (Key.extend K (wdCall sevm).keys) (.bal sevm.caller) := Or.inr (by simp [wdCall, Call.keys])
  have hb := (hinv.extend hfresh).balance_le hbk
  have h_eth : ¬ (pre.getAcct sevm.currentTarget).bal < Sevm.dataWord sevm 4 := by
    intro hlt
    have h1 := B256.toNat_lt_toNat hlt
    have h2 := B256.toNat_le_toNat hle
    have h3 : (pre.getStorVal sevm.currentTarget (balSlot sevm.caller)).toNat ≤
        (pre.getAcct sevm.currentTarget).bal.toNat := hb
    omega
  obtain ⟨post, hex, hg, ho, hst, hother⟩ := weth9_withdraw_any_live h_code hfork h_static h_value
    h_sel h_len h_len' h_stack h_mem h_depth hle h_eoa h_prec h_eth h_gas hG
  refine ⟨post, hex, hg, ho, model_ledger hinv hfresh ?_ hok⟩
  simp only [wdCall, Call.stor, hnlt, ↓reduceIte, hst]
  rfl

end Blanc.Lift.Weth9
