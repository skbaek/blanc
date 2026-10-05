import Blanc.Lift.ExactWalk
import Blanc.ForwardCall
import Blanc.StorageOnlySpec

/-!
# Gas-exact walk step: a value-bearing `CALL` to an account without code

A solc `address.transfer(v)` is a `CALL` with an empty input window, an empty output window and no
forwarded gas (the stipend covers the recipient).  When the recipient has no code (an externally
owned account) and is no precompile, the callee runs nothing and gives the whole stipend back, so the
caller's gas falls by exactly the fixed part of the charge less the stipend:

* `rx_callNZ`: the step for a nonzero value, at the net charge `callNet` (account access, a possible
  new-account charge, the value-transfer charge, less the stipend);

The step exposes the state the `CALL` leaves (`CallPost`): the balances moved, storage kept, output,
logs, error and refund counter kept and the emptiness of the accounts to delete kept.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- The net gas a value-bearing `CALL` to a code-free recipient costs its caller: the account-access
charge (warm/cold), the new-account charge when the recipient is empty, the value-transfer charge, less
the stipend the callee returns unspent. -/
def callNet (b : Devm) (a : Adr) : Nat :=
  accessCost a b.accessedAddresses + (if ¬ (b.getAcct a).Empty then 0 else gNewAccount) +
    gasCallValue - gCallStipend

/-- What a `CALL` to a code-free recipient leaves besides the stack, memory and gas. -/
structure CallPost (sevm : Sevm) (b post : Devm) (a : Adr) (v : B256) : Prop where
  output : post.output = b.output
  logs : post.logs = b.logs
  error : post.error = b.error
  refund : post.refundCounter = b.refundCounter
  accountsToDelete : post.accountsToDelete.isEmpty = b.accountsToDelete.isEmpty
  state : ∃ stmid, b.state.subBal sevm.currentTarget v = some stmid ∧ post.state = stmid.addBal a v

/-- A `CALL` to a code-free recipient keeps every account's storage: the balances move and nothing
else of the world changes. -/
theorem CallPost.getStor {sevm : Sevm} {b post : Devm} {a : Adr} {v : B256}
    (h : CallPost sevm b post a v) (x : Adr) : Devm.getStor post x = Devm.getStor b x := by
  obtain ⟨stmid, hsub, hst⟩ := h.state
  show post.state.getStor x = b.state.getStor x
  rw [hst]
  exact getStor_subBal_addBal hsub

section Steps

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  {f : SFunc} {o : Outcome}

/-- **`CALL` with nonzero value and no forwarded gas, to a recipient without code.**  The recipient
`cw` has empty code and is no precompile, the caller is not static, the frame is not the outermost, and
the caller's ether covers the value; the gas left before the `CALL` exceeds the gas after by exactly
`callNet`, and after it must cover the stipend the callee returns.  Both windows are empty. -/
theorem callNZ_ex {gw cw vw iiw isw oiw osw : B256} {c : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hvw : vw ≠ 0) (hgw : gw.toNat = 0)
    (hisw : isw.toNat = 0) (hosw : osw.toNat = 0)
    (hcode : (b.getCode cw.toAdr).size = 0) (hprec : sevm.benvStat.rules.isPrecomp cw.toAdr = false)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hbal : ¬ (b.getAcct sevm.currentTarget).bal < vw) (hroom : S.length < 1024)
    (hc : c = callNet b cw.toAdr) (hgas : gCallStipend ≤ G) :
    ∃ post, Ninst.RunCompiled sevm
        (St b (gw :: cw :: vw :: iiw :: isw :: oiw :: osw :: S) M (G + c)) (.exec .call) post ∧
      CallPost sevm b post cw.toAdr vw ∧ post = St post (1 :: S) M G := by
  have hvw' : vw.toNat ≠ 0 := fun h => hvw (by apply B256.toNat_inj; rw [h]; rfl)
  have hext : ∀ (S' : List B256) (G' : Nat), ((St b S' M G').extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]) = 0 := by
    intro S' G'
    simp only [Devm.extCost, memExtsSize, memExtSize, hosw, ↓reduceIte, hisw, St.memory, tsub_self]
  have hnodel : getDelegatedCodeAddress (b.state.getCode cw.toAdr) = none := by
    have h23 : ¬ isValidDelegation (b.state.getCode cw.toAdr) := fun h => by
      have := h.1
      change (b.getCode cw.toAdr).size = eoaDelegatedCodeLength at this
      rw [hcode] at this
      exact absurd this (by decide)
    unfold getDelegatedCodeAddress
    simp only [h23, ↓reduceIte]
  set devm : Devm := St b (gw :: cw :: vw :: iiw :: isw :: oiw :: osw :: S) M (G + c) with hdevm
  set X : Devm := addAccessedAddress (devm.setMach ⟨S, devm.memory, devm.gasLeft, devm.stateGas⟩)
    cw.toAdr with hX
  have hdel : accessDelegation X cw.toAdr =
      ⟨false, cw.toAdr, b.state.getCode cw.toAdr, 0, X⟩ := by
    unfold accessDelegation
    show (match getDelegatedCodeAddress (b.state.getCode cw.toAdr) with
      | some adr => _
      | none => _) = _
    rw [hnodel]
    rfl
  have hacc : callNet b cw.toAdr + gCallStipend =
      accessCost cw.toAdr b.accessedAddresses +
        (if ¬ (b.getAcct cw.toAdr).Empty then 0 else gNewAccount) + gasCallValue := by
    unfold callNet
    generalize accessCost cw.toAdr b.accessedAddresses = x
    generalize (if ¬ (b.getAcct cw.toAdr).Empty then 0 else gNewAccount) = y
    have : gCallStipend ≤ gasCallValue := by decide
    omega
  have hsplit : calculateMsgCallGas vw.toNat gw.toNat X.gasLeft 0
      (accessCost cw.toAdr b.accessedAddresses +
        (if ¬ (b.getAcct cw.toAdr).Empty then 0 else gNewAccount) + gasCallValue) =
      ⟨accessCost cw.toAdr b.accessedAddresses +
        (if ¬ (b.getAcct cw.toAdr).Empty then 0 else gNewAccount) + gasCallValue, gCallStipend⟩ := by
    unfold calculateMsgCallGas
    simp only [hgw, hvw', ite_false]
    split_ifs <;> simp only [zero_add, tsub_zero, zero_le, inf_of_le_left, add_zero]
  obtain ⟨post, hrun, hstk, hmem, hgasl, herr, hout, hrd, hlogs, hrefund, hdelete, stmid, hsub,
    hstate⟩ := Ninst.runCompiled_call_nonzero_codeFree (sevm := sevm) (devm := devm)
    (gw := gw) (cw := cw) (vw := vw) (iiw := iiw) (isw := isw) (oiw := oiw) (osw := osw) (s := S)
    (dp := false) (dadr := cw.toAdr) (code := b.state.getCode cw.toAdr) (dgc := 0) (d1 := X)
    (ext := 0)
    (acc := accessCost cw.toAdr b.accessedAddresses)
    (create := if ¬ (b.getAcct cw.toAdr).Empty then 0 else gNewAccount)
    (mcc := accessCost cw.toAdr b.accessedAddresses +
      (if ¬ (b.getAcct cw.toAdr).Empty then 0 else gNewAccount) + gasCallValue)
    (mcs := gCallStipend)
    hfork rfl hvw (by
      have := hext S (G + c)
      simpa only [hdevm, St, Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach,
        Devm.stateGas_setMach] using this) hdel rfl rfl hsplit
    (by
      have := hacc
      have hgas' : X.gasLeft = G + c := rfl
      rw [hgas']
      generalize accessCost cw.toAdr b.accessedAddresses = x at this ⊢
      generalize (if ¬ (b.getAcct cw.toAdr).Empty then 0 else gNewAccount) = y at this ⊢
      have e1 : gCallStipend = 2300 := rfl
      have e2 : gasCallValue = 9000 := rfl
      omega)
    hstatic hbal hdepth hprec hcode (by omega)
  have hmem' : post.memory = M := by
    rw [hmem]
    have hM : devm.memory = M := rfl
    rw [hM]
    simp only [Mem.extends, memExtsSize, memExtSize, hosw, ↓reduceIte, hisw]
  have hgas'' : post.gasLeft = G := by
    rw [hgasl]
    have hgas' : X.gasLeft = G + c := rfl
    rw [hgas']
    have := hacc
    generalize accessCost cw.toAdr b.accessedAddresses = x at this ⊢
    generalize (if ¬ (b.getAcct cw.toAdr).Empty then 0 else gNewAccount) = y at this ⊢
    have e1 : gCallStipend = 2300 := rfl
    have e2 : gasCallValue = 9000 := rfl
    omega
  have hpost : post = St post (1 :: S) M G := by
    have := St.self hstk hmem'
    rwa [hgas''] at this
  exact ⟨post, hrun, ⟨hout, hlogs, herr, hrefund, hdelete, ⟨stmid, hsub, hstate⟩⟩, hpost⟩

/-- The step form of `callNZ_ex`. -/
theorem rx_callNZ {gw cw vw iiw isw oiw osw : B256} {c : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hvw : vw ≠ 0) (hgw : gw.toNat = 0)
    (hisw : isw.toNat = 0) (hosw : osw.toNat = 0)
    (hcode : (b.getCode cw.toAdr).size = 0) (hprec : sevm.benvStat.rules.isPrecomp cw.toAdr = false)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hbal : ¬ (b.getAcct sevm.currentTarget).bal < vw) (hroom : S.length < 1024)
    (hc : c = callNet b cw.toAdr) (hgas : gCallStipend ≤ G)
    (k : ∀ post : Devm, CallPost sevm b post cw.toAdr vw →
      SFunc.RunExact fs sevm (St post (1 :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (gw :: cw :: vw :: iiw :: isw :: oiw :: osw :: S) M (G + c))
      (.next (.exec .call) f) o := by
  obtain ⟨post, hrun, hp, he⟩ := callNZ_ex (S := S) hfork hvw hgw hisw hosw hcode hprec
    hstatic hdepth hbal hroom hc hgas
  refine .next hrun ?_
  rw [he]
  exact k post hp

/-- **`CALL` with zero value and the stipend as the gas argument, to a recipient without code.**  No
value moves; the callee gets `2300` gas and returns it all, so the caller pays only the account
access. -/
theorem callZ_ex {gw cw iiw isw oiw osw : B256} {c : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hgw : gw.toNat = 2300)
    (hisw : isw.toNat = 0) (hosw : osw.toNat = 0)
    (hcode : (b.getCode cw.toAdr).size = 0) (hprec : sevm.benvStat.rules.isPrecomp cw.toAdr = false)
    (hdepth : sevm.depth ≠ 0) (hroom : S.length < 1024)
    (hc : c = accessCost cw.toAdr b.accessedAddresses) :
    ∃ post, Ninst.RunCompiled sevm
        (St b (gw :: cw :: 0 :: iiw :: isw :: oiw :: osw :: S) M (G + c)) (.exec .call) post ∧
      CallPost sevm b post cw.toAdr 0 ∧ post = St post (1 :: S) M G := by
  have hext : ∀ (S' : List B256) (G' : Nat), ((St b S' M G').extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]) = 0 := by
    intro S' G'
    simp only [Devm.extCost, memExtsSize, memExtSize, hosw, ↓reduceIte, hisw, St.memory, tsub_self]
  have hnodel : getDelegatedCodeAddress (b.state.getCode cw.toAdr) = none := by
    have h23 : ¬ isValidDelegation (b.state.getCode cw.toAdr) := fun h => by
      have := h.1
      change (b.getCode cw.toAdr).size = eoaDelegatedCodeLength at this
      rw [hcode] at this
      exact absurd this (by decide)
    unfold getDelegatedCodeAddress
    simp only [h23, ↓reduceIte]
  set devm : Devm := St b (gw :: cw :: 0 :: iiw :: isw :: oiw :: osw :: S) M (G + c) with hdevm
  set X : Devm := addAccessedAddress (devm.setMach ⟨S, devm.memory, devm.gasLeft, devm.stateGas⟩)
    cw.toAdr with hX
  have hdel : accessDelegation X cw.toAdr =
      ⟨false, cw.toAdr, b.state.getCode cw.toAdr, 0, X⟩ := by
    unfold accessDelegation
    show (match getDelegatedCodeAddress (b.state.getCode cw.toAdr) with
      | some adr => _
      | none => _) = _
    rw [hnodel]
    rfl
  have hg' : X.gasLeft = G + c := rfl
  have hle : min 2300 (except64th G) ≤ G := (Nat.min_le_right _ _).trans (Nat.sub_le _ _)
  have hsplit : calculateMsgCallGas 0 gw.toNat X.gasLeft 0 (accessCost cw.toAdr b.accessedAddresses) =
      ⟨min 2300 (except64th G) + accessCost cw.toAdr b.accessedAddresses,
        min 2300 (except64th G)⟩ := by
    unfold calculateMsgCallGas
    rw [hg', hgw, hc]
    have : ¬ (G + accessCost cw.toAdr b.accessedAddresses < accessCost cw.toAdr b.accessedAddresses + 0) := by
      omega
    simp only [this, ite_false]
    simp only [tsub_zero, add_tsub_cancel_right, ↓reduceIte, add_zero]
  obtain ⟨post, hrun, hstk, hmem, hgasl, herr, hout, hrd, hlogs, hrefund, hdelete, stmid, hsub,
    hstate⟩ := Ninst.runCompiled_call_zero_value_codeFree (sevm := sevm) (devm := devm)
    (gw := gw) (cw := cw) (iiw := iiw) (isw := isw) (oiw := oiw) (osw := osw) (s := S)
    (dp := false) (dadr := cw.toAdr) (code := b.state.getCode cw.toAdr) (dgc := 0) (d1 := X)
    (ext := 0) (acc := accessCost cw.toAdr b.accessedAddresses)
    (mcc := min 2300 (except64th G) + accessCost cw.toAdr b.accessedAddresses)
    (mcs := min 2300 (except64th G))
    hfork rfl (by
      have := hext S (G + c)
      simpa only [hdevm, St, Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach,
        Devm.stateGas_setMach] using this) hdel rfl hsplit
    (by rw [hg', hc]; omega) hdepth hprec hcode (by omega)
  have hmem' : post.memory = M := by
    rw [hmem]
    have hM : devm.memory = M := rfl
    rw [hM]
    simp only [Mem.extends, memExtsSize, memExtSize, hosw, ↓reduceIte, hisw]
  have hgas'' : post.gasLeft = G := by
    rw [hgasl, hg', hc]
    omega
  have hpost : post = St post (1 :: S) M G := by
    have := St.self hstk hmem'
    rwa [hgas''] at this
  exact ⟨post, hrun, ⟨hout, hlogs, herr, hrefund, hdelete, ⟨stmid, hsub, hstate⟩⟩, hpost⟩

/-- The step form of `callZ_ex`. -/
theorem rx_callZ {gw cw iiw isw oiw osw : B256} {c : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hgw : gw.toNat = 2300)
    (hisw : isw.toNat = 0) (hosw : osw.toNat = 0)
    (hcode : (b.getCode cw.toAdr).size = 0) (hprec : sevm.benvStat.rules.isPrecomp cw.toAdr = false)
    (hdepth : sevm.depth ≠ 0) (hroom : S.length < 1024)
    (hc : c = accessCost cw.toAdr b.accessedAddresses)
    (k : ∀ post : Devm, CallPost sevm b post cw.toAdr 0 →
      SFunc.RunExact fs sevm (St post (1 :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (gw :: cw :: 0 :: iiw :: isw :: oiw :: osw :: S) M (G + c))
      (.next (.exec .call) f) o := by
  obtain ⟨post, hrun, hp, he⟩ := callZ_ex (S := S) hfork hgw hisw hosw hcode hprec hdepth
    hroom hc
  refine .next hrun ?_
  rw [he]
  exact k post hp

end Steps

end Blanc.Lift
