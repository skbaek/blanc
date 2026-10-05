import Blanc.Lift.UniswapV2Pair.LPMintCore
import Blanc.Lift.UniswapV2Pair.TransferSource

/-! Finite source accounting for the actual internal mint62 and its literal callers. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def lpMintTouched (recipient : Adr) : List WriterKey := [.balance recipient]

def lpMintSupplyState (st : State) (supply : B256) : State :=
  { st with totalSupply := supply }

def lpMintSourceState (st : State) (recipient : Adr) (value : B256) : State :=
  balanceSourceState (lpMintSupplyState st (st.totalSupply + value)) recipient
    (st.balanceOf recipient + value)

theorem lpMintSupplyState_value (st : State) (supply : B256) (k : WriterKey) :
    k.value (lpMintSupplyState st supply) = k.value st := by
  cases k <;> rfl

/-- A supply write preserves all tagged rows and all other fixed physical words. -/
theorem WriterRep.lpMint_supply_store {K : WriterKey → Prop} {s : Stor} {st : State}
    {supply : B256} (rep : WriterRep K s st) :
    WriterRep K (s.set 0 supply) (lpMintSupplyState st supply) := by
  have unchanged (n : B256) (off : (0 : B256) ≠ n) :
      (s.set 0 supply).get n = s.get n := Stor.get_set_ne s off supply
  refine ⟨rep.finite, ?_, ?_, rep.inj, rep.apart, ?_, ?_⟩
  · dsimp only [WriterFixedMatches, lpMintSupplyState]
    rw [Stor.get_set_self, unchanged 3 (by decide), unchanged 5 (by decide),
      unchanged 6 (by decide), unchanged 7 (by decide), unchanged 8 (by decide),
      unchanged 9 (by decide), unchanged 10 (by decide), unchanged 11 (by decide),
      unchanged 12 (by decide)]
    exact ⟨rfl, rep.fixed.2⟩
  · intro n nonzero
    by_cases zero : n = 0
    · exact .inl (zero.symm ▸ (by decide : (0 : B256) ∈ writerFixedSlots))
    · rw [unchanged n (Ne.symm zero)] at nonzero
      exact rep.support n nonzero
  · intro k tracked
    have off : (0 : B256) ≠ k.slot :=
      fun eq => rep.apart k tracked (eq ▸ (by decide : (0 : B256) ∈ writerFixedSlots))
    rw [unchanged k.slot off, lpMintSupplyState_value]
    exact rep.selected k tracked
  · intro k outside
    rw [lpMintSupplyState_value]
    exact rep.logicalZero k outside

theorem WriterRep.lpMint_store {K : WriterKey → Prop} {s : Stor} {st : State}
    {recipient : Adr} {value : B256} (rep : WriterRep K s st)
    (fresh : WriterFreshKeys K (lpMintTouched recipient)) :
    WriterRep (WriterExtend K (lpMintTouched recipient))
      ((s.set 0 (st.totalSupply + value)).set (WriterKey.slot (.balance recipient))
        (st.balanceOf recipient + value)) (lpMintSourceState st recipient value) := by
  have extended := rep.extend fresh
  have tracked : WriterExtend K (lpMintTouched recipient) (.balance recipient) :=
    .inr (List.mem_singleton.mpr rfl)
  exact (extended.lpMint_supply_store (supply := st.totalSupply + value)).balance_store
    (value := st.balanceOf recipient + value) tracked

/-- The source recipient read follows the supply store, justified by finite separation. -/
theorem lpMint_source_reads {K : WriterKey → Prop} {st : State} {sevm : Sevm} {b : Devm}
    {toWord value : B256} (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (lpMintTouched toWord.toAdr)) :
    lpMintSupplyWord sevm b = st.totalSupply ∧
      lpMintRecipientWord sevm (afterSload sevm b 0) toWord
        (lpMintSupplyWord sevm b + value) = st.balanceOf toWord.toAdr := by
  have extended := rep.extend fresh
  have tracked : WriterExtend K (lpMintTouched toWord.toAdr) (.balance toWord.toAdr) :=
    .inr (List.mem_singleton.mpr rfl)
  have supply : lpMintSupplyWord sevm b = st.totalSupply := rep.fixed.1
  refine ⟨supply, ?_⟩
  change ((lpMintSupplyBase sevm (afterSload sevm b 0)
    (lpMintSupplyWord sevm b + value)).getStor sevm.currentTarget).get
    (transferBalanceSlot toWord.toAdr) = _
  rw [lpMintSupplyBase, afterSstore_getStor_self, afterSload_getStor, supply]
  exact (extended.lpMint_supply_store (supply := st.totalSupply + value)).selected
    (.balance toWord.toAdr) tracked

theorem lpMintLP_accept {st : State} {recipient : Adr} {value : B256}
    (supply : st.totalSupply.toNat + value.toNat < 2 ^ 256)
    (balance : (st.balanceOf recipient).toNat + value.toNat < 2 ^ 256) :
    st.mintLP recipient value =
      .ok (lpMintSourceState st recipient value, [.transfer 0 recipient value]) := by
  rw [State.mintLP, ite_eq_left supply, ite_eq_left balance]
  rfl

theorem lpMintLP_inv {st : State} {recipient : Adr} {value : B256}
    {post : State} {events : List Event}
    (accepted : st.mintLP recipient value = .ok (post, events)) :
    st.totalSupply.toNat + value.toNat < 2 ^ 256 ∧
      (st.balanceOf recipient).toNat + value.toNat < 2 ^ 256 ∧
      post = lpMintSourceState st recipient value ∧ events = [.transfer 0 recipient value] := by
  by_cases supply : st.totalSupply.toNat + value.toNat < 2 ^ 256
  · by_cases balance : (st.balanceOf recipient).toNat + value.toNat < 2 ^ 256
    · rw [lpMintLP_accept supply balance] at accepted
      cases accepted
      exact ⟨supply, balance, rfl, rfl⟩
    · simp only [State.mintLP, ite_eq_left supply, ite_eq_right balance] at accepted
      cases accepted
  · simp only [State.mintLP, ite_eq_right supply] at accepted
    cases accepted


def lpMintRawLog (pair recipient : Adr) (value : B256) : Jaune.Log :=
  ⟨pair, [transferTopic, 0, recipient.toB256], value.toBytes⟩

/-- Projection facts retain the complete raw post carrier, without reducing its memory image. -/
theorem lpMintPost_facts {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {toWord value : B256} {G : Nat} :
    (lpMintPost sevm b R M toWord value G).getStor sevm.currentTarget =
      ((b.getStor sevm.currentTarget).set 0 (lpMintSupplyWord sevm b + value)).set
        (transferBalanceSlot toWord.toAdr)
        (lpMintRecipientWord sevm (afterSload sevm b 0) toWord
          (lpMintSupplyWord sevm b + value) + value) ∧
    (∀ a, a ≠ sevm.currentTarget →
      (lpMintPost sevm b R M toWord value G).getStor a = b.getStor a) ∧
    (lpMintPost sevm b R M toWord value G).logs = b.logs ++
      [lpMintRawLog sevm.currentTarget toWord.toAdr value] ∧
    (lpMintPost sevm b R M toWord value G).gasLeft = G := by
  have stor (a : Adr) : (lpMintPost sevm b R M toWord value G).getStor a =
      (lpMintCreditBase sevm
        (afterSload sevm (lpMintSupplyBase sevm (afterSload sevm b 0)
          (lpMintSupplyWord sevm b + value)) (transferBalanceSlot toWord.toAdr))
        toWord value (lpMintRecipientWord sevm (afterSload sevm b 0) toWord
          (lpMintSupplyWord sevm b + value) + value)).getStor a := by
    unfold lpMintPost lpMintSupplyPost lpMintCreditPost
    exact St_getStor _ _ _ _ _
  have gas : (lpMintPost sevm b R M toWord value G).gasLeft = G := by
    unfold lpMintPost lpMintSupplyPost lpMintCreditPost
    exact St.gasLeft
  refine ⟨?_, ?_, ?_, gas⟩
  · rw [stor]
    simp only [lpMintCreditBase, Devm.addLog_getStor, afterSstore_getStor_self,
      afterSload_getStor, lpMintSupplyBase]
  · intro a different
    rw [stor]
    simp only [lpMintCreditBase, Devm.addLog_getStor,
      afterSstore_getStor_ne _ _ _ _ _ different.symm, afterSload_getStor, lpMintSupplyBase]
  · unfold lpMintPost lpMintSupplyPost lpMintCreditPost
    change (afterSstore sevm
      (afterSload sevm (lpMintSupplyBase sevm (afterSload sevm b 0)
        (lpMintSupplyWord sevm b + value)) (transferBalanceSlot toWord.toAdr))
      (transferBalanceSlot toWord.toAdr)
      (lpMintRecipientWord sevm (afterSload sevm b 0) toWord
        (lpMintSupplyWord sevm b + value) + value)).logs ++
          [lpMintRawLog sevm.currentTarget toWord.toAdr value] = _
    simp only [afterSstore_logs, afterSload_logs, lpMintSupplyBase]

theorem WriterRep.lpMint_post {K : WriterKey → Prop} {st : State} {sevm : Sevm}
    {b : Devm} {R : List B256} {M : Mem} {toWord value : B256} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (lpMintTouched toWord.toAdr)) :
    WriterRep (WriterExtend K (lpMintTouched toWord.toAdr))
      ((lpMintPost sevm b R M toWord value G).getStor sevm.currentTarget)
      (lpMintSourceState st toWord.toAdr value) := by
  have reads := lpMint_source_reads (value := value) rep fresh
  rw [lpMintPost_facts.1, reads.2, reads.1]
  exact rep.lpMint_store fresh

/-- Supply is the only fixed word changed; all other whole words retain their upper bits. -/
theorem WriterRep.lpMint_fixed {K : WriterKey → Prop} {st : State} {sevm : Sevm}
    {b : Devm} {R : List B256} {M : Mem} {toWord value : B256} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (lpMintTouched toWord.toAdr)) :
    ∀ n, n ∈ writerFixedSlots → n ≠ 0 →
      ((lpMintPost sevm b R M toWord value G).getStor sevm.currentTarget).get n =
        (b.getStor sevm.currentTarget).get n := by
  have extended := rep.extend fresh
  have tracked : WriterExtend K (lpMintTouched toWord.toAdr) (.balance toWord.toAdr) :=
    .inr (List.mem_singleton.mpr rfl)
  have apart := extended.apart (.balance toWord.toAdr) tracked
  change transferBalanceSlot toWord.toAdr ∉ writerFixedSlots at apart
  intro n fixed nonzero
  have off : transferBalanceSlot toWord.toAdr ≠ n :=
    fun eq => apart (eq.symm ▸ fixed)
  rw [lpMintPost_facts.1, Stor.get_set_ne _ off, Stor.get_set_ne _ (Ne.symm nonzero)]

/-- The source result is derived from incoming representation and the raw arithmetic guards. -/
def LPMintSourceResult (K : WriterKey → Prop) (st : State) (sevm : Sevm) (b : Devm)
    (R : List B256) (M : Mem) (toWord value : B256) (G : Nat) : Prop :=
  st.mintLP toWord.toAdr value =
    .ok (lpMintSourceState st toWord.toAdr value, [.transfer 0 toWord.toAdr value]) ∧
  WriterRep (WriterExtend K (lpMintTouched toWord.toAdr))
    ((lpMintPost sevm b R M toWord value G).getStor sevm.currentTarget)
    (lpMintSourceState st toWord.toAdr value) ∧
  (∀ n, n ∈ writerFixedSlots → n ≠ 0 →
    ((lpMintPost sevm b R M toWord value G).getStor sevm.currentTarget).get n =
      (b.getStor sevm.currentTarget).get n) ∧
  (∀ a, a ≠ sevm.currentTarget →
    (lpMintPost sevm b R M toWord value G).getStor a = b.getStor a) ∧
  (lpMintPost sevm b R M toWord value G).logs = b.logs ++
    [lpMintRawLog sevm.currentTarget toWord.toAdr value] ∧
  (lpMintPost sevm b R M toWord value G).gasLeft = G

theorem lpMint_source_result {K : WriterKey → Prop} {st : State} {sevm : Sevm}
    {b : Devm} {R : List B256} {M : Mem} {toWord value : B256} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (lpMintTouched toWord.toAdr))
    (guards : lpMintAccepts sevm b toWord value) :
    LPMintSourceResult K st sevm b R M toWord value G := by
  have reads := lpMint_source_reads (value := value) rep fresh
  obtain ⟨supply, _, balance⟩ := guards
  rw [reads.1] at supply
  rw [reads.2] at balance
  have facts := lpMintPost_facts (sevm := sevm) (b := b) (R := R) (M := M)
    (toWord := toWord) (value := value) (G := G)
  exact ⟨lpMintLP_accept supply balance, rep.lpMint_post fresh, rep.lpMint_fixed fresh,
    facts.2.1, facts.2.2.1, facts.2.2.2⟩

/-- Selected charges keep the raw original/current/new values and warming order. -/
def lpMintSourceCharge (sevm : Sevm) (b : Devm) : Nat := sloadCost sevm b 0

def lpMintSupplyCharge (sevm : Sevm) (b : Devm) (value : B256) : Nat :=
  sstoreCost sevm (afterSload sevm b 0) 0 (lpMintSupplyWord sevm b + value)

def lpMintRecipientLoadCharge (sevm : Sevm) (b : Devm) (toWord value : B256) : Nat :=
  sloadCost sevm (lpMintSupplyBase sevm (afterSload sevm b 0) (lpMintSupplyWord sevm b + value))
    (transferBalanceSlot toWord.toAdr)

def lpMintCreditCharge (sevm : Sevm) (b : Devm) (toWord value : B256) : Nat :=
  sstoreCost sevm
    (afterSload sevm (lpMintSupplyBase sevm (afterSload sevm b 0)
      (lpMintSupplyWord sevm b + value)) (transferBalanceSlot toWord.toAdr))
    (transferBalanceSlot toWord.toAdr)
    (lpMintRecipientWord sevm (afterSload sevm b 0) toWord (lpMintSupplyWord sevm b + value) + value)

def lpMintGas (sevm : Sevm) (b : Devm) (toWord value : B256) (G : Nat) : Nat :=
  G + lpMintSourceCharge sevm b + lpMintSupplyCharge sevm b value +
    lpMintRecipientLoadCharge sevm b toWord value + lpMintCreditCharge sevm b toWord value + 2171

def lpMintSupplySentry (sevm : Sevm) (b : Devm) (toWord value : B256) (G : Nat) : Prop :=
  gCallStipend < G + lpMintSupplyCharge sevm b value +
    lpMintRecipientLoadCharge sevm b toWord value + lpMintCreditCharge sevm b toWord value + 2077

def lpMintCreditSentry (sevm : Sevm) (b : Devm) (toWord value : B256) (G : Nat) : Prop :=
  gCallStipend < G + lpMintCreditCharge sevm b toWord value + 1828

/-- Accepted actual State.mintLP yields the exact raw entry and finite complete post. -/
theorem lpMint62_source_exact {K : WriterKey → Prop} {st post : State} {events : List Event}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {toWord value ρ : B256} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (lpMintTouched toWord.toAdr))
    (accepted : st.mintLP toWord.toAdr value = .ok (post, events))
    (nonstatic : sevm.isStatic = false)
    (supplySentry : lpMintSupplySentry sevm b toWord value G)
    (creditSentry : lpMintCreditSentry sevm b toWord value G)
    (room : R.length ≤ 1014) :
    SFunc.RunExact cert.prog sevm (St b (value :: toWord :: ρ :: R)
      M (lpMintGas sevm b toWord value G)) t_28ca_c62
      (.returned (lpMintPost sevm b R M toWord value G)) ∧
    LPMintSourceResult K st sevm b R M toWord value G ∧
    post = lpMintSourceState st toWord.toAdr value ∧ events = [.transfer 0 toWord.toAdr value] := by
  obtain ⟨supply, balance, postEq, eventsEq⟩ := lpMintLP_inv accepted
  have reads := lpMint_source_reads (value := value) rep fresh
  have supplyRaw : (lpMintSupplyWord sevm b).toNat + value.toNat < 2 ^ 256 := by
    rw [reads.1]
    exact supply
  have balanceRaw : (lpMintRecipientWord sevm (afterSload sevm b 0) toWord
      (lpMintSupplyWord sevm b + value)).toNat + value.toNat < 2 ^ 256 := by
    rw [reads.2]
    exact balance
  exact ⟨lpMint62_exact fork mem rfl rfl rfl rfl supplySentry creditSentry nonstatic
      supplyRaw balanceRaw room,
    lpMint_source_result rep fresh ⟨supplyRaw, nonstatic, balanceRaw⟩, postEq, eventsEq⟩

end Blanc.Lift.UniswapV2Pair
