import Blanc.Lift.UniswapV2Pair.LPBurnCore
import Blanc.Lift.UniswapV2Pair.LPMintSource

/-! Finite WriterRep adapter for the actual LP balance-then-supply burn. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def lpBurnSourceState (st : State) (owner : Adr) (value : B256) : State :=
  lpMintSupplyState (balanceSourceState st owner (st.balanceOf owner - value))
    (st.totalSupply - value)

/-- The finite row write follows the actual balance-then-supply order. -/
theorem WriterRep.lpBurn_store {K : WriterKey → Prop} {s : Stor} {st : State}
    {owner : Adr} {value : B256} (rep : WriterRep K s st)
    (fresh : WriterFreshKeys K (lpMintTouched owner)) :
    WriterRep (WriterExtend K (lpMintTouched owner))
      ((s.set (WriterKey.slot (.balance owner)) (st.balanceOf owner - value)).set 0
        (st.totalSupply - value)) (lpBurnSourceState st owner value) := by
  have extended := rep.extend fresh
  have tracked : WriterExtend K (lpMintTouched owner) (.balance owner) :=
    .inr (List.mem_singleton.mpr rfl)
  exact (extended.balance_store (value := st.balanceOf owner - value) tracked).lpMint_supply_store

/-- Finite separation derives the supply read after the balance debit. -/
theorem lpBurn_source_reads {K : WriterKey → Prop} {st : State} {sevm : Sevm} {b : Devm}
    {fromWord value : B256} (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (lpMintTouched fromWord.toAdr)) :
    lpBurnBalanceWord sevm b fromWord = st.balanceOf fromWord.toAdr ∧
      lpBurnSupplyWord sevm (afterSload sevm b (transferBalanceSlot fromWord.toAdr))
        fromWord (lpBurnBalanceWord sevm b fromWord - value) = st.totalSupply := by
  have extended := rep.extend fresh
  have tracked : WriterExtend K (lpMintTouched fromWord.toAdr) (.balance fromWord.toAdr) :=
    .inr (List.mem_singleton.mpr rfl)
  have balance : lpBurnBalanceWord sevm b fromWord = st.balanceOf fromWord.toAdr :=
    extended.selected (.balance fromWord.toAdr) tracked
  refine ⟨balance, ?_⟩
  change ((lpBurnBalanceBase sevm (afterSload sevm b (transferBalanceSlot fromWord.toAdr))
    fromWord (lpBurnBalanceWord sevm b fromWord - value)).getStor sevm.currentTarget).get 0 = _
  rw [lpBurnBalanceBase, afterSstore_getStor_self, afterSload_getStor, balance]
  exact (extended.balance_store (value := st.balanceOf fromWord.toAdr - value) tracked).fixed.1

theorem lpBurnLP_accept {st : State} {owner : Adr} {value : B256}
    (balance : value ≤ st.balanceOf owner) (supply : value ≤ st.totalSupply) :
    st.burnLP owner value =
      .ok (lpBurnSourceState st owner value, [.transfer owner 0 value]) := by
  rw [State.burnLP, ite_eq_left balance, ite_eq_left supply]
  rfl

theorem lpBurnLP_inv {st : State} {owner : Adr} {value : B256}
    {post : State} {events : List Event}
    (accepted : st.burnLP owner value = .ok (post, events)) :
    value ≤ st.balanceOf owner ∧ value ≤ st.totalSupply ∧
      post = lpBurnSourceState st owner value ∧ events = [.transfer owner 0 value] := by
  by_cases balance : value ≤ st.balanceOf owner
  · by_cases supply : value ≤ st.totalSupply
    · rw [lpBurnLP_accept balance supply] at accepted
      cases accepted
      exact ⟨balance, supply, rfl, rfl⟩
    · simp only [State.burnLP, ite_eq_left balance, ite_eq_right supply] at accepted
      cases accepted
  · simp only [State.burnLP, ite_eq_right balance] at accepted
    cases accepted

def lpBurnRawLog (pair owner : Adr) (value : B256) : Jaune.Log :=
  ⟨pair, [transferTopic, owner.toB256, 0], value.toBytes⟩

/-- The full raw post preserves the other accounts and appends exactly the LP debit log. -/
theorem lpBurnPost_facts {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {fromWord value : B256} {G : Nat} :
    (lpBurnPost sevm b R M fromWord value G).getStor sevm.currentTarget =
      ((b.getStor sevm.currentTarget).set (transferBalanceSlot fromWord.toAdr)
        (lpBurnBalanceWord sevm b fromWord - value)).set 0
        (lpBurnSupplyWord sevm (afterSload sevm b (transferBalanceSlot fromWord.toAdr))
          fromWord (lpBurnBalanceWord sevm b fromWord - value) - value) ∧
    (∀ a, a ≠ sevm.currentTarget →
      (lpBurnPost sevm b R M fromWord value G).getStor a = b.getStor a) ∧
    (lpBurnPost sevm b R M fromWord value G).logs = b.logs ++
      [lpBurnRawLog sevm.currentTarget fromWord.toAdr value] ∧
    (lpBurnPost sevm b R M fromWord value G).gasLeft = G := by
  have stor (a : Adr) : (lpBurnPost sevm b R M fromWord value G).getStor a =
      (lpBurnSupplyBase sevm
        (afterSload sevm (lpBurnBalanceBase sevm
          (afterSload sevm b (transferBalanceSlot fromWord.toAdr)) fromWord
          (lpBurnBalanceWord sevm b fromWord - value)) 0)
        fromWord value (lpBurnSupplyWord sevm (afterSload sevm b (transferBalanceSlot fromWord.toAdr))
          fromWord (lpBurnBalanceWord sevm b fromWord - value) - value)).getStor a := by
    unfold lpBurnPost lpBurnBalancePost lpBurnSupplyPost
    exact St_getStor _ _ _ _ _
  have gas : (lpBurnPost sevm b R M fromWord value G).gasLeft = G := by
    unfold lpBurnPost lpBurnBalancePost lpBurnSupplyPost
    exact St.gasLeft
  refine ⟨?_, ?_, ?_, gas⟩
  · rw [stor]
    simp only [lpBurnSupplyBase, Devm.addLog_getStor, afterSstore_getStor_self,
      afterSload_getStor, lpBurnBalanceBase]
  · intro a different
    rw [stor]
    simp only [lpBurnSupplyBase, Devm.addLog_getStor,
      afterSstore_getStor_ne _ _ _ _ _ different.symm, afterSload_getStor, lpBurnBalanceBase]
  · unfold lpBurnPost lpBurnBalancePost lpBurnSupplyPost
    change (afterSstore sevm
      (afterSload sevm (lpBurnBalanceBase sevm
        (afterSload sevm b (transferBalanceSlot fromWord.toAdr)) fromWord
        (lpBurnBalanceWord sevm b fromWord - value)) 0) 0
      (lpBurnSupplyWord sevm (afterSload sevm b (transferBalanceSlot fromWord.toAdr))
        fromWord (lpBurnBalanceWord sevm b fromWord - value) - value)).logs ++
          [lpBurnRawLog sevm.currentTarget fromWord.toAdr value] = _
    simp only [afterSstore_logs, afterSload_logs, lpBurnBalanceBase]

/-- Incoming finite representation extends only the actually touched balance row. -/
theorem WriterRep.lpBurn_post {K : WriterKey → Prop} {st : State} {sevm : Sevm}
    {b : Devm} {R : List B256} {M : Mem} {fromWord value : B256} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (lpMintTouched fromWord.toAdr)) :
    WriterRep (WriterExtend K (lpMintTouched fromWord.toAdr))
      ((lpBurnPost sevm b R M fromWord value G).getStor sevm.currentTarget)
      (lpBurnSourceState st fromWord.toAdr value) := by
  have reads := lpBurn_source_reads (value := value) rep fresh
  rw [lpBurnPost_facts.1, reads.2, reads.1]
  exact rep.lpBurn_store fresh

/-- Finite source result and all physical storage/log/gas projections of the actual raw post. -/
def LPBurnSourceResult (K : WriterKey → Prop) (st : State) (sevm : Sevm) (b : Devm)
    (R : List B256) (M : Mem) (fromWord value : B256) (G : Nat) : Prop :=
  st.burnLP fromWord.toAdr value =
    .ok (lpBurnSourceState st fromWord.toAdr value, [.transfer fromWord.toAdr 0 value]) ∧
  WriterRep (WriterExtend K (lpMintTouched fromWord.toAdr))
    ((lpBurnPost sevm b R M fromWord value G).getStor sevm.currentTarget)
    (lpBurnSourceState st fromWord.toAdr value) ∧
  (lpBurnPost sevm b R M fromWord value G).getStor sevm.currentTarget =
    ((b.getStor sevm.currentTarget).set (transferBalanceSlot fromWord.toAdr)
      (st.balanceOf fromWord.toAdr - value)).set 0 (st.totalSupply - value) ∧
  (∀ a, a ≠ sevm.currentTarget →
    (lpBurnPost sevm b R M fromWord value G).getStor a = b.getStor a) ∧
  (lpBurnPost sevm b R M fromWord value G).logs = b.logs ++
    [lpBurnRawLog sevm.currentTarget fromWord.toAdr value] ∧
  (lpBurnPost sevm b R M fromWord value G).gasLeft = G

theorem lpBurn_source_result {K : WriterKey → Prop} {st : State} {sevm : Sevm}
    {b : Devm} {R : List B256} {M : Mem} {fromWord value : B256} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (lpMintTouched fromWord.toAdr))
    (balance : value ≤ lpBurnBalanceWord sevm b fromWord)
    (supply : value ≤ lpBurnSupplyWord sevm (afterSload sevm b (transferBalanceSlot fromWord.toAdr))
      fromWord (lpBurnBalanceWord sevm b fromWord - value)) :
    LPBurnSourceResult K st sevm b R M fromWord value G := by
  have reads := lpBurn_source_reads (value := value) rep fresh
  rw [reads.1] at balance
  rw [reads.2] at supply
  have facts := lpBurnPost_facts (sevm := sevm) (b := b) (R := R) (M := M)
    (fromWord := fromWord) (value := value) (G := G)
  have physical := facts.1
  rw [reads.2, reads.1] at physical
  exact ⟨lpBurnLP_accept balance supply, rep.lpBurn_post fresh, physical,
    facts.2.1, facts.2.2.1, facts.2.2.2⟩

/-- The actual successful internal LP burn derives source acceptance and the finite post. -/
theorem lpBurn63_source_inv {K : WriterKey → Prop} {st : State} {sevm : Sevm}
    {b : Devm} {R : List B256} {M : Mem} {fromWord value ρ : B256} {G : Nat} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (lpMintTouched fromWord.toAdr))
    (run : SFunc.Run cert.prog sevm (St b (value :: fromWord :: ρ :: R) M G) t_2992_c63 o) :
    sevm.isStatic = false ∧ ∃ residual,
      o = .returned (lpBurnPost sevm b R M fromWord value residual) ∧
      LPBurnSourceResult K st sevm b R M fromWord value residual := by
  obtain ⟨nonstatic, balance, supply, residual, result⟩ := lpBurn63_inv fork mem run
  exact ⟨nonstatic, residual, result, lpBurn_source_result rep fresh balance supply⟩

def lpBurnSourceCharge (sevm : Sevm) (b : Devm) (fromWord : B256) : Nat :=
  sloadCost sevm b (transferBalanceSlot fromWord.toAdr)

def lpBurnBalanceCharge (sevm : Sevm) (b : Devm) (fromWord value : B256) : Nat :=
  sstoreCost sevm (afterSload sevm b (transferBalanceSlot fromWord.toAdr))
    (transferBalanceSlot fromWord.toAdr) (lpBurnBalanceWord sevm b fromWord - value)

def lpBurnSupplyLoadCharge (sevm : Sevm) (b : Devm) (fromWord value : B256) : Nat :=
  sloadCost sevm (lpBurnBalanceBase sevm (afterSload sevm b (transferBalanceSlot fromWord.toAdr))
    fromWord (lpBurnBalanceWord sevm b fromWord - value)) 0

def lpBurnSupplyCharge (sevm : Sevm) (b : Devm) (fromWord value : B256) : Nat :=
  sstoreCost sevm
    (afterSload sevm (lpBurnBalanceBase sevm (afterSload sevm b (transferBalanceSlot fromWord.toAdr))
      fromWord (lpBurnBalanceWord sevm b fromWord - value)) 0) 0
    (lpBurnSupplyWord sevm (afterSload sevm b (transferBalanceSlot fromWord.toAdr))
      fromWord (lpBurnBalanceWord sevm b fromWord - value) - value)

def lpBurnGas (sevm : Sevm) (b : Devm) (fromWord value : B256) (G : Nat) : Nat :=
  G + lpBurnSourceCharge sevm b fromWord + lpBurnBalanceCharge sevm b fromWord value +
    lpBurnSupplyLoadCharge sevm b fromWord value + lpBurnSupplyCharge sevm b fromWord value + 2168

def lpBurnBalanceSentry (sevm : Sevm) (b : Devm) (fromWord value : B256) (G : Nat) : Prop :=
  gCallStipend < G + lpBurnBalanceCharge sevm b fromWord value +
    lpBurnSupplyLoadCharge sevm b fromWord value + lpBurnSupplyCharge sevm b fromWord value + 1921

def lpBurnSupplySentry (sevm : Sevm) (b : Devm) (fromWord value : B256) (G : Nat) : Prop :=
  gCallStipend < G + lpBurnSupplyCharge sevm b fromWord value + 1831

/-- Actual source acceptance constructs entry63 at the exact sequential storage gas. -/
theorem lpBurn63_source_exact {K : WriterKey → Prop} {st post : State} {events : List Event}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {fromWord value ρ : B256} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (lpMintTouched fromWord.toAdr))
    (accepted : st.burnLP fromWord.toAdr value = .ok (post, events))
    (nonstatic : sevm.isStatic = false)
    (balanceSentry : lpBurnBalanceSentry sevm b fromWord value G)
    (supplySentry : lpBurnSupplySentry sevm b fromWord value G)
    (room : R.length ≤ 1014) :
    SFunc.RunExact cert.prog sevm (St b (value :: fromWord :: ρ :: R)
      M (lpBurnGas sevm b fromWord value G)) t_2992_c63
      (.returned (lpBurnPost sevm b R M fromWord value G)) ∧
    LPBurnSourceResult K st sevm b R M fromWord value G ∧
    post = lpBurnSourceState st fromWord.toAdr value ∧ events = [.transfer fromWord.toAdr 0 value] := by
  obtain ⟨balance, supply, postEq, eventsEq⟩ := lpBurnLP_inv accepted
  have reads := lpBurn_source_reads (value := value) rep fresh
  have balanceRaw : value ≤ lpBurnBalanceWord sevm b fromWord := by
    rw [reads.1]
    exact balance
  have supplyRaw : value ≤ lpBurnSupplyWord sevm (afterSload sevm b (transferBalanceSlot fromWord.toAdr))
      fromWord (lpBurnBalanceWord sevm b fromWord - value) := by
    rw [reads.2]
    exact supply
  exact ⟨lpBurn63_exact fork mem rfl rfl rfl rfl balanceSentry supplySentry nonstatic
      balanceRaw supplyRaw room,
    lpBurn_source_result rep fresh balanceRaw supplyRaw, postEq, eventsEq⟩

end Blanc.Lift.UniswapV2Pair
