import Blanc.Composition.UniswapV2PairWeth9Tx2XRead
import Blanc.Composition.UniswapV2PairWeth9Tx2Data
import Blanc.Composition.UniswapV2PairWeth9W0

/-!
# The swap frame of `tx2`: its entry, its calldata and a view of the machines it passes through

`Tx2Frame sevm b` is what the Pair's `swap` frame of the closed instance's second transaction needs
of its entry machine: the Pair's code and storage (`W0`'s), WETH9's and `X`'s code and touched slots,
cold storage keys, `X` and WETH9 not yet accessed.  The calldata facts (`tx2_amount0`, …) decode
`swap(0, swapOut, trader, "")`.

`DView b d K A S rc L` records exactly what the frame's later charges and the transaction read of an
intermediate machine `d`: its warm storage keys (the explicit list `K`), its warm addresses (`A`
on top of the entry's), the entry's created accounts, its world `S`, its refund counter `rc`, its
logs `L` and no deletion.  The lemmas below carry it through each primitive the swap executes.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Instance

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.Composition.UniswapV2PairWeth9Joint

/-! ## The calldata -/

section Decode
variable {sevm : Sevm} (hdata : sevm.data = tx2Data)
include hdata

theorem tx2_amount0 : swapAmount0Out sevm = 0 := by
  simp only [swapAmount0Out, Sevm.dataWord, hdata, tx2Data]
  decide +kernel

theorem tx2_amount1 : swapAmount1Out sevm = swapOut := by
  simp only [swapAmount1Out, Sevm.dataWord, hdata, tx2Data]
  decide +kernel

theorem tx2_recipientWord : swapRecipientWord sevm = trader.toB256 := by
  simp only [swapRecipientWord, Sevm.dataWord, hdata, tx2Data]
  decide +kernel

theorem tx2_recipient : swapRecipient sevm = trader := by
  simp only [swapRecipient, Sevm.dataWord, hdata, tx2Data]
  decide +kernel

theorem tx2_dataLength : swapDataLength sevm = 0 := by
  simp only [swapDataLength, swapDataOffset, Sevm.dataWord, hdata, tx2Data]
  decide +kernel

theorem tx2_selector : Blanc.Sevm.selector sevm = 0x022c0d9f := by
  simp only [Blanc.Sevm.selector, Sevm.dataWord, hdata, tx2Data]
  decide +kernel

theorem tx2_guards : SwapAbiGuards sevm := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [swapDataLength, swapDataStart, swapDataOffset, Sevm.dataWord, hdata, tx2Data] <;>
    decide +kernel

theorem tx2_size : (4 : B256) ≤ sevm.data.length.toB256 := by
  rw [hdata]
  decide +kernel

theorem tx2_representable : sevm.data.length < 2 ^ 256 := by
  rw [hdata]
  decide +kernel

end Decode

/-! ## The frame entry -/

/-- The Pair's model state at `W0` (and after `tx1`, which does not touch the Pair's storage). -/
def tx2St : UniswapV2Pair.State := UniswapV2Pair.rowsState w0Base w0PairRows

/-- **What the swap frame of `tx2` needs of its entry machine.** -/
structure Tx2Frame (sevm : Sevm) (b : Devm) : Prop where
  code : sevm.code = UniswapV2Pair.code
  fork : sevm.benvStat.fork = .bpo2
  caller : sevm.caller = trader
  target : sevm.currentTarget = pair
  static : sevm.isStatic = false
  data : sevm.data = tx2Data
  value : sevm.value = 0
  depth : sevm.depth = 1024
  time : sevm.benvStat.time = 1
  origPair : sevm.benvStat.origState.getStor pair = w0PairStor
  origWethPair : (sevm.benvStat.origState.getStor weth).get (Weth9.balSlot pair) = 1000000
  origWethTrader : (sevm.benvStat.origState.getStor weth).get (Weth9.balSlot trader) = 0
  stack : b.stack = []
  memory : b.memory = Mem.empty
  output : b.output = []
  error : b.error = none
  refund : b.refundCounter = 0
  logs : b.logs = []
  deleted : ∀ a, a ∉ b.accountsToDelete
  keys : ∀ k, k ∉ b.accessedStorageKeys
  coldX : tokenX ∉ b.accessedAddresses
  coldWeth : weth ∉ b.accessedAddresses
  createdPair : pair ∉ b.createdAccounts
  createdWeth : weth ∉ b.createdAccounts
  createdX : tokenX ∉ b.createdAccounts
  pairStor : b.state.getStor pair = w0PairStor
  pairCode : b.state.getCode pair = UniswapV2Pair.code
  wethCode : b.state.getCode weth = Weth9.code
  xCode : b.state.getCode tokenX = VyperNonreentrantDeployed.Token20.code
  wethPair : (b.state.getStor weth).get (Weth9.balSlot pair) = 1000000
  wethTrader : (b.state.getStor weth).get (Weth9.balSlot trader) = 0
  xPair : (b.state.getStor tokenX).get (VyperNonreentrantDeployed.Token20.balSlot pair) = 1001000

theorem w0PairStor_12 : w0PairStor.get 12 = 1 := by decide +kernel
theorem w0PairStor_8 : w0PairStor.get 8 = Nat.toB256 (1000000 + 1000000 * 2 ^ 112) := by
  decide +kernel
theorem w0PairStor_6 : w0PairStor.get 6 = tokenX.toB256 := by decide +kernel
theorem w0PairStor_7 : w0PairStor.get 7 = weth.toB256 := by decide +kernel
theorem w0PairStor_9 : w0PairStor.get 9 = 0 := by decide +kernel
theorem w0PairStor_10 : w0PairStor.get 10 = 0 := by decide +kernel

theorem weth_balSlot_trader_ne_pair : Weth9.balSlot trader ≠ Weth9.balSlot pair := by
  decide +kernel
theorem pair_ne_weth : pair ≠ weth := by decide +kernel
theorem pair_ne_tokenX : pair ≠ tokenX := by decide +kernel
theorem weth_ne_tokenX : weth ≠ tokenX := by decide +kernel
theorem trader_ne_weth : trader ≠ weth := by decide +kernel

/-! ## Reading storage -/

theorem getStorVal_eq' (d : Devm) (a : Adr) (k : B256) : d.getStorVal a k = (d.getStor a).get k :=
  rfl

theorem getStor_eq' (d : Devm) (a : Adr) : d.getStor a = d.state.getStor a := rfl

theorem getOrigStorVal_eq' (sevm : Sevm) (a : Adr) (k : B256) :
    Jaune.getOrigStorVal sevm a k = (sevm.benvStat.origState.getStor a).get k := rfl

theorem State.setStorVal_getStor_self (S : Jaune.State) (a : Adr) (k v : B256) :
    (S.setStorVal a k v).getStor a = (S.getStor a).set k v := by
  unfold State.setStorVal State.getStor
  rw [State.get_set_self]

theorem State.setStorVal_getStor_ne (S : Jaune.State) {a a' : Adr} (h : a ≠ a') (k v : B256) :
    (S.setStorVal a k v).getStor a' = S.getStor a' := by
  unfold State.setStorVal State.getStor
  rw [State.get_set_ne _ h]

theorem State.setStorVal_getCode (S : Jaune.State) (a a' : Adr) (k v : B256) :
    (S.setStorVal a k v).getCode a' = S.getCode a' := by
  unfold State.setStorVal State.getCode
  by_cases h : a = a'
  · subst h
    rw [State.get_set_self]
  · rw [State.get_set_ne _ h]

/-! ## The view -/

/-- **What the swap's later steps read of an intermediate machine `d`** (relative to the entry `b`):
warm keys `K`, warm addresses `A` beyond the entry's, the entry's created accounts, world `S`,
refund counter `rc`, logs `L`, no deletion. -/
structure DView (b d : Devm) (K : List (Adr × B256)) (A : List Adr) (S : Jaune.State) (rc : Int)
    (L : List Log) : Prop where
  keys : ∀ k, k ∈ d.accessedStorageKeys ↔ k ∈ K
  addrs : ∀ a, a ∈ d.accessedAddresses ↔ a ∈ A ∨ a ∈ b.accessedAddresses
  created : d.createdAccounts = b.createdAccounts
  state : d.state = S
  refund : d.refundCounter = rc
  logs : d.logs = L
  deleted : ∀ a, a ∉ d.accountsToDelete

section View

variable {b d : Devm} {K : List (Adr × B256)} {A : List Adr} {S : Jaune.State} {rc : Int}
  {L : List Log}

/-- The entry's own view. -/
theorem DView.entry {sevm : Sevm} (h : Tx2Frame sevm b) : DView b b [] [] b.state 0 [] where
  keys k := by simp only [h.keys, List.not_mem_nil]
  addrs a := by simp only [List.not_mem_nil, false_or]
  created := rfl
  state := rfl
  refund := h.refund
  logs := h.logs
  deleted := h.deleted

/-- Machines with the same viewed columns share the view. -/
theorem DView.congr {d' : Devm} (h : DView b d K A S rc L)
    (hk : d'.accessedStorageKeys = d.accessedStorageKeys)
    (ha : d'.accessedAddresses = d.accessedAddresses) (hc : d'.createdAccounts = d.createdAccounts)
    (hs : d'.state = d.state) (hr : d'.refundCounter = d.refundCounter) (hl : d'.logs = d.logs)
    (hd : d'.accountsToDelete = d.accountsToDelete) : DView b d' K A S rc L where
  keys k := hk ▸ h.keys k
  addrs a := ha ▸ h.addrs a
  created := hc.trans h.created
  state := hs.trans h.state
  refund := hr.trans h.refund
  logs := hl.trans h.logs
  deleted a := hd ▸ h.deleted a

theorem DView.setMach (h : DView b d K A S rc L) (m : Mach) : DView b (d.setMach m) K A S rc L :=
  h.congr rfl rfl rfl rfl rfl rfl rfl

theorem DView.St (h : DView b d K A S rc L) (R : List B256) (M : Mem) (g : Nat) :
    DView b (Lift.St d R M g) K A S rc L := h.setMach _

theorem DView.withGasLeft (h : DView b d K A S rc L) (g : Nat) :
    DView b (d.withGasLeft g) K A S rc L := h.setMach _

theorem DView.memRead (h : DView b d K A S rc L) (i n : Nat) :
    DView b (d.memRead i n).2 K A S rc L := h.setMach _

theorem DView.memWrite (h : DView b d K A S rc L) (i : Nat) (v : Bytes) :
    DView b (d.memWrite i v) K A S rc L := h.congr rfl rfl rfl rfl rfl rfl rfl

theorem DView.memExtends (h : DView b d K A S rc L) (ps : List (Nat × Nat)) :
    DView b (d.memExtends ps) K A S rc L := h.congr rfl rfl rfl rfl rfl rfl rfl

theorem DView.withOutput (h : DView b d K A S rc L) (o : Bytes) :
    DView b (d.withOutput o) K A S rc L := h.congr rfl rfl rfl rfl rfl rfl rfl

theorem DView.withReturnData (h : DView b d K A S rc L) (o : Bytes) :
    DView b (d.withReturnData o) K A S rc L := h.congr rfl rfl rfl rfl rfl rfl rfl

theorem DView.addLog (h : DView b d K A S rc L) (l : Log) :
    DView b (d.addLog l) K A S rc (L ++ [l]) where
  keys := h.keys
  addrs := h.addrs
  created := h.created
  state := h.state
  refund := h.refund
  logs := by rw [← h.logs]; rfl
  deleted := h.deleted

theorem DView.addAccessedAddress (h : DView b d K A S rc L) (x : Adr) :
    DView b (Jaune.addAccessedAddress d x) K (x :: A) S rc L where
  keys := h.keys
  addrs a := by
    change a ∈ d.accessedAddresses.insert x ↔ _
    rw [Std.HashSet.mem_insert, h.addrs a, List.mem_cons, beq_iff_eq]
    constructor
    · rintro (e | e | e)
      · exact Or.inl (Or.inl e.symm)
      · exact Or.inl (Or.inr e)
      · exact Or.inr e
    · rintro ((e | e) | e)
      · exact Or.inl e.symm
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr e)
  created := h.created
  state := h.state
  refund := h.refund
  logs := h.logs
  deleted := h.deleted

theorem DView.temporalAccountAccessBase (h : DView b d K A S rc L) (x : Adr) :
    DView b (Lift.temporalAccountAccessBase d x) K (x :: A) S rc L := by
  unfold Lift.temporalAccountAccessBase
  split
  · rename_i hx
    refine ⟨h.keys, fun a => ?_, h.created, h.state, h.refund, h.logs, h.deleted⟩
    rw [h.addrs a, List.mem_cons]
    constructor
    · rintro (e | e)
      · exact Or.inl (Or.inr e)
      · exact Or.inr e
    · rintro ((e | e) | e)
      · subst e
        exact (h.addrs a).mp hx
      · exact Or.inl e
      · exact Or.inr e
  · exact h.addAccessedAddress x

theorem DView.afterSload {sevm : Sevm} {t : Adr} (ht : sevm.currentTarget = t)
    (h : DView b d K A S rc L) (k : B256) :
    DView b (Blanc.afterSload sevm d k) ((t, k) :: K) A S rc L := by
  unfold Blanc.afterSload
  split
  · rename_i hk
    refine ⟨fun k' => ?_, h.addrs, h.created, h.state, h.refund, h.logs, h.deleted⟩
    rw [h.keys k', List.mem_cons]
    constructor
    · exact Or.inr
    · rintro (e | e)
      · subst e
        rw [← ht]
        exact (h.keys _).mp hk
      · exact e
  · refine ⟨fun k' => ?_, h.addrs, h.created, h.state, h.refund, h.logs, h.deleted⟩
    change k' ∈ d.accessedStorageKeys.insert (sevm.currentTarget, k) ↔ _
    rw [Std.HashSet.mem_insert, h.keys k', List.mem_cons, beq_iff_eq, ht]
    constructor
    · rintro (e | e)
      · exact Or.inl e.symm
      · exact Or.inr e
    · rintro (e | e)
      · exact Or.inl e.symm
      · exact Or.inr e

theorem DView.afterSstore {sevm : Sevm} {t : Adr} (ht : sevm.currentTarget = t)
    (hcr : t ∉ b.createdAccounts) (h : DView b d K A S rc L) (k v : B256) :
    DView b (Blanc.afterSstore sevm d k v) ((t, k) :: K) A (S.setStorVal t k v)
      (sstoreNewRefundCounter sevm.benvStat.rules.gas v
        ((sevm.benvStat.origState.getStor t).get k) ((S.getStor t).get k) rc) L := by
  have keys : ∀ k', k' ∈ (Blanc.afterSstore sevm d k v).accessedStorageKeys ↔ k' ∈ (t, k) :: K := by
    intro k'
    rw [afterSstore_accessedStorageKeys, mem_sloadAccessedStorageKeys_iff, h.keys k', ht,
      List.mem_cons]
  refine ⟨keys, fun a => ?_, ?_, ?_, ?_, (afterSstore_logs _ _ _ _).trans h.logs, ?_⟩
  · rw [afterSstore_accessedAddresses]
    exact h.addrs a
  · rw [afterSstore_createdAccounts]
    exact h.created
  · unfold Blanc.afterSstore
    rw [← h.state, ← ht]
    split <;> rfl
  · rw [afterSstore_refundCounter, h.refund]
    unfold Devm.getOrigStorVal
    rw [h.created, ite_eq_right_iff.mpr (fun e => absurd (ht ▸ e) hcr), ht, getStorVal_eq',
      getStor_eq', h.state]
    rfl
  · intro a
    rw [afterSstore_accountsToDelete]
    exact h.deleted a

/-- An `SLOAD`'s charge, read off the view. -/
theorem DView.sloadCost {sevm : Sevm} {t : Adr} (ht : sevm.currentTarget = t)
    (h : DView b d K A S rc L) (k : B256) :
    Blanc.sloadCost sevm d k = if (t, k) ∈ K then gasWarmAccess else gasColdSload := by
  unfold Blanc.sloadCost
  simp only [ht, h.keys]

/-- An `SSTORE`'s charge, read off the view. -/
theorem DView.sstoreCost {sevm : Sevm} {t : Adr} (ht : sevm.currentTarget = t)
    (hcr : t ∉ b.createdAccounts) (h : DView b d K A S rc L) (k v : B256) :
    Blanc.sstoreCost sevm d k v = (if (t, k) ∈ K then 0 else gasColdSload) +
      sstoreValueCost ((sevm.benvStat.origState.getStor t).get k) ((S.getStor t).get k) v := by
  unfold Blanc.sstoreCost Devm.getOrigStorVal
  simp only [ht, h.keys, h.created, hcr, ite_false, getStorVal_eq', getStor_eq', h.state]
  rfl

/-- A storage read, off the view. -/
theorem DView.getStorVal (h : DView b d K A S rc L) (a : Adr) (k : B256) :
    d.getStorVal a k = (S.getStor a).get k := by
  rw [getStorVal_eq', getStor_eq', h.state]

/-- An account's warmth, off the view. -/
theorem DView.accessCost (h : DView b d K A S rc L) (x : Adr) :
    Jaune.accessCost x d.accessedAddresses =
      if x ∈ A ∨ x ∈ b.accessedAddresses then gasWarmAccess else gasColdAccountAccess := by
  unfold Jaune.accessCost
  simp only [h.addrs]

/-- A child message built from `P` starts from `P`'s keys, addresses, created accounts and world,
with no refund, log or deletion. -/
theorem DView.initDevm_callMsg (h : DView b d K A S rc L) {sevm : Sevm}
    (hsg : sevm.benvStat.rules.stateGas = none) (gas : Nat) (value : B256) (caller target cadr : Adr)
    (stv st : Bool) (data : Bytes) (code : ByteArray) (dp : Bool) :
    DView b (initDevm (callMsg sevm d gas value caller target cadr stv st data code dp)) K A S 0 []
    where
  keys := h.keys
  addrs := h.addrs
  created := h.created
  state := h.state
  refund := rfl
  logs := by
    change (match sevm.benvStat.rules.stateGas with | none => [] | some _ => _) = []
    rw [hsg]
  deleted a := Std.HashSet.not_mem_emptyWithCapacity

/-- A parent resumed after its child halted cleanly: the union of keys and addresses, the child's
world, the summed refunds, the appended logs. -/
theorem DView.callChildPost {P c : Devm} {K' : List (Adr × B256)} {A' : List Adr} {S' : Jaune.State}
    {rc' : Int} {L' : List Log} (hp : DView b P K A S rc L) (hc : DView b c K' A' S' rc' L')
    (oi os : Nat) : DView b (Lift.callChildPost P c oi os) (K ++ K') (A ++ A') S' (rc + rc')
      (L ++ L') where
  keys k := by
    change k ∈ P.accessedStorageKeys.union c.accessedStorageKeys ↔ _
    refine Std.HashSet.mem_union_iff.trans ?_
    rw [Std.HashSet.contains_iff_mem, Std.HashSet.contains_iff_mem, hp.keys, hc.keys,
      List.mem_append]
  addrs a := by
    change a ∈ P.accessedAddresses.union c.accessedAddresses ↔ _
    refine Std.HashSet.mem_union_iff.trans ?_
    rw [Std.HashSet.contains_iff_mem, Std.HashSet.contains_iff_mem, hp.addrs, hc.addrs,
      List.mem_append]
    constructor
    · rintro ((e | e) | (e | e))
      · exact Or.inl (Or.inl e)
      · exact Or.inr e
      · exact Or.inl (Or.inr e)
      · exact Or.inr e
    · rintro ((e | e) | e)
      · exact Or.inl (Or.inl e)
      · exact Or.inr (Or.inl e)
      · exact Or.inl (Or.inr e)
  created := hc.created
  state := hc.state
  refund := by
    change P.refundCounter + c.refundCounter = _
    rw [hp.refund, hc.refund]
  logs := by
    change P.logs ++ c.logs = _
    rw [hp.logs, hc.logs]
  deleted a := by
    change a ∉ P.accountsToDelete.union c.accountsToDelete
    intro m
    rcases Std.HashSet.mem_union_iff.mp m with e | e
    · exact hp.deleted a (Std.HashSet.contains_iff_mem.mp e)
    · exact hc.deleted a (Std.HashSet.contains_iff_mem.mp e)

end View

end Blanc.Composition.UniswapV2PairWeth9Instance
