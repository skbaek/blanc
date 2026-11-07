import Blanc.Lift.WalkCost
import Blanc.StorageRefund

/-!
# What a coin's successful frame leaves

The contract-neutral carriers of a forward coin law: `Keeps` (the world a coin frame must not
disturb), `FrameLands` (a frame's run, charge, reply, ledger and refund), and the guards a solc
0.5-or-later prologue and ABI wrapper make. Nothing here names a contract.
-/

namespace Blanc.Lift.AccumulatedWalk

open Jaune Blanc Blanc.Lift

/-- **`B` keeps what a coin frame must**: every code, every other account's storage, the error
flag, the created accounts. -/
structure Keeps (sevm : Sevm) (pre B : Devm) : Prop where
  code : ∀ a, B.getCode a = pre.getCode a
  other : ∀ a, a ≠ sevm.currentTarget → Devm.getStor B a = Devm.getStor pre a
  error : B.error = pre.error
  created : B.createdAccounts = pre.createdAccounts

namespace Keeps

variable {sevm : Sevm} {pre B : Devm}

theorem refl (sevm : Sevm) (pre : Devm) : Keeps sevm pre pre := ⟨fun _ => rfl, fun _ _ => rfl, rfl, rfl⟩

theorem sload (h : Keeps sevm pre B) (k : B256) : Keeps sevm pre (afterSload sevm B k) :=
  ⟨fun a => (afterSload_getCode sevm B k a).trans (h.code a),
   fun a ha => (afterSload_getStor sevm B k a).trans (h.other a ha),
   (afterSload_error sevm B k).trans h.error, (afterSload_createdAccounts sevm B k).trans h.created⟩

theorem sstore (h : Keeps sevm pre B) (k v : B256) : Keeps sevm pre (afterSstore sevm B k v) :=
  ⟨fun a => (afterSstore_getCode sevm B k v a).trans (h.code a),
   fun a ha => (afterSstore_getStor_ne sevm B k v a (Ne.symm ha)).trans (h.other a ha),
   (afterSstore_error sevm B k v).trans h.error, (afterSstore_createdAccounts sevm B k v).trans h.created⟩

theorem log (h : Keeps sevm pre B) (l : Log) : Keeps sevm pre (B.addLog l) :=
  ⟨h.code, h.other, h.error, h.created⟩

end Keeps

/-- A first store to a slot still at its snapshot value does not lower the refund counter. -/
theorem sstore_ge {s : Sevm} {d : Devm} {k v : B256} {σ : Stor}
    (hcr : s.currentTarget ∉ d.createdAccounts) (hor : (getOrigAcct s s.currentTarget).stor = σ)
    (hcur : (Devm.getStor d s.currentTarget).get k = σ.get k) :
    d.refundCounter ≤ (afterSstore s d k v).refundCounter :=
  afterSstore_refundCounter_ge_of_original_eq_current s d k v (by
    unfold Devm.getOrigStorVal
    rw [ite_eq_right hcr]
    unfold Jaune.getOrigStorVal
    rw [hor]
    exact hcur.symm)

theorem eqCheck_one {x y : B256} (h : x = y) : B256.eqCheck x y = 1 := by
  subst h
  simp only [B256.eqCheck, ↓reduceIte]

/-- **What a successful frame leaves**: the run of `prog`, its charge `used`, the reply `w`, the ledger
`σ'`, and the rest of the world kept (the refund counter not lowered when `R` holds). -/
structure FrameLands (prog : List SFunc) (sevm : Sevm) (pre post : Devm) (used : Nat) (w : B256) (σ' : Stor)
    (R : Prop) : Prop where
  run : SProg.RunExact prog sevm pre post
  gas : post.gasLeft = pre.gasLeft - used
  out : post.output = w.toBytes
  keeps : Keeps sevm pre post
  stor : Devm.getStor post sevm.currentTarget = σ'
  refund : R → pre.refundCounter ≤ post.refundCounter

/-- A frame run at every residual gas above the store sentry lands. -/
theorem frameLands_of {prog : List SFunc} {f : SFunc} {sevm : Sevm} {pre : Devm} {P : Nat → Devm} {w : B256}
    {c K : Nat} {σ' : Stor} {R : Prop} (hf : prog[0]? = some f)
    (hrun : ∀ G, 2300 ≤ G → SFunc.RunExact prog sevm (St pre [] Mem.empty (G + c)) f (.halted (P G)))
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hc : c ≤ K) (hgas : K + 2300 ≤ pre.gasLeft)
    (hG : ∀ G, (P G).gasLeft = G) (hout : ∀ G, (P G).output = w.toBytes) (hk : ∀ G, Keeps sevm pre (P G))
    (hst : ∀ G, Devm.getStor (P G) sevm.currentTarget = σ')
    (hr : R → ∀ G, pre.refundCounter ≤ (P G).refundCounter) :
    FrameLands prog sevm pre (P (pre.gasLeft - c)) c w σ' R := by
  refine ⟨⟨f, hf, ?_⟩, hG _, hout _, hk _, hst _, fun r => hr r _⟩
  have h := hrun (pre.gasLeft - c) (by omega)
  rwa [pre_eq_St hs hm (Nat.sub_add_cancel (by omega))] at h

/-- A frame's selector word as a solc 0.5-or-later dispatcher reads it. -/
abbrev selW (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [0]) >>> (Bytes.toB256 [224]).toNat

/-- The guards a frame's prologue and wrapper make, with `n` argument words. -/
structure Guards (sevm : Sevm) (sel n : B256) : Prop where
  value : sevm.value = 0
  short : (Nat.toB256 sevm.data.length <? Bytes.toB256 [4]) = 0
  args : ((Nat.toB256 sevm.data.length - Bytes.toB256 [4]) <? n) = 0
  sel : selW sevm = sel

/-- The wrapper's argument-size guard, from the calldata's length. -/
theorem args_of_le {n : Nat} {w : B256} (h : w.toNat + 4 ≤ n) (hn : n < 2 ^ 256) :
    B256.ltCheck (Nat.toB256 n - Bytes.toB256 [4]) w = 0 := by
  have h4 : (Bytes.toB256 [4]).toNat = 4 := by decide
  have le : Bytes.toB256 [4] ≤ Nat.toB256 n := by
    apply B256.not_lt.mp
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hn, h4]
    omega
  apply B256.ltCheck_eq_zero_of_toNat_le
  rw [B256.toNat_sub_eq_of_le _ _ le, B256.toNat_toB256_of_lt hn, h4]
  omega

theorem guards_of {e : Sevm} {sel w : B256} (hv : e.value = 0) (hsel : Blanc.Sevm.selector e = sel)
    (hlen : w.toNat + 4 ≤ e.data.length) (hn : e.data.length < 2 ^ 256) : Guards e sel w :=
  ⟨hv, short_of_len (by omega) hn, args_of_le hlen hn, hsel⟩

end Blanc.Lift.AccumulatedWalk
