import Blanc.Lift.Usdc.Footprint

/-!
# The USDC footprint ledger across storage writes

Read lemmas (`ledger_bal`, …: a tracked key's ledger entry is its storage word, read as the code
reads it), write lemmas (one per storage-write family: the packed balance word, allowance, nonce,
authorization state, minter flag, minter allowance, and each fixed word: the ledger of the written
storage is the matching `Ledger` update, under `Inj`/`Apart` and the written key tracked), and
`FootInv` preservation (a write at a tracked key or a fixed word keeps the support; mapping writes
keep `Good`; a step's result is good by `step_good`; touching fresh keys extends the footprint).
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.SlotFootprint

/-- The packed word of `a` becomes `w`: balance bits and blacklist flag together. -/
def Ledger.setWord (l : Ledger) (a : Adr) (w : B256) : Ledger :=
  { l with bal := Function.update l.bal a (balanceBits w),
           frozen := Function.update l.frozen a (frozenBit w) }

/-- A packed write that keeps the flag is the model's balance write. -/
theorem Ledger.setWord_eq_setBal {l : Ledger} {a : Adr} {w : B256}
    (flag : frozenBit w = l.frozen a) : l.setWord a w = l.setBal a (balanceBits w) := by
  unfold Ledger.setWord Ledger.setBal
  rw [flag, Function.update_eq_self]

/-- A packed write that keeps the balance bits is the model's blacklist write. -/
theorem Ledger.setWord_eq_setFrozen {l : Ledger} {a : Adr} {w : B256}
    (bits : balanceBits w = l.bal a) : l.setWord a w = l.setFrozen a (frozenBit w) := by
  unfold Ledger.setWord Ledger.setFrozen
  rw [bits, Function.update_eq_self]

/-! ## Reading the ledger -/

section Read

variable {K : Key → Prop} {s : Stor}

theorem ledger_bal {a : Adr} (h : K (.bal a)) :
    (ledger K s).bal a = balanceBits (s.get (balSlot a)) := by
  simp only [ledger, ledgerOf, trackedWord_of_mem h, Key.slot]

theorem ledger_frozen {a : Adr} (h : K (.bal a)) :
    (ledger K s).frozen a = frozenBit (s.get (balSlot a)) := by
  simp only [ledger, ledgerOf, trackedWord_of_mem h, Key.slot]

theorem ledger_allow {o p : Adr} (h : K (.allow o p)) :
    (ledger K s).allow o p = (s.get (allowSlot o p)).toNat := by
  simp only [ledger, ledgerOf, trackedWord_of_mem h, Key.slot]

theorem ledger_nonce {a : Adr} (h : K (.nonce a)) :
    (ledger K s).nonce a = (s.get (nonceSlot a)).toNat := by
  simp only [ledger, ledgerOf, trackedWord_of_mem h, Key.slot]

theorem ledger_authUsed {a : Adr} {n : B256} (h : K (.auth a n)) :
    (ledger K s).authUsed a n = boolBit (s.get (authSlot a n)) := by
  simp only [ledger, ledgerOf, trackedWord_of_mem h, Key.slot]

theorem ledger_minter {a : Adr} (h : K (.minter a)) :
    (ledger K s).minter a = boolBit (s.get (minterSlot a)) := by
  simp only [ledger, ledgerOf, trackedWord_of_mem h, Key.slot]

theorem ledger_minterAllowance {a : Adr} (h : K (.minterAllowance a)) :
    (ledger K s).minterAllowance a = (s.get (minterAllowanceSlot a)).toNat := by
  simp only [ledger, ledgerOf, trackedWord_of_mem h, Key.slot]

end Read

/-! ## Mapping writes -/

/-- `ledgerOf` reads its storage words only at fixed slots. -/
theorem ledgerOf_congr_fixed {m : Key → B256} {f f' : B256 → B256}
    (h : ∀ x ∈ fixedSlots, f x = f' x) : ledgerOf m f = ledgerOf m f' := by
  have e : ∀ x, x ∈ fixedSlots → f x = f' x := h
  unfold ledgerOf
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 8 (by decide), e 11 (by decide),
    e 14 (by decide), e 18 (by decide), e adminSlot (by decide)]

/-- A write at a tracked key's slot changes the tracked words at that key and no fixed word. -/
theorem ledger_set_key {K : Key → Prop} {s : Stor} (inj : Inj Key.slot K)
    (apart : Apart Key.slot fixedSlots K) {k : Key} (hk : K k) (w : B256) :
    ledger K (s.set k.slot w) = ledgerOf (Function.update (trackedWord Key.slot K s) k w) s.get := by
  unfold ledger
  rw [trackedWord_set inj hk]
  apply ledgerOf_congr_fixed
  intro x hx
  exact Stor.get_set_ne _ (fun e => apart k hk (by rw [e]; exact hx)) w

section Writes

variable {K : Key → Prop} {s : Stor} (inj : Inj Key.slot K) (apart : Apart Key.slot fixedSlots K)
include inj apart

/-- **A packed balance-word write** is the ledger's packed write. -/
theorem ledger_set_bal {a : Adr} (h : K (.bal a)) (w : B256) :
    ledger K (s.set (balSlot a) w) = (ledger K s).setWord a w := by
  rw [show balSlot a = (Key.bal a).slot from rfl, ledger_set_key inj apart h]
  unfold ledger ledgerOf Ledger.setWord
  congr 1 <;> funext <;>
    simp only [Function.update_apply, Key.bal.injEq] <;> split_ifs <;> rfl

/-- **An allowance write** is the ledger's allowance write. -/
theorem ledger_set_allow {o p : Adr} (h : K (.allow o p)) (w : B256) :
    ledger K (s.set (allowSlot o p) w) = (ledger K s).setAllow o p w.toNat := by
  rw [show allowSlot o p = (Key.allow o p).slot from rfl, ledger_set_key inj apart h]
  unfold ledger ledgerOf Ledger.setAllow
  congr 1
  funext
  simp only [Function.update_apply, Key.allow.injEq]
  split_ifs <;> rfl

/-- **A permit-nonce write** sets that nonce. -/
theorem ledger_set_nonce {a : Adr} (h : K (.nonce a)) (w : B256) :
    ledger K (s.set (nonceSlot a) w) =
      { ledger K s with nonce := Function.update (ledger K s).nonce a w.toNat } := by
  rw [show nonceSlot a = (Key.nonce a).slot from rfl, ledger_set_key inj apart h]
  unfold ledger ledgerOf
  congr 1
  funext
  simp only [Function.update_apply, Key.nonce.injEq]
  split_ifs <;> rfl

/-- The nonce write of `_permitNonces[o]++` is the model's `bumpNonce`. -/
theorem ledger_set_nonce_bump {a : Adr} (h : K (.nonce a)) {w : B256}
    (hw : w.toNat = ((ledger K s).nonce a + 1) % 2 ^ 256) :
    ledger K (s.set (nonceSlot a) w) = (ledger K s).bumpNonce a := by
  rw [ledger_set_nonce inj apart h, hw]
  rfl

/-- **An authorization-state write of `true`** is the model's `useAuth`. -/
theorem ledger_set_auth {a : Adr} {n : B256} (h : K (.auth a n)) {w : B256}
    (hw : boolBit w = true) :
    ledger K (s.set (authSlot a n) w) = (ledger K s).useAuth a n := by
  rw [show authSlot a n = (Key.auth a n).slot from rfl, ledger_set_key inj apart h]
  unfold ledger ledgerOf Ledger.useAuth
  congr 1
  funext
  simp only [Function.update_apply, Key.auth.injEq]
  split_ifs <;> first | rfl | exact hw

/-- **A minter-flag write** sets that flag. -/
theorem ledger_set_minter {a : Adr} (h : K (.minter a)) (w : B256) :
    ledger K (s.set (minterSlot a) w) =
      { ledger K s with minter := Function.update (ledger K s).minter a (boolBit w) } := by
  rw [show minterSlot a = (Key.minter a).slot from rfl, ledger_set_key inj apart h]
  unfold ledger ledgerOf
  congr 1
  funext
  simp only [Function.update_apply, Key.minter.injEq]
  split_ifs <;> rfl

/-- **A minter-allowance write** is the model's `setMinterAllowance`. -/
theorem ledger_set_minterAllowance {a : Adr} (h : K (.minterAllowance a)) (w : B256) :
    ledger K (s.set (minterAllowanceSlot a) w) = (ledger K s).setMinterAllowance a w.toNat := by
  rw [show minterAllowanceSlot a = (Key.minterAllowance a).slot from rfl,
    ledger_set_key inj apart h]
  unfold ledger ledgerOf Ledger.setMinterAllowance
  congr 1
  funext
  simp only [Function.update_apply, Key.minterAllowance.injEq]
  split_ifs <;> rfl

end Writes

/-! ## Fixed-word writes -/

section Fixed

variable {K : Key → Prop} {s : Stor} (apart : Apart Key.slot fixedSlots K)
include apart

/-- A write at a fixed slot leaves the tracked words alone. -/
theorem ledger_set_fixed {x : B256} (hx : x ∈ fixedSlots) (w : B256) :
    ledger K (s.set x w) = ledgerOf (trackedWord Key.slot K s) (s.set x w).get := by
  unfold ledger
  rw [trackedWord_set_off (fun k hk e => apart k hk (by rw [e]; exact hx))]

/-- **`_owner` (slot 0).** -/
theorem ledger_set_owner (w : B256) :
    ledger K (s.set 0 w) = { ledger K s with owner := w.toAdr } := by
  rw [ledger_set_fixed apart (by decide)]
  unfold ledger ledgerOf
  simp (disch := decide) only [Stor.get_set_self, Stor.get_set_ne]

/-- **`pauser` and `paused` (slot 1).** -/
theorem ledger_set_pauser (w : B256) :
    ledger K (s.set 1 w) = { ledger K s with pauser := w.toAdr, paused := flag20 w } := by
  rw [ledger_set_fixed apart (by decide)]
  unfold ledger ledgerOf
  simp (disch := decide) only [Stor.get_set_self, Stor.get_set_ne]

/-- **`blacklister` (slot 2).** -/
theorem ledger_set_blacklister (w : B256) :
    ledger K (s.set 2 w) = { ledger K s with blacklister := w.toAdr } := by
  rw [ledger_set_fixed apart (by decide)]
  unfold ledger ledgerOf
  simp (disch := decide) only [Stor.get_set_self, Stor.get_set_ne]

/-- **`masterMinter` and `initialized` (slot 8).** -/
theorem ledger_set_masterMinter (w : B256) :
    ledger K (s.set 8 w) =
      { ledger K s with masterMinter := w.toAdr, initialized := flag20 w } := by
  rw [ledger_set_fixed apart (by decide)]
  unfold ledger ledgerOf
  simp (disch := decide) only [Stor.get_set_self, Stor.get_set_ne]

/-- **`totalSupply_` (slot 11).** -/
theorem ledger_set_supply (w : B256) :
    ledger K (s.set 11 w) = { ledger K s with supply := w.toNat } := by
  rw [ledger_set_fixed apart (by decide)]
  unfold ledger ledgerOf
  simp (disch := decide) only [Stor.get_set_self, Stor.get_set_ne]

/-- **`_rescuer` (slot 14).** -/
theorem ledger_set_rescuer (w : B256) :
    ledger K (s.set 14 w) = { ledger K s with rescuer := w.toAdr } := by
  rw [ledger_set_fixed apart (by decide)]
  unfold ledger ledgerOf
  simp (disch := decide) only [Stor.get_set_self, Stor.get_set_ne]

/-- **`_initializedVersion` (slot 18).** -/
theorem ledger_set_version (w : B256) :
    ledger K (s.set 18 w) = { ledger K s with version := w.toNat % 256 } := by
  rw [ledger_set_fixed apart (by decide)]
  unfold ledger ledgerOf
  simp (disch := decide) only [Stor.get_set_self, Stor.get_set_ne]

/-- **The proxy's admin word.** -/
theorem ledger_set_admin (w : B256) :
    ledger K (s.set adminSlot w) = { ledger K s with admin := w.toAdr } := by
  rw [ledger_set_fixed apart (by decide)]
  unfold ledger ledgerOf
  simp (disch := decide) only [Stor.get_set_self, Stor.get_set_ne]

/-- **The words the ledger does not read** (`name`, `symbol`, `decimals`, `currency`, the
deprecated domain separator, the implementation slot). -/
theorem ledger_set_inert {x : B256} (hx : x ∈ [4, 5, 6, 7, 15, implSlot]) (w : B256) :
    ledger K (s.set x w) = ledger K s := by
  have hx' : x ∈ fixedSlots := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [ledger_set_fixed apart hx']
  unfold ledger ledgerOf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [Stor.get_set_ne]

end Fixed

/-! ## The footprint invariant across writes -/

/-- `Good` reads only the `initialized` and version words (balance bits always fit). -/
theorem ledger_good_congr {K K' : Key → Prop} {s s' : Stor} (good : (ledger K s).Good)
    (h8 : s'.get 8 = s.get 8) (h18 : s'.get 18 = s.get 18) : (ledger K' s').Good := by
  refine ⟨fun a => Nat.mod_lt _ (Nat.two_pow_pos 255), ?_, ?_⟩
  · show flag20 (s'.get 8) = true
    rw [h8]
    exact good.initialized
  · show (s'.get 18).toNat % 256 = 3
    rw [h18]
    exact good.version

section Inv

variable {K : Key → Prop} {s : Stor}

/-- **A write at a tracked key keeps the footprint invariant** (mapping words never touch the
`initialized` and version words). -/
theorem FootInv.set_key (h : FootInv K s) {k : Key} (hk : K k) (w : B256) :
    FootInv K (s.set k.slot w) := by
  have off : ∀ x ∈ fixedSlots, (s.set k.slot w).get x = s.get x := fun x hx =>
    Stor.get_set_ne _ (fun e => h.apart k hk (by rw [e]; exact hx)) w
  exact ⟨h.support.set hk w, h.inj, h.apart,
    ledger_good_congr h.good (off 8 (by decide)) (off 18 (by decide))⟩

/-- A write at a fixed word keeps the support; `Good` is the write's to show. -/
theorem FootInv.set_fixed (h : FootInv K s) {x : B256} (hx : x ∈ fixedSlots) (w : B256)
    (good : (ledger K (s.set x w)).Good) : FootInv K (s.set x w) :=
  ⟨h.support.set_fixed hx w, h.inj, h.apart, good⟩

/-- **A committed step keeps the footprint invariant**: the support is the writes' (`Support.set`,
`Support.set_fixed`), `Good` is `step_good`'s. -/
theorem FootInv.of_step (h : FootInv K s) {s' : Stor} (support : Support Key.slot fixedSlots K s')
    {self caller : Adr} {c : Call} {l' : Ledger}
    (st : (ledger K s).step self caller c = some l') (eq : ledger K s' = l') : FootInv K s' :=
  ⟨support, h.inj, h.apart, eq ▸ Ledger.step_good h.good st⟩

/-- **Touching fresh keys leaves the ledger alone.** -/
theorem ledger_extend {ks : List Key} (support : Support Key.slot fixedSlots K s)
    (fresh : KeysFresh K ks) : ledger (extendBy K ks) s = ledger K s := by
  unfold ledger
  rw [trackedWord_extend support fresh]

/-- **Touching fresh keys extends the footprint invariant.** -/
theorem FootInv.extend (h : FootInv K s) {ks : List Key} (fresh : KeysFresh K ks) :
    FootInv (extendBy K ks) s := by
  refine ⟨h.support.mono (fun k hk => Or.inl hk), h.inj.extend fresh, h.apart.extend fresh, ?_⟩
  rw [ledger_extend h.support fresh]
  exact h.good

end Inv

end Blanc.Lift.Usdc
