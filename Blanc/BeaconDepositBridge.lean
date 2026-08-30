import Blanc.BeaconDepositCore
import Blanc.BeaconDepositCorrectness

/-!
# Beacon deposit concrete/model storage bridge

The three persistent regions of the compiled artifact are disjoint.  This
module packages their total abstraction, the constructor's canonical target
storage, and the pure preservation lemmas consumed by the compiled C6
endpoints.  Execution of the constructor is proved separately; the target
defined here is independent of that walk.
-/

namespace Blanc.BeaconDeposit

open Jaune

/-- The artifact invariant combines the constructor-owned zero-hash region
with the model/history invariant over the branch and count regions. -/
def ArtifactInv (stor : Stor) (history : List B256) : Prop :=
  ZeroHashesCorrect stor ∧
    Inv Bytes.sha256 (accOfStor stor) history

/-! ## Region separation -/

theorem branchSlot_injective
    {left right : Nat} (leftBound : left < 32) (rightBound : right < 32)
    (equal : branchSlot left = branchSlot right) :
    left = right := by
  have equalNat := congrArg B256.toNat equal
  simp only [branchSlot] at equalNat
  rw [B256.toNat_toB256_of_lt (by omega : 0x100 + left < 2 ^ 256),
    B256.toNat_toB256_of_lt (by omega : 0x100 + right < 2 ^ 256)] at equalNat
  omega

theorem zeroHashSlot_injective
    {left right : Nat} (leftBound : left < 32) (rightBound : right < 32)
    (equal : zeroHashSlot left = zeroHashSlot right) :
    left = right := by
  have equalNat := congrArg B256.toNat equal
  simp only [zeroHashSlot] at equalNat
  rw [B256.toNat_toB256_of_lt (by omega : 0x300 + left < 2 ^ 256),
    B256.toNat_toB256_of_lt (by omega : 0x300 + right < 2 ^ 256)] at equalNat
  omega

theorem branchSlot_ne_depositCountSlot
    {height : Nat} (bound : height < 32) :
    branchSlot height ≠ depositCountSlot := by
  intro equal
  have equalNat := congrArg B256.toNat equal
  simp only [branchSlot, depositCountSlot] at equalNat
  rw [B256.toNat_toB256_of_lt (by omega : 0x100 + height < 2 ^ 256),
    show (0x200 : B256).toNat = 0x200 by decide +kernel] at equalNat
  omega

theorem branchSlot_ne_zeroHashSlot
    {branchHeight zeroHeight : Nat}
    (branchBound : branchHeight < 32) (zeroBound : zeroHeight < 32) :
    branchSlot branchHeight ≠ zeroHashSlot zeroHeight := by
  intro equal
  have equalNat := congrArg B256.toNat equal
  simp only [branchSlot, zeroHashSlot] at equalNat
  rw [B256.toNat_toB256_of_lt
        (by omega : 0x100 + branchHeight < 2 ^ 256),
    B256.toNat_toB256_of_lt
        (by omega : 0x300 + zeroHeight < 2 ^ 256)] at equalNat
  omega

theorem depositCountSlot_ne_zeroHashSlot
    {height : Nat} (bound : height < 32) :
    depositCountSlot ≠ zeroHashSlot height := by
  intro equal
  have equalNat := congrArg B256.toNat equal
  simp only [depositCountSlot, zeroHashSlot] at equalNat
  rw [show (0x200 : B256).toNat = 0x200 by decide +kernel,
    B256.toNat_toB256_of_lt (by omega : 0x300 + height < 2 ^ 256)] at equalNat
  omega

/-! ## Constructor target storage -/

/-- Storage after materializing zero-hash slots `1` through `height`.
Slot zero deliberately remains the EVM default zero. -/
def constructorZeroHashStorage : Nat → Stor
  | 0 => Stor.empty
  | height + 1 =>
      (constructorZeroHashStorage height).set (zeroHashSlot (height + 1))
        (zeroHash Bytes.sha256 (height + 1))

def constructorFinalStorage : Stor :=
  constructorZeroHashStorage 31

theorem constructorZeroHashStorage_get_of_pos_le
    {height limit : Nat} (positive : 0 < height) (le : height ≤ limit)
    (limitBound : limit < 32) :
    (constructorZeroHashStorage limit).get (zeroHashSlot height) =
      zeroHash Bytes.sha256 height := by
  induction limit with
  | zero => omega
  | succ limit ih =>
      by_cases equal : height = limit + 1
      · subst height
        simp only [constructorZeroHashStorage, Stor.get_set_self]
      · rw [constructorZeroHashStorage,
          Stor.get_set_ne _ (by
            intro slotEqual
            apply equal
            exact zeroHashSlot_injective (by omega) (by omega)
              slotEqual.symm) _]
        exact ih (by omega) (by omega)

theorem constructorZeroHashStorage_get_zero
    {limit : Nat} (limitBound : limit < 32) :
    (constructorZeroHashStorage limit).get (zeroHashSlot 0) = 0 := by
  induction limit with
  | zero => rfl
  | succ limit ih =>
      rw [constructorZeroHashStorage,
        Stor.get_set_ne _ (by
          intro slotEqual
          have impossible := zeroHashSlot_injective
            (left := limit + 1) (right := 0) (by omega) (by omega)
            slotEqual
          omega) _, ih (by omega)]

theorem constructorFinalStorage_zeroHashesCorrect :
    ZeroHashesCorrect constructorFinalStorage := by
  intro height bound
  rcases Nat.eq_zero_or_pos height with rfl | positive
  · exact constructorZeroHashStorage_get_zero (limit := 31) (by omega)
  · exact constructorZeroHashStorage_get_of_pos_le positive (by omega)
      (by omega)

private theorem constructorZeroHashStorage_get_of_region_ne
    {key : B256} {limit : Nat} (limitBound : limit < 32)
    (separate : ∀ height, 0 < height → height ≤ limit →
      key ≠ zeroHashSlot height) :
    (constructorZeroHashStorage limit).get key = 0 := by
  induction limit with
  | zero => rfl
  | succ limit ih =>
      rw [constructorZeroHashStorage,
        Stor.get_set_ne _ (separate (limit + 1) (by omega) (by omega)).symm _,
        ih (by omega)]
      intro height positive le
      exact separate height positive (by omega)

theorem accOfStor_constructorFinalStorage :
    accOfStor constructorFinalStorage = Acc.empty := by
  unfold accOfStor Acc.empty constructorFinalStorage
  apply congrArg₂ Acc.mk
  · funext height
    by_cases bound : height < 32
    · simp only [bound, if_true]
      apply constructorZeroHashStorage_get_of_region_ne (limit := 31) (by omega)
      intro zeroHeight positive le
      exact branchSlot_ne_zeroHashSlot bound (by omega)
    · simp only [bound, if_false]
  · have countWord :
        (constructorZeroHashStorage 31).get depositCountSlot = 0 := by
      apply constructorZeroHashStorage_get_of_region_ne (limit := 31) (by omega)
      intro height positive le
      exact depositCountSlot_ne_zeroHashSlot (by omega)
    rw [countWord, show (0 : B256).toNat = 0 by decide +kernel]

theorem constructorFinalStorage_artifactInv :
    ArtifactInv constructorFinalStorage [] := by
  refine ⟨constructorFinalStorage_zeroHashesCorrect, ?_⟩
  rw [accOfStor_constructorFinalStorage]
  exact empty_inv Bytes.sha256

/-- C4-to-C6 seam.  A root-view result phrased over the concrete storage
projection is the reference mixed root of the history carried by the artifact
invariant. -/
theorem ArtifactInv.root_eq_mixedRootOf
    {stor : Stor} {history : List B256}
    (invariant : ArtifactInv stor history) :
    Acc.root Bytes.sha256 (accOfStor stor) =
      mixedRootOf Bytes.sha256 history :=
  root_correct Bytes.sha256 (accOfStor stor) history invariant.2

/-- C4 count-view seam: the concrete count projection is exactly the model
history length carried by the artifact invariant. -/
theorem ArtifactInv.count_eq_history_length
    {stor : Stor} {history : List B256}
    (invariant : ArtifactInv stor history) :
    (accOfStor stor).count = history.length :=
  invariant.2.1

/-! ## Deposit-region updates -/

/-- The two concrete successful-deposit writes, in their retained execution
order: increment the count, then write the unique first-live branch cell. -/
def applyDepositWrites
    (stor : Stor) (height : Nat) (node : B256) : Stor :=
  (stor.set depositCountSlot
      (Nat.toB256 (accOfStor stor).count + 1)).set
    (branchSlot height) node

theorem ZeroHashesCorrect.applyDepositWrites
    {stor : Stor} {height : Nat} {node : B256}
    (correct : ZeroHashesCorrect stor) (heightBound : height < 32) :
    ZeroHashesCorrect (applyDepositWrites stor height node) := by
  intro zeroHeight zeroBound
  calc
    (_root_.Blanc.BeaconDeposit.applyDepositWrites stor height node).get
        (zeroHashSlot zeroHeight) =
        (stor.set depositCountSlot
          (Nat.toB256 (accOfStor stor).count + 1)).get
            (zeroHashSlot zeroHeight) := by
      exact Stor.get_set_ne _
        (branchSlot_ne_zeroHashSlot heightBound zeroBound) _
    _ = stor.get (zeroHashSlot zeroHeight) := by
      exact Stor.get_set_ne _
        (depositCountSlot_ne_zeroHashSlot zeroBound) _
    _ = zeroHash Bytes.sha256 zeroHeight := correct zeroHeight zeroBound

theorem accOfStor_countWrite_branch
    (stor : Stor) :
    (accOfStor
      (stor.set depositCountSlot
        (Nat.toB256 (accOfStor stor).count + 1))).branch =
      (accOfStor stor).branch := by
  funext height
  by_cases bound : height < 32
  · simp only [accOfStor, bound, if_true,
      Stor.get_set_ne _ (branchSlot_ne_depositCountSlot bound).symm _]
  · simp only [accOfStor, bound, if_false]

theorem accOfStor_applyDepositWrites
    (stor : Stor) (height : Nat) (node : B256)
    (heightBound : height < 32)
    (countBound : (accOfStor stor).count < 2 ^ 32 - 1) :
    accOfStor (applyDepositWrites stor height node) =
      ⟨setSlot (accOfStor stor).branch height node,
        (accOfStor stor).count + 1⟩ := by
  unfold accOfStor
  apply congrArg₂ Acc.mk
  · funext selected
    by_cases selectedBound : selected < 32
    · simp only [selectedBound, if_true, applyDepositWrites, setSlot]
      by_cases same : selected = height
      · subst selected
        rw [Stor.get_set_self]
        simp
      · have keyNe : branchSlot height ≠ branchSlot selected := by
          intro slotEqual
          apply same
          exact (branchSlot_injective heightBound selectedBound slotEqual).symm
        rw [if_neg same,
          Stor.get_set_ne _ keyNe _,
          Stor.get_set_ne _
            (branchSlot_ne_depositCountSlot selectedBound).symm _]
    · simp only [selectedBound, if_false, setSlot,
        if_neg (by omega : selected ≠ height)]
  · rw [applyDepositWrites,
      Stor.get_set_ne _ (branchSlot_ne_depositCountSlot heightBound) _,
      Stor.get_set_self,
      B256.toNat_add_eq_of_nof]
    · rw [B256.toNat_toB256_of_lt (by omega)]
      rfl
    · unfold B256.Nof
      rw [B256.toNat_toB256_of_lt (by omega),
        show (1 : B256).toNat = 1 by decide +kernel]
      omega

/-- The concrete count/branch update realizes the model success result at the
unique first-live height. -/
theorem accOfStor_applyDepositWrites_eq_model
    (stor : Stor) (height : Nat)
    (pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256) (s' : Acc) (ev : DepositEvent)
    (value : Nat)
    (success : deposit Bytes.sha256 (accOfStor stor) pubkey
      withdrawalCredentials signature depositDataRoot value = .ok (s', ev))
    (heightBound : height < 32)
    (firstLive : FirstLive ((accOfStor stor).count + 1) height) :
    accOfStor
        (applyDepositWrites stor height
          (accumulatedNode Bytes.sha256 (accOfStor stor).branch
            0 height depositDataRoot)) = s' := by
  obtain ⟨-, -, -, -, -, -, rootEq, countBound, -, -, -⟩ :=
    deposit_ok_spec Bytes.sha256 (accOfStor stor) pubkey
      withdrawalCredentials signature depositDataRoot value s' ev success
  have result := deposit_ok_result_eq_firstLive Bytes.sha256
    (accOfStor stor) pubkey withdrawalCredentials signature depositDataRoot
    value s' ev success heightBound firstLive
  have stateEq := congrArg Prod.fst result
  rw [accOfStor_applyDepositWrites stor height _ heightBound countBound]
  simpa only [rootEq] using stateEq.symm

/-- Pure C6 preservation: the exact two-cell concrete update transfers the
model/history invariant while leaving the constructor-owned region intact. -/
theorem ArtifactInv.applyDepositWrites
    {stor : Stor} {history : List B256} {height : Nat}
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {s' : Acc} {ev : DepositEvent} {value : Nat}
    (invariant : ArtifactInv stor history)
    (success : deposit Bytes.sha256 (accOfStor stor) pubkey
      withdrawalCredentials signature depositDataRoot value = .ok (s', ev))
    (heightBound : height < 32)
    (firstLive : FirstLive ((accOfStor stor).count + 1) height) :
    ArtifactInv
      (applyDepositWrites stor height
        (accumulatedNode Bytes.sha256 (accOfStor stor).branch
          0 height depositDataRoot))
      (history ++ [depositDataNode Bytes.sha256 pubkey
        withdrawalCredentials signature (le64 (value / oneGwei))]) := by
  refine ⟨invariant.1.applyDepositWrites heightBound, ?_⟩
  rw [accOfStor_applyDepositWrites_eq_model stor height pubkey
    withdrawalCredentials signature depositDataRoot s' ev value success
    heightBound firstLive]
  exact deposit_inv Bytes.sha256 (accOfStor stor) history pubkey
    withdrawalCredentials signature depositDataRoot value s' ev invariant.2
    success

/-- Normalization into the exact storage expression exported by C2: its
branch value is phrased over the count-updated intermediate map. -/
theorem applyDepositWrites_eq_successStorage
    (stor : Stor) (height : Nat) (depositDataRoot : B256) :
    applyDepositWrites stor height
        (accumulatedNode Bytes.sha256 (accOfStor stor).branch
          0 height depositDataRoot) =
      (stor.set depositCountSlot
        (Nat.toB256 (accOfStor stor).count + 1)).set
        (branchSlot height)
        (accumulatedNode Bytes.sha256
          (accOfStor
            (stor.set depositCountSlot
              (Nat.toB256 (accOfStor stor).count + 1))).branch
          0 height depositDataRoot) := by
  unfold applyDepositWrites
  rw [accOfStor_countWrite_branch]

/-- C2-to-C6 seam.  Any compiled poststate carrying C2's exact count-then-
branch storage expression inherits the artifact invariant and the appended
model history. -/
theorem ArtifactInv.of_depositSuccessStorage
    {stor postStor : Stor} {history : List B256} {height : Nat}
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {s' : Acc} {ev : DepositEvent} {value : Nat}
    (invariant : ArtifactInv stor history)
    (success : deposit Bytes.sha256 (accOfStor stor) pubkey
      withdrawalCredentials signature depositDataRoot value = .ok (s', ev))
    (heightBound : height < 32)
    (firstLive : FirstLive ((accOfStor stor).count + 1) height)
    (postStorage : postStor =
      (stor.set depositCountSlot
        (Nat.toB256 (accOfStor stor).count + 1)).set
        (branchSlot height)
        (accumulatedNode Bytes.sha256
          (accOfStor
            (stor.set depositCountSlot
              (Nat.toB256 (accOfStor stor).count + 1))).branch
          0 height depositDataRoot)) :
    ArtifactInv postStor
      (history ++ [depositDataNode Bytes.sha256 pubkey
        withdrawalCredentials signature (le64 (value / oneGwei))]) := by
  rw [postStorage, ← applyDepositWrites_eq_successStorage]
  exact invariant.applyDepositWrites success heightBound firstLive

/-- Direct C2-to-C6 adapter over the storage fields exported by
`deposit_success_runCompiled`.  The intermediate map is the count write and
the compiled post map is its subsequent first-live branch write. -/
theorem ArtifactInv.of_depositSuccessCompiledStorage
    {base post : Devm} {storageTarget : Adr} {stor : Stor}
    {history : List B256} {height : Nat}
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {s' : Acc} {ev : DepositEvent} {value : Nat}
    (invariant : ArtifactInv
      (Devm.getStor base storageTarget) history)
    (success : deposit Bytes.sha256
      (accOfStor (Devm.getStor base storageTarget)) pubkey
      withdrawalCredentials signature depositDataRoot value = .ok (s', ev))
    (heightBound : height < 32)
    (firstLive : FirstLive
      ((accOfStor (Devm.getStor base storageTarget)).count + 1) height)
    (countStorage : stor =
      (Devm.getStor base storageTarget).set depositCountSlot
        (Nat.toB256
          (accOfStor (Devm.getStor base storageTarget)).count + 1))
    (postStorage : Devm.getStor post storageTarget =
      stor.set (branchSlot height)
        (accumulatedNode Bytes.sha256 (accOfStor stor).branch
          0 height depositDataRoot)) :
    ArtifactInv (Devm.getStor post storageTarget)
      (history ++ [depositDataNode Bytes.sha256 pubkey
        withdrawalCredentials signature (le64 (value / oneGwei))]) := by
  have exactStorage :
      Devm.getStor post storageTarget =
        _root_.Blanc.BeaconDeposit.applyDepositWrites
          (Devm.getStor base storageTarget) height
          (accumulatedNode Bytes.sha256
            (accOfStor (Devm.getStor base storageTarget)).branch
            0 height depositDataRoot) := by
    rw [postStorage, countStorage]
    exact (applyDepositWrites_eq_successStorage
      (Devm.getStor base storageTarget) height depositDataRoot).symm
  rw [exactStorage]
  exact invariant.applyDepositWrites success heightBound firstLive

end Blanc.BeaconDeposit
