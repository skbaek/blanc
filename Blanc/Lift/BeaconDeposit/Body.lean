import Blanc.Lift.BeaconDeposit.BodyGuards
import Blanc.Lift.BeaconDeposit.BodyEvent
import Blanc.Lift.BeaconDeposit.BodyPubkeyRoot
import Blanc.Lift.BeaconDeposit.BodySignatureRoot
import Blanc.Lift.BeaconDeposit.BodyNode
import Blanc.Lift.BeaconDeposit.BodyCount
import Blanc.Lift.BeaconDeposit.BodyInsertDead
import Blanc.Lift.BeaconDeposit.BodyInsertLive
import Jaune.MulDiv

/-!
# The deployed `deposit` body: success, composed from its segments
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-! ## The insertion walk, arithmetically -/

section Walk

open Blanc.BeaconDeposit

theorem insertDepth_lt : ∀ (fuel x : Nat), 1 ≤ x → x < 2 ^ fuel → insertDepth fuel x < fuel
  | 0, x, h1, h2 => by simp at h2; omega
  | fuel + 1, x, h1, h2 => by
    unfold insertDepth
    split_ifs with h
    · omega
    · have := insertDepth_lt fuel (x / 2) (by omega) (by rw [Nat.pow_succ] at h2; omega)
      omega

theorem insertDepth_dead : ∀ (fuel x h : Nat), h < insertDepth fuel x → (x / 2 ^ h) % 2 = 0
  | 0, x, h, hh => by simp [insertDepth] at hh
  | fuel + 1, x, h, hh => by
    unfold insertDepth at hh
    split_ifs at hh with hx
    · omega
    · rcases h with _ | h
      · simpa using hx
      · have := insertDepth_dead fuel (x / 2) h (by omega)
        rwa [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]

theorem insertDepth_live : ∀ (fuel x : Nat), 1 ≤ x → x < 2 ^ fuel →
    (x / 2 ^ insertDepth fuel x) % 2 = 1
  | 0, x, h1, h2 => by simp at h2; omega
  | fuel + 1, x, h1, h2 => by
    unfold insertDepth
    split_ifs with hx
    · simpa using hx
    · have := insertDepth_live fuel (x / 2) (by omega) (by rw [Nat.pow_succ] at h2; omega)
      rwa [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]

theorem walk_insertNode (H : Bytes → B256) (br : Nat → B256) (node0 : B256) :
    ∀ (fuel h x : Nat), 1 ≤ x → x < 2 ^ fuel →
      walk H br fuel h x (insertNode H br h node0) =
        some (setSlot br (h + insertDepth fuel x)
          (insertNode H br (h + insertDepth fuel x) node0))
  | 0, h, x, h1, h2 => by simp at h2; omega
  | fuel + 1, h, x, h1, h2 => by
    unfold walk insertDepth
    split_ifs with hx
    · rfl
    · have := walk_insertNode H br node0 fuel (h + 1) (x / 2) (by omega)
        (by rw [Nat.pow_succ] at h2; omega)
      rw [show hashPair H (br h) (insertNode H br h node0) = insertNode H br (h + 1) node0 from rfl,
        this, show h + 1 + insertDepth fuel (x / 2) = h + (insertDepth fuel (x / 2) + 1) by omega]

end Walk

/-! ## Storage slots and key sets -/

theorem solBranchSlot_toNat {h : Nat} (hh : h < 32) : (solBranchSlot h).toNat = h :=
  B256.toNat_toB256_of_lt (by omega)

theorem solBranchSlot_inj {i j : Nat} (hi : i < 32) (hj : j < 32)
    (h : solBranchSlot i = solBranchSlot j) : i = j := by
  have := congrArg B256.toNat h
  rwa [solBranchSlot_toNat hi, solBranchSlot_toNat hj] at this

theorem solBranchSlot_ne_count {h : Nat} (hh : h < 32) : solBranchSlot h ≠ solCountSlot := by
  intro e
  have := congrArg B256.toNat e
  rw [solBranchSlot_toNat hh] at this
  have h32 : (solCountSlot).toNat = 32 := by decide
  omega

theorem mem_sloadAccessedStorageKeys {t : Adr} {keys : KeySet} {k : B256} {y : Adr × B256} :
    y ∈ sloadAccessedStorageKeys t keys k ↔ y ∈ keys ∨ y = (t, k) := by
  unfold sloadAccessedStorageKeys
  split_ifs with hk
  · constructor
    · exact fun h => .inl h
    · rintro (h | rfl)
      · exact h
      · exact hk
  · rw [Std.HashSet.mem_insert]
    constructor
    · rintro (h | h)
      · exact .inr (by simp at h; exact h.symm)
      · exact .inl h
    · rintro (h | rfl)
      · exact .inr h
      · exact .inl (by simp)

/-! ## The base through the insertion loop -/

/-- What the insertion loop keeps of the base `b₀` it started from, at height `h`: everything
but the key set, which has gained the branch slots below `h`. -/
structure LoopBase (tgt : Adr) (b₀ b : Devm) (h : Nat) : Prop where
  stor : ∀ a, Devm.getStor b a = Devm.getStor b₀ a
  code : ∀ a, b.getCode a = b₀.getCode a
  addrs : b.accessedAddresses = b₀.accessedAddresses
  logs : b.logs = b₀.logs
  output : b.output = b₀.output
  error : b.error = b₀.error
  keys : ∀ y, y ∈ b.accessedStorageKeys ↔
    y ∈ b₀.accessedStorageKeys ∨ ∃ j < h, y = (tgt, solBranchSlot j)

theorem ShaReady.of_eq {sevm : Sevm} {b b' : Devm} (h : ShaReady sevm b)
    (hc : ∀ a, b'.getCode a = b.getCode a) (ha : b'.accessedAddresses = b.accessedAddresses) :
    ShaReady sevm b' :=
  ⟨by rw [hc]; exact h.nodeleg, by rw [ha]; exact h.warm, h.pre, h.fork, h.depth⟩

theorem LoopBase.step {sevm : Sevm} {b₀ b b' : Devm} {h : Nat}
    (hL : LoopBase sevm.currentTarget b₀ b h)
    (hK : Keep (afterSload sevm b (solBranchSlot h)) b') :
    LoopBase sevm.currentTarget b₀ b' (h + 1) where
  stor a := by rw [hK.stor, afterSload_getStor, hL.stor]
  code a := by rw [hK.code, afterSload_getCode, hL.code]
  addrs := by rw [hK.addrs, afterSload_accessedAddresses, hL.addrs]
  logs := by rw [hK.logs, afterSload_logs, hL.logs]
  output := by rw [hK.output, afterSload_output, hL.output]
  error := by rw [hK.error, afterSload_error, hL.error]
  keys y := by
    rw [hK.keys, afterSload_accessedStorageKeys, mem_sloadAccessedStorageKeys, hL.keys]
    constructor
    · rintro ((h0 | ⟨j, hj, rfl⟩) | rfl)
      · exact .inl h0
      · exact .inr ⟨j, by omega, rfl⟩
      · exact .inr ⟨h, by omega, rfl⟩
    · rintro (h0 | ⟨j, hj, rfl⟩)
      · exact .inl (.inl h0)
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact .inl (.inr ⟨j, hj, rfl⟩)
        · exact .inr rfl

/-- `Keep` without the key set. -/
structure WorldEq (b b' : Devm) : Prop where
  stor : ∀ a, Devm.getStor b' a = Devm.getStor b a
  code : ∀ a, b'.getCode a = b.getCode a
  addrs : b'.accessedAddresses = b.accessedAddresses
  logs : b'.logs = b.logs
  output : b'.output = b.output
  error : b'.error = b.error

theorem getStor_afterSstore (sevm : Sevm) (b : Devm) (k v : B256) (a : Adr) :
    Devm.getStor (afterSstore sevm b k v) a =
      if a = sevm.currentTarget then (Devm.getStor b sevm.currentTarget).set k v
      else Devm.getStor b a := by
  split_ifs with h
  · subst h; exact afterSstore_getStor_self _ _ _ _
  · exact afterSstore_getStor_ne _ _ _ _ _ (Ne.symm h)

theorem LoopBase.mem_self {tgt : Adr} {b₀ b : Devm} {h : Nat} (hL : LoopBase tgt b₀ b h)
    (hh : h < 32) :
    (tgt, solBranchSlot h) ∈ b.accessedStorageKeys ↔ (tgt, solBranchSlot h) ∈ b₀.accessedStorageKeys := by
  rw [hL.keys]
  constructor
  · rintro (h0 | ⟨j, hj, hj'⟩)
    · exact h0
    · have := solBranchSlot_inj hh (by omega) (Prod.mk.inj hj').2
      omega
  · exact .inl

theorem toB256_div_two {y : Nat} (hy : y < 2 ^ 256) : Nat.toB256 y / 2 = Nat.toB256 (y / 2) := by
  apply B256.toNat_inj
  rw [B256.toNat_div (by decide), B256.toNat_toB256_of_lt hy,
    B256.toNat_toB256_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) hy)]
  rfl

/-! ## The insertion loop -/

/-- **The insertion loop from height `h`**, `m` dead iterations before the storing one at
`n = h + m`: the dead segment `m` times (by induction), then the storing segment. -/
theorem insert_loop {sevm : Sevm} {b₀ : Devm} {G : Nat} {x n : Nat} {node0 : B256}
    {br : Nat → B256} {keys0 : KeySet} {stor1 : Stor}
    {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ y₅ y₆ y₇ d : B256} {rest : List B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hsha : ShaReady sevm b₀) (hrest : rest.length ≤ 4)
    (hx : x < 2 ^ 256) (hn : n < 32) (hdead : ∀ h < n, (x / 2 ^ h) % 2 = 0)
    (hlive : (x / 2 ^ n) % 2 = 1)
    (hstor1 : Devm.getStor b₀ sevm.currentTarget = stor1)
    (hbr : ∀ h < 32, stor1.get (solBranchSlot h) = br h)
    (hkeys : ∀ j < 32, ((sevm.currentTarget, solBranchSlot j) ∈ b₀.accessedStorageKeys ↔
      (sevm.currentTarget, solBranchSlot j) ∈ keys0))
    (hsentry : gCallStipend < G + 51 +
      liveStoreCost sevm keys0 stor1 n (insertNode Bytes.sha256 br n node0)) :
    ∀ m h b M, h + m = n → LoopBase sevm.currentTarget b₀ b h →
      BodyMem M (1024 + 96 * h) (Nat.toB256 (928 + 96 * h)) [] →
      G + (deadRun sevm.currentTarget keys0 h m +
        (143 + liveStoreCost sevm keys0 stor1 n (insertNode Bytes.sha256 br n node0))) < 2 ^ 256 →
      ∃ bf Mf, WorldEq
          (afterSstore sevm b₀ (solBranchSlot n) (insertNode Bytes.sha256 br n node0)) bf ∧
        SFunc.RunExact prog sevm
          (St b (Nat.toB256 h :: Nat.toB256 (x / 2 ^ h) :: insertNode Bytes.sha256 br h node0 ::
            x₁ :: x₂ :: x₃ :: x₄ :: y₁ :: y₂ :: y₃ :: y₄ :: y₅ :: y₆ :: y₇ :: d :: rest) M
            (G + (deadRun sevm.currentTarget keys0 h m +
              (143 + liveStoreCost sevm keys0 stor1 n (insertNode Bytes.sha256 br n node0)))))
          t_0f6e_c23 (.returned (St bf rest Mf G)) := by
  intro m
  induction m with
  | zero =>
    intro h b M hhm hL hM hG
    simp only [Nat.add_zero] at hhm
    subst hhm
    set nd := insertNode Bytes.sha256 br h node0
    have hmem : (sevm.currentTarget, solBranchSlot h) ∈ b.accessedStorageKeys ↔
        (sevm.currentTarget, solBranchSlot h) ∈ keys0 := by
      rw [hL.keys, ← hkeys h hn]
      constructor
      · rintro (h0 | ⟨j, hj, hj'⟩)
        · exact h0
        · have := solBranchSlot_inj hn (by omega) (Prod.mk.inj hj').2
          omega
      · exact .inl
    have hval : b.getStorVal sevm.currentTarget (solBranchSlot h) = stor1.get (solBranchSlot h) := by
      show (Devm.getStor b sevm.currentTarget).get _ = _
      rw [hL.stor, hstor1]
    have hcost : sstoreCost sevm b (solBranchSlot h) nd = liveStoreCost sevm keys0 stor1 h nd := by
      unfold sstoreCost liveStoreCost
      rw [hval]
      congr 1
      by_cases hk : (sevm.currentTarget, solBranchSlot h) ∈ keys0
      · rw [if_pos (hmem.mpr hk), if_pos hk]
      · rw [if_neg (fun h' => hk (hmem.mp h')), if_neg hk]
    refine ⟨afterSstore sevm b (solBranchSlot h) nd, M, ?_, ?_⟩
    · refine ⟨fun a => ?_, fun a => ?_, ?_, ?_, ?_, ?_⟩
      · rw [getStor_afterSstore, getStor_afterSstore, hL.stor, hL.stor]
      · rw [afterSstore_getCode, afterSstore_getCode, hL.code]
      · rw [afterSstore_accessedAddresses, afterSstore_accessedAddresses, hL.addrs]
      · rw [afterSstore_logs, afterSstore_logs, hL.logs]
      · rw [afterSstore_output, afterSstore_output, hL.output]
      · rw [afterSstore_error, afterSstore_error, hL.error]
    rw [show deadRun sevm.currentTarget keys0 h 0 = 0 from rfl, Nat.zero_add, ← hcost]
    exact body_insertLive hfork hstatic hn
      (by rw [B256.toNat_toB256_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) hx)]; exact hlive)
      (by omega) (by rw [hcost]; exact hsentry)
  | succ m ih =>
    intro h b M hhm hL hM hG
    have hh : h < n := by omega
    have hh32 : h < 32 := by omega
    set L := 143 + liveStoreCost sevm keys0 stor1 n (insertNode Bytes.sha256 br n node0)
    have hcostS : sloadCost sevm b (solBranchSlot h) =
        sloadCostOfKeys sevm.currentTarget keys0 (solBranchSlot h) := by
      unfold sloadCost sloadCostOfKeys
      have hm := (hL.mem_self hh32).trans (hkeys h hh32)
      by_cases hk : (sevm.currentTarget, solBranchSlot h) ∈ keys0
      · rw [if_pos (hm.mpr hk), if_pos hk]
      · rw [if_neg (fun h' => hk (hm.mp h')), if_neg hk]
    have hrun0 : deadRun sevm.currentTarget keys0 h (m + 1) =
        deadGas h + sloadCostOfKeys sevm.currentTarget keys0 (solBranchSlot h) +
          deadRun sevm.currentTarget keys0 (h + 1) m := rfl
    have hxh : x / 2 ^ h < 2 ^ 256 := lt_of_le_of_lt (Nat.div_le_self _ _) hx
    obtain ⟨b', M', hK, hM', hrun⟩ := body_insertDead (sevm := sevm) (b := b)
      (sz := Nat.toB256 (x / 2 ^ h)) (nd := insertNode Bytes.sha256 br h node0)
      (R := [x₁, x₂, x₃, x₄, y₁, y₂, y₃, y₄, y₅, y₆, y₇, d] ++ rest) (h := h)
      (G := G + (deadRun sevm.currentTarget keys0 (h + 1) m + L))
      (hsha.of_eq hL.code hL.addrs) hh32
      (by rw [B256.toNat_toB256_of_lt hxh]; exact hdead h hh) (by simp; omega)
      (by rw [hcostS]; rw [hrun0] at hG; omega) hM
    have hM'' : BodyMem M' (1024 + 96 * (h + 1)) (Nat.toB256 (928 + 96 * (h + 1))) [] := by
      rw [show 1024 + 96 * (h + 1) = 1120 + 96 * h by omega,
        show 928 + 96 * (h + 1) = 1024 + 96 * h by omega]
      exact hM'
    obtain ⟨bf, Mf, hW, hrun'⟩ := ih (h + 1) b' M' (by omega) (hL.step hK) hM''
      (by rw [hrun0] at hG; omega)
    refine ⟨bf, Mf, hW, ?_⟩
    have hgas : G + (deadRun sevm.currentTarget keys0 h (m + 1) + L) =
        G + (deadRun sevm.currentTarget keys0 (h + 1) m + L) +
          (deadGas h + sloadCost sevm b (solBranchSlot h)) := by
      rw [hrun0, hcostS]; omega
    rw [hgas]
    apply hrun
    have hsz : Nat.toB256 (x / 2 ^ h) / 2 = Nat.toB256 (x / 2 ^ (h + 1)) := by
      rw [toB256_div_two hxh, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
    have hnd : BeaconDeposit.hashPair Bytes.sha256
        (b.getStorVal sevm.currentTarget (solBranchSlot h)) (insertNode Bytes.sha256 br h node0) =
        insertNode Bytes.sha256 br (h + 1) node0 := by
      show _ = BeaconDeposit.hashPair Bytes.sha256 (br h) _
      congr 1
      show (Devm.getStor b sevm.currentTarget).get _ = _
      rw [hL.stor, hstor1, hbr h hh32]
    rw [hsz, hnd]
    exact hrun'

/-! ## What a successful model deposit says -/

theorem deposit_ok_facts {H : Bytes → B256} {s s' : BeaconDeposit.Acc}
    {pk wc sig : Bytes} {root : B256} {v : Nat} {ev : BeaconDeposit.DepositEvent}
    (hOk : BeaconDeposit.deposit H s pk wc sig root v = .ok (s', ev)) :
    pk.length = 48 ∧ wc.length = 32 ∧ sig.length = 96 ∧ BeaconDeposit.oneEther ≤ v ∧
      v % BeaconDeposit.oneGwei = 0 ∧ v / BeaconDeposit.oneGwei ≤ 2 ^ 64 - 1 ∧
      BeaconDeposit.depositDataNode H pk wc sig (BeaconDeposit.le64 (v / BeaconDeposit.oneGwei)) =
        root ∧
      s.count < 2 ^ 32 - 1 ∧
      ∃ br, BeaconDeposit.walk H s.branch 32 0 (s.count + 1) root = some br ∧
        s' = ⟨br, s.count + 1⟩ ∧
        ev = ⟨pk, wc, BeaconDeposit.le64 (v / BeaconDeposit.oneGwei), sig,
          BeaconDeposit.le64 s.count⟩ := by
  unfold BeaconDeposit.deposit at hOk
  split_ifs at hOk with h1 h2 h3 h4 h5 h6 h7
  all_goals first | (simp at hOk; done) | skip
  by_cases hn : BeaconDeposit.depositDataNode H pk wc sig
      (BeaconDeposit.le64 (v / BeaconDeposit.oneGwei)) = root
  · rw [if_neg (not_not.mpr hn), hn] at hOk
    split at hOk
    · rename_i br hw
      cases hOk
      exact ⟨not_not.mp h1, not_not.mp h2, not_not.mp h3, by omega, not_not.mp h5, by omega, hn,
        h7, br, hw, rfl, rfl⟩
    · cases hOk
  · rw [if_pos hn] at hOk
    cases hOk
  all_goals (simp only at hOk; split_ifs at hOk <;> cases hOk)

/-! ## Small facts the composition uses -/

theorem t_0f6e_c20_eq : t_0f6e_c20 = t_0f6e_c23 := rfl

theorem liveStoreCost_congr {sevm : Sevm} {keys : KeySet} {s t : Stor} {n : Nat} {nd : B256}
    (h : s.get (solBranchSlot n) = t.get (solBranchSlot n)) :
    liveStoreCost sevm keys s n nd = liveStoreCost sevm keys t n nd := by
  unfold liveStoreCost; rw [h]

theorem argBytes_eq {sevm : Sevm} {i k : Nat} (h : (argBytes sevm i).length = k) :
    argBytes sevm i = sevm.data.sliceD (argPtr sevm i).toNat k 0 ∧ argLen sevm i = Nat.toB256 k := by
  have hl : (argLen sevm i).toNat = k := by
    rw [← h, argBytes, List.length_sliceD]
  refine ⟨by rw [argBytes, hl], ?_⟩
  apply B256.toNat_inj
  rw [hl, B256.toNat_toB256_of_lt]
  have := B256.toNat_lt (argLen sevm i)
  omega

/-! ## The body -/

/-- **The deployed `deposit` body on the success path, gas-exact.**  For calldata the deployed
decoder accepts and a model deposit that succeeds on the arguments it reads (`argBytes`,
`argRoot`, `CALLVALUE`) from the storage's `solAcc`, the internal function at entry 7 runs from
the decoder's argument stack over `mem0` and returns to the decoder's tag with exactly `g + 1`
gas left, having spent `bodyGas`.  Its storage is `bodyStor` (count incremented, one branch slot
written), whose `solAcc` is the model's new accumulator; one log, the model event's, is appended;
every other account's storage, all code, the accessed addresses, output and error are
unchanged.  Premises: the SHA-256 precompile's (`ShaReady`), a non-static frame, the two
`SSTORE` sentries, and the gas below `2^256`. -/
theorem deposit_body_runExact (sevm : Sevm) (b : Devm) (sel : B256) (g : Nat)
    (s' : BeaconDeposit.Acc) (ev : BeaconDeposit.DepositEvent)
    (hdec : DepositDecodable sevm) (hcd : sevm.data.length < 2 ^ 256)
    (hOk : BeaconDeposit.deposit Bytes.sha256 (solAcc (Devm.getStor b sevm.currentTarget))
      (argBytes sevm 0) (argBytes sevm 1) (argBytes sevm 2) (argRoot sevm) sevm.value.toNat =
        .ok (s', ev))
    (hsha : ShaReady sevm b) (hstatic : sevm.isStatic = false)
    (hsentryLive : gCallStipend < g + 52 + bodyLiveCost sevm b)
    (hsentryCount : gCallStipend < g + 4 + bodyInsertGas sevm b + countStoreCost sevm (bodyCount sevm b))
    (hbound : g + 1 + bodyGas sevm b < 2 ^ 256) :
    ∃ b' M', SFunc.RunExact prog sevm
        (St b (depositArgStack sevm [sel]) mem0 (g + 1 + bodyGas sevm b)) t_0304_c7
        (.returned (St b' [sel] M' (g + 1))) ∧
      Devm.getStor b' sevm.currentTarget = bodyStor sevm b ∧
      solAcc (Devm.getStor b' sevm.currentTarget) = s' ∧
      (∀ a, a ≠ sevm.currentTarget → Devm.getStor b' a = Devm.getStor b a) ∧
      b'.logs = b.logs ++ [BeaconDeposit.depositEventLog sevm.currentTarget ev] ∧
      (∀ a, b'.getCode a = b.getCode a) ∧ b'.accessedAddresses = b.accessedAddresses ∧
      b'.output = b.output ∧ b'.error = b.error := by
  sorry

end Blanc.Lift.BeaconDeposit
