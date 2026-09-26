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

/-! ## The insertion loop -/

/-- **The insertion loop from height `h`**, `m` dead iterations before the storing one at
`n = h + m`: the dead segment `m` times (by induction), then the storing segment. -/
theorem insert_loop {sevm : Sevm} {b₀ : Devm} {G : Nat} {x n : Nat} {node0 : B256}
    {br : Nat → B256} {keys0 : KeySet} {stor1 : Stor}
    {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ y₅ y₆ y₇ d : B256} {rest : List B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hsha : ShaReady sevm b₀) (hdepth : sevm.depth ≠ 0) (hrest : rest.length ≤ 4)
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
      ∃ bf Mf, BaseRel
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
      · rw [ite_eq_left (hmem.mpr hk), ite_eq_left hk]
      · rw [ite_eq_right (fun h' => hk (hmem.mp h')), ite_eq_right hk]
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
      · rw [ite_eq_left (hm.mpr hk), ite_eq_left hk]
      · rw [ite_eq_right (fun h' => hk (hm.mp h')), ite_eq_right hk]
    have hrun0 : deadRun sevm.currentTarget keys0 h (m + 1) =
        deadGas h + sloadCostOfKeys sevm.currentTarget keys0 (solBranchSlot h) +
          deadRun sevm.currentTarget keys0 (h + 1) m := rfl
    have hxh : x / 2 ^ h < 2 ^ 256 := lt_of_le_of_lt (Nat.div_le_self _ _) hx
    obtain ⟨b', M', hK, hM', hrun⟩ := body_insertDead (sevm := sevm) (b := b)
      (sz := Nat.toB256 (x / 2 ^ h)) (nd := insertNode Bytes.sha256 br h node0)
      (R := [x₁, x₂, x₃, x₄, y₁, y₂, y₃, y₄, y₅, y₆, y₇, d] ++ rest) (h := h)
      (G := G + (deadRun sevm.currentTarget keys0 (h + 1) m + L))
      (hsha.of_eq hL.code hL.addrs) hdepth hh32
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
  by_cases hn : BeaconDeposit.depositDataNode H pk wc sig
      (BeaconDeposit.le64 (v / BeaconDeposit.oneGwei)) = root
  · rw [ite_eq_right (not_not.mpr hn), hn] at hOk
    split at hOk
    · rename_i br hw
      cases hOk
      exact ⟨not_not.mp h1, not_not.mp h2, not_not.mp h3, by omega, not_not.mp h5, by omega, hn,
        h7, br, hw, rfl, rfl⟩
    · cases hOk
  · rw [ite_eq_left hn] at hOk
    cases hOk
  all_goals (simp only at hOk; split_ifs at hOk)

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

theorem argPtr_toNat {sevm : Sevm} {i : Nat} (h : TailDecodable sevm i) :
    (argPtr sevm i).toNat = 36 + (argOff sevm i).toNat := by
  have h1 := h.1
  unfold argPtr
  rw [B256.toNat_add, B256.toNat_add, Nat.lo_eq_of_lt (a := (4 : B256).toNat + _) (by
      rw [show (4 : B256).toNat = 4 from rfl]; omega),
    Nat.lo_eq_of_lt (by rw [show (4 : B256).toNat = 4 from rfl, show (32 : B256).toNat = 32 from rfl]; omega),
    show (4 : B256).toNat = 4 from rfl, show (32 : B256).toNat = 32 from rfl]
  omega

theorem acc_mk_eq {f g : Nat → B256} {c d : Nat} (h1 : f = g) (h2 : c = d) :
    (⟨f, c⟩ : BeaconDeposit.Acc) = ⟨g, d⟩ := by
  subst h1 h2; rfl

/-! ## The body -/

/-- **The deployed `deposit` body on the success path, gas-exact.**  For calldata the deployed
decoder accepts and a model deposit that succeeds on the arguments it reads (`argBytes`,
`argRoot`, `CALLVALUE`) from the storage's `solAcc`, the internal function at entry 7 runs from
the decoder's argument stack over `mem0` and returns to the decoder's tag with exactly `g + 1`
gas left, having spent `bodyGas`.  Its storage is `bodyStor` (count incremented, one branch slot
written), whose `solAcc` is the model's new accumulator; one log, the model event's, is appended;
every other account's storage, all code, the accessed addresses, output and error are
unchanged.  Premises: the SHA-256 precompile's (`ShaReady`), a frame not at the maximal call
depth (at depth `0` the `STATICCALL` fails), a non-static frame, the two
`SSTORE` sentries, and the gas below `2^256`. -/
theorem deposit_body_runExact (sevm : Sevm) (b : Devm) (sel : B256) (g : Nat)
    (s' : BeaconDeposit.Acc) (ev : BeaconDeposit.DepositEvent)
    (hdec : DepositDecodable sevm) (hcd : sevm.data.length < 2 ^ 256)
    (hOk : BeaconDeposit.deposit Bytes.sha256 (solAcc (Devm.getStor b sevm.currentTarget))
      (argBytes sevm 0) (argBytes sevm 1) (argBytes sevm 2) (argRoot sevm) sevm.value.toNat =
        .ok (s', ev))
    (hsha : ShaReady sevm b) (hdepth : sevm.depth ≠ 0) (hstatic : sevm.isStatic = false)
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
  -- the model's success
  obtain ⟨hpk, hwc, hsg, hv1, hv2, hv3, hnode, hcap, br', hwalk, rfl, rfl⟩ := deposit_ok_facts hOk
  clear hOk
  set tgt := sevm.currentTarget with htgt
  set stor := Devm.getStor b tgt with hstor
  set w := bodyCount sevm b with hw
  have hwst : stor.get solCountSlot = w := rfl
  have hcnt : (solAcc stor).count = w.toNat := rfl
  obtain ⟨hpkB, hL0⟩ := argBytes_eq hpk
  obtain ⟨hwcB, hL1⟩ := argBytes_eq hwc
  obtain ⟨hsgB, hL2⟩ := argBytes_eq hsg
  set pP := argPtr sevm 0
  set wP := argPtr sevm 1
  set sP := argPtr sevm 2
  set rt := argRoot sevm
  have hstk : depositArgStack sevm [sel] = [rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] := by
    rw [depositArgStack, hL0, hL1, hL2]; rfl
  -- the value
  set v := sevm.value.toNat
  have hamt : (gweiAmount sevm).toNat = v / 10 ^ 9 := by
    rw [gweiAmount, B256.toNat_div (by decide)]; rfl
  have hv1' : 10 ^ 18 ≤ v := hv1
  have hv2' : v % 10 ^ 9 = 0 := hv2
  have hv3' : v / 10 ^ 9 < 2 ^ 64 := by
    have : v / 10 ^ 9 ≤ 2 ^ 64 - 1 := hv3
    omega
  set a := gweiAmount sevm
  -- gas accounting
  set L := bodyInsertGas sevm b
  set cs := countStoreCost sevm w
  set G6 := g + 1 + L
  set G5 := G6 + (281 + cs)
  set G4 := G5 + 2553
  set G3 := G4 + 2526
  set G2 := G3 + 6205
  set G1 := G2 + 1104
  have hstart : G1 + (1882 + sloadCost sevm b solCountSlot) = g + 1 + bodyGas sevm b := by
    show _ = g + 1 + (14551 + sloadCostOfKeys sevm.currentTarget b.accessedStorageKeys
      solCountSlot + cs + L)
    rw [sloadCostOfKeys_eq_sloadCost]
    simp only [G1, G2, G3, G4, G5, G6]
    omega
  -- segment 1
  obtain ⟨b1, M1, hK1, hM1, r1⟩ := body_guards (b := b) (sel := sel) (rt := rt) (sP := sP)
    (wP := wP) (pP := pP) (G := G1) hcd hsha.fork hv1' hv2' hv3'
  -- segment 2
  obtain ⟨b2, M2, hK2, hM2, r2⟩ := body_event (sevm := sevm) (b := b1) (sel := sel) (rt := rt)
    (sP := sP) (wP := wP) (pP := pP) (a := a) (c := w) (G := G2) hM1
  -- segment 3
  have hc1 : ∀ x, b1.getCode x = b.getCode x := fun x => by rw [hK1.code, afterSload_getCode]
  have ha1 : b1.accessedAddresses = b.accessedAddresses := by
    rw [hK1.addrs, afterSload_accessedAddresses]
  have hsha2 : ShaReady sevm b2 :=
    hsha.of_eq (fun x => by rw [hK2.code, hc1]) (by rw [hK2.addrs, ha1])
  set ev := bodyEvent sevm pP wP sP a w
  have hlen : (BeaconDeposit.abiDepositEvent ev).length = 576 := by
    simp [ev, bodyEvent, BeaconDeposit.abiDepositEvent, abiBytesTail, List.length_sliceD,
      BeaconDeposit.le64, ceil32, B256.length_toBytes]
  obtain ⟨b3, M3, hK3, hM3, r3⟩ := body_pubkeyRoot (sevm := sevm) (b := b2) (sel := sel) (rt := rt)
    (sP := sP) (wP := wP) (pP := pP) (a := a) (G := G3) hsha2 hdepth hstatic hlen (by omega) hM2
  -- world facts so far
  have hc3 : ∀ x, b3.getCode x = b.getCode x := fun x => by
    rw [hK3.code]; show b2.getCode x = _; rw [hK2.code, hc1]
  have ha3 : b3.accessedAddresses = b.accessedAddresses := by
    rw [hK3.addrs]; show b2.accessedAddresses = _; rw [hK2.addrs, ha1]
  -- segment 4
  have hsP : sP.toNat + 96 < 2 ^ 256 := by
    have := argPtr_toNat hdec.2.2.2
    have := hdec.2.2.2.1
    show (argPtr sevm 2).toNat + 96 < _
    omega
  set pkR := BeaconDeposit.pubkeyRoot Bytes.sha256 (sevm.data.sliceD pP.toNat 48 0)
  obtain ⟨b4, M4, hK4, hM4, r4⟩ := body_signatureRoot (sevm := sevm) (b := b3) (sel := sel)
    (rt := rt) (sP := sP) (wP := wP) (pP := pP) (a := a) (pkR := pkR) (G := G4)
    (hsha.of_eq hc3 ha3) hdepth hsP (by omega) hM3
  -- segment 5
  set sR := BeaconDeposit.signatureRoot Bytes.sha256 (sevm.data.sliceD sP.toNat 96 0)
  obtain ⟨b5, M5, hK5, hM5, r5⟩ := body_dataNode (sevm := sevm) (b := b4) (sel := sel) (rt := rt)
    (sP := sP) (wP := wP) (pP := pP) (a := a) (pkR := pkR) (sR := sR) (G := G5)
    (hsha.of_eq (fun x => by rw [hK4.code, hc3]) (by rw [hK4.addrs, ha3])) hdepth (by omega) hM4
  -- segment 6
  have hkeys5 : b5.accessedStorageKeys =
      sloadAccessedStorageKeys tgt b.accessedStorageKeys solCountSlot := by
    rw [hK5.keys, hK4.keys, hK3.keys]
    show b2.accessedStorageKeys = _
    rw [hK2.keys, hK1.keys, afterSload_accessedStorageKeys]
  have hstor5 : ∀ x, Devm.getStor b5 x = Devm.getStor b x := fun x => by
    rw [hK5.stor, hK4.stor, hK3.stor]
    show Devm.getStor b2 x = _
    rw [hK2.stor, hK1.stor, afterSload_getStor]
  have hw5 : b5.getStorVal sevm.currentTarget solCountSlot = w := by
    show (Devm.getStor b5 _).get _ = _
    rw [hstor5]; rfl
  have hwarm5 : (⟨sevm.currentTarget, solCountSlot⟩ : Adr × B256) ∈ b5.accessedStorageKeys := by
    rw [hkeys5, mem_sloadAccessedStorageKeys]; exact .inr rfl
  have hcs5 : sstoreCost sevm b5 solCountSlot (1 + w) = cs := by
    unfold sstoreCost; rw [ite_eq_left hwarm5, hw5, Nat.zero_add]; rfl
  have hroot : BeaconDeposit.hashPair Bytes.sha256
      (Bytes.sha256 (pkR.toBytes ++ sevm.data.sliceD wP.toNat 32 0))
      (Bytes.sha256 (BeaconDeposit.le64 a.toNat ++ BeaconDeposit.zeros 24 ++ sR.toBytes)) = rt := by
    rw [← hnode, hpkB, hwcB, hsgB, hamt]; rfl
  obtain ⟨b6, M6, hK6, hM6, r6⟩ := body_countBump (sevm := sevm) (b := b5) (sel := sel) (rt := rt)
    (sP := sP) (wP := wP) (pP := pP) (a := a) (pkR := pkR) (sR := sR) (G := G6) hsha.fork hstatic
    hwarm5 hroot (by rw [hw5]; omega) (by rw [hw5, hcs5]; omega) hM5
  rw [hw5] at hK6 r6
  rw [hcs5] at r6
  -- the insertion loop
  set x := w.toNat + 1 with hx
  have hx32 : x < 2 ^ 32 := by
    have : w.toNat < 2 ^ 32 - 1 := hcnt ▸ hcap
    omega
  set n := bodyDepth sevm b
  have hn : n < 32 := insertDepth_lt 32 x (by omega) hx32
  set br := (solAcc stor).branch
  set nd := insertNode Bytes.sha256 br n rt
  set stor1 := stor.set solCountSlot (1 + w)
  have hb6stor : Devm.getStor b6 sevm.currentTarget = stor1 := by
    rw [hK6.stor, afterSstore_getStor_self, hstor5]
  have hbr : ∀ h < 32, stor1.get (solBranchSlot h) = br h := fun h hh => by
    rw [Stor.get_set_ne _ (Ne.symm (solBranchSlot_ne_count hh))]
    simp [br, solAcc, hh, stor]
  have hkeys6 : ∀ j < 32, ((sevm.currentTarget, solBranchSlot j) ∈ b6.accessedStorageKeys ↔
      (sevm.currentTarget, solBranchSlot j) ∈ b.accessedStorageKeys) := fun j hj => by
    rw [hK6.keys, afterSstore_accessedStorageKeys, mem_sloadAccessedStorageKeys, hkeys5,
      mem_sloadAccessedStorageKeys]
    have hne : (sevm.currentTarget, solBranchSlot j) ≠ (tgt, solCountSlot) :=
      fun e => solBranchSlot_ne_count hj (Prod.mk.inj e).2
    constructor
    · rintro ((h | h) | h)
      · exact h
      · exact absurd h hne
      · exact absurd h hne
    · exact fun h => .inl (.inl h)
  have hlc : liveStoreCost sevm b.accessedStorageKeys stor1 n nd = bodyLiveCost sevm b :=
    liveStoreCost_congr (Stor.get_set_ne _ (Ne.symm (solBranchSlot_ne_count hn)) _)
  have hc6 : ∀ y, b6.getCode y = b.getCode y := fun y => by
    rw [hK6.code, afterSstore_getCode, hK5.code, hK4.code, hc3]
  have ha6 : b6.accessedAddresses = b.accessedAddresses := by
    rw [hK6.addrs, afterSstore_accessedAddresses, hK5.addrs, hK4.addrs, ha3]
  have hM6' : BodyMem M6 (1024 + 96 * 0) (Nat.toB256 (928 + 96 * 0)) [] := hM6
  have hL0' : LoopBase sevm.currentTarget b6 b6 0 :=
    ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl, fun _ =>
      ⟨.inl, fun h => h.elim id (fun ⟨_, hj, _⟩ => absurd hj (Nat.not_lt_zero _))⟩⟩
  obtain ⟨bf, Mf, hW, rL⟩ := insert_loop (sevm := sevm) (b₀ := b6) (G := g + 1) (x := x) (n := n)
    (node0 := rt) (br := br) (keys0 := b.accessedStorageKeys) (stor1 := stor1)
    (x₁ := sR) (x₂ := pkR) (x₃ := 128) (x₄ := a) (y₁ := rt) (y₂ := 96) (y₃ := sP) (y₄ := 32)
    (y₅ := wP) (y₆ := 48) (y₇ := pP) (d := 440) (rest := [sel]) hsha.fork hstatic
    (hsha.of_eq hc6 ha6) hdepth (by simp) (by omega) hn (fun h hh => insertDepth_dead 32 x h hh)
    (insertDepth_live 32 x (by omega) hx32) hb6stor hbr hkeys6 (by rw [hlc]; omega)
    n 0 b6 M6 (by omega) hL0' hM6' (by rw [hlc]; show g + 1 + L < 2 ^ 256; omega)
  rw [hlc] at rL
  have e1 : (1 + w) = Nat.toB256 (x / 2 ^ 0) := by
    rw [Nat.pow_zero, Nat.div_one]
    apply B256.toNat_inj
    rw [B256.toNat_toB256_of_lt (by omega), B256.toNat_add, show (1 : B256).toNat = 1 from rfl,
      Nat.lo_eq_of_lt (by omega)]
    omega
  have hrun6 : SFunc.RunExact prog sevm
      (St b6 [0, 1 + w,
        BeaconDeposit.hashPair Bytes.sha256
          (Bytes.sha256 (pkR.toBytes ++ sevm.data.sliceD wP.toNat 32 0))
          (Bytes.sha256 (BeaconDeposit.le64 a.toNat ++ BeaconDeposit.zeros 24 ++ sR.toBytes)),
        sR, pkR, 128, a, rt, 96, sP, 32, wP, 48, pP, 440, sel] M6 G6) t_0f6e_c20
      (.returned (St bf [sel] Mf (g + 1))) := by
    rw [t_0f6e_c20_eq, hroot, e1]
    exact rL
  refine ⟨bf, Mf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hstk, ← hstart]
    exact r1 _ (r2 _ (r3 _ (r4 _ (r5 _ (r6 _ hrun6)))))
  · rw [hW.stor, afterSstore_getStor_self, hb6stor]; rfl
  · -- the model's accumulator
    have hw' := walk_insertNode Bytes.sha256 br rt 32 0 x (by omega) hx32
    rw [Nat.zero_add] at hw'
    have hbr' : br' = BeaconDeposit.setSlot br n nd := by
      have : BeaconDeposit.walk Bytes.sha256 br 32 0 x rt = some br' := by rw [hx, ← hcnt]; exact hwalk
      rw [show insertNode Bytes.sha256 br 0 rt = rt from rfl] at hw'
      rw [hw'] at this
      exact (Option.some.inj this).symm
    rw [hW.stor, afterSstore_getStor_self, hb6stor, hbr', hcnt]
    refine acc_mk_eq ?_ ?_
    · funext h
      by_cases hh : h < 32
      · rw [ite_eq_left hh]
        unfold BeaconDeposit.setSlot
        by_cases hhn : h = n
        · subst hhn; rw [ite_eq_left rfl, Stor.get_set_self]
        · rw [ite_eq_right hhn, Stor.get_set_ne _ (fun e => hhn (solBranchSlot_inj hh hn e.symm)),
            hbr h hh]
      · rw [ite_eq_right hh]
        unfold BeaconDeposit.setSlot
        rw [ite_eq_right (by omega)]
        simp [br, solAcc, hh]
    · rw [Stor.get_set_ne _ (solBranchSlot_ne_count hn), Stor.get_set_self]
      have := congrArg B256.toNat e1
      rw [Nat.pow_zero, Nat.div_one, B256.toNat_toB256_of_lt (by omega)] at this
      exact this
  · intro y hy
    rw [hW.stor, getStor_afterSstore, ite_eq_right hy, hK6.stor, getStor_afterSstore, ite_eq_right hy, hstor5]
  · rw [hW.logs, afterSstore_logs, hK6.logs, afterSstore_logs, hK5.logs, hK4.logs, hK3.logs]
    show b2.logs ++ _ = _
    rw [hK2.logs, hK1.logs, afterSload_logs]
    have hev : ev = ⟨argBytes sevm 0, argBytes sevm 1,
        BeaconDeposit.le64 (v / BeaconDeposit.oneGwei), argBytes sevm 2,
        BeaconDeposit.le64 (solAcc stor).count⟩ := by
      rw [hpkB, hwcB, hsgB, hcnt]
      show bodyEvent sevm pP wP sP a w = _
      unfold bodyEvent
      rw [hamt]
      rfl
    rw [hev]
    rfl
  · intro y; rw [hW.code, afterSstore_getCode, hc6]
  · rw [hW.addrs, afterSstore_accessedAddresses, ha6]
  · rw [hW.output, afterSstore_output, hK6.output, afterSstore_output, hK5.output, hK4.output,
      hK3.output]
    show b2.output = _
    rw [hK2.output, hK1.output, afterSload_output]
  · rw [hW.error, afterSstore_error, hK6.error, afterSstore_error, hK5.error, hK4.error,
      hK3.error]
    show b2.error = _
    rw [hK2.error, hK1.error, afterSload_error]

end Blanc.Lift.BeaconDeposit
