import Blanc.Lift.Usdc.Footprint

/-!
# `Ledger.step` reads and writes only the frame's keys

Completeness of `frameKeys` against U5a's step, stated once:

* **reads** (`frameKeys_reads`): forgetting every mapping entry outside a key set `K` that holds the
  frame's keys (`Ledger.restrict K`) commutes with the step of the decoded call, so the step's
  outcome and its effect on `K` depend only on the entries at `K` and the fixed fields;
* **writes** (`frameKeys_writes`): a committed step leaves every mapping entry outside the frame's
  keys as it was (`Ledger.AgreeAt`).

Both hold at good ledgers (`Ledger.Good`), where `initializeV2_1` reverts before it reads the
proxy's own balance.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc

namespace Ledger

open Classical in
/-- The ledger with every mapping entry outside `K` forgotten (zero, or `false`); fixed fields
kept. -/
noncomputable def restrict (K : Key → Prop) (l : Ledger) : Ledger :=
  { l with
    bal := fun a => if K (.bal a) then l.bal a else 0
    frozen := fun a => if K (.bal a) then l.frozen a else false
    allow := fun o p => if K (.allow o p) then l.allow o p else 0
    nonce := fun a => if K (.nonce a) then l.nonce a else 0
    authUsed := fun a n => if K (.auth a n) then l.authUsed a n else false
    minter := fun a => if K (.minter a) then l.minter a else false
    minterAllowance := fun a => if K (.minterAllowance a) then l.minterAllowance a else 0 }

/-- Two ledgers agree at a key's entries. -/
def AgreeAt (l l' : Ledger) : Key → Prop
  | .bal a => l.bal a = l'.bal a ∧ l.frozen a = l'.frozen a
  | .allow o p => l.allow o p = l'.allow o p
  | .nonce a => l.nonce a = l'.nonce a
  | .auth a n => l.authUsed a n = l'.authUsed a n
  | .minter a => l.minter a = l'.minter a
  | .minterAllowance a => l.minterAllowance a = l'.minterAllowance a

section Restrict

variable {K : Key → Prop} {l : Ledger}

theorem restrict_bal {a : Adr} (h : K (.bal a)) : (l.restrict K).bal a = l.bal a := by
  simp only [restrict, h, ↓reduceIte]
theorem restrict_frozen {a : Adr} (h : K (.bal a)) : (l.restrict K).frozen a = l.frozen a := by
  simp only [restrict, h, ↓reduceIte]
theorem restrict_allow {o p : Adr} (h : K (.allow o p)) :
    (l.restrict K).allow o p = l.allow o p := by
  simp only [restrict, h, ↓reduceIte]
theorem restrict_authUsed {a : Adr} {n : B256} (h : K (.auth a n)) :
    (l.restrict K).authUsed a n = l.authUsed a n := by
  simp only [restrict, h, ↓reduceIte]
theorem restrict_minter {a : Adr} (h : K (.minter a)) : (l.restrict K).minter a = l.minter a := by
  simp only [restrict, h, ↓reduceIte]
theorem restrict_minterAllowance {a : Adr} (h : K (.minterAllowance a)) :
    (l.restrict K).minterAllowance a = l.minterAllowance a := by
  simp only [restrict, h, ↓reduceIte]

theorem restrict_paused : (l.restrict K).paused = l.paused := by
  unfold restrict; rfl
theorem restrict_owner : (l.restrict K).owner = l.owner := by
  unfold restrict; rfl
theorem restrict_pauser : (l.restrict K).pauser = l.pauser := by
  unfold restrict; rfl
theorem restrict_blacklister : (l.restrict K).blacklister = l.blacklister := by
  unfold restrict; rfl
theorem restrict_masterMinter : (l.restrict K).masterMinter = l.masterMinter := by
  unfold restrict; rfl
theorem restrict_rescuer : (l.restrict K).rescuer = l.rescuer := by
  unfold restrict; rfl
theorem restrict_supply : (l.restrict K).supply = l.supply := by
  unfold restrict; rfl
theorem restrict_initialized : (l.restrict K).initialized = l.initialized := by
  unfold restrict; rfl
theorem restrict_version : (l.restrict K).version = l.version := by
  unfold restrict; rfl

theorem restrict_setBal {a : Adr} (h : K (.bal a)) (x : Nat) :
    (l.restrict K).setBal a x = (l.setBal a x).restrict K := by
  unfold restrict setBal
  congr 1
  funext b
  by_cases hb : b = a
  · subst hb
    simp only [h, Function.update_self, ↓reduceIte]
  · simp only [Function.update_of_ne hb]

theorem restrict_setFrozen {a : Adr} (h : K (.bal a)) (x : Bool) :
    (l.restrict K).setFrozen a x = (l.setFrozen a x).restrict K := by
  unfold restrict setFrozen
  congr 1
  funext b
  by_cases hb : b = a
  · subst hb
    simp only [h, Function.update_self, ↓reduceIte]
  · simp only [Function.update_of_ne hb]

theorem restrict_setAllow {o p : Adr} (h : K (.allow o p)) (x : Nat) :
    (l.restrict K).setAllow o p x = (l.setAllow o p x).restrict K := by
  unfold restrict setAllow
  congr 1
  funext o' p'
  by_cases e : o' = o ∧ p' = p
  · obtain ⟨rfl, rfl⟩ := e
    simp only [h, and_self, ↓reduceIte]
  · simp only [e, ↓reduceIte]

theorem restrict_useAuth {a : Adr} {n : B256} (h : K (.auth a n)) :
    (l.restrict K).useAuth a n = (l.useAuth a n).restrict K := by
  unfold restrict useAuth
  congr 1
  funext a' n'
  by_cases e : a' = a ∧ n' = n
  · obtain ⟨rfl, rfl⟩ := e
    simp only [h, and_self, ↓reduceIte]
  · simp only [e, ↓reduceIte]

theorem restrict_setMinterAllowance {a : Adr} (h : K (.minterAllowance a)) (x : Nat) :
    (l.restrict K).setMinterAllowance a x = (l.setMinterAllowance a x).restrict K := by
  unfold restrict setMinterAllowance
  congr 1
  funext b
  by_cases hb : b = a
  · subst hb
    simp only [h, Function.update_self, ↓reduceIte]
  · simp only [Function.update_of_ne hb]

theorem restrict_bumpNonce {a : Adr} (h : K (.nonce a)) :
    (l.restrict K).bumpNonce a = (l.bumpNonce a).restrict K := by
  unfold restrict bumpNonce
  congr 1
  funext b
  by_cases hb : b = a
  · subst hb
    simp only [h, Function.update_self, ↓reduceIte]
  · simp only [Function.update_of_ne hb]

/-- The configure/remove-minter update commutes with forgetting (stated in the form the step's
record update takes once its fixed fields are read through `restrict`). -/
theorem restrict_setMinter {m : Adr} (hm : K (.minter m)) (hma : K (.minterAllowance m))
    (b : Bool) (x : Nat) :
    ({ bal := (l.restrict K).bal, frozen := (l.restrict K).frozen, allow := (l.restrict K).allow,
       nonce := (l.restrict K).nonce, authUsed := (l.restrict K).authUsed, paused := l.paused,
       owner := l.owner, pauser := l.pauser, blacklister := l.blacklister,
       masterMinter := l.masterMinter, rescuer := l.rescuer,
       minter := Function.update (l.restrict K).minter m b,
       minterAllowance := Function.update (l.restrict K).minterAllowance m x, supply := l.supply,
       initialized := l.initialized, version := l.version, admin := (l.restrict K).admin } : Ledger) =
      ({ l with minter := Function.update l.minter m b,
                minterAllowance := Function.update l.minterAllowance m x } : Ledger).restrict K := by
  unfold restrict
  dsimp only
  congr 1 <;> funext a <;> by_cases ha : a = m
  · subst ha
    simp only [hm, Function.update_self, ↓reduceIte]
  · simp only [Function.update_of_ne ha]
  · subst ha
    simp only [hma, Function.update_self, ↓reduceIte]
  · simp only [Function.update_of_ne ha]

/-- The supply update commutes with forgetting (in the step's post-read form). -/
theorem restrict_withSupply (x : Nat) :
    ({ bal := (l.restrict K).bal, frozen := (l.restrict K).frozen, allow := (l.restrict K).allow,
       nonce := (l.restrict K).nonce, authUsed := (l.restrict K).authUsed, paused := l.paused,
       owner := l.owner, pauser := l.pauser, blacklister := l.blacklister,
       masterMinter := l.masterMinter, rescuer := l.rescuer, minter := (l.restrict K).minter,
       minterAllowance := (l.restrict K).minterAllowance, supply := x,
       initialized := l.initialized, version := l.version, admin := (l.restrict K).admin } : Ledger) =
      ({ l with supply := x } : Ledger).restrict K := by
  unfold restrict
  rfl

theorem restrict_setBalance {a : Adr} (h : K (.bal a)) (x : Nat) :
    (l.restrict K).setBalance a x = (l.setBalance a x).map (restrict K) := by
  unfold setBalance
  rw [restrict_frozen h]
  split_ifs
  · rfl
  · rw [Option.map_some, restrict_setBal h]

theorem restrict_move {src dst : Adr} (hs : K (.bal src)) (hd : K (.bal dst)) (v : Nat) :
    (l.restrict K).move src dst v = (l.move src dst v).map (restrict K) := by
  unfold move
  rw [restrict_bal hs]
  split_ifs
  · rfl
  · rw [restrict_setBalance hs]
    rcases l.setBalance src (l.bal src - v) with _ | l₁
    · rfl
    · rw [Option.map_some, Option.bind_some, Option.bind_some, restrict_bal hd,
        restrict_setBalance hd]

theorem restrict_approveOf {o p : Adr} (h : K (.allow o p)) (x : Nat) :
    (l.restrict K).approveOf o p x = (l.approveOf o p x).map (restrict K) := by
  unfold approveOf
  split_ifs
  · rfl
  · rw [Option.map_some, restrict_setAllow h]

end Restrict

/-! ## Reads: the step commutes with forgetting untracked entries -/

/-- **The step reads only the call's keys**: at a good ledger, forgetting every mapping entry
outside a key set holding the call's keys commutes with the step. -/
theorem step_restrict {K : Key → Prop} {l : Ledger} (good : l.Good) (self caller : Adr) {c : Call}
    (hK : ∀ k ∈ c.keys caller, K k) :
    (l.restrict K).step self caller c = (l.step self caller c).map (restrict K) := by
  have v3 : l.version = 3 := good.version
  cases c
  all_goals
    simp (disch := (apply hK; simp only [Call.keys, List.mem_cons, List.not_mem_nil, true_or,
        or_true])) only [step, restrict_bal, restrict_frozen, restrict_allow, restrict_authUsed,
      restrict_minter, restrict_minterAllowance, restrict_paused, restrict_owner, restrict_pauser,
      restrict_blacklister, restrict_masterMinter, restrict_rescuer, restrict_supply,
      restrict_initialized, restrict_version, restrict_move, restrict_setBalance,
      restrict_approveOf, restrict_bumpNonce, restrict_useAuth, restrict_setAllow,
      restrict_setFrozen, restrict_setMinter, restrict_withSupply, restrict_setMinterAllowance,
      Option.map_map, Function.comp_def]
  all_goals (try split_ifs) <;>
    try (first | rfl | omega | simp only [Option.map_map, Function.comp_def])

/-! ## Writes: a committed step changes only the call's keys -/

/-- **The step writes only the call's keys**: at a good ledger, a committed step leaves every
mapping entry outside the call's keys as it was. -/
theorem step_agree {l l' : Ledger} (good : l.Good) {self caller : Adr} {c : Call}
    (h : l.step self caller c = some l') (k : Key) (hk : k ∉ c.keys caller) : l.AgreeAt l' k := by
  have v3 : l.version = 3 := good.version
  cases c <;> simp only [step] at h <;> (try split_ifs at h) <;> (try cases h) <;>
    (try (exfalso; omega))
  all_goals try first
    | (obtain ⟨-, -, -, rfl⟩ := move_eq_some h)
    | (obtain ⟨l₁, h₁, rfl⟩ := Option.map_eq_some_iff.mp h
       first
         | obtain ⟨-, -, -, rfl⟩ := move_eq_some h₁
         | obtain ⟨-, -, rfl⟩ := setBalance_eq_some h₁)
    | (obtain rfl := approveOf_eq_some h)
    | (obtain ⟨-, -, rfl⟩ := setBalance_eq_some h)
  all_goals
    cases k <;>
    (try simp only [Call.keys, List.mem_cons, List.not_mem_nil, or_false, not_or, Key.bal.injEq,
      Key.allow.injEq, Key.nonce.injEq, Key.auth.injEq, Key.minter.injEq, Key.minterAllowance.injEq,
      reduceCtorEq, not_false_eq_true] at hk) <;>
    simp_all only [AgreeAt, setBal, setAllow, setFrozen, useAuth, bumpNonce, setMinterAllowance,
      moveBal, Function.update_apply, ↓reduceIte, and_self, true_and]

end Ledger

/-! ## Against `frameKeys` -/

/-- **`frameKeys` is complete for the step's reads**: for a decodable frame whose keys are all in
`K`, forgetting the entries outside `K` commutes with the decoded call's step. -/
theorem frameKeys_reads {e : Sevm} {c : Call} (dec : decodeCall e = some c) {K : Key → Prop}
    (tracked : ∀ k ∈ frameKeys e, K k) {l : Ledger} (good : l.Good) (self : Adr) :
    (l.restrict K).step self e.caller c = (l.step self e.caller c).map (Ledger.restrict K) :=
  Ledger.step_restrict good self e.caller fun k hk => tracked k (keys_sub_frameKeys dec k hk)

/-- **`frameKeys` is complete for the step's writes**: a committed step of a decodable frame
leaves every mapping entry outside the frame's keys as it was. -/
theorem frameKeys_writes {e : Sevm} {c : Call} (dec : decodeCall e = some c) {l l' : Ledger}
    (good : l.Good) {self : Adr} (h : l.step self e.caller c = some l') (k : Key)
    (hk : k ∉ frameKeys e) : l.AgreeAt l' k :=
  Ledger.step_agree good h k fun hc => hk (keys_sub_frameKeys dec k hc)

end Blanc.Lift.Usdc
