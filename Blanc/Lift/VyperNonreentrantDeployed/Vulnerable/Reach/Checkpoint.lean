import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Fund
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Approve
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.AddTop

/-! # V3: the funded checkpoint with a sound LP ledger, reached by execution

`setup_checkpoint` composes the seven root messages of the V− setup, each starting from exactly
the previous message's settled world, on every covered fork, from the disclosed initial world
(the funded code-free creator only):

1. the preserved implementation CREATE; 2. the synthetic clone CREATE; 3. `initialize` through
the clone; 4. the synthetic token CREATE (minting `10^6` to the creator); 5. the synthetic
attacker CREATE; 6. `T.approve(proxy, 1000)`; 7. `P.add_liquidity([1000, 1000], 0, attacker)`
with value 1000, whose `transferFrom(creator, proxy, 1000)` runs as a real child.

The reached world satisfies `SoundCheckpoint` (an explicit, finite statement about storage and
accounts): the LP ledger is sound over the footprint `{attacker}` (`totalSupply = 2000 =
balanceOf[attacker]`), every nonzero pool slot is a configuration slot, a reserve slot, the
supply slot or the attacker's LP slot (raw support; the LP slot is checked distinct from the
fixed slots), the five locks are free, the reserves are `[1000, 1000]`, and the assets are held:
the pool's account has 1000 wei and the token's `balanceOf[proxy] = 1000`.  No pool state is
seeded and no token answer is fabricated: every write is an executed `SSTORE`.  The raw-support
statement is about slots: that no mapping key of another address hashes onto one of these slots
is a hash fact outside the finite observation. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init (WorldIs)

/-! ### Worlds described by shadows, through creations -/

theorem worldIs_congr {W : State} {acs acs' : AcctShadow} {stor : StorShadow}
    (h : WorldIs W acs stor) (ha : ∀ a, lookupA acs a = lookupA acs' a) : WorldIs W acs' stor :=
  ⟨fun a => (h.1 a).trans (ha a), h.2⟩

/-- A world that changes exactly one account `T` (to `ac`, whose storage the shadow `sT ++ stor`
describes, `sT` only at `T`) is described by the shadows with `T`'s view and writes prepended. -/
theorem worldIs_set {W W' : State} {acs : AcctShadow} {stor sT : StorShadow} {T : Adr} {ac : Acct}
    (hW : WorldIs W acs stor) (hT : W'.get T = ac) (hrest : ∀ a, a ≠ T → W'.get a = W.get a)
    (hsT : ∀ e ∈ sT, e.1.1 = T) (hstor : ∀ k, ac.stor.get k = lookupS (sT ++ stor) T k) :
    WorldIs W' ((T, acctView ac) :: acs) (sT ++ stor) := by
  refine ⟨fun a => ?_, fun a k => ?_⟩
  · by_cases h : a = T
    · subst h; rw [hT]; simp only [lookupA, if_pos]
    · rw [hrest a h, hW.1 a]; simp only [lookupA, Ne.symm h, if_false]
  · by_cases h : a = T
    · subst h; rw [storOf, hT]; exact hstor k
    · rw [storOf, hrest a h, ← storOf, hW.2 a k,
        lookupS_append_of_ne (fun e he hea => h (hea.symm.trans (hsT e he)))]

/-- The account view of an absent account is nil: nonce 0, balance 0. -/
theorem nonce_bal_of_nil {W : State} {acs : AcctShadow} {a : Adr} (hW : AcctAgree W acs)
    (h : lookupA acs a = .nil) : (W.get a).nonce = 0 ∧ (W.get a).bal = 0 := by
  have hv := (hW a).trans h
  have h1 := congrArg Acct.nonce hv
  have h2 := congrArg Acct.bal hv
  exact ⟨h1, h2⟩

/-! ### The funded world -/

theorem acs2_attacker : lookupA acs2 attackerAddr = .nil := by
  simp only [acs2, lookupA]; rfl
theorem acs2_token : lookupA acs2 tokenAddr = .nil := by
  simp only [acs2, lookupA]; rfl

theorem stor2_attacker (k : B256) : lookupS (initWrites ++ stor2) attackerAddr k = 0 :=
  lookupS_eq_zero_of fun e he hek => by
    simp only [initWrites, stor2, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Prod.mk.injEq] at hek <;> exact absurd hek.1 (by decide)

theorem stor2_token (k : B256) : lookupS (initWrites ++ stor2) tokenAddr k = 0 :=
  lookupS_eq_zero_of fun e he hek => by
    simp only [initWrites, stor2, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Prod.mk.injEq] at hek <;> exact absurd hek.1 (by decide)

/-- The account shadow of the funded world, as the creations build it. -/
def acsFund : AcctShadow :=
  (attackerAddr, ⟨1, 0, .empty, AttackerR.code⟩) ::
    (tokenAddr, ⟨1, 0, .empty, Token20.code⟩) :: acs2

theorem acsFund_lookup (a : Adr) : lookupA acsFund a = lookupA acs6 a := by
  refine lookupA_eq_of_keys (fun b hb => ?_) a
  have hk : acsFund.map Prod.fst ++ acs6.map Prod.fst =
      [attackerAddr, tokenAddr, creator, implAddr, proxyAddr, attackerAddr, tokenAddr, proxyAddr,
        implAddr, creator] := rfl
  rw [hk] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ### The sound checkpoint -/

/-- `balanceOf[h]`'s slot in the pool (`keccak256(pad32(24) ‖ pad32(h))`). -/
def lpSlot (h : Adr) : B256 := Bytes.keccak (abiWord 24 ++ abiWord h.toNat)

/-- The LP footprint of the setup: every `balanceOf` write it executes is to the attacker. -/
def lpFootprint : List Adr := [attackerAddr]

/-- The pool slots the reached world may hold nonzero: the configuration, the reserves
`balances[0..1]` (8, 9), `totalSupply` (26), and the footprint's LP balance. -/
def supportSlots : List B256 := configSlots ++ [8, 9, 26, lpSlotA]

/-- **The sound funded checkpoint** of the V− pool at `proxyAddr` over the world `W`. -/
def SoundCheckpoint (W : State) : Prop :=
  -- the sound LP ledger over the finite footprint
  (storOf W proxyAddr 26).toNat = (lpFootprint.map fun h => (storOf W proxyAddr (lpSlot h)).toNat).sum ∧
  storOf W proxyAddr 26 = 2000 ∧ storOf W proxyAddr (lpSlot attackerAddr) = 2000 ∧
  -- raw support, and the footprint slot separated from the fixed slots
  (∀ k, storOf W proxyAddr k ≠ 0 → k ∈ supportSlots) ∧
  lpSlot attackerAddr ∉ configSlots ++ [0, 1, 2, 3, 4, 8, 9, 26] ∧
  -- recorded reserves, free locks, held assets
  storOf W proxyAddr 8 = 1000 ∧ storOf W proxyAddr 9 = 1000 ∧
  (∀ i ∈ ([0, 1, 2, 3, 4] : List B256), storOf W proxyAddr i = 0) ∧
  (W.get proxyAddr).bal = 1000 ∧ storOf W tokenAddr (Token20.balSlot proxyAddr) = 1000 ∧
  -- the configuration `initialize` set is unchanged
  (∀ k ∈ configSlots, storOf W proxyAddr k = lookupS initWrites proxyAddr k)

theorem lpSlot_attacker : lpSlot attackerAddr = lpSlotA := lpSlotA_eq.symm

theorem storAdd_proxy (k : B256) (hk : k ∉ supportSlots) : lookupS storAdd proxyAddr k = 0 := by
  refine lookupS_eq_zero_of fun e he hek => ?_
  have hs : ∀ e ∈ storAdd, e.1.1 = proxyAddr → e.1.2 ∈ supportSlots := by decide +kernel
  by_contra _
  have h := hs e he (by rw [hek])
  rw [hek] at h
  exact hk h

theorem checkpoint_of {W : State} (hs : ∀ a k, storOf W a k = lookupS storAdd a k)
    (ha : AcctAgree W acsB) : SoundCheckpoint W := by
  have hsep : lpSlotA ∉ configSlots ++ [0, 1, 2, 3, 4, 8, 9, 26] := by decide +kernel
  have h26 : storOf W proxyAddr 26 = 2000 := (hs _ _).trans (by decide +kernel)
  have hA : storOf W proxyAddr lpSlotA = 2000 := (hs _ _).trans (by decide +kernel)
  refine ⟨?_, h26, (by rw [lpSlot_attacker]; exact hA), fun k hk => ?_,
    (by rw [lpSlot_attacker]; exact hsep), (hs _ _).trans (by decide +kernel),
    (hs _ _).trans (by decide +kernel),
    fun i hi => ?_, ?_, (hs _ _).trans (by decide +kernel), fun k hk => ?_⟩
  · simp only [lpFootprint, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      lpSlot_attacker, h26, hA]
  · by_contra hn
    exact hk ((hs _ _).trans (storAdd_proxy k hn))
  · rw [hs]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · have h := congrArg Acct.bal (ha proxyAddr)
    exact h.trans (by decide +kernel)
  · rw [hs]
    simp only [configSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-! ### The seven messages -/

/-- **V3, every covered fork: the V− setup reaches a sound funded checkpoint by execution.**
From the disclosed initial world (the funded code-free creator only), seven root messages, each
starting from exactly the previous message's settled world, all succeed: the implementation and
clone creations, `initialize`, the token and attacker creations, `approve(proxy, 1000)` (77,697
gas left) and the first `add_liquidity([1000, 1000], 0, attacker)` with value 1000 (826,595 gas
left, 2000 LP minted).  The world before `approve` is the funded world (`acs6`/`stor5`), and the
reached world satisfies `SoundCheckpoint`; it is also fully described by the shadows
`acsB`/`storAdd` (every account and every storage slot). -/
theorem setup_checkpoint (fork : Fork) (hfork : CoveredFork fork) :
    ∃ postI postP postC tokenPost attackerPost approvePost addPost : Devm,
      processCreateMessage (implCreateMsg fork initialWorld) = .ok postI ∧ postI.error = none ∧
      processCreateMessage (cloneCreateMsg fork postI.state) = .ok postP ∧ postP.error = none ∧
      processMessage (initMsg fork postP.state) = .ok postC ∧ postC.error = none ∧
      CleanPool postC.state ∧
      processCreateMessage (tokenCreateMsg fork postC.state) = .ok tokenPost ∧
      tokenPost.error = none ∧
      processCreateMessage (attackerCreateMsg fork tokenPost.state) = .ok attackerPost ∧
      attackerPost.error = none ∧
      WorldIs attackerPost.state acs6 stor5 ∧
      processMessage (approveMsg fork attackerPost.state) = .ok approvePost ∧
      approvePost.error = none ∧ approvePost.gasLeft = 77697 ∧
      WorldIs approvePost.state acs6 stor6 ∧
      processMessage (addMsg fork approvePost.state) = .ok addPost ∧
      addPost.error = none ∧ addPost.gasLeft = 826595 ∧ addPost.output = abiWord 2000 ∧
      SoundCheckpoint addPost.state ∧
      (∀ a k, storOf addPost.state a k = lookupS storAdd a k) ∧ AcctAgree addPost.state acsB := by
  -- messages 1–3
  obtain ⟨postI, postP, h1, e1, -, -, -, -, h2, e2, -, -, -, -, hS⟩ :=
    setup_creations fork hfork initialWorld initialWorld_absent.1 initialWorld_absent.2
  have hw : postP.state = world2 := hS
  obtain ⟨postC, h3, e3, -, -, hs, ha⟩ := init_message_at (g := fork) hfork
  obtain ⟨hpool, -, hview⟩ := init_world_facts hs ha
  have hWC : WorldIs postC.state acs2 (initWrites ++ stor2) :=
    ⟨fun a => (hview a).trans (acctAgree2 a), hs⟩
  -- message 4: the token
  obtain ⟨tokenPost, hT, eT, -, hTtok, hTrest, -⟩ :=
    Token20.Creation.create_token (tokenCreateMsg fork postC.state) hfork rfl rfl rfl rfl rfl
      (by show (82000 : Nat) ≤ 200000; decide)
  have hTtok' : tokenPost.state.get tokenAddr = Token20.Creation.tokenAcct postC.state tokenAddr
      creator := hTtok
  obtain ⟨hTn, hTb⟩ := nonce_bal_of_nil hWC.1 acs2_token
  have hWT := worldIs_set (sT := [((tokenAddr, creator.toB256), 1000000)]) hWC hTtok' hTrest
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq])
    (fun k => by
      show (Stor.empty.set creator.toB256 1000000).get k = _
      rw [Stor.get_set_ite]
      simp only [List.cons_append, List.nil_append, lookupS, true_and]
      by_cases hk : creator.toB256 = k
      · rw [if_pos hk, if_pos hk]
      · rw [if_neg hk, if_neg hk, stor2_token]; rfl)
  have hvT : acctView (Token20.Creation.tokenAcct postC.state tokenAddr creator) =
      ⟨1, 0, .empty, Token20.code⟩ := by
    simp only [acctView, Token20.Creation.tokenAcct, hTn, hTb]; rfl
  rw [hvT] at hWT
  -- message 5: the attacker
  obtain ⟨attackerPost, hA, eA, -, hAatk, hArest, -⟩ :=
    AttackerR.Creation.create_attacker (attackerCreateMsg fork tokenPost.state) hfork rfl rfl rfl
      rfl (by show (37252 : Nat) ≤ 200000; decide)
  have hAatk' : attackerPost.state.get attackerAddr =
      AttackerR.Creation.attackerAcct tokenPost.state attackerAddr := hAatk
  obtain ⟨hAn, hAb⟩ := nonce_bal_of_nil hWT.1 (show lookupA ((tokenAddr, _) :: acs2) attackerAddr = .nil
    by simp only [lookupA, show tokenAddr ≠ attackerAddr by decide, if_false]; exact acs2_attacker)
  have hWA := worldIs_set (sT := []) hWT hAatk' hArest (by simp only [List.not_mem_nil,
    false_implies, implies_true])
    (fun k => by
      show Stor.empty.get k = _
      simp only [List.nil_append, List.cons_append, lookupS,
        show tokenAddr ≠ attackerAddr by decide, false_and, if_false]
      rw [stor2_attacker]; rfl)
  have hvA : acctView (AttackerR.Creation.attackerAcct tokenPost.state attackerAddr) =
      ⟨1, 0, .empty, AttackerR.code⟩ := by
    simp only [acctView, AttackerR.Creation.attackerAcct, hAn, hAb]; rfl
  rw [hvA] at hWA
  have hW5 : WorldIs attackerPost.state acs6 stor5 := worldIs_congr hWA acsFund_lookup
  -- message 6: approve
  obtain ⟨apPost, hAp, hApe, hApg, hW6⟩ := approve_message_at hfork hW5
  -- message 7: add_liquidity
  obtain ⟨addPost, hAdd, hAe, hAg, hAo, hstor, hacs⟩ := add_message_at hfork hW6
  exact ⟨postI, postP, postC, tokenPost, attackerPost, apPost, addPost, h1, e1, h2, e2,
    by rw [hw]; exact h3, e3, cleanPool_of hpool, hT, eT, hA, eA, hW5, hAp, hApe, hApg, hW6, hAdd,
    hAe, hAg, hAo, checkpoint_of hstor hacs, hstor, hacs⟩

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach
