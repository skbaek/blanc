import Blanc.LidoCircuitBreakerHistory

/-!
# Registry integrity through arbitrary histories — storage-silent and
Registry-disjoint endpoints

The dispatch targets whose `FuncSound` obligation needs neither the Registry
mutation machinery nor the deeper-frame hypothesis: the twelve views, and the
three endpoints whose only persistent writes land outside every Registry
region.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

/-! ## The five immutable-constant views

`returnDeployWord` is call-free: a PUSH32, an MSTORE and a RETURN.  One lemma
covers `ADMIN`, `MIN_PAUSE_DURATION`, `MAX_PAUSE_DURATION`,
`MIN_HEARTBEAT_INTERVAL` and `MAX_HEARTBEAT_INTERVAL`. -/

theorem storFixed_returnDeployWord (dp : DeployParams) (w : B256) :
    StorFixed dp (returnDeployWord w) := by
  apply StorFixed.of_inv
  unfold returnDeployWord pushDeployWord
  func_inv

/-! ## The two configuration views -/

theorem storFixed_pauseDuration (dp : DeployParams) :
    StorFixed dp pauseDuration :=
  StorFixed.of_inv (by func_inv)

theorem storFixed_heartbeatInterval (dp : DeployParams) :
    StorFixed dp heartbeatInterval :=
  StorFixed.of_inv (by func_inv)

/-! ## The four argument-taking views

Each shares one envelope: the static-argument length guard, whose failure arm
is `Func.rev`, then the canonical-address check, whose failure arm tail-jumps
to `emptyRevertSlot`.  The jump is what `Func.Inv` cannot cross, and what
`StorFixed` discharges by naming the slot's actual occupant. -/

/-- `emptyRevertSlot` is index 12, and `aux`'s twelfth entry is the bare
revert. -/
theorem get_emptyRevertSlot (dp : DeployParams) :
    ((runtime dp).main :: aux)[emptyRevertSlot]? = some Func.rev := rfl

theorem storFixed_staticAddressView {dp : DeployParams} {body : Func}
    (h : Func.Inv Devm.getStor Devm.getStor body) :
    StorFixed dp (requireStaticArgs 1 (canonicalAddressArg 0 body)) := by
  unfold requireStaticArgs canonicalAddressArg
  refine StorFixed.next (StorFixed.next (StorFixed.next ?_))
  refine StorFixed.branch ?_ StorFixed.rev
  refine StorFixed.prepend (by line_inv) (StorFixed.prepend (by line_inv) ?_)
  exact StorFixed.branch (StorFixed.of_inv h)
    (StorFixed.call (get_emptyRevertSlot dp) StorFixed.rev)

theorem storFixed_heartbeatExpiry (dp : DeployParams) :
    StorFixed dp heartbeatExpiry :=
  storFixed_staticAddressView (by func_inv)

theorem storFixed_getPauser (dp : DeployParams) :
    StorFixed dp getPauser :=
  storFixed_staticAddressView (by func_inv)

theorem storFixed_getPausableCount (dp : DeployParams) :
    StorFixed dp getPausableCount :=
  storFixed_staticAddressView (by func_inv)

theorem storFixed_isPauserLive (dp : DeployParams) :
    StorFixed dp isPauserLive :=
  storFixed_staticAddressView (by func_inv)

/-! ## The enumeration cycle

`enumLoop` tail-jumps to its own auxiliary slot, so `StorFixed.call` cannot
discharge it: the obligation it leaves is the one being proved.  The fixed
point is taken instead over the `Func.Run` derivation, guarded by a syntactic
storage-silence predicate that is closed under the permitted jump — exactly the
shape `Func.CallsIn` uses to make `Func.Run.mono` structural. -/

private theorem storFixed_of_silentIn {dp : DeployParams} {P : Nat → Prop}
    (hclosed : ∀ k g, P k → ((runtime dp).main :: aux)[k]? = some g →
      Func.StorSilentIn P g)
    {f : Func} (hf : Func.StorSilentIn P f) : StorFixed dp f :=
  fun hrun => Func.getStor_eq_of_run_storSilentIn hclosed hrun hf

private theorem silentIn_enumLoop :
    Func.StorSilentIn (fun k => k = enumLoopSlot) enumLoop := by
  unfold enumLoop
  repeat' first
    | rfl
    | exact Ninst.Hinv.inv
    | exact Linst.Hinv.inv
    | refine ⟨?_, ?_⟩

private theorem silentIn_getPausables :
    Func.StorSilentIn (fun k => k = enumLoopSlot) getPausables := by
  unfold getPausables
  repeat' first
    | rfl
    | exact Ninst.Hinv.inv
    | exact Linst.Hinv.inv
    | refine ⟨?_, ?_⟩

/-- `enumLoopSlot` is index 21, and `aux`'s twenty-first entry is the loop
itself. -/
theorem get_enumLoopSlot (dp : DeployParams) :
    ((runtime dp).main :: aux)[enumLoopSlot]? = some enumLoop := rfl

private theorem enumLoopSlot_closed (dp : DeployParams) :
    ∀ k g, k = enumLoopSlot → ((runtime dp).main :: aux)[k]? = some g →
      Func.StorSilentIn (fun k => k = enumLoopSlot) g := by
  rintro k g rfl hget
  obtain rfl : enumLoop = g :=
    Option.some.inj ((get_enumLoopSlot dp).symm.trans hget)
  exact silentIn_enumLoop

theorem storFixed_enumLoop (dp : DeployParams) : StorFixed dp enumLoop :=
  storFixed_of_silentIn (enumLoopSlot_closed dp) silentIn_enumLoop

theorem storFixed_getPausables (dp : DeployParams) : StorFixed dp getPausables :=
  storFixed_of_silentIn (enumLoopSlot_closed dp) silentIn_getPausables

/-! ## Writes that miss every Registry region

`RegistryWitness` reads five families: the array length and entries (region 6),
the assignments (region 3), the reverse indices (region 4) and the counts
(region 5).  `RegistryWitness.expiry_set` is the landed statement that a write
in region 2 disturbs none of them.  Region 1 — the configuration pair
`pauseDurationSlot`/`heartbeatIntervalSlot` — has no landed analogue, so it is
supplied here, on the same skeleton. -/

private theorem zero_payload_lt : (0 : B256).toNat < 2 ^ 252 := by
  change (0 : Nat) < 2 ^ 252
  norm_num

private theorem one_payload_lt : (1 : B256).toNat < 2 ^ 252 := by
  change (1 : Nat) < 2 ^ 252
  norm_num

private theorem configSlot_ne_arrayLengthSlot {payload : B256}
    (hpayload : payload.toNat < 2 ^ 252) :
    slot configRegion payload ≠ arrayLengthSlot :=
  slot_ne_of_region_ne (by norm_num [configRegion]) (by norm_num [arrayRegion])
    hpayload zero_payload_lt (by norm_num [configRegion, arrayRegion])

private theorem configSlot_ne_arrayEntrySlot {payload index : B256}
    (hpayload : payload.toNat < 2 ^ 252) (hindex : index.toNat < 2 ^ 252) :
    slot configRegion payload ≠ arrayEntrySlot index :=
  slot_ne_of_region_ne (by norm_num [configRegion]) (by norm_num [arrayRegion])
    hpayload hindex (by norm_num [configRegion, arrayRegion])

private theorem configSlot_ne_assignmentSlot {payload target : B256}
    (hpayload : payload.toNat < 2 ^ 252) (htarget : target.toNat < 2 ^ 252) :
    slot configRegion payload ≠ assignmentSlot target :=
  slot_ne_of_region_ne (by norm_num [configRegion])
    (by norm_num [assignmentRegion]) hpayload htarget
    (by norm_num [configRegion, assignmentRegion])

private theorem configSlot_ne_indexSlot {payload target : B256}
    (hpayload : payload.toNat < 2 ^ 252) (htarget : target.toNat < 2 ^ 252) :
    slot configRegion payload ≠ indexSlot target :=
  slot_ne_of_region_ne (by norm_num [configRegion]) (by norm_num [indexRegion])
    hpayload htarget (by norm_num [configRegion, indexRegion])

private theorem configSlot_ne_countSlot {payload pauser : B256}
    (hpayload : payload.toNat < 2 ^ 252) (hpauser : pauser.toNat < 2 ^ 252) :
    slot configRegion payload ≠ countSlot pauser :=
  slot_ne_of_region_ne (by norm_num [configRegion]) (by norm_num [countRegion])
    hpayload hpauser (by norm_num [configRegion, countRegion])

/-- Writing one configuration word cannot alter any projected Registry field.
The region-1 counterpart of `RegistryWitness.expiry_set`. -/
theorem RegistryWitness.config_set {s : Stor} {entries : List Entry}
    (hw : RegistryWitness (logicalStorageOfStor s) entries)
    {payload value : B256} (hpayload : payload.toNat < 2 ^ 252) :
    RegistryWitness
      (logicalStorageOfStor (s.set (slot configRegion payload) value))
      entries := by
  refine {
    targetsNodup := hw.targetsNodup
    targetsValid := hw.targetsValid
    pausersValid := hw.pausersValid
    lengthWord := ?_
    arrayWords := ?_
    assignments := ?_
    indices := ?_
    counts := ?_
    zeroCount := ?_
  }
  · change (s.set (slot configRegion payload) value).get arrayLengthSlot =
      Nat.toB256 entries.length
    rw [Stor.get_set_ne _ (configSlot_ne_arrayLengthSlot hpayload)]
    exact hw.lengthWord
  · intro index hindex
    have hindex256 : index + 1 < 2 ^ 256 := by
      have hbound := hw.entries_length_le
      norm_num at hbound ⊢
      omega
    have hindex252 : (Nat.toB256 (index + 1)).toNat < 2 ^ 252 := by
      rw [B256.toNat_toB256_of_lt hindex256]
      have hbound := hw.entries_length_le
      norm_num at hbound ⊢
      omega
    change (s.set (slot configRegion payload) value).get
      (arrayEntrySlot (Nat.toB256 (index + 1))) = targetAt entries index
    rw [Stor.get_set_ne _ (configSlot_ne_arrayEntrySlot hpayload hindex252)]
    exact hw.arrayWords index hindex
  · intro target htarget
    change (s.set (slot configRegion payload) value).get
      (assignmentSlot target) = assignmentAt entries target
    rw [Stor.get_set_ne _ (configSlot_ne_assignmentSlot hpayload
      (canonicalAddress_payload_lt htarget))]
    exact hw.assignments target htarget
  · intro target htarget
    change (s.set (slot configRegion payload) value).get (indexSlot target) =
      Nat.toB256 (oneBasedIndexAt entries target)
    rw [Stor.get_set_ne _ (configSlot_ne_indexSlot hpayload
      (canonicalAddress_payload_lt htarget))]
    exact hw.indices target htarget
  · intro counted hcounted
    change (s.set (slot configRegion payload) value).get (countSlot counted) =
      Nat.toB256 (assignmentCount entries counted)
    rw [Stor.get_set_ne _ (configSlot_ne_countSlot hpayload
      (canonicalAddress_payload_lt hcounted))]
    exact hw.counts counted hcounted
  · change (s.set (slot configRegion payload) value).get (countSlot 0) = 0
    rw [Stor.get_set_ne _ (configSlot_ne_countSlot hpayload zero_payload_lt)]
    exact hw.zeroCount

theorem RegistryCoherent.config_set {s : Stor} (h : RegistryCoherent s)
    {payload value : B256} (hpayload : payload.toNat < 2 ^ 252) :
    RegistryCoherent (s.set (slot configRegion payload) value) :=
  h.imp fun _ hw => hw.config_set hpayload

theorem RegistryCoherent.expiry_set {s : Stor} (h : RegistryCoherent s)
    {pauser value : B256} (hpauser : canonicalAddress pauser) :
    RegistryCoherent (s.set (expirySlot pauser) value) :=
  h.imp fun _ hw => hw.expiry_set hpauser

/-- An `Adr` word is a canonical address: its `B256` image is its own
`Adr.toNat`, which is below `2 ^ 160`. -/
theorem canonicalAddress_toB256 (a : Adr) : canonicalAddress a.toB256 := by
  have heq : a.toB256.toNat = a.toNat := by
    simp [Adr.toB256, Adr.toNat, B256.toNat, B128.toNat]
  show a.toB256.toNat < 2 ^ 160
  rw [heq]
  exact Adr.toNat_lt_size a

/-! ## Coherence-preserving bodies

The three writing endpoints are not storage-silent, so `StorFixed` cannot carry
them.  `Coherent` is the same assembly discipline over the program-free core:
silent fragments transport the invariant unchanged, and the one write per body
is discharged by the region-disjointness of the key it actually uses. -/

/-- Registry-coherence preservation at the frame's own target, in the exact
runtime context: the shape `funcSound_of_registryCore` consumes. -/
def Coherent (dp : DeployParams) (f : Func) : Prop :=
  Func.Core ((runtime dp).main :: aux) RegistryCoherent f

namespace Coherent

variable {dp : DeployParams}

theorem of_storFixed {f : Func} (h : StorFixed dp f) : Coherent dp f := by
  intro sevm s r hrun hcoh
  rw [h hrun]
  exact hcoh

theorem prepend {l : Line} {f : Func} (hl : Line.Inv Devm.getStor l)
    (hf : Coherent dp f) : Coherent dp (l +++ f) := by
  intro sevm s r hrun hcoh
  rcases of_run_prepend _ _ hrun with ⟨s', hl', hf'⟩
  refine hf hf' ?_
  rw [← congrFun (hl hl') sevm.currentTarget]
  exact hcoh

theorem next {i : Ninst} {f : Func} [Ninst.Hinv Devm.getStor i]
    (hf : Coherent dp f) : Coherent dp (i ::: f) := by
  intro sevm s r hrun hcoh
  rcases of_run_next hrun with ⟨s', hi, hrest⟩
  refine hf hrest ?_
  rw [← congrFun (Ninst.Hinv.inv (f := Devm.getStor) hi) sevm.currentTarget]
  exact hcoh

theorem branch {f g : Func} (hf : Coherent dp f) (hg : Coherent dp g) :
    Coherent dp (Func.branch f g) := by
  intro sevm s r hrun hcoh
  rcases of_run_branch hrun with
    ⟨s', hpb, hrun'⟩ | ⟨w, s', s'', hw, hpb, hb, hrun'⟩
  · refine hf hrun' ?_
    rw [← getStor_eq_of_state_eq hpb.state sevm.currentTarget]
    exact hcoh
  · refine hg hrun' ?_
    rw [← getStor_eq_of_state_eq (hpb.state.trans hb.state) sevm.currentTarget]
    exact hcoh

theorem call {k : Nat} {g : Func}
    (hk : ((runtime dp).main :: aux)[k]? = some g) (hg : Coherent dp g) :
    Coherent dp (.call k) := by
  intro sevm s r hrun hcoh
  cases hrun with
  | call hget hburn hrun' =>
    obtain rfl := Option.some.inj (hk.symm.trans hget)
    refine hg hrun' ?_
    rw [← getStor_eq_of_state_eq hburn.state sevm.currentTarget]
    exact hcoh

/-- The `PUSH key; SSTORE` idiom at a fixed key, with a storage-silent
continuation. -/
theorem pushSstore {key : B256} {f : Func}
    (hkey : ∀ (t : Stor) (v : B256),
      RegistryCoherent t → RegistryCoherent (t.set key v))
    (hf : StorFixed dp f) :
    Coherent dp (pushB256 key ::: Ninst.sstore ::: f) := by
  intro sevm s r hrun hcoh
  rcases of_run_next hrun with ⟨s1, hpush, hrest⟩
  rcases of_run_next hrest with ⟨s2, hstore, htail⟩
  have hpref : [key] <<+ s1.stack :=
    prefix_of_push (of_run_pushB256 hpush) nil_pref
  obtain ⟨v, hset⟩ := sstore_getStor_setStorVal hstore hpref
  have h1 : Devm.getStor s = Devm.getStor s1 :=
    Ninst.Hinv.inv (f := Devm.getStor) hpush
  rw [hf htail, hset, ← congrFun h1]
  exact hkey _ v hcoh

/-- The `CALLER; PUSH tag; OR; SSTORE` idiom: the key is the caller's cell in
`region`, and the caller is a canonical address by construction. -/
theorem callerTagSstore {region : Nat} {f : Func}
    (hkey : ∀ (a : Adr) (t : Stor) (v : B256),
      RegistryCoherent t → RegistryCoherent (t.set (slot region a.toB256) v))
    (hf : StorFixed dp f) :
    Coherent dp (Ninst.caller ::: pushB256 (regionWord region) :::
      Ninst.or ::: Ninst.sstore ::: f) := by
  intro sevm s r hrun hcoh
  rcases of_run_next hrun with ⟨s1, hcaller, hrest⟩
  rcases of_run_next hrest with ⟨s2, hpush, hrest⟩
  rcases of_run_next hrest with ⟨s3, hor, hrest⟩
  rcases of_run_next hrest with ⟨s4, hstore, htail⟩
  have p1 : [sevm.caller.toB256] <<+ s1.stack :=
    prefix_of_push (of_run_caller hcaller) nil_pref
  have p2 : [regionWord region, sevm.caller.toB256] <<+ s2.stack :=
    prefix_of_push (of_run_pushB256 hpush) p1
  have p3 : [slot region sevm.caller.toB256] <<+ s3.stack := prefix_of_or hor p2
  obtain ⟨v, hset⟩ := sstore_getStor_setStorVal hstore p3
  have hs : Devm.getStor s = Devm.getStor s3 :=
    (Ninst.Hinv.inv (f := Devm.getStor) hcaller).trans
      ((Ninst.Hinv.inv (f := Devm.getStor) hpush).trans
        (Ninst.Hinv.inv (f := Devm.getStor) hor))
  rw [hf htail, hset, ← congrFun hs]
  exact hkey sevm.caller _ v hcoh

end Coherent

/-! ## The reverting auxiliary targets

Every guard arm of a writing endpoint tail-jumps to a custom-error reverter.
`Func.revSelector` is a fixed six-node chain and needs no evaluation; the
arithmetic panic is a `Func.revData`, whose node count depends on a Keccak
image, so it is handled generically over the blob instead of by unfolding. -/

private theorem funcInv_prependStoresRev :
    ∀ (iws : List (B256 × Nat)) {rest : Func},
      Func.Inv Devm.getStor Devm.getStor rest →
      Func.Inv Devm.getStor Devm.getStor (prependStoresRev iws rest)
  | [], _, h => h
  | _ :: iws, _, h =>
      funcInv_prependStoresRev iws
        (next_inv Ninst.Hinv.inv
          (next_inv Ninst.Hinv.inv (next_inv Ninst.Hinv.inv h)))

private theorem storFixed_revData {dp : DeployParams} (blob : Bytes) :
    StorFixed dp (Func.revData blob) :=
  StorFixed.of_inv
    (funcInv_prependStoresRev _
      (next_inv Ninst.Hinv.inv
        (next_inv Ninst.Hinv.inv (last_inv Linst.Hinv.inv))))

theorem storFixed_senderNotAdminError (dp : DeployParams) :
    StorFixed dp senderNotAdminError := StorFixed.of_inv (by func_inv)

theorem storFixed_senderNotPauserError (dp : DeployParams) :
    StorFixed dp senderNotPauserError := StorFixed.of_inv (by func_inv)

theorem storFixed_pauseBelowMinError (dp : DeployParams) :
    StorFixed dp pauseBelowMinError := StorFixed.of_inv (by func_inv)

theorem storFixed_pauseAboveMaxError (dp : DeployParams) :
    StorFixed dp pauseAboveMaxError := StorFixed.of_inv (by func_inv)

theorem storFixed_heartbeatBelowMinError (dp : DeployParams) :
    StorFixed dp heartbeatBelowMinError := StorFixed.of_inv (by func_inv)

theorem storFixed_heartbeatAboveMaxError (dp : DeployParams) :
    StorFixed dp heartbeatAboveMaxError := StorFixed.of_inv (by func_inv)

theorem storFixed_heartbeatExpiredError (dp : DeployParams) :
    StorFixed dp heartbeatExpiredError := StorFixed.of_inv (by func_inv)

/-! ## The two configuration setters

Each writes exactly one region-1 word.  Every other fragment of the walk —
the static-argument guard, the admin check, both bound checks, the event
staging and the terminal `STOP` — is storage-silent, and each failure arm
tail-jumps to a custom-error reverter. -/

theorem coherent_setPauseDuration (dp : DeployParams) :
    Coherent dp (setPauseDuration dp) := by
  unfold setPauseDuration requireStaticArgs onlyAdmin pushDeployWord
  refine Coherent.next (Coherent.next (Coherent.next
    (Coherent.branch ?_ (Coherent.of_storFixed StorFixed.rev))))
  refine Coherent.next (Coherent.next (Coherent.next
    (Coherent.branch (Coherent.call rfl
      (Coherent.of_storFixed (storFixed_senderNotAdminError dp))) ?_)))
  refine Coherent.next (Coherent.prepend (by line_inv) (Coherent.next
    (Coherent.branch ?_ (Coherent.call rfl
      (Coherent.of_storFixed (storFixed_pauseBelowMinError dp))))))
  refine Coherent.next (Coherent.prepend (by line_inv) (Coherent.next
    (Coherent.branch ?_ (Coherent.call rfl
      (Coherent.of_storFixed (storFixed_pauseAboveMaxError dp))))))
  refine Coherent.next (Coherent.next (Coherent.prepend (by line_inv)
    (Coherent.prepend (by line_inv) (Coherent.prepend (by line_inv)
      (Coherent.next (Coherent.prepend (by line_inv)
        (Coherent.prepend (by line_inv) ?_)))))))
  exact Coherent.pushSstore
    (fun _ _ hcoh => hcoh.config_set (payload := 0) zero_payload_lt)
    (StorFixed.last Linst.Hinv.inv)

theorem coherent_setHeartbeatInterval (dp : DeployParams) :
    Coherent dp (setHeartbeatInterval dp) := by
  unfold setHeartbeatInterval requireStaticArgs onlyAdmin pushDeployWord
  refine Coherent.next (Coherent.next (Coherent.next
    (Coherent.branch ?_ (Coherent.of_storFixed StorFixed.rev))))
  refine Coherent.next (Coherent.next (Coherent.next
    (Coherent.branch (Coherent.call rfl
      (Coherent.of_storFixed (storFixed_senderNotAdminError dp))) ?_)))
  refine Coherent.next (Coherent.prepend (by line_inv) (Coherent.next
    (Coherent.branch ?_ (Coherent.call rfl
      (Coherent.of_storFixed (storFixed_heartbeatBelowMinError dp))))))
  refine Coherent.next (Coherent.prepend (by line_inv) (Coherent.next
    (Coherent.branch ?_ (Coherent.call rfl
      (Coherent.of_storFixed (storFixed_heartbeatAboveMaxError dp))))))
  refine Coherent.next (Coherent.next (Coherent.prepend (by line_inv)
    (Coherent.prepend (by line_inv) (Coherent.prepend (by line_inv)
      (Coherent.next (Coherent.prepend (by line_inv)
        (Coherent.prepend (by line_inv) ?_)))))))
  exact Coherent.pushSstore
    (fun _ _ hcoh => hcoh.config_set (payload := 1) one_payload_lt)
    (StorFixed.last Linst.Hinv.inv)

/-! ## The heartbeat

The only persistent write is the caller's own expiry cell, in region 2.  Its
key is built on the stack by `CALLER; PUSH tag; OR`, and the caller is an
`Adr`, hence a canonical address; `RegistryWitness.expiry_set` is then the
disjointness fact. -/

/-- `arithmeticPanicSlot` is index 22, and `aux`'s twenty-second entry is the
`Panic(0x11)` reverter. -/
theorem get_arithmeticPanicSlot (dp : DeployParams) :
    ((runtime dp).main :: aux)[arithmeticPanicSlot]? =
      some (Func.revData
        ((signatureHash "Panic" [.uint256]).toBytes.take 4 ++
          (Nat.toB256 0x11).toBytes)) := rfl

theorem coherent_heartbeat (dp : DeployParams) : Coherent dp heartbeat := by
  unfold heartbeat checkedHeartbeatExpiry storeHeartbeatExpiryFromStack
  refine Coherent.next (Coherent.prepend (by line_inv) (Coherent.next
    (Coherent.next (Coherent.branch ?_ (Coherent.call rfl
      (Coherent.of_storFixed (storFixed_senderNotPauserError dp)))))))
  refine Coherent.next (Coherent.prepend (by line_inv) (Coherent.next
    (Coherent.next (Coherent.next (Coherent.branch (Coherent.call rfl
      (Coherent.of_storFixed (storFixed_heartbeatExpiredError dp))) ?_)))))
  refine Coherent.next (Coherent.next (Coherent.next (Coherent.next
    (Coherent.next (Coherent.next (Coherent.next (Coherent.next
      (Coherent.branch ?_ (Coherent.call (get_arithmeticPanicSlot dp)
        (Coherent.of_storFixed (storFixed_revData _)))))))))))
  refine Coherent.next (Coherent.next (Coherent.next ?_))
  exact Coherent.callerTagSstore
    (fun a _ _ hcoh => hcoh.expiry_set (canonicalAddress_toB256 a))
    (StorFixed.of_inv (by func_inv))

/-! ## The fifteen obligations

Twelve views go through `funcSound_of_storFixed`; the three writing endpoints
go through `funcSound_of_registryCore`.  Neither route consumes the
deeper-frame hypothesis. -/

theorem pauseDuration_funcSound (dp : DeployParams) (ca : Adr) :
    (registrySpec dp).FuncSound ca aux pauseDuration :=
  funcSound_of_storFixed (storFixed_pauseDuration dp)

theorem heartbeatInterval_funcSound (dp : DeployParams) (ca : Adr) :
    (registrySpec dp).FuncSound ca aux heartbeatInterval :=
  funcSound_of_storFixed (storFixed_heartbeatInterval dp)

theorem admin_funcSound (dp : DeployParams) (ca : Adr) :
    (registrySpec dp).FuncSound ca aux (admin dp) :=
  funcSound_of_storFixed (storFixed_returnDeployWord dp dp.admin)

theorem minPauseDuration_funcSound (dp : DeployParams) (ca : Adr) :
    (registrySpec dp).FuncSound ca aux (minPauseDuration dp) :=
  funcSound_of_storFixed (storFixed_returnDeployWord dp dp.minPauseDuration)

theorem maxPauseDuration_funcSound (dp : DeployParams) (ca : Adr) :
    (registrySpec dp).FuncSound ca aux (maxPauseDuration dp) :=
  funcSound_of_storFixed (storFixed_returnDeployWord dp dp.maxPauseDuration)

theorem minHeartbeatInterval_funcSound (dp : DeployParams) (ca : Adr) :
    (registrySpec dp).FuncSound ca aux (minHeartbeatInterval dp) :=
  funcSound_of_storFixed
    (storFixed_returnDeployWord dp dp.minHeartbeatInterval)

theorem maxHeartbeatInterval_funcSound (dp : DeployParams) (ca : Adr) :
    (registrySpec dp).FuncSound ca aux (maxHeartbeatInterval dp) :=
  funcSound_of_storFixed
    (storFixed_returnDeployWord dp dp.maxHeartbeatInterval)

theorem getPauser_funcSound (dp : DeployParams) (ca : Adr) :
    (registrySpec dp).FuncSound ca aux getPauser :=
  funcSound_of_storFixed (storFixed_getPauser dp)

theorem getPausableCount_funcSound (dp : DeployParams) (ca : Adr) :
    (registrySpec dp).FuncSound ca aux getPausableCount :=
  funcSound_of_storFixed (storFixed_getPausableCount dp)

theorem heartbeatExpiry_funcSound (dp : DeployParams) (ca : Adr) :
    (registrySpec dp).FuncSound ca aux heartbeatExpiry :=
  funcSound_of_storFixed (storFixed_heartbeatExpiry dp)

theorem isPauserLive_funcSound (dp : DeployParams) (ca : Adr) :
    (registrySpec dp).FuncSound ca aux isPauserLive :=
  funcSound_of_storFixed (storFixed_isPauserLive dp)

theorem getPausables_funcSound (dp : DeployParams) (ca : Adr) :
    (registrySpec dp).FuncSound ca aux getPausables :=
  funcSound_of_storFixed (storFixed_getPausables dp)

theorem heartbeat_funcSound (dp : DeployParams) (ca : Adr) :
    (registrySpec dp).FuncSound ca aux heartbeat :=
  funcSound_of_registryCore (coherent_heartbeat dp)

theorem setPauseDuration_funcSound (dp : DeployParams) (ca : Adr) :
    (registrySpec dp).FuncSound ca aux (setPauseDuration dp) :=
  funcSound_of_registryCore (coherent_setPauseDuration dp)

theorem setHeartbeatInterval_funcSound (dp : DeployParams) (ca : Adr) :
    (registrySpec dp).FuncSound ca aux (setHeartbeatInterval dp) :=
  funcSound_of_registryCore (coherent_setHeartbeatInterval dp)

/-! ## The dispatch list

`registerPauser` and `pause` are the two Registry-mutating targets; they are
not proved here.  The membership split is driven by `List.mem_cons`.  It must
not be driven by `decide`: deciding anything about these leaves forces the
`String.keccak` behind every `selector` and blows `maxRecDepth`. -/

/-- The whole dispatch list, given the two Registry-mutating obligations. -/
theorem funcSound_of_mem_funcs (dp : DeployParams) (ca : Adr)
    (hregister : (registrySpec dp).FuncSound ca aux (registerPauser dp))
    (hpause : (registrySpec dp).FuncSound ca aux pause)
    {p : B256 × Func} (hp : p ∈ funcs dp) :
    (registrySpec dp).FuncSound ca aux p.2 := by
  simp only [funcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h <;> (cases h)
  · exact pauseDuration_funcSound dp ca
  · exact maxPauseDuration_funcSound dp ca
  · exact admin_funcSound dp ca
  · exact hregister
  · exact heartbeat_funcSound dp ca
  · exact getPauser_funcSound dp ca
  · exact getPausables_funcSound dp ca
  · exact heartbeatInterval_funcSound dp ca
  · exact setHeartbeatInterval_funcSound dp ca
  · exact hpause
  · exact minPauseDuration_funcSound dp ca
  · exact maxHeartbeatInterval_funcSound dp ca
  · exact getPausableCount_funcSound dp ca
  · exact minHeartbeatInterval_funcSound dp ca
  · exact heartbeatExpiry_funcSound dp ca
  · exact setPauseDuration_funcSound dp ca
  · exact isPauserLive_funcSound dp ca

/-- The same fifteen rows, stated as an exclusion instead of as hypotheses. -/
theorem funcSound_of_mem_nonRegistry (dp : DeployParams) (ca : Adr)
    {p : B256 × Func} (hp : p ∈ funcs dp)
    (hreg : p.2 ≠ registerPauser dp) (hpause : p.2 ≠ pause) :
    (registrySpec dp).FuncSound ca aux p.2 := by
  simp only [funcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h <;> (cases h)
  · exact pauseDuration_funcSound dp ca
  · exact maxPauseDuration_funcSound dp ca
  · exact admin_funcSound dp ca
  · exact absurd rfl hreg
  · exact heartbeat_funcSound dp ca
  · exact getPauser_funcSound dp ca
  · exact getPausables_funcSound dp ca
  · exact heartbeatInterval_funcSound dp ca
  · exact setHeartbeatInterval_funcSound dp ca
  · exact absurd rfl hpause
  · exact minPauseDuration_funcSound dp ca
  · exact maxHeartbeatInterval_funcSound dp ca
  · exact getPausableCount_funcSound dp ca
  · exact minHeartbeatInterval_funcSound dp ca
  · exact heartbeatExpiry_funcSound dp ca
  · exact setPauseDuration_funcSound dp ca
  · exact isPauserLive_funcSound dp ca

end LidoCircuitBreaker

end Blanc
