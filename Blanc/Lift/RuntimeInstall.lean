import Blanc.Lift.HistCreate
import Blanc.Lift.CreationOps
import Blanc.BytesWrite

/-!
# Installing a referenced runtime from a PUSH0 constructor

Contract-neutral steps for a constructor that ends `PUSH len; DUP1; PUSH offset; PUSH0; CODECOPY;
PUSH0; RETURN`, as `geas`-assembled system contracts do, over a creation input that is a prefix
followed by one reference to a registered runtime: the code window, the terminal walk, and the
settled account after `processCreateMessage`.
-/

namespace Blanc.Lift

open Jaune

/-- The runtime window of a creation input that is a prefix followed by the runtime. -/
theorem creation_runtime_window (pre : Bytes) (runtime : ByteArray) :
    (⟨(pre ++ runtime.toList).toArray⟩ : ByteArray).sliceD pre.length runtime.toList.length 0 =
      runtime.toList := by
  rw [ByteArray.sliceD_eq, ByteArray.toList_eq_toList_data, List.toList_toArray]
  simpa only [List.append_nil] using Bytes.sliceD_append_middle pre runtime.toList []

/-- The terminal copy and return of a PUSH0 constructor, from empty memory. -/
theorem push0RuntimeReturn_runExact
    {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {G : Nat}
    {sizeHead offsetHead : UInt8} {sizeTail offsetTail : Bytes}
    {sizeBound : (sizeHead :: sizeTail).length ≤ 32}
    {offsetBound : (offsetHead :: offsetTail).length ≤ 32}
    {le0 le1 : ([] : Bytes).length ≤ 32} {size offset : B256}
    (hpush0 : sevm.benvStat.rules.op.push0 = true)
    (sizeWord : Bytes.toB256 (sizeHead :: sizeTail) = size)
    (offsetWord : Bytes.toB256 (offsetHead :: offsetTail) = offset)
    (nonzero : size.toNat ≠ 0) (room : S.length + 4 ≤ 1024) :
    SFunc.RunExact fs sevm
      (St b S Mem.empty (G + 2 + (3 + gasCopy * ceilDiv size.toNat 32 +
        calculateMemoryGasCost (memExtSize 0 0 size.toNat)) + 2 + 3 + 3 + 3))
      (.next (.push (sizeHead :: sizeTail) sizeBound) (.next (.reg (.dup 0))
        (.next (.push (offsetHead :: offsetTail) offsetBound) (.next (.push [] le0)
          (.next (.reg .codecopy) (.next (.push [] le1) (.last .return_)))))))
      (.halted ((St b S
        (Mem.empty.write 0 (sevm.code.sliceD offset.toNat size.toNat (Linst.toUInt8 .stop))) G).withOutput
        (sevm.code.sliceD offset.toNat size.toNat (Linst.toUInt8 .stop)))) := by
  let window := sevm.code.sliceD offset.toNat size.toNat (Linst.toUInt8 .stop)
  let copied := Mem.empty.write 0 window
  have length : window.length = size.toNat := ByteArray.length_sliceD _ _ _ _
  have nonempty : window ≠ [] := by
    intro empty
    apply nonzero
    rw [empty] at length
    exact length.symm
  have memorySize : copied.size = memExtSize 0 0 size.toNat :=
    Mem.size_write_of_size rfl (by decide) length
  have memoryAligned : copied.size % 32 = 0 := by
    rw [memorySize]
    exact memExtSize_mod_32 (by decide)
  have fits : 0 + size.toNat ≤ copied.size := by
    have bound := Mem.write_end_le_size Mem.empty 0 nonempty
    rw [length] at bound
    exact bound
  have read : (copied.read 0 size.toNat).1 = window := by
    change ((Mem.empty.write 0 window).read 0 size.toNat).1 = window
    rw [← length]
    exact Mem.read_write_zero Mem.empty nonempty
  have memory : (copied.read 0 size.toNat).2 = copied :=
    Mem.read_snd_eq_self (memExtSize_of_le memoryAligned fits)
  have post : returnPost (St b (0 :: size :: S) copied G) 0 size S =
      (St b S copied G).withOutput window := by
    change ((St b S copied G).withMemory (copied.read 0 size.toNat).2).withOutput
      (copied.read 0 size.toNat).1 = _
    rw [memory, read]
    rfl
  change SFunc.RunExact fs sevm _ _ (.halted ((St b S copied G).withOutput window))
  rw [← post]
  apply rx_push sizeWord (by omega)
  apply rx_dup (n := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_push offsetWord (by simp only [List.length_cons]; omega)
  apply rx_push0 hpush0 (by simp only [List.length_cons]; omega)
  refine rx_codecopy (G := G + 2)
    (c := 3 + gasCopy * ceilDiv size.toNat 32 + calculateMemoryGasCost (memExtSize 0 0 size.toNat))
    (M' := copied) ?_ rfl ?_
  · rw [St.extCost_eq rfl]
    rfl
  · apply rx_push0 hpush0 (by simp only [List.length_cons]; omega)
    have hx : memExtSize copied.size (0 : B256).toNat size.toNat = copied.size :=
      memExtSize_of_le memoryAligned fits
    exact rx_return_any rfl (by rw [St.extCost_eq rfl, hx, Nat.sub_self])

/-- The covered forks' code-size limit. -/
theorem covered_maxCodeSize {s : BenvStat} (hfork : CoveredFork s.fork) :
    s.rules.code.maxCodeSize = 24576 :=
  hfork.cases (motive := fun f => (Fork.ruleSet f).code.maxCodeSize = 24576) rfl rfl rfl rfl

/-- Creation entry bumps the target's nonce by one. -/
theorem processCreateMessage_msg_nonce (msg : Msg) :
    ((processCreateMessage.msg msg).benv.state.get msg.currentTarget).nonce =
      (msg.benv.state.get msg.currentTarget).nonce + 1 := by
  change (((msg.benv.state.setStor msg.currentTarget .empty).incrNonce
    msg.currentTarget).get msg.currentTarget).nonce = _
  unfold State.incrNonce
  dsimp only
  rw [State.setAccount_get_self, Acct.clearIfEmpty_nonce]
  unfold State.setStor
  dsimp only
  split
  · rw [State.get_setPresent_self]
  · rw [State.get_set_self]

/-- `SSTORE` under historical rules keeps the account's nonce. -/
theorem afterSstoreH_nonce (sevm : Sevm) (base : Devm) (key value : B256) :
    ((afterSstoreH sevm base key value).state.get sevm.currentTarget).nonce =
      (base.state.get sevm.currentTarget).nonce := by
  have hstate : (storageAccessH sevm base key).state = base.state := by
    unfold storageAccessH
    split
    · rfl
    · split <;> rfl
  unfold afterSstoreH
  change ((((storageAccessH sevm base key).state).setStorVal sevm.currentTarget key value).get
    sevm.currentTarget).nonce = _
  rw [hstate]
  unfold State.setStorVal
  dsimp only
  split
  · rw [State.get_setPresent_self]
  · rw [State.get_set_self]

theorem byteArray_of_toList (r : ByteArray) : (⟨⟨r.toList⟩⟩ : ByteArray) = r := by
  rw [ByteArray.toList_eq_toList_data]

/-- A checked constructor run that returns the referenced runtime installs it: the settled target
holds the runtime, the run's storage and the run's nonce. No storage or code outcome is assumed. -/
theorem install_of_run {code : ByteArray} {c : Cert}
    (hc : Cert.check code c = true) (hj : Cert.jumpsOk code c = true) {runtime : ByteArray}
    (msg : Msg) (hcodeAddress : msg.codeAddress = none) (hcode : msg.code = code)
    (hsg : msg.benv.stat.rules.stateGas = none) (hvalue : msg.value = 0) {raw : Devm}
    (hrun : SProg.RunExact c.prog (initSevm (processCreateMessage.msg msg))
      (initDevm (processCreateMessage.msg msg)) raw)
    (herror : raw.error = none) (houtput : raw.output = runtime.toList)
    (hne : runtime.toList ≠ []) (hprefix : runtime.toList.head? ≠ some 0xEF)
    (hdeposit : runtime.toList.length * gasCodeDeposit ≤ raw.gasLeft)
    (hmax : runtime.toList.length ≤ msg.benv.stat.rules.code.maxCodeSize) :
    ∃ post, processCreateMessage msg = .ok post ∧ post.error = none ∧
      post.getCode msg.currentTarget = runtime ∧
      post.getStor msg.currentTarget = raw.getStor msg.currentTarget ∧
      (post.state.get msg.currentTarget).nonce = (raw.state.get msg.currentTarget).nonce := by
  have hvalue0 : (processCreateMessage.msg msg).value = 0 := hvalue
  have htransfer := Msg.benvAfterTransfer_of_value_zero hvalue0
  have hpost := liftCreate_postH hc hj msg hcodeAddress hcode hsg htransfer hrun herror
    (by rw [houtput]; exact hprefix) (by rw [houtput]; exact hdeposit)
    (by rw [houtput]; exact hmax)
  have facts := liftCreatePost_facts msg.currentTarget
    (raw.recordTouch msg.benv.stat.rules true msg.currentTarget)
  have hget := facts.2.2.1
  rw [Devm.recordTouch_state, Devm.recordTouch_output, houtput] at hget
  refine ⟨_, hpost, facts.1.trans ((Devm.recordTouch_error _ _ _ _).trans herror), ?_, ?_, ?_⟩
  · unfold Devm.getCode Devm.getAcct
    rw [hget, Acct.clearIfEmpty_code]
    exact byteArray_of_toList runtime
  · have hsize : (⟨⟨runtime.toList⟩⟩ : ByteArray).size ≠ 0 := by
      show (List.toArray runtime.toList).size ≠ 0
      rw [List.size_toArray]
      exact fun h => hne (List.length_eq_zero_iff.mp h)
    have hnotempty : ¬ ({ raw.state.get msg.currentTarget with
        code := ⟨⟨runtime.toList⟩⟩ } : Acct).Empty := fun hacc => hsize hacc.1
    unfold Devm.getStor Devm.getAcct
    rw [hget, Acct.clearIfEmpty_stor, ite_eq_right hnotempty]
  · rw [hget, Acct.clearIfEmpty_nonce]

end Blanc.Lift
