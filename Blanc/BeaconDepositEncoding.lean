import Blanc.BeaconDepositCore
import Blanc.BytesWrite

/-!
# Beacon deposit ABI encoding facts

Loop-independent selector, interface, calldata, return, and event identities
for Blanc's BeaconDeposit artifact.
-/

namespace Blanc.BeaconDeposit

open Jaune

/-! ## Pinned selectors, topic, and interface identifiers -/

theorem supportsInterfaceSelector_eq :
    supportsInterfaceSelector = (0x01ffc9a7 : B256) := by
  decide +kernel

theorem depositSelector_eq :
    depositSelector = (0x22895118 : B256) := by
  decide +kernel

theorem getDepositCountSelector_eq :
    getDepositCountSelector = (0x621fd130 : B256) := by
  decide +kernel

theorem getDepositRootSelector_eq :
    getDepositRootSelector = (0xc5f2892f : B256) := by
  decide +kernel

theorem beaconSelectors_eq_literals :
    beaconSelectors =
      [(0x01ffc9a7 : B256), 0x22895118, 0x621fd130, 0xc5f2892f] := by
  decide +kernel

theorem beaconSelectors_pairwise :
    beaconSelectors.Pairwise (fun left right => left < right) := by
  decide +kernel

theorem depositEventTopic_eq :
    depositEventTopic =
      (0x649bbc62d0e31342afea4e5cd82d4049e7e1ee912fc0889aa790803be39038c5 :
        B256) := by
  decide +kernel

theorem erc165InterfaceIdBytes_length : erc165InterfaceIdBytes.length = 4 := by
  decide +kernel

theorem depositInterfaceIdBytes_length :
    depositInterfaceIdBytes.length = 4 := by
  decide +kernel

theorem erc165InterfaceIdBytes_toB256 :
    Bytes.toB256 erc165InterfaceIdBytes = erc165InterfaceId := by
  decide +kernel

theorem depositInterfaceIdBytes_toB256 :
    Bytes.toB256 depositInterfaceIdBytes = depositInterfaceId := by
  decide +kernel

theorem erc165InterfaceId_abiBytes :
    abiSelectorBytes erc165InterfaceId = erc165InterfaceIdBytes := by
  decide +kernel

theorem depositInterfaceId_abiBytes :
    abiSelectorBytes depositInterfaceId = depositInterfaceIdBytes := by
  decide +kernel

/-! ## Small ABI length and read lemmas -/

theorem abiBytesTail_length (data : Bytes) :
    (abiBytesTail data).length = 32 + ceil32 data.length := by
  simp only [abiBytesTail, List.length_append, B256.length_toBytes,
    List.length_replicate]
  have hle := Nat.le_ceil32 data.length
  omega

theorem canonicalSupportsInterfaceCalldata_length
    {data interfaceId : Bytes}
    (h : CanonicalSupportsInterfaceCalldata data interfaceId) :
    data.length = 36 := by
  rcases h with ⟨hlen, rfl⟩
  simp [abiSupportsInterfaceCall, abiSelectorBytes_length, hlen]

theorem canonicalSupportsInterfaceCalldata_bytes4
    {data interfaceId : Bytes}
    (h : CanonicalSupportsInterfaceCalldata data interfaceId) :
    data.sliceD 4 4 0 = interfaceId := by
  rcases h with ⟨hlen, rfl⟩
  unfold abiSupportsInterfaceCall
  rw [List.append_assoc, List.sliceD,
    List.drop_length_append' (abiSelectorBytes_length _).symm,
    List.takeD_eq_take _ (by simp [hlen]),
    List.take_length_append' hlen.symm]

theorem canonicalSupportsInterfaceCalldata_word
    {data interfaceId : Bytes}
    (h : CanonicalSupportsInterfaceCalldata data interfaceId) :
    calldataWord data 4 =
      Bytes.toB256 (interfaceId ++ List.replicate 28 0) := by
  rcases h with ⟨hlen, rfl⟩
  unfold calldataWord abiSupportsInterfaceCall
  apply congrArg Bytes.toB256
  rw [List.append_assoc, List.sliceD,
    List.drop_length_append' (abiSelectorBytes_length _).symm,
    List.takeD_eq_take _ (by simp [hlen]),
    List.take_of_length_le (by simp [hlen])]
  simp [hlen]

/-! ## Dynamic return and event images -/

theorem abiDynamicBytesReturn_le64_eq (n : Nat) :
    abiDynamicBytesReturn (le64 n) =
      (32 : B256).toBytes ++ (8 : B256).toBytes ++
        le64 n ++ List.replicate 24 0 := by
  simp [abiDynamicBytesReturn, abiBytesTail, le64, ceil32,
    List.append_assoc]
  decide +kernel

theorem abiDynamicBytesReturn_le64_length (n : Nat) :
    (abiDynamicBytesReturn (le64 n)).length = 96 := by
  rw [abiDynamicBytesReturn_le64_eq]
  simp [le64, B256.length_toBytes]

theorem abiDepositEvent_mk
    (pubkey withdrawalCredentials amount signature index : Bytes) :
    abiDepositEvent
        ⟨pubkey, withdrawalCredentials, amount, signature, index⟩ =
      (160 : B256).toBytes ++
      (256 : B256).toBytes ++
      (320 : B256).toBytes ++
      (384 : B256).toBytes ++
      (512 : B256).toBytes ++
      abiBytesTail pubkey ++
      abiBytesTail withdrawalCredentials ++
      abiBytesTail amount ++
      abiBytesTail signature ++
      abiBytesTail index := by
  rfl

theorem abiDepositEvent_length
    (event : DepositEvent)
    (hpubkey : event.pubkey.length = 48)
    (hwithdrawal : event.withdrawal_credentials.length = 32)
    (hamount : event.amount.length = 8)
    (hsignature : event.signature.length = 96)
    (hindex : event.index.length = 8) :
    (abiDepositEvent event).length = 576 := by
  simp only [abiDepositEvent, List.length_append, B256.length_toBytes,
    abiBytesTail_length]
  rw [hpubkey, hwithdrawal, hamount, hsignature, hindex]
  decide +kernel

/-- The canonical event image specialized to the five fixed widths used by
the deposit contract. -/
theorem abiDepositEvent_fixed_layout
    (event : DepositEvent)
    (hpubkey : event.pubkey.length = 48)
    (hwithdrawal : event.withdrawal_credentials.length = 32)
    (hamount : event.amount.length = 8)
    (hsignature : event.signature.length = 96)
    (hindex : event.index.length = 8) :
    abiDepositEvent event =
      (160 : B256).toBytes ++ (256 : B256).toBytes ++
        (320 : B256).toBytes ++ (384 : B256).toBytes ++
          (512 : B256).toBytes ++ (48 : B256).toBytes ++
            event.pubkey ++ zeros 16 ++ (32 : B256).toBytes ++
              event.withdrawal_credentials ++ (8 : B256).toBytes ++
                event.amount ++ zeros 24 ++ (96 : B256).toBytes ++
                  event.signature ++ (8 : B256).toBytes ++ event.index ++
                    zeros 24 := by
  have hpubkeyTail : abiBytesTail event.pubkey =
      (48 : B256).toBytes ++ event.pubkey ++ zeros 16 := by
    rw [abiBytesTail, hpubkey]
    simp [ceil32, zeros]
    decide +kernel
  have hwithdrawalTail : abiBytesTail event.withdrawal_credentials =
      (32 : B256).toBytes ++ event.withdrawal_credentials := by
    rw [abiBytesTail, hwithdrawal]
    simp [ceil32]
    decide +kernel
  have hamountTail : abiBytesTail event.amount =
      (8 : B256).toBytes ++ event.amount ++ zeros 24 := by
    rw [abiBytesTail, hamount]
    simp [ceil32, zeros]
    decide +kernel
  have hsignatureTail : abiBytesTail event.signature =
      (96 : B256).toBytes ++ event.signature := by
    rw [abiBytesTail, hsignature]
    simp [ceil32]
    decide +kernel
  have hindexTail : abiBytesTail event.index =
      (8 : B256).toBytes ++ event.index ++ zeros 24 := by
    rw [abiBytesTail, hindex]
    simp [ceil32, zeros]
    decide +kernel
  simp only [abiDepositEvent, hpubkeyTail, hwithdrawalTail, hamountTail,
    hsignatureTail, hindexTail, List.append_assoc]

/-- The first reconstruction hash input is the padded pubkey payload inside
the canonical fixed-width event image. -/
theorem abiDepositEvent_pubkeyInput_read
    (event : DepositEvent)
    (hpubkey : event.pubkey.length = 48)
    (hwithdrawal : event.withdrawal_credentials.length = 32)
    (hamount : event.amount.length = 8)
    (hsignature : event.signature.length = 96)
    (hindex : event.index.length = 8) :
    (abiDepositEvent event).sliceD 192 64 0 =
      event.pubkey ++ zeros 16 := by
  rw [abiDepositEvent_fixed_layout event hpubkey hwithdrawal hamount
    hsignature hindex]
  let pre : Bytes :=
    (160 : B256).toBytes ++ (256 : B256).toBytes ++
      (320 : B256).toBytes ++ (384 : B256).toBytes ++
        (512 : B256).toBytes ++ (48 : B256).toBytes
  let middle : Bytes := event.pubkey ++ zeros 16
  let post : Bytes :=
    (32 : B256).toBytes ++ event.withdrawal_credentials ++
      (8 : B256).toBytes ++ event.amount ++ zeros 24 ++
        (96 : B256).toBytes ++ event.signature ++
          (8 : B256).toBytes ++ event.index ++ zeros 24
  have h := Bytes.sliceD_append_middle pre middle post
  have hpre : pre.length = 192 := by
    simp [pre, B256.length_toBytes]
  have hmiddle : middle.length = 64 := by
    simp [middle, hpubkey, zeros]
  rw [hpre, hmiddle] at h
  simpa only [pre, middle, post, List.append_assoc] using h

/-- The withdrawal-credentials reconstruction word inside the canonical
fixed-width event image. -/
theorem abiDepositEvent_withdrawal_read
    (event : DepositEvent)
    (hpubkey : event.pubkey.length = 48)
    (hwithdrawal : event.withdrawal_credentials.length = 32)
    (hamount : event.amount.length = 8)
    (hsignature : event.signature.length = 96)
    (hindex : event.index.length = 8) :
    (abiDepositEvent event).sliceD 288 32 0 =
      event.withdrawal_credentials := by
  rw [abiDepositEvent_fixed_layout event hpubkey hwithdrawal hamount
    hsignature hindex]
  let pre : Bytes :=
    (160 : B256).toBytes ++ (256 : B256).toBytes ++
      (320 : B256).toBytes ++ (384 : B256).toBytes ++
        (512 : B256).toBytes ++ (48 : B256).toBytes ++
          event.pubkey ++ zeros 16 ++ (32 : B256).toBytes
  let middle : Bytes := event.withdrawal_credentials
  let post : Bytes :=
    (8 : B256).toBytes ++ event.amount ++ zeros 24 ++
      (96 : B256).toBytes ++ event.signature ++
        (8 : B256).toBytes ++ event.index ++ zeros 24
  have h := Bytes.sliceD_append_middle pre middle post
  have hpre : pre.length = 288 := by
    simp [pre, B256.length_toBytes, hpubkey, zeros]
  have hmiddle : middle.length = 32 := by
    simpa only [middle] using hwithdrawal
  rw [hpre, hmiddle] at h
  simpa only [pre, middle, post, List.append_assoc] using h

/-- The little-endian amount and its zero padding inside the canonical
fixed-width event image. -/
theorem abiDepositEvent_amountPadded_read
    (event : DepositEvent)
    (hpubkey : event.pubkey.length = 48)
    (hwithdrawal : event.withdrawal_credentials.length = 32)
    (hamount : event.amount.length = 8)
    (hsignature : event.signature.length = 96)
    (hindex : event.index.length = 8) :
    (abiDepositEvent event).sliceD 352 32 0 =
      event.amount ++ zeros 24 := by
  rw [abiDepositEvent_fixed_layout event hpubkey hwithdrawal hamount
    hsignature hindex]
  let pre : Bytes :=
    (160 : B256).toBytes ++ (256 : B256).toBytes ++
      (320 : B256).toBytes ++ (384 : B256).toBytes ++
        (512 : B256).toBytes ++ (48 : B256).toBytes ++
          event.pubkey ++ zeros 16 ++ (32 : B256).toBytes ++
            event.withdrawal_credentials ++ (8 : B256).toBytes
  let middle : Bytes := event.amount ++ zeros 24
  let post : Bytes :=
    (96 : B256).toBytes ++ event.signature ++
      (8 : B256).toBytes ++ event.index ++ zeros 24
  have h := Bytes.sliceD_append_middle pre middle post
  have hpre : pre.length = 352 := by
    simp [pre, B256.length_toBytes, hpubkey, hwithdrawal, zeros]
  have hmiddle : middle.length = 32 := by
    simp [middle, hamount, zeros]
  rw [hpre, hmiddle] at h
  simpa only [pre, middle, post, List.append_assoc] using h

/-- The complete signature payload inside the canonical fixed-width event
image. -/
theorem abiDepositEvent_signature_read
    (event : DepositEvent)
    (hpubkey : event.pubkey.length = 48)
    (hwithdrawal : event.withdrawal_credentials.length = 32)
    (hamount : event.amount.length = 8)
    (hsignature : event.signature.length = 96)
    (hindex : event.index.length = 8) :
    (abiDepositEvent event).sliceD 416 96 0 = event.signature := by
  rw [abiDepositEvent_fixed_layout event hpubkey hwithdrawal hamount
    hsignature hindex]
  let pre : Bytes :=
    (160 : B256).toBytes ++ (256 : B256).toBytes ++
      (320 : B256).toBytes ++ (384 : B256).toBytes ++
        (512 : B256).toBytes ++ (48 : B256).toBytes ++
          event.pubkey ++ zeros 16 ++ (32 : B256).toBytes ++
            event.withdrawal_credentials ++ (8 : B256).toBytes ++
              event.amount ++ zeros 24 ++ (96 : B256).toBytes
  let middle : Bytes := event.signature
  let post : Bytes :=
    (8 : B256).toBytes ++ event.index ++ zeros 24
  have h := Bytes.sliceD_append_middle pre middle post
  have hpre : pre.length = 416 := by
    simp [pre, B256.length_toBytes, hpubkey, hwithdrawal, hamount, zeros]
  have hmiddle : middle.length = 96 := by
    simpa only [middle] using hsignature
  rw [hpre, hmiddle] at h
  simpa only [pre, middle, post, List.append_assoc] using h

/-! ## Canonical deposit calldata round-trip -/

private theorem calldataWord_append_word
    (pre post : Bytes) (word : B256) :
    calldataWord (pre ++ word.toBytes ++ post) pre.length = word := by
  simp only [calldataWord, List.sliceD]
  rw [List.append_assoc,
    List.drop_length_append' rfl,
    List.takeD_eq_take _ (by simp [B256.length_toBytes]),
    List.take_length_append' (B256.length_toBytes word).symm,
    B256.toB256_toBytes]

private theorem calldataWord_append_abiBytesTail
    (pre data post : Bytes) :
    calldataWord (pre ++ abiBytesTail data ++ post) pre.length =
      Nat.toB256 data.length := by
  simp only [calldataWord, abiBytesTail, List.sliceD]
  rw [List.append_assoc,
    List.drop_length_append' rfl,
    List.append_assoc, List.append_assoc,
    List.takeD_eq_take _ (by simp [B256.length_toBytes]),
    List.take_length_append'
      (B256.length_toBytes (Nat.toB256 data.length)).symm,
    B256.toB256_toBytes]

private theorem sliceD_append_abiBytesTail
    (pre data post : Bytes) :
    (pre ++ abiBytesTail data ++ post).sliceD
      (pre.length + 32) data.length 0 = data := by
  convert Bytes.sliceD_append_middle
    (pre ++ (Nat.toB256 data.length).toBytes)
    data
    (List.replicate (ceil32 data.length - data.length) 0 ++ post) using 1
  all_goals simp [abiBytesTail, List.append_assoc, B256.length_toBytes]

private def depositCallHead
    (pubkey withdrawalCredentials : Bytes)
    (depositDataRoot : B256) : Bytes :=
  abiSelectorBytes depositSelector ++
    (Nat.toB256 firstDepositTailOffset).toBytes ++
    (Nat.toB256 (secondDepositTailOffset pubkey)).toBytes ++
    (Nat.toB256
      (thirdDepositTailOffset pubkey withdrawalCredentials)).toBytes ++
    depositDataRoot.toBytes

private theorem depositCallHead_length
    (pubkey withdrawalCredentials : Bytes)
    (depositDataRoot : B256) :
    (depositCallHead pubkey withdrawalCredentials depositDataRoot).length =
      132 := by
  simp [depositCallHead, abiSelectorBytes_length, B256.length_toBytes]

private theorem abiDepositCall_eq_head_tails
    (pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256) :
    abiDepositCall pubkey withdrawalCredentials signature depositDataRoot =
      depositCallHead pubkey withdrawalCredentials depositDataRoot ++
        abiBytesTail pubkey ++ abiBytesTail withdrawalCredentials ++
        abiBytesTail signature := by
  rfl

private theorem abiDepositCall_offsetWord_zero
    (pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256) :
    calldataWord
        (abiDepositCall pubkey withdrawalCredentials signature depositDataRoot)
        4 =
      Nat.toB256 firstDepositTailOffset := by
  simpa [abiDepositCall, List.append_assoc, abiSelectorBytes_length] using
    calldataWord_append_word
      (abiSelectorBytes depositSelector)
      ((Nat.toB256 (secondDepositTailOffset pubkey)).toBytes ++
        (Nat.toB256
          (thirdDepositTailOffset pubkey withdrawalCredentials)).toBytes ++
        depositDataRoot.toBytes ++ abiBytesTail pubkey ++
        abiBytesTail withdrawalCredentials ++ abiBytesTail signature)
      (Nat.toB256 firstDepositTailOffset)

private theorem abiDepositCall_offsetWord_one
    (pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256) :
    calldataWord
        (abiDepositCall pubkey withdrawalCredentials signature depositDataRoot)
        36 =
      Nat.toB256 (secondDepositTailOffset pubkey) := by
  simpa [abiDepositCall, List.append_assoc, abiSelectorBytes_length,
      B256.length_toBytes] using
    calldataWord_append_word
      (abiSelectorBytes depositSelector ++
        (Nat.toB256 firstDepositTailOffset).toBytes)
      ((Nat.toB256
          (thirdDepositTailOffset pubkey withdrawalCredentials)).toBytes ++
        depositDataRoot.toBytes ++ abiBytesTail pubkey ++
        abiBytesTail withdrawalCredentials ++ abiBytesTail signature)
      (Nat.toB256 (secondDepositTailOffset pubkey))

private theorem abiDepositCall_offsetWord_two
    (pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256) :
    calldataWord
        (abiDepositCall pubkey withdrawalCredentials signature depositDataRoot)
        68 =
      Nat.toB256
        (thirdDepositTailOffset pubkey withdrawalCredentials) := by
  simpa [abiDepositCall, List.append_assoc, abiSelectorBytes_length,
      B256.length_toBytes] using
    calldataWord_append_word
      (abiSelectorBytes depositSelector ++
        (Nat.toB256 firstDepositTailOffset).toBytes ++
        (Nat.toB256 (secondDepositTailOffset pubkey)).toBytes)
      (depositDataRoot.toBytes ++ abiBytesTail pubkey ++
        abiBytesTail withdrawalCredentials ++ abiBytesTail signature)
      (Nat.toB256
        (thirdDepositTailOffset pubkey withdrawalCredentials))

private theorem abiDepositCall_rootWord
    (pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256) :
    calldataWord
        (abiDepositCall pubkey withdrawalCredentials signature depositDataRoot)
        100 =
      depositDataRoot := by
  simpa [abiDepositCall, List.append_assoc, abiSelectorBytes_length,
      B256.length_toBytes] using
    calldataWord_append_word
      (abiSelectorBytes depositSelector ++
        (Nat.toB256 firstDepositTailOffset).toBytes ++
        (Nat.toB256 (secondDepositTailOffset pubkey)).toBytes ++
        (Nat.toB256
          (thirdDepositTailOffset pubkey withdrawalCredentials)).toBytes)
      (abiBytesTail pubkey ++ abiBytesTail withdrawalCredentials ++
        abiBytesTail signature)
      depositDataRoot

private theorem abiDepositCall_lengthWord_zero
    (pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256) :
    calldataWord
        (abiDepositCall pubkey withdrawalCredentials signature depositDataRoot)
        132 =
      Nat.toB256 pubkey.length := by
  rw [abiDepositCall_eq_head_tails]
  simpa [depositCallHead_length, List.append_assoc] using
    calldataWord_append_abiBytesTail
      (depositCallHead pubkey withdrawalCredentials depositDataRoot)
      pubkey
      (abiBytesTail withdrawalCredentials ++ abiBytesTail signature)

private theorem abiDepositCall_lengthWord_one
    (pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256) :
    calldataWord
        (abiDepositCall pubkey withdrawalCredentials signature depositDataRoot)
        (4 + secondDepositTailOffset pubkey) =
      Nat.toB256 withdrawalCredentials.length := by
  rw [abiDepositCall_eq_head_tails]
  have hpre :
      (depositCallHead pubkey withdrawalCredentials depositDataRoot ++
        abiBytesTail pubkey).length =
        4 + secondDepositTailOffset pubkey := by
    simp only [List.length_append, depositCallHead_length,
      abiBytesTail_length, secondDepositTailOffset,
      firstDepositTailOffset]
    omega
  have hword := calldataWord_append_abiBytesTail
      (depositCallHead pubkey withdrawalCredentials depositDataRoot ++
        abiBytesTail pubkey)
      withdrawalCredentials
      (abiBytesTail signature)
  rw [hpre] at hword
  simpa only [List.append_assoc] using hword

private theorem abiDepositCall_lengthWord_two
    (pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256) :
    calldataWord
        (abiDepositCall pubkey withdrawalCredentials signature depositDataRoot)
        (4 + thirdDepositTailOffset pubkey withdrawalCredentials) =
      Nat.toB256 signature.length := by
  rw [abiDepositCall_eq_head_tails]
  have hpre :
      (depositCallHead pubkey withdrawalCredentials depositDataRoot ++
        abiBytesTail pubkey ++ abiBytesTail withdrawalCredentials).length =
        4 + thirdDepositTailOffset pubkey withdrawalCredentials := by
    simp only [List.length_append, depositCallHead_length,
      abiBytesTail_length, thirdDepositTailOffset,
      secondDepositTailOffset, firstDepositTailOffset]
    omega
  have hword := calldataWord_append_abiBytesTail
      (depositCallHead pubkey withdrawalCredentials depositDataRoot ++
        abiBytesTail pubkey ++ abiBytesTail withdrawalCredentials)
      signature
      []
  rw [hpre] at hword
  simpa only [List.append_nil] using hword

private theorem abiDepositCall_payload_zero
    (pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256)
    (hoffset : dynamicOffset
      (abiDepositCall pubkey withdrawalCredentials signature depositDataRoot)
      0 = firstDepositTailOffset)
    (hlength : dynamicLength
      (abiDepositCall pubkey withdrawalCredentials signature depositDataRoot)
      0 = pubkey.length) :
    dynamicPayload
        (abiDepositCall pubkey withdrawalCredentials signature depositDataRoot)
        0 =
      pubkey := by
  unfold dynamicPayload
  rw [hoffset, hlength, abiDepositCall_eq_head_tails]
  simpa [depositCallHead_length, firstDepositTailOffset,
      List.append_assoc] using
    sliceD_append_abiBytesTail
      (depositCallHead pubkey withdrawalCredentials depositDataRoot)
      pubkey
      (abiBytesTail withdrawalCredentials ++ abiBytesTail signature)

private theorem abiDepositCall_payload_one
    (pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256)
    (hoffset : dynamicOffset
      (abiDepositCall pubkey withdrawalCredentials signature depositDataRoot)
      1 = secondDepositTailOffset pubkey)
    (hlength : dynamicLength
      (abiDepositCall pubkey withdrawalCredentials signature depositDataRoot)
      1 = withdrawalCredentials.length) :
    dynamicPayload
        (abiDepositCall pubkey withdrawalCredentials signature depositDataRoot)
        1 =
      withdrawalCredentials := by
  unfold dynamicPayload
  rw [hoffset, hlength, abiDepositCall_eq_head_tails]
  have hstart :
      (depositCallHead pubkey withdrawalCredentials depositDataRoot ++
        abiBytesTail pubkey).length + 32 =
        36 + secondDepositTailOffset pubkey := by
    simp only [List.length_append, depositCallHead_length,
      abiBytesTail_length, secondDepositTailOffset,
      firstDepositTailOffset]
    omega
  have hpayload := sliceD_append_abiBytesTail
      (depositCallHead pubkey withdrawalCredentials depositDataRoot ++
        abiBytesTail pubkey)
      withdrawalCredentials
      (abiBytesTail signature)
  rw [hstart] at hpayload
  simpa only [List.append_assoc] using hpayload

private theorem abiDepositCall_payload_two
    (pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256)
    (hoffset : dynamicOffset
      (abiDepositCall pubkey withdrawalCredentials signature depositDataRoot)
      2 = thirdDepositTailOffset pubkey withdrawalCredentials)
    (hlength : dynamicLength
      (abiDepositCall pubkey withdrawalCredentials signature depositDataRoot)
      2 = signature.length) :
    dynamicPayload
        (abiDepositCall pubkey withdrawalCredentials signature depositDataRoot)
        2 =
      signature := by
  unfold dynamicPayload
  rw [hoffset, hlength, abiDepositCall_eq_head_tails]
  have hstart :
      (depositCallHead pubkey withdrawalCredentials depositDataRoot ++
        abiBytesTail pubkey ++ abiBytesTail withdrawalCredentials).length + 32 =
        36 + thirdDepositTailOffset pubkey withdrawalCredentials := by
    simp only [List.length_append, depositCallHead_length,
      abiBytesTail_length, thirdDepositTailOffset,
      secondDepositTailOffset, firstDepositTailOffset]
    omega
  have hpayload := sliceD_append_abiBytesTail
      (depositCallHead pubkey withdrawalCredentials depositDataRoot ++
        abiBytesTail pubkey ++ abiBytesTail withdrawalCredentials)
      signature
      []
  rw [hstart] at hpayload
  simpa only [List.append_nil] using hpayload

theorem abiDepositCall_length
    (pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256) :
    (abiDepositCall pubkey withdrawalCredentials signature
      depositDataRoot).length =
      132 + (32 + ceil32 pubkey.length) +
        (32 + ceil32 withdrawalCredentials.length) +
        (32 + ceil32 signature.length) := by
  simp only [abiDepositCall, List.length_append, abiSelectorBytes_length,
    B256.length_toBytes, abiBytesTail_length]

theorem canonicalDepositCalldata_dataBound
    {data pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256}
    (hcanonical : CanonicalDepositCalldata data pubkey
      withdrawalCredentials signature depositDataRoot) :
    data.length < 2 ^ 256 := by
  rcases hcanonical with ⟨rfl, hbound⟩
  omega

theorem canonicalDepositCalldata_decodable
    {data pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256}
    (hcanonical : CanonicalDepositCalldata data pubkey
      withdrawalCredentials signature depositDataRoot) :
    DepositAbiDecodable data pubkey withdrawalCredentials signature
      depositDataRoot := by
  rcases hcanonical with ⟨rfl, hbound⟩
  rw [abiDepositCall_length] at hbound
  have hpubkeyCeil := Nat.le_ceil32 pubkey.length
  have hwithdrawalCredentialsCeil :=
    Nat.le_ceil32 withdrawalCredentials.length
  have hsignatureCeil := Nat.le_ceil32 signature.length
  have hpubkeyBound : pubkey.length < 2 ^ 32 := by
    omega
  have hwithdrawalCredentialsBound :
      withdrawalCredentials.length < 2 ^ 32 := by
    omega
  have hsignatureBound : signature.length < 2 ^ 32 := by
    omega
  have hfirstOffsetBound : firstDepositTailOffset < 2 ^ 32 := by
    norm_num [firstDepositTailOffset]
  have hsecondOffsetBound :
      secondDepositTailOffset pubkey < 2 ^ 32 := by
    simp only [secondDepositTailOffset, firstDepositTailOffset,
      abiBytesTail_length]
    omega
  have hthirdOffsetBound :
      thirdDepositTailOffset pubkey withdrawalCredentials < 2 ^ 32 := by
    simp only [thirdDepositTailOffset, secondDepositTailOffset,
      firstDepositTailOffset, abiBytesTail_length]
    omega
  have hfirstOffsetWordBound : firstDepositTailOffset < 2 ^ 256 := by
    omega
  have hsecondOffsetWordBound :
      secondDepositTailOffset pubkey < 2 ^ 256 := by
    omega
  have hthirdOffsetWordBound :
      thirdDepositTailOffset pubkey withdrawalCredentials < 2 ^ 256 := by
    omega
  have hoffsetZero : dynamicOffset
      (abiDepositCall pubkey withdrawalCredentials signature depositDataRoot)
      0 = firstDepositTailOffset := by
    unfold dynamicOffset
    rw [show 4 + 32 * 0 = 4 by omega,
      abiDepositCall_offsetWord_zero]
    exact B256.toNat_toB256_of_lt hfirstOffsetWordBound
  have hoffsetOne : dynamicOffset
      (abiDepositCall pubkey withdrawalCredentials signature depositDataRoot)
      1 = secondDepositTailOffset pubkey := by
    unfold dynamicOffset
    rw [show 4 + 32 * 1 = 36 by omega,
      abiDepositCall_offsetWord_one]
    exact B256.toNat_toB256_of_lt hsecondOffsetWordBound
  have hoffsetTwo : dynamicOffset
      (abiDepositCall pubkey withdrawalCredentials signature depositDataRoot)
      2 = thirdDepositTailOffset pubkey withdrawalCredentials := by
    unfold dynamicOffset
    rw [show 4 + 32 * 2 = 68 by omega,
      abiDepositCall_offsetWord_two]
    exact B256.toNat_toB256_of_lt hthirdOffsetWordBound
  have hpubkeyWordBound : pubkey.length < 2 ^ 256 := by
    omega
  have hwithdrawalCredentialsWordBound :
      withdrawalCredentials.length < 2 ^ 256 := by
    omega
  have hsignatureWordBound : signature.length < 2 ^ 256 := by
    omega
  have hlengthZero : dynamicLength
      (abiDepositCall pubkey withdrawalCredentials signature depositDataRoot)
      0 = pubkey.length := by
    unfold dynamicLength
    rw [hoffsetZero,
      show 4 + firstDepositTailOffset = 132 by
        norm_num [firstDepositTailOffset],
      abiDepositCall_lengthWord_zero]
    exact B256.toNat_toB256_of_lt hpubkeyWordBound
  have hlengthOne : dynamicLength
      (abiDepositCall pubkey withdrawalCredentials signature depositDataRoot)
      1 = withdrawalCredentials.length := by
    unfold dynamicLength
    rw [hoffsetOne, abiDepositCall_lengthWord_one]
    exact B256.toNat_toB256_of_lt hwithdrawalCredentialsWordBound
  have hlengthTwo : dynamicLength
      (abiDepositCall pubkey withdrawalCredentials signature depositDataRoot)
      2 = signature.length := by
    unfold dynamicLength
    rw [hoffsetTwo, abiDepositCall_lengthWord_two]
    exact B256.toNat_toB256_of_lt hsignatureWordBound
  refine {
    head := ?_
    pubkeyTail := ?_
    withdrawalCredentialsTail := ?_
    signatureTail := ?_
    pubkey_eq := abiDepositCall_payload_zero pubkey withdrawalCredentials
      signature depositDataRoot hoffsetZero hlengthZero
    withdrawalCredentials_eq := abiDepositCall_payload_one pubkey
      withdrawalCredentials signature depositDataRoot hoffsetOne hlengthOne
    signature_eq := abiDepositCall_payload_two pubkey withdrawalCredentials
      signature depositDataRoot hoffsetTwo hlengthTwo
    root_eq := abiDepositCall_rootWord pubkey withdrawalCredentials signature
      depositDataRoot
  }
  · rw [abiDepositCall_length]
    omega
  · simp only [DynamicTailDecodable, hoffsetZero, hlengthZero,
      abiDepositCall_length, firstDepositTailOffset]
    omega
  · simp only [DynamicTailDecodable, hoffsetOne, hlengthOne,
      abiDepositCall_length, secondDepositTailOffset,
      firstDepositTailOffset, abiBytesTail_length]
    omega
  · simp only [DynamicTailDecodable, hoffsetTwo, hlengthTwo,
      abiDepositCall_length, thirdDepositTailOffset,
      secondDepositTailOffset, firstDepositTailOffset,
      abiBytesTail_length]
    omega

end Blanc.BeaconDeposit
