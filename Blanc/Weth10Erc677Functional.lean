-- Exact successful effects and shared failure links for WETH10 ERC-677 calls.

import Blanc.Weth10StateFunctional
import Blanc.Weth10StateSound
import Blanc.Weth10Errors
import Blanc.Weth10TransferFunctional
import Blanc.Ladder

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace Weth10

/-! ## Public selectors and canonical calldata -/

def approveAndCallSelector : B256 :=
  selector "approveAndCall" [.address, .uint256, .dynBytes]

def depositToAndCallSelector : B256 :=
  selector "depositToAndCall" [.address, .dynBytes]

def transferAndCallSelector : B256 :=
  selector "transferAndCall" [.address, .uint256, .dynBytes]

private lemma decodesTwo_split {e : Sevm} {sel a b : B256} {data : Bytes}
    (h : Sevm.DecodesCallWithTail e sel [a, b] data) :
    e.data = abiSelectorBytes sel ++
      (a.toBytes ++ (b.toBytes ++
        ((Nat.toB256 96).toBytes ++ abiBytesTail data))) := by
  simpa [Sevm.DecodesCallWithTail, abiCallWithTail,
    List.append_assoc] using h

private lemma argWord_zero_of_decodesTwo
    {e : Sevm} {sel a b : B256} {data : Bytes}
    (h : Sevm.DecodesCallWithTail e sel [a, b] data) :
    Sevm.argWord e 0 = a :=
  dataWord_of_append (by rw [abiSelectorBytes_length]; rfl)
    (decodesTwo_split h)

private lemma argWord_one_of_decodesTwo
    {e : Sevm} {sel a b : B256} {data : Bytes}
    (h : Sevm.DecodesCallWithTail e sel [a, b] data) :
    Sevm.argWord e 1 = b := by
  have hd : e.data = (abiSelectorBytes sel ++ a.toBytes) ++
      (b.toBytes ++ ((Nat.toB256 96).toBytes ++ abiBytesTail data)) := by
    rw [List.append_assoc]
    exact decodesTwo_split h
  exact dataWord_of_append
    (by rw [List.length_append, abiSelectorBytes_length,
      B256.length_toBytes]; rfl) hd

private lemma argWord_two_of_decodesTwo
    {e : Sevm} {sel a b : B256} {data : Bytes}
    (h : Sevm.DecodesCallWithTail e sel [a, b] data) :
    Sevm.argWord e 2 = Nat.toB256 96 := by
  have hd : e.data =
      (abiSelectorBytes sel ++ a.toBytes ++ b.toBytes) ++
        ((Nat.toB256 96).toBytes ++ abiBytesTail data) := by
    rw [List.append_assoc, List.append_assoc]
    exact decodesTwo_split h
  exact dataWord_of_append
    (by rw [List.length_append, List.length_append,
      abiSelectorBytes_length, B256.length_toBytes,
      B256.length_toBytes]; rfl) hd

private lemma tailLen_two_of_decodes
    {e : Sevm} {sel a b : B256} {data : Bytes}
    (h : Sevm.DecodesCallWithTail e sel [a, b] data) :
    Sevm.tailLen e 2 = Nat.toB256 data.length := by
  have hptr : Sevm.tailPtr e 2 = Nat.toB256 100 := by
    simp only [Sevm.tailPtr, argWord_two_of_decodesTwo h]
    rfl
  rw [Sevm.tailLen, hptr]
  have hd : e.data =
      (abiSelectorBytes sel ++ a.toBytes ++ b.toBytes ++
        (Nat.toB256 96).toBytes) ++
      ((Nat.toB256 data.length).toBytes ++
        (data ++ List.replicate (ceil32 data.length - data.length) 0)) := by
    simpa [Sevm.DecodesCallWithTail, abiCallWithTail, abiBytesTail,
      List.append_assoc] using h
  exact dataWord_of_append
    (by rw [List.length_append, List.length_append,
      List.length_append, abiSelectorBytes_length,
      B256.length_toBytes, B256.length_toBytes,
      B256.length_toBytes]; rfl) hd

private lemma tailBytes_two_of_decodes
    {e : Sevm} {sel a b : B256} {data : Bytes}
    (hlen : data.length < 2 ^ 256)
    (h : Sevm.DecodesCallWithTail e sel [a, b] data) :
    Sevm.tailBytes e 2 = data := by
  have hptr : Sevm.tailPtr e 2 = Nat.toB256 100 := by
    simp only [Sevm.tailPtr, argWord_two_of_decodesTwo h]
    rfl
  have hnat : (Nat.toB256 data.length).toNat = data.length := by
    rw [B256.toNat_toB256]
    exact Nat.mod_eq_of_lt hlen
  simp only [Sevm.tailBytes, hptr, tailLen_two_of_decodes h, hnat]
  have hd : e.data =
      ((abiSelectorBytes sel ++ a.toBytes ++ b.toBytes ++
        (Nat.toB256 96).toBytes) ++ (Nat.toB256 data.length).toBytes) ++
      (data ++ List.replicate (ceil32 data.length - data.length) 0) := by
    simpa [Sevm.DecodesCallWithTail, abiCallWithTail, abiBytesTail,
      List.append_assoc] using h
  show List.sliceD e.data 132 data.length 0 = data
  rw [hd, List.sliceD,
    List.drop_length_append' (by
      simp [abiSelectorBytes_length, B256.length_toBytes]),
    List.takeD_eq_take _ (by simp [List.length_append]),
    List.take_length_append' rfl]

private lemma decodesOne_split {e : Sevm} {sel a : B256} {data : Bytes}
    (h : Sevm.DecodesCallWithTail e sel [a] data) :
    e.data = abiSelectorBytes sel ++
      (a.toBytes ++ ((Nat.toB256 64).toBytes ++ abiBytesTail data)) := by
  simpa [Sevm.DecodesCallWithTail, abiCallWithTail,
    List.append_assoc] using h

private lemma argWord_zero_of_decodesOne
    {e : Sevm} {sel a : B256} {data : Bytes}
    (h : Sevm.DecodesCallWithTail e sel [a] data) :
    Sevm.argWord e 0 = a :=
  dataWord_of_append (by rw [abiSelectorBytes_length]; rfl)
    (decodesOne_split h)

private lemma argWord_one_of_decodesOne
    {e : Sevm} {sel a : B256} {data : Bytes}
    (h : Sevm.DecodesCallWithTail e sel [a] data) :
    Sevm.argWord e 1 = Nat.toB256 64 := by
  have hd : e.data = (abiSelectorBytes sel ++ a.toBytes) ++
      ((Nat.toB256 64).toBytes ++ abiBytesTail data) := by
    rw [List.append_assoc]
    exact decodesOne_split h
  exact dataWord_of_append
    (by rw [List.length_append, abiSelectorBytes_length,
      B256.length_toBytes]; rfl) hd

private lemma tailLen_one_of_decodes
    {e : Sevm} {sel a : B256} {data : Bytes}
    (h : Sevm.DecodesCallWithTail e sel [a] data) :
    Sevm.tailLen e 1 = Nat.toB256 data.length := by
  have hptr : Sevm.tailPtr e 1 = Nat.toB256 68 := by
    simp only [Sevm.tailPtr, argWord_one_of_decodesOne h]
    rfl
  rw [Sevm.tailLen, hptr]
  have hd : e.data =
      (abiSelectorBytes sel ++ a.toBytes ++ (Nat.toB256 64).toBytes) ++
      ((Nat.toB256 data.length).toBytes ++
        (data ++ List.replicate (ceil32 data.length - data.length) 0)) := by
    simpa [Sevm.DecodesCallWithTail, abiCallWithTail, abiBytesTail,
      List.append_assoc] using h
  exact dataWord_of_append
    (by rw [List.length_append, List.length_append,
      abiSelectorBytes_length, B256.length_toBytes,
      B256.length_toBytes]; rfl) hd

private lemma tailBytes_one_of_decodes
    {e : Sevm} {sel a : B256} {data : Bytes}
    (hlen : data.length < 2 ^ 256)
    (h : Sevm.DecodesCallWithTail e sel [a] data) :
    Sevm.tailBytes e 1 = data := by
  have hptr : Sevm.tailPtr e 1 = Nat.toB256 68 := by
    simp only [Sevm.tailPtr, argWord_one_of_decodesOne h]
    rfl
  have hnat : (Nat.toB256 data.length).toNat = data.length := by
    rw [B256.toNat_toB256]
    exact Nat.mod_eq_of_lt hlen
  simp only [Sevm.tailBytes, hptr, tailLen_one_of_decodes h, hnat]
  have hd : e.data =
      ((abiSelectorBytes sel ++ a.toBytes ++ (Nat.toB256 64).toBytes) ++
        (Nat.toB256 data.length).toBytes) ++
      (data ++ List.replicate (ceil32 data.length - data.length) 0) := by
    simpa [Sevm.DecodesCallWithTail, abiCallWithTail, abiBytesTail,
      List.append_assoc] using h
  show List.sliceD e.data 100 data.length 0 = data
  rw [hd, List.sliceD,
    List.drop_length_append' (by
      simp [abiSelectorBytes_length, B256.length_toBytes]),
    List.takeD_eq_take _ (by simp [List.length_append]),
    List.take_length_append' rfl]

private lemma normalize_adr_toB256 (a : Adr) :
    ((~~~ addressMask) &&& a.toB256) = a.toB256 := by
  have u64_and_max (x : UInt64) : UInt64.max &&& x = x := by
    apply UInt64.toBitVec_inj.mp
    rw [UInt64.toBitVec_and]
    have hmax : UInt64.max.toBitVec = BitVec.allOnes 64 := by rfl
    rw [hmax]
    exact BitVec.allOnes_and
  have b128_and_max (x : B128) : B128.max &&& x = x := by
    apply Prod.ext <;> apply u64_and_max
  have hm : (~~~ addressMask) =
      (⟨⟨0, 0x00000000ffffffff⟩, B128.max⟩ : B256) := by
    decide +kernel
  rw [hm]
  rcases a with ⟨ahi, alo⟩
  simp only [Adr.toB256, B256.and_eq_and_prod_and,
    B128.and_eq_and_prod_and, UInt64.zero_and]
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · change (-1 : UInt32).toUInt64 &&& ahi.toUInt64 = ahi.toUInt64
      rw [← UInt32.toUInt64_and]
      simp
  · exact b128_and_max alo

/-! ## Canonical token-callback image -/

private def tokenCallbackImage (img : Bytes) (sel caller value len : B256)
    (payload : Bytes) : Bytes :=
  Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
    (Bytes.writeAt (Bytes.writeAt img 0 sel.toBytes)
      32 caller.toBytes) 64 value.toBytes) 96 (0x60 : B256).toBytes)
      128 len.toBytes) 160 payload

private lemma of_storeTokenCallbackHead_val
    {e : Sevm} {s s' : Devm} {sel value : B256} {xs : Stack}
    (hp : value :: xs <<+ s.stack)
    (h : Line.Run e s (storeTokenCallbackHead sel) s') :
    xs <<+ s'.stack ∧
      s'.memory =
        ((((s.memory.write 0 sel.toBytes).write
          32 e.caller.toB256.toBytes).write
          64 value.toBytes).write 96 (0x60 : B256).toBytes) := by
  simp only [storeTokenCallbackHead] at h
  rcases Line.of_run_cons h with ⟨t1, q1, h⟩
  have hb1 := of_run_pushB256 q1
  have hp1 : sel :: value :: xs <<+ t1.stack :=
    prefix_of_push hb1 hp
  rcases of_run_append (mstoreAt 0) h with ⟨t2, q2, h⟩
  rcases of_run_mstoreAt_val q2 hp1 with ⟨hp2, hm2⟩
  have e2 : t2.memory = s.memory.write 0 sel.toBytes := by
    rw [hm2, ← hb1.memory]
    rfl
  rcases Line.of_run_cons h with ⟨t3, q3, h⟩
  have hb3 := of_run_caller q3
  have hp3 : e.caller.toB256 :: value :: xs <<+ t3.stack :=
    prefix_of_push hb3 hp2
  rcases of_run_append (mstoreAt 1) h with ⟨t4, q4, h⟩
  rcases of_run_mstoreAt_val q4 hp3 with ⟨hp4, hm4⟩
  have e4 : t4.memory =
      (s.memory.write 0 sel.toBytes).write
        32 e.caller.toB256.toBytes := by
    rw [hm4, ← hb3.memory, e2]
    rfl
  rcases of_run_append (mstoreAt 2) h with ⟨t5, q5, h⟩
  rcases of_run_mstoreAt_val q5 hp4 with ⟨hp5, hm5⟩
  have e5 : t5.memory =
      ((s.memory.write 0 sel.toBytes).write
        32 e.caller.toB256.toBytes).write 64 value.toBytes := by
    rw [hm5, e4]
    rfl
  rcases Line.of_run_cons h with ⟨t6, q6, h⟩
  have hb6 := of_run_pushB256 q6
  have hp6 : (0x60 : B256) :: xs <<+ t6.stack :=
    prefix_of_push hb6 hp5
  rcases of_run_mstoreAt_val h hp6 with ⟨hp7, hm7⟩
  exact ⟨hp7, by rw [hm7, ← hb6.memory, e5]; rfl⟩

private lemma of_tokenCallbackArgsSize_val
    {e : Sevm} {s s' : Devm} {len xs}
    (hp : len :: xs <<+ s.stack)
    (h : Line.Run e s tokenCallbackArgsSize s') :
    (0x84 + ((~~~ (31 : B256)) &&& (31 + len))) :: xs <<+
      s'.stack := by
  simp only [tokenCallbackArgsSize] at h
  rcases Line.of_run_cons h with ⟨u1, q1, h⟩
  have hp1 : (31 : B256) :: len :: xs <<+ u1.stack :=
    prefix_of_push (of_run_pushB256 q1) hp
  rcases Line.of_run_cons h with ⟨u2, q2, h⟩
  have hp2 := prefix_of_add q2 hp1
  rcases Line.of_run_cons h with ⟨u3, q3, h⟩
  have hp3 : (31 : B256) :: (31 + len) :: xs <<+ u3.stack :=
    prefix_of_push (of_run_pushB256 q3) hp2
  rcases Line.of_run_cons h with ⟨u4, q4, h⟩
  have hp4 := prefix_of_not q4 hp3
  rcases Line.of_run_cons h with ⟨u5, q5, h⟩
  have hp5 := prefix_of_and q5 hp4
  rcases Line.of_run_cons h with ⟨u6, q6, h⟩
  have hp6 : (0x84 : B256) ::
      ((~~~ (31 : B256)) &&& (31 + len)) :: xs <<+ u6.stack :=
    prefix_of_push (of_run_pushB256 q6) hp5
  rcases Line.of_run_cons h with ⟨u7, q7, hnil⟩
  cases hnil
  exact prefix_of_add q7 hp6

private lemma toNat_tokenCallbackArgsSize {len : Nat}
    (h : 132 + ceil32 len < 2 ^ 256) :
    ((0x84 : B256) +
      ((~~~ (31 : B256)) &&& (31 + Nat.toB256 len))).toNat =
        132 + ceil32 len := by
  have hlen : 31 + len < 2 ^ 256 := by
    have := Nat.le_ceil32 len
    omega
  rw [B256.toNat_add, B256.toNat_ceil32 hlen,
    show B256.toNat 0x84 = 132 from rfl, Nat.lo_eq_of_lt h]

private lemma Bytes.writeAt_after_prefix
    (pre tail new : Bytes) :
    Bytes.writeAt (pre ++ tail) pre.length new =
      pre ++ new ++ tail.drop new.length := by
  unfold Bytes.writeAt
  rw [List.takeD_eq_take _ (by simp), List.take_left,
    List.drop_append]
  simp [List.append_assoc]

private lemma tokenCallbackImage_of_short
    (img : Bytes) (sel caller value len : B256) (payload : Bytes)
    (himg : img.length ≤ 160) :
    tokenCallbackImage img sel caller value len payload =
      sel.toBytes ++ caller.toBytes ++ value.toBytes ++
        (0x60 : B256).toBytes ++ len.toBytes ++ payload := by
  have hlen : ∀ x : B256, x.toBytes.length = 32 :=
    B256.length_toBytes
  have e0 : Bytes.writeAt img 0 sel.toBytes =
      sel.toBytes ++ img.drop 32 := by
    rw [Bytes.writeAt, hlen,
      show List.takeD 0 img 0 = [] from rfl,
      List.nil_append, Nat.zero_add]
  have e1 : Bytes.writeAt (sel.toBytes ++ img.drop 32)
      32 caller.toBytes = sel.toBytes ++ caller.toBytes ++ img.drop 64 := by
    simpa only [hlen, List.drop_drop, Nat.reduceAdd] using
      Bytes.writeAt_after_prefix sel.toBytes (img.drop 32) caller.toBytes
  have e2 : Bytes.writeAt
      (sel.toBytes ++ caller.toBytes ++ img.drop 64)
      64 value.toBytes =
      sel.toBytes ++ caller.toBytes ++ value.toBytes ++ img.drop 96 := by
    have h := Bytes.writeAt_after_prefix
      (sel.toBytes ++ caller.toBytes) (img.drop 64) value.toBytes
    simpa only [List.length_append, hlen, Nat.reduceAdd,
      List.drop_drop] using h
  have e3 : Bytes.writeAt
      (sel.toBytes ++ caller.toBytes ++ value.toBytes ++ img.drop 96)
      96 (0x60 : B256).toBytes =
      sel.toBytes ++ caller.toBytes ++ value.toBytes ++
        (0x60 : B256).toBytes ++ img.drop 128 := by
    have h := Bytes.writeAt_after_prefix
      (sel.toBytes ++ caller.toBytes ++ value.toBytes)
      (img.drop 96) (0x60 : B256).toBytes
    simpa only [List.length_append, hlen, Nat.reduceAdd,
      List.drop_drop] using h
  have e4 : Bytes.writeAt
      (sel.toBytes ++ caller.toBytes ++ value.toBytes ++
        (0x60 : B256).toBytes ++ img.drop 128)
      128 len.toBytes =
      sel.toBytes ++ caller.toBytes ++ value.toBytes ++
        (0x60 : B256).toBytes ++ len.toBytes ++ img.drop 160 := by
    have h := Bytes.writeAt_after_prefix
      (sel.toBytes ++ caller.toBytes ++ value.toBytes ++
        (0x60 : B256).toBytes) (img.drop 128) len.toBytes
    simpa only [List.length_append, hlen, Nat.reduceAdd,
      List.drop_drop] using h
  have hdrop : img.drop 160 = [] :=
    List.drop_eq_nil_of_le himg
  unfold tokenCallbackImage
  rw [e0, e1, e2, e3, e4, hdrop]
  simp only [List.append_nil]
  rw [Bytes.writeAt_of_length_eq (by simp [hlen])]

private lemma tokenCallbackWindow
    (sel caller value : B256) (payload : Bytes) :
    (sel.toBytes ++ caller.toBytes ++ value.toBytes ++
      (0x60 : B256).toBytes ++ (Nat.toB256 payload.length).toBytes ++
      payload).sliceD 28 (132 + ceil32 payload.length) 0 =
      abiCallWithTail sel [caller, value] payload := by
  have hlen : ∀ x : B256, x.toBytes.length = 32 :=
    B256.length_toBytes
  have hce : payload.length ≤ ceil32 payload.length := Nat.le_ceil32 _
  have himg :
      (sel.toBytes ++ caller.toBytes ++ value.toBytes ++
        (0x60 : B256).toBytes ++ (Nat.toB256 payload.length).toBytes ++
        payload) =
      sel.toBytes ++ (caller.toBytes ++ value.toBytes ++
        (0x60 : B256).toBytes ++ (Nat.toB256 payload.length).toBytes ++
        payload) := by
    simp [List.append_assoc]
  unfold List.sliceD
  rw [himg, List.drop_append_of_le_length (by rw [hlen]; omega)]
  rw [List.takeD_of_length_le]
  · simp only [abiCallWithTail, abiBytesTail, abiSelectorBytes,
      List.map, List.flatten, List.length_cons, List.length_nil,
      List.append_assoc, List.length_append, hlen, List.length_drop]
    rw [show 132 + ceil32 payload.length -
        (32 - 28 + (32 + (32 + (32 + (32 + payload.length))))) =
        ceil32 payload.length - payload.length from by omega]
    norm_num
    rfl
  · simp only [List.length_append, List.length_drop, hlen]
    omega

/-! ## Normalized callback return -/

/-- Solidity-0.7 truthiness normalized to an ABI Boolean word. -/
def normalizedBoolWord (w : B256) : B256 := (w =? 0) =? 0

private lemma retdatacopy_logs
    {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s retdatacopy s') : s.logs = s'.logs := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s1⟩, h1, run1⟩
  rcases Except.bind_eq_ok run1 with ⟨⟨di, s2⟩, h2, run2⟩
  rcases Except.bind_eq_ok run2 with ⟨⟨sz, s3⟩, h3, run3⟩
  rcases Except.bind_eq_ok run3 with ⟨s4, h4, h5⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x1, p1⟩
  rcases Devm.pop_of_popToNat h2 with ⟨x2, p2⟩
  rcases Devm.pop_of_popToNat h3 with ⟨x3, p3⟩
  have hb := Devm.burn_of_chargeGas h4
  split at h5
  · cases h5
  · injection h5 with eq
    rw [← eq]
    exact (((p1.logs.trans p2.logs).trans p3.logs).trans hb.logs)

private lemma mload_logs
    {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s mload s') : s.logs = s'.logs := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨si, s1⟩, h1, run1⟩
  rcases Except.bind_eq_ok run1 with ⟨s2, h2, run2⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x, p1⟩
  have hb := Devm.burn_of_chargeGas h2
  have hp := Devm.push_of_push run2
  exact ((p1.logs.trans hb.logs).trans rfl).trans hp.logs

private lemma retdataShorterThan_logs
    {e : Sevm} {s s' : Devm} {n : B256}
    (h : Line.Run e s (retdataShorterThan n) s') : s.logs = s'.logs := by
  simp only [retdataShorterThan] at h
  rcases Line.of_run_cons h with ⟨u1, q1, h⟩
  have hb1 := of_run_pushB256 q1
  rcases Line.of_run_cons h with ⟨u2, q2, h⟩
  have hb2 := of_run_retdatasize_val q2
  rcases Line.of_run_cons h with ⟨u3, q3, hnil⟩
  cases hnil
  obtain ⟨a, b, hdb⟩ :
      ∃ a b, Devm.DiffBurn [a, b] [B256.ltCheck a b] u2 s' := by
    rcases of_run_reg q3 with ⟨pc, run⟩
    simp only [Rinst.run, Rinst.runCore] at run
    exact Devm.diffBurn_of_applyBinary run
  exact (hb1.logs.trans hb2.logs).trans hdb.logs

private theorem boolReturn_success_effect
    {dp : DeployParams} {e : Sevm} {s r : Devm}
    {xs : Stack} {img : Bytes}
    (hp : (1 : B256) :: xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s boolReturn r) :
    32 ≤ s.returnData.length ∧
      ReturnsWord
        (normalizedBoolWord
          (Bytes.toB256 (s.returnData.sliceD 0 32 0))) r ∧
      r.logs = s.logs := by
  simp only [boolReturn] at run
  rcases of_run_next run with ⟨s1, hiszeroCall, run1⟩
  have hp1 := prefix_of_iszero hiszeroCall hp
  obtain ⟨callWord, hdbCall⟩ :
      ∃ w, Devm.DiffBurn [w] [w =? 0] s s1 := by
    rcases of_run_reg hiszeroCall with ⟨pc, hreg⟩
    simp only [Rinst.run, Rinst.runCore] at hreg
    exact Devm.diffBurn_of_applyUnary hreg
  rw [show ((1 : B256) =? 0) = 0 from by
    simp [B256.eqCheck]] at hp1
  rcases of_run_branch run1 with
      ⟨s2, hpopCall, hcontinue⟩ |
      ⟨w, s2, s3, hnz, hpopCall, hburn, hbubble⟩
  · have hpopCallStack := hpopCall.stack
    simp only [Stack.Pop, Split, List.nil_append,
      List.cons_append] at hpopCallStack
    rw [hpopCallStack] at hp1
    have hp2 : xs <<+ s2.stack := cons_pref_cons_inv hp1
    rcases of_run_prepend (retdataShorterThan 32) _ hcontinue with
      ⟨s3, hshort, run3⟩
    rcases of_retdataShorterThan_val hp2 hshort with
      ⟨hp3, hmem3, hrd3⟩
    rcases of_run_branch_rev run3 with ⟨s4, hpopShort, hdecode⟩
    have hpopShortStack := hpopShort.stack
    simp only [Stack.Pop, Split, List.nil_append,
      List.cons_append] at hpopShortStack
    rw [hpopShortStack] at hp3
    have hshortFlag : (s2.returnData.length.toB256 <? 32) = 0 :=
      pref_head_unique hp3 (pref_append [(0 : B256)] s4.stack)
    have hlen : 32 ≤ s2.returnData.length := by
      by_contra hlt
      have hlt' : s2.returnData.length < 32 := by omega
      have hltWord : s2.returnData.length.toB256 < (32 : B256) := by
        rw [B256.lt_iff_toNat_lt_toNat,
          B256.toNat_toB256_of_lt (by omega)]
        exact hlt'
      rw [B256.ltCheck, if_pos hltWord] at hshortFlag
      exact B256.zero_ne_one hshortFlag.symm
    rw [hshortFlag] at hp3
    have hp4 : xs <<+ s4.stack := cons_pref_cons_inv hp3
    have hmem_s_s4 : s.memory = s4.memory :=
      (Ninst.Hinv.inv (f := Devm.memory) hiszeroCall).trans
        (hpopCall.memory.trans (hmem3.symm.trans hpopShort.memory))
    have hrd_s_s4 : s.returnData = s4.returnData :=
      hdbCall.returnData.trans
        (hpopCall.returnData.trans (hrd3.symm.trans hpopShort.returnData))
    have hwf4 : Mem.Wf s4.memory := hmem_s_s4 ▸ h_wf
    have hreads4 : Mem.Reads s4.memory img := hmem_s_s4 ▸ h_reads

    let decodePrefix : Line :=
      pushList [32, 0, 0] ++
        [retdatacopy, pushB256 0, mload, iszero, iszero]
    rcases of_run_prepend decodePrefix
        (mstoreAt 0 +++ returnMemoryRange 0 32) hdecode with
      ⟨st, hdecodePrefix, hreturn⟩
    have hdecodePrefixAll := hdecodePrefix
    simp only [decodePrefix, pushList, List.map] at hdecodePrefix
    rcases Line.of_run_cons hdecodePrefix with
      ⟨u1, hpush32, hdecodePrefix⟩
    have hpD1 : (32 : B256) :: xs <<+ u1.stack :=
      prefix_of_push (of_run_pushB256 hpush32) hp4
    rcases Line.of_run_cons hdecodePrefix with
      ⟨u2, hpushSrc, hdecodePrefix⟩
    have hpD2 : (0 : B256) :: 32 :: xs <<+ u2.stack :=
      prefix_of_push (of_run_pushB256 hpushSrc) hpD1
    rcases Line.of_run_cons hdecodePrefix with
      ⟨u3, hpushDst, hdecodePrefix⟩
    have hpD3 : (0 : B256) :: 0 :: 32 :: xs <<+ u3.stack :=
      prefix_of_push (of_run_pushB256 hpushDst) hpD2
    rcases Line.of_run_cons hdecodePrefix with
      ⟨u4, hcopy, hdecodePrefix⟩
    rcases prefix_of_retdatacopy_val hcopy hpD3 with
      ⟨hpD4, hcopyBound, hmem4, hrd4⟩
    have hmem_s4_u3 : s4.memory = u3.memory :=
      ((of_run_pushB256 hpush32).memory.trans
        (of_run_pushB256 hpushSrc).memory).trans
          (of_run_pushB256 hpushDst).memory
    have hrd_s4_u3 : s4.returnData = u3.returnData :=
      ((of_run_pushB256 hpush32).returnData.trans
        (of_run_pushB256 hpushSrc).returnData).trans
          (of_run_pushB256 hpushDst).returnData
    let copied := s4.returnData.sliceD 0 32 0
    let copiedImg := Bytes.writeAt img 0 copied
    have hwf4' : Mem.Wf u4.memory := by
      rw [hmem4, ← hmem_s4_u3, ← hrd_s4_u3]
      exact hwf4.write _ _
    have hreads4' : Mem.Reads u4.memory copiedImg := by
      rw [hmem4, ← hmem_s4_u3, ← hrd_s4_u3]
      exact Mem.Reads.write hwf4 hreads4 0 _
    rcases Line.of_run_cons hdecodePrefix with
      ⟨u5, hpushLoad, hdecodePrefix⟩
    have hpD5 : (0 : B256) :: xs <<+ u5.stack :=
      prefix_of_push (of_run_pushB256 hpushLoad) hpD4
    have hwf5 : Mem.Wf u5.memory := by
      rw [← (of_run_pushB256 hpushLoad).memory]
      exact hwf4'
    have hreads5 : Mem.Reads u5.memory copiedImg := by
      rw [← (of_run_pushB256 hpushLoad).memory]
      exact hreads4'
    rcases Line.of_run_cons hdecodePrefix with
      ⟨u6, hload, hdecodePrefix⟩
    rcases prefix_of_mload_val hload hpD5 hreads5 with
      ⟨hpD6, hmem6, hrd6⟩
    have hslice : copiedImg.sliceD 0 32 0 = copied := by
      unfold copiedImg
      rw [show (32 : Nat) = copied.length by
        unfold copied List.sliceD
        rw [List.takeD_length],
        Bytes.sliceD_writeAt]
    rw [show (0 : B256).toNat = 0 from rfl] at hpD6
    rw [hslice] at hpD6
    rcases Line.of_run_cons hdecodePrefix with
      ⟨u7, hiszero1, hdecodePrefix⟩
    have hpD7 := prefix_of_iszero hiszero1 hpD6
    obtain ⟨z1, hdbZero1⟩ :
        ∃ w, Devm.DiffBurn [w] [w =? 0] u6 u7 := by
      rcases of_run_reg hiszero1 with ⟨pc, hreg⟩
      simp only [Rinst.run, Rinst.runCore] at hreg
      exact Devm.diffBurn_of_applyUnary hreg
    rcases Line.of_run_cons hdecodePrefix with
      ⟨u8, hiszero2, hnil⟩
    cases hnil
    have hpD8 := prefix_of_iszero hiszero2 hpD7
    obtain ⟨z2, hdbZero2⟩ :
        ∃ w, Devm.DiffBurn [w] [w =? 0] u7 st := by
      rcases of_run_reg hiszero2 with ⟨pc, hreg⟩
      simp only [Rinst.run, Rinst.runCore] at hreg
      exact Devm.diffBurn_of_applyUnary hreg
    change normalizedBoolWord (Bytes.toB256 copied) :: xs <<+
      st.stack at hpD8
    have hwfSt : Mem.Wf st.memory := by
      rw [← (Ninst.Hinv.inv (f := Devm.memory) hiszero2),
        ← (Ninst.Hinv.inv (f := Devm.memory) hiszero1), hmem6]
      exact Mem.Wf.extend hwf5 _ _
    have hreadsSt : ∃ out, Mem.Reads st.memory out := by
      rw [← (Ninst.Hinv.inv (f := Devm.memory) hiszero2),
        ← (Ninst.Hinv.inv (f := Devm.memory) hiszero1), hmem6]
      exact ⟨copiedImg, Mem.Reads.extend hreads5 _ _⟩
    rcases hreadsSt with ⟨out, hreadsSt⟩
    obtain ⟨hword, _⟩ :=
      of_storeReturnWord hpD8 hwfSt hreadsSt hreturn
    have hlogsTail : st.logs = r.logs :=
      Func.of_inv Devm.logs Devm.logs (by
        unfold returnMemoryRange pushList
        func_inv) hreturn
    have hlogsPrefix : s4.logs = st.logs :=
      (((((((of_run_pushB256 hpush32).logs.trans
        (of_run_pushB256 hpushSrc).logs).trans
          (of_run_pushB256 hpushDst).logs).trans
            (retdatacopy_logs hcopy)).trans
              (of_run_pushB256 hpushLoad).logs).trans
                (mload_logs hload)).trans hdbZero1.logs).trans
                  hdbZero2.logs
    have hlogs_s_s4 : s.logs = s4.logs :=
      hdbCall.logs.trans
        (hpopCall.logs.trans
          ((retdataShorterThan_logs hshort).trans
            hpopShort.logs))
    have hrd_s_s2 : s.returnData = s2.returnData :=
      hdbCall.returnData.trans hpopCall.returnData
    refine ⟨?_, ?_, ?_⟩
    · rw [hrd_s_s2]
      exact hlen
    · simpa only [ReturnsWord, copied, hrd_s_s4] using hword
    · exact (hlogs_s_s4.trans (hlogsPrefix.trans hlogsTail)).symm
  · rcases of_run_call hbubble with ⟨f, sb, hget, hburn', hrun⟩
    have hf : f = bubbleRevert := by
      simpa [weth10Aux, bubbleRevertSlot] using hget.symm
    subst f
    exact absurd hrun not_run_bubbleRevert

/-! ## Shared successful callback frame -/

private theorem of_run_callBoolCallback_frame
    (dp : DeployParams) (sel targetArg dataArg valueWord : B256)
    (value : Line)
    {e : Sevm} {s r : Devm} {img : Bytes}
    (h_value_stack : ∀ {a b : Devm} {xs : Stack},
      xs <<+ a.stack → Line.Run e a value b →
        valueWord :: xs <<+ b.stack)
    (h_value_stor : Line.Inv Devm.getStor value)
    (h_value_bal : Line.Inv Devm.getBal value)
    (h_value_code : Line.Inv Devm.getCode value)
    (h_value_mem : Line.Inv Devm.memory value)
    (h_value_logs : Line.Inv Devm.logs value)
    (h_value_output : Line.Inv Devm.output value)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s
      (callBoolCallback sel targetArg dataArg value) r) :
    ∃ sc sf g inputSize,
      inputSize =
        0x84 + ((~~~ (31 : B256)) &&&
          (31 + Sevm.tailLen e dataArg)) ∧
      (g :: Sevm.argWord e targetArg :: 0 :: callbackArgsOffset ::
        inputSize :: 0 :: 0 :: []) <<+ sc.stack ∧
      Ninst.Run e sc call sf ∧
      Func.Run ((weth10 dp).main :: weth10Aux) e sf
        (.call boolReturnSlot) r ∧
      Devm.getStor s = Devm.getStor sc ∧
      Devm.getBal s = Devm.getBal sc ∧
      Devm.getCode s = Devm.getCode sc ∧
      s.logs = sc.logs ∧
      s.output = sc.output ∧
      Mem.Wf sc.memory ∧
      Mem.Reads sc.memory
        (tokenCallbackImage img sel e.caller.toB256 valueWord
          (Sevm.tailLen e dataArg) (Sevm.tailBytes e dataArg)) := by
  unfold callBoolCallback at run
  let checkLine : Line :=
    arg targetArg ++ [dup 0, extcodesize, iszero]
  rcases of_run_prepend checkLine _ run with
    ⟨s1, hcheck, run1⟩
  rcases of_run_branch_rev run1 with
    ⟨s2, hpopCheck, run2⟩
  rcases of_run_next run2 with
    ⟨s3, hpopTarget, run3⟩
  rcases of_run_prepend value _ run3 with
    ⟨s4, hvalueLine, run4⟩
  have hp4 : valueWord :: [] <<+ s4.stack :=
    h_value_stack nil_pref hvalueLine
  rcases of_run_prepend (storeTokenCallbackHead sel) _ run4 with
    ⟨s5, hhead, run5⟩
  rcases of_storeTokenCallbackHead_val hp4 hhead with
    ⟨hp5, hmemHead⟩
  rcases of_run_prepend (pushList [0, 0]) _ run5 with
    ⟨s6, hzeros, run6⟩
  have hp6 : (0 : B256) :: 0 :: [] <<+ s6.stack := by
    unfold pushList at hzeros
    simp only [List.map] at hzeros
    rcases Line.of_run_cons hzeros with ⟨z1, hz1, hzeros1⟩
    have hpz1 : (0 : B256) :: [] <<+ z1.stack :=
      prefix_of_push (of_run_pushB256 hz1) hp5
    rcases Line.of_run_cons hzeros1 with ⟨z2, hz2, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 hz2) hpz1
  rcases of_run_prepend (forwardArgTail dataArg 4) _ run6 with
    ⟨s7, htail, run7⟩
  rcases of_forwardArgTail_val hp6 htail with
    ⟨hp7, hmemTail⟩
  rcases of_run_prepend tokenCallbackArgsSize _ run7 with
    ⟨s8, hsize, run8⟩
  have hp8 := of_tokenCallbackArgsSize_val hp7 hsize
  let inputSize : B256 :=
    0x84 + ((~~~ (31 : B256)) &&&
      (31 + Sevm.tailLen e dataArg))
  change inputSize :: 0 :: 0 :: [] <<+ s8.stack at hp8
  rcases of_run_prepend
      [pushB256 callbackArgsOffset, pushB256 0] _ run8 with
    ⟨s9, hoffsets, run9⟩
  have hp9 :
      (0 : B256) :: callbackArgsOffset :: inputSize :: 0 :: 0 :: [] <<+
        s9.stack := by
    rcases Line.of_run_cons hoffsets with ⟨o1, ho1, hoffsets1⟩
    have hpo1 : callbackArgsOffset :: inputSize :: 0 :: 0 :: [] <<+
        o1.stack := prefix_of_push (of_run_pushB256 ho1) hp8
    rcases Line.of_run_cons hoffsets1 with ⟨o2, ho2, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 ho2) hpo1
  rcases of_run_prepend (arg targetArg) _ run9 with
    ⟨s10, htarget, run10⟩
  have hp10 :
      Sevm.argWord e targetArg :: 0 :: callbackArgsOffset :: inputSize ::
        0 :: 0 :: [] <<+ s10.stack :=
    prefix_of_arg hp9 htarget
  rcases of_run_next run10 with ⟨sc, hgas, run11⟩
  rcases of_run_gas hgas with ⟨g, hpushGas⟩
  have hpCall :
      g :: Sevm.argWord e targetArg :: 0 :: callbackArgsOffset ::
        inputSize :: 0 :: 0 :: [] <<+ sc.stack :=
    prefix_of_push hpushGas hp10
  rcases of_run_next run11 with ⟨sf, hcall, hbool⟩

  have hmem_s_s4 : s.memory = s4.memory := by
    unfold checkLine at hcheck
    rcases of_run_append (arg targetArg) hcheck with
      ⟨c0, hargCheck, hcheck0⟩
    rcases Line.of_run_cons hcheck0 with
      ⟨c1, hdupCheck, hcheck1⟩
    rcases Line.of_run_cons hcheck1 with
      ⟨c2, hextCheck, hcheck2⟩
    rcases Line.of_run_cons hcheck2 with
      ⟨c3, hiszeroCheck, hnil⟩
    cases hnil
    have hpArg : Sevm.argWord e targetArg :: [] <<+ c0.stack :=
      prefix_of_arg nil_pref hargCheck
    have hpDup :
        Sevm.argWord e targetArg :: Sevm.argWord e targetArg :: [] <<+
          c1.stack :=
      prefix_of_dup_val hdupCheck (by show_nth) hpArg
    rcases of_extcodesize_frame hpDup hextCheck with
      ⟨_, _, hmemExt⟩
    have hmemArg : s.memory = c0.memory :=
      Line.of_inv Devm.memory (by
        unfold arg cdl
        line_inv) hargCheck
    have hmemDup : c0.memory = c1.memory :=
      Line.of_inv Devm.memory (by line_inv)
        (Line.Run.cons hdupCheck Line.Run.nil)
    have hmemIszero : c2.memory = s1.memory :=
      Line.of_inv Devm.memory (by line_inv)
        (Line.Run.cons hiszeroCheck Line.Run.nil)
    have hmemPop : s2.memory = s3.memory :=
      Line.of_inv Devm.memory (by line_inv)
        (Line.Run.cons hpopTarget Line.Run.nil)
    exact hmemArg.trans (hmemDup.trans (hmemExt.trans
      (hmemIszero.trans (hpopCheck.memory.trans
        (hmemPop.trans (h_value_mem hvalueLine))))))
  have hwf4 : Mem.Wf s4.memory := hmem_s_s4 ▸ h_wf
  have hreads4 : Mem.Reads s4.memory img := hmem_s_s4 ▸ h_reads
  let headImg := Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
    (Bytes.writeAt img 0 sel.toBytes) 32 e.caller.toB256.toBytes)
      64 valueWord.toBytes) 96 (0x60 : B256).toBytes
  have hwf5 : Mem.Wf s5.memory := by
    rw [hmemHead]
    exact (((hwf4.write _ _).write _ _).write _ _).write _ _
  have hreads5 : Mem.Reads s5.memory headImg := by
    rw [hmemHead]
    exact Mem.Reads.write
      (((hwf4.write _ _).write _ _).write _ _)
      (Mem.Reads.write ((hwf4.write _ _).write _ _)
        (Mem.Reads.write (hwf4.write _ _)
          (Mem.Reads.write hwf4 hreads4 0 _) 32 _) 64 _) 96 _
  have hmem5_6 : s5.memory = s6.memory :=
    Line.of_inv Devm.memory (by
      unfold pushList
      line_inv) hzeros
  have hwf6 : Mem.Wf s6.memory := hmem5_6 ▸ hwf5
  have hreads6 : Mem.Reads s6.memory headImg := hmem5_6 ▸ hreads5
  have hwf7 : Mem.Wf s7.memory := by
    rw [hmemTail]
    exact (hwf6.write _ _).write _ _
  have hreads7 : Mem.Reads s7.memory
      (tokenCallbackImage img sel e.caller.toB256 valueWord
        (Sevm.tailLen e dataArg) (Sevm.tailBytes e dataArg)) := by
    rw [hmemTail]
    exact Mem.Reads.write (hwf6.write _ _)
      (Mem.Reads.write hwf6 hreads6 128 _) 160 _
  have hmem7_sc : s7.memory = sc.memory :=
    (Line.of_inv Devm.memory (by line_inv) hsize).trans
      ((Line.of_inv Devm.memory (by line_inv) hoffsets).trans
        ((Line.of_inv Devm.memory (by
          unfold arg cdl
          line_inv) htarget).trans
            (Line.of_inv Devm.memory (by line_inv)
              (Line.Run.cons hgas Line.Run.nil))))
  have hwfSc : Mem.Wf sc.memory := hmem7_sc ▸ hwf7
  have hreadsSc : Mem.Reads sc.memory
      (tokenCallbackImage img sel e.caller.toB256 valueWord
        (Sevm.tailLen e dataArg) (Sevm.tailBytes e dataArg)) :=
    hmem7_sc ▸ hreads7

  have h_stor_s3_sc : Devm.getStor s3 = Devm.getStor sc :=
    (h_value_stor hvalueLine).trans
      ((Line.of_inv Devm.getStor (by line_inv) hhead).trans
        ((Line.of_inv Devm.getStor (by line_inv) hzeros).trans
          ((Line.of_inv Devm.getStor (by line_inv) htail).trans
            ((Line.of_inv Devm.getStor (by line_inv) hsize).trans
              ((Line.of_inv Devm.getStor (by line_inv) hoffsets).trans
                ((Line.of_inv Devm.getStor (by line_inv) htarget).trans
                  (Line.of_inv Devm.getStor (by line_inv)
                    (Line.Run.cons hgas Line.Run.nil))))))))
  have h_bal_s3_sc : Devm.getBal s3 = Devm.getBal sc :=
    (h_value_bal hvalueLine).trans
      ((Line.of_inv Devm.getBal (by line_inv) hhead).trans
        ((Line.of_inv Devm.getBal (by line_inv) hzeros).trans
          ((Line.of_inv Devm.getBal (by line_inv) htail).trans
            ((Line.of_inv Devm.getBal (by line_inv) hsize).trans
              ((Line.of_inv Devm.getBal (by line_inv) hoffsets).trans
                ((Line.of_inv Devm.getBal (by line_inv) htarget).trans
                  (Line.of_inv Devm.getBal (by line_inv)
                    (Line.Run.cons hgas Line.Run.nil))))))))
  have h_code_s3_sc : Devm.getCode s3 = Devm.getCode sc :=
    (h_value_code hvalueLine).trans
      ((Line.of_inv Devm.getCode (by line_inv) hhead).trans
        ((Line.of_inv Devm.getCode (by line_inv) hzeros).trans
          ((Line.of_inv Devm.getCode (by line_inv) htail).trans
            ((Line.of_inv Devm.getCode (by line_inv) hsize).trans
              ((Line.of_inv Devm.getCode (by line_inv) hoffsets).trans
                ((Line.of_inv Devm.getCode (by line_inv) htarget).trans
                  (Line.of_inv Devm.getCode (by line_inv)
                    (Line.Run.cons hgas Line.Run.nil))))))))
  have h_stor_s_sc : Devm.getStor s = Devm.getStor sc :=
    (Line.of_inv Devm.getStor (by line_inv) hcheck).trans
      ((PopBurn.Inv.inv hpopCheck).trans
        ((Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hpopTarget Line.Run.nil)).trans h_stor_s3_sc))
  have h_bal_s_sc : Devm.getBal s = Devm.getBal sc :=
    (Line.of_inv Devm.getBal (by line_inv) hcheck).trans
      ((PopBurn.Inv.inv hpopCheck).trans
        ((Line.of_inv Devm.getBal (by line_inv)
          (Line.Run.cons hpopTarget Line.Run.nil)).trans h_bal_s3_sc))
  have h_code_s_sc : Devm.getCode s = Devm.getCode sc :=
    (Line.of_inv Devm.getCode (by line_inv) hcheck).trans
      ((funext fun a => getCode_eq_of_state_eq hpopCheck.state a).trans
        ((Line.of_inv Devm.getCode (by line_inv)
          (Line.Run.cons hpopTarget Line.Run.nil)).trans h_code_s3_sc))
  have h_logs_s3_sc : s3.logs = sc.logs :=
    (h_value_logs hvalueLine).trans
      ((Line.of_inv Devm.logs (by line_inv) hhead).trans
        ((Line.of_inv Devm.logs (by line_inv) hzeros).trans
          ((Line.of_inv Devm.logs (by line_inv) htail).trans
            ((Line.of_inv Devm.logs (by line_inv) hsize).trans
              ((Line.of_inv Devm.logs (by line_inv) hoffsets).trans
                ((Line.of_inv Devm.logs (by line_inv) htarget).trans
                  (Line.of_inv Devm.logs (by line_inv)
                    (Line.Run.cons hgas Line.Run.nil))))))))
  have h_logs_s_sc : s.logs = sc.logs :=
    (Line.of_inv Devm.logs (by
      unfold checkLine arg cdl
      line_inv) hcheck).trans
      (hpopCheck.logs.trans
        ((Line.of_inv Devm.logs (by line_inv)
          (Line.Run.cons hpopTarget Line.Run.nil)).trans h_logs_s3_sc))
  have h_output_s3_sc : s3.output = sc.output :=
    (h_value_output hvalueLine).trans
      ((Line.of_inv Devm.output (by line_inv) hhead).trans
        ((Line.of_inv Devm.output (by line_inv) hzeros).trans
          ((Line.of_inv Devm.output (by line_inv) htail).trans
            ((Line.of_inv Devm.output (by line_inv) hsize).trans
              ((Line.of_inv Devm.output (by line_inv) hoffsets).trans
                ((Line.of_inv Devm.output (by line_inv) htarget).trans
                  (Line.of_inv Devm.output (by line_inv)
                    (Line.Run.cons hgas Line.Run.nil))))))))
  have h_output_s_sc : s.output = sc.output :=
    (Line.of_inv Devm.output (by
      unfold checkLine arg cdl
      line_inv) hcheck).trans
      (hpopCheck.output.trans
        ((Line.of_inv Devm.output (by line_inv)
          (Line.Run.cons hpopTarget Line.Run.nil)).trans h_output_s3_sc))
  exact ⟨sc, sf, g, inputSize, rfl, hpCall, hcall, hbool,
    h_stor_s_sc, h_bal_s_sc, h_code_s_sc, h_logs_s_sc,
    h_output_s_sc, hwfSc, hreadsSc⟩

/-! The remaining sections construct the exact callback frame and compose
the three endpoint prefixes around it. -/

/-! ## Successful callback boundary -/

/-- A successful ERC-677 callback boundary stated directly in terms of the
words and memory window consumed by `CALL`.  Unlike `TokenCallbackBoundary`,
this relation does not assume that the enclosing calldata has a canonical ABI
tail: `rawTarget` is the full 256-bit argument word, `target` is its low-160-bit
normalization, and `inputSize` and `input` are exactly the modular size word
and memory slice used by the instruction. -/
def RawTokenCallbackBoundary (dp : DeployParams) (e : Sevm)
    (self target : Adr)
    (rawTarget sel value tailLen inputSize : B256) (tail input : Bytes)
    (pre post : Devm) : Prop :=
  target = rawTarget.toAdr ∧
  inputSize =
    0x84 + ((~~~ (31 : B256)) &&& (31 + tailLen)) ∧
  ∃ (callPre callPost parent child : Devm) (xl : Xlot)
      (delegated : Bool) (code : ByteArray) (gasWord : B256) (avail : Nat),
    0 < e.depth ∧
    callPre.stack =
      gasWord :: rawTarget :: (0 : B256) :: callbackArgsOffset ::
        inputSize :: (0 : B256) :: (0 : B256) :: parent.stack ∧
    (callPre.memory.read callbackArgsOffset.toNat inputSize.toNat).1 =
      input ∧
    (∃ img, Mem.Reads callPre.memory
      (tokenCallbackImage img sel e.caller.toB256 value tailLen tail)) ∧
    Devm.getStor pre = Devm.getStor callPre ∧
    Devm.getBal pre = Devm.getBal callPre ∧
    Devm.getCode pre = Devm.getCode callPre ∧
    pre.logs = callPre.logs ∧
    pre.output = callPre.output ∧
    parent.state = callPre.state ∧
    parent.memory = callPre.memory.extends
      [(callbackArgsOffset.toNat, inputSize.toNat), (0, 0)] ∧
    parent.logs = callPre.logs ∧
    parent.output = callPre.output ∧
    ((getDelegatedCodeAddress (callPre.getCode target) = none ∧
        code = callPre.getCode target ∧ delegated = false) ∨
      (∃ delegatedTarget,
        getDelegatedCodeAddress (callPre.getCode target) =
          some delegatedTarget ∧
        code = callPre.getCode delegatedTarget ∧ delegated = true)) ∧
    Xlot.Filled xl ∧
    ProcessMessage
      (callMsg e parent (min gasWord.toNat (except64th avail)) 0
        self target target true false input code delegated)
      xl (.ok child) ∧
    child.error.isSome = false ∧
    (Resume.call parent 0 0).run (.ok child) = .ok callPost ∧
    callPost.state = child.state ∧
    callPost.returnData = child.output ∧
    callPost.memory = parent.memory.write 0 (child.output.take 0) ∧
    callPost.stack = (1 : B256) :: parent.stack ∧
    Func.Run ((weth10 dp).main :: weth10Aux) e
      callPost (.call boolReturnSlot) post

/-- The exact ABI-size word passed to the ERC-677 callback `CALL`. -/
def tokenCallbackSizeWord (data : Bytes) : B256 :=
  0x84 + ((~~~ (31 : B256)) &&& (31 + Nat.toB256 data.length))

/-- A successful ERC-677 child call, including the parent state visible at
entry, the exact callback message, the arbitrary child/reentrant log segment,
and the normalized Solidity-0.7 Boolean returned by the outer WETH10 frame. -/
def TokenCallbackBoundary (e : Sevm) (self target : Adr)
    (sel value : B256) (data : Bytes) (pre post : Devm) : Prop :=
  ∃ (callPre parent child mid : Devm) (xl : Xlot) (delegated : Bool)
      (code : ByteArray) (gasWord : B256) (avail : Nat),
    0 < e.depth ∧
    callPre.stack =
      gasWord :: target.toB256 :: (0 : B256) :: callbackArgsOffset ::
        tokenCallbackSizeWord data :: (0 : B256) :: (0 : B256) ::
        parent.stack ∧
    Devm.getStor pre = Devm.getStor callPre ∧
    Devm.getBal pre = Devm.getBal callPre ∧
    Devm.getCode pre = Devm.getCode callPre ∧
    pre.logs = callPre.logs ∧
    pre.output = callPre.output ∧
    parent.state = callPre.state ∧
    parent.memory = callPre.memory.extends
      [(callbackArgsOffset.toNat, 132 + ceil32 data.length), (0, 0)] ∧
    parent.logs = pre.logs ∧
    parent.output = pre.output ∧
    ((getDelegatedCodeAddress (callPre.getCode target) = none ∧
        code = callPre.getCode target ∧ delegated = false) ∨
      (∃ delegatedTarget,
        getDelegatedCodeAddress (callPre.getCode target) =
          some delegatedTarget ∧
        code = callPre.getCode delegatedTarget ∧ delegated = true)) ∧
    Xlot.Filled xl ∧
    ProcessMessage
      (callMsg e parent (min gasWord.toNat (except64th avail)) 0
        self target target true false
        (abiCallWithTail sel [e.caller.toB256, value] data)
        code delegated)
      xl (.ok child) ∧
    child.error.isSome = false ∧
    32 ≤ child.output.length ∧
    (Resume.call parent 0 0).run (.ok child) = .ok mid ∧
    mid.state = child.state ∧
    mid.returnData = child.output ∧
    mid.stack = (1 : B256) :: parent.stack ∧
    mid.logs = pre.logs ++ child.logs ∧
    mid.output = pre.output ∧
    Devm.getStor post = Devm.getStor child ∧
    Devm.getBal post = Devm.getBal child ∧
    Devm.getCode post self = Devm.getCode child self ∧
    post.logs = pre.logs ++ child.logs ∧
    ReturnsWord
      (normalizedBoolWord
        (Bytes.toB256 (child.output.sliceD 0 32 0))) post

private theorem not_run_call_boolReturn_of_zero
    (dp : DeployParams) {e : Sevm} {s r : Devm} {xs : Stack}
    (hp : (0 : B256) :: xs <<+ s.stack)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s
      (.call boolReturnSlot) r) : False := by
  rcases of_run_call run with
    ⟨f, sb, hget, hburn, hbool⟩
  have hlookup :
      ((weth10 dp).main :: weth10Aux)[boolReturnSlot]? =
        some boolReturn := by
    simp [weth10, weth10Aux, boolReturnSlot]
  have hf : f = boolReturn := by
    rw [hlookup] at hget
    exact Option.some.inj hget.symm
  subst f
  have hpb : (0 : B256) :: xs <<+ sb.stack := by
    rw [← hburn.stack]
    exact hp
  simp only [boolReturn] at hbool
  rcases of_run_next hbool with ⟨s1, hiszero, hbranch⟩
  have hp1 := prefix_of_iszero hiszero hpb
  rw [show ((0 : B256) =? 0) = 1 from by simp [B256.eqCheck]] at hp1
  rcases of_run_branch hbranch with
      ⟨s2, hpop, -⟩ |
      ⟨w, s2, s3, hnz, hpop, hburnCall, hbubbleCall⟩
  · have hs := hpop.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hs
    rw [hs] at hp1
    have h10 : (1 : B256) = 0 :=
      pref_head_unique hp1 (pref_append [(0 : B256)] s2.stack)
    exact B256.zero_ne_one h10.symm
  · rcases of_run_call hbubbleCall with
      ⟨fb, sr, hgetb, hburnb, hbubble⟩
    have hlookupb :
        ((weth10 dp).main :: weth10Aux)[bubbleRevertSlot]? =
          some bubbleRevert := by
      simp [weth10, weth10Aux, bubbleRevertSlot]
    have hfb : fb = bubbleRevert := by
      rw [hlookupb] at hgetb
      exact Option.some.inj hgetb.symm
    subst fb
    exact absurd hbubble not_run_bubbleRevert

/-- Every successful `callBoolCallback` run exposes its exact raw callback
frame, even when the enclosing dynamic-tail pointer or length is malformed.
The existential `inputSize` is the modular EVM word computed by the program;
`input` is the exact memory slice passed to the child rather than a canonical
ABI payload reconstructed from hypotheses. -/
theorem callBoolCallback_rawBoundary
    (dp : DeployParams) (sel targetArg dataArg valueWord : B256)
    (valueLine : Line) {e : Sevm} {pre post : Devm} {img : Bytes}
    (h_value_stack : ∀ {a b : Devm} {xs : Stack},
      xs <<+ a.stack → Line.Run e a valueLine b →
        valueWord :: xs <<+ b.stack)
    (h_value_stor : Line.Inv Devm.getStor valueLine)
    (h_value_bal : Line.Inv Devm.getBal valueLine)
    (h_value_code : Line.Inv Devm.getCode valueLine)
    (h_value_mem : Line.Inv Devm.memory valueLine)
    (h_value_logs : Line.Inv Devm.logs valueLine)
    (h_value_output : Line.Inv Devm.output valueLine)
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e pre
      (callBoolCallback sel targetArg dataArg valueLine) post) :
    ∃ inputSize input,
      RawTokenCallbackBoundary dp e e.currentTarget
        (Sevm.argWord e targetArg).toAdr (Sevm.argWord e targetArg)
        sel valueWord (Sevm.tailLen e dataArg) inputSize
        (Sevm.tailBytes e dataArg) input pre post := by
  rcases of_run_callBoolCallback_frame dp sel targetArg dataArg valueWord
      valueLine h_value_stack h_value_stor h_value_bal h_value_code
      h_value_mem h_value_logs h_value_output h_wf h_reads run with
    ⟨callPre, callPost, gasWord, inputSize, h_input_size, h_stack,
      h_call, h_bool_call, h_stor_pre, h_bal_pre, h_code_pre,
      h_logs_pre, h_output_pre, _h_wf_call, h_reads_call⟩
  let input :=
    (callPre.memory.read callbackArgsOffset.toNat inputSize.toNat).1
  refine ⟨inputSize, input, ?_⟩
  unfold RawTokenCallbackBoundary
  refine ⟨rfl, h_input_size, ?_⟩
  rcases of_run_call_val_with_depth_frame h_stack h_call with
      h_failed | h_success
  · exact absurd h_bool_call
      (not_run_call_boolReturn_of_zero dp h_failed.1)
  · rcases h_success with
      ⟨parent, child, xl, delegated, code, avail,
        h_depth, h_stack_eq, h_parent_state, h_parent_memory,
        h_parent_logs, h_parent_output, h_delegated, h_filled,
        h_message, h_child_clean, h_resume, h_post_state,
        h_post_returnData, h_post_memory, h_post_stack⟩
    refine ⟨callPre, callPost, parent, child, xl, delegated, code,
      gasWord, avail, h_depth, h_stack_eq, rfl, ⟨img, h_reads_call⟩,
      h_stor_pre, h_bal_pre, h_code_pre, h_logs_pre, h_output_pre,
      h_parent_state, ?_, h_parent_logs, h_parent_output, h_delegated,
      h_filled, ?_, h_child_clean, h_resume, h_post_state,
      h_post_returnData, ?_, h_post_stack, h_bool_call⟩
    · simpa only [show (0 : B256).toNat = 0 from rfl] using
        h_parent_memory
    · simpa only [input, show (0 : B256).toNat = 0 from rfl,
        if_true, Nat.add_zero] using h_message
    · simpa only [show (0 : B256).toNat = 0 from rfl] using
        h_post_memory

/-- The common successful ERC-677 callback suffix exposes its exact child
message and transports the child's final world and logs through the normalized
Boolean decoder. -/
theorem callBoolCallback_successEffect
    (dp : DeployParams) (sel targetArg dataArg valueWord : B256)
    (valueLine : Line) {e : Sevm} {pre post : Devm} {img data : Bytes}
    {target : Adr}
    (h_value_stack : ∀ {a b : Devm} {xs : Stack},
      xs <<+ a.stack → Line.Run e a valueLine b →
        valueWord :: xs <<+ b.stack)
    (h_value_stor : Line.Inv Devm.getStor valueLine)
    (h_value_bal : Line.Inv Devm.getBal valueLine)
    (h_value_code : Line.Inv Devm.getCode valueLine)
    (h_value_mem : Line.Inv Devm.memory valueLine)
    (h_value_logs : Line.Inv Devm.logs valueLine)
    (h_value_output : Line.Inv Devm.output valueLine)
    (h_target : target.toB256 = Sevm.argWord e targetArg)
    (h_tail_len : Sevm.tailLen e dataArg = Nat.toB256 data.length)
    (h_tail_bytes : Sevm.tailBytes e dataArg = data)
    (h_size : 132 + ceil32 data.length < 2 ^ 256)
    (h_img : img.length ≤ 160)
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e pre
      (callBoolCallback sel targetArg dataArg valueLine) post) :
    TokenCallbackBoundary e e.currentTarget target sel valueWord data
      pre post := by
  rcases of_run_callBoolCallback_frame dp sel targetArg dataArg valueWord
      valueLine h_value_stack h_value_stor h_value_bal h_value_code
      h_value_mem h_value_logs h_value_output h_wf h_reads run with
    ⟨callPre, callPost, gasWord, inputSize, h_input, h_stack, h_call,
      h_bool_call, h_stor_pre, h_bal_pre, h_code_pre, h_logs_pre,
      h_output_pre, h_wf_call, h_reads_call⟩
  have h_input_word : inputSize = tokenCallbackSizeWord data := by
    rw [h_input, h_tail_len]
    rfl
  rw [h_input_word, ← h_target] at h_stack
  rw [h_tail_len, h_tail_bytes] at h_reads_call
  have h_flat :
      tokenCallbackImage img sel e.caller.toB256 valueWord
          (Nat.toB256 data.length) data =
        sel.toBytes ++ e.caller.toB256.toBytes ++ valueWord.toBytes ++
          (0x60 : B256).toBytes ++
          (Nat.toB256 data.length).toBytes ++ data :=
    tokenCallbackImage_of_short img sel e.caller.toB256 valueWord
      (Nat.toB256 data.length) data h_img
  have h_size_nat :
      (tokenCallbackSizeWord data).toNat =
        132 + ceil32 data.length := by
    unfold tokenCallbackSizeWord
    exact toNat_tokenCallbackArgsSize h_size
  have h_window :
      (callPre.memory.read callbackArgsOffset.toNat
        (tokenCallbackSizeWord data).toNat).1 =
        abiCallWithTail sel [e.caller.toB256, valueWord] data := by
    rw [h_size_nat,
      Mem.Reads.read h_reads_call, h_flat,
      show callbackArgsOffset.toNat = 28 from rfl,
      tokenCallbackWindow]
  rcases of_run_call_val_with_depth_frame h_stack h_call with
      h_failed | h_success
  · exact absurd h_bool_call
      (not_run_call_boolReturn_of_zero dp h_failed.1)
  · rcases h_success with
      ⟨parent, child, xl, delegated, code, avail,
        h_depth, h_stack_eq, h_parent_state, h_parent_memory,
        h_parent_logs, h_parent_output, h_delegated, h_filled,
        h_message, h_child_clean, h_resume, h_post_state,
        h_post_returnData, h_post_memory, h_post_stack⟩
    rw [toAdr_toB256] at h_delegated h_message
    rw [h_window] at h_message
    rcases of_run_call h_bool_call with
      ⟨f, decode, h_get, h_burn, h_bool⟩
    have h_bool_lookup :
        ((weth10 dp).main :: weth10Aux)[boolReturnSlot]? =
          some boolReturn := by
      simp [weth10, weth10Aux, boolReturnSlot]
    have hf : f = boolReturn := by
      rw [h_bool_lookup] at h_get
      exact Option.some.inj h_get.symm
    subst f
    have hp_post : (1 : B256) :: parent.stack <<+ callPost.stack := by
      rw [h_post_stack]
      simpa using (pref_append ((1 : B256) :: parent.stack) [])
    have hp_decode : (1 : B256) :: parent.stack <<+ decode.stack := by
      rw [← h_burn.stack]
      exact hp_post
    have h_post_memory' : callPost.memory = parent.memory := by
      simpa only [show (0 : B256).toNat = 0 from rfl, List.take_zero,
        Mem.write] using h_post_memory
    have h_wf_post : Mem.Wf callPost.memory := by
      rw [h_post_memory', h_parent_memory]
      exact Mem.Wf.extends _ h_wf_call
    have h_reads_post :
        Mem.Reads callPost.memory
          (tokenCallbackImage img sel e.caller.toB256 valueWord
            (Nat.toB256 data.length) data) := by
      rw [h_post_memory', h_parent_memory]
      exact Mem.Reads.extends _ h_reads_call
    have h_wf_decode : Mem.Wf decode.memory := by
      rw [← h_burn.memory]
      exact h_wf_post
    have h_reads_decode :
        Mem.Reads decode.memory
          (tokenCallbackImage img sel e.caller.toB256 valueWord
            (Nat.toB256 data.length) data) := by
      rw [← h_burn.memory]
      exact h_reads_post
    rcases boolReturn_success_effect hp_decode h_wf_decode
        h_reads_decode h_bool with
      ⟨h_output_len, h_return_word, h_decode_logs⟩
    rcases boolReturn_preserves_fields dp h_bool with
      ⟨h_decode_stor, h_decode_bal, h_decode_code⟩
    have h_decode_returnData : decode.returnData = child.output :=
      h_burn.returnData.symm.trans h_post_returnData
    have h_child_len : 32 ≤ child.output.length := by
      rw [← h_decode_returnData]
      exact h_output_len
    have h_clean_not : ¬ child.error.isSome = true := by
      rw [h_child_clean]
      decide
    have h_mid_logs : callPost.logs = pre.logs ++ child.logs := by
      rw [Resume.call_logs h_resume, if_neg h_clean_not,
        h_parent_logs, ← h_logs_pre]
    have h_mid_output : callPost.output = pre.output := by
      rw [Resume.call_output h_resume, h_parent_output, ← h_output_pre]
    have h_decode_child_state : decode.state = child.state :=
      h_burn.state.symm.trans h_post_state
    have h_decode_child_stor :
        Devm.getStor decode = Devm.getStor child :=
      funext (getStor_eq_of_state_eq h_decode_child_state)
    have h_decode_child_bal :
        Devm.getBal decode = Devm.getBal child :=
      funext (getBal_eq_of_state_eq h_decode_child_state)
    have h_decode_child_code :
        Devm.getCode decode e.currentTarget =
          Devm.getCode child e.currentTarget :=
      getCode_eq_of_state_eq h_decode_child_state e.currentTarget
    have h_final_stor : Devm.getStor post = Devm.getStor child :=
      h_decode_stor.symm.trans h_decode_child_stor
    have h_final_bal : Devm.getBal post = Devm.getBal child :=
      h_decode_bal.symm.trans h_decode_child_bal
    have h_final_code :
        Devm.getCode post e.currentTarget =
          Devm.getCode child e.currentTarget :=
      h_decode_code.symm.trans h_decode_child_code
    have h_final_logs : post.logs = pre.logs ++ child.logs :=
      h_decode_logs.trans (h_burn.logs.symm.trans h_mid_logs)
    have h_final_word :
        ReturnsWord
          (normalizedBoolWord
            (Bytes.toB256 (child.output.sliceD 0 32 0))) post := by
      rw [← h_decode_returnData]
      exact h_return_word
    refine ⟨callPre, parent, child, callPost, xl, delegated, code,
      gasWord, avail, h_depth, h_stack_eq, h_stor_pre, h_bal_pre,
      h_code_pre, h_logs_pre, h_output_pre, h_parent_state, ?_, ?_, ?_,
      h_delegated, h_filled, ?_, h_child_clean, h_child_len, h_resume,
      h_post_state, h_post_returnData, h_post_stack, h_mid_logs,
      h_mid_output, h_final_stor, h_final_bal, h_final_code,
      h_final_logs, h_final_word⟩
    · simpa only [h_size_nat,
        show (0 : B256).toNat = 0 from rfl] using h_parent_memory
    · exact h_parent_logs.trans h_logs_pre.symm
    · exact h_parent_output.trans h_output_pre.symm
    · simpa only [show (0 : B256).toNat = 0 from rfl,
        if_true, Nat.add_zero] using h_message

/-! ## Approval callback -/

private def approvePrefixImage (img : Bytes) (e : Sevm) : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt
      (Bytes.writeAt img 0 e.caller.toB256.toBytes)
      32 (e.data.sliceD 4 32 0))
    0 (e.data.sliceD 36 32 0)

private lemma approvePrefixImage_nil_length (e : Sevm) :
    (approvePrefixImage [] e).length ≤ 160 := by
  simp only [approvePrefixImage]
  have hfirst : Bytes.writeAt [] 0 e.caller.toB256.toBytes =
      e.caller.toB256.toBytes :=
    Bytes.writeAt_zero_of_le (Nat.zero_le _)
  have hsecond :
      Bytes.writeAt e.caller.toB256.toBytes 32
          (e.data.sliceD 4 32 0) =
        e.caller.toB256.toBytes ++ e.data.sliceD 4 32 0 :=
    Bytes.writeAt_of_length_eq (by rw [B256.length_toBytes])
  rw [hfirst, hsecond]
  simp only [Bytes.writeAt, List.takeD_zero, List.nil_append,
    List.length_append, List.length_drop, List.sliceD,
    List.takeD_length, B256.length_toBytes]
  omega

/-- Exact approval prefix, stopped immediately before the ERC-677 child
call.  This is the state and log image the child can observe. -/
private theorem approvePrefix_effect
    {e : Sevm} {s r : Devm} {xs : Stack} {img : Bytes}
    (hp : xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Line.Run e s approvePrefix r) :
    Devm.getStor r e.currentTarget =
        (Devm.getStor s e.currentTarget).set
          (approveRuntimeKey e) (Sevm.argWord e 1) ∧
      r.logs = s.logs ++ [approveApprovalLog e] ∧
      Devm.getBal r = Devm.getBal s ∧
      Devm.getCode r = Devm.getCode s ∧
      r.output = s.output ∧
      Mem.Wf r.memory ∧
      Mem.Reads r.memory (approvePrefixImage img e) := by
  have hbalPrefix : Devm.getBal s = Devm.getBal r :=
    Line.of_inv Devm.getBal (by
      unfold approvePrefix allowanceKeyFromMemory Blanc.logApprove
        argCopy cdc pushList
      line_inv) run
  have hcodePrefix : Devm.getCode s = Devm.getCode r :=
    Line.of_inv Devm.getCode (by
      unfold approvePrefix allowanceKeyFromMemory Blanc.logApprove
        argCopy cdc pushList
      line_inv) run
  have houtputPrefix : s.output = r.output :=
    Line.of_inv Devm.output (by
      unfold approvePrefix allowanceKeyFromMemory Blanc.logApprove
        argCopy cdc pushList
      line_inv) run
  unfold approvePrefix at run
  rcases Line.of_run_cons run with ⟨s1, hcaller, run⟩
  have hp1 : e.caller.toB256 :: xs <<+ s1.stack :=
    prefix_of_push (of_run_caller hcaller) hp
  have hm1 : s.memory = s1.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hcaller
  have hwf1 : Mem.Wf s1.memory := hm1 ▸ h_wf
  have hr1 : Mem.Reads s1.memory img := hm1 ▸ h_reads
  rcases of_run_append (mstoreAt 0) run with
    ⟨s2, hmstore0, run⟩
  rcases of_run_mstoreAt_val hmstore0 hp1 with ⟨hp2, hm2⟩
  rw [show (((0 : B256) * 32).toNat) = 0 from rfl] at hm2
  let img1 := Bytes.writeAt img 0 e.caller.toB256.toBytes
  have hwf2 : Mem.Wf s2.memory := by
    rw [hm2]
    exact hwf1.write _ _
  have hr2 : Mem.Reads s2.memory img1 := by
    rw [hm2]
    exact Mem.Reads.write hwf1 hr1 0 _
  rcases of_run_append (argCopy 1 0 1) run with
    ⟨s3, hcopySpender, run⟩
  rcases of_run_argCopy101 hp2 hcopySpender with ⟨hp3, hm3⟩
  let spenderBytes := e.data.sliceD 4 32 0
  let img2 := Bytes.writeAt img1 32 spenderBytes
  have hwf3 : Mem.Wf s3.memory := by
    rw [hm3]
    exact hwf2.write _ _
  have hr3 : Mem.Reads s3.memory img2 := by
    rw [hm3]
    exact Mem.Reads.write hwf2 hr2 32 _
  rcases of_run_append allowanceKeyFromMemory run with
    ⟨s4, hkey, run⟩
  rcases prefix_of_allowanceKeyFromMemory_image hp3 hwf3 hr3 hkey with
    ⟨hp4raw, hwf4, hr4⟩
  have hspenderLen : spenderBytes.length = 32 := by
    unfold spenderBytes List.sliceD
    rw [List.takeD_length]
  have himg2 :
      img2.sliceD 0 64 0 =
        e.caller.toB256.toBytes ++ spenderBytes :=
    slice_two_words img e.caller.toB256 spenderBytes hspenderLen
  have hp4 : approveRuntimeKey e :: xs <<+ s4.stack := by
    rw [himg2] at hp4raw
    simpa only [approveRuntimeKey, img1, spenderBytes] using hp4raw
  rcases of_run_append (arg 1) run with ⟨s5, hargValue, run⟩
  have hp5 : Sevm.argWord e 1 :: approveRuntimeKey e :: xs <<+
      s5.stack := prefix_of_arg hp4 hargValue
  rcases Line.of_run_cons run with ⟨s6, hswap, run⟩
  have hswapCore : Stack.Swap (0 : Fin 16).val
      (Sevm.argWord e 1 :: approveRuntimeKey e :: xs)
      (approveRuntimeKey e :: Sevm.argWord e 1 :: xs) :=
    Stack.swapCore_zero
  have hp6 : approveRuntimeKey e :: Sevm.argWord e 1 :: xs <<+
      s6.stack :=
    Stack.prefix_of_swap hswapCore (of_run_swap hswap) hp5
  rcases Line.of_run_cons run with ⟨s7, hstore, hlogApprove⟩
  have hp7 : xs <<+ s7.stack := prefix_of_sstore hstore hp6
  have hset :
      Devm.getStor s7 e.currentTarget =
        (Devm.getStor s6 e.currentTarget).set
          (approveRuntimeKey e) (Sevm.argWord e 1) :=
    sstore_getStor_set hstore hp6
  have hstorBefore : Devm.getStor s = Devm.getStor s6 := by
    calc
      Devm.getStor s = Devm.getStor s1 :=
        Ninst.Hinv.inv (f := Devm.getStor) hcaller
      _ = Devm.getStor s2 :=
        Line.of_inv Devm.getStor (by line_inv) hmstore0
      _ = Devm.getStor s3 :=
        Line.of_inv Devm.getStor (by
          unfold argCopy cdc
          line_inv) hcopySpender
      _ = Devm.getStor s4 :=
        Line.of_inv Devm.getStor (by
          unfold allowanceKeyFromMemory pushList
          line_inv) hkey
      _ = Devm.getStor s5 :=
        Line.of_inv Devm.getStor (by line_inv) hargValue
      _ = Devm.getStor s6 :=
        Ninst.Hinv.inv (f := Devm.getStor) hswap
  have hmem4to7 : s4.memory = s7.memory := by
    calc
      s4.memory = s5.memory :=
        Line.of_inv Devm.memory (by line_inv) hargValue
      _ = s6.memory := Ninst.Hinv.inv (f := Devm.memory) hswap
      _ = s7.memory := Ninst.Hinv.inv (f := Devm.memory) hstore
  have hwf7 : Mem.Wf s7.memory := hmem4to7 ▸ hwf4
  have hr7 : Mem.Reads s7.memory img2 := hmem4to7 ▸ hr4
  have hstorLog : Devm.getStor s7 = Devm.getStor r :=
    Line.of_inv Devm.getStor (by
      unfold Blanc.logApprove argCopy cdc
      line_inv) hlogApprove
  unfold Blanc.logApprove at hlogApprove
  rcases of_run_append (argCopy 0 1 1) hlogApprove with
    ⟨s8, hcopyValue, hlogApprove⟩
  rcases of_run_argCopy011 hp7 hcopyValue with ⟨hp8, hm8⟩
  let valueBytes := e.data.sliceD 36 32 0
  let img3 := Bytes.writeAt img2 0 valueBytes
  have hwf8 : Mem.Wf s8.memory := by
    rw [hm8]
    exact hwf7.write _ _
  have hr8 : Mem.Reads s8.memory img3 := by
    rw [hm8]
    exact Mem.Reads.write hwf7 hr7 0 _
  rcases of_run_append (arg 0) hlogApprove with
    ⟨s9, hargSpender, hlogApprove⟩
  have hp9 : Sevm.argWord e 0 :: xs <<+ s9.stack :=
    prefix_of_arg hp8 hargSpender
  rcases Line.of_run_cons hlogApprove with
    ⟨s10, hcallerTopic, hlogApprove⟩
  have hp10 : e.caller.toB256 :: Sevm.argWord e 0 :: xs <<+
      s10.stack :=
    prefix_of_push (of_run_caller hcallerTopic) hp9
  rcases Line.of_run_cons hlogApprove with
    ⟨s11, hevent, hlogWith⟩
  have hp11 : approvalEvent :: e.caller.toB256 ::
      Sevm.argWord e 0 :: xs <<+ s11.stack :=
    prefix_of_push (of_run_pushB256 hevent) hp10
  have hmem8to11 : s8.memory = s11.memory := by
    calc
      s8.memory = s9.memory :=
        Line.of_inv Devm.memory (by line_inv) hargSpender
      _ = s10.memory := Ninst.Hinv.inv (f := Devm.memory) hcallerTopic
      _ = s11.memory := Ninst.Hinv.inv (f := Devm.memory) hevent
  have hread : (s11.memory.read 0 32).1 = valueBytes := by
    rw [Mem.Reads.read (hmem8to11 ▸ hr8) 0 32,
      show 32 = valueBytes.length by
        unfold valueBytes List.sliceD
        rw [List.takeD_length],
      Bytes.sliceD_writeAt]
  rcases of_logWith201_val hp11 hlogWith with ⟨hp12, hlogs⟩
  have hlogMem := of_logWith201_mem hp11 hlogWith
  have hwfr : Mem.Wf r.memory := by
    rw [hlogMem, ← hmem8to11]
    exact hwf8.extend _ _
  have hreadsr : Mem.Reads r.memory (approvePrefixImage img e) := by
    rw [hlogMem, ← hmem8to11]
    exact Mem.Reads.extend hr8 _ _
  rw [hread] at hlogs
  have hlogsBefore : s.logs = s11.logs := by
    calc
      s.logs = s1.logs := (of_run_caller hcaller).logs
      _ = s2.logs := Line.of_inv Devm.logs (by line_inv) hmstore0
      _ = s3.logs := Line.of_inv Devm.logs (by
        unfold argCopy cdc
        line_inv) hcopySpender
      _ = s4.logs := Line.of_inv Devm.logs (by
        unfold allowanceKeyFromMemory pushList
        line_inv) hkey
      _ = s5.logs := Line.of_inv Devm.logs (by line_inv) hargValue
      _ = s6.logs := Ninst.Hinv.inv (f := Devm.logs) hswap
      _ = s7.logs := Ninst.Hinv.inv (f := Devm.logs) hstore
      _ = s8.logs := Line.of_inv Devm.logs (by
        unfold argCopy cdc
        line_inv) hcopyValue
      _ = s9.logs := Line.of_inv Devm.logs (by line_inv) hargSpender
      _ = s10.logs := (of_run_caller hcallerTopic).logs
      _ = s11.logs := Ninst.Hinv.inv (f := Devm.logs) hevent
  refine ⟨?_, ?_, hbalPrefix.symm, hcodePrefix.symm,
    houtputPrefix.symm, hwfr, ?_⟩
  · rw [← congrFun hstorLog e.currentTarget, hset,
      ← congrFun hstorBefore e.currentTarget]
  · calc
      r.logs = s11.logs ++ [approveApprovalLog e] := by
        simpa only [approveApprovalLog, valueBytes] using hlogs
      _ = s.logs ++ [approveApprovalLog e] := by rw [hlogsBefore]
  · simpa only [approvePrefixImage, img1, img2, img3, spenderBytes,
      valueBytes] using hreadsr

/-- Exact successful `approveAndCall` effect.  The witness is the state at
the callback boundary, after the allowance write and `Approval` log and before
the child can observe or reenter WETH10. -/
def ApproveAndCallSuccessEffect (e : Sevm) (pre post : Devm)
    (spender : Adr) (amount : B256) (data : Bytes) : Prop :=
  ∃ callbackPre,
    Devm.getStor callbackPre e.currentTarget =
        (Devm.getStor pre e.currentTarget).set
          (approveRuntimeKey e) amount ∧
    callbackPre.logs = pre.logs ++ [approveApprovalLog e] ∧
    Devm.getBal callbackPre = Devm.getBal pre ∧
    Devm.getCode callbackPre = Devm.getCode pre ∧
    callbackPre.output = pre.output ∧
    TokenCallbackBoundary e e.currentTarget spender
      onTokenApprovalSelector amount data callbackPre post

/-- Selected-body `approveAndCall`: exact approval state/log visibility,
canonical callback calldata and target, arbitrary child-log interleaving, and
the normalized Boolean word returned by the outer frame. -/
theorem approveAndCall_successEffect (dp : DeployParams)
    {e : Sevm} {pre post : Devm} {spender : Adr} {amount : B256}
    {data : Bytes}
    (h_dec : Sevm.DecodesCallWithTail e approveAndCallSelector
      [spender.toB256, amount] data)
    (h_size : 132 + ceil32 data.length < 2 ^ 256)
    (h_wf : Mem.Wf pre.memory)
    (h_fresh : Mem.Reads pre.memory [])
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e pre
      approveAndCall post) :
    ApproveAndCallSuccessEffect e pre post spender amount data := by
  have h_data_len : data.length < 2 ^ 256 := by
    have hceil := Nat.le_ceil32 data.length
    omega
  have h0 := argWord_zero_of_decodesTwo h_dec
  have h1 := argWord_one_of_decodesTwo h_dec
  have htl := tailLen_two_of_decodes h_dec
  have htb := tailBytes_two_of_decodes h_data_len h_dec
  simp only [approveAndCall] at run
  rcases of_run_prepend approvePrefix _ run with
    ⟨callbackPre, hprefix, hcallback⟩
  rcases approvePrefix_effect nil_pref h_wf h_fresh hprefix with
    ⟨hstor, hlogs, hbal, hcode, houtput, hwfCallback,
      hreadsCallback⟩
  have hboundary :
      TokenCallbackBoundary e e.currentTarget spender
        onTokenApprovalSelector amount data callbackPre post :=
    callBoolCallback_successEffect dp onTokenApprovalSelector 0 2 amount
      (arg 1)
      (by
        intro a b xs hp hline
        rw [← h1]
        exact prefix_of_arg hp hline)
      (by unfold arg cdl; line_inv)
      (by unfold arg cdl; line_inv)
      (by unfold arg cdl; line_inv)
      (by unfold arg cdl; line_inv)
      (by unfold arg cdl; line_inv)
      (by unfold arg cdl; line_inv)
      h0.symm htl htb h_size
      (approvePrefixImage_nil_length e)
      hwfCallback hreadsCallback hcallback
  exact ⟨callbackPre, by simpa only [h1] using hstor,
    hlogs, hbal, hcode, houtput, hboundary⟩

/-- Compiled public-selector form of `approveAndCall_successEffect`. -/
theorem weth10_approveAndCall_successEffect (dp : DeployParams)
    {e : Sevm} {pre post : Devm} {spender : Adr} {amount : B256}
    {data : Bytes}
    (h_code : some e.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector e = approveAndCallSelector)
    (h_nonempty : e.data.length.toB256 ≠ 0)
    (h_dec : Sevm.DecodesCallWithTail e approveAndCallSelector
      [spender.toB256, amount] data)
    (h_size : 132 + ceil32 data.length < 2 ^ 256)
    (h_wf : Mem.Wf pre.memory)
    (h_fresh : Mem.Reads pre.memory [])
    (exc : Exec 0 e pre (.ok post)) :
    e.value = 0 ∧
      ApproveAndCallSuccessEffect e pre post spender amount data := by
  have h_mem :
      (approveAndCallSelector, nonpayable approveAndCall) ∈
        weth10Funcs dp := by
    simp [approveAndCallSelector, weth10Funcs]
  rcases exec_enters_weth10Nonpayable_logs exc h_code h_sel h_nonempty
      h_mem with
    ⟨bodyPre, hvalue, hstor, hbal, hcodeFrame, hmemory,
      hlogs, houtput, hbody⟩
  have hwfBody : Mem.Wf bodyPre.memory := by
    rw [hmemory]
    exact h_wf
  have hfreshBody : Mem.Reads bodyPre.memory [] := by
    rw [hmemory]
    exact h_fresh
  have heffect := approveAndCall_successEffect dp h_dec h_size
    hwfBody hfreshBody hbody
  refine ⟨hvalue, ?_⟩
  unfold ApproveAndCallSuccessEffect at heffect ⊢
  simpa only [hstor, hbal, hcodeFrame, hlogs, houtput] using heffect

/-! ## Deposit callback -/

/-- Memory frame left by `mintToPrefix`: the amount word used by its
`Transfer` log remains readable for the following callback encoder. -/
private theorem mintToPrefix_memory_frame
    {e : Sevm} {s r : Devm}
    (h_wf : Mem.Wf s.memory)
    (h_fresh : Mem.Reads s.memory [])
    (run : Line.Run e s mintToPrefix r) :
    Mem.Wf r.memory ∧ Mem.Reads r.memory e.value.toBytes := by
  unfold mintToPrefix at run
  rcases of_run_append (addressArg 0) run with ⟨s1, harg1, run1⟩
  have hp1 : normalizedAddressArg e 0 :: [] <<+ s1.stack :=
    by simpa only [normalizedAddressArg] using
      prefix_of_addressArg nil_pref harg1
  rcases Line.of_run_cons run1 with ⟨s2, hload, run2⟩
  rcases prefix_of_sload hload hp1 with ⟨toBal, hp2, _⟩
  rcases Line.of_run_cons run2 with ⟨s3, hvalue1, run3⟩
  have hp3 : e.value :: toBal :: [] <<+ s3.stack :=
    prefix_of_push (of_run_callvalue hvalue1) hp2
  rcases Line.of_run_cons run3 with ⟨s4, hadd, run4⟩
  have hp4 : (e.value + toBal) :: [] <<+ s4.stack :=
    prefix_of_add hadd hp3
  rcases of_run_append (addressArg 0) run4 with
    ⟨s5, harg2, run5⟩
  have hp5 : normalizedAddressArg e 0 :: (e.value + toBal) :: [] <<+
      s5.stack := by simpa only [normalizedAddressArg] using
        prefix_of_addressArg hp4 harg2
  rcases Line.of_run_cons run5 with ⟨s6, hstore, run6⟩
  have _hp6 : [] <<+ s6.stack := prefix_of_sstore hstore hp5
  rcases Line.of_run_cons run6 with ⟨s7, hvalue2, run7⟩
  have hp7 : e.value :: [] <<+ s7.stack :=
    prefix_of_push (of_run_callvalue hvalue2) nil_pref
  rcases of_run_append (mstoreAt 0) run7 with
    ⟨s8, hmstore, run8⟩
  rcases of_run_mstoreAt_val hmstore hp7 with ⟨hp8, hm8⟩
  rcases of_run_append (addressArg 0) run8 with
    ⟨s9, harg3, run9⟩
  have hp9 : normalizedAddressArg e 0 :: [] <<+ s9.stack :=
    by simpa only [normalizedAddressArg] using
      prefix_of_addressArg hp8 harg3
  rcases Line.of_run_cons run9 with ⟨s10, hzero, run10⟩
  have hp10 : (0 : B256) :: normalizedAddressArg e 0 :: [] <<+
      s10.stack := prefix_of_push (of_run_pushB256 hzero) hp9
  rcases Line.of_run_cons run10 with ⟨s11, hevent, hlog⟩
  have hp11 : transferEvent :: (0 : B256) ::
      normalizedAddressArg e 0 :: [] <<+ s11.stack :=
    prefix_of_push (of_run_pushB256 hevent) hp10
  have hmemTo7 : s.memory = s7.memory := by
    calc
      s.memory = s1.memory := Line.of_inv Devm.memory (by
        unfold addressArg normalizeAddress pushAddressMask
        line_inv) harg1
      _ = s2.memory := Ninst.Hinv.inv (f := Devm.memory) hload
      _ = s3.memory := Ninst.Hinv.inv (f := Devm.memory) hvalue1
      _ = s4.memory := Ninst.Hinv.inv (f := Devm.memory) hadd
      _ = s5.memory := Line.of_inv Devm.memory (by
        unfold addressArg normalizeAddress pushAddressMask
        line_inv) harg2
      _ = s6.memory := Ninst.Hinv.inv (f := Devm.memory) hstore
      _ = s7.memory := Ninst.Hinv.inv (f := Devm.memory) hvalue2
  let img := Bytes.writeAt [] 0 e.value.toBytes
  have hwf8 : Mem.Wf s8.memory := by
    rw [hm8, ← hmemTo7]
    exact h_wf.write _ _
  have hreads8 : Mem.Reads s8.memory img := by
    rw [hm8, ← hmemTo7]
    exact Mem.Reads.write h_wf h_fresh 0 _
  have hmem8to11 : s8.memory = s11.memory := by
    calc
      s8.memory = s9.memory := Line.of_inv Devm.memory (by
        unfold addressArg normalizeAddress pushAddressMask
        line_inv) harg3
      _ = s10.memory := Ninst.Hinv.inv (f := Devm.memory) hzero
      _ = s11.memory := Ninst.Hinv.inv (f := Devm.memory) hevent
  have hlogMem := of_logWith201_mem hp11 hlog
  have himg : img = e.value.toBytes := by
    exact Bytes.writeAt_zero_of_le (Nat.zero_le _)
  constructor
  · rw [hlogMem, ← hmem8to11]
    exact hwf8.extend _ _
  · rw [hlogMem, ← hmem8to11, ← himg]
    exact Mem.Reads.extend hreads8 _ _

/-- Raw successful `depositToAndCall` effect.  The mint prefix is exact, while
the callback keeps the dirty target word and the dynamic-tail interpretation
performed by the EVM program itself. -/
def DepositToAndCallRawSuccessEffect (dp : DeployParams) (e : Sevm)
    (pre post : Devm) : Prop :=
  ∃ callbackPre inputSize input,
    Devm.getStor callbackPre e.currentTarget =
        (Devm.getStor pre e.currentTarget).set
          (normalizedAddressArg e 0)
          (e.value + (Devm.getStor pre e.currentTarget).get
            (normalizedAddressArg e 0)) ∧
    callbackPre.logs = pre.logs ++ [mintToTransferLog e] ∧
    Devm.getBal callbackPre = Devm.getBal pre ∧
    Devm.getCode callbackPre = Devm.getCode pre ∧
    callbackPre.output = pre.output ∧
    RawTokenCallbackBoundary dp e e.currentTarget
      (Sevm.argWord e 0).toAdr (Sevm.argWord e 0)
      onTokenTransferSelector e.value (Sevm.tailLen e 1) inputSize
      (Sevm.tailBytes e 1) input callbackPre post

/-- Selected-body raw `depositToAndCall`: exact normalized mint prefix and
the actual modular callback input, with no canonical ABI-tail premise. -/
theorem depositToAndCall_rawSuccessEffect (dp : DeployParams)
    {e : Sevm} {pre post : Devm}
    (h_wf : Mem.Wf pre.memory)
    (h_fresh : Mem.Reads pre.memory [])
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e pre
      depositToAndCall post) :
    DepositToAndCallRawSuccessEffect dp e pre post := by
  simp only [depositToAndCall] at run
  rcases of_run_prepend mintToPrefix _ run with
    ⟨callbackPre, hprefix, hcallback⟩
  rcases mintToPrefix_effect h_wf h_fresh hprefix with
    ⟨hstor, hlogs, hbal, hcode, houtput⟩
  rcases mintToPrefix_memory_frame h_wf h_fresh hprefix with
    ⟨hwfCallback, hreadsCallback⟩
  rcases callBoolCallback_rawBoundary dp onTokenTransferSelector 0 1
      e.value [callvalue]
      (by
        intro a b xs hp hline
        rcases Line.of_run_cons hline with ⟨c, hcv, hnil⟩
        cases hnil
        exact prefix_of_push (of_run_callvalue hcv) hp)
      (by line_inv) (by line_inv) (by line_inv) (by line_inv)
      (by
        intro e' a b hline
        rcases Line.of_run_cons hline with ⟨c, hcv, hnil⟩
        cases hnil
        exact (of_run_callvalue hcv).logs)
      (by
        intro e' a b hline
        rcases Line.of_run_cons hline with ⟨c, hcv, hnil⟩
        cases hnil
        exact (of_run_callvalue hcv).output)
      hwfCallback hreadsCallback hcallback with
    ⟨inputSize, input, hboundary⟩
  exact ⟨callbackPre, inputSize, input, hstor, hlogs, hbal, hcode,
    houtput, hboundary⟩

/-- Compiled public-selector form of
`depositToAndCall_rawSuccessEffect`. -/
theorem weth10_depositToAndCall_rawSuccessEffect (dp : DeployParams)
    {e : Sevm} {pre post : Devm}
    (h_code : some e.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector e = depositToAndCallSelector)
    (h_nonempty : e.data.length.toB256 ≠ 0)
    (h_wf : Mem.Wf pre.memory)
    (h_fresh : Mem.Reads pre.memory [])
    (exc : Exec 0 e pre (.ok post)) :
    DepositToAndCallRawSuccessEffect dp e pre post := by
  have h_mem :
      (depositToAndCallSelector, depositToAndCall) ∈ weth10Funcs dp := by
    simp [depositToAndCallSelector, weth10Funcs]
  rcases exec_enters_weth10Selector_logs exc h_code h_sel h_nonempty
      h_mem with
    ⟨bodyPre, hstor, hbal, hcodeFrame, hmemory, hlogs, houtput, hbody⟩
  have hwfBody : Mem.Wf bodyPre.memory := by
    rw [hmemory]
    exact h_wf
  have hfreshBody : Mem.Reads bodyPre.memory [] := by
    rw [hmemory]
    exact h_fresh
  have heffect := depositToAndCall_rawSuccessEffect dp
    hwfBody hfreshBody hbody
  unfold DepositToAndCallRawSuccessEffect at heffect ⊢
  simpa only [hstor, hbal, hcodeFrame, hlogs, houtput] using heffect

/-- Exact successful `depositToAndCall` effect.  The credited balance and mint
event are already visible at callback entry, while the child and its reentrant
logs are retained by `TokenCallbackBoundary`. -/
def DepositToAndCallSuccessEffect (e : Sevm) (pre post : Devm)
    (recipient : Adr) (data : Bytes) : Prop :=
  ∃ callbackPre,
    recipient.toB256 = normalizedAddressArg e 0 ∧
    Devm.getStor callbackPre e.currentTarget =
        (Devm.getStor pre e.currentTarget).set
          (normalizedAddressArg e 0)
          (e.value + (Devm.getStor pre e.currentTarget).get
            (normalizedAddressArg e 0)) ∧
    callbackPre.logs = pre.logs ++ [mintToTransferLog e] ∧
    Devm.getBal callbackPre = Devm.getBal pre ∧
    Devm.getCode callbackPre = Devm.getCode pre ∧
    callbackPre.output = pre.output ∧
    TokenCallbackBoundary e e.currentTarget recipient
      onTokenTransferSelector e.value data callbackPre post

/-- Selected-body `depositToAndCall`: exact normalized credit and mint log,
canonical payable callback calldata, arbitrary child-log interleaving, and the
normalized Boolean outer return. -/
theorem depositToAndCall_successEffect (dp : DeployParams)
    {e : Sevm} {pre post : Devm} {recipient : Adr} {data : Bytes}
    (h_dec : Sevm.DecodesCallWithTail e depositToAndCallSelector
      [recipient.toB256] data)
    (h_size : 132 + ceil32 data.length < 2 ^ 256)
    (h_wf : Mem.Wf pre.memory)
    (h_fresh : Mem.Reads pre.memory [])
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e pre
      depositToAndCall post) :
    DepositToAndCallSuccessEffect e pre post recipient data := by
  have h_data_len : data.length < 2 ^ 256 := by
    have hceil := Nat.le_ceil32 data.length
    omega
  have h0 := argWord_zero_of_decodesOne h_dec
  have htl := tailLen_one_of_decodes h_dec
  have htb := tailBytes_one_of_decodes h_data_len h_dec
  have hrecipient : recipient.toB256 = normalizedAddressArg e 0 := by
    unfold normalizedAddressArg
    rw [h0, normalize_adr_toB256]
  simp only [depositToAndCall] at run
  rcases of_run_prepend mintToPrefix _ run with
    ⟨callbackPre, hprefix, hcallback⟩
  rcases mintToPrefix_effect h_wf h_fresh hprefix with
    ⟨hstor, hlogs, hbal, hcode, houtput⟩
  rcases mintToPrefix_memory_frame h_wf h_fresh hprefix with
    ⟨hwfCallback, hreadsCallback⟩
  have hboundary :
      TokenCallbackBoundary e e.currentTarget recipient
        onTokenTransferSelector e.value data callbackPre post :=
    callBoolCallback_successEffect dp onTokenTransferSelector 0 1 e.value
      [callvalue]
      (by
        intro a b xs hp hline
        rcases Line.of_run_cons hline with ⟨c, hcv, hnil⟩
        cases hnil
        exact prefix_of_push (of_run_callvalue hcv) hp)
      (by line_inv) (by line_inv) (by line_inv)
      (by line_inv)
      (by
        intro e' a b hline
        rcases Line.of_run_cons hline with ⟨c, hcv, hnil⟩
        cases hnil
        exact (of_run_callvalue hcv).logs)
      (by
        intro e' a b hline
        rcases Line.of_run_cons hline with ⟨c, hcv, hnil⟩
        cases hnil
        exact (of_run_callvalue hcv).output)
      h0.symm htl htb h_size
      (by rw [B256.length_toBytes]; omega)
      hwfCallback hreadsCallback hcallback
  exact ⟨callbackPre, hrecipient, hstor, hlogs, hbal, hcode,
    houtput, hboundary⟩

/-- Compiled public-selector form of `depositToAndCall_successEffect`. -/
theorem weth10_depositToAndCall_successEffect (dp : DeployParams)
    {e : Sevm} {pre post : Devm} {recipient : Adr} {data : Bytes}
    (h_code : some e.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector e = depositToAndCallSelector)
    (h_nonempty : e.data.length.toB256 ≠ 0)
    (h_dec : Sevm.DecodesCallWithTail e depositToAndCallSelector
      [recipient.toB256] data)
    (h_size : 132 + ceil32 data.length < 2 ^ 256)
    (h_wf : Mem.Wf pre.memory)
    (h_fresh : Mem.Reads pre.memory [])
    (exc : Exec 0 e pre (.ok post)) :
    DepositToAndCallSuccessEffect e pre post recipient data := by
  have h_mem :
      (depositToAndCallSelector, depositToAndCall) ∈ weth10Funcs dp := by
    simp [depositToAndCallSelector, weth10Funcs]
  rcases exec_enters_weth10Selector_logs exc h_code h_sel h_nonempty
      h_mem with
    ⟨bodyPre, hstor, hbal, hcodeFrame, hmemory, hlogs, houtput, hbody⟩
  have hwfBody : Mem.Wf bodyPre.memory := by
    rw [hmemory]
    exact h_wf
  have hfreshBody : Mem.Reads bodyPre.memory [] := by
    rw [hmemory]
    exact h_fresh
  have heffect := depositToAndCall_successEffect dp h_dec h_size
    hwfBody hfreshBody hbody
  unfold DepositToAndCallSuccessEffect at heffect ⊢
  simpa only [hstor, hbal, hcodeFrame, hlogs, houtput] using heffect

/-! ## Transfer callback -/

/-- Raw successful `transferAndCall` effect.  The branch is selected by the
unmodified target word: raw zero performs the redemption prefix, while every
raw nonzero word performs a transfer to its normalized storage recipient.  In
both arms the callback retains that same raw word and the actual dynamic-tail
memory window. -/
def TransferAndCallRawSuccessEffect (dp : DeployParams) (e : Sevm)
    (pre post : Devm) : Prop :=
  (Sevm.argWord e 0 = 0 ∧
    ∃ callPre callbackPre inputSize input,
      BurnCallPrefix e pre callPre callbackPre e.caller
        (Sevm.argWord e 1) e.caller.toB256 ∧
      RawTokenCallbackBoundary dp e e.currentTarget
        (Sevm.argWord e 0).toAdr (Sevm.argWord e 0)
        onTokenTransferSelector (Sevm.argWord e 1)
        (Sevm.tailLen e 2) inputSize (Sevm.tailBytes e 2) input
        callbackPre post) ∨
  (Sevm.argWord e 0 ≠ 0 ∧
    ∃ recipient callbackPre inputSize input,
      recipient.toB256 = normalizedAddressArg e 0 ∧
      Transfer (Stor.rest (Devm.getStor pre e.currentTarget))
        e.caller (Sevm.argWord e 1) recipient
        (Stor.rest (Devm.getStor callbackPre e.currentTarget)) ∧
      (Devm.getStor callbackPre e.currentTarget).get flashMintedSlot =
        (Devm.getStor pre e.currentTarget).get flashMintedSlot ∧
      callbackPre.logs = pre.logs ++
        [ordinaryTransferLog e e.caller.toB256
          (normalizedAddressArg e 0) (Sevm.argWord e 1)] ∧
      Devm.getBal callbackPre = Devm.getBal pre ∧
      Devm.getCode callbackPre = Devm.getCode pre ∧
      callbackPre.output = pre.output ∧
      RawTokenCallbackBoundary dp e e.currentTarget
        (Sevm.argWord e 0).toAdr (Sevm.argWord e 0)
        onTokenTransferSelector (Sevm.argWord e 1)
        (Sevm.tailLen e 2) inputSize (Sevm.tailBytes e 2) input
        callbackPre post)

/-- Selected-body raw `transferAndCall`: exact raw-zero redemption or
raw-nonzero normalized transfer prefix, followed by the actual modular
callback input. -/
theorem transferAndCall_rawSuccessEffect (dp : DeployParams)
    {e : Sevm} {pre post : Devm}
    (h_wf : Mem.Wf pre.memory)
    (h_fresh : Mem.Reads pre.memory [])
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e pre
      transferAndCall post) :
    TransferAndCallRawSuccessEffect dp e pre post := by
  simp only [transferAndCall] at run
  rcases transferThen_callbackPrefix_effect dp h_wf h_fresh run with
      hzero | hnonzero
  · rcases hzero with
      ⟨hargZero, callPre, callbackPre, img, hprefix, _hlen,
        hwfCallback, hreadsCallback, hcallback⟩
    rcases callBoolCallback_rawBoundary dp onTokenTransferSelector 0 2
        (Sevm.argWord e 1) (arg 1)
        (by
          intro a b xs hp hline
          exact prefix_of_arg hp hline)
        (by unfold arg cdl; line_inv)
        (by unfold arg cdl; line_inv)
        (by unfold arg cdl; line_inv)
        (by unfold arg cdl; line_inv)
        (by unfold arg cdl; line_inv)
        (by unfold arg cdl; line_inv)
        hwfCallback hreadsCallback hcallback with
      ⟨inputSize, input, hboundary⟩
    exact Or.inl ⟨hargZero, callPre, callbackPre, inputSize, input,
      hprefix, hboundary⟩
  · rcases hnonzero with
      ⟨hargNonzero, recipient, callbackPre, img,
        hrecipient, htransfer, hflash, hlogs, hbal, hcode,
        houtput, _hlen, hwfCallback, hreadsCallback, hcallback⟩
    rcases callBoolCallback_rawBoundary dp onTokenTransferSelector 0 2
        (Sevm.argWord e 1) (arg 1)
        (by
          intro a b xs hp hline
          exact prefix_of_arg hp hline)
        (by unfold arg cdl; line_inv)
        (by unfold arg cdl; line_inv)
        (by unfold arg cdl; line_inv)
        (by unfold arg cdl; line_inv)
        (by unfold arg cdl; line_inv)
        (by unfold arg cdl; line_inv)
        hwfCallback hreadsCallback hcallback with
      ⟨inputSize, input, hboundary⟩
    exact Or.inr ⟨hargNonzero, recipient, callbackPre, inputSize,
      input, hrecipient, htransfer, hflash, hlogs, hbal, hcode,
      houtput, hboundary⟩

/-- Compiled public-selector form of
`transferAndCall_rawSuccessEffect`. -/
theorem weth10_transferAndCall_rawSuccessEffect (dp : DeployParams)
    {e : Sevm} {pre post : Devm}
    (h_code : some e.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector e = transferAndCallSelector)
    (h_nonempty : e.data.length.toB256 ≠ 0)
    (h_wf : Mem.Wf pre.memory)
    (h_fresh : Mem.Reads pre.memory [])
    (exc : Exec 0 e pre (.ok post)) :
    e.value = 0 ∧ TransferAndCallRawSuccessEffect dp e pre post := by
  have h_mem :
      (transferAndCallSelector, nonpayable transferAndCall) ∈
        weth10Funcs dp := by
    simp [transferAndCallSelector, weth10Funcs]
  rcases exec_enters_weth10Nonpayable_logs exc h_code h_sel h_nonempty
      h_mem with
    ⟨bodyPre, hvalue, hstor, hbal, hcodeFrame, hmemory,
      hlogs, houtput, hbody⟩
  have hwfBody : Mem.Wf bodyPre.memory := by
    rw [hmemory]
    exact h_wf
  have hfreshBody : Mem.Reads bodyPre.memory [] := by
    rw [hmemory]
    exact h_fresh
  have heffect := transferAndCall_rawSuccessEffect dp
    hwfBody hfreshBody hbody
  refine ⟨hvalue, ?_⟩
  rcases heffect with hzero | hnonzero
  · rcases hzero with
      ⟨hargZero, callPre, callbackPre, inputSize, input,
        hprefix, hboundary⟩
    exact Or.inl ⟨hargZero, callPre, callbackPre, inputSize, input,
      hprefix.of_entry_eq hstor.symm hbal.symm hcodeFrame.symm
        hlogs.symm houtput.symm,
      hboundary⟩
  · exact Or.inr (by
      simpa only [hstor, hbal, hcodeFrame, hlogs, houtput] using
        hnonzero)

/-- Exact successful `transferAndCall` effect.  The raw-zero branch burns and
sends ETH before the token callback; the raw-nonzero branch transfers tagged
storage directly.  In both cases the callback boundary exposes the exact state
and logs visible to the child and the child's final effects. -/
def TransferAndCallSuccessEffect (e : Sevm) (pre post : Devm)
    (recipient : Adr) (amount : B256) (data : Bytes) : Prop :=
  (Sevm.argWord e 0 = 0 ∧
    ∃ callPre callbackPre,
      BurnCallPrefix e pre callPre callbackPre e.caller amount
        e.caller.toB256 ∧
      TokenCallbackBoundary e e.currentTarget recipient
        onTokenTransferSelector amount data callbackPre post) ∨
  (Sevm.argWord e 0 ≠ 0 ∧
    ∃ callbackPre,
      recipient.toB256 = normalizedAddressArg e 0 ∧
      Transfer (Stor.rest (Devm.getStor pre e.currentTarget))
        e.caller amount recipient
        (Stor.rest (Devm.getStor callbackPre e.currentTarget)) ∧
      (Devm.getStor callbackPre e.currentTarget).get flashMintedSlot =
        (Devm.getStor pre e.currentTarget).get flashMintedSlot ∧
      callbackPre.logs = pre.logs ++
        [ordinaryTransferLog e e.caller.toB256
          (normalizedAddressArg e 0) amount] ∧
      Devm.getBal callbackPre = Devm.getBal pre ∧
      Devm.getCode callbackPre = Devm.getCode pre ∧
      callbackPre.output = pre.output ∧
      TokenCallbackBoundary e e.currentTarget recipient
        onTokenTransferSelector amount data callbackPre post)

/-- Selected-body `transferAndCall`: exact zero/nonzero transfer prefix,
canonical callback calldata and target, arbitrary child-log interleaving, final
world/ETH state, and normalized Boolean outer return. -/
theorem transferAndCall_successEffect (dp : DeployParams)
    {e : Sevm} {pre post : Devm} {recipient : Adr} {amount : B256}
    {data : Bytes}
    (h_dec : Sevm.DecodesCallWithTail e transferAndCallSelector
      [recipient.toB256, amount] data)
    (h_size : 132 + ceil32 data.length < 2 ^ 256)
    (h_wf : Mem.Wf pre.memory)
    (h_fresh : Mem.Reads pre.memory [])
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e pre
      transferAndCall post) :
    TransferAndCallSuccessEffect e pre post recipient amount data := by
  have h_data_len : data.length < 2 ^ 256 := by
    have hceil := Nat.le_ceil32 data.length
    omega
  have h0 := argWord_zero_of_decodesTwo h_dec
  have h1 := argWord_one_of_decodesTwo h_dec
  have htl := tailLen_two_of_decodes h_dec
  have htb := tailBytes_two_of_decodes h_data_len h_dec
  have hrecipient : recipient.toB256 = normalizedAddressArg e 0 := by
    unfold normalizedAddressArg
    rw [h0, normalize_adr_toB256]
  simp only [transferAndCall] at run
  rcases transferThen_callbackPrefix_effect dp h_wf h_fresh run with
      hzero | hnonzero
  · rcases hzero with
      ⟨hargZero, callPre, callbackPre, img, hprefix, hlen,
        hwfCallback, hreadsCallback, hcallback⟩
    have hboundary :
        TokenCallbackBoundary e e.currentTarget recipient
          onTokenTransferSelector amount data callbackPre post :=
      callBoolCallback_successEffect dp onTokenTransferSelector 0 2 amount
        (arg 1)
        (by
          intro a b xs hp hline
          rw [← h1]
          exact prefix_of_arg hp hline)
        (by unfold arg cdl; line_inv)
        (by unfold arg cdl; line_inv)
        (by unfold arg cdl; line_inv)
        (by unfold arg cdl; line_inv)
        (by unfold arg cdl; line_inv)
        (by unfold arg cdl; line_inv)
        h0.symm htl htb h_size hlen hwfCallback hreadsCallback hcallback
    exact Or.inl ⟨hargZero, callPre, callbackPre,
      by simpa only [h1] using hprefix, hboundary⟩
  · rcases hnonzero with
      ⟨hargNonzero, actualRecipient, callbackPre, img,
        hactualRecipient, htransfer, hflash, hlogs, hbal, hcode,
        houtput, hlen, hwfCallback, hreadsCallback, hcallback⟩
    have hrecipientEq : actualRecipient = recipient :=
      Adr.toB256_inj (hactualRecipient.trans hrecipient.symm)
    subst actualRecipient
    have hboundary :
        TokenCallbackBoundary e e.currentTarget recipient
          onTokenTransferSelector amount data callbackPre post :=
      callBoolCallback_successEffect dp onTokenTransferSelector 0 2 amount
        (arg 1)
        (by
          intro a b xs hp hline
          rw [← h1]
          exact prefix_of_arg hp hline)
        (by unfold arg cdl; line_inv)
        (by unfold arg cdl; line_inv)
        (by unfold arg cdl; line_inv)
        (by unfold arg cdl; line_inv)
        (by unfold arg cdl; line_inv)
        (by unfold arg cdl; line_inv)
        h0.symm htl htb h_size hlen hwfCallback hreadsCallback hcallback
    exact Or.inr ⟨hargNonzero, callbackPre, hrecipient,
      by simpa only [h1] using htransfer, hflash,
      by simpa only [h1] using hlogs, hbal, hcode, houtput, hboundary⟩

/-- Compiled public-selector form of `transferAndCall_successEffect`. -/
theorem weth10_transferAndCall_successEffect (dp : DeployParams)
    {e : Sevm} {pre post : Devm} {recipient : Adr} {amount : B256}
    {data : Bytes}
    (h_code : some e.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector e = transferAndCallSelector)
    (h_nonempty : e.data.length.toB256 ≠ 0)
    (h_dec : Sevm.DecodesCallWithTail e transferAndCallSelector
      [recipient.toB256, amount] data)
    (h_size : 132 + ceil32 data.length < 2 ^ 256)
    (h_wf : Mem.Wf pre.memory)
    (h_fresh : Mem.Reads pre.memory [])
    (exc : Exec 0 e pre (.ok post)) :
    e.value = 0 ∧
      TransferAndCallSuccessEffect e pre post recipient amount data := by
  have h_mem :
      (transferAndCallSelector, nonpayable transferAndCall) ∈
        weth10Funcs dp := by
    simp [transferAndCallSelector, weth10Funcs]
  rcases exec_enters_weth10Nonpayable_logs exc h_code h_sel h_nonempty
      h_mem with
    ⟨bodyPre, hvalue, hstor, hbal, hcodeFrame, hmemory,
      hlogs, houtput, hbody⟩
  have hwfBody : Mem.Wf bodyPre.memory := by
    rw [hmemory]
    exact h_wf
  have hfreshBody : Mem.Reads bodyPre.memory [] := by
    rw [hmemory]
    exact h_fresh
  have heffect := transferAndCall_successEffect dp h_dec h_size
    hwfBody hfreshBody hbody
  refine ⟨hvalue, ?_⟩
  rcases heffect with hzero | hnonzero
  · rcases hzero with
      ⟨hargZero, callPre, callbackPre, hprefix, hboundary⟩
    exact Or.inl ⟨hargZero, callPre, callbackPre,
      hprefix.of_entry_eq hstor.symm hbal.symm hcodeFrame.symm
        hlogs.symm houtput.symm,
      hboundary⟩
  · exact Or.inr (by
      simpa only [hstor, hbal, hcodeFrame, hlogs, houtput] using hnonzero)

/-! ## Shared ERC-677 failure links -/

/-- Any of the three ERC-677 callbacks empty-reverts after its exact
`EXTCODESIZE` check reports a codeless target; no child `CALL` is reached. -/
theorem erc677_codelessCallback_runCompiledTo
    {dp : DeployParams} {e : Sevm} {base : Devm} {G : Nat}
    {stack : List B256} {sel targetArg dataArg : B256} {value : Line}
    (h_room : stack.length < 1022) :
    Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) e
      (base.setMach ⟨0 :: stack, base.memory,
        G + codelessCallbackCost⟩)
      (iszero ::: Func.rev <?>
        (pop ::: value +++ storeTokenCallbackHead sel +++
          pushList [0, 0] +++ forwardArgTail dataArg 4 +++
          tokenCallbackArgsSize +++
          pushB256 callbackArgsOffset ::: pushB256 0 :::
          arg targetArg +++ gas ::: call ::: .call boolReturnSlot))
      (.error (.revert,
        (base.setMach ⟨stack, base.memory, G⟩).withOutput [])) := by
  exact codelessCallback_runCompiledTo h_room

/-- All three ERC-677 endpoints use the same Boolean auxiliary, so a failed
child bubbles its returndata byte-for-byte. -/
theorem erc677_childRevert_runCompiledTo
    {dp : DeployParams} {e : Sevm} {base : Devm} {G : Nat}
    {stack : List B256} {img : Bytes}
    (h_wf : Mem.Wf base.memory) (h_reads : Mem.Reads base.memory img)
    (h_align : base.memory.size % 32 = 0)
    (h_len : base.returnData.length < 2 ^ 256)
    (h_room : stack.length < 1021) :
    Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) e
      (base.setMach
        ⟨0 :: stack, base.memory, G + bubbleContinuationCost base⟩)
      boolReturn
      (.error (.revert,
        (base.setMach
          ⟨stack, base.memory.write 0 base.returnData, G⟩).withOutput
            base.returnData)) := by
  exact boolReturn_childRevert_runCompiledTo
    h_wf h_reads h_align h_len h_room

/-- All three ERC-677 endpoints empty-revert when a successful child returns
fewer than the Boolean decoder's required 32 bytes. -/
theorem erc677_shortReturn_runCompiledTo
    {dp : DeployParams} {e : Sevm} {base : Devm} {G : Nat}
    {stack : List B256}
    (h_short : base.returnData.length < 32)
    (h_room : stack.length < 1020) :
    Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) e
      (base.setMach ⟨1 :: stack, base.memory, G + shortReturnCost⟩)
      boolReturn
      (.error (.revert,
        (base.setMach ⟨stack, base.memory, G⟩).withOutput [])) := by
  exact boolReturn_short_runCompiledTo h_short h_room

end Weth10

end Blanc
