-- Weth10Deploy.lean : generic fresh-deployment initcode for WETH10.
--
-- The installed Solidity initcode is provenance, not a compatibility surface.
-- This constructor returns the same parameterized Blanc runtime family while
-- deriving both deployment immutables from CHAINID and ADDRESS at creation.

import Blanc.Weth10DeployDomainSlices
import Blanc.Weth10DeployUpperSlices
import Blanc.Weth10TemplateCode
import Mathlib.Tactic.IntervalCases

namespace Blanc

open Jaune

namespace Weth10

/-! ## Deployment parameter derivation -/

/-- The constructor-time EIP-712 separator, encoded as five ABI words. -/
def deploymentDomainSeparator
    (chainId : B256) (contractAddress : Adr) : B256 :=
  (DOMAIN_TYPEHASH.toBytes ++ NAME_HASH.toBytes ++ VERSION_HASH.toBytes ++
    chainId.toBytes ++ contractAddress.toB256.toBytes).keccak

/-- The runtime parameters derived by a fresh deployment. -/
def freshDeployParams
    (chainId : B256) (contractAddress : Adr) : DeployParams :=
  ⟨chainId, deploymentDomainSeparator chainId contractAddress⟩

@[simp] theorem freshDeployParams_deploymentChainId
    (chainId : B256) (contractAddress : Adr) :
    (freshDeployParams chainId contractAddress).deploymentChainId = chainId :=
  rfl

@[simp] theorem freshDeployParams_cachedDomainSeparator
    (chainId : B256) (contractAddress : Adr) :
    (freshDeployParams chainId contractAddress).cachedDomainSeparator =
      deploymentDomainSeparator chainId contractAddress :=
  rfl

/-! ## Initcode emitter

The constructor first rejects nonzero endowment, copies the all-zero member of
the fixed-width runtime family into memory, patches every generated deployment
word span, and returns that runtime.  Scratch memory starts at the next 32-byte
boundary after the runtime, so hashing cannot alter returned code.
-/

private def initPush2 (n : Nat) : Bytes :=
  [0x61, (n >>> 8).toUInt8, n.toUInt8]

private def initPush32 (w : B256) : Bytes := 0x7f :: w.toBytes

private abbrev align32 (n : Nat) : Nat := ((n + 31) / 32) * 32

/-- Re-read `CHAINID` for each fixed-width occurrence and store the word into
the copied runtime. -/
private def patchChainWords (offsets : List Nat) : Bytes :=
  offsets.flatMap fun off => [0x46] ++ initPush2 off ++ [0x52]

/-- Store the separator currently on the stack at every generated occurrence,
then discard the retained source word. -/
private def patchStackWord (offsets : List Nat) : Bytes :=
  offsets.flatMap (fun off => [0x80] ++ initPush2 off ++ [0x52]) ++ [0x50]

private def deploymentPrefix
    (runtimeLength codeOffset : Nat) : Bytes :=
  let scratch := align32 runtimeLength
  -- CALLVALUE; ISZERO; branch to pc 9; otherwise empty REVERT.
  [0x34, 0x15] ++ initPush2 9 ++ [0x57, 0x5f, 0x5f, 0xfd, 0x5b] ++
  -- Copy the zero-parameter runtime tail to memory offset zero.
  initPush2 runtimeLength ++ initPush2 codeOffset ++ [0x5f, 0x39] ++
  patchChainWords deploymentChainIdWordOffsets ++
  -- keccak256(abi.encode(typeHash, nameHash, versionHash, chainid, address)).
  initPush32 DOMAIN_TYPEHASH ++ initPush2 scratch ++ [0x52] ++
  initPush32 NAME_HASH ++ initPush2 (scratch + 32) ++ [0x52] ++
  initPush32 VERSION_HASH ++ initPush2 (scratch + 64) ++ [0x52] ++
  [0x46] ++ initPush2 (scratch + 96) ++ [0x52] ++
  [0x30] ++ initPush2 (scratch + 128) ++ [0x52] ++
  initPush2 160 ++ initPush2 scratch ++ [0x20] ++
  patchStackWord cachedDomainSeparatorWordOffsets ++
  -- Return only the patched runtime; scratch memory is outside this window.
  initPush2 runtimeLength ++ [0x5f, 0xf3]

/-- Stable zero-parameter template whose generated word spans are patched by
the constructor.  The body is the generated literal so that kernel-side
computation over the template runs on a literal byte list; the witness below
keeps the identity with the compiled family kernel-checked. -/
def weth10RuntimeTemplate : Bytes := weth10TemplateCode

private theorem weth10RuntimeTemplate_eq_code :
    weth10RuntimeTemplate = weth10Code ⟨0, 0⟩ := by
  unfold weth10Code
  rw [weth10TemplateCode_compile]
  rfl

/-- Overlay one deployment word at every generated fixed-width runtime span. -/
def patchRuntimeWords (runtime : Bytes) (word : B256)
    (offsets : List Nat) : Bytes :=
  offsets.foldl (fun bs off => Bytes.writeAt bs off word.toBytes) runtime

/-- The runtime image produced by constructor patching, before it is returned
from memory.  The offsets are generated beside `weth10Code`, so this definition
cannot silently drift from the compiled family. -/
def weth10PatchedRuntime (chainId domainSeparator : B256) : Bytes :=
  patchRuntimeWords
    (patchRuntimeWords weth10RuntimeTemplate chainId
      deploymentChainIdWordOffsets)
    domainSeparator cachedDomainSeparatorWordOffsets

/-- Constructor instructions.  Its own length is the runtime tail's CODECOPY
source offset; every immediate has fixed width, so one sizing pass suffices. -/
def weth10InitPrefix : Bytes :=
  let provisional := deploymentPrefix weth10RuntimeTemplate.length 0
  deploymentPrefix weth10RuntimeTemplate.length provisional.length

/-- Generic WETH10 creation bytecode. -/
def weth10InitCode : Bytes := weth10InitPrefix ++ weth10RuntimeTemplate

/-! ## Static artifact connections

These equations identify the creation artifact and its compiled-runtime tail.
They do not claim that Jaune's creation interpreter executes the hand-emitted
prefix to that tail; that is a separate semantic crossing. -/

/-- The zero-parameter template is the complete suffix of the initcode. -/
theorem weth10InitCode_drop_prefix :
    weth10InitCode.drop weth10InitPrefix.length = weth10RuntimeTemplate := by
  simp [weth10InitCode]

/-- The initcode consists of exactly the prefix and runtime-template lengths. -/
theorem weth10InitCode_length_add :
    weth10InitCode.length =
      weth10InitPrefix.length + weth10RuntimeTemplate.length := by
  simp [weth10InitCode]

/-- The zero-parameter runtime template used as the initcode tail is 6,313
bytes. -/
theorem weth10RuntimeTemplate_length : weth10RuntimeTemplate.length = 6313 := by
  unfold weth10RuntimeTemplate
  decide +kernel

private def compileShapeByteSize : Func.CompileShape → Nat
  | .last => 1
  | .next size rest => compileShapeByteSize rest + size
  | .branch left right =>
      compileShapeByteSize left + compileShapeByteSize right + 5
  | .call _ => 4

private theorem compileShapeByteSize_eq (p : Func) :
    compileShapeByteSize p.compileShape = compsize p := by
  induction p with
  | last => rfl
  | next i p ih =>
      simp [Func.compileShape, compileShapeByteSize, compsize, ih,
        Ninst.size_eq_length_toBytes]
  | branch p q ihp ihq =>
      simp [Func.compileShape, compileShapeByteSize, compsize, ihp, ihq]
  | call => rfl

private def programShapeByteSize (s : Prog.CompileShape) : Nat :=
  1 + compileShapeByteSize s.main +
    (s.aux.map fun f => 1 + compileShapeByteSize f).sum

private theorem programShapeByteSize_eq (p : Prog) :
    programShapeByteSize p.compileShape =
      ((p.main :: p.aux).map fun f => 1 + compsize f).sum := by
  simp [Prog.compileShape, programShapeByteSize, compileShapeByteSize_eq,
    List.map_map, Function.comp_def, Nat.add_assoc]

/-- Fixed-width deployment words preserve the 6,313-byte length of every
member of the parameterized runtime family. -/
theorem weth10Code_length (dp : DeployParams) :
    (weth10Code dp).length = 6313 := by
  calc
    (weth10Code dp).length =
        programShapeByteSize (weth10 dp).compileShape :=
      (Prog.length_compile (weth10Code_compile dp)).trans
        (programShapeByteSize_eq (weth10 dp)).symm
    _ = programShapeByteSize (weth10 ⟨0, 0⟩).compileShape :=
      congrArg programShapeByteSize (weth10_compileShape_eq_zero dp)
    _ = (weth10Code ⟨0, 0⟩).length :=
      ((Prog.length_compile (weth10Code_compile ⟨0, 0⟩)).trans
        (programShapeByteSize_eq (weth10 ⟨0, 0⟩)).symm).symm
    _ = weth10RuntimeTemplate.length :=
      (congrArg List.length weth10RuntimeTemplate_eq_code).symm
    _ = 6313 := weth10RuntimeTemplate_length

private theorem weth10Code_eq_emitUnchecked (dp : DeployParams) :
    weth10Code dp = (weth10 dp).emitUnchecked :=
  Prog.compile_eq_emitUnchecked (weth10Code_compile dp)

private theorem weth10Code_eq_emitByShape (dp : DeployParams) :
    weth10Code dp =
      Prog.emitByShape (weth10 dp).compileShape (weth10 dp) :=
  (weth10Code_eq_emitUnchecked dp).trans
    (Prog.emitByShape_compileShape (weth10 dp)).symm

private theorem weth10Code_eq_emitByZeroShape (dp : DeployParams) :
    weth10Code dp =
      Prog.emitByShape (weth10 (⟨0, 0⟩ : DeployParams)).compileShape
        (weth10 dp) := by
  rw [weth10Code_eq_emitByShape, weth10_compileShape_eq_zero dp]

private def runtimeChunks (bs : Bytes) : Bytes :=
  bs.take 372 ++ (bs.drop 372).take 32 ++
  (bs.drop 404).take 132 ++ (bs.drop 536).take 32 ++
  (bs.drop 568).take 123 ++ (bs.drop 691).take 32 ++
  (bs.drop 723).take 2152 ++ (bs.drop 2875).take 32 ++
  (bs.drop 2907).take 132 ++ (bs.drop 3039).take 32 ++
  bs.drop 3071

private theorem runtimeChunks_eq (bs : Bytes) : runtimeChunks bs = bs := by
  simp only [runtimeChunks, ← List.take_add, Nat.reduceAdd,
    List.take_append_drop]

private def runtimeSlices (bs : Bytes) : Bytes :=
  bs.sliceD 0 372 0 ++ bs.sliceD 372 32 0 ++
  bs.sliceD 404 132 0 ++ bs.sliceD 536 32 0 ++
  bs.sliceD 568 123 0 ++ bs.sliceD 691 32 0 ++
  bs.sliceD 723 2152 0 ++ bs.sliceD 2875 32 0 ++
  bs.sliceD 2907 132 0 ++ bs.sliceD 3039 32 0 ++
  bs.sliceD 3071 3242 0

private theorem runtimeSlices_eq (bs : Bytes) (hlen : bs.length = 6313) :
    runtimeSlices bs = bs := by
  unfold runtimeSlices List.sliceD
  repeat rw [List.takeD_eq_take _ (by
    simp only [List.length_drop]
    omega)]
  simp [← List.take_add]
  omega

private def runtimeSegments (chainId domainSeparator : B256) : Bytes :=
  weth10RuntimeTemplate.take 372 ++ chainId.toBytes ++
  (weth10RuntimeTemplate.drop 404).take 132 ++ domainSeparator.toBytes ++
  (weth10RuntimeTemplate.drop 568).take 123 ++ chainId.toBytes ++
  (weth10RuntimeTemplate.drop 723).take 2152 ++ chainId.toBytes ++
  (weth10RuntimeTemplate.drop 2907).take 132 ++ domainSeparator.toBytes ++
  weth10RuntimeTemplate.drop 3071

private lemma Bytes.writeAt_append_middle
    {pre old post new : Bytes}
    (hlen : old.length = new.length) :
    Bytes.writeAt (pre ++ old ++ post) pre.length new =
      pre ++ new ++ post := by
  unfold Bytes.writeAt
  rw [List.takeD_eq_take _ (by simp)]
  simp only [List.append_assoc]
  rw [List.take_left]
  simp [List.drop_append, hlen]

private lemma Bytes.writeAt_five_spans
    {a0 w1 a1 w2 a2 w3 a3 w4 a4 w5 a5 : Bytes}
    {chainId domainSeparator : B256}
    (ha0 : a0.length = 372)
    (ha1 : a1.length = 132)
    (ha2 : a2.length = 123)
    (ha3 : a3.length = 2152)
    (ha4 : a4.length = 132)
    (hw1 : w1.length = 32)
    (hw2 : w2.length = 32)
    (hw3 : w3.length = 32)
    (hw4 : w4.length = 32)
    (hw5 : w5.length = 32) :
    Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt
          (Bytes.writeAt
            (Bytes.writeAt
              (a0 ++ w1 ++ a1 ++ w2 ++ a2 ++ w3 ++ a3 ++ w4 ++
                a4 ++ w5 ++ a5)
              372 chainId.toBytes)
            691 chainId.toBytes)
          2875 chainId.toBytes)
        536 domainSeparator.toBytes)
      3039 domainSeparator.toBytes =
      a0 ++ chainId.toBytes ++ a1 ++ domainSeparator.toBytes ++ a2 ++
        chainId.toBytes ++ a3 ++ chainId.toBytes ++ a4 ++
        domainSeparator.toBytes ++ a5 := by
  have h1 :
      Bytes.writeAt
        (a0 ++ w1 ++ a1 ++ w2 ++ a2 ++ w3 ++ a3 ++ w4 ++
          a4 ++ w5 ++ a5)
        372 chainId.toBytes =
      a0 ++ chainId.toBytes ++ a1 ++ w2 ++ a2 ++ w3 ++ a3 ++ w4 ++
        a4 ++ w5 ++ a5 := by
    have h := Bytes.writeAt_append_middle
      (pre := a0) (old := w1)
      (post := a1 ++ w2 ++ a2 ++ w3 ++ a3 ++ w4 ++ a4 ++ w5 ++ a5)
      (new := chainId.toBytes)
      (by simpa [hw1] using (B256.length_toBytes chainId).symm)
    rw [ha0] at h
    simpa only [List.append_assoc] using h
  rw [h1]
  have h2 :
      Bytes.writeAt
        (a0 ++ chainId.toBytes ++ a1 ++ w2 ++ a2 ++ w3 ++ a3 ++ w4 ++
          a4 ++ w5 ++ a5)
        691 chainId.toBytes =
      a0 ++ chainId.toBytes ++ a1 ++ w2 ++ a2 ++ chainId.toBytes ++
        a3 ++ w4 ++ a4 ++ w5 ++ a5 := by
    have h := Bytes.writeAt_append_middle
      (pre := a0 ++ chainId.toBytes ++ a1 ++ w2 ++ a2) (old := w3)
      (post := a3 ++ w4 ++ a4 ++ w5 ++ a5) (new := chainId.toBytes)
      (by simpa [hw3] using (B256.length_toBytes chainId).symm)
    have hpre :
        (a0 ++ chainId.toBytes ++ a1 ++ w2 ++ a2).length = 691 := by
      simp [ha0, ha1, ha2, hw2, B256.length_toBytes]
    rw [hpre] at h
    simpa only [List.append_assoc] using h
  rw [h2]
  have h3 :
      Bytes.writeAt
        (a0 ++ chainId.toBytes ++ a1 ++ w2 ++ a2 ++ chainId.toBytes ++
          a3 ++ w4 ++ a4 ++ w5 ++ a5)
        2875 chainId.toBytes =
      a0 ++ chainId.toBytes ++ a1 ++ w2 ++ a2 ++ chainId.toBytes ++
        a3 ++ chainId.toBytes ++ a4 ++ w5 ++ a5 := by
    have h := Bytes.writeAt_append_middle
      (pre := a0 ++ chainId.toBytes ++ a1 ++ w2 ++ a2 ++
        chainId.toBytes ++ a3)
      (old := w4) (post := a4 ++ w5 ++ a5) (new := chainId.toBytes)
      (by simpa [hw4] using (B256.length_toBytes chainId).symm)
    have hpre :
        (a0 ++ chainId.toBytes ++ a1 ++ w2 ++ a2 ++ chainId.toBytes ++
          a3).length = 2875 := by
      simp [ha0, ha1, ha2, ha3, hw2, B256.length_toBytes]
    rw [hpre] at h
    simpa only [List.append_assoc] using h
  rw [h3]
  have h4 :
      Bytes.writeAt
        (a0 ++ chainId.toBytes ++ a1 ++ w2 ++ a2 ++ chainId.toBytes ++
          a3 ++ chainId.toBytes ++ a4 ++ w5 ++ a5)
        536 domainSeparator.toBytes =
      a0 ++ chainId.toBytes ++ a1 ++ domainSeparator.toBytes ++ a2 ++
        chainId.toBytes ++ a3 ++ chainId.toBytes ++ a4 ++ w5 ++ a5 := by
    have h := Bytes.writeAt_append_middle
      (pre := a0 ++ chainId.toBytes ++ a1) (old := w2)
      (post := a2 ++ chainId.toBytes ++ a3 ++ chainId.toBytes ++
        a4 ++ w5 ++ a5)
      (new := domainSeparator.toBytes)
      (by simpa [hw2] using (B256.length_toBytes domainSeparator).symm)
    have hpre : (a0 ++ chainId.toBytes ++ a1).length = 536 := by
      simp [ha0, ha1, B256.length_toBytes]
    rw [hpre] at h
    simpa only [List.append_assoc] using h
  rw [h4]
  have h5 :
      Bytes.writeAt
        (a0 ++ chainId.toBytes ++ a1 ++ domainSeparator.toBytes ++ a2 ++
          chainId.toBytes ++ a3 ++ chainId.toBytes ++ a4 ++ w5 ++ a5)
        3039 domainSeparator.toBytes =
      a0 ++ chainId.toBytes ++ a1 ++ domainSeparator.toBytes ++ a2 ++
        chainId.toBytes ++ a3 ++ chainId.toBytes ++ a4 ++
        domainSeparator.toBytes ++ a5 := by
    have h := Bytes.writeAt_append_middle
      (pre := a0 ++ chainId.toBytes ++ a1 ++ domainSeparator.toBytes ++
        a2 ++ chainId.toBytes ++ a3 ++ chainId.toBytes ++ a4)
      (old := w5) (post := a5) (new := domainSeparator.toBytes)
      (by simpa [hw5] using (B256.length_toBytes domainSeparator).symm)
    have hpre :
        (a0 ++ chainId.toBytes ++ a1 ++ domainSeparator.toBytes ++
          a2 ++ chainId.toBytes ++ a3 ++ chainId.toBytes ++ a4).length =
          3039 := by
      simp [ha0, ha1, ha2, ha3, ha4, B256.length_toBytes]
    rw [hpre] at h
    simpa only [List.append_assoc] using h
  exact h5

private theorem weth10PatchedRuntime_eq_segments
    (chainId domainSeparator : B256) :
    weth10PatchedRuntime chainId domainSeparator =
      runtimeSegments chainId domainSeparator := by
  unfold weth10PatchedRuntime patchRuntimeWords
  simp only [deploymentChainIdWordOffsets, cachedDomainSeparatorWordOffsets,
    List.foldl_cons, List.foldl_nil]
  rw [← runtimeChunks_eq weth10RuntimeTemplate]
  unfold runtimeChunks runtimeSegments
  apply Bytes.writeAt_five_spans
  all_goals simp [List.length_take, weth10RuntimeTemplate_length]

private lemma Bytes.take_eq_take_of_getD_eq
    (xs ys : Bytes) (n : Nat) (d : UInt8)
    (hxs : n ≤ xs.length) (hys : n ≤ ys.length)
    (h : ∀ i, i < n → xs.getD i d = ys.getD i d) :
    xs.take n = ys.take n := by
  have hs : xs.sliceD 0 n d = ys.sliceD 0 n d := by
    calc
      xs.sliceD 0 n d =
          (List.range n).map (fun j => xs.getD (0 + j) d) :=
        List.sliceD_eq_map xs d n 0
      _ = (List.range n).map (fun j => ys.getD (0 + j) d) := by
        apply List.map_congr_left
        intro i hi
        simpa using h i (List.mem_range.mp hi)
      _ = ys.sliceD 0 n d :=
        (List.sliceD_eq_map ys d n 0).symm
  unfold List.sliceD at hs
  simp only [List.drop_zero] at hs
  rw [List.takeD_eq_take d hxs, List.takeD_eq_take d hys] at hs
  exact hs

private theorem dispatchForkByteAt_eq_prefix
    (locations : List Nat) (n k : Nat)
    (left0 right0 left right : DispatchTree)
    (hselector : leftmostFsig right = leftmostFsig right0)
    (hpush : (Ninst.pushB256 (leftmostFsig right0)).size = 5)
    (i : Nat) (hi : i < 11) :
    Func.byteAtByShape locations n
        (dispatchWith k (.fork left0 right0)).compileShape
        (dispatchWith k (.fork left right)) i 0 =
      Func.byteAtByShape locations n
        (dispatchWith k (.fork left0 right0)).compileShape
        (dispatchWith k (.fork left0 right0)) i 0 := by
  have hdup : (Ninst.dup 0).size = 1 := by decide +kernel
  have hgt : Ninst.gt.size = 1 := by decide +kernel
  interval_cases i <;>
    simp [dispatchWith, Func.byteAtByShape, Func.compileShape,
      hselector, hdup, hgt, hpush]

private def weth10TreeLeft (dp : DeployParams) : DispatchTree :=
  DispatchTree.build 26 ((weth10Funcs dp).take 14)

private def weth10TreeRight (dp : DeployParams) : DispatchTree :=
  DispatchTree.build 26 ((weth10Funcs dp).drop 14)

private theorem weth10Tree_eq_fork (dp : DeployParams) :
    weth10Tree dp = .fork (weth10TreeLeft dp) (weth10TreeRight dp) := by
  simp [weth10Tree, DispatchTree.ofSorted, weth10TreeLeft,
    weth10TreeRight, weth10Funcs, DispatchTree.build]

private theorem weth10TreeRight_leftmost_eq (dp : DeployParams) :
    leftmostFsig (weth10TreeRight dp) =
      leftmostFsig (weth10TreeRight (⟨0, 0⟩ : DeployParams)) := by
  simp [weth10TreeRight, weth10Funcs, DispatchTree.build, leftmostFsig]

private theorem weth10DispatchByteAt_eq_zero_0_11
    (locations : List Nat) (n : Nat) (chainId domainSeparator : B256)
    (i : Nat) (hi : i < 11) :
    Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot
          (weth10Tree ⟨chainId, domainSeparator⟩)) i 0 =
      Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))) i 0 := by
  rw [weth10Tree_eq_fork, weth10Tree_eq_fork]
  apply dispatchForkByteAt_eq_prefix
  · exact weth10TreeRight_leftmost_eq _
  · decide +kernel
  · exact hi

private theorem noncesSel_eq :
    selector "nonces" [.address] = (0x7ecebe00 : B256) := by
  decide +kernel

private theorem approveAndCallSel_eq :
    selector "approveAndCall" [.address, .uint256, .dynBytes] =
      (0xcae9ca51 : B256) := by
  decide +kernel

private theorem permitSel_eq :
    selector "permit"
        [.address, .address, .uint256, .uint256, .uint 8, .bytes 32,
          .bytes 32] = (0xd505accf : B256) := by
  decide +kernel

private theorem flashFeeSel_eq :
    selector "flashFee" [.address, .uint256] = (0xd9d98ce4 : B256) := by
  decide +kernel

private theorem allowanceSel_eq :
    selector "allowance" [.address, .address] = (0xdd62ed3e : B256) := by
  decide +kernel

private def treeSlice (dp : DeployParams) (fuel lo len : Nat) : DispatchTree :=
  DispatchTree.build fuel ((weth10Funcs dp).drop lo |>.take len)

private def dispatch26_0_14 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 26 0 14)

private def dispatch25_14_7 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 25 14 7)

private def dispatch24_21_3 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 24 21 3)

private def dispatch23_26_1 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 23 26 1)

private def dispatch22_24_1 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 22 24 1)

private def dispatchNode (selector : B256) (offPath onPath : Func) : Func :=
  Ninst.dup 0 ::: Ninst.pushB256 selector ::: Ninst.gt :::
    (offPath <?> onPath)

private theorem dispatchNodeByteAt_eq_prefix
    (locations : List Nat) (n : Nat) (selector : B256)
    (off0 on0 off on : Func)
    (hpush : (Ninst.pushB256 selector).size = 5)
    (i : Nat) (hi : i < 11) :
    Func.byteAtByShape locations n
        (dispatchNode selector off0 on0).compileShape
        (dispatchNode selector off on) i 0 =
      Func.byteAtByShape locations n
        (dispatchNode selector off0 on0).compileShape
        (dispatchNode selector off0 on0) i 0 := by
  have hdup : (Ninst.dup 0).size = 1 := by decide +kernel
  have hgt : Ninst.gt.size = 1 := by decide +kernel
  interval_cases i <;>
    simp [dispatchNode, Func.byteAtByShape, Func.compileShape,
      hdup, hgt, hpush]

private lemma dispatchNodeByteAt_to_onPath
    (locations : List Nat) (n : Nat) (selector : B256)
    (off0 on0 off on : Func) (i : Nat) (d : UInt8)
    (hpush : (Ninst.pushB256 selector).size = 5)
    (hlo : 11 ≤ i)
    (hinside : i - 11 < on0.compileShape.byteSize) :
    Func.byteAtByShape locations n
        (dispatchNode selector off0 on0).compileShape
        (dispatchNode selector off on) i d =
      Func.byteAtByShape locations (n + 11) on0.compileShape on
        (i - 11) d := by
  have hdup : (Ninst.dup 0).size = 1 := by decide +kernel
  have hgt : Ninst.gt.size = 1 := by decide +kernel
  have hiEq : i - 1 - 5 - 1 - 4 = i - 11 := by omega
  change
    Func.byteAtByShape locations n
      (.next (Ninst.dup 0).size
        (.next (Ninst.pushB256 selector).size
          (.next Ninst.gt.size
            (.branch on0.compileShape off0.compileShape))))
      (Ninst.dup 0 ::: Ninst.pushB256 selector ::: Ninst.gt :::
        (off <?> on)) i d = _
  conv_lhs => rw [Func.byteAtByShape, if_neg (by omega)]
  conv_lhs => rw [Func.byteAtByShape, if_neg (by omega)]
  conv_lhs => rw [Func.byteAtByShape, if_neg (by omega)]
  conv_lhs => rw [Func.byteAtByShape]
  conv_lhs => rw [if_neg (by
    simp only [List.length_cons, List.length_nil]
    omega)]
  dsimp only
  conv_lhs => rw [if_pos (by
    simpa only [hdup, hpush, hgt, List.length_cons, List.length_nil,
      Nat.reduceAdd, hiEq] using hinside)]
  simp only [hdup, hpush, hgt, List.length_cons, List.length_nil,
    Nat.reduceAdd, hiEq]

private lemma dispatchNodeByteAt_to_offPath
    (locations : List Nat) (n : Nat) (selector : B256)
    (off0 on0 off on : Func) (i : Nat) (d : UInt8)
    (hpush : (Ninst.pushB256 selector).size = 5)
    (hlo : 12 + on0.compileShape.byteSize ≤ i) :
    Func.byteAtByShape locations n
        (dispatchNode selector off0 on0).compileShape
        (dispatchNode selector off on) i d =
      Func.byteAtByShape locations
        (n + 12 + on0.compileShape.byteSize) off0.compileShape off
        (i - (12 + on0.compileShape.byteSize)) d := by
  have hdup : (Ninst.dup 0).size = 1 := by decide +kernel
  have hgt : Ninst.gt.size = 1 := by decide +kernel
  change
    Func.byteAtByShape locations n
      (.next (Ninst.dup 0).size
        (.next (Ninst.pushB256 selector).size
          (.next Ninst.gt.size
            (.branch on0.compileShape off0.compileShape))))
      (Ninst.dup 0 ::: Ninst.pushB256 selector ::: Ninst.gt :::
        (off <?> on)) i d = _
  conv_lhs => rw [Func.byteAtByShape, if_neg (by omega)]
  conv_lhs => rw [Func.byteAtByShape, if_neg (by omega)]
  conv_lhs => rw [Func.byteAtByShape, if_neg (by omega)]
  conv_lhs => rw [Func.byteAtByShape]
  conv_lhs => rw [if_neg (by
    simp only [List.length_cons, List.length_nil]
    omega)]
  dsimp only
  conv_lhs => rw [if_neg (by
    simp only [hdup, hpush, hgt, List.length_cons, List.length_nil,
      Nat.reduceAdd]
    omega)]
  conv_lhs => rw [if_neg (by
    simp only [hdup, hpush, hgt, List.length_cons, List.length_nil,
      Nat.reduceAdd]
    omega)]
  simp only [hdup, hpush, hgt, List.length_cons, List.length_nil,
    Nat.reduceAdd]
  congr 1 <;> omega

private lemma dispatchNodeByteAt_jumpdest
    (locations : List Nat) (n : Nat) (selector : B256)
    (off0 on0 off on : Func)
    (hpush : (Ninst.pushB256 selector).size = 5) (d : UInt8) :
    Func.byteAtByShape locations n
        (dispatchNode selector off0 on0).compileShape
        (dispatchNode selector off on) (11 + on0.compileShape.byteSize) d =
      Jinst.jumpdest.toUInt8 := by
  have hdup : (Ninst.dup 0).size = 1 := by decide +kernel
  have hgt : Ninst.gt.size = 1 := by decide +kernel
  change
    Func.byteAtByShape locations n
      (.next (Ninst.dup 0).size
        (.next (Ninst.pushB256 selector).size
          (.next Ninst.gt.size
            (.branch on0.compileShape off0.compileShape))))
      (Ninst.dup 0 ::: Ninst.pushB256 selector ::: Ninst.gt :::
        (off <?> on)) (11 + on0.compileShape.byteSize) d = _
  conv_lhs => rw [Func.byteAtByShape, if_neg (by
    simp only [hdup]
    omega)]
  conv_lhs => rw [Func.byteAtByShape, if_neg (by
    simp only [hdup, hpush]
    omega)]
  conv_lhs => rw [Func.byteAtByShape, if_neg (by
    simp only [hdup, hpush, hgt]
    omega)]
  conv_lhs => rw [Func.byteAtByShape]
  conv_lhs => rw [if_neg (by
    simp only [hdup, hpush, hgt, List.length_cons, List.length_nil]
    omega)]
  dsimp only
  conv_lhs => rw [if_neg (by
    simp only [hdup, hpush, hgt, List.length_cons, List.length_nil,
      Nat.reduceAdd]
    omega)]
  conv_lhs => rw [if_pos (by
    simp only [hdup, hpush, hgt, List.length_cons, List.length_nil,
      Nat.reduceAdd]
    omega)]
  have hi0 :
      11 + on0.compileShape.byteSize - 1 - 5 - 1 - 4 -
        on0.compileShape.byteSize = 0 := by
    omega
  simp only [hdup, hpush, hgt, List.length_cons, List.length_nil,
    Nat.reduceAdd]
  rw [hi0]
  rfl

private theorem dispatchNodeByteAt_eq_jumpdest
    (locations : List Nat) (n : Nat) (selector : B256)
    (off0 on0 off on : Func)
    (hpush : (Ninst.pushB256 selector).size = 5) :
    Func.byteAtByShape locations n
        (dispatchNode selector off0 on0).compileShape
        (dispatchNode selector off on) (11 + on0.compileShape.byteSize) 0 =
      Func.byteAtByShape locations n
        (dispatchNode selector off0 on0).compileShape
        (dispatchNode selector off0 on0)
        (11 + on0.compileShape.byteSize) 0 := by
  rw [dispatchNodeByteAt_jumpdest locations n selector off0 on0 off on hpush,
    dispatchNodeByteAt_jumpdest locations n selector off0 on0 off0 on0 hpush]

private def flashFeeLeaf : Func :=
  Ninst.pushB256 (0xd9d98ce4 : B256) ::: Ninst.eq :::
    ((nonpayable flashFee) <?> .call fallbackSlot)

private def dispatchD9 (dp : DeployParams) : Func :=
  dispatchNode 0xd9d98ce4 (dispatch22_24_1 dp) flashFeeLeaf

private def dispatchDd (dp : DeployParams) : Func :=
  dispatchNode 0xdd62ed3e (dispatchD9 dp) (dispatch23_26_1 dp)

private def dispatchD505 (dp : DeployParams) : Func :=
  dispatchNode 0xd505accf (dispatch24_21_3 dp) (dispatchDd dp)

private def dispatchCae9 (dp : DeployParams) : Func :=
  dispatchNode 0xcae9ca51 (dispatch25_14_7 dp) (dispatchD505 dp)

private def flashFeeDispatch (dp : DeployParams) : Func :=
  dispatchNode 0x7ecebe00 (dispatch26_0_14 dp) (dispatchCae9 dp)

private theorem flashFeeDispatch_eq (dp : DeployParams) :
    dispatchWith fallbackSlot (weth10Tree dp) = flashFeeDispatch dp := by
  simp [weth10Tree, DispatchTree.ofSorted, weth10Funcs, DispatchTree.build,
    treeSlice, dispatch26_0_14, dispatch25_14_7, dispatch24_21_3,
    dispatch23_26_1, dispatch22_24_1, flashFeeDispatch, dispatchCae9,
    dispatchD505, dispatchDd, dispatchD9, flashFeeLeaf, dispatchNode,
    dispatchWith,
    leftmostFsig, noncesSel_eq, approveAndCallSel_eq, permitSel_eq,
    flashFeeSel_eq, allowanceSel_eq]

private theorem dispatch23_26_1_eq_zero (dp : DeployParams) :
    dispatch23_26_1 dp =
      dispatch23_26_1 (⟨0, 0⟩ : DeployParams) := by
  simp [dispatch23_26_1, treeSlice, weth10Funcs, DispatchTree.build,
    dispatchWith, allowanceSel_eq]

private theorem dispatch25_14_7_eq_zero (dp : DeployParams) :
    dispatch25_14_7 dp =
      dispatch25_14_7 (⟨0, 0⟩ : DeployParams) := by
  simp [dispatch25_14_7, treeSlice, weth10Funcs, DispatchTree.build,
    dispatchWith]

private theorem dispatch22_24_1_eq_permit (dp : DeployParams) :
    dispatch22_24_1 dp =
      Ninst.pushB256 (0xd505accf : B256) ::: Ninst.eq :::
        ((nonpayable (permit dp)) <?> .call fallbackSlot) := by
  simp [dispatch22_24_1, treeSlice, weth10Funcs, DispatchTree.build,
    dispatchWith, permitSel_eq]

private def approveAndCallLeaf : Func :=
  Ninst.pushB256 (selector "approveAndCall"
      [.address, .uint256, .dynBytes]) ::: Ninst.eq :::
    ((nonpayable approveAndCall) <?> .call fallbackSlot)

private def deploymentChainIdLeafPrefix : Line :=
  [Ninst.pushB256 (selector "deploymentChainId" []), Ninst.eq]

private def deploymentChainIdLeaf (dp : DeployParams) : Func :=
  deploymentChainIdLeafPrefix +++
    ((nonpayable (deploymentChainId dp)) <?> .call fallbackSlot)

private def depositLeaf : Func :=
  Ninst.pushB256 (selector "deposit" []) ::: Ninst.eq :::
    (deposit <?> .call fallbackSlot)

private def deploymentPairDispatch (dp : DeployParams) : Func :=
  dispatchNode (selector "deploymentChainId" []) approveAndCallLeaf
    (deploymentChainIdLeaf dp)

private def deploymentDispatch (dp : DeployParams) : Func :=
  dispatchNode (selector "deposit" []) (deploymentPairDispatch dp) depositLeaf

private theorem dispatch24_21_3_eq_deploymentDispatch (dp : DeployParams) :
    dispatch24_21_3 dp = deploymentDispatch dp := by
  simp [dispatch24_21_3, treeSlice, weth10Funcs, DispatchTree.build,
    deploymentDispatch, deploymentPairDispatch, deploymentChainIdLeaf,
    deploymentChainIdLeafPrefix, approveAndCallLeaf, depositLeaf,
    dispatchNode, dispatchWith, prepend,
    leftmostFsig]

/-! ## Composed dispatch sizes

Kernel-evaluating `compileShape.byteSize` over a dispatch subtree re-walks
every leaf below it, so the walk lemmas' former per-site `decide +kernel`
size facts repeated the same traversal at every level.  The lemmas below
pay one small `decide` per leaf and derive every internal node's size
arithmetically through `dispatchNode_size`. -/

private theorem dispatchNode_size (s : B256) (off on : Func)
    (hpush : (Ninst.pushB256 s).size = 5) :
    (dispatchNode s off on).compileShape.byteSize =
      12 + on.compileShape.byteSize + off.compileShape.byteSize := by
  have hpushBytes : (Ninst.toBytes (Ninst.pushB256 s)).length = 5 := by
    rw [← Ninst.size_eq_length_toBytes]
    exact hpush
  have hdup : (Ninst.toBytes (Ninst.dup 0)).length = 1 := rfl
  have hgt : (Ninst.toBytes Ninst.gt).length = 1 := rfl
  simp only [Func.CompileShape.byteSize_compileShape, dispatchNode, compsize,
    hpushBytes, hdup, hgt]
  omega

private theorem flashFeeLeaf_size :
    flashFeeLeaf.compileShape.byteSize = 47 := by
  decide +kernel

private theorem depositLeaf_size :
    depositLeaf.compileShape.byteSize = 64 := by
  decide +kernel

private theorem deploymentChainIdLeaf_size :
    (deploymentChainIdLeaf
      (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 64 := by
  decide +kernel

private theorem approveAndCallLeaf_size :
    approveAndCallLeaf.compileShape.byteSize = 239 := by
  decide +kernel

private theorem dispatch22_24_1_size :
    (dispatch22_24_1 (⟨0, 0⟩ : DeployParams)).compileShape.byteSize =
      351 := by
  decide +kernel

private theorem dispatch23_26_1_size :
    (dispatch23_26_1 (⟨0, 0⟩ : DeployParams)).compileShape.byteSize =
      110 := by
  decide +kernel

private theorem dispatch25_14_7_size :
    (dispatch25_14_7 (⟨0, 0⟩ : DeployParams)).compileShape.byteSize =
      822 := by
  decide +kernel

private theorem dispatchD9_size :
    (dispatchD9 (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 410 := by
  unfold dispatchD9
  rw [dispatchNode_size _ _ _ (by decide +kernel),
    flashFeeLeaf_size, dispatch22_24_1_size]

private theorem dispatchDd_size :
    (dispatchDd (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 532 := by
  unfold dispatchDd
  rw [dispatchNode_size _ _ _ (by decide +kernel),
    dispatch23_26_1_size, dispatchD9_size]

private theorem deploymentPairDispatch_size :
    (deploymentPairDispatch
      (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 315 := by
  unfold deploymentPairDispatch
  rw [dispatchNode_size _ _ _ (by decide +kernel),
    deploymentChainIdLeaf_size, approveAndCallLeaf_size]


private theorem deploymentDispatch_size :
    (deploymentDispatch
      (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 391 := by
  unfold deploymentDispatch
  rw [dispatchNode_size _ _ _ (by decide +kernel),
    depositLeaf_size, deploymentPairDispatch_size]

private theorem dispatch24_21_3_size :
    (dispatch24_21_3 (⟨0, 0⟩ : DeployParams)).compileShape.byteSize =
      391 := by
  rw [dispatch24_21_3_eq_deploymentDispatch]
  exact deploymentDispatch_size

private theorem dispatchD505_size :
    (dispatchD505 (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 935 := by
  unfold dispatchD505
  rw [dispatchNode_size _ _ _ (by decide +kernel),
    dispatchDd_size, dispatch24_21_3_size]

private theorem dispatchCae9_size :
    (dispatchCae9 (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 1769 := by
  unfold dispatchCae9
  rw [dispatchNode_size _ _ _ (by decide +kernel),
    dispatchD505_size, dispatch25_14_7_size]

private theorem dispatch26_0_14_size :
    (dispatch26_0_14 (⟨0, 0⟩ : DeployParams)).compileShape.byteSize =
      2158 := by
  have hfull := fullDispatch_size
  rw [flashFeeDispatch_eq (⟨0, 0⟩ : DeployParams)] at hfull
  unfold flashFeeDispatch at hfull
  rw [dispatchNode_size _ _ _ (by decide +kernel), dispatchCae9_size]
    at hfull
  omega

private lemma byteAt_main_to_dispatch
    (locations : List Nat) (n : Nat) (p q : Func) (i : Nat) (d : UInt8)
    (hlo : 11 ≤ i)
    (hinside :
      i - Ninst.calldatasize.size - Ninst.iszero.size - 4 <
        (fsig +++ p).compileShape.byteSize) :
    Func.byteAtByShape locations n
        (Ninst.calldatasize ::: Ninst.iszero :::
          (receiveEther <?> (fsig +++ p))).compileShape
        (Ninst.calldatasize ::: Ninst.iszero :::
          (receiveEther <?> (fsig +++ q))) i d =
      Func.byteAtByShape locations (n + 11) p.compileShape q (i - 11) d := by
  have hcd : Ninst.calldatasize.size = 1 := by decide +kernel
  have hiz : Ninst.iszero.size = 1 := by decide +kernel
  have hp0 : (Ninst.pushB256 0).size = 1 := by decide +kernel
  have hcdl : Ninst.calldataload.size = 1 := by decide +kernel
  have hp224 : (Ninst.pushB256 224).size = 2 := by decide +kernel
  have hshr : Ninst.shr.size = 1 := by decide +kernel
  change
    Func.byteAtByShape locations n
      (.next Ninst.calldatasize.size
        (.next Ninst.iszero.size
          (.branch (fsig +++ p).compileShape receiveEther.compileShape)))
      (Ninst.calldatasize ::: Ninst.iszero :::
        (receiveEther <?> (fsig +++ q))) i d = _
  conv_lhs => rw [Func.byteAtByShape, if_neg (by omega)]
  conv_lhs => rw [Func.byteAtByShape, if_neg (by omega)]
  conv_lhs => rw [Func.byteAtByShape]
  conv_lhs => rw [if_neg (by
    simp only [List.length_cons, List.length_nil]
    rw [hcd, hiz]
    omega)]
  dsimp only
  conv_lhs => rw [if_pos (by
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd] using
      hinside)]
  change
    Func.byteAtByShape locations
      (n + Ninst.calldatasize.size + Ninst.iszero.size + 4)
      (.next (Ninst.pushB256 0).size
        (.next Ninst.calldataload.size
          (.next (Ninst.pushB256 224).size
            (.next Ninst.shr.size p.compileShape))))
      (Ninst.pushB256 0 ::: Ninst.calldataload :::
        Ninst.pushB256 224 ::: Ninst.shr ::: q)
      (i - Ninst.calldatasize.size - Ninst.iszero.size - 4) d = _
  conv_lhs => rw [Func.byteAtByShape, if_neg (by omega)]
  conv_lhs => rw [Func.byteAtByShape, if_neg (by omega)]
  conv_lhs => rw [Func.byteAtByShape, if_neg (by omega)]
  conv_lhs => rw [Func.byteAtByShape, if_neg (by omega)]
  simp only [hcd, hiz, hp0, hcdl, hp224, hshr]
  have hn : n + 1 + 1 + 4 + 1 + 1 + 2 + 1 = n + 11 := by omega
  have hi' : i - 1 - 1 - 4 - 1 - 1 - 2 - 1 = i - 11 := by omega
  rw [hn, hi']

private theorem weth10MainByteAt_to_dispatch
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (d : UInt8) (hlo : 11 ≤ i)
    (hinside :
      i - Ninst.calldatasize.size - Ninst.iszero.size - 4 <
        (fsig +++ dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape.byteSize) :
    Func.byteAtByShape locations n
        (weth10 (⟨0, 0⟩ : DeployParams)).main.compileShape
        (weth10 dp).main i d =
      Func.byteAtByShape locations (n + 11)
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot (weth10Tree dp)) (i - 11) d := by
  change
    Func.byteAtByShape locations n
        (Ninst.calldatasize ::: Ninst.iszero :::
          (receiveEther <?>
            (fsig +++ dispatchWith fallbackSlot
              (weth10Tree (⟨0, 0⟩ : DeployParams))))).compileShape
        (Ninst.calldatasize ::: Ninst.iszero :::
          (receiveEther <?>
            (fsig +++ dispatchWith fallbackSlot (weth10Tree dp)))) i d = _
  exact byteAt_main_to_dispatch locations n _ _ i d hlo hinside

private theorem prepend4_size (i1 i2 i3 i4 : Ninst) (p : Func) :
    (i1 ::: i2 ::: i3 ::: i4 ::: p).compileShape.byteSize =
      p.compileShape.byteSize + i4.size + i3.size + i2.size + i1.size := by
  simp only [Func.compileShape, Func.CompileShape.byteSize]

private theorem branch2_size (i1 i2 : Ninst) (p q : Func) :
    (i1 ::: i2 ::: Func.branch p q).compileShape.byteSize =
      p.compileShape.byteSize + q.compileShape.byteSize + 5 +
        i2.size + i1.size := by
  simp only [Func.compileShape, Func.CompileShape.byteSize]

private theorem fsigFullDispatch_size :
    (fsig +++ dispatchWith fallbackSlot
      (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape.byteSize = 3944 := by
  have hshape : fsig +++ dispatchWith fallbackSlot
      (weth10Tree (⟨0, 0⟩ : DeployParams)) =
      Ninst.pushB256 0 ::: Ninst.calldataload :::
        Ninst.pushB256 (Nat.toB256 224) ::: Ninst.shr :::
        dispatchWith fallbackSlot (weth10Tree (⟨0, 0⟩ : DeployParams)) := rfl
  rw [hshape, prepend4_size, fullDispatch_size]
  decide

private theorem weth10ZeroMain_size_lower :
    3950 ≤
      (weth10Main
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize := by
  have hshape : weth10Main (⟨0, 0⟩ : DeployParams) =
      Ninst.calldatasize ::: Ninst.iszero :::
        Func.branch
          (fsig +++ dispatchWith fallbackSlot
            (weth10Tree (⟨0, 0⟩ : DeployParams)))
          receiveEther := rfl
  rw [hshape, branch2_size, fsigFullDispatch_size]
  have hcd : Ninst.calldatasize.size = 1 := by decide
  have hiz : Ninst.iszero.size = 1 := by decide
  rw [hcd, hiz]
  omega

private theorem weth10MainByteAt_to_dispatch_inside
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (d : UInt8) (hlo : 11 ≤ i)
    (hinside : i - 11 <
      (dispatchWith fallbackSlot
        (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape.byteSize) :
    Func.byteAtByShape locations n
        (weth10 (⟨0, 0⟩ : DeployParams)).main.compileShape
        (weth10 dp).main i d =
      Func.byteAtByShape locations (n + 11)
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot (weth10Tree dp)) (i - 11) d := by
  have hdispatchSize :
      (dispatchWith fallbackSlot
        (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape.byteSize =
        3939 := by
    exact fullDispatch_size
  have hfsig :
      (fsig +++ dispatchWith fallbackSlot
        (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape.byteSize =
        3944 := by
    exact fsigFullDispatch_size
  apply weth10MainByteAt_to_dispatch locations n dp i d hlo
  change i - 1 - 1 - 4 < _
  omega

private def prefixByteSize : Line → Nat
  | [] => 0
  | inst :: rest => inst.size + prefixByteSize rest

private theorem compileShapeByteSize_prepend (l : Line) (p : Func) :
    (l +++ p).compileShape.byteSize =
      prefixByteSize l + p.compileShape.byteSize := by
  induction l with
  | nil =>
      change p.compileShape.byteSize = 0 + p.compileShape.byteSize
      omega
  | cons inst rest ih =>
      change (rest +++ p).compileShape.byteSize + inst.size =
        (inst.size + prefixByteSize rest) + p.compileShape.byteSize
      rw [ih]
      omega

private theorem byteAt_prepend_eq_prefix
    (locations : List Nat) (n : Nat) (l : Line) (p0 p : Func)
    (i : Nat) (d : UInt8) (hi : i < prefixByteSize l) :
    Func.byteAtByShape locations n (l +++ p0).compileShape
        (l +++ p) i d =
      Func.byteAtByShape locations n (l +++ p0).compileShape
        (l +++ p0) i d := by
  induction l generalizing n i with
  | nil => simp [prefixByteSize] at hi
  | cons inst rest ih =>
      change
        Func.byteAtByShape locations n
            (.next inst.size (rest +++ p0).compileShape)
            (inst ::: (rest +++ p)) i d =
          Func.byteAtByShape locations n
            (.next inst.size (rest +++ p0).compileShape)
            (inst ::: (rest +++ p0)) i d
      by_cases hinst : i < inst.size
      · conv_lhs => rw [Func.byteAtByShape, if_pos hinst]
        conv_rhs => rw [Func.byteAtByShape, if_pos hinst]
      · conv_lhs => rw [Func.byteAtByShape, if_neg hinst]
        conv_rhs => rw [Func.byteAtByShape, if_neg hinst]
        apply ih
        simp only [prefixByteSize] at hi
        omega

private theorem byteAt_prepend_to_tail
    (locations : List Nat) (n : Nat) (l : Line) (p0 p : Func)
    (i : Nat) (d : UInt8) (hlo : prefixByteSize l ≤ i) :
    Func.byteAtByShape locations n (l +++ p0).compileShape
        (l +++ p) i d =
      Func.byteAtByShape locations (n + prefixByteSize l) p0.compileShape
        p (i - prefixByteSize l) d := by
  induction l generalizing n i with
  | nil => simp [prefixByteSize, prepend]
  | cons inst rest ih =>
      have hinst : inst.size ≤ i := by
        simp only [prefixByteSize] at hlo
        omega
      change
        Func.byteAtByShape locations n
            (.next inst.size (rest +++ p0).compileShape)
            (inst ::: (rest +++ p)) i d = _
      conv_lhs => rw [Func.byteAtByShape, if_neg (Nat.not_lt_of_ge hinst)]
      rw [ih (n := n + inst.size) (i := i - inst.size) (by
        simp only [prefixByteSize] at hlo
        omega)]
      simp only [prefixByteSize, Nat.add_assoc, Nat.sub_sub]

private theorem byteAt_next_to_tail
    (locations : List Nat) (n : Nat) (inst0 inst : Ninst) (p0 p : Func)
    (i : Nat) (d : UInt8) (hlo : inst0.size ≤ i) :
    Func.byteAtByShape locations n (inst0 ::: p0).compileShape
        (inst ::: p) i d =
      Func.byteAtByShape locations (n + inst0.size) p0.compileShape
        p (i - inst0.size) d := by
  rw [Func.compileShape, Func.byteAtByShape,
    if_neg (Nat.not_lt_of_ge hlo)]

private theorem byteAt_branch_eq_header
    (locations : List Nat) (n : Nat)
    (left0 right0 left right : Func) (i : Nat) (d : UInt8)
    (hi : i < 4) :
    Func.byteAtByShape locations n
        (.branch left0.compileShape right0.compileShape)
        (.branch left right) i d =
      Func.byteAtByShape locations n
        (.branch left0.compileShape right0.compileShape)
        (.branch left0 right0) i d := by
  conv_lhs => rw [Func.byteAtByShape, if_pos (by
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd] using hi)]
  conv_rhs => rw [Func.byteAtByShape, if_pos (by
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd] using hi)]

private theorem byteAt_branch_to_left
    (locations : List Nat) (n : Nat)
    (left0 right0 left right : Func) (i : Nat) (d : UInt8)
    (hlo : 4 ≤ i) (hinside : i - 4 < left0.compileShape.byteSize) :
    Func.byteAtByShape locations n
        (.branch left0.compileShape right0.compileShape)
        (.branch left right) i d =
      Func.byteAtByShape locations (n + 4) left0.compileShape left
        (i - 4) d := by
  conv_lhs => rw [Func.byteAtByShape]
  conv_lhs => rw [if_neg (by
    simp only [List.length_cons, List.length_nil]
    omega)]
  dsimp only
  conv_lhs => rw [if_pos (by
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd] using
      hinside)]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd]

private lemma byteAt_branch_jumpdest
    (locations : List Nat) (n : Nat)
    (left0 right0 left right : Func) (d : UInt8) :
    Func.byteAtByShape locations n
        (.branch left0.compileShape right0.compileShape)
        (.branch left right) (4 + left0.compileShape.byteSize) d =
      Jinst.jumpdest.toUInt8 := by
  conv_lhs => rw [Func.byteAtByShape]
  conv_lhs => rw [if_neg (by
    simp only [List.length_cons, List.length_nil]
    omega)]
  dsimp only
  conv_lhs => rw [if_neg (by
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
    omega)]
  conv_lhs => rw [if_pos (by
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
    omega)]
  have hi0 :
      4 + left0.compileShape.byteSize - 4 -
        left0.compileShape.byteSize = 0 := by
    omega
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
  rw [hi0]
  rfl

private theorem byteAt_branch_eq_before_right
    (locations : List Nat) (n : Nat)
    (left0 right0 right : Func) (i : Nat) (d : UInt8)
    (hi : i < 5 + left0.compileShape.byteSize) :
    Func.byteAtByShape locations n
        (.branch left0.compileShape right0.compileShape)
        (.branch left0 right) i d =
      Func.byteAtByShape locations n
        (.branch left0.compileShape right0.compileShape)
        (.branch left0 right0) i d := by
  by_cases hheader : i < 4
  · exact byteAt_branch_eq_header locations n left0 right0 left0 right
      i d hheader
  · by_cases hleft : i - 4 < left0.compileShape.byteSize
    · rw [byteAt_branch_to_left locations n left0 right0 left0 right i d
          (by omega) hleft,
        byteAt_branch_to_left locations n left0 right0 left0 right0 i d
          (by omega) hleft]
    · have hjump : i = 4 + left0.compileShape.byteSize := by omega
      subst i
      rw [byteAt_branch_jumpdest locations n left0 right0 left0 right,
        byteAt_branch_jumpdest locations n left0 right0 left0 right0]

private theorem byteAt_branch_to_right
    (locations : List Nat) (n : Nat)
    (left0 right0 left right : Func) (i : Nat) (d : UInt8)
    (hlo : 5 + left0.compileShape.byteSize ≤ i) :
    Func.byteAtByShape locations n
        (.branch left0.compileShape right0.compileShape)
        (.branch left right) i d =
      Func.byteAtByShape locations
        (n + 5 + left0.compileShape.byteSize) right0.compileShape right
        (i - (5 + left0.compileShape.byteSize)) d := by
  conv_lhs => rw [Func.byteAtByShape]
  conv_lhs => rw [if_neg (by
    simp only [List.length_cons, List.length_nil]
    omega)]
  dsimp only
  conv_lhs => rw [if_neg (by
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
    omega)]
  conv_lhs => rw [if_neg (by
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
    omega)]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
  congr 1 <;> omega

private theorem pushDeployWord_opcode_eq
    (locations : List Nat) (n : Nat) (p0 p : Func) (w : B256) :
    Func.byteAtByShape locations n (pushDeployWord 0 ::: p0).compileShape
        (pushDeployWord w ::: p) 0 0 =
      Func.byteAtByShape locations n (pushDeployWord 0 ::: p0).compileShape
        (pushDeployWord 0 ::: p0) 0 0 := by
  simp [Func.byteAtByShape, Func.compileShape, pushDeployWord,
    Ninst.toBytes, Ninst.size, pushToB8L, pushToB8, B256.length_toBytes]

private def permitCorePrefix : Line :=
  [Ninst.chainid] ++ addressArg 0 ++ [Ninst.dup 0] ++ tagNonceKey ++
  [Ninst.dup 0, Ninst.sload, Ninst.dup 0] ++ mstoreAt 4 ++
  [Ninst.pushB256 1, Ninst.add, Ninst.swap 0, Ninst.sstore, Ninst.pop,
    Ninst.pushB256 PERMIT_TYPEHASH] ++ mstoreAt 0 ++
  argCopy 1 0 3 ++ arg 3 ++ mstoreAt 5 ++
  pushList [192, 0] ++ [Ninst.kec, Ninst.dup 1]

private def permitDynamicPath : Func :=
  Ninst.swap 0 ::: calculateDomainSeparator +++ .call permitRecoverSlot

private def permitCachedPath (dp : DeployParams) : Func :=
  Ninst.swap 0 ::: Ninst.pop :::
    pushDeployWord dp.cachedDomainSeparator ::: .call permitRecoverSlot

private def permitCoreTail (dp : DeployParams) : Func :=
  pushDeployWord dp.deploymentChainId ::: Ninst.eq :::
    Func.branch permitDynamicPath (permitCachedPath dp)

private def permitCoreX (dp : DeployParams) : Func :=
  permitCorePrefix +++ permitCoreTail dp

private def permitGuardPrefix : Line :=
  arg 3 ++ [Ninst.timestamp, Ninst.gt]

private def permitFactored (dp : DeployParams) : Func :=
  permitGuardPrefix +++
    Func.branch (permitCoreX dp) (.call expiredPermitErrorSlot)

private theorem permit_eq_factored (dp : DeployParams) :
    permit dp = permitFactored dp := by
  unfold permit permitFactored permitCoreX permitCoreTail
  simp only [permitGuardPrefix, permitCorePrefix, permitDynamicPath,
    permitCachedPath, prepend_append,
    List.cons_append, List.nil_append, prepend]

private theorem permitCoreX_size :
    (permitCoreX (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 312 := by
  decide +kernel

private theorem permitByteAt_eq_zero_0_121
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hi : i < 121) :
    Func.byteAtByShape locations n
        (permit (⟨0, 0⟩ : DeployParams)).compileShape (permit dp) i 0 =
      Func.byteAtByShape locations n
        (permit (⟨0, 0⟩ : DeployParams)).compileShape
        (permit (⟨0, 0⟩ : DeployParams)) i 0 := by
  rw [permit_eq_factored dp,
    permit_eq_factored (⟨0, 0⟩ : DeployParams)]
  unfold permitFactored
  have hguard : prefixByteSize permitGuardPrefix = 5 := by decide +kernel
  have hcore : prefixByteSize permitCorePrefix = 111 := by decide +kernel
  by_cases hpre : i < 5
  · apply byteAt_prepend_eq_prefix
    simpa only [hguard] using hpre
  · conv_lhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n) (l := permitGuardPrefix)
      (p0 := Func.branch
        (permitCoreX (⟨0, 0⟩ : DeployParams)) (.call expiredPermitErrorSlot))
      (p := Func.branch (permitCoreX dp) (.call expiredPermitErrorSlot))
      (i := i) (d := 0) (by omega)]
    conv_rhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n) (l := permitGuardPrefix)
      (p0 := Func.branch
        (permitCoreX (⟨0, 0⟩ : DeployParams)) (.call expiredPermitErrorSlot))
      (p := Func.branch
        (permitCoreX (⟨0, 0⟩ : DeployParams)) (.call expiredPermitErrorSlot))
      (i := i) (d := 0) (by omega)]
    simp only [hguard]
    change
      Func.byteAtByShape locations (n + 5)
          (.branch (permitCoreX (⟨0, 0⟩ : DeployParams)).compileShape
            (Func.call expiredPermitErrorSlot).compileShape)
          (.branch (permitCoreX dp) (.call expiredPermitErrorSlot))
          (i - 5) 0 =
        Func.byteAtByShape locations (n + 5)
          (.branch (permitCoreX (⟨0, 0⟩ : DeployParams)).compileShape
            (Func.call expiredPermitErrorSlot).compileShape)
          (.branch (permitCoreX (⟨0, 0⟩ : DeployParams))
            (.call expiredPermitErrorSlot)) (i - 5) 0
    by_cases hheader : i - 5 < 4
    · apply byteAt_branch_eq_header
      exact hheader
    · have hcoreSize :
          112 ≤ (permitCoreX
            (⟨0, 0⟩ : DeployParams)).compileShape.byteSize := by
        rw [permitCoreX_size]
        omega
      conv_lhs => rw [byteAt_branch_to_left
        (locations := locations) (n := n + 5)
        (left0 := permitCoreX (⟨0, 0⟩ : DeployParams))
        (right0 := .call expiredPermitErrorSlot)
        (left := permitCoreX dp) (right := .call expiredPermitErrorSlot)
        (i := i - 5) (d := 0) (by omega) (by omega)]
      conv_rhs => rw [byteAt_branch_to_left
        (locations := locations) (n := n + 5)
        (left0 := permitCoreX (⟨0, 0⟩ : DeployParams))
        (right0 := .call expiredPermitErrorSlot)
        (left := permitCoreX (⟨0, 0⟩ : DeployParams))
        (right := .call expiredPermitErrorSlot)
        (i := i - 5) (d := 0) (by omega) (by omega)]
      unfold permitCoreX
      by_cases hcommon : i - 5 - 4 < 111
      · apply byteAt_prepend_eq_prefix
        simpa only [hcore] using hcommon
      · have hlast : i - 5 - 4 = 111 := by omega
        conv_lhs => rw [byteAt_prepend_to_tail
          (locations := locations) (n := n + 5 + 4)
          (l := permitCorePrefix)
          (p0 := permitCoreTail (⟨0, 0⟩ : DeployParams))
          (p := permitCoreTail dp) (i := i - 5 - 4) (d := 0) (by omega)]
        conv_rhs => rw [byteAt_prepend_to_tail
          (locations := locations) (n := n + 5 + 4)
          (l := permitCorePrefix)
          (p0 := permitCoreTail (⟨0, 0⟩ : DeployParams))
          (p := permitCoreTail (⟨0, 0⟩ : DeployParams))
          (i := i - 5 - 4) (d := 0) (by omega)]
        simp only [hcore, hlast, Nat.reduceSub]
        exact pushDeployWord_opcode_eq _ _ _ _ _

private def nonpayablePrefix : Line :=
  [Ninst.callvalue, Ninst.iszero]

private theorem nonpayablePermitByteAt_eq_zero_0_131
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hi : i < 131) :
    Func.byteAtByShape locations n
        (nonpayable (permit (⟨0, 0⟩ : DeployParams))).compileShape
        (nonpayable (permit dp)) i 0 =
      Func.byteAtByShape locations n
        (nonpayable (permit (⟨0, 0⟩ : DeployParams))).compileShape
        (nonpayable (permit (⟨0, 0⟩ : DeployParams))) i 0 := by
  change
    Func.byteAtByShape locations n
        (nonpayablePrefix +++
          Func.branch Func.rev
            (permit (⟨0, 0⟩ : DeployParams))).compileShape
        (nonpayablePrefix +++ Func.branch Func.rev (permit dp)) i 0 =
      Func.byteAtByShape locations n
        (nonpayablePrefix +++
          Func.branch Func.rev
            (permit (⟨0, 0⟩ : DeployParams))).compileShape
        (nonpayablePrefix +++
          Func.branch Func.rev
            (permit (⟨0, 0⟩ : DeployParams))) i 0
  have hprefix : prefixByteSize nonpayablePrefix = 2 := by decide +kernel
  have hrev : Func.rev.compileShape.byteSize = 3 := by decide +kernel
  by_cases hpre : i < 2
  · apply byteAt_prepend_eq_prefix
    simpa only [hprefix] using hpre
  · conv_lhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n) (l := nonpayablePrefix)
      (p0 := Func.branch Func.rev
        (permit (⟨0, 0⟩ : DeployParams)))
      (p := Func.branch Func.rev (permit dp))
      (i := i) (d := 0) (by omega)]
    conv_rhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n) (l := nonpayablePrefix)
      (p0 := Func.branch Func.rev
        (permit (⟨0, 0⟩ : DeployParams)))
      (p := Func.branch Func.rev
        (permit (⟨0, 0⟩ : DeployParams)))
      (i := i) (d := 0) (by omega)]
    simp only [hprefix]
    by_cases hbranch : i - 2 < 8
    · apply byteAt_branch_eq_before_right
      simpa only [hrev] using hbranch
    · change
        Func.byteAtByShape locations (n + 2)
            (.branch Func.rev.compileShape
              (permit (⟨0, 0⟩ : DeployParams)).compileShape)
            (.branch Func.rev (permit dp)) (i - 2) 0 =
          Func.byteAtByShape locations (n + 2)
            (.branch Func.rev.compileShape
              (permit (⟨0, 0⟩ : DeployParams)).compileShape)
            (.branch Func.rev
              (permit (⟨0, 0⟩ : DeployParams))) (i - 2) 0
      rw [byteAt_branch_to_right locations (n + 2) Func.rev
          (permit (⟨0, 0⟩ : DeployParams)) Func.rev (permit dp)
          (i - 2) 0 (by simp only [hrev, Nat.reduceAdd]; omega),
        byteAt_branch_to_right locations (n + 2) Func.rev
          (permit (⟨0, 0⟩ : DeployParams)) Func.rev
          (permit (⟨0, 0⟩ : DeployParams)) (i - 2) 0
          (by simp only [hrev, Nat.reduceAdd]; omega)]
      simp only [hrev]
      apply permitByteAt_eq_zero_0_121
      omega

private def permitLeafPrefix : Line :=
  [Ninst.pushB256 (0xd505accf : B256), Ninst.eq]

private theorem dispatch22_24_1ByteAt_eq_zero_0_146
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hi : i < 146) :
    Func.byteAtByShape locations n
        (dispatch22_24_1 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch22_24_1 dp) i 0 =
      Func.byteAtByShape locations n
        (dispatch22_24_1 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch22_24_1 (⟨0, 0⟩ : DeployParams)) i 0 := by
  rw [dispatch22_24_1_eq_permit dp,
    dispatch22_24_1_eq_permit (⟨0, 0⟩ : DeployParams)]
  change
    Func.byteAtByShape locations n
        (permitLeafPrefix +++
          Func.branch (.call fallbackSlot)
            (nonpayable (permit (⟨0, 0⟩ : DeployParams)))).compileShape
        (permitLeafPrefix +++
          Func.branch (.call fallbackSlot) (nonpayable (permit dp))) i 0 =
      Func.byteAtByShape locations n
        (permitLeafPrefix +++
          Func.branch (.call fallbackSlot)
            (nonpayable (permit (⟨0, 0⟩ : DeployParams)))).compileShape
        (permitLeafPrefix +++
          Func.branch (.call fallbackSlot)
            (nonpayable (permit (⟨0, 0⟩ : DeployParams)))) i 0
  have hprefix : prefixByteSize permitLeafPrefix = 6 := by decide +kernel
  have hcall : (Func.call fallbackSlot).compileShape.byteSize = 4 := by
    decide +kernel
  by_cases hpre : i < 6
  · apply byteAt_prepend_eq_prefix
    simpa only [hprefix] using hpre
  · conv_lhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n) (l := permitLeafPrefix)
      (p0 := Func.branch (.call fallbackSlot)
        (nonpayable (permit (⟨0, 0⟩ : DeployParams))))
      (p := Func.branch (.call fallbackSlot) (nonpayable (permit dp)))
      (i := i) (d := 0) (by omega)]
    conv_rhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n) (l := permitLeafPrefix)
      (p0 := Func.branch (.call fallbackSlot)
        (nonpayable (permit (⟨0, 0⟩ : DeployParams))))
      (p := Func.branch (.call fallbackSlot)
        (nonpayable (permit (⟨0, 0⟩ : DeployParams))))
      (i := i) (d := 0) (by omega)]
    simp only [hprefix]
    by_cases hbranch : i - 6 < 9
    · apply byteAt_branch_eq_before_right
      simpa only [hcall] using hbranch
    · change
        Func.byteAtByShape locations (n + 6)
            (.branch (Func.call fallbackSlot).compileShape
              (nonpayable
                (permit (⟨0, 0⟩ : DeployParams))).compileShape)
            (.branch (.call fallbackSlot) (nonpayable (permit dp)))
            (i - 6) 0 =
          Func.byteAtByShape locations (n + 6)
            (.branch (Func.call fallbackSlot).compileShape
              (nonpayable
                (permit (⟨0, 0⟩ : DeployParams))).compileShape)
            (.branch (.call fallbackSlot)
              (nonpayable
                (permit (⟨0, 0⟩ : DeployParams)))) (i - 6) 0
      rw [byteAt_branch_to_right locations (n + 6) (.call fallbackSlot)
          (nonpayable (permit (⟨0, 0⟩ : DeployParams)))
          (.call fallbackSlot) (nonpayable (permit dp))
          (i - 6) 0 (by simp only [hcall, Nat.reduceAdd]; omega),
        byteAt_branch_to_right locations (n + 6) (.call fallbackSlot)
          (nonpayable (permit (⟨0, 0⟩ : DeployParams)))
          (.call fallbackSlot)
          (nonpayable (permit (⟨0, 0⟩ : DeployParams)))
          (i - 6) 0 (by simp only [hcall, Nat.reduceAdd]; omega)]
      simp only [hcall]
      apply nonpayablePermitByteAt_eq_zero_0_131
      omega

private theorem dispatchD9ByteAt_eq_zero_0_205
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hi : i < 205) :
    Func.byteAtByShape locations n
        (dispatchD9 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatchD9 dp) i 0 =
      Func.byteAtByShape locations n
        (dispatchD9 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatchD9 (⟨0, 0⟩ : DeployParams)) i 0 := by
  unfold dispatchD9
  have hpush : (Ninst.pushB256 (0xd9d98ce4 : B256)).size = 5 := by
    decide +kernel
  have hflash : flashFeeLeaf.compileShape.byteSize = 47 :=
    flashFeeLeaf_size
  by_cases hheader : i < 11
  · exact dispatchNodeByteAt_eq_prefix locations n 0xd9d98ce4
      (dispatch22_24_1 (⟨0, 0⟩ : DeployParams)) flashFeeLeaf
      (dispatch22_24_1 dp) flashFeeLeaf hpush i hheader
  · by_cases hon : i - 11 < 47
    · rw [dispatchNodeByteAt_to_onPath locations n 0xd9d98ce4
          (dispatch22_24_1 (⟨0, 0⟩ : DeployParams)) flashFeeLeaf
          (dispatch22_24_1 dp) flashFeeLeaf i 0 hpush (by omega)
          (by simpa only [hflash] using hon),
        dispatchNodeByteAt_to_onPath locations n 0xd9d98ce4
          (dispatch22_24_1 (⟨0, 0⟩ : DeployParams)) flashFeeLeaf
          (dispatch22_24_1 (⟨0, 0⟩ : DeployParams)) flashFeeLeaf
          i 0 hpush (by omega) (by simpa only [hflash] using hon)]
    · by_cases hjump : i = 58
      · have hiEq : i = 11 + flashFeeLeaf.compileShape.byteSize := by
          omega
        rw [hiEq]
        exact dispatchNodeByteAt_eq_jumpdest locations n 0xd9d98ce4
          (dispatch22_24_1 (⟨0, 0⟩ : DeployParams)) flashFeeLeaf
          (dispatch22_24_1 dp) flashFeeLeaf hpush
      · rw [dispatchNodeByteAt_to_offPath locations n 0xd9d98ce4
            (dispatch22_24_1 (⟨0, 0⟩ : DeployParams)) flashFeeLeaf
            (dispatch22_24_1 dp) flashFeeLeaf i 0 hpush (by
              simp only [hflash]
              omega),
          dispatchNodeByteAt_to_offPath locations n 0xd9d98ce4
            (dispatch22_24_1 (⟨0, 0⟩ : DeployParams)) flashFeeLeaf
            (dispatch22_24_1 (⟨0, 0⟩ : DeployParams)) flashFeeLeaf
            i 0 hpush (by
              simp only [hflash]
              omega)]
        simp only [hflash, Nat.reduceAdd]
        apply dispatch22_24_1ByteAt_eq_zero_0_146
        omega

private theorem dispatchDdByteAt_eq_zero_0_327
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hi : i < 327) :
    Func.byteAtByShape locations n
        (dispatchDd (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatchDd dp) i 0 =
      Func.byteAtByShape locations n
        (dispatchDd (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatchDd (⟨0, 0⟩ : DeployParams)) i 0 := by
  unfold dispatchDd
  have hpush : (Ninst.pushB256 (0xdd62ed3e : B256)).size = 5 := by
    decide +kernel
  have hallowance :
      (dispatch23_26_1
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 110 :=
    dispatch23_26_1_size
  by_cases hheader : i < 11
  · exact dispatchNodeByteAt_eq_prefix locations n 0xdd62ed3e
      (dispatchD9 (⟨0, 0⟩ : DeployParams))
      (dispatch23_26_1 (⟨0, 0⟩ : DeployParams))
      (dispatchD9 dp) (dispatch23_26_1 dp) hpush i hheader
  · by_cases hon : i - 11 < 110
    · rw [dispatchNodeByteAt_to_onPath locations n 0xdd62ed3e
          (dispatchD9 (⟨0, 0⟩ : DeployParams))
          (dispatch23_26_1 (⟨0, 0⟩ : DeployParams))
          (dispatchD9 dp) (dispatch23_26_1 dp) i 0 hpush (by omega)
          (by simpa only [hallowance] using hon),
        dispatchNodeByteAt_to_onPath locations n 0xdd62ed3e
          (dispatchD9 (⟨0, 0⟩ : DeployParams))
          (dispatch23_26_1 (⟨0, 0⟩ : DeployParams))
          (dispatchD9 (⟨0, 0⟩ : DeployParams))
          (dispatch23_26_1 (⟨0, 0⟩ : DeployParams)) i 0 hpush
          (by omega) (by simpa only [hallowance] using hon)]
      rw [dispatch23_26_1_eq_zero dp]
    · by_cases hjump : i = 121
      · have hiEq : i = 11 +
            (dispatch23_26_1
              (⟨0, 0⟩ : DeployParams)).compileShape.byteSize := by
          omega
        rw [hiEq]
        exact dispatchNodeByteAt_eq_jumpdest locations n 0xdd62ed3e
          (dispatchD9 (⟨0, 0⟩ : DeployParams))
          (dispatch23_26_1 (⟨0, 0⟩ : DeployParams))
          (dispatchD9 dp) (dispatch23_26_1 dp) hpush
      · rw [dispatchNodeByteAt_to_offPath locations n 0xdd62ed3e
            (dispatchD9 (⟨0, 0⟩ : DeployParams))
            (dispatch23_26_1 (⟨0, 0⟩ : DeployParams))
            (dispatchD9 dp) (dispatch23_26_1 dp) i 0 hpush (by
              simp only [hallowance]
              omega),
          dispatchNodeByteAt_to_offPath locations n 0xdd62ed3e
            (dispatchD9 (⟨0, 0⟩ : DeployParams))
            (dispatch23_26_1 (⟨0, 0⟩ : DeployParams))
            (dispatchD9 (⟨0, 0⟩ : DeployParams))
            (dispatch23_26_1 (⟨0, 0⟩ : DeployParams)) i 0 hpush (by
              simp only [hallowance]
              omega)]
        simp only [hallowance, Nat.reduceAdd]
        apply dispatchD9ByteAt_eq_zero_0_205
        omega

private theorem dispatchD505ByteAt_eq_zero_0_338
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hi : i < 338) :
    Func.byteAtByShape locations n
        (dispatchD505 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatchD505 dp) i 0 =
      Func.byteAtByShape locations n
        (dispatchD505 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatchD505 (⟨0, 0⟩ : DeployParams)) i 0 := by
  unfold dispatchD505
  have hpush : (Ninst.pushB256 (0xd505accf : B256)).size = 5 := by
    decide +kernel
  have hdd :
      327 ≤ (dispatchDd
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize := by
    decide +kernel
  by_cases hheader : i < 11
  · exact dispatchNodeByteAt_eq_prefix locations n 0xd505accf
      (dispatch24_21_3 (⟨0, 0⟩ : DeployParams))
      (dispatchDd (⟨0, 0⟩ : DeployParams))
      (dispatch24_21_3 dp) (dispatchDd dp) hpush i hheader
  · rw [dispatchNodeByteAt_to_onPath locations n 0xd505accf
          (dispatch24_21_3 (⟨0, 0⟩ : DeployParams))
          (dispatchDd (⟨0, 0⟩ : DeployParams))
          (dispatch24_21_3 dp) (dispatchDd dp) i 0 hpush (by omega)
          (by omega),
        dispatchNodeByteAt_to_onPath locations n 0xd505accf
          (dispatch24_21_3 (⟨0, 0⟩ : DeployParams))
          (dispatchDd (⟨0, 0⟩ : DeployParams))
          (dispatch24_21_3 (⟨0, 0⟩ : DeployParams))
          (dispatchDd (⟨0, 0⟩ : DeployParams)) i 0 hpush (by omega)
          (by omega)]
    apply dispatchDdByteAt_eq_zero_0_327
    omega

private theorem dispatchCae9ByteAt_eq_zero_0_349
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hi : i < 349) :
    Func.byteAtByShape locations n
        (dispatchCae9 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatchCae9 dp) i 0 =
      Func.byteAtByShape locations n
        (dispatchCae9 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatchCae9 (⟨0, 0⟩ : DeployParams)) i 0 := by
  unfold dispatchCae9
  have hpush : (Ninst.pushB256 (0xcae9ca51 : B256)).size = 5 := by
    decide +kernel
  have hd505 :
      338 ≤ (dispatchD505
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize := by
    decide +kernel
  by_cases hheader : i < 11
  · exact dispatchNodeByteAt_eq_prefix locations n 0xcae9ca51
      (dispatch25_14_7 (⟨0, 0⟩ : DeployParams))
      (dispatchD505 (⟨0, 0⟩ : DeployParams))
      (dispatch25_14_7 dp) (dispatchD505 dp) hpush i hheader
  · rw [dispatchNodeByteAt_to_onPath locations n 0xcae9ca51
          (dispatch25_14_7 (⟨0, 0⟩ : DeployParams))
          (dispatchD505 (⟨0, 0⟩ : DeployParams))
          (dispatch25_14_7 dp) (dispatchD505 dp) i 0 hpush (by omega)
          (by omega),
        dispatchNodeByteAt_to_onPath locations n 0xcae9ca51
          (dispatch25_14_7 (⟨0, 0⟩ : DeployParams))
          (dispatchD505 (⟨0, 0⟩ : DeployParams))
          (dispatch25_14_7 (⟨0, 0⟩ : DeployParams))
          (dispatchD505 (⟨0, 0⟩ : DeployParams)) i 0 hpush (by omega)
          (by omega)]
    apply dispatchD505ByteAt_eq_zero_0_338
    omega

private theorem flashFeeDispatchByteAt_eq_zero_0_360
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hi : i < 360) :
    Func.byteAtByShape locations n
        (flashFeeDispatch (⟨0, 0⟩ : DeployParams)).compileShape
        (flashFeeDispatch dp) i 0 =
      Func.byteAtByShape locations n
        (flashFeeDispatch (⟨0, 0⟩ : DeployParams)).compileShape
        (flashFeeDispatch (⟨0, 0⟩ : DeployParams)) i 0 := by
  unfold flashFeeDispatch
  have hpush : (Ninst.pushB256 (0x7ecebe00 : B256)).size = 5 := by
    decide +kernel
  have hcae9 :
      349 ≤ (dispatchCae9
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize := by
    decide +kernel
  by_cases hheader : i < 11
  · exact dispatchNodeByteAt_eq_prefix locations n 0x7ecebe00
      (dispatch26_0_14 (⟨0, 0⟩ : DeployParams))
      (dispatchCae9 (⟨0, 0⟩ : DeployParams))
      (dispatch26_0_14 dp) (dispatchCae9 dp) hpush i hheader
  · rw [dispatchNodeByteAt_to_onPath locations n 0x7ecebe00
          (dispatch26_0_14 (⟨0, 0⟩ : DeployParams))
          (dispatchCae9 (⟨0, 0⟩ : DeployParams))
          (dispatch26_0_14 dp) (dispatchCae9 dp) i 0 hpush (by omega)
          (by omega),
        dispatchNodeByteAt_to_onPath locations n 0x7ecebe00
          (dispatch26_0_14 (⟨0, 0⟩ : DeployParams))
          (dispatchCae9 (⟨0, 0⟩ : DeployParams))
          (dispatch26_0_14 (⟨0, 0⟩ : DeployParams))
          (dispatchCae9 (⟨0, 0⟩ : DeployParams)) i 0 hpush (by omega)
          (by omega)]
    apply dispatchCae9ByteAt_eq_zero_0_349
    omega

private theorem weth10DispatchByteAt_eq_zero_0_360
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hi : i < 360) :
    Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot (weth10Tree dp)) i 0 =
      Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))) i 0 := by
  rw [flashFeeDispatch_eq dp,
    flashFeeDispatch_eq (⟨0, 0⟩ : DeployParams)]
  exact flashFeeDispatchByteAt_eq_zero_0_360 locations n dp i hi

private theorem weth10MainByteAt_eq_zero_0_11
    (locations : List Nat) (n : Nat) (chainId domainSeparator : B256)
    (i : Nat) (hi : i < 11) :
    Func.byteAtByShape locations n
        (weth10 (⟨0, 0⟩ : DeployParams)).main.compileShape
        (weth10 ⟨chainId, domainSeparator⟩).main i 0 =
      Func.byteAtByShape locations n
        (weth10 (⟨0, 0⟩ : DeployParams)).main.compileShape
        (weth10 (⟨0, 0⟩ : DeployParams)).main i 0 := by
  have hcd : Ninst.calldatasize.size = 1 := by decide +kernel
  have hiz : Ninst.iszero.size = 1 := by decide +kernel
  have hp0 : (Ninst.pushB256 0).size = 1 := by decide +kernel
  have hcdl : Ninst.calldataload.size = 1 := by decide +kernel
  have hp224 : (Ninst.pushB256 224).size = 2 := by decide +kernel
  have hshr : Ninst.shr.size = 1 := by decide +kernel
  interval_cases i <;>
    simp (disch := omega) [Func.byteAtByShape, Func.compileShape,
      weth10, weth10Main, fsig, cdl, shiftRight,
      prepend, hcd, hiz, hp0, hcdl, hp224, hshr]

private theorem weth10MainByteAt_eq_zero_0_371
    (locations : List Nat) (n : Nat) (chainId domainSeparator : B256)
    (i : Nat) (hi : i < 371) :
    Func.byteAtByShape locations n
        (weth10 (⟨0, 0⟩ : DeployParams)).main.compileShape
        (weth10 ⟨chainId, domainSeparator⟩).main i 0 =
      Func.byteAtByShape locations n
        (weth10 (⟨0, 0⟩ : DeployParams)).main.compileShape
        (weth10 (⟨0, 0⟩ : DeployParams)).main i 0 := by
  by_cases hiMain : i < 11
  · exact weth10MainByteAt_eq_zero_0_11 locations n chainId
      domainSeparator i hiMain
  · have hdispatch :
        365 ≤ (fsig +++ dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape.byteSize := by
      rw [fsigFullDispatch_size]
      omega
    have hiDispatch :
        i - Ninst.calldatasize.size - Ninst.iszero.size - 4 <
          (fsig +++ dispatchWith fallbackSlot
            (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape.byteSize := by
      change i - 1 - 1 - 4 < _
      omega
    change
      Func.byteAtByShape locations n
          (Ninst.calldatasize ::: Ninst.iszero :::
            (receiveEther <?>
              (fsig +++ dispatchWith fallbackSlot
                (weth10Tree (⟨0, 0⟩ : DeployParams))))).compileShape
          (Ninst.calldatasize ::: Ninst.iszero :::
            (receiveEther <?>
              (fsig +++ dispatchWith fallbackSlot
                (weth10Tree ⟨chainId, domainSeparator⟩)))) i 0 =
        Func.byteAtByShape locations n
          (Ninst.calldatasize ::: Ninst.iszero :::
            (receiveEther <?>
              (fsig +++ dispatchWith fallbackSlot
                (weth10Tree (⟨0, 0⟩ : DeployParams))))).compileShape
          (Ninst.calldatasize ::: Ninst.iszero :::
            (receiveEther <?>
              (fsig +++ dispatchWith fallbackSlot
                (weth10Tree (⟨0, 0⟩ : DeployParams))))) i 0
    conv_lhs => rw [byteAt_main_to_dispatch
      (p := dispatchWith fallbackSlot
        (weth10Tree (⟨0, 0⟩ : DeployParams)))
      (q := dispatchWith fallbackSlot
        (weth10Tree ⟨chainId, domainSeparator⟩))
      (i := i) (d := 0) (hlo := by omega)
      (hinside := hiDispatch)]
    conv_rhs => rw [byteAt_main_to_dispatch
      (p := dispatchWith fallbackSlot
        (weth10Tree (⟨0, 0⟩ : DeployParams)))
      (q := dispatchWith fallbackSlot
        (weth10Tree (⟨0, 0⟩ : DeployParams)))
      (i := i) (d := 0) (hlo := by omega)
      (hinside := hiDispatch)]
    apply weth10DispatchByteAt_eq_zero_0_360
    omega

private theorem weth10MainEmitTake_eq_zero_371
    (locations : List Nat) (n : Nat) (chainId domainSeparator : B256) :
    (Func.emitByShape locations n
        (weth10 (⟨0, 0⟩ : DeployParams)).main.compileShape
        (weth10 ⟨chainId, domainSeparator⟩).main).take 371 =
      (Func.emitByShape locations n
        (weth10 (⟨0, 0⟩ : DeployParams)).main.compileShape
        (weth10 (⟨0, 0⟩ : DeployParams)).main).take 371 := by
  apply Bytes.take_eq_take_of_getD_eq (d := 0)
  · rw [Func.length_emitByShape]
    exact le_trans (by omega) weth10ZeroMain_size_lower
  · rw [Func.length_emitByShape]
    exact le_trans (by omega) weth10ZeroMain_size_lower
  · intro i hi
    rw [Func.getD_emitByShape, Func.getD_emitByShape]
    exact weth10MainByteAt_eq_zero_0_371 locations n chainId
      domainSeparator i hi

private def weth10ZeroShapes : List Func.CompileShape :=
  (weth10 (⟨0, 0⟩ : DeployParams)).main.compileShape ::
    weth10Aux.map Func.compileShape

private def weth10RuntimeLocations : List Nat :=
  Func.CompileShape.locations 0 weth10ZeroShapes

private lemma List.getD_cons_of_pos {α : Type} (x : α) (xs : List α)
    (i : Nat) (d : α) (hi : 0 < i) :
    (x :: xs).getD i d = xs.getD (i - 1) d := by
  cases i with
  | zero => omega
  | succ i => rfl

private lemma List.getD_append_of_lt {α : Type} (xs ys : List α)
    (i : Nat) (d : α) (hi : i < xs.length) :
    (xs ++ ys).getD i d = xs.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append, hi]

private theorem Bytes.sliceD_eq_drop_take_of_getD_eq
    (xs ys : Bytes) (start len : Nat)
    (hys : start + len ≤ ys.length)
    (hget : ∀ j, j < len →
      xs.getD (start + j) 0 = ys.getD (start + j) 0) :
    xs.sliceD start len 0 = (ys.drop start).take len := by
  calc
    xs.sliceD start len 0 = ys.sliceD start len 0 := by
      rw [List.sliceD_eq_map, List.sliceD_eq_map]
      apply List.map_congr_left
      intro j hj
      exact hget j (List.mem_range.mp hj)
    _ = (ys.drop start).take len := by
      unfold List.sliceD
      rw [List.takeD_eq_take _ (by
        simp only [List.length_drop]
        omega)]

private theorem weth10CodeGetD_to_main
    (dp : DeployParams) (i : Nat) (hlo : 1 ≤ i)
    (hinside : i - 1 <
      (weth10Main
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize) :
    (weth10Code dp).getD i 0 =
      Func.byteAtByShape weth10RuntimeLocations 1
        (weth10Main (⟨0, 0⟩ : DeployParams)).compileShape
        (weth10Main dp) (i - 1) 0 := by
  rw [weth10Code_eq_emitByZeroShape]
  unfold weth10RuntimeLocations weth10ZeroShapes
  simp only [Prog.emitByShape, Prog.compileShape, weth10,
    Table.emitByShape, Func.CompileShape.locations]
  rw [List.getD_append_of_lt]
  · rw [List.getD_cons_of_pos _ _ i 0 (by omega)]
    rw [Func.getD_emitByShape]
  · simp only [List.length_cons, Func.length_emitByShape]
    omega

private theorem weth10CodeGetD_to_dispatch
    (dp : DeployParams) (i : Nat) (hlo : 12 ≤ i)
    (hinside : i - 12 <
      (dispatchWith fallbackSlot
        (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape.byteSize) :
    (weth10Code dp).getD i 0 =
      Func.byteAtByShape weth10RuntimeLocations 12
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot (weth10Tree dp)) (i - 12) 0 := by
  have hdispatchSize :
      (dispatchWith fallbackSlot
        (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape.byteSize =
        3939 := by
    exact fullDispatch_size
  have hmain :
      3950 ≤ (weth10Main
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize :=
    weth10ZeroMain_size_lower
  rw [weth10CodeGetD_to_main dp i (by omega) (by omega)]
  have hroute := weth10MainByteAt_to_dispatch_inside
    weth10RuntimeLocations 1 dp (i - 1) 0 (by omega) (by omega)
  have hn : 1 + 11 = 12 := by omega
  have hi : i - 1 - 11 = i - 12 := by omega
  rw [hn, hi] at hroute
  exact hroute

private theorem weth10CodeGetD_eq_zero_of_dispatch
    (dp : DeployParams) (i : Nat) (hlo : 12 ≤ i)
    (hinside : i - 12 <
      (dispatchWith fallbackSlot
        (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape.byteSize)
    (hbyte :
      Func.byteAtByShape weth10RuntimeLocations 12
          (dispatchWith fallbackSlot
            (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
          (dispatchWith fallbackSlot (weth10Tree dp)) (i - 12) 0 =
        Func.byteAtByShape weth10RuntimeLocations 12
          (dispatchWith fallbackSlot
            (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
          (dispatchWith fallbackSlot
            (weth10Tree (⟨0, 0⟩ : DeployParams))) (i - 12) 0) :
    (weth10Code dp).getD i 0 = weth10RuntimeTemplate.getD i 0 := by
  rw [weth10CodeGetD_to_dispatch dp i hlo hinside]
  rw [weth10RuntimeTemplate_eq_code]
  rw [weth10CodeGetD_to_dispatch (⟨0, 0⟩ : DeployParams) i hlo hinside]
  exact hbyte

private theorem byteAt_pushDeployWord_data
    (locations : List Nat) (n : Nat) (p0 p : Func) (w : B256)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n (pushDeployWord 0 ::: p0).compileShape
        (pushDeployWord w ::: p) (j + 1) 0 =
      w.toBytes.getD j 0 := by
  rw [Func.compileShape, Func.byteAtByShape]
  rw [if_pos (by
    simp only [pushDeployWord, Ninst.size, B256.length_toBytes]
    omega)]
  rw [List.getD_takeD]
  rw [if_pos (by
    simp only [pushDeployWord, Ninst.size, B256.length_toBytes]
    omega)]
  simp only [pushDeployWord, Ninst.toBytes, pushToB8L,
    List.getD_cons_succ]

private theorem deploymentChainIdByteAt_word
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (deploymentChainId
          (⟨0, 0⟩ : DeployParams)).compileShape
        (deploymentChainId dp) (1 + j) 0 =
      dp.deploymentChainId.toBytes.getD j 0 := by
  unfold deploymentChainId returnDeployWord
  simpa [Nat.add_comm] using
    (byteAt_pushDeployWord_data locations n
      (mstoreAt 0 +++ returnMemoryRange 0 32)
      (mstoreAt 0 +++ returnMemoryRange 0 32)
      dp.deploymentChainId j hj)

private theorem nonpayableDeploymentChainIdByteAt_word
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (nonpayable (deploymentChainId
          (⟨0, 0⟩ : DeployParams))).compileShape
        (nonpayable (deploymentChainId dp)) (11 + j) 0 =
      dp.deploymentChainId.toBytes.getD j 0 := by
  change
    Func.byteAtByShape locations n
        (nonpayablePrefix +++
          Func.branch Func.rev
            (deploymentChainId
              (⟨0, 0⟩ : DeployParams))).compileShape
        (nonpayablePrefix +++
          Func.branch Func.rev (deploymentChainId dp)) (11 + j) 0 = _
  have hpreSize : prefixByteSize nonpayablePrefix = 2 := by decide +kernel
  have hrevSize : Func.rev.compileShape.byteSize = 3 := by decide +kernel
  conv_lhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n) (l := nonpayablePrefix)
      (p0 := Func.branch Func.rev
        (deploymentChainId (⟨0, 0⟩ : DeployParams)))
      (p := Func.branch Func.rev (deploymentChainId dp))
      (i := 11 + j) (d := 0) (by rw [hpreSize]; omega)]
  simp only [hpreSize]
  change
    Func.byteAtByShape locations (n + 2)
        (.branch Func.rev.compileShape
          (deploymentChainId
            (⟨0, 0⟩ : DeployParams)).compileShape)
        (.branch Func.rev (deploymentChainId dp)) (11 + j - 2) 0 = _
  conv_lhs => rw [byteAt_branch_to_right
      (locations := locations) (n := n + 2)
      (left0 := Func.rev)
      (right0 := deploymentChainId (⟨0, 0⟩ : DeployParams))
      (left := Func.rev) (right := deploymentChainId dp)
      (i := 11 + j - 2) (d := 0) (by rw [hrevSize]; omega)]
  simp only [hrevSize]
  have hi : 11 + j - 2 - (5 + 3) = 1 + j := by omega
  rw [hi]
  exact deploymentChainIdByteAt_word locations (n + 2 + 5 + 3) dp j hj

private theorem deploymentChainIdLeafByteAt_word
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (deploymentChainIdLeaf
          (⟨0, 0⟩ : DeployParams)).compileShape
        (deploymentChainIdLeaf dp) (26 + j) 0 =
      dp.deploymentChainId.toBytes.getD j 0 := by
  unfold deploymentChainIdLeaf
  have hpreSize : prefixByteSize deploymentChainIdLeafPrefix = 6 := by
    decide +kernel
  have hcallSize : (Func.call fallbackSlot).compileShape.byteSize = 4 := by
    decide +kernel
  conv_lhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n) (l := deploymentChainIdLeafPrefix)
      (p0 := Func.branch (.call fallbackSlot)
        (nonpayable (deploymentChainId
          (⟨0, 0⟩ : DeployParams))))
      (p := Func.branch (.call fallbackSlot)
        (nonpayable (deploymentChainId dp)))
      (i := 26 + j) (d := 0) (by rw [hpreSize]; omega)]
  simp only [hpreSize]
  change
    Func.byteAtByShape locations (n + 6)
        (.branch (Func.call fallbackSlot).compileShape
          (nonpayable (deploymentChainId
            (⟨0, 0⟩ : DeployParams))).compileShape)
        (.branch (.call fallbackSlot)
          (nonpayable (deploymentChainId dp))) (26 + j - 6) 0 = _
  conv_lhs => rw [byteAt_branch_to_right
      (locations := locations) (n := n + 6)
      (left0 := .call fallbackSlot)
      (right0 := nonpayable (deploymentChainId
        (⟨0, 0⟩ : DeployParams)))
      (left := .call fallbackSlot)
      (right := nonpayable (deploymentChainId dp))
      (i := 26 + j - 6) (d := 0) (by rw [hcallSize]; omega)]
  simp only [hcallSize]
  have hi : 26 + j - 6 - (5 + 4) = 11 + j := by omega
  rw [hi]
  exact nonpayableDeploymentChainIdByteAt_word
    locations (n + 6 + 5 + 4) dp j hj

private theorem deploymentPairDispatchByteAt_word
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (deploymentPairDispatch
          (⟨0, 0⟩ : DeployParams)).compileShape
        (deploymentPairDispatch dp) (37 + j) 0 =
      dp.deploymentChainId.toBytes.getD j 0 := by
  unfold deploymentPairDispatch
  have hpush :
      (Ninst.pushB256 (selector "deploymentChainId" [])).size = 5 := by
    decide +kernel
  have honSize :
      58 ≤ (deploymentChainIdLeaf
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize := by
    rw [deploymentChainIdLeaf_size]
    omega
  conv_lhs => rw [dispatchNodeByteAt_to_onPath
      (locations := locations) (n := n)
      (selector := selector "deploymentChainId" [])
      (off0 := approveAndCallLeaf)
      (on0 := deploymentChainIdLeaf (⟨0, 0⟩ : DeployParams))
      (off := approveAndCallLeaf) (on := deploymentChainIdLeaf dp)
      (i := 37 + j) (d := 0) hpush (by omega) (by omega)]
  have hi : 37 + j - 11 = 26 + j := by omega
  rw [hi]
  exact deploymentChainIdLeafByteAt_word locations (n + 11) dp j hj

private theorem deploymentDispatchByteAt_word
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (deploymentDispatch
          (⟨0, 0⟩ : DeployParams)).compileShape
        (deploymentDispatch dp) (113 + j) 0 =
      dp.deploymentChainId.toBytes.getD j 0 := by
  unfold deploymentDispatch
  have hpush : (Ninst.pushB256 (selector "deposit" [])).size = 5 := by
    decide +kernel
  have honSize : depositLeaf.compileShape.byteSize = 64 :=
    depositLeaf_size
  conv_lhs => rw [dispatchNodeByteAt_to_offPath
      (locations := locations) (n := n)
      (selector := selector "deposit" [])
      (off0 := deploymentPairDispatch (⟨0, 0⟩ : DeployParams))
      (on0 := depositLeaf)
      (off := deploymentPairDispatch dp) (on := depositLeaf)
      (i := 113 + j) (d := 0) hpush (by rw [honSize]; omega)]
  simp only [honSize]
  have hi : 113 + j - (12 + 64) = 37 + j := by omega
  rw [hi]
  exact deploymentPairDispatchByteAt_word locations (n + 12 + 64) dp j hj

private theorem dispatch24_21_3ByteAt_chainWord
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (dispatch24_21_3
          (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch24_21_3 dp) (113 + j) 0 =
      dp.deploymentChainId.toBytes.getD j 0 := by
  rw [dispatch24_21_3_eq_deploymentDispatch dp,
    dispatch24_21_3_eq_deploymentDispatch
      (⟨0, 0⟩ : DeployParams)]
  exact deploymentDispatchByteAt_word locations n dp j hj

private theorem dispatchD505ByteAt_deploymentChainWord
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (dispatchD505 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatchD505 dp) (657 + j) 0 =
      dp.deploymentChainId.toBytes.getD j 0 := by
  unfold dispatchD505
  have hpush : (Ninst.pushB256 (0xd505accf : B256)).size = 5 := by
    decide +kernel
  have honSize :
      (dispatchDd
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 532 :=
    dispatchDd_size
  conv_lhs => rw [dispatchNodeByteAt_to_offPath
      (locations := locations) (n := n) (selector := 0xd505accf)
      (off0 := dispatch24_21_3 (⟨0, 0⟩ : DeployParams))
      (on0 := dispatchDd (⟨0, 0⟩ : DeployParams))
      (off := dispatch24_21_3 dp) (on := dispatchDd dp)
      (i := 657 + j) (d := 0) hpush (by rw [honSize]; omega)]
  simp only [honSize]
  have hi : 657 + j - (12 + 532) = 113 + j := by omega
  rw [hi]
  exact dispatch24_21_3ByteAt_chainWord
    locations (n + 12 + 532) dp j hj

private theorem dispatchCae9ByteAt_deploymentChainWord
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (dispatchCae9 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatchCae9 dp) (668 + j) 0 =
      dp.deploymentChainId.toBytes.getD j 0 := by
  unfold dispatchCae9
  have hpush : (Ninst.pushB256 (0xcae9ca51 : B256)).size = 5 := by
    decide +kernel
  have honSize :
      700 ≤ (dispatchD505
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize := by
    rw [dispatchD505_size]
    omega
  conv_lhs => rw [dispatchNodeByteAt_to_onPath
      (locations := locations) (n := n) (selector := 0xcae9ca51)
      (off0 := dispatch25_14_7 (⟨0, 0⟩ : DeployParams))
      (on0 := dispatchD505 (⟨0, 0⟩ : DeployParams))
      (off := dispatch25_14_7 dp) (on := dispatchD505 dp)
      (i := 668 + j) (d := 0) hpush (by omega) (by omega)]
  have hi : 668 + j - 11 = 657 + j := by omega
  rw [hi]
  exact dispatchD505ByteAt_deploymentChainWord locations (n + 11) dp j hj

private theorem flashFeeDispatchByteAt_deploymentChainWord
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (flashFeeDispatch (⟨0, 0⟩ : DeployParams)).compileShape
        (flashFeeDispatch dp) (679 + j) 0 =
      dp.deploymentChainId.toBytes.getD j 0 := by
  unfold flashFeeDispatch
  have hpush : (Ninst.pushB256 (0x7ecebe00 : B256)).size = 5 := by
    decide +kernel
  have honSize :
      711 ≤ (dispatchCae9
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize := by
    rw [dispatchCae9_size]
    omega
  conv_lhs => rw [dispatchNodeByteAt_to_onPath
      (locations := locations) (n := n) (selector := 0x7ecebe00)
      (off0 := dispatch26_0_14 (⟨0, 0⟩ : DeployParams))
      (on0 := dispatchCae9 (⟨0, 0⟩ : DeployParams))
      (off := dispatch26_0_14 dp) (on := dispatchCae9 dp)
      (i := 679 + j) (d := 0) hpush (by omega) (by omega)]
  have hi : 679 + j - 11 = 668 + j := by omega
  rw [hi]
  exact dispatchCae9ByteAt_deploymentChainWord locations (n + 11) dp j hj

private theorem weth10DispatchByteAt_deploymentChainWord
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot (weth10Tree dp)) (679 + j) 0 =
      dp.deploymentChainId.toBytes.getD j 0 := by
  rw [flashFeeDispatch_eq dp,
    flashFeeDispatch_eq (⟨0, 0⟩ : DeployParams)]
  exact flashFeeDispatchByteAt_deploymentChainWord locations n dp j hj

private theorem deploymentChainIdLeafByteAt_eq_zero_58_64
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 58 ≤ i) (hi : i < 64) :
    Func.byteAtByShape locations n
        (deploymentChainIdLeaf
          (⟨0, 0⟩ : DeployParams)).compileShape
        (deploymentChainIdLeaf dp) i 0 =
      Func.byteAtByShape locations n
        (deploymentChainIdLeaf
          (⟨0, 0⟩ : DeployParams)).compileShape
        (deploymentChainIdLeaf (⟨0, 0⟩ : DeployParams)) i 0 := by
  unfold deploymentChainIdLeaf
  have hleafPrefix : prefixByteSize deploymentChainIdLeafPrefix = 6 := by
    decide +kernel
  conv_lhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n) (l := deploymentChainIdLeafPrefix)
      (p0 := Func.branch (.call fallbackSlot)
        (nonpayable (deploymentChainId
          (⟨0, 0⟩ : DeployParams))))
      (p := Func.branch (.call fallbackSlot)
        (nonpayable (deploymentChainId dp)))
      (i := i) (d := 0) (by rw [hleafPrefix]; omega)]
  conv_rhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n) (l := deploymentChainIdLeafPrefix)
      (p0 := Func.branch (.call fallbackSlot)
        (nonpayable (deploymentChainId
          (⟨0, 0⟩ : DeployParams))))
      (p := Func.branch (.call fallbackSlot)
        (nonpayable (deploymentChainId
          (⟨0, 0⟩ : DeployParams))))
      (i := i) (d := 0) (by rw [hleafPrefix]; omega)]
  simp only [hleafPrefix]
  have hcall : (Func.call fallbackSlot).compileShape.byteSize = 4 := by
    decide +kernel
  change
    Func.byteAtByShape locations (n + 6)
        (.branch (Func.call fallbackSlot).compileShape
          (nonpayable (deploymentChainId
            (⟨0, 0⟩ : DeployParams))).compileShape)
        (.branch (.call fallbackSlot)
          (nonpayable (deploymentChainId dp))) (i - 6) 0 =
      Func.byteAtByShape locations (n + 6)
        (.branch (Func.call fallbackSlot).compileShape
          (nonpayable (deploymentChainId
            (⟨0, 0⟩ : DeployParams))).compileShape)
        (.branch (.call fallbackSlot)
          (nonpayable (deploymentChainId
            (⟨0, 0⟩ : DeployParams)))) (i - 6) 0
  rw [byteAt_branch_to_right locations (n + 6) (.call fallbackSlot)
      (nonpayable (deploymentChainId (⟨0, 0⟩ : DeployParams)))
      (.call fallbackSlot) (nonpayable (deploymentChainId dp))
      (i - 6) 0 (by rw [hcall]; omega),
    byteAt_branch_to_right locations (n + 6) (.call fallbackSlot)
      (nonpayable (deploymentChainId (⟨0, 0⟩ : DeployParams)))
      (.call fallbackSlot)
      (nonpayable (deploymentChainId (⟨0, 0⟩ : DeployParams)))
      (i - 6) 0 (by rw [hcall]; omega)]
  simp only [hcall]
  change
    Func.byteAtByShape locations (n + 15)
        (nonpayablePrefix +++ Func.branch Func.rev
          (deploymentChainId (⟨0, 0⟩ : DeployParams))).compileShape
        (nonpayablePrefix +++ Func.branch Func.rev
          (deploymentChainId dp)) (i - 15) 0 =
      Func.byteAtByShape locations (n + 15)
        (nonpayablePrefix +++ Func.branch Func.rev
          (deploymentChainId (⟨0, 0⟩ : DeployParams))).compileShape
        (nonpayablePrefix +++ Func.branch Func.rev
          (deploymentChainId (⟨0, 0⟩ : DeployParams))) (i - 15) 0
  have hnonpayable : prefixByteSize nonpayablePrefix = 2 := by
    decide +kernel
  conv_lhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n + 15) (l := nonpayablePrefix)
      (p0 := Func.branch Func.rev
        (deploymentChainId (⟨0, 0⟩ : DeployParams)))
      (p := Func.branch Func.rev (deploymentChainId dp))
      (i := i - 15) (d := 0) (by rw [hnonpayable]; omega)]
  conv_rhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n + 15) (l := nonpayablePrefix)
      (p0 := Func.branch Func.rev
        (deploymentChainId (⟨0, 0⟩ : DeployParams)))
      (p := Func.branch Func.rev
        (deploymentChainId (⟨0, 0⟩ : DeployParams)))
      (i := i - 15) (d := 0) (by rw [hnonpayable]; omega)]
  simp only [hnonpayable]
  have hrev : Func.rev.compileShape.byteSize = 3 := by decide +kernel
  change
    Func.byteAtByShape locations (n + 17)
        (.branch Func.rev.compileShape
          (deploymentChainId
            (⟨0, 0⟩ : DeployParams)).compileShape)
        (.branch Func.rev (deploymentChainId dp)) (i - 15 - 2) 0 =
      Func.byteAtByShape locations (n + 17)
        (.branch Func.rev.compileShape
          (deploymentChainId
            (⟨0, 0⟩ : DeployParams)).compileShape)
        (.branch Func.rev
          (deploymentChainId (⟨0, 0⟩ : DeployParams)))
        (i - 15 - 2) 0
  rw [byteAt_branch_to_right locations (n + 17) Func.rev
      (deploymentChainId (⟨0, 0⟩ : DeployParams)) Func.rev
      (deploymentChainId dp) (i - 15 - 2) 0 (by rw [hrev]; omega),
    byteAt_branch_to_right locations (n + 17) Func.rev
      (deploymentChainId (⟨0, 0⟩ : DeployParams)) Func.rev
      (deploymentChainId (⟨0, 0⟩ : DeployParams))
      (i - 15 - 2) 0 (by rw [hrev]; omega)]
  simp only [hrev]
  unfold deploymentChainId returnDeployWord
  change
    Func.byteAtByShape locations (n + 17 + 5 + 3)
        (pushDeployWord 0 :::
          (mstoreAt 0 +++ returnMemoryRange 0 32)).compileShape
        (pushDeployWord dp.deploymentChainId :::
          (mstoreAt 0 +++ returnMemoryRange 0 32))
        (i - 15 - 2 - (5 + 3)) 0 =
      Func.byteAtByShape locations (n + 17 + 5 + 3)
        (pushDeployWord 0 :::
          (mstoreAt 0 +++ returnMemoryRange 0 32)).compileShape
        (pushDeployWord 0 :::
          (mstoreAt 0 +++ returnMemoryRange 0 32))
        (i - 15 - 2 - (5 + 3)) 0
  have hn : n + 17 + 5 + 3 = n + 25 := by omega
  have hiIndex : i - 15 - 2 - (5 + 3) = i - 25 := by omega
  rw [hn, hiIndex]
  have hpush : (pushDeployWord 0).size = 33 := by
    simp [pushDeployWord, Ninst.size, B256.length_toBytes]
  rw [byteAt_next_to_tail locations (n + 25)
      (pushDeployWord 0) (pushDeployWord dp.deploymentChainId)
      (mstoreAt 0 +++ returnMemoryRange 0 32)
      (mstoreAt 0 +++ returnMemoryRange 0 32)
      (i - 25) 0 (by rw [hpush]; omega),
    byteAt_next_to_tail locations (n + 25)
      (pushDeployWord 0) (pushDeployWord 0)
      (mstoreAt 0 +++ returnMemoryRange 0 32)
      (mstoreAt 0 +++ returnMemoryRange 0 32)
      (i - 25) 0 (by rw [hpush]; omega)]

private theorem deploymentDispatchByteAt_eq_zero_145_391
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 145 ≤ i) (hi : i < 391) :
    Func.byteAtByShape locations n
        (deploymentDispatch
          (⟨0, 0⟩ : DeployParams)).compileShape
        (deploymentDispatch dp) i 0 =
      Func.byteAtByShape locations n
        (deploymentDispatch
          (⟨0, 0⟩ : DeployParams)).compileShape
        (deploymentDispatch (⟨0, 0⟩ : DeployParams)) i 0 := by
  unfold deploymentDispatch
  have hdepositPush :
      (Ninst.pushB256 (selector "deposit" [])).size = 5 := by
    decide +kernel
  have hdeposit : depositLeaf.compileShape.byteSize = 64 :=
    depositLeaf_size
  rw [dispatchNodeByteAt_to_offPath locations n (selector "deposit" [])
      (deploymentPairDispatch (⟨0, 0⟩ : DeployParams)) depositLeaf
      (deploymentPairDispatch dp) depositLeaf i 0 hdepositPush (by
        rw [hdeposit]
        omega),
    dispatchNodeByteAt_to_offPath locations n (selector "deposit" [])
      (deploymentPairDispatch (⟨0, 0⟩ : DeployParams)) depositLeaf
      (deploymentPairDispatch (⟨0, 0⟩ : DeployParams)) depositLeaf
      i 0 hdepositPush (by rw [hdeposit]; omega)]
  simp only [hdeposit, Nat.reduceAdd]
  unfold deploymentPairDispatch
  have hdeploymentPush :
      (Ninst.pushB256 (selector "deploymentChainId" [])).size = 5 := by
    decide +kernel
  have hdeployment :
      (deploymentChainIdLeaf
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 64 :=
    deploymentChainIdLeaf_size
  by_cases hon : i < 151
  · rw [dispatchNodeByteAt_to_onPath locations (n + 76)
        (selector "deploymentChainId" []) approveAndCallLeaf
        (deploymentChainIdLeaf (⟨0, 0⟩ : DeployParams))
        approveAndCallLeaf (deploymentChainIdLeaf dp) (i - 76) 0
        hdeploymentPush (by omega) (by rw [hdeployment]; omega),
      dispatchNodeByteAt_to_onPath locations (n + 76)
        (selector "deploymentChainId" []) approveAndCallLeaf
        (deploymentChainIdLeaf (⟨0, 0⟩ : DeployParams))
        approveAndCallLeaf
        (deploymentChainIdLeaf (⟨0, 0⟩ : DeployParams))
        (i - 76) 0 hdeploymentPush (by omega)
        (by rw [hdeployment]; omega)]
    apply deploymentChainIdLeafByteAt_eq_zero_58_64
    · omega
    · omega
  · by_cases hjump : i = 151
    · subst i
      have hindex : 151 - 76 = 11 +
        (deploymentChainIdLeaf
          (⟨0, 0⟩ : DeployParams)).compileShape.byteSize := by
        rw [hdeployment]
      rw [hindex]
      exact dispatchNodeByteAt_eq_jumpdest locations (n + 76)
        (selector "deploymentChainId" []) approveAndCallLeaf
        (deploymentChainIdLeaf (⟨0, 0⟩ : DeployParams))
        approveAndCallLeaf (deploymentChainIdLeaf dp) hdeploymentPush
    · rw [dispatchNodeByteAt_to_offPath locations (n + 76)
          (selector "deploymentChainId" []) approveAndCallLeaf
          (deploymentChainIdLeaf (⟨0, 0⟩ : DeployParams))
          approveAndCallLeaf (deploymentChainIdLeaf dp) (i - 76) 0
          hdeploymentPush (by rw [hdeployment]; omega),
        dispatchNodeByteAt_to_offPath locations (n + 76)
          (selector "deploymentChainId" []) approveAndCallLeaf
          (deploymentChainIdLeaf (⟨0, 0⟩ : DeployParams))
          approveAndCallLeaf
          (deploymentChainIdLeaf (⟨0, 0⟩ : DeployParams))
          (i - 76) 0 hdeploymentPush (by rw [hdeployment]; omega)]

private theorem dispatchD505ByteAt_eq_zero_689_935
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 689 ≤ i) (hi : i < 935) :
    Func.byteAtByShape locations n
        (dispatchD505 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatchD505 dp) i 0 =
      Func.byteAtByShape locations n
        (dispatchD505 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatchD505 (⟨0, 0⟩ : DeployParams)) i 0 := by
  unfold dispatchD505
  have hpush : (Ninst.pushB256 (0xd505accf : B256)).size = 5 := by
    decide +kernel
  have hdd :
      (dispatchDd
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 532 :=
    dispatchDd_size
  rw [dispatchNodeByteAt_to_offPath locations n 0xd505accf
      (dispatch24_21_3 (⟨0, 0⟩ : DeployParams))
      (dispatchDd (⟨0, 0⟩ : DeployParams))
      (dispatch24_21_3 dp) (dispatchDd dp) i 0 hpush (by
        rw [hdd]
        omega),
    dispatchNodeByteAt_to_offPath locations n 0xd505accf
      (dispatch24_21_3 (⟨0, 0⟩ : DeployParams))
      (dispatchDd (⟨0, 0⟩ : DeployParams))
      (dispatch24_21_3 (⟨0, 0⟩ : DeployParams))
      (dispatchDd (⟨0, 0⟩ : DeployParams)) i 0 hpush (by
        rw [hdd]
        omega)]
  simp only [hdd, Nat.reduceAdd]
  rw [dispatch24_21_3_eq_deploymentDispatch dp,
    dispatch24_21_3_eq_deploymentDispatch
      (⟨0, 0⟩ : DeployParams)]
  apply deploymentDispatchByteAt_eq_zero_145_391
  · omega
  · omega

private theorem dispatchCae9ByteAt_eq_zero_700_1769
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 700 ≤ i) (hi : i < 1769) :
    Func.byteAtByShape locations n
        (dispatchCae9 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatchCae9 dp) i 0 =
      Func.byteAtByShape locations n
        (dispatchCae9 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatchCae9 (⟨0, 0⟩ : DeployParams)) i 0 := by
  unfold dispatchCae9
  have hpush : (Ninst.pushB256 (0xcae9ca51 : B256)).size = 5 := by
    decide +kernel
  have hd505 :
      (dispatchD505
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 935 :=
    dispatchD505_size
  by_cases hon : i < 946
  · rw [dispatchNodeByteAt_to_onPath locations n 0xcae9ca51
        (dispatch25_14_7 (⟨0, 0⟩ : DeployParams))
        (dispatchD505 (⟨0, 0⟩ : DeployParams))
        (dispatch25_14_7 dp) (dispatchD505 dp) i 0 hpush (by omega)
        (by rw [hd505]; omega),
      dispatchNodeByteAt_to_onPath locations n 0xcae9ca51
        (dispatch25_14_7 (⟨0, 0⟩ : DeployParams))
        (dispatchD505 (⟨0, 0⟩ : DeployParams))
        (dispatch25_14_7 (⟨0, 0⟩ : DeployParams))
        (dispatchD505 (⟨0, 0⟩ : DeployParams)) i 0 hpush (by omega)
        (by rw [hd505]; omega)]
    apply dispatchD505ByteAt_eq_zero_689_935
    · omega
    · omega
  · by_cases hjump : i = 946
    · subst i
      have hindex : 946 = 11 +
          (dispatchD505
            (⟨0, 0⟩ : DeployParams)).compileShape.byteSize := by
        rw [hd505]
      rw [hindex]
      exact dispatchNodeByteAt_eq_jumpdest locations n 0xcae9ca51
        (dispatch25_14_7 (⟨0, 0⟩ : DeployParams))
        (dispatchD505 (⟨0, 0⟩ : DeployParams))
        (dispatch25_14_7 dp) (dispatchD505 dp) hpush
    · rw [dispatchNodeByteAt_to_offPath locations n 0xcae9ca51
          (dispatch25_14_7 (⟨0, 0⟩ : DeployParams))
          (dispatchD505 (⟨0, 0⟩ : DeployParams))
          (dispatch25_14_7 dp) (dispatchD505 dp) i 0 hpush (by
            rw [hd505]
            omega),
        dispatchNodeByteAt_to_offPath locations n 0xcae9ca51
          (dispatch25_14_7 (⟨0, 0⟩ : DeployParams))
          (dispatchD505 (⟨0, 0⟩ : DeployParams))
          (dispatch25_14_7 (⟨0, 0⟩ : DeployParams))
          (dispatchD505 (⟨0, 0⟩ : DeployParams)) i 0 hpush (by
            rw [hd505]
            omega)]
      rw [dispatch25_14_7_eq_zero dp]

private theorem weth10DispatchByteAt_eq_zero_711_1780
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 711 ≤ i) (hi : i < 1780) :
    Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot (weth10Tree dp)) i 0 =
      Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))) i 0 := by
  rw [flashFeeDispatch_eq dp,
    flashFeeDispatch_eq (⟨0, 0⟩ : DeployParams)]
  unfold flashFeeDispatch
  have hpush : (Ninst.pushB256 (0x7ecebe00 : B256)).size = 5 := by
    decide +kernel
  have hcae9 :
      (dispatchCae9
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 1769 :=
    dispatchCae9_size
  rw [dispatchNodeByteAt_to_onPath locations n 0x7ecebe00
      (dispatch26_0_14 (⟨0, 0⟩ : DeployParams))
      (dispatchCae9 (⟨0, 0⟩ : DeployParams))
      (dispatch26_0_14 dp) (dispatchCae9 dp) i 0 hpush (by omega)
      (by rw [hcae9]; omega),
    dispatchNodeByteAt_to_onPath locations n 0x7ecebe00
      (dispatch26_0_14 (⟨0, 0⟩ : DeployParams))
      (dispatchCae9 (⟨0, 0⟩ : DeployParams))
      (dispatch26_0_14 (⟨0, 0⟩ : DeployParams))
      (dispatchCae9 (⟨0, 0⟩ : DeployParams)) i 0 hpush (by omega)
      (by rw [hcae9]; omega)]
  apply dispatchCae9ByteAt_eq_zero_700_1769
  · omega
  · omega

private theorem weth10DispatchByteAt_eq_zero_1780
    (locations : List Nat) (n : Nat) (dp : DeployParams) :
    Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot (weth10Tree dp)) 1780 0 =
      Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))) 1780 0 := by
  rw [flashFeeDispatch_eq dp,
    flashFeeDispatch_eq (⟨0, 0⟩ : DeployParams)]
  unfold flashFeeDispatch
  have hpush : (Ninst.pushB256 (0x7ecebe00 : B256)).size = 5 := by
    decide +kernel
  have hcae9 :
      (dispatchCae9
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 1769 :=
    dispatchCae9_size
  have hindex : 1780 = 11 +
      (dispatchCae9
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize := by
    rw [hcae9]
  rw [hindex]
  exact dispatchNodeByteAt_eq_jumpdest locations n 0x7ecebe00
    (dispatch26_0_14 (⟨0, 0⟩ : DeployParams))
    (dispatchCae9 (⟨0, 0⟩ : DeployParams))
    (dispatch26_0_14 dp) (dispatchCae9 dp) hpush

private theorem permitByteAt_chainWord
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (permit (⟨0, 0⟩ : DeployParams)).compileShape
        (permit dp) (121 + j) 0 =
      dp.deploymentChainId.toBytes.getD j 0 := by
  rw [permit_eq_factored dp,
    permit_eq_factored (⟨0, 0⟩ : DeployParams)]
  unfold permitFactored
  have hguard : prefixByteSize permitGuardPrefix = 5 := by decide +kernel
  conv_lhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n) (l := permitGuardPrefix)
      (p0 := Func.branch
        (permitCoreX (⟨0, 0⟩ : DeployParams)) (.call expiredPermitErrorSlot))
      (p := Func.branch (permitCoreX dp) (.call expiredPermitErrorSlot))
      (i := 121 + j) (d := 0) (by rw [hguard]; omega)]
  simp only [hguard]
  have hcoreSize :
      144 ≤ (permitCoreX
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize := by
    rw [permitCoreX_size]
    omega
  change
    Func.byteAtByShape locations (n + 5)
        (.branch
          (permitCoreX (⟨0, 0⟩ : DeployParams)).compileShape
          (Func.call expiredPermitErrorSlot).compileShape)
        (.branch (permitCoreX dp) (.call expiredPermitErrorSlot))
        (121 + j - 5) 0 = _
  conv_lhs => rw [byteAt_branch_to_left
      (locations := locations) (n := n + 5)
      (left0 := permitCoreX (⟨0, 0⟩ : DeployParams))
      (right0 := .call expiredPermitErrorSlot)
      (left := permitCoreX dp) (right := .call expiredPermitErrorSlot)
      (i := 121 + j - 5) (d := 0) (by omega) (by omega)]
  unfold permitCoreX
  have hcore : prefixByteSize permitCorePrefix = 111 := by decide +kernel
  conv_lhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n + 5 + 4)
      (l := permitCorePrefix)
      (p0 := permitCoreTail (⟨0, 0⟩ : DeployParams))
      (p := permitCoreTail dp) (i := 121 + j - 5 - 4) (d := 0)
      (by rw [hcore]; omega)]
  simp only [hcore]
  unfold permitCoreTail
  have hi : 121 + j - 5 - 4 - 111 = j + 1 := by omega
  rw [hi]
  exact byteAt_pushDeployWord_data locations (n + 5 + 4 + 111)
    _ _ dp.deploymentChainId j hj

private theorem nonpayablePermitByteAt_chainWord
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (nonpayable (permit (⟨0, 0⟩ : DeployParams))).compileShape
        (nonpayable (permit dp)) (131 + j) 0 =
      dp.deploymentChainId.toBytes.getD j 0 := by
  change
    Func.byteAtByShape locations n
        (nonpayablePrefix +++
          Func.branch Func.rev
            (permit (⟨0, 0⟩ : DeployParams))).compileShape
        (nonpayablePrefix +++ Func.branch Func.rev (permit dp))
        (131 + j) 0 = _
  have hpreSize : prefixByteSize nonpayablePrefix = 2 := by decide +kernel
  have hrevSize : Func.rev.compileShape.byteSize = 3 := by decide +kernel
  conv_lhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n) (l := nonpayablePrefix)
      (p0 := Func.branch Func.rev
        (permit (⟨0, 0⟩ : DeployParams)))
      (p := Func.branch Func.rev (permit dp))
      (i := 131 + j) (d := 0) (by rw [hpreSize]; omega)]
  simp only [hpreSize]
  change
    Func.byteAtByShape locations (n + 2)
        (.branch Func.rev.compileShape
          (permit (⟨0, 0⟩ : DeployParams)).compileShape)
        (.branch Func.rev (permit dp)) (131 + j - 2) 0 = _
  conv_lhs => rw [byteAt_branch_to_right
      (locations := locations) (n := n + 2)
      (left0 := Func.rev)
      (right0 := permit (⟨0, 0⟩ : DeployParams))
      (left := Func.rev) (right := permit dp)
      (i := 131 + j - 2) (d := 0) (by rw [hrevSize]; omega)]
  simp only [hrevSize]
  have hi : 131 + j - 2 - (5 + 3) = 121 + j := by omega
  rw [hi]
  exact permitByteAt_chainWord locations (n + 2 + 5 + 3) dp j hj

private theorem dispatch22_24_1ByteAt_chainWord
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (dispatch22_24_1 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch22_24_1 dp) (146 + j) 0 =
      dp.deploymentChainId.toBytes.getD j 0 := by
  rw [dispatch22_24_1_eq_permit dp,
    dispatch22_24_1_eq_permit (⟨0, 0⟩ : DeployParams)]
  change
    Func.byteAtByShape locations n
        (permitLeafPrefix +++
          Func.branch (.call fallbackSlot)
            (nonpayable (permit (⟨0, 0⟩ : DeployParams)))).compileShape
        (permitLeafPrefix +++
          Func.branch (.call fallbackSlot) (nonpayable (permit dp)))
        (146 + j) 0 = _
  have hpreSize : prefixByteSize permitLeafPrefix = 6 := by decide +kernel
  have hcallSize : (Func.call fallbackSlot).compileShape.byteSize = 4 := by
    decide +kernel
  conv_lhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n) (l := permitLeafPrefix)
      (p0 := Func.branch (.call fallbackSlot)
        (nonpayable (permit (⟨0, 0⟩ : DeployParams))))
      (p := Func.branch (.call fallbackSlot) (nonpayable (permit dp)))
      (i := 146 + j) (d := 0) (by rw [hpreSize]; omega)]
  simp only [hpreSize]
  change
    Func.byteAtByShape locations (n + 6)
        (.branch (Func.call fallbackSlot).compileShape
          (nonpayable
            (permit (⟨0, 0⟩ : DeployParams))).compileShape)
        (.branch (.call fallbackSlot) (nonpayable (permit dp)))
        (146 + j - 6) 0 = _
  conv_lhs => rw [byteAt_branch_to_right
      (locations := locations) (n := n + 6)
      (left0 := .call fallbackSlot)
      (right0 := nonpayable (permit (⟨0, 0⟩ : DeployParams)))
      (left := .call fallbackSlot) (right := nonpayable (permit dp))
      (i := 146 + j - 6) (d := 0) (by rw [hcallSize]; omega)]
  simp only [hcallSize]
  have hi : 146 + j - 6 - (5 + 4) = 131 + j := by omega
  rw [hi]
  exact nonpayablePermitByteAt_chainWord
    locations (n + 6 + 5 + 4) dp j hj

private theorem dispatchD9ByteAt_chainWord
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (dispatchD9 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatchD9 dp) (205 + j) 0 =
      dp.deploymentChainId.toBytes.getD j 0 := by
  unfold dispatchD9
  have hpush : (Ninst.pushB256 (0xd9d98ce4 : B256)).size = 5 := by
    decide +kernel
  have honSize : flashFeeLeaf.compileShape.byteSize = 47 := by
    exact flashFeeLeaf_size
  conv_lhs => rw [dispatchNodeByteAt_to_offPath
      (locations := locations) (n := n) (selector := 0xd9d98ce4)
      (off0 := dispatch22_24_1 (⟨0, 0⟩ : DeployParams))
      (on0 := flashFeeLeaf) (off := dispatch22_24_1 dp)
      (on := flashFeeLeaf) (i := 205 + j) (d := 0) hpush (by
        rw [honSize]
        omega)]
  simp only [honSize]
  have hi : 205 + j - (12 + 47) = 146 + j := by omega
  rw [hi]
  exact dispatch22_24_1ByteAt_chainWord locations (n + 12 + 47) dp j hj

private theorem dispatchDdByteAt_chainWord
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (dispatchDd (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatchDd dp) (327 + j) 0 =
      dp.deploymentChainId.toBytes.getD j 0 := by
  unfold dispatchDd
  have hpush : (Ninst.pushB256 (0xdd62ed3e : B256)).size = 5 := by
    decide +kernel
  have honSize :
      (dispatch23_26_1
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 110 := by
    exact dispatch23_26_1_size
  conv_lhs => rw [dispatchNodeByteAt_to_offPath
      (locations := locations) (n := n) (selector := 0xdd62ed3e)
      (off0 := dispatchD9 (⟨0, 0⟩ : DeployParams))
      (on0 := dispatch23_26_1 (⟨0, 0⟩ : DeployParams))
      (off := dispatchD9 dp) (on := dispatch23_26_1 dp)
      (i := 327 + j) (d := 0) hpush (by rw [honSize]; omega)]
  simp only [honSize]
  have hi : 327 + j - (12 + 110) = 205 + j := by omega
  rw [hi]
  exact dispatchD9ByteAt_chainWord locations (n + 12 + 110) dp j hj

private theorem dispatchD505ByteAt_chainWord
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (dispatchD505 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatchD505 dp) (338 + j) 0 =
      dp.deploymentChainId.toBytes.getD j 0 := by
  unfold dispatchD505
  have hpush : (Ninst.pushB256 (0xd505accf : B256)).size = 5 := by
    decide +kernel
  have honSize :
      359 ≤ (dispatchDd
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize := by
    rw [dispatchDd_size]
    omega
  conv_lhs => rw [dispatchNodeByteAt_to_onPath
      (locations := locations) (n := n) (selector := 0xd505accf)
      (off0 := dispatch24_21_3 (⟨0, 0⟩ : DeployParams))
      (on0 := dispatchDd (⟨0, 0⟩ : DeployParams))
      (off := dispatch24_21_3 dp) (on := dispatchDd dp)
      (i := 338 + j) (d := 0) hpush (by omega) (by omega)]
  have hi : 338 + j - 11 = 327 + j := by omega
  rw [hi]
  exact dispatchDdByteAt_chainWord locations (n + 11) dp j hj

private theorem dispatchCae9ByteAt_chainWord
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (dispatchCae9 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatchCae9 dp) (349 + j) 0 =
      dp.deploymentChainId.toBytes.getD j 0 := by
  unfold dispatchCae9
  have hpush : (Ninst.pushB256 (0xcae9ca51 : B256)).size = 5 := by
    decide +kernel
  have honSize :
      370 ≤ (dispatchD505
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize := by
    rw [dispatchD505_size]
    omega
  conv_lhs => rw [dispatchNodeByteAt_to_onPath
      (locations := locations) (n := n) (selector := 0xcae9ca51)
      (off0 := dispatch25_14_7 (⟨0, 0⟩ : DeployParams))
      (on0 := dispatchD505 (⟨0, 0⟩ : DeployParams))
      (off := dispatch25_14_7 dp) (on := dispatchD505 dp)
      (i := 349 + j) (d := 0) hpush (by omega) (by omega)]
  have hi : 349 + j - 11 = 338 + j := by omega
  rw [hi]
  exact dispatchD505ByteAt_chainWord locations (n + 11) dp j hj

private theorem flashFeeDispatchByteAt_chainWord
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (flashFeeDispatch (⟨0, 0⟩ : DeployParams)).compileShape
        (flashFeeDispatch dp) (360 + j) 0 =
      dp.deploymentChainId.toBytes.getD j 0 := by
  unfold flashFeeDispatch
  have hpush : (Ninst.pushB256 (0x7ecebe00 : B256)).size = 5 := by
    decide +kernel
  have honSize :
      381 ≤ (dispatchCae9
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize := by
    rw [dispatchCae9_size]
    omega
  conv_lhs => rw [dispatchNodeByteAt_to_onPath
      (locations := locations) (n := n) (selector := 0x7ecebe00)
      (off0 := dispatch26_0_14 (⟨0, 0⟩ : DeployParams))
      (on0 := dispatchCae9 (⟨0, 0⟩ : DeployParams))
      (off := dispatch26_0_14 dp) (on := dispatchCae9 dp)
      (i := 360 + j) (d := 0) hpush (by omega) (by omega)]
  have hi : 360 + j - 11 = 349 + j := by omega
  rw [hi]
  exact dispatchCae9ByteAt_chainWord locations (n + 11) dp j hj

private theorem weth10DispatchByteAt_chainWord
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot (weth10Tree dp)) (360 + j) 0 =
      dp.deploymentChainId.toBytes.getD j 0 := by
  rw [flashFeeDispatch_eq dp,
    flashFeeDispatch_eq (⟨0, 0⟩ : DeployParams)]
  exact flashFeeDispatchByteAt_chainWord locations n dp j hj

private theorem weth10Code_getD_chainWord
    (dp : DeployParams) (j : Nat) (hj : j < 32) :
    (weth10Code dp).getD (372 + j) 0 =
      dp.deploymentChainId.toBytes.getD j 0 := by
  rw [weth10CodeGetD_to_dispatch dp (372 + j) (by omega) (by
    have hdispatch :
        (dispatchWith fallbackSlot
          (weth10Tree
            (⟨0, 0⟩ : DeployParams))).compileShape.byteSize = 3939 := by
      exact fullDispatch_size
    omega)]
  have hi : 372 + j - 12 = 360 + j := by omega
  rw [hi]
  exact weth10DispatchByteAt_chainWord weth10RuntimeLocations 12 dp j hj

private theorem weth10Code_slice_372_404
    (chainId domainSeparator : B256) :
    (weth10Code ⟨chainId, domainSeparator⟩).sliceD 372 32 0 =
      chainId.toBytes := by
  calc
    (weth10Code ⟨chainId, domainSeparator⟩).sliceD 372 32 0 =
        chainId.toBytes.sliceD 0 32 0 := by
      rw [List.sliceD_eq_map, List.sliceD_eq_map]
      apply List.map_congr_left
      intro j hj
      have hj' : j < 32 := List.mem_range.mp hj
      simpa using weth10Code_getD_chainWord
        (⟨chainId, domainSeparator⟩ : DeployParams) j hj'
    _ = chainId.toBytes := by
      unfold List.sliceD
      simp only [List.drop_zero]
      rw [List.takeD_eq_take 0 (by
        rw [B256.length_toBytes])]
      simpa only [B256.length_toBytes] using
        (List.take_length (l := chainId.toBytes))

private theorem weth10Code_getD_deploymentChainWord
    (dp : DeployParams) (j : Nat) (hj : j < 32) :
    (weth10Code dp).getD (691 + j) 0 =
      dp.deploymentChainId.toBytes.getD j 0 := by
  rw [weth10CodeGetD_to_dispatch dp (691 + j) (by omega) (by
    have hdispatch :
        (dispatchWith fallbackSlot
          (weth10Tree
            (⟨0, 0⟩ : DeployParams))).compileShape.byteSize = 3939 := by
      exact fullDispatch_size
    omega)]
  have hi : 691 + j - 12 = 679 + j := by omega
  rw [hi]
  exact weth10DispatchByteAt_deploymentChainWord
    weth10RuntimeLocations 12 dp j hj

private theorem weth10Code_slice_691_723
    (chainId domainSeparator : B256) :
    (weth10Code ⟨chainId, domainSeparator⟩).sliceD 691 32 0 =
      chainId.toBytes := by
  calc
    (weth10Code ⟨chainId, domainSeparator⟩).sliceD 691 32 0 =
        chainId.toBytes.sliceD 0 32 0 := by
      rw [List.sliceD_eq_map, List.sliceD_eq_map]
      apply List.map_congr_left
      intro j hj
      have hj' : j < 32 := List.mem_range.mp hj
      simpa using weth10Code_getD_deploymentChainWord
        (⟨chainId, domainSeparator⟩ : DeployParams) j hj'
    _ = chainId.toBytes := by
      unfold List.sliceD
      simp only [List.drop_zero]
      rw [List.takeD_eq_take 0 (by
        rw [B256.length_toBytes])]
      simpa only [B256.length_toBytes] using
        (List.take_length (l := chainId.toBytes))

private theorem weth10Code_slice_0_372
    (chainId domainSeparator : B256) :
    (weth10Code ⟨chainId, domainSeparator⟩).sliceD 0 372 0 =
      weth10RuntimeTemplate.take 372 := by
  unfold List.sliceD
  simp only [List.drop_zero]
  rw [List.takeD_eq_take _ (by
    rw [weth10Code_length]
    omega)]
  have hdp := weth10Code_eq_emitByShape ⟨chainId, domainSeparator⟩
  have hzero : weth10RuntimeTemplate =
      Prog.emitByShape (weth10 ⟨0, 0⟩).compileShape (weth10 ⟨0, 0⟩) :=
    weth10RuntimeTemplate_eq_code.trans (weth10Code_eq_emitByShape ⟨0, 0⟩)
  rw [hdp, hzero]
  rw [weth10_compileShape_eq_zero ⟨chainId, domainSeparator⟩]
  simp only [Prog.emitByShape, Prog.compileShape, Table.emitByShape,
    Func.CompileShape.locations, weth10]
  rw [List.take_append_of_le_length (by
    simp only [List.length_cons, Func.length_emitByShape]
    have hmain := weth10ZeroMain_size_lower
    omega)]
  rw [List.take_append_of_le_length (by
    simp only [List.length_cons, Func.length_emitByShape]
    have hmain := weth10ZeroMain_size_lower
    omega)]
  simp only [List.take, List.cons.injEq, true_and]
  exact weth10MainEmitTake_eq_zero_371 _ _ chainId domainSeparator

private theorem emitByShape_next_drop_rest
    (locations : List Nat) (n size : Nat)
    (restShape : Func.CompileShape)
    (inst : Ninst) (rest : Func) :
    (Func.emitByShape locations n (.next size restShape)
      (.next inst rest)).drop size =
      Func.emitByShape locations (n + size) restShape rest := by
  conv_lhs => rw [Func.emitByShape]
  have hlen :
      (List.takeD size (Ninst.toBytes inst) 0).length = size :=
    List.takeD_length size _ _
  simpa only [hlen] using
    (List.drop_left
      (l₁ := List.takeD size (Ninst.toBytes inst) 0)
      (l₂ := Func.emitByShape locations (n + size) restShape rest))

private theorem emitByShape_branch_drop_right
    (locations : List Nat) (n : Nat)
    (leftShape rightShape : Func.CompileShape)
    (left right : Func) :
    (Func.emitByShape locations n (.branch leftShape rightShape)
      (.branch left right)).drop (4 + leftShape.byteSize) =
      Jinst.jumpdest.toUInt8 ::
        Func.emitByShape locations
          (n + leftShape.byteSize + 4 + 1) rightShape right := by
  let header : Bytes :=
    [0x61, ((n + leftShape.byteSize + 4) >>> 8).toUInt8,
      (n + leftShape.byteSize + 4).toUInt8, Jinst.jumpi.toUInt8]
  let leftBytes :=
    Func.emitByShape locations (n + 4) leftShape left
  let rightBytes :=
    Func.emitByShape locations
      (n + leftShape.byteSize + 4 + 1) rightShape right
  conv_lhs => rw [Func.emitByShape]
  change
    ((((header ++ leftBytes) ++ [Jinst.jumpdest.toUInt8]) ++ rightBytes)).drop
        (4 + leftShape.byteSize) =
      Jinst.jumpdest.toUInt8 :: rightBytes
  rw [List.append_assoc (header ++ leftBytes)]
  have hheader : header.length = 4 := by simp [header]
  have hleft : leftBytes.length = leftShape.byteSize := by
    simp [leftBytes, Func.length_emitByShape]
  have hlen : (header ++ leftBytes).length = 4 + leftShape.byteSize := by
    simp [hheader, hleft]
  rw [← hlen, List.drop_left]
  rfl

private theorem weth10MainEmit_drop_3950
    (locations : List Nat) (n : Nat) (dp : DeployParams) :
    (Func.emitByShape locations n
      (weth10Main (⟨0, 0⟩ : DeployParams)).compileShape
      (weth10Main dp)).drop 3950 =
    (Func.emitByShape locations n
      (weth10Main (⟨0, 0⟩ : DeployParams)).compileShape
      (weth10Main (⟨0, 0⟩ : DeployParams))).drop 3950 := by
  have hcd : Ninst.calldatasize.size = 1 := by decide +kernel
  have hiz : Ninst.iszero.size = 1 := by decide +kernel
  have hleft :
      (fsig +++ dispatchWith fallbackSlot
        (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape.byteSize =
        3944 := by
    exact fsigFullDispatch_size
  have htail (q : DeployParams) :
      (Func.emitByShape locations n
        (weth10Main (⟨0, 0⟩ : DeployParams)).compileShape
        (weth10Main q)).drop 3950 =
      Jinst.jumpdest.toUInt8 ::
        Func.emitByShape locations (n + 3951)
          receiveEther.compileShape receiveEther := by
    change
      (Func.emitByShape locations n
        (.next Ninst.calldatasize.size
          (.next Ninst.iszero.size
            (.branch
              (fsig +++ dispatchWith fallbackSlot
                (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
              receiveEther.compileShape)))
        (Ninst.calldatasize ::: Ninst.iszero :::
          Func.branch
            (fsig +++ dispatchWith fallbackSlot (weth10Tree q))
            receiveEther)).drop 3950 = _
    simp only [hcd, hiz]
    rw [show 3950 = 1 + 3949 by omega, ← List.drop_drop]
    rw [emitByShape_next_drop_rest]
    rw [show 3949 = 1 + 3948 by omega, ← List.drop_drop]
    rw [emitByShape_next_drop_rest]
    rw [show 3948 = 4 + (fsig +++ dispatchWith fallbackSlot
      (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape.byteSize by omega]
    rw [emitByShape_branch_drop_right]
    simp only [hleft]
  exact (htail dp).trans (htail (⟨0, 0⟩ : DeployParams)).symm

private theorem weth10Code_drop_3951 (dp : DeployParams) :
    (weth10Code dp).drop 3951 = weth10RuntimeTemplate.drop 3951 := by
  rw [weth10RuntimeTemplate_eq_code]
  rw [weth10Code_eq_emitByZeroShape,
    weth10Code_eq_emitByZeroShape]
  let zeroMainShape :=
    (weth10Main (⟨0, 0⟩ : DeployParams)).compileShape
  let zeroAuxShapes := weth10Aux.map Func.compileShape
  let shapes := zeroMainShape :: zeroAuxShapes
  let locations := Func.CompileShape.locations 0 shapes
  let auxBytes :=
    Table.emitByShape locations
      (Func.CompileShape.locations
        (zeroMainShape.byteSize + 1) zeroAuxShapes)
      zeroAuxShapes weth10Aux
  have htail (q : DeployParams) :
      (Prog.emitByShape
        (weth10 (⟨0, 0⟩ : DeployParams)).compileShape
        (weth10 q)).drop 3951 =
      (Func.emitByShape locations 1 zeroMainShape
        (weth10Main q)).drop 3950 ++ auxBytes := by
    change
      (Table.emitByShape locations locations shapes
        (weth10Main q :: weth10Aux)).drop 3951 = _
    unfold locations shapes
    rw [Func.CompileShape.locations, Table.emitByShape]
    rw [List.drop_append_of_le_length]
    · rw [show 3951 = 3950 + 1 by omega, List.drop_succ_cons]
      unfold auxBytes locations shapes
      rw [Func.CompileShape.locations]
      simp only [Nat.zero_add]
    · simp only [List.length_cons, Func.length_emitByShape]
      have hmain : 3950 ≤ zeroMainShape.byteSize := by
        simpa [zeroMainShape] using weth10ZeroMain_size_lower
      omega
  calc
    (Prog.emitByShape
      (weth10 (⟨0, 0⟩ : DeployParams)).compileShape
      (weth10 dp)).drop 3951 =
        (Func.emitByShape locations 1 zeroMainShape
          (weth10Main dp)).drop 3950 ++ auxBytes :=
      htail dp
    _ = (Func.emitByShape locations 1 zeroMainShape
          (weth10Main (⟨0, 0⟩ : DeployParams))).drop 3950 ++ auxBytes := by
      rw [weth10MainEmit_drop_3950]
    _ = (Prog.emitByShape
      (weth10 (⟨0, 0⟩ : DeployParams)).compileShape
      (weth10 (⟨0, 0⟩ : DeployParams))).drop 3951 :=
      (htail (⟨0, 0⟩ : DeployParams)).symm

private theorem weth10Code_slice_404_536
    (chainId domainSeparator : B256) :
    (weth10Code ⟨chainId, domainSeparator⟩).sliceD 404 132 0 =
      (weth10RuntimeTemplate.drop 404).take 132 := by
  apply Bytes.sliceD_eq_drop_take_of_getD_eq
  · rw [weth10RuntimeTemplate_length]
    omega
  · intro j hj
    apply weth10CodeGetD_eq_zero_of_dispatch
    · omega
    · have hdispatch :
          (dispatchWith fallbackSlot
            (weth10Tree
              (⟨0, 0⟩ : DeployParams))).compileShape.byteSize = 3939 := by
        exact fullDispatch_size
      rw [hdispatch]
      omega
    · have hindex : 404 + j - 12 = 392 + j := by omega
      rw [hindex]
      exact weth10DispatchByteAt_eq_zero_392_524
        weth10RuntimeLocations 12
        (⟨chainId, domainSeparator⟩ : DeployParams) (392 + j)
        (by omega) (by omega)

private theorem weth10Code_getD_cachedWord_536
    (dp : DeployParams) (j : Nat) (hj : j < 32) :
    (weth10Code dp).getD (536 + j) 0 =
      dp.cachedDomainSeparator.toBytes.getD j 0 := by
  rw [weth10CodeGetD_to_dispatch dp (536 + j) (by omega) (by
    have hdispatch :
        (dispatchWith fallbackSlot
          (weth10Tree
            (⟨0, 0⟩ : DeployParams))).compileShape.byteSize = 3939 := by
      exact fullDispatch_size
    rw [hdispatch]
    omega)]
  have hi : 536 + j - 12 = 524 + j := by omega
  rw [hi]
  exact weth10DispatchByteAt_cachedWord
    weth10RuntimeLocations 12 dp j hj

private theorem weth10Code_slice_536_568
    (chainId domainSeparator : B256) :
    (weth10Code ⟨chainId, domainSeparator⟩).sliceD 536 32 0 =
      domainSeparator.toBytes := by
  calc
    (weth10Code ⟨chainId, domainSeparator⟩).sliceD 536 32 0 =
        domainSeparator.toBytes.sliceD 0 32 0 := by
      rw [List.sliceD_eq_map, List.sliceD_eq_map]
      apply List.map_congr_left
      intro j hj
      have hj' : j < 32 := List.mem_range.mp hj
      simpa using weth10Code_getD_cachedWord_536
        (⟨chainId, domainSeparator⟩ : DeployParams) j hj'
    _ = domainSeparator.toBytes := by
      unfold List.sliceD
      simp only [List.drop_zero]
      rw [List.takeD_eq_take 0 (by rw [B256.length_toBytes])]
      simpa only [B256.length_toBytes] using
        (List.take_length (l := domainSeparator.toBytes))

private theorem weth10Code_slice_568_691
    (chainId domainSeparator : B256) :
    (weth10Code ⟨chainId, domainSeparator⟩).sliceD 568 123 0 =
      (weth10RuntimeTemplate.drop 568).take 123 := by
  apply Bytes.sliceD_eq_drop_take_of_getD_eq
  · rw [weth10RuntimeTemplate_length]
    omega
  · intro j hj
    apply weth10CodeGetD_eq_zero_of_dispatch
    · omega
    · have hdispatch :
          (dispatchWith fallbackSlot
            (weth10Tree
              (⟨0, 0⟩ : DeployParams))).compileShape.byteSize = 3939 := by
        exact fullDispatch_size
      rw [hdispatch]
      omega
    · have hindex : 568 + j - 12 = 556 + j := by omega
      rw [hindex]
      exact weth10DispatchByteAt_eq_zero_556_679
        weth10RuntimeLocations 12
        (⟨chainId, domainSeparator⟩ : DeployParams) (556 + j)
        (by omega) (by omega)

private theorem weth10Code_slice_723_2875
    (chainId domainSeparator : B256) :
    (weth10Code ⟨chainId, domainSeparator⟩).sliceD 723 2152 0 =
      (weth10RuntimeTemplate.drop 723).take 2152 := by
  apply Bytes.sliceD_eq_drop_take_of_getD_eq
  · rw [weth10RuntimeTemplate_length]
    omega
  · intro j hj
    apply weth10CodeGetD_eq_zero_of_dispatch
    · omega
    · have hdispatch :
          (dispatchWith fallbackSlot
            (weth10Tree
              (⟨0, 0⟩ : DeployParams))).compileShape.byteSize = 3939 := by
        exact fullDispatch_size
      rw [hdispatch]
      omega
    · have hindex : 723 + j - 12 = 711 + j := by omega
      rw [hindex]
      by_cases hhigh : 711 + j < 1780
      · exact weth10DispatchByteAt_eq_zero_711_1780
          weth10RuntimeLocations 12
          (⟨chainId, domainSeparator⟩ : DeployParams) (711 + j)
          (by omega) hhigh
      · by_cases hjump : 711 + j = 1780
        · rw [hjump]
          exact weth10DispatchByteAt_eq_zero_1780
            weth10RuntimeLocations 12
            (⟨chainId, domainSeparator⟩ : DeployParams)
        · exact fullDispatchByteAt_eq_zero_1781_2863
            weth10RuntimeLocations 12
            (⟨chainId, domainSeparator⟩ : DeployParams) (711 + j)
            (by omega) (by omega)

private theorem weth10Code_getD_chainWord_2875
    (dp : DeployParams) (j : Nat) (hj : j < 32) :
    (weth10Code dp).getD (2875 + j) 0 =
      dp.deploymentChainId.toBytes.getD j 0 := by
  rw [weth10CodeGetD_to_dispatch dp (2875 + j) (by omega) (by
    have hdispatch :
        (dispatchWith fallbackSlot
          (weth10Tree
            (⟨0, 0⟩ : DeployParams))).compileShape.byteSize = 3939 := by
      exact fullDispatch_size
    rw [hdispatch]
    omega)]
  have hindex : 2875 + j - 12 = 2863 + j := by omega
  rw [hindex]
  have hword := fullDispatchByteAt_deploymentWord_2863_2895
    weth10RuntimeLocations 12 dp (2863 + j) (by omega) (by omega)
  have hout : 2863 + j - 2863 = j := by omega
  rw [hout] at hword
  exact hword

private theorem weth10Code_slice_2875_2907
    (chainId domainSeparator : B256) :
    (weth10Code ⟨chainId, domainSeparator⟩).sliceD 2875 32 0 =
      chainId.toBytes := by
  calc
    (weth10Code ⟨chainId, domainSeparator⟩).sliceD 2875 32 0 =
        chainId.toBytes.sliceD 0 32 0 := by
      rw [List.sliceD_eq_map, List.sliceD_eq_map]
      apply List.map_congr_left
      intro j hj
      have hj' : j < 32 := List.mem_range.mp hj
      simpa using weth10Code_getD_chainWord_2875
        (⟨chainId, domainSeparator⟩ : DeployParams) j hj'
    _ = chainId.toBytes := by
      unfold List.sliceD
      simp only [List.drop_zero]
      rw [List.takeD_eq_take 0 (by rw [B256.length_toBytes])]
      simpa only [B256.length_toBytes] using
        (List.take_length (l := chainId.toBytes))

private theorem weth10Code_slice_2907_3039
    (chainId domainSeparator : B256) :
    (weth10Code ⟨chainId, domainSeparator⟩).sliceD 2907 132 0 =
      (weth10RuntimeTemplate.drop 2907).take 132 := by
  apply Bytes.sliceD_eq_drop_take_of_getD_eq
  · rw [weth10RuntimeTemplate_length]
    omega
  · intro j hj
    apply weth10CodeGetD_eq_zero_of_dispatch
    · omega
    · have hdispatch :
          (dispatchWith fallbackSlot
            (weth10Tree
              (⟨0, 0⟩ : DeployParams))).compileShape.byteSize = 3939 := by
        exact fullDispatch_size
      rw [hdispatch]
      omega
    · have hindex : 2907 + j - 12 = 2895 + j := by omega
      rw [hindex]
      exact fullDispatchByteAt_eq_zero_2895_3027
        weth10RuntimeLocations 12
        (⟨chainId, domainSeparator⟩ : DeployParams) (2895 + j)
        (by omega) (by omega)

private theorem weth10Code_getD_cachedWord_3039
    (dp : DeployParams) (j : Nat) (hj : j < 32) :
    (weth10Code dp).getD (3039 + j) 0 =
      dp.cachedDomainSeparator.toBytes.getD j 0 := by
  rw [weth10CodeGetD_to_dispatch dp (3039 + j) (by omega) (by
    have hdispatch :
        (dispatchWith fallbackSlot
          (weth10Tree
            (⟨0, 0⟩ : DeployParams))).compileShape.byteSize = 3939 := by
      exact fullDispatch_size
    rw [hdispatch]
    omega)]
  have hindex : 3039 + j - 12 = 3027 + j := by omega
  rw [hindex]
  have hword := fullDispatchByteAt_cachedWord_3027_3059
    weth10RuntimeLocations 12 dp (3027 + j) (by omega) (by omega)
  have hout : 3027 + j - 3027 = j := by omega
  rw [hout] at hword
  exact hword

private theorem weth10Code_slice_3039_3071
    (chainId domainSeparator : B256) :
    (weth10Code ⟨chainId, domainSeparator⟩).sliceD 3039 32 0 =
      domainSeparator.toBytes := by
  calc
    (weth10Code ⟨chainId, domainSeparator⟩).sliceD 3039 32 0 =
        domainSeparator.toBytes.sliceD 0 32 0 := by
      rw [List.sliceD_eq_map, List.sliceD_eq_map]
      apply List.map_congr_left
      intro j hj
      have hj' : j < 32 := List.mem_range.mp hj
      simpa using weth10Code_getD_cachedWord_3039
        (⟨chainId, domainSeparator⟩ : DeployParams) j hj'
    _ = domainSeparator.toBytes := by
      unfold List.sliceD
      simp only [List.drop_zero]
      rw [List.takeD_eq_take 0 (by rw [B256.length_toBytes])]
      simpa only [B256.length_toBytes] using
        (List.take_length (l := domainSeparator.toBytes))

private theorem weth10Code_slice_3071_6313
    (chainId domainSeparator : B256) :
    (weth10Code ⟨chainId, domainSeparator⟩).sliceD 3071 3242 0 =
      weth10RuntimeTemplate.drop 3071 := by
  let dp : DeployParams := ⟨chainId, domainSeparator⟩
  have hprefix :
      ((weth10Code dp).drop 3071).take 880 =
        (weth10RuntimeTemplate.drop 3071).take 880 := by
    apply Bytes.take_eq_take_of_getD_eq (d := 0)
    · rw [List.length_drop, weth10Code_length]
      omega
    · rw [List.length_drop, weth10RuntimeTemplate_length]
      omega
    · intro j hj
      rw [List.getD_drop, List.getD_drop]
      apply weth10CodeGetD_eq_zero_of_dispatch
      · omega
      · have hdispatch :
            (dispatchWith fallbackSlot
              (weth10Tree
                (⟨0, 0⟩ : DeployParams))).compileShape.byteSize = 3939 := by
          exact fullDispatch_size
        rw [hdispatch]
        omega
      · have hindex : 3071 + j - 12 = 3059 + j := by omega
        rw [hindex]
        exact fullDispatchByteAt_eq_zero_3059_3939
          weth10RuntimeLocations 12 dp (3059 + j)
          (by omega) (by omega)
  have hdecomp (bs : Bytes) :
      bs.drop 3071 = (bs.drop 3071).take 880 ++ bs.drop 3951 := by
    calc
      bs.drop 3071 =
          (bs.drop 3071).take 880 ++ (bs.drop 3071).drop 880 :=
        (List.take_append_drop 880 (bs.drop 3071)).symm
      _ = (bs.drop 3071).take 880 ++ bs.drop 3951 := by
        rw [List.drop_drop]
  have hdrop :
      (weth10Code dp).drop 3071 = weth10RuntimeTemplate.drop 3071 := by
    calc
      (weth10Code dp).drop 3071 =
          ((weth10Code dp).drop 3071).take 880 ++
            (weth10Code dp).drop 3951 :=
        hdecomp (weth10Code dp)
      _ = (weth10RuntimeTemplate.drop 3071).take 880 ++
            weth10RuntimeTemplate.drop 3951 := by
        rw [hprefix, weth10Code_drop_3951]
      _ = weth10RuntimeTemplate.drop 3071 :=
        (hdecomp weth10RuntimeTemplate).symm
  unfold List.sliceD
  rw [List.takeD_eq_take _ (by
    simp only [List.length_drop]
    rw [weth10Code_length])]
  rw [hdrop]
  have hlen : (weth10RuntimeTemplate.drop 3071).length = 3242 := by
    rw [List.length_drop, weth10RuntimeTemplate_length]
  rw [← hlen, List.take_length]

private theorem weth10Code_eq_runtimeSegments
    (chainId domainSeparator : B256) :
    weth10Code ⟨chainId, domainSeparator⟩ =
      runtimeSegments chainId domainSeparator := by
  rw [← runtimeSlices_eq (weth10Code ⟨chainId, domainSeparator⟩)
    (weth10Code_length ⟨chainId, domainSeparator⟩)]
  unfold runtimeSlices runtimeSegments
  rw [weth10Code_slice_0_372, weth10Code_slice_372_404,
    weth10Code_slice_404_536, weth10Code_slice_536_568,
    weth10Code_slice_568_691, weth10Code_slice_691_723,
    weth10Code_slice_723_2875, weth10Code_slice_2875_2907,
    weth10Code_slice_2907_3039, weth10Code_slice_3039_3071,
    weth10Code_slice_3071_6313]

/-- Patching the zero-parameter template at all generated word spans yields
exactly the corresponding member of the universally compiled runtime family. -/
theorem weth10PatchedRuntime_eq_code (chainId domainSeparator : B256) :
    weth10PatchedRuntime chainId domainSeparator =
      weth10Code ⟨chainId, domainSeparator⟩ :=
  (weth10PatchedRuntime_eq_segments chainId domainSeparator).trans
    (weth10Code_eq_runtimeSegments chainId domainSeparator).symm

/-- The fixed-width constructor prefix is 177 bytes. -/
theorem weth10InitPrefix_length : weth10InitPrefix.length = 177 := by
  unfold weth10InitPrefix
  rw [weth10RuntimeTemplate_length]
  simp [deploymentPrefix, patchChainWords, patchStackWord, initPush2, initPush32,
    align32, deploymentChainIdWordOffsets, cachedDomainSeparatorWordOffsets,
    B256.length_toBytes]

/-- The complete generic creation bytecode is 6,490 bytes. -/
theorem weth10InitCode_length : weth10InitCode.length = 6490 := by
  rw [weth10InitCode_length_add, weth10InitPrefix_length,
    weth10RuntimeTemplate_length]

/-! ## Constructor program connection

The creation prefix is hand-emitted only because its successful path copies a
6,313-byte data tail which is not itself Blanc constructor code.  The prefix
instructions nevertheless have an exact Blanc `Func` presentation.  Keeping
that presentation here lets the semantic proof use Blanc's compiled-program
bridge while treating the appended runtime template as ordinary CODECOPY data.
-/

private abbrev initPush2Inst (n : Nat) : Ninst :=
  .push [(n >>> 8).toUInt8, n.toUInt8] (by simp)

private abbrev initPush32Inst (w : B256) : Ninst :=
  .push w.toBytes (by rw [B256.length_toBytes])

/-- Copy the appended zero-parameter runtime template into memory. -/
def weth10InitCopyLine (runtimeLength codeOffset : Nat) : Line :=
  [initPush2Inst runtimeLength, initPush2Inst codeOffset,
    Ninst.pushB256 0, Ninst.codecopy]

/-- Patch the three deployment-chain words in the copied runtime. -/
def weth10InitChainLine : Line :=
  deploymentChainIdWordOffsets.flatMap fun off =>
    [Ninst.chainid, initPush2Inst off, Ninst.mstore]

/-- Write the five-word EIP-712 deployment preimage above the returned runtime
window. -/
def weth10InitPreHashLine (runtimeLength : Nat) : Line :=
  let scratch := align32 runtimeLength
  [initPush32Inst DOMAIN_TYPEHASH, initPush2Inst scratch, Ninst.mstore,
   initPush32Inst NAME_HASH, initPush2Inst (scratch + 32), Ninst.mstore,
   initPush32Inst VERSION_HASH, initPush2Inst (scratch + 64), Ninst.mstore,
   Ninst.chainid, initPush2Inst (scratch + 96), Ninst.mstore,
   Ninst.address, initPush2Inst (scratch + 128), Ninst.mstore]

/-- Hash the completed deployment preimage. -/
def weth10InitHashLine (runtimeLength : Nat) : Line :=
  let scratch := align32 runtimeLength
  [initPush2Inst 160, initPush2Inst scratch, Ninst.kec]

/-- Patch the two cached-domain-separator words and discard the retained hash. -/
def weth10InitSeparatorLine : Line :=
  cachedDomainSeparatorWordOffsets.flatMap
      (fun off => [Ninst.dup 0, initPush2Inst off, Ninst.mstore]) ++
    [Ninst.pop]

/-- Place the successful constructor's return window on the stack. -/
def weth10InitReturnLine (runtimeLength : Nat) : Line :=
  [initPush2Inst runtimeLength, Ninst.pushB256 0]

private def deploymentSuccessLine
    (runtimeLength codeOffset : Nat) : Line :=
  weth10InitCopyLine runtimeLength codeOffset ++
    weth10InitChainLine ++
    weth10InitPreHashLine runtimeLength ++
    weth10InitHashLine runtimeLength ++
    weth10InitSeparatorLine ++
    weth10InitReturnLine runtimeLength

/-- The successful constructor arm, factored into independently provable
straight-line phases followed by `RETURN`. -/
def weth10InitSuccess
    (runtimeLength codeOffset : Nat) : Func :=
  deploymentSuccessLine runtimeLength codeOffset +++ Func.ret

/-- The Blanc constructor's successful arm exposed as its six independently
checkable straight-line phases. -/
theorem weth10InitSuccess_eq_phases :
    weth10InitSuccess 6313 177 =
      weth10InitCopyLine 6313 177 +++
        (weth10InitChainLine +++
          (weth10InitPreHashLine 6313 +++
            (weth10InitHashLine 6313 +++
              (weth10InitSeparatorLine +++
                (weth10InitReturnLine 6313 +++ Func.ret))))) := by
  rfl

/-- The exact Blanc presentation of the hand-emitted constructor prefix. -/
def weth10InitFunc : Func :=
  Ninst.callvalue ::: Ninst.iszero :::
    (weth10InitSuccess 6313 177 <?>
      Func.rev)

private def lineByteSize (xs : Line) : Nat :=
  (xs.map Ninst.size).sum

private lemma Func.compile_prepend_of {entries : List (Nat × Func)}
    {n : Nat} {xs : Line} {f : Func} {bs : Bytes}
    (h : Func.compile entries (n + lineByteSize xs) f = some bs) :
    Func.compile entries n (xs +++ f) =
      some (xs.flatMap Ninst.toBytes ++ bs) := by
  induction xs generalizing n with
  | nil =>
      change Func.compile entries n f = some bs
      change Func.compile entries (n + 0) f = some bs at h
      simpa only [Nat.add_zero] using h
  | cons i is ih =>
      change Func.compile entries
        (n + (i.size + lineByteSize is)) f = some bs at h
      simp only [prepend, Func.compile]
      rw [ih (n := n + i.size) (by
        simpa only [Nat.add_assoc] using h)]
      simp only [bind, Option.bind, pure, List.flatMap_cons,
        List.append_assoc]

private lemma deploymentSuccess_compile
    (entries : List (Nat × Func)) (n : Nat) :
    Func.compile entries n (weth10InitSuccess 6313 177) =
      some ((deploymentSuccessLine 6313 177).flatMap Ninst.toBytes ++
        [Linst.toUInt8 .ret]) := by
  unfold weth10InitSuccess
  apply Func.compile_prepend_of
  rfl

private lemma deploymentReject_compile
    (entries : List (Nat × Func)) (n : Nat) :
    Func.compile entries n Func.rev = some [0x5f, 0x5f, 0xfd] := by
  rfl

private lemma deploymentBranch_compile (entries : List (Nat × Func)) :
    Func.compile entries 2
        (weth10InitSuccess 6313 177 <?> Func.rev) =
      some ([0x61, 0, 9, 0x57, 0x5f, 0x5f, 0xfd, 0x5b] ++
        (deploymentSuccessLine 6313 177).flatMap Ninst.toBytes ++
        [Linst.toUInt8 .ret]) := by
  change Func.compile entries 2
    (Func.branch Func.rev (weth10InitSuccess 6313 177)) = _
  simp only [Func.compile]
  rw [deploymentReject_compile entries 6]
  simp only [bind, Option.bind, pure, List.length_cons, List.length_nil,
    Nat.reduceAdd, guard]
  rw [deploymentSuccess_compile entries 10]
  rfl

/-- Compiling the Blanc constructor presentation yields exactly the committed
177-byte init prefix.  The runtime template remains the data suffix of
`weth10InitCode`; no bytecode identity is assumed here. -/
theorem weth10InitFunc_compile :
    Func.compile (table 0 [weth10InitFunc]) 0 weth10InitFunc =
      some weth10InitPrefix := by
  unfold weth10InitFunc
  change Func.compile
    (table 0
      [Ninst.callvalue ::: Ninst.iszero :::
        (weth10InitSuccess 6313 177 <?> Func.rev)])
    0
    ([Ninst.callvalue, Ninst.iszero] +++
      (weth10InitSuccess 6313 177 <?> Func.rev)) = some weth10InitPrefix
  rw [Func.compile_prepend_of
    (xs := [Ninst.callvalue, Ninst.iszero])
    (f := weth10InitSuccess 6313 177 <?> Func.rev)
    (deploymentBranch_compile _)]
  have hprefix : weth10InitPrefix = deploymentPrefix 6313 177 := by
    unfold weth10InitPrefix
    rw [weth10RuntimeTemplate_length]
    rfl
  rw [hprefix]
  rfl

/-- The constructor prefix contains no Blanc table calls, so its successful
walk depends only on the compiled prefix and may safely ignore the appended
runtime-data suffix. -/
theorem weth10InitFunc_noCalls : weth10InitFunc.NoCalls := by
  change Func.rev.NoCalls ∧ (weth10InitSuccess 6313 177).NoCalls
  constructor
  · simp [Func.rev, Func.NoCalls]
  · unfold weth10InitSuccess
    exact Func.NoCalls.prepend _ (by simp [Func.ret, Func.NoCalls])

end Weth10

end Blanc
