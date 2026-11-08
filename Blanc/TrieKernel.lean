import Jaune.RlpEval
import Jaune.Machine

/-!
# Kernel-evaluable Merkle–Patricia trie roots

Jaune's `trie` does not reduce in the kernel: `BLT.toBytes` is well-founded recursion over a
nested inductive and gets stuck inside `nodeComp`/`structComp` and `trie`'s outer encode. This
module is a verbatim twin with Jaune's structural `BLT.toBytesS` (`Jaune/RlpEval.lean`) in its
place (`trieS`, `trie_eq_trieS`), then the same twin with Keccak abstracted to a parameter `H`
(`trieH`, `trie_eq_trieH`).

A node-hash certificate keeps each kernel check small. `cached cert` looks a preimage up in a list
of `(preimage, digest)` pairs and falls back to real Keccak; when every pair is a separately
checked Keccak equation, `cached cert = Bytes.keccak` (`cached_eq`), so
`trie j = trieH (cached cert) j` (`trie_eq_cached`) and the root check evaluates no Keccak at all.
Route: one `theorem kᵢ : Bytes.keccak pᵢ = hᵢ := by decide +kernel` per node, chunked into modules
of at most about 24 KB of preimages, then `rw [trie_eq_cached cert hc]; decide +kernel`.

- Probe: `Blanc/Probe/N100K*.lean` and `TrieTwin.lean` in the disposable `weth9-binding-probe`
  worktree (commit `ae402337`, 100 entries of 1024 bytes, 107 certificate nodes, 5 chunks).
- Measured cost: kernel Keccak about 1.7–2.0 s and 0.33–0.4 GB RSS per KB of preimage within one
  declaration, released per declaration; 24 KB chunks about 41 s; N100K 231 s wall, 6.5 GB peak (WSL).
- Simplest alternative tried: `rw [trie_eq_trieS]; decide +kernel` with no certificate passes at
  16 × 40 B (5 s) but N100 (100 × 300 B) was retracted at 15.7 GB.
- Date: 2026-11-02
-/

namespace Blanc.TrieKernel
open Jaune

mutual

  def nodeCompS : Nat → NTB → BLT
    | 0, _ => .bytes []
    | k + 1, j =>
      if j.isEmpty
      then .bytes []
      else let r := structCompS k j
           if (BLT.toBytesS r).length < 32
           then r
           else .bytes <| (BLT.toBytesS r).keccak.toBytes

  def structCompS : Nat → NTB → BLT
    | 0, _ => .bytes []
    | k + 1, j =>
      if j.isEmpty
            then .bytes []       else if j.isSingleton
           then match j.toList with
                | [(k, v)] => .list [.bytes (hp k 1), .bytes v]
                | _ => .bytes []            else match j.factor with
                | none =>
                  let js := Std.TreeMap.foldl NTBs.insert NTBs.empty j
                  .list [ nodeCompS k js.x0, nodeCompS k js.x1, nodeCompS k js.x2,
                          nodeCompS k js.x3, nodeCompS k js.x4, nodeCompS k js.x5,
                          nodeCompS k js.x6, nodeCompS k js.x7, nodeCompS k js.x8,
                          nodeCompS k js.x9, nodeCompS k js.xA, nodeCompS k js.xB,
                          nodeCompS k js.xC, nodeCompS k js.xD, nodeCompS k js.xE,
                          nodeCompS k js.xF, .bytes (j.getD [] []) ]
                | some (pfx, j') => .list [.bytes (hp pfx 0), nodeCompS k j']

end

/-! ### Hash-parametric twin and a hash certificate

`trieH H` is `trieS` with `Bytes.keccak` abstracted to `H`. Instantiated at
`cached cert`, where every pair of `cert` is a separately kernel-checked keccak,
the kernel looks node hashes up instead of recomputing them, so one declaration
never evaluates more than one keccak. -/

mutual

  def nodeCompH (H : Bytes → B256) : Nat → NTB → BLT
    | 0, _ => .bytes []
    | k + 1, j =>
      if j.isEmpty
      then .bytes []
      else let r := structCompH H k j
           if (BLT.toBytesS r).length < 32
           then r
           else .bytes <| (H (BLT.toBytesS r)).toBytes

  def structCompH (H : Bytes → B256) : Nat → NTB → BLT
    | 0, _ => .bytes []
    | k + 1, j =>
      if j.isEmpty
            then .bytes []       else if j.isSingleton
           then match j.toList with
                | [(k, v)] => .list [.bytes (hp k 1), .bytes v]
                | _ => .bytes []            else match j.factor with
                | none =>
                  let js := Std.TreeMap.foldl NTBs.insert NTBs.empty j
                  .list [ nodeCompH H k js.x0, nodeCompH H k js.x1, nodeCompH H k js.x2,
                          nodeCompH H k js.x3, nodeCompH H k js.x4, nodeCompH H k js.x5,
                          nodeCompH H k js.x6, nodeCompH H k js.x7, nodeCompH H k js.x8,
                          nodeCompH H k js.x9, nodeCompH H k js.xA, nodeCompH H k js.xB,
                          nodeCompH H k js.xC, nodeCompH H k js.xD, nodeCompH H k js.xE,
                          nodeCompH H k js.xF, .bytes (j.getD [] []) ]
                | some (pfx, j') => .list [.bytes (hp pfx 0), nodeCompH H k j']

end

end Blanc.TrieKernel
