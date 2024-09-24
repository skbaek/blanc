-- Deployer.lean : Makeshift solution for deploying bytecode compiled from Blanc programs

import Blanc.Weth



def Bytes.toList (bs : Bytes) : List Byte := go bs [] where
  go : Bytes → List Byte → List Byte
  | ⟪⟫, l => l
  | bs' :> b, l => go bs' (b :: l)

def List.toBytes (l : List Byte) : Bytes := go ⟪⟫ l where
  go : Bytes → List Byte → Bytes
  | xs, [] => xs
  | xs, y :: ys => go (xs :> y) ys

lemma List.length_toBytes {ys : List Byte} : ys.toBytes.length = ys.length := by
  have h :
      ∀ {xs : Bytes}, (List.toBytes.go xs ys).length = xs.length + ys.length := by
    induction ys with
    | nil => intro xs; rfl
    | cons y ys ih =>
      intro xs; simp only [List.toBytes.go]
      rw [ih]; simp [Bytes.length, List.length]
      rw [Nat.add_comm ys.length 1, Nat.add_assoc]
  have h' := @h ⟪⟫
  simp [Bytes.length] at h'; exact h'

partial def List.break : List Byte → List {ys : Bytes // ys.length ≤ 32}
  | [] => []
  | xs@(_ :: _) =>
    ⟨ List.toBytes (xs.take 32),
      by rw [List.length_toBytes];
         simp [Bytes.length];
         apply min_le_left ⟩ :: (xs.drop 32).break

def initializeStore : Word → List {xs : Bytes // xs.length ≤ 32} → Line
  | _, [] => []
  | w, [⟨xs, _⟩] =>
    match xs.length with
    | 32 => Inst.push xs asm :: mstoreAt w
    | n => Inst.push xs asm :: Inst.pushWord (Nat.toWord (8 * (32 - n))) :: Inst.shl :: mstoreAt w
  | w, ⟨xs, _⟩ :: l => (Inst.push xs asm :: mstoreAt w) ++ initializeStore (w + 1) l

def initializer (bs : Bytes) : Func :=
  initializeStore 0 (List.break <| Bytes.toList bs) +++
  pushList [Nat.toBits 256 bs.length, 0] +++
  Func.ret

def initFunc (p : Prog) : Func :=
initializer <| (Prog.compile p).getD ⟪⟫

def initCode (p : Prog) : Bytes :=
  (Prog.compile ⟨initFunc p, []⟩).getD ⟪⟫

partial def Bytes.chunks (bs : Bytes) : List Bytes :=
  (go bs.toList).map List.toBytes where
  go : List Byte → List (List Byte)
  | l =>
    match List.splitAt 32 l with
    | (_, []) => [l ++ (List.repeat 0 (32 - l.length))]
    | (l', l'') => l' :: go l''

def mstoreLine (n : Nat) (bs : Bytes) : String :=
  s!"mstore({n}, {Bytes.toString' bs})"

def mstoreLines (bs : Bytes) : List String := go 96 (Bytes.chunks bs) where
  go : Nat → List Bytes → List String
  | _, [] => []
  | n, bs :: bss => mstoreLine n bs :: go (n + 32) bss

def deployerCode (bs : Bytes) : String :=
  List.foldl (λ x y => x ++ "\n" ++ y) "" <|
  [ "pragma solidity ^0.8.26;",
    "contract Deploy {",
    "  function deploy() public returns (address) {",
    "  address retval;",
    "    assembly{" ]
  ++ (mstoreLines bs).map ("      " ++ ·)
  ++ [s!"      retval := create(0, 96, {bs.length})"]
  ++ [ "    }",
       "    return retval;",
       "  }",
       "}" ]

def printDeployerCode (p : Prog) : IO Unit :=
  IO.print <| deployerCode <| initCode p

#eval printDeployerCode weth
