import Blanc.Composition.Curve3PoolVirtualPriceFallsWorld

/-!
# The generator of the bytes-level fall's literal boundaries

An untrusted evaluation, in Lean's interpreter, of the run the kernel then checks: it walks each
call, prints a boundary every `chunkSteps` steps and at every frame edge, and writes the data, chunk
and composition modules `Curve3PoolVirtualPriceFallsData`, `Curve3PoolVirtualPriceFallsFactsN` and
`Curve3PoolVirtualPriceFallsChain`.  Nothing it prints is trusted: a wrong boundary fails its chunk's kernel
check.  To regenerate, build a scratch module whose only command is `#eval genAll "<directory>"`.
-/

namespace Blanc.Composition.Curve3PoolVirtualPriceFalls.Gen

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk
open Blanc.Lift.Curve3Pool.VirtualPriceFalls
open Blanc.Lift.Curve3Pool (answerWord)

/-- Steps in one walk chunk. -/
def chunkSteps : Nat := 400

/-- Steps in one facts module. -/
def moduleSteps : Nat := 3000

/-- Code with its tries and its name in the generated text. -/
structure CodeE where
  code : ByteArray
  d : Nat
  T : CodeTries code d
  codeName : String
  triesName : String

/-- The code table, by code address. -/
def codeTable : List (Adr × CodeE) :=
  [(poolA, ⟨_, _, Curve3Pool.codeTries, "Curve3Pool.code", "Curve3Pool.codeTries"⟩),
   (c3A, ⟨_, _, Curve3Crv.codeTries, "Curve3Crv.code", "Curve3Crv.codeTries"⟩),
   (daiA, ⟨_, _, Dai.codeTries, "Dai.code", "Dai.codeTries"⟩),
   (usdcA, ⟨_, _, Usdc.Proxy.codeTries, "Usdc.Proxy.code", "Usdc.Proxy.codeTries"⟩),
   (implA, ⟨_, _, Usdc.ImplV2.codeTries, "Usdc.ImplV2.code", "Usdc.ImplV2.codeTries"⟩),
   (usdtA, ⟨_, _, Usdt.codeTries, "Usdt.code", "Usdt.codeTries"⟩)]

def entryOf (s : Sevm) : Option CodeE :=
  match s.codeAddress with
  | none => none
  | some a => (codeTable.find? fun p => p.1 == a).map (·.2)

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- `0x…` of a number. -/
def natHex (n : Nat) : String :=
  "0x" ++ String.ofList ((Nat.toDigits 16 n))

def bytesNat (l : List UInt8) : Nat := l.foldl (fun acc b => acc * 256 + b.toNat) 0

def listLit (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"

def bytesLit (l : List UInt8) : String := listLit (l.map fun b => natHex b.toNat)

def b256Lit (b : B256) : String := natHex b.toNat
def adrLit (a : Adr) : String := natHex a.toNat

def keyLit (k : Adr × B256) : String := s!"({adrLit k.1}, {b256Lit k.2})"
def storLit (e : (Adr × B256) × B256) : String := s!"({keyLit e.1}, {b256Lit e.2})"

structure GenSt where
  data : Array String := #[]
  facts : Array (Array String) := #[#[]]
  factSteps : Nat := 0
  chain : Array String := #[]
  nb : Nat := 0
  nf : Nat := 0
  ns : Nat := 0
  nr : Nat := 0
  keysPool : List (List (Adr × B256) × String) := []
  adrsPool : List (List Adr × String) := []
  storPool : List (StorShadow × String) := []
  sevmNames : List String := []

abbrev GenM := StateT GenSt IO

def emitD (t : String) : GenM Unit := modify fun g => { g with data := g.data.push t }

def emitF (steps : Nat) (t : String) : GenM Unit :=
  modify fun g =>
    let g := if moduleSteps ≤ g.factSteps then { g with facts := g.facts.push #[], factSteps := 0 } else g
    { g with facts := g.facts.modify (g.facts.size - 1) (·.push t), factSteps := g.factSteps + steps }

def emitC (t : String) : GenM Unit := modify fun g => { g with chain := g.chain.push t }

def internKeys (l : List (Adr × B256)) : GenM String := do
  let g ← get
  match g.keysPool.find? (·.1 == l) with
  | some (_, n) => pure n
  | none =>
    let n := s!"kS{g.keysPool.length}"
    emitD s!"def {n} : List (Adr × B256) := {listLit (l.map keyLit)}"
    modify fun g => { g with keysPool := (l, n) :: g.keysPool }
    pure n

def internAdrs (l : List Adr) : GenM String := do
  let g ← get
  match g.adrsPool.find? (·.1 == l) with
  | some (_, n) => pure n
  | none =>
    let n := s!"aS{g.adrsPool.length}"
    emitD s!"def {n} : List Adr := {listLit (l.map adrLit)}"
    modify fun g => { g with adrsPool := (l, n) :: g.adrsPool }
    pure n

def internStor (l : StorShadow) : GenM String := do
  let g ← get
  match g.storPool.find? (·.1 == l) with
  | some (_, n) => pure n
  | none =>
    let n := s!"sS{g.storPool.length}"
    emitD s!"def {n} : StorShadow := {listLit (l.map storLit)}"
    modify fun g => { g with storPool := (l, n) :: g.storPool }
    pure n

def intLit (i : Int) : String := if i < 0 then s!"(-{i.natAbs})" else s!"{i.natAbs}"

/-- Print a boundary, named. -/
def emitB (pc : Nat) (d : Devm) (keys : List (Adr × B256)) (adrs : List Adr) (stor : StorShadow) :
    GenM String := do
  let kn ← internKeys keys
  let an ← internAdrs adrs
  let sn ← internStor stor
  let g ← get
  let n := s!"b{g.nb}"
  modify fun g => { g with nb := g.nb + 1 }
  let dataL := d.mach.memory.data.toList
  emitD s!"def {n} : XB := ⟨{pc}, {listLit (d.mach.stack.map b256Lit)}, memHex {d.mach.memory.size} {dataL.length} {natHex (bytesNat dataL)}, {d.mach.gasLeft}, {intLit d.refundCounter}, {bytesLit d.output}, {bytesLit d.returnData}, {kn}, {an}, {sn}⟩"
  pure n

/-- Print a static machine, named. -/
def emitSevm (s : Sevm) (codeName statName : String) : GenM String := do
  let g ← get
  let n := s!"sv{g.ns}"
  modify fun g => { g with ns := g.ns + 1 }
  let optA : Option Adr → String
    | none => "none"
    | some a => s!"some {adrLit a}"
  emitD s!"def {n} : Sevm := ⟨{adrLit s.caller}, {optA s.target}, {adrLit s.currentTarget}, {s.gas}, {b256Lit s.value}, {bytesLit s.data}, {optA s.codeAddress}, {codeName}, {s.depth}, {s.shouldTransferValue}, {s.isStatic}, {s.disablePrecompiles}, {statName}, (default : Tenv).stat⟩"
  pure n

def freshFact (pre : String) : GenM String := do
  let g ← get
  modify fun g => { g with nf := g.nf + 1 }
  pure s!"{pre}{g.nf}"

def freshRun : GenM String := do
  let g ← get
  modify fun g => { g with nr := g.nr + 1 }
  pure s!"r{g.nr}"

/-- The chain events of a frame, in order. -/
inductive Ev
  | walk (b fact : String)
  | spawn (b factS factR stName : String) (hstat : Unit) (run : String)
  | done (b fact : String)
  | halt (b fact : String)

/-- Evaluate one frame from a configuration named `b0`; returns the halted machine, its last
configuration and the names of its end boundary and its composition theorem. -/
partial def genFrame (e : CodeE) (s : Sevm) (sName statName : String) (b0 : String) (c0 : PCfg) :
    GenM (Devm × PCfg × String × String) := do
  let hcName := s!"hc_{sName}"
  emitC s!"theorem {hcName} : {sName}.code = {e.codeName} := rfl"
  let mut evs : Array Ev := #[]
  let mut names : Array String := #[b0]
  let mut c := c0
  let mut bn := b0
  let mut result : Option (Devm × PCfg × String) := none
  while result.isNone do
    -- walk up to a chunk
    let mut k := 0
    let mut cur := c
    let mut stop := false
    while !stop && k < chunkSteps do
      match xStep e.T s cur with
      | .cont c' =>
        cur := c'
        k := k + 1
      | _ => stop := true
    if 0 < k then
      let y ← emitB cur.pc cur.devm cur.keys cur.adrs cur.stor
      let f ← freshFact "w"
      emitF k s!"theorem {f} : ∀ m w, walkObs {e.triesName} {sName} acsW {bn} {y} {k} m w = some (xOk acsW) := by\n  kernel_forall_rfl"
      evs := evs.push (.walk bn f)
      c := cur
      bn := y
    else
      match xStep e.T s c with
      | .halt (.ok d) =>
        let z ← emitB 0 d c.keys c.adrs c.stor
        let f ← freshFact "h"
        emitF 1 s!"theorem {f} : ∀ m w, haltObs {e.triesName} {sName} acsW {bn} {z} m w = some (xOk acsW) := by\n  kernel_forall_rfl"
        evs := evs.push (.halt bn f)
        result := some (d, c, z)
      | .halt (.error _) => throw (IO.userError s!"halt error at pc {c.pc} in {sName}")
      | .cont _ => throw (IO.userError "unreachable")
      | .stuck =>
        match decodeT e.d e.T.bytes c.pc with
        | some (.next (.exec i)) =>
          match prepX s c i with
          | none => throw (IO.userError s!"prep none at pc {c.pc} in {sName}")
          | some cp =>
            match frameEnterS cp.f c.acs with
            | .done (.ok ch) =>
              match resumeCallB cp.p cp.oi cp.os (.ok ch) with
              | none => throw (IO.userError s!"resume none at pc {c.pc}")
              | some d' =>
                let y ← emitB (c.pc + 1) d' c.keys cp.adrs c.stor
                let f ← freshFact "d"
                emitF 1 s!"theorem {f} : ∀ m w, doneObsC {e.triesName} {sName} ({bn}.cfg acsW m w) {y} = some (xOk acsW, 0, false) := by\n  kernel_forall_rfl"
                evs := evs.push (.done bn f)
                c := { pc := c.pc + 1, devm := d', keys := c.keys, adrs := cp.adrs, stor := c.stor, acs := c.acs }
                bn := y
            | .done (.error _) => throw (IO.userError s!"precompile error at pc {c.pc}")
            | .run ce =>
              match entryOf ce.sta with
              | none => throw (IO.userError s!"no code entry at pc {c.pc}")
              | some e' =>
                let cc := childCfg ce cp.f c.keys cp.adrs c.stor c.acs
                let sc ← emitSevm ce.sta e'.codeName statName
                let cx ← emitB cc.pc cc.devm cc.keys cc.adrs cc.stor
                let (dch, cl, zc, rc) ← genFrame e' ce.sta sc statName cx cc
                let fs ← freshFact "sp"
                emitF 1 s!"theorem {fs} : ∀ m w, spawnObs {e.triesName} {sName} acsW {bn} {cx} {sc} m w = some (xOk acsW, 0, {sc}, true) := by\n  kernel_forall_rfl"
                match resumeCallB cp.p cp.oi cp.os (.ok dch) with
                | none => throw (IO.userError s!"resume none at pc {c.pc}")
                | some d' =>
                  let c' : PCfg := ⟨c.pc + 1, d', mergeL c.keys cl.keys, mergeL cp.adrs cl.adrs, cl.stor, cl.acs⟩
                  let y ← emitB c'.pc c'.devm c'.keys c'.adrs c'.stor
                  let fr ← freshFact "rs"
                  emitF 1 s!"theorem {fr} : ∀ m w m' w', resumeObsC {e.triesName} {sName} acsW ({bn}.cfg acsW m w) {zc} {y} m' w' = some (xOk acsW) := by\n  kernel_forall_rfl"
                  evs := evs.push (.spawn bn fs fr sc () rc)
                  c := c'
                  bn := y
        | _ => throw (IO.userError s!"stuck at pc {c.pc} in {sName}")
  let some (d, cl, z) := result | throw (IO.userError "no result")
  -- the composition, backwards
  let mut last := ""
  for ev in evs.reverse do
    let r ← freshRun
    match ev with
    | .halt b f =>
      emitC s!"theorem {r} : RunsB {sName} acsW {b} {z} := .halt {e.triesName} {hcName} {f}"
    | .walk b f =>
      emitC s!"theorem {r} : RunsB {sName} acsW {b} {z} := .walk {e.triesName} {hcName} {f} {last}"
    | .done b f =>
      emitC s!"theorem {r} : RunsB {sName} acsW {b} {z} := .done {e.triesName} {hcName} {f} {last}"
    | .spawn b fs fr sc _ rc =>
      emitC s!"theorem {r} : RunsB {sName} acsW {b} {z} := .call {e.triesName} (sc := {sc}) {hcName} rfl {fs} {rc} {fr} {last}"
    last := r
  pure (d, cl, z, last)

/-- The top-level call of one stage, at the world's shadows. -/
def genStage (name : String) (W : Jaune.State) (statName : String) (stat : BenvStat) (dataName : String) (data : Bytes)
    (st : Bool) (stor : StorShadow) : GenM (Devm × PCfg × String × String × String) := do
  let m := msgOf W stat data st
  let f := Frame.ofCall m
  match frameEnterS f acsW with
  | .done _ => throw (IO.userError "top done")
  | .run ce =>
    let sv := s!"sevm{name}"
    emitD s!"def {sv} : Sevm := sevmOf {statName} {dataName} {st}"
    let cc := childCfg ce f [] [] stor acsW
    let b := s!"start{name}"
    let n ← emitB cc.pc cc.devm cc.keys cc.adrs cc.stor
    emitD s!"abbrev {b} : XB := {n}"
    let some e := entryOf ce.sta | throw (IO.userError "no top entry")
    let (d, cl, z, r) ← genFrame e ce.sta sv statName n cc
    emitC s!"abbrev end{name} : XB := {z}"
    emitC s!"theorem run{name} : RunsB {sv} acsW {n} {z} := {r}"
    IO.println s!"{name}: gas used {10000000 - d.gasLeft}, word {answerWord d.output}"
    pure (d, cl, sv, n, z)

/-- The generation parameters: the deposit and the burn. -/
structure Params where
  a0 : Nat := amt0
  a1 : Nat := amt1
  a2 : Nat := amt2
  burn : Nat := 8

def header (imports : List String) (doc : String) : String :=
  "\n".intercalate (imports.map (s!"import {·}")) ++ "\n\n/-! GENERATED by `Curve3PoolVirtualPriceFallsGen.genAll`: do not edit. " ++ doc ++ " -/\n\nnamespace Blanc.Composition.Curve3PoolVirtualPriceFalls\n\nopen Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk\nopen Blanc.Lift.Curve3Pool.VirtualPriceFalls\n\n"

def footer : String := "\nend Blanc.Composition.Curve3PoolVirtualPriceFalls\n"

/-- Generate the data, chunk and composition modules into `dir`. -/
def genAll (dir : String) (p : Params := {}) : IO Unit := do
  let storW := storShadowOf worldWrites
  let act : GenM Unit := do
    emitD s!"def storW : StorShadow := {listLit (storW.map storLit)}"
    emitD "def stat1 : BenvStat := statOf storW"
    emitD s!"def data1 : Bytes := {bytesLit (depositData p.a0 p.a1 p.a2)}"
    emitD s!"def data2 : Bytes := {bytesLit (oneCoinData p.burn)}"
    emitD s!"def dataP : Bytes := {bytesLit priceData}"
    let (d1, c1, _, _, _) ← genStage "Deposit" worldW "stat1" (statOf storW) "data1" (depositData p.a0 p.a1 p.a2) false storW
    let s1n ← internStor c1.stor
    emitD s!"def stat2 : BenvStat := statOf {s1n}"
    let st2 := statOf c1.stor
    let _ ← genStage "Price1" d1.state "stat2" st2 "dataP" priceData true c1.stor
    let (d2, c2, _, _, _) ← genStage "Call" d1.state "stat2" st2 "data2" (oneCoinData p.burn) false c1.stor
    let _ ← genStage "Price2" d2.state "stat2" st2 "dataP" priceData true c2.stor
  let (_, g) ← act.run {}
  let pre := "Blanc.Composition.Curve3Pool"
  IO.FS.writeFile s!"{dir}/Curve3PoolVirtualPriceFallsData.lean"
    (header [pre ++ "VirtualPriceFallsWorld"] "The literal boundaries of the fall's four calls." ++
      "\n\n".intercalate g.data.toList ++ "\n" ++ footer)
  let mut mods : List String := []
  for i in [0:g.facts.size] do
    IO.FS.writeFile s!"{dir}/Curve3PoolVirtualPriceFallsFacts{i}.lean"
      (header [pre ++ "VirtualPriceFallsData"] "Kernel decisions of the fall's chunks." ++
        "\n\n".intercalate g.facts[i]!.toList ++ "\n" ++ footer)
    mods := mods ++ [pre ++ s!"VirtualPriceFallsFacts{i}"]
  IO.FS.writeFile s!"{dir}/Curve3PoolVirtualPriceFallsChain.lean"
    (header mods "The composition of the chunks; it evaluates nothing." ++
      "\n\n".intercalate g.chain.toList ++ "\n" ++ footer)
  IO.println s!"data {g.data.size} facts modules {g.facts.size} boundaries {g.nb} frames {g.ns}"

end Blanc.Composition.Curve3PoolVirtualPriceFalls.Gen
