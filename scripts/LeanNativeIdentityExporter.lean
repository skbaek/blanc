import Lean
import Lean.Util.CollectAxioms

/-!
Lean-native declaration-type exporter for the bounded shadow pilot.

This file is pasted into the existing access/enumeration axiom-probe source by
`lean_native_identity_shadow.py`.  It is deliberately not a production module
or registered gate input.  The caller supplies this file's SHA-256 in every
record, and the Python decoder verifies it before accepting the frame.

The v1 policy preserves binder/interface names, BinderInfo, universe parameter
order, referenced names and all implicit terms.  It removes `Expr.mdata`
wrappers only.  It performs no reduction or pretty printing and never reads a
declaration value.
-/

open Lean Elab Command

namespace Blanc.LeanNativeIdentityPilot

private def nameJson : Name → Json
  | .anonymous => .arr #[.str "anonymous"]
  | .str pfx value => .arr #[.str "str", nameJson pfx, .str value]
  | .num pfx value => .arr #[.str "num", nameJson pfx, toJson value]

private def binderInfoJson : BinderInfo → Json
  | .default => .str "default"
  | .implicit => .str "implicit"
  | .strictImplicit => .str "strictImplicit"
  | .instImplicit => .str "instImplicit"

private def levelJson (params : List Name) : Level → Except String Json
  | .zero => pure <| .arr #[.str "zero"]
  | .succ level => return .arr #[.str "succ", ← levelJson params level]
  | .max left right =>
      return .arr #[.str "max", ← levelJson params left, ← levelJson params right]
  | .imax left right =>
      return .arr #[.str "imax", ← levelJson params left, ← levelJson params right]
  | .param name =>
      if params.contains name then
        pure <| .arr #[.str "param", nameJson name]
      else
        throw s!"undeclared universe parameter {name}"
  | .mvar _ => throw "unresolved universe metavariable"

private def literalJson : Literal → Json
  | .natVal value => .arr #[.str "nat", toJson value]
  | .strVal value => .arr #[.str "string", .str value]

private partial def exprJson
    (params : List Name) (depth : Nat) : Expr → Except String Json
  | .bvar index =>
      if index < depth then
        pure <| .arr #[.str "bvar", toJson index]
      else
        throw s!"loose bound variable {index} at depth {depth}"
  | .fvar _ => throw "free variable in closed declaration type"
  | .mvar _ => throw "unresolved expression metavariable"
  | .sort level => return .arr #[.str "sort", ← levelJson params level]
  | .const name levels =>
      return .arr #[.str "const", nameJson name,
        .arr <| (← levels.mapM (levelJson params)).toArray]
  | .app fn arg =>
      return .arr #[.str "app", ← exprJson params depth fn,
        ← exprJson params depth arg]
  | .lam name type body info =>
      return .arr #[.str "lam", nameJson name, binderInfoJson info,
        ← exprJson params depth type, ← exprJson params (depth + 1) body]
  | .forallE name type body info =>
      return .arr #[.str "forall", nameJson name, binderInfoJson info,
        ← exprJson params depth type, ← exprJson params (depth + 1) body]
  | .letE name type value body nondep =>
      return .arr #[.str "let", nameJson name, toJson nondep,
        ← exprJson params depth type, ← exprJson params depth value,
        ← exprJson params (depth + 1) body]
  | .lit literal => pure <| .arr #[.str "lit", literalJson literal]
  | .mdata _ expr => exprJson params depth expr
  | .proj typeName index struct =>
      return .arr #[.str "proj", nameJson typeName, toJson index,
        ← exprJson params depth struct]

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def importedModuleName (env : Environment) (name : Name) : Option Name := do
  let index ← env.getModuleIdxFor? name
  env.header.moduleNames[index.toNat]?

syntax (name := blancNativeIdentity)
  "#blanc_native_identity" str str str str : command

@[command_elab blancNativeIdentity] def elabBlancNativeIdentity : CommandElab
  | `(#blanc_native_identity $moduleSyntax:str $nameSyntax:str
      $kindSyntax:str $exporterSyntax:str) => do
      let moduleText := moduleSyntax.getString
      let nameText := nameSyntax.getString
      let expectedKind := kindSyntax.getString
      let exporter := exporterSyntax.getString
      let moduleName := moduleText.toName
      let declarationName := nameText.toName
      let info ← getConstInfo declarationName
      let actualKind := declarationKind info
      unless actualKind == expectedKind do
        throwError "declaration kind mismatch for {declarationName}: got {actualKind}, expected {expectedKind}"
      let env ← getEnv
      let actualModule ←
        match importedModuleName env declarationName with
        | some actual => pure actual
        | none =>
            if env.mainModule == moduleName then pure moduleName
            else throwError "declaration {declarationName} has no imported owner and current module is {env.mainModule}, expected {moduleName}"
      unless actualModule == moduleName do
        throwError "declaration module mismatch for {declarationName}: got {actualModule}, expected {moduleName}"
      let params := info.levelParams
      let type ←
        match exprJson params 0 info.type with
        | .ok value => pure value
        | .error message => throwError "cannot encode {declarationName}: {message}"
      let axioms ← collectAxioms declarationName
      let record := Json.mkObj [
        ("schema", .str "blanc-declaration-type/v1"),
        ("toolchain", Json.mkObj [
          ("version", .str Lean.versionString),
          ("githash", .str Lean.githash)
        ]),
        ("exporter", .str exporter),
        ("module", nameJson actualModule),
        ("name", nameJson info.name),
        ("kind", .str actualKind),
        ("levelParams", .arr <| params.map nameJson |>.toArray),
        ("type", type),
        ("axioms", .arr <| axioms.qsort (fun a b => a.toString < b.toString) |>.map nameJson)
      ]
      IO.println <| "BLANC_NATIVE_IDENTITY\t" ++ record.compress
  | _ => throwUnsupportedSyntax

end Blanc.LeanNativeIdentityPilot
