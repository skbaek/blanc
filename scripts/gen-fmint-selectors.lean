-- gen-fmint-selectors.lean : the named emitter for `scripts/fmint-selectors.json`.
--
-- Run from the repository root:
--
--     lake env lean scripts/gen-fmint-selectors.lean
--
-- It evaluates `Blanc.Fmint.fmintFuncs.map Prod.fst` -- the twelve function
-- selectors Blanc's own fmint dispatcher actually routes to, in the ascending
-- order `Blanc.Fmint.fmintFuncs_sorted` requires -- and writes them to
-- `scripts/fmint-selectors.json`.
--
-- The sibling of `gen-weth-selectors.lean`: this is the SOLE source
-- `scripts/check-fmint-coverage.py` uses for "what are fmint's twelve
-- selectors", no ABI signature string retyped anywhere else. Regenerating
-- must leave the working tree clean
-- (`git diff --exit-code scripts/fmint-selectors.json`).
--
-- Unlike WETH, fmint has no `deposit`-style fallback entrypoint: its
-- fallback (`Blanc.Fmint.fallbackSlot`) is a bare revert, and every fmint
-- behaviour is reached through one of these twelve selectors -- so, unlike
-- `gen-weth-selectors.lean`, there is no eleventh "empty calldata" case to
-- document here.

import Blanc.Fmint

namespace Blanc

open Jaune

/-- 8-hex-digit `0x`-prefixed selector, e.g. `0x06fdde03` -- the same
rendering `gen-weth-selectors.lean`'s `hexSelector` uses. -/
private def hexSelector (w : B256) : String :=
  let ds := Nat.toDigits 16 w.toNat
  let padded := (List.replicate (8 - ds.length) '0') ++ ds
  "0x" ++ String.ofList padded

private def renderJson (ws : List String) : String :=
  let items := ws.map (fun s => "\"" ++ s ++ "\"")
  "[\n  " ++ String.intercalate ",\n  " items ++ "\n]\n"

private def outPath : System.FilePath := "scripts" / "fmint-selectors.json"

#eval show IO Unit from do
  let selectors := Blanc.Fmint.fmintFuncs.map Prod.fst
  if selectors.length ≠ 12 then
    throw (IO.userError s!"Blanc.Fmint.fmintFuncs has {selectors.length} entries, \
expected 12 -- this is a real change to fmint's dispatcher and \
scripts/fmint-coverage-budget.txt needs a matching, deliberate update, not a \
silent regeneration")
  let hexes := selectors.map hexSelector
  IO.FS.writeFile outPath (renderJson hexes)
  IO.println s!"wrote {outPath} ({hexes.length} selectors)"

end Blanc
