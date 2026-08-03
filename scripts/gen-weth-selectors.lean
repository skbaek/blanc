-- gen-weth-selectors.lean : the named emitter for `scripts/weth-selectors.json`.
--
-- Run from the repository root:
--
--     lake env lean scripts/gen-weth-selectors.lean
--
-- It evaluates `Blanc.wethFuncs.map Prod.fst` -- the ten function selectors
-- Blanc's own WETH dispatcher actually routes to -- and writes them, in
-- ascending order (the order `Blanc.wethFuncs_sorted` requires `wethFuncs`
-- to already be in), to `scripts/weth-selectors.json`.
--
-- This is the SOLE source `scripts/check-weth-coverage.sh` uses for "what
-- are Blanc's ten selectors" (~/plans/weth-evidence.md, Fixed design
-- decision 5): no ABI signature string is retyped in the Python checker or
-- anywhere else. Regenerating must leave the working tree clean
-- (`git diff --exit-code scripts/weth-selectors.json`), exactly like
-- `gen-weth-code.lean` / `Blanc/WethCode.lean`.
--
-- `deposit` is deliberately absent from the emitted list: `wethFuncs` does
-- not include it -- it is the fallback, reached via `Func.mainWith 1` when
-- calldata is empty or unrecognised, never through a selector match. See
-- `Blanc/Weth.lean`, the comment on `wethFuncs`.

import Blanc.Weth

namespace Blanc

open Jaune

/-- 8-hex-digit `0x`-prefixed selector, e.g. `0x06fdde03`. A selector is a
`B256`, but `CommonCore.selector` already shifts the signature hash right by
224 bits before returning it, so its value fits in 32 bits; four bytes
(8 hex digits) is the exact width the leading comment beside each
`wethFuncs` entry already uses. -/
private def hexSelector (w : B256) : String :=
  let ds := Nat.toDigits 16 w.toNat
  let padded := (List.replicate (8 - ds.length) '0') ++ ds
  "0x" ++ String.ofList padded

private def renderJson (ws : List String) : String :=
  let items := ws.map (fun s => "\"" ++ s ++ "\"")
  "[\n  " ++ String.intercalate ",\n  " items ++ "\n]\n"

private def outPath : System.FilePath := "scripts" / "weth-selectors.json"

#eval show IO Unit from do
  let selectors := Blanc.wethFuncs.map Prod.fst
  if selectors.length ≠ 10 then
    throw (IO.userError s!"Blanc.wethFuncs has {selectors.length} entries, \
expected 10 -- this is a real change to Blanc's dispatcher and \
scripts/weth-coverage-budget.txt (and possibly check-weth-coverage.sh's \
fixed idea of 'ten selectors plus one fallback') needs a matching, \
deliberate update, not a silent regeneration")
  let hexes := selectors.map hexSelector
  IO.FS.writeFile outPath (renderJson hexes)
  IO.println s!"wrote {outPath} ({hexes.length} selectors)"

end Blanc
