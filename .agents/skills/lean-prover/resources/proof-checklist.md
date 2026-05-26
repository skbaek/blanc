# Lean 4 Tactic Guardrails

When planning your next tactic step in the Read-Think-Write-Look loop, adhere to these mathematical constraints:

- Prefer structured tactics (`rcases`, `obtain`, `gcongr`) over chaotic, unmaintainable strings of rewrites when breaking down structures.
- If a goal looks like it can be discharged by automation, try `aesop`, `simp`, or `linarith` as a single step, then instantly check the Look step to see if it worked.
- Never loop endlessly on the same tactic if the goal state isn't changing. If a tactic results in the identical goal state, backtrack immediately.
- Do not invent lemma names. Only use mathlib4 lemmas that you have verified exist in the imported files or can safely infer.