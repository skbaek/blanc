Task an agent: Step 1 (harness recreation, both repos).
Accept: cd ~/elevm && scripts/check.sh --depth && scripts/check.sh --smoke, then cd ~/blanc && scripts/check.sh — three OK verdicts.
Commit: elevm + blanc.
----------------------------------------------------------------
Launch the FULL baseline overnight: cd ~/elevm && nohup scripts/check.sh --full --rebase > full-run.log 2>&1 &
Next morning: tail full-run.log (a --rebase run can't fail; it defines the baseline), then commit scripts/baseline-full.txt in elevm. This just needs to happen on some night before Step 12 — it doesn't block Steps 2–11.
----------------------------------------------------------------
Task an agent: Step 2 (dead-weight sweep, both repos).
Accept: cd ~/elevm && scripts/check.sh --depth + cd ~/blanc && scripts/check.sh.
Commit: elevm + blanc.
----------------------------------------------------------------
Task an agent: Step 3 (frame relations + lift lemmas, blanc, additive).
Accept: cd ~/blanc && scripts/check.sh.
Also read the report's two calibration proofs — the blobhash one at ≤ 10 lines is the go/no-go for the whole consolidation. Commit: blanc.
----------------------------------------------------------------
Task an agent: Step 4 (master Rinst frame theorem, blanc, additive).
Accept: cd ~/blanc && scripts/check.sh. Commit: blanc.
----------------------------------------------------------------
Task an agent: Step 5 (collapse the Rinst observation corpus, blanc).
Accept: cd ~/blanc && scripts/check.sh. Any lemma the report says wouldn't collapse into a ≤ 10-line projection is worth your eyes before committing. Commit: blanc.
----------------------------------------------------------------
Task an agent: Step 6 (Jinst/Linst/Ninst masters + collapse, blanc).
Accept: cd ~/blanc && scripts/check.sh. Commit: blanc (possibly at the Jinst-only boundary if the agent stopped early — that's a sanctioned stopping point).
----------------------------------------------------------------
Task an agent: Step 7 (Xinst prep consolidation, blanc).
Accept: cd ~/blanc && scripts/check.sh. Keep the footprint-classification table from the report. Commit: blanc.
----------------------------------------------------------------
Task an agent: Step 8 (global deletion + Solvent retargeting, blanc).
Accept: cd ~/elevm && scripts/check.sh --depth + cd ~/blanc && scripts/check.sh.
Commit: blanc.
----------------------------------------------------------------
Task an agent: Step 9 (effect-framework rationalization, blanc).
Accept: cd ~/blanc && scripts/check.sh. Commit: blanc.
----------------------------------------------------------------
Task an agent: Step 10 (elevm _def/lift-layer audit).
Accept: cd ~/elevm && scripts/check.sh --depth + cd ~/blanc && scripts/check.sh.
Commit: elevm.
----------------------------------------------------------------
Task an agent: Step 11 (Phase 3 prep, eta-safe rewrites, both repos).
Accept: cd ~/elevm && scripts/check.sh --depth + cd ~/blanc && scripts/check.sh.
Commit: elevm + blanc.
----------------------------------------------------------------
Checkpoint — confirm the FULL baseline exists (ls ~/elevm/scripts/baseline-full.txt and that it's committed). If you never ran the overnight baseline, do it now; Step 12 must not start without it.
----------------------------------------------------------------
Task an agent: Step 12 (the Devm nesting flip, both repos, coordinated).
Accept: cd ~/elevm && scripts/check.sh --depth && scripts/check.sh --smoke + cd ~/blanc && scripts/check.sh — any tier diff is a hard stop and revert, not a fix-forward.
Commit: elevm first, then blanc with the elevm hash in the message (the agent's report states it).
----------------------------------------------------------------
Task an agent: Step 13 (post-flip cleanup + final accounting, both repos).
Accept: same V3 trio as Step 12. Commit: elevm + blanc.
----------------------------------------------------------------
Launch the closing FULL run overnight: cd ~/elevm && nohup scripts/check.sh --full > full-run.log 2>&1 & (no --rebase this time).
Next morning: tail full-run.log must end OK — full: 2984 files match baseline. That line is the arc's final certificate. If it reports a regression instead, the diff report names the files — that's a debugging session against Step 12/13's changes before anything else builds on this work.
