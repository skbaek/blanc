import Blanc.Lift.Usdc.ProxyForward
import Blanc.Lift.Usdc.Book

/-!
# The proxy's admin selectors (U6b)

`proxy_admin_selectors`: a successful pc-0 proxy frame called by the admin word has the selector of
one of the proxy's five admin functions, `admin()`, `implementation()`, `upgradeTo`,
`upgradeToAndCall` or `changeAdmin`.  Every other selector reaches `ifAdmin`'s `_fallback`, whose
`_willFallback` reverts for the admin.  The walk `proxy_halt_dispatch` is `proxy_halt`'s dispatcher
inversion, keeping the selector on every taken branch.
-/

namespace Blanc.Lift.Usdc.Proxy

open Jaune Blanc Blanc.Lift

/-- **The halting runs of the proxy certificate, by selector.**  A halting run from entry `0` runs
`_delegate`'s `DELEGATECALL` (`DelegateStep`, for a caller other than the admin word), or the
dispatcher selected one of the five admin functions. -/
theorem proxy_halt_dispatch {sevm : Sevm} {S : List B256} {M : Mem} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) {b : Devm} {post : Devm}
    (run : SFunc.RunP Ninst.Run prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    DelegateStep Ninst.Run sevm b post ∨
      dispatchWord sevm = Bytes.toB256 [0x36, 0x59, 0xcf, 0xe6] ∨
      dispatchWord sevm = Bytes.toB256 [0x4f, 0x1e, 0xf2, 0x86] ∨
      dispatchWord sevm = Bytes.toB256 [0x5c, 0x60, 0xda, 0x1b] ∨
      dispatchWord sevm = Bytes.toB256 [0x8f, 0x28, 0x39, 0x70] ∨
      dispatchWord sevm = Bytes.toB256 [0xf8, 0x51, 0xa4, 0x40] := by
  unfold t_0000_c0 at run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push s
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push s
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_mstore s
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push s
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_calldatasize s
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_lt s
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push s
  rcases rpw_branch run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · unfold t_000d_c0 at run
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push s
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_calldataload s
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push s
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_div s
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push s
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_and s
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push s
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_eq s
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push s
    rcases rpw_branchTo run with ⟨-, _, run⟩ | ⟨h, -⟩
    swap
    · exact .inr (.inl (eqCheck_ne_zero h).symm)
    unfold t_0041_c0 at run
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push s
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_eq s
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push s
    rcases rpw_branchTo run with ⟨-, _, run⟩ | ⟨h, -⟩
    swap
    · exact .inr (.inr (.inl (eqCheck_ne_zero h).symm))
    unfold t_004c_c0 at run
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push s
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_eq s
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push s
    rcases rpw_branchTo run with ⟨-, _, run⟩ | ⟨h, -⟩
    swap
    · exact .inr (.inr (.inr (.inl (eqCheck_ne_zero h).symm)))
    unfold t_0057_c0 at run
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push s
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_eq s
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push s
    rcases rpw_branchTo run with ⟨-, _, run⟩ | ⟨h, -⟩
    swap
    · exact .inr (.inr (.inr (.inr (.inl (eqCheck_ne_zero h).symm))))
    unfold t_0062_c0 at run
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push s
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_eq s
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push s
    rcases rpw_branchTo run with ⟨-, _, run⟩ | ⟨h, -⟩
    swap
    · exact .inr (.inr (.inr (.inr (.inr (eqCheck_ne_zero h).symm))))
    unfold t_006d_c0 at run
    obtain ⟨_, run⟩ := rpw_dest run
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push s
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push s
    obtain ⟨g, _, hg, run⟩ := rpw_jump run
    obtain rfl : g = fbTree 23 := Option.some.inj (hg.symm.trans rfl)
    exact .inl (fb_halted (fun h => h) hfork rfl run)
  unfold t_006d_c0_1 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push s
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push s
  obtain ⟨g, _, hg, run⟩ := rpw_jump run
  obtain rfl : g = fbTree 24 := Option.some.inj (hg.symm.trans rfl)
  exact .inl (fb_halted (fun h => h) hfork rfl run)

end Blanc.Lift.Usdc.Proxy

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc.Proxy

/-- **The proxy admits only its five admin functions to the admin word** (U4a addendum; additive to
`proxy_admin_rule`): a successful pc-0 proxy frame called by the admin word has the selector of
`admin()`, `implementation()`, `upgradeTo`, `upgradeToAndCall` or `changeAdmin`
(`ifAdmin`/`_willFallback`). -/
theorem proxy_admin_selectors {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (codeEq : sevm.code = Proxy.code) (fork : CoveredFork sevm.benvStat.fork)
    (admin : sevm.caller = adminOf pre.state sevm.currentTarget) :
    adminGetter sevm ∨ Blanc.Sevm.selector sevm ∈ [0x3659cfe6, 0x4f1ef286, 0x8f283970] := by
  obtain ⟨f, hf0, hrun⟩ := lift_sound cert_check codeEq fork run
  obtain rfl : f = t_0000_c0 := Option.some.inj (hf0.symm.trans rfl)
  rw [St.self' pre] at hrun
  rw [← dispatchWord_eq_selector]
  rcases proxy_halt_dispatch fork hrun with ⟨notAdmin, -⟩ | hw | hw | hw | hw | hw
  · exact (notAdmin (by rw [← adminOf_eq]; exact admin)).elim
  · exact .inr (by rw [hw]; decide)
  · exact .inr (by rw [hw]; decide)
  · exact .inl (.inr (by rw [← dispatchWord_eq_selector, hw]; decide))
  · exact .inr (by rw [hw]; decide)
  · exact .inl (.inl (by rw [← dispatchWord_eq_selector, hw]; decide))

end Blanc.Lift.Usdc
