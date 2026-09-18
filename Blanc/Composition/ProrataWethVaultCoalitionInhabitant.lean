import Blanc.Composition.ProrataWethVaultCoalition

namespace Blanc.Composition.ProrataWethVault

open Blanc.Prorata

theorem pair_attack_carrier_inhabited :
    ∃ state : PairAttackState Blanc.ProrataWethVault.offsetN,
      PairAttackPath Blanc.ProrataWethVault.offsetN state ∧
        state.inA = 1000001 ∧ state.outA = 500125 ∧ state.outsideSubsidy = 0 ∧
        state.sharesIn = 0 ∧ state.sharesOut = 0 := by
  have prov : ProrataAccountingProvenance := ⟨0, none, [], none⟩
  -- The coalition seeds one wei and is minted the offset's worth of shares.
  have p1 : PairAttackPath Blanc.ProrataWethVault.offsetN _ :=
    .snoc ⟨_, _, _, prov,
      .nonVictimDeposit
        (PairAttackState.genesis Blanc.ProrataWethVault.offsetN)
        .coalition 1 1000 (by norm_num [Blanc.ProrataWethVault.offsetN,
          PairAttackState.genesis,
          Blanc.Prorata.ProrataAttackState.genesis,
          Blanc.Prorata.mintN, Blanc.Prorata.payN])⟩ .genesis
  -- It donates a million, moving the price but not the supply.
  have p2 : PairAttackPath Blanc.ProrataWethVault.offsetN _ :=
    .snoc ⟨_, _, _, prov,
      .externalCredit _ .coalition 1000000⟩ p1
  -- The victim deposits a million into the moved price.
  have p3 : PairAttackPath Blanc.ProrataWethVault.offsetN _ :=
    .snoc ⟨_, _, _, prov,
      .victimDeposit _
        ⟨_, 1000000, 1999, rfl,
          (by norm_num [Blanc.ProrataWethVault.offsetN, PairAttackState.genesis,
            Blanc.Prorata.ProrataAttackState.genesis, PairAttackState.inbound,
            PairAttackState.credited,
            Blanc.Prorata.mintN, Blanc.Prorata.payN])⟩
        rfl rfl⟩ p2
  -- The coalition exits its 1000 shares.
  have p4 : PairAttackPath Blanc.ProrataWethVault.offsetN _ :=
    .snoc ⟨_, _, _, prov,
      .nonVictimWithdraw _ .coalition 1000 500125
        (by norm_num [Blanc.ProrataWethVault.offsetN, PairAttackState.genesis,
          Blanc.Prorata.ProrataAttackState.genesis, PairAttackState.inbound,
          PairAttackState.credited, PairAttackState.victimDeposited,
          Blanc.Prorata.VictimDeposit.post,
          Blanc.Prorata.mintN, Blanc.Prorata.payN])
        (by norm_num [Blanc.ProrataWethVault.offsetN, PairAttackState.genesis,
          Blanc.Prorata.ProrataAttackState.genesis, PairAttackState.inbound,
          PairAttackState.credited, PairAttackState.victimDeposited,
          Blanc.Prorata.VictimDeposit.post,
          Blanc.Prorata.mintN, Blanc.Prorata.payN])⟩ p3
  refine ⟨_, p4, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Blanc.ProrataWethVault.offsetN, PairAttackState.genesis,
      Blanc.Prorata.ProrataAttackState.genesis,
      PairAttackState.inbound,
      PairAttackState.credited, PairAttackState.victimDeposited,
      PairAttackState.outbound, Blanc.Prorata.AttackAttribution.coalitionAmount,
      Blanc.Prorata.AttackAttribution.outsideAmount,
      Blanc.Prorata.VictimDeposit.post,
      Blanc.Prorata.mintN, Blanc.Prorata.payN]

end Blanc.Composition.ProrataWethVault
