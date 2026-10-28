import Blanc.Lift.Usdc.ImplV2_1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb006 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x5b 0x56 0x36 0x3 0x61 0x57 0x42 0x7)) 1 (by decide) (UInt64.ofBytes 0x61 0x14 0x9 0x1e 0xc8 0x2f 0x63 0x80)) 2 (by decide) (UInt64.ofBytes 0xaf 0x92 0x30 0x63 0x80 0x57 0xca 0x4)) 3 (by decide) (UInt64.ofBytes 0x63 0x80 0x57 0xfd 0x4 0x61 0x14 0xd5)) 4 (by decide) (UInt64.ofBytes 0x30 0x5 0x61 0x14 0x1f 0xf8 0xad 0x30)) 5 (by decide) (UInt64.ofBytes 0x63 0x80 0x5b 0x56 0x36 0x3 0x61 0x57)) 6 (by decide) (UInt64.ofBytes 0x14 0x3 0x61 0x11 0x66 0x52 0x89 0x1a)) 7 (by decide) (UInt64.ofBytes 0x14 0x66 0x52 0x89 0x1a 0x63 0x80 0x57)) 8 (by decide) (UInt64.ofBytes 0xb8 0x23 0x63 0x80 0x57 0x1f 0x4 0x61)) 9 (by decide) (UInt64.ofBytes 0x80 0x57 0x54 0x4 0x61 0x14 0xdd 0x72)) 10 (by decide) (UInt64.ofBytes 0x4 0x61 0x14 0x45 0x0 0xb6 0x2a 0x63)) 11 (by decide) (UInt64.ofBytes 0x80 0x5b 0x56 0x36 0x3 0x61 0x57 0x97)) 12 (by decide) (UInt64.ofBytes 0x3 0x61 0x14 0x3 0xde 0xfd 0x6 0x63)) 13 (by decide) (UInt64.ofBytes 0xb3 0xa7 0x5e 0x9 0x63 0x80 0x57 0x3b)) 14 (by decide) (UInt64.ofBytes 0x18 0x63 0x80 0x57 0xb8 0x3 0x61 0x14)) 15 (by decide) (UInt64.ofBytes 0x57 0x5 0x4 0x61 0x14 0xdd 0xd 0x16)) 16 (by decide) (UInt64.ofBytes 0x3 0x61 0x5b 0xfd 0x80 0x0 0x60 0x5b))

private def absorbed006 : Vector UInt64 25 :=
  #v[0xcaaef879256db1ba, 0xe3bc40d1a3714949, 0x5969aa037cb4f60d, 0x773b696cac66bfc4, 0xab57acea3fe971bf, 0x5e762498efd66fb0, 0x1dc3bdfc26e39fbf, 0x7d0f04acec63b906, 0xee529ad2faf1d227, 0x877f4a6cad6ccb22, 0xba5c6f8a4610ed5b, 0x1bda7e58c9dbac7c, 0x1d7936a4161e892d, 0x66865f3e69e51ca2, 0x58bb6faf4179669d, 0x57ef5accd11ac6cb, 0xb517b837f93ce4cf, 0x387b0a799b044125, 0x31a4b64c582a20c9, 0xb5dabf7707b72031, 0xdcd305c6f743a5a5, 0x1ddc4e75479e6365, 0x55397ef2827d928f, 0x98848c2180c7b1be, 0xa1f14b6b7a2ae5ce]

private theorem words006 : absorb006 state006 = absorbed006 := by
  decide +kernel

private def quarter006_1 : Vector UInt64 25 :=
  #v[0x1e12eecafc465a61, 0x7d6f6510550999f0, 0xff0b82b8ed18389a, 0x8c417aaf26294eaf, 0xd5270dcbc4bdc1c6, 0xf30764d13ec7c8ef, 0x1441ca6737fe927b, 0x7f7d6a07ce301a36, 0xa1ec0233d3937d8e, 0x5f73d450f2103543, 0x1c9c77286941f358, 0x804db99b55931aa6, 0x91abd9bb46c63e0e, 0xa0084d2dd9d5d36b, 0x9a567449a1e31d20, 0xf645aeb6a1d520ef, 0x33037cdea2538efd, 0xbd48e28e8e05430c, 0x6ce8931f42311b56, 0xa9d8b967207007bc, 0x9466d92d2f19a67d, 0xcc7ef438ea171b7e, 0xd4949a0348a4dcbf, 0x6f977abef17146f3, 0x71bc2aa8fc00bf5c]

private theorem rounds006_0 : sixRounds 0 (by decide) absorbed006 = quarter006_1 := by
  decide +kernel

private def quarter006_2 : Vector UInt64 25 :=
  #v[0x80c174efdb502177, 0x6676b4e830a19a5e, 0x882e28eeb3346ec, 0xca8dd5e20bb91b40, 0x930c36c78331f7b3, 0xc7499b8ff4d2ad1d, 0xbd833511eb65897a, 0xfd2ac1a19cd02144, 0x9502a39cd32681c2, 0xfccf9b1710ebc7f4, 0xe9a4aaddb9cafbed, 0xdca694db83124142, 0xeb26b00d111c441f, 0x3b4e98bfabc39100, 0x860f41f405b5e86c, 0xc0ae2089a1afec62, 0xdae6c299d39c6c51, 0x97f09af8408e0f63, 0x96bb6832d5af4b64, 0xf031c78a6635cfd8, 0x82866ee9379e5582, 0xa168911e1a20e759, 0x3e7aded3c66712a, 0x875d1946d11636c5, 0x1e1d2301f59f331e]

private theorem rounds006_1 : sixRounds 6 (by decide) quarter006_1 = quarter006_2 := by
  decide +kernel

private def quarter006_3 : Vector UInt64 25 :=
  #v[0xd0266467d66730bf, 0x54e352e110079b9b, 0xca3c9e56376953c6, 0xa4cb01b2593fe39, 0x704d1818e00ce884, 0x8ac68a9b8825826, 0xa78c336bf723b02a, 0x2f4fc56889ba4258, 0x985ac5484dd672af, 0x6c985e81071b93e0, 0xa9f4728fb1dbac7f, 0xc9c60b1d452910e7, 0x27df5e6b19ac64fd, 0xe29dc949a69e6bc2, 0x2c11eb4c4e1ef919, 0x277ca889ba838b96, 0xfdac2e8d29ca358e, 0xead0f84f790e9f80, 0x686950c5e84abf7b, 0x78bee4fe5ddbea7b, 0xf3e9f843c371c002, 0xb9ff66b73237711f, 0xece114fe06b6da6f, 0x2cee9d983f50726b, 0x1412d0fcc9a136b7]

private theorem rounds006_2 : sixRounds 12 (by decide) quarter006_2 = quarter006_3 := by
  decide +kernel

private theorem rounds006_3 : sixRounds 18 (by decide) quarter006_3 = state007 := by
  decide +kernel

private theorem perm006 : KECCAK.f1600 absorbed006 = state007 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds006_0, rounds006_1, rounds006_2, rounds006_3]
  rfl

theorem block006 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes006 ++ tail) state006 =
      KECCAK.Bytes.run 0 tail state007 := by
  exact run_block_of_step bytes006 tail absorb006 state006 absorbed006
    state007 (fun _ => rfl) words006 perm006

private def absorb007 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x40 0x60 0x5b 0x56 0xc6 0xd 0x61 0x43)) 1 (by decide) (UInt64.ofBytes 0x83 0x52 0x82 0x80 0x20 0x60 0x51 0x80)) 2 (by decide) (UInt64.ofBytes 0x91 0x51 0x83 0x52 0x1 0x83 0x81 0x51)) 3 (by decide) (UInt64.ofBytes 0x85 0x91 0x1 0x83 0x90 0x92 0x83 0x92)) 4 (by decide) (UInt64.ofBytes 0x5b 0x0 0x60 0x83 0x83 0x80 0x90 0x1)) 5 (by decide) (UInt64.ofBytes 0x57 0x7d 0x3 0x61 0x15 0x10 0x81 0x83)) 6 (by decide) (UInt64.ofBytes 0x52 0x1 0x82 0x83 0x51 0x1 0x81 0x81)) 7 (by decide) (UInt64.ofBytes 0x5b 0x56 0x65 0x3 0x61 0x1 0x20 0x60)) 8 (by decide) (UInt64.ofBytes 0x81 0x90 0x50 0x90 0x50 0x50 0x50 0x50)) 9 (by decide) (UInt64.ofBytes 0x61 0x15 0x80 0x16 0x1f 0x60 0x90 0x1)) 10 (by decide) (UInt64.ofBytes 0x51 0x80 0x3 0x82 0x80 0x57 0xaa 0x3)) 11 (by decide) (UInt64.ofBytes 0x1 0x61 0x3 0x20 0x60 0x83 0x1 0x60)) 12 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x16 0x19 0x3 0xa 0x0)) 13 (by decide) (UInt64.ofBytes 0x50 0x92 0x50 0x5b 0x50 0x91 0x1 0x20)) 14 (by decide) (UInt64.ofBytes 0x3 0x91 0x80 0x51 0x40 0x60 0x50 0x50)) 15 (by decide) (UInt64.ofBytes 0x4 0x60 0xf1 0x3 0x61 0x5b 0xf3 0x90)) 16 (by decide) (UInt64.ofBytes 0x15 0x10 0x81 0x40 0x60 0x3 0x36 0x80))

private def absorbed007 : Vector UInt64 25 :=
  #v[0x4e2207e1be6a986c, 0x4a98f385c467c50, 0xeff175584448def4, 0x2a9847c9898839e3, 0x6e738aebf1890cd1, 0xe064eb1633a4e033, 0x378470d3112245aa, 0xeabad3e47bd65d58, 0x99acde43a3d9df85, 0x1e4dcb61b21ab1f1, 0x11247deed2c281e1, 0x544b364f3f7c7ced, 0xb9ab6c36cc1add6c, 0xf30347916c96a195, 0x323ff2a67c1ac8b9, 0x538fae86599daac4, 0xd40cde819a5917d2, 0x2a3d6e0db34388cf, 0xf1ee64ae3c17c6b8, 0x7e41904ec7800019, 0xf1492f8425519470, 0xf544c9b1683dc666, 0x71828884d8102101, 0xb2993f9efac6752a, 0x1d942aa71d1b5a0a]

private theorem words007 : absorb007 state007 = absorbed007 := by
  decide +kernel

private def quarter007_1 : Vector UInt64 25 :=
  #v[0x64bd64bb131fbe2e, 0x24ca0b08941d12ba, 0xc7cc8c45e0cc921, 0x6daa3b25eaf98dfe, 0x13ffa15c3aaf17e1, 0x2aa00e79d84b3a16, 0x54ef84544a898e99, 0x95a6ccbdb8fbe473, 0x3ae1ebfbcce09519, 0xc86067b236319738, 0x3f9ade91bec576cb, 0xea0f38138fa66e49, 0xfbe4d31bb8d48ae6, 0x2004c80a6a765154, 0x68e4d7413775491, 0x26ef34efad936cd2, 0x1a49b28423baf173, 0x7a4e71b5ffa1e368, 0x3c217adb90b1c4d4, 0x76894e6133a01d84, 0x3b66e3e51bb1bbd3, 0x2b9121f8500198df, 0x2462bc33d226973, 0x8919a2a6aab3558f, 0x4c5395601e75587c]

private theorem rounds007_0 : sixRounds 0 (by decide) absorbed007 = quarter007_1 := by
  decide +kernel

private def quarter007_2 : Vector UInt64 25 :=
  #v[0xd6659ea2b3873f8d, 0xf4395ba45c7c9e0e, 0x965b5befc5a1fd0a, 0x951d349eaa63ee37, 0x5bf8f4a5cf657369, 0x61cf62687b8802ee, 0x8c421d3e143b9a6, 0x446260359dadaeba, 0x5a20a424f4ed9dd0, 0xdde3bbbc0054939d, 0x462d5bef4240c99c, 0x597839c3b42593ca, 0x7999abf5b566829f, 0x92b690b671b0017c, 0x9d28a655310be7b2, 0xf8a2e0397cce89b8, 0xfd5df24657e62247, 0x18a56333728615de, 0x4f1a5328364b6e0a, 0xd3b104088f74d386, 0xae586b1a2f1a10e9, 0x22bdc81f32d961ee, 0x6f8bdfccb18b1200, 0x99a472f835a97e72, 0x40f2c12bb3233b8d]

private theorem rounds007_1 : sixRounds 6 (by decide) quarter007_1 = quarter007_2 := by
  decide +kernel

private def quarter007_3 : Vector UInt64 25 :=
  #v[0xf972c62b07db11f9, 0xe7357eb76a1e1abd, 0xae87c9b1e8710061, 0x22016b44ddb0c768, 0x80f391cfe14aeb2f, 0x638e8d0bcb584b90, 0x61ad73056e192903, 0xb56d1bd253605455, 0x36ce972f7c8a8999, 0x7357b44f78d14130, 0x5ddf2dc750930fd9, 0xbb71b9c208c5c208, 0x46aaf6a92f9e63f8, 0xe54d7bb1999975dd, 0x6c0cf5ecef7a1eb3, 0x9d88f2e07589bae8, 0x708d67aa125291ac, 0x157a54a626fd6519, 0x474743eebde3b085, 0x1d7c0296fb136c63, 0x2d2335903536476b, 0xd7500eb01b8483b8, 0xdd6bb6c12de079f2, 0x9579ba6f952dc438, 0xa65285d663f35427]

private theorem rounds007_2 : sixRounds 12 (by decide) quarter007_2 = quarter007_3 := by
  decide +kernel

private theorem rounds007_3 : sixRounds 18 (by decide) quarter007_3 = state008 := by
  decide +kernel

private theorem perm007 : KECCAK.f1600 absorbed007 = state008 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds007_0, rounds007_1, rounds007_2, rounds007_3]
  rfl

theorem block007 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes007 ++ tail) state007 =
      KECCAK.Bytes.run 0 tail state008 := by
  exact run_block_of_step bytes007 tail absorb007 state007 absorbed007
    state008 (fun _ => rfl) words007 perm007

private def absorb008 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xfd 0x80 0x0 0x60 0x57 0xce 0x3 0x61)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x50 0x5b)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x81 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x61 0x35 0x1 0x20 0x60 0x90 0x16 0x35)) 5 (by decide) (UInt64.ofBytes 0x51 0x80 0x40 0x60 0x5b 0x56 0x72 0xe)) 6 (by decide) (UInt64.ofBytes 0x81 0x90 0x51 0x52 0x82 0x15 0x15 0x91)) 7 (by decide) (UInt64.ofBytes 0x5b 0xf3 0x90 0x1 0x20 0x60 0x3 0x90)) 8 (by decide) (UInt64.ofBytes 0x5b 0x56 0xff 0xf 0x61 0xd 0x4 0x61)) 9 (by decide) (UInt64.ofBytes 0x51 0x52 0x82 0x91 0x51 0x80 0x40 0x60)) 10 (by decide) (UInt64.ofBytes 0x90 0x1 0x20 0x60 0x3 0x90 0x81 0x90)) 11 (by decide) (UInt64.ofBytes 0x80 0x4 0x60 0x52 0x4 0x61 0x5b 0xf3)) 12 (by decide) (UInt64.ofBytes 0x61 0x15 0x10 0x81 0x20 0x60 0x3 0x36)) 13 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x80 0x0 0x60 0x57 0x35 0x4)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x35 0x50)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed008 : Vector UInt64 25 :=
  #v[0xea5b3cd79fd5c6c7, 0x63ca36ec961e70dc, 0xa58b547c8f8d7f58, 0x4a5e0f3507220dae, 0xf2471597de2b627b, 0x83a2db189de1d070, 0x6126f08ad19b8f61, 0x85e99054f7b2b43c, 0x6d993711970ee882, 0xcdb527198730b472, 0x3d9011d86532fe8d, 0xad8d235a6acaf8b6, 0x56b8dd1d1a5028a5, 0x42e4ae1c4885a267, 0xf0ef5835a91e200d, 0x3b6e0d26c000bf40, 0x9f177d2d5db54e6f, 0x5a686d4c40cce693, 0x1d4232a4524845d6, 0x86530162e5136b49, 0x41867891977670f9, 0x9d216191a2e5c32e, 0x34348a3f2365a28c, 0x73ed8f104ee942c, 0x5fbc1959e3ba8926]

private theorem words008 : absorb008 state008 = absorbed008 := by
  decide +kernel

private def quarter008_1 : Vector UInt64 25 :=
  #v[0x5f49864ed7af74d3, 0x281580e5b0af838e, 0x280b32b5c6c1edbc, 0x82cbac352ea70ac4, 0xe1017227573ffcf5, 0xe797c73a9bca7856, 0x4dcdd06514e48798, 0x9b90b69b4e7a1977, 0x69da039b1ae6b6f8, 0x738336453bef89b, 0xa33e252b86ad28c5, 0x3e0d8f0ee9890edc, 0x9333af2cc563754b, 0x4da616c9741576de, 0x88f5bca6635d0c32, 0x68a65868ece57fa, 0xe00c52311825758c, 0xa2ad7cda23b5dd04, 0x10ed181daf0b35b6, 0x897d6677ae3fe8, 0xf756c25eaa4a2fa5, 0x4e3cc617276b885d, 0xe962751caf03c1e8, 0x4f4b80a6c81c5bc3, 0xcebb95f3688358fb]

private theorem rounds008_0 : sixRounds 0 (by decide) absorbed008 = quarter008_1 := by
  decide +kernel

private def quarter008_2 : Vector UInt64 25 :=
  #v[0xe88e0c356243c45d, 0x33340ecb2c1b4c87, 0x392dfb57a2a50326, 0xf0f354d18998899f, 0x6e105a3a369335dc, 0x80a2b957d10d9638, 0x3c8cbff8631d8962, 0x53e74f2665a98e4b, 0xa83c199f70cd9ab6, 0xb2685e5d852fde70, 0xce0a9988fe02238, 0x6cdbe6cafac1533a, 0x2e9b035462dd6f8f, 0x63f4dcc91e5ce291, 0x299d4212af8cc26b, 0xaf63cdfcdf5d749a, 0xfe41ac39cc9706bf, 0x2cb5a86a844bea3d, 0x192bc0d2fdd2a1b2, 0x565dbaf0522686b6, 0xab13eae3a563e7fa, 0xcc2c6f7e8306bdb5, 0x669e9316e80352a9, 0xafbac902a8965ad9, 0xdf26711851cef9f1]

private theorem rounds008_1 : sixRounds 6 (by decide) quarter008_1 = quarter008_2 := by
  decide +kernel

private def quarter008_3 : Vector UInt64 25 :=
  #v[0xcf92775acdac9444, 0x259f1ef757c679f9, 0xaffbb634788c89de, 0xa0d876256c36526a, 0x9eabdf51664b7db6, 0x65d5723fa0e43c4b, 0x4f7eb8241a36524, 0xd430fb0474b2aff0, 0x6c207c66ccafdf11, 0x42595c3ef3d41d1, 0x37dd97396aa16353, 0xce3452c9b2a2561, 0x3a4bd1e10e455d86, 0x82c0252114d8cb17, 0xbc9a1f6530015a26, 0x31bc52cab62ba580, 0xd726fcea534669e4, 0xc00cfd1b89e882cb, 0x63d274004ef80225, 0x639bda22ac2607ce, 0x26b00112bf1c55b5, 0x9d8a5b1472e7d675, 0xf04d099873ca301c, 0x63c1965908224c58, 0x81f1043f5d42d84b]

private theorem rounds008_2 : sixRounds 12 (by decide) quarter008_2 = quarter008_3 := by
  decide +kernel

private theorem rounds008_3 : sixRounds 18 (by decide) quarter008_3 = state009 := by
  decide +kernel

private theorem perm008 : KECCAK.f1600 absorbed008 = state009 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds008_0, rounds008_1, rounds008_2, rounds008_3]
  rfl

theorem block008 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes008 ++ tail) state008 =
      KECCAK.Bytes.run 0 tail state009 := by
  exact run_block_of_step bytes008 tail absorb008 state008 absorbed008
    state009 (fun _ => rfl) words008 perm008

private def absorb009 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x61 0x5b 0x0 0x5b 0x56 0x5 0x10 0x61)) 1 (by decide) (UInt64.ofBytes 0x60 0x3 0x36 0x80 0x4 0x60 0xf1 0x3)) 2 (by decide) (UInt64.ofBytes 0x57 0x6a 0x4 0x61 0x15 0x10 0x81 0x60)) 3 (by decide) (UInt64.ofBytes 0xff 0x73 0x50 0x5b 0xfd 0x80 0x0 0x60)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x91 0x16 0x81 0x35 0x81 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x16 0x91 0x90 0x35 0x1 0x81 0x20 0x60)) 8 (by decide) (UInt64.ofBytes 0xe9 0x10 0x61 0x35 0x1 0x40 0x60 0x90)) 9 (by decide) (UInt64.ofBytes 0x80 0x4 0x60 0x52 0x4 0x61 0x5b 0x56)) 10 (by decide) (UInt64.ofBytes 0x61 0x15 0x10 0x81 0x20 0x60 0x3 0x36)) 11 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x80 0x0 0x60 0x57 0xad 0x4)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x35 0x50)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x52 0x4 0x61 0x5b 0x56 0xef 0x13 0x61)) 16 (by decide) (UInt64.ofBytes 0x81 0x20 0x60 0x3 0x36 0x80 0x4 0x60))

private def absorbed009 : Vector UInt64 25 :=
  #v[0xb70f4e0eccd5f5e0, 0xc79375f4de7a46f4, 0x89d9240cbcbdfc4d, 0xa915609216a16d6, 0xf4a52e11f83b41f1, 0x7a264594bf8b090c, 0x8a153d919ff09acf, 0x13a4b510514d87ee, 0x89761f5720184d7b, 0x10192242a390c7f8, 0xf34fcf6f3463d214, 0x10e81bec0ac35198, 0x52066474924ed0f6, 0x3af74a9842aa1bf6, 0xd292fb635fddb76, 0xd4edeed79f6eb7ca, 0x26ca2bc1cf247d3c, 0x83787a60c09459a0, 0xf578d528966fb669, 0xbcfeffb0e6444b0d, 0xb16afd95ce87157a, 0x434f17c3c20dbdd7, 0x7939425f99e93ad7, 0xaf06afcfbc192f7c, 0xc7b08234e675331c]

private theorem words009 : absorb009 state009 = absorbed009 := by
  decide +kernel

private def quarter009_1 : Vector UInt64 25 :=
  #v[0x13550d402440dcd2, 0xd317e9df5335df08, 0xa19d37606a798091, 0x252faff14ba64849, 0x56284d245d2153c1, 0x7f20713bd2e9971e, 0x735ee15b1cf6f24e, 0x6457ffb1d22876d9, 0xc11c42fc833a01c9, 0xfdc5616335119639, 0xf9c9fb61a2babe2a, 0xdeaffde02d6ef718, 0x9cc0f6fbec0ba5ac, 0x49e6e58fe071d5d7, 0x156e5692e3e464af, 0x8ea9af8373f813d1, 0x6455fa408309a6d1, 0x2b0378fa2015ed11, 0x41aa766e6220574b, 0x9ff1c7ce443321ec, 0x5f474d5a70469b0f, 0x39231ac40f8d0b3b, 0x9bd35100c5896284, 0x1cc1e2d1e5fcba, 0x7d7a976d32535e61]

private theorem rounds009_0 : sixRounds 0 (by decide) absorbed009 = quarter009_1 := by
  decide +kernel

private def quarter009_2 : Vector UInt64 25 :=
  #v[0x7bcd28cd30611878, 0x8ad6435957f5db4b, 0x2feb5c6a8a43f028, 0xea36403e2188beac, 0x9f2d734976ab33a7, 0x6848d06511d1e2d9, 0x79b56f12dbccfb3a, 0x355f2e3b09e9b6b6, 0xab7f2b2a6dbcccdb, 0xf83d378646c535aa, 0x2f0ef87af6c46c37, 0x3d3efa1e943f7f08, 0x9906b0494ec9c5de, 0xc4fd72481bfb631d, 0xe617b615434e9367, 0xb0e7fcd09459a341, 0xab3ee39223df9edf, 0x4cfab0eac52a1330, 0xd7d3ab31490ee4fe, 0x5f347cfda502d354, 0x5c9f82ac3f30d2dd, 0xa2a397b76f778854, 0x3ee33c9a0eeccbfd, 0xd48b9a04fa900019, 0xf483a118bc568f3a]

private theorem rounds009_1 : sixRounds 6 (by decide) quarter009_1 = quarter009_2 := by
  decide +kernel

private def quarter009_3 : Vector UInt64 25 :=
  #v[0x8d5f45954d76cf35, 0xce78942662b38317, 0x2f85d113caf696c9, 0xe495b3e17a501303, 0x9ef9d397b849a08, 0xc846203f3c0f66ac, 0x5cce4613f725bede, 0xd00bff0de2b61267, 0x58b98e3b0326c5c7, 0x82169209b4a03646, 0x25017c81f48194d5, 0x76381d3ed1ee1cf0, 0x730f83e1b093fd24, 0x2b39674b5004cee7, 0xdd1571e915fe9d67, 0x5b538c0696e496b8, 0x58c86af2a875b306, 0xb660f8c0d23acbf7, 0x33ad63f5a6f76bc7, 0x88f974b8e852b1e0, 0x6a263966df78d58c, 0x46e38a6cced31985, 0xe3857e157616ff1a, 0x1160978c7d828a06, 0x6ebb0a30e05e9d6e]

private theorem rounds009_2 : sixRounds 12 (by decide) quarter009_2 = quarter009_3 := by
  decide +kernel

private theorem rounds009_3 : sixRounds 18 (by decide) quarter009_3 = state010 := by
  decide +kernel

private theorem perm009 : KECCAK.f1600 absorbed009 = state010 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds009_0, rounds009_1, rounds009_2, rounds009_3]
  rfl

theorem block009 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes009 ++ tail) state009 =
      KECCAK.Bytes.run 0 tail state010 := by
  exact run_block_of_step bytes009 tail absorb009 state009 absorbed009
    state010 (fun _ => rfl) words009 perm009

private def absorb010 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x60 0x57 0xe0 0x4 0x61 0x15 0x10)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x35 0x50 0x5b 0xfd 0x80)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x5b 0x56 0x50 0x15 0x61 0x16 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x3 0x36 0x80 0x4 0x60 0xf1 0x3 0x61)) 6 (by decide) (UInt64.ofBytes 0x13 0x5 0x61 0x15 0x10 0x81 0x20 0x60)) 7 (by decide) (UInt64.ofBytes 0x35 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x15 0x61 0x16 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x16 0x61 0xd 0x4 0x61 0x5b 0x56 0xce)) 12 (by decide) (UInt64.ofBytes 0x16 0x61 0x40 0x5 0x61 0x5b 0x56 0xc7)) 13 (by decide) (UInt64.ofBytes 0x60 0x51 0x80 0x40 0x60 0x5b 0x56 0xeb)) 14 (by decide) (UInt64.ofBytes 0x90 0x51 0x52 0x82 0x16 0x92 0x90 0xff)) 15 (by decide) (UInt64.ofBytes 0xf3 0x90 0x1 0x20 0x60 0x3 0x90 0x81)) 16 (by decide) (UInt64.ofBytes 0x36 0x80 0x4 0x60 0x52 0x4 0x61 0x5b))

private def absorbed010 : Vector UInt64 25 :=
  #v[0x8d0967429f0ad7ef, 0xeb9835f72161c328, 0xb57b3b7f9b866791, 0x4857feb9e867f7eb, 0xb426126acef90982, 0x56706b9f86f1c420, 0xc238f7bb1a4b4824, 0xc63700f5540e0fbe, 0x54368beb5ba072a3, 0xf96b432be38ed567, 0x5424907acbce4d48, 0x1bedf9639c3f701d, 0xfd49fa91d2f07328, 0x9718776d266e25b7, 0x96a0b01e4be7609d, 0x4c45298737924ba5, 0x89da21238c3725b6, 0x7f82c73d4a96617e, 0x58c2766413f83a31, 0x8bb5b7d4e2f878ef, 0xcc2952d2d61b38e9, 0x29f464c3d0b5d3b4, 0x9abdee76e5ae140c, 0x72ce4d7319505947, 0xa8147f08da9d70c5]

private theorem words010 : absorb010 state010 = absorbed010 := by
  decide +kernel

private def quarter010_1 : Vector UInt64 25 :=
  #v[0x47120f690a6c6443, 0xf2a2d815377db8b4, 0xd3d11777dcc8b2da, 0x827132cbd87bea25, 0x413f316470c395f3, 0x2d5432abcf265647, 0xf894c2c12f7fb2b8, 0x54cbb793e6c2b263, 0x455b622ade9bb4fc, 0x2fc373318e5fe44c, 0x48ca03b7544b1f6c, 0x20a8e35f3b1260d2, 0x6ac7493637579116, 0x389fa8ab40dd7515, 0x99fb9dc094713434, 0xc6a32c6acc1c263b, 0x1c31319b7cb29368, 0xef7efe50f4604258, 0x8cf988bbc4b93898, 0x8eafbb29461e1632, 0xd7167ec5077c742a, 0x938d93412656150e, 0xc97fb7cc1429896c, 0x4414f8cff9fd02b3, 0x84beed6f09482c4d]

private theorem rounds010_0 : sixRounds 0 (by decide) absorbed010 = quarter010_1 := by
  decide +kernel

private def quarter010_2 : Vector UInt64 25 :=
  #v[0x765e191a801ece3, 0xa1e66b8b8c72d5bc, 0x8d827685f482c9ed, 0x57d8902c26ad041e, 0x22dc8bbde1d276ef, 0xf4ca1c15836ec085, 0x6a1509fa78b03f55, 0xf5d166e4384a03c1, 0xd20190f7fbf62979, 0x4e9d8429600be666, 0x5364cbfb586d725e, 0x5c9fcd30c931943c, 0x2e8eefeb82d5b73e, 0x5df59a78a579400, 0xe826497bd280b95f, 0x5085385c9555223b, 0xda2299a36184d70f, 0xc2b46bc6d14f578c, 0x7820e9785e56b160, 0x61513965bc0d9bab, 0xfab94f2057b8c35f, 0xde35fc36d1641071, 0x53827f8c79340fa7, 0xc5a83ac8ad9f8fc9, 0x92c108ee62b81cb5]

private theorem rounds010_1 : sixRounds 6 (by decide) quarter010_1 = quarter010_2 := by
  decide +kernel

private def quarter010_3 : Vector UInt64 25 :=
  #v[0x58d616d4c977ff0e, 0x6daa0556af6fc2cc, 0x7d447fa255d3c4d9, 0xc30d097e9be1ebef, 0x8a1f18616a2cab0c, 0xed976f7a36fdc401, 0xbc4c2d27d8ab2d55, 0x3815956efcf03549, 0xd2e5d247dadc3cb8, 0xe099f440ff217563, 0xcc72a85c6139f1da, 0x573e655d3c7520d5, 0xff9caeab55cde1c2, 0x679449a423f2a24b, 0x78babae03f3d8ddb, 0x8abc716a85ea5ffa, 0x6ea7f22a74ffb58e, 0x1c0a09bd988c515, 0xd64ee22426d2dee1, 0x1386f4f3d1bbaa90, 0xd700b17d77c9213, 0x23e2bc70c1ec2a62, 0x8796a682f160d7a0, 0x829ef1e0bac7668a, 0xe9109a1dccce27c8]

private theorem rounds010_2 : sixRounds 12 (by decide) quarter010_2 = quarter010_3 := by
  decide +kernel

private theorem rounds010_3 : sixRounds 18 (by decide) quarter010_3 = state011 := by
  decide +kernel

private theorem perm010 : KECCAK.f1600 absorbed010 = state011 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds010_0, rounds010_1, rounds010_2, rounds010_3]
  rfl

theorem block010 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes010 ++ tail) state010 =
      KECCAK.Bytes.run 0 tail state011 := by
  exact run_block_of_step bytes010 tail absorb010 state010 absorbed010
    state011 (fun _ => rfl) words010 perm010

private def absorb011 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x61 0x15 0x10 0x81 0x0 0x1 0x61 0x3)) 1 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x80 0x0 0x60 0x57 0x6d 0x5)) 2 (by decide) (UInt64.ofBytes 0x81 0x1 0x81 0x20 0x60 0x90 0x1 0x81)) 3 (by decide) (UInt64.ofBytes 0x81 0x0 0x0 0x0 0x0 0x1 0x64 0x35)) 4 (by decide) (UInt64.ofBytes 0x0 0x60 0x57 0x88 0x5 0x61 0x15 0x11)) 5 (by decide) (UInt64.ofBytes 0x20 0x60 0x83 0x1 0x82 0x5b 0xfd 0x80)) 6 (by decide) (UInt64.ofBytes 0x57 0x9a 0x5 0x61 0x15 0x11 0x1 0x82)) 7 (by decide) (UInt64.ofBytes 0x90 0x35 0x80 0x5b 0xfd 0x80 0x0 0x60)) 8 (by decide) (UInt64.ofBytes 0x83 0x1 0x60 0x84 0x91 0x1 0x20 0x60)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x1 0x64 0x11 0x1 0x84 0x2)) 10 (by decide) (UInt64.ofBytes 0x5 0x61 0x15 0x17 0x11 0x83 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x91 0x5b 0xfd 0x80 0x0 0x60 0x57 0xbc)) 12 (by decide) (UInt64.ofBytes 0x20 0x60 0x1 0x1f 0x60 0x80 0x80 0x90)) 13 (by decide) (UInt64.ofBytes 0x60 0x1 0x20 0x60 0x2 0x4 0x91 0x80)) 14 (by decide) (UInt64.ofBytes 0x52 0x40 0x60 0x1 0x81 0x90 0x51 0x40)) 15 (by decide) (UInt64.ofBytes 0x52 0x81 0x81 0x90 0x91 0x92 0x93 0x80)) 16 (by decide) (UInt64.ofBytes 0x84 0x82 0x80 0x83 0x83 0x1 0x20 0x60))

private def absorbed011 : Vector UInt64 25 :=
  #v[0x3d675ca445cb2573, 0x640c764caadd7e0, 0xc6fe8c15a294fe18, 0x8e7a2e00e49a60d, 0xe8bd6318b1742bb9, 0x76d9ad01fc7ff93e, 0xd4e33476b5086c17, 0xfb3d8b3c6922f994, 0xde4da5281db3828a, 0x3ded83d6a07543d9, 0xa2e35731c9074196, 0x5f43621c07c23687, 0xb14c4fc2dc287c86, 0x31dd19ae01d0abe1, 0x37fff3978acb4c71, 0x5d3eec77bb951ca7, 0x881360bc92ee01df, 0xb26882ebb1925340, 0xe34fb199ff9c5c2d, 0xfcbadd129754d2f1, 0x2ca120e8eeb68796, 0x13a3d10780c478d8, 0x8cf85e67e94b582e, 0x4013fdbf55de2c74, 0x937395e11398e279]

private theorem words011 : absorb011 state011 = absorbed011 := by
  decide +kernel

private def quarter011_1 : Vector UInt64 25 :=
  #v[0x29cd2605e8b5d30c, 0x85927c00d2d44f1a, 0xad382c6f4495e33a, 0x6bbd7b26e37649b2, 0xe771da39fe2b04d7, 0xd90f19707c5ce6d1, 0xa26a1efd97bb6f57, 0x17740b8976f5c1b5, 0x15f87c6e221eeab8, 0xb695b9bf01914e86, 0xb933243e04e46456, 0xcaf069215221a4f, 0x30c7ac7453c4389e, 0x6061c57c2748c9bd, 0x53bac2a194ba5a1a, 0xabecd761a6951e86, 0x7831ca9157f555bb, 0xddf5627a9f317fb2, 0x72a4fc1dcb4cb2de, 0xcd8f278b19c3d3c6, 0x7b0cc2ee8ced8ae5, 0xc445a33e0722cf, 0x90b8d9f9d396105b, 0x75c80c124ac98c85, 0x562a3b5ce4d543eb]

private theorem rounds011_0 : sixRounds 0 (by decide) absorbed011 = quarter011_1 := by
  decide +kernel

private def quarter011_2 : Vector UInt64 25 :=
  #v[0xc6a956389c0e8ea6, 0xe3fdf42bed9666c8, 0xb871f01403116c2f, 0x6d644df23c3b09e3, 0xd1408fea644c95a5, 0x66ec5617cb22fff5, 0xf8fa554bd3579ab0, 0x253bcb171841f310, 0x14322d3dfaeead35, 0x5d549b0121a1f81a, 0x9f651165b539da24, 0x76c99d87da272f81, 0xc4d21d4552149f1f, 0x2be57287c46dce3, 0xaaf505aad0f7758d, 0xb8eb5030e9d8a577, 0xc09ca8bf51a8f54b, 0x8a688d773ae3c2ed, 0x2ddb7309dcc75b1, 0x7e62eb3f75a5c6cf, 0x8f8b8681bce8731d, 0x990a70190af928b2, 0xfc9e633455797a16, 0x169ef9f79ab18848, 0x8d9f40edddcb58ea]

private theorem rounds011_1 : sixRounds 6 (by decide) quarter011_1 = quarter011_2 := by
  decide +kernel

private def quarter011_3 : Vector UInt64 25 :=
  #v[0xad81ca1df28dee89, 0x77cf10aac6930797, 0x9073dbc89629f46, 0x3ae6c27ee4f5087b, 0x8f3fada1291fad13, 0xfc0d0257e6b6d375, 0x66ddb51d2d7e45b4, 0xe70d346a908083ae, 0xe3b38cf42725c151, 0xecdf925b0e63390b, 0x3de17a845fbbc17f, 0x7129ca27ed34ffbb, 0x250dcbf1fae5b302, 0xed53ae008e8c41bb, 0x940be9026b9970a6, 0xa5f07d190ed331a7, 0x9407ff3b55dd07f2, 0x8b589691da43621e, 0xf658c9d34ac326c7, 0xdfada278bd355667, 0x1bd0b328643aef52, 0x6a48f5c3f3b70ca9, 0x80b443b3fc21e16b, 0x3469778572eea6b6, 0x6bdfd31e0ca33c1f]

private theorem rounds011_2 : sixRounds 12 (by decide) quarter011_2 = quarter011_3 := by
  decide +kernel

private theorem rounds011_3 : sixRounds 18 (by decide) quarter011_3 = state012 := by
  decide +kernel

private theorem perm011 : KECCAK.f1600 absorbed011 = state012 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds011_0, rounds011_1, rounds011_2, rounds011_3]
  rfl

theorem block011 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes011 ++ tail) state011 =
      KECCAK.Bytes.run 0 tail state012 := by
  exact run_block_of_step bytes011 tail absorb011 state011 absorbed011
    state012 (fun _ => rfl) words011 perm011

end Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
