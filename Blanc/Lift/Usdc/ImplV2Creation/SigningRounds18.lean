import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb108 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x90 0x3 0x91 0x80 0x51 0x40)) 1 (by decide) (UInt64.ofBytes 0x8b 0x8b 0x8b 0x8b 0x8b 0xd0 0x31 0x61)) 2 (by decide) (UInt64.ofBytes 0x56 0x76 0x49 0x61 0x8b 0x8b 0x8b 0x8b)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x1 0x74 0x54 0x1 0x60 0x5b)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x15 0x16 0xff 0x60 0x4 0x90 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x51 0x80 0x40 0x60 0x57 0x88 0x39 0x61)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8 0x7f)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x82 0x4 0x60 0x20 0x60 0x52 0x81 0x0)) 13 (by decide) (UInt64.ofBytes 0x1 0x82 0x24 0x60 0x10 0x60 0x52 0x1)) 14 (by decide) (UInt64.ofBytes 0x62 0x61 0x73 0x75 0x61 0x50 0x7f 0x52)) 15 (by decide) (UInt64.ofBytes 0x73 0x75 0x61 0x70 0x20 0x3a 0x65 0x6c)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x64 0x65))

private def absorbed108 : Vector UInt64 25 :=
  #v[0x77d7bed6ef3f2cc6, 0xa36affe03eca77b5, 0xb3f91880c5bd7ee6, 0xcdb7b60a9ebc23a7, 0x9e8ff928aec61589, 0x976ca9651dd5b1c1, 0x48a8d1ae227b2059, 0xe3abd72af67df846, 0x8068955bdfb1eba1, 0xfa019782368b0da4, 0xe6a53649bc58bba1, 0x84ed6931c9155c10, 0x4e37c8cd0a4476a4, 0x655c9160949404a1, 0xa9f6002cb0eecdfe, 0x9b3f6b1c4c1b74aa, 0x95cba847713fd6c1, 0xcfed72649e32b9c3, 0x2b1302d043b576d0, 0xb41b63859ce4e9e, 0x830e92192536cdc, 0xf35dce8a516741a6, 0xa724d3e38c0b2f18, 0xfd4fdb4cf56fcc4d, 0xc1c8cfdb4fe2427b]

private theorem words108 : absorb108 state108 = absorbed108 := by
  decide +kernel

private def quarter108_1 : Vector UInt64 25 :=
  #v[0xfc6f1172142d82bd, 0x95b332c732ec3705, 0x3dd09c9c539027d, 0x243cb1f82781a34, 0x1e5101b0e349801d, 0x2d881725b7a09e2b, 0x3aae825b1c97e2db, 0xa98f85fc3e700194, 0x22af3e746e55b2da, 0xae1e96a4404e56d, 0xbd6edf103f69d106, 0x167d404729af8394, 0x204ab984eac13726, 0xff51a6d80a14c574, 0x6205574b405907de, 0x805c61e10ddce070, 0x90d3699b8cbb7798, 0xb8f9acc17eac58c5, 0x78bdb8a40ff0523b, 0x223c9c8d9b9391f8, 0x12928261f2450f19, 0x2070be4fdea3a1b4, 0xfa1b141fd10049fe, 0xa8d3889f53251d6f, 0x3445a14149b189de]

private theorem rounds108_0 : sixRounds 0 (by decide) absorbed108 = quarter108_1 := by
  decide +kernel

private def quarter108_2 : Vector UInt64 25 :=
  #v[0x9291ba0627d19c9f, 0xdef1fd7f0a7e0eed, 0x581525b44e5c9883, 0x9bff9f98b7feda0c, 0xa5646eaba4a3d3f0, 0xe3b4365321253d72, 0xe03fefb9d0f10799, 0xcf0e5575f8383382, 0x2c3e8c8147657abc, 0x2fd09c8d610f26dd, 0x37b3930b927c3f86, 0xf88166e4d4385521, 0x5deab6ba7f7ba4dc, 0xe6c202e1a825de6e, 0x627dc9b6fdba4bb7, 0xdf540fea9ae6e8c9, 0x5cdf4638bab147ae, 0xaccc1d6da226c936, 0x8abcca1fdd2b713, 0x2d59cd04a9a868cb, 0xe13e2c1310701429, 0xf8fdd355db74c058, 0x347bb48cbb021bc4, 0xd0c007d1756b201a, 0x1714b9a464319ab3]

private theorem rounds108_1 : sixRounds 6 (by decide) quarter108_1 = quarter108_2 := by
  decide +kernel

private def quarter108_3 : Vector UInt64 25 :=
  #v[0xf71236df48c5f24f, 0xefad0fbffe214175, 0x40d496d7cacbc4b1, 0x473b0e1becfc5ae0, 0xbd8017a70a5b6fe3, 0xb202bb40a5871176, 0x78b7c37ec88479b0, 0x6817b28d85a2522c, 0xfbe6ada2a8833cf0, 0x61aa67e5b8b1529, 0xabecdd52ffdb39d2, 0x183d786ba883df78, 0x31a74c6889827799, 0x3fc9b5ba0524c143, 0x82c5fb243f7f544e, 0xfe42912842d81ef8, 0x984c778a42640bfe, 0xed01be35f4a31933, 0xb7a3bb7133f64c5, 0xd8df28c46fde0eb7, 0x543e3b32c79893d4, 0x75732e161c43eb8, 0x718a6778e37e5710, 0xd86b61d32b0fcf8a, 0x593b68c0d211a6da]

private theorem rounds108_2 : sixRounds 12 (by decide) quarter108_2 = quarter108_3 := by
  decide +kernel

private theorem rounds108_3 : sixRounds 18 (by decide) quarter108_3 = state109 := by
  decide +kernel

private theorem perm108 : KECCAK.f1600 absorbed108 = state109 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds108_0, rounds108_1, rounds108_2, rounds108_3]
  rfl

theorem block108 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes108 ++ tail) state108 =
      KECCAK.Bytes.run 0 tail state109 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes108 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb108 ws)) := by
    rfl
  exact (step state108).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words108).trans perm108))

private def absorb109 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x90 0x52 0x1 0x82 0x44 0x60 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x1 0x64 0x60 0x3 0x90 0x81 0x90 0x51)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x5b 0xfd 0x90)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x90 0x0 0x60 0x16 0x89)) 7 (by decide) (UInt64.ofBytes 0x20 0x90 0x40 0x60 0x52 0x20 0x60 0x3)) 8 (by decide) (UInt64.ofBytes 0x61 0x15 0x16 0xff 0x60 0x90 0x89 0x54)) 9 (by decide) (UInt64.ofBytes 0x8 0x7f 0x51 0x40 0x60 0x57 0x9 0x3a)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x81 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x20 0x60 0x80 0x80 0x1 0x4 0x60 0x52)) 15 (by decide) (UInt64.ofBytes 0x25 0x60 0x52 0x82 0x3 0x81 0x82 0x1)) 16 (by decide) (UInt64.ofBytes 0x59 0x61 0x80 0x1 0x20 0x60 0x52 0x81))

private def absorbed109 : Vector UInt64 25 :=
  #v[0xd68999ea8df6d1b1, 0x9eea9c36913d7796, 0x17fa7e122b848579, 0x65080842d699b377, 0x78ba580326043bf4, 0xe61611a0c314f9b3, 0x270f42acedab39da, 0x4b0211ccf535053a, 0x6d4ef1527f5135cb, 0xa57847c66dba6dbf, 0xfbd40725d691a2d8, 0x8ed01281781b5d5a, 0x750b5088451a3b53, 0x81b44d2a9132ceac, 0xbfdfdcd4059e1787, 0x88d0f94ff03dbffa, 0x63009530348643c6, 0x7f38f56091acbb52, 0xa7574ef4c4c7289f, 0xcd523af2bea4691b, 0x7e6c37b5db346b33, 0xa76489013eb7af21, 0x57f0cc4e0842875b, 0x38286057ade2b36a, 0xc1d1276fd2207177]

private theorem words109 : absorb109 state109 = absorbed109 := by
  decide +kernel

private def quarter109_1 : Vector UInt64 25 :=
  #v[0xb0ecb1f030c39261, 0x950542762e9aacf1, 0x7b0b80bc91a2cddf, 0xd2b888795ac89fc3, 0x20f92d7546a9131b, 0x252c8a25bc71c7ba, 0x34403633cd53b4d4, 0xd12c2a36f47ca9fb, 0xbbc3e9e5d37ef9fb, 0x373e3be5a47bd7b3, 0x87ad6e2b2ca16918, 0xf32d0de8e3566043, 0xf280d875c2e69d09, 0xf176d8334592dfff, 0x786695f5061ddea1, 0x9dc659692217da6e, 0x270d0d79b7680d78, 0x51f1d5d103066b9e, 0x9533f5c1b5b163fa, 0x99ef38ceebe2c1a6, 0x8229653beee106e3, 0xd9cbe16939d2a49c, 0xe43c2f6beef6a2fd, 0x531092900ac572d, 0xa309ffa8df8f57ba]

private theorem rounds109_0 : sixRounds 0 (by decide) absorbed109 = quarter109_1 := by
  decide +kernel

private def quarter109_2 : Vector UInt64 25 :=
  #v[0x86ef168967dcc901, 0x6d96f6ffd60a8fa9, 0x826b7b962f13688a, 0x40a3e76911c789c7, 0x4ccc9c77640d3c1c, 0x7dcc78cda6e3f098, 0x42bc3fc804076612, 0x917bea5664bba61a, 0x533b6a4312718345, 0x97c5c91e814d51d3, 0x1795414f753c056, 0xcd4c96150b57a8b0, 0x36ffdfaa8620a089, 0x9d03d3154924d8dc, 0x7675544022ef7972, 0x2706e500c24923d7, 0x4456a11e3b3216ca, 0x48ab43bf975e3cce, 0x50f1389777fbba78, 0x8d57615206ac0df6, 0xf4cb0e06d4772f09, 0x1bcef6f6f8d1d688, 0xe42ef613ae9b40c2, 0x9d78f8ee91b8d5e0, 0xd36f3b26d9ca9011]

private theorem rounds109_1 : sixRounds 6 (by decide) quarter109_1 = quarter109_2 := by
  decide +kernel

private def quarter109_3 : Vector UInt64 25 :=
  #v[0x6f091005e01edb12, 0x9484c227176cfc3a, 0x52b4d253cff23f0a, 0xd68ab2296cf97874, 0xd3e460fc678ebe6e, 0xf44a1db78c240e7a, 0x1457c1f4b9fb1580, 0xd480b278def7e9fb, 0x877c5e695288685c, 0x6560a030309f182d, 0x6981e11125875b0, 0x7460946ee787aa37, 0x85bb9ebc4a8d51c, 0xb26155ac7aeacbdb, 0xd2523013d4cdabb4, 0x4f801ee838d73de0, 0x9dc669878583b809, 0x7e71c939cd2940cb, 0x4b2fc96a7091d7b2, 0x48c711dfbe7ec9d0, 0x69cdf2e510be4576, 0x1478b83d8cd95239, 0xf08c88428bff890e, 0x4234e426a9b9b53c, 0x48a8569c3d94fe83]

private theorem rounds109_2 : sixRounds 12 (by decide) quarter109_2 = quarter109_3 := by
  decide +kernel

private theorem rounds109_3 : sixRounds 18 (by decide) quarter109_3 = state110 := by
  decide +kernel

private theorem perm109 : KECCAK.f1600 absorbed109 = state110 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds109_0, rounds109_1, rounds109_2, rounds109_3]
  rfl

theorem block109 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes109 ++ tail) state109 =
      KECCAK.Bytes.run 0 tail state110 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes109 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb109 ws)) := by
    rfl
  exact (step state109).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words109).trans perm109))

private def absorb110 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x1 0x40 0x60 0x39 0x91 0x25 0x60 0xc5)) 1 (by decide) (UInt64.ofBytes 0x91 0x80 0x51 0x40 0x60 0x50 0x50 0x91)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x5b 0xfd 0x90 0x3)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x52 0x81 0x90 0x0 0x60 0x16 0x89 0xff)) 6 (by decide) (UInt64.ofBytes 0x90 0x40 0x60 0x52 0x20 0x60 0x3 0x60)) 7 (by decide) (UInt64.ofBytes 0x15 0x16 0xff 0x60 0x90 0x89 0x54 0x20)) 8 (by decide) (UInt64.ofBytes 0x7f 0x51 0x40 0x60 0x57 0x8a 0x3a 0x61)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x60 0x80 0x80 0x1 0x4 0x60 0x52 0x81)) 14 (by decide) (UInt64.ofBytes 0x60 0x52 0x82 0x3 0x81 0x82 0x1 0x20)) 15 (by decide) (UInt64.ofBytes 0x61 0x80 0x1 0x20 0x60 0x52 0x81 0x25)) 16 (by decide) (UInt64.ofBytes 0x40 0x60 0x39 0x91 0x25 0x60 0xc5 0x59))

private def absorbed110 : Vector UInt64 25 :=
  #v[0xe3ffb89833b5babe, 0x5be17c8c29008322, 0x360669bbe217506b, 0xcc4dc81156342fc5, 0xb168ca2b4d56fa80, 0xc6aa2aef80e6448d, 0x4b7424ac805a2426, 0x608796c158077c67, 0x6a0afd9b98ce67a7, 0x8d46ac7e956ab52e, 0xaf5409ed94c7d102, 0x7363907e0724ffe0, 0x51cb9426ca711cf8, 0xc8170b588c85ab42, 0x8f2d6995cf70f7c1, 0x77c1b7dfddd56435, 0xf9f3b77619d57361, 0xc6bc6aecbc12650d, 0xe3c6236b4a6043a2, 0x4774adce19a1f748, 0xf5f3672388757d34, 0x5357a7c2d2015f33, 0xbf8886b278017e12, 0x26f28444eaa4640a, 0x5f974600de984bae]

private theorem words110 : absorb110 state110 = absorbed110 := by
  decide +kernel

private def quarter110_1 : Vector UInt64 25 :=
  #v[0x63dcd0e77cc4d715, 0xdb379c74accef047, 0x8e2e353e2cd0f2d8, 0xf0a3ed74935fb5af, 0xe249163dd20f8f12, 0x28eda744fe801b26, 0x9e796acb267abb7b, 0xd2a8135310a82d00, 0x82f89c956955a6c8, 0xf2bed0c3470adc40, 0x44f1863d31bd6758, 0x4493da8e36052e88, 0xbac16c4951f57475, 0x52c60c87de5da292, 0x5d21e80adb2aceb5, 0x341cb0d178183815, 0x4efbd1110af3b11f, 0xce00a3a5460f4f04, 0xf8877c95240350fd, 0xdea90d1ffb31b257, 0xe80bb66c8f0e88c0, 0xcb0eb9af05a6d261, 0xcabf5a3cd8cdf40c, 0x896be7bc5aa25236, 0xaad8db1bf8dc5a68]

private theorem rounds110_0 : sixRounds 0 (by decide) absorbed110 = quarter110_1 := by
  decide +kernel

private def quarter110_2 : Vector UInt64 25 :=
  #v[0xc71eb5e3a7c272d6, 0x8d0e7e327011720b, 0xf44504e7e1657a64, 0x43c89173e8420ccb, 0xfcd752ea9ee140d0, 0xa4741465b7c0fc17, 0xc449cf879872db33, 0x31402a8d0aab6da7, 0xb3744a2192b075fb, 0x2b5b9abe7d6900a9, 0x48224a72e10662c3, 0xc871f7c177de806e, 0x2bdbcbbff770f31c, 0xa212ce4fe0e5753d, 0x2382e4a749e3bfe4, 0xe08ce54f42e1a2a, 0xf3272eb4c7c69a5d, 0xd7186d1cbb8ed6b9, 0x2d0ad41a67bda002, 0x5e07e26699c2a5d2, 0xc61dba99e24a5ddc, 0xc75b4bdc6ce9e4cd, 0x9bced74d0b4cf7d, 0xa1c843112d8e3f0, 0x1e29bd2cc5f001ed]

private theorem rounds110_1 : sixRounds 6 (by decide) quarter110_1 = quarter110_2 := by
  decide +kernel

private def quarter110_3 : Vector UInt64 25 :=
  #v[0xeec59dd663b46a65, 0x2a75711be2d0831e, 0x54bee8c76078c659, 0x377c387797854dbb, 0x13b9efa001ba2068, 0x26802dbb75bbbc3e, 0x8061968c083678a8, 0x6f3846bb51b0a4a2, 0x4aff4acede3e5435, 0xb3fe5259e3a5d3e3, 0xbe8dd0d252e75aba, 0x396d2ce8c182f663, 0x34afd4583b533eeb, 0x7fd128bc54122c82, 0x14f5b1b4af15c81f, 0xa32cb62400ed56a4, 0x66bc0a1fa2e25e02, 0x300a386bb187e2eb, 0x975b50fa8652c3a0, 0xca7294df200ff5dd, 0x3abcbcba6f4a1ad9, 0x6f702071897f655f, 0xc5effe2ef9e39870, 0x525484109e4c858f, 0x5eeb89c20cb68505]

private theorem rounds110_2 : sixRounds 12 (by decide) quarter110_2 = quarter110_3 := by
  decide +kernel

private theorem rounds110_3 : sixRounds 18 (by decide) quarter110_3 = state111 := by
  decide +kernel

private theorem perm110 : KECCAK.f1600 absorbed110 = state111 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds110_0, rounds110_1, rounds110_2, rounds110_3]
  rfl

theorem block110 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes110 ++ tail) state110 =
      KECCAK.Bytes.run 0 tail state111 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes110 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb110 ws)) := by
    rfl
  exact (step state110).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words110).trans perm110))

private def absorb111 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x80 0x51 0x40 0x60 0x50 0x50 0x91 0x1)) 1 (by decide) (UInt64.ofBytes 0xd0 0x31 0x61 0x5b 0xfd 0x90 0x3 0x91)) 2 (by decide) (UInt64.ofBytes 0x8b 0x8b 0x8b 0x8b 0x8b 0x8b 0x8b 0x8b)) 3 (by decide) (UInt64.ofBytes 0x7 0x60 0x5b 0x56 0xac 0x4a 0x61 0x8b)) 4 (by decide) (UInt64.ofBytes 0x20 0x60 0x51 0x80 0x40 0x60 0x54 0x80)) 5 (by decide) (UInt64.ofBytes 0x61 0x15 0x16 0x85 0x1 0x60 0x2 0x60)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x7f 0x2 0x0 0x1)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x16 0x94 0x90 0x1 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x1 0x81 0x1f 0x60 0x4 0x93 0x90 0x93)) 12 (by decide) (UInt64.ofBytes 0x84 0x1 0x82 0x2 0x84 0x4 0x90 0x84)) 13 (by decide) (UInt64.ofBytes 0x92 0x52 0x81 0x81 0x52 0x92 0x90 0x1)) 14 (by decide) (UInt64.ofBytes 0x61 0x15 0x80 0x82 0x82 0x1 0x83 0x91)) 15 (by decide) (UInt64.ofBytes 0x61 0x10 0x1f 0x60 0x80 0x57 0x4e 0xf)) 16 (by decide) (UInt64.ofBytes 0x83 0x80 0x0 0x1 0x61 0x57 0x23 0xf))

private def absorbed111 : Vector UInt64 25 :=
  #v[0x8011e8e2169d6e08, 0xcbfa79e487dd34a6, 0x4ecae262a6712840, 0xd34c9d07ede6baff, 0x17dbe78d4709011f, 0x9375cc6ff3638316, 0xab8b7f9071303e5e, 0x8998be04a6be5cb0, 0xdf6997cc950eb428, 0xd94ef04ed3366b06, 0x73a12ad429ac9c68, 0xe3f5bd7b4ef1d518, 0x568c5e1734caf954, 0x5e399cd259b7dd07, 0xe70a4f68e666dba7, 0xaac6c864adc6a913, 0x82d3bb4b8da6e2ab, 0xa4dd1ff35ba2f45f, 0xe2f431758e861996, 0xaf251c1a40f5b0a0, 0xf117ad649b3d97f6, 0x5d20dc9638b35ea9, 0x6dc7f9108694bb87, 0x9276c68628d8bc70, 0x540431fd5769398c]

private theorem words111 : absorb111 state111 = absorbed111 := by
  decide +kernel

private def quarter111_1 : Vector UInt64 25 :=
  #v[0x8f1d86a62b98b2e4, 0x986e5859473a0682, 0xfd289fde0cbf14aa, 0x6ad89c42d023c054, 0x1ec61eac469725d6, 0x92891c7cc39d572e, 0x488d9658adc88f4d, 0xec6d91441744b67e, 0x9301d1a714c470cd, 0x5e5958481b1c3ee, 0x8e83d12374701ef7, 0xf7a9c8c84fb2d9a1, 0x750050390ba9770c, 0x8cdb7efb31a460e0, 0xc8216ebc15ac41f7, 0x523889b8d4b07a05, 0x7bb40b49505cfab, 0xd4140e164953899a, 0x16a40d0643c5ffdf, 0x8c027c541131acb0, 0xbcee2cb61f427064, 0xb4efff1bd408c7c3, 0xbe689b7cb0cf96de, 0xc2ff1dc4792269af, 0xcf7c932011744847]

private theorem rounds111_0 : sixRounds 0 (by decide) absorbed111 = quarter111_1 := by
  decide +kernel

private def quarter111_2 : Vector UInt64 25 :=
  #v[0x8070fc97b8b437be, 0xfdb4559bea161422, 0x4989b1d1114ea86e, 0x880d76eabe1f96ad, 0x5a2da8befaaa5a8e, 0xd137d64e1136cde8, 0x3c161f7985b350ba, 0xe7aae16b28d60324, 0x13c07b6f96fa0a5c, 0x19653d53dfc3560b, 0xb9377d61b9fa061c, 0xe13cbf59f72d9dea, 0x8f94a64d17f2bf37, 0xda18222de5d540b9, 0xdd99e0905d5fecd, 0x4b1b8345a2bab7d3, 0xf7bf727246d75139, 0xfe58fd51f163c58c, 0x34e5035eebf95c9b, 0xe7a90999f130a0e7, 0xcec4c6ff03611215, 0x6018da4036ba25fd, 0x1b781e9c6bcd30c5, 0x786531586a0b83b4, 0x34a381194adf6e3e]

private theorem rounds111_1 : sixRounds 6 (by decide) quarter111_1 = quarter111_2 := by
  decide +kernel

private def quarter111_3 : Vector UInt64 25 :=
  #v[0xc256a03344b9b781, 0x6ffe5bcfe6ea735e, 0x4ddbb640a4a4fc68, 0x9debfd3ef6ea882d, 0x7bcf0c06464d4e77, 0xc1a2352498f31cf2, 0x3e07f3ec492e6029, 0xcee14e467e59a97a, 0x6daa754be27a7d9, 0x547e30b8c6cf137c, 0xfc09ad826ec1092a, 0xdbf03e3708ac9fc9, 0x58d226e43345c7d8, 0xb536732243d5f68d, 0xebfb480d58b3c91f, 0x3e1b140d1546aeab, 0x2521103bec323c62, 0x3b8dc01199117e58, 0x3f3fbae51d424960, 0x2c0309b6a8577459, 0x40ed4b235342056e, 0x3c33bb28366301c4, 0xa2854b3c47e3be27, 0x5ad0550d8c1ce99b, 0xb48978b354c530f2]

private theorem rounds111_2 : sixRounds 12 (by decide) quarter111_2 = quarter111_3 := by
  decide +kernel

private theorem rounds111_3 : sixRounds 18 (by decide) quarter111_3 = state112 := by
  decide +kernel

private theorem perm111 : KECCAK.f1600 absorbed111 = state112 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds111_0, rounds111_1, rounds111_2, rounds111_3]
  rfl

theorem block111 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes111 ++ tail) state111 =
      KECCAK.Bytes.run 0 tail state112 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes111 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb111 ws)) := by
    rfl
  exact (step state111).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words111).trans perm111))

private def absorb112 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x20 0x60 0x91 0x52 0x83 0x2 0x4 0x54)) 1 (by decide) (UInt64.ofBytes 0x73 0x5b 0x56 0x4e 0xf 0x61 0x91 0x1)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x16 0x91 0x90 0x91 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x60 0x10 0x60 0x52 0x81 0x90 0x0 0x60)) 6 (by decide) (UInt64.ofBytes 0x83 0x80 0x40 0x60 0x52 0x81 0x90 0x20)) 7 (by decide) (UInt64.ofBytes 0x20 0x52 0x90 0x92 0x52 0x83 0x93 0x20)) 8 (by decide) (UInt64.ofBytes 0x60 0x5b 0x56 0x90 0x16 0xff 0x60 0x54)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x54 0x0)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x40 0x60 0x57 0xd2 0x3b 0x61 0x14 0x33)) 13 (by decide) (UInt64.ofBytes 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x80)) 14 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0))

private def absorbed112 : Vector UInt64 25 :=
  #v[0x155739b50726ab66, 0x96aad5086bb9d221, 0x76a52ada52d12c77, 0xfb65f827cdb668bf, 0x6eaaf571fe98e7ed, 0x6e6463bd68d7ee60, 0x16c3291ca078846d, 0x62d3df67af9c18a3, 0x89e1cdb9b74b9534, 0xc4e52585773fa037, 0xdd342872f614fe19, 0xa51ec0211de6d318, 0x9821fe50cd07459, 0x9b1ab85ce69991c2, 0xa3fbfba9c64b5689, 0x85171b80e52f1c6d, 0x1bf88215f2a0f117, 0xac41a9a6a7ea5c9f, 0xe6487a5b1ec3f9e8, 0xe96f89af094844b2, 0xf0bb9c8ae3d0e3b0, 0xb004ff4d7f7c7dbe, 0xdc55f6a172037bb1, 0x9cde4e06ef261ca3, 0x49a3df0f5893ed73]

private theorem words112 : absorb112 state112 = absorbed112 := by
  decide +kernel

private def quarter112_1 : Vector UInt64 25 :=
  #v[0x4eb7c93a467b5978, 0x1bc58d928ce86084, 0x28d785866a5c2e43, 0xc70f6e6b8f033de4, 0xfe4a79cbb82b877e, 0x42a6dfc9856b9d55, 0x9304e06914ce4e90, 0xc697249c9ed002e5, 0xacbb6a23eaeec358, 0xb301c8e17fc9b43e, 0xce8be11a036b09a4, 0xfdabe81d8d756108, 0x14bc0226fbc39acb, 0x8232f13b37455bc1, 0xefcb12b285b9d563, 0xd0c8b0b2111a220b, 0x3044438b7da40743, 0xd695e6904ccd809b, 0xbca500afcb1b532c, 0x3aa8650c9c4d6800, 0x280e782ace18572, 0x29b2170a31ddf6f3, 0x954d74500f8fe991, 0x7ef73d714937e893, 0xae5492cb5ef6095e]

private theorem rounds112_0 : sixRounds 0 (by decide) absorbed112 = quarter112_1 := by
  decide +kernel

private def quarter112_2 : Vector UInt64 25 :=
  #v[0x4f8bf8d821a24dc7, 0x30216bac834c1515, 0xa6a04a48c976a84b, 0x3296c85e5f6ba84c, 0x7ed118f34157cac7, 0xad073613e06a8628, 0x264f02974f4c5122, 0xc1ebc52393246e98, 0x83cdb136399ebdb2, 0xf4a178f48b8d5944, 0x7282e193fcb79333, 0xb03aa5cffdd598d6, 0xcceb833e8be55c71, 0x9a5fd4639b9222a3, 0xad3630efa6d570b7, 0x176178a05c46245a, 0x96c1bb77260a5672, 0xb64848ad14f4d534, 0x18f06ddc4c91ad6, 0x2512f121f07df0fc, 0xf3b2475f0d657e90, 0xbba3f8c6ab7c6f4, 0xeed7590d644a23a3, 0xc911ddc5f625a6cd, 0xe239f147d3b22ef]

private theorem rounds112_1 : sixRounds 6 (by decide) quarter112_1 = quarter112_2 := by
  decide +kernel

private def quarter112_3 : Vector UInt64 25 :=
  #v[0x2599df090dbec189, 0xf3a638fbd163aefb, 0xe147e60f0ae6103, 0x9c6c256f1a6b3ea6, 0x445c149efca6fb75, 0x50f946c232a76408, 0xc1a22e5446210bac, 0x4bc066cb9f9ab3ab, 0x5d79e011edfd73cc, 0xd8a51e1b23e6ebbc, 0x9212b30ef1be6f57, 0x280c8ec374658cf1, 0xa1b4fb05170a83aa, 0x1db3c63b5e09f4dd, 0x9fa0b88c77f80fe2, 0x4a91ab652240bba3, 0x5e3b69e2e208275f, 0xa1b4f2aa71c8d120, 0xe5d5969369ab3686, 0x89659e4790eed8b1, 0x70b26a9ee382763e, 0xfa52dbe6687a0e90, 0xe44d01b3cc31cdd0, 0x61d501d4a7ec9606, 0x8c104054a0595f]

private theorem rounds112_2 : sixRounds 12 (by decide) quarter112_2 = quarter112_3 := by
  decide +kernel

private theorem rounds112_3 : sixRounds 18 (by decide) quarter112_3 = state113 := by
  decide +kernel

private theorem perm112 : KECCAK.f1600 absorbed112 = state113 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds112_0, rounds112_1, rounds112_2, rounds112_3]
  rfl

theorem block112 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes112 ++ tail) state112 =
      KECCAK.Bytes.run 0 tail state113 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes112 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb112 ws)) := by
    rfl
  exact (step state112).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words112).trans perm112))

private def absorb113 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x60 0x20 0x60 0x52 0x81 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x24 0x60 0x52 0x90 0x81 0x1 0x82 0x4)) 2 (by decide) (UInt64.ofBytes 0x61 0x6e 0x77 0x4f 0x7f 0x52 0x1 0x82)) 3 (by decide) (UInt64.ofBytes 0x6c 0x61 0x63 0x20 0x3a 0x65 0x6c 0x62)) 4 (by decide) (UInt64.ofBytes 0x6e 0x20 0x73 0x69 0x20 0x72 0x65 0x6c)) 5 (by decide) (UInt64.ofBytes 0x6f 0x20 0x65 0x68 0x74 0x20 0x74 0x6f)) 6 (by decide) (UInt64.ofBytes 0x1 0x82 0x44 0x60 0x72 0x65 0x6e 0x77)) 7 (by decide) (UInt64.ofBytes 0x60 0x3 0x90 0x81 0x90 0x51 0x90 0x52)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x5b 0xfd 0x90 0x1 0x64)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x57 0x3e 0x3c 0x61 0x16 0x81 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x40 0x60)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 16 (by decide) (UInt64.ofBytes 0x4 0x60 0x52 0x81 0x0 0x0 0x0 0x0))

private def absorbed113 : Vector UInt64 25 :=
  #v[0x810b364c808f05b3, 0xb49750c57969df3f, 0x21118d84b7ecc89b, 0xaaaa497ce8cb0b6d, 0x28c028f8628613f6, 0xcb18eff665170876, 0x4de54c3628c2b99e, 0x11439c80bbed6622, 0xb91412df73ab79af, 0x7d499bcc96c2398f, 0x2f28f0406bf8de1b, 0x5284c5a37ea425e7, 0x3548b6f3c0070b79, 0x5c8d526efcf873ba, 0x294c77f1ffde7578, 0x6b61fc57c0c900db, 0x9891f28d29f8a10b, 0x92fa8916c4391bd4, 0x966f8427f9375e9, 0xd3c018fa2c723013, 0x61823bb5717d966, 0x2706438550d84f81, 0x58884abe0fc3083f, 0x17d3f0c7e1e87bbc, 0x9cc121d6091c00f0]

private theorem words113 : absorb113 state113 = absorbed113 := by
  decide +kernel

private def quarter113_1 : Vector UInt64 25 :=
  #v[0x6545303dba7d33f, 0xb762a64ab55562d1, 0x6f40a0c172d1ea74, 0x7621851684c8521, 0x228dfbeedb75c147, 0x503af34b6c5c3cff, 0x1481cb47a0bdd049, 0x69c41d648049d63, 0x6c32eb6e41be16c1, 0xd66775969ea5c4b7, 0xdc470c50aeaa3599, 0x15a80cac02ac9e1a, 0x1129a7bd7002d452, 0x589209287b26823f, 0xb811e5e17c6d7b80, 0xfb46bb3a52f4db8c, 0xbadd1e5e8461e33, 0xc8576740fa1ff3e3, 0x84dd14622a22f233, 0x7f29e9feb4a0a7b9, 0x165635b253454162, 0xb9747433b4a62146, 0xe3d6af218756ad1d, 0x2ec82c16742ecc29, 0x61df26070fe4e702]

private theorem rounds113_0 : sixRounds 0 (by decide) absorbed113 = quarter113_1 := by
  decide +kernel

private def quarter113_2 : Vector UInt64 25 :=
  #v[0xfd08e27d7fbc55f4, 0x19ba1780fb19df85, 0x88f0cffe070754e, 0x2eaf1344f97f2dd6, 0xfe31f39e6f17f811, 0x5cb13b6da3502a07, 0x562c02e6834b8b70, 0x5ebf59ea0c5255e0, 0xafb48f3290390c5b, 0xbc74c7a37a49bcb0, 0xe2bd944e49bf8890, 0xc622961d5c8324df, 0xa488c650904cda22, 0xa315b737d44b8b68, 0x7e1873164812899a, 0x10051ab64048c5d3, 0xfcbbf3671af812e1, 0x24cdc2163a9ff56b, 0x6c5111c57fb8143c, 0xb4b7d8faec081196, 0x4902033935d05c9c, 0x487fe457900598f7, 0x1770193e40f1b3de, 0x192b74c13a7ac0da, 0xca13d972e5b9fad9]

private theorem rounds113_1 : sixRounds 6 (by decide) quarter113_1 = quarter113_2 := by
  decide +kernel

private def quarter113_3 : Vector UInt64 25 :=
  #v[0xb61ddc6a089d09c0, 0x6744cb618d65c880, 0xb2f8c3224f44eaa3, 0x8e704afdd20eed81, 0xbb973a55c338ad, 0x332f255fc9dd4a3d, 0x457d213325f04cee, 0x95b11ac93723a341, 0x7390bbf7ab61ffad, 0xc28f33a24b8e6e04, 0x3cf0adb0e7c4259a, 0xc520297fabf2dd51, 0xa5ef9cbd1b97f419, 0x35039d825e5433b1, 0xd8655086a37c30d0, 0x5fb488128e72850e, 0xb3e19c5e5c7a5115, 0x6b0719e74e61807b, 0xafbb53ef2cf01e9c, 0x9e12bb1b21cfbbbf, 0xb2de6645065d0b96, 0xf009ee7e59d6cc3f, 0xd57ab540bde0b7a8, 0x1e4f03ddbe370bcb, 0x71276c044809878c]

private theorem rounds113_2 : sixRounds 12 (by decide) quarter113_2 = quarter113_3 := by
  decide +kernel

private theorem rounds113_3 : sixRounds 18 (by decide) quarter113_3 = state114 := by
  decide +kernel

private theorem perm113 : KECCAK.f1600 absorbed113 = state114 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds113_0, rounds113_1, rounds113_2, rounds113_3]
  rfl

theorem block113 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes113 ++ tail) state113 =
      KECCAK.Bytes.run 0 tail state114 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes113 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb113 ws)) := by
    rfl
  exact (step state113).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words113).trans perm113))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
