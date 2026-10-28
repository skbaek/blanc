import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb126 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x40 0x60 0x5b 0x56 0x93 0x4c 0x61 0x85)) 1 (by decide) (UInt64.ofBytes 0xdf 0x9e 0xa 0x8b 0x15 0x7f 0x51 0x80)) 2 (by decide) (UInt64.ofBytes 0xd5 0x3c 0xf6 0x2 0xad 0x8a 0x82 0x7a)) 3 (by decide) (UInt64.ofBytes 0x7 0xa8 0xb 0xf5 0xf2 0x8e 0xc6 0x15)) 4 (by decide) (UInt64.ofBytes 0xa1 0x33 0x28 0x84 0x12 0x6d 0x6f 0x39)) 5 (by decide) (UInt64.ofBytes 0x52 0x1 0x82 0x20 0x60 0x29 0x74 0x59)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x81 0x16 0x87 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x82 0x60 0x60 0x52 0x90 0x81 0x1 0x83)) 10 (by decide) (UInt64.ofBytes 0x80 0x51 0x83 0x52 0x90 0x88 0x1 0x81)) 11 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x1 0x91 0x90 0x3 0x84)) 12 (by decide) (UInt64.ofBytes 0x60 0x52 0x92 0x90 0x1 0x92 0x90 0x80)) 13 (by decide) (UInt64.ofBytes 0xef 0x42 0x61 0x90 0x91 0x90 0x54 0xf)) 14 (by decide) (UInt64.ofBytes 0x2c 0x4d 0x61 0x86 0x86 0x86 0x86 0x90)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x5b 0x56)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed126 : Vector UInt64 25 :=
  #v[0x93a8f44fbc487168, 0x50814d68c1e7a440, 0x9f03e0b14b01d04f, 0x96af5f391f63e5a5, 0xf25947ae30375cbe, 0x39254803680891c, 0xd1122df0e209c6b5, 0xae49ec57b22b75a9, 0x5f489f5856943efe, 0xb54a63c5385aedab, 0x87d849c3142b6143, 0xef7c636331137035, 0xa0b46893ade72a51, 0x5b02562ad7433e80, 0x2c3584918bb4e74d, 0x4e60f5a9b2140882, 0xb773646a03967108, 0x256f1cd8b279f424, 0x1befaefaba4a4486, 0xd1c3093eeabfedf2, 0xc82395cd3e6c84de, 0xf74cd78de41f2cb8, 0x469b303ba110038e, 0xd5f6a7749e10b525, 0x75918b75c8b82ddf]

private theorem words126 : absorb126 state126 = absorbed126 := by
  decide +kernel

private def quarter126_1 : Vector UInt64 25 :=
  #v[0x52155a8a4898c117, 0x18312baddc7cba01, 0xa897614bc9200b0d, 0x258dd427a8614d61, 0xe9ba8dc1766a2eab, 0x1a27c3e11be97b2b, 0xfaa3b777df4a2e9e, 0xac362c17002f125f, 0x295006540dfef6d0, 0x966e8c61cdca373, 0xc797996d4e37aaf0, 0x350126f95e6fe781, 0x20c9dfced8e747e8, 0xe0088d6da5d9f867, 0xbc19cbb892125a5, 0x5274bb0ddb78ffff, 0x961f39e2eab9abec, 0xcba04bf97a9eebd1, 0x9cf913fcad4e2885, 0xf02182b17fac1686, 0xf44f29f87ba3ab85, 0x56f8e3341787b8a9, 0xc4d39d03908d04ef, 0xf11b10264844c5a6, 0x13df4cc69d5b3b6d]

private theorem rounds126_0 : sixRounds 0 (by decide) absorbed126 = quarter126_1 := by
  decide +kernel

private def quarter126_2 : Vector UInt64 25 :=
  #v[0xe5afcc988e9de7e4, 0xe2120372a7249286, 0xb2cc2c13cfdec3b3, 0xe8a4bf64eb4c507, 0x6a58a95460e14482, 0x5ae04d4d4fa42a8f, 0x256ab497a3a7ec5f, 0xf878da4b13209eb3, 0x5b339e2ef370cde, 0x71ada6940e105610, 0xd5bebd083a39d889, 0xdd953c8255c91548, 0x8936717d629a2a3b, 0x7ac0bff8b763d8bd, 0x8e6ae7662a7ddc4, 0x21bb6703a56b1357, 0x94da3222cf573d8b, 0x18f9a4bf7d3cb31d, 0xf30cd5176644cb13, 0xd0a1422a65f5ef0f, 0xfab53dab2a53a07e, 0xac845ef23e8bc396, 0xf74dce42a9901e6f, 0x6463379ef63b2af3, 0x70b66ea271c94f28]

private theorem rounds126_1 : sixRounds 6 (by decide) quarter126_1 = quarter126_2 := by
  decide +kernel

private def quarter126_3 : Vector UInt64 25 :=
  #v[0xfd56bb882fe82e96, 0xed25fcb0580822a2, 0x812e851310dfe43f, 0x47be87f8b5e891b6, 0xa8141d7c7f3608a7, 0x1e6e04e3182134f0, 0x5ed1fefad69cc9bf, 0x1dbfa4f0f220f6ee, 0xbac94a9705f1fd92, 0x373c2336f706f7e7, 0x3dc61a30a4f82ec3, 0xb47d71f8b98677b8, 0x6fb0fe3096664af1, 0xd7110d6ffe46a439, 0xd9c9ceeb0121aa19, 0x913b066a6eaf8e16, 0xafdaf1224a451c3e, 0xc94ec757c98eed30, 0x53a55a63898b78ad, 0xe8f7f208058446eb, 0x6d642035b5c1e039, 0xef6d0f080e867a5c, 0x9f8a24002e2dce5b, 0x78749e8184c50269, 0x185321856c22f80e]

private theorem rounds126_2 : sixRounds 12 (by decide) quarter126_2 = quarter126_3 := by
  decide +kernel

private theorem rounds126_3 : sixRounds 18 (by decide) quarter126_3 = state127 := by
  decide +kernel

private theorem perm126 : KECCAK.f1600 absorbed126 = state127 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds126_0, rounds126_1, rounds126_2, rounds126_3]
  rfl

theorem block126 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes126 ++ tail) state126 =
      KECCAK.Bytes.run 0 tail state127 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes126 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb126 ws)) := by
    rfl
  exact (step state126).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words126).trans perm126))

private def absorb127 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x80 0x40 0x60 0x57 0x71 0x43 0x61 0x14)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x4 0x60 0x20 0x60 0x52 0x81 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x82 0x24 0x60 0x1e 0x60 0x52 0x1 0x82)) 8 (by decide) (UInt64.ofBytes 0x54 0x74 0x61 0x69 0x46 0x7f 0x52 0x1)) 9 (by decide) (UInt64.ofBytes 0x20 0x3a 0x32 0x56 0x6e 0x65 0x6b 0x6f)) 10 (by decide) (UInt64.ofBytes 0x20 0x64 0x69 0x6c 0x61 0x76 0x6e 0x69)) 11 (by decide) (UInt64.ofBytes 0x72 0x75 0x74 0x61 0x6e 0x67 0x69 0x73)) 12 (by decide) (UInt64.ofBytes 0x52 0x1 0x82 0x44 0x60 0x0 0x0 0x65)) 13 (by decide) (UInt64.ofBytes 0x64 0x60 0x3 0x90 0x81 0x90 0x51 0x90)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x5b 0xfd 0x90 0x1)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed127 : Vector UInt64 25 :=
  #v[0x4ad059289073ff98, 0x2231eb7b27469967, 0x1325d3c3f4e29028, 0x3c3cd993eb6d9d4a, 0x6ca83a9f99b23b14, 0x7dc1a4a9d2810838, 0x959c51863f255b34, 0x34583e4e36382059, 0x4fa29c80160689b9, 0x99d7937d39f391b, 0x2685e71056740fef, 0x858eab1f08be8717, 0x91ae1ec1322b9c96, 0xab52261ecdf09a68, 0x2b9a0af8f693a14b, 0x4601f253b5531b57, 0x281201ec61eac7f9, 0x44b42042d413e68f, 0x80ffe352ffaa4df1, 0x9258f1116dd6a3c5, 0xb868d1b4fc488f46, 0xc5c93cb8d36b4065, 0xe47e13b3f6662b73, 0x3dcd5b6b65533644, 0x18a6ff60473c49b1]

private theorem words127 : absorb127 state127 = absorbed127 := by
  decide +kernel

private def quarter127_1 : Vector UInt64 25 :=
  #v[0xaeda8f1115f21c55, 0x4e316cc1d6abeb37, 0xc85118b9a48e744d, 0xdce9083995626a89, 0x27a5551d2713d130, 0x8af71d2013c63f30, 0xd5cbe1c60024a8bf, 0x8d1490b756c5cbc, 0x23365a316e687a4d, 0x9840c2aea298950c, 0xd1690584d0f7607a, 0x9513841aeafe815a, 0xb739d9355cbf06f4, 0xf010217e34fbaa42, 0x3a731d8a26dba10d, 0x13b7b93027e47232, 0x9b5a6668b79cf660, 0x755cc39242619a99, 0x4514c165b41e71f, 0xf2476eb08ad063c1, 0xdc5e57fa32b08fce, 0xdf3da1d6f5cbaaa2, 0x476cdd8509acf44, 0x38ef83b437a5582, 0x9152fbb110d6b886]

private theorem rounds127_0 : sixRounds 0 (by decide) absorbed127 = quarter127_1 := by
  decide +kernel

private def quarter127_2 : Vector UInt64 25 :=
  #v[0x86a3ead16522f60f, 0x52fb38df1bfc085e, 0x44e08a16d8e6d08d, 0xebfd8c1c701c4902, 0x355ffe7a2462968f, 0x8a81b23cf7bc06c9, 0xecc740cc299e9c97, 0xd94f64eed0d5e816, 0xec25d3ee59bddabf, 0xe2b4834be42bcef4, 0x13d7d4b71d1dcbed, 0x66c4fc8af3a918e6, 0xa80a2bcde0772529, 0x4405681bc2e18f60, 0xc0181c44bf5df411, 0xde41e2ee68ed61f2, 0x90bdbe8be4da6483, 0xfb5ed7e95f9c3b05, 0x841fc23ff073779, 0x4ed9d81907218c0a, 0x7f8a0d6b3856c6d4, 0x28a4666f1c297461, 0x5b19ea4510d7fb70, 0x5dc3c40f97673396, 0xf800ccfee847e176]

private theorem rounds127_1 : sixRounds 6 (by decide) quarter127_1 = quarter127_2 := by
  decide +kernel

private def quarter127_3 : Vector UInt64 25 :=
  #v[0xe00b11ce1e03ce84, 0x9c47553348b5df0f, 0xce694aef96b83de9, 0xee69bbf409db223, 0xffce9a5cb15300eb, 0xb9b39464c99a590, 0x199fdd27035cbef, 0x1abfe0700987b951, 0x4f2c4df29ba8c49a, 0x753f1bdd3e4c5078, 0x5c36b6fbec76d74a, 0xf4f3f1beae13d22, 0x519f27c563fb8668, 0x174126011b800c34, 0xc8904c063f5a0375, 0xec0d64a7af9aabab, 0xb8401fb0aeefa919, 0x4463a63ffb316716, 0xcd52f4052ea691e2, 0x2eb20990f573e5a4, 0xfe06c00aac8704fa, 0x4a656c4b1a5b6760, 0x85cf6a7df78a1eee, 0x204ae031c0795cff, 0x376d1361851bf997]

private theorem rounds127_2 : sixRounds 12 (by decide) quarter127_2 = quarter127_3 := by
  decide +kernel

private theorem rounds127_3 : sixRounds 18 (by decide) quarter127_3 = state128 := by
  decide +kernel

private theorem perm127 : KECCAK.f1600 absorbed127 = state128 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds127_0, rounds127_1, rounds127_2, rounds127_3]
  rfl

theorem block127 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes127 ++ tail) state127 =
      KECCAK.Bytes.run 0 tail state128 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes127 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb127 ws)) := by
    rfl
  exact (step state127).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words127).trans perm127))

private def absorb128 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x52 0x81 0x81 0x0 0x60 0x16 0x86 0xff)) 1 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x90 0x20 0x60 0x10 0x60)) 2 (by decide) (UInt64.ofBytes 0x90 0x52 0x84 0x89 0x20 0x83 0x80 0x40)) 3 (by decide) (UInt64.ofBytes 0x7f 0x54 0x80 0x20 0x82 0x80 0x52 0x91)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x0 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x87 0x51 0x55 0x90 0x17 0x2 0x60 0x16)) 9 (by decide) (UInt64.ofBytes 0x24 0xff 0x46 0xdd 0x1c 0x7f 0x91 0x92)) 10 (by decide) (UInt64.ofBytes 0xd3 0x59 0xd1 0x72 0xaa 0xcd 0x16 0x27)) 11 (by decide) (UInt64.ofBytes 0x34 0x98 0x83 0x43 0xb3 0x85 0xa4 0x39)) 12 (by decide) (UInt64.ofBytes 0x59 0xa 0x8c 0x7c 0x9d 0xf0 0x68 0x8d)) 13 (by decide) (UInt64.ofBytes 0x50 0x50 0x50 0xa3 0x91 0x81 0x3d 0x35)) 14 (by decide) (UInt64.ofBytes 0x6e 0x32 0x61 0x5b 0x56 0x50 0x50 0x50)) 15 (by decide) (UInt64.ofBytes 0x40 0x60 0x84 0xf8 0x41 0x61 0x83 0x83)) 16 (by decide) (UInt64.ofBytes 0x52 0x40 0x60 0x1 0x60 0x60 0x80 0x51))

private def absorbed128 : Vector UInt64 25 :=
  #v[0x356cafcd6c0a952a, 0x436c68bc36a377e7, 0x27d3754a90d5c75b, 0x8f9661d34df0fffb, 0x76b94324f6128c3e, 0xaf8e2b777feb53e9, 0x2c6faa5dd1223f54, 0x2205e570caf5b622, 0xfd1c4a1739d54b06, 0xdb2b3136938ef4de, 0xb866d77159f1eda2, 0xfe22f80388b60912, 0xc682d858fafda6c1, 0x6e83607100b16c49, 0xeef89a64673ab1fe, 0xd30175163694c71, 0x57285e8b6bb6ab5b, 0xe9f1ab4b9db85454, 0x1af6f37855094071, 0xb2db64561befa5a0, 0x2de10256fd87be64, 0x98f3b0938dc242d6, 0x84463fd0e4a7023f, 0x4e5c405cfad52aec, 0x276d1f31bacc7fc7]

private theorem words128 : absorb128 state128 = absorbed128 := by
  decide +kernel

private def quarter128_1 : Vector UInt64 25 :=
  #v[0xa32d392c499375b7, 0xe9e9420b3dd6d212, 0x914253981660e621, 0x679e7066d869f9a6, 0xd834e0d40de4ccd2, 0x95226951fbb25d42, 0xbbc7b9f76fdc0bf3, 0xd72500610c39dc3c, 0x2870d1889378367c, 0xcf5df18b152fbb3f, 0xbc2dd6a2dd1ef6b6, 0xb35f749db36a79c, 0x82099086e3275a26, 0xe331a161f481e969, 0x5e402ab4a05e8f3a, 0x7599f84b45266066, 0x9e8b4ed7cea66a83, 0x6b48641328eb0cbe, 0xce14c9816b608ae8, 0x8301c0df20cd847f, 0x117e5840c2a8e609, 0x59a93d0de3a71c5e, 0x3ec827da18b53ae2, 0x5060f3ccd359d7af, 0x3c6efe713345047c]

private theorem rounds128_0 : sixRounds 0 (by decide) absorbed128 = quarter128_1 := by
  decide +kernel

private def quarter128_2 : Vector UInt64 25 :=
  #v[0x889d321a0640cae9, 0x8bfe232334aa220f, 0x8bb09854a26ea9f2, 0xa2be802a66436687, 0x8673d00f650ec10b, 0x29a52e5879772a34, 0x56d3b0a099723522, 0xbc6bca28430ae1e, 0xd127d8c3d579470c, 0x2e582abe320f1b9e, 0xd69e4d6e3cb9aeb0, 0x364a5acd733599e3, 0x827ce7c5b8aca4e5, 0xf48243a486765eae, 0x63caeab9d98a9f41, 0xd2bd40509426af3b, 0xa06efa70853680b6, 0xefd53c44d2b543e1, 0x87bc4d7d74e80478, 0x27c8a192f3b1b773, 0x5ca8fd1995a411b3, 0xaca578df595f44e1, 0x1ca979338f56cd78, 0x2c0a97c896d2def6, 0x6d0a01dd9364874a]

private theorem rounds128_1 : sixRounds 6 (by decide) quarter128_1 = quarter128_2 := by
  decide +kernel

private def quarter128_3 : Vector UInt64 25 :=
  #v[0x3b201b29ad00d4a, 0x9b605bbf2be07b73, 0x2666ecd8e07a9d17, 0xcfd7fadfd2120693, 0x3a9ee30728cb594a, 0xc239b2549e89c7de, 0xb47a919e075be9f4, 0x1e27cf1f5393b318, 0x545a70943761af40, 0x28bd3d1ba42094e5, 0xbdddff3a574f0d21, 0xee6f01ebf123a55b, 0x8e30218d4788c840, 0x3c379f2fd950dd5, 0x1762ecc577132b3e, 0x94f8e43a5c8b3e93, 0xdb5110049cc904c4, 0x4725e313152326c1, 0xb85bab16681bb163, 0x6d5471e4e10df1ac, 0xd0edecd3bd7fd90f, 0x7a87067121763581, 0x4fbf4a26f0dbf3f4, 0xf7785f10799cd123, 0xd13c070fa0e41237]

private theorem rounds128_2 : sixRounds 12 (by decide) quarter128_2 = quarter128_3 := by
  decide +kernel

private theorem rounds128_3 : sixRounds 18 (by decide) quarter128_3 = state129 := by
  decide +kernel

private theorem perm128 : KECCAK.f1600 absorbed128 = state129 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds128_0, rounds128_1, rounds128_2, rounds128_3]
  rfl

theorem block128 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes128 ++ tail) state128 =
      KECCAK.Bytes.run 0 tail state129 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes128 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb128 ws)) := by
    rfl
  exact (step state128).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words128).trans perm128))

private def absorb129 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x25 0x60 0x80)) 1 (by decide) (UInt64.ofBytes 0x73 0x39 0x91 0x25 0x60 0xf 0x5a 0x61)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x60 0x16 0x8a 0x80 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x20 0x60 0xa 0x60 0x52 0x81 0x90 0x0)) 6 (by decide) (UInt64.ofBytes 0x20 0x83 0x80 0x40 0x60 0x52 0x81 0x90)) 7 (by decide) (UInt64.ofBytes 0x52 0x90 0x92 0x52 0x83 0x16 0x8c 0x93)) 8 (by decide) (UInt64.ofBytes 0x56 0xe2 0x4b 0x61 0x90 0x91 0x54 0x20)) 9 (by decide) (UInt64.ofBytes 0x88 0x88 0x85 0x89 0x62 0x44 0x61 0x5b)) 10 (by decide) (UInt64.ofBytes 0x80 0x40 0x60 0x5b 0x56 0x9e 0x4d 0x61)) 11 (by decide) (UInt64.ofBytes 0xbd 0x4c 0xe9 0x59 0x5 0xb7 0x7f 0x51)) 12 (by decide) (UInt64.ofBytes 0xb6 0xf9 0x7 0xec 0xeb 0x58 0x19 0xa9)) 13 (by decide) (UInt64.ofBytes 0x5c 0xd2 0xc8 0x97 0x0 0x49 0x3b 0x5b)) 14 (by decide) (UInt64.ofBytes 0x15 0x10 0xdf 0x5 0x11 0xd7 0xac 0x8d)) 15 (by decide) (UInt64.ofBytes 0x73 0x52 0x1 0x82 0x20 0x60 0xd8 0xb6)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed129 : Vector UInt64 25 :=
  #v[0xd06da1f428d09c04, 0x280dec12ebd37f6a, 0x157c4cf70e52319b, 0x4bc88e28d9cf85c6, 0x36a4861365d6d0e5, 0x4540330f81d56418, 0xf52f1eda9536dc8f, 0x33bc2367343c8eb4, 0x5076c198b375156f, 0x49c26fcd4c2e7dad, 0x11f598a85538cd5f, 0x92eb671ca0b7abcd, 0x34f60ea38208da91, 0x2ed5c767b05107e4, 0x2d42004c12b44e5d, 0x214d9742674354af, 0x5ea980d99a37e2e3, 0x8604da606c05f8a9, 0xf41e791f1f1bb9dd, 0xd83f9caefdfb57b7, 0x1d2df34980e6bbd6, 0xe73a94dd04d28754, 0x760b3e86ebe8f64d, 0x760b6be06d10087, 0xafa7b739e92a179b]

private theorem words129 : absorb129 state129 = absorbed129 := by
  decide +kernel

private def quarter129_1 : Vector UInt64 25 :=
  #v[0x7857ad553b113940, 0xc5ad744927b9113d, 0x1b6793d915f761ec, 0x86a235f8639c486c, 0xcef8cab070a0f2b3, 0x8116e28f3da83696, 0xf91c01493d9a8c35, 0x89589e0fa5d541, 0x9ad54755fb06216d, 0x94325ac3b5ed1045, 0x9ca6cdfd3b32892, 0xacd029610783d8b7, 0xd9db7f1011c78369, 0xd4629867b8de13e7, 0x46fba492b6986645, 0xb1f8aa052a929503, 0x6560e6f33424764c, 0x7501684456b70e34, 0x24741eb0e69f7314, 0xe79e9bf53ff81a3, 0x5179d8c22f587db6, 0x51f885044a0fbd73, 0x8b939dbf125901ca, 0x2addedcff153afe0, 0xc31ee3235f899d00]

private theorem rounds129_0 : sixRounds 0 (by decide) absorbed129 = quarter129_1 := by
  decide +kernel

private def quarter129_2 : Vector UInt64 25 :=
  #v[0xa93793bf4d457938, 0x6e92fde57e32cc60, 0xa348b7fcb6b30aa8, 0xfd6e49e9acec88fa, 0xadb35c207c5cf330, 0xf7d68112aa105cfa, 0x7d5cd426342b0595, 0x7037220f69562a9c, 0x8cd8a62d94dd9169, 0xed03921c05f5ce8, 0x33aa184798f0e626, 0xb97d2c6bd1b9fe05, 0xcdd34e0ca44d8ece, 0xe75b3089840a0286, 0xe438ba966b20f8fb, 0xf0600f3647579bd2, 0xc543aa3f300fcb7a, 0x841e97bb3a6f8078, 0x35c8e748f22da7a6, 0xfdd4a1fb26782144, 0xd5c43d079eb8beb2, 0xe517af1982174181, 0x65496863eb135a5d, 0x7675293f35c7f485, 0x8d2bae1f345bc0a0]

private theorem rounds129_1 : sixRounds 6 (by decide) quarter129_1 = quarter129_2 := by
  decide +kernel

private def quarter129_3 : Vector UInt64 25 :=
  #v[0x145a1b78f63a9590, 0x9a9084b8d66ac97b, 0x5195ac412efbc786, 0xeed5b53021900dc3, 0x10277c1cdc3e4f2e, 0xc733226c3c89a7b9, 0x624394c10c9b9b43, 0x6314a835ea8c7ce0, 0x36d225765f283bed, 0x50ff186593db2a67, 0x3cb19d183201483d, 0x8ad679ead0a2ed79, 0x57ba89486a5e349f, 0xa4d77c41d3728b66, 0x826ef448550e2bf0, 0xe73b002f77816547, 0x89954b90e9ea9eca, 0xb9e9702743972253, 0xefbffd325e297f6c, 0xae7bcf3da466f50e, 0x35db7bff08238515, 0x2b7b76906491c098, 0x97e03d600258b77f, 0x7de7a2978711856d, 0xd370a73c2bd388b1]

private theorem rounds129_2 : sixRounds 12 (by decide) quarter129_2 = quarter129_3 := by
  decide +kernel

private theorem rounds129_3 : sixRounds 18 (by decide) quarter129_3 = state130 := by
  decide +kernel

private theorem perm129 : KECCAK.f1600 absorbed129 = state130 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds129_0, rounds129_1, rounds129_2, rounds129_3]
  rfl

theorem block129 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes129 ++ tail) state129 =
      KECCAK.Bytes.run 0 tail state130 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes129 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb129 ws)) := by
    rfl
  exact (step state129).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words129).trans perm129))

private def absorb130 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x82 0x16 0x8c 0x80 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x16 0x8b 0x90 0x52 0x90 0x81 0x1 0x84)) 3 (by decide) (UInt64.ofBytes 0x82 0x80 0x60 0x52 0x1 0x83 0x60 0x60)) 4 (by decide) (UInt64.ofBytes 0x1 0x82 0xa0 0x60 0x52 0x90 0x8a 0x1)) 5 (by decide) (UInt64.ofBytes 0x88 0x1 0x82 0xc0 0x60 0x52 0x90 0x89)) 6 (by decide) (UInt64.ofBytes 0x88 0x1 0x83 0x80 0xe0 0x60 0x52 0x90)) 7 (by decide) (UInt64.ofBytes 0x90 0x3 0x84 0x80 0x51 0x83 0x52 0x90)) 8 (by decide) (UInt64.ofBytes 0x90 0x0 0x1 0x61 0x52 0x81 0x1 0x91)) 9 (by decide) (UInt64.ofBytes 0x54 0xf 0x60 0x52 0x92 0x90 0x1 0x92)) 10 (by decide) (UInt64.ofBytes 0x86 0x90 0xf5 0x44 0x61 0x90 0x91 0x90)) 11 (by decide) (UInt64.ofBytes 0x5b 0x56 0x2c 0x4d 0x61 0x86 0x86 0x86)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x61 0x14 0x16 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x7f 0x51 0x80 0x40 0x60 0x57 0x77 0x45)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8))

private def absorbed130 : Vector UInt64 25 :=
  #v[0x4b8cd69fd31e844d, 0x6ac81a35bbe47c23, 0x22b4e358c05313ca, 0xa2085a995d4eee2, 0xd6a7039f256a082d, 0xa68a31883a858cfa, 0x2ec01bbf05347f9b, 0x1ed7d00b9ef95789, 0x24234f1338db772c, 0x75c7a9a5d258bb15, 0x7223c3a4049940ec, 0x91b23e87a1f9e2bd, 0xf9db7125c2c016d1, 0x27ed3a45913db450, 0x45cd971e7afc61fb, 0xba5b2cc32d465fcd, 0x9cf34660418d28dd, 0xb4591c981c16703a, 0x369ee079ee4cd46d, 0xb21574b021e0aa77, 0x245f370aabe4a25b, 0x75ce425dd08fe2e4, 0x1ea6bc86ba9f9ea3, 0x38b2c104d6294c1d, 0x197f37ce7a31dc5f]

private theorem words130 : absorb130 state130 = absorbed130 := by
  decide +kernel

private def quarter130_1 : Vector UInt64 25 :=
  #v[0xc618d38ccb7135b4, 0x89ee25d289c7b7aa, 0xfeb0955ffb493d11, 0xea0367688bebd757, 0x2afe905925c6dc29, 0x30c07013b98aed73, 0x8c00b798b74ca9ff, 0xc37bd33bb47e0be7, 0x55056fbdf7aae853, 0xc857b1921f8dadf0, 0x74189adfad38a371, 0xa4de751c06e83f5, 0x471cb159895f4313, 0xbbd065cefa10ad68, 0x5895ea15e4f605b1, 0xc432634dfff09257, 0xbf58d8308098e571, 0xa18d40f38b5761e1, 0x6943605b7a58c6a4, 0xf9c3e6aecf3d6065, 0xce3ed194d0693aa8, 0xd4c4d3a72b4c04dd, 0xf739eb2f4d14536a, 0x747e557ab3074e54, 0x500de979044dd75c]

private theorem rounds130_0 : sixRounds 0 (by decide) absorbed130 = quarter130_1 := by
  decide +kernel

private def quarter130_2 : Vector UInt64 25 :=
  #v[0xd54f60ec59663f23, 0x5d7792cfeef1487e, 0x5339d09e77d2a483, 0x1da9e9f57184d29b, 0xdfdc9c03dbaf7cb9, 0x6dd03ab0b8d1a1ed, 0xa99fdf5605be7394, 0x309b23618bfcd4dd, 0x11a1e374a2e7efd4, 0xd328143aeec158ad, 0x938cd949c7be86df, 0x878412e096f14596, 0x7133f2a769298de7, 0x70a2de6b9c728cee, 0xfbe8b8df35173c9, 0xe8e77aaabda89538, 0xc818ff5f3e8a8247, 0x7c7694c0f6a062cb, 0xbbf911cd1c1475, 0x76a8326140517200, 0xfd04009a9f441b3e, 0x8ee688bd90d7df31, 0x65fdcbf769ab9e51, 0x6383ba8fb3e7d5c0, 0x10b2544e827e6715]

private theorem rounds130_1 : sixRounds 6 (by decide) quarter130_1 = quarter130_2 := by
  decide +kernel

private def quarter130_3 : Vector UInt64 25 :=
  #v[0x7110f57baf031569, 0xea90d824ad6db6fe, 0xff5721faa693c8d1, 0xe987a9ab931a7d10, 0x598d5f8ace2b91ad, 0x8a35a3db831e79da, 0xb1599d6993712c73, 0xa05733a0cf337be1, 0x5b7ed357a82b5800, 0x79678c0574aad146, 0x5bf1d0aa58ca8643, 0x854b8b48c0ef3535, 0xadc0686ab1c0a958, 0xaf517420f795a875, 0xbfcffe607e10fed2, 0xc625af61f6baab6e, 0xfa906889a0e3925a, 0x9152bb43fb852d23, 0x840a8137dd1e40ff, 0x336f3cde1425a061, 0x33fc408c2ac4ec9, 0xca87374e58991039, 0x7aef034a65c6095f, 0x3c87a50dbbf8770b, 0x37e024bc75b5929e]

private theorem rounds130_2 : sixRounds 12 (by decide) quarter130_2 = quarter130_3 := by
  decide +kernel

private theorem rounds130_3 : sixRounds 18 (by decide) quarter130_3 = state131 := by
  decide +kernel

private theorem perm130 : KECCAK.f1600 absorbed130 = state131 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds130_0, rounds130_1, rounds130_2, rounds130_3]
  rfl

theorem block130 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes130 ++ tail) state130 =
      KECCAK.Bytes.run 0 tail state131 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes130 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb130 ws)) := by
    rfl
  exact (step state130).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words130).trans perm130))

private def absorb131 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x1 0x82 0x4 0x60 0x20 0x60 0x52 0x81)) 4 (by decide) (UInt64.ofBytes 0x52 0x1 0x82 0x24 0x60 0x1e 0x60 0x52)) 5 (by decide) (UInt64.ofBytes 0x6b 0x6f 0x54 0x74 0x61 0x69 0x46 0x7f)) 6 (by decide) (UInt64.ofBytes 0x6e 0x69 0x20 0x3a 0x32 0x56 0x6e 0x65)) 7 (by decide) (UInt64.ofBytes 0x69 0x73 0x20 0x64 0x69 0x6c 0x61 0x76)) 8 (by decide) (UInt64.ofBytes 0x0 0x65 0x72 0x75 0x74 0x61 0x6e 0x67)) 9 (by decide) (UInt64.ofBytes 0x51 0x90 0x52 0x1 0x82 0x44 0x60 0x0)) 10 (by decide) (UInt64.ofBytes 0x90 0x1 0x64 0x60 0x3 0x90 0x81 0x90)) 11 (by decide) (UInt64.ofBytes 0x61 0x86 0x8a 0x81 0x45 0x61 0x5b 0xfd)) 12 (by decide) (UInt64.ofBytes 0x8a 0x8c 0x45 0x61 0x5b 0x56 0x5e 0x4e)) 13 (by decide) (UInt64.ofBytes 0x50 0x5b 0x56 0xfa 0x43 0x61 0x8a 0x8a)) 14 (by decide) (UInt64.ofBytes 0x50 0x50 0x50 0x50 0x50 0x50 0x50 0x50)) 15 (by decide) (UInt64.ofBytes 0x73 0x51 0x80 0x40 0x60 0x5b 0x56 0x50)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed131 : Vector UInt64 25 :=
  #v[0x8d194235f5e17ca3, 0xe774418e0dfd094f, 0x65282e360b3504f3, 0xabb1f31aed3c7972, 0xa8278b0a52e4667, 0x80b946d3f8984872, 0x84e9f24c60564cd1, 0x23410d7f4392479b, 0xda6fe2cbbd90e71b, 0x53048b50b2cfaf3, 0x7645a9836602493a, 0xfe9a2f490d366a19, 0x5e826429bedcc92, 0xe72426c5ca79f49d, 0x548819c8cac1c3ad, 0xe87f06b963a05d9d, 0xabf9ebde94180d93, 0xb710e5b9805977c0, 0xba5769099d1efea5, 0x23d398d71d4d2bb, 0x72f335a67b878ec4, 0x52f39604d00ece5e, 0x7972d3837112280b, 0x5187fe2a0af1c736, 0x36bc192d53832c6b]

private theorem words131 : absorb131 state131 = absorbed131 := by
  decide +kernel

private def quarter131_1 : Vector UInt64 25 :=
  #v[0xcb6c051d7ba7c699, 0xac236d3faba34f97, 0x544acfaebfdcbeaa, 0x735552f66d6e29f9, 0x726ff2791ff98ce3, 0xf98f16da4374d479, 0x84f6b453e479d545, 0x7d5cb73e56bc536e, 0x2d7f80d1d8763690, 0xadf190fb963bbb9e, 0xa8e4e6d912ae3125, 0x1e5d50a217f1be3e, 0xb928d7eb77e25522, 0xefcbf83fd15e89a8, 0x1152f00b54b93f32, 0xf76a5ac11547a549, 0x4f3234121026a2c8, 0x7a87293135d26fdc, 0x93687f957b3786a1, 0x7ccde27938dbea0c, 0x6550ece4ce7fb890, 0xe6ae3ed3b88a206c, 0x4da61df4e30781a3, 0xf89e8e095d549f98, 0xa4ae535562bad6ba]

private theorem rounds131_0 : sixRounds 0 (by decide) absorbed131 = quarter131_1 := by
  decide +kernel

private def quarter131_2 : Vector UInt64 25 :=
  #v[0xb0a220effa934133, 0x77921f7d3b8dc74c, 0x75a425d0e83cf7f6, 0xbc2af1d1fc8acfcd, 0xd38870f1a01eb5b5, 0x400fd222a944ee90, 0x668934c9420df567, 0x5c99572177b42301, 0x5965c56d08b5f4de, 0xdae10e3b9612745e, 0x5e1bf8adda83012b, 0xf617089a399aab81, 0x6342ab3779eb4793, 0x389dde006cb6482e, 0x8be09d62edef214a, 0x6c1f832d31d16e86, 0xd0ad221bd2a09ab5, 0x3c71301993e7e073, 0xf00cf59477b8b7ec, 0x3e5f449c1d3d4c3, 0x5cb2e0bad7984ed8, 0xadcbf18a1a45e9f5, 0x5630d7fcd15ea458, 0x969bb511860f07fe, 0xefce6c2abddfe7c5]

private theorem rounds131_1 : sixRounds 6 (by decide) quarter131_1 = quarter131_2 := by
  decide +kernel

private def quarter131_3 : Vector UInt64 25 :=
  #v[0x898efcf96f579b1c, 0x15af717c8f841c95, 0x4df732a0cf62a3b0, 0xab3f02244178675b, 0xfddfcb880655471c, 0x3b5465f1c88ced00, 0xe2dfa7518d74ac35, 0x1c864f1ae1d054c6, 0xb45ff3bad1df3147, 0x543b3b2ead2a97d7, 0x516ba5f3cace5fbe, 0xf605bed402aef1ed, 0x5af722f1b02e0776, 0x4c15a2333593a5e7, 0x9708f7c77d49eeba, 0x5a61ea7e702fc2cf, 0xfc4ae1c122c1bf73, 0x14f421bebf821a02, 0x78902859d9fd0a70, 0x8a6b811716ea38d0, 0x32f59f08c5297f5c, 0xf591d29f88160ed1, 0xc93b5a01921a30a1, 0x8c30869f30b9edbb, 0xc679ce30779cb665]

private theorem rounds131_2 : sixRounds 12 (by decide) quarter131_2 = quarter131_3 := by
  decide +kernel

private theorem rounds131_3 : sixRounds 18 (by decide) quarter131_3 = state132 := by
  decide +kernel

private theorem perm131 : KECCAK.f1600 absorbed131 = state132 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds131_0, rounds131_1, rounds131_2, rounds131_3]
  rfl

theorem block131 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes131 ++ tail) state131 =
      KECCAK.Bytes.run 0 tail state132 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes131 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb131 ws)) := by
    rfl
  exact (step state131).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words131).trans perm131))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
