import Blanc.Lift.Usdc.ImplV2_1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb120 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x60 0x20 0x60 0x52 0x81 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x24 0x60 0x1e 0x60 0x52 0x1 0x82 0x4)) 4 (by decide) (UInt64.ofBytes 0x74 0x61 0x69 0x46 0x7f 0x52 0x1 0x82)) 5 (by decide) (UInt64.ofBytes 0x3a 0x32 0x56 0x6e 0x65 0x6b 0x6f 0x54)) 6 (by decide) (UInt64.ofBytes 0x64 0x69 0x6c 0x61 0x76 0x6e 0x69 0x20)) 7 (by decide) (UInt64.ofBytes 0x75 0x74 0x61 0x6e 0x67 0x69 0x73 0x20)) 8 (by decide) (UInt64.ofBytes 0x1 0x82 0x44 0x60 0x0 0x0 0x65 0x72)) 9 (by decide) (UInt64.ofBytes 0x60 0x3 0x90 0x81 0x90 0x51 0x90 0x52)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x5b 0xfd 0x90 0x1 0x64)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x81 0x81 0x0 0x60 0x16 0x86 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x52 0x81 0x90 0x20 0x60 0x10 0x60 0x52)) 15 (by decide) (UInt64.ofBytes 0x52 0x84 0x89 0x20 0x83 0x80 0x40 0x60)) 16 (by decide) (UInt64.ofBytes 0x54 0x80 0x20 0x82 0x80 0x52 0x91 0x90))

private def absorbed120 : Vector UInt64 25 :=
  #v[0xf140a67e70133d0b, 0xe5e88a5d3181e1f0, 0x14b890b2106e58c, 0x7a0feb9858bd242, 0x305c1db18dbb70ca, 0x9331af2d6dace0e5, 0xa105d9bd1385badf, 0x2c2371e807104df5, 0xfe2fd9e0719ceabb, 0xc0515f29c7f3a0db, 0xcfa61d5ebf5ca705, 0xcaaa9701f40e964, 0xa4be0ee05f0e8b03, 0x10df70a567d51a98, 0xde15656a732126ca, 0xd7138f509499525e, 0x24974f28b4aea58a, 0x79beabb2ac2737a8, 0x4a9cfae5b4052304, 0xc79dd703db66f75c, 0x3fc7a34d5e462955, 0x93b30d004f46f404, 0x22f51940a432c2f5, 0x9fed4c427e995e61, 0x55d078e4f862e6d6]

private theorem words120 : absorb120 state120 = absorbed120 := by
  decide +kernel

private def quarter120_1 : Vector UInt64 25 :=
  #v[0x6823e2d6aa65a59e, 0x57770f3c53cdb2d8, 0x8eceff81a93ba9e3, 0xba7e88841dbbd982, 0xedb369f63661eb78, 0xb0135c1dc16fa2b6, 0x69f89d4544f2395a, 0xc591d7d7f38f7d37, 0x44150d47c11b1263, 0x947187ebffce8d1b, 0xaf22844bb943f722, 0x86acca7421f51bd2, 0xf25fd9b1f0ac8eaa, 0x7192fda37210a374, 0x453d0542a7015b9b, 0x2b9189ff50b19ded, 0xdd70310875dc9689, 0xd719518cafa849ea, 0x43bf5776635bcef8, 0xed9525ca060edadc, 0xb2a44cd51f852d55, 0x280dc976fe33682d, 0x9a426d37ee44acc3, 0xa0aa2fd719bc486a, 0x489b4c83f6490a71]

private theorem rounds120_0 : sixRounds 0 (by decide) absorbed120 = quarter120_1 := by
  decide +kernel

private def quarter120_2 : Vector UInt64 25 :=
  #v[0x49b33fa04f31d2f0, 0x84544dc6cb1d93f7, 0xcdb2e178ee525f03, 0x3c423e54967ecbd6, 0xd620b0ab8b179f27, 0xe69cc065ef0dee26, 0xa113920eb118837d, 0xd72a311aefe408ee, 0x5309315112d1c417, 0xf2d8ad05a0a43943, 0xa10e98e3fc46321f, 0x2f89ab71e70beec5, 0xafd087c9df81924e, 0xa70217e9bad6fc02, 0x33ddd9701a875ba8, 0x8b4f30d63cc20fdc, 0x7fa5b1596f7e9b61, 0xf225530c1640436b, 0x6b82fe83cac5056d, 0x2c1015736b7eea95, 0x827d380044bb8ef5, 0x434303a94467e5bd, 0xb8abfcf278fe3322, 0x18e216855b5c1608, 0xe6c966937fde2ee5]

private theorem rounds120_1 : sixRounds 6 (by decide) quarter120_1 = quarter120_2 := by
  decide +kernel

private def quarter120_3 : Vector UInt64 25 :=
  #v[0x5a162519b0f8a352, 0x8efa2782841795eb, 0x4368f8558e3711ed, 0x4f41b11094460fb3, 0xbba47792ccc8878f, 0x586f666e17354a0e, 0xf7960ce77dfd9d8b, 0x2d72e2ddc9d9fc0e, 0x93ea8472618e0daa, 0x85bc96da4aeb3a3b, 0xe26f0faa2192f9f8, 0x4262b1228b9d03f2, 0x541f517e91cc1e6f, 0xf80b0a167c971b19, 0x204b5d53bd3fd0db, 0xfcdad3e7d60f7595, 0x28f11c694786bd60, 0xac280e0c45baf2ef, 0x23c40b872fe12128, 0x40e29a6f3d6f5b9e, 0x8384fe54eb952039, 0xc49c7e4e9c6b23d6, 0x1488350819717f13, 0xa4ba3e12359056b5, 0x5a1db584cf003122]

private theorem rounds120_2 : sixRounds 12 (by decide) quarter120_2 = quarter120_3 := by
  decide +kernel

private theorem rounds120_3 : sixRounds 18 (by decide) quarter120_3 = state121 := by
  decide +kernel

private theorem perm120 : KECCAK.f1600 absorbed120 = state121 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds120_0, rounds120_1, rounds120_2, rounds120_3]
  rfl

theorem block120 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes120 ++ tail) state120 =
      KECCAK.Bytes.run 0 tail state121 := by
  exact run_block_of_step bytes120 tail absorb120 state120 absorbed120
    state121 (fun _ => rfl) words120 perm120

private def absorb121 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x7f)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x51 0x55 0x90 0x17 0x1 0x60 0x16 0x0)) 5 (by decide) (UInt64.ofBytes 0xff 0x46 0xdd 0x1c 0x7f 0x91 0x92 0x87)) 6 (by decide) (UInt64.ofBytes 0x59 0xd1 0x72 0xaa 0xcd 0x16 0x27 0x24)) 7 (by decide) (UInt64.ofBytes 0x98 0x83 0x43 0xb3 0x85 0xa4 0x39 0xd3)) 8 (by decide) (UInt64.ofBytes 0xa 0x8c 0x7c 0x9d 0xf0 0x68 0x8d 0x34)) 9 (by decide) (UInt64.ofBytes 0x50 0x50 0xa3 0x91 0x81 0x3d 0x35 0x59)) 10 (by decide) (UInt64.ofBytes 0x30 0x61 0x5b 0x56 0x50 0x50 0x50 0x50)) 11 (by decide) (UInt64.ofBytes 0x60 0x84 0x21 0x3e 0x61 0x83 0x83 0x71)) 12 (by decide) (UInt64.ofBytes 0x40 0x60 0x1 0x60 0x60 0x80 0x51 0x40)) 13 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x25 0x60 0x80 0x52)) 14 (by decide) (UInt64.ofBytes 0x39 0x91 0x25 0x60 0x91 0x53 0x61 0x1)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed121 : Vector UInt64 25 :=
  #v[0x48b446a60d50e031, 0xff81781d5c870b1d, 0x979dfd5c663e7276, 0xeac4a4235b85a022, 0x424ef438c8122eb6, 0x190b4aba19df195c, 0x5520e9fdf1a26763, 0xdc6b968b5c29d116, 0x9c0ec9db776ff92e, 0xae6789f790be787e, 0x9f4f5d707a840ac2, 0x5ecdbd4b0d9b4eb8, 0x2c2450829f00b15e, 0x30e55f27f8f637f1, 0x2453cfc596d5cb33, 0xa5248b110bd265c0, 0x933dabbc38f28f7d, 0x9ecfe9f8511e4c26, 0x228fc72eb75335a5, 0x7973a11a68e6d919, 0x844df648ec45e459, 0xc39efd1ebb312f4c, 0x67f441bce77d2e0c, 0x989f3f336f458807, 0x1ac695011cfdecd3]

private theorem words121 : absorb121 state121 = absorbed121 := by
  decide +kernel

private def quarter121_1 : Vector UInt64 25 :=
  #v[0xccca6d4e4610f1d1, 0xe511080389d1c7b5, 0xac2f6f707e82283a, 0x9f99f70bf747ab4f, 0x4c0857489539e0a6, 0xeb36f9bb7448f72d, 0xb434c4a63999e888, 0x3f5aaccbfcb1c983, 0x976726cda33dffc3, 0xacc3b9e01ac1ad3d, 0x1bf4bd79c3d7b984, 0x3ec3a27739a5b054, 0xe5c1ca280cd4a6b7, 0xfdbe632e2c17dd00, 0xae1bf8fb66bb6c09, 0x6082c279bea9d034, 0xf1b891f3b56ea127, 0xc879d521050ea85e, 0x2edade670c58b907, 0x4820b0a71f55a20d, 0x6721a26313186979, 0x5b82f816c1fd7a0c, 0x8584f1abe7f8be18, 0xa286d6aae514f18b, 0xd712228f2a728b8]

private theorem rounds121_0 : sixRounds 0 (by decide) absorbed121 = quarter121_1 := by
  decide +kernel

private def quarter121_2 : Vector UInt64 25 :=
  #v[0x2ae3d5eb1f9b2945, 0x8cea6de6278a17fd, 0x88d09433eeb86b82, 0xc38ef052c22012eb, 0xc0e4334e868babdc, 0xe0216f803784dd4e, 0xec6a83189420797, 0xdfc4eb4631296aa, 0x60cb5ce6b48d4c61, 0x2225b5c040d0bad5, 0x251d5ef65b7b2712, 0x6f4eee893b7207ba, 0x9a280c1a62219fda, 0xe88441953b7dc48b, 0x8e09370438fb9f07, 0x2a104550871926c3, 0xb84d3b4cf9055b47, 0xe1ffeaad3e4e97f2, 0x48c259d3579b43a7, 0x1667d609e3dbf70d, 0xad373904cff3e174, 0xa774d46b095a0ab9, 0xcfbebff899fa99a1, 0x441e7a69ce4424a3, 0xe91cfeba64b4e5a8]

private theorem rounds121_1 : sixRounds 6 (by decide) quarter121_1 = quarter121_2 := by
  decide +kernel

private def quarter121_3 : Vector UInt64 25 :=
  #v[0x5c788ec6c4dec0a0, 0x4ce10a1cb064bf16, 0xa92b372d8b8e48ec, 0x76d934fcaf7fbcf9, 0x211ab4ec65fbaae2, 0x884ab4aada27ec0d, 0x11f1bd2ca7b4640, 0x98de6bcd07c77b2e, 0xd0f53298be0a74fd, 0x65b96c3654557180, 0x7772261f4377e1a2, 0x37e3c5aa0d52beb7, 0x574da6b0ad134d91, 0xc0b053715e1c29a2, 0xb0338321a89a5181, 0x1a00ea5d1e2b4820, 0x51bc286621dae959, 0xb83a5bb38b2c6bf4, 0x68479f1045fc9adb, 0xdca62a6381f9db3c, 0x9b21cc9bcbe586e6, 0x5f2f366bf7c30036, 0x35f4b1f10cec23b, 0x2b0eb0fa21c295a2, 0x9df299d8ff3ef4b7]

private theorem rounds121_2 : sixRounds 12 (by decide) quarter121_2 = quarter121_3 := by
  decide +kernel

private theorem rounds121_3 : sixRounds 18 (by decide) quarter121_3 = state122 := by
  decide +kernel

private theorem perm121 : KECCAK.f1600 absorbed121 = state122 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds121_0, rounds121_1, rounds121_2, rounds121_3]
  rfl

theorem block121 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes121 ++ tail) state121 =
      KECCAK.Bytes.run 0 tail state122 := by
  exact run_block_of_step bytes121 tail absorb121 state121 absorbed121
    state122 (fun _ => rfl) words121 perm121

private def absorb122 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x16 0x8a 0x80 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x60 0xa 0x60 0x52 0x81 0x90 0x0 0x60)) 2 (by decide) (UInt64.ofBytes 0x83 0x80 0x40 0x60 0x52 0x81 0x90 0x20)) 3 (by decide) (UInt64.ofBytes 0x90 0x92 0x52 0x83 0x16 0x8c 0x93 0x20)) 4 (by decide) (UInt64.ofBytes 0x76 0x45 0x61 0x90 0x91 0x54 0x20 0x52)) 5 (by decide) (UInt64.ofBytes 0xff 0x73 0x51 0x80 0x40 0x60 0x5b 0x56)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x82 0x24 0x60 0x16 0x84 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x84 0x1 0x82 0x80 0x44 0x60 0x52 0x1)) 10 (by decide) (UInt64.ofBytes 0x90 0x3 0x83 0x80 0x51 0x82 0x52 0x90)) 11 (by decide) (UInt64.ofBytes 0x91 0x90 0x64 0x60 0x52 0x81 0x1 0x91)) 12 (by decide) (UInt64.ofBytes 0x1 0x81 0x20 0x60 0x52 0x91 0x90 0x1)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x7b 0x51 0x80)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed122 : Vector UInt64 25 :=
  #v[0xb2a5cc23792393c8, 0x3bb5bff3664f01e1, 0xe276cb33f0efae15, 0x73919959552a609b, 0x5e8309f62f1acd79, 0x7d647fefd6fb4043, 0xe15478d79de4394a, 0xe982a5b20abe492f, 0x969fbae0918cc55, 0x8cb6a62586561f49, 0xe9117e40783547f0, 0x82446c446b35c4da, 0x6d3a3860a90d050a, 0x9c76acfc6dbe32f8, 0xb6c58958d39e279d, 0xb420a4d4f1b30308, 0x78f2f03838e6c762, 0xb8a5b62b1c0666dc, 0x48b10bd329127a2, 0xa7b2f1175d50b2bc, 0x2d56c090e4b23e03, 0xf2fba360114aa54a, 0x197f33e0be5c2874, 0x1ca80ac3cdc77cb8, 0x9b12b2c4ad062fc4]

private theorem words122 : absorb122 state122 = absorbed122 := by
  decide +kernel

private def quarter122_1 : Vector UInt64 25 :=
  #v[0x9c8f520e5cd11f49, 0xad10240575ceeaee, 0x51870db85fe968d8, 0xd321d56f4db95c00, 0xdf4df8c8deabfd71, 0x3b84f46b7413b94b, 0x3d60914748ace2eb, 0x828485d5448ccc47, 0xf4b8b03c99f8cc13, 0x960cd88c221a8e4f, 0x27a7066dcd0ffecc, 0x14e26183a9f72d28, 0x7eebc19c9f9f66cd, 0x88c24f9939752a02, 0x499c18203244418c, 0x31430be5ec4f762b, 0xa0396a2cd4603511, 0xc35dbe28d615288, 0xb46c891b3f3e85b1, 0xc1c4fdf24b9f7762, 0x12ae7643df955884, 0xdf66894823e6301f, 0x4e5e5a2d2c47a699, 0xb780a1ba745154bb, 0xc18291556575b3fa]

private theorem rounds122_0 : sixRounds 0 (by decide) absorbed122 = quarter122_1 := by
  decide +kernel

private def quarter122_2 : Vector UInt64 25 :=
  #v[0x3375bc83cf96bc16, 0xc88e7552e757abf8, 0x2e816f7812aa1b7a, 0x165739fcd6f47006, 0x52c19841d84a8003, 0x1d5f3dcde642a7e1, 0x47f2737d3f29e859, 0x3bb3d01b5b855856, 0xa76f13002e8b60c4, 0x99a4295b36c1323a, 0xd728b8e223816810, 0xe7a5cb1a62ea08de, 0x7dcea6e531d3b663, 0x1d439dd2371aec7e, 0x25dcf0471c756d0d, 0x6c3e33499e0835c0, 0x33208b1ba106f01e, 0x96b844b169ee523f, 0x88804d6e99f4109b, 0xa2c698647f424301, 0xfa046a8e3392aca5, 0xec18b4c758fa7fb, 0x361ba94a10d3812b, 0xa0d4707a9e1f5911, 0xd2da322af0ae2bb5]

private theorem rounds122_1 : sixRounds 6 (by decide) quarter122_1 = quarter122_2 := by
  decide +kernel

private def quarter122_3 : Vector UInt64 25 :=
  #v[0x56e7b615c3b0250a, 0x462dfdbb2a734ec7, 0x4243cc78ed52402f, 0x51e5cf882f904b97, 0x313b9ae73f28ee3d, 0xa604f83177a16d67, 0x795823bd0606fb28, 0x588315c9d195cb26, 0x4d0b39dc5b98243d, 0x34f077495169812f, 0x17fe69d85c22731c, 0x700f0e4497cada4e, 0x411b0aaa58cd05c6, 0xd185a96b5b3c7f5, 0xc5dbca259b8b1070, 0x1956bf3f4c8258f5, 0x506c4ebe2681c606, 0x93a35d4454e99173, 0xf542dc25cb0e7791, 0xc6a97c0e8af3fa43, 0xbf524a04b875715c, 0x3f26e78580e66987, 0x9ff3b11e4ea4bf8, 0x864245afad2a92fe, 0x80b05f218a4d9a8d]

private theorem rounds122_2 : sixRounds 12 (by decide) quarter122_2 = quarter122_3 := by
  decide +kernel

private theorem rounds122_3 : sixRounds 18 (by decide) quarter122_3 = state123 := by
  decide +kernel

private theorem perm122 : KECCAK.f1600 absorbed122 = state123 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds122_0, rounds122_1, rounds122_2, rounds122_3]
  rfl

theorem block122 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes122 ++ tail) state122 =
      KECCAK.Bytes.run 0 tail state123 := by
  exact run_block_of_step bytes122 tail absorb122 state122 absorbed122
    state123 (fun _ => rfl) words122 perm122

private def absorb123 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0xbb 0x9c 0x5 0xa9 0x7f)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x90 0x71 0x30 0x61 0x52 0x90 0x17 0x0)) 5 (by decide) (UInt64.ofBytes 0x42 0x5b 0x56 0x27 0x47 0x61 0x90 0x84)) 6 (by decide) (UInt64.ofBytes 0x60 0x57 0x7b 0x41 0x61 0x15 0x10 0x84)) 7 (by decide) (UInt64.ofBytes 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x80 0x40)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x60 0x1e 0x60 0x52 0x1 0x82 0x4 0x60)) 13 (by decide) (UInt64.ofBytes 0x61 0x69 0x46 0x7f 0x52 0x1 0x82 0x24)) 14 (by decide) (UInt64.ofBytes 0x32 0x56 0x6e 0x65 0x6b 0x6f 0x54 0x74)) 15 (by decide) (UInt64.ofBytes 0x74 0x69 0x6d 0x72 0x65 0x70 0x20 0x3a)) 16 (by decide) (UInt64.ofBytes 0x69 0x70 0x78 0x65 0x20 0x73 0x69 0x20))

private def absorbed123 : Vector UInt64 25 :=
  #v[0x530f99fd7a8f6643, 0x7d918896fe01abe, 0x5f85da76b39dead5, 0xd10f6dd72b6ff5ee, 0x66c8dca10b8307fd, 0x74d933e5b05f7b2b, 0xecb0b758ab97b167, 0xa1b0ecc9c7925b80, 0x86dc41c6bf2d072a, 0xa58b985b0125925, 0xbe75f4fe049a3d6e, 0xbd78f9eb64dad3ce, 0x20b710a2c58b9f9e, 0x4d7e8cfe44f8c2ee, 0xe7e4639bb87cb268, 0xe2b85acde13f999a, 0xae465d663ed05548, 0xd0ecb84fcc9dba05, 0xd1c2ea820dc85646, 0x2b7e6a0c7ed4b5ac, 0x40be5693f40c64ba, 0x798ccefd86d0af28, 0x41558098b764eb6d, 0x3d882e049650aef3, 0xe996d909ab8ca4cf]

private theorem words123 : absorb123 state123 = absorbed123 := by
  decide +kernel

private def quarter123_1 : Vector UInt64 25 :=
  #v[0x60475d69119c3116, 0xb618958fa05e5d7c, 0x1e3d07bb6e64e767, 0xc13e980cd1cfb50c, 0x2b45d69511371676, 0xe8642a323fb850a4, 0x5e53498bfed93b7c, 0x68b869074bbe80d5, 0x83f228b14d58aa08, 0x9e0fc4798237b9e5, 0x519d6a5964e650b4, 0x7b5ef8147663cdf5, 0x9472336df63449aa, 0x242afa0c61f02dd9, 0x793232e79f0c154d, 0xfce06d0e7c82df8, 0x2edb124631f34d72, 0x348c82402487a797, 0xab73e422990266d8, 0x38779aae839f3b1f, 0xdc34a2f783413ee4, 0x8929d998ab580792, 0x8420af66419d540b, 0x74e374e3f5837a8, 0xc32d2b2ee0007428]

private theorem rounds123_0 : sixRounds 0 (by decide) absorbed123 = quarter123_1 := by
  decide +kernel

private def quarter123_2 : Vector UInt64 25 :=
  #v[0x573c6f1dd9c513d5, 0x821ae13da2fa0e87, 0x7a1b81c8337fcfef, 0x19005612bfec6d08, 0xb13e9c5ae2d76519, 0x1da4da9072389a76, 0xd8dfa98a862ced5c, 0x254242010fdcd26f, 0xb23f23a107e21da4, 0x48230ec67f8236c7, 0xc14a9eb2ac91126f, 0xc02c22666cba13d3, 0x7ee2539ea749e589, 0xac25cdc9b05a657a, 0x2b2268ede1be5961, 0xbfebee440d28cee1, 0xd706917a3380c1f3, 0x6c357b753444f242, 0x1aafd7aef419a129, 0x87fd019b8a8a1ea1, 0xd16721e6408c0853, 0x66084746a1c1cfd4, 0x60f021b4a06e4f59, 0xcd246f17620664d6, 0xece6520049216833]

private theorem rounds123_1 : sixRounds 6 (by decide) quarter123_1 = quarter123_2 := by
  decide +kernel

private def quarter123_3 : Vector UInt64 25 :=
  #v[0x139d8082eaf263f6, 0xee4433d6dbf2f49a, 0xfaca95d6c88974c6, 0x332bede1f3aecdcd, 0x5e1b70d0fd672317, 0xd946a630cf7727f3, 0x5033da56583b22ae, 0x96128da12a32cd67, 0xe8b6cb914517789d, 0x6008fb2a1a0f779a, 0xd28b5b67742ccb86, 0x5440d291ed502e12, 0x27e9653ea51483fd, 0x1d2ceb83ecf649ca, 0xb39d681ac3dda757, 0xe6eab31c4ee8bfc7, 0x7c94db64f3260ec0, 0xce9e7c0fe7365db3, 0x3ef63bcb71c5d94f, 0xacc41707e1fed202, 0x41f8ad74cb150785, 0x8964aa2521d4d2ca, 0x88547a67aa06acc6, 0xdb8e83fb1b7725aa, 0xe1735c5ef10323b2]

private theorem rounds123_2 : sixRounds 12 (by decide) quarter123_2 = quarter123_3 := by
  decide +kernel

private theorem rounds123_3 : sixRounds 18 (by decide) quarter123_3 = state124 := by
  decide +kernel

private theorem perm123 : KECCAK.f1600 absorbed123 = state124 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds123_0, rounds123_1, rounds123_2, rounds123_3]
  rfl

theorem block123 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes123 ++ tail) state123 =
      KECCAK.Bytes.run 0 tail state124 := by
  exact run_block_of_step bytes123 tail absorb123 state123 absorbed123
    state124 (fun _ => rfl) words123 perm123

private def absorb124 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x82 0x44 0x60 0x0 0x0 0x64 0x65 0x72)) 1 (by decide) (UInt64.ofBytes 0x3 0x90 0x81 0x90 0x51 0x90 0x52 0x1)) 2 (by decide) (UInt64.ofBytes 0xff 0x73 0x5b 0xfd 0x90 0x1 0x64 0x60)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x0 0x60 0x16 0x88 0x80 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x90 0x20 0x60 0x11 0x60 0x52 0x81 0x81)) 7 (by decide) (UInt64.ofBytes 0x20 0x90 0x82 0x91 0x40 0x60 0x52 0x81)) 8 (by decide) (UInt64.ofBytes 0x91 0x90 0x1 0x81 0x1 0x60 0x54 0x80)) 9 (by decide) (UInt64.ofBytes 0xae 0xed 0x71 0x6e 0x7f 0x51 0x82 0x55)) 10 (by decide) (UInt64.ofBytes 0x37 0x60 0x1f 0x4d 0x7f 0xb9 0xb1 0x12)) 11 (by decide) (UInt64.ofBytes 0xae 0xfa 0xa2 0x5f 0x10 0x10 0xef 0xf)) 12 (by decide) (UInt64.ofBytes 0x84 0x64 0x9c 0x16 0x4a 0x11 0x26 0x1)) 13 (by decide) (UInt64.ofBytes 0x92 0x1 0x81 0x92 0xc9 0x26 0x61 0x5d)) 14 (by decide) (UInt64.ofBytes 0x90 0x84 0x1 0x83 0x81 0x52 0x92 0x90)) 15 (by decide) (UInt64.ofBytes 0x1 0x82 0x60 0x60 0x16 0x8a 0x93 0x52)) 16 (by decide) (UInt64.ofBytes 0x52 0x90 0x89 0x1 0x81 0x80 0x60 0x52))

private def absorbed124 : Vector UInt64 25 :=
  #v[0x5db3ba5d2f52e555, 0x831d9817cdbf200, 0x7ae0ba68d3454561, 0xe38c230a967bee92, 0xcad45989a6b985c, 0x2f19fd2c9d7e997c, 0xbd8d72c0cb093e57, 0x1023923ddb6f8a66, 0x415451c9dd93604, 0x1acb5a9706aecebb, 0x183acc6b1a2cb3cd, 0x429b31dd59a765f2, 0x7aef6e7050eea4a7, 0x5e4bf6382f26b808, 0x57e2c0c19cfd90f2, 0xd50e4e9360b38227, 0xe92a05b5be9e9d95, 0x8cd1b0d2afe05969, 0x24cc9d6d77d7278b, 0x73460278e0eed88d, 0x1621a643cb7aa2f3, 0xb6eb1ff8ab1e41bb, 0x4324a8b46016bb29, 0xca8f7b7dbde4725, 0x7b9d5b66dd77aac4]

private theorem words124 : absorb124 state124 = absorbed124 := by
  decide +kernel

private def quarter124_1 : Vector UInt64 25 :=
  #v[0x4ca7338e405cf6c7, 0x34a713c396422dbf, 0x9950b5f8b6ec82c7, 0x4c388ac2c3166bab, 0x1a0295f549c64f71, 0x33f67644b5061717, 0xf0e9f6e61f507076, 0x98096756dd12b465, 0x6ede242fb0a2af83, 0x6dfc997349229fac, 0xc78680d96dfbfbda, 0x6a0be60625f50f3b, 0x24f15e5862a6e5e, 0x9a6e0ca59f94abd4, 0xb0822e6eba052be0, 0xc1316b9607991310, 0x4690773dc0a528ec, 0x52532e11f073520, 0xa2a1ee278601a9cd, 0x16e3440181c7f065, 0x7db8869c7d69c989, 0x7791bd0792ab8dc6, 0xe07dae0ae29e3b08, 0x6ef000681b4799bf, 0xd3de0d027ca974f8]

private theorem rounds124_0 : sixRounds 0 (by decide) absorbed124 = quarter124_1 := by
  decide +kernel

private def quarter124_2 : Vector UInt64 25 :=
  #v[0x53245fba0bada94, 0x4ee6537cf09dff9f, 0x33eae63667147d4a, 0x47ef0b0d7245860f, 0xdba673c2d4a16ca, 0x895b569b1185a67, 0x9ad197dd20f384cb, 0x69a762914e758074, 0xba95e86126032e1d, 0x47b1b8190a66e225, 0x110091522dff0da0, 0x5823961e37b7c03, 0x888ea7079c85691f, 0xc73aadfd866d4192, 0xfad135798f2072ce, 0x5ab1f71d5089d346, 0xbcda88cfdad76b0f, 0x59973a4b53bc2346, 0x77461042506b789a, 0x3ba70f47312e4b5d, 0xe59c7f8fcb389ccd, 0xb7928503c1a36888, 0x409efefd76eebaaa, 0x1988c8f272c5cd9, 0x413c0729b17f91ef]

private theorem rounds124_1 : sixRounds 6 (by decide) quarter124_1 = quarter124_2 := by
  decide +kernel

private def quarter124_3 : Vector UInt64 25 :=
  #v[0xc59d7be910bd3e36, 0xa4a35d93037090e9, 0x39f613c1c5a38803, 0xb3bda55f4f675214, 0xbe1e3a7a4b9264, 0xa0e55ffff2972198, 0xf7d4f18f5e009ddd, 0x6bcb124cfff14990, 0x92ed39715814d1b6, 0xf416552261954033, 0x618eb664235637b0, 0xac98d4bd1dab829e, 0xc32e8117ea427947, 0x418238bac7250d8f, 0x8a7c472191cc2c1, 0xa1c65233c53c98, 0x11a8ac36b8b5e756, 0x6fbcaaf609b47e17, 0x247c60bc05ee27e8, 0xf4c9544343962461, 0x9642c8819a214026, 0x2a0e1c348d2c3210, 0xc7a87facb0eaddac, 0xa71eb1d34c99417d, 0x7e58acdaacbf7366]

private theorem rounds124_2 : sixRounds 12 (by decide) quarter124_2 = quarter124_3 := by
  decide +kernel

private theorem rounds124_3 : sixRounds 18 (by decide) quarter124_3 = state125 := by
  decide +kernel

private theorem perm124 : KECCAK.f1600 absorbed124 = state125 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds124_0, rounds124_1, rounds124_2, rounds124_3]
  rfl

theorem block124 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes124 ++ tail) state124 =
      KECCAK.Bytes.run 0 tail state125 := by
  exact run_block_of_step bytes124 tail absorb124 state124 absorbed124
    state125 (fun _ => rfl) words124 perm124

private def absorb125 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x52 0x93 0x90 0x93 0x1 0x81 0xa0 0x60)) 1 (by decide) (UInt64.ofBytes 0x52 0x90 0x88 0x1 0x84 0x80 0xc0 0x60)) 2 (by decide) (UInt64.ofBytes 0x1 0x91 0x90 0x3 0x85 0x80 0x51 0x81)) 3 (by decide) (UInt64.ofBytes 0x90 0x1 0x93 0x90 0xe0 0x60 0x52 0x81)) 4 (by decide) (UInt64.ofBytes 0x90 0x1e 0x42 0x61 0x54 0xf 0x60 0x52)) 5 (by decide) (UInt64.ofBytes 0x56 0xb5 0x46 0x61 0x86 0x86 0x86 0x86)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x5b)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x14 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x51 0x80 0x40 0x60 0x57 0xa0 0x42 0x61)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8 0x7f)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x82 0x4 0x60 0x20 0x60 0x52 0x81 0x0)) 15 (by decide) (UInt64.ofBytes 0x1 0x82 0x24 0x60 0x1a 0x60 0x52 0x1)) 16 (by decide) (UInt64.ofBytes 0x31 0x36 0x32 0x50 0x49 0x45 0x7f 0x52))

private def absorbed125 : Vector UInt64 25 :=
  #v[0x2b13e813ec60b91, 0xcc59597e52357dee, 0x28c812c6f7f8beea, 0x4d981a557fe9a139, 0x1bdaea300513ab6c, 0xaf9815889850a2b8, 0x12ed9c923c57e963, 0xbbedf4f3241ca24, 0x6d6d27bec25aed69, 0x24e4c87c034bfd6, 0x9e053cfd49f0f7ac, 0x22ae8195e0762eb2, 0x614fef1138f0d06e, 0x99f208a9d02ac9b2, 0x9cc3f1881093bcb5, 0x859dbcc18bc3d732, 0x55575bfcfadaf708, 0xeba90dddd4f3177b, 0xc51757df17f527f, 0xe65116c729d2c2e1, 0x1673a13f7525ae69, 0x57c0df1a6a1519ca, 0x32b2387217c0fd1c, 0x4c2876eb964891b3, 0xca66da9c3e5703b6]

private theorem words125 : absorb125 state125 = absorbed125 := by
  decide +kernel

private def quarter125_1 : Vector UInt64 25 :=
  #v[0x256b120a0680e61d, 0x3051168faed93891, 0xa86be763bb906a73, 0x5bb32b3fc6e5b6b7, 0x984b36cb792c91ce, 0x12b6f236f2fa2275, 0xbc0f06e88169f06b, 0xdc7997aa10ca426, 0xa145f6ec2022055a, 0xb5340ab683fcfb3f, 0x1aa765753cb868c1, 0xdbab1fb6e3261da5, 0x922b54ac628bfacb, 0xe103422cd0676ed, 0xa40258891fab778a, 0x113c545c597424af, 0x555e43b16b8dc77, 0x9a3e5a4dde7e7745, 0x87a7e39106dd23a3, 0xcfa5975a470f48b4, 0xc0a287d2c9a676bd, 0x7e6be2da8539dfca, 0xf7eee5e6943c116e, 0x547e4b78c221bf6d, 0xd1ead7c6f0337bb0]

private theorem rounds125_0 : sixRounds 0 (by decide) absorbed125 = quarter125_1 := by
  decide +kernel

private def quarter125_2 : Vector UInt64 25 :=
  #v[0x7a09a7832def59b4, 0xef31a89184ec5c6e, 0xef5e4f6ab741330e, 0x447e6e43f54f48c0, 0xb3e8e9db08db9893, 0xa43c0fd96d5f28e2, 0x7520e3284667f8a6, 0xa5c9465b485b68dd, 0x20a8a7318389dd8f, 0x413e6760ceecb76b, 0x6059f6264647e598, 0x890a50a4258a36d, 0xaa8fc5880c50e251, 0x981252bc556eb8d1, 0xa68ff31355297888, 0xf18e9fc80d47a45, 0xc07fe39c31ed9423, 0x5d25864e5fe43445, 0x9aebd005702984dd, 0x134eb7c41542435b, 0x9c637a7ea9955e66, 0x37c595939f7860a3, 0x80ff94990f219e78, 0x5a124bc590086504, 0xf6aaee5c7cd1a58b]

private theorem rounds125_1 : sixRounds 6 (by decide) quarter125_1 = quarter125_2 := by
  decide +kernel

private def quarter125_3 : Vector UInt64 25 :=
  #v[0x11e70f9f609cb53e, 0x3700fd68b22dc9e0, 0xff37ed8577c7a8b, 0x3ba2bb77373a3b04, 0x20a6a080e45ccd7b, 0x63d01e95dfde4844, 0x80fb454313d2d859, 0x5d29191aaa8a8e1b, 0xe2b3ba6c22d1c374, 0x87b20877f5c3bbd1, 0xb4494e6827d3aafa, 0x3838d8d2bc72fcd8, 0x80997ce05bf247bf, 0xaf208af2610fc680, 0x39aa1a9add3177f5, 0xee220a0590ee0a1c, 0x1ab6b49179d85897, 0xb2925aa6feb9a76c, 0x9cb5cb0805f4870f, 0x80bd19aa64f086b3, 0x87f0d4fe62cfd9ee, 0xf4890277e7c03eb0, 0x489966586437ee61, 0x4b4f8e67efc723c0, 0xbf1f6304ed6c2162]

private theorem rounds125_2 : sixRounds 12 (by decide) quarter125_2 = quarter125_3 := by
  decide +kernel

private theorem rounds125_3 : sixRounds 18 (by decide) quarter125_3 = state126 := by
  decide +kernel

private theorem perm125 : KECCAK.f1600 absorbed125 = state126 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds125_0, rounds125_1, rounds125_2, rounds125_3]
  rfl

theorem block125 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes125 ++ tail) state125 =
      KECCAK.Bytes.run 0 tail state126 := by
  exact run_block_of_step bytes125 tail absorb125 state125 absorbed125
    state126 (fun _ => rfl) words125 perm125

end Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
