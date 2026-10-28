import Blanc.Lift.Usdc.ImplV2_1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb114 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x90 0x40 0x60 0x52 0x20 0x60 0x9 0x60)) 1 (by decide) (UInt64.ofBytes 0x77 0x3c 0x61 0x15 0x11 0x81 0x54 0x20)) 2 (by decide) (UInt64.ofBytes 0x79 0xc3 0x8 0x7f 0x51 0x40 0x60 0x57)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0xa0)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x82 0x1 0x20 0x60 0x80 0x80 0x1 0x4)) 8 (by decide) (UInt64.ofBytes 0x52 0x81 0x26 0x60 0x52 0x82 0x3 0x81)) 9 (by decide) (UInt64.ofBytes 0x60 0x1c 0x50 0x61 0x80 0x1 0x20 0x60)) 10 (by decide) (UInt64.ofBytes 0x50 0x91 0x1 0x40 0x60 0x39 0x91 0x26)) 11 (by decide) (UInt64.ofBytes 0x90 0x3 0x91 0x80 0x51 0x40 0x60 0x50)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x5b 0xfd)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x83 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x9 0x60 0x52 0x81 0x90 0x0 0x60 0x16)) 16 (by decide) (UInt64.ofBytes 0x54 0x20 0x90 0x40 0x60 0x52 0x20 0x60))

private def absorbed114 : Vector UInt64 25 :=
  #v[0xd0c15c432832e973, 0xc78e3da56f2253e6, 0x6b51bd3b0f6e2b8a, 0xe37ff81e668b0521, 0xe5f166f61b81b178, 0x34cb51eaf4de2db2, 0x223cabad33b35e6f, 0x5e77943435ede6ca, 0x9a15794c9f443f88, 0x9fc602c54a0e3fe7, 0xc29ecb55699d231c, 0x533593d5bd70a054, 0xbbbd9e56a9c7d53e, 0xd0953acc32a34c84, 0x90d9333f8c08fee1, 0xd96197c8dac6eb97, 0x13d9500153b012ad, 0x64686ab803708efd, 0xd7bd0da03deeecd0, 0x5dc22068d43b675a, 0x758e17ca33730fda, 0xe6dd02cfea8fec21, 0xeea3d74ade84f15b, 0xc8d1ecd36f684f1f, 0x4e8c996bbca6357f]

private theorem words114 : absorb114 state114 = absorbed114 := by
  decide +kernel

private def quarter114_1 : Vector UInt64 25 :=
  #v[0x45a5fd2594a17fbd, 0x8b68fad3804a9c49, 0x71692c7edc18dd3b, 0xbb273f5a112f6b15, 0xba739dcbf1dadf10, 0x1ddb9c23423e108, 0x6134514ba448032f, 0xfe087349b921c75b, 0xb61ca0698dc72199, 0x39b476fc2aaecf86, 0x960cac465fba8fda, 0xd105c101a316d9a7, 0xd80a85039575b8b8, 0x921b08d2be0334a2, 0xac4dd2adb7765b80, 0xf96c550d7bce6cb3, 0xf9ceab7bdccdd85, 0xf14f55070d19aca9, 0xd23bc4d20eebd9a6, 0xd36e3c217b1ae392, 0xbc4bc9574fbaab52, 0xefba57632761ba8f, 0xb05e4b09e4da2104, 0xac6617fbba4f0b3c, 0x3dad0b1298f9832e]

private theorem rounds114_0 : sixRounds 0 (by decide) absorbed114 = quarter114_1 := by
  decide +kernel

private def quarter114_2 : Vector UInt64 25 :=
  #v[0x5e750de855067647, 0x43cab3e7a13ac4e2, 0x1c11cf3ea43768ea, 0xc970a3532503c5be, 0x6dd3346cb02c8109, 0xd50d3b76bb1b5f9e, 0xdd36120be2417342, 0xaf554a14d9091ca, 0xd81f25580045f604, 0x446dd525f955d85a, 0xa6224d748a62a6db, 0x151840b3bfd1cd8b, 0x57fd824d170128ff, 0xfae0d17afbbb554b, 0x6ed687cfb2b7aaae, 0xca5b42c23e9ab620, 0xa7c68b110f7e19f, 0xe0b6a0d09396f878, 0xf5eb64de37ac17b9, 0x2b3f60995a52cd36, 0xd0dc7adb4cc63dee, 0x73ca48a327bdac92, 0x32340ff6fde41536, 0xdb7765cd1180da85, 0x3d39d02073dfe577]

private theorem rounds114_1 : sixRounds 6 (by decide) quarter114_1 = quarter114_2 := by
  decide +kernel

private def quarter114_3 : Vector UInt64 25 :=
  #v[0xa45d1addc7d81118, 0xecf4dfd15d256f1, 0xf8bd0b828095a655, 0x1ec6acc6f7fa3c17, 0xbf1d0c7adf58656f, 0x2503640a4d7f78af, 0x28d6b893ad852281, 0x4303d375860abf8d, 0xfed0af142812775, 0x937e858b4045ef8d, 0xbe335e6651de2558, 0x6e64f57add4adea5, 0x85b3838225324125, 0x52761eafbe7f6fc8, 0x7b15441687b8f677, 0x461510715f2e851a, 0xe1bf472c1f7e372e, 0x660ec63139e68b7d, 0x871d043e19742d6c, 0x395b12984a665e40, 0xd01d35b456548fa8, 0xae74b0fe3c4ac229, 0x89c9bb23f8323671, 0xaf69fb0dd3f8cbd7, 0x1adf8710f5c82a1e]

private theorem rounds114_2 : sixRounds 12 (by decide) quarter114_2 = quarter114_3 := by
  decide +kernel

private theorem rounds114_3 : sixRounds 18 (by decide) quarter114_3 = state115 := by
  decide +kernel

private theorem perm114 : KECCAK.f1600 absorbed114 = state115 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds114_0, rounds114_1, rounds114_2, rounds114_3]
  rfl

theorem block114 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes114 ++ tail) state114 =
      KECCAK.Bytes.run 0 tail state115 := by
  exact run_block_of_step bytes114 tail absorb114 state114 absorbed114
    state115 (fun _ => rfl) words114 perm114

private def absorb115 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x4c 0x3d 0x61 0x82 0x90 0xa7 0x3c 0x61)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x5b 0x56)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x80 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x90 0x0 0x60 0x16 0x85)) 5 (by decide) (UInt64.ofBytes 0x82 0x80 0x40 0x60 0x52 0x20 0x60 0x9)) 6 (by decide) (UInt64.ofBytes 0x16 0x84 0x90 0x55 0x93 0x90 0x93 0x20)) 7 (by decide) (UInt64.ofBytes 0x90 0xe3 0x3c 0x61 0x54 0x20 0x52 0x81)) 8 (by decide) (UInt64.ofBytes 0xff 0x73 0x5b 0x56 0x26 0x3e 0x61 0x82)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x0 0x60 0x16 0x84 0x80 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x90 0x20 0x60 0x9 0x60 0x52 0x81 0x81)) 13 (by decide) (UInt64.ofBytes 0x20 0x90 0x82 0x91 0x40 0x60 0x52 0x81)) 14 (by decide) (UInt64.ofBytes 0x81 0x85 0x51 0x80 0x55 0x94 0x90 0x94)) 15 (by decide) (UInt64.ofBytes 0x16 0x87 0x92 0x93 0x91 0x51 0x90 0x52)) 16 (by decide) (UInt64.ofBytes 0xe2 0x1b 0xad 0x52 0xf2 0xdd 0x7f 0x92))

private def absorbed115 : Vector UInt64 25 :=
  #v[0x395710f632edb4a6, 0x597b7cf364006ccb, 0xc98dee88a99da727, 0x3784ad60b9465765, 0xffafad2a94afb716, 0xa1caa07f11eea92f, 0xb86d2ad12f1b6303, 0xc65ca0d633c8e27c, 0x8464abd123cdc317, 0x5a4b254c24f929f4, 0xd1503c4b7832f80c, 0xc9b9b9b2f5f5d58a, 0xb8e7af2d9dc19fd8, 0x8413fcc8f8fa6082, 0x8f598d0ba085ebe5, 0x3c1ccff446f2107d, 0x251536da338c2c99, 0x50e1e513dad45834, 0x26983f54459e1a37, 0x3acfc038b289113d, 0x3cf261462527df7e, 0x3b1e05acf23914eb, 0x3a61e6ef4bfbd9ba, 0x9bb8784f6e34425, 0x4b1691a9b3b1d856]

private theorem words115 : absorb115 state115 = absorbed115 := by
  decide +kernel

private def quarter115_1 : Vector UInt64 25 :=
  #v[0x7e3dd1aee00ef6cf, 0x201f39a644e4188, 0xd7fae9221098fd, 0xf942fe9178e421a7, 0x6ea1086ed221cbf5, 0x9a6613c69800823d, 0x5ffa4a24ae1291e8, 0x4dd9526f0c47db65, 0xd88c373e07e27de2, 0xc43f60167826eec1, 0x353b337febc04cc4, 0xbef7f667c92c40eb, 0x8fb39ffbc430cf0d, 0x51481b39ce1d2ab8, 0xaae290d81a6c92c4, 0xf63599765e2f266d, 0x71d43dc921e30221, 0xc6c5678cced06ce5, 0x1a14ad9a2b1be598, 0x11dd807e4e18e099, 0xe3e814abb8ded606, 0xb3fbe4cfdd250368, 0x3331cf42b5f193de, 0xcd6b55aa8c914ae9, 0x1fe2a7fde6bfbdd5]

private theorem rounds115_0 : sixRounds 0 (by decide) absorbed115 = quarter115_1 := by
  decide +kernel

private def quarter115_2 : Vector UInt64 25 :=
  #v[0xc080c6211ccb7c68, 0x610b5e403f78c71a, 0x490680d442a4779a, 0x832eb271c3a54d24, 0x8c13833bf256b0ce, 0xce558937b8fb68d3, 0xdce25bbcc43ec5bc, 0xd10ece32d20a46c0, 0xc330cccd47230c01, 0x4431f13ee6c91b46, 0x4c3aa72752e1b2a9, 0xa07d23ba094251c2, 0xbf7e7593d414da39, 0x26882398155f61f6, 0x9ee536aa18b37916, 0xb197e4231487eff9, 0x979d3469b107439a, 0x79e5052e82fe16fc, 0xfddfa0decdd80d81, 0x788a779cbe328ecd, 0xe0e0c3d1d9a8fc7a, 0x63ee89a35b9fcb42, 0x34bf4af506930cdc, 0x380bbcf2e5504714, 0xdf55d17e00afce4d]

private theorem rounds115_1 : sixRounds 6 (by decide) quarter115_1 = quarter115_2 := by
  decide +kernel

private def quarter115_3 : Vector UInt64 25 :=
  #v[0x913c27f328fb4a57, 0x1a52994789dfc412, 0x65b04a60c098b0ef, 0x8005baa6788e4f86, 0x20d848148fe3917b, 0x57a8bbed77a35424, 0x4a3dd20ac4bff7d8, 0xd5cd8650326fd821, 0x2896b88236622bd3, 0xdf35ef5b79face4c, 0x53cafddb867014db, 0x2fa3b0d33575cd62, 0x99066bd623b5fda5, 0x8891d661321f814e, 0x4f06d2a9390cd900, 0x85d5eb991f80fc34, 0x2366d07302e58aab, 0x80ca54130e49902, 0x7bd65a86580fddb4, 0x1fa478e162726d44, 0x8b8865a208a1ddc5, 0xe2c7ecf1ed842f24, 0xc5ea9e8f97dd4b09, 0x67a1033170bede29, 0x2a2cea3c3a6a1211]

private theorem rounds115_2 : sixRounds 12 (by decide) quarter115_2 = quarter115_3 := by
  decide +kernel

private theorem rounds115_3 : sixRounds 18 (by decide) quarter115_3 = state116 := by
  decide +kernel

private theorem perm115 : KECCAK.f1600 absorbed115 = state116 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds115_0, rounds115_1, rounds115_2, rounds115_3]
  rfl

theorem block115 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes115 ++ tail) state115 =
      KECCAK.Bytes.run 0 tail state116 := by
  exact run_block_of_step bytes115 tail absorb115 state115 absorbed115
    state116 (fun _ => rfl) words115 perm115

private def absorb116 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x37 0xfc 0x68 0xb0 0xc2 0x69 0x9b 0xc8)) 1 (by decide) (UInt64.ofBytes 0xc4 0x63 0xf1 0xa7 0x2b 0x95 0xaa 0x8d)) 2 (by decide) (UInt64.ofBytes 0x23 0xf5 0x4d 0x5a 0xf5 0x28 0x16 0xa1)) 3 (by decide) (UInt64.ofBytes 0x1 0x3 0x90 0x82 0x91 0x92 0xef 0xb3)) 4 (by decide) (UInt64.ofBytes 0x60 0x5b 0x56 0x50 0x50 0x50 0xa3 0x90)) 5 (by decide) (UInt64.ofBytes 0x40 0x60 0x83 0x83 0x8e 0x3d 0x61 0x0)) 6 (by decide) (UInt64.ofBytes 0x52 0x40 0x60 0x1 0x40 0x60 0x80 0x51)) 7 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x1e 0x60 0x80)) 8 (by decide) (UInt64.ofBytes 0x74 0x61 0x4d 0x65 0x66 0x61 0x53 0x7f)) 9 (by decide) (UInt64.ofBytes 0x72 0x74 0x62 0x75 0x73 0x20 0x3a 0x68)) 10 (by decide) (UInt64.ofBytes 0x6f 0x20 0x6e 0x6f 0x69 0x74 0x63 0x61)) 11 (by decide) (UInt64.ofBytes 0x0 0x77 0x6f 0x6c 0x66 0x72 0x65 0x76)) 12 (by decide) (UInt64.ofBytes 0x56 0x76 0x45 0x61 0x50 0x52 0x81 0x0)) 13 (by decide) (UInt64.ofBytes 0x5b 0x56 0x50 0x50 0x50 0x92 0x93 0x5b)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x7f 0x54 0x80 0x0 0x60)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0xff))

private def absorbed116 : Vector UInt64 25 :=
  #v[0x11159267ffc83f11, 0x4aefcc3cb326d77, 0xa74d23df1ea65344, 0xbcd7d34798a83f06, 0x6e50c3f206dc55c9, 0xef4fc05b7032f381, 0x662a94ab4869ebd7, 0x4b253159b3777357, 0xedc743497652c417, 0xa464c67ae210e16c, 0x67cd78086b516d26, 0x5cf7622bd65f274e, 0x874c7d7ee05978e4, 0x46de928b89bff58c, 0x782b82f95c217e4d, 0xfe665886f19d41e9, 0x7e81b275556a6a2f, 0xc72d93425449db3f, 0x9c9e10e008c6ce9e, 0x477bb5506950efc7, 0xde48d212c60923e7, 0x4a47f63bc4465dc1, 0x6f2cef7ae34dd0c0, 0x8211f36b8a44394a, 0xd245ee370df94c39]

private theorem words116 : absorb116 state116 = absorbed116 := by
  decide +kernel

private def quarter116_1 : Vector UInt64 25 :=
  #v[0x26db0902fbc8d523, 0xf5593723d22b3e25, 0x9b248685fc1de979, 0x29753b593fdfa20b, 0x9ebf307bd1abea37, 0xa687c93a49e30d90, 0x9fbdaeb1d4305f09, 0x90a97635dc43d238, 0x4b108903ce3343f9, 0xc0fe0922a2eedfeb, 0x645bd36abaef8e4e, 0xf76e4e1417358a2d, 0x148e3ea56e6b9cf1, 0xda57602f333648b, 0x5b9b221f1c99a5ae, 0x71c702ddd413065a, 0x6a13f111d33b3fc1, 0x1efb14b1365d988a, 0xdb0a3f659d901dea, 0x5471c30bce297600, 0x569846d53ae69d99, 0xf139d1406525bd6b, 0x1682488cfb651346, 0x1be0d5457cbd0024, 0x8c55d7dea32e8053]

private theorem rounds116_0 : sixRounds 0 (by decide) absorbed116 = quarter116_1 := by
  decide +kernel

private def quarter116_2 : Vector UInt64 25 :=
  #v[0x31bab384a4c7108b, 0xd97bf1d5a5d33372, 0x8282a799e74f7941, 0xd9631cba31300925, 0xd7ea7d264d003e0c, 0xf067b313d1a4cd42, 0x6c454f4547b452e5, 0x6973c357bbd094ae, 0xa3f4c512d9c74f90, 0x4daf39467aa7408e, 0x5b9cded36e5cf48e, 0x5ed1b5e71d153cab, 0x565ff8fa05a0dde8, 0xcf20c7ea3888ce16, 0xa200ad08a81e903a, 0x43357635e3f378f2, 0x33c32f72ad2a16f7, 0x70d768c20ea4f61d, 0x50d2a5d4d34518b5, 0xb3cd696cbe84f748, 0xa7bd12ee6453d660, 0xfe5bac26113faa27, 0xf3a4ef6a3c7b7af9, 0x3cf256a9163283b2, 0x1c55b1fcf8c278bf]

private theorem rounds116_1 : sixRounds 6 (by decide) quarter116_1 = quarter116_2 := by
  decide +kernel

private def quarter116_3 : Vector UInt64 25 :=
  #v[0xd303d4cc17d1a0a5, 0xf7388460e39f902a, 0x7a60b146f26c802b, 0x4d9739e72db8e7bb, 0x9256a1d096de2, 0xc3be489fb771dfc8, 0x9662535f6bb443cb, 0x9397ac09aa154434, 0xbb8aba293c8f6c05, 0xb85d42fbcdeea0d2, 0xb37bce04529fa326, 0x5237d49e8e570c8c, 0x1164663346ab7767, 0xcb0be17e6da3adbf, 0x19c8d20a38fcd14a, 0xe6e4ddf3319a2d72, 0x382885931b32aa79, 0x9ec0f0c500f8b9ce, 0x8db8d8b19c4f1a80, 0x1fb475de9f96956a, 0x5352764c444e6583, 0x6d8c1a4b7e11ed4, 0x245ebfb9ca551307, 0xc4e0e37b6a524ba2, 0x26cd08493aab5536]

private theorem rounds116_2 : sixRounds 12 (by decide) quarter116_2 = quarter116_3 := by
  decide +kernel

private theorem rounds116_3 : sixRounds 18 (by decide) quarter116_3 = state117 := by
  decide +kernel

private theorem perm116 : KECCAK.f1600 absorbed116 = state117 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds116_0, rounds116_1, rounds116_2, rounds116_3]
  rfl

theorem block116 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes116 ++ tail) state116 =
      KECCAK.Bytes.run 0 tail state117 := by
  exact run_block_of_step bytes116 tail absorb116 state116 absorbed116
    state117 (fun _ => rfl) words116 perm116

private def absorb117 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0xff 0x73 0x16 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x91 0x16 0x92 0x90 0x92 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x73 0x5b 0x56 0x55 0x90 0x17 0x91 0x90)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x60 0x16 0x84 0x80 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x20 0x60 0xa 0x60 0x52 0x81 0x90 0x0)) 10 (by decide) (UInt64.ofBytes 0x20 0x83 0x80 0x40 0x60 0x52 0x81 0x90)) 11 (by decide) (UInt64.ofBytes 0x52 0x90 0x92 0x52 0x83 0x16 0x86 0x93)) 12 (by decide) (UInt64.ofBytes 0x90 0x84 0x90 0x71 0x30 0x61 0x54 0x20)) 13 (by decide) (UInt64.ofBytes 0x61 0x85 0x90 0x21 0x3e 0x61 0x90 0x84)) 14 (by decide) (UInt64.ofBytes 0x56 0xda 0x39 0x61 0x5b 0x56 0x26 0x3e)) 15 (by decide) (UInt64.ofBytes 0x81 0x83 0x1 0x82 0x82 0x0 0x60 0x5b)) 16 (by decide) (UInt64.ofBytes 0x40 0x60 0x57 0x8e 0x3d 0x61 0x15 0x10))

private def absorbed117 : Vector UInt64 25 :=
  #v[0xb8f073813b5b02f3, 0xb1a9238057151025, 0xfca241783abbf234, 0xa9e2d11695578861, 0x248cb14cee76d76c, 0xce15a6949d832f27, 0xcbef7238a23afc8a, 0x97090cdad77857e3, 0x1232cb93545ca135, 0xc897efad3e99102f, 0xe079ec8413d46746, 0x1a9e7deb3d53993e, 0xa56ffc8f3c50d9ce, 0xbc18128f8b9d5521, 0x9f8de73f2abb8cc7, 0xbd8b5c5a4ee168b4, 0xb500c1aca3bcef28, 0x49239e4e36b8ec4, 0x3b8c558d69375e6, 0x28c156413a20debd, 0x306d0e23fa2bebeb, 0x7aede3c8bd271005, 0xdc78e1fcdd8dded, 0xf575b4a03bd17d6b, 0x98acf8881d2743ff]

private theorem words117 : absorb117 state117 = absorbed117 := by
  decide +kernel

private def quarter117_1 : Vector UInt64 25 :=
  #v[0xe0b7c087713b269d, 0xcb795a5f9cbdabcf, 0x563a3fbbf6b9ba21, 0xd9e0d17912ed6527, 0xe224bc67bb0e7de4, 0xe71f56cba971e149, 0xfc2bf5a7ddf6652e, 0x772937e6ca7762ce, 0xd852856c77627c32, 0xeda7d1f5096f7f17, 0x715eccd699009dcc, 0xd6a7a59707d307d8, 0xb2c2040139ab368d, 0xdbe23c14168e015, 0xb510b39af3162e4e, 0xb15c322c105e2335, 0xd3ebd6e392e4a784, 0xbeb3f33db9081114, 0x56d47e977ce34ed5, 0xef495de2b9417e51, 0x30c6875fc5b3cdf1, 0xd13458b0e40a5261, 0x14903c3cb1157ce7, 0x40dccacbc1bad6f, 0xbaa99a1b34db0fb8]

private theorem rounds117_0 : sixRounds 0 (by decide) absorbed117 = quarter117_1 := by
  decide +kernel

private def quarter117_2 : Vector UInt64 25 :=
  #v[0x41535457433a11c9, 0x308101e223665234, 0xd14f2fb947353432, 0x1446f2ef98369e77, 0x2ba9d0efc56339b1, 0x6e6e7cd99494ac3, 0x609434ba6a7909f0, 0x8532ea87efd9f917, 0xbb3bb4ca999d5b75, 0xcca038a2c4becf12, 0xa933d7853b17cc08, 0xad5fd8e9f1738c6f, 0xf7b811664b771a37, 0xfd16ab9de48ce237, 0x630e1f65cf487956, 0x96b56ecebb8f1636, 0xce1d7b4dd1dfdf17, 0xe749d97372e71bfa, 0x4b44f6bf5649d32d, 0x28e1571380d21a6, 0x2aa50a9b026271bf, 0x7a5b557c1b1e472e, 0xadbca4ee30562327, 0x902cde4e34ffc54f, 0x21346d45b8003bf9]

private theorem rounds117_1 : sixRounds 6 (by decide) quarter117_1 = quarter117_2 := by
  decide +kernel

private def quarter117_3 : Vector UInt64 25 :=
  #v[0x232abd8defac06ef, 0x2072ff3cededacfb, 0x9db7acbb1ede2334, 0x6bf15cba9a005271, 0xd1d03379a7b316c2, 0x296641447d451fce, 0xfeb3cbcdee32ac24, 0x778fa652d3552d31, 0x93138d95efb27e61, 0xd2eae2ff74f89b3a, 0xc7097e33f168c996, 0xdff52f2487189e0d, 0x13aca4eb1f005fb6, 0x60e92c5d7918f4ea, 0xcb73c582c216b1dc, 0x65cc91e84937c0e8, 0x6d68d1f516b7c603, 0xc4b0c81deee8944c, 0x6d668a037774035a, 0x79b38f08715c6117, 0x266adc07c8555c76, 0xc9bfecbff4223e45, 0xadd5113f9411225e, 0xafb62b9157a2bc88, 0x9706630822e43311]

private theorem rounds117_2 : sixRounds 12 (by decide) quarter117_2 = quarter117_3 := by
  decide +kernel

private theorem rounds117_3 : sixRounds 18 (by decide) quarter117_3 = state118 := by
  decide +kernel

private theorem perm117 : KECCAK.f1600 absorbed117 = state118 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds117_0, rounds117_1, rounds117_2, rounds117_3]
  rfl

theorem block117 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes117 ++ tail) state117 =
      KECCAK.Bytes.run 0 tail state118 := by
  exact run_block_of_step bytes117 tail absorb117 state117 absorbed117
    state118 (fun _ => rfl) words117 perm117

private def absorb118 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x80)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x60 0x20 0x60 0x52 0x81 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x24 0x60 0x1b 0x60 0x52 0x1 0x82 0x4)) 6 (by decide) (UInt64.ofBytes 0x65 0x66 0x61 0x53 0x7f 0x52 0x1 0x82)) 7 (by decide) (UInt64.ofBytes 0x64 0x61 0x20 0x3a 0x68 0x74 0x61 0x4d)) 8 (by decide) (UInt64.ofBytes 0x6f 0x20 0x6e 0x6f 0x69 0x74 0x69 0x64)) 9 (by decide) (UInt64.ofBytes 0x0 0x77 0x6f 0x6c 0x66 0x72 0x65 0x76)) 10 (by decide) (UInt64.ofBytes 0x1 0x82 0x44 0x60 0x0 0x0 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x60 0x3 0x90 0x81 0x90 0x51 0x90 0x52)) 12 (by decide) (UInt64.ofBytes 0xa4 0x3e 0x61 0x5b 0xfd 0x90 0x1 0x64)) 13 (by decide) (UInt64.ofBytes 0x60 0x5b 0x56 0x27 0x46 0x61 0x85 0x85)) 14 (by decide) (UInt64.ofBytes 0x9e 0xa 0x8b 0x15 0x7f 0x51 0x80 0x40)) 15 (by decide) (UInt64.ofBytes 0x3c 0xf6 0x2 0xad 0x8a 0x82 0x7a 0xdf)) 16 (by decide) (UInt64.ofBytes 0xa8 0xb 0xf5 0xf2 0x8e 0xc6 0x15 0xd5))

private def absorbed118 : Vector UInt64 25 :=
  #v[0xdbf3df319b4fa92e, 0x550c8121672e6af9, 0x4e65a1b5a7df462d, 0x133f91d55f69c828, 0xa9a66291c0e5d3b9, 0xcffef48dc49dcd4c, 0xb2fae9c607ced4ce, 0xeb405072fabd69ba, 0xd466e8aa0c26f2be, 0x2f78f9e233aa3a13, 0x950b98b488f252c6, 0x5f0b6d0d606f1edd, 0xb0185ad76f7f07bd, 0x83762e3616a08066, 0x52dd20d9f0a52e9b, 0x300129322d9e8c97, 0xca51b1e6468c841f, 0x4d233894403261a2, 0x59320438f805e8b2, 0xb52cb0482f820a50, 0x7449932760b8fac6, 0x2a79386055482ecd, 0x484edceb3758e5b2, 0x97a88a47b5d113f4, 0xe4214a634643721f]

private theorem words118 : absorb118 state118 = absorbed118 := by
  decide +kernel

private def quarter118_1 : Vector UInt64 25 :=
  #v[0xbcaba95a541e033f, 0xa14c1b7e333913e1, 0xb7d64cf010629b24, 0x2398173d046b666c, 0x383cb45aca63ebab, 0x9f608d5bda9776b7, 0xd24629ec86606abb, 0x1331e845373b6574, 0xc9f0c9186bedc15f, 0x1e3de379a9d63483, 0x113bc6dbfa8a1f55, 0x915f2e6024230667, 0x133108292fe50a0, 0xcbcf0dd1c78ded5, 0x32c115aaf6ff90d2, 0x997e603ca074323f, 0xa84bb8d97bc70633, 0x8e82fe226afcd420, 0x4f3265c6ff82c63b, 0xc4ecb1cc0459d97, 0xc2bae1236609d902, 0xa818ce5f7e236797, 0x79ab7e374fc23cec, 0x10a29d9756d0b661, 0x769c8afcaf8efb82]

private theorem rounds118_0 : sixRounds 0 (by decide) absorbed118 = quarter118_1 := by
  decide +kernel

private def quarter118_2 : Vector UInt64 25 :=
  #v[0x4e997144a732fa3e, 0x98574cb060d5837a, 0xd39aa1e7ec96886b, 0xc24579a7efb36039, 0xbfc3c99c00fdf2de, 0x64f2d7d5d94a2a72, 0xfc840d3d717d1bb3, 0x687b82ded3e5e2b2, 0xba260880371bfa8b, 0x26070e7ac46656ab, 0xb6f79f20e593cf48, 0x83b57e344712739e, 0x8a325c2355422e33, 0x4619b8f3025019f1, 0x2a43423f87d3f076, 0x87ea33955257c7cf, 0x31aa349b74ff4dc4, 0xf367be0aa5786772, 0x15dd99454af420a0, 0xe1a5a858c4b0d6a8, 0xf678be1b9d08a4a9, 0x97867a3d855e3f93, 0x628c708e251b2118, 0x3d9ba72b4e0901fc, 0x4ced8f09b1f7508a]

private theorem rounds118_1 : sixRounds 6 (by decide) quarter118_1 = quarter118_2 := by
  decide +kernel

private def quarter118_3 : Vector UInt64 25 :=
  #v[0x96ca132d328d8eab, 0xc84362684f7a95c6, 0x979efa45a60270d3, 0xf5619f5f63f8bcd4, 0x7b1fd29e52f2a6dc, 0xbeb99aea382c468b, 0xbde1b3a6701fedb4, 0x5fb28544fc3aa738, 0xe8afd38c4339536f, 0x65e312aacf9a187e, 0xa2865be6b8bb5dce, 0xbf7598609eb6a414, 0x1bc36eeb9579b408, 0x6863371c209dae84, 0xc6a59f9a90693c09, 0x66f647a8c921886f, 0xf590f21ac6e82158, 0x1f13b020c73b0b84, 0xaae7a39ee9485dde, 0xf89b2a3a34c67047, 0x6ce43762c8c0bdab, 0xcd3d2fee523369e8, 0x6bbf43e6b51c5237, 0xb89601e069304fe6, 0x57fa90c0c6e1614c]

private theorem rounds118_2 : sixRounds 12 (by decide) quarter118_2 = quarter118_3 := by
  decide +kernel

private theorem rounds118_3 : sixRounds 18 (by decide) quarter118_3 = state119 := by
  decide +kernel

private theorem perm118 : KECCAK.f1600 absorbed118 = state119 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds118_0, rounds118_1, rounds118_2, rounds118_3]
  rfl

theorem block118 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes118 ++ tail) state118 =
      KECCAK.Bytes.run 0 tail state119 := by
  exact run_block_of_step bytes118 tail absorb118 state118 absorbed118
    state119 (fun _ => rfl) words118 perm118

private def absorb119 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x33 0x28 0x84 0x12 0x6d 0x6f 0x39 0x7)) 1 (by decide) (UInt64.ofBytes 0x1 0x82 0x20 0x60 0x29 0x74 0x59 0xa1)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x52)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x16 0x87 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x60 0x60 0x52 0x90 0x81 0x1 0x83 0x81)) 6 (by decide) (UInt64.ofBytes 0x51 0x83 0x52 0x90 0x88 0x1 0x81 0x82)) 7 (by decide) (UInt64.ofBytes 0x52 0x81 0x1 0x91 0x90 0x3 0x84 0x80)) 8 (by decide) (UInt64.ofBytes 0x52 0x92 0x90 0x1 0x92 0x90 0x80 0x60)) 9 (by decide) (UInt64.ofBytes 0x3f 0x61 0x90 0x91 0x90 0x54 0xf 0x60)) 10 (by decide) (UInt64.ofBytes 0x46 0x61 0x86 0x86 0x86 0x86 0x90 0x18)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x5b 0x56 0xb5)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x40 0x60 0x57 0x9a 0x3f 0x61 0x14 0x16)) 15 (by decide) (UInt64.ofBytes 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x80)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0))

private def absorbed119 : Vector UInt64 25 :=
  #v[0x9923494bb4dc419b, 0xeb3a549663b6757c, 0x65f0d4745c1a3360, 0x23a58caa63554f9a, 0xb9ddf57c2446e7b6, 0x61d6c636f2f1e609, 0x153557ef0a03c0c2, 0xa0876b46e90b6f24, 0x9e3bdf9a11c61b69, 0xf80bf4191e49defa, 0x6cd4cba47125c938, 0xc7e453d686e0c497, 0x397cc7061719a2ba, 0xd6cde55bdfad5688, 0xce275b804b80173c, 0x344b84c95b06fb14, 0x2fee66bfef8b89df, 0xe053262487d66bc6, 0x775aa9aebc1789f, 0x7fd8d1893ae28dd8, 0x461db49bd29cac2f, 0xca95fa188104225c, 0x8c47ea0f038debec, 0xa5e226906d5bcfa2, 0xe52b68415d82615a]

private theorem words119 : absorb119 state119 = absorbed119 := by
  decide +kernel

private def quarter119_1 : Vector UInt64 25 :=
  #v[0x82036ec354f37dd4, 0x1d041a4ed3ba9e67, 0x5d792b166b048aa3, 0x2ae7232a835c3065, 0xb59df192c7b42810, 0x8b23bf27e1e55592, 0xe63901847d4fe213, 0xa80f6df10c1e8922, 0x122e88b5b512a638, 0xd58d3b9f7547e9e0, 0x1e8a05710b8b5c08, 0xad1bc9d7bdba5dfb, 0x7a3b4916a0dfa43f, 0x42dbf403b7587112, 0x88aa96bbcd785794, 0x965ffd1d2fb1f601, 0x9d2273684bc773e8, 0xbdd1a5b66c558867, 0x3bfea6026d46bd78, 0xb28295dd6d3f8e99, 0x899e3639889299c6, 0x3e374978ef620804, 0xc48e12a616b6ab24, 0x372f8f8b600ccda2, 0xa3f74a30e6b51faa]

private theorem rounds119_0 : sixRounds 0 (by decide) absorbed119 = quarter119_1 := by
  decide +kernel

private def quarter119_2 : Vector UInt64 25 :=
  #v[0xd2ebfd796c3f1e8b, 0x5cb907225d17e023, 0x6d6919dee77dab2e, 0x1eb6dfad194a5a81, 0xce5491a2e2fdd54, 0x4a30cd2ca4892ec4, 0xf45705b4a4414721, 0x98440ab3eccb2d4f, 0x53416beacb7aba7d, 0x47486950773ff703, 0xa7d49807aefa5343, 0x211f504489478be6, 0xc84cb98d5ee7c0a0, 0x4ce5738eca598ccb, 0x72229f3eec6cd4d8, 0x45a33b3528075083, 0x162a83bb92e3ffe4, 0x3030372e4c9d2f85, 0xa3bf97e514dda556, 0x1dbff86e620d620c, 0xfa417ecee826c6f1, 0x1edc2dae346a4d83, 0xe229211892daff2f, 0x16fb49fae8545ebe, 0x9dde8ca512a62084]

private theorem rounds119_1 : sixRounds 6 (by decide) quarter119_1 = quarter119_2 := by
  decide +kernel

private def quarter119_3 : Vector UInt64 25 :=
  #v[0xb5e7b34d3a6c4501, 0x62b1ee9a9a9c9832, 0xe29dcaf1f3676072, 0xf32c3d5435c3cce1, 0x57ca2fe66274be3b, 0x1cf429673d7f29b8, 0x6c5ea5670b7157cb, 0x2170907dd43325d1, 0x179ceed2c8496b22, 0x562c5c1d0be375b, 0x22fbae33c887ee76, 0x34f9acd8a96a807c, 0xce8a834f49b3c7b2, 0x129df89c79de713b, 0xc0226a34e64f9d4c, 0xe4e8cd631f0e75d7, 0x2ce93a6181fed473, 0x2834986ac7873248, 0xbd6beb99265b9cd0, 0x76e557d5f41cc8a9, 0x6af3e5c0da571e8c, 0x1715c08422dca4fc, 0x733021453d6cc942, 0xf5209c328e4c1330, 0x721a6cb12053b90f]

private theorem rounds119_2 : sixRounds 12 (by decide) quarter119_2 = quarter119_3 := by
  decide +kernel

private theorem rounds119_3 : sixRounds 18 (by decide) quarter119_3 = state120 := by
  decide +kernel

private theorem perm119 : KECCAK.f1600 absorbed119 = state120 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds119_0, rounds119_1, rounds119_2, rounds119_3]
  rfl

theorem block119 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes119 ++ tail) state119 =
      KECCAK.Bytes.run 0 tail state120 := by
  exact run_block_of_step bytes119 tail absorb119 state119 absorbed119
    state120 (fun _ => rfl) words119 perm119

end Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
