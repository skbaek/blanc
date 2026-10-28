import Blanc.Lift.Usdc.ImplV2_1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb036 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x81 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x20 0x60 0x80 0x80 0x1 0x4 0x60 0x52)) 3 (by decide) (UInt64.ofBytes 0x25 0x60 0x52 0x82 0x3 0x81 0x82 0x1)) 4 (by decide) (UInt64.ofBytes 0x53 0x61 0x80 0x1 0x20 0x60 0x52 0x81)) 5 (by decide) (UInt64.ofBytes 0x1 0x40 0x60 0x39 0x91 0x25 0x60 0x47)) 6 (by decide) (UInt64.ofBytes 0x91 0x80 0x51 0x40 0x60 0x50 0x50 0x91)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x5b 0xfd 0x90 0x3)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x52 0x81 0x90 0x0 0x60 0x16 0x87 0xff)) 11 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x90 0x20 0x60 0xa 0x60)) 12 (by decide) (UInt64.ofBytes 0x90 0x52 0x84 0x33 0x20 0x83 0x80 0x40)) 13 (by decide) (UInt64.ofBytes 0x15 0x11 0x85 0x54 0x20 0x90 0x52 0x91)) 14 (by decide) (UInt64.ofBytes 0x7f 0x51 0x40 0x60 0x57 0x6a 0x13 0x61)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0))

private def absorbed036 : Vector UInt64 25 :=
  #v[0x10a93287a6548531, 0x849b29843baab535, 0x21f96473f83227e5, 0xeae6524d7695bc88, 0x318db21853f6442d, 0x447a8222f1795926, 0x16c6c372f9299a0a, 0xab125293033ffdea, 0x74b4c80757cca93c, 0xe320dd87d629dd1d, 0x114f322657d292ef, 0x193759b649307895, 0x8e215b60d49e885, 0x5430e063ad74d63c, 0xf1878b9f52e3f1fb, 0xc80ac2c2360f2535, 0x2cb4258f2bbb174a, 0x7b417f052c9bc9e1, 0x5c1fd1e4e46a4ab6, 0x81ddc6dad881073d, 0x6185375bb4a7abdf, 0x1099e885d2484738, 0x4e2a40463e3379b1, 0xdeda915204dd47ef, 0x46658f398c6b417c]

private theorem words036 : absorb036 state036 = absorbed036 := by
  decide +kernel

private def quarter036_1 : Vector UInt64 25 :=
  #v[0x9d81c42c142bcd9e, 0x4e6b9921527db59b, 0x99fc2327436a5c3a, 0x7e524a5c51a847b9, 0xee955cc331acc763, 0xfccaf1045dffd8eb, 0x52c2051d58d68129, 0xa14223c1d5eadae0, 0x843bce77fbe629d5, 0x1c552dbf16e4b425, 0xdbee30a7dd655923, 0x940801d959fb9ed0, 0xd273f083256651b7, 0xc18ebc7760d37582, 0x4326ddd9934af4e5, 0xf50d4b350d037986, 0x8b264bb6409c3817, 0x552be7c78783ce1f, 0xa905d882448a6575, 0x9ca422995f02b32f, 0xf8973406d2eab53b, 0xc71bcd770ff3043d, 0x2e6f21b97ed878ea, 0xcfe1976493280b05, 0x663f66b2647634b0]

private theorem rounds036_0 : sixRounds 0 (by decide) absorbed036 = quarter036_1 := by
  decide +kernel

private def quarter036_2 : Vector UInt64 25 :=
  #v[0x4ef2b945a1367a66, 0x82fa0df6a5650940, 0xc57863e0b6eee837, 0x4f82c4d7c000e34c, 0x363fab127958267a, 0x3e807155d326a622, 0xe8ab160d2ca84054, 0xe6ad1296a0030d68, 0x4671e3ee12e74ae7, 0x18f8d4edd89e0018, 0xe47f24ba2b3e4672, 0x3ecf2a9c92771c98, 0x3e0eb982e396ad14, 0x774141ba9126f134, 0x6d95b32ccb6e29bd, 0x642c031c5c83d9c9, 0x89d9bbd79b5f2f3, 0xe4df5b4c9bb1da40, 0x392848494345a8bb, 0x4bb52e8741645ca4, 0xd1c09deaa7599502, 0x1ac99f16a8df367d, 0x343e3df9d7b86361, 0xf7db9e221bc7001, 0x1a01e512724a6117]

private theorem rounds036_1 : sixRounds 6 (by decide) quarter036_1 = quarter036_2 := by
  decide +kernel

private def quarter036_3 : Vector UInt64 25 :=
  #v[0x2e67cde1937b908f, 0x8d125396f7c7d81c, 0xfa855ab3411b7d3f, 0xe17af58ed7a722c3, 0x776fd3582c3b1046, 0xfa425d28a78e37f0, 0xa0c76abbc0617dd1, 0xe1e9586885a0872e, 0xd4710e51bcd305ce, 0xce33d8c0b29fe55b, 0x566d1b9b301a5e22, 0x311816fdb56ef98, 0xbc076f32477bc589, 0x7403fa70f6ee2208, 0xa3361558db8b1f58, 0xf82a4ad6cc704db7, 0x26f07262fff61bb9, 0x887853c4b2554a7e, 0x3c782e931b863a9f, 0xcecd610a449eed39, 0x3ffde9497bfe44d1, 0x8ef66bb5d1ab2264, 0x6fb9ed92f40a21ba, 0x57061563df0e06fa, 0xb2eb935f45ef63e1]

private theorem rounds036_2 : sixRounds 12 (by decide) quarter036_2 = quarter036_3 := by
  decide +kernel

private theorem rounds036_3 : sixRounds 18 (by decide) quarter036_3 = state037 := by
  decide +kernel

private theorem perm036 : KECCAK.f1600 absorbed036 = state037 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds036_0, rounds036_1, rounds036_2, rounds036_3]
  rfl

theorem block036 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes036 ++ tail) state036 =
      KECCAK.Bytes.run 0 tail state037 := by
  exact run_block_of_step bytes036 tail absorb036 state036 absorbed036
    state037 (fun _ => rfl) words036 perm036

private def absorb037 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x60 0x80 0x80 0x1 0x4 0x60 0x52 0x81)) 3 (by decide) (UInt64.ofBytes 0x60 0x52 0x82 0x3 0x81 0x82 0x1 0x20)) 4 (by decide) (UInt64.ofBytes 0x61 0x80 0x1 0x20 0x60 0x52 0x81 0x28)) 5 (by decide) (UInt64.ofBytes 0x40 0x60 0x39 0x91 0x28 0x60 0x31 0x51)) 6 (by decide) (UInt64.ofBytes 0x80 0x51 0x40 0x60 0x50 0x50 0x91 0x1)) 7 (by decide) (UInt64.ofBytes 0x75 0x13 0x61 0x5b 0xfd 0x90 0x3 0x91)) 8 (by decide) (UInt64.ofBytes 0x5b 0x56 0x21 0x3b 0x61 0x87 0x87 0x87)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x60 0x16 0x87 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x20 0x60 0xa 0x60 0x52 0x81 0x90 0x0)) 13 (by decide) (UInt64.ofBytes 0x20 0x83 0x80 0x40 0x60 0x52 0x81 0x90)) 14 (by decide) (UInt64.ofBytes 0x20 0x90 0x52 0x91 0x90 0x52 0x84 0x33)) 15 (by decide) (UInt64.ofBytes 0x3d 0x61 0x86 0x90 0xb0 0x13 0x61 0x54)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x5b 0x56 0x4c))

private def absorbed037 : Vector UInt64 25 :=
  #v[0x8b4167c3c363136, 0x4777e4db3630a49f, 0x17b5460b3c8288f1, 0x12a93fe7079d562b, 0x5ae55b8070507bc5, 0xfbb7017c5d6b19e7, 0x979a727dfa79fde5, 0x31d56afc18a5e311, 0x649b946dc629876f, 0x11fa5dce26e013, 0xe2629679212ca23e, 0xa0b8ae6cb97b2a00, 0x121d25d20cc52761, 0x5e837b7b55743fc1, 0xd2467346e5377bc3, 0x56b692bf37b5dd87, 0x8e6b129fef90be0a, 0x13a933f7988491da, 0xb62b555f7b0fb963, 0xdbc4068409f4a6e3, 0xf281d43c835d0d9b, 0xee2000dbbdfabb77, 0x6c9f929a5a48fbcf, 0x6c83ab0968317a27, 0xa14a9204f47f480b]

private theorem words037 : absorb037 state037 = absorbed037 := by
  decide +kernel

private def quarter037_1 : Vector UInt64 25 :=
  #v[0x1bcd28126880e0f5, 0x1a519fa0ad421f81, 0x4e68c8ba9a214732, 0xbadfdd5a9067fe3a, 0x2fe35e57aa076da0, 0xfca18e8d386a3f22, 0xc81ca254c1839ee, 0xc03b88023130cf58, 0x339d7e95b1e2f79e, 0x929f67429f5c3dfc, 0xb51660dcf9a38fa0, 0x7e685588dc7c5016, 0x1a4188a2e8dc870f, 0x19c768241a1fb659, 0x460046de40eb7016, 0xbace42c9031c2472, 0x1c26bf6259fe6542, 0xbf21eb6406039140, 0xc9700b620e1faba1, 0x72a5fd897d50e983, 0xa425198dcaad2d71, 0x1fac9307ed69b2f3, 0x8c357ca1af215deb, 0x7e9211a955275a8b, 0x7ca5fd613b566430]

private theorem rounds037_0 : sixRounds 0 (by decide) absorbed037 = quarter037_1 := by
  decide +kernel

private def quarter037_2 : Vector UInt64 25 :=
  #v[0x33aa0cf266cb25f0, 0xd39f84b3da515bea, 0xbb6b1008da18dbc6, 0x50596fc751806803, 0xd9a5e5663b81e4d0, 0x1feadb7b789dc0fe, 0x874d4eee7b2b3f3b, 0x997782497f50608d, 0x87850e2bab92d0dd, 0x7aeea284dbf73168, 0x9fbb7372b1ca8de5, 0xc3867fdc11c4cd74, 0xf950acafcabc7e4e, 0xaa42eee252b39568, 0xddfb3081ae73c121, 0xc25a28b169851aa2, 0x6089eae30458b8ac, 0x739b5732b3f1165, 0xdc1fdefa6b14bceb, 0xae7984ea2c6edbdd, 0xfefe1b820d271ae4, 0xc1e03c0dd5f884e0, 0xa8e566bacd205651, 0xfa59e667ade9c80d, 0x9047250224179196]

private theorem rounds037_1 : sixRounds 6 (by decide) quarter037_1 = quarter037_2 := by
  decide +kernel

private def quarter037_3 : Vector UInt64 25 :=
  #v[0x834934b827bc66af, 0x50529e0b7aaf28ff, 0x7e99059336d0e03c, 0x646fa89ecce9f831, 0x906aa9f75a8904d2, 0xc9fd9714ab307c5, 0x7f5d98c8f9ce384a, 0x5b443c6bbb98ab33, 0xc847c139b414b9e3, 0x491e325bd123f656, 0x98460f91d10a4a82, 0xe34fef06426aada0, 0xce4637aa1c0313b7, 0x240497092eff08ec, 0xc29948c9b7407441, 0xd9eaaa64a984a4e0, 0x292223027a9b4e67, 0xecab5204922d21ec, 0x10e8e9084220ad06, 0x2c5b4cfbcacbcd06, 0xb1a1257613e16983, 0xd7f03a2aa5c7c9d8, 0x7981463e04962ccd, 0xb185d0fb70399b6, 0xaff97b360a2f7437]

private theorem rounds037_2 : sixRounds 12 (by decide) quarter037_2 = quarter037_3 := by
  decide +kernel

private theorem rounds037_3 : sixRounds 18 (by decide) quarter037_3 = state038 := by
  decide +kernel

private theorem perm037 : KECCAK.f1600 absorbed037 = state038 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds037_0, rounds037_1, rounds037_2, rounds037_3]
  rfl

theorem block037 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes037 ++ tail) state037 =
      KECCAK.Bytes.run 0 tail state038 := by
  exact run_block_of_step bytes037 tail absorb037 state037 absorbed037
    state038 (fun _ => rfl) words037 perm037

private def absorb038 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x90 0x0 0x60 0x16 0x88)) 3 (by decide) (UInt64.ofBytes 0x40 0x60 0x52 0x81 0x90 0x20 0x60 0xa)) 4 (by decide) (UInt64.ofBytes 0x91 0x90 0x52 0x84 0x33 0x20 0x83 0x80)) 5 (by decide) (UInt64.ofBytes 0x50 0x93 0x1 0x60 0x55 0x20 0x90 0x52)) 6 (by decide) (UInt64.ofBytes 0x50 0x50 0x50 0x92 0x93 0x50 0x50 0x50)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x54 0x0 0x60 0x5b 0x56)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x75 0x14 0x61 0x14 0x33 0x16 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xc3 0x8 0x7f 0x51 0x80 0x40 0x60 0x57)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0xa0 0x79)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x52 0x81 0x0 0x0 0x0 0x0 0x0 0x0)) 16 (by decide) (UInt64.ofBytes 0x90 0x81 0x1 0x82 0x4 0x60 0x20 0x60))

private def absorbed038 : Vector UInt64 25 :=
  #v[0xe7f37e7bdf57577f, 0xa895077d7e739fca, 0xa9aaec4d1300478a, 0x30ee495b2ad8e02c, 0x900ea70d9a827ce6, 0xc2e6494711b984ea, 0x96f8336239527b82, 0x1681222cc5eb3edc, 0xa5d62d3551fc2e07, 0xfa4d9f48e9d7f6e6, 0x64b431c8bd06913, 0xb1fc5801cc02d24e, 0xd2560cb13af55ce, 0xafd84d2006764013, 0x69cc8feddbb24139, 0x3c236d3cc1ff52f3, 0xbc35efb5977f2913, 0x17c8a2656b8faf65, 0x7f60879193ac005d, 0xa9350b09a0db39a2, 0x183f0dae5bc7fc56, 0x90f84d9cca36c55c, 0x5f35e2b2c2d7a26b, 0xd7a44a7de7948750, 0x8a9bc040b3fda44c]

private theorem words038 : absorb038 state038 = absorbed038 := by
  decide +kernel

private def quarter038_1 : Vector UInt64 25 :=
  #v[0x118f6a5d27beb24, 0x2cc62f13e5bfa2a8, 0xaac43d38efe8d7b6, 0x7e27068a90866754, 0x6e27fa82edf0c9b9, 0xfa42a9e32a73cecd, 0x8dbc795f298357cd, 0xbfd4f4180d443055, 0x4e291d118b17119c, 0xfbc7671c724a64e1, 0x4093acfb58c43944, 0x220e4d0eb595f2d9, 0x8879ac551dedde57, 0x7eefd82b71adea21, 0x57597cdeed7a8a60, 0xaeff86286049ace0, 0xa3d29ed97dd64740, 0xed7da12b7fba941a, 0xff021de4046a1fbe, 0x2658f154983b5e06, 0xcf795093cd92936b, 0xda4f874dcd7061cb, 0xffb7bc2e1465d580, 0x1e3a32d462d996b5, 0xdfe192ceb90fbc94]

private theorem rounds038_0 : sixRounds 0 (by decide) absorbed038 = quarter038_1 := by
  decide +kernel

private def quarter038_2 : Vector UInt64 25 :=
  #v[0x982ea88fd1f5a74b, 0x22f41b89fe8b6e9b, 0xc375e17111034b5c, 0xfc9222c62033f6de, 0xa2b52dfdaf53c438, 0xa140e38a02280bd9, 0xde9a1917bf096872, 0x56f92246b2eb28a7, 0x83dc10fb569ed947, 0xd17e5a9516c51935, 0x982216b8f2b252db, 0x391a688face969aa, 0x17488c31ac74ce50, 0x644e34cef27e91c5, 0x907836b9b419f596, 0x7efdf39290d9f39b, 0xee6f1bae2494b290, 0x3983d28a821c9154, 0xbe9196e2b2fc1aa6, 0xf6f4ee807b8237d6, 0x818c353a5411f51e, 0xfcbf602853e600fd, 0xdcf407f4923344e8, 0xf8d3a63454ee7ec3, 0x798964ad348ce260]

private theorem rounds038_1 : sixRounds 6 (by decide) quarter038_1 = quarter038_2 := by
  decide +kernel

private def quarter038_3 : Vector UInt64 25 :=
  #v[0x89ff409b2f45cb2b, 0x6086a291dbedbee1, 0xeba29bf968e8384b, 0x47e66375fb9d3b3c, 0x7174b4e1399467f4, 0x2b31cee42b42c7ef, 0x67900fb1637071cf, 0x67e57edba78f3d1c, 0x82cb0363c0d8b360, 0x45c3a9c3123a8c25, 0x4a98a0d83873a1d1, 0x72c71595a240fec7, 0x57d12a944e5ad0a8, 0x3ca19960ce3a06d0, 0xaa56132b6daab2e4, 0x5cbb94911c779674, 0xdbe41d7322a593a0, 0x504121056bd38d11, 0xb8552d0d531f8752, 0x4c63ccc80ddb5e51, 0x536dedbad053715f, 0x250b1514a536db6c, 0xfa5277e9c5c81edd, 0x885e2eefc5f6837f, 0xcb1738e5976ae6]

private theorem rounds038_2 : sixRounds 12 (by decide) quarter038_2 = quarter038_3 := by
  decide +kernel

private theorem rounds038_3 : sixRounds 18 (by decide) quarter038_3 = state039 := by
  decide +kernel

private theorem perm038 : KECCAK.f1600 absorbed038 = state039 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds038_0, rounds038_1, rounds038_2, rounds038_3]
  rfl

theorem block038 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes038 ++ tail) state038 =
      KECCAK.Bytes.run 0 tail state039 := by
  exact run_block_of_step bytes038 tail absorb038 state038 absorbed038
    state039 (fun _ => rfl) words038 perm038

private def absorb039 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x4f 0x7f 0x52 0x1 0x82 0x24 0x60 0x52)) 1 (by decide) (UInt64.ofBytes 0x20 0x3a 0x65 0x6c 0x62 0x61 0x6e 0x77)) 2 (by decide) (UInt64.ofBytes 0x69 0x20 0x72 0x65 0x6c 0x6c 0x61 0x63)) 3 (by decide) (UInt64.ofBytes 0x68 0x74 0x20 0x74 0x6f 0x6e 0x20 0x73)) 4 (by decide) (UInt64.ofBytes 0x60 0x72 0x65 0x6e 0x77 0x6f 0x20 0x65)) 5 (by decide) (UInt64.ofBytes 0x81 0x90 0x51 0x90 0x52 0x1 0x82 0x44)) 6 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x90 0x1 0x64 0x60 0x3 0x90)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x61 0x16 0x81 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x8 0x7f 0x51 0x40 0x60 0x57 0xe1 0x14)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x81 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x20 0x60 0x80 0x80 0x1 0x4 0x60 0x52)) 16 (by decide) (UInt64.ofBytes 0x2a 0x60 0x52 0x82 0x3 0x81 0x82 0x1))

private def absorbed039 : Vector UInt64 25 :=
  #v[0xe1fe132e63d8ddf7, 0x937d83c3a30934b1, 0xde80fe136f88f645, 0xdda7392755a3cc24, 0x14ecc70f78c19b5, 0x3d6f394e86e2605a, 0xfe2f15eeec22f653, 0xbb2ed0f5ac33d303, 0xa40088df602ffdde, 0x87fff6ea62703127, 0xa8b69f22dd1a9018, 0x5219ccdfb5466b4, 0x8f9365acd329d2dc, 0x5107ce5c50ca920c, 0x4b2cb8889f517395, 0xe2bbb9ae13cb77ef, 0x48ce994027d7ebed, 0x424a38561049af92, 0x560882ac1be4fa9f, 0xe87f2d6f18129418, 0x2a089dd0ff8137c3, 0x6ce105e500ec187b, 0x3b5748b5049dad21, 0x8fd894fe8433de94, 0x6a0848810666d17c]

private theorem words039 : absorb039 state039 = absorbed039 := by
  decide +kernel

private def quarter039_1 : Vector UInt64 25 :=
  #v[0x4032e7d434e43f85, 0x2165a27e364d4d23, 0x2c050eda918d0723, 0x40d3aff1803695a, 0xbe36df4f55bfed37, 0xa37f97bb92e43240, 0x454ab46ccde15fae, 0x9c7c5567cfd9a4bb, 0xdaee51e1a840691c, 0x6e93abc051a3377d, 0xfc6786e851a26bfc, 0xc5ba68304daa5d72, 0x76904b1344658534, 0x899e00b4cff90bf3, 0xd588340a4f0ac6f1, 0xaa4d22b382cfc12f, 0x62c5a2c04661fc21, 0xaa7434335a1be160, 0x148e09352ce90cd6, 0xe6dc5f4d9ab12353, 0xbc500e454a90c948, 0x8ffbadcae746d63c, 0xb9388b543e5df91a, 0x2d39555d0547b620, 0x4184b445fec6e6b1]

private theorem rounds039_0 : sixRounds 0 (by decide) absorbed039 = quarter039_1 := by
  decide +kernel

private def quarter039_2 : Vector UInt64 25 :=
  #v[0x1259bab10122003f, 0xb3e3fd6dafa112ce, 0x61ae32a2af7b7a6d, 0xab756a9d9ff5ccd3, 0x5ac66ef87780166f, 0x1c92e49591cbf32a, 0xb13f21a6b3876a9d, 0x87b9823e1727ebbe, 0x1eef11a520da56a, 0xe838b9678c288447, 0xbb592262cdddf097, 0x59e1d9bcefdab912, 0xb4d47be11e0377c, 0x3ddcb26d17295454, 0xfa57095f70220cdb, 0xb67f7a2a0289591b, 0x3fa0ffa47a0eaa78, 0x2b27a87aa0ee9eca, 0xf2967b43cef9e55b, 0x24f2f50e514a040a, 0x9828a4353a3422f0, 0x6e8d2cadf8671e9c, 0xa384469dc3f70dc9, 0x9b9570209e45e4d0, 0xcf9cf4b7b150a416]

private theorem rounds039_1 : sixRounds 6 (by decide) quarter039_1 = quarter039_2 := by
  decide +kernel

private def quarter039_3 : Vector UInt64 25 :=
  #v[0xaea1a86fe373e5c9, 0xbea4b969034a28d4, 0xf1374290650eadb4, 0x49fdc605728e86eb, 0xa377fa5ef29a8a75, 0x9fded911c8119e71, 0xec5529054b6016a8, 0xcd3d32b0a85b2afd, 0x15f48b3a1d6a0aa2, 0xf9a44e2f8755024a, 0x5f729ca4f1c3917c, 0x3b8b19119947f52d, 0xc505a828585d80e2, 0xa286233f238dc722, 0xcb97cada073fd694, 0x6cf25b10226ed0f3, 0x239b30b238ab80f2, 0x7be1771b10c05204, 0x2bc0549c6e21f342, 0x42b756247f921b48, 0xdfe7fd9cfbc7a0f7, 0xadb16bd9949957c6, 0x14fbfa1b9bec373f, 0x5dde111795272878, 0xcec382d2c26541da]

private theorem rounds039_2 : sixRounds 12 (by decide) quarter039_2 = quarter039_3 := by
  decide +kernel

private theorem rounds039_3 : sixRounds 18 (by decide) quarter039_3 = state040 := by
  decide +kernel

private theorem perm039 : KECCAK.f1600 absorbed039 = state040 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds039_0, rounds039_1, rounds039_2, rounds039_3]
  rfl

theorem block039 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes039 ++ tail) state039 =
      KECCAK.Bytes.run 0 tail state040 := by
  exact run_block_of_step bytes039 tail absorb039 state039 absorbed039
    state040 (fun _ => rfl) words039 perm039

private def absorb040 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x4f 0x61 0x80 0x1 0x20 0x60 0x52 0x81)) 1 (by decide) (UInt64.ofBytes 0x1 0x40 0x60 0x39 0x91 0x2a 0x60 0xc9)) 2 (by decide) (UInt64.ofBytes 0x91 0x80 0x51 0x40 0x60 0x50 0x50 0x91)) 3 (by decide) (UInt64.ofBytes 0x54 0x80 0xe 0x60 0x5b 0xfd 0x90 0x3)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x7f)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x16 0x0)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x83 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x60 0x55 0x91 0x90 0x17 0x81 0x90 0x16)) 12 (by decide) (UInt64.ofBytes 0xd8 0x80 0xe5 0x75 0xe4 0x7f 0x51 0x40)) 13 (by decide) (UInt64.ofBytes 0x33 0xca 0xd8 0x40 0x8e 0x34 0x11 0x51)) 14 (by decide) (UInt64.ofBytes 0x5c 0x65 0xe1 0xf 0xc3 0x74 0xdd 0xcf)) 15 (by decide) (UInt64.ofBytes 0x6 0x10 0xbc 0x3a 0xa1 0x37 0x85 0x2d)) 16 (by decide) (UInt64.ofBytes 0xa2 0x90 0x0 0x60 0x90 0x5a 0xfa 0x5f))

private def absorbed040 : Vector UInt64 25 :=
  #v[0x1c95df550e553eaa, 0xfacbeb55ad610a06, 0x53da5101266c06dd, 0x3c7d2e45d4b9fd46, 0x88b4afa98cd1ef43, 0xe9756d6675b2074, 0xaf19c2d0b8642aba, 0xaa265fb0414cd5ee, 0xba6420686f3e31ce, 0x36e71f376aca16f0, 0x4cdbe021f505b103, 0xc523335b88e779dd, 0x224cc90cc6839e6b, 0x5d14b33aeaaf4e7f, 0x113dd51c12696342, 0xd3baab0978a2e5b4, 0xcc236018b12138db, 0x93c7330a4c6b7aa9, 0x8ca6fe950a322a90, 0xd327d721c9dd75cb, 0xc642a1b1bc16e7fc, 0xc62a80c515f33ffd, 0x3fc023377a0083bf, 0x6a54e701d2b2aff4, 0xab52a388e38bf5b4]

private theorem words040 : absorb040 state040 = absorbed040 := by
  decide +kernel

private def quarter040_1 : Vector UInt64 25 :=
  #v[0x8b8f00fbb5798fb1, 0x3974a5b6d1e4295d, 0x8a781de682b21970, 0xca0c7a547c5c4d0c, 0xbb7c621b66d541ea, 0x66b3619a7adc2e82, 0x600f5f8cf36fd985, 0x7f09ff762482f4da, 0xb1ea9a425588c4e3, 0xd1973ea10651d98a, 0x6a378aea00d8a987, 0x82ceae4e54cc1aae, 0x91011f9fd5a49dc2, 0x2c8825a4418cb6fc, 0x1c0111a26e7aed36, 0x5d10e8d6f5d55e11, 0x2c22716339cf0faa, 0x111cb3f0a823f7e3, 0x99d29b9d154ebe76, 0x3190ae4d9be01678, 0xc7042057b3231e1, 0x3ea4a856d1577d98, 0xdf50e4a5e40c007d, 0xbbd1614948bc3003, 0x6a9f6e60e5f17b5d]

private theorem rounds040_0 : sixRounds 0 (by decide) absorbed040 = quarter040_1 := by
  decide +kernel

private def quarter040_2 : Vector UInt64 25 :=
  #v[0x795e2977b004b89e, 0x4426a0dd4a450248, 0x3bb45597a038ffb8, 0xcd9e028756421a47, 0xa9bd940ddd3202c, 0x1300d10a7da5ef21, 0x6cedaefe8f861f59, 0x4153dbb019618cfb, 0x5629736a7ba508af, 0x55058393d615561e, 0xf594f0cc0f50105a, 0xd727bede936df91a, 0x5e09de78397711ab, 0x87d9d7d65316394b, 0x84405b910d62a615, 0xdfa1897c7d011dd3, 0xe63baea2aa3ea1bf, 0x6f2ae148c824d8eb, 0x2d565f98a00b58f5, 0xee9c743c55f2c139, 0xb3427d427d40235a, 0x5e4e9683901c1384, 0xa1333edb47e88c2b, 0xce8541a2cdd5deb0, 0x66785d761daeb314]

private theorem rounds040_1 : sixRounds 6 (by decide) quarter040_1 = quarter040_2 := by
  decide +kernel

private def quarter040_3 : Vector UInt64 25 :=
  #v[0x7147f69f851d42d0, 0x8aa3d3ed9f01ab05, 0x87fb2b63e620dbb8, 0x9cc12285bc651445, 0x9500a0ac9f7a0b1a, 0x74994cf9ee3b9b75, 0x5ae5ea451fc87a1d, 0x17a2f17fb454946a, 0x84b75ec182ea4986, 0xf800336daa57f596, 0x318b4c0417439d40, 0x3ee27e8396984818, 0xecde5eb0fe9b625f, 0xcc5752cc8dd9131d, 0x7d3ade45f7eba1b6, 0x8a11c80ed9a1677d, 0x3c38863edc38b9fc, 0x7157f7734cae38ab, 0x84296f5c2ed738e6, 0x140ce232e0439561, 0x443f41c09d63a1e, 0x52cb88f27c70d6e2, 0x405172e03b5947e8, 0x2fddc5016215c1a9, 0xb6c7ad87c46845ef]

private theorem rounds040_2 : sixRounds 12 (by decide) quarter040_2 = quarter040_3 := by
  decide +kernel

private theorem rounds040_3 : sixRounds 18 (by decide) quarter040_3 = state041 := by
  decide +kernel

private theorem perm040 : KECCAK.f1600 absorbed040 = state041 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds040_0, rounds040_1, rounds040_2, rounds040_3]
  rfl

theorem block040 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes040 ++ tail) state040 =
      KECCAK.Bytes.run 0 tail state041 := by
  exact run_block_of_step bytes040 tail absorb040 state040 absorbed040
    state041 (fun _ => rfl) words040 perm040

private def absorb041 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0x60 0x54 0x12 0x60 0x5b 0x56 0x50)) 1 (by decide) (UInt64.ofBytes 0x57 0x62 0x15 0x61 0x14 0x1 0x60 0x16)) 2 (by decide) (UInt64.ofBytes 0x0 0x60 0x30 0x5b 0xfd 0x80 0x0 0x60)) 3 (by decide) (UInt64.ofBytes 0x52 0x20 0x60 0x9 0x60 0x52 0x81 0x90)) 4 (by decide) (UInt64.ofBytes 0x61 0x15 0x80 0x54 0x20 0x90 0x40 0x60)) 5 (by decide) (UInt64.ofBytes 0x83 0x30 0x83 0x15 0x61 0x57 0x83 0x15)) 6 (by decide) (UInt64.ofBytes 0x50 0x50 0x5b 0x56 0x21 0x3b 0x61 0x83)) 7 (by decide) (UInt64.ofBytes 0x3 0x60 0x52 0x81 0x90 0x0 0x60 0x30)) 8 (by decide) (UInt64.ofBytes 0x80 0x20 0x90 0x40 0x60 0x52 0x20 0x60)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x7f 0x54)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x17 0x1 0x60 0x16 0x81 0x90 0x0 0xff)) 14 (by decide) (UInt64.ofBytes 0x90 0x54 0x80 0x12 0x60 0x55 0x91 0x90)) 15 (by decide) (UInt64.ofBytes 0x56 0x55 0x90 0x17 0x2 0x60 0x16 0x91)) 16 (by decide) (UInt64.ofBytes 0x73 0x90 0x0 0x60 0x54 0x8 0x60 0x5b))

private def absorbed041 : Vector UInt64 25 :=
  #v[0x8b395aa3d88419f3, 0x28ac48dc2f9b2e05, 0x2abff4274172e544, 0xb86a92b52e920517, 0x93ad2566c7c27b7b, 0x810ccbcd716d65e4, 0xac53b63b90b78b52, 0xa42c88e120c571c3, 0xe7dba4d356505c66, 0x39f0f93cb99cdc8b, 0xab9e069cc446d805, 0x900eb742fb9afed1, 0xff6e5715bdb18d80, 0x93fb762ff065eae4, 0xd41ec6bfc7578bb, 0x9ee6f491da3ef3c6, 0x9949a39985d2b0cb, 0xbf36f96cb7521800, 0xf38612ed0ae50517, 0x7b8865b3fe79933, 0x30173e3f91247d0c, 0x53bf14e4dd665023, 0xa8cb01a1fcb56f3c, 0xdf90e62e51d17d56, 0x2cef156a73c7f21]

private theorem words041 : absorb041 state041 = absorbed041 := by
  decide +kernel

private def quarter041_1 : Vector UInt64 25 :=
  #v[0xb21ea3ce996c093e, 0xb8cadf0cefd25ed5, 0xab84efb4ab2bf2f3, 0x7343f3cc440b6ff6, 0xe65f3e3a8e916a63, 0x1eadd56262467173, 0x6273b1642cfce563, 0xe52bbbd55f33c0a, 0x7247285b8d03ce0c, 0x98e435364c399dec, 0x78218a66b0b0144c, 0xea75adceee0ef0ea, 0x253abe943ff0bcf3, 0x32c51cffacda0e6a, 0xcf1efda74f73154e, 0x8adc79da5c9d5e36, 0x3be87d92ccb2eb88, 0x964e527ecd260f58, 0xd56a18bad2f00564, 0xfbd58d1b00b25322, 0x43c52e230923a9b4, 0x82f6665f912fae6c, 0x9e465b176dd6136c, 0xee64189fcd433bf, 0x49747c4da0d96c60]

private theorem rounds041_0 : sixRounds 0 (by decide) absorbed041 = quarter041_1 := by
  decide +kernel

private def quarter041_2 : Vector UInt64 25 :=
  #v[0xd33828914f3e67f7, 0xf915a518f968d01e, 0x62dd8b8232c5aacb, 0x7eadb7ec19a033be, 0xcc7be541c91f422c, 0x4d32ce7da46511d3, 0x51c9433f177efa33, 0x482280782e3f2c16, 0x5b18957d42abb480, 0x824746564a8c91d3, 0x4074657e44a4b0ab, 0xbba1d128423c0fea, 0x38c0af580757c94b, 0x3162b550ef8cb42d, 0x2dfb8275de0648b6, 0xbdde21f5aec5840, 0x419054cebfa22b1d, 0x757043b33cd1f842, 0x33d6fae4392bc03c, 0x55b835303f75022, 0xd3483caa5be2a202, 0xbabd09c1f8fbe236, 0xc84697964b18986d, 0xbb853f4fa218dad5, 0x38e33b6c2a2e059e]

private theorem rounds041_1 : sixRounds 6 (by decide) quarter041_1 = quarter041_2 := by
  decide +kernel

private def quarter041_3 : Vector UInt64 25 :=
  #v[0x1c34801680a5eeac, 0xe3d1899316a9c883, 0xadf7dcbddfd4a248, 0x810f4b19c1ec3aa5, 0x6e9a94db3d7af792, 0x691f4929a1c103c3, 0xf13ca4b3dfe33e52, 0xaf93c1a62f5c4b70, 0xef9ed1ca98dcab65, 0xb764dccf484ad850, 0x8be78470a73acbde, 0x9d85fc3f080bacae, 0xa40f8630d9ee2187, 0x161d5840569987b4, 0x482513e5b3dd1cd3, 0x187a27b04c01374e, 0x7bc2b37c5202fdfe, 0x11bc104b161e36f0, 0x2278655d9b502189, 0xb5e95a4ec87397c, 0x37a210e3a4e3b1fa, 0xaecca3cce05fa5f2, 0x5e66f9e026940e5a, 0x970fcf936538c463, 0xcb1a75d102a7a424]

private theorem rounds041_2 : sixRounds 12 (by decide) quarter041_2 = quarter041_3 := by
  decide +kernel

private theorem rounds041_3 : sixRounds 18 (by decide) quarter041_3 = state042 := by
  decide +kernel

private theorem perm041 : KECCAK.f1600 absorbed041 = state042 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds041_0, rounds041_1, rounds041_2, rounds041_3]
  rfl

theorem block041 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes041 ++ tail) state041 =
      KECCAK.Bytes.run 0 tail state042 := by
  exact run_block_of_step bytes041 tail absorb041 state041 absorbed041
    state042 (fun _ => rfl) words041 perm041

end Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
