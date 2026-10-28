import Blanc.Lift.Usdc.ImplV2_1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb126 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x6c 0x61 0x76 0x6e 0x69 0x20 0x3a 0x32)) 1 (by decide) (UInt64.ofBytes 0x61 0x6e 0x67 0x69 0x73 0x20 0x64 0x69)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x65 0x72 0x75 0x74)) 3 (by decide) (UInt64.ofBytes 0x90 0x52 0x1 0x82 0x44 0x60 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x1 0x64 0x60 0x3 0x90 0x81 0x90 0x51)) 5 (by decide) (UInt64.ofBytes 0x88 0x88 0xab 0x42 0x61 0x5b 0xfd 0x90)) 6 (by decide) (UInt64.ofBytes 0x50 0x50 0x5b 0x56 0xda 0x39 0x61 0x88)) 7 (by decide) (UInt64.ofBytes 0x5b 0x56 0x50 0x50 0x50 0x50 0x50 0x50)) 8 (by decide) (UInt64.ofBytes 0x20 0x1 0x83 0x92 0x20 0x60 0x51 0x81)) 9 (by decide) (UInt64.ofBytes 0x91 0x90 0x91 0x1 0x83 0x91 0x51 0x81)) 10 (by decide) (UInt64.ofBytes 0x73 0x8b 0x7f 0x51 0x80 0x40 0x60 0x20)) 11 (by decide) (UInt64.ofBytes 0x2e 0x51 0x3d 0xfe 0xb8 0x9b 0xc6 0xc3)) 12 (by decide) (UInt64.ofBytes 0x9f 0x23 0x79 0xcc 0x59 0xf7 0x4c 0xcc)) 13 (by decide) (UInt64.ofBytes 0xa7 0xa9 0xca 0xfa 0xf 0x9b 0x17 0x7b)) 14 (by decide) (UInt64.ofBytes 0x86 0x81 0xf 0x40 0x39 0x2b 0x52 0x5d)) 15 (by decide) (UInt64.ofBytes 0x93 0x90 0x93 0x1 0x82 0x80 0x52 0x1)) 16 (by decide) (UInt64.ofBytes 0x91 0x90 0x91 0x1 0x83 0x60 0x60 0x52))

private def absorbed126 : Vector UInt64 25 :=
  #v[0xd322f747beb87e60, 0xdca94cc57813a108, 0x409d561bf7886dc2, 0x544a15873047f439, 0x39ecb0ac162e123c, 0xc763648999b8c8a9, 0xdcea5b76a2cda697, 0xe5ef4685328617e1, 0x41f7b86c3756816a, 0xa7d4639f63a2072a, 0x9f94838110a51fec, 0x9af3bccf212dd596, 0x6cd44a6a025ac88a, 0xcd0d3d4e54fb32fa, 0x1cca8eceba5425f3, 0x97887b4fd4ccecec, 0xfd760bd47daa6f64, 0x8b9ac88a8e06d2c4, 0xf7fc78b65eaf4bf8, 0xe05c584899449b1d, 0x5e5cb76e3f47cf18, 0x84188bf4784bfead, 0xf45bfa99459796bd, 0x86ae3933ea55bcc5, 0x314f41864ed3f7dd]

private theorem words126 : absorb126 state126 = absorbed126 := by
  decide +kernel

private def quarter126_1 : Vector UInt64 25 :=
  #v[0xa313d961c6b14827, 0xf99a70fcd98daa70, 0x806f093b2163941, 0x1afa0d8b73546828, 0x6ce32dd83cecfb44, 0x7713deda51ad9539, 0xc940deeb012d0e85, 0xe3f47099429e55bd, 0xbddc303691038d6b, 0x2655ff61052e8b65, 0xc9a2d1016c7271e7, 0x95cd193602e1881c, 0x81d0cffcbce2d3f7, 0xab737885257dfe5f, 0xab0d239279044b9a, 0xc6c3150d27f16b4a, 0x92fdde835e411ac, 0x24fe5d813951f5d4, 0xbe1884fe948fa8e8, 0x8ddfdc7e71b8dadd, 0x7669b5b1671474a4, 0xe78136377ddde365, 0xd8915902a4db3a14, 0xf74ecdc967e8b521, 0x854ffb2358ae06f7]

private theorem rounds126_0 : sixRounds 0 (by decide) absorbed126 = quarter126_1 := by
  decide +kernel

private def quarter126_2 : Vector UInt64 25 :=
  #v[0xf8766a0216cec0df, 0xa6980d654901bcd5, 0x5186a64c8ee87ff3, 0xd721a500884678be, 0xaeea01ef5395c03e, 0x837c07c19909f137, 0xe620467a730bc2d4, 0x3a9707494f5c41c2, 0xb029f2926eec7af1, 0xa3e94308692eeab9, 0x50e4c1ee6c9ef48, 0x5bacc6106d30ac0e, 0xa682a8f811169df2, 0xbb91fe7bebd2bec3, 0xde0797ad7faf2906, 0x8da07b8fcb1d8880, 0x9222108ba33eda66, 0x3594242478fe1880, 0x9f052d142d3d7c94, 0xd23f105d4fb9c196, 0x5308f062c72554bb, 0x6596426d31274ef3, 0x402f07b24902453, 0xfde5e0f0aaec8881, 0xb98ee5309f14d4bc]

private theorem rounds126_1 : sixRounds 6 (by decide) quarter126_1 = quarter126_2 := by
  decide +kernel

private def quarter126_3 : Vector UInt64 25 :=
  #v[0x34c346cd520a2443, 0x1f54da96b08abc92, 0x3cc0c990b3d8e0b0, 0x75811ed5325ff5f5, 0xf7634557f336e99c, 0xd9e66689881a847b, 0xe1f9bd72d5320a3b, 0x984fa0e6f5727434, 0x75f4ca702c2eceae, 0x58021d08d7f82d0b, 0x9ca0cb11d1636162, 0x2372ad60512c9b9b, 0x18e00f64a4ed3e15, 0xeae380068c079c6c, 0x764533b3a985407a, 0x92a523818e8e434b, 0x1bee1e5a73a4d565, 0x494e6b29a5b15e8a, 0xd1d31d76b844fe0, 0xf3d4fa2f43e6dea6, 0x73d95a8709836ff6, 0xcb0cb12fbc4fddea, 0xf26bc1b61d44d9a4, 0x9dc692d31a786fa3, 0xaee2e1621c61f25]

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
  exact run_block_of_step bytes126 tail absorb126 state126 absorbed126
    state127 (fun _ => rfl) words126 perm126

private def absorb127 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x30 0x52 0x1 0x83 0x80 0x60 0x46 0x52)) 1 (by decide) (UInt64.ofBytes 0x91 0x90 0x91 0x1 0x84 0x80 0xa0 0x60)) 2 (by decide) (UInt64.ofBytes 0x91 0x90 0x3 0x84 0x80 0x51 0x81 0x52)) 3 (by decide) (UInt64.ofBytes 0x1 0x92 0x90 0xc0 0x60 0x52 0x81 0x1)) 4 (by decide) (UInt64.ofBytes 0x90 0x20 0x1 0x91 0x51 0x80 0x52 0x90)) 5 (by decide) (UInt64.ofBytes 0x88 0x85 0x89 0x33 0x43 0x61 0x5b 0x56)) 6 (by decide) (UInt64.ofBytes 0x40 0x60 0x5b 0x56 0xff 0x47 0x61 0x88)) 7 (by decide) (UInt64.ofBytes 0x67 0xdb 0x6c 0x7c 0x7c 0x7f 0x51 0x80)) 8 (by decide) (UInt64.ofBytes 0x9b 0xfa 0xc6 0x9e 0xf4 0x43 0x87 0xa1)) 9 (by decide) (UInt64.ofBytes 0xed 0xcb 0x5 0xed 0x52 0xd 0xf5 0x35)) 10 (by decide) (UInt64.ofBytes 0x1c 0x50 0x44 0x3b 0xe1 0x92 0xc5 0x4c)) 11 (by decide) (UInt64.ofBytes 0x52 0x1 0x82 0x20 0x60 0x67 0x22 0x1a)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x16 0x8c 0x80 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x8b 0x90 0x52 0x90 0x81 0x1 0x84 0x82)) 16 (by decide) (UInt64.ofBytes 0x80 0x60 0x52 0x1 0x83 0x60 0x60 0x16))

private def absorbed127 : Vector UInt64 25 :=
  #v[0x5700b1a53a5dc59f, 0x177b5e8c35404b2c, 0x70714805825b7693, 0x33a303122d3c3a58, 0xb8f8c9a55cd7cb7a, 0xcc1487b2a159d5fd, 0x78a334741cc1fd81, 0xeecb8121620316, 0xaadc8af66a4fd6b9, 0xfde3f6a2b3aa4866, 0x96ff436282cdbffe, 0x67f37b540f4afa61, 0xc1033eaa968b4d9c, 0x98d9ac5bb9bc543b, 0xd8112f315fbc5d3d, 0xa59f80637dac77e8, 0x2add18d33f21fec7, 0x4baf67ce346ec739, 0xcd99fd30dd24b164, 0x49e4b3ca16e78b06, 0xeb5c5aeb0efec4c4, 0x7ac354eb9e79d515, 0x22385495eaad287a, 0x735703ce88933711, 0xdc47000dda2e8762]

private theorem words127 : absorb127 state127 = absorbed127 := by
  decide +kernel

private def quarter127_1 : Vector UInt64 25 :=
  #v[0x79de4a76bc859933, 0xbfcf0fa07cd832d6, 0x4046369386acdc5f, 0xe275ec7dd53242a2, 0xdf8755fc88308a04, 0x7160b60c9c962a58, 0x2b2913d27b60219b, 0xc019e14158f2cbce, 0x7d9885ef14701cf4, 0x830c592370be8a34, 0xef81807b0f30002e, 0xefb3c2c0a60229c5, 0xa426c2edfbfa7e65, 0x2841d2ac3c9ad64b, 0x33c88bf54e26371, 0x820851b4e7f17cb, 0x26497628804dc8d3, 0x6725980b83448549, 0x9202c96a455ed520, 0x57d380d6cdc0b22a, 0x2d8d57fc3633ab2e, 0x3006af3ca859a694, 0x6f1435cebf5f430d, 0x72b88bfa4b0c0614, 0xea4f64a256c33f1d]

private theorem rounds127_0 : sixRounds 0 (by decide) absorbed127 = quarter127_1 := by
  decide +kernel

private def quarter127_2 : Vector UInt64 25 :=
  #v[0xd6bd56bc986c77ee, 0x174dd946d5d97574, 0x70d83e14f429cba9, 0xf936ca2d609cff92, 0xb479b46108998d9b, 0x19ae4d8aaae82932, 0xb418d74d6e34f8b2, 0xd45ab9c7cdcea99c, 0xf68ebd61c5913b8b, 0xe2de18ad567c5b4f, 0x732efed92e03b0f4, 0x39b30659305fe237, 0xa5db40a88e4b79, 0xf413a5574dbf5106, 0xcebc249a91c1af5d, 0xc2215a847eb6612d, 0x47cf6aa7ccac8ef1, 0x61d75d76690a44fa, 0x81c5a7bdf1212be6, 0xd5c31201be02df7f, 0x4951997b2ff11041, 0xd04e9473f718af46, 0x47e1ba9152c8d004, 0x4500f9c76ac6c27c, 0xc796d5fd8a522405]

private theorem rounds127_1 : sixRounds 6 (by decide) quarter127_1 = quarter127_2 := by
  decide +kernel

private def quarter127_3 : Vector UInt64 25 :=
  #v[0x4304c2385f6de258, 0x39bba4f06dc89f5d, 0x774ecab13668678d, 0x4e57c176f1add3e8, 0xbe2a63c292baaa24, 0x779fb9d89213c716, 0xa66b7e6eeb342e3c, 0x4dd08620276b3083, 0xdc456eb7a83c8871, 0xae9a39c034d3da61, 0x63b80fd7528af58e, 0x482b38a1ec28a25d, 0x196d3b01deff56ec, 0x3d28f02d155ac208, 0x995d426f4eddcdd7, 0x98f8419e6d114d5a, 0xb0d59dc370288f9a, 0x1f673b239e46599e, 0xe97e3b7efa5771de, 0x5f815bf3b1686ff9, 0xc5a50ab93f2ca88f, 0xde4c4ab98bf2771b, 0xfb2a576fc301fbde, 0x70a1a5b769e13e2a, 0x8a73c9d83d31113e]

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
  exact run_block_of_step bytes127 tail absorb127 state127 absorbed127
    state128 (fun _ => rfl) words127 perm127

private def absorb128 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x82 0xa0 0x60 0x52 0x90 0x8a 0x1 0x82)) 1 (by decide) (UInt64.ofBytes 0x1 0x82 0xc0 0x60 0x52 0x90 0x89 0x1)) 2 (by decide) (UInt64.ofBytes 0x1 0x83 0x80 0xe0 0x60 0x52 0x90 0x88)) 3 (by decide) (UInt64.ofBytes 0x3 0x84 0x80 0x51 0x83 0x52 0x90 0x88)) 4 (by decide) (UInt64.ofBytes 0x0 0x1 0x61 0x52 0x81 0x1 0x91 0x90)) 5 (by decide) (UInt64.ofBytes 0xf 0x60 0x52 0x92 0x90 0x1 0x92 0x90)) 6 (by decide) (UInt64.ofBytes 0x90 0xc6 0x43 0x61 0x90 0x91 0x90 0x54)) 7 (by decide) (UInt64.ofBytes 0x56 0xb5 0x46 0x61 0x86 0x86 0x86 0x86)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x5b)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x14 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x51 0x80 0x40 0x60 0x57 0x48 0x44 0x61)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8 0x7f)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 16 (by decide) (UInt64.ofBytes 0x82 0x4 0x60 0x20 0x60 0x52 0x81 0x0))

private def absorbed128 : Vector UInt64 25 :=
  #v[0xae7efb98924f2c2a, 0x5b333f9b87829b98, 0x76940ed0cd027b94, 0xf2e3f67a1e432c6c, 0xbfb016c309d4fe0a, 0xe979ae089cc6e72d, 0xe951c472f415a5e1, 0xf97d9426fa6be9c2, 0xbf141d2bcee5a006, 0x2d13329b986ad58b, 0x2ea3021cff800f89, 0x306ea758d079aeae, 0x6b7b7943ce0e1d77, 0x6756c577fa9a0a80, 0x685e28849bba1ad1, 0x3a5e190f11621ede, 0xef0d9916505034e8, 0xacc896c70960db67, 0xd9d2177992247592, 0x686dea0db1414c68, 0xe99c9ab477476c22, 0x8bf001d94fe55b63, 0x98fccbd9617c0537, 0x492c4ef9f64c150b, 0x378da5b386b12912]

private theorem words128 : absorb128 state128 = absorbed128 := by
  decide +kernel

private def quarter128_1 : Vector UInt64 25 :=
  #v[0x9cc218d2128067b8, 0xf6312344d05d3e7a, 0x46b297c0eb6a1967, 0x80da1b478252e698, 0x47f0c78c0525c914, 0x34573858cb91c8c7, 0xb880c78e5517004d, 0xf551a7fe34a399e5, 0x8f8c18e43519cbff, 0x1f2aaffb54a0e610, 0x9c3112714c9477c8, 0x8663233fd5cad888, 0x23dd23665f649dfe, 0x31ef135e392619f1, 0x7c2b387ce1f1a134, 0xbbeecbd021966084, 0xd9bf8cdb8ae98d16, 0xdd573188201efbbd, 0x9c1949e6de4a8f9c, 0x8be4d9b08a0b6d94, 0x952660af020ae06f, 0x8de3c4e22e58fcae, 0x9ad4dbb0a0e1ac69, 0xb4716874adee9570, 0xf22ef438f8882290]

private theorem rounds128_0 : sixRounds 0 (by decide) absorbed128 = quarter128_1 := by
  decide +kernel

private def quarter128_2 : Vector UInt64 25 :=
  #v[0xf5cbe09d0fa89acf, 0x3843954e2ea4ed94, 0x88a5a873449d457e, 0x81fdf91a8889972, 0x7cc51900b3bb3fc, 0xc788b358709d4e30, 0x812736c3a788db3b, 0x6317b45d5ede04a1, 0xa7184c8673bde755, 0xd335fac380ea41cb, 0xe152ac90792b7255, 0x3c13b28a851e97b1, 0x4be3f7e718433e39, 0xce4431c993dd0ab2, 0x37eba3be09d37152, 0x2a95080ee92a9ad7, 0x27775f8dc9903cbf, 0xadd0fef48e4d7db7, 0xa632fd67a7081576, 0xbc48692ff2d52f82, 0x25e1ae977a18f1c3, 0xe6460363b7ff960d, 0x9fe43f03c7b33484, 0x62efe3b505dbfb2d, 0xb227e51a119f8880]

private theorem rounds128_1 : sixRounds 6 (by decide) quarter128_1 = quarter128_2 := by
  decide +kernel

private def quarter128_3 : Vector UInt64 25 :=
  #v[0x24bf1758d3bd6b1a, 0x3a074a291d3b8386, 0xdf4bbc260001f922, 0xb55e6fda460ae60e, 0x495707e69be7ca6e, 0x561090c6e02a9d73, 0x1c796958991a2d41, 0x7e0a772a708aede0, 0x14fa88c122c0c290, 0xf7e1ab5680d3de09, 0xcc36d33def90ef9e, 0xb727c76c6a113877, 0xf287ba26cd1964d9, 0xa3a1ade7c2748174, 0x7628604ce37cf5a6, 0x6bda43d48ccf9c2a, 0x5f5aac1b6573060f, 0x13591bfbf711d9d8, 0xff02cdb38991a268, 0xc2d5029f1bfe0926, 0x351d293af87617cf, 0x20a09769bd3656e3, 0x8b7ba69b42a5f0e6, 0x63b47f992ce52db0, 0xd6258165812fd6e4]

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
  exact run_block_of_step bytes128 tail absorb128 state128 absorbed128
    state129 (fun _ => rfl) words128 perm128

private def absorb129 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x1 0x82 0x24 0x60 0x1e 0x60 0x52 0x1)) 1 (by decide) (UInt64.ofBytes 0x6f 0x54 0x74 0x61 0x69 0x46 0x7f 0x52)) 2 (by decide) (UInt64.ofBytes 0x69 0x20 0x3a 0x32 0x56 0x6e 0x65 0x6b)) 3 (by decide) (UInt64.ofBytes 0x73 0x20 0x64 0x69 0x6c 0x61 0x76 0x6e)) 4 (by decide) (UInt64.ofBytes 0x65 0x72 0x75 0x74 0x61 0x6e 0x67 0x69)) 5 (by decide) (UInt64.ofBytes 0x90 0x52 0x1 0x82 0x44 0x60 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x1 0x64 0x60 0x3 0x90 0x81 0x90 0x51)) 7 (by decide) (UInt64.ofBytes 0x86 0x8a 0x52 0x44 0x61 0x5b 0xfd 0x90)) 8 (by decide) (UInt64.ofBytes 0x5d 0x44 0x61 0x5b 0x56 0xbf 0x48 0x61)) 9 (by decide) (UInt64.ofBytes 0x5b 0x56 0x21 0x3b 0x61 0x8a 0x8a 0x8a)) 10 (by decide) (UInt64.ofBytes 0x50 0x50 0x50 0x50 0x50 0x50 0x50 0x50)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x5b 0x56 0x50 0x50)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0xd7 0x44 0x61 0x14 0x33 0x16 0x88 0xff)) 15 (by decide) (UInt64.ofBytes 0x79 0xc3 0x8 0x7f 0x51 0x40 0x60 0x57)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0xa0))

private def absorbed129 : Vector UInt64 25 :=
  #v[0x50842c734a1af96f, 0xe8e5d7b2ee1d3685, 0xdd24e1cbcf7c4153, 0x698645aae549b90c, 0x808771b165e2b1c5, 0x328baf38efd6ed94, 0x356f2bd2ba952567, 0xaf89c232ad8f1c58, 0x62a6aaf6a7e425c0, 0x976e9aad5a7b796e, 0x854c3dc24d6bfcae, 0x71fb60234491496b, 0x31fde635d90e6055, 0x40ba553f44dc6b7d, 0x6f02eaf9d6adca83, 0xe87673824ce992bd, 0x56014ec9eda3320, 0x931c409ec7aa533b, 0x9b5225d2ed02a0, 0x774cd9a7db075a4, 0x821dc2bc0d989df0, 0xb6f76e2c6ec9568b, 0xd65316e16e2f5fac, 0x1cbc0df11f16b1a5, 0x49fca7cc2ad85618]

private theorem words129 : absorb129 state129 = absorbed129 := by
  decide +kernel

private def quarter129_1 : Vector UInt64 25 :=
  #v[0x5d89df2dd4ef9edd, 0xbe1ca3b897cb7b0a, 0x7b0aab526bbfab11, 0xb8ac4a43a1d33924, 0xd0fa3a8c6d6897c, 0x8eaeec8459b9a3c7, 0x5279fd994de38c1a, 0x4fc67157960091fa, 0xc184c93cbb3ef96d, 0x161a9ec1d7a02819, 0x6ce4536a3ab4ef06, 0x6220be8328ef36cb, 0x9e56bfd12dc2c34d, 0x7b860a6e2ae5faba, 0x97e9d3658207512e, 0xaf4db2f4f5c01ed6, 0xec307803c8279a16, 0x8c552e9f7cc990aa, 0x6ae59180656ee36, 0x8853ba0b6e17f886, 0xc87ee5c3629e80dc, 0x65e0b0515d3f5c7a, 0xdcb2dfb6b9a67a46, 0x21f24b714e2fdadc, 0x462b194b6659a5bd]

private theorem rounds129_0 : sixRounds 0 (by decide) absorbed129 = quarter129_1 := by
  decide +kernel

private def quarter129_2 : Vector UInt64 25 :=
  #v[0xf9bb55f3a5c4e8f7, 0x769d0cc0e33a4ab8, 0xa575fc411d6297d7, 0xc3f9f1fa0ada5c4e, 0xba6269956d255a9b, 0x384be07e7af1ec00, 0xc2427e5d4cba61cd, 0x44d141ad0b18f4f, 0x54d0c6f0637494cb, 0x64a477f14df95c9, 0x602b855daedbe96c, 0x719c9efda2ade890, 0x76ff53365f55a5fa, 0x7b4f037fcb4c5956, 0x9bdb1d59e637b94, 0x48f9a25a0def2cf, 0x43d040451b5a9914, 0xd0f1b0679883544b, 0x130abfdf6f7ca21e, 0xa78a221756e67950, 0xb8478f72ad5dc3bb, 0x9691a8c581ff5ef3, 0x899033ad5ca46a9d, 0x80f1e27f2b08cb4d, 0x3b9625fc357442e7]

private theorem rounds129_1 : sixRounds 6 (by decide) quarter129_1 = quarter129_2 := by
  decide +kernel

private def quarter129_3 : Vector UInt64 25 :=
  #v[0x910063a1ab48d1af, 0xf90cc0a531efd67e, 0xe19c73fe13a784b3, 0xba2396750085faf7, 0xaac4da06e740edd8, 0x82dfd7c16d13fff8, 0xd059231bbb939bb0, 0xbe3f6ef1f745fdac, 0x773db4b833f9c1d6, 0xb4c6d1eefad47d0b, 0xb25acffceffbe215, 0x89a5ef9d1ee9a3e5, 0xc22f898f02daed77, 0xc716836e21b18ff0, 0x137eed36fb68c5b8, 0x876ac6c08fb4664c, 0x63368d3ae18864bb, 0x88e7907d73cf2dd2, 0x8d8ef680b4dc476a, 0x34b12a7a888ce031, 0x8cc861867fa8ab3f, 0x17adccbd06dad9e0, 0x835dc0d015421322, 0x199f3ba9fb13a4a7, 0xfafc0acd0a585eb2]

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
  exact run_block_of_step bytes129 tail absorb129 state129 absorbed129
    state130 (fun _ => rfl) words129 perm129

private def absorb130 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x82 0x1 0x20 0x60 0x80 0x80 0x1 0x4)) 4 (by decide) (UInt64.ofBytes 0x52 0x81 0x25 0x60 0x52 0x82 0x3 0x81)) 5 (by decide) (UInt64.ofBytes 0x60 0x87 0x51 0x61 0x80 0x1 0x20 0x60)) 6 (by decide) (UInt64.ofBytes 0x50 0x91 0x1 0x40 0x60 0x39 0x91 0x25)) 7 (by decide) (UInt64.ofBytes 0x90 0x3 0x91 0x80 0x51 0x40 0x60 0x50)) 8 (by decide) (UInt64.ofBytes 0x88 0x85 0x89 0xe3 0x44 0x61 0x5b 0xfd)) 9 (by decide) (UInt64.ofBytes 0x40 0x60 0x5b 0x56 0xff 0x47 0x61 0x88)) 10 (by decide) (UInt64.ofBytes 0xef 0x98 0xcc 0x99 0xd0 0x7f 0x51 0x80)) 11 (by decide) (UInt64.ofBytes 0x94 0xf 0x4f 0x6c 0x61 0x7a 0x10 0x71)) 12 (by decide) (UInt64.ofBytes 0xfe 0x54 0xe2 0xd8 0x22 0xc3 0x4 0x1f)) 13 (by decide) (UInt64.ofBytes 0xae 0x7a 0xb8 0x8d 0x66 0xc6 0xb3 0x26)) 14 (by decide) (UInt64.ofBytes 0x52 0x1 0x82 0x20 0x60 0xe8 0x3d 0x41)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed130 : Vector UInt64 25 :=
  #v[0xee3016b86e623f0e, 0x8945272fb3ff1f4d, 0x822ce21d765e3c1c, 0xe4e1728650a8be6b, 0xd51168c13b2be573, 0xa84e9a89f2aeedaa, 0x5b9efa476664d9f1, 0x53da5eabf0cbcc93, 0x1bf9290fef1a5797, 0xc14220d9f2dd18f8, 0x1c8b1a3480272563, 0x7e74cc5050b5f7e8, 0xe9f2d6483e7707f4, 0x8db052ef855bb4e8, 0xf292873d06bec212, 0xc62007bf6e265113, 0x22a6486808b2f2ac, 0xdfdeb672f4b6741c, 0x71f2bd92887da217, 0x8ec0494c8845d183, 0x44fb7b80c6c1edd5, 0xf222e2c99ea44f2c, 0xb6a35f1bcd8772e7, 0x49041376eb7c0973, 0xb7be5e0586deb00a]

private theorem words130 : absorb130 state130 = absorbed130 := by
  decide +kernel

private def quarter130_1 : Vector UInt64 25 :=
  #v[0xd642b3c50088dc7d, 0xfc10af478d168a01, 0xcef12eff2a6da97, 0x676e409fab24021e, 0xa0ca496bc14fc3c8, 0x455d37334f9ec491, 0xb23130d4d396c131, 0x51f29571e88c604e, 0xe64f561c851b69a9, 0xf1265ed047f7243b, 0x34fe2ce323a6f2ca, 0xda34a65e9192b87c, 0x1f50f4c11221ed7e, 0x7e1c609150c2073e, 0x209778ea2a9e66ba, 0x79331e4a01414a6e, 0x1a85f28c985b3438, 0x50d5d2658d78bd3f, 0x4159bb25ce5f9826, 0x38dd041db6cda4e, 0x4b896cf11e13ae01, 0x68a4eaf2687375db, 0xe23ab11004e060f4, 0xc0cd7392ded7d10f, 0xd50de0db500162ed]

private theorem rounds130_0 : sixRounds 0 (by decide) absorbed130 = quarter130_1 := by
  decide +kernel

private def quarter130_2 : Vector UInt64 25 :=
  #v[0x45ad9f0d80b046db, 0x94f3d291bb872612, 0x7b298456309294c2, 0xac3bd0ff339a677, 0xb8eccef38786d027, 0x2b1f92891beee417, 0x12e5a8e8182d49b7, 0x475c44eb2f2b1091, 0x10a3f201a9d3e0a6, 0x11ecbb8f0af38f70, 0x7e6a0caba2a0605b, 0x84950d0827d089fd, 0xfa1aaad18a8171d7, 0xa03f73be6050af92, 0xc03a41f5edc2cdd3, 0xc7c61e6acde058e5, 0x576faa346f6d22d7, 0x8cddbfce13855c6c, 0x6c663cdac832522c, 0x31ae866b3b1840ac, 0xfd72d187475267ab, 0xe29c0b4a771f35fc, 0xe42e2c5a7ac5dc2a, 0x49ceb2603f71d900, 0xf8bd62b1505fe09f]

private theorem rounds130_1 : sixRounds 6 (by decide) quarter130_1 = quarter130_2 := by
  decide +kernel

private def quarter130_3 : Vector UInt64 25 :=
  #v[0x6f193f066f9589a6, 0xeb0b8872bf52b522, 0xba1d6ca9ae13bd50, 0x81b2c7e764c0d878, 0x3df528f2f0534ada, 0xddc580e6a442cf01, 0xc390ccc952fe0050, 0x2528c0fe1d3d5105, 0x61c548296dc638e7, 0x5bd7519b6cb1132e, 0xeff3ab0a095a1397, 0x643d3b17f5f19bcb, 0x5173fa82fae99646, 0x572e044dab449870, 0x871d6c8b0b63e38e, 0x9ccf56f2913a097, 0xbc446a0c8a1aa096, 0x50a8361d8494fc56, 0x149824355516e90d, 0x98239275f2c93e9, 0x93664f7f2e4ff767, 0x77292150b0240b4e, 0x6bdff675b36daae6, 0x41706595cd92a1ee, 0xdfe5557bf53fdccf]

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
  exact run_block_of_step bytes130 tail absorb130 state130 absorbed130
    state131 (fun _ => rfl) words130 perm130

private def absorb131 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x16 0x8c 0x80 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x8b 0x90 0x52 0x90 0x81 0x1 0x84 0x82)) 2 (by decide) (UInt64.ofBytes 0x80 0x60 0x52 0x1 0x83 0x60 0x60 0x16)) 3 (by decide) (UInt64.ofBytes 0x82 0xa0 0x60 0x52 0x90 0x8a 0x1 0x82)) 4 (by decide) (UInt64.ofBytes 0x1 0x82 0xc0 0x60 0x52 0x90 0x89 0x1)) 5 (by decide) (UInt64.ofBytes 0x1 0x83 0x80 0xe0 0x60 0x52 0x90 0x88)) 6 (by decide) (UInt64.ofBytes 0x3 0x84 0x80 0x51 0x83 0x52 0x90 0x88)) 7 (by decide) (UInt64.ofBytes 0x0 0x1 0x61 0x52 0x81 0x1 0x91 0x90)) 8 (by decide) (UInt64.ofBytes 0xf 0x60 0x52 0x92 0x90 0x1 0x92 0x90)) 9 (by decide) (UInt64.ofBytes 0x90 0xc6 0x43 0x61 0x90 0x91 0x90 0x54)) 10 (by decide) (UInt64.ofBytes 0x56 0xb5 0x46 0x61 0x86 0x86 0x86 0x86)) 11 (by decide) (UInt64.ofBytes 0x15 0x11 0x84 0x84 0x81 0x0 0x60 0x5b)) 12 (by decide) (UInt64.ofBytes 0x7f 0x51 0x40 0x60 0x57 0x1f 0x46 0x61)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8)) 14 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0))

private def absorbed131 : Vector UInt64 25 :=
  #v[0x64dc7eaa3b48713b, 0x8f95d0ff660e94c5, 0x201276fbbd5c0126, 0x28ec3efa38b346ce, 0xbe96893f4fcc7857, 0x8984874ea8ee8216, 0xa3d8290a31ace3d2, 0x8d787af8dcc5cdf2, 0x49c78df64873d032, 0x8859af45ed56abae, 0xa0027cd74b6eb565, 0xeab8d21c51986bf3, 0x1e1103ed48da64df, 0x26a2287e69dd23af, 0xee6153a991dbf471, 0x6986d36948b2a295, 0xc39d27121cad3156, 0x1fd72ba49e85eb54, 0x182bd3670b3fce90, 0x75809f09b2425176, 0x396833128fd2c655, 0xb76af4bb3d87cc55, 0xdeed85d7df21a80e, 0xec9b67fe53c77883, 0x8154c0f935791509]

private theorem words131 : absorb131 state131 = absorbed131 := by
  decide +kernel

private def quarter131_1 : Vector UInt64 25 :=
  #v[0xac946f1c8effb41d, 0x63d7da5cac1a0060, 0x96fb6b5c66425316, 0x4337912657567275, 0x8a2b2e03c80c55d0, 0x5c8bbe844f2b28c4, 0xaeaa08db91d861e7, 0x868597062c5f4cd3, 0x3afed5a6f83fd116, 0x54d613fa2a5c438f, 0x93a8ec281b500336, 0x5546627a6f6a9869, 0x35204e4e9da1215c, 0xc1c8e541b85ae6d9, 0x73ab5c585e729b7b, 0x3f386daa45bdf2d5, 0xcb82fee0aadcdbcb, 0xd914a21a57f1f088, 0x2a197ac83f5b18a1, 0xe669dbb1cb47e208, 0xd6779dd0c436ca72, 0x88334f569e638ac4, 0xa46d9f7ed85c686a, 0xd883471de194e3b3, 0xa2e168f7d2f9a131]

private theorem rounds131_0 : sixRounds 0 (by decide) absorbed131 = quarter131_1 := by
  decide +kernel

private def quarter131_2 : Vector UInt64 25 :=
  #v[0xe9f068f3aa14388, 0xb3cf93857688e77b, 0xdea77c783c625d87, 0xaa8857d446d49344, 0xd4d6e3e1dfefb246, 0xdcf0f33449d3cd95, 0xf56d8c9a6d466d58, 0x8af7ab36e3fa8374, 0x97fdb1f0c0fc25e0, 0xaccb51639436d292, 0x23456fd3170e7c24, 0x718c02a709cfd37d, 0xe13ae41e51713b8a, 0xac9bad44d14efbf9, 0x4b81eedf88f0cb8f, 0x8ed7ef94f2119258, 0xafcd1836c7ef90b4, 0x74dfe0b9383a9d9c, 0x79f3abce8ee90aeb, 0xb02ef65342a6a1f9, 0x76feea5ee61f9b8b, 0xe8e9fd98dc3f77f3, 0x938c56b3f6e5871d, 0xfb2e59b9efc793fa, 0x6fe8bfe6817cad50]

private theorem rounds131_1 : sixRounds 6 (by decide) quarter131_1 = quarter131_2 := by
  decide +kernel

private def quarter131_3 : Vector UInt64 25 :=
  #v[0xef9d9cae938cf7e6, 0xf4257849b221d122, 0x8df43bb7bee27612, 0x6f34f4115a0ff5c6, 0x221ca5c403e25c98, 0x734d81748b4af49f, 0xc025e4b2286f49f2, 0x20051078d55946d0, 0xa0168b3ce48413c0, 0xf22d539786fda83a, 0xf7c4447fb04a3336, 0x997f67ec742d5c9c, 0xcf157fd29ac673cd, 0x9b8b3ed2cbfb9edf, 0x23b0b4c2d6780f21, 0xb8c29c981b3f6c0f, 0x7792a0367e4268a6, 0x4c1a89335d72e03, 0x9778b7182e936f44, 0x7d981cc7c5a9d6f9, 0xcdf1094a3a082b34, 0xb53f70f0edfb4d6f, 0xeec8e01303af89b9, 0xd7d52555f9035a78, 0xb42364ac2d8f6d14]

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
  exact run_block_of_step bytes131 tail absorb131 state131 absorbed131
    state132 (fun _ => rfl) words131 perm131

end Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
