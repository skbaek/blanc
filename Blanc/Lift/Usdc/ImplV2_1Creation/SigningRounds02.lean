import Blanc.Lift.Usdc.ImplV2_1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb012 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x91 0x90 0x91 0x1 0x92 0x0 0x60 0x37)) 1 (by decide) (UInt64.ofBytes 0x20 0x60 0x93 0x94 0x95 0x92 0x50 0x52)) 2 (by decide) (UInt64.ofBytes 0x50 0x50 0x91 0x35 0x50 0x93 0x1 0x81)) 3 (by decide) (UInt64.ofBytes 0x11 0x81 0x0 0x0 0x0 0x0 0x1 0x64)) 4 (by decide) (UInt64.ofBytes 0x80 0x0 0x60 0x57 0xf 0x6 0x61 0x15)) 5 (by decide) (UInt64.ofBytes 0x82 0x20 0x60 0x83 0x1 0x82 0x5b 0xfd)) 6 (by decide) (UInt64.ofBytes 0x60 0x57 0x21 0x6 0x61 0x15 0x11 0x1)) 7 (by decide) (UInt64.ofBytes 0x60 0x90 0x35 0x80 0x5b 0xfd 0x80 0x0)) 8 (by decide) (UInt64.ofBytes 0x2 0x83 0x1 0x60 0x84 0x91 0x1 0x20)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x1 0x64 0x11 0x1 0x84)) 10 (by decide) (UInt64.ofBytes 0x43 0x6 0x61 0x15 0x17 0x11 0x83 0x0)) 11 (by decide) (UInt64.ofBytes 0x90 0x91 0x5b 0xfd 0x80 0x0 0x60 0x57)) 12 (by decide) (UInt64.ofBytes 0x80 0x20 0x60 0x1 0x1f 0x60 0x80 0x80)) 13 (by decide) (UInt64.ofBytes 0x40 0x60 0x1 0x20 0x60 0x2 0x4 0x91)) 14 (by decide) (UInt64.ofBytes 0x80 0x52 0x40 0x60 0x1 0x81 0x90 0x51)) 15 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x81 0x90 0x91 0x92 0x93)) 16 (by decide) (UInt64.ofBytes 0x37 0x84 0x82 0x80 0x83 0x83 0x1 0x20))

private def absorbed012 : Vector UInt64 25 :=
  #v[0x778158537888326d, 0x8c5d85012716a074, 0xe3bca17e72019336, 0x1e3216a13cae225b, 0x4748e780fc8fed5d, 0x2a52d40db91c6d, 0x6d2081e1b41df8c3, 0x55d9959fcfeb12c, 0x46b2f0f18bf383d1, 0x14e0fbfeed49bfd7, 0x9881051f5b481d93, 0x9df0333f67744673, 0xd7b9ec4724f68a23, 0xe7170083f214b44c, 0x7895a483da14020d, 0x20aa218553d52d14, 0x12aa2719c5f648f, 0xa80e80476d5948df, 0x95404061293a8603, 0x2f2ff734e75146be, 0xf03fe88c28ab7789, 0x963c59089a61cff1, 0xd3d5d870e3ff000a, 0x26640b96c4d2c8d3, 0x4c4510ea05358994]

private theorem words012 : absorb012 state012 = absorbed012 := by
  decide +kernel

private def quarter012_1 : Vector UInt64 25 :=
  #v[0xbc0ecae7478f7da9, 0xc23f9dc386ea7efc, 0x7f5de7143bf23b41, 0x63784b916671a322, 0x254316cbe57f4f97, 0xe80417d41e02d65e, 0x8c2cafe9dcf54a26, 0xd69ccafb47ace6af, 0xa892c3a68a7588cd, 0x7633d8334de43a04, 0x14a8616951b44c3e, 0xf8d75f1c9798f472, 0x3444443b3ce9ed9a, 0x3e7ad7cd2c0e8fd, 0xad0a1aa1f810f46, 0xd6bfeec89b20a1f6, 0x153c4f2365bc6c, 0x986d45420eb24201, 0xfdc7cf03f0b5e4e, 0x18b728d248ca4fe2, 0x88a2151c0025d3a8, 0x5e7aecb981c3d2f6, 0x74e328840516f0a0, 0x29520c5bb3b3f344, 0xd67a6acab5e9fdb3]

private theorem rounds012_0 : sixRounds 0 (by decide) absorbed012 = quarter012_1 := by
  decide +kernel

private def quarter012_2 : Vector UInt64 25 :=
  #v[0x9dc0bcaf712962fe, 0xd12c9b69af1420d9, 0xed409875bf85ab46, 0xeb2581d7a067fc2c, 0x2fc530880024fc9a, 0x25c4cf9bc9392c6a, 0x81a11c2c9f887234, 0x2a05ab3294d9b949, 0xd63806289bbb0b15, 0xd6be0c9012b43ec8, 0x43424f7bd95e1663, 0xff4fa93762a3486c, 0x104a7d4e9d5e1eae, 0x965d7c371523bdb8, 0x574f3e6ea6021da1, 0x32dffaa23cb65e7f, 0x1865e20644b2e79e, 0x3e27e59ead5de13c, 0xdafdafe5a26a2e10, 0xca37e135707e3d9c, 0x70ae55a1dabc4526, 0x6ebe79aa1ce3632, 0x9ed7fbfcf9ab9c5b, 0xbd73c74d6bac6654, 0x3e897076a1c2b6e8]

private theorem rounds012_1 : sixRounds 6 (by decide) quarter012_1 = quarter012_2 := by
  decide +kernel

private def quarter012_3 : Vector UInt64 25 :=
  #v[0x852712ea8f246b58, 0x1af803b3695123cc, 0x8eba62f52a8e8bfa, 0x5c5dce10dea48abf, 0x10661fd928c8f5e6, 0xdbcd1e8fd6af86d6, 0x490c58053192819, 0xbfbaac8837977698, 0xb05e442f9bb60016, 0xed613b03c5bf42c2, 0x17ef2f442c0eb521, 0xcabfa23f78b3c6a4, 0x5bbdb434b2ee4d3e, 0xe893f69fca005cfe, 0x52fbf8f1de1f2080, 0x7afbb8a9a9f1e42a, 0xc4ffc1f6c780e935, 0xbdc76628a391f05b, 0x1b322a670ee55f1e, 0xc882a5ebbbc8ef2c, 0xa4e357951d86075c, 0xcd4b53fa1d1126e2, 0x591563fa516e3719, 0xbc37a78223a65c2d, 0xd5f46e33af8f2e7f]

private theorem rounds012_2 : sixRounds 12 (by decide) quarter012_2 = quarter012_3 := by
  decide +kernel

private theorem rounds012_3 : sixRounds 18 (by decide) quarter012_3 = state013 := by
  decide +kernel

private theorem perm012 : KECCAK.f1600 absorbed012 = state013 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds012_0, rounds012_1, rounds012_2, rounds012_3]
  rfl

theorem block012 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes012 ++ tail) state012 =
      KECCAK.Bytes.run 0 tail state013 := by
  exact run_block_of_step bytes012 tail absorb012 state012 absorbed012
    state013 (fun _ => rfl) words012 perm012

private def absorb013 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x52 0x91 0x90 0x91 0x1 0x92 0x0 0x60)) 1 (by decide) (UInt64.ofBytes 0x81 0x20 0x60 0x93 0x94 0x95 0x92 0x50)) 2 (by decide) (UInt64.ofBytes 0x64 0x50 0x50 0x91 0x35 0x50 0x93 0x1)) 3 (by decide) (UInt64.ofBytes 0x15 0x11 0x81 0x0 0x0 0x0 0x0 0x1)) 4 (by decide) (UInt64.ofBytes 0xfd 0x80 0x0 0x60 0x57 0x96 0x6 0x61)) 5 (by decide) (UInt64.ofBytes 0x1 0x82 0x20 0x60 0x83 0x1 0x82 0x5b)) 6 (by decide) (UInt64.ofBytes 0x0 0x60 0x57 0xa8 0x6 0x61 0x15 0x11)) 7 (by decide) (UInt64.ofBytes 0x20 0x60 0x90 0x35 0x80 0x5b 0xfd 0x80)) 8 (by decide) (UInt64.ofBytes 0x84 0x2 0x83 0x1 0x60 0x84 0x91 0x1)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x1 0x64 0x11 0x1)) 10 (by decide) (UInt64.ofBytes 0x57 0xca 0x6 0x61 0x15 0x17 0x11 0x83)) 11 (by decide) (UInt64.ofBytes 0x80 0x90 0x91 0x5b 0xfd 0x80 0x0 0x60)) 12 (by decide) (UInt64.ofBytes 0x91 0x80 0x20 0x60 0x1 0x1f 0x60 0x80)) 13 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x1 0x20 0x60 0x2 0x4)) 14 (by decide) (UInt64.ofBytes 0x93 0x80 0x52 0x40 0x60 0x1 0x81 0x90)) 15 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x81 0x90 0x91 0x92)) 16 (by decide) (UInt64.ofBytes 0x60 0x37 0x84 0x82 0x80 0x83 0x83 0x1))

private def absorbed013 : Vector UInt64 25 :=
  #v[0x55a57329e15392b5, 0x38d7118ca30c73b7, 0x6098fc24d224f43b, 0xc71d080c93022664, 0x22e0536acacb1226, 0x334668bfe7bc4082, 0xa33df765095304c6, 0xcafe23ab8782b756, 0xb7b1cfec2f71530a, 0xfd0d1e999f3c3b6d, 0x826e0f30c167e20f, 0xa6cdaa6cad21cf3a, 0x5afbd398114fcfd5, 0x1d905f5f83afbd1d, 0x7f1fdf0974d32813, 0x190c972de4137dc0, 0x81e04287056dd55b, 0x74d672d9c2aecbb5, 0xea49543cd6a6c831, 0xa1df0668eed04444, 0xb5b66e2eb3baa065, 0x8c3e768d13ef883c, 0x9ca03c4159ec7b7b, 0xca393bf67de0add4, 0xc203b816b0e6c244]

private theorem words013 : absorb013 state013 = absorbed013 := by
  decide +kernel

private def quarter013_1 : Vector UInt64 25 :=
  #v[0xd2d18a446676c5da, 0x44d616e6ceab6893, 0x4d632ff4e900ebee, 0x14212228837a0b2, 0xf8778a325d9fbc53, 0x34dddebd62d9f539, 0x6924338999fffb14, 0x2629351086c5c3e9, 0x4fbce27508bd4cf, 0xc8caafeb45aa1101, 0xee287b7a542d2a03, 0x30a655236efccf9, 0x762759588898eddb, 0x781eaaf9e2513a61, 0xa1a5392d57e3a368, 0x1cb817ef9a54f0e6, 0x4abf5b5341b7acb2, 0xc45f419858689ae7, 0x7632c982550c05e9, 0x19b5a3a6c9557d3b, 0x4cfff49ed1b6432d, 0xb6c8577ae26f541, 0xdf406e45545b365c, 0x746c9fe6826ba390, 0xfcd16fc5555f0c28]

private theorem rounds013_0 : sixRounds 0 (by decide) absorbed013 = quarter013_1 := by
  decide +kernel

private def quarter013_2 : Vector UInt64 25 :=
  #v[0x330444d9f7b5cb19, 0xb90b9ea01e1baddd, 0xac7711c0951ebccc, 0x7b1637730edd965e, 0x529e2a051bbf92c5, 0x9b96e02424b91c23, 0xcc96cb3e817a59fe, 0xf7bdceb6c85fe6db, 0x5bc9ce677adbcf9c, 0xb008a8b7bcc371dd, 0xf37ce0c5eb067ccd, 0x90227e6985cfaa9, 0x4877610b85272949, 0x239b1d2cffc3c2fb, 0xb1866dd7c6504ece, 0x6278953f2dd5ae56, 0xb9c3dffd7d868bdd, 0xd0d9fc2d00491ef6, 0xe8eb15396e4e3819, 0x13bd31693a9135a8, 0xc4b1a8998560b6d7, 0x5a75f50c9e60758, 0xa477532f8ba95703, 0x33eaaa28d66cbb22, 0x619054acbdd06ae4]

private theorem rounds013_1 : sixRounds 6 (by decide) quarter013_1 = quarter013_2 := by
  decide +kernel

private def quarter013_3 : Vector UInt64 25 :=
  #v[0x2e7ac93666544442, 0xdb17a1fcdf9c1465, 0x160b713333291ed5, 0x873283e3eec692fa, 0x9d3de8d98db4aac6, 0xcbd7193d75e6b610, 0xa00100f5b5ba985b, 0x7681377ae4659e08, 0x36a35ba556599259, 0xc78bcae63052509e, 0x774ac0784abc87cf, 0x393355d76cb741a6, 0x63276d0388b8e7e8, 0x8b9e15c9197e9bfd, 0x242d3194e61c21eb, 0x914afb74e427833a, 0x3445f54d05387d0f, 0xbbfa09f273acea7b, 0xcff17c0a748cc2cb, 0x769afada8633bed6, 0xe85c22e3042e6a69, 0x57ea5d1970477fd4, 0x2136183cd608b50a, 0x3f3bcb3df2c828a3, 0x2d6113b99032ba68]

private theorem rounds013_2 : sixRounds 12 (by decide) quarter013_2 = quarter013_3 := by
  decide +kernel

private theorem rounds013_3 : sixRounds 18 (by decide) quarter013_3 = state014 := by
  decide +kernel

private theorem perm013 : KECCAK.f1600 absorbed013 = state014 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds013_0, rounds013_1, rounds013_2, rounds013_3]
  rfl

theorem block013 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes013 ++ tail) state013 =
      KECCAK.Bytes.run 0 tail state014 := by
  exact run_block_of_step bytes013 tail absorb013 state013 absorbed013
    state014 (fun _ => rfl) words013 perm013

private def absorb014 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x50 0x52 0x91 0x90 0x91 0x1 0x92 0x0)) 1 (by decide) (UInt64.ofBytes 0x60 0x35 0x81 0x50 0x50 0x50 0x95 0x92)) 2 (by decide) (UInt64.ofBytes 0x81 0x20 0x60 0x50 0x50 0x92 0x16 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x35 0x1)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x90 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x35 0x1 0x81 0x40 0x60 0x91 0x16 0x81)) 7 (by decide) (UInt64.ofBytes 0x35 0x1 0x82 0x60 0x60 0x91 0x16 0x82)) 8 (by decide) (UInt64.ofBytes 0x16 0x35 0x1 0x80 0x60 0x91 0x16 0x81)) 9 (by decide) (UInt64.ofBytes 0x4a 0x7 0x61 0x5b 0x56 0xf4 0x16 0x61)) 10 (by decide) (UInt64.ofBytes 0x80 0x40 0x60 0x5b 0x56 0x36 0x1a 0x61)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x51)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x92 0x90 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x3 0x90 0x81 0x90 0x51 0x52 0x82 0x16)) 15 (by decide) (UInt64.ofBytes 0x4 0x61 0x5b 0xf3 0x90 0x1 0x20 0x60)) 16 (by decide) (UInt64.ofBytes 0x7 0x61 0x5b 0x56 0x52 0x1a 0x61 0xd))

private def absorbed014 : Vector UInt64 25 :=
  #v[0x2d9b877afc4655f3, 0xa6d2a35980ab2850, 0x88ef882dd27bd8bb, 0x6ad666b65782d631, 0x73dcb3dae4f9c320, 0x24754bdac6b95f27, 0xfb4339ec061e717b, 0x26bce644d7e3474, 0x98f640541d3ecf2, 0x2b5be5476b65957f, 0x4ecd91cec5e0e882, 0x6a99515b4c750ec5, 0xbe04e7b74a45fdd7, 0x4223f9f4a51ccce7, 0x720f0dbc2eb8f0b9, 0xc0fc0f1fea5cde92, 0xb8693ccd48189dd0, 0x4796852f111aa31c, 0x76bdccade601da21, 0x9ad95d203816bf0, 0x302d8cb30e92f3cc, 0x6737406416aecb88, 0xb9164aef9bddfad1, 0xe9c59b8a68a64abb, 0x48976437b303068c]

private theorem words014 : absorb014 state014 = absorbed014 := by
  decide +kernel

private def quarter014_1 : Vector UInt64 25 :=
  #v[0xfcf7796c67c47af3, 0xbf277aac449c3971, 0xc948d8bd1c297347, 0xba4bc63f1b2b0b9c, 0x1b2435e94d0f46b7, 0x53afaca147c104a8, 0xaf402171dbffedf4, 0x6a1dbf84883a246, 0x5b2b6964c14f1111, 0x15b3151b7f2cf1e6, 0xe6c68cb81ecd1970, 0x60d7d44150b163d8, 0xd38df7cb80aba819, 0xeeba70104fbe9c7, 0x550177231c16da8, 0x3f3d014240cdf7c6, 0x7423d4da3efe8308, 0xb18a1dc3d3418f13, 0x97082f00faf4d751, 0x26b21da3406c9af8, 0x4c74823b0ddeb737, 0x4257703090f51f86, 0x9e10e54b5907677f, 0x9a9a3564f4bda517, 0x111150ff7ac2c3ed]

private theorem rounds014_0 : sixRounds 0 (by decide) absorbed014 = quarter014_1 := by
  decide +kernel

private def quarter014_2 : Vector UInt64 25 :=
  #v[0xb8a3d723e57c5a28, 0x1b504d9ba3735f4a, 0x78b34d0aa8250049, 0x9eac2e4e94fab496, 0x3ef4fea59c591d95, 0x8812cbbf8f5629ac, 0x17fe5badf41a75f9, 0x4fcd4dd51f4322a3, 0x2bf3d9f03eed775c, 0xb4ca792a3519cfed, 0x63d2e708bc51cc4e, 0x9129db0e19c7a625, 0x36a28ab9620f7d89, 0x142dde998168b1ae, 0xc622e8245b063a9b, 0xf6a1b182e93f6222, 0xd05a39d9b0d24fd4, 0xb7f12b3b0279a96b, 0xde9d32dc2f39ec57, 0x18367a5c7facd950, 0x566e375e4bd1f840, 0xeddf025565670f8d, 0xa08ac36e164bf96f, 0x2c5e3603e981cfee, 0x6a8bdd2f90a830e]

private theorem rounds014_1 : sixRounds 6 (by decide) quarter014_1 = quarter014_2 := by
  decide +kernel

private def quarter014_3 : Vector UInt64 25 :=
  #v[0xe967eb0a92f06356, 0x2f1c31f760d9460b, 0xb79a103b4ce4bbc6, 0x7ead765de9d823c0, 0x478d674c1a32b29, 0xfea3b89bd5d6a143, 0xb5803213b5478f5d, 0x33e6ad4897247dbf, 0xd1444af86a81b3c3, 0xcecbfcb1797ae439, 0x30e25113e27d5c4e, 0x8b619cc03fc75648, 0x286811e391382d04, 0xd63d6fd32e99c232, 0xfdbe75aa0a1942ce, 0x57168ed734990239, 0xce85ad5374760c8e, 0x63431171ff0247ab, 0x35f211f7b18bbc08, 0xf308e3809f110599, 0x69150e5120c25872, 0x2221841f00c85b5c, 0x9efd899abf2d2bee, 0xd08f251ed731806b, 0x9a8b6f08b53d603d]

private theorem rounds014_2 : sixRounds 12 (by decide) quarter014_2 = quarter014_3 := by
  decide +kernel

private theorem rounds014_3 : sixRounds 18 (by decide) quarter014_3 = state015 := by
  decide +kernel

private theorem perm014 : KECCAK.f1600 absorbed014 = state015 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds014_0, rounds014_1, rounds014_2, rounds014_3]
  rfl

theorem block014 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes014 ++ tail) state014 =
      KECCAK.Bytes.run 0 tail state015 := by
  exact run_block_of_step bytes014 tail absorb014 state014 absorbed014
    state015 (fun _ => rfl) words014 perm014

private def absorb015 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x3 0x61 0x5b 0x56 0x58 0x1a 0x61 0x4a)) 1 (by decide) (UInt64.ofBytes 0x40 0x60 0x3 0x36 0x80 0x4 0x60 0xf1)) 2 (by decide) (UInt64.ofBytes 0x60 0x57 0x99 0x7 0x61 0x15 0x10 0x81)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x50 0x5b 0xfd 0x80 0x0)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x20 0x60 0x90 0x16 0x35 0x81 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x61 0x5b 0x56 0x74 0x1a 0x61 0x35 0x1)) 8 (by decide) (UInt64.ofBytes 0x61 0x5b 0x56 0xf6 0x1b 0x61 0x52 0x4)) 9 (by decide) (UInt64.ofBytes 0x60 0x3 0x36 0x80 0x4 0x60 0xf1 0x3)) 10 (by decide) (UInt64.ofBytes 0x57 0xda 0x7 0x61 0x15 0x10 0x81 0x40)) 11 (by decide) (UInt64.ofBytes 0xff 0x73 0x50 0x5b 0xfd 0x80 0x0 0x60)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x60 0x90 0x16 0x35 0x81 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x5b 0x56 0xb9 0x1c 0x61 0x35 0x1 0x20)) 16 (by decide) (UInt64.ofBytes 0x3 0x36 0x80 0x4 0x60 0x52 0x4 0x61))

private def absorbed015 : Vector UInt64 25 :=
  #v[0x5d061405ff0786aa, 0xc57702bb5c21491e, 0x341ab6f5bc3eca22, 0x20d72ae8980af8f4, 0x64ce15c0e3658101, 0x4987cfe88fb59cb9, 0x5b634e044dfae19e, 0x7da1c6c2b4cfe6d0, 0x41d3e54388a345f, 0x82bc8652e7fe819f, 0x70187077647ee330, 0xb1687672a20c1e19, 0xedf4e2da11de9eba, 0xd6d99b62448118ea, 0x2b8a9635e5ded4c8, 0x20e9bd6edefbc349, 0xc395f14087e449a7, 0x2c4ef5d3588e5a15, 0xfb4e0a6e5f0e2049, 0x897b1d91e27bb36, 0xa62894ee3d3a5faa, 0x6cabe0a16bc22586, 0x19f374c491748b47, 0xee81f3203a50b678, 0xc9de8cf1f6cf1b6a]

private theorem words015 : absorb015 state015 = absorbed015 := by
  decide +kernel

private def quarter015_1 : Vector UInt64 25 :=
  #v[0x704f59ac40c2f045, 0x63acea8addc933a7, 0x94519871c98a2f14, 0xa609886d1966dea6, 0x3237d9d761149b40, 0x61838dcd2113777d, 0x9939e6dff3aa4e05, 0x4b59c1869f36bbbb, 0x56f7261335924b26, 0xd1f625c2c861e9c3, 0x50e1a04266f571cc, 0x30b97d79c567aeef, 0xcc361fe208dd4460, 0xe62e10abcb372e96, 0x10ac332d33dc1e01, 0x27eb15c1163b113a, 0xedff66314aea6870, 0x48f5cc15954b0841, 0x449c57b5f89dc292, 0xa04b7bf2e34e11b6, 0x8685f2862d67dcde, 0x962c3766beefbe77, 0x11d30a4a3cf01f6e, 0xea3ad8a8fca50997, 0x549a9b10da42c5df]

private theorem rounds015_0 : sixRounds 0 (by decide) absorbed015 = quarter015_1 := by
  decide +kernel

private def quarter015_2 : Vector UInt64 25 :=
  #v[0x2804067769d4d9c4, 0x40497db88986c942, 0x8e6efb1b29a33757, 0x6e7fc96d6510a783, 0x6b54da87bbfde6ef, 0x7572f593dad2cd0e, 0xeb0c2c7cc0fe1f00, 0x6e4c8d4b881d2d8f, 0x227ecb29477fbcf0, 0x387cea9a87851b02, 0x85c85e3b42f7e7a, 0x4b114a242de1b834, 0x356652645ffc32c1, 0x9ecc1f35f3a262, 0xa8bda956e3f93556, 0x1f34cafb98ad8599, 0x478ab3ffb05776eb, 0x6115f8cef15c6660, 0x7c7cac4f26d5e4f4, 0xa3fbdb672174bca3, 0x199028e0bc8387cd, 0x62a63ce8ea17123, 0xbac95c594668212, 0x4e5101a351a49d3f, 0xecc687c1a86c827c]

private theorem rounds015_1 : sixRounds 6 (by decide) quarter015_1 = quarter015_2 := by
  decide +kernel

private def quarter015_3 : Vector UInt64 25 :=
  #v[0x85328a8ff69550f5, 0xe9ff6f16d04b8adf, 0x55eb344045927381, 0xaae753bf04126bdb, 0xd050b540d9510135, 0x41a0280d91a01a37, 0x6bfe05e25bbc8b4f, 0xf05f2d601c53b7c1, 0x6d2c77e4b3bd3208, 0xdfb99d4942ca63c0, 0xf197a87192cd53b3, 0x70b069798631d8d0, 0x77bec94022534e9c, 0xaeeaabcde47b3e16, 0x1f38958845a6ace5, 0x2ce2b1c1ba0ade4c, 0x59869106829b718a, 0x405e629c06f75055, 0x41af62b2201c1d52, 0x38c9315a59ec2123, 0xb339fea33cdb4839, 0x6eecd5f6f24f9ec6, 0x50263ac54ed3467, 0x65818ece7d1414cd, 0xd97340918912afd6]

private theorem rounds015_2 : sixRounds 12 (by decide) quarter015_2 = quarter015_3 := by
  decide +kernel

private theorem rounds015_3 : sixRounds 18 (by decide) quarter015_3 = state016 := by
  decide +kernel

private theorem perm015 : KECCAK.f1600 absorbed015 = state016 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds015_0, rounds015_1, rounds015_2, rounds015_3]
  rfl

theorem block015 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes015 ++ tail) state015 =
      KECCAK.Bytes.run 0 tail state016 := by
  exact run_block_of_step bytes015 tail absorb015 state015 absorbed015
    state016 (fun _ => rfl) words015 perm015

private def absorb016 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x13 0x8 0x61 0x15 0x10 0x81 0x20 0x60)) 1 (by decide) (UInt64.ofBytes 0x35 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57)) 2 (by decide) (UInt64.ofBytes 0xf1 0x3 0x61 0x5b 0x56 0xee 0x20 0x61)) 3 (by decide) (UInt64.ofBytes 0x81 0x40 0x60 0x3 0x36 0x80 0x4 0x60)) 4 (by decide) (UInt64.ofBytes 0x0 0x60 0x57 0x30 0x8 0x61 0x15 0x10)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x50 0x5b 0xfd 0x80)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x90 0x16 0x35 0x81 0xff)) 9 (by decide) (UInt64.ofBytes 0x3 0x61 0x5b 0x56 0xa8 0x23 0x61 0x35)) 10 (by decide) (UInt64.ofBytes 0x4 0x61 0x5b 0x56 0x3b 0x25 0x61 0x43)) 11 (by decide) (UInt64.ofBytes 0x20 0x60 0x3 0x36 0x80 0x4 0x60 0x52)) 12 (by decide) (UInt64.ofBytes 0x60 0x57 0x71 0x8 0x61 0x15 0x10 0x81)) 13 (by decide) (UInt64.ofBytes 0xff 0x73 0x35 0x50 0x5b 0xfd 0x80 0x0)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x56 0x72 0x25 0x61 0x16 0xff 0xff 0xff))

private def absorbed016 : Vector UInt64 25 :=
  #v[0x992cfa7993e96b75, 0xe2f22dc7252355bd, 0x8f416a7a3fee69f7, 0x947a187ce32b290a, 0x8c064fdfe1f031d1, 0xed3828d15cc17f06, 0x4dfb2c01b3bf1b92, 0x5808ff4e27cd8657, 0x44b828c178d38f71, 0xbd872a573745ea24, 0xf80dc483faca5734, 0x6aedc57c7e697d28, 0x87be78ada68146c0, 0xe61f80bb8ca2b650, 0x8aba0a86fcc3714b, 0x47de7fbfaa09e0d1, 0x6fd8abf5d8a80e91, 0x899b83d1f52e6298, 0xedec729eb78ec295, 0xeaaf8e419cf916a, 0xae34992b6da45fc, 0xd6fdc2ab044e4bb2, 0x4dd36298dcbce523, 0x68aca304a9d6d05a, 0x15cbab3ffe76c174]

private theorem words016 : absorb016 state016 = absorbed016 := by
  decide +kernel

private def quarter016_1 : Vector UInt64 25 :=
  #v[0x7ef8d67b3f8f3c91, 0x78ac98eacfa5a5d0, 0xb9d6ab854598fdc, 0xd281179abd52f7f2, 0x5566f1f111ffd4ca, 0x498366435476ab06, 0x65ab4c6d8b3fa1fe, 0xe8840ad9e92d6d6e, 0xa230dca69aa9ad71, 0x148bfb627f56d722, 0x1c01a66c54ffa2cc, 0x7ec944ce959c36d8, 0xf91f3419864780bb, 0x6d6103eb5b502340, 0xa0011ef849b276f9, 0xc4d2b26fa940b115, 0xa900e138b0cdcd43, 0x4433a860b99e1df5, 0x39f9ac537a6d9687, 0x2a8bff34521023af, 0x3f6c36c60874f62c, 0x32a8316dcacfd969, 0x6168c65405f1f4da, 0xecba19b0d90b7511, 0x1c04d35dc46b900b]

private theorem rounds016_0 : sixRounds 0 (by decide) absorbed016 = quarter016_1 := by
  decide +kernel

private def quarter016_2 : Vector UInt64 25 :=
  #v[0x4fb376857fce675b, 0xe1de0e721167660a, 0x47d2b3206cfe5209, 0x16d91e8471b0b7d0, 0x46e5fc86f4d5fcff, 0x45e3f66be52974c1, 0x142535a71bc1c091, 0x6dd81b3ff4739c3f, 0xb5ddc92a39e0be69, 0xd276d711fc9f1d1a, 0xd26e137acac1e04d, 0xd5afc1070f2eb770, 0x282014622ee6266f, 0x15ed7456d8d15d01, 0xadd7db588b219de1, 0x2452dc87d2875b1c, 0xf85f210f613bd36c, 0xa2ccb07f37407e4, 0x3d93d521caf4a084, 0xdbf7b756531b3ef8, 0x4b5f9879ddef414c, 0xc691ecd9172c086c, 0x16cc22c8f8326921, 0x10fb5f3d0e1a6b99, 0x1870398d8e826d01]

private theorem rounds016_1 : sixRounds 6 (by decide) quarter016_1 = quarter016_2 := by
  decide +kernel

private def quarter016_3 : Vector UInt64 25 :=
  #v[0x50f262740ff45be0, 0x4030e21a7693a74c, 0x7a1db3ce64101aa2, 0x5b15307066331a3c, 0xaae3a4e842b3d943, 0xc4516a0430e02d50, 0xdd0f9a534bef5903, 0x1e94954018f1aba9, 0x5f1063ca5f13d1d8, 0x89325b6ff07d6db5, 0xe6cfd2cd7f99d992, 0x95f9d8bf73aa8c4d, 0x3a1c6112de0c2f25, 0xda49c036d8b94dda, 0xdb5dd9eae351293b, 0x2a33b68243d86957, 0x830c254267f3748f, 0x6b71cb5a3ad7993a, 0xfe9f6dcdb124f65f, 0x9f1d6852259d140e, 0xe552c88d7825aa83, 0xf75e0aed8138760f, 0x683257eab7dd880d, 0xa8fecea52c7af6d0, 0x52d1441bc364e5c9]

private theorem rounds016_2 : sixRounds 12 (by decide) quarter016_2 = quarter016_3 := by
  decide +kernel

private theorem rounds016_3 : sixRounds 18 (by decide) quarter016_3 = state017 := by
  decide +kernel

private theorem perm016 : KECCAK.f1600 absorbed016 = state017 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds016_0, rounds016_1, rounds016_2, rounds016_3]
  rfl

theorem block016 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes016 ++ tail) state016 =
      KECCAK.Bytes.run 0 tail state017 := by
  exact run_block_of_step bytes016 tail absorb016 state016 absorbed016
    state017 (fun _ => rfl) words016 perm016

private def absorb017 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x36 0x80 0x4 0x60 0x52 0x4 0x61 0x5b)) 1 (by decide) (UInt64.ofBytes 0x8 0x61 0x15 0x10 0x81 0xa0 0x60 0x3)) 2 (by decide) (UInt64.ofBytes 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57 0xa4)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x16 0x35 0x81 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x60 0x90 0x35 0x1 0x81 0x20 0x60 0x90)) 7 (by decide) (UInt64.ofBytes 0x90 0x16 0x35 0x1 0x82 0x40 0x60 0xff)) 8 (by decide) (UInt64.ofBytes 0x80 0x60 0x90 0x35 0x1 0x81 0x60 0x60)) 9 (by decide) (UInt64.ofBytes 0x61 0x5b 0x56 0xd9 0x26 0x61 0x35 0x1)) 10 (by decide) (UInt64.ofBytes 0x61 0x5b 0x56 0x77 0x27 0x61 0xf1 0x3)) 11 (by decide) (UInt64.ofBytes 0x60 0x3 0x36 0x80 0x4 0x60 0xd 0x4)) 12 (by decide) (UInt64.ofBytes 0x57 0xfa 0x8 0x61 0x15 0x10 0x81 0x20)) 13 (by decide) (UInt64.ofBytes 0x73 0x35 0x50 0x5b 0xfd 0x80 0x0 0x60)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x98 0x27 0x61 0x16 0xff 0xff 0xff 0xff))

private def absorbed017 : Vector UInt64 25 :=
  #v[0xa49b9eeaabb582ca, 0xc902385935d3e119, 0x64a2b0ce504a9cce, 0x4b48bc917e664824, 0x6a84a40afa4baf50, 0x3e010d4ae5703e80, 0xc0c8dc30ae670772, 0xb65813f196ca0f38, 0xd0201b557f27e2d8, 0x5ba9f362b1f42a56, 0xfe38292a6562e848, 0x22ffcf6363b15624, 0x50ce2e2332f7b5d1, 0x8cd68ff4cd187821, 0xbd029ffe42ffe558, 0x1fce48dd98b2bca5, 0xd479442d48047563, 0x1c214ad13814a024, 0xe18e32a780ffefc7, 0x9388a3018d6da17e, 0x8581d467b313ba8, 0x59b93ca33989976f, 0x2bb3bc762ecf8a3e, 0x7e3a2e71c29b1b5e, 0xc6b68669f9c7515f]

private theorem words017 : absorb017 state017 = absorbed017 := by
  decide +kernel

private def quarter017_1 : Vector UInt64 25 :=
  #v[0x40f40bdd3aee309f, 0xda448b1425c1ef93, 0x86bee06c6af819fc, 0x77ab5befc48893cc, 0xeb372124a0c70cee, 0xe896d9bf597d58fb, 0x4602fc0ff6ce70b9, 0x7caee961bfe4dc27, 0x5266472b5d30679a, 0x26119dba670595ca, 0xf9c07a377d0d95e5, 0x39e79ba1df567fd9, 0xf9fe1869a97ba0fb, 0x723910725088801, 0x8447478aee7b896e, 0x384e6e51fdaf9d30, 0xf15596b59ef2d55d, 0xa1aaec25cc1c2145, 0xd34e2b9434232759, 0x7c884b6c6eb9ab62, 0xf9291b615cfc3458, 0x7990f1afbb615f95, 0xab89dd8caac77ced, 0x565e5c325a660dd7, 0xaf9758b7ac3f3517]

private theorem rounds017_0 : sixRounds 0 (by decide) absorbed017 = quarter017_1 := by
  decide +kernel

private def quarter017_2 : Vector UInt64 25 :=
  #v[0xa4597995c36dcce8, 0x5702d4688bc3a5e8, 0xc594adb0db8d162f, 0xe77e55a38ccf5690, 0x615e1946f4b23418, 0xa4fda7769fe9a856, 0xf072091972d29f84, 0x7cd80ee629ce54, 0x7c4753be4d67d0a5, 0x8245c2dfa55bf806, 0x4498e138a8b8bb0, 0x8e857616438f1749, 0x5dee30f1031ec3bd, 0xb411b26992ff26c4, 0xd2c02b082709b888, 0x9c4d23a635b105aa, 0x54dd8d9b6955b56e, 0x3be05eb556c26801, 0xfa6066e15c905e2c, 0xd458e388bb5d4a72, 0x29817f99058db2ed, 0x4001757e56391675, 0x851fdd8699cc6c53, 0xccd85647acf11d82, 0x22293bc70f3d3c19]

private theorem rounds017_1 : sixRounds 6 (by decide) quarter017_1 = quarter017_2 := by
  decide +kernel

private def quarter017_3 : Vector UInt64 25 :=
  #v[0xd30557dbfa37291d, 0x24cc24db2dc14fe6, 0x263f821d55df3b0d, 0xb2eeb845c7e0760d, 0x511aa7d40f8e9d33, 0x69ab3c3921124c84, 0xaac5ed77a4c8c3b9, 0xe39ac9df8ddbc15a, 0x7d029025cd0fc235, 0xc654203fc8593d13, 0xc17b3471e8a68773, 0xe43c68846b0ea568, 0x44eaf7de626b73da, 0xc888ad2f290cdead, 0xfb9d68a6bf59674a, 0x80228b7873d4e923, 0x1daeceeb018a7f82, 0x60f416985e11a5b1, 0xc9357e8f4758b2ec, 0x36ab8c9cc92e71d1, 0x3b1c8c68627ace93, 0x6f2fd6b2c546754d, 0x6f004c69f47af22b, 0x98be5949d5920175, 0x8e288262394baa90]

private theorem rounds017_2 : sixRounds 12 (by decide) quarter017_2 = quarter017_3 := by
  decide +kernel

private theorem rounds017_3 : sixRounds 18 (by decide) quarter017_3 = state018 := by
  decide +kernel

private theorem perm017 : KECCAK.f1600 absorbed017 = state018 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds017_0, rounds017_1, rounds017_2, rounds017_3]
  rfl

theorem block017 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes017 ++ tail) state017 =
      KECCAK.Bytes.run 0 tail state018 := by
  exact run_block_of_step bytes017 tail absorb017 state017 absorbed017
    state018 (fun _ => rfl) words017 perm017

end Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
