import Blanc.Lift.Usdc.ImplV1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb48 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xe8 0x18 0x61 0x50 0x55 0x90 0x17 0x2)) 1 (by decide) (UInt64.ofBytes 0x1 0x60 0x5b 0x56 0x47 0x2e 0x61 0x81)) 2 (by decide) (UInt64.ofBytes 0xa 0x0 0x1 0x61 0x14 0x60 0x8 0x60)) 3 (by decide) (UInt64.ofBytes 0x16 0x19 0x2 0xff 0x60 0x81 0x54 0x81)) 4 (by decide) (UInt64.ofBytes 0x55 0x90 0x17 0x2 0x15 0x15 0x83 0x90)) 5 (by decide) (UInt64.ofBytes 0x50 0x50 0x50 0x50 0x50 0x50 0x50 0x50)) 6 (by decide) (UInt64.ofBytes 0x90 0x0 0x60 0x8 0x60 0x5b 0x56 0x50)) 7 (by decide) (UInt64.ofBytes 0x4 0x90 0xa 0x0 0x1 0x61 0x90 0x54)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x56 0x81 0x16 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x90 0x54 0x90 0x0 0x60 0x1 0x60 0x5b)) 12 (by decide) (UInt64.ofBytes 0xff 0x73 0x4 0x90 0xa 0x0 0x1 0x61)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x16 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed48 : Vector UInt64 25 :=
  #v[0x3d62c180ec782124, 0xe8f28d84c76c9a2f, 0xd705c967207dba60, 0x829eedae32a3458e, 0x4f30fcd1d7ab0db9, 0x9ab3aebe776ff706, 0x872ea177fa4b00a, 0x7982aa8f4ef00712, 0xe02487d918247b4a, 0x84e90fc00c796b0f, 0x3366c35f06bd8fee, 0x382bdc18919a4dd7, 0xbc14072c4bac3075, 0xdb2a2b0b0bbf0543, 0x22d844e390e3b4b4, 0x7207454251aceb25, 0xb6f8b9fe6fa9b074, 0x68dd3dc1f331a0e5, 0x9eba3d5dcbf0e9a3, 0xdb7c93b6eb6073ca, 0xc8ea869aaf07111f, 0x79f600af3ee997d4, 0xb89bdd79f23f3f65, 0x92ebd72f7e4f10c8, 0x68441b4341836830]

private theorem words48 : absorb48 state48 = absorbed48 := by
  decide +kernel

private def quarter48_1 : Vector UInt64 25 :=
  #v[0x5f8795020e8a3bfc, 0x8c69c6f13ba5b143, 0x16ce39d3ae13dad7, 0x5070faf8616e6214, 0x97d1b605858e0e7c, 0xcf5c261760f00915, 0xaad357ad17fe5778, 0x6d0c430f0ab15772, 0x716ac0c214bafa1, 0x4d0b5e4e81360145, 0x63d91176f7e2e613, 0x51d730349569dd87, 0x2a9c815b3c0fad6e, 0x750f9ab952dccb3b, 0xf73485851633e749, 0xd4ecd1c2948f2bea, 0x483e7e422b51ec8c, 0xc88f762ef217a930, 0x6c61f717056d5d4, 0x3d29855d6c3f5e4e, 0x89b7e2f1864659f5, 0x1fad6d5e6c5e6a1c, 0xeee0a63c3f416807, 0x8616a7ad552268d5, 0x86427bf417695c79]

private theorem rounds48_0 : sixRounds 0 (by decide) absorbed48 = quarter48_1 := by
  decide +kernel

private def quarter48_2 : Vector UInt64 25 :=
  #v[0x87fba7f62c2aa4f3, 0x9cfe4a59d581d973, 0xe1763bd88e500c8f, 0xafe6d87ac660ff35, 0xac9fd2cfb67a8153, 0x3e78c7a57342092, 0x72fed403ce675d83, 0x1a4b07bfc4e9a546, 0xd3a99177bc843a42, 0x5fe61ef77c573acf, 0x5c43219d14d692f5, 0x772e7b7ccb23ef68, 0x63399ca6b2fa5f8a, 0x5137035d9e2c5f4f, 0x7872e2e64fe670f7, 0x6a45f76d05546909, 0x47c6970b03449daa, 0x8a17727704420e59, 0x6ee3d85006a6330e, 0xcdf822b0c990c9b6, 0xb5fe5453a557a745, 0x5e882b79473e128e, 0x6212eddbc2739c12, 0x123439eae209f15b, 0x59dd2bfd3a28360c]

private theorem rounds48_1 : sixRounds 6 (by decide) quarter48_1 = quarter48_2 := by
  decide +kernel

private def quarter48_3 : Vector UInt64 25 :=
  #v[0xb7de6ba871e6e15, 0xa84f0c633bb9942a, 0xcb0294c53b9cea66, 0xf462172ccc8276c1, 0xa9ddf5ec51648165, 0xb90c19d829935542, 0xc832bf2a083b0e04, 0x6dbd64b0481525bc, 0x70306753eca8c89d, 0x4c127e9aff104ec, 0x89e365130c5a803a, 0xba86705b9d3d11f4, 0x1e9e92e664426d51, 0xe9502911132cdd8e, 0x2dc2e2a5b776c86d, 0x9837bf668a7152ce, 0x4eebb4412f1ea47f, 0xa0ea3baf75344e17, 0x28d182e358e73120, 0x606cf6ca2b8fc996, 0x8b6b0f32ae2f3acc, 0x484eef30c7323c60, 0x35c743e694a9b1d, 0x63218ca0af5df088, 0x3a4f893478522118]

private theorem rounds48_2 : sixRounds 12 (by decide) quarter48_2 = quarter48_3 := by
  decide +kernel

private theorem rounds48_3 : sixRounds 18 (by decide) quarter48_3 = state49 := by
  decide +kernel

private theorem perm48 : KECCAK.f1600 absorbed48 = state49 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds48_0, rounds48_1, rounds48_2, rounds48_3]
  rfl

theorem block48 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes48 ++ tail) state48 =
      KECCAK.Bytes.run 0 tail state49 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes48 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb48 ws)) := by
    rfl
  exact (step state48).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words48).trans perm48))

private def absorb49 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x33 0x16 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x57 0x8f 0x19 0x61 0x15 0x15 0x14 0x16)) 5 (by decide) (UInt64.ofBytes 0x60 0x0 0x60 0x5b 0xfd 0x80 0x0 0x60)) 6 (by decide) (UInt64.ofBytes 0x81 0xa 0x0 0x1 0x61 0x14 0x60 0x1)) 7 (by decide) (UInt64.ofBytes 0x90 0x16 0x19 0x2 0xff 0x60 0x81 0x54)) 8 (by decide) (UInt64.ofBytes 0x50 0x55 0x90 0x17 0x2 0x15 0x15 0x83)) 9 (by decide) (UInt64.ofBytes 0x2f 0x9e 0x68 0x2f 0x86 0x5 0x78 0x7f)) 10 (by decide) (UInt64.ofBytes 0xad 0x82 0xf4 0x2f 0x6 0x9f 0xdf 0x13)) 11 (by decide) (UInt64.ofBytes 0x79 0x84 0xe0 0xa9 0xac 0x12 0xd1 0x3a)) 12 (by decide) (UInt64.ofBytes 0x5b 0x52 0x8c 0x15 0x2e 0x83 0xed 0x11)) 13 (by decide) (UInt64.ofBytes 0x80 0x51 0x40 0x60 0x51 0x40 0x60 0x33)) 14 (by decide) (UInt64.ofBytes 0x0 0x60 0x5b 0x56 0xa1 0x90 0x3 0x91)) 15 (by decide) (UInt64.ofBytes 0x90 0x54 0x90 0x14 0x60 0x1 0x60 0x80)) 16 (by decide) (UInt64.ofBytes 0xff 0x60 0x4 0x90 0xa 0x0 0x1 0x61))

private def absorbed49 : Vector UInt64 25 :=
  #v[0x5b2d3f4325cb02ce, 0xaeb008a44349c76c, 0xbe2342be64fc8506, 0x7a77006e89947dca, 0xca3d50b2831ec11d, 0xa2559482daa8e950, 0xc1f35bc7848448f3, 0x477b4b34013c0046, 0xba11275883c98466, 0x5e46caca57d88ae7, 0xc15f5ba21bd26a06, 0xfe24b979836821ab, 0x24b2ecdd5fee98a1, 0x689f329d700502e2, 0xda77cc3ac74b2cbf, 0x44453d8afc0fa812, 0xebf282d11e0ca17a, 0xe972c3cb111a7940, 0xa5bdbbe8562229f6, 0xdc20299b004bed5e, 0x7fadec9269e37a4d, 0xaee8138ef3263838, 0x6c4e06d7f092138f, 0x91588e14d2577741, 0x822015ae2746ef63]

private theorem words49 : absorb49 state49 = absorbed49 := by
  decide +kernel

private def quarter49_1 : Vector UInt64 25 :=
  #v[0x6d140049f0fd7cd8, 0xf8b0677e4f5ecda9, 0xf2648e9c67829cea, 0xb97ae5999f38d321, 0xa0e0568438d243aa, 0xbfdef5e4b5af69c5, 0xfa560220806ca8c5, 0x681bb75aecea0b95, 0x17ef50c8bcf9b08c, 0x70fa9dbc5167a6b2, 0x93f1fedd0aa8652c, 0xc3cebd32c643a2d, 0x21f208913b374b08, 0x618be4661e675348, 0xba1d2b350341d1c7, 0x14e7fc7643b99da, 0x21140a7a4f72a5be, 0x2310b20244f591b2, 0x46f5f8302cd435b6, 0x2e4c20def31d28df, 0x382eefb0f7e79c5e, 0x8b9ebf59d65ae891, 0x6418762d99be581, 0xaa7bff34b13adddf, 0x426615b8eee8f147]

private theorem rounds49_0 : sixRounds 0 (by decide) absorbed49 = quarter49_1 := by
  decide +kernel

private def quarter49_2 : Vector UInt64 25 :=
  #v[0x36c693685f8195f0, 0xd536dc6307787270, 0x947d2ba7aecad136, 0x5cce89dcfcdfbd6e, 0x8552dbfa667fd24d, 0xd1f55c63752ab7a7, 0xcd67a31e6be78d9d, 0x96f0055bd7b9f65, 0xfd7f40f0328d1c93, 0x785c2d36bd6252de, 0x70770489f73e76d6, 0x95a6b5042c8ac1cd, 0x6114ea4a58160fe2, 0x183559577cc8d7b7, 0x683282a8530f9015, 0xb1375b719f099619, 0xc585b60b8b1cb48, 0xf6b2b50bde760944, 0x9798be82aa6178ff, 0x4b6bd01f96f40e2d, 0x9fa38a7194cfa99d, 0xe6c2b09f822e645d, 0x50b75922a59b1ce4, 0x5b56fce5fa0a51a1, 0xb94d2ccffa5bfd0f]

private theorem rounds49_1 : sixRounds 6 (by decide) quarter49_1 = quarter49_2 := by
  decide +kernel

private def quarter49_3 : Vector UInt64 25 :=
  #v[0x1003cd6030b6de31, 0x4f02bff65f63d404, 0x72c904985080ae7f, 0x400e6fa233612bf9, 0x33d066ac1cac70a4, 0x4bda46d9ab1f5fbd, 0xe06a873dfc905a69, 0x3bcd16a87fed6537, 0xb9a6ad0e924baa5e, 0x22ff42d3c8b2d50f, 0x4873e91502bbda07, 0x1a32df13db5d137c, 0xb07c2edc575c33b, 0x333daa1b73ae2be6, 0xc4d9e987f53ded54, 0x4525dee421744c3a, 0xe6627b7edc5227b8, 0x1956f87a714c26f6, 0xaa8b273a8f7b8b3c, 0x60034660165c090, 0xd007e15c6136ac17, 0x4f00380714f75bfa, 0xa72b0e92dc30b291, 0x88a2305ce784c7a3, 0x908cb30885febfb7]

private theorem rounds49_2 : sixRounds 12 (by decide) quarter49_2 = quarter49_3 := by
  decide +kernel

private theorem rounds49_3 : sixRounds 18 (by decide) quarter49_3 = state50 := by
  decide +kernel

private theorem perm49 : KECCAK.f1600 absorbed49 = state50 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds49_0, rounds49_1, rounds49_2, rounds49_3]
  rfl

theorem block49 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes49 ++ tail) state49 =
      KECCAK.Bytes.run 0 tail state50 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes49 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb49 ws)) := by
    rfl
  exact (step state49).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words49).trans perm49))

private def absorb50 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x57 0xf7 0x19 0x61 0x15 0x15 0x15 0x16)) 1 (by decide) (UInt64.ofBytes 0x15 0x1 0x60 0x5b 0xfd 0x80 0x0 0x60)) 2 (by decide) (UInt64.ofBytes 0xff 0x73 0x33 0x0 0x60 0xc 0x60 0x15)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x16 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x90 0x1 0x20 0x60 0x52 0x81 0x16 0xff)) 9 (by decide) (UInt64.ofBytes 0x20 0x0 0x60 0x1 0x20 0x60 0x52 0x81)) 10 (by decide) (UInt64.ofBytes 0x0 0x1 0x61 0x90 0x54 0x90 0x0 0x60)) 11 (by decide) (UInt64.ofBytes 0x15 0x15 0x16 0xff 0x60 0x4 0x90 0xa)) 12 (by decide) (UInt64.ofBytes 0x60 0x57 0x56 0x1a 0x61 0x15 0x15 0x14)) 13 (by decide) (UInt64.ofBytes 0x15 0x0 0x60 0x33 0x5b 0xfd 0x80 0x0)) 14 (by decide) (UInt64.ofBytes 0xff 0x73 0x83 0x0 0x60 0x3 0x60 0x15)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed50 : Vector UInt64 25 :=
  #v[0x4762aab8dfcffd0a, 0x5f924390bdd11f15, 0xbea1fb36403fd5b2, 0xb38b6ef936d78234, 0x592ef12d5069380e, 0xcc7dc3ca8568a2f, 0x1f362e12bca53e14, 0x1d1f0a7fcbd8d80e, 0xbd96e73241901cc8, 0x4fec675680638844, 0x8a93ba50f1069406, 0xdc13d3eb232bb342, 0xb627bb41de6e1c5e, 0x1d57c8e3c40ad4e1, 0x46dbdf095b6b3d21, 0x9d3a4164180e35f6, 0xd828ea844daf5af7, 0x458b00f960bb3fc2, 0x13758cc4e5d0df76, 0x324757057e8b558a, 0x2f553dd42a550f7c, 0x1cf74e0a646d5a2a, 0xe07c96df0e17ef2, 0x2ed153e764867a71, 0x5e5c759da3c1d46a]

private theorem words50 : absorb50 state50 = absorbed50 := by
  decide +kernel

private def quarter50_1 : Vector UInt64 25 :=
  #v[0xaee41e03972bc3c5, 0xe26e75c85bbf10d6, 0x7248f4eeab8a6bbb, 0x8bb7dffffeda2a05, 0x36910c03471a8b0d, 0x12a9c9110628973d, 0x73c53a72a96af10e, 0x7cc7682749f18381, 0x920e99075af68f1b, 0xd398920d9c7b9a69, 0x55aad5ec80ed5af8, 0xe673eefe31645a26, 0x3334ddd7af48ef18, 0x30551713d1cc0dd5, 0x42c98920ad1a52a2, 0x921135d66cdfb73d, 0xce49945813a98f62, 0xba5c95bf3505cb33, 0xf81596437b516e1a, 0x95867fb722ee9cca, 0x88a8620af05b4169, 0x2da87b128d5b6791, 0xf11f7e41d208c432, 0x3fd0b0ac150eb307, 0x40992b41a9662ab8]

private theorem rounds50_0 : sixRounds 0 (by decide) absorbed50 = quarter50_1 := by
  decide +kernel

private def quarter50_2 : Vector UInt64 25 :=
  #v[0xc374e1e863054549, 0xe15462660fbc0639, 0x9fc6355b33d17a34, 0x966f5fae0d62a6a3, 0x59d5a2934ad63d5, 0xaec5c07f2bc10219, 0xb3fe24d11bf3f47, 0x59791952f19a38ab, 0xe0381d6c05abff09, 0x9f4ab0324c2739c5, 0xae05eb9351fd3e9c, 0x73057065ff2bcd25, 0x469832d6d5e63770, 0xdc111e40b57fbc52, 0x3535c40ac42b083e, 0x3c1789e078a8d936, 0xc7a6cd1797e9874d, 0x7dc83cf88b8dee3d, 0x2e8dccf82d2639e3, 0x7caf121345fe732f, 0xcb4994f477ec5f06, 0x950208496baa5176, 0x3b8682666c6a091e, 0x1879fad0181d73e2, 0xdf4755c4b7068de5]

private theorem rounds50_1 : sixRounds 6 (by decide) quarter50_1 = quarter50_2 := by
  decide +kernel

private def quarter50_3 : Vector UInt64 25 :=
  #v[0x9fb9299fa459f20e, 0x168b83e03fd5b88e, 0xd01edd5c31b3854c, 0xacbfa56ad6e55043, 0xf10605eb9ec2dd45, 0x81df9c82465711d0, 0x9b9e5f11ac55d124, 0xc5762f054204e87c, 0xd06e90b11667aac6, 0xcd909d9d124ad3d0, 0xb7ed45282ad2e1a1, 0x7f6f437f56fcaa23, 0x5e07db8526eeb754, 0x122e15604211965f, 0xa830609dbcf1c53a, 0x2d1bfb26cee24b8, 0x9ce708a142b0c8bb, 0xacb3dce0816b19ec, 0x1f8911f6eba5c73a, 0x635ce55f03d99e9b, 0x9204d0680e53915d, 0xbd573e27fb7e2c84, 0x58ea3870e7d1b4f0, 0xfe4f9dbed2ee0d4e, 0xd3175cc79c5ec8f3]

private theorem rounds50_2 : sixRounds 12 (by decide) quarter50_2 = quarter50_3 := by
  decide +kernel

private theorem rounds50_3 : sixRounds 18 (by decide) quarter50_3 = state51 := by
  decide +kernel

private theorem perm50 : KECCAK.f1600 absorbed50 = state51 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds50_0, rounds50_1, rounds50_2, rounds50_3]
  rfl

theorem block50 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes50 ++ tail) state50 =
      KECCAK.Bytes.run 0 tail state51 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes50 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb50 ws)) := by
    rfl
  exact (step state50).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words50).trans perm50))

private def absorb51 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x16 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x90 0x1 0x20 0x60 0x52 0x81 0x16 0xff)) 4 (by decide) (UInt64.ofBytes 0x20 0x0 0x60 0x1 0x20 0x60 0x52 0x81)) 5 (by decide) (UInt64.ofBytes 0x0 0x1 0x61 0x90 0x54 0x90 0x0 0x60)) 6 (by decide) (UInt64.ofBytes 0x15 0x15 0x16 0xff 0x60 0x4 0x90 0xa)) 7 (by decide) (UInt64.ofBytes 0x60 0x57 0xb6 0x1a 0x61 0x15 0x15 0x14)) 8 (by decide) (UInt64.ofBytes 0x15 0x0 0x60 0x84 0x5b 0xfd 0x80 0x0)) 9 (by decide) (UInt64.ofBytes 0xff 0x73 0x83 0x0 0x60 0x3 0x60 0x15)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x16 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x90 0x1 0x20 0x60 0x52 0x81 0x16 0xff)) 16 (by decide) (UInt64.ofBytes 0x20 0x0 0x60 0x1 0x20 0x60 0x52 0x81))

private def absorbed51 : Vector UInt64 25 :=
  #v[0x7a1c138424a809fc, 0x5de0f8a51774fa1e, 0x311df0dc3a1f7f95, 0xc3470dfeb340b35, 0x215dc8c2f0744dab, 0x6d171edf10e3a47b, 0x26b6e06902044987, 0xb7fc3d9f76971431, 0x62f28dfb400cb1c, 0xb374a128bdf0c67b, 0xaaf2edcfe7335a43, 0x5d69853d48d6598, 0x2668c2b71cfde775, 0x5b4246a22bd5f80b, 0x5d66683a9e5acb30, 0xdd0732d2f65091d8, 0xc7bdfd6d24f25f9a, 0x924e02f0ffc9dd6, 0xcc7dec55d1380efd, 0xa95aad700423b2f4, 0xb2becb183c7b16d4, 0x6f9f3b393dbee0ef, 0xd5e60cf0132293cf, 0xd7617634cba014c4, 0xae5da494dc66eee5]

private theorem words51 : absorb51 state51 = absorbed51 := by
  decide +kernel

private def quarter51_1 : Vector UInt64 25 :=
  #v[0xe5d94a4b383c9ed1, 0xa1c152a32a78d060, 0xc7daf353a3edf1b1, 0x412f3a47ddceed80, 0x1b429203cedf202c, 0x52aeab5b37f24207, 0xef648be127bcc299, 0x281788de80ee593c, 0x4cdc2232ac03e5a3, 0x6d6c8d7b51881b30, 0xd5a11979b867b206, 0x4c70a9e83ea675d3, 0x8b33f8d0ab189054, 0x17903797044d1b29, 0x69693952c3a92292, 0x49aff51773786f6c, 0x2f20b99b304fdb02, 0xf7e514d730038d31, 0x7f9ec5fa94f5dac0, 0x4fe99bca021ff458, 0x932af1daa813681d, 0xf28f7634e419f63b, 0xf8163bc333c260d9, 0xfb43cc1403b2f641, 0x4df8bfb0d64c93b1]

private theorem rounds51_0 : sixRounds 0 (by decide) absorbed51 = quarter51_1 := by
  decide +kernel

private def quarter51_2 : Vector UInt64 25 :=
  #v[0xc1d57e3f98975266, 0xb78d6ec69e9c3ac, 0x4b8f1408d8613c59, 0x5765fc5809593e01, 0x8bb0cf1a078926f6, 0x7bb4c182803853c8, 0x1ae4a74985635fe, 0xd8307ffbe3c5ff13, 0xf4c49c3c83048d1, 0x66fd1fdecaa27079, 0x9d9cdf48f63ecf01, 0x2f7391780062f256, 0x6cae337c8eed8c9, 0xb1049ce2343d7850, 0x568ae9869695aeec, 0x1c22075566b8d33c, 0xe8fe51ef14460ec0, 0xb1e7035812c277e, 0x48c363cf2fc8a662, 0xd30b1c7c39a0d754, 0xfb59e4bb08428485, 0x453e257e057dca69, 0xb80eca045ba2f01b, 0xbe04c3573bfb0c26, 0x99c12a0f3a9443d6]

private theorem rounds51_1 : sixRounds 6 (by decide) quarter51_1 = quarter51_2 := by
  decide +kernel

private def quarter51_3 : Vector UInt64 25 :=
  #v[0x1751f5b379a1928b, 0xba2868ce3c9ed5b0, 0x8bb3496839cdfc04, 0x14d6fbc2464d9ccf, 0xbe0684da006062f, 0xf8d6d69469474a78, 0x2e14c5a2dfd67c67, 0xc1c4b645263683e4, 0xbb2170cbf254304a, 0xf01fea64f17dd1fb, 0xfd0601715aee22ef, 0x8ebaf60fca1b06c9, 0x1f90499e70dc3dd7, 0x7736522da788fbab, 0x163b6e528620cb83, 0x94f04418896b8beb, 0x1e4658bcca6cdd97, 0xc3fe4f15446e9c7c, 0xe48c04693da7107c, 0xe5b2334f9809bc6f, 0x87f272f24304d3f7, 0x5b037fbb6791703, 0xdf036406766e5316, 0x667de51e06c6a1de, 0x3aa0bb29c5bfdc1]

private theorem rounds51_2 : sixRounds 12 (by decide) quarter51_2 = quarter51_3 := by
  decide +kernel

private theorem rounds51_3 : sixRounds 18 (by decide) quarter51_3 = state52 := by
  decide +kernel

private theorem perm51 : KECCAK.f1600 absorbed51 = state52 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds51_0, rounds51_1, rounds51_2, rounds51_3]
  rfl

theorem block51 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes51 ++ tail) state51 =
      KECCAK.Bytes.run 0 tail state52 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes51 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb51 ws)) := by
    rfl
  exact (step state51).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words51).trans perm51))

private def absorb52 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x1 0x61 0x90 0x54 0x90 0x0 0x60)) 1 (by decide) (UInt64.ofBytes 0x15 0x15 0x16 0xff 0x60 0x4 0x90 0xa)) 2 (by decide) (UInt64.ofBytes 0x60 0x57 0x16 0x1b 0x61 0x15 0x15 0x14)) 3 (by decide) (UInt64.ofBytes 0xff 0x73 0x0 0x60 0x5b 0xfd 0x80 0x0)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x86 0x16 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x61 0x15 0x15 0x15 0x14 0x16 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x80 0x0 0x60 0x57 0x52 0x1b)) 11 (by decide) (UInt64.ofBytes 0x1b 0x61 0x15 0x15 0x11 0x85 0x0 0x60)) 12 (by decide) (UInt64.ofBytes 0x60 0x5b 0xfd 0x80 0x0 0x60 0x57 0x61)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x33 0x0 0x60 0xd)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x16 0xff))

private def absorbed52 : Vector UInt64 25 :=
  #v[0xe629ec2415f58096, 0xdd1d708d87c750ae, 0xa8edcdcb8a10f046, 0xcb556d48515cf11e, 0x8edfb33d4476dc8b, 0x1830902e5007d6a4, 0xb03f2d8ea473ad2f, 0x35612d7c28349510, 0x1eab72214cf3c12a, 0x479ef5dba0fb560e, 0x491dcd1977d7abee, 0xfb5857bb637a5b9f, 0x529e960d2eb64d4a, 0xf07f01f391cc831f, 0xdae2298f7079d926, 0xf8cde9dc8d37f997, 0x82b828982b475ded, 0xda16fbc15ddccef0, 0xb6c09ae051333f40, 0xdf8068196aeda630, 0x68ae2965c3f7745e, 0x378a3b42fd15f9b5, 0x193ccc38da2384ca, 0xc36f27f8d88ec09e, 0x613abbc293ef6ec1]

private theorem words52 : absorb52 state52 = absorbed52 := by
  decide +kernel

private def quarter52_1 : Vector UInt64 25 :=
  #v[0x7e4ad0bd658fba09, 0xb18088a5faa61a2a, 0x5950e0f6c035298e, 0x71a67121e9a8fb9b, 0x6bc1ab7dc9d5944a, 0xba5d4a40cee218d4, 0x256f1e2b9a51d7b2, 0xf1fa5ea671e93243, 0xb2df53c107452b99, 0xd74290620c33aa5, 0x64c0f07a333d95f3, 0x86f603d59cb74009, 0x227f1355cb92688e, 0x94413cb9546c6ba0, 0xb9e8050099e98bc4, 0x9aded1c2b173dbfd, 0x69309ef4c30ba488, 0xde3128b63b180142, 0xee1205fba11f07e2, 0xb8eac7080f7e8741, 0xadf8008e7271e37f, 0x5a97f9e5dc95edf4, 0x41336e83a42a0ed1, 0xe287b44b9973089, 0xbaaefa0c2be28092]

private theorem rounds52_0 : sixRounds 0 (by decide) absorbed52 = quarter52_1 := by
  decide +kernel

private def quarter52_2 : Vector UInt64 25 :=
  #v[0x7e600f92b26cdea7, 0xe0e529777823b3f0, 0x141407a74afaf6b6, 0x29e1ccca7e8896bc, 0x83cdba92ed10b103, 0xbf880b62deb50ff, 0x8f655d35cc173bf0, 0x414a27cc4371ac59, 0xc3c5a494d52ebcd2, 0xbc79f16f210c262e, 0x2c2b8d8379cedaf, 0xac3ddac140bed0eb, 0xb04cb732a0b33ad7, 0x48e4485a1c82c98e, 0x90359857e824f6a1, 0x7a27dd82e6075f83, 0xcd2323df79667bb3, 0x82f8df956e6b5c90, 0x48cc40dd9aead57b, 0x4a79975b28e32b92, 0x1d803e8744989abe, 0x2d40d7dbc03a6658, 0x3ebe508d5f3174bc, 0x9db08d8415673a73, 0xaa9bdb092c08d5c2]

private theorem rounds52_1 : sixRounds 6 (by decide) quarter52_1 = quarter52_2 := by
  decide +kernel

private def quarter52_3 : Vector UInt64 25 :=
  #v[0xcd97b0132bbeebef, 0xd4fec551f9e9ccdc, 0xe2459a79bd22f6a4, 0x448496989de3994c, 0xeee0d0f3677db04e, 0x9160283d31f52cfa, 0xe17d4fabebf5f8c6, 0xfb72198cf2fc302a, 0x674f2f6a546fa709, 0x4a4ef346701214cc, 0x57b2666ea34e2106, 0x174db9fc06baad0c, 0x3c6e565167dd98fb, 0x13413c7c327409a3, 0xb101cb26974aaf, 0xb7b46a3a8b85e286, 0xecbc7869ac2eb49f, 0x1e4c4e26262d8a6d, 0x95e73da5fb5efee2, 0x1c619d38c6c8539b, 0x35f4f9a1a8b5b2e9, 0xc952df14e70ff191, 0xaed69478db201bdf, 0x9de402b4cc28e37b, 0x89a3cc70b1df45eb]

private theorem rounds52_2 : sixRounds 12 (by decide) quarter52_2 = quarter52_3 := by
  decide +kernel

private theorem rounds52_3 : sixRounds 18 (by decide) quarter52_3 = state53 := by
  decide +kernel

private theorem perm52 : KECCAK.f1600 absorbed52 = state53 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds52_0, rounds52_1, rounds52_2, rounds52_3]
  rfl

theorem block52 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes52 ++ tail) state52 =
      KECCAK.Bytes.run 0 tail state53 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes52 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb52 ws)) := by
    rfl
  exact (step state52).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words52).trans perm52))

private def absorb53 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x52 0x81 0x90 0x1 0x20 0x60 0x52 0x81)) 3 (by decide) (UInt64.ofBytes 0x92 0x54 0x20 0x0 0x60 0x1 0x20 0x60)) 4 (by decide) (UInt64.ofBytes 0x61 0x15 0x15 0x15 0x11 0x85 0x82 0x50)) 5 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x80 0x0 0x60 0x57 0xb2 0x1b)) 6 (by decide) (UInt64.ofBytes 0x61 0x54 0xb 0x60 0x85 0xc7 0x1b 0x61)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0x63 0x90 0x91 0x90 0x2b 0x2e)) 8 (by decide) (UInt64.ofBytes 0x81 0xb 0x60 0x5b 0x56 0x16 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x60 0x85 0x1f 0x1c 0x61 0x50 0x55 0x90)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x89 0x0 0x60 0x9)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x16 0xff)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x52 0x81 0x90 0x1 0x20 0x60 0x52 0x81))

private def absorbed53 : Vector UInt64 25 :=
  #v[0xc8ff562b75e22b28, 0x91a9a41f52ce49c1, 0xc4d15ff7848375dd, 0x693240c6bc9c89b0, 0x29d1673c4b5d9ebc, 0x37db2dc856bd4a42, 0x31ab15aab43b0927, 0x47569e64774f0073, 0x38a5a3d853b6ce79, 0x1cb614f3d787f14a, 0xb9d2977d7ed6e62e, 0x420cf7038c7df159, 0x87abd768442d63a1, 0x30618fa41bf0e276, 0x99e512f6fad763b0, 0x22666b3d4839cc87, 0x3917dec7f4e0ce57, 0xad74cb59e0e7c0f3, 0xc697b90e105c07b5, 0xcc62bdf2c426e126, 0xc737a5286625472a, 0x57dedc389ddbb0cd, 0xa1a8b5028f13963d, 0xfb8d89de33701220, 0x705aa9ed772f51f4]

private theorem words53 : absorb53 state53 = absorbed53 := by
  decide +kernel

private def quarter53_1 : Vector UInt64 25 :=
  #v[0xcf10b4327215df3d, 0xd6f2ed86d6ac4d1b, 0x54a8aae5f866da5b, 0xf9f416656bb2e500, 0x7270d15aaa1d45b8, 0x29e507c03efb75ad, 0xf3ca5d5dabeb22ab, 0xcd4bb193ef009b2a, 0xa4719dca905e9dfe, 0x7ad0265df32aeb67, 0x15a0598eb74379ee, 0xa53137a8bc87bb89, 0x7553c44ea1a098a2, 0x426e756db1e7614b, 0x28456e26f545b022, 0x581f71ff4f367a84, 0x5c18171e02a106f5, 0x83f33c187849dbda, 0x5490552689adc84f, 0x42531f2200b14818, 0xab62025184cbbaef, 0x38c3e8243e540d0e, 0xebc48256dae4fa2d, 0xb52967dfb830ce70, 0xc132e0731cb1fdb]

private theorem rounds53_0 : sixRounds 0 (by decide) absorbed53 = quarter53_1 := by
  decide +kernel

private def quarter53_2 : Vector UInt64 25 :=
  #v[0x90814b193db62d15, 0xa52b3a65ed7d4808, 0x6f282866bb9697d1, 0xc880e68280505039, 0xb617c89138963b4c, 0x7d797f6ffed79bea, 0xb3eb6f9187a80a46, 0xa746eed1cc77d52f, 0x833f7209e3817202, 0xde19adcd52d83e29, 0x436327d8223cf45d, 0x14c705daf8e723fa, 0x664f8d90530e09f5, 0x8c4342a7bf053513, 0xa01000be2e401e71, 0xcdc93014dba894be, 0x165b4c63d4f765ab, 0x1faefd29160cebfa, 0x8f743a4c1cbf892b, 0xf85ad1e60826e8bd, 0xfaf9c4a3366588c4, 0x8f6620122495ae02, 0x4650118bb3465ce2, 0x7f9a009c2d7330a1, 0x754b937daf1af53c]

private theorem rounds53_1 : sixRounds 6 (by decide) quarter53_1 = quarter53_2 := by
  decide +kernel

private def quarter53_3 : Vector UInt64 25 :=
  #v[0xc016df9d1cc0b28d, 0x2059d1892094cfbf, 0xdbb152a2154f1eff, 0x6c2169451ef0ec4, 0x6de328852e84470e, 0xb4ffa09df75b2e25, 0xceda5142b2644b83, 0x82db652d49f52a05, 0xf2c78593894cf4cc, 0x83c26d0b97e05b06, 0x760af18ef7211e01, 0x39109dd2e1f12, 0x9699aa1173cf2dc1, 0x5fdb48daac3dd4c4, 0x97d65464f05b0202, 0xcda0078890328e00, 0xc52112964001504c, 0xcd57ecacc947a698, 0x4cd642be64f4af4f, 0x530b12ba7b3ed5d4, 0x14c7f3a859d83c96, 0x64f24cccb77106aa, 0x1c48e395909571b1, 0xd881ad7e04e74063, 0x197e77c6e06e5da1]

private theorem rounds53_2 : sixRounds 12 (by decide) quarter53_2 = quarter53_3 := by
  decide +kernel

private theorem rounds53_3 : sixRounds 18 (by decide) quarter53_3 = state54 := by
  decide +kernel

private theorem perm53 : KECCAK.f1600 absorbed53 = state54 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds53_0, rounds53_1, rounds53_2, rounds53_3]
  rfl

theorem block53 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes53 ++ tail) state53 =
      KECCAK.Bytes.run 0 tail state54 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes53 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb53 ws)) := by
    rfl
  exact (step state53).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words53).trans perm53))

end Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
