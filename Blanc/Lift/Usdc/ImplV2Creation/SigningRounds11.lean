import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb066 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x80 0x80 0x1 0x4 0x60 0x52 0x81 0x0)) 3 (by decide) (UInt64.ofBytes 0x52 0x82 0x3 0x81 0x82 0x1 0x20 0x60)) 4 (by decide) (UInt64.ofBytes 0x80 0x1 0x20 0x60 0x52 0x81 0x25 0x60)) 5 (by decide) (UInt64.ofBytes 0x60 0x39 0x91 0x25 0x60 0xc5 0x59 0x61)) 6 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x50 0x50 0x91 0x1 0x40)) 7 (by decide) (UInt64.ofBytes 0x60 0x33 0x5b 0xfd 0x90 0x3 0x91 0x80)) 8 (by decide) (UInt64.ofBytes 0x20 0x60 0x9 0x60 0x52 0x81 0x90 0x0)) 9 (by decide) (UInt64.ofBytes 0x61 0x82 0x54 0x20 0x90 0x40 0x60 0x52)) 10 (by decide) (UInt64.ofBytes 0x8 0x7f 0x51 0x40 0x60 0x57 0x39 0x23)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x81 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x20 0x60 0x80 0x80 0x1 0x4 0x60 0x52)) 16 (by decide) (UInt64.ofBytes 0x29 0x60 0x52 0x82 0x3 0x81 0x82 0x1))

private def absorbed066 : Vector UInt64 25 :=
  #v[0x895ca5522c246d8c, 0xad308ca2d9392064, 0x7fac6f9e7678afd1, 0x7f7add39380f38a4, 0xfba3b7087ccc02cf, 0x3cc3d6343ef7f5e4, 0xe7f5856111533036, 0xd526a94194c2ecf7, 0x39fe06392356d5ed, 0xdaf55dc024930634, 0x378486e87b22f821, 0x1da3ff171133581b, 0xb03193750aaa5a24, 0xe8d07ac56e2140b7, 0xc39feb0a2b6f15b5, 0x3833cb5b5f9a4ae7, 0xcc09e11b9cb34dd0, 0x9d6f638ed4fda7a6, 0x7f32bedc1a7f35c9, 0xab018fc0c6fcd0d1, 0x1ba2cbf99fce094e, 0x90f41132b233fc75, 0xaa50acb97a451e2a, 0x5903e53d92c52f26, 0x38d850cf3007e4c1]

private theorem words066 : absorb066 state066 = absorbed066 := by
  decide +kernel

private def quarter066_1 : Vector UInt64 25 :=
  #v[0xca5f0702eb9842bb, 0x170b47d4b4b2c729, 0x683aaca62e9fea34, 0x4ba563529d246159, 0x2ed2940d43f867e7, 0x18f306a1bbd625c9, 0xf681b0649dbb8886, 0x6acbe5ec477bac97, 0x6d2a6fb6283edafe, 0x466389f40e93c9de, 0x6cf2867cc988c4f5, 0x48810e84a3ca5077, 0x2e36070767aa85c4, 0xb249d248bb49cace, 0x1c4c79c50f6b0800, 0x7597f9f3af8332a3, 0x52b3e273cbdb5484, 0x75b3a7f36a1ea949, 0xb05be718214a25f3, 0xe4178bbf8411b5c7, 0xcc0b19cf99fa4e9b, 0xa4767db79a50886c, 0x895aea55adb48b43, 0x6458c5bfc8cb930d, 0x8705ee1cf4d6122]

private theorem rounds066_0 : sixRounds 0 (by decide) absorbed066 = quarter066_1 := by
  decide +kernel

private def quarter066_2 : Vector UInt64 25 :=
  #v[0x8be9d7fea713e4f7, 0x366c66b25437c40, 0xcee75eb0a802f1da, 0xb7855ae5c8996dbd, 0xd06912c8ac607be8, 0xcd37a607ed944c83, 0xd43b58b3ff178d51, 0xded7e430a18752f4, 0xd10f6ae8fe04cb7c, 0xc78a90c5871b1518, 0xb0a4f9bd09c77090, 0xee7abe3c3458129e, 0x68d12c7dd3544fba, 0xffc3e3ffa4c41f78, 0x2940a7b2a85e7e3b, 0xa9f4ff124109dafc, 0xcd790663ed89a51, 0xd467a3bafc8c31cb, 0xb8196e96c66575f2, 0x2f43fd1b67c9f101, 0xac73a7cc79847091, 0x5eaa503ca2aa949, 0x39a328255a30d08, 0xace11880d1cc854c, 0xe5deaf33d49aaf41]

private theorem rounds066_1 : sixRounds 6 (by decide) quarter066_1 = quarter066_2 := by
  decide +kernel

private def quarter066_3 : Vector UInt64 25 :=
  #v[0x49328127ad35208, 0x992b75aa5bdd44ca, 0xcb0ad1377e0ca03f, 0xf04da4f399dff794, 0xdd3768c9fcc46ca2, 0xa9519261e367327a, 0xf917a900aa4cf1fe, 0xd33fe9dc95e9a395, 0x25227c2307173734, 0xa91cf1def05fc594, 0xee9f6b61d7f382f0, 0x297f757b24332af, 0x938335b9bb147f26, 0x34413c192d512a05, 0xb575aaa90efc45ab, 0x7636edc5259dc278, 0x1ed60007b10fe698, 0x17e2c9a4a362b288, 0x185b425041c8584d, 0x558e40933d10c313, 0xc501daecd68ba9a5, 0x53d721330184052a, 0x660ab8d660bbbfc7, 0xfe5ae5c80a25114c, 0xb24d843be83d5b2c]

private theorem rounds066_2 : sixRounds 12 (by decide) quarter066_2 = quarter066_3 := by
  decide +kernel

private theorem rounds066_3 : sixRounds 18 (by decide) quarter066_3 = state067 := by
  decide +kernel

private theorem perm066 : KECCAK.f1600 absorbed066 = state067 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds066_0, rounds066_1, rounds066_2, rounds066_3]
  rfl

theorem block066 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes066 ++ tail) state066 =
      KECCAK.Bytes.run 0 tail state067 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes066 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb066 ws)) := by
    rfl
  exact (step state066).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words066).trans perm066))

private def absorb067 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x55 0x61 0x80 0x1 0x20 0x60 0x52 0x81)) 1 (by decide) (UInt64.ofBytes 0x1 0x40 0x60 0x39 0x91 0x29 0x60 0x5d)) 2 (by decide) (UInt64.ofBytes 0x91 0x80 0x51 0x40 0x60 0x50 0x50 0x91)) 3 (by decide) (UInt64.ofBytes 0x15 0x10 0x81 0x82 0x5b 0xfd 0x90 0x3)) 4 (by decide) (UInt64.ofBytes 0x7f 0x51 0x40 0x60 0x57 0x92 0x23 0x61)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x60 0x80 0x80 0x1 0x4 0x60 0x52 0x81)) 10 (by decide) (UInt64.ofBytes 0x60 0x52 0x82 0x3 0x81 0x82 0x1 0x20)) 11 (by decide) (UInt64.ofBytes 0x61 0x80 0x1 0x20 0x60 0x52 0x81 0x26)) 12 (by decide) (UInt64.ofBytes 0x40 0x60 0x39 0x91 0x26 0x60 0xe 0x57)) 13 (by decide) (UInt64.ofBytes 0x80 0x51 0x40 0x60 0x50 0x50 0x91 0x1)) 14 (by decide) (UInt64.ofBytes 0x54 0xb 0x60 0x5b 0xfd 0x90 0x3 0x91)) 15 (by decide) (UInt64.ofBytes 0x23 0x41 0x61 0x84 0x90 0x9f 0x23 0x61)) 16 (by decide) (UInt64.ofBytes 0xac 0x23 0x61 0x55 0xb 0x60 0x5b 0x56))

private def absorbed067 : Vector UInt64 25 :=
  #v[0x1d6e1d29c3b0b238, 0xc3ca15ccbb46e62a, 0x84b729c618daba8, 0x69a8cf09ce48f159, 0xb17fc398f5fdae4e, 0x7503de63a8b96786, 0xeda2017c8d1998c6, 0x9202695e1ea2655f, 0xf1dd70e88c929229, 0x80d52d0c6e46d4ca, 0xc3d1a2bd941bd0d5, 0x23ee5409f93bb695, 0x8155678afcb0625d, 0x4fb075314c8cb8a0, 0xa1c7b1ca2f7797b0, 0xdddce4965ac57e18, 0xd2e6a6aa224d99af, 0x22c23052d5806163, 0x7832a3fae43650f0, 0xfd0c4bf76b6bf409, 0x811adefa2cd2e9ca, 0x2de3e318c6a1feb4, 0xdf6e1f733e75900d, 0x65a44819bcdbac2e, 0x405b149f781ecb02]

private theorem words067 : absorb067 state067 = absorbed067 := by
  decide +kernel

private def quarter067_1 : Vector UInt64 25 :=
  #v[0x635da723fa8ce941, 0x897b5d751516be55, 0x37114d12a09f2df1, 0x82cf22b439f45e0e, 0x3cdea0d8d5ab5c10, 0x76cf9e44f3683a49, 0x87155d7559cc83ea, 0xcfdfbceb374079c7, 0x78970cb64afca62d, 0x5cdb1225420e547f, 0xc45d7b89a6658a3d, 0xbfba39da54151bc, 0xf7393547f992c30, 0x471a7438951907bb, 0x8647fac9ca12129a, 0xa609ca1a9db5c441, 0xe86d94fb22ddf4c5, 0x3871f3ab6e443d6a, 0xa78668131d79f62e, 0x4d64514ecec80dc4, 0x26f35fb255f35693, 0x725f473673fd9015, 0x37917216781cdeab, 0x5d66279d97c10f07, 0x5a0ac64125da5ef1]

private theorem rounds067_0 : sixRounds 0 (by decide) absorbed067 = quarter067_1 := by
  decide +kernel

private def quarter067_2 : Vector UInt64 25 :=
  #v[0xbd51a1ee3407590c, 0xaf3d91d2e18213b1, 0x51757d9bda2d5ffb, 0x8eae3c8cfcba2143, 0x2994030b884b87c6, 0xd4f75bb32e837176, 0xbc30b686bf2b6e43, 0xea4f74155b8f47a8, 0x5ffc0616beb145a9, 0xaa27a1fae3ed5457, 0x8dc628108945a3d0, 0xeac738223eb4e382, 0x7f41d8e7db973d47, 0xdcb5b72f60a8b94e, 0x70716c3d8574705b, 0x89fc06c4c8029308, 0x94b21aa71824e99a, 0xc077ce8171af13a5, 0xe7647270dda794fa, 0xa46870e92a11a0f0, 0x171bc27f4ac3fe9f, 0x45b569895d647863, 0x8b9bae800598b7d8, 0xc35bec3037c7856c, 0x7a037e5bb6e79849]

private theorem rounds067_1 : sixRounds 6 (by decide) quarter067_1 = quarter067_2 := by
  decide +kernel

private def quarter067_3 : Vector UInt64 25 :=
  #v[0xbfd315818022f534, 0x142bb049328243b, 0x920418f386c9ee2e, 0x12b1f0e293884740, 0xc1957cff4da97def, 0x364bd9236a93628e, 0x9638d9b3e31e0f55, 0x5a71173e90a67a0c, 0xe5f6ab590922e916, 0x4e0747523b5aa7d7, 0x607f46d91cf36618, 0x400cd85c99d64655, 0x867b392c8bfaa0, 0x82f8ebe9727a8923, 0x3a71f9076d366fa8, 0xd789badc9c23c555, 0xba31f678a8860f0c, 0x1c345278064a26d7, 0x6f4fa07a5014c6a7, 0xbb88f162deb71d37, 0x456ddbec792a795e, 0x25f3a72dde8c611f, 0x79b800e3108415ff, 0xd2b5825ccf315b38, 0xedd30b44bb0389ab]

private theorem rounds067_2 : sixRounds 12 (by decide) quarter067_2 = quarter067_3 := by
  decide +kernel

private theorem rounds067_3 : sixRounds 18 (by decide) quarter067_3 = state068 := by
  decide +kernel

private theorem perm067 : KECCAK.f1600 absorbed067 = state068 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds067_0, rounds067_1, rounds067_2, rounds067_3]
  rfl

theorem block067 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes067 ++ tail) state067 =
      KECCAK.Bytes.run 0 tail state068 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes067 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb067 ws)) := by
    rfl
  exact (step state067).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words067).trans perm067))

private def absorb068 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x33 0x5b 0x56 0x23 0x41 0x61 0x84 0x81)) 1 (by decide) (UInt64.ofBytes 0x60 0x9 0x60 0x52 0x81 0x81 0x0 0x60)) 2 (by decide) (UInt64.ofBytes 0x82 0x91 0x40 0x60 0x52 0x81 0x90 0x20)) 3 (by decide) (UInt64.ofBytes 0x51 0x80 0x55 0x93 0x90 0x93 0x20 0x90)) 4 (by decide) (UInt64.ofBytes 0x7f 0x92 0x91 0x51 0x90 0x52 0x81 0x86)) 5 (by decide) (UInt64.ofBytes 0x80 0x32 0x87 0xb4 0xdb 0xf5 0x16 0xcc)) 6 (by decide) (UInt64.ofBytes 0x73 0x6 0xbd 0x9d 0xe0 0x1e 0x5c 0x81)) 7 (by decide) (UInt64.ofBytes 0x7a 0xcf 0x12 0x44 0x18 0xcc 0xff 0x6c)) 8 (by decide) (UInt64.ofBytes 0xa5 0x7c 0x39 0x5d 0xb7 0xfd 0xa0 0x71)) 9 (by decide) (UInt64.ofBytes 0xa2 0x90 0x1 0x3 0x90 0x82 0x91 0x92)) 10 (by decide) (UInt64.ofBytes 0x90 0x52 0x81 0x84 0x51 0x80 0x40 0x60)) 11 (by decide) (UInt64.ofBytes 0xdd 0x7f 0x91 0x33 0x91 0x0 0x60 0x51)) 12 (by decide) (UInt64.ofBytes 0x69 0x9b 0xc8 0xe2 0x1b 0xad 0x52 0xf2)) 13 (by decide) (UInt64.ofBytes 0x95 0xaa 0x8d 0x37 0xfc 0x68 0xb0 0xc2)) 14 (by decide) (UInt64.ofBytes 0x28 0x16 0xa1 0xc4 0x63 0xf1 0xa7 0x2b)) 15 (by decide) (UInt64.ofBytes 0x91 0xef 0xb3 0x23 0xf5 0x4d 0x5a 0xf5)) 16 (by decide) (UInt64.ofBytes 0xa3 0x90 0x1 0x20 0x60 0x3 0x90 0x81))

private def absorbed068 : Vector UInt64 25 :=
  #v[0xe93b798768133702, 0x949f52edcac458ad, 0x778ad74fb1cc883b, 0x1ef8eee405439054, 0xbb039b4c5a96eeb2, 0x1497dc52064b82e6, 0x4bcee67076a6abbe, 0xac4c7993edda7124, 0x6662465c59f810, 0xcfcda439176cee12, 0xef4907a32424cf0f, 0x152a6d31ca33bac3, 0xa7a3ad03c7613c35, 0x383d96494faa4e2a, 0x9d9e7b19f14ef0fb, 0x56c3b9d9b0294079, 0x3e70e86dd8294fbc, 0xfc24429ca7a9900c, 0x170923832929a63e, 0x3a57f88c067e0601, 0xc9ac02990d2d950d, 0x7fc0573ffa747ea4, 0x9f975c4939216b92, 0x90cf90be21621ac8, 0xf6040b9c78d1f2c9]

private theorem words068 : absorb068 state068 = absorbed068 := by
  decide +kernel

private def quarter068_1 : Vector UInt64 25 :=
  #v[0x86c02cfe421ba89c, 0x6c3a4f47a982bc89, 0x70a6817c5e563536, 0x378ede2f412cc7d4, 0xe2ec6515a791ef1f, 0x6010b36c248a28d8, 0x1ce9fce260d8c097, 0x1365847a014b48d8, 0xf4368049094d26d0, 0x9fbe329c223c47b4, 0x1aaee6d4d3df4db0, 0x13a27da141bfc423, 0xc4b135f55bb7f274, 0x64d5b9a0e64e328a, 0x96cad57edd1efdad, 0x89f01a5c8e2db6fe, 0x85e4e70eee187cf6, 0x1bad5518da001350, 0xce1fd057ab03b5cc, 0xffb160f7fc317335, 0x9074fa08366b57d3, 0xce1e3ce7d8593d09, 0x7abf64c08122e8b2, 0xab94f55d59dcac6d, 0x5f68f296d18ec0aa]

private theorem rounds068_0 : sixRounds 0 (by decide) absorbed068 = quarter068_1 := by
  decide +kernel

private def quarter068_2 : Vector UInt64 25 :=
  #v[0xad232f2314115afa, 0x706c215901b21826, 0x7527da21d199da4d, 0x22f6fdfa05ffca0, 0x957ec1e28b7c1605, 0x923b9ef0825fa103, 0x3ac31a8149664146, 0x4891ce51ca7c675d, 0xe755d54a63caa1ef, 0x6f838cbca7cfbe82, 0xe1d5d8ef5025d3cf, 0x57fbe4d26b28142, 0xe19d61a04096a8cd, 0x8a9480362716e529, 0x589888783bd5dee2, 0x58bbcc5e828d0b00, 0x995084de0a8be624, 0x85cd65a5baa2565f, 0x56c281ecef8c906a, 0xb73a0e41b1226201, 0xf3065501d00394c2, 0xfacb64757121ee58, 0x6a5f5ebd80c6315a, 0xdd75c1a7b8d095f6, 0x4d28dc10dd1d7ee5]

private theorem rounds068_1 : sixRounds 6 (by decide) quarter068_1 = quarter068_2 := by
  decide +kernel

private def quarter068_3 : Vector UInt64 25 :=
  #v[0xb33c7f08da815398, 0x735a08177ba260ee, 0x490587be57b07489, 0x655c9f0b1ca2e043, 0x57214459149320b3, 0xf578855f8271e5e7, 0x63600f51960e3d6, 0x8509b08e0b94748d, 0x59e989e5b4fbf2a9, 0xd21f9d6a82f11f7d, 0x6ececc35a86e2907, 0xfe6f4a6358fb6633, 0x3f03127ca9c436b6, 0xec6918f4f75fbad5, 0x82b325d967213d30, 0x936daa98e27f4cf0, 0xce104300f484d661, 0x797f6af3101cae02, 0x192d42d298198cbc, 0xf43b4803670f17e9, 0x890316d502591092, 0x4eaa167c7b8998b7, 0xa1c131895dabaf16, 0xca8b3304d88a4628, 0xd4225abae6f0b915]

private theorem rounds068_2 : sixRounds 12 (by decide) quarter068_2 = quarter068_3 := by
  decide +kernel

private theorem rounds068_3 : sixRounds 18 (by decide) quarter068_3 = state069 := by
  decide +kernel

private theorem perm068 : KECCAK.f1600 absorbed068 = state069 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds068_0, rounds068_1, rounds068_2, rounds068_3]
  rfl

theorem block068 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes068 ++ tail) state068 =
      KECCAK.Bytes.run 0 tail state069 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes068 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb068 ws)) := by
    rfl
  exact (step state068).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words068).trans perm068))

private def absorb069 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x5 0xb7 0x7f 0x5b 0x56 0x50 0x50 0x50)) 1 (by decide) (UInt64.ofBytes 0xeb 0x58 0x19 0xa9 0xbd 0x4c 0xe9 0x59)) 2 (by decide) (UInt64.ofBytes 0x0 0x49 0x3b 0x5b 0xb6 0xf9 0x7 0xec)) 3 (by decide) (UInt64.ofBytes 0x11 0xd7 0xac 0x8d 0x5c 0xd2 0xc8 0x97)) 4 (by decide) (UInt64.ofBytes 0x56 0x81 0xd8 0xb6 0x15 0x10 0xdf 0x5)) 5 (by decide) (UInt64.ofBytes 0x74 0x90 0x0 0x60 0x54 0x1 0x60 0x5b)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x1)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x60 0x4 0x90 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x60 0x57 0xe3 0x24 0x61 0x15 0x16 0xff)) 10 (by decide) (UInt64.ofBytes 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x80 0x40)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x0 0x0 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x60 0x10 0x60 0x52 0x1 0x82 0x4 0x60)) 16 (by decide) (UInt64.ofBytes 0x75 0x61 0x50 0x7f 0x52 0x1 0x82 0x24))

private def absorbed069 : Vector UInt64 25 :=
  #v[0x245683f7aa14ded3, 0x1367da01d67eabef, 0x9d09c30303205fe9, 0x8a7a444991979845, 0x7488881cf6e68948, 0xe3559909225e66cf, 0x937211c24a0202c, 0x88f97bd13f33e493, 0x137717c8c45f8e0a, 0xd0ce4de56ba852c4, 0x7b31e67f09755f69, 0xef8f63be15319e0c, 0xd1af98effc7edb31, 0xfce13d78a62d17cf, 0x305ecbd2a2476275, 0xa27efa373a55af15, 0xf80dc0c007f4cb43, 0x2f0622ebb64349f9, 0x469d1d53b56ae1ff, 0x7aca68a4718694dd, 0x7291504e1bb17b0c, 0x2194b8c20f887156, 0xb1bd97e00cccd562, 0xbac552147f7a81c1, 0xc66db1e408b01085]

private theorem words069 : absorb069 state069 = absorbed069 := by
  decide +kernel

private def quarter069_1 : Vector UInt64 25 :=
  #v[0xf086965629d0944e, 0xc9cdf1e021f28ff5, 0x58b28e55bfa8d8b4, 0x89cca07974564163, 0xab76d772d687c52f, 0x4eb9eff47e824de0, 0x9899109e949ef226, 0xaf444a98255774f0, 0x1eaa99ed1e2d545, 0x8b1f127f5406e35, 0x1684c33418777513, 0x9a27705ffb8a5c40, 0xa5f013b87e5e3f90, 0x6a212cf6bec18b97, 0xaf4d9b682b81fcfd, 0x91e2bab9eb7b295f, 0x2cf07943cf9eca88, 0xe9722f3210d767f2, 0xe5e1736cc452961d, 0xb3892a035864d9c2, 0x6ed23585fc565555, 0x241cde2f307c5fb9, 0x208bbb4f297ed837, 0x43f6789777cd255, 0x1e1c9db535d31e9b]

private theorem rounds069_0 : sixRounds 0 (by decide) absorbed069 = quarter069_1 := by
  decide +kernel

private def quarter069_2 : Vector UInt64 25 :=
  #v[0x3842108a603503a3, 0x25916eb58b07145, 0x8a738a4902230ee6, 0x6d5d1222322082e7, 0x57ece82f6873a9ee, 0x908d749efb1239b3, 0x982dab0133e7cb39, 0xef2c02eeae06ae85, 0xde30d56b977f6cf4, 0xae1d4645e54aa643, 0xd1e33f67950354c3, 0x5ed13c78a71e1edb, 0x320c5e43611d2779, 0x89f287436bd0ae4d, 0x75662d97d775f053, 0xe51a3e59ac87a72d, 0xae2fc4b84e7a2847, 0xc21f8fe8e31ba956, 0xd560f7169b83da6b, 0xeb8889aa47d337e5, 0x12e9e25f3755838, 0x529b6e7e285c54e8, 0x3eeb1071e590ff8b, 0x70299d0d1d0208e9, 0x7651047beddf873f]

private theorem rounds069_1 : sixRounds 6 (by decide) quarter069_1 = quarter069_2 := by
  decide +kernel

private def quarter069_3 : Vector UInt64 25 :=
  #v[0x2dca413b0c937c8a, 0xbc8b7d24c4de45af, 0xf105d54b33ec1246, 0x3161340037bbe8f8, 0x25c43279aff500a1, 0xfc3c3ccc772264d4, 0xbd6678f86a2e5a4b, 0xa080bf5fbe6d4dc7, 0xb6855c443d27a3fb, 0xfd4fd9db231ad0a9, 0xad6be95563641b70, 0xc9758207e16c313b, 0xdfc9a952520e7ce9, 0x4c20d42808ec367, 0x6856213efd21a315, 0xa96f59456cf97858, 0x29157b006d0f962e, 0x26df2c2a70627d9b, 0xe0c5888884c1d3d4, 0x9c72f0950b8ce090, 0x8c3c1620bc750480, 0x5b96cb9693212137, 0x92da815805690158, 0xefeaa568f0b43493, 0xd117ae5236e5283f]

private theorem rounds069_2 : sixRounds 12 (by decide) quarter069_2 = quarter069_3 := by
  decide +kernel

private theorem rounds069_3 : sixRounds 18 (by decide) quarter069_3 = state070 := by
  decide +kernel

private theorem perm069 : KECCAK.f1600 absorbed069 = state070 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds069_0, rounds069_1, rounds069_2, rounds069_3]
  rfl

theorem block069 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes069 ++ tail) state069 =
      KECCAK.Bytes.run 0 tail state070 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes069 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb069 ws)) := by
    rfl
  exact (step state069).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words069).trans perm069))

private def absorb070 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x70 0x20 0x3a 0x65 0x6c 0x62 0x61 0x73)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x64 0x65 0x73 0x75 0x61)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x82 0x44 0x60 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x3 0x90 0x81 0x90 0x51 0x90 0x52 0x1)) 5 (by decide) (UInt64.ofBytes 0x8 0x60 0x5b 0xfd 0x90 0x1 0x64 0x60)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x54)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x33 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x57 0x53 0x25 0x61 0x14)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8 0x7f)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x80 0x80 0x1 0x4 0x60 0x52 0x81 0x0)) 15 (by decide) (UInt64.ofBytes 0x52 0x82 0x3 0x81 0x82 0x1 0x20 0x60)) 16 (by decide) (UInt64.ofBytes 0x80 0x1 0x20 0x60 0x52 0x81 0x29 0x60))

private def absorbed070 : Vector UInt64 25 :=
  #v[0x6d989de1629049e0, 0xd450e76ba01ace78, 0x35863aca51ef5bc4, 0xa5a74279ec78306b, 0xe0d47776ea015238, 0xe335b3926437928f, 0xc4804267b936ee77, 0xd1636e315245ffb1, 0x346296c46785666a, 0x9642ba203953621f, 0x5ef81c36cabb3972, 0xff78965118dfc3a9, 0x91bde7a8fd053ae7, 0x46c57c5c1738e4c6, 0xed44bc9589b789ff, 0x9255c1520babaeff, 0x2137c0e7b3afbef7, 0x4f824f9004945bcb, 0xa196429910b0593a, 0xf5ab4e4c9b1a2fe5, 0xbe9641b733d701ed, 0xb4d7075adabbbe3c, 0x94ef40bd91964095, 0xa3e5b64eef640234, 0xff7bdeefb3bdaf72]

private theorem words070 : absorb070 state070 = absorbed070 := by
  decide +kernel

private def quarter070_1 : Vector UInt64 25 :=
  #v[0xf9d14be164722c65, 0xcfe2bf0eddbe628c, 0xb0978d68ae8b2070, 0xfb38bf012934fea1, 0xe5235e537df483e, 0xc6beb8126fa92f7, 0x73f7141951e97937, 0xcf00ae3c800bcf61, 0x562f0a5fcf534a4b, 0x8809f573425030ac, 0x29d7571597c5b758, 0x693044e31271dfbe, 0xed9b41669d28d2e3, 0x580fd7a5dafd3d1a, 0x1dbf29f1756cf05a, 0x449fcd65dc62ebfa, 0xd00ae73ca5966265, 0x9d427846947b068c, 0xa27bf20d33b5c96a, 0x8f1d831949b2cc91, 0x9e0062c03bed8dda, 0xc82d695fdc891470, 0xd55b411090065939, 0xeeb5e0d4b44ac7d9, 0x415fc27cd8e12330]

private theorem rounds070_0 : sixRounds 0 (by decide) absorbed070 = quarter070_1 := by
  decide +kernel

private def quarter070_2 : Vector UInt64 25 :=
  #v[0x2222786fbf993838, 0x7e419477c994a5ab, 0xa6444bb986a65a39, 0x83557c5fba0dbdb0, 0xbaee79a308b540a2, 0x5453f2936e5a7048, 0xbd2ded7e070f2076, 0xad78943c3487a65, 0x2fe8787520735b93, 0x1c57ab34fb910ce6, 0xc5524899d013cb1a, 0x825fd519efbc63b5, 0xe1c795830b0c3ae9, 0x9982172836e9948c, 0x4a140b7b2a95b8ec, 0x202540f43f0aa8d1, 0xa5565dc75b647491, 0x437707e8ba1081ed, 0x344b5144bc7622aa, 0xa75a6f2ecfa94809, 0xdbe3a41509b5abef, 0x251b9aaa992f4e97, 0xae2fa19720e23d8b, 0x8bada17dd94751e8, 0x19c6757b49950eff]

private theorem rounds070_1 : sixRounds 6 (by decide) quarter070_1 = quarter070_2 := by
  decide +kernel

private def quarter070_3 : Vector UInt64 25 :=
  #v[0x4a6a53e3c2abbb6c, 0xf2422a898e4ee354, 0x43ebf7743e9189e5, 0x3471005d956560f4, 0x92d9bf6b757f6518, 0x8b684c00c9091a16, 0xf8edd9eae3ef112, 0x7d3acfa1602a7ee5, 0x9c8d89a867d3c01b, 0x19dc4bfbe40a9208, 0x30a7415d7e72aa45, 0x15ecf588c7c02729, 0xd78624be8c0d226d, 0xf4292a7f181710b8, 0xde315fbc31f191a7, 0xd70e8c0a3a69c6a4, 0x845faacaf380da6, 0xa02cf4c775c7ba12, 0xffdaf4d719a39d5a, 0xeff24e712bc063ed, 0x229f7c60c9cb2fba, 0x9fc1014a266598c0, 0x797d32813b5fe097, 0x196079d8c3950693, 0x4e7bc0c715075101]

private theorem rounds070_2 : sixRounds 12 (by decide) quarter070_2 = quarter070_3 := by
  decide +kernel

private theorem rounds070_3 : sixRounds 18 (by decide) quarter070_3 = state071 := by
  decide +kernel

private theorem perm070 : KECCAK.f1600 absorbed070 = state071 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds070_0, rounds070_1, rounds070_2, rounds070_3]
  rfl

theorem block070 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes070 ++ tail) state070 =
      KECCAK.Bytes.run 0 tail state071 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes070 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb070 ws)) := by
    rfl
  exact (step state070).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words070).trans perm070))

private def absorb071 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x60 0x39 0x91 0x29 0x60 0xb9 0x56 0x61)) 1 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x50 0x50 0x91 0x1 0x40)) 2 (by decide) (UInt64.ofBytes 0xff 0x73 0x5b 0xfd 0x90 0x3 0x91 0x80)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x81 0x0 0x60 0x16 0x83 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x81 0x90 0x20 0x60 0xc 0x60 0x52 0x81)) 7 (by decide) (UInt64.ofBytes 0x54 0x80 0x20 0x83 0x80 0x40 0x60 0x52)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x7f)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x60 0x55 0x90 0x17 0x1 0x60 0x16 0x0)) 13 (by decide) (UInt64.ofBytes 0x85 0x20 0x90 0x82 0x91 0x52 0x82 0xd)) 14 (by decide) (UInt64.ofBytes 0x91 0x52 0x81 0x85 0x51 0x81 0x55 0x90)) 15 (by decide) (UInt64.ofBytes 0x2e 0x91 0xca 0xf 0x98 0x46 0x7f 0x51)) 16 (by decide) (UInt64.ofBytes 0x7b 0x42 0x77 0x68 0xd3 0xdb 0xbc 0xf9))

private def absorbed071 : Vector UInt64 25 :=
  #v[0xb768d65b59e46b93, 0x5181e735b087936c, 0x60140bf7a31abf68, 0xdab73b16330c3d6c, 0xa891bef0cd4d58f8, 0x9ee4c735224ae70, 0xf5daaca2816478a7, 0x1cab906177944aaf, 0xd485ba39a9447172, 0xc2f188f9411f13d0, 0xe557e325e6d6e9fb, 0x22a12edee4422e39, 0xdafae09ddb0ac24b, 0xe2ad7d8a83e86a71, 0xf00a524ef58f4346, 0x1d5d399d62c13511, 0x53ca49f8b5fecce4, 0xba8b7a614d47ae0a, 0xcdfae48b49bb1736, 0xbdef013ce833a7ea, 0x9f456e614ad39359, 0xf773aed6c3f6d14b, 0x88fa93b9b33928dc, 0x30456511ae61ec0f, 0x81d6efd5ee62656a]

private theorem words071 : absorb071 state071 = absorbed071 := by
  decide +kernel

private def quarter071_1 : Vector UInt64 25 :=
  #v[0x1b1ee38bf9f78b5d, 0x82eb728064f68e77, 0x394acf5fe0f25a06, 0xada5b41df6835381, 0x26f3c3d6950a47f3, 0x7bdc4331bb1ad75, 0xce8ba7dfcb05a0ff, 0x8a720085b7b6d4af, 0xb2a6ca22c911ebd, 0xfb6c1938511f06c3, 0xfb858b1ece899b1b, 0xf5bc00928d13077, 0x42709ad0766a9dd7, 0xa04a35f7190f71f1, 0xd0ad4810d90a2b2b, 0x19327a55fee28791, 0x95508ca6eef261c2, 0xf8a86305fe7d143f, 0x6e7c8ad9452a9964, 0x86e9163387227a69, 0x921faf0ff761337e, 0x54c06a8c97259b18, 0xa3963db5578f03e5, 0x1164954af710d5c6, 0xf17c212cd30eed38]

private theorem rounds071_0 : sixRounds 0 (by decide) absorbed071 = quarter071_1 := by
  decide +kernel

private def quarter071_2 : Vector UInt64 25 :=
  #v[0x31ab6969e318f34e, 0xf3aa156fdd3923a8, 0x456d6c7c3816a07a, 0x89f8061b8aa933f0, 0x5defdc5bae0ce091, 0x7a506e4e2d67ed8, 0x89acb8dc2ef226c, 0xa57ad9d03e043ce5, 0x146569b23d891080, 0x2e2d68815b199bc5, 0xd28917f9e59f8bc6, 0x61a9aadbcb831b23, 0xbe420c242b86e7f3, 0x9e9de999b8230ff1, 0xb66859a74a3ce843, 0xf87b59d110a3b41c, 0x7140d6e80b48ffb2, 0xe86dacb4b9fdac7f, 0xe54b2e148f0ab4bd, 0xfee612b50b85a79d, 0x92516092ac319f20, 0x6561813f847a80ee, 0xda0db183c202ffcf, 0x120df133a071a749, 0xbfaff7e841aed25e]

private theorem rounds071_1 : sixRounds 6 (by decide) quarter071_1 = quarter071_2 := by
  decide +kernel

private def quarter071_3 : Vector UInt64 25 :=
  #v[0xae1fae9abece654c, 0x984ed745d2de9f8a, 0xc738bc0d7e0392fa, 0x211c8ce49d814a44, 0x1c219380024e79ec, 0xe78d17a655049d23, 0x757b14a91c1e68ca, 0x929e8790dbc3410c, 0x1984f7ec8a16d28a, 0xfc6342449bb6c92, 0xfdcdb8da7b740d6f, 0x45dee89b689404b, 0xdc4af39bee346fb3, 0x5d7a1706020c188d, 0x5adccd5a8b27e2d3, 0x6aa6938070c82202, 0xf419cfe31647b422, 0x73104c47a5bde88d, 0x3e47de198a77fb58, 0x8b150c61fdc8f61c, 0xfcd21932a16ef548, 0x796e05cfc34fc0da, 0x3dc67e7d1606b1d2, 0x80f202c4ffa945c1, 0x92c2d0073ed73ca]

private theorem rounds071_2 : sixRounds 12 (by decide) quarter071_2 = quarter071_3 := by
  decide +kernel

private theorem rounds071_3 : sixRounds 18 (by decide) quarter071_3 = state072 := by
  decide +kernel

private theorem perm071 : KECCAK.f1600 absorbed071 = state072 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds071_0, rounds071_1, rounds071_2, rounds071_3]
  rfl

theorem block071 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes071 ++ tail) state071 =
      KECCAK.Bytes.run 0 tail state072 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes071 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb071 ws)) := by
    rfl
  exact (step state071).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words071).trans perm071))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
