import Blanc.Lift.Usdc.ImplV2_1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb144 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x92 0x90 0xe0 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x91 0x1 0x82 0x91 0x20 0x60 0x91 0x1)) 4 (by decide) (UInt64.ofBytes 0x1 0x60 0x5b 0x56 0xee 0x4b 0x61 0x1)) 5 (by decide) (UInt64.ofBytes 0xa 0x0 0x1 0x61 0x3 0x20 0x60 0x83)) 6 (by decide) (UInt64.ofBytes 0x84 0x81 0x16 0x51 0x82 0x19 0x80 0x3)) 7 (by decide) (UInt64.ofBytes 0x50 0x52 0x85 0x17 0x82 0x80 0x16 0x51)) 8 (by decide) (UInt64.ofBytes 0x1 0x50 0x90 0x50 0x50 0x50 0x50 0x50)) 9 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x0 0x60 0x50 0x50 0x91)) 10 (by decide) (UInt64.ofBytes 0xf1 0x5a 0x87 0x85 0x81 0x3 0x83 0x80)) 11 (by decide) (UInt64.ofBytes 0x0 0x60 0x80 0x3d 0x50 0x50 0x50 0x92)) 12 (by decide) (UInt64.ofBytes 0x40 0x60 0x57 0x8d 0x4c 0x61 0x14 0x81)) 13 (by decide) (UInt64.ofBytes 0x3f 0x60 0x19 0x1f 0x60 0x50 0x91 0x51)) 14 (by decide) (UInt64.ofBytes 0x52 0x40 0x60 0x1 0x82 0x16 0x1 0x3d)) 15 (by decide) (UInt64.ofBytes 0x20 0x60 0x0 0x60 0x3d 0x52 0x82 0x3d)) 16 (by decide) (UInt64.ofBytes 0x5b 0x56 0x92 0x4c 0x61 0x3e 0x1 0x84))

private def absorbed144 : Vector UInt64 25 :=
  #v[0x31263cb87b77cec3, 0xc3cd67da81688e74, 0x3810a860d6f25759, 0x5357f4a6094c6922, 0x9ade4c7743de4162, 0xae99d81ab467edde, 0xa557003f572ba466, 0xb6aa13f75b0800d5, 0xc15677844aa10cb2, 0xd8ebb72d5ae0dfcb, 0x21b1d19e7c85a7c3, 0x3356f6eaa417da64, 0x1c30756e6ae3007a, 0xef382ffdce7bdc60, 0x7f3b6e08d9e0ded2, 0x351b83a4d875d105, 0xa51bce96d4f09703, 0x3473e628c6d9fba3, 0xec2048eea385fe69, 0x9028d2795c35c7d6, 0xd9aa9e8624e6ea42, 0xb45dd36c70a6f715, 0xe85d373c754d555, 0x7d54921a2678fc33, 0x7e53f8448d317d81]

private theorem words144 : absorb144 state144 = absorbed144 := by
  decide +kernel

private def quarter144_1 : Vector UInt64 25 :=
  #v[0x30fc618f2741ffe8, 0xa69961e665d9f82d, 0x79669747b335ebe7, 0x63ec41c6f2d23f1a, 0xc855f1781bcbada8, 0xa6ea94526efecd06, 0x5ca4ed7d0df34398, 0xac4d4119966966f9, 0x389a7488e71fd7fe, 0xda77466a43179929, 0x713014baeab6bcf9, 0xec0f3afc00edd726, 0xa5e3cc125f2cc3a6, 0x59f1e2679e148d9b, 0xe10711e218244d13, 0x13793242da8a80bd, 0x1a66743cb69ce842, 0x74d050c250a3bf0c, 0x134a4ed835fb6fb5, 0xa319513f2d779f49, 0x1dd56151c96edeeb, 0x69d52efd8be0e4e1, 0xe1b07871a613df95, 0x6a3c170f84cdc0e1, 0xe03aef8de420c0d7]

private theorem rounds144_0 : sixRounds 0 (by decide) absorbed144 = quarter144_1 := by
  decide +kernel

private def quarter144_2 : Vector UInt64 25 :=
  #v[0x5f67b6b733d2c6f7, 0x2884b39748039dc5, 0x6547986eab2cdbf2, 0xc7523ac042cbf667, 0xd059e399d012835b, 0x9ececabd5deec7d4, 0x8274f320fc92e43c, 0x928eb049b3e30add, 0x6e24e945d0dd2ddd, 0xb2c36a5b74e98d69, 0x575f42976677e646, 0xf59b8de4e354b3cb, 0x7530e364925102cd, 0xeb33ec584cd3b339, 0x430dab98886701e7, 0xda818bfa02009160, 0xc850604a7c72e2fe, 0x15012d6e602e250b, 0xbd7e917259d713e9, 0xb082c37d945a5117, 0xb5fddd61621d777a, 0x105102beb8f92511, 0x22082a31ef22fedd, 0x65b4275ff3f83d03, 0xc8a325db330da014]

private theorem rounds144_1 : sixRounds 6 (by decide) quarter144_1 = quarter144_2 := by
  decide +kernel

private def quarter144_3 : Vector UInt64 25 :=
  #v[0x87428d16ecb2ae5d, 0x294da68125c3f6f0, 0x79ace8ece4d86a2d, 0x6562ea6aba4c3c4d, 0x7b28ba5be3f02e67, 0xb3c50402e36e964a, 0xf7c0223f8d00d336, 0x90852831d2d5b828, 0xbd505e9584ab4f18, 0x8fd2889be5965b58, 0x84c242b61422c742, 0x58ba949ce0bccf4, 0x4093c1f1a545557e, 0x8ca843add4e5a528, 0xad33107c754fd47c, 0x251efcde64c32b35, 0x50c5f1a92b5e771a, 0x60dd08d65a5147c4, 0xcec859c71180c5af, 0x2bdde79a0093405c, 0x9f43b6f75fd2ae95, 0xa94e241fbdf58051, 0xdb46c1ee4cb24027, 0x82da933e6ab4f18e, 0xbac01dff295f5e4e]

private theorem rounds144_2 : sixRounds 12 (by decide) quarter144_2 = quarter144_3 := by
  decide +kernel

private theorem rounds144_3 : sixRounds 18 (by decide) quarter144_3 = state145 := by
  decide +kernel

private theorem perm144 : KECCAK.f1600 absorbed144 = state145 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds144_0, rounds144_1, rounds144_2, rounds144_3]
  rfl

theorem block144 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes144 ++ tail) state144 =
      KECCAK.Bytes.run 0 tail state145 := by
  exact run_block_of_step bytes144 tail absorb144 state144 absorbed144
    state145 (fun _ => rfl) words144 perm144

private def absorb145 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x50 0x91 0x50 0x5b 0x50 0x91 0x60 0x60)) 1 (by decide) (UInt64.ofBytes 0x57 0xa6 0x4c 0x61 0x15 0x81 0x50 0x91)) 2 (by decide) (UInt64.ofBytes 0x56 0x50 0x90 0x39 0x4b 0x61 0x50 0x91)) 3 (by decide) (UInt64.ofBytes 0x57 0xb6 0x4c 0x61 0x15 0x51 0x80 0x5b)) 4 (by decide) (UInt64.ofBytes 0xfd 0x1 0x20 0x60 0x82 0x80 0x51 0x80)) 5 (by decide) (UInt64.ofBytes 0x79 0xc3 0x8 0x7f 0x51 0x40 0x60 0x5b)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0xa0)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x0 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x52 0x81 0x81 0x1 0x82 0x4 0x60 0x20)) 11 (by decide) (UInt64.ofBytes 0x86 0x52 0x1 0x84 0x24 0x60 0x51 0x86)) 12 (by decide) (UInt64.ofBytes 0x60 0x92 0x83 0x92 0x91 0x93 0x87 0x51)) 13 (by decide) (UInt64.ofBytes 0x80 0x90 0x1 0x85 0x90 0x91 0x1 0x44)) 14 (by decide) (UInt64.ofBytes 0x45 0x61 0x15 0x83 0x0 0x60 0x83 0x83)) 15 (by decide) (UInt64.ofBytes 0x82 0x83 0x51 0x1 0x81 0x81 0x57 0xe4)) 16 (by decide) (UInt64.ofBytes 0xcc 0x45 0x61 0x1 0x20 0x60 0x52 0x1))

private def absorbed145 : Vector UInt64 25 :=
  #v[0x75e011feaf354db0, 0xe3a9f5e23f33e13b, 0x161b1f0648847fce, 0x11e1642d1c49d7da, 0xd44aa3db952d70e8, 0x236f7f397862b28f, 0x5dd041ec44adbbc9, 0x456898c3fa77be2b, 0x91006361538b225, 0x1d3d5d24b2d2ceba, 0x7110415e47e09399, 0x1bc80fa7a683f51c, 0x284d173a2745520c, 0x3db07c1dc171422e, 0xf4949c945007245, 0x4cc74b39f970cefb, 0x8b213029ab120fdd, 0x235db635ded53ff8, 0x983ad91080eeece4, 0xce08479f359bb471, 0x711aa75a8d9e2a16, 0xf4466a486f7694b0, 0x8ad2a2b6fd571b69, 0xc5c19928fae9d8bf, 0x9f6f7a88425363ee]

private theorem words145 : absorb145 state145 = absorbed145 := by
  decide +kernel

private def quarter145_1 : Vector UInt64 25 :=
  #v[0x3041af50820a63cb, 0xd8d8a3493ae3c3d, 0xfeb8965184e59b8, 0x67aa9413875b502f, 0x23d613fbc2a0759b, 0x9f4ea7d32b4607a9, 0xdbd0ffcc5ab63d28, 0xec149844d5a23f6a, 0x9fd9a2d085ffb6b5, 0xfa1fb49fbe2ebe25, 0xe65430e0eea5bfd2, 0x9c45f3d10afdbbe3, 0xbac0439d0d635caf, 0xf59781908ae08c53, 0x36a3386a69acea2b, 0x8d8c467aa7b88fe, 0x490d309edbd97e5b, 0x502a198fab6d2788, 0x86d291c07d8a2b10, 0xa72e5e9a57c9a989, 0x54366572f541e5a5, 0x10a0108e0ecb6dfb, 0x5584d5b3ffe858df, 0xbd417503fc9669af, 0xc1ad97686bb95c16]

private theorem rounds145_0 : sixRounds 0 (by decide) absorbed145 = quarter145_1 := by
  decide +kernel

private def quarter145_2 : Vector UInt64 25 :=
  #v[0x9274649fdb3346cf, 0x7e67120659f021a5, 0xd8fe056977986b2, 0x95a19037cba47310, 0x86e2e4304977d4e8, 0xc6a1c91ac6ab18c3, 0x95aac12e2457a131, 0x42c0c682776dd4ba, 0xd27655bc10805566, 0x96984ea7c695b654, 0xcc0ebfff9b9c17b2, 0x1aada5e030d905c8, 0xa4b257951406472e, 0x7571274d8d7a2f0f, 0x1ea3d7384e76b670, 0x9f539a6bb8027601, 0x5d5e7b2e2bb488b4, 0xd514bca3f8d0ebcf, 0x3f6f4c25f76eb843, 0xd71dbf465aadca1a, 0x779846a0bb5a1c32, 0x9ca1867e837431da, 0x84ea877f731d13be, 0xc666db8a573a4b84, 0xf986c3377d074e72]

private theorem rounds145_1 : sixRounds 6 (by decide) quarter145_1 = quarter145_2 := by
  decide +kernel

private def quarter145_3 : Vector UInt64 25 :=
  #v[0x5e3f449de82504ed, 0x5e9e237fe856378, 0xbd2a2d7d50b5e32e, 0x7f3e4ea8443170be, 0x374a55918f33ec52, 0x354918697a6fbedb, 0xe96fffd293dce31e, 0x11392267282dd873, 0x445b39800645f759, 0x64ce15108ce0151e, 0x240b9cbe32c741d9, 0xa06c02388608bb81, 0x8f40909ed148df84, 0x344181062858311c, 0x4008edaf73e2d26c, 0x26f0ae48bf1e3d79, 0x8d105d76581c4ddb, 0x3a1ac141004ca4e3, 0x87ec3ed679e89803, 0x6aed240ed85547b5, 0x367d85fd3ecb37d4, 0x89c0c1e1262279e7, 0x7565f4aebc2325cb, 0x45d27858d194db8, 0xd9a2147a7626fd85]

private theorem rounds145_2 : sixRounds 12 (by decide) quarter145_2 = quarter145_3 := by
  decide +kernel

private theorem rounds145_3 : sixRounds 18 (by decide) quarter145_3 = state146 := by
  decide +kernel

private theorem perm145 : KECCAK.f1600 absorbed145 = state146 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds145_0, rounds145_1, rounds145_2, rounds145_3]
  rfl

theorem block145 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes145 ++ tail) state145 =
      KECCAK.Bytes.run 0 tail state146 := by
  exact run_block_of_step bytes145 tail absorb145 state145 absorbed145
    state146 (fun _ => rfl) words145 perm145

private def absorb146 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xc5 0x7f 0x3f 0x81 0x0 0x60 0x5b 0x56)) 1 (by decide) (UInt64.ofBytes 0x92 0x3c 0x23 0xf7 0x86 0x1 0x46 0xd2)) 2 (by decide) (UInt64.ofBytes 0xe5 0xc0 0x3 0xc7 0xdc 0xb2 0x7d 0x7e)) 3 (by decide) (UInt64.ofBytes 0x7b 0x3b 0x27 0x82 0xca 0x53 0xb6 0x0)) 4 (by decide) (UInt64.ofBytes 0x81 0x70 0xa4 0x85 0x5d 0x4 0xd8 0xfa)) 5 (by decide) (UInt64.ofBytes 0x39 0x4b 0x61 0x90 0x15 0x80 0x14 0x81)) 6 (by decide) (UInt64.ofBytes 0x50 0x91 0x92 0x15 0x15 0x50 0x50 0x57)) 7 (by decide) (UInt64.ofBytes 0x1 0x60 0x54 0x80 0x82 0x5b 0x56 0x50)) 8 (by decide) (UInt64.ofBytes 0x0 0x1 0x61 0x15 0x16 0x1 0x60 0x81)) 9 (by decide) (UInt64.ofBytes 0x90 0x4 0x90 0x2 0x60 0x16 0x3 0x2)) 10 (by decide) (UInt64.ofBytes 0x20 0x0 0x60 0x20 0x60 0x52 0x0 0x60)) 11 (by decide) (UInt64.ofBytes 0x4 0x90 0x20 0x60 0x1 0x1f 0x60 0x90)) 12 (by decide) (UInt64.ofBytes 0x61 0x10 0x1f 0x60 0x82 0x92 0x1 0x81)) 13 (by decide) (UInt64.ofBytes 0x19 0xff 0x60 0x51 0x80 0x57 0x91 0x4d)) 14 (by decide) (UInt64.ofBytes 0x61 0x55 0x85 0x17 0x1 0x80 0x83 0x16)) 15 (by decide) (UInt64.ofBytes 0x60 0x1 0x80 0x82 0x5b 0x56 0xbe 0x4d)) 16 (by decide) (UInt64.ofBytes 0x4d 0x61 0x15 0x82 0x55 0x85 0x1 0x1))

private def absorbed146 : Vector UInt64 25 :=
  #v[0x9b6de2d1cbf1f514, 0x5d0e1f04de8c4adf, 0x65454655be855928, 0xc24f08159b05d243, 0x8f3d68bd29154593, 0xa525d35b9b25dd6d, 0xc2949f2cff5c4cc9, 0xe315079478a98988, 0x30fdf5e7597acce, 0x573e7b396b4924a6, 0xc7a9cece9e509b8d, 0xccf8ffbd7499982e, 0xe34774a982f2fd7e, 0xc4309b103d15ff98, 0xf975e5e3c5e6f32a, 0xeff37adaf87374ae, 0xf09a305834dd3e73, 0x26cdad377ede6e08, 0xf17d10406dc22fe6, 0x6466f19a2a6c99bf, 0xa5c81f4710eeb1d7, 0x3bd13b7507886df1, 0x4d76c153d8778afd, 0xaae414ef9258cbac, 0x7678162ff0c7dfeb]

private theorem words146 : absorb146 state146 = absorbed146 := by
  decide +kernel

private def quarter146_1 : Vector UInt64 25 :=
  #v[0xccdc84c722346be9, 0x71d9b4fbb01ca7e4, 0xb358e401f77424f0, 0x7e5acbcdbad90650, 0x20092c13ee087a40, 0x88d31ca63c60813c, 0xd7339a1811bc941c, 0x4fe6f6101e1bf569, 0xc1235ccb27bd7c05, 0xc501c4c14ecfedc4, 0xb952586959c915b, 0xaeaab6393beb3bcd, 0xe90df538dd46463d, 0xa1c0646e961de394, 0xafd72db0f644e0f5, 0xbc7869dc5292b8b5, 0x7d37ed4b174c7e3e, 0x3de5d82aa41e0436, 0x8c47d2e6d3d2a707, 0xbdaf95677ad10161, 0x60f2439a90981db5, 0x253ef7c6cc4da508, 0x18d30e575701c6d8, 0x774fbe4ab0003c4c, 0x60d5fa8454a6a45d]

private theorem rounds146_0 : sixRounds 0 (by decide) absorbed146 = quarter146_1 := by
  decide +kernel

private def quarter146_2 : Vector UInt64 25 :=
  #v[0x9d1f5297799bbddf, 0x659109e8099499da, 0xecb73a2c631b89d0, 0x1520ff9486d24432, 0x550983cbd3decb46, 0xca593c34ab57b356, 0xc30d23d20b10c77b, 0x4ff0d3226792ac4a, 0x378ae3fcaf562ad9, 0x3df4e83e169f994c, 0xf78be95e7b11086f, 0xe24eb98f2a0dec53, 0x735bba9711fb2596, 0x8589f42cf170b1f4, 0xa864e645021a278c, 0x60ef25095f27c747, 0xbb59dfa40c73d9b9, 0xffd2fa87971450c7, 0x58767c25e5395436, 0xf4d4f250b445de90, 0x858143aba2982ebc, 0x3b13ecfd1477bcef, 0x3365e6db4d43d6b4, 0x6ec199a1d6c1d332, 0x6098a41b12b39028]

private theorem rounds146_1 : sixRounds 6 (by decide) quarter146_1 = quarter146_2 := by
  decide +kernel

private def quarter146_3 : Vector UInt64 25 :=
  #v[0xb66c7e3a0761281f, 0x6da28e3811e3cbc8, 0xac19b3cd9cb29ed0, 0x42f0b484d057e948, 0x9d131ed37d7511f6, 0x1c1748488c7a8de1, 0x8745cfa9b112966d, 0x826a81da1167e23c, 0x74fd9f8e101dc88f, 0x2d186b7ae77e4250, 0x224eded191ca3668, 0x2d9442a475b73eed, 0x9027d6241e3b6105, 0xd76c70317619d007, 0x6c1947d1619642ae, 0xee165dfe31286325, 0xb1a9a60ae3cc092, 0x61bf3b86706bcdd9, 0x592e4e090897bb5e, 0xfac777017d5a425a, 0xf3abc9b9e77c0c20, 0x1f700810ea2d8af8, 0x3c68e8161b2c4ad5, 0x73a3f672b7e19c4f, 0x336ec9adbc800e29]

private theorem rounds146_2 : sixRounds 12 (by decide) quarter146_2 = quarter146_3 := by
  decide +kernel

private theorem rounds146_3 : sixRounds 18 (by decide) quarter146_3 = state147 := by
  decide +kernel

private theorem perm146 : KECCAK.f1600 absorbed146 = state147 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds146_0, rounds146_1, rounds146_2, rounds146_3]
  rfl

theorem block146 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes146 ++ tail) state146 =
      KECCAK.Bytes.run 0 tail state147 := by
  exact run_block_of_step bytes146 tail absorb146 state146 absorbed146
    state147 (fun _ => rfl) words146 perm146

private def absorb147 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x81 0x82 0x5b 0x1 0x82 0x91 0x57 0xbe)) 1 (by decide) (UInt64.ofBytes 0x51 0x82 0x57 0xbe 0x4d 0x61 0x15 0x11)) 2 (by decide) (UInt64.ofBytes 0x90 0x91 0x1 0x20 0x60 0x91 0x55 0x82)) 3 (by decide) (UInt64.ofBytes 0x56 0xa3 0x4d 0x61 0x90 0x1 0x1 0x60)) 4 (by decide) (UInt64.ofBytes 0x50 0x91 0x92 0xca 0x4d 0x61 0x50 0x5b)) 5 (by decide) (UInt64.ofBytes 0x56 0x90 0x50 0x5b 0x56 0x5a 0x4e 0x61)) 6 (by decide) (UInt64.ofBytes 0x60 0x81 0x1 0x60 0x54 0x80 0x82 0x5b)) 7 (by decide) (UInt64.ofBytes 0x3 0x2 0x0 0x1 0x61 0x15 0x16 0x1)) 8 (by decide) (UInt64.ofBytes 0x0 0x60 0x90 0x4 0x90 0x2 0x60 0x16)) 9 (by decide) (UInt64.ofBytes 0x60 0x90 0x20 0x0 0x60 0x20 0x60 0x52)) 10 (by decide) (UInt64.ofBytes 0x1 0x81 0x4 0x90 0x20 0x60 0x1 0x1f)) 11 (by decide) (UInt64.ofBytes 0x2d 0x4e 0x61 0x10 0x1f 0x60 0x82 0x92)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x7f 0x1 0x80 0x82 0x57)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x16 0x35 0x82 0x0 0xff 0xff 0xff 0xff))

private def absorbed147 : Vector UInt64 25 :=
  #v[0xc69e4187648f7d65, 0x4752ae1d2da832d6, 0xd12592fba5de9366, 0xf4535a758114b094, 0x86ffa4ec69c09a04, 0xd77756eb1705dcda, 0x2e2f47686d6e1e66, 0x65350efd7fbcc32f, 0xb0d9b852f18dcf00, 0x6ddffce7978aa936, 0x380f2266b0f0d4bf, 0x7cc398b07dacc5df, 0xdb1e6acf861ab4be, 0x342668df9bdfaa13, 0x4a1652fbe216c95b, 0x40455f6ba1b8974a, 0xcb1fa30b6c956771, 0x1f5f873689598961, 0x33deb6dfb16c2950, 0xda07df3de730d5cb, 0xb0e63aaad3e77d62, 0x7bacddb40d630230, 0xa163756fab833fff, 0xac480c08313f2f28, 0x8d94bdcc5f4b34c4]

private theorem words147 : absorb147 state147 = absorbed147 := by
  decide +kernel

private def quarter147_1 : Vector UInt64 25 :=
  #v[0x6540e52d71783137, 0x9a2e7039f6c231d9, 0x33a6357f9378767f, 0x7f16e33ce01deb02, 0xe544621468388488, 0x6eac0dcbbe34f9ea, 0x9f548eb3e3b386c6, 0xf538a293ee10854c, 0xf83b262cc092e7fc, 0x56ed517755cd3eaa, 0xa1f6f8853679b364, 0x38ec7150fcd7e97c, 0x84d45e3c35afc6b7, 0xc5377b59228ad70b, 0x88f234277abd7e02, 0x14a846f160bf57e7, 0x8eb3c8408948088b, 0x1c6f2803ba8a9c8a, 0x194d73f1528136c5, 0x9d17da2ca09a0a8, 0xfd6dfdca43eabffc, 0x37d474947c0d3e2f, 0xab7544b431c2ce1b, 0xf23b994102b4c6d7, 0x9b8838fc27b37971]

private theorem rounds147_0 : sixRounds 0 (by decide) absorbed147 = quarter147_1 := by
  decide +kernel

private def quarter147_2 : Vector UInt64 25 :=
  #v[0x8ff7cb63bcbe0052, 0x449c0382d1d945ff, 0x780f29400dac95cb, 0xcc69dc99178ef4b9, 0x865564e55bb18557, 0xde26a1a4dac49160, 0x55a1944cb219717, 0x1965dc5a642a3794, 0x1460f4e743fe1089, 0xf28d05e315b2befa, 0x62e47194ad6a02e6, 0x227de9a012e09cb6, 0x727300eb03ee5cf4, 0x613c9d9e97936b84, 0x32d578946b0383e8, 0xe282aa3c316ca846, 0x272589481fa49ffe, 0x304fd03444653517, 0x5ef0300ebaf4d8cf, 0xed15f3ba0da7cbb2, 0x5c1aef5593987c38, 0x8a76e3104e696787, 0x4905f4830e21e34a, 0x4bd051c994fcc46b, 0x7d34b79ccf806278]

private theorem rounds147_1 : sixRounds 6 (by decide) quarter147_1 = quarter147_2 := by
  decide +kernel

private def quarter147_3 : Vector UInt64 25 :=
  #v[0x9f76ab27c1f8fba2, 0x38e7701618c83615, 0x5c00992f4eecf764, 0x4ce4f89b924c2ffc, 0x8f970bc742f630e8, 0x4eb4aa7fb73e8b92, 0x7bda6a2303a0d48, 0xdf7653926413fa, 0xe912710ab0d26314, 0x806c83e7f10c2a2d, 0x691bb7798de3b103, 0x6a3a074f38f2d799, 0x4810ab6cd6456e8d, 0x89be27daad4598ca, 0x1a3260597d439a8d, 0x805497d3e5ec05fc, 0xc318131a48926111, 0x43b0126695f1623c, 0x8dd9c115123cb958, 0xf88135440d095623, 0xd016a3aa4d72c5b3, 0x35185ba6bf2d6396, 0x4f1538b13904458e, 0x87152a6be1d98724, 0x298279f9d7791bf4]

private theorem rounds147_2 : sixRounds 12 (by decide) quarter147_2 = quarter147_3 := by
  decide +kernel

private theorem rounds147_3 : sixRounds 18 (by decide) quarter147_3 = state148 := by
  decide +kernel

private theorem perm147 : KECCAK.f1600 absorbed147 = state148 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds147_0, rounds147_1, rounds147_2, rounds147_3]
  rfl

theorem block147 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes147 ++ tail) state147 =
      KECCAK.Bytes.run 0 tail state148 := by
  exact run_block_of_step bytes147 tail absorb147 state147 absorbed147
    state148 (fun _ => rfl) words147 perm147

private def absorb148 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x5b 0x56 0xbe 0x4d 0x61 0x55 0x85 0x17)) 1 (by decide) (UInt64.ofBytes 0x55 0x85 0x1 0x1 0x60 0x1 0x80 0x82)) 2 (by decide) (UInt64.ofBytes 0x82 0x91 0x57 0xbe 0x4d 0x61 0x15 0x82)) 3 (by decide) (UInt64.ofBytes 0x4d 0x61 0x15 0x11 0x81 0x82 0x5b 0x1)) 4 (by decide) (UInt64.ofBytes 0x60 0x91 0x55 0x82 0x35 0x82 0x57 0xbe)) 5 (by decide) (UInt64.ofBytes 0x90 0x1 0x1 0x60 0x90 0x91 0x1 0x20)) 6 (by decide) (UInt64.ofBytes 0x82 0x80 0x5b 0x5b 0x56 0x3f 0x4e 0x61)) 7 (by decide) (UInt64.ofBytes 0x0 0x60 0x57 0xca 0x4d 0x61 0x15 0x11)) 8 (by decide) (UInt64.ofBytes 0x5b 0x4e 0x61 0x1 0x1 0x60 0x55 0x81)) 9 (by decide) (UInt64.ofBytes 0x3a 0x30 0x32 0x43 0x52 0x45 0xfe 0x56)) 10 (by decide) (UInt64.ofBytes 0x65 0x66 0x73 0x6e 0x61 0x72 0x74 0x20)) 11 (by decide) (UInt64.ofBytes 0x65 0x68 0x74 0x20 0x6f 0x74 0x20 0x72)) 12 (by decide) (UInt64.ofBytes 0x64 0x61 0x20 0x6f 0x72 0x65 0x7a 0x20)) 13 (by decide) (UInt64.ofBytes 0x75 0x61 0x50 0x73 0x73 0x65 0x72 0x64)) 14 (by decide) (UInt64.ofBytes 0x6e 0x20 0x3a 0x65 0x6c 0x62 0x61 0x73)) 15 (by decide) (UInt64.ofBytes 0x65 0x73 0x75 0x61 0x70 0x20 0x77 0x65)) 16 (by decide) (UInt64.ofBytes 0x65 0x68 0x74 0x20 0x73 0x69 0x20 0x72))

private def absorbed148 : Vector UInt64 25 :=
  #v[0x2ad8b8f23af7e70b, 0xfc0273c22863c581, 0xce02f2a7cb4e07db, 0x62125f8aedb95922, 0x5023e4d54b5e90df, 0x1e3ab52f7e9096e0, 0xaeeacb29f2f4f2ef, 0x8b1eeedbfeea5513, 0x63cbb5f5ac127d64, 0xb2a67384427286db, 0x5ad7586aed4052bc, 0x83f1e5e67e6e5350, 0xea320b19823c4efe, 0xfe0a338777c218c4, 0x9a5500418241396b, 0xbaa789b4418a88d1, 0x9d5497aa8160d891, 0x2a4b5cc37738cb16, 0xcb43f61301e1f8bd, 0x830c2f04307e6dad, 0x460c8d8fd2b81250, 0x1c9b4f23df8672d9, 0xd7937778aae92e5e, 0xb4e8d54f629bcb5d, 0x2eedc892a41ed6bc]

private theorem words148 : absorb148 state148 = absorbed148 := by
  decide +kernel

private def quarter148_1 : Vector UInt64 25 :=
  #v[0xb52783407a44ad19, 0x8f7db8de4ab52ed2, 0x669ddff44aed0810, 0x25c134164dac61b8, 0x4798bdd5635227d6, 0xfa45309d400f59f7, 0xaed354477c649471, 0xe0761e9dcd0166c3, 0x1cfd6d62fe8161ae, 0xd086cad19ac57e0f, 0xf6be8112e4f844a0, 0x55e17750c6999aec, 0x5021968e1a92daba, 0x364631f12d932d3a, 0x1b2e5a4a5c2ff650, 0x482b91af5517a6da, 0x18b2a69625a5eb3c, 0x24c957053ba62891, 0x6f66528862be1603, 0x2ba490f0b15bed7c, 0x1ab817de9812a6cf, 0x2b47c7a55a24a62a, 0x221da571dafef563, 0xc2b2efb6916b6e8f, 0x848fb13d6843157d]

private theorem rounds148_0 : sixRounds 0 (by decide) absorbed148 = quarter148_1 := by
  decide +kernel

private def quarter148_2 : Vector UInt64 25 :=
  #v[0xd0cf2c3011685b55, 0x200d001db6acc8a5, 0x6bd98dcbee35c73, 0xf6a656786dcebb6a, 0xf8ce0532693dc6e7, 0x10c928abfc0d8561, 0xfe3d017fa12d7126, 0x19599d415d744627, 0x730c0137172b4c7b, 0xd3cfa09a8a57ed39, 0xa1ff587ee63367fe, 0xa71c4335d97c9c11, 0xaa20bbd5a8a1f0c7, 0x6e12b6b3328521ec, 0x7bae73f5109625b0, 0x13b3ba80bfe3a5fb, 0xd36b20658fef2696, 0x5a69ed3174cfb46d, 0xe9a82cccc6e47235, 0x1b749ca9169fe28f, 0xd375177fc89f3ff0, 0x1c49082273a3820e, 0x17ab13aa556b96a1, 0xae164a9fe6fd893e, 0xbe1596c89d8c543e]

private theorem rounds148_1 : sixRounds 6 (by decide) quarter148_1 = quarter148_2 := by
  decide +kernel

private def quarter148_3 : Vector UInt64 25 :=
  #v[0xa5afba327b38b9d5, 0xfa80ab1f38515738, 0x26c7a4720441cd27, 0x5262d8b85c19af78, 0x2ec0c1d2955c6a4c, 0xa1e35506fb0ceb72, 0x65504a7f3e36f022, 0x5eb486c478605e06, 0x1338a2122cca6e60, 0x5c19a7c81bac60d0, 0x6dd5e2e7fb9282a0, 0x881053c92e221257, 0xa8855ce33a1c247, 0x3402b7591ff401b2, 0x59554992f9838a78, 0x9572da2be3d0c7f1, 0x27e62aea6befa0ee, 0x7f2941d19f8f0922, 0xf092b566c5435428, 0x1eca6e13d2733446, 0x42c28d45f8b452b4, 0x2a2fc035b4f91aed, 0x3d2971070e0f894e, 0xf00e6420df51d5b3, 0xd299532de72ca99a]

private theorem rounds148_2 : sixRounds 12 (by decide) quarter148_2 = quarter148_3 := by
  decide +kernel

private theorem rounds148_3 : sixRounds 18 (by decide) quarter148_3 = state149 := by
  decide +kernel

private theorem perm148 : KECCAK.f1600 absorbed148 = state149 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds148_0, rounds148_1, rounds148_2, rounds148_3]
  rfl

theorem block148 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes148 ++ tail) state148 =
      KECCAK.Bytes.run 0 tail state149 := by
  exact run_block_of_step bytes148 tail absorb148 state148 absorbed148
    state149 (fun _ => rfl) words148 perm148

private def absorb149 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x64 0x61 0x20 0x6f 0x72 0x65 0x7a 0x20)) 1 (by decide) (UInt64.ofBytes 0x61 0x69 0x46 0x73 0x73 0x65 0x72 0x64)) 2 (by decide) (UInt64.ofBytes 0x32 0x56 0x6e 0x65 0x6b 0x6f 0x54 0x74)) 3 (by decide) (UInt64.ofBytes 0x72 0x6f 0x68 0x74 0x75 0x61 0x20 0x3a)) 4 (by decide) (UInt64.ofBytes 0x20 0x6e 0x6f 0x69 0x74 0x61 0x7a 0x69)) 5 (by decide) (UInt64.ofBytes 0x79 0x20 0x74 0x6f 0x6e 0x20 0x73 0x69)) 6 (by decide) (UInt64.ofBytes 0x64 0x69 0x6c 0x61 0x76 0x20 0x74 0x65)) 7 (by decide) (UInt64.ofBytes 0x65 0x6b 0x6f 0x54 0x74 0x61 0x69 0x46)) 8 (by decide) (UInt64.ofBytes 0x20 0x6e 0x72 0x75 0x62 0x20 0x3a 0x6e)) 9 (by decide) (UInt64.ofBytes 0x6e 0x20 0x74 0x6e 0x75 0x6f 0x6d 0x61)) 10 (by decide) (UInt64.ofBytes 0x74 0x61 0x65 0x72 0x67 0x20 0x74 0x6f)) 11 (by decide) (UInt64.ofBytes 0x20 0x6e 0x61 0x68 0x74 0x20 0x72 0x65)) 12 (by decide) (UInt64.ofBytes 0x6b 0x6f 0x54 0x74 0x61 0x69 0x46 0x30)) 13 (by decide) (UInt64.ofBytes 0x74 0x6e 0x69 0x6d 0x20 0x3a 0x6e 0x65)) 14 (by decide) (UInt64.ofBytes 0x20 0x65 0x68 0x74 0x20 0x6f 0x74 0x20)) 15 (by decide) (UInt64.ofBytes 0x64 0x64 0x61 0x20 0x6f 0x72 0x65 0x7a)) 16 (by decide) (UInt64.ofBytes 0x65 0x52 0x43 0x45 0x73 0x73 0x65 0x72))

private def absorbed149 : Vector UInt64 25 :=
  #v[0x9baebd6eb20eb29, 0x18a233ad5e373c70, 0x8e9e1ffd556ba248, 0x841662aac98b2cee, 0xd54d97d568f8438, 0x990c1958c01b02b0, 0xeca3785134543b45, 0xe200265dee9e6b88, 0x37134cf5ad3aba60, 0x567689bf8b83c6e0, 0x9e13519c3e60451d, 0x3704d904dd33786c, 0x15c6688cfc094197, 0xd48a0594db69417e, 0x3790326a1bc490e1, 0x3df02c9be4167399, 0x8ba91ab879e3f054, 0x124fbe07aeab894f, 0x3862bbf2ed1404a2, 0xeededf5e5f7df05e, 0x668dbd1af0f9e415, 0xfc33b64d5a37fe2, 0xf858dbb9ebb6163e, 0x59e7fcebcecdcdfd, 0x84d3fe1c364afbea]

private theorem words149 : absorb149 state149 = absorbed149 := by
  decide +kernel

private def quarter149_1 : Vector UInt64 25 :=
  #v[0xe0b1c81c5ccbc695, 0xe1cc6b76a72629f2, 0x6c896c2ba2975af3, 0x71f6d0dd9c7df682, 0xbb114163702c5611, 0xe95c49433087e9b7, 0x6886420f2979985e, 0x957474d07f648166, 0xc01cce8c0726e889, 0xb1ecd1e2a1a55415, 0x8674dc3dcd9f1f90, 0x7cb800acf56a88ea, 0x4ca477cd229378da, 0x81299647ee9d09b4, 0x3148d7549bcc6069, 0x9d5d28fd74445b99, 0x238c23bd58a07d7c, 0x3ca08483fba71e5b, 0xf029d1ed1d022f5c, 0xbd37be94ec4e49ae, 0x78584502731b4f97, 0xa38ab203f6a3273f, 0x1bcbf8da821a1991, 0x2e93a6292988ec54, 0x98a465d9f71ac23e]

private theorem rounds149_0 : sixRounds 0 (by decide) absorbed149 = quarter149_1 := by
  decide +kernel

private def quarter149_2 : Vector UInt64 25 :=
  #v[0xb33915de89c46482, 0xa99dd9c371a4655c, 0xa94d81f0b8759dcf, 0x3a018bcc6707d8ba, 0x4445d42224ed46f1, 0x3239a6e94fa4f048, 0xb5e2cbc278bcb877, 0x593524ba2358cbf4, 0x4f5b7d1be09e086c, 0xe305d0502937dbff, 0x5cefbb73c8aa35f2, 0x294977f6bf56365b, 0xc435bf8a8627d9d3, 0xe53a1ffcd1489789, 0xa65b569654f1c7c, 0x81a6f1d9ed6c8d09, 0xf42d979aec87f671, 0x73baf1d46345b885, 0x89073cced5b958f3, 0xa58754c50cb19f45, 0x351c547d1f0f2a8d, 0x4cc4de1de2884a6d, 0x8202d154818ca191, 0x6bc326647eb923b1, 0xc4707fcd03903f6f]

private theorem rounds149_1 : sixRounds 6 (by decide) quarter149_1 = quarter149_2 := by
  decide +kernel

private def quarter149_3 : Vector UInt64 25 :=
  #v[0x73ae8950324e2084, 0x978a206c0ef59a62, 0x9ae67acac3b88176, 0x40cea8d7fe5fe376, 0xc9d0f464d29a2e0d, 0xb8652a6766eebae1, 0x9a188602e4fabf49, 0x37c7cb091d9efbec, 0x16880d7ddf1599f3, 0x224146751e8100db, 0xf85d0674d067788a, 0x4fd47c276ed3503b, 0x7f6e2c321b6899ca, 0x8d5225b1b76f41f2, 0xe1468675cd34e152, 0x40a6d5bef5b5df62, 0xf90329c10e3994e8, 0xe7eb9945c5fb9363, 0xf9930ee320276fb9, 0xfd29f0d311fe7bc3, 0xf230ed2c98792ba, 0x6e4d825d109d7a06, 0x110456b8fa1b3b7f, 0xfd192ec94e13a45d, 0x8ec17578e2c2f22d]

private theorem rounds149_2 : sixRounds 12 (by decide) quarter149_2 = quarter149_3 := by
  decide +kernel

private theorem rounds149_3 : sixRounds 18 (by decide) quarter149_3 = state150 := by
  decide +kernel

private theorem perm149 : KECCAK.f1600 absorbed149 = state150 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds149_0, rounds149_1, rounds149_2, rounds149_3]
  rfl

theorem block149 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes149 ++ tail) state149 =
      KECCAK.Bytes.run 0 tail state150 := by
  exact run_block_of_step bytes149 tail absorb149 state149 absorbed149
    state150 (fun _ => rfl) words149 perm149

end Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
