import Blanc.Lift.Usdc.ImplV2_1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb018 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x80 0x4 0x60 0xd 0x4 0x61 0x5b 0x56)) 1 (by decide) (UInt64.ofBytes 0x61 0x15 0x10 0x81 0x20 0x60 0x3 0x36)) 2 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x80 0x0 0x60 0x57 0x2d 0x9)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x35 0x50)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xd 0x4 0x61 0x5b 0x56 0xc0 0x27 0x61)) 7 (by decide) (UInt64.ofBytes 0x52 0x4 0x61 0x5b 0x56 0xe8 0x27 0x61)) 8 (by decide) (UInt64.ofBytes 0xd 0x4 0x61 0x5b 0x56 0xc 0x28 0x61)) 9 (by decide) (UInt64.ofBytes 0x81 0x20 0x60 0x3 0x36 0x80 0x4 0x60)) 10 (by decide) (UInt64.ofBytes 0x0 0x60 0x57 0x70 0x9 0x61 0x15 0x10)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x35 0x50 0x5b 0xfd 0x80)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x5b 0x56 0xe6 0x28 0x61 0x16 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x5b 0x56 0xe 0x29 0x61 0x4a 0x7 0x61)) 16 (by decide) (UInt64.ofBytes 0x5b 0x56 0x2a 0x29 0x61 0x43 0x3 0x61))

private def absorbed018 : Vector UInt64 25 :=
  #v[0xa72c0b791b819e9, 0x643db360b6eee352, 0x84d2d81cef4c999c, 0x46ff07e898ddd956, 0xa06dbea3cfd6db6b, 0xc3524d9085acc954, 0x819d5236b63a3246, 0xad127943f600d458, 0xc725235b4a7f90d6, 0x524f78f9888f486f, 0x3c2e4633c2eda26, 0x99f2a7af763f6475, 0xafe8e099dec61a88, 0xa97b0e7bf6eb7579, 0x4d93bc624b9992c5, 0x8ab7ede7033d4bf9, 0xdac5024c7e7e4be1, 0x4d5aa41eed69832c, 0x7a36a8529bdbdbf, 0x6e5fce5d9617368e, 0x6efdd363b861364a, 0x85f9326c67cb8c84, 0x8898d6c68d0fb748, 0x503cc90042ae20be, 0x41f5fa65ce9f82f4]

private theorem words018 : absorb018 state018 = absorbed018 := by
  decide +kernel

private def quarter018_1 : Vector UInt64 25 :=
  #v[0x59968a9a329bb7ad, 0xc4cc5983f0c1bc8f, 0x300b587f148b4076, 0xb3be603d388c9e52, 0xf3abc0272166094f, 0xa05e4d7c2ccebf14, 0x18d62b4aa98c59ee, 0xbe148b1fb2193ae8, 0x77a203936d56f6ee, 0xb2180a53738f656e, 0x3b389455508ad6e0, 0xdfa26ee97a40fcc6, 0x5880088419da15d7, 0x68614d9fe897d63c, 0x65f6c5fef733926b, 0x95b117baff539120, 0x5fb937f3dfb5ec19, 0xe15c04481698d897, 0x400a6e694c88292f, 0x14836dbe36769cb, 0x1a5ee489de1e3c22, 0xa56812d3279a045a, 0x2fac358501223137, 0x7e31643836eddd06, 0x5c8ef68e50eed97a]

private theorem rounds018_0 : sixRounds 0 (by decide) absorbed018 = quarter018_1 := by
  decide +kernel

private def quarter018_2 : Vector UInt64 25 :=
  #v[0x5972c1db0b6f54d8, 0x9cda65752195701f, 0x1e329536bfb05d44, 0xa216af2d633b65d4, 0xc0a7d41f82b22990, 0x648cece2a95d9b0f, 0x89029048a671e1e4, 0x2154b0ed5d545a6f, 0x8fd156aff0f37ac1, 0x9f89ef5adf872bd1, 0x7923fc4519b8296f, 0x1c3eaaf39f12ccbd, 0xd72934dd66871d06, 0x89e6e56abb7306b7, 0x5350b3fc05d15528, 0x72fe0cd1bab0888d, 0x1054a431ebc79440, 0xae9957e63b18e803, 0xdffd038d51479fb9, 0xb2a96190887a521d, 0x22ad111a05db6816, 0x71ffa1dc1080e3fa, 0xeebf7bc1e8b9a5a2, 0xd03a79434daa5c00, 0x6c7b8e24e001f16e]

private theorem rounds018_1 : sixRounds 6 (by decide) quarter018_1 = quarter018_2 := by
  decide +kernel

private def quarter018_3 : Vector UInt64 25 :=
  #v[0x37f5d5a00e84184e, 0x1b7081fff56f453, 0x33615f7f2429a218, 0xf4d5e4fcc10c4f1e, 0xca6a2e97c4c1ca5c, 0xc790e5861c7a070c, 0xe7c7d0e4babd295f, 0xceca8835879d2e38, 0xdabc3fce060f5b14, 0x4f667ddf6104932, 0xf37ef178c69baa66, 0xb5d76b78ecd8fa99, 0x794110bb8147785e, 0xc84747fca65ad61c, 0x625bea1f3ed75dca, 0xdaa54bbbf5e6d1bb, 0x40236ba73ed8eae6, 0x6544f1a5caa6b082, 0x313d7ca7fd5cecef, 0xa32a53bbb7da6294, 0x8fdbeee3b5d3a4d8, 0x7131728ba25fdaca, 0xfcf1a0dc6aa0d11, 0xea69f552e40a269, 0x5e8822ee811161e]

private theorem rounds018_2 : sixRounds 12 (by decide) quarter018_2 = quarter018_3 := by
  decide +kernel

private theorem rounds018_3 : sixRounds 18 (by decide) quarter018_3 = state019 := by
  decide +kernel

private theorem perm018 : KECCAK.f1600 absorbed018 = state019 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds018_0, rounds018_1, rounds018_2, rounds018_3]
  rfl

theorem block018 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes018 ++ tail) state018 =
      KECCAK.Bytes.run 0 tail state019 := by
  exact run_block_of_step bytes018 tail absorb018 state018 absorbed018
    state019 (fun _ => rfl) words018 perm018

private def absorb019 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x5b 0x56 0xa3 0x29 0x61 0x4a 0x7 0x61)) 1 (by decide) (UInt64.ofBytes 0x5b 0x56 0xbf 0x29 0x61 0xd 0x4 0x61)) 2 (by decide) (UInt64.ofBytes 0x3 0x36 0x80 0x4 0x60 0xf1 0x3 0x61)) 3 (by decide) (UInt64.ofBytes 0xc3 0x9 0x61 0x15 0x10 0x81 0x40 0x60)) 4 (by decide) (UInt64.ofBytes 0x73 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x90 0x16 0x35 0x81 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x56 0xe3 0x29 0x61 0x35 0x1 0x20 0x60)) 9 (by decide) (UInt64.ofBytes 0x36 0x80 0x4 0x60 0xf1 0x3 0x61 0x5b)) 10 (by decide) (UInt64.ofBytes 0x9 0x61 0x15 0x10 0x81 0x40 0x60 0x3)) 11 (by decide) (UInt64.ofBytes 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57 0xfc)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x16 0x35 0x81 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x65 0x2b 0x61 0x35 0x1 0x20 0x60 0x90)) 16 (by decide) (UInt64.ofBytes 0x80 0x4 0x60 0x52 0x4 0x61 0x5b 0x56))

private def absorbed019 : Vector UInt64 25 :=
  #v[0x944c7d5dd6efeef3, 0x409f323f44a68866, 0x8b3e17b411c791b3, 0x14dc5c25df51c961, 0x5414010581956e59, 0x3fdf16b9bd0824cf, 0xf58953351e1bbe78, 0x64f601516e317845, 0x82ec976297a8e04c, 0x6c78f11b69a11180, 0x5ea244933c764416, 0xba2c13151887e0fa, 0x1d549934cdcf4da1, 0x7b4d390c22a1c50f, 0x5aba8ee71413a006, 0x8481b802837f8066, 0x4ac2f90705e61c20, 0xac235c2104700488, 0xf43f30f21bee8a4a, 0x6805a87fa3d9ebc2, 0xee1c3d95c2f5bd98, 0x49aa24b1bd5cdf4f, 0xb41c8ab80d737854, 0xadd46d0c6178f9df, 0x1bc9d1c5aaa5ee9d]

private theorem words019 : absorb019 state019 = absorbed019 := by
  decide +kernel

private def quarter019_1 : Vector UInt64 25 :=
  #v[0x4274104b6f25e40, 0x1dd569411e8f19f9, 0x198f31d36ef1f875, 0xf59c8a16b0a3a0be, 0xf072f681421f40ab, 0xab7f1bcc876e9742, 0xd51ae03a7f5c64db, 0x20edacc1a151a6d3, 0x660e00e13ca83614, 0xb5b9ddbf207f9fa1, 0xe84c51335b54afa0, 0xa407cea009afb466, 0x31edb5ae28b27be5, 0x16ef074ff1c12254, 0xe241006217407c78, 0xd641f66149c8dc2d, 0x902acd912a2639aa, 0x4c54ab96d773f39b, 0x9d92baed633f5cea, 0xa7a05d3f6f2dfdd5, 0x4b604a1bb7cdd9dc, 0xb34fd8c0a3451165, 0x1f301c31a93c06d6, 0x7b3b68c4edddd2d2, 0xb29861993de140cf]

private theorem rounds019_0 : sixRounds 0 (by decide) absorbed019 = quarter019_1 := by
  decide +kernel

private def quarter019_2 : Vector UInt64 25 :=
  #v[0xbb0ae5c5058f73f0, 0x6c365ad48883e3fc, 0x305079b5b23985d0, 0x5e5b2b59d0e23295, 0x40a420f7d32ae21, 0x70fbfe40df1b692f, 0x282be9ba2e918478, 0xad045f6be056d096, 0x71fff00972a9dacd, 0xf667de287ac230d2, 0x4085755d3f45a9e4, 0x2afaa3330dcf386d, 0xf589402f82f6128f, 0xf8ca51cbb5cb772e, 0x55fcce8975066102, 0x9aa8c787e2a5fbf5, 0x81d247a6833b1edb, 0x3b579f1f42fb1991, 0x37bc27bf580eb33f, 0x7baa6b7b99829b1d, 0x870b725cd58b5bc1, 0x20d86e0e4b1f922d, 0xb6e86b40b469dd7c, 0xa157fd211acf21bb, 0x23a8ff192055f045]

private theorem rounds019_1 : sixRounds 6 (by decide) quarter019_1 = quarter019_2 := by
  decide +kernel

private def quarter019_3 : Vector UInt64 25 :=
  #v[0xdd5e66d6b00f29ba, 0xf1bc84da78d49dfd, 0x38bd46b860443548, 0x99c0885244e42bf0, 0xab3c4437b930d876, 0xf7a60a1ab74a33b2, 0x398d9f2a2fc3ccf3, 0x440f806029f95a56, 0xf3d54570d8746a2, 0x2991af78a9d7ba74, 0xce5833e45ceb77c8, 0x7a7e88d306613dc1, 0x1cc8df02301975d8, 0x45297f53b95ea804, 0xb75fcdca805c8471, 0x2cb681d64c078589, 0x4ed4a32133aa8f41, 0xb003b00bb48de55a, 0x3239525cf52deb84, 0xc1306609ae46b9de, 0xfaff9ae25d98bb2d, 0x6b843ae2ff77d49a, 0x8e213cd9bb1030a9, 0xe8508de568719091, 0x59909608f2564824]

private theorem rounds019_2 : sixRounds 12 (by decide) quarter019_2 = quarter019_3 := by
  decide +kernel

private theorem rounds019_3 : sixRounds 18 (by decide) quarter019_3 = state020 := by
  decide +kernel

private theorem perm019 : KECCAK.f1600 absorbed019 = state020 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds019_0, rounds019_1, rounds019_2, rounds019_3]
  rfl

theorem block019 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes019 ++ tail) state019 =
      KECCAK.Bytes.run 0 tail state020 := by
  exact run_block_of_step bytes019 tail absorb019 state019 absorbed019
    state020 (fun _ => rfl) words019 perm019

private def absorb020 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x61 0x15 0x10 0x81 0x20 0x60 0x3 0x36)) 1 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x80 0x0 0x60 0x57 0x35 0xa)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x35 0x50)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xf1 0x3 0x61 0x5b 0x56 0xe7 0x2c 0x61)) 6 (by decide) (UInt64.ofBytes 0x81 0x20 0x60 0x3 0x36 0x80 0x4 0x60)) 7 (by decide) (UInt64.ofBytes 0x0 0x60 0x57 0x68 0xa 0x61 0x15 0x10)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x35 0x50 0x5b 0xfd 0x80)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x5b 0x56 0x4e 0x2e 0x61 0x16 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x3 0x36 0x80 0x4 0x60 0x52 0x4 0x61)) 13 (by decide) (UInt64.ofBytes 0x9b 0xa 0x61 0x15 0x10 0x81 0x20 0x60)) 14 (by decide) (UInt64.ofBytes 0x35 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed020 : Vector UInt64 25 :=
  #v[0x2113d138617e9a89, 0x11a6db45d56d615, 0xfd3c40250d4122d0, 0x2151569fb36add8b, 0xe812d44e4a8bfefd, 0xa9ae25109ed00287, 0x84dd1445419b9d61, 0xfe54428cdb2734ae, 0xb2ea6b0bd0174e78, 0xa7f6fc6ba625b98e, 0xb8cd1973b26a803d, 0xa0b65e5870dcf137, 0x34f686ad588ba74a, 0xa04f80b8bf6ec94f, 0x9bbcf51a828d34c0, 0xc110fd0d6a6a2d60, 0x439b902ff23e749d, 0x3223270235c36b17, 0xddf07e28063b14e6, 0xe2feb02e403c6d24, 0xa50a85b48ca509bd, 0x75f6e04430f47b94, 0x3af453fa260f738f, 0xc6cd9f5b0b90e07b, 0x3fd133baf8ffe5bb]

private theorem words020 : absorb020 state020 = absorbed020 := by
  decide +kernel

private def quarter020_1 : Vector UInt64 25 :=
  #v[0x25d86e7dc001d3e1, 0x940fb92c7aec9b50, 0x242414c75f505ff4, 0x709fce27310a6893, 0x1e4cfd1c34523dbe, 0xc33274ec949997ee, 0x99952729d1a20767, 0x903f6a6b697d90fa, 0x9a3b93e021cc3890, 0x800a3aa25aaf6f42, 0xed52cc04cf7a3557, 0xf775623eb7542f57, 0x1e93b898e38eb053, 0xe8c1e1da6c589eec, 0x283ad6b139801461, 0xc38432d99ca98286, 0x74976e1c8da3c5d1, 0xe1bcd8edca3c8b8c, 0x70ac1fdb45c1095b, 0x28b814eab9c6e175, 0x4f5d16d9b260e7d, 0x114f77ebe89d5512, 0xb710f3dcade0a54e, 0x124cd6e5d68bcd26, 0xfda203dd15b622a3]

private theorem rounds020_0 : sixRounds 0 (by decide) absorbed020 = quarter020_1 := by
  decide +kernel

private def quarter020_2 : Vector UInt64 25 :=
  #v[0x49c93bb4ef1746df, 0x6995666b4527df86, 0xecc03e57c8f786a3, 0xab4692d2e214bd7e, 0x4ba884218fa5c77c, 0xb1a65ba5fcf44e29, 0x1147d5a58762ecc8, 0x2d186f2a75bb02f3, 0xbb5cdcae053b15a5, 0x2ea01a3c0e88d2b0, 0x436be2268ef7fe29, 0x810079796c48c64c, 0xe8c8a935446614a1, 0xe49325fab112ed58, 0xc40b2d5d3433d97b, 0x37836f682b30ae78, 0xf9c32245aff0bbd6, 0xcdb9839143983a22, 0xbe59e8277fd367fb, 0x27fc8ab8fed1e324, 0x778ff4e13ce3c071, 0x5a2d85e4eb49abe4, 0xa8a02cf159bd8c2a, 0x858337e43181c718, 0xd1d80e58bb067249]

private theorem rounds020_1 : sixRounds 6 (by decide) quarter020_1 = quarter020_2 := by
  decide +kernel

private def quarter020_3 : Vector UInt64 25 :=
  #v[0x7b750b8463738e2c, 0x24d011e0bc8502de, 0x7e37269ab2c01afe, 0xd2b47dc22cc8dd0d, 0xc3d2ea26a4d8ec4e, 0x7f67673a77e752a1, 0x8036cec15b4b5793, 0xa6bf02986bd027ca, 0x6dcb4e210c4649b6, 0xd5f1b7fedcfe190d, 0xbd9ffd8d4e6b547a, 0x9071e4ecbf894755, 0x7a851a121810f1d4, 0xe2f182e8804d68c, 0x5897d8dc55323344, 0x9c0fcbd3e8f49710, 0x30c510ca14a0cdd6, 0x95de97792719e276, 0x5fbced2c757ca809, 0x4ac18df516ebcdb, 0x709b0bab1c9c9b9e, 0x4ac8398d790ecfd7, 0x463c34f55eac8e7b, 0x50511c629bf383f1, 0xf005e81f53f7c8a0]

private theorem rounds020_2 : sixRounds 12 (by decide) quarter020_2 = quarter020_3 := by
  decide +kernel

private theorem rounds020_3 : sixRounds 18 (by decide) quarter020_3 = state021 := by
  decide +kernel

private theorem perm020 : KECCAK.f1600 absorbed020 = state021 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds020_0, rounds020_1, rounds020_2, rounds020_3]
  rfl

theorem block020 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes020 ++ tail) state020 =
      KECCAK.Bytes.run 0 tail state021 := by
  exact run_block_of_step bytes020 tail absorb020 state020 absorbed020
    state021 (fun _ => rfl) words020 perm020

private def absorb021 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x2e 0x61 0x16 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x4 0x60 0x52 0x4 0x61 0x5b 0x56 0x79)) 2 (by decide) (UInt64.ofBytes 0x15 0x10 0x81 0x60 0x60 0x3 0x36 0x80)) 3 (by decide) (UInt64.ofBytes 0xfd 0x80 0x0 0x60 0x57 0xce 0xa 0x61)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x50 0x5b)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x81 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x1 0x81 0x20 0x60 0x91 0x16 0x81 0x35)) 8 (by decide) (UInt64.ofBytes 0x1 0x40 0x60 0x90 0x16 0x91 0x90 0x35)) 9 (by decide) (UInt64.ofBytes 0x7 0x61 0x5b 0x56 0xe0 0x2f 0x61 0x35)) 10 (by decide) (UInt64.ofBytes 0x4 0x61 0x5b 0x56 0x76 0x30 0x61 0x4a)) 11 (by decide) (UInt64.ofBytes 0xe0 0x60 0x3 0x36 0x80 0x4 0x60 0x52)) 12 (by decide) (UInt64.ofBytes 0x60 0x57 0x19 0xb 0x61 0x15 0x10 0x81)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x50 0x5b 0xfd 0x80 0x0)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x60 0x91 0x16 0x81 0x35 0x81 0xff 0xff))

private def absorbed021 : Vector UInt64 25 :=
  #v[0x9e036959bc8f8371, 0x3fa892cbf9b363e9, 0x79957e53036ad778, 0x9a1ab500e5703d4, 0xeb476cfed3f490df, 0x3f903849ef9aff81, 0x6972f95de3a8ad3c, 0x5a4cb93ed671459f, 0xd752cd34cae1e30b, 0x7d66b8a6c57e5511, 0xaa6d6fc3ffec3b5, 0xd671503e04bdb127, 0x808fe3d1ea7c562b, 0xe86f429bfa734afa, 0xfa48600cc92c1839, 0x20f4e6d1c027600f, 0xc1fa4df3d508571b, 0x2e21249dbf19a76e, 0x212fb9d50c01bebd, 0x1662b1043b183bba, 0x71b1ca4f3435069e, 0x98a4af5894a1aa02, 0x4e20da76a8eeb1e5, 0x18d7c360339e9973, 0xf841704713c4f2b6]

private theorem words021 : absorb021 state021 = absorbed021 := by
  decide +kernel

private def quarter021_1 : Vector UInt64 25 :=
  #v[0x1de486a21aebd8f3, 0xdf6d47fa12557a91, 0xf04375746466bc0b, 0x471b3b85c29a6841, 0xd693507aa6d9c93, 0xcc2bf331bd2bebea, 0x6261e6842f7c331d, 0x6f152dd242c90908, 0xc0bf51063cbd48ab, 0xb2e7a30d803b4b81, 0xdf4cd858e1b94190, 0x7211e2281b9e8d51, 0x2abbc0324356140, 0x247907acadfd6879, 0x3203b376387f43cc, 0x4514fa5a9e3fdf5f, 0x216dfaf4f97b21a5, 0xe0ba5744d95c8ba0, 0x189ca0e461a3c731, 0x71aa09053ed132e, 0x8bb5095d12f93b31, 0xd2152d9fdbf2f2a4, 0xbebdab46d07cf4e, 0x6e96b402a24d0c1f, 0xbfea7c14a3996de7]

private theorem rounds021_0 : sixRounds 0 (by decide) absorbed021 = quarter021_1 := by
  decide +kernel

private def quarter021_2 : Vector UInt64 25 :=
  #v[0x112df01cbfcaffcf, 0x5203fc9834294d13, 0xe18c944db9d6b29, 0xc1feb567b135a4f0, 0x5fb446af081d1a46, 0xf03b282638a44e5f, 0x23d4bd5a254bad50, 0x9e6e5d725e8dfd60, 0xd33210c8e5a362d5, 0x995676d4f618b4b, 0x2f2c52cf48189ea0, 0x7781d75905f5530d, 0x62260a80e7f329c3, 0xbcacc5008fc61d85, 0x8e21b4d2df028555, 0x1e32bea23e0e75a2, 0xce0605099e2c78e5, 0xd3b9f2cd61da03d0, 0xdf1000ee3a68180, 0xbba13479b2694b8a, 0xaf069f35dac0a5d4, 0x5c557ae681e5199f, 0x83f8aa8f64a073e6, 0x8d96b925aca62904, 0x8f22fcdd12570aec]

private theorem rounds021_1 : sixRounds 6 (by decide) quarter021_1 = quarter021_2 := by
  decide +kernel

private def quarter021_3 : Vector UInt64 25 :=
  #v[0x6012850cf12a7ef2, 0x7be84e3a77eb3227, 0xe93e76f35f3373f4, 0x5c2705ab99c90ee4, 0xb7f56ea433c9e18, 0xb6234387cf7d7252, 0x112bfe044da1d221, 0x4bdc748dafb4286, 0xb87361a59b961b7b, 0x623025807b777fd3, 0x9cbae5f319b2a494, 0xa15b6916f7c8fdfa, 0x6f07d37cb0444d02, 0xa02506f1e8500c2d, 0x47008ea8a28f2bc7, 0x2f1c53ab245df8f4, 0xcc3edfec18b60437, 0x3ea1593b4afce1b2, 0x22b67bfda1160e7d, 0xd6f140ad38732993, 0x9ad4b202a09d5d36, 0xd07d2f347994db0d, 0x54ab77f2bad55a2e, 0xda84f80468aa7c37, 0xb90c64dfa16d8b5a]

private theorem rounds021_2 : sixRounds 12 (by decide) quarter021_2 = quarter021_3 := by
  decide +kernel

private theorem rounds021_3 : sixRounds 18 (by decide) quarter021_3 = state022 := by
  decide +kernel

private theorem perm021 : KECCAK.f1600 absorbed021 = state022 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds021_0, rounds021_1, rounds021_2, rounds021_3]
  rfl

theorem block021 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes021 ++ tail) state021 =
      KECCAK.Bytes.run 0 tail state022 := by
  exact run_block_of_step bytes021 tail absorb021 state021 absorbed021
    state022 (fun _ => rfl) words021 perm021

private def absorb022 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x90 0x16 0x91 0x90 0x35 0x1 0x81 0x20)) 1 (by decide) (UInt64.ofBytes 0x60 0x60 0x90 0x35 0x1 0x81 0x40 0x60)) 2 (by decide) (UInt64.ofBytes 0x80 0x60 0xff 0x60 0x90 0x35 0x1 0x81)) 3 (by decide) (UInt64.ofBytes 0x81 0xa0 0x60 0x90 0x16 0x35 0x1 0x82)) 4 (by decide) (UInt64.ofBytes 0x61 0x35 0x1 0xc0 0x60 0x90 0x35 0x1)) 5 (by decide) (UInt64.ofBytes 0x60 0x52 0x4 0x61 0x5b 0x56 0x92 0x30)) 6 (by decide) (UInt64.ofBytes 0x10 0x81 0x20 0x60 0x3 0x36 0x80 0x4)) 7 (by decide) (UInt64.ofBytes 0x80 0x0 0x60 0x57 0x77 0xb 0x61 0x15)) 8 (by decide) (UInt64.ofBytes 0x81 0x20 0x60 0x90 0x1 0x81 0x5b 0xfd)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x1 0x64 0x35 0x81 0x1)) 10 (by decide) (UInt64.ofBytes 0x57 0x92 0xb 0x61 0x15 0x11 0x81 0x0)) 11 (by decide) (UInt64.ofBytes 0x83 0x1 0x82 0x5b 0xfd 0x80 0x0 0x60)) 12 (by decide) (UInt64.ofBytes 0xb 0x61 0x15 0x11 0x1 0x82 0x20 0x60)) 13 (by decide) (UInt64.ofBytes 0x80 0x5b 0xfd 0x80 0x0 0x60 0x57 0xa4)) 14 (by decide) (UInt64.ofBytes 0x60 0x84 0x91 0x1 0x20 0x60 0x90 0x35)) 15 (by decide) (UInt64.ofBytes 0x1 0x64 0x11 0x1 0x84 0x2 0x83 0x1)) 16 (by decide) (UInt64.ofBytes 0x15 0x17 0x11 0x83 0x0 0x0 0x0 0x0))

private def absorbed022 : Vector UInt64 25 :=
  #v[0x89cc6889c41af71e, 0x61099d89a0a88a13, 0xbb322a883b95b376, 0x3e95bcb8b53e4503, 0x17ad014d3075eb0b, 0xb58ec356cb349743, 0xfcbe38695064076c, 0xf25d50fb385c0abe, 0x37ab7408b9d3bf2f, 0xe8b2adf4e46827f7, 0x50b055ef5d8e268a, 0x972326ad0bbedfcc, 0x73f526121beb0261, 0xf29a3a3f4673e4b4, 0x62539c05a9fa3696, 0x369d2ce3876afdf0, 0xe0a92ab345be149a, 0xaf18813bc759765e, 0x7d5a390603c603a, 0x321c6356679d356d, 0x72611116c7a961bd, 0x323c73ba9e5af99b, 0xcd3f5b5697913c82, 0xc8a83ebc909984d7, 0x8b403c1ea67a87b3]

private theorem words022 : absorb022 state022 = absorbed022 := by
  decide +kernel

private def quarter022_1 : Vector UInt64 25 :=
  #v[0x27f02680329be241, 0x46bca7f202862d06, 0xd69f2f02d6ef407b, 0xec5960491b4076c0, 0x5c9ec7c26d8659e7, 0x12a2c72e8e0ed9f5, 0xc86432b4336b4e4b, 0x76d38081aacd880f, 0x7f128c83ebdd6cb9, 0x3c45feb35c89ac1f, 0x90f9213e3b03dc3e, 0x73ecbaee2f928631, 0x25f94388db970a71, 0xea122104a0c31c41, 0xeb69bd6487f8a494, 0xba1b5f50bae7762d, 0x4ebedb03b4b34717, 0xe0aca87a596ee5ec, 0x952cbdade99e5da9, 0x37bacf5c028b4f59, 0xb18b51beda34a06f, 0x8ebb59b17b863520, 0x5e3b5282edc81a92, 0x61e1f9771b846bf3, 0x41089484a26d6b67]

private theorem rounds022_0 : sixRounds 0 (by decide) absorbed022 = quarter022_1 := by
  decide +kernel

private def quarter022_2 : Vector UInt64 25 :=
  #v[0x5e61a7c034607d0a, 0xac311de7add087f5, 0xaf4913e1c949ce1d, 0xe228db6724ddadac, 0x89bd05a028f15e28, 0x6942eeec6df5fe76, 0x1e5b2cc6e6000a0b, 0xbe44a4346b946de8, 0x9a906aa25377f09a, 0xb34fe839ca831fc3, 0x1a64d53fc9de70cd, 0xcf29f7ffa4161c1d, 0xef12998981a8f023, 0x4fb85370a7767735, 0xe7f63ef9cbd676b0, 0xb005a97f9602d8ac, 0x8e4e5d52be047815, 0xfcba7ce1101aed60, 0xb84ac6eb7db9d917, 0xfe15592e735fcf2b, 0xfac56f3d7daca287, 0x3dfb45e9371371a2, 0x8a63d6e846cc7b9f, 0xee44fa7980758a2c, 0x2cdbb93fb1ecea]

private theorem rounds022_1 : sixRounds 6 (by decide) quarter022_1 = quarter022_2 := by
  decide +kernel

private def quarter022_3 : Vector UInt64 25 :=
  #v[0x1b7fdab348dc38d2, 0xcc9942d0d4f43c4a, 0x1c3dfb22ef73d5c6, 0xc3c7e12cedab692c, 0xac8a0383741f5ee4, 0xbe59b5f6c46b6e37, 0x1e3b0ad24544d922, 0xbb7de5db58758032, 0x73447dae7d57b1a8, 0xa45a698d96cf93db, 0x7bfa0754d6193c99, 0x6ccccae8755cbad4, 0xfe142f10eeb437d2, 0x408d0bd950ed088, 0x265e071c7110bf35, 0x7f499273d6a945fd, 0x6d405e4f717d18ae, 0x1ffbc688aeb2b0aa, 0x897e4c469894d40a, 0x8dec2f4c2f5cefd8, 0xd536091021601853, 0x2a37375c4a695b27, 0xbe2028be956780fc, 0x562019ed13698a10, 0xac6db1572568339b]

private theorem rounds022_2 : sixRounds 12 (by decide) quarter022_2 = quarter022_3 := by
  decide +kernel

private theorem rounds022_3 : sixRounds 18 (by decide) quarter022_3 = state023 := by
  decide +kernel

private theorem perm022 : KECCAK.f1600 absorbed022 = state023 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds022_0, rounds022_1, rounds022_2, rounds022_3]
  rfl

theorem block022 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes022 ++ tail) state022 =
      KECCAK.Bytes.run 0 tail state023 := by
  exact run_block_of_step bytes022 tail absorb022 state022 absorbed022
    state023 (fun _ => rfl) words022 perm022

private def absorb023 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xfd 0x80 0x0 0x60 0x57 0xc6 0xb 0x61)) 1 (by decide) (UInt64.ofBytes 0x61 0x50 0x90 0x50 0x92 0x90 0x50 0x5b)) 2 (by decide) (UInt64.ofBytes 0x61 0xd 0x4 0x61 0x5b 0x56 0x38 0x32)) 3 (by decide) (UInt64.ofBytes 0x60 0xd 0x4 0x61 0x5b 0x56 0x21 0x33)) 4 (by decide) (UInt64.ofBytes 0x10 0x81 0x40 0x60 0x3 0x36 0x80 0x4)) 5 (by decide) (UInt64.ofBytes 0x80 0x0 0x60 0x57 0xef 0xb 0x61 0x15)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x50 0x5b 0xfd)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x91 0x16 0x81 0x35 0x81)) 10 (by decide) (UInt64.ofBytes 0x61 0x5b 0x56 0x45 0x33 0x61 0x16 0x35)) 11 (by decide) (UInt64.ofBytes 0x61 0x3 0x36 0x80 0x4 0x60 0x52 0x4)) 12 (by decide) (UInt64.ofBytes 0x2b 0xc 0x61 0x15 0x10 0x81 0x20 0x1)) 13 (by decide) (UInt64.ofBytes 0x73 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x16 0x81 0x35 0x81 0xff 0xff 0xff 0xff))

private def absorbed023 : Vector UInt64 25 :=
  #v[0xae641add974446dc, 0xabfff50bc0baa934, 0xb0d3e122c1fbaffe, 0xedae44fb2b2e13c5, 0x61384ce3c5ff43e1, 0xa586102be6362301, 0x83086992697bd67c, 0x5a6d8c05e8ea02cd, 0x2986c4cf2d82d1a5, 0xf74468a961c08a53, 0x1760b0ddf027b771, 0xd1409874ccf3f86f, 0xcf694527b8a51179, 0x4388fbfe6296b474, 0x871b3324b298387c, 0x3db13238d1924a54, 0xedd5efb9feb8fea2, 0xfdf3c8280cf44cf0, 0xb5fa4da7282b8c49, 0x65a1ef8eb3decf0a, 0x886afed4bc392a65, 0x9c88ce009f7ee245, 0x391993e166a62ff8, 0x73e48911260bf21, 0x548b556d630f52c1]

private theorem words023 : absorb023 state023 = absorbed023 := by
  decide +kernel

private def quarter023_1 : Vector UInt64 25 :=
  #v[0x2917902637641e3a, 0x12d45b37448e7894, 0x6b5be160f9eea637, 0x30972fa4c81992c7, 0xc4a632ccc4361b7, 0xf420bddc13eb100f, 0x49b58b453a2525b0, 0x7bc9fcc33fcf25e6, 0xa65739e4572a3dd, 0xdc4cd7a4fdf08ae0, 0x9c81208093826b1f, 0xce78cfc325712b0e, 0x88c0b5b76ecfc8dd, 0x49d4f18400d62a43, 0xb2fbaaedd8befedb, 0x1008e8d01161865, 0x676924a5b3226521, 0x419f723d4cc680a2, 0x13c158a4f7940356, 0x877f6acb4943255e, 0xa867100add340627, 0xc24a242c42cc083e, 0x7e644fc3adcb8a19, 0xc2f422196698a575, 0x48bc8616e15894e0]

private theorem rounds023_0 : sixRounds 0 (by decide) absorbed023 = quarter023_1 := by
  decide +kernel

private def quarter023_2 : Vector UInt64 25 :=
  #v[0x873e55191e64145a, 0xd0ca7f459d9be0e, 0x2df53832f918605d, 0x11c1025cb10d18bd, 0x7274648745a8d792, 0xe7c02f4e0e4b28cf, 0x592f951677fae4f9, 0x6029338e327c3acc, 0xa287b5a4370fa6ce, 0x144cb3d54842df84, 0x71e1bc5ff3ece33, 0x456fb9ec62d3216, 0x69c340933a7ab72, 0xcbe13da4e2c3269a, 0xb059f4dfc23e1338, 0x49fff636b40e5173, 0x46f9904f8e35e8e4, 0xd8cb05f711f0e019, 0x1a33a4badeaa0423, 0xecbb8c81799f3a7d, 0x9172137e89c0ff77, 0x5064f8bf20e01a29, 0xd71e7b25b6a6d6e1, 0x59bc6d7890d1473e, 0x1106960e2615c0c7]

private theorem rounds023_1 : sixRounds 6 (by decide) quarter023_1 = quarter023_2 := by
  decide +kernel

private def quarter023_3 : Vector UInt64 25 :=
  #v[0x2228f52c97319a87, 0x71f6c7c873477f95, 0x8252c4046d053cae, 0x52babd204df8634a, 0x266c5d428d24379f, 0x7107971bf9db3e49, 0xb274e284827f2a39, 0xf71ccc6a17c960fe, 0xb6b52d582ce22be5, 0x7ff20e906acded01, 0x91fc6fc7de40beeb, 0x8314fb6cc8a1d0d0, 0xab75e6327aae8319, 0x35370ee6ffb12c9, 0x3fee29b0546a640b, 0x4113da8ccf84d51e, 0xdcc95af9bde4785b, 0xd3d0c4f67745aeb4, 0x60c9d717009eb88b, 0x9fb13d249bc6308a, 0x66138baa8e16bcb5, 0xf0aa962a48580182, 0x2be8d8b41eebfed1, 0xfe5b041d9c6188d, 0x603e9f819aa64932]

private theorem rounds023_2 : sixRounds 12 (by decide) quarter023_2 = quarter023_3 := by
  decide +kernel

private theorem rounds023_3 : sixRounds 18 (by decide) quarter023_3 = state024 := by
  decide +kernel

private theorem perm023 : KECCAK.f1600 absorbed023 = state024 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds023_0, rounds023_1, rounds023_2, rounds023_3]
  rfl

theorem block023 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes023 ++ tail) state023 =
      KECCAK.Bytes.run 0 tail state024 := by
  exact run_block_of_step bytes023 tail absorb023 state023 absorbed023
    state024 (fun _ => rfl) words023 perm023

end Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
