import Blanc.Lift.Usdc.ImplV2_1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb156 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x65 0x73 0x75 0x61 0x70 0x20 0x65 0x68)) 1 (by decide) (UInt64.ofBytes 0x76 0x6f 0x63 0x65 0x52 0x43 0x45 0x72)) 2 (by decide) (UInt64.ofBytes 0x61 0x76 0x6e 0x69 0x20 0x3a 0x72 0x65)) 3 (by decide) (UInt64.ofBytes 0x6e 0x67 0x69 0x73 0x20 0x64 0x69 0x6c)) 4 (by decide) (UInt64.ofBytes 0x73 0x27 0x20 0x65 0x72 0x75 0x74 0x61)) 5 (by decide) (UInt64.ofBytes 0x53 0x65 0x75 0x6c 0x61 0x76 0x20 0x27)) 6 (by decide) (UInt64.ofBytes 0x30 0x32 0x43 0x52 0x45 0x65 0x66 0x61)) 7 (by decide) (UInt64.ofBytes 0x20 0x30 0x32 0x43 0x52 0x45 0x20 0x3a)) 8 (by decide) (UInt64.ofBytes 0x6f 0x69 0x74 0x61 0x72 0x65 0x70 0x6f)) 9 (by decide) (UInt64.ofBytes 0x6f 0x6e 0x20 0x64 0x69 0x64 0x20 0x6e)) 10 (by decide) (UInt64.ofBytes 0x65 0x65 0x63 0x63 0x75 0x73 0x20 0x74)) 11 (by decide) (UInt64.ofBytes 0x6b 0x6f 0x54 0x74 0x61 0x69 0x46 0x64)) 12 (by decide) (UInt64.ofBytes 0x20 0x77 0x65 0x6e 0x20 0x3a 0x6e 0x65)) 13 (by decide) (UInt64.ofBytes 0x73 0x69 0x20 0x72 0x65 0x6e 0x77 0x6f)) 14 (by decide) (UInt64.ofBytes 0x72 0x65 0x7a 0x20 0x65 0x68 0x74 0x20)) 15 (by decide) (UInt64.ofBytes 0x73 0x65 0x72 0x64 0x64 0x61 0x20 0x6f)) 16 (by decide) (UInt64.ofBytes 0x6b 0x6f 0x54 0x74 0x61 0x69 0x46 0x73))

private def absorbed156 : Vector UInt64 25 :=
  #v[0x805b0d96c8d480de, 0x4dbec4644d6ffc86, 0x3ed5f95fe395d84b, 0x936e13b0b1d23ac3, 0x4e2cb5ff94d61570, 0x65674ace41c6bf2c, 0x6f8293c679f8c44b, 0x97813b46ec159cbc, 0x4e3b72d31c55ac16, 0x979793f7c71ef0bb, 0xfd7424357dcdd7a3, 0xde820d590ea410e, 0x9534eca47f27ea04, 0x51439b6ef3951acd, 0x395ffd492f68c5d5, 0x5a05663b83d4040b, 0x6587bae980883a15, 0x6881f162a60a51fa, 0x22b953f33642956e, 0xccfcbd80ee22a412, 0xbded91f31a78f57b, 0x6f9c558249b0eebe, 0x9c5afa80737b87b, 0xd5e78762c33820af, 0x207c7303e1b47b35]

private theorem words156 : absorb156 state156 = absorbed156 := by
  decide +kernel

private def quarter156_1 : Vector UInt64 25 :=
  #v[0x1e4cc65685b47c6a, 0x49fdc8efb0234434, 0x753d8a80f5d92b0, 0xc27752e275219df5, 0x65d46cfc4051c6b5, 0x21e5f4c839ed75ba, 0xc67f23105a1c1526, 0xadf7802026a6b498, 0xf60e55e73df69595, 0xf19848f9327e7831, 0x38d45825a17e2d66, 0xb58a88191a8e78b1, 0x6111e46c21dcfc3f, 0x71cfeb729a5bdd79, 0x43e75e8df936f72e, 0x39d3e6de2444d65b, 0xfa4b98aa228e4bca, 0x10497035908791c0, 0x2b36e21b5062cb8, 0xc22253924ce3291b, 0xb4b38d9020649750, 0x9c9f3bca81904e8b, 0xd6946a67275a4b33, 0xf05ba20dd2feabf3, 0x166117d3ca55f8c8]

private theorem rounds156_0 : sixRounds 0 (by decide) absorbed156 = quarter156_1 := by
  decide +kernel

private def quarter156_2 : Vector UInt64 25 :=
  #v[0xca6f9729e34a8df8, 0xc697e8868e3dc635, 0x719a0b02146be54, 0xe27460367ecd9252, 0xa7012bcc633ae405, 0x8f3c0b2e68fd237c, 0x7f9339499199fdfa, 0xafd5a3db80fcb132, 0xed2cca3a4cb2469f, 0xb0b4448f708195a3, 0x8d4cd5b2c6ff1f1f, 0x3b77f4292ea3753b, 0xc191b10b7587c67f, 0xc798f0639183827a, 0x2086747a4d81e34d, 0x23bae852896e049c, 0xce1d32d74b89ca5b, 0x6567ca88b6574051, 0x61c9c19adbc0909b, 0x59905fa97cd48db, 0x84245b3c526b8159, 0x122babafd92dd3d, 0x66621fa6fcf379a6, 0xcc3d47f0729a5499, 0xab21fdabd182da9b]

private theorem rounds156_1 : sixRounds 6 (by decide) quarter156_1 = quarter156_2 := by
  decide +kernel

private def quarter156_3 : Vector UInt64 25 :=
  #v[0x8c065ae0e98c6c21, 0x31992eb8faf2f63a, 0x5996728d822bd1ff, 0x76848cf5dd1e87cd, 0xa1f9396ef1f2c2fb, 0x6596ae15dcca9436, 0xe66b2e3217baa5b1, 0xf2a0226e51e100ba, 0xcdfa7f7af45eaf40, 0x95768790e7aee75f, 0xbdb750cfed899446, 0x3abc3ff1cc20147e, 0x34670fb790f381e0, 0x101ebc7255eb069f, 0x99dc0f2d519e9c61, 0x64254931340f6309, 0x4810ad77b77412b4, 0x6b4fbc1ba3ba03dd, 0x4d861cd4a46fea41, 0xe4c74aebdaca04a0, 0x46b6074f587c0ed5, 0xfb93c160c0232ac0, 0xf0bbd8be983f4e41, 0xcad48076b89d932b, 0xb4b5a35c3540c0ad]

private theorem rounds156_2 : sixRounds 12 (by decide) quarter156_2 = quarter156_3 := by
  decide +kernel

private theorem rounds156_3 : sixRounds 18 (by decide) quarter156_3 = state157 := by
  decide +kernel

private theorem perm156 : KECCAK.f1600 absorbed156 = state157 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds156_0, rounds156_1, rounds156_2, rounds156_3]
  rfl

theorem block156 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes156 ++ tail) state156 =
      KECCAK.Bytes.run 0 tail state157 := by
  exact run_block_of_step bytes156 tail absorb156 state156 absorbed156
    state157 (fun _ => rfl) words156 perm156

private def absorb157 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x75 0x61 0x20 0x3a 0x32 0x56 0x6e 0x65)) 1 (by decide) (UInt64.ofBytes 0x74 0x61 0x7a 0x69 0x72 0x6f 0x68 0x74)) 2 (by decide) (UInt64.ofBytes 0x75 0x20 0x73 0x69 0x20 0x6e 0x6f 0x69)) 3 (by decide) (UInt64.ofBytes 0x63 0x20 0x72 0x6f 0x20 0x64 0x65 0x73)) 4 (by decide) (UInt64.ofBytes 0x42 0x64 0x65 0x6c 0x65 0x63 0x6e 0x61)) 5 (by decide) (UInt64.ofBytes 0x74 0x73 0x69 0x6c 0x6b 0x63 0x61 0x6c)) 6 (by decide) (UInt64.ofBytes 0x65 0x6e 0x20 0x3a 0x65 0x6c 0x62 0x61)) 7 (by decide) (UInt64.ofBytes 0x6c 0x6b 0x63 0x61 0x6c 0x62 0x20 0x77)) 8 (by decide) (UInt64.ofBytes 0x73 0x69 0x20 0x72 0x65 0x74 0x73 0x69)) 9 (by decide) (UInt64.ofBytes 0x72 0x65 0x7a 0x20 0x65 0x68 0x74 0x20)) 10 (by decide) (UInt64.ofBytes 0x73 0x65 0x72 0x64 0x64 0x61 0x20 0x6f)) 11 (by decide) (UInt64.ofBytes 0x69 0x6c 0x6b 0x63 0x61 0x6c 0x42 0x73)) 12 (by decide) (UInt64.ofBytes 0x20 0x3a 0x65 0x6c 0x62 0x61 0x74 0x73)) 13 (by decide) (UInt64.ofBytes 0x20 0x74 0x6e 0x75 0x6f 0x63 0x63 0x61)) 14 (by decide) (UInt64.ofBytes 0x6b 0x63 0x61 0x6c 0x62 0x20 0x73 0x69)) 15 (by decide) (UInt64.ofBytes 0x69 0x46 0x64 0x65 0x74 0x73 0x69 0x6c)) 16 (by decide) (UInt64.ofBytes 0x56 0x6e 0x65 0x6b 0x6f 0x54 0x74 0x61))

private def absorbed157 : Vector UInt64 25 :=
  #v[0x176ba4637465577, 0x748ae76cf345e726, 0xb26a8acec18a12a8, 0xc5681f0c8e22b909, 0x3522e5138c87725b, 0x821eb345e3599a07, 0x344dbd45fbe242b3, 0x6e09e674aca22c36, 0xbdd7b389ca17573f, 0x43950bfa6fd25dc2, 0xad04941e38e9778c, 0x4e685ec1c9d3e032, 0x4aef4618474c47eb, 0x26acefd09745357b, 0xbf1a6ecc692a5fd0, 0x61bde6c930d2c6, 0xcf2d69b78cc845a7, 0x6fed04ad2b2f1dcd, 0x619722ea1f9c2d71, 0xbbe416e5c949970e, 0xa1da2f0a5d01f0d1, 0xbb5ccfe42459b0a0, 0x429d95976fcd20ac, 0x7f50d5871afcc0fc, 0x58abd21fb018d28e]

private theorem words157 : absorb157 state157 = absorbed157 := by
  decide +kernel

private def quarter157_1 : Vector UInt64 25 :=
  #v[0xdea76ea03ae2fda1, 0x4d409eb203e8438f, 0xd89281f9e1693827, 0xd93eaa2c99168a8c, 0x29d8cb4072c1d96e, 0x271b7f8e5e6864d9, 0x2da613438776f88e, 0xf6f49de3488a4ad, 0x58db70d37dc735a9, 0x6dfba9c7eea6ddca, 0xd5f1380927711f7, 0xc904b4283dbb92f8, 0x633921f520b77971, 0xa7a3779e9553def4, 0x12ca1d0456850475, 0x790b8773bc17ed03, 0x12b6ca3652ea43, 0x64b5b74a59de6023, 0xc12a6bbd05efa785, 0x30533ba2376b521a, 0x861bde562b24c7a0, 0x864a466207875db4, 0x800acb77e0cd75e3, 0xc74d2bbbb3a688f1, 0x2cbf286486aa3226]

private theorem rounds157_0 : sixRounds 0 (by decide) absorbed157 = quarter157_1 := by
  decide +kernel

private def quarter157_2 : Vector UInt64 25 :=
  #v[0xa8ba8504d2fc9942, 0x8f4ba32b075bf127, 0xda608bdc23c05f53, 0x1450b54eb4c73eda, 0x596d93f842644e0f, 0xd59e1ffbaea464fb, 0xb4184bd8edc1a410, 0x601aab80534e8e6b, 0xeecacdd17fcc313a, 0x28bd2b50858d5050, 0xf82fdd84e3c4308c, 0xe14906f603d70ad, 0x83e093017a897a0d, 0x407d01362fd5a9c, 0xcf07eac19c6d922f, 0x690f34a73a0786e5, 0x44b377c1cc539e19, 0x4eac7a20fa72c083, 0x8a352956951b7af7, 0x685bc941d0d1a93a, 0xad2eca866688327e, 0x6346ed8a4d457f4c, 0xa448c41870f9c255, 0x8f5dfe4ac631e6a6, 0x3e37ca996bf74c9]

private theorem rounds157_1 : sixRounds 6 (by decide) quarter157_1 = quarter157_2 := by
  decide +kernel

private def quarter157_3 : Vector UInt64 25 :=
  #v[0x549a9897acd34908, 0xdaa5b50e53fd0b5a, 0x681364f905042ec9, 0xd019a9b52502575f, 0xaebff90fcdc8d04a, 0x39c701dd9b831154, 0x369548d3ecb175e1, 0x60fe02110dbca2e6, 0x67ebc8d3dd1c5026, 0x1a25c7511deacd81, 0x981a943b9d85b77d, 0x6cdbe84a8e4817c2, 0xd47bece36ebdc78b, 0x68bfa18913912019, 0xcb398d09d3b374b9, 0xdf5bf934d4256c4f, 0xe010e1830142f330, 0xc525876585483437, 0x2b27f2409d3678f0, 0x4322656ec679d803, 0x42ec1b79d5bd8f47, 0x5553731daa8f50ae, 0x19f169d4acd95be2, 0x80855705d0a5d73a, 0x5a992eb9f87864db]

private theorem rounds157_2 : sixRounds 12 (by decide) quarter157_2 = quarter157_3 := by
  decide +kernel

private theorem rounds157_3 : sixRounds 18 (by decide) quarter157_3 = state158 := by
  decide +kernel

private theorem perm157 : KECCAK.f1600 absorbed157 = state158 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds157_0, rounds157_1, rounds157_2, rounds157_3]
  rfl

theorem block157 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes157 ++ tail) state157 =
      KECCAK.Bytes.run 0 tail state158 := by
  exact run_block_of_step bytes157 tail absorb157 state157 absorbed157
    state158 (fun _ => rfl) words157 perm157

private def absorb158 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x6f 0x68 0x74 0x75 0x61 0x20 0x3a 0x32)) 1 (by decide) (UInt64.ofBytes 0x6e 0x6f 0x69 0x74 0x61 0x7a 0x69 0x72)) 2 (by decide) (UInt64.ofBytes 0x69 0x70 0x78 0x65 0x20 0x73 0x69 0x20)) 3 (by decide) (UInt64.ofBytes 0x30 0x32 0x43 0x52 0x45 0x64 0x65 0x72)) 4 (by decide) (UInt64.ofBytes 0x61 0x65 0x72 0x63 0x65 0x64 0x20 0x3a)) 5 (by decide) (UInt64.ofBytes 0x6f 0x6c 0x6c 0x61 0x20 0x64 0x65 0x73)) 6 (by decide) (UInt64.ofBytes 0x65 0x62 0x20 0x65 0x63 0x6e 0x61 0x77)) 7 (by decide) (UInt64.ofBytes 0x6f 0x72 0x65 0x7a 0x20 0x77 0x6f 0x6c)) 8 (by decide) (UInt64.ofBytes 0x22 0x58 0x73 0x66 0x70 0x69 0x64 0xa2)) 9 (by decide) (UInt64.ofBytes 0x9a 0xf7 0xec 0x1b 0x73 0x7e 0x20 0x12)) 10 (by decide) (UInt64.ofBytes 0x8e 0x44 0x50 0x9d 0x9f 0xe3 0x1e 0x9)) 11 (by decide) (UInt64.ofBytes 0xf5 0x60 0xee 0x75 0xd3 0xfd 0x72 0x54)) 12 (by decide) (UInt64.ofBytes 0x9d 0x3b 0x4b 0x3d 0xfd 0xe5 0xa1 0x32)) 13 (by decide) (UInt64.ofBytes 0x43 0x63 0x6c 0x6f 0x73 0x64 0x63 0x8b)) 14 (by decide) (UInt64.ofBytes 0x0 0x0 0x1 0x33 0x0 0xc 0x6 0x0)) 16 (by decide) ((8 : UInt64) <<< 60))

private def absorbed158 : Vector UInt64 25 :=
  #v[0x5029ae76b7f858ff, 0x9c32b711180e3e1c, 0xbda198c06d611ff4, 0x9c9fcd3cad55e52c, 0x71a43827309c421e, 0x62cd026943e4de6c, 0x2a6a8646632ab3a0, 0xc364abd46da30253, 0xc17dbef7f10f5da, 0x2db89868c87fadb3, 0x5e7b1107f94b968d, 0x6e23d6f1fa3f2e84, 0xe6130f43d07726a4, 0xd0d6af7f851a38b5, 0x113378cd1a8051af, 0x765eef64ef8391f0, 0x9d86153d1d1ec654, 0x492cceadd0887d0c, 0x581a9c41ee2ad3d9, 0xeea5c595567435e4, 0xd0c2b7a8cac34cd3, 0x97173e42b45d1a7c, 0xfd2de4ef72f24ecf, 0x7e5ca419bbcf3e89, 0xe9d7323ab536d65a]

private theorem words158 : absorb158 state158 = absorbed158 := by
  decide +kernel

private def quarter158_1 : Vector UInt64 25 :=
  #v[0xe96c893bfdc2cb7a, 0xafcc1424e0516d58, 0x1dcd03e06d247ecc, 0x7513fbe8836c7a37, 0xe98f57d532c88e4b, 0xf153dd319aaf07e1, 0xc165500ba502a668, 0x591f8ef3b856cef7, 0x66c17724fa30f54c, 0x2cf47355476841e8, 0x405f75354acc6b36, 0xf35b38cf8bdced22, 0x2c07ad825c834bd7, 0x50ae56844f8a874f, 0x5f71db22598695a4, 0x3644bcdd0814ae97, 0xba87a5e62e92497c, 0xf2db77082b5919b8, 0x5a0b138788a222dd, 0xae0c4ea0eaa05858, 0xa2a3714371138083, 0xf6844e5915330f78, 0x2a6dacf3a47ce35d, 0x31c110bc6d1d0340, 0xe52471d8faea7f5a]

private theorem rounds158_0 : sixRounds 0 (by decide) absorbed158 = quarter158_1 := by
  decide +kernel

private def quarter158_2 : Vector UInt64 25 :=
  #v[0x29269a42e2cfa13b, 0x238da9dbb1f43496, 0xb51a110c66939080, 0xee7e31be99bf77bf, 0x24d735f9d39603e3, 0xe099512b878ce0f9, 0x404bb7ca1cf673ac, 0x8c92f633747f8dcf, 0xcd60f18c5fdb0114, 0xf10b929282f9373, 0xc5f3f1872728751a, 0x5fbc0f930ef36885, 0xc9f0f7e18843b24a, 0x69db3462bb1425b7, 0x65fb18d8845d378a, 0x40144b00defb0bca, 0xa098c21a0256e584, 0xae3026ab40984788, 0x9fc59c9ee3427a41, 0x2ed33a731288ea84, 0xec2b8f22787990f1, 0x4717f27f07af39af, 0x3ac5e164a900f582, 0xc524eadbc936175f, 0x7c6b648fd432f3b8]

private theorem rounds158_1 : sixRounds 6 (by decide) quarter158_1 = quarter158_2 := by
  decide +kernel

private def quarter158_3 : Vector UInt64 25 :=
  #v[0x65497b381455a33, 0x41b64b11fee7b96a, 0x743b798cd39efd35, 0xd8233ae73d504b0c, 0x4b7280b539cc0e40, 0x901eff7063afa138, 0x5b108db3b8925388, 0x4b0684e237a25fad, 0x231d04b01a709a50, 0x2cbfd4ed21902bbb, 0x7413945982ffed1f, 0x3aabeca3bbf18438, 0x27663b562d36f9de, 0x629257368f63cb8e, 0x3b9441b529d60dfe, 0x2b789420e5ff23cb, 0xa74e04c5c62ddee9, 0x337542234a55079c, 0x692b8016690f636d, 0x3620294260b58d74, 0xcbe9eb9b98428285, 0xb9a042d7d10eb6a4, 0x246dc9b630d11851, 0x6da59e89f5ea504f, 0xe5f3e2b31b0bc52b]

private theorem rounds158_2 : sixRounds 12 (by decide) quarter158_2 = quarter158_3 := by
  decide +kernel

private theorem rounds158_3 : sixRounds 18 (by decide) quarter158_3 = state159 := by
  decide +kernel

private theorem perm158 : KECCAK.f1600 absorbed158 = state159 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds158_0, rounds158_1, rounds158_2, rounds158_3]
  rfl

private theorem finalDigest : squeeze state159 = (0x67266765a0508883ae11ac6dd0ad8d63c2d6cf26d7af55c349361662a14ede87 : B256) := by
  decide +kernel

theorem finalHash :
    KECCAK.Bytes.run 0 bytes158 state158 = (0x67266765a0508883ae11ac6dd0ad8d63c2d6cf26d7af55c349361662a14ede87 : B256) := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 bytes158 ws = squeeze (KECCAK.f1600 (absorb158 ws)) := by
    rfl
  exact (step state158).trans ((congrArg squeeze
    ((congrArg KECCAK.f1600 words158).trans perm158)).trans finalDigest)

end Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
