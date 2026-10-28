import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb168 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x75 0x61 0x50 0x65 0x63 0x6e 0x61 0x77)) 1 (by decide) (UInt64.ofBytes 0x63 0x20 0x3a 0x65 0x6c 0x62 0x61 0x73)) 2 (by decide) (UInt64.ofBytes 0x73 0x69 0x20 0x72 0x65 0x6c 0x6c 0x61)) 3 (by decide) (UInt64.ofBytes 0x65 0x68 0x74 0x20 0x74 0x6f 0x6e 0x20)) 4 (by decide) (UInt64.ofBytes 0x45 0x72 0x65 0x73 0x75 0x61 0x70 0x20)) 5 (by decide) (UInt64.ofBytes 0x72 0x65 0x76 0x6f 0x63 0x65 0x52 0x43)) 6 (by decide) (UInt64.ofBytes 0x69 0x6c 0x61 0x76 0x6e 0x69 0x20 0x3a)) 7 (by decide) (UInt64.ofBytes 0x74 0x61 0x6e 0x67 0x69 0x73 0x20 0x64)) 8 (by decide) (UInt64.ofBytes 0x20 0x27 0x73 0x27 0x20 0x65 0x72 0x75)) 9 (by decide) (UInt64.ofBytes 0x66 0x61 0x53 0x65 0x75 0x6c 0x61 0x76)) 10 (by decide) (UInt64.ofBytes 0x20 0x3a 0x30 0x32 0x43 0x52 0x45 0x65)) 11 (by decide) (UInt64.ofBytes 0x70 0x6f 0x20 0x30 0x32 0x43 0x52 0x45)) 12 (by decide) (UInt64.ofBytes 0x20 0x6e 0x6f 0x69 0x74 0x61 0x72 0x65)) 13 (by decide) (UInt64.ofBytes 0x20 0x74 0x6f 0x6e 0x20 0x64 0x69 0x64)) 14 (by decide) (UInt64.ofBytes 0x46 0x64 0x65 0x65 0x63 0x63 0x75 0x73)) 15 (by decide) (UInt64.ofBytes 0x6e 0x65 0x6b 0x6f 0x54 0x74 0x61 0x69)) 16 (by decide) (UInt64.ofBytes 0x77 0x6f 0x20 0x77 0x65 0x6e 0x20 0x3a))

private def absorbed168 : Vector UInt64 25 :=
  #v[0x1cee9c5fdd814216, 0x89d6eebba187b8a4, 0x5217129323f0d90d, 0xf12a4bd9d0efd910, 0x116f6e1ed12268dd, 0x9b97d6e828452a3b, 0x86e2d01d21b62f77, 0x5a09001faf9c3974, 0xb99a82cef1e73da8, 0xa4a3beee98c9a2ef, 0x722f11e1af058948, 0x642bc8551b28a7cf, 0x6b2196026e1d9c72, 0x6a7f1b75f55283f0, 0x591ef554de0aec4f, 0x56bdb7c68c5f16c9, 0xd7b86cfe30bc7995, 0x22ee5273640f0a99, 0xd94f3deb59e7555b, 0x9c0f0fed425f8dc7, 0x77e9dd531c030247, 0x897dc2a5a5ae4837, 0xad1370d88201ff62, 0xfcdca581c26bc896, 0x1ee13cb0b6e28bb4]

private theorem words168 : absorb168 state168 = absorbed168 := by
  decide +kernel

private def quarter168_1 : Vector UInt64 25 :=
  #v[0x1f94262704f524e7, 0x1d25fbd36a4871fc, 0x206aa5dec5dd3c6d, 0x9b0530b07c00136d, 0x5904e73ddc31e20c, 0xdaa4234ae83fff78, 0x1ad388951d9c6aa9, 0x1b3e6a89b3e6d1de, 0xc2dd40d1079c9a41, 0x77fe92e59113af4, 0xec8ca2736e490092, 0x2cf2112dafac8796, 0x7ad62acd360b3017, 0xff823ed8b5e9f7e4, 0x223aa7526bf21085, 0xa6b59297cb159dff, 0x1c4232f46e797cf2, 0x99012b44873f3697, 0x12bc580fff7c2ba9, 0xe1c852ca0d3570de, 0xac7aa39c5e52711c, 0xf0a542c83ee3d5b8, 0x2935d0d862306d1c, 0xf4ae9f94d1395942, 0x78375223c4537074]

private theorem rounds168_0 : sixRounds 0 (by decide) absorbed168 = quarter168_1 := by
  decide +kernel

private def quarter168_2 : Vector UInt64 25 :=
  #v[0x2fd8e1ca54e50dc8, 0xb31fd35621a755d4, 0x86aa3be270cda119, 0x8726864d6e82051c, 0x43783e43280687f8, 0xf842927ca4e2f6ca, 0x9b477cd81836124a, 0xf49b6e9e6f18da08, 0xab199ff4bf01c8eb, 0x136abae81f5e7f07, 0xb5796ae2d0589d8c, 0xf6067360e9769fcc, 0x2fc45d905ee86e48, 0xec52ef4239595768, 0x48b480493b775095, 0x72a5d9086ad1058f, 0xc3edd5e9fd58c651, 0xfe470f9875008ea2, 0xbb251ffcbd8fb85e, 0xe52850b77dbb533d, 0x40b521a9eef8dd48, 0xf860079fd0fedaa9, 0xb943e612d593a35c, 0xab8ffb181bb6c9b4, 0x90d48f0758409e04]

private theorem rounds168_1 : sixRounds 6 (by decide) quarter168_1 = quarter168_2 := by
  decide +kernel

private def quarter168_3 : Vector UInt64 25 :=
  #v[0xc4ea66bd12d975a0, 0x346808a4bf97e0d2, 0x8443db9f0f24be5a, 0x849ae662d67dcf51, 0x1d2b1c4ac6ebaa98, 0xf4f55c0bdf1bee96, 0xadc788725cfd5d7a, 0xe4b4468264fade5d, 0x9643530093ee6c5f, 0xb435e5591fc3e88d, 0xccea0b14bd36e103, 0x7f43b891899c59a4, 0x6126d7a707858825, 0xb4833aff9075dffe, 0x83073ea96172f8cf, 0x69b2397aa3723b5c, 0x678ebf2492d38c60, 0x11b09fac2834f54c, 0xad087be07beed0fe, 0x4bc2b4caa6755c57, 0xf32dfd59f7e8bdbc, 0xf92dbbd5f3b22f42, 0x2a410860ee575640, 0x73c585d9c06042e0, 0x3a4dedd31f7fd400]

private theorem rounds168_2 : sixRounds 12 (by decide) quarter168_2 = quarter168_3 := by
  decide +kernel

private theorem rounds168_3 : sixRounds 18 (by decide) quarter168_3 = state169 := by
  decide +kernel

private theorem perm168 : KECCAK.f1600 absorbed168 = state169 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds168_0, rounds168_1, rounds168_2, rounds168_3]
  rfl

theorem block168 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes168 ++ tail) state168 =
      KECCAK.Bytes.run 0 tail state169 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes168 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb168 ws)) := by
    rfl
  exact (step state168).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words168).trans perm168))

private def absorb169 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x74 0x20 0x73 0x69 0x20 0x72 0x65 0x6e)) 1 (by decide) (UInt64.ofBytes 0x20 0x6f 0x72 0x65 0x7a 0x20 0x65 0x68)) 2 (by decide) (UInt64.ofBytes 0x46 0x73 0x73 0x65 0x72 0x64 0x64 0x61)) 3 (by decide) (UInt64.ofBytes 0x6e 0x65 0x6b 0x6f 0x54 0x74 0x61 0x69)) 4 (by decide) (UInt64.ofBytes 0x68 0x74 0x75 0x61 0x20 0x3a 0x32 0x56)) 5 (by decide) (UInt64.ofBytes 0x6f 0x69 0x74 0x61 0x7a 0x69 0x72 0x6f)) 6 (by decide) (UInt64.ofBytes 0x65 0x73 0x75 0x20 0x73 0x69 0x20 0x6e)) 7 (by decide) (UInt64.ofBytes 0x6e 0x61 0x63 0x20 0x72 0x6f 0x20 0x64)) 8 (by decide) (UInt64.ofBytes 0x61 0x6c 0x42 0x64 0x65 0x6c 0x65 0x63)) 9 (by decide) (UInt64.ofBytes 0x62 0x61 0x74 0x73 0x69 0x6c 0x6b 0x63)) 10 (by decide) (UInt64.ofBytes 0x20 0x77 0x65 0x6e 0x20 0x3a 0x65 0x6c)) 11 (by decide) (UInt64.ofBytes 0x73 0x69 0x6c 0x6b 0x63 0x61 0x6c 0x62)) 12 (by decide) (UInt64.ofBytes 0x74 0x20 0x73 0x69 0x20 0x72 0x65 0x74)) 13 (by decide) (UInt64.ofBytes 0x20 0x6f 0x72 0x65 0x7a 0x20 0x65 0x68)) 14 (by decide) (UInt64.ofBytes 0x42 0x73 0x73 0x65 0x72 0x64 0x64 0x61)) 15 (by decide) (UInt64.ofBytes 0x74 0x73 0x69 0x6c 0x6b 0x63 0x61 0x6c)) 16 (by decide) (UInt64.ofBytes 0x63 0x61 0x20 0x3a 0x65 0x6c 0x62 0x61))

private def absorbed169 : Vector UInt64 25 :=
  #v[0x3bd18c1a6ee4cbf5, 0x6eaef93057b3a8fa, 0x5e281edb3a73b6c, 0x4e5c87988fb87b79, 0xfaba829f74e609f4, 0x226916990551226f, 0x867bfddeefd474be, 0x123fe0880110a1a, 0xf1be2dc39cfdd340, 0x10c81c38eb2e218b, 0x48c3aa539917c012, 0x5f40f3b290f08612, 0xb48ad296b9be7e01, 0x539cdc2041fb8ad5, 0xfb4cbbdf97474c4c, 0x7081b5d6d5b608fd, 0xc14c0f8afd9003c0, 0x88e49589cc9b30da, 0xb4718959ba862c1, 0x3313b40079630534, 0xd8d7b39148c78be1, 0x6e529fa03f82be8, 0xa17aaeead4a23de4, 0x6575fa1a9e12e13e, 0xbd16b5409f03bc9d]

private theorem words169 : absorb169 state169 = absorbed169 := by
  decide +kernel

private def quarter169_1 : Vector UInt64 25 :=
  #v[0x65a160f0943003c, 0x497986240c61091f, 0xab33afd3ccaa1864, 0x71b98666a8183166, 0x5d7659a627fa88b7, 0xf9cce57d126f7eae, 0xc4c5a2ba97b21751, 0xaaae1d8ae68aac00, 0xa7e0a44eae1e0d77, 0x5b03cf090e85f429, 0x292fcecf4c25a3a3, 0x22316ab49841ab09, 0x78d837d435a5870e, 0x5ed922c973ccf8ea, 0xea30e3b42ad91289, 0x791e08ac2769c138, 0x65e4f010f258b2d7, 0x5b4f3420d1abca3c, 0xf7353c290ed66b0c, 0x19310fa81ec7f460, 0x1df38bc49261f102, 0x77a144bc18a5bac1, 0x822a9d533524daac, 0x2b29f1be20c97c23, 0xbb68a070bf178529]

private theorem rounds169_0 : sixRounds 0 (by decide) absorbed169 = quarter169_1 := by
  decide +kernel

private def quarter169_2 : Vector UInt64 25 :=
  #v[0x5a917db1aa362600, 0x678e9e2c552888b8, 0xeb7f89f264ffae51, 0xa66a33d2d27c577d, 0x4df1ecee9088fafc, 0xebd2c24871a83ece, 0x5feb1883123af854, 0xaa963309e61c7fe3, 0x78215d0223424b0a, 0xb082fba54fa8fd04, 0x67f8b7a19abdeb5e, 0x698895e058bb0872, 0xfaa0126a26e19d04, 0x1536b8f22fa457d, 0xb83ec774e802dd6b, 0x1daf83ae1406f9fa, 0x517b90027ea5aac9, 0x1ca388655bda36c1, 0x78652762731364dd, 0xe956c73a682d27f5, 0x89ede3229b249974, 0xc85675cd297f8962, 0x7ae08ecae5d6cff9, 0x3b293f73f8a84d97, 0xbc2f283c30c3ab6c]

private theorem rounds169_1 : sixRounds 6 (by decide) quarter169_1 = quarter169_2 := by
  decide +kernel

private def quarter169_3 : Vector UInt64 25 :=
  #v[0xcf5c825f36eaeb1b, 0x8902f4436ec88baf, 0x695da57f5b7d4c02, 0xc81ce51fa967a523, 0xe7e818ddfbc4c378, 0xb49a923e22446037, 0xb3f4dd4b547bccfa, 0xc122bdcac4415a95, 0xee935c7dc4df29d2, 0xc4ae86bbcb07df11, 0xd316c30feea74dc6, 0x4b9b0f046f85eed9, 0x3d90733dc63cd583, 0x34e7dd315d578cfb, 0xdb6815bb9f184da4, 0xb1d09eda08ea516c, 0xe935fb9a4dfc1949, 0xa045989b2063ab99, 0xeed0c816a9347544, 0xf4034e3a01c6612b, 0xeada8e614c43a302, 0x7c48e6c93f173903, 0x27123c1a699b1774, 0x841439d109a0df6, 0xaab55f70e0032625]

private theorem rounds169_2 : sixRounds 12 (by decide) quarter169_2 = quarter169_3 := by
  decide +kernel

private theorem rounds169_3 : sixRounds 18 (by decide) quarter169_3 = state170 := by
  decide +kernel

private theorem perm169 : KECCAK.f1600 absorbed169 = state170 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds169_0, rounds169_1, rounds169_2, rounds169_3]
  rfl

theorem block169 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes169 ++ tail) state169 =
      KECCAK.Bytes.run 0 tail state170 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes169 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb169 ws)) := by
    rfl
  exact (step state169).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words169).trans perm169))

private def absorb170 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x73 0x69 0x20 0x74 0x6e 0x75 0x6f 0x63)) 1 (by decide) (UInt64.ofBytes 0x69 0x6c 0x6b 0x63 0x61 0x6c 0x62 0x20)) 2 (by decide) (UInt64.ofBytes 0x74 0x61 0x69 0x46 0x64 0x65 0x74 0x73)) 3 (by decide) (UInt64.ofBytes 0x3a 0x32 0x56 0x6e 0x65 0x6b 0x6f 0x54)) 4 (by decide) (UInt64.ofBytes 0x69 0x72 0x6f 0x68 0x74 0x75 0x61 0x20)) 5 (by decide) (UInt64.ofBytes 0x69 0x20 0x6e 0x6f 0x69 0x74 0x61 0x7a)) 6 (by decide) (UInt64.ofBytes 0x65 0x72 0x69 0x70 0x78 0x65 0x20 0x73)) 7 (by decide) (UInt64.ofBytes 0x20 0x3a 0x30 0x32 0x43 0x52 0x45 0x64)) 8 (by decide) (UInt64.ofBytes 0x65 0x73 0x61 0x65 0x72 0x63 0x65 0x64)) 9 (by decide) (UInt64.ofBytes 0x61 0x77 0x6f 0x6c 0x6c 0x61 0x20 0x64)) 10 (by decide) (UInt64.ofBytes 0x6f 0x6c 0x65 0x62 0x20 0x65 0x63 0x6e)) 11 (by decide) (UInt64.ofBytes 0x64 0xa2 0x6f 0x72 0x65 0x7a 0x20 0x77)) 12 (by decide) (UInt64.ofBytes 0x20 0x12 0x22 0x58 0x73 0x66 0x70 0x69)) 13 (by decide) (UInt64.ofBytes 0x9e 0xb1 0xea 0xf3 0x62 0xa6 0x97 0xc5)) 14 (by decide) (UInt64.ofBytes 0xaf 0x17 0x1a 0xbe 0xc5 0xa8 0x6f 0x5d)) 15 (by decide) (UInt64.ofBytes 0x3e 0x3c 0xfd 0x9e 0x10 0x7c 0x94 0xe3)) 16 (by decide) (UInt64.ofBytes 0xf1 0xed 0xca 0x8c 0x5f 0x44 0x7f 0x94))

private def absorbed170 : Vector UInt64 25 :=
  #v[0xb550842b7bfae3a9, 0xc3b046dc7e02fc4e, 0x3e05f37b6a5f9299, 0x84fea2e23bdd32a9, 0xdb26e5d406165a79, 0x444cffda433b440c, 0xbe02c2d20ca53667, 0x9eaf917231e24d80, 0x717e7c529498271f, 0x64fdcfbca0aaf2ae, 0xb904be098fa6aae4, 0x610b0fda78ac8c5, 0x48a63e7ef14661bc, 0xa08f6faba68c3054, 0xad50d8003a94a251, 0x86137f98b82ddea2, 0xeee6ec8c4e314448, 0x8fbd3dad8f5ffb68, 0x18236812c8d84723, 0xd000a5cb3ca21928, 0x9e250da9e009bc18, 0xe294dc125c117a91, 0xcac23e6fac17bfd0, 0xaafc04af66a57072, 0xda5c746d3cc16f21]

private theorem words170 : absorb170 state170 = absorbed170 := by
  decide +kernel

private def quarter170_1 : Vector UInt64 25 :=
  #v[0x311106a39f0ef6d5, 0xd22fc8123cc7cf40, 0x8bdb86bcde0561b5, 0x9b7747e10c239f5e, 0x8529d97294c091c7, 0x8d4fc6022807c471, 0xe54c88c63a6a393f, 0x7870077a1f1f8886, 0x7fd36721f0ee6f02, 0x7cb1fd3f23dff95, 0x2822e40788e5d6e, 0x22468a956f5639e6, 0x2744d9e0e0e2112d, 0x60e7239a61ef4ef2, 0xdce6e624174092b5, 0x6ad054181d73648a, 0xb2a1594563fcdf31, 0xbc9f90d4924185df, 0x22dd858543bf5c18, 0x66771d9833e4a72e, 0x92b211e574288ae, 0x2b614dd77b52d1f8, 0xf725566419c9d3ca, 0x638948a768cb50c7, 0x66e8eeb43c08ec4a]

private theorem rounds170_0 : sixRounds 0 (by decide) absorbed170 = quarter170_1 := by
  decide +kernel

private def quarter170_2 : Vector UInt64 25 :=
  #v[0xbb635dee8f749724, 0x115f8e253e7710aa, 0x458db5ac24a5066, 0x37d0c191a7bc1aed, 0x78536ba1d32b8174, 0xfc5210101704ef4a, 0xa55288d28c3518e5, 0x6ba41f121dcee73, 0xde4884a6301add40, 0xbbfe41c62f739f78, 0x824c3304a5e18122, 0x8706b4df9814fa9c, 0x969b535dc14a4773, 0xdd16f0c170cbd855, 0xd2032fcec25668a6, 0x597f474f507d9379, 0xf892a2012b9a8254, 0x55680e3edfc54b59, 0xc3362e70960f5be7, 0x5a3f2c443418aead, 0x907b263a1f42c188, 0xbbced23f9d122b08, 0x511eacd7cd25f59a, 0xabac07cd2c9bc72b, 0x77cfce59db2a55b9]

private theorem rounds170_1 : sixRounds 6 (by decide) quarter170_1 = quarter170_2 := by
  decide +kernel

private def quarter170_3 : Vector UInt64 25 :=
  #v[0x146b0f1eba12c5ea, 0x696a4bcda0c369a4, 0xd75a91c61dff2a86, 0xa40fe8d78da72cdb, 0x2ebd791fc4a75341, 0xe1d96c9de305ea4e, 0x819a7c5ae625aaca, 0xb4e67808033068ba, 0x81b669202164100f, 0xf0aa4f69c8cb1726, 0xb6536bc59138ff10, 0xd9655e385929b520, 0xe95ef198f745b662, 0xd595e0fe762350c0, 0x45b7795c9637dd4a, 0x8f3db4405515e864, 0x6c8338c55eab3d5d, 0xe0e6ddfd84688135, 0x50088d17a82ac390, 0xdcffc42a69d65c4, 0xb334328a75c55ef6, 0x49867fe8f2762f6d, 0xeee0a69fb9a665df, 0xeaf07b9d50bb14d8, 0xb60c7eeb0bb35dd7]

private theorem rounds170_2 : sixRounds 12 (by decide) quarter170_2 = quarter170_3 := by
  decide +kernel

private theorem rounds170_3 : sixRounds 18 (by decide) quarter170_3 = state171 := by
  decide +kernel

private theorem perm170 : KECCAK.f1600 absorbed170 = state171 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds170_0, rounds170_1, rounds170_2, rounds170_3]
  rfl

theorem block170 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes170 ++ tail) state170 =
      KECCAK.Bytes.run 0 tail state171 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes170 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb170 ws)) := by
    rfl
  exact (step state170).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words170).trans perm170))

private def absorb171 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x6 0x0 0x43 0x63 0x6c 0x6f 0x73 0x64)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x1 0x33 0x0 0xc)) 16 (by decide) ((8 : UInt64) <<< 60))

private def absorbed171 : Vector UInt64 25 :=
  #v[0xf15957586b5369c7, 0x8216f19950c69192, 0x38386086c4f66cc1, 0xf4ce97c7c15a3e3, 0x4e1d69509a6168f1, 0x574a6ad43f49b3a3, 0x801dfbc2653236bc, 0xbdeea1a1b4905ae3, 0x11ae544b4032a1b1, 0x9bef5e3bc0992c3a, 0x51a20abd49472f56, 0x45331b6101ff7823, 0x8894856360eaddc5, 0x93707d7dd4f964e9, 0xdf93fc3f0e113b3d, 0xa4a26941261a393, 0x6b62160e996f68cb, 0xddf20ba1b471810b, 0xc3f8e0d108014466, 0xf689e0cb4f7be2a1, 0x52f8836eb1475a97, 0x58482b46b96ddb78, 0x274a40b923319f4c, 0xc9137997878b64c2, 0xe1276a40d3683318]

private theorem words171 : absorb171 state171 = absorbed171 := by
  decide +kernel

private def quarter171_1 : Vector UInt64 25 :=
  #v[0xf323f0c7e0cddda7, 0xabc04aaed2b7f091, 0x334cd766b3d276b7, 0x18b8dde6472d6b3a, 0x416e1d0758c0f838, 0xb93b6aac61ee48b8, 0x8c7ba2f64ddbae73, 0x24587e8dc82939eb, 0x4c2421ba16a99fee, 0x1fe07d3557f94d50, 0xb9b1f0bcf12d1406, 0x86f06ce22bce28a4, 0x74e42a661709b061, 0x8ccd1c08b25aa3ad, 0xf3c76538ca9dffb5, 0x29f3a8dbca68c240, 0x39bafc6cb827ee1c, 0x49cf97fd44702f73, 0xd3938dd2db05ab3d, 0x8a876f56d8fa4466, 0xaa6f0024094635de, 0x2c63f2c740ff07d1, 0x7bb7baa5e75a3b53, 0x32ce4ed51760d8e1, 0x1d4414f7244603aa]

private theorem rounds171_0 : sixRounds 0 (by decide) absorbed171 = quarter171_1 := by
  decide +kernel

private def quarter171_2 : Vector UInt64 25 :=
  #v[0x2cb7636baa859fa3, 0xb5e91e67c5af82a5, 0x41356e2fdc1545a8, 0xaaf9cb626681d3d, 0xb7d6c75a0615c7f2, 0x9a47da604d25361, 0xa41d0593952c4d07, 0x34bb4e34adb9c265, 0x223d7088821333aa, 0xcbaffc9ab37e414b, 0xb98c85fca65d4521, 0x52a9ea2e95f93f3b, 0xc6a8b381d77633c8, 0x403236fea04aa6bf, 0x659b1426d8834c74, 0x5b3bf5da3280416, 0x7206c0e8c5b82473, 0xaaadc44e55d8a17, 0x9fde3ec902575ce9, 0x3706f8948cec136f, 0x5cf3ed4facea8b48, 0x319d5f064cd2b071, 0x51752e2799623a10, 0xd6c9fc78c259c5c7, 0xb7d3828b12146db2]

private theorem rounds171_1 : sixRounds 6 (by decide) quarter171_1 = quarter171_2 := by
  decide +kernel

private def quarter171_3 : Vector UInt64 25 :=
  #v[0x52ab6cd47292694a, 0xf63200f11588bd3, 0x8cf43f5feed309ff, 0x5f0675f99c9282b0, 0xedb886933385a014, 0xe68b4e3613e1d1bf, 0xc9fd5d38bad22c2d, 0x32aa9f9295a202a7, 0x1536e6b25b99bc6d, 0xc1243653c4a078d6, 0x1d99bb22974cbd31, 0x6512db0a764e9be5, 0xd02627723d0abe98, 0xc862d056baec451d, 0x783695cce6ffc283, 0x539c9001abc526cb, 0xa185bfbe82e7d2ab, 0xd0831081f6f3547d, 0x466703da9e42d376, 0x4028bbf1ab0bf4d5, 0x88b1ede189d8120c, 0x7cdb1acd02619a4c, 0x2ba183502e3cc4fa, 0x13258b34c2a82bc9, 0x46bce5fde6f0466c]

private theorem rounds171_2 : sixRounds 12 (by decide) quarter171_2 = quarter171_3 := by
  decide +kernel

private theorem rounds171_3 : sixRounds 18 (by decide) quarter171_3 = state172 := by
  decide +kernel

private theorem perm171 : KECCAK.f1600 absorbed171 = state172 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds171_0, rounds171_1, rounds171_2, rounds171_3]
  rfl

private theorem finalDigest : squeeze state172 = (0xf2c79146b7c5d2251888a408d1391aee591ac0f105668159b5638f7ac3c73215 : B256) := by
  decide +kernel

theorem finalHash :
    KECCAK.Bytes.run 0 bytes171 state171 = (0xf2c79146b7c5d2251888a408d1391aee591ac0f105668159b5638f7ac3c73215 : B256) := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 bytes171 ws = squeeze (KECCAK.f1600 (absorb171 ws)) := by
    rfl
  exact (step state171).trans ((congrArg squeeze
    ((congrArg KECCAK.f1600 words171).trans perm171)).trans finalDigest)

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
