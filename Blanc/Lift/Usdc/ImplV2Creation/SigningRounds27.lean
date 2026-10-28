import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb162 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x7a 0x20 0x65 0x68 0x74 0x20 0x6f 0x74)) 1 (by decide) (UInt64.ofBytes 0x72 0x64 0x64 0x61 0x20 0x6f 0x72 0x65)) 2 (by decide) (UInt64.ofBytes 0x63 0x65 0x52 0x43 0x45 0x73 0x73 0x65)) 3 (by decide) (UInt64.ofBytes 0x6e 0x69 0x20 0x3a 0x72 0x65 0x76 0x6f)) 4 (by decide) (UInt64.ofBytes 0x69 0x73 0x20 0x64 0x69 0x6c 0x61 0x76)) 5 (by decide) (UInt64.ofBytes 0x20 0x65 0x72 0x75 0x74 0x61 0x6e 0x67)) 6 (by decide) (UInt64.ofBytes 0x75 0x6c 0x61 0x76 0x20 0x27 0x76 0x27)) 7 (by decide) (UInt64.ofBytes 0x65 0x6c 0x62 0x61 0x6e 0x77 0x4f 0x65)) 8 (by decide) (UInt64.ofBytes 0x77 0x6f 0x20 0x77 0x65 0x6e 0x20 0x3a)) 9 (by decide) (UInt64.ofBytes 0x74 0x20 0x73 0x69 0x20 0x72 0x65 0x6e)) 10 (by decide) (UInt64.ofBytes 0x20 0x6f 0x72 0x65 0x7a 0x20 0x65 0x68)) 11 (by decide) (UInt64.ofBytes 0x45 0x73 0x73 0x65 0x72 0x64 0x64 0x61)) 12 (by decide) (UInt64.ofBytes 0x70 0x61 0x20 0x3a 0x30 0x32 0x43 0x52)) 13 (by decide) (UInt64.ofBytes 0x6f 0x74 0x20 0x65 0x76 0x6f 0x72 0x70)) 14 (by decide) (UInt64.ofBytes 0x72 0x65 0x7a 0x20 0x65 0x68 0x74 0x20)) 15 (by decide) (UInt64.ofBytes 0x73 0x65 0x72 0x64 0x64 0x61 0x20 0x6f)) 16 (by decide) (UInt64.ofBytes 0x6b 0x6f 0x54 0x74 0x61 0x69 0x46 0x73))

private def absorbed162 : Vector UInt64 25 :=
  #v[0x1055d706b6b89058, 0x34640e3588555fcc, 0xd3c5bade11dba091, 0xb6a36a9d03a17b49, 0x8073a46073c5dddd, 0x445d24aa9b5b66d0, 0x8835b8f79327ad6c, 0x67a6cbb8378911a1, 0x5e072186716eb331, 0x4436986871827f02, 0x466f3f52454d1b2e, 0xb11c3910e9bd0c4c, 0x9418ee2c7beee5e4, 0xa6e64c5c8328e0cc, 0x57dcecd0200629ed, 0x4d928529dd8ce781, 0x10eee147e015575d, 0x29b53455c13e848d, 0xa72270f4c9c2970, 0xfee0aa8670190e98, 0x6c9e7e2f20b444a7, 0xa9da7aab4d565f0, 0xc094b9b78bebf467, 0x6706486fd388a1f3, 0x572dd3b0bd8a24f6]

private theorem words162 : absorb162 state162 = absorbed162 := by
  decide +kernel

private def quarter162_1 : Vector UInt64 25 :=
  #v[0x166a86eec51e087f, 0xa09b2cd4bca3e1f3, 0x99f94ef0df3a1c43, 0x461c315b82b1f562, 0x8f63bbe015abc90e, 0x875f3e14dc944244, 0xa0c600d5f3d7e3b7, 0xf0d341fc46ed69c5, 0x259e958859fb0f6c, 0x1c601bdea5196b0a, 0xb8767d0c46c52c19, 0xe9b8ad16f1151664, 0x24c0d1946e034995, 0x8835693d7005d393, 0xd0fb886792bcf305, 0x168b37821a5ea62f, 0x7ccb3e4083e8203c, 0x4d4b079d6ebc2229, 0xec878fea14ffc0f5, 0x34fd622bb416fe5a, 0x582acd34b9cfd306, 0x884f90ac2dd096d6, 0xd51301214e2bc6af, 0x83e8208055261799, 0xdb089c2fe4566629]

private theorem rounds162_0 : sixRounds 0 (by decide) absorbed162 = quarter162_1 := by
  decide +kernel

private def quarter162_2 : Vector UInt64 25 :=
  #v[0xfde9700612c0350, 0x56c2ed8470bfe01d, 0x3ed057981ad64b00, 0x5d18e62cd9c60ae5, 0xd55651d058e72a6e, 0x1241defae5b15c93, 0xdc96dc6dc452989a, 0x76fd405a6afe2369, 0xb9e4d8b7db2cf26b, 0x974f030c79450eff, 0xa1d349fbd2c1713f, 0x441edcb8ee2765f7, 0x11e6e42175176cc1, 0x21354de65479082b, 0xef26ab64efa8f332, 0xeae1c2ff532959f8, 0xea74a7893a5a8ebc, 0x58645b8137995f11, 0x57b71072f40499fa, 0x29bb734817d97725, 0x8e0b6bf28ea8ee6, 0xf4cd9b199eccd31b, 0xf2a14870dbf0b06d, 0xec14f14f84a75dc5, 0xb7de8ea2f0380eae]

private theorem rounds162_1 : sixRounds 6 (by decide) quarter162_1 = quarter162_2 := by
  decide +kernel

private def quarter162_3 : Vector UInt64 25 :=
  #v[0x24af19c6bdec03bc, 0x1e8d7d031d825894, 0x5c629e87fd83279f, 0x62a959b8699c3ea6, 0xb09a7c3466ab35a6, 0x48775b7c7d13d624, 0x2b34b3715c774f93, 0x40cace2427451284, 0x84043e83fe1f5795, 0x8b5555e4cca4603e, 0x25f14c05ca86a256, 0x5116928ba39d7a2d, 0x383d20bbdc882214, 0x59ec863f191c51c5, 0xf9b7a58f7e92e9d6, 0x55f53ede827a4c01, 0x5e61dc90cd4ac73f, 0x42fd4d3ed759c21a, 0x1fd7624e6ef18f09, 0xdf9dbccad299065e, 0xd2bb1aaf92d1b6aa, 0xc8f8ce5885a52023, 0xc0c200bba88c02e, 0x375f5301eede4a9f, 0xc17816077aff2d6a]

private theorem rounds162_2 : sixRounds 12 (by decide) quarter162_2 = quarter162_3 := by
  decide +kernel

private theorem rounds162_3 : sixRounds 18 (by decide) quarter162_3 = state163 := by
  decide +kernel

private theorem perm162 : KECCAK.f1600 absorbed162 = state163 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds162_0, rounds162_1, rounds162_2, rounds162_3]
  rfl

theorem block162 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes162 ++ tail) state162 =
      KECCAK.Bytes.run 0 tail state163 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes162 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb162 ws)) := by
    rfl
  exact (step state162).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words162).trans perm162))

private def absorb163 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x20 0x77 0x65 0x6e 0x20 0x3a 0x6e 0x65)) 1 (by decide) (UInt64.ofBytes 0x69 0x20 0x72 0x65 0x73 0x75 0x61 0x70)) 2 (by decide) (UInt64.ofBytes 0x65 0x7a 0x20 0x65 0x68 0x74 0x20 0x73)) 3 (by decide) (UInt64.ofBytes 0x65 0x72 0x64 0x64 0x61 0x20 0x6f 0x72)) 4 (by decide) (UInt64.ofBytes 0x61 0x75 0x63 0x73 0x65 0x52 0x73 0x73)) 5 (by decide) (UInt64.ofBytes 0x77 0x65 0x6e 0x20 0x3a 0x65 0x6c 0x62)) 6 (by decide) (UInt64.ofBytes 0x72 0x65 0x75 0x63 0x73 0x65 0x72 0x20)) 7 (by decide) (UInt64.ofBytes 0x20 0x65 0x68 0x74 0x20 0x73 0x69 0x20)) 8 (by decide) (UInt64.ofBytes 0x64 0x64 0x61 0x20 0x6f 0x72 0x65 0x7a)) 9 (by decide) (UInt64.ofBytes 0x74 0x61 0x69 0x46 0x73 0x73 0x65 0x72)) 10 (by decide) (UInt64.ofBytes 0x6d 0x20 0x3a 0x6e 0x65 0x6b 0x6f 0x54)) 11 (by decide) (UInt64.ofBytes 0x75 0x6f 0x6d 0x61 0x20 0x74 0x6e 0x69)) 12 (by decide) (UInt64.ofBytes 0x67 0x20 0x74 0x6f 0x6e 0x20 0x74 0x6e)) 13 (by decide) (UInt64.ofBytes 0x74 0x20 0x72 0x65 0x74 0x61 0x65 0x72)) 14 (by decide) (UInt64.ofBytes 0x43 0x52 0x45 0x30 0x20 0x6e 0x61 0x68)) 15 (by decide) (UInt64.ofBytes 0x6e 0x61 0x72 0x74 0x20 0x3a 0x30 0x32)) 16 (by decide) (UInt64.ofBytes 0x6f 0x6d 0x61 0x20 0x72 0x65 0x66 0x73))

private def absorbed163 : Vector UInt64 25 :=
  #v[0xfcf33664b22259be, 0x68497d7fa1f4e914, 0x158c32b91ca2faf0, 0x9e517a88d6274495, 0x622b1ece0acc3f48, 0x2dde5f24e25f0143, 0x84e52b72b73921b2, 0x7913527a73f8b3a2, 0x357b973696297c7f, 0x65a24249d78d413b, 0xa3c7b198355a3677, 0x1f37f5048c606de, 0xd3f768df6426c578, 0x354fb4d842514843, 0xc7e096ca4da3b88a, 0x9d9917b620652838, 0xe92aaf93b002966d, 0x170343c8688297f3, 0xbc374c5697c4e145, 0xcff342496ddf4334, 0xaff1f05381ec78e9, 0x186808b7ea12756e, 0x3ac3a0f019ceb61f, 0xb47a34c8d38dbfb1, 0xe7d5a06bc838e98e]

private theorem words163 : absorb163 state163 = absorbed163 := by
  decide +kernel

private def quarter163_1 : Vector UInt64 25 :=
  #v[0x9485214c44bfdf56, 0xb7ff5649f95a87b0, 0xfe7541ab83b5f052, 0xcfff4d374295345, 0xdfa24b03c0a37aed, 0x58457a6a74b4228d, 0xfc9d503c7e7953c3, 0x30cd142d1729d7be, 0xfc411f5af7d29aba, 0x7ee0a3e02281b6b8, 0xab75c907f4a8197, 0x2f8312167d9e5ba1, 0x26e2cda275b22bfb, 0xafbba4afaf5e8ad, 0x4c482f80c7eadcc1, 0x83591a5dcb616111, 0x527a72138b3940fa, 0x884e759f51d7783a, 0x6a86bab8192f8a4, 0xb010af896e8ab4f6, 0x34fdb479675091e2, 0xd01daa72088f524, 0xcd7599c0c372a321, 0xf3744b0196dab77f, 0xd6a5d18a89d547f3]

private theorem rounds163_0 : sixRounds 0 (by decide) absorbed163 = quarter163_1 := by
  decide +kernel

private def quarter163_2 : Vector UInt64 25 :=
  #v[0x9295163d17c43b8, 0xc13c696a1344ba9f, 0x413d3e802dcac7b1, 0x302bfce7b3a33aaf, 0x3fd925f6f1bfecf4, 0xe4d643fb44a166f8, 0x858b78113e8c31be, 0xf2fcd38d53d29c56, 0x85d5195a00d4eb1b, 0xf8be595c2fcf2c67, 0x49519dd8bfbd22c2, 0x1386c20091ce9c00, 0xb7deeaab4bd09971, 0xd57aa2e80fda41d3, 0xefbd220052b3a87, 0xe2e1c8d3e16e3f0b, 0xa7bbe3a8e295cd64, 0xd96b00260312a219, 0xf7863c4dd2ea1fb2, 0x796647039de91c41, 0x6e2eed08ca87d23d, 0x8a1e8be8e496fccd, 0x93ea39583dcde5d9, 0x156a600e130a693, 0x136eda320be0b168]

private theorem rounds163_1 : sixRounds 6 (by decide) quarter163_1 = quarter163_2 := by
  decide +kernel

private def quarter163_3 : Vector UInt64 25 :=
  #v[0x3f694ab60e0603b3, 0x38e82e25c7f25206, 0x79d59348ff4519de, 0x74b3393cda3c00e, 0x6db1fd5e3b77880c, 0xc6f68cf7d329abb5, 0xf229d4f8536fe89a, 0x2dc7d0ede199ab2e, 0x3fe2712e82a538d2, 0x6c88decd67e9b84a, 0x4550afe58cae9693, 0xbfd7dbd0e26a747c, 0x4b6cc275bee07422, 0xbbc3af9d9ea82c0e, 0x194cbf9655b873a8, 0x290bae3cc8748b40, 0x213b03bd2e6ce0d8, 0x667b6d4af13653ab, 0x60b764a009112933, 0xfab34304831b1f85, 0x6037c2ad0b34f337, 0x1a5353ef99f953c6, 0x785444eb78e8b472, 0xf8a85575390aef2b, 0xdb81ae6d9bb8bded]

private theorem rounds163_2 : sixRounds 12 (by decide) quarter163_2 = quarter163_3 := by
  decide +kernel

private theorem rounds163_3 : sixRounds 18 (by decide) quarter163_3 = state164 := by
  decide +kernel

private theorem perm163 : KECCAK.f1600 absorbed163 = state164 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds163_0, rounds163_1, rounds163_2, rounds163_3]
  rfl

theorem block163 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes163 ++ tail) state163 =
      KECCAK.Bytes.run 0 tail state164 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes163 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb163 ws)) := by
    rfl
  exact (step state163).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words163).trans perm163))

private def absorb164 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x65 0x63 0x78 0x65 0x20 0x74 0x6e 0x75)) 1 (by decide) (UInt64.ofBytes 0x61 0x6c 0x61 0x62 0x20 0x73 0x64 0x65)) 2 (by decide) (UInt64.ofBytes 0x54 0x74 0x61 0x69 0x46 0x65 0x63 0x6e)) 3 (by decide) (UInt64.ofBytes 0x61 0x63 0x20 0x3a 0x6e 0x65 0x6b 0x6f)) 4 (by decide) (UInt64.ofBytes 0x20 0x73 0x69 0x20 0x72 0x65 0x6c 0x6c)) 5 (by decide) (UInt64.ofBytes 0x20 0x65 0x68 0x74 0x20 0x74 0x6f 0x6e)) 6 (by decide) (UInt64.ofBytes 0x69 0x4d 0x72 0x65 0x74 0x73 0x61 0x6d)) 7 (by decide) (UInt64.ofBytes 0x63 0x61 0x6c 0x42 0x72 0x65 0x74 0x6e)) 8 (by decide) (UInt64.ofBytes 0x6c 0x62 0x61 0x74 0x73 0x69 0x6c 0x6b)) 9 (by decide) (UInt64.ofBytes 0x65 0x6c 0x6c 0x61 0x63 0x20 0x3a 0x65)) 10 (by decide) (UInt64.ofBytes 0x74 0x6f 0x6e 0x20 0x73 0x69 0x20 0x72)) 11 (by decide) (UInt64.ofBytes 0x61 0x6c 0x62 0x20 0x65 0x68 0x74 0x20)) 12 (by decide) (UInt64.ofBytes 0x72 0x65 0x74 0x73 0x69 0x6c 0x6b 0x63)) 13 (by decide) (UInt64.ofBytes 0x65 0x6b 0x6f 0x54 0x74 0x61 0x69 0x46)) 14 (by decide) (UInt64.ofBytes 0x20 0x6e 0x72 0x75 0x62 0x20 0x3a 0x6e)) 15 (by decide) (UInt64.ofBytes 0x65 0x20 0x74 0x6e 0x75 0x6f 0x6d 0x61)) 16 (by decide) (UInt64.ofBytes 0x62 0x20 0x73 0x64 0x65 0x65 0x63 0x78))

private def absorbed164 : Vector UInt64 25 :=
  #v[0x8a18ca0f8bc07d5e, 0xb45b63b8ca337c73, 0x3334d2364530a1a1, 0xd5d69ca158d45566, 0xd301ed38c24f21f4, 0x121bbc56aac0a5bc, 0x543acc142c842ebc, 0x6202cee0ea0dfbd4, 0xe145735e4146da18, 0x26c1027487d33ec7, 0x4bf5f6009d9e79ef, 0xb0858416994903f7, 0x974efb2da9cd18c0, 0x642b2b7219a333c9, 0xd946f6960e92fa0e, 0x2dc4cb5366de942b, 0xc16d4c28be03d357, 0x11834e8c15e18e69, 0xbabbb3ccad77555d, 0x6e533e772a5beb54, 0x949d8eebe88591b, 0x4fe48e928bf4deff, 0x8a0720aad5c0d46c, 0xba7028744a04a0a3, 0x58357dec0f16a3f3]

private theorem words164 : absorb164 state164 = absorbed164 := by
  decide +kernel

private def quarter164_1 : Vector UInt64 25 :=
  #v[0xae742f1f3410afe5, 0xfd4ab862160d81d1, 0x4b05e537211c5720, 0xfd064e4316e69dcb, 0xd05cd5394198e8fc, 0xa320b9f140ee961b, 0xb53ec2dfd6b56c7a, 0xaa531724ca3757dd, 0x5b4067bfff824a48, 0x744840a71af4750a, 0xa701168f0f641991, 0xba5a6e41f5eaa0d5, 0x9183bef8fe7ade99, 0xaa394e2441c0156a, 0x7adbf36cb03e2063, 0x7a793e6f19d1aa53, 0xa3f0b276d405bab4, 0x5bc42c888d77f4b2, 0x575ecb3e1d93e93e, 0xe5c498a45494a1dd, 0xf461509e7a396fa3, 0x569b650065acd34c, 0x5157186d45d77c6a, 0xda2c3d840e87b5be, 0x244fa56b9a7059f1]

private theorem rounds164_0 : sixRounds 0 (by decide) absorbed164 = quarter164_1 := by
  decide +kernel

private def quarter164_2 : Vector UInt64 25 :=
  #v[0x6ac3757df18ef239, 0x70bd149bdd5e7d14, 0xcc0a27765c9aabb, 0xd17d1b33a565c89, 0xee8470b9d8ec1dbb, 0x1cabd84410e4acc5, 0xdc85f69ca3063a05, 0xed8ea4132c9be097, 0xb460f6d69f51a009, 0x3ed0b6126d4d78e0, 0xdd03d9d0d36df893, 0x8836fe0707dffda9, 0xc83795f7853e7d09, 0x199637accf73cf66, 0x69a089ae527f23a6, 0xdf6991b7766113cd, 0x60d9be7eddaf3122, 0x931890c0f1897c27, 0x8e90c802bd604807, 0xf6e85cd66e603c59, 0x74a76692ffcb340b, 0xb8398f6568a64814, 0x92b2f86af6c8def7, 0x8a9ffef4b15803c9, 0xdc03efd99b9e179c]

private theorem rounds164_1 : sixRounds 6 (by decide) quarter164_1 = quarter164_2 := by
  decide +kernel

private def quarter164_3 : Vector UInt64 25 :=
  #v[0x649807d72856db03, 0xfd8ff88f705a95f9, 0xaaf7be6b89de1097, 0x7b7a03ad9b20af4c, 0xd01ef240bce9fdda, 0xd29bbba75b171545, 0xcf91b98a62fa8dd3, 0xc2544190169f70e0, 0x55b8e4bbe4431fd2, 0x9c1c5120e506692d, 0x3e39d93cc60a28c0, 0xfb8b1473b97dbaeb, 0x7c6957b6a014d865, 0x3997897070f967de, 0x4369d355e8b8015b, 0x169b5f1e3c3ae1ff, 0x7cea34cd53dfde45, 0xcabd7bb493ba9e7c, 0xce4605b8b343381a, 0xeb5fd4dbc154dd85, 0xcbdc9a395fee8714, 0x43597ff28a76496b, 0xccaacf0bb25481fc, 0xe80241212ed11383, 0xf179bef6760137cb]

private theorem rounds164_2 : sixRounds 12 (by decide) quarter164_2 = quarter164_3 := by
  decide +kernel

private theorem rounds164_3 : sixRounds 18 (by decide) quarter164_3 = state165 := by
  decide +kernel

private theorem perm164 : KECCAK.f1600 absorbed164 = state165 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds164_0, rounds164_1, rounds164_2, rounds164_3]
  rfl

theorem block164 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes164 ++ tail) state164 =
      KECCAK.Bytes.run 0 tail state165 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes164 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb164 ws)) := by
    rfl
  exact (step state164).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words164).trans perm164))

private def absorb165 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x69 0x46 0x65 0x63 0x6e 0x61 0x6c 0x61)) 1 (by decide) (UInt64.ofBytes 0x3a 0x6e 0x65 0x6b 0x6f 0x54 0x74 0x61)) 2 (by decide) (UInt64.ofBytes 0x20 0x72 0x65 0x6c 0x6c 0x61 0x63 0x20)) 3 (by decide) (UInt64.ofBytes 0x61 0x20 0x74 0x6f 0x6e 0x20 0x73 0x69)) 4 (by decide) (UInt64.ofBytes 0x46 0x72 0x65 0x74 0x6e 0x69 0x6d 0x20)) 5 (by decide) (UInt64.ofBytes 0x6e 0x65 0x6b 0x6f 0x54 0x74 0x61 0x69)) 6 (by decide) (UInt64.ofBytes 0x61 0x6d 0x20 0x77 0x65 0x6e 0x20 0x3a)) 7 (by decide) (UInt64.ofBytes 0x74 0x6e 0x69 0x4d 0x72 0x65 0x74 0x73)) 8 (by decide) (UInt64.ofBytes 0x68 0x74 0x20 0x73 0x69 0x20 0x72 0x65)) 9 (by decide) (UInt64.ofBytes 0x61 0x20 0x6f 0x72 0x65 0x7a 0x20 0x65)) 10 (by decide) (UInt64.ofBytes 0x65 0x52 0x73 0x73 0x65 0x72 0x64 0x64)) 11 (by decide) (UInt64.ofBytes 0x3a 0x65 0x6c 0x62 0x61 0x75 0x63 0x73)) 12 (by decide) (UInt64.ofBytes 0x20 0x72 0x65 0x6c 0x6c 0x61 0x63 0x20)) 13 (by decide) (UInt64.ofBytes 0x74 0x20 0x74 0x6f 0x6e 0x20 0x73 0x69)) 14 (by decide) (UInt64.ofBytes 0x75 0x63 0x73 0x65 0x72 0x20 0x65 0x68)) 15 (by decide) (UInt64.ofBytes 0x3a 0x30 0x32 0x43 0x52 0x45 0x72 0x65)) 16 (by decide) (UInt64.ofBytes 0x65 0x66 0x73 0x6e 0x61 0x72 0x74 0x20))

private def absorbed165 : Vector UInt64 25 :=
  #v[0x1274b88091d67a68, 0xb5f0fc134f46825b, 0xa5ffc662c20f7cc7, 0x3cb9092e3aa25132, 0x8314e44618b1d225, 0xddd8b3145384dcef, 0x398b37c441a89c74, 0x77b61de88a9d9695, 0xbb1c27b262087b18, 0x491cfa4fbe3b5d9d, 0x41feaa17c70c8c14, 0xc01745345163171b, 0xe726234e5e06fa31, 0x3380eaa65392a44, 0x22a11bd3f66d819e, 0x819045ce1d2ecc09, 0xd8d60d18ef81fe84, 0xd5ed2e829baaea9, 0x937f300ab570aef2, 0x7b92a741ed3cfbf2, 0xf7f18e413746b85c, 0x4f0fb2ddf9192bc7, 0xb9cac4e6f2dc9d5e, 0x21905e8a3d6d5390, 0x9879cdf3b02d7d09]

private theorem words165 : absorb165 state165 = absorbed165 := by
  decide +kernel

private def quarter165_1 : Vector UInt64 25 :=
  #v[0xc62ca5092d0f682f, 0xb7e1fb3c53adb4cd, 0x695ece45e6dee2a7, 0xaea9a7d00f67aa92, 0x1c7cade70a2447a0, 0xfb48744a08269e5b, 0x346cbb13c932b960, 0x9c6f2c5737d44a9c, 0xb57d68b587ddb738, 0x35d237986633cf26, 0x3455fdf3ceb73f55, 0x9638b22d37b38a7a, 0xecce3cd2c09f9ae3, 0xa5eabe44736b47e1, 0x722178163c5ca78, 0x8d262717559b57ea, 0x34b24e5b920415fa, 0xbd04f5d583645e09, 0x591da49ff92ba30e, 0x19d5298ad39961ee, 0xae9901b311255b0b, 0x7e924c185ce63ca8, 0xb138d027505ee381, 0x36f4589a2c249a8f, 0xae624633da505196]

private theorem rounds165_0 : sixRounds 0 (by decide) absorbed165 = quarter165_1 := by
  decide +kernel

private def quarter165_2 : Vector UInt64 25 :=
  #v[0xd1e43b1ac5a67daa, 0xa93d2eb4087427e0, 0x9c61d78abb9796f8, 0xc52f84382a96a4b6, 0x5799809da02040ef, 0x7a18c501d556a567, 0xece6d1f3ff84a9e6, 0x513a2509843d5ad4, 0x63a264e2aa86c116, 0x6f38c069aa2d700, 0x84e029826ff21073, 0x2561126e51263eda, 0x9e7bee53a6583d3e, 0xea5559b8217cdc54, 0x69e445cae66b1f62, 0x53290e690a6041b4, 0xba5cf05ce2c8f92, 0x7fec5c85417d63fe, 0x4692e015f1c20856, 0xd3f292368ad93832, 0x1d4918a700e78c, 0x11a8cf98d9d926ed, 0x494e946172107659, 0x4754158cd98d9ab0, 0x9284df44279e3416]

private theorem rounds165_1 : sixRounds 6 (by decide) quarter165_1 = quarter165_2 := by
  decide +kernel

private def quarter165_3 : Vector UInt64 25 :=
  #v[0xb5c2a5145e46c61c, 0xc88038a364eed5cf, 0x369fecf7cacac3db, 0xbd6dc5c0c561ea09, 0x84a37cec214d866c, 0xf109d386cd37e245, 0x771b680c4ed006ea, 0x4a70da1cb930d620, 0x69c42c99a52e1393, 0x369e0fbc8dcad266, 0x45a17117a1c7c358, 0xc8f35a7a05e2afd3, 0xca41fda09fe049a5, 0x8e1a107dc8891e8f, 0xb8acb1448ea90533, 0x9498e4e216c5609d, 0xc048beb5207f5591, 0x6714820ef9759e3c, 0x3b70713f5cf5969c, 0x9f9789f5e86a37e5, 0x8f45f0a5b6db1714, 0x1c9b61c56a0f3e77, 0xfde96462701d26ae, 0x15a040d1dafa4972, 0xb3d272e039b33e4]

private theorem rounds165_2 : sixRounds 12 (by decide) quarter165_2 = quarter165_3 := by
  decide +kernel

private theorem rounds165_3 : sixRounds 18 (by decide) quarter165_3 = state166 := by
  decide +kernel

private theorem perm165 : KECCAK.f1600 absorbed165 = state166 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds165_0, rounds165_1, rounds165_2, rounds165_3]
  rfl

theorem block165 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes165 ++ tail) state165 =
      KECCAK.Bytes.run 0 tail state166 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes165 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb165 ws)) := by
    rfl
  exact (step state165).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words165).trans perm165))

private def absorb166 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x74 0x6e 0x75 0x6f 0x6d 0x61 0x20 0x72)) 1 (by decide) (UInt64.ofBytes 0x73 0x64 0x65 0x65 0x63 0x78 0x65 0x20)) 2 (by decide) (UInt64.ofBytes 0x6e 0x61 0x77 0x6f 0x6c 0x6c 0x61 0x20)) 3 (by decide) (UInt64.ofBytes 0x6f 0x54 0x74 0x61 0x69 0x46 0x65 0x63)) 4 (by decide) (UInt64.ofBytes 0x77 0x65 0x6e 0x20 0x3a 0x6e 0x65 0x6b)) 5 (by decide) (UInt64.ofBytes 0x69 0x6c 0x6b 0x63 0x61 0x6c 0x62 0x20)) 6 (by decide) (UInt64.ofBytes 0x20 0x73 0x69 0x20 0x72 0x65 0x74 0x73)) 7 (by decide) (UInt64.ofBytes 0x6f 0x72 0x65 0x7a 0x20 0x65 0x68 0x74)) 8 (by decide) (UInt64.ofBytes 0x73 0x73 0x65 0x72 0x64 0x64 0x61 0x20)) 9 (by decide) (UInt64.ofBytes 0x65 0x6b 0x6f 0x54 0x74 0x61 0x69 0x46)) 10 (by decide) (UInt64.ofBytes 0x72 0x74 0x6e 0x6f 0x63 0x20 0x3a 0x6e)) 11 (by decide) (UInt64.ofBytes 0x61 0x20 0x73 0x69 0x20 0x74 0x63 0x61)) 12 (by decide) (UInt64.ofBytes 0x69 0x20 0x79 0x64 0x61 0x65 0x72 0x6c)) 13 (by decide) (UInt64.ofBytes 0x7a 0x69 0x6c 0x61 0x69 0x74 0x69 0x6e)) 14 (by decide) (UInt64.ofBytes 0x6f 0x54 0x74 0x61 0x69 0x46 0x64 0x65)) 15 (by decide) (UInt64.ofBytes 0x63 0x20 0x3a 0x32 0x56 0x6e 0x65 0x6b)) 16 (by decide) (UInt64.ofBytes 0x20 0x74 0x63 0x61 0x72 0x74 0x6e 0x6f))

private def absorbed166 : Vector UInt64 25 :=
  #v[0x82d04d0e444b125b, 0x36767534af4f3e6f, 0x696f883acd5a7df8, 0xd95c3060c82d52a8, 0x88812dced3c6f634, 0xd85489ca2f29fc7b, 0xc1a2b08b6bf3f5aa, 0xd13a95cd41740ddb, 0x5c683aad3853fd2b, 0x75965e9c870bf956, 0xdc2a0b32488778c1, 0x21a8e18fc48f6fcc, 0x8558689a4bafa053, 0xab85260f1c648105, 0x1d3af7261a39f5ee, 0x99a581194cc86bcc, 0xebcd161ea7ae71d3, 0x54cb20cd7978d20e, 0x472636aaa1820a3a, 0x46893d6ede4f2189, 0xe4b4b7e2511864fa, 0x64b8132fa024f85b, 0xdf79875eee051843, 0xb4d48813a0617135, 0xee89f2d5ade17490]

private theorem words166 : absorb166 state166 = absorbed166 := by
  decide +kernel

private def quarter166_1 : Vector UInt64 25 :=
  #v[0xc7b2e2561c626aa9, 0x4be78b5912e73094, 0x1a718275330e08a7, 0x9b129e3ea78f4237, 0x34b7cb51a5133f1b, 0xd5d4342406999e6d, 0x3fc3df7223d4003d, 0x6084c64c6e236d7a, 0x91b8b59817507970, 0xf51d7c7a9ef41ffb, 0x3afa6144666761e0, 0xd9945c49d860070f, 0xa17bdeae3876bf0, 0x55781c16f63cf628, 0xae83bc42c8d9ac8c, 0xf5b187a2ff959806, 0xfa8d4e681a5ba159, 0x97a947d7c3dc9734, 0x959511b784f97e98, 0x4bd8edf85c33fae2, 0x6177e2c6248eba15, 0x952a6eb7cf85e571, 0x1575dc8d886edf9c, 0x98eb4f08a8b304cf, 0x93beeb51de536c6]

private theorem rounds166_0 : sixRounds 0 (by decide) absorbed166 = quarter166_1 := by
  decide +kernel

private def quarter166_2 : Vector UInt64 25 :=
  #v[0x9825b1d410e4d613, 0xc5dab90e3945b815, 0x22e0f9734023afc, 0x86a3209524e88b3a, 0x9c4e77330b845716, 0x52a5dc7474650286, 0x7aac46f0d99eb7d4, 0xb43e159518390e4e, 0x4809a710b4bd5afa, 0x1c42828ed100696d, 0xbaeb6c9114b7d3ba, 0xefda5cdae9d37a5d, 0x8c18f3cd3ca3c808, 0x63074f7049ff9611, 0x8b9499293f1d8c1e, 0xa42cc0c2f3a6f67b, 0x674cc3554ac3540e, 0x76531bf6d84bb7d, 0x9aecac1a213268bf, 0x2d7f18b48585cd0f, 0xd1fba1d8c64536ff, 0x1f8b55825796ac3d, 0x338c70f43c0bb586, 0xfd5d137dfa13c326, 0x9868dd6cd8070e38]

private theorem rounds166_1 : sixRounds 6 (by decide) quarter166_1 = quarter166_2 := by
  decide +kernel

private def quarter166_3 : Vector UInt64 25 :=
  #v[0xebbecfae74750730, 0x88a099e9059cad86, 0x3ed38301acda6a91, 0x70802191b0280da9, 0x8c556fa0bb99869c, 0x9f62004581879ef, 0x653963f1ae26902d, 0x4833a08c8418a5f5, 0x5a8e4a69079cb92e, 0x579f6b5fa99eace8, 0xc9aab9bf7a836f02, 0x5134502610bad120, 0x518ded18fc6193d9, 0x8ad2f769194f16b1, 0xaf098c0eab30d7f2, 0xaac248e2d9d8152e, 0xf0a1a14003f1880a, 0x172037ab297d36d4, 0x8e1e6d495c4b6607, 0xa2ec216d87d040e4, 0xf7e69e8d0386d3c0, 0x1fbca95982a191cc, 0x470be170e4c6fbf5, 0x2f9d969589579254, 0xf2840aa69244c52f]

private theorem rounds166_2 : sixRounds 12 (by decide) quarter166_2 = quarter166_3 := by
  decide +kernel

private theorem rounds166_3 : sixRounds 18 (by decide) quarter166_3 = state167 := by
  decide +kernel

private theorem perm166 : KECCAK.f1600 absorbed166 = state167 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds166_0, rounds166_1, rounds166_2, rounds166_3]
  rfl

theorem block166 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes166 ++ tail) state166 =
      KECCAK.Bytes.run 0 tail state167 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes166 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb166 ws)) := by
    rfl
  exact (step state166).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words166).trans perm166))

private def absorb167 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x61 0x65 0x72 0x6c 0x61 0x20 0x73 0x69)) 1 (by decide) (UInt64.ofBytes 0x69 0x74 0x69 0x6e 0x69 0x20 0x79 0x64)) 2 (by decide) (UInt64.ofBytes 0x52 0x45 0x64 0x65 0x7a 0x69 0x6c 0x61)) 3 (by decide) (UInt64.ofBytes 0x61 0x72 0x74 0x20 0x3a 0x30 0x32 0x43)) 4 (by decide) (UInt64.ofBytes 0x72 0x66 0x20 0x72 0x65 0x66 0x73 0x6e)) 5 (by decide) (UInt64.ofBytes 0x7a 0x20 0x65 0x68 0x74 0x20 0x6d 0x6f)) 6 (by decide) (UInt64.ofBytes 0x72 0x64 0x64 0x61 0x20 0x6f 0x72 0x65)) 7 (by decide) (UInt64.ofBytes 0x30 0x32 0x43 0x52 0x45 0x73 0x73 0x65)) 8 (by decide) (UInt64.ofBytes 0x76 0x6f 0x72 0x70 0x70 0x61 0x20 0x3a)) 9 (by decide) (UInt64.ofBytes 0x74 0x20 0x6d 0x6f 0x72 0x66 0x20 0x65)) 10 (by decide) (UInt64.ofBytes 0x20 0x6f 0x72 0x65 0x7a 0x20 0x65 0x68)) 11 (by decide) (UInt64.ofBytes 0x46 0x73 0x73 0x65 0x72 0x64 0x64 0x61)) 12 (by decide) (UInt64.ofBytes 0x6e 0x65 0x6b 0x6f 0x54 0x74 0x61 0x69)) 13 (by decide) (UInt64.ofBytes 0x61 0x20 0x74 0x6e 0x69 0x6d 0x20 0x3a)) 14 (by decide) (UInt64.ofBytes 0x78 0x65 0x20 0x74 0x6e 0x75 0x6f 0x6d)) 15 (by decide) (UInt64.ofBytes 0x69 0x6d 0x20 0x73 0x64 0x65 0x65 0x63)) 16 (by decide) (UInt64.ofBytes 0x6f 0x6c 0x6c 0x41 0x72 0x65 0x74 0x6e))

private def absorbed167 : Vector UInt64 25 :=
  #v[0x9fbd316610bd7ef4, 0x8de92a70ce0d5819, 0x1da8c06b9689e53f, 0xa298faf7aff8fd8b, 0xc22fec93570fd0d3, 0x873e14b50b92ed0, 0x4c228bae09190f74, 0x1413efdb5246eca0, 0x9d4d604d31bb1f53, 0xe60bcd0725247123, 0x3b8a407065e2c7b4, 0x328fdc53b6209f12, 0x945bd91e85ce9f74, 0xecb0caba1bf72d45, 0x5781b9621db630e0, 0xf66aa952b4130c0e, 0x7cec65b189077026, 0xa843cb1773b389f6, 0x48529c1452d506c7, 0xa1ee6ddf63d6f0b1, 0xca89d012fc4aac2b, 0x2e227d22394e6535, 0x7ce3079e3ee2fc83, 0xc6a529602f3547f, 0x2b2a1be00613c4b6]

private theorem words167 : absorb167 state167 = absorbed167 := by
  decide +kernel

private def quarter167_1 : Vector UInt64 25 :=
  #v[0xa19e59614e587d03, 0x2cab410f8241e0e5, 0x2be8bbfdff09ce4b, 0xb37baaacf8fb0ee6, 0x333dcac792d2a80b, 0x8fb4504cb3493671, 0xae2aef58962b1438, 0xfdccc03516680468, 0x3d6fc782345641d6, 0xffc8deb2943925a3, 0x74bc6a04c91ef606, 0xac9a8ada9b1c78ce, 0x3554bc88dbfa19ee, 0xc134700caba7d5d3, 0xc90fed06116a70a3, 0xa4a399c3ae8ae89c, 0x4e9e7dbf0df27f9b, 0x62f70d2616eb8773, 0xfc5c8d8ffec067eb, 0x9a6bc7df1d281fc6, 0xdace48954b08b573, 0x72007d1f0f0eeacb, 0xb0c27452c7cbaecf, 0xe26a12975295734, 0x6da48aac10d6f17b]

private theorem rounds167_0 : sixRounds 0 (by decide) absorbed167 = quarter167_1 := by
  decide +kernel

private def quarter167_2 : Vector UInt64 25 :=
  #v[0x81c893d0c357eb93, 0x34cb4f45d54c522, 0x3851cab712aadac, 0xf306924856afdc06, 0xb8ef60d139ff46fd, 0xa670654cd88af698, 0x88437b64a3027bc, 0xe4fa9b2c6a40a1a6, 0x6cc23dcf3e03ef30, 0xc896a6ee9169823f, 0x4387617081eb39de, 0x2ce61427d098c135, 0x39682884c1f0d551, 0xa487ddef31a1039a, 0xd38543fbe7396f1, 0xe2956b5b476b0b97, 0x21b0ec387de0a1f7, 0x48fb1347500c9b6f, 0xe01a7faa7bdacbd0, 0x2098b4c2c484aad, 0x3ea63dac657084e4, 0x70a7bba13476c794, 0x6b19585bc731f33, 0xdf01368ba572e6b3, 0xa536e65b4e6e3084]

private theorem rounds167_1 : sixRounds 6 (by decide) quarter167_1 = quarter167_2 := by
  decide +kernel

private def quarter167_3 : Vector UInt64 25 :=
  #v[0x3f85410b665dddb0, 0xcf152b91412b3e4, 0x6b0e10e7e9f93ff1, 0xe353ea14d8990ca, 0xd29093456c77735e, 0xceba7a154df90e10, 0xd32a368fb94d0fe6, 0xa4954ddcd7599f2b, 0x4c80e6cb81fe1b60, 0xe9b9152e1683783a, 0xc946c8e95f73d472, 0xd81a7b1ce1fb029b, 0x8ceb12c59841ed86, 0xf7244b199459a492, 0xfcbe8a6b1f2f384a, 0xc976858720ae43ba, 0x13cf8d09ae92b247, 0x7c7a73cbf33c8944, 0x1b908fa8fd541adf, 0x127e7414552156ba, 0xd1c12a0f19be7fca, 0x3a642649d2a7736e, 0x8d2272cb2d90a60a, 0x9fbaaf8a30fae3cd, 0xdeafd3c06b70623a]

private theorem rounds167_2 : sixRounds 12 (by decide) quarter167_2 = quarter167_3 := by
  decide +kernel

private theorem rounds167_3 : sixRounds 18 (by decide) quarter167_3 = state168 := by
  decide +kernel

private theorem perm167 : KECCAK.f1600 absorbed167 = state168 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds167_0, rounds167_1, rounds167_2, rounds167_3]
  rfl

theorem block167 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes167 ++ tail) state167 =
      KECCAK.Bytes.run 0 tail state168 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes167 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb167 ws)) := by
    rfl
  exact (step state167).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words167).trans perm167))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
