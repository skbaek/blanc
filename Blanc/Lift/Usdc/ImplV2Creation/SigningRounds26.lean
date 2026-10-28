import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb156 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x57 0xa2 0x52 0x61 0x10 0x83 0x20 0x60)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x7f 0x52 0x82 0x51 0x80)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x1 0x92 0x90 0xe0 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x1 0x91 0x1 0x82 0x91 0x20 0x60 0x91)) 7 (by decide) (UInt64.ofBytes 0x83 0x1 0x60 0x5b 0x56 0x65 0x52 0x61)) 8 (by decide) (UInt64.ofBytes 0x3 0xa 0x0 0x1 0x61 0x3 0x20 0x60)) 9 (by decide) (UInt64.ofBytes 0x51 0x84 0x81 0x16 0x51 0x82 0x19 0x80)) 10 (by decide) (UInt64.ofBytes 0x50 0x50 0x52 0x85 0x17 0x82 0x80 0x16)) 11 (by decide) (UInt64.ofBytes 0x91 0x1 0x50 0x90 0x50 0x50 0x50 0x50)) 12 (by decide) (UInt64.ofBytes 0x80 0x51 0x40 0x60 0x0 0x60 0x50 0x50)) 13 (by decide) (UInt64.ofBytes 0x92 0xf1 0x5a 0x87 0x85 0x81 0x3 0x83)) 14 (by decide) (UInt64.ofBytes 0x81 0x0 0x60 0x80 0x3d 0x50 0x50 0x50)) 15 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x57 0x4 0x53 0x61 0x14)) 16 (by decide) (UInt64.ofBytes 0x3d 0x3f 0x60 0x19 0x1f 0x60 0x50 0x91))

private def absorbed156 : Vector UInt64 25 :=
  #v[0x803bf1b59c4e366f, 0x6893d51abf1000c9, 0x744231df78e75cf7, 0xf41802485f35f91d, 0xd68f88cff3f45f85, 0xc9a23b89fcf31e75, 0x3a40815c713bd35f, 0x720be5c27414eebf, 0x8e27e23438a51344, 0x92f166bd7435287e, 0x1ebadb6768a71748, 0x32a6fee829ea4d6c, 0x925952ff26ef6c1d, 0xbf716556a9591ed, 0xf5f2d50fd05a6b56, 0x8d8c1fe9010483c, 0x76fc26d0d6ed2d0f, 0x868e8f13812a3e39, 0xaaf17ce748a49c85, 0xa39651ff711dc425, 0x3c4e1d9e448d9a4f, 0xcee775cd79ca470, 0x28634fe34d65bbce, 0xff9c79df80b4bc06, 0xf79c06f8a0a2bdca]

private theorem words156 : absorb156 state156 = absorbed156 := by
  decide +kernel

private def quarter156_1 : Vector UInt64 25 :=
  #v[0x4a08304fdf18ff5c, 0x52e85e2a4397a21b, 0xa230252dae2f9f7d, 0x36aa088128f4383d, 0xcfdfa4c1e879ac1e, 0xa22931ceab2047df, 0x63b9a458055f951a, 0x9910571b6e7c8e3d, 0x2924f4a973796e5a, 0xc607886f4514b8a, 0x3e5c736b709dd415, 0x80755e31fe230c62, 0xcf438d51c3878ed7, 0x2d4ee2ac77378e8c, 0x77aa68b0f934d4ef, 0x6103d7a08bc6bffe, 0x46d109b3787fba21, 0x5cd5af8d1a2bd75, 0x81d5f0a41175a5f8, 0xf2fedd13e74319a2, 0xca3d98e6d9259105, 0xf68dcb464c87b5b4, 0x5938690dddbb3229, 0x71cffd3577badd8, 0x7c8d4f9117823c30]

private theorem rounds156_0 : sixRounds 0 (by decide) absorbed156 = quarter156_1 := by
  decide +kernel

private def quarter156_2 : Vector UInt64 25 :=
  #v[0x117c05b221a50c70, 0x16059836da773edf, 0xf0aec9e98deff1ab, 0xdbb11d620eb0adf5, 0x34c4011c35740e20, 0x71be4cae10ca1353, 0x8f6dd0018e6c5e5a, 0x706683336acba0ed, 0x55cc89e701ad8408, 0x63356900f5ced8b9, 0xa80eb8a6ce048438, 0x908078ac3f35b17f, 0x919984556f0c6998, 0x307d3a6e4a750aa9, 0xc076e4fd48e2a276, 0x8694d6713e05027e, 0x46ce5620c72f4080, 0xe18727349bd8e932, 0x2582621dd393e15, 0xa565f2f35551d5ef, 0x7832fccc56dc24ba, 0xc8b8ed89b9cf57ef, 0xc0f492e0d0c50d11, 0x19d35b33b35daf40, 0xc1a8d996955446f9]

private theorem rounds156_1 : sixRounds 6 (by decide) quarter156_1 = quarter156_2 := by
  decide +kernel

private def quarter156_3 : Vector UInt64 25 :=
  #v[0x4509d0b61a3d1922, 0xb07bd790eece3718, 0x4cdff506685f32fb, 0x7dba903f47f16620, 0x6fa07c0e2d221c41, 0xede5a9506d1fca8, 0xf7e12ac9fdd13dd3, 0x6742edc1b7bbe890, 0xac960b97f4ddbc04, 0x56d12ac8f7b7a6dd, 0x216987a33d2211fc, 0x95bc9cf1b0ed283f, 0x84a59f2352be1a46, 0xd1741bca8518b790, 0x98234f094eec5c50, 0x40e7031fc07ffc9a, 0xe9fb57331bc23a66, 0x9859f158b25c946c, 0xabc60f2ce6629372, 0x58069c2641bcf6d7, 0x7e25ddd6f201cc70, 0x47b623f64904b33d, 0xa54b9fb28a1ca85d, 0xba2f88f40e796465, 0xe4c5180225bca8a2]

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
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes156 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb156 ws)) := by
    rfl
  exact (step state156).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words156).trans perm156))

private def absorb157 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x3d 0x52 0x40 0x60 0x1 0x82 0x16 0x1)) 1 (by decide) (UInt64.ofBytes 0x84 0x20 0x60 0x0 0x60 0x3d 0x52 0x82)) 2 (by decide) (UInt64.ofBytes 0x60 0x5b 0x56 0x9 0x53 0x61 0x3e 0x1)) 3 (by decide) (UInt64.ofBytes 0x91 0x50 0x91 0x50 0x5b 0x50 0x91 0x60)) 4 (by decide) (UInt64.ofBytes 0x91 0x57 0x1d 0x53 0x61 0x15 0x81 0x50)) 5 (by decide) (UInt64.ofBytes 0x5b 0x56 0x50 0x90 0xb0 0x51 0x61 0x50)) 6 (by decide) (UInt64.ofBytes 0x80 0x57 0x2d 0x53 0x61 0x15 0x51 0x80)) 7 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x1 0x20 0x60 0x82 0x80 0x51)) 8 (by decide) (UInt64.ofBytes 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x40 0x60)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x0 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x86 0x52 0x81 0x81 0x1 0x82 0x4 0x60)) 14 (by decide) (UInt64.ofBytes 0x51 0x86 0x52 0x1 0x84 0x24 0x60 0x51)) 15 (by decide) (UInt64.ofBytes 0x44 0x60 0x92 0x83 0x92 0x91 0x93 0x87)) 16 (by decide) (UInt64.ofBytes 0x83 0x80 0x90 0x1 0x85 0x90 0x91 0x1))

private def absorbed157 : Vector UInt64 25 :=
  #v[0xadb267f8f28712ad, 0xea1ba7aa5977f343, 0xc9907b24608b1d40, 0x1cf400e8cc7f5f27, 0xda988199c2a68c57, 0xec0624de4de5c854, 0x5e8e9b618618be42, 0x595262b601899aea, 0xf1a0a6023b08a9b9, 0x6b961afe4e14cb1b, 0x27e9d19f8181401a, 0xda0a175359ef3e88, 0xb80128f7043293ba, 0x94c13ec7d0e849b9, 0xbfb19f40967236ee, 0x903dd527f7c82043, 0x24fc1c6c0fefdc5a, 0x54a09fc19cf968fe, 0xe388ba0d70d80869, 0xdcc3930befc13a1a, 0xbc6177d1663d4537, 0x4d90ccd55ecfc8dc, 0x22f022d91d3788e8, 0x50bb17ce4e126831, 0x4daf8772b3ce9f95]

private theorem words157 : absorb157 state157 = absorbed157 := by
  decide +kernel

private def quarter157_1 : Vector UInt64 25 :=
  #v[0x51961b72ab4d757c, 0x171c86008b10682f, 0x2a1b7d1f89137187, 0x8f30d792786df16, 0x788b5de46d5dddbb, 0x4f16c14667eba55a, 0x92cac60123604ae9, 0x81a2d9c06edd7aed, 0x1c1b43b33f74ba8c, 0x113113212140e4b, 0x32a21dbbf877f675, 0xd4a376e9dad59a08, 0xff2210ab862021a1, 0x7ccdd4f641cff639, 0x5e574f5223054fd6, 0xe9f07165aec74dc3, 0x9b2d57f0cb14130a, 0xde6a11483c8625b8, 0xf7a30faba88cf935, 0xad1cbfa4de130729, 0xa7c73d2805393059, 0xae867e4b73cf358f, 0xac2e0cf3be6dafae, 0xbf8c0c231faa62c7, 0x6b63f9b2db55cc5]

private theorem rounds157_0 : sixRounds 0 (by decide) absorbed157 = quarter157_1 := by
  decide +kernel

private def quarter157_2 : Vector UInt64 25 :=
  #v[0x27e6044ceb1bf08f, 0x5783029e38a50e3f, 0x659c41d35462a1cf, 0xaa2d4d7acd30fe44, 0x2a5df211d1d563c8, 0x90ba48e456d1840e, 0xe9b0c381e7470163, 0xd459d2b95afea23d, 0xd5b3da5b2376ea18, 0xc2f3fdb20ee9a9cf, 0xe699ae7a738964a6, 0x70d1776a49a96e3f, 0x7a1e6cf6ae273bef, 0x79e3287d406e07c1, 0x7e12ee79ec424bf8, 0x876971b5c56c4693, 0x86eb889392e1bfce, 0x115c351d9459ea7f, 0x5cf799ac487441c2, 0x52d0786a4c80fff, 0xcb5c1b236e09f63c, 0x303584e5834c8746, 0xf8da2d7a72b5f89b, 0x7a5a9b67b57cfc4c, 0xf9c5a228c0d833fd]

private theorem rounds157_1 : sixRounds 6 (by decide) quarter157_1 = quarter157_2 := by
  decide +kernel

private def quarter157_3 : Vector UInt64 25 :=
  #v[0xa8b600e3666882fd, 0xf7b6e33da0da3e79, 0x3b64f5f94090de7, 0xe9c6c2ec553be971, 0x9089961c1be3b9c7, 0x997266bfc385e280, 0x2d6cd0ab491c3fc6, 0x722660040c6e35e9, 0xd36a845c799b927f, 0x3e78044a429a778f, 0x7bdf5dcf024bde32, 0xeb25863fb7234a0d, 0x6c32a65bf64d6d4d, 0x22a7422be37f46e3, 0xf1249f7c0ea39b2b, 0xebafca0d13793541, 0x2320059a6023f6d9, 0xb7ff87a98e5c12c1, 0x923db0ee0c31f0f4, 0x48530ed66ddca7e9, 0x5d3997f0ce673628, 0xe46c2b8d7b826559, 0x75c2660398e5df68, 0x50600825055ad045, 0xc56b307df567eed4]

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
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes157 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb157 ws)) := by
    rfl
  exact (step state157).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words157).trans perm157))

private def absorb158 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x50 0x4c 0x61 0x15 0x83 0x0 0x60 0x83)) 1 (by decide) (UInt64.ofBytes 0x1 0x82 0x83 0x51 0x1 0x81 0x81 0x57)) 2 (by decide) (UInt64.ofBytes 0x56 0x38 0x4c 0x61 0x1 0x20 0x60 0x52)) 3 (by decide) (UInt64.ofBytes 0xd2 0xc5 0x7f 0x3f 0x81 0x0 0x60 0x5b)) 4 (by decide) (UInt64.ofBytes 0x7e 0x92 0x3c 0x23 0xf7 0x86 0x1 0x46)) 5 (by decide) (UInt64.ofBytes 0x0 0xe5 0xc0 0x3 0xc7 0xdc 0xb2 0x7d)) 6 (by decide) (UInt64.ofBytes 0xfa 0x7b 0x3b 0x27 0x82 0xca 0x53 0xb6)) 7 (by decide) (UInt64.ofBytes 0x81 0x81 0x70 0xa4 0x85 0x5d 0x4 0xd8)) 8 (by decide) (UInt64.ofBytes 0x57 0xb0 0x51 0x61 0x90 0x15 0x80 0x14)) 9 (by decide) (UInt64.ofBytes 0x50 0x50 0x91 0x92 0x15 0x15 0x50 0x50)) 10 (by decide) (UInt64.ofBytes 0x81 0x1 0x60 0x54 0x80 0x82 0x5b 0x56)) 11 (by decide) (UInt64.ofBytes 0x2 0x0 0x1 0x61 0x15 0x16 0x1 0x60)) 12 (by decide) (UInt64.ofBytes 0x60 0x90 0x4 0x90 0x2 0x60 0x16 0x3)) 13 (by decide) (UInt64.ofBytes 0x90 0x20 0x0 0x60 0x20 0x60 0x52 0x0)) 14 (by decide) (UInt64.ofBytes 0x81 0x4 0x90 0x20 0x60 0x1 0x1f 0x60)) 15 (by decide) (UInt64.ofBytes 0x54 0x61 0x10 0x1f 0x60 0x82 0x92 0x1)) 16 (by decide) (UInt64.ofBytes 0x16 0x19 0xff 0x60 0x51 0x80 0x57 0x8))

private def absorbed158 : Vector UInt64 25 :=
  #v[0x8bdbc1e1f8015d98, 0x54771bf864b81aa2, 0x50cb29e377823041, 0xe1f999495bfb3b0a, 0x695890d1c3b76119, 0x6cf48cad03067fce, 0x35d57cff2165a837, 0x2d6e7dfa0f19e15a, 0x851983aee9439514, 0x1fbd81bbc875c5e3, 0xb263a382038fd3c1, 0xbf47deca659ad90, 0xd2fec72d0f9a2681, 0xcaa467a89ad254ae, 0x1950d2a5fad2a1f4, 0x4bb480b27d683d30, 0xd62b1c784f8ea45f, 0x2ab56236cf805665, 0x70cfbe747d6bd731, 0x2d6511371d49dee, 0x1302d81adeb0ab21, 0xdd5406c820bfdb31, 0x8f0ee63c9fe03961, 0x54b3aef63a9cb3dc, 0xc0e56cc9babf8e98]

private theorem words158 : absorb158 state158 = absorbed158 := by
  decide +kernel

private def quarter158_1 : Vector UInt64 25 :=
  #v[0x78329a7ee01a8129, 0x3e3b4bbc0841a42, 0xb67073ebe34b213d, 0x7f477ecdc8e46e60, 0x194c03ec515087ab, 0x8766c1ac4b0d65bf, 0xcef88b84d30bc28, 0x2c14f85f1d9570b0, 0x2ef31999764db57, 0x7eec9d570d3ceb83, 0x87628b8254545545, 0xada48f8fa15f3c6d, 0x808a54a18604c88e, 0xaa7a48ed37efb3a6, 0x701861f93467954d, 0xdacb87b668051e1, 0xa83a70975be49bda, 0x3d406ed33582b76e, 0x2a7a17c29af42ad9, 0xdd5b5d57918b82a7, 0x3d5c9c162cb6599d, 0x20847005de581eca, 0x2f61065cbcd6d5c8, 0x33e216e65cdc3e12, 0x875555b2f1548ad2]

private theorem rounds158_0 : sixRounds 0 (by decide) absorbed158 = quarter158_1 := by
  decide +kernel

private def quarter158_2 : Vector UInt64 25 :=
  #v[0x30fc868269ba2949, 0x9890da32adecf735, 0xdef2e4e9fd25bcd9, 0x55c644195162b184, 0x83970b40e5c802c3, 0x5b6e5150ae66abaf, 0xbe1b9cee26f4323d, 0xd4d1815a7233af04, 0x9a7dcd7b2c1e5248, 0x5436281930b07bd2, 0xe6d0695521780105, 0xb368a7aa6d349dd7, 0x30b9a0b1a702f786, 0x501f734cb5c4eb6c, 0x7a60707f3d3c0c79, 0xd20f790cb8a3f922, 0xb1428ca4fd972356, 0x26f0b1eacb4c8d98, 0x87e6e75b367c1a9f, 0xe6af79b0db3e0e97, 0x6c9e2d5eac22b6c1, 0x12257ac11bbf8cc, 0xcf07e075df3eecff, 0x935ed52e2d4c01f1, 0x54c61b6dc55ca317]

private theorem rounds158_1 : sixRounds 6 (by decide) quarter158_1 = quarter158_2 := by
  decide +kernel

private def quarter158_3 : Vector UInt64 25 :=
  #v[0xf8de89fe30e1be5d, 0xe610b5c29312c0b4, 0x97c984c7db813e22, 0x4898469a4f62e1dc, 0xd60033cb9f64832b, 0xdc16121494816ba4, 0xf5a68806f8726f82, 0x3cdac5628de13ab8, 0xe7b56f76243f7c43, 0x5f92c6a93bd30597, 0x76250b21eb93c2a7, 0xa9c76bbd4b1e8b71, 0x37f584204efd126a, 0x96d4d702a7158e41, 0x9eaa8965bb96dd9e, 0xa14afdbcef2370da, 0xba7b023ed03d0b1a, 0xc37b8904ecb036fd, 0xfaea98f4fbfdb45b, 0x23ea95e4e9f5a028, 0xda7db2285bcf14e9, 0xd9ce6f6d9efe6dd0, 0x716d409006625021, 0xc2466db51c5e4c5c, 0x12cee2c854f56809]

private theorem rounds158_2 : sixRounds 12 (by decide) quarter158_2 = quarter158_3 := by
  decide +kernel

private theorem rounds158_3 : sixRounds 18 (by decide) quarter158_3 = state159 := by
  decide +kernel

private theorem perm158 : KECCAK.f1600 absorbed158 = state159 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds158_0, rounds158_1, rounds158_2, rounds158_3]
  rfl

theorem block158 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes158 ++ tail) state158 =
      KECCAK.Bytes.run 0 tail state159 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes158 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb158 ws)) := by
    rfl
  exact (step state158).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words158).trans perm158))

private def absorb159 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x54 0x61 0x55 0x85 0x17 0x1 0x80 0x83)) 1 (by decide) (UInt64.ofBytes 0x1 0x60 0x1 0x80 0x82 0x5b 0x56 0x35)) 2 (by decide) (UInt64.ofBytes 0x35 0x54 0x61 0x15 0x82 0x55 0x85 0x1)) 3 (by decide) (UInt64.ofBytes 0x11 0x81 0x82 0x5b 0x1 0x82 0x91 0x57)) 4 (by decide) (UInt64.ofBytes 0x82 0x51 0x82 0x57 0x35 0x54 0x61 0x15)) 5 (by decide) (UInt64.ofBytes 0x60 0x90 0x91 0x1 0x20 0x60 0x91 0x55)) 6 (by decide) (UInt64.ofBytes 0x5b 0x56 0x1a 0x54 0x61 0x90 0x1 0x1)) 7 (by decide) (UInt64.ofBytes 0x61 0x50 0x91 0x92 0x41 0x54 0x61 0x50)) 8 (by decide) (UInt64.ofBytes 0x5b 0x56 0x90 0x50 0x5b 0x56 0xd1 0x54)) 9 (by decide) (UInt64.ofBytes 0x1 0x60 0x81 0x1 0x60 0x54 0x80 0x82)) 10 (by decide) (UInt64.ofBytes 0x16 0x3 0x2 0x0 0x1 0x61 0x15 0x16)) 11 (by decide) (UInt64.ofBytes 0x52 0x0 0x60 0x90 0x4 0x90 0x2 0x60)) 12 (by decide) (UInt64.ofBytes 0x1f 0x60 0x90 0x20 0x0 0x60 0x20 0x60)) 13 (by decide) (UInt64.ofBytes 0x92 0x1 0x81 0x4 0x90 0x20 0x60 0x1)) 14 (by decide) (UInt64.ofBytes 0x57 0xa4 0x54 0x61 0x10 0x1f 0x60 0x82)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x7f 0x1 0x80 0x82)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed159 : Vector UInt64 25 :=
  #v[0xa7130beb30a81407, 0xb6abe24dc55ade5, 0xcb108a376526e0fc, 0x15097ba04735f750, 0x1fabe3e1b8885bd6, 0xd83ec377fd0be572, 0x3bf16d5cac1fc98b, 0x72400fc31ce19477, 0x8f3c236a5eb516e6, 0xafc73e8cc22f57f, 0xf62ed8d1dd222109, 0xd4933e4e84f3908b, 0xf4e7438d80006198, 0x291308d60ef2e6d7, 0xd404eee110d62bb7, 0xd7545496dc33c72b, 0x2d2cfc0623bd9641, 0x75f5d64895564c69, 0xe218efe4eb453cda, 0x3cbdc05d5a4adc6, 0xa75287926cdaa931, 0x6ec326c58c1709cc, 0x349a080655dd4139, 0xa8dbd242c915295d, 0xbf6ebd4f18e522e5]

private theorem words159 : absorb159 state159 = absorbed159 := by
  decide +kernel

private def quarter159_1 : Vector UInt64 25 :=
  #v[0x2c477f9b75293084, 0xe2f6721def48fc11, 0x7cb447c0d6baaad4, 0x6dba51f7664c8599, 0x568c5efd814a1e55, 0x86b4198f3cc4b8b2, 0xefb271168a6a294b, 0x33fd7c0b2d8a5d00, 0x7a9addba5db96bd7, 0xeced3bdcf09bcab5, 0x3d029e3808c8e21b, 0x242a0f458618e52c, 0xd736ac47b14036a, 0x239dce970c489d6b, 0xa1081fef8c25867, 0x8923ec05ed2e0eed, 0xcb5da9c28e65e634, 0x8a69295f29935351, 0x9e6a16170d692ecf, 0xecb425818782577a, 0x509e4fc88974d6ce, 0x30cd620095bef98, 0x5293528b3477dedc, 0xc10f1b8567c7d3d4, 0xab7ea9c0ec37c5d3]

private theorem rounds159_0 : sixRounds 0 (by decide) absorbed159 = quarter159_1 := by
  decide +kernel

private def quarter159_2 : Vector UInt64 25 :=
  #v[0x8aae7ac5e27567f6, 0xe90e0abdb8a20789, 0x49a11ebad1d3fd9f, 0x438803fd19ef00a0, 0xee0f6f20dfe4ae8b, 0x856e1e3bc4a1f71e, 0xe64d2ab69059df6f, 0xdac0d3fa1e3682ac, 0xb30eae48f83663c8, 0x24027665aa5d7e7, 0xc14f60fb4490d4df, 0x9961cd3c2544abc5, 0x3fd0899da4fb714f, 0x1e9c65ec300b9bdc, 0x5cd34e054e5c1a15, 0x62ebb1e384823cc6, 0x2755dcc1f9470f8e, 0xfef6589157bb6755, 0x8f51ba98a6240aa, 0xdde4dac067415176, 0xe9a526e2cd200362, 0xf481d45b17da66f8, 0xa82cac1dd72af965, 0x8aa3deaf68a040df, 0xa70d3afecf1f541b]

private theorem rounds159_1 : sixRounds 6 (by decide) quarter159_1 = quarter159_2 := by
  decide +kernel

private def quarter159_3 : Vector UInt64 25 :=
  #v[0xe019948b12b1adc0, 0x90cdd77bc9869b6a, 0x643456c89611e38c, 0x7b6a88baef9fc4b, 0x7d3259bb471c4f09, 0x4208062075b007e2, 0xb0db115feafdbb5b, 0x930a0a6438d13251, 0xd91bbe33997ddfd6, 0x3d96946ebd662af8, 0xc59e0f4c1d28af2f, 0x859faad1ff99fd2a, 0x3aa80fa8751293aa, 0xa66ffabc707a8994, 0x58b6953e9d9c0830, 0x50864684fe29e12e, 0x25b88d5813b1d009, 0xec551d38d6911305, 0xafa4834a022827e7, 0x3a7924ef298533bb, 0x37e52da8f82d301b, 0x66e5bae7f615cef6, 0xa6715a8262be702e, 0x507ea46da886875f, 0x24b8111e02b9f75]

private theorem rounds159_2 : sixRounds 12 (by decide) quarter159_2 = quarter159_3 := by
  decide +kernel

private theorem rounds159_3 : sixRounds 18 (by decide) quarter159_3 = state160 := by
  decide +kernel

private theorem perm159 : KECCAK.f1600 absorbed159 = state160 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds159_0, rounds159_1, rounds159_2, rounds159_3]
  rfl

theorem block159 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes159 ++ tail) state159 =
      KECCAK.Bytes.run 0 tail state160 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes159 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb159 ws)) := by
    rfl
  exact (step state159).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words159).trans perm159))

private def absorb160 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x17 0x16 0x35 0x82 0x0 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x82 0x5b 0x56 0x35 0x54 0x61 0x55 0x85)) 4 (by decide) (UInt64.ofBytes 0x82 0x55 0x85 0x1 0x1 0x60 0x1 0x80)) 5 (by decide) (UInt64.ofBytes 0x1 0x82 0x91 0x57 0x35 0x54 0x61 0x15)) 6 (by decide) (UInt64.ofBytes 0x35 0x54 0x61 0x15 0x11 0x81 0x82 0x5b)) 7 (by decide) (UInt64.ofBytes 0x20 0x60 0x91 0x55 0x82 0x35 0x82 0x57)) 8 (by decide) (UInt64.ofBytes 0x61 0x90 0x1 0x1 0x60 0x90 0x91 0x1)) 9 (by decide) (UInt64.ofBytes 0x11 0x82 0x80 0x5b 0x5b 0x56 0xb6 0x54)) 10 (by decide) (UInt64.ofBytes 0x81 0x0 0x60 0x57 0x41 0x54 0x61 0x15)) 11 (by decide) (UInt64.ofBytes 0x56 0xd2 0x54 0x61 0x1 0x1 0x60 0x55)) 12 (by decide) (UInt64.ofBytes 0x20 0x3a 0x30 0x32 0x43 0x52 0x45 0xfe)) 13 (by decide) (UInt64.ofBytes 0x72 0x65 0x66 0x73 0x6e 0x61 0x72 0x74)) 14 (by decide) (UInt64.ofBytes 0x20 0x65 0x68 0x74 0x20 0x6f 0x74 0x20)) 15 (by decide) (UInt64.ofBytes 0x64 0x64 0x61 0x20 0x6f 0x72 0x65 0x7a)) 16 (by decide) (UInt64.ofBytes 0x73 0x75 0x61 0x50 0x73 0x73 0x65 0x72))

private def absorbed160 : Vector UInt64 25 :=
  #v[0xc430e0f451c2e754, 0xed4a01b8c7c57ecb, 0xb664cc4369f96ecf, 0x505429a438e43ac5, 0x73af0f68d2c7d594, 0xd595ce412b73436b, 0x4d4a81d6ef971c19, 0xb6efa810843d08a6, 0x15509d93f6284388, 0x9341c0a378761102, 0xedf6cee7e2f644a3, 0x418d002d54d86b82, 0xf129df4539105207, 0x98e0f61b3bfc6413, 0xeabaabc743d85163, 0x17e094e83d8d96ca, 0x71aec85f00964280, 0x5ffc1e2f06bc2a4c, 0xa2a813dcb2558b08, 0xbdd8a10e56627b7c, 0x13fb5def4b54f7f0, 0x28f57ebabd2ec837, 0x68840730c03b99ed, 0x7459b1b7ab991a2e, 0x2c9cc3f1583443ec]

private theorem words160 : absorb160 state160 = absorbed160 := by
  decide +kernel

private def quarter160_1 : Vector UInt64 25 :=
  #v[0x84450180d3ac2df2, 0x467c61c611c60b2b, 0x6d19dd2e260b303f, 0xf55be6236b707127, 0xa0fae9ce85940e78, 0xa0b033b9fc7bed98, 0x56dca0d70abe4c9c, 0xa1ddfb1b799e9c91, 0xff028c1924e029de, 0x3d15ba8eb27cc3ba, 0xfd98b8fbf4a8d358, 0xfde9332dada72f17, 0x7d8980e273b16909, 0xb95b4b2b05f6254e, 0x653e45cc134cbd70, 0xb4ac8f280c09437f, 0x8a766e75d4227eb7, 0x469ddc7ed79eea83, 0x507fe022c61e1853, 0xc2e0d967f5cb97, 0x21837b6f4add1db6, 0x5d5b667a26839b94, 0x9b10406d328bc57c, 0xc34ee87cc6f8b449, 0x492837516eeff204]

private theorem rounds160_0 : sixRounds 0 (by decide) absorbed160 = quarter160_1 := by
  decide +kernel

private def quarter160_2 : Vector UInt64 25 :=
  #v[0xb4c5139e0ff8ad7a, 0x3ccf3b71f458b1a7, 0xb62fb2808144436b, 0xb10aa00f69fefb82, 0xda4b1c498d7d749, 0x4a096e43f91c0112, 0xc56ad15d636e43cb, 0x6d71f02bc32b30a7, 0x9d67d69398b1747a, 0xff02bdd020b6f81b, 0xe7ae8c534988db65, 0x2af65e74f838b929, 0x748581141311df72, 0x3a3a4b1035af8456, 0x6a99425f6a59b39d, 0xcf37409043446c89, 0x2b04e592ff0b3dc7, 0x5a4a3500bef3fa14, 0xeef884a0830c0d2a, 0xadf53f755bbefc28, 0x85694ed94e1baacf, 0xffd934d9bb3f41f0, 0x8e2319f8c5a68226, 0x3bc271e2bea20cad, 0x51b3b8653cedae91]

private theorem rounds160_1 : sixRounds 6 (by decide) quarter160_1 = quarter160_2 := by
  decide +kernel

private def quarter160_3 : Vector UInt64 25 :=
  #v[0xac680dd944bf7e42, 0x22137191de64725d, 0xa5ca2bfee9becbc8, 0x2f1174af257d0838, 0x714beb81c9c74ce7, 0xfe1bb11c1fabec68, 0xfe9d38be286d0640, 0xd809fde64cb731db, 0x868b6f842d2730a5, 0x450d0ba5808d8690, 0x705c439d6aaf1c04, 0xa8869d07fef98dcf, 0xf4d7addd39c4f323, 0x99a44afd79b00065, 0x18bb6b429d0506af, 0x3f492cbd9ae0abfc, 0x5993f8b8a4246a6f, 0x615871a0ffa9a783, 0xf6bd2ce998656c0d, 0x799ad57e03a3c929, 0x90f4c7845c117b02, 0x72ec3bf40f1331a8, 0x7561878a76673744, 0x6aa3cb5bb4308aaf, 0x30c41216a7633355]

private theorem rounds160_2 : sixRounds 12 (by decide) quarter160_2 = quarter160_3 := by
  decide +kernel

private theorem rounds160_3 : sixRounds 18 (by decide) quarter160_3 = state161 := by
  decide +kernel

private theorem perm160 : KECCAK.f1600 absorbed160 = state161 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds160_0, rounds160_1, rounds160_2, rounds160_3]
  rfl

theorem block160 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes160 ++ tail) state160 =
      KECCAK.Bytes.run 0 tail state161 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes160 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb160 ws)) := by
    rfl
  exact (step state160).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words160).trans perm160))

private def absorb161 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x65 0x6e 0x20 0x3a 0x65 0x6c 0x62 0x61)) 1 (by decide) (UInt64.ofBytes 0x72 0x65 0x73 0x75 0x61 0x70 0x20 0x77)) 2 (by decide) (UInt64.ofBytes 0x20 0x65 0x68 0x74 0x20 0x73 0x69 0x20)) 3 (by decide) (UInt64.ofBytes 0x64 0x64 0x61 0x20 0x6f 0x72 0x65 0x7a)) 4 (by decide) (UInt64.ofBytes 0x74 0x61 0x69 0x46 0x73 0x73 0x65 0x72)) 5 (by decide) (UInt64.ofBytes 0x3a 0x32 0x56 0x6e 0x65 0x6b 0x6f 0x54)) 6 (by decide) (UInt64.ofBytes 0x69 0x72 0x6f 0x68 0x74 0x75 0x61 0x20)) 7 (by decide) (UInt64.ofBytes 0x69 0x20 0x6e 0x6f 0x69 0x74 0x61 0x7a)) 8 (by decide) (UInt64.ofBytes 0x65 0x79 0x20 0x74 0x6f 0x6e 0x20 0x73)) 9 (by decide) (UInt64.ofBytes 0x46 0x64 0x69 0x6c 0x61 0x76 0x20 0x74)) 10 (by decide) (UInt64.ofBytes 0x6e 0x65 0x6b 0x6f 0x54 0x74 0x61 0x69)) 11 (by decide) (UInt64.ofBytes 0x61 0x20 0x6e 0x72 0x75 0x62 0x20 0x3a)) 12 (by decide) (UInt64.ofBytes 0x6f 0x6e 0x20 0x74 0x6e 0x75 0x6f 0x6d)) 13 (by decide) (UInt64.ofBytes 0x65 0x74 0x61 0x65 0x72 0x67 0x20 0x74)) 14 (by decide) (UInt64.ofBytes 0x30 0x20 0x6e 0x61 0x68 0x74 0x20 0x72)) 15 (by decide) (UInt64.ofBytes 0x65 0x6b 0x6f 0x54 0x74 0x61 0x69 0x46)) 16 (by decide) (UInt64.ofBytes 0x20 0x74 0x6e 0x69 0x6d 0x20 0x3a 0x6e))

private def absorbed161 : Vector UInt64 25 :=
  #v[0xf37339e01db36498, 0x8e7a60151ab72c21, 0xb4db98380049f960, 0x8a0b56ffa354d1d, 0x7857594721f04336, 0xbff6874ec4024f2c, 0xab8f1bbe2a1b1bb1, 0xc092c57b9d89df8f, 0x1c758a0cf1222280, 0xe7f57ad38e6cb69a, 0x76bf9f0175f6e17d, 0x3fd175835845cfb, 0xb09f6022796057dd, 0x3fefdb4ce0afd66, 0x1488c9e446cd7f8d, 0xf43e9391ae0d5bbf, 0xcae62316ee79e707, 0x8b85640e167eb4e5, 0x635dedac542061e9, 0xf8e64750a50efddd, 0xc9b30aa6e421a82b, 0x21a08602d89befe7, 0x196f12b3493e4b95, 0x9c796621300073a1, 0x83fb4d85c00f8630]

private theorem words161 : absorb161 state161 = absorbed161 := by
  decide +kernel

private def quarter161_1 : Vector UInt64 25 :=
  #v[0x6b4cb67006ae4892, 0xdb36b5c3817c9ce, 0x2bb7d17557b0d7f5, 0x1719d15f40bd3ddb, 0xb407d0d59ba479b8, 0x2e377207e7f0c661, 0x73427cb07bcc5f6e, 0x5f66c0877ca52170, 0x3bc606634be41494, 0xf00dd50d0d3c9de, 0xb4571225ddf01ec9, 0x3d8a6583a0f62ecc, 0xce291420d9b32d20, 0x886b4bc7d0988d8, 0xced56b4d027b33b3, 0xe69b09804a6bcbf1, 0x35569decd8c4e347, 0x4aaa9d6f920eba63, 0x44f4c8244320fe68, 0x591a1baee7ae2f53, 0xfd72730246ffaa8f, 0x4d319f31d419ada7, 0x971f8c32a18298f7, 0x989a7b134c9b4ec, 0x7b0d98aeae6e5f5f]

private theorem rounds161_0 : sixRounds 0 (by decide) absorbed161 = quarter161_1 := by
  decide +kernel

private def quarter161_2 : Vector UInt64 25 :=
  #v[0x9036d64e9872abe5, 0x7c3f992a3e0e78e9, 0x880194823ca87179, 0x7872235936ba32fa, 0xf9bbb33c3f24cdc9, 0xdc02f15e0964b8f5, 0x1db1c68a988a0b4d, 0x40462c712aa2a855, 0x674a9426baed8df1, 0x9a105bd08e791c0c, 0xf157c0ec12f1eebe, 0xf94b7d636e863bc1, 0xa15cf99df379a093, 0xd80e92de234b16d0, 0x5fe5f9570bb8d262, 0xdd24e8c2799388b2, 0x77a3c77157a0ea50, 0x16de367aef03a53c, 0xb8930f5e473af641, 0x924f8bb817a85450, 0xaac1bff33503e05a, 0xe6b5cdefdfcc8442, 0xf5007046a45b0c8c, 0xadb2dd37378ce8c4, 0xb4ac890ac3e67b99]

private theorem rounds161_1 : sixRounds 6 (by decide) quarter161_1 = quarter161_2 := by
  decide +kernel

private def quarter161_3 : Vector UInt64 25 :=
  #v[0xb700db0c2deb2ea1, 0xbcd8e6cbf8c72688, 0x49d879321415ef08, 0xa8fba86d5b86e2cf, 0x10769ab3c2a6198c, 0xf855485c342169c6, 0x3bc019b3f6f86ac6, 0x2a93ed5bc8556357, 0xe95013675b0a1329, 0x36167018c74ea4b8, 0x988a0843ee954d6b, 0x5308dd2d24152fc4, 0x916a808ace6438d, 0x34e1bb1e37e0f2cd, 0xd98e3af13b0d02e1, 0xf5fe66e8220d8972, 0xa858be90733f9d3b, 0xd31a0056598c985, 0x6c8ea8a579d329fe, 0x8989e3ff2dee6fe3, 0xab7edfcee5e655b, 0xfd79ffa07c5fd1f3, 0x5bffe0bed7a8772, 0x6bb50a07cb8b606, 0xe6f5973827bf7b21]

private theorem rounds161_2 : sixRounds 12 (by decide) quarter161_2 = quarter161_3 := by
  decide +kernel

private theorem rounds161_3 : sixRounds 18 (by decide) quarter161_3 = state162 := by
  decide +kernel

private theorem perm161 : KECCAK.f1600 absorbed161 = state162 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds161_0, rounds161_1, rounds161_2, rounds161_3]
  rfl

theorem block161 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes161 ++ tail) state161 =
      KECCAK.Bytes.run 0 tail state162 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes161 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb161 ws)) := by
    rfl
  exact (step state161).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words161).trans perm161))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
