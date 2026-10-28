import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb120 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x25 0x60 0x52)) 1 (by decide) (UInt64.ofBytes 0x39 0x91 0x25 0x60 0x54 0x58 0x61 0x80)) 2 (by decide) (UInt64.ofBytes 0x40 0x60 0x50 0x50 0x91 0x1 0x40 0x60)) 3 (by decide) (UInt64.ofBytes 0x73 0x5b 0xfd 0x90 0x3 0x91 0x80 0x51)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x3f 0x61 0x16 0x82 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xc3 0x8 0x7f 0x51 0x40 0x60 0x57 0xd0)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0xa0 0x79)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x52 0x81 0x0 0x0 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x80 0x80 0x1 0x4 0x60)) 13 (by decide) (UInt64.ofBytes 0x81 0x23 0x60 0x52 0x82 0x3 0x81 0x82)) 14 (by decide) (UInt64.ofBytes 0xe7 0x54 0x61 0x80 0x1 0x20 0x60 0x52)) 15 (by decide) (UInt64.ofBytes 0x91 0x1 0x40 0x60 0x39 0x91 0x23 0x60)) 16 (by decide) (UInt64.ofBytes 0x3 0x91 0x80 0x51 0x40 0x60 0x50 0x50))

private def absorbed120 : Vector UInt64 25 :=
  #v[0x53d03eb0f16b59a, 0x7cd8c1d6445215e7, 0x7acf16ae7b739809, 0x57e76ac94b11ebad, 0x8ae80a3100b334db, 0xecbb27fb04820a66, 0x40d9a845957553d7, 0x349e4ca8cef43bf7, 0xcc31ba588454d237, 0xa5b28bbd7a147ab0, 0x8c66d331d2667e47, 0x806194b4821ec326, 0x714eb4bf16f72745, 0x95569a78c2982534, 0xcf7bd4644422cdd5, 0x654f71b36d9aa9c8, 0x4ab69b19bc7fc3b0, 0x42316976c5b33376, 0x2f8764d45b2f1edd, 0x1f33dd33e154919e, 0x7734117122d779c1, 0xc3848dbc964d088b, 0xca113a498d33751a, 0x2b6caadd85b66300, 0x284d1fde2c783453]

private theorem words120 : absorb120 state120 = absorbed120 := by
  decide +kernel

private def quarter120_1 : Vector UInt64 25 :=
  #v[0x922f715979f273a1, 0xe989c65e0aabe36f, 0x703836a6b7343095, 0xa0f2ea5d0c84aab, 0x9e65561e10df533e, 0xbd06d6029239a800, 0x6d775f02bf4a3a0e, 0x5f33647d7fd28b54, 0x9bee52733e5358ae, 0x2f436ab91e2f0e91, 0x5060fbac215f46c4, 0xb8bcb59f1d94d4ad, 0x902287f23f36cfbb, 0xc255721fdb89bcaf, 0x1ab5fdf397ed0e63, 0xa7d775e83707a76f, 0xc0ba54aa39f24fbe, 0xfef002e5f3fc52a8, 0x58c1a37c9a14a3f1, 0x788fa626ccd1ccdc, 0xcc8ad53c3a80591e, 0xc9ee23b99216f04, 0xadaa969979dad662, 0x1cd749068ffdaef5, 0x1a1a55f575ee1bd4]

private theorem rounds120_0 : sixRounds 0 (by decide) absorbed120 = quarter120_1 := by
  decide +kernel

private def quarter120_2 : Vector UInt64 25 :=
  #v[0xafefcd8372e7f796, 0xae293a3d23011db3, 0xd57445c5e9ca1dbc, 0xd25895558b6128ab, 0xfe1e14a02d5b871c, 0x571b0a812fa8eca7, 0x1b2cfe0937f990df, 0x4ea498fe3d2f0fd1, 0xe32848a45bd7bfd4, 0x9e0c6a1e4dc6c9f1, 0xa501c0da58215684, 0xcc37608c6a9b6e9e, 0x729095a25c90675c, 0x6d3fb01a41705785, 0x9cf3875cb3a3a26d, 0x125466048593246b, 0xdb51ad4b8379e4ec, 0x7dca6cd9de309887, 0x2e9a81240e9c2f21, 0x7793f34e9520c6c0, 0x90830b0198caa52b, 0xd080c1b5b6aafe59, 0xc99cf0926eb604a0, 0x2edb8a00da124afd, 0x8ed857c9c7ba8e89]

private theorem rounds120_1 : sixRounds 6 (by decide) quarter120_1 = quarter120_2 := by
  decide +kernel

private def quarter120_3 : Vector UInt64 25 :=
  #v[0x6d27a255d062c62d, 0x49c7c3729e685dd3, 0x7ca2ae8e836f2043, 0x70143585018e5030, 0xc9c976efff96d70d, 0x69d63e62c0d4c0a8, 0x26c16caa30c8253a, 0x71ec88d6682fd9fa, 0xf3762b11e66db74d, 0x7f120efa79b62a6e, 0xa776aaca75d04c62, 0x33e30104d6caaf66, 0xa39c916b94e0e8ec, 0x149bb57209946042, 0x75a2718f89ed0c06, 0x33757bb0474958e0, 0x18003dec028ca254, 0x38af2df885dcd160, 0xe8c3d68a5dce4e34, 0xaed96eac65798d08, 0x9a20b2569a01e824, 0x9f605e7e09dbd6b6, 0xc78d98acf7969a73, 0x872a73ee3dcffbb8, 0x2371622fe3a91462]

private theorem rounds120_2 : sixRounds 12 (by decide) quarter120_2 = quarter120_3 := by
  decide +kernel

private theorem rounds120_3 : sixRounds 18 (by decide) quarter120_3 = state121 := by
  decide +kernel

private theorem perm120 : KECCAK.f1600 absorbed120 = state121 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds120_0, rounds120_1, rounds120_2, rounds120_3]
  rfl

theorem block120 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes120 ++ tail) state120 =
      KECCAK.Bytes.run 0 tail state121 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes120 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb120 ws)) := by
    rfl
  exact (step state120).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words120).trans perm120))

private def absorb121 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x5b 0xfd 0x90)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x90 0x0 0x60 0x16 0x83)) 4 (by decide) (UInt64.ofBytes 0x20 0x90 0x40 0x60 0x52 0x20 0x60 0x9)) 5 (by decide) (UInt64.ofBytes 0x57 0x4e 0x40 0x61 0x15 0x11 0x81 0x54)) 6 (by decide) (UInt64.ofBytes 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x40 0x60)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x4 0x60 0x52 0x81 0x0 0x0 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x81 0x82 0x1 0x20 0x60 0x80 0x80 0x1)) 12 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x26 0x60 0x52 0x82 0x3)) 13 (by decide) (UInt64.ofBytes 0x26 0x60 0x93 0x56 0x61 0x80 0x1 0x20)) 14 (by decide) (UInt64.ofBytes 0x50 0x50 0x91 0x1 0x40 0x60 0x39 0x91)) 15 (by decide) (UInt64.ofBytes 0xfd 0x90 0x3 0x91 0x80 0x51 0x40 0x60)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x5b))

private def absorbed121 : Vector UInt64 25 :=
  #v[0x9079449edaddeecf, 0x40848051caeba4de, 0xa3bef9e787b1af46, 0x16fc18d84febcb2c, 0x52b27818f1effc4d, 0x56aa4c627b143bcf, 0xf8a054211427b0ca, 0xbd1409ac259e6492, 0x99c9f0c6206ed7b1, 0xa37c839b3165d3ce, 0x31ac65c53c3c0284, 0x9eb6308c84226c39, 0x1beb965fdb229ad, 0xde4fd9333fe49eff, 0x1d90424357aac986, 0x71346507384cec99, 0x8f7166c88e4aabdc, 0x44d42179eae1dbef, 0x4aada68cac30145c, 0xded16a6acb0fa669, 0xe469a63d8dc4c3be, 0x7607ae329d3c62b6, 0x6caf4cb6173e3cb0, 0xf676c58f9deb788b, 0xa22377eed5dcf19]

private theorem words121 : absorb121 state121 = absorbed121 := by
  decide +kernel

private def quarter121_1 : Vector UInt64 25 :=
  #v[0xd5fa3f4b117c0f29, 0xda5d5c763c26a9d8, 0x191894383ae485ae, 0xc57db4180c39d939, 0xdf18f538f347a159, 0xfdfa2e0ced387b35, 0x1b11fe784986dea4, 0xbd2de4ed864855af, 0x4d467e32a9e2410b, 0x43b65f2e89abd529, 0xac35ee9b9239a0b2, 0x67fa5f17f0209c50, 0xc930d39ba7b9b274, 0x55b217d477178845, 0x209ee4af6dfe4e02, 0x126587a10ef4c422, 0x79f44138f292fdf9, 0x4213cde8274a0f29, 0xf5fdcba2198b851c, 0x26021e0298d69fe, 0x4127534ce1556228, 0xc885b23c9caae5eb, 0xd8d392884cf46af7, 0x81070f5f286056fd, 0x97376691b64698ab]

private theorem rounds121_0 : sixRounds 0 (by decide) absorbed121 = quarter121_1 := by
  decide +kernel

private def quarter121_2 : Vector UInt64 25 :=
  #v[0xc2a52e9d4a29916e, 0x6b38bf83b94bf7ac, 0xef0e0205247ea213, 0xaf37a6f7867be0fb, 0x77f697bf74c65e6e, 0x16a28b49e8dc28d, 0x6de7b8e1ef5a4e05, 0x7df58d07093275cb, 0x201346c8cbf9485f, 0x9d71a86ccdb9dab5, 0x2bea7c7e4cde889b, 0x7792a25c51ee6e32, 0x88dce4e9f238c5d8, 0xb1ed3b7bd81634b4, 0xa8e2991277a81635, 0x69617034046d1f51, 0x43689439f01bc784, 0x6ba5b46e0b85a845, 0xcd82227e045f4428, 0xdb2da3d3a390cc60, 0xa8c97dcb1a67c910, 0x5a3cc372d0d045bd, 0xaac29db1744a36bd, 0xd337ea4e843b3c25, 0xfbdd58d81951e708]

private theorem rounds121_1 : sixRounds 6 (by decide) quarter121_1 = quarter121_2 := by
  decide +kernel

private def quarter121_3 : Vector UInt64 25 :=
  #v[0x4b0d8ada1fe1e799, 0xe9d8c4da645cde88, 0x89ce9dee56411f06, 0xf148f455c53ebc11, 0xaaf589cb3ad9a202, 0x8e1c364e7cf8e0f1, 0x6c7fd5b74f77593f, 0x83d038b8f1d658b9, 0xab08931d813e5dc4, 0x3d43e38bc8d77d32, 0x12cceab4c7860b01, 0x7b563ae16d6f99c6, 0x9264dcf94a3a1687, 0xfcb9d1b469272a11, 0x6edfce2d98aa1391, 0x70567b8bae83f6e3, 0x1988728d0eadffcc, 0xf470111670ffaccb, 0x879a482b02ab9957, 0x30adda85f9a3c057, 0x832ee77c6a6a0e6, 0xac40a7f27051cf65, 0x8e56746c9c0691e0, 0x2fe996cc3d52408, 0x2c02910466f6db88]

private theorem rounds121_2 : sixRounds 12 (by decide) quarter121_2 = quarter121_3 := by
  decide +kernel

private theorem rounds121_3 : sixRounds 18 (by decide) quarter121_3 = state122 := by
  decide +kernel

private theorem perm121 : KECCAK.f1600 absorbed121 = state122 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds121_0, rounds121_1, rounds121_2, rounds121_3]
  rfl

theorem block121 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes121 ++ tail) state121 =
      KECCAK.Bytes.run 0 tail state122 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes121 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb121 ws)) := by
    rfl
  exact (step state121).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words121).trans perm121))

private def absorb122 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x16 0x83 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x60 0x9 0x60 0x52 0x81 0x90 0x0 0x60)) 3 (by decide) (UInt64.ofBytes 0x61 0x54 0x20 0x90 0x40 0x60 0x52 0x20)) 4 (by decide) (UInt64.ofBytes 0x56 0x23 0x41 0x61 0x82 0x90 0x7e 0x40)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x5b)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x85 0x80 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x9 0x60 0x52 0x81 0x90 0x0 0x60 0x16)) 9 (by decide) (UInt64.ofBytes 0x20 0x82 0x80 0x40 0x60 0x52 0x20 0x60)) 10 (by decide) (UInt64.ofBytes 0x81 0x16 0x84 0x90 0x55 0x93 0x90 0x93)) 11 (by decide) (UInt64.ofBytes 0x82 0x90 0xba 0x40 0x61 0x54 0x20 0x52)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x5b 0x56 0xfd 0x41 0x61)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x81 0x0 0x60 0x16 0x84 0x80 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x81 0x90 0x20 0x60 0x9 0x60 0x52 0x81))

private def absorbed122 : Vector UInt64 25 :=
  #v[0xf2edd2dc921e7126, 0x4cf317eb33466dc7, 0x55c359bc7dca7067, 0xc3b4da8f59921d11, 0x268d56cfb52593c1, 0xac39945d6aa3184e, 0x4aaf0f6d6ce8ed2a, 0xd4abcba59ef8fb4e, 0xab976cf5eccaeef4, 0x303d36ccf427c963, 0x783a9483f35b844f, 0xfa759504dd1d0eb8, 0x525969e279dd10eb, 0xcd4ce7b4015438cc, 0xb0a3c3c92fd16740, 0xb44cf9b56d7e07fe, 0xa340c545ce85dd5a, 0xb2427f7466c989fd, 0x81855b58623f71f6, 0x3099ac6c02091a71, 0x8d213025e3b5b782, 0x8e496eae2b7c8b60, 0x1473cd2fdb3ee852, 0x905bc413867ddcff, 0x287cbab31fd5366f]

private theorem words122 : absorb122 state122 = absorbed122 := by
  decide +kernel

private def quarter122_1 : Vector UInt64 25 :=
  #v[0x5ec8d131891eea26, 0xad2927ab9c612e81, 0x123f821c798d42da, 0xf55cfc02ff360091, 0xa81616e2649c9f95, 0xb5d2be0bc48bebdc, 0x697bcffb3932b0e3, 0xf25b1357f15f6740, 0xf32c1be8731409a1, 0xbfecf01b05fe25ab, 0xed1fa38322973fbc, 0x62227e93f8d3bfc6, 0xf836053432f3d932, 0xb3767e5540c2297, 0x4a5376b264aed050, 0xfb88995c588d8921, 0xe6f7ba8528211bf7, 0xf3154112352f8c2, 0xd99f70daa6d36684, 0xc052b2f38490331f, 0xf16031c862839e1c, 0x6c6698e6ef1e4926, 0x97f436833c7e038c, 0xfb2985d80e588659, 0x726d7360d188441]

private theorem rounds122_0 : sixRounds 0 (by decide) absorbed122 = quarter122_1 := by
  decide +kernel

private def quarter122_2 : Vector UInt64 25 :=
  #v[0xae2bc88ec49b72cf, 0x3e79770c00cfd422, 0xfe3eb3b619e5b097, 0xb90ba5900268a26c, 0xa3e1d9801ad0e915, 0xbb35c58a30f6594b, 0xcd44ef697ba24b9e, 0xd5b424c0e6b7a27f, 0xe38660f5b24ef002, 0x4d0e5a7cbb433a2b, 0x3fa9ad583eca7c87, 0x21e48663997dea82, 0xdf485951cdb83c86, 0xddaa38f2dba9e2a4, 0x727723525d4016ae, 0xa8d035984a0d8e8a, 0x282eddaa82332c5d, 0x3c0ea6bdf48d1007, 0x30dd3589f70aa274, 0x2d9f20e2e85f27f1, 0x3f724f149cb6006d, 0xf647e90ce7947690, 0x62fbe0b5eb335fdf, 0x49a3d2ab46d9632d, 0x2777c3941dd39a42]

private theorem rounds122_1 : sixRounds 6 (by decide) quarter122_1 = quarter122_2 := by
  decide +kernel

private def quarter122_3 : Vector UInt64 25 :=
  #v[0xe220fc4096354cff, 0xcb8801c124234419, 0x3ac8748bf04ae6ac, 0x6f702ae4e2157ef, 0x2d8e4c1e9da63426, 0x48e5241c4ae90bd2, 0x21f6c87e5f3c4686, 0x1927db6a1e7b18c4, 0x10d968dbf969ac21, 0xf24f7ff67e35e925, 0x46bdc4a51d5589fa, 0xbe821d86aa9202fe, 0x3c0a10bf0662b4ee, 0xe18f47fc70baea20, 0xfbb59cf67f3c47ad, 0xf53f7e2dc13fdbd8, 0x2bc13f7c0df40721, 0xddf48a0cfdcd2430, 0x16f223815b4d39f3, 0x151973bc4a99e732, 0xf7df85c0a6ce5763, 0xaa2ec3c0a5e7e22e, 0xe5b802fe4524d548, 0x76b935f8610afaad, 0x85bce5432e326402]

private theorem rounds122_2 : sixRounds 12 (by decide) quarter122_2 = quarter122_3 := by
  decide +kernel

private theorem rounds122_3 : sixRounds 18 (by decide) quarter122_3 = state123 := by
  decide +kernel

private theorem perm122 : KECCAK.f1600 absorbed122 = state123 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds122_0, rounds122_1, rounds122_2, rounds122_3]
  rfl

theorem block122 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes122 ++ tail) state122 =
      KECCAK.Bytes.run 0 tail state123 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes122 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb122 ws)) := by
    rfl
  exact (step state122).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words122).trans perm122))

private def absorb123 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x94 0x20 0x90 0x82 0x91 0x40 0x60 0x52)) 1 (by decide) (UInt64.ofBytes 0x52 0x81 0x85 0x51 0x80 0x55 0x94 0x90)) 2 (by decide) (UInt64.ofBytes 0x92 0x16 0x87 0x92 0x93 0x91 0x51 0x90)) 3 (by decide) (UInt64.ofBytes 0xc8 0xe2 0x1b 0xad 0x52 0xf2 0xdd 0x7f)) 4 (by decide) (UInt64.ofBytes 0x8d 0x37 0xfc 0x68 0xb0 0xc2 0x69 0x9b)) 5 (by decide) (UInt64.ofBytes 0xa1 0xc4 0x63 0xf1 0xa7 0x2b 0x95 0xaa)) 6 (by decide) (UInt64.ofBytes 0xb3 0x23 0xf5 0x4d 0x5a 0xf5 0x28 0x16)) 7 (by decide) (UInt64.ofBytes 0x90 0x1 0x3 0x90 0x82 0x91 0x92 0xef)) 8 (by decide) (UInt64.ofBytes 0x0 0x60 0x5b 0x56 0x50 0x50 0x50 0xa3)) 9 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x83 0x83 0x65 0x41 0x61)) 10 (by decide) (UInt64.ofBytes 0x80 0x52 0x40 0x60 0x1 0x40 0x60 0x80)) 11 (by decide) (UInt64.ofBytes 0x7f 0x1 0x20 0x60 0x52 0x81 0x1e 0x60)) 12 (by decide) (UInt64.ofBytes 0x68 0x74 0x61 0x4d 0x65 0x66 0x61 0x53)) 13 (by decide) (UInt64.ofBytes 0x61 0x72 0x74 0x62 0x75 0x73 0x20 0x3a)) 14 (by decide) (UInt64.ofBytes 0x76 0x6f 0x20 0x6e 0x6f 0x69 0x74 0x63)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x77 0x6f 0x6c 0x66 0x72 0x65)) 16 (by decide) (UInt64.ofBytes 0x5b 0x56 0xe2 0x4b 0x61 0x50 0x52 0x81))

private def absorbed123 : Vector UInt64 25 :=
  #v[0x69de35a22467f199, 0xb00368e883fb6c4, 0x8f9fd0e36ca9755d, 0x20d4bbceeda24c3c, 0x78a47dd555564bb7, 0x885df65279a44103, 0xe647dfe43412fdd3, 0x5429f62733876fee, 0x5b14c34ac0f85ee5, 0xb8f9924a65897a24, 0xe9ac73074a27089a, 0xc6fa29519f6ac56b, 0xbd5c8fa48d418ef6, 0x699b20bcbe34524, 0x5e5711a54b10b0df, 0x56431b969a7f861f, 0x478960c21e8410f2, 0xf3e319106422236c, 0xaf995f901a9a7343, 0x109dc955b0fca030, 0xfa9c90fcdef7c287, 0x3d20420cb3b28657, 0x4b9a2e896bc48d81, 0xe4d892f3c123189b, 0x93b55efa28b82129]

private theorem words123 : absorb123 state123 = absorbed123 := by
  decide +kernel

private def quarter123_1 : Vector UInt64 25 :=
  #v[0x8dead5f7d8606b60, 0x9e0125c4cfc5c8a0, 0x8f39e6996e08f8cb, 0xca7139cfdac9ae29, 0x89fb14a1e5b514d3, 0x6f34724ac75e78af, 0xc6a058a4adf6e12, 0x510af39e8650862c, 0xc396b03c5af880f3, 0xc1bd28477b8fd193, 0xf198f24d8f625217, 0xdbb5f16a7dff8ceb, 0x627ea9f689093c9f, 0xead01c40bb9f7f5d, 0xd4b3d75098c32967, 0xd6383698b6649f24, 0x9e02a9a716121f3f, 0x4dd00be18b3ecd1e, 0xb23c308bce2e2f05, 0x8d0c28cc5b51c469, 0x7add31ea03ba909c, 0x7ce4a96718a76cbd, 0x67719cb6428aaaca, 0x55532e1486ab5351, 0x1088bbdafc1d8aa3]

private theorem rounds123_0 : sixRounds 0 (by decide) absorbed123 = quarter123_1 := by
  decide +kernel

private def quarter123_2 : Vector UInt64 25 :=
  #v[0x2ecf3b75c5a8d02b, 0xf31648596c7605e0, 0x356dd904327cb044, 0xefca370a19bb2ed5, 0x62b31b7e7e10e0e9, 0xbf65a79de3b29978, 0x467232546fdf6e25, 0x85ef5c907cd1dff3, 0xa51552b1316005fd, 0xc9382ffab6fcf363, 0xc9b10137dfca6cbf, 0xdbc4ee8a5f662045, 0xfee30ae28ee7e63e, 0xc48a374010e4ef5d, 0x1612b298412eb54c, 0x49dc0765d426c736, 0xbf95f2ab106adab1, 0xd8534e548805bb5d, 0x88d36e7b6985edf6, 0x4c2d7106bcbca993, 0x183644da6559937b, 0x8047d5d4dd79e5a7, 0x27171ec9c8cc04a2, 0xddf04f2b25cd1826, 0x8f3da9214a1f5be0]

private theorem rounds123_1 : sixRounds 6 (by decide) quarter123_1 = quarter123_2 := by
  decide +kernel

private def quarter123_3 : Vector UInt64 25 :=
  #v[0xdcd38ecd7fae3d28, 0x775a92e134791e74, 0x60abbb87d05ca2bf, 0xd8c1ca65bd9c0942, 0x494a271cb31b0fb, 0x873f6c380367789f, 0x8700c2b36cb26798, 0xbb54015f34d726c5, 0x35156e56fe380529, 0x20a22674232fece, 0x4e241dce58d29d29, 0xc7a7e83c0143dc50, 0x6f74cb6d5138a37b, 0xb267ac9cd8d9f82b, 0x2a8c124995009571, 0x80aeb791fdcd529b, 0xe6b8224d46f0d16f, 0x7e9a2420585f2ae3, 0x9975e7a5790536a4, 0xcb26c57d5fd9e103, 0x5b13c3f0891296a0, 0xb0b5f7ae006b4ea, 0xc551a0ee6071cdb3, 0x57cfe97b6bab38f, 0xdfca31866ac22404]

private theorem rounds123_2 : sixRounds 12 (by decide) quarter123_2 = quarter123_3 := by
  decide +kernel

private theorem rounds123_3 : sixRounds 18 (by decide) quarter123_3 = state124 := by
  decide +kernel

private theorem perm123 : KECCAK.f1600 absorbed123 = state124 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds123_0, rounds123_1, rounds123_2, rounds123_3]
  rfl

theorem block123 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes123 ++ tail) state123 =
      KECCAK.Bytes.run 0 tail state124 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes123 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb123 ws)) := by
    rfl
  exact (step state123).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words123).trans perm123))

private def absorb124 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x60 0x5b 0x56 0x50 0x50 0x50 0x92 0x93)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x7f 0x54 0x80 0x0)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x16 0x0 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x90 0x91 0x16 0x92 0x90 0x92 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0x73 0x5b 0x56 0x55 0x90 0x17 0x91)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x0 0x60 0x16 0x84 0x80 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x90 0x20 0x60 0xa 0x60 0x52 0x81 0x90)) 14 (by decide) (UInt64.ofBytes 0x93 0x20 0x83 0x80 0x40 0x60 0x52 0x81)) 15 (by decide) (UInt64.ofBytes 0x20 0x52 0x90 0x92 0x52 0x83 0x16 0x86)) 16 (by decide) (UInt64.ofBytes 0x84 0x90 0x84 0x90 0x6e 0x32 0x61 0x54))

private def absorbed124 : Vector UInt64 25 :=
  #v[0x441d143c8dad6ce6, 0x4931624a356a1f63, 0x798756e5f849bb56, 0x56b8b1a9d9f845a, 0x2672d26a6edf7ad7, 0x82faffac0071f8cd, 0xb5066ce85c2dd752, 0x7db67c7f0e273701, 0xf721f82f6f5c911e, 0x910b06cd34cab5ac, 0xdde52d4231a47b16, 0x6d1eb1fe991d7055, 0x5f4dc10628ad4ff5, 0x7bb1865411fdff9d, 0x2855baf94656abf8, 0xe6cf07cde6ea29e8, 0x4d693b4f91b9e4bb, 0x3387239ca04b774e, 0x39dd836c7849ed87, 0x6aa1a2ad895d32ec, 0x280e2e74c34077c4, 0xdb2fc0ef702feafb, 0xf811c050e1552931, 0x912257bcabdbe268, 0x7bcfef7d48e9c473]

private theorem words124 : absorb124 state124 = absorbed124 := by
  decide +kernel

private def quarter124_1 : Vector UInt64 25 :=
  #v[0xabb55a6e14244dc8, 0x4faf0b307936e54e, 0xd2c0640abd6c1ae6, 0x9eeeeef7891b6309, 0x1fe0d886b2d1b7ea, 0xddbf6117b565d517, 0x37e57b826e2392c5, 0xd71235223e1426ba, 0x2b7d86687648e2e4, 0x9619f8e7f2781dea, 0x61b6a30f62df1d0b, 0xb88df8c2c2e0a387, 0x3ecad0421f5d7d33, 0x32f995eada0a938, 0x19aaa9aad59b2b3d, 0xb2c1bca148a88a3b, 0xae1740bfe8afb50f, 0xd421c786b03eb2ea, 0xbafa71c2e8550442, 0x79e803e6b18b9055, 0x689d6e97cb0e3f54, 0xd28bf66e6cbcb421, 0x8cad01945cce096, 0xacbb5e455dd7064c, 0x47a085d985adad9d]

private theorem rounds124_0 : sixRounds 0 (by decide) absorbed124 = quarter124_1 := by
  decide +kernel

private def quarter124_2 : Vector UInt64 25 :=
  #v[0xf843244a7a3375cb, 0x44c13fcd0e3aeff0, 0x92b273d03c0e0b29, 0x57d90bcb00b9436a, 0xfaa5c8940d254031, 0x9f51323e114cf3c4, 0xf9aff6ca3bb4c3fe, 0x514e7d9879046ec5, 0x478e0477a85984fd, 0x4cd8dc287d99bb3c, 0x4e5c2df10f87fa55, 0xbb3a2b0ba3829f16, 0xbc41a67ab66b6d48, 0x8bf05b83b4c1a1a4, 0xaf2f387773ca06ca, 0xe6e6b0bd3666e0c1, 0xe84d12ace9e9c1fb, 0xe00a6241e95a5cfe, 0x2057728688b6a82c, 0x854ed00ca33129b, 0x20d72db411623599, 0xbbce44b793d65321, 0xbd1e77362000d0fe, 0xfccafb0158ab1f23, 0x2b3669c7428ff923]

private theorem rounds124_1 : sixRounds 6 (by decide) quarter124_1 = quarter124_2 := by
  decide +kernel

private def quarter124_3 : Vector UInt64 25 :=
  #v[0xc685e29d6d554bea, 0xf7359fd298a07148, 0xdcf3e16045fbe9ed, 0xf536695c8e828b2c, 0xc46dbd57791aa7eb, 0xeea97164bb683318, 0xc72e1443800f0d63, 0xc4c512f57f93fa3e, 0x8c4816eb739530b5, 0xd482a5dcbde797b6, 0x3a954d563897cef3, 0x1af33a57fff8302c, 0xbcfe4a3c87929bc8, 0x687b9acee237e09, 0x6c360469e89bfd2f, 0x9a6b90ab88a75878, 0x260ae341d8866568, 0xf383d74ebe0e213e, 0x9bfa1d92d738fe3a, 0xcf11e9a3e69e348e, 0xa9e3e96f535bed04, 0x71c1c92012bfadc3, 0x51994e6299861db7, 0xc117ceeda3304550, 0xef0358cd1def2454]

private theorem rounds124_2 : sixRounds 12 (by decide) quarter124_2 = quarter124_3 := by
  decide +kernel

private theorem rounds124_3 : sixRounds 18 (by decide) quarter124_3 = state125 := by
  decide +kernel

private theorem perm124 : KECCAK.f1600 absorbed124 = state125 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds124_0, rounds124_1, rounds124_2, rounds124_3]
  rfl

theorem block124 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes124 ++ tail) state124 =
      KECCAK.Bytes.run 0 tail state125 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes124 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb124 ws)) := by
    rfl
  exact (step state124).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words124).trans perm124))

private def absorb125 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x41 0x61 0x85 0x90 0xf8 0x41 0x61 0x90)) 1 (by decide) (UInt64.ofBytes 0x5b 0x56 0xb1 0x3d 0x61 0x5b 0x56 0xfd)) 2 (by decide) (UInt64.ofBytes 0x10 0x81 0x83 0x1 0x82 0x82 0x0 0x60)) 3 (by decide) (UInt64.ofBytes 0x80 0x40 0x60 0x57 0x65 0x41 0x61 0x15)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x4 0x60 0x20 0x60 0x52 0x81 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x82 0x24 0x60 0x1b 0x60 0x52 0x1 0x82)) 10 (by decide) (UInt64.ofBytes 0x4d 0x65 0x66 0x61 0x53 0x7f 0x52 0x1)) 11 (by decide) (UInt64.ofBytes 0x64 0x64 0x61 0x20 0x3a 0x68 0x74 0x61)) 12 (by decide) (UInt64.ofBytes 0x76 0x6f 0x20 0x6e 0x6f 0x69 0x74 0x69)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x77 0x6f 0x6c 0x66 0x72 0x65)) 14 (by decide) (UInt64.ofBytes 0x52 0x1 0x82 0x44 0x60 0x0 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x64 0x60 0x3 0x90 0x81 0x90 0x51 0x90)) 16 (by decide) (UInt64.ofBytes 0x85 0x7b 0x42 0x61 0x5b 0xfd 0x90 0x1))

private def absorbed125 : Vector UInt64 25 :=
  #v[0x744e1205f7b0c0e3, 0x589e2898b0170391, 0xe8598f4e6cff83f5, 0x41adc8f730cb3b76, 0xb3bb4f507eeedd3b, 0x443a36356f6bcb48, 0xa0daf7e62727b4b0, 0xb31da47605d9f71f, 0xaf31058e9e6ca9ae, 0x3f2debeb51da6fcd, 0x1690130d34c55a08, 0xeb0848132b3fb33a, 0x21b27e0478e1920f, 0x2f37602a7b85e679, 0x92f3685f8463f68, 0x75ea4099d37f48a6, 0xbdab4269498a3dc4, 0x6f837d6e212623c4, 0xc4b77f76c022224f, 0x33dfef3bbd330845, 0x593cdfcf4e8d205a, 0x763ac4754f475d75, 0x3ec96794fe69f769, 0x27f187f374c649f7, 0x1559fc5321d32d13]

private theorem words125 : absorb125 state125 = absorbed125 := by
  decide +kernel

private def quarter125_1 : Vector UInt64 25 :=
  #v[0x62ee1af9c3422d84, 0x4a1ff969980ba2bb, 0xb614925fb906746f, 0xda89af6f2bc7d97f, 0xcc66171c8fb610, 0x583d65b3f8385f3e, 0xe7d57f487b4bc09e, 0x6ed0da319a87a4c3, 0x5f25ffbd76ca1421, 0x5db069bdf0c3861, 0x7579c49a47963f1, 0xb60ad510c7e8ae48, 0x2a4d99b645ab8b1b, 0x22e5fb2c0a30e81c, 0xcf0f6902476c9f8b, 0x148a3320a0ecc2e0, 0xddffcd7cfa9b8597, 0xdbafebadec944698, 0x6aa7defc6b3f435b, 0x5c644cfa5b6d2222, 0xbd7643433131c513, 0x8927fea39bb011bf, 0x28ee69f8360dfb6d, 0xcd8e6815e68b1797, 0x77e9387c1209953a]

private theorem rounds125_0 : sixRounds 0 (by decide) absorbed125 = quarter125_1 := by
  decide +kernel

private def quarter125_2 : Vector UInt64 25 :=
  #v[0xaf1ff69b7f316680, 0x64fd11dc29a9ad03, 0x49dd91bd20ba3bf, 0x275839340ef97d18, 0xa8e2138de50cf275, 0xd483ded9bd4e177, 0x28f20d2934454f7f, 0xdf2d6ce2989b96ad, 0xda833444aed96ebd, 0x4fc73f70240bec19, 0x9428075f0e7f8812, 0x9778678534885d46, 0x29038ebd5b59c05b, 0x3a159341440da7c4, 0x8dec15e5bd4d0a24, 0xd26ac17c1817f63b, 0x353674a104952e8a, 0x72d60ea1eceb246c, 0x6d01e9954182f08, 0x33050845fb2a4d71, 0x53c27a72156a7143, 0xa0168532ad922b45, 0x911cba70b3a6dd33, 0x34a00767fced8745, 0xc1bec228cc01b3ca]

private theorem rounds125_1 : sixRounds 6 (by decide) quarter125_1 = quarter125_2 := by
  decide +kernel

private def quarter125_3 : Vector UInt64 25 :=
  #v[0xfe8c0f2dff4e5e7a, 0xf9e80dd42f60f846, 0xa5edab12bbea444, 0x27a1e87eff771493, 0xde6c70f93c6ded84, 0xf670fa4f0563f717, 0x93752275a2026905, 0x5d282e79b27bb5cc, 0x103f5670f9fd73fd, 0xad4cd7c04056ad7b, 0xbf6a548e10a7388b, 0xf7d28ebf45f2b676, 0xe88b28a0f78d3839, 0xcf9e211fb2f0237c, 0x4d769e99464c844d, 0x28772929a629c5f6, 0x7b5a973da3abf14, 0xd25d74764ff40801, 0xae5c7490f97462ba, 0x4a8a6e17fd35046a, 0xd6f98248935ad3fa, 0xdd51cc09356b15fa, 0x6e39f3f5b539265b, 0x7db604809936d390, 0xca657f0fcd4643a4]

private theorem rounds125_2 : sixRounds 12 (by decide) quarter125_2 = quarter125_3 := by
  decide +kernel

private theorem rounds125_3 : sixRounds 18 (by decide) quarter125_3 = state126 := by
  decide +kernel

private theorem perm125 : KECCAK.f1600 absorbed125 = state126 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds125_0, rounds125_1, rounds125_2, rounds125_3]
  rfl

theorem block125 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes125 ++ tail) state125 =
      KECCAK.Bytes.run 0 tail state126 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes125 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb125 ws)) := by
    rfl
  exact (step state125).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words125).trans perm125))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
