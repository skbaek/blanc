import Blanc.Lift.Usdc.ImplV1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb60 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x16 0xcc 0x7f 0x16 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x5c 0x81 0x80 0x32 0x87 0xb4 0xdb 0xf5)) 2 (by decide) (UInt64.ofBytes 0xff 0x6c 0x73 0x6 0xbd 0x9d 0xe0 0x1e)) 3 (by decide) (UInt64.ofBytes 0xa0 0x71 0x7a 0xcf 0x12 0x44 0x18 0xcc)) 4 (by decide) (UInt64.ofBytes 0x60 0x84 0xa5 0x7c 0x39 0x5d 0xb7 0xfd)) 5 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x82 0x80 0x51 0x40)) 6 (by decide) (UInt64.ofBytes 0x80 0x51 0x40 0x60 0x50 0x50 0x91 0x1)) 7 (by decide) (UInt64.ofBytes 0xff 0x73 0x0 0x60 0xa2 0x90 0x3 0x91)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x33 0x16 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xad 0x52 0xf2 0xdd 0x7f 0x16 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x68 0xb0 0xc2 0x69 0x9b 0xc8 0xe2 0x1b)) 15 (by decide) (UInt64.ofBytes 0xf1 0xa7 0x2b 0x95 0xaa 0x8d 0x37 0xfc)) 16 (by decide) (UInt64.ofBytes 0x4d 0x5a 0xf5 0x28 0x16 0xa1 0xc4 0x63))

private def absorbed60 : Vector UInt64 25 :=
  #v[0xac6997487879f09, 0x9dd6f25cd6681390, 0x48ce33dad492db8b, 0xec8ea64a334db646, 0xc557f990bd6685ff, 0xd2efc54dfc282575, 0xe6ba828fc7a65a25, 0x953be62b37748a3a, 0xa1049cca28b8465b, 0x908074552fd5d4cc, 0x4e574e7f467d2d8, 0xb65c6b1cd7bbe9c7, 0x60a960259b65d9c9, 0xc77856ecc6fef0ff, 0x3c44bf7632b05037, 0x67257a7df6f6876a, 0xbb88324317536fe9, 0xc8d34d4ed72e971f, 0x5bbdfbb4a35104b6, 0x64433337e24e0d80, 0xc0cad2d159ec4805, 0x77d8839c99e91a37, 0xf19dacbddcad84c0, 0x484bfdbee8c37ce1, 0x110ff1d39cda3944]

private theorem words60 : absorb60 state60 = absorbed60 := by
  decide +kernel

private def quarter60_1 : Vector UInt64 25 :=
  #v[0xbab43a15ccab1261, 0x4608146e86ca3452, 0x33aca84a0ce4d54, 0x572253ad2c212546, 0x69859d50259d7354, 0xc66da879f6c4d1a7, 0x65d0167b63de5713, 0xbf8fed900f272bab, 0x4444318c441647d1, 0xcabe8699c79f9459, 0xae26a77d55dc97b7, 0x12d245d99a81f552, 0xf2fee718271929b2, 0x51e83be1ad0898b9, 0xd10c22f64180ce4c, 0xc6fc53b5ef73af95, 0x9d8b134aec41c007, 0x48928c87ab9b1a76, 0x7358b6982c03ea22, 0xdb31272463fce162, 0x8674be15e7df7d3d, 0xb2ecefd7cee88bd4, 0xbb847bb84bafab5b, 0xeeb4006cbc4946e, 0x2c95374ccbf579a9]

private theorem rounds60_0 : sixRounds 0 (by decide) absorbed60 = quarter60_1 := by
  decide +kernel

private def quarter60_2 : Vector UInt64 25 :=
  #v[0xe28367dd190edcb4, 0x841637517e816d3a, 0xde7890f9e394ef49, 0x8d71d952f3ebb856, 0xfa4751d5e1fd6b64, 0x174211601045fb88, 0xfde0767e5fe425b2, 0x3e5cd7b5d185971d, 0x8be8d9f8710691c2, 0x4df97725f51d5141, 0x84a1802b53d5135e, 0xb320bc595b228362, 0x4c44722ec98da326, 0xf5476cb378a4fe4b, 0xf87aa926f054e518, 0xe38297ad72c10687, 0x59bc91ac75d5a80f, 0x8d4253962d4b12f4, 0xe8ab23f36982e798, 0x3b2daee6c2434706, 0x9014a1499988db3a, 0xa737e52493128461, 0x67db7138fcffd63d, 0xd022ec61e6adbd17, 0x67c374639f79ce3a]

private theorem rounds60_1 : sixRounds 6 (by decide) quarter60_1 = quarter60_2 := by
  decide +kernel

private def quarter60_3 : Vector UInt64 25 :=
  #v[0x4ea1e4f7a7cbcc37, 0xfee28d254388a9df, 0x777c4ab23da4e97, 0xc70fdff636306297, 0xab55b60bf3774ffa, 0x1628b7af97415ad7, 0x160db7e6ea62316c, 0x5d4f6c4b9727920c, 0xf0f37a9a07d3d1a9, 0xca1c3d7b71f7aa7a, 0xba0c0534df0eb989, 0xb816fb831a277256, 0x3687058a7a41f744, 0x6baeae434cecc7d7, 0xac3827259aa72453, 0x463ad4f5db356122, 0x78bf150ea4c5e75a, 0x5dc390428f41852, 0x387988f3eb1a6b0f, 0x482b0b071cc75dda, 0x86cfd92cdcc5fd22, 0x291160a448207245, 0x24eb3bf14abc939e, 0xc58bdeea6c1723dd, 0xdd6012d369cd9ed8]

private theorem rounds60_2 : sixRounds 12 (by decide) quarter60_2 = quarter60_3 := by
  decide +kernel

private theorem rounds60_3 : sixRounds 18 (by decide) quarter60_3 = state61 := by
  decide +kernel

private theorem perm60 : KECCAK.f1600 absorbed60 = state61 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds60_0, rounds60_1, rounds60_2, rounds60_3]
  rfl

theorem block60 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes60 ++ tail) state60 =
      KECCAK.Bytes.run 0 tail state61 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes60 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb60 ws)) := by
    rfl
  exact (step state60).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words60).trans perm60))

private def absorb61 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x85 0xef 0xb3 0x23 0xf5)) 1 (by decide) (UInt64.ofBytes 0x91 0x1 0x20 0x60 0x52 0x81 0x82 0x80)) 2 (by decide) (UInt64.ofBytes 0x3 0x91 0x80 0x51 0x40 0x60 0x50 0x50)) 3 (by decide) (UInt64.ofBytes 0x60 0x5b 0x56 0x50 0x50 0x50 0xa3 0x90)) 4 (by decide) (UInt64.ofBytes 0x90 0x54 0x90 0x14 0x60 0x1 0x60 0x0)) 5 (by decide) (UInt64.ofBytes 0xff 0x60 0x4 0x90 0xa 0x0 0x1 0x61)) 6 (by decide) (UInt64.ofBytes 0x57 0xff 0x1f 0x61 0x15 0x15 0x15 0x16)) 7 (by decide) (UInt64.ofBytes 0x60 0x8 0x60 0x5b 0xfd 0x80 0x0 0x60)) 8 (by decide) (UInt64.ofBytes 0xa 0x0 0x1 0x61 0x90 0x54 0x90 0x0)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x4 0x90)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x73 0x33 0x16 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed61 : Vector UInt64 25 :=
  #v[0xbef8a918877b662a, 0x469cd4ba8608dbb, 0x3c45ebacf499fdae, 0x5272d417aedfe493, 0x92fd14aa515e21c2, 0x4d2c09bdd8d9d97d, 0x27f3f2a910b0297f, 0xd939784e8a70a1d, 0x8eac35d0f72cb6c4, 0xd1c1ecab2ef05e1c, 0x51bf650c9bba811f, 0xa2da561481dd54a, 0x8c2b9846075be654, 0xde9ffdd34492326b, 0x72e199fc61f1126e, 0xf90417086b5a858b, 0xb995b1e8dcacbfff, 0xd0a143de77141e55, 0xc779c767bc2306e2, 0xeac373c4b7526487, 0xd052b59305f14ffc, 0x6a3cb4e799e4323a, 0xe638c41a4616b098, 0x13c701038255b18c, 0xc8e6048b088fb771]

private theorem words61 : absorb61 state61 = absorbed61 := by
  decide +kernel

private def quarter61_1 : Vector UInt64 25 :=
  #v[0xdb907e2a0ddcec72, 0xf1b9b83ecc3f9619, 0xbd7a806a1444878a, 0x3f847ddd34afe1bc, 0x7b1d7e0daf711025, 0x55a9d7c930b4b85, 0xb121f01c9e9f1d87, 0xfda15b0d9db015d5, 0xb412bb6fda6aebb3, 0x95572d85a247e2c, 0x769b50c5693742ee, 0x987b78eb51b43d33, 0xa9dd8156491a5b2b, 0x7257b8572e8ccb2, 0x9137bdb0ff5a7377, 0xd283ce1984d7e35, 0x410e28f1da36b5d9, 0x9761c0dba7106d9a, 0x32b910fd27f115b6, 0xa6587544ace64028, 0xc0c3a31feb0ecc99, 0x57ee2ccf433a8873, 0xf748998b15a7db84, 0xdaab83644caa33ae, 0x1a699035e1ab0b3]

private theorem rounds61_0 : sixRounds 0 (by decide) absorbed61 = quarter61_1 := by
  decide +kernel

private def quarter61_2 : Vector UInt64 25 :=
  #v[0xb842415d4980713d, 0x4c803cb3b431f14b, 0x76ae5af5cf383ff8, 0xe99053e7c9d0e860, 0xd8d277d06d43f5d1, 0x130bb2a90f173c82, 0x6f5363f2acdd0d96, 0xe7e64a876e44be62, 0xb0fd2424a2c78707, 0xeb57063a44f7f48, 0x6c60039ceaddb03d, 0xc0bd935a9404cdd8, 0x39987a72a56a4830, 0xae67c81b1bbd2c, 0xc069db8a061f24cf, 0x9010847bff823e8a, 0xc12059c2e6c9a5f, 0x74c028611817b36d, 0x5a16d4b053f76c05, 0xb8e8af0abb67b39, 0x2a1e8aceb0b25ea0, 0xf035f93944d3ed7c, 0x12976684f1eaf227, 0xe16257c43ed462ee, 0xdcd15c512230c499]

private theorem rounds61_1 : sixRounds 6 (by decide) quarter61_1 = quarter61_2 := by
  decide +kernel

private def quarter61_3 : Vector UInt64 25 :=
  #v[0x9b588abf518fa4db, 0x15776c359e76b5c7, 0xd25378e44519ad5e, 0x296bed80db6703d1, 0xc7281ef593e7ed90, 0x9dfb4ad886a2a0a3, 0xfd6395ec3a3c2761, 0x757a009164b24a25, 0x7bdd15bcc577f874, 0xfb86dcc78ccc105b, 0x3652d166d20202c7, 0xed012484764c19bb, 0xbb2f210520939a49, 0x298c5b5fdf80c050, 0xa75818b012210074, 0x26eb50e743b5408c, 0x2877a5b88866d41c, 0x3842a2524ce95aef, 0x55c80a28a47a2c85, 0x4fd7cb1023b2338c, 0x502004709f4a9b56, 0x771fb373097ae2c7, 0x19224d59febc9c5b, 0x61c4655ef958fb6c, 0xb3d3fddf2caef9a1]

private theorem rounds61_2 : sixRounds 12 (by decide) quarter61_2 = quarter61_3 := by
  decide +kernel

private theorem rounds61_3 : sixRounds 18 (by decide) quarter61_3 = state62 := by
  decide +kernel

private theorem perm61 : KECCAK.f1600 absorbed61 = state62 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds61_0, rounds61_1, rounds61_2, rounds61_3]
  rfl

theorem block61 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes61 ++ tail) state61 =
      KECCAK.Bytes.run 0 tail state62 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes61 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb61 ws)) := by
    rfl
  exact (step state61).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words61).trans perm61))

private def absorb62 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x15 0x15 0x14 0x16 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xfd 0x80 0x0 0x60 0x57 0x5b 0x20 0x61)) 2 (by decide) (UInt64.ofBytes 0x85 0x0 0x60 0xc 0x60 0x1 0x60 0x5b)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0x73 0x16 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x16 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x60 0x1 0x20 0x60 0x52 0x81 0x90 0x1)) 10 (by decide) (UInt64.ofBytes 0xa 0x0 0x1 0x61 0x0 0x60 0x20 0x0)) 11 (by decide) (UInt64.ofBytes 0x16 0x19 0x2 0xff 0x60 0x81 0x54 0x81)) 12 (by decide) (UInt64.ofBytes 0x55 0x90 0x17 0x2 0x15 0x15 0x83 0x90)) 13 (by decide) (UInt64.ofBytes 0x73 0x85 0x0 0x60 0xd 0x60 0x81 0x50)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x16 0xff 0xff 0xff 0xff))

private def absorbed62 : Vector UInt64 25 :=
  #v[0xb353067f0053ff5e, 0x6676ca22dfc1a701, 0x1a582c74939f5ead, 0xbf3c49942ca07096, 0x702abcd01010a7c5, 0xac119a911cb66ca8, 0x9b9cd785ff2e5c49, 0x45b3b1753170bcee, 0x42be747b3157f902, 0x92ab8f9aee65606e, 0xf6a4dc7e8a756d2, 0x14ac848b89ed98ec, 0x5e951fc2cd5f803e, 0xd723f32d71edd469, 0x4f44463088ac3ff8, 0x1e4877bd7c65fb13, 0xfb5f666ac7afad63, 0xa683fa3dc45131ff, 0xd05cff7deea135bb, 0x48b6983eee5de862, 0xacd6ef00e3f400cd, 0xaf996ce0a7203199, 0xfff8abc2b79e64c5, 0xd8d96d26184c8c36, 0xa1a187d39b58654a]

private theorem words62 : absorb62 state62 = absorbed62 := by
  decide +kernel

private def quarter62_1 : Vector UInt64 25 :=
  #v[0x4cfd4ade30f70deb, 0x23f63c9bce07914a, 0x6546cb0881d2825e, 0xd261a8ffde070f69, 0xf40eddad9f2d8f31, 0xb479616c3f7c0440, 0xd1c0a8ecae5895f9, 0x36287c94ab6b3d07, 0xb31fd021816800ef, 0xcf7cfab6c5dc93de, 0xbb9b0a99a5288429, 0x108274718d1f12f9, 0xde1e628b325af779, 0xd54a24983f5beaab, 0x453edde4123c7dc1, 0x814a5ddf970346db, 0x764f03ceb71f5de9, 0x350a281f42fda601, 0x784bade30aacd18a, 0x8724b5373ac2dcea, 0xcaab08fe7297778d, 0xca4b594e4a8c1feb, 0xe467d3877b4fd9c1, 0x620d3d49cab333fb, 0xd697268a5c151062]

private theorem rounds62_0 : sixRounds 0 (by decide) absorbed62 = quarter62_1 := by
  decide +kernel

private def quarter62_2 : Vector UInt64 25 :=
  #v[0x9b45a143257e92e6, 0xbbf21d86490b5afd, 0x44f3cb5af3b35313, 0xa56e419cadc624d1, 0x913bc8ae89cfa09b, 0x7c6ac2e2288d07fe, 0x2a07bf5aebcd69f4, 0xbbb678b706104fcd, 0xe35674d82ae6bf4a, 0x56dfe6ae4f59f680, 0x9518ae72ccc86424, 0x43adf27307050093, 0xe507fd16563bdd46, 0xc00c8d6572b11139, 0xdaa1b6258ee82500, 0x9e7be1557104a29d, 0xd44b85480a1e0735, 0x4ac9fa795133f7c, 0x7ba4a59927947d02, 0xd6b1a5e06a72f3f9, 0x8f43164adfacdd4e, 0xb36b63bf71b72e43, 0xc8c1cc7baba623ed, 0xcc4e958c1cb77738, 0x111f0bc86bfcc09a]

private theorem rounds62_1 : sixRounds 6 (by decide) quarter62_1 = quarter62_2 := by
  decide +kernel

private def quarter62_3 : Vector UInt64 25 :=
  #v[0x7f982fda7dcbb797, 0x25bc69309e32c285, 0x5ff94d7b3faea8f7, 0x1ae4480e4bcdb3e4, 0x8131973613ef578b, 0xd3c5eca3bbee140b, 0xf49c20d89c300340, 0x3c3d52e61c0c786f, 0x19206e61ffaad28d, 0x269ba4b6838fcb8c, 0x5e1c83323731348b, 0x6f65062466226d76, 0x4c9a3a8a870f6314, 0xb6658f3c8b4889e9, 0x606d0c6fd1ff0b66, 0x253a47cb8961af23, 0xbe1701a68ecaf83b, 0x28c9f9973d7eb3b8, 0xeb0e46dcd97b7216, 0xf12419462b002dfb, 0x6d34a359343f6423, 0x8cf369551054bfa8, 0xb33dd215ca037979, 0xb1a54eecc3634ac0, 0xf96a70bde400884]

private theorem rounds62_2 : sixRounds 12 (by decide) quarter62_2 = quarter62_3 := by
  decide +kernel

private theorem rounds62_3 : sixRounds 18 (by decide) quarter62_3 = state63 := by
  decide +kernel

private theorem perm62 : KECCAK.f1600 absorbed62 = state63 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds62_0, rounds62_1, rounds62_2, rounds62_3]
  rfl

theorem block62 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes62 ++ tail) state62 =
      KECCAK.Bytes.run 0 tail state63 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes62 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb62 ws)) := by
    rfl
  exact (step state62).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words62).trans perm62))

private def absorb63 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x16 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x0 0x60 0x1 0x20 0x60 0x52 0x81 0x90)) 4 (by decide) (UInt64.ofBytes 0xff 0x73 0x82 0x50 0x55 0x90 0x81 0x20)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xf 0x98 0x46 0x7f 0x16 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x68 0xd3 0xdb 0xbc 0xf9 0x2e 0x91 0xca)) 9 (by decide) (UInt64.ofBytes 0x76 0x60 0xe8 0x90 0x6b 0x7b 0x42 0x77)) 10 (by decide) (UInt64.ofBytes 0x20 0x77 0xe6 0xc0 0x89 0x4e 0x60 0x9f)) 11 (by decide) (UInt64.ofBytes 0x40 0x60 0x83 0x20 0xd 0x53 0xce 0xce)) 12 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x82 0x80 0x51)) 13 (by decide) (UInt64.ofBytes 0x91 0x80 0x51 0x40 0x60 0x50 0x50 0x91)) 14 (by decide) (UInt64.ofBytes 0x92 0x50 0x90 0x1 0x60 0xa2 0x90 0x3)) 15 (by decide) (UInt64.ofBytes 0x57 0x21 0x61 0x5b 0x56 0x50 0x50 0x91)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x5b 0x56 0xbe 0x23 0x61))

private def absorbed63 : Vector UInt64 25 :=
  #v[0x4b06b3566b210829, 0xe4eea4d070e15f9c, 0xe8f47a10b1f95999, 0xd9acedfdf1773c92, 0x300f04ab198b966d, 0x5e67658b820d2873, 0x4daebd17e69978cb, 0x4a29c9b2f5644f26, 0x4c011d2f900d2932, 0xd501beb0815ffa84, 0xa5c12a1de92185c3, 0x259e5a885c63a86a, 0xa661f366f80f6f1, 0x1f640939dd3d93de, 0x3cd0e6c621d76c7d, 0x87d86164c084cedf, 0x57228f4724c7378, 0xf3827eb6af0a4b, 0xee7496a6255471c7, 0x97699181d11014b7, 0xc9e004a9c7385739, 0xb77b05ca0af97c6e, 0xc815662980886013, 0x11ca55f92757bbb6, 0x4c52b773c619a77b]

private theorem words63 : absorb63 state63 = absorbed63 := by
  decide +kernel

private def quarter63_1 : Vector UInt64 25 :=
  #v[0x65ffdf4740cc039b, 0x2125fddd1ae597ca, 0xc3ed43fd5f6fac35, 0x9a6b4ff5066ab262, 0x874ef4c31cdb6558, 0x197c6dbc41712c43, 0x35ac6342a73ea3d6, 0xce64d0e54dded119, 0x7a73837bba954133, 0x95c08db793b4d9dc, 0x4262ce2aeb6746e0, 0x9843e47e15bc2b0, 0x32bd0f5a966a785e, 0x3637079e15beb7dc, 0x290de581380de659, 0x4b550923b6e449bd, 0x6f5df501b2e0e2c3, 0xf4fbb978cef6f046, 0xa279afe4dc8ad3d5, 0xbd06c5ebe7a32d7f, 0x380e147a241747fc, 0x502bf6ab9b85377b, 0xfc8b65eec6ff9bcf, 0x32245bbc90f2e2c7, 0xba094ae08665fb1e]

private theorem rounds63_0 : sixRounds 0 (by decide) absorbed63 = quarter63_1 := by
  decide +kernel

private def quarter63_2 : Vector UInt64 25 :=
  #v[0x1f3aac54a710e601, 0xe0fd4f97fb6367fb, 0x7e3c50b08bb5936b, 0x7657c8814614be27, 0xe713c0265c33c3e9, 0x4bafbe6d144827ef, 0x4ea48edb8afa08d3, 0xcf04c14ac4d9e8d, 0x27fa708177743bb0, 0xdb9384f44c1a8eae, 0xcbeebd2386d68603, 0xce5309eb18511530, 0xe22e9fa963122f84, 0xb1fd1d6032c80867, 0x896517e0105c9625, 0xa7d7032efde956e2, 0xb25f37847ccb3500, 0x5909c7289dc4cf56, 0x8f71750ceadefd02, 0x55a71b7565513e64, 0xf419068ca7e789e3, 0x3be3a789bd81c714, 0xef811f73e55a1302, 0x4e64d5723748975d, 0x515a61a21dff47c]

private theorem rounds63_1 : sixRounds 6 (by decide) quarter63_1 = quarter63_2 := by
  decide +kernel

private def quarter63_3 : Vector UInt64 25 :=
  #v[0xe5d1f05b072753c4, 0x47fc3bb67bea461b, 0x39de4a023bf74544, 0x45a08593ca8a29c9, 0xd72bbc083bd42ffd, 0x5e7e3e5a1d1b752b, 0x80babe60d2269ee8, 0x41b73cefc9857ac4, 0x9148c15579887455, 0xb2341d5a8f8a8da3, 0xd8c97c4de541e78c, 0xb6e1c4725b645381, 0xfc289b1c751221af, 0x3d01527ab46ed817, 0xa5a613d74efc33d5, 0xc1a61b6dc83cc33e, 0x5c542b53c5e30e0d, 0x279eec942ac9d377, 0xf2dcd9be83697fa7, 0x52423f5ffa416a, 0x7000495d15a4d0f7, 0xb40e1efd2f7a3311, 0xaefc9593f187aadb, 0x70c66ae932fc7160, 0x50bd8fe0d02cd2d5]

private theorem rounds63_2 : sixRounds 12 (by decide) quarter63_2 = quarter63_3 := by
  decide +kernel

private theorem rounds63_3 : sixRounds 18 (by decide) quarter63_3 = state64 := by
  decide +kernel

private theorem perm63 : KECCAK.f1600 absorbed63 = state64 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds63_0, rounds63_1, rounds63_2, rounds63_3]
  rfl

theorem block63 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes63 ++ tail) state63 =
      KECCAK.Bytes.run 0 tail state64 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes63 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb63 ws)) := by
    rfl
  exact (step state63).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words63).trans perm63))

private def absorb64 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x33 0x16 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x90 0x21 0x61 0x15 0x15 0x14 0x16 0xff)) 6 (by decide) (UInt64.ofBytes 0x0 0x60 0x5b 0xfd 0x80 0x0 0x60 0x57)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x73 0x81 0x16 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x15 0x15 0x14 0x16 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x80 0x0 0x60 0x57 0xcc 0x21 0x61 0x15)) 14 (by decide) (UInt64.ofBytes 0x61 0x0 0x60 0x1 0x60 0x80 0x5b 0xfd)) 15 (by decide) (UInt64.ofBytes 0xff 0x73 0x81 0x54 0x81 0xa 0x0 0x1)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed64 : Vector UInt64 25 :=
  #v[0xc1573beb47ddc9e2, 0x1e9b63a5b9dafb97, 0xd7ef06667add9408, 0x40d1c837664def09, 0xbf9bbb1871f48fe0, 0x7ca36cc2da8334f1, 0xd06a118c24a832bc, 0xb6a692ca029a5350, 0xac9d851d199e71e, 0x59d51ba20d571e57, 0x749a2e31bdece898, 0x1d9617419b9ebc6b, 0x34549f9084dcd4ae, 0xe0224137d24ef964, 0x330e2ae2bbc9f84f, 0x49742b591ecf3452, 0xaad4fb3f90523ed7, 0x21f815fb7147460, 0xbe504e5fa44785db, 0xf956ab624a38722f, 0x7c499e787c0cd596, 0x4ce27a4099e2052c, 0x38b6e0ffd21e7483, 0xf1d9e3bd87b2301d, 0x40fdc854908f80f2]

private theorem words64 : absorb64 state64 = absorbed64 := by
  decide +kernel

private def quarter64_1 : Vector UInt64 25 :=
  #v[0x4e9b3effb937c6a8, 0xd68f85c8f203dc39, 0xad26e86a5356ce4d, 0xb8750eea1e744118, 0x551fe35077387712, 0x7f004130547196b0, 0x8e5a51c38a073ce3, 0xfdb02e1f5870eb56, 0xaed2f9a317405d55, 0xba05d7d6595443d1, 0x996ad66e8656f183, 0x441b3236fbc551b7, 0xb5a303f1dd0877aa, 0x7d2a4f153fda92ab, 0x53e248672a7a6b54, 0x4c29d1213c638728, 0x60c0e76a2607acfe, 0x3e6c5b4a330330ce, 0x3dd4b8e481ec680a, 0x8616ff30c56112c2, 0x6f878b8c23346041, 0x92dd271e68e2845a, 0xe1d5b81f3f829d6, 0x10dfe823d39f3e65, 0x87513c786c95f41d]

private theorem rounds64_0 : sixRounds 0 (by decide) absorbed64 = quarter64_1 := by
  decide +kernel

private def quarter64_2 : Vector UInt64 25 :=
  #v[0x2dac4a62de58e244, 0x3bbfa84e79348ee6, 0x95f6c329b5095eba, 0xd292ca40395fa394, 0x730c0b9ef60a974f, 0x68fcf9e82fcdea4a, 0xe133e4d2b77fd3d8, 0x25b137dde5817a22, 0xf39d535631171b90, 0x9d35ca460cf2ecde, 0x8d0aa0221063c41a, 0x9c96bb4e131225e, 0xd58a0246b269772, 0xa279ef9b99eabf77, 0x93db234717387582, 0xcf426aea5688c9a0, 0xac2d3bda76cd9328, 0x13514b30c1edf17d, 0x2679219275365c78, 0x8b12fa0eab79a341, 0xa4ca5c755d8d56ac, 0xddb072482cda2159, 0x98af1af741b79139, 0x569d7adcbacd1e5, 0x1812dbb2b744bd21]

private theorem rounds64_1 : sixRounds 6 (by decide) quarter64_1 = quarter64_2 := by
  decide +kernel

private def quarter64_3 : Vector UInt64 25 :=
  #v[0x285575df43441d46, 0xe990194192a49c19, 0x3d252d844ba8ecd7, 0x640f3727bca61f9c, 0x815d645b9bf9c3d3, 0xf6d03b748887c632, 0xc5f20571d51ea09f, 0x130834cadbca835b, 0xd124c81e36792a47, 0xfe12eabd17d06648, 0xd9e2b18c1c1bd9e2, 0x21bd4674d70f6149, 0xbc6b365dd59947fd, 0xc59b881dea4e5aaa, 0x429dabc42b2d947a, 0xa2663e4d9564361c, 0x9e4d3910a9697e36, 0xaab8b9d44b425a6c, 0x16887025f19bf1d8, 0xdb9a8d53f937279c, 0xaacc124e603570f3, 0x9326eb256cdd2728, 0x69ea663fc4873020, 0xab5a9d38e43e7ba5, 0xb71986451a25b9ac]

private theorem rounds64_2 : sixRounds 12 (by decide) quarter64_2 = quarter64_3 := by
  decide +kernel

private theorem rounds64_3 : sixRounds 18 (by decide) quarter64_3 = state65 := by
  decide +kernel

private theorem perm64 : KECCAK.f1600 absorbed64 = state65 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds64_0, rounds64_1, rounds64_2, rounds64_3]
  rfl

theorem block64 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes64 ++ tail) state64 =
      KECCAK.Bytes.run 0 tail state65 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes64 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb64 ws)) := by
    rfl
  exact (step state64).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words64).trans perm64))

private def absorb65 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x83 0x90 0x16 0x19 0x2 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x17 0x2 0x16 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x90 0x0 0x60 0x1 0x60 0x50 0x55 0x90)) 6 (by decide) (UInt64.ofBytes 0x4 0x90 0xa 0x0 0x1 0x61 0x90 0x54)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0x73 0x16 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x82 0x4 0xb8 0x7f 0x16 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x86 0xda 0x3e 0x1 0x2e 0xca 0x93 0xa2)) 14 (by decide) (UInt64.ofBytes 0xfd 0x7c 0x34 0xc8 0x7f 0xbd 0xc9 0x83)) 15 (by decide) (UInt64.ofBytes 0x6d 0xa4 0xcb 0x58 0xde 0x5e 0xea 0xae)) 16 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x4 0xa6 0xc2 0x2 0xf5))

private def absorbed65 : Vector UInt64 25 :=
  #v[0x51b39313fb9626a6, 0x1c01ee86820c9a23, 0xfd1a03f8a397ad4, 0xcb9d357c07bde7d9, 0xfb170e0c7cbdbac5, 0xb0f094c9bbb9c8b8, 0x6865fedb80f59920, 0xc21c1ff6efababd2, 0x302ec9b5c95b2300, 0xbe57f3ca5a195174, 0x4320e0ace01b05a5, 0x2489e0b1a9961b07, 0xce834644bbb88fb, 0x10919501814f3737, 0x8aebe20eb5d3967d, 0x1b53b2911c6819fc, 0x5679e6f335679949, 0xf865a49f08fa57df, 0xcab49104753396c6, 0xb7417a93b63157eb, 0x42d59ff2d4ec7200, 0x72aabd0e22b9d4f9, 0xdd9e7c47b32bfecc, 0x415fdfec757f1abf, 0x6e95b4dca2295996]

private theorem words65 : absorb65 state65 = absorbed65 := by
  decide +kernel

private def quarter65_1 : Vector UInt64 25 :=
  #v[0x86320590ec7c6c12, 0xdac84216e3a62075, 0xf17ae8b1f0381da3, 0x2f0e69c2c7388ad7, 0xa4440953823c6b16, 0x514d76132d09654, 0x56c2a6823973b345, 0x9fae93c5ee46d9c5, 0xe359a0d95b957f33, 0x28725caa5a3554e, 0xc6b2a97e502089ec, 0x9463ccaf0dd59bd2, 0x2118998aafa77498, 0xafcddeb25bd98754, 0x74712bb7fba4f295, 0x629171fa0cabf320, 0x4805c563014f927d, 0x5f05cc568e8c354a, 0x30d3a60c539fc89c, 0xc0cec0d2532ab7c1, 0xe10eff0a4f5f1c96, 0x589b2219c3441b9a, 0x4c6db264b3b82e6f, 0x90debf401fa9e33c, 0x9921d2bc4a188f7]

private theorem rounds65_0 : sixRounds 0 (by decide) absorbed65 = quarter65_1 := by
  decide +kernel

private def quarter65_2 : Vector UInt64 25 :=
  #v[0xde2b2251800b838f, 0x503412298a716038, 0x2ed57a17892ba52d, 0xfd6167815d0f3a4, 0x59b33c2d0edbf6a2, 0xb35e9f7320fc01b9, 0xe733c9e9871bb590, 0x72bd7fd5e42617cd, 0x8ae9a10adf07fc2d, 0xb73fc093e7cad84b, 0x739f982bd11477d3, 0x742b15ebaf73200e, 0xeee99311fcbc5507, 0xe72ade512c7fd46c, 0xcca4ce4292ab55b2, 0x63284410ef3a0934, 0x9aa45db91a3af0f4, 0x2f5dd03d4cb67cca, 0x6d60a2b9bd2d0f76, 0x7dd786d05e995ea8, 0x5e3ddf5e0a26a93e, 0x2599982ace430952, 0x19a2147ada4ec4b5, 0x6d1e0e989d89931b, 0x23964d3cbdfdd1f2]

private theorem rounds65_1 : sixRounds 6 (by decide) quarter65_1 = quarter65_2 := by
  decide +kernel

private def quarter65_3 : Vector UInt64 25 :=
  #v[0x41a3b158f290d707, 0xee7b78d19ccb485, 0xe45fb07866e49b4a, 0xb092ea09afd50b56, 0xd6e06672ff5e40e6, 0xf1d0b64cc71f67e1, 0x1278da43cdbec69c, 0x966bc39c3b8bf254, 0x13a38af8ff78be60, 0xc70cee49c566534c, 0x2dea211ef55362e4, 0x49fa73cf236b0bae, 0x9072c780fd73fe0c, 0xf201ee866a889f8c, 0x4612e26d41b1ad2, 0x2d6ef7b05a370637, 0xd526eb3855feb12d, 0x1583e8fc08eba127, 0xab6349daf6303d9f, 0xdb40370e0d066064, 0xd413da8e49ee17e5, 0xad6208376825cc4b, 0xe22d4c19ea0daf3e, 0xb67a125471a2e8aa, 0x8f12fb3bf9543bae]

private theorem rounds65_2 : sixRounds 12 (by decide) quarter65_2 = quarter65_3 := by
  decide +kernel

private theorem rounds65_3 : sixRounds 18 (by decide) quarter65_3 = state66 := by
  decide +kernel

private theorem perm65 : KECCAK.f1600 absorbed65 = state66 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds65_0, rounds65_1, rounds65_2, rounds65_3]
  rfl

theorem block65 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes65 ++ tail) state65 =
      KECCAK.Bytes.run 0 tail state66 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes65 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb65 ws)) := by
    rfl
  exact (step state65).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words65).trans perm65))

end Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
