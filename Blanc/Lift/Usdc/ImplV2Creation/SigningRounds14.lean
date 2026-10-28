import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb084 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x60 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x81 0x90 0x51 0x90 0x52 0x1 0x82 0x44)) 3 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x90 0x1 0x64 0x60 0x3 0x90)) 4 (by decide) (UInt64.ofBytes 0x3 0x60 0x52 0x81 0x81 0x0 0x60 0x33)) 5 (by decide) (UInt64.ofBytes 0x54 0x20 0x90 0x40 0x60 0x52 0x20 0x60)) 6 (by decide) (UInt64.ofBytes 0x57 0xae 0x2c 0x61 0x15 0x16 0xff 0x60)) 7 (by decide) (UInt64.ofBytes 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x40 0x60)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x4 0x60 0x52 0x81 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x81 0x82 0x1 0x20 0x60 0x80 0x80 0x1)) 13 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x25 0x60 0x52 0x82 0x3)) 14 (by decide) (UInt64.ofBytes 0x25 0x60 0xc5 0x59 0x61 0x80 0x1 0x20)) 15 (by decide) (UInt64.ofBytes 0x50 0x50 0x91 0x1 0x40 0x60 0x39 0x91)) 16 (by decide) (UInt64.ofBytes 0xfd 0x90 0x3 0x91 0x80 0x51 0x40 0x60))

private def absorbed084 : Vector UInt64 25 :=
  #v[0x806f53f06c17584f, 0xc618740717d31962, 0x27f2a30c4f432f0d, 0x5a053f1d48985f61, 0x78d5644b9330c58f, 0x9abd6b2e7c11e353, 0x4051675d924256c2, 0x4ad89abbb1bdf1ea, 0x2afdba8c7350b517, 0xa50c43a85992a15d, 0xcf27677eaa99d780, 0x4236b749e355bacd, 0x2b34015221596e9c, 0xc9e26de2b2c745e4, 0x458018cf056a6a88, 0xa45f4bda64791f0c, 0x7decf9338899aacb, 0xbc433b0e15d5fa7, 0xc57d0ddaafd8c755, 0x74ee5274566c09ad, 0x8872b43eddfcee78, 0x846e199919526458, 0xc719730676535457, 0x658284ea6cf9829c, 0xf316dd9ee226a843]

private theorem words084 : absorb084 state084 = absorbed084 := by
  decide +kernel

private def quarter084_1 : Vector UInt64 25 :=
  #v[0xa572e13a12cac5f1, 0x9d0088c8106de93b, 0x18927138114ad586, 0x3daeada1b7832a80, 0x9b45dfca9c345b4e, 0x1e3e89c4660c0bc9, 0x73c6a3b41c76a284, 0x17348fcb83f6e614, 0xc48df3dca89641c3, 0x7b681f37fca5d620, 0x55bb049950ac47f, 0x8b0fa236e80de12b, 0x84daa0a90f15f894, 0x20a8e650a3a2cc49, 0x4e0bac0a93695963, 0x93cf842c5c20e3e7, 0x64a9c9c1e7b0e42d, 0x8f8c4b272445c92f, 0x1131adbda7b63782, 0xdfe819f8a93a67f2, 0x53517774a48011fe, 0xfa72af91001c583f, 0x92dc094cdc2d1091, 0x1e570acf44918d05, 0xb0383222b3077354]

private theorem rounds084_0 : sixRounds 0 (by decide) absorbed084 = quarter084_1 := by
  decide +kernel

private def quarter084_2 : Vector UInt64 25 :=
  #v[0x63f31627ee1ac18a, 0x526f0726ea17bac9, 0x6a8342fb3c197461, 0xb9c8c7f9192f22c3, 0xa24727299805266e, 0x241f6797b610cd0f, 0x6cfe22e4a4fa61ed, 0x1a2b08e60c40b7c4, 0x4e237ca7e1afd857, 0xd2835730449868d7, 0xe0e063642ed8223, 0x89e91a90590d74ed, 0x743fdbd75297cf66, 0xea77ed3331e496e9, 0x40354e93f359a041, 0xeada42050589ae7f, 0x2afb957d83b2d966, 0x9abc90e253d9da49, 0x1b0ee05462e0c903, 0xaa861c4da60bfb40, 0x3efcf416a5fbdbc6, 0xd93847933129a345, 0x6e2a0489256743ac, 0x37fa42a3fea5244b, 0xe496ba4613cb5814]

private theorem rounds084_1 : sixRounds 6 (by decide) quarter084_1 = quarter084_2 := by
  decide +kernel

private def quarter084_3 : Vector UInt64 25 :=
  #v[0x7063790d71fe01ed, 0x2624562f82d92f1e, 0xa9ff377b7572f686, 0x47a228fdd36be68b, 0xc1d730f92f86c38e, 0x22d148ef5a99ca61, 0x906a00764393e3fe, 0x1331d29b3148cf22, 0x1aa001ad963418c7, 0xf47e045d63abaa61, 0x7faaa4df994d4bc5, 0x706c63f23005d4cc, 0xc91d19d788d51c2b, 0x7e902e9c48ae5147, 0x37fda6d3f0b3680a, 0x72d60b295632c304, 0x1541df24ed2aaed, 0x7480e4590bf4ccdc, 0x534e86b30c7fe2f3, 0xc0ed9b3293249838, 0xc346521af8be949a, 0xce91a6246d689b04, 0x1d1833adcbe87f8d, 0x9a9198b008cdec4f, 0xdd18340acf63e604]

private theorem rounds084_2 : sixRounds 12 (by decide) quarter084_2 = quarter084_3 := by
  decide +kernel

private theorem rounds084_3 : sixRounds 18 (by decide) quarter084_3 = state085 := by
  decide +kernel

private theorem perm084 : KECCAK.f1600 absorbed084 = state085 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds084_0, rounds084_1, rounds084_2, rounds084_3]
  rfl

theorem block084 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes084 ++ tail) state084 =
      KECCAK.Bytes.run 0 tail state085 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes084 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb084 ws)) := by
    rfl
  exact (step state084).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words084).trans perm084))

private def absorb085 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x5b)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x16 0x84 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x60 0x3 0x60 0x52 0x81 0x90 0x0 0x60)) 4 (by decide) (UInt64.ofBytes 0x84 0x54 0x20 0x90 0x40 0x60 0x52 0x20)) 5 (by decide) (UInt64.ofBytes 0x2f 0x2d 0x61 0x15 0x16 0xff 0x60 0x90)) 6 (by decide) (UInt64.ofBytes 0x79 0xc3 0x8 0x7f 0x51 0x40 0x60 0x57)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0xa0)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x0 0x0 0x0 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x82 0x1 0x20 0x60 0x80 0x80 0x1 0x4)) 12 (by decide) (UInt64.ofBytes 0x52 0x81 0x25 0x60 0x52 0x82 0x3 0x81)) 13 (by decide) (UInt64.ofBytes 0x60 0xc5 0x59 0x61 0x80 0x1 0x20 0x60)) 14 (by decide) (UInt64.ofBytes 0x50 0x91 0x1 0x40 0x60 0x39 0x91 0x25)) 15 (by decide) (UInt64.ofBytes 0x90 0x3 0x91 0x80 0x51 0x40 0x60 0x50)) 16 (by decide) (UInt64.ofBytes 0x86 0x86 0x33 0xd8 0x10 0x61 0x5b 0xfd))

private def absorbed085 : Vector UInt64 25 :=
  #v[0xbbf39e6e38b3f8c6, 0x2493aa251cbac1c6, 0x85dec4b0c8d9557b, 0x33cd71f3909497df, 0xc5d456f4c7504f8e, 0x1fcfd9712ca6c4b4, 0x246c15fa7c6a6be1, 0x8bdcb8a81641543d, 0xee7cf9616d23cd5e, 0xc98073aa1e44ab6e, 0xaa9f98923caa4ff1, 0xc494615c44d44d93, 0x83ecf12f5c09f705, 0xc956c50851298a97, 0xb69cbba2a3f366df, 0xd644b0ace8ce8cd5, 0x92f7b7203948e5c7, 0xaa20059ce417dba, 0xa7c81342042753bd, 0xe8c20467bd5e04d6, 0x7fc1df57d1a95aab, 0x5244e2daa64040c7, 0x8a6b13d7a80c595b, 0x36b372adf1239b43, 0x1d93286dfe5901cd]

private theorem words085 : absorb085 state085 = absorbed085 := by
  decide +kernel

private def quarter085_1 : Vector UInt64 25 :=
  #v[0x238210b363fbad53, 0x90c65a94859afaed, 0xaaf4df6865d89456, 0xb2b7ffa485a89476, 0x851364812f8e118c, 0x3690287c9090481e, 0xb8f2cc2573077d44, 0x8dc9eb28869680d2, 0x86c0369ecf83dfb0, 0x2b56a146cc407659, 0xabe5d2b5f93ae, 0x90b4655ffbd68b56, 0x25249c21cab02675, 0x626a122ada338c41, 0x3c1df7ee03bb33e1, 0x1f2953f45188304d, 0xe32ef2ff1edf1b1a, 0xe9ff3b6c85e9a89e, 0x7834cdcc01a7708, 0x669373c43faf8d59, 0xc37175000ccdcf96, 0xd671785bc4a57467, 0xc13272e577fc3aef, 0xf7dcfb84f60673cb, 0x87c814b93a5be058]

private theorem rounds085_0 : sixRounds 0 (by decide) absorbed085 = quarter085_1 := by
  decide +kernel

private def quarter085_2 : Vector UInt64 25 :=
  #v[0x8ada438696748b6c, 0x55f4fbb93c98d240, 0xe00a04f3f0d06251, 0xf0ea031b708b2b79, 0xff83bb24d3444d60, 0x1db3b1429288a610, 0x2c10382ba0ecf9fc, 0x3b2742b4d46efa7c, 0xe3ca7445c50ad714, 0x7928ed25b9ba5c5f, 0x9b0fd48f6e18170b, 0x83273cc44f392af2, 0xc4e1e8049215e442, 0x9f4e433acfc25435, 0x64fcf94d059dc4bd, 0xea08a26d6b9009ca, 0x268f190f8184ce93, 0x4594f95bc2f6fea5, 0x8ed4e54f96db527d, 0xa0123e6e6d2e5b9b, 0xef8b0b7fed5dec7b, 0x8d7e35b1442d1d19, 0xf5b6b2a6502128be, 0xe7c9b554cfbe80a0, 0x1f09eafd0edd0c2c]

private theorem rounds085_1 : sixRounds 6 (by decide) quarter085_1 = quarter085_2 := by
  decide +kernel

private def quarter085_3 : Vector UInt64 25 :=
  #v[0xb774e1f700a1d61a, 0x9c60b8877f5a0a59, 0x1cc988dc339ad5ca, 0xce847c1972a844b1, 0xa028578343451b86, 0x37a6eddc4f2a725e, 0x8938ad82b870045, 0x35ca2ec55a941c59, 0xa3705627d54abc, 0xd89dbce78b6e72e5, 0x47be810581108026, 0x4653c9be96eae91f, 0x631c3f3d47019fa2, 0x29c4b39013b71de7, 0xf2e8c0fe88fa30c0, 0x61f7552b4399ce9a, 0x547cb820e548a8ff, 0xaa28ac3cfa2269f9, 0x40c2ae7762aa943, 0xce04b30bc1677aff, 0x71ef402bbc2c4c6f, 0xd309be1a31c83426, 0xa95096b86a3cae2, 0xaef3854c65f8fd14, 0x485712c685f9c948]

private theorem rounds085_2 : sixRounds 12 (by decide) quarter085_2 = quarter085_3 := by
  decide +kernel

private theorem rounds085_3 : sixRounds 18 (by decide) quarter085_3 = state086 := by
  decide +kernel

private theorem perm085 : KECCAK.f1600 absorbed085 = state086 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds085_0, rounds085_1, rounds085_2, rounds085_3]
  rfl

theorem block085 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes085 ++ tail) state085 =
      KECCAK.Bytes.run 0 tail state086 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes085 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb085 ws)) := by
    rfl
  exact (step state085).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words085).trans perm085))

private def absorb086 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x54 0x0 0x60 0x5b 0x56 0xf8 0x3e 0x61)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x14 0x33 0x16 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x51 0x80 0x40 0x60 0x57 0xc0 0x2d 0x61)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8 0x7f)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x82 0x4 0x60 0x20 0x60 0x52 0x81 0x0)) 10 (by decide) (UInt64.ofBytes 0x1 0x82 0x24 0x60 0x52 0x90 0x81 0x1)) 11 (by decide) (UInt64.ofBytes 0x6c 0x62 0x61 0x6e 0x77 0x4f 0x7f 0x52)) 12 (by decide) (UInt64.ofBytes 0x65 0x6c 0x6c 0x61 0x63 0x20 0x3a 0x65)) 13 (by decide) (UInt64.ofBytes 0x74 0x6f 0x6e 0x20 0x73 0x69 0x20 0x72)) 14 (by decide) (UInt64.ofBytes 0x6e 0x77 0x6f 0x20 0x65 0x68 0x74 0x20)) 15 (by decide) (UInt64.ofBytes 0x90 0x52 0x1 0x82 0x44 0x60 0x72 0x65)) 16 (by decide) (UInt64.ofBytes 0x1 0x64 0x60 0x3 0x90 0x81 0x90 0x51))

private def absorbed086 : Vector UInt64 25 :=
  #v[0x1a57d8c67acab86b, 0x9b65cd12a44132b2, 0xb45f4fcd550de91f, 0x89039e40423b0e23, 0x76bf19e4628df2f1, 0xa52a8b2c9a0dabb2, 0x29ac574c87738014, 0x42e8ce3ac0a1f6fb, 0x9356fbe59b332cf1, 0xb896a4dc2ecf804a, 0xbaff0d2e0be481c3, 0x9df5467bd5f204dd, 0xf8c5b5664d0174c6, 0x5e15f0a22f838a56, 0x8de584d5de2ddeb2, 0x2ae6f6562225d224, 0x908b953c2b209c95, 0xa2e7cf1bec9618e1, 0x243603e2789f0404, 0x9758dda16dd35045, 0x4bf304ac160db94a, 0xe384e7b88bcaff79, 0x1e1a21ebb61c3fd1, 0x872d6007c0b981d3, 0x2712b4f01655515f]

private theorem words086 : absorb086 state086 = absorbed086 := by
  decide +kernel

private def quarter086_1 : Vector UInt64 25 :=
  #v[0xdb251489eec3e711, 0x12284fcdee04c1f9, 0xddcfe2e5fd39215a, 0x915efaecec4845fc, 0x273aeb29a031b73, 0x766fb0a130f2cde9, 0x4bd4a64ae9399f11, 0x18d2c9918d0bcce1, 0x5153c94682a7d638, 0x3d17113c1ecfa4ff, 0xf7da9704b733248e, 0xfdfd27fa273fa195, 0xab9372fa9f1dca62, 0x325eefa5565e0b13, 0x8bc48b48e15c7026, 0x53aabd4e6306e14d, 0xe4e94fae3b10c485, 0x6807822534318b8e, 0x615e982bd80f2a40, 0xcef9953e71df43b2, 0x3afcdf4679d58ceb, 0x68e0d957a435b8d1, 0x836f73eaaec5f6a3, 0x6d1e1277bab4d557, 0x8c940a7938f36d1d]

private theorem rounds086_0 : sixRounds 0 (by decide) absorbed086 = quarter086_1 := by
  decide +kernel

private def quarter086_2 : Vector UInt64 25 :=
  #v[0xe5076f5fec1e9fa2, 0xc4f5784ed46da46a, 0xfa8c1fb0acd2ce40, 0xf47c8e8cea870bd0, 0x98a7af5ab0c6e4fb, 0xb64cc81b76e9624b, 0x60b3d2fa7f1750bb, 0x6b5945f6fb3537ca, 0xad877cdbe80c7533, 0x24057ac8217c8f69, 0x2ed5d288ef6fbfbb, 0x80abec6d67c58b34, 0xd80c6201d7e20d77, 0x368828ce0fd09a96, 0x5f4095b4369922e8, 0xcd3794cd90543eaa, 0x9e941dcccc03f6d6, 0xe8aa0c26c6cb8a99, 0xb7e5329a13304041, 0x56351a96a6918566, 0x7f0cbd66172b5dc4, 0xced7a47afd6e55cb, 0x7849f67feda1b741, 0xfffe1b1dc0f3f18e, 0xe600978d76a188cd]

private theorem rounds086_1 : sixRounds 6 (by decide) quarter086_1 = quarter086_2 := by
  decide +kernel

private def quarter086_3 : Vector UInt64 25 :=
  #v[0x109880457f358f3f, 0xc34fffaa783e8577, 0x9d8629c49a944915, 0xa979838f3641d21d, 0x58d75839eaefd2e4, 0x833e5bd78f8db273, 0x9f6eb90d563a10d7, 0xcceea982fe556842, 0x3680ec1dbe83c3ff, 0xb0c9bfaa66d91030, 0xb4d6d07f6bd013b2, 0xca95a3c83515919a, 0xc9e2a127b93437e1, 0x230d8ff70b5e1a5f, 0xc7bb97b56adc0a1a, 0xd5f029a299ced0bd, 0xd2e074d97d535fd2, 0x4e074516284f1afb, 0x848b6f665343661d, 0x8fb212ce4f9fd532, 0xf84348cb197d9bf7, 0x9b4e4489bfbdab7c, 0x76388de1bbab774c, 0x836b1b7b8cf3e3c2, 0xe3aa769cd3ce3d30]

private theorem rounds086_2 : sixRounds 12 (by decide) quarter086_2 = quarter086_3 := by
  decide +kernel

private theorem rounds086_3 : sixRounds 18 (by decide) quarter086_3 = state087 := by
  decide +kernel

private theorem perm086 : KECCAK.f1600 absorbed086 = state087 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds086_0, rounds086_1, rounds086_2, rounds086_3]
  rfl

theorem block086 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes086 ++ tail) state086 =
      KECCAK.Bytes.run 0 tail state087 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes086 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb086 ws)) := by
    rfl
  exact (step state086).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words086).trans perm086))

private def absorb087 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x5b 0xfd 0x90)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x40 0x60 0x57 0x2c 0x2e 0x61 0x16 0x81)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x80 0x1 0x4 0x60 0x52 0x81 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x82 0x3 0x81 0x82 0x1 0x20 0x60 0x80)) 10 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x2f 0x60 0x52)) 11 (by decide) (UInt64.ofBytes 0x39 0x91 0x2f 0x60 0x55 0x57 0x61 0x80)) 12 (by decide) (UInt64.ofBytes 0x40 0x60 0x50 0x50 0x91 0x1 0x40 0x60)) 13 (by decide) (UInt64.ofBytes 0x60 0x5b 0xfd 0x90 0x3 0x91 0x80 0x51)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x7f 0x54 0x80 0x8)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0))

private def absorbed087 : Vector UInt64 25 :=
  #v[0x3fbeedb3a2962250, 0xf0d8eed5fa060312, 0xdadc5eb6c58cf774, 0x6073912a854f994, 0xc2d2f6e3d48d68e0, 0xdeaf32c585678a8f, 0xc81a5c75a1a90448, 0x18e8f929e35c1a38, 0x43b7809e1e985a94, 0x3761fc9421aa7438, 0x54906cf675e1eadf, 0xad992bb592c1d4a4, 0x9238f5993cf6f142, 0xa35fa7ecdfa4e621, 0x87fcad738f63b90a, 0xfad09cb3b125fffd, 0x6b104623cc1fd793, 0x53ccaa9d5bb6eaf8, 0xdbf623c353c16071, 0x6f9d2e4082aa8f63, 0x99c67963d2c1ace8, 0xda05a1a7713e801d, 0xe5c6f5d96fbc97df, 0x56c60c23a87fb720, 0xd9dbac91f98d2dfe]

private theorem words087 : absorb087 state087 = absorbed087 := by
  decide +kernel

private def quarter087_1 : Vector UInt64 25 :=
  #v[0xc787eea6c91a3a75, 0xd4b9f30225f9c18a, 0x185ba309100e1c0f, 0x9394a87923fbe0d1, 0xd61219f324e47151, 0x42746114f4604487, 0x3e429f1a837623c4, 0x25a069d9c4f407ac, 0x3ef1ab1a80e505f0, 0x6b105e974279e574, 0x909b847ca872517e, 0x8566667bd73404c9, 0xf6858fc1e525d80a, 0x3d68a2425bae8aa6, 0x22e7415baac0aa9c, 0x9df4dbaa4c7dce79, 0x7e004d3562621d5e, 0xb435eb785da603f6, 0xaf059c6e9240fffb, 0xe2abebc1cf4c7403, 0xacc980ce44efd1c, 0x16587eae4540cd10, 0xe302e736ac3ada53, 0xf6ca33ba12fa7b36, 0x34f17a6ac36a3186]

private theorem rounds087_0 : sixRounds 0 (by decide) absorbed087 = quarter087_1 := by
  decide +kernel

private def quarter087_2 : Vector UInt64 25 :=
  #v[0xfcdbc3f901011d79, 0xa2dabbde32bd1663, 0x9907041cb400490e, 0xa6393d13fad454f3, 0x5b6701e685a0452f, 0x1df776b4a44e38b1, 0xe1d114d4ed1b979e, 0xf46f6e9575e478cc, 0xd9accd8b60f7c3f0, 0xa5c22b001c85b31e, 0x627aed409d29819b, 0x87044ea0b19138b5, 0x368b5f0af04d1ba5, 0xf5dd7ee48320db40, 0x51769d6b1a199805, 0x82bde71a76d12291, 0xa5e0996dd9479fee, 0x42f19d5f67f21230, 0x5c41532195ab6338, 0x373b45e7da4bf77a, 0xe450d2d6802039c8, 0xfa34814eda821c55, 0x6b8b8b9506dbd136, 0x826fd6ba38a3b0a6, 0x737ca928ceba000]

private theorem rounds087_1 : sixRounds 6 (by decide) quarter087_1 = quarter087_2 := by
  decide +kernel

private def quarter087_3 : Vector UInt64 25 :=
  #v[0x3553cc90c1626d84, 0x5279e3801c44bfa7, 0xf2ca85d161dc8533, 0xdf658170345c5630, 0xffb7e79bb3d163b9, 0xa47cccb4e8276287, 0xd1af2dd38d5d3cd7, 0x158ea0d9b74d121, 0x8f817c17daaacc47, 0xe3241179e6321d6d, 0x8d788af7c598a19f, 0xd160f3a478074f06, 0x8301b5bb6573c1f0, 0xe57d4c99af47241e, 0xd97fac8673cb6115, 0x9786314717b77a53, 0x8b0b981a62983320, 0xdd8f4a5e1e73cf88, 0x9d60c9ae88fb2252, 0x43a0e0f14253b80c, 0xbb4916d7f4017ee1, 0xe5596629b0629134, 0xab06e8868e907fa9, 0xf25c8b7a3d8258af, 0x304f375df6b1cce2]

private theorem rounds087_2 : sixRounds 12 (by decide) quarter087_2 = quarter087_3 := by
  decide +kernel

private theorem rounds087_3 : sixRounds 18 (by decide) quarter087_3 = state088 := by
  decide +kernel

private theorem perm087 : KECCAK.f1600 absorbed087 = state088 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds087_0, rounds087_1, rounds087_2, rounds087_3]
  rfl

theorem block087 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes087 ++ tail) state087 =
      KECCAK.Bytes.run 0 tail state088 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes087 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb087 ws)) := by
    rfl
  exact (step state087).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words087).trans perm087))

private def absorb088 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x16 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x91 0x90 0x91 0x16 0x81 0x83 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x55 0x90 0x82 0x91 0x17)) 6 (by decide) (UInt64.ofBytes 0xa9 0xdf 0x66 0xdb 0x7f 0x90 0x16 0x91)) 7 (by decide) (UInt64.ofBytes 0xc7 0xaa 0xe9 0x6f 0x22 0xf5 0xb8 0xc6)) 8 (by decide) (UInt64.ofBytes 0xc3 0x4a 0xe9 0x8e 0xae 0x97 0x18 0xe5)) 9 (by decide) (UInt64.ofBytes 0x25 0xb 0x90 0xc9 0xb6 0xb 0xc7 0x1d)) 10 (by decide) (UInt64.ofBytes 0x90 0x0 0x60 0x90 0xe6 0x7 0xb7 0x74)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x5b 0x56 0x50 0xa2)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x90 0x0 0x60 0x16 0xff)) 15 (by decide) (UInt64.ofBytes 0x20 0x90 0x40 0x60 0x52 0x20 0x60 0xc)) 16 (by decide) (UInt64.ofBytes 0x60 0x5b 0x56 0x90 0x16 0xff 0x60 0x54))

private def absorbed088 : Vector UInt64 25 :=
  #v[0x8b21b7c0e4b90950, 0x9bb2b63e8211ba91, 0x1a14793095770c0f, 0x320b38f422d310a5, 0x7afb0c57f35e1d90, 0xd0c83d0a409f6ba3, 0x351a3ff80c005b7, 0x89fc870e96c1a145, 0xeca68168dc98a351, 0x9058d95484a91d05, 0xa783eb4d08b8bc89, 0x23fba35ffe9a4d6b, 0xf805f6586b2889f5, 0xe50b98d0888ac005, 0xd024d6230d76d82d, 0x5ef6695d15c7d8db, 0xc9c98a0f86d4874e, 0x4e86b1aa96809dc0, 0x77f32c626a7f72e0, 0x897dd262d52b8fdf, 0x86b104ae4816c271, 0x5fffde25805d31f, 0x7e0d99961f29673c, 0x9611c7f049c46307, 0xbb1303e5df8bae16]

private theorem words088 : absorb088 state088 = absorbed088 := by
  decide +kernel

private def quarter088_1 : Vector UInt64 25 :=
  #v[0x8c04a7cfae33eeec, 0x41417fad164b08e5, 0xa6ba4bcd08373f7, 0x580fbc36b03b5870, 0x43d7c9d06f13382f, 0xfe05399d5ff94eff, 0x5b03958ccd9438d5, 0x2343ea209c49a29f, 0xde4bb831d4c40cb2, 0x65c7036e613209ca, 0xf85f4c1ecda9850b, 0x2f593764f1cb0d3a, 0x70c7f571fb3e5553, 0xe9ed8b3e9c8831db, 0xb5962dbc6a288946, 0x2eec86c36b7a634, 0x9a0fb9e38983ba1c, 0xda8d795ce1db9f61, 0x19985ce3c3f3bac9, 0x77763952d529efd4, 0x16fd6be62a3f2642, 0x5f360073bc099099, 0xfb26b4747e3f8e9a, 0x16e9a778379af622, 0x2d526d00763f7834]

private theorem rounds088_0 : sixRounds 0 (by decide) absorbed088 = quarter088_1 := by
  decide +kernel

private def quarter088_2 : Vector UInt64 25 :=
  #v[0x79cd463b6688979a, 0xa9b6f406623cbdb3, 0x9232b9c9ae2b4fde, 0x498fdac5e5c4b6d6, 0x55d52e93f0a59dc9, 0xbf321d062ce9b537, 0x8a99601fe04c905c, 0x61474dbb88a83c0b, 0xcecbc2cc895f6683, 0xd5ffdf36bac7b481, 0xe647f37191c6eb2f, 0x19f17a09f7044dec, 0x2df1e2d31e3b342e, 0xc3cfb57ce792c064, 0x869c676baca42182, 0xdc5e4dd997afb18f, 0x90d979d29534a3ac, 0x48223157f21e14de, 0x1cf354f471519bbc, 0xeeae7d2d9c33dd1e, 0x9442125c09438c3a, 0xa9d47ad2a70f3571, 0xdb3adc6d7718b129, 0xa084102eeae01657, 0xd8ea6936641ebbc1]

private theorem rounds088_1 : sixRounds 6 (by decide) quarter088_1 = quarter088_2 := by
  decide +kernel

private def quarter088_3 : Vector UInt64 25 :=
  #v[0xb4efb1d82109365, 0x2c665e59d66a9710, 0xd91f418ca21ccca9, 0x39132a137d65cf42, 0x92294ba16229bfa6, 0xeb9572b3ff9cfa16, 0xa23fb736d5e7dce9, 0xd9948e9e1c67c18b, 0xda02ef494a0b0575, 0x65ff8f722f9163fc, 0x75dec07b0b8e148, 0xf2c83b6c80dd9449, 0x64efd5e8ceceb91d, 0x78a868e6bc67aa8f, 0x4fd9718bb72b8338, 0x4bf5d704fff9e67e, 0x1520728a795dd21c, 0xfca50349ce45bc8, 0x944acb7760b3fd74, 0x597b23cd802bf806, 0x5fa1d2b463c5d984, 0x1ed15766a26938d9, 0xb8d21a9636244676, 0x606874ecbe4c61a0, 0x8840c360433de36b]

private theorem rounds088_2 : sixRounds 12 (by decide) quarter088_2 = quarter088_3 := by
  decide +kernel

private theorem rounds088_3 : sixRounds 18 (by decide) quarter088_3 = state089 := by
  decide +kernel

private theorem perm088 : KECCAK.f1600 absorbed088 = state089 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds088_0, rounds088_1, rounds088_2, rounds088_3]
  rfl

theorem block088 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes088 ++ tail) state088 =
      KECCAK.Bytes.run 0 tail state089 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes088 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb088 ws)) := by
    rfl
  exact (step state088).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words088).trans perm088))

private def absorb089 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x54 0x0)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x40 0x60 0x57 0x52 0x2f 0x61 0x14 0x33)) 4 (by decide) (UInt64.ofBytes 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x80)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x60 0x20 0x60 0x52 0x81 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x24 0x60 0x52 0x90 0x81 0x1 0x82 0x4)) 10 (by decide) (UInt64.ofBytes 0x61 0x6e 0x77 0x4f 0x7f 0x52 0x1 0x82)) 11 (by decide) (UInt64.ofBytes 0x6c 0x61 0x63 0x20 0x3a 0x65 0x6c 0x62)) 12 (by decide) (UInt64.ofBytes 0x6e 0x20 0x73 0x69 0x20 0x72 0x65 0x6c)) 13 (by decide) (UInt64.ofBytes 0x6f 0x20 0x65 0x68 0x74 0x20 0x74 0x6f)) 14 (by decide) (UInt64.ofBytes 0x1 0x82 0x44 0x60 0x72 0x65 0x6e 0x77)) 15 (by decide) (UInt64.ofBytes 0x60 0x3 0x90 0x81 0x90 0x51 0x90 0x52)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x5b 0xfd 0x90 0x1 0x64))

private def absorbed089 : Vector UInt64 25 :=
  #v[0x870ca0ff46c0f9fa, 0x73ed3011227885d6, 0x5c507807b0c438d6, 0xa081cb5b68faf9fb, 0x584e3158e3cb2860, 0x20cd9b6f7abff66f, 0x8699535c0409882c, 0x31177ecd60314b5e, 0xabd892bf4d18e547, 0x2d5cf76e52931c24, 0x8a334c8c52681f61, 0xba8178b9a506cd9f, 0x7d2fe322c23dbd06, 0x5632ae220507fa75, 0x428510b891c8d286, 0xfc1889f8fa21fa3c, 0x1de8ce75bf705da, 0x50942d91eb1bf5ff, 0x8af15023885dcb72, 0x35336650df935cd0, 0xc21509254df9a708, 0xc5154a06c82645dd, 0xa3a9567be172a17, 0x763a9578af475a71, 0x4fb0df7fb055b753]

private theorem words089 : absorb089 state089 = absorbed089 := by
  decide +kernel

private def quarter089_1 : Vector UInt64 25 :=
  #v[0xc6d5f5ef077db94f, 0xd88141f65aa29dbe, 0x963a3c4e1f2940bf, 0xcc865364597537ff, 0x4356f0df9ff57718, 0x3558baebcbc2f393, 0x178810336b0488c0, 0x1ff320bd52949c35, 0x5f56192c6ba666fc, 0x7a80b3b1fb6a92d8, 0x5d8de7929b6443c9, 0xb5c2c35a3ebc4dda, 0xe355fd488dafaec6, 0x52ce9a135fb109a8, 0xfe0ab3b8f120d557, 0x6622ff00a7a8c8ff, 0x4bf635745026fbbb, 0xa6914eb5b7044402, 0x119d937718a7413a, 0xa6ba5679e50d8ced, 0xb2e12b2b6e8ebeed, 0xc2074f3dce88d4e3, 0x23b5106a55b6fdfb, 0xdf4825b6237d7882, 0xf488b5e985491bb7]

private theorem rounds089_0 : sixRounds 0 (by decide) absorbed089 = quarter089_1 := by
  decide +kernel

private def quarter089_2 : Vector UInt64 25 :=
  #v[0xc752bbe85d5a473b, 0xae8baa03f59b9ac, 0x7408eb7fd3b1ac79, 0x2da3f5891238ca8d, 0x9fd57eebfe41c65b, 0xc22f40296456d6d9, 0xee50a4f933a5ce1e, 0xa81f6aae762577b2, 0x811b5db6a55e194, 0xd8ab4f0c33da437d, 0x57d51d8df313b646, 0xd6d4995f6bdfca5a, 0x4fe93544eff81a2c, 0xdfebb506f5f6ea75, 0xbf3de37523214798, 0xc037266fcac4552f, 0x59e7acacf97b695a, 0x608cfce8fa5d31bb, 0xe106d7cfa8453675, 0x7b32185d991c695d, 0xaae1d2c49924b979, 0x26f9c3aa59268a74, 0x621178c809a3fe27, 0x781331c99a46654d, 0x2612dad65af6b259]

private theorem rounds089_1 : sixRounds 6 (by decide) quarter089_1 = quarter089_2 := by
  decide +kernel

private def quarter089_3 : Vector UInt64 25 :=
  #v[0x26e4de5102d95c26, 0x7e8346d9cb16e74b, 0x1de84324e7f4c771, 0x4e0c5e779bee85de, 0x629046f37200a56d, 0x9e1476d0a08ec8, 0x8cf61dddfd9bb3e2, 0xbe2ac2674afb6d23, 0x57ac15a82ac36029, 0x7cf297bb8437ab34, 0x5a08b8395eb61d30, 0xc66afe520285e5d4, 0xe31da761b4f64247, 0x29e9cb86425021e3, 0x1d7adc591098963a, 0xe8854399df5e684a, 0xfbcf1548e9c4a8f1, 0xa27a103189d7d1d9, 0x74ef291421dd583c, 0xdfeef8ce5ee45613, 0x79fbca2494801d91, 0x13e56029b1e6b957, 0x4fcaa79dcc474aa2, 0xba721044c3c6c148, 0xcd4ba78217c5d94a]

private theorem rounds089_2 : sixRounds 12 (by decide) quarter089_2 = quarter089_3 := by
  decide +kernel

private theorem rounds089_3 : sixRounds 18 (by decide) quarter089_3 = state090 := by
  decide +kernel

private theorem perm089 : KECCAK.f1600 absorbed089 = state090 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds089_0, rounds089_1, rounds089_2, rounds089_3]
  rfl

theorem block089 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes089 ++ tail) state089 =
      KECCAK.Bytes.run 0 tail state090 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes089 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb089 ws)) := by
    rfl
  exact (step state089).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words089).trans perm089))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
