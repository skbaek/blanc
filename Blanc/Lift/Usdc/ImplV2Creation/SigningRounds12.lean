import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb072 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x4e 0x60 0x9f 0x76 0x60 0xe8 0x90 0x6b)) 1 (by decide) (UInt64.ofBytes 0x53 0xce 0xce 0x20 0x77 0xe6 0xc0 0x89)) 2 (by decide) (UInt64.ofBytes 0x91 0x90 0x3 0x90 0x81 0x92 0x20 0xd)) 3 (by decide) (UInt64.ofBytes 0x91 0x92 0x1 0x60 0x50 0xa2 0x90 0x1)) 4 (by decide) (UInt64.ofBytes 0x73 0x54 0x0 0x60 0x5b 0x56 0x50 0x50)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x61 0x14 0x33 0x16 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x7f 0x51 0x80 0x40 0x60 0x57 0x6f 0x26)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x1 0x82 0x4 0x60 0x20 0x60 0x52 0x81)) 14 (by decide) (UInt64.ofBytes 0x52 0x1 0x82 0x24 0x60 0x52 0x90 0x81)) 15 (by decide) (UInt64.ofBytes 0x65 0x6c 0x62 0x61 0x6e 0x77 0x4f 0x7f)) 16 (by decide) (UInt64.ofBytes 0x72 0x65 0x6c 0x6c 0x61 0x63 0x20 0x3a))

private def absorbed072 : Vector UInt64 25 :=
  #v[0x8fed0e1a6502be48, 0xd0957aeb59f4f3a2, 0xb333cf07eee008a5, 0x647c8b7a356538b4, 0xddafc453de01ebd5, 0xb7c8b6f45d104f28, 0xc0a888977076891d, 0x777a68e4c7c009dd, 0xc6859eb4d2720c19, 0xa13ad55d986dbdb7, 0x7e5ad0f334ff18d9, 0x246c20b086b15a1f, 0xbe7d78f5a2e0900b, 0xad1f733a4fd8010e, 0xa8f1e8288b59c23f, 0xf51f13e29d7a4f, 0xdc22f47493267ef4, 0x61935dad4e62c382, 0x81efd8955b42f7b7, 0xbdb7dfca806973a3, 0x86c6004a94d0387c, 0xb4b510e66257ff6a, 0x334c2021c5f3fea0, 0xbe06611622d06c2e, 0x324ce913943396d6]

private theorem words072 : absorb072 state072 = absorbed072 := by
  decide +kernel

private def quarter072_1 : Vector UInt64 25 :=
  #v[0xf7de5f1716bfe732, 0x568eef91c3e954c2, 0xb463bb3cf25c08e1, 0x3fc89e49e29a411b, 0xaaca656296f3b93a, 0x6190406c65c5db05, 0x3bb3fb2ea53ed6f3, 0xd7a4465f7e558fe1, 0xf800b2f27afde19f, 0x13bd42ba109b9b6f, 0x3c7a0a2859eccd00, 0xdcf64b88d1323b90, 0x254952b52a879b5b, 0xfc2ac93e4210cebe, 0x53172ded27f73649, 0x1f4c1dbc53c20222, 0xd0e34096ca8149ec, 0x568e96d898b34767, 0x193835d6804b2df5, 0xf137add3912b4ab, 0xc6e3cdafa0d80ef9, 0x31025bfef1bb339a, 0xc1c5d03eda94f02c, 0xbc3e33142859129b, 0x303c7347ce028833]

private theorem rounds072_0 : sixRounds 0 (by decide) absorbed072 = quarter072_1 := by
  decide +kernel

private def quarter072_2 : Vector UInt64 25 :=
  #v[0xf75fbb7d5e6df2ed, 0x3185b3aa3ad23a6f, 0xc622a97d98768597, 0xf1e6bc6d93c6a34, 0x10b7f5ec7825607f, 0x4a6b9f9ec604038f, 0x234cf24c1f499d3b, 0x2be768c9b4c1d12e, 0x9f85c029fb2df3a6, 0xe1f92a87b0af458a, 0xdd26cb3164b2d8c0, 0xd64cde805da8cae2, 0x423415763bc8e13e, 0x71e22d3685bed726, 0xb5dd2bb7b901204, 0xd299f8f0d69fb94, 0x7801f4c62b996c67, 0x937db9d84de65d98, 0xc72b6d81f8c74a56, 0xf471f12f2f8b101e, 0x78b19c10c01ac184, 0x565fbad224e812fb, 0x10aa0bbaf3178fb6, 0x49f8ad03219159f7, 0xfb800386adcd1092]

private theorem rounds072_1 : sixRounds 6 (by decide) quarter072_1 = quarter072_2 := by
  decide +kernel

private def quarter072_3 : Vector UInt64 25 :=
  #v[0x87d3697bedccc2ce, 0x1b013dac48adf9a3, 0x9ea74e194d00e165, 0x361c6c72d1efce83, 0xda4c9b25bfdf0c19, 0xfa6126107cb04fbd, 0x3089972d9bc66df1, 0xbd80ed930975d1c9, 0x6fc09fc1263d6669, 0x4d540e808ebfa139, 0xe06338d74de29adf, 0xde7395120a40cb75, 0x84281b0a48abd97b, 0x80c112040b58f2c8, 0x9cfa782b3fbfe43e, 0x546f5d653ab70ed0, 0x3a3467f4d21285ce, 0x81824fdc458b93fe, 0xd6ac18bcce2f0b1e, 0x6351230b935f668e, 0x55437d5b36c4df08, 0x7508677af304b152, 0x5d0c6c487536a340, 0xa8f95b321bb30791, 0x4f0e592d5c05f136]

private theorem rounds072_2 : sixRounds 12 (by decide) quarter072_2 = quarter072_3 := by
  decide +kernel

private theorem rounds072_3 : sixRounds 18 (by decide) quarter072_3 = state073 := by
  decide +kernel

private theorem perm072 : KECCAK.f1600 absorbed072 = state073 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds072_0, rounds072_1, rounds072_2, rounds072_3]
  rfl

theorem block072 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes072 ++ tail) state072 =
      KECCAK.Bytes.run 0 tail state073 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes072 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb072 ws)) := by
    rfl
  exact (step state072).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words072).trans perm072))

private def absorb073 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x20 0x74 0x6f 0x6e 0x20 0x73 0x69 0x20)) 1 (by decide) (UInt64.ofBytes 0x65 0x6e 0x77 0x6f 0x20 0x65 0x68 0x74)) 2 (by decide) (UInt64.ofBytes 0x51 0x90 0x52 0x1 0x82 0x44 0x60 0x72)) 3 (by decide) (UInt64.ofBytes 0x90 0x1 0x64 0x60 0x3 0x90 0x81 0x90)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x5b 0xfd)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x81 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x57 0xdb 0x26 0x61 0x16)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8 0x7f)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x80 0x80 0x1 0x4 0x60 0x52 0x81 0x0)) 13 (by decide) (UInt64.ofBytes 0x52 0x82 0x3 0x81 0x82 0x1 0x20 0x60)) 14 (by decide) (UInt64.ofBytes 0x80 0x1 0x20 0x60 0x52 0x81 0x28 0x60)) 15 (by decide) (UInt64.ofBytes 0x60 0x39 0x91 0x28 0x60 0xa 0x55 0x61)) 16 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x50 0x50 0x91 0x1 0x40))

private def absorbed073 : Vector UInt64 25 :=
  #v[0x87414dff7eb8a3ff, 0x76f382291897be4b, 0xcff35416bd8dcfcd, 0x349a043706a33f5c, 0x9886a77e7d8cdc5f, 0xd9ad3fac995683b1, 0xdd3718f98ef1f11d, 0x64d1e93eeb2c9072, 0x100b17a74b8ed54b, 0x498102a5eeacac7a, 0x355abee31122ef0c, 0xe38c477820ce6d1, 0xd99850c5e4efd0b4, 0xc4c8f4a6383d3cda, 0xc571d9e76be416dc, 0xacd9683a7d6d3559, 0x39b85ffe658de59, 0xd75172b7ad574816, 0x2ce4ecb333b19aec, 0xf4681784553b01f, 0xb46918bbb5ae8422, 0x322a9dff21637e7e, 0x6c34029446110a35, 0xa5130fd5734c9dfa, 0x298e8fd50ff6cb3a]

private theorem words073 : absorb073 state073 = absorbed073 := by
  decide +kernel

private def quarter073_1 : Vector UInt64 25 :=
  #v[0x3abb62eed716a49a, 0x8c54740beeeb8375, 0x1bd91e83ffb0d331, 0x87277c9e03c2b262, 0xe6ca266cd8770b93, 0x979dda81e0bf61a6, 0xe46f7649be6e9cee, 0x77e14272b179ca6e, 0xa67961bd56fa318a, 0xaaa9a81ff161508e, 0xff5b2547eaeebfd3, 0x7387b3fe9f61f7a1, 0x66ea2532fd27af7, 0xb7bb912164573c89, 0xd209c929a2089834, 0x14c7350ada0756c9, 0x964bb5f0f40c9d8d, 0x4a953892af5cb250, 0xca701c002bbbe973, 0x8f31eb69768134c8, 0x9a7e4eea6c84c154, 0x45ad303eda7d1af3, 0xa8f3ce636a41a2ac, 0x652a5d70c8df8c50, 0xcdad822e7ced0b32]

private theorem rounds073_0 : sixRounds 0 (by decide) absorbed073 = quarter073_1 := by
  decide +kernel

private def quarter073_2 : Vector UInt64 25 :=
  #v[0xc498929346a0d9cf, 0xb61ecf513eda70ed, 0xe9fa44202c535877, 0xfdb80c27a04dc64c, 0xf4772157772aa2e2, 0x2c60689e588027c, 0x6c86905c94e2ccc2, 0xaf1943effef245e7, 0xfedf4d81f9e34922, 0xa7894f6a5eb5dcdc, 0xf971e6e335c2767b, 0x20aa1826da19dec3, 0xa39c0c4f93c882c0, 0x7cf9174ebc3f1259, 0xc22929eff967a085, 0x354da5dd05a8d12, 0x55b285e1b3e305ab, 0x877c5fa58af05ea9, 0x1f7dba717e3afdea, 0x658b32672371c7e8, 0x10fc1715cdbd7084, 0xf18f13de87f604a0, 0x19dc29b18f9df2f6, 0x38b2df62548718bd, 0xd545326a6f56e220]

private theorem rounds073_1 : sixRounds 6 (by decide) quarter073_1 = quarter073_2 := by
  decide +kernel

private def quarter073_3 : Vector UInt64 25 :=
  #v[0xea02f2e109d71448, 0xc6cf41809c7429cd, 0xdaa2934ea73f0f48, 0x6ce874690b66e207, 0x84547c5535309cb9, 0xecb1894d664bda98, 0x190a845d6ec7beed, 0xad005266cc5314d9, 0xdb71dffc647d4c46, 0xcc40e9df693d48eb, 0x399cf402cd17a5c0, 0xa54bbdc22d59c247, 0xba21a5600174f664, 0x57542d30a3e44ecb, 0xff80e79843b23481, 0xfc9d50a02eef2f62, 0x6ac6ea72a96da06c, 0xa1a8ff385622524f, 0x4d2418860d2945be, 0x8ce1c56e337d57e2, 0xa282b35b31ad7572, 0xa71f267646932c0d, 0xeaf49bc29cd19b38, 0x1706c2b113097a9, 0xb7c5f33ef4486fc0]

private theorem rounds073_2 : sixRounds 12 (by decide) quarter073_2 = quarter073_3 := by
  decide +kernel

private theorem rounds073_3 : sixRounds 18 (by decide) quarter073_3 = state074 := by
  decide +kernel

private theorem perm073 : KECCAK.f1600 absorbed073 = state074 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds073_0, rounds073_1, rounds073_2, rounds073_3]
  rfl

theorem block073 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes073 ++ tail) state073 =
      KECCAK.Bytes.run 0 tail state074 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes073 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb073 ws)) := by
    rfl
  exact (step state073).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words073).trans perm073))

private def absorb074 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x1 0x60 0x5b 0xfd 0x90 0x3 0x91 0x80)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x7f 0x54 0x80)) 2 (by decide) (UInt64.ofBytes 0x0 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x16 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x17 0x91 0x90 0x91 0x16 0x81 0x83 0xff)) 9 (by decide) (UInt64.ofBytes 0x91 0x51 0x40 0x60 0x55 0x90 0x82 0x91)) 10 (by decide) (UInt64.ofBytes 0x93 0xa2 0x82 0x4 0xb8 0x7f 0x90 0x16)) 11 (by decide) (UInt64.ofBytes 0xc9 0x83 0x86 0xda 0x3e 0x1 0x2e 0xca)) 12 (by decide) (UInt64.ofBytes 0xea 0xae 0xfd 0x7c 0x34 0xc8 0x7f 0xbd)) 13 (by decide) (UInt64.ofBytes 0x2 0xf5 0x6d 0xa4 0xcb 0x58 0xde 0x5e)) 14 (by decide) (UInt64.ofBytes 0xa2 0x90 0x0 0x60 0x90 0x4 0xa6 0xc2)) 15 (by decide) (UInt64.ofBytes 0x1 0x74 0x54 0x1 0x60 0x5b 0x56 0x50)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0))

private def absorbed074 : Vector UInt64 25 :=
  #v[0x280d054c4390a3bd, 0x1d0fd1414d71087b, 0xc351f01c25e0afb7, 0x6ca74134c1646bc7, 0xc8a9ed88500aa7fd, 0x3fbb9149e74ac884, 0x8e61bf8c295bca1c, 0xcd418613b25cdeb1, 0x854cc7616a01d661, 0x807e1961035cc1cc, 0xded7ff2caa637e66, 0xd0444bd940a2079d, 0x7ccba17d86a6de99, 0x3e99e29e396adb8, 0x2274cbb5a4576611, 0xc43d15190d048189, 0x3ffe025a84b90d87, 0xfa8412b39f479688, 0x4cf2c37cdbeabca1, 0x1489166b0e8633dd, 0xdaa60b2085109221, 0xe598774b52be784d, 0x7b8d54d5255f61ff, 0x1130cafaad5990b8, 0x47a5fe47194e59c1]

private theorem words074 : absorb074 state074 = absorbed074 := by
  decide +kernel

private def quarter074_1 : Vector UInt64 25 :=
  #v[0xb73c926f7242d8d, 0x677a46cc2734beb9, 0x554bd556d4a77bd1, 0x3d214a8aeac85180, 0xd8d9a803acfe6553, 0x525f832796a4a24f, 0xdd376580e79ddbaf, 0x383a328dad7412ab, 0xad48841781fc099, 0x97cb0a061b177c37, 0x39be7ab40c2e3b5a, 0x8d947b983950de0f, 0xbe8eae575ade0db0, 0x88937987473ac54a, 0xa988a2435e3c8fc8, 0xc2d56b8b606070ae, 0x622ead5e1c94e580, 0xdccf49b9f1d2edc, 0xdfff1c8671af8a16, 0xe6b5a6b4c11f1470, 0x5373782b8dc1911c, 0xf8175daf1fff9c55, 0x923e08dbadd1e0d, 0x69b4849a83551555, 0x26e4dd2eb4bd4b98]

private theorem rounds074_0 : sixRounds 0 (by decide) absorbed074 = quarter074_1 := by
  decide +kernel

private def quarter074_2 : Vector UInt64 25 :=
  #v[0xf3dc5759898c786, 0x52e4f1423f3a8333, 0xedd83d11857e9c8b, 0x9d682da818d9e0de, 0x6cf3cb35898c51cf, 0x7bd0ab5f7b654187, 0xad55380936cc2998, 0x5b921d3e4783ac35, 0xcfef561ce1a63cf2, 0xf7216b3900feffe1, 0x2dc53c638b8b250c, 0xcd0ed8903cf23e84, 0x41967c3754fa9389, 0x1b3d57ad78e7f394, 0xf40dcf101cf281b7, 0xe120738c2c8162b0, 0x4d2cea2768256126, 0xeb735e26100fe113, 0xc48b42a0640f1b9a, 0xbd5e11bd5a4bf40, 0xf2e359b00a7cd9b8, 0xfe8f15004e0a2e92, 0xd654df0bc41115c5, 0x3b6ffc3ad3730f00, 0x51c0a73c68fa07d9]

private theorem rounds074_1 : sixRounds 6 (by decide) quarter074_1 = quarter074_2 := by
  decide +kernel

private def quarter074_3 : Vector UInt64 25 :=
  #v[0xd4c4c69620accb83, 0xeaa3825de322b1a8, 0x4c7bfcb58cfae17e, 0x836563d65aff538e, 0x4caa883557a807cb, 0x7c7f81f917a76748, 0x42d83a6416b21a72, 0xf2c3d223743bf0db, 0xf2f4985f57d07441, 0x78d48d766c471f0b, 0xe246712d64482cc0, 0xa1d22e0db888e8a0, 0x4e9eb0955a198b0c, 0xeda6d911cdb312f, 0xe027211d4f7edd88, 0xe86602e74778985a, 0x22392ba821b7adb0, 0x2dad3d1e05e6fad4, 0x2c311592ea902751, 0xc35cde7694dd2d8c, 0xc709f1b38b71af78, 0xee9a4665370997a2, 0xffb3c494d2599444, 0xd5c14ea579362469, 0xb5dafeb95d262354]

private theorem rounds074_2 : sixRounds 12 (by decide) quarter074_2 = quarter074_3 := by
  decide +kernel

private theorem rounds074_3 : sixRounds 18 (by decide) quarter074_3 = state075 := by
  decide +kernel

private theorem perm074 : KECCAK.f1600 absorbed074 = state075 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds074_0, rounds074_1, rounds074_2, rounds074_3]
  rfl

theorem block074 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes074 ++ tail) state074 =
      KECCAK.Bytes.run 0 tail state075 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes074 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb074 ws)) := by
    rfl
  exact (step state074).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words074).trans perm074))

private def absorb075 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0xff 0x60 0x4 0x90 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x40 0x60 0x57 0xda 0x27 0x61 0x15 0x16)) 3 (by decide) (UInt64.ofBytes 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x80)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x60 0x20 0x60 0x52 0x81 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x24 0x60 0x10 0x60 0x52 0x1 0x82 0x4)) 9 (by decide) (UInt64.ofBytes 0x73 0x75 0x61 0x50 0x7f 0x52 0x1 0x82)) 10 (by decide) (UInt64.ofBytes 0x61 0x70 0x20 0x3a 0x65 0x6c 0x62 0x61)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x64 0x65 0x73 0x75)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x1 0x82 0x44 0x60 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x60 0x3 0x90 0x81 0x90 0x51 0x90 0x52)) 15 (by decide) (UInt64.ofBytes 0xe7 0x27 0x61 0x5b 0xfd 0x90 0x1 0x64)) 16 (by decide) (UInt64.ofBytes 0x71 0x42 0x61 0x85 0x85 0x85 0x85 0x85))

private def absorbed075 : Vector UInt64 25 :=
  #v[0xf1ccb1945f0a924b, 0x1025ef10e0e980e5, 0x656881ff336fe5cd, 0xfcb5dab73d80d37d, 0xac77d4001ac14a58, 0x41199919d1587b72, 0xb6740c1a785bb2f2, 0x3d16aea6b9cb59a2, 0x236f8b442c194cca, 0x540cc813cf5b729c, 0x63e03d5b7157a032, 0xf9639cca364c793f, 0x659f3a7685a05b32, 0x8ac4302e1f0297ba, 0xaa8620f593f7239c, 0xebfbc654f20edb22, 0x727b39f81c2ccbe4, 0x5b6a9412efb97681, 0xa61858e401bf2681, 0x6dd09a53137db9d7, 0xa93d0a58d61b42fb, 0xcaacdf082b24f9f6, 0x48da40d06352d678, 0x3cfc8e67dc5c2a5e, 0x8e6f550b5cb6ba99]

private theorem words075 : absorb075 state075 = absorbed075 := by
  decide +kernel

private def quarter075_1 : Vector UInt64 25 :=
  #v[0xc4b33cb4a553ac99, 0x4dedb4fa8be42588, 0x918f141b636460d3, 0x6657868ad7f8788b, 0x91b1dabbdfb43e1d, 0x1f2481b37e32c23e, 0xd84566fe6d4e80c3, 0x565367c3c8aa9be1, 0x2b5cf76e2854024, 0x2da0704979a8c3a8, 0x5f8514291fb4cdf4, 0x841556313e51bb00, 0xef366159d032f929, 0x585b85d5bb3839e5, 0x4e9dba11411d5edd, 0x8a6c719113b024f0, 0x2625077a77af6bdf, 0x2ea699ede6f23655, 0x688ae22f8112c299, 0xa0c920a30672fda4, 0xfd2b9ef343bc1bf6, 0xef24bd583a6c7564, 0x74bb539cf1c34224, 0x7cb6e55bc631e90a, 0xb185c1d0a1a978db]

private theorem rounds075_0 : sixRounds 0 (by decide) absorbed075 = quarter075_1 := by
  decide +kernel

private def quarter075_2 : Vector UInt64 25 :=
  #v[0xe4fb9019ab779792, 0x420d15fd9efd8df, 0x1e0ccc8e5a533853, 0xe9580227bd8f19b0, 0x903086b323c6b34f, 0x976c19ea35669f06, 0x818ffe2f125cf586, 0xedc5e1229ee36c60, 0xed853d4a9c8e5a7b, 0xa0d930fc45f4c56, 0x8cc6c2dcabd20171, 0x398080364931d3bb, 0x23b3370ff8c76cc7, 0xc9e66bb68c0cc1e, 0x369e0fa0c0c81f70, 0xa01ac20e71b7f9dd, 0x2dfb85be209d53e, 0x6e713c8394049fc7, 0x442ad4081032ae4b, 0x2612d1bb1684fe53, 0x992f6080b71d0781, 0x472f788c8637b7e6, 0x5003fe2a994aa8df, 0x8440f79a370e7c3d, 0x3bd939a79f363ba0]

private theorem rounds075_1 : sixRounds 6 (by decide) quarter075_1 = quarter075_2 := by
  decide +kernel

private def quarter075_3 : Vector UInt64 25 :=
  #v[0x1fdea4faf29048f2, 0xe6983102680c3b6b, 0x18ad6fc8ab2f7311, 0x44c626e498983019, 0x407b2d4ea497839b, 0xdaaffd2da0f61e8c, 0xb1339078f1a8a98, 0xaf108137f1ae6688, 0x89a57de44ad4d400, 0x1c8ae42a581debd, 0xc910431fbf92d281, 0x6eb746c3c099c3a9, 0xe3472ae1486cd638, 0x17e92dd267811b76, 0x30e6a635b1a85fbf, 0x6bc79e5646afe6d9, 0x4dbb66e6dc3c35c0, 0x13b645a4c854be79, 0xc1e0e4763da6da43, 0x5d18dc8af097cfa1, 0x177146c959c8ece2, 0x2b123f6447221a7a, 0x356ea3687635851, 0xf3512813a8178a78, 0x8ba293a63ce597f0]

private theorem rounds075_2 : sixRounds 12 (by decide) quarter075_2 = quarter075_3 := by
  decide +kernel

private theorem rounds075_3 : sixRounds 18 (by decide) quarter075_3 = state076 := by
  decide +kernel

private theorem perm075 : KECCAK.f1600 absorbed075 = state076 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds075_0, rounds075_1, rounds075_2, rounds075_3]
  rfl

theorem block075 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes075 ++ tail) state075 =
      KECCAK.Bytes.run 0 tail state076 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes075 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb075 ws)) := by
    rfl
  exact (step state075).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words075).trans perm075))

private def absorb076 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x56 0x50 0x50 0x50 0x50 0x50 0x5b 0x56)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x1 0x74 0x54 0x1 0x60 0x5b)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x81 0x16 0xff 0x60 0x4 0x90 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x5b 0x56)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x60 0x9 0x60 0x52 0x81 0x90 0x0 0x60)) 9 (by decide) (UInt64.ofBytes 0x90 0x54 0x20 0x90 0x40 0x60 0x52 0x20)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x5b 0x56)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x60 0x11 0x60 0x52 0x81 0x90 0x0 0x60)) 14 (by decide) (UInt64.ofBytes 0x90 0x54 0x20 0x90 0x40 0x60 0x52 0x20)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x54 0x1 0x60 0x5b 0x56)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed076 : Vector UInt64 25 :=
  #v[0xd4b9eac3ddd914a7, 0xac0dd8628b888e69, 0xd69275acfbf89286, 0xfc51b18f808ec428, 0x74c10b033649518, 0xa60d23f57ff39c91, 0xe14624079e93a3e4, 0x3ca37654ac411f8f, 0x8261e134f5386d79, 0x453c73c724fd809e, 0x562927b970979a94, 0x1208c3d8c3481bda, 0x8b8139128ac74543, 0x61fd3bcd214d9b88, 0xc6a16b1facdeb0ac, 0x1360c2e55d51de52, 0x1e71ded637d725c1, 0x3392eb6a58336496, 0x5276a3992951e5a8, 0x5543bf9f2507e6a3, 0x5db1f6c53c68d28a, 0x6b6291591e71b0a3, 0x142b9c99113ab44b, 0xfc07a3c77cff5253, 0xaa0b12a9c9a6e3c5]

private theorem words076 : absorb076 state076 = absorbed076 := by
  decide +kernel

private def quarter076_1 : Vector UInt64 25 :=
  #v[0x110b76d4e97a7f11, 0xde009d1302fa5805, 0xf07339df8b52f1b7, 0x77face71bd366a1e, 0x4049c469d5d4aae7, 0x16e22d58ea891d64, 0xffa45d0afa462d6a, 0x47e0f7761d335528, 0xd74f8d6bc44ffc19, 0x12d0f3b6ae13c5b2, 0xa203a7d518a26804, 0x21d700ad47f8f6e4, 0x250d5a74db6c4faf, 0xf7f058d3d3d36174, 0xd1b660be2251f227, 0x7e3a5e3257f82572, 0x9e988cff5bb5d713, 0xf430dd9d6e70e720, 0xc899cc0754b44d90, 0x40d25b7cfdf8eb6d, 0x23afde2b7f5ca8dc, 0x68ac3db47e669f0e, 0x3a65914879dd0df3, 0xd27ac606a5f6ac10, 0xedd6a91e35f4afa7]

private theorem rounds076_0 : sixRounds 0 (by decide) absorbed076 = quarter076_1 := by
  decide +kernel

private def quarter076_2 : Vector UInt64 25 :=
  #v[0x1c6263f0fd8ccad6, 0x71dd99233a979bba, 0xb0337e00d050b4ee, 0x90f232b6387f9e12, 0x719c87ef83b6654, 0x74907e6be4d38306, 0xd8997116131cd5a9, 0x1602e4bfb3c4d2b5, 0xe82be8037f3ce300, 0x51d04879efa64302, 0xdb968401a6d3d457, 0x5d06d7d974cabae7, 0x51d959dfb201ac84, 0xba7937460043c28f, 0x352b3f083fa65143, 0xfa08ae08ce18c85f, 0x23db398f1264128a, 0x306dff4030ce77aa, 0xc56ecd015b30a1f0, 0xe3124115934bccde, 0x9f07549623b7b9fa, 0xd5582b3f2e9d1bb0, 0xa2c6ca483cde4350, 0x89a2a87ef94de6d5, 0xb29396d9217999f1]

private theorem rounds076_1 : sixRounds 6 (by decide) quarter076_1 = quarter076_2 := by
  decide +kernel

private def quarter076_3 : Vector UInt64 25 :=
  #v[0xcd5ae8016d94a5b9, 0x963ef9d7e16a10ff, 0xe28dc6527c74db89, 0xc1581aadcbf8a3d5, 0x2488c223096fa800, 0x81562be48bd41fd4, 0xf5c6e93abc080896, 0xe15ec2d87ce33521, 0xc405049d0a41c72e, 0xf2522b64ecdb03ee, 0x224a2af38acd7a62, 0x903930c3db8a6009, 0x797c703c0f185abe, 0x8bde07dd33e5030, 0x27ff3f11de1adcf5, 0x5d984a71a15b5c5a, 0xc85d38a039fab255, 0x50370cba5d764412, 0x8b7a153e8cda0786, 0x217cbfde6fae2791, 0xb04c72c096ad8890, 0xd7f6e1ed832d4ab7, 0x907f8ccb1a503ab1, 0xe215876b4585b7db, 0x9b51643a68423af4]

private theorem rounds076_2 : sixRounds 12 (by decide) quarter076_2 = quarter076_3 := by
  decide +kernel

private theorem rounds076_3 : sixRounds 18 (by decide) quarter076_3 = state077 := by
  decide +kernel

private theorem perm076 : KECCAK.f1600 absorbed076 = state077 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds076_0, rounds076_1, rounds076_2, rounds076_3]
  rfl

theorem block076 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes076 ++ tail) state076 =
      KECCAK.Bytes.run 0 tail state077 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes076 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb076 ws)) := by
    rfl
  exact (step state076).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words076).trans perm076))

private def absorb077 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xcf 0x28 0x61 0x14 0x33 0x16 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x79 0xc3 0x8 0x7f 0x51 0x40 0x60 0x57)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0xa0)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x82 0x1 0x20 0x60 0x80 0x80 0x1 0x4)) 8 (by decide) (UInt64.ofBytes 0x52 0x81 0x22 0x60 0x52 0x82 0x3 0x81)) 9 (by decide) (UInt64.ofBytes 0x60 0xcb 0x58 0x61 0x80 0x1 0x20 0x60)) 10 (by decide) (UInt64.ofBytes 0x50 0x91 0x1 0x40 0x60 0x39 0x91 0x22)) 11 (by decide) (UInt64.ofBytes 0x90 0x3 0x91 0x80 0x51 0x40 0x60 0x50)) 12 (by decide) (UInt64.ofBytes 0xff 0x7f 0x54 0x80 0x1 0x60 0x5b 0xfd)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x0 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed077 : Vector UInt64 25 :=
  #v[0xcea284a443c2c8ef, 0xbe29d463d4665b72, 0x1fb5a05318ba670, 0x5759a1e9c0a0d8d0, 0x8cd92a13e95951b1, 0x35cbd069fbdaa447, 0x89ab168ce81c2ddd, 0xaa861f5a745d843d, 0x427a370d6eb62b0a, 0x9cc7bfe2118ae543, 0x904abccedbbdd09f, 0x240c6b6ea4cc0780, 0x8dc2bca6225841db, 0xb0e36e8fdec3f6ab, 0x5ccccf70e2c5d206, 0xa225df163103f66a, 0x9dc0262915e4f191, 0x895ca0db4045fb9a, 0x4a4acab38b5cde14, 0xb57c9e40c2dbd959, 0x8c031915bbdd16c, 0x79548546af7b1c39, 0xf0959fe9a443897e, 0x7f7fac84961a2592, 0xcdfe98a8feb02f94]

private theorem words077 : absorb077 state077 = absorbed077 := by
  decide +kernel

private def quarter077_1 : Vector UInt64 25 :=
  #v[0xf00a94c8529ba828, 0x55a25fc2092d60ac, 0x9aa6963ed3b3c328, 0xe3e523add8db58b8, 0xd338a9c0dabe5253, 0x1168cde82b71e93, 0x439a8e0ea0a71397, 0x571c75d13316369c, 0xbb54aa4017c912c7, 0x159919d17ab93e0b, 0x1f175f5d101cbfbd, 0x2287f0fa275cc5bb, 0x34089d84f2eb8341, 0x25dab7cd803173cc, 0xd7a82adf5e30261, 0x1e4ee78e0e6c4cd8, 0x3f7d5b3a1256d782, 0x8dd6a34902f227c1, 0xac25d4ea0ab720f3, 0x52d741fab096de3f, 0xa80891929986bd7f, 0x8930561f5ab9b350, 0x42c395b558716d16, 0xc632a55440390c34, 0xed91deed777d7907]

private theorem rounds077_0 : sixRounds 0 (by decide) absorbed077 = quarter077_1 := by
  decide +kernel

private def quarter077_2 : Vector UInt64 25 :=
  #v[0x47c14b337c79bac2, 0x87fbe35d7dee7d05, 0xcfcb2c09ed5d96be, 0x4bc85d7632792e87, 0x82b09a94229b94cd, 0x15eb5a42e78601ae, 0xad05864684f82e9d, 0x742fb5a33948cefe, 0x3d8bc0c9f63cc83f, 0xfccb55fe19d21ba0, 0x72c37cf98e1d0c0d, 0x500148287ed0df27, 0xeff8d76ae609d0f7, 0x7d5c6e1d3e4e0433, 0xcc8a75145537ad48, 0x8729b05321cf3597, 0x3fa7260aa091eaca, 0x15d75d279b9188c4, 0xfdbcd7f84757f2d7, 0x5bdb44c714d9122d, 0xdbdd41646a0a6b27, 0xe0a24f9d223b03c3, 0xbef291e523fdf909, 0x3031f90f166f3ef7, 0x27066773119b94b7]

private theorem rounds077_1 : sixRounds 6 (by decide) quarter077_1 = quarter077_2 := by
  decide +kernel

private def quarter077_3 : Vector UInt64 25 :=
  #v[0x65137a240e67ebe8, 0x478289a541e871dd, 0x77052730c920e0de, 0xdad9dcb799b6694c, 0x5b6ec7a25595b68a, 0xbc7d4061080bca88, 0x23a38a0743f4bf62, 0x2f78f4c6d9f44647, 0x8cfbc16a15c08b21, 0xcc0fbb8104b3c807, 0xda56b08e76a02597, 0x880589533c8f245f, 0xf350880949e79cdb, 0xea9e5d274151bcf3, 0xdc7d38893b01a290, 0x1d94f44819f2adfd, 0x3dc7adeaa0996c40, 0x147720d1d0397b89, 0x5799f641553c4dcc, 0x6045a4526de68455, 0x8ab4d1ea3ee83432, 0xc61157c52fec063c, 0x4e8d624c642d9c05, 0x45fd46c49f593089, 0xeef3a9eeb9354b0c]

private theorem rounds077_2 : sixRounds 12 (by decide) quarter077_2 = quarter077_3 := by
  decide +kernel

private theorem rounds077_3 : sixRounds 18 (by decide) quarter077_3 = state078 := by
  decide +kernel

private theorem perm077 : KECCAK.f1600 absorbed077 = state078 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds077_0, rounds077_1, rounds077_2, rounds077_3]
  rfl

theorem block077 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes077 ++ tail) state077 =
      KECCAK.Bytes.run 0 tail state078 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes077 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb077 ws)) := by
    rfl
  exact (step state077).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words077).trans perm077))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
