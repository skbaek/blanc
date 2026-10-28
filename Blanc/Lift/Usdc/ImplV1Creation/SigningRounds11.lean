import Blanc.Lift.Usdc.ImplV1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb66 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xa2 0x90 0x3 0x91 0x80 0x51 0x40 0x60)) 1 (by decide) (UInt64.ofBytes 0x90 0x14 0x60 0x1 0x60 0x5b 0x56 0x50)) 2 (by decide) (UInt64.ofBytes 0x4 0x90 0xa 0x0 0x1 0x61 0x90 0x54)) 3 (by decide) (UInt64.ofBytes 0x0 0x60 0x5b 0x56 0x81 0x16 0xff 0x60)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x83 0x0 0x60 0x9 0x60)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x16 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x81 0x90 0x1 0x20 0x60 0x52 0x81 0x16)) 11 (by decide) (UInt64.ofBytes 0x54 0x20 0x0 0x60 0x1 0x20 0x60 0x52)) 12 (by decide) (UInt64.ofBytes 0x60 0x5b 0x56 0x50 0x90 0x91 0x50 0x90)) 13 (by decide) (UInt64.ofBytes 0x1 0x61 0x90 0x54 0x90 0x0 0x60 0x1)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x4 0x90 0xa 0x0)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed66 : Vector UInt64 25 :=
  #v[0x9fd51c02ea0f7f5, 0x83919ef24bc8616d, 0xa185d07cd67e715b, 0x650285305b9bcb6, 0x27bf8becb5285528, 0x3703697599e3a6aa, 0xfa62ba10e6e84366, 0x5ed7fc041d3c1f35, 0x30c7b35ce1a5cd2c, 0xb9a52667bd916281, 0x860f80e34cec2e32, 0x30db39dc773fd54d, 0x29ce6fae2dc8dd9, 0xc4cbcd6851bda194, 0x5df8871713a9384a, 0xd94a5698d5f37e7, 0x61b14e2bdf2643ad, 0x567f504fa963c780, 0x1c5f77362389839a, 0x813f9b908dfbab80, 0xf1d71972363cff6f, 0x95d9207652fd35b3, 0xe6cab8fe08d42fad, 0xf51e84bd176c0827, 0x119a33a3e77782a6]

private theorem words66 : absorb66 state66 = absorbed66 := by
  decide +kernel

private def quarter66_1 : Vector UInt64 25 :=
  #v[0x88c49b52cdaac8ba, 0xaf9a1dbc3a93d269, 0x518e60bea38b779a, 0x6863779da10d212b, 0x6ff7e1db5fe7dcb3, 0x4013858668e75913, 0x32e89c797abd467, 0x401d9c476f276e1, 0xf868c5a48c26cca, 0x69d4c7ec54701b5a, 0xef114cadc5530be, 0x787ed6ab6d944d80, 0xb8354527c61f9f9, 0x9d86d4cfa5f65373, 0xdd3471fa492e4fd7, 0x5b67b9ca2891bbc1, 0x24c1ed513e128196, 0x23cc7a69bf3318c2, 0xdb101be09da7f2ea, 0x318ebeb1ca81d7a7, 0x5ef7d130f37dea7, 0x92e45ed1999b95af, 0xcf446be38a7c2190, 0x4c64f2fb8625f2c7, 0x692cdc2efb7df063]

private theorem rounds66_0 : sixRounds 0 (by decide) absorbed66 = quarter66_1 := by
  decide +kernel

private def quarter66_2 : Vector UInt64 25 :=
  #v[0xde2c5f3052770442, 0x64fe96c24141e761, 0x62d6e8e982b05fb3, 0xded3d136d76f84b2, 0x4706b1791286aa5b, 0xa65f3f071d7f9acc, 0xb7049964b51e6d31, 0x1a1cf6e0c0ee7a06, 0x1529c7bd940b33a8, 0x52cae325e4e7c6d, 0xa2040cb126ec28db, 0x71559e053fe73db3, 0x1728742eb1f691a3, 0x39f25d581d7cc7f9, 0xf782dfc47576dd7f, 0xfc868430f3bd1e15, 0x88d313766e1eb946, 0xb86a1446a8ceda03, 0x5833933288812135, 0xc67c153023809e7, 0x5a0023f79f955590, 0x93ae23d6bb6c6780, 0x7104a8c0e6242c3, 0x4148d27e8ed77255, 0xa8a656ecb2518735]

private theorem rounds66_1 : sixRounds 6 (by decide) quarter66_1 = quarter66_2 := by
  decide +kernel

private def quarter66_3 : Vector UInt64 25 :=
  #v[0x1a563bd5c2c9fcbc, 0x7450f67878a70f52, 0x39b41319ab0b4044, 0x1957685cdfd00d9b, 0xd1c3e5c00a572928, 0xe6f9af556a3e2b45, 0x47cf77431779cda7, 0xac5a81c63db234d8, 0x350401dabe158e0c, 0xd9872af60ff45601, 0xc08d4bd3a235b478, 0x77e462283c4a6c66, 0xa0cb451fb18e86cc, 0xe08180e306c86dae, 0x245afa1bcf1996f7, 0xabad03cb192ebc2d, 0x9b43eacebc6979af, 0x4682733c3634832, 0xedd6f05fd285e13a, 0x86fd32628d7a65ad, 0x267bcb498ac5fa34, 0x4aa6a06d0d8989f5, 0xd3294ddc82be77be, 0x7bba66303059cb7a, 0xee980931290b3991]

private theorem rounds66_2 : sixRounds 12 (by decide) quarter66_2 = quarter66_3 := by
  decide +kernel

private theorem rounds66_3 : sixRounds 18 (by decide) quarter66_3 = state67 := by
  decide +kernel

private theorem perm66 : KECCAK.f1600 absorbed66 = state67 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds66_0, rounds66_1, rounds66_2, rounds66_3]
  rfl

theorem block66 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes66 ++ tail) state66 =
      KECCAK.Bytes.run 0 tail state67 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes66 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb66 ws)) := by
    rfl
  exact (step state66).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words66).trans perm66))

private def absorb67 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x16 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x33)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x14 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x0 0x60 0x57 0x2d 0x23 0x61 0x15 0x15)) 7 (by decide) (UInt64.ofBytes 0x14 0x60 0x80 0x1 0x60 0x5b 0xfd 0x80)) 8 (by decide) (UInt64.ofBytes 0x60 0x81 0x54 0x81 0xa 0x0 0x1 0x61)) 9 (by decide) (UInt64.ofBytes 0x15 0x15 0x83 0x90 0x16 0x19 0x2 0xff)) 10 (by decide) (UInt64.ofBytes 0x85 0x69 0x7f 0x50 0x55 0x90 0x17 0x2)) 11 (by decide) (UInt64.ofBytes 0x2 0x66 0xe6 0x68 0xa1 0x10 0x22 0xa0)) 12 (by decide) (UInt64.ofBytes 0xf9 0x70 0xe 0xdb 0xb6 0x5c 0x23 0xd3)) 13 (by decide) (UInt64.ofBytes 0xf 0x3c 0xa3 0x76 0xd3 0xa4 0x3b 0x2b)) 14 (by decide) (UInt64.ofBytes 0x40 0x60 0x25 0xf6 0xbf 0x34 0x94 0x3d)) 15 (by decide) (UInt64.ofBytes 0x90 0x3 0x91 0x80 0x51 0x40 0x60 0x51)) 16 (by decide) (UInt64.ofBytes 0x60 0xd 0x60 0x0 0x60 0x5b 0x56 0xa1))

private def absorbed67 : Vector UInt64 25 :=
  #v[0x3356bbbdac9d7bb3, 0x99e4fcfcd855b0f3, 0x8fad32b7a9b7c3a0, 0x7ec89e9cfcfa0fbd, 0x3edcb1d4390b0385, 0x75347a818a14d5c7, 0x83863899bbeae445, 0x818a25b50d29aea, 0x5fdaae53370861de, 0x9eb21a33e9c991d4, 0x1085b53cb4ec0fd8, 0xfee3f524dca544a3, 0xab162055bc23a920, 0x108d4956178f76f5, 0x20e9ba99bcfe358c, 0xe2e9345e7eda6328, 0xf450525d38997c4c, 0x50f05d179d39f14e, 0xb8a5e7341573cdad, 0xaf8ee0ced2b17007, 0x21a17a6b5b334b2c, 0xda3dd39a251c0645, 0x401cde209d2be28d, 0x9218c81c20ebde56, 0x631e88392820800b]

private theorem words67 : absorb67 state67 = absorbed67 := by
  decide +kernel

private def quarter67_1 : Vector UInt64 25 :=
  #v[0x3c007e5b0f279a5f, 0xff3267f68148e826, 0x4ab7aad247c17d5b, 0x93ece9054b14d3f4, 0xffee920d3dc14594, 0x287318b87d6d946f, 0x3041aa76e388e697, 0x5c97f92c2d138c49, 0xe1ebf04c9cfc0c7e, 0x5152e5000078d48e, 0xe675d80ca2bbdaac, 0xbafb306f421e2df4, 0x3a09e2f145b827ca, 0xe4099d06679a8964, 0xa053cd62b4dc15d8, 0x4a0414eb70f9f0ef, 0x6f2e846a83c88e3d, 0x3e677216740ccab1, 0x15b56c39925fc537, 0x6657c303ef6a27eb, 0xc2935c8119b163f2, 0xb3f3368cf91cc46c, 0x87545e378280b199, 0x50897c1328414299, 0x881f1b10d755f793]

private theorem rounds67_0 : sixRounds 0 (by decide) absorbed67 = quarter67_1 := by
  decide +kernel

private def quarter67_2 : Vector UInt64 25 :=
  #v[0xda9f9f3911411cb, 0x10f13a6c2006c903, 0xd68796c5d6f842d6, 0x43ba212e6fac1fe4, 0x2ca599ad8327c82c, 0xda673693e4f4650f, 0xdc23f352abd3f878, 0x1d99b1651ef46d4b, 0x38509517bc79d182, 0x64efb031ac1a3f8, 0x1e10d061ee518235, 0xe6a06a20c1f453ab, 0x2c15adb6d5370511, 0x48d60654708b3320, 0x2b21fe0c7d2768f2, 0xdee0728c0386aed, 0xf4c54723c1cbe8ca, 0x77b772c58b01cbe7, 0x736bb897137e9455, 0x7744562d01caa5df, 0x7bb725080d8a7f3e, 0x8bf626e1dbcb62b0, 0x62fe8e0a41d8fd73, 0xd2d3bd57faaac22e, 0xa048120dec61ef31]

private theorem rounds67_1 : sixRounds 6 (by decide) quarter67_1 = quarter67_2 := by
  decide +kernel

private def quarter67_3 : Vector UInt64 25 :=
  #v[0xcf6dd54b2ba8cb7, 0x2b4dba00d85b5ad, 0x75411899d120adaf, 0x84f65ef1f00ff18b, 0x4f995515e362d9f9, 0x1456bd59be9b5012, 0xbdecce24b5b60fe2, 0xd42869ef62a46c73, 0xdff19a9ebb720f75, 0xd02a13f7b24408b7, 0x96ae21482aa118c6, 0xeaae68d877c19753, 0x47dcb57a93ccbbf5, 0x263e1e016b8a4c68, 0x308fe4accb6d172f, 0xf57a2b4d520bfe34, 0xfd6c177ccc72e795, 0xb117b9574251938d, 0xfcddc61e857a7fb7, 0x3509bbcb8fe37179, 0xd3e57c8b6d22ba0d, 0xfa282e2371c89e5c, 0x30f7c88fe513b6df, 0x8ce6e160486b8799, 0x962e79e25a025a46]

private theorem rounds67_2 : sixRounds 12 (by decide) quarter67_2 = quarter67_3 := by
  decide +kernel

private theorem rounds67_3 : sixRounds 18 (by decide) quarter67_3 = state68 := by
  decide +kernel

private theorem perm67 : KECCAK.f1600 absorbed67 = state68 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds67_0, rounds67_1, rounds67_2, rounds67_3]
  rfl

theorem block67 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes67 ++ tail) state67 =
      KECCAK.Bytes.run 0 tail state68 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes67 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb67 ws)) := by
    rfl
  exact (step state67).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words67).trans perm67))

private def absorb68 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x83 0x0)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x52 0x81 0x16 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x90 0x1 0x20 0x60)) 7 (by decide) (UInt64.ofBytes 0x91 0x50 0x90 0x54 0x20 0x0 0x60 0x1)) 8 (by decide) (UInt64.ofBytes 0x60 0x80 0x0 0x60 0x5b 0x56 0x50 0x90)) 9 (by decide) (UInt64.ofBytes 0xa 0x0 0x1 0x61 0x90 0x54 0x90 0x0)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x4 0x90)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x80 0x5 0x60 0x5b 0x56 0x90 0x50 0x90)) 14 (by decide) (UInt64.ofBytes 0x15 0x16 0x1 0x60 0x81 0x1 0x60 0x54)) 15 (by decide) (UInt64.ofBytes 0x2 0x60 0x16 0x3 0x2 0x0 0x1 0x61)) 16 (by decide) (UInt64.ofBytes 0x20 0x60 0x1 0x1f 0x60 0x80 0x4 0x90))

private def absorbed68 : Vector UInt64 25 :=
  #v[0x4a7a46e93b097f73, 0xc0ee991c634ead5a, 0xe55355030e620d73, 0x6c88ca48133488ba, 0x446baeacc7fac28, 0xa1b65e5490d2c886, 0x9b1442d8221b7625, 0x2b88a7b3e6c7a882, 0x82ecdad33490b7fe, 0x576e7fa2a484761a, 0xab259e38432cbed0, 0xab3bd76e84b9d560, 0x3ec344f9d9fb26e9, 0xc4c3d0d3ffc87e75, 0xe0f13d0ef91d5dbf, 0xedd485f5ee792156, 0x8bebf9134a57bf0e, 0x5dec37d7c9554d08, 0x4fedaaec84807da3, 0xbef96dcad99ea536, 0x226e06f953611fa7, 0xfa85e029627e27e0, 0xcbcf3bf3bd407dc8, 0x698bdce4dd0924ea, 0x9b4ca2ecb1e6da66]

private theorem words68 : absorb68 state68 = absorbed68 := by
  decide +kernel

private def quarter68_1 : Vector UInt64 25 :=
  #v[0x33fd4b3827a46dd7, 0x2d1bb2f685e0a514, 0xc6ea76681a7b7288, 0x6a7f277f33bc89a2, 0x1f33bf40ba0779d2, 0xb504c6e8929cc4b8, 0xe276f64a0ced250e, 0x841da80a770f17c, 0x232570c2d56311c8, 0x678b0b5b3f572e14, 0x699ba390e3931ad, 0x1959553f8809f664, 0x5d496df9d09a3474, 0xfb50a937a5823f8e, 0x3b8a948fe296df6e, 0xebae5adce43bb45f, 0xe97a235a25777212, 0x4938874ed74b0b5, 0x612cfe6b0f3275e4, 0x5bbee656d3c71b0d, 0x475c7bd46910cac7, 0xe43cbc0c79392070, 0x706dcbbe5ab7787c, 0x404c8f7eaeb6486, 0x7e60b8bb919d9ef0]

private theorem rounds68_0 : sixRounds 0 (by decide) absorbed68 = quarter68_1 := by
  decide +kernel

private def quarter68_2 : Vector UInt64 25 :=
  #v[0xb9a1c87ea63817ac, 0x88e6d8aad92de57c, 0x76f38f9a680ccfdf, 0xa3bff0f2bf9f826e, 0x2e5312a3a96470fe, 0x8effec92a442b942, 0xf12023953ffc5069, 0x9c24d863fad0f57b, 0xeb723164a55e12fe, 0x38756ca67ce04efb, 0xcb4971e556c6608d, 0x8240fb7b8eb35ff, 0x3214b856536d68c3, 0xfd77ec0721bf9262, 0x8fe0d751a00ac538, 0x61e2f309bbc218a, 0xfb40a654f902f05, 0xc8d43e769dd3a8ba, 0xad415bcd0e24e84a, 0xa6d0e2ff3a370150, 0xd98cf3c28bba53a, 0xae9008b6938c4ce, 0xb714ecdbaac790b2, 0x58360d1f682bdfb0, 0xcc0eb6f58d0fcdfd]

private theorem rounds68_1 : sixRounds 6 (by decide) quarter68_1 = quarter68_2 := by
  decide +kernel

private def quarter68_3 : Vector UInt64 25 :=
  #v[0x1ccc3d162af31a7b, 0x3615a321aa2c99dc, 0x14b893bd5dafc072, 0xde496b01c364b487, 0x83b35777d5c75d19, 0xd7a0a87182103adb, 0xdf68ba6d754eae09, 0x6fe220d6682d684, 0xbcb34e3d3c092d0f, 0x8af2ea747141026c, 0xef23bfef9f4eb4e, 0x73e3242aa5129309, 0xd0e13cdae5fc1fa1, 0xf248d307a17c34e3, 0xc538080e44db5d69, 0x172f9a389e43e3e8, 0x958ba6c3859c26bd, 0xb8148473ee4935a8, 0x22440c8b70604ee4, 0x3bd4732b591b353b, 0x6605e89ad6fe57e2, 0x88bf4298eded8c79, 0xcb8fcb8b290b430c, 0x1f4ee1db198de55f, 0x5a7301f641208dc3]

private theorem rounds68_2 : sixRounds 12 (by decide) quarter68_2 = quarter68_3 := by
  decide +kernel

private theorem rounds68_3 : sixRounds 18 (by decide) quarter68_3 = state69 := by
  decide +kernel

private theorem perm68 : KECCAK.f1600 absorbed68 = state69 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds68_0, rounds68_1, rounds68_2, rounds68_3]
  rfl

theorem block68 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes68 ++ tail) state68 =
      KECCAK.Bytes.run 0 tail state69 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes68 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb68 ws)) := by
    rfl
  exact (step state68).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words68).trans perm68))

private def absorb69 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x60 0x1 0x20 0x60 0x2 0x4 0x91 0x80)) 1 (by decide) (UInt64.ofBytes 0x52 0x40 0x60 0x1 0x81 0x90 0x51 0x40)) 2 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x81 0x90 0x91 0x92 0x80)) 3 (by decide) (UInt64.ofBytes 0x81 0x1 0x60 0x54 0x80 0x82 0x1 0x20)) 4 (by decide) (UInt64.ofBytes 0x2 0x0 0x1 0x61 0x15 0x16 0x1 0x60)) 5 (by decide) (UInt64.ofBytes 0x15 0x80 0x4 0x90 0x2 0x60 0x16 0x3)) 6 (by decide) (UInt64.ofBytes 0x10 0x1f 0x60 0x80 0x57 0x7d 0x24 0x61)) 7 (by decide) (UInt64.ofBytes 0x80 0x0 0x1 0x61 0x57 0x52 0x24 0x61)) 8 (by decide) (UInt64.ofBytes 0x60 0x91 0x52 0x83 0x2 0x4 0x54 0x83)) 9 (by decide) (UInt64.ofBytes 0x5b 0x56 0x7d 0x24 0x61 0x91 0x1 0x20)) 10 (by decide) (UInt64.ofBytes 0x60 0x52 0x0 0x60 0x90 0x91 0x1 0x82)) 11 (by decide) (UInt64.ofBytes 0x54 0x81 0x5b 0x90 0x20 0x0 0x60 0x20)) 12 (by decide) (UInt64.ofBytes 0x60 0x90 0x1 0x1 0x60 0x90 0x52 0x81)) 13 (by decide) (UInt64.ofBytes 0x60 0x24 0x61 0x11 0x83 0x80 0x1 0x20)) 14 (by decide) (UInt64.ofBytes 0x82 0x16 0x1f 0x60 0x3 0x90 0x82 0x57)) 15 (by decide) (UInt64.ofBytes 0x50 0x50 0x50 0x50 0x50 0x5b 0x91 0x1)) 16 (by decide) (UInt64.ofBytes 0x90 0x0 0x60 0x1 0x60 0x5b 0x56 0x81))

private def absorbed69 : Vector UInt64 25 :=
  #v[0xc6965d1459bda21f, 0xb1b7e29ef0f54ca3, 0xe5dc95c902244ad9, 0x9b381846f5e1787f, 0x465bf23dfedd1c75, 0xca8ed8a47823c8ca, 0x6a75d0f8a1228645, 0xc6a94d0f2279c123, 0xec0eb43d1758d4ab, 0x641feb0f121c43fd, 0x3bc880ff73d4103e, 0xdb7482cd4fb0f69d, 0x7fdede07cacb46a2, 0xf7fc9ad4a25526e8, 0x78945615bc872304, 0xc54c76c958dfae5c, 0xa05b13ffcb00ad3, 0x796b86b21fe9f48e, 0xa18c7867d26baa47, 0x1cecde6b154d3fa3, 0xfef303737fce108d, 0x57cda2d7072a1104, 0xd048f3e9ef466aac, 0x547f99696a6fdc2d, 0x37b0f43cd84a50df]

private theorem words69 : absorb69 state69 = absorbed69 := by
  decide +kernel

private def quarter69_1 : Vector UInt64 25 :=
  #v[0x8fb1d8bd31939f68, 0x12a37b0a460b9958, 0x2670d5f19e192c63, 0xd6ebc1fcd222e07f, 0xa3961604b68317b9, 0x5766062eeb93d323, 0x957b46ab6eafd47e, 0x256da83841b6af2, 0x7d2ab0aa476e6e58, 0x56efbf9cbf3d5bda, 0xd8320abf27e84264, 0xc42eab96e30aa252, 0x3e03fda6c80bcf09, 0xe1d3eec1f8ea6cb7, 0x9f7e564e1c8970b6, 0xebe0bad600206c66, 0x7964dc7f26632852, 0x9d8fa3614df8d8d6, 0x38832a04c62f4ba2, 0x39d39045612dcca, 0xf991dd6ce7b0adc3, 0xae771b7cd24c57d8, 0x252487fd97249dcc, 0xc8472d0b7ece0a16, 0x53d131d0c26fa65]

private theorem rounds69_0 : sixRounds 0 (by decide) absorbed69 = quarter69_1 := by
  decide +kernel

private def quarter69_2 : Vector UInt64 25 :=
  #v[0x6c0b7b264bab0130, 0x588ed394039a69f3, 0x9803ca6317b14340, 0xcba59d317eb69d80, 0x8dc77eb624eaaf41, 0x285893baf14cfae2, 0xa0482eb20f1c25ca, 0x9e1217a721927d8c, 0x1ec774d030621831, 0x5b1a74a20c36f0a2, 0x87e35febf885e693, 0xc83aef81b37dc2e5, 0x91909c7ad9e4d62a, 0x76f2bd5fd4355cea, 0xf1ae674662b92388, 0xf03ec2a78357f133, 0x832a6e589ce180ea, 0x47b885b5bdabc6f8, 0x7bfa3ab6fccf1305, 0x368e6b0cabf26d19, 0xe79dfe2209add5f5, 0xa31a5cee9f3916fd, 0xb04844f774e22d85, 0x18ffaf6a251d3a0, 0x909290e9f4d629be]

private theorem rounds69_1 : sixRounds 6 (by decide) quarter69_1 = quarter69_2 := by
  decide +kernel

private def quarter69_3 : Vector UInt64 25 :=
  #v[0x73fedbbc0c6ef61e, 0xab9df7159478e40d, 0xcd846beb54fb, 0x59d3171a93cf4f38, 0x80f3d50bb2945140, 0x39c812b4eb241653, 0xee03b511f8c3dcff, 0xfee7caefc2db30ea, 0xa6ad6387aab2aa9b, 0x8f02db284af9973e, 0x728016e0c7d7ce40, 0x3fe7843fb20954ff, 0xa39733b474ef7e1d, 0xb3eab1a0ff14d973, 0x7b3fe13925b919e3, 0x7c0cc5ba946ef2ed, 0x8c14bad187f3b7b, 0xe2354fbce526a30a, 0x4710816b9eaa9b2e, 0xcd94b2c05013de38, 0xf80e093a7dfd1e80, 0x609a239f2629339e, 0x273b02527959baa5, 0x8c39c74cb178860f, 0x720ee8baa81023bc]

private theorem rounds69_2 : sixRounds 12 (by decide) quarter69_2 = quarter69_3 := by
  decide +kernel

private theorem rounds69_3 : sixRounds 18 (by decide) quarter69_3 = state70 := by
  decide +kernel

private theorem perm69 : KECCAK.f1600 absorbed69 = state70 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds69_0, rounds69_1, rounds69_2, rounds69_3]
  rfl

theorem block69 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes69 ++ tail) state69 =
      KECCAK.Bytes.run 0 tail state70 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes69 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb69 ws)) := by
    rfl
  exact (step state69).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words69).trans perm69))

private def absorb70 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x4 0x90 0xa 0x0 0x1 0x61 0x90 0x54)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x56 0x81 0x16 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x90 0x14 0x60 0x1 0x60 0x0 0x60 0x5b)) 5 (by decide) (UInt64.ofBytes 0x4 0x90 0xa 0x0 0x1 0x61 0x90 0x54)) 6 (by decide) (UInt64.ofBytes 0x24 0x61 0x15 0x15 0x15 0x16 0xff 0x60)) 7 (by decide) (UInt64.ofBytes 0x33 0x5b 0xfd 0x80 0x0 0x60 0x57 0xc9)) 8 (by decide) (UInt64.ofBytes 0x0 0x60 0x3 0x60 0x15 0x15 0x0 0x60)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x83)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x73 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x16 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x90 0x1 0x20)) 16 (by decide) (UInt64.ofBytes 0x90 0x54 0x90 0x0 0x60 0x20 0x0 0x60))

private def absorbed70 : Vector UInt64 25 :=
  #v[0xdda99017c7f7147c, 0xa1d3ca5e9e14a3ce, 0xdc04843c038f19ec, 0x84284e95796a6709, 0x5be496ef811965d, 0x3ea7a6964d610d4f, 0xe3699453c6eb3c54, 0x3075f5eaf412dbb8, 0xb2e1639568b9d725, 0x6d933b3b14f59a4a, 0xfc5a4292b3020490, 0x3454497ad9747cd0, 0x98d438059da7c10c, 0xe48150070446dc5f, 0xb2dcafddfc8f2731, 0xe11fe9f5f5899a7e, 0xcb8d823aa045da29, 0xe53b91633e76f5aa, 0xbe7df2604bdc64f7, 0x6ba03655509a19dd, 0x583553771d572770, 0xce311c10d5802eed, 0x4570d22c393527c4, 0x96099fedc239f0e9, 0x4f304747dad653fe]

private theorem words70 : absorb70 state70 = absorbed70 := by
  decide +kernel

private def quarter70_1 : Vector UInt64 25 :=
  #v[0x618420ff9aa096ae, 0x684174937b9726ef, 0xa8b9054d5c000201, 0xa835f8b8f550d17f, 0x76f7ae6ab7c7fb78, 0x4af6d9435a71d89, 0x63e8433032aa06f8, 0xcb391106b76118b3, 0xa1213f8cee86274f, 0xd44b201f725b6db8, 0x663e62f6875b18f, 0xb2160f46da28cd55, 0x63bda4df9ac742a8, 0x2c0e4eaf1dfadf19, 0x7a4f0c61a3da96b0, 0xd2f069667adc2669, 0xeb30dd125a4a14e3, 0xa381ea87e41691bc, 0xf7da4b30672cf2ae, 0x8d9486b8bdf05dd6, 0x4ed2eb9d0f40a28b, 0x3789f33c23515a6, 0xef576b481abaa917, 0x73f6dbbd3728a547, 0x78fcd1bf6c827ed]

private theorem rounds70_0 : sixRounds 0 (by decide) absorbed70 = quarter70_1 := by
  decide +kernel

private def quarter70_2 : Vector UInt64 25 :=
  #v[0x925ed988dadc52b5, 0x2d45b0bac2217827, 0x44e203911d8007bd, 0xed4d869a08e13ca6, 0xb0360c2ab67ea124, 0xd34f1bf306d03330, 0x986e986a1d453e65, 0x66dd49a3db37a0a1, 0xe4b3cb503612c391, 0xf418aaef141836a5, 0xd187d37c74d1b846, 0x4fec611bd775ca73, 0x34e285481a16db33, 0x4424db100039a75d, 0x984784a1a1ef928, 0x82939be7f3206847, 0xab805a2015f5f136, 0xe1e0a49f40ef857e, 0x632f4335c9a69944, 0xc689c4f39be9b09b, 0xef6f66e2842dc2a0, 0x6b044ad071918203, 0x1dea635da93f801d, 0x9c8bf0f89b81f880, 0x99575ff98f68c25b]

private theorem rounds70_1 : sixRounds 6 (by decide) quarter70_1 = quarter70_2 := by
  decide +kernel

private def quarter70_3 : Vector UInt64 25 :=
  #v[0x3d83e842ecbc48e0, 0x380cc26c76bf8637, 0x6b123252c0fee17b, 0x472c2281a973f5e8, 0x819f1f4dd770347b, 0xfb9a93f2e567fc61, 0x2c56182156b91feb, 0x5785c058ab65ebda, 0xeb16bb202be02991, 0xac4aea2b0e09cc99, 0x656e36197f73afee, 0x2a93493dfdc604b1, 0x65574ccffd755d71, 0x14e8034a1ee87e52, 0x9770447bc444d51a, 0xacfcf856dfb691a, 0x81d9159c1ce4d222, 0x1552c72e0780c02a, 0x60a78f068fd5cc86, 0x520ba0567a2c890b, 0xd753a4c5d7761791, 0x77c966a7cec99bda, 0x75389f7db1768126, 0xbac75a104b879719, 0x6d34ea1d73896472]

private theorem rounds70_2 : sixRounds 12 (by decide) quarter70_2 = quarter70_3 := by
  decide +kernel

private theorem rounds70_3 : sixRounds 18 (by decide) quarter70_3 = state71 := by
  decide +kernel

private theorem perm70 : KECCAK.f1600 absorbed70 = state71 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds70_0, rounds70_1, rounds70_2, rounds70_3]
  rfl

theorem block70 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes70 ++ tail) state70 =
      KECCAK.Bytes.run 0 tail state71 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes70 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb70 ws)) := by
    rfl
  exact (step state70).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words70).trans perm70))

private def absorb71 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0x60 0x4 0x90 0xa 0x0 0x1 0x61)) 1 (by decide) (UInt64.ofBytes 0x25 0x61 0x15 0x15 0x14 0x15 0x15 0x16)) 2 (by decide) (UInt64.ofBytes 0x83 0x5b 0xfd 0x80 0x0 0x60 0x57 0x29)) 3 (by decide) (UInt64.ofBytes 0x0 0x60 0x3 0x60 0x15 0x15 0x0 0x60)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x83)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x73 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x16 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x90 0x1 0x20)) 11 (by decide) (UInt64.ofBytes 0x90 0x54 0x90 0x0 0x60 0x20 0x0 0x60)) 12 (by decide) (UInt64.ofBytes 0xff 0x60 0x4 0x90 0xa 0x0 0x1 0x61)) 13 (by decide) (UInt64.ofBytes 0x25 0x61 0x15 0x15 0x14 0x15 0x15 0x16)) 14 (by decide) (UInt64.ofBytes 0x60 0x5b 0xfd 0x80 0x0 0x60 0x57 0x89)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x0)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed71 : Vector UInt64 25 :=
  #v[0xe846b5b5b0462b6e, 0x77c9971cbd8ee92f, 0xc0141a9adc909b46, 0x21c5906e2d6ed814, 0xf65ac97a03cac908, 0xb518417004a6c276, 0x2482e877fc9fc7ae, 0xe9dd95464a935dde, 0xa334943a75134acd, 0x90ba6660cf655520, 0xfc5bece5c8c97260, 0x5a7ef5609ac1ce3e, 0xdbe3811fb7cfd46a, 0x3b40fc1d6b063f86, 0xdc99dc16ec100428, 0x1a24386fbb1eaca4, 0x46ebc9efce48c1cd, 0x2707a10a26a89c37, 0x93802449c8088f30, 0x1b3309d680d40031, 0x164e365da8d8970c, 0x6f268caa37b19440, 0x8eac06e5cad7cb0e, 0xc27a880ba1ccfda0, 0x6a1913689482b5b0]

private theorem words71 : absorb71 state71 = absorbed71 := by
  decide +kernel

private def quarter71_1 : Vector UInt64 25 :=
  #v[0xa7d876babb6ded61, 0x111c1e6f896045dc, 0x33523421fbbe5227, 0x1ef0c9f60e0a0548, 0xfd8824e58a2eb0c1, 0x2ecd179011f8d7ca, 0x2b86c645d163524e, 0x506619f864a4bb5d, 0xc4c1523396f3235f, 0x12ecbcabb3937890, 0x1e98ee81e5e83dd3, 0x42695ad23cb6f48d, 0x129f10b1de05dbeb, 0x1e78d64df14950d6, 0x42cc5cb291f95dc1, 0xe85a7adb0d1875ce, 0xd9dddba43db45728, 0x33f53e0e3d623036, 0x386a2a8071f57aa7, 0x7fc3c24074f54bd6, 0x8b71c1cc1f01b1b5, 0x35d964589ddeca27, 0xf5b082ffb8dc4fdb, 0x87f8a1879faf7d8e, 0x8a77f193d75f58aa]

private theorem rounds71_0 : sixRounds 0 (by decide) absorbed71 = quarter71_1 := by
  decide +kernel

private def quarter71_2 : Vector UInt64 25 :=
  #v[0x7e5703ce0568c4a0, 0xd014ea5d4d08cf93, 0xb6873ac934ff3d27, 0xe5f3d405e6ce4d94, 0x9a521ff9a26c9ca6, 0xfda1e32be144c6e3, 0xb3628a2e41358b1b, 0xe9e84e07bcced162, 0x61dba44d787be497, 0x383897895bd0a8cd, 0x56ad9ce90d20ca60, 0xc8b508f0d292fef1, 0x6a5c05612ec49ac, 0x5f8462b8d55af10e, 0x7b9590781831f4ae, 0xcf6adc21d58974ef, 0x526c6273171216a2, 0xb763b8cf9069e1c4, 0xb03c92b94e99fdbb, 0xc44bad8d46529244, 0x40cbfb9e4944e21c, 0xa95dc3f291b05cb4, 0x9dd9958588566616, 0xac8b9db7bc7ac0ef, 0xe8c8107921c080d]

private theorem rounds71_1 : sixRounds 6 (by decide) quarter71_1 = quarter71_2 := by
  decide +kernel

private def quarter71_3 : Vector UInt64 25 :=
  #v[0x8fb4d1af0d4b6dea, 0xe0735b8c70cad7e6, 0x7846c76dd5baa8a3, 0x955ce058f80c921a, 0x977ab6bb613a7da2, 0x5255a15d541fd8ce, 0xaa733635e74d210, 0x29e0859e3d6a6909, 0x1697cb3e12ccc525, 0x1b84c70ed11d6142, 0xe4cc2e3c50922623, 0x64272c7caa6114f4, 0x10af8fc21131241f, 0xb2d4d183e0c15087, 0xeb408344d0149f18, 0xd75dff771a22756b, 0xddafc399e7cd2a5f, 0x15737b57587863b9, 0x65a4004eb142e791, 0x5a5b27d9c5818044, 0x7e5d0f84a73c442f, 0x280c99ed401c0d, 0xaa7a1c13dcda99ac, 0x7976e02f40f23906, 0x9980bfe65e89bd5]

private theorem rounds71_2 : sixRounds 12 (by decide) quarter71_2 = quarter71_3 := by
  decide +kernel

private theorem rounds71_3 : sixRounds 18 (by decide) quarter71_3 = state72 := by
  decide +kernel

private theorem perm71 : KECCAK.f1600 absorbed71 = state72 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds71_0, rounds71_1, rounds71_2, rounds71_3]
  rfl

theorem block71 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes71 ++ tail) state71 =
      KECCAK.Bytes.run 0 tail state72 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes71 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb71 ws)) := by
    rfl
  exact (step state71).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words71).trans perm71))

end Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
