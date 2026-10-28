import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb024 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x61 0x15 0x11 0x81 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x80 0x0 0x60 0x57 0x55 0xc)) 2 (by decide) (UInt64.ofBytes 0x11 0x1 0x82 0x20 0x60 0x83 0x1 0x82)) 3 (by decide) (UInt64.ofBytes 0x80 0x0 0x60 0x57 0x67 0xc 0x61 0x15)) 4 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x90 0x35 0x80 0x5b 0xfd)) 5 (by decide) (UInt64.ofBytes 0x1 0x84 0x2 0x83 0x1 0x60 0x84 0x91)) 6 (by decide) (UInt64.ofBytes 0x83 0x0 0x0 0x0 0x0 0x1 0x64 0x11)) 7 (by decide) (UInt64.ofBytes 0x60 0x57 0x89 0xc 0x61 0x15 0x17 0x11)) 8 (by decide) (UInt64.ofBytes 0x50 0x92 0x90 0x50 0x5b 0xfd 0x80 0x0)) 9 (by decide) (UInt64.ofBytes 0x61 0x5b 0x56 0xf6 0x35 0x61 0x50 0x90)) 10 (by decide) (UInt64.ofBytes 0x61 0x5b 0x56 0x5 0x37 0x61 0x23 0x4)) 11 (by decide) (UInt64.ofBytes 0x60 0x3 0x36 0x80 0x4 0x60 0x23 0x4)) 12 (by decide) (UInt64.ofBytes 0x57 0xb2 0xc 0x61 0x15 0x10 0x81 0x40)) 13 (by decide) (UInt64.ofBytes 0xff 0x73 0x50 0x5b 0xfd 0x80 0x0 0x60)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x91 0x16 0x81 0x35 0x81 0xff 0xff 0xff))

private def absorbed024 : Vector UInt64 25 :=
  #v[0x8f227ec80c1999ad, 0xf0fe0c370dba7d1c, 0xf824c3b9ef41360f, 0xe36c0fc83a463ba3, 0xbc76844cce233c9e, 0xfca1339e4dd430d1, 0xf663d08fcd57d779, 0x917378bad93f8673, 0xeeb39d9e36d124e8, 0xb2cb2636c71d8532, 0x215902c6dff77b69, 0xa1f93900958e239e, 0xbf16db4feba3d658, 0x224ffe10cc6f446f, 0x4ef66db9358552d5, 0xd1aaca07d255e68c, 0xbba93d4accc6bf9b, 0xf4a4fc81d85be58a, 0x84f6bd23d3a110e5, 0x33206a36b0b5e27a, 0xe5e795a312ee7ca9, 0xda03f6fc5a1df09b, 0x77aa8c4790f1d5d1, 0x3211cc8b3ba2ce7d, 0x889dff6b9c176f28]

private theorem words024 : absorb024 state024 = absorbed024 := by
  decide +kernel

private def quarter024_1 : Vector UInt64 25 :=
  #v[0x4ebe6582af0d6987, 0x557ac5273a4528b1, 0x7b293f84072aceb, 0x57df7f34c0043ca3, 0x519d8efdc535dcce, 0xa4fccfd232de160, 0x22ab36ddb7e85d0a, 0xbdf54d9a82eb31b4, 0xa3de5efcebd906b, 0xb2faa88e764338f6, 0xd261b75c19236fbd, 0xcb77b85e0e5ddbc9, 0xee2c9e9cb4d80a90, 0x8eedfdd16ed26a8a, 0x1105b1ccd26e8635, 0x5b9193d6711e6129, 0xb9f98f2befff93ee, 0xa9aceb9c02eadb1b, 0x16341219ded999cd, 0xf098761525e26b90, 0x50bd2a9a828d1d2d, 0xf9751db2ff72902e, 0x2a7a85ae399e29d4, 0x6382faa438e7e83d, 0x3fb74c0940fcf48a]

private theorem rounds024_0 : sixRounds 0 (by decide) absorbed024 = quarter024_1 := by
  decide +kernel

private def quarter024_2 : Vector UInt64 25 :=
  #v[0x9194b8917fe9f5b, 0x4c6e2ba21fcf481c, 0xed364e219752c035, 0xc762d8d3a83ca454, 0xd50f694c0a49be9a, 0xb5cb7df502ed9aba, 0xda285b157c2487f5, 0xf52603795a27e54f, 0x89e03c6291380e54, 0x76dee81f406ad491, 0xe2b461c5b2a126c3, 0xf40df83d64404258, 0x6c0a90e469889684, 0x316f8b148a66bd3a, 0xf003f4503186f5d5, 0x445dc2cfb3409a95, 0x4a6f4a43447bbe44, 0x99b90410ba94a000, 0x88f09d6d88e954ee, 0x4c0164094f76dc7c, 0xb2655f683383ea88, 0xad875db2c0ccea94, 0x2d2aba60d58d3e8a, 0x6487e633024cec43, 0xe2969b9801ed9ac0]

private theorem rounds024_1 : sixRounds 6 (by decide) quarter024_1 = quarter024_2 := by
  decide +kernel

private def quarter024_3 : Vector UInt64 25 :=
  #v[0x692690a3521310cd, 0x22ac190c1a3c8f21, 0xc50ed96747eeb367, 0x24010a96e077aeca, 0xe9f2ad00d674dd66, 0x8161b460850a6142, 0x3137995385fbb778, 0x3a45c9a3fdb222be, 0x906e5283a719ca3b, 0x7a09d2470bb5ce8b, 0x607afdb794239ea2, 0xd0811544e3670013, 0x6a1d7b5894a437c3, 0xa74b95bc3e13b142, 0xa13c8191cd046bb3, 0x1f57752e5c880091, 0x858187bc328361f1, 0x7af76132e86b9f35, 0xa48d4901985d3dc9, 0xf13be9b77280ab98, 0x22031d3e3539217c, 0x825492ab5c29d07f, 0x2ae209c29303c753, 0xf9ac71c7e2182b44, 0xdb1ed0d1d245e521]

private theorem rounds024_2 : sixRounds 12 (by decide) quarter024_2 = quarter024_3 := by
  decide +kernel

private theorem rounds024_3 : sixRounds 18 (by decide) quarter024_3 = state025 := by
  decide +kernel

private theorem perm024 : KECCAK.f1600 absorbed024 = state025 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds024_0, rounds024_1, rounds024_2, rounds024_3]
  rfl

theorem block024 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes024 ++ tail) state024 =
      KECCAK.Bytes.run 0 tail state025 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes024 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb024 ws)) := by
    rfl
  exact (step state024).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words024).trans perm024))

private def absorb025 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x29 0x37 0x61 0x16 0x35 0x1 0x20 0x60)) 1 (by decide) (UInt64.ofBytes 0x80 0x4 0x60 0x70 0x4 0x61 0x5b 0x56)) 2 (by decide) (UInt64.ofBytes 0x15 0x10 0x81 0x20 0x1 0x61 0x3 0x36)) 3 (by decide) (UInt64.ofBytes 0xfd 0x80 0x0 0x60 0x57 0xee 0xc 0x61)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x50 0x5b)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x81 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x1 0x81 0x20 0x60 0x91 0x16 0x81 0x35)) 8 (by decide) (UInt64.ofBytes 0x81 0x40 0x60 0x90 0x16 0x91 0x90 0x35)) 9 (by decide) (UInt64.ofBytes 0x35 0x1 0x81 0x60 0x60 0x90 0x35 0x1)) 10 (by decide) (UInt64.ofBytes 0x60 0x90 0x35 0x1 0x81 0x80 0x60 0x90)) 11 (by decide) (UInt64.ofBytes 0x60 0xff 0x60 0x90 0x35 0x1 0x81 0xa0)) 12 (by decide) (UInt64.ofBytes 0xe0 0x60 0x90 0x16 0x35 0x1 0x82 0xc0)) 13 (by decide) (UInt64.ofBytes 0x1 0x0 0x1 0x61 0x90 0x35 0x1 0x81)) 14 (by decide) (UInt64.ofBytes 0x4 0x61 0x5b 0x56 0x61 0x37 0x61 0x35)) 15 (by decide) (UInt64.ofBytes 0x1 0x61 0x3 0x36 0x80 0x4 0x60 0x70)) 16 (by decide) (UInt64.ofBytes 0x57 0x5a 0xd 0x61 0x15 0x10 0x81 0x20))

private def absorbed025 : Vector UInt64 25 :=
  #v[0xf6adcab845081714, 0x80ab5e6098f01f51, 0xd9aa14b13b6dda6e, 0x6020d038a793cb5b, 0x1090960e8e2c2b6e, 0x5876c07c9be082e6, 0x6614088ae73549, 0x2ad770fd83946104, 0x76a996b814384519, 0x713ce8c52a11d922, 0x448036802689356c, 0x5c8f435443c81b28, 0x4a4123a5cf9b4539, 0xee6991c4e2459bc5, 0xd92fbb4978ae8dce, 0x17bcdb4d7d445c8a, 0x45ee67276fbaa184, 0x7fa90dbe2fbd3bb8, 0xd3d80abad7645356, 0xf55dc63241329697, 0xd1ecb75bdd3e8bb1, 0xfc2ccb737469c1ed, 0xfc451e37db281bd5, 0x68ae09d51a288ab, 0x206cbd246273fcb7]

private theorem words025 : absorb025 state025 = absorbed025 := by
  decide +kernel

private def quarter025_1 : Vector UInt64 25 :=
  #v[0x72eabd345dab2bc5, 0x28b62921f133b0ad, 0x5dbfb0df9d22d4de, 0x72e522094ef4b501, 0x22c051571c3e3fad, 0x6106c9b0e7b1ab71, 0x64e3f247e2b8db83, 0x773f8a07f3dacbf, 0x9378edf83b82b49f, 0xa13344535aa198a1, 0x2a9ae0c1d69d4972, 0x22bf0db39ec294ca, 0x1f29b6e5e9271b2f, 0x56614bd54491cf71, 0xa95b960c3f0ae87b, 0x8a898dbbdd63cbe4, 0xb2f355f461ab9959, 0xbd02775ebdb7ac81, 0xc12187c4f278065d, 0xb1ed7ee3601d7a6, 0x5c5e6ce04323ad36, 0xaecccb68ad6887a3, 0xa1b23f0e47a81468, 0x68d946aa6bc36324, 0xddd720b1a045b98d]

private theorem rounds025_0 : sixRounds 0 (by decide) absorbed025 = quarter025_1 := by
  decide +kernel

private def quarter025_2 : Vector UInt64 25 :=
  #v[0x1d50d7d212963a88, 0x654ca61daa3a50ff, 0xe6498fc15314e4d0, 0xe4473ed8dafebc50, 0x45502ca783ae975b, 0x5aee518caf3c0075, 0x409e7ebbe9da10a8, 0x43f8c23b47ec7778, 0xba50c4be6cec99f2, 0xd3b04b378dc713b4, 0x5581fe2db0cf7902, 0x5fb931e773303ba2, 0x2d14127d633083b9, 0xdeabf02b3356beb4, 0x9494ae4e4c105b2e, 0x5885a3e480392413, 0x8c7d20402e13bf62, 0xac2de1457ef2ae8d, 0x2f6b0b730743397, 0xe2d3e16de0fe06ba, 0x3cdf35a634777323, 0xe4086d93dcff2f66, 0x5552e6a924430a68, 0x3721aa1c820e31e0, 0x8a1be17960348dd2]

private theorem rounds025_1 : sixRounds 6 (by decide) quarter025_1 = quarter025_2 := by
  decide +kernel

private def quarter025_3 : Vector UInt64 25 :=
  #v[0x6d6f2db4560d5692, 0xba36323658dcc08c, 0x83f12acd9df11802, 0x3fa8d39822d26e86, 0xa29141b3f82f09d1, 0x7b8387ef5495ca61, 0x640e5a052c8e844e, 0x3958e1036497259d, 0x46c1fd5f1656a21a, 0xe9e2df5f6ee2db27, 0x762b90cb188b9cd5, 0xeced490ceaf6ebba, 0x58aa74e1237439d3, 0xd03322950457fe3b, 0x396b71ae50fd042b, 0x7263061cd9f51d05, 0xc59da4e4bb3f2e3b, 0xfedd16e983e09906, 0x1ead40d68a3626ed, 0x9100138db12d908a, 0xf6a4263fc1ff5010, 0x59db045c48d68326, 0x56dd93d08cd4e204, 0xcc073e9c5e5b3b38, 0x7c45da7e34f9051a]

private theorem rounds025_2 : sixRounds 12 (by decide) quarter025_2 = quarter025_3 := by
  decide +kernel

private theorem rounds025_3 : sixRounds 18 (by decide) quarter025_3 = state026 := by
  decide +kernel

private theorem perm025 : KECCAK.f1600 absorbed025 = state026 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds025_0, rounds025_1, rounds025_2, rounds025_3]
  rfl

theorem block025 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes025 ++ tail) state025 =
      KECCAK.Bytes.run 0 tail state026 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes025 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb025 ws)) := by
    rfl
  exact (step state025).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words025).trans perm025))

private def absorb026 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0x73 0x50 0x5b 0xfd 0x80 0x0 0x60)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x91 0x16 0x81 0x35 0x81 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x16 0x91 0x90 0x35 0x1 0x81 0x20 0x60)) 5 (by decide) (UInt64.ofBytes 0x60 0x90 0x35 0x1 0x81 0x40 0x60 0x90)) 6 (by decide) (UInt64.ofBytes 0x81 0x80 0x60 0x90 0x35 0x1 0x81 0x60)) 7 (by decide) (UInt64.ofBytes 0x35 0x1 0x81 0xa0 0x60 0x90 0x35 0x1)) 8 (by decide) (UInt64.ofBytes 0x35 0x1 0x82 0xc0 0x60 0xff 0x60 0x90)) 9 (by decide) (UInt64.ofBytes 0x90 0x35 0x1 0x81 0xe0 0x60 0x90 0x16)) 10 (by decide) (UInt64.ofBytes 0xfe 0x38 0x61 0x35 0x1 0x0 0x1 0x61)) 11 (by decide) (UInt64.ofBytes 0x9b 0x3a 0x61 0x59 0x3 0x61 0x5b 0x56)) 12 (by decide) (UInt64.ofBytes 0x80 0x4 0x60 0xf0 0xd 0x61 0x5b 0x56)) 13 (by decide) (UInt64.ofBytes 0x61 0x15 0x10 0x81 0x40 0x60 0x3 0x36)) 14 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x80 0x0 0x60 0x57 0xcd 0xd)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x50)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed026 : Vector UInt64 25 :=
  #v[0x3f3b92da20b612ba, 0xea042919a11b0bbb, 0x511e21afaead601c, 0xad707ba7b283ec40, 0x3c78bc2ddd48b6b7, 0xe3594774a41296bc, 0xf22d9df1969b31eb, 0x370442a74623ce44, 0xe3b8b6db83bc60ba, 0x457531e49d5e2ce7, 0x4aa69564e6534a83, 0x5945d7794b41a645, 0x26e62b6970451494, 0x5d4e1d86deba5a33, 0x318597c2c18e7e1b, 0x290320aed9c9ba31, 0x9f91fc01450c837b, 0x10090169cb3e56bf, 0xd4f09e17096bb5d2, 0xa7c6a17581c3ac07, 0x4233628a6b06b814, 0xbc472f919117736a, 0x4aafe8db69643720, 0x65c6772f7879f243, 0x92fa079402dd3fe3]

private theorem words026 : absorb026 state026 = absorbed026 := by
  decide +kernel

private def quarter026_1 : Vector UInt64 25 :=
  #v[0xb728edbc13eb5879, 0x26e4bd3561dc2ba5, 0x8fc6152fad61bfde, 0x958985f80c1a5661, 0x1bd347ff92bd0e54, 0x494196ef92db805f, 0x9574f53647949a63, 0x2270e61cbda6e71b, 0xbe0cff63fa96858f, 0x87e35852535957d1, 0xf21af8a2b0c75f71, 0x9f8f52e2f11d7616, 0xb8ce7d30c07e542c, 0x1c9e0f1a9aae0fd9, 0x930fbc4c958ccea2, 0xe3a542ac05b27782, 0x6381cebb9da7f716, 0x34f6226666d04628, 0xb7984135f2d71f5, 0x3a2c7e69689ec11c, 0x62c95997145db1c2, 0x3d24b875e7181cf1, 0xfea0dc843f1acac1, 0xc7c548459cbeecdd, 0xb5c2ec62faf7fcc5]

private theorem rounds026_0 : sixRounds 0 (by decide) absorbed026 = quarter026_1 := by
  decide +kernel

private def quarter026_2 : Vector UInt64 25 :=
  #v[0x4468e919201404ce, 0x7abf51205483f932, 0x51aab9b3c415d29f, 0x9888579eb16f7f3, 0xe191fbdeecf5f270, 0x1c141121b2d00f9e, 0xa6580859985d2d10, 0x6979ea92601fbf46, 0x5f54f191f9b52f43, 0x65395044995cce35, 0x3f1c8d0f41f57f1c, 0x50fdc1bc8c0b4485, 0xca9605813e87d0d4, 0xfa14c12177799cb5, 0x7552a5cdf1afc2ce, 0x339264bbf2c234da, 0xee8a15ed6846710, 0x7840508aabf873ae, 0x2fc968201851e087, 0xc0e4a5b3aa60a3e6, 0xb9f52453f6acab4, 0xb33464235a789519, 0x88c4056e14ccba21, 0xdbe6a188ebfa4881, 0x740ce257ff34dc4d]

private theorem rounds026_1 : sixRounds 6 (by decide) quarter026_1 = quarter026_2 := by
  decide +kernel

private def quarter026_3 : Vector UInt64 25 :=
  #v[0x78ae72e753883403, 0x4329dba3cbe56b75, 0x2cfefd954ff5b4ac, 0xdf3fd1bb0684f3de, 0xab5541a1439c034c, 0xf51227babbdd6013, 0x15344db65d22080, 0x447cc7c15f909105, 0xed60a367febbed13, 0xb07cf7a3bdb4ac2d, 0x77aff380d46e1603, 0x7ecfc0ce43e148c9, 0x6107be665e7b54e8, 0xba048cd7a2d23e6f, 0x3b197f59b487ac95, 0x1208835642f617f8, 0x2057bae56c135307, 0xd03c94ba37c13fd1, 0x3adbff522aca772a, 0xffd5eca19e503374, 0x2d7447b561f96b9a, 0x9324de00ef1b6d15, 0x67c7f1dc86cfe190, 0x815b1de60e749a5, 0xfb1a3bca53a72b0]

private theorem rounds026_2 : sixRounds 12 (by decide) quarter026_2 = quarter026_3 := by
  decide +kernel

private theorem rounds026_3 : sixRounds 18 (by decide) quarter026_3 = state027 := by
  decide +kernel

private theorem perm026 : KECCAK.f1600 absorbed026 = state027 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds026_0, rounds026_1, rounds026_2, rounds026_3]
  rfl

theorem block026 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes026 ++ tail) state026 =
      KECCAK.Bytes.run 0 tail state027 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes026 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb026 ws)) := by
    rfl
  exact (step state026).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words026).trans perm026))

private def absorb027 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x35 0x81 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x3b 0x61 0x35 0x1 0x20 0x60 0x90 0x16)) 2 (by decide) (UInt64.ofBytes 0x82 0x80 0x51 0x40 0x60 0x5b 0x56 0x14)) 3 (by decide) (UInt64.ofBytes 0x0 0xe 0x61 0x15 0x11 0x81 0x2 0x60)) 4 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x5b 0xfe 0x57)) 5 (by decide) (UInt64.ofBytes 0x91 0x80 0x51 0x40 0x60 0x50 0x50 0x91)) 6 (by decide) (UInt64.ofBytes 0x60 0x70 0x4 0x61 0x5b 0xf3 0x90 0x3)) 7 (by decide) (UInt64.ofBytes 0x10 0x81 0x20 0x60 0x3 0x36 0x80 0x4)) 8 (by decide) (UInt64.ofBytes 0x80 0x0 0x60 0x57 0x27 0xe 0x61 0x15)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x35 0x50 0x5b 0xfd)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x61 0x5b 0x56 0x4c 0x3b 0x61 0x16 0xff)) 13 (by decide) (UInt64.ofBytes 0x60 0x3 0x36 0x80 0x4 0x60 0x70 0x4)) 14 (by decide) (UInt64.ofBytes 0x57 0x5a 0xe 0x61 0x15 0x10 0x81 0x20)) 15 (by decide) (UInt64.ofBytes 0x73 0x35 0x50 0x5b 0xfd 0x80 0x0 0x60)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed027 : Vector UInt64 25 :=
  #v[0x7602fecfe9dc093a, 0x71f19c4b45d76e02, 0x53648c8d72077add, 0x95ad336362e20e5f, 0xa5c88fd61f7b9f0c, 0xa5a47069e6c55f6f, 0x86ec4b80fff2c481, 0x9d7fa15360306c90, 0x5e769b75e62d2d05, 0x7ecec3c4eda7f1c7, 0x37eb09ffdd94d491, 0xfbc09dedd24b243e, 0xdbc5a8f887509bcd, 0xacbdbae040fe8d18, 0xe42ac3b79a399e53, 0xf7e47b2b46220b49, 0xe5f6fbc74168b21a, 0x11e535640b6994ef, 0xd08e1afc87725125, 0x9240e511f75fe943, 0x7dfede7b95babb50, 0x1fe7455d6bbd1be6, 0xd34a2cdc01cba586, 0xeacdb1b73e3b5f0c, 0x7bc626abecf1fdb7]

private theorem words027 : absorb027 state027 = absorbed027 := by
  decide +kernel

private def quarter027_1 : Vector UInt64 25 :=
  #v[0xb4820ca71a302976, 0x4f91fe188fe74ac0, 0x57f924fa8a07bd3d, 0x58e16da5c8ba8df6, 0x24a3b50ab8c820e5, 0x1945eb5b0d86dd07, 0x1d083230845dad2b, 0xabc6e912fcab5816, 0x84a21f6cfe497038, 0x3a3381644df8460c, 0x6d0daf785ef4b4d8, 0xab18d855e611461a, 0xaf5417cbe17292ea, 0xef03d2e813afad88, 0x942353083753ae61, 0x5be5c7e30ef52aec, 0xff1f880fd754bb4, 0xa22bad1c5cdc09ef, 0xae4dfadd78a6cad8, 0x1137b77b8f9a1c2c, 0x655a336f941a4573, 0xa9a4bf9c46f395fd, 0x69a6c67bc04ab51e, 0xa170370efa8ee2e5, 0x2e0cbd5a6b277bb1]

private theorem rounds027_0 : sixRounds 0 (by decide) absorbed027 = quarter027_1 := by
  decide +kernel

private def quarter027_2 : Vector UInt64 25 :=
  #v[0x73661797f7cfb7f, 0x7fae95b458112734, 0x89fabbf08bd9d2d, 0x23c78a9714a7533a, 0xee6b0daf47f26210, 0x32fc8e9fff7a84ac, 0xff4d41abc8ef4d8a, 0x3b1347e504ef0382, 0xefb18f30b65a906a, 0xb60381b22a80ed1d, 0x73bbe8b5d257ab07, 0xe3c9d212997deaae, 0x3655010567a5f4d2, 0xd5429bc9b09e12b4, 0xa508dcc978fd526f, 0x6cf3c7ee0d6a1db, 0x235f4c76c9f397cf, 0x7a5d21aaf54d8859, 0x27b828b845553cf9, 0xcbbb2030efe339c0, 0x6d288537c59c23a0, 0x43df965140ee472, 0xdc18e6b87504edc5, 0x5400ff8a070084e, 0x15105f88ecc419fa]

private theorem rounds027_1 : sixRounds 6 (by decide) quarter027_1 = quarter027_2 := by
  decide +kernel

private def quarter027_3 : Vector UInt64 25 :=
  #v[0xf2f4ee2ff1087310, 0x25c851733474e604, 0xdd78b6822e270c32, 0x460ab8aa10167a8c, 0x7fd1d949d4c867f0, 0xcfa30d0f9db05c35, 0x299c6039f8393372, 0xa2722ba3fe28d976, 0x5c020edec53522f7, 0xb996af914bab33ed, 0x93a088f46f5ad375, 0x3e074f7df2b2ae01, 0xf40257826e7a958c, 0xfa2070238a9e1181, 0x22bcf01ec5b7b861, 0x7e27e3031246f648, 0x7149b21cb4530bb8, 0x832da9539a2db2cb, 0x87e37749a6ee01bd, 0x7f739bddfed7e568, 0x4ef8f8f78c676fe3, 0xd5f091f8a403e324, 0x35431b0ce4277f38, 0x2b946d6298826d7e, 0xcca0459608ec397b]

private theorem rounds027_2 : sixRounds 12 (by decide) quarter027_2 = quarter027_3 := by
  decide +kernel

private theorem rounds027_3 : sixRounds 18 (by decide) quarter027_3 = state028 := by
  decide +kernel

private theorem perm027 : KECCAK.f1600 absorbed027 = state028 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds027_0, rounds027_1, rounds027_2, rounds027_3]
  rfl

theorem block027 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes027 ++ tail) state027 =
      KECCAK.Bytes.run 0 tail state028 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes027 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb027 ws)) := by
    rfl
  exact (step state027).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words027).trans perm027))

private def absorb028 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x9f 0x3c 0x61 0x16 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x80 0x4 0x60 0x7 0x4 0x61 0x5b 0x56)) 3 (by decide) (UInt64.ofBytes 0x61 0x15 0x10 0x81 0x20 0x60 0x3 0x36)) 4 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x80 0x0 0x60 0x57 0x8d 0xe)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x35 0x50)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x80 0x4 0x60 0x5b 0x56 0x86 0x3d 0x61)) 9 (by decide) (UInt64.ofBytes 0x60 0x20 0x60 0x51 0x80 0x40 0x60 0x54)) 10 (by decide) (UInt64.ofBytes 0x1 0x61 0x15 0x16 0x85 0x1 0x60 0x2)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x7f 0x2 0x0)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x93 0x16 0x94 0x90 0x1 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x84 0x1 0x81 0x1f 0x60 0x4 0x93 0x90))

private def absorbed028 : Vector UInt64 25 :=
  #v[0xdb47057dc584c741, 0x36026436ee487ac6, 0x76c5f54e3671b3fb, 0x192e018535d2313c, 0x5aaad756df416f63, 0x83ca52e8e5ea3c7d, 0xa2ec025f4c82956b, 0x6a5d92f4ddf64257, 0xceacc06da542b598, 0xb48543983bcbe67, 0xcf58b9b8aeca747a, 0x2c375b02980a8cf4, 0xd863ef61e967cd32, 0xb8069185308126ea, 0x6dddf98b8a5dc3b8, 0x562a9dfffcc4213b, 0x1dfa07f6aea0f679, 0x9dd9dbe69bc7f5a, 0xcb07dd0874c6f193, 0xb25aba65670ec8ac, 0x6a42157f5ad28abb, 0xaf6c1c90bc21878d, 0x6a97edb738482b83, 0x1705efff55cc4e2, 0x74ce4accb71bdcf4]

private theorem words028 : absorb028 state028 = absorbed028 := by
  decide +kernel

private def quarter028_1 : Vector UInt64 25 :=
  #v[0x825fb0c556e600a, 0xfcd0ce291ccb642, 0x58d8bbb9496db8eb, 0x744bc8bddbd5f764, 0x485069d96b185a94, 0x85545a165e3e0688, 0x6b55a633b1fe8ac3, 0x3167288e27928c1a, 0xc3dc9796a7539006, 0xa7599f098c7ff4da, 0x1e26073f96a5407d, 0x7c9b4e2d5870c6eb, 0x98d03aef22d4c92d, 0xfb21984dd29ef5e7, 0x546978f54139276f, 0x6f66f85c40876fb8, 0x238b57c76ca7e046, 0xed27905a1b896daf, 0xb2aa3e45167ce432, 0x1c0445b5adf39580, 0xfacbbbecb1077527, 0xb8b4f9d72dac196d, 0x7d6ec6c3380165ec, 0x26d9f1001350b81e, 0x7607dcfbc1bd35f5]

private theorem rounds028_0 : sixRounds 0 (by decide) absorbed028 = quarter028_1 := by
  decide +kernel

private def quarter028_2 : Vector UInt64 25 :=
  #v[0xc2c2427f49bd9591, 0xe5119506910f6e19, 0xf6ba7ff6a3e7df16, 0xaef42b951e99df1c, 0x351d992f382d9, 0xe65827b61bbebbc7, 0x5d2832c9cfd0c2b9, 0x314d7e707bd3857d, 0x7b102e289926b043, 0x494032e578952554, 0xd517be4dc5717b7a, 0xd76f5c863ad7955f, 0xe8d39ad9efb45c43, 0xde6a9b271c3d160, 0x3e85af69f414de15, 0x67876a197cd92f30, 0x16ccae2cd7580a1d, 0xcf2e3cf788a608f6, 0x7314b71a279a90ff, 0xf790aab248af101b, 0xc01f2888e11f6ef1, 0xa8d869bba7523d89, 0x681a876a5e3231e6, 0x4b62d8669f64ae05, 0xed8565fe27ea3d9d]

private theorem rounds028_1 : sixRounds 6 (by decide) quarter028_1 = quarter028_2 := by
  decide +kernel

private def quarter028_3 : Vector UInt64 25 :=
  #v[0xb6e099d022468ca5, 0x7c5237f668e10955, 0x3192c19c4fdd457, 0xc64d91ece4cb3534, 0x791e5efa7160bd1e, 0x311b60913c9cf19f, 0x506646a2a991a56e, 0xe9466e6a4441dac1, 0xba6b0896db07229f, 0x150c2cf29ddd4153, 0xc5f4fac63f000c2a, 0xa25c98941054006d, 0x1c68a8133d88e6f4, 0x22cf3f7cbfb5cb43, 0x9a08a0a884b07deb, 0xfdf1fb03ef8e136f, 0x2224b5bf4b05777d, 0x372615c4552d465c, 0x5604f7c0342bdefd, 0xee6d57a2ab3da7ca, 0x8c738b4dd69d4874, 0xe41ddf6306af7b45, 0x516d20f22ab81d5d, 0x8a427ee343e27707, 0x16e25a67218775fd]

private theorem rounds028_2 : sixRounds 12 (by decide) quarter028_2 = quarter028_3 := by
  decide +kernel

private theorem rounds028_3 : sixRounds 18 (by decide) quarter028_3 = state029 := by
  decide +kernel

private theorem perm028 : KECCAK.f1600 absorbed028 = state029 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds028_0, rounds028_1, rounds028_2, rounds028_3]
  rfl

theorem block028 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes028 ++ tail) state028 =
      KECCAK.Bytes.run 0 tail state029 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes028 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb028 ws)) := by
    rfl
  exact (step state028).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words028).trans perm028))

private def absorb029 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x1 0x84 0x1 0x82 0x2 0x84 0x4 0x90)) 1 (by decide) (UInt64.ofBytes 0x91 0x92 0x52 0x81 0x81 0x52 0x92 0x90)) 2 (by decide) (UInt64.ofBytes 0xf 0x61 0x15 0x80 0x82 0x82 0x1 0x83)) 3 (by decide) (UInt64.ofBytes 0xf 0x61 0x10 0x1f 0x60 0x80 0x57 0x4e)) 4 (by decide) (UInt64.ofBytes 0x54 0x83 0x80 0x0 0x1 0x61 0x57 0x23)) 5 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x91 0x52 0x83 0x2 0x4)) 6 (by decide) (UInt64.ofBytes 0x1 0x82 0x5b 0x56 0x4e 0xf 0x61 0x91)) 7 (by decide) (UInt64.ofBytes 0x60 0x20 0x60 0x52 0x0 0x60 0x90 0x91)) 8 (by decide) (UInt64.ofBytes 0x52 0x81 0x54 0x81 0x5b 0x90 0x20 0x0)) 9 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x90 0x1 0x1 0x60 0x90)) 10 (by decide) (UInt64.ofBytes 0x82 0x57 0x31 0xf 0x61 0x11 0x83 0x80)) 11 (by decide) (UInt64.ofBytes 0x91 0x1 0x82 0x16 0x1f 0x60 0x3 0x90)) 12 (by decide) (UInt64.ofBytes 0x56 0x81 0x50 0x50 0x50 0x50 0x50 0x5b)) 13 (by decide) (UInt64.ofBytes 0x74 0x90 0x0 0x60 0x54 0x1 0x60 0x5b)) 14 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x1)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 16 (by decide) (UInt64.ofBytes 0x60 0x4 0x90 0x0 0x0 0x0 0x0 0x0))

private def absorbed029 : Vector UInt64 25 :=
  #v[0xd9771f8bde7af883, 0x4a2946351d88c8ba, 0x32542b733c553535, 0xe07ada9a50bef46f, 0xba9fc1402a333010, 0x89b0800befe24db8, 0x977126916b3f2d5, 0x18f705a1ec7e3b1, 0x8a978b547fa68f33, 0x3c6a305ad12de01a, 0x77e1ed526c18dade, 0xc76cb2e96b6f8c5b, 0x88b98b7d40902c07, 0x536dcba5a1a6b69f, 0x9942316824ab34b2, 0xcbc15dd859a215d8, 0xd6d87817001cabd0, 0x3dc378735753420a, 0xc169752aa5398daa, 0x8638c6ea31e45b27, 0x7fa571cb24aafb25, 0xfdf65a2859cf07ec, 0x681484e85ab93e69, 0xb978cc1441c2d8ae, 0x65ff652ec7c174f9]

private theorem words029 : absorb029 state029 = absorbed029 := by
  decide +kernel

private def quarter029_1 : Vector UInt64 25 :=
  #v[0x3d09ec6bf993bc2e, 0xe1fdbeaae7a50b28, 0xa8ae3f89ce37bc76, 0x30b42e8f2d97825d, 0xd08795ca05e422a4, 0x36df0c2d06d66021, 0xf403c5f0a92eade9, 0xf31d539ef2be28af, 0xed043466061b8ed6, 0xcabefdf90e2f8dd0, 0x66916b5f01fc3387, 0x28d6611e443addfc, 0xf0401746269bf6a8, 0xd4299ec61d6723f1, 0xab748aa92bb82147, 0x9b23a0fd38c6c8ad, 0xcac292a81137ba3b, 0xb1f977db12c95839, 0x71c31602662dfe9c, 0xfdd1743f0d5663fc, 0x860810af6ab26565, 0x77b0961d4d804ed9, 0xfb8cd8c81ad10354, 0x5758a79d98b199e1, 0xfc16c7bd2286d499]

private theorem rounds029_0 : sixRounds 0 (by decide) absorbed029 = quarter029_1 := by
  decide +kernel

private def quarter029_2 : Vector UInt64 25 :=
  #v[0xe8703a44287a003e, 0x3744a1ad1901d6db, 0xb9267ffe567f66, 0x69d0c67fa8e7f9df, 0x7a2b79e0c1f1494c, 0xf29445c88057e7ea, 0x8f04f8f6dec9d75b, 0xaa1425166b2f8a87, 0x8b8024b0af3c35d8, 0xfd725ae10dfea06b, 0xa7d24e64d66d956a, 0xdee88975cb34317f, 0x5ea6436971d171e1, 0x3617cc2f28fc7d55, 0x6cac76f30dc5fbcb, 0x217ca152ab6893e8, 0xdc1db3e0e3184472, 0xebf39c368b4acc84, 0x4a02ec97d0fa2de2, 0x2b4eb62b2ff88383, 0xcdfcc2950bbcf7b7, 0xec5242287cb4fd9d, 0x7f1fea3d69d0ba0d, 0x54f868b8f1cdc96f, 0xf440575bf85457d1]

private theorem rounds029_1 : sixRounds 6 (by decide) quarter029_1 = quarter029_2 := by
  decide +kernel

private def quarter029_3 : Vector UInt64 25 :=
  #v[0xd8b7b62d51c702e5, 0x65f4e7fa7e6f2aab, 0x1f2f74e5429b14bd, 0x4f619a12152adb0c, 0x65ac4413719164de, 0x8ead81893dde1380, 0x7b9aff7ed3c6bf87, 0xb8d099ea34666f5a, 0xc42d561489405cff, 0x52946dd56aa3cb6a, 0xed5aa239282573d1, 0xf54dc41a99fb36a0, 0x8b83d50f382c447a, 0xd061bafd15d293dc, 0xc0be24c38e427128, 0xd855d72c99ab6842, 0x96f1c5e7af8f91f0, 0x15600d96322d369, 0xba8a1a467fc801c4, 0xd2ff17d3e769ec1f, 0xcc0b58e31462f60f, 0xe6a13049fc62a8d7, 0x267c2b3a80724de2, 0xd6b1243dff88ab54, 0xbbd44468062bbff6]

private theorem rounds029_2 : sixRounds 12 (by decide) quarter029_2 = quarter029_3 := by
  decide +kernel

private theorem rounds029_3 : sixRounds 18 (by decide) quarter029_3 = state030 := by
  decide +kernel

private theorem perm029 : KECCAK.f1600 absorbed029 = state030 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds029_0, rounds029_1, rounds029_2, rounds029_3]
  rfl

theorem block029 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes029 ++ tail) state029 =
      KECCAK.Bytes.run 0 tail state030 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes029 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb029 ws)) := by
    rfl
  exact (step state029).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words029).trans perm029))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
