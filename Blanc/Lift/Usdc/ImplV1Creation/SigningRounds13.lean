import Blanc.Lift.Usdc.ImplV1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb78 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x50 0xa2 0x90 0x3 0x91 0x80 0x51 0x40)) 1 (by decide) (UInt64.ofBytes 0x0 0x60 0xc 0x60 0x0 0x60 0x5b 0x56)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x83)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x73 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x16 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x90 0x1 0x20)) 9 (by decide) (UInt64.ofBytes 0x90 0x54 0x90 0x0 0x60 0x20 0x0 0x60)) 10 (by decide) (UInt64.ofBytes 0xff 0x60 0x4 0x90 0xa 0x0 0x1 0x61)) 11 (by decide) (UInt64.ofBytes 0x5b 0x56 0x50 0x90 0x91 0x50 0x90 0x16)) 12 (by decide) (UInt64.ofBytes 0x5b 0x56 0xbe 0x23 0x61 0x32 0x29 0x61)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x73 0x33 0x16 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed78 : Vector UInt64 25 :=
  #v[0x7726d89c3da70506, 0x34c8a8e563b8764c, 0x5c09e9d941add3e8, 0x4e6e4a45e0dbcbcb, 0xa34ad9ef202c8c2e, 0xd970b8a998e99f34, 0xe6e4b662315246a9, 0x8e98e593fc504f84, 0xf92c8e682aa7c35f, 0xb0e391eeaab3f29, 0xe67e603966bc7c10, 0x314d662b8622145a, 0x33deb76526a96034, 0xdfeb851aa812daea, 0x39bc1084cf798b8, 0xf999003e9b2632f3, 0xcea336c2d3222685, 0x4212d09b7eca2d03, 0xe64380467b9d797a, 0xccd28270607c9374, 0x1afafa7243f90ab5, 0x69be487deb5135d7, 0xe0ba49ea5206ce9c, 0xeba134338fbfbc96, 0x6a133e4aa758709e]

private theorem words78 : absorb78 state78 = absorbed78 := by
  decide +kernel

private def quarter78_1 : Vector UInt64 25 :=
  #v[0xa257ee0d0fcbc215, 0xb2eb1933ca35b9bd, 0x5427595a8642027b, 0x6db786fd55732516, 0xbf86a15161b44772, 0xa8e037975a10e644, 0xf9b93f08733b5f8f, 0xf1d6a92fd1d2140f, 0xa341d5ccf75605b0, 0xbf09341375b05a19, 0xb3b074106df13c22, 0xbb0c681eb932db7, 0xa6aca0d3f3868468, 0x763af359fcb9c98e, 0xb1fb88dabd2b8c5c, 0xc25468f519b1ddfb, 0xa1bfd47e2c407e9e, 0x1329199831ea9ac1, 0x60c4c6b08df4bf4e, 0xfb415a0f70161769, 0x241c807b84a5ae95, 0xb8a1998f84dc159a, 0x62a830384c6cb9d7, 0xe1235f674b4c47, 0xacfbe482b3b0264a]

private theorem rounds78_0 : sixRounds 0 (by decide) absorbed78 = quarter78_1 := by
  decide +kernel

private def quarter78_2 : Vector UInt64 25 :=
  #v[0xc29053e5f6d39589, 0x1eb43617de595967, 0x51ae7ba833bd6666, 0x19835661f5717ce3, 0xf8c1a6755d546c06, 0xd368d70e79c9a4de, 0x4fb1244fb4673c96, 0xb2f374a324f35dc8, 0x6ebd13962e425c88, 0x1778cca07ce4bd7c, 0x3fd84673da803564, 0x34b272b5a0694d54, 0xc1fc6e78e4e43ff6, 0xab63594cd1bee674, 0x5017d500b6f9a4d2, 0x3dc0e7ea3a2d5e31, 0x39a15a3a904c31b3, 0x8bccb3f94f723d60, 0x9d5ba09abc3f0e7a, 0x4f7573a7f50d7d77, 0x646533469fb58100, 0xa7676cf9d82827de, 0x1db10bc4c0fb31b2, 0x86679e7a43b5305c, 0xd8c852d6c62f8ba4]

private theorem rounds78_1 : sixRounds 6 (by decide) quarter78_1 = quarter78_2 := by
  decide +kernel

private def quarter78_3 : Vector UInt64 25 :=
  #v[0x611dcfda287d73d3, 0xf70239ede3943433, 0xd43cc756603c5a32, 0x7048dd4f64507910, 0x3b25aa61828a8859, 0xeb138eff0a6a3407, 0xb0bc1b4cee99ff07, 0x5776e58ccf99dc92, 0x49369920224f6cf3, 0x474c93a4014ad576, 0xeccbb0a9eb3c0f2a, 0x8364c0926aa1157e, 0x5f1b372cf977a397, 0x81bc471b689a770f, 0xd9a62b1fb62faf8e, 0xeee8aa6c43a2a2b1, 0x702c5528c3dd9717, 0xac0c21233b8b1450, 0x771f12fe9671d97f, 0x7521509e5543f881, 0xebf32e70b972ddf0, 0x8fc5733ceeb69b2f, 0xaeee7338d2ea9b78, 0x2f5c741da6b3117b, 0x80cea51b8e880b84]

private theorem rounds78_2 : sixRounds 12 (by decide) quarter78_2 = quarter78_3 := by
  decide +kernel

private theorem rounds78_3 : sixRounds 18 (by decide) quarter78_3 = state79 := by
  decide +kernel

private theorem perm78 : KECCAK.f1600 absorbed78 = state79 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds78_0, rounds78_1, rounds78_2, rounds78_3]
  rfl

theorem block78 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes78 ++ tail) state78 =
      KECCAK.Bytes.run 0 tail state79 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes78 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb78 ws)) := by
    rfl
  exact (step state78).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words78).trans perm78))

private def absorb79 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x15 0x15 0x14 0x16 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xfd 0x80 0x0 0x60 0x57 0x6b 0x29 0x61)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x0 0x60 0x5b)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x81 0x16)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x57 0xa7 0x29 0x61 0x15 0x15 0x15 0x14)) 10 (by decide) (UInt64.ofBytes 0x2 0x60 0x80 0x5b 0xfd 0x80 0x0 0x60)) 11 (by decide) (UInt64.ofBytes 0x54 0x81 0xa 0x0 0x1 0x61 0x0 0x60)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x81)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x19 0x2 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x83 0x90 0x16)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed79 : Vector UInt64 25 :=
  #v[0xa442dd9ccee93ab3, 0x690062c7ee3e0f88, 0x79bcb67a405142b7, 0x1a4e789254ffb3b3, 0xfae2f7bd7c37da3a, 0xdd104419187fcc5, 0xbf8e2b8fb44124b3, 0xa30f378fc14fd269, 0x696b9c3110908fc1, 0x25e937d0178e32a3, 0x14eaefa11ad8d1ef, 0xe2b321d16666a1e8, 0x3e080b6c09a716f9, 0xa39dc5a51cd0e60e, 0x1138dc5c96a101b3, 0xf7ca2f19dbd1f3cf, 0x36ab23822bd3fd2f, 0xaf000c9ead8ea41e, 0x8dfc5842071b1be8, 0xda3485138de8abc1, 0x7aa23302b1f9cad, 0x621c01ca95407f46, 0x438b7a9860ee8b84, 0xc0974f9ec4c85976, 0x96558da6a486f76d]

private theorem words79 : absorb79 state79 = absorbed79 := by
  decide +kernel

private def quarter79_1 : Vector UInt64 25 :=
  #v[0x2fae0f4fa446dd5d, 0x130fd5e63f6f67fd, 0xa292d4426864c0bb, 0x67ec673bf6097429, 0x361acad6540dca01, 0xb3db9e2dde7dc94a, 0xde2d31d803f8f6d0, 0x3f3ebee17089ac19, 0x6913ed01b7ee0f1b, 0xc137237c04ea6d, 0xef3809484bb2ed3c, 0x88360f299d500b14, 0xa8c5f3d86f95d7a2, 0x523b1372a4be6ebe, 0xec487160399e8e5d, 0x67513e2a29ccfa0a, 0xe317e2636c66fdbb, 0x31af53d238115789, 0x2f347ebc9664f7a1, 0xe97502e451c3b844, 0xbcb2334c806c5b, 0x59e1b7352a3de87b, 0x5946258f99c05eb7, 0x629cdcb206434eb3, 0xd36c960751edafd5]

private theorem rounds79_0 : sixRounds 0 (by decide) absorbed79 = quarter79_1 := by
  decide +kernel

private def quarter79_2 : Vector UInt64 25 :=
  #v[0xed40ee2d59a6a72b, 0x9d571ce0f77da378, 0x63be0a05eb064778, 0xa2be739a45e2c7b0, 0x683237776009e824, 0xe715c73092a181a5, 0x610a6dd4a8d414bc, 0xd3f12544dd1aefa0, 0xd23d1dff5c6e7620, 0x7363ef672d3bdad1, 0x2d18e3535ad5192c, 0x8bce3b6e4e29278f, 0xa09f7b7584ef607c, 0x6be393e43a48004d, 0x90e85316d99cf33d, 0x47273e038b1f3592, 0x93c2a10d6374ad1c, 0x93b1d8609ca8dac1, 0xb1659496998d7ae1, 0x461abdaf5aa721ab, 0xd1a7cd877db49059, 0x480631707fed57ea, 0x4b54dc729843aba8, 0xa262dcf12ca55e67, 0x241acd5952f60cf6]

private theorem rounds79_1 : sixRounds 6 (by decide) quarter79_1 = quarter79_2 := by
  decide +kernel

private def quarter79_3 : Vector UInt64 25 :=
  #v[0x1a70d81e348c2c0c, 0xe7e722782cb67e1a, 0x1419339263c10640, 0x5ebd3fa2e2f16db7, 0x152359f99d5844bd, 0x9706593b972d319a, 0x1329f23c3f3962a0, 0xabbd22d0ebcb01e7, 0x63433846fa566f0, 0x18da41913876101c, 0x27bd27d8f43e7ce4, 0x2aa93dbb00b2cd37, 0xf36ffb1f9f7a555d, 0xd37fb8b6b5b1ef3, 0xff0ec499cee46213, 0x392f70cebe34de16, 0x87a965b5f2fab2e4, 0xba29b40818026f32, 0xcbeb32bc00dafba7, 0x1905b50b33f60594, 0xf509b3bc62f7ae45, 0xc1eb7f8b8a2e9ec7, 0x7b99704bc71ea5cd, 0xb281da37b259ad2f, 0xd6a5a780a8528afb]

private theorem rounds79_2 : sixRounds 12 (by decide) quarter79_2 = quarter79_3 := by
  decide +kernel

private theorem rounds79_3 : sixRounds 18 (by decide) quarter79_3 = state80 := by
  decide +kernel

private theorem perm79 : KECCAK.f1600 absorbed79 = state80 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds79_0, rounds79_1, rounds79_2, rounds79_3]
  rfl

theorem block79 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes79 ++ tail) state79 =
      KECCAK.Bytes.run 0 tail state80 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes79 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb79 ws)) := by
    rfl
  exact (step state79).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words79).trans perm79))

private def absorb80 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x2 0x60 0x50 0x55 0x90 0x17 0x2 0x16)) 2 (by decide) (UInt64.ofBytes 0x0 0x1 0x61 0x90 0x54 0x90 0x0 0x60)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x4 0x90 0xa)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x16)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x7f 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xe9 0x1c 0x11 0x2c 0x1 0x98 0x73 0xc6)) 10 (by decide) (UInt64.ofBytes 0x6c 0x9 0x33 0xb9 0x29 0x74 0xcb 0x5e)) 11 (by decide) (UInt64.ofBytes 0x75 0x11 0x42 0x6c 0xee 0x80 0x73 0x97)) 12 (by decide) (UInt64.ofBytes 0x6e 0xc0 0x88 0x6c 0x4c 0x4a 0x1a 0xa7)) 13 (by decide) (UInt64.ofBytes 0x91 0x80 0x51 0x40 0x60 0x51 0x40 0x60)) 14 (by decide) (UInt64.ofBytes 0x2 0x60 0x5b 0x56 0x50 0xa2 0x90 0x3)) 15 (by decide) (UInt64.ofBytes 0x0 0x1 0x61 0x90 0x54 0x90 0x0 0x60)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x4 0x90 0xa))

private def absorbed80 : Vector UInt64 25 :=
  #v[0x3966eb699e97d62, 0x42a423cd11e7250, 0x9d9ef9556f030657, 0x5c224125d2713d7, 0x646bcc8d2a9f320, 0x8da60ce8ea57d0be, 0x3edc4d1f0df2fddb, 0x5e8e372c12c2af93, 0x4c0bfdfd37344163, 0x7a693fdda6f04e7, 0xfe78fe355c9397ee, 0x99027aa8ba0511f4, 0x56fa05018ab7f190, 0x2a50ec7eb2757261, 0x30ff798e3ffc4359, 0xc85e393cfa192fbd, 0xe0bf04b210a6c1dd, 0xd9c4c7753172ad2c, 0xa1c8952464d50249, 0x30449c8e0c16c492, 0x22d31d2b88abd4a9, 0x8fe468026d3a1b0d, 0x47a99109cf702afa, 0xd66af06830d1da6e, 0x21b846520d61fae8]

private theorem words80 : absorb80 state80 = absorbed80 := by
  decide +kernel

private def quarter80_1 : Vector UInt64 25 :=
  #v[0x4075ad41f85e5c99, 0x377e17fc3d478168, 0xbf4aaceb263c9295, 0xef9da082ad3a07d0, 0x31d3173b418a3a9, 0x2fb60a4b5e916e8f, 0xd3e7770f16dc5dee, 0xdf0e6abf5a64ef3f, 0xa916832a077868ca, 0x77decd2c9acec57a, 0x9ff17b2e12d207af, 0xa3601d1822f7aea7, 0x97ba57dfe89ade47, 0x1b3f286af68a8814, 0xdbf808a6f6bf6afe, 0x628b700bcc245986, 0xc394d265527f1159, 0xe6beff29528d4a5b, 0xf6077415d9ea2be7, 0x4dba9ea9496f2598, 0x40e58715622ed51e, 0x4a7d4c4679836d5f, 0x3de3cee21b079d67, 0xddade9fca2cf7b66, 0x6409b738065a6e03]

private theorem rounds80_0 : sixRounds 0 (by decide) absorbed80 = quarter80_1 := by
  decide +kernel

private def quarter80_2 : Vector UInt64 25 :=
  #v[0x156c1de3ac5dd2e8, 0xc1f07065e7cb1911, 0x3a913db906178573, 0xd6f0d61e050d9539, 0x11c7d4e7c7b3ca31, 0xa69e6ed6845becb, 0x68fc3b8315556a15, 0x78b47bfdec349693, 0x330d6558b7546441, 0x781400bbe145fdb8, 0xd5077bcf36274d1f, 0xd62e92ab02826ad5, 0xaba13de53e16ddbf, 0x54916d63f93e7466, 0xb0167453a2658546, 0xb5639ec85619fff4, 0x2b3fe16600777ef5, 0xea7080d94fb21025, 0xa803039174f652cc, 0x6541ce3dccaaf6a1, 0x2237446cda6a0206, 0x856ee57098c6c08c, 0x369ead4abd8e734, 0x6e6db8172243e081, 0x7ed0a0b393ec6781]

private theorem rounds80_1 : sixRounds 6 (by decide) quarter80_1 = quarter80_2 := by
  decide +kernel

private def quarter80_3 : Vector UInt64 25 :=
  #v[0xfeba415ac6cd10e, 0x2aca2a95f079033f, 0xe9feb2c9d1c67110, 0xace367e2086ebe5, 0xd55611edebf6af6f, 0x10a746645300f3f2, 0xab65d1ed039553a5, 0xbafd24aa2de3ee2a, 0x28a853380c5c2123, 0xe46862c182358141, 0xaa3bce46c4a066d5, 0x990afd877a45d6c1, 0xc2c498f08c10c0b8, 0x132300783e125b6f, 0xb48579dc99815c3c, 0x8c1352b4e6712581, 0xa17390b676d84170, 0x7429d48386acb28b, 0xfe65536bf88492cd, 0xcc9e29a511a0502a, 0x462a4441a7a3088a, 0xdf678d84a19d6d5a, 0xaf184a85fa8fece1, 0xdb6dc3c18112a203, 0x373f981159b9cb16]

private theorem rounds80_2 : sixRounds 12 (by decide) quarter80_2 = quarter80_3 := by
  decide +kernel

private theorem rounds80_3 : sixRounds 18 (by decide) quarter80_3 = state81 := by
  decide +kernel

private theorem perm80 : KECCAK.f1600 absorbed80 = state81 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds80_0, rounds80_1, rounds80_2, rounds80_3]
  rfl

theorem block80 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes80 ++ tail) state80 =
      KECCAK.Bytes.run 0 tail state81 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes80 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb80 ws)) := by
    rfl
  exact (step state80).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words80).trans perm80))

private def absorb81 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xa 0x60 0x0 0x60 0x5b 0x56 0x81 0x16)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x84 0x0 0x60)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x16)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x81 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x90 0x1 0x20 0x60 0x52)) 10 (by decide) (UInt64.ofBytes 0x83 0x0 0x60 0x20 0x0 0x60 0x1 0x20)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xff 0x73 0x16 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x16 0xff 0xff 0xff))

private def absorbed81 : Vector UInt64 25 :=
  #v[0x8176a54143987057, 0x17cfec10f8b8bf82, 0x440a30c22b096e09, 0xcf632a7c7f7738a1, 0x3733d419b5209266, 0xdcc2b807888994f7, 0x2346aa9b101449d2, 0x93ce21f23621aed0, 0xbc8bd9368448d933, 0x2f3e0a3aa3a0b799, 0xbbe1855dead0bb09, 0xf27fd9792de02b31, 0xad810abcbb1c29b9, 0x247c6b042958c7d3, 0xb79767f6add5c159, 0xd4a6e833a022e837, 0x6877138cccc81cd, 0xe4f0cc08d57ff6c, 0x3775e244c471658f, 0xf82c8971ec4f287e, 0x603dcab063d6da89, 0x29cc4f32b56534ec, 0x60a22bb9de01bfd8, 0xe87b97e237a64f3a, 0xe10671aeaeb3aa6f]

private theorem words81 : absorb81 state81 = absorbed81 := by
  decide +kernel

private def quarter81_1 : Vector UInt64 25 :=
  #v[0xb4bdd96387a0ac8d, 0x6a188461999cf535, 0xec29074d0e753a0b, 0xb864e0af191900e9, 0x19239be632250112, 0x4259f57db33cb2cd, 0x85b498129e8db0e, 0x83a681f20405c540, 0x74ee630898d113b9, 0x3a9f6ce4a8a0f1d2, 0xce161221c5cdd81, 0x13757cdc73e1184e, 0xfd42fa000f420f02, 0x385584f2f86ab59e, 0xd19fb54aec56bd07, 0x6456a2737cc972aa, 0x91b769eea97d3dac, 0x46f8c065c2b175d3, 0x9fd3e7eaeeed09fe, 0xb33f4080cbe815d4, 0x110bcb6b4622a2ef, 0x59f2e940921bea28, 0x8270fdebfe4356c4, 0x54af554157d8656f, 0x9c0808f9bc9abdac]

private theorem rounds81_0 : sixRounds 0 (by decide) absorbed81 = quarter81_1 := by
  decide +kernel

private def quarter81_2 : Vector UInt64 25 :=
  #v[0x60a4330c734a83ba, 0xccade6b386d11817, 0xbc16405c9b9daee2, 0x63b5cbb9f6d331bb, 0x9aa65c960b1ae782, 0xcb1956b12761df79, 0x4ac938c9d582d9b1, 0x17abd0f06545e3f1, 0x4f1326152d70c9b, 0xe688952328c08b92, 0xf254013194d5a1ee, 0x5529ee838158c978, 0x1d94fd190f74e80a, 0x5dd8ceb726e32b84, 0x387d6cfef02ece8e, 0x41207602f63b58ba, 0x6281d8d743b68d4, 0x2f1175cc09445cd2, 0x5c62ad8908e2cbd5, 0xab2cadf08438bb5c, 0x70afe877012a8240, 0x875a1eba670d2d7f, 0xc2f76141263aebec, 0xe275726132b1c8a7, 0x9b05aaecb6b0fc5d]

private theorem rounds81_1 : sixRounds 6 (by decide) quarter81_1 = quarter81_2 := by
  decide +kernel

private def quarter81_3 : Vector UInt64 25 :=
  #v[0x5a901feea7fc7f71, 0xb0d9e3c32a4a8fde, 0xebeaa9b44ae145c, 0xa268eea557ae43ee, 0x39a38eee3449c88e, 0x675a2de9436a769a, 0xbb9a7583d4a65555, 0x5abd120ca9cfe9f6, 0x30e3ffb73559a922, 0xf783cded48b36298, 0x153638cf0ee868b1, 0xab0139aa7688a91, 0xce646f386b1f8261, 0xd29532985546fdd5, 0xf26def1f288cf1fe, 0x991a4928d089a751, 0x3de0fac18bb6a1a1, 0x808d2a6341093f53, 0x4cd660d20a588121, 0xaa62b3578d150aff, 0xbe45f6817ebe8c92, 0xf28776f9f0af7bf2, 0x836a3a47d68a57b6, 0x494677642066aa60, 0xf4a3cba115ab6c3c]

private theorem rounds81_2 : sixRounds 12 (by decide) quarter81_2 = quarter81_3 := by
  decide +kernel

private theorem rounds81_3 : sixRounds 18 (by decide) quarter81_3 = state82 := by
  decide +kernel

private theorem perm81 : KECCAK.f1600 absorbed81 = state82 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds81_0, rounds81_1, rounds81_2, rounds81_3]
  rfl

theorem block81 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes81 ++ tail) state81 =
      KECCAK.Bytes.run 0 tail state82 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes81 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb81 ws)) := by
    rfl
  exact (step state81).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words81).trans perm81))

private def absorb82 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x60 0x1 0x20 0x60 0x52 0x81 0x90 0x1)) 1 (by decide) (UInt64.ofBytes 0x50 0x91 0x92 0x50 0x90 0x54 0x20 0x0)) 2 (by decide) (UInt64.ofBytes 0x60 0x54 0x80 0x7 0x60 0x5b 0x56 0x50)) 3 (by decide) (UInt64.ofBytes 0x1 0x61 0x15 0x16 0x1 0x60 0x81 0x1)) 4 (by decide) (UInt64.ofBytes 0x4 0x90 0x2 0x60 0x16 0x3 0x2 0x0)) 5 (by decide) (UInt64.ofBytes 0x91 0x80 0x20 0x60 0x1 0x1f 0x60 0x80)) 6 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x1 0x20 0x60 0x2 0x4)) 7 (by decide) (UInt64.ofBytes 0x92 0x80 0x52 0x40 0x60 0x1 0x81 0x90)) 8 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x81 0x90 0x91)) 9 (by decide) (UInt64.ofBytes 0x1 0x60 0x81 0x1 0x60 0x54 0x80 0x82)) 10 (by decide) (UInt64.ofBytes 0x16 0x3 0x2 0x0 0x1 0x61 0x15 0x16)) 11 (by decide) (UInt64.ofBytes 0x2b 0x61 0x15 0x80 0x4 0x90 0x2 0x60)) 12 (by decide) (UInt64.ofBytes 0x2b 0x61 0x10 0x1f 0x60 0x80 0x57 0x93)) 13 (by decide) (UInt64.ofBytes 0x54 0x83 0x80 0x0 0x1 0x61 0x57 0x68)) 14 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x91 0x52 0x83 0x2 0x4)) 15 (by decide) (UInt64.ofBytes 0x1 0x82 0x5b 0x56 0x93 0x2b 0x61 0x91)) 16 (by decide) (UInt64.ofBytes 0x60 0x20 0x60 0x52 0x0 0x60 0x90 0x91))

private def absorbed82 : Vector UInt64 25 :=
  #v[0xa3d3a39db7fb8a2e, 0xfb3f3f1648350935, 0x84463f68de8db51, 0xbdf93f30ddb13a9c, 0x435eb47b0bfd0689, 0x97ea7e6dd9303e43, 0x2b56cdf41e47dd0c, 0x5619ed1774223256, 0x6c3adda6e97456a8, 0x1284aaf30612b9e5, 0xc5781086dfb37486, 0x22ac1d5a73607702, 0xd67e7ee69f8b4bd2, 0x8870d47f3c46f922, 0xec9242150a197a11, 0x33737216c792b6b8, 0x2a2f8f859bbbf699, 0x94736cece016c958, 0xff4f4332229d48b0, 0x1549824185b763e8, 0xe557e06c7e51edb9, 0xd76e6e828e4e3376, 0x23c1340e0e9f67db, 0xe692d4f13d1b04bb, 0x1dc7f6c3b3ccf770]

private theorem words82 : absorb82 state82 = absorbed82 := by
  decide +kernel

private def quarter82_1 : Vector UInt64 25 :=
  #v[0x2a1bed9f8a77dc1b, 0x1920651dedef20f7, 0x2ca7d2e75abc09cb, 0xf35bbbb0b3cc3853, 0xc768cb13f1d83310, 0x59246b3a3c0b69f0, 0x37328fec0e0ef854, 0x69f8260af9ca33fa, 0x986455d6ff4f69f9, 0xca3ba64d271835d9, 0x56af56a25b3f48b8, 0xe63ff8e453290c12, 0x41afec10ae9ff4d2, 0xcae57f5493f356f5, 0xb7e1a90afb6f3315, 0x1e4c69fa3707460, 0x55ad16beb8349a37, 0x8e8cc11375de75c7, 0xce7d80516456e793, 0xca80420e8c057e45, 0xa9df856a78837249, 0x3e36b825ec8e18dd, 0x51867e11cad169c3, 0xf3146b5bb9e5773a, 0x34fedbe0191b1c61]

private theorem rounds82_0 : sixRounds 0 (by decide) absorbed82 = quarter82_1 := by
  decide +kernel

private def quarter82_2 : Vector UInt64 25 :=
  #v[0x640c7fdea132c, 0xc6391aa58d946533, 0xbe95763c4b0eb2e6, 0xb7823f5c668d7dd0, 0x973d4e07d9eef67b, 0xc3016db959ff6be1, 0x52f451b58112e92e, 0xd9b4bc8611d6161, 0x3db9e47e35bed1bb, 0xcc9c3e19400e64d9, 0x77212506ba5ca26c, 0x1f32cd60d1a0dfaa, 0xc4ec2765c0a75975, 0xc70ad3cd1a4fc95, 0x6ce4a4f77020b86f, 0x60274ab08944bc, 0xacd0662ce4c3f891, 0x1ee023893305fba8, 0x8b5e86a2d0f960ec, 0x301441824f0e5c76, 0x277bb49e31b55bdc, 0xe7b29e6fac2d4ffc, 0xcae6aa143cc01e48, 0x1f706afbb57592b8, 0x800e25ea13c69565]

private theorem rounds82_1 : sixRounds 6 (by decide) quarter82_1 = quarter82_2 := by
  decide +kernel

private def quarter82_3 : Vector UInt64 25 :=
  #v[0xbf5cf748b5130a01, 0x8d06f2f249cfaacb, 0x4bbea86f2145fb37, 0x179b11564a418146, 0xd457af7d88309b82, 0xb48d8f1fe543ad98, 0x58e245dcd470a714, 0xa232887bc27c1cf9, 0x7503d74383d3fc32, 0xd82e66a03a4576f7, 0x723a598060afbef7, 0x1e31bd4a47c7768a, 0xce321d8a61482b6, 0xdc194a534a71431f, 0xa4ebaa6470ab7764, 0x5bcf791793365f5c, 0x3b3d75501166e28d, 0x9d649e443c03a572, 0xaa97bed38b306a76, 0xd9fe297d8b29be8c, 0x8df01d039e73a332, 0xe8cf797b88f16e3f, 0xbce050ce4ab7458a, 0x4c5e58086cab1a39, 0x6edbfbf802e9fec9]

private theorem rounds82_2 : sixRounds 12 (by decide) quarter82_2 = quarter82_3 := by
  decide +kernel

private theorem rounds82_3 : sixRounds 18 (by decide) quarter82_3 = state83 := by
  decide +kernel

private theorem perm82 : KECCAK.f1600 absorbed82 = state83 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds82_0, rounds82_1, rounds82_2, rounds82_3]
  rfl

theorem block82 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes82 ++ tail) state82 =
      KECCAK.Bytes.run 0 tail state83 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes82 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb82 ws)) := by
    rfl
  exact (step state82).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words82).trans perm82))

private def absorb83 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x52 0x81 0x54 0x81 0x5b 0x90 0x20 0x0)) 1 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x90 0x1 0x1 0x60 0x90)) 2 (by decide) (UInt64.ofBytes 0x82 0x57 0x76 0x2b 0x61 0x11 0x83 0x80)) 3 (by decide) (UInt64.ofBytes 0x91 0x1 0x82 0x16 0x1f 0x60 0x3 0x90)) 4 (by decide) (UInt64.ofBytes 0x56 0x81 0x50 0x50 0x50 0x50 0x50 0x5b)) 5 (by decide) (UInt64.ofBytes 0x56 0xbe 0x23 0x61 0xa3 0x2b 0x61 0x5b)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x5b)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x33 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x15 0x14 0x16 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x80 0x0 0x60 0x57 0xdc 0x2b 0x61 0x15)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x0 0x60 0x5b 0xfd)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x81 0x16 0xff))

private def absorbed83 : Vector UInt64 25 :=
  #v[0xab12b2db5e96abe7, 0x909263922976ad47, 0x39dfa148bfba6ed9, 0x2b92fe56e1926f44, 0xf75866c530690e5f, 0x441153ba371dc757, 0xa8763ab94d531fb5, 0xbb258e64a1e87379, 0x45d839adf2e05643, 0xba257f5e6124287f, 0xe2fe36338367a077, 0xe3251bcc225232c2, 0x7955edc02b99dc12, 0x6635a2d22669f64, 0x54a134ebccea1612, 0x6cdefb641caf2126, 0xbbf5827046642e1, 0x916247d38fa014fd, 0x905745ebd38c26db, 0x37b384d19c5f8d9, 0x23ea7a06778854f, 0x59b8551353e58384, 0x32a4ff9b17e2a63b, 0xfd7c1277fd213fc5, 0xd6477459c66e2d8]

private theorem words83 : absorb83 state83 = absorbed83 := by
  decide +kernel

private def quarter83_1 : Vector UInt64 25 :=
  #v[0xa3d9306c307d3a93, 0x427e782800dcc1b, 0x9d2f512b69695000, 0x84e71754e520ec4d, 0x2c0ff272e89aa02f, 0x7568895531110e85, 0x9494696dcda9b6da, 0x954bce46b6495edd, 0x12b01fe8b7d65c19, 0xb503511bb20b3e98, 0x37ad43add06ff124, 0x726d231f1c48365f, 0x89b3837e5b41cfe0, 0x8f7655da027aa822, 0xbdda1dbbf2c08d35, 0xaa015ad581128ff4, 0xd336b49f6c664b2a, 0x788bf3bdce4f799f, 0xf37ca4e3cfe2b5c0, 0x3576d04a383adc4, 0xbfae72ca734b4694, 0xcb29468a686c5e0, 0xf2a67218a32c3e5c, 0x9cc6a2b8a292e600, 0x46dcaea7ec6a6126]

private theorem rounds83_0 : sixRounds 0 (by decide) absorbed83 = quarter83_1 := by
  decide +kernel

private def quarter83_2 : Vector UInt64 25 :=
  #v[0x5bc5a4a93ee430fe, 0xe37e894626c57879, 0xfeffe4a2f3237c59, 0x2bdf7cf4d3799436, 0x25f0258c109580fb, 0x402ff2610cce27cb, 0x72c639558306f7df, 0x8ff6baa0579b6e7d, 0x4f5c5e2d691dcb0f, 0x57244247203aa27b, 0xd6d7ca321d1ed1ef, 0xfc0888bb1c7ace53, 0xe3f3325b5acfa0e1, 0x3a5dbb855af8967a, 0x2f9575bbf8e91d88, 0xb15b92893b20a3c6, 0x47ca37383cc1cfc7, 0x5e2f38084ed9817d, 0xddc1bbf86872555d, 0xc3edab1837b199f, 0x826d45302a4fa4c9, 0x590ea0a9b40f35a0, 0x6b371b0f95f9757f, 0xb3b7db771f5acbc0, 0x4717e72182ab2016]

private theorem rounds83_1 : sixRounds 6 (by decide) quarter83_1 = quarter83_2 := by
  decide +kernel

private def quarter83_3 : Vector UInt64 25 :=
  #v[0x91eeaf7950b384f7, 0x8407cc31f8b4eff7, 0xba433c1c000fde57, 0xca62b96d37319870, 0x59ca938dedee6163, 0x50ef4578682462b1, 0x58f53753359850b2, 0xd75945e15f6b0dbe, 0x9ad2cf11b27896b3, 0x9b1ffafd5757ff14, 0x891823639238b0a8, 0xb82c636861fa0123, 0x6371814948ca5232, 0x5b7bf8fc9c05e054, 0x5e57d01c956db2a2, 0xce9d6968570dba77, 0x236b6a723ef4cc80, 0x7c0192e1be629b3a, 0xa08797f0a40c01f2, 0x279963682fe9f06f, 0xb33a0ecf152de9ff, 0x3f41e32246abe835, 0x30425b704b28574a, 0xf844cad070b5acb1, 0x9656dba0252f24a0]

private theorem rounds83_2 : sixRounds 12 (by decide) quarter83_2 = quarter83_3 := by
  decide +kernel

private theorem rounds83_3 : sixRounds 18 (by decide) quarter83_3 = state84 := by
  decide +kernel

private theorem perm83 : KECCAK.f1600 absorbed83 = state84 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds83_0, rounds83_1, rounds83_2, rounds83_3]
  rfl

theorem block83 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes83 ++ tail) state83 =
      KECCAK.Bytes.run 0 tail state84 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes83 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb83 ws)) := by
    rfl
  exact (step state83).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words83).trans perm83))

end Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
