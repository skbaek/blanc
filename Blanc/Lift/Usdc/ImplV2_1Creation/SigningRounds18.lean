import Blanc.Lift.Usdc.ImplV2_1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb108 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xc3 0x8 0x7f 0x51 0x40 0x60 0x57 0x38)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0xa0 0x79)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x52 0x81 0x0 0x0 0x0 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x80 0x80 0x1 0x4 0x60)) 6 (by decide) (UInt64.ofBytes 0x81 0x2c 0x60 0x52 0x82 0x3 0x81 0x82)) 7 (by decide) (UInt64.ofBytes 0x6b 0x50 0x61 0x80 0x1 0x20 0x60 0x52)) 8 (by decide) (UInt64.ofBytes 0x91 0x1 0x40 0x60 0x39 0x91 0x2c 0x60)) 9 (by decide) (UInt64.ofBytes 0x3 0x91 0x80 0x51 0x40 0x60 0x50 0x50)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x5b 0xfd 0x90)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x81 0x0 0x60 0x16 0x81)) 14 (by decide) (UInt64.ofBytes 0x82 0x80 0x40 0x60 0x52 0x20 0x60 0x3)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x7f 0x54 0x80 0x20)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed108 : Vector UInt64 25 :=
  #v[0xee31867971e2c03f, 0x5b0a02b74a530477, 0x8a217d178b5f0a00, 0xdfd36f279dd1ca1b, 0x3ac05befd8ac1bd8, 0xeef9f4abf7e8ec0, 0xf1957732e180a6c0, 0x1f1d3d5fa0d4e8e1, 0xbefe05c0c572f8d4, 0x4ee955a5a87148de, 0x880ee397a9d3115e, 0xd39f8c281edc0781, 0xfdec75fe25090b47, 0xf20ac6f68c9c6545, 0xa017d87316551d37, 0x6969536c2000633f, 0x24f70665406a75ce, 0xe8f1d54fb44e99f9, 0x43e985648c34923d, 0xd943c39d46ddb36b, 0xfaa6c03460d1b72c, 0xd1b65b789ca047a6, 0xb7ade247a9359577, 0x4af23c74b20264e6, 0x36f25ce4788f48c0]

private theorem words108 : absorb108 state108 = absorbed108 := by
  decide +kernel

private def quarter108_1 : Vector UInt64 25 :=
  #v[0xe0e55bc22c51747d, 0xff5ea94d6862bc9, 0xadfb253db6051ad1, 0x41c6f59d5f49eb2c, 0x20135432b21973df, 0x519a1fce493b42e1, 0xb1d07e0e0b6a311d, 0xe76c8f9ae995b8af, 0xd039ebc277ca7707, 0x9450ab04628c51ea, 0xffe7cbcc828a20da, 0x78892d233721f96d, 0x3c896ef602be36ae, 0x32dda0480c4a535f, 0x4559dce981d2244d, 0xbb85d732b02f75f7, 0xcff75c7688a74c6a, 0xe242f31fab053d5b, 0x7c82c713b229bfbe, 0xf90ca4a177135105, 0xa24b51484355801f, 0x52d80f1ebcb2f978, 0xe1ae6a7150875465, 0x99d642127b0406e9, 0xac466fecc697494b]

private theorem rounds108_0 : sixRounds 0 (by decide) absorbed108 = quarter108_1 := by
  decide +kernel

private def quarter108_2 : Vector UInt64 25 :=
  #v[0xd9f2ed7d422bd3a0, 0x1796d8521ee83792, 0xb92368d46a3d7e8f, 0x21ffd26b4a7e47b, 0x907157fd9ab1060d, 0x2c55dcb71ce383a4, 0xe9353ab661e9d737, 0xc2b92f65a223fa3a, 0xed25538f98098e01, 0x13d7565fc2576a3c, 0x2aedd7f56288e61, 0xe5200605ebacd279, 0xf57607b2965a3d7c, 0x9e7fdac8e83f3f6, 0x1ff2dbef4143a3a9, 0x32d26faf7c2197a3, 0x18cc89b50fd15c4e, 0x28446d6d11ea9dbc, 0xb13116c65c5b1b94, 0xd21839802ae6f181, 0x85b7eb1d31e3fbed, 0xd7947de71e6d8431, 0x1372be6bae7f837a, 0xd7937fe97154351e, 0xa930541e41fda8aa]

private theorem rounds108_1 : sixRounds 6 (by decide) quarter108_1 = quarter108_2 := by
  decide +kernel

private def quarter108_3 : Vector UInt64 25 :=
  #v[0x1f68c3d5f508b770, 0xb02518e068fb9ffc, 0xa2bd582a950aad7c, 0x1bfe4ba142900f3d, 0x475bc50703f17ca3, 0x28d3e36fcc2ea71d, 0xfe3c4ef3c6d9834, 0x66543fc790784e03, 0xc4da4851b9b83585, 0x2cf809a273c47b0d, 0x25c4e493c64751b3, 0x564c7af858202038, 0x8b9e16e7e8957307, 0x8ce4eabaf2ef2a67, 0x7ae97cf7045bf3ae, 0x2c0810e554827a36, 0x73d986960c6bba56, 0xe253cb377bffb8f8, 0xf478632cdb1ab4c5, 0xdf2f6a3f29b70d74, 0xa7c87e68c317ead4, 0x87af2c3041400d09, 0xea353d601cd41169, 0x1e4865697bbd86d9, 0x956428da6d368617]

private theorem rounds108_2 : sixRounds 12 (by decide) quarter108_2 = quarter108_3 := by
  decide +kernel

private theorem rounds108_3 : sixRounds 18 (by decide) quarter108_3 = state109 := by
  decide +kernel

private theorem perm108 : KECCAK.f1600 absorbed108 = state109 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds108_0, rounds108_1, rounds108_2, rounds108_3]
  rfl

theorem block108 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes108 ++ tail) state108 =
      KECCAK.Bytes.run 0 tail state109 := by
  exact run_block_of_step bytes108 tail absorb108 state108 absorbed108
    state109 (fun _ => rfl) words108 perm108

private def absorb109 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x17 0x1 0x60 0x16 0x0 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x18 0xe6 0xa4 0xff 0x7f 0x51 0x55 0x90)) 4 (by decide) (UInt64.ofBytes 0x52 0x28 0xcf 0x65 0x25 0x69 0x77 0x17)) 5 (by decide) (UInt64.ofBytes 0x6b 0xa8 0x6e 0x51 0xd1 0x8f 0xc8 0x8f)) 6 (by decide) (UInt64.ofBytes 0x5a 0x57 0xfa 0x35 0x52 0x7 0xda 0x56)) 7 (by decide) (UInt64.ofBytes 0x50 0xa2 0x90 0x91 0x55 0xb8 0xa4 0xf6)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x5b 0x56)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x60 0x3 0x60 0x52 0x81 0x90 0x0 0x60)) 12 (by decide) (UInt64.ofBytes 0x60 0x54 0x20 0x90 0x40 0x60 0x52 0x20)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x5b 0x56 0x90 0x16 0xff)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x57 0x46 0x3a 0x61 0x16 0x83 0xff 0xff))

private def absorbed109 : Vector UInt64 25 :=
  #v[0x9faa6fa91e22d5e1, 0x3218931ecfc85bb5, 0xceb1c17a312e88, 0xf57b4012506c6183, 0x5bb3f8c3437d4d58, 0x9449618f5e7feb4d, 0x952641ea8031221f, 0x261413dac6c01867, 0x9d000cc37946e4a2, 0x5434dd390a98ad75, 0x439cab89cc205d5c, 0xcc832a88d43c5591, 0x47e22cf08fbe9c9f, 0xfd21afe72e388804, 0x1d9e01fce067d927, 0x449a29615c11454, 0x297b86e8d85b6803, 0x4ce6412d39a7fcd5, 0x855a96e3de2e3aac, 0xc98a2f6701cf7f66, 0x9231c370a91a46b9, 0xa4789129c4ff635b, 0x2e58bc3e801d5cab, 0x9b0e425d6cf8c78a, 0x9aa856fd546db948]

private theorem words109 : absorb109 state109 = absorbed109 := by
  decide +kernel

private def quarter109_1 : Vector UInt64 25 :=
  #v[0xf6e42c1bf1c254ce, 0xd599d5e42a59c46a, 0xc5eeacdd0bff00ac, 0x4db279812cd9048a, 0xb718af2c4b0834f9, 0x5f80c3468a041d6b, 0x7918619ba0807140, 0xae61711fcaae0bf9, 0x801f50b763652e88, 0x6f06ff0660e98a02, 0xede2dddace2f261c, 0x3ea1418db5b3debe, 0xf67952301da99556, 0xc905f2339e1b3c9c, 0xcdeb9a33a8772d33, 0xd5682bec46b59fda, 0xe33ce2f0626ad860, 0x804d0c969954a25a, 0xa16822e6a3919ff5, 0xa9acb1c6a700ba73, 0x890952b82a6542e8, 0xa658bea3b7b494a2, 0xc9c21ace5ad3c146, 0x18ee979ae2d2fc64, 0xc1b69ec08ef30fe5]

private theorem rounds109_0 : sixRounds 0 (by decide) absorbed109 = quarter109_1 := by
  decide +kernel

private def quarter109_2 : Vector UInt64 25 :=
  #v[0x5d6ae6e900da1c2f, 0x60e2fa2e2bbcecaf, 0xd3de0832b1bad907, 0x163035ef12e02df0, 0x6bc3edf3f167ddc0, 0x67ab650d2a407ed4, 0xe96ecba8e5c0190f, 0x9c40b62e077e97c6, 0x62eb87c1573e9117, 0x233a97a290b61ee2, 0xd803aababa5fd2e6, 0x4f6cefd859cc927, 0x8b6971b86ed610ad, 0x647c96455eb044b2, 0xb7352305a7d0cd25, 0x4c37bfeb2a07b606, 0x1a53e0e15555a864, 0xf66398aeedb419ba, 0xd592b54e258887ca, 0x4dd191bedcea97ab, 0x2679efbec05e323e, 0x3eba4513bc31458e, 0x14e9217a660e89f5, 0x3e9f483ad96c0202, 0x986a27c3ed33f9e7]

private theorem rounds109_1 : sixRounds 6 (by decide) quarter109_1 = quarter109_2 := by
  decide +kernel

private def quarter109_3 : Vector UInt64 25 :=
  #v[0x5e6297159772785b, 0xf8a11dd37fdd7eb4, 0xc98c9b798cfc4dfd, 0x662ee7a9d476d60, 0x1ec77d54e717855e, 0xc74c0d469180362, 0x32dc425121d86ec0, 0xeef0d4f037df63b4, 0x428a2474180e99ae, 0x47a0bbc46ae8d90c, 0xaf1e71524c82e057, 0x4caefe7863512f0e, 0x34d0b6725f57cb02, 0x28367b6bc88aa587, 0xfe7dcadb98c0240e, 0xe04645fabba3131e, 0x2f010747e3abef36, 0x3d5a2a389419eab6, 0xb46996bdf0a749cc, 0x59ff1cb56f635bd3, 0x512f6f3cbe6f0eb6, 0xeb0a3b0b7dd6dda3, 0xcd1508a27bef7fad, 0x3fe19dd0d4158ba0, 0x4910e227e625ceb1]

private theorem rounds109_2 : sixRounds 12 (by decide) quarter109_2 = quarter109_3 := by
  decide +kernel

private theorem rounds109_3 : sixRounds 18 (by decide) quarter109_3 = state110 := by
  decide +kernel

private theorem perm109 : KECCAK.f1600 absorbed109 = state110 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds109_0, rounds109_1, rounds109_2, rounds109_3]
  rfl

theorem block109 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes109 ++ tail) state109 =
      KECCAK.Bytes.run 0 tail state110 := by
  exact run_block_of_step bytes109 tail absorb109 state109 absorbed109
    state110 (fun _ => rfl) words109 perm109

private def absorb110 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x40 0x60)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x4 0x60 0x52 0x81 0x0 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x81 0x82 0x1 0x20 0x60 0x80 0x80 0x1)) 6 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x24 0x60 0x52 0x82 0x3)) 7 (by decide) (UInt64.ofBytes 0x24 0x60 0xfb 0x51 0x61 0x80 0x1 0x20)) 8 (by decide) (UInt64.ofBytes 0x50 0x50 0x91 0x1 0x40 0x60 0x39 0x91)) 9 (by decide) (UInt64.ofBytes 0xfd 0x90 0x3 0x91 0x80 0x51 0x40 0x60)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x5b)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x16 0x82 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x7f 0x51 0x40 0x60 0x57 0xb2 0x3a 0x61)) 14 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0))

private def absorbed110 : Vector UInt64 25 :=
  #v[0xa4fa62e893e7e865, 0xfe62e049de185061, 0x60c5739b56507c30, 0x4bbdf1b2b0d5b872, 0x4daaaced53981b87, 0x3d3304ee7304f822, 0xe78aacf407e2b0dc, 0x8efdd7577ade9720, 0x5a8fad3b100e840b, 0x48d978e51c550806, 0xd1c6c44948061b, 0xf446648e74e4c86, 0x55ef6bed7cc08673, 0x87b5b64c60732d96, 0x9493eac1912c3159, 0xff175a9a89dd18f9, 0xd88451166feb2c0d, 0x5e70791b8333cb62, 0x9182587527449fdc, 0xde35d8701bc02c6b, 0x6c5ee1dafe9d16f7, 0xc9985b041017915b, 0x2fc1d84629710088, 0xec14b6d4202a8599, 0x79c9cd278e83c415]

private theorem words110 : absorb110 state110 = absorbed110 := by
  decide +kernel

private def quarter110_1 : Vector UInt64 25 :=
  #v[0x7ccaf82609856049, 0xe6fcf29ff1e9901e, 0x99c1f8fd0bfe84c6, 0xc9a5e11d9e8ead7e, 0x7ea60e2b5bf53e1c, 0x92c7524c912db19, 0x8e8e2fd18082296c, 0x13af9d660a84be7, 0x946f382a3b8b652a, 0xf84b4cd2dcd8e886, 0x536c1908955e32a0, 0x6e7705aba595bc85, 0x51bfc482456e6b12, 0xde2ed305b520bfa9, 0xf84bc7ed939ee250, 0x5fcc8c1eb152ae7a, 0x3045abcdf8cf1e71, 0x39e031fa745c9f29, 0x41e75575b08622be, 0xd3fd4fbbabbae22f, 0xf9ac405fc42b8526, 0x4efbe636b8855b53, 0x94115c02b5acb3bb, 0x7496bc027b2f537f, 0x9fc7ee493182da88]

private theorem rounds110_0 : sixRounds 0 (by decide) absorbed110 = quarter110_1 := by
  decide +kernel

private def quarter110_2 : Vector UInt64 25 :=
  #v[0x453d11881e245b05, 0xa41dc5d7021bf475, 0xd3e1addc8ca0b78a, 0xa0fde972e7800166, 0xc70e5a98cf53dfa7, 0x4d2285e78139facc, 0xa8865a5b0ef60e21, 0x9314ecd216df4829, 0x72b7bc6fdba16228, 0xe9b2ed94ebc956cc, 0x9325a9659a2dbc8c, 0xbd33979ef229640e, 0x42a7afec161720da, 0x843af6339ca67c5b, 0x9b30ab4ac73b1448, 0x911ac6a9e955edf6, 0x4fedb70593cdb972, 0xca3fa20151932e95, 0xc6742fb6c077f3b0, 0x9f44b1d648cfe434, 0xa0abd782d2f4ee3a, 0xf41402721e65efc2, 0xc7fcc5960c087317, 0xf33620dd88ac57ca, 0x90590b76dd2aa0b3]

private theorem rounds110_1 : sixRounds 6 (by decide) quarter110_1 = quarter110_2 := by
  decide +kernel

private def quarter110_3 : Vector UInt64 25 :=
  #v[0x53d624c9a6ae8794, 0xc6ce622230f3bb4e, 0x2b747b825f22e023, 0xe257886fc62604f5, 0x789432ecc2f412ee, 0xd4a0a84e9736a92f, 0xd4d9dea6f01f9db4, 0xef62634765ff62c2, 0x8c711d9a03e4f8ea, 0xff26f1b58ce35262, 0x21d913410a27af14, 0xccee6dc17a7fed61, 0xc1d1e04bd1b82afe, 0x35104df16dafa8f1, 0x27a8ab18f381795f, 0x84c3d51255087dee, 0x96ec919edb7c6724, 0x3154e5c1c6aba190, 0xf1a863f7291e1ffa, 0x54d4b237634afe25, 0x132436b251ee24f5, 0xe2b8d71a561cc779, 0xebf1702803fb3a95, 0xd45b8d8bc6bccdb6, 0xb3280f57e0dfc85b]

private theorem rounds110_2 : sixRounds 12 (by decide) quarter110_2 = quarter110_3 := by
  decide +kernel

private theorem rounds110_3 : sixRounds 18 (by decide) quarter110_3 = state111 := by
  decide +kernel

private theorem perm110 : KECCAK.f1600 absorbed110 = state111 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds110_0, rounds110_1, rounds110_2, rounds110_3]
  rfl

theorem block110 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes110 ++ tail) state110 =
      KECCAK.Bytes.run 0 tail state111 := by
  exact run_block_of_step bytes110 tail absorb110 state110 absorbed110
    state111 (fun _ => rfl) words110 perm110

private def absorb111 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x60 0x80 0x80 0x1 0x4 0x60 0x52 0x81)) 2 (by decide) (UInt64.ofBytes 0x60 0x52 0x82 0x3 0x81 0x82 0x1 0x20)) 3 (by decide) (UInt64.ofBytes 0x61 0x80 0x1 0x20 0x60 0x52 0x81 0x22)) 4 (by decide) (UInt64.ofBytes 0x40 0x60 0x39 0x91 0x22 0x60 0x7e 0x4f)) 5 (by decide) (UInt64.ofBytes 0x80 0x51 0x40 0x60 0x50 0x50 0x91 0x1)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x5b 0xfd 0x90 0x3 0x91)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x81 0x0 0x60 0x16 0x84 0x80 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x81 0x90 0x20 0x60 0xa 0x60 0x52 0x81)) 11 (by decide) (UInt64.ofBytes 0x87 0x94 0x20 0x83 0x80 0x40 0x60 0x52)) 12 (by decide) (UInt64.ofBytes 0x91 0x52 0x82 0x94 0x52 0x84 0x80 0x16)) 13 (by decide) (UInt64.ofBytes 0x51 0x81 0x55 0x90 0x85 0x20 0x90 0x82)) 14 (by decide) (UInt64.ofBytes 0x5b 0x8c 0x7f 0x51 0x91 0x52 0x81 0x85)) 15 (by decide) (UInt64.ofBytes 0x4f 0xd1 0x5b 0x7d 0xec 0xeb 0xe5 0xe1)) 16 (by decide) (UInt64.ofBytes 0x3 0xdd 0xf3 0x84 0x1e 0x7d 0x42 0x71))

private def absorbed111 : Vector UInt64 25 :=
  #v[0x48a9b90e37f5f525, 0x3c4eb08f90631195, 0x546c92b06b760368, 0x83b180a6c8431eb3, 0x3cfc09027e58c91d, 0xa5930bbb7d729982, 0x55005243a91b11d0, 0x54ed4e75de89cc24, 0x976841f82327589d, 0xafc3723868882866, 0x91588e9df2e6b094, 0x88dd690f2853e653, 0x2581da66e62c9b19, 0xa561e2769d625cb1, 0x3017e9c066b226a5, 0xef7a074c152a1365, 0xdfe31b2f835f5e8b, 0xa20d9957c3f26e36, 0x31647f509babe1e8, 0x6905fc0a56c0f6ee, 0xef7642ef27644bb2, 0x528560c98b9b5e35, 0x71c27faa0c43470a, 0x66a84cb68af9a131, 0xb588048d02c93cba]

private theorem words111 : absorb111 state111 = absorbed111 := by
  decide +kernel

private def quarter111_1 : Vector UInt64 25 :=
  #v[0xa381bb8ed2d07cb2, 0xcf3d494c2d12342d, 0xbccea63ce1f2a61f, 0x120910aec9c28c51, 0x27414b885a95f1ac, 0x1c640fc9c314a516, 0xfc9100ed3d1742d8, 0x9033081b4f004191, 0xf6d2edc83235213d, 0xf011f0d60305e1bf, 0x2c8ffb21ad860454, 0x59260c22ef58e013, 0x2c115b921db08218, 0x1ff0003e014570ef, 0xe63a1504fce503b4, 0xde4f7a1f01091362, 0xd9ae61f0c9c32df9, 0x129174439eb37c27, 0x98c790b58b6d3baa, 0x7b69adaaeac14168, 0x3667b598f487858e, 0x425e2b95f9f65a36, 0x45420ceb9136608c, 0xb5c0992b4fd1727f, 0xe3266931508bab78]

private theorem rounds111_0 : sixRounds 0 (by decide) absorbed111 = quarter111_1 := by
  decide +kernel

private def quarter111_2 : Vector UInt64 25 :=
  #v[0xccf1725eb2ceecc8, 0x2f5e390b2232699a, 0x6bee7eb1f8fdb36e, 0x28c5fd88f7c8476f, 0xefb39ed47de2a975, 0x703ad2e29a6a1862, 0x24bb37f193ef7dca, 0x7e0c041d2ca5d9ed, 0x5ba6e19c37ece017, 0xb1417f912ca707eb, 0x386d71dbd85028a2, 0x7feab61f8eb1c796, 0x5e60f17dad5e0ac5, 0xbd01c71fbe9465ce, 0x4dc0419622007cb0, 0x99d797e1f65d66c7, 0x677b3846e57b81fd, 0x1978568ee9080f2b, 0xfa58401fc2899cc5, 0xb566d66af08b8437, 0x85684da4065d5939, 0x67e880c1ce59a060, 0x667938fc5f12e3f, 0x33e94ce18e5d97ea, 0x62886e1f2847b99b]

private theorem rounds111_1 : sixRounds 6 (by decide) quarter111_1 = quarter111_2 := by
  decide +kernel

private def quarter111_3 : Vector UInt64 25 :=
  #v[0x4610043972d1c1d7, 0xd8d38658b469f3a2, 0xdfd5ed12378b1448, 0xa5f99bbb77d0f5c2, 0x2558a6df7ab000f7, 0x1a0f9e776b1f80c2, 0x1f3e633c33b0c920, 0xa74382240d735aa4, 0x2318b95384a410fe, 0x3187167252e10c66, 0x90d287d3cff41e79, 0x94bf0b153dc76614, 0x25c71e309fb9baaa, 0xf30073615f8767fc, 0xd21bead46f31c2fd, 0x8db189835478e1e4, 0xb33878a0e493e593, 0x58117413f463f632, 0x374605969a301238, 0x6d488a521a2891b8, 0x8f45d34d63c75e41, 0x55b0f78e24266e1e, 0x691eebb1aacdebc1, 0x331a6fc753bad96d, 0x19e874140695e6d9]

private theorem rounds111_2 : sixRounds 12 (by decide) quarter111_2 = quarter111_3 := by
  decide +kernel

private theorem rounds111_3 : sixRounds 18 (by decide) quarter111_3 = state112 := by
  decide +kernel

private theorem perm111 : KECCAK.f1600 absorbed111 = state112 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds111_0, rounds111_1, rounds111_2, rounds111_3]
  rfl

theorem block111 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes111 ++ tail) state111 =
      KECCAK.Bytes.run 0 tail state112 := by
  exact run_block_of_step bytes111 tail absorb111 state111 absorbed111
    state112 (fun _ => rfl) words111 perm111

private def absorb112 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x20 0x5b 0x1e 0x29 0xb2 0xf7 0xc0 0x14)) 1 (by decide) (UInt64.ofBytes 0x81 0x92 0x25 0xb9 0xc3 0xc7 0xc8 0xa)) 2 (by decide) (UInt64.ofBytes 0x50 0xa3 0x90 0x1 0x91 0x90 0x3 0x90)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x5b 0x56 0x50 0x50)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x60 0x57 0x8d 0x3b 0x61 0x16 0x83 0xff)) 7 (by decide) (UInt64.ofBytes 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x40)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x1 0x4 0x60 0x52 0x81 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x3 0x81 0x82 0x1 0x20 0x60 0x80 0x80)) 13 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x25 0x60 0x52 0x82)) 14 (by decide) (UInt64.ofBytes 0x91 0x25 0x60 0xd6 0x51 0x61 0x80 0x1)) 15 (by decide) (UInt64.ofBytes 0x60 0x50 0x50 0x91 0x1 0x40 0x60 0x39)) 16 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x90 0x3 0x91 0x80 0x51 0x40))

private def absorbed112 : Vector UInt64 25 :=
  #v[0xf2eda79a85a5582a, 0xdce5d1b4ebe3a32e, 0xf89ef03c6f9baa46, 0xcf65c8eb4d69f05e, 0x9b67efd324e7f63c, 0x9089bf8d6d4f8fc, 0xf4d434026e458d29, 0x797d5552107fd41f, 0x6dacdbba67ca1ec7, 0x36142d22291f14bc, 0xaee9a47926bdc32f, 0xf7c56915284efcbd, 0xf71fb6f4a41729e4, 0xf44b5e946d6edab4, 0xc22ca06effab1df5, 0xe8b5c4c87a104b5a, 0x13fa507ee7827eba, 0xeb21bbe5cd4c3ee3, 0x7d6f5109a4f9d97, 0x203f8012eb61b6c, 0x7ca28e05d32f33ef, 0x456825a58c40d2bc, 0x7faef65bbf91cfc1, 0xd3ddc1c6c677afe, 0xa614812a06c4ebb3]

private theorem words112 : absorb112 state112 = absorbed112 := by
  decide +kernel

private def quarter112_1 : Vector UInt64 25 :=
  #v[0x8b89a49fd50b8c96, 0xfdea50880e68b14e, 0x6dde6d2803ed371e, 0xb48586268f9702b3, 0x9854b449ee109840, 0xd7b919ed1ab72744, 0x1c95fc2437e5e43d, 0x2d2d28daf691dcf6, 0xeab92f5bbd42c96, 0x5813d1509f595180, 0xf83775920809d286, 0x82821bcec93ce06e, 0xd6263a31e87d08f3, 0x714fdaa84ac29178, 0xe8ea1f56aab87fd7, 0xb5a29de894b0f8ee, 0x67e4730604c0c5d3, 0x41d057439c54eb26, 0xde96219560c6062e, 0xa357751fcb904d04, 0xfe15fe7517d38f44, 0x10c80d1bf9649c2, 0x3e801fea23f5bbcd, 0xeac4a0ecfb003ad9, 0xcbb5146957ddf243]

private theorem rounds112_0 : sixRounds 0 (by decide) absorbed112 = quarter112_1 := by
  decide +kernel

private def quarter112_2 : Vector UInt64 25 :=
  #v[0x12b89f0cd4914944, 0xb2938c1e9659cc26, 0x377937b640ef2554, 0xba850fdf42422629, 0x6240f36f120e6f9a, 0xca92b0019d268068, 0xeda1a26c4410e019, 0xca40ffc66770b7ab, 0x63d78c64e379a491, 0xfaf9fbb568cc2695, 0xbed5998769774627, 0xe14221bc1808707f, 0x3c292b38d83ac4e9, 0xda07bb6ccbed9580, 0xba5bb7c8d2398732, 0x4e9f78d5ce98b127, 0x745caaad69aeb7e4, 0x1b30c09c31fbcc56, 0x33e096ebd1d3271, 0xd023d9e5dfacc31a, 0xd4f14030ffbd6b20, 0x46a74739be5602e5, 0xb2f1998e9dc4a452, 0xa8490ef31efd43bc, 0xf6df3645ec326b0f]

private theorem rounds112_1 : sixRounds 6 (by decide) quarter112_1 = quarter112_2 := by
  decide +kernel

private def quarter112_3 : Vector UInt64 25 :=
  #v[0x6e6e20467d93c4d2, 0xe22c112582aab892, 0x5ebd5e3d0b3e5238, 0x7faddde1f7535651, 0x4c24146febd8a8f4, 0xf67f7551205738d3, 0xa7ad8ca699ae73ca, 0x532f13332dc9b16d, 0x52b345be35e8cb06, 0x6152ecb4856d0f54, 0xadd14e9ca08c826f, 0xc1e8ec71bad09dea, 0xed87e7cebb7027a1, 0xa71ba17ed4688043, 0x91a6670d72b25acf, 0xd79d504f77123fdd, 0xce41042ec2cc02de, 0x791da13c24b170f6, 0x472c0761a861f0b4, 0x7aa7d872742e517d, 0x8464019e68c79ad8, 0x18e9eccf1d5cdf4e, 0xc081bbbd21d367f4, 0x4baa026575207c77, 0x4cfec5fda7f5d627]

private theorem rounds112_2 : sixRounds 12 (by decide) quarter112_2 = quarter112_3 := by
  decide +kernel

private theorem rounds112_3 : sixRounds 18 (by decide) quarter112_3 = state113 := by
  decide +kernel

private theorem perm112 : KECCAK.f1600 absorbed112 = state113 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds112_0, rounds112_1, rounds112_2, rounds112_3]
  rfl

theorem block112 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes112 ++ tail) state112 =
      KECCAK.Bytes.run 0 tail state113 := by
  exact run_block_of_step bytes112 tail absorb112 state112 absorbed112
    state113 (fun _ => rfl) words112 perm112

private def absorb113 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x61 0x16 0x82 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x8 0x7f 0x51 0x40 0x60 0x57 0xf9 0x3b)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x81 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x20 0x60 0x80 0x80 0x1 0x4 0x60 0x52)) 9 (by decide) (UInt64.ofBytes 0x23 0x60 0x52 0x82 0x3 0x81 0x82 0x1)) 10 (by decide) (UInt64.ofBytes 0x4e 0x61 0x80 0x1 0x20 0x60 0x52 0x81)) 11 (by decide) (UInt64.ofBytes 0x1 0x40 0x60 0x39 0x91 0x23 0x60 0x70)) 12 (by decide) (UInt64.ofBytes 0x91 0x80 0x51 0x40 0x60 0x50 0x50 0x91)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x5b 0xfd 0x90 0x3)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x52 0x81 0x90 0x0 0x60 0x16 0x83 0xff))

private def absorbed113 : Vector UInt64 25 :=
  #v[0xbf12b9fab5809ea1, 0xb07e969fcb2cdabb, 0xcc0ded421e85ff52, 0x7d3a788ac98932aa, 0x6eb0f703ae80aef9, 0xd5bb407a337fe2af, 0x3ef46b32d56e4db1, 0x1abe7baeebffc6e2, 0x7a5c4dd6876018af, 0xe5a54770c4d12a60, 0x492a2cb1938d00a2, 0x99f374b8b91c898c, 0xc7d768b7acd70b0f, 0x7eafab7924743804, 0xd6816eed9d40d416, 0xfb72be7a6b80bbaa, 0xc8eae8c96a12373, 0xfa98e77c113fc630, 0x2453d0a0d39be952, 0xa6fc36a154cabedd, 0xd603216fa70786a4, 0x168cd11ae3346c04, 0xe3d01a51c04511c0, 0x92480e30c73a378c, 0xf9c14f3f07995da3]

private theorem words113 : absorb113 state113 = absorbed113 := by
  decide +kernel

private def quarter113_1 : Vector UInt64 25 :=
  #v[0x5db24d1549b8d32d, 0xba04f8e1f4ccd194, 0x8c887c6a8e6cc1c4, 0xfed48e5b82a3e1e9, 0xc11a2eef2096c469, 0x2524d72753843663, 0xd59f5987df073654, 0x7efd07c7ab0098c8, 0x4ea027c098c84518, 0x72186487fdab58e6, 0xa72bf0e0b5920909, 0xa0957a7bb5b65488, 0x1d7b41239be4682b, 0x41205aed51a724c8, 0x986d33d6462402b5, 0x3b99de6c10ec5acd, 0x7605db63b95e8dd6, 0xec8cd42d369cc027, 0x61c3dd077bc80ad6, 0x1778b8ed8405d26b, 0xedbc68edf2f1f697, 0xf095dab8f24bfca7, 0x92309d06190d9ca4, 0xbfa82c0e7be16584, 0xd46c8c01c1e9ea81]

private theorem rounds113_0 : sixRounds 0 (by decide) absorbed113 = quarter113_1 := by
  decide +kernel

private def quarter113_2 : Vector UInt64 25 :=
  #v[0x272ba1553440150e, 0xb4822028fca76fc8, 0xa5f783502cb7d4e9, 0xe5f754bb953201e2, 0x76689d3f6a0730a1, 0x982eb0fc4e7a2f7a, 0xd848a586fbff347b, 0x56e7ebc4390e0bff, 0x206b6dfbbd40be7f, 0x760664f43f1086d7, 0x1fd283d61606968c, 0x73bb3ce607884bd8, 0xea5726500f5aaa8e, 0x73cf8101d6fb4549, 0xe26b59a3a768b9c0, 0x74815409095129b0, 0xfe14ea7bc1528ae2, 0x540b7af6c2e2bb7b, 0x4f2d28991528d7fb, 0xe7ecdffa27a43014, 0x1aca376183418fda, 0xebbf7a42c8297736, 0x904472ffb1443aa, 0x13f8f080d8ca38ce, 0xd2f446cf71d3ed57]

private theorem rounds113_1 : sixRounds 6 (by decide) quarter113_1 = quarter113_2 := by
  decide +kernel

private def quarter113_3 : Vector UInt64 25 :=
  #v[0x37c320734c0af1f2, 0x9d99668d5a8c239a, 0xde6bb6a1c6be4b3, 0x49f4b3f5ac67de3, 0xee3b7444f23e99f7, 0x5de4f4a8219dafc1, 0x4f69668669e86d0b, 0x5e3488add4923dc3, 0x9eefb2113f0b58cd, 0x7c12f4b3348094, 0x6a260ab56119a374, 0x6245f6fe5b9fe79e, 0xd26ccc499d93b9b7, 0xfdb690c8ddb5f9a2, 0x146e130930260be0, 0xbdbae39df5a75064, 0xe45815043ae6c04f, 0x561667508a8c622b, 0x9670591c1b7c3bb1, 0x4471468c1af4e715, 0xa56785e4b62dc89c, 0xb167919c7e1ccca7, 0x789a757c5dd1a42c, 0xad737747bdd1f14f, 0x39152ca33cfeacab]

private theorem rounds113_2 : sixRounds 12 (by decide) quarter113_2 = quarter113_3 := by
  decide +kernel

private theorem rounds113_3 : sixRounds 18 (by decide) quarter113_3 = state114 := by
  decide +kernel

private theorem perm113 : KECCAK.f1600 absorbed113 = state114 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds113_0, rounds113_1, rounds113_2, rounds113_3]
  rfl

theorem block113 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes113 ++ tail) state113 =
      KECCAK.Bytes.run 0 tail state114 := by
  exact run_block_of_step bytes113 tail absorb113 state113 absorbed113
    state114 (fun _ => rfl) words113 perm113

end Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
