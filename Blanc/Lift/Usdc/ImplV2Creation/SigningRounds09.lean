import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb054 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x1 0x4 0x60 0x52 0x81 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x3 0x81 0x82 0x1 0x20 0x60 0x80 0x80)) 4 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x25 0x60 0x52 0x82)) 5 (by decide) (UInt64.ofBytes 0x91 0x25 0x60 0xc5 0x59 0x61 0x80 0x1)) 6 (by decide) (UInt64.ofBytes 0x60 0x50 0x50 0x91 0x1 0x40 0x60 0x39)) 7 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x90 0x3 0x91 0x80 0x51 0x40)) 8 (by decide) (UInt64.ofBytes 0x41 0x61 0x86 0x86 0x33 0xd8 0x10 0x61)) 9 (by decide) (UInt64.ofBytes 0xff 0x73 0x54 0x1 0x60 0x5b 0x56 0xb3)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x1c 0x61 0x14 0x33 0x16 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xc3 0x8 0x7f 0x51 0x40 0x60 0x57 0xf0)) 14 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0xa0 0x79)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0))

private def absorbed054 : Vector UInt64 25 :=
  #v[0xc406b3566487e407, 0xd7b7fffbc931683f, 0x83c6e3467524bdd2, 0x77ab36cb767cce84, 0xcac41b72ff71dc50, 0x19ebcb44f8e23a56, 0x1973d769cbde68ba, 0xb9437221f4189624, 0xf51b36d8a497d96a, 0x1077e08d48f43c01, 0x18eb54e2a6bc5f3a, 0x21e78627fdb20042, 0xe339293b687c5f67, 0x9324b698ee4b98b8, 0x4155637806e7a8b9, 0x4bbaf01d74cfbd0, 0xaaa83f2bad1ba9e6, 0xcfac0b456c184a4a, 0xcde173d75a74a921, 0xb68a22e620192e30, 0xbbc8733e470e7e89, 0x5007a93e7a8d57e3, 0x8ed75182a850368a, 0x11480b5f3b6dc360, 0x2442605ad9d8aded]

private theorem words054 : absorb054 state054 = absorbed054 := by
  decide +kernel

private def quarter054_1 : Vector UInt64 25 :=
  #v[0x83322950bf164e65, 0x3dc8846dc2018927, 0x52ef0a6acc52ff35, 0x7b76ec7736406a22, 0x62191bfa03ef7f1b, 0xe8b1562917489234, 0xde595265e90d8736, 0xe62d218aac9de633, 0x1a0d31e40c220411, 0x2b00c580cf63d0c2, 0x1cff98a9130d44de, 0xc53152d08bc8570, 0x723c026b1c403a02, 0xd82872df0f02afea, 0x9639af892caa516d, 0x8281a191cbd9cc86, 0xf95f3644435c680a, 0xfdf03ca146092b66, 0x272edd08771f7ae1, 0x74efd3153741b633, 0x87a1b357ba6a05bd, 0x8a397995be440477, 0xbd2bb5da712fa2ac, 0xd8c3feb0e0d00aa2, 0x4efe2138092dff2f]

private theorem rounds054_0 : sixRounds 0 (by decide) absorbed054 = quarter054_1 := by
  decide +kernel

private def quarter054_2 : Vector UInt64 25 :=
  #v[0x712607202c507fb5, 0x64fba5bf314f747a, 0x9a245f38521f88b0, 0xa4b4cb79051b359b, 0xec59876bd6af1dbc, 0xa35c61bf16bc543d, 0x69930116b786554c, 0xa5ba70bee2afd93b, 0x503555cd9fe7d418, 0x54a22596a030fc4c, 0x97ac520864a600bb, 0xcb9ce90d9223e3e0, 0x2c4cf54e25d10a47, 0xe6a7f70bae4b4b27, 0xf88858ba2b44315c, 0xa6e3a9c3b62bb7a4, 0x78d33098fd33e3d5, 0xb351570e37cf84cd, 0xca39b5a7a2de0190, 0x6453c39a033c31c0, 0x25ca77f5c52c6979, 0x1a1b9fc28eb3eaf8, 0x19e8f7af9dfc89ba, 0x49b870b9e82660ec, 0xc4f6637f0671715]

private theorem rounds054_1 : sixRounds 6 (by decide) quarter054_1 = quarter054_2 := by
  decide +kernel

private def quarter054_3 : Vector UInt64 25 :=
  #v[0xa3ab215846f67b46, 0x2e4a505753ff37a0, 0xe024d7a691536007, 0x8f158b4a4a7465a5, 0x8549754a7eeb1bd7, 0xaba95b03be41b7d4, 0xba133ceeffcd2d51, 0x96aeb70f691e0a11, 0x2f09d3bfd3868ff5, 0x7e292871e2fbb199, 0x718c4cfd271eb751, 0x8e697c8611853194, 0x8f9a8f06802bda15, 0xc7b3ac4b3333dec0, 0xf047986be5babb5, 0x8dd3f5b6aaab7c6, 0xa35e5988a1ceb6cf, 0xad3acfd0baa32cf2, 0xc3da415ceed17ea2, 0x77cdbdd9a00271ce, 0x2e0509226b862337, 0x61b9f9e7f3c31172, 0x6f196a33870950d1, 0xa6cea17cfbc45e6, 0x2c8d2caca4d2eab1]

private theorem rounds054_2 : sixRounds 12 (by decide) quarter054_2 = quarter054_3 := by
  decide +kernel

private theorem rounds054_3 : sixRounds 18 (by decide) quarter054_3 = state055 := by
  decide +kernel

private theorem perm054 : KECCAK.f1600 absorbed054 = state055 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds054_0, rounds054_1, rounds054_2, rounds054_3]
  rfl

theorem block054 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes054 ++ tail) state054 =
      KECCAK.Bytes.run 0 tail state055 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes054 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb054 ws)) := by
    rfl
  exact (step state054).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words054).trans perm054))

private def absorb055 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x52 0x81 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x80 0x80 0x1 0x4 0x60)) 2 (by decide) (UInt64.ofBytes 0x81 0x22 0x60 0x52 0x82 0x3 0x81 0x82)) 3 (by decide) (UInt64.ofBytes 0xcb 0x58 0x61 0x80 0x1 0x20 0x60 0x52)) 4 (by decide) (UInt64.ofBytes 0x91 0x1 0x40 0x60 0x39 0x91 0x22 0x60)) 5 (by decide) (UInt64.ofBytes 0x3 0x91 0x80 0x51 0x40 0x60 0x50 0x50)) 6 (by decide) (UInt64.ofBytes 0x7f 0x54 0x80 0x1 0x60 0x5b 0xfd 0x90)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x0 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x78 0x7f 0x51 0x40 0x60 0x55 0x90 0x16)) 12 (by decide) (UInt64.ofBytes 0xdf 0x13 0x2f 0x9e 0x68 0x2f 0x86 0x5)) 13 (by decide) (UInt64.ofBytes 0xd1 0x3a 0xad 0x82 0xf4 0x2f 0x6 0x9f)) 14 (by decide) (UInt64.ofBytes 0xed 0x11 0x79 0x84 0xe0 0xa9 0xac 0x12)) 15 (by decide) (UInt64.ofBytes 0x90 0x33 0x5b 0x52 0x8c 0x15 0x2e 0x83)) 16 (by decide) (UInt64.ofBytes 0x1 0x60 0x5b 0x56 0xa1 0x90 0x0 0x60))

private def absorbed055 : Vector UInt64 25 :=
  #v[0x8568502a4086f0f, 0xa669b08e01b738d4, 0xa49414a20f435144, 0x159f42ab5591684d, 0x17c7a89a976078de, 0x894b360951bd6504, 0xdb9964b1d8cd8922, 0x200f5805bdeb7df9, 0x153be306500e3499, 0xd6652fa4dc3cdc77, 0xfdbde426c6f542b2, 0x8559f93c3ff9d0d9, 0xe02df580a7a9a3f4, 0x954de27097700adc, 0x2987fe17302c82ac, 0x9447a2cf7fda638f, 0x47a82db78b427eaf, 0xa1e0b9fd5f6a3dd4, 0xa9b307b77fdab7bb, 0xd43903166c06b7eb, 0x6b037d0eb706a9c8, 0x619987b8b9c35698, 0xf35faf4ebaa9dcb9, 0xf974f93c8ad4016e, 0x7503e359d5a42c5b]

private theorem words055 : absorb055 state055 = absorbed055 := by
  decide +kernel

private def quarter055_1 : Vector UInt64 25 :=
  #v[0x81a07f34d62fe9f, 0x4106091e86aeb00c, 0xab3cf1f2a05ec281, 0xaaa403fbb1769a6e, 0xdade266e1456dc1f, 0x5ab6221885aebfeb, 0xf3365c6047714cb0, 0x1ac732a9ce925ec9, 0x92228cb7fcfc8103, 0x5aadd3baf3293896, 0x4567dd0c6947c7f3, 0xa7aaf946e32ae592, 0xc8eb577c8b348d78, 0x3b271e43617b5811, 0xe4d301cd51b8eaa, 0x657e3b360b6a4c0e, 0x2df88d25f734ac70, 0x57b5a5208529370b, 0xafd5966918a73a5d, 0xbbc299ef593d6b13, 0xebea3f39f58fe9d9, 0x69dbe9427af948b8, 0xb5ed0a9cc792ff45, 0x9264a7a15baa60aa, 0x2229151f36c5385d]

private theorem rounds055_0 : sixRounds 0 (by decide) absorbed055 = quarter055_1 := by
  decide +kernel

private def quarter055_2 : Vector UInt64 25 :=
  #v[0xc60c746a82727f66, 0xb112269541493169, 0x9a5a0d2e4a0421a9, 0xf759959f4898e9, 0xa0b8e34de7f7e8f8, 0xdac24566cf541f75, 0x2ba10e544f4d00e7, 0xf28d1f6dee6ca184, 0xb446ed6c0c31775d, 0x53ced5ca9875086f, 0x4301fba38abcb444, 0x8f0d743e0883366b, 0xc8942b99d709d8d9, 0x8d32632076d5c935, 0xfc6980e2f48b1e11, 0x8d7eb03ca73ad4fa, 0x5d1f0df480b12b05, 0x66cad1cfc94b2f96, 0x5ada325748be1b89, 0xa760386d7b27f39b, 0xbc8b940a05bb47c7, 0x7a19adc9fc3b5042, 0x7c516aec5f05ab62, 0x7581595814f397b9, 0x3e2a0745b1e6cf78]

private theorem rounds055_1 : sixRounds 6 (by decide) quarter055_1 = quarter055_2 := by
  decide +kernel

private def quarter055_3 : Vector UInt64 25 :=
  #v[0x459ecf148a60248d, 0x2772f3b37541b548, 0x17f57aa0fd233ec8, 0xd810e22df70dd2ec, 0xa8a739aa6a2a5d6e, 0x75ff1f6bd8e283fb, 0xf87768a6eeb459c0, 0x818b7055b4b29f0a, 0x106ea738860937e, 0x66c05f585f5c5070, 0xa09de6b568436ef6, 0xca690b6b02aa0f6, 0xc8629322bfaaab9f, 0x7ae3d6bacd0d23a8, 0xf0463bea91a15b2b, 0x2e940e8f8666a1c4, 0xa9a2ff785bdcec8e, 0x2cd98651b55aafed, 0x86465bdad31f8c91, 0xe00cbf915a874879, 0x1bd22e0e2c2c7dea, 0x1a87de89bc81c87d, 0xac7435b8edb9834, 0x33c9ddc8d065ac04, 0xe7fe3bc9a3097212]

private theorem rounds055_2 : sixRounds 12 (by decide) quarter055_2 = quarter055_3 := by
  decide +kernel

private theorem rounds055_3 : sixRounds 18 (by decide) quarter055_3 = state056 := by
  decide +kernel

private theorem perm055 : KECCAK.f1600 absorbed055 = state056 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds055_0, rounds055_1, rounds055_2, rounds055_3]
  rfl

theorem block055 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes055 ++ tail) state055 =
      KECCAK.Bytes.run 0 tail state056 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes055 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb055 ws)) := by
    rfl
  exact (step state055).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words055).trans perm055))

private def absorb056 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x1 0x74 0x90 0x0 0x60 0x54)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x15 0x16 0xff 0x60 0x4 0x90 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x51 0x80 0x40 0x60 0x57 0xd0 0x1d 0x61)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8 0x7f)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x82 0x4 0x60 0x20 0x60 0x52 0x81 0x0)) 10 (by decide) (UInt64.ofBytes 0x1 0x82 0x24 0x60 0x10 0x60 0x52 0x1)) 11 (by decide) (UInt64.ofBytes 0x62 0x61 0x73 0x75 0x61 0x50 0x7f 0x52)) 12 (by decide) (UInt64.ofBytes 0x73 0x75 0x61 0x70 0x20 0x3a 0x65 0x6c)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x64 0x65)) 14 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x90 0x52 0x1 0x82 0x44 0x60 0x0 0x0)) 16 (by decide) (UInt64.ofBytes 0x1 0x64 0x60 0x3 0x90 0x81 0x90 0x51))

private def absorbed056 : Vector UInt64 25 :=
  #v[0x367de9b20dd3b28f, 0x3940793e929dcec2, 0xaf0903320e177485, 0xfb3c18d627d7edf, 0x87f052e835bc8a8c, 0xb0b5dfa06fb5df90, 0x32e03c52a2365f10, 0x28efb276934828ec, 0x61583d2011ffb301, 0xb5af16133ed85dc, 0x2dd618cffc171bcf, 0xe0a96233fdb79656, 0x4ba5c46f1cb289a1, 0xb0598e1ff8212dc9, 0x50af5653ab8a57d0, 0x5fea87bfa8a56e2d, 0xb57413193468bc52, 0x4bb50e384286c962, 0xc6e49f0b79e28dbc, 0xef33a05271e1fba2, 0x3dd2cc51b935e155, 0xc9761fccd3565e2c, 0x82d98a1d37ac2f4, 0x8f7d3a4d4ee27d67, 0x7052e8271cefecd5]

private theorem words056 : absorb056 state056 = absorbed056 := by
  decide +kernel

private def quarter056_1 : Vector UInt64 25 :=
  #v[0x4bd49bd7c5f6f18f, 0x10597a27d91fad3b, 0x5edffc98ed7e07c7, 0x279d45025a7837b3, 0x912cdbb154c4e7f7, 0xcebd11377b48a4fd, 0xe295f66aa8c45481, 0x553fb1423a3ec380, 0x7b27a86966cfd25f, 0xaa22fd5a7c29acdb, 0xecb67ca632bd09bf, 0x401717364812e214, 0x583d73da3c685981, 0xf3bf665838790fc3, 0xd2a861ae50149c92, 0xf7168c859c9ff8b4, 0xa1e5da5eed836030, 0x8186037ad61e91b, 0x74c3b3d1fcca8f7f, 0xa66b902b59fa1590, 0xae9fa37c8849bee, 0x507b90cb1f8c2fa6, 0x16f3cf07b582cd79, 0xabcbb72e42ad35a7, 0x860ae255a1a18df]

private theorem rounds056_0 : sixRounds 0 (by decide) absorbed056 = quarter056_1 := by
  decide +kernel

private def quarter056_2 : Vector UInt64 25 :=
  #v[0x38ef71ab3b3520dc, 0x4f8c47abc51de72a, 0x959cd47d12f8ec77, 0x96b9b403d76b51ff, 0x338c3df51ed1fb18, 0xd16e676559e83773, 0x518074ba00d10be9, 0x4442b7a00d14bfd8, 0xf3c894794f41e128, 0xb6d1f2c72422aebc, 0x7b5aec09ec11e10e, 0xa0219867f548fbf3, 0x86c908e2b7667795, 0x283f98931c414b0b, 0xdb8b3e299eaa31e, 0xdebfb6df5955118, 0xf44b49d701286c18, 0x1d272665e1621cbc, 0x8e4f0b5643dc6fd7, 0xbe9b607aa09f3ad1, 0x8687ff7dd5130536, 0xbc802ca116a6e337, 0x31f192aca9a7b733, 0x478e359500ca0782, 0x5bd5a4b2e1f3683f]

private theorem rounds056_1 : sixRounds 6 (by decide) quarter056_1 = quarter056_2 := by
  decide +kernel

private def quarter056_3 : Vector UInt64 25 :=
  #v[0x68a83b658653959d, 0x87e88af3862b7f2b, 0xec01d424c444ab76, 0x959efe05e0a0f055, 0xedb40d9c5da9947e, 0xa01582b7a09af211, 0x9c08b8a853703ffe, 0xb4dcdbafe322b517, 0x9d9311fa0d8f0404, 0xff346b7dada4280c, 0x385f5808fc7965b0, 0x67f489b644d3ceea, 0x82bd7720a7a6a5a1, 0xee2fa8b17e41db62, 0xde6a9f6c92312e83, 0xd452b4c738b139d2, 0x9fcf580e25010aec, 0x1564f8e79163de28, 0x34e51477be581536, 0xb3d97758c805c6e, 0xff79247f9d523a1a, 0x4e7d9725f5b8c956, 0x53f7677ab0042a07, 0x953eb5ff1434dcf9, 0x2fdc4f985d8ab534]

private theorem rounds056_2 : sixRounds 12 (by decide) quarter056_2 = quarter056_3 := by
  decide +kernel

private theorem rounds056_3 : sixRounds 18 (by decide) quarter056_3 = state057 := by
  decide +kernel

private theorem perm056 : KECCAK.f1600 absorbed056 = state057 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds056_0, rounds056_1, rounds056_2, rounds056_3]
  rfl

theorem block056 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes056 ++ tail) state056 =
      KECCAK.Bytes.run 0 tail state057 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes056 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb056 ws)) := by
    rfl
  exact (step state056).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words056).trans perm056))

private def absorb057 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x81 0x90 0x0 0x60 0x33 0x5b 0xfd 0x90)) 1 (by decide) (UInt64.ofBytes 0x40 0x60 0x52 0x20 0x60 0xc 0x60 0x52)) 2 (by decide) (UInt64.ofBytes 0x1e 0x61 0x16 0xff 0x60 0x54 0x20 0x90)) 3 (by decide) (UInt64.ofBytes 0xc3 0x8 0x7f 0x51 0x40 0x60 0x57 0x38)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0xa0 0x79)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x52 0x81 0x0 0x0 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x80 0x80 0x1 0x4 0x60)) 9 (by decide) (UInt64.ofBytes 0x81 0x21 0x60 0x52 0x82 0x3 0x81 0x82)) 10 (by decide) (UInt64.ofBytes 0x34 0x57 0x61 0x80 0x1 0x20 0x60 0x52)) 11 (by decide) (UInt64.ofBytes 0x91 0x1 0x40 0x60 0x39 0x91 0x21 0x60)) 12 (by decide) (UInt64.ofBytes 0x3 0x91 0x80 0x51 0x40 0x60 0x50 0x50)) 13 (by decide) (UInt64.ofBytes 0x81 0x81 0x0 0x60 0x33 0x5b 0xfd 0x90)) 14 (by decide) (UInt64.ofBytes 0x40 0x60 0x52 0x20 0x60 0x3 0x60 0x52)) 15 (by decide) (UInt64.ofBytes 0x61 0x15 0x16 0xff 0x60 0x54 0x20 0x90)) 16 (by decide) (UInt64.ofBytes 0x8 0x7f 0x51 0x40 0x60 0x57 0xa1 0x1e))

private def absorbed057 : Vector UInt64 25 :=
  #v[0x4631b0222b0a38be, 0xafb2dbda589944e3, 0xd8ceb07f435f5926, 0xcf97ec1b2d83b3c5, 0x7593f131021ea61f, 0xb92f2a29a15d11e1, 0x539b61513ebe878a, 0x8917ee84634dc2c7, 0xf5bbee4fedaa83f0, 0x9ea8a6ce43c27b8c, 0x3899568c2b9c6881, 0xb1b3984f55120ca5, 0x16a9d59325458cf6, 0x25b2b5b2b342860c, 0x1c9dd761abf20d28, 0xcc6cd90eea8f032f, 0x42ca07c45af0735a, 0x63ec73ea14b1b5ec, 0x5a24d5d9cd31c6b, 0xf3630a1a5d6f3706, 0x8f99d14f924d7f11, 0x16995fbfdcd7e110, 0xdd87134605028e68, 0x43cc5338d3a0849f, 0x32871e085c70fd82]

private theorem words057 : absorb057 state057 = absorbed057 := by
  decide +kernel

private def quarter057_1 : Vector UInt64 25 :=
  #v[0x419d84312406803a, 0xbf66fd4b67940031, 0xe0685cbf7f03c92e, 0xa2b2b8a9d726e96d, 0x9a8fd05b7a7fadc9, 0x93b0703e8556f92a, 0x9effff25b49d2955, 0xda86c1afcfb1526, 0x3cf115eb90648121, 0x1e70f5444504a49e, 0xf2d330c5091a7847, 0xaaa956c8926fc7e7, 0x668bbbb8724a7551, 0xdf99d4b2c9f22640, 0x6df966515a27e5d, 0x5281d6c1fbd22bd8, 0xe0722e20c400b8e7, 0xc7fc113643d7bb23, 0x96e24e330c83d643, 0x1f1095274de4feef, 0x8664c924c7ee4a5, 0xe1280fe679b461cc, 0x762653fe54c8a58d, 0xaca41e0d78c80bfa, 0xdb74d6100904f064]

private theorem rounds057_0 : sixRounds 0 (by decide) absorbed057 = quarter057_1 := by
  decide +kernel

private def quarter057_2 : Vector UInt64 25 :=
  #v[0x991c8657279ced4a, 0xfeb66da1c90f2057, 0xcc99f84ca2e01fac, 0x8ffa6050f5d39d7a, 0xa3f4623cf6c2587b, 0x739d6c343d2d949a, 0x96959b9d0990cbb7, 0xd91987dc4e6448c4, 0xc3ae0d3e6a420582, 0x7b4c721d896a7e2b, 0xde8ede6eda99e60c, 0x818e4842e33adc4b, 0xba16955f87474317, 0xe4d77799cfc934af, 0x412d3d6a98607745, 0x76f200e7684f1c, 0x407cfce8ade0c1ba, 0xf7624bf3b9cf475f, 0xe05e24c12c8b2b5a, 0x4c3ce009da3d880d, 0xc658ef2e8f725662, 0x132951e26909d4da, 0xb79cebc9b5d3f24a, 0x853bc72f26ad4934, 0x7b122e553831b606]

private theorem rounds057_1 : sixRounds 6 (by decide) quarter057_1 = quarter057_2 := by
  decide +kernel

private def quarter057_3 : Vector UInt64 25 :=
  #v[0xfc95e9c444a738e6, 0xfe76a3143c3af16a, 0x9cf032508152e916, 0xb7e124dbbfd5f477, 0x4c58928e2f010cf6, 0x1d254703e2bb90b1, 0x6b4e5fabedf79c6b, 0x32219bcf471b7d0, 0xe87efadfe7102bf2, 0x102613f2bebcdfe4, 0x15e58f6a759dd364, 0x890dcbc09dfc9a3d, 0xdd3566058fcdc614, 0x1fce176b4bd9ddee, 0x750d9843623451fe, 0xde0d3c06b05c0619, 0x8033a50facffbcb9, 0x6107caa87204ff77, 0xee94f38b12641533, 0xfe0a052c7e059cd3, 0xbbd1c0d291cdfd54, 0x26370f482f40c5d4, 0x7b4b5cd5fbc3e0cd, 0xab5289fb695d0ab9, 0x7d2a95caf5f8e833]

private theorem rounds057_2 : sixRounds 12 (by decide) quarter057_2 = quarter057_3 := by
  decide +kernel

private theorem rounds057_3 : sixRounds 18 (by decide) quarter057_3 = state058 := by
  decide +kernel

private theorem perm057 : KECCAK.f1600 absorbed057 = state058 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds057_0, rounds057_1, rounds057_2, rounds057_3]
  rfl

theorem block057 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes057 ++ tail) state057 =
      KECCAK.Bytes.run 0 tail state058 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes057 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb057 ws)) := by
    rfl
  exact (step state057).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words057).trans perm057))

private def absorb058 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x81 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x20 0x60 0x80 0x80 0x1 0x4 0x60 0x52)) 5 (by decide) (UInt64.ofBytes 0x25 0x60 0x52 0x82 0x3 0x81 0x82 0x1)) 6 (by decide) (UInt64.ofBytes 0x59 0x61 0x80 0x1 0x20 0x60 0x52 0x81)) 7 (by decide) (UInt64.ofBytes 0x1 0x40 0x60 0x39 0x91 0x25 0x60 0xc5)) 8 (by decide) (UInt64.ofBytes 0x91 0x80 0x51 0x40 0x60 0x50 0x50 0x91)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x5b 0xfd 0x90 0x3)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x52 0x81 0x90 0x0 0x60 0x16 0x84 0xff)) 13 (by decide) (UInt64.ofBytes 0x90 0x40 0x60 0x52 0x20 0x60 0x3 0x60)) 14 (by decide) (UInt64.ofBytes 0x15 0x16 0xff 0x60 0x90 0x84 0x54 0x20)) 15 (by decide) (UInt64.ofBytes 0x7f 0x51 0x40 0x60 0x57 0x22 0x1f 0x61)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8))

private def absorbed058 : Vector UInt64 25 :=
  #v[0x6b4f1e893705c47d, 0x62f8c075aa930da2, 0xc5d8d2c4baedad35, 0xda4e947cc387f42f, 0x21cb081d08842947, 0x3e57210bf3481f3d, 0xa3228e6758d684a3, 0xd3e2a47eab266fde, 0x1db336ca7a4b5e83, 0x2cca2f93aa33c5a3, 0x8166ee226ce2fa81, 0xd43a5c3a11afd0f9, 0xe8054447a0127987, 0xeede30768330d962, 0x4a3bca023d76915b, 0xaa996f66c275268d, 0x403d9a26e322165d, 0xc4ee479f992dc680, 0x8b1ecdc8bf7145d2, 0x5ce12b59ed0f0ae7, 0x81cf1bd04d9642, 0x765e8d3ce8a4e3ee, 0x8bfda719cfcb685, 0xa4d691d2f1e3b239, 0x7e436e9452a4f548]

private theorem words058 : absorb058 state058 = absorbed058 := by
  decide +kernel

private def quarter058_1 : Vector UInt64 25 :=
  #v[0x7892cc239746aa1b, 0xad8682676dfea1b1, 0x3296aba945b0919f, 0x5136855d06d6129d, 0xbde3a2ea14b9f32a, 0xe084791a5dcb659e, 0x1b3f49780d4b1ed8, 0xa58981a236e63a57, 0xec62adea26bc752d, 0x794ffc65613b18fd, 0x9098e0fb1e9f36b8, 0xd8a83003c72bdeb4, 0xe5618183cfac975e, 0xbe7ab34a2c5b0486, 0x950c15650bd4f303, 0x9f273a25177a6dd0, 0x9008ecff87b198b5, 0xa75004c85c92bd7b, 0x156b13a17b3530be, 0x812a0787c62e6dca, 0xde67b1bf927e4aad, 0xa48b4a6389782e8f, 0x83e1d30b0098e11f, 0x5805fff6530ff5, 0xf465fe9dc540ac94]

private theorem rounds058_0 : sixRounds 0 (by decide) absorbed058 = quarter058_1 := by
  decide +kernel

private def quarter058_2 : Vector UInt64 25 :=
  #v[0x8165364cc64b8524, 0x2881906eeaafb884, 0x4035ecbeb5c720e9, 0xd04c8a964de9b88c, 0xc63b7b1eaaea265a, 0x1ffd6a3e501cf746, 0x2a76015e6731a52e, 0x78327301f9ce937a, 0x78c0ca278e637a7d, 0x3df1ea3e1b57b2fa, 0xfa08314f637c9c64, 0xad47ebc61f335ba2, 0xe9a580375fdf126f, 0x2b0df5e2475b0e64, 0x59d02f636561d139, 0x88b89da23af7b102, 0x59dc7dca22716f02, 0x114208bcc13dd3c9, 0xcf1916abda0b9783, 0x447fe63306eaf804, 0x392b74baaa8d8f86, 0x944334a83eecbb52, 0x90960afc1d3ec9a0, 0x2873bc9d4e087443, 0x5c44649e8e1f34e4]

private theorem rounds058_1 : sixRounds 6 (by decide) quarter058_1 = quarter058_2 := by
  decide +kernel

private def quarter058_3 : Vector UInt64 25 :=
  #v[0xdc9d5f91a3741a0, 0xe3de9a44b11973c4, 0xb35e3761e6704679, 0xfa0829ad4545214, 0x664e59af4eff1e0a, 0x93d3dbbc846964cc, 0x5609ce35f366ce5, 0xcc8734ddbef91228, 0x4dadc7a99f7a324f, 0xee59230bd1adde35, 0x4862b7ae01d2afe5, 0x328f5c0a4909aa37, 0xdf882297f27b534f, 0x5cb1f4cbf4019d64, 0x10fc39d0613dfe14, 0x8a2e4a6c6184c242, 0x3f26aa2ac4389829, 0xb7402435102c0f06, 0xcfc259994e06206c, 0x77d2025ad3faf5c0, 0x4343c12cdca305d6, 0x3846d972bd3f03d, 0x5119b684f2e1365, 0x714bdb5f24bdbca0, 0xb4bd0aa112163339]

private theorem rounds058_2 : sixRounds 12 (by decide) quarter058_2 = quarter058_3 := by
  decide +kernel

private theorem rounds058_3 : sixRounds 18 (by decide) quarter058_3 = state059 := by
  decide +kernel

private theorem perm058 : KECCAK.f1600 absorbed058 = state059 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds058_0, rounds058_1, rounds058_2, rounds058_3]
  rfl

theorem block058 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes058 ++ tail) state058 =
      KECCAK.Bytes.run 0 tail state059 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes058 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb058 ws)) := by
    rfl
  exact (step state058).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words058).trans perm058))

private def absorb059 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x60 0x80 0x80 0x1 0x4 0x60 0x52 0x81)) 4 (by decide) (UInt64.ofBytes 0x60 0x52 0x82 0x3 0x81 0x82 0x1 0x20)) 5 (by decide) (UInt64.ofBytes 0x61 0x80 0x1 0x20 0x60 0x52 0x81 0x25)) 6 (by decide) (UInt64.ofBytes 0x40 0x60 0x39 0x91 0x25 0x60 0xc5 0x59)) 7 (by decide) (UInt64.ofBytes 0x80 0x51 0x40 0x60 0x50 0x50 0x91 0x1)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x5b 0xfd 0x90 0x3 0x91)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x57 0x8e 0x1f 0x61 0x16 0x85 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x40 0x60)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 16 (by decide) (UInt64.ofBytes 0x4 0x60 0x52 0x81 0x0 0x0 0x0 0x0))

private def absorbed059 : Vector UInt64 25 :=
  #v[0x87f29f95d44c6440, 0xea10fb535418d7a5, 0xb1a2252bdd2c67fc, 0x6c96eab482bb2689, 0x82179226bc3eedbe, 0x512c35d2c095cdb, 0x3420e4ef315eabc4, 0x4ca2a85de527ee4e, 0x4d798bc7163e0788, 0xb80c8588c306173a, 0xd91204d2de5d1960, 0xdc7f201505cd7fda, 0xb028584c96bb48b1, 0x932fae70d985d454, 0x275124e6f0cd5fa3, 0xf933b827194a9f19, 0xf4e897ed4bed3ec4, 0x92db185ad301746e, 0x4b89a6baef41f090, 0x50f19f4106a404d3, 0x1ba1690149d2f761, 0x9d959456cb7bdcfe, 0x7522aa6894e1d316, 0xbde0cacec634a70d, 0x745970bf5a6a95bb]

private theorem words059 : absorb059 state059 = absorbed059 := by
  decide +kernel

private def quarter059_1 : Vector UInt64 25 :=
  #v[0x921d185df2d48c51, 0xad8f21907e0e65b8, 0x683aaa8a81483721, 0x2daab306aeb854d2, 0xb5eed6f9d306965d, 0x970c82db02d07aad, 0x6dc895e98fa1edc9, 0x52c2ce074fd761bd, 0xb74ea84158912e3c, 0x4e9c809a75541e9, 0x12f436b7f79397ef, 0xb02bed1f46aedaf5, 0x592e6e6a202909df, 0x328482e67d515338, 0x253ff66e7723c266, 0x11ac19ff8c58671, 0x98af15bf49b6edad, 0x69e614c256ce35f1, 0x7619a8cd32ef9eaf, 0xa59eb4a51e2c998c, 0xd01603df24a08ac, 0xb17309ed3d49a0cd, 0x98567860a8cec87b, 0xa9856f9d5f40366d, 0x7c931a96708a292]

private theorem rounds059_0 : sixRounds 0 (by decide) absorbed059 = quarter059_1 := by
  decide +kernel

private def quarter059_2 : Vector UInt64 25 :=
  #v[0x9dce747272f78cdd, 0x43e5608da71b01f4, 0xe7d5ee08593f1fd3, 0xee36c57e31f96a80, 0x3980631e9e85ab2a, 0xb75e35fc8875f808, 0xcc24c7d57313b602, 0x507039390217f37d, 0x21d8013a02b0ee66, 0xce2fcc45efff5239, 0x3af1ca36405de43e, 0x456b5b5f8c400c28, 0x2d6a3ba13f6009f7, 0xeb1d0ab183a795e2, 0x157a90910045ae81, 0xcb0572eda91fdfae, 0x4b77542659b9ee16, 0xd869da2a98aac731, 0xf39639d1ac75e944, 0xbe048dc4336c33ba, 0xcee20bea2f6f7ced, 0x8b37f9503818ef29, 0xdfb58fc5ae9a6963, 0x7bb1c14f35f395bd, 0x965e2fad97069030]

private theorem rounds059_1 : sixRounds 6 (by decide) quarter059_1 = quarter059_2 := by
  decide +kernel

private def quarter059_3 : Vector UInt64 25 :=
  #v[0xee5554868c09fef0, 0x6946af39e67ec4e6, 0xc411c61d36f72b1e, 0x35b32b091cea3a16, 0xb20d2ed1594eaa4c, 0x391000b19d9c0f08, 0x538fe610a6a54dd9, 0xc69652a4103989c0, 0x151e61f8cc43d370, 0x8d90219878357dd9, 0xb61f3a70128c9073, 0x98b5d0df8f9f929c, 0xdb54e9ccf8c92702, 0x2830a3e2f4908c8d, 0x506be1b2a56fd5af, 0xb380523ddeb38cb6, 0x4610ebbbedc1e415, 0x1e560bc14fb0c97d, 0xacae4bb3b19ffd30, 0x4e87b99ff5f06544, 0x7a60c71ef5a6e782, 0xa157ae54b680d15d, 0xd3cf2928853b497, 0xd39d24b401ba3c71, 0x50804d70d32a5c31]

private theorem rounds059_2 : sixRounds 12 (by decide) quarter059_2 = quarter059_3 := by
  decide +kernel

private theorem rounds059_3 : sixRounds 18 (by decide) quarter059_3 = state060 := by
  decide +kernel

private theorem perm059 : KECCAK.f1600 absorbed059 = state060 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds059_0, rounds059_1, rounds059_2, rounds059_3]
  rfl

theorem block059 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes059 ++ tail) state059 =
      KECCAK.Bytes.run 0 tail state060 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes059 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb059 ws)) := by
    rfl
  exact (step state059).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words059).trans perm059))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
