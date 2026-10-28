import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb012 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x1 0x64 0x50 0x50 0x91)) 1 (by decide) (UInt64.ofBytes 0x57 0xfa 0x5 0x61 0x15 0x11 0x81 0x0)) 2 (by decide) (UInt64.ofBytes 0x83 0x1 0x82 0x5b 0xfd 0x80 0x0 0x60)) 3 (by decide) (UInt64.ofBytes 0x6 0x61 0x15 0x11 0x1 0x82 0x20 0x60)) 4 (by decide) (UInt64.ofBytes 0x80 0x5b 0xfd 0x80 0x0 0x60 0x57 0xc)) 5 (by decide) (UInt64.ofBytes 0x60 0x84 0x91 0x1 0x20 0x60 0x90 0x35)) 6 (by decide) (UInt64.ofBytes 0x1 0x64 0x11 0x1 0x84 0x2 0x83 0x1)) 7 (by decide) (UInt64.ofBytes 0x15 0x17 0x11 0x83 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0xfd 0x80 0x0 0x60 0x57 0x2e 0x6 0x61)) 9 (by decide) (UInt64.ofBytes 0x1 0x1f 0x60 0x80 0x80 0x90 0x91 0x5b)) 10 (by decide) (UInt64.ofBytes 0x20 0x60 0x2 0x4 0x91 0x80 0x20 0x60)) 11 (by decide) (UInt64.ofBytes 0x60 0x1 0x81 0x90 0x51 0x40 0x60 0x1)) 12 (by decide) (UInt64.ofBytes 0x81 0x90 0x91 0x92 0x93 0x80 0x52 0x40)) 13 (by decide) (UInt64.ofBytes 0x80 0x83 0x83 0x1 0x20 0x60 0x52 0x81)) 14 (by decide) (UInt64.ofBytes 0x91 0x1 0x92 0x0 0x60 0x37 0x84 0x82)) 15 (by decide) (UInt64.ofBytes 0x93 0x94 0x95 0x92 0x50 0x52 0x91 0x90)) 16 (by decide) (UInt64.ofBytes 0x91 0x35 0x50 0x93 0x1 0x81 0x20 0x60))

private def absorbed012 : Vector UInt64 25 :=
  #v[0xbff7df1160b925b0, 0x4fd8b9c6c7947d92, 0x49f71445c6d7bd3c, 0x2fd67aafdc17434, 0xcb81296246ea982c, 0xc2ee25dedfc70981, 0x1f217798d097849d, 0xce3dce10a29178ad, 0xe27b72a39609e31d, 0x12dedb0d62d99e5c, 0x397777852ee23e89, 0x706738abe62ec030, 0xb1b65db584d9ad44, 0xc8e0baca8b3198a9, 0x77aab1adfb9de03b, 0x354181c4e51077b6, 0xe23a3739b8d3c367, 0x598a4e482531c3c5, 0x9b3fe643fcdbb8c1, 0xe0a4851596f6b8a5, 0x6da55110befac5f3, 0xd51f641723de5da7, 0x9ffdb4d75fa44c77, 0xe5841ac348a459ff, 0xa7bf2b46e00f48d3]

private theorem words012 : absorb012 state012 = absorbed012 := by
  decide +kernel

private def quarter012_1 : Vector UInt64 25 :=
  #v[0x7f4231d7690b1dce, 0x6172004cb4423da2, 0xd5b0264e1cc352e9, 0xff5f87444cf3adc3, 0xa652e43a4d758679, 0x1d32ff35bf214cb2, 0x237fd9f68c0f61ee, 0x5a05d166523555e7, 0xd838c608102a158b, 0xeb5a343f4c6a76ba, 0x2367d47b1de3b5f9, 0xa4c3cb377a14b9f0, 0x342f3dd042022c38, 0xd9cc54fe1f324566, 0x3da89e7be4512880, 0x8a00b2cd742c1b36, 0x9fb3f362e97a87be, 0xe95d1dee9e31c4af, 0x1b5b15da10910ea9, 0x1b558eb56e51fb99, 0xa911311e0ca6dfb6, 0x82258468d68bbda4, 0xcc5e1648117e2ea2, 0xcdebd6c25e6b34d3, 0xabe20ec7f765a9f8]

private theorem rounds012_0 : sixRounds 0 (by decide) absorbed012 = quarter012_1 := by
  decide +kernel

private def quarter012_2 : Vector UInt64 25 :=
  #v[0x95c244bb12ce4bb9, 0xe03bba02ecbc24c4, 0x55e139aabf4f41c, 0xd7ed15d4e7b9a65a, 0x739a5bfd56bba799, 0x9d3d2574b1a801e7, 0xdcc5daa08239bf6f, 0xac42fcbfa2f68b0b, 0xb84bf1579df14e36, 0x2ae28a377a72c0fe, 0xcd2ba5a4b6260e9d, 0x41606904eb29a6ba, 0x462b310e9352c29e, 0xec709a66a6094acd, 0x12c61d1057ee0a7e, 0xdac913cc9ce2bda8, 0x48cbb7008b43c07, 0xc817ca63babee6c4, 0xab12e9301d425cfd, 0x717a2bf40c0afc07, 0xee7282bbcec7fe59, 0xd2113a515b85c53, 0xac5b9ac8128d68a7, 0xfe91a75570a73ef0, 0x79bd03da399fecdf]

private theorem rounds012_1 : sixRounds 6 (by decide) quarter012_1 = quarter012_2 := by
  decide +kernel

private def quarter012_3 : Vector UInt64 25 :=
  #v[0xe39cdacd059a7e41, 0xc69a637327dfea31, 0xd3d1455cde5ffa1f, 0x460a3d1eef38c52e, 0xebe517e3f4078f4f, 0xea1a79dca8681823, 0xaeef6f0af6a09414, 0x2a481f2c3878dad7, 0xb1bd399d7a833282, 0xc57a041c2da892a9, 0xa15f3fbf87be4385, 0x7fe965064ebbdc5, 0x638342232aeec81f, 0xa8216f6419599263, 0x29f3d753bc7a50da, 0xb2274fc3fa2a9a73, 0xe02aad7d8e1300d2, 0x9571b0c865093656, 0x380699bc7b33e40f, 0x23f349727ff2f3dd, 0x649025e9080d3934, 0x1165cb8732bf50be, 0xe9af6a983b6d935f, 0xff8b5423d44efcff, 0x5f3ed331822f0d13]

private theorem rounds012_2 : sixRounds 12 (by decide) quarter012_2 = quarter012_3 := by
  decide +kernel

private theorem rounds012_3 : sixRounds 18 (by decide) quarter012_3 = state013 := by
  decide +kernel

private theorem perm012 : KECCAK.f1600 absorbed012 = state013 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds012_0, rounds012_1, rounds012_2, rounds012_3]
  rfl

theorem block012 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes012 ++ tail) state012 =
      KECCAK.Bytes.run 0 tail state013 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes012 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb012 ws)) := by
    rfl
  exact (step state012).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words012).trans perm012))

private def absorb013 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x1 0x64 0x50 0x50)) 1 (by decide) (UInt64.ofBytes 0x60 0x57 0x81 0x6 0x61 0x15 0x11 0x81)) 2 (by decide) (UInt64.ofBytes 0x60 0x83 0x1 0x82 0x5b 0xfd 0x80 0x0)) 3 (by decide) (UInt64.ofBytes 0x93 0x6 0x61 0x15 0x11 0x1 0x82 0x20)) 4 (by decide) (UInt64.ofBytes 0x35 0x80 0x5b 0xfd 0x80 0x0 0x60 0x57)) 5 (by decide) (UInt64.ofBytes 0x1 0x60 0x84 0x91 0x1 0x20 0x60 0x90)) 6 (by decide) (UInt64.ofBytes 0x0 0x1 0x64 0x11 0x1 0x84 0x2 0x83)) 7 (by decide) (UInt64.ofBytes 0x61 0x15 0x17 0x11 0x83 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x80 0x0 0x60 0x57 0xb5 0x6)) 9 (by decide) (UInt64.ofBytes 0x60 0x1 0x1f 0x60 0x80 0x80 0x90 0x91)) 10 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x2 0x4 0x91 0x80 0x20)) 11 (by decide) (UInt64.ofBytes 0x40 0x60 0x1 0x81 0x90 0x51 0x40 0x60)) 12 (by decide) (UInt64.ofBytes 0x81 0x81 0x90 0x91 0x92 0x93 0x80 0x52)) 13 (by decide) (UInt64.ofBytes 0x82 0x80 0x83 0x83 0x1 0x20 0x60 0x52)) 14 (by decide) (UInt64.ofBytes 0x90 0x91 0x1 0x92 0x0 0x60 0x37 0x84)) 15 (by decide) (UInt64.ofBytes 0x50 0x50 0x50 0x95 0x92 0x50 0x52 0x91)) 16 (by decide) (UInt64.ofBytes 0x50 0x50 0x92 0x16 0xff 0x60 0x35 0x81))

private def absorbed013 : Vector UInt64 25 :=
  #v[0xfa2c479b13941be4, 0xd8015d3d25a13d92, 0x80c23c6c7e5993b7, 0x1e6283d9bde10d1c, 0xd778f85c57f2c88b, 0xe5183fa8b23d9b41, 0x97beff0da505548d, 0xa248dde55a6d8bab, 0x6f5aa6fe1827c8a1, 0xeec9450ccc475a8b, 0x806025c8b77e991, 0xdc6bce2858915a5d, 0x9dcc106bc50f328c, 0xde17dfa057a7dfe0, 0xaf3c19beb1d0ea50, 0xc9ca893859b1b4b1, 0xb1cdce412770a4a, 0xe1362ce03df53ef8, 0x60785438f2cdf2b7, 0xba492773210f6863, 0xda95d30d7ab1c45d, 0xdd4e420adc7dd69b, 0x6e6b64293d714ffb, 0xcdd361a87a11432c, 0x686272a9200c9182]

private theorem words013 : absorb013 state013 = absorbed013 := by
  decide +kernel

private def quarter013_1 : Vector UInt64 25 :=
  #v[0xb3c0c339215294ca, 0x8a861c0e90d68dc7, 0xc243a6599dde7004, 0x5d56a20dd5e57729, 0x52f6c0f98b487a7a, 0x5000970ba72a7ea8, 0x6798fa34cd925db5, 0x7daf1455cd8cc9b3, 0x1700680d152a42c3, 0xd5f7a848a250e056, 0xf85fe0754deb5390, 0x32f0840f46644b28, 0xc05d295b09dde536, 0x36709d19388de14c, 0x8d64a99ae3df9b9a, 0xde1038107a30a326, 0x30fcb08c2e3fae6d, 0xfde8e4f5ffb838c8, 0xde0a8195084ba888, 0xd8f3a6273eaa4616, 0xf933e12b9e7a9e79, 0x7891f9fdc044a85f, 0x16841b037ffeebb8, 0x27df3707db55578e, 0x4b77c6823345ce8f]

private theorem rounds013_0 : sixRounds 0 (by decide) absorbed013 = quarter013_1 := by
  decide +kernel

private def quarter013_2 : Vector UInt64 25 :=
  #v[0x6385f50230df50d3, 0xce2bac95fd9636b1, 0x137c390f5fef8e93, 0x677c829696f38e12, 0x2aa3c8480e7e6b6e, 0x4f7ee2238ebc8b2f, 0xcbeba12dbead2e7, 0xe6c246b9e15c890b, 0x2ff5a94ab95ebbd3, 0x35afa9ef301f8c72, 0xabeb0b0327bfb2d0, 0x1394696954db8927, 0xf26951b8fae064c0, 0x6c84c84488382a7d, 0xc3d9ad3d70228bfa, 0x78cc08c3d4d4c570, 0xcaf6976667803eec, 0xeab4209c27e5645b, 0x6d90c08227cfbcb1, 0x79e49911da6380f3, 0x7e32bbaed21102e7, 0x94b715d1a8bbbf07, 0x8e9b1dcc3e7305ba, 0x784592c36439646c, 0x9fe9df150000246f]

private theorem rounds013_1 : sixRounds 6 (by decide) quarter013_1 = quarter013_2 := by
  decide +kernel

private def quarter013_3 : Vector UInt64 25 :=
  #v[0xbce829ffed114563, 0x205ecb4a816894f0, 0x990d07ee3369d569, 0xfeb5ebbf9dcaadd3, 0xd36a6be4b6ad66d9, 0x9ade622e154df3c6, 0xc1a6945894fcab79, 0x71e34fc11ca54b13, 0x8b42ff00d03d7ad8, 0x286ac915b7193ee3, 0xf888e5426accde77, 0x5513dc84a2d3f66f, 0xc23472b70e76a8d6, 0xa5e193454a15ef18, 0x5bf1009ea42e5677, 0x3d782b774d8558ee, 0xfd6726705e7ea6cc, 0xe80b4a2ad7675177, 0xfd9e1bf7f595f32a, 0x1987e98b0d9dad82, 0x39d5f45a7b8bfc5e, 0x3dbe322aeb230795, 0x1d0fff49e37464aa, 0xd160ff9f61b9d9dc, 0x7c42ab46c04ba021]

private theorem rounds013_2 : sixRounds 12 (by decide) quarter013_2 = quarter013_3 := by
  decide +kernel

private theorem rounds013_3 : sixRounds 18 (by decide) quarter013_3 = state014 := by
  decide +kernel

private theorem perm013 : KECCAK.f1600 absorbed013 = state014 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds013_0, rounds013_1, rounds013_2, rounds013_3]
  rfl

theorem block013 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes013 ++ tail) state013 =
      KECCAK.Bytes.run 0 tail state014 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes013 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb013 ws)) := by
    rfl
  exact (step state013).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words013).trans perm013))

private def absorb014 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x35 0x1 0x81 0x20 0x60)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x40 0x60 0x91 0x16 0x81 0x90 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x60 0x60 0x91 0x16 0x82 0x35 0x1 0x81)) 5 (by decide) (UInt64.ofBytes 0x80 0x60 0x91 0x16 0x81 0x35 0x1 0x82)) 6 (by decide) (UInt64.ofBytes 0x5b 0x56 0x7e 0x17 0x61 0x16 0x35 0x1)) 7 (by decide) (UInt64.ofBytes 0x5b 0x56 0xc0 0x1a 0x61 0x35 0x7 0x61)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x51 0x80 0x40 0x60)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x90 0x51 0x52 0x82 0x16 0x92 0x90 0xff)) 12 (by decide) (UInt64.ofBytes 0xf3 0x90 0x1 0x20 0x60 0x3 0x90 0x81)) 13 (by decide) (UInt64.ofBytes 0x56 0xdc 0x1a 0x61 0x23 0x4 0x61 0x5b)) 14 (by decide) (UInt64.ofBytes 0x56 0xe2 0x1a 0x61 0x35 0x7 0x61 0x5b)) 15 (by decide) (UInt64.ofBytes 0x36 0x80 0x4 0x60 0x7 0x4 0x61 0x5b)) 16 (by decide) (UInt64.ofBytes 0x7 0x61 0x15 0x10 0x81 0x40 0x60 0x3))

private def absorbed014 : Vector UInt64 25 :=
  #v[0x6ec581b08fb34687, 0xa0d4385f5a0fae29, 0xd12266f802e07252, 0x51851eaf0fca4ba1, 0x86f0a5368c99d841, 0xd76201ce32939548, 0x74be876587a9f22b, 0xfd1f0b47fb16941e, 0xc2d93d178f8f0fc0, 0xc86f83396e4fb884, 0xb613049112b003e9, 0x7c1b16dc96bdccd6, 0x2204c2ce35b90a7c, 0x91aedadbc94f1945, 0x7423826d5744892e, 0xb99b93638a739a28, 0x36234b986a7ed3bc, 0x2bbdc49c518f6a6f, 0x906e69edb9246a7b, 0x45824dd2502815c8, 0x94056491f53d191c, 0x370d4e708b0c88ce, 0x34d5aedcc3bc1f8c, 0x94570627b4f70234, 0x3709c310a4660bbb]

private theorem words014 : absorb014 state014 = absorbed014 := by
  decide +kernel

private def quarter014_1 : Vector UInt64 25 :=
  #v[0x1a4d88d7e9a79e22, 0xe95364a15c8eb74a, 0x1b1a7649c68c286b, 0xa2591f3073229fcc, 0x2ce6dff2f91c0fb4, 0xf7bbc8800f8cc7d7, 0xabd973311a23481f, 0x6646d6faeb9bc980, 0xf6508a24a2693c0a, 0xb90ba80a0092d050, 0xdcf581e648714fb, 0x8335e79149e5987a, 0xba153f4e756a457e, 0xf4accadc9e529778, 0xb489df2985d4ea7, 0x4a9e8eaf875fdfce, 0xb7ee82c8db388c28, 0xe8d86612088460e0, 0x94fd6bf74a6e5298, 0x740dc7f3323f44a8, 0xb9a2391abf7f0c7f, 0x64f3157c57fdcf85, 0x18f6de192040ddc9, 0xb42739650416c193, 0xc16c08f8556888bd]

private theorem rounds014_0 : sixRounds 0 (by decide) absorbed014 = quarter014_1 := by
  decide +kernel

private def quarter014_2 : Vector UInt64 25 :=
  #v[0xc9e7de95dc6e69fa, 0x15f370179bdf2fa0, 0x6453accfd12ba4a6, 0x97022b137961ea0e, 0x41e7499740c803cd, 0xd7822fff134c4f4, 0xf7316da891c0abd3, 0xf9e18ed651e93ff, 0x25495b7a50370bb7, 0x4e9c2cb6df93422, 0xe81d1019615e9086, 0x16664fd5998b3c29, 0xeb2482e57839ec2c, 0x8ca9f56658b51fd1, 0xeba5d2f7760edc5d, 0x2905eb64f475fcbe, 0x57f5c6c62ca42934, 0x1a51b7df02d6c3de, 0x11a083238e7f6f47, 0x81c50c28379b4126, 0xbe465377d0279d6d, 0x308334bbfb325d56, 0x8ce49b65c8d35af9, 0xc9a25baf9dfda7a2, 0xcb9d34fffd1ba5ce]

private theorem rounds014_1 : sixRounds 6 (by decide) quarter014_1 = quarter014_2 := by
  decide +kernel

private def quarter014_3 : Vector UInt64 25 :=
  #v[0x6dbbb469fd5acf68, 0xd7934f37f6bd360a, 0x38a30cdd24a7d267, 0x6d36e70c2fd19797, 0xe46beec7f6fb300a, 0x43d9b5ae7ece0421, 0x68508658f46027a0, 0xf0289869512ee933, 0xa4d91962b87f5422, 0x3ef715ae5b01779, 0x871113f1ee2a539e, 0x6835b477a42d6d0c, 0x27b8e7259bec1bd4, 0x67bd551c17ed4d3f, 0xfc1270df4a500f07, 0x55e5ea141e19ea8f, 0xad47435c9108841, 0x89c08eab62110314, 0x5487f65887d1014d, 0xd9b7500d6d7047c2, 0x6d224b545bf8e4, 0xa4fc65130a78a930, 0x21fe4dbac21dabb0, 0x7c07c2e4b32a99bb, 0xdd7aec07529c85f1]

private theorem rounds014_2 : sixRounds 12 (by decide) quarter014_2 = quarter014_3 := by
  decide +kernel

private theorem rounds014_3 : sixRounds 18 (by decide) quarter014_3 = state015 := by
  decide +kernel

private theorem perm014 : KECCAK.f1600 absorbed014 = state015 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds014_0, rounds014_1, rounds014_2, rounds014_3]
  rfl

theorem block014 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes014 ++ tail) state014 =
      KECCAK.Bytes.run 0 tail state015 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes014 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb014 ws)) := by
    rfl
  exact (step state014).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words014).trans perm014))

private def absorb015 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57 0x84)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x16 0x35 0x81 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0xfe 0x1a 0x61 0x35 0x1 0x20 0x60 0x90)) 5 (by decide) (UInt64.ofBytes 0x80 0x1c 0x61 0x70 0x4 0x61 0x5b 0x56)) 6 (by decide) (UInt64.ofBytes 0x80 0x4 0x60 0x7 0x4 0x61 0x5b 0x56)) 7 (by decide) (UInt64.ofBytes 0x61 0x15 0x10 0x81 0x40 0x60 0x3 0x36)) 8 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x80 0x0 0x60 0x57 0xc5 0x7)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x50)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x35 0x81 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x1d 0x61 0x35 0x1 0x20 0x60 0x90 0x16)) 13 (by decide) (UInt64.ofBytes 0x4 0x60 0x70 0x4 0x61 0x5b 0x56 0x43)) 14 (by decide) (UInt64.ofBytes 0x15 0x10 0x81 0x20 0x60 0x3 0x36 0x80)) 15 (by decide) (UInt64.ofBytes 0xfd 0x80 0x0 0x60 0x57 0xfe 0x7 0x61)) 16 (by decide) (UInt64.ofBytes 0x5b 0x56 0x78 0x21 0x61 0x35 0x50 0x5b))

private def absorbed015 : Vector UInt64 25 :=
  #v[0x97ae39e7a8778ad4, 0x6c21cb24510b4e6e, 0x2999c13a11759611, 0xc51440005c291312, 0x2c720c17bab81ab3, 0xbd87b14b08d4af89, 0x115d0b9d34a50993, 0xf8c159389c986056, 0x6868ccbc88deedbf, 0x5bf2f49371c9b1bd, 0xb7a4e5ee93abb6c3, 0xa2a7a2dd06dab3a, 0x6a0a41f15942548e, 0xa581c5534ac105b1, 0x602c062712612cbb, 0x8cd2e9ecfcf7923b, 0x45c58b5fc8e6efc6, 0xbc7ba7021fb8f8a7, 0xc7a1ae57a40d5f30, 0xb417b48bed13e906, 0xefdc0166d9a1f4c6, 0x12ee48c30ef779d3, 0xf0b8004b27f87d34, 0x9e2868e7ec5209d0, 0x1ffe9782e5f152bf]

private theorem words015 : absorb015 state015 = absorbed015 := by
  decide +kernel

private def quarter015_1 : Vector UInt64 25 :=
  #v[0x87f772264ee8bac7, 0xcb6210fb71d27d98, 0xe900b45371dee506, 0x7475c48e6519a779, 0x517b43650609d71c, 0x688b6436ea32ff6b, 0x4fd5032620d6af26, 0x755618062a18cd2e, 0x7cb35934e4422b59, 0x8f58ff520ab79511, 0x1ad4ac8f783abbbb, 0xb658eb894e3329ec, 0x30fd2806e72f643f, 0x5ddb661a9d711512, 0x6040b315c99a7b9e, 0x9f6e220a91e1d228, 0xd946e845581eb02e, 0xc02b04c099ce1158, 0xc2b701a922012df7, 0xb84a6bdc66123496, 0x6c366dd349e361d7, 0x5a32e4024c1c99aa, 0x7b2904bd19a3642a, 0x6b9b1caa1a997376, 0x78d27714d3497309]

private theorem rounds015_0 : sixRounds 0 (by decide) absorbed015 = quarter015_1 := by
  decide +kernel

private def quarter015_2 : Vector UInt64 25 :=
  #v[0x36ad9597280de6a5, 0x84958973e60ce5a2, 0xe0de0a20f737f297, 0x40adafbbf37f61b8, 0x306f488ec0d2b75a, 0xc9b831848a3051fe, 0xe834afad81ef8430, 0xb9f7696ff3aec96c, 0x3fa50562cf4953, 0x77704a0d33644bde, 0x9450e58ba671e278, 0x50f15bba06f0e0a6, 0x58c01af242247130, 0x635ed20b79193f40, 0xffd0c0c7cb8e158c, 0x85e450dcc9018eae, 0xbf5de8e0ccaa19f3, 0x2853b48e3aa12c77, 0x6a6181a5fd428eac, 0x6c2994ccf485b2c2, 0x7e2cffb617bed3fd, 0xb8c6d534011d43db, 0x6b957c7c787fce42, 0x785fdf0361ace2ee, 0x77ba0a112309f375]

private theorem rounds015_1 : sixRounds 6 (by decide) quarter015_1 = quarter015_2 := by
  decide +kernel

private def quarter015_3 : Vector UInt64 25 :=
  #v[0x5a0d126d4e2494c, 0xacbbc514a52052ac, 0x1826f208894a1e31, 0x983768c22d34d4b5, 0x1ea93e88054b7702, 0x53f86279d8e34c3, 0x431ed6955c6bb1e5, 0xe2436b3f61fa0305, 0x554c4b0bb7d10547, 0xac0c353dd3042267, 0xa172d6b49e5e6192, 0xfe6824937343e9e0, 0x31b66f73e933a6f, 0x7d26b21089b7890f, 0xf4ec5b5f5eada24b, 0x19fad1698ea80e11, 0xe1b8a6242e6d114e, 0x8e9a48ef36803991, 0xb9412d4deb746da1, 0x7e007a1c04b8bf85, 0x8432b42c8ed1c562, 0xed9495111c3cbb80, 0xc246c137d4f62a8f, 0xa4b2ce7f9cf11eaa, 0x3fbdd68ebcecc666]

private theorem rounds015_2 : sixRounds 12 (by decide) quarter015_2 = quarter015_3 := by
  decide +kernel

private theorem rounds015_3 : sixRounds 18 (by decide) quarter015_3 = state016 := by
  decide +kernel

private theorem perm015 : KECCAK.f1600 absorbed015 = state016 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds015_0, rounds015_1, rounds015_2, rounds015_3]
  rfl

theorem block015 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes015 ++ tail) state015 =
      KECCAK.Bytes.run 0 tail state016 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes015 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb015 ws)) := by
    rfl
  exact (step state015).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words015).trans perm015))

private def absorb016 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x5b 0x56 0x32 0x24 0x61 0x23 0x4 0x61)) 1 (by decide) (UInt64.ofBytes 0x3 0x36 0x80 0x4 0x60 0x7 0x4 0x61)) 2 (by decide) (UInt64.ofBytes 0x23 0x8 0x61 0x15 0x10 0x81 0x40 0x60)) 3 (by decide) (UInt64.ofBytes 0x73 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x90 0x16 0x35 0x81 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x56 0x56 0x24 0x61 0x35 0x1 0x20 0x60)) 8 (by decide) (UInt64.ofBytes 0x36 0x80 0x4 0x60 0x70 0x4 0x61 0x5b)) 9 (by decide) (UInt64.ofBytes 0x8 0x61 0x15 0x10 0x81 0x20 0x60 0x3)) 10 (by decide) (UInt64.ofBytes 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57 0x5c)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x35)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x61 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x60 0x70 0x4 0x61 0x5b 0x56 0xe9 0x25)) 15 (by decide) (UInt64.ofBytes 0x10 0x81 0xa0 0x60 0x3 0x36 0x80 0x4)) 16 (by decide) (UInt64.ofBytes 0x80 0x0 0x60 0x57 0x8f 0x8 0x61 0x15))

private def absorbed016 : Vector UInt64 25 :=
  #v[0x421320ca0963fce4, 0xa6b484e31c75de8e, 0xa741691b2c2e20f, 0xf940b2336d5066af, 0xa6f2a3f4c9ae52af, 0x6092550a95144bb6, 0x99adc63c496e5fed, 0x2cc54f6a029b321c, 0xd5645a41ded0f259, 0x270facef1b38e249, 0x64a7725b41944c3, 0x6d076be22242cc11, 0xf23909b6cfbbdcfe, 0x9cd27f8f9198cc5b, 0x52a332ea974fd1d9, 0x2c447b01a589210c, 0xfca42a8d1d8a5f72, 0xc304d17fcc13f207, 0x5c4aa63a8314a265, 0x5bb59a225bf2fc33, 0x74715e04622594fc, 0xe7fb8f62f32b65d2, 0x944a433903cf447d, 0xeb05a52646aff8e9, 0x774cf2e5015c1a73]

private theorem words016 : absorb016 state016 = absorbed016 := by
  decide +kernel

private def quarter016_1 : Vector UInt64 25 :=
  #v[0xb4d3c76de0b0e740, 0x85b42461b8b5c0ee, 0x71813d43fbc65551, 0xb6f23ee9438e38f8, 0x7e3bb13d4a29a00f, 0xd94419cf3e274066, 0xfe37a7cdb64db17d, 0xec99d5bb26e8ac2b, 0x8086f071473eedf4, 0x1b57ac6ffa87d601, 0xba7ef96486e311d3, 0x5c45352569c0fe6b, 0x66f3bf7736d57dc, 0x2292bcb61d249fb0, 0xdf866800739d40, 0x842e46aec6469769, 0x9adc39774a62cb3c, 0x59417a1d29b73ee9, 0xf5a87d8466e57c55, 0xccba706bef86cbd5, 0x4f19308252cf9ea3, 0x2dcc62002b00a027, 0xfc973dc2595b6a8f, 0xec2ad08525bdfd8b, 0xca519ece817fe2bf]

private theorem rounds016_0 : sixRounds 0 (by decide) absorbed016 = quarter016_1 := by
  decide +kernel

private def quarter016_2 : Vector UInt64 25 :=
  #v[0x52e28e4d48214e5e, 0x4523c8179d9a19dd, 0x27338b0e082a2b0e, 0xaa0f98730ab9c581, 0x5b653590e0628e7c, 0x5407451cc714b62f, 0x1fcc281a7600485f, 0x8d400b3a33a445a7, 0xd750730a461ff038, 0xc0185c9a04351636, 0x838d5ec3a94b5276, 0xd2de855a6f170270, 0x495520d9ed7b8bb, 0xd073659f31d7cfc0, 0x8eb0dac5dc34149f, 0xb24b72bf2ed6a5a3, 0x402464e31dce4b59, 0xfe73dbb3358ed1ff, 0x94225bbcdcd7ee8e, 0x2411555df9053b97, 0x4b052deaa4016937, 0xca2e09431954e1e4, 0x1507ecf3342fd399, 0xe864ff8d21d9469a, 0xe17f92922366531d]

private theorem rounds016_1 : sixRounds 6 (by decide) quarter016_1 = quarter016_2 := by
  decide +kernel

private def quarter016_3 : Vector UInt64 25 :=
  #v[0x3c21186f6729034c, 0x879f49b5fb1cdfb1, 0x86666dc61aa38c67, 0xbe97f2359bf1f43b, 0x36c09893c31aeacd, 0x4c9a4ea678349c32, 0x58462099e656c867, 0xf9869c346c0b8215, 0xb02d0b37d5482891, 0x149919ce32ded0fc, 0x77f158fd7ab785ba, 0xffa90e113234b063, 0xbd1e9daf6b6a7e1c, 0xeeba9c5c8043fb60, 0x7734ddcd511568e8, 0xf5f5c5698404d6fa, 0xcc0f6eb679cdb5bc, 0xd3c11ce0419f8c82, 0x7f4e82ccb4f040ed, 0xfc5993b86b6d1713, 0xc08d9d13b60831e, 0xe286635b2716c77, 0x5715d2acf18ff114, 0x25f6c60a651e5abd, 0x39d2c3a550a1d3f6]

private theorem rounds016_2 : sixRounds 12 (by decide) quarter016_2 = quarter016_3 := by
  decide +kernel

private theorem rounds016_3 : sixRounds 18 (by decide) quarter016_3 = state017 := by
  decide +kernel

private theorem perm016 : KECCAK.f1600 absorbed016 = state017 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds016_0, rounds016_1, rounds016_2, rounds016_3]
  rfl

theorem block016 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes016 ++ tail) state016 =
      KECCAK.Bytes.run 0 tail state017 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes016 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb016 ws)) := by
    rfl
  exact (step state016).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words016).trans perm016))

private def absorb017 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x50 0x5b 0xfd)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x1 0x81 0x20 0x60 0x90 0x16 0x35 0x81)) 4 (by decide) (UInt64.ofBytes 0x1 0x82 0x40 0x60 0xff 0x60 0x90 0x35)) 5 (by decide) (UInt64.ofBytes 0x35 0x1 0x81 0x60 0x60 0x90 0x16 0x35)) 6 (by decide) (UInt64.ofBytes 0x50 0x27 0x61 0x35 0x1 0x80 0x60 0x90)) 7 (by decide) (UInt64.ofBytes 0xee 0x27 0x61 0x7 0x4 0x61 0x5b 0x56)) 8 (by decide) (UInt64.ofBytes 0x80 0x4 0x60 0x23 0x4 0x61 0x5b 0x56)) 9 (by decide) (UInt64.ofBytes 0x61 0x15 0x10 0x81 0x20 0x60 0x3 0x36)) 10 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x80 0x0 0x60 0x57 0xe5 0x8)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x35 0x50)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x23 0x4 0x61 0x5b 0x56 0xf 0x28 0x61)) 15 (by decide) (UInt64.ofBytes 0x81 0x20 0x60 0x3 0x36 0x80 0x4 0x60)) 16 (by decide) (UInt64.ofBytes 0x0 0x60 0x57 0x18 0x9 0x61 0x15 0x10))

private def absorbed017 : Vector UInt64 25 :=
  #v[0x618d5989292a8d64, 0x19cd6a675aa645eb, 0x7278b1f0e18246f8, 0xbaae210234e66ccf, 0x4f963533c9f1ed3, 0x56eb0b84b8649c3f, 0x75dc99dccd8012f7, 0xa8e54e16d906ff06, 0xdcf19791e1a80317, 0x41446c30837a0334, 0x1d558d5aedee7c6f, 0x8704ef7cbdfdb4e1, 0x31c862a5f4c10487, 0xe38b3dbfe93a6d4, 0x861c40eca8f06340, 0x61b1338531b2d203, 0x93b5fad696ca0964, 0xce1925cc33eef890, 0xcc9e063bcee1504, 0x319707c6fe4b56f5, 0xa722e53b2c34972, 0x15e9b2958eb5861, 0x6d3d28360d77b45c, 0xa73cd5a081c6c043, 0x5d5759d4db1553f1]

private theorem words017 : absorb017 state017 = absorbed017 := by
  decide +kernel

private def quarter017_1 : Vector UInt64 25 :=
  #v[0x173e31128007f7df, 0x278da85b0a1c5dce, 0xbc9f0b6603bfe144, 0x9406e9c230f65284, 0x533eb890c8dbb7be, 0x306aa8ec206d0944, 0x89d2ac33fbcb7c7b, 0xd4f3f64be2a81392, 0x33a5c425f9e63bd3, 0x6fc2ccfd58b643e, 0xe9d67e74a18d1390, 0xda9ebfa4e8db96b8, 0xac33d158a73ed878, 0x46baa6e734a7adf3, 0x8e50ebf0439bf800, 0xa11af3b8e7d7a983, 0xdbfb5dc7d507cb53, 0xe9920ae30fecf4f3, 0x7d05588525d74821, 0x10140e84cad4f01, 0xfd53fd42cf32ed7, 0xf6f2dad799d745b0, 0xc6c22561aa74163d, 0xe3c621fd3f82cc6, 0x5d01f468a74e6e78]

private theorem rounds017_0 : sixRounds 0 (by decide) absorbed017 = quarter017_1 := by
  decide +kernel

private def quarter017_2 : Vector UInt64 25 :=
  #v[0xc86b28eb41bebe8f, 0xf00b8de4f99c9296, 0x2bdb70072f1c28a, 0x8da868c805047033, 0x82fc0848c1a9fa88, 0x825861f590e112a6, 0x3bcaae7a9a6f4f1, 0x6f2453db7abff21a, 0x1a96f31481a4355b, 0x565d573ecc3445b0, 0x9f599aa03f215a0a, 0x521a06430e3469a4, 0xa45c7f6109a538a9, 0x2bc62bf26d0284df, 0x87916d0e051600ea, 0xc26a532daad99770, 0x8ff21c3e55756607, 0x4e396b9fb156bed7, 0xc3064d1dc6b9ff60, 0xfe333cdeab0d1213, 0x2cf242e519a90626, 0xb0bc3f390bf32a88, 0x94ab3d9f142a2fa1, 0x1ccd0ab452ebef5e, 0xb3cdc7648f5dd852]

private theorem rounds017_1 : sixRounds 6 (by decide) quarter017_1 = quarter017_2 := by
  decide +kernel

private def quarter017_3 : Vector UInt64 25 :=
  #v[0xca3ffbd49e835bc9, 0x65cf1768bb3b13a3, 0x2a05a3b04e865e4e, 0x3182105f2947b26c, 0x5c8ea754abc1039d, 0x51831c080d1d8865, 0x61b944d50aa77096, 0xe30d7afe34501fc1, 0xa258d95f2c6583ec, 0xb9ef8d700e787aa8, 0xeb24871695c4e083, 0xf1022eccfb6e097b, 0x8a0f70de207c2837, 0x35c800f809d936d9, 0x890e60699383482a, 0xc9d10f3e4828f7d6, 0x205ca14d56196bc9, 0x503b1db170bca28a, 0x1eaf8e51ccbbd920, 0x77b57f91c5f95811, 0x79802025778827d6, 0xcacc1e52379ac6c1, 0xec98fbb58e2f7fbc, 0x3262a86f6d07f6c1, 0x4e9db08c80ec6009]

private theorem rounds017_2 : sixRounds 12 (by decide) quarter017_2 = quarter017_3 := by
  decide +kernel

private theorem rounds017_3 : sixRounds 18 (by decide) quarter017_3 = state018 := by
  decide +kernel

private theorem perm017 : KECCAK.f1600 absorbed017 = state018 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds017_0, rounds017_1, rounds017_2, rounds017_3]
  rfl

theorem block017 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes017 ++ tail) state017 =
      KECCAK.Bytes.run 0 tail state018 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes017 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb017 ws)) := by
    rfl
  exact (step state017).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words017).trans perm017))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
