import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb132 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x24 0x60 0x16 0x84 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x1 0x82 0x80 0x44 0x60 0x52 0x1 0x82)) 3 (by decide) (UInt64.ofBytes 0x3 0x83 0x80 0x51 0x82 0x52 0x90 0x84)) 4 (by decide) (UInt64.ofBytes 0x90 0x64 0x60 0x52 0x81 0x1 0x91 0x90)) 5 (by decide) (UInt64.ofBytes 0x81 0x20 0x60 0x52 0x91 0x90 0x1 0x91)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x7b 0x51 0x80 0x1)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0xbb 0x9c 0x5 0xa9 0x7f 0x16)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x6e 0x32 0x61 0x52 0x90 0x17 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x5b 0x56 0xe3 0x4e 0x61 0x90 0x84 0x90)) 16 (by decide) (UInt64.ofBytes 0x61 0x88 0x88 0x85 0x89 0x31 0x46 0x61))

private def absorbed132 : Vector UInt64 25 :=
  #v[0xec680b11d0bb506, 0x70d102d63609513b, 0xb48099201cbfdd8c, 0xdb738dd29c57d036, 0xfbd96fefb0ab78bb, 0xddcf21932e2ac6f5, 0x88d5796e968e0bba, 0x6cc2171a7125cd20, 0x7c1d3af19cd11f37, 0x901e580fa0250954, 0xd9eb9a73a0507d40, 0x8095b58187af4feb, 0x98b954e5e471ab61, 0xb7e4882551e15382, 0xa314c442f0545791, 0x23f7f4590eb7f521, 0x641a5e84a576c26, 0x5b2fabb61e1a5695, 0xf174d04c6c6b80b1, 0xbc61585b870812fa, 0xb99e24d2265ae4b3, 0x3e7752e85e4971f, 0x30031b9a5679fd80, 0xab6471b58bf4628b, 0xc114de143c925048]

private theorem words132 : absorb132 state132 = absorbed132 := by
  decide +kernel

private def quarter132_1 : Vector UInt64 25 :=
  #v[0x96f054e7a58a8003, 0xab58858696f7d22f, 0xb15df4784b83004b, 0x7fd62812c7ee8644, 0xd78b5ddc894562, 0xc0786f7f982ff144, 0x5154f942a27514a1, 0x9c5797a7452c3db7, 0xca4daeab8ef9c800, 0x9bd9ba720d393230, 0xc1ae9520a6a6349, 0xcf36eb9417498143, 0x6c4f7665611a0b30, 0x1550a2e929d492a9, 0x5da505b7ec6779d2, 0x241029500110abac, 0x96c559fa9ae617fb, 0xf93801e99ec7c231, 0x219fa6b060378c6a, 0x45ccf142c1377519, 0x865081d37a2193ca, 0x69e794d076d7df7e, 0x7fbdf3fc3b38e000, 0x7abc0a549303f09, 0xf6c00bc1c4410d12]

private theorem rounds132_0 : sixRounds 0 (by decide) absorbed132 = quarter132_1 := by
  decide +kernel

private def quarter132_2 : Vector UInt64 25 :=
  #v[0xf40931e9476ab86f, 0x1e3061672f125d1f, 0x7f5b79885c857b57, 0x528ef882d3c177f5, 0x772b0a96d8150d67, 0x7b00a7087c81d5ad, 0xbc29fc2e53715830, 0x92f975ed72a20d71, 0x1a3bf3b90f6c244b, 0xfe9c822587696794, 0x404f9891a260b6c6, 0x4673b8231bcb6ac3, 0xb6b04c349c7aebec, 0x6da4ab1a4df7da6c, 0x14ffb971e2139aa6, 0x9f65d75f19d85382, 0xc3c7bd8ee82f7969, 0xb914106a3ce760a, 0xfc262e52a742b691, 0xc84b6b619dd9592f, 0x157f02f501540090, 0xa59cb528b6300681, 0x3fd45229989507d4, 0x99e2c1d671e135cc, 0x11854757b7c26c10]

private theorem rounds132_1 : sixRounds 6 (by decide) quarter132_1 = quarter132_2 := by
  decide +kernel

private def quarter132_3 : Vector UInt64 25 :=
  #v[0x780e079407f56672, 0x4b059ab26a2b26b9, 0x11e351875d64b1f, 0xd513304fb3831009, 0xb7dda1d503456260, 0x6466e0315389efdc, 0x11f875bd420395e6, 0x948e4b083afafceb, 0xe02edecec027d235, 0x9e096f72f5e1342c, 0x5e6598c217397821, 0x2675a4256b3395d3, 0x13bd77506492f32a, 0x255aa4859ce31658, 0xff6e1d926962981f, 0x940909e0fe1079ce, 0x1714b1cdfb76b4b1, 0xdc964d5278d79114, 0x37053d95f5540d0d, 0x81622550b9480c79, 0x2e6699fb2092f774, 0x70efd969466b549e, 0xc793bd791f27ebf0, 0xab93fe07515afa12, 0x35103632eeb65a85]

private theorem rounds132_2 : sixRounds 12 (by decide) quarter132_2 = quarter132_3 := by
  decide +kernel

private theorem rounds132_3 : sixRounds 18 (by decide) quarter132_3 = state133 := by
  decide +kernel

private theorem perm132 : KECCAK.f1600 absorbed132 = state133 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds132_0, rounds132_1, rounds132_2, rounds132_3]
  rfl

theorem block132 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes132 ++ tail) state132 =
      KECCAK.Bytes.run 0 tail state133 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes132 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb132 ws)) := by
    rfl
  exact (step state132).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words132).trans perm132))

private def absorb133 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x51 0x80 0x40 0x60 0x5b 0x56 0x9e 0x4d)) 1 (by decide) (UInt64.ofBytes 0x1f 0xa 0x5 0xbb 0x22 0x42 0x42 0x7f)) 2 (by decide) (UInt64.ofBytes 0x1f 0x67 0xa5 0x32 0x72 0x1 0x14 0x7f)) 3 (by decide) (UInt64.ofBytes 0x4b 0x50 0xf 0x42 0xd3 0xa2 0x80 0x26)) 4 (by decide) (UInt64.ofBytes 0x19 0x53 0x5c 0x3 0x3 0xcf 0x65 0xd5)) 5 (by decide) (UInt64.ofBytes 0xff 0x73 0x52 0x1 0x82 0x20 0x60 0x8a)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x84 0x82 0x16 0x8c 0x80 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x60 0x16 0x8b 0x90 0x52 0x90 0x81 0x1)) 10 (by decide) (UInt64.ofBytes 0x1 0x82 0x80 0x60 0x52 0x1 0x83 0x60)) 11 (by decide) (UInt64.ofBytes 0x89 0x1 0x82 0xa0 0x60 0x52 0x90 0x8a)) 12 (by decide) (UInt64.ofBytes 0x90 0x88 0x1 0x82 0xc0 0x60 0x52 0x90)) 13 (by decide) (UInt64.ofBytes 0x90 0x88 0x1 0x83 0x80 0xe0 0x60 0x52)) 14 (by decide) (UInt64.ofBytes 0x91 0x90 0x3 0x84 0x80 0x51 0x83 0x52)) 15 (by decide) (UInt64.ofBytes 0x92 0x90 0x0 0x1 0x61 0x52 0x81 0x1)) 16 (by decide) (UInt64.ofBytes 0x90 0x54 0xf 0x60 0x52 0x92 0x90 0x1))

private def absorbed133 : Vector UInt64 25 :=
  #v[0x588185f8de8e75ec, 0xf7bc4f1f1071043d, 0x9f93b2692f568f7, 0x86460caa3c0e30b6, 0x61aa02a570332811, 0x70bf8a636848e624, 0x7d3b8d5b339f1a33, 0x1b94b0542cd68cd6, 0xb580a1e7be055959, 0x8bf016575c78c757, 0x167e31e727af10a6, 0x76a409c81247a374, 0xf98658cff9516d2d, 0x1a7583391a126a4, 0xe91406b3a81563fc, 0x7ce1bc03ebaee5b5, 0x8969aae73d6841eb, 0xad4e4c4711aeeb2f, 0xaf2b9f0c3cfdea14, 0x5d986978f707cb2b, 0x24b099d9f758be34, 0x1c521fd2de1402c5, 0x652a85d0ca424965, 0x3ffd5b7bca86fc62, 0xbb6f680c4c63bc27]

private theorem words133 : absorb133 state133 = absorbed133 := by
  decide +kernel

private def quarter133_1 : Vector UInt64 25 :=
  #v[0xa7df5e467fdad335, 0x8d6a230e59cba6d8, 0x6eb89226f6c56858, 0xb927617f9c9b8f2c, 0x237a84e25ba939af, 0x10535bc520827b79, 0xf43eb7cf9cc6f820, 0xb04dc297bd88f0b0, 0x3782cf7a4dafcda5, 0x1f2ee2555ef4307c, 0x18f78f40336bb1ca, 0xa44f028dc489f598, 0x1fca78ee9ad260ed, 0x5e07a254acabe0dc, 0x4d567d891eb1533d, 0x4667c5b746a8168f, 0x5031c16da49a33c4, 0x6e4a4e780408e578, 0xfdd84aae79b3b7db, 0xf9defff3de0337a8, 0x896c58e8cd37158e, 0x9d0fd22b877a266d, 0xbc521987685ade10, 0x7cdabcbd6442fbc0, 0xa3fee891ccd67bde]

private theorem rounds133_0 : sixRounds 0 (by decide) absorbed133 = quarter133_1 := by
  decide +kernel

private def quarter133_2 : Vector UInt64 25 :=
  #v[0xd5ef7b43402727a6, 0xec2bf21223ab00b5, 0xdc72262d37ca1c73, 0x1cd32fc841f7cf7d, 0x5b34a24338d6756d, 0x7e4320cc6866aa12, 0xcbf2193621873517, 0x959da8849bc448ff, 0x1b04ede7cc57bab0, 0x1546cb5886b39f54, 0xcb552aac0be26a30, 0x80c7d990d74c05d8, 0x7387b90868e12910, 0xeb66e690d2191dc9, 0x46e2ef2411993221, 0x75ae40ebfbcbbdeb, 0xb112541ea995e5dd, 0x1d82b8120982cc3a, 0xcb0c8b53bf5234ba, 0x801f8f338e99a635, 0x58c8c66abec81854, 0xe368a20bbf79b53b, 0x6ccf6f09a0ce2fc2, 0x86b0fa6c330bbe46, 0xb86b918cea10386f]

private theorem rounds133_1 : sixRounds 6 (by decide) quarter133_1 = quarter133_2 := by
  decide +kernel

private def quarter133_3 : Vector UInt64 25 :=
  #v[0xa1460319bce6ce9f, 0x89147643a481ace0, 0x5338060d164273c7, 0xf180e232f04b7020, 0x2dd39fd14899ef72, 0x2ec9e63d70be98c7, 0x3031ab657f4860aa, 0xe2fe0ae599bec75c, 0x1cd0208230055e6, 0xb45896ba93eb8295, 0xe471294cda27d9db, 0xba7a1565cbc92a48, 0x750a4a96c8360c3, 0x35a6f6bb103f197c, 0x365a10f1b2cf9b4b, 0x3ca34d363b74fe67, 0x32f576d1f5eb31b9, 0x9b6cd31e651c9b29, 0x7f4ad16aa7a60958, 0x2057702546ec4a3b, 0x56b1bee383cb48d7, 0x51084d87443ca7ed, 0xbc89b386920d232a, 0x3728eeaa1bc12cca, 0xfdd8eea7944d0e96]

private theorem rounds133_2 : sixRounds 12 (by decide) quarter133_2 = quarter133_3 := by
  decide +kernel

private theorem rounds133_3 : sixRounds 18 (by decide) quarter133_3 = state134 := by
  decide +kernel

private theorem perm133 : KECCAK.f1600 absorbed133 = state134 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds133_0, rounds133_1, rounds133_2, rounds133_3]
  rfl

theorem block133 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes133 ++ tail) state133 =
      KECCAK.Bytes.run 0 tail state134 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes133 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb133 ws)) := by
    rfl
  exact (step state133).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words133).trans perm133))

private def absorb134 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x86 0x86 0x90 0xc4 0x46 0x61 0x90 0x91)) 1 (by decide) (UInt64.ofBytes 0x73 0x5b 0x56 0x2c 0x4d 0x61 0x86 0x86)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x47 0x61 0x14 0x16 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x8 0x7f 0x51 0x80 0x40 0x60 0x57 0x46)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x81 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x52 0x1 0x82 0x4 0x60 0x20 0x60 0x52)) 11 (by decide) (UInt64.ofBytes 0x7f 0x52 0x1 0x82 0x24 0x60 0x1e 0x60)) 12 (by decide) (UInt64.ofBytes 0x65 0x6b 0x6f 0x54 0x74 0x61 0x69 0x46)) 13 (by decide) (UInt64.ofBytes 0x76 0x6e 0x69 0x20 0x3a 0x32 0x56 0x6e)) 14 (by decide) (UInt64.ofBytes 0x67 0x69 0x73 0x20 0x64 0x69 0x6c 0x61)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x65 0x72 0x75 0x74 0x61 0x6e)) 16 (by decide) (UInt64.ofBytes 0x90 0x51 0x90 0x52 0x1 0x82 0x44 0x60))

private def absorbed134 : Vector UInt64 25 :=
  #v[0x6e062287331103af, 0xe33a9c648f4319db, 0x21df68f0908759b3, 0x4fe68c507dbd63b3, 0xac8f681560633834, 0x3ba03e033aee2432, 0xb98790f382381c4, 0xfdf5ec95b1542379, 0x93b0e97325d93e80, 0xfbb629d71b8547c2, 0xb107a6bdddd917a1, 0x2d2b0d3fc09c69fd, 0xd262edc3369bc04e, 0x3b07d61e3dddd115, 0x1e4fd63a810d05a6, 0xb2e2932245d58d08, 0x3b089e457f1502bc, 0xc680d74dff8674e2, 0xa9fe8e8f135494d1, 0x4a51e5496e298d1a, 0x9aca6ba7ec72758f, 0x4f8ac121f2e40d70, 0xec9b04ae3531aca9, 0x86bd446dc637970e, 0xe9d15529c3b363cd]

private theorem words134 : absorb134 state134 = absorbed134 := by
  decide +kernel

private def quarter134_1 : Vector UInt64 25 :=
  #v[0xd09a1a06d7bca321, 0xbfde4b304e6ef99f, 0xd2ea6c44a137bd62, 0x352143ad592ba42e, 0xbe21248b17df3ec6, 0x8ca63bdadb99f7e0, 0x261f4e3deea4632b, 0x5a4edc6a4c404e34, 0x1cb0f805fd2dd1d7, 0xdb4cc1c595b53154, 0xef5bcae66c01883d, 0x686864c0af0650e2, 0xa1fd5ed680d455d9, 0x150ddc1513136183, 0x61f1d9bdbee51f04, 0x743b4adbc3d1ea75, 0x75fe8abbc96ed6a0, 0xd7f74fae0d0a9c76, 0xe24cc35aea9dbf19, 0xe86273d25b843960, 0x966e523665790357, 0x177e3f3fb90499b, 0xe7cc2f1ce71557c0, 0x69ea2a51298266f6, 0x1588984bc6e31b7c]

private theorem rounds134_0 : sixRounds 0 (by decide) absorbed134 = quarter134_1 := by
  decide +kernel

private def quarter134_2 : Vector UInt64 25 :=
  #v[0x97d8dbaf06c1f9cd, 0xe5a9a68fd9101be5, 0xa105103fa3c5e852, 0x39731e43f28f79ea, 0x4dd3b16ac7b15e79, 0x4b2526b48b24db1f, 0xe0ae3124d46c413c, 0x1f41686913ed492c, 0xb78979780087e69a, 0xb487d1f5cb510f48, 0xb1811ab5cf98219c, 0x56cddae257910a35, 0xae940741549c516a, 0x3e62b5bf5175eae6, 0x8446f9006f4b5a24, 0x9623de508311903d, 0x49fa11cbb4dff1c7, 0xa31d0e9b08938353, 0x889c048fc628a66e, 0xce537e340768e35f, 0x170e956cee6d7f05, 0x7cf86816e08eeab6, 0x719df0869e68525b, 0x3a2c3a55ebd2585, 0x96abddcccf4335ff]

private theorem rounds134_1 : sixRounds 6 (by decide) quarter134_1 = quarter134_2 := by
  decide +kernel

private def quarter134_3 : Vector UInt64 25 :=
  #v[0x3786489c5c0ae52a, 0x2b0cd7a223d2ff8c, 0x10d0ca574c36a4e, 0x52600353153f4f25, 0x2faa128902a193c1, 0xd96b8542b96e4c2b, 0x5de31276c1eea158, 0x253ef57a7428ffaa, 0xf45cf9da551400, 0x830ab0e3ed1bf399, 0x8f4eb00fbbd8ccc6, 0xd6959637551fc91, 0x11a4713fcf100f08, 0xeabbedb2879d15a4, 0x7ac043801166620e, 0x87aefc6252fc7100, 0xc158c6bca4334035, 0x7751af0a54f6ff42, 0xa770c3810aa24b18, 0x79f15ffb2459f1f0, 0xe4241129b39c99e5, 0x38edae4bc563070d, 0x731c4d56a1d4d0ce, 0xde5c4977d849fdf, 0x47edf24090acd920]

private theorem rounds134_2 : sixRounds 12 (by decide) quarter134_2 = quarter134_3 := by
  decide +kernel

private theorem rounds134_3 : sixRounds 18 (by decide) quarter134_3 = state135 := by
  decide +kernel

private theorem perm134 : KECCAK.f1600 absorbed134 = state135 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds134_0, rounds134_1, rounds134_2, rounds134_3]
  rfl

theorem block134 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes134 ++ tail) state134 =
      KECCAK.Bytes.run 0 tail state135 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes134 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb134 ws)) := by
    rfl
  exact (step state134).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words134).trans perm134))

private def absorb135 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xfd 0x90 0x1 0x64 0x60 0x3 0x90 0x81)) 1 (by decide) (UInt64.ofBytes 0x4e 0x61 0x86 0x8a 0x50 0x47 0x61 0x5b)) 2 (by decide) (UInt64.ofBytes 0x8a 0x8a 0x8c 0x45 0x61 0x5b 0x56 0x5e)) 3 (by decide) (UInt64.ofBytes 0x84 0x42 0x5b 0x56 0xb3 0x41 0x61 0x8a)) 4 (by decide) (UInt64.ofBytes 0x40 0x60 0x57 0xca 0x47 0x61 0x15 0x10)) 5 (by decide) (UInt64.ofBytes 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x80)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x60 0x20 0x60 0x52 0x81 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x24 0x60 0x1e 0x60 0x52 0x1 0x82 0x4)) 11 (by decide) (UInt64.ofBytes 0x74 0x61 0x69 0x46 0x7f 0x52 0x1 0x82)) 12 (by decide) (UInt64.ofBytes 0x3a 0x32 0x56 0x6e 0x65 0x6b 0x6f 0x54)) 13 (by decide) (UInt64.ofBytes 0x20 0x74 0x69 0x6d 0x72 0x65 0x70 0x20)) 14 (by decide) (UInt64.ofBytes 0x72 0x69 0x70 0x78 0x65 0x20 0x73 0x69)) 15 (by decide) (UInt64.ofBytes 0x1 0x82 0x44 0x60 0x0 0x0 0x64 0x65)) 16 (by decide) (UInt64.ofBytes 0x60 0x3 0x90 0x81 0x90 0x51 0x90 0x52))

private def absorbed135 : Vector UInt64 25 :=
  #v[0x5dbedbb7f39ea871, 0x1ceb4a0c832b5be8, 0x2b78a704192bf810, 0xcf881948a916a0bd, 0x42c823ecc8e7a5bf, 0x8dbab6779edc7de2, 0xfdb00865d27d407b, 0xb89b33dd1c88ebd9, 0x4f53577590ac6eab, 0xee83e13e5cb3db7d, 0x45dc508792acc0b4, 0xffad0e5cab10f9c3, 0xf04c26d792bd8ce1, 0xeeef18b5df2829b5, 0x7008c3ef7f17d51c, 0x2a9fae1840f50464, 0xfd5f93899037659e, 0x5e6e44891f008fb9, 0x3ea4607f5461fa3c, 0x9dc7483a8d233b83, 0xa46f722b8f753f8f, 0x96adcc79eb31f23c, 0x50e9135e016e8a32, 0xb776775429ba71d1, 0x9e5cf47b5a134c7c]

private theorem words135 : absorb135 state135 = absorbed135 := by
  decide +kernel

private def quarter135_1 : Vector UInt64 25 :=
  #v[0x9a1dbc1466b3e564, 0xb7eaa21deeae94cd, 0xf2133fa7071977dd, 0x8b13dcc726fba220, 0xd61c1d7b4f0d01d3, 0xbd578d237675bdd2, 0x4ed8ea2738e1f3ed, 0x356e84ce8c80aa64, 0xc402e6e85b1833f3, 0x4e274df50c3cc88, 0xbb2b8307abaff2e0, 0x454c46761ad39abe, 0x9c4e05e5579f6f26, 0xfae79b8dee375de7, 0x48f6d3183e86112b, 0x3ec4d880d234dd68, 0xb9ff39377ed5d69a, 0xb95e0739c5d46acf, 0xc3e1785afa97e05, 0x8bdb921a088b76cb, 0x837ef7162de8f248, 0xab919993465c380, 0xc8ee619904422b25, 0x42ab6cdfee4fbd01, 0x944eb703f5a704b0]

private theorem rounds135_0 : sixRounds 0 (by decide) absorbed135 = quarter135_1 := by
  decide +kernel

private def quarter135_2 : Vector UInt64 25 :=
  #v[0x9f684cc9183330bb, 0xb43f5e7154366e5b, 0x33a9901cebb14183, 0xd116de27ff022460, 0x2e2cb2f2791467b1, 0xaaf136869c09fb42, 0x2320db25465a5ca6, 0x4be76b45f68f5861, 0x2ab1caea27e2dd47, 0xfda5ce01ac379b37, 0x8fda50c678cba8ce, 0xd1b3e2f0cf296e7b, 0xaef3d361f3bdf1c1, 0xc3239ceacd1d0869, 0x3a9d7980157b8fa3, 0xe349f247fff9a65e, 0x6cd6fde71e74af3f, 0xf4535f27b0f0c3a3, 0x8ee689974764007c, 0x2850ad327b6bb66, 0x36e03e2ca31e9d41, 0xded3121bb11a2225, 0xa459947b2f49e73b, 0x493c09e46f88ecc1, 0xbb4f38264d09dd67]

private theorem rounds135_1 : sixRounds 6 (by decide) quarter135_1 = quarter135_2 := by
  decide +kernel

private def quarter135_3 : Vector UInt64 25 :=
  #v[0x8c96c9619cb4bfdd, 0x9b7025ae0f497128, 0x1afc5ce0854686b4, 0x53852590d0fbbc38, 0xb27b1b2b9eaa5f5c, 0xe1579944b691a6af, 0x2d45876e7f94d7bb, 0xef155bcb50ec750, 0x4b78e9bbf8c832c6, 0xccaed422b25b286f, 0xcd1a96de65bb655b, 0xd071a923758d930f, 0xeab3e2cf35b2b74e, 0xa42872ea7f3bfdc6, 0x8c781392c7cf0fc0, 0xea3b0bbc70408923, 0xaf0581d5ee843f12, 0x3a81a87cd604d36, 0x319ebc29c7b8544a, 0xe30395d7c28f4d24, 0xa38e3f9cf47c1ac3, 0xdad7767e6181e82b, 0x18ffc6cbc5d07441, 0x7a19c19935a0e94f, 0x92fc62923353b2c9]

private theorem rounds135_2 : sixRounds 12 (by decide) quarter135_2 = quarter135_3 := by
  decide +kernel

private theorem rounds135_3 : sixRounds 18 (by decide) quarter135_3 = state136 := by
  decide +kernel

private theorem perm135 : KECCAK.f1600 absorbed135 = state136 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds135_0, rounds135_1, rounds135_2, rounds135_3]
  rfl

theorem block135 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes135 ++ tail) state135 =
      KECCAK.Bytes.run 0 tail state136 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes135 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb135 ws)) := by
    rfl
  exact (step state135).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words135).trans perm135))

private def absorb136 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x5b 0xfd 0x90 0x1 0x64)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x81 0x0 0x60 0x16 0x88 0x80 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x81 0x90 0x20 0x60 0x11 0x60 0x52 0x81)) 5 (by decide) (UInt64.ofBytes 0x80 0x20 0x90 0x82 0x91 0x40 0x60 0x52)) 6 (by decide) (UInt64.ofBytes 0x55 0x91 0x90 0x1 0x81 0x1 0x60 0x54)) 7 (by decide) (UInt64.ofBytes 0x12 0xae 0xed 0x71 0x6e 0x7f 0x51 0x82)) 8 (by decide) (UInt64.ofBytes 0xf 0x37 0x60 0x1f 0x4d 0x7f 0xb9 0xb1)) 9 (by decide) (UInt64.ofBytes 0x1 0xae 0xfa 0xa2 0x5f 0x10 0x10 0xef)) 10 (by decide) (UInt64.ofBytes 0x5d 0x84 0x64 0x9c 0x16 0x4a 0x11 0x26)) 11 (by decide) (UInt64.ofBytes 0x90 0x92 0x1 0x81 0x92 0xc9 0x26 0x61)) 12 (by decide) (UInt64.ofBytes 0x52 0x90 0x84 0x1 0x83 0x81 0x52 0x92)) 13 (by decide) (UInt64.ofBytes 0x52 0x1 0x82 0x60 0x60 0x16 0x8a 0x93)) 14 (by decide) (UInt64.ofBytes 0x60 0x52 0x90 0x89 0x1 0x81 0x80 0x60)) 15 (by decide) (UInt64.ofBytes 0x60 0x52 0x93 0x90 0x93 0x1 0x81 0xa0)) 16 (by decide) (UInt64.ofBytes 0x81 0x52 0x90 0x88 0x1 0x84 0x80 0xc0))

private def absorbed136 : Vector UInt64 25 :=
  #v[0x742af1db83ddc848, 0x148ce12a8db4add7, 0x16210e2f0c2cc6ba, 0xb858f4e06ed54d21, 0x3b2614c682823d4a, 0x33a6d89c8ec53a6e, 0x879cc1f035136431, 0x833f96e9a153bc7d, 0xe055ade44ff236f6, 0xed06bfc084eb8a87, 0x3827d5bd32cc37a5, 0x7975effd68ede06b, 0x6da6a9366bce5eec, 0xa2f411442c49cc0a, 0x9a9d65ef95b1e05d, 0x777a7747e365be0f, 0x1d68f7b9332da9a8, 0xb4d03e097a9a137c, 0x71284103de0f8e47, 0xf7e68377e7bd8ee9, 0xfa98b8b4647b20f3, 0xff8558c873b4c9bb, 0x43864b95434aac67, 0xee78e540d931f4c8, 0xb9eef9b4101241bf]

private theorem words136 : absorb136 state136 = absorbed136 := by
  decide +kernel

private def quarter136_1 : Vector UInt64 25 :=
  #v[0x81df74f354b40144, 0x4bfb2249845cd902, 0x3ab9226103b0dc35, 0x762f174658ac98d4, 0xa76aca470b10567e, 0x490d89d9822f8ec9, 0xcecef372ef479cf, 0x8e3b535e95ab2aae, 0x25a92269d3352de3, 0xb3198820dc88f205, 0x2e87cb0db620084d, 0x92a368d0c8cee110, 0xedd94b6ed2d5b51b, 0x94052951b1c07732, 0x68b8e18f2880d052, 0x12564e4e13a191b3, 0x1c67d36fb0a093d4, 0x5c637fc22f58c05f, 0x445984858619d364, 0xb983634753b76d4a, 0xba997a54aabb4588, 0x1b07c9ed638d59dc, 0x7267b1b536657786, 0xeb55758204dc7176, 0x34a14e9a9edd37a6]

private theorem rounds136_0 : sixRounds 0 (by decide) absorbed136 = quarter136_1 := by
  decide +kernel

private def quarter136_2 : Vector UInt64 25 :=
  #v[0x84fe9ee0e8ac661a, 0x9270802b1b9d52cf, 0xaf52cc6955791c28, 0xeda507b6d24d79dc, 0x4b0c0dc6b485b7ed, 0x764a80ab3534b9b5, 0xa2cef9b65b3e2cdb, 0xfafe2e02ef18ffa4, 0x4b6ff2919f2ffbaa, 0x49623d57ea61d0dd, 0xf8838249cd045324, 0x8dab31dc7c874cbb, 0x133d32f1b8ebbf0, 0x216e5fdd15345e76, 0x30f9e3bf54b169, 0x41f98580d23c63e, 0xa0700ffb355ffef9, 0x521be56717d54274, 0x7453bef50cbf0fe0, 0x90dfbfe5f023289d, 0x83931c706a6fe9a8, 0xa5388e4eeab1d891, 0x584828ef5d3597ed, 0x2e20c45927fe2e31, 0x3ceb044cdbfc0fec]

private theorem rounds136_1 : sixRounds 6 (by decide) quarter136_1 = quarter136_2 := by
  decide +kernel

private def quarter136_3 : Vector UInt64 25 :=
  #v[0x2e289a5c12775264, 0x9daaf6b291789cf8, 0xec0bf851d7fb4ef4, 0x884bebe5a184b218, 0xbcc4269edf242451, 0x60f4b22d9fffc260, 0x3d8d26ed1373aaca, 0xb24223f17aed4b23, 0x312472bd949c143f, 0xef953cfb1acfaa57, 0xf62c4d8fce2a66ac, 0x9c7b9f79da46c432, 0xfcacfd93501211fe, 0x4cf889e29a8d61fc, 0xc1083cea291b9760, 0x63e923e1f1c0688b, 0x3227a9e01d7d9184, 0x76c9557ea67b870a, 0xecdfe8df929f2010, 0x39793dc9476b7bbe, 0x130a7e5863fb0150, 0xac8b1bca23c675ae, 0x141319ae96ba8fd1, 0x6ba3a620ae09f585, 0xe9a3bbcc255cf973]

private theorem rounds136_2 : sixRounds 12 (by decide) quarter136_2 = quarter136_3 := by
  decide +kernel

private theorem rounds136_3 : sixRounds 18 (by decide) quarter136_3 = state137 := by
  decide +kernel

private theorem perm136 : KECCAK.f1600 absorbed136 = state137 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds136_0, rounds136_1, rounds136_2, rounds136_3]
  rfl

theorem block136 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes136 ++ tail) state136 =
      KECCAK.Bytes.run 0 tail state137 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes136 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb136 ws)) := by
    rfl
  exact (step state136).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words136).trans perm136))

private def absorb137 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x81 0x1 0x91 0x90 0x3 0x85 0x80 0x51)) 1 (by decide) (UInt64.ofBytes 0x52 0x90 0x1 0x93 0x90 0xe0 0x60 0x52)) 2 (by decide) (UInt64.ofBytes 0x86 0x90 0x6d 0x48 0x61 0x54 0xf 0x60)) 3 (by decide) (UInt64.ofBytes 0x5b 0x56 0x2c 0x4d 0x61 0x86 0x86 0x86)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x61 0x14 0x16 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x7f 0x51 0x80 0x40 0x60 0x57 0xef 0x48)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x1 0x82 0x4 0x60 0x20 0x60 0x52 0x81)) 13 (by decide) (UInt64.ofBytes 0x52 0x1 0x82 0x24 0x60 0x1e 0x60 0x52)) 14 (by decide) (UInt64.ofBytes 0x6b 0x6f 0x54 0x74 0x61 0x69 0x46 0x7f)) 15 (by decide) (UInt64.ofBytes 0x6e 0x69 0x20 0x3a 0x32 0x56 0x6e 0x65)) 16 (by decide) (UInt64.ofBytes 0x69 0x73 0x20 0x64 0x69 0x6c 0x61 0x76))

private def absorbed137 : Vector UInt64 25 :=
  #v[0xabbbad808e01814b, 0xae2ec4239563e431, 0xf41a095ee88de2c2, 0x593fa47e944df4bd, 0x6d30e291bd150ae7, 0x7a82b242c1fb2d55, 0x5a6dc2ca594d95fc, 0xb798a975fbcd456a, 0x1ce110952a119de6, 0x6da2a309142ad9d9, 0x1ed665ec2c0a6dbd, 0x3b9cb0792f76e2e7, 0xbe82c11abf4e20b0, 0x7d8a8d9f88358ba8, 0x24a4d818b2154011, 0xee8f316cd3649de6, 0x212fcbd4975f67e1, 0x81898154e5652b58, 0xe92634767fb95800, 0xa8c14d5c079ccd23, 0xb24bff0e72abcecd, 0xaf34e704b86b7b18, 0xe014fc9b87317359, 0x2d558fec7d13ce03, 0xd322f6064adeb92a]

private theorem words137 : absorb137 state137 = absorbed137 := by
  decide +kernel

private def quarter137_1 : Vector UInt64 25 :=
  #v[0xc7df4df37223dfb1, 0xa8a8c1436e643ac5, 0xd9ce6aa1db66fa7b, 0xeede2971877f71, 0x3adaed0a710cf1d3, 0xd87ca9963efe8e2b, 0x55ed5c4841819397, 0xa10aca19f9138227, 0x2bbd94668aa5ac9, 0x14f2e9d6e5bbee7b, 0xb9a2fce7d0b3eaf3, 0x73d3ffea7d85c94, 0xbd47be695c6e906, 0xb5800dbf04c440f7, 0x4ad478aec88cc40f, 0x5cc170f062007865, 0xa828497ef2674eeb, 0xa06380bc6437f19c, 0x5c7a835863a44221, 0xbe6c2f4198b29115, 0x5bf71fa6adcf5cc7, 0x4001b242d2796406, 0xe5502002e37aa9a9, 0x9e8fb5cdfb6fc9d3, 0xf8793122cd2290c9]

private theorem rounds137_0 : sixRounds 0 (by decide) absorbed137 = quarter137_1 := by
  decide +kernel

private def quarter137_2 : Vector UInt64 25 :=
  #v[0x36dfad658c752ece, 0x5a1c0e350634d768, 0xef95a5a420685c80, 0xc2b262fc321ec5dc, 0x727a40b7dcb6c7a0, 0xdf7f4df1b5e219ae, 0x10aec9832957c26e, 0x6f08e3bdae7dfcae, 0x85ac0f24554a14e7, 0x8d718b62a9ad3979, 0x8e89f3979ef9e9ae, 0x4d3590bdea6c219e, 0xca3eee47295d81a4, 0xc29ef55d22f98052, 0x2bd7fc2c44cdd637, 0xb3ce91cc73b8ec5a, 0x6c9f94c7aa647a6c, 0x2c3133809b700423, 0x7400f6c5adf37402, 0xd840d3c80b583457, 0xfb9090e857bccfd2, 0xb74d1cce3867b25f, 0x21f101cb180d18bd, 0xa7899a7b927d469, 0xe451deed40d1fe9b]

private theorem rounds137_1 : sixRounds 6 (by decide) quarter137_1 = quarter137_2 := by
  decide +kernel

private def quarter137_3 : Vector UInt64 25 :=
  #v[0x896a94242536fc4f, 0x934d5537a22a0853, 0x36990bfdb02d1bc7, 0x9ea020dd825eb95e, 0xb320613f1068ff16, 0x7ec3915b8afd363d, 0xe52ad264f4184f34, 0xc4b28b070c2a48a3, 0xcf3fcae958f24dd1, 0x1121861174b34756, 0x144cba34d906404b, 0x7fff03e0ece2a644, 0x38788a34389447eb, 0x1c032f29d1d201e9, 0x9ee3ed0e5bdb71ef, 0x37d96acbf10e3411, 0xe3581e61e0aff0e6, 0xdd468bcc5ce812b6, 0xb526560d94187dde, 0x86e114992317b719, 0x25325a8aa263df94, 0x9d812fb4a55f3908, 0xc2135a9d8cbd9c64, 0xa78e636c180733d2, 0xbad75c0465087b38]

private theorem rounds137_2 : sixRounds 12 (by decide) quarter137_2 = quarter137_3 := by
  decide +kernel

private theorem rounds137_3 : sixRounds 18 (by decide) quarter137_3 = state138 := by
  decide +kernel

private theorem perm137 : KECCAK.f1600 absorbed137 = state138 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds137_0, rounds137_1, rounds137_2, rounds137_3]
  rfl

theorem block137 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes137 ++ tail) state137 =
      KECCAK.Bytes.run 0 tail state138 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes137 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb137 ws)) := by
    rfl
  exact (step state137).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words137).trans perm137))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
