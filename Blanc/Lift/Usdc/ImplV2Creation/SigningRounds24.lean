import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb144 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x4 0x60 0x52 0x81 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x81 0x82 0x1 0x20 0x60 0x80 0x80 0x1)) 3 (by decide) (UInt64.ofBytes 0x81 0x51 0x81 0x81 0x83 0x52 0x82 0x3)) 4 (by decide) (UInt64.ofBytes 0x51 0x80 0x50 0x91 0x1 0x20 0x60 0x52)) 5 (by decide) (UInt64.ofBytes 0x83 0x83 0x80 0x90 0x1 0x20 0x60 0x90)) 6 (by decide) (UInt64.ofBytes 0x61 0x15 0x10 0x81 0x83 0x5b 0x0 0x60)) 7 (by decide) (UInt64.ofBytes 0x83 0x51 0x1 0x81 0x81 0x57 0x50 0x4c)) 8 (by decide) (UInt64.ofBytes 0x4c 0x61 0x1 0x20 0x60 0x52 0x1 0x82)) 9 (by decide) (UInt64.ofBytes 0x90 0x50 0x50 0x50 0x50 0x5b 0x56 0x38)) 10 (by decide) (UInt64.ofBytes 0x16 0x1f 0x60 0x90 0x1 0x81 0x90 0x50)) 11 (by decide) (UInt64.ofBytes 0x82 0x80 0x57 0x7d 0x4c 0x61 0x15 0x80)) 12 (by decide) (UInt64.ofBytes 0x20 0x60 0x83 0x1 0x60 0x51 0x80 0x3)) 13 (by decide) (UInt64.ofBytes 0x16 0x19 0x3 0xa 0x0 0x1 0x61 0x3)) 14 (by decide) (UInt64.ofBytes 0x5b 0x50 0x91 0x1 0x20 0x60 0x52 0x81)) 15 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x50 0x50 0x50 0x92 0x50)) 16 (by decide) (UInt64.ofBytes 0x50 0x50 0x5b 0xfd 0x90 0x3 0x91 0x80))

private def absorbed144 : Vector UInt64 25 :=
  #v[0xabc4556d9e190789, 0x55c14d8388f61646, 0x75936ea3921c7dfa, 0xb36d8e5f28be10be, 0xe6e20b009cb74c7e, 0x648b6df3e10e328c, 0x7aa55bb2e2d628ba, 0xbe3a301efbd4615a, 0xc8b691e27244db47, 0xc9a7bee0367f9b8d, 0x40c12ef9fadc0bb0, 0xda6039cd93f43b5f, 0x7649418ebd0c6214, 0xa31a466fc6078cbd, 0x8c3ffe28291c71bd, 0xa3310916baea9b37, 0x9b77c9fd570a4245, 0xa1cb929295f433d9, 0x453605e42106fd75, 0xde27835ce347eb7f, 0x2d6d089c830ad0d5, 0xb5b90a198fae0319, 0xfb5cea6fe48fb8a5, 0x82d64da25dda1b82, 0xbbbd29e23e35c612]

private theorem words144 : absorb144 state144 = absorbed144 := by
  decide +kernel

private def quarter144_1 : Vector UInt64 25 :=
  #v[0x81f31cff240c2e82, 0xc43421ff4c2cd57c, 0x7c134ab8b1ec6db8, 0x6bba414d9c2cef4b, 0xe31a8dddb5ef695f, 0x73fa0c04acfd891a, 0x73316ee6cad04bed, 0x9d6ef58f41fbdb48, 0x30c45c5c235fa48e, 0xa8dd9374ea6c5158, 0x7daf2c4210878792, 0x2b34f1c6c141e58d, 0x8149597c69c4d715, 0x46c994f2788e96df, 0x83be6e129b3fd0e2, 0x7dbb134bb8d544f3, 0xadaca08aba06972f, 0x7127d261829c797a, 0x47b663c37d12a6fa, 0x833a0dc7568749e5, 0x9c7886efd8e96012, 0xba3bcb455d08e56a, 0x4581e3deff88a843, 0x365c00ede7c965c3, 0xcfa06f4d30eec1bf]

private theorem rounds144_0 : sixRounds 0 (by decide) absorbed144 = quarter144_1 := by
  decide +kernel

private def quarter144_2 : Vector UInt64 25 :=
  #v[0xbac66ae1859b85f7, 0xf70879ca217e9bf5, 0x71f1257b9f1d25bf, 0x8040a2bf0c8c8ac2, 0x23515ad085a0bf49, 0xff082b896a6c6a7, 0x93fcadd40aa0bd1, 0x5ef864a864c39fb9, 0x178abb815bc14b1f, 0xe364ccd8919f9c4a, 0x2672c4ab1ed0aec1, 0x3b70f6ebdc240d36, 0x6584596213da8b62, 0x4c81c87fdb1f862e, 0x4f878575758fcaac, 0xa7e60fdeb738085e, 0x3a3fb15fbf07710, 0xd3358133daf6794d, 0xbef3ea4c31107301, 0x3aa8b186151aaa4c, 0xb05c48e7310f3ea1, 0x12a090373d3e948d, 0x155efe61667c1aa8, 0x6e915ba9a4a33870, 0xc79a7a0209911aac]

private theorem rounds144_1 : sixRounds 6 (by decide) quarter144_1 = quarter144_2 := by
  decide +kernel

private def quarter144_3 : Vector UInt64 25 :=
  #v[0x9add77d55c6f4028, 0xa03d9007e7c3d3b5, 0x7831db4f92fa9b9b, 0x3a6b6a1d713cd879, 0x34f62146eb5296e5, 0x85feebef8e71045e, 0x484552bca281fcbd, 0x1a0372f232f9996, 0x8796ea9ef7298dd8, 0xb747e4f1cbd9ce6d, 0xe7596ba8ce5b2ff9, 0xe76c37a6d9e52b8c, 0x915d0a0eb362d022, 0xc7e82502df648432, 0x90a1479a21ac8fe7, 0xdb1efa70819b4990, 0xabb66064c1333162, 0x94a73d8fee476ccf, 0x9b4c63a7fdff64d2, 0xfffebc1f329ce5f3, 0x979603ab35c551a7, 0xb0be879b2f615f2d, 0x3fddce3d49c234c, 0x758ec0b46ec53e3e, 0xea48aa3397ed3963]

private theorem rounds144_2 : sixRounds 12 (by decide) quarter144_2 = quarter144_3 := by
  decide +kernel

private theorem rounds144_3 : sixRounds 18 (by decide) quarter144_3 = state145 := by
  decide +kernel

private theorem perm144 : KECCAK.f1600 absorbed144 = state145 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds144_0, rounds144_1, rounds144_2, rounds144_3]
  rfl

theorem block144 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes144 ++ tail) state144 =
      KECCAK.Bytes.run 0 tail state145 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes144 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb144 ws)) := by
    rfl
  exact (step state144).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words144).trans perm144))

private def absorb145 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0x73 0x5b 0x56 0x90 0x3 0x90 0x50)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x90 0x0 0x60 0x16 0x82 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x81 0x90 0x20 0x60 0x10 0x60 0x52 0x81)) 5 (by decide) (UInt64.ofBytes 0x84 0x84 0x20 0x83 0x80 0x40 0x60 0x52)) 6 (by decide) (UInt64.ofBytes 0x60 0x54 0x20 0x81 0x52 0x91 0x90 0x52)) 7 (by decide) (UInt64.ofBytes 0x61 0x15 0x11 0x81 0x2 0x60 0x16 0xff)) 8 (by decide) (UInt64.ofBytes 0x4d 0x61 0x14 0x5b 0xfe 0x57 0xd2 0x4c)) 9 (by decide) (UInt64.ofBytes 0xc3 0x8 0x7f 0x51 0x40 0x60 0x57 0x28)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0xa0 0x79)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x52 0x81 0x0 0x0 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x80 0x80 0x1 0x4 0x60)) 15 (by decide) (UInt64.ofBytes 0x81 0x2e 0x60 0x52 0x82 0x3 0x81 0x82)) 16 (by decide) (UInt64.ofBytes 0x65 0x59 0x61 0x80 0x1 0x20 0x60 0x52))

private def absorbed145 : Vector UInt64 25 :=
  #v[0xdaab22cff1b50368, 0x1ede25c63cae2733, 0xd8b51c3f237754eb, 0xd20d39dadeb24bbf, 0xdbc50d02d5693120, 0x8398e0143c4af8a7, 0x446c90cbc1176eb3, 0xa352df4d717d139d, 0x81c46b87cb7408bd, 0xbe46c627d90d9942, 0x7a75d9e8b88662d0, 0xd062335c983797a8, 0x49c6c0619f7d7a7f, 0xc5270fbf8270f44d, 0xb34730d674eec107, 0xfdf2a5e202ecb840, 0xad47a69c7e291069, 0xa6c8fcd575966db7, 0x5cc2dd008dbd4a8, 0x601636dfa2183e19, 0x6e8160875ded9a4c, 0x2f1d79948b707309, 0x3e9cea9f90f7653d, 0xc3fc546e2f697526, 0x267f9b5dd8a2bc42]

private theorem words145 : absorb145 state145 = absorbed145 := by
  decide +kernel

private def quarter145_1 : Vector UInt64 25 :=
  #v[0xcf61da92a9badc29, 0x226ec0f9b6c488af, 0x25280a448c96dd83, 0x83954965b117c48c, 0x367fa33f5fabc1bf, 0x1d3c245f0bb2dd6f, 0xe75c4f81f2f1259f, 0x899c15bb956ef38, 0x647eacb5ce472659, 0xb4a09ff4b86cea97, 0x5dbf80f881ea9f4e, 0xf7e978b4f50f8c0, 0x53e8c760bdedce52, 0x7982dfc2f9485181, 0x4869a1c8a6429a5f, 0x142b23797325bd6a, 0x76b76d7298c65f65, 0x3834d1e1832c5608, 0x11c5c57978bd75b0, 0x124e045906658f1, 0xb2e2276a834e6889, 0x3e152cd2f25525b2, 0x50b246af053717d6, 0xff707e16c03eba64, 0x88ef40adab5d0449]

private theorem rounds145_0 : sixRounds 0 (by decide) absorbed145 = quarter145_1 := by
  decide +kernel

private def quarter145_2 : Vector UInt64 25 :=
  #v[0x421f6b5aff9a2f11, 0xc11a5fcc727bac00, 0x907226817a089a2e, 0xb00c63ea2a983325, 0x53df143892c36c3c, 0x8f3b21bd4e6f25d2, 0x401eb3de8e6e4851, 0xf320376040a5d0f, 0x882d75c03cf71dbc, 0xbf09cd56d4170d3f, 0xeba81041c55364f2, 0x60efde006fd52b23, 0x90a64db77848eb29, 0x71549c0abc8400fa, 0x8471f844da4ddf08, 0xccabfce4dbb5b91, 0xaa25439cb2e63877, 0x870f9bd191788074, 0xb982680985d5bdd3, 0x382a4cab4c2272da, 0x61d8eec0887eed82, 0xcab36051aa455508, 0xd8d07a881e699b73, 0x8f0055a5ee44bac9, 0x80f65f874b1140f9]

private theorem rounds145_1 : sixRounds 6 (by decide) quarter145_1 = quarter145_2 := by
  decide +kernel

private def quarter145_3 : Vector UInt64 25 :=
  #v[0x4708b6d36e12f47a, 0x2bef46f461287dac, 0x2bd99a0dff25e2a, 0x47551c2c75023a16, 0xa427a14b75b705b7, 0x2421696ab89ae4c9, 0xbc62d81fb3f908de, 0x75f358955fd5b2c4, 0x3648a5e88102fda4, 0x81f3a61c5203680, 0x4b37740b87626f8, 0x3cfedcca675080a9, 0x1a3e18e6d186ecd4, 0x631bbe6d0229b378, 0xe199f9c01abec991, 0x5d8e8e497424d4c5, 0xf84e9cc87bb815cd, 0x84af547e9c95290e, 0xec424d09ae21a3, 0xcd9574bc849b19bb, 0x8fe306bdd7404f22, 0x48fd025f3b4d2886, 0x7b6b3e707f768730, 0x51ece82e712cbc05, 0x3212de89a69cbae6]

private theorem rounds145_2 : sixRounds 12 (by decide) quarter145_2 = quarter145_3 := by
  decide +kernel

private theorem rounds145_3 : sixRounds 18 (by decide) quarter145_3 = state146 := by
  decide +kernel

private theorem perm145 : KECCAK.f1600 absorbed145 = state146 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds145_0, rounds145_1, rounds145_2, rounds145_3]
  rfl

theorem block145 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes145 ++ tail) state145 =
      KECCAK.Bytes.run 0 tail state146 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes145 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb145 ws)) := by
    rfl
  exact (step state145).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words145).trans perm145))

private def absorb146 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x91 0x1 0x40 0x60 0x39 0x91 0x2e 0x60)) 1 (by decide) (UInt64.ofBytes 0x3 0x91 0x80 0x51 0x40 0x60 0x50 0x50)) 2 (by decide) (UInt64.ofBytes 0x80 0x5b 0x56 0x50 0x50 0x5b 0xfd 0x90)) 3 (by decide) (UInt64.ofBytes 0x90 0x91 0x1 0x83 0x80 0x20 0x60 0x51)) 4 (by decide) (UInt64.ofBytes 0x19 0x7f 0x51 0x80 0x40 0x60 0x20 0x91)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x1)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x81 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x89 0x1 0x81 0x22 0x60 0x52 0x1 0x85)) 10 (by decide) (UInt64.ofBytes 0x93 0x1 0x82 0x80 0x42 0x60 0x52 0x90)) 11 (by decide) (UInt64.ofBytes 0x3 0x82 0x80 0x51 0x81 0x52 0x93 0x90)) 12 (by decide) (UInt64.ofBytes 0x1 0x62 0x60 0x52 0x83 0x1 0x93 0x90)) 13 (by decide) (UInt64.ofBytes 0x60 0x20 0x1 0x91 0x51 0x80 0x52 0x90)) 14 (by decide) (UInt64.ofBytes 0x87 0x87 0x81 0x93 0x4d 0x61 0x90 0x0)) 15 (by decide) (UInt64.ofBytes 0x96 0x97 0x5b 0x56 0xbb 0x4f 0x61 0x87)) 16 (by decide) (UInt64.ofBytes 0x56 0x50 0x50 0x50 0x50 0x50 0x50 0x50))

private def absorbed146 : Vector UInt64 25 :=
  #v[0x351ed7d687a9a1df, 0x387bf3ffc18ac924, 0x43e678dd28fe3fe3, 0x88bf0e6114b600f3, 0xec0161ea8de0fa93, 0x919cb9fcad0efee6, 0x5fa8ce58466fe3f4, 0x93be0cb5a856482e, 0xda3b97a466eb9f2e, 0x4c47a5a2b405ccf2, 0x4a58aee1791a42b4, 0x96608db756e19416, 0x9ec4bb45af842297, 0x499b636ac7741013, 0x9a1f4d0f2c1dc617, 0xdf25dce32c7c5ab6, 0x5665e138f526919d, 0xd62c3d05a253a530, 0x2fc15b759c65ffd5, 0xa7ddb4002e7d6926, 0xefabac336e5acded, 0x5757b8d3e6473c41, 0x7b3d4e742830ddda, 0x49562c59fd7766bd, 0x87940540329e61f9]

private theorem words146 : absorb146 state146 = absorbed146 := by
  decide +kernel

private def quarter146_1 : Vector UInt64 25 :=
  #v[0x756b90067c1b4fee, 0x43ac10048f2b0414, 0xa2dcb656c1a7e725, 0xebd8ef3368feba0c, 0x32bd5f6ce78088b7, 0xb7edbad521cf35cd, 0xdf09c9d84a2aba7a, 0xa6af65b16423cde8, 0x6b6a97fa64588834, 0xc5f5f1911dc44900, 0x2a481f4850006087, 0x38f7d93d88ef1b29, 0xa3f1d09bfd821227, 0x257284f4588703f7, 0x59830c3b846e1436, 0xe49e7f1d4a7b8472, 0x9d30ef13f388a042, 0xb9b076a6e3880d4b, 0x9aa9db55f59c12f, 0xcf0960e2fccdf765, 0xd68b8504a7a1b0b, 0xcffb70f42fe5fa68, 0xf5f726475641575d, 0x8e6d225052c19488, 0x88775ed6a0f25dd]

private theorem rounds146_0 : sixRounds 0 (by decide) absorbed146 = quarter146_1 := by
  decide +kernel

private def quarter146_2 : Vector UInt64 25 :=
  #v[0x4feac4a9fc62a00a, 0xb72bbc0f660ee884, 0x7eb838f58930bc3a, 0x3ae5284b5e988bf3, 0xae9ae4e0f5c7aea5, 0xbbae7644e4f1ca03, 0xf06130f192f5ed34, 0xaef017cfa8da6092, 0x22595befa3f37fd, 0x2f27443ddff3b9f1, 0x14a2d29223ed8539, 0x51e75df6d5955458, 0x7f0646d7179807a0, 0xd840e7a05d9328bd, 0x786c418a98761ea5, 0x8213ce896f6a8a60, 0x5793a253afdb689, 0x6ca49e8e3a7132b3, 0x5b284e5b174b9098, 0x1d3a6fe968b83a58, 0xe4e8df6b8969d8ff, 0xeea8816f2413b962, 0x6392f3679430222f, 0xe8415eb8368c143e, 0xa5f5d66de7d44794]

private theorem rounds146_1 : sixRounds 6 (by decide) quarter146_1 = quarter146_2 := by
  decide +kernel

private def quarter146_3 : Vector UInt64 25 :=
  #v[0x3d56ca86b75c2ef6, 0xacdd862bad50fc6a, 0xb3c95096437f33ca, 0x1612e2ced226c64b, 0x74d9ea5bd8b74564, 0x7606d2853549dcb3, 0xa94f1d540b2073aa, 0xc362170a551dcf, 0x4dfee5cb579fe936, 0x3eea56e208215541, 0xacc9aeef4a98433c, 0xbae20d14622d27b9, 0xdb28329a55c0c107, 0x74145ac6f7ec4f79, 0x5ba4c3df932ecb4e, 0x6e10c9a216c1023f, 0xe9af1ccbf09a0702, 0x6ca5af50db6a9752, 0xc30e79cbdf289535, 0x441b96ac6b2d58a5, 0x366bc7fb13d3cf4a, 0x6043c8be9e1c1c13, 0x16d7941087a7df9d, 0x34ef2c50b6490cf9, 0x479afc30a25ff4ed]

private theorem rounds146_2 : sixRounds 12 (by decide) quarter146_2 = quarter146_3 := by
  decide +kernel

private theorem rounds146_3 : sixRounds 18 (by decide) quarter146_3 = state147 := by
  decide +kernel

private theorem perm146 : KECCAK.f1600 absorbed146 = state147 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds146_0, rounds146_1, rounds146_2, rounds146_3]
  rfl

theorem block146 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes146 ++ tail) state146 =
      KECCAK.Bytes.run 0 tail state147 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes146 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb146 ws)) := by
    rfl
  exact (step state146).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words146).trans perm146))

private def absorb147 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x57 0xf6 0x4d 0x61 0x11 0x42 0x81 0x5b)) 1 (by decide) (UInt64.ofBytes 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x40 0x60)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x4 0x60 0x52 0x81 0x0 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x81 0x82 0x1 0x20 0x60 0x80 0x80 0x1)) 7 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x2b 0x60 0x52 0x82 0x3)) 8 (by decide) (UInt64.ofBytes 0x2b 0x60 0x32 0x55 0x61 0x80 0x1 0x20)) 9 (by decide) (UInt64.ofBytes 0x50 0x50 0x91 0x1 0x40 0x60 0x39 0x91)) 10 (by decide) (UInt64.ofBytes 0xfd 0x90 0x3 0x91 0x80 0x51 0x40 0x60)) 11 (by decide) (UInt64.ofBytes 0x57 0x4e 0x4e 0x61 0x10 0x42 0x80 0x5b)) 12 (by decide) (UInt64.ofBytes 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x40 0x60)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 16 (by decide) (UInt64.ofBytes 0x4 0x60 0x52 0x81 0x0 0x0 0x0 0x0))

private def absorbed147 : Vector UInt64 25 :=
  #v[0xed4c516a747df89b, 0xc00b104d9027f3ca, 0x200ac69ad2e53464, 0x1fab0af6c14eb688, 0xf1fb633a035cb114, 0xbe3be69deb78f8dc, 0x7c5fb324ff848ab0, 0xb37f97f154b701fc, 0xfc9cb0431209a6f8, 0x2feb8b0595d4eb62, 0x647fe7a700c80c2a, 0xeb607cb0b0796ad9, 0xb712f0fdd9312482, 0x56bc9d2e379fd943, 0x9dba330d8343cdb, 0x4ede0faa561afc3e, 0xfbbb9fd24ca19146, 0x169c2234effc45c8, 0x71d45cefa45b1426, 0x1a9b00817dc53c0c, 0xa456696c516ca2a6, 0xe5c83a67eec2fb55, 0x1d92819e953fc36, 0x7e834f20e908a01, 0xdbd7b82b686d76a9]

private theorem words147 : absorb147 state147 = absorbed147 := by
  decide +kernel

private def quarter147_1 : Vector UInt64 25 :=
  #v[0xb59550cd39723535, 0x4518f1929fb9e586, 0x25fca8bad07e68eb, 0x5ca963dcb0915c88, 0xe1a7fee027d7dab7, 0x74a59ddef55017f0, 0x11931773f31e2b92, 0x6505b807e6a010e0, 0x7b9d4fb2315acca, 0x883bb730cdbb0e74, 0x1a1386fa6056fdfb, 0x158729b2d192890e, 0x41f11e592e6ff179, 0x2fad19cecd14dda9, 0x892667b9c51e6d02, 0x490c53e51599486b, 0xf97e91548a0286c9, 0xfe42169ddb2bad10, 0xb3e1b0dec58efd02, 0x96b004c45f9ca158, 0x2df2ed79d742e0b3, 0x805075dad359b826, 0x7eab6c83ee14102d, 0x35023204b888177a, 0xb398416fa3c5f6bd]

private theorem rounds147_0 : sixRounds 0 (by decide) absorbed147 = quarter147_1 := by
  decide +kernel

private def quarter147_2 : Vector UInt64 25 :=
  #v[0x7207e327baa2dbf8, 0x9958033400182af8, 0xac7806a9bf4798e2, 0xddcb368035ec3ac7, 0x83f6462787348079, 0xa5331504676638d2, 0x9982abdb27fa6bbe, 0x49a0961b860c7b3f, 0x523863631f36ea32, 0xc2dcd92e5d34d32c, 0x93b95b679c0853da, 0xb00abab86fc7d716, 0x1f6742af284f92f0, 0xdd7d951fb0daf2db, 0x8110c94cf0d77d64, 0xe8357eb17138d2d8, 0x3f27a973cd97e0e9, 0x6272220ca93b5338, 0x78a663d14089b4f, 0x648d15738b0960b6, 0xea2d33828684b94d, 0x12fb7bdf72fae481, 0x512b7e1a63e4db94, 0x7730114a11083d7b, 0xf6d9b202617a5697]

private theorem rounds147_1 : sixRounds 6 (by decide) quarter147_1 = quarter147_2 := by
  decide +kernel

private def quarter147_3 : Vector UInt64 25 :=
  #v[0xa5966cb841ff8a95, 0x4541afd7098cf4fa, 0x8a9816b8fee9fa5d, 0xd56dce0bf09e5142, 0xaf02768b13da2de3, 0x95c64f6d249c4cb1, 0x12fc0448224b7d69, 0xd83a62773248d2ae, 0xecb641f01f96a81f, 0x10f3c384499873a9, 0x7fba80466c3ab92b, 0xd60bc01f8a0167c1, 0x35a19a1ad44371e0, 0x3de1568e933b3f3e, 0x24fbd5c84a6a2454, 0x4eb89229383df660, 0xb0000bda49a1d59f, 0xcf69457646402b05, 0x8022e1c19b729aac, 0xe8729434132a5cc2, 0x201ff48556fba915, 0xf58e084740eed83f, 0xa107c1ec7eccd2d1, 0x270788aa75e5e8e6, 0x9cf34a0c33a83941]

private theorem rounds147_2 : sixRounds 12 (by decide) quarter147_2 = quarter147_3 := by
  decide +kernel

private theorem rounds147_3 : sixRounds 18 (by decide) quarter147_3 = state148 := by
  decide +kernel

private theorem perm147 : KECCAK.f1600 absorbed147 = state148 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds147_0, rounds147_1, rounds147_2, rounds147_3]
  rfl

theorem block147 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes147 ++ tail) state147 =
      KECCAK.Bytes.run 0 tail state148 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes147 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb147 ws)) := by
    rfl
  exact (step state147).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words147).trans perm147))

private def absorb148 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x81 0x82 0x1 0x20 0x60 0x80 0x80 0x1)) 1 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x25 0x60 0x52 0x82 0x3)) 2 (by decide) (UInt64.ofBytes 0x25 0x60 0xea 0x59 0x61 0x80 0x1 0x20)) 3 (by decide) (UInt64.ofBytes 0x50 0x50 0x91 0x1 0x40 0x60 0x39 0x91)) 4 (by decide) (UInt64.ofBytes 0xfd 0x90 0x3 0x91 0x80 0x51 0x40 0x60)) 5 (by decide) (UInt64.ofBytes 0x4c 0x61 0x84 0x84 0x58 0x4e 0x61 0x5b)) 6 (by decide) (UInt64.ofBytes 0x56 0x50 0x50 0x50 0x50 0x5b 0x56 0x93)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x5b)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x16 0x82 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x60 0x10 0x60 0x52 0x81 0x81 0x0 0x60)) 11 (by decide) (UInt64.ofBytes 0x83 0x80 0x40 0x60 0x52 0x81 0x90 0x20)) 12 (by decide) (UInt64.ofBytes 0x80 0x52 0x91 0x90 0x52 0x84 0x85 0x20)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x7f 0x54 0x80 0x20 0x82)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed148 : Vector UInt64 25 :=
  #v[0xfc7082b43c2f77cf, 0x1156efc77df61528, 0x5a28429c4fbf7776, 0xc4c137f896e292d7, 0x64ee7b24c659e470, 0x90d0144fbfd23e48, 0x8b2377fb3cb9267, 0x918cc9161353ad1b, 0x5fbe379ccfc73e67, 0xb735a3840e2e1be1, 0x5106c22f6e965ca4, 0x8f81ec3f78abdd7d, 0x173d95993d8fa97b, 0x1992220ebde4e8f6, 0x647b37b1c123e664, 0x3fc6d52bd00162b8, 0x1380cbe6732eaf0, 0x7f546360638fb13c, 0xe74e51edd9ae1851, 0x1411fb0a7e2274ba, 0x3e49bf985ebf1766, 0xc4092d28b7fb722a, 0xcf737a580c12df0f, 0x90f51e5da54c8c31, 0x615c912fe97ce18c]

private theorem words148 : absorb148 state148 = absorbed148 := by
  decide +kernel

private def quarter148_1 : Vector UInt64 25 :=
  #v[0x29d036e20e2ad84b, 0x11a3d81c3f1d50a4, 0x39707419a92282d3, 0x9f2d2a358de44114, 0xeb22d0f5cdecb838, 0x6340f896951885f3, 0x4e57cbb854b8ae53, 0xa512838d536d6c41, 0x78d48a97baf25363, 0x96f35522081a6a0, 0xa27f14b1356584d2, 0x651f686ae6562465, 0x93eea1b5ca368368, 0xec0812196f12c034, 0x69ade15c84177364, 0x2763471753a4d748, 0xc2dfd00240255b00, 0xfcf6f3e55c938390, 0x33a03434a5e18d83, 0x2b1c49875c6b6b0b, 0xa4376d10634b1913, 0x5d64c302bd7bd93b, 0xa26a1967d5c689a, 0x9c445dfc9ec930cf, 0x18795b514c5374c9]

private theorem rounds148_0 : sixRounds 0 (by decide) absorbed148 = quarter148_1 := by
  decide +kernel

private def quarter148_2 : Vector UInt64 25 :=
  #v[0x94107a0ee35aec50, 0xc25e4915469456e0, 0x75a005d70e745a05, 0x92df4278a72105aa, 0xdc18e400389dcb21, 0x4d56530b81b83f24, 0x13df68da28d846de, 0x3ec19ce853941f45, 0x352d661f8e3fe734, 0xe057fa5783ed2f1d, 0xea453468c915d9ba, 0x88233e988fb84914, 0xe3cb44bcd91cafdd, 0xcfe60163270863ac, 0x3a811d21b8cba7e3, 0x43794eb17819f27e, 0x5b56c6a8a57ba144, 0x236c6dba47a54158, 0x1dcd5a5abe33cafd, 0x8ec834df8ae4c881, 0x54de8d67f2c0aa16, 0x612c36c6b6107c53, 0x4b7033c621fa98f6, 0x617811c51f40e6a1, 0x3130eb6ab6230c81]

private theorem rounds148_1 : sixRounds 6 (by decide) quarter148_1 = quarter148_2 := by
  decide +kernel

private def quarter148_3 : Vector UInt64 25 :=
  #v[0x5b7883a6e8ef8119, 0xdba1cda457bf66ae, 0xfdd01d7140aefc06, 0xb6b6fecc5b774e94, 0x2724e8232399215a, 0x8f6e5e69679996fd, 0xb1f1eed40c3f075a, 0x14d7c035cb690486, 0x83587229cda64d8, 0xd7e9f9fda83150e0, 0x18eb995461d8f469, 0x87f9bd820a233dd9, 0x626de8105758bb29, 0x6c4d5fabfad1d2e, 0x65a063ebb24e913a, 0x7bdc4d3da79eec41, 0x1d519dd497e676e, 0xb9a568482c4e988b, 0x8562192bc255e0ae, 0x90d1490e2781b25a, 0x1076c748b5dd67c6, 0x306f7cf2bae870de, 0x7009a0e9aacf8a75, 0x874412d656a59c4f, 0x40ab4d8e1bff930e]

private theorem rounds148_2 : sixRounds 12 (by decide) quarter148_2 = quarter148_3 := by
  decide +kernel

private theorem rounds148_3 : sixRounds 18 (by decide) quarter148_3 = state149 := by
  decide +kernel

private theorem perm148 : KECCAK.f1600 absorbed148 = state149 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds148_0, rounds148_1, rounds148_2, rounds148_3]
  rfl

theorem block148 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes148 ++ tail) state148 =
      KECCAK.Bytes.run 0 tail state149 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes148 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb148 ws)) := by
    rfl
  exact (step state148).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words148).trans perm148))

private def absorb149 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x1 0x60 0x16 0x0 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x7f 0x91 0x92 0x83 0x51 0x55 0x90 0x17)) 2 (by decide) (UInt64.ofBytes 0xb5 0x59 0xee 0x28 0x35 0x50 0xde 0x98)) 3 (by decide) (UInt64.ofBytes 0x24 0xa8 0x76 0x25 0xa 0xc 0xef 0x75)) 4 (by decide) (UInt64.ofBytes 0x20 0x5b 0x68 0xa5 0x29 0xc0 0xbf 0x97)) 5 (by decide) (UInt64.ofBytes 0xa5 0x10 0x9b 0x47 0x33 0xc3 0x9e 0x9e)) 6 (by decide) (UInt64.ofBytes 0x60 0x60 0x5b 0x56 0x50 0x50 0xa3 0x91)) 7 (by decide) (UInt64.ofBytes 0x80 0x51 0x40 0x60 0x82 0x45 0x4f 0x61)) 8 (by decide) (UInt64.ofBytes 0x60 0x80 0x52 0x40 0x60 0x1 0x40 0x60)) 9 (by decide) (UInt64.ofBytes 0x53 0x7f 0x1 0x20 0x60 0x52 0x81 0x20)) 10 (by decide) (UInt64.ofBytes 0x30 0x32 0x43 0x52 0x45 0x65 0x66 0x61)) 11 (by decide) (UInt64.ofBytes 0x65 0x6c 0x2d 0x77 0x6f 0x6c 0x20 0x3a)) 12 (by decide) (UInt64.ofBytes 0x6c 0x6c 0x61 0x63 0x20 0x6c 0x65 0x76)) 13 (by decide) (UInt64.ofBytes 0x81 0x64 0x65 0x6c 0x69 0x61 0x66 0x20)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x85 0x50 0x52)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed149 : Vector UInt64 25 :=
  #v[0x67b522431ad8bd5d, 0xfacb51ab1565f96, 0x4f497aee6f1b89a6, 0x84a54e4f80f54f1, 0x36aa7d0fec87c0ce, 0x81182152a615b9f3, 0xf9265e2c739df925, 0x302e62ce12d20ea8, 0x5d1573a4cd70ca37, 0xf2eff65b8d0f60e4, 0xa02157145e7f5066, 0x5113ab9ea1ab601a, 0x74b5df4437d1b78a, 0x109228c2a4c46270, 0xbe0ec472941ba722, 0x894419778b04f70a, 0x51640a9cb2c3ad0a, 0xfef3194ccddbe6ef, 0x245656fbe0cbe5ad, 0x35459d8de08f1aa3, 0x5f9beb9f90c9b787, 0xe3dbb1f5e46c27af, 0xc4a8062a1d3556af, 0x56439e1af12eadd9, 0xb10f095dc8b0dbe2]

private theorem words149 : absorb149 state149 = absorbed149 := by
  decide +kernel

private def quarter149_1 : Vector UInt64 25 :=
  #v[0xe56a1341b51dde9d, 0x707b8b1c1693d7f7, 0xd6ba2eeab57bfff4, 0xf73c018ec4a369b7, 0xbd190b1ae22063c0, 0x4d63da2ede0b12e1, 0xe08a5cc6b5a49421, 0x287301246654974d, 0xd581d650edbf1579, 0x895f64c31bdcb1a7, 0xc070735e8c20b86f, 0x1c335bf6e8ffd256, 0x7b13ff52c14ebf49, 0x9ff60f5d2f910ce2, 0xdaa0a8869f02a9b2, 0x290da7c79c12360f, 0x49ac9436b69446f, 0x83064c0254493ce, 0xaca9f1fca7fde0ea, 0x87746d7cadc8245, 0xbcc0ae3a6bc8643d, 0x8f28dec3348d35ec, 0x167fabeef155ce37, 0xb385d875cf7e688a, 0xa85b594a5e469508]

private theorem rounds149_0 : sixRounds 0 (by decide) absorbed149 = quarter149_1 := by
  decide +kernel

private def quarter149_2 : Vector UInt64 25 :=
  #v[0xcf2bdebe897cfeb7, 0x5bf5a2209b0879e, 0xfd8e63f679b2ddd, 0xefaf3ac061b4c750, 0x1f56604384e24b00, 0x17e82095e8652580, 0x1ca6df391a9bdd08, 0x4726aa6b5a0d2af7, 0x5588716890c0b547, 0x79d199b5d56ac494, 0xe5f48334074c1918, 0xd8cec3fc686105a6, 0x387df69570f02df8, 0x76d05b4aaf5431e, 0x3b112c59cf75580, 0xbb2ac2456760e223, 0xbf8c388410a466e6, 0x5aef77cef29f648c, 0xf677ca5f527a04e7, 0x1d9b9beb1c4b87cc, 0x74a0bfd878b09b77, 0xfcd56414ac3fef49, 0x748abf2fecb90c9b, 0xb6f58dc054139821, 0xc9a14582ed4f96ef]

private theorem rounds149_1 : sixRounds 6 (by decide) quarter149_1 = quarter149_2 := by
  decide +kernel

private def quarter149_3 : Vector UInt64 25 :=
  #v[0xe945f27a5813ed76, 0x10cb67d15d0023dd, 0x8ecdd2ee71e9058b, 0xbb7c3400c0a87acd, 0xb0d07f5e3e36e9d9, 0x45c66744fcf25499, 0x8a9eadd485ee94a7, 0xa86f50d083d82385, 0xa8209d1094825066, 0x67eb0125e9315b95, 0x8f2957ef0691dd70, 0xbc369b6e0e459cc3, 0x9454739ebbb87996, 0x380972a0f5422975, 0xbf1a67f096483f62, 0x96a3211975adc16, 0x6bcf8f6f540e5202, 0x4a180af0b54f659d, 0x4b7088f914fb5b4c, 0x50735593a1a06ad7, 0xd0863343d8841980, 0xe7e7c7a11605e2c5, 0xe4ad9891a7413fbb, 0x4cdd76c777aea34c, 0x7904b28b8c7f0684]

private theorem rounds149_2 : sixRounds 12 (by decide) quarter149_2 = quarter149_3 := by
  decide +kernel

private theorem rounds149_3 : sixRounds 18 (by decide) quarter149_3 = state150 := by
  decide +kernel

private theorem perm149 : KECCAK.f1600 absorbed149 = state150 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds149_0, rounds149_1, rounds149_2, rounds149_3]
  rfl

theorem block149 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes149 ++ tail) state149 =
      KECCAK.Bytes.run 0 tail state150 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes149 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb149 ws)) := by
    rfl
  exact (step state149).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words149).trans perm149))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
