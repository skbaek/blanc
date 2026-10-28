import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb042 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x1 0x40 0x60 0x39 0x91 0x2a 0x60 0x40)) 1 (by decide) (UInt64.ofBytes 0x91 0x80 0x51 0x40 0x60 0x50 0x50 0x91)) 2 (by decide) (UInt64.ofBytes 0x54 0x80 0xe 0x60 0x5b 0xfd 0x90 0x3)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x7f)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x16 0x0)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x83 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x60 0x55 0x91 0x90 0x17 0x81 0x90 0x16)) 11 (by decide) (UInt64.ofBytes 0xd8 0x80 0xe5 0x75 0xe4 0x7f 0x51 0x40)) 12 (by decide) (UInt64.ofBytes 0x33 0xca 0xd8 0x40 0x8e 0x34 0x11 0x51)) 13 (by decide) (UInt64.ofBytes 0x5c 0x65 0xe1 0xf 0xc3 0x74 0xdd 0xcf)) 14 (by decide) (UInt64.ofBytes 0x6 0x10 0xbc 0x3a 0xa1 0x37 0x85 0x2d)) 15 (by decide) (UInt64.ofBytes 0xa2 0x90 0x0 0x60 0x90 0x5a 0xfa 0x5f)) 16 (by decide) (UInt64.ofBytes 0x0 0x60 0x54 0x8 0x60 0x5b 0x56 0x50))

private def absorbed042 : Vector UInt64 25 :=
  #v[0x156f35d934b76264, 0xb26052b4d508ad1e, 0x31433bef35e30247, 0x6aafeac47914be34, 0x74d4c32f741290a9, 0x81816804213f0834, 0x86f3032416d03e4f, 0x9ce10a5e03e7e8f, 0x52b7989db9cec605, 0x30065fd57beeda86, 0x5d43a642ea923500, 0x37253e1913ca3cfb, 0x8ea3ad87b80dceaa, 0xe07cde1bfae6acb2, 0xf474aae628ee26c7, 0xac99b6409e8be9bd, 0x2741dcda4b4281af, 0x6f113320b8937a4b, 0x39af1ada1a728ada, 0xc1d00ecbfd5b0d4, 0xf86218c8fd9412d5, 0x6a41775c411331a5, 0x39ade17cadc43594, 0xd8fbbd06a985d753, 0x253789f128ecb13b]

private theorem words042 : absorb042 state042 = absorbed042 := by
  decide +kernel

private def quarter042_1 : Vector UInt64 25 :=
  #v[0x5c887ff89bad3d03, 0x52a7fdf91b97e8bd, 0x486629aac5bdd83a, 0xdf0ba5643d4c4adc, 0x4f5e9ff064746fb5, 0xa4936a35b9d72490, 0x93218efefaeea5e9, 0x3ae146bb98a1bc49, 0xea04e23ee754b97c, 0x8ab0a36ddfec6f0, 0xcb5288cadfd254ab, 0xc9f43f1a95e4a28b, 0xa0cffefb1fd8e298, 0x6c8f743f3ebd2af, 0x4919939280c244b8, 0x4c7e5b5075f4523a, 0x9eeb07209738f678, 0x174a8b015d74369c, 0x66d7659dc313454d, 0x6d0d41d68abd584d, 0x4b7a046addc5ed9, 0x3bec2dfad1ebb85b, 0x466db31b757a1ead, 0x3188a9d55cb60baf, 0x9e3afd7340295886]

private theorem rounds042_0 : sixRounds 0 (by decide) absorbed042 = quarter042_1 := by
  decide +kernel

private def quarter042_2 : Vector UInt64 25 :=
  #v[0x7622944e4e4961aa, 0xcc00b4b8863cb614, 0x7652dfc0c8c4b394, 0xe207e3690d3b2c7a, 0xfe52bf92697edaa0, 0xe970e4a723fc4abc, 0x40957552f978e785, 0x789afc21835015ed, 0xdb3088bdea22102b, 0x6c59d7f256fcda1e, 0x90246640dcf926e0, 0xc1da9688b6221836, 0xceb8d3b0569f648f, 0xba95aa22d602bc25, 0x28aa53f9931132ce, 0xe5814c65ce7cc808, 0x473dcf46ae11c2ad, 0xa93df1f67ba4797f, 0x435c7c5ab8692c49, 0x472b2487cd899124, 0xd51e7695b5711bf, 0xa481fece1d8cd8aa, 0xae6db786dfc80749, 0x6dc1dcd3eb645b73, 0xe31ee056631febbb]

private theorem rounds042_1 : sixRounds 6 (by decide) quarter042_1 = quarter042_2 := by
  decide +kernel

private def quarter042_3 : Vector UInt64 25 :=
  #v[0x4f8de5c33a88a92b, 0x5f55ca11ca838bd6, 0x5326f3d8c6cfbd39, 0xeaae95cd737d4511, 0x70bb729437f891a1, 0x3ee75ca7e15f37c5, 0x7677dadbec85128e, 0xf0b6d7a6ff2062aa, 0xb7f43c7cdb332edf, 0xe7b1d04bc2c4d8bd, 0x3afa7f785dd12421, 0xc29395260281acff, 0x95a8ec3ef1c0a064, 0x98f68e5f0c0bb438, 0xe4ac7465e07324e1, 0xcf7f94c8f600a445, 0xfabb2e41cf619a50, 0xf9f6c5c11bc24380, 0x48e8b213c59e3923, 0x63e1b81903d2d4ae, 0x8ff370c21bfa27e9, 0x7fdc49a890fabd31, 0xad79ec2a004d07d1, 0xad601e884f372e61, 0x6ef1d3e4d996efb4]

private theorem rounds042_2 : sixRounds 12 (by decide) quarter042_2 = quarter042_3 := by
  decide +kernel

private theorem rounds042_3 : sixRounds 18 (by decide) quarter042_3 = state043 := by
  decide +kernel

private theorem perm042 : KECCAK.f1600 absorbed042 = state043 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds042_0, rounds042_1, rounds042_2, rounds042_3]
  rfl

theorem block042 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes042 ++ tail) state042 =
      KECCAK.Bytes.run 0 tail state043 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes042 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb042 ws)) := by
    rfl
  exact (step state042).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words042).trans perm042))

private def absorb043 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x90)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x33 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x57 0xcb 0x16 0x61 0x14)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8 0x7f)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x80 0x80 0x1 0x4 0x60 0x52 0x81 0x0)) 9 (by decide) (UInt64.ofBytes 0x52 0x82 0x3 0x81 0x82 0x1 0x20 0x60)) 10 (by decide) (UInt64.ofBytes 0x80 0x1 0x20 0x60 0x52 0x81 0x29 0x60)) 11 (by decide) (UInt64.ofBytes 0x60 0x39 0x91 0x29 0x60 0xb9 0x56 0x61)) 12 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x50 0x50 0x91 0x1 0x40)) 13 (by decide) (UInt64.ofBytes 0xff 0x73 0x5b 0xfd 0x90 0x3 0x91 0x80)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x81 0x0 0x60 0x16 0x82 0xff 0xff 0xff))

private def absorbed043 : Vector UInt64 25 :=
  #v[0x98d4e70b28cff8f9, 0x79ab9c2495c37ee3, 0x76c597443d4f100d, 0x5d9bb6dc50d58744, 0xe46d54b918c2dd48, 0x967e0bba7745d66c, 0xf8166eeca965be34, 0x569d1fa7d57a9fb2, 0x829e8a24cac74fff, 0xfbb8f0dfd714fb73, 0xec66f3c65bea77e1, 0xf40561af1352b903, 0xc3985d727bb958c7, 0x63baa02927d7092c, 0x298304b526f8499f, 0x8c46c18f99460e5b, 0xafb79369ea3fa502, 0xe5fff1482edf405b, 0x1bf3b192695231c0, 0x5cbbee2f5933d417, 0xcbdbced39d7f3b97, 0x20e903c48e95cf2f, 0x8ccb34a4bb001472, 0x38d33a873d99a932, 0xa74b6e0f740899cb]

private theorem words043 : absorb043 state043 = absorbed043 := by
  decide +kernel

private def quarter043_1 : Vector UInt64 25 :=
  #v[0xa845a5045c8d71d4, 0x8c46ca02479a9ab6, 0xef8fcb0522181382, 0x3e43e5a819acae0f, 0xec14cef409079ab5, 0xffdd879effe650d2, 0x90099b48322ce35f, 0x23d36b1a17c3e380, 0x19b5aa07b61cc60e, 0x7dff4b74bf22381c, 0xe0a0a92a0f4259f2, 0xf04db6057430c3cd, 0x2cf1f6c39b61dda5, 0x188bdf5b49f3e86e, 0x85516dc85e0a6085, 0xad2d6a10e6dc679, 0x74b2d9874fea1a99, 0xe6bda3b722c5e0ca, 0x3eacce6fe673f106, 0xb059ae3e4a8e8c, 0x175769140c8f9ce9, 0x765cd8320b469dea, 0x4c06637fe51798e7, 0x82b93519451ec2b1, 0xed5be069aa208798]

private theorem rounds043_0 : sixRounds 0 (by decide) absorbed043 = quarter043_1 := by
  decide +kernel

private def quarter043_2 : Vector UInt64 25 :=
  #v[0x5caa69a75231fab0, 0xaa00b443042f27ad, 0x11a0e4a6cc880037, 0x8684f032c0e9eb9e, 0x66c568bc2235e2de, 0xf4da864cff3dfc11, 0x4b08b7c066eb2e8b, 0x783d6edc05ad303d, 0x5e85cc39100ed654, 0x2b2da68ae037eca3, 0xce775289c7dd3d73, 0x8a495427aff5228, 0x6eb1deed72d6bcd4, 0x33d5ab6b1bffeaa4, 0x9c439391a01f3b0f, 0x4150b9a6a7d6de4f, 0x7ac3e02a62cb859a, 0xcad607461149a6cf, 0x47adede5a56549c, 0x1d596add8bdb65c8, 0x4fe7081e7eb09ede, 0xed866e8348021124, 0x2b9b70a17bb48148, 0x20c56251a91d2cb6, 0xf4c035d8960492e0]

private theorem rounds043_1 : sixRounds 6 (by decide) quarter043_1 = quarter043_2 := by
  decide +kernel

private def quarter043_3 : Vector UInt64 25 :=
  #v[0x387f761147e8c1f5, 0x2930574dd9c7d337, 0x77392df8e27563a3, 0xdf767f86c99781ba, 0x82a71731c0be225, 0x41ee159c2dd98828, 0xb10d8d4a23f86cd9, 0xf6499d3b20d9c74c, 0x956c45159ffaac72, 0x5735c8a7a590a6e, 0x3a6ac888de2aabe3, 0x175f618439c25443, 0xd02b807bc02540da, 0x58061822be6ab311, 0x5f98deabb40d8e07, 0x39a1db5ad54c660c, 0x4dc9e359d34a1bcd, 0x5c1ede545dfad1a1, 0x2ae99a86ab2af792, 0xe451926de71082dc, 0x90a2dc83c2226a36, 0x8df5f58fa2aafdc2, 0x8585362ecfee464, 0x5fd518a3f4a3c212, 0x7ff97bf26a9e75ca]

private theorem rounds043_2 : sixRounds 12 (by decide) quarter043_2 = quarter043_3 := by
  decide +kernel

private theorem rounds043_3 : sixRounds 18 (by decide) quarter043_3 = state044 := by
  decide +kernel

private theorem perm043 : KECCAK.f1600 absorbed043 = state044 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds043_0, rounds043_1, rounds043_2, rounds043_3]
  rfl

theorem block043 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes043 ++ tail) state043 =
      KECCAK.Bytes.run 0 tail state044 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes043 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb043 ws)) := by
    rfl
  exact (step state043).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words043).trans perm043))

private def absorb044 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x81 0x90 0x20 0x60 0xc 0x60 0x52 0x81)) 1 (by decide) (UInt64.ofBytes 0x54 0x80 0x20 0x83 0x80 0x40 0x60 0x52)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x7f)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x91 0x90 0xd 0x60 0x55 0x90 0x16 0x0)) 7 (by decide) (UInt64.ofBytes 0x51 0x55 0x90 0x82 0x20 0x82 0x80 0x52)) 8 (by decide) (UInt64.ofBytes 0x95 0xe1 0xf7 0xa9 0x79 0x44 0xe9 0x7f)) 9 (by decide) (UInt64.ofBytes 0x78 0xb6 0xaa 0x6b 0x2d 0x8f 0xc7 0x2c)) 10 (by decide) (UInt64.ofBytes 0x58 0xc6 0x36 0xd9 0x72 0xb7 0xc1 0xad)) 11 (by decide) (UInt64.ofBytes 0x66 0xb6 0x4c 0x52 0x9e 0x48 0xef 0x3d)) 12 (by decide) (UInt64.ofBytes 0x91 0x1 0x60 0x50 0xa2 0x90 0x91 0x92)) 13 (by decide) (UInt64.ofBytes 0xed 0x71 0x6e 0x7f 0x5b 0x56 0x50 0x90)) 14 (by decide) (UInt64.ofBytes 0x60 0x1f 0x4d 0x7f 0xb9 0xb1 0x12 0xae)) 15 (by decide) (UInt64.ofBytes 0xfa 0xa2 0x5f 0x10 0x10 0xef 0xf 0x37)) 16 (by decide) (UInt64.ofBytes 0x64 0x9c 0x16 0x4a 0x11 0x26 0x1 0xae))

private def absorbed044 : Vector UInt64 25 :=
  #v[0xab87d2fd84bfed4a, 0x660639b7bbd8a04b, 0x5420d047a4c794fa, 0x206255cb65f82190, 0x7c6db3a649a457, 0x5fdfef25e4c760f1, 0xe139a4229ea863e0, 0xf39caf4ef9fb2e40, 0x6fc6bd180eefa07c, 0x3bbddc660dc8e11, 0x1286f9f79379fa75, 0xb0986d4cddaae04e, 0xfb952760ae82c941, 0x3009d90edcdb9f21, 0x7992e8ab7a7c0fbc, 0x452b402ca4acd3c4, 0x2733993aa89e4ba, 0xc5e833b58821dce2, 0xd40449dbdbdd521b, 0x4c15308b48b8e89a, 0x162db6394db47291, 0x1e5a59454daadea, 0xd9f2edacd5be08ac, 0xda3db7719e6963ab, 0xcbae07dac4c9528c]

private theorem words044 : absorb044 state044 = absorbed044 := by
  decide +kernel

private def quarter044_1 : Vector UInt64 25 :=
  #v[0x8b4d57d54b00fad6, 0xb4204fb1eabf642f, 0x197cd1125258a8fe, 0x311d129b6fe15a06, 0x1379f8d574a77e3b, 0xd2aad156a94e792f, 0x870c14ffe8d3dfee, 0xa739a1ae586d172f, 0x5420c6b7d651875e, 0x87f4eaec78f1431a, 0xac60ad5cd6c4bfef, 0x436a2da624beea97, 0x5428348fd39ab2ec, 0xc23e666f6edef2b, 0x598df332582edd49, 0x4f57f82dff1a83ee, 0xa98827d9146c8b86, 0xe64cfd64cd6f1fa7, 0x576a5141bc9eab09, 0x7f0cbdf1718d1673, 0xb18f3e3423b8207d, 0xfd2b0bdacdcdc500, 0xe1249e06ff568e94, 0x606187f633d9322b, 0x895c6ac13aaaece1]

private theorem rounds044_0 : sixRounds 0 (by decide) absorbed044 = quarter044_1 := by
  decide +kernel

private def quarter044_2 : Vector UInt64 25 :=
  #v[0x7302e411b8487752, 0x113c25f08c174d2c, 0xf7e49dde61cb8e2c, 0xb86591c25bb17006, 0x9df539f4ca6d5b4f, 0xfec0bf6b90ec4c67, 0xa6bd012475872d52, 0x325d184ee3b0c15f, 0x330ece52798e1235, 0xc3a463bb7b4547a6, 0xd947f644de5ea342, 0x86bf3d8aec02f2b9, 0xb0e0cebaa0d42794, 0xf9fcc2d15c9d80ac, 0xa0cb2b843562d503, 0x3cc0c58b107edbd4, 0xd6ae0ce7392eabea, 0x90779d047a25ef2c, 0x1ef1a8bbe1df0bf4, 0x5bb96bcaa8027eaa, 0x374f4fbe493a82be, 0x55209e3f1c7637ff, 0x7d2a268f1209c406, 0x4569928085cc8f62, 0x3fa7990236154c19]

private theorem rounds044_1 : sixRounds 6 (by decide) quarter044_1 = quarter044_2 := by
  decide +kernel

private def quarter044_3 : Vector UInt64 25 :=
  #v[0x44180beb4556ef29, 0xad4b592f64697728, 0x1b4604062438a5e, 0xf8b88c70affb918b, 0x381e156b04b38b4b, 0xa4c275bbc595a295, 0x3c30bf443884670e, 0xb6a3775991bf4b69, 0x9050cf6541b458f2, 0x1c3d7cbc6a8f1fde, 0x53313968f472cd65, 0xa42a70b24ffaf645, 0x9a6e2cc100b10b59, 0x69e943a896ceef62, 0x1ef7f82c9979ee07, 0xdb25941512b709a5, 0xad90270c5a3d27f, 0x7dc77e139d95df87, 0x37dd5d701d92c41, 0x26048a21531af6e2, 0x3e880cb64c66201a, 0x920f807050c934dc, 0xbbd8d57d98a7f60d, 0x584ef971061545f3, 0xd697770b6ced86df]

private theorem rounds044_2 : sixRounds 12 (by decide) quarter044_2 = quarter044_3 := by
  decide +kernel

private theorem rounds044_3 : sixRounds 18 (by decide) quarter044_3 = state045 := by
  decide +kernel

private theorem perm044 : KECCAK.f1600 absorbed044 = state045 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds044_0, rounds044_1, rounds044_2, rounds044_3]
  rfl

theorem block044 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes044 ++ tail) state044 =
      KECCAK.Bytes.run 0 tail state045 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes044 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb044 ws)) := by
    rfl
  exact (step state044).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words044).trans perm044))

private def absorb045 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x5b 0x56 0x81 0xc9 0x26 0x61 0x5d 0x84)) 1 (by decide) (UInt64.ofBytes 0x56 0x81 0x16 0xff 0x60 0x54 0x6 0x60)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x1 0x74 0x54 0x8 0x60 0x5b)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x15 0x16 0xff 0x60 0x4 0x90 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x7f 0x51 0x40 0x60 0x57 0xf2 0x17 0x61)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x60 0x80 0x80 0x1 0x4 0x60 0x52 0x81)) 12 (by decide) (UInt64.ofBytes 0x60 0x52 0x82 0x3 0x81 0x82 0x1 0x20)) 13 (by decide) (UInt64.ofBytes 0x61 0x80 0x1 0x20 0x60 0x52 0x81 0x2a)) 14 (by decide) (UInt64.ofBytes 0x40 0x60 0x39 0x91 0x2a 0x60 0xfe 0x57)) 15 (by decide) (UInt64.ofBytes 0x80 0x51 0x40 0x60 0x50 0x50 0x91 0x1)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x5b 0xfd 0x90 0x3 0x91))

private def absorbed045 : Vector UInt64 25 :=
  #v[0xb336a330edf60d65, 0x5ac02d3b9486defb, 0x2f4c2e79e4265c2b, 0xce368dc96cc2f9ee, 0x630167c4f7cb8c4d, 0x34d0078bdde6b563, 0x432ef6b5232fdf79, 0xa5c3bd3256a8fc46, 0x6ebeb38d4deecfd1, 0x1adc54d6a12eab0c, 0xe0cecdd4c38c7433, 0xf81f3c60df77a323, 0xf74c0db717feef37, 0x1d1a2c45ef54683a, 0x5e9cc7e133080c9b, 0xf7d86e4d7d8259b9, 0xe83303eb72d372a5, 0xebbc883749a64b86, 0x446f75b2ca87e2a, 0x661e8ce8bd007405, 0x4ad697b4d9cf0ec1, 0x8147478196735b74, 0x95b57ff6f043b63a, 0x99443638b920dacf, 0x4c72a54d0020f637]

private theorem words045 : absorb045 state045 = absorbed045 := by
  decide +kernel

private def quarter045_1 : Vector UInt64 25 :=
  #v[0xafe39eedafd00ad, 0x4bacc69188358fc, 0xfc1ee8b082beae70, 0xae56e8bf316df74d, 0x105fd2f555ce3e17, 0x606bb7b85aba2692, 0xdc1b80c3ee685b4a, 0x510a4ee98d1b8a, 0xe9c858c9d299849c, 0x8ec40c5faea70489, 0x64b063f2b9092a90, 0xa0be73ea5d54cb9f, 0xc90538f480610ada, 0xbafeaf9b893f0837, 0x9cb3502f10ec6bdb, 0xac87eb358e23ad0d, 0x75a366f6df5468f0, 0x523acfe640fb34e7, 0xc218d1c5bca3d5a7, 0x1f1fed9973ab4989, 0xc3623f2fb4191ae, 0xc3e6b4334d9e86e1, 0xd901b6d43553d688, 0x4743218865c4509c, 0x7f065ed5ae6ece10]

private theorem rounds045_0 : sixRounds 0 (by decide) absorbed045 = quarter045_1 := by
  decide +kernel

private def quarter045_2 : Vector UInt64 25 :=
  #v[0xa0c3ff50205ec853, 0x7930c5a377d9478, 0x70b141fe6aa5b730, 0xef56f9fb9d04fe66, 0xed42211e50a2b13c, 0xa1beeb2f134cfcc8, 0x72ecdf53969bc74c, 0x1ff7e1958d699aa2, 0x7f8790d50aa78b3b, 0x4c6d7d0ae452c835, 0x9d287ceb1cc72088, 0x2c830b7a1ff69ca7, 0xe7381702eb770982, 0xc37be7a64eea3dc0, 0x2ee2d9559d818a62, 0xbaba8309b3d3c9ed, 0x7478269f9bcda2cd, 0xda60a91a747e6e79, 0x8584964307c17b28, 0x38b5d6767a8d5c84, 0xc70e8630ba171670, 0x536397d49c1a050a, 0x7bb91b270d82823b, 0x92239fed0e94645e, 0x644a584e7c8b81d9]

private theorem rounds045_1 : sixRounds 6 (by decide) quarter045_1 = quarter045_2 := by
  decide +kernel

private def quarter045_3 : Vector UInt64 25 :=
  #v[0xb67c1c58564c3ac5, 0x8d328da223caf249, 0xfe4a1bab332727b0, 0xaed1f06f42713d5c, 0xa43c9b6f8da99eaa, 0xa7a54b7b30a0f1c1, 0x94b10e025f521da0, 0xa4c9dc85e43fd86, 0x777d33f17c251b57, 0x86694ac1e7c5ed95, 0x2fa0319602272d54, 0x4eac98ea78edc9df, 0xf750035828dea879, 0x342c76614bb86ef6, 0xa258f9e77d2999b9, 0x22ceebc64c5adc46, 0x73e3060082172756, 0x746300a036e8cb56, 0xf588d39e408c6ab5, 0x5d1294aaa2b965ec, 0x86259d7941f7bd2, 0xcefb860d78175759, 0x1c8df76be4fcb57e, 0x87880d1a5ba10f49, 0x921515403472757a]

private theorem rounds045_2 : sixRounds 12 (by decide) quarter045_2 = quarter045_3 := by
  decide +kernel

private theorem rounds045_3 : sixRounds 18 (by decide) quarter045_3 = state046 := by
  decide +kernel

private theorem perm045 : KECCAK.f1600 absorbed045 = state046 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds045_0, rounds045_1, rounds045_2, rounds045_3]
  rfl

theorem block045 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes045 ++ tail) state045 =
      KECCAK.Bytes.run 0 tail state046 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes045 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb045 ws)) := by
    rfl
  exact (step state045).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words045).trans perm045))

private def absorb046 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x57 0x5e 0x18 0x61 0x16 0x84 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x40 0x60)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x4 0x60 0x52 0x81 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x81 0x82 0x1 0x20 0x60 0x80 0x80 0x1)) 9 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x2f 0x60 0x52 0x82 0x3)) 10 (by decide) (UInt64.ofBytes 0x2f 0x60 0x55 0x57 0x61 0x80 0x1 0x20)) 11 (by decide) (UInt64.ofBytes 0x50 0x50 0x91 0x1 0x40 0x60 0x39 0x91)) 12 (by decide) (UInt64.ofBytes 0xfd 0x90 0x3 0x91 0x80 0x51 0x40 0x60)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x5b)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x16 0x83 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x7f 0x51 0x40 0x60 0x57 0xca 0x18 0x61))

private def absorbed046 : Vector UInt64 25 :=
  #v[0x38c66daf409c5488, 0xb74dc22313418aa2, 0x724d4beba4676502, 0xc1177975d1921ca4, 0xddb56d10c6d41f45, 0x7930ea45ac51091c, 0x122e334cc6f487d0, 0x2e2d56e3fd63a1c9, 0x33123cad0ad8af18, 0x4fdd5062f8340522, 0x65c4132673965295, 0xefb47918e28f8307, 0x9bf2daf8d88a52b, 0xdcd3ccc6524b780, 0x1a2ac8d7bb1eb7b3, 0x6d0954786ba1883c, 0xbe4c77bbc0e80b68, 0x973678d4f18813fb, 0x15ab9465622bd1f5, 0xe3b2e242b16b9335, 0xc71696a63f3ef177, 0xf2214e4589ac961e, 0xe496c6037a4f4a4c, 0x39515f34f5ea8cf5, 0x735b32c6bbdd8c1e]

private theorem words046 : absorb046 state046 = absorbed046 := by
  decide +kernel

private def quarter046_1 : Vector UInt64 25 :=
  #v[0xd5442f955ea0dffa, 0x4a43ad305048400b, 0x1576f0b9c397346e, 0x77895eba5bbff6db, 0xd79658205f8dbc42, 0x75054a669b90cd0a, 0x246ed4bd5fda2a71, 0xc30182f0f12c80d8, 0x8d72a448b1257df, 0xe462c2a9a7bc5203, 0x45f78ee4cdef4ebd, 0x2f9f714e56017258, 0xb8b32d85b391fe79, 0xfdc05b26a36c88d9, 0xf77cc3ccc0b3f202, 0x6cbaba3b434f29d3, 0xa0a3a722928d85c8, 0x47e599275a1ffb22, 0xb2c9fe8a1bb98e39, 0xe1c498daceb34f0, 0x46d2b107575e1b82, 0xb0e7dad416494a2b, 0x5c271b12882857ef, 0xa1a71e1e805078aa, 0x182b6c2438c8ab3]

private theorem rounds046_0 : sixRounds 0 (by decide) absorbed046 = quarter046_1 := by
  decide +kernel

private def quarter046_2 : Vector UInt64 25 :=
  #v[0xd4178d742aecce26, 0xae51ed3f6344cfa6, 0x1e4c91f402da2052, 0x74c73e4112eb6690, 0xd3056b22ecf991fa, 0x963ebaa2371743fd, 0x7243019223a65c71, 0x80f47fc95de90a29, 0xfcb03d61e8226085, 0xdc6ae71e81de23c2, 0xcae3409863e2d899, 0x33736236707a38d8, 0x220777dcc6d76f1c, 0xf484deb348bd74b4, 0x7533519eda5407a0, 0x4ed710fa49387ef8, 0xb9e6d738c7b78275, 0xd005573084f1331c, 0xb075981b9666d7f2, 0x9ac4d8341223b191, 0xa2d6b865b786c8de, 0xf0da12b288c42b76, 0x2760bed69a21f595, 0x17b5a5f8ebbe3ae4, 0x85da91a87f33db2]

private theorem rounds046_1 : sixRounds 6 (by decide) quarter046_1 = quarter046_2 := by
  decide +kernel

private def quarter046_3 : Vector UInt64 25 :=
  #v[0xb43dee14795a5521, 0x2c987f328ec3f7a3, 0xada5f3c0f7a6a001, 0x47cc0560b15ffde5, 0x21d48ee0ab8e84d7, 0xce26a796d22991a9, 0xa83a2e7544c86f7d, 0xb375165a87a309d9, 0xf18a8d0f31eba4c, 0x109ca5f0a0ff7b7a, 0x8529dbdfb09b4a1a, 0x9cc1fa46d4fd4802, 0xa9424313c2e62fde, 0xd5761ce255e93695, 0xab9b0f5fef46db04, 0xe8fccdf1dd3bbb4b, 0x6d745e65b6320d88, 0xd01bf273a9937fb8, 0xe6ca2a131d3895e, 0xbb9f2307800e570, 0xbe1aba54f6fe5ebf, 0x70705c00e5e67415, 0x459a8065cc507a2b, 0xf1d7a8681d13695, 0x614d5dd13578bbd8]

private theorem rounds046_2 : sixRounds 12 (by decide) quarter046_2 = quarter046_3 := by
  decide +kernel

private theorem rounds046_3 : sixRounds 18 (by decide) quarter046_3 = state047 := by
  decide +kernel

private theorem perm046 : KECCAK.f1600 absorbed046 = state047 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds046_0, rounds046_1, rounds046_2, rounds046_3]
  rfl

theorem block046 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes046 ++ tail) state046 =
      KECCAK.Bytes.run 0 tail state047 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes046 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb046 ws)) := by
    rfl
  exact (step state046).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words046).trans perm046))

private def absorb047 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x60 0x80 0x80 0x1 0x4 0x60 0x52 0x81)) 5 (by decide) (UInt64.ofBytes 0x60 0x52 0x82 0x3 0x81 0x82 0x1 0x20)) 6 (by decide) (UInt64.ofBytes 0x61 0x80 0x1 0x20 0x60 0x52 0x81 0x29)) 7 (by decide) (UInt64.ofBytes 0x40 0x60 0x39 0x91 0x29 0x60 0x17 0x56)) 8 (by decide) (UInt64.ofBytes 0x80 0x51 0x40 0x60 0x50 0x50 0x91 0x1)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x5b 0xfd 0x90 0x3 0x91)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x57 0x36 0x19 0x61 0x16 0x82 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x40 0x60)) 14 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0))

private def absorbed047 : Vector UInt64 25 :=
  #v[0x6920460ac9079c92, 0x44e15a424fddb0b1, 0x23b48e196176470e, 0x913a96bebeb0ebae, 0x4de75fb0d037a403, 0x595b35da4fbf7ddd, 0x9b95d56499e0e55d, 0x552ea596676ddee5, 0xc7ae9dfc5f09b70c, 0xb1dbd97826e0a3d8, 0x1f299360329f0018, 0x409cc644ebc27f16, 0x4156383c4a4d394, 0x63e9f46931799d3f, 0xa1c6c89b0d56a2dd, 0x460ac5e3b70941cf, 0x5fc4098df0cb01c3, 0x41bc2543c16f60c9, 0xfc011c24b269e0fa, 0xd4bfee65deef665c, 0xa22164d39d8ec537, 0x7e02c2f626db72c1, 0x44e9c8878406cd8a, 0xa67e2b5d03cb257a, 0xd163c04fba484d95]

private theorem words047 : absorb047 state047 = absorbed047 := by
  decide +kernel

private def quarter047_1 : Vector UInt64 25 :=
  #v[0xabdd5178301c1ed0, 0x5ca04d9d8329a663, 0xf759964ae1fce89f, 0x9dd937148a66d7ed, 0x4d6871046aed8999, 0x5e00625994da459f, 0x8a1e680a4f5bb1c6, 0xac211bf019d75ccb, 0xb0c7e1bc6d406f1, 0x64d6fd37994f2351, 0xf107c4302911bea1, 0x8a91ad602235f5a7, 0x1c93d75286b1edfa, 0x207319109f1d347f, 0x806464d03549aa5b, 0xfcce12261eae11ac, 0xfa7df03664fee1c8, 0x5e236c3e50ccb318, 0xa40b824a2865295b, 0x934f15e6cda16b9c, 0x99c6e43fd9f469fd, 0x4d350604c5b8e2fb, 0x3fd20f3b9315dee3, 0x355fc110453b6e3e, 0xbe2925a6561d4e46]

private theorem rounds047_0 : sixRounds 0 (by decide) absorbed047 = quarter047_1 := by
  decide +kernel

private def quarter047_2 : Vector UInt64 25 :=
  #v[0x6acd149c328f2abb, 0x9471bfc6aafbf016, 0xfc0b9464259bfb5f, 0xff3c2331f60c1dea, 0x1a39ce921b6a9a97, 0xaa5a56ce9b79dd37, 0x97ab8c44d4a52cd3, 0xb8932f1d847a9c24, 0x9d0b2f77786a7b85, 0x5916140e01257a86, 0xa723dd6ebb10cf0, 0xa1a3d80236fad4c3, 0x6ec19e3d976e0a79, 0x18afddb1784b816f, 0x7ce700edd838f1da, 0xdf5c9011058d57a8, 0x7c4ec71ef2c37905, 0x4f650a3791d5ad92, 0xaaf7d34c4a00902c, 0x175cc36e050185c9, 0xedcedca0ced78f3b, 0x26f2da8b17d5ca47, 0xaffaa19abe1a8c4a, 0x21c7a5c8c92b55b0, 0xcb13ff0623bb64f4]

private theorem rounds047_1 : sixRounds 6 (by decide) quarter047_1 = quarter047_2 := by
  decide +kernel

private def quarter047_3 : Vector UInt64 25 :=
  #v[0xe55c7cccfa670c1d, 0x9b80d51dd484ed2e, 0xae3fc1970cbdd726, 0x4217de7c6be76ad4, 0xf69e5a1b115f374d, 0xe00d195f78f2b45a, 0x808946b1ac414f70, 0xbe2c0379430feff3, 0xecb4f9a079938eee, 0xfc415227a0183ca1, 0x6886a29e01a98896, 0x84e1cce5ee9caaa3, 0xccf3ff73cb55a3ec, 0xc089ddd5358ca0f9, 0x9f93791d0d905fe1, 0x1cab599eea1d5f53, 0x71ef4f640f966167, 0xec91ccbbfb948ff0, 0xa866cfd9b65b4b34, 0x80c41304285861e8, 0x992168f6c36b7764, 0x4cf32a05d22077fb, 0x14dd8ae3102da47e, 0x502f30ff0c797fae, 0xb0945d0994d92293]

private theorem rounds047_2 : sixRounds 12 (by decide) quarter047_2 = quarter047_3 := by
  decide +kernel

private theorem rounds047_3 : sixRounds 18 (by decide) quarter047_3 = state048 := by
  decide +kernel

private theorem perm047 : KECCAK.f1600 absorbed047 = state048 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds047_0, rounds047_1, rounds047_2, rounds047_3]
  rfl

theorem block047 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes047 ++ tail) state047 =
      KECCAK.Bytes.run 0 tail state048 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes047 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb047 ws)) := by
    rfl
  exact (step state047).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words047).trans perm047))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
