import Blanc.Lift.Usdc.LibCreation.SigningBytes
import Blanc.Lift.Usdc.LibCreation.SigningStates

/-! Unadopted bounded kernel proofs against the production Keccak permutation. -/
namespace Blanc.Lift.Usdc.LibCreation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb012 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x6f 0x63 0x65 0x52 0x43 0x45 0xfe 0x56)) 1 (by decide) (UInt64.ofBytes 0x76 0x6e 0x69 0x20 0x3a 0x72 0x65 0x76)) 2 (by decide) (UInt64.ofBytes 0x67 0x69 0x73 0x20 0x64 0x69 0x6c 0x61)) 3 (by decide) (UInt64.ofBytes 0x6c 0x20 0x65 0x72 0x75 0x74 0x61 0x6e)) 4 (by decide) (UInt64.ofBytes 0x52 0x43 0x45 0x68 0x74 0x67 0x6e 0x65)) 5 (by decide) (UInt64.ofBytes 0x20 0x3a 0x72 0x65 0x76 0x6f 0x63 0x65)) 6 (by decide) (UInt64.ofBytes 0x20 0x64 0x69 0x6c 0x61 0x76 0x6e 0x69)) 7 (by decide) (UInt64.ofBytes 0x72 0x75 0x74 0x61 0x6e 0x67 0x69 0x73)) 8 (by decide) (UInt64.ofBytes 0x61 0x76 0x20 0x27 0x76 0x27 0x20 0x65)) 9 (by decide) (UInt64.ofBytes 0x63 0x65 0x52 0x43 0x45 0x65 0x75 0x6c)) 10 (by decide) (UInt64.ofBytes 0x6e 0x69 0x20 0x3a 0x72 0x65 0x76 0x6f)) 11 (by decide) (UInt64.ofBytes 0x69 0x73 0x20 0x64 0x69 0x6c 0x61 0x76)) 12 (by decide) (UInt64.ofBytes 0x20 0x65 0x72 0x75 0x74 0x61 0x6e 0x67)) 13 (by decide) (UInt64.ofBytes 0x75 0x6c 0x61 0x76 0x20 0x27 0x73 0x27)) 14 (by decide) (UInt64.ofBytes 0x58 0x73 0x66 0x70 0x69 0x64 0xa2 0x65)) 15 (by decide) (UInt64.ofBytes 0x8f 0x6c 0xf7 0xb3 0x88 0x20 0x12 0x22)) 16 (by decide) (UInt64.ofBytes 0x32 0xdd 0x5d 0xd0 0x13 0x81 0x93 0x3f))

private def absorbed012 : Vector UInt64 25 :=
  #v[0xfe46f59164e9be3d, 0xac7f25937d65010f, 0x322602ba65bd23b0, 0xbfc5c1fd9ae233c7, 0xaba5acd4b6d35c78, 0xa280edc294ad1516, 0xc54c780469b9ef7, 0xd35cb6713e6a93f7, 0xdda368acbfd810e1, 0x20e3a53c5b81a0c7, 0xb094c9d30a1c3e7, 0x19739104f1194f9b, 0xa74653f49dfb3f76, 0x79e1828ef3231b12, 0x9335c6cd896e7b20, 0xe3a1fd4057b4f315, 0xea4fc67ddb0bf7bb, 0x6b12bfca9044e316, 0x3a680e3ff4c9e0cf, 0x5fbdad4928364a8, 0x58483804c2e0fd08, 0xff1a4648a514700c, 0x20260a6d73a1e2be, 0x7da680dbe526365b, 0xb954003199ef9d77]

private theorem words012 : absorb012 state012 = absorbed012 := by
  decide +kernel

private def quarter012_1 : Vector UInt64 25 :=
  #v[0x58abf42d604b560a, 0x6878b7e8f6b15925, 0x49251b984b7b6637, 0xeb156882470a4613, 0xbad3a4629782c39d, 0x3c9552e87f75a2a3, 0x178b2be1c660e94, 0x251b791134eb46e8, 0xd53684e30f8a06d4, 0xc9b2b06cb152696c, 0xf8bb944babd8ac25, 0xe08e2b301d4beecc, 0x19f22eabb7695241, 0xbbaee66f01b9f2f3, 0x9ba4b16cc2196082, 0x971aee6fe7f56532, 0x2981b0c2a9fbb9ba, 0x2245c7d40c5eb933, 0x4bd9aaa6249f2d74, 0x3b586fe7dfc23752, 0x46417ef501a04911, 0xb013f295fe356c6c, 0x12e16b1b4a5b39ce, 0xeb080000c2b9b4f1, 0x2b0f710950d421ea]

private theorem rounds012_0 : sixRounds 0 (by decide) absorbed012 = quarter012_1 := by
  decide +kernel

private def quarter012_2 : Vector UInt64 25 :=
  #v[0x1066a04286ef4cce, 0xdc0509a901c3a7cc, 0xd4962906e813fef4, 0x75a2d73d8e97a831, 0x852a0f79571659a3, 0x7db681550445ed61, 0xf8060b7d269ee30e, 0x436855523b66089, 0xdb2efcdac9cd7cfc, 0x90233cab8925a9ae, 0x4764f8a8bbfd782, 0xcb8220c65d7c1034, 0x900753e32c42a241, 0x2da9d82ea4af8328, 0xfbbca62220f995d8, 0x6aa67669cdf313f, 0xbee2ce875ed1f89f, 0x945fc5173accd270, 0x2069754019fb0cb9, 0x6e7dad89bb3f6307, 0x990d89a095431755, 0x5a312bb4d7c3ff21, 0x44daaa2ad77eca25, 0x5afdfe6e1e01ab70, 0x913f32b4652f6d50]

private theorem rounds012_1 : sixRounds 6 (by decide) quarter012_1 = quarter012_2 := by
  decide +kernel

private def quarter012_3 : Vector UInt64 25 :=
  #v[0xcdf1844b61299b6c, 0xde31a3e454d7659c, 0x147bfa95dd60b276, 0x3eb7435c1bf8c176, 0xfe7f4d4aab692d7c, 0xf4b90dcf740398da, 0xb64ffcfa682ae7fd, 0x581b01ffdd4da868, 0x3e14860f8c415cf6, 0x22ec86c689c62987, 0x2f573d51a4d5fc86, 0x908b7e547275e211, 0xd107082c8bcc156a, 0x44b31dab82695f7a, 0x4e524b62e83a7e32, 0x753004416818b075, 0x461d32fa467c590b, 0xcba0c33a4789a6df, 0x21264af98167fb91, 0x3a5ee82cc14195b1, 0xda8ced40eb748004, 0xff59a44b4c48f0b2, 0x2ecad37c461407c2, 0xc5bcbb475ea95204, 0x9648a0ab6de02c20]

private theorem rounds012_2 : sixRounds 12 (by decide) quarter012_2 = quarter012_3 := by
  decide +kernel

private theorem rounds012_3 : sixRounds 18 (by decide) quarter012_3 = state013 := by
  decide +kernel

private theorem perm012 : KECCAK.f1600 absorbed012 = state013 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds012_0, rounds012_1, rounds012_2, rounds012_3]
  rfl

private def absorb013 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x8 0x8a 0x6d 0x16 0x6e 0x20 0xb0 0xd)) 1 (by decide) (UInt64.ofBytes 0x67 0x98 0x52 0x5b 0x96 0xa7 0x48 0xf6)) 2 (by decide) (UInt64.ofBytes 0x63 0x6c 0x6f 0x73 0x64 0x2d 0x48 0xe5)) 3 (by decide) (UInt64.ofBytes 0x80 0x1 0x33 0x0 0xc 0x6 0x0 0x43)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x1 0x80)) 16 (by decide) ((8 : UInt64) <<< 60))

private def absorbed013 : Vector UInt64 25 :=
  #v[0x33a6efaf91fe249a, 0x120ae1410fb865ec, 0x2411f867ea59b7f1, 0x3e57fe55a0fa01d2, 0x91cf806c30a87349, 0x20ef88202c081dc6, 0x694d1363e1ef8d31, 0xa72eb34a7c6695d8, 0x75c1bce10334e335, 0x4a0e5b329dfdb692, 0x50a643d4fbebcb64, 0xb27c0f9d580bbb10, 0x916d11cd0586858f, 0x61cab220504e11ab, 0x157d9bd61e4034c5, 0x67b2a466074a88cf, 0x63cdc159803704b9, 0x9d8f3da14b2bdf84, 0xc6716fc6bed93391, 0x9e4f5d52a5577488, 0x52f1c8f16cbdcf99, 0x5b979c17c159ad3, 0xce99b8c05e4698f9, 0x4443e0390023ebad, 0x7cf0349a25bb0cb1]

private theorem words013 : absorb013 state013 = absorbed013 := by
  decide +kernel

private def quarter013_1 : Vector UInt64 25 :=
  #v[0xc8ce9847b376cbf0, 0xa530957d67f5e83e, 0x5ba2064b76ecd7a9, 0x61eb857f43328f76, 0xe24cf3727566d5d0, 0x2684b336e8fa31c9, 0xd6aa06a31e190317, 0x5c3604f2c72fbdc7, 0x7a0b3c802af6f981, 0x3fd3ca4e54c89866, 0x7d98ae1ac7184aa, 0x28b0fc2f77fb495e, 0xc96cfa8d58efea88, 0x872bdb5a24176cfe, 0xb4cc45a5d5a89f66, 0x93f8d6a2f51b13f1, 0x6da4701fde05880d, 0x410a530958feedce, 0x2453458fffd7d5e, 0x558897f9e8ca22e, 0x41994ddce8a15219, 0xc695380848763c8e, 0x4c1e7442b4639b6f, 0xce6b3574e3281e2f, 0xb9b2613b97b9bd56]

private theorem rounds013_0 : sixRounds 0 (by decide) absorbed013 = quarter013_1 := by
  decide +kernel

private def quarter013_2 : Vector UInt64 25 :=
  #v[0x4a87c5d3f3571472, 0x7de406d0375e0d17, 0x67bedf33fc3be8a2, 0x6fb20f28038e674e, 0x61c958069b35c91b, 0x63ee48f5935801d1, 0xf1cd05eddb8f3b60, 0xcab77446a8383164, 0xa305d57d4ec79c07, 0xe22979eabcc0db17, 0x4491c89d503f1d27, 0x32c8e5cc64992c35, 0x7791946746788842, 0x6a4f4fe15d70606c, 0x9310338944945698, 0x3b67c2981f31ca26, 0x767a861f8568d7e0, 0x5ecb9cb6f82cd18f, 0x2685bfa4e87aa84f, 0x94ddd8f0a41780ec, 0x3cc885221fa14045, 0xb92e4b59ece5e9ee, 0xacb84fe766d0ff00, 0x5d95ef9b400418f1, 0x7cde5371e3e3a836]

private theorem rounds013_1 : sixRounds 6 (by decide) quarter013_1 = quarter013_2 := by
  decide +kernel

private def quarter013_3 : Vector UInt64 25 :=
  #v[0x6eb8aac0fdc644be, 0x4a1b5abe372c2e5d, 0x320997926ecefb65, 0x689b9e74b89dd629, 0xa2ce60b3f007d978, 0xc1d5be8a187a701a, 0xb7a369fc653a504, 0xcc8afdd65dd0bd50, 0x1545a8f5c9790c, 0x568463cd008cc9ee, 0x81a15ea3ca48277e, 0x5e22aeec8de952d9, 0x2b4cbab4b9c39636, 0xaa0155d74d0a0bc5, 0xc90b496e31f8af5b, 0x441bbc4c4a0ce4c, 0x48a26e5fd174e7a8, 0x85ffb7d0fe69e4aa, 0xf4cd005638816bb7, 0x36cda309c7c55fb1, 0x765228ebc59dcc53, 0x3d7635e9b0cadba7, 0x2145adea4b87a32c, 0x4e206b0f7c973253, 0xab2eb567e06a117b]

private theorem rounds013_2 : sixRounds 12 (by decide) quarter013_2 = quarter013_3 := by
  decide +kernel

private theorem rounds013_3 : sixRounds 18 (by decide) quarter013_3 = state014 := by
  decide +kernel

private theorem perm013 : KECCAK.f1600 absorbed013 = state014 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds013_0, rounds013_1, rounds013_2, rounds013_3]
  rfl

private theorem finalDigest : squeeze state014 = (0x0b923c20ae300a3a20431bf4781920c212aa03d3894190c1bde5a93411bc8abd : B256) := by
  decide +kernel

theorem finalHash :
    KECCAK.Bytes.run 0 bytes013 state013 = (0x0b923c20ae300a3a20431bf4781920c212aa03d3894190c1bde5a93411bc8abd : B256) := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 bytes013 ws = squeeze (KECCAK.f1600 (absorb013 ws)) := by
    rfl
  exact (step state013).trans ((congrArg squeeze
    ((congrArg KECCAK.f1600 words013).trans perm013)).trans finalDigest)

theorem blocks03 :
    KECCAK.Bytes.run 0 (bytes012 ++ (bytes013)) state012 =
      (0x0b923c20ae300a3a20431bf4781920c212aa03d3894190c1bde5a93411bc8abd : B256) := by
  rw [run_block_of_step bytes012 _ absorb012 state012 absorbed012
    state013 (fun _ => rfl) words012 perm012]
  exact finalHash

end Blanc.Lift.Usdc.LibCreation.SigningBlocks
