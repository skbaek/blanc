import Blanc.CommonCore

/-!
# USDC addresses and the proxy's unstructured slots (C0 §1.2, §4.1)

The exhibit proxy, the FiatTokenV2_2 implementation it names at block 26,213,219, the linked
`SignatureChecker` library, and the two ZeppelinOS "unstructured" proxy slots.  `adminOf` reads the
proxy's admin word at a state.  The code inputs and certified semantics are U3's
(`Blanc/Lift/Usdc/{Proxy,Impl,Lib}/`).
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc

/-- The FiatTokenV2_2 implementation the proxy names at block 26,213,219 (C0 §1.2). -/
def usdcImpl : Adr := 0x43506849D7C04F9138D1A2050bbF3A0c054402dd
/-- The linked `SignatureChecker` library (`PUSH20` in the implementation). -/
def usdcLib : Adr := 0x800C32EaA2a6c93cF4CB51794450ED77fBfbB172
/-- The exhibit proxy address. -/
def usdcProxy : Adr := 0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48
/-- keccak256("org.zeppelinos.proxy.implementation"). -/
def implSlot : B256 := 0x7050c9e0f4ca769c69bd3a8ef740bc37934f8e2c036e5a723fd8ee048ed3f8c3
/-- keccak256("org.zeppelinos.proxy.admin"). -/
def adminSlot : B256 := 0x10d6a54a4754c8869d6886b5f5d7fbfa5b4522237ea5c60d11bc4e7a1ff9390b

/-- The admin word of the proxy at a state. -/
def adminOf (w : State) (P : Adr) : Adr := ((w.getStor P).get adminSlot).toAdr

end Blanc.Lift.Usdc
