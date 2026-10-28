import Blanc.Lift.Weth9.Creation.SigningHash

/-!
# WETH creation sender recovery from explicit signature fields

The conditional APIs separate recovery from the payload hash. The final
field specialization supplies the kernel-proved payload hash. These facts do
not identify an original mainnet transaction or adopt its observed fields.
-/

namespace Blanc.Lift.Weth9.Creation

open Jaune

theorem recoveredSender_of_signingHash {tx : Tx}
    (htype : tx.type = .zero 21000000000 none)
    (hv : tx.v = 37)
    (hr : tx.r.toB256 =
      0x7ce08af79f7a6c1b8b336f50890a80602c4dcd1e3cc5ca131373f0e8ff15e278)
    (hs : tx.s.toB256 =
      0x45e183d91f1e8f31e32d333cf6090990c9bf7d35dd00472cfd2d3a63ca8b1a5)
    (hashed : tx.signingHash = some
      0x1e62afdbf54076edd8083f93eab1bf693f2a5a3675886b669d13d9b3e6221235) :
    recoverSender 1 tx = .ok deployer := by
  rw [recoverSender, hr, hs, hv, hashed, htype]
  decide +kernel

/-- The observed transaction fields determine the creator once the single
fixed signing-payload hash has been established. No sender is supplied as a
separate premise. Original-body correspondence remains the consumer's job. -/
theorem recoveredSender_of_fields {tx : Tx}
    (htype : tx.type = .zero 21000000000 none)
    (hnonce : tx.nonce = 446) (hgas : tx.gas = 1500000)
    (hvalue : tx.value = 0) (hdata : tx.data = code.toList) (hv : tx.v = 37)
    (hr : tx.r.toB256 =
      0x7ce08af79f7a6c1b8b336f50890a80602c4dcd1e3cc5ca131373f0e8ff15e278)
    (hs : tx.s.toB256 =
      0x45e183d91f1e8f31e32d333cf6090990c9bf7d35dd00472cfd2d3a63ca8b1a5)
    (hashed : signingPayload.keccak =
      0x1e62afdbf54076edd8083f93eab1bf693f2a5a3675886b669d13d9b3e6221235) :
    recoverSender 1 tx = .ok deployer := by
  apply recoveredSender_of_signingHash htype hv hr hs
  exact (signingEncoded htype hnonce hgas hvalue hdata hv).trans (congrArg some hashed)

/-- The explicit creation fields recover the deployer using the proved payload
hash. Original transaction correspondence remains explicit at the consumer. -/
theorem recoveredSender_of_creation_fields {tx : Tx}
    (htype : tx.type = .zero 21000000000 none)
    (hnonce : tx.nonce = 446) (hgas : tx.gas = 1500000)
    (hvalue : tx.value = 0) (hdata : tx.data = code.toList) (hv : tx.v = 37)
    (hr : tx.r.toB256 =
      0x7ce08af79f7a6c1b8b336f50890a80602c4dcd1e3cc5ca131373f0e8ff15e278)
    (hs : tx.s.toB256 =
      0x45e183d91f1e8f31e32d333cf6090990c9bf7d35dd00472cfd2d3a63ca8b1a5)
    : recoverSender 1 tx = .ok deployer := by
  exact recoveredSender_of_fields htype hnonce hgas hvalue hdata hv hr hs signingPayload_hash

end Blanc.Lift.Weth9.Creation
