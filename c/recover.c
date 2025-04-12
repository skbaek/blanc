#include <stdio.h>
#include <string.h>
#include <lean/lean.h>
#include <secp256k1.h>
#include <secp256k1_recovery.h>
#include "keccak.h"

int recover_address(
  const unsigned char *msg_hash,
  const unsigned char *signature,
  int recovery_id,
  unsigned char *address_out  // expects 20 bytes buffer
) {
  secp256k1_context* ctx = secp256k1_context_create(SECP256K1_CONTEXT_VERIFY);
  secp256k1_ecdsa_recoverable_signature sig;
  secp256k1_pubkey pubkey;
  unsigned char public_key[65];
  size_t pubkey_len = 65;

  // Parse the recoverable signature
  if (!secp256k1_ecdsa_recoverable_signature_parse_compact(ctx, &sig, signature, recovery_id)) {
    printf("Signature parsing failed\n");
    secp256k1_context_destroy(ctx);
    return 0;
  }

  // Recover the public key
  if (!secp256k1_ecdsa_recover(ctx, &pubkey, &sig, msg_hash)) {
    printf("Public key recovery failed\n");
    secp256k1_context_destroy(ctx);
    return 0;
  }

  // Serialize the public key
  if (!secp256k1_ec_pubkey_serialize(
    ctx, public_key, &pubkey_len, &pubkey, 
    SECP256K1_EC_UNCOMPRESSED
  )) {
    printf("Public key serialization failed\n");
    secp256k1_context_destroy(ctx);
    return 0;
  }

  // Convert to normal signature
  secp256k1_ecdsa_signature sig_normal;
  if (!secp256k1_ecdsa_recoverable_signature_convert(ctx, &sig_normal, &sig)) {
    printf("Signature conversion failed\n");
    secp256k1_context_destroy(ctx);
    return 0;
  }

  // // Verify signature
  // // This step sometimes fails, even for inputs & outputs harmless
  // // for EVM functioning, so it is disabled.
  // if (!secp256k1_ecdsa_verify(ctx, &sig_normal, msg_hash, &pubkey)) {
  //   printf("Verification failed\n");
  //   secp256k1_context_destroy(ctx);
  //   return 0;
  // }
  
  secp256k1_context_destroy(ctx);

  // Hash the public key (excluding the first byte)
  bytes32 hash = keccak(&public_key[1], 64);
  
  // Copy last 20 bytes to output address
  memcpy(address_out, &hash.data[12], 20);
  
  return 1;
}

lean_obj_res ecrecover_flag(lean_obj_arg hsa, uint8_t ri, lean_obj_arg rsa) 
{
  // Get direct access to the byte array data
  uint8_t* rs = lean_sarray_cptr(rsa);
  uint8_t* hs = lean_sarray_cptr(hsa);

  // Create new ByteArray
  lean_obj_res pubAddr = lean_alloc_sarray(1, 21, 21);
  uint8_t* pubAddrPtr = lean_sarray_cptr(pubAddr);

  if (recover_address(hs, rs, ri, pubAddrPtr + 1)) {
    *pubAddrPtr = 1;
  } else {
    *pubAddrPtr = 0;
  }

  lean_dec_ref(rsa);
  lean_dec_ref(hsa);
  return pubAddr;
}          