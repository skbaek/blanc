#include <string.h>
#include "keccak.h"

#if defined(_MSC_VER)
#define SHA3_CONST(x) x
#else
#define SHA3_CONST(x) x##L
#endif

#ifndef SHA3_ROTL64
#define SHA3_ROTL64(x, y) \
	(((x) << (y)) | ((x) >> (64 - (y))))
#endif

static const uint64_t keccakf_rndc[24] = {
    SHA3_CONST(0x0000000000000001UL), SHA3_CONST(0x0000000000008082UL),
    SHA3_CONST(0x800000000000808aUL), SHA3_CONST(0x8000000080008000UL),
    SHA3_CONST(0x000000000000808bUL), SHA3_CONST(0x0000000080000001UL),
    SHA3_CONST(0x8000000080008081UL), SHA3_CONST(0x8000000000008009UL),
    SHA3_CONST(0x000000000000008aUL), SHA3_CONST(0x0000000000000088UL),
    SHA3_CONST(0x0000000080008009UL), SHA3_CONST(0x000000008000000aUL),
    SHA3_CONST(0x000000008000808bUL), SHA3_CONST(0x800000000000008bUL),
    SHA3_CONST(0x8000000000008089UL), SHA3_CONST(0x8000000000008003UL),
    SHA3_CONST(0x8000000000008002UL), SHA3_CONST(0x8000000000000080UL),
    SHA3_CONST(0x000000000000800aUL), SHA3_CONST(0x800000008000000aUL),
    SHA3_CONST(0x8000000080008081UL), SHA3_CONST(0x8000000000008080UL),
    SHA3_CONST(0x0000000080000001UL), SHA3_CONST(0x8000000080008008UL)
};

static const unsigned keccakf_rotc[24] = {
  1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 
  27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44
};

static const unsigned keccakf_piln[24] = {
  10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 
  15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1
};

static void keccakf(uint64_t s[25])
{
  int i, j, round;
  uint64_t t, bc[5];
  #define KECCAK_ROUNDS 24

  for(round = 0; round < KECCAK_ROUNDS; round++) 
  {
    /* Theta */
    for(i = 0; i < 5; i++)
      bc[i] = s[i] ^ s[i + 5] ^ s[i + 10] ^ s[i + 15] ^ s[i + 20];

    for(i = 0; i < 5; i++) 
    {
      t = bc[(i + 4) % 5] ^ SHA3_ROTL64(bc[(i + 1) % 5], 1);
      for(j = 0; j < 25; j += 5)
        s[j + i] ^= t;
    }

    /* Rho Pi */
    t = s[1];
    for(i = 0; i < 24; i++) 
    {
      j = keccakf_piln[i];
      bc[0] = s[j];
      s[j] = SHA3_ROTL64(t, keccakf_rotc[i]);
      t = bc[0];
    }
    
    /* Chi */
    for(j = 0; j < 25; j += 5) {
      for(i = 0; i < 5; i++)
        bc[i] = s[j + i];
      for(i = 0; i < 5; i++)
        s[j + i] ^= (~bc[(i + 1) % 5]) & bc[(i + 2) % 5];
    }

    /* Iota */
    s[0] ^= keccakf_rndc[round];
  }
}

void sha3_Update(void *priv, void const *bufIn, size_t len)
{
  sha3_context *ctx = (sha3_context *) priv;
  size_t words = len / 8;
  unsigned tail = len - (len / 8) * 8;
  size_t i;
  const uint8_t *buf = bufIn;

  for(i = 0; i < words; i++, buf += 8) 
  {
    const uint64_t t = (uint64_t) (buf[0]) |
            ((uint64_t) (buf[1]) << 8 * 1) |
            ((uint64_t) (buf[2]) << 8 * 2) |
            ((uint64_t) (buf[3]) << 8 * 3) |
            ((uint64_t) (buf[4]) << 8 * 4) |
            ((uint64_t) (buf[5]) << 8 * 5) |
            ((uint64_t) (buf[6]) << 8 * 6) |
            ((uint64_t) (buf[7]) << 8 * 7);
    ctx->u.s[ctx->wordIndex] ^= t;
    if(++ctx->wordIndex == 17) 
    {
      keccakf(ctx->u.s);
      ctx->wordIndex = 0;
    }
  }

  while (tail--) {
    ctx->saved |= (uint64_t) (*(buf++)) << ((ctx->byteIndex++) * 8);
  }
}

void const * sha3_Finalize(void *priv)
{
  sha3_context *ctx = (sha3_context *) priv;
  uint64_t t = (uint64_t)(((uint64_t) 1) << (ctx->byteIndex * 8));
  unsigned i;

  ctx->u.s[ctx->wordIndex] ^= ctx->saved ^ t;
  ctx->u.s[16] ^= SHA3_CONST(0x8000000000000000UL);
  keccakf(ctx->u.s);

  for(i = 0; i < 25; i++) 
  {
    const unsigned t1 = (uint32_t) ctx->u.s[i];
    const unsigned t2 = (uint32_t) ((ctx->u.s[i] >> 16) >> 16);
    ctx->u.sb[i * 8 + 0] = (uint8_t) (t1);
    ctx->u.sb[i * 8 + 1] = (uint8_t) (t1 >> 8);
    ctx->u.sb[i * 8 + 2] = (uint8_t) (t1 >> 16);
    ctx->u.sb[i * 8 + 3] = (uint8_t) (t1 >> 24);
    ctx->u.sb[i * 8 + 4] = (uint8_t) (t2);
    ctx->u.sb[i * 8 + 5] = (uint8_t) (t2 >> 8);
    ctx->u.sb[i * 8 + 6] = (uint8_t) (t2 >> 16);
    ctx->u.sb[i * 8 + 7] = (uint8_t) (t2 >> 24);
  }

  return (ctx->u.sb);
}

bytes32 keccak(void* p, size_t input_len) 
{
  unsigned i;
  sha3_context c;
  const uint8_t *hash;
  bytes32 bs;

  memset(&c, 0, sizeof(c));
  c.capacityWords = 0x80000008; 
  sha3_Update(&c, p, input_len);
  hash = sha3_Finalize(&c);

  memcpy(bs.data, hash, 32);
  return bs;
}