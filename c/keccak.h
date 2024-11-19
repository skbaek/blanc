#include <stdint.h>

typedef struct {
    uint64_t saved;             /* the portion of the input message that we
                                 * didn't consume yet */
    union {                     /* Keccak's state */
        uint64_t s[25];
        uint8_t sb[25 * 8];
    } u;
    unsigned byteIndex;         /* 0..7--the next byte after the set one
                                 * (starts from 0; 0--none are buffered) */
    unsigned wordIndex;         /* 0..24--the next word to integrate input
                                 * (starts from 0) */
    unsigned capacityWords;     /* the double size of the hash output in
                                 * words (e.g. 16 for Keccak 512) */
} sha3_context;

// void sha3_Update(void *priv, void const *bufIn, size_t len);
// 
// void const *sha3_Finalize(void *priv);

typedef struct 
{
  uint8_t data[32];
} bytes32;

bytes32 keccak(void* p, size_t input_len);