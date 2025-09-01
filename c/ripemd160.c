/*
 *  MIT License
 *
 *  Copyright (c) 2021 David Turner
 *
 *  Permission is hereby granted, free of charge, to any person obtaining a copy
 *  of this software and associated documentation files (the "Software"), to deal
 *  in the Software without restriction, including without limitation the rights
 *  to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 *  copies of the Software, and to permit persons to whom the Software is
 *  furnished to do so, subject to the following conditions:
 *
 *  The above copyright notice and this permission notice shall be included in all
 *  copies or substantial portions of the Software.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 *  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 *  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 *  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 *  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 *  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 *  SOFTWARE.
 */

#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <lean/lean.h>

/**
 * @brief Reverses the byte order (endianness) of a 32-bit integer.
 * @param value The integer to swap.
 * @return The byte-swapped integer.
 * @example 0x12345678 -> 0x78563412
 */
uint32_t mirror(uint32_t value) {
    // Isolate each byte and shift it to its new position
    uint32_t byte1 = (value & 0x000000FF) << 24; // LSB to MSB
    uint32_t byte2 = (value & 0x0000FF00) << 8;
    uint32_t byte3 = (value & 0x00FF0000) >> 8;
    uint32_t byte4 = (value & 0xFF000000) >> 24; // MSB to LSB
    
    return byte1 | byte2 | byte3 | byte4;
}

/**
 * @brief Prints the 160-bit (5 x 32-bit) RIPEMD-160 digest state.
 * @param label A descriptive string for the debug message.
 * @param digest A pointer to the five 32-bit words of the digest.
 */
void print_digest(const char* label, const uint32_t* digest) {
    printf("%-30s: ", label);
    for (int i = 0; i < 5; i++) {
        printf("%08x ", digest[i]);
    }
    printf("\n");
}

// void ripemd160(const uint8_t* data, uint32_t data_len, uint8_t* digest_bytes);

/* Constants etc. taken directly from https://homes.esat.kuleuven.be/~bosselae/ripemd160/pdf/AB-9601/AB-9601.pdf */

uint32_t ripemd160_initial_digest[5] =
    { 0x67452301UL, 0xefcdab89UL, 0x98badcfeUL, 0x10325476UL, 0xc3d2e1f0UL };

uint8_t ripemd160_rho[16] =
    { 0x7, 0x4, 0xd, 0x1, 0xa, 0x6, 0xf, 0x3, 0xc, 0x0, 0x9, 0x5, 0x2, 0xe, 0xb, 0x8 };

uint8_t ripemd160_shifts[80] =
    { 11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8
    , 12, 13, 11, 15, 6, 9, 9, 7, 12, 15, 11, 13, 7, 8, 7, 7
    , 13, 15, 14, 11, 7, 7, 6, 8, 13, 14, 13, 12, 5, 5, 6, 9
    , 14, 11, 12, 14, 8, 6, 5, 5, 15, 12, 15, 14, 9, 9, 8, 6
    , 15, 12, 13, 13, 9, 5, 8, 6, 14, 11, 12, 11, 8, 6, 5, 5
    };

uint32_t ripemd160_constants_left[5] =
    { 0x00000000UL, 0x5a827999UL, 0x6ed9eba1UL, 0x8f1bbcdcUL, 0xa953fd4eUL };

uint32_t ripemd160_constants_right[5] =
    { 0x50a28be6UL, 0x5c4dd124UL, 0x6d703ef3UL, 0x7a6d76e9UL, 0x00000000UL };

uint8_t ripemd160_fns_left[5]  = { 1, 2, 3, 4, 5 };

uint8_t ripemd160_fns_right[5] = { 5, 4, 3, 2, 1 };

#define ROL(x, n) (((x) << (n)) | ((x) >> (32 - (n))))

void ripemd160_compute_line(uint32_t* digest, uint32_t* words, uint32_t* chunk, uint8_t* index, uint8_t* shifts, uint32_t* ks, uint8_t* fns) {

    printf("\n---------------- ENTER : compute line ----------------\n");

    for (uint8_t i = 0; i < 5; i++) {
        words[i] = digest[i];
    }

    for (uint8_t round = 0; /* breaks out mid-loop */; round++) {
        // printf("round : %02x\n", round);

        uint32_t k  = ks[round];
        uint8_t  fn = fns[round];

        bool verbose = false;

        if (fns[0] == 1 && round == 0) {
            verbose = true;
        }  

        if (verbose) {
            printf("values at beginning of round-loop :\n");
            printf("  k : %08x\n", k);
            printf("  fn : %02x\n", fn);
            printf("  indices :");
            for (uint8_t i = 0; i < 16; i++) {
                printf(" %02x", index[i]);
            }
            printf("\n");
        } 

        for (uint8_t i = 0; i < 16; i++) {
            if (verbose) {
                printf("i : %02x\n", i);
            }

            if (verbose) {
                printf("words at beginning of i-loop :");
                for (uint8_t i = 0; i < 5; i++) {
                    printf(" %08x", words[i]);
                }
                printf("\n");
            } 

            uint32_t tmp;
            switch (fn) {
                case 1:
                    tmp = words[1] ^ words[2] ^ words[3];
                    break;
                case 2:
                    tmp = (words[1] & words[2]) | (~words[1] & words[3]);
                    break;
                case 3:
                    tmp = (words[1] | ~words[2]) ^ words[3];
                    break;
                case 4:
                    tmp = (words[1] & words[3]) | (words[2] & ~words[3]);
                    break;
                case 5:
                    tmp = words[1] ^ (words[2] | ~words[3]);
                    break;
            }

            if (verbose) {
                printf("init tmp : %08x\n", tmp);
            }

            tmp += words[0] + chunk[index[i]] + k;



            if (verbose) {
                printf("tmp after addition : %08x\n", tmp);
            }

            // printf("tmp after ROL by %02x : %08x\n", shifts[index[i]], ROL(tmp, shifts[index[i]]));

            tmp = ROL(tmp, shifts[index[i]]) + words[4];

            if (verbose) {
                printf("index retrieved : %02x\n", index[i]);
                printf("rotation offset : %02x\n", shifts[index[i]]);
                printf("add amount (w4) : %08x\n", words[4]);
                printf("tmp after rotation & addition : %08x\n", tmp);
            }

            words[0] = words[4];
            words[4] = words[3];
            words[3] = ROL(words[2], 10);
            words[2] = words[1];
            words[1] = tmp;
        }
        if (round == 4) {
            break;
        }
        shifts += 16;

        uint8_t index_tmp[16];
        for (uint8_t i = 0; i < 16; i++) {
            index_tmp[i] = ripemd160_rho[index[i]];
        }

        for (uint8_t i = 0; i < 16; i++) {
            index[i] = index_tmp[i];
        }

        if (verbose) {
            printf("new indices :");
            for (uint8_t i = 0; i < 16; i++) {
                printf(" %02x", index[i]);
            }
            printf("\n");
        }
    }

    printf("words returned by compute line :");
    for (uint8_t i = 0; i < 5; i++) {
        printf(" %08x", words[i]);
    }
    printf("\n");

    printf("\n---------------- EXIT : compute line ----------------\n");
}

void ripemd160_update_digest(uint32_t* digest, uint32_t* chunk)
{
    printf("\n---------------- ENTER : update digest ----------------\n");

    print_digest("digest arg for update digest", digest); 

    printf("--- chunk arg for update digest ---\n");

    for (int i = 0; i < 16; i++) {
        printf("%08x ", chunk[i]);
        if ((i + 1) % 4 == 0) {
            printf("\n");
        }
    }

    uint8_t index[16];

    /* initial permutation for left line is the identity */
    for (uint8_t i = 0; i < 16; i++) {
        index[i] = i;
    }

    uint32_t words_left[5];
    ripemd160_compute_line(digest, words_left, chunk, index, ripemd160_shifts, ripemd160_constants_left, ripemd160_fns_left);

    printf("\nwords left after compute :");
    for (uint8_t i = 0; i < 5; i++) {
        printf("%08x ", words_left[i]);
    }
    printf("\n");

    /* initial permutation for right line is 5+9i (mod 16) */
    index[0] = 5;
    for (uint8_t i = 1; i < 16; i++) {
        index[i] = (index[i-1] + 9) & 0x0f;
    }

    uint32_t words_right[5];
    ripemd160_compute_line(digest, words_right, chunk, index, ripemd160_shifts, ripemd160_constants_right, ripemd160_fns_right);

    printf("\nwords right after compute :");
    for (uint8_t i = 0; i < 5; i++) {
        printf("%08x ", words_right[i]);
    }
    printf("\n");

    /* update digest */
    digest[0] += words_left[1] + words_right[2];
    digest[1] += words_left[2] + words_right[3];
    digest[2] += words_left[3] + words_right[4];
    digest[3] += words_left[4] + words_right[0];
    digest[4] += words_left[0] + words_right[1];

    /* final rotation */
    words_left[0] = digest[0];
    digest[0] = digest[1];
    digest[1] = digest[2];
    digest[2] = digest[3];
    digest[3] = digest[4];
    digest[4] = words_left[0];

    print_digest("digest computed by update digest", digest); 

    printf("\n---------------- EXIT : update digest ----------------\n");
}


void ripemd160(const uint8_t* data, uint32_t data_len, uint8_t* digest_bytes)
{
    printf("\n---------------- ENTER : ripemd160 (C) ----------------\n");

    printf("\ndata arg for ripemd160 (%u bytes) : \n", data_len);
    for (uint32_t i = 0; i < data_len; i++) {
        printf("%02x ", data[i]);
        if ((i + 1) % 16 == 0 && (i + 1) < data_len) {
            printf("\n");
        }
    }

    /* NB assumes correct endianness */
    uint32_t *digest = (uint32_t*)digest_bytes;
    for (uint8_t i = 0; i < 5; i++) {
        digest[i] = ripemd160_initial_digest[i];
    }

    print_digest("\ninitial digest", digest); // <<< DEBUG MESSAGE

    const uint8_t *last_chunk_start = data + (data_len & (~0x3f));
    while (data < last_chunk_start) {
        printf("\nrunning while loop...");
        ripemd160_update_digest(digest, (uint32_t*)data);
        data += 0x40;
    }

    print_digest("\ndigest after while loop", digest); // <<< DEBUG MESSAGE

    uint8_t last_chunk[0x40];
    uint8_t leftover_size = data_len & 0x3f;
    for (uint8_t i = 0; i < leftover_size; i++) {
        last_chunk[i] = *data++;
    }

    /* append a single 1 bit and then zeroes, leaving 8 bytes for the length at the end */
    last_chunk[leftover_size] = 0x80;
    for (uint8_t i = leftover_size + 1; i < 0x40; i++) {
        last_chunk[i] = 0;
    }

    if (leftover_size >= 0x38) {
        /* no room for size in this chunk, add another chunk of zeroes */
        ripemd160_update_digest(digest, (uint32_t*)last_chunk);
        for (uint8_t i = 0; i < 0x38; i++) {
            last_chunk[i] = 0;
        }
    }

    print_digest("\ndigest after penultimate chunk", digest); // <<< DEBUG MESSAGE

    uint32_t *length_lsw = (uint32_t *)(last_chunk + 0x38);
    *length_lsw = (data_len << 3);
    uint32_t *length_msw = (uint32_t *)(last_chunk + 0x3c);
    *length_msw = (data_len >> 29);

    ripemd160_update_digest(digest, (uint32_t*)last_chunk);

    print_digest("digest after last chunk", digest); // <<< DEBUG MESSAGE

    printf("\n---------------- EXIT : ripemd160 ----------------\n");
}

lean_obj_res rip160(lean_obj_arg da) 
{
  // Get direct access to the byte array data
  uint8_t* d = lean_sarray_cptr(da);
  size_t len = lean_sarray_size(da);

  // Create new ByteArray
  lean_obj_res pubAddr = lean_alloc_sarray(1, 20, 20);
  uint8_t* pubAddrPtr = lean_sarray_cptr(pubAddr);

  ripemd160(d, len, pubAddrPtr);

  lean_dec_ref(da);
  return pubAddr;
}          