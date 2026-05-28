// -----------------------------------------------------------------------
// Simple primality check based on BPSW
// -----------------------------------------------------------------------

#include <assert.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "simple_primality.h"
#include "simple_primality_alloc.h"
#include "simple_primality_precompute.h"

typedef unsigned __int128 uint128_t;

// x % (2^b -1)
static uint64_t mpz_mod_mersenne(mpz_t x, uint64_t b)
{
    uint64_t mask = (1ull << b) - 1;
    unsigned s = mpz_size(x);
    const mp_limb_t *array = mpz_limbs_read(x);
    uint128_t t, r = 0;

    if ((b & (b - 1)) == 0)
    {
        // b is an exact power of 2
        for (unsigned i = 0; i < s; i += 1)
        {
            r += array[i];
        }
    }
    else
    {
        // add, shift first, and reduce after
        unsigned c = 0;
        for (unsigned i = 0; i < b; i += 1)
        {
            t = 0;
            for (unsigned j = i; j < s; j += b)
            {
                t += array[j];
            }
            t = (t & mask) + (t >> b);
            t = t << c;
            r += t;
            r = (r & mask) + (r >> b);
            c += 64;
            while (c >= b)
            {
                c -= b;
            }
        }
    }
    // reduce mod 2^b - 1 to a 64 bit number
    while (r >> 64)
    {
        r = (r & mask) + (r >> b);
    }
    return (uint64_t)r;
}

// (u << 64 + v) mod n
static inline uint64_t longmod(uint64_t u, uint64_t v, uint64_t n)
{
#ifdef __x86_64__
    uint64_t r, a;
    asm("divq %4" : "=d"(r), "=a"(a) : "0"(u), "1"(v), "r"(n));
    return r;
#else
    uint128_t t = ((uint128_t)u << 64) + v;
    return t % n;
#endif
}

// (u) mod n
static inline uint64_t longlongmod(uint128_t u, uint64_t n)
{
#ifdef __x86_64__
    uint64_t r = (uint64_t)(u >> 64), a = (uint64_t)u;
    asm("divq %4" : "=d"(r), "=a"(a) : "0"(r), "1"(a), "r"(n));
    return r;
#else
    return u % n;
#endif
}

static inline uint64_t mulmod(uint64_t a, uint64_t b, uint64_t n)
{
#ifdef __x86_64__
    uint64_t r;
    asm("mul %3" : "=d"(r), "=a"(a) : "1"(a), "r"(b));
    asm("div %4" : "=d"(r), "=a"(a) : "0"(r), "1"(a), "r"(n));
    return r;
#else
    uint128_t tmp = (uint128_t)a * b;
    tmp %= n;
    return tmp;
#endif
}

static inline uint64_t squaremod(uint64_t a, uint64_t n)
{
#ifdef __x86_64__
    uint64_t r;
    asm("mul %2" : "=d"(r), "=a"(a) : "1"(a));
    asm("div %4" : "=d"(r), "=a"(a) : "0"(r), "1"(a), "r"(n));
    return r;
#else
    uint128_t tmp = (uint128_t)a * a;
    tmp %= n;
    return tmp;
#endif
}

// (u << s) mod n
static inline uint64_t shiftmod(uint64_t u, uint64_t s, uint64_t n)
{
#ifdef __x86_164__
    uint64_t r;
    asm("xor %0, %0\n shldq %b3, %1, %0\n shlxq %3, %1, %%rax\n divq %2"
        : "=&d"(r)
        : "r"(u), "r"(n), "c"(s)
        : "flags", "%rax");
    return r;
#else
    uint128_t t = (uint128_t)u;
    t <<= s;
    return t % n;
#endif
}

// count leading zeroed bits
static inline uint64_t uint64_lzcnt(uint64_t a)
{
#ifdef __x86_64__
    uint64_t r;
    asm("lzcnt %1,%0" : "=r"(r) : "r"(a));
    return r;
#else
    return __builtin_clzll(a);
#endif
}

// count trailing zeroed bits
static inline uint64_t uint64_tzcnt(uint64_t a)
{
#ifdef __x86_64__
    uint64_t r;
    asm("tzcnt %1,%0" : "=r"(r) : "r"(a));
    return r;
#else
    return __builtin_ctzll(a);
#endif
}

// simple floor(log_2) function for integers
// log(1) = 0
// log(2) = 1
// log(3) = 1
// log(4) = 2 ...
static inline uint64_t uint64_log_2(uint64_t a)
{
    return 63 - uint64_lzcnt(a);
}

typedef enum sieve_e
{
    COMPOSITE_FOR_SURE,
    PRIME_FOR_SURE,
    UNDECIDED
} sieve_t;

// sieve small primes
static sieve_t uint64_composite_sieve(uint64_t a)
{
    if (a <= 152)
    {
        // return COMPOSITE_FOR_SURE for small numbers which are composite for sure , without checking further.
        sieve_t stooopid_prime_table[] = {
            PRIME_FOR_SURE,     PRIME_FOR_SURE,     PRIME_FOR_SURE,     PRIME_FOR_SURE,     COMPOSITE_FOR_SURE,
            PRIME_FOR_SURE,     COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE, PRIME_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, PRIME_FOR_SURE,
            COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, PRIME_FOR_SURE,
            COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, PRIME_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, PRIME_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE, PRIME_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE, PRIME_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, PRIME_FOR_SURE,
            COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, PRIME_FOR_SURE,
            COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE,
            COMPOSITE_FOR_SURE, COMPOSITE_FOR_SURE, PRIME_FOR_SURE,     COMPOSITE_FOR_SURE, PRIME_FOR_SURE,
            COMPOSITE_FOR_SURE};
        return stooopid_prime_table[a];
    }

    // divisibility is based on Barrett modular reductions by constants, use modular multiplications
    if ((uint64_t)(a * 0xaaaaaaaaaaaaaaabull) <= 0x5555555555555555ull)
        return COMPOSITE_FOR_SURE; // divisible by 3
    if ((uint64_t)(a * 0xcccccccccccccccdull) <= 0x3333333333333333ull)
        return COMPOSITE_FOR_SURE; // divisible by 5
    if ((uint64_t)(a * 0x6db6db6db6db6db7ull) <= 0x2492492492492492ull)
        return COMPOSITE_FOR_SURE; // divisible by 7
    if ((uint64_t)(a * 0x2e8ba2e8ba2e8ba3ull) <= 0x1745d1745d1745d1ull)
        return COMPOSITE_FOR_SURE; // divisible by 11
    if ((uint64_t)(a * 0x4ec4ec4ec4ec4ec5ull) <= 0x13b13b13b13b13b1ull)
        return COMPOSITE_FOR_SURE; // divisible by 13
    if ((uint64_t)(a * 0xf0f0f0f0f0f0f0f1ull) <= 0x0f0f0f0f0f0f0f0full)
        return COMPOSITE_FOR_SURE; // divisible by 17
    if ((uint64_t)(a * 0x86bca1af286bca1bull) <= 0x0d79435e50d79435ull)
        return COMPOSITE_FOR_SURE; // divisible by 19
    if ((uint64_t)(a * 0xd37a6f4de9bd37a7ull) <= 0x0b21642c8590b216ull)
        return COMPOSITE_FOR_SURE; // divisible by 23
    if ((uint64_t)(a * 0x34f72c234f72c235ull) <= 0x08d3dcb08d3dcb08ull)
        return COMPOSITE_FOR_SURE; // divisible by 29
    if ((uint64_t)(a * 0xef7bdef7bdef7bdfull) <= 0x0842108421084210ull)
        return COMPOSITE_FOR_SURE; // divisible by 31
    if (a < 37 * 37)
        return PRIME_FOR_SURE;
    if ((uint64_t)(a * 0x14c1bacf914c1badull) <= 0x06eb3e45306eb3e4ull)
        return COMPOSITE_FOR_SURE; // divisible by 37
    if ((uint64_t)(a * 0x8f9c18f9c18f9c19ull) <= 0x063e7063e7063e70ull)
        return COMPOSITE_FOR_SURE; // divisible by 41
    if ((uint64_t)(a * 0x82fa0be82fa0be83ull) <= 0x05f417d05f417d05ull)
        return COMPOSITE_FOR_SURE; // divisible by 43
    if ((uint64_t)(a * 0x51b3bea3677d46cfull) <= 0x0572620ae4c415c9ull)
        return COMPOSITE_FOR_SURE; // divisible by 47
    if ((uint64_t)(a * 0x21cfb2b78c13521dull) <= 0x04d4873ecade304dull)
        return COMPOSITE_FOR_SURE; // divisible by 53
    if ((uint64_t)(a * 0xcbeea4e1a08ad8f3ull) <= 0x0456c797dd49c341ull)
        return COMPOSITE_FOR_SURE; // divisible by 59
    if ((uint64_t)(a * 0x4fbcda3ac10c9715ull) <= 0x04325c53ef368eb0ull)
        return COMPOSITE_FOR_SURE; // divisible by 61
    if ((uint64_t)(a * 0xf0b7672a07a44c6bull) <= 0x03d226357e16ece5ull)
        return COMPOSITE_FOR_SURE; // divisible by 67
    if ((uint64_t)(a * 0x193d4bb7e327a977ull) <= 0x039b0ad12073615aull)
        return COMPOSITE_FOR_SURE; // divisible by 71
    if ((uint64_t)(a * 0x7e3f1f8fc7e3f1f9ull) <= 0x0381c0e070381c0eull)
        return COMPOSITE_FOR_SURE; // divisible by 73
    if ((uint64_t)(a * 0x9b8b577e613716afull) <= 0x033d91d2a2067b23ull)
        return COMPOSITE_FOR_SURE; // divisible by 79
    if ((uint64_t)(a * 0xa3784a062b2e43dbull) <= 0x03159721ed7e7534ull)
        return COMPOSITE_FOR_SURE; // divisible by 83
    if ((uint64_t)(a * 0xf47e8fd1fa3f47e9ull) <= 0x02e05c0b81702e05ull)
        return COMPOSITE_FOR_SURE; // divisible by 89
    if ((uint64_t)(a * 0xa3a0fd5c5f02a3a1ull) <= 0x02a3a0fd5c5f02a3ull)
        return COMPOSITE_FOR_SURE; // divisible by 97
    if (a < 101 * 101)
        return PRIME_FOR_SURE;
    if ((uint64_t)(a * 0x3a4c0a237c32b16dull) <= 0x0288df0cac5b3f5dull)
        return COMPOSITE_FOR_SURE; // divisible by 101
    if ((uint64_t)(a * 0xdab7ec1dd3431b57ull) <= 0x027c45979c95204full)
        return COMPOSITE_FOR_SURE; // divisible by 103
    if ((uint64_t)(a * 0x77a04c8f8d28ac43ull) <= 0x02647c69456217ecull)
        return COMPOSITE_FOR_SURE; // divisible by 107
    if ((uint64_t)(a * 0xa6c0964fda6c0965ull) <= 0x02593f69b02593f6ull)
        return COMPOSITE_FOR_SURE; // divisible by 109
    if ((uint64_t)(a * 0x90fdbc090fdbc091ull) <= 0x0243f6f0243f6f02ull)
        return COMPOSITE_FOR_SURE; // divisible by 113
    if ((uint64_t)(a * 0x7efdfbf7efdfbf7full) <= 0x0204081020408102ull)
        return COMPOSITE_FOR_SURE; // divisible by 127
    if ((uint64_t)(a * 0x03e88cb3c9484e2bull) <= 0x01f44659e4a42715ull)
        return COMPOSITE_FOR_SURE; // divisible by 131
    if ((uint64_t)(a * 0xe21a291c077975b9ull) <= 0x01de5d6e3f8868a4ull)
        return COMPOSITE_FOR_SURE; // divisible by 137
    if ((uint64_t)(a * 0x3aef6ca970586723ull) <= 0x01d77b654b82c339ull)
        return COMPOSITE_FOR_SURE; // divisible by 139
    if ((uint64_t)(a * 0xdf5b0f768ce2cabdull) <= 0x01b7d6c3dda338b2ull)
        return COMPOSITE_FOR_SURE; // divisible by 149
    if ((uint64_t)(a * 0x6fe4dfc9bf937f27ull) <= 0x01b2036406c80d90ull)
        return COMPOSITE_FOR_SURE; // divisible by 151

    // no factor less than 157
    if (a < 157 * 157)
        return PRIME_FOR_SURE; // prime
    return UNDECIDED;
}

// modular exponentiation 2^e mod m
// assume e > 0, m > 0
static uint64_t pow2_mod(uint64_t e, uint64_t m)
{
    uint64_t n = uint64_log_2(e);
    uint64_t s = (n >= 5) ? 5 : n;
    n -= s;
    uint64_t mask = e >> n;
    uint64_t result = shiftmod(1ull, mask, m);
    while (n >= 6)
    {
        n -= 6;
        result = squaremod(result, m);
        result = squaremod(result, m);
        result = squaremod(result, m);
        result = squaremod(result, m);
        result = squaremod(result, m);
        result = squaremod(result, m);
        mask = (e >> n) & 0x3f;
        result = shiftmod(result, mask, m);
    }
    while (n > 0)
    {
        n -= 1;
        result = squaremod(result, m);
        if ((e >> n) & 1)
        {
            result <<= 1;
            result -= (result >= m) ? m : 0;
        }
    }
    return result;
}

static bool is_perfect_square(uint64_t a)
{
    if (0xffedfdfefdecull & (1ull << (a % 48)))
        return false;
    if (0xfdfdfdedfdfcfdecull & (1ull << (a % 64)))
        return false;
    if (0x7bfdb7cfedbafd6cull & (1ull << (a % 63)))
        return false;
    if (0x7dcfeb79ee35ccull & (1ull << (a % 55)))
        return false;
    if (0x8ec196bf5a60dc4ull & (1ull << (a % 61)))
        return false;
    if (0x5d49de7c1846d44ull & (1ull << (a % 59)))
        return false;
    if (0xd228fccfc512cull & (1ull << (a % 53)))
        return false;
    if (0x7bcae4d8ac20ull & (1ull << (a % 47)))
        return false;
    if (0x4a77c5c11acull & (1ull << (a % 43)))
        return false;
    if (0x4c7d4af8c8ull & (1ull << (a % 41)))
        return false;
    if (0x9a1dee164ull & (1ull << (a % 37)))
        return false;
    if (0x6de2b848ull & (1ull << (a % 31)))
        return false;
    if (0xc2edd0cull & (1ull << (a % 29)))
        return false;
    if (0x7acca0ull & (1ull << (a % 23)))
        return false;
    if (0x4f50cull & (1ull << (a % 19)))
        return false;
    if (0x5ce8ull & (1ull << (a % 17)))
        return false;
    if (0x9e4ull & (1ull << (a % 13)))
        return false;

    // approximation of square root with floating point accuracy
    double d = (double)a;
    d = exp(log(d) / 2.0); // square root
    double dl = d * 0.999999;
    double dh = d * 1.000001;
    uint64_t c, m;
    // binary search (1 more bit of square root per iteration)
    uint64_t r = (uint64_t)d;
    uint64_t l = (uint64_t)dl;
    uint64_t h = (uint64_t)dh;
    while (l <= h)
    {
        m = (l + h) >> 1;
        c = m * m;
        if (c == a)
        {
            return true; // perfect square
        }
        if (c < a)
        {
            l = m + 1;
            r = m;
        }
        else
        {
            h = m - 1;
        }
    }
    c = r * r; // check perfect square
    return (c == a);
}

static bool mpz_is_perfect_square(mpz_t n)
{
    mpz_t ignore;
    mpz_init(ignore);
    uint64_t a = mpz_mod_ui(ignore, n, 64ull * 63ull * 55ull * 61ull * 59ull * 53ull * 47ull * 43ull * 41ull * 37ull);
    uint64_t b = mpz_mod_ui(ignore, n, 31ull * 29ull * 23ull * 19ull * 17ull * 13ull);
    mpz_clear(ignore);

    if (0xffedfdfefdecull & (1ull << (a % 48)))
        return false;
    if (0xfdfdfdedfdfcfdecull & (1ull << (a % 64)))
        return false;
    if (0x7bfdb7cfedbafd6cull & (1ull << (a % 63)))
        return false;
    if (0x7dcfeb79ee35ccull & (1ull << (a % 55)))
        return false;
    if (0x8ec196bf5a60dc4ull & (1ull << (a % 61)))
        return false;
    if (0x5d49de7c1846d44ull & (1ull << (a % 59)))
        return false;
    if (0xd228fccfc512cull & (1ull << (a % 53)))
        return false;
    if (0x7bcae4d8ac20ull & (1ull << (a % 47)))
        return false;
    if (0x4a77c5c11acull & (1ull << (a % 43)))
        return false;
    if (0x4c7d4af8c8ull & (1ull << (a % 41)))
        return false;
    if (0x9a1dee164ull & (1ull << (a % 37)))
        return false;
    if (0x6de2b848ull & (1ull << (b % 31)))
        return false;
    if (0xc2edd0cull & (1ull << (b % 29)))
        return false;
    if (0x7acca0ull & (1ull << (b % 23)))
        return false;
    if (0x4f50cull & (1ull << (b % 19)))
        return false;
    if (0x5ce8ull & (1ull << (b % 17)))
        return false;
    if (0x9e4ull & (1ull << (b % 13)))
        return false;

    // compute the rounded-down integer square root, check if the solution is exact.
    mpz_t u;
    mpz_init(u);
    uint64_t e = mpz_root(u, n, 2); // e = squareroot(n), e non zero if computation is exact.
    mpz_clear(u);
    return e ? true : false;
}

static int uint64_jacobi(uint64_t x, uint64_t y)
{
    // assert((y & 1) == 1);
    if (y == 1 || x == 1)
    {
        return 1;
    }

    if (x == 2)
    {
        // char j[4] = { -1,-1,1,1};
        // return j[((y - 3) >> 1) % 4];
        return ((y + 2) & 4) ? -1 : 1;
    }
    if (x == 3)
    {
        char j[6] = {0, (char)-1, (char)-1, 0, 1, 1};
        return j[((y - 3) >> 1) % 6];
    }
    if (x == 5)
    {
        char j[5] = {(char)-1, 0, (char)-1, 1, 1};
        return j[((y - 3) >> 1) % 5];
    }
    if (x == 7)
    {
        char j[14] = {1, (char)-1, 0, 1, (char)-1, (char)-1, (char)-1, (char)-1, 1, 0, (char)-1, 1, 1, 1};
        return j[((y - 3) >> 1) % 14];
    }
    if (x == 11)
    {
        char j[22] = {(char)-1, 1,        1,        1, 0, (char)-1, (char)-1, (char)-1, 1, (char)-1, (char)-1, 1,
                      (char)-1, (char)-1, (char)-1, 0, 1, 1,        1,        (char)-1, 1, 1};
        return j[((y - 3) >> 1) % 22];
    }
    if (x == 13)
    {
        char j[13] = {1, (char)-1, (char)-1, 1, (char)-1, 0, (char)-1, 1, (char)-1, (char)-1, 1, 1, 1};
        return j[((y - 3) >> 1) % 13];
    }
    if (x == 17)
    {
        char j[17] = {(char)-1, (char)-1, (char)-1, 1,        (char)-1, 1,        1, 0, 1,
                      1,        (char)-1, 1,        (char)-1, (char)-1, (char)-1, 1, 1};
        return j[((y - 3) >> 1) % 17];
    }
    if (x == 19)
    {
        char j[19] = {1,        1, (char)-1, 1,        (char)-1, (char)-1, 1,        1,        0,       (char)-1,
                      (char)-1, 1, 1,        (char)-1, 1,        (char)-1, (char)-1, (char)-1, (char)-1};
        unsigned t = ((y - 3) >> 1) % 38;
        return t >= 19 ? -j[t - 19] : j[t];
    }
    if (x == 23)
    {
        char j[23] = {(char)-1, (char)-1, 1,        1, 1,        1,        1,        (char)-1,
                      1,        (char)-1, 0,        1, (char)-1, 1,        (char)-1, (char)-1,
                      (char)-1, (char)-1, (char)-1, 1, 1,        (char)-1, (char)-1};
        unsigned t = ((y - 3) >> 1) % 46;
        return t >= 23 ? -j[t - 23] : j[t];
    }
    if (x == 29)
    {
        char j[29] = {(char)-1, 1, 1,        1, (char)-1, 1, (char)-1, (char)-1, (char)-1, (char)-1,
                      1,        1, (char)-1, 0, (char)-1, 1, 1,        (char)-1, (char)-1, (char)-1,
                      (char)-1, 1, (char)-1, 1, 1,        1, (char)-1, 1,        1};
        return j[((y - 3) >> 1) % 29];
    }
    if (x == 31)
    {
        char j[31] = {1,        1, (char)-1, 1,        1, (char)-1, 1,        (char)-1, (char)-1, (char)-1, 1,
                      1,        1, (char)-1, 0,        1, (char)-1, (char)-1, (char)-1, 1,        1,        1,
                      (char)-1, 1, (char)-1, (char)-1, 1, (char)-1, (char)-1, (char)-1, (char)-1};
        unsigned t = ((y - 3) >> 1) % 62;
        return t >= 31 ? -j[t - 31] : j[t];
    }

    int t = 1;
    uint64_t a = x;
    uint64_t n = y;
    unsigned v = n & 7;
    unsigned c = (v == 3) || (v == 5);
    while (a)
    {
        v = __builtin_ctzll(a);
        a >>= v;
        t = (c & (v & 1)) ? -t : t;

        if (a < n)
        {
            uint64_t tmp = a;
            a = n;
            n = tmp;
            t = ((a & n & 3) == 3) ? -t : t;
            v = n & 7;
            c = (v == 3) || (v == 5);
        }

        a -= n;
    }

    return (n == 1) ? t : 0;
}

static int uint64_minus_one_kronecker(uint64_t n)
{
    return (n & 2) ? -1 : 1;
}

static int mpz_minus_one_kronecker(mpz_t n)
{
    return (mpz_get_ui(n) & 2) ? -1 : 1;
}

// modular exponentiation a^e mod m
// assume e > 0, m > 0
static uint64_t pow_mod(uint64_t a, uint64_t e, uint64_t m)
{
    uint64_t n = uint64_log_2(e);
    uint64_t result = a;
    while (n--)
    {
        result = squaremod(result, m);
        if ((e >> n) & 1)
            result = mulmod(result, a, m);
    }
    return result;
}

// MR strong test
static bool uint64_witness(uint64_t n, uint64_t s, uint64_t d, uint64_t a)
{
    uint64_t x, y;
    if (n == a)
    {
        return true;
    }

    if (a == 2)
    {
        x = pow2_mod(d, n);
    }
    else
    {
        x = pow_mod(a, d, n);
    }

    while (s)
    {
        y = squaremod(x, n);
        if (y == 1 && x != 1 && x != n - 1)
        {
            return false;
        }
        x = y;
        --s;
    }
    if (x != 1)
    {
        return false;
    }
    return true;
}

// MR strong test
static bool mpz_witness(mpz_t n, uint64_t s, mpz_t d, mpz_t a)
{
    bool r = true;
    mpz_t x, y, nm1;
    mpz_inits(x, y, nm1, 0);
    mpz_sub_ui(nm1, n, 1);

    if (mpz_cmp(n, a) == 0)
    {
        goto done;
    }

    mpz_powm(x, a, d, n);

    while (s)
    {
        mpz_mul(y, x, x);
        mpz_mod(y, y, n);
        if (mpz_cmp_ui(y, 1) == 0 && mpz_cmp_ui(x, 1) != 0 && mpz_cmp(x, nm1) != 0)
        {
            r = false;
            goto done;
        }
        mpz_set(x, y);
        --s;
    }
    if (mpz_cmp_ui(x, 1) != 0)
    {
        r = false;
        goto done;
    }
done:
    mpz_clears(x, y, nm1, 0);
    return r;
}

// deterministic primality test for n < 2^64.
// Assume that small factors are already processed, assume n > 2
bool uint64_is_prime(uint64_t n)
{
    uint64_t d = n / 2;
    uint64_t s = uint64_tzcnt(d);
    d >>= s++;

    if (n < 1373653)
        return uint64_witness(n, s, d, 2) && uint64_witness(n, s, d, 3);
    if (n < 9080191)
        return uint64_witness(n, s, d, 31) && uint64_witness(n, s, d, 73);
    if (n < 4759123141)
        return uint64_witness(n, s, d, 2) && uint64_witness(n, s, d, 7) && uint64_witness(n, s, d, 61);
    if (n < 1122004669633)
        return uint64_witness(n, s, d, 2) && uint64_witness(n, s, d, 13) && uint64_witness(n, s, d, 23) &&
               uint64_witness(n, s, d, 1662803);
    if (n < 2152302898747)
        return uint64_witness(n, s, d, 2) && uint64_witness(n, s, d, 3) && uint64_witness(n, s, d, 5) &&
               uint64_witness(n, s, d, 7) && uint64_witness(n, s, d, 11);
    if (n < 3474749660383)
        return uint64_witness(n, s, d, 2) && uint64_witness(n, s, d, 3) && uint64_witness(n, s, d, 5) &&
               uint64_witness(n, s, d, 7) && uint64_witness(n, s, d, 11) && uint64_witness(n, s, d, 13);
    if (n < 341550071728321)
        return uint64_witness(n, s, d, 2) && uint64_witness(n, s, d, 3) && uint64_witness(n, s, d, 5) &&
               uint64_witness(n, s, d, 7) && uint64_witness(n, s, d, 11) && uint64_witness(n, s, d, 13) &&
               uint64_witness(n, s, d, 17);
    if (n < 3825123056546413051)
        return uint64_witness(n, s, d, 2) && uint64_witness(n, s, d, 3) && uint64_witness(n, s, d, 5) &&
               uint64_witness(n, s, d, 7) && uint64_witness(n, s, d, 11) && uint64_witness(n, s, d, 13) &&
               uint64_witness(n, s, d, 17) && uint64_witness(n, s, d, 19) && uint64_witness(n, s, d, 23);
    // n < 318665857834031151167461
    return uint64_witness(n, s, d, 2) && uint64_witness(n, s, d, 3) && uint64_witness(n, s, d, 5) &&
           uint64_witness(n, s, d, 7) && uint64_witness(n, s, d, 11) && uint64_witness(n, s, d, 13) &&
           uint64_witness(n, s, d, 17) && uint64_witness(n, s, d, 19) && uint64_witness(n, s, d, 23) &&
           uint64_witness(n, s, d, 29) && uint64_witness(n, s, d, 31) && uint64_witness(n, s, d, 37);
}

static sieve_t mpz_composite_sieve(mpz_t n)
{
    // detect small 64-bit numbers
    unsigned sz = mpz_sizeinbase(n, 2);
    if (sz <= 64)
    {
        uint64_t a = mpz_get_ui(n);
        sieve_t sv = uint64_composite_sieve(a);
        return sv;
    }
    else
    {
        // large number, do the modular reduction in 2 steps
        // step 1 :
        //   reduce by a multiple of small factors
        // step 2:
        //    divisibility is based on Barrett modular reductions by constants

        uint64_t a;

        // 2^60-1 is divisible by 3,5,7,11,13,31,41,61,151 ...
        a = mpz_mod_mersenne(n, 60);
        if ((uint64_t)(a * 0xaaaaaaaaaaaaaaabull) <= 0x5555555555555555ull)
            return COMPOSITE_FOR_SURE; // divisible by 3
        if ((uint64_t)(a * 0xcccccccccccccccdull) <= 0x3333333333333333ull)
            return COMPOSITE_FOR_SURE; // divisible by 5
        if ((uint64_t)(a * 0x6db6db6db6db6db7ull) <= 0x2492492492492492ull)
            return COMPOSITE_FOR_SURE; // divisible by 7
        if ((uint64_t)(a * 0x2e8ba2e8ba2e8ba3ull) <= 0x1745d1745d1745d1ull)
            return COMPOSITE_FOR_SURE; // divisible by 11
        if ((uint64_t)(a * 0x4ec4ec4ec4ec4ec5ull) <= 0x13b13b13b13b13b1ull)
            return COMPOSITE_FOR_SURE; // divisible by 13
        if ((uint64_t)(a * 0xef7bdef7bdef7bdfull) <= 0x0842108421084210ull)
            return COMPOSITE_FOR_SURE; // divisible by 31
        if ((uint64_t)(a * 0x8f9c18f9c18f9c19ull) <= 0x063e7063e7063e70ull)
            return COMPOSITE_FOR_SURE; // divisible by 41
        if ((uint64_t)(a * 0x4fbcda3ac10c9715ull) <= 0x04325c53ef368eb0ull)
            return COMPOSITE_FOR_SURE; // divisible by 61
        if ((uint64_t)(a * 0x6fe4dfc9bf937f27ull) <= 0x01b2036406c80d90ull)
            return COMPOSITE_FOR_SURE; // divisible by 151

        // 2^56-1 is divisible by 3, 5, 17, 29, 43, 113, 127, .....
        a = mpz_mod_mersenne(n, 56);
        if ((uint64_t)(a * 0xf0f0f0f0f0f0f0f1ull) <= 0x0f0f0f0f0f0f0f0full)
            return COMPOSITE_FOR_SURE; // divisible by 17
        if ((uint64_t)(a * 0x34f72c234f72c235ull) <= 0x08d3dcb08d3dcb08ull)
            return COMPOSITE_FOR_SURE; // divisible by 29
        if ((uint64_t)(a * 0x82fa0be82fa0be83ull) <= 0x05f417d05f417d05ull)
            return COMPOSITE_FOR_SURE; // divisible by 43
        if ((uint64_t)(a * 0x90fdbc090fdbc091ull) <= 0x0243f6f0243f6f02ull)
            return COMPOSITE_FOR_SURE; // divisible by 113
        if ((uint64_t)(a * 0x7efdfbf7efdfbf7full) <= 0x0204081020408102ull)
            return COMPOSITE_FOR_SURE; // divisible by 127

        // 2^36-1 is divisible by 3,5,7,19,37,73,109, ...
        a = mpz_mod_mersenne(n, 36);
        if ((uint64_t)(a * 0x86bca1af286bca1bull) <= 0x0d79435e50d79435ull)
            return COMPOSITE_FOR_SURE; // divisible by 19
        if ((uint64_t)(a * 0x14c1bacf914c1badull) <= 0x06eb3e45306eb3e4ull)
            return COMPOSITE_FOR_SURE; // divisible by 37
        if ((uint64_t)(a * 0x7e3f1f8fc7e3f1f9ull) <= 0x0381c0e070381c0eull)
            return COMPOSITE_FOR_SURE; // divisible by 73
        if ((uint64_t)(a * 0xa6c0964fda6c0965ull) <= 0x02593f69b02593f6ull)
            return COMPOSITE_FOR_SURE; // divisible by 109

        // 2^44-1 is divisible by 3, 5, 23, 89, .....
        a = mpz_mod_mersenne(n, 44);
        if ((uint64_t)(a * 0xd37a6f4de9bd37a7ull) <= 0x0b21642c8590b216ull)
            return COMPOSITE_FOR_SURE; // divisible by 23
        if ((uint64_t)(a * 0xf47e8fd1fa3f47e9ull) <= 0x02e05c0b81702e05ull)
            return COMPOSITE_FOR_SURE; // divisible by 89

        // 2^23-1 is divisible by 47, .....
        a = mpz_mod_mersenne(n, 23);
        if ((uint64_t)(a * 0x51b3bea3677d46cfull) <= 0x0572620ae4c415c9ull)
            return COMPOSITE_FOR_SURE; // divisible by 47

        // 2^52-1 is divisible by 3, 5, 53, 157, .....
        a = mpz_mod_mersenne(n, 52);
        if ((uint64_t)(a * 0x21cfb2b78c13521dull) <= 0x04d4873ecade304dull)
            return COMPOSITE_FOR_SURE; // divisible by 53

        // next small prime to test 59
    }

    // no trivial small factor detected
    return UNDECIDED; // might be prime
}

// BPSW test
// find Lucas parameters where Jacobi(D, n) == -1
// Note that when d < 0 , kronecker(d | n) == kronecker(-1 | n) * jacobi( -d | n)
// Note that when d > 0, jacobi(d | n) == jacobi( d | n % (4 * d))
// run Lucas sequence L(D, 1, 1)
static bool uint64_lucas(uint64_t n, bool verbose = false)
{
    int64_t d = 5;
    int j;
    int sgn = 1;

    // process the sequence 5, -7, 9, -11, 13, -15 .....
    while (1)
    {
        j = uint64_jacobi(d, n % (4 * d));
        if (j == 0)
        {
            return false; // composite
        }
        j *= (sgn < 0) ? uint64_minus_one_kronecker(n) : 1;
        if (j == -1)
        {
            break; // quadratic non-residue
        }
        d += 2;
        sgn = -sgn;
    }

    if (verbose)
    {
        printf("Test lucas sequence with D=%s%lu\n", sgn < 0 ? "-" : "", d);
    }

    // Lucas sequence L(sgn*D, U=1, V=1)
    uint64_t D = d;
    uint64_t e = n + 1;
    uint64_t nU;
    uint64_t bits = uint64_log_2(e);
    uint64_t tmp;
    uint128_t ttmp;
    uint64_t U = 1;
    uint64_t V = 1;
    while (bits--)
    {
        // U, V  = U * V, (U * U * d + V * V ) /2
        nU = (sgn < 0) ? n - U : U;
        ttmp = (uint128_t)nU * U;
        U = mulmod(U, V, n);

        tmp = longlongmod(ttmp, n);
        ttmp = (uint128_t)tmp * D + (uint128_t)V * V;
        ttmp += (ttmp & 1) ? n : 0;
        V = longlongmod(ttmp >> 1, n);
        if ((e >> bits) & 1)
        {
            // U, V  = (U + V) / 2, (U * d + V ) / 2
            nU = (sgn < 0) ? n - U : U;
            ttmp = (uint128_t)nU * D + V;
            U = U + V;
            U += (U & 1) ? n : 0;
            U = U >> 1;
            U -= (U >= n) ? n : 0;

            ttmp += (ttmp & 1) ? n : 0;
            V = longlongmod(ttmp >> 1, n);
        }
    }
    return (U == 0);
}

static bool mpz_lucas(mod_precompute_t *p, bool verbose = false)
{
    int64_t d = 5;
    int j;
    int sgn = 1;
    bool r = true;
    uint64_t nn;
    mpz_t ignore;
    mpz_init(ignore);

    // process the sequence 5, -7, 9, -11, 13, -15 .....
    while (1)
    {
        nn = mpz_mod_ui(ignore, p->m, 4 * d);
        j = uint64_jacobi(d, nn);
        if (j == 0)
        {
            mpz_clear(ignore);
            return false; // composite
        }
        j *= sgn < 0 ? mpz_minus_one_kronecker(p->m) : 1;
        if (j == -1)
        {
            break; // quadratic non-residue
        }
        d += 2;
        sgn = -sgn;
    }
    mpz_clear(ignore);

    if (verbose)
    {
        printf("Test lucas sequence with D=%s%lu\n", sgn < 0 ? "-" : "+", d);
    }

    mpz_t e, tmp, U, V;
    mpz_inits(e, tmp, U, V, 0);
    d *= sgn;
    mpz_set_ui(U, 1);
    mpz_set_ui(V, 1);
    mpz_add_ui(e, p->m, 1);
    mpz_mod_to_montg(U, p);
    mpz_mod_to_montg(V, p);

    // Lucas sequence L(sgn*D, U=1, V=1)
    uint64_t bits = mpz_sizeinbase(e, 2) - 1;
    while (bits--)
    {
        // U, V  = U * V, (U * U * d + V * V ) / 2
        mpz_mul(tmp, U, U);
        mpz_mul_si(tmp, tmp, d);
        mpz_mul(U, U, V);
        mpz_mul(V, V, V);
        mpz_add(V, V, tmp);
        mpz_mod_div2(V, p);

        if (mpz_tstbit(e, bits))
        {
            // U, V  = (U + V) / 2, (U * d + V ) / 2
            mpz_mul_si(tmp, U, d);
            mpz_add(U, U, V);
            mpz_mod_div2(U, p);

            mpz_add(V, tmp, V);
            mpz_mod_div2(V, p);
        }
        mpz_mod_positive_reduce(U, tmp, p);
        mpz_mod_fast_reduce(U, tmp, p);
        mpz_mod_positive_reduce(V, tmp, p);
        mpz_mod_fast_reduce(V, tmp, p);
    }

    mpz_mod_from_montg(U, tmp, p);
    mpz_mod_from_montg(V, tmp, p);
    mpz_mod_slow_reduce(U, p->m);
    mpz_mod_slow_reduce(V, p->m);
    r = mpz_cmp_ui(U, 0) == 0;
    mpz_clears(e, tmp, U, V, 0);

    return r;
}

static bool uint64_simple_primality(uint64_t n, bool verbose = false)
{
    if (n >> 61)
    {
        // the simple test might overflow for numbers > 61 bits along
        // the inner additions.
        // Better use another slower deterministic test for numbers <= 60 bits
        // More precise constraint is n < 2^64/6
        mpz_t v;
        mpz_init_set_ui(v, n);
        bool r = mpz_simple_primality(v, verbose);
        mpz_clear(v);
        return r;
    }

    if (n < 2)
    {
        if (verbose)
        {
            printf("Number is < 2, not prime\n");
        }
	return false;
    }

    if ((n & 1) == 0)
    {
        if (verbose)
        {
            printf("Number is even\n");
        }
        return n == 2; // even
    }

    // sieve small numbers with small factors
    sieve_t sv = uint64_composite_sieve(n);
    switch (sv)
    {
    case COMPOSITE_FOR_SURE:
        if (verbose)
        {
            printf("Number has a small factor\n");
        }
        return false; // composite
    case PRIME_FOR_SURE:
        if (verbose)
        {
            printf("Small number has no small factor\n");
        }
        return true; // prime
    case UNDECIDED:
    default:
        break;
    }

    uint64_t d = n / 2;
    uint64_t s = uint64_tzcnt(d);
    d >>= s++;

    bool b = uint64_witness(n, s, d, 2);
    if (b != true)
    {
        if (verbose)
        {
            printf("Number is not a 2-SPRP\n");
        }
        return false; // composite
    }
    b = is_perfect_square(n);
    if (b == true)
    {
        if (verbose)
        {
            printf("Number is a perfect square\n");
        }
        return false; // composite
    }
    b = uint64_lucas(n, verbose);
    if (b != true)
    {
        if (verbose)
        {
            printf("Number is not a Lucas PRP\n");
        }
        return false; // composite
    }
    // prime (BPSW proven to 2^64 and higher, no known countereaxample)
    return true;
}

bool mpz_simple_primality(mpz_t n, bool verbose)
{
    if (verbose)
    {
        gmp_printf("Testing a %lu digits number\n", mpz_sizeinbase(n, 10));
    }

    if (mpz_cmp_ui(n, 1ull << 61) < 0)
    {
        // the simple test will run in 64 bits calculations
        return uint64_simple_primality(mpz_get_ui(n), verbose);
    }

    if (mpz_tstbit(n, 0) == 0)
    {
        if (verbose)
        {
            printf("Number is even\n");
        }
        return (mpz_cmp_ui(n, 2) == 0); // even
    }

    // detects small primes, small composites
    // detects smooth composites
    sieve_t sv = mpz_composite_sieve(n);
    switch (sv)
    {
    case COMPOSITE_FOR_SURE:
        if (verbose)
        {
            printf("Number has a small factor\n");
        }
        return false; // composite
    case PRIME_FOR_SURE:
        if (verbose)
        {
            printf("Small number has no small factor\n");
        }
        return true; // prime
    case UNDECIDED:
    default:
        break;
    }

    mpz_t md, ma;
    mpz_inits(md, ma, 0);
    mpz_set_ui(ma, 2);
    mpz_div_2exp(md, n, 1);
    uint64_t s = mpz_scan1(md, 0);
    mpz_div_2exp(md, md, s++);

    bool b = mpz_witness(n, s, md, ma);
    mpz_clears(md, ma, 0);
    if (b != true)
    {
        if (verbose)
        {
            printf("Number is not a 2-SPRP\n");
        }
        return false; // composite
    }
    else
    {
        if (verbose)
        {
            printf("Number is a 2-SPRP\n");
        }
    }

    b = mpz_is_perfect_square(n);
    if (b == true)
    {
        if (verbose)
        {
            printf("Number is a perfect square\n");
        }
        return false; // composite
    }

    mod_precompute_t *pcpt = mpz_mod_precompute(n, verbose);
    bool r = mpz_lucas(pcpt, verbose);
    mpz_mod_uncompute(pcpt);

    if (verbose && r == false)
    {
        printf("Number is composite\n");
    }
    if (verbose && r == true)
    {
        printf("Number is a Lucas-PRP\n");
        printf("Number passed all tests and is unlikely a composite one\n");
    }

    return r;
}

// ------------------------------------------------------------------------------
// Simple foolguard unit tests
// ------------------------------------------------------------------------------

void simple_primality_self_test(void)
{
    uint64_t a, b, m;
    uint128_t aa;

    // ---------------------------------------------------------------------------------
    printf("Modular arithmetic sanity check ...\n");

    m = 0x8765432187654321ull;
    a = 0xffffffffffffffffull;
    b = longmod(0, a, m);
    assert(b == 8690466094656961758ull);
    aa = a;
    b = longlongmod(aa, m);
    assert(b == 8690466094656961758ull);

    b = longmod(1, a, m);
    assert(b == 7624654210261333660ull);
    aa = ((uint128_t)1 << 64) + a;
    b = longlongmod(aa, m);
    assert(b == 7624654210261333660ull);

    // ---------------------------------------------------------------------------------
    printf("Fast reduction mod 2^b-1 ...\n");
    mpz_t ma, mb;
    mpz_inits(ma, mb, 0);
    mpz_set_ui(ma, 11);
    for (unsigned b = 1; b < 10; b++)
    {
        mpz_mul(ma, ma, ma);
    }
    for (unsigned b = 1; b < 64; b++)
    {
        uint64_t mm = (1ull << b) - 1;
        uint64_t r = mpz_mod_mersenne(ma, b);
        assert(r % mm == mpz_mod_ui(mb, ma, mm));
    }

    // ---------------------------------------------------------------------------------
    printf("Sieve (uint64)\n");
    assert(uint64_composite_sieve(101) == PRIME_FOR_SURE);
    assert(uint64_composite_sieve(1661) == COMPOSITE_FOR_SURE);
    assert(uint64_composite_sieve(281474976710677ull) == UNDECIDED);

    printf("Sieve (mpz)\n");
    // 2^127 - 1 (a prime)
    mpz_init_set_ui(ma, 1);
    mpz_mul_2exp(ma, ma, 127);
    mpz_sub_ui(ma, ma, 1);
    assert(mpz_composite_sieve(ma) == UNDECIDED);
    // 2^127 + 1
    mpz_add_ui(ma, ma, 2);
    assert(mpz_composite_sieve(ma) == COMPOSITE_FOR_SURE);

    // ---------------------------------------------------------------------------------
    printf("Slow modular reduction\n");
    mpz_t x;
    mpz_init(x);
    mpz_set_ui(ma, 0x1);
    mpz_mul_2exp(ma, ma, 127);
    mpz_add_ui(ma, ma, 0x1d);
    // verify 2*(modulus +1) == 2
    mpz_add_ui(mb, ma, 0x1);
    mpz_add(x, mb, mb);
    mpz_mod_slow_reduce(x, ma);
    assert(mpz_cmp_ui(x, 2) == 0);

    // ---------------------------------------------------------------------------------
    printf("Fast modular reduction\n");
    // verify generic modulus
    mpz_set_ui(ma, 0x1cc);
    mod_precompute_t *p = mpz_mod_precompute(ma);
    assert(p->special_case == false);
    mpz_set_ui(mb, 0x2000ull * 0x1cc);
    mpz_mod_fast_reduce(mb, x, p);
    mpz_mod_slow_reduce(mb, ma);
    assert(mpz_get_ui(mb) == 0);
    // clears temp structure
    mpz_mod_uncompute(p);

    // verify proth modulus
    mpz_t mx, mtt;
    mpz_init(mx);
    mpz_init(mtt);
    mpz_set_ui(ma, 0xcdefabcdcdefabcdull);
    mpz_mul_2exp(ma, ma, 64);
    mpz_add_ui(ma, ma, 1);
    p = mpz_mod_precompute(ma);
    assert(p->special_case == true);
    assert(p->montg == true);
    assert(p->proth == true);
    assert(p->n2 == 64);
    assert(p->n == 128);
    mpz_set_ui(ma, 0xabcdef01abcdef01ull);
    mpz_mul(ma, ma, ma);
    mpz_set_ui(mb, 0x1234567812345678ull);
    mpz_mul(mb, mb, mb);
    mpz_mul(x, ma, mb);
    mpz_mod(x, x, p->m);
    mpz_mod_to_montg(ma, p);
    mpz_mod_to_montg(mb, p);
    mpz_mul(mx, ma, mb);
    mpz_mod_fast_reduce(mx, mtt, p);
    mpz_mod_from_montg(mx, mtt, p);
    mpz_mod_slow_reduce(mx, p->m);
    assert(mpz_cmp(x, mx) == 0);
    // clears temp structure
    mpz_clear(mx);
    mpz_mod_uncompute(p);

    // verify (modulus + 0x17)^2 == 17*17
    mpz_set_ui(ma, 1);
    mpz_mul_2exp(ma, ma, 127);
    p = mpz_mod_precompute(ma);
    assert(p->special_case == false);
    mpz_add_ui(mb, ma, 17);
    mpz_mul(x, mb, mb);
    mpz_mod_fast_reduce(x, mtt, p);
    mpz_mod_slow_reduce(x, ma);
    assert(mpz_get_ui(x) == 17 * 17);

    // verify (modulus + 0x19)^4 == 17*17*17*17
    mpz_add_ui(mb, ma, 19);
    mpz_mul(x, mb, mb);
    mpz_mul(x, x, x);
    mpz_mod_fast_reduce(x, mtt, p);
    mpz_mod_slow_reduce(x, ma);
    assert(mpz_get_ui(x) == 19 * 19 * 19 * 19);

    // clears temp structure
    mpz_mod_uncompute(p);
    p = 0;
    mpz_clear(x);

    // ---------------------------------------------------------------------------------
    printf("Small primes (uint64)\n");
    assert(uint64_simple_primality(16777259ull) == true);
    assert(uint64_simple_primality(281474976710677ull) == true);

    // ---------------------------------------------------------------------------------
    printf("Small composites (uint64)\n");
    assert(uint64_simple_primality(16777265ull) == false);
    assert(uint64_simple_primality(281474976710683ull) == false);

    // ---------------------------------------------------------------------------------
    printf("Small primes (uint64 sanity check)\n");

    bool res = uint64_simple_primality(31, false);
    assert(res == true);

    res = uint64_simple_primality(65537, false);
    assert(res == true);

    // ---------------------------------------------------------------------------------
    printf("Small primes (mpz sanity check)\n");
    mpz_t ms, me, mtmp;
    mpz_inits(ms, me, mtmp, 0);

    // quick tests mod 31
    mpz_set_ui(ma, 31);
    p = mpz_mod_precompute(ma);

    res = mpz_simple_primality(ma);
    assert(res == true);

    mpz_mod_uncompute(p);

    // quick tests mod 2^89+29
    mpz_set_ui(ma, 1);
    mpz_mul_2exp(ma, ma, 89);
    mpz_add_ui(ma, ma, 29);
    p = mpz_mod_precompute(ma);

    res = mpz_simple_primality(ma);
    assert(res == true);

    mpz_mod_uncompute(p);

    // quick tests mod 21*2^128+1
    mpz_set_ui(ma, 21);
    mpz_mul_2exp(ma, ma, 128);
    mpz_add_ui(ma, ma, 1);
    p = mpz_mod_precompute(ma);
    assert(p->proth == true);

    res = mpz_simple_primality(ma);
    assert(res == true);

    mpz_mod_uncompute(p);
    mpz_clears(ms, me, mtmp, 0);

    // ---------------------------------------------------------------------------------
    uint32_t smallq[] = {
        1,   1,   1,   3,   1,   5,   3,   3,   1,  9,   7,   5,   3,   17,  27,  3,   1,   29,  3,   21,  7,   17,
        15,  9,   43,  35,  15,  29,  3,   11,  3,  11,  15,  17,  25,  53,  31,  9,   7,   23,  15,  27,  15,  29,
        7,   59,  15,  5,   21,  69,  55,  21,  21, 5,   159, 3,   81,  9,   69,  131, 33,  15,  135, 29,  13,  131,
        9,   3,   33,  29,  25,  11,  15,  29,  37, 33,  15,  11,  7,   23,  13,  17,  9,   75,  3,   171, 27,  39,
        7,   29,  133, 59,  25,  105, 129, 9,   61, 105, 7,   255, 277, 81,  267, 81,  111, 39,  99,  39,  33,  147,
        27,  51,  25,  281, 43,  71,  33,  29,  25, 9,   451, 41,  277, 165, 67,  27,  7,   29,  51,  17,  169, 39,
        67,  27,  27,  33,  85,  155, 87,  155, 37, 5,   217, 5,   175, 27,  85,  51,  91,  69,  147, 45,  253, 95,
        27,  15,  45,  69,  97,  299, 7,   107, 19, 21,  117, 141, 85,  83,  87,  147, 49,  129, 105, 77,  7,   9,
        427, 75,  87,  309, 15,  165, 49,  215, 27, 159, 205, 303, 57,  35,  129, 5,   133, 65,  27,  35,  21,  107,
        15,  101, 235, 351, 67,  15,  7,   581, 33, 203, 375, 47,  33,  71,  57,  75,  7,   251, 423, 129, 163, 185,
        217, 81,  49,  189, 735, 119, 735, 483, 3,  249, 67,  105, 357, 431, 43,  81,  25,  249, 67,  29,  115, 261,
        69,  59,  133, 315, 337, 63,  81,  119, 25, 65,  421, 39,  79,  95,  297, 155, 73,  435, 223, 0};

    printf("Medium primes (mpz)\n");
    for (int j = 0; smallq[j]; j++)
    {
        // primes (2^j + q) must be catched
        mpz_set_ui(ma, 1);
        mpz_mul_2exp(ma, ma, j);
        mpz_add_ui(ma, ma, smallq[j]);
        bool res = mpz_simple_primality(ma, false);
        if (!res)
        {
            gmp_printf("prime 0x%Zx\n", ma);
            printf("error at %d %d\n", (int)j, (int)smallq[j]);
            assert(res == true);
        }
    }

    // ---------------------------------------------------------------------------------
    uint32_t smallp[] = {2,  3,  5,  7,  11, 13, 17, 19, 23, 29, 31, 37,  41,  43,
                         47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 0};
    printf("Medium composites (mpz)\n");
    for (int j = 0; smallp[j]; j++)
    {
        // Composites p * (2^127-1) must be catched
        mpz_set_ui(ma, 1);
        mpz_mul_2exp(ma, ma, 127);
        mpz_sub_ui(ma, ma, 1);
        mpz_mul_ui(ma, ma, smallp[j]);
        bool res = mpz_simple_primality(ma);
        if (res)
        {
            printf("error at %d %d\n", (int)j, (int)smallp[j]);
            assert(res == false);
        }
    }

    // ---------------------------------------------------------------------------------
    printf("Large primes (mpz)\n");

    // large proth prime 333*2^448+1
    mpz_set_ui(ma, 333);
    mpz_mul_2exp(ma, ma, 448);
    mpz_add_ui(ma, ma, 1);
    assert(mpz_simple_primality(ma) == true);

    // Large Riesel prime 100000000000037*2^5982-1
    mpz_set_ui(ma, 1);
    mpz_mul_2exp(ma, ma , 5982);
    mpz_mul_ui(ma, ma , 100000000000037ul);
    mpz_sub_ui(ma, ma, 1ul);
    assert(mpz_simple_primality(ma) == true);

    // 11111...6442446...11111 (1001-digits) The smallest zeroless titanic palindromic prime
    // https://t5k.org/curios/page.php?number_id=3797
    char titanic[1002];
    memset(titanic, '1', 1001);
    titanic[497] = '6';
    titanic[498] = '4';
    titanic[499] = '4';
    titanic[500] = '2';
    titanic[501] = '4';
    titanic[502] = '4';
    titanic[503] = '6';
    titanic[1001] = 0;
    mpz_set_str(ma, titanic, 10);
    // gmp_printf("%Zd\n", ma);
    assert(mpz_simple_primality(ma) == true);

    // 11111...0...3781 (1001-digits) The smallest Cyclops titanic prime.
    // https://t5k.org/curios/page.php?number_id=18967
    memset(titanic, '1', 1001);
    titanic[500] = '0';
    titanic[997] = '3';
    titanic[998] = '7';
    titanic[999] = '8';
    titanic[1000] = '1';
    titanic[1001] = 0;
    mpz_set_str(mb, titanic, 10);
    assert(mpz_simple_primality(mb) == true);

    // ---------------------------------------------------------------------------------
    printf("Large composites (mpz)\n");
    // a semiprime out of the 2 previous tests, no small factors.
    mpz_mul(ma, mb, ma);
    assert(mpz_simple_primality(ma) == false);

    // a large square
    mpz_mul(ma, mb, mb);
    assert(mpz_simple_primality(ma) == false);

    // a large cube
    mpz_mul(ma, ma, mb);
    assert(mpz_simple_primality(ma) == false);

    mpz_clears(ma, mb, 0);
}
