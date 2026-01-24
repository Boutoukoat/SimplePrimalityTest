#pragma once

// -----------------------------------------------------------------------
// Cubic primality test
//
// mpz_simple_primality():
//    true: composite for sure
//    false: might be prime
//
// simple_primality_self_test()
//    simplified unit tests to detect a possible compiler/platform issue.
//    assert when fail (this should not happen).
// -----------------------------------------------------------------------

#include "gmp.h"
#include <stdbool.h>

bool mpz_simple_primality(mpz_t v, bool verbose = false);
void simple_primality_self_test(void);
