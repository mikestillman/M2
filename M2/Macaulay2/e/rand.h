// Copyright 2008 by Michael Stillman

#ifndef _rand_h_
#define _rand_h_

#include "engine-includes.hpp"

#if defined(__cplusplus)
extern "C" {
#endif

  void rawRandomInitialize();

  void rawSetRandomSeed(gmp_ZZ newseed);

  void rawSetRandomMax(gmp_ZZ);

  unsigned long rawRandomULong(unsigned long max);
  /* generate a random number in the range 0..max-1 */

  int32_t rawRandomInt(int32_t max);
  /* generate a random number in the range 0..max-1 */

  void rawRandomInteger(mpz_ptr result, mpz_srcptr maxN);
  /* if height is the null pointer, use the default height */

  void rawRandomQQ(mpq_ptr result, mpz_srcptr height);
  /* returns random a/b, where 1 <= b <= height, 1 <= a <= height */
  /* if height is the null pointer, use the default height */

  void rawSetRandomQQ(mpq_ptr result, gmp_ZZ height);
  /* sets result = random a/b, where 1 <= b <= height, 1 <= a <= height */
  /* if height is the null pointer, use the default height */

  gmp_RR rawRandomRR(unsigned long prec);
  /* returns a uniformly distributed random real with the given precision, in range [0.0,1.0] */

  void rawRandomMpfr(mpfr_t result, unsigned long precision);

  gmp_CC rawRandomCC(unsigned long prec);

#if defined(__cplusplus)
}
#endif

#endif

// Local Variables:
// compile-command: "make -C $M2BUILDDIR/Macaulay2/e "
// indent-tabs-mode: nil
// End:
