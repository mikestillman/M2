#include <M2/config.h>
#include <M2/gc-include.h>

#include "gmp_init.h"

// we override factory's routine so it doesn't install any gmp memory allocation functions
int initializeGMP()
{
   return 1;
}

/*
// Local Variables:
// compile-command: "echo \"make: Entering directory \\`$M2BUILDDIR/Macaulay2/d'\" && make -C $M2BUILDDIR/Macaulay2/d "
// End:
*/
