// Parts taken from MathicGB copyright 2012 all rights reserved. MathicGB comes with ABSOLUTELY
// NO WARRANTY and is licensed as GPL v2.0 or later - see LICENSE.txt.
// Changes Copyright 2021 Michael Stillman.

#ifndef __classic_gb_alg_hpp__
#define __classic_gb_alg_hpp__

#include <functional>

namespace mgbF4 {
  class Reducer;
  class Basis;

  struct ClassicGBAlgParams {
    Reducer* reducer;
    int monoLookupType;
    bool preferSparseReducers;
    size_t sPairQueueType;
    
    unsigned int breakAfter;
    unsigned int printInterval;
    unsigned int sPairGroupSize;
    size_t reducerMemoryQuantum;
    bool useAutoTopReduction;
    bool useAutoTailReduction;
    std::function<bool(void)> callback;
  };
  
  Basis computeGBClassicAlg(Basis&& inputBasis, ClassicGBAlgParams params);
  Basis computeModuleGBClassicAlg(Basis&& inputBasis, ClassicGBAlgParams params);
};

#endif

// Local Variables:
// compile-command: "make -C $M2BUILDDIR/Macaulay2/e "
// indent-tabs-mode: nil
// End:
