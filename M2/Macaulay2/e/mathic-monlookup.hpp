#ifndef M2_MATHIC_MONLOOKUP_GUARD
#define M2_MATHIC_MONLOOKUP_GUARD

// This is an experiment.  Use exponent vectors, int entries.

#include "mathic.h"
#include "ntuple.hpp"

using Exponent = int;

#if 0
class Mono;
class MonoRef;
class MonoPtr;
class ConstMonoPtr;
class ConstMonoRef;

class ConstMonoPtr {
public:
  ConstMonoPtr(): mMono(nullptr) {}
  ConstMonoPtr(std::nullptr_t): mMono(nullptr) {}
  ConstMonoPtr(const ConstMonoPtr& mono): mMono(rawPtr(mono)) {}
  
  ConstMonoPtr operator=(const ConstMonoPtr& mono) {
    mMono = mono.mMono;
    return *this;
  }
  
  ConstMonoRef operator*() const {return ConstMonoRef(*this);}
private:
  friend class MonoMonoid;
  
  const Exponent* internalRawPtr() const {return mMono;}
  ConstMonoPtr(const Exponent* mono): mMono(mono) {}
  
  const Exponent* mMono;
};

class ConstMonoRef {
public:
  ConstMonoRef(const ConstMonoRef& mono): mMono(mono.ptr()) {}
  ConstMonoRef(const Mono& mono): mMono(mono.ptr()) {
    MATHICGB_ASSERT(!mono.isNull());
  }
  
  ConstMonoPtr ptr() const {return mMono;}
  ConstMonoPtr operator&() const {return ptr();}
  
  MonoRef castAwayConst() const {return MonoRef(mMono.castAwayConst());}
  
private:
  void operator=(const MonoRef&) = delete; // not available
  //  friend class MonoMonoid;
  
  ConstMonoRef(ConstMonoPtr mono): mMono(mono) {}
  const Exponent* internalRawPtr() const {return internalRawPtr(mMono);}
  
  const ConstMonoPtr mMono;
};

class MonoRef {
public:
  MonoRef(const MonoRef& mono): mMono(mono.ptr()) {}
  
  MonoPtr ptr() const {return mMono;}
  MonoPtr operator&() const {return ptr();}
  
  operator ConstMonoRef() const {return *static_cast<ConstMonoPtr>(mMono);}
  
private:
  void operator=(const MonoRef&); // not available
  //  friend class MonoMonoid;
  friend class ConstMonoRef;
  
  MonoRef(MonoPtr mono): mMono(mono) {}
  Exponent* internalRawPtr() const {return rawPtr(mMono);}
  
  const MonoPtr mMono;
};


class MonoPtr {
public:
  MonoPtr(): mMono(nullptr) {}
  MonoPtr(std::nullptr_t): mMono(nullptr) {}
  MonoPtr(const MonoPtr& mono): mMono(mono.mMono) {}
  
  MonoPtr operator=(const MonoPtr& mono) {
    mMono = mono.mMono;
    return *this;
  }
  
  MonoRef operator*() const {return MonoRef(*this);}
  
  bool isNull() const {return mMono == nullptr;}
  void toNull() {mMono = nullptr;}
  
  bool operator==(std::nullptr_t) const {return isNull();}
  bool operator!=(std::nullptr_t) const {return !isNull();}
  
  operator ConstMonoPtr() const {return ConstMonoPtr(mMono);}
private:
  friend class MonoMonoid;
  friend class ConstMonoPtr;
  
  Exponent* internalRawPtr() const {return mMono;}
  MonoPtr(Exponent* mono): mMono(mono) {}
  
  Exponent* mMono;
};

class Mono {
};
#endif

class MathicMonomialLookup
{
  using Data = int;

  static const bool DM = true;
  static const bool AR = true;
  
  // template parameters here: DM, AR (divmask, allow removals)
  class Configuration {
  public:
    Configuration(int nvars): mNumVars(nvars) {}
    
    using ConstMonoRef = const int*;
    using ConstMonoPtr = const int*;
    using Exponent = int;
    using Monomial = const int*; // ConstMonoRef

    class Entry {
    public:
      Entry(): mEntry() {}

      template<class D>
      Entry(ConstMonoRef mono, D&& data):
        mEntry(mono, std::forward<D>(data)) {}

      ConstMonoRef mono() const {return mEntry.first;}
      const Data& data() const {return mEntry.second;}
      Data& data() {return mEntry.second;}

    private:
      // Store in a std::pair so that if Data has no members then no space
      // will be used on it. Here we are depending on std::pair to be using
      // the empty base class optimization.
      std::pair<ConstMonoPtr, Data> mEntry;
    };

    Exponent getExponent(const Monomial& m, size_t var) const {
      return m[var];
    }

    Exponent getExponent(const Entry& e, size_t var) const {
      return e.mono()[var];
    }

    bool divides(const Monomial& a, const Monomial& b) const {
      return ntuple::divides(mNumVars, a, b);
    }

    bool divides(const Entry& a, const Monomial& b) const {
      return divides(a.mono(), b);
    }

    bool divides(const Monomial& a, const Entry& b) const {
      return divides(a, b.mono());
    }

    bool divides(const Entry& a, const Entry& b) const {
      return divides(a.mono(), b.mono());
    }

    bool getSortOnInsert() const {return false;}
    template<class A, class B>
    bool isLessThan(const A& a, const B& b) const {
      M2_ASSERT(false);
      return false;
    }

    size_t getVarCount() const {return mNumVars;}

    static const bool UseTreeDivMask = DM;
    static const bool UseLinkedList = false;
    static const bool UseDivMask = DM;
    static const size_t LeafSize = 1;
    static const bool PackedTree = true;
    static const bool AllowRemovals = AR;

    bool getUseDivisorCache() const {return true;}
    bool getMinimizeOnInsert() const {return false;}

    bool getDoAutomaticRebuilds() const {return UseDivMask;}
    double getRebuildRatio() const {return 0.5;}
    size_t getRebuildMin() const {return 50;}

  private:
    int mNumVars;
  };

};
#endif

/*
// Local Variables:
// compile-command: "make -C $M2BUILDDIR/Macaulay2/e "
// indent-tabs-mode: nil
// End:
*/
