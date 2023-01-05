#ifndef _vectors_hpp_
#define _vectors_hpp_

#include <vector>
#include "aring-zzp-flint.hpp"
#include "Iterators.hpp"

class SparseVector;
class DenseVector;

using ZZpElement = M2::ARingZZpFlint::ElementType; // really just long.
using IndexType = int;

// I think this should be along the lines of VectorArithmetic where we store these
// as (void *) and then reinterpret_cast to the appropriate thing.
// however, we kept the components and elements separate.  I think making this a single
// class that works in the same way would be best.

// in the meantime, we define classes for dense vector and sparse vector below.

class SparseVector
{
private:
  std::vector<ZZpElement> mNonzeroElements;
  std::vector<IndexType> mColumns;
  IndexType mNumColumns;

public:

  using ConstIter = DiagonalIter<
    decltype(mColumns.cbegin()),
    decltype(mNonzeroElements.cbegin())
    >;
  using Iter = DiagonalIter<
    decltype(mColumns.cbegin()),
    decltype(mNonzeroElements.cbegin())
    >;

  ConstIter cbegin() const;
  ConstIter cend() const;
  Iter begin();
  Iter end();

};

inline SparseVector::ConstIter SparseVector::cbegin() const {
  return ConstIter(mColumns.cbegin(),
		   mNonzeroElements.cbegin());
}

inline SparseVector::ConstIter SparseVector::cend() const {
  return ConstIter(mColumns.cend(),
		   mNonzeroElements.cend());
}

inline SparseVector::Iter SparseVector::begin() {
  return Iter(mColumns.begin(),
              mNonzeroElements.begin());
}

inline SparseVector::ConstIter SparseVector::end() {
  return Iter(mColumns.end(),
              mNonzeroElements.end());
}

class DenseVector
{
private:
  std::vector<ZZpElement> mEntries;

public:
  using ConstIter = decltype(mEntries.cbegin());
  using Iter = decltype(mEntries.begin());

  void resize( size_t size ) { mEntries.resize(size); }
  void fill( const ZZpElement& element ) { std::fill(mEntries.begin(), mEntries.end(), element); }
  IndexType size() const { return mEntries.size(); }

  ZZpElement& operator[]( size_t pos ) { return mEntries[pos]; }
  const ZZpElement& operator[]( size_t pos ) const { return mEntries[pos]; }

  ConstIter cbegin() const { return mEntries.cbegin(); }
  ConstIter cend() const { return mEntries.cend(); }

  Iter begin() { return mEntries.begin(); }
  Iter end() { return mEntries.end(); }
};

#endif

// Local Variables:
// indent-tabs-mode: nil
// End:
