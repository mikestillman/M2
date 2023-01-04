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

  using ConstIter = DiagonalIter<
    decltype(mColumns.cbegin()),
    decltype(mNonzeroElements.cbegin())
    >;

  ConstIter cbegin() const;
  ConstIter cend() const;

};

inline SparseMatrixZZp::ConstRowIter SparseMatrixZZp::cbegin() const {
  return ConstIter(mColumns.cbegin(),
		   mNonzeroElements.cbegin());
}

inline SparseMatrixZZp::ConstRowIter SparseMatrixZZp::cend() const {
  return ConstIter(mColumns.cend(),
		   mNonzeroElements.cend());
}

class DenseVector
{
private:
  std::vector<ZZpElement> mEntries;
}

#endif

// Local Variables:
// indent-tabs-mode: nil
// End:
