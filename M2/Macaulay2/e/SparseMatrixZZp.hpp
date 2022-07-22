#ifndef _sparse_matrix_ZZp_hpp_
#define _sparse_matrix_ZZp_hpp_

#include <vector>
#include <tuple>
#include <iostream>
#include "aring-zzp-flint.hpp"

using ZZpElement = M2::ARingZZpFlint::ElementType; // reallt just long.

class SparseMatrixZZpConstRowIterator;

class SparseMatrixZZp
{
  friend class SparseMatrixZZpConstRowIterator;
private:
  // Let e be the number of non-zero elements in the matrix
  const M2::ARingZZpFlint& mField;
  long mNumRows;
  long mNumColumns;
  std::vector<ZZpElement> mNonzeroElements; // 0..e-1
  std::vector<long> mColumns; // 0..e-1: mColumns[i] is the column number of of the i-th element in mNonzeroElements.
  std::vector<long> mRows; // 0..mNumRows // mRows[r]..mRows[r+1]-1 are the indices into mNonzeroElements, in this row.
  // Note: if none, mRows[r-1] == mRows[r].

  // Question: what is the format of a 0x0 matrix.
  // [[], [], [0]]

public:
  long numRows() const { return mNumRows; }
  long numColumns() const { return mNumColumns; }
  long numNonZeros() const { return mColumns.size(); }
  const M2::ARingZZpFlint& field() const {return mField; }

  /// Constructor: from a set of triples, IN LEX ORDER, (r,c,element).
  SparseMatrixZZp(const M2::ARingZZpFlint& F,
                  long nrows,
                  long ncols,
                  const std::vector<std::tuple<long,long,ZZpElement>>& triples
                  );

  SparseMatrixZZpConstRowIterator cbegin(int row) const;
  SparseMatrixZZpConstRowIterator cend(int row) const;

  void dump(std::ostream &o) const;
  void denseDisplay(std::ostream& o) const;

  SparseMatrixZZp transpose() const;

  static SparseMatrixZZp randomSparseMatrix(const M2::ARingZZpFlint& F,
                                            long nrows,
                                            long ncols,
                                            float density);
private:
  // Private initializer that sets sizes of the vectors, but does not initialize them?
  SparseMatrixZZp(long nrows,
                  long ncols,
                  long nentries,
                  const M2::ARingZZpFlint& F
                  );
};

class SparseMatrixZZpConstRowIterator
{
private:
  const SparseMatrixZZp& mMatrix;
  long mLoc;
public:
  SparseMatrixZZpConstRowIterator(const SparseMatrixZZp& A, long r)
    : mMatrix(A),
      mLoc(A.mRows[r])
  {
  }

  SparseMatrixZZpConstRowIterator(const SparseMatrixZZp& A, long r, int this_is_the_end_constructor)
    : mMatrix(A),
      mLoc(A.mRows[r+1])
  {
  }

  bool operator==(SparseMatrixZZpConstRowIterator j)
  {
    //TODO assert or test: same row, same matrix.
    return(mLoc == j.mLoc);
  }

  bool operator!=(SparseMatrixZZpConstRowIterator j)
  {
    //TODO assert or test: same row, same matrix.
    return(mLoc != j.mLoc);
  }
  
  SparseMatrixZZpConstRowIterator operator++()
  {
    mLoc++;
    return *this;
  }

  // operator*: returns (column, (nonzero) entry at given row and this column)
  std::pair<long, ZZpElement> operator*()
  {
    return {mMatrix.mColumns[mLoc], mMatrix.mNonzeroElements[mLoc]};
  }
};

inline SparseMatrixZZpConstRowIterator SparseMatrixZZp::cbegin(int row) const {
  return SparseMatrixZZpConstRowIterator(*this, row);
}

inline SparseMatrixZZpConstRowIterator SparseMatrixZZp::cend(int row) const {
  return SparseMatrixZZpConstRowIterator(*this, row, 0);
}

#if 0

class Permutation
{
public:
  // Operations:
private:
  std::vector<long> mPermutation;
};

class SparseVectorZZp
{
public:
  std::vector<long> mComponents;
  std::vector<ZZpElement> mElements;
  // or:
  std::vector<std::pair<long, ZZpElement>> mVector;
};


// TODO: also create a hash table class (r,c) => value.
class SparseMatrixTripleZZp
{
public:
  explicit operator(SparseMatrixZZp&);
  long numRows() const { return mNumRows; }
  long numColumns() const { return mNumColumns; }
private:
  // Let e be the number of non-zero elements in the matrix
  long mNumRows;
  long mNumColumns;

  // Should the following be a stdd::vector<struct of 3 items> ?
  std::vector<ZZpElement> mNonzeroElements; // 0..e-1
  std::vector<long> mRows; // 0..e-1
  std::vector<long> mColumns; // 0..e-1
};


namespace SparseMatrixOps
{
  // Constructors, change of representation
  // read/write to/from file

  // Transpose
  // Matrix/Vector Multiplication (v*A, A*B, ...)

  // sparse PLUQ decomposition:
  // Wiedemann
  // Lanczos
  // rank computation

  // finding a good matching...
};
#endif
#endif

// Local Variables:
// indent-tabs-mode: nil
// End:
