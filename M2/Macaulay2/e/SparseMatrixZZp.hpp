#ifndef _sparse_matrix_ZZp_hpp_
#define _sparse_matrix_ZZp_hpp_

#include <vector>
#include <tuple>
#include <iostream>
#include "aring-zzp-flint.hpp"

using ZZpElement = M2::ARingZZpFlint::ElementType; // reallt just long.

class Permutation
{
  // bool: is identity.
  // single std::vector<long>... possibly, or as a sparse set of operations.
};

template<typename Iter1, typename Iter2>
class DiagonalIter
{
  // Assumption: both iterators should point to valid memory simultaneously
  // even after each increment.
private:
  Iter1 mIter1;
  Iter2 mIter2;
  long mIndex;

  using Value1 = decltype(* mIter1);
  using Value2 = decltype(* mIter2);
public:
  DiagonalIter(Iter1 iter1, Iter2 iter2, long firstIndex = 0)
    : mIter1(iter1),
      mIter2(iter2),
      mIndex(firstIndex)
  {
  }
  
  bool operator==(DiagonalIter j)
  {
    return (mIter1 == j.mIter1 and mIter2 == j.mIter2);
  }

  bool operator!=(DiagonalIter j)
  {
    return (mIter1 != j.mIter1 or mIter2 != j.mIter2);
  }
  
  DiagonalIter operator++()
  {
    ++mIndex;
    ++mIter1;
    ++mIter2;
    return *this;
  }

  // operator*: returns (column, (nonzero) entry at given row and this column)
  long index()
  {
    return mIndex;
  }
  
  std::pair<Value1, Value2> operator*()
  {
    return {*mIter1, *mIter2};
  }
};

class SparseMatrixZZp
{
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

  using RowIter = DiagonalIter<
    decltype(mColumns.cbegin()),
    decltype(mNonzeroElements.cbegin())
    >;
  
  RowIter cbegin(int row) const;
  RowIter cend(int row) const;

  void dump(std::ostream &o) const;
  void denseDisplay(std::ostream& o) const;

  // read and write files.  Formats: triples.  compressed.

  // Submatrices, windows?

  // Permutations of rows and columns?
  
  // Basic operations. d, e dense vectors, x,y sparse (row) vectors, A,B sparse matrices, c field element
  //  x, y should be allowed to be rows of a sparse matrix A (without creating separate vector).
  //   d += c*x
  //   d += e*A (dense e)
  //   d += x*A (sparse x)

  // for rank.
  //   sparse PLUQ decomposition
  //   

  // Solve x*A = b, A upper triangular, A lower triangular, b dense, b sparse/
  
  // Operations
  SparseMatrixZZp transpose() const;

  // What about: A+B, A-B, A += c*D, A*B, etc...
  
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

inline SparseMatrixZZp::RowIter SparseMatrixZZp::cbegin(int row) const {
  return RowIter(mColumns.cbegin() + mRows[row],
                 mNonzeroElements.cbegin() + mRows[row],
                 mRows[row]);
}

inline SparseMatrixZZp::RowIter SparseMatrixZZp::cend(int row) const {
  return RowIter(mColumns.cbegin() + mRows[row + 1],
                 mNonzeroElements.cbegin() + mRows[row + 1]);
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
