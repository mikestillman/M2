#ifndef _sparse_matrix_ZZp_hpp_
#define _sparse_matrix_ZZp_hpp_

#include <vector>
#include <tuple>
#include <iostream>
#include "aring-zzp-flint.hpp"

using ZZpElement = M2::ARingZZpFlint::ElementType; // really just long.

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
  using TriplesList = std::vector<std::tuple<long,long,ZZpElement>>; // each entry is (row index, column index, value).

  using ConstRowIter = DiagonalIter<
    decltype(mColumns.cbegin()),
    decltype(mNonzeroElements.cbegin())
    >;

  long numRows() const { return mNumRows; }
  long numColumns() const { return mNumColumns; }
  long numNonZeros() const { return mColumns.size(); }
  const M2::ARingZZpFlint& field() const {return mField; }

  /// Constructor: from a set of triples, IN LEX ORDER, (r,c,element).
  SparseMatrixZZp(const M2::ARingZZpFlint& F,
                  long nrows,
                  long ncols,
                  const TriplesList& triples
                  );

  SparseMatrixZZp(const M2::ARingZZpFlint& F, std::istream& i); // i is in sms format (meaning TODO: what is this)
  
  ConstRowIter cbegin(int row) const;
  ConstRowIter cend(int row) const;

  void dump(std::ostream &o) const;
  void denseDisplay(std::ostream& o) const;

  // read and write files.  Formats: triples.  compressed.

  // Submatrices, windows?

  // Permutations of rows and columns?
  
  // Basic operations. d, e dense vectors, x,y sparse (row) vectors, A,B sparse matrices, c field element
  //  x, y should be allowed to be rows of a sparse matrix A (without creating separate vector).
  //   d += c*x (scatter in spasm)
  //   d += e*A (dense e)
  //   d += x*A (sparse x)
  //  void rowUpdate(DenseRow& d, const FieldElement c, const SparseRow x);

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
  // Fill in entire object except for the field.
  // Assumption: each matrix element (i,j) must appear at most once, and the element must be non-zero.
  void initialize(long nrows,
                  long ncols,
                  const TriplesList& triples);
  
  // Private initializer that sets sizes of the vectors, but does not initialize them?
  SparseMatrixZZp(long nrows,
                  long ncols,
                  long nentries,
                  const M2::ARingZZpFlint& F
                  );

  // The following assume that mField has been set, in order to read/copy field elements.
  // Format of the file:
  //  (line 1): numrows numcols unusedString
  //  lines of the form:  i j val
  //  ending with 0 0 0
  // Notes: these are 1-indexed, val is a long
  static std::pair<long, long> sizesFromTriplesFile(std::istream& i);
  static TriplesList triplesFromFile(const M2::ARingZZpFlint& field, std::istream& i);
  
  // Are the i,j values in ascending lex order?  The field elements are not accessed.
  static bool isOrdered(const TriplesList& triples);
};

inline SparseMatrixZZp::ConstRowIter SparseMatrixZZp::cbegin(int row) const {
  return ConstRowIter(mColumns.cbegin() + mRows[row],
                 mNonzeroElements.cbegin() + mRows[row],
                 mRows[row]);
}

inline SparseMatrixZZp::ConstRowIter SparseMatrixZZp::cend(int row) const {
  return ConstRowIter(mColumns.cbegin() + mRows[row + 1],
                 mNonzeroElements.cbegin() + mRows[row + 1]);
}

// helper class for determining pivots
class PivotHelper
{
public:
  PivotHelper (int numcols) :
     mWhichRow(numcols) 
  {
     std::fill(mWhichRow.begin(), mWhichRow.end(), -1); // set -1 to all.
  }  

  void addPivot(long row, long col)
  {
     mPivotRows.push_back(row);
     mPivotCols.push_back(col);
     mWhichRow[col] = row;
  }

  // the following two vectors will have same length, equal to numpivots
  std::vector<long> mPivotRows;
  std::vector<long> mPivotCols;

  // this vector is of length numcols and is initialized to -1 indicating no
  // pivot in that column.  If not -1, then the entry is the row that has
  // a pivot in this column.
  std::vector<int> mWhichRow;
};

std::ostream& operator<<(std::ostream& buf, const PivotHelper& pivotHelper);

void trivialRowPivots(const SparseMatrixZZp& A,
                      PivotHelper& pivotHelper);

void trivialColumnPivots(const SparseMatrixZZp& A,
                         PivotHelper& pivotHelper);


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
