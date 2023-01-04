#ifndef _sparse_matrix_ZZp_hpp_
#define _sparse_matrix_ZZp_hpp_

#include <vector>
#include <tuple>
#include <iostream>
#include "aring-zzp-flint.hpp"
#include "aring-zzp-ffpack.hpp"
#include "dmat.hpp"
#include "Iterators.hpp"

class SparseVector;
class DenseVector;

using ZZpElement = M2::ARingZZpFlint::ElementType; // really just long.
using IndexType = int;

class SparseMatrixZZp
{
private:
  // Let e be the number of non-zero elements in the matrix
  const M2::ARingZZpFlint& mField;
  IndexType mNumRows;
  IndexType mNumColumns;
  std::vector<ZZpElement> mNonzeroElements; // 0..e-1
  std::vector<IndexType> mColumns; // 0..e-1: mColumns[i] is the column number of of the i-th element in mNonzeroElements.
  std::vector<IndexType> mRows; // 0..mNumRows // mRows[r]..mRows[r+1]-1 are the indices into mNonzeroElements, in this row.
  // Note: if none, mRows[r-1] == mRows[r].

  // Question: what is the format of a 0x0 matrix.
  // [[], [], [0]]

public:
  using TriplesList = std::vector<std::tuple<IndexType,IndexType,ZZpElement>>; // each entry is (row index, column index, value).

  using ConstRowIter = DiagonalIter<
    decltype(mColumns.cbegin()),
    decltype(mNonzeroElements.cbegin())
    >;
  
  using ConstRowIterColumns = decltype(mColumns.cbegin());

  IndexType numRows() const { return mNumRows; }
  IndexType numColumns() const { return mNumColumns; }
  IndexType numNonZeros() const { return mColumns.size(); }
  IndexType numRowEntries(IndexType row) const { return (mRows[row+1] - mRows[row]); }

  const M2::ARingZZpFlint& field() const {return mField; }

  /// Constructor: from a set of triples, IN LEX ORDER, (r,c,element).
  SparseMatrixZZp(const M2::ARingZZpFlint& F,
                  IndexType nrows,
                  IndexType ncols,
                  const TriplesList& triples
                  );

  SparseMatrixZZp(const M2::ARingZZpFlint& F, std::istream& i); // i is in sms format (meaning TODO: what is this)

  ConstRowIter cbegin(int row) const;
  ConstRowIter cend(int row) const;

  ConstRowIterColumns cbeginColumns(int row) const;  
  ConstRowIterColumns cendColumns(int row) const;  

  // warning: This is painfully slow - think before you use :)
  bool entryPresent(IndexType row, IndexType col) const;

  bool checkUpperTrapeziodalPermutations(const std::vector<IndexType>& rowPerm,
                                         const std::vector<IndexType>& columnPermInverse,
                                         const IndexType numPivots) const;

  void dump(std::ostream &o) const;
  void denseDisplay(std::ostream& o) const;

  void writeSMSFile(std::ostream &o) const;

  // Submatrices, windows?

  // Permutations of rows and columns?
  
  // Operations
  SparseMatrixZZp transpose() const;
  SparseMatrixZZp applyPermutations(const std::vector<IndexType>& rowPerm,
                                    const std::vector<IndexType>& columnPerm) const;

  static SparseMatrixZZp randomSparseMatrix(const M2::ARingZZpFlint& F,
                                            IndexType nrows,
                                            IndexType ncols,
                                            float density);
private:
  // Fill in entire object except for the field.
  // Assumption: each matrix element (i,j) must appear at most once, and the element must be non-zero.
  void initialize(IndexType nrows,
                  IndexType ncols,
                  const TriplesList& triples);
  
  // Private initializer that sets sizes of the vectors, but does not initialize them?
  SparseMatrixZZp(IndexType nrows,
                  IndexType ncols,
                  IndexType nentries,
                  const M2::ARingZZpFlint& F
                  );

  // The following assume that mField has been set, in order to read/copy field elements.
  // Format of the file:
  //  (line 1): numrows numcols unusedString
  //  lines of the form:  i j val
  //  ending with 0 0 0
  // Notes: these are 1-indexed, val is a IndexType
  static std::pair<IndexType, IndexType> sizesFromTriplesFile(std::istream& i);
  static TriplesList triplesFromFile(const M2::ARingZZpFlint& field, std::istream& i);
  
  // Are the i,j values in ascending lex order?  The field elements are not accessed.
  static bool isOrdered(const TriplesList& triples);
};

inline SparseMatrixZZp::ConstRowIter SparseMatrixZZp::cbegin(int row) const {
  return ConstRowIter(mColumns.cbegin() + mRows[row],
                      mNonzeroElements.cbegin() + mRows[row]);
}

inline SparseMatrixZZp::ConstRowIter SparseMatrixZZp::cend(int row) const {
  return ConstRowIter(mColumns.cbegin() + mRows[row + 1],
                      mNonzeroElements.cbegin() + mRows[row + 1]);
}

inline SparseMatrixZZp::ConstRowIterColumns SparseMatrixZZp::cbeginColumns(int row) const {
  return (mColumns.cbegin() + mRows[row]);
}

inline SparseMatrixZZp::ConstRowIterColumns SparseMatrixZZp::cendColumns(int row) const {
  return (mColumns.cbegin() + mRows[row + 1]);
}

void toDenseMatrix(const SparseMatrixZZp& input,
                   const M2::ARingZZpFlint& field,
                   DMat<M2::ARingZZpFFPACK>& result);

// TODO: Do we want to keep these?
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

#endif
#endif

// Local Variables:
// indent-tabs-mode: nil
// End:
