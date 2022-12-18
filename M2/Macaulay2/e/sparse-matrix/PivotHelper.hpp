#ifndef _pivot_helper_hpp_
#define _pivot_helper_hpp_

#include "SparseMatrixZZp.hpp"

// helper class for determining pivots
class PivotHelper
{
  friend std::ostream& operator<<(std::ostream& buf, const PivotHelper& pivotHelper);
    
public:
  PivotHelper (const SparseMatrixZZp& A) : 
     mWhichRow(A.numColumns()), 
     mWhichColumn(A.numRows()) 
  {
     std::fill(mWhichRow.begin(), mWhichRow.end(), -1); // set -1 to all.
     std::fill(mWhichColumn.begin(), mWhichColumn.end(), -1); // set -1 to all.
  }

  void addPivot(IndexType row, IndexType col)
  {
     mPivotRows.push_back(row);
     mPivotColumns.push_back(col);
     mWhichRow[col] = row;
     mWhichColumn[row] = col;
  }

  void findTrivialRowPivots(const SparseMatrixZZp& A);

  void findTrivialColumnPivots(const SparseMatrixZZp& A);

  void findPivots(const SparseMatrixZZp& A);
  
  IndexType numPivots() const { return mPivotRows.size(); }

  void findRemainingPivotsGreedy(const SparseMatrixZZp& A);

  void findUpperTrapezoidalPermutations(const SparseMatrixZZp& A,
                                        std::vector<IndexType>& rowPerm,
                                        std::vector<IndexType>& columnPermInverse) const;

  void buildPivotGraph(const SparseMatrixZZp& A,
                       std::vector<std::vector<IndexType>>& pivotGraph) const;
  
  void sortPivots(const SparseMatrixZZp& A,
                  std::stack<IndexType>& result) const;

  void sortPivotsWorker(IndexType curVertex,
                        std::vector<std::vector<IndexType>>& vertices,
                        std::vector<bool>& visited,
                        std::stack<IndexType>& result) const;

private:
  // the following two vectors will have same length, equal to numpivots
  std::vector<IndexType> mPivotRows;
  std::vector<IndexType> mPivotColumns;

  // these vectors are of length numcols/numrows respectively and are initialized to -1 indicating no
  // pivot in that column/row.  If not -1, then the entry is the row/col that has
  // a pivot in this column/row.
  std::vector<IndexType> mWhichRow;
  std::vector<IndexType> mWhichColumn;

};

#endif

// Local Variables:
// indent-tabs-mode: nil
// End:
