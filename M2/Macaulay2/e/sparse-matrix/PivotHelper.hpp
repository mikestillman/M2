#ifndef _pivot_helper_hpp_
#define _pivot_helper_hpp_

#include "SparseMatrixZZp.hpp"
#include <unordered_map>

// with vector: 

// helper class for determining pivotsw
class PivotHelper
{
private:
  // the following two vectors will have same length, equal to numpivots
  std::vector<IndexType> mPivotRows;
  std::vector<IndexType> mPivotColumns;

  // these vectors are of length numcols/numrows respectively and are initialized to -1 indicating no
  // pivot in that column/row.  If not -1, then the entry is the row/col that has
  // a pivot in this column/row.

  //std::vector<IndexType> mWhichRow;
  //std::vector<IndexType> mWhichColumn;
  std::unordered_map<IndexType,IndexType> mWhichRow;
  std::unordered_map<IndexType,IndexType> mWhichColumn;

  // these vectors tell you the index of a given pivot in mPivotRows/Columns.
  // That is, if mWhichRow[col] is not -1, then mWhichPivotColumn[col] tells you the index of that pivot.

  //std::vector<IndexType> mWhichPivotRow;
  //std::vector<IndexType> mWhichPivotColumn;
  std::unordered_map<IndexType,IndexType> mWhichPivotRow;
  std::unordered_map<IndexType,IndexType> mWhichPivotColumn;

  friend std::ostream& operator<<(std::ostream& buf, const PivotHelper& pivotHelper);
    
public:
  PivotHelper (const SparseMatrixZZp& A) { }
  // PivotHelper (const SparseMatrixZZp& A) :
  //    mWhichRow(A.numColumns()),
  //    mWhichColumn(A.numRows()),
  //    mWhichPivotRow(A.numRows()),
  //    mWhichPivotColumn(A.numColumns())
  // {
  //    std::fill(mWhichRow.begin(), mWhichRow.end(), -1);
  //    std::fill(mWhichColumn.begin(), mWhichColumn.end(), -1);
  //    std::fill(mWhichPivotRow.begin(), mWhichPivotRow.end(), -1);
  //    std::fill(mWhichPivotColumn.begin(), mWhichPivotColumn.end(), -1);
  // }

  void addPivot(IndexType row, IndexType col)
  {
     mWhichPivotRow[row] = numPivots();
     mWhichPivotColumn[col] = numPivots();
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

  void sortPivots(const SparseMatrixZZp& A,
                  std::stack<IndexType>& result) const;

  IndexType pivotRow(IndexType piv) const { return mPivotRows[piv]; }
  IndexType pivotColumn(IndexType piv) const { return mPivotColumns[piv]; }

  // select the version of isPivotRow/Column depending on storage type of mWhichRow/Column 
  bool isPivotRow(IndexType row) const { return mWhichColumn.count(row) > 0; }
  bool isPivotColumn(IndexType col) const { return mWhichRow.count(col) > 0; }
  //bool isPivotRow(IndexType row) const { return mWhichColumn[row] != -1; }
  //bool isPivotColumn(IndexType col) const { return mWhichRow[col] != -1; }

  // these will throw an exception if an entry is not there (which shouldn't happen!)
  IndexType rowPivotIndex(IndexType row) const { return mWhichPivotRow.at(row); }
  IndexType columnPivotIndex(IndexType col) const { return mWhichPivotColumn.at(col); }

private:

  void sortPivotsWorker(IndexType curVertex,
                        std::vector<std::vector<IndexType>>& vertices,
                        std::vector<bool>& visited,
                        std::stack<IndexType>& result) const;

  void buildPivotGraph(const SparseMatrixZZp& A,
                       std::vector<std::vector<IndexType>>& pivotGraph) const;

};

#endif

// Local Variables:
// indent-tabs-mode: nil
// End:
