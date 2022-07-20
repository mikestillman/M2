#include "SparseMatrixZZp.hpp"

// example format
// . 1 . . 2 . 3
// . . . 4 . . .
// 5 . 6 . . . 7
// 8 . . . . . .
// elems[0..]: [1 2 3 4 5 6 7 8]
// cols: [1 4 6 3 0 2 6 0]
// rows: [0 3 4 7 8]


SparseMatrixZZp::SparseMatrixZZp(const M2::ARingZZpFlint& field,
                                 long nrows,
                                 long ncols,
                                 const std::vector<std::tuple<long,long,ZZpElement>>& triples)
  : mField(field),
    mNumRows(nrows),
    mNumColumns(ncols)
{
  // Assume for now that the data is in row major order: first row, then the second, etc.

  long last_r = 0;
  mRows.push_back(0);
  for (auto t : triples)
    {
      long r = std::get<0>(t);
      long c = std::get<1>(t);
      long v = std::get<2>(t);
      if (r > last_r) mRows.insert(mRows.end(), r-last_r, mColumns.size());
      last_r = r;
      mNonzeroElements.push_back(v);
      mColumns.push_back(c);
    }
  mRows.insert(mRows.end(), nrows-last_r, mColumns.size());
  mRows.push_back(mColumns.size());
}

void SparseMatrixZZp::dump(std::ostream& o) const
{
  o << "Sparse matrix over a finite field, size = " << mNumRows << "x" << mNumColumns << std::endl;
  o << "  Entries: length " << mNonzeroElements.size() << std::endl;
  o << "  Columns: length " << mColumns.size() << std::endl;
  o << "  Rows: length " << mRows.size() << std::endl;
}

void SparseMatrixZZp::denseDisplay(std::ostream& o) const
{
  long nextEntry = 0;
  for (long r=0; r < numRows(); ++r)
    for (long c=0; c < numColumns(); ++c)
      {
        // to be completed
      }
}

// Local Variables:
// indent-tabs-mode: nil
// End:
