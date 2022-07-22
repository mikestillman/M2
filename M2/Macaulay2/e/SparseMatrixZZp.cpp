#include "SparseMatrixZZp.hpp"
#include <iomanip>
// example format
// . 1 . . 2 . 3
// . . . 4 . . .
// 5 . 6 . . . 7
// 8 . . . . . .
// elems[0..]: [1 2 3 4 5 6 7 8]
// cols: [1 4 6 3 0 2 6 0]
// rows: [0 3 4 7 8]

SparseMatrixZZp::SparseMatrixZZp(long nrows,
                                 long ncols,
                                 long nentries,
                                 const M2::ARingZZpFlint& F)
  : mField(F),
    mNumRows(nrows),
    mNumColumns(ncols),
    mNonzeroElements(nentries, 0),
    mColumns(nentries, 0),
    mRows(nrows+1, 0)
{
}

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

// void SparseMatrixZZp::denseDisplay(std::ostream& o) const
// {
//   long nextEntry = 0;
//   for (long r=0; r < numRows(); ++r)
//     for (long c=0; c < numColumns(); ++c)
//       {
//         // to be completed
//       }
// }

// TODO with Frank: simplify this code.
void SparseMatrixZZp::denseDisplay(std::ostream& o) const
{
  long nextEntry = 0;
  for (long r=0; r < numRows(); ++r)
    {
      long c = 0;
      auto i {cbegin(r)};
      do
        {
          long nextcol = (i == cend(r) ? numColumns() : (*i).first);
          for ( ; c < nextcol; ++c) std::cout << "   .";
          if (c < numColumns())
            {
              std::cout << " " << std::setw(3) << (*i).second;
              ++c;
              ++i;
            }
        } while (c < numColumns());
      std::cout << std::endl;
    }
}

/// Transpose a sparse matrix
SparseMatrixZZp SparseMatrixZZp::transpose() const
{
  // private internal initializer.  This does not initialize its data.
  SparseMatrixZZp result {numColumns(), numRows(), numNonZeros(), field()};
  
  long *work = new long[numColumns()];
  std::fill(work, work + numColumns(), 0);
  //  for (long i=0; i < numColumns(); ++i) work[i] = 0;

  for (long e=0; e < numNonZeros(); ++e)
    {
      work[mColumns[e]]++;
    }

  // Now compute partial sums (but starting 0, a0, a0+a1, ...) into w, result->mColumns.
  long sum = 0;
  for (long c = 0; c < numColumns(); ++c)
    {
      result.mRows[c] = sum;
      sum += work[c];
    }
  result.mRows[numColumns()] = sum;

  for (long c = 0; c < numColumns(); ++c)
    work[c] = result.mRows[c]; // These are now the next locations for elements in the transposed row.

  // Now we loop through all rows of original matrix, and for each column in that row
  // We will set the column index of the transposed element, and the entry itself.
  for (long r = 0; r < numRows(); ++r)
    for (long ic = mRows[r]; ic < mRows[r+1]; ++ic)
      {
        long oldloc = ic;
        long newloc = work[mColumns[ic]]++; // new location, and bump next location for this column
        result.mNonzeroElements[newloc] = mNonzeroElements[oldloc];
        result.mColumns[newloc] = r;
      }

  return result;
}
// Local Variables:
// indent-tabs-mode: nil
// End:
