#include "SparseMatrixZZp.hpp"
#include "interface/random.h"
#include "timing.hpp"

#include <iomanip> // for std::setw
#include <algorithm> // for std::sort
#include <numeric> // for std::iota
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

  auto t1 = now();
  std::vector<long> indices(triples.size()); // set the size of the vector.
  std::iota(indices.begin(), indices.end(), 0); // fill it with 0..#triples-1
  std::sort(indices.begin(), indices.end(), [&triples](long i, long j) {
    auto i1 = std::get<0>(triples[i]);
    auto i2 = std::get<1>(triples[i]);
    auto j1 = std::get<0>(triples[j]);
    auto j2 = std::get<1>(triples[j]);
    return i1 < j1 or (i1 == j1 and i2 < j2);
      });
  std::cout << "sort time: " << seconds(now() - t1) << std::endl;

  t1 = now();
  // auto sorted_triples = triples;
  // std::sort(sorted_triples.begin(), sorted_triples.end());
  long last_r = 0;
  mRows.push_back(0);
  for (auto t : indices)
    {
      long r = std::get<0>(triples[t]);
      long c = std::get<1>(triples[t]);
      long v = std::get<2>(triples[t]);
      if (r > last_r) mRows.insert(mRows.end(), r-last_r, mColumns.size());
      last_r = r;
      mNonzeroElements.push_back(v);
      mColumns.push_back(c);
    }
  mRows.insert(mRows.end(), nrows-last_r, mColumns.size());
  mRows.push_back(mColumns.size());
  std::cout << "construct time: " << seconds(now() - t1) << std::endl;
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

  // Now compute partial sums (but starting 0, a0, a0+a1, ...) into w, result.mColumns.
  // We also change work to have these partial sums as well.
  long sum = 0;
  for (long c = 0; c < numColumns(); ++c)
    {
      result.mRows[c] = sum;
      sum += work[c];
      work[c] = result.mRows[c];
    }
  result.mRows[numColumns()] = sum;

  // Now we loop through all rows of original matrix, and for each column in that row
  // We will set the column index of the transposed element, and the entry itself.
  for (long r = 0; r < numRows(); ++r)
    for (long ic = mRows[r]; ic < mRows[r+1]; ++ic)
      {
        long oldloc = ic;
        long newloc = work[mColumns[ic]]++; // new location, and bump next location for this column
        result.mNonzeroElements[newloc] = mNonzeroElements[oldloc];
        //TODO: use field().set(...) instead...
        result.mColumns[newloc] = r;
      }

  delete[] work;
  return result;
}

SparseMatrixZZp SparseMatrixZZp::randomSparseMatrix(const M2::ARingZZpFlint& F,
                                                    long nrows,
                                                    long ncols,
                                                    float density)
{
  long nentries = nrows * 1.0 * ncols * density;
  auto t1 = now();
  std::vector<std::tuple<long,long,ZZpElement>> triples(nentries);
  std::generate(triples.begin(),triples.end(), [&F,nrows,ncols]() {
    ZZpElement val;
    do
      F.random(val);
    while (F.is_zero(val));
    return std::tuple<long,long,ZZpElement>(
      rawRandomULong(nrows),
      rawRandomULong(ncols),
      val);
  });
  auto t2 = now();
  auto result = SparseMatrixZZp(F, nrows, ncols, triples);
  auto t3 = now();
  std::cout << "time for generate: " << seconds(t2-t1) << std::endl;
  std::cout << "time for constructor: " << seconds(t3-t2) << std::endl;
  return result;
}

// Local Variables:
// indent-tabs-mode: nil
// End:
