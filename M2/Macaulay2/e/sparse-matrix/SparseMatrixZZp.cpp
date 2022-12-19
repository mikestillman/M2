#include "SparseMatrixZZp.hpp"
#include "interface/random.h"
#include "timing.hpp"

#include <iomanip> // for std::setw
#include <algorithm> // for std::sort
#include <numeric> // for std::iota
#include <string>
// example format
// . 1 . . 2 . 3
// . . . 4 . . .
// 5 . 6 . . . 7
// 8 . . . . . .
// elems[0..]: [1 2 3 4 5 6 7 8]
// cols: [1 4 6 3 0 2 6 0]
// rows: [0 3 4 7 8]

void SparseMatrixZZp::initialize(IndexType nrows,
                                 IndexType ncols,
                                 const TriplesList& triples)
{
  mNumRows = nrows;
  mNumColumns = ncols;

  auto t1 = now();
  std::vector<IndexType> indices(triples.size()); // set the size of the vector.
  std::iota(indices.begin(), indices.end(), 0); // fill it with 0..#triples-1
  std::sort(indices.begin(), indices.end(), [&triples](IndexType i, IndexType j) {
    auto i1 = std::get<0>(triples[i]);
    auto i2 = std::get<1>(triples[i]);
    auto j1 = std::get<0>(triples[j]);
    auto j2 = std::get<1>(triples[j]);
    return i1 < j1 or (i1 == j1 and i2 < j2);
  });
  std::cout << "sort time: " << seconds(now() - t1) << std::endl;

  t1 = now();
  IndexType last_r = 0;
  mRows.push_back(0);
  for (auto t : indices)
    {
      IndexType r = std::get<0>(triples[t]);
      IndexType c = std::get<1>(triples[t]);
      IndexType v = std::get<2>(triples[t]);
      if (r > last_r) mRows.insert(mRows.end(), r-last_r, mColumns.size());
      last_r = r;
      mNonzeroElements.push_back(v);
      mColumns.push_back(c);
    }
  mRows.insert(mRows.end(), nrows-last_r, mColumns.size());
  //mRows.push_back(mColumns.size());
  std::cout << "construct time: " << seconds(now() - t1) << std::endl;
}

                                 
SparseMatrixZZp::SparseMatrixZZp(IndexType nrows,
                                 IndexType ncols,
                                 IndexType nentries,
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
                                 IndexType nrows,
                                 IndexType ncols,
                                 const TriplesList& triples)
                                 
  : mField(field)
{
  initialize(nrows, ncols, triples);
}

std::pair<IndexType, IndexType> SparseMatrixZZp::sizesFromTriplesFile(std::istream& i)
{
  IndexType nrows;
  IndexType ncols;
  char notused;
  i >> nrows >> ncols >> notused;
  std::cout << "sizes: " << nrows << " " << ncols << std::endl;  
  return std::make_pair(nrows, ncols);
}

auto SparseMatrixZZp::triplesFromFile(const M2::ARingZZpFlint& field, std::istream& i) -> TriplesList
{
  TriplesList t;
  IndexType rownum, colnum;
  long val;
  ZZpElement normalized_val;
  field.init(normalized_val);
  std::string str;
  
  // TODO: this code assumes that the tuples in the file are sorted lexicographically without repeats
  while (true)
    {
      i >> rownum >> colnum;
      std::getline(i, str);

      val = std::stol(str.c_str());
      if (rownum == 0) break;
      field.set_from_long(normalized_val, val);
      t.push_back({rownum-1, colnum-1, normalized_val});
    }

  field.clear(normalized_val);
  return t;
}


SparseMatrixZZp::SparseMatrixZZp(const M2::ARingZZpFlint& F,
                                 std::istream& i)
  : mField(F)
{
  auto sizes = sizesFromTriplesFile(i);
  auto triples = triplesFromFile(F, i);
  initialize(sizes.first, sizes.second, triples);
}

bool SparseMatrixZZp::checkUpperTrapeziodalPermutations(const std::vector<IndexType>& rowPerm,
                                                        const std::vector<IndexType>& columnPermInverse,
                                                        const IndexType numPivots) const
{
   for (int r = 0; r < numPivots; ++r)
   {
      IndexType newRow = rowPerm[r];
      for (auto c = cbegin(newRow); c != cend(newRow); ++c)
      {
         if (columnPermInverse[(*c).first] < r && (*c).second != 0)
         {
           std::cout << "Error in position (" << rowPerm[r] << "," << columnPermInverse[(*c).first] << ")" << std::endl;
           return false;
         }
      }
   }
   return true;
}

bool SparseMatrixZZp::entryPresent(IndexType row, IndexType col) const
{
   // TODO: this code also assumes that the entries in a row are sorted according to column
   for (auto c = cbegin(row); c != cend(row); ++c)
   {
      if ((*c).first == col && (*c).second != 0) return true;
      if ((*c).first > col) break;
   }
   return false;
}

void SparseMatrixZZp::dump(std::ostream& o) const
{
  o << "Sparse matrix over a finite field, size = " << mNumRows << "x" << mNumColumns << std::endl;
  o << "  Entries: length " << mNonzeroElements.size() << std::endl;
  o << "  Columns: length " << mColumns.size() << std::endl;
  o << "  Rows: length " << mRows.size() << std::endl;
}

// TODO with Frank: simplify this code.
void SparseMatrixZZp::denseDisplay(std::ostream& o) const
{
  // TODO: this code assumes the entries for a row are in increasing column order.
  //       do we want to enforce this?  if not, where else are we using this?  I am not sure...
  for (IndexType r=0; r < numRows(); ++r)
    {
      IndexType c = 0;
      auto i {cbegin(r)};
      do
        {
          IndexType nextcol = (i == cend(r) ? numColumns() : (*i).first);
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

//////////////////////////////////////
/// Transpose a sparse matrix ////////
//////////////////////////////////////
SparseMatrixZZp SparseMatrixZZp::transpose() const
{
  // private internal initializer.  This does not initialize its data.
  SparseMatrixZZp result {numColumns(), numRows(), numNonZeros(), field()};
  
  IndexType *work = new IndexType[numColumns()];
  std::fill(work, work + numColumns(), 0);

  for (IndexType e=0; e < numNonZeros(); ++e)
    {
      work[mColumns[e]]++;
    }

  // Now compute partial sums (but starting 0, a0, a0+a1, ...) into w, result.mColumns.
  // We also change work to have these partial sums as well.
  IndexType sum = 0;
  for (IndexType c = 0; c < numColumns(); ++c)
    {
      result.mRows[c] = sum;
      sum += work[c];
      work[c] = result.mRows[c];
    }
  result.mRows[numColumns()] = sum;

  // ConstRowIter version
  for (IndexType r = 0; r < numRows(); ++r)
    for (auto ic = cbegin(r); ic != cend(r); ++ic)
      {
        IndexType newloc = work[(*ic).first]++; // new location, and bump next location for this column
        result.mNonzeroElements[newloc] = (*ic).second;
        // TODO: use field().set(...) instead...
        result.mColumns[newloc] = r;
      }
  
  delete[] work;
  return result;
}

SparseMatrixZZp SparseMatrixZZp::applyPermutations(const std::vector<IndexType>& rowPerm,
                                                   const std::vector<IndexType>& columnPermInverse) const
{
  // private internal initializer.  This does not initialize its data.
  SparseMatrixZZp result {numRows(), numColumns(), numNonZeros(), field()};
  
  IndexType newloc = 0;
  IndexType *work = new IndexType[numColumns()];

  for (IndexType i = 0; i < numRows(); ++i)
  {
     result.mRows[i] = newloc;
     
     // we can decide to either keep the columns in a row sorted by column number or not.

     // sorting version here
     IndexType rowEntries = numRowEntries(rowPerm[i]);
     IndexType rowLoc = mRows[rowPerm[i]];
     std::iota(work, work+rowEntries,0);
     std::sort(work, work+rowEntries, [this,&columnPermInverse,rowLoc] (IndexType i, IndexType j) {
       return (columnPermInverse[mColumns[rowLoc+i]] < columnPermInverse[mColumns[rowLoc+j]]);
     });
     for (IndexType j = 0; j < rowEntries; ++j)
     {
        result.mNonzeroElements[newloc+j] = mNonzeroElements[rowLoc+work[j]];
        result.mColumns[newloc+j] = columnPermInverse[mColumns[rowLoc+work[j]]];
     }
     newloc += rowEntries;
     // end sorting version
     
     // non-sorting version here
     // for (auto c = cbegin(rowPerm[i]); c != cend(rowPerm[i]); ++c)
     // {
     //    // do we care about sorting the entries for a row in column order?
     //    // this will mess up the order, if we care.
     //    result.mNonzeroElements[newloc] = (*c).second;
     //    result.mColumns[newloc] = columnPermInverse[(*c).first];
     //    newloc++;
     // }
     // end non-sorting version
  }
  result.mRows[numRows()] = newloc;
  delete [] work;
  return result;
}

SparseMatrixZZp SparseMatrixZZp::randomSparseMatrix(const M2::ARingZZpFlint& F,
                                                    IndexType nrows,
                                                    IndexType ncols,
                                                    float density)
{
  IndexType nentries = nrows * 1.0 * ncols * density;
  auto t1 = now();
  std::vector<std::tuple<IndexType,IndexType,ZZpElement>> triples(nentries);
  std::generate(triples.begin(),triples.end(), [&F,nrows,ncols]() {
    ZZpElement val;
    do
      F.random(val);
    while (F.is_zero(val));
    return std::tuple<IndexType,IndexType,ZZpElement>(
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

void toDenseMatrix(const SparseMatrixZZp& input,
                   const M2::ARingZZpFlint& field,
                   DMat<M2::ARingZZpFFPACK>& result)
{
   auto& R = result.ring();
   for (IndexType r = 0; r < input.numRows(); ++r)
   {
      for (auto c = input.cbegin(r); c != input.cend(r); ++c)
      {
         R.set_from_long(result.entry(r,(*c).first),
                         field.coerceToLongInteger((*c).second));
      }
   }
}

#if 0

// constructor for a PivotGraph object?
void buildPivotGraph(const SparseMatrixZZp& A,
                     PivotHelper& pivotHelper,
                     PivotGraph& pivotGraph)
{
  // build the graph with vertices corresponding to pivots and
  // add an edge from pivot i (in position (r_i,c_i)) to
  // pivot j (in position (r_j,c_j)) if A_(r_i,c_j) \neq 0
}

void applyPermutations(SparseMatrixZZp& A,
                       const std::vector<int>& rowPerm,
                       const std::vector<int>& colPermInv)
{
  // apply the row and column permutations -- if these perms come from pivotFinder,
  // A will have an upper triangular upper-lefthand block
}

// PivotHelper class
// row pivots (std::vector<int> of length = #pivots found thus far) 
// column pivots (std::vector<int> of length = #cols, -1 as a sentinel meaning no pivot in that col
// pivotLocations (std::vector<std::pair<int>>) (so we don't have to rebuilt it to do topological sort)

/////////////////////////////////
// axpy type functions //////////
/////////////////////////////////

// x: dense,
// A[j] sparse row (iterator perhaps: pointer to list of entries, list of columns, and the number)
// c: field element
// Routine:
//   x += c*A[j].  This is what we use in F4 algorithm alot... (give first, last?)
//
//

A = matrix{
    {1,0,1,0,0,1,1,0,1},
    {0,1,1,1,0,1,0,1,0},
    {0,0,1,1,0,0,0,1,1},
    {0,1,1,0,1,0,0,0,0},
    {0,1,0,1,0,0,1,0,1},
    {1,0,1,0,1,1,0,1,1}}

A_{0,1,2,4,3,5,6,7,8}
B = A_{4,0,1,2,3,5,6,7,8}
B^{3,0,1,2,4,5}

needsPackage "Graphs"

A_{0,1,2,4}^{0,1,2,3}

nodes: A = (0,0)
B = (1,1)
C = (2,2)
D = (3,4)
E = (4,6)

-- add an edge from i (r_i,c_i) to j (r_j,c_j) if A_(r_i,c_j) \neq 0
-- find a topological sort of this directed acyclic graph

-- use vertex order: 




A_{4,1,0,2}^{3,1,0,2} -- D B A C
A_{4,0,1,2}^{3,0,1,2} -- D A B C

R = ZZ
M = mutableMatrix(R,10,12)

#endif

// Local Variables:
// indent-tabs-mode: nil
// End:

