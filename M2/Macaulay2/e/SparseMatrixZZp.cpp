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

void SparseMatrixZZp::initialize(long nrows,
                                 long ncols,
                                 const TriplesList& triples)
{
  mNumRows = nrows;
  mNumColumns = ncols;

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
                                 const TriplesList& triples)
                                 
  : mField(field)
{
  initialize(nrows, ncols, triples);
}

std::pair<long, long> SparseMatrixZZp::sizesFromTriplesFile(std::istream& i)
{
  long nrows;
  long ncols;
  char notused;
  i >> nrows >> ncols >> notused;
  std::cout << "sizes: " << nrows << " " << ncols << std::endl;  
  return std::make_pair(nrows, ncols);
}

auto SparseMatrixZZp::triplesFromFile(const M2::ARingZZpFlint& field, std::istream& i) -> TriplesList
{
  TriplesList t;
  long rownum, colnum, val;
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

bool SparseMatrixZZp::checkUpperTrapeziodalPermutations(const std::vector<long>& rowPerm,
                                                        const std::vector<long>& columnPermInverse,
                                                        const long numPivots) const
{
   for (int r = 0; r < numPivots; ++r)
   {
      long newRow = rowPerm[r];
      for (auto c = cbegin(newRow); c != cend(newRow); ++c)
      {
         if (columnPermInverse[(*c).first] < r && (*c).second != 0)
            return false;
      }
   }
   return true;
}

bool SparseMatrixZZp::entryPresent(long row, long col) const
{
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

//////////////////////////////////////
/// Transpose a sparse matrix ////////
//////////////////////////////////////
SparseMatrixZZp SparseMatrixZZp::transpose() const
{
  // private internal initializer.  This does not initialize its data.
  SparseMatrixZZp result {numColumns(), numRows(), numNonZeros(), field()};
  
  long *work = new long[numColumns()];
  std::fill(work, work + numColumns(), 0);

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

  // ConstRowIter version
  for (long r = 0; r < numRows(); ++r)
    for (auto ic = cbegin(r); ic != cend(r); ++ic)
      {
        long newloc = work[(*ic).first]++; // new location, and bump next location for this column
        result.mNonzeroElements[newloc] = (*ic).second;
        // TODO: use field().set(...) instead...
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

//void pivotFinder(const SparseMatrixZZp& A,
//                 std::vector<std::pair<int,int>>& pivotLocations)
//{
   // first find easy pivots corresponding to rows
   // first find easy pivots corresponding to cols
   // find rest of the pivots using the recursive greedy algorithm (spasm sec 3.4)
//}

void PivotHelper::findTrivialRowPivots(const SparseMatrixZZp& A)
{  
  // find trivial row pivots -- populates pivotHelper (should be empty beforehand)
  assert(mPivotRows.size() == 0);
  for (auto r = 0; r < A.numRows(); ++r)
  {
     for (auto j = A.cbeginColumns(r); j != A.cendColumns(r); ++j)
     {
        long c = *j;
        if (mWhichRow[c] == -1)
           addPivot(r,c);
        break;
     }
  }
}

void PivotHelper::findTrivialColumnPivots(const SparseMatrixZZp& A)
{  
  // find trivial column pivots, assuming trivial row pivots have been found are in pivotLocations
  if (mPivotRows.size() == 0) return;

  std::vector<bool> isObstructed(A.numColumns());
  std::fill(isObstructed.begin(), isObstructed.end(), false);

  // mark columns as obstructed based on pivot rows
  // this requires us to loop through *all* nonzero entries of pivot rows
  for(auto i : mPivotRows)
  {
     for(auto j = A.cbeginColumns(i); j != A.cendColumns(i); ++j)
     {
       isObstructed[*j] = true;
     }
  }

  // find those rows that have an entry in an unobstructed column
  
  long currentPivotIndex = 0;
  long nRowPivots = mPivotRows.size();
  for (auto r = 0; r < A.numRows(); ++r)
  {
     // determine if i is a pivot row
     if (currentPivotIndex < nRowPivots && r == mPivotRows[currentPivotIndex])
     {
        currentPivotIndex++;
        continue;
     }

     // is there an unobstructed column in row i?
     for (auto j = A.cbeginColumns(r); j != A.cendColumns(r); ++j)
     {
        long c = *j;
        if (!isObstructed[c])
        {
           // found a new pivot!
           addPivot(r,c);
           nRowPivots++;
           while (j != A.cendColumns(r))
           {
             isObstructed[*j] = true;
             ++j;
           }
           break;
        }
     }
  }
}

void PivotHelper::findRemainingPivotsGreedy(const SparseMatrixZZp& A)
{
   enum ColumnStatus { Unmarked, Candidate, Visited };

   std::vector<ColumnStatus> columnStatuses(A.numColumns());
   std::fill(columnStatuses.begin(), columnStatuses.end(), Unmarked);
   std::vector<long> columnQueue(A.numColumns());

   long queueHead = 0;
   long queueTail = 0;
   long survivors = 0;

   for (long r = 0; r < A.numRows(); ++r)
   {
      // if row r is matched, then continue
      if (mWhichColumn[r] != -1) continue;

      // otherwise, begin the search for a pivot in this row

      // initialization step
      for (auto c = A.cbeginColumns(r); c != A.cendColumns(r); ++c)
      {
         unsigned long thisCol = *c;
         if (mWhichRow[thisCol] != -1)
            columnQueue[queueTail++] = thisCol;
         else
         {
            // otherwise, mark this column as a candidate
            columnStatuses[thisCol] = Candidate;
            survivors++;
         }
      }

      while (queueHead < queueTail && survivors > 0)
      {
        long queueTopColumn = columnQueue[queueHead++];
        long queueTopRow = mWhichRow[queueTopColumn];
        if (queueTopRow == -1)
          continue;
        // otherwise, we enqueue the non-visited entries in the matched row
        for (auto c = A.cbeginColumns(queueTopRow); c != A.cendColumns(queueTopRow); ++c)
        {
          long thisCol = *c;
          if (columnStatuses[thisCol] != Visited)
          {
            if (columnStatuses[thisCol] == Candidate)
              survivors--;
            columnStatuses[thisCol] = Visited;
            columnQueue[queueTail++] = thisCol;
          }
        }
      }
      
      if (survivors > 0)
      {
         // find the survivor and add to the list
         long newPivotCol = -1;
         for (auto c = A.cbeginColumns(r); c != A.cendColumns(r); ++c)
         {
           long thisCol = *c;
           if (columnStatuses[thisCol] == Candidate)
           {
             addPivot(r,thisCol);
             break;
           }
         }
      }

      // cleanup:
      // clear the marks from nonzero entries in current row
      for (auto c = A.cbeginColumns(r); c != A.cendColumns(r); ++c)
      {
         long thisCol = *c;
         columnStatuses[thisCol] = Unmarked;
      }
      for (long i = 0; i < queueTail; ++i)
         columnStatuses[i] = Unmarked;
      queueHead = 0;
      queueTail = 0;
      survivors = 0;
   }

   return;
}

void PivotHelper::findPivots(const SparseMatrixZZp& A)
{
   findTrivialRowPivots(A);
   long prevPivots = 0;
   std::cout << "Number of trivial row pivots found   : " << numPivots() - prevPivots << std::endl;
   prevPivots = numPivots();
   findTrivialColumnPivots(A);
   std::cout << "Number of trivial column pivots found: " << numPivots() - prevPivots << std::endl;
   prevPivots = numPivots();
   // if we already have all the pivots, then return 
   if (mPivotRows.size() == std::min(A.numRows(), A.numColumns())) return;

   findRemainingPivotsGreedy(A);
   std::cout << "Number of greedy pivots found        : " << numPivots() - prevPivots << std::endl;

   return;
}

void PivotHelper::findUpperTrapezoidalPermutations(const SparseMatrixZZp& A,
                                                   std::vector<long>& rowPerm,
                                                   std::vector<long>& columnPermInverse) const
{
   assert(rowPerm.size() == 0);
   assert(columnPerm.size() == 0);
   columnPermInverse.resize(A.numColumns());
   std::stack<long> pivotOrder;
   sortPivots(A,pivotOrder);
   long colNum = 0;
   while (!pivotOrder.empty())
   {
     auto top = pivotOrder.top();
     rowPerm.push_back(mPivotRows[top]);
     columnPermInverse[mPivotColumns[top]] = colNum++;
     pivotOrder.pop();
   }

   // now have to fill out the row and column perm with the non-pivot rows and columns arbitrarily
   for (int r = 0; r < A.numRows(); ++r)
      if (mWhichColumn[r] == -1) rowPerm.push_back(r);
   for (int c = 0; c < A.numColumns(); ++c)
      if (mWhichRow[c] == -1) columnPermInverse[c] = colNum++;
}

void PivotHelper::buildPivotGraph(const SparseMatrixZZp& A,
                                  std::vector<std::vector<long>>& pivotGraph) const
{
   assert(pivotGraph.size() == 0);
   // build pivot graph
   for (int i = 0; i < mPivotRows.size(); ++i)
      pivotGraph.emplace_back(std::vector<long> {});
   
   for (int i = 0; i < mPivotRows.size(); ++i)
   {
      for (int j = i+1; j < mPivotRows.size(); ++j)
      {
         if (A.entryPresent(mPivotRows[i],mPivotColumns[j])) pivotGraph[i].push_back(j);
         if (A.entryPresent(mPivotRows[j],mPivotColumns[i])) pivotGraph[j].push_back(i);
      }
   }
}

void PivotHelper::sortPivots(const SparseMatrixZZp& A,
                             std::stack<long>& result) const
{
   assert(result.size() == 0);
   std::vector<std::vector<long>> pivotGraph;
   std::vector<bool> visited(mPivotRows.size(),false);

   buildPivotGraph(A,pivotGraph);
   
   for (int i = 0; i < mPivotRows.size(); ++i)
      if (!visited[i])
	 sortPivotsWorker(i,pivotGraph,visited,result);

   return;
}

void PivotHelper::sortPivotsWorker(long curVertex,
                                   std::vector<std::vector<long>>& pivotGraph,
                                   std::vector<bool>& visited,
                                   std::stack<long>& result) const
{
   visited[curVertex] = true;

   for (auto edgeTo = pivotGraph[curVertex].cbegin(); edgeTo != pivotGraph[curVertex].cend(); ++edgeTo)
      if (!visited[*edgeTo])
         sortPivotsWorker(*edgeTo, pivotGraph, visited, result);

   result.push(curVertex);
}

std::ostream& operator<<(std::ostream& buf, const PivotHelper& pivotHelper)
{
  buf << "[";
  for (auto i = 0; i < pivotHelper.mPivotRows.size(); ++i)
  {
    if (i != 0)
      buf << ",";
    buf << "(" << pivotHelper.mPivotRows[i]
        << "," << pivotHelper.mPivotColumns[i]
        << ")";
  }
  buf << "]";
  return buf;
}

void toDenseMatrix(const SparseMatrixZZp& input,
                   const M2::ARingZZpFlint& field,
                   DMat<M2::ARingZZpFFPACK>& result)
{
   auto& R = result.ring();
   for (long r = 0; r < input.numRows(); ++r)
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

