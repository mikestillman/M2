#include "PivotHelper.hpp"
#include "PivotGraph.hpp"
#include "SparseMatrixZZp.hpp"
#include "interface/random.h"
#include "timing.hpp"

#include <iomanip> // for std::setw
#include <algorithm> // for std::sort
#include <numeric> // for std::iota
#include <string>

void PivotHelper::findTrivialRowPivots(const SparseMatrixZZp& A)
{  
  // find trivial row pivots -- populates pivotHelper (should be empty beforehand)
  // TODO: This code requires rows to be sorted in column index order.
  assert(mPivotRows.size() == 0);
  for (auto r = 0; r < A.numRows(); ++r)
  {
     for (auto j = A.cbeginColumns(r); j != A.cendColumns(r); ++j)
     {
        IndexType c = *j;
        if (!isPivotColumn(c))
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
  
  for (auto r = 0; r < A.numRows(); ++r)
  {
     // determine if r is a pivot row
     if (isPivotRow(r)) continue;

     // is there an unobstructed column in row i?
     for (auto j = A.cbeginColumns(r); j != A.cendColumns(r); ++j)
     {
        IndexType c = *j;
        if (!isObstructed[c])
        {
           // found a new pivot!
           addPivot(r,c);
           // set the remainder of the row to be obstructed
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
   std::vector<IndexType> columnQueue(A.numColumns());

   IndexType queueHead = 0;
   IndexType queueTail = 0;
   IndexType survivors = 0;

   for (IndexType r = 0; r < A.numRows(); ++r)
   {
      // if row r is matched, then continue
      if (isPivotRow(r)) continue;

      // otherwise, begin the search for a pivot in this row

      // initialization step
      for (auto c = A.cbeginColumns(r); c != A.cendColumns(r); ++c)
      {
         IndexType thisCol = *c;
         // if column is pivotal, then queue this column
         if (isPivotColumn(thisCol))
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
        IndexType queueTopColumn = columnQueue[queueHead++];
        if (!isPivotColumn(queueTopColumn))
          continue;
        IndexType queueTopRow = mWhichRow.at(queueTopColumn);
        // otherwise, we enqueue the non-visited entries in the matched row
        for (auto c = A.cbeginColumns(queueTopRow); c != A.cendColumns(queueTopRow); ++c)
        {
          IndexType thisCol = *c;
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
         IndexType newPivotCol = -1;
         for (auto c = A.cbeginColumns(r); c != A.cendColumns(r); ++c)
         {
           IndexType thisCol = *c;
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
         columnStatuses[*c] = Unmarked;
      for (IndexType i = 0; i < queueTail; ++i)
         columnStatuses[columnQueue[i]] = Unmarked;
      queueHead = 0;
      queueTail = 0;
      survivors = 0;
   }

   return;
}

void PivotHelper::findPivots(const SparseMatrixZZp& A)
{
   findTrivialRowPivots(A);
   IndexType prevPivots = 0;
   // std::cout << "Number of trivial row pivots found   : " << numPivots() - prevPivots << std::endl;
   prevPivots = numPivots();
   findTrivialColumnPivots(A);
   // std::cout << "Number of trivial column pivots found: " << numPivots() - prevPivots << std::endl;
   prevPivots = numPivots();
   // if we already have all the pivots, then return 
   if (mPivotRows.size() == std::min(A.numRows(), A.numColumns())) return;

   findRemainingPivotsGreedy(A);
   // std::cout << "Number of greedy pivots found        : " << numPivots() - prevPivots << std::endl;

   return;
}

void PivotHelper::findUpperTrapezoidalPermutations(const SparseMatrixZZp& A,
                                                   std::vector<IndexType>& rowPerm,
                                                   std::vector<IndexType>& columnPermInverse) const
{
   assert(rowPerm.size() == 0);
   assert(columnPerm.size() == 0);
   columnPermInverse.resize(A.numColumns());
   
   std::vector<VertexType> topSort;
   PivotGraph pivotGraph(A,*this);
   pivotGraph.topologicalSort(topSort);
   if (topSort.size() != numPivots())
      std::cout << "Error finding structural pivots." << std::endl;

   int index = 0;
   for ( ; index < numPivots(); ++index)
   {
      rowPerm.push_back(mPivotRows[topSort[index]]);
      columnPermInverse[mPivotColumns[topSort[index]]] = index;
   }

   // now have to fill out the row and column perm with the non-pivot rows and columns arbitrarily
   // TODO: Think about how to use mWhichColumn instead and deal with 'extra' rows more efficiently
   // TODO: In fact, do we want to pad these out at all, or just infer the remainder of the permutation?
   for (int r = 0; r < A.numRows(); ++r)
      if (!isPivotRow(r)) rowPerm.push_back(r);
   for (int c = 0; c < A.numColumns(); ++c)
      if (!isPivotColumn(c)) columnPermInverse[c] = index++;

   assert(rowPerm.size() == A.numRows());
   assert(columnPermInverse.size() == A.numColumns());
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

