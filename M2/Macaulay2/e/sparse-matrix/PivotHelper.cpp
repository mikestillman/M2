#include "PivotHelper.hpp"
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
  
  for (auto r = 0; r < A.numRows(); ++r)
  {
     // determine if r is a pivot row
     if (mWhichColumn[r] != -1) continue;

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
      if (r % 5000 == 0)
      {
         std::cout << "Processed " << r << " rows." << std::endl;
      }

      // if row r is matched, then continue
      if (mWhichColumn[r] != -1) continue;

      // otherwise, begin the search for a pivot in this row

      // initialization step
      for (auto c = A.cbeginColumns(r); c != A.cendColumns(r); ++c)
      {
         IndexType thisCol = *c;
         // if column is pivotal, then queue this column
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
        IndexType queueTopColumn = columnQueue[queueHead++];
        IndexType queueTopRow = mWhichRow[queueTopColumn];
        if (queueTopRow == -1)
          continue;
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
                                                   std::vector<IndexType>& rowPerm,
                                                   std::vector<IndexType>& columnPermInverse) const
{
   assert(rowPerm.size() == 0);
   assert(columnPerm.size() == 0);
   columnPermInverse.resize(A.numColumns());
   
   std::stack<IndexType> pivotOrder;
   sortPivots(A,pivotOrder);
   IndexType colNum = 0;
   while (!pivotOrder.empty())
   {
     auto top = pivotOrder.top();
     rowPerm.push_back(mPivotRows[top]);
     columnPermInverse[mPivotColumns[top]] = colNum++;
     pivotOrder.pop();
   }

   // now have to fill out the row and column perm with the non-pivot rows and columns arbitrarily
   // TODO: Think about how to use mWhichColumn instead and deal with 'extra' rows more efficiently
   for (int r = 0; r < A.numRows(); ++r)
      if (mWhichColumn[r] == -1) rowPerm.push_back(r);
   for (int c = 0; c < A.numColumns(); ++c)
      if (mWhichRow[c] == -1) columnPermInverse[c] = colNum++;

   assert(rowPerm.size() == A.numRows());
   assert(columnPermInverse.size() == A.numColumns());
}

void PivotHelper::buildPivotGraph(const SparseMatrixZZp& A,
                                  std::vector<std::vector<IndexType>>& pivotGraph) const
{
   assert(pivotGraph.size() == 0);
   // build pivot graph
   for (int i = 0; i < mPivotRows.size(); ++i)
      pivotGraph.emplace_back(std::vector<IndexType> {});
   
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
                             std::stack<IndexType>& result) const
{
   assert(result.size() == 0);
   std::vector<std::vector<IndexType>> pivotGraph;
   std::vector<bool> visited(mPivotRows.size(),false);

   buildPivotGraph(A,pivotGraph);
   
   for (int i = 0; i < mPivotRows.size(); ++i)
      if (!visited[i])
	 sortPivotsWorker(i,pivotGraph,visited,result);

   return;
}

void PivotHelper::sortPivotsWorker(IndexType curVertex,
                                   std::vector<std::vector<IndexType>>& pivotGraph,
                                   std::vector<bool>& visited,
                                   std::stack<IndexType>& result) const
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

