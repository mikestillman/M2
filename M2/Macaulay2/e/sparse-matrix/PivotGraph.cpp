#include "SparseMatrixZZp.hpp"
#include "PivotHelper.hpp"
#include "PivotGraph.hpp"

#include <unordered_map>
#include <queue>
#include <vector>
#include <ostream>

void PivotGraph::initialize(const std::vector<Edge>& edges)
{
   for (const auto& e : edges)
     addEdge(e);
}

PivotGraph::PivotGraph(const SparseMatrixZZp& A,
		       const PivotHelper& pivotHelper)
  : mAdjacency(pivotHelper.numPivots(),std::vector<VertexType> {})
{
   std::vector<Edge> edges;
   std::cout << "Determining graph: " << std::endl;
   // this seems to be where almost all time is spent...
   //   need to do this faster.  in order to do that, we need
   //   a way to determine which pivot index (in pivotHelper) a given (r,c) pivot pair corresponds to.
   // for (int i = 0; i < pivotHelper.numPivots(); ++i)
   // {
   //    for (int j = i+1; j < pivotHelper.numPivots(); ++j)
   //    {
   //       if (A.entryPresent(pivotHelper.pivotRow(i),pivotHelper.pivotColumn(j)))
   // 	    edges.push_back(std::make_pair(i,j));
   //       if (A.entryPresent(pivotHelper.pivotRow(j),pivotHelper.pivotColumn(i)))
   // 	    edges.push_back(std::make_pair(j,i));
   //    }
   // }

   for (VertexType i = 0; i < pivotHelper.numPivots(); ++i)
   {
      auto begin = A.cbegin(pivotHelper.pivotRow(i));
      auto end = A.cend(pivotHelper.pivotRow(i));
      for (auto c = begin; c != end; ++c)
      {
   	 if (pivotHelper.pivotColumn(i) != (*c).first && pivotHelper.isPivotColumn((*c).first))
   	 {
   	    // if it is a pivot column, what is its pivot index?
   	    VertexType j = pivotHelper.columnPivotIndex((*c).first);
	    edges.push_back(std::make_pair(i,j));
   	 }
      }
   }
   std::cout << "Number of edges: " << edges.size() << std::endl;
   initialize(edges);
}

void PivotGraph::topologicalSort(std::vector<VertexType> &result) const
{
   assert(result.size() == 0);
   std::unordered_map<VertexType, int> inDegree;
   std::queue<VertexType> queue;
   
   for (auto src : mAdjacency)
      for (auto tgt : src)
         ++inDegree[tgt];
   
   for (int i = 0; i < mAdjacency.size(); ++i)
   {
      if (inDegree[i] == 0)
	 queue.push(i);
   }

   while (!queue.empty())
   {
      VertexType v = queue.front();
      queue.pop();
      result.push_back(v);
      
      for (auto tgt : mAdjacency[v])
      {
	auto& tmp = inDegree[tgt];
	--tmp;
	if (tmp == 0)
	  queue.push(tgt);
      }
   }
   if (result.size() != mAdjacency.size())
   {
      std::cout << "Error: Topological sort not possible." << std::endl;
   }
}
