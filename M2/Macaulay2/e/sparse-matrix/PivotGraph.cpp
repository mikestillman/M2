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
  : mAdjacency(pivotHelper.numPivots(),
	       std::vector<VertexType> {})
{
   std::vector<Edge> edges;

   for (VertexType i = 0; i < pivotHelper.numPivots(); ++i)
   {
      auto begin = A.cbeginColumns(pivotHelper.pivotRow(i));
      auto end = A.cendColumns(pivotHelper.pivotRow(i));
      for (auto c = begin; c != end; ++c)
      {
   	 if (pivotHelper.pivotColumn(i) != (*c) && pivotHelper.isPivotColumn(*c))
   	 {
   	    // if it is a pivot column, what is its pivot index?
   	    VertexType j = pivotHelper.columnPivotIndex(*c);
	    edges.push_back(std::make_pair(i,j));
   	 }
      }
   }
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
