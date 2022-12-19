#ifndef _pivot_graph_hpp_
#define _pivot_graph_hpp_

#include "SparseMatrixZZp.hpp"
#include "PivotHelper.hpp"

using Edge = std::pair<unsigned int, unsigned int>;

using VertexType = unsigned int;

class PivotGraph {
private:

   std::vector<std::vector<VertexType>> mAdjacency;

public:
   PivotGraph(const SparseMatrixZZp& A,
              const PivotHelper& pivotHelper);

   PivotGraph(const std::vector<Edge>& edges,
              unsigned int N) :
     mAdjacency(N,std::vector<VertexType> {}) { initialize(edges); }

   void addEdge(const Edge& edge) { mAdjacency[edge.first].push_back(edge.second); }

   void topologicalSort(std::vector<VertexType> &result) const;

private:
   void initialize(const std::vector<Edge>& edges);
};

#endif

// Local Variables:
// indent-tabs-mode: nil
// End:
