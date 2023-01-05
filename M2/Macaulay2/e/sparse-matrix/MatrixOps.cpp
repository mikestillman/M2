#include "MatrixOps.hpp"
#include "SparseMatrixZZp.hpp"
#include "Vectors.hpp"

// some utility functions needed:
// rowToSparseVector
// rowToDenseVector

// do we need to make an allocator for the vector types?

namespace MatrixOps
{
  // solves result*A = a.  Requires A to be a block 2x2 matrix with a upper unitriangular matrix in
  // top left corner.
  void upperUnitriangluarSolve(const SparseMatrixZZp& A, IndexType numPivots, const SparseVector& a, SparseVector& result)
  {
  }

  void upperUnitriangularSolve(const SparseMatrixZZp& A, IndexType numPivots, const SparseVector& a, DenseVector& result)
  {
    result.resize(numPivots);
    // initialize result with the values in a
    result.fill(0);
    for (auto c = a.cbegin(); c != a.cend(); ++c)
       result[(*c).first] = (*c).second;
    
    for (IndexType r = 0; r < numPivots; ++r)
    {
       auto c = A.cbegin(r);
       ++c;
       for ( /* already initialized */ ; c != A.cend(r); ++c)
       {
	  if ((*c).first > numPivots) break;
	  result[(*c).first] -= ((*c).second) * (result[r]);
       }
    }
  }

  void upperUnitriangluarSolve(const SparseMatrixZZp& A, IndexType numPivots, const DenseVector& a, SparseVector& result)
  {
  }

  void upperUnitriangularSolve(const SparseMatrixZZp& A, IndexType numPivots, const DenseVector& a, DenseVector& result)
  {
  }

  // performs result += cx.  Scatters cx into result
  void scatter(SparseVector& result, const ZZpElement& element, const SparseVector& x)
  {
     // would have to interlace result with nonzero entries in x.
  }

  void scatter(SparseVector& result, const ZZpElement& element, const SparseMatrixZZp& A, IndexType row)
  {
     // would have to interlace result with nonzero entries in x.
  }

  void scatter(SparseVector& result, const ZZpElement& element, const DenseVector& x)
  {
     // would have to interlace result with nonzero entries in x.
  }

  void scatter(DenseVector& result, const ZZpElement& element, const SparseVector& x)
  {
     for (auto c = x.cbegin(); c != x.cend(); ++c)
        result[(*c).first] += element * ((*c).second);
  }

  void scatter(DenseVector& result, const ZZpElement& element, const SparseMatrixZZp& A, IndexType row)
  {
     for (auto c = A.cbegin(row); c != A.cend(row); ++c)
        result[(*c).first] += element * ((*c).second);
  }

  void scatter(DenseVector& result, const ZZpElement& element, const DenseVector& x)
  {
     for (auto c = 0; c < x.size(); ++c)
     {
        if (x[c] == 0) continue;
        result[c] += element * x[c];
     }
  }

  // performs result += bA where b is either dense or sparse.  Result has same form of b.
  void rowUpdate(SparseVector& result, const SparseMatrixZZp& A, SparseVector& b)
  {
  }

  void rowUpdate(SparseVector& result, const SparseMatrixZZp& A, DenseVector& b)
  {
  }

  void rowUpdate(DenseVector& result, const SparseMatrixZZp& A, SparseVector& b)
  {
     for (auto c = b.cbegin(); c != b.cend(); ++c)
        scatter(result, (*c).second, A, (*c).first);
  }

  void rowUpdate(DenseVector& result, const SparseMatrixZZp& A, DenseVector& b)
  {
     for (auto c = 0; c < b.size(); ++c)
     {
        if (b[c] == 0) continue;
	scatter(result, b[c], A, c);
     }
  }

  void schurComplement(const SparseMatrixZZp& A, SparseMatrixZZp& result)
  {
  }

  IndexType rank(const SparseMatrixZZp& A)
  {
     return 0;
  }
  
}
