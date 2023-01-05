#ifndef _matrixops_hpp
#define _matrixops_hpp

#include "aring-zzp-flint.hpp"

using ZZpElement = M2::ARingZZpFlint::ElementType; // really just long.
using IndexType = int;

class SparseMatrixZZp;
class SparseVector;
class DenseVector;

// TODO: Go through these, brought over from SparseMatrixZZp header

  // Constructors, change of representation
  // read/write to/from file

  // Transpose
  // Matrix/Vector Multiplication (v*A, A*B, ...)

  // sparse PLUQ decomposition:
  // Wiedemann
  // Lanczos
  // rank computation

  // finding a good matching...

namespace MatrixOps
{
  // solves result*A = a.  Requires A to be a matrix with a upper unitriangular matrix in
  // top left corner with numPivots many pivots.
  void upperUnitriangluarSolve(const SparseMatrixZZp& A, IndexType numPivots, const SparseVector& a, SparseVector& result);
  void upperUnitriangularSolve(const SparseMatrixZZp& A, IndexType numPivots, const SparseVector& a, DenseVector& result);
  void upperUnitriangluarSolve(const SparseMatrixZZp& A, IndexType numPivots, const DenseVector& a, SparseVector& result);
  void upperUnitriangularSolve(const SparseMatrixZZp& A, IndexType numPivots, const DenseVector& a, DenseVector& result);

  // performs result += cx.  Scatters cx into result
  void scatter(SparseVector& result, const ZZpElement& element, const SparseVector& x);
  void scatter(SparseVector& result, const ZZpElement& element, const DenseVector& x);

  void scatter(SparseVector& result, const ZZpElement& element, const SparseMatrixZZp& A, IndexType row);

  void scatter(DenseVector& result, const ZZpElement& element, const SparseVector& x);
  void scatter(DenseVector& result, const ZZpElement& element, const DenseVector& x);

  void scatter(DenseVector& result, const ZZpElement& element, const SparseMatrixZZp& A, IndexType row);

  // performs result += bA where b is either dense or sparse.  Result has same form of b.
  void rowUpdate(SparseVector& result, const SparseMatrixZZp& sparse, SparseVector& b);
  void rowUpdate(SparseVector& result, const SparseMatrixZZp& sparse, DenseVector& b);
  void rowUpdate(SparseVector& result, const SparseMatrixZZp& sparse, SparseVector& b);
  void rowUpdate(SparseVector& result, const SparseMatrixZZp& sparse, DenseVector& b);

  void schurComplement(const SparseMatrixZZp& A, SparseMatrixZZp& result);

  IndexType rank(const SparseMatrixZZp& A);
  
}

#endif

// Local Variables:
// indent-tabs-mode: nil
// End:
