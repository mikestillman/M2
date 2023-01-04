#ifndef _matrixops_hpp
#define _matrixops_hpp

using ZZpElement = M2::ARingZZpFlint::ElementType; // really just long.
using IndexType = int;

class SparseMatrixZZp;
class SparseVector;
class DenseVector;

namespace MatrixOps
{
  void upperUnitriangularSolve(const SparseMatrixZZp& A, const SparseVector& sparse, DenseVector& result);
  void upperUnitriangluarSolve(const SparseMatrixZZp& A, const SparseVector& sparse, SparseVector& result);

  // performs result += cx.  Scatters cx into result
  void scatter(const SparseMatrixZZp& A, const ZZpElement& element, const SparseVector& x, SparseVector& result);
  void scatter(const SparseMatrixZZp& A, const ZZpElement& element, const SparseVector& x, DenseVector& result);
  void scatter(const SparseMatrixZZp& A, const ZZpElement& element, const DenseVector& x, SparseVector& result);
  void scatter(const SparseMatrixZZp& A, const ZZpElement& element, const DenseVector& x, DenseVector& result);

  // performs result += bA where b is either dense or sparse.  Result has same form of b.
  void rowUpdate(const SparseVector& sparse, SparseVector& result, SparseVector& b);
  void rowUpdate(const SparseVector& sparse, SparseVector& result, DenseVector& b);
  void rowUpdate(const SparseVector& sparse, DenseVector& result, SparseVector& b);
  void rowUpdate(const SparseVector& sparse, DenseVector& result, DenseVector& b);
}

#endif

// Local Variables:
// indent-tabs-mode: nil
// End:
