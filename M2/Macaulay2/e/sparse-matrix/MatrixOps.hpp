#ifndef _matrixops_hpp
#define _matrixops_hpp

using ZZpElement = M2::ARingZZpFlint::ElementType; // really just long.
using IndexType = int;

class SparseMatrixZZp;
class SparseVector;
class DenseVector;

// TODO: Go Through These, brought over from SparseMatrixZZp header

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
  // solves result*A = a.  Requires A to be a block 2x2 matrix with a upper unitriangular matrix in
  // top left corner.
  void upperUnitriangluarSolve(const SparseMatrixZZp& A, const SparseVector& a, SparseVector& result);
  void upperUnitriangularSolve(const SparseMatrixZZp& A, const SparseVector& a, DenseVector& result);
  void upperUnitriangluarSolve(const SparseMatrixZZp& A, const DenseVector& a, SparseVector& result);
  void upperUnitriangularSolve(const SparseMatrixZZp& A, const DenseVector& a, DenseVector& result);

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

  // What about: A+B, A-B, A += c*D, A*B, etc...

  void schurComplement(const SparseMatrix& A, SparseMatrix& result);

  IndexType rank(const SparseMatrix& A);
  
}

#endif

// Local Variables:
// indent-tabs-mode: nil
// End:
