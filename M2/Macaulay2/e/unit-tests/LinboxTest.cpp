#include <iostream>
#include <memory>
#include <gtest/gtest.h>

#include <givaro/modular.h>
#include <linbox/matrix/sparse-matrix.h>
#include <linbox/solutions/rank.h>

TEST(linbox, zzp)
{
  typedef Givaro::Modular<short> Field;
  typedef LinBox::SparseMatrix<Field> Matrix;
  Field F(101);

  Field::Element a, b, c;
  F.init(a, 2); F.init(b, 3);
  F.mul(c, a, b); // c <- a*b
  //  F.write(std::cout, c);

  Matrix A(F);
  //  std::string filename { "/Users/mike/Downloads/10164x1740.sms" };
  std::string filename { "/Users/mike/Downloads/GL7d14.sms" };
  std::ifstream i { filename };
  A.read(i, LinBox::Tag::FileFormat::MatrixMarket);
  //A.write(std::cout, LinBox::Tag::FileFormat::Pretty);

  size_t r = 38219381;
  LinBox::rank (r, A);
  std::cout << "Rank = " << r << std::endl;
  // Field::Element det;
  // determinant(det, A, blasElimination);
  // F.write(cout << "the determinant is ", det) << endl;
}
