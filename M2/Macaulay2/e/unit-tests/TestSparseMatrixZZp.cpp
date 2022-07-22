#include "SparseMatrixZZp.hpp"
#include "timing.hpp"

#include <iostream>
#include <gtest/gtest.h>

TEST(SparseMatrixZZp, fromTriple)
{
  M2:: ARingZZpFlint F(101);
  SparseMatrixZZp A(F, 5, 7, {{0,1,1}, {0,4,2}, {0,6,3},
                           {1,3,4},
                           {2,0,5}, {2,2,6}, {2,6,7},
                           {4,0,8}});
  A.dump(std::cout);
  
  for (auto r=0; r < A.numRows(); ++r)
    {
      for (auto i = A.cbegin(r); i != A.cend(r); ++i)
        {
          auto t = *i;
          std::cout << "[" << r << "," << t.first << "," << t.second << "] ";
        }
      std::cout << std::endl;
    }

  A.denseDisplay(std::cout);
}

TEST(SparseMatrixZZp, fromUnsortedTriple)
{
  M2:: ARingZZpFlint F(101);
  SparseMatrixZZp A(F, 5, 7, {{0,6,3},
                           {1,3,4}, {2,6,7},
                           {2,0,5}, {2,2,6}, {0,4,2}, 
                           {0,1,1}, {4,0,8}});
  A.dump(std::cout);
  
  for (auto r=0; r < A.numRows(); ++r)
    {
      for (auto i = A.cbegin(r); i != A.cend(r); ++i)
        {
          auto t = *i;
          std::cout << "[" << r << "," << t.first << "," << t.second << "] ";
        }
      std::cout << std::endl;
    }

  A.denseDisplay(std::cout);
}

TEST(SparseMatrixZZp, zeroMatrix)
{
  M2:: ARingZZpFlint F(101);
  SparseMatrixZZp A(F, 0, 0, {{}});

  for (auto r=0; r < A.numRows(); ++r)
    {
      for (auto i = A.cbegin(r); i != A.cend(r); ++i)
        {
          auto t = *i;
          std::cout << "[" << r << "," << t.first << "," << t.second << "] ";
        }
      std::cout << std::endl;
    }
}

TEST(SparseMatrixZZp, zeroEntries)
{
  M2:: ARingZZpFlint F(101);
  SparseMatrixZZp A(F, 3, 5, {});

  A.dump(std::cout);
  
  for (auto r=0; r < A.numRows(); ++r)
    {
      for (auto i = A.cbegin(r); i != A.cend(r); ++i)
        {
          auto t = *i;
          std::cout << "[" << r << "," << t.first << "," << t.second << "] ";
        }
      std::cout << std::endl;
    }
}

TEST(SparseMatrixZZp, transpose)
{
  M2:: ARingZZpFlint F(101);
  SparseMatrixZZp A(F, 5, 7, {{0,1,1}, {0,4,2}, {0,6,3},
                           {1,3,4},
                           {2,0,5}, {2,2,6}, {2,6,7},
                           {4,0,8}});

  A.denseDisplay(std::cout);

  std::cout << "Now for the transpose:" << std::endl;
  SparseMatrixZZp B = A.transpose();
  B.denseDisplay(std::cout);
}

TEST(SparseMatrixZZp, randomSparseMatrix)
{
  M2:: ARingZZpFlint F(101);
  auto A = SparseMatrixZZp::randomSparseMatrix(F, 50, 60, .1);
  A.denseDisplay(std::cout);
  auto B = A.transpose();
  std::cout << "and its transpose is: " << std::endl;
  B.denseDisplay(std::cout);
}

TEST(SparseMatrixZZp, bigRandomSparseMatrix)
{
  M2:: ARingZZpFlint F(101);
  auto A = SparseMatrixZZp::randomSparseMatrix(F, 50000, 60000, .01);
  std::cout << "and now lets work on the transpose" << std::endl;
  auto t1 = now();
  auto B = A.transpose();
  std::cout << "transose time: " << seconds(now() - t1) << std::endl;
}
