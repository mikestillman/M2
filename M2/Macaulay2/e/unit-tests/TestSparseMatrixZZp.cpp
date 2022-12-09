#include "SparseMatrixZZp.hpp"
#include "timing.hpp"

#include <iostream>
#include <fstream>
#include <gtest/gtest.h>


TEST(SparseMatrixZZp, fromTriple)
{
  M2:: ARingZZpFlint F(101);
  SparseMatrixZZp A(F, 5, 7, {{0,1,1}, {0,4,2}, {0,6,3},
                           {1,3,4},
                           {2,0,5}, {2,2,6}, {2,6,7},
                           {4,0,8},{4,5,9}});
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

TEST(SparseMatrixZZp, trivialPivotTest)
{
  M2:: ARingZZpFlint F(101);
  SparseMatrixZZp A(F, 5, 7, {{ 0,1,1}, {0,4,2}, {0,6,3},
                           {1,3,4},
                           {2,0,5}, {2,2,6}, {2,6,7},
                           {4,0,8},{4,5,9}});
  PivotHelper pivotHelper(7);
  pivotHelper.findTrivialRowPivots(A);
  std::cout << pivotHelper << std::endl;
  pivotHelper.findTrivialColumnPivots(A);
  std::cout << pivotHelper << std::endl;

  SparseMatrixZZp A2(F, 6, 9, {{0,0,1}, {0,2,2}, {0,5,3}, {0,6,4}, {0,8,5},
			      {1,1,1}, {1,2,2}, {1,3,3}, {1,5,4}, {1,7,5},
			      {2,2,1}, {2,3,2}, {2,7,3}, {2,8,4},
			      {3,1,1}, {3,2,2}, {3,4,3},
			      {4,1,1}, {4,3,2}, {4,6,3}, {4,8,4},
			      {5,0,1}, {5,2,2}, {5,4,3}, {5,5,4}, {5,7,5}, {5,8,6}});
  A2.denseDisplay(std::cout);
  
  PivotHelper pivotHelper2(9);
  pivotHelper2.findTrivialRowPivots(A2);
  std::cout << pivotHelper2 << std::endl;
  pivotHelper2.findTrivialColumnPivots(A2);
  std::cout << pivotHelper2 << std::endl;

}


TEST(SparseMatrixZZp, fromTriplesFile)
{
  M2:: ARingZZpFlint F(101);
  std::ifstream infile;
  infile.open("sparsemat-1.txt");
  if (not infile)
    {
      std::cout << "file not opened properly" << std::endl;
      exit(1);
    }
  
  SparseMatrixZZp A(F, infile);

  infile.close();;

  SparseMatrixZZp B(F, 5, 7, {{0,1,1}, {0,4,2}, {0,6,3},
                           {1,3,4},
                           {2,0,5}, {2,2,6}, {2,6,7},
                           {4,0,8}});

  A.denseDisplay(std::cout);
  B.denseDisplay(std::cout);

  // eventually: check that A == B.
}

TEST(SparseMatrixZZp, fromTriplesFile1)
{
  M2:: ARingZZpFlint F(101);
  std::ifstream infile;
  infile.open("/Users/mike/Downloads/10164x1740.sms");
  if (not infile)
    {
      std::cout << "file not opened properly" << std::endl;
      exit(1);
    }
  
  SparseMatrixZZp A(F, infile);

  infile.close();;

  //  A.denseDisplay(std::cout);
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
  // A.denseDisplay(std::cout);
  auto B = A.transpose();
  // std::cout << "and its transpose is: " << std::endl;
  // B.denseDisplay(std::cout);
}

// TEST(SparseMatrixZZp, bigRandomSparseMatrix)
// {
//   M2:: ARingZZpFlint F(101);
//   auto A = SparseMatrixZZp::randomSparseMatrix(F, 50000, 60000, .01);
//   std::cout << "and now lets work on the transpose" << std::endl;
//   auto t1 = now();
//   auto B = A.transpose();
//   std::cout << "transose time: " << seconds(now() - t1) << std::endl;
// }
