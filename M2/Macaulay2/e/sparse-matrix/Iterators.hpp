#ifndef _iterators_hpp
#define _iterators_hpp


template<typename Iter1, typename Iter2>
class DiagonalIter
{
  // Assumption: both iterators should point to valid memory simultaneously
  // even after each increment.
private:
  Iter1 mIter1;
  Iter2 mIter2;

  using Value1 = decltype(* mIter1);
  using Value2 = decltype(* mIter2);
public:
  DiagonalIter(Iter1 iter1, Iter2 iter2)
    : mIter1(iter1),
      mIter2(iter2)
  {
  }
  
  bool operator==(DiagonalIter j)
  {
    return (mIter1 == j.mIter1 and mIter2 == j.mIter2);
  }

  bool operator!=(DiagonalIter j)
  {
    return (mIter1 != j.mIter1 or mIter2 != j.mIter2);
  }
  
  DiagonalIter operator++()
  {
    ++mIter1;
    ++mIter2;
    return *this;
  }

  // operator*: returns (column, (nonzero) entry at given row and this column)
  std::pair<Value1, Value2> operator*()
  {
    return {*mIter1, *mIter2};
  }
};

#endif

// Local Variables:
// indent-tabs-mode: nil
// End:
