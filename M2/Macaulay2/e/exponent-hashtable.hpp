#ifndef M2_EXPONENT_HASHTABLE_GUARD
#define M2_EXPONENT_HASHTABLE_GUARD

#include <unordered_map>
#include <iostream>
#include <iomanip>

template<typename T1, typename T2>
std::ostream& operator << (std::ostream& o, const std::pair<T1,T2>& p)
{
  return o << "[" << p.first << "," << p.second << "]";
}

template<typename T>
inline void PRINT_ELEMENTS(const T& collection, const std::string& prefix)
{
  std::cout << prefix;
  for (const auto& elem : collection) {
    std::cout << elem << ' ';
  }
  std::cout << std::endl;
}

template<typename T>
void printHashTableState(const T& cont)
{
  // basic layout data
  std::cout << "size:            " << cont.size() << std::endl;
  std::cout << "buckets:         " << cont.bucket_count() << std::endl;
  std::cout << "load factor:     " << cont.load_factor() << std::endl;
  std::cout << "max load factor: " << cont.max_load_factor() << std::endl;

  // iterator category
  if (typeid(typename std::iterator_traits<typename T::iterator>::iterator_category)
      == typeid(std::bidirectional_iterator_tag))
    {
      std::cout << "chaining style:  doubly-linked" << std::endl;
    }
  else
    {
      std::cout << "chaining style:  singly-linked" << std::endl;
    }

  // elements per bucket
  std::cout << "data: " << std::endl;
  for (auto idx=0ul; idx != cont.bucket_count(); ++idx)
    {
      std::cout << " b[" << std::setw(2) << idx << "]: ";
      for (auto pos = cont.begin(idx); pos != cont.end(idx); ++pos)
        {
          std::cout << *pos << " ";
        }
      std::cout << std::endl;
    }
}

using ExponentVector = int*;

class ExponentConfig
{
public:
  using Key = ExponentVector;
  using Value = int;

  ExponentConfig(int nvars) : mNumVars(nvars) {}
  
  std::size_t hash(const Key& e) const
  {
    std::cout << "hash" << std::endl;
    std::size_t result = 0;
    for (int i=0; i<mNumVars; i++)
      result = 17*result + e[i];
    return result;
  }

  bool keysEqual(const Key& e1, const Key& e2) const
  {
    std::cout << "equal" << std::endl;
    for (int i=0; i<mNumVars; ++i)
      if (e1[i] != e2[i]) return false;
    return true;
  }

  //  std::ostream& show(std::ostream& o, const Key& e) const
  //  {
  //  }
  
  const Value notFoundValue = -1;
  
  std::size_t operator() (const Key& e) const { return hash(e); }
  bool operator() (const Key& e1, const Key& e2) const { return keysEqual(e1,e2); }
private:
  int mNumVars;
};


template<typename Configuration>
class BasicHashTable
{
public:
  using Conf = Configuration;
  using Key = typename Conf::Key;
  using Value = typename Conf::Value;
  using Map = std::unordered_map<Key,
                                 Value,
                                 Conf,
                                 Conf
                                 >;

  BasicHashTable(Conf conf, int size_hint)
    : mConf(conf),
      mMap(size_hint,
           mConf,
           mConf) {
    mMap.max_load_factor(.3);
  }
    
  size_t size() { return mMap.size(); }

  Value find(const Key& v) const {
    auto i = mMap.find(v);
    if (i == mMap.end()) return mConf.notFoundValue;
    std::cout << *i << std::endl;
    return i->second;
  }

  Conf& configuration() { return mConf; }
  const Conf& configuration() const { return mConf; }
  Map& hashtable() { return mMap; }
  const Map& hashtable() const { return mMap; }
private:
  Conf mConf;
  Map mMap;
};

#include "mathic/HashTable.h"

using MExponentHashTable = mathic::HashTable<ExponentConfig>;

#endif

/*
// Local Variables:
// compile-command: "make -C $M2BUILDDIR/Macaulay2/e "
// indent-tabs-mode: nil
// End:
*/
