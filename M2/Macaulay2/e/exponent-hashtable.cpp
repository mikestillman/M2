// g++ --std=c++11 -I~/src/M2-new/M2/submodules/mathic/src/ -Wall exponent-hashtable.cpp -o exponent-hashtable-test
#include "exponent-hashtable.hpp"

int main(int argc, char** argv)
{
  MExponentHashTable E2(ExponentConfig(3), 10);
  std::cout << E2.name() << std::endl;
  
  std::cout << "new version" << std::endl;
  BasicHashTable<ExponentConfig> E(ExponentConfig(3), 10);
  int expmemory[30] = {0,1,1,
                       1,2,3,
                       0,1,1,
                       1,0,0,
                       0,0,0,
                       3,6,1,
                       1,1,1,
                       2,3,4,
                       9,9,9,
                       1,0,0};

  using Map = BasicHashTable<ExponentConfig>::Map;
  Map hashtab = E.hashtable();

  auto hashtab2 = BasicHashTable<ExponentConfig>(ExponentConfig(3), 10).hashtable();
  ExponentVector exps[10];
  for (int i=0; i<10; i++)
    {
      exps[i] = &expmemory[3*i];
    }

#if 1  
  for (int i=0; i<10; i++)
    {
      E.hashtable().emplace(exps[i], i);
    }
#endif
#if 0
  for (int i=0; i<10; i++)
    {
      E.hashtable()[exps[i]] = i;
    }
#endif
#if 1
  std::cout << "about to do find" << std::endl;
  for (int i=0; i<10; i++)
    {
      exps[i][0] += 10;
      if (-1 == E.find(exps[i]))
        E.hashtable().emplace(exps[i],i);
    }
#endif
  PRINT_ELEMENTS(E.hashtable(), "hash: ");
  std::cout << "state of E: " << std::endl;
  printHashTableState(E.hashtable());

  std::cout << "state of hashtab: " << std::endl;  
  printHashTableState(hashtab);
  std::cout << "state of hashtab2: " << std::endl;  
  printHashTableState(hashtab2);
  

  
  return 0;
}

// "make -C $M2BUILDDIR/Macaulay2/e "

/*
// Local Variables:
// compile-command: "g++ --std=c++11 -I ~/src/M2-new/M2/submodules/mathic/src -I ~/src/M2-new/M2/submodules/memtailor/src -L/Users/mike/src/M2-new/M2/BUILD/mike/builds.tmp/darwin64-gcc4.9/submodules/memtailor/.libs  -L/Users/mike/src/M2-new/M2/BUILD/mike/builds.tmp/darwin64-gcc4.9/submodules/mathic/.libs exponent-hashtable.cpp -lmathic -lmemtailor -o exponent-hashtable-test" 
// indent-tabs-mode: nil
// End:
*/
