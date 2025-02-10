#include <gmp.h>
#include <memory>
#include <iostream>

namespace M2Engine {

  /// The abstract Ring class
  /// 
  /// TODO: should be immutable, but finalized
  /// This is an immutable class.
  ///
  /// this translates to a RawRing type in the front enf.
  /// generally called from the d language.

  class RingElement;

  class Ring /*: public MutableEngineObject */ {
  public:
    virtual ~Ring() {}
    virtual RingElement* fromInt64(int64_t val) const = 0;
  };

  template<typename RT>
  class ConcreteRing : public Ring {
  private:
    std::unique_ptr<RT> mRing;
  public:
    virtual ~ConcreteRing() {}
    ConcreteRing(std::unique_ptr<RT> R) : mRing(std::move(R)) {}
    RingElement* fromInt64(int64_t val) const override {
    }
  };
  
  // This is completely abstract class
  class RingElement
  {
  private:
    Ring* mRing;

  public:
    
  };

  class RingZZp {
  private:
    uint64_t mCharacteristic;
  public:
    using ElementType = uint64_t;
    RingZZp(uint64_t characteristic) : mCharacteristic(characteristic) {}

    auto fromInt64(int64_t val) -> ElementType
    {
      return val % mCharacteristic;
    }

    void setFromInt64(ElementType& result, int64_t val)
    {
      result = val % mCharacteristic;
    }
  };

  template <class RT>
  class DeletableElementType
  {
  public:
    class ElementTypeArray
    {
      size_t mSize;
      std::unique_ptr<typename RT::RawElementType[]> mElements;
    public:
    };
  };
  
  class RingZZ : public DeletableElementType<RingZZ> {
  public:
    RingZZ() = default;

  public:
    using RawElementType = __mpz_struct;
    class ElementType
    {
    private:
      friend class RingZZ;
      RawElementType mValue;
    public:
      ElementType()
      {
        mpz_init(&mValue);
      }

      ~ElementType()
      {
        mpz_clear(&mValue);
      }
    };
      
    auto fromInt64(int64_t val) -> ElementType
    {
      
      ElementType result;
      mpz_set_si(&result.mValue, val); // TODO: mpz takes int64_t...
      return result;
    }

    void setFromInt64(ElementType& result, int64_t val)
    {
      mpz_set_si(&result.mValue, val);
    }
  };
  

  template<class RT>
  class UnivariatePolynomialRing {
  private:
    const RT* mCoefficientRing;
  public:
    using CoefficientElementType = typename RT::ElementType;
    using ElementType = std::vector<CoefficientElementType>;
    UnivariatePolynomialRing(const RT* coefficientRing) : mCoefficientRing(coefficientRing) {}
  };
  

  ConcreteRing<RingZZp>* rawZZpRing(long charac)
  {
    return new ConcreteRing<RingZZp>(std::make_unique<RingZZp>(charac));
  }
}  // M2Engine namespace

using namespace M2Engine;
int main()
{
  Ring* R = rawZZpRing(5);
  RingElement* f = R->fromInt64(2);
  //  RingElement* g = RingElement(R, 2);
  std::cout << "at end of main\n";
}
