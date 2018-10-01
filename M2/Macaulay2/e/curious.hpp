template <class ConcreteRing>
class RingInterface
{
  using Element = typename ConcreteRing::Element;

  Element add(Element a, Element b) {
    return static_cast<ConcreteRing*>(this)->add(a, b);
  }
};

class Ring
{
};

class PolynomialRing : public RingInterface<PolynomialRing>
{
  using Element = Polynomial;

  Element add(Element a, Element b) {
    for (i..) {
    }
  }
};

class QQ : public Ring<QQ>
{
  using Element = mpq_ptr;
  
  Element add(Element a, Element b) {
    for (i..) {
    }
  }
};


template <class ConcreteRing>
class RingElement
{
  using ElementType = ConcreteRing::ElementType;

  RingElement (Ring<ConcreteRing>, ElementType);
  RingElement operator+(const RingElement &a) const;
};


 *   RingElementArray (Ring<ConcreteRing>, vector of ElementType's)
