--- status: DRAFT
--- author(s): L. Gold, and Dan Grayson
--- notes:  

undocumented {
    (degreesRing,   PolynomialRing), (degreesRing,   QuotientRing), (degreesRing,   Module), (degreesRing, LeftIdeal),
    (degreesMonoid, PolynomialRing), (degreesMonoid, QuotientRing), (degreesMonoid, Module),
    }

doc ///
Node
  Key
     degreesRing
    (degreesRing, Ring)
    (degreesRing, Monoid)
     degreesMonoid
    (degreesMonoid, Ring)
    (degreesMonoid, Monoid)
  Headline
    the ring or monoid of degrees
  Usage
    degreesRing A
    degreesMonoid A
  Inputs
    A:{Ring,Monoid}
  Outputs
    :{PolynomialRing,Monoid} -- a Laurent polynomial ring or monoid with inverses
  Description
    Text
      Given a ring or monoid @TT "A"@ with @TO2(degreeLength, "degree length")@ $n$,
      @TT "degreesRing"@ and @TT "degreesMonoid"@ produce a Laurent polynomial ring
      or monoid of Laurent monomials in $n$ variables, respectively, whose monomials
      correspond to the degrees of elements of @TT "A"@. The variable has no subscript
      when $n=1$.
    Example
      A = ZZ[x,y];
      degreesRing A
      degreesMonoid A
      degrees oo
      heft A
      R = QQ[x,y, Degrees => {{1,-2}, {2,-1}}];
      degreesRing R
      degreesMonoid R
      degrees oo
      heft R
      S = QQ[x,y, Degrees => {-2,1}];
      degreesRing S
      degreesMonoid S
      degrees oo
      heft S
    Text
      Note that in the last example the ring does not have a @TO2("heft vectors", "heft vector")@.

      @TO2(hilbertSeries, "Hilbert series")@ and @TO2(hilbertPolynomial, "polynomials")@ of modules
      over @TT "A"@ are elements of its degrees ring over @TO "ZZ"@.  The monomial ordering is chosen
      so that the Hilbert series, which has an infinite number of terms, is bounded above by the weight.
      Elements of this ring are also used as variables for Poincare polynomials generated by @TO "poincare"@
      and @TO "poincareN"@.
    Example
      R = QQ[x,y, Degrees => {{1,-2,0}, {2,-1,1}}];
      use degreesRing R
      hilbertSeries module ideal vars R
      (1+T_1+T_2^2)^3 -* no-capture-flag *-
  SeeAlso
    use
    heft
    poincare
    poincareN
    hilbertFunction
    hilbertPolynomial
    hilbertSeries
    degreeLength
    [monoid, DegreeRank]
  Subnodes
    (degreesRing, List)

Node
  Key
    (degreesRing, List)
    (degreesRing, ZZ)
    (degreesMonoid, List)
    (degreesMonoid, ZZ)
  Headline
    the ring or monoid of degrees
  Usage
    degreesRing L
    degreesMonoid L
    degreesRing n
    degreesMonoid n
  Inputs
    :{List,ZZ} -- see @TO "heft vectors"@ or @TO degreeLength@
  Outputs
    A:{Monoid,PolynomialRing}
      a monoid of Laurent monomials or ring of Laurent polynomials.
  Description
    Text
      These functions produce either a monoid of Laurent monomials or Laurent polynomial
      ring $A$ in @TT "n"@ variables, where @TT "n"@ is the length of the list @TT "L"@,
      which is typically a @TO2("heft vectors", "heft vector")@. Each monomial in the
      output corresponds to a degree vector for a ring with heft vector @TT "L"@ or
      degree length @TT "n"@ and no heft vector.

      When a list is given, the variables of the output have degrees given by the
      elements of @TT "L"@ and weights are the negative of the degrees.
      When an integer is given, then the number of variables is @TT "n"@,
      the degrees are all @TT "{}"@, and the weights are all @TT "-1"@.
    Example
      degreesMonoid {1,2,3}
      degreesMonoid 3
    Text
      The monomial ordering used in the degrees ring is @TT "RevLex"@ so the polynomials
      in it will be displayed with the smallest exponents first, because such polynomials
      are often used as Hilbert series.

      Assign the degrees ring to a global variable or call @TO(use, Monoid)@ to assign
      the indeterminates of the ring or monoid to global variables.
    Example
      assert instance(T_0, IndexedVariable)
      use degreesMonoid 3
      assert instance(T_0, degreesMonoid 3)
      A = degreesRing 4
      assert instance(T_0, degreesRing 4)
  SeeAlso
    use
    heft
    degreeLength
    "division in polynomial rings with monomials less than 1"
///
