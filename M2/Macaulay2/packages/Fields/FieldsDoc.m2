doc ///
  Key
    Fields
  Headline
    general fields
  Description
    Text
      A {\it field} in Macaulay2 is a ring $F$  of the form $F = K(t_0, \ldots, t_{r-1})[a_0, \ldots, a_{s-1}]/I$,
      where $I$ is zero-dimensional prime ideal, and $K$ is a basic field: either a prime field, or a finite field.

      Not all fields are created this way, but we say that $F$ is in {\bf normal form} if it is defined in the above manner.

      This package provides methods for working with fields.  Typically, Macaulay2 keeps fields in normal form.
    Example
     R = ZZ/5
    Text
      @SUBSECTION "Constructing fields"@
    Text
      @UL {
          TO field,
          TO adjoinRoot,
          TO splittingField,
          TO baseField,
          TO getCoefficientField
          }@
    Text
      @SUBSECTION "Recognizing fields"@
    Text
      @UL {
          TO isFieldInNormalForm,
          TO isBasicField,
          TO isPrimeField,
          TO isFiniteField,
          TO isFractionField,
          TO isFiniteExtensionField
          }@
    Text
      @SUBSECTION "Inspecting a field"@
    Text
      @UL {
          TO fieldGens,
          TO fieldInfo,
          TO displayFieldInfo,
          TO fieldInclusion,
          TO inducedMapOnFields,
          TO useTower
          }@
    Text
      @SUBSECTION "Extensions and their elements"@
    Text
      @UL {
          TO extensionDegree,
          TO extensionBasis,
          TO coeffsInBasis,
          TO minimalPolynomial,
          TO multiplicationMap,
          TO (randomElement, Ring)
          }@
    Text
      @SUBSECTION "Greatest common divisors"@
    Text
      @UL {
          TO monicGCD,
          TO monicGCDNaive,
          TO monicGCDModular
          }@
    Text
      @SUBSECTION "Factorization"@
    Text
      @UL {
          TO factorData,
          TO factors,
          TO monicFactorData,
          TO monicFactors,
          TO squareFreeFactors,
          TO distinctDegreeFactors,
          TO isIrreducible,
          TO prettyFactor
          }@
    Text
      @SUBSECTION "Contents, denominators and associates"@
    Text
      @UL {
          TO fieldContent,
          TO mydenominator,
          TO denominatorRing,
          TO numeratorMap,
          TO primitiveAssociate,
          TO monicAssociate,
          TO makeMonic
          }@
  Caveat
  SeeAlso
    "creating a field"
    "GCD's over a field"
    "factoring polynomials over a field"
    "extension fields"
    "working with multiple fields"
///

doc ///
  Key
    "creating a field"
  Headline
    ways to create fields
  Description
    Text
      One can create prime fields in the following manner.
    Example
      F1 = ZZ/13
      F2 = QQ
      nextPrime 2^40
      P = 1099511627791
      isPrime P

      F3 = ZZ/P
    Text
      Use @TO GF@ to create non-prime finite fields.
    Example
      F4 = GF(3^2, Variable => a)
      a^2+2*a-1
      C = ZZ/3[x]
      --minimalPolynomial(a, C) -- doesn't work yet.
    Text
      Creating extension fields
    Example
      A = ZZ/3[a]
      B = field(A/(a^2+2*a-1))
      minimalPolynomial(a, C)

      A1 = QQ[a]
      B1 = field(A1/(a^2+2*a-1))
      describe B1
      R = B1[x]
      f1 = (x^2-a*x-13)
      g1 = (x^3-a*x-17)
      factors f1
      h = f1*g1
      factors h
      assert(monicGCD(f1*g1^2, f1^3) == f1)
    Text
  SeeAlso
    field
    adjoinRoot
    splittingField
    "Fields"
///

doc ///
  Key
    "extension fields"
  Headline
    working with a finite extension and its elements
  Description
    Text
      A field in normal form has the shape
      $K(t_0, \ldots, t_{r-1})[a_0, \ldots, a_{s-1}]/I$.  The functions
      described here concern the finite part: the extension of the rational
      function field $K(t_0, \ldots, t_{r-1})$ cut out by $I$.

      Extensions are usually created with @TO field@, @TO adjoinRoot@ or
      @TO splittingField@.  Its degree and a vector space basis are given by
      @TO extensionDegree@ and @TO extensionBasis@.
    Example
      K = field(QQ[a]/(a^3-2))
      extensionDegree K
      extensionBasis K
    Text
      An element of the extension can be expanded in that basis with
      @TO coeffsInBasis@.
    Example
      coeffsInBasis(a^2+3*a-1)
    Text
      Multiplication by a fixed element is a linear map on this basis; its
      matrix is returned by @TO multiplicationMap@.  For $a$ itself this is
      the companion matrix of $x^3-2$.
    Example
      multiplicationMap a
    Text
      The characteristic behaviour of an individual element is captured by
      its minimal polynomial over the base, computed by
      @TO minimalPolynomial@.  The second argument is the univariate
      polynomial ring in which to return the answer.
    Example
      P = QQ[T]
      minimalPolynomial(a, P)
      minimalPolynomial(a^2, P)
      minimalPolynomial(1+a, P)
    Text
      A random element of the extension is produced by
      @TO (randomElement, Ring)@.
    Example
      assert(ring randomElement K === K)
    Text
      The extension need not be presented by a single generator.  Here is
      $\QQ(\sqrt 2, \sqrt 3)$, of degree four.
    Example
      K2 = field(QQ[b1,b2]/(b1^2-2, b2^2-3))
      extensionDegree K2
      extensionBasis K2
    Text
      Even so, individual elements have minimal polynomials over $\QQ$, and
      some of them are primitive for the whole extension: $\sqrt 2 + \sqrt 3$
      has degree four, so it generates.
    Example
      minimalPolynomial(b1, P)
      minimalPolynomial(b1+b2, P)
    Text
      A field with no finite part, such as a rational function field, has
      extension degree one.
    Example
      K3 = field(QQ[t])
      extensionDegree K3
      extensionBasis K3
    Text
      Transcendental and algebraic generators can be combined.  The
      transcendental ones are reported by @TO fieldGens@ along with the
      algebraic ones, while @TO extensionDegree@ counts only the finite part.
    Example
      K4 = field(K3[z]/(z^3-t))
      extensionDegree K4
      extensionBasis K4
      fieldGens K4
      baseField K4
  SeeAlso
    field
    adjoinRoot
    splittingField
    extensionDegree
    extensionBasis
    coeffsInBasis
    minimalPolynomial
    multiplicationMap
    "working with multiple fields"
///

doc ///
  Key
    "GCD's over a field"
  Headline
    greatest common divisors of univariate polynomials over a field
  Description
    Text
      @TO monicGCD@ computes the greatest common divisor of univariate
      polynomials over a field in normal form (see @TO field@).
    Example
      K = field(QQ[a]/(a^3+a+1))
      R = K[x]
      f = (x^2-a*x-1)*(x+a)^3
      g = (x^2-a*x-1)*(x^3+a)
      monicGCD(f, g)
    Text
      Scaling the inputs does not change the answer, and coprime polynomials
      give 1.
    Example
      assert(monicGCD(3*f, 5*g) == monicGCD(f, g))
      monicGCD(x+a, x+a+1)
    Text
      Several polynomials can be handled at once by passing a list.
    Example
      monicGCD {f, g, (x^2-a*x-1)*x}
    Text
      Two strategies are available.  The default, {\tt "Modular"}, reduces
      modulo several primes, applies the Chinese Remainder Theorem, and lifts
      back by rational reconstruction; {\tt "Naive"} runs the classical
      Euclidean algorithm.  They may also be called directly as
      @TO monicGCDModular@ and @TO monicGCDNaive@.
    Example
      monicGCD(f, g, Strategy => "Naive")
      assert(monicGCD(f, g, Strategy => "Naive") == monicGCD(f, g, Strategy => "Modular"))
      assert(monicGCDNaive(f, g) == monicGCDModular(f, g))
    Text
      If one argument is zero, the other is returned unchanged -- so in that
      one case the result need not be monic.
    Example
      monicGCD(3*f, 0_R)
    Text
      Everything works over a finite field and its extensions as well.
    Example
      Kp = field((ZZ/32003)[b]/(b^2+1))
      Rp = Kp[x]
      monicGCD((x^2+b*x+1)*(x-b), (x^2+b*x+1)*(x+2))
    Text
      Over a tower involving transcendental variables, the representative
      returned is the primitive associate of the monic GCD, that is, the
      denominators have been cleared.  Apply @TO makeMonic@ to see the monic
      one.
    Example
      K0 = field(QQ[t])
      K1 = field(K0[z]/(z^2-t))
      R1 = K1[x]
      useTower R1
      f1 = (x+z)*(x - 2*t*z/3 + 5/t)
      g1 = (z*x+1)*(x - 2*t*z/3 + 5/t)
      h1 = monicGCD(f1, g1)
      makeMonic h1
      assert(makeMonic h1 == x - 2*t*z/3 + 5/t)
  Caveat
    The polynomials must be univariate.
  SeeAlso
    monicGCD
    monicGCDNaive
    monicGCDModular
    makeMonic
    monicAssociate
    "factoring polynomials over a field"
///

doc ///
  Key
    "factoring polynomials over a field"
  Headline
    factoring polynomials over a general field
  Description
    Text
      @TO factors@ returns the factorization of a polynomial as a list of
      pairs {\tt \{e, h\}}, where $h$ is an irreducible factor and $e$ is its
      multiplicity.  Over $\QQ(2^{1/3})$ the polynomial $x^3-2$ acquires a
      linear factor.
    Example
      K = field(QQ[a]/(a^3-2))
      R = K[x]
      factors(x^3-2)
    Text
      The unit left over is not part of that list.  @TO factorData@ returns
      it together with the factors, in a @TO FactorData@ hash table with keys
      @TO Coefficient@ and @TO Factors@.
    Example
      h = 6*(x^2-2)*(x+1)^2
      factors h
      fd = factorData h
      fd.Coefficient
      fd.Factors
    Text
      Applying @TO value@ to a @TO FactorData@ multiplies everything back
      out, so it can be used to check a factorization.
    Example
      assert(value factorData h == h)
      assert(value factorData(x^3-2) == x^3-2)
    Text
      @TO prettyFactor@ displays the factorization as an unevaluated product.
    Example
      prettyFactor h
      prettyFactor(x^3-2)
    Text
      @TO monicFactors@ and @TO monicFactorData@ are the variants whose
      factors have been made monic, with the correction absorbed into the
      coefficient.
    Example
      monicFactors h
    Text
      To ask only whether a polynomial is irreducible, use
      @TO isIrreducible@.
    Example
      assert isIrreducible(x^2+x+1)
      assert not isIrreducible(x^3-2)
    Text
      Two lower level routines are also exported.  @TO distinctDegreeFactors@
      performs a squarefree decomposition, returning pairs $(e, h_e)$ where
      $h_e$ is the product of the irreducible factors occurring with
      multiplicity exactly $e$.  @TO squareFreeFactors@ takes a squarefree
      polynomial and splits it into irreducibles.
    Example
      K1 = field(QQ[i]/(i^2+1))
      R1 = K1[x]
      u = (x^2+1)*(x+3)^2*(x+5)
      distinctDegreeFactors u
      squareFreeFactors((x^2+1)*(x+3))
      factors u
    Text
      Multivariate polynomials may also be factored.  Over $\QQ(i)$ the sum
      of two squares splits.
    Example
      S = K1[x,y]
      factors(x^2+y^2)
      assert(value factorData(x^2+y^2) == x^2+y^2)
    Text
      This also works over a function field.  Here the base is the function
      field of the twisted cubic.
    Example
      A = QQ[a..d]
      B = A/monomialCurveIdeal(A, {1,2,3})
      L = field B
      useTower L
      S2 = L[x,y]
      F = b*((y+1)*x + a*y)*(x*y + c*y + b)*(x+y+a)
      fd2 = factorData F
      #fd2.Factors
      assert(value fd2 == F)
  Caveat
    In spite of its name, @TO distinctDegreeFactors@ computes a squarefree
    decomposition rather than a distinct degree factorization, and
    @TO squareFreeFactors@ expects its input to be squarefree already.
  SeeAlso
    factors
    factorData
    monicFactors
    monicFactorData
    prettyFactor
    isIrreducible
    squareFreeFactors
    distinctDegreeFactors
    "GCD's over a field"
///

doc ///
  Key
    "working with multiple fields"
  Headline
    moving elements and maps between related fields
  Description
    Text
      Whenever @TO field@ normalizes a ring, it records the map from the
      original ring into the resulting field.  That map is recovered with
      @TO fieldInclusion@.
    Example
      A = QQ[u,v]
      B = A/(v^2-u^3)
      D = field B
      phi = fieldInclusion B
      assert(source phi === B)
      assert(target phi === D)
      phi v
    Text
      Given a ring built over one of these fields, @TO getCoefficientField@
      walks down the tower of coefficient rings until it finds a field in
      normal form.  It returns @TO null@ if there is none.
    Example
      S = D[p,q]
      assert(getCoefficientField S === D)
      assert(getCoefficientField D === D)
      getCoefficientField(ZZ[w])
    Text
      Extensions built one on top of another form a tower.  Elements of a
      smaller field in the tower are moved up with @TO promote@.
    Example
      KA = field(QQ[a]/(a^2-2))
      RA = KA[y]
      c1 = adjoinRoot(y^2-a, Variable => symbol c1)
      LA = ring c1
      extensionDegree LA
      fieldGens LA
      promote(a, LA)
      assert(c1^2 == promote(a, LA))
    Text
      After building a tower, the variable names of the intermediate rings
      are no longer bound to the elements of the top ring.  @TO useTower@
      rebinds them, working down the whole tower of coefficient rings.
    Example
      useTower LA
      assert(ring a === LA)
    Text
      Fields that were not built as a tower are unrelated to one another, and
      Macaulay2 will not silently coerce between them.  Maps between them
      must be given explicitly, and @TO isWellDefined@ will check whether the
      result makes sense.  There is no map from $\QQ(\sqrt 2)$ to
      $\QQ(\sqrt 3)$ sending $\sqrt 2$ to $\sqrt 3$.
    Example
      U = QQ[x]
      s2 = adjoinRoot(x^2-2, Variable => symbol s2)
      use U
      s3 = adjoinRoot(x^2-3, Variable => symbol s3)
      assert(not isWellDefined map(ring s3, ring s2, {s3}))
  Caveat
    Arithmetic combining elements of two unrelated fields is an error rather
    than an automatic coercion: with $s_2$ and $s_3$ as above, {\tt s2+s3}
    fails.  Build a field containing both, or supply an explicit ring map.
  SeeAlso
    field
    fieldInclusion
    getCoefficientField
    useTower
    fieldGens
    baseField
    "extension fields"
///

doc ///
  Key
    field
    (field, Ring)
    [field, Independents]
  Headline
    put a field, or the fraction field of a domain, into normal form
  Usage
    K = field R
    K = field(R, Independents => xs)
  Inputs
    R:Ring
      a domain, typically a field, or a quotient of a polynomial ring by a prime ideal
    Independents => List
      of variables of $R$ to be used as the transcendental generators; the
      default value @TO null@ lets the function choose them with @TO independentSets@
  Outputs
    K:Ring
      the fraction field of $R$, presented in normal form
  Description
    Text
      This is the main entry point of the package.  Given a domain $R$, it
      returns the fraction field of $R$ written as
      $K(t_0, \ldots, t_{r-1})[a_0, \ldots, a_{s-1}]/I$, where $K$ is a basic
      field, the $t_i$ are transcendental over $K$, and $I$ is a
      zero-dimensional prime ideal.  This presentation is what
      @TO isFieldInNormalForm@ tests for, and it is what the GCD and
      factorization routines in this package expect.

      A simple algebraic extension of $\QQ$ is already in normal form, and is
      returned essentially unchanged, but now carrying the cached
      @TO FieldInfo@ that the rest of the package uses.
    Example
      K = field(QQ[a]/(a^2+1))
      describe K
      baseField K
      extensionDegree K
      assert isFieldInNormalForm K
    Text
      A polynomial ring is sent to its field of rational functions.  Note
      that the coefficient ring of the result is $\ZZ$, not $\QQ$: the field
      $\QQ(t)$ is the fraction field of $\ZZ[t]$.  Use @TO baseField@ to
      recover $\QQ$.
    Example
      K1 = field(QQ[t])
      1/t
      baseField K1
      coefficientRing K1
      assert(char K1 == 0)
    Text
      Towers are built one layer at a time.  Each layer is again in normal form.
    Example
      K0 = field(QQ[t])
      K2 = field(K0[z]/(z^2-t))
      describe K2
      fieldGens K2
      extensionDegree K2
    Text
      The input need not be zero-dimensional.  Given a domain of positive
      dimension, @TT "field"@ returns its function field: some of the
      variables become transcendental and the remaining ones become algebraic
      over them.  Here the coordinate ring of the cuspidal cubic $y^2 = x^3$
      becomes a degree three extension of $\QQ(y)$.
    Example
      A = QQ[x,y]
      B = A/(y^2-x^3)
      D = field B
      describe D
      extensionDegree D
    Text
      The map from $R$ into the resulting field is recorded, and can be
      retrieved with @TO fieldInclusion@.
    Example
      fieldInclusion B
    Text
      By default the transcendental variables are chosen by
      @TO independentSets@.  Use @TT "Independents"@ to choose them yourself.
      Presenting the same curve as an extension of $\QQ(x)$ instead of
      $\QQ(y)$ gives a degree two extension.
    Example
      A1 = QQ[x,y]
      B1 = A1/(y^2-x^3)
      D1 = field(B1, Independents => {x})
      describe D1
      extensionDegree D1
    Text
      Basic fields are returned unchanged, and the function is idempotent.
    Example
      assert(field QQ === QQ)
      assert(field(ZZ/5) === ZZ/5)
      assert(field K === K)
  Caveat
    The input is assumed to be a domain; this is not checked.

    The answer is cached on the input ring, so a second call on the same ring
    returns the previously computed field.  In particular, changing
    @TT "Independents"@ has no effect once @TT "field"@ has been applied to
    that ring; build a fresh copy of the ring instead, as in the example above.
  SeeAlso
    isFieldInNormalForm
    baseField
    fieldGens
    fieldInclusion
    adjoinRoot
    splittingField
    "creating a field"
///

doc ///
  Key
    isBasicField
    (isBasicField, Ring)
  Headline
    whether a ring is QQ or a small characteristic finite field
  Usage
    isBasicField R
  Inputs
    R:Ring
  Outputs
    :Boolean
  Description
    Text
      This function returns true if the field can be represented natively, i.e.
      QQ or a finite field of characteristic at most $2^64$.
    Example
      isBasicField QQ
      assert isBasicField(ZZ/101)
      assert isBasicField GF 3
      assert isBasicField GF 9
    Text
      18446744073709551557 is the largest prime less than $2^64$.
    Example
      isBasicField(ZZ/18446744073709551557)
    Text
      However, some fields with more than $2^64$ elements are basic fields.
      The characteristic must be less than $2^64$.
    Example
      K1 = GF(3, 64, Variable => a)
      isBasicField K1
      K2 = GF(3^8, Variable => a)
      isBasicField K2 -- operations are implemented with the aid of a table
    Text
      The following are not basic fields.
    Example
      isBasicField (toField (QQ[a]/(a^2+1)))
      isBasicField (frac (QQ[a,b]))
      isBasicField (ZZ/(nextPrime 2^64))
      K3 = field(K1[b,c])
      isBasicField K3
  Caveat
    Galois fields with less than about 10000 elements are implemented
    in a much more efficient manner than Galois fields with more elements.
  SeeAlso
    isFiniteField
    isPrimeField
    isFractionField
    isFiniteExtensionField
    field
///

doc ///
  Key
    isFiniteField
    (isFiniteField, Ring)
  Headline
    whether a ring is a small characteristic finite field
  Usage
    isFiniteField R
  Inputs
    R:Ring
  Outputs
    :Boolean
  Description
    Text
      This function returns true if $R$ is
      a finite field of characteristic at most $2^64$.
    Example
      isFiniteField QQ
      assert isFiniteField(ZZ/101)
      assert isFiniteField GF 3
      assert isFiniteField GF 9
    Text
      18446744073709551557 is the largest prime less than $2^64$.
    Example
      isFiniteField(ZZ/18446744073709551557)
    Text
      However, some fields with more than $2^64$ elements are basic fields.
      The characteristic must be less than $2^64$.
    Example
      K1 = GF(3, 64, Variable => a)
      isFiniteField K1
      K2 = GF(3^8, Variable => a)
      isFiniteField K2 -- operations are implemented with the aid of a table
    Text
      The following are not small characteristic finite fields.
    Example
      isFiniteField (toField (QQ[a]/(a^2+1)))
      isFiniteField (frac (QQ[a,b]))
      isFiniteField (ZZ/(nextPrime 2^64))
  Caveat
    Galois fields with less than about 10000 elements are implemented
    in a much more efficient manner than Galois fields with more elements.
  SeeAlso
    isBasicField
    isPrimeField
    isFractionField
    isFiniteExtensionField
    field
///

doc ///
  Key
    isPrimeField
    (isPrimeField, Ring)
  Headline
    whether a ring is QQ or a small characteristic finite prime field
  Usage
    isPrimeField R
  Inputs
    R:Ring
  Outputs
    :Boolean
  Description
    Text
      This function returns true if $R$ is $\Q$ or is
      a finite prime field of characteristic at most $2^64$.
    Example
      isPrimeField QQ
      isPrimeField(ZZ/101)
      isPrimeField GF 3
      isPrimeField GF 9
    Text
      18446744073709551557 is the largest prime less than $2^64$.
    Example
      isPrimeField(ZZ/18446744073709551557)
    Text
      However, fields with more than $2^64$ elements are not recognized as prime fields
      via this function.
      The following are not small characteristic finite fields.
    Example
      isPrimeField (ZZ/(nextPrime 2^64))
  SeeAlso
    isBasicField
    isFiniteField
    isFractionField
    isFiniteExtensionField
    field
///

doc ///
  Key
    adjoinRoot
    (adjoinRoot, RingElement)
    [adjoinRoot, Variable]
    [adjoinRoot, AssumeIrreducible]
  Headline
    adjoin a root of an irreducible univariate polynomial
  Usage
    a = adjoinRoot f
    a = adjoinRoot(f, Variable => v)
  Inputs
    f:RingElement
      an irreducible univariate polynomial over a field in normal form
    Variable => Symbol
      the name to give the new generator; it may also be an
      @TO IndexedVariable@.  The default value @TO null@ reuses the name of
      the variable of $f$
    AssumeIrreducible => Boolean
      if true, skip the irreducibility check on $f$
  Outputs
    a:RingElement
      a root of $f$, in a field extension of the coefficient field of $f$
  Description
    Text
      Given an irreducible univariate polynomial $f$ over a field $K$, this
      returns a root of $f$ living in $K[v]/(f)$.  Use @TO ring@ to get hold
      of the extension field itself.
    Example
      U = QQ[x]
      a = adjoinRoot(x^3-x-1, Variable => symbol a)
      K = ring a
      describe K
      extensionDegree K
      assert(a^3-a-1 == 0)
    Text
      If $f$ is linear, no extension is needed and the root is returned in the
      coefficient field itself.
    Example
      adjoinRoot(3*x-5)
      assert(ring adjoinRoot(3*x-5) === QQ)
    Text
      If @TT "Variable"@ is omitted, the new generator inherits the name of
      the variable of $f$.
    Example
      U1 = QQ[y]
      r = adjoinRoot(y^2-2)
      describe ring r
    Text
      It works over finite fields as well.
    Example
      V = (ZZ/5)[x]
      c = adjoinRoot(x^2+2, Variable => symbol c)
      describe ring c
      assert(c^2 == -2)
      extensionDegree ring c
    Text
      Roots may be adjoined repeatedly, building a tower.  The result is
      again a field in normal form.
    Example
      W = K[x]
      d = adjoinRoot(x^2 - a, Variable => symbol d)
      L = ring d
      describe L
      extensionDegree L
      assert(d^2 == promote(a, L))
    Text
      Note that $a$ still refers to the element of the smaller field $K$;
      to compare it with elements of $L$ it must be promoted, as above.

      By default $f$ is checked for irreducibility, and it is an error if it
      is reducible.
    Example
      U2 = QQ[x]
      assert(try (adjoinRoot(x^2-1, Variable => symbol e); false) else true)
    Text
      The check can be expensive, so it may be skipped with
      @TT "AssumeIrreducible => true"@ when irreducibility is already known
      (this is how @TO splittingField@ uses the function).
  Caveat
    Passing @TT "AssumeIrreducible => true"@ for a polynomial that is in fact
    reducible produces a quotient ring that is not a field, and division by a
    zero divisor in it will fail.
  SeeAlso
    splittingField
    field
    minimalPolynomial
    isIrreducible
    extensionDegree
///

doc ///
  Key
    splittingField
    (splittingField, RingElement)
    [splittingField, Variable]
  Headline
    the splitting field of a univariate polynomial
  Usage
    L = splittingField f
    L = splittingField(f, Variable => v)
  Inputs
    f:RingElement
      a univariate polynomial over a field in normal form
    Variable => Symbol
      the base name for the generators adjoined along the way; the resulting
      generators are $v_1, v_2, \ldots$.  An @TO IndexedVariable@ may be given
      instead, in which case the indices continue from there
  Outputs
    L:Ring
      a field extension of the coefficient ring of $f$ over which $f$ splits
      into linear factors
  Description
    Text
      The splitting field is built by repeatedly factoring $f$ over the
      current field and adjoining a root of a nonlinear irreducible factor,
      using @TO adjoinRoot@, until only linear factors remain.
    Example
      R = QQ[x]
      f = x^3-2
      L = splittingField f
      describe L
      extensionDegree L
    Text
      Two generators were adjoined here: a cube root of 2, and a primitive
      cube root of unity.  By default they are named $xx_1, xx_2, \ldots$.
    Example
      fieldGens L
    Text
      Over the splitting field, $f$ really does factor into linear factors.
    Example
      S = L[x]
      monicFactors sub(f, S)
    Text
      If $f$ already splits over its coefficient field, that field is returned
      unchanged.
    Example
      R2 = QQ[x]
      assert(splittingField ((x-1)*(x-2)*(x-3)) === QQ)
      assert(splittingField (2*x-3) === QQ)
    Text
      Use @TT "Variable"@ to control the names of the adjoined generators.
    Example
      R1 = QQ[x]
      L1 = splittingField(x^3-2, Variable => symbol b)
      fieldGens L1
      extensionDegree L1
  Caveat
    Splitting fields grow quickly: the degree of the splitting field of a
    degree $d$ polynomial can be as large as $d!$.  Even modest inputs can
    take a long time.
  SeeAlso
    adjoinRoot
    field
    factors
    monicFactors
    extensionDegree
///

-- TODO: this node was created with claude code, and needs modification.
-- Don't forget to quote the papers of Monagan and van Hoeij that we use!
-- We have to figure out what it should really return.  Have a pointer to
-- makeMonic, associate of the monic version...
doc ///
  Key
    monicGCD
    (monicGCD, RingElement, RingElement)
    (monicGCD, List)
    [monicGCD, Strategy]
  Headline
    compute the monic GCD of univariate polynomials over a field
  Usage
    h = monicGCD(f, g)
    h = monicGCD(f, g, Strategy => "Modular")
    h = monicGCD L
  Inputs
    f:RingElement
      a polynomial in $F[x]$ for some field $F$
    g:RingElement
      a polynomial in the same ring as $f$
    L:List
      a list of polynomials in $F[x]$
    Strategy => String
      either {\tt "Modular"} (the default) or {\tt "Naive"}
  Outputs
    h:RingElement
      the monic GCD of the inputs, or @TO null@ if a leading coefficient is not invertible
  Description
    Text
      Computes the monic greatest common divisor of univariate polynomials
      over a field created using @TO field@.  The result is monic (leading
      coefficient 1), or is the zero polynomial if both inputs are zero.

      The default strategy is {\tt "Modular"}, which reduces the polynomials
      modulo several primes, computes GCDs there, applies the Chinese Remainder
      Theorem, and uses rational reconstruction to recover the result.  The
      {\tt "Naive"} strategy uses the classical Euclidean algorithm.

      Over a simple finite extension of $\QQ$ or $\mathbb{F}_p$:
    Example
      K = field(QQ[a]/(a^3 + a + 1))
      R = K[x]
      f = (x^2 - a*x - 1) * (x + a)^3
      g = (x^2 - a*x - 1) * (x^3 + a)
      monicGCD(f, g)
    Text
      Over a tower extension with transcendental variables:
    Example
      K0 = field(QQ[t])
      K1 = field(K0[z]/(z^2 - t))
      R = K1[x]
      useTower R
      f = (x + z) * (x - 2*t*z/3 + 5/t)
      g = (z*x + 1) * (x - 2*t*z/3 + 5/t)
      monicGCD(f, g)
    Text
      The list form computes the GCD of several polynomials at once.
    Example
      K = field(QQ[a]/(a^3 + a + 1))
      R = K[x]
      f1 = (x - a)^2 * (x + 1)
      f2 = (x - a) * (x^2 + a*x + 1)
      f3 = (x - a)^3
      monicGCD {f1, f2, f3}
    Text
      The {\tt "Naive"} strategy can be selected explicitly:
    Example
      monicGCD(f1, f2, Strategy => "Naive")
  Caveat
    The polynomials must be univariate over a field.  If a leading coefficient
    cannot be inverted (which can happen over a {\tt toField} ring that is not
    actually a field), the function returns @TO null@.
  SeeAlso
    monicGCDNaive
    monicGCDModular
    field
    factors
///

doc ///
  Key
    isFieldInNormalForm
    (isFieldInNormalForm, Ring)
  Headline
    whether a field is presented in the normal form used by this package
  Usage
    isFieldInNormalForm R
  Inputs
    R:Ring
  Outputs
    :Boolean
      whether $R$ is a field in normal form
  Description
    Text
      A field is in {\bf normal form} if it is either a basic field
      (see @TO isBasicField@), or it has been built by @TO field@, and so
      carries the cached @TO FieldInfo@ that the rest of this package relies on.
      Concretely, a field in normal form has the shape
      $K(t_0, \ldots, t_{r-1})[a_0, \ldots, a_{s-1}]/I$, with $K$ a basic
      field and $I$ a zero-dimensional prime ideal.

      Basic fields are always in normal form.
    Example
      assert isFieldInNormalForm QQ
      assert isFieldInNormalForm(ZZ/13)
      assert isFieldInNormalForm GF 9
    Text
      Rings that are not fields at all are never in normal form.
    Example
      isFieldInNormalForm ZZ
      isFieldInNormalForm(QQ[x])
    Text
      This is where the test has teeth: a field built by @TO toField@ or by
      @TO frac@ is a perfectly good field to Macaulay2, but it has not been
      normalized by this package, so it is not in normal form.  Applying
      @TO field@ produces a ring that is.
    Example
      K = toField(QQ[x]/(x^2-x-1))
      isField K
      isFieldInNormalForm K
      K2 = field(QQ[x]/(x^2-x-1))
      describe K2
      assert isFieldInNormalForm K2
    Text
      The same holds for fraction fields.  Note that @TO frac@ and @TO field@
      produce different (though isomorphic) rings here.
    Example
      L1 = frac(QQ[x])
      isFieldInNormalForm L1
      L2 = field(QQ[x])
      assert isFieldInNormalForm L2
      baseField L2
    Text
      Towers built with @TO field@ at each stage stay in normal form.
    Example
      L3 = field(L2[y]/(y^2-x))
      describe L3
      assert isFieldInNormalForm L3
      extensionDegree L3
    Text
      A finite extension may also be adjoined first and the transcendental
      variables afterwards; the result is still in normal form.
    Example
      M1 = field(QQ[x]/(x^2-2))
      M = field(M1[y])
      assert isFieldInNormalForm M
      fieldGens M
  SeeAlso
    field
    fieldInfo
    isBasicField
    isFiniteField
    isPrimeField
    isFractionField
    isFiniteExtensionField
///

///
  Key
  Headline
  Usage
  Inputs
  Outputs
  Description
    Text
    Example
  SeeAlso
///

///
  Key
  Headline
  Usage
  Inputs
  Outputs
  Description
    Text
    Example
  SeeAlso
///

doc ///
  Key
    mydenominator
    (mydenominator, RingElement)
    (mydenominator, QQ)
  Headline
    denominator of a field element or polynomial over a field
  Usage
    d = mydenominator f
  Inputs
    f:RingElement
      an element of a field, or of a polynomial ring over a field
  Outputs
    d:RingElement
      the common denominator of the coefficients of $f$
  Description
    Text
      This function computes the common denominator of (the coefficients of) a field
      element or a polynomial over a field.  The result depends on
      the type of field:

      Over $\QQ$, the result is an integer: the LCM of the denominators
      of all coefficients.
    Example
      R = QQ[x,y]
      F = 3*5/(2*7)*x*y - 3*13/(17*7) * x^2 + 3
      mydenominator F
      assert(mydenominator F == 238)
      mydenominator(-2/3)
    Text
      Over a finite algebraic extension of $\QQ$, the result is still
      an integer (the algebraic extension elements are treated as having
      denominator 1 after clearing integer denominators).
    Example
      K = field(QQ[z1, z2]/(z1^2-z2-1, z2^3+z2+1))
      R = K[x,y]
      F = 3*5/(2*7*z1)*x*y - 3*5*13/(17*7) * x^2 + 30
      mydenominator F
      assert(mydenominator F == 238)
      assert(ring mydenominator F === ZZ)
    Text
      Over a fraction field $\QQ(t_1, \ldots, t_n)$, the result lies in
      $\ZZ[t_1, \ldots, t_n]$: it is the LCM of the denominators of
      all coefficients, viewed as rational functions.
    Example
      K = field(QQ[t1,t2])
      R = K[x,y]
      F = 3*5/(2*7*(t1+2/3*t2))*x*y - 3*13/(17*7) * x^2 + 3
      mydenominator F
    Text
      Over a finite field, the denominator is always 1.
    Example
      R = (ZZ/32003)[x,y]
      F = 3*5/(2*7)*x*y - 3*13/(17*7) * x^2 + 3
      mydenominator F
      assert(mydenominator F === 1_(ZZ/32003))
  Caveat
    The name of this function may change in a future version of this package.
  SeeAlso
    fieldContent
    primitiveAssociate
    monicAssociate
///

doc ///
  Key
    fieldContent
    (fieldContent, RingElement)
  Headline
    content of a polynomial over a field
  Usage
    c = fieldContent f
  Inputs
    f:RingElement
      an element of a field, or of a polynomial ring over a field
  Outputs
    c:RingElement
      the content of $f$, an element of the coefficient field
  Description
    Text
      This function computes the content of $f$: the GCD of its
      coefficients when viewed over the base field.  Dividing $f$ by its
      field content yields the @TO primitiveAssociate@ of $f$.
    Text
      Over $\QQ$, the field content is a rational number.
      The primitive associate is chosen so that its integer content is 1
      and its leading term is positive.
    Example
      R = QQ[x,y]
      F = 3*5/(2*7)*x*y - 3*13/(17*7) * x^2 + 3
      fieldContent F
      assert(fieldContent F === -3/238)
      assert(ring fieldContent F === QQ)
      (1/fieldContent F) * F
      assert((1/fieldContent F) * F == primitiveAssociate F)
    Text
      Over a finite algebraic extension of $\QQ$, the field content
      is again a rational number.
    Example
      K = field(QQ[z1, z2]/(z1^2-z2-1, z2^3+z2+1))
      R = K[x,y]
      F = 3*5/(2*7*z1)*x*y - 3*5*13/(17*7) * x^2 + 30
      fieldContent F
      assert(fieldContent F === -15/238)
      assert(ring fieldContent F === QQ)
    Text
      Over a fraction field of $\QQ[t_1, \ldots]$, the content lies
      in the fraction field.
    Example
      K = field(QQ[t1,t2])
      R = K[x,y]
      F = 3*5/(2*7*(t1+2/3*t2))*x*y - 3*13/(17*7) * x^2 + 3
      fieldContent F
      (1/fieldContent F) * F
    Text
      Over a finite field, the field content is the leading coefficient.
    Example
      R = (ZZ/32003)[x,y]
      F = 3*5/(2*7)*x*y - 3*13/(17*7) * x^2 + 3
      fieldContent F
      primitiveAssociate F
  SeeAlso
    mydenominator
    primitiveAssociate
    monicAssociate
///

doc ///
  Key
    primitiveAssociate
    (primitiveAssociate, RingElement)
  Headline
    canonical associate of a polynomial obtained by dividing out the field content
  Usage
    G = primitiveAssociate F
  Inputs
    F:RingElement
      a polynomial over a field
  Outputs
    G:RingElement
      the primitive associate of $F$
  Description
    Text
      The primitive associate of a polynomial $F$ is $F / c$, where
      $c$ = @TO fieldContent@ $F$.  The result is a polynomial whose
      field content is a unit.

      Over $\QQ$, the result has integer content 1 and positive leading coefficient.
    Example
      R = QQ[x,y]
      F = -6/7*x^2 + 9/14*x*y + 3
      primitiveAssociate F
      fieldContent F
      assert(primitiveAssociate F == (1/fieldContent F) * F)
    Text
      Scalar multiples of a polynomial have the same primitive associate.
    Example
      assert(primitiveAssociate F == primitiveAssociate(21*F))
      assert(primitiveAssociate F == primitiveAssociate(-2/3*F))
    Text
      Over a finite field, the primitive associate is obtained by
      dividing by the leading coefficient, since every element is a unit.
    Example
      R = (ZZ/101)[x,y]
      F = 3*x^2 + 6*x*y + 9
      primitiveAssociate F
    Text
      Over an algebraic extension, the primitive associate
      clears the base field content but may leave an algebraic
      leading coefficient.  Use @TO monicAssociate@ to further
      normalize the leading coefficient.
    Example
      K = field(QQ[a]/(a^2+1))
      R = K[x]
      F = a*x^2 + (3/2)*x + a + 1
      primitiveAssociate F
      monicAssociate F
      assert(primitiveAssociate F != monicAssociate F)
    Text
      The primitive associate of the zero polynomial is zero.
    Example
      R = QQ[x]
      assert(primitiveAssociate(0_R) == 0)
  SeeAlso
    fieldContent
    monicAssociate
    mydenominator
///

doc ///
  Key
    monicAssociate
    (monicAssociate, RingElement)
  Headline
    canonical associate of a polynomial with leading coefficient made monic
  Usage
    G = monicAssociate F
  Inputs
    F:RingElement
      a polynomial over a field
  Outputs
    G:RingElement
      the monic associate of $F$
  Description
    Text
      The monic associate of a polynomial $F$ is computed by first making $F$
      monic (dividing by the leading coefficient), and then taking the
      @TO primitiveAssociate@ of the result.

      When the leading coefficient of $F$ lies in the base field (e.g. $\QQ$ or $\mathbb{F}_q$),
      the monic associate and the primitive associate coincide.
    Example
      R = QQ[x,y]
      F = -6/7*x^2 + 9/14*x*y + 3
      monicAssociate F
      primitiveAssociate F
      assert(monicAssociate F == primitiveAssociate F)
    Text
      Over a finite field, the monic associate divides by the leading coefficient.
    Example
      R = (ZZ/101)[x]
      F = 3*x^2 + 6*x + 9
      monicAssociate F
      assert(monicAssociate F == monicAssociate(7*F))
    Text
      The two functions differ when the leading coefficient involves
      algebraic extension elements.  In this case, @TO monicAssociate@
      first inverts the leading coefficient (making the polynomial monic),
      and then clears the resulting field content.
    Example
      K = field(QQ[a]/(a^2+1))
      R = K[x]
      F = a*x^2 + (3/2)*x + a + 1
      primitiveAssociate F
      monicAssociate F
    Text
      The leading monomial of @TO monicAssociate@ will have a coefficient that is
      primitive in the base field, rather than being 1 in the full coefficient field.
    Example
      K0 = field(QQ[t1,t2])
      K = field(K0[z1, z2, MonomialOrder => Lex]/(z1^2-2, z2^3-z1))
      R = K[x,y,w]
      useTower R
      F = (t1 + t2)/(3*t1-3*t2^2) * x * y - (t1 * z1 * z2)^(-1) * w^3 + 1/3
      primitiveAssociate F
      monicAssociate F
  SeeAlso
    primitiveAssociate
    fieldContent
    mydenominator
///

doc ///
  Key
    makeMonic
    (makeMonic, RingElement)
  Headline
    divide a polynomial by its leading coefficient
  Usage
    G = makeMonic F
  Inputs
    F:RingElement
      a polynomial
  Outputs
    G:RingElement
      $F$ divided by its leading coefficient, or @TO null@ if the
      leading coefficient is not invertible
  Description
    Text
      This function divides a polynomial by its leading coefficient,
      producing a monic polynomial (leading coefficient equal to 1).
    Example
      R = QQ[x]
      F = 3*x^2 + 6*x + 9
      makeMonic F
      assert(leadCoefficient makeMonic F == 1)
    Text
      It works over any field, including algebraic extensions and
      fraction fields.
    Example
      K = field(QQ[a]/(a^2+1))
      R = K[x]
      F = a*x^2 + (3/2)*x + a + 1
      makeMonic F
      assert(leadCoefficient makeMonic F == 1)
    Example
      K = field(QQ[t1,t2])
      R = K[x]
      F = (t1+t2)*x^2 + 3*x + 1
      makeMonic F
    Text
      The zero polynomial is returned unchanged.
    Example
      R = QQ[x]
      makeMonic(0_R)
    Text
      If the leading coefficient is not invertible in the coefficient ring
      (e.g. over $\ZZ$), the function returns @TO null@.
    Example
      S = ZZ[x]
      G = 3*x^2 + 6*x + 9
      makeMonic G === null
  SeeAlso
    monicAssociate
    primitiveAssociate
///


///
  Key
  Headline
  Description
    Text
    Example
  SeeAlso
///

///
Key
Headline
Usage
Inputs
Outputs
Consequences
  Item
Description
  Text
  Example
  CannedExample
  Code
  Pre
ExampleFiles
Contributors
References
Caveat
SeeAlso
///
