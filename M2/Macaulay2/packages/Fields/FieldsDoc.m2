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
  Caveat
  SeeAlso
    "creating a field"
    "GCD's over a field"
    "factoring polynomials over a field"
    "extension fields"
    "working with multiple fields"
///

///
  Key
  Headline
  Description
    Text
      @SUBSECTION "Constructing fields"@
    Text
      @UL {
          TO (),
          TO (normalToricVariety, Matrix),
          TO NormalToricVariety,
          TO (isWellDefined, NormalToricVariety),

    Example
  SeeAlso
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

///
  Key
    isFieldInNormalForm
    (isFieldInNormalForm, Ring)
    (isWellDefined, FieldInfo)
  Headline
    whether a field is presented in a standard form
  Usage
    isFieldInNormalForm R
  Inputs
    R:Ring
  Outputs
    :Boolean
  Description
    Text
    Example
      isFieldInNormalForm QQ -- TODO: should populate the FieldInfo
      K = toField(QQ[x]/(x^2-x-1))
      isFieldInNormalForm K -- false.
      K2 = field(QQ[x]/(x^2-x-1))
      describe K2
      isFieldInNormalForm K2

      L1 = frac(QQ[x])
      L2 = toField(L1[y]/(y^2-x))
      isField L2

      L1' = field(QQ[x])
      L2' = field(L1'[y]/(y^2-x))
      isFieldInNormalForm L2'

      L1' = field(QQ[x])
      L2' = field(L1'[y]/(y^2-2))
      describe L2'
      isFieldInNormalForm L2'

      L1' = field(QQ[x]/(x^2-2))
      L2' = field(L1'[y])
      isFieldInNormalForm L2'
      fieldInfo L2'

      A = QQ[a..d]
      B = A/monomialCurveIdeal(A, {1,2,3})
      D = field B
      fieldInclusion D
  SeeAlso
    isBasicField
    isFiniteField
    isPrimeField
    isFractionField
    isFiniteExtensionField
    field
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
