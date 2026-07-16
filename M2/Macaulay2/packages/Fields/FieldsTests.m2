-* Test section *-

-*
  restart
  needsPackage "Fields"
*-
TEST /// -- isPrimeField
  assert isPrimeField QQ
  assert isPrimeField(ZZ/101)
  assert not isPrimeField(ZZ/(nextPrime 2^65)) -- TODO:  Want to allow this as a prime field?  Probably!
  assert isPrimeField GF 3
  assert not isPrimeField GF 9
  assert not isPrimeField (toField (QQ[a]/(a^2+1)))
  assert not isPrimeField (frac (QQ[a,b]))
///

TEST /// -- isFiniteField
  assert not isFiniteField QQ
  assert isFiniteField(ZZ/101)
  assert not isFiniteField(ZZ/(nextPrime 2^65)) -- fails.  Want to allow this likely?
  assert isFiniteField GF 3
  assert isFiniteField GF 9
  assert not isFiniteField (toField (QQ[a]/(a^2+1)))
  assert not isFiniteField (toField (ZZ/101[a]/(a^2+a+1))) -- TODO: this is a finite field...  Allow it?
  assert not isFiniteField (frac (QQ[a,b]))
///

TEST /// -- isBasicField
  assert isBasicField QQ
  assert isBasicField(ZZ/101)
  assert not isBasicField(ZZ/(nextPrime 2^65))
  assert isBasicField GF 3
  assert isBasicField GF 9
  assert not isBasicField (toField (QQ[a]/(a^2+1)))
  assert not isBasicField (frac (QQ[a,b]))
///

TEST /// -- induced maps on GF's.  TODO: problem: this map phi is not natural or canonical...!
  K1 = GF(9, Variable => a)
  K2 = GF(81, Variable => b)
  phi = map(K2, K1)
  f = (ideal ambient K1)_0
  c = phi.matrix_(0,0)
  assert(sub(f, a => c) == 0)

  K3 = GF(27, Variable => b)
  assert try (phi = map(K3, K1); false) else true
///

-- xxx
-*
  restart
  needsPackage "Fields"
  errorDepth = 0
*-
TEST /// -- isFieldInNormalForm
  assert isFieldInNormalForm QQ
  assert isFieldInNormalForm(ZZ/101)
  assert not isFieldInNormalForm(ZZ/(nextPrime 2^65))
  assert isFieldInNormalForm GF 3
  assert isFieldInNormalForm GF 9
  assert not isFieldInNormalForm (toField (QQ[a]/(a^2+1)))
  assert not isFieldInNormalForm (frac (QQ[a,b]))
  K1 = field (QQ[a]/(a^2+1))
  isFieldInNormalForm K1
  K2 = field(K1[b,c,d,e])
  isFieldInNormalForm K2
  K3 = K2[x]
  isFieldInNormalForm K3

  K4 = field (QQ[x,y])
  fieldInfo K4 --
  ---- TODO: WANT THIS TO WORK, I think -- K4 = field (ZZ[x,y]) -- fails
  ---- A = ZZ[x,y]
  ---- B = A/ideal(3_A)
  ---- C = field B -- fails: TODO: fix this?

  -- what is the point of the following code?
  getCoefficientField K4
  getCoefficientField K1
  useTower K2
  getCoefficientField(K2[x]/(x^2-b))
  getCoefficientField((K2[x]/(x^2-b))[y]/(x*b))
  baseRing ((K2[x]/(x^2-b))[y]/(x*b))

  coefficientRing (K1[x][y]/(x^2+y^2))
  
///

-*
  restart
  needsPackage "Fields"
*-
TEST ///
  kk = QQ
  A1 = QQ[z1]/(z1^2-5)
  F = field A1
  F2 = field(F[z2]/(z2^2-z1))
  z1
  z2
  use F
  g = z1^1 + 2
  use F2
  useTower F2
  -- g + z2 -- TODO: fails
  sub(g, F2) + z2 -- this works, but can't do it directly...
  -- 
///
-*
  restart
  needsPackage "Fields"
*-
TEST /// -- fieldInfo on basic fields, fraction fields, finite extensions
  K1 = ZZ/5
  fieldInfo K1
  assert isPrimeField K1
  assert(char K1 === 5)
  assert isBasicField K1
  
  K2 = QQ
  displayFieldInfo K2
  assert isPrimeField K2
  assert(char K2 === 0)
  assert isBasicField K2

  K3 = GF 4
  displayFieldInfo K3
  assert not isPrimeField K3
  assert(char K3 === 2)
  -- TODO: assert isFiniteExtensionField K3 -- how to handle this one
  assert not isFractionField K3
  assert isBasicField K3

  K4 = toField(K1[x]/(x^2+x+2))
  displayFieldInfo K4
  assert not isPrimeField K4
  assert(char K4 === char K1)
  assert isFiniteExtensionField K4
  assert not isFractionField K4
  assert not isBasicField K4
  
  K5 = frac(K1[a,b])
  displayFieldInfo K5
  assert not isPrimeField K5
  assert(char K5 === char K1)
  assert not isFiniteExtensionField K5
  assert isFractionField K5
  assert not isBasicField K5
///

///
  K[x,y]
  -- examples of fields
  K1 = ZZ/5
  K2 = QQ

  K5 = frac(K1[a,b])
  K5 = toField(K5[x]/(x^3-a))
  K6 = frac(K5[y,z]) -- not implmented yet
  K7 = toField(K5[y]/(y^2-x))
  describe K7
  K8 = toField(K5[x,y]/(x^2-a, y^3-b))

  -- these fail as the information needed is not set?

  isBasicField K2

  nextPrime (2^63)
  KK = ZZ/9223372036854775837

  nextPrime (2^64)
  KK = ZZ/18446744073709551629
  nextPrime 84593758943758375398987
  ZZ/84593758943758375399117

  nextPrime (2^64)
  18446744073709551629 - 2^64
///

-*
  restart
  needsPackage "Fields"
*-
TEST /// -* field *-
  kk = ZZ/101
  fieldInfo kk
  isWellDefined fieldInfo kk

  -- simple finite extension
  kk = ZZ/101
  fieldInfo kk
  A = field(kk[a]/(a^2+a+1))
  fieldInfo A
  isWellDefined fieldInfo A
  describe A
  ring a === A
  assert(1/a == -a-1)
  useTower A
  ring a === A
  phi = fieldInclusion A
  isWellDefined phi

  -- a simple fraction field
  K = field (QQ[a..d])
  fieldInfo K
  fieldInclusion K
  1/2 * 1/(a+b)
  1/2 * a

  -- a fraction field on top of a finite extension
  C = A[b,c,d]
  D = field C
  describe D
  fieldInfo D
  assert isWellDefined fieldInfo D
  useTower D
  fieldInclusion D

  -- a finite extension on top of something that has both indep and fiber vars
  E = D[e]/(e^2-a-b)
  F = field E
  fieldInfo F
  assert isWellDefined fieldInfo F
  useTower F
  e
  a
  1/(a+b)
  assert(oo * (a+b) == 1)

  denominator(1/(a+b+e))
  R = F[x,y,z]/(x*y - a^2, y^2 - b^2)
  denominator (1/(a+b))
  F = 1/(b+c)^2 * x^2 - 1/e * y^3
  mydenominator F
///

TEST ///
  R = QQ[a..d]
  I = monomialCurveIdeal(R, {1,3,4})
  A = field(R/I)
  useTower A
  b
  fieldInfo A

  B = A[t]/(t*a-b)
  describe B
  C = field B
  describe C
  fieldInfo C


  useTower A
  E = A[alpha]/(alpha^2-a)
  field(E)

  -- we make b a symbol again, as b is an element in a quotient ring...
  B = frac(GF(4)[symbol b,c,d,e])
  fieldInfo B
///

-*
  restart
  needsPackage "Fields"
*-
TEST /// -* field *-
  debug needsPackage "Fields"
  setFieldInfo QQ
  fieldInfo QQ

  kk = ZZ/101
  setFieldInfo kk
  assert kk.cache.?FieldInfo
  kk.cache.FieldInfo
  fieldInfo kk

  A = kk[a,b,c]
  R = frac A
  setFieldInfo R
  R.cache.FieldInfo
  R2 = field A
  
  A = kk[a, b]
  B = A/ideal(a^2-3, b^2-5)
  C = field B
  fieldInfo C
  displayFieldInfo C

  A = QQ[a,b, MonomialOrder=>Lex]
  B = A/ideal(a^2-3, b^2-5)
  C = toField B
  fieldInfo C
  displayFieldInfo C
  
  kk = ZZ/101
  A = frac(kk[a,b])
  B = A[c,d, MonomialOrder => Lex]
  C = B/(ideal groebnerBasis ideal(c^2-d-3, d^2-5))
  D = field C
  fieldInfo D
  displayFieldInfo D
  
  1/(a+b+c)
  assert isField D

  K1 = frac(QQ[a,b])
  R1 = K1[d,e]
  R2 = R1/(d^2-2, e^3-3)
  K2 = field R2
  fieldInfo K2
  field coefficientRing K2
///

-*
  restart
  needsPackage "Fields"
*-
TEST ///
  A = ZZ/101[a..d]
  I = monomialCurveIdeal(A, {1,3,4})
  B = A/I
  C = field B -- here c generated C over ZZ/101(a,d).  But b is linear, so we might want to keep it too?
  fieldInfo C
///

-*
  restart
  needsPackage "Fields"
*-
TEST /// -- basicField
  assert(basicField (ZZ/101) === ZZ/101)
  assert(basicField QQ === QQ)
  A = toField(QQ[a]/(a^3+a+1))
  B = frac (ZZ[a..d])
  C = toField(QQ[a,b,c]/(a^3+a+1))
  D = GF 8
  E = toField(D[e]/(e^4+e^3+1))
  assert(basicField A === QQ)
  basicField B -- want this to be QQ probably, not ZZ
  assert(basicField C === QQ)
  assert(basicField D === D) -- or should it be ZZ/2?
  assert(basicField E === D)

  a = 40
  useTower E

  a -- should be in D...

  F = field(ZZ[a]/(3, a^2+a+1))
  assert(char F == 3)
  baseField F === ZZ/3

  -- it can choose which is the finite var...
  F0 = field(ZZ[s,t,symbol a]/(3, a^2 + a + s^2))
  useTower F0
  describe F0
  fieldInfo F0
  assert(baseField F0 === ZZ/3)
  ring a
///

-*
  restart
  debug needsPackage "Fields"
*-
TEST /// -- testing `mydenominator` (name should change...)
  debug needsPackage "Fields"
  (K1,K2,K3,K4,K5,K6,K7,K8) = allFieldCases 32003;

  -- case 1. QQ
  useTower K1
  R = K1[x,y]
    F = 3*5/(2*7)*x*y - 3*13/(17*7) * x^2 + 3
    assert(mydenominator F == 2*7*17)
    assert(mydenominator (-2/3) == 3)

  -- case 2. QQ[z]/Iz
    useTower K2
    R = K2[x,y]
    F = 3*5/(2*7*z1)*x*y - 3*13/(17*7) * x^2 + 3
    assert(mydenominator F == 238)
    assert(ring mydenominator F === ZZ)

  -- case 3.  field(QQ[t...])
    useTower K3
    R = K3[x,y]
    F = 3*5/(2*7*(t1+2/3*t2))*x*y - 3*13/(17*7) * x^2 + 3
    denF = mydenominator F
    use ring denF
    assert(denF === 238*(3*t1 + 2*t2))
    useTower R
    G = 3*5/(2*7*(t1+2/3*t2^2+t1*t2))*x*y - 3*13/(17*7*t1) * x^2 + 3
    denG = mydenominator G
    assert(ring denF === ring denG)

  -- case 4.  field(QQ[t...])[zs]/Iz
    useTower K4
    R = K4[x,y]
    useTower R
    F = 3*5/(2*7*(t1+2/3*t2*z2))*x*y - 3*13/(17*7) * x^2 + 3
    denF = mydenominator F
    assert(denF == 238 * t1 * (64*t2^8 - 729*t1^5))
    assert(toString ring denF == "ZZ[t1, t2]")

    G = 3*5/(2*7*(t1+2/3*t2^2+t1*t2))*x*y - 3*13/(17*7*t1) * x^2 + 3
    denG = mydenominator G
    assert(ring denF === ring denG)

  -- case 5. Fq.  This case just returns 1 in the base field.
    useTower K5
    R = K5[x,y]
    F = 3*5/(2*7)*x*y - 3*13/(17*7) * x^2 + 3
    assert(mydenominator F === 1_(K5))

    K5' = (allFieldCases(101^2))_4;

    R = K5'[x,y]
    F = 3*5/(2*7*a)*x*y - 3*13/(17*7) * x^2 + 3
    assert(mydenominator F === 1_(coefficientRing R))

  -- case 6. Fq[z]/Iz.  This case just returns 1 in the base field.
    -- denominator should be 1, if the element is nonzero.
    useTower K6
    R = K6[x,y]
    F = 3*5/(2*7*z1)*x*y - 3*13/(17*7) * x^2 + 3
    assert(mydenominator F === 1_K5) 

  -- case 7.  field(Fq[t...])
    useTower K7
    R = K7[x,y]
    F = 3*5/(2*7*(t1+2/3*t2))*x*y - 3*13/(17*7) * x^2 + 3
    assert((denF = mydenominator F) == t1 - 10667*t2)
    assert(ring denF === ring numerator (1_K7))

    G = 3*5/(2*7*(t1+2/3*t2^2+t1*t2))*x*y - 3*13/(17*7*t1) * x^2 + 3
    denG = mydenominator G
    assert(ring denF === ring denG)

  -- case 8. field(Fq[t...])[zs]/Iz
    useTower K8
    R = K8[x,y]
    F = 3*5/(2*7*(t1+2/3*t2*z2))*x*y - 3*13/(17*7) * x^2 + 3
    assert((denF = mydenominator F) == t2^4+3997*t1^3+16000*t1*t2^2)

    G = 3*5/(2*7*(t1+2/3*t2^2+t1*t2*z1))*x*y - 3*13/(17*7*t1) * x^2 + 3
    denG = mydenominator G
    assert(ring denF === ring denG)
///

-*
  restart
  debug needsPackage "Fields"
*-
TEST /// -- testing primitiveAssociate, monicAssociate
  -- case 1. QQ
    R = QQ[x,y]
    F = 3*5/(2*7)*x*y - 3*13/(17*7) * x^2 + 3
    fieldContent F
    1/fieldContent F * F 
    assert(
        primitiveAssociate F
        ==
        26 * x^2 - 85*x*y - 238 -- note: integer content is 1, lead term is > 0.
        )
    assert(
        monicAssociate F
        ==
        26 * x^2 - 85*x*y - 238
        )
    assert(fieldContent F === - 3/238)
    assert(ring fieldContent F === QQ)
    assert(1/fieldContent F * F == primitiveAssociate F)
    
  -- case 2. QQ[z]/Iz
    K = field(QQ[z1, z2]/(z1^2-z2-1, z2^3+z2+1))
    describe K
    R = K[x,y]
    F = 3*5/(2*7*z1)*x*y - 3*5*13/(17*7) * x^2 + 30
    assert(
        primitiveAssociate F
        ==
        26 * x^2 + (-17 * z1 * z2^2 + 17 * z1 * z2 - 34 * z1) * x * y - 476
        )
    assert(
        monicAssociate F
        ==
        primitiveAssociate F
        )
    
    assert(mydenominator F == 238)
    assert(ring mydenominator F === ZZ)
    assert(fieldContent F === -15/238)
    assert(ring fieldContent F === QQ)
    assert((1/fieldContent F) * F == primitiveAssociate F)
    
    -- case 3.  field(QQ[t...])
    K = field(QQ[t1,t2]) 
    R = K[x,y]
    F = 3*5/(2*7*(t1+2/3*t2))*x*y - 3*13/(17*7) * x^2 + 3
    F = (3 + 2*t1) * F
    denF = mydenominator F
    fieldContent F
    (1/fieldContent F) * F
    fieldContent oo
    use ring denF
    assert(denF === 238*(3*t1 + 2*t2))
    useTower R
    G = 3*5/(2*7*(t1+2/3*t2^2+t1*t2))*x*y - 3*13/(17*7*t1) * x^2 + 3
    denG = mydenominator G
    fieldContent G
    assert(ring denF === ring denG)
    (1/fieldContent G) * G

  -- case 4.  field(QQ[t...])[zs]/Iz
    K0 = field(QQ[t1,t2])
    K = field(K0[z1, z2, MonomialOrder => Lex]/(z1^2-2, z2^3-z1))
    R = K[x,y]
    useTower R
    F = 3*5/(2*7*(t1+2/3*t2*z2))*x*y - 3*13/(17*7) * x^2 + 3
    denF = mydenominator F
    assert(denF == 238 * (729*t1^6 - 128*t2^6))
    assert(toString ring denF == "ZZ[t1, t2]")
    F = (2*t1 + 3*t2 - 1) * F
    fieldContent F
    assert(ring fieldContent F === K0)
    (1/fieldContent F) * F
    fieldContent oo

    G = 3*5/(2*7*(t1+2/3*t2^2+t1*t2))*x*y - 3*13/(17*7*t1) * x^2 + 3
    denG = mydenominator G
    assert(ring denF === ring denG)

  -- case 5. Fq.  This case just returns 1 in the base field.
    R = ZZ/32003[x,y]
    F = 3*5/(2*7)*x*y - 3*13/(17*7) * x^2 + 3
    assert(mydenominator F === 1_(ZZ/32003))
    (1/fieldContent F) * F

    R = (GF(101,2))[x,y]
    F = 3*5/(2*7*a)*x*y - 3*13/(17*7) * x^2 + 3
    assert(mydenominator F === 1_(coefficientRing R))
    fieldContent F
    primitiveAssociate F

  -- case 6. Fq[z]/Iz.  This case just returns 1 in the base field.
    -- denominator should be 1, if the element is nonzero.
    z1 = symbol z1
    z2 = symbol z2
    K = field(ZZ/32003[z2, z1, MonomialOrder => Lex]/(z1^2-z2-1, z2^3+z2+1))
    describe K
    R = K[x,y]
    F = 3*5/(2*7*z1)*x*y - 3*13/(17*7) * x^2 + 3
    assert(mydenominator F === 1_(ZZ/32003))
    fieldContent F === 2689_(ZZ/32003)    

  -- case 7.  field(Fq[t...])
    kk = ZZ/101
    K = field(kk[t1,t2]) 
    R = K[x,y]
    F = 3*5/(2*7*(t1+2/3*t2))*x*y - 3*13/(17*7) * x^2 + 3
    assert((denF = mydenominator F) == t1 - 33*t2)
    assert(ring denF === ring numerator (1_K))
    fieldContent F
    1/oo * F

    G = 3*5/(2*7*(t1+2/3*t2^2+t1*t2))*x*y - 3*13/(17*7*t1) * x^2 + 3
    denG = mydenominator G
    assert(ring denF === ring denG)
    fieldContent G

    F1 = (2*t1 + 3*t2 + 1) * F
    fieldContent F1
    assert(1/(fieldContent F1) * F1 == primitiveAssociate F)

  -- case 8. field(Fq[t...])[zs]/Iz
    kk = ZZ/101
    K0 = field(kk[t1,t2])
    z1 = symbol z1
    z2 = symbol z2
    K = field(K0[z1, z2, MonomialOrder => Lex]/(z1^2-2, z2^3-z1))
    R = K[x,y]
    useTower R
    F = 3*5/(2*7*(t1+2/3*t2*z2))*x*y - 3*13/(17*7) * x^2 + 3
    assert((denF = mydenominator F) == t1^6 - 15*t2^6)
    fieldContent F
    (1/fieldContent F) * F

    F1 = (t1+1)*F
    fieldContent F1
    assert(primitiveAssociate F1 == primitiveAssociate F)
    G = 3*5/(2*7*(t1+2/3*t2^2+t1*t2*z1))*x*y - 3*13/(17*7*t1) * x^2 + 3
    denG = mydenominator G
    assert(ring denF === ring denG)
    1/fieldContent G * G
///



/// -- don't need this any more: this was to test the 8denominator routines.
-- but those are now rolled into `mydenominator`
  restart
  debug needsPackage "Fields"

  -- case 1. QQ
    R = QQ[x,y]
    F = 3*5/(2*7)*x*y - 3*13/(17*7) * x^2 + 3
    assert(mydenominator F == 2*7*17)
    assert(mydenomQQ {-2/3} == 3)

  -- case 2. QQ[z]/Iz
  -- TODO: the next line needs a better error message
    -- field(ZZ[z1, z2, MonomialOrder => Lex]/(z1^2-z2-1, z2^3+z2+z2))

    K = field(QQ[z1, z2]/(z1^2-z2-1, z2^3+z2+z2))
    describe K
    R = K[x,y]
    F = 3*5/(2*7*z1)*x*y - 3*13/(17*7) * x^2 + 3
    assert(mydenominator F == 238)
    assert(ring mydenominator F === ZZ)
    
    tmsf = (terms F)/leadCoefficient
    terms tmsf_0
    (terms leadCoefficient tmsf_1)/leadCoefficient
    assert(mydenomQQz tmsf == 7*17*2)

  -- case 3.  field(ZZ[t...])

  -- TODO: the next line needs to work, AND it stashes ZZ[t1,t2]
    --K = field(ZZ[t1,t2]) -- giving error
  -- TODO: this line needs to also create ZZ[t1,t2], stash it.
    K = field(QQ[t1,t2]) 
    R = K[x,y]
    F = 3*5/(2*7*(t1+2/3*t2))*x*y - 3*13/(17*7) * x^2 + 3
    denF = mydenominator F
    use ring denF
    assert(denF === 238*(3*t1 + 2*t2))

    tmsf = terms F
    denF = mydenomQQt tmsf
    G = 3*5/(2*7*(t1+2/3*t2^2+t1*t2))*x*y - 3*13/(17*7*t1) * x^2 + 3
    tmsg = terms G
    denG = mydenomQQt tmsg
    ring denF === ring denG -- true...  so maybe we don't need to store it?

  -- case 4.  field(ZZ[t...])[zs]/Iz

    K0 = field(QQ[t1,t2])
    K = field(K0[z1, z2, MonomialOrder => Lex]/(z1^2-2, z2^3-z1))
    R = K[x,y]
    useTower R
    F = 3*5/(2*7*(t1+2/3*t2*z2))*x*y - 3*13/(17*7) * x^2 + 3
    mydenominator F

    tmsf = terms F
    g1 = tmsf/leadCoefficient//flatten/leadCoefficient
    g2 = g1/terms//flatten/leadCoefficient
    g2/denominator//lcm
    /terms//flatten/leadCoefficient
    denF = mydenomQQt tmsf
    G = 3*5/(2*7*(t1+2/3*t2^2+t1*t2))*x*y - 3*13/(17*7*t1) * x^2 + 3
    tmsg = terms G
    denG = mydenomQQt tmsg
    ring denF === ring denG -- true...  so maybe we don't need to store it?

  -- case 5. Fq.  This case just returns 1 in the base field.
    R = ZZ/32003[x,y]
    F = 3*5/(2*7)*x*y - 3*13/(17*7) * x^2 + 3
    tmsf = terms F
    assert(mydenomFq tmsf == 1)

    R = (GF(101,2))[x,y]
    F = 3*5/(2*7*a)*x*y - 3*13/(17*7) * x^2 + 3
    tmsf = terms F
    assert(mydenomFq tmsf == 1)

  -- case 6. Fq[z]/Iz.  This case just returns 1 in the base field.
  -- denominator should be 1, if the element is nonzero.
    K = field(ZZ/32003[z2, z1, MonomialOrder => Lex]/(z1^2-z2-1, z2^3+z2+z2))
    describe K
    R = K[x,y]
    F = 3*5/(2*7*z1)*x*y - 3*13/(17*7) * x^2 + 3
    tmsf = (terms F)
    assert(mydenomFqz tmsf == 1_(ZZ/32003))

  -- case 7.  field(Fq[t...])

    kk = ZZ/101
    K = field(kk[t1,t2]) 
    R = K[x,y]
    F = 3*5/(2*7*(t1+2/3*t2))*x*y - 3*13/(17*7) * x^2 + 3
    tmsf = terms F
    denF = mydenomQQt tmsf
    G = 3*5/(2*7*(t1+2/3*t2^2+t1*t2))*x*y - 3*13/(17*7*t1) * x^2 + 3
    tmsg = terms G
    denG = mydenomFqt tmsg
    ring denF === ring denG -- true...  so maybe we don't need to store it?

  -- case 8. field(Fq[t...])[zs]/Iz
    kk = ZZ/101
    K0 = field(kk[t1,t2])
    K = field(K0[z1, z2, MonomialOrder => Lex]/(z1^2-2, z2^3-z1))
    R = K[x,y]
    useTower R
    F = 3*5/(2*7*(t1+2/3*t2*z2))*x*y - 3*13/(17*7) * x^2 + 3
    tmsf = terms F
    mydenomFqtz tmsf
    G = 3*5/(2*7*(t1+2/3*t2^2+t1*t2*z1))*x*y - 3*13/(17*7*t1) * x^2 + 3
    tmsg = terms G
    mydenomFqtz tmsg
    ring denF === ring denG -- true...  so maybe we don't need to store it?
    
///

///
  L1 = ZZ/101
  L2 = GF(9)
  L3 = QQ
  L4 = frac(QQ[a,b])
  L5 = toField(L4[x]/(x^2-1/a))
  describe L5
  baseRing L1 === ZZ
  baseRing L2 -- is a integral extension of ZZ/3
  baseRing L3 === ZZ
  baseRing L4 -- QQ[a,b]
  baseRing baseRing L5 -- L4[x]
  ambient L5 -- not really useful...
  coefficientRing L5
  ideal coefficientRing L5

  basicField L -- always returns QQ or finite field (or prime field?)
  independents L -- returns the list of variables in the fraction field part (or empty list, in none).
  extensionRing L -- this is the "coefficient ring" of the toField'ed L.
///

-*
  restart
  needsPackage "Fields"
*-
-- REDO, or REMOVE this test
TEST /// -- monicGCD for a finite extension of Fp or QQ.
-- First, a single extension over Fp, which is not actually a field...
  nextPrime 2^25
  K1 = ZZ/33554467
  A1 = K1[z]
  mz = z^2-34326437287
  K2 = field(A1/mz)
  R = K2[x]
  useTower R
///

-*
  restart
  debug  needsPackage "Fields"
*-
TEST /// -- monicGCDNaive for a finite extension of Fp or QQ.
-- First, a single extension over Fp
  debug  needsPackage "Fields" -- for makeMonic
  nextPrime 2^25
  K1 = ZZ/33554467
  A1 = K1[z]
  mz = z^3 - 23/2*z^2 + 41*z  - 7
  K2 = field(A1/mz)
  R = K2[x]
  useTower R

  t = 241334781
  g = (10-4*t)*x^2 - 5*x*z^2 + (4*t+1)*x*z + (11 - 17*t^2 + 9*t)*x -
    19*z^2 + (-7*t+6)*z + (-11*t^2 + 15*t + 3)
  a = (18 + 10*t)*x^2 + 10*x*z^2 + (17*t + 2)*x*z + (2 + 17*t^2 + 8*t)*x +
    6*z^2 + (17*t+6)*z + (4*t^2-4*t+2)
  b = (-8-11*t)*x^2 -14*x*z^2 + (8*t-4)*x*z + (-17 - 5*t^2 + 19*t)*x -
    11*z^2 + (17*t-4)*z + (-14*t^2 - 19*t - 2)
  pol1 = g^2*a^8;
  pol2 = g^2*b^8;
  elapsedTime h = monicGCD(pol1, pol2, Strategy=>"Naive") -- .0025 sec
  assert(h == makeMonic(g^2))

  pol1 = g^3*a^8;
  pol2 = g^3*b^8;
  pol1
  elapsedTime h = monicGCD(pol1, pol2, Strategy=>"Naive") -- .0009 sec
  assert(h == makeMonic(g^3))

  pol1 = g^8*a^8;
  pol2 = g^8*b^8;
  elapsedTime h = monicGCD(pol1, pol2, Strategy=>"Naive") -- .005 sec
  assert(h == makeMonic(g^8))

-- Second -- a double extension
  nextPrime 2^25
  K1 = ZZ/33554467
  A1 = K1[w, z, MonomialOrder => Lex]
  I = ideal(z^3 - 23/2*z^2 + 41*z  - 7, (w^3 - 13*z*w + 14*(z-1) + z^2))
  K2 = toField(A1/I)
  R = K2[x]
  useTower R

  t = w
  g = (10-4*t)*x^2 - 5*x*z^2 + (4*t+1)*x*z + (11 - 17*t^2 + 9*t)*x -
    19*z^2 + (-7*t+6)*z + (-11*t^2 + 15*t + 3)
  a = (18 + 10*t)*x^2 + 10*x*z^2 + (17*t + 2)*x*z + (2 + 17*t^2 + 8*t)*x +
    6*z^2 + (17*t+6)*z + (4*t^2-4*t+2)
  b = (-8-11*t)*x^2 -14*x*z^2 + (8*t-4)*x*z + (-17 - 5*t^2 + 19*t)*x -
    11*z^2 + (17*t-4)*z + (-14*t^2 - 19*t - 2)
  pol1 = g^2*a^8;
  pol2 = g^2*b^8;
  elapsedTime h = monicGCD(pol1, pol2, Strategy=>"Naive") 
  assert(h == makeMonic(g^2))

  pol1 = g^3*a^8;
  pol2 = g^3*b^8;
  pol1
  elapsedTime h = monicGCD(pol1, pol2, Strategy=>"Naive") 
  assert(h == makeMonic(g^3))

  pol1 = g^8*a^8;
  pol2 = g^8*b^8;
  elapsedTime h = monicGCD(pol1, pol2, Strategy=>"Naive") 
  assert(h == makeMonic(g^8))

  -- GCD of several polys in a list
  assert(try(monicGCD({}, Strategy=>"Naive");) false else true)
  elapsedTime h = monicGCD({pol1}, Strategy=>"Naive");
  assert(h == pol1)
  
  elapsedTime h = monicGCD({pol1,pol2,1_R}, Strategy=>"Naive") 
  pol3 = g^7*a*b;
  elapsedTime h = monicGCD({pol1,pol2,pol3}, Strategy=>"Naive")   
  assert(h == makeMonic(g^7))
///

-- TODO: this test is several mashed together

TEST /// -- monicGCDNaive (naive strategy)
-- First, over QQ
  debug needsPackage "Fields" -- for makeMonic
  R = QQ[x]
  (F, G) = ((x-1)^2*(3*x-2), (x-1)*(x^5+1))
  assert(monicGCDNaive(F, G) == x-1)

  (F, G) = ((x^5+1)^2*(3*x-2)^3, (x-1)^4*(x^5+1))
  assert(monicGCDNaive(F, G) == x^5 + 1)

  R = frac(QQ[symbol t])[x]
  useTower R
  (F, G) = ((x-t)^2*(3*x-2*t), (x-t)*((t+1)*x^5+1))
  assert(monicGCDNaive(F, G) == x-t)

  -- example from vHoeij-Monagan 2004
  K1 = frac(QQ[t])
  K2 = toField(K1[z]/(z^2-t))
  R = K2[x]
  F = x^2 + (-2*t+3)/3 * z * x + 5/t * x + 5/t * z - 2/3 * t^2
  G = z * x^2 + 5/t * z * x - (-3 + 2*t^2)/3 * x - 2/3 * t * z + 5/t
  F1 = (x+z)*(x - 2*t*z/3 + 5/t)
  G1 = (z*x+1)*(x - 2*t*z/3 + 5/t)
  F == F1
  G == G1  
  elapsedTime monicGCDNaive(F,G)

  -- example set from vHoeij-Monagan 2004
  K1 = field(QQ[symbol t])
  A1 = K1[symbol z]
  useTower A1
  mz = z^3 - (5-t)*z^2 + (7-t^2)*z  - (9-t^3)
  K2 = field(A1/mz)
  R = K2[x]
  useTower R

  g = (10-4*t)*x^2 - 5*x*z^2 + (4*t+1)*x*z + (11 - 17*t^2 + 9*t)*x -
    19*z^2 + (-7*t+6)*z + (-11*t^2 + 15*t + 3)
  a = (18 + 10*t)*x^2 + 10*x*z^2 + (17*t + 2)*x*z + (2 + 17*t^2 + 8*t)*x +
    6*z^2 + (17*t+6)*z + (4*t^2-4*t+2)
  b = (-8-11*t)*x^2 -14*x*z^2 + (8*t-4)*x*z + (-17 - 5*t^2 + 19*t)*x -
    11*z^2 + (17*t-4)*z + (-14*t^2 - 19*t - 2)

  elapsedTime h = monicGCDNaive(g^2*a^2,g^2*b^2) -- this version is currently the naive one, with quite large intermediate explostion... -- 3 sec!
    -- this gets polynomials of degree 40 in t... integers are not so small either...
  elapsedTime h = monicGCDNaive(g^2*a,g^2*b) -- this version is currently the naive one, with quite large intermediate explostion... -- 3 sec!

  mydenominator h

  -- now do this over Fp
  nextPrime 2^25
  K1 = field(ZZ/33554467[t])
  A1 = K1[z]
  mz = z^3 - (5-t)*z^2 + (7-t^2)*z  - (9-t^3)
  K2 = field(A1/mz)
  R = K2[x]
  useTower R

  g = (10-4*t)*x^2 - 5*x*z^2 + (4*t+1)*x*z + (11 - 17*t^2 + 9*t)*x -
    19*z^2 + (-7*t+6)*z + (-11*t^2 + 15*t + 3)
  a = (18 + 10*t)*x^2 + 10*x*z^2 + (17*t + 2)*x*z + (2 + 17*t^2 + 8*t)*x +
    6*z^2 + (17*t+6)*z + (4*t^2-4*t+2)
  b = (-8-11*t)*x^2 -14*x*z^2 + (8*t-4)*x*z + (-17 - 5*t^2 + 19*t)*x -
    11*z^2 + (17*t-4)*z + (-14*t^2 - 19*t - 2)
  elapsedTime h = monicGCDNaive(g^2*a^2,g^2*b^2) -- this version is currently the naive one, with quite large intermediate explostion... -- .63 sec!
  assert(h == makeMonic(g^2))

-- Older toField way...    
  K1 = frac(QQ[t])
  A1 = K1[z]
  mz = z^3 - (5-t)*z^2 + (7-t^2)*z  - (9-t^3)
  K2 = toField(A1/mz)
  R = K2[x]
  g = (10-4*t)*x^2 - 5*x*z^2 + (4*t+1)*x*z + (11 - 17*t^2 + 9*t)*x -
    19*z^2 + (-7*t+6)*z + (-11*t^2 + 15*t + 3)
  a = (18 + 10*t)*x^2 + 10*x*z^2 + (17*t + 2)*x*z + (2 + 17*t^2 + 8*t)*x +
    6*z^2 + (17*t+6)*z + (4*t^2-4*t+2)
  b = (-8-11*t)*x^2 -14*x*z^2 + (8*t-4)*x*z + (-17 - 5*t^2 + 19*t)*x -
    11*z^2 + (17*t-4)*z + (-14*t^2 - 19*t - 2)
  monicGCDNaive(g^2*a,g^2*b) == makeMonic(g^2)
///

///
  -- Code to do modular methods for gcd
   -- example set from vHoeij-Monagan 2004
  restart
  needsPackage "Fields"
  K1 = field(QQ[symbol t])
  A1 = K1[symbol z]
  useTower A1
  mz = z^3 - (5-t)*z^2 + (7-t^2)*z  - (9-t^3)
  K2 = field(A1/mz)
  R = K2[x]
  useTower R

  g = (10-4*t)*x^2 - 5*x*z^2 + (4*t+1)*x*z + (11 - 17*t^2 + 9*t)*x -
    19*z^2 + (-7*t+6)*z + (-11*t^2 + 15*t + 3)
  a = (18 + 10*t)*x^2 + 10*x*z^2 + (17*t + 2)*x*z + (2 + 17*t^2 + 8*t)*x +
    6*z^2 + (17*t+6)*z + (4*t^2-4*t+2)
  b = (-8-11*t)*x^2 -14*x*z^2 + (8*t-4)*x*z + (-17 - 5*t^2 + 19*t)*x -
    11*z^2 + (17*t-4)*z + (-14*t^2 - 19*t - 2)

  elapsedTime h = monicGCDNaive(g^2*a^2,g^2*b^2) -- this version is currently the naive one, with quite large intermediate explostion... -- 3 sec!
    -- this gets polynomials of degree 40 in t... integers are not so small either...
  elapsedTime h = monicGCDNaive(g^2*a,g^2*b) -- this version is currently the naive one, with quite large intermediate explostion... -- 3 sec!
///

/// -- let's do this with modular methods
  restart
-- step 0: setup field, ring, elements to use for test  
  debug needsPackage "Fields"
  nextPrime (2^28 + 100)
  p = 268435561
  kk = ZZ/p
  K1 = field(kk[symbol t])
  A1 = K1[symbol z]
  useTower A1
  mz = z^3 - (5-t)*z^2 + (7-t^2)*z  - (9-t^3)
  K2 = field(A1/mz)
  R = K2[x]
  useTower R
  g = (10-4*t)*x^2 - 5*x*z^2 + (4*t+1)*x*z + (11 - 17*t^2 + 9*t)*x -
    19*z^2 + (-7*t+6)*z + (-11*t^2 + 15*t + 3)
  a = (18 + 10*t)*x^2 + 10*x*z^2 + (17*t + 2)*x*z + (2 + 17*t^2 + 8*t)*x +
    6*z^2 + (17*t+6)*z + (4*t^2-4*t+2)
  b = (-8-11*t)*x^2 -14*x*z^2 + (8*t-4)*x*z + (-17 - 5*t^2 + 19*t)*x -
    11*z^2 + (17*t-4)*z + (-14*t^2 - 19*t - 2)
  --H = elapsedTime monicGCDNaive(g^2*a^3, g^2*b^3) -- 4.2 sec (1/8 time for over QQ).

--  (terms H)/(f -> (leadMonomial f, terms leadCoefficient leadCoefficient f))
--  val = random kk
--  reduceMod(oo, t, val)

  F0 = g^2*a^2
  G0 = g^2*b^2

  elapsedTime monicGCDModular(F0, G0)

  elapsedTime primitiveAssociate gcd(F0,G0)
      
  F0 = g^5*a^4
  G0 = g^5*b^4

  elapsedTime primitiveAssociate(monicGCDModular(F0, G0))

-- Step 1. Set up the rings we will use. First, let's do this over a finite field
-- TODO: remove below this in the test??
  kk = ZZ/p
  Ap = kk[x, z, t, MonomialOrder => Lex]
  H = monicGCDNaive(g*a, g*b) -- this is what we want to construct?

  G = sub(g*a, Ap)
  F = sub(g*b, Ap)
  Z = sub(ideal mz, Ap)

  val = random kk
  d1 = (monicGCD0(F, G, Z, val), t-val)
  val = random kk
  d2 = (monicGCD0(F, G, Z, val), t-val)
  val = random kk
  d3 = (monicGCD0(F, G, Z, val), t-val)

  d12 = polyCRA(d1, d2, t)
  d13 = polyCRA(d12, d3, t)

  val = random kk
  d4 = (monicGCD0(F, G, Z, val), t-val)
  d14 = polyCRA(d13, d4, t)

  reduceMod(H, d14_1, Ap) == d14_0
  d14_1

  reduceMod(H, d14_1, Ap)
  polyRationalReconstructionOverFiniteField(d14, t)
///

-*
  restart
*-
/// -- test of monicGCDModular with a tower of finite extensions
  needsPackage "Fields"
  nextPrime (2^28 + 100)
  p = 268435561
  kk = ZZ/p
  K1 = field(kk[symbol t])
  z = symbol z
  K2 = field(K1[z_2, z_1, MonomialOrder => Lex]/ideal(z_1^2-t, z_2^3-(z_1+t)))
  R = K2[x]
  useTower R
  g = (10-4*t)*x^2 - 5*x*z_1 + (4*t+1)*x*z_2 + (11 - 17*t^2 + 9*t)*x -
    19*z_2^2 + (-7*t+6)*z_1 + (-11*t^2 + 15*t + 3)
  a = (18 + 10*t)*x^2 + 10*x*z_2^2 + (17*t + 2)*x*z_1 + (2 + 17*t^2 + 8*t)*x +
    6*z_2^2 + (17*t+6)*z_2 + (4*t^2-4*t+2)*z_1
  b = (-8-11*t)*x^2 -14*x*z_2^2 + (8*t-4)*x*z_1 + (-17 - 5*t^2 + 19*t)*x -
    11*z_2^2 + (17*t-4)*z_1 + (-14*t^2 - 19*t - 2)

  F0 = a
  G0 = b
  elapsedTime monicGCDModular(F0, G0)

  F0 = g*a
  G0 = g*b
  ans1 = elapsedTime monicGCDModular(F0, G0)
  ans2 = primitiveAssociate(monicGCDNaive(F0, G0))
  assert(ans1 == ans2)

  F0 = g^2*a
  G0 = g^2*b
  ans1 = elapsedTime monicGCDModular(F0, G0)
  ans2 = elapsedTime primitiveAssociate(monicGCDNaive(F0, G0))
  assert(ans1 == ans2)

  F0 = g^2*a^3
  G0 = g^2*b^3
  ans1 = elapsedTime monicGCDModular(F0, G0)
  --ans2 = elapsedTime primitiveAssociate(monicGCDNaive(F0, G0))
  assert(ans1 == primitiveAssociate (g^2))
///

-*
  restart
  needsPackage "Fields"
*-
/// -- test of monicGCDModular with more than 1 transcendental variable
  nextPrime (2^28 + 100)
  z = symbol z
  t = symbol t
  p = 268435561
  kk = ZZ/p
  K1 = field(kk[t_1, t_2])
  A1 = K1[z]
  useTower A1
  mz = z^3 - (5-t_1)*z^2 + (7-t_2^2)*z  - (9-t_1^3)
  K2 = field(A1/mz)
  R = K2[x]
  useTower R
  g = (10-4*t_1)*x^2 - 5*x*z^2 + (4*t_2+1)*x*z + (11 - 17*t_1^2 + 9*t_2)*x -
    19*z^2 + (-7*t_1+6)*z + (-11*t_2^2 + 15*t_1 + 3)
  a = (18 + 10*t_2)*x^2 + 10*x*z^2 + (17*t_1 + 2)*x*z + (2 + 17*t_1^2 + 8*t_2)*x +
    6*z^2 + (17*t_2+6)*z + (4*t_1^2-4*t_1+2)
  b = (-8-11*t_1)*x^2 -14*x*z^2 + (8*t_2-4)*x*z + (-17 - 5*t_1^2 + 19*t_2)*x -
    11*z^2 + (17*t_2-4)*z + (-14*t_1^2 - 19*t_2 - 2)

  F0 = a
  G0 = b
  elapsedTime monicGCDModular(F0, G0)

  F0 = g*a
  G0 = g*b
  ans1 = elapsedTime monicGCDModular(F0, G0) -- seems quite bad... How long does it take? ZZZZ
  ans2 = elapsedTime primitiveAssociate(monicGCDNaive(F0, G0)) -- faster...!
  assert(ans1 == ans2)

  F0 = g^2*a
  G0 = g^2*b
  ans1 = elapsedTime monicGCDModular(F0, G0)
  ans2 = elapsedTime primitiveAssociate(monicGCDNaive(F0, G0))
  assert(ans1 == ans2)

  F0 = g^2*a^3;
  G0 = g^2*b^3;
  ans1 = elapsedTime monicGCDModular(F0, G0);
  assert(ans1 == primitiveAssociate(g^2))
  --ans2 = elapsedTime primitiveAssociate(monicGCDNaive(F0, G0)) -- takes quite a long time...
  --assert(ans1 == ans2)
///

-*
  restart
*-
/// -- test of monicGCDModular with a tower of finite extensions
  needsPackage "Fields"
  kk = QQ
  K1 = field(kk[symbol t])
  z = symbol z
  K2 = field(K1[z_2, z_1, MonomialOrder => Lex]/ideal(z_1^2-t, z_2^3-(z_1+t)))
  R = K2[x]
  useTower R
  g = (10-4*t)*x^2 - 5*x*z_1 + (4*t+1)*x*z_2 + (11 - 17*t^2 + 9*t)*x -
    19*z_2^2 + (-7*t+6)*z_1 + (-11*t^2 + 15*t + 3)
  a = (18 + 10*t)*x^2 + 10*x*z_2^2 + (17*t + 2)*x*z_1 + (2 + 17*t^2 + 8*t)*x +
    6*z_2^2 + (17*t+6)*z_2 + (4*t^2-4*t+2)*z_1
  b = (-8-11*t)*x^2 -14*x*z_2^2 + (8*t-4)*x*z_1 + (-17 - 5*t^2 + 19*t)*x -
    11*z_2^2 + (17*t-4)*z_1 + (-14*t^2 - 19*t - 2)

  F0 = a
  G0 = b
  elapsedTime monicGCDModular(F0, G0)

  F0 = g*a
  G0 = g*b
  ans1 = elapsedTime monicGCDModular(F0, G0)
  ans2 = elapsedTime primitiveAssociate(monicGCDNaive(F0, G0))
  assert(ans1 == ans2)

  F0 = g^2*a
  G0 = g^2*b
  ans1 = elapsedTime monicGCDModular(F0, G0)
  ans2 = elapsedTime primitiveAssociate(monicGCDNaive(F0, G0))
  assert(ans1 == ans2)

  F0 = g^2*a^3
  G0 = g^2*b^3
  ans1 = elapsedTime monicGCDModular(F0, G0)
  ans2 = elapsedTime primitiveAssociate(monicGCDNaive(F0, G0))
  assert(ans1 == primitiveAssociate (g^2))
///


TEST ///
  -- where does M2 factoring work currently? (May 2025)
  R = ZZ[symbol a..symbol d]
  F = (a+2*b)^2*(3*a+b)^3*123
  factor F

  R = ZZ[x,y,z]
  F = (x+2*y-z^3)^2 * 123 * x * (3*x^3 + y^2) * (2*z^2 + x + y)
  factor F

  R = (GF 9)[x,y,z]
  a
  f1 = x+2*y-a*z^3
  f2 = x
  f3 = 3*x^3 + a^2*y^2
  f4 = 2*z^2 + a*x + y
  F = f1^2 * 100 * f2 * f3 * f4
  F == (x+2*y-a*z^3)^2 * 100 * x * (3*x^3 + a^2*y^2) * (2*z^2 + a*x + y)
  factor F

  KK = frac(ZZ/101[a,b,c])
  F = (a+2*b)^2*(3*a+b)^-3
  factor F -- TODO: this is not so good... the coefficient should be combined.

  R = KK[x,y]
  f1 = 1/a * x
  f2 = 1/b * y
  F = f1 + f2
  factor oo
  -- numerator F -- TODO: want this to work
  -- mydenominator F -- TODO: want this to work

  -- How about factorization over a primitive extension field.
  -- first, over QQ.
  A = QQ[a]
  m = 13*a^3-a-1
  B = A/m
  C = toField B
  R = C[x,y]
  F = 13*x^3-x*y^2-y^3
  factor F
  -- numerator F -- TODO: gives error
  -- denominator F -- TODO: gives error
///

-*
  restart
  debug needsPackage "Fields"
*-
TEST
///
R = ZZ[x]
I1 = ideal (2, x^2 + x + 1)
S1 = R/I1
F1 = field S1
phi1 = fieldInclusion F1
assert(source phi1 === S1)
assert(target phi1 === F1)

use R
I2 = ideal (4, x^2 + x + 1)
S2 = R/I2
assert(try(F2 = field S2; false) else true)

use R
I3 = ideal (nextPrime 2^64, x^2 + x + 1)
S3 = R/I3
assert(try(F3 = field S3; false) else true)

use R
I4 = ideal (nextPrime (2^29 - 100), x^2 + x + 1)
S4 = R/I4
F4 = field S4
phi4 = fieldInclusion F4
assert(source phi4 === S4)
assert(target phi4 === F4)
///

TEST ///
  needsPackage "Fields"
  kk = ZZ/32003
  A1 = field(kk[r]/(r^2-3))
  A2 = field(A1[g_3]/(g_3^4+14661*g_3^2-57))
  R = A2[g_2]
  F = (g_2^8+8*g_2^7*g_3+8*g_2^7*r+28*g_2^6*g_3^2+56*g_2^6*g_3*r+28*g_2^6*r^2
      -10736*g_2^6+56*g_2^5*g_3^3+168*g_2^5*g_3^2*r+168*g_2^5*g_3*r^2
      -410*g_2^5*g_3+56*g_2^5*r^3-410*g_2^5*r+169*g_2^5+70*g_2^4*g_3^4
      +280*g_2^4*g_3^3*r+420*g_2^4*g_3^2*r^2-1025*g_2^4*g_3^2+280*g_2^4*g_3*r^3
      -2050*g_2^4*g_3*r+845*g_2^4*g_3+70*g_2^4*r^4-1025*g_2^4*r^2+845*g_2^4*r
      -15883*g_2^4+56*g_2^3*g_3^5+280*g_2^3*g_3^4*r+560*g_2^3*g_3^3*r^2
      +9301*g_2^3*g_3^3+560*g_2^3*g_3^2*r^3-4100*g_2^3*g_3^2*r
      +1690*g_2^3*g_3^2+280*g_2^3*g_3*r^4-4100*g_2^3*g_3*r^2+3380*g_2^3*g_3*r
      +474*g_2^3*g_3+56*g_2^3*r^5+9301*g_2^3*r^3+1690*g_2^3*r^2+474*g_2^3*r
      -11129*g_2^3+28*g_2^2*g_3^6+168*g_2^2*g_3^5*r+420*g_2^2*g_3^4*r^2
      -1025*g_2^2*g_3^4+560*g_2^2*g_3^3*r^3-4100*g_2^2*g_3^3*r+1690*g_2^2*g_3^3
      +420*g_2^2*g_3^2*r^4-6150*g_2^2*g_3^2*r^2+5070*g_2^2*g_3^2*r
      +711*g_2^2*g_3^2+168*g_2^2*g_3*r^5-4100*g_2^2*g_3*r^3+5070*g_2^2*g_3*r^2
      +1422*g_2^2*g_3*r-1384*g_2^2*g_3+28*g_2^2*r^6-1025*g_2^2*r^4+1690*g_2^2*r^3
      +711*g_2^2*r^2-1384*g_2^2*r+1268*g_2^2+8*g_2*g_3^7+56*g_2*g_3^6*r
      +168*g_2*g_3^5*r^2-410*g_2*g_3^5+280*g_2*g_3^4*r^3-2050*g_2*g_3^4*r
      +845*g_2*g_3^4+280*g_2*g_3^3*r^4-4100*g_2*g_3^3*r^2+3380*g_2*g_3^3*r
      +474*g_2*g_3^3+168*g_2*g_3^2*r^5-4100*g_2*g_3^2*r^3+5070*g_2*g_3^2*r^2
      +1422*g_2*g_3^2*r-1384*g_2*g_3^2+56*g_2*g_3*r^6-2050*g_2*g_3*r^4
      +3380*g_2*g_3*r^3+1422*g_2*g_3*r^2-2768*g_2*g_3*r+2536*g_2*g_3+8*g_2*r^7
      -410*g_2*r^5+845*g_2*r^4+474*g_2*r^3-1384*g_2*r^2+2536*g_2*r-3350*g_2+g_3^8
      +8*g_3^7*r+28*g_3^6*r^2-10736*g_3^6+56*g_3^5*r^3-410*g_3^5*r+169*g_3^5
      +70*g_3^4*r^4-1025*g_3^4*r^2+845*g_3^4*r-15883*g_3^4+56*g_3^3*r^5
      +9301*g_3^3*r^3+1690*g_3^3*r^2+474*g_3^3*r-11129*g_3^3+28*g_3^2*r^6
      -1025*g_3^2*r^4+1690*g_3^2*r^3+711*g_3^2*r^2-1384*g_3^2*r
      +1268*g_3^2+8*g_3*r^7-410*g_3*r^5+845*g_3*r^4+474*g_3*r^3-1384*g_3*r^2
      +2536*g_3*r-3350*g_3+r^8-10736*r^6+169*r^5-15883*r^4
      -11129*r^3+1268*r^2-3350*r+8128)
  G = g_2^2-3*g_3^2
  F % (g_2 - r*g_3)
  F % (g_2 + r*g_3)
  elapsedTime assert(monicGCDNaive(F,G) == g_2 + r*g_3) -- this is using the naive algorithm, quite fast here.
///

-*
  restart
  needsPackage "Fields"
*-
TEST ///
-- 9257 is not invertible...
  kk = ZZ/32003
  A = field(kk[a]/(a^3-a-1))
  R = A[x]
  F = ((x^2-a*x-(a^2-1))^20 * (x-a)^3 * (x - 9257) )
  G = ((x^2-a*x-(a^2-1)) * (x+a)^3 )
  assert(monicGCDNaive(F,G) === null)
///

-*
  restart
  needsPackage "Fields"
*-
TEST /// -- primitive associate, monic associate
-- we will test primitiveAssociate, monicAssociate for all 8 variants of fields.

  -- case 1.

-- example 1. over QQ
  A = QQ[t_1, t_2]
  AZ = ZZ (monoid A)
  K1 = field A
  K1[z_1, z_2, MonomialOrder => Lex]
  K2 = field (K1[z_1, z_2, MonomialOrder => Lex]/(z_2^2-2, z_1^2-z_2-1))

  R = K2[x,y,w]
  useTower R
  F = (t_1 + t_2)/(3*t_1-3*t_2^2) * x * y - (t_1 * z_1 * z_2)^(-1) * w^3 + 1/3
  assert(mydenominator F == 6*t_1*t_2^2-6*t_1^2)
  assert(toString(ring mydenominator F) == "ZZ[t_1..t_2]")
  assert(
      primitiveAssociate F
      ==
      ((3*t_2^2-3*t_1)*z_1*z_2+(-6*t_2^2+6*t_1)*z_1)*w^3+(-2*t_1^2-2*t_1*t_2)*x*y+2*t_1*t_2^2-2*t_1^2
      )
  assert(
      monicAssociate F
      ==
      (3*t_2^2-3*t_1)*w^3+(t_1^2+t_1*t_2)*z_1*z_2*x*y+(-t_1*t_2^2+t_1^2)*z_1*z_2
      )

  -- Another example, constructed at one go
  K0 = QQ[z_1, z_2, t_1, t_2, MonomialOrder => Lex]/(z_2^2-2, z_1^2-z_2-t_1)
  K1 = field K0
  describe K1
  R = K1[x,y,w]
  useTower R
  F = (t_1 + t_2)/(3*t_1-3*t_2^2) * x * y - (t_1 * z_1 * z_2)^(-1) * w^3 + 1/3
  primitiveAssociate F
  monicAssociate F

  K0 = ZZ/134217757[z_1, z_2, t_1, t_2, MonomialOrder => Lex]/(z_2^2-2, z_1^2-z_2-t_1)
  K1 = field K0
  describe K1
  R = K1[x,y,w]
  useTower R
  F = (t_1 + t_2)/(3*t_1-3*t_2^2) * x * y - (t_1 * z_1 * z_2)^(-1) * w^3 + 1/3
  primitiveAssociate F -- this one needs to have a lead coefficient of 1.
  monicAssociate F

  -- no finite extension variables
  K0 = field(ZZ/134217757[t_1, t_2])
  K1 = field K0
  describe K1
  R = K1[x,y,w]
  useTower R
  F = (t_1 + t_2)/(3*t_1-3*t_2^2) * x * y - (t_1 * t_2)^(-1) * w^3 + 1/3
  primitiveAssociate F -- this one needs to have a lead coefficient of 1.
  monicAssociate F
  makeMonic F

  -- no indep variables
  K0 = ZZ/134217757[z_1, z_2, MonomialOrder => Lex]/(z_2^2-2, z_1^2-z_2-1)
  K1 = field K0
  R = K1[x,y,w]
  F = (z_1 + z_2)/(3*z_1-3*z_2) * x * y - (z_1 * z_2)^(-1) * w^3 + 1/3
  primitiveAssociate F -- error: doesn't like lcm of field elements
  mydenominator F -- error: not implemented for this ring
  makeMonic F

  -- no indep variables
  K0 = QQ[z_1, z_2, MonomialOrder => Lex]/(z_2^2-2, z_1^2-z_2-1)
  K1 = field K0
  R = K1[x,y,w]
  F = (z_1 + z_2)/(3*z_1-3*z_2) * x * y - (z_1 * z_2)^(-1) * w^3 + 1/3
  primitiveAssociate F -- wrong: need integer coefficients
  mydenominator F == 1
  makeMonic F -- ok
  
  ///

-*
  restart
  needsPackage "Fields"
*-
TEST /// -- myfactor
  F = field(QQ[c]/(c^3 - 2))
  R = F[x]
  squareFreeFactors (x^3 - 2)
  factor (x^3 - 2) -- works
  assert(set factors (x^3 - 2) == set {{1, x-c}, {1, x^2+c*x+c^2}})
  assert(set factors (2*x^3 - 4) == set {{1, x-c}, {1, x^2+c*x+c^2}})
  
  prettyFactor (x^3 - 2)
  prettyFactor (2*x^3 - 4)
  
  factors (4 * (x^3-2)^3 * (x^2 - 2))
  prettyFactor (4 * (x^3-2)^3 * (x^2 - 2))
  prettyFactor (4 * (2*x^3-4)^3 * (x^2 - 2))
  
  debug Fields
  K0 = field(QQ[c]/(c^3 - 2))
  K1 = field(K0[d]/(d^2 + c*d + c^2))

  R = K1[x]
  squareFreeFactors (x^3 - 2) -- splits linearly.
  factors (x^3-2)
  prettyFactor (x^3 - 2)
  prettyFactor ((1/4)*x^3 - 1/2)
  prettyFactor (c*x^3 - 2*c)
  prettyFactor (d*x^3 - 2*d)
  prettyFactor (c*(c^3*x^3 - 2*c^4))

  K0 = field(QQ[c]/(c^5 - 2))

  R = K0[x]
  factor (x^5 - 2) -- works

  K1 = field(K0[d]/(d^4+c*d^3+c^2*d^2+c^3*d+c^4))

  S = K1[x]

  f = x^5 - 2
  
  -- TODO: make the test values monic
  factors f
  pretFac = prettyFactor f

  assert(value pretFac == f)
  
  assert(
    set ((squareFreeFactors(x^5-2))/makeMonic)
    ===
    set {
      x-d,x-(1/2)*d^3*c^3,x+(1/2)*d^3*c^3+(1/2)*d^2*c^4+d+c,x-c,x-(1/2)*d^2*c^4
      }
  )
///

-*
  restart
  needsPackage "Fields"
*-
TEST ///

  p = 32003
  A = ZZ/p
  K = field (A[c]/(c^2 + c + 1))
  R = K[x]
  
  f = x^3 - 1
  factors f

  A = QQ[t]
  K = field A
  R = K[x];
  
  f = x^3 - t^3
  factors f

  debug needsPackage "Fields"
  allFields = allFieldCases 32003;
  for K in allFields do (
    if (fieldInfo K).Finites === null then continue;  -- TODO: remove this line
    R := K[x];
    << "basic test for factors over " << describe K << endl;
    factors (x^3 - 2)
  )
  
///

-*
  restart
debug   needsPackage "Fields"
*-
///
  -- How about over a fraction field?
  K0 = field(QQ[t1,t2])
  K1 = field(K0[z]/(z^3-t1))
  describe K1
  baseRing K1
  R = K1[x]
  x^3-t1
  factor(x^3-t1) -- nope
  myFactor(x^3-t1) -- NOT WORKING
  useTower R
  numR = K0[x, z, MonomialOrder => Lex]
  resultant(x^3-t1, z^3-t1, z)
  monicGCDNaive(x^3-t1, oo)

  F = K1
  newF = coefficientRing F
        phi = map(newF, F)
        phiinv = map(F, newF)
        k = coefficientRing newF -- either a bsic field, or a pure fraction field
        tryPrim = sum gens newF
        G = k(monoid[X]);
        psi = map(newF,G,{tryPrim})
        degExtn = numcols basis newF
        minPoly = first flatten entries gens ker psi
        if first degree minPoly != degExtn then error "Selected primitive element, or sum of variables, not primitive.";
        -- TODO: Adapt our primitive element if the sum is not primitive
        --       allow for user-provided primitive element, or random
        quotG = G/ideal(minPoly)
        psiQuotG = map(newF, quotG, {tryPrim})
        tfQuotG = field quotG -- TODO: toField => field, but need to fix code...
        tfPsi = map(F, tfQuotG, {tryPrim})
        tfPsiInv = map(tfQuotG, F, tfQuotG.cache.FieldInclusion((psiQuotG^(-1)).matrix))
        assert(tfPsi * tfPsiInv == 1);
        (tfPsi, tfPsiInv)
  
///

-*
  restart
  needsPackage "Fields"
*-
TEST ///
  U = QQ[x]
  a = adjoinRoot(x^3-x-1, Variable => symbol a)
  K = ring a
  K[x]
  f = x^3 - x - 1
  facs = factors f
  assert(#facs == 2)
  assert(isMember(x - a, facs / last))
  assert(value factorData f == f)

  b = adjoinRoot(((ring a)[x]; x^3-a), Variable => symbol b)
  K = ring b
  K[x]
  f = x^3 - a
  facs = factors f
  assert(#facs == 2)
  assert(isMember(x - b, facs / last))
  assert(value factorData f == f)

  c = adjoinRoot(((ring b)[x]; x^2 + x + 1), Variable => symbol c)
  K = ring c
  K[x]
  f = x^2 + x + 1
  facs = factors f
  assert(#facs == 2)
  assert(isMember(x - c, facs / last))
  assert(value factorData f == f)

  g = x^3 - a
  facs2 = factors g
  assert(#facs2 == 3)
  assert(all(facs2 / first, n -> n == 1))
  assert(value factorData g == g)  

  U = QQ[x]
  a = adjoinRoot(x^4-2, Variable => symbol a)
  assert(try (adjoinRoot( ((ring a)[x]; x^2 - 2), Variable => symbol b); false) else true)

///

-*
  restart
  needsPackage "Fields"
*-
TEST /// -- splitting field of a polynomial "by hand"
    d = 4
    kk = QQ
    R0 = kk[x]
    f = x^d + sum apply(d, i -> random ZZ * x^i)
    while not isIrreducible f do f = x^d + sum apply(d, i -> random ZZ * x^i);
    assert(isIrreducible f)

    elapsedTime S = splittingField(f, Variable => a)
   
    a = adjoinRoot(f, Variable => symbol a)
    K = ring a
    R1 = K[x]
    phi = map(R1,R0)
    facs = factors phi f
    g = last first select(1,facs, p -> first degree p#1 > 1)

    b = adjoinRoot(g, Variable => symbol b)
    K = ring b
    R2 = K[x]
    phi = map(R2,R0)
    facs = factors phi f
    g = last first select(1,facs, p -> first degree p#1 > 1)

    c = adjoinRoot(g, Variable => symbol c)
    K = ring c
    R3 = K[x]
    phi = map(R3,R0)

    facData = factorData phi f
    assert(value facData == phi f)
    assert(all(facData.Factors, p -> p#0 == 1 and first degree p#1 == 1))

    kk = field(QQ[t])
    R0 = kk[x]
    f = x^3 - t*x + 1
    assert(isIrreducible f)
    
    a = adjoinRoot(f, Variable => symbol a)
    K = ring a
    R1 = K[x]
    phi = map(R1,R0)
    facs = factors phi f
    g = last first select(1,facs, p -> first degree p#1 > 1)

    b = adjoinRoot(g, Variable => symbol b)
    K = ring b
    R2 = K[x]
    phi = map(R2,R0)
    facs = factors phi f

    -- TODO: Finish this test.
///

-*
  restart
  debug needsPackage "Fields"
*-
TEST ///
    -- making sure splitting field gives the right answer
    -- should get a degree 12 extension (the Galois group is A_4)
    kk = QQ
    R0 = kk[x]
    f = x^4 + 8*x + 12

    a_1 = adjoinRoot(f, Variable => (symbol a)_1)
    R1 = (ring a_1)[x]
    factors sub(f,R1)
    g = last last factors sub(f, R1)

    a_2 = adjoinRoot(g, Variable => (symbol a)_2)
    R2 = (ring a_2)[x]
    facs = monicFactors sub(f, R2)
    assert(product apply(facs, p -> (p#1)^(p#0)) == sub(f,R2))
    assert(all(facs, p -> degree last p == {1} and first p == 1))
    assert(extensionDegree (ring a_2) == 12)

    ll = splittingField(f, Variable => symbol b)
    assert(extensionDegree ll == 12)
    S = ll[x]
    facs = monicFactors sub(f, S)
    assert(product apply(facs, p -> (p#1)^(p#0)) == sub(f,S))
    assert(all(facs, p -> degree last p == {1} and first p == 1))

    -* experimenting with polredbest from RationalPoints2
    debug Fields
    debug needsPackage "RationalPoints2"
    primInfo = computePrimitiveInfo ll
    minPoly = primInfo.MinimalPolynomial
    h = polredbest minPoly
    mm = splittingField(h, Variable => c)
    phi = map(ll[x], (ring h), {x})
    rootsOverLL = rootsFromFactors phi h
    psi = map(ll,mm,{first rootsOverLL})
    psiInv = map(mm,ll,{mm_0})
    *-
///

-*
  restart
  needsPackage "Fields"
*-
-- TODO: Operations such as these should "just work".
--       Potential workarounds include installing base rings, promotions, etc.
--       When one creates a field, install several promotions
///
A = QQ[x]
B = A[y]/(y^2 - x^3)
kA = field A
kB = field B
A_0 + kB_0
kA_0 + B_0
kA_0 + kB_0
fieldInclusion kB
fieldInclusion kA
///


TEST ///
    R = QQ[x]
    a = adjoinRoot(x^2 - 2, Variable => symbol a)
    use R
    b = adjoinRoot(x^2 - 3, Variable => symbol b)
    phi = map(ring a, ring b, {a})
    assert(not isWellDefined phi)
///

-*
  restart
  needsPackage "Fields"
*-
TEST /// -- reductionMap, numeratorMap
-- need also to find Iz, and ambient ring of R or F.
-- notation:
--  R = k(tvars)[zvars]/Iz [xvars] --  k is a basic finite field or QQ.
-- needs several rings:
--  A = k[xvars, zvars, tvars], Iz in A (i.e. no denominators).
--  maybe: ambient R = k(tvars)[xvars, zvars]
--  Rp = ZZ/p(tvars)[zvars]/Izp [xvars] -- or GF q.
--  Ap = ZZ/p[xvars, zvars, tvars] -- Iz in A (i.e. no denominators). also GF q...

  debug needsPackage "Fields"
  kk = field(ZZ[t])
  fieldInfo kk
  A = field(kk[a]/(a^2+a+t))
  B = field(A[b]/(b^3 - a*t - 1))
  R = B[x]
  
  -- test numeratorMap first
  (AtoB, BtoA, xztvars, Iz) = numeratorMap B
  BZZ = source AtoB
  instance(BZZ, PolynomialRing)
  assert(ideal BZZ == 0)
  assert(target AtoB === B)
  assert(source AtoB === BZZ)
  assert(target BtoA === BZZ)
  assert(source BtoA === B)
  assert(toList flatten xztvars === gens BZZ)
  assert(ring Iz === BZZ)
  Bgens = matrix{generators(B, CoefficientRing => ZZ)}
  assert(AtoB BtoA Bgens === Bgens)

  -- numeratorMap for R
  (AZZtoR, RtoAZZ, xztvars, Iz) = numeratorMap R
  AZZ = source AZZtoR
  instance(AZZ, PolynomialRing)
  assert(ideal AZZ == 0)
  assert(target AZZtoR === R)
  assert(source AZZtoR === AZZ)
  assert(target RtoAZZ === AZZ)
  assert(source RtoAZZ === R)
  assert(toList flatten xztvars === gens AZZ)
  assert(ring Iz === AZZ)
  Rgens = matrix{generators(R, CoefficientRing => ZZ)}
  assert(AZZtoR RtoAZZ Rgens === Rgens)

  -- numeratorMap for Rp done after reductionMap...
  RtoRp = reductionMap(R, 23)
  Rp = target RtoRp
  Rpgens = matrix{generators(Rp, CoefficientRing => ZZ/23)}
  assert(source RtoRp === R)
  assert(char Rp === 23)
  -- what about the lift map?
  RptoR = map(R, Rp)
  assert(RtoRp RptoR Rpgens == Rpgens)
  
  -- numeratorMap for Rp
  (AptoRp, RptoAp, xztvars, Iz) = numeratorMap(Rp, AZZ)
  Ap = source AptoRp
  instance(Ap, PolynomialRing)
  assert(ideal Ap == 0)
  assert(target AptoRp === Rp)
  assert(source AptoRp === Ap)
  assert(target RptoAp === Ap)
  assert(source RptoAp === Rp)
  assert(toList flatten xztvars === gens Ap)
  assert(ring Iz === Ap)
  Rpgens = matrix{generators(Rp, CoefficientRing => ZZ)}
  assert(AptoRp RptoAp Rpgens === Rpgens)
  assert(entries AptoRp vars Ap === entries Rpgens) -- degrees differ...
  assert(monoid Ap === monoid AZZ)
  
  -- TODO: check examples with more generators...
///

-*
  restart
  debug needsPackage "Fields"
*-
TEST /// -- test of distinctDegreeFactorization
  kk = QQ
  F0 = field(QQ[t])
  F1 = field(F0[b]/(b^2+b+t))
  F2 = field(F1[a]/(a^3-b*t))
  describe F2
  F2.cache.FieldInfo
  R = F2[x]
  useTower R
  f = (x-b)^3*(x-(a+b*t)^2)^2*(x-a)
  distinctDegreeFactors f
///

-*
restart
needsPackage "Fields"
*-
TEST
///
kk = ZZ/101
fieldInfo kk
A = field(kk[a]/(a^2+a+1))
extensionBasis A
multa = multiplicationMap a
assert(multa == matrix {{0, -1}, {1_kk, -1}})

B = field(A[b]/(b^3 - a - 1))
extensionBasis B
multab = multiplicationMap (a + b)
minimalPolynomial(multab,kk[T])
minimalPolynomial(a + b,kk[T])

f1 = randomElement B
f1Mult = multiplicationMap f1
f2 = randomElement B
f2Mult = multiplicationMap f2
g = f1*f2
gMult = multiplicationMap g
assert(f1Mult * f2Mult == gMult)
///

-*
restart
needsPackage "Fields"
*-
TEST
///
kk = field(ZZ/101[t])
P = kk[T]
fieldInfo kk
A = field(kk[a]/(a^2+a+1))
extensionBasis A
multa = multiplicationMap a
assert(multa == matrix {{0, -1}, {1_kk, -1}})

B = field(A[b]/(b^3 - a - 1))
extensionBasis B
multab = multiplicationMap (a + b)
minPolyab = T^6+3*T^5+6*T^4+6*T^3+9*T^2+9*T+3
assert(minPolyab == minimalPolynomial(multab,P))
assert(minPolyab == minimalPolynomial(a + b,P))
///


-*
restart
needsPackage "Fields"
*-
TEST
///
kk = field(ZZ/101[t])
P = kk[T]
fieldInfo kk
A = field(kk[a]/(a^2+a+t))
extensionBasis A
multa = multiplicationMap a
assert(entries multa == entries matrix {{0, -t}, {1_kk, -1}})

B = field(A[b]/(b^3 - a*t - 1))
extensionBasis B
multab = multiplicationMap (a + b)
minPolyab = T^6+3*T^5+(3*t+3)*T^4+(7*t-1)*T^3+(9*t^2+3*t-3)*T^2+(6*t^2+6*t-3)*T+t^2+2*t
assert(minPolyab == minimalPolynomial(multab,P))
assert(minPolyab == minimalPolynomial(a + b,P))
///

-*
restart
needsPackage "Fields"
*-
TEST
///
kk = field(QQ[t])
P = kk[T]
fieldInfo kk
A = field(kk[a]/(a^2+a+t))
extensionBasis A
multa = multiplicationMap a
assert(entries multa == entries matrix {{0, -t}, {1_kk, -1}})

B = field(A[b]/(b^3 - a*t - 1))
extensionBasis B
multab = multiplicationMap (a + b)
minPolyab = T^6+3*T^5+(3*t+3)*T^4+(7*t-1)*T^3+(9*t^2+3*t-3)*T^2+(6*t^2+6*t-3)*T+t^2+2*t
assert(minPolyab == minimalPolynomial(multab,P))
assert(minPolyab == minimalPolynomial(a + b,P))
///


-*
restart
debug needsPackage "Fields"
*-
TEST
///
-- Given F = QQ(t)[a]/(a^2+a+t)
-- and f = x^2 + x + t in R = F[x]
-- then f factors as 
--
debug needsPackage "Fields"
kk = field(QQ[t])
fieldInfo kk
A = field(kk[a]/(a^2+a+t))
B = field(A[b]/(b^3 - a*t - 1))
primInfo = computePrimitiveInfo B
use ring primInfo.MinimalPolynomial
minPolyab = T^6+3*T^5+(3*t+3)*T^4+(7*t-1)*T^3+(9*t^2+3*t-3)*T^2+(6*t^2+6*t-3)*T+t^2+2*t
assert(primInfo.PrimitiveElement == a + b)
assert(primInfo.MinimalPolynomial == minPolyab)

phi = primInfo.FromPrimitive
psi = primInfo.ToPrimitive
PB = target psi
assert(getCoefficientField PB === PB)
assert(source psi === B)
assert(target phi === B)
assert(source phi === PB)

psi a
psi b
use source phi -- set T from source phi.
assert((psi * phi)(T) == T)
use source psi -- set T from source phi.
assert((phi * psi)(a) == a)
assert((phi * psi)(b) == b)
assert((psi a)^2 + (psi a) + psi t == 0)
assert((psi b)^3 - (psi a) * t - 1 == 0)
-- this is continued in the string block below
///

///
-- this is continued from the previous test
a
b
R = B[x]
f = x^2 + x + t
--factor f -- nope
RP = PB (monoid R)
  assert(getCoefficientField RP === PB)
psi' = inducedPolynomialMap(psi, RP, R)
phi' = inducedPolynomialMap(phi, R, RP)

assert(phi' psi' f == f)
g = psi' f
--factor g -- nope
RZ = ZZ[x, T, t, MonomialOrder => Lex]
fz = sub(psi' f, RZ)
mpPB = sub((ideal coefficientRing PB)_0, RZ) -- minpoly of T 
resultant(fz, mpPB, T) -- this is a power of a irreducible...
factor oo
mpPBShift = resultant(sub(fz, x => x-T), mpPB, T)
factor mpPBShift
facs = (factor mpPBShift)//toList/toList
netList oo
facs = facs / first

-- try #1: shift factors by x => x+T, and place into the ring RP = PB[x]
useTower ring facs_0
shiftBackFacs = for h0 in facs list sub(sub(h0, x => x+T), RP)
shiftBackFacs/ring
fac0 = monicGCDNaive(shiftBackFacs_0, psi' f)
fac1 = monicGCDNaive(shiftBackFacs_1, psi' f)
fac0 * fac1 == psi' f
phi' fac0
phi' fac1

-- TODO: Why are these not finishing?
-- fac0' = monicGCDModular(shiftBackFacs_0, psi' f)
-- fac1' = monicGCDModular(shiftBackFacs_1, psi' f)

-- try#2: shift f, not the factors.  take gcd, then shift x => x + T
facsh = (factor mpPBShift)//toList/toList/first
facsh = for h0 in facsh list sub(h0, RP)

-- TODO: not correct yet:
fac0'' = monicGCDNaive(facsh_0, sub(psi' f, RP_0 => RP_0 + sub(T, RP)))
fac1'' = monicGCDNaive(facsh_1, sub(mpPBShift, RP))
///

-*
restart
needsPackage "Fields"
*-
TEST
///
-- Given F = QQ(t)[a]/(a^2+a+t)
-- and f = x^2 + x + t in R = F[x]
-- then f factors as 
--
kk = field(QQ[t])
fieldInfo kk
A = field(kk[a]/(a^2+a+t))
B = field(A[b]/(b^3 - a*t - 1))
R = B[x]
f = x^2 + x + t
assert(set squareFreeFactors f === set { x + a + 1, x - a})
///

-*
  restart
  needsPackage "Fields"
*-
-- here is a test at using multiple resultants
-- TODO: In progress
///
  kk = QQ
  F0 = field(QQ[t])
  F1 = field(F0[b]/(b^2+b+t))
  F2 = field(F1[a]/(a^3-b*t))
  describe F2
  F2.cache.FieldInfo
  R = F2[x]
  useTower R
  f = (x-b)*(x-(a+b*t)^2)*(x-(a+b^2))
  squareFreeFactors f  -- too slow with monicGCDNaive Ouch, wrong.,..
  RZ = ZZ[x, a, b, t, MonomialOrder => {4:1}]

  -- method 1A
  fZ = sub(f, RZ)
  gZ = translatedResultant(fZ, R, 1, a)
  hZ = translatedResultant(gZ, R, 2, b)
  facs = (factor hZ)//toList/toList/first; -- TODO: make sure it is squarefree?
  facs/(f -> sub(f, {x => x + a + 2*b}))
  oldfacs = facs/(f -> sub(sub(sub(f, x => x + a + 2*b), R), RZ))
  elapsedTime answer = for g in oldfacs list monicGCDModular(sub(g, R), f)
  assert(product answer == f)

  -- method 1B
  fZ = sub(f, RZ)
  gZ = translatedResultant(fZ, R, 1, a)
  hZ = translatedResultant(gZ, R, 2, b)
  facs = (factor hZ)//toList/toList/first; -- TODO: make sure it is squarefree?
  resultants = {sub(gZ, R), f}
  elems = {sub(2*b, R), sub(a, R)};
  origfacs = facs/(g -> sub(g, R));
  facs = origfacs
  elapsedTime for i from 0 to 1 do (
      facs1 := facs/(g -> sub(g, {R_0 => R_0 + elems#i }));
      facs = for g in facs1 list monicGCDModular(g, resultants#i);
      )
  ans = facs
  assert(product ans === f)
  
  -- method 2: primitive elements
  debug needsPackage "Fields"
  --(phi, psi) = primitiveElementMaps F2 -- doesn't work yet.
  P = (coefficientRing coefficientRing F2)[c]
  (primelem, minpol, phi, psi) = toSequence computePrimitiveInfo(F2, P)
  R' = (source phi)(monoid R)
  minpol
  phi' = inducedPolynomialMap(phi, R, R')
  psi' = inducedPolynomialMap(psi, R', R)
  phi' * psi'
  psi' * phi'
  f' = psi' f
  useTower ring f'
  f'' = (27*t^2-9*t+1) * f'
  
  Rnum = QQ[x, c, t]
  f''' = sub(f'', Rnum)
  g = sub(minpol, Rnum)
  use Rnum
  h = sub(f''', x => x)
  h1 = resultant(h, g, c)
  facs = factor h1 // toList / toList
  S = F0[c]
  L = field(S/(sub(minpol, S)))
  S1 = L[symbol x]
  for i from 1 to 3 list sub(facs#i#1, S1)
  for fac in oo list monicGCDModular(fac, sub(f''', S1))   -- TODO: this is wrong
    
  resultant(f', sub(minpol, ring f'), sub(c, ring f'))
  fieldContent f' -- FAILS
  fieldContent f' -- FAILS
  E = toField source phi
  Ex = E (monoid R)
  f'' = (fieldContent (leadCoefficient last terms f'))^-1 * f'
  f''' = sub(f'', Ex)
  factor f'''
  
  
  f
  netList oo  
    
  -- method 1C -- not working yet
  eqns = ideal F2.cache.FieldInfo.Finites
  FZ = ring eqns -- not over ZZ, but QQ(t)
  RZ = FZ (monoid R)
  eqns = (promote(eqns, RZ))_*
  fZ = sub(f, RZ)
  finiteVars = (gens FZ)/(g -> promote(g, RZ));
  gZ = translatedResultant(fZ, R, 1, finiteVars#0)
  hZ = translatedResultant(gZ, R, 2, finiteVars#1)
  facs = (factor hZ)//toList/toList/first; -- TODO: make sure it is squarefree?
  facs/(f -> sub(f, {x => x + a + 2*b}))
  oldfacs = facs/(f -> sub(sub(sub(f, x => x + a + 2*b), R), RZ))
  elapsedTime answer = for g in oldfacs list monicGCDModular(sub(g, R), f)
  assert(product answer == f)

  -- factor fZ -- just check that without the field equations, this doesn't factor
  gZ = resultant(sub(fZ, {x => x-a}), a^3-b*t, a)
  g = sub(gZ, R)
  gZ = sub(g, RZ)
  use RZ
  hZ = resultant(sub(gZ, {x => x - 2*b}), b^2+b+t, b)
  h = sub(hZ, R)
  hZ = sub(h, RZ)
  factor hZ -- 3 factors.
  facs = (factor hZ)//toList/toList/first
  netList facs
  Rt = QQ[t]
  useTower R
  facs = for f in facs list sub(f, R)
  sub(facs_0, R)
  facslevel1 = for fac in facs list (
      fac0 := sub(fac, x => x+2*b);
      monicGCDModular(g, fac0)
      )
  finalfacs = facslevel2 = for fac in facslevel1 list (
      fac0 := sub(fac, x => x + a);
      monicGCDModular(f, fac0)
      )
  assert(f == product finalfacs) -- YES!!

-- To make a function that does this:
-- factor (f in R = F[x]):
-- create RZ, maps RZ --> R, R --> RZ (only works on elements of R that are not fractions...)
-- create the extension rings too?
-- list all of the extension polynomials (in RZ). m1, ..., mr.
-- g1 = resultant(f(x-c1*z1, m1, z1) -- somehow detect whether c1 was a good choice...
-- g2 = resultant(g1(x-c2*z2, m2, z2)
-- ...
-- gr = resultant(g(r-1)(x - cr*zr), mr, zr)
--   This gr is a polynomial in x, t1, ..., tm.
-- facs_r := factors of gr.
-- now for j = r-1 downto 0 (f = g0) do:
--   for each factor fac of 
--   monicGCDModular(gj, 
///

/// -- methods to implement this
-- method 1: do everything with R, RZ, essentially as above.


-- method 2: create a tower of polynomial rings, do the computations there.
-- method 3: choose the x => x + (random) * a + (random * b), do iterated resultants.
--   seems we still want to reduce each though...  

///

-*
restart
debug needsPackage "Fields"
*-
TEST ///
  debug needsPackage "Fields"  
  K0 = field(QQ[c]/(c^3 - 2))
  K1 = field(K0[d]/(d^2 + c*d + c^2))
  -- note that both c + 2d and 2c + d have minl poly T^6 + 108
  primInfo = computePrimitiveInfo K1
  use ring primInfo.MinimalPolynomial
  assert(primInfo.MinimalPolynomial == T^6+108)
  phi = primInfo.FromPrimitive
  psi = primInfo.ToPrimitive
  assert(isWellDefined phi)
  assert(isWellDefined psi)
  assert(phi * psi == 1)
  -- assert(psi * phi == 1) -- FAILS (related to degreeMap?)

  psi c
  psi d

  assert(phi psi c == c)
  assert(phi psi d == d)
///

-*
restart
debug needsPackage "Fields"
*-
TEST ///
  debug needsPackage "Fields"
  kk = field(QQ[t])
  K0 = field(kk[c]/(c^3 - t))
  K1 = field(K0[d]/(d^2 + c*d + c^2))
  -- note that both c + 2d and 2c + d have minl poly T^6 + 108
  primInfo = computePrimitiveInfo K1
  use ring primInfo.MinimalPolynomial
  assert(primInfo.MinimalPolynomial == T^6+27*t^2)
  phi = primInfo.FromPrimitive
  psi = primInfo.ToPrimitive
  assert(isWellDefined phi)
  assert(isWellDefined psi)
  assert(phi * psi == 1)
  -- assert(psi * phi == 1) -- FAILS (related to degreeMap?)

  psi c
  psi d

  assert(phi psi c == c)
  assert(phi psi d == d)

  R = K1[x]
  f = (x^2 - c) * (x^3 - d)
  monicGCDNaive(f, diff(x,f))
  -- good example, as it seems the shift is not helping in the resultant code
  -- squareFreeFactors f
///

///
-- start with f above, place it into RprimF
  cont = fieldContent psi' f
  f1 = primitiveAssociate psi' f
  makeMonic f1
  assert(ring f1 === RprimF)
  gensRprimF = gens(RprimF, CoefficientRing => ZZ)
  f2 = sub(f1, RprimF_0 => RprimF_0 - 2 * gensRprimF_1)
  f3 = sub(f2, RprimFoverZ)
  h1 = resultant(f3, mpPrimF, RprimFoverZ_1)
  factor h1
  positiveDegreeFactors h1  
///

-*
restart
needsPackage "Fields"
*-
///
  kk = field(ZZ/3[t])
  R = kk[x]
  distinctDegreeFactors (x^3 - t)
///

-*
  restart
  needsPackage "Fields"
*-
TEST ///
  -- discriminants over towers.
  K = field(QQ[a]/(a^3-2))
  L = field(K[b]/(b^2-a^2-2))
  A = L[x]
  useTower A
  (x-a)*(x^2+x-b)
  toString oo
  describe L
  R = QQ[x,b,a, MonomialOrder => Lex]
  f1 = a^3-2
  f2 = b^2-a^2-2
  F = x^3+(-a+1)*x^2+(-b-a)*x+b*a
  g1 = resultant(F,f2,b)
  g2 = resultant(x-a, f1, a)
///

-*
  restart
  needsPackage "Fields"
*-
TEST /// 
-- ZZZZ
  debug needsPackage "Fields"
  kk = field(QQ[t])
  fieldInfo kk
  A = field(kk[a]/(a^2+a+t))
  B = field(A[b]/(b^3 - a*t - 1))
  primInfo = computePrimitiveInfo B
  use ring primInfo.MinimalPolynomial
  minPolyab = T^6+3*T^5+(3*t+3)*T^4+(7*t-1)*T^3+(9*t^2+3*t-3)*T^2+(6*t^2+6*t-3)*T+t^2+2*t
  assert(primInfo.PrimitiveElement == a + b)
  assert(primInfo.MinimalPolynomial == minPolyab)

  R = B[x]
  phi = primInfo.FromPrimitive
  psi = primInfo.ToPrimitive
  
  PB = target psi
  RP = PB (monoid R)

  useTower RP
  g0 = x^2+x+t
  g1 = x^6+(6*T+6)*x^5+(15*T^2+30*T+15)*x^4+(20*T^3+60*T^2+60*T+t+18)*x^3+(15*T^4+60*T^3+90*T^2+(3*t+54)*T+3*t+9)*x^2+(6*T^5+30*T^4+60*T^3+(3*t+54)*T^2+(6*t+18)*T+3*t)*x+3*T^5+(-3*t+12)*T^4+(-6*t+19)*T^3+(-9*t^2+12)*T^2+(-6*t^2-3*t+3)*T+t^3-t^2-2*t

  -- TODO: the following doesn't appear to finish...
  monicGCDModular(g0, g1)
  monicGCDModular(g1, g0)

  -- here is a prime
  K1 = field(ZZ/268435463[t])
  K2 = field(K1[T]/(T^6+3*T^5+(3*t+3)*T^4+(7*t-1)*T^3+(9*t^2+3*t-3)*T^2+(6*t^2+6*t-3)*T+t^2+2*t))
  R = K2[x]
  g0 = x^2+x+t
  g1 = x^6+(6*T+6)*x^5+(15*T^2+30*T+15)*x^4+(20*T^3+60*T^2+60*T+t+18)*x^3+(15*T^4+60*T^3+90*T^2+(3*t+54)*T+3*t+9)*x^2+(6*T^5+30*T^4+60*T^3+(3*t+54)*T^2+(6*t+18)*T+3*t)*x+3*T^5+(-3*t+12)*T^4+(-6*t+19)*T^3+(-9*t^2+12)*T^2+(-6*t^2-3*t+3)*T+t^3-t^2-2*t
  ans1 = monicGCDNaive(g0, g1)

  ans2 = monicGCDModular(g0, g1)
  assert(makeMonic ans2 == ans1)
///


///
 -- example from vHoeij-Monagan 2004
  restart
  needsPackage "Fields"
  K1 = field(QQ[t])
  K2 = field(K1[z]/(z^2-t))
  R = K2[x]
  useTower R
  F = x^2 + (-2*t+3)/3 * z * x + 5/t * x + 5/t * z - 2/3 * t^2
  G = z * x^2 + 5/t * z * x - (-3 + 2*t^2)/3 * x - 2/3 * t * z + 5/t
  -- TODO: A function: F --> the "simple" associate of F
  F1 = (x+z)*(x - 2*t*z/3 + 5/t)
  G1 = (z*x+1)*(x - 2*t*z/3 + 5/t)
  F == F1
  G == G1  
  H = monicGCDNaive(F,G)
  F1' = 3*t*F
  G1' = 3*t*G
  assert(primitiveAssociate F === F1')
  assert(primitiveAssociate G === G1')
  assert(monicGCDModular(F1', G1') === primitiveAssociate H)
  
  -- R1 = ZZ[x, z, t, MonomialOrder => Lex]
  -- f1 = sub(F1', R1)
  -- g1 = sub(G1', R1)

  -- nextPrime 2^28
  -- p = 268435459

  -- -- interestingly, using a GB leads to several components:
  -- Ap = ZZ/p[x,z,t, MonomialOrder => {1,1,1}]
  -- I = ideal(z^2-t, sub(F1', Ap), sub(G1', Ap))
  -- groebnerBasis I
  -- decompose I


  -- f1p = reduceMod(f1, p)
  -- g1p = reduceMod(g1, p)
  -- use ring f1p
  -- mz = z^2-t
  -- mzp = reduceMod(mz, p)

  -- f1p = sub(f1p, Ap)
  -- g1p = sub(g1p, Ap)
  -- mz = sub(mz, Ap)

  -- f1p
  -- g1p
  -- eval1 = (Ap, i) -> (
  --     kk := coefficientRing Ap;
  --     a := random  kk;
  --     (map(Ap, Ap, {Ap_i => a}), Ap_i - a)
  --     )
  -- {x}, {z}, {t}, {f1p, g1p}, {mz}
  -- -- this isn't quite working...
  -- gcdMod = method()
  -- gcdMod(RingElement, RingElement, Ideal, Sequence) := (F, G, Iz, data) -> (
  --     (xvars, zvars, var, randelem) := data;
  --     -- make the pseudo-field first
  --     Ap := ring F;
  --     kk := coefficientRing Ap; -- prime field or at least a finite field.
  --     A0 := kk(monoid[zvars]);
  --     I0z := sub(sub(Iz, Ap_var => randelem), A0);
  --     K0 := field(A0/I0z);
  --     R0 := K0(monoid[x]);
  --     f0 := sub(sub(F, Ap_var => randelem), R0);
  --     g0 := sub(sub(G, Ap_var => randelem), R0);
  --     (sub(monicGCDNaive(f0, g0), Ap), Ap_var - randelem)
  --     )
  -- use Ap
  -- gcdMod(f1p, g1p, ideal (z^2-t), ({x}, {z}, 2, 3252351))
  -- a = random (coefficientRing Ap)
  -- use Ap
  -- gcdMod(f1p, g1p, ideal (z^2-t), ({x}, {z}, 2, a))
      
  -- (phi,tc) = eval1(Ap, 2)
  -- phi f1p, phi g1p
  -- phi mz

  
  
  -- A1 = ZZ/p[z]
  -- K1 = field(A1/sub(phi mz, A1))
  -- R1 = K1[x]
  -- f1' = sub(phi f1p, R1)
  -- g1' = sub(phi g1p, R1)
  -- monicGCDNaive(f1', g1')
  
  -- -- our goal is to find the (monic associate) gcd of F, G mod p.
  -- useTower ring F
  -- gcdFG = 3*t*  monicGCDNaive(F,G)

  -- K1p = field(ZZ/p[t])
  -- K2p = field(K1p[z]/(z^2-t))
  -- Rp = K2p[x]
  -- useTower Rp
  -- f1p = sub(F1', Rp)
  -- g1p = sub(G1', Rp)
  -- -- goal: compute this using modular methods:
  -- t * monicGCDNaive(f1p, g1p)

  -- Sp = ZZ/p[x,t,z, MonomialOrder => Lex]
  -- gcds = for i from 1 to 5 list (
  --     randomval = random p;
  --     K = field(ZZ/p[z]/(z^2-randomval));
  --     R2 = K[x];
  --     ev = map(R2, Rp, {x, z, randomval});
  --     f10 = ev f1p;
  --     g10 = ev g1p;
  --     gcd1 = monicGCDNaive(f10, g10);
  --     (sub(gcd1, Sp), t-randomval)
  --     )
  -- ans = gcds_0
  -- for i from 1 to #gcds-1 do ans = polyCRA(ans, gcds_i, t)
  -- polyRationalReconstruction(ans_0, t, ans_1) -- this doesn't look quite right...
  -- times oo -- ??
///

-*
  restart
  needsPackage "Fields"
*-

TEST
///
-- Here is an example from vHoeij-Monagan 2004
  -- example set 
  K1 = field(QQ[t])
  A1 = K1[z]
  mz = z^3 - (5-t)*z^2 + (7-t^2)*z  - (9-t^3)
  K2 = field(A1/mz)
  R = K2[x]
  useTower R

  g = (10-4*t)*x^2 - 5*x*z^2 + (4*t+1)*x*z + (11 - 17*t^2 + 9*t)*x -
    19*z^2 + (-7*t+6)*z + (-11*t^2 + 15*t + 3)
  a = (18 + 10*t)*x^2 + 10*x*z^2 + (17*t + 2)*x*z + (2 + 17*t^2 + 8*t)*x +
    6*z^2 + (17*t+6)*z + (4*t^2-4*t+2)
  b = (-8-11*t)*x^2 -14*x*z^2 + (8*t-4)*x*z + (-17 - 5*t^2 + 19*t)*x -
    11*z^2 + (17*t-4)*z + (-14*t^2 - 19*t - 2)

  assert(monicGCDModular(g*a, g*b) ===  primitiveAssociate monicGCDNaive(g*a, g*b))
  assert(monicGCDModular(g*a, g*b) ===  primitiveAssociate g)
  assert(monicGCDModular(g*a^2, g*b^2) ===  primitiveAssociate g)
  assert(monicGCDModular(g^2*a^2, g^2*b^2) ===  primitiveAssociate g^2)
  assert(monicGCDModular(g^2*a^3, g^2*b^3) ===  primitiveAssociate g^2)
  assert(monicGCDModular(g^2*a^4, g^2*b^4) ===  primitiveAssociate g^2)
  assert(monicGCDModular(g^2*a^5, g^2*b^5) ===  primitiveAssociate g^2)
  assert(monicGCDModular(g^2*a^6, g^2*b^6) ===  primitiveAssociate g^2)
  assert(monicGCDModular(g^2*a^7, g^2*b^7) ===  primitiveAssociate g^2)
  assert(monicGCDModular(g^2*a^8, g^2*b^8) ===  primitiveAssociate g^2)
  assert(monicGCDModular(g^2*a^9, g^2*b^9) ===  primitiveAssociate g^2)
  assert(monicGCDModular(g^2*a^10, g^2*b^10) ===  primitiveAssociate g^2)
  --elapsedTime assert(monicGCDModular(g^3*a^10, g^3*b^10) ===  primitiveAssociate g^3) -- 3.7 sec
  --elapsedTime assert(monicGCDModular(g^4*a^10, g^4*b^10) ===  primitiveAssociate g^4) -- 19 sec
  --elapsedTime assert(monicGCDModular(g^4*a^10, g^3*b^10) ===  primitiveAssociate g^3) -- 4.7 sec
  --elapsedTime assert(monicGCDModular(g^5*a^8, g^5*b^8) ===  primitiveAssociate g^5) -- 70 sec
  --elapsedTime assert(monicGCDModular(g^5*a^6, g^5*b^6) ===  primitiveAssociate g^5) -- 24.8 sec
  --elapsedTime assert(monicGCDModular(g^5*a^5, g^5*b^5) ===  primitiveAssociate g^5) -- 12.8 sec
///

///
restart
needsPackage "Fields"
  A = ZZ/32003[g_3, r, MonomialOrder=>Lex]
  K = field(A/ideal(r^2-3, g_3^4+14661*g_3^2-57))
  inv = 1 // (g_3)
  inv * g_3 == 1
  isUnit g_3
  
  fieldInfo K
  B = K[g_2]
  F = g_2^8+8*g_2^7*g_3+8*g_2^7*r+28*g_2^6*g_3^2+56*g_2^6*g_3*r+
      28*g_2^6*r^2-10736*g_2^6+56*g_2^5*g_3^3+168*g_2^5*g_3^2*r+
      168*g_2^5*g_3*r^2-410*g_2^5*g_3+56*g_2^5*r^3-410*g_2^5*r+
      169*g_2^5+70*g_2^4*g_3^4+280*g_2^4*g_3^3*r+
      420*g_2^4*g_3^2*r^2-1025*g_2^4*g_3^2+280*g_2^4*g_3*r^3-2050*g_2^4*g_3*r+
      845*g_2^4*g_3+70*g_2^4*r^4-1025*g_2^4*r^2+845*g_2^4*r-
      15883*g_2^4+56*g_2^3*g_3^5+280*g_2^3*g_3^4*r+560*g_2^3*g_3^3*r^2+9301*g_2^3*g_3^3+
      560*g_2^3*g_3^2*r^3-4100*g_2^3*g_3^2*r+1690*g_2^3*g_3^2+280*g_2^3*g_3*r^4-
      4100*g_2^3*g_3*r^2+3380*g_2^3*g_3*r+474*g_2^3*g_3+56*g_2^3*r^5+
      9301*g_2^3*r^3+1690*g_2^3*r^2+474*g_2^3*r-11129*g_2^3+
      28*g_2^2*g_3^6+168*g_2^2*g_3^5*r+420*g_2^2*g_3^4*r^2-1025*g_2^2*g_3^4+
      560*g_2^2*g_3^3*r^3-4100*g_2^2*g_3^3*r+1690*g_2^2*g_3^3+420*g_2^2*g_3^2*r^4-
      6150*g_2^2*g_3^2*r^2+5070*g_2^2*g_3^2*r+711*g_2^2*g_3^2+168*g_2^2*g_3*r^5-
      4100*g_2^2*g_3*r^3+5070*g_2^2*g_3*r^2+1422*g_2^2*g_3*r-1384*g_2^2*g_3+28*g_2^2*r^6-
      1025*g_2^2*r^4+1690*g_2^2*r^3+711*g_2^2*r^2-1384*g_2^2*r+
      1268*g_2^2+8*g_2*g_3^7+56*g_2*g_3^6*r+168*g_2*g_3^5*r^2-
      410*g_2*g_3^5+280*g_2*g_3^4*r^3-2050*g_2*g_3^4*r+845*g_2*g_3^4+280*g_2*g_3^3*r^4-
      4100*g_2*g_3^3*r^2+3380*g_2*g_3^3*r+474*g_2*g_3^3+168*g_2*g_3^2*r^5-
      4100*g_2*g_3^2*r^3+5070*g_2*g_3^2*r^2+1422*g_2*g_3^2*r-
      1384*g_2*g_3^2+56*g_2*g_3*r^6-2050*g_2*g_3*r^4+3380*g_2*g_3*r^3+1422*g_2*g_3*r^2-
      2768*g_2*g_3*r+2536*g_2*g_3+8*g_2*r^7-410*g_2*r^5+845*g_2*r^4+474*g_2*r^3-
      1384*g_2*r^2+2536*g_2*r-3350*g_2+g_3^8+8*g_3^7*r+28*g_3^6*r^2-
      10736*g_3^6+56*g_3^5*r^3-410*g_3^5*r+169*g_3^5+70*g_3^4*r^4-1025*g_3^4*r^2+845*g_3^4*r-
      15883*g_3^4+56*g_3^3*r^5+9301*g_3^3*r^3+1690*g_3^3*r^2+474*g_3^3*r-11129*g_3^3+28*g_3^2*r^6-
      1025*g_3^2*r^4+1690*g_3^2*r^3+711*g_3^2*r^2-1384*g_3^2*r+1268*g_3^2+8*g_3*r^7-
      410*g_3*r^5+845*g_3*r^4+474*g_3*r^3-1384*g_3*r^2+2536*g_3*r-3350*g_3+r^8-
      10736*r^6+169*r^5-15883*r^4-11129*r^3+1268*r^2-3350*r+8128
  G = g_2^2-3*g_3^2
  monicGCDNaive(F,G)
  exts = {r^2-3, g_3^4+14661*g_3^2-57}
  R = A/ideal exts
  L  = ideal(F,G) + ideal(exts)
  gens gb L
  T = makeTower(A, {r^2-3, g_3^4+14661*g_3^2-57})
  debug Core
  F = rawTowerTranslatePoly(T, raw F)
  G = rawTowerTranslatePoly(T, raw G)
  rawGCD(F,G) -- should should be g_2 + r*g_3, or g_2 - r*g_3.  -- RIGHT NOW, this FAILS...

  F
  describe ring F
  describe coefficientRing ring F
///

-*
  restart
  needsPackage "Fields"
*-
"TEST"
///
  kk = ZZ/5
  F = field(kk[t])
  R = F[a]
  f = a^5 - t
  factor f
  F2 = field(R/f)
  extensionBasis F2
  multiplicationMap a
  minimalPolynomial(oo, F[T])
  minimalPolynomial(a, F[T])
  R = F2[x]
  distinctDegreeFactors (x^5-a) -- fails
///

-*
  restart
  needsPackage "Fields"
*-
TEST /// -- of extensionBasis, extensionDegree, coeffsInBasis
  debug needsPackage "Fields"
  (K1,K2,K3,K4,K5,K6,K7,K8) = allFieldCases 32003;

  extensionBasis K1
  extensionBasis K2
  extensionBasis K3
  extensionBasis K4
  extensionBasis K5
  extensionBasis K6
  extensionBasis K7
  extensionBasis K8

  assert(extensionDegree K1 == 1)
  assert(extensionDegree K2 == 6)
  assert(extensionDegree K3 == 1)
  assert(extensionDegree K4 == 6)
  assert(extensionDegree K5 == 1)
  assert(extensionDegree K6 == 6)
  assert(extensionDegree K7 == 1)
  assert(extensionDegree K8 == 6)

  -- TODO: we need a name for the fraction field base....!
  minimalPolynomial(K2_0 + K2_1, (baseField K2)[T])
  minimalPolynomial(K4_0 + K4_1, K3[T])
  minimalPolynomial(K6_0 + K6_1, K5[T])
  minimalPolynomial(K8_0 + K8_1, K7[T])
///

-*
  restart
  needsPackage "Fields"
*-
/// -- of extensionBasis, extensionDegree, coeffsInBasis
  -- factor over the 8 different types of fields. (univariate for now), F[x]
  -- F = QQ -- can mostly use current factor code
  -- F = QQ[zs]/Iz -- if there is only one variable, can mostly use current factor code
  -- F = QQ(ts) -- can mostly use current factor code, sort of.
  -- F = QQ(ts)[zs]/Iz -- move to primitive extension, factor there, gcds, bring back

  -- F = kk = ZZ/p or GF(q) -- can mostly use current factor code
  -- F = kk[zs]/Iz -- if there is only one variable, can mostly use current factor code
  -- F = kk(ts) -- can mostly use current factor code, sort of.
  -- F = kk(ts)[zs]/Iz -- move to primitive extension, factor there, gcds, bring back

  debug needsPackage "Fields"
  (K1,K2,K3,K4,K5,K6,K7,K8) = allFieldCases 32003;

  methods factorData
  methods factors
  methods positiveDegreeFactors
  methods prettyFactor
  methods distinctDegreeFactors -- needs GCD, separability, otherwise is good

  R = K1[x]
  f = (x^3-x-1)^2*(2*x-3)*(2*x^7+x^3+1)
  facDat = factorData f -- ok
  assert(f == facDat.Coefficient * product apply(facDat.Factors, p -> (p#1)^(p#0)))
  assert(sort (facDat.Factors / first) === {1,1,2})
  assert(ring facDat.Coefficient === coefficientRing R)
  assert(all(facDat.Factors / last, g -> ring g === R))
  
  R = K2[x]
  describe K2
  useTower R
  f = (x^3-x-z1)^2*(z2*x-3)*(2*x^7+x^3+z1*z2)
  facDat = factorData f -- ok
  assert(f == facDat.Coefficient * product apply(facDat.Factors, p -> (p#1)^(p#0)))
  assert(sort (facDat.Factors / first) === {1,1,2})
  assert(ring facDat.Coefficient === coefficientRing R)
  assert(all(facDat.Factors / last, g -> ring g === R))
  prettyFactor f

  R = K3[x]
  describe K3
  useTower R
  f = (x^3-x-t1)^2*(t2*x-3)*(2*x^7+x^3+t1*t2)
  facDat = factorData f -- ok
  assert(f == facDat.Coefficient * product apply(facDat.Factors, p -> (p#1)^(p#0)))
  assert(sort (facDat.Factors / first) === {1,1,2})
  assert(ring facDat.Coefficient === coefficientRing R)
  assert(all(facDat.Factors / last, g -> ring g === R))
  prettyFactor f

  R = K4[x]
  describe K4
  useTower R
  f = (x^3-x-z1)^2*(z2*x-3*z1)*(2*x^7+x^3+z2*t2)
  elapsedTime facDat = factorData f -- doesn't appear to finish...
  assert(f == facDat.Coefficient * product apply(facDat.Factors, p -> (p#1)^(p#0)))
  assert(sort (facDat.Factors / first) === {1,1,2})
  assert(ring facDat.Coefficient === coefficientRing R)
  assert(all(facDat.Factors / last, g -> ring g === R))
  prettyFactor f

  R = K5[x]
  useTower R
  f = (x^3-x-1)^2*(2*x-3)*(2*x^7+x^3+1) -- 2x^7 + x^3 + 1 has a linear factor
  facDat = factorData f -- ok
  assert(f == facDat.Coefficient * product apply(facDat.Factors, p -> (p#1)^(p#0)))
  assert(sort (facDat.Factors / first) === {1,1,1,2,2})
  assert(ring facDat.Coefficient === coefficientRing R)
  assert(all(facDat.Factors / last, g -> ring g === R))
  prettyFactor f
  
  R = K6[x]
  describe K5
  useTower R
  f = (x^3-x-z1)^2*(z2*x-3)*(2*x^7+x^3+z1*z2)
  facDat = factorData f -- ok
  assert(f == facDat.Coefficient * product apply(facDat.Factors, p -> (p#1)^(p#0)))
  assert(sort (facDat.Factors / first) === {1,1,2})
  assert(ring facDat.Coefficient === coefficientRing R)
  assert(all(facDat.Factors / last, g -> ring g === R))
  prettyFactor f

  R = K7[x]
  describe K7
  useTower R
  f = (x^3-x-t1)^2*(t2*x-3)*(2*x^7+x^3+t1*t2)
  facDat = factorData f -- ok
  assert(f == facDat.Coefficient * product apply(facDat.Factors, p -> (p#1)^(p#0)))
  assert(sort (facDat.Factors / first) === {1,1,2})
  assert(ring facDat.Coefficient === coefficientRing R)
  assert(all(facDat.Factors / last, g -> ring g === R))
  prettyFactor f

  R = K8[x]
  describe K4
  useTower R
  f = (x^3-x-z1)^2*(z2*x-3*z1)*(2*x^7+x^3+z2*t2)
  f = primitiveAssociate makeMonic f
  elapsedTime facDat = factorData f -- doesn't appear to finish... -- 80 sec
  assert(f == facDat.Coefficient * product apply(facDat.Factors, p -> (p#1)^(p#0)))
  assert(sort (facDat.Factors / first) === {1,1,2})
  assert(ring facDat.Coefficient === coefficientRing R)
  assert(all(facDat.Factors / last, g -> ring g === R))
  prettyFactor f
 
///

///
-- example of extension of fields, want the basis, multiplication map, etc.
restart
  K = GF(4,Variable => a)    -- (2,2)
  L = GF(64, Variable => b)  -- (2,6)

  phi = map(L,K,{b^3+b^2+b+1})
  isWellDefined phi
  pushForward(phi, L^1) -- fails.  Maybe for stupid reasons?

  needsPackage "PushForward"
  pushFwd(phi, L^1) -- fails too
  
  ambK = ambient K
  ambL = ambient L
 
  phi = map(ambient L,ambient K,{b^3+b^2+b+1})
  isWellDefined phi
  pushForward(phi, ambL^1)  -- fails
  needsPackage "PushForward"
  pushFwd(phi, ambL^1)  -- works
  pushFwd(matrix{{b}})

  R = K[x]
  factor (x^3 + x + 1)
  quotR = R/(x^3 + x + 1)
  L' = GF quotR  -- fails

  describe quotR
  describe first flattenRing quotR

  
  F1 = ZZ/2[a]/(a^2+a+1)
  F2 = F1[b]/(b^6+b^4+b^3+b+1)
  -- F2 has two components, we need to take one, or:
  F2 = F1[b]/(b^6+b^4+b^3+b+1, a-(b^3+b^2+b+1))
  minimalPresentation first flattenRing F2 -- this is not good...  
///

-*
  restart
  needsPackage "Fields"
*-
TEST ///
kk = field ZZ
assert(kk === QQ)
assert(source ZZ.cache.FieldInclusion === ZZ)
assert(target ZZ.cache.FieldInclusion === QQ)
assert(source QQ.cache.FieldInclusion === ZZ)
assert(target QQ.cache.FieldInclusion === QQ)
assert(QQ.cache.?FieldInfo)

kk = field QQ
assert(kk === QQ)
assert(source ZZ.cache.FieldInclusion === ZZ)
assert(target ZZ.cache.FieldInclusion === QQ)
assert(source QQ.cache.FieldInclusion === ZZ)
assert(target QQ.cache.FieldInclusion === QQ)

R = ZZ/101
kk = field R
assert(kk === R)
assert(kk.cache.?FieldInfo)
assert(source kk.cache.FieldInclusion === kk)
assert(target kk.cache.FieldInclusion === kk)

R = GF 9
kk = field R
assert(kk === R)
assert(kk.cache.?FieldInfo)
assert(source kk.cache.FieldInclusion === kk)
assert(target kk.cache.FieldInclusion === kk)

R = QQ[x][y]
kk = field R
ll = field R
assert(kk === ll)
assert(source kk.cache.FieldInclusion === R)
assert(target kk.cache.FieldInclusion === kk)
assert(source R.cache.FieldInclusion === R)
assert(target R.cache.FieldInclusion === kk)
assert(source kk.cache.LiftBack === kk)
assert(target kk.cache.LiftBack === R)

R = ZZ[x][y]
I = ideal (3_R)
S = R/I
kk = field S
ll = field S
assert(kk === ll)
assert(source S.cache.FieldInclusion === S)
assert(target S.cache.FieldInclusion === kk)
assert(source kk.cache.FieldInclusion === S)
assert(target kk.cache.FieldInclusion === kk)
assert(source kk.cache.LiftBack === kk)
assert(target kk.cache.LiftBack === S)

R = QQ[a..d]
I = monomialCurveIdeal(R, {1,3,4})
S = R/I
kk = field S
assert(source S.cache.FieldInclusion === S)
assert(target S.cache.FieldInclusion === kk)
assert(source kk.cache.FieldInclusion === S)
assert(target kk.cache.FieldInclusion === kk)
assert(source kk.cache.LiftBack === kk)
assert(target kk.cache.LiftBack === S)

R = ZZ[a..d]
I = ideal(b*c-a*d,c^3-b*d^2,a*c^2-b^2*d,b^3-a^2*c)
S = R/I
kk = field S
assert(source S.cache.FieldInclusion === S)
assert(target S.cache.FieldInclusion === kk)
assert(source kk.cache.FieldInclusion === S)
assert(target kk.cache.FieldInclusion === kk)
assert(source kk.cache.LiftBack === kk)
assert(target kk.cache.LiftBack === S)
///

-*
restart
needsPackage "Fields"
*-

TEST ///
-- factoring two variable case
A = QQ[a..d]
B = A/monomialCurveIdeal(A, {1,2,3})
L = field B
useTower L
R = L[x,y]
f = b*((y+1)*x + a*y)*(x*y + c*y + b)*(x+y+a)*(y+a)*(x+c)
elapsedTime facData = factorData f
assert(facData.Coefficient * product apply(facData.Factors, p -> (p#1)^(p#0)) == f)

-- factoring three variable case
A = QQ[a..d]
B = A/monomialCurveIdeal(A, {1,2,3})
L = field B
useTower L
R = L[x,y,z]
f = b*((y+1)*x + y + c*z)*(x*y + a*y + d*z)*(x+y+a)*(x+z+b)*(y+a)*(z+b)*(x+c);
elapsedTime facData = factorData f
assert(facData.Coefficient * product apply(facData.Factors, p -> (p#1)^(p#0)) == f)
///

-*
restart
debug needsPackage "Fields"
*-

TEST ///
debug needsPackage "Fields"  -- for randomNonzero
-- this seems to either: not finish, or not be correct when it does finish
L = field (QQ[z]/(z^2 + (randomNonzero QQ)^2))
R = L[x,y]
f = x^2 + y^2
facData = multivarFactorData f   
assert(product apply(facData.Factors, p -> (p#1)^(p#0)) == f)

-- this seems to work
L = field (QQ[z]/(z^2 + (randomNonzero ZZ)^2))
R = L[x,y]
f = x^2 + y^2
facData = multivarFactorData f
assert(product apply(facData.Factors, p -> (p#1)^(p#0)) == f)
///

-- this is a cool example for absolute factorization
///
debug needsPackage "RationalPoints2"
L = field (QQ[a,b]/ideal (a^2 - 2,b^2 - 3))
R = L[x,y,z]
-- product of Galois conjugates of x + ay + bz
f = (x + a*y + b*z)*(x - a*y - b*z)*(x + a*y - b*z)*(x - a*y + b*z)
factorData f
S = QQ[x,y,z]
g = sub(f,S)
factorData g
h = sub(g, {y => random QQ, z => random QQ})
K0 = QQ[a]
phi = map(K0,S,{a,0,0})
assert(isIrreducible phi h)
K = field(K0/(polredbest phi h))
T = K[x,y,z]
g = sub(g,T)
elapsedTime factorData g
///

-- how long could computing ideal jacobian h for a factor h take?
-- minimalPrimes ideal jacobian g

ISSUE ///
  -- test from bugs/mike/1-moty-frac.m2 (from 2008!)
  -- pp = 5
  -- K=frac(ZZ/pp[u,v]);
  -- R=K[x,y,z_0..z_(2*pp-1)];
  -- y/(u^2+v^2)

  pp = 5
  K=field(ZZ/pp[u,v]);
  R=K[x,y,z_0..z_(2*pp-1)];
  1/(u^2+v^2) * y      -- ok
  (u^2 + v^2)^(-1) * y -- ok
  y * (u^2 + v^2)^(-1) -- ok
  y/(u^2+v^2) -- this still fails: how best to handle it?
              -- need to change (frac,EngineRing) and (RingElement / RingElement)
              -- so that the denominator is promoted but the code knows its invertible.
///

-*
  restart
  needsPackage "Fields"
*-
TEST /// -- fieldGens, inducedMapOnFields
  assert({} == fieldGens QQ)
  assert({} == fieldGens (ZZ/5))
  kk = GF 25
  assert({kk_0} == fieldGens kk)

  A = ZZ[a..d]
  B = field A
  assert(fieldGens B == {a,b,c,d})
  assert(all ((fieldGens B)/ring, x -> x === B))

  C = B[s,t]/(t^3-b, s^2-a)
  D = field C
  fieldGens D == {s, t, a, b, c, d}
  assert((fieldGens D)/ring//unique === {D})
///

-*
  restart
  needsPackage "Fields"
*-
ISSUE ///  
  -- example of a map of fields:
  A = QQ[a..b]
  KA = field A
  useTower A
  C = A[c]/(c^2-b)
  phi = map(C, A)
  phi' = inducedMapOnFields phi -- not working...
  describe C

  -- a second example
  A = QQ[a..d]
  I = monomialCurveIdeal(A, {1,3,4})
  B = A/I
  KB = field B
  G = id_B
  inducedMapOnFields G -- how to get this to work!?  
///

-*
  restart
  needsPackage "Fields"
  -- example taken from IntegralClosure.m2, Wolmer Vasconcelos test
  -- the issue seems to be that our normal form has a complicated representation
  -- of c, which satisfies a polynomial of degree 8 over the independent variables
  -- and so f2 looks much worse than its description below.
*-
ISSUE ///
  S = ZZ/101[symbol a..symbol e]
  I = ideal(a^2*b*c^2+b^2*c*d^2+a^2*d^2*e+a*b^2*e^2+c^2*d*e^2,
      a*b^3*c+b*c^3*d+a^3*b*e+c*d^3*e+a*d*e^3,
      a^5+b^5+c^5+d^5-5*a*b*c*d*e+e^5,
      a^3*b^2*c*d-b*c^2*d^4+a*b^2*c^3*e-b^5*d*e-d^6*e+3*a*b*c*d^2*e^2-a^2*b*e^4-d*e^6,
      a*b*c^5-b^4*c^2*d-2*a^2*b^2*c*d*e+a*c^3*d^2*e-a^4*d*e^2+b*c*d^2*e^3+a*b*e^5,
      a*b^2*c^4-b^5*c*d-a^2*b^3*d*e+2*a*b*c^2*d^2*e+a*d^4*e^2-a^2*b*c*e^3-c*d*e^5,
      b^6*c+b*c^6+a^2*b^4*e-3*a*b^2*c^2*d*e+c^4*d^2*e-a^3*c*d*e^2-a*b*d^3*e^2+b*c*e^5,
      a^4*b^2*c-a*b*c^2*d^3-a*b^5*e-b^3*c^2*d*e-a*d^5*e+2*a^2*b*c*d*e^2+c*d^2*e^4)
  -- isPrime I
  R = S/I
  F = field R
  --fracF = frac R
  useTower F
  --use fracF
  f1 = (a*d^4*e-c*d*e^4)/b
  f2 = (-a^2*b^3*e+a*d^3*e^2)/c
  g = leadCoefficient (f1 * mydenominator f1)
  G = (fieldInfo F).Independents
  T = G[x]

  --minimalPolynomial(f1, (fieldInfo F).Independents[x]) -- hmmm
  -- we would like such small fractions...  Is that possible
///

-*
  restart
  needsPackage "Fields"
*-
ISSUE ///
kk = field(QQ[x])    -- NF is frac(ZZ[x]), not frac(QQ[x]).
B = matrix {{(1/2)}}
A = matrix {{x_kk}}
A * B                -- fails; promote doesn't realize QQ is promotable to frac(ZZ[x])
x_kk * (1/2)         -- ok
///
