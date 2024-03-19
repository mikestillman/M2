newPackage(
        "HilbertSchemes",
        Version => "0.1", 
        Date => "",
        Authors => {{Name => "Ayah Almousa", 
                Email => "almou007@umn.edu", 
                HomePage => "http://sites.google.com/view/ayah-almousa"},
            {Name => "Mike Stillman", 
                Email => "mike@math.cornell.edu", 
                HomePage => "http://pi.math.cornell.edu/~mike"}
        },
        Headline => "functions for investigating Hilbert schemes",
        PackageExports => {
            "GenericInitialIdeal",
            "LexIdeals", 
            "StronglyStableIdeals", 
            "VersalDeformations"
            },
        DebuggingMode => true
        )

export {
    "HP",
    "HF",
    "mVector",
    "gotzmannHP",
    "macaulayHP",
    "MtoA",
    "AtoM",
    "dimHilbTangentSpace",
    "randomPtOnLex",
    "canonicalDistraction",
    "randomCanonicalDistraction",
    "makeRandomCanonicalDistractionHyperplanes",
    "fanComponents"
    }

-- Utility routines --
  findIndices = method()
  findIndices(List, List) := (L, Bs) -> for ell in L list position(Bs, b -> b == ell)

  randomPoint = method()
  randomPoint Ring := S -> trim minors(2, (vars S) || random(S^1, S^(numgens S)))

  randomPoints = method()
  randomPoints(ZZ, Ring) := (npts, S) -> intersect for i from 1 to npts list randomPoint S

  randomMap = method()
  randomMap(Ring,Ring) := (S, S') -> (
      A := coefficientRing S';
      cfs := (for i from 1 to numgens S' list random(1, S));
      cfs2 :=(for i from 1 to numgens A list random(0, S));
      map(S, S', cfs|cfs2)
      )

-------------------------------
-- Part 1. Hilbert polynomials, mvectors (as Partition)
-- Gotzmann is just the conjugate of the partition.
-------------------------------
-- a local function for mVector
mpart = (t, deg, m) -> binomial(t + deg, deg+1) - binomial(t + deg - m, deg+1)

-- the macaulay partition (m0, m1, ..., md) for  Hilbert polynomial of degree d.
mVector = method()
mVector Ideal := (I) -> mVector hilbertPolynomial(I, Projective=>false)
mVector RingElement := Partition => (hp) -> (
    t := (ring hp)_0;
    d := first degree hp;
    c := lift(d! * leadCoefficient hp, ZZ);
    if d == 0 then {c}
    else new Partition from append(mVector (hp - mpart(t, d, c)), c)
    )

MtoA = method()
MtoA Partition := 
MtoA List := (M) -> append(for i from 0 to #M-2 list M#i - M#(i+1), M#(#M-1))

AtoM = method()
AtoM List := Partition => (a) -> new Partition from accumulate(a, 0, (x,y) -> x+y)

macaulayHP = method()
macaulayHP(List, RingElement) :=
macaulayHP(Partition, RingElement) := (M, z) -> (
    sum for i from 0 to #M-1 list (binomial(z + i, i+1) - binomial(z + i - M_i, i+1))
    )

gotzmannHP = method()
gotzmannHP(List, RingElement) := 
gotzmannHP(Partition, RingElement) := (p, z) -> sum for i from 0 to #p-1 list binomial(z + p#i - i - 1, p#i - 1)

HP = method()
HP Ideal := (I) -> hilbertPolynomial(I, Projective => false)
HP Module := (M) -> hilbertPolynomial(M, Projective => false)
HP(Ideal, RingElement) := (I, z) -> sub(HP I, matrix{{z}})
HP(Module, RingElement) := (M, z) -> sub(HP M, matrix{{z}})
HP(Partition, RingElement) := (mvec, z) -> macaulayHP(mvec, z)

-- HF: currently only for single gradings...
HF = method() 
HF(Module, ZZ, ZZ) :=
HF(Ring, ZZ, ZZ) :=
HF(Ideal, ZZ, ZZ) := (I, lo, hi) -> for i from lo to hi list hilbertFunction(i, I)
HF(Ideal, ZZ) := (I, hi) -> HF(I, 0, hi)

TEST ///
-*
  restart
  needsPackage "HilbertSchemes"
*-
  A = QQ[t]
  p = new Partition from {4,3}
  h1 = gotzmannHP(conjugate p, t)
  h2 = macaulayHP(p, t)
  assert(h1 == h2)
  assert(AtoM MtoA p === p)

  h1 = gotzmannHP(p, t)
  h2 = macaulayHP(conjugate p, t)
  assert(h1 == h2)
  q = conjugate p
  assert(AtoM MtoA q === q)

  p = new Partition from {23,7,3}
  h1 = gotzmannHP(conjugate p, t)
  h2 = macaulayHP(p, t)
  assert(h1 == h2)
  assert(AtoM MtoA p === p)
  assert(AtoM MtoA conjugate p === conjugate p)

  h1 = gotzmannHP(p, t)
  h2 = macaulayHP(conjugate p, t)
  assert(h1 == h2)
  
  S = ZZ/101[a..d]
  I = monomialCurveIdeal(S, {1,2,3})
  HP I
  HP(I, t)
  HF(I, 10)
  HF(I, 3, 6)
///

-----------------------------
-- Part 2. Saturated Lex ideals associated to an m vector.
-----------------------------

Lideal = method()
Lideal(Ring, List) := (S, L) -> (
    -- L is the list (a0, a1, a2, ..., a(d-1)).
    n := numgens S - 1;
    if #L == 1 then ideal(S_(n-1)^(L#0))
    else S_(n-#L)^(L#(#L-1)) * (ideal(S_(n-#L)) + Lideal(S, drop(L,-1)))
    )

lexIdeal(Partition, Ring) := opts -> (M, S) -> (
    a := MtoA M;
    n := numgens S - 1;
    d := #M - 1;
    L1 := ideal for i from 0 to n-d-2 list S_i;
    L2 := Lideal(S, a);
    trim(L1 + L2)
    )

TEST ///
-*
  restart
  needsPackage "HilbertSchemes"
*-
  S = ZZ/101[a..d]
  A = QQ[t]
  L1 = lexIdeal(new Partition from {4,3}, S)
  L2 = lexIdeal(3*t+1, S)
  L1 == L2

  p = new Partition from {17, 5}
  L1 = lexIdeal(p, S)
  L2 = lexIdeal(macaulayHP(p, t), S)
  assert(L1 == L2)

  S = ZZ/101[a..g]
  p = new Partition from {17, 5, 4, 2}
  L1 = lexIdeal(p, S)
  L2 = lexIdeal(macaulayHP(p, t), S)
  assert(L1 == L2)
///

------------------------------
-- Part 3. Normal bundles and dim tangent space.
------------------------------
dimHilbTangentSpace = method()
dimHilbTangentSpace Ideal := (I) -> rank HH^0(sheaf Hom(I, comodule I))

TEST ///
-*
  restart
  needsPackage "HilbertSchemes"
*-
  S = ZZ/101[a..d]
  A = QQ[t]
  hp = macaulayHP(new Partition from {4,3}, t)
  Bs = stronglyStableIdeals(hp, S)
  assert(set(Bs/dimHilbTangentSpace) === set{12, 15, 16})
///    

------------------------------
-- Part 4. Lex component
------------------------------

randomPtOnLex = method()
randomPtOnLex(Partition, Ring) := (M, S) -> (
    a := MtoA M;
    linears := for ell from 1 to numgens S - 1 list random(1, S);
    -- random a#0 points
    I0 := intersect for i from 1 to a#0 list minors(2, (vars S) || random(S^1, S^(numgens S)));
    Ids := for d from 1 to #a-1 list (
        trim (ideal(random(a#d, S)) + ideal for i from 1 to (numgens S) - 2 - d list linears_(i-1))
        );
    -- random degree a#1 curve in a P^2
    -- random degree a#2 hypersurface in a P^3 (containing the P^2? yes, but what happens if not?)
    intersect(I0, intersect Ids)
    )

TEST ///
-*
  restart
  needsPackage "HilbertSchemes"
*-
  S = ZZ/101[a..d]
  A = QQ[t]
  p = new Partition from {4,3}
  hp = HP(lexIdeal(p, S), t)
  hp = macaulayHP(new Partition from {4,3}, t)
  J = randomPtOnLex(p, S)
  assert(HP(J, t) == hp)
  assert(J == intersect decompose J)
  assert(# decompose J == 2)

  S = ZZ/101[a..f]
  Slex = ZZ/101[gens S, MonomialOrder => Lex]
  use S
  mv = new Partition from {7, 5, 3}
  L = lexIdeal(mv, S)
  L1 = randomPtOnLex(mv, S)
  HP(L, t) == HP(L1, t)
  decompose L1
  
  dimHilbTangentSpace L
  -- dimHilbTangentSpace L1 -- ouch, this takes a while! But we don't really need it...
///    

------------------------------
-- Part 5. Polarization and fan of a Borel ideal.
------------------------------
-- create a (random) fan, with specified number in each dimension
-- fan({n0, n1, n2, ...nd}, S)
hartshorneFan = method()
hartshorneFan(List, Ring) := (degs, S) -> (
    -- assumption: S is a polynomial ring in n vars, where n > #degs
    kk := coefficientRing S;
    n := numgens S - 1;
    intersect flatten for i from 0 to #degs-1 list (
        for j from 1 to degs#i list (
            ideal for k from 0 to n - i - 1 list (S_k - (random kk) * S_n)
            )
        )
    )

-- fan components of a monomial ideal
fanComponents = method()
fanComponents MonomialIdeal := (I) -> (
    PI := polarize I;
    C := decompose PI;
    for c in C list for c1 in flatten entries gens c list (baseName c1)#1
    )

makeRandomCanonicalDistractionHyperplanes = method()
makeRandomCanonicalDistractionHyperplanes(List, Ring) := HashTable => (fanComps, S) -> (
    kk := coefficientRing S;
    p := sort unique flatten fanComps; -- list of {i,j}
    hashTable for p1 in p list p1 => S_(p1#0) - (random kk) * S_(numgens S - 1)
    )

randomCanonicalDistraction = method()
randomCanonicalDistraction MonomialIdeal := (I) -> (
    fc := fanComponents I;
    H := makeRandomCanonicalDistractionHyperplanes(fc, ring I);
    intersect for c in fc list ideal for p in c list H#p
    )
randomCanonicalDistraction(MonomialIdeal, HashTable) := (I, H) -> (
    fc := fanComponents I;
    intersect for c in fc list ideal for p in c list H#p
    )

canonicalDistraction = method()
canonicalDistraction(MonomialIdeal, Thing) := (I, t) -> (
    -- assumption: I does not have any generators involving x_n (last var in S = ring I)
    fc := fanComponents I;
    ij := sort unique flatten fc;
    S := ring I;
    n := numgens S - 1;
    A := (coefficientRing S)[for a in ij list t_(toSequence a)];
    S' := A (monoid [gens S, Join => false, Degrees => {n:2, 1}]);
    H := hashTable for a from 0 to #ij-1 list ij#a => A_a;
    I' := ideal for m in I_* list (
        e := first exponents m;
        product flatten for i from 0 to n-1 list for j from 0 to e#i-1 list S'_i - H#{i,j} * S'_n
        );
    I'
    )

TEST ///
-*
  restart
  debug needsPackage "HilbertSchemes"
*-

  S = ZZ/101[a..e]
  I = monomialIdeal"a2,ab3,bc4,cd5"
  fanComponents I
  canonicalDistraction(I, symbol t)
  C = irreducibleDecomposition I
  
  H = makeRandomCanonicalDistractionHyperplanes(fanComponents I, S)
  J = randomCanonicalDistraction I
  monomialIdeal leadTerm J == I
  phi = map(S, S, random(S^1, S^{5:-1}))
  gJ = phi J
  intersect apply(decompose J, i -> phi i)
  Slex = ZZ/101[a..e, MonomialOrder => Lex]
  gJlex = sub(gJ, Slex)
  groebnerBasis(gJlex, Strategy=>"F4");
--  gens gb gJlex --very slow


  S = ZZ/101[a..d]
  I0 = monomialIdeal"a,b4,b3c"
  I1 = monomialIdeal"a2,ab,ac,b3"
  I2 = monomialIdeal"a2,ab,b2"
  
  netList fanComponents I0
  netList fanComponents I1
  netList fanComponents I2
  H = makeRandomCanonicalDistractionHyperplanes(join(fanComponents I0, fanComponents I1, fanComponents I2), S)
  fan0 = randomCanonicalDistraction(I0, H)
  fan1 = randomCanonicalDistraction(I1, H)
  fan2 = randomCanonicalDistraction(I2, H)

  netList ((decompose fan0)/trim)
  netList ((decompose fan1)/trim)
  netList ((decompose fan2)/trim)

  Slex = ZZ/101[a..d, MonomialOrder => Lex]
  phi = map(Slex, S, random(Slex^1, Slex^{(numgens Slex:-1)}))
  gfan0 = phi fan0
  gfan1 = phi fan1
  gfan2 = phi fan2

  leadTerm gfan0
  saturate ideal leadTerm gfan1
  saturate ideal leadTerm gfan2

  dimHilbTangentSpace I0  
  dimHilbTangentSpace I1
  dimHilbTangentSpace I2

  dimHilbTangentSpace fan0
  dimHilbTangentSpace fan1
  dimHilbTangentSpace fan2
  
///

TEST ///
  -- partition of the Borels via double saturation
-*
  restart
  debug needsPackage "HilbertSchemes"
*-
  display = method()
  display Ideal := (fan) -> fan//decompose/trim/(i -> flatten entries gens i)/sort//sort//netList
  S = ZZ/101[a..e]
  A = QQ[t]
  Bs = stronglyStableIdeals(4*t+1, S)
  Bs = Bs/monomialIdeal
  partition(b -> monomialIdeal sub(b, d => 1), Bs)
  Ls = keys oo
  doubleL = (sort (Ls/(m -> flatten entries gens m)))/monomialIdeal
  for b in Bs list position(doubleL, ell -> ell == monomialIdeal sub(b, d=>1))
  
  -- Lets consider the fans for all the Bs.
  allfancomps = Bs/fanComponents/flatten
  H = makeRandomCanonicalDistractionHyperplanes(allfancomps, S)
  FBs = Bs/(b -> randomCanonicalDistraction(b, H))

  FLs = doubleL/(b -> randomCanonicalDistraction(b, H))
  FBs/(f -> (decompose f)/trim)
  FLs/(f -> (decompose f)/trim)

  positions(FBs, b -> isSubset(b, FLs_0))      
  positions(FBs, b -> isSubset(b, FLs_1))      
  positions(FBs, b -> isSubset(b, FLs_2))      

  I4 = monomialCurveIdeal(S, {1,2,3,4})
  HP I4
  dimHilbTangentSpace I4 -- 21.
  
  display FBs_11
  display FLs_2

  display FBs_10
  display FBs_9
  display FLs_1
///

///
  -- The rational quartic in P^3.  p(z) = 4*z+1
-*
  restart
  debug needsPackage "HilbertSchemes"
*-
  needsPackage("MonomialOrbits", FileName => "~/src/integral-closure/MonomialOrbits.m2")
  needsPackage "gfanInterface"

  kk = ZZ/32003
  S = kk[a..d]
  A = QQ[t]
  Bs = (stronglyStableIdeals(4*t+1, S))/monomialIdeal

  -- set doubleL, the list of double saturations of all Borels on this Hilbert scheme
  partition(b -> monomialIdeal sub(b, S_(numgens S-2) => 1), Bs)
  Ls = keys oo
  doubleL = (sort (Ls/(m -> flatten entries gens m)))/monomialIdeal

  -- which double saturation does each one correspond to?
  for b in Bs list position(doubleL, ell -> ell == monomialIdeal sub(b, c=>1))

  FL0 = canonicalDistraction(doubleL_0, symbol t)
  netList decompose FL0
  
  FL1 = canonicalDistraction(doubleL_1, symbol t)
  netList decompose FL1  -- 4 lines through a point (2 in one plane, 2 in another plane)

  FB7 = canonicalDistraction(Bs_7, symbol t)
  netList decompose FB7

  FB6 = canonicalDistraction(Bs_6, symbol t)
  netList decompose FB6

  psi = randomMap(S, ring FL1)
  IL1 = intersect(psi FL1, randomPoint S)
  HP IL1

  psi = randomMap(S, ring FL0)
  IL0 = intersect(psi FL0, randomPoints(3, S))
  HP IL0  

  (gfan IL1)/first/monomialIdeal/saturate/monomialIdeal;
  BL1s = select(oo, isBorel)
  findIndices(oo, Bs)

  (gfan IL0)/first/monomialIdeal/saturate/monomialIdeal;
  BL1s = select(oo, isBorel)
  findIndices(oo, Bs)

  Bs/ dimHilbTangentSpace
  HP IL0
  (gfan IL0)/first/monomialIdeal/saturate/monomialIdeal;
  BL1s = select(oo, isBorel)
  findIndices(oo, Bs)

  -- What are the Hilbert functions of all saturated Borels here?
  unique for b in Bs list for i from 0 to 10 list hilbertFunction(i, ideal b)

  hilbertRepresentatives(S, {4,9,13,17,21,25});
  hilbertRepresentatives(S, {4,8,13,17,21,25});
  hilbertRepresentatives(S, {4,8,12,17,21,25});
  hilbertRepresentatives(S, {4,7,11,16,21,25});
  hilbertRepresentatives(S, {3,6,10,15,21,25});
  hilbertRepresentatives(S, {3,6,10,15,20,25});
    

  Slex = (coefficientRing S)[gens S, MonomialIdeal => Lex]
  
  -- Thus, there are two components containng fans (of the sort we are considering.  
  --   Question: what about other fans?
  fanComponents Bs_6
  F6 = canonicalDistraction(Bs_6, symbol t)
  C = irreducibleDecomposition Bs_6
  decompose F6    

  F7 = canonicalDistraction(Bs_7, symbol t)
  netList decompose F7

  F0 = canonicalDistraction(Bs_0, symbol t)
  netList decompose F0

  F1 = canonicalDistraction(Bs_1, symbol t)
  netList decompose F1

  -- choice of general parameters, and also random change of coordinates.
  psi = map(S, ring F7, (for x in gens S list random(1,S)) | (for i from 1 to 6 list random kk))

  I7 = psi F7
  HP I7
  needsPackage "gfanInterface"
  (gfan I7)/first/monomialIdeal/saturate/monomialIdeal;
  B7s = select(oo, isBorel)
  for b in B7s list position(Bs, b1 -> b1 == b)
  Slex = (coefficientRing S)[gens S, MonomialIdeal => Lex]
  

  netList oo
  H = makeRandomCanonicalDistractionHyperplanes(fanComponents I, S)
  J = randomCanonicalDistraction I
  monomialIdeal leadTerm J == I
  phi = map(S, S, random(S^1, S^{5:-1}))
  gJ = phi J
  intersect apply(decompose J, i -> phi i)
  Slex = ZZ/101[a..e, MonomialOrder => Lex]
  gJlex = sub(gJ, Slex)
  groebnerBasis(gJlex, Strategy=>"F4");
  gens gb gJlex

  -- What are the Hilbert functions of all saturated Borels here?
  unique for b in Bs list for i from 0 to 10 list hilbertFunction(i, ideal b)
///

///
-- The Veronese Hilbert scheme 

-*
  restart
  debug needsPackage "HilbertSchemes"
*-
  display = method()
  display Ideal := (fan) -> fan//decompose/trim/(i -> flatten entries gens i)/sort//sort//netList
  S = ZZ/101[a..f]
  M = genericSymmetricMatrix(S, a, 3)
  I = minors(2, M)
  A = QQ[t]
  hp = HP(I, t) -- 2*t^2 + 3t + 1
  mVector hp -- (18, 7, 4)
  elapsedTime Bs = stronglyStableIdeals(hp, S); -- 3865...

  BsH = partition(b -> monomialIdeal sub(b, e => 1), Bs);
  Ls = keys BsH -- 12 of these
  doubleL = (sort (Ls/(m -> flatten entries gens m)))/monomialIdeal

  #BsH#(doubleL#0) -- 2575 on lex component...!
  #BsH#(doubleL#1) -- 958
  #BsH#(doubleL#2) -- 11
  #BsH#(doubleL#3) --  8
  #BsH#(doubleL#4) -- 265
  #BsH#(doubleL#5) -- 31
  #BsH#(doubleL#6) -- 4
  #BsH#(doubleL#7) -- 4
  #BsH#(doubleL#8) -- 1
  #BsH#(doubleL#9) -- 1
  #BsH#(doubleL#10) -- 1
  #BsH#(doubleL#11) -- 6

  Bs/ dimHilbTangentSpace;
  -- also consider other monomial ideals?
///

------------------------------
-- Part 6. Radius of the Hilbert scheme?
------------------------------


-----------------------------
-- Documentation
-----------------------------

beginDocumentation()

doc ///
    Key
      HilbertSchemes
    Headline
      a package for investigating Hilbert schemes
    Description
      Text
       This package provides functions for investigating Hilbert schemes. For example, it allows one to study Hilbert polynomials or saturated
       lex ideals associated to Macaulay or Gotzmann partitions.
      Example
       S = ZZ/101[a..f];
       M = genericSymmetricMatrix(S, a, 3);
       I = minors(2, M) --Veronese in P4
       f = HP(I) --non-Projective Hilbert polynomial of I
       m = mVector f --Macaulay decomposition for f
       A = MtoA m -- A-vector for lex ideal with Hilbert polynomial f    
      Text
      	  In addition, this package contains methods to study Hartshorne fans and canonical distractions of monomial ideals,
	  as well as to study the dimension of the tangent space at a point on the Hilbert scheme.
      Example
      	  m = new Partition from {4,3}
      	  L = monomialIdeal lexIdeal(m,S)
	  netList fanComponents L
	  netList{decompose canonicalDistraction(L, symbol t), decompose randomCanonicalDistraction(L)}
///

doc ///
    Key
    	HP
	(HP,Ideal)
	(HP,Ideal,RingElement)
	(HP,Module)
	(HP,Module,RingElement)
	(HP,Partition,RingElement)
    Headline
    	Compute the Hilbert Polynomial of an ideal or module
    Usage
    	HP(I)
	HP(I,z)
	HP(M)
	HP(M,z)
	HP(mvec,z)
    Inputs
    	I:Ideal
	z:RingElement
	    variable used in output of Hilbert polynomial
	M:Module
	mvec:Partition
    Description
    	Text
	    Given an ideal, module, or partition, HP outputs the (non-projective) Hilbert polynomial associated to it.
	    Inputting a RingElement changes the variable used in the polynomial.
	Example
	    S = ZZ/101[a..d];
	    I = monomialCurveIdeal(S, {1,2,3});
  	    HP I
  	    HP(I, c)
	Text
	    Given a partition, HP outputs the Hilbert polynomial associated to it using Macaulay's theorem.
	Example
	    p = new Partition from {4,3}
    	    HP(p,c)
///

doc ///
    Key
    	fanComponents
	(fanComponents,MonomialIdeal)
	
    Headline
    	computes Hartshorne fan components of a monomial ideal
    Usage
    	fancomponents(I)
    Inputs
    	I:MonomialIdeal
    Description
    	Text
	    Given a monomial ideal J, fanComponents computes the irreducible (linear) components of the Hartshorne fan of J. 
	    See Reeves 1995 or Hartshorne 1966.   
	Example
	    S = ZZ/101[a..d];
  	    J = monomialIdeal"a,b4,b3c"
  	    netList fanComponents J
///

doc ///
    Key
    	randomPtOnLex
	(randomPtOnLex,Partition,Ring)
    Headline
    	Outputs random point on the lex component of the Hilbert scheme
    Usage
    	randomPtOnLex(M,S)
    Inputs
    	M:Partition
	S:Ring
    Outputs
    	:Ideal
    Description
    	Text
	    Given a Macaulay partition associated to a Hilbert polynomial of an ideal in the ring S,
	    randomPtOnLex outputs a random point on the lexicographic component of the Hilbert Scheme associated to
	    the polynomial with that Macaulay partition.
	Example
	    S = ZZ/101[a..d];
  	    p = new Partition from {4,3}
  	    J = randomPtOnLex(p, S)
///

doc///
    Key
    	macaulayHP
	(macaulayHP,List,RingElement)
	(macaulayHP,Partition,RingElement)
    Headline
    	Computes a Hilbert polynomial associated to a Macaulay partition
    Usage
    	macaulayHP(L,z)
	macaulayhP(M,z)
    Inputs
    	L:List
	M:Partition
	z:RingElement
    Description
    	Text
	    Computes a Hilbert polynomial associated to a Macaulay partition
    	Example
	    A = ZZ/101[t];
  	    p = new Partition from {4,3};
	    macaulayHP(p, t)
    	Text
	    Observe that the Hilbert polynomial computed from a Macaulay partition is
	    equal to the Gotzmann Hilbert polynomial of the conjugate partition.
	Example
	     gotzmannHP(conjugate p, t)
///

doc///
    Key
    	MtoA
	(MtoA,List)
	(MtoA,Partition)
    Headline
    	Converts an M-vector into its associated A-vector
    Usage
    	MtoA(L)
	MtoA(p)
    Inputs
    	L:List
	p:Partition
    Description
    	Text
	    The A-vector gives rise to a unique, saturated lexicographic ideal associated to that Hilbert polynomial;
	    see e.g. Reeves-Stillman 1997. MtoA gives the associated A-vector corresponding to the M-vector satisfying Macaulay's theorem.
    	Example
	    M = {4,3};
	    MtoA(M)
///

doc///
    Key
    	gotzmannHP
	(gotzmannHP,List,RingElement)
	(gotzmannHP,Partition,RingElement)
    Headline
    	Computes a Hilbert polynomial associated to a partition using Gotzmann's theorem
    Usage
    	gotzmannHP(L,z)
	gotzmannHP(M,z)
    Inputs
    	L:List
	M:Partition
	z:RingElement
    Description
    	Text
	    Computes a Hilbert polynomial associated to a partition using Gotzmann's theorem.
    	Example
	    A = ZZ/101[t];
  	    p = new Partition from {4,3};
	    gotzmannHP(p, t)
    	Text
	    Observe that the Hilbert polynomial computed from a Gotzmann decomposition is
	    equal to the Hilbert polynomial computed using Macaulay's theorem on the conjugate partition.
	Example
	     macaulayHP(conjugate p, t)
///

doc///
    Key
    	canonicalDistraction
	(canonicalDistraction,MonomialIdeal,Thing)
    Headline
    	Computes the canonical distraction of a monomial ideal
    Usage
    	canonicalDistraction(I,t)
    Inputs
    	I:MonomialIdeal
	t:Thing
    Outputs
    	:Ideal
	    canonical distraction of I
    Description
    	Text
	    Let J be the standard polarization of an ideal I. The canonical distraction of I is the image of J under the map
	    $z_{i,j} \mapsto x_i - t_{i,j} x_n$. 
	    By Theorem 4.9 of [Harshrone 1996], the canonical distraction of $I$ is an intersection of prime ideals of the form
	    $
	    (x_{i_1}-t_{i_1, j_1} x_0, \dots, x_{i_s}-t_{i_s, j_s} x_0)
	    $
	    with $i_1 < i_2 < \dots < i_s$.
	Example
	    S = ZZ/101[a..d];
	    I = monomialIdeal"a,b4,b3c"
	    dist = canonicalDistraction(I, symbol t)
	    netList decompose dist
	    netList fanComponents I
    Caveat
    	It is assumed that the input ideal I does not have any generators involving the last variable in S = ring I.
///

doc///
    Key
    	HF
	(HF,Ideal,ZZ)
	(HF,Ideal,ZZ,ZZ)
	(HF,Module,ZZ,ZZ)
	(HF,Ring,ZZ,ZZ)
///

doc///
    Key
    	dimHilbTangentSpace
	(dimHilbTangentSpace,Ideal)
    Headline
    	Computes the dimension of the tangent space of the Hilbert Scheme at a point
    Usage
    	dimHilbTangentSpace(I)
    Inputs
    	I:Ideal
    Description
    	Text
	    Given an ideal I, dimHilbTangentSpace outputs the dimension of the tangent space of the Hilbert Scheme
	    on which I lies at the point I.
	Example
	    S = ZZ/101[a..d];
  	    A = QQ[t];
  	    hp = macaulayHP(new Partition from {4,3}, t) --Hilbert polynomial for the twisted cubic curve
  	    Bs = stronglyStableIdeals(hp, S) --list of Borel-fixed ideals with Hilbert polynomial hp
	    Bs/dimHilbTangentSpace
///

doc///
    Key
    	mVector
	(mVector,Ideal)
	(mVector,RingElement)
    Headline
    	Compute Macaulay decomposition of a Hilbert polynomial
    Usage
    	mVector(I)
	mVector(hp)
    Inputs
    	I:Ideal
	hp:RingElement
	    non-projective Hilbert polynomial
    Outputs
    	:Partition
	    M-vector associated to a Hilbert polynomial
    Description
    	Text
    	    Given an ideal or a Hilbert polynomial, mVector computes the Macaulay partition associated to the Hilbert polynomial.
	Example
	    S = ZZ/101[a..d];
  	    I = monomialCurveIdeal(S, {1,2,3}) --twisted cubic curve
	    mVector(I)
	    mVector(HP(I))
///

doc///
    Key
    	randomCanonicalDistraction
	(randomCanonicalDistraction,MonomialIdeal)
	(randomCanonicalDistraction,MonomialIdeal,HashTable)
    Headline
    	Compute a random canonical distraction of a monomial ideal
    Usage
    	randomCanonicalDistraction(I)
	randomCanonicalDistraction(I,H)
    Inputs
    	I:Ideal
	H:HashTable
    Description
    	Text
	    Given a monomial ideal J, produces a random canonical distraction of J.
	Example
	    S = ZZ/101[a..d];
	    I = monomialIdeal"a,b4,b3c"
	    dist = canonicalDistraction(I, symbol t)
	    randomDist = randomCanonicalDistraction(I)
	    netList{decompose dist, decompose randomDist}
///

doc///
    Key
    	AtoM
	(AtoM,List)
    Headline
    	Converts an A-vector into its associated M-vector
    Usage
    	AtoM(L)
    Inputs
    	L:List
    Description
    	Text
	    The A-vector gives rise to a unique, saturated lexicographic ideal associated to that Hilbert polynomial;
	    see e.g. Reeves-Stillman 1997. AtoM gives the associated M-vector corresponding to the Macaulay partition
	    corresponding to the Hilbert polynomial of the lexicographic ideal associated to the vector A.
	Example
	    A = {11,3,4}
	    AtoM(A)
///

doc///
    Key
	(lexIdeal,Partition,Ring)
    Headline
    	Computes the saturated lex ideal associated to a Macaulay partition
    Usage
    	lexIdeal(M,S)
    Inputs
    	M:Partition
	S:Ring
    Description
    	Text
	    Given a Macaulay partition, computes the unique saturated lex ideal with a Hilbert polynomial corresponding to that partition.
	Example
	      S = ZZ/101[a..d];
  	      p = new Partition from {4,3};
  	      L = lexIdeal(p, S)
	      HP(L)
///
end---------------------------------------------------------------


restart
debug needsPackage "HilbertSchemes"
-- Let's check all of these on the twisted cubic
S = ZZ/101[a,b,c,d]
I = saturate lexIdeal monomialCurveIdeal(S, {1,2,3})
assert(Mvector I === new Partition from {4,3})
lexIdeal(S, new Partition from {4,3})
MtoA {4,3} == {1,3}
AtoPartition {1,3} == {2,2,2,1}
PartitionToA {2,2,2,1} == {1,3}
hilbViaM {4,3}
hilbViaPartition {2,2,2,1}

Lideal(S, {2,3})
Lideal(S, {10,2,3})
lexIdealViaM(S, {10,3,2})
hilbViaM {10,3,2}

AtoM MtoA {10,4,4,3,1} == {10,4,4,3,1}
AtoM MtoA {3} == {3}
AtoM MtoA {7,2,2,2,1} 
p = AtoPartition {10,3,2}
PartitionToA p

hilbViaPartition {3,3,2,2,1,1,1}
AtoM PartitionToA {3,3,2,2,1,1,1}
hilbViaM oo

S = ZZ/101[a,b,c,d]
I = monomialCurveIdeal(S, {1,3,4})
Mvector I

S = ZZ/101[a..f]
I = minors(2, genericSymmetricMatrix(S, a, 3))
Mvector I
lexIdeal I
saturate oo

needs "hilbert-polynomials.m2"
S = ZZ/101[a,b,c,d]
hilbViaPartition({2,2,2,1})
binomial(t + 2 - 1, 2 - 1) + binomial(t + 2 - 2, 2 - 1) + binomial(t + 2 - 3, 2 - 1) + 1
binomial(t - 5 + 3, 3) - binomial(t + 2, 3)

-- Veronese
S = ZZ/101[a..f]
M = genericSymmetricMatrix(S, a, 3)
I = minors(2, oo)
f = hilbertPolynomial(I, Projective => false)
Mvector f
MtoA oo
L = lexIdeal(S, Mvector f)
hilbViaPartition {3,3,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1} -- veronese: lex has regularity 18!

-- -- Let's check some 
L = lexIdeal(S, new Partition from {18, 7, 4})
hp = hilbertPolynomial(L, Projective => false)
netList for d from 0 to 30 list {d, hilbertFunction(d, L), sub(hp, {(ring hp)_0 => d})}


------------------------------------
--Development Section
------------------------------------

restart
uninstallPackage "HilbertSchemes"
restart
installPackage "HilbertSchemes"
restart
needsPackage "HilbertSchemes"
elapsedTime check "HilbertSchemes"
viewHelp "HilbertSchemes"
