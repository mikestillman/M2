debug Core

-- taking code mostly from local/classes/math731-factoring
--  and also from packages/development/UPolynomials.m2
--  and also from packages/development/UPolynomials2.m2

newPackage(
        "TowerRings",
    	Version => "0.1", 
    	Date => "12 Feb 2010",
        Authors => {{Name => "Mike Stillman", 
                  Email => "mike@math.cornell.edu", 
                  HomePage => "http://www.math.cornell.edu/~mike"}},
        Headline => "gcds and factorization of univariate polynomials",
        DebuggingMode => true
        )

debug Core

export {
     "towerRing",
     "powerModF",
     "lowerP",
     "randomPolynomial",
     "squareFreeDecomposition",
     "distinctDegreeFactorization",
     "ord",
     "cantorZassenhaus",
     "factorizeCZ"
     }

lowerP = method()

Tower = new Type of EngineRing
Tower.synonym = "tower ring"

pretty := relns -> (
     s := toSequence relns;
     if #s === 1 then s = first s;
     s)

expression Tower := S -> (
     if #S.relations > 0 then (
	  new Divide from { expression S.ambient, expression pretty S.relations }
	  )
     else new FunctionApplication from { towerRing, (expression last S.baseRings, toSequence S.generators) }
     )     
     
undocumented (expression, Tower)

toExternalString Tower := R -> toString expression R
undocumented (toExternalString, Tower),

toString Tower := R -> (
     if hasAttribute(R,ReverseDictionary) then toString getAttribute(R,ReverseDictionary)
     else toString expression R)
undocumented (toString, Tower)

net Tower := R -> (
     if hasAttribute(R,ReverseDictionary) then toString getAttribute(R,ReverseDictionary)
     else net expression R)
undocumented (net, Tower)

describe Tower := R -> net expression R

coefficientRing Tower := Ring => R -> last R.baseRings
numgens Tower := Ring => R -> R.numgens

--------------------------------------
--------------------------------------

newTowerRing = method()
newTowerRing(Ring,List) := (A,genSymbols) -> (
     if not (A.?Engine and A.Engine) 
     then error "expected coefficient ring handled by the engine";
     -- check that A is a finite field
     if not A.?char then error "expected a finite field as coefficient ring";
     p := A.char;
     if not isPrime p then error "towerRing: for now we expect a finite field as coefficient ring";
     varnames := genSymbols/toString;
     T := new Tower from rawTowerRing(p,toSequence varnames);
     T.baseRings = append(A.baseRings,A);
     T.numgens = #varnames;
     T.degreeLength = 0;
     commonEngineRingInitializations T;
     ONE := T#1;
     toExternalString T := r -> toString expression r;
     expression T := f -> raw f;
     T.generatorSymbols = genSymbols;
     T.generators = apply(#genSymbols, i -> T_i);
     T.relations = {};
     T.ambient = null;
     gcd(T,T) := (a,b) -> new T from rawGCD(raw a, raw b);
     gcdCoefficients(T,T) := (a,b) -> apply(rawExtendedGCD(raw a, raw b), r -> new T from r);
     lowerP(T) := (a) -> new T from rawLowerP a;
     inverse(T) := (a) -> (b := rawInverse raw a; if b == 0 then null else new T from b);
     -- need to write: listForm
     -- need to write: promote, lift
     T
     )
newTowerRing(Tower,Ideal) := (T, I) -> (
     IL := join(T.relations, I_*);
     polys := IL/raw//toSequence;
     if #polys < numgens T then polys = splice(polys, (numgens T - #polys : 0_(raw T)));
     TQ := new Tower from rawTowerQuotientRing(raw T,polys);
     TQ.baseRings = T.baseRings;
     TQ.numgens = numgens T;
     TQ.degreeLength = 0;
     commonEngineRingInitializations TQ;
     ONE := TQ#1;
     toExternalString TQ := r -> toString expression r;
     expression TQ := f -> raw f;
     TQ.generatorSymbols = T.generatorSymbols;
     TQ.generators = apply(numgens T, i -> TQ_i);
     TQ.relations = IL;
     TQ.ambient = T;
     gcd(TQ,TQ) := (a,b) -> new TQ from rawGCD(raw a, raw b);
     gcdCoefficients(TQ,TQ) := (a,b) -> apply(rawExtendedGCD(raw a, raw b), r -> new TQ from r);
     lowerP(TQ) := (a) -> new TQ from rawLowerP a;
     inverse(TQ) := (a) -> (b := rawInverse raw a; if b == 0 then null else new TQ from b);
     -- need to write: listForm
     -- need to write: promote, lift
     TQ
     )
towerRing = method()
towerRing(Ring,Sequence) := (A,variables) -> (
     v := flatten toList apply(variables, x->if class x === MutableList then toList x else x);
     v = apply(#v, 
	       i -> (
		    try baseName v#i
		    else if instance(v#i,String) and match("[[:alnum:]$]+",v#i) then getSymbol v#i
		    else error "name " | v#i | " not usable as a variable"));
     newTowerRing(A,v)
     )
towerRing(Ring) := (R) -> (
     -- if monoid R is Weyl or Skew, complain.
     -- if there is a quotient ring, we need to check if it is triangular.  If so, create a quotient tower ring
     A := coefficientRing R;
     towerRing(A, generators R)
     )

Tower / Ideal := (T, I) -> newTowerRing(T,I)

-- in preparation:7/7/10
--rawResultant = method()
--rawResultant(RawRingElement,RawRingElement) := (F,y) -> (
--     )

squareFreeDecomposition = method()
squareFreeDecomposition RawRingElement := (f) -> (
     -- ASSUMPTION: f is in a tower ring
     --  s.t. the tower missing outermost variable is a field
     R := ring f;
     p := rawCharacteristic R;
     x := R_0;
     result := {};
     T := rawGCD(f,rawDiff(0,f));
     V := f//T;
     k := 0;
     while rawDegree(0,V) =!= 0 do (
	  k = k+1;
	  W := rawGCD(T,V);
	  Ak := V//W;
	  V = W;
	  T = T//V;
	  if rawDegree(0,Ak) =!= 0 then 
	      result = append(result,{k,Ak});
	  );
     if rawDegree(0,T) != 0 then (
	  -- we have a polynomial in x^p
	  result2 := squareFreeDecomposition rawLowerP(T);
	  result2 = apply(result2, a -> {p*a#0, a#1});
	  result = join(result,result2);
	  );
     result
     );
squareFreeDecomposition RingElement := (f) -> (
    R := ring f;
    C := squareFreeDecomposition raw f;
    apply(C, v -> {v#0, new R from v#1})
    )

ord = method()
ord RawRing := (R) -> (
     p := rawCharacteristic R; -- charac.
     n := rawExtensionDegree(1,R); -- all but first variable
     if n < 0 then error "expected univariate ring over a finite field";
     p^n
     )

distinctDegreeFactorization = method()
distinctDegreeFactorization RawRingElement := (f) -> (
     result := {};
     R := ring f;
     q := ord R; -- actually of coeff ring of R (all but outermost variable)
     x := R_0;
     w := x;
     for d from 1 when rawDegree(0, f) > 0 do (
	  if 2*d > rawDegree(0, f) then (
	       result = append(result,{rawDegree(0,f),f});
	       f = 1_R;)
	  else (
	       w = rawPowerMod(w,q,f);
	       gd := rawGCD(w-x,f);
	       if rawDegree(0, gd) =!= 0 then (
		    result = append(result,{d, gd});
		    f = f // gd;
		    w = w % f;
		    ));
	  );
     result);

randomPolynomial = (R,d) -> (
     x := R_0;
     sum for i from 0 to d list rawMatrixEntry(rawRandomConstantMatrix(R,1,1,1.0,0,1),0,0) * x^i
     )

cantorZassenhaus = method()
cantorZassenhaus(ZZ,RawRingElement) := (d,F) -> (
     -- assumption: F is a polynomial in k[x],
     -- where k is a finite field of char > 2, and F is a 
     -- squarefree product of irreducible 
     -- polynomials, all of degree d.
     R := ring F;
     q := ord R;
     k := rawDegree(0,F) // d;
     if k === 1 then {F}
     else (
          --print "Entering CZ";
	  --<< " Factoring " << toString(F) << " d = " << d << " k = " << k << endl;
          M := (q^d-1)//2;
          count := 0;
	  while (
	       T := randomPolynomial(R,2*d-1);
               count = count+1;
	       --<< "  trying " << see T << endl;
	       T1 := rawPowerMod(T,M,F);
	       G := rawGCD(F,T1-1);
	       --<< "    G = " << see G << endl;
	       rawDegree(0,G) === 0 or rawDegree(0,G) === rawDegree(0,F)) do ();
          --<< "count = " << count << endl;
     	  -- At this point, G is a proper factor, as is F//G,
     	  -- so recurse
     	  join(cantorZassenhaus(d,G),
	       cantorZassenhaus(d,F//G)))
     );

factorizeCZ = method()
factorizeCZ RawRingElement := (f) -> (
      F := squareFreeDecomposition f;
      F1 := apply(F, xf -> {xf#0,
             distinctDegreeFactorization (xf#1)});
      F2 := apply(F1, xf -> {xf#0, flatten (
             apply(xf#1, f -> cantorZassenhaus(f#0,f#1)))});
      flatten apply(F2, xf -> 
              apply(xf#1, g -> {xf#0,g}))
      )

------------------------------------------
-- Maybe keep tower rings ONLY low level
-*
debug Core
makeTowerRing = method()
makeTowerRing PolynomialRing := (R) -> (
    -- use the same names as R
    -- build the full stack of towers?
    -- make sure we can transfer back and forth
    -- if the coefficient ring has variables, use them too!  Even if they are 'toField'ed
    T := rawTowerRing(char p, toSequence R.generatorSymbols)
    )
*-
------------------------------------------
beginDocumentation()

TEST ///
  -- creation of tower rings
  restart
  debug needsPackage "TowerRings"
  R = ZZ/101[a]
  S = ZZ/101[a]
  T = ZZ/101[a, Constants=>true]
  U = ZZ/101[a]  
  V = ZZ/101[a, Constants=>true]
  use R    
  use T
  assert(ring a === T)
  
  R = towerRing(ZZ/101, (a,b,c,d))
  assert(ring a === R)
  assert(ring b === R)
  assert(ring c === R)
  assert(ring d === R)
  assert(0_R == 0)
  F = (a+3)^2*(a^2-3*a-7)*(a-1)
  G = (a+3)^3*(a^2-3*a-7)
  assert(F * (a+3) == G * (a-1))

  a = 4
  use R
  ring a
  assert(gens R == {a,b,c,d})

  assert(R_0 == a)
  assert(R_1 == b)
  assert(R_2 == c)
  assert(R_3 == d)
  assert(numgens R == 4)

  --S = towerRing(ZZ/3, toSequence{a}) -- ERROR: it cannot seem to reuse a here.
  S = towerRing(ZZ/3, toSequence{symbol a})
  use R  
  assert(ring(a+b) === R)
///

TEST ///
  a = symbol a
  b = symbol b  
  ZZ/101[a,b]/(a^3-a-5, b^2-a-2)
  primaryDecomposition ideal oo

  needsPackage "TowerRings"
  R = towerRing(ZZ/101, (symbol a,symbol b,symbol x))
  F = a^3-a-5
  G = b^2-a-2
  A = R/(F,G)  -- this is a field[x]
  describe A
  f = (x^2-a-2)
  assert(a * inverse a == 1)
  assert(a * a^-1 == 1)
  assert(b * b^-1 == 1)
  assert((a+b) * (a+b)^-1 == 1)
  
  -- Now for gcd in A
  F = (x-a)*(x-b)
  G = (x-a)^2
  gcd(F,G) == x-a
  (g,u,v) = gcdCoefficients(F,G)
  assert(u*F + v*G == g)

  F = b*(x-a)^10*(x-b)^13
  G = (x-a)^2*(x-a-b)^6
  gcd(F,G) == (x-a)^2
  (g,u,v) = gcdCoefficients(F,G)
  assert(u*F + v*G == g)
  -- NEED: get at lead coefficient: check that g is monic.  
///

TEST ///
  needsPackage "TowerRings"
  -- gcd's over extension fields
  testGCD = (F1,F2) -> (
     G1 := gcd(F1,F2);
     (G,U,V) := gcdCoefficients(F1,F2);
     assert(G == U*F1 + V*F2);
     assert(G == G1);
     (G,U,V)
     )

  R = towerRing(ZZ/101, (symbol a,symbol b,symbol x))
  f = a^3-a-5
  g = b^2-a-2
  A = R/(f,g)  -- this is a field[x]
  describe A

  F = (b*x-a)^6*(x-a*b)^3
  G = (x - b^-1*a) * (x-a*b)^7
  testGCD(F,G)
  
  -- More interesting gcd
  g = symbol g
  r = symbol r
  R = towerRing(ZZ/32003, (r, g_3, g_2))
  exts = {r^2-3, g_3^4+14661*g_3^2-57}
  A = R/exts
  describe A
  F = g_2^8+8*g_2^7*g_3+8*g_2^7*r+28*g_2^6*g_3^2+56*g_2^6*g_3*r+28*g_2^6*r^2-10736*g_2^6+56*g_2^5*g_3^3+168*g_2^5*g_3^2*r+168*g_2^5*g_3*r^2-410*g_2^5*g_3+56*g_2^5*r^3-410*g_2^5*r+169*g_2^5+70*g_2^4*g_3^4+280*g_2^4*g_3^3*r+420*g_2^4*g_3^2*r^2-1025*g_2^4*g_3^2+280*g_2^4*g_3*r^3-2050*g_2^4*g_3*r+845*g_2^4*g_3+70*g_2^4*r^4-1025*g_2^4*r^2+845*g_2^4*r-15883*g_2^4+56*g_2^3*g_3^5+280*g_2^3*g_3^4*r+560*g_2^3*g_3^3*r^2+9301*g_2^3*g_3^3+560*g_2^3*g_3^2*r^3-4100*g_2^3*g_3^2*r+1690*g_2^3*g_3^2+280*g_2^3*g_3*r^4-4100*g_2^3*g_3*r^2+3380*g_2^3*g_3*r+474*g_2^3*g_3+56*g_2^3*r^5+9301*g_2^3*r^3+1690*g_2^3*r^2+474*g_2^3*r-11129*g_2^3+28*g_2^2*g_3^6+168*g_2^2*g_3^5*r+420*g_2^2*g_3^4*r^2-1025*g_2^2*g_3^4+560*g_2^2*g_3^3*r^3-4100*g_2^2*g_3^3*r+1690*g_2^2*g_3^3+420*g_2^2*g_3^2*r^4-6150*g_2^2*g_3^2*r^2+5070*g_2^2*g_3^2*r+711*g_2^2*g_3^2+168*g_2^2*g_3*r^5-4100*g_2^2*g_3*r^3+5070*g_2^2*g_3*r^2+1422*g_2^2*g_3*r-1384*g_2^2*g_3+28*g_2^2*r^6-1025*g_2^2*r^4+1690*g_2^2*r^3+711*g_2^2*r^2-1384*g_2^2*r+1268*g_2^2+8*g_2*g_3^7+56*g_2*g_3^6*r+168*g_2*g_3^5*r^2-410*g_2*g_3^5+280*g_2*g_3^4*r^3-2050*g_2*g_3^4*r+845*g_2*g_3^4+280*g_2*g_3^3*r^4-4100*g_2*g_3^3*r^2+3380*g_2*g_3^3*r+474*g_2*g_3^3+168*g_2*g_3^2*r^5-4100*g_2*g_3^2*r^3+5070*g_2*g_3^2*r^2+1422*g_2*g_3^2*r-1384*g_2*g_3^2+56*g_2*g_3*r^6-2050*g_2*g_3*r^4+3380*g_2*g_3*r^3+1422*g_2*g_3*r^2-2768*g_2*g_3*r+2536*g_2*g_3+8*g_2*r^7-410*g_2*r^5+845*g_2*r^4+474*g_2*r^3-1384*g_2*r^2+2536*g_2*r-3350*g_2+g_3^8+8*g_3^7*r+28*g_3^6*r^2-10736*g_3^6+56*g_3^5*r^3-410*g_3^5*r+169*g_3^5+70*g_3^4*r^4-1025*g_3^4*r^2+845*g_3^4*r-15883*g_3^4+56*g_3^3*r^5+9301*g_3^3*r^3+1690*g_3^3*r^2+474*g_3^3*r-11129*g_3^3+28*g_3^2*r^6-1025*g_3^2*r^4+1690*g_3^2*r^3+711*g_3^2*r^2-1384*g_3^2*r+1268*g_3^2+8*g_3*r^7-410*g_3*r^5+845*g_3*r^4+474*g_3*r^3-1384*g_3*r^2+2536*g_3*r-3350*g_3+r^8-10736*r^6+169*r^5-15883*r^4-11129*r^3+1268*r^2-3350*r+8128
  G = g_2^2-3*g_3^2
  assert(gcd(F,G) == g_2+r*g_3)
  testGCD(F,G)
  
  -- This one seems to fail? (in ModularGCD.m2)  Here it seems to work.  What is the difference?
  -- difference: rawTowerTranslatePoly is not reducing mod the ideal.
  x = symbol x
  a = symbol a
  b = symbol b
  R = towerRing(ZZ/32003, (b,a,x));
  A = R/(b^2-3, a^2-b-1)
  F = (x - b^2 - a)*(x - a - b)^100
  G = (x - b^2 - a)*(x - a + b)^100
  assert(gcd(F,G) == x-b^2-a)
  testGCD(F,G)
///

TEST ///
  -- squarefree factorization
  R = towerRing(ZZ/101, (symbol a,symbol b,symbol x))
  f = a^3-a-5
  g = b^2-a-2
  A = R/(f,g)  -- this is a field[x]

  F = (x-b)^2*(x-a)^2*(b*x^2-b*x-a^2)^3  
  result = squareFreeDecomposition F
  assert(#result == 2)
  assert(result/first//set === set{2,3})
  assert(result/last//product == b^-1 * (x-b)*(x-a)*(b*x^2-b*x-a^2))
  for f in result do assert(ring f#1 === A)
  
  -- What about if f is a polynomial in x^p, but the coefficients are not?
  R = towerRing(ZZ/7, (symbol a,symbol x))
  f = a^3-a-5
  A = R/f  -- this is a field[x]
  F = a*x^14-x^7-a+1
  facs = squareFreeDecomposition F
  assert(a^-1 * F == facs#0#1 ^ (facs#0#0))
  
  -- TODO: try x^3-a, for all a in GF(9).
///

TEST ///
  -- power mod F
  R = towerRing(ZZ/3, (symbol a, symbol x))
  f = a^3-a-1
  A = R/f

  F = (x^2-a)*(x-a-1)
  rawPowerMod(raw x, 3^2, raw F) - raw x
    
  R = towerRing(ZZ/3, (symbol a,symbol b,symbol x))
  f = a^3-a-1
  g = b^2-a-2
  A = R/(f,g)  -- this is a field[x]
  
///

TEST ///
  -- distinct degree factorization
  R = towerRing(ZZ/101, (symbol a,symbol b,symbol x))
  f = a^3-a-5
  g = b^2-a-2
  A = R/(f,g)  -- this is a field[x]

  F = (x-a)*(x-b)*(x^2-a-3)*(x^2-b-3)    
  rawGCD(rawPowerMod(raw x, 101, raw F), raw F)
  rawGCD(rawPowerMod(raw x, 101^2, raw F), raw F)
  facs = squareFreeDecomposition F
  distinctDegreeFactorization raw (facs#0#1)
  
  squareFreeDecomposition (x^2-a-3)
///

TEST ///
  -- this test really doesn't work
-*
  restart
  needsPackage "TowerRings"
*-
  R = towerRing(ZZ/17, (a,b,c))
  index a
  index b
  index c
  S = R/(b^3-b-1)  -- this should eitehr give an error or work!
  S = R/(a^3-a-1) -- this one worked. FAILS
  use R
  S = R/(ideal(a^3-a-1, b^3-a)) -- this one worked.
  raw S
  use R
  S = R/(a^3-a-1, b^3-a) -- this one doesn't work WORKS NOW
  use R
  S = R/(ideal(b^3-a,a^3-a-1)) -- should either reorder, or should give an error.
  raw S

  use R
  S = R/(a^3-a-1, b^3-a) -- OK
  inducedMap(S,R)-- not defined
  phi = map(S,R,{a,b,c})
  use R
  phi a^3 -- crashes
///

end--

restart
uninstallPackage "TowerRings"
restart
needsPackage "TowerRings"
check "TowerRings" -- 3 error occurs
restart
installPackage "TowerRings" -- no doc nodes.


TEST ///
  -- evaluation  FAILS
  R = towerRing(ZZ/101, (symbol a,symbol b,symbol x))
  f = a^3-a-5
  g = b^2-a-2
  A = R/(f,g)  -- this is a field[x]

  F = a*x^3-b*x-1  
  sub(F, {x=>a}) -- CRASH!
  phi = map(A,A,{a,b,a})
  phi x -- CRASH
  
  -- also: promote/lift between different tower rings
///

TEST ///
  -- rawDiff, rawDegree, rawWhatElse?
///

TEST ///
  -- Do this example as a tower ring (over finite field)
  restart
  needsPackage "TowerRings"
  S1 = towerRing(ZZ/32003, (symbol x, symbol y, symbol t))
  T = S1/(ideal(x^4+x^3+2*x^2+1,y+x^3+x^2+x))
  describe T
  f = (t+x)*(t-2*y)*(t^2+x+y)
  squareFreeDecomposition raw f
  distinctDegreeFactorization raw f
  factorizeCZ raw f -- never never land....

///

TEST ///
restart
path  = prepend("~/src/M2-dev/mike/integral-closure-packages/", path)
needsPackage "TowerRings"

-- the first of these doesn't work so well (actually, neither is really functional yet)
R = ZZ/101[a..d, Constants=>true]  -- Constants is an awkward name, not really describing what this ring is
R = towerRing(ZZ/101, vars(0..3))
a
b
a+b
F = a^2+a+1
A2 = R/(ideal(F, b^2-a))
describe A2
debug Core
raw A2
b^100
b^(101^4)
(b+a)^(101^4)

-- Desired:
--  translate to/from a polynomial ring
--  allow "reuse" of variable names
--  make sure 'use T' works  DONE
--  allow lift/promote between related tower rings?
--  division in this ring:  seems to currently be:  1//f (so OK?)
--  'describe T' should do better than give 'T'  DONE

-- Computations to do:
--  resultant
--  factorization
--  make sure operations work for a tower of extensions
///

TEST ///
path  = prepend("~/src/M2-dev/mike/integral-closure-packages/", path)
needsPackage "TowerRings"

S = QQ[y,x, MonomialOrder=>Lex]
I = ideal gens gb ideal(x+y^2, 1+x^2-x*y)
R = S/I
Rt = R[t, Join=>false]
f = (t+x)*(t-2*y)*(t^2+x+y)

///






TEST ///
path  = prepend("~/src/M2-dev/mike/integral-closure-packages/", path)
needsPackage "TowerRings"
R = towerRing(ZZ/2, 1:symbol x)
F = x^3
rawPowerMod(raw x, 2, raw F) -- CRASH on optimized M2, fine on non-optimized...

factorizeCZ raw F
apply(squareFreeDecomposition raw F, xf -> {xf#0, distinctDegreeFactorization(xf#1)})
///

TEST ///
restart
loadPackage "TowerRings"
R = towerRing(ZZ/2, 1:symbol x)
F = (x^2+x+1)^4*x^2
F // F
squareFreeDecomposition raw F
///
end

restart
loadPackage "TowerRings"

---------------------
-- test: resultant --
---------------------
-- create a tower ring:
-- resultant example:
A = (ZZ/2) (monoid[symbol y, symbol x,MonomialOrder=>{1,1}])
R1 = rawTowerRing(2, ("x","y"))
x = R1_0
y = R1_1
F = (y^21
 +y^20*x
 +y^18*(x^3+x+1)
 +y^17*(x^3+1)
 +y^16*(x^4+x)
 +y^15*(x^7+x^6+x^3+x+1)
 +y^14*x^7
 +y^13*(x^8+x^7+x^6+x^4+x^3+1)
 +y^12*(x^9+x^8+x^4+1)
 +y^11*(x^11+x^9+x^8+x^5+x^4+x^3+x^2)
 +y^10*(x^12+x^9+x^8+x^7+x^5+x^3+x+1)
 +y^9*(x^14+x^13+x^10+x^9+x^8+x^7+x^6+x^3+x^2+1)
 +y^8*(x^13+x^9+x^8+x^6+x^4+x^3+x)
 +y^7*(x^16+x^15+x^13+x^12+x^11+x^7+x^3+x)
 +y^6*(x^17+x^16+x^13+x^9+x^8+x)
 +y^5*(x^17+x^16+x^12+x^7+x^5+x^2+x+1)
 +y^4*(x^19+x^16+x^15+x^12+x^6+x^5+x^3+1)
 +y^3*(x^18+x^15+x^12+x^10+x^9+x^7+x^4+x)
 +y^2*(x^22+x^21+x^20+x^18+x^13+x^12+x^9+x^8+x^7+x^5+x^4+x^3)
 +y*(x^23+x^22+x^20+x^17+x^15+x^14+x^12+x^9)
 +(x^25+x^23+x^19+x^17+x^15+x^13+x^11+x^5))
-- Want: resultant wrt y
rawDegree(0, F) == 21
rawDegree(1, F) == 25

toA = (F) -> (
     use A;
     value toString ("poly\"" | toString F | "\"")
     )

toR1 = (F) -> (
     x = rawRingVar(R1,0);
     y = rawRingVar(R1,1);
     value toString F
     )
G = toA F
time discriminant(G,y) -- 4.3 sec on my MBP i7

R1 = rawTowerRing(2, 1:"x")
x = R1_0
D = x^500+x^498+x^494+x^488+x^486+x^484+x^482+x^480+x^478+x^476+x^472+x^470+x^466+x^452+x^450+x^438+x^430+x^428+x^418+x^416+x^414+x^410+x^406+x^402+x^396+x^394+x^388+x^380+x^378+x^374+x^368+x^366+x^364+x^360+x^356+x^352+x^350+x^344+x^338+x^336+x^334+x^332+x^328+x^322+x^312+x^306+x^302+x^296+x^294+x^292+x^290+x^288+x^286+x^280+x^276+x^272+x^268+x^266+x^264+x^260+x^258+x^256+x^252+x^248+x^246+x^244+x^240+x^238+x^232+x^228+x^224+x^214+x^212+x^208+x^204+x^202+x^192+x^188+x^186+x^184+x^182+x^174+x^164+x^158+x^150+x^144+x^142+x^136+x^130+x^120+x^118+x^108+x^96+x^94+x^92+x^86+x^82+x^74+x^72+x^68+x^60+x^54+x^44+x^36+x^34+x^26+x^24+x^22
toR1 G

facs = time squareFreeDecomposition D 
apply(facs, t -> (t#0, distinctDegreeFactorization t#1))
facs#0#1

R1 = rawTowerRing(2, 1:"x")
x = R1_0
F = poly"x197+x196+x195+x192+x189+x187+x180+x179+x178+x175+x174+x171+x168+x167+x165+x164+x162+x161+x158+x157+x156+x154+x150+x147+x143+x141+x137+x136+x135+x134+x132+x131+x130+x129+x127+x126+x125+x123+x122+x120+x117+x116+x115+x113+x112+x111+x108+x102+x100+x99+x98+x97+x95+x94+x93+x92+x90+x89+x87+x86+x84+x81+x77+x74+x73+x69+x66+x65+x62+x61+x59+x58+x57+x56+x54+x53+x51+x49+x47+x46+x45+x44+x43+x40+x39+x38+x36+x34+x33+x31+x25+x23+x21+x20+x18+x17+x16+x15+x12+x9+x2+x+1"
distinctDegreeFactorization F
-----------------------------------------------------
-- squarefree decompositions and gcds of these two --
-- (x+1)^72 factor of disc(G,y)
F0 = y^21+y^20+y^18+y^15+y^14+y^11+y^8
F1 = y^20+y^17+y^16+y^15+y^14+y^12+y^10
-- (x^3+x+1)^2 factor of disc(G,y)
R1 = rawTowerRing(2, ("a","y"))
a = rawRingVar(R1,0)
y = rawRingVar(R1,1)
R2 = rawTowerQuotientRing(R1, (a^3+a+1, 0_R1))
assert(rawExtensionDegree(1,R2) == 3)
a = rawRingVar(R2,0)
y = rawRingVar(R2,1)
F0 = y^21+a*y^20+a*y^17+a^2*y^16+a^2*y^15+y^14+a*y^13+y^12+(a^2+a)*y^11+(a^2+a+1)*y^10+(a+1)*y^9+y^8+a*y^7+(a^2+a)*y^6+y^5+(a^2+a)*y^4+y^3+(a^2+a+1)*y^2
F1 = y^20+(a^2+1)*y^18+a^2*y^17+y^16+(a^2+1)*y^14+y^13+a*y^12+(a+1)*y^11+a^2*y^10+a^2*y^9+(a^2+1)*y^7+(a^2+a)*y^5+(a^2+1)*y^4+(a^2+a+1)*y^3+(a^2+a+1)*y^2+(a^2+1)*y
squareFreeDecomposition F0
squareFreeDecomposition F1
rawGCD(F0,F1)
-- (x^3+x^2+1)^4 factor of disc(G,y)
R1 = rawTowerRing(2, ("a","y"))
a = rawRingVar(R1,0)
y = rawRingVar(R1,1)
R2 = rawTowerQuotientRing(R1, (a^3+a^2+1, 0_R1))
a = rawRingVar(R2,0)
y = rawRingVar(R2,1)
F0 = y^21+a*y^20+(a^2+a)*y^18+a^2*y^17+(a^2+1)*y^16+y^15+y^14+(a^2+a)*y^13+a^2*y^11+y^10+(a+1)*y^9+(a^2+a)*y^8+a*y^7+(a+1)*y^6+(a^2+a+1)*y^5+(a^2+a+1)*y^4+(a+1)*y^3+y^2+y+a^2+1
F1 = y^20+(a^2+1)*y^18+a^2*y^17+y^16+(a+1)*y^15+(a^2+a)*y^14+a*y^13+a*y^12+a^2*y^11+(a^2+a)*y^10+(a+1)*y^9+a^2*y^8+a^2*y^7+a^2*y^6+a^2*y^5+(a^2+1)*y^4+a^2*y^3+a*y^2+(a^2+1)*y+a^2
-- (x^7+x^3+x^2+x+1)^2
R1 = rawTowerRing(2, ("a","y"))
a = rawRingVar(R1,0)
y = rawRingVar(R1,1)
ga = a^7+a^3+a^2+a+1
R2 = rawTowerQuotientRing(R1, (ga, 0_R1))
a = rawRingVar(R2,0)
y = rawRingVar(R2,1)
F0 = y^21+a*y^20+(a^3+a+1)*y^18+(a^3+1)*y^17+(a^4+a)*y^16+(a^6+a^2)*y^15+(a^3+a^2+a+1)*y^14+(a^6+a^3)*y^13+(a^5+a^4+a+1)*y^12+(a^6+a^5+1)*y^11+(a^6+a^5+a^4+a^2+a+1)*y^10+a^5*y^9+(a^4+a^2+1)*y^8+(a^3+1)*y^7+(a^4+a^3+a^2)*y^6+a^3*y^5+(a^4+a^3+a+1)*y^4+(a^5+a^4+a^3+a+1)*y^3+(a^3+a+1)*y^2+(a^5+a^4+a^3)*y+a^6+a^2+a+1
F1 = y^20+(a^2+1)*y^18+a^2*y^17+y^16+(a^6+a^2+1)*y^15+a^6*y^14+(a^6+a^2)*y^13+(a^4+a^3+a^2+a)*y^12+(a^6+a^5+a^4+a)*y^11+(a^6+a^3+a+1)*y^10+(a^5+a^3+a+1)*y^9+(a^6+a^5+a^3+a)*y^8+(a^4+a^3+1)*y^7+(a^5+a^2)*y^6+(a^4+a^3+a+1)*y^5+(a^6+a^5+a^4+a^2+a+1)*y^4+(a^3+a)*y^3+(a^6+a^5+a^3+a^2)*y^2+(a^6+a+1)*y+a^6+a^5+a^2
rawGCD(F0,F1)
-- (x^17+x^16+x^15+x^14+x^13+x^11+x^8+x^6+x^5+x^2+1)^2
R1 = rawTowerRing(2, ("a","y"))
a = rawRingVar(R1,0)
y = rawRingVar(R1,1)
ga = a^17+a^16+a^15+a^14+a^13+a^11+a^8+a^6+a^5+a^2+1
R2 = rawTowerQuotientRing(R1, (ga, 0_R1))
a = rawRingVar(R2,0)
y = rawRingVar(R2,1)
F0 = y^21+a*y^20+(a^3+a+1)*y^18+(a^3+1)*y^17+(a^4+a)*y^16+(a^7+a^6+a^3+a+1)*y^15+a^7*y^14+(a^8+a^7+a^6+a^4+a^3+1)*y^13+(a^9+a^8+a^4+1)*y^12+(a^11+a^9+a^8+a^5+a^4+a^3+a^2)*y^11+(a^12+a^9+a^8+a^7+a^5+a^3+a+1)*y^10+(a^14+a^13+a^10+a^9+a^8+a^7+a^6+a^3+a^2+1)*y^9+(a^13+a^9+a^8+a^6+a^4+a^3+a)*y^8+(a^16+a^15+a^13+a^12+a^11+a^7+a^3+a)*y^7+(a^15+a^14+a^11+a^9+a^6+a^5+a^2+a+1)*y^6+(a^15+a^14+a^13+a^12+a^11+a^8+a^7+a^6+a)*y^5+(a^16+a^15+a^14+a^13+a^10+a^9+a^8+a^5+a^4+a^2+a+1)*y^4+(a^15+a^13+a^11+a^10+a^8+a^5+a^4+a^3+a^2+1)*y^3+(a^16+a^14+a^13+a^11+a^6+a^2+a)*y^2+(a^16+a^13+a^8+a^6+a^5+a^2+a)*y+a^15+a^14+a^13+a^10+a^7+a^6+a^5+a^4+a^3+a^2
F1 = y^20+(a^2+1)*y^18+a^2*y^17+y^16+(a^6+a^2+1)*y^15+a^6*y^14+(a^6+a^2)*y^13+a^8*y^12+(a^10+a^8+a^4+a^2)*y^11+(a^8+a^6+a^4+a^2+1)*y^10+(a^12+a^8+a^6+a^2)*y^9+(a^12+a^8+a^2+1)*y^8+(a^14+a^12+a^10+a^6+a^2+1)*y^7+(a^16+a^12+a^8+1)*y^6+(a^16+a^6+a^4+1)*y^5+(a^14+a^13+a^12+a^11+a^9+a^8+a^7+a^5+a^4+a^3+a+1)*y^4+(a^14+a^8+a^6+1)*y^3+(a^15+a^14+a^13+a^12+a^11+a^10+a^9+a^8+a^7+a^6+a^5+a^3)*y^2+(a^16+a^12+a^9+a^7+a^4+a^2+1)*y+a^14+a^13+a^12+a^9+a^6+a^5+a^4+a^3+a^2+a
rawGCD(F0,F1)
-- (x^58+x^56+x^55+x^54+x^53+x^52+x^51+x^50+x^46+x^45+x^44+x^43+x^42+x^41+x^38+x^35+x^33+x^31+x^29+x^28+x^27+x^26+x^24+x^22+x^15+x^14+x^12+x^10+x^8+x^7+x^6+x^5+x^4+x^3+x^2+x+1)^2
ga = a^58+a^56+a^55+a^54+a^53+a^52+a^51+a^50+a^46+a^45+a^44+a^43+a^42+a^41+a^38+a^35+a^33+a^31+a^29+a^28+a^27+a^26+a^24+a^22+a^15+a^14+a^12+a^10+a^8+a^7+a^6+a^5+a^4+a^3+a^2+a+1
F0 = y^21+a*y^20+(a^3+a+1)*y^18+(a^3+1)*y^17+(a^4+a)*y^16+(a^7+a^6+a^3+a+1)*y^15+a^7*y^14+(a^8+a^7+a^6+a^4+a^3+1)*y^13+(a^9+a^8+a^4+1)*y^12+(a^11+a^9+a^8+a^5+a^4+a^3+a^2)*y^11+(a^12+a^9+a^8+a^7+a^5+a^3+a+1)*y^10+(a^14+a^13+a^10+a^9+a^8+a^7+a^6+a^3+a^2+1)*y^9+(a^13+a^9+a^8+a^6+a^4+a^3+a)*y^8+(a^16+a^15+a^13+a^12+a^11+a^7+a^3+a)*y^7+(a^17+a^16+a^13+a^9+a^8+a)*y^6+(a^17+a^16+a^12+a^7+a^5+a^2+a+1)*y^5+(a^19+a^16+a^15+a^12+a^6+a^5+a^3+1)*y^4+(a^18+a^15+a^12+a^10+a^9+a^7+a^4+a)*y^3+(a^22+a^21+a^20+a^18+a^13+a^12+a^9+a^8+a^7+a^5+a^4+a^3)*y^2+(a^23+a^22+a^20+a^17+a^15+a^14+a^12+a^9)*y+a^25+a^23+a^19+a^17+a^15+a^13+a^11+a^5
F1 = y^20+(a^2+1)*y^18+a^2*y^17+y^16+(a^6+a^2+1)*y^15+a^6*y^14+(a^6+a^2)*y^13+a^8*y^12+(a^10+a^8+a^4+a^2)*y^11+(a^8+a^6+a^4+a^2+1)*y^10+(a^12+a^8+a^6+a^2)*y^9+(a^12+a^8+a^2+1)*y^8+(a^14+a^12+a^10+a^6+a^2+1)*y^7+(a^16+a^12+a^8+1)*y^6+(a^16+a^6+a^4+1)*y^5+(a^18+a^14+a^4+a^2)*y^4+(a^14+a^8+a^6+1)*y^3+(a^20+a^12+a^8+a^6+a^4+a^2)*y^2+(a^22+a^16+a^14+a^8)*y+a^24+a^22+a^18+a^16+a^14+a^12+a^10+a^4
-- (x^112+x^109+x^108+x^102+x^101+x^100+x^90+x^89+x^86+x^84+x^83+x^80+x^78+x^77+x^76+x^75+x^74+x^73+x^70+x^69+x^68+x^67+x^64+x^63+x^62+x^61+x^59+x^58+x^54+x^52+x^50+x^49+x^47+x^46+x^45+x^42+x^40+x^39+x^35+x^34+x^32+x^31+x^30+x^26+x^25+x^24+x^23+x^21+x^17+x^16+x^15+x^13+x^12+x^11+x^8+x^6+x^4+x^2+1)^2
ga = a^112+a^109+a^108+a^102+a^101+a^100+a^90+a^89+a^86+a^84+a^83+a^80+a^78+a^77+a^76+a^75+a^74+a^73+a^70+a^69+a^68+a^67+a^64+a^63+a^62+a^61+a^59+a^58+a^54+a^52+a^50+a^49+a^47+a^46+a^45+a^42+a^40+a^39+a^35+a^34+a^32+a^31+a^30+a^26+a^25+a^24+a^23+a^21+a^17+a^16+a^15+a^13+a^12+a^11+a^8+a^6+a^4+a^2+1
F0 = y^21+a*y^20+(a^3+a+1)*y^18+(a^3+1)*y^17+(a^4+a)*y^16+(a^7+a^6+a^3+a+1)*y^15+a^7*y^14+(a^8+a^7+a^6+a^4+a^3+1)*y^13+(a^9+a^8+a^4+1)*y^12+(a^11+a^9+a^8+a^5+a^4+a^3+a^2)*y^11+(a^12+a^9+a^8+a^7+a^5+a^3+a+1)*y^10+(a^14+a^13+a^10+a^9+a^8+a^7+a^6+a^3+a^2+1)*y^9+(a^13+a^9+a^8+a^6+a^4+a^3+a)*y^8+(a^16+a^15+a^13+a^12+a^11+a^7+a^3+a)*y^7+(a^17+a^16+a^13+a^9+a^8+a)*y^6+(a^17+a^16+a^12+a^7+a^5+a^2+a+1)*y^5+(a^19+a^16+a^15+a^12+a^6+a^5+a^3+1)*y^4+(a^18+a^15+a^12+a^10+a^9+a^7+a^4+a)*y^3+(a^22+a^21+a^20+a^18+a^13+a^12+a^9+a^8+a^7+a^5+a^4+a^3)*y^2+(a^23+a^22+a^20+a^17+a^15+a^14+a^12+a^9)*y+a^25+a^23+a^19+a^17+a^15+a^13+a^11+a^5
F1 = y^20+(a^2+1)*y^18+a^2*y^17+y^16+(a^6+a^2+1)*y^15+a^6*y^14+(a^6+a^2)*y^13+a^8*y^12+(a^10+a^8+a^4+a^2)*y^11+(a^8+a^6+a^4+a^2+1)*y^10+(a^12+a^8+a^6+a^2)*y^9+(a^12+a^8+a^2+1)*y^8+(a^14+a^12+a^10+a^6+a^2+1)*y^7+(a^16+a^12+a^8+1)*y^6+(a^16+a^6+a^4+1)*y^5+(a^18+a^14+a^4+a^2)*y^4+(a^14+a^8+a^6+1)*y^3+(a^20+a^12+a^8+a^6+a^4+a^2)*y^2+(a^22+a^16+a^14+a^8)*y+a^24+a^22+a^18+a^16+a^14+a^12+a^10+a^4

-----------------------
-- Multiple extensions
R1 = rawTowerRing(2, ("a","b","c","x"))
a = R1_0
b = R1_1
c = R1_2
x = R1_3
R2 = rawTowerQuotientRing(R1, (a^3+a+1, b^2-a, c^5-b-1, 0_R1))
assert(rawExtensionDegree(1,R2) == 30)
rawGCD((x-c)^2*(x-b), (x-b)*(x-1))
----------------------
-- function: input is two polynomials F0,F1 in a tower ring

makeTowerRing = (charac,str) -> (
     R1 := rawTowerRing(charac, ("a", "y"));
     a = R1_0;
     ga := value str;
     R2 := rawTowerQuotientRing(R1, (ga, 0_R1));
     a = R2_0;
     y = R2_1;
     R2
     )

ga = "a^112+a^109+a^108+a^102+a^101+a^100+a^90+a^89+a^86+a^84+a^83+a^80+a^78+a^77+a^76+a^75+a^74+a^73+a^70+a^69+a^68+a^67+a^64+a^63+a^62+a^61+a^59+a^58+a^54+a^52+a^50+a^49+a^47+a^46+a^45+a^42+a^40+a^39+a^35+a^34+a^32+a^31+a^30+a^26+a^25+a^24+a^23+a^21+a^17+a^16+a^15+a^13+a^12+a^11+a^8+a^6+a^4+a^2+1"
F0 = y^21+a*y^20+(a^3+a+1)*y^18+(a^3+1)*y^17+(a^4+a)*y^16+(a^7+a^6+a^3+a+1)*y^15+a^7*y^14+(a^8+a^7+a^6+a^4+a^3+1)*y^13+(a^9+a^8+a^4+1)*y^12+(a^11+a^9+a^8+a^5+a^4+a^3+a^2)*y^11+(a^12+a^9+a^8+a^7+a^5+a^3+a+1)*y^10+(a^14+a^13+a^10+a^9+a^8+a^7+a^6+a^3+a^2+1)*y^9+(a^13+a^9+a^8+a^6+a^4+a^3+a)*y^8+(a^16+a^15+a^13+a^12+a^11+a^7+a^3+a)*y^7+(a^17+a^16+a^13+a^9+a^8+a)*y^6+(a^17+a^16+a^12+a^7+a^5+a^2+a+1)*y^5+(a^19+a^16+a^15+a^12+a^6+a^5+a^3+1)*y^4+(a^18+a^15+a^12+a^10+a^9+a^7+a^4+a)*y^3+(a^22+a^21+a^20+a^18+a^13+a^12+a^9+a^8+a^7+a^5+a^4+a^3)*y^2+(a^23+a^22+a^20+a^17+a^15+a^14+a^12+a^9)*y+a^25+a^23+a^19+a^17+a^15+a^13+a^11+a^5
F1 = y^20+(a^2+1)*y^18+a^2*y^17+y^16+(a^6+a^2+1)*y^15+a^6*y^14+(a^6+a^2)*y^13+a^8*y^12+(a^10+a^8+a^4+a^2)*y^11+(a^8+a^6+a^4+a^2+1)*y^10+(a^12+a^8+a^6+a^2)*y^9+(a^12+a^8+a^2+1)*y^8+(a^14+a^12+a^10+a^6+a^2+1)*y^7+(a^16+a^12+a^8+1)*y^6+(a^16+a^6+a^4+1)*y^5+(a^18+a^14+a^4+a^2)*y^4+(a^14+a^8+a^6+1)*y^3+(a^20+a^12+a^8+a^6+a^4+a^2)*y^2+(a^22+a^16+a^14+a^8)*y+a^24+a^22+a^18+a^16+a^14+a^12+a^10+a^4

A = makeTowerRing(2, ga)
F0 = y^21+a*y^20+(a^3+a+1)*y^18+(a^3+1)*y^17+(a^4+a)*y^16+(a^7+a^6+a^3+a+1)*y^15+a^7*y^14+(a^8+a^7+a^6+a^4+a^3+1)*y^13+(a^9+a^8+a^4+1)*y^12+(a^11+a^9+a^8+a^5+a^4+a^3+a^2)*y^11+(a^12+a^9+a^8+a^7+a^5+a^3+a+1)*y^10+(a^14+a^13+a^10+a^9+a^8+a^7+a^6+a^3+a^2+1)*y^9+(a^13+a^9+a^8+a^6+a^4+a^3+a)*y^8+(a^16+a^15+a^13+a^12+a^11+a^7+a^3+a)*y^7+(a^17+a^16+a^13+a^9+a^8+a)*y^6+(a^17+a^16+a^12+a^7+a^5+a^2+a+1)*y^5+(a^19+a^16+a^15+a^12+a^6+a^5+a^3+1)*y^4+(a^18+a^15+a^12+a^10+a^9+a^7+a^4+a)*y^3+(a^22+a^21+a^20+a^18+a^13+a^12+a^9+a^8+a^7+a^5+a^4+a^3)*y^2+(a^23+a^22+a^20+a^17+a^15+a^14+a^12+a^9)*y+a^25+a^23+a^19+a^17+a^15+a^13+a^11+a^5
F1 = y^20+(a^2+1)*y^18+a^2*y^17+y^16+(a^6+a^2+1)*y^15+a^6*y^14+(a^6+a^2)*y^13+a^8*y^12+(a^10+a^8+a^4+a^2)*y^11+(a^8+a^6+a^4+a^2+1)*y^10+(a^12+a^8+a^6+a^2)*y^9+(a^12+a^8+a^2+1)*y^8+(a^14+a^12+a^10+a^6+a^2+1)*y^7+(a^16+a^12+a^8+1)*y^6+(a^16+a^6+a^4+1)*y^5+(a^18+a^14+a^4+a^2)*y^4+(a^14+a^8+a^6+1)*y^3+(a^20+a^12+a^8+a^6+a^4+a^2)*y^2+(a^22+a^16+a^14+a^8)*y+a^24+a^22+a^18+a^16+a^14+a^12+a^10+a^4

findH = (str'ga,strF0, strF1) -> (
     A := makeTowerRing(2, str'ga);
     F0 := value strF0;
     F1 := value strF1;
     S1 = squareFreeDecomposition F0;
     splitc = apply(S1, t -> (if t#0 == 1 then (1_A, t#1) else (g1 := rawGCD(t#1, F1); (g1, F1 // g1))));
     (F0 // product (splitc/first), splitc))

(H, facs) = findH(
     "a^112+a^109+a^108+a^102+a^101+a^100+a^90+a^89+a^86+a^84+a^83+a^80+a^78+a^77+a^76+a^75+a^74+a^73+a^70+a^69+a^68+a^67+a^64+a^63+a^62+a^61+a^59+a^58+a^54+a^52+a^50+a^49+a^47+a^46+a^45+a^42+a^40+a^39+a^35+a^34+a^32+a^31+a^30+a^26+a^25+a^24+a^23+a^21+a^17+a^16+a^15+a^13+a^12+a^11+a^8+a^6+a^4+a^2+1",
     "y^21+a*y^20+(a^3+a+1)*y^18+(a^3+1)*y^17+(a^4+a)*y^16+(a^7+a^6+a^3+a+1)*y^15+a^7*y^14+(a^8+a^7+a^6+a^4+a^3+1)*y^13+(a^9+a^8+a^4+1)*y^12+(a^11+a^9+a^8+a^5+a^4+a^3+a^2)*y^11+(a^12+a^9+a^8+a^7+a^5+a^3+a+1)*y^10+(a^14+a^13+a^10+a^9+a^8+a^7+a^6+a^3+a^2+1)*y^9+(a^13+a^9+a^8+a^6+a^4+a^3+a)*y^8+(a^16+a^15+a^13+a^12+a^11+a^7+a^3+a)*y^7+(a^17+a^16+a^13+a^9+a^8+a)*y^6+(a^17+a^16+a^12+a^7+a^5+a^2+a+1)*y^5+(a^19+a^16+a^15+a^12+a^6+a^5+a^3+1)*y^4+(a^18+a^15+a^12+a^10+a^9+a^7+a^4+a)*y^3+(a^22+a^21+a^20+a^18+a^13+a^12+a^9+a^8+a^7+a^5+a^4+a^3)*y^2+(a^23+a^22+a^20+a^17+a^15+a^14+a^12+a^9)*y+a^25+a^23+a^19+a^17+a^15+a^13+a^11+a^5",
     "y^20+(a^2+1)*y^18+a^2*y^17+y^16+(a^6+a^2+1)*y^15+a^6*y^14+(a^6+a^2)*y^13+a^8*y^12+(a^10+a^8+a^4+a^2)*y^11+(a^8+a^6+a^4+a^2+1)*y^10+(a^12+a^8+a^6+a^2)*y^9+(a^12+a^8+a^2+1)*y^8+(a^14+a^12+a^10+a^6+a^2+1)*y^7+(a^16+a^12+a^8+1)*y^6+(a^16+a^6+a^4+1)*y^5+(a^18+a^14+a^4+a^2)*y^4+(a^14+a^8+a^6+1)*y^3+(a^20+a^12+a^8+a^6+a^4+a^2)*y^2+(a^22+a^16+a^14+a^8)*y+a^24+a^22+a^18+a^16+a^14+a^12+a^10+a^4")
H
netList facs

(H, facs) = findH(
  "a^58+a^56+a^55+a^54+a^53+a^52+a^51+a^50+a^46+a^45+a^44+a^43+a^42+a^41+a^38+a^35+a^33+a^31+a^29+a^28+a^27+a^26+a^24+a^22+a^15+a^14+a^12+a^10+a^8+a^7+a^6+a^5+a^4+a^3+a^2+a+1",
  "y^21+a*y^20+(a^3+a+1)*y^18+(a^3+1)*y^17+(a^4+a)*y^16+(a^7+a^6+a^3+a+1)*y^15+a^7*y^14+(a^8+a^7+a^6+a^4+a^3+1)*y^13+(a^9+a^8+a^4+1)*y^12+(a^11+a^9+a^8+a^5+a^4+a^3+a^2)*y^11+(a^12+a^9+a^8+a^7+a^5+a^3+a+1)*y^10+(a^14+a^13+a^10+a^9+a^8+a^7+a^6+a^3+a^2+1)*y^9+(a^13+a^9+a^8+a^6+a^4+a^3+a)*y^8+(a^16+a^15+a^13+a^12+a^11+a^7+a^3+a)*y^7+(a^17+a^16+a^13+a^9+a^8+a)*y^6+(a^17+a^16+a^12+a^7+a^5+a^2+a+1)*y^5+(a^19+a^16+a^15+a^12+a^6+a^5+a^3+1)*y^4+(a^18+a^15+a^12+a^10+a^9+a^7+a^4+a)*y^3+(a^22+a^21+a^20+a^18+a^13+a^12+a^9+a^8+a^7+a^5+a^4+a^3)*y^2+(a^23+a^22+a^20+a^17+a^15+a^14+a^12+a^9)*y+a^25+a^23+a^19+a^17+a^15+a^13+a^11+a^5",
  "y^20+(a^2+1)*y^18+a^2*y^17+y^16+(a^6+a^2+1)*y^15+a^6*y^14+(a^6+a^2)*y^13+a^8*y^12+(a^10+a^8+a^4+a^2)*y^11+(a^8+a^6+a^4+a^2+1)*y^10+(a^12+a^8+a^6+a^2)*y^9+(a^12+a^8+a^2+1)*y^8+(a^14+a^12+a^10+a^6+a^2+1)*y^7+(a^16+a^12+a^8+1)*y^6+(a^16+a^6+a^4+1)*y^5+(a^18+a^14+a^4+a^2)*y^4+(a^14+a^8+a^6+1)*y^3+(a^20+a^12+a^8+a^6+a^4+a^2)*y^2+(a^22+a^16+a^14+a^8)*y+a^24+a^22+a^18+a^16+a^14+a^12+a^10+a^4"
)
H

(H, facs) = findH(
  "a^17+a^16+a^15+a^14+a^13+a^11+a^8+a^6+a^5+a^2+1",
  "y^21+a*y^20+(a^3+a+1)*y^18+(a^3+1)*y^17+(a^4+a)*y^16+(a^7+a^6+a^3+a+1)*y^15+a^7*y^14+(a^8+a^7+a^6+a^4+a^3+1)*y^13+(a^9+a^8+a^4+1)*y^12+(a^11+a^9+a^8+a^5+a^4+a^3+a^2)*y^11+(a^12+a^9+a^8+a^7+a^5+a^3+a+1)*y^10+(a^14+a^13+a^10+a^9+a^8+a^7+a^6+a^3+a^2+1)*y^9+(a^13+a^9+a^8+a^6+a^4+a^3+a)*y^8+(a^16+a^15+a^13+a^12+a^11+a^7+a^3+a)*y^7+(a^15+a^14+a^11+a^9+a^6+a^5+a^2+a+1)*y^6+(a^15+a^14+a^13+a^12+a^11+a^8+a^7+a^6+a)*y^5+(a^16+a^15+a^14+a^13+a^10+a^9+a^8+a^5+a^4+a^2+a+1)*y^4+(a^15+a^13+a^11+a^10+a^8+a^5+a^4+a^3+a^2+1)*y^3+(a^16+a^14+a^13+a^11+a^6+a^2+a)*y^2+(a^16+a^13+a^8+a^6+a^5+a^2+a)*y+a^15+a^14+a^13+a^10+a^7+a^6+a^5+a^4+a^3+a^2",
  "y^20+(a^2+1)*y^18+a^2*y^17+y^16+(a^6+a^2+1)*y^15+a^6*y^14+(a^6+a^2)*y^13+a^8*y^12+(a^10+a^8+a^4+a^2)*y^11+(a^8+a^6+a^4+a^2+1)*y^10+(a^12+a^8+a^6+a^2)*y^9+(a^12+a^8+a^2+1)*y^8+(a^14+a^12+a^10+a^6+a^2+1)*y^7+(a^16+a^12+a^8+1)*y^6+(a^16+a^6+a^4+1)*y^5+(a^14+a^13+a^12+a^11+a^9+a^8+a^7+a^5+a^4+a^3+a+1)*y^4+(a^14+a^8+a^6+1)*y^3+(a^15+a^14+a^13+a^12+a^11+a^10+a^9+a^8+a^7+a^6+a^5+a^3)*y^2+(a^16+a^12+a^9+a^7+a^4+a^2+1)*y+a^14+a^13+a^12+a^9+a^6+a^5+a^4+a^3+a^2+a"
)
H

(H, facs) = findH(
  "a^7+a^3+a^2+a+1",
  "y^21+a*y^20+(a^3+a+1)*y^18+(a^3+1)*y^17+(a^4+a)*y^16+(a^6+a^2)*y^15+(a^3+a^2+a+1)*y^14+(a^6+a^3)*y^13+(a^5+a^4+a+1)*y^12+(a^6+a^5+1)*y^11+(a^6+a^5+a^4+a^2+a+1)*y^10+a^5*y^9+(a^4+a^2+1)*y^8+(a^3+1)*y^7+(a^4+a^3+a^2)*y^6+a^3*y^5+(a^4+a^3+a+1)*y^4+(a^5+a^4+a^3+a+1)*y^3+(a^3+a+1)*y^2+(a^5+a^4+a^3)*y+a^6+a^2+a+1",
  "y^20+(a^2+1)*y^18+a^2*y^17+y^16+(a^6+a^2+1)*y^15+a^6*y^14+(a^6+a^2)*y^13+(a^4+a^3+a^2+a)*y^12+(a^6+a^5+a^4+a)*y^11+(a^6+a^3+a+1)*y^10+(a^5+a^3+a+1)*y^9+(a^6+a^5+a^3+a)*y^8+(a^4+a^3+1)*y^7+(a^5+a^2)*y^6+(a^4+a^3+a+1)*y^5+(a^6+a^5+a^4+a^2+a+1)*y^4+(a^3+a)*y^3+(a^6+a^5+a^3+a^2)*y^2+(a^6+a+1)*y+a^6+a^5+a^2"
  )
H
netList facs -- non-singular point

(H, facs) = findH(
     "a^3+a^2+1",
     "y^21+a*y^20+(a^2+a)*y^18+a^2*y^17+(a^2+1)*y^16+y^15+y^14+(a^2+a)*y^13+a^2*y^11+y^10+(a+1)*y^9+(a^2+a)*y^8+a*y^7+(a+1)*y^6+(a^2+a+1)*y^5+(a^2+a+1)*y^4+(a+1)*y^3+y^2+y+a^2+1",
     "y^20+(a^2+1)*y^18+a^2*y^17+y^16+(a+1)*y^15+(a^2+a)*y^14+a*y^13+a*y^12+a^2*y^11+(a^2+a)*y^10+(a+1)*y^9+a^2*y^8+a^2*y^7+a^2*y^6+a^2*y^5+(a^2+1)*y^4+a^2*y^3+a*y^2+(a^2+1)*y+a^2"
     )
H


-----------------------------------------------------------------------------------
-- 
restart
loadPackage "TowerRings"

---------------------
-- test: resultant --
---------------------
-- create a tower ring:
-- resultant example:
A = (ZZ/2) (monoid[symbol x, symbol y,MonomialOrder=>{1,1}])
R1 = rawTowerRing(2, ("x","y"))
x = R1_0
y = R1_1

use A
debug Core
rawTowerTranslatePoly(R1, raw(x+y^4))
F = (y^21
 +y^20*x
 +y^18*(x^3+x+1)
 +y^17*(x^3+1)
 +y^16*(x^4+x)
 +y^15*(x^7+x^6+x^3+x+1)
 +y^14*x^7
 +y^13*(x^8+x^7+x^6+x^4+x^3+1)
 +y^12*(x^9+x^8+x^4+1)
 +y^11*(x^11+x^9+x^8+x^5+x^4+x^3+x^2)
 +y^10*(x^12+x^9+x^8+x^7+x^5+x^3+x+1)
 +y^9*(x^14+x^13+x^10+x^9+x^8+x^7+x^6+x^3+x^2+1)
 +y^8*(x^13+x^9+x^8+x^6+x^4+x^3+x)
 +y^7*(x^16+x^15+x^13+x^12+x^11+x^7+x^3+x)
 +y^6*(x^17+x^16+x^13+x^9+x^8+x)
 +y^5*(x^17+x^16+x^12+x^7+x^5+x^2+x+1)
 +y^4*(x^19+x^16+x^15+x^12+x^6+x^5+x^3+1)
 +y^3*(x^18+x^15+x^12+x^10+x^9+x^7+x^4+x)
 +y^2*(x^22+x^21+x^20+x^18+x^13+x^12+x^9+x^8+x^7+x^5+x^4+x^3)
 +y*(x^23+x^22+x^20+x^17+x^15+x^14+x^12+x^9)
 +(x^25+x^23+x^19+x^17+x^15+x^13+x^11+x^5))
time rawTowerTranslatePoly(R1, raw F) -- seems to work first time ?!

---------------------------------------
-- test of tow level Tower ring type --
---------------------------------------

TEST ///
path  = prepend("~/src/M2-dev/mike/integral-closure-packages/", path)
loadPackage "TowerRings"

T = towerRing(ZZ/101,1:symbol a)
F = (a^4-a-1)^2*(a-1)^2*(a+1)^3*a^7
factorizeCZ raw F
squareFreeDecomposition raw F
distinctDegreeFactorization raw F

G = (a^4-a+1)*(a-1)^3
///

restart
--debug Core
path  = prepend("~/src/M2-dev/mike/integral-closure-packages/", path)
loadPackage "TowerRings"

T = towerRing(ZZ/101,1:a)
F = (a^4-a-1)^2*(a-1)
G = (a^4-a+1)*(a-1)^3
gcd(F,G)
(g,u,v) = gcdCoefficients(F,G)
assert(u*F + v*G == g)
(F//g) * g == F
(G // g) * g == G

randomPolynomial(raw T, 3)
a*a
1_T//a

a = symbol a
B = ZZ/101[a..d]
T = towerRing(ZZ/101, (a,b,c,d))
toB = map(B,T,gens B)
toT = map(T,B,gens T)

use T
T/(ideal(a^2-a-1))
S = T/(a^2-a-1, b^2-a)
use B
f1 = a+3*b*c-d^10
f2 = a^40+13*a^39+b*a^4
assert(toB toT f1 == f1)
assert(toB toT f2 == f2)

1/a
use T
I = ideal(a^2-2, b^2-a, c^2-b)
T/I

a  -- now in T
use B
a
use T
a
d
gens T
vars T
T_0
T_1
T_2
T_3
matrix{{T_0,T_1}} -- ok
ideal oo -- ok

use T
F = map(T,B,{T_0,T_1,T_2,T_3}) -- works!
use B
F (a+4*b^3)


T = towerRing(ZZ/101, (a,b))

use B
G = map(B,T,{a,b,c,d})

use T
G a -- CRASH!!
G (a^3+b+3*c)
g1 = G ((a+b+c)^3-3*a*b*c)
use B
g2 = ((a+b+c)^3-3*a*b*c)
g1 == g2

A = ZZ/101[a,b,c,d,Constants=>true]
phi = map(A,B,{a,b,c,d}) -- fails, as does using DegreeMap => i -> {}
degree a

M = matrix{{a,b,x,y}}
(transpose M) * M
det oo
(a+1)^2*(x+1)^2
raw oo

A/(a^2+a+1)  -- crash
B = QQ[symbol a,symbol b, symbol x, symbol y,Constants=>true]  -- crash

-------------------------------------------------------
-- 
restart
loadPackage "TowerRings"
A = towerRing(ZZ/2, (symbol x, symbol y))
F = (y^21
 +y^20*x
 +y^18*(x^3+x+1)
 +y^17*(x^3+1)
 +y^16*(x^4+x)
 +y^15*(x^7+x^6+x^3+x+1)
 +y^14*x^7
 +y^13*(x^8+x^7+x^6+x^4+x^3+1)
 +y^12*(x^9+x^8+x^4+1)
 +y^11*(x^11+x^9+x^8+x^5+x^4+x^3+x^2)
 +y^10*(x^12+x^9+x^8+x^7+x^5+x^3+x+1)
 +y^9*(x^14+x^13+x^10+x^9+x^8+x^7+x^6+x^3+x^2+1)
 +y^8*(x^13+x^9+x^8+x^6+x^4+x^3+x)
 +y^7*(x^16+x^15+x^13+x^12+x^11+x^7+x^3+x)
 +y^6*(x^17+x^16+x^13+x^9+x^8+x)
 +y^5*(x^17+x^16+x^12+x^7+x^5+x^2+x+1)
 +y^4*(x^19+x^16+x^15+x^12+x^6+x^5+x^3+1)
 +y^3*(x^18+x^15+x^12+x^10+x^9+x^7+x^4+x)
 +y^2*(x^22+x^21+x^20+x^18+x^13+x^12+x^9+x^8+x^7+x^5+x^4+x^3)
 +y*(x^23+x^22+x^20+x^17+x^15+x^14+x^12+x^9)
 +(x^25+x^23+x^19+x^17+x^15+x^13+x^11+x^5))
-- Want: resultant wrt y
rawDegree(0, raw F) == 21
rawDegree(1, raw F) == 25

Ax = towerRing(ZZ/2, 1:(symbol x))
B = (ZZ/2) (monoid[symbol x, symbol y,MonomialOrder=>{1,1}])
toB = map(B,A,gens B)
toAx = map(Ax,B,{Ax_0, 0_Ax})
discF = toAx discriminant(toB F, B_1)
squareFreeDecomposition raw discF
factorizeCZ raw discF

----------------------------------------------------
-- Try to get m2 code for creating a tower ring to be useful:
restart
loadPackage "TowerRings"
A = ZZ/7[x,y,z,Constants=>true] -- which variable is the "outer" variable
z^4+x^3+x*z+y*z
oo^2*x
y
z
x+y+z
x+y
x
x^3-y^3
A_0
A_1
A_2
degree x
degree(x, x+y)
I = ideal(x,y,z)
rawPromote(raw A, raw x)
rawPromote(raw A, raw (1_(coefficientRing A))) -- cannot promote
rawLift(raw coefficientRing A, raw (3_A)) -- returns null

B = A/I  -- CRASH
  -- seems we need to make sure the following work: 
  --   rawIndexIfVariable
  --   lift/promote/liftable
  --   rawCoefficient
  --   perhaps other RingElement routines?
  x

-------- Below this taken from Macaulay2Doc/test/tower3.m2, 10 Mar 2014.
needsPackage "TowerRings"

-- example of squarefree fact
R1 = rawTowerRing(101, (1:"x"))
x = R1_0
F = (x+1)^3*(x^2+x+1)*x^3*(x+2)^2
assert(squareFreeDecomposition F == {{1, x^2+x+1}, {2, x+2}, {3, x^2+x}})

R1 = rawTowerRing(101, ("a","x"))
a = R1_0
x = R1_1
R2 = rawTowerQuotientRing(R1, (a^3+a^2+1, 0_R1))
a = R2_0
x = R2_1
F = (x+1)^3*(x^2+x+1)*x^3*(x+2)^2
squareFreeDecomposition F 
assert(squareFreeDecomposition F == {{1, x^2+x+1}, {2, x+2}, {3, x^2+x}})

F = (x+a)^3*(x^2+x+a)*x^3*(x+2+a)^2
squareFreeDecomposition F 

time distinctDegreeFactorization F

ord R1 -- 2
x
w = x
result = {}

w = rawPowerMod(w,2,F)
gd = rawGCD(w-x,F)
rawDegree(0, gd)
  F = F // gd  
  w % F

debug Core
R1 = rawTowerRing(17, 1:"x")
x = R1_0
F = x^(17^3)-x
time factorizeCZ F
F
distinctDegreeFactorization F
F = oo#1#1

cantorZassenhaus(2,F)


-- bug:
{*
restart
*}
needsPackage "TowerRings"
debug Core
R1 = rawTowerRing(17, 1:"x")
x = R1_0
F = x^3-x
distinctDegreeFactorization F

w = x
rawDegree(0,F)
rawPowerMod(w,17,F);
oo
rawPowerMod(w,1,F);
oo

rawPowerMod(w,16,F);
oo
x^2 % F
x^4 % F


R = ZZ[symbol x,symbol y,symbol h0,symbol h1,symbol h2,symbol h3,symbol h4]
F = y^5 + x^2*(h0+h1*y+h2*y^2+h3*y^3+h4*y^4)
F' = diff(y,F)
resultant(F,F',y)
factor oo

R = ZZ/101[y,x,MonomialOrder=>{1,1}]
F = y^5 + x^2*(1+x^3*y+(x^2-x)*y^2)
F = y^12 + x^3*(x^2+(1+x^3)*y+(x^2-x)*y^2)
factor discriminant(F,y)
