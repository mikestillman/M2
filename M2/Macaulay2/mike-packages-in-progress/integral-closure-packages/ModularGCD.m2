///////////////////////////////////////
// DO NOT USE!! 
// After r762, this file was moved to
// the repo svn.macaulay2.com/M2-workshops/IMA-2011/PrimaryDecomposition/ModularGCD.m2
// I am leaving it here for now, just to ease svn history movement
// (and I have these comments so the package won't load).
///////////////////////////////////////




newPackage(
        "ModularGCD",
        Version => "0.1", 
        Date => "",
        Authors => {{Name => "", 
                  Email => "", 
                  HomePage => ""}},
        Headline => "",
        DebuggingMode => true
        )

export {
     integerCRA,
     integerRationalReconstruction,
     reduceMod,     
     polyCRA,
     polyRationalReconstruction,
     modularGCD,
     newgcd -- just a test for mod p gcd in various cases
     }

debug Core

----------------------------------------
-- gcd mod p, and extensions -----------
----------------------------------------
makeTower = method()
makeTower(Ring, List) := (R, extensions) -> (
     -- R should be a ring in a lex order
     -- extensions should be of length 1 less that #vars R.
     varnames := (reverse gens R)/toString//toSequence;
     R1 := rawTowerRing(char R, varnames);
     extensions1 := extensions/(f -> rawTowerTranslatePoly(R1, raw f));
     zeros := (numgens R - #extensions) : 0_R1;
     extensions1 = splice (toSequence extensions1, zeros);
     rawTowerQuotientRing(R1, extensions1)
     )

modpGCD = method()
modpGCD(RingElement, RingElement, List) := (F,G, extensions) -> (
     R := makeTower(ring F, extensions);
     F1 := rawTowerTranslatePoly(R, raw F);
     G1 := rawTowerTranslatePoly(R, raw G);
     H := rawGCD(F1,G1);
     if H == 0 then null else (
     	  use ring F;
     	  poly toString H
	  )
     )
TEST ///
A = ZZ/32003[g_2, g_3, r, MonomialOrder=>Lex]
F = g_2^8+8*g_2^7*g_3+8*g_2^7*r+28*g_2^6*g_3^2+56*g_2^6*g_3*r+28*g_2^6*r^2-10736*g_2^6+56*g_2^5*g_3^3+168*g_2^5*g_3^2*r+168*g_2^5*g_3*r^2-410*g_2^5*g_3+56*g_2^5*r^3-410*g_2^5*r+169*g_2^5+70*g_2^4*g_3^4+280*g_2^4*g_3^3*r+420*g_2^4*g_3^2*r^2-1025*g_2^4*g_3^2+280*g_2^4*g_3*r^3-2050*g_2^4*g_3*r+845*g_2^4*g_3+70*g_2^4*r^4-1025*g_2^4*r^2+845*g_2^4*r-15883*g_2^4+56*g_2^3*g_3^5+280*g_2^3*g_3^4*r+560*g_2^3*g_3^3*r^2+9301*g_2^3*g_3^3+560*g_2^3*g_3^2*r^3-4100*g_2^3*g_3^2*r+1690*g_2^3*g_3^2+280*g_2^3*g_3*r^4-4100*g_2^3*g_3*r^2+3380*g_2^3*g_3*r+474*g_2^3*g_3+56*g_2^3*r^5+9301*g_2^3*r^3+1690*g_2^3*r^2+474*g_2^3*r-11129*g_2^3+28*g_2^2*g_3^6+168*g_2^2*g_3^5*r+420*g_2^2*g_3^4*r^2-1025*g_2^2*g_3^4+560*g_2^2*g_3^3*r^3-4100*g_2^2*g_3^3*r+1690*g_2^2*g_3^3+420*g_2^2*g_3^2*r^4-6150*g_2^2*g_3^2*r^2+5070*g_2^2*g_3^2*r+711*g_2^2*g_3^2+168*g_2^2*g_3*r^5-4100*g_2^2*g_3*r^3+5070*g_2^2*g_3*r^2+1422*g_2^2*g_3*r-1384*g_2^2*g_3+28*g_2^2*r^6-1025*g_2^2*r^4+1690*g_2^2*r^3+711*g_2^2*r^2-1384*g_2^2*r+1268*g_2^2+8*g_2*g_3^7+56*g_2*g_3^6*r+168*g_2*g_3^5*r^2-410*g_2*g_3^5+280*g_2*g_3^4*r^3-2050*g_2*g_3^4*r+845*g_2*g_3^4+280*g_2*g_3^3*r^4-4100*g_2*g_3^3*r^2+3380*g_2*g_3^3*r+474*g_2*g_3^3+168*g_2*g_3^2*r^5-4100*g_2*g_3^2*r^3+5070*g_2*g_3^2*r^2+1422*g_2*g_3^2*r-1384*g_2*g_3^2+56*g_2*g_3*r^6-2050*g_2*g_3*r^4+3380*g_2*g_3*r^3+1422*g_2*g_3*r^2-2768*g_2*g_3*r+2536*g_2*g_3+8*g_2*r^7-410*g_2*r^5+845*g_2*r^4+474*g_2*r^3-1384*g_2*r^2+2536*g_2*r-3350*g_2+g_3^8+8*g_3^7*r+28*g_3^6*r^2-10736*g_3^6+56*g_3^5*r^3-410*g_3^5*r+169*g_3^5+70*g_3^4*r^4-1025*g_3^4*r^2+845*g_3^4*r-15883*g_3^4+56*g_3^3*r^5+9301*g_3^3*r^3+1690*g_3^3*r^2+474*g_3^3*r-11129*g_3^3+28*g_3^2*r^6-1025*g_3^2*r^4+1690*g_3^2*r^3+711*g_3^2*r^2-1384*g_3^2*r+1268*g_3^2+8*g_3*r^7-410*g_3*r^5+845*g_3*r^4+474*g_3*r^3-1384*g_3*r^2+2536*g_3*r-3350*g_3+r^8-10736*r^6+169*r^5-15883*r^4-11129*r^3+1268*r^2-3350*r+8128
G = g_2^2-3*g_3^2
exts = {r^2-3, g_3^4+14661*g_3^2-57}
L  = ideal(F,G) + ideal(exts)
gens gb L
T = makeTower(A, {r^2-3, g_3^4+14661*g_3^2-57})
debug Core
F = rawTowerTranslatePoly(T, raw F)
G = rawTowerTranslatePoly(T, raw G)
rawGCD(F,G) -- should should be g_2 + r*g_3, or g_2 - r*g_3.  -- RIGHT NOW, this FAILS...
///

modpGCDCoefficients = method()
modpGCDCoefficients(RingElement, RingElement, List) := (F,G, extensions) -> (
     R := makeTower(ring F, extensions);
     F1 := rawTowerTranslatePoly(R, raw F);
     G1 := rawTowerTranslatePoly(R, raw G);
     (H,u,v) := rawExtendedGCD(F1,G1);
     if H == 0 then (null,null,null) else (
     	  use ring F;
     	  (poly toString H, poly toString u, poly toString v)
	  )
     )
----------------------------------------

getZZRing = (RQ) -> (
     if not RQ#?"RingOverZZ" then (
	  if coefficientRing RQ === ZZ then
	       RQ#"RingOverZZ" = RQ
     	  else (
	       RQ#"RingOverZZ" = ZZ (monoid RQ);
	       RQ#"RingOverZZ"#"RingOverQQ" = RQ;
	       )
	  );
     RQ#"RingOverZZ"
     )

getQQRing = (RZ) -> (
     if not RZ#?"RingOverQQ" then (
	  RZ#"RingOverQQ" = QQ (monoid RZ);
	  RZ#"RingOverQQ"#"RingOverZZ" = RZ;
	  );
     RZ#"RingOverQQ"
     )

primitiveAssociate = method()
primitiveAssociate RingElement := (F) -> (
     -- assumption: F is in a ring QQ[vars]?
     << "primitiveAssociate needs to be written!" << endl;
     (F, 1)
     )

integerCRA = method()
integerCRA(RingElement, RingElement, ZZ, ZZ) := (f,g,m,n) -> (
     new ring f from rawRingElementCRA(raw f, raw g, m, n)
     )

integerCRA(Sequence, Sequence) := (F,G) -> (
     -- F should be (f,m), G = (G,n)
     -- where f, g are in a poly ring ZZ[vars], and m,n are relatively prime integers.
     -- will return (h, m*n)
     (f,m) := F;
     (g,n) := G;
     (integerCRA(f,g,m,n), m*n)
     )

integerRationalReconstruction = method()
integerRationalReconstruction(RingElement, ZZ) := (F,m) -> (
     RQ := getQQRing ring F;
     new RQ from rawRingElementRatConversion(raw F, m, raw RQ)
     )

reduceMod = method()
reduceMod(RingElement, ZZ) := (F, m) -> (
     -- F should be in frac(ZZ[vars]), or in QQ[vars] or in ZZ[vars]
     -- plan: if F is in one of the first two rings: place it into frac(ZZ[vars]).
     -- answer will be placed into ZZ/m
     G := (numerator F) % m;
     c := sub(denominator F, ZZ);
     (g,u,v) := toSequence gcdCoefficients(c, m);
     if g != 1 then return null;
     (u * G) % m
     )

reduceMod(RingElement, RingElement, RingElement, ZZ) := (F, t, tval, m) -> (
     numer := reduceMod(sub(numerator F, {t => tval}), m);
     denom := reduceMod(sub(denominator F, {t => tval}), m);
     if liftable(denom, coefficientRing ring denom) then (
	  c := lift(denom, coefficientRing ring denom);
	  c = c%m;
	  if c == 0 then error "cannot reduce fraction";
	  (g,a,b) := toSequence gcdCoefficients(c, m);
	  (a * numer) % m
	  )
     else
          error "cannot reduce fraction"
     )

TEST ///
restart
load "ModularGCD.m2"
  RZZ = ZZ[a..d]
  RK = frac RZZ
  numerator(1/3 * a)
  R = ZZ/32003[a..d]
  use RK
  F = a^3 - 12/37 * a^2*b + 11*a*b*c - 1/45 * c^3
  reduceMod(F, 11)
  assert(reduceMod(F, 37) === null)
  assert(reduceMod(F, 15) === null)
  reduceMod(F, 101)
  f1 = reduceMod(F, 11)
  f2 = reduceMod(F, 13)
  (g,r) = integerCRA((f1,11),(f2,13))
  (g,r) = integerCRA((reduceMod(F, 32003), 32003), (g,r))
  integerRationalReconstruction (g,r)
///

polyCRA = method()
polyCRA(RingElement, RingElement, RingElement, RingElement) := (a,b,f,g) -> (
     -- given polynomials a,f,b,g in K[x]
     -- where deg a < deg f,  and deg b < deg g.
     -- return a poly h s.t. h == a mod f, and h == b mod g.
     (p,u,v) := toSequence gcdCoefficients(f,g);
     if p != 1 then error "gcd is not one!";
     u1 := (b * u) % g;
     v1 := (a * v) % f;
     (u1 * f + v1 * g, f*g)
     )

polyCRA(Sequence, Sequence, RingElement, ZZ) := (F,G,t,p) -> (
     -- F should be (f(t), m(t)), G = (g(t), n(t)).
     -- construct h(t) (mod m(t)*n(t)) s.t. h == f mod m, h == g mod n.
     -- All variables except t are considered coefficients.
     (f,m) := F;
     (g,n) := G;
     R := ring f;
     othervars := toList(set gens R - set{t});
     monF := set flatten entries monomials(f, Variables=>othervars);
     monG := set flatten entries monomials(g, Variables=>othervars);
     mons := toList(monF + monG);
     (mnsF, cfsF) := coefficients(f, Monomials=>mons, Variables=>othervars);
     (mnsG, cfsG) := coefficients(g, Monomials=>mons, Variables=>othervars);
     T := local T;
     Rt := ZZ/p[T];
     toRt := map(Rt, R, for f in gens R list if f == t then Rt_0 else 0_Rt);
     fromRt := map(R,Rt, {t});
     cfsF = flatten entries toRt cfsF;
     cfsG = flatten entries toRt cfsG;
     newcoeffs := for i from 0 to #cfsF - 1 list (
	  {fromRt first polyCRA(cfsF#i, cfsG#i, toRt m, toRt n)}
	  );
     ((mnsF * matrix newcoeffs)_(0,0), fromRt(toRt m* toRt n))
     )

rationalFunctionReconstruction = method()
rationalFunctionReconstruction(RingElement, RingElement) := (u,m) -> (
     -- expected: m and u are polynomials in 1 variable, over ZZ/p
     -- outputs: either null, or (a,b), where a,b are polynomials in the
     --  same ring as m, u and satisfy:
     --    (1) deg(a) + deg(b) < deg(m)
     --    (2) lc(b) = 1
     --    (3) gcd(a,b) = 1
     --    (4) gcd(b,m) = 1
     --    (5) a/b == u mod m
     R := ring m;
     M := first degree m;
     N := M//2;
     D := M-N-1;
     (r0,s0) := (m,0_R);
     (r1,s1) := (u,1_R);
     while first degree r1 > N do (
	  q := r0 // r1;
	  (r0,r1) = (r1,r0 - q * r1);
	  (s0,s1) = (s1,s0 - q * s1);
	  );
     (a,b) := (r1,s1);
     if first degree b > D-1 or gcd(b,m) != 1 then null
     else (
	  c := 1 / leadCoefficient(b);
	  (c*a, c*b)
	  )
     )

checkRatRecon = (F, u, ans) -> (
     if ans === null then return null;
     (numer,denom) := ans;
     -- we want to check that if a(t) := 1/denom (mod u)
     -- then F * a == numer mod u
     (g,a,b) := toSequence gcdCoefficients(denom, u);
     if g != 1 then error "check rat recon: gcd is not 1";
     rem := (F  - a*numer) % u;
     if rem != 0 then error ("remainder: "|toString rem);
     )

polyRationalReconstruction = method()
polyRationalReconstruction(RingElement, RingElement, RingElement, ZZ) := (F, t, mt, p) -> (
     -- F should be a poly in R = ZZ[vars]
     -- t is one of the vars
     -- mt is a poly in t, coeffs in ZZ, but mt is in R.
     -- output is (G, denom), G and denom are in ZZ[all vars], but denom only involves t.
     R := ring F;
     kk := ZZ/p;  -- or coefficientRing R?
     othervars := toList(set gens R - set{t});
     (mons, cfs) := coefficients(F, Variables=>othervars);
     T := local T;
     Rt := kk[T];
     toRt := map(Rt, R, for f in gens R list if f == t then Rt_0 else 0_Rt);
     fromRt := map(R,Rt, {t});
     cfs = flatten entries toRt cfs;
     newpairs := for i from 0 to #cfs - 1 list (
	  ans := rationalFunctionReconstruction(cfs#i, toRt mt);
	  checkRatRecon(cfs#i, toRt mt, ans);
	  if ans === null then return null;
	  ans);
     -- now find lcm of the denoms
     newdenom := newpairs/last//lcm;
     newnumers := apply(newpairs, (numer, denom) -> {(newdenom//denom) * numer});
     ((mons * fromRt matrix newnumers)_(0,0), fromRt newdenom)
     )

TEST ///
restart
load "ModularGCD.m2"
  RZZ = ZZ[a..d,s, MonomialOrder=>Lex]
  RK = frac RZZ
  F = (s^2+1) * a^3 - 12*(s+1)/s * a^2*b + (11*s^2-s-1)*a*b*c - 1/45 * s * c^3
  
  use RZZ
  f1 = reduceMod(numerator F, s, 5_RK, 11)
  f2 = reduceMod(numerator F, s, 6_RK, 11)
  f3 = reduceMod(numerator F, s, 7_RK, 11)
  f4 = reduceMod(numerator F, s, 8_RK, 11)

  (g,r) = polyCRA((f1,s-5), (f2,s-6), s, 11)
  (g,r) = polyCRA((f3,s-7), (g,r), s, 11)  
  (g,r) = polyCRA((f4,s-8), (g,r), s, 11)  

  polyRationalReconstruction(g,s,r,11)


  use RZZ
  f1 = reduceMod(F, s, 5_RK, 32003)
  f2 = reduceMod(F, s, 6_RK, 32003)
  f3 = reduceMod(F, s, 7_RK, 32003)
  f4 = reduceMod(F, s, 8_RK, 32003)
  f5 = reduceMod(F, s, 9_RK, 32003)

  (g,r) = polyCRA((f1,s-5), (f2,s-6), s, 32003)
  (g,r) = polyCRA((f3,s-7), (g,r), s, 32003)  
  (g,r) = polyCRA((f4,s-8), (g,r), s, 32003)  
  (g,r) = polyCRA((f5,s-9), (g,r), s, 32003)  

  polyRationalReconstruction(g,s,r,32003)
///


listPrimes = null

modularGCD = method()
modularGCD(RingElement, RingElement) := (F1', F2') -> (
     -- F1, F2 are in K[x], K of char 0, alg ext of QQ
     -- return the monic gcd G of F1 and F2.
     A := ring F1';
     extensionsR := (ideal A)_*;
     R := ring ideal A;
     RZZ := ZZ (monoid R);
     if listPrimes === null then listPrimes = select(reverse(30000..32767), i -> isPrime i);
     nextprime := 0;
     n := 0;
     fibonacci := (1,1);
     -- G is the currently reconstructed gcd
     -- G has been constructed mod m
     -- degG is the (univariate) degree of G
     (G,m,degG) := (null,null,null);
     -- Step 1: remove integer content of F, G
     (F1, content1) := primitiveAssociate lift(F1', R);
     (F2, content2) := primitiveAssociate lift(F2', R);
     -- Step 2: main loop:
     while true do (
	  P := listPrimes#nextprime;
	  nextprime = nextprime+1;
	  Rp := (ZZ/P)(monoid R);
	  toRp := map(Rp,R);
	  extensionsP := (toRp (ideal A))_*;
	  H := modpGCD(toRp F1, toRp F2,extensionsP);
	  if H === null then continue;
	  H = sub(H, RZZ);
	  d := first degree H;
	  if d === 0 then return 1_(ring F1');
	  if n == fibonacci#1 then (
	    -- the test means: n is the next fibonacci number
	    fibonacci = (fibonacci#1, plus fibonacci);
	    h := integerRationalReconstruction(G,m);
	    if h =!= null then (
		 -- we might be done:  we need to check div
		 -- (For Trager's alg, we can skip the expensive one of these)
		 return h;
--	         if reduceModM(h, P) == H and trialDivision(h,F1) and trialDivision(h,F2)
--		 then return h;
		 ));
	  if n == 0 or d < degG then (
	       G = H;
	       degG = d; -- is mod P
	       m = P;
	       n = 1;
	       )
	  else if d > degG then 
	       continue
	  else (
	       (G,m) = integerCRA((G,m),(H,P));
	       n = n+1;
	       );
	  );
     )
--*}


---------------------------------------------
newgcd = method()
newgcd1 = method()

newgcd1(RingElement, RingElement, RingElement, List) := (F,G, x, params) -> (
     -- F,G,x,elements of params, should all be in the same ring A.
     A := ring F; -- should be kk[t,x], or kk[x,t]...
     kk := coefficientRing A;
     B := kk[x];
     t := params#0;
     getPair := () -> (
     	  a1 := random kk;
     	  eval1 := map(B, A, {a1, B_0});
     	  f := eval1 F;
     	  g := eval1 G;
     	  h1 := modpGCD(f,g,{});
     	  (sub(h1,A), t-a1)
     	  );
     h := getPair();
     L := h;
     deg := degree(x, first L);
     n := 1;
     while true do (
	  h2 := getPair();
	  n = n+1;
	  deg2 := degree(x, first h2);
	  if deg2 > deg then continue;
	  if deg2 < deg then (
	       << "first choice was via a bad point.  Throwing out: " << L << endl;
	       L = h2;
	       deg = deg2;
	       continue;
	       );
	  (L1,mt1) := polyCRA(L, h2, t, char kk);
	  L = (L1,mt1);
	  ans := polyRationalReconstruction(L_0, t, L_1, char kk);
	  if ans =!= null then (
	       << "# evaluation points: " << n << endl;
	       return ans;
	       )
	  else (
	       --<< "try so far: " << L << endl;
	       );
	  )
     )

newgcd(RingElement, RingElement, RingElement, List) := (F,G, x, params) -> (
     -- F,G,x,elements of params, should all be in the same ring A.
     A := ring F; -- should be kk[t,x], or kk[x,t]...
     kk := coefficientRing A;
     B := kk[x];
     toB := map(B,A);
     if #params === 0 then (
	  -- at this point, we just call the basic function, and return
	  f := toB F;
	  g := toB G;
	  return modpGCD(f,g,{});
	  );
     t := params#0;
     others := drop(params,1);
     getPair := () -> (
     	  a1 := random kk;
     	  --eval1 := map(A, A, {a1, B_0});
	  eval1 := map(A, A, flatten{x=>x, apply(others, y -> y => y), t=>a1});
     	  f := eval1 F;
     	  g := eval1 G;
     	  h1 := newgcd(f,g,x,others);
	  h1 = sub(h1,A);
     	  (h1, t-a1)
     	  );
     h := getPair();
     L := h;
     deg := degree(x, first L);
     n := 1;
     while true do (
	  h2 := getPair();
	  n = n+1;
	  deg2 := degree(x, first h2);
	  if deg2 > deg then continue;
	  if deg2 < deg then (
	       << "first choice was via a bad point.  Throwing out: " << L << endl;
	       L = h2;
	       deg = deg2;
	       continue;
	       );
	  (L1,mt1) := polyCRA(L, h2, t, char kk);
	  L = (L1,mt1);
	  ans := polyRationalReconstruction(L_0, t, L_1, char kk);
	  if ans =!= null then (
	       << "# evaluation points: " << n << endl;
	       return ans#0;
	       )
	  else (
	       --<< "try so far: " << L << endl;
	       );
	  )
     )

TEST ///
-- ZZZZZZZZZZZ
restart
debug loadPackage "ModularGCD"
kk = ZZ/32003
K = frac(kk[t])
A = kk[t,x]
use K
R = K[x]
F = t^2*((t+2)*(x-1/t)^2*(x+t^2))
G = t^2*((t+2)*(x-1/t)*(x+1/t))

F = t^3*((t+2)*(x-1/t)^3*(x+t^2))
G = t^8*((t-2)*(x-1/t)^4*(x+1/t)^4)
F = sub(F,A)
G = sub(G,A)

use A
newgcd(F,G,x,{t})

A = kk[s,t,x]
F = ((t*s-2)^2*x^4-(s+t)^2*x-s^5)*(s*t*x-1)
G = ((t*s-2)^2*x^4-(s+t)^2*x-s^5)*(s*t*x+1)
newgcd(F,G,x,{t,s})
use A
(t*s-2)^2*x^4-(s+t)^2*x-s^5


F = ((t*s-2)^2*x^4-(s+t)^2*x-s^5)^3*(s*t*x+1)*(s^2*t*x-1)
G = ((t*s-2)^2*x^4-(s+t)^2*x-s^5)*(s*t*x+1)^3
newgcd(F,G,x,{t,s})
///
---------------------------------------------

balancedRemainder = (a,m) -> (
     b := a % m;
     mhalf := m//2;
     if b > mhalf then b - m
     else if b < -mhalf then b + m
     else b
     )

-- a/b mod m == (a*c mod m), where cb + dm = 1, or if (m,b) != 1, then return null.
-- TODO: should the final "%" be a balanced remainder?  I think yes!
rem = (a, m) -> (
     b := denominator a; 
     (g,c,d) := toSequence gcdCoefficients(b, m); 
     if g != 1 then 
       null 
     else balancedRemainder((numerator a) * c, m)
     )

-- reduceMod(F,m): returns null if any coefficient of F is not rel prime to m.
--  otherwise returns a polynomial over the integers.     
reduceMod1 = method()
reduceMod1(RingElement, ZZ) := (F, m) -> (
     -- F: a polynomial in a ring ZZ[x1,...] or QQ[x1,...]
     -- m: ZZ, a number to reduce by
     -- if any denominator of F is a zero divisor mod m, then null is returned.
     (mons, cfs) := coefficients F;
     reducedsCfs := (flatten entries sub(cfs, QQ))/(x -> rem(x,m));
     if any(reducedsCfs, x -> x === null) then null else
     (sub(mons, getZZRing ring F) * transpose matrix {reducedsCfs})_(0,0)
     )

-- Other operations desired here:
-- integerCRA
-- polynomialCRA (interpolation)
-- rationalFunctionReconstruction

TEST ///
XXXXXXXXXXX
restart
loadPackage "ModularGCD"
R = QQ[x,a,MonomialOrder=>Lex]/(a^2-3)
F = (x-a)*(x+a)
G = (x-a)^3
modularGCD(F,G)
///

TEST ///
restart
load "ModularGCD.m2"
  R=QQ[x_0..x_5];
  F = sum apply(flatten entries basis(2, R), m -> (random 1000)/(1 + random 100) * m)
  select(1..100, i -> isPrime(2^58+2*i+1))
  P1 = 2^58 + 2*34+1
  G = reduceMod(F, P1)
  assert(F == rationalReconstruction(G, P1))
  P2 = 101
  G = reduceMod(F, P2)
  rationalReconstruction(G, P2) -- needs to return an indication as to whether it succeeded
  G = reduceMod(F, P2^4)  
  rationalReconstruction(G, P2^4) -- needs to return an indication as to whether it succeeded
  F == oo 

  f1 = reduceMod(F, 101)
  f2 = reduceMod(F, 103)
  (g,m) = (integerCRA(f1,f2,101,103), 101*103)
  rationalReconstruction(g, m) == F
  (g,m) = (integerCRA(reduceMod(F, 107),g,107,m), m*107)
  rationalReconstruction(g, m)
  (g,m) = (integerCRA(reduceMod(F, 109),g,109,m), m*109)
  rationalReconstruction(g, m) == F -- true
///

TEST ///
restart
load "ModularGCD.m2"
kk = ZZ/11
R = kk[t]
F = frac R
phi = (t^2-t-1)/(t^4+1)
-- reconstruct phi from its values:
use R
(f1,m1) = (sub(phi, t_F=>1_R), t-1)
(f2,m2) = (sub(phi, t_F=>2_R), t-2)
(g1,h1) = polyCRA(f1,f2,m1,m2)
(f3,m3) = (sub(phi, t_F=>3_R), t-3)
(g1,h1) = polyCRA(g1,f3,h1,m3)
(f3,m3) = (sub(phi, t_F=>4_R), t-4)
(g1,h1) = polyCRA(g1,f3,h1,m3)
(f3,m3) = (sub(phi, t_F=>5_R), t-5)
(g1,h1) = polyCRA(g1,f3,h1,m3)
(f3,m3) = (sub(phi, t_F=>6_R), t-6)
(g1,h1) = polyCRA(g1,f3,h1,m3)
(f3,m3) = (sub(phi, t_F=>7_R), t-7)
(g1,h1) = polyCRA(g1,f3,h1,m3)
(f3,m3) = (sub(phi, t_F=>8_R), t-8)
(g1,h1) = polyCRA(g1,f3,h1,m3)
(f3,m3) = (sub(phi, t_F=>9_R), t-9)
(g1,h1) = polyCRA(g1,f3,h1,m3)
polyRationalReconstruction(g1,h1)
rationalFunctionReconstruction(g1,h1)
///

beginDocumentation()

end

doc ///
Key
  ModularGCD
Headline
Description
  Text
  Example
Caveat
SeeAlso
///

doc ///
Key
Headline
Usage
Inputs
Outputs
Consequences
Description
  Text
  Example
  Code
  Pre
Caveat
SeeAlso
///

TEST ///
-- test code and assertions here
-- may have as many TEST sections as needed
///
