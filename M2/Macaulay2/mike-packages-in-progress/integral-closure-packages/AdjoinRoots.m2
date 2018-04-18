newPackage(
        "AdjoinRoots",
        Version => "0.2", 
        Date => "30 Mar 2015",
        Authors => {{Name => "Mike Stillman", 
                  Email => "", 
                  HomePage => ""}},
        Headline => "Adjoining roots to fields",
        DebuggingMode => true
        )

export {
    "adjoinRoot",
    "switchCenter" -- this is an easier "helper" function
    }

isFinitePrimeField = method()
isFinitePrimeField Ring := (R) -> R.?order and R.order == char R

-- TODO: (14 March 2015 MES)
--   add tests:
--     base = ZZ/p
--     base = GF (might not work)
--     base = QQ
--     base = toField'd extension of QQ
--   get to work with tower rings too?
adjoinRoot = method(Options => {Variable=>null})
adjoinRoot RingElement := opts -> (f) -> (
    -- returns a root of the irreducible univariate polynomial f, 
    -- possibly after an extension of fields
    R := ring f;
    supp := support f;
    if #supp != 1 or numgens R =!= 1 then error "expected a univariate polynomial";
    x := supp#0;
    if degree(x,f) == 1 then (
        a := coefficient(x, f);
        b := coefficient(1_R, f);
        if a == 1 then -b else -b/a
        )
    else (
        -- Here we need to add a root to kk.
        kk := coefficientRing R;
        if opts.Variable =!= null and not instance(opts.Variable, Symbol) then
            error "Variable given is not a symbol";
        if not isPolynomialRing kk then (
            -- In this case, kk is QQ, or a finite prime field.
            -- (what about GF?)
            v := if opts.Variable === null then getSymbol "a"
            else opts.Variable;
            A1 := kk (monoid[v]);
            A2 := A1/(sub(f, x=> A1_0));
            A3 := if isFinitePrimeField kk then
                    GF(A2)
                  else
                    toField A2;
            A3_0
            )
      else (
            kk = coefficientRing kk;  -- we expect that kk is a 'toField'ed field
            I := ideal kk; -- this should be in a "triangular form"
            kk1 := coefficientRing kk;
            if instance(kk1, PolynomialRing) then error "expected the original ring in the form toField(kk[vars]/I), where kk is a prime field";
            n := numgens kk;
            v = if opts.Variable === null then vars n else opts.Variable;
            A1 = kk1[v, generators kk];
            to1 := map(A1, ring I, drop(gens A1, 1)); -- map on inner variables
            to2 := map(A1, R, gens A1);
            J := ideal to2 f + to1 I;
            A2 = A1/J;
            A3 = toField(A2);
            A3_0
            )
        )
    )

switchCenter = method()
switchCenter(Ring, RingElement) := (origR,gx) -> (
    -- origR should be a polynomial ring, over a field kk
    -- gx should be a polynomial, involving exactly one variable in x, possibly over the same ring.
    -- adjoin a root 'a' to kk if needed to get a new ring R1 = B (monoid origR), and
    -- then return inc : origR --> R, identity on the variables
    --        and  toNewRing : R --> R, x -> x+a, y -> y 
    --        and  toOld : R --> R  which sends x -> x-a, y -> y.
    kk := coefficientRing origR;
    supp := support gx;
    if #supp != 1 then error "expected center to be a polynomial involving one variable";
    x := supp#0;
    ix := index x;
    x1 := local x1;
    A := kk[x1];
    toA := map(A,origR, for v in gens origR list if v == x then A_0 else 0_A);
    gx1 := toA gx;
    a := adjoinRoot gx1;
    local R;
    if ring a === kk then (
        R = origR;
        )
    else (
        if not (ring a).?order then
            (ring a).order = (char kk)^(degree(x,gx));
        R = (ring a)(monoid origR)
        );
    vars := for i from 0 to numgens R - 1 list (
        if i == ix then R_i + a else R_i
        );
    vars2 := for i from 0 to numgens R - 1 list (
        if i == ix then R_i - a else R_i
        );
    inc := map(R,origR);
    toCenter := map(R,R,vars);
    fromCenter := map(R,R,vars2); 
    (inc,toCenter,fromCenter)
    )

TEST ///
{*
  restart
  loadPackage "AdjoinRoots"
*}
  A1 = ZZ/101
  B = A1[x]
  gx = x^2-2*x-14

  b = adjoinRoot(gx, Variable=>b)
  A2 = ring b
  B1 = A1[x,y]
  B2 = A2[x,y]
  inc = map(B2,B1)
  change = map(B2,B2,{x+b,y})
  change^-1
  use B1
  F = (y^6-x*y^4-x^3*y^2-1);
  G = sub(change^-1 change inc F, B1) -- what is a better way to lift to B1?
  assert(F == G)
  
  (inc,toA,fromA) = switchCenter(ring F, x+7)
  G = toA F
  factorize discriminant(G,y)
  G = inc F
  assert(fromA toA G == G)
///

TEST ///
  S = ZZ/2[y,x, MonomialOrder=>{1,1}]
  F = 27*x^11+27*x^4*y^3-9*x^5*y-27*x^4*y^2-
       27*y^6+27*x*y^4+81*y^5-9*x^2*y^2-54*x*y^3-
       81*y^4+x^3+9*x^2*y+27*x*y^2+27*y^3;
  factorize discriminant(F,y)
  (inc, toA, fromA) = switchCenter(S,x^3+x^2+1)
  F1 = toA inc F
  factorize discriminant(F1,(ring F1)_0)
///


beginDocumentation()

doc ///
Key
  AdjoinRoots
Headline
  package simplify adjoining roots of polynomials to fields
Description
  Text
  Example
Caveat
  Needs testing.
///

doc ///
   Key
       adjoinRoot
       (adjoinRoot,RingElement)
   Headline
       create a finite extension field
   Usage
       alpha = adjoinRoot(f, Variable=>a)
   Inputs
       f:RingElement
         A polynomial in a ring kk[x] in one variable over a field kk
   Outputs
       alpha:RingElement
         An element in the new ring which is a root of f
   Description
       Text
           Create a field kk[a]/f(a), and return the generator of this new field.
           
           The field kk may be QQ, ZZ/p, GF(p,n), or a field already constructed with adjoinRoot

           If f is linear, a new field is not created.
       Example
           k1 = ZZ/101;
           R = k1[x]
           f = x^3+x+1
           factor f -- f is irreducible
           alpha = adjoinRoot f
       Text
           Over QQ, it uses @TO "toField"@.
       Example
           R = QQ[t]
           F = t^2-3
           b = adjoinRoot(F, Variable=>symbol b)
           1//b
       Text
           kk = ring b
           ambient kk -- nothing useful!
           A = last kk.baseRings
           isField A
           1/A_0
   Caveat
       This doesn't yet work in all situations.  Also, it is not verified that
         f is irreducible
   SeeAlso
       switchCenter
       toField
///

doc ///
    Key
        switchCenter
        (switchCenter,Ring,RingElement)
    Headline
        switch center to a new point
    Usage
        (inc, toNew, toOld) = switchCenter(R, P)
    Inputs
        R:Ring
            a polynomial ring
        P:RingElement
            an irreducible polynomial in R, in one variable
    Outputs
        :Sequence
            A Sequence of three ring maps (inc, toNew, toOld), described below.
    Description
        Text
            A new ring S is created (unless P is a linear polynomial),
            which has the same variables as R, but the base field has
            been extended.
            
            The returned ring maps are:
            
             (1) inc: R --> S, the inclusion of fields,
            and an identity on the variables.
 
            The change of coordinates is done by toNew, fromNew:
                       
            (2) toNew: S --> S, satisfies toNew(x) == x+a
            
            (3) fromNew : S --> S, the inverse map, x --> x-a

        Example
            kk = ZZ/101
            R = kk[x,y]
            Px = x^2+x+1
            F = y^3-x
            (inc, toA, fromA) = switchCenter(R, Px)
            G = inc Px
            G1 = toA G
            G2 = fromA G1
            -- How to lift back to R?.  What is the best way?
            sub(G2,R)
    Caveat
        Only works with polynomial rings.  Bugs?  Maybe the coeff ring
          being a field is not checked?
    SeeAlso
        adjoinRoot
///

TEST ///
  -- adjoining a root over QQ
  -- once we have a 'toField', frac should return itself and / should just work.
  R = QQ[t]
  F = t^2-3
  b = adjoinRoot(F, Variable=>symbol b)
  kk = ring b
  assert(ring b === frac ring b)
  c = 1/b
  assert(c * b == 1)
  assert(ring c === ring b)
  assert(1//b == c)
  assert(1 % b == 0) -- all remainders like this in a field will be 0
  R = kk[x,y,z]
  G = (x+y+z)^2-3
  --factor G -- BUG: cannot factor!!
///

TEST ///
  -- adjoining a root of a linear polynomial over QQ
  R = QQ[t]
  F = 3*t-7
  b = adjoinRoot(F, Variable=>symbol b)
  kk = ring b
  assert(ring b === frac ring b)
  assert(ring b === QQ)
  c = 1/b
  assert(c * b == 1)
  assert(ring c === ring b)
///

TEST ///
  -- adjoining a root over ZZ/p
  R = ZZ/23[t]
  F = t^2-5
  isPrime F
  b = adjoinRoot(F, Variable=>symbol b) -- creates a Galois Field, but a BigFlint GF.  Is that OK?
  kk = ring b
  assert(ring b === frac ring b)
  c = 1/b
  assert(c * b == 1)
  assert(ring c === ring b)
  assert(1//b == c)
  assert(1 % b == 0) -- all remainders like this in a field will be 0
  -- Now we can use this as a base ring:
  R = kk[x,y,z]
  G = (x^(23^2) - x)
  factor G -- factors into linears
///

TEST ///
  F = conwayPolynomial(23,2)
  kk = coefficientRing ring F
  k1 = ring adjoinRoot F -- is a Flint ring
  R = kk[x]
  -- want the isomorphism between k1 and kk[x]/(x^2-5)
  -- how to get this?  The plan is to find a root of x^2-5 in this field.  Any will do
  R = k1[x]  
  last first factorize(x^2-5) -- so map x to -4+4a
  b = adjoinRoot(oo)
  phi = map(k1,kk[x]/(x^2-5),{b})
  ker phi
  coimage phi
///

TEST ///
  -- making a tower
  R = QQ[t]
  F = t^2-3
  a = adjoinRoot(F, Variable=>a)
  R1 = (ring a)[t]
  b = adjoinRoot(t^2-a, Variable=>b)
  kk = ring b
  assert(ring b === frac ring b)
  c = 1/b
  assert(c * b == 1)
  assert(ring c === ring b)
  assert(1//b == c)
  assert(1 % b == 0) -- all remainders like this in a field will be 0
  R = kk[x,y,z]
  G = (x+y+z)^2-3
  R2 = (ring b)[t]
  --factor G -- BUG: cannot factor!!
  d = adjoinRoot(a*t-b)
  R2 = (ring b)[t]
  use ring b
  c = adjoinRoot(t^3-a*t-b, Variable=>symbol c)
  ring c
  1/c
  assert((c-3) * 1/(c-3) == 1)
///

end

restart
loadPackage "AdjoinRoots"
uninstallPackage "AdjoinRoots"
restart
installPackage "AdjoinRoots"
check "AdjoinRoots"
viewHelp "AdjoinRoots"
