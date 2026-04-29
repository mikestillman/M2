newPackage(
    "IntegralClosure2",
    Version => "1.10", 
    Date => "31 Dec 2020",
    Authors => {
        {Name => "David Eisenbud", Email => "de@msri.org", HomePage => "http://www.msri.org/~de/"},
        {Name => "Mike Stillman", Email => "mike@math.cornell.edu", HomePage => "https://mikestillman.github.io"},
        {Name => "Amelia Taylor", Email => "originalbrickhouse@gmail.com"}
        },
    Headline => "integral closure",
    Keywords => {"Commutative Algebra"},
    PackageImports => {
        "PrimaryDecomposition",  -- only used for an obscure "rad" function
        "ReesAlgebra" -- used for integral closure of an ideal
        },
    PackageExports => {
        "Fields",
        "MinimalPrimes", -- really helps speed up most computations here. Use minprimes.
        "PushForward"
        },
    DebuggingMode => false,
    AuxiliaryFiles => true
    )

importFrom_Core { "generatorSymbols" } -- use as R#generatorSymbols.
importFrom_MinimalPrimes { "rad" } -- a function we seem to be using in integralClosure.

export{
    -- code over ZZ
     "badPrimes",
     "contractOverZZ",
     "radicalOverZZ",
     "decomposeOverZZ",
     "OverZZ",
    -- methods
     "integralClosure",
     "icDenominator",
     "icFractions", 
     "icMap", 
     "conductor", 
     "makeS2",
     "canonicalIdeal",
     "idealizer", 
     "ringFromFractions",
     "findConductorInSubring",
     "fractionsSpecificDenominator",
     "showFraction",
     "showFractions",
     -- small characteristic method
     "icFracP", 
     "icPIdeal",
     --mes--"extendIdeal",
     -- "testHunekeQuestion", -- MES remove or make hidden?
     -- optional argument names
     "Keep",
     "Index",
     "ConductorElement",
     "Denominator",
     "AllCodimensions",
     "RadicalCodim1",
     "Radical",
     "StartWithOneMinor",
     "SimplifyFractions",
     "Vasconcelos"
     } 

----------- below: radicals, minimal primes over ZZ ----------------------
-- to be placed elsewhere later (e.g. in MinimalPrimes package).
badPrimes = method()
badPrimes Ideal := (IZ) -> (
    -- assumption: I is an ideal in a flattened polynomial ring over ZZ.
    R := ring IZ;
    if coefficientRing R =!= ZZ then error "expected ideal in a flattened polynomial ring over ZZ";
    ltI := leadTerm gb IZ;
    badP := for f in flatten entries ltI list leadCoefficient f;
    -- now we find all primes which divide lcm badP;
    badprimes := sort unique flatten for a in badP list (
        if a < 0 then a = -a;
        facs := (factor a)//toList/toList;
        facs/first);
    badprimes
    )

contractOverZZ = method()
contractOverZZ(Ideal, Ring) := Ideal => (IQQ, RZ) -> (
    -- remove all denominators, lift to RZ, find badprimes, saturate (over ZZ)
    liftBack := map(RZ, ring IQQ, vars RZ);
    Ilift := ideal for f in IQQ_* list (
        g := (terms f)/leadCoefficient//gcd;
        liftBack(1/g * f)
        );
    badprimes := badPrimes Ilift;
    saturate(Ilift, product badprimes)
    )

-- need:
-- (a) given I in R = ZZ[x], find h = product of primes in ZZ s.t. I QQ[x] \cap ZZ[x] = saturate(I, h).
-- (b) given J in R = QQ[x], find J \cap ZZ[x] ( = saturate(I,h), all gens over ZZ, lifted to ZZ[x]).

-- TODO: not tested over unflattened rings, or quotient rings.  Actually, only one test has been done!
decomposeOverZZ = (opts, I) -> (
    R := ring I;
    if not isCommutative R then return null;
    if not (instance(R, PolynomialRing) or instance(R, QuotientRing))
      then return null;
    if coefficientRing R =!= ZZ then return null;
    (S, F) := flattenRing R;
    IZ := F I;
    badprimes := badPrimes IZ;
    RQ := QQ (monoid R);
    IQQ := (map(RQ, R)) I;
    comps0 := for comp in decompose IQQ list contractOverZZ(comp, R);
    finitecomps := flatten for p in badprimes list (
        Sp := (ZZ/p)(monoid S);
        Ip := (map(Sp, S, vars Sp)) I;
        compsIp := decompose Ip;
        for C in compsIp list (ideal p_S) + sub(C, S)
        );
    -- now we can remove any component of finitecomps, which contains any component of comps0
    -- these are the only redunduncies that can occur
    finitecompsMinimal := for c in finitecomps list (
        if any(comps0, c0 -> isSubset(c0, c)) then continue else c
        );
    answer := join(comps0, finitecompsMinimal);
    answer
    )
addHook((minimalPrimes, Ideal), decomposeOverZZ, Strategy => OverZZ);

radicalOverZZ = (opts, I) -> (
    ret := decomposeOverZZ(opts, I);
    if ret === null then return null; -- this should happen quickly.
    intersect ret)
addHook((radical, Ideal), radicalOverZZ, Strategy => OverZZ);

"TEST"  -- radical over ZZ, in progress 3/22/26
/// 
-*
  restart
  needsPackage "IntegralClosure2"
*-
  S = ZZ[x,y,z]
  I = ideal(x^6-z^6-y^2*z^4)
  singI = I + ideal jacobian I
  badPrimes singI
decompose singI
R = S/I
integralClosure R -- fails on codim
use S
  assert(radical singI == ideal(6*z,6*x,2*y*z,2*x*y,2*x^2-2*z^2,x^3+2*x*z^2+y*z^2+3*z^3))
  -- this next test is not good: the ideals could come in any order, with different generators.
  assert(minimalPrimes singI === {ideal(z,x), ideal(2,x^3+y*z^2+z^3), ideal(3,y,x-z), ideal(3,y,x+z)})

  -- remove after this?
  gens gb singI
  -- bad primes: 2,3.
  I1 = saturate(singI, 6)
  singI : 6 == I1
  singI : 36 == I1
  isSubset(6 * I1, singI)
  isSubset(36 * I1, singI)

  I2 = trim(ideal 6 + singI)
  I21 = I2 : 2
  I2 : 2 == I2 : 4 -- true
  I2 == intersect(I21, I2 + ideal(2)) -- true
  I22 = trim(ideal 2 + I2)

  SQ = QQ (monoid S)
  S2 = (ZZ/2) (monoid S)
  S3 = (ZZ/3) (monoid S)
  
  decompose sub(I21, S3) -- {ideal (z, x), ideal (y, x - z), ideal (y, x + z)}
  decompose sub(I22, S2) -- {ideal(x^3+y*z^2+z^3)}
  decompose sub(I1, SQ) -- {ideal (z, x)}
  singIrad = intersect(ideal(x,z), ideal(2, x^3+y*z^2+z^3), ideal(3, y, x-z), ideal(3, y, x+z))
  -- this should be the radical of singI!

  (gens singIrad) % singI
  (gens singIrad^2) % singI
  (gens singIrad^3) % singI  

  (6*z)^6 % singI
  singIrad
  ((6*z)^6*singIrad) : singIrad

  IsingQ = sub(singI, SQ)
  Ising2 = sub(singI, S2)
  Ising3 = sub(singI, S3)
  decompose IsingQ
  decompose Ising2
  decompose Ising3
  
///
----------- above: radicals, minimal primes over ZZ ----------------------

 
makeVariable = opts -> (
     s := opts.Variable;
     if instance(s,Symbol) then s else
     if instance(s,String) then getSymbol s else
     error "expected Variable option to provide a string or a symbol"
     )

integralClosure = method(Options=>{
        Variable => "w",
        Limit => infinity,
        Strategy => {}, -- a mix of certain symbols
        Verbosity => 0,
        --mes--Denominator => null, -- if given, should be a nonzero divisor in Jacobian ideal of the ring.
        Keep => null -- list of variables to not simplify away.  Default is all original vars
        }
    )

idealInSingLocus = method(Options => {
	Verbosity => 0,
	Strategy => {}
	})

--3/4/26: make this work in char p small: need an elt of the radical of the conductor
--(== non-normal locus) -look
idealInSingLocus Ring := Ideal => opts -> S -> (
     -- Input: ring S = S'/I, where S' is a flattened poly ring.
     --  Verbosity: if >0 display timing
     --  Strategy: List. If isMember(StartWithOneMinor, opts.Strategy) then 
     -- Output:
     --        ideal in non-normal locus
     -- private subroutine of integralClosure

     if opts.Verbosity >= 1 then (
	  << " [jacobian time " << flush;
	  );
     if member(StartWithOneMinor, opts.Strategy) then 
          t1 := timing (J := ideal nonzeroMinor(codim ideal S, jacobian S))
     else
          t1 = timing (J = minors(codim ideal S, jacobian S));

     if opts.Verbosity >= 1 then (
        << t1#0 << " sec #minors " << numgens J << "]" << endl;
	);
     J
     )

integralClosure(Ring, Ring) := Ring => o -> (B,A) -> (
    (fB,fromB) := flattenRing B;
    fC := integralClosure(fB, o);
    if fB === fC and coefficientRing B === A then return B;
    gensA := generators(A, CoefficientRing => ZZ);
    newvars := drop(gens ambient fC, - #gensA);
    newdegs := drop(degrees ambient fC, - #gensA);
    aC := A (monoid[newvars, Degrees => newdegs, Join => false]);
    L := trim sub(ideal fC, aC);
    C := aC/L;
    B.icFractions = fB.icFractions;
    fCtoC := map(C, fC, gens(C, CoefficientRing => coefficientRing fC));
    B.icMap = fCtoC * fB.icMap * fromB;
    C
    )

integralClosure Ring := Ring => opts -> (R) -> (
     -- R: Ring, a reduced affine ring. TODO: can we handle integral closures over ZZ as well?
     --   answer: if we choose J in the non-normal ideal some other way?
     if R.?icMap then return target R.icMap;
     verbosity := opts.Verbosity;

     strategies := if instance(opts.Strategy, Symbol) then {opts.Strategy} else opts.Strategy;
     strategyList := {AllCodimensions, RadicalCodim1, Radical, 
             StartWithOneMinor, SimplifyFractions, Vasconcelos};
     if not isSubset(strategies, strategyList) then
       error("expected Strategy option to be either an element of, or a list containing some of, "|toString strategyList);
     if #((set strategies) * set {AllCodimensions, RadicalCodim1, Radical}) >= 2 then
       error " expected Strategy option to include at most one of AllCodimensions, Radical, Radical";

     if ultimate(coefficientRing, R) =!= coefficientRing R
     then return integralClosure(R, coefficientRing R, opts);

     (S,F) := flattenRing R;
     flattenMap := F;

     -- right here, we will grab the variables to be excluded
     -- this seems a bit awkward, perhaps there is a better way?
     T := ambient S;
     kk := ultimate(coefficientRing,T);
     allgens := generators(T, CoefficientRing => kk);
     --keepvars := opts.Keep; -- TODO MES: bug? these will not be in the correct ring, bring them over?
     keepvars := null;
       -- TODO MES: check that opts.Keep contains a list of variables in the ring R?
     if keepvars === null then keepvars = allgens;

     P := ideal S;
     startingCodim := codim P;
     isCompleteIntersection := (startingCodim == numgens P);
     --G := map(frac R, frac S, substitute(F^-1 vars S, frac R));

     isS2 := isCompleteIntersection; -- true means is, false means 'do not know'
     nsteps := 0;
     t1 := null;  -- used for timings
     --3/4/26: if  homogeneous, checking Cohen-Macaulay with res might avoid some S2 comps.
     
     allCodimensionsNotPresent := not member(AllCodimensions, strategies);
     codim1only := not member(AllCodimensions, strategies);
       -- this means: don't bother to compute the S2-ification
       -- and don't try to take only the codim 1 part of the radical
       -- of the jacobian locus.
       
     ------------------------------------------
     -- Step 1: Find ideal in singular locus --
     ------------------------------------------     
     -- other possible things here: make a list of ideals, and we 
     --   will compute End of each in turn.
     --   (b) use discriminant
     J := idealInSingLocus(S, Verbosity => verbosity, Strategy => strategies); 
        -- returns ideal in non-normal locus S
     codimJ := codim J;
     isR1 := (codimJ > 1);

     if verbosity >= 1 then (
     	  << "integral closure nvars " << numgens S;
	  << " numgens " << numgens ideal S;
	  if isS2 then << " is S2";
	  if isR1 then << " is R1";
	  << " codim " << startingCodim;
	  << " codimJ " << startingCodim + codimJ << endl;
       << endl;
       );

     radJ := radical J;
     if radJ == 1 then (
         isR1 = true;
         );

     -- denom := null; --mes--opts.Denominator; -- either null (means for the routine to find a possible denominator),
     -- or a nzd in the radical of the ideal J.
     denom := findSmallGen radJ;
     R.icDenominator = flattenMap^(-1) denom;
   
     ------------------------------
     -- Step 2: make the ring S2 --
     ------------------------------
     --  unless we are using an option that
     --  doesn't require it.
     if not isS2 and allCodimensionsNotPresent then (
         if verbosity >= 1 then 
         << "   S2-ification " << flush;
         t1 = (timing F' := makeS2(target F,Variable=>makeVariable opts,Verbosity=>verbosity));
         nsteps = nsteps + 1;
         if verbosity >= 1 then
             << t1#0 << " seconds" << endl;
	 if F' === null then (
             << "warning: probabilistic computation of S2-ification failed " << endl;
             << "         reverting to standard algorithm" << endl;
             strategies =  append(strategies, AllCodimensions);
             codim1only = false
	 ) else (
             F = F'*F;
	     -- also extend J to be in this ring
	     J = trim(F' J);
             denom = F' denom;
	     isS2 = true;
	     )
         );

     
     -------------------------------------------
     -- Step 3: incrementally add to the ring --
     -------------------------------------------

     
     F0 := null; -- is set below.
     if not isR1 or not codim1only then (     
     -- loop (note: F : R --> Rn, G : frac Rn --> frac R)
     while (
	  R1 := target F;

	  if verbosity >= 1 then << " [step " << nsteps << ": " << flush;

          t1 = timing((F0,J,denom) = integralClosure1(R1,J,denom,nsteps,makeVariable opts,keepvars,strategies,verbosity));

          --if nsteps == 6 then error "debug me in IntegralClosure";
          
          F = F0 * F;
          -- if verbosity >= 1 then (
	  --        if verbosity >= 5 then (
	  --             << "  time " << t1#0<< " sec  fractions " << first entries G.matrix << "]" << endl << endl;
	  --             )
	  --        else (
	  --             << "  time " << t1#0<< " sec  #fractions " << numColumns G.matrix << "]" << endl;
	  --             );
	  --        );

	  nsteps = nsteps + 1;
	  nsteps < opts.Limit and target F0 =!= source F0
	  ) do (
	  ));
     R.icMap = F;
     target R.icMap
     )

doingMinimalization = true;

--the following finds an element in the intersection of the
--principal ideals generated by the ring elements in a list.
commonDenom = X -> findSmallGen intersect(apply (X, x->ideal x));

-- integralClosure1: the iterative step in the integral closure algorithm.
-- Some rings appearing here:
--     R is an affine  domain, the original ring for which we are computing the integral closure
--     R0 is a partial normalization.
-- Inputs:
--     F:RingMap, F : R -> R0, R0 is assumed to be a domain
--     G:RingMap  G : frac R0 --> frac R (really, the list of fractions).
--     J:Ideal, an ideal in the non-normal ideal of R0
--     denom: either null, or, a RingElement, a nonzero-divisor in R0, in the radical of J.
--        if null, this function will choose an element of this radical.
--     nsteps:ZZ
--     varname:Symbol
--     keepvars:List of variables to keep (where are these variables?) if/when we prune the ring.
--     strategies:List of elements from:
--       AllCodimensions
--       SimplifyFractions
--       doingMinimalization (always true, can't give this: it is currently a local variable set to true).
-- Outputs:
--     F1:RingMap, F1 : R --> R1, R1 is a (potentially) larger partial normalization.
--     J1:Ideal, J1 = radJ R1, the extension of the radical of J to R1.
--     denom1: either null, if denom===null, or 'denom' in the ring R1.
-- Features of the output:
--     The ring R0 is integrally closed (normal) iff R0 === R1.
--     New variables in the ring R1 will be named varname_(nsteps, 0), varnames_(nsteps, 1), ...

integralClosure1 = (R0, J, denom, nsteps, varname, keepvars, strategies, verbosity) -> (
     codim1only := not member(AllCodimensions, strategies);

     if ring J =!= R0 then error "expected ideal in given ring";
     --J = trim J; -- this seems bad sometimes...
     radJ := radical J;
     if radJ == 1 then return (id_R0,ideal(1_R0),denom);

     f := if denom === null then findSmallGen radJ else denom; -- we assume that f is a non-zero divisor!!

     << "denominator used for Hom is: " << toString f << endl;
     -- Compute Hom_R0(radJ,radJ), using f as the common denominator.

     
     
     if verbosity >= 3 then <<"      small gen of radJ: " << f << endl << endl;
     if verbosity >= 6 then << "rad J: " << netList flatten entries gens radJ << endl;
     if verbosity >= 2 then <<"      idlizer1:  " << flush;

     t1 := timing((He,fe) := endomorphisms(radJ,f));

     if verbosity >= 2 then << t1#0 << " seconds" << endl;
     if verbosity >= 6 then << "endomorphisms returns: " << netList flatten entries He << endl;

     --TODO: make verbosity into Verbosity, a passed option
     
     if He == 0 then (
	  -- there are no new fractions to add, and this process will add no new fractions
	  return (id_R0,radJ,denom);
	  );

     if verbosity >= 6 then (
	  << "        about to add fractions" << endl;
          -- << "        " << apply(flatten entries He, g -> G(g/f)) << endl;
	  );

     if verbosity >= 2 then <<"      idlizer2:  " << flush;

     t1 = timing(F0 := ringFromFractions(He, fe, Variable=>varname, Index=>nsteps));

     --if nsteps == 6 then error "debug me";
     
     if verbosity >= 2 then << t1#0 << " seconds" << endl;
     
     -- These would be correct, except that we want to clean up the
     -- presentation
     R1temp := target F0;
     if R1temp === R0 then return(id_R0, radJ,denom);

     if verbosity >= 2 then << "      minpres:   " << flush;
     R1tempAmbient := ambient R1temp;
     keepindices := apply(keepvars, x -> index substitute(x, R1tempAmbient));
     t1 = timing(R1 := minimalPresentation(R1temp, Exclude => keepindices));
     if verbosity >= 2 then << t1#0 << " seconds" << endl;
     i := R1temp.minimalPresentationMap; -- R1temp --> R1
     -- iinv := R1temp.minimalPresentationMapInv.matrix; -- R1 --> R1temp
     --   iinvfrac := map(frac R1temp , frac R1, substitute(iinv,frac R1temp));
       -- We also want to trim the ring     
       F0' := i*F0; -- R0 --> R1

       if denom === null then
          (F0', F0' radJ, null) -- 3/21/26: TODO: replace null with the actual denominator used?
       else
          (F0', F0' radJ, F0' denom)
    )

---------------------------------------------------
-- Support routines, perhaps should be elsewhere --
---------------------------------------------------

randomMinors = method()
randomMinors(ZZ,ZZ,Matrix) := (n,d,M) -> (
     --produces a list of n distinct randomly chosend d x d minors of M
     r := numrows M;
     c := numcols M;
     if d > min(r,c) then return null;
     if n >= binomial(r,d) * binomial(c,d)
	then return (minors(d,M))_*;
     L := {}; -- L will be a list of minors, specified by the pair of lists "rows" and "cols"
     dets := {}; -- the list of determinants taken so far
     rowlist := toList(0..r-1);
     collist := toList(0..c-1);
     ds := toList(0..d-1);

     for i from 1 to n do (
      -- choose a random set of rows and of columns, add it to L 
      -- only if it doesn't appear already. When a pair is added to L, 
      -- the corresponding minor is added to "dets"
       while ( 
         rows := sort (random rowlist)_ds ;
         cols := sort (random collist)_ds ;
         for p in L do (if (rows,cols) == p then break true);
         false)
        do();
       L = L|{(rows,cols)};
       dets = dets | {det (M^rows_cols)}
       );
     dets
     )

nonzeroMinor = method(Options => {Limit => 100})
nonzeroMinor(ZZ,Matrix) :=  opts -> (d,M) -> (
     --produces one d x d nonzero minor, making up to 100 random tries.
     r := numrows M;
     c := numcols M;
     if d > min(r,c) then return null;
     candidate := 0_(ring M);
     rowlist := toList(0..r-1);
     collist := toList(0..c-1);
     ds := toList(0..d-1);
     for i from 1 to opts.Limit do(
      -- choose a random set of rows and of columns, test the determinant.
         rows := sort (random rowlist)_ds ;
         cols := sort (random collist)_ds ;
         candidate = det (M^rows_cols);
	 if candidate != 0 then return(candidate);
       );
     error("no nonzero minors found");
     )

-------------------------------------------
-- Rings of fractions, finding fractions --
-------------------------------------------
findSmallGen = (J) -> (
     a := toList((numgens ring J):1);
     L := sort apply(J_*, f -> ((weightRange(a,f))_1, size f, f));
     --<< "first choices are " << netList take(L,3) << endl;
--     << "ideal: " << toString J << endl;
     L#0#2
     )

idealizer = method(Options=>{
        Variable => "w", 
        Index => 0, 
        Strategy => {},
        Verbosity => 0
        }
    )

idealizer (Ideal, RingElement) := opts -> (J, g) ->  (
     -- J is an ideal in a ring R containing a nonzerodivisor
     -- g is a nonzero divisor in J
     -- compute R1 = Hom(J,J) = (g*J:J)/g (default, Strategy => {})
     --   or computes R1 = Hom(J^-1, J^-1), where J^-1 = Hom_R(J,R) (Strategy => {Vasconcelos})
     -- returns a RingMap F, where 
     --   F : R --> R1 is the natural inclusion
     -- Optional arguments:
     --   opts.Variable: base name for new variables added
     --   opts.Index: the first subscript to use for such variables
     R := ring J;

     (H, f) := if member(Vasconcelos, opts.Strategy) then (
                    vasconcelos (J,g))
                 else 
                    endomorphisms (J,g);
     
     if opts.Verbosity >= 5 then << "endomorphism fractions:" << netList prepend(f,flatten entries H) << endl;
     if H == 0 then 
         id_R -- in this case R is isomorphic to Hom(J,J)
     else 
         ringFromFractions(H, f, Variable=>makeVariable opts, Index=>opts.Index, Verbosity => opts.Verbosity)
     )

-- private function for `idealizer`
endomorphisms = method()
endomorphisms(Ideal,RingElement) := (I,f) -> (
     --computes generators in frac ring I of
     --Hom(I,I)
     --assumes that f is a nonzerodivisor in I.
     --returns the answer as a sequence (H,f) where
     --H is a matrix of numerators
     --f = is the denominator.
     if not fInIdeal(f,I) then error "Proposed denominator was not in the ideal.";
     timing(H1 := (f*I):I);
     H := compress ((gens H1) % f);
     (H,f)
     )

-- private function for `idealizer`
vasconcelos = method()
vasconcelos(Ideal,RingElement) := (I,f) -> (
     --computes generators in frac ring I of
     --(I^(-1)*I)^(-1) = Hom(I*I^-1, I*I^-1),
     --which is in general a larger ring than Hom(I,I)
     --(though in a 1-dim local ring, with a radical ideal I = mm,
     --they are the same.)
     --assumes that f is a nonzerodivisor (not necessarily in the conductor).
     --returns the answer as a sequence (H,f) where
     --H is a matrix of numerators
     --f  is the denominator. MUST BE AN ELEMENT OF I.
     if f%I != 0 then error "Proposed denominator was not in the ideal.";
     m := presentation module I;
     timing(n := syz transpose m);
     J := trim ideal flatten entries n;
     timing(H1 := ideal(f):J);
     H := compress ((gens H1) % f);
     (H,f)
     )

ringFromFractions = method(Options=>{
	  Variable => "w", 
	  Index => 0,
	  Verbosity => 0})
ringFromFractions (Matrix, RingElement) := RingMap => opts -> (H, f) ->  (
    -- f is a nonzero divisor in R
    -- H is a (row) matrix of numerators, elements of R
    -- Forms the ring R1 = R[H_0/f, H_1/f, ..].
    -- returns a ring map F, where 
    --   F : R --> R1 is the natural inclusion
    -- Optional arguments:
    --   opts.Variable: base name for new variables added, defaults to w
    --   opts.Index: the first subscript to use for such variables, defaults to 0
    --   so in the default case, the new variables produced are w_(0,0), w_(0,1)...
    -- ASSUMPTIONS:
    --   a. H/f = Hom(I,I), for some ideal in R.
    --   b. R is presented as a flattened ring: kk[vars]/ideal, where kk is the base field.
    isgraded := isHomogeneous H and isHomogeneous f;
    R := ring H;
    Hf := H | matrix{{f}};
    -- Make the new polynomial ring.
    -- This section avoids creating degree zero variables.
    n := numgens source H;
    newdegs := degrees source H - toList(n:degree f);
    if not isgraded and #newdegs#0 === 1 and any(newdegs, i -> i == {0})
    then newdegs = for d in newdegs list if first d > 0 then d else {1};
    degs := join(newdegs, (monoid R).Options.Degrees);
    -- 
    MO := prepend(GRevLex => n, (monoid R).Options.MonomialOrder);
    kk := coefficientRing R;
    var := makeVariable opts; -- TODO 3/20/26: use variable iterators?
    A := kk(monoid [var_(opts.Index,0)..var_(opts.Index,n-1), R#generatorSymbols, -- 3/20/26: could use `gens ambient R`.
            MonomialOrder=>MO, Degrees => degs]);
    I := ideal presentation R;
    IA := ideal ((map(A,ring I,(vars A)_{n..numgens R + n-1})) (generators I));
    B := A/IA; -- this is sometimes a slow op

    -- Make the linear and quadratic relations
    varsB := (vars B)_{0..n-1};
    RtoB := map(B, R, (vars B)_{n..numgens R + n - 1});
    XX := varsB | matrix{{1_B}};
    -- Linear relations in the new variables
    lins := XX * RtoB syz Hf; 
    -- linear equations(in new variables) in the ideal
    -- Quadratic relations in the new variables
    tails := (symmetricPower(2,H) // f) // Hf;
    --3/4/26: if Hom(I,I) = R[a/f,1] then a^2/f^2 = c(a/f)+d, so a^2 = caf+df^2;
    --so (symmetricPower(2,H) // f)  = ca+df, and ca+df //Hf = (c,d).
    tails = RtoB tails;
    quads := matrix(B, entries (symmetricPower(2,varsB) - XX * tails));
    both := ideal lins + ideal quads;
	  
    gb both; -- sometimes slow
    Bflat := flattenRing (B/both); --sometimes very slow
    R1 := trim Bflat_0; -- sometimes slow

    -- Now construct the return value
    F := map(R1, R, (vars R1)_{n..numgens R + n - 1});
    F
    )

fInIdeal = (f,I) -> (
     -- << "warning: fix fInIdeal" << endl;
     if isHomogeneous I -- really want to say: is the ring local?
       then f%I == 0
       else substitute(I:f, ultimate(coefficientRing, ring I)) != 0
     )


-- PURPOSE: check if an affine domain is normal.  
-- INPUT: any quotient ring.  
-- OUTPUT:  true if the ring is normal and false otherwise. 
-- COMMENT: This computes the jacobian of the ring which can be expensive.  
-- However, it first checks the less expensive S2 condition and then 
-- checks R1.  

--isNormal = method()     
isNormal(Ring) := Boolean => (R) -> (
     -- 1 argument:  A ring - usually a quotient ring. 
     -- Return: A boolean value, true if the ring is normal and false
     -- otherwise. 
     -- Method:  Check if the Jacobian ideal of R has
     -- codim >= 2, if true then check the codimension 
     -- of Ext^i(S/I,S) where R = S/I and i>codim I. If 
     -- the codimensions are >= i+2 then return true.
     I := ideal (R);
     M := cokernel generators I;
     n := codim I;         
     test := apply((dim ring I)-n-1,i->i);
     if all(test, j -> (codim Ext^(j+n+1)(M,ring M)) >= j+n+3) 
     then ( 
	  Jac := minors(n,jacobian R);
	  d := dim Jac;
	  if d < 0 then d = -infinity;
	  dim R - d >=2)
     else false
     )

--------------------------------------------------------------------
conductor = method()
conductor RingMap := Ideal => phi -> (
    -- 3/25/26 TODO: do we want to cache the results?
    pf := pushFwd phi;
    assert(pf#1_(0,0) == 1);
    pmod := pf_0_{0};
    ann coker pmod
    )
conductor Ring := Ideal => R -> conductor icMap R

icMap = method()
icMap Ring := RingMap => R -> R.icMap ??= (
    -- 1 argument: a ring.  May be a quotient ring, or a tower ring.
    -- Returns: The map from R to the integral closure of R.  
    -- Note:  This is a map where the target is finitely generated as
    -- a module over the source, so it can be used as the input to
    -- conductor and other methods that require this. 
    R' := integralClosure R;
    R.icMap
    )

--------------------------------------------------------------------
icFractions = method(Options => {
        Denominator => null, -- if not null, should be a ring element in the radical of the conductor
        Module => false} -- if true, all module generators, otherwise all ring generators.
    )
icFractions Ring := List => opts -> R -> (
    f := icMap R;
    denom := opts.Denominator ?? R.icDenominator;
    if opts.Denominator === null then
        icFractions(f, Denominator => R.icDenominator, Module => opts#Module)
    else
        icFractions(f, opts)
    )

--------------------------------------------------------------------

icFracP = method(Options=>{ConductorElement => null, Limit => infinity, Verbosity => 0})
icFracP Ring := List => o -> (R) -> (
     -- 1 argument: a ring whose base field has characteristic p.
     -- Returns: Fractions
     -- MES:
     --  ideal presentation R ==== ideal R
     --  does not seem to handle towers
     --  this ring in the next line can't really be ZZ?
     if ring ideal presentation R === ZZ then (
	  D := 1_R;
	  U := ideal(D);
	  if o.Verbosity > 0 then print ("Number of steps: " | toString 0 | ",  Conductor Element: " | toString 1_R);
	  )    
     else if coefficientRing(R) === ZZ or coefficientRing(R) === QQ then error("Expected coefficient ring to be a finite field")
     else(
	  if o.ConductorElement === null then (
     	       P := ideal presentation R;
     	       c := codim P;
     	       S := ring P;
	       J := promote(jacobian P,R);
	       n := 1;
	       det1 := ideal(0_R);
	       while det1 == ideal(0_R) do (
		    det1 = minors(c, J, Limit => n);
		    n = n+1
		    );
	       D = det1_0;
	       D = (mingens(ideal(D)))_(0,0);
	       )
     	  else D = o.ConductorElement;
     	  p := char(R);
     	  K := ideal(1_R);
     	  U = ideal(0_R);
     	  F := apply(generators R, i-> i^p);
     	  n = 1;
     	  while (U != K) do (
	       U = K;
	       L := U*ideal(D^(p-1));
	       f := map(R/L,R,F);
	       K = intersect(kernel f, U);
	       if (o.Limit < infinity) then (
	       	    if (n >= o.Limit) then U = K;
	       	    );
               n = n+1;
     	       );
     	  if o.Verbosity > 0 then print ("Number of steps: " | toString n | ",  Conductor Element: " | toString D);
     	  );
     U = mingens U;
     if numColumns U == 0 then {1_R}
     else apply(numColumns U, i-> U_(0,i)/D)
     )

icPIdeal = method()
icPIdeal (RingElement, RingElement, ZZ) := Ideal => (a, D, N) -> (
     -- 3 arguments: An element in a ring of characteristic P that
     -- generates the principal ideal we are interested in, a
     -- non-zerodivisor of $ in the conductor, and the number of steps
     -- in icFracP to compute the integral closure of R using the
     -- conductor element given.  
     -- Returns: the integral closure of the ideal generated by the
     -- first argument.  
     n := 1;
     R := ring a;
     p := char(R);
     J := ideal(1_R);
     while (n <= N+1) do (
	F := apply(generators R, i-> i^(p^n));
	U := ideal(a^(p^n)) : D;
        f := map(R/U, R, F);
        J = intersect(J, kernel f);
	n = n+1;
     );
     J
     )

----------------------------------------
-- Integral closure of ideal -----------
----------------------------------------

-* version 2.  Not working yet, Dec 2020, perhaps use something like this in M2 1.18?
integralClosure(Ideal, RingElement, ZZ) := opts -> (I,a,D) -> (
    S := ring I;
    if a % I != 0 then error "The ring element should be an element of the ideal.";
    if ((ideal 0_S):a) != 0 then error "The given ring element must be a nonzerodivisor of the ring.";
    z := local z;
    w := local w;
    I = trim I;
    Reesi := reesAlgebra(I,a,Variable => z);
    Rbar := integralClosure(Reesi, S,  Variable => w); --opts is missing
    T := S[select(gens Rbar, x -> first degree x == 0)];
    J := ideal select((ideal Rbar)_*, f -> first degree f == 0);
    count := -1;
    TRbar := map(T,ring J,for x in gens ring J list 
        if first degree x == 0 
        then (count = count+1; T_count) 
        else 0);
    S' := T/TRbar J;
    S'S := map(S', S);
    M'' := basis({D}, Rbar, SourceRing => S');
    M := coimage M'';
    IS'D := S'S (I^D);
    -- the last generators of M correspond to IS'D, in order (checking on this).
    rg := splice{(numgens M - numgens IS'D)..(numgens M - 1)};
    phi := map(M, module IS'D, M_rg);
    assert(isWellDefined phi);
    I' := extendIdeal phi;
--    error "debug me";
    preimage(map(S', S), I')
    )
*-

integralClosureOfIdeal = (I, a, D, opts) -> (
    -- Assumption: ring I is integrally closed.
    S := ring I;
    if a % I != 0 then error "The ring element should be an element of the ideal.";
    if ((ideal 0_S):a) != 0 then error "The given ring element must be a nonzerodivisor of the ring.";
    z := local z;
    w := local w;
    I = trim I;
    Reesi := (flattenRing reesAlgebra(I,a,Variable => z))_0;
    Rbar := integralClosure(Reesi, opts, Variable => w);
    psi := map(Rbar,S,DegreeMap =>d->prepend(0,d));
    zIdeal := ideal(map(Rbar,Reesi))((vars Reesi)_{0..numgens I -1});
    zIdealD := module zIdeal^D;
    LD := prepend(D,toList(degreeLength S:null));
    degD := image basisOfDegreeD(LD,Rbar); --all gens of first-degree D.
    degsM := apply(degrees cover degD,d->drop(d,1));
    --the following line is ***slow***
    psi' := map(degD,S^(-degsM),psi,id_(cover degD));
    mapback := map(S,Rbar, matrix{{numgens Rbar-numgens S:0_S}}|(vars S), DegreeMap => d -> drop(d, 1));
    pdegD := gens gb presentation degD;
    origVarsInRbar := support sub(vars S, Rbar);
    ind := select(toList(0..numcols pdegD-1), i -> isSubset(support pdegD_{i}, origVarsInRbar));

    M := coker mapback pdegD_ind;

    phi := map(M,module(I^D), mapback matrix inducedMap(degD,zIdealD));
    if isHomogeneous I and isHomogeneous a then assert(isHomogeneous phi);
    assert(isWellDefined phi);
    extendIdeal phi
    )

integralClosure(Ideal, RingElement, ZZ) := opts -> (I,a,D) -> (
    S := ring I;
    if a % I != 0 then error "The ring element should be an element of the ideal.";
    if ((ideal 0_S):a) != 0 then error "The given ring element must be a nonzerodivisor of the ring.";
    Sbar := integralClosure S;
    Ibar := if Sbar === S then I else S.icMap I;
    abar := if Sbar === S then a else S.icMap a;
    Ibar = trim Ibar;
    J := integralClosureOfIdeal(Ibar, abar, D, opts); -- J is now an ideal in Sbar.
    -- now we need to take preimage in S, if needed.
    if Sbar === S then trim J else trim preimage(S.icMap, J)
    )

integralClosure(Ideal,ZZ) := Ideal => o -> (I,D) -> integralClosure(I, I_0, D, o)
integralClosure(Ideal,RingElement) := Ideal => o -> (I,a) -> integralClosure(I, a, 1, o)
integralClosure(Ideal) := Ideal => o -> I -> integralClosure(I, I_0, 1, o)

-*
Theorem (Saito): If R is a formal power series ring over a field of char 0, 
and f\in R has isolated singularity, then f is contained in j(f), the Jacobian ideal iff f is
quasi-homogeneous after a change of variables.

Theorem (Lejeune-Teisser?; see Swanson-Huneke Thm 7.1.5) 
f \in integral closure(ideal apply(numgens R,i-> x_i*df/dx_i))

Conjecture (Huneke: f is never a minimal generator of the integral closure of
ideal apply(numgens R,i-> df/dx_i).
*-

testHunekeQuestion = method()
testHunekeQuestion RingElement := Boolean => f -> (
    R := ring f;
    mm := ideal vars R;
    j := ideal jacobian f;
    if f % (j+mm*f) == 0 then (
	<< "power series is crypto-quasi-homogeneous"<<flush<<endl;
	return "yes");
    <<"power series is not crypto-quasi-homogeneous"<<flush<<endl;
    j' := ideal apply(numgens R, i -> R_i*j_i);
    J' := integralClosure j';
    if f % (mm*f+ mm*integralClosure j) == 0 then return "yes";
    )

extendIdeal = method()
extendIdeal(Matrix) := Ideal => phi -> ( --This method is WRONG on integralClosure ideal"a2,b2".
    --input: f: (module I) --> M, an inclusion from an ideal 
    --to a module that is isomorphic to the inclusion of I into an ideal J containing I.
    --output: the ideal J, so that f becomes the inclusion I subset J.
    inc := transpose gens source phi;
    phi0 := transpose matrix phi;
    sz := syz transpose presentation target phi;    
    (q,r) := quotientRemainder(inc,phi0*sz);
    if r !=0 then error "phi is not isomorphic to an inclusion of ideals";
    trim ideal (sz*q)
    )

basisOfDegreeD = method()
basisOfDegreeD (List,Ring) := Matrix => (L,R) ->(
    --assumes degrees of R are non-negative
    --change to a heft value sometime.
    PL := positions(L, d-> d=!=null);    
    PV := positions(degrees R, D->any(PL,i->D#i > 0));
    PVars := (gens ambient R)_PV;
    PDegs := PVars/degree/(D->D_PL);
      kk := ultimate(coefficientRing, R);
    R1 := kk(monoid[PVars,Degrees =>PDegs]);
    back := map(R,R1,PVars);
    g := back basis(L_PL, R1);
    map(target g,,g)
    )

-- MES TODO: this function needs to be documented.  I don't know what it is really doing?
-- I have un-exported this function.
integralClosures = method (Options => options integralClosure)
integralClosures(Ideal) := opts -> I -> (
    -- input: ideal I in an affine ring S
    -- output: 
     S := ring I;
     z := local z;
     w := local w;
     t := local t;
     A := tensor(coefficientRing(S)[t],S,Join=>false);
     IA := sub(I,A);
     ReesI := (flattenRing reesAlgebra(IA,Variable =>z))_0;
     fracs := icFractions ReesI;
     phi := map(frac(A),frac(ReesI),gens(A_0*IA)|vars A);
     newfracs := delete((frac A)_0, fracs/phi);
     -- The following two lines remove powers of t, and returns a hashtable
     L := partition(f -> degree(A_0, numerator f), newfracs);
     toFracS := map(frac S, frac A, {0} | gens frac S);
     result := hashTable apply(keys L, d -> d => apply(L#d, f -> toFracS(f // (A_0)^d)));
     result
    )

----------------------------------------
-- Canonical ideal, makeS2 --------
----------------------------------------
parametersInIdeal = method()

parametersInIdeal Ideal := I -> (
     --first find a maximal system of parameters in I, that is, a set of
     --c = codim I elements generating an ideal of codimension c.
     --assumes ring I is affine. 
     --routine is probabilistic, often fails over ZZ/2, returns null when it fails.
     R := ring I;
     c := codim I;
     G := sort(gens I, DegreeOrder=>Ascending);
     s := 0; --  elements of G_{0..s-1} are already a sop (codim s)
     while s<c do(
     	  t := s-1; -- elements of G_{0..t} generate an ideal of codim <= s
     	  --make t maximal with this property, and then add one
     	  while codim ideal(G_{0..t})<=s and t<rank source G -1 do t=t+1;
     	  G1 := G_{s..t};
	  coeffs := random(source G1, R^{-last flatten degrees G1});
	  lastcoef := lift(last last entries coeffs,ultimate(coefficientRing, R));
	  --coeffs = (1/lastcoef)*coeffs;
     	  newg := G1*coeffs;
     	  if s<c-1 then G = G_{0..s-1}|newg|G_{t..rank source G-1}
	       else G = G_{0..s-1}|newg;
	  if codim ideal G <s+1 then (
	       return null;
--	       error ("random coeffs not general enough at step ",s);
	       );
	  s = s+1);
      ideal G)

canonicalIdeal1 = method()
canonicalIdeal1 Ring := R -> (
     --tries to find a canonical ideal in R. Note that if R is
     --not generically Gorenstein, then it has no canonical ideal!
     --This routine is
     --guaranteed to work if R is a domain; if R is merely reduced,
     --or just generically Gorenstein, it may fail. If it fails, 
     --it returns null
     (S,f) := flattenRing R;
     P := ideal S;
     SS := ring P;
     n := numgens SS;
     c := codim P;
     WSS := prune Ext^c(SS^1/P, SS);
     WS := prune coker (map(S,SS)) (presentation WSS);
     H := Hom(WS, S^1);
     toIdeal := homomorphism H_{0};
     if ker toIdeal != 0 then return null;
     trim ideal f^-1 (image toIdeal))

canonicalIdeal = method()
canonicalIdeal Ring := R -> (
     --try to find a canonical ideal in R by the probabilistic method.
     --If you fail, try the method of canonicalIdeal1
     if degreeLength R =!= 1 or any(degrees R, x -> first x <= 0) then
     return canonicalIdeal1 R; -- problems with parametersInIdeal prevent its use yet
     (S,f) := flattenRing R;
     P := ideal S;
     J := parametersInIdeal P;
     if J === null then return canonicalIdeal1 R;
     Jp := J:P;
     trim (f^-1) promote(Jp,S)
     )

makeS2 = method(Options => {
        Variable => "w",
        Verbosity => 0 -- 3/20/26: not currently used!?
        })
-- note, see also S2 in CompleteIntersectionResolutions
makeS2 Ring := RingMap => opts -> R -> (
     --try to find the S2-ification of a domain (or more generally an
     --unmixed, generically Gorenstein ring) R.
     --    Input: R, an affine ring
     --    Output: (like "idealizer") a RingMap F : R --> R'
     --      where R' is the "S2-ification" of R.
     --to obtain the S2-ification.
     --    Uses the method of Vasconcelos, "Computational Methods..." p. 161, taking the idealizer
     --    of a canonical ideal.
     --Assumes that first element of canonicalIdeal R is a nonzerodivisor; else raises error (or returns null?!)
     --CAVEAT:
          --If w_0 turns out to be a zerodivisor
	  --then we should replace it with a general element of w. But if things
	  --are multiply graded this might involve finding a degree with maximal heft 
	  --or some such. How should this be done?? There should be a "general element"
	  --routine...
     w := canonicalIdeal R;
     if w === null then return null; -- 3/20/26: when does this happen?
     if ideal(0_R):w_0 == 0 then (
         result := idealizer(w,w_0,Variable=>makeVariable opts);
         return result;
         )
     else (
	  return null;
	  error"first generator of the canonical ideal was a zerodivisor"
	  )
     )

findConductorInSubring = method()
findConductorInSubring RingMap := (phi) -> (
    R := source phi;
    R' := target phi;
    S := ambient R;
    KR := field R;
    condR := conductor R;
    indeps := support first independentSets ideal R;
    fibervars := sort toList(set gens S - set indeps);
    --fibervars := for s in gens (fieldInfo KR).Finites list sub(s, S); -- TODO: remove 'sub'
    eliminate(fibervars, lift(condR, S))
    )

fractionsSpecificDenominator = method()
fractionsSpecificDenominator(RingMap, RingElement) := List => (phi, f) -> (
    -- phi : R --> R', where R' is integral over R.
    -- f in R is an element of the conductor of phi
    -- returns a list of pairs {numer, denom}, all elements of R.
    R := source phi;
    R' := target phi;
    if ring f =!= R then error "expected an element of the source ring";
    S := ambient R;
    KR := field R;
    fibervars := for s in gens (fieldInfo KR).Finites list sub(s, S); -- TODO: remove 'sub'
    eliminate(fibervars, lift(conductor R, S));
    oldvars := for x in gens R list phi x;
    if any(oldvars/index, i -> i === null) then error "old variables are not variables in the integral closure";
    newvars := sort toList(set gens R' - set oldvars);
    liftback := map(R, R', join(for x in newvars list x => 0, for x in gens R list (phi x) => x));
    fracs := for g in newvars list (
      h := (phi f) * g;
      if not isSubset(support(h), oldvars) then error "my logic is wrong...!";
      {liftback h, f}
      );
    fracs
    )
fractionsSpecificDenominator(RingMap, RingElement) := List => (phi, f) -> (
    -- phi : R --> R', where R' is integral over R.
    -- f in R is an element of the conductor of phi
    -- returns a list of pairs {numer, denom}, all elements of R.

    -- (phi f) * vars target F
    -- lift answer back to R
    --
    numers := (phi f) * vars target phi;
    numersR := sub(numers, source phi); -- assumes TOO MUCH! need more robust way to lift back.
    flatten entries(1/f * numersR) -- TODO: this is NOT what we want!  Want denominator factored.
    )

showFraction = method()
showFraction RingElement  := (x) -> (
    -- x is in a KR = field R.
    den := mydenominator x;
    (hold (den*x)) / factor den
    )

showFractions = method()
showFractions(List, RingElement) := (x, den) -> (
    -- x is a list of elements which can have den as a denominator
    fden := factor den;
    for y in x list 
        (hold (den*y)) / fden
    )

-- icFractions(RingMap, RingElement) := (icm, den) -> ( -- actual denominators can be powers of this
--     -- eventually, stash this.
--     -- icm : R --> R' (R' finite over R)
--     -- den in R, an element in the radical of the conductor of icm.
--     -- steps:
--     --  0. consider the ring R[newvars]/J \isom R'
--     --  1. create the graph ring base[y, x]/(x - icm(x), I(R), I(R'));
--     --   OR: assume that the variables of R are the last variables in a block order.
--     --  2. den * (vars R' over R) = elems
--     --   if elems_i is in R, then gcd over ambient of (den, elems_i). Get fraction.
--     --  3. den * elems. Again, if in R, gcd over ambient of (den^2, elems_i).
--     --  keep going until all elements are accounted for.
--     R := source icm;
--     R' := target icm;
--     nbase := numgens R;
--     nfiber := numgens R' - nbase;
--     for i from 0 to nbase-1 do if index icm (R_i) != nfiber+i then error "rings not in correct form";
--     -- for now, assume they are the last how many blocks?  1 for now.  But we need to match it with R's monomial order...
--     -- let's find the correct subring.

--     i := 1;
--     while numcols selectInSubring(i, vars R') > nbase do i = i+1;
--     liftBack := map(R, R', matrix{{nfiber: 0}} | vars R); -- only use once you know argument is in the subring...!
-- --what's wrong with this?
--     --    insubring := f -> leadTerm(i, f) == f;
--     inSubring := f -> numcols selectInSubring(i, matrix{{f}}) > 0;
--     den' := icm den;

--     modgens := drop(flatten entries ((pushFwd icm)_1), 1); -- remove unit element
--     modFracs := for g in modgens list(
--        j := 0;
--        while (g = den'*g; j = j+1; not inSubring g) do ();
--       (hold liftBack g)/(hold den)^j);

--     ringgens := select(gens R', x -> not inSubring x);
--     ringFracs := for g in ringgens list(
--        j := 0;
--        while (g = den'*g; j = j+1; not inSubring g) do ();
--       (hold liftBack g)/(hold den)^j);
  
-- {ringFracs, modFracs}
-- )

leadCoefficientsOfVariable = method()
leadCoefficientsOfVariable(List, RingElement) := (L, w) -> (
    -- Not correct yet.
    -- want it to be w * (stuff in later block) - (stuff in later block)?
    -- consider the block w is in.
    -- then take elements whose coeff in w is in later subring only, and same with degree 0 term.
    b := 0;
    while member(w, flatten entries selectInSubring(b, vars ring w)) do b = b+1;
    << "first block not containing " << w << " is " << b << endl;
    L0 := select(L, f -> degree_w f == 1 and
                   numcols selectInSubring(b, matrix{{diff(w, f)}}) > 0
                   );
    for f in L0 list leadMonomial diff(w, f)
    )


simplestElement = method()
simplestElement Ideal := RingElement => I -> (
    elts := I_*;
    f0 := first sort for f in elts list {degree f, size f, f};
    return last f0)

-- TODO: this code if one of the variables is not a variable!
--          (i.e. there is a quotient element linear with this variable).
--       also, number of blocks might depend on monomial order, not just number of blocks!
--         and might be different for leadTerm, selectInSubring?
--         In the code below, we assume they are the same!

icFractions RingMap := List => opts -> F -> (
    -- F: R --> R' should be a module finite extension of R, e.g. the integral closure.
    R := source F;
    R' := target F;
    den := opts.Denominator ?? (
        if R.?icDenominator then
            R.icDenominator
        else
            simplestElement radical conductor F
        );
    ----if R === R' then return {};
    -- we need to determine how many/which variables of R' are from R.
    -- and we need to be able to determine whether an element of R' is in image F,
    -- and if so, lift it back.
    nbase := numgens R;
    nfiber := numgens R' - nbase;
    for i from 0 to nbase-1 do if index F (R_i) != nfiber+i then error "rings not in correct form";
    nblocksForSubring := 0;
    while numcols selectInSubring(nblocksForSubring, vars R') > nbase do nblocksForSubring = nblocksForSubring + 1;
    liftBack := map(R, R', matrix{{nfiber: 0}} | vars R); -- only use once you know argument is in the subring...!
    --what's wrong with this? Anything?
    --    insubring := f -> leadTerm(i, f) == f;
    inSubring := f -> numcols selectInSubring(nblocksForSubring, matrix{{f}}) > 0;
    den' := F den;

    gensOverR := if opts#Module then
                     drop(flatten entries ((pushFwd F)_1), 1) -- remove unit element
                 else
                     select(gens R', x -> not inSubring x);
    ourfracs := for g in gensOverR list ( -- if g is already in the subring, this fails!
       if inSubring g then continue;
       j := 0;
       while (g = den'*g; j = j+1; not inSubring g) do ();
       (hold liftBack g)/(hold den)^j
       );
    ourfracs
    )

///
restart
debug needsPackage "IntegralClosure2"
S = ZZ/101[a,b,c,Degrees => {3:{1,2}}]
I =reesIdeal ideal (a^2-b^3, a+b+c, a-1)
I = reesIdeal ideal(a^3,b^3, c^4)
R = ring I/I
R = (flattenRing R)_0
R' = integralClosure R
R.icMap
C = conductor R
simplestElement C
simplestElement radical C
size oo

///
    


-*
    fden := icm den;
    elems := for i from 0 to nfiber-1 list (fden * R'_i);
    den' := lift(fden, ambient R');

    for j from 0 to nfiber-1 list (
        g := fden * R'_j;
        if not insubring g then 0_R
        else (
            g1 := liftBack g;
            g1h := lift(g1, ambient R);
            denh := lift(den, ambient R);
            h := gcd(g1h, denh);
            if h != 1 then (
                g1h = g1h // h;
                denh = denh // h;
                );
            (hold g1h) / factor denh
            )
        )
    )
*-
///--Boehm19
restart
needsPackage "IntegralClosure2"
  S = QQ[u,v] -- MonomialOrder => Lex]
  F = 5*v^6+7*v^2*u^4+6*u^6+21*v^2*u^3+12*u^5+21*v^2*u^2+6*u^4+7*v^2*u
  ideal F
  R = S/F
--  KR = field(R, Independents => {v})
  R' = integralClosure R
icm = icMap R
icFractions icm

C = conductor R
  rC = radical C
 den = rC_0  

  pushFwd icMap R
  icFractions(icMap R,den)
pushFwd icMap R
gens R'
///
///
restart
needsPackage "IntegralClosure2"
-- boehm6
  S = QQ[u,v,z]
  F = u^6+3*u^4*v^2+3*u^2*v^4+v^6-4*u^4*z^2-34*u^3*v*z^2-7*u^2*v^2*z^2+12*u*v^3*z^2+6*v^4*z^2+36*u^2*z^4+36*u*v*z^4+9*v^2*z^4
  factor discriminant(F, u)

  R = S/F
  R' = integralClosure R
den = (radical conductor R)_0
netList   icFractions (icMap R,den)
denominator o20_0
factor oo
factor den


  oo//last//factor
pf = pushFwd icMap R

///

-*
  restart
  needsPackage "IntegralClosure2"
  -- test of this. --boehm19
*-

--------------------------------------------------------------------
TOOSLOW = method()
TOOSLOW String := (str) -> null

beginDocumentation()
--StartWithOneMinor, "vasconcelos",RadicalCodim1,AllCodimensions,SimplifyFractions
--radical(J, Unmixed)
doc ///
  Key
    IntegralClosure2
  Headline
    routines for integral closure of affine domains and ideals
  Description
    Text
      This package contains several algorithms for computing the
      integral closure (i.e. normalization) of an affine domain,
      and also of an ideal.
      
      The basic use of this package is shown in the following example.
    Example
      R = QQ[x,y,z]/(x^3-x^2*z^5-z^2*y^5)
      S = integralClosure R
      describe S
    Text
      Use @TO icFractions@ to see what fractions have been added.
    Example
      icFractions R
    Text
      Look at the ideal of S or the generators of S to see the structure of the
      integral closure.
    Example
      gens S
      trim ideal S
    Text
      The integral closure of an ideal can be computed as follows.
    Example
      use R
      I = ideal(y,z)
      integralClosure I
    Text
      Integral closures of powers of ideals can be computed in a more efficient manner than
      using e.g. {\tt integralClosure(I^d)}, by using e.g. {\tt integralClosure(I,d)}.
    Example
      integralClosure(I^2)
      integralClosure(I, 2)
      integralClosure(I, 3) == integralClosure(I^3)
    Text
      If the characteristic is positive, yet small compared to the degree, but the
      fraction ring is still separable over a subring, then use
      @TO icFracP@, which is an implementation of an algorithm due to
      Leonard-Pellikaan, and modified by Singh-Swanson (see arXiv:0901.0871).
      However, the interface to this routine is likely to change in future
      releases to more closely match the functions above.

      The method used by integralClosure is a modification of the De Jong algorithm
      presented in the paper: De Jong, T., {\em An Algorithm for 
	  Computing the Integral Closure}, J. Symbolic Computation, 
	  (1998) 26, 273-277.
///

doc ///
  Key
    integralClosure
  Headline
    integral closure of an ideal or a domain
///

doc ///
  Key
    (isNormal, Ring)
  Headline
    determine if a reduced ring is normal
  Usage
    isNormal R
  Inputs
    R:Ring
      a reduced equidimensional ring
  Outputs
    :Boolean
      whether {\tt R} is normal, that is, whether it satisfies
      Serre's conditions S2 and R1
  Description
   Text
     This function computes the jacobian of the ring which can be costly for 
     larger rings.  Therefore it checks the less costly S2 condition first and if 
     true, then tests the R1 condition using the jacobian of {\tt R}.
   Example
     R = QQ[x,y,z]/ideal(x^6-z^6-y^2*z^4);
     isNormal R
     isNormal(integralClosure R)
  Caveat
    The ring {\tt R} must be an equidimensional ring.  If {\tt R} is a domain,
    then sometimes computing the integral closure of {\tt R} can be faster than
    this test.
  SeeAlso
    integralClosure
    makeS2
///

doc ///
  Key
    (integralClosure, Ring)
  Headline
    compute the integral closure (normalization) of an affine domain
  Usage
    R' = integralClosure R
  Inputs
    R:Ring
      a quotient of a polynomial ring over a field
    Keep => List
      of variables of R
    Limit => ZZ
    Variable => Symbol
    Verbosity => ZZ
    Strategy => List
      of some of the symbols: AllCodimensions, Radical, RadicalCodim1, 
      Vasconcelos, StartWithOneminor, SimplifyFractions
  Outputs
    R':Ring
      the integral closure of {\tt R}
  Consequences
   Item
    The inclusion map $R \rightarrow R'$
      can be obtained with @TO icMap@.  
   Item
    The fractions corresponding to the variables
      of the ring {\tt R'} can be found with @TO icFractions@
  Description
   Text
     The integral closure of a domain is the subring of the fraction field
     consisting of all fractions integral over the domain.  For example,
   Example
     R = QQ[x,y,z]/ideal(x^6-z^6-y^2*z^4-z^3);
     R' = integralClosure R
     gens R'
     icFractions R
     icMap R
     I = trim ideal R'
   Text
     Sometimes using @TO trim@ provides a cleaner set of generators.
   Text
     If $R$ is not a domain, first decompose it, and collect all of the 
     integral closures.
   Example
     S = ZZ/101[a..d]/ideal(a*(b-c),c*(b-d),b*(c-d));
     C = decompose ideal S
     Rs = apply(C, I -> (ring I)/I);
     Rs/integralClosure
     oo/prune
   Text
     This function is roughly based on
     Theo De Jong's paper, {\em An Algorithm for 
     Computing the Integral Closure}, J. Symbolic Computation, 
     (1998) 26, 273-277. This algorithm is similar to the round two
     algorithm of Zassenhaus in algebraic number theory.
   Text
     There are several optional parameters which allows the user to control
     the way the integral closure is computed.  These options may change
     in the future.
  Caveat
    This function requires that the degree of the field extension 
    (over a pure transcendental subfield) be greater 
    than the characteristic of the base field.  If not, use @TO icFracP@.
    This function requires that the ring be finitely generated over a ring.  If not (e.g. 
    if it is f.g. over the integers), then the result is integral, but not necessarily 
    the entire integral closure. Finally, if the ring is not a domain, then
    the answers will often be incorrect, or an obscure error will occur.
  SeeAlso
    icMap
    icFractions
    conductor
    icFracP
///

doc ///
  Key
    (integralClosure, Ring, Ring)
  Headline
    compute the integral closure (normalization) of an affine reduced ring over a base ring
  Usage
    R' = integralClosure(R, A)
  Inputs
    R:Ring
      a quotient of a polynomial ring ultimately over a field
    A:Ring
      a base ring of $R$ (one of its coefficient rings)
    Keep => List
      of variables of R
    Limit => ZZ
    Variable => Symbol
    Verbosity => ZZ
    Strategy => List
      of some of the symbols: AllCodimensions, Radical, RadicalCodim1, 
      Vasconcelos, StartWithOneminor, SimplifyFractions
  Outputs
    R':Ring
      the integral closure of $R$, having coefficient ring $A$
  Consequences
   Item
    The inclusion map $R \rightarrow R'$
      can be obtained with @TO icMap@.  
   Item
    The fractions corresponding to the variables
      of the ring {\tt R'} can be found with @TO icFractions@
  Description
   Text
     This function packages the output integral closure in the desired way.
     For more details about integral closure, see @TO (integralClosure, Ring)@.
     
     In the following example, there are three possible coefficient rings for $R$: $R$, $A$ and ${\mathbb Q}$.
   Example
     A = QQ[x,y]/(x^3-y^2)
     R = reesAlgebra(ideal(x*y,y^2), Variable => z)
     coefficientRing R
     describe R
   Example
     R' = integralClosure(R, R)
     describe R'
     icMap R
     fracs1 = icFractions R
   Example
     R'' = integralClosure(R, A)
     describe R''
     icMap R
     fracs2 = icFractions R
     assert(fracs1 == fracs2)
   Example
     R''' = integralClosure(R, QQ)
     describe R'''
     icMap R
     fracs3 = icFractions R
     assert(fracs1 == fracs3)
   Text
     Note that the second and third calls to {\tt integralClosure} changes the output of {\tt icMap}
     but the fractions are the same.
  Caveat
    All the caveats of @TO (integralClosure, Ring)@ are in effect and the output of @TO icMap@
    changes upon each call to this function.
  SeeAlso
    (integralClosure, Ring)
    icMap
    icFractions
///

--StartWithOneMinor, "vasconcelos",RadicalCodim1,AllCodimensions,SimplifyFractions
doc ///
  Key
    [integralClosure, Keep]
  Headline
    list ring generators which should not be simplified away
  Usage
    integralClosure(R, Keep=>L)
  Inputs
    L:List
      a list of variables in the ring R, or {\tt null} (the default).
  Consequences
   Item
    The given list of variables (or all of the outer generators, if L is null)
    will be generators of the integral closure
  Description
   Text
     Consider the cuspidal cubic, and three different possibilities for {\tt Keep}.
   Example
     R = QQ[x,y]/ideal(x^3-y^2);
     R' = integralClosure(R, Variable => symbol t)
     trim ideal R'
   Example
     R = QQ[x,y]/ideal(x^3-y^2);
     R' = integralClosure(R, Variable => symbol t, Keep => {x})
     trim ideal R'
   Example
     R = QQ[x,y]/ideal(x^3-y^2);
     integralClosure(R, Variable => symbol t, Keep => {})
///

doc ///
  Key
    [integralClosure, Variable]
  Headline
    set the base letter for the indexed variables introduced while computing the integral closure
  Usage
    integralClosure(R, Variable=>x)
  Inputs
    x:Symbol
  Consequences
   Item
    The new variables will be subscripted using {\tt x}.
  Description
   Example
     R = QQ[x,y,z]/ideal(x^6-z^6-y^2*z^4-z^3);
     R' = integralClosure(R, Variable => symbol t)
     trim ideal R'
   Text
     The algorithm works in stages, each time adding new fractions to the ring.
     A variable {\tt t_(3,0)} represents the first (zero-th) variables added at stage 3.
     
  Caveat
    The base name should be a symbol
    The variables added may be changed to {\tt t_1, t_2, ...} in the future.
///

doc ///
  Key
    [integralClosure,Limit]
  Headline
    do a partial integral closure
  Usage
    integralClosure(R, Limit => n)
  Inputs
    n:ZZ
      how many steps to perform
  Description
   Text
     The integral closure algorithm proceeds by finding a suitable ideal $J$,
     and then computing $Hom_R(J,J)$, and repeating these steps.  This
     optional argument limits the number of such steps to perform.
     
     The result is an integral extension, but is not necessarily integrally closed.
   Example
     R = QQ[x,y,z]/ideal(x^6-z^6-y^2*z^4-z^3);
     R' = integralClosure(R, Variable => symbol t, Limit => 2)
     trim ideal R'
     icFractions R
///

doc ///
  Key
    [integralClosure,Verbosity]
  Headline
    display a certain amount of detail about the computation
  Usage
    integralClosure(R, Verbosity => n)
  Inputs
    n:ZZ
      The higher the number, the more information is displayed.  A value
      of 0 means: keep quiet.
  Description
   Text
     When the computation takes a considerable time, this function can be used to 
     decide if it will ever finish, or to get a feel for what is happening
     during the computation.
   Example
     R = QQ[x,y,z]/ideal(x^8-z^6-y^2*z^4-z^3);
     time R' = integralClosure(R, Verbosity => 2)
     trim ideal R'
     icFractions R
  Caveat
    The exact information displayed may change.
///

doc ///
  Key
    [integralClosure,Strategy]
  Headline
    control the algorithm used
  Usage
    integralClosure(R, Strategy=>L)
  Inputs
    L:List
      of a subset of the following: {\tt RadicalCodim1, Radical, AllCodimensions, Vasconcelos, SimplifyFractions, StartWithOneMinor}
  Description
   Text
     Overall, the default options are the best.  However, sometimes one of these is dramatically 
     better (or worse!).  For the examples here, one doesn't notice much difference.
     
     {\tt RadicalCodim1} chooses an alternate, often much faster, sometimes much slower,
     algorithm for computing the radical of ideals.  This will often produce a different
     presentation for the integral closure. {\tt Radical} chooses yet another such algorithm.
     
     {\tt AllCodimensions} tells the algorithm to bypass the computation of the
     S2-ification, but in each iteration of the algorithm, use the radical of
     the extended Jacobian ideal from the previous step, instead of using only the
     codimension 1 components of that.  This is useful when for some reason the
     S2-ification is hard to compute, or if the probabilistic algorithm for 
     computing it fails.  In general though, this option slows down the computation
     for many examples.
     
     {\tt StartWithOneMinor} tells the algorithm to not compute the entire Jacobian ideal, 
     just find one element in it.  This is often a bad choice, unless the ideal is large
     enough that one can't compute the Jacobian ideal.  In the future, we plan on using
     the @TO "FastMinors::FastMinors"@ package to compute part of the Jacobian ideal.
     
     {\tt SimplifyFractions} changes the fractions to hopefully be simpler.  Sometimes it
     succeeds, yet sometimes it makes the fractions worse.  This is because of the manner
     in which fraction fields work.  We are hoping that in the future, less drastic 
     change of fractions will happen by default.

     {\tt Vasconocelos} tells the routine to instead of computing Hom(J,J),
     to instead compute Hom(J^-1, J^-1).  This is usually a more time consuming
     computation, but it does potentially get to the answer in a smaller number of steps.
   Example
     S = QQ[x,y,z]
     f = ideal (x^8-z^6-y^2*z^4-z^3)
     R = S/f
     time R' = integralClosure R
     netList (ideal R')_*
     icFractions R
   Example
     S = QQ[x,y,z]
     f = ideal (x^8-z^6-y^2*z^4-z^3)
     R = S/f
     time R' = integralClosure(R, Strategy => Radical)
     netList (ideal R')_*
     icFractions R
   Example
     S = QQ[x,y,z]
     f = ideal (x^8-z^6-y^2*z^4-z^3)
     R = S/f
     time R' = integralClosure(R, Strategy => AllCodimensions)
     netList (ideal R')_*
   Example
     S = QQ[x,y,z]
     f = ideal (x^8-z^6-y^2*z^4-z^3)
     R = S/f
     time R' = integralClosure(R, Strategy => SimplifyFractions)
     netList (ideal R')_*     
   Example
     S = QQ[x,y,z]
     f = ideal (x^8-z^6-y^2*z^4-z^3)
     R = S/f
     time R' = integralClosure (R, Strategy => RadicalCodim1)
     netList (ideal R')_*
   Example
     S = QQ[x,y,z]
     f = ideal (x^8-z^6-y^2*z^4-z^3)
     R = S/f
     time R' = integralClosure (R, Strategy => Vasconcelos)
     netList (ideal R')_*
   Example
     S = QQ[a,b,c,d]
     f = monomialCurveIdeal(S,{1,3,4})
     R = S/f
     time R' = integralClosure R
     netList (ideal R')_*
   Text
    Rational Quartic
   Example
     S = QQ[a,b,c,d]
     I = monomialCurveIdeal(S,{1,3,4})
     R = S/I
     time R' = integralClosure(R, Strategy => Radical)
     icFractions R
   Example
     S = QQ[a,b,c,d]
     I = monomialCurveIdeal(S,{1,3,4})
     R = S/I
     time R' = integralClosure(R, Strategy => AllCodimensions)
     icFractions R
   Example
     S = QQ[a,b,c,d]
     I = monomialCurveIdeal(S,{1,3,4})
     R = S/I
     time R' = integralClosure (R, Strategy => RadicalCodim1)
     icFractions R
   Example
     S = QQ[a,b,c,d]
     I = monomialCurveIdeal(S,{1,3,4})
     R = S/I
     time R' = integralClosure (R, Strategy => Vasconcelos)
     icFractions R
   Text
    Projected Veronese
   Example
     S' = QQ[symbol a .. symbol f]
     M' = genericSymmetricMatrix(S',a,3)
     I' = minors(2,M')
     center = ideal(b,c,e,a-d,d-f)
     S = QQ[a,b,c,d,e]
     p = map(S'/I',S,gens center)
     I = kernel p
     betti res I
     R = S/I
     time R' = integralClosure(R, Strategy => Radical)
     icFractions R
   Example
     S' = QQ[a..f]
     M' = genericSymmetricMatrix(S',a,3)
     I' = minors(2,M')
     center = ideal(b,e,a-d,d-f)
     S = QQ[a,b,d,e]
     p = map(S'/I',S,gens center)
     I = kernel p
     betti res I
     R = S/I
     time R' = integralClosure(R, Strategy => Radical)
     icFractions R
   Example
     S = QQ[a,b,d,e]
     R = S/sub(I,S)
     time R' = integralClosure(R, Strategy => AllCodimensions)
     icFractions R
   Example
     S = QQ[a,b,d,e]
     R = S/sub(I,S)
     time R' = integralClosure (R, Strategy => RadicalCodim1, Verbosity => 1)
     icFractions R
   Example
     S = QQ[a,b,d,e]
     R = S/sub(I,S)
     time R' = integralClosure (R, Strategy => Vasconcelos, Verbosity => 1)
     icFractions R
   Text
     One can give several of these options together.  Although note that only one
     of {\tt AllCodimensions}, {\tt RadicalCodim1}, {\tt Radical} will be used.
   Example
     S = QQ[a,b,d,e]
     R = S/sub(I,S)
     time R' = integralClosure (R, Strategy => {Vasconcelos, StartWithOneMinor}, Verbosity => 1)
     icFractions R
     ideal R'
  Caveat
   The list of strategies may change in the future! 
///

--mes--  
   --StartWithOneMinor, "vasconcelos",RadicalCodim1,AllCodimensions,SimplifyFractions
   -- Example
   --   S = QQ[x,y]
   --   f = ideal (y^4-2*x^3*y^2-4*x^5*y+x^6-x^7)
   --   R = S/f
   --   --time R' = integralClosure (R, Strategy => StartWithOneMinor)
   --   icFractions R
   -- Example
   --   S = QQ[a,b,c,d]
   --   I = monomialCurveIdeal(S,{1,3,4})
   --   R = S/I
   --   time R' = integralClosure (R, Strategy => StartWithOneMinor)
   --   icFractions R
   -- Example
   --   S = QQ[a,b,c,d]
   --   I = monomialCurveIdeal(S,{1,3,4})
   --   R = S/I
   --   time R' = integralClosure(R, Strategy => SimplifyFractions)
   --   icFractions R

   -- Example
   --   S = QQ[a,b,d,e]
   --   R = S/sub(I,S)
   --   time R' = integralClosure (R, Strategy => StartWithOneMinor)
   --   icFractions R

   -- Example
   --   S = QQ[a,b,d,e]
   --   R = S/sub(I,S)
   --   time R' = integralClosure(R, Strategy => SimplifyFractions)
   --   icFractions R
-- The use of Denominator isn't working well yet.
     -- XXX     
     -- time R' = integralClosure(R, Denominator => x*(x+4)) -- crash!
     -- time R' = integralClosure(R, Denominator => x*(x+4), Verbosity => 2) -- crash!
     -- time R' = integralClosure(R, Denominator => x, Verbosity => 2)
     -- time R' = integralClosure(R, Denominator => x+4, Verbosity => 2)


doc ///
  Key
    (integralClosure, Ideal, RingElement, ZZ)  
    (integralClosure, Ideal, ZZ)  
    (integralClosure, Ideal)
    (integralClosure, Ideal, RingElement)
  Headline
    integral closure of an ideal in an affine domain
  Usage
    integralClosure J
    integralClosure(J, d)
    integralClosure(J, f)
    integralClosure(J, f, d)
  Inputs
    J:Ideal
    f:RingElement
      optional, an element of J which is a nonzerodivisor in the ring of J.
      If not give, the first generator of {\tt J} is used
    d:ZZ
      optional, default value 1
    Keep => List
      unused
    Limit => ZZ
      unused
    Variable => Symbol
      symbol used for new variables
    Verbosity => ZZ
    Strategy => List
      of some of the symbols: AllCodimensions, SimplifyFractions, Radical, RadicalCodim1, Vasconcelos.
      These are passed on to the computation of the integral closure of the Rees algebra of {\tt J}
  Outputs
    :Ideal
      the integral closure of $J^d$
  Description
   Text
     The method used is described in Vasconcelos' book, 
     {\em Computational methods in commutative algebra and algebraic
	  geometry}, Springer, section 6.6.  Basically, one first
     computes the integral closure of the Rees Algebra of the ideal,
     and then one reads off the integral closure of any of the powers
     of the ideal, using linear algebra.
   Example
     S = ZZ/32003[a,b,c];
     F = a^2*b^2*c+a^3+b^3+c^3
     J = ideal jacobian ideal F
     time integralClosure J
     time integralClosure(J, Strategy=>{RadicalCodim1})
     J2' = integralClosure(J,2)
   Text
     Sometimes it is useful to give the specific nonzerodivisor $f$ in the ideal.
   Example
     assert(integralClosure(J, J_2, 2) == J2')
  Caveat
    It is usually much faster to use {\tt integralClosure(J,d)}
    rather than {\tt integralClosure(J^d)}.
    Also, the element {\tt f} (or the first generator of {\tt J}, if {\tt f} is not given)
    must be a nonzero divisor in the ring. This is not checked.
  SeeAlso
    (integralClosure,Ring)
    reesAlgebra
    testHunekeQuestion
///

doc ///
  Key
    idealizer
    (idealizer, Ideal, RingElement)
    [idealizer, Strategy]
    [idealizer, Verbosity]
  Headline
    compute Hom(I,I) as a quotient ring
  Usage
    (F,G) = idealizer(I,f)
  Inputs
    I:Ideal
      whose endomorphism ring we'll compute
    f:RingElement
      a nonzerodivisor in $I$
    Variable:Symbol
    Index:ZZ
    Strategy => List
     possible elements include ``Vasconcelos''
    Verbosity => ZZ
     larger numbers give more information 
  Outputs
    F:RingMap
      The inclusion map from $R$ into $S = Hom_R(I,I)$
    G:RingMap
      $frac S \rightarrow frac R$, giving the fractions
      corresponding to each generator of $S$.
  Description
   Text
     The idealizer of $I$, computed as target F, 
     is the largest subring of the fraction field of ring I in which $I$ is
     still an ideal.  Note that this is NOT the common use of the term
     in commutative algebra.
     
     This is a key subroutine used in the computation of 
     integral closures.
   Example
     R = QQ[x,y]/(y^3-x^7)
     I = ideal(x^2,y^2)
     (F,G) = idealizer(I,x^2);
     target F
     first entries G.matrix
  SeeAlso
    ringFromFractions
    integralClosure
///

document {
     Key => [makeS2,Variable],
     Headline=> "Sets the name of the indexed variables introduced in computing
     the S2-ification."
     }

document {
     Key => [idealizer,Variable],
     Headline=> "Sets the name of the indexed variables introduced in computing 
     the endomorphism ring Hom(J,J)."
     }

document {
     Key => Index,
     Headline => "Optional input for idealizer",
     PARA{},
     "This option allows the user to select the starting index for the
     new variables added in computing Hom(J,J) as a ring.  The default
     value is 0 and is what most users will use.  The option is needed
     for the iteration implemented in integralClosure."
}


document {
     Key => [idealizer, Index],
     Headline => "Sets the starting index on the new variables used to build the endomorphism ring Hom(J,J)",
     "If the program idealizer is
     used independently, the user will generally want to use the
     default value of 0.  However, when used as part of the
     integralClosure computation the number needs to start higher
     depending on the level of recursion involved. "
     }

doc ///
  Key
    icMap
    (icMap,Ring)
  Headline
    natural map from an affine domain into its integral closure
  Usage
    f = icMap R
  Inputs
    R:Ring
      an affine domain
  Outputs
    f:RingMap
      from {\tt R} to its integral closure
  Description
   Text
     If the integral closure of {\tt R} has not yet been computed, 
     that computation is performed first.  No extra computation
     is involved.  If {\tt R} is integrally closed, then the identity
     map is returned.
   Example
     R = QQ[x,y]/(y^2-x^3)
     f = icMap R
     isWellDefined f
     source f === R
     describe target f
   Text     
   
     This finite ring map can be used to compute the conductor,
     that is, the ideal of elements of {\tt R} which are 
     universal denominators for the integral closure (i.e. those d \in R
	  such that d R' \subset R).
   Example
     S = QQ[a,b,c]/ideal(a^6-c^6-b^2*c^4);
     F = icMap S;
     conductor F
  Caveat
    If you want to control the computation of the integral closure via optional
    arguments, then make sure you call @TO (integralClosure,Ring)@ first, since
    {\tt icMap} does not have optional arguments.
  SeeAlso
    (integralClosure,Ring)
    conductor
///

doc ///
  Key
    icFractions
    (icFractions, Ring)
  Headline
    fractions integral over an affine domain
  Usage
    icFractions R
  Inputs
    R:Ring
      an affine domain
  Outputs
    :List
      a list of fractions over {\tt R}, generating the
      integral closure of {\tt R}, as an {\tt R}-algebra.
  Description
   Text
     If the integral closure of {\tt R} has not yet been computed, 
     that computation is performed first.  No extra computation
     is then involved to find the fractions.
   Example
     R = QQ[x,y,z]/ideal(x^6-z^6-y^2*z^4);
     icFractions R
     R' = integralClosure R
     gens R'
     netList (ideal R')_*
   Text
     Notice that the $i$-th fraction corresponds to the $i$-th generator 
     of the integral closure.  For instance, the variable $w_(3,0) = {x^2 \over z}$.
  Caveat
     (a) Currently in Macaulay2, fractions over quotients of polynomial rings
     do not have a nice normal form.  In particular, sometimes
     the fractions are `simplified' to give much nastier looking fractions.
     We hope to improve this.

     (b)
     If you want to control the computation of the integral closure via optional
     arguments, then make sure you call @TO (integralClosure,Ring)@ first, since
     {\tt icFractions} does not have optional arguments.
  SeeAlso
    integralClosure
    icMap
///

doc ///
  Key
    conductor
    (conductor,RingMap)
    (conductor,Ring)
  Headline
    the conductor of a finite ring map
  Usage
    conductor F
    conductor R
  Inputs
    F:RingMap
      $R \rightarrow S$, a finite map with $R$ an affine reduced ring
    R:Ring
      an affine domain.  In this case, $F : R \rightarrow S$ is the 
      inclusion map of $R$ into the integral closure $S$
  Outputs
    :Ideal
      of $R$ consisting of all $d \in R$ such that $dS \subset F(R)$
  Description
   Text
     Suppose that the ring map $F : R \rightarrow S$ is finite: i.e. $S$ is a finitely 
     generated $R$-module.  The conductor of $F$ is defined to be 
     $\{ g \in R \mid g S \subset F(R) \}$.
     One way to think
     about this is that the conductor is the set of universal denominators
     of {\tt S} over {\tt R}, or as the largest ideal of {\tt R}
     which is also an ideal in {\tt S}. An important case is the
     conductor of the map from a ring to its integral closure.
   Example
     R = QQ[x,y,z]/ideal(x^7-z^7-y^2*z^5);
     icFractions R
     F = icMap R
     conductor F
   Text
     If an affine domain (a ring finitely generated over a field) is given as input,
     then the conductor of $R$ in its integral closure is returned.
   Example
     conductor R
   Text
     If the map is not {\tt icFractions(R)}, then @TO pushForward@ is called to compute
     the conductor.
  Caveat
    Currently this function only works if {\tt F} comes from a
    integral closure computation, or is homogeneous
  SeeAlso
    integralClosure
    icFractions
    icMap
    pushFwd
///

doc ///
  Key
    ringFromFractions
    (ringFromFractions,Matrix,RingElement)
    [ringFromFractions,Variable]
    [ringFromFractions,Index]
    [ringFromFractions,Verbosity]
  Headline
    find presentation for f.g. ring  
  Usage
    F = ringFromFractions(H,f)
  Inputs
    H:Matrix
      a one row matrix over a ring $R$
    f:RingElement
    Variable => Symbol
      name of symbol used for new variables
    Index => ZZ
      the starting index for new variables
    Verbosity => ZZ
      values up to 6 are implemented. Larger values show more output.
  Outputs
    F:RingMap
      $R \rightarrow S$, where $S$ is the extension ring
      of $R$ generated by the fractions $1/f H$
  Description
   Text
     Serious restriction: It is assumed that this ring R[1/f H] is an endomorphism ring
     of an ideal in $R$.  This means that the Groebner basis, in a product order,
     will have lead terms all quadratic monomials in the new variables,
     together with other elements which are degree 0 or 1 in the new variables.
   Example
     R = QQ[x,y]/(y^2-x^3)
     H = (y * ideal(x,y)) : ideal(x,y)
     F = ringFromFractions(((gens H)_{1}), H_0);
     S = target F
     F
     ideal S
///

doc ///
  Key
    makeS2
    (makeS2,Ring)
    [makeS2, Verbosity]
  Headline
    compute the S2ification of a reduced ring
  Usage
    F = makeS2 R
  Inputs
    R:Ring
      an equidimensional reduced (or just unmixed and genericaly Gorenstein) affine ring
    Verbosity => ZZ
     larger values give more information.
  Outputs
    F:RingMap
      $R \rightarrow S$, where $S$ is the so-called S2-ification of $R$
  Description
   Text
     A ring $S$ satisfies Serre's S2 condition if every codimension 1 ideal
     contains a nonzerodivisor and every principal ideal generated by a nonzerodivisor
     is equidimensional of codimension one.  If $R$ is an affine reduced ring, 
     then there is a unique smallest extension $R\subset S\subset {\rm frac}(R)$ satisfying S2, 
     and $S$ is finite as an $R$-module.

     Uses the method of Vasconcelos, "Computational Methods..." p. 161, taking the idealizer
     of a canonical ideal.
     
     There are other methods to compute $S$, not currently implemented in this package. See
     for example the function (S2,Module) in the package "CompleteIntersectionResolutions".

     We compute the S2-ification of the rational quartic curve in $P^3$
   Example
     A = ZZ/101[a..d];
     I = monomialCurveIdeal(A,{1,3,4})
     R = A/I;
     F = makeS2 R
     describe target F
  Caveat
     Assumes that first element of canonicalIdeal R is a nonzerodivisor; else returns error.
     The return value of this function has changed in M2 version 1.26.05
     from a sequence of two ring maps, to a single ring map.
  SeeAlso
    integralClosure
///

doc ///
   Key
    testHunekeQuestion
    (testHunekeQuestion, RingElement)
   Headline
    tests a conjecture on integral closures strengthening the Eisenbud-Mazur conjecture
   Usage
    B = testHunekeQuestion f
   Inputs
    f:RingElement
   Outputs
    B:Boolean
     whether f the answer to the question is yes for f
   Description
    Text
     Background:
     
     Theorem (Saito): If R is a formal power series ring over a field of char 0, 
     and f \in R is a power series with an isolated singularity,
     then f\in j(f), the Jacobian ideal iff f becomes
     quasi-homogeneous after a change of variables. 
     
     This can be tested over an affine ring by testing f % (j(f)+ideal vars S).
     If the result is 0 we call f crypto-quasi-homogeneous.

     Theorem (Lejeune-Teisser; see Swanson-Huneke Thm 7.1.5) 
     f \in integral closure(ideal apply(numgens R,i-> x_i*df/dx_i))

     Question (Huneke): Is f actually contained in the maximal ideal
     times the integral closure of
     ideal apply(numgens R,i-> df/dx_i).
     
     Note that the answer is trivially yes if f is crypto-quasi-homogeneous.
     
     Huneke has shown that if the answer is always yes, then the Eisenbud-Mazur conjecture
     on evolutions is true.
    
    Example
     R = QQ[x,y,z]
     f = random(3,R)+random(4,R)+random(5,R)
     testHunekeQuestion f
    Text
     The function y^4-2*x^3*y^2-4*x^5*y+x^6-x^7 is defines the simplest plane curve
     singularity with 2 characteristic pairs, and is thus NOT crypto- quasi-homogeneous.
    Example
     R = QQ[x,y]
     f = (y^4-2*x^3*y^2-4*x^5*y+x^6-x^7)
     testHunekeQuestion f
   SeeAlso
    (integralClosure, Ideal)
///



document {
     Key => {icFracP, (icFracP, Ring)},
     Headline => "compute the integral closure in prime characteristic",
     Usage => "icFracP R, icFracP(R, ConductorElement => D), icFracP(R, Limit => N), icFracP(R, Verbosity => ZZ)",
     Inputs => {
	"R" => {"that is reduced, equidimensional,
           finitely and separably generated over a field of characteristic p"},
	ConductorElement => {"optionally provide a non-zerodivisor conductor element ",
               TT "ConductorElement => D", ";
               the output is then the module generators of the integral closure.
               A good choice of ", TT "D", " may speed up the calculations?"},
	Limit => {"if value N is given, perform N loop steps only"},
	Verbosity => {"if value is greater than 0, report the conductor element and number of steps in the loop"},
	},
     Outputs => {{"The module generators of the integral closure of ", TT "R",
               " in its total ring of fractions.  The generators are
               given as elements in the total ring of fractions."}
          },
     "Input is an equidimensional reduced ring in characteristic p
     that is finitely and separably generated over the base field.
     The output is a finite set of fractions that generate
     the integral closure as an ", TT "R", "-module.
     An intermediate step in the code
     is the computation of a conductor element ", TT "D",
     " that is a non-zerodivisor;
     its existence is guaranteed by the separability assumption.
     The user may supply ", TT "D",
     " with the optional ", TT "ConductorElement => D", ".
     (Sometimes, but not always, supplying ", TT "D", " speeds up the computation.)
     In any case, with the non-zero divisor ", TT "D", ",
     the algorithm starts by setting the initial approximation of the integral closure
     to be the finitely generated ", TT "R", "-module
     ", TT "(1/D)R", ",
     and in the subsequent loop the code recursively constructs submodules.
     Eventually two submodules repeat;
     the repeated module is the integral closure of ", TT "R", ".
     The user may optionally provide ", TT "Limit => N", " to stop the loop
     after ", TT "N", " steps,
     and the optional ", TT "Verbosity => 1", " reports the conductor
     element and the number of steps it took for the loop to stabilize.
     The algorithm is based on the
     Leonard--Pellikaan--Singh--Swanson algorithm.",
     PARA{},
     "A simple example.",
     EXAMPLE {
          "R = ZZ/5[x,y,z]/ideal(x^6-z^6-y^2*z^4);",
          "icFracP R"
     },
     "The user may provide an optional non-zerodivisor conductor element ",
     TT "D",
     ".  The output generators need not
     be expressed in  the form with denominator ", TT "D", ".",
     EXAMPLE {
          "R = ZZ/5[x,y,u,v]/ideal(x^2*u-y^2*v);",
          "icFracP(R)",
          "icFracP(R, ConductorElement => x)",
     },
     "In case ", TT "D", " is not in the conductor, the output is ",
     TT "V_e = (1/D) {r in R | r^(p^i) in (D^(p^i-1)) ", "for ",
     TT "i = 1, ..., e}",
     " such that ", TT "V_e = V_(e+1)", " and ", TT "e",
     " is the smallest such ", TT "e", ".",
     EXAMPLE {
	  "R=ZZ/2[u,v,w,x,y,z]/ideal(u^2*x^3+u*v*y^3+v^2*z^3);",
          "icFracP(R)",
          "icFracP(R, ConductorElement => x^2)"
     },
     "The user may also supply an optional limit on the number of steps
     in the algorithm.  In this case, the output is a finitely generated ",
     TT "R", "-module contained in ", TT "(1/D)R",
     " which contains the integral closure (intersected with ", TT "(1/D)R",
     ".",
     EXAMPLE {
          "R=ZZ/2[u,v,w,x,y,z]/ideal(u^2*x^3+u*v*y^3+v^2*z^3);",
          "icFracP(R, Limit => 1)",
          "icFracP(R, Limit => 2)",
          "icFracP(R)"
     },
     "With the option above one can for example determine how many
     intermediate modules the program should compute or did compute
     in the loop to get the integral closure.  A shortcut for finding
     the number of steps performed is to supply the ",
     TT "Verbosity => 1", " option.",
     EXAMPLE {
          "R=ZZ/3[u,v,w,x,y,z]/ideal(u^2*x^4+u*v*y^4+v^2*z^4);",
          "icFracP(R, Verbosity => 1)"
     },
     "With this extra bit of information, the user can now compute
     integral closures of principal ideals in ", TT "R", " via ",
     TO icPIdeal, ".",
     SeeAlso => {"icPIdeal", "integralClosure", (isNormal, Ring)},
     Caveat => "The interface to this algorithm will likely change eventually"
--     Caveat => "NOTE: mingens is not reliable, neither is kernel of the zero map!!!"
}

document {
     Key => ConductorElement,
     Headline => "Specifies a particular non-zerodivisor in the conductor."
}

document {
     Key => [icFracP,ConductorElement],
     Headline => "Specifies a particular non-zerodivisor in the conductor.",
     "A good choice can possibly speed up the calculations.  See ",
     TO icFracP, "."
}


document {
     Key => [icFracP,Limit],
     Headline => "Limits the number of computed intermediate modules."
--     Caveat => "NOTE: How do I make M2 put icFracP on the list of all functions that use Limit?"
}

document {
     Key => [icFracP,Verbosity],
     Headline => "Prints out the conductor element and
           the number of intermediate modules it computed.",
     Usage => "icFracP(R, Verbosity => ZZ)",
     "The main use of the extra information is in computing the
     integral closure of principal ideals in ", TT "R",
     ", via ", TO icPIdeal,
     ".",
     EXAMPLE {
          "R=ZZ/3[u,v,x,y]/ideal(u*x^2-v*y^2);",
          "icFracP(R, Verbosity => 1)",
	  "S = ZZ/3[x,y,u,v];",
          "R = S/kernel map(S,S,{x-y,x+y^2,x*y,x^2});",
	  "icFracP(R, Verbosity => 1)"
     },
}

document {
     Key => {icPIdeal,(icPIdeal, RingElement, RingElement, ZZ)},
     Headline => "compute the integral closure
                  in prime characteristic of a principal ideal",
     Usage => "icPIdeal (a, D, N)",
     Inputs => {
	"a" => {"an element in ", TT "R"},
        "D" => {"a non-zerodivisor of ", TT "R",
                " that is in the conductor"},
        "N" => {"the number of steps in ", TO icFracP,
                " to compute the integral closure of ", TT "R",
                ", by using the conductor element ", TT "D"}},
     Outputs => {{"the integral closure of the ideal ", TT "(a)", "."}},
     "The main input is an element ", TT "a",
     " which generates a principal ideal whose integral closure we are
     seeking.  The other two input elements,
     a non-zerodivisor conductor element ", TT "D",
     " and the number of steps ", TT "N", 
     " are the pieces of information obtained from ",
     TT "icFracP(R, Verbosity => true)",
     ".  (See the Singh--Swanson paper, An algorithm for computing
     the integral closure, Remark 1.4.)",
     EXAMPLE {
          "R=ZZ/3[u,v,x,y]/ideal(u*x^2-v*y^2);",
          "icFracP(R, Verbosity => 1)",
          "icPIdeal(x, x^2, 3)"
     },
     SeeAlso => {"icFracP"},
     Caveat => "The interface to this algorithm will likely change eventually"     
}


doc ///
  Key
    Keep
  Headline
    an optional argument for various functions
  SeeAlso
    (integralClosure,Ring)
    (integralClosure,Ideal,ZZ)
///

doc ///
  Key
    RadicalCodim1
  Headline
    a symbol denoting a strategy element usable with integralClosure(...,Strategy=>...)
  SeeAlso
    (integralClosure,Ring)
///

doc ///
  Key
    Radical
  Headline
    a symbol denoting a strategy element usable with integralClosure(...,Strategy=>...)
  SeeAlso
    (integralClosure,Ring)
///

doc ///
  Key
    AllCodimensions
  Headline
    a symbol denoting a strategy element usable with integralClosure(...,Strategy=>...)
  SeeAlso
    (integralClosure,Ring)
///

doc ///
  Key
    StartWithOneMinor
  Headline
    a symbol denoting a strategy element usable with integralClosure(...,Strategy=>...)
  SeeAlso
    (integralClosure,Ring)
///

doc ///
  Key
    SimplifyFractions
  Headline
    a symbol denoting a strategy element usable with integralClosure(...,Strategy=>...)
  SeeAlso
    (integralClosure,Ring)
///

doc ///
  Key
    Vasconcelos
  Headline
    a symbol denoting a strategy element usable with integralClosure(...,Strategy=>...)
  SeeAlso
    (integralClosure,Ring)
///

///
  -- This (disabled) test indicates we want to use Normaliz when computing
  -- the integral closure if a binomial ideal.
  -- disabled: because the last paragraph of 4 commands takes over 10 seconds total.
  debug IntegralClosure2
  setRandomSeed 0
  S' = ZZ/101[x,y]
  S = S'/ideal(x^3 -y^2)  
  J = idealInSingLocus S
  J' = idealInSingLocus (S,Strategy => {StartWithOneMinor})
  assert(J == ideal"x2,y")
  assert(numgens J' === 1)

  degs = {1,3,4,7}
  S = ZZ/101[vars(0..length degs)]
  I = monomialCurveIdeal(S,degs)
  J = reesIdeal I

  R = (ring J)/J
  R = first flattenRing reesAlgebra I
  isHomogeneous R

  elapsedTime Jsing = idealInSingLocus R;
  CJsing = decompose ideal gens gb Jsing  
  elapsedTime  R' = integralClosure R
  assert(R' === R)
///

-- MES TODO: remove this test, or at least make it a better test.
TEST ///
-*
  restart
  needsPackage "IntegralClosure2"
  debug loadPackage("IntegralClosure2", Reload => true)
*-
  debug IntegralClosure2
  kk=ZZ/101
  S=kk[a,b,c,d]
  I=monomialCurveIdeal(S, {3,5,6})
  R=S/I
  K = ideal(b,c)
  f=b*d
  vasconcelos(K, f)
  endomorphisms(K, f)
  codim K
  R1=ringFromFractions vasconcelos(K,f)
  R2=ringFromFractions endomorphisms(K,f)
  betti res I -- NOT depth 2.

  elapsedTime R' = integralClosure R
  condR = conductor icMap R
  use R
  assert(condR == ideal(d^2,c*d,b*d,c^2,b*c))
  icFractions(R, Denominator => R.icDenominator)
  use R
  
  I = ideal I_*
  time integralClosure(S/I, Strategy => {Vasconcelos})

  I = ideal I_*
  time integralClosure(S/I, Strategy => {})

  makeS2 R
///

-- MES TODO: remove this test, or at least make it a better test.
TEST ///
-*
  restart
  debug loadPackage("IntegralClosure2", Reload => true)
*-
  debug IntegralClosure2
  kk=ZZ/101
  S=kk[a,b,c,d]
  I=monomialCurveIdeal(S, {3,5,6})
  M=jacobian I
  D = randomMinors(2,2,M)
  R=S/I
  J = trim substitute(ideal D ,R)
  vasconcelos (J, J_0)
  codim((J*((ideal J_0):J)):ideal(J_0))
  endomorphisms (J,J_0)
  vasconcelos (radical J, J_0)
  endomorphisms (radical J,J_0)
  codim J
  syz gens J
///

-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TEST ///
restart
needsPackage "IntegralClosure2"
///
///
S = QQ [(symbol Y)_1, (symbol Y)_2, (symbol Y)_3, (symbol Y)_4, symbol x, symbol y, Degrees => {{7, 1}, {5, 1}, {6, 1}, {6, 1}, {1, 0}, {1, 0}}, MonomialOrder => ProductOrder {4, 2}]
  J =
    ideal(Y_3*y-Y_2*x^2,Y_3*x-Y_4*y,Y_1*x^3-Y_2*y^5,Y_3^2-Y_2*Y_4*x,Y_1*Y_4-Y_2^2*y^3)
  R = S/J       
  elapsedTime R' = integralClosure R
  conductor R
  den = (radical conductor R)_0
  icFractions(icMap R, den)
pushFwd icMap R
  KF = frac(ring ideal R')
  M1 = first entries substitute(vars R, KF)
  M2 = apply(R.icFractions, i -> matrix{{i}})

  assert(matrix{icFractions R} == substitute(matrix {{(Y_2*y^2)/x, (Y_1*x)/y,
                  Y_1, Y_2, Y_3, Y_4, x, y}}, frac R))
///

TEST ///
-*
  restart
  loadPackage("IntegralClosure2", Reload => true)
*-
  assert isNormal (QQ[x]/(x^2+1))
  assert not isNormal (QQ[x,y,z]/( ideal(x*y, z) * ideal (z-1) ))
  assert not isNormal (QQ[x,y,z]/( ideal(x*y)    * ideal (x-1,y-1) ))
  assert not isNormal (QQ[x,y,z]/( ideal(x*y, z) * ideal (x-1,y-1) ))
  assert not isNormal (QQ[x,y,z]/( ideal(x*y)    * ideal (z-1) ))
  assert not isNormal (QQ[x,y,z]/( ideal(x*y)    * ideal (z-1) ))
  assert isNormal (QQ[x,y,z,t]/( ideal (x^2+y^2+z^2,t) ))

  -- here is an example of why the ring has to be equidimensional:
  -- assert isNormal (QQ[x,y,z,t]/( ideal (x^2+y^2+z^2,t) * ideal(t-1) ))
///


TEST ///
-*
  restart
  loadPackage("IntegralClosure2", Reload => true)
*-
  debug IntegralClosure2
  kk=ZZ/101
  S=kk[a,b,c]
  I =ideal"a3,ac2"
  M = module ideal"a2,ac"
  f=inducedMap(M,module I)
  assert(extendIdeal(f) == ideal(a^2, a*c))
///


-- MES TODO: make this into a test.  There are no assert's here.
TEST ///
-*
  restart
  loadPackage("IntegralClosure2", Reload => true)
*-
  debug IntegralClosure2
  kk=ZZ/2
  S=kk[a,b,c,d]
  PP = monomialCurveIdeal(S,{1,3,4})
  betti res PP
  for count from 1 to 10 list parametersInIdeal PP
  for count from 1 to 10 list canonicalIdeal (S/PP)
///     

-- MES TODO: test canonicalIdeal1 here?
TEST ///
-*
  restart
  loadPackage("IntegralClosure2", Reload => true)
*-
  debug IntegralClosure2
  setRandomSeed 0
  A = ZZ/101[a..e]
  I = ideal"ab,bc,cd,de,ea"
  R = reesAlgebra I
  describe I
  describe R
  assert(canonicalIdeal1 R == ideal(w_4, a*b))
  assert(canonicalIdeal R == ideal(w_4, a*b))
  R1 = first flattenRing R
  assert(canonicalIdeal1 R1 == ideal(w_4, a*b))
  assert(canonicalIdeal R1 == ideal(w_4, a*b))
///


TEST ///
-*
  restart
  loadPackage("IntegralClosure2", Reload => true)
*-
  debug IntegralClosure2
  kk=ZZ/101
  S=kk[a,b,c,d]
  canonicalIdeal S
  PP = monomialCurveIdeal(S,{1,3,4})
  betti res PP
  R = S/PP
  w=canonicalIdeal R
  w1 = canonicalIdeal1 R -- a different, somewhat less pleasing answer...
  -- check that these two different canonical ideals are isomorphic.
  F = homomorphism (Hom(w,w1))_{0}
  ker F
  prune coker F
  assert isIsomorphism F
///     

-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TEST ///
  kk=ZZ/101
  S = kk[a,b,d,e]
  S' = kk[a,b,c,d,e]
  I = monomialCurveIdeal(S,{1,3,4})
  R = S/I
  J = ideal integralClosure R
  use R
  assert(value first icFractions R == d^2/e)

  Rtilde = target makeS2 R
  J' = ideal integralClosure(Rtilde)
  icFractions Rtilde
  assert(J' == substitute(J, ring J'))
  J'' = monomialCurveIdeal(S', {1,2,3,4})
  use S'
  phi = map(S',ring J,{c,a,b,d,e})
  assert(J'' == phi J)
  use R
  assert(first icFractions R == (d^2/e))
  f = makeS2 R
  assert(isWellDefined f)
  assert(source f === R)
///     

TOOSLOW /// -- TODO: no longer so slow
-*
  restart
  loadPackage("IntegralClosure2", Reload => true)
*-
  createD = () -> (
      C = QQ[B1,B2,B3,B4,B5,B6];
      I =  ideal(B4*B5+B1*B6,B1*B4+B2*B4-B3*B6,B1^2+B1*B2+B3*B5,B2*B5^2-B6^2,B1*B2*
           B5+B4*B6,B3*B4^2-B6^2,B3^2*B4-B1*B6-B2*B6,B2*B3*B4-B3^2*B6-B5*B6,B3^3-B1
           *B2-B2^2+B3*B5,B1*B3^2+B1*B5+B2*B5,B1*B2*B3+B3^2*B5+B5^2,B1*B2^2+B2*B3*
           B5+B4^2,B3^2*B5^2+B5^3-B3*B4*B6,B2^3*B4-B2^2*B3*B6-B3^2*B5*B6-B4^3-B5^2*
           B6);
      D = C/I
      );

  D = createD();
  D' = integralClosure D
  assert(numgens integralClosure(D, Strategy=>{RadicalCodim1})==numgens D+2)

  D = createD();
  assert(numgens integralClosure D == numgens D + 2)

 
  D = createD();
  assert(numgens elapsedTime integralClosure(D, Strategy => {SimplifyFractions}) == numgens D + 2)

///

-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TOOSLOW ///
  S = ZZ/32003[a,b,c,d,x,y,z,u]
  I = ideal(
     a*x-b*y,
     b*u^7+b*u^6-2*b*z*u^4+b*u^5-2*b*z*u^3-2*b*z*u^2+3*b*z^2+c*x,
     a*u^7+a*u^6-2*a*z*u^4+a*u^5-2*a*z*u^3-2*a*z*u^2+3*a*z^2+c*y,
     b*z*u^6+9142*b*z*u^5+13715*b*z^2*u^3-9143*b*z*u^4-9145*b*u^5-13716*b*z^2*u^2-13712*b*z^2*u-13713*b*z*u^2+4568*b*z^2+9145*c*x*u-9145*c*x+4572*d*x,
     a*z*u^6+9142*a*z*u^5+13715*a*z^2*u^3-9143*a*z*u^4-9145*a*u^5-13716*a*z^2*u^2-13712*a*z^2*u-13713*a*z*u^2+4568*a*z^2+9145*c*y*u-9145*c*y+4572*d*y,
     c*u^8+7111*c*z*u^6+3556*d*u^7+10667*c*z*u^5+3556*d*u^6+14224*c*z^2*u^3+14223*c*z*u^4-7112*d*z*u^4+3556*d*u^5+10668*c*z^2*u^2-7112*d*z*u^3+7112*c*z^2*u-7112*d*z*u^2+10668*d*z^2);
  R = S/I
  time R' = integralClosure(R) 
  time R' = integralClosure(R, Strategy=>{RadicalCodim1}) -- slightly faster than without it
  see ideal R'
  use R
  icFractions(icMap R)
  use R
  netList icFractions R
  assert isWellDefined icMap R
  assert(R' === target icMap R)
  assert(R === source icMap R)
  --time conductor R very slow!
  --assert(conductor icMap R == ideal"x,y,z-u,u2-u") -- MES: get conductor working on these
  ///

-- integrally closed test
-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TEST ///
  R = QQ[u,v]/ideal(u+2)
  time J = integralClosure (R,Variable => symbol a) 
  use ring ideal J
  assert(ideal J == ideal(u+2))
  assert(set icFractions R === set{-2_(frac R), v_(frac R)})
///

-- degrees greater than 1 test
-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TEST ///
  R = ZZ/101[symbol x..symbol z,Degrees=>{2,5,6}]/(z*y^2-x^5*z-x^8)
  time R' = integralClosure (R,Variable => symbol b) 
  use ring ideal R'
  answer = ideal(b_(1,0)*x^2-y*z, x^6-b_(1,0)*y+x^3*z, -b_(1,0)^2+x^4*z+x*z^2)
  assert(ideal R' == answer)
  use R
  assert(conductor R== ideal(x^2,y))
  assert(conductor(R.icMap) == ideal(x^2,y))
  assert(#(icFractions R) === 1)
  assert(value (icFractions R)_0 === y*z/x^2)
  assert isWellDefined icMap R
  assert isNormal R'
///

-- multigraded test
-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TEST ///
  R = ZZ/101[symbol x..symbol z,Degrees=>{{1,2},{1,5},{1,6}}]/(z*y^2-x^5*z-x^8)
  time R' = integralClosure (R,Variable=>symbol a) 
  use ring ideal R'
  assert(ideal R' == ideal(-x^6+a_(1,0)*y-x^3*z,-a_(1,0)*x^2+y*z,a_(1,0)^2-x^4*z-x*z^2))
  use R
  assert(#(icFractions R) === 1)
  assert(value (icFractions R)_0 == y*z/x^2)
  assert isWellDefined icMap R'
  assert isNormal R'
///

-- multigraded homogeneous test
-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TEST ///
  R = ZZ/101[symbol x..symbol z,Degrees=>{{4,2},{10,5},{12,6}}]/(z*y^2-x^5*z-x^8)
  time R' = integralClosure (R,Variable=>symbol a) 
  use ring ideal R'
  assert(ideal R' == ideal(a_(1,0)*x^2-y*z,a_(1,0)*y-x^6-x^3*z,a_(1,0)^2-x^4*z-x*z^2))
  use R
  assert(#(icFractions R) === 1)
  assert(value (icFractions R)_0 === y*z/x^2)
  assert(conductor(R.icMap) == ideal(x^2,y))
  isNormal R'
  ///

-- Reduced not a domain test
-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TEST ///
  S=ZZ/101[symbol a,symbol b,symbol c, symbol d]
  I=ideal(a*(b-c),c*(b-d),b*(c-d))
  R=S/I                              
  compsR = apply(decompose ideal R, J -> S/J)
  ansR = compsR/integralClosure
  compsR/icFractions
  apply(decompose ideal R, J -> integralClosure(S/J))
  assert all(compsR/icMap, f -> f == 1)
///

--Craig's example as a test
-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TEST ///
  S = ZZ/101[symbol x,symbol y,symbol z,MonomialOrder => Lex]
  I = ideal(x^6-z^6-y^2*z^4)
  Q = S/I
  time Q' = integralClosure (Q, Variable => symbol a)
  use ring ideal Q'
  assert(ideal Q' == ideal (x^2-a_(3,0)*z, a_(3,0)*x-a_(4,0)*z, a_(3,0)^2-a_(4,0)*x, a_(4,0)^2-y^2-z^2))
  use Q
  assert(conductor(Q.icMap) == ideal(z^3,x*z^2,x^3*z,x^4))
  assert(matrix{(icFractions Q)/value} == matrix{{x^3/z^2,x^2/z}}) -- MES FLAG: this looks like z^2 is in the conductor?? possible bug?
  isNormal Q'
///

--Mike's inhomogeneous test
-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TEST ///
  R = QQ[symbol a..symbol d]
  I = ideal(a^5*b*c-d^2)
  Q = R/I
  Q' = time integralClosure(Q,Variable => symbol x, Keep=>{})
  use ring ideal Q'
  assert(ideal Q' == ideal(x_(1,0)^2-a*b*c))
  use Q
  assert(matrix{(icFractions Q)/value} == matrix{{d/a^2}}) -- BUG: Keep => {} is not compatible with our impl of icFractions!
///

-- rational quartic, to make sure S2 is not being forgotten!
-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TEST ///
  S = QQ[a..d]
  I = monomialCurveIdeal(S,{1,3,4})
  R = S/I
  R' = integralClosure R
  assert(numgens R' == 5)
  assert isNormal R'
  icFractions R
  integralClosure R'
  icFractions R'
///

--Ex from Wolmer's book - tests longer example and published result.
-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TEST ///
  R = ZZ/101[symbol a..symbol e]
  I = ideal(a^2*b*c^2+b^2*c*d^2+a^2*d^2*e+a*b^2*e^2+c^2*d*e^2,
      a*b^3*c+b*c^3*d+a^3*b*e+c*d^3*e+a*d*e^3,
      a^5+b^5+c^5+d^5-5*a*b*c*d*e+e^5,
      a^3*b^2*c*d-b*c^2*d^4+a*b^2*c^3*e-b^5*d*e-d^6*e+3*a*b*c*d^2*e^2-a^2*b*e^4-d*e^6,
      a*b*c^5-b^4*c^2*d-2*a^2*b^2*c*d*e+a*c^3*d^2*e-a^4*d*e^2+b*c*d^2*e^3+a*b*e^5,
      a*b^2*c^4-b^5*c*d-a^2*b^3*d*e+2*a*b*c^2*d^2*e+a*d^4*e^2-a^2*b*c*e^3-c*d*e^5,
      b^6*c+b*c^6+a^2*b^4*e-3*a*b^2*c^2*d*e+c^4*d^2*e-a^3*c*d*e^2-a*b*d^3*e^2+b*c*e^5,
      a^4*b^2*c-a*b*c^2*d^3-a*b^5*e-b^3*c^2*d*e-a*d^5*e+2*a^2*b*c*d*e^2+c*d^2*e^4)
  S = R/I
  elapsedTime S' = integralClosure S
  use S
  icFractions S
  icFractions(icMap S, Denominator => b)
  M = pushForward (icMap S, S'^1);
  assert(degree (M/(M_0)) == 2) -- MES: what are we testing here?
  assert(# icFractions S == 2)

   -- this is part of the above example.  But what to really place into the test?
  StoS2 = (makeS2 S)
  S2 = target StoS2 -- MES: this doesn't set fractions.  Should it?
  conductor StoS2
  icFractions(StoS2, Denominator => a_S)
  icFractions(StoS2)
  
  
-*  
  time integralClosure(S2, Verbosity => 3) -- MES: example where jacobian time is long, whole thing is very long
  M = pushForward (StoS2, S2^1);
  gens M
  N = prune(M/M_0)
  assert(degree N == 2)

  time V = integralClosure (S, Variable => X) -- MES BUG: this doesn't change variable name!
  degree S
  codim singularLocus S
  use ring ideal V

  oldanswer = ideal(a^2*b*c^2+b^2*c*d^2+a^2*d^2*e+a*b^2*e^2+c^2*d*e^2,
	   a*b^3*c+b*c^3*d+a^3*b*e+c*d^3*e+a*d*e^3,
	   a^5+b^5+c^5+d^5-5*a*b*c*d*e+e^5,
	   a*b*c^4-b^4*c*d-X_0*e-a^2*b^2*d*e+a*c^2*d^2*e+b^2*c^2*e^2-b*d^2*e^3,
	   a*b^2*c^3+X_1*d+a*b*c*d^2*e-a^2*b*e^3-d*e^5,
	   a^3*b^2*c-b*c^2*d^3-X_1*e-b^5*e-d^5*e+2*a*b*c*d*e^2,
	   a^4*b*c+X_0*d-a*b^4*e-2*b^2*c^2*d*e+a^2*c*d*e^2+b*d^3*e^2,
	   X_1*c+b^5*c+a^2*b^3*e-a*b*c^2*d*e-a*d^3*e^2,
	   X_0*c-a^2*b^2*c*d-b^2*c^3*e-a^4*d*e+2*b*c*d^2*e^2+a*b*e^4,
	   X_1*b-b*c^5+2*a*b^2*c*d*e-c^3*d^2*e+a^3*d*e^2-b*e^5,
	   X_0*b+a*b*c^2*d^2-b^3*c^2*e+a*d^4*e-a^2*b*c*e^2+b^2*d^2*e^2-c*d*e^4,
	   X_1*a-b^3*c^2*d+c*d^2*e^3,X_0*a-b*c*d^4+c^4*d*e,
	   X_1^2+b^5*c^5+b^4*c^3*d^2*e+b*c^2*d^3*e^4+b^5*e^5+d^5*e^5,
	   X_0*X_1+b^3*c^4*d^3-b^2*c^7*e+b^2*c^2*d^5*e-b*c^5*d^2*e^2-
	     a*b^2*c*d^3*e^3+b^4*c*d*e^4+a^2*b^2*d*e^5-a*c^2*d^2*e^5-b^2*c^2*e^6+b*d^2*e^7,
	   X_0^2+b*c^3*d^6+2*b^5*c*d^3*e+c*d^8*e-b^4*c^4*e^2+a^3*c^3*d^2*e^2+
	     2*a^2*b^3*d^3*e^2-5*a*b*c^2*d^4*e^2+4*b^3*c^2*d^2*e^3-3*a*d^6*e^3+
	     5*a^2*b*c*d^2*e^4-b^2*d^4*e^4-2*b*c^3*d*e^5-a^3*b*e^6+3*c*d^3*e^6-a*d*e^8)

  -- We need to check the correctness of this example!
  newanswer = ideal(
    a^2*b*c^2+b^2*c*d^2+a^2*d^2*e+a*b^2*e^2+c^2*d*e^2,
    a*b^3*c+b*c^3*d+a^3*b*e+c*d^3*e+a*d*e^3,
    a^5+b^5+c^5+d^5-5*a*b*c*d*e+e^5,
    X_1*e-a^3*b^2*c+b*c^2*d^3,
    X_1*d+a*b^2*c^3-b^5*d-d^6+3*a*b*c*d^2*e-a^2*b*e^3-d*e^5,
    X_1*c-c*d^5+a^2*b^3*e+a*b*c^2*d*e-a*d^3*e^2,
    X_1*b-b^6-b*c^5-b*d^5+4*a*b^2*c*d*e-c^3*d^2*e+a^3*d*e^2-b*e^5,
    X_1*a-a*b^5-b^3*c^2*d-a*d^5+2*a^2*b*c*d*e+c*d^2*e^3,
    X_0*e-a*b*c^4+b^4*c*d,
    X_0*d+a^4*b*c-a^2*b^2*d^2+a*c^2*d^3-a*b^4*e-b^2*c^2*d*e+a^2*c*d*e^2,
    X_0*c-2*a^2*b^2*c*d+a*c^3*d^2-a^4*d*e+b*c*d^2*e^2+a*b*e^4,
    X_0*b-a^2*b^3*d+2*a*b*c^2*d^2+a*d^4*e-a^2*b*c*e^2-c*d*e^4,
    X_0*a-a^3*b^2*d+a^2*c^2*d^2-b*c*d^4+a*b^2*c^2*e+c^4*d*e-a*b*d^2*e^2,
    X_1^2-b^10-b^5*c^5+2*a*b^2*c^3*d^4-2*b^5*d^5-d^10-5*b^4*c^3*d^2*e+6*a*b*c*d^6*e-6*a^3*b^4*d*e^2-4*b^3*c*d^4*e^2+2*a^2*b*d^4*e^3-4*a*b^3*d^2*e^4+b*c^2*d^3*e^4-b^5*e^5-d^5*e^5,
    X_0*X_1-a^2*b^7*d+b^3*c^4*d^3+a^4*b*c*d^4-a^2*b^2*d^6+a*c^2*d^7+4*b^2*c^2*d^5*e+b^6*d^2*e^2+b*c^5*d^2*e^2+3*a^2*c*d^5*e^2+b*d^7*e^2+a^4*b^3*e^3+4*c^3*d^4*e^3-2*a^3*d^3*e^4+b*d^2*e^7,
    X_0^2-a^4*b^4*d^2-a^2*c^4*d^4+7*b*c^3*d^6-2*b^5*c*d^3*e-2*c^6*d^3*e+2*a^3*b*d^5*e+5*c*d^8*e+a^3*c^3*d^2*e^2-6*a^2*b^3*d^3*e^2-a*b*c^2*d^4*e^2-2*a*b^5*d*e^3-2*b^3*c^2*d^2*e^3+5*a*d^6*e^3-a^2*b*c*d^2*e^4+a^3*b*e^6+c*d^3*e^6+a*d*e^8)

  assert(ideal V == newanswer)   
*-
///

-- Test of isNormal
-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TEST ///
  S = ZZ/101[x,y,z]/ideal(x^2-y, x*y-z^2)
  assert not isNormal S
  assert isNormal integralClosure S
///

-- Test of icMap and conductor
-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TEST ///
  R = QQ[x,y,z]/ideal(x^6-z^6-y^2*z^4)
  R' = integralClosure R
  F = R.icMap
  describe R'
  use R
  assert(conductor F == ideal(z^3,x*z^2,x^3*z,x^4))
  icFractions R -- not a bug: (x^2/z)*(x^3/z^2) = x^5/z^3, so need z^3 for the conductor.
///

-- Test of not keeping the original variables
-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TEST ///
  R = QQ[x,y]/(y^2-x^3)
  R' = integralClosure(R, Keep=>{})
  assert(numgens R' == 1)
  assert(numgens ideal R' == 0)
  assert(ring x === R)
  assert(icFractions R == {y/x})
  F = icMap R
  assert(target F === R')
  assert(source F === R)
///


-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TEST ///
--huneke2
  kk = ZZ/32003
  S = kk[a,b,c]
  F = a^2*b^2*c+a^4+b^4+c^4
  J = ideal jacobian ideal F
  substitute(J:F, kk) -- check local quasi-homogeneity!
  I = ideal first (flattenRing reesAlgebra J)
  betti I
  R = (ring I)/I
  --time R'=integralClosure(R, Strategy => {StartWithOneMinor}, Verbosity =>3 ) -- this is bad in the first step!
  time R' = integralClosure(R, Verbosity => 3) -- this one takes perhaps too long for a test
  assert(numgens R' == 13)
  assert(numgens ideal gens gb ideal R' == 54) -- this is not an invariant...!
  -- this is not satisfactory: want to know at least one denominator.  e.g. one used in doing the integral closure.
  icFractions(R, Denominator => b_R) -- MES: these fractions are messier than they could be?

  -- clear R, and do another one
  R1 = (ring I)/(ideal I_*)
  time R1'=integralClosure(R1, Verbosity => 3, Strategy => {RadicalCodim1})
  assert(numgens R1' == 13)
  assert(numgens ideal gens gb ideal R1' == 54) -- this is not an invariant!
  icFractions(R1, Denominator => b_R1) -- MES: these fractions are messier than they could be?
///

-- see https://github.com/Macaulay2/M2/issues/933
-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TEST ///
    S = QQ[a..f]
    I = ideal(a*b*c,a*d*f,c*e*f,b*e*d)
    assert (integralClosure I == integralClosure trim I)
///

-- added from bug-integralClosure.m2 May 2020
-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TEST ///
    debug IntegralClosure2 -- for extendIdeal
    S = ZZ/101[a,b,c,d]
    K =ideal(a,b)
    I = c*d*K
    M = module (c*K)
    M' = module(d*K)
    phi = map(M,module I,d*id_M)
    phi' = map(M',module I,c*id_M')
    assert(isWellDefined phi)
    assert(extendIdeal phi == c*K)
    assert(extendIdeal phi'== d*K)    
    assert(integralClosure I == I)
    assert(integralClosure ideal"a2,b2" == ideal"a2,ab,b2")
///

-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TEST ///
    debug IntegralClosure2 -- for extendIdeal
    S = ZZ/101[a,b,c]/ideal(a^3-b*(b-c)*(b+c))
    K =ideal(a,b)
    I = c*(b+c)*K
    M = module (c*K)
    M' = module((b+c)*K)
    phi = map(M,module I,(b+c)*id_M)
    phi' = map(M',module I,c*id_M')
    assert(isWellDefined phi)
    assert(isWellDefined phi')    
    assert(extendIdeal phi == c*K)
    assert(extendIdeal phi'== (b+c)*K)    
    assert(integralClosure I == I) 
///

-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TEST///
    debug IntegralClosure2 -- for extendIdeal
    S = ZZ/101[a,b,c]/ideal(a^3-b^2*c)
    K =ideal(a,b)
    I = c*(b+c)*K
    M = module (c*K)
    M' = module((b+c)*K)
    phi = map(M,module I,(b+c)*id_M)
    phi' = map(M',module I,c*id_M')
    assert(isWellDefined phi)
    assert(isWellDefined phi')    
    assert(extendIdeal(phi)== c*K)
    assert(extendIdeal(phi')== (b+c)*K)    
    assert(integralClosure(ideal(a^2,b^2))==ideal"a2,ab,b2")
    assert(integralClosure I == I)
///

load "./IntegralClosure2/HarbourneExamples.m2"
-- an example of Brian Harbourne

-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TEST ///
-- An example construction communicated to us by Craig Huneke
-- Start with a polynomial f (but generally not quasi-homog), 
-- consider the Jacobian ideal J, then f is in the integral closure of J.
-- Actually, is this true?
  kk = ZZ/32003
  S = kk[x,y,z,t]
  F = poly"xy-(z-t2)(z-t3)(z-t4)"
  J = ideal jacobian ideal F
  mm = ideal vars S
  F % (J+mm*F)!=0 -- shows that F is not crypto-quasihomogeneous
  J' = integralClosure J
  assert (F % (J'+mm*F) == 0)
///

-- a homogeneous example which extends the ground field
-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TEST ///
  kk = QQ
  R = kk[x,y, z]
  I1 = ideal(x,y-z)
  I2 = ideal(x-3*z, y-5*z)
  I3 = ideal(x,y)
  I4 = ideal(x-5*z,y-2*z)

  I = intersect(I1^3, I2^3, I3^3, I4^3)
  F = I_0 + I_1 + I_2 + I_3
  assert isHomogeneous F
  S = R/F
  V = integralClosure S
  ring presentation V
  ideal V
  trim ideal V -- MES: should we be using this? It is much simpler
  icFractions S -- nasty fraction, is it that bad?
    -- notice that this fraction is actually algebraic over the base field
  use ring ideal V
  G = eliminate(ideal V, {x,y,z})
  assert(numgens G == 1)
  assert(isPrime G_0)  -- G_0 is a cubic over kk
///

-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TEST ///
  -- git issue #1117
  R = QQ[a,b,c,d,e,f]
  I = ideal(a*b*d,a*c*e,b*c*f,d*e*f);
  J = I^2;
  K = integralClosure(I,2)
  F = ideal(a*b*c*d*e*f);
  assert not isSubset(F,J)
  assert isSubset(F,K)
  assert isSubset(F^2,J^2)
  assert(K != J)
  assert(K == J + F)
///

-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TEST ///
  -- git issue #846
  R = QQ[x,y]
  I = ideal(x^2,y^2)
  assert(integralClosure I == ideal(x^2, x*y, y^2))
///

-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TEST ///
  -- bug mentioned on 22 Dec 2020 in googlegroup.
  -- fixed later in Dec 2020.
  R = QQ[x,y]/(x^3-y^2)
  I = ideal(y)
  integralClosure I
  integralClosure(I,2)
  assert(integralClosure I == ideal(y, x^2))
///

-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TEST ///
  R = QQ[x,y]/(x^3-y^2)
  I = ideal(y)
  integralClosure I
  integralClosure(I,2)
  assert(integralClosure I == ideal(y, x^2))
///

-*
  restart
  needsPackage "IntegralClosure2"
  loadPackage("IntegralClosure2", Reload => true)
*-
TEST ///
  R = QQ[x,y]
  assert(integralClosure R === R)
  assert(integralClosure ideal 1_R == ideal 1_R)
  --integralClosure ideal 0_R -- so so error message, but at least there is one.

  A = QQ[x,y,z]
  assert(A === integralClosure A)
  S = A/ker map(QQ[t],A,{t^3,t^5,t^7})
  assert(integralClosure ideal(y,z) == ideal(x^2, y, z))
///

-- Let's add in tests for the Leonard-Pellikan, Singh-Swanson algorith,
-- Maybe also call out to QthPower?

-*
  restart
  needsPackage "IntegralClosure2"
*-
TEST ///
  -- Singh-Swanson, example 2.1.
  make2'1 = (p) -> (
      S := ZZ/p[x,y,u,v];
      I := ideal(x^2 * v - y^2 * u);
      S/I)
  R = make2'1 2
  R' = integralClosure R
  icFractions R
  use R
  conductor R == ideal(x,y)
  icFracP R

  R = make2'1 29
  R' = integralClosure R
  icFractions R
  use R
  conductor R == ideal(x,y)
  icFracP R
  ///

-*
  restart
  needsPackage "IntegralClosure2"
*-
TEST ///
  -- Singh-Swanson, example 2.2.
  make2'2 = (p) -> (
      S := ZZ/p[u,v,x,y,z,t];
      I := ideal(u^2*x^4 + u*v*y^4 + v^2*z^4);
      S/I)
  R = make2'2 2
  R' = integralClosure R
  icFractions R
  conductor R
  use R
  assert member(v*y^3, conductor R)
  for g in v*y^3 * icFractions R list lift(value g, R)
  for g in oo list g/(v*y^3)
  icFracP R

  R = make2'2 3
  R' = integralClosure R
  R' === R
  icFractions R
  use R
  conductor R == ideal(u,v)
  icFracP R -- one new fraction.
  
  R = make2'2 5
  R' = integralClosure R
  icFractions R
  use R
  conductor R == ideal(u,v)
  elapsedTime icFracP R

  R = make2'2 7
  R' = integralClosure R
  icFractions R -- new fraction is u*x^4/v == -(u*y^4+v*z^4)/u
  use R
  conductor R == ideal(u,v)
--  elapsedTime icFracP R -- 38 sec -- TODO: place an assert here for the answer...

  R = make2'2 23
  elapsedTime R' = integralClosure R -- 0.04 sec
  icFractions R -- new fraction is u*x^4/v == -(u*y^4+v*z^4)/u
  use R
  conductor R == ideal(u,v)
  --elapsedTime icFracP R -- long
  ///

-*
  restart
  needsPackage "IntegralClosure2"
*-
TEST ///
  -- Singh-Swanson, example 2.3.
  make2'3 = (p) -> (
      S := ZZ/p[u,v,x,y,z];
      I := ideal(u^2*x^p + 2*u*v*y^p + v^2*z^p);
      S/I)

  R = make2'3 3
  elapsedTime R' = integralClosure R
  icFractions R
  use R
  conductor R
  elapsedTime icFracP R -- 3 new fractions
  
  R = make2'3 5
  elapsedTime R' = integralClosure R
  icFractions R
  use R
  conductor R
  elapsedTime icFracP R -- 5 new fractions

  R = make2'3 7
  elapsedTime R' = integralClosure R
  icFractions R -- 7 new fractions
  use R
  radical conductor R
  elapsedTime icFracP R -- 7 new fractions.  Quite fast.

  R = make2'3 13
  elapsedTime R' = integralClosure R -- 5 sec
  icFractions R -- 13 new fractions
  use R
  radical conductor R
  elapsedTime icFracP R -- < 1 sec

  -- the following takes too long for a test
  -- R = make2'3 17
  -- elapsedTime R' = integralClosure R -- 17 sec
  -- icFractions R -- 17 new fractions
  -- use R
  -- radical conductor R
  -- elapsedTime icFracP R -- 4 sec
  ///


-*
-- YYY
-- TODO: determine if this is a bug.
  restart
  needsPackage "IntegralClosure2"
-- email from Doug Leonard, July 13, 2025, 8:28 pm
*-
TEST ///
  R=QQ[x,y,z];
  I=ideal(x^6+x^3*z+y^3*z^2);
  A=R/I;
  time ic0=integralClosure(A,Verbosity=>6)
  -- It looks like the fractions produced are:
  -- w_(0,0)=y^2z/x
  -- w_(1,0)=yz/x, w_(1,1)=y^2z/x^2,
  -- so w_(0,0) is no longer necessary, 
  -- w_(2,0)=(-x^3-z)/z
  -- Please explain why w_(1,0) disappeared!
  -- Doug

  use frac A -- w_(1,0) is indeed written in terms of w_(1,1) (and x^2*y).
   (y^2*z/x^2)^2 + y*z/x +  x^2*y == 0
  conductor A
///

-*
-- TODO: determine if this is a bug.
  restart
  needsPackage "IntegralClosure2"
-- Another email: 14 July 2025, 8:57 pm
*-
TEST ///
  loadPackage "QthPower";
  wt=matrix{{19,15,12,9,9},{12,9,9,9,0}};
  R=ZZ/2[z,y1,y2,x2,x1,Weights=>entries weightGrevlex(wt)];
  I=ideal(
    y1^2-y2*x2*x1,
    y1*y2-y1-x2^2*x1-x2*x1^2,
    y2^2-y2-y1*(x2+x1),
    z^3-(y2+y1)*(x2+1)*x1*z-(y2*(x2*x1+1)-y1*(x2+x1))*x2^2*x1);
  A=R/I;
  time ic0=integralClosure(A,Verbosity=>6)
  -- Again w_(1,0) and w_(1,1) are produced
  -- then w_(2,0) and w_(2,1) are produced
  -- but somehow w_(1,1) disappears
///


-*
-- BUG!!!!
  restart
  needsPackage "IntegralClosure2"
  --Doug said: Did I ask you about this before?
*-
TEST ///
  R=QQ[y,x];
  --R=ZZ/32003[y,x];
  b=(y^12-4*y^10*x+6*y^8*x^2-4*y^6*x^3+8*y^5*x^7+y^4*x^4+8*y^3*x^8-x^13);
  A=R/ideal(b)
  --elapsedTime A' = integralClosure(A, Verbosity => 6)
  elapsedTime A' = integralClosure A -- not short, but used to be a SERIOUS BUG
  conductor A
  icFractions A
  time G=gens gb ideal A';
  see ideal G
  toString G
  time icf=icFractions(A);
  toString icf
///

-- Same example as above, done partially.  Several examples below relate to this (current) bug.
-*
  restart
  needsPackage "IntegralClosure2"
*-
TEST ///
  errorDepth=0
  R=QQ[y,x];
  b=(y^12-4*y^10*x+6*y^8*x^2-4*y^6*x^3+8*y^5*x^7+y^4*x^4+8*y^3*x^8-x^13);
  A=R/ideal(b)
  A' = integralClosure(A, Verbosity => 6, Limit => 6)
  use A
  icFractions(A, Denominator => y^4 + 6*y^2*x + x^2)
  
  --The outputs (below) are clearly a mess, and not even close to being correct. Do you know why this was the answer?
  -- :
  --  {{x^3, y^2*x^2, y^4-16*y^2*x, 1280*w_(4,0)-37*y^3*x+85072*y*x^2,
  --      w_(4,1)*x, w_(4,1)*y-240*y*x^2, w_(4,4)*y, w_(4,4)*x^2-4*y^3*x+64*y*x^2,
  --      w_(4,3)*y-w_(4,4)*x+4*y^3-64*y*x, w_(4,3)*x^2, w_(4,2)*x-4000*y*x^2,
  --      4*w_(4,2)*y+5*w_(4,3)*x-320*x^2, w_(4,1)^2,
  --      w_(4,1)*w_(4,4)-952*y^3*x+15232*y*x^2, w_(4,1)*w_(4,3), w_(4,1)*w_(4,2),
  --      w_(4,4)^2, w_(4,3)*w_(4,4)-256*w_(4,4)*x+768*y^3-12288*y*x,
  --      w_(4,2)*w_(4,4), w_(4,3)^2-512*w_(4,3)*x-6144*w_(4,1)-256*y^2*x+1478656*x^
  --      2, 2*w_(4,2)*w_(4,3)+52885*y^3*x-1357520*y*x^2, w_(4,2)^2}}

  -- i6 : time icf=icFractions(A);
  -- used 1.3294e-05s (cpu); 9.17e-06s (thread); 0s (gc)

  -- i7 : toString icf

  -- o7 = {(37*y^3*x-85072*y*x^2)/1280,
  --    (y^3*x^6+5*y*x^7+96*y^2*x^3+16*x^4)/(y^4+6*y^2*x+x^2),
  --    (25*y^11+200*y^4*x^7-225*y^9*x+200*y^2*x^8+1375*y^7*x^2-400*x^9-7975*y^5*x
  --    ^3-67600*y^3*x^4-11600*y*x^5)/(25*y^4*x^2+150*y^2*x^3+25*x^4),
  --    (328125*y^11+2625000*y^4*x^7-1115625*y^9*x+9712500*y^2*x^8+1194375*y^7*x^2
  --    +840000*x^9-721875*y^5*x^3+5040000*y^3*x^4+24360000*y*x^5-840000*y^4+
  --    13440000*y^2*x)/(65625*y^3*x^3+380625*y*x^4+210000*y^2),
  --    (5*y^9*x+40*y^2*x^8-46*y^7*x^2-68*x^9+285*y^5*x^3-1660*y^3*x^4-336*y*x^5
  --    )/(x^5+20*y^3+4*y*x), y, x}
///

-*
  restart
  needsPackage "IntegralClosure2"
  -- this is investigating a bug in an example of Doug Leonard
*-
TEST /// -- of endomorphisms, and ringFromFractions
-- YYY
  debug needsPackage "IntegralClosure2"
  kk = QQ
  --kk = ZZ/32003
  S = kk[w_(3,0)..w_(3,3), y, x, Degrees => {2:5, 2:6, 2:1}, MonomialOrder => VerticalList{MonomialSize => 32, GRevLex => {2:5, 2:6}, 3:(GRevLex => {}), GRevLex => {2:1}, Position => Up}]
  I = ideal(
      x^13-y^12-8*y^5*x^7+4*y^10*x-8*y^3*x^8-6*y^8*x^2+4*y^6*x^3-y^4*x^4,
      w_(3,1)*y^4+6*w_(3,1)*y^2*x+w_(3,1)*x^2-y^2*x^7-x^8+96*y^3*x^3+16*y*x^4,
      w_(3,1)*x^6+20*w_(3,1)*y^3*x+4*w_(3,1)*y*x^2-y^10-8*y^3*x^7+9*y^8*x+12*y*x^8-55*y^6*x^2+319*y^4*x^3+64*y^2*x^4,
      w_(3,1)*y^2*x^4+5*w_(3,1)*x^5-16*w_(3,1)*y^3-x^11-4*y^8+80*y*x^7+40*y^6*x-260*y^4*x^2,
      4*w_(3,0)*x-w_(3,1)*y^3-5*w_(3,1)*y*x+y*x^7-96*y^2*x^3+80*x^4,
      4*w_(3,0)*y+w_(3,1)*y^2+w_(3,1)*x-x^7+96*y*x^3,
      4*w_(3,3)*y-w_(3,1)*y^2*x^2-5*w_(3,1)*x^3+x^9-96*y*x^5+4*y^4-64*y^2*x,
      w_(3,3)*x^2-4*w_(3,1)*y^2-y^7-4*x^7+10*y^5*x-64*y^3*x^2-16*y*x^3,
      w_(3,2)*x-20*w_(3,1)*y-5*y^6+51*y^4*x-336*y^2*x^2+80*x^3,
      w_(3,2)*y-5*w_(3,3)*x+20*x^6+y^5-16*y^3*x+160*y*x^2,
      w_(3,1)^2-8*w_(3,1)*y^3*x+32*w_(3,1)*y*x^2-y^8*x+14*y^6*x^2-129*y^4*x^3+256*y^2*x^4,
      w_(3,0)*w_(3,1)-13*w_(3,1)*y^2*x^2+15*w_(3,1)*x^3-y^7*x^2+5*x^9+15*y^5*x^3-144*y^3*x^4-80*y*x^5,
      w_(3,0)^2+12*w_(3,1)*y^3*x^2+52*w_(3,1)*y*x^3-12*y*x^9-y^6*x^3+16*y^4*x^4+992*y^2*x^5-400*x^6,
      w_(3,1)*w_(3,3)-8*w_(3,1)*x^5+81*w_(3,1)*y^3-16*w_(3,1)*y*x-y^5*x^5+15*y^3*x^6+20*y^8-64*y*x^7-200*y^6*x+1300*y^4*x^2,
      4*w_(3,0)*w_(3,3)+1109*w_(3,1)*y^2*x+145*w_(3,1)*x^2-4*y^4*x^6-32*y^9-192*y^2*x^7+400*y^7*x+175*x^8-2880*y^5*x^2+17488*y^3*x^3+3600*y*x^4,
      w_(3,1)*w_(3,2)+783*w_(3,1)*y^2*x+159*w_(3,1)*x^2-5*y^4*x^6-20*y^9-84*y^2*x^7+280*y^7*x-79*x^8-2100*y^5*x^2+12784*y^3*x^3+1264*y*x^4,
      w_(3,0)*w_(3,2)-56*w_(3,1)*y^3*x+503*w_(3,1)*y*x^2-5*y^3*x^7-20*y^8*x-23*y*x^8+300*y^6*x^2-2300*y^4*x^3+8688*y^2*x^4-1600*x^5,
      2*w_(3,3)^2-81*w_(3,1)*y^2*x^3-81*w_(3,1)*x^4-2*y^2*x^9-16*y^7*x^3-15*x^10+160*y^5*x^4-1040*y^3*x^5-1552*y*x^6-2*y^6+64*y^4*x-512*y^2*x^2,
      4*w_(3,2)*w_(3,3)-7*w_(3,1)*y^3*x^3-351*w_(3,1)*y*x^4-13*y*x^10-80*y^6*x^4+800*y^4*x^5-5872*y^2*x^6-4*y^7+1280*x^7+108*y^5*x-1024*y^3*x^2+5120*y*x^3,
      w_(3,2)^2+10*w_(3,1)*x^5-480*w_(3,1)*y^3+3200*w_(3,1)*y*x-25*x^11-40*y^3*x^6-121*y^8+160*y*x^7+2022*y^6*x-16081*y^4*x^2+53760*y^2*x^3-6400*x^4)
  R = S/I
  f = y^4+6*y^2*x+x^2
  radJ = ideal(y^4+6*y^2*x+x^2,
      x^5+20*y^3+4*y*x,
      y*x^4-116*y^2-20*x,
      5*y^2*x^3+29*x^4+16*y,
      80*w_(3,0)+w_(3,1)*x^4-96*w_(3,1)*y+400*y^2*x^2+2000*x^3,
      4*w_(3,3)+5*w_(3,1)*y^3*x+29*w_(3,1)*y*x^2-316*y^3-64*y*x,
      4*w_(3,2)+25*w_(3,1)*y^2*x^2+145*w_(3,1)*x^3-3268*y^2*x-4*x^2,
      29*w_(3,1)*y^3*x^2+169*w_(3,1)*y*x^3-16*w_(3,1))
  -- first step: is this correct:
  assert(f == radJ_0)
  (He1,f1) = endomorphisms(radJ,f);
  assert(((f*radJ):radJ) == ideal He1 + ideal f)
  fe = y^4+6*y^2*x+x^2
  He = matrix {{x^8+20*y^3*x^3+4*y*x^4, y^3*x^6+5*y*x^7+96*y^2*x^3+16*x^4, w_(3,1)*y*x^4-116*w_(3,1)*y^2-20*w_(3,1)*x+40*y^2*x^6+4*x^7-4560*y^3*x^2-784*y*x^3, 5*w_(3,1)*y^2*x^3+29*w_(3,1)*x^4+16*w_(3,1)*y+84*y^3*x^5+484*y*x^6+640*y^2*x^2+64*x^3, 4*w_(3,3)*x+5*w_(3,1)*y^3*x^2+29*w_(3,1)*y*x^3-20*y^2*x^5-100*x^6+4*y^3*x-64*y*x^2}}
  if char kk == 0 then assert(He1 == He)
  assert(f1 == fe)
  member(f, ideal He) -- OK.  endomorphisms removes it from the list of generators.  But what if it isn't a generator?
    -- TODO: 3/31/26: find an example of this...
  -- second step: is this correct?  (answer: no, if endomorphisms is correct.
  errorDepth=0
  F = ringFromFractions(He, fe, Variable=>symbol w, Index=>7);
  --see ideal gens gb ideal target F -- WRONG!!

  -- now we try out the parts of ringFromFractions
  H = He
  f = fe
  R = ring H;
  Hf = H | matrix{{f}};
  n = numgens source H
  assert(n == 5)
  newdegs = degrees source H - toList(n:degree f)
  if #newdegs#0 === 1 and any(newdegs, i -> i == {0})
    then newdegs = for d in newdegs list if first d > 0 then d else {1};
  degs = join(newdegs, (monoid R).Options.Degrees);
  assert(degs == {{4}, {5}, {6}, {6}, {6}, {5}, {5}, {6}, {6}, {1}, {1}})
  MO = prepend(GRevLex => n, (monoid R).Options.MonomialOrder);
  kk = coefficientRing R
  varm = symbol w
  A = kk(monoid [varm_(7,0)..varm_(7,n-1), R#generatorSymbols, -- 3/20/26: could use `gens ambient R`.
          MonomialOrder=>MO, Degrees => degs]);
  I = ideal presentation R;
  IA = ideal ((map(A,ring I,(vars A)_{n..numgens R + n-1})) (generators I));
  B = A/IA; -- this is sometimes a slow op
  varsB = (vars B)_{0..n-1}
  RtoB = map(B, R, (vars B)_{n..numgens R + n - 1})
  newfracs = for i from 0 to n-1 list (H_(0,i) / f)
  BtoK = map(frac R, B, matrix{newfracs} | (vars frac R))
  XX = varsB | matrix{{1_B}}
  syzHf = RtoB syz Hf; 
  lins = XX * syzHf;
  assert(BtoK lins == 0) -- linear equations are fine.
  sH = symmetricPower(2, H)
  IfHf = ideal(f * Hf)
  sH % IfHf == 0
  tails = sH // gens IfHf
  tails = RtoB tails
  quads = matrix(B, entries (symmetricPower(2,varsB) - XX * tails));
  assert(BtoK quads == 0) -- this is ok.
  fm = matrix{{f}}  -- divide sH by f:
    q = sH // fm
    sH - fm * q -- this should be 0!!
    sH % fm == 0
    tails2a = sH // fm
    rem = remainder(sH, fm)
    q = quotient(sH, fm)
    assert(rem == 0)
    assert(sH - fm * q == 0) -- FAILS!!
    sH - (sH + (sH % fm)) -- this should be zero!?
    degrees source fm , degrees target sH -- different!

    assert( (matrix{{f}} * tails2a) - sH == 0)
    tails := (symmetricPower(2,H) // f) // Hf;
    --3/4/26: if Hom(I,I) = R[a/f,1] then a^2/f^2 = c(a/f)+d, so a^2 = caf+df^2;
    --so (symmetricPower(2,H) // f)  = ca+df, and ca+df //Hf = (c,d).


  both := ideal lins + ideal quads;
	  
    gb both; -- sometimes slow
    Bflat := flattenRing (B/both); --sometimes very slow
    R1 := trim Bflat_0; -- sometimes slow

    -- Now construct the return value
    F := map(R1, R, (vars R1)_{n..numgens R + n - 1});
    F
  
///

-*
-- TODO: this should be a git issue, and needs to be addressed!!
  restart
  needsPackage "IntegralClosure2"
*-
TEST ///
  kk = QQ
  --kk = ZZ/32003
  S = kk[w_(3,0)..w_(3,3), y, x, Degrees => {2:5, 2:6, 2:1}, MonomialOrder => VerticalList{MonomialSize => 32, GRevLex => {2:5, 2:6}, 3:(GRevLex => {}), GRevLex => {2:1}, Position => Up}]
  I = ideal(
      x^13-y^12-8*y^5*x^7+4*y^10*x-8*y^3*x^8-6*y^8*x^2+4*y^6*x^3-y^4*x^4,
      w_(3,1)*y^4+6*w_(3,1)*y^2*x+w_(3,1)*x^2-y^2*x^7-x^8+96*y^3*x^3+16*y*x^4,
      w_(3,1)*x^6+20*w_(3,1)*y^3*x+4*w_(3,1)*y*x^2-y^10-8*y^3*x^7+9*y^8*x+12*y*x^8-55*y^6*x^2+319*y^4*x^3+64*y^2*x^4,
      w_(3,1)*y^2*x^4+5*w_(3,1)*x^5-16*w_(3,1)*y^3-x^11-4*y^8+80*y*x^7+40*y^6*x-260*y^4*x^2,
      4*w_(3,0)*x-w_(3,1)*y^3-5*w_(3,1)*y*x+y*x^7-96*y^2*x^3+80*x^4,
      4*w_(3,0)*y+w_(3,1)*y^2+w_(3,1)*x-x^7+96*y*x^3,
      4*w_(3,3)*y-w_(3,1)*y^2*x^2-5*w_(3,1)*x^3+x^9-96*y*x^5+4*y^4-64*y^2*x,
      w_(3,3)*x^2-4*w_(3,1)*y^2-y^7-4*x^7+10*y^5*x-64*y^3*x^2-16*y*x^3,
      w_(3,2)*x-20*w_(3,1)*y-5*y^6+51*y^4*x-336*y^2*x^2+80*x^3,
      w_(3,2)*y-5*w_(3,3)*x+20*x^6+y^5-16*y^3*x+160*y*x^2,
      w_(3,1)^2-8*w_(3,1)*y^3*x+32*w_(3,1)*y*x^2-y^8*x+14*y^6*x^2-129*y^4*x^3+256*y^2*x^4,
      w_(3,0)*w_(3,1)-13*w_(3,1)*y^2*x^2+15*w_(3,1)*x^3-y^7*x^2+5*x^9+15*y^5*x^3-144*y^3*x^4-80*y*x^5,
      w_(3,0)^2+12*w_(3,1)*y^3*x^2+52*w_(3,1)*y*x^3-12*y*x^9-y^6*x^3+16*y^4*x^4+992*y^2*x^5-400*x^6,
      w_(3,1)*w_(3,3)-8*w_(3,1)*x^5+81*w_(3,1)*y^3-16*w_(3,1)*y*x-y^5*x^5+15*y^3*x^6+20*y^8-64*y*x^7-200*y^6*x+1300*y^4*x^2,
      4*w_(3,0)*w_(3,3)+1109*w_(3,1)*y^2*x+145*w_(3,1)*x^2-4*y^4*x^6-32*y^9-192*y^2*x^7+400*y^7*x+175*x^8-2880*y^5*x^2+17488*y^3*x^3+3600*y*x^4,
      w_(3,1)*w_(3,2)+783*w_(3,1)*y^2*x+159*w_(3,1)*x^2-5*y^4*x^6-20*y^9-84*y^2*x^7+280*y^7*x-79*x^8-2100*y^5*x^2+12784*y^3*x^3+1264*y*x^4,
      w_(3,0)*w_(3,2)-56*w_(3,1)*y^3*x+503*w_(3,1)*y*x^2-5*y^3*x^7-20*y^8*x-23*y*x^8+300*y^6*x^2-2300*y^4*x^3+8688*y^2*x^4-1600*x^5,
      2*w_(3,3)^2-81*w_(3,1)*y^2*x^3-81*w_(3,1)*x^4-2*y^2*x^9-16*y^7*x^3-15*x^10+160*y^5*x^4-1040*y^3*x^5-1552*y*x^6-2*y^6+64*y^4*x-512*y^2*x^2,
      4*w_(3,2)*w_(3,3)-7*w_(3,1)*y^3*x^3-351*w_(3,1)*y*x^4-13*y*x^10-80*y^6*x^4+800*y^4*x^5-5872*y^2*x^6-4*y^7+1280*x^7+108*y^5*x-1024*y^3*x^2+5120*y*x^3,
      w_(3,2)^2+10*w_(3,1)*x^5-480*w_(3,1)*y^3+3200*w_(3,1)*y*x-25*x^11-40*y^3*x^6-121*y^8+160*y*x^7+2022*y^6*x-16081*y^4*x^2+53760*y^2*x^3-6400*x^4)
  R = S/I
  f = y^4+6*y^2*x+x^2
  H = matrix {{x^8+20*y^3*x^3+4*y*x^4, y^3*x^6+5*y*x^7+96*y^2*x^3+16*x^4, w_(3,1)*y*x^4-116*w_(3,1)*y^2-20*w_(3,1)*x+40*y^2*x^6+4*x^7-4560*y^3*x^2-784*y*x^3, 5*w_(3,1)*y^2*x^3+29*w_(3,1)*x^4+16*w_(3,1)*y+84*y^3*x^5+484*y*x^6+640*y^2*x^2+64*x^3, 4*w_(3,3)*x+5*w_(3,1)*y^3*x^2+29*w_(3,1)*y*x^3-20*y^2*x^5-100*x^6+4*y^3*x-64*y*x^2}}
  sH = symmetricPower(2, H)
  fm = matrix{{f}}
  assert(target sH === target fm)
  assert(sH % fm == 0)
  assert(remainder(sH, fm) == 0)
  q = sH // fm
  assert(source q === source sH)
  assert(source fm === target q)
  fmq = fm * q
  assert(fmq == sH) -- FAILS!!
  assert(source fmq === source sH) -- ok 
  assert(target fmq === target sH) -- ok
  Hf = H | fm
  IHf = ideal Hf
  IfHf = f * IHf
  fhfm = gens IfHf
  assert(sH % fhfm == 0) -- ok
  q2 = sH // fhfm
  assert(source q2 === source sH) -- ok
  assert(source fhfm === target q2) -- ok
  fhfmq = fhfm * q2
  assert(fhfmq == sH) -- OK!!
  assert(source fhfmq === source sH) -- ok 
  assert(target fhfmq === target sH) -- ok

  -- the change of basis matrix is screwed up...  We don't even need H...
  fm = ideal gens (G = gb(ideal f, ChangeMatrix => true))
  hm = getChangeMatrix G
  assert(hm_1 * f == fm_1) -- 2 of them are incorrect, this is the first one.

  -- let's lift up and do this over S
  fS = lift(f, S)
  f1 = ideal fS + I
  Gf1 = gb(f1, ChangeMatrix => true)
  gbf1 = gens Gf1
  ch1 = getChangeMatrix Gf1
  assert(gens f1 * ch1 - gbf1 == 0)
  see ideal gbf1
  (gbf1) % I
  gbf1 % I
  leadTerm gens gb I
  leadTerm Gf1

  w_(3,0) * f == fm_2
  w_(3,1) * f == fm_3
  w_(3,2) * f - fm_4
  f * flatten entries hm
  flatten entries gens G

  -- here is the first one that screws up:
  g = H_(0,1) * H_(0,4)
  g % f
  f * (g // f) - g
  G = gb(fm, ChangeMatrix => true)
  
  J = ideal lift(f, ambient R) + ideal R
  see ideal gens gb J
  (gens gb J) % (ideal R)
  -- let's get to the bottom of this!
  -- this makes it seem like a engine GB error...!
  gens gb fm
  see ideal oo
  fm = matrix entries gens fm
  G = gb(fm, ChangeMatrix => true)
  getChangeMatrix G
  q' = sH // G
  debug Core
  (a1,a2,a3) = rawGBMatrixLift(raw G, raw sH)
///

-*
  restart
  needsPackage "IntegralClosure2"
*-
TEST ///
  -- OK, appears ok over S.
  -- It is possibly a reduction issue since elements are represented by polys over ZZ.
  S = QQ[x,y,z]
  I = ideal(2*x^6-7*y^2)
  R = S/I
  f = ideal(x^4, 3*x^3*y-x*z)
  gbf = gens (G = gb(ideal f, ChangeMatrix => true))
  chf = getChangeMatrix G
  assert((gens f) * chf - gbf == 0)
///

-*
  restart
  needsPackage "IntegralClosure2"
*-
TEST /// -- for debugging the above problem, drilled down even more
-- YYY This is the one to debug right now!!
  kk = QQ
  S = kk[w_(3,0)..w_(3,3), y, x, Degrees => {2:5, 2:6, 2:1}, MonomialOrder => VerticalList{MonomialSize => 32, GRevLex => {2:5, 2:6}, 3:(GRevLex => {}), GRevLex => {2:1}, Position => Up}]
  I = ideal(
      x^13-y^12-8*y^5*x^7+4*y^10*x-8*y^3*x^8-6*y^8*x^2+4*y^6*x^3-y^4*x^4,
      w_(3,1)*y^4+6*w_(3,1)*y^2*x+w_(3,1)*x^2-y^2*x^7-x^8+96*y^3*x^3+16*y*x^4,
      w_(3,1)*x^6+20*w_(3,1)*y^3*x+4*w_(3,1)*y*x^2-y^10-8*y^3*x^7+9*y^8*x+12*y*x^8-55*y^6*x^2+319*y^4*x^3+64*y^2*x^4,
      w_(3,1)*y^2*x^4+5*w_(3,1)*x^5-16*w_(3,1)*y^3-x^11-4*y^8+80*y*x^7+40*y^6*x-260*y^4*x^2,
      4*w_(3,0)*x-w_(3,1)*y^3-5*w_(3,1)*y*x+y*x^7-96*y^2*x^3+80*x^4,
      4*w_(3,0)*y+w_(3,1)*y^2+w_(3,1)*x-x^7+96*y*x^3,
      4*w_(3,3)*y-w_(3,1)*y^2*x^2-5*w_(3,1)*x^3+x^9-96*y*x^5+4*y^4-64*y^2*x,
      w_(3,3)*x^2-4*w_(3,1)*y^2-y^7-4*x^7+10*y^5*x-64*y^3*x^2-16*y*x^3,
      w_(3,2)*x-20*w_(3,1)*y-5*y^6+51*y^4*x-336*y^2*x^2+80*x^3,
      w_(3,2)*y-5*w_(3,3)*x+20*x^6+y^5-16*y^3*x+160*y*x^2,
      w_(3,1)^2-8*w_(3,1)*y^3*x+32*w_(3,1)*y*x^2-y^8*x+14*y^6*x^2-129*y^4*x^3+256*y^2*x^4,
      w_(3,0)*w_(3,1)-13*w_(3,1)*y^2*x^2+15*w_(3,1)*x^3-y^7*x^2+5*x^9+15*y^5*x^3-144*y^3*x^4-80*y*x^5,
      w_(3,0)^2+12*w_(3,1)*y^3*x^2+52*w_(3,1)*y*x^3-12*y*x^9-y^6*x^3+16*y^4*x^4+992*y^2*x^5-400*x^6,
      w_(3,1)*w_(3,3)-8*w_(3,1)*x^5+81*w_(3,1)*y^3-16*w_(3,1)*y*x-y^5*x^5+15*y^3*x^6+20*y^8-64*y*x^7-200*y^6*x+1300*y^4*x^2,
      4*w_(3,0)*w_(3,3)+1109*w_(3,1)*y^2*x+145*w_(3,1)*x^2-4*y^4*x^6-32*y^9-192*y^2*x^7+400*y^7*x+175*x^8-2880*y^5*x^2+17488*y^3*x^3+3600*y*x^4,
      w_(3,1)*w_(3,2)+783*w_(3,1)*y^2*x+159*w_(3,1)*x^2-5*y^4*x^6-20*y^9-84*y^2*x^7+280*y^7*x-79*x^8-2100*y^5*x^2+12784*y^3*x^3+1264*y*x^4,
      w_(3,0)*w_(3,2)-56*w_(3,1)*y^3*x+503*w_(3,1)*y*x^2-5*y^3*x^7-20*y^8*x-23*y*x^8+300*y^6*x^2-2300*y^4*x^3+8688*y^2*x^4-1600*x^5,
      2*w_(3,3)^2-81*w_(3,1)*y^2*x^3-81*w_(3,1)*x^4-2*y^2*x^9-16*y^7*x^3-15*x^10+160*y^5*x^4-1040*y^3*x^5-1552*y*x^6-2*y^6+64*y^4*x-512*y^2*x^2,
      4*w_(3,2)*w_(3,3)-7*w_(3,1)*y^3*x^3-351*w_(3,1)*y*x^4-13*y*x^10-80*y^6*x^4+800*y^4*x^5-5872*y^2*x^6-4*y^7+1280*x^7+108*y^5*x-1024*y^3*x^2+5120*y*x^3,
      w_(3,2)^2+10*w_(3,1)*x^5-480*w_(3,1)*y^3+3200*w_(3,1)*y*x-25*x^11-40*y^3*x^6-121*y^8+160*y*x^7+2022*y^6*x-16081*y^4*x^2+53760*y^2*x^3-6400*x^4)
  R = S/I
  f = y^4+6*y^2*x+x^2
  H = matrix {{x^8+20*y^3*x^3+4*y*x^4, y^3*x^6+5*y*x^7+96*y^2*x^3+16*x^4, w_(3,1)*y*x^4-116*w_(3,1)*y^2-20*w_(3,1)*x+40*y^2*x^6+4*x^7-4560*y^3*x^2-784*y*x^3, 5*w_(3,1)*y^2*x^3+29*w_(3,1)*x^4+16*w_(3,1)*y+84*y^3*x^5+484*y*x^6+640*y^2*x^2+64*x^3, 4*w_(3,3)*x+5*w_(3,1)*y^3*x^2+29*w_(3,1)*y*x^3-20*y^2*x^5-100*x^6+4*y^3*x-64*y*x^2}}
  g = H_(0,1) * H_(0,4)
  fm = ideal f

  assert(g % f == 0)
  assert(f * (g // f) - g == 0) -- FAILS
  gbTrace=15
  G = gb(fm, ChangeMatrix => true)
  assert((gens G) - (gens fm * getChangeMatrix G) == 0) -- FAILS
  see ideal getChangeMatrix G
  see ideal leadTerm ideal R
///

-*
  restart
  needsPackage "IntegralClosure2"
*-
TEST /// -- bugs involving use_denom, denom, and ideals/modules over poly rings over QQ
-- what to check?
S = QQ[x,y]
I = ideal(3*x^3-y^2-y, y^4)
f = x^3 * I_0 + x*y*I_1
R = S/I
fR = promote(f, R)

see ideal gens gb ideal R
J = ideal(x^3)
///

-*
  restart
  needsPackage "IntegralClosure2"
   -- email from Doug 12 June 2024
*-
TEST ///
  needsPackage "QthPower";
  wt = matrix{{19,15,12,9,9},{12,9,9,9,0}};
  R2 = ZZ/2[z19,y15,y12,x9,u9,Weights=>entries(weightGrevlex(wt))];
  GB2 = {y15^2+y12*x9*u9,
       y15*y12+x9^2*u9+x9*u9^2+y15,
       y12^2+y15*x9+y15*u9+y12,
       z19^3+z19*(y15+y12)*(x9+1)*u9+(y15*(x9+u9)+y12*(x9*u9+1))*x9^2*u9};
   time ic2 = qthIntegralClosure(wt,R2,GB2); toString(ic2)

  A2=R2/ideal(GB2);

--TODO: improve this next call?
  -- elapsedTime icfp=icFracP A2; -- 42 sec
  --   toString icfp
  --1(unnecessary),f2624,f2924,f3224 (should be f2315x99),f3430

  -- Is this algorithm correct for char=2?
  elapsedTime A2' = integralClosure A2; -- .4 sec
  --pushFwd icMap A2
  --conductor A2 -- takes awhile!!  Why!?
  use A2
  elapsedTime icf2=icFractions(A2, Denominator => z19)
  
  toString icf2
  --f2624,f3430,f2315,(missing f2924),z1912,y159,y129,x99,u90

  time G2=gens gb ideal integralClosure A2;
  toString G2
///

-*
  restart
  needsPackage "IntegralClosure2"
  -- basic tests of makeS2
*-
TEST ///
  S = ZZ/101[symbol a .. symbol d]
  I = monomialCurveIdeal(S, {1,3,4})
  R = S/I
  canonicalIdeal R
  F = makeS2 R
  assert(conductor F == ideal(a,b,c,d))
  assert(source F === R)
  target F
  use R
  w = first icFractions(F, Denominator => b)
  assert(value numerator w == a*c)
  assert(value denominator w == b)
///
  
-*
  restart
  needsPackage "IntegralClosure2"
  -- test of makeS2, Wolmer's example
*-
TEST ///
  S = ZZ/101[symbol a..symbol e]
  I = ideal(a^2*b*c^2+b^2*c*d^2+a^2*d^2*e+a*b^2*e^2+c^2*d*e^2,
      a*b^3*c+b*c^3*d+a^3*b*e+c*d^3*e+a*d*e^3,
      a^5+b^5+c^5+d^5-5*a*b*c*d*e+e^5,
      a^3*b^2*c*d-b*c^2*d^4+a*b^2*c^3*e-b^5*d*e-d^6*e+3*a*b*c*d^2*e^2-a^2*b*e^4-d*e^6,
      a*b*c^5-b^4*c^2*d-2*a^2*b^2*c*d*e+a*c^3*d^2*e-a^4*d*e^2+b*c*d^2*e^3+a*b*e^5,
      a*b^2*c^4-b^5*c*d-a^2*b^3*d*e+2*a*b*c^2*d^2*e+a*d^4*e^2-a^2*b*c*e^3-c*d*e^5,
      b^6*c+b*c^6+a^2*b^4*e-3*a*b^2*c^2*d*e+c^4*d^2*e-a^3*c*d*e^2-a*b*d^3*e^2+b*c*e^5,
      a^4*b^2*c-a*b*c^2*d^3-a*b^5*e-b^3*c^2*d*e-a*d^5*e+2*a^2*b*c*d*e^2+c*d^2*e^4)
  R = S/I
  elapsedTime F = makeS2 R;
  R' = target F
  gens R' -- two new generators, both of degree 5.
  assert(numgens R' === 2 + numgens S)
  assert(flatten degrees R' === {5, 5, 1, 1, 1, 1, 1})
  use R
  assert(conductor F == ideal(a,b,c,d,e))
  use R
  ws = icFractions(F, Denominator => b)
  w = first ws
  assert(numerator w == a*d^4*e - c*d*e^4) -- this one happens to work out.
  assert(value denominator w == b)
  assert(value denominator ws_1 == b)
///

-*
-- XXX
  restart
  needsPackage "IntegralClosure2"
  --vanHoeij2
*-
TEST ///
  S = QQ[x,y]
  --S = QQ[x,y, MonomialOrder => Lex]
  --S = QQ[y,x, MonomialOrder => Lex]
  I = ideal"y20+y13x+x4y5+x3(x+1)2"
  R = S/I
  elapsedTime R' = integralClosure R
  -- elapsedTime R' = integralClosure(R, Verbosity => 6)
  see ideal R'

  elapsedTime conductor R
  icFractions R
  use R
  icFractions(icMap R, Denominator => y^13)
  icFractions(icMap R, Denominator => x^3+x^2)

  -- the following is for S = QQ[x,y].  Different monomial orders will have different values
  assert(numcols selectInSubring(1, vars R') == 4)
  assert(numcols selectInSubring(2, vars R') == 3)
  assert(numcols selectInSubring(3, vars R') == 2) -- x,y.
  assert(selectInSubring(4, vars R') == 0)  -- nothing
///



end-------------------------------------------------------------------------


-*
restart
loadPackage("IntegralClosure2",Reload =>true)

restart
uninstallPackage("IntegralClosure2")
restart
installPackage("IntegralClosure2")
check IntegralClosure2
viewHelp IntegralClosure2
*-

restart
uninstallPackage "IntegralClosure2"
restart
installPackage "IntegralClosure2"
check "IntegralClosure2" -- 3/19/2026: test 35 takes 42 sec, test 36 takes 36 sec (yes both same number!), test 40 takes 45 sec.

viewHelp IntegralClosure2
viewHelp integralClosure

needsPackage "IntegralClosure2"

loadPackage("IntegralClosure2", Reload=>true)
/// MIKETEST
  -- XXX
    R = ZZ/32003[x,y,z]
    f = y^4-2*x^3*y^2-4*x^5*y+x^6-x^7+z^4

    eulerIdeal = method()
    eulerIdeal RingElement := Ideal => (f) -> (
        R := ring f;
        I := ideal jacobian ideal f;
        ideal apply(numgens R, i -> R_i * I_i)
        )

    localIsQuasiHomogeneous = method()
    localIsQuasiHomogeneous RingElement := Boolean => f -> (
        mm := ideal vars ring f;
        f % (f * mm + (ideal jacobian ideal f)) == 0
        )

    assert not localIsQuasiHomogeneous f    

    -- now get the Rees ideal of the Euler ideal
    I = eulerIdeal f
    J = reesIdeal(I, I_0, Variable => w)
    J = first flattenRing J
    A = (ring J)/J
    integralClosure(A, Strategy => {SimplifyFractions}, Verbosity => 4);
    integralClosure(A, Verbosity => 4);
///


TEST ///
  -- MES TODO: put assertions in here
  S = QQ[y,x,MonomialOrder=>Lex]
  F = poly"y5-y2+x3+x4"
  factor discriminant(F,y)
  R=S/F
  R' = integralClosure R
  icFractions R
  describe R'
///

TEST ///
  -- of idealizer
  -- MES TODO: add assertions
  S = QQ[y,x,MonomialOrder=>Lex]
  F = poly"y4-y2+x3+x4"
  factor discriminant(F,y)
  R=S/F
  L = trim radical ideal(x_R)
  (f1,g1) = idealizer(L,L_0)
  U = target f1
  K = frac R
  f1
  g1
  L = trim ideal jacobian R

  R' = integralClosure R
  icFractions R
  icMap R
///



-- Tests that Mike has added:
needsPackage "IntegralClosure2"
S = ZZ/101[a..d]
I = ideal(b^2-b)
R = S/I
integralClosure(R)

-- 
kk = QQ
R = kk[x,y,z, MonomialOrder => Lex]
p1 = ideal"x,y,z"
p2 = ideal"x,y-1,z-2"
p3 = ideal"x-2,y,5,z"
p4 = ideal"x+1,y+1,z+1"
D = trim intersect(p1^3,p2^3,p3^3,p4^3)
betti D
B = basis(4,D)
F = (super(B * random(source B, R^{-4})))_(0,0)
ideal F + ideal jacobian matrix{{F}}
decompose oo

factor F
A = R/F
needsPackage "IntegralClosure2"

ideal F + ideal jacobian matrix{{F}}
decompose oo
-------------------

kk = ZZ/101
R = kk[x,y,z]
p1 = ideal"x,y,z"
p2 = ideal"x,y-1,z-2"
p3 = ideal"x-2,y,5,z"
p4 = ideal"x+1,y+1"
D = trim intersect(p1^3,p2^3,p3^3,p4^2)
betti D
B = basis(5,D)
F = (super(B * random(source B, R^{-5})))_(0,0)
factor F
A = R/F
JF = trim(ideal F + ideal jacobian matrix{{F}})
codim JF
radJF = radical(JF, Strategy=>Unmixed)
NNL = radJF
NNL = substitute(NNL,A)
(phi,fracs) = idealizer(NNL,NNL_0)
phi
#fracs

----------------------

kk = ZZ/101
R = kk[x,y,z]
p1 = ideal"x,y,z"
p2 = ideal"x,y-1,z-2"
p3 = ideal"x-2,y,5,z"
p4 = ideal"x+1,y+1"
D = trim intersect(p1^3,p2^3,p3^3,p4^3)
betti D
F = random(6,D)
factor F
A = R/F
JF = trim(ideal F + ideal jacobian matrix{{F}})
codim JF
radJF = radical(JF, Strategy=>Unmixed)
decompose radJF
elapsedTime integralClosure A -- MES TODO: 19 May 2020: 4.94 seconds on my MBP

---------------------- Birational Work
-- MES TODO: what is this block of code testing?
R = ZZ/101[b_1, x,y,z, MonomialOrder => {GRevLex => {7}, GRevLex=>{2,5,6}}]
R = ZZ/101[x,y,z]
S = R[b_1, b_0]
I = ideal(b_1*x^2-42*y*z, x^6+12*b_1*y+ x^3*z, b_1^2 - 47*x^4*z - 47*x*z^2)
I = ideal(b_1*x-42*b_0, b_0*x-y*z, x^6+12*b_1*y+ x^3*z, b_1^2 -47*x^4*z - 47*x*z^2, b_0^2-x^6*z - x^4*z^2)
leadTerm gens gb I

R = ZZ/101[x,y,z]/(z*y^2-x^5*z-x^8)
J = integralClosure(R)
R.icFractions
describe J


S=ZZ/101[symbol x,symbol y,symbol z,MonomialOrder => Lex]
I=ideal(x^6-z^6-y^2*z^4)
Q=S/I
time J = integralClosure (Q, Variable => symbol a)


S = ZZ/101[a_7,a_6,x,y,z, MonomialOrder => {GRevLex => 2, GRevLex => 3}]
Inew = ideal(x^2-a_6*z,a_6*x-a_7*z,a_6^2-a_7*x,a_7^2-y^2-z^2)
leadTerm gens gb Inew
radical ideal oo


///
-*
  restart
  loadPackage"IntegralClosure2"
*-
  R=ZZ/2[x,y,Weights=>{{8,9},{0,1}}]
  I=ideal(y^8+y^2*x^3+x^9) -- eliminates x and y at some point. 
  A = R/I
  elapsedTime A' = integralClosure(A, Verbosity => 1) -- MES TODO: the ideal is messy, also: is the answer correct, given ZZ/2??

  R=ZZ/2[x,y,Weights=>{{31,12},{0,1}}]
  I=ideal"y12+y11+y10x2+y8x9+x31" -- really long, should it really be this bad?
  A = R/I
  elapsedTime A' = integralClosure(A, Verbosity => 1) -- MES TODO: pretty bad timing
  transpose gens ideal A'
///

--------------
-- Examples --
--------------
-*
Theorem (Saito): If R is a formal power series ring over a field of char 0, 
and f has isolated singularity,
then f\in R is contained in j(f), the Jacobian ideal iff f is
quasi-homogeneous after a change of variables.

Theorem (Lejeune-Teisser?; see Swanson-Huneke Thm 7.1.5) 
f \in integral closure(ideal apply(numgens R,i-> x_i*df/dx_i))

Conjecture (Huneke: f is never a minimal generator of the integral closure of
ideal apply(numgens R,i-> df/dx_i).

--the method (testHunekeQuestion, Ring, RingElement) checks this
viewHelp testHunekeQuestion
*-
debug IntegralClosure2 -- for testHunekeQuestion
n = 3
R = QQ[x_0..x_(n-1)]
mm = ideal vars R
f = random({3},R)+random({4},R)+random(5,R)
testHunekeQuestion f

    R = ZZ/32003[x,y,z]
    f = (y^4-2*x^3*y^2-4*x^5*y+x^6-x^7+z^4)
    --    testHunekeQuestion(R,f) -- currently too slow	   


--from Eisenbud-Neumann p.11: simplest poly with 2 characteristic pairs. 
R = QQ[y,x]
f = (y^4-2*x^3*y^2-4*x^5*y+x^6-x^7)
testHunekeQuestion f
R = R/f
time R' = integralClosure R
icFractions R
icMap R

R = QQ[y,x]/(y^2-x^4-x^7)
integralClosure R
icFractions R
icMap R

R = QQ[x,y]/(y^4-2*x^3*y^2-4*x^5*y+x^6-x^7)
time R' = integralClosure R 
icFractions R
icMap R

R = ZZ/32003[x,y,z]/(z^3*y^4-2*x^3*y^2*z^2-4*x^5*y*z+x^6*z-x^7)
isHomogeneous R
time R' = integralClosure R
icFractions R
icMap R

kk = ZZ/32003
S = kk[v,u]
I=ideal(5*v^6+7*v^2*u^4+6*u^6+21*v^2*u^3+12*u^5+21*v^2*u^2+6*u^4+7*v^2*u)
R = S/I
time R' = integralClosure R
ideal R'
icFractions R
conductor icMap R -- can't do it since not homogeneous

-- Doug Leonard example ----------------------
restart
S=ZZ/2[z19,y15,y12,x9,u9,MonomialOrder=>{Weights=>{19,15,12,9,9},Weights=>{12,9,9,9,0},1,2,2}]

I = ideal(
     y15^2+y12*x9*u9,
     y15*y12+x9^2*u9+x9*u9^2+y15,
     y12^2+y15*x9+y15*u9+y12,
     z19^3+y12*x9^3*u9^2+z19*y15*x9*u9+y15*x9^3*u9+y15*x9^2*u9^2
       +z19*y12*x9*u9+z19*y15*u9+z19*y12*u9+y12*x9^2*u9)

isHomogeneous I
R = S/I;

time icFractions R -- MES TODO: correct? better basis choice?
errorDepth=0
time A = icFracP R -- MES TODO: pretty long
time A = integralClosure R;
----------------------------------------------
-- Another example from Doug Leonard
S = ZZ/2[z19,y15,y12,x9,u9,MonomialOrder=>{Weights=>{19,15,12,9,9},Weights=>{12,9,9,9,0},1,2,2}]
I = ideal(y15^3+x9*u9*y15+x9^3*u9^2+x9^2*u9^3,y15^2+y12*x9*u9,z19^3+(y12+y15)*(x9+1)*u9*z19+(y12*(x9*u9+1)+y15*(x9+u9))*x9^2*u9)
R = S/I
time A = integralClosure R;

S = ZZ/2[z19,y15,y12,x9,u9,MonomialOrder=>{Weights=>{19,15,12,9,9},Weights=>{12,9,9,9,0},1,2,2}]
I = ideal(
     y15^2+y12*x9*u9,
     y15*y12+x9^2*u9+x9*u9^2+y15,
     y12^2+y15*x9+y15*u9+y12,
     z19^3+y12*x9^3*u9^2+z19*y15*x9*u9+y15*x9^3*u9+y15*x9^2*u9^2
       +z19*y12*x9*u9+z19*y15*u9+z19*y12*u9+y12*x9^2*u9)
isHomogeneous I
R = S/I;
time A = integralClosure R;

errorDepth=0
time A = icFracP R
time A = integralClosure R;
icFractions R
----------------------------------------------
restart
load "IntegralClosure2.m2"
S = ZZ/32003[x,y];
F = (y^2-3/4*y-15/17)^3-9*y*(y^2-3/4*y-15/17*x)-27*x^11
R = S/F
time R' = integralClosure R
assert(R === R')
use ring F
factor discriminant(F,y)
factor discriminant(F,x)
----------------------------------------------

restart
load "IntegralClosure2.m2"

S=ZZ/2[x,y,Weights=>{{8,9},{0,1}}]
I=ideal(y^8+y^2*x^3+x^9) -- eliminates x and y at some point. 
R=S/I
time R'=integralClosure(R, Strategy => {StartWithOneMinor})--, Verbosity =>3 )
time R'=integralClosure(R)--, Verbosity =>3)
icFractions R

S=ZZ/2[x,y,Weights=>{{31,12},{0,1}}]
I=ideal"y12+y11+y10x2+y8x9+x31" 
R = S/I
time R'=integralClosure(R) -- really long?
transpose gens ideal S

S=ZZ/2[x,y]
I=ideal"y12+y11+y10x2+y8x9+x31" 
R = S/I
time R'=integralClosure(R) -- really long?
transpose gens ideal S
icFracP R -- very much faster!
----------------------------------------------

-- MES TODO: this doesn't run.
restart
-- in IntegralClosure2 dir:
load "IntegralClosure2/runexamples.m2"
runExamples(H,10,Verbosity=>3)


restart
load "IntegralClosure2.m2"
kk = QQ
S = kk[x,y,u]
R = S/(u^2-x^3*y^3)
time integralClosure R

-- another example from Doug Leonard ----------------------------
S=ZZ/2[z,y,x,MonomialOrder=>{Weights=>{32,21,14}}];
I=ideal(z^7+x^5*(x+1)^5*(x^2+x+1)^3,y^2+y*x+x*(x^2+x+1));
R=S/I;
time P=presentation(integralClosure(R));    -- used 4.73 seconds
toString(gens gb P)

-- MES TODO: FractionalIdeals is not here!
loadPackage "FractionalIdeals"
S=ZZ/2[z,y,x,MonomialOrder=>{2,1}];
I=ideal(z^7+x^5*(x+1)^5*(x^2+x+1)^3,y^2+y*x+x*(x^2+x+1));
R=S/I;
time integralClosureHypersurface(R) -- doesn't work yet
use R
time integralClosureDenominator(R,x^16+x^14+x^13+x^11+x^10+x^8+x^7+x^5)
-----------------------------------------------------------------

///
R = ZZ/101[a,b,c,Degrees=>{{1,1,0},{1,0,0},{0,0,2}}]
L = {2,2,null}
basisOfDegreeD({2,null,2}, S)

S = ZZ/101[vars(0..10), Degrees => {{2, 6}, {1, 3}, {1, 3}, {1, 3}, {1, 3}, {0, 1}, {0, 1}, {0, 1}, {0, 1}, {0, 1}, {0, 1}}]
basisOfDegreeD({2,null}, S)
///



--start of file "bug-integralClosure.m2"



--family of inhomogeneous examples suggested by craig:
--integral dependence of a power series on its derivatives.
restart
--needs "bug-integralClosure.m2"
kk = ZZ/101
S = kk[a,b]
mm = ideal vars S
T = kk[t]
f = (ker map(T,S,{t^4,t^6+t^7}))_0
R = S/f
R' = integralClosure R
vars R'
see ideal R'
netList (ideal R')_*
--the simplest plane curve singularity with 2 characteristic pairs,
--thus NOT quasi-homogeneous.
--f could be any polynomial, preferably inhomogeneous, since then it's not obvious.
I = ideal diff(vars S,f)
assert(f%(I+f*mm)!=0)--f is not even locally in I
J = integralClosure I
assert(f%J != 0)--f is not in the integral closure of I; but 
assert(f % (J+f*mm) == 0) --f IS locally in the integral closure of I

IR' = sub (I, R')
elapsedTime integralClosure (IR', Verbosity => 4)
---------------------------
--examples made with Dedekind-Mertens theorem
--Dedekind-Mertens example
--Let c(f,x) be the content of f with respect to the variable x. 
--Theorem: c(f,x)*c(g,x) is integral over c(f*g, x).
restart
loadPackage ("IntegralClosure2", Reload=>true)
setRandomSeed 0
kk = QQ
S = kk[a,b,c]
f = random(2,S)
g = random(3,S)
f' = f-sub(f, {S_0=>0,S_2=>0})
g' = g-sub(g, {S_0=>0,S_2=>0})
If = content(f',S_1)
Ig = content(g',S_1)
Ifg = content(f'*g',S_1)
assert((gens(If*Ig) % Ifg)!=0)
assert(gens(If*Ig) % integralClosure Ifg == 0)


setRandomSeed 0
kk = ZZ/32003
S = kk[a,b,c,d]
phi = map(S,S,{S_0}|toList((numgens S -1):0))
f = random(4,S)
g = random(4,S)
f' = f- phi f
g' = g- phi g
If = content(f',S_0)
Ig = content(g',S_0)
--Ig = content(g'^2,S_0)

Ifg = content(f'*g',S_0)
assert((gens(If*Ig) % Ifg)!=0)
elapsedTime assert(gens(If*Ig) % integralClosure(Ifg, Verbosity => 4) == 0)
--slow in extendIdeal!
--bug when minPrimes is used.

setRandomSeed 0
kk = ZZ/32003
S = kk[a,b,c]
phi = map(S,S,{S_0}|toList((numgens S -1):0))
f = random(4,S)
g = random(4,S)
f' = f- phi f
g' = g- phi g
If = content(f'^2,S_0)
Ig = content(g'^2,S_0)
Ifg = content(f'^2*g'^2,S_0)
assert((gens(If*Ig) % Ifg)!=0)
assert(gens(If*Ig) % integralClosure Ifg == 0)


setRandomSeed 0
kk = ZZ/32003
S = kk[a,b,c,d]
phi = map(S,S,{S_0}|toList((numgens S -1):0))
f = random(3,S)
g = random(4,S)
f' = f- phi f
g' = g- phi g
If = content(f',S_0)
Ig = content(g',S_0)
--Ig = content(g'^2,S_0)

Ifg = content(f'*g',S_0)
assert((gens(If*Ig) % Ifg)!=0)
elapsedTime assert(gens(If*Ig) % integralClosure(Ifg, Verbosity => 4) == 0)
elapsedTime integralClosure Ifg


-- MES: this is me playing around trying to find better fractions, can be removed.
use ring ideal R'
contract(w_(2,0), gens ideal R')
ideal R'

use R'
use R
f = y^3 + 6*y^2 - 16*y
g = 2*x-y
(ideal g) : (ideal f)

-- eliminate: error: expected a polynomial ring over ZZ or a field
denoms = (ideal g) : (ideal f)
lift(denoms, ambient R)
eliminate(oo, S_1)
radical((ideal g) : (ideal f))
lift(oo, S)
ideal gens gb oo
eliminate(oo, S_1)

-- write it with denominator x^3*(x+4)
((x^3*(x+4) * f)) // g
----- MES: can be removed above this line --

restart
loadPackage("IntegralClosure2", Reload => true)
needsPackage "Normaliz"

-- Bug in program.  Perhaps the missing variable is causing issues?
R = ZZ/101[x,y,z]
I = ideal(y^2-x^3)
normalToricRing(I, t) -- gives an error.

-- How does the following give me any info about the integral closure?
-- (It probably does, but how?)
R = ZZ/101[x,y]
I = ideal(y^2-x^3)
normalToricRing(I, t)

-- This is correct, how can I get the actual fractions added?
-- Can I?  Or the image of R in this new ring?
R = ZZ/101[a,b,c,d]
I = monomialCurveIdeal(R, {1,3,4})
normalToricRing(I, t)

----- below this line: TODO --------------------------------------------------------------

-*TODO next: 
documentation (strategies); 

StartWithOneMinor
*AllCodimensions
*RadicalCodimOne
Radical
pSimplifyFractions

StartWithS2

Vasconcelos??

ConductorElement??

correctness; makeS2; 
use Normaliz where possible?; 
FastMinors?
*-

--- Should Singh/Swanson be an option to integralClosure or its own
--- program.  Right now it is well documented on its own.  I'm not
--- sure what is best long term. 

-- MES TODO. The following are either to be removed or placed above.
--     "canonicalIdeal", 
--     "parametersInIdeal",
--     "randomMinors",
     "endomorphisms",
     "vasconcelos",
     "Endomorphisms", -- compute end(I)
     "Vasconcelos", -- compute end(I^-1).  If both this and Endomorphisms are set:
                 -- compare them.
     "StartWithS2", -- compute S2-ification first
     "RecomputeJacobian",
     "S2First", 
     "S2Last", 
     "S2None", -- when to do S2-ification
     "RadicalBuiltin" -- true: use 'intersect decompose' to get radical, other wise use 'rad' in PrimaryDecomposition package

