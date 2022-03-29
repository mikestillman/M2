newPackage(
        "NoetherNormalization",
        Version => "0.9", 
        Date => "17 January 2022",
        Authors => {
            {Name => "David Eisenbud", 
                Email => "de@msri.org", 
                HomePage => "http://www.msri.org/~de/"},
            {Name => "Mike Stillman", 
                Email => "mike@math.cornell.edu", 
                HomePage => "http://www.math.cornell.edu/~mike"},
	        {Name => "Bart Snapp", 
                Email => "snapp@math.ohio-state.edu", 
                HomePage => "http://www.math.ohio-state.edu/~snapp/"},
            {Name => "Nathaniel Stapleton", 
                Email => "nstaple2@math.uiuc.edu"}
            },
        Headline => "Noether normalizations",
        PackageExports => {
            "PushForward" -- for 'isModuleFinite'
            },
        DebuggingMode => true
        )

export {
--    "checkNoetherNormalization", -- TODO: get this to work?
    "inNoetherForm", -- remove?
    "isNoetherRing",
    "hasNoetherRing",
    "noetherMap",
    "noetherRing",
    "noetherNormalization",

    "noetherBasis",
    "noetherBasisMatrix",
    "multiplicationMap",
    "traceForm",
    "homogeneousLinearParameters",    
    -- keys used:
    "NoetherInfo",
    "Remove",
    "CheckDomain",
    "MaxTries"
    }
export{"noetherNormalizationData","LimitList","RandomRange"}
----------------------------------------------------------------
-- The following 3 lines: probably should be in m2/enginering.m2?
raw = value Core#"private dictionary"#"raw"
rawIsField = value Core#"private dictionary"#"rawIsField"
isField EngineRing := R -> (R.?isField and R.isField) or rawIsField raw R
----------------------------------------------------------------

noetherNormalization = method(Options => {
        Remove => null, 
        Variable => getSymbol "t", 
        CheckDomain => false
        })

--inNoetherForm
-- this function isn't used locally, instead the internal function `noetherInfo` is used.
inNoetherForm = method()
inNoetherForm Ring := Boolean => (R) -> R.?NoetherInfo

noetherRing = method(Options => options noetherNormalization)
noetherRing Ring := Ring => opts -> R -> (
    if not R.?noetherRing then 
        noetherNormalization(R, opts); -- this will set R.noetherRing
    R.noetherRing    
    )

hasNoetherRing = method()
hasNoetherRing Ring := Boolean => R -> R.?noetherRing

isNoetherRing = method()
isNoetherRing Ring := Boolean => (B) -> B.?NoetherInfo and B.NoetherInfo#"ring" === B

-- private routine
-- NoetherInfo (placed into both B, frac B):
-- keys:
--   "ring"
--   "field"
--   "basis of ring" -- really, a generating set, over coefficient ring
--   "basis of field" -- generating set, over coefficient field
--   "traces" -- of the basis of the field
--   "field trace form"
--   "ring trace form"
--   "noether map" -- isomorphism back to the original ring.
setNoetherInfo = method()
setNoetherInfo(Ring, Ring) := (B, KB) -> (
    -- this is meant to also handle the case B === KB.
    NI := new MutableHashTable;
    B.NoetherInfo = NI;
    KB.NoetherInfo = NI;
    NI#"ring" = B;
    NI#"field" = KB;
    -- Other fields are set on demand.
    )

-- private routine
noetherInfo = method()
noetherInfo Ring := MutableHashTable => (R) -> (
    if not R.?NoetherInfo
    then error "expected a ring or field created with `noetherNormalization`";
    R.NoetherInfo
    )

noetherMap = method()
noetherMap Ring := Ring => (B) -> (
    if B.?noetherRing then B = B.noetherRing;
    NI := noetherInfo B;
    NI#"noether map"
    )

computeBasis = method()
computeBasis Ring := Matrix => (R) -> (
    -- assumption: R is finite over the coefficient ring
    -- returns  B: matrix of module generators of R over its coeff ring
    -- This just does the computation, does not stash anything!
    LT := leadTerm ideal R;
    K := ultimate(coefficientRing, R);
    R1 := K (monoid R);
    J := ideal sub(LT,R1);
    B := sub(cover basis(comodule J), R);
    -- now present this in two ways:
    -- (1) as a list of monomials in R (or, as a matrix?)
    -- (2) as a hash table, m => i, giving the index of each monomial.
    B = sort B;
--    L := flatten entries B;
--    H := hashTable for i from 0 to #L-1 list L#i => i;
--    Rambient := ambient R;
--    S := new MutableHashTable from apply(L, s -> {lift(s,Rambient),s});
    B
    )

-- The following sets (or gets, if already computed) the
-- basis of the ring over its coefficient ring, assuming that
-- the ring has been placed in Noether normal form.
basisOfRing = method()
basisOfRing Ring := (R) -> (
    -- assumption: R is finite over the coefficient ring
    -- returns a matrix over R whose entries are generators
    -- of R over the coeff ring
    NI := noetherInfo R;
    if not NI#?"basis of ring" then NI#"basis of ring" = computeBasis NI#"ring";
    if not NI#?"basis of field" then NI#"basis of field" = computeBasis NI#"field";
    if R === NI#"ring" then  NI#"basis of ring"
    else if R === NI#"field" then NI#"basis of field"
    else error "internal error in basisOfRing"
    )

noetherBasis = method()
noetherBasis Ring := List => (R) -> first entries (basisOfRing R)

noetherBasisMatrix = method()
noetherBasisMatrix Ring := Matrix => (R) -> basisOfRing R

multiplicationMap = method()
multiplicationMap RingElement := (m) -> (
     R := ring m;
     S := noetherBasisMatrix R;
     (mn, cf) := coefficients(m * S, Monomials => S);
     lift(cf,coefficientRing R)
     )

-- private function.  Sets the traces for the basis of the noether field.
-- mostly for use in 'trace RingElement'.
getTraces = (NI) -> (
    if not NI#?"traces" then NI#"traces" = (
        RK := NI#"field";
        B := noetherBasis RK;
        traces := for b in B list trace multiplicationMap b;
        matrix{traces}
        );
    NI#"traces"
    )

-- trace f
-- Assumptions: f is in either a noether ring R or noether field RK = frac R.
-- result is in the coefficient ring of the ring of f.
-- Traces are computed as traces of the map over a field, and then, if the element is over the
--  noether ring, the element is lifted to the coefficient ring.
trace RingElement := (f) -> (
    R := ring f;
    NI := noetherInfo R;
    RK := NI#"field";
    traces := getTraces NI;
    if R =!= RK then f = promote(f,RK);
    M := lift(last coefficients(f, Monomials => noetherBasisMatrix RK), coefficientRing RK);
    g := (traces * M)_(0,0);
    if R =!= RK then g = lift(g, coefficientRing R);
    g
    )

computeTraceForm = method()
computeTraceForm Ring := (R) -> (
    S := noetherBasis R;
    K := coefficientRing R;
    M := mutableMatrix(K, #S, #S);
    for i from 0 to #S-1 do
    for j from i to #S-1 do (
        f := trace(S#i * S#j);
        M_(i,j) = M_(j,i) = f;
        );
    matrix M
    )

traceForm = method()
traceForm Ring := (R) -> (
    NI := noetherInfo R;
    if not NI#?"ring trace form" then NI#"ring trace form" = computeTraceForm NI#"ring";
    if not NI#?"field trace form" then NI#"field trace form" = computeTraceForm NI#"field";
    if R === NI#"ring" then NI#"ring trace form"
    else if R === NI#"field" then NI#"field trace form"
    else error "internal error in traceForm"
    )

-- TODO: is this what we want?
isComputablePolynomialRing = method()
isComputablePolynomialRing Ring := Boolean => R ->(
    --checks whether R is suitable as coefficientRing for a Noether normalization
    --In the future we might want a broader class, for example poly ring over poly ring or a fraction field.
    if not isPolynomialRing R then return false;
    k := coefficientRing R;
    isAffineRing R and
    isField k and
    precision k === infinity and -- eliminates approximate fields RR, CC 
    not instance(k, FractionField)
    )



-- TODO
checkNoetherNormalization = method()
checkNoetherNormalization RingMap := Boolean => (phi) -> (
    -- phi : A --> R
    -- check: 
    --   A is a polynomial ring over a field.
    --   phi(each var) is a linear form in R
    --   R is a quotient of a polynomial ring over the same field or over A.
    --   R is finite over A.
    )

-- TODO
checkNoetherNormalization Ring := Boolean => (B) -> (
    -- check that 
    --   B is a ring of the form A[x's]/I
    --   B is finite over A
    -- if so:
    --   set frac B? (using makeFrac)
    --   set NoetherInfo in B, frac B.
    if not isModuleFinite B
    then error "ring is not in the proper form (set 'debugLevel>0' for details)";
    )


makeFrac = method()
makeFrac Ring := Ring => (B) -> (
    -- If the user has somehow already set the fraction field of B (generally as an engine ring)
    -- then should we silently change that, or give an error?  Right now, we give an error.
    if not isModuleFinite B then
        error "expected the ring to be finite over the chosen polynomial ring";
    A := coefficientRing B; -- ASSUME: a polynomial ring over a field.
    KA := frac A;
    
    if KA =!= A then (
        if B.?frac then <<"warning: ring had a fraction field; creating simpler fraction field"<<endl;
    	kk := coefficientRing A; -- must be a field, but not a fraction field.
    	I := ideal B;
    	ambientB := ring I;
    	ambientKB := ((frac A)(monoid B)); -- TODO: does this handle degrees correctly?
    	phiK := map(ambientKB,ambientB, vars ambientKB);
    	JK := trim phiK I;
    	KB := ambientKB / JK;
        KB.baseRings = append(KB.baseRings, B)
        )
     else ( 
        -- in this case, B is finite over a field.  We basically assume it is a field here.
        -- even if it isn't we treat it as such.  I think we will not create a non-invertible
        -- element in B.
        KB = B;
        B.frac = B;
        B.isField = true; -- ASSUMPTION: this is not correct, if we are dealing with a reduced ring...!
    	I = ideal B;
    	ambientB = ring I;
        --fraction(B,B) := (f,g) -> (BtoKB f) * inverse g;
        --fraction(KB,KB) := (f,g) -> f * inverse g;
        --promote(B, KB) := (f,KB) -> BtoKB f;
        -- todo: factorization?
        numerator B := f -> f;
        denominator B := f -> 1_B;
        B / B := (a,b) -> a * (1 // b);
        inverse B := f -> 1 // f;
        factor B := opts -> (f) -> hold f; -- TODO: call this factorDenominator?
        setNoetherInfo(B, KB); -- watch out!
        return KB;
        );

    -- At this point: A =!= KA
    -- B will not be KB.  But we want to set frac B to be (frac A) **_A B.
    B.frac = KB;
    KB.frac = KB;
    KB.isField = true;
    BtoKB := map(KB,B,generators KB);
    inverse B := f -> 1_KB // BtoKB f;
    inverse KB := f -> 1 // f;
    fraction(B,B) := (f,g) -> (BtoKB f) * inverse g;
    fraction(KB,KB) := (f,g) -> f * inverse g;
    promote(B, KB) := (f,KB) -> BtoKB f;
    KA + B := (f,g) -> f + BtoKB g;
    B + KA := (f,g) -> BtoKB f + g;
    KA - B := (f,g) -> f - BtoKB g;
    B - KA := (f,g) -> BtoKB f - g;
    KA * B := (f,g) -> f * BtoKB g;
    B * KA := (f,g) -> BtoKB f * g;
    KA % B := (f,g) -> f % BtoKB g;
    B % KA := (f,g) -> BtoKB f % g;
    KA // B := (f,g) -> f // BtoKB g;
    B // KA := (f,g) -> BtoKB f // g;

    -- Now we consider factorization.  The plan is to factor (numerator and denominator if needed)
    -- over a polynomial ring, then bring back to B or KB
    (flattenedB, mapBtoFlattenedB) := flattenRing ambientB;
    S := ambient flattenedB; -- this is the polynomial ring where we will factor elements...
    mapBtofracS := map(frac S, B); -- TODO: does this do a 'sub'?
    mapKBtofracS := map(frac S, KB); -- TODO: does this do a 'sub'?
    StoB := map(B, S);
--error here when the ground field is a GF
--error "debug me";
    numerator B := (f) -> StoB (numerator mapBtofracS f);
    denominator B := (f) -> lift(StoB denominator mapBtofracS f, A);
    numerator KB := (f) -> StoB (numerator mapKBtofracS f);
    denominator KB := (f) -> lift(StoB denominator mapKBtofracS f, A);
    factor KB := opts -> (f) -> hold numerator f/factor denominator f;
    expression KB := f -> expression numerator f / expression denominator f;
    setNoetherInfo(B, KB);
    KB
    )



-- This workaround sets the inverse of the isomorphism phi, in the case
-- when the coefficient ring of source ring is not the coefficient ring of the target ring.
-- It is currently assumed, I think, that the target ring's coefficient ring is the
-- same as the coeff ring of the flattened ring of the source.
workAroundInverse = method()
workAroundInverse RingMap := (phi) -> (
    B := source phi;
    R := target phi;
    (B'', F) := flattenRing B;
    phi.cache.inverse = F^-1 * (phi * F^-1)^-1;
    phi.cache.inverse.cache.inverse = phi;
    --assert(phi^-1 * phi === id_B); -- TODO: make sure these are the same?  The matrices are different sometimes only with degrees.
    --assert(phi * phi^-1 === id_R); -- TODO: same
    )

createCoefficientRing = method(Options => {Variable => getSymbol "t"})
createCoefficientRing(Ring, List) := RingMap => opts -> (R, L) -> (
    count := -1;
    t := opts.Variable;
    coeffVarNames := for f in L list (
        if index f =!= null then 
            f 
        else (
            count = count+1;
            t_count
            )
        );
    A := (coefficientRing R)(monoid [coeffVarNames]);
    map(R, A, L)
    )

-- From the ring map f: A --> R (created from createCoefficientRing(Ring, List), or given by the user
--  check (perhaps): ker = 0, 
--  create a new ring, isomorphic to R (stash isomorphisms too), of the form A[new vars]/I.
-- This is what the following function is supposed to do.  But it should give errors that are reasonabe.
-- The following is currently hideous code to do something simple.
  createRingPair = method()
  createRingPair RingMap := RingMap => (f) -> (
      -- Given f : A --> R (R a polynomial ring) (A,R polynomial rings)
      -- create a ring B = A[new vars]/I, and an isomorphism R --> B.
      --   preferably, the ideal I has no linear forms of the "new vars".
      -- Return a ring map phi: R --> B
      A := source f;
      R := target f;
      if isField A or A === ZZ then return id_R;
      
      kk := coefficientRing A;
      nR := numgens R;
      lins := positions(flatten entries f.matrix, g -> (exponents g)/sum//max == 1);
      -- create the matrix over the base: of size #elems of A x (numgens R + numgens A)
      monsR := reverse append(gens R, 1_R);
      (mons, cfs) := coefficients(f.matrix, Monomials => monsR);
      ev0 := map(kk, R, toList((numgens R) : 0));
      cfs = map((ring cfs)^(numrows cfs),,cfs); -- clear out the degree information so 'lift' 
        -- in this next line succeeds.
      M1 := -id_(kk^#lins) || ev0 cfs_lins; -- lift(cfs_lins, kk); -- BUG: this last part fails if cfs_lines is in multigraded ring?
      M := gens gb M1;
      inM := leadTerm M;
      inM0 := submatrix(inM, {#lins+1 .. numrows M - 1},);
      -- keepIndices: indices of variables in R we will keep in B
      -- removeIndices: indices of variables in R that we will map to a linear poly.
      --   for i, the variable (in R) with index removeIndices#i will map to newlins#i (in B)
      removeIndices := apply(transpose entries inM0, x -> nR - 1 - position(x, x1 -> x1 != 0));
      keepIndices := sort toList ((set(0..nR-1)) - set removeIndices);
      B := A[(gens R)_keepIndices, Join => false];
      monsB := (vars A)_lins | matrix{{1_B}} | matrix {reverse for i from 0 to nR-1 list (
          if member(i, keepIndices) then B_((position(keepIndices, a -> a == i))) else 0_B
          )};
      newlins := flatten entries(monsB * (inM - M));
      images := new MutableList from gens R;
      for i from 0 to numgens B - 1 do images#(keepIndices#i) = B_i;
      for i from 0 to #newlins-1 do images#(removeIndices#i) = newlins#i;
      -- now make the map R --> B
      RtoB := map(B, R, toList images);
      BtoR := map(R, B, ((vars R)_keepIndices | f.matrix)); -- TODO: these are not quite inverses if f.matrix has non-linear terms...
      RtoB.cache.inverse = BtoR;
      BtoR.cache.inverse = RtoB;
      BtoR
      )

noetherNormalization Ring := RingMap => opts -> R -> (
    -- case 1: R is already in Noether form: finite over its coeff ring.
    --   In this case, set NoetherInfo, map to/from R is the identity
    -- case 2: not the case.
    --   Compute random linear forms (if not too low of characteristic).
    --   make a list L of these, call noetherNormalization L.

    A := coefficientRing R;
    
    if (isPolynomialRing A or isField A) and isModuleFinite R then (
	KR := makeFrac R; -- do this?
	setNoetherInfo(R,KR);
	R.NoetherInfo#"noether map" = map(R,R);
        R.noetherRing = R;
	return map(R,A)
        );
    
    -- get the flattened coeff ring of R.
    -- use the flattened ring to get elements.    
    (F, J, xv) := noetherNormalizationData R;
    kk := coefficientRing R;
    t := opts.Variable;
    A = if #xv == 0 then kk else kk[t_0..t_(#xv-1)];
    phi := map(R,A,for x in xv list F^-1 x);
    noetherNormalization phi
    )

noetherNormalization(Ring, List) := RingMap => opts -> (R, L) -> (
    -- check that ring R of all elements is the same
    if #L === 0 then 
        error "expected non-empty list of ring elements";
    if any(L, f -> not instance(f, RingElement)) then 
        error "expected non-empty list of ring elements";
    if not all(L, f -> ring f === R) then
        error "expected elements in the same ring";
    f := createCoefficientRing(R, L, Variable => opts.Variable);
    noetherNormalization f
    )

noetherNormalization RingMap := RingMap => opts -> f -> (
    if not isModuleFinite f then
        error "expected map or elements which make ring finite over the base";
    -- check that f is module finite
    -- if f : A --> R has A = cofficient ring of R, then set noether info in R and return it.
    -- otherwise:
    --   determine what variables from R to keep in B over A.
    --   construct ambientB = A[these vars]
    --             J inside ambientB
    --             B = ambientB/J
    --             isomorphism from R to B, vice versa.
    --             
    F := createRingPair f;
    G := inverse F;
    -- now we need to descend this to R --> B = ambientB/(image of I)
    R := source G;
    I := trim ker F;
    B := (target G)/I;
    L := makeFrac B;
    -- Now create the isomorphism B --> R and its inverse.
    GR := map(B, R, G.matrix);
    FR := map(R, B, F.matrix);
    GR.cache.inverse = FR;
    FR.cache.inverse = GR;
    B.NoetherInfo#"noether map" = FR; -- stash the map B --> R, but the other can be obtained via 'inverse'
    R.noetherRing = B;
    f
    )

noetherRing(Ring, List) := Ring => opts -> (R, L) -> (
    noetherNormalization(R, L, opts);
    noetherRing R
    )

noetherRing RingMap := Ring => opts -> f -> (
    noetherNormalization(f, opts);
    noetherRing target f
    )

--Code from old NoetherNormalization package
-- The algorithm given here is based on A. Logar's algorithm as given
-- in:

-- A. Logar. A Computational Proof of the Noether Normalization
-- Lemma. In: Proceedings 6th AAEEC, Lecture Notes in Computer Science
-- 357, Springer, 1989, 259--273.

-- an additional algorithm was implemented from:

-- H. Kredel and V. Weispfenning. Computing Dimension and Independent
-- sets for Polynomial Ideals. J. Symbolic Computation (1988) 6,
-- 231--247.


--=========================================================================--
-- initial comments: noetherNormalizationData takes an ideal I of a ring R
-- over a field k such that the dimension of I in R is d (fix these
-- symbols for all comments) and returns 1) a linear transformation
-- that puts the ideal in Noether position and 2) the independent
-- variables of R

-----------------------------------------------------------------------------

integralSet = G -> (
     J := {};
     M := gens G;
     for i from 0 to numgens source M - 1 do ( -- check the gens of G to see if their leadMonomial is in a single variable
           if # support leadMonomial (M)_(0,i) === 1 then J = J | {support leadMonomial (M)_(0,i)} --checks how many vars are in the lead
           );
     J = unique flatten J; --note that according to the algorithm J is a set of integers (in fact indices), we choose to return the variables
     J);

-- comments: The procedure integralSet takes a Groebner basis G (ie a
-- list of polynomials) and returns the variables that already have an
-- integral relation. It does this by taking the lead monomial of each
-- polynomial and checking whether or not it consists of a power of a
-- single variable. We are assuming that the ring is over a field and
-- thus we don't check the lead coefficient.

-----------------------------------------------------------------------------

varPrep = (X,I) -> (
     U := support (independentSets(I,Limit => 1))_0;
     (U,X - set U)
     );
-- comments: varPrep is the initial function we run on the Groebner
-- basis of the inputted ideal I. It returns sets U and V, with U
-- being algebraically independent and V being algebraically
-- dependent. For all prime ideals it returns a maximal algebraically
-- independent set of variables whose cardinality is equal to d.

-----------------------------------------------------------------------------

lastCheck = (X,G,d) -> (
     M := gens G;
     i := 0;
     while i < numgens source M and not isSubset(support M_(0,i),toList(X_{0..d-1})) do ( 
	  i = i+1;
	  );
     if i != numgens source M then return false
     else(
     	  if X_{d..#X-1} != integralSet(G) then return false
	  );
     true
     );

-- comments: We use lastCheck to check that our final Groebner basis
-- (the gb of the ideal after the change of variables) witnesses the
-- integrality of each variable that should be integral. It first
-- checks that there are no elements of the Groebner basis with
-- support in the independent variables and then that each variable
-- that should be integral after the linear transformation is
-- integral.


-----------------------------------------------------------------------------

inverseSequence = (U,X) -> (
     N := {};
     for i to #X - 1 do (
	  for j to #U - 1 do (
	       if X_i == U_j then (
		    N = {X_j}|N;
		    break;
		    );
	       );
	  );
     return N;
     );

-- comments: inverseSequence is used to give the inverse of a ring
-- map. A ring map is given by a list explaining where each of the
-- ring's variables should go. If the ring map is just a permutation
-- of the variables then it is obviously an isomorphism and
-- inverseSequence returns the sequence that gives the inverse
-- morphism.


-----------------------------------------------------------------------------

randomSum = (U,V,k,rr) -> (
     for j to #V - 1 do (
	  if rr == 0 then 
	  U = apply(U, i -> i + random(k)*V_j) else 
	  U = apply(U, i -> i + random(-rr,rr)*V_j);
	  );
     return U;
     );


-- comments: randomSum is used to make the random linear
-- transformations which are candidates for putting I in
-- noetherPosition. It takes in two lists and adds the second to the
-- first with random coefficients.

-----------------------------------------------------------------------------

-- comments: noetherNormalizationData is the main method. An ideal I is
-- passed to it and its Groebner basis is immediately computed.  Next
-- a random linear transformation is applied and we check to see if
-- the ideal is in Noether position. We then check to see if the the
-- ideal in Noether position by partially computing a Groebner basis
-- for the ideal. If the partially computed Groebner basis witnesses
-- the integrality of all of the dependent variables, we are done, if
-- not we try again.  If the entire Groebner basis is computed and the
-- integrality is never witnessed then we apply another random linear
-- transformation and start the process again. 

noetherNormalizationData = method(Options => {Verbose => false, LimitList => {5,20,40,60,80,infinity}, RandomRange => 0})
noetherNormalizationData(Ideal) := opts -> I -> (
     A := ring I;
     (flatA,fAtoFlatA) := flattenRing A;
     fFlatAtoA := fAtoFlatA^-1;
--   (flatA,fAtoFlatA,fFlatAtoA) := flattenRing A;
     if not isPolynomialRing A then error "expected an ideal over a polynomial ring";
     k := coefficientRing flatA;
     if not isField k then error "expected the ring to contain a field";
     R := k (monoid [gens flatA,MonomialOrder => Lex]);
     ff := map(R,flatA,gens R)*fAtoFlatA; --these maps merely change the order of the ring
     ffinverse := fFlatAtoA*map(flatA, R, gens flatA); --these maps merely change the order of the ring
     I = ff(I);
     G := gb I;
     d := dim I;
     X := sort gens R;
     (U,V) := varPrep(X,I);
     counter := 1; --counts the number of times lastCheck is called
     limitsequence := opts.LimitList; -- {5,20,40,60,80,infinity}; -- this is for the basiselementlimit setting for computing gb and is based on experience (and nothing else)
     done := false;
     indep := U;
     f := map(R,R,inverseSequence(U|V,X));
     finverse := map(R,R, reverse(U|V));
     J := apply(integralSet G,i -> f i); -- may need to do a gb comp.
     V = apply(V, i -> f(i)); --there might be a faster way to do this, perhaps V={x_(#U)..x_(#U+#V-1)}
     U = apply(U, i -> f(i)); -- might be faster to do U = {x_0..x_(#U-1)}
     Uold := U;
     while not done do ( 
     	  if opts.Verbose then << "--trying random transformation: " << counter << endl;
	  seqindex := 0;
     	  stuff := Uold;
	  rr := opts.RandomRange;
     	  if counter == 0 then U = randomSum(U,V-set J,k,rr);
	  if counter >= 1 then U = randomSum(U,V-set integralSet(G),k,rr);
	  stuff = stuff + (stuff - U);
    	  g := map(R,R,reverse(U|V));
	  ginverse := map(R,R,reverse(stuff|V));
	  f = g*f;
	  finverse = finverse*ginverse;
     	  while (not done and seqindex < #limitsequence) do (
	       if opts.Verbose then (<< "--trying with basis element limit: " << limitsequence_seqindex << endl;);
	       fI := f I;
	       G = gb(fI, BasisElementLimit => limitsequence_seqindex); 
	       done = lastCheck(X,G,d);-- may want to define f I above, but this causes noetherNormalizationData to fail at the moment
     	       seqindex = seqindex + 1;
	       );
	  if counter == 5 then << "--warning: no good linear transformation found by noetherNormalizationData" <<endl;
	  if done or counter == 5 then(
	       ffinal := ffinverse*f*ff;
	       ffinalInverse := ffinverse*finverse*ff;	     	  
	       ffinal.cache.inverse = ffinalInverse;
               ffinalInverse.cache.inverse = ffinal;
	       X = apply(X, i -> ffinverse i);   	       
	     --  return (ffinal, ffinverse f I,map(A, k[X_{0..d-1}], X_{0..d-1}));
	       return (ffinal, ffinverse f I,X_{0..d-1});
	       );
	  counter = counter + 1;
     	  ); -- f puts the ideal into noether normal position. f inverse goes back to the original ring 
     );  

-----------------------------------------------------------------------------

noetherNormalizationData(QuotientRing) := noetherNormalizationData(PolynomialRing) := opts -> R -> (
     if not isPolynomialRing ring ideal R then error "expected a quotient of a polynomial ring";
     noetherNormalizationData(ideal R, Verbose => opts.Verbose)
     );


--=========================================================================--
homogeneousLinearParameters = method(Options =>{Prefix =>{}})
homogeneousLinearParameters Ring := List => o -> S -> (
    if not isHomogeneous S then error "not appropriate function";
    if #unique degrees S>1 then error "need all vars of same degree";
    --we'd like to use a heft vector making all degrees equal
    --we're assuming that its a flattened ring.
    prefix := o.Prefix;
    d := dim S;
    restvars := gens S - set prefix;
    i := 1;
    L :=   sum\subsets(restvars, i);
    while i <= #restvars and #prefix < d do(
	  for s in L do(
	      if codim ideal (p' := append(prefix, s)) > # prefix then prefix = p';
	      if #prefix == d then return prefix
	   );
        i = i+1; 
        L = sum\subsets(restvars, i);
	);
    prefix
    )
homogeneousLinearParameters(Ring, List) := List => o -> (S,Candidates) ->
    for P in Candidates list homogeneousLinearParameters(S, Prefix => P)

candidateParameters = method()
candidateParameters Ring := List => S ->(
    candidates := findParameters1 S;
    homogeneousLinearParameters(S, candidates)
    )
findParameters1 = method(Options => {MaxTries => 5})
findParameters1 Ring := List => o -> S ->(
    -- find beginning of a NN for S
    -- consisting of variables.
    L := gens S;
    d := dim S;
    ss := elapsedTime subsets L;
    ns := #ss;
    tries := 0;
    sss := while tries < o.MaxTries list(
	s := ss_(random(ns));
	if #s > d or codim ideal s =!= #s then continue;
	tries = tries+1;
	s
	);
    m := max (sss/(s -> #s));
    select(sss, s -> #s ===m)
    )

findIndeterminantParameters = method(Options => {MaxTries => 5})
findIndeterminantParameters Ring := List => o -> S ->(
    -- find beginning of a NN for S
    -- consisting of variables.
    L := gens S;
    d := dim S;
    sz := 1;
    while sz <= d do (
        -- TODO
        );
    -- REMOVE:
    ss := elapsedTime subsets L;
    ns := #ss;
    tries := 0;
    sss := while tries < o.MaxTries list(
	s := ss_(random(ns));
	if #s > d or codim ideal s =!= #s then continue;
	tries = tries+1;
	s
	);
    m := max (sss/(s -> #s));
    select(sss, s -> #s ===m)
    )
///
restart
debug loadPackage "NoetherNormalization"
  kk = ZZ/101
  R = kk[a,b,c,d]
  I = ideal"a2,ab,cd,d2"
  S = reesAlgebra I
  S = first flattenRing S
  T = newRing(S, Degrees => {numgens S:1})
isHomogeneous T
degrees S
findParameters1 T
homogeneousLinearParameters T
netList candidateParameters T
///
///
restart
debug loadPackage "NoetherNormalization"
  kk = ZZ/101
  n = 5
  R = kk[vars(0..2*n-1)]
  m = genericMatrix(R,a,2,n)
  I = minors(2,m)
  S = reesAlgebra I
  S = first flattenRing S
  T = newRing(S, Degrees => {numgens S:1})
isHomogeneous T
degrees S
elapsedTime findParameters1 (T, MaxTries => 100)
homogeneousLinearParameters T
elapsedTime netList (pp= candidateParameters T)
#pp
p = pp_0
p = elapsedTime homogeneousLinearParameters T
tally (pp/(p ->sum (size\p)))


--elapsedTime noetherNormalizationData T

-- first try one element
goodL = for x in gens T list (
    if codim ideal x =!= 1 then continue else x
    )
-- in this example, these are all the variables.
elapsedTime L2 = subsets(goodL, 2);
elapsedTime M2 = for x in L2 list (
    if codim ideal x =!= 2 then continue else x
    );
elapsedTime bad2 = for x in L2 list (
    if codim ideal x === 2 then continue else x
    );
elapsedTime L3 = subsets(goodL, 3);
elapsedTime M3 = for x in L3 list (
    if codim ideal x =!= #x then continue else x
    );

elapsedTime L4 = subsets(goodL, 4);
elapsedTime M4 = for x in L4 list (
    if codim ideal x =!= #x then continue else x
    );

elapsedTime L5 = subsets(goodL, 5);
elapsedTime M5 = for x in L5 list (
    if codim ideal x =!= #x then continue else x
    );

elapsedTime L6 = subsets(goodL, 6);
elapsedTime M6 = for x in L6 list (
    if codim ideal x =!= #x then continue else x
    );
-- nothing here.  Time to move up to sums of 2 variables.

L2s = (subsets(gens T, 2))/sum;
count = 0;
elapsedTime M6 = flatten for x in M5 list (
    count = count + 1;
    << "." << flush;
    if count % 100 == 0 then << endl;
    for y in L2s list (
        xy := append(x, y);
        if codim ideal xy =!= #xy then continue else xy
        )    
    );

///
beginDocumentation()

doc ///
  Key
    NoetherNormalization
  Headline
    code for Noether normal forms of affine domains
  Description
    Text
///

///
  Consequences
    Item
      The following fields are set in {\tt R}:
    Item
      The following fields are set in {\tt B}:
    Item
      The following fields are set in {\tt L = frac B}:
///

doc ///
  Key
    noetherNormalization
    (noetherNormalization, Ring, List)
    (noetherNormalization, RingMap)
    (noetherNormalization, Ring)
    [noetherNormalization, CheckDomain]
    [noetherNormalization, Variable]
    [noetherNormalization, Remove]
  Headline
    create a polynomial ring in Noether normal form
  Usage
    f = noetherNormalization phi
    f = noetherNormalization(R, xv)
    f = noetherNormalization R
  Inputs
    phi:RingMap
      from a ring {\tt A} to a ring {\tt R}
    R:Ring
      an affine domain
    xv:List
      of variables in an affine ring {\tt R} over which {\tt R} is finite
    CheckDomain => Boolean
      if true then returns an error if R is not a domain
    Variable => String
      name of new indexed variables
    Remove => Boolean
      whether to remove extraneous existing variables
  Outputs
    f:RingMap
      an injective ring map from a polynomial ring $A$ to the ring $R$, such that
      $R$ is module finite over $A$
  Description
    Text
     A Noether normalization of a domain R is an injective ring map f from a polynomial
     ring A to R such that R becomes (module-)finite over A.
      
     It is convenient to have an isomorphic copy B of $R$ such that A = coefficientRing B.
     The program also creates such a ring B. It can be obtained as {\tt noetherRing R},
     and an isomorphism $B\to R$ can be obtained as {\tt noetherMap B} or 
     {\tt noetherMap R}.
     
     In the form {\tt noetherNormalization phi}, A is the source of phi.
     Otherwise, A is created. Its variables may be some of the variables of R,
     and new indexed variables corresponding to linear combinations of variables of R.
     
     The fraction field of B is represented as a finite extension of the fraction 
     field of A, a useful simplification.
     One advantage of having a noether normalization is that it allows the construction
     of the fraction field of R to be put in a form that is more convenient for
     certain computations.
     

    Example
      C = QQ[x,y]/(y^2 - x^2*(x-1))
      f = noetherNormalization C -- map from poly ring A to C
      A = source f
      C === target f
      B = noetherRing C 
      noetherBasis B
      A === coefficientRing B
      g = noetherMap B
      source g === B
      target g === C
      h = g^(-1)
      L = frac B
      noetherBasis L
      frac A === coefficientRing L
      --Booleans:
      isNoetherRing B
      B === noetherRing C
      hasNoetherRing C
      --isNoethered C

    Example
      S = ZZ/32003[a..d]
      I = monomialCurveIdeal(S, {1,3,4})
      R = S/I
      f = noetherNormalization R -- map from poly ring A to C
      A = source f
      R === target f
      B = noetherRing R
      noetherBasis B
      A === coefficientRing B
      g = noetherMap B
      source g === B
      target g === R
      h = g^(-1)
      L = frac B
      noetherBasis L
      frac A === coefficientRing L
      --Booleans:
      isNoetherRing B
      B === noetherRing R
      hasNoetherRing R

    Example
      S = ZZ/32003[a..d]
      I = monomialCurveIdeal(S, {1,3,4})
      R = S/I
      f = noetherNormalization(R, {a, d})
      A = source f
      R === target f
      B = noetherRing R
      noetherBasis B
      A === coefficientRing B
      g = noetherMap B
      source g === B
      target g === R
      h = g^(-1)
      L = frac B
      noetherBasis L
      frac A === coefficientRing L
      --Booleans:
      isNoetherRing B
      B === noetherRing R
      hasNoetherRing R

    Example
      S = ZZ/32003[a..d]
      I = monomialCurveIdeal(S, {1,3,4})
      R = S/I
      f = noetherNormalization(R, {a^2, d^2-a})
      A = source f
      R === target f
      B = noetherRing R
      noetherBasis B
      A === coefficientRing B
      g = noetherMap B
      source g === B
      target g === R
      h = g^(-1)
      L = frac B
      noetherBasis L
      frac A === coefficientRing L
      --Booleans:
      isNoetherRing B
      B === noetherRing R
      hasNoetherRing R

    Example
      kk = ZZ/101
      A = kk[t]
      R = kk[x,y]/(y^4-x*y^3-(x^2+1)*y-x^6)
      phi = map(R,A,{R_0})
      phi === noetherNormalization phi
      B = noetherRing R
    Text
     In case the ring R is reduced, this program does produce a Noether normalization B,
     but L = frac B may not be a field, and computations in L may be erroneous.
     This is why we have aimed at the case when R is a domain.
    Example
      kk = ZZ/101
      x = symbol x
      y = symbol y
      R = kk[x,y,z]/(ideal(x*y, x*z, y*z))
      A = kk[t]
      phi = map(R,A,{R_0+R_1+R_2})
      B = noetherRing phi
      L = frac B
      use L 
      1/y -- note that the returned answer 0 is incorrect.
    Example
      kk = ZZ/101
      R = kk[a,b,c]/(a*b,a*c)
      B = noetherRing (R, Variable => s)
      A = coefficientRing B
      noetherMap B
      frac B
      gens A
      
  Caveat
    The base field must currently be a finite field, or the rationals.

    The input ring must be a domain, which may be checked by setting CheckDomain => true
    (the default is CheckDomain => false to avoid the expense of the procedure.)

    The routine noetherNormalization R fails if it does not find dim R 
    linear forms such that R is finite over the ring they generate.
    
    
  SeeAlso
   noetherRing
   (noetherBasis, Ring)
   (noetherMap, Ring)
   (traceForm, Ring)
///

doc ///
  Key
    noetherBasis
    (noetherBasis, Ring)
  Headline
    basis over coefficient ring of ring in Noether form
  Usage
    noetherBasis R
  Inputs
    R:Ring
  Outputs
    :Matrix
  Description
    Text
    Example
      kk = ZZ/101
      R = kk[x,y,z]/(y^4-x*y^3-(x^2+1)*y-x^6, z^3-x*z-x)
      f = noetherNormalization(R, {x})
      B = noetherRing R
      noetherBasis B
      noetherBasis frac B
      use frac B
      assert(multiplicationMap(y^3) == (multiplicationMap y)^3)
      trace(y^3)
  Caveat
    One must have created this ring with @TO noetherNormalization@.
  SeeAlso
    noetherNormalization
    (inNoetherForm, Ring)
    (noetherBasis, Ring)
    (multiplicationMap, RingElement)
///

doc ///
  Key
    multiplicationMap
    (multiplicationMap, RingElement)
  Headline
    matrix of multiplication by an element
  Usage
    multiplicationMap f
  Inputs
    f:RingElement
  Outputs
    :Matrix
  Description
    Text
      Given a ring...
    Example
      S = QQ[a..d];
      I = monomialCurveIdeal(S, {1,3,4})
      R = S/I
      use R
      noetherNormalization(R, {a,d})
      use R
      B = noetherRing(R, {a, d})
      describe B
      bas = noetherBasis B
      bas/ring
    Example
      basKB = noetherBasis frac B
    Text
      The trace form is only defined for the fraction field?
      Where is the result defined?
    Example
      A = coefficientRing B
      KA = coefficientRing frac B
      assert(KA === frac A)
      traceForm frac B
      det oo
    Text
  Caveat
    One must have created this ring with @TO noetherNormalization@.
  SeeAlso
    noetherNormalization
    (inNoetherForm, Ring)
    (noetherBasis, Ring)
    (trace, RingElement)
    (traceForm, Ring)
///

doc ///
  Key
    traceForm
    (traceForm, Ring)
  Headline
    trace form matrix of ring created using noetherNormalization
  Usage
    traceForm R
  Inputs
    R:Ring
  Outputs
    :Matrix
  Description
    Text
  Caveat
    One must have created this ring with @TO noetherNormalization@.
  SeeAlso
    noetherNormalization
    (inNoetherForm, Ring)
    (noetherBasis, Ring)
    (multiplicationMap, RingElement)
///

doc ///
  Key
    (trace, RingElement)
  Headline
    trace of an element in a ring or field in Noether normal form
  Usage
    trace f
  Inputs
    f:RingElement
  Outputs
    :RingElement
  Description
    Text
    Example
      S = ZZ/101[a..d]
      I = monomialCurveIdeal(S, {1,3,4})
      R = S/I
      B = noetherRing(R, {a, d})
      bas = noetherBasis B
      bas/trace
      bas = noetherBasis frac B
      bas/trace
      use B
      trace(b*c)
      use frac B
      trace(b*c)
      traceForm frac B
      traceForm B
  Caveat
    One must have created this ring with @TO noetherNormalization@.
  SeeAlso
    noetherNormalization
    (inNoetherForm, Ring)
    (noetherBasis, Ring)
    (multiplicationMap, RingElement)
///

doc ///
  Key
    inNoetherForm
    (inNoetherForm, Ring)
  Headline
    whether the ring was created using noetherNormalization
  Usage
    inNoetherForm R
  Inputs
    R:Ring
  Outputs
    :Boolean
  Description
    Text
  Caveat
    This function only checks whether the ring was created using @TO noetherNormalization@, not
    whether it really is in Noether normal form
  SeeAlso
    noetherNormalization
///
-*
document { 
     Key => "NoetherNormalization",
     Headline => "routines related to Noether normalization",
     EM "NoetherNormalization", " is a package for computing ring homomorphisms 
     which will place ideals in Noether normal position. The algorithms
     used are based on algorithms found in A. Logar's paper: A
     Computational Proof of the Noether Normalization Lemma. In:
     Proceedings 6th AAEEC, Lecture Notes in Computer Science 357,
     Springer, 1989, 259-273."
     }
*-
doc ///
  Key
    noetherNormalizationData
    (noetherNormalizationData,Ideal)
    (noetherNormalizationData,QuotientRing)
    (noetherNormalizationData,PolynomialRing)
    LimitList
    RandomRange
    [noetherNormalizationData,LimitList]
    [noetherNormalizationData,RandomRange]
    [noetherNormalizationData,Verbose]
  Headline
    data for Noether normalization
  Usage
    (f,J,X) = noetherNormalizationData C
  Inputs
    C:Ideal
      $I$ or @ofClass  QuotientRing@ $R/I$ where $R$ is a @ofClass PolynomialRing@ 
    LimitList => List 
      gives the value which @TO "BasisElementLimit"@ will take 
      in calls to groebner basis computations
    RandomRange => ZZ 
      if not 0, gives an integer bound for the random coefficients. 
      If 0, then chooses random elements from the coefficient field
  Outputs
    f:RingMap 
      an automorphism of $R$
    J:Ideal 
      the image of $I$ under $f$
    X:List 
      a list of variables which are algebraically independent in $R/J$
  Description
    Text
      The computations performed in the routine {\tt noetherNormalizationData}
      use a random linear change of coordinates,
      hence one should expect the output to change each time the routine is executed.
    Example
      R = QQ[x_1..x_4];
      I = ideal(x_2^2+x_1*x_2+1, x_1*x_2*x_3*x_4+1);
      (f,J,X) = noetherNormalizationData I
    Text
      The next example shows how when we use the lexicographical ordering, 
      we can see the integrality of $R/f(I)$
      over the polynomial ring in $\dim(R/I)$, variables.
    Example
       R = QQ[x_1..x_5, MonomialOrder => Lex];
       I = ideal(x_2*x_1-x_5^3, x_5*x_1^3);
       (f,J,X) = noetherNormalizationData I
       transpose gens gb J
    Text
      If {\tt noetherNormalizationData} is unable to place the ideal into 
      the desired position after a few tries, the following warning is given.
    Example
      R = ZZ/2[a,b];
      I = ideal(a^2*b+a*b^2+1);
      (f,J,X) = noetherNormalizationData I
    Text
      Here is an example with the option {\tt Verbose => true}.
    Example
      R = QQ[x_1..x_4];
      I = ideal(x_2^2+x_1*x_2+1, x_1*x_2*x_3*x_4+1);
      (f,J,X) = noetherNormalizationData(I, Verbose => true)
    Text
      The first number in the output above gives the number of
      linear transformations performed by the routine while attempting to
      place $I$ into the desired position.
      The second number tells which {\tt BasisElementLimit}
      was used when computing the (partial) Groebner basis.
      By default, {\tt noetherNormalizationData} tries to use a partial
      Groebner basis. It does this by sequentially computing a Groebner
      basis with the option {\tt BasisElementLimit}, set to
      predetermined values. The default values come from the following list:
      $\{5,20,40,60,80,\infty\}$.
      To set the values manually, use the option {\tt LimitList}.
    Example
      R = QQ[x_1..x_4]; 
      I = ideal(x_2^2+x_1*x_2+1, x_1*x_2*x_3*x_4+1);
      (f,J,X) = noetherNormalizationData(I,Verbose => true,LimitList => {5,10})
    Text
      To limit the randomness of the coefficients, use the option {\tt RandomRange}. 
      Here is an example where the coefficients of the linear transformation are 
      random integers from in the range $[-2, 2]$.
    Example
      R = QQ[x_1..x_4];
      I = ideal(x_2^2+x_1*x_2+1, x_1*x_2*x_3*x_4+1);
      (f,J,X) = noetherNormalizationData(I,Verbose => true,RandomRange => 2)
    Text
      The algorithms
      used are based on algorithms found in A. Logar's paper: {\it A
      Computational Proof of the Noether Normalization Lemma}. In:
      Proceedings 6th AAEEC, Lecture Notes in Computer Science 357,
      Springer, 1989, 259-273.
    Text
      This symbol is provided by the package @TO "NoetherNormalization"@
  Caveat
  SeeAlso
///


TEST ///
-*
  restart
  debug needsPackage "NoetherNormalization"
*-
  kk = ZZ/101
  S = kk[a..d]
  I = monomialCurveIdeal(S, {1,2,3})
  R = S/I
  B = noetherRing R
  phi1 = noetherNormalization R
  assert isModuleFinite phi1
  B = noetherRing R
  assert isModuleFinite B
  frac B
  g = B.NoetherInfo#"noether map"
  assert(g^-1 * g == 1)
  assert(g * g^-1 == 1)

  use R
  phi2 = noetherNormalization(R, {a,d})
  assert isModuleFinite phi2
  noetherRing R
  B = noetherRing R
  frac noetherRing R
  use coefficientRing B
  use B
  1/(d+b)
///


TEST ///
-*
restart
debug needsPackage "NoetherNormalization"
*-
  -- Zero dimensional noetherNormalization...

  R = QQ[x,y]/(x^4-3, y^3-2);
  phi = map(R, QQ, {})
  B = noetherRing phi
  
  assert inNoetherForm R
  assert(B === R)
  assert(# noetherBasis R == 12)

  -- XXX  
  kk = ZZ/32003
  R = kk[x,y]/(x^4-3, y^3-2);
  phi = map(R, kk, {})
  isWellDefined phi  -- ok
  B = noetherRing R
  assert(B === R)
  assert inNoetherForm R
  assert(# noetherBasis B == 12)
  numerator x_B
  denominator x_B
  assert(x/y == -16001 * x * y^2)

  kk = QQ
  R = kk[x,y]/(x^4-3, y^3-2);
  phi = map(R, kk, {})
  -- TODO: isWellDefined phi -- fails... BUG in Core... git issue #1998
  assert inNoetherForm B
--isWellDefined phi

  kk = GF(27)
  assert(kk === frac kk)
  R = kk[x,y]/(x^4-2, y^5-2);
  phi = map(R, kk, {})
  isWellDefined phi  -- ok
  f = noetherNormalization R
  B = noetherRing R
  assert(B === R)
  assert(frac B === R)
  assert(x/y === - x * y^4)
  f = x^3/y
  factor oo
  factor((x^3/y)) -- fails...
  assert(# noetherBasis B == 20)
  traceForm B -- (now works). (used to fail! due to the bug below, which is now git issue #1999)

  kk = QQ
  R = kk[x,y]/(x^4-2, y^5-2);
  phi = map(R, kk, {})
  B = noetherRing R
  noetherBasis B
  traceForm B
  det oo

  -- bug in M2 #1999  NOW FIXED, it appears.
  -- kk = ZZ/101
  -- R = kk[x]
  -- f = matrix(kk, {{1,1}})  
  -- g = map(R^{0,1},, {{1,1},{1,1}})
  -- f*g
  --   also try:   lift(f*g, kk)
///

TEST ///
  -- we test usage of noetherNormalization R, where R is a ring:
  -- here: if R is finite over its base, (and R.?frac is not set).
  --          in this case, we set the noether info, and set frac R too.
  -- if R is not finite over its base, we call the noether normalization code.
-*  
  restart
  needsPackage "NoetherNormalization"
*-
  R = ZZ/101[x,y]/(x^2-y-1, y^3-x*y-3)

  B = noetherRing R
  noetherMap B -- FAILS: need to set this!
  A = coefficientRing B
  assert(coefficientRing frac B === frac A)
///

TEST ///
  -- we test usage of noetherNormalization R, where R is a ring:
  -- here: if R is finite over its base, (and R.?frac is not set).
  --          in this case, we set the noether info, and set frac R too.
  -- if R is not finite over its base, we call the noether normalization code.
-*  
  restart
  needsPackage "NoetherNormalization"
*-
  R = ZZ/101[x,y]/(x*y^3-x^2-y*x)
  B = noetherRing R
  noetherMap B
  A = coefficientRing B
  assert(coefficientRing frac B === frac A)
///

TEST ///
  -- we test usage of noetherNormalization f, f a RingMap A --> R
  -- case 1: f is the inclusion of A into R, where A is the coefficient ring of R, and B is finite over A
  --   in this case, return B, as in the previous case.
  -- In other cases, we set B = A[new vars]/I, where B is isomorphic to target of f.
  --   "new vars": either given by the user, or, if some of the variables appear in A and target 
  --   AND they map to same elements, then we use these names in A, and leave them out of B.
  --   any variables not mapping to themselves are given new names.
  
  -- This function creates A and B, then calls noetherNormalization B (which sets frac B, and the noether info).
///

TEST ///
  -- we test usage of noetherNormalization List
  -- A will be a polynomial ring given by variables taken from the list: if an element of the list is a variable,
  --  then we use that name.  If not, we give it a new variable name.
///

--=========================================================================--

--Assertions

TEST ///
  --uninstallPackage "NoetherNormalization"
  --installPackage "NoetherNormalization"
A = QQ[x_1..x_4]
I = ideal(x_1^2 + x_1*x_4+1,x_1*x_2*x_3*x_4+1)
assert((noetherNormalizationData(I))_2=={x_4,x_3})
///

TEST ///
--loadPackage "NoetherNormalization"
R = QQ[x,y]
I = ideal (y^2-x^2*(x+1))
(F,J,xs) = noetherNormalizationData I
assert(F === map(R,R,{x, y}))
assert(J == ideal(-x^3-x^2+y^2))
assert(xs == {y})
///

TEST ///
-*
  restart
  needsPackage "NoetherNormalization"
*-
-- Simple test
  R = ZZ/101[x,y]/(x^4-y^5-x*y^3)
  B = noetherRing(R, {x})
  describe B
  f = noetherMap B
  g = f^-1
  assert(f*g === id_R)
  assert(g*f === id_B)

  A = coefficientRing B
  L = frac B

  assert(coefficientRing B === A) -- automatic, by def of A
  assert(frac B === L) -- automatic, by def of L
  assert(coefficientRing L === frac A) -- needs checking
  assert(ring numerator 1_L === B) -- needs checking
  
--  R = ZZ/101[x,y]/(x^4-y^5-x*y^7)
--  B = noetherRing (R, {x}) -- fails... actually, this is not finite over the base...
///

TEST ///
-*
  restart
  needsPackage "NoetherNormalization"
*-
-- Simple test
  S = ZZ/101[a..d]
  I = monomialCurveIdeal(S, {1,3,4})
  R = S/I

  B = noetherRing(R, {a,d})
  describe B
  f = noetherMap B
  g = f^-1
  assert(f*g === id_R)
  assert(g*f === id_B)

  A = coefficientRing B
  L = frac B

  assert(coefficientRing B === A) -- automatic, by def of A
  assert(frac B === L) -- automatic, by def of L
  assert(coefficientRing L === frac A) -- needs checking
  assert(ring numerator 1_L === B) -- needs checking
///

TEST ///
-*
  restart
  needsPackage "NoetherNormalization"
*-
-- Simple test
  S = ZZ/101[a..d]
  I = monomialCurveIdeal(S, {1,3,4})
  R = S/I

  B = noetherRing(R, {a+d,a+c+d}, Variable => {s,t})
  describe B
  assert(#gens B === 2) -- make sure it removes 2 of the variables of a,b,c,d

  f = noetherMap B
  g = f^-1
  assert(f*g === id_R)
  assert(g*f === id_B)

  A = coefficientRing B
  L = frac B

  assert(coefficientRing L === frac A) -- needs checking
  assert(ring numerator 1_L === B) -- needs checking
///

TEST ///
-*
  restart
  needsPackage "NoetherNormalization"
*-
-- Simple test
  S = ZZ/101[a..d]
  I = monomialCurveIdeal(S, {1,3,4})
  R = S/I

  B = noetherRing(R, {a, a+c+d}, Variable => {s,t})
  assert(#gens B === 2) -- make sure it removes 2 of the variables of a,b,c,d
  use coefficientRing B
  assert(gens coefficientRing B === {a,s})
  use B
  assert(gens B === {b,d})
  
  f = noetherMap B
  g = f^-1
  assert(f*g === id_R)
  assert(g*f === id_B)

  A = coefficientRing B
  L = frac B

  assert(coefficientRing L === frac A) -- needs checking
  assert(ring numerator 1_L === B) -- needs checking
///

TEST ///
-*
  restart
  needsPackage "NoetherNormalization"
*-
-- Test to make sure that degrees in R don't mess up what happens in B.
-- Currently: B is set to have the standard grading.  How should we really handle this?
  S = ZZ/101[a..d]
  I = monomialCurveIdeal(S, {1,3,4})
  S = ZZ/101[a..d, Degrees => {1,3,2,4}, MonomialOrder => {2,2}]
  I = sub(I, S)
  R = S/I

  B = noetherRing(R, {a,d})
  degrees B
  degrees coefficientRing B

  use R  
  B = noetherRing(R, {a+d,a+c+d}, Variable => {s,t})
  describe B
  assert(#gens B === 2) -- make sure it removes 2 of the variables of a,b,c,d

  f = noetherMap B
  g = f^-1
  assert(f*g === id_R)
  assert(g*f === id_B)

  A = coefficientRing B
  L = frac B

  assert(coefficientRing L === frac A) -- needs checking
  assert(ring numerator 1_L === B) -- needs checking
///

TEST ///
-*
  restart
  needsPackage "NoetherNormalization"
*-
-- CURRENT PROBLEM: degrees are not preserved.
-- Test: what if the original ring has a multi-grading?
-- TODO: current problem is that the maps f,g below are not 
--   degree preserving.  Should they be? Can they be?
  S = ZZ/101[a..d]
  I = monomialCurveIdeal(S, {1,3,4})
  S = ZZ/101[a..d, DegreeRank => 4, MonomialOrder => {2,2}]
  I = sub(I, S)
  R = S/I

  B = noetherRing(R, {a,d})
  degrees B
  degrees coefficientRing B

  f = noetherMap B
  g = f^-1
--TODO  assert(f*g === id_R)
--TODO  assert(g*f === id_B)
  -- The maps are correct, except for grading?
  assert(flatten entries (g*f).matrix == generators(B, CoefficientRing => ZZ/101))
  assert(flatten entries (f*g).matrix == generators(R, CoefficientRing => ZZ/101))

  use R  
  B = noetherRing(R, {a+d,a+c+d}, Variable => {s,t})
  describe B
  assert(#gens B === 2) -- make sure it removes 2 of the variables of a,b,c,d

  f = noetherMap B
  g = f^-1
  --assert(f*g === id_R)
  --assert(g*f === id_B)
  assert(flatten entries (g*f).matrix == generators(B, CoefficientRing => ZZ/101))
  assert(flatten entries (f*g).matrix == generators(R, CoefficientRing => ZZ/101))

  A = coefficientRing B
  L = frac B

  assert(coefficientRing L === frac A) -- needs checking
  assert(ring numerator 1_L === B) -- needs checking
///


-- AAA
TEST ///
-*
  restart
  needsPackage "NoetherNormalization"
*-
-- Test: what if the original ring is a tower of rings?
-- CURRENT PROBLEM: original ring cannot be a tower.  Need to flatten it first.
  S = ZZ/101[a..d]
  I = monomialCurveIdeal(S, {1,3,4})
  S = ZZ/101[c,d][a,b, Join => false]
  I = sub(I, S)
  R = S/I
  
  -- the following fails
  (flatR, fR) = flattenRing R
  use R; use coefficientRing R
  elems = flatten entries matrix{{a,d}}
  elems = (elems/fR) 
  assert all(elems, a -> ring a === flatR)
--TODO  B = noetherRing elems -- STILL FAILS...

  -- Why does this work, but the above one fails?
  S = ZZ/101[a..d, MonomialOrder=>{2,Position=>Up,2}]
  I = monomialCurveIdeal(S, {1,3,4})
  R = S/I
  B = noetherRing(R, {a,d})
///


-- todo: clean up tests below this.
///
-*
  restart
  debug needsPackage "NoetherNormalization"
  S = ZZ/101[a..e]
  g = createCoefficientRing(S, {b+d, b+e})
  createRingPair g  

  restart
  debug needsPackage "NoetherNormalization"
  S = ZZ/101[a..e]
  g = createCoefficientRing(S, {b+d, b+e, c^3-d^3})
  F = createRingPair g  
  G = F^-1
F*G
G*F
*-
  -- working on noetherRing {list of polys"
  S = ZZ/101[a..d]
  I = monomialCurveIdeal(S, {1,3,4})
  R = S/I
  B = noetherRing(R, {a+b, a+d})
  describe B  

  use R
  B = noetherRing(R, {a, d})
  describe B  
  B.cache#"NoetherMap"

  use R
  B = noetherRing(R, {a, c+d})
  describe B  
  F = B.cache#"NoetherMap"
  F(c)
  F^-1(b)
  
  phi = createRingPair(S, {})
  assert isWellDefined phi
  phi = createRingPair(S, {a, d})
  assert isWellDefined phi

  g = createCoefficientRing(S, {a,d})
  isWellDefined g
  source g 
  target g === S
  h = createRingPair g
  isWellDefined h
  source h
  target h
  h.matrix -- This is not correct...
  use S
  g = createCoefficientRing(S, {a,d+c})
  h = createRingPair g
  createCoefficientRing(S, {a+b,d+c})
  
  use S
  g = createCoefficientRing(S, {a+b,a+d})
  createRingPair g  
  
  -- of the elements L:
  --  if element is a variable in S
  --    then var in A is the same
    --  if element is linear (affine linear), 
    --  then var is a new t_i.
  --  if it not linear, then have a new t_i.
  --  in the polynomial ring A[gens S]
  --  
  
  -- in this last case:
  -- A = kk[t_0, t_1]
  -- A --> S, given by t_0 --> a+b, t_1 --> a+d
  -- want ambientB = A[c,d] and a ring map phi: ambientR --> ambientB
  -- which is an isomorphism, i.e. 
  --   a -> t_1 - d
  --   b -> t_0 - t_1 + d
  --   c -> c
  --   d -> d
  -- 
  -- After that, we let B = ambientB/(phi I), if I = ideal of R.
  
  -- what if the elements have higer degree?
  -- e.g. {a+b, a+d, c^3-d^3}
  -- want A = kk[t_0, t_1, t_2]
  -- B = A[c,d]/(t_2 - (c^3-d^3))
  -- R --> B
  -- B --> R
  
  
  R = S/I

  T = ZZ/101[a..d,s,t,MonomialOrder=>{4,2}]
  IT = sub(I,T)
  J = IT+ideal(s-(a+b), t-(c+d))
  radical ideal leadTerm gens gb J

  use R; noetherRing(R, {a,d})
  use R; noetherRing(R, {a,d+c})
  use R; noetherRing(R, {a+b,d+c}) -- this one is NOT finite
  use R; B = noetherRing(R, {a+b,a+d})
  describe B
    
  

  describe ambient B
  use R; noetherRing(R, {a^2, d^2})

  B1 = ZZ/101[a, b, c, d, t_0, t_1, MonomialOrder=>{4, 2}]
  ideal(t_0 - (a+b), t_1 - (a+d)) + sub(I, B1)
  see ideal gens gb oo    
  -- loop through the list, 
  -- make a variable name for each polynomial (for the coeff ring A)
  -- for each, say what the image is in R?
  -- also, if we are taking a variable name out of R, place it in a set?
  -- 
  -- 
  
  -- xv = {a, d+c}
  f1 = c+d
  A = ZZ/101[a, t]
  B' = A[b,d,Join=>false]
  use R
  phi = map(R, B', {b, d, a, f1})
  J = trim ker phi
  B = B'/J
  -- now we need the isomorphism
  phi' = map(R, B, phi.matrix)
  ker phi'
  
  -- here is one way to compute the inverse of phi'...
  -- this should not be required, this is a workaround
  (B'', F) = flattenRing source phi'
  phi'.cache.inverse = F^-1 * (phi' * F^-1)^-1
  phi'.cache.inverse.cache.inverse = phi'
  assert(phi'^-1 * phi' === id_B) 
  assert(phi' * phi'^-1 === id_R) 

  -- I will need to place the inverse of the ring F : map R --> B into F.cache.inverse (and vice versa)

  -- Create A, create B' (ambient)
  -- make a map phi'
  -- ker of it, then make a map phi.
  -- create its inverse.
  -- stash phi into B? or R?
///

TEST ///
  -- test-finiteOverCoefficientRing
-*
  restart
  needsPackage "NoetherNormalization"
*-
  A = ZZ/101[t]  
  B = A[x,y]/(x^2-y*t, y^3)
  assert isModuleFinite B

  debugLevel = 1
  A = ZZ/101
  B = A[x,y]/(x^2, y^3)
  assert isModuleFinite B


  A = ZZ/101
  B = A[x,y]/(x^2, x*y)
  assert not isModuleFinite B
///

TEST ///
-*
  restart
  needsPackage "NoetherNormalization"
*-
  kk = ZZ/101
  R = kk[x,y]/(y^4-x*y^3-(x^2+1)*y-x^6)
  B = noetherRing(R, {x})
  L = frac B
  describe B
  describe L
  basisB = noetherBasis B
  basisL = noetherBasis L
  assert(#basisB == 4)
  assert(#basisL == 4)
  assert(all(basisB, m -> ring m === B))
  assert(all(basisL, m -> ring m === L))
  M0 = multiplicationMap B_0
  (noetherBasis B)/multiplicationMap/trace
  (noetherBasis L)/multiplicationMap/trace
  trB = (noetherBasis B)/trace
  trL = (noetherBasis L)/trace
  A = coefficientRing B
  assert all(trB, f -> ring f === A)
  assert all(trL, f -> ring f === frac A)
  trace y
  trace multiplicationMap y == trace y
  trace multiplicationMap y_L == trace y_L
  M = multiplicationMap y_L
  trace M
  trace(y_L)
  trace y
  
  TB = traceForm B -- should be over A
  TL = traceForm L -- should be over frac kk[x]
  assert(ring TB === A)
  assert(ring TL === frac A)
  assert(ring trace B_0 === coefficientRing B)
  assert(ring trace L_0 === coefficientRing L)
///

TEST ///
  -- of makeFrac
-*
  restart
  debug needsPackage "NoetherNormalization"
*-
  -- teat of the internal function 'makeFrac'
  debug needsPackage "NoetherNormalization"
  kk = ZZ/101
  A = kk[x];
  B = A[y, Join => false]/(y^4-x*y^3-(x^2+1)*y-x^6)
  L = makeFrac B
  describe L
  assert(degree y_L === {1})
  assert(monoid L === monoid B)
  --assert(isField L) -- not yet.
///

TEST ///
-*
  restart
  needsPackage "NoetherNormalization"
  
  test the following:
    1. singly graded case.
    2. inhomog case
    3. multi-graded case.  What to do if phi is not graded?
    4. subset of the variables
    5. a bunch of linear forms
    6. what else?
*-
  needsPackage "PushForward"
  kk = ZZ/101
  A = kk[t]
  x = symbol x
  y = symbol y
  R = kk[x,y]/(y^4-x*y^3-(x^2+1)*y-x^6)
  phi = map(R,A,{R_0})
  phi = map(R,A,{R_0^2})  
  B = noetherRing phi
  describe B
  L = frac B
  describe L
  noetherBasis B
  noetherBasis L

  multmaps = for x in noetherBasis B list pushFwd(map(B,A), map(B^1, B^1, {{x}}))
  multmaps2 = for x in noetherBasis B list multiplicationMap x
-- TODO: should we try to insure that these matrices use the same bases?
--  assert(multmaps === multmaps2) -- NOT EQUAL.  pushFwd uses different basis for B?
--                                  -- would be nice: to have this play well with pushFwd... if possible.

  traces = multmaps/trace
  MB = pushFwd(map(B,A), B^1) -- dim 4, free
  map(A^1, MB, {traces}) -- traces as a map of modules
  
  use B
  1/x
  1/x^2
  1/y
  (1/y) * y == 1
///

TEST ///
-*
  restart
  needsPackage "NoetherNormalization"
  
  test the following:
    1. singly graded case.
    2. inhomog case
    3. multi-graded case.  What to do if phi is not graded?
    4. subset of the variables
    5. a bunch of linear forms
    6. what else?
*-
  S = QQ[a..d]
  I = ideal"a3-b2-c, bc-d, a2-b2-d2"
  R = S/I

  B = noetherRing R
  A = coefficientRing B  
  degrees B -- not good... multigradings!
  leadTerm ideal B

  

///

TEST ///      
-*
  restart
  needsPackage "NoetherNormalization"
*-
  kk = ZZ/101
  A = kk[s,t]
  S = kk[a..d]
  I = monomialCurveIdeal(S, {1,3,4})
  R = S/I
  phi = map(R,A,{R_0, R_3})
  B = noetherRing phi
  L = frac B
describe B
describe L
noetherBasis B
noetherBasis L
  multmaps = for x in noetherBasis L list multiplicationMap x
  multmapsB = for x in noetherBasis B list multiplicationMap x

  traces = multmaps/trace
  traces = multmapsB/trace

  traceForm L
-*
  -- pushFwd doesn't currently work if the coeff ring is a fraction field.
  needsPackage "PushForward"
  --multmaps2 = for x in noetherBasis L list pushFwd(map(L,frac A), map(L^1, L^1, {{x}}))
  --assert(multmaps === multmaps2)
  MB = pushFwd(map(B,A), B^1) -- dim 4, free
  map(A^1, MB, {traces}) -- traces as a map of modules
  ML = pushFwd(map(L,frac A), L^1) -- dim 4, free -- FAILS
  map(A^1, ML, {traces}) -- traces as a map of modules -- FAILS, since last line fails.
  traces = for x in flatten entries basis B list 
    trace pushFwd(map(B,A), map(B^1, B^1, {{x}}))
*-
  kk = ZZ/101
  R = kk[symbol x,y,z]/(x*y, x*z, y*z)
--  R = ZZ[symbol x,y,z]/(x*y, x*z, y*z)  --??
  A = kk[t]
  phi = map(R,A,{R_0+R_1+R_2})
  B = noetherRing phi
  L = frac B
  noetherBasis B
  noetherBasis L
  (noetherBasis L)/multiplicationMap/trace
  traceForm L
///

-- WIP --
TEST ///
  -- test of creation of Noether normal form from a list of variables in a ring.
-*
  restart
  needsPackage "NoetherNormalization"
*-

  S = QQ[a..d]
  R = S/monomialCurveIdeal(S,{1,3,4})
  B = noetherRing(R,{a,d})
  frac B
  coefficientRing B
  coefficientRing frac B
  assert(coefficientRing frac B === frac coefficientRing B)
  assert(vars B == matrix"b,c")
  assert(numcols vars coefficientRing B == 2)
  -- going back and forth from R to B
  --   this works since we can do matching of variable names
  f = map(R, B)
  g = map(B, R)
  assert(f*g === id_R)
  assert(g*f === id_B)    

  -- Let's check some ring of elements
  A = coefficientRing B
  L = frac B
  assert(ring a === A)
  assert(ring b === L)
  use B
  assert(ring b === B)
  use frac A
  assert(ring a === frac A)

  use L
  gens(L, CoefficientRing => ZZ)
  assert(all(oo, v -> ring v === L))
  assert((1/b) * b == 1)
  assert((1/c) * c == 1)
  assert((1/(b+c)) * (b+c) == 1)
  assert(1/(a+b)*(a+b) == 1)
  assert (1/(b+c) * (b+c) == 1)

  h = 1/(b+c)
  factor h
  assert (denominator h == a^2*d - a*d^2)
  numerator h -- in the ring B
  assert(ring numerator h === B)
  assert(ring denominator h === A)
  
  noetherBasis B
  noetherBasis L

  multiplicationMap b
  multiplicationMap L_0
  traceForm L

  R = QQ[a..d]/(b^2-a, b*c-d)
  assert try (B = noetherRing(R,{a,d}); false) else true  
 -- noetherRing(R, {a,d}) should fail, as R is not finite over QQ[a,d]
///

TEST ///
-*
  restart
  needsPackage "NoetherNormalization"
*-
--  needsPackage "NoetherNormalization"
  kk = ZZ/101
  R = kk[x,y]/(x*y-1)
  B = noetherRing R
  describe B
  frac B
  A = kk[t]
  use R
  phi = map(R,A,{x+y})

  noetherRing phi
  noetherRing R
    
  (F, J, xv) = noetherNormalizationData R
  R' = (ambient R)/J

  G = map(R', R, sub(F.matrix, R'))
  isWellDefined G    
  G^-1 (xv_0)
  ideal R'
  ideal R
  for x in xv list G^-1 x
  A = kk[t]
  phi = map(R, A, for x in xv list G^-1 x)
  noetherRing phi
///


TEST ///
-*
  restart
  needsPackage "NoetherNormalization"
*-
  kk = ZZ/101
  R = kk[a,b,c,d]
  I = ideal"a2,ab,cd,d2"
  S = reesAlgebra I
  S = first flattenRing S

elapsedTime  noetherNormalizationData S
elapsedTime noetherNormalization S
elapsedTime  B = noetherRing S
  assert (numgens coefficientRing B == 5)
  assert(radical ideal leadTerm ideal B == ideal gens ambient B)

  T = kk[t_0..t_4]
  use S
  f = map(S,T,{w_0+w_2+b, w_3+a+c, w_1+w_2+d, a+b+d, w_2+c+d})
  assert isModuleFinite f
  B = noetherRing f
  assert isModuleFinite B
  assert(numgens coefficientRing B == 5)
  assert(radical ideal leadTerm ideal B == ideal gens ambient B)

-- We found this system of parameters as follows:
-- This code is not run automatically as the first line takes too much space
-*

linForms = (n,S) ->(
  G := gens S;
  sum\subsets(gens S, n)
  )

linForms(3,S)


fP = findParams1 S

P = findMoreParams (S, fP_0)
P = findMoreParams (S, fP_1)
P = findMoreParams (S, fP_2)
P = findMoreParams (S, fP_3)
P = findMoreParams (S, fP_4)
P = findMoreParams (S, fP_5)


findParams(S,T,{linForms(3,S)},100)
L = for b from 1 to 4 list linForms(b,S)
findParams(S,T,L,100)

tally oo

  i = 0
  f = map(S,T,sss_0)
  while not isModuleFinite f do (i= random (#sss); f =  map(S,T,sss_i);print i)
*-
///

-*
  restart
debug  needsPackage "NoetherNormalization"
*-

///
  -- Joe's example


n = 2;
--A = QQ[x_(1,1)..x_(n,n),y_(1,1)..y_(n,n),MonomialOrder => Lex]
--A = ZZ/32003[x_(1,1)..x_(n,n),y_(1,1)..y_(n,n),MonomialOrder => Lex]
A = ZZ/32003[x_(1,1)..x_(n,n),y_(1,1)..y_(n,n)]
X = transpose genericMatrix(A,n,n)
Y = transpose genericMatrix(A,y_(1,1),n,n)
bracket = ideal flatten entries (X*Y - Y*X)
--f = map(A,A,toList apply(0..(2*n^2-1), i -> sum(gens A)_{0..i}))
--f bracket
R = A/bracket
elapsedTime B = noetherRing R
ind =support first (independentSets bracket)
fiber = gens ring bracket - set IS
S = coefficientRing A[t_0..t_(#ind-1)]

--HERE find sparse NN
isModuleFinite map(R,S, ind)

coefficientRing B
noetherMap B
transpose matrix oo
independentSets bracket
transpose generators ideal B
netList (ideal B)_*
(f,J,j) = noetherNormalizationData(bracket,Verbose=>true,LimitList => {5,10})
transpose gens J
independentSets bracket
res bracket
--Example 1
clearAll
A = QQ[x_1..x_3][x_4]
A = QQ[x_1..x_4]
I = ideal(x_1^2 + x_1*x_4+1,x_1*x_2*x_3*x_4+1)
(f,J,j) = noetherNormalizationData(I,Verbose=>true,LimitList => {5})
A/f I

A = QQ
I = promote(ideal 0,QQ)
noetherNormalizationData(I,Verbose=>true)



transpose gens gb J
()
ring I
ring x_1
ring x_4

--Example 2
R = QQ[x_2,x_3,x_4,x_1,x_5,MonomialOrder=>Lex] -- this is a nice example...
R = QQ[x_1..x_5, MonomialOrder => Lex]; -- this is a nice example...
I = ideal(x_2*x_1-x_5^3, x_5*x_1^3);              -- compare with the same example in singular. 
(f,J,j) = noetherNormalizationData (I,Verbose => true)
transpose gens gb J


-- Not inverse maps!
S_2*S_1 -- Not inverse maps!
S_4*S_3
S_3*S_4
S_5*S_6
S_6*S_5
S_3*S_5*S_6*S_4


--Example 2.5
R = QQ[x_1..x_5,MonomialOrder=>Lex] -- this is a nice example...
I = ideal(x_2*x_1-x_5^3, x_5*x_1^3)              -- compare with the same example in singular. 
noetherNormalizationData(I,Verbose => true)
f = noetherPosition(I)
transpose gens gb f I
dim I
sort gens R
gens R

///



--Example 3 -- this one the indep vars are different
-*
restart
debug  needsPackage "NoetherNormalization"
*-
TEST///
R = QQ[x_5,x_4,x_3,x_2,x_1]
I = ideal(x_1^3 + x_1*x_2, x_2^3-x_4+x_3, x_1^2*x_2+x_1*x_2^2)
A = R/I
primaryDecomposition I
decompose I
B = noetherRing A
J = ideal B
pJ = primaryDecomposition J

decompose J
coefficientRing B
netList J_*
J' = ideal gens gb J
netList J'_*

L = frac B
describe L
--noetherNormalizationData(I,Verbose => true)
f := (noetherNormalizationData(I))_1


R = QQ[x,y,z]/(x*y,y^2-z)
R = QQ[x,y,z]/(x*y, y^2)
B = noetherRing R
///


--------------------------------------------------------------
-- Examples from Singular's noether.lib ----------------------
--------------------------------------------------------------
SLOW = method()
SLOW String := s -> null
TOOSLOW = method()
TOOSLOW String := s -> null

TEST ///
-* -- Singular code from noether.lib
  LIB "noether.lib";
  LIB "mregular.lib";
  ring r=0,(X,Y,a,b),dp;
  poly f=X^8+a*Y^4-Y;
  poly g=Y^8+b*X^4-X;
  poly h=diff(f,X)*diff(g,Y)-diff(f,Y)*diff(g,X);
  ideal i=f,g,h;
  
  NoetherPosition(i);
  NPos(i);
*-
-*
  restart
  debug needsPackage "NoetherNormalization"
*-
  kk = ZZ/32003 -- kk = QQ is original...
  R1 = kk[X,Y,a,b]
  f = X^8+a*Y^4-Y;
  g = Y^8+b*X^4-X;
  h = diff(X,f)*diff(Y,g)-diff(Y,f)*diff(X,g)
  I = ideal(f,g,h);
  R = R1/I  
--  elapsedTime noetherNormalization R -- takes too long...
///
--------------------------------------------------------------
TEST ///
-*
  LIB "noether.lib";
  LIB "mregular.lib";
  ring r=0,(x,y,z,a,b),dp;
  ideal i=2*y^2*(y^2+x^2)+(b^2-3*a^2)*y^2-2*b*y^2*(x+y)+2*a^2*b*(y+x)-a^2*x^2+a^2*(a^2-b^2),4*y^3+4*y*(y^2+x^2)-2*b*y^2-4*b*y*(y+x)+2*(b^2-3*a^2)*y+2*a^2*b,4*x*y^2-2*b*y^2-2*a^2*x+2*a^2*b;
  NPos(i); // -- so so sop
  NoetherPosition(i); // so so sop
*-
-*
  restart
  debug needsPackage "NoetherNormalization"
*-
  kk = QQ
  R1 = kk[x,y,z,a,b];
  I = ideal(2*y^2*(y^2+x^2)+(b^2-3*a^2)*y^2-2*b*y^2*(x+y)+2*a^2*b*(y+x)-a^2*x^2+a^2*(a^2-b^2),4*y^3+4*y*(y^2+x^2)-2*b*y^2-4*b*y*(y+x)+2*(b^2-3*a^2)*y+2*a^2*b,4*x*y^2-2*b*y^2-2*a^2*x+2*a^2*b);
  assert isHomogeneous I
  R = R1/I  
  elapsedTime noetherNormalization R  -- poor sop, better to use integer randoms?

  -- the following should be cleaned and made into tests
  findParameters1 R
  homogeneousLinearParameters R
  B = noetherRing(R, homogeneousLinearParameters R)
  L = frac B
  netList candidateParameters R
///
--------------------------------------------------------------
TEST ///
-*
  LIB "noether.lib";
  LIB "mregular.lib";
  ring r=0,(t,a,b,c,d),dp;
  ideal i=b4-a3d, ab3-a3c, bc4-ac3d-bcd3+ad4, c6-bc3d2-c3d3+bd5, ac5-b2c3d-ac2d3+b2d4, a2c4-a3d3+b3d3-a2cd3, b3c3-a3d3, ab2c3-a3cd2+b3cd2-ab2d3, a2bc3-a3c2d+b3c2d-a2bd3, a3c3-a3bd2, a4c2-a3b2d;
  NPos(i); // 
  NoetherPosition(i); // so so sop
*-
-*
  restart
  debug needsPackage "NoetherNormalization"
*-
  kk = QQ
  R1 = kk[t,a,b,c,d];
  I = ideal"b4-a3d, ab3-a3c, bc4-ac3d-bcd3+ad4, c6-bc3d2-c3d3+bd5, ac5-b2c3d-ac2d3+b2d4, a2c4-a3d3+b3d3-a2cd3, b3c3-a3d3, ab2c3-a3cd2+b3cd2-ab2d3, a2bc3-a3c2d+b3c2d-a2bd3, a3c3-a3bd2, a4c2-a3b2d";
  assert isHomogeneous I  
  dim I
  R = R1/I
  noetherNormalization R
  findParameters1 R -- good one
  B = noetherRing(R, first oo)
  see ideal gens gb ideal B
  gens B
  L = frac B
  ideal L
///
--------------------------------------------------------------
TEST ///
-*
  LIB "noether.lib";
  LIB "mregular.lib";
  ring r=0,(a,b,c,d,e),dp;
  ideal i=6*b4*c3+21*b4*c2*d+15b4cd2+9b4d3-8b2c2e-28b2cde+36b2d2e-144b2c-648b2d-120, 9b4c4+30b4c3d+39b4c2d2+18b4cd3-24b2c3e-16b2c2de+16b2cd2e+24b2d3e-432b2c2-720b2cd-432b2d2+16c2e2-32cde2+16d2e2+576ce-576de-240c+5184,-15b2c3e+15b2c2de-81b2c2+216b2cd-162b2d2+40c2e2-80cde2+40d2e2+1008ce-1008de+5184, -4b2c2+4b2cd-3b2d2+22ce-22de+261;
  NPos(i); // 
  NoetherPosition(i); // so so sop
*-
-*
  restart
  debug needsPackage "NoetherNormalization"
*-
  kk = QQ
  R1 = kk[a,b,c,d,e];
  I = ideal"6b4c3+21b4c2d+15b4cd2+9b4d3-8b2c2e-28b2cde+36b2d2e-144b2c-648b2d-120, 9b4c4+30b4c3d+39b4c2d2+18b4cd3-24b2c3e-16b2c2de+16b2cd2e+24b2d3e-432b2c2-720b2cd-432b2d2+16c2e2-32cde2+16d2e2+576ce-576de-240c+5184,-15b2c3e+15b2c2de-81b2c2+216b2cd-162b2d2+40c2e2-80cde2+40d2e2+1008ce-1008de+5184, -4b2c2+4b2cd-3b2d2+22ce-22de+261"
  R = R1/I
  f = noetherNormalization R;
///
--------------------------------------------------------------
TEST ///
  -- really hard one, apparently...
-*
  LIB "noether.lib";
  LIB "mregular.lib";
  ring r=0,(c,b,d,p,q),dp;
  ideal i=2*(b-1)^2+2*(q-p*q+p^2)+c^2*(q-1)^2-2*b*q+2*c*d*(1-q)*(q-p)+2*b*p*q*d*(d-c)+b^2*d^2*(1-2*p)+2*b*d^2*(p-q)+2*b*d*c*(p-1)+2*b*p*q*(c+1)+(b^2-2*b)*p^2*d^2+2*b^2*p^2+4*b*(1-b)*p+d^2*(p-q)^2,d*(2*p+1)*(q-p)+c*(p+2)*(1-q)+b*(b-2)*d+b*(1-2*b)*p*d+b*c*(q+p-p*q-1)+b*(b+1)*p^2*d, -b^2*(p-1)^2+2*p*(p-q)-2*(q-1),b^2+4*(p-q*q)+3*c^2*(q-1)*(q-1)-3*d^2*(p-q)^2+3*b^2*d^2*(p-1)^2+b^2*p*(p-2)+6*b*d*c*(p+q+q*p-1);

  NPos(i); // seems to take some time...
  NoetherPosition(i); // seems to take some time...
*-
-*
  restart
  debug needsPackage "NoetherNormalization"
*-
  kk = ZZ/101
  R1 = kk[c,b,d,p,q];
  I = ideal(2*(b-1)^2+2*(q-p*q+p^2)+c^2*(q-1)^2-2*b*q+2*c*d*(1-q)*(q-p)+2*b*p*q*d*(d-c)+b^2*d^2*(1-2*p)+2*b*d^2*(p-q)+2*b*d*c*(p-1)+2*b*p*q*(c+1)+(b^2-2*b)*p^2*d^2+2*b^2*p^2+4*b*(1-b)*p+d^2*(p-q)^2,d*(2*p+1)*(q-p)+c*(p+2)*(1-q)+b*(b-2)*d+b*(1-2*b)*p*d+b*c*(q+p-p*q-1)+b*(b+1)*p^2*d, -b^2*(p-1)^2+2*p*(p-q)-2*(q-1),b^2+4*(p-q*q)+3*c^2*(q-1)*(q-1)-3*d^2*(p-q)^2+3*b^2*d^2*(p-1)^2+b^2*p*(p-2)+6*b*d*c*(p+q+q*p-1));
///
--------------------------------------------------------------
TEST ///
-*
  LIB "noether.lib";
  LIB "mregular.lib";
  ring r=0,(a,b,c,d,e,f),dp;
  ideal i=2adef+3be2f-cef2,4ad2f+5bdef+cdf2,2abdf+3b2ef-bcf2,4a2df+5abef+acf2,4ad2e+3bde2+7cdef, 2acde+3bce2-c2ef, 4abde+3b2e2-4acdf+2bcef-c2f2, 4a2de+3abe2+7acef, 4acd2+5bcde+c2df, 4abd2+3b2de+7bcdf, 16a2d2-9b2e2+32acdf-18bcef+7c2f2, 2abcd+3b2ce-bc2f, 4a2cd+5abce+ac2f, 4a2bd+3ab2e+7abcf, abc2f-cdef2, ab2cf-bdef2, 2a2bcf+3be2f2-cef3, ab3f-3bdf3, 2a2b2f-4adf3+3bef3-cf4, a3bf+4aef3, 3ac3e-cde3, 3b2c2e-bc3f+2cd2ef, abc2e-cde2f, 6a2c2e-4ade3-3be4+ce3f, 3b3ce-b2c2f+2bd2ef, 2a2bce+3be3f-ce2f2, 3a3ce+4ae3f, 4bc3d+cd3e, 4ac3d-3bc3e-2cd2e2+c4f, 8b2c2d-4ad4-3bd3e-cd3f, 4b3cd+3bd3f, 4ab3d+3b4e-b3cf-6bd2f2, 4a4d+3a3be+a3cf-8ae2f2;
  NPos(i); // immediate.
  NoetherPosition(i); // immediate.
*-
-*
  restart
  debug needsPackage "NoetherNormalization"
*-
  kk = QQ
  kk = ZZ/101
  R1 = QQ[a,b,c,d,e,f]
  I = ideal"2adef+3be2f-cef2,4ad2f+5bdef+cdf2,2abdf+3b2ef-bcf2,4a2df+5abef+acf2,4ad2e+3bde2+7cdef, 2acde+3bce2-c2ef, 4abde+3b2e2-4acdf+2bcef-c2f2, 4a2de+3abe2+7acef, 4acd2+5bcde+c2df, 4abd2+3b2de+7bcdf, 16a2d2-9b2e2+32acdf-18bcef+7c2f2, 2abcd+3b2ce-bc2f, 4a2cd+5abce+ac2f, 4a2bd+3ab2e+7abcf, abc2f-cdef2, ab2cf-bdef2, 2a2bcf+3be2f2-cef3, ab3f-3bdf3, 2a2b2f-4adf3+3bef3-cf4, a3bf+4aef3, 3ac3e-cde3, 3b2c2e-bc3f+2cd2ef, abc2e-cde2f, 6a2c2e-4ade3-3be4+ce3f, 3b3ce-b2c2f+2bd2ef, 2a2bce+3be3f-ce2f2, 3a3ce+4ae3f, 4bc3d+cd3e, 4ac3d-3bc3e-2cd2e2+c4f, 8b2c2d-4ad4-3bd3e-cd3f, 4b3cd+3bd3f, 4ab3d+3b4e-b3cf-6bd2f2, 4a4d+3a3be+a3cf-8ae2f2";
  assert isHomogeneous I
  R = R1/I
  f = noetherNormalization R; -- really slow... even in char. p
  
  sop = homogeneousLinearParameters R -- quick quick, gives a seemingly nice sop?
  dim R === 3
  B = noetherRing(R, sop) -- this takes a while...  note that NPos and NoetherPosition aren't nec computing resulting ideals...
///
--------------------------------------------------------------
TEST ///
-*
  LIB "noether.lib";
  LIB "mregular.lib";
  ring r=0,(x,y,z,t,u,v,w),dp;
  ideal i=2tw+2wy-wz,2uw2-10vw2+20w3-7tu+35tv-70tw, 6tw2+2w2y-2w2z-21t2-7ty+7tz, 2v3-4uvw-5v2w+6uw2+7vw2-15w3-42vy, 6tw+9wy+2vz-3wz-21x, 9uw3-45vw3+135w4+14tv2-70tuw+196tvw-602tw2-14v2z+28uwz+14vwz-28w2z+147ux-735vx+2205wx-294ty+98tz+294yz-98z2, 36tw3+6w3y-9w3z-168t2w-14v2x+28uwx+14vwx-28w2x-28twy+42twz+588tx+392xy-245xz, 2uvw-6v2w-uw2+13vw2-5w3-28tw+14wy, u2w-3uvw+5uw2-28tw+14wy, tuw+tvw-11tw2-2vwy+8w2y+uwz-3vwz+5w2z-21wx, 5tuw-17tvw+33tw2-7uwy+22vwy-39w2y-2uwz+6vwz-10w2z+63wx, 20t2w-12uwx+30vwx-15w2x-10twy-8twz+4wyz, 4t2w-6uwx+12vwx-6w2x+2twy-2wy2-2twz+wyz, 8twx+8wxy-4wxz;
  NPos(i);
  NoetherPosition(i);
*-
-*
  restart
  debug needsPackage "NoetherNormalization"
*-
  kk = QQ
  R1 = kk[x,y,z,t,u,v,w];
  I = ideal"2tw+2wy-wz,2uw2-10vw2+20w3-7tu+35tv-70tw, 6tw2+2w2y-2w2z-21t2-7ty+7tz, 2v3-4uvw-5v2w+6uw2+7vw2-15w3-42vy, 6tw+9wy+2vz-3wz-21x, 9uw3-45vw3+135w4+14tv2-70tuw+196tvw-602tw2-14v2z+28uwz+14vwz-28w2z+147ux-735vx+2205wx-294ty+98tz+294yz-98z2, 36tw3+6w3y-9w3z-168t2w-14v2x+28uwx+14vwx-28w2x-28twy+42twz+588tx+392xy-245xz, 2uvw-6v2w-uw2+13vw2-5w3-28tw+14wy, u2w-3uvw+5uw2-28tw+14wy, tuw+tvw-11tw2-2vwy+8w2y+uwz-3vwz+5w2z-21wx, 5tuw-17tvw+33tw2-7uwy+22vwy-39w2y-2uwz+6vwz-10w2z+63wx, 20t2w-12uwx+30vwx-15w2x-10twy-8twz+4wyz, 4t2w-6uwx+12vwx-6w2x+2twy-2wy2-2twz+wyz, 8twx+8wxy-4wxz";
  assert not isHomogeneous I
///
--------------------------------------------------------------
TEST ///
-*
  LIB "noether.lib";
  LIB "mregular.lib";
  ring r=0,(a,b,c,d,x,w,u,v),dp;
  ideal i=a+b+c+d,u+v+w+x, 3ab+3ac+3bc+3ad+3bd+3cd+2,bu+cu+du+av+cv+dv+aw+bw+dw+ax+bx+cx,bcu+bdu+cdu+acv+adv+cdv+abw+adw+bdw+abx+acx+bcx,abc+abd+acd+bcd,bcdu+acdv+abdw+abcx;
  NPos(i);
  NoetherPosition(i);
*-
-*
  restart
  debug needsPackage "NoetherNormalization"
*-
  kk = QQ
  R1 = kk[a,b,c,d,x,w,u,v];
  I = ideal"a+b+c+d,u+v+w+x, 3ab+3ac+3bc+3ad+3bd+3cd+2,bu+cu+du+av+cv+dv+aw+bw+dw+ax+bx+cx,bcu+bdu+cdu+acv+adv+cdv+abw+adw+bdw+abx+acx+bcx,abc+abd+acd+bcd,bcdu+acdv+abdw+abcx";
  R = R1/I
///
--------------------------------------------------------------
TEST ///
-- I think: this is the 2x2 permanents of 3x3.  Why the funny variable names?
-*
  LIB "noether.lib";
  LIB "mregular.lib";
  ring r=0,(b,x,y,z,s,t,u,v,w),dp;
  ideal i=su+bv, tu+bw,tv+sw,sx+by,tx+bz,ty+sz,vx+uy,wx+uz,wy+vz;
  NPos(i);
  NoetherPosition(i);
*-
-*
  restart
  debug needsPackage "NoetherNormalization"
*-
  kk = QQ
  kk = ZZ/32003
  R1 = kk[b,x,y,z,s,t,u,v,w];
  I = ideal"su+bv, tu+bw,tv+sw,sx+by,tx+bz,ty+sz,vx+uy,wx+uz,wy+vz";
  R = R1/I
  noetherNormalization R -- really bad and slow
  homogeneousLinearParameters R
///
--------------------------------------------------------------
TEST ///
-*
  LIB "noether.lib";
  LIB "mregular.lib";
  ring r=0,(t,a,b,c,d,e,f,g,h),dp;
  ideal i=a+c+d-e-h,2df+2cg+2eh-2h2-h-1,3df2+3cg2-3eh2+3h3+3h2-e+4h, 6bdg-6eh2+6h3-3eh+6h2-e+4h, 4df3+4cg3+4eh3-4h4-6h3+4eh-10h2-h-1, 8bdfg+8eh3-8h4+4eh2-12h3+4eh-14h2-3h-1, 12bdg2+12eh3-12h4+12eh2-18h3+8eh-14h2-h-1, -24eh3+24h4-24eh2+36h3-8eh+26h2+7h+1;
  NPos(i);
  NoetherPosition(i);
*-
-*
  restart
  debug needsPackage "NoetherNormalization"
*-
  kk = QQ
///
--------------------------------------------------------------
TEST ///
-*
  LIB "noether.lib";
  LIB "mregular.lib";
  ring r=0,(a,b,c,d,e,f,g,h,k,l),dp;
  ideal i=f2h-1,ek2-1,g2l-1, 2ef2g2hk2+f2g2h2k2+2ef2g2k2l+2f2g2hk2l+f2g2k2l2+ck2, 2e2fg2hk2+2efg2h2k2+2e2fg2k2l+4efg2hk2l+2fg2h2k2l+2efg2k2l2+2fg2hk2l2+2bfh, 2e2f2ghk2+2ef2gh2k2+2e2f2gk2l+4ef2ghk2l+2f2gh2k2l+2ef2gk2l2+2f2ghk2l2+2dgl, e2f2g2k2+2ef2g2hk2+2ef2g2k2l+2f2g2hk2l+f2g2k2l2+bf2, 2e2f2g2hk+2ef2g2h2k+2e2f2g2kl+4ef2g2hkl+2f2g2h2kl+2ef2g2kl2+2f2g2hkl2+2cek, e2f2g2k2+2ef2g2hk2+f2g2h2k2+2ef2g2k2l+2f2g2hk2l+dg2, -e2f2g2hk2-ef2g2h2k2-e2f2g2k2l-2ef2g2hk2l-f2g2h2k2l-ef2g2k2l2-f2g2hk2l2+a2;
  NPos(i);
  NoetherPosition(i);
*-
-*
  restart
  debug needsPackage "NoetherNormalization"
*-
  kk = QQ
  R1 = kk[t,a,b,c,d,e,f,g,h];
  I = ideal"a+c+d-e-h,2df+2cg+2eh-2h2-h-1,3df2+3cg2-3eh2+3h3+3h2-e+4h, 6bdg-6eh2+6h3-3eh+6h2-e+4h, 4df3+4cg3+4eh3-4h4-6h3+4eh-10h2-h-1, 8bdfg+8eh3-8h4+4eh2-12h3+4eh-14h2-3h-1, 12bdg2+12eh3-12h4+12eh2-18h3+8eh-14h2-h-1, -24eh3+24h4-24eh2+36h3-8eh+26h2+7h+1";
  R = R1/I
  --  noetherNormalization R
///
--------------------------------------------------------------
TEST ///
-*
  LIB "noether.lib";
  LIB "mregular.lib";
  ring r=0,(b,c,d,e,f,g,h,j,k,l),dp;
  ideal i=-k9+9k8l-36k7l2+84k6l3-126k5l4+126k4l5-84k3l6+36k2l7-9kl8+l9, -bk8+8bk7l+k8l-28bk6l2-8k7l2+56bk5l3+28k6l3-70bk4l4-56k5l4+56bk3l5+70k4l5-28bk2l6-56k3l6+8bkl7+28k2l7-bl8-8kl8+l9, ck7-7ck6l-k7l+21ck5l2+7k6l2-35ck4l3-21k5l3+35ck3l4+35k4l4-21ck2l5-35k3l5+7ckl6+21k2l6-cl7-7kl7+l8, -dk6+6dk5l+k6l-15dk4l2-6k5l2+20dk3l3+15k4l3-15dk2l4-20k3l4+6dkl5+15k2l5-dl6-6kl6+l7, ek5-5ek4l-k5l+10ek3l2+5k4l2-10ek2l3-10k3l3+5ekl4+10k2l4-el5-5kl5+l6, -fk4+4fk3l+k4l-6fk2l2-4k3l2+4fkl3+6k2l3-fl4-4kl4+l5, gk3-3gk2l-k3l+3gkl2+3k2l2-gl3-3kl3+l4, -hk2+2hkl+k2l-hl2-2kl2+l3, jk-jl-kl+l2;
  NPos(i);
  NoetherPosition(i); // much worse that NPos
*-
-*
  restart
  debug needsPackage "NoetherNormalization"
*-
  kk = QQ
  R1 = kk[b,c,d,e,f,g,h,j,k,l];
  I = ideal"-k9+9k8l-36k7l2+84k6l3-126k5l4+126k4l5-84k3l6+36k2l7-9kl8+l9, -bk8+8bk7l+k8l-28bk6l2-8k7l2+56bk5l3+28k6l3-70bk4l4-56k5l4+56bk3l5+70k4l5-28bk2l6-56k3l6+8bkl7+28k2l7-bl8-8kl8+l9, ck7-7ck6l-k7l+21ck5l2+7k6l2-35ck4l3-21k5l3+35ck3l4+35k4l4-21ck2l5-35k3l5+7ckl6+21k2l6-cl7-7kl7+l8, -dk6+6dk5l+k6l-15dk4l2-6k5l2+20dk3l3+15k4l3-15dk2l4-20k3l4+6dkl5+15k2l5-dl6-6kl6+l7, ek5-5ek4l-k5l+10ek3l2+5k4l2-10ek2l3-10k3l3+5ekl4+10k2l4-el5-5kl5+l6, -fk4+4fk3l+k4l-6fk2l2-4k3l2+4fkl3+6k2l3-fl4-4kl4+l5, gk3-3gk2l-k3l+3gkl2+3k2l2-gl3-3kl3+l4, -hk2+2hkl+k2l-hl2-2kl2+l3, jk-jl-kl+l2";
  R = R1/I
  see I
  assert isHomogeneous I
  homogeneousLinearParameters R
///
--------------------------------------------------------------
TEST ///
-*
  LIB "noether.lib";
  LIB "mregular.lib";
  ring r=0,x(0..10),dp;
  ideal i=x(1)*x(0),x(1)*x(2),x(2)*x(3),x(3)*x(4),x(4)*x(5),x(5)*x(6),x(6)*x(7),x(7)*x(8),x(8)*x(9),x(9)*x(10),x(10)*x(0);
  NPos(i);
  NoetherPosition(i);
*-
-*
  restart
  debug needsPackage "NoetherNormalization"
*-
  kk = QQ
  R1 = kk[x_0..x_10];
  I = ideal(x_1*x_0,x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_5,x_5*x_6,x_6*x_7,x_7*x_8,x_8*x_9,x_9*x_10,x_10*x_0);
  R = R1/I
  assert isHomogeneous I
  homogeneousLinearParameters R
///
--------------------------------------------------------------
TEST ///
-*
  LIB "noether.lib";
  LIB "mregular.lib";
  ring r=0,(a,b,c,d,e,f,g,h,j,k,l,m,n,o,p,q,s),dp;
  ideal i=ag,gj+am+np+q,bl,nq,bg+bk+al+lo+lp+b+c,ag+ak+jl+bm+bn+go+ko+gp+kp+lq+a+d+f+h+o+p,gj+jk+am+an+mo+no+mp+np+gq+kq+e+j+q+s-1,jm+jn+mq+nq,jn+mq+2nq,gj+am+2an+no+np+2gq+kq+q+s,2ag+ak+bn+go+gp+lq+a+d,bg+al, an+gq, 2jm+jn+mq, gj+jk+am+mo+2mp+np+e+2j+q, jl+bm+gp+kp+a+f+o+2p,lp+b,jn+mq,gp+a;
  NPos(i);
  NoetherPosition(i);
*-
-*
  restart
  debug needsPackage "NoetherNormalization"
*-
  kk = QQ
  R = QQ[a,b,c,d,e,f,g,h,j,k,l,m,n,o,p,q,s]
  I = ideal"ag,gj+am+np+q,bl,nq,bg+bk+al+lo+lp+b+c,ag+ak+jl+bm+bn+go+ko+gp+kp+lq+a+d+f+h+o+p,gj+jk+am+an+mo+no+mp+np+gq+kq+e+j+q+s-1,jm+jn+mq+nq,jn+mq+2nq,gj+am+2an+no+np+2gq+kq+q+s,2ag+ak+bn+go+gp+lq+a+d,bg+al, an+gq, 2jm+jn+mq, gj+jk+am+mo+2mp+np+e+2j+q, jl+bm+gp+kp+a+f+o+2p,lp+b,jn+mq,gp+a"
  see I
  R = R/I
  -- FIXME
  --elapsedTIme noetherNormalization R; -- takes too long currently...
///
--------------------------------------------------------------
TOOSLOW ///
-- doesn't seem to run in Singular either.
-*
  LIB "noether.lib";
  LIB "mregular.lib";
  ring r=0,(a,b,c,d,e,f,g,h,v,w,k,l,m,n,o,p,q,s,t,u),dp;
  ideal i=af+bg+ch+dv+ew-1/2, a2f+b2g+c2h+d2v+e2w-1/3,tdw+agk+ahl+bhm+avn+bvo+cvp+awq+bwu+cws-1/6, a3f+b3g+c3h+d3v+e3w-1/4, tdew+abgk+achl+bchm+advn+bdvo+cdvp+aewq+bewu+cews-1/8, td2w+a2gk+a2hl+b2hm+a2vn+b2vo+c2vp+a2wq+b2wu+c2ws-1/12, ahkm+tawn+tbwo+avko+tcwp+avlp+bvmp+awku+awls+bwms-1/24, a4f+b4g+c4h+d4v+e4w-1/5, tde2w+ab2gk+ac2hl+bc2hm+ad2vn+bd2vo+cd2vp+ae2wq+be2wu+ce2ws-1/10, td2ew+a2bgk+a2chl+b2chm+a2dvn+b2dvo+c2dvp+a2ewq+b2ewu+c2ews-1/15,achkm+taewn+tbewo+advko+tcewp+advlp+bdvmp+aewku+aewls+bewms-1/30,t2d2w+a2gk2+a2hl2+2abhlm+b2hm2+a2vn2+2abvno+b2vo2+2acvnp+2bcvop+c2vp2+2tadwq+a2wq2+2tbdwu+2abwqu+b2wu2+2tcdws+2acwqs+2bcwus+c2ws2-1/20,td3w+a3gk+a3hl+b3hm+a3vn+b3vo+c3vp+a3wq+b3wu+c3ws-1/20,abhkm+tadwn+tbdwo+abvko+tcdwp+acvlp+bcvmp+abwku+acwls+bcwms-1/40,a2hkm+ta2wn+tb2wo+a2vko+tc2wp+a2vlp+b2vmp+a2wku+a2wls+b2wms-1/60,tawko+tawlp+tbwmp+avkmp+awkms-1/20;
  NPos(i);
  NoetherPosition(i);
*-
-*
  restart
  debug needsPackage "NoetherNormalization"
*-
  kk = QQ
  R1 = kk[a,b,c,d,e,f,g,h,v,w,k,l,m,n,o,p,q,s,t,u];
  I = ideal"af+bg+ch+dv+ew-1/2, a2f+b2g+c2h+d2v+e2w-1/3,tdw+agk+ahl+bhm+avn+bvo+cvp+awq+bwu+cws-1/6, a3f+b3g+c3h+d3v+e3w-1/4, tdew+abgk+achl+bchm+advn+bdvo+cdvp+aewq+bewu+cews-1/8, td2w+a2gk+a2hl+b2hm+a2vn+b2vo+c2vp+a2wq+b2wu+c2ws-1/12, ahkm+tawn+tbwo+avko+tcwp+avlp+bvmp+awku+awls+bwms-1/24, a4f+b4g+c4h+d4v+e4w-1/5, tde2w+ab2gk+ac2hl+bc2hm+ad2vn+bd2vo+cd2vp+ae2wq+be2wu+ce2ws-1/10, td2ew+a2bgk+a2chl+b2chm+a2dvn+b2dvo+c2dvp+a2ewq+b2ewu+c2ews-1/15,achkm+taewn+tbewo+advko+tcewp+advlp+bdvmp+aewku+aewls+bewms-1/30,t2d2w+a2gk2+a2hl2+2abhlm+b2hm2+a2vn2+2abvno+b2vo2+2acvnp+2bcvop+c2vp2+2tadwq+a2wq2+2tbdwu+2abwqu+b2wu2+2tcdws+2acwqs+2bcwus+c2ws2-1/20,td3w+a3gk+a3hl+b3hm+a3vn+b3vo+c3vp+a3wq+b3wu+c3ws-1/20,abhkm+tadwn+tbdwo+abvko+tcdwp+acvlp+bcvmp+abwku+acwls+bcwms-1/40,a2hkm+ta2wn+tb2wo+a2vko+tc2wp+a2vlp+b2vmp+a2wku+a2wls+b2wms-1/60,tawko+tawlp+tbwmp+avkmp+awkms-1/20";
  R = R1/I -- already hard, as the GB of I isn't easy.
///
--------------------------------------------------------------
-- End of examples from Singular, noether.lib ----------------
--------------------------------------------------------------





///
-*
restart
debug  needsPackage "NoetherNormalization"
*-

-- MES Note:
--   MES: Check the math here too...
--   For which f.g. k-algebras R does noetherNormalization produce useful answers?
--    a. R = domain: this is the main case.  All should work here.
--    b. R = unmixed radical ideal.  Even though `frac B` is not a field,
--         we should be inverting the correc things.
--    c. R = unmixed ideal, with primary components.  Does `frac B` produce something usable?
--    d. R = not unmixed: should always give an error, as the ring shold not be
--          finite over a polynomial ring with dim R number of variables?
R = QQ[x,y]/(x*y,y^2)
B = noetherRing(R, {x})
noetherMap B
J = ideal B
pJ = primaryDecomposition J
J == radical J
decompose J
coefficientRing B
netList J_*
J' = ideal gens gb J
netList J'_*
noetherMap B
L = frac B

describe L
///

///
-*
restart
debug  needsPackage "NoetherNormalization"
*-
R = QQ[x,y,z]/intersect(ideal x, ideal(y,z))
B = noetherRing(R, {x+y,z})

noetherMap B
J = ideal B
pJ = primaryDecomposition J
J == radical J
decompose J
coefficientRing B
netList J_*
J' = ideal gens gb J
netList J'_*
noetherMap B
L = frac B
0==HH_1 koszul matrix{{x,z}}
describe L


support (independentSets(I,Limit=>1))_0

--Example 4
R = QQ[x_1,x_2,x_3]
I = ideal(x_1*x_2,x_1*x_3)
noetherNormalizationData(I,Verbose => true)
support (independentSets(I,Limit=>1))_0
X = (noetherNormalizationData(I,Verbose => true))_0
f = (noetherNormalizationData(I,Verbose => true))_1
R/f(I)
X
apply(X, i-> f i)



--Example 5
R := QQ[x_5,x_4,x_3,x_2,x_1, MonomialOrder => Lex]
I = ideal(x_4^3*x_3*x_2-x_4, x_2*x_1-x_5^3, x_5*x_1^3)
S = noetherNormalizationData(I,Verbose => true)
f = S_1
f x_2
x_2
describe ring x_2


--Example 6
R = QQ[x_1..x_5] --80
I = ideal(x_4^3*x_3*x_2-x_4, x_2*x_1-x_5^3, x_5*x_1^3)
noetherNormalizationData(I,Verbose => true)
support (independentSets(I,Limit=>1))_0


--Example 6.5
R = QQ[x_5,x_4,x_3,x_2,x_1] --20
I = ideal(x_4^3*x_3*x_2-x_4, x_2*x_1-x_5^3, x_5*x_1^3)
noetherNormalizationData(I,Verbose => true)
support (independentSets(I,Limit=>1))_0

--Example 7 Nat, check this one later. CANNOT DO in ALT NN
R = QQ[x_6,x_5,x_4,x_3,x_2,x_1];
I = ideal(x_6^2+x_5*x_3*x_4-2,x_4^4*x_3^2+x_1,x_2*x_1^3);
noetherNormalizationData(I,Verbose => true)
support (independentSets(I,Limit=>1))_0


--Example 8 -- kills m2 in AltNN! 
R = QQ[x_6,x_5,x_4,x_3,x_2,x_1];
I = ideal(x_6^3+x_5^2*x_3*x_4-2,x_4^4*x_3^2+x_1,x_2*x_1^3);
noetherNormalizationData(I,Verbose => true)
support (independentSets(I,Limit=>1))_0


--We cannot compute even the gb with this ordering
R = QQ[x_1..x_4];
I = ideal(-(3/2)*x_3^3*x_2-(4/5)*x_2^2+4*x_1^5-x_1,x_3^3*x_1-(5/8)*x_3^2*x_2*x_1^2+(2/5)*x_2+(8/3)*x_1^3)
noetherNormalizationData I
support (independentSets(I,Limit=>1))_0




-- output should be:

-- alg independent vars, ideal, map

          p       s
I < k[x] <= k[y] <- k[p^-1(U)]
            J<
	    
we take I we currently return p^-1, we want p,s,J --MIKE AGREES
don't compute the inverse asking for it. 

cache the inverse using something like

keys f.cache


-- Singular is better...

R = QQ[x_5,x_4,x_3,x_2,x_1,MonomialOrder => Lex] 
I = ideal(x_2*x_1-x_5^3, x_5*x_1^3)              
gens gb I
noetherNormalizationData I



R = QQ[x_5,x_4,x_3,x_2,x_1,MonomialOrder => Lex]
I = ideal(x_4^3*x_3*x_2-x_4, x_2*x_1-x_5^3, x_5*x_1^3)
gens gb I
noetherNormalizationData I
--this guys a problem, what to do?

R = QQ[x_1..x_4,MonomialOrder => Lex];
I = ideal((4/7)*x_3^2*x_4-(4/3)*x_4^2-(3/7)*x_3,(5/4)*x_2*x_4^2+(7/8)*x_1+(7/2),-(10/9)*x_1^2*x_4-(7/9)*x_2^2+(7/4)*x_4+(3/2))
noetherNormalizationData(I,Verbose => true)



-- Examples should be listed in a reasonable order
-- Comments should be given about why each example is good

--========================================================



--Examples:
clearAll
uninstallPackage "NoetherNormalization"
installPackage "NoetherNormalization"
methods noetherNormalizationData
help noetherNormalizationData

R = QQ[x_3,x_3,x_2,x_1, MonomialOrder => Lex];
I = ideal(-(3/2)*x_3^3*x_2-(4/5)*x_2^2+4*x_1^5-x_1,x_3^3*x_1-(5/8)*x_3^2*x_2*x_1^2+(2/5)*x_2+(8/3)*x_1^3)



--Ex#1
-- this is the example from the paper
-- this makes it a good first example
R = QQ[x_1..x_4,MonomialOrder => Lex];
R = QQ[x_4,x_3,x_2,x_1, MonomialOrder => Lex]; --the same ordering as in the paper
R = QQ[x_2,x_3,x_4,x_1, MonomialOrder => Lex];
I = ideal(x_2^2+x_1*x_2+1, x_1*x_2*x_3*x_4+1);
noetherNormalizationData I
I = ideal((6/5)*x_4*x_1-(8/7)*x_1^3-(9/4),(3/7)*x_4*x_3+(7/8)*x_3*x_2^2+x_1-(5/3),-(5/6)*x_4*x_2-(5/6)*x_3^2*x_1)
G = gb I
X = sort gens R -- note that this "sort" is very important
benchmark "varPrep(X,G)"
benchmark "support (independentSets(I,Limit => 1))_0"


--Examples of not so good I
--Ex#2
R = QQ[x_5,x_4,x_3,x_2,x_1,MonomialOrder => Lex]
I = ideal(x_1^3 + x_1*x_2, x_2^3-x_4+x_3, x_1^2*x_2+x_1*x_2^2)
noetherNormalizationData I
G = gb I
X = sort gens R -- note that this "sort" is very important
varPrep(X,G)
ZZ[x]
support (independentSets(ideal(x),Limit => 1))_0
independentSets(ideal(x))

dim(ZZ[x]/(7,x))
dim (ZZ[x]/ideal(7,x))

--Ex#3
R = QQ[x_1,x_2,x_3,MonomialOrder => Lex]
I = ideal(x_1*x_2,x_1*x_3)
noetherNormalizationData(I)
G = gb I
X = sort gens R -- note that this "sort" is very important
benchmark "varPrep(X,G)"
benchmark "support (independentSets(I,Limit => 1))_0"
benchmark "independentSets(I,Limit => 1)"
altVarPrep(X,I)

--Ex#4
R = QQ[x_3,x_2,x_1,MonomialOrder => Lex]
I = ideal(x_1*x_2, x_1*x_3)
G = gb I
X = sort gens R -- note that this "sort" is very important
varPrep(X,G)
independentSets I


prune ideal gens G
d = dim I
X = sort gens R -- note that this "sort" is very important
varPrep(X,G)
np = maxAlgPerm(R,X,G,d)
maxAlgPermC(R,X,G,d)
maxAlgPermB(R,X,G,d,{})


--Ex#5
R = QQ[x_1..x_6,MonomialOrder => Lex]
R = QQ[x_6,x_5,x_4,x_3,x_2,x_1,MonomialOrder => Lex]
I = ideal(x_1*x_2,x_1*x_3, x_2*x_3,x_2*x_4,x_2*x_5,x_3*x_4,x_3*x_5,x_4*x_5, x_4*x_6, x_5*x_6)
G = gb I
d = dim I
X = sort gens R -- note that this "sort" is very important
varPrep(X,G)
np = maxAlgPerm(R,X,G,d)
G = gb np I
(U,V) = varPrep(X,G)
noetherNormalizationData I
x_5<x_4

--Dan's finite field killing examples
xy(x+y)
(xy-1)(x+y)
x^2*y+x*y^2+1

R = ZZ/2[x,y]
I = ideal((x^2*y+x*y^2+1))
noetherNormalizationData I

-- we need more complex examples.

viewHelp


--Nat's examples

R = QQ[x_7,x_6,x_5,x_4,x_3,x_2,x_1, MonomialOrder => Lex];
I = ideal(x_2^2+x_1*x_2+x_5^2+1, x_1*x_2*x_3*x_4+x_5^4, x_6^4*x_3+x_4^2+8, x_7*x_6*x_5^2+x_5*x_2^2+12);
gens gb I
noetherNormalizationData I
///

end----------------------------------------------------------
restart
load "NoetherNormalization.m2"

uninstallPackage "NoetherNormalization"
restart
installPackage "NoetherNormalization"
check NoetherNormalization

---------
