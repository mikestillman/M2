newPackage(
        "NoetherNormalForm",
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
    "noetherForm",
    "noetherBasis",
    "noetherBasisMatrix",
    "inNoetherForm",
    "multiplicationMap",
    "traceForm",
    "noetherMap",
    -- keys used:
    "NoetherInfo",
    "Remove"
    }
export{"noetherNormalization","LimitList","RandomRange"}
----------------------------------------------------------------
-- The following 3 lines: probably should be in m2/enginering.m2?
raw = value Core#"private dictionary"#"raw"
rawIsField = value Core#"private dictionary"#"rawIsField"
isField EngineRing := R -> (R.?isField and R.isField) or rawIsField raw R
----------------------------------------------------------------

--inNoetherForm
-- this function isn't used locally, instead the internal function `noetherInfo` is used.
inNoetherForm = method()
inNoetherForm Ring := Boolean => (R) -> R.?NoetherInfo

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
    then error "expected a ring or field created with `noetherForm`";
    R.NoetherInfo
    )

noetherMap = method()
noetherMap Ring := Ring => (B) -> (
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

noetherForm = method(Options => {Remove => null, Variable => getSymbol "t"})


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

noetherForm Ring := Ring => opts -> R -> (
    -- case 1: R is already in Noether form: finite over its coeff ring.
    --   In this case, set NoetherInfo, map to/from R is the identity
    -- case 2: not the case.
    --   Compute random linear forms (if not too low of characteristic).
    --   make a list L of these, call noetherForm L.

    A := coefficientRing R;
    
    if (isPolynomialRing A or isField A) and isModuleFinite R then (
	KR := makeFrac R; -- do this?
	setNoetherInfo(R,KR);
	R.NoetherInfo#"noether map" = map(R,R);
	return R
        );
    
    -- get the flattened coeff ring of R.
    -- use the flattened ring to get elements.    
    (F, J, xv) := noetherNormalization R;
    kk := coefficientRing R;
    t := opts.Variable;
    A = if #xv == 0 then kk else kk[t_0..t_(#xv-1)];
    phi := map(R,A,for x in xv list F^-1 x);
    noetherForm phi
    )

noetherForm List := Ring => opts -> L -> (
    -- check that ring R of all elements is the same
    if #L === 0 then 
        error "expected non-empty list of ring elements";
    if any(L, f -> not instance(f, RingElement)) then 
        error "expected non-empty list of ring elements";
    R := ring L_0;
    if not all(L, f -> ring f === R) then
        error "expected elements in the same ring";
    f := createCoefficientRing(R, L, Variable => opts.Variable);
    noetherForm f
    )

noetherForm RingMap := Ring => opts -> f -> (
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
    B
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
-- initial comments: noetherNormalization takes an ideal I of a ring R
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

-- comments: noetherNormalization is the main method. An ideal I is
-- passed to it and its Groebner basis is immediately computed.  Next
-- a random linear transformation is applied and we check to see if
-- the ideal is in Noether position. We then check to see if the the
-- ideal in Noether position by partially computing a Groebner basis
-- for the ideal. If the partially computed Groebner basis witnesses
-- the integrality of all of the dependent variables, we are done, if
-- not we try again.  If the entire Groebner basis is computed and the
-- integrality is never witnessed then we apply another random linear
-- transformation and start the process again. 

noetherNormalization = method(Options => {Verbose => false, LimitList => {5,20,40,60,80,infinity}, RandomRange => 0})
noetherNormalization(Ideal) := opts -> I -> (
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
	       done = lastCheck(X,G,d);-- may want to define f I above, but this causes noetherNormalization to fail at the moment
     	       seqindex = seqindex + 1;
	       );
	  if counter == 5 then << "--warning: no good linear transformation found by noetherNormalization" <<endl;
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

noetherNormalization(QuotientRing) := noetherNormalization(PolynomialRing) := opts -> R -> (
     if not isPolynomialRing ring ideal R then error "expected a quotient of a polynomial ring";
     noetherNormalization(ideal R, Verbose => opts.Verbose)
     );


--=========================================================================--


beginDocumentation()

doc ///
  Key
    NoetherNormalForm
  Headline
    code for Noether normal forms of affine rings
  Description
    Text
///

doc ///
  Key
    noetherForm
    (noetherForm, List)
    (noetherForm, RingMap)
    (noetherForm, Ring)
  Headline
    create a polynomial ring in Noether normal form
  Usage
    B = noetherForm phi
    B = noetherForm xv
    B = noetherForm R
  Inputs
    phi:RingMap
      from a ring {\tt A} to a ring {\tt R}
    xv:List
      of variables in an affine ring {\tt R} over which {\tt R} is finite
    R:Ring
      an affine equidimensional and reduced ring
  Outputs
    B:Ring
      isomorphic to B, but of the form {\tt A[new variables]/(ideal)}.
  Consequences
    Item
      The following fields are set in {\tt R}:
    Item
      The following fields are set in {\tt B}:
    Item
      The following fields are set in {\tt L = frac B}:
  Description
    Text
    Example
      kk = ZZ/101
      A = kk[t]
      R = kk[x,y]/(y^4-x*y^3-(x^2+1)*y-x^6)
      phi = map(R,A,{R_0})
      B = noetherForm phi
    Example
      kk = ZZ/101
      x = symbol x
      y = symbol y
      R = kk[x,y,z]/(ideal(x*y, x*z, y*z))
      A = kk[t]
      phi = map(R,A,{R_0+R_1+R_2})
      B = noetherForm phi
  Caveat
    The base field must currently be a finite field, or the rationals.
    Finiteness is not yet checked.
  SeeAlso
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
      B = noetherForm {x}
      noetherBasis B
      noetherBasis frac B
      assert(multiplicationMap(y^3) == (multiplicationMap y)^3)
      trace(y^3) -- fails?
  Caveat
    One must have created this ring with @TO noetherForm@.
  SeeAlso
    noetherForm
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
      B = noetherForm {a,d}
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
    One must have created this ring with @TO noetherForm@.
  SeeAlso
    noetherForm
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
    trace form matrix of ring created using noetherForm
  Usage
    traceForm R
  Inputs
    R:Ring
  Outputs
    :Matrix
  Description
    Text
  Caveat
    One must have created this ring with @TO noetherForm@.
  SeeAlso
    noetherForm
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
      B = noetherForm {a,d}
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
    One must have created this ring with @TO noetherForm@.
  SeeAlso
    noetherForm
    (inNoetherForm, Ring)
    (noetherBasis, Ring)
    (multiplicationMap, RingElement)
///

doc ///
  Key
    inNoetherForm
    (inNoetherForm, Ring)
  Headline
    whether the ring was created using noetherForm
  Usage
    inNoetherForm R
  Inputs
    R:Ring
  Outputs
    :Boolean
  Description
    Text
  Caveat
    This function only checks whether the ring was created using @TO noetherForm@, not
    whether it really is in Noether normal form
  SeeAlso
    noetherForm
///

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

doc ///
  Key
    noetherNormalization
    (noetherNormalization,Ideal)
    (noetherNormalization,QuotientRing)
    (noetherNormalization,PolynomialRing)
    LimitList
    RandomRange
    [noetherNormalization,LimitList]
    [noetherNormalization,RandomRange]
    [noetherNormalization,Verbose]
  Headline
    data for Noether normalization
  Usage
    (f,J,X) = noetherNormalization C
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
      The computations performed in the routine {\tt noetherNormalization}
      use a random linear change of coordinates,
      hence one should expect the output to change each time the routine is executed.
    Example
      R = QQ[x_1..x_4];
      I = ideal(x_2^2+x_1*x_2+1, x_1*x_2*x_3*x_4+1);
      (f,J,X) = noetherNormalization I
    Text
      The next example shows how when we use the lexicographical ordering, 
      we can see the integrality of $R/f(I)$
      over the polynomial ring in $\dim(R/I)$, variables.
    Example
       R = QQ[x_1..x_5, MonomialOrder => Lex];
       I = ideal(x_2*x_1-x_5^3, x_5*x_1^3);
       (f,J,X) = noetherNormalization I
       transpose gens gb J
    Text
      If {\tt noetherNormalization} is unable to place the ideal into 
      the desired position after a few tries, the following warning is given.
    Example
      R = ZZ/2[a,b];
      I = ideal(a^2*b+a*b^2+1);
      (f,J,X) = noetherNormalization I
    Text
      Here is an example with the option {\tt Verbose => true}.
    Example
      R = QQ[x_1..x_4];
      I = ideal(x_2^2+x_1*x_2+1, x_1*x_2*x_3*x_4+1);
      (f,J,X) = noetherNormalization(I, Verbose => true)
    Text
      The first number in the output above gives the number of
      linear transformations performed by the routine while attempting to
      place $I$ into the desired position.
      The second number tells which {\tt BasisElementLimit}
      was used when computing the (partial) Groebner basis.
      By default, {\tt noetherNormalization} tries to use a partial
      Groebner basis. It does this by sequentially computing a Groebner
      basis with the option {\tt BasisElementLimit}, set to
      predetermined values. The default values come from the following list:
      $\{5,20,40,60,80,\infty\}$.
      To set the values manually, use the option {\tt LimitList}.
    Example
      R = QQ[x_1..x_4]; 
      I = ideal(x_2^2+x_1*x_2+1, x_1*x_2*x_3*x_4+1);
      (f,J,X) = noetherNormalization(I,Verbose => true,LimitList => {5,10})
    Text
      To limit the randomness of the coefficients, use the option {\tt RandomRange}. 
      Here is an example where the coefficients of the linear transformation are 
      random integers from in the range $[-2, 2]$.
    Example
      R = QQ[x_1..x_4];
      I = ideal(x_2^2+x_1*x_2+1, x_1*x_2*x_3*x_4+1);
      (f,J,X) = noetherNormalization(I,Verbose => true,RandomRange => 2)
    Text
      The algorithms
      used are based on algorithms found in A. Logar's paper: {\it A
      Computational Proof of the Noether Normalization Lemma}. In:
      Proceedings 6th AAEEC, Lecture Notes in Computer Science 357,
      Springer, 1989, 259-273.
    Text
      This symbol is provided by the package @TO "NoetherNormalForm"@
  Caveat
  SeeAlso
///


TEST ///
-*
  restart
  debug needsPackage "NoetherNormalForm"
*-
  kk = ZZ/101
  S = kk[a..d]
  I = monomialCurveIdeal(S, {1,2,3})
  R = S/I
  phi1 = noetherForm R
  assert isModuleFinite phi1
  B = noetherForm phi1
  assert isModuleFinite B
  frac B
  g = B.NoetherInfo#"noether map"
  assert(g^-1 * g == 1)
  assert(g * g^-1 == 1)
  use R
  phi2 = noetherForm {a,d}
  assert isModuleFinite phi2
  
  
///


TEST ///
-*
restart
debug needsPackage "NoetherNormalForm"
*-
  -- Zero dimensional noetherForm...

  R = QQ[x,y]/(x^4-3, y^3-2);
  phi = map(R, QQ, {})
  B = noetherForm phi
  
  assert inNoetherForm R
  assert(B === R)
  assert(# noetherBasis R == 12)

  -- XXX  
  kk = ZZ/32003
  R = kk[x,y]/(x^4-3, y^3-2);
  phi = map(R, kk, {})
  isWellDefined phi  -- ok
  B = noetherForm R
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
  B = noetherForm R
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
  B = noetherForm R
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
  -- we test usage of noetherForm R, where R is a ring:
  -- here: if R is finite over its base, (and R.?frac is not set).
  --          in this case, we set the noether info, and set frac R too.
  -- if R is not finite over its base, we call the noether normalization code.
-*  
  restart
  needsPackage "NoetherNormalForm"
*-
  R = ZZ/101[x,y]/(x^2-y-1, y^3-x*y-3)

  B = noetherForm R
  noetherMap B -- FAILS: need to set this!
  A = coefficientRing B
  assert(coefficientRing frac B === frac A)
///

TEST ///
  -- we test usage of noetherForm R, where R is a ring:
  -- here: if R is finite over its base, (and R.?frac is not set).
  --          in this case, we set the noether info, and set frac R too.
  -- if R is not finite over its base, we call the noether normalization code.
-*  
  restart
  needsPackage "NoetherNormalForm"
*-
  R = ZZ/101[x,y]/(x*y^3-x^2-y*x)
  B = noetherForm R
  noetherMap B
  A = coefficientRing B
  assert(coefficientRing frac B === frac A)
///

TEST ///
  -- we test usage of noetherForm f, f a RingMap A --> R
  -- case 1: f is the inclusion of A into R, where A is the coefficient ring of R, and B is finite over A
  --   in this case, return B, as in the previous case.
  -- In other cases, we set B = A[new vars]/I, where B is isomorphic to target of f.
  --   "new vars": either given by the user, or, if some of the variables appear in A and target 
  --   AND they map to same elements, then we use these names in A, and leave them out of B.
  --   any variables not mapping to themselves are given new names.
  
  -- This function creates A and B, then calls noetherForm B (which sets frac B, and the noether info).
///

TEST ///
  -- we test usage of noetherForm List
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
assert((noetherNormalization(I))_2=={x_4,x_3})
///

TEST ///
--loadPackage "NoetherNormalization"
R = QQ[x,y]
I = ideal (y^2-x^2*(x+1))
(F,J,xs) = noetherNormalization I
assert(F === map(R,R,{x, y}))
assert(J == ideal(-x^3-x^2+y^2))
assert(xs == {y})
///

TEST ///
-*
  restart
  needsPackage "NoetherNormalForm"
*-
-- Simple test
  R = ZZ/101[x,y]/(x^4-y^5-x*y^3)
  B = noetherForm {x}
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
--  B = noetherForm {x} -- fails... actually, this is not finite over the base...
///

TEST ///
-*
  restart
  needsPackage "NoetherNormalForm"
*-
-- Simple test
  S = ZZ/101[a..d]
  I = monomialCurveIdeal(S, {1,3,4})
  R = S/I

  B = noetherForm {a,d}
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
  needsPackage "NoetherNormalForm"
*-
-- Simple test
  S = ZZ/101[a..d]
  I = monomialCurveIdeal(S, {1,3,4})
  R = S/I

  B = noetherForm({a+d,a+c+d}, Variable => {s,t})
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
  needsPackage "NoetherNormalForm"
*-
-- Simple test
  S = ZZ/101[a..d]
  I = monomialCurveIdeal(S, {1,3,4})
  R = S/I

  B = noetherForm({a, a+c+d}, Variable => {s,t})
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
  needsPackage "NoetherNormalForm"
*-
-- Test to make sure that degrees in R don't mess up what happens in B.
-- Currently: B is set to have the standard grading.  How should we really handle this?
  S = ZZ/101[a..d]
  I = monomialCurveIdeal(S, {1,3,4})
  S = ZZ/101[a..d, Degrees => {1,3,2,4}, MonomialOrder => {2,2}]
  I = sub(I, S)
  R = S/I

  B = noetherForm {a,d}
  degrees B
  degrees coefficientRing B

  use R  
  B = noetherForm({a+d,a+c+d}, Variable => {s,t})
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
  needsPackage "NoetherNormalForm"
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

  B = noetherForm {a,d}
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
  B = noetherForm({a+d,a+c+d}, Variable => {s,t})
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
  needsPackage "NoetherNormalForm"
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
--TODO  B = noetherForm elems -- STILL FAILS...

  -- Why does this work, but the above one fails?
  S = ZZ/101[a..d, MonomialOrder=>{2,Position=>Up,2}]
  I = monomialCurveIdeal(S, {1,3,4})
  R = S/I
  B = noetherForm {a,d}
///


-- todo: clean up tests below this.
///
-*
  restart
  debug needsPackage "NoetherNormalForm"
  S = ZZ/101[a..e]
  g = createCoefficientRing(S, {b+d, b+e})
  createRingPair g  

  restart
  debug needsPackage "NoetherNormalForm"
  S = ZZ/101[a..e]
  g = createCoefficientRing(S, {b+d, b+e, c^3-d^3})
  F = createRingPair g  
  G = F^-1
F*G
G*F
*-
  -- working on noetherForm {list of polys"
  S = ZZ/101[a..d]
  I = monomialCurveIdeal(S, {1,3,4})
  R = S/I
  B = noetherForm({a+b, a+d})
  describe B  

  use R
  B = noetherForm({a, d})
  describe B  
  B.cache#"NoetherMap"

  use R
  B = noetherForm({a, c+d})
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

  use R; noetherForm {a,d}
  use R; noetherForm {a,d+c}
  use R; noetherForm {a+b,d+c} -- this one is NOT finite
  use R; B = noetherForm {a+b,a+d}
  describe B
    
  

  describe ambient B
  use R; noetherForm {a^2, d^2}

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
  needsPackage "NoetherNormalForm"
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
  needsPackage "NoetherNormalForm"
*-
  kk = ZZ/101
  R = kk[x,y]/(y^4-x*y^3-(x^2+1)*y-x^6)
  B = noetherForm {x}
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
  debug needsPackage "NoetherNormalForm"
*-
  -- teat of the internal function 'makeFrac'
  debug needsPackage "NoetherNormalForm"
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
  needsPackage "NoetherNormalForm"
  
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
  B = noetherForm phi
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
  needsPackage "NoetherNormalForm"
  
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

  B = noetherForm R
  A = coefficientRing B  
  degrees B -- not good... multigradings!
  leadTerm ideal B

  

///

TEST ///      
-*
  restart
  needsPackage "NoetherNormalForm"
*-
  kk = ZZ/101
  A = kk[s,t]
  S = kk[a..d]
  I = monomialCurveIdeal(S, {1,3,4})
  R = S/I
  phi = map(R,A,{R_0, R_3})
  B = noetherForm phi
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
  B = noetherForm phi
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
  needsPackage "NoetherNormalForm"
*-

  S = QQ[a..d]
  R = S/monomialCurveIdeal(S,{1,3,4})
  B = noetherForm{a,d}
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
  assert try (B = noetherForm{a,d}; false) else true  
 -- noetherForm{a,d} should fail, as R is not finite over QQ[a,d]
///

TEST ///
-*
  restart
  needsPackage "NoetherNormalForm"
*-
--  needsPackage "NoetherNormalization"
  kk = ZZ/101
  R = kk[x,y]/(x*y-1)
  B = noetherForm R
  describe B
  frac B
  A = kk[t]
  use R
  phi = map(R,A,{x+y})

  noetherForm phi
  noetherForm R
    
  (F, J, xv) = noetherNormalization R
  R' = (ambient R)/J

  G = map(R', R, sub(F.matrix, R'))
  isWellDefined G    
  G^-1 (xv_0)
  ideal R'
  ideal R
  for x in xv list G^-1 x
  A = kk[t]
  phi = map(R, A, for x in xv list G^-1 x)
  noetherForm phi
///


TEST ///
-*
  restart
  needsPackage "NoetherNormalForm"
*-
  kk = ZZ/101
  R = kk[a,b,c,d]
  I = ideal"a2,ab,cd,d2"
  S = reesAlgebra I
  S = first flattenRing S

  noetherNormalization S
  B = noetherForm S
  assert (numgens coefficientRing B == 5)
  assert(radical ideal leadTerm ideal B == ideal gens ambient B)

  T = kk[t_0..t_4]
  use S
  f = map(S,T,{w_0+w_2+b, w_3+a+c, w_1+w_2+d, a+b+d, w_2+c+d})
  assert isModuleFinite f
  B = noetherForm f
  assert isModuleFinite B
  assert(numgens coefficientRing B == 5)
  assert(radical ideal leadTerm ideal B == ideal gens ambient B)

-- We found this system of parameters as follows:
-- This code is not run automatically as the first line takes too much space
-*
  elapsedTime sss = subsets(ss = (subsets(gens S, 3)/sum),5);
  #sss
  i = 0
  f = map(S,T,sss_0)
  while not isModuleFinite f do (i= random (#sss); f =  map(S,T,sss_i);print i)
*-
///

end----------------------------------------------------------
restart
load "NoetherNormalForm.m2"

uninstallPackage "NoetherNormalForm"
restart
installPackage "NoetherNormalForm"
check NoetherNormalForm

restart
needsPackage  "NoetherNormalForm"
check NoetherNormalForm

doc ///
  Key
  Headline
  Usage
  Inputs
  Outputs
  Description
    Text
    Example
  Caveat
  SeeAlso
///

