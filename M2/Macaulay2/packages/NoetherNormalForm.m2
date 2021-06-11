newPackage(
        "NoetherNormalForm",
        Version => "0.1", 
        Date => "9 July 2020",
        Authors => {
            {Name => "David Eisenbud", 
                Email => "de@msri.org", 
                HomePage => "http://www.msri.org/~de/"},
            {Name => "Mike Stillman", 
                Email => "mike@math.cornell.edu", 
                HomePage => "http://www.math.cornell.edu/~mike"}
            },
        Headline => "code for Noether normal forms of affine rings",
        PackageExports => {"NoetherNormalization", "PushForward"},
        DebuggingMode => true
        )

-- TODO:
--  Currently (Feb 2021) one test fails (#14 at the moment), as 
--    noetherForm should give an error, but it doesn't. (this is (1), next line)
--  1. bug: finiteness is still not checked?
--  2. bug: if original ring has multigrading, then get an error.
--  remove old bracketed code
--  get noetherForm(RingMap) to work with the other methods.
--  if R is multigraded, then we get an error.  Fix.  What do we want to happen?
--  place this code into NoetherNormalization?
--  call the functions here noetherNormalization?

-- TODO:
--  need a function that takes B, and determines if it has been placed into this form?
--    inNoetherForm -- change name?  MAYBE OK?
--  test noetherForm for all kinds of rings/gradings.
--
--    DONE trace? of an element in B or L = frac B.
--    DONE noetherBasis (getBasisMatrix) (of frac B, of B?)
--    discriminant?

export {
--    "isFiniteOverCoefficientRing", -- TODO: get this to work
--    "checkNoetherNormalization", -- TODO: get this to work
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

raw = value Core#"private dictionary"#"raw"
rawIsField = value Core#"private dictionary"#"rawIsField"
isField EngineRing := R -> (R.?isField and R.isField) or rawIsField raw R

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
computeBasis Ring := Sequence => (R) -> (
    -- assumption: R is finite over the coefficient ring
    -- returns a sequence (B, S, H):
    --   B: matrix of module generators of R over its coeff ring
    --   S: not sure: seems to be a hashtable: each monom over ambient => actual monom in R.
    --   H: hashtable, keys: monomial generators, value: index in B.
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
    L := flatten entries B;
    H := hashTable for i from 0 to #L-1 list L#i => i;
    Rambient := ambient R;
    S := new MutableHashTable from apply(L, s -> {lift(s,Rambient),s});
    (B, S, H)
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
    if R === NI#"ring" then first NI#"basis of ring"
    else if R === NI#"field" then first NI#"basis of field"
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

-*
-- TODO: this function is not general enough?
isFiniteOverCoefficients1 = method()
isFiniteOverCoefficients1 Ring := Boolean => R -> (
    g := gens gb ideal R;
    S := coefficientRing R;
    lt := flatten entries (leadTerm g%promote(ideal vars S,ring g));
    #select(lt/support , l->#l==1) == numgens R
    )
*-
    
TEST/// -- of finiteOverCoefficients
-*
  restart
*-
  debug needsPackage "NoetherNormalForm"
  R1 = ZZ/5[a,b][x,y]/intersect(ideal (a*(x-1),y), ideal(x^2,y^2))
  R2 = ZZ/5[a,b][x,y]/intersect(ideal (a*x-1,y), ideal(x^2,y^2))
  R3 = ZZ/5[a,b][x,y]/intersect(ideal ((a-1)*x-1,y), ideal(x^2,y^2))
  R4 = QQ[a,b][x,y]
  R5 = QQ[a,b][x,y]/ideal(x^2-a,y^2-b)
  R6 = QQ[x,y]/(x^2-1, x*y^3-3)
  R7 = GF(27)[x,y]/(x^2-1, y^3-a)
  R8 = GF(27)[x,y]/(x^2-1, x*y^3-a)
  R9 = QQ[x,y]/(x^2, x*y^3-3) -- is trivial.
  x = symbol x; y = symbol y
  R10 = QQ[a..d]/(b^2-a, b*c-d)

  assert not isModuleFinite R1
  assert not isModuleFinite R2
  assert not isModuleFinite R3
  assert not isModuleFinite R4
  assert isModuleFinite R5
  assert isModuleFinite R6
  assert isModuleFinite R7 
  assert isModuleFinite R8 

  assert isModuleFinite R9 --wrong

  assert not isModuleFinite R10

  assert isModuleFinite ZZ -- wrong-- a bug! should say "no CoefficientRing present"

  assert isModuleFinite (ZZ/32003) --wrong -- a bug! should say "no CoefficientRing present"

  assert isModuleFinite QQ
  
  assert not isModuleFinite map(QQ , ZZ) -- bug

  assert isModuleFinite (A = frac (QQ[a,b]))

  assert isModuleFinite ( (frac (QQ[a,b]))[x]/(a*x^2-1))
  
  A = (frac (QQ[a,b]));
  R11 = A[x]/(a*x^2-1)
  coefficientRing R11 === A
  assert isModuleFinite R11
  assert not isModuleFinite A


  A = (frac (ZZ[a,b]));
  R12 = A[x]/(a*x^2-1)
  assert isModuleFinite R12

  A = toField(QQ[a]/(a^2-a-1))
  R13 = A[x,y]/(x^2-a, a*y^3-x)
  assert isModuleFinite R13

  kk = toField(QQ[a]/(a^2-a-1))
  A = kk[t]
  R14 = A[x,y]/(x^2-a*t, a*y^3-x-t)
  assert isModuleFinite R14
  
  assert isModuleFinite(A = ZZ[]/32743287482974)
  coefficientRing A  
  
  A = ZZ/101[a,b]
  B = A[x,y]/(x^2+y^2)
  R15 = B[z]/(z^3-1)
  coefficientRing R15
  assert isModuleFinite R15
  assert(not isModuleFinite map(R15,A))
///

-*
isFiniteOverCoefficientRing = method()
isFiniteOverCoefficientRing Ring := Boolean => (R) -> (
    if R.?NoetherInfo then return true;
    if isField R then return true;
    if not isAffineRing R then return false; 
    A := coefficientRing R;
    --if not (try (coefficientRing R; true) else false) then return false;
    --if there is a coefficientRing R then does nothing; if not then the whole funct returns false.

    --    if isField A then return(dim R ===0);

    if not isField A and not isComputablePolynomialRing A then (
	    if debugLevel > 0 then << "expected a quotient of a polynomial ring over a field" << endl;
	    return false);
    if not isFiniteOverCoefficients1 R then (
        if debugLevel > 0 then << "ring is not finite over its coefficient ring" << endl;
        false
        )
    else true
    )    
*-
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
-- TODO: put this check back in once it is working:
--    if not isModuleFinite B
--    then error "expected the ring to be finite over the chosen polynomial ring";
    A := coefficientRing B; -- ASSUME: a polynomial ring over a field.
    KA := frac A;
    kk := coefficientRing A; -- must be a field, but not a fraction field.
    I := ideal B;
    ambientB := ring I;
    ambientKB := ((frac A)(monoid B)); -- TODO: does this handle degrees correctly?
    phiK := map(ambientKB,ambientB, vars ambientKB);
    JK := trim phiK I;
    KB := ambientKB / JK;
    B.frac = KB;
    KB.frac = KB;
    KB.isField = true;
    KB.baseRings = append(KB.baseRings, B);    
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
    numerator B := (f) -> StoB (numerator mapBtofracS f);
    numerator KB := (f) -> StoB (numerator mapKBtofracS f);
    denominator B := (f) -> lift(StoB denominator mapBtofracS f, A);
    denominator KB := (f) -> lift(StoB denominator mapKBtofracS f, A);
    factor KB := opts -> (f) -> hold numerator f/factor denominator f;
    expression KB := f -> expression numerator f / expression denominator f;
    setNoetherInfo(B, KB);
    KB
    )

noetherForm = method(Options => {Remove => null, Variable => getSymbol "t"})

--------- Code below to be removed ---------------------------------------------------------------
noetherForm RingMap := Ring => opts -> (f) -> (
    A := source f;
    R := target f;
    kk := coefficientRing R;
    if not isCommutative A then 
        error "expected source of ring map to be a commutative ring";
    if A === kk then return R;
    if not isAffineRing R then 
        error "expected an affine ring";
    if not isAffineRing A then 
        error "expected an affine ring";
    if not ( kk === coefficientRing A) then 
        error "expected polynomial rings over the same ring";
    gensk := generators(kk, CoefficientRing => ZZ);
    if not all(gensk, x -> promote(x,R) == f promote(x,A)) then 
        error "expected ring map to be identity on coefficient ring";

    ambientB := A[gens R, MonomialOrder => (monoid R).Options.MonomialOrder,
        Degrees => apply(degrees R, f.cache.DegreeMap)
        ]; 
    f' := map(ambientB, A, sub(f.matrix, ambientB));
    J1 := ideal for x in gens A list f' x - x; 
      -- todo: if opts.Remove, take lead terms of these (if they are linear?)
      -- reduce them (in ambient ring?)
      -- the lead terms which are variables in ambientB:
      --   create new ambientB' which leaves these variables out.
      -- then take J2 below, which should not involve the variables removed.
      --   perhaps check that.
      -- is the answer B = ambientB'/J2? (J2 after %J1, moving this to ambientB')
    J2 := sub(ideal R, vars ambientB);
    J2 = trim ideal((gens J2) % J1);
    B := ambientB/(J1 + J2);
    L := makeFrac B;
    B)

-* MES working on this.
noetherForm RingMap := Ring => opts -> (f) -> (
    A := source f;
    R := target f;
    kk := coefficientRing R;
    if not isCommutative A then 
        error "expected source of ring map to be a commutative ring";
    if A === kk then return R;
    if not isAffineRing R then 
        error "expected an affine ring";
    if not isAffineRing A then 
        error "expected an affine ring";
    if not ( kk === coefficientRing A) then 
        error "expected polynomial rings over the same ring";
    gensk := generators(kk, CoefficientRing => ZZ);
    if not all(gensk, x -> promote(x,R) == f promote(x,A)) then 
        error "expected ring map to be identity on coefficient ring";

    S := ambient R;
    keep := findComplement lift(f.matrix, S); -- FIX.
    ambientB := A[keep, Degrees => apply(keep/degree, f.cache.DegreeMap), Join => false
        ];  -- IS CORRECT?
    f' := map(ambientB, A, sub(f.matrix, ambientB)); -- FIX
    J1 := ideal for x in gens A list f' x - x; 
      -- todo: if opts.Remove, take lead terms of these (if they are linear?)
      -- reduce them (in ambient ring?)
      -- the lead terms which are variables in ambientB:
      --   create new ambientB' which leaves these variables out.
      -- then take J2 below, which should not involve the variables removed.
      --   perhaps check that.
      -- is the answer B = ambientB'/J2? (J2 after %J1, moving this to ambientB')
    J2 := sub(ideal R, vars ambientB);
    J2 = trim ideal((gens J2) % J1);
    B := ambientB/(J1 + J2);
    L := makeFrac B;
    B)
*-

-*
noetherForm List := Ring => opts -> (xv) -> (
    -- R should be a quotient of a polynomial ring,
    -- xv a list of variables, algebraically independent in R
    -- result: a ring over the sub-poly ring or subfield generated by
    --  the variables xv.
    -- TODO: allow the xv to be linear forms, or even perhaps higher degree polynomials.
    --   for this part:
    --     make a polynomial ring A with #xv variables.
    --     make a ring map A --> (ring xv's), sending i-th var to xv#i.
    --     call noetherForm Ringmap.
    if #xv === 0 then error "expected non-empty list of variables";
    R := ring xv#0;
    if any(xv, x -> ring x =!= R) then error "expected variables all in the same ring";
    if any(xv, x -> index x === null) then error "expected variables";
    I := ideal R;
    Rambient := ring I;
    xindices := for x in xv list index x;
    otherindices := sort toList (set toList(0..numgens R - 1) - set xindices);
    kk := coefficientRing R;
    A := kk [xv, Degrees => (degrees R)_xindices, Join=>false];
    S := A[(gens R)_otherindices, Degrees => (degrees R)_otherindices, Join=>false];
    phi := map(S,Rambient, sub(vars Rambient, S));
    J := trim phi I;
    B := S/J;
    L := makeFrac B;
    B
    )
*-

noetherForm List := Ring => opts -> (xv) -> (
    -- R should be a quotient of a polynomial ring,
    -- xv a list of algebraically independent polynomials in R
    -- result: a ring over the sub-poly ring or subfield generated by
    --  the xv.
    -- More detail:
    --   If {f0, ..., fr} are the algebraically indep polynomials.
    --   if any is a variable: use that name, remove from list of variables from ambientR
    --          has lead term which is a variable: use a variable t_i, but remove the var from the ambientR vars
    --          is a polynomial whose lead term is not linear: use a variable t_i.
    --   This function constructs a polynomial ring A, and with the remaining set of variables
    --      a quotient A[remaining vars]/I, isomorphic to R.
    
    -- TODO: allow the xv to be linear forms, or even perhaps higher degree polynomials.
    --   for this part:
    --     make a polynomial ring A with #xv variables.
    --     make a ring map A --> (ring xv's), sending i-th var to xv#i.
    --     call noetherForm Ringmap.
    if #xv === 0 then error "expected non-empty list of ring elements";
    R := ring xv#0;
    if any(xv, x -> ring x =!= R) then error "expected elements all in the same ring";
    I := ideal R;
    ambientR := ring I; 
    gensR := new MutableList from gens ambientR;
    --gensA1 := select(xv, f -> index f =!= null); -- keep these in order.  Note that there should not be two the same.
    --if #gensA1 != #(unique gensA1) then error "cannot have same variable occuring twice";
    count := -1;
    -- this loop returns a list of {varname, value in R}, 
    -- and it also modifies gensR (sets any variable to null that should not be in gens of B).
    elems := for f in xv list (
        if index f =!= null then ( --index of the variable in R
            gensR#(index f) = null;
            {f, f}
            )
        else (
            m := leadMonomial f;
            if index m =!= null then (
                gensR#(index m) = null;
                );
            count = count+1;
            {(opts.Variable)_count, f}
        ));
    keepList := select(toList gensR, x -> x =!= null);
    -- Create A and B' (ambient for the soon to be created B).
    A := (coefficientRing R)(monoid [elems/first]);
    B' := A(monoid [keepList, Join => false]);
    -- Now create B, and the isomorphism phi: B --> R
    phi' := map(R, B', keepList | (elems/last));
    J := trim ker phi';
    B := B'/J;
    phi := map(R, B, phi'.matrix);
    -- Now create the inverse of phi.  One should be able to do phi^-1, but fails (Sep 2020, 1.16)
    -- Here is a workaround for the moment.
    workAroundInverse phi; -- sets inverse of phi.
-*    
    (B'', F) := flattenRing B; -- B == source phi, R == target phi
    phi.cache.inverse = F^-1 * (phi * F^-1)^-1;
    phi.cache.inverse.cache.inverse = phi;
    assert(phi^-1 * phi === id_(source phi));
    assert(phi * phi^-1 === id_(target phi));
*-
    B.cache#"NoetherMap" = phi; -- TODO: where to put this.
    L := makeFrac B;
    B
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

--------- Code above to be removed ---------------------------------------------------------------

  -- This one we would like to have the base be A = kk[t_0, t_1],
  -- and B = A[c,d], know that t_0 --> a+b, t_1 --> a+d.
  --                  a = d - t_1
  --   therefore that b = d + t_0 - t_1.  How do we get this?
  -- we have seversal sets of variables:
  --  newA -- from linear equations, or higer degree elements of R.
  --  oldA -- from B itself, these are variables in the list.
  --  rewriteB -- these are variables we don't need, but we do need to know how to write them
  --        in the new ring.
  --  keepB -- these are the variables of B.  A subset of the current set of variables of R.
  --
  -- we are given the list L of polynomials (in ambient ring of R) that will form the variables of A
  --   if L_i is a variable in ambientR, then use that name, remove from list of keepB, otherwise use a new name.
  --   at this point, we can form the subring A.
  -- now, we need the variables we will use in B
  --   


createCoefficientRing = method(Options => {Variable => getSymbol "t"})
createCoefficientRing(Ring, List) := RingMap => opts -> (R, L) -> (
    count := -1;
    t := opts.Variable;
    coeffVarNames := for f in L list (
        if index f  =!= null then 
            f 
        else (
            count = count+1;
            t_count
            )
        );
    A := (coefficientRing R)(monoid [coeffVarNames]);
    map(R, A, L)
    )

  -- The following is currently hideous code to do something simple.
  createRingPair = method()
  createRingPair(RingMap) := RingMap => (f) -> (
      -- Given f : A --> R (R a polynomial ring) (A,R polynomial rings)
      -- create a ring B = A[new vars]/I, and an isomorphism R --> B.
      --   preferably, the ideal I has no linear forms of the "new vars".
      -- Return a ring map phi: R --> B
      A := source f;
      kk := coefficientRing A;
      R := target f;
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

noetherForm List := Ring => opts -> (xv) -> (
    -- R should be a quotient of a polynomial ring,
    -- xv a list of algebraically independent polynomials in R
    -- result: a ring over the sub-poly ring or subfield generated by
    --  the xv.
    -- More detail:
    --   If {f0, ..., fr} are the algebraically indep polynomials.
    --   if any is a variable: use that name, remove from list of variables from ambientR
    --          has lead term which is a variable: use a variable t_i, but remove the var from the ambientR vars
    --          is a polynomial whose lead term is not linear: use a variable t_i.
    --   This function constructs a polynomial ring A, and with the remaining set of variables
    --      a quotient A[remaining vars]/I, isomorphic to R.
    
    -- TODO: allow the xv to be linear forms, or even perhaps higher degree polynomials.
    --   for this part:
    --     make a polynomial ring A with #xv variables.
    --     make a ring map A --> (ring xv's), sending i-th var to xv#i.
    --     call noetherForm Ringmap.
    if #xv === 0 then error "expected non-empty list of ring elements";
    R := ring xv#0;
    if any(xv, x -> ring x =!= R) then error "expected elements all in the same ring";
    I := ideal R;
    -- First we create the rings A --> ambientB, without regard to I.
    ambientR := ring I;
    xvAmbientR := for x in xv list lift(x, ambientR);
    f := createCoefficientRing(ambientR, xvAmbientR, Variable => opts.Variable);
    F := createRingPair f;
    G := inverse F;
    -- now we need to descend this to R --> B = ambientB/(image of I)
    J := trim (G I); 
    B := (target G)/J;
    L := makeFrac B;
    -- Now create the isomorphism B --> R and its inverse.
    GR := map(B, R, G.matrix);
    FR := map(R, B, F.matrix);
    GR.cache.inverse = FR;
    FR.cache.inverse = GR;
    B.NoetherInfo#"noether map" = FR; -- stash the map B --> R, but the other can be obtained via 'inverse'
    B
    )

-- Input: a ring map F : A --> R such that:
--   (a) A is a polynomial ring over a field, TODO: should allow a field too!
--   (b) R is a quotient of a polynomial ring over the same field
--   (c) R is a finite A-module
-- Output:
--   A ring B = A[vars]/I
--     which is isomorphic to R (the isomorphism is available as `noetherMap B`)
--     if A is the base field of R, then B should be the same as A.
-- Notes
--   (a) the `noetherMap B` is stored in B, not the original R.
--   (b) if the image of a variable is a variable, that variable is not in `vars`
--   (c) if the image of a variable is a linear polynomial, one of the variables present will not be 
--        placed into the vars of B.
noetherForm RingMap := Ring => opts -> (f) -> (
    A := source f;
    R := target f;
    kk := coefficientRing R;
    if not isCommutative A then 
        error "expected source of ring map to be a commutative ring";
    if not isAffineRing R then 
        error "expected an affine ring";
    if not isAffineRing A then 
        error "expected an affine ring";
    if not (kk === A or kk === coefficientRing A) then 
        error "expected polynomial rings over the same ring";
    gensk := generators(kk, CoefficientRing => ZZ);
    if not all(gensk, x -> promote(x,R) == f promote(x,A)) then 
        error "expected ring map to be identity on coefficient ring";
    --check finiteness
    -- if not isModuleFinite(A, R) then 
    --     error "expected ring to be finite over coefficients";

    if A === kk then (
        setNoetherInfo(R, R);
	    return R
        );
    
     -- AAA    

    ambientB := A[gens R, MonomialOrder => (monoid R).Options.MonomialOrder,
        Degrees => apply(degrees R, f.cache.DegreeMap)
        ]; 
    f' := map(ambientB, A, sub(f.matrix, ambientB));
    J1 := ideal for x in gens A list f' x - x; 
      -- todo: if opts.Remove, take lead terms of these (if they are linear?)
      -- reduce them (in ambient ring?)
      -- the lead terms which are variables in ambientB:
      --   create new ambientB' which leaves these variables out.
      -- then take J2 below, which should not involve the variables removed.
      --   perhaps check that.
      -- is the answer B = ambientB'/J2? (J2 after %J1, moving this to ambientB')
    J2 := sub(ideal R, vars ambientB);
    J2 = trim ideal((gens J2) % J1);
    B := ambientB/(J1 + J2);
    L := makeFrac B;
    B)

noetherForm Ring := Ring => opts -> R -> (
    (F, J, xv) := noetherNormalization R;
    kk := coefficientRing R;
    t := opts.Variable;
    A := if #xv == 0 then kk else kk[t_0..t_(#xv-1)];
    phi := map(R,A,for x in xv list F^-1 x);
    noetherForm (phi, Remove => opts.Remove)
    )

TEST ///
-*
restart
debug needsPackage "NoetherNormalForm"
*-
  -- Zero dimensional noetherForm...

  R = QQ[x,y]/(x^4-3, y^3-2);
  phi = map(R, QQ, {})
  noetherForm phi
  assert inNoetherForm R
  
  kk = ZZ/32003
  R = kk[x,y]/(x^4-3, y^3-2);
  phi = map(R, kk, {})
  isWellDefined phi  -- ok
  B = noetherForm R
  assert inNoetherForm R

  kk = QQ
  R = kk[x,y]/(x^4-3, y^3-2);
  phi = map(R, kk, {})
  -- TODO: isWellDefined phi -- fails... BUG in Core... git issue #1998
  assert inNoetherForm B

  kk = GF(27)
  R = kk[x,y]/(x^4-2, y^5-2);
  phi = map(R, kk, {})
  isWellDefined phi  -- ok
  B = noetherForm R
  noetherBasis B
  traceForm B -- (now works). (used to fail! due to the bug below, which is now git issue #1999)

  kk = QQ
  R = kk[x,y]/(x^4-2, y^5-2);
  phi = map(R, kk, {})
  B = noetherForm R
  noetherBasis B
  traceForm B
  det oo

  -- bug in M2 #1999  
  -- kk = ZZ/101
  -- R = kk[x]
  -- f = matrix(kk, {{1,1}})  
  -- g = map(R^{0,1},, {{1,1},{1,1}})
  -- f*g
///

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
  B = noetherForm{a,d};
  presentation B
  assert try (B = noetherForm{a,d}; false) else true  -- should give an error message
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

  noetherForm({a - w_0,b,c,d,w_0 + w_1 + w_2 + w_3})  

  elapsedTime (F, J, xv) = noetherNormalization S -- wow, this takes more time than I would have thought! 3.1 sec on my macbookpro, Sep 2020.

  xv/(x -> F x)

  F (ideal S) == J  
  R' = (ambient S)/J  
  A = kk[t_0..t_(#xv-1)]
  
  phi = map(S,A, xv/(x -> F x))
  
  B = noetherForm phi
  L = frac B
  describe L
  
  isHomogeneous S -- true
  isHomogeneous R' -- false
  
  noetherForm S
///

end----------------------------------------------------------

restart
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

kk= ZZ/101
S = kk[a,b, Degrees =>{2:{-2,3}}, Join => false]
I = ideal(a^2,b^2)
R = reesAlgebra(I,a)
A = first flattenRing R
B = ambient R
C = first flattenRing B
M = matrix{{1_S,2_S},{1_S,2_S}}
MR = sub(M, R)
MA = sub(M, A)
MB = sub(M, B)
MC = sub(M, C)

lift(M,kk)
lift(MR,kk)
lift(MA,kk)
lift(MB,kk)
lift(MC,kk) -- error

describe S
describe kk

monoid ring oo26
options oo

options monoid A
methods flattenRing
code 2
code 
