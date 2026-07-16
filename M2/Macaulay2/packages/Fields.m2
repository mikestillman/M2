newPackage(
    "Fields",
    Version => "0.11", 
    Date => "8 April 2025",
    Authors => {
        {
            Name => "Frank Moore", 
            Email => "moorewf@wfu.edu",
            HomePage => "https://sites.google.com/wfu.edu/frank-moore"},
        {
            Name => "Mike Stillman",  
            Email => "mike@math.cornell.edu", 
            HomePage => "http://www.math.cornell.edu/~mike"}
        },
    Headline => "algorithms for more general fields",
    PackageImports => {"Elimination", "ModularMethods"},
    Keywords => {"Computer Algebra"},
    AuxiliaryFiles => true,
    DebuggingMode => true
    )

export {
    "Field",
    "FactorData",
    "FieldInfo",
    "PrimitiveInfo",
    
    "adjoinRoot",
    "baseField",
    "basicField",
    "coeffsInBasis",
    "denominatorRing",
    "displayFieldInfo",
    "distinctDegreeFactors",
    "extensionBasis",
    "extensionDegree",
    "factorData",
    "factors",
    "field",
    "fieldGens",
    "fieldContent",
    "fieldInclusion",
    "fieldInfo",
    "getCoefficientField",
    "inducedMapOnFields",
    "isBasicField",  -- doc done
    "isFieldInNormalForm",
    "isFiniteExtensionField",
    "isFiniteField", -- doc done
    "isFractionField",
    "isIrreducible",
    "isPrimeField", -- doc done
    "makeMonic",
    "minimalPolynomial",
    "monicAssociate",
    "monicFactorData",
    "monicFactors",
    "monicGCD",
    "monicGCD0", -- move to ModularMethods! Or better, remove it??
    "monicGCDNaive",
    "monicGCDModular",
    "multiplicationMap",
    "mydenominator",
    "numeratorMap",
    "prettyFactor",
    "primitiveAssociate",
    "randomElement",
    "reductionMap",
    "splittingField",
    "squareFreeFactors",
    "translatedResultant",
    "useTower",

    "AssumeIrreducible",
    "Coefficient",
    "Factors",
    "FieldInclusion",
    "Finites",
    "FromPrimitive",
    "LiftBack",
    "Independents",
    "MinimalPolynomial",
    "ToPrimitive"
    }

ISSUE = method()
--ISSUE String := str -> TEST str;
ISSUE String := str -> ();

BENCHMARK = method()
--BENCHMARK String := str -> TEST str;
BENCHMARK String := str -> ();

TOOSLOW = method()
--TOOSLOW String := str -> TEST str;
TOOSLOW String := str -> ();

importFrom_Core { "commonEngineRingInitializations" }

Field = new Type of PolynomialRing
FieldInfo = new Type of HashTable
FactorData = new Type of HashTable
PrimitiveInfo = new Type of HashTable

-- TODO
-- see ~/src/M2-workshops/Workshop-2011-IMA/PrimaryDecomposition/

-- BUG list/todo
-- 1. toField Ring allows non-finite extensions, and currently does the wrong thing with them
-- 2. 'field' is this the right name to return the field of something?
-- 3. when creating a field, need to put it in normal form, but also have maps both ways...
--    I haven't done the maps yet...
-- 4. ZZ should be the base in frac(ZZ[...])... not QQ?
-- 5. finite extensions which are linear should not be placed in here (at least by default).
-- 6. field(R/I, IndependentSet => {...}) should take an optional argument with a choice of max indep set.
-- 7. R --> field R.
-- 8. field(R/I, Base => ...).  To allow changing base field from GF p^n to GF p, or something
-- 9. denominator, numerator : field R --> ??  what ring are these elements in?
-- 10. factor of an element in K[x's].
--  K[x,y][z]
--  (K(x,y)/I)[z, w, ...] 

-- basic fields:
--  ZZ/p (p could be "small" or "big")
--  QQ
--  GF(q) -- maybe

-- rational fraction fields K(t1, ..., tr), K is basic.
-- if K is not basic, still want the constructor
--  frac(K[t1, ..., tr]) --> maybe should give the normal form.

-- if given a ring K (not nec basic), and an ideal I in K[x1, ..., xn]
-- such that I is a maximal ideal in this field.
-- form L = K[x1, ..., xn, Lex]/gb(I)

-- normal form for a field: (K is a basic field)
-- L = K(t1, ..., tr)[x1, ..., xn]/I
-- 

-- frac K[t1, ..., tr, x1, ..., xn]/I
-- frac(R, IndependentSet => {t1, ..., tr})
-- frac
-- frac(R/I), but R/I has dim > 0, (I is prime)

-- denominator should work for R = K[y1,...,ym]

-- inseparable field extensions:
-- K = ZZ/p(t)
-- frac(K[x]/(x^p-t))
-- represent

-------
-- variable iteration code
VariableIterator = new Type of Iterator

variableIterator = method(Options => {"MaxVars" => infinity})
variableIterator(List, Symbol) := VariableIterator => opts -> (myVarList, myIndexedVar) -> (
    Iterator (
        -- local variables keeping state
        varList := myVarList;
        indexedVar := myIndexedVar;
        thisVar := 0;
        maxVars := opts#"MaxVars";
        -- iteration function
        () -> (
            if thisVar >= maxVars then return StopIteration;
            result := if thisVar < #varList then
                         varList#thisVar
                      else
                         indexedVar_(thisVar - #varList);
            thisVar = thisVar + 1;
            result
        )
    )
)

-*
  restart
  debug needsPackage "Fields"
*-
///
varIter = variableIterator({x,y,z},a,"MaxVars"=>6)
for var in varIter list var
///

--------

isFiniteField = method()
isPrimeField = method()
isBasicField = method()
isFractionField = method()
isFiniteExtensionField = method()

-- Todo: these are not quite correct!  I mean, really not right...
isFiniteField Ring := R -> (
    -- need to allow finite extension of ZZ/p too!
    isField R and
    (instance(R, GaloisField) or (instance(R,QuotientRing) and ambient R === ZZ and char R > 0))
    )
isPrimeField Ring := R -> (
    R === QQ or
    (isField R and isQuotientRing R) or -- if R is ZZ/p
    (instance(R, GaloisField) and isPrime R.order)  -- if R is GF (prime)
    )
isBasicField Ring := R -> isPrimeField R or isFiniteField R
isFractionField Ring := Boolean => R -> instance(R, FractionField)
isFiniteExtensionField Ring := Boolean => R -> (
    if not isField R then return false;
    if not isPolynomialRing R then return false;
    if numgens R > 0 then return false;
    R1 := coefficientRing R; -- this is the "real" extension
    isBasicField coefficientRing R1 and dim R1 === 0
    )

isFieldInNormalForm = method()
isFieldInNormalForm Ring := Boolean => R -> (
    isBasicField R or R.?cache and R.cache.?FieldInfo
    )

getCoefficientField = method()
getCoefficientField Ring := Ring => R -> (
    -- returns null, if not over a field in normal form.
    -- returns this normal from field otherwise.  If R is a field, returns R.
    if isFieldInNormalForm R then return R;
    K := coefficientRing R;
    while ZZ =!= K and not isFieldInNormalForm K do
        K = coefficientRing K;
    if K === ZZ then null else K
    )

-- TODO: this is not quite correct.
-- e.g. over GF(4), the variable a is not set to the generator of GF 4.
useTower = method()
useTower Ring := R -> (
    A := R;
    coefRings := while A =!= null list (
        ans := A;
        A = try coefficientRing A else null;
        if A === null then break;
        ans
        );
    --print coefRings;
    for a in reverse coefRings do use a
    )

isWellDefined FieldInfo := FI -> (
    if set keys FI =!= set {
        symbol denominator, symbol content,
        symbol Base, symbol Independents, symbol Finites,
        symbol cache} then return false;
    if FI.Base === null or not isBasicField FI.Base then return false;
    if FI.Independents =!= null and not instance(FI.Independents, FractionField) then return false;
    if FI.Finites =!= null and not instance(FI.Finites, Ring) then return false;
    if FI.Independents =!= null then (
        K := FI.Independents;
        if coefficientRing K =!= FI.Base then return false;
        );
    if FI.Finites =!= null then (
        A := FI.Finites;
        --if not isFiniteExtensionField A then return false;
        KA := coefficientRing A;
        if FI.Independents === null and (KA =!= FI.Base) then return false;
        if FI.Independents =!= null and (KA =!= FI.Independents) then return false;
        );
    -- TODO: also check that the defining ideal is prime?
    true
    )

mydenomQQ = (tmsf) -> tmsf/denominator//lcm
mydenomQQz = (tmsf) -> (
    -- in this case, each element of tmsf is in K = (QQ[zs]/Iz)[],
    -- which is a "toField" ring.  ie. to see the element here, we need to
    -- strip off the 0-variable ring.
    -- the answer should be an integer.
    -- first, get a list of coefficients in QQ[z1, z2]/Iz:
    g1 := tmsf/leadCoefficient; -- list of elements in K, not K[].
    g2 := g1/terms//flatten/leadCoefficient; -- should be elements in QQ
    mydenomQQ g2
    )
mydenomQQt = (tmsf) -> (
    -- each element of tmsf is in K = QQ(ts).
    -- take the denominator of each, and then after that we need to remove the
    --   denominator part in ZZ.
    --g1 := tmsf/leadCoefficient; -- list of elements in K, not K[].
    g2 := tmsf/denominator//lcm; -- should be elements in ZZ[t1,t2]
    g2
    )
mydenomQQtz = (tmsf) -> (
    g1 := tmsf/leadCoefficient;
    g2 := g1/terms//flatten/leadCoefficient;
    g2/denominator//lcm
    )

mydenomFq = (tmsf) -> (
    -- ASSUME: tmsf is a non-empty list of non-zero elements of a field or ring
    -- this just returns 1 over the base field
    L := basicField getCoefficientField ring tmsf_0;
    1_L
    )
mydenomFqz = (tmsf) -> (
    -- in this case, each element of tmsf is in K = (QQ[zs]/Iz)[],
    -- which is a "toField" ring.  ie. to see the element here, we need to
    -- strip off the 0-variable ring.
    -- the answer should be an integer.
    -- first, get a list of coefficients in QQ[z1, z2]/Iz:
    L := basicField getCoefficientField ring tmsf_0;
    1_L
    )
mydenomFqt = (tmsf) -> (
    -- SAME as mydenomQQt (at least when I write this).
    -- each element of tmsf is in K = QQ(ts).
    -- take the denominator of each, and then after that we need to remove the
    --   denominator part in ZZ.
    ---- wrong: g1 := tmsf/leadCoefficient; -- list of elements in K, not K[].
    g2 := tmsf/denominator//lcm; -- should be elements in Fq[t1,t2]
    g2
    )
mydenomFqtz = (tmsf) -> (
    g1 := tmsf/leadCoefficient;
    g2 := g1/terms//flatten/leadCoefficient;
    g2/denominator//lcm
    )

mycontentQQ = (tmsf) -> (
    g := gcd tmsf;
    if tmsf_0 > 0 then g else -g
    )
mycontentQQz = (tmsf) -> (
    -- in this case, each element of tmsf is in K = (QQ[zs]/Iz)[],
    -- which is a "toField" ring.  ie. to see the element here, we need to
    -- strip off the 0-variable ring.
    -- the answer should be an integer.
    -- first, get a list of coefficients in QQ[z1, z2]/Iz:
    g1 := tmsf/leadCoefficient; -- list of elements in K, not K[].
    g2 := g1/terms//flatten/leadCoefficient; -- should be elements in QQ
    mycontentQQ g2
    )
mycontentQQt = (tmsf) -> (
    -- each element of tmsf is in K = QQ(ts).
    -- take the denominator of each, and then after that we need to remove the
    --   denominator part in ZZ.
    --g1 := tmsf/leadCoefficient; -- list of elements in K, not K[].
    sgn := if leadCoefficient numerator tmsf_0 > 0 then 1 else -1;
    n := tmsf/numerator//gcd;
    if sgn === -1 then n = -n;
    d := tmsf/denominator//lcm;
    n/d -- let's make sure this is in K!
    )
mycontentQQtz = (tmsf) -> (
    g1 := tmsf/leadCoefficient;
    g2 := g1/terms//flatten/leadCoefficient;
    mycontentQQt g2
    )

mycontentFq = (tmsf) -> (
    -- ASSUME: tmsf is a non-empty list of non-zero elements of a field or ring
    -- this just returns 1 over the base field
    tmsf_0 -- is just the lead coefficient...
    )
mycontentFqz = (tmsf) -> (
    -- in this case, each element of tmsf is in K = (QQ[zs]/Iz)[],
    -- which is a "toField" ring.  ie. to see the element here, we need to
    -- strip off the 0-variable ring.
    -- the answer should be an integer.
    -- first, get a list of coefficients in QQ[z1, z2]/Iz:
    leadCoefficient leadCoefficient tmsf_0
    )
mycontentFqt = (tmsf) -> (
    lt := leadCoefficient numerator tmsf_0; -- should be an element of Fq.
    n := tmsf/numerator//gcd; -- should be monic...
    d := tmsf/denominator//lcm;
    (lt*n) / d
    )
mycontentFqtz = (tmsf) -> (
    g1 := tmsf/leadCoefficient;
    g2 := g1/terms//flatten/leadCoefficient;
    lt := leadCoefficient numerator g2_0; -- should be an element of Fq.
    n := g2/numerator//gcd; -- should be monic... 
    d := g2/denominator//lcm;
    (lt*n) / d
    )

denomFunction = new HashTable from {
    {true, true, true} => mydenomQQtz,
    {true, true, false} => mydenomQQt,
    {true, false, true} => mydenomQQz,
    {true, false, false} => mydenomQQ,
    {false, true, true} => mydenomFqtz,
    {false, true, false} => mydenomFqt,
    {false, false, true} => mydenomFqz,
    {false, false, false} => mydenomFq
    }

contentFunction = new HashTable from {
    {true, true, true} => mycontentQQtz,
    {true, true, false} => mycontentQQt,
    {true, false, true} => mycontentQQz,
    {true, false, false} => mycontentQQ,
    {false, true, true} => mycontentFqtz,
    {false, true, false} => mycontentFqt,
    {false, false, true} => mycontentFqz,
    {false, false, false} => mycontentFq
    }

-- This is NOT to be exported...
setFieldInfo' = method(Options => {Base => null, Independents => null, Finites => null})
setFieldInfo' Ring := FieldInfo => opts -> R -> (
    if not R.?cache then R.cache = new CacheTable;
    if R.cache.?FieldInfo then return; -- don't need to set anything...  Maybe we should check that Independents, Finites match, if present...
    -- TODO: cannot reset values once set...  So give an error if this is attempted...
    -- determine the denominator function
    fieldtype := {opts.Base === QQ,
        opts.Independents =!= null,
        opts.Finites =!= null};
    denomFcn := denomFunction#fieldtype;
    contentFcn := contentFunction#fieldtype;
    R.cache.FieldInfo = new FieldInfo from {
        Base => opts.Base,
        Independents => opts.Independents,
        Finites => opts.Finites,
        symbol denominator => denomFcn,
        symbol content => contentFcn,
	symbol cache => new CacheTable from {}
        };
    R.cache.FieldInfo
    )

-- This is NOT to be exported...
setFieldInfo = method()
setFieldInfo Ring := R -> (
    if not R.?cache then R.cache = new CacheTable;
    if R.cache.?FieldInfo then return;
    if isBasicField R then (
        setFieldInfo'(R, Base => R);
        )
    else if isFractionField R then (
        setFieldInfo'(R, Base => coefficientRing R, Independents => R);
        )
    else if isFiniteExtensionField R then (
        R1 := coefficientRing R; -- this is the actual extension.
        K1 := coefficientRing R1; -- this is either a basic field or a fraction field.
        if dim R1 != 0 then error "dimension of finite extension part is not zero";
        setFieldInfo K1; -- field info of the base
        FI := K1.cache.FieldInfo;
        setFieldInfo'(R1, Base => FI.Base, Independents => FI.Independents,
            Finites => R1);
        setFieldInfo'(R, Base => FI.Base, Independents => FI.Independents,
            Finites => R1);
        )
    else if R === ZZ then return -- do nothing here
    else
        error "field is not in normal form";
    )

fieldInfo = method()
fieldInfo Ring := HashTable => R -> (
    setFieldInfo R;
    R.cache.FieldInfo
    )

displayFieldInfo = method()
displayFieldInfo Ring := HashTable => R -> (
    setFieldInfo R;
    info := pairs R.cache.FieldInfo;
    if R.cache.FieldInfo#Finites =!= null then
        info = append(info, Ideal => netList (ideal coefficientRing R)_*);
    new HashTable from info
    )

baseField = method()
baseField Ring := Ring => R -> (
    if R === ZZ then error "Expected a ring with a base field.";
    if isField R then (
        FI := fieldInfo R;
        return FI.Base;
        );
    baseField coefficientRing R
    )

rationalBaseField = method()
rationalBaseField Ring := Ring => R -> (
    if R === ZZ then error "Expected a ring with a base field.";
    if isField R then (
        FI := fieldInfo R;
        return if FI.?Independents and FI.Independents =!= null then FI.Independents else FI.Base;
        );
    rationalBaseField coefficientRing R
    )    

hasFiniteExtension = method()
hasFiniteExtension Ring := Boolean => R -> (
    -*
    if isField R then (
        FI := fieldInfo R;
        return FI.Independents =!= FI.Finites;
        );
    *-
    if isField R then (
        FI := fieldInfo R;
        return FI.Finites =!= null;
        );
    error "expected a field";
)

hasRationalExtension = method()
hasRationalExtension Ring := Boolean => R -> (
    -*
    if isField R then (
        FI := fieldInfo R;
        return FI.Independents =!= FI.Base;
        );
    *-
    if isField R then (
        FI := fieldInfo R;
        return FI.Independents =!= null;
        );    
    error "expected a field"
)

-- internal function to strip off toField'ed outer []
basicField = method()
basicField Ring := (K) -> (
    -- assumption: K is either a basic field (QQ, ZZ/p, GF q), or
    -- is in "normal form"
    if not isField K then error "expected a field as input";
    if instance(K, FractionField) then coefficientRing K
    else if instance(K, PolynomialRing) and numgens K == 0 then coefficientRing coefficientRing K
    else K
    )

-*
basicField Ring := K -> (
    if isFiniteField K or K === QQ then return K;
    FI := fieldInfo K;
    if FI.Independents
)
*-

combineFields = method()
combineFields(Ring, Ring, List, List) := RingMap => (K, R, indeps, fibervars) -> (
    -- note: R should be a flattened ring...
    FI := fieldInfo K;
    I := ideal R;
    -- create frac field part
    
    -- WIP: fix QQ/ZZ/all cases of independents in base and extension
    -*
    R2 := if FI.Independents =!= null then (
	     if indeps == {} then FI.Independents else (
	        fracvars := join(if FI.Independents === null then {} else gens FI.Independents, indeps);
	        B := FI.Base;
	        if B === QQ then B = ZZ;
	        R1 := B(monoid [fracvars]);
	        ans := frac R1;
	        setFieldInfo'(ans, Base => FI.Base, Independents => ans);
	        ans
	     )
	  else (
	     
	  );
    *-

    -- first: do we have any fraction vars at all?
    R2 := if FI.Independents =!= null and indeps == {} then 
        FI.Independents
    else if indeps =!= {} then (
        -- yes, we need to create a fraction field here.
        fracvars := join(if FI.Independents === null then {} else gens FI.Independents, indeps);
        B := FI.Base;
        if B === QQ then B = ZZ;
        R1 := B(monoid [fracvars]);
	ans := frac R1;
        setFieldInfo'(ans, Base => FI.Base, Independents => ans);
        ans
        )
    else
        FI.Base;
    -- create the finite part
    newK := if FI.Finites === null and fibervars === {} then R2
        else (
            -- now: we have some finite extension part.
            newfibervars := join(fibervars, if FI.Finites =!= null then gens ambient FI.Finites else {});
            R3 := R2(monoid [newfibervars, MonomialOrder => Lex]);
            -- now we need to put the elements of the ideal together into R2.
            ideal1 := if FI.Finites =!= null then sub(ideal FI.Finites, R3) else trim ideal(0_R3);
            ideal2 := if fibervars =!= {} then sub(I, R3) else trim ideal(0_R3);
            J := ideal1 + ideal2;
            gbJ := ideal groebnerBasis J;
            -- ok, get rid of linear polynomials here I think, remove them from 
            R4 := R3/gbJ;
            ans= toField R4;
            -- TODO: Can we figure out how to do something like what is below?
            -- ans = new Field from tfR4;
            setFieldInfo'(ans,
                Base => FI.Base,
                Independents => if R2 === FI.Base then null else R2,
                Finites => R4);
            denominator ans := (f) -> (
                -- this code uses the fact that R4 is of the form R3[].
                -- so in particular to get the coefficient ring of R3, we need to do the following:
                R := ring f;
                K := coefficientRing coefficientRing R;
                if instance(K, FractionField) then (
                    denoms := (terms leadCoefficient f)/leadCoefficient/denominator;
                    lcm denoms
                    )
                else 1_K
                );
            ans
	 );
    -- now create the map R --> newK, place it into newK? or just return the ring map?
    map(newK, R)
    )

-- set up the cache, FieldInclusion and LiftBack for the global rings ZZ and QQ
if not ZZ.?cache then ZZ.cache = new CacheTable;
if not QQ.?cache then QQ.cache = new CacheTable;
if not QQ.cache.?FieldInclusion then QQ.cache.FieldInclusion = map(QQ,ZZ);
if not QQ.cache.?LiftBack then QQ.cache.LiftBack = map(ZZ,QQ);
if not ZZ.cache.?FieldInclusion then ZZ.cache.FieldInclusion = map(QQ,ZZ);
if not ZZ.cache.?LiftBack then ZZ.cache.LiftBack = map(ZZ,QQ);  -- note:  usable only on numerators
fieldInfo QQ -- populates QQ.cache.FieldInfo

field = method(Options => {Independents => null})
field Ring := Field => opts -> origR -> (
    -- Input: a domain origR (this is not checked!)
    -- Output: origR in `normal form', i.e. (frac(baseField[ts])[zs] / Iz)[]
    if not origR.?cache then origR.cache = new CacheTable;
    if origR.cache.?FieldInfo then return origR;
    if origR.cache.?FieldInclusion then return target origR.cache.FieldInclusion;
    if isFiniteField origR then (
        fieldInfo origR;  -- populate origR.cache.FieldInfo if necessary
        if not origR.cache.?FieldInclusion then origR.cache.FieldInclusion = id_origR;
        if not origR.cache.?LiftBack then origR.cache.LiftBack = id_origR;
        return origR;
    );
    (R, phi) := flattenRing origR;
    I := ideal R;
    K := coefficientRing R; -- this should be a field in normal form or ZZ
    if K === ZZ then (
	-- compute J = I \cap ZZ
	-- check that J is a prime integer p or 0
	-- if J is a prime integer: form newR = ZZ/p (monoid R) / (I substituted into this ring)
	--                          call field newR and return
        -- if J is zero: form newR = QQ (monoid R) / (I substituted into this ring)
	--                          call field newR and return
	Igb := ideal gens gb I;
	elimI := select(Igb_*, f -> support f === {});
	kk := if #elimI != 1 then QQ else
	      (
	         p := leadCoefficient elimI_0;
		 if not isPrime p or p > 2^64 then error "Expected a field over a prime < 2^64";
		 ZZ/p
	      );
	numer := kk (monoid R);
	J := ideal compress gens sub(I, vars numer);
	newR := numer / J;
	fieldNewR := field newR;  -- has the inclusion map from newR to fieldNewR
	                          -- so we have to update this with a map from R to newR
        alpha := map(newR, R, vars newR);
	fieldNewR.cache.FieldInclusion = fieldNewR.cache.FieldInclusion * alpha * phi;
	origR.cache.FieldInclusion = fieldNewR.cache.FieldInclusion;
        
        fieldNewR.cache.LiftBack = map(origR,fieldNewR);   -- TODO: be careful here
        return fieldNewR;
    );
    FI := fieldInfo K;
    -- what are the options for R?
    --  1. R is already a field in normal form (i.e. basic field, frac field or finite extension of such)
    psi := if I == 0 then (
        -- possibly a bunch of new transcendental elements
        combineFields(K, R, gens R, {}) * phi     
        )
    else (
        indeps := if opts.Independents =!= null then
                      for x in opts.Independents list sub(x, ring I)
                  else 
                      independentSets(I, Limit => 1);
        indepvars := if #indeps === 0 then {} else support first indeps;
        fibervars := rsort toList(set gens ring I - set indepvars); -- should we keep degrees?  I think not...
        combineFields(K, R, indepvars, fibervars) * phi
        );
    -- psi : origR --> flattened origR --> field we understand
    result := target psi;
    result.cache.FieldInclusion = psi;
    result.cache.LiftBack = map(source psi, target psi);  -- TODO: be more careful here
    origR.cache.FieldInclusion = psi;
    result
    )

isIrreducible = method()
isIrreducible RingElement := Boolean => f -> (
    if #(support f) > 1 then error "Not yet implemented for multivariate polynomials.";
    facsf := factors f;
    (#facsf == 1 and facsf#0#0 == 1)
)

adjoinRoot = method(Options => {Variable=>null,AssumeIrreducible=>false})
adjoinRoot RingElement := RingElement => opts -> (f) -> (
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
        if not opts#AssumeIrreducible and not isIrreducible f then
            error "expected an irreducible polynomial.";
        kk := coefficientRing R;
        if opts.Variable =!= null and not (instance(opts.Variable, Symbol) or instance(opts.Variable, IndexedVariable)) then
            error "Variable given is not a symbol or indexed variable.";
        v := opts.Variable ?? baseName x;
        A := kk(monoid [v]);
        fA := sub(f, vars A);
        Rnew := field (A/fA);
        promote((baseRing Rnew)_0, Rnew)
        )
    )

splittingField = method(Options => {Variable=>(getSymbol "xx")})
splittingField RingElement := Ring => opts -> f -> (
    R := ring f;
    supp := support f;
    if #supp != 1 or numgens R =!= 1 then error "expected a univariate polynomial";
    x := supp#0;
    if degree(x,f) == 1 then return coefficientRing R;
    facs := factors f;
    -- can we stop factoring as soon as we find a nonlinear irreducible factor?
    irreds := select(facs, p -> first degree p#1 > 1);
    if irreds == {} then return coefficientRing R;
    g := last first irreds;
    v := opts#Variable;
    firstVar := if class v === Symbol then v_1 else v;
    newRoot := adjoinRoot(g, Variable => firstVar, AssumeIrreducible=>true);
    newKK := ring newRoot;
    newR := newKK (monoid R);
    phi := map(newR, R);
    indexVarAsList := toList firstVar;
    nextVar := (indexVarAsList#0)_(indexVarAsList#1 + 1);
    splittingField(phi f, Variable => nextVar)
)

fieldInclusion = method()
fieldInclusion Ring := RingMap => R -> if R.cache.?FieldInclusion then R.cache.FieldInclusion

inducedMapOnFields = method()
inducedMapOnFields RingMap := RingMap =>  F -> (
    R := source F;
    S := target F;
    KR := field R;
    KS := field S;
    phi := fieldInclusion R;
    g := fieldGens KR;
    vals := for x in g list (
        num := phi numerator x;
        den := phi denominator x;
        if den == 0 then error "cannot form induced map";
        phi num / phi den
        );
    map(KS, KR, vals)
    )
fieldGens = method()
fieldGens FractionField := List => R -> (
    base := ultimate(coefficientRing, R);
    generators(R, CoefficientRing => base)
    )
fieldGens QuotientRing := 
fieldGens PolynomialRing := List => R -> (
    if isBasicField R then return {};
    if isFieldInNormalForm R then (
        base := ultimate(coefficientRing, R);
        return generators(R, CoefficientRing => base)
        );
    fieldGens coefficientRing R
    )
fieldGens GaloisField := R -> gens R
fieldGens Ring := R -> if R === QQ then {} else error "not implemented yet"

-- The following is not correct yet.
-- I want it to work for elements in a field K in normal form, as
-- well as for polynomials in K[x1, x2, ...]
denom = method()
denom RingElement := (f) -> (
    -- if f is a polynomial over a fraction field, gives the lcm of the denominators
    R := ring f;
    K := coefficientRing R;
    if instance(K, FractionField) then (
        denoms := (terms f)/leadCoefficient/denominator;
        lcm denoms
        )
    else 1_K
    )

mydenominator = method()
    -- we have basically 8 cases, some can be handled the same, I hope...
    --  K = QQ
    --  K = QQ[z1, ...]/Iz -- we need to stash the ring ZZ[z1, ...] too...
    --  K = frac(ZZ[t1,...])
    --  K = frac(ZZ[t1,...])[z1, ...]/Iz
    --  K = Fq
    --  K = Fq[z1, ...]/Iz
    --  K = frac(Fq[t1,...])
    --  K = frac(Fq[t1,...])[z1, ...]/Iz
mydenominator RingElement := (f) -> (
    R := ring f;
    K := getCoefficientField R; -- if R is a field already (in normal form), then K === R
    tmsf := if K === R then {f}
            else (terms f)/leadCoefficient;
    (fieldInfo K).denominator tmsf
    )
mydenominator QQ := f -> denominator f

fieldContent = method()
fieldContent RingElement := (f) -> (
    R := ring f;
    K := getCoefficientField R; -- if R is a field already (in normal form), then K === R
    tmsf := if K === R then {f}
            else (terms f)/leadCoefficient;
    (fieldInfo K).content tmsf
    )



-- denominator:
--  finite field: 1
--  QQ: actual denominator in ZZ
--  frac field of QQ[...], denominator will be over ZZ.
--  finite extension of QQ(...): denominator will be over ZZ[...].
--  finite extension of L: denominator will be the denominator of L.
-- denominatorRing: what ring the denominators will lie in.
-- polynomial ring over a field L: the lcm of the denominators, in denominatorRing L

makeMonic = method()
makeMonic RingElement := F -> (
    -- TODO: avoide use of GB's here?
    -- make sure ring F is a ring where all this works...
    --<< "inverting " << leadCoefficient F << endl;
    if F == 0 then return F;
    lc := leadCoefficient F;
    I := ideal(lc);
    if 1 != I then return null;
    lcinv := (1 // matrix gens I)_(0,0);
    lcinv * F
    )

-- sign: over ZZ (or QQ) sign is +1 if the lead coefficient (over QQ) is positive, -1 otherwise.
--       over Fq, "sign" is lead coefficient (i.e. divide by the lead Fq-coefficient)
-- also need (over ZZ, QQ) the integer content (should match the lead coefficient)
-- over Fq: integer content is the lead coefficient.
-- TODO: handle uniqueness: +- 1, and maybe monic mod p?
primitiveAssociate = method()
primitiveAssociate RingElement := RingElement =>  F -> (
    if F == 0 then F else 1/(fieldContent F) * F
    )

monicAssociate = method()
monicAssociate RingElement := RingElement =>  F -> (
    G := makeMonic F;
    primitiveAssociate G
    )

-- Currently, this is the naive algorithm
-- It isn't so bad over finite extensions of finite fields...
--monicGCD = method(Options => {Strategy => "Naive"})
monicGCD = method(Options => {Strategy => "Modular"})
monicGCDNaive = method()
monicGCDModular = method()
monicGCD(RingElement, RingElement) := RingElement => opts -> (f, g) -> (
    R := ring f;
    if R =!= ring g then error "expected polynomials in the same ring";
    if not instance(R, PolynomialRing) and numgens R =!= 1 then error "expected elements in a polynomial ring";
    if f == 0 then return g else if g == 0 then return f;
    if f == 1 then return f else if g == 1 then return g;
    (f',g') := if first degree f <= first degree g then (g,f) else (f,g);
    if f' % g' == 0 then return g';
    if opts.Strategy === null or opts.Strategy === "Modular" then
        monicGCDModular(f, g)
    else if opts.Strategy === "Naive" then
        monicGCDNaive(f, g)
    else
        error "expected Strategy option to be \"Naive\" or \"Modular\""
    )

monicGCDNaive(RingElement, RingElement) := (f, g) -> (
    -- f and g should be polynomials over a field in (currently) one variable
    R := ring f;
    K := coefficientRing R;
    if not isField K then error "expected a polynomial ring over a field";
    x := R_0;
    (r, s) := if degree_x f < degree_x g then (g, f) else (f, g);
    r = makeMonic r;
    s = makeMonic s;
    if r === null or s === null then return null;
    --print r;
    --print s;
    while s != 0 do (
        newr := makeMonic(r % s);
        if newr === null then return null;
        --print newr;
        (r,s) = (s,newr);
        );
    r)

monicGCD List := RingElement => opts -> fs -> (
    if #fs == 0 then error "expected a nonempty list";
    if #fs == 1 then return fs#0;
    sortFs := sort(fs,degree);
    R := ring first sortFs;
    curGCD := 0_R;
    for f in sortFs do (
        curGCD = monicGCD(curGCD,f,opts);
        if curGCD === null then return null;
        if curGCD == 1 then return curGCD;
    );
    curGCD
)

-----------------------
-- Modular monic GCD --
-----------------------

 
-- algorithm for gcd Monagan-vHoeij 2004.
-- All polynomials are in ZZ[x, z, t1, t2, ..., tk, MonomialOrder => Lex]
-- We want to implement a combination of this algorithm with their 2002 paper
-- which details what happens when the base field is a tower of extensions.
--
-- input: f,g: two polynomials in ZZ[x, z1, z2, ..., zr, t1, ..., tk]
--        a list of polynomials: GB of the field ideal in z1, ..., zr.
-- output: the primitive associate of the monic GCD of (f, g) over QQ[z1, ..., t1, ...]/(field ideal).
--
-- algorithm:
--
--
-- PGCD:
--   2 versions.  Version 1 works directly over a field ZZ/p, returning a polynomial over this ring (or null)
--                Version 2 does the same, but input and output are over ZZ, and "mod p" is understood.
--                  (all coefficients appearing have been reduced, and are all positive, or balanced (not sure which yet...)
-- input:
--        a prime number p
--        f,g: two polynomials in ZZ[x, z1, z2, ..., zr, t1, ..., tk]
--        a list of polynomials: GB of the field ideal in z1, ..., zr.
-- output: the primitive associate of the monic GCD of (f, g) over ZZ/p[z1, ..., t1, ...]/(field ideal).
--        but as an element of ZZ[z1, ..., t1, ...]
--
-- algorithm:

monicGCDModP = method()
-*
monicGCDModP(RingElement, RingElement) := (F0, G0) -> (
    -- F0, G0 are in R = L[x], where L = Fq(t1..ts)[z1..zr]/Iz is finite over Fq(t1..ts)
    -- currently: x = a SINGLE variable...
    -- returns the primitive associate of the monic GCD of F0, G0,
    -- After setting up the desired rings and ring maps, this calls
    -- the main workhorse: monicGCDModPWorker.
    R := ring F0;
    if ring G0 =!= R then error "expected elements in the same ring";
    L := coefficientRing R; -- should be a field(...)
    x := gens R; -- list of x variables
    if #x =!= 1 then error "currently, requires only gcd's over one variable are implemented";
    kk := baseField L;  -- TODO: Check that kk is finite
    z := gens baseRing L; -- z vars
    t := gens coefficientRing baseRing L;
    Ap := kk(monoid [x, z, t, MonomialOrder => {#x, #z, #t}]); -- be careful not to set ring vars.
    xvars := (gens Ap)_{0..#x-1};
    zvars := (gens Ap)_{#x..#x+#z-1};
    tvars := (gens Ap)_{#x + #z .. numgens Ap - 1};
    Iz0 := ideal baseRing L;
    toAp := map(Ap, R, gens Ap);
    fromAp := map(R, Ap, flatten{x,z,t});
    fromRingIz0 := map(Ap, ring Iz0, drop(gens Ap, #x));
    base := kk(monoid[z]);
    toBase := map(base, Ap, flatten splice{#x : 0_base, gens base, #t : 0_base});

    topAnswer := monicGCDModPWorker(toAp F0,
	                            toAp G0,
				    fromRingIz0 Iz0,
				    xvars,
				    zvars,
				    tvars,
				    toBase,
                                    fromAp,
				    #t);
    if topAnswer === null then return null;
    fromAp topAnswer
    )
*-

-- todo: this version is currently (almost) exactly the same as the above.
-- use numeratorMap to clean up this code.
monicGCDModP(RingElement, RingElement) := (F0, G0) -> (
    -- F0, G0 are in R = F[x], where F = kk(t1..ts)[z1..zr]/Iz is finite over kk(t1..ts)
    -- and kk should be a finite field
    -- currently: x = a SINGLE variable...
    -- returns the primitive associate of the monic GCD of F0, G0,
    -- After setting up the desired rings and ring maps, this calls
    -- the main workhorse: monicGCDModPWorker.
    Rp := ring F0;
    if ring G0 =!= Rp then error "expected elements in the same ring";
    if numgens Rp =!= 1 then error "currently, only gcd's over one variable are implemented";
    kk := baseField Rp; -- TODO: Make sure kk is finite

    (fromAp,toAp,xztvars,Iz') := numeratorMap Rp; 
    (xvars,zvars,tvars) := xztvars;
    Ap := source fromAp;
    
    base := kk(monoid[zvars]);
    toBase := map(base, Ap, flatten splice{#xvars : 0_base, gens base, #tvars : 0_base});
    
    topAnswer := monicGCDModPWorker(toAp F0,
	                            toAp G0,
				    Iz',
				    xvars,
				    zvars,
				    tvars,
				    toBase,
				    #tvars);
    if topAnswer === null then return null;
    primitiveAssociate fromAp topAnswer
    )

monicGCDModPWorker = (f,g,Iz,xs,zs,ts,toBase,k) -> (
    -- f,g polynomials in Ap
    -- Iz is ideal of z variables in Ap
    -- xs,zs,ts are packets of variables in Ap corresponding to field information
    -- base is kk(monoid(zs))
    -- toBase: ???? Ap --> base,
    -- fromAp: Ap --> Rp, this is where exact division will be checked.
    -- this function performs computations in Ap, as well as C[x]
    -- where C is field(quotient kk[zs])
    Ap := ring f;
    kk := coefficientRing Ap;
    if k === 0 then (
	C := field(quotient toBase Iz);
	D := C(monoid[xs]); -- don't set x!!
	toD := map(D, Ap, flatten{D_0, gens baseRing C, #ts:0_D}); -- TODO (maybe factor out actual map above)
	fromD := map(Ap, D, flatten{Ap_0, zs} ); -- TODO (maybe factor out actual map above)
	F' := toD f; -- toD: Ap --> D 
	G' := toD g;
	ans0 := monicGCDNaive(F', G');
	if ans0 === null then return null;
	return fromD ans0
	);
    -- create the ring where we will do the exact divisions (this is the NAIVE algorithm).
    -- TODO: do it without new rings, using pseudo-division.
    A1 := (field(kk(monoid [ts_{0..k-1}])))(monoid [zs]);
    A2 := field(A1/sub(Iz, A1));
    A3 := A2(monoid [xs]);
    f' := sub(f, A3);
    g' := sub(g, A3);

    tvar := ts#(k-1);
    n := 1;
    d := 1;
    currentCRA := null;
    while true do ( -- main loop
	-- choose random eval point, compute gcd at that point using P.
	a := random kk;
	f0 := sub(f, {tvar => a});
	g0 := sub(g, {tvar => a});
	Iz0 := sub(Iz, {tvar => a});
	h := monicGCDModPWorker(f0, g0, Iz0, xs, zs, ts, toBase, k-1);
	if h === null then (
	    d = d+1;
	    if d > n then return null;
	    continue -- main loop
	    );
	if h == 1 then return h;
	hCRA := (h, tvar - a);
	currentCRA = if currentCRA === null then hCRA
	             else chineseRemainder(currentCRA, hCRA, tvar);
	n = n+1;
	reconstr := rationalFunctionReconstruction(currentCRA, tvar);
	if reconstr === null then continue; -- main loop
	ans := reconstr_0;
        ans' := sub(ans, A3);
        if f' % ans' == 0 and g' % ans' == 0 then (
            -- a check that these really do divide:
            --q1 := f' // ans'
            --q2 := g' // ans'
            --assert(q1 * ans' == f')
            --assert(q2 * ans' == g')
            return ans;
            );
        << "note: exact division test failed at k=" << k <<  endl;
    );
)

monicGCDQQ = method()
monicGCDQQ(RingElement, RingElement) := RingElement => (F0, G0) -> (
    R := ring F0;
    if ring G0 =!= R then error "expected elements in the same ring";
    F0 = primitiveAssociate F0;
    G0 = primitiveAssociate G0;

    (fromAZZ, toAZZ, xztvars, Iz) := numeratorMap R;
    (xvars, zvars, tvars) := xztvars;
    AZZ := source fromAZZ;

    FZZ := toAZZ F0;
    GZZ := toAZZ G0;

    p := nextPrime (2^28 + 1);
    currentCRA := null;
    numBadPrimes := 0;
    while true do (  -- main loop
       p = nextPrime(p+1);
       phi := reductionMap(R, p);
       Rp := target phi;

       kkp := ZZ/p;
       Ap := kkp(monoid AZZ);
       toAp := map(Ap, AZZ, gens Ap);
       fromAp := map(AZZ, Ap, gens AZZ); -- lifting map, not a ring map...!
       fp := toAp FZZ;
       gp := toAp GZZ;
       Izp := toAp Iz;

       base := kkp(monoid[zvars]);
       toBase := map(base, Ap, flatten splice{#xvars : 0_base, gens base, #tvars : 0_base});

       hp := monicGCDModPWorker(fp,
	                        gp,
				Izp,
				xvars / toAp,
				zvars / toAp,
				tvars / toAp,
				toBase,
                                #tvars);

       if hp === null then (
          numBadPrimes = numBadPrimes + 1;
	  continue;
       );
			    
       hCRA := (fromAp hp, p);
       currentCRA = if currentCRA === null then hCRA
                    else chineseRemainder(currentCRA, hCRA);
       hQQ := rationalReconstruction currentCRA;
       hR := sub(hQQ, matrix {generators(R,CoefficientRing => ZZ)});
       if F0 % hR == 0 and G0 % hR == 0 then (   -- checked in R
           if numBadPrimes > 0 then (
	       << "Bad primes found in computation: " << numBadPrimes << endl;
	   );
           return primitiveAssociate hR;
       );
       print "Failed division check in monicGCDQQ.";
    );
)

monicGCDModular(RingElement, RingElement) := (f, g) -> (
    -- TODO: use `char` instead....
    R := ring f;
    if ring g =!= R then error "expected polynomials in the same ring";
    if f == 0 then return g else if g == 0 then return f;
    FI := fieldInfo coefficientRing R;
    retval := if FI.Base === QQ then 
        monicGCDQQ(f, g)
    else
        monicGCDModP(f, g);
    if retval === null then error "coefficient ring is likely not a field.";
    retval
    )

-----------------------
-- Factoring over F ---
-----------------------
inducedPolynomialMap = method()
inducedPolynomialMap (RingMap, Ring, Ring) := (psi, tar, src) -> (
   -- psi: map between coefficient rings of src and tar
   if numgens tar != numgens src then error "Expected number of generators to match";
   if coefficientRing tar =!= target psi or coefficientRing src =!= source psi then error "Expected map between coefficient rings.";
   map(tar,src, vars tar | psi.matrix)
)

-*
primitiveElementMaps = method(Options => {
        Variable => null,
        CoefficientRing => null,
        PrimitiveElement => null})
primitiveElementMaps Ring := opts -> F -> (
    F.cache.PrimitiveMaps ??= (
        -- assumes that F is toField of a flattened finite extension of QQ or ZZ/p
        newF := coefficientRing F; -- strips off the zero variables poly ring prt.
        phi := map(newF, F);
        phiinv := map(F, newF);
        k := coefficientRing newF; -- either a basic field, or a pure fraction field
        tryPrim := opts.PrimitiveElement ?? sum gens newF;
        X := if opts.Variable === null then getSymbol("X") else opts.Variable;
        G := k(monoid[X]);
        psi := map(newF,G,{leadCoefficient tryPrim});
        degExtn := numcols basis newF;
        minPoly := first flatten entries gens ker psi;
        if first degree minPoly != degExtn then error "Selected primitive element, or sum of variables, not primitive.";
        -- TODO: Adapt our primitive element if the sum is not primitive
        --       allow for user-provided primitive element, or random
        quotG := G/ideal(minPoly);
        psiQuotG := map(newF, quotG, {leadCoefficient tryPrim});
        tfQuotG := toField quotG; -- TODO: toField => field, but need to fix code...
        tfPsi := map(F, tfQuotG, {tryPrim});
        tfPsiInv := map(tfQuotG, F, (psiQuotG^(-1)).matrix);
        assert(tfPsi * tfPsiInv == 1);
        (tfPsi, tfPsiInv)
        )
)

primitiveElementRing = method(Options => options primitiveElementMaps)
primitiveElementRing Ring := Ring => opts -> F -> (
    (f, finv) := primitiveElementMaps(F, opts);
    source f
    )
*-

minimalPolynomial = method()
minimalPolynomial (Matrix,PolynomialRing) := RingElement => (M,R) -> (
    -- M input matrix, R ring in one variable where minl poly will live
    var := R_0;
    A := ring M;
    if coefficientRing R =!= A then error "Expected polynomial ring over ring of matrix.";
    if numgens R != 1 then error "Expected polynomial ring in one variable.";
    if numcols M != numrows M then error "Expected a square matrix.";
	
    curPow := 0;
    curM := id_(A^(numcols M));
    MPowList := new MutableList from {};
    MPowList#0 = transpose matrix {flatten entries curM};
    N := null;
    while (curPow <= numcols M) do (
        N = matrix {toList MPowList};
	if (rank N != numcols N) then break;
	curPow = curPow + 1;
	curM = curM * M;
	MPowList#curPow = transpose matrix {flatten entries curM};
    );
    syzN := syz N;
    if numcols syzN != 1 then error "Unexpected syzygy.";
    kerVec := flatten entries syzN;
    makeMonic sum for i from 0 to numcols N - 1 list kerVec#i * var^i 
)

minimalPolynomial (RingElement,PolynomialRing) := RingElement => (f,R) -> (
    -- M input matrix, R ring in one variable where minl poly will live
    var := R_0;
    F := ring f;
    FI := fieldInfo F;
    kk := coefficientRing FI.Finites;
    d := numcols extensionBasis F; -- degree of F
    if coefficientRing R =!= kk then error "Expected polynomial ring over ring of matrix.";
    if numgens R != 1 then error "Expected polynomial ring in one variable.";
	
    curPow := 0;
    curg := 1_F; 
    fPowList := new MutableList from {};
    fPowList#0 = coeffsInBasis curg;
    N := null;
    while (curPow <= d) do (
        N = matrix {toList fPowList};
	if (rank N != numcols N) then break;
	curPow = curPow + 1;
	curg = curg * f;
	fPowList#curPow = coeffsInBasis curg;
    );
    syzN := syz N;
    if numcols syzN != 1 then error "Unexpected syzygy.";
    kerVec := flatten entries syzN;
    makeMonic sum for i from 0 to numcols N - 1 list kerVec#i * var^i 
)

extensionBasis = method()
extensionBasis Ring := Matrix => F -> (
    FI := fieldInfo F;
    FI.cache.extensionBasis ??= (
        if FI.Finites === null then
            map(F^1, F^1, {{1}})
        else
            basis FI.Finites
        )
)

--extensionBasis RingMap := Matrix => phi -> (
--    
--    )

extensionDegree = method()
extensionDegree Ring := ZZ => F -> numcols extensionBasis F

coeffsInBasis = method()
coeffsInBasis Matrix := Matrix => fs -> (
    fs0 := lift(fs,coefficientRing ring fs);
    B := extensionBasis ring fs;
    M := last coefficients(fs0, Monomials => B);
    lift(M, coefficientRing ring B)
)

coeffsInBasis RingElement := Matrix => f -> coeffsInBasis matrix {{f}}

randomElement = method()
randomElement Ring := RingElement => A -> (
    B := extensionBasis A;
    bas := baseField A;
    rand := random(bas^(numcols B),bas^1);
    promote(first flatten entries (B*rand),A)
)    

multiplicationMap = method()
multiplicationMap RingElement := Matrix => f -> (
    B := extensionBasis ring f;
    coeffsInBasis(f * B)
)

-- TODO: Option allowing for first `try'
computePrimitiveInfo = method()
computePrimitiveInfo Ring := List => F -> (
   -- F is a field in normal form
   -- P is a polynomial ring in one variable over FI.Independents
   -- (where FI = fieldInfo F)

   FI := fieldInfo F;
   gensList := gens FI.Finites;
   if FI.Finites === null then error "expected a finite extension of rational base field.";
   -- if the field is already presented as a primitive extension, then
   -- use that presentation.
   if #gensList == 1 then return new PrimitiveInfo from {
        (symbol PrimitiveElement) => gensList_0,
	(symbol MinimalPolynomial) => makeMonic (ideal FI.Finites)_0,
	(symbol FromPrimitive) => id_F,
	(symbol ToPrimitive) => id_F
   };
          
   count := 0;
   d := 0;
   D := extensionDegree F;
   curPrim := null;
   primPoly := null;
   kk := coefficientRing FI.Finites;
   T := getSymbol "T";
   P := kk (monoid [T]);
   
   while (d < D) do (
      if (count == 20) then error "cannot find primitive extension";

      if count == 0 then
         curPrim = sum gensList
      else if (count < 10) then
         curPrim += gensList#(random(#gensList))
      else
         curPrim = leadCoefficient randomElement F;  -- to place in FI.Finites
      
      primPoly = minimalPolynomial(promote(curPrim,F),P);
      d = first degree primPoly;
      count = count + 1;
   );

   -- TODO: Make field() below, but issues getting back & forth for now
   newF := P/primPoly;
   fieldNewF := field newF;
   fieldInc := fieldNewF.cache.FieldInclusion;
   fieldLift := fieldNewF.cache.LiftBack;
   phi := map(FI.Finites,newF,{curPrim});
   psi := map(newF,FI.Finites,(phi^(-1)).matrix);
   fromFinites := map(F,FI.Finites);
   toFinites := map(FI.Finites,F,gens FI.Finites);
   -- TODO: Figure out what is wrong with degreeMaps from the below composites
   primInfo := new PrimitiveInfo from {
        (symbol PrimitiveElement) => curPrim,
	(symbol MinimalPolynomial) => primPoly,
	(symbol FromPrimitive) => fromFinites*phi*fieldLift,
	(symbol ToPrimitive) => fieldInc*psi*toFinites
   };
   primInfo
)



-- tryPrimitiveElement = method()
-- tryPrimitiveElement(Ring, RingElement, Ring) := (F, primElem, G) -> (
--     --(newF,phi) := flattenRing(F,CoefficientRing => opts.CoefficientRing);
--     --k := coefficientRing newF;
--     --degExtn := numcols basis newF;
--     psi := map(F,G,{primElem});
--     minPoly := first flatten entries gens ker psi;
--     minPoly
--     --if first degree minPoly == degExtn then primElem else null
--     )

--     --     -- TODO: Adapt our primitive element if the sum is not primitive
--     --     --       allow for user-provided primitive element, or random
--     --     quotG := G/ideal(minPoly);
--     --     psiQuotG := map(newF,quotG,{primElem});
--     --     tfQuotG := toField quotG;
--     --     tfPsi := map(F,tfQuotG,{phi^(-1) primElem});
--     --     tfPsiInv := map(tfQuotG,F,(psiQuotG^(-1)).matrix);
--     --     assert(tfPsi * tfPsiInv == 1);
--     --     (tfPsi,tfPsiInv)
--     -- )

-- primitiveElementField = method(Options => {Variable => null, PrimitiveElement => null})
-- primitiveElementField Ring := opts -> F -> (
--     -- this is only valid for a finite extension.
--     if not isFieldInNormalForm F then error "Base field not in normal form.";
--     FK := coefficientRing F;
--     K := coefficientRing FK; -- first dtrips zero var extension, the second gives the base
--     if opts.PrimitiveElement =!= null or not F.cache?.PrimitiveMaps then (
--         primelem := if opts.PrimitiveElement === null then sum gens F else opts.PrimitiveElement;
--         F.cache.PrimitiveMaps = (
--             X := if opts.Variable === null then getSymbol("X") else opts.Variable;
--             G := K(monoid[X]);
--             psi := map(FK,G,{primElem}); -- try different ones each loop execution!
--             degExtn := numcols basis FK;
--             minPoly := first flatten entries gens ker psi;
--             if first degree minPoly == degExtn then error "need a primitive generator!";
--             quotG := G/ideal(minPoly);
--             psiQuotG := map(FK, quotG, {primElem});
--             tfQuotG := field quotG;
--             tfPsi := map(F, tfQuotG, {phi^(-1) primElem});
--             tfPsiInv := map(tfQuotG,F,(psiQuotG^(-1)).matrix);
--             assert(tfPsi * tfPsiInv == 1);
--             (tfPsi,tfPsiInv)
--             );
--         );
--     F.cache.PrimitiveMaps
--     )
    
--     F.cache.PrimitiveMaps ??= (
-- 	-- assumes that F is toField of a flattened finite extension of QQ or ZZ/p
-- 	(newF,phi) := flattenRing(F,CoefficientRing => opts.CoefficientRing);
-- 	k := coefficientRing newF;
-- 	X := if opts.Variable === null then getSymbol("X") else opts.Variable;
-- 	G := k(monoid[X]);
--         count := 0;
--         minPoly := null;
--         primElem := null;
--         while count < opts.Limit do (
--             primElem = sum gens newF;
--             psi := map(newF,G,{primElem}); -- try different ones each loop execution!
--             degExtn := numcols basis newF;
--             minPoly = first flatten entries gens ker psi;
--             if first degree minPoly == degExtn then break;
--             count = count + 1;
--             );
--         if count == opts.Limit then error "Sum of variables not primitive.";
-- 	-- TODO: Adapt our primitive element if the sum is not primitive
-- 	--       allow for user-provided primitive element, or random
-- 	quotG := G/ideal(minPoly);
-- 	psiQuotG := map(newF,quotG,{primElem});
-- 	tfQuotG := toField quotG;
-- 	tfPsi := map(F,tfQuotG,{phi^(-1) primElem});
-- 	tfPsiInv := map(tfQuotG,F,(psiQuotG^(-1)).matrix);
-- 	assert(tfPsi * tfPsiInv == 1);
-- 	(tfPsi,tfPsiInv)
--     )
-- )

positiveDegreeFactors = method()
positiveDegreeFactors RingElement := f -> (
    R := ring f;
    facs := (factor f) // toList / toList;
    select(facs, p -> degree(R_0,p_0) > 0)
)

squareFreeFactors = method()
squareFreeFactors RingElement := f -> (
   -- f is in R = F[x], F is a field in normal form
   -- Assume that f is squarefree for this method, will be called
   -- by myFactor after computing a squarefree decomposition
   R := ring f;
   F := coefficientRing R;
   if not isFieldInNormalForm F then error "Base field not in normal form.";
   T := local T;
   --FI := fieldInfo F;
   --kk := if (FI.?Independents and FI.Independents =!= null) then FI.Independents else baseField F;
   kk := rationalBaseField F;
   
   primInfo := computePrimitiveInfo F;
   phi := primInfo.FromPrimitive;
   psi := primInfo.ToPrimitive;
     
   primF := target psi;

   RprimF := primF (monoid R);
   psi' := inducedPolynomialMap(psi, RprimF, R);
   phi' := inducedPolynomialMap(phi, R, RprimF);

   baseR := if baseField R === QQ then ZZ else baseField R;
   RprimFoverZ := baseR (monoid [gens R, (ambient primF)_0, gens kk, MonomialOrder => Lex]);
   mapToR := map(R,RprimFoverZ,matrix phi');
   fz := primitiveAssociate psi' f; -- in RprimF
   --fz := sub(psi' f, RprimFoverZ);
   mpPrimF := sub(primitiveAssociate (ideal coefficientRing primF)_0, RprimFoverZ); -- minpoly of primF
   a := 0;
   isSqFreeResultant := false;
   mpPBShift := null;
   facs := null;
   gensRprimF := gens(RprimF, CoefficientRing => baseR); -- not quite correct, e.g. for GF 8? x, T, t.
   --error "debug me A";
   while not isSqFreeResultant do (
      a = a + 1;
      fz' := primitiveAssociate sub(fz, gensRprimF_0 => gensRprimF_0 - a * gensRprimF_1);
      fz'' := sub(fz', RprimFoverZ);
      --error "debug me B";      
      mpPBShift = resultant(fz'', mpPrimF, RprimFoverZ_1);

      facs = positiveDegreeFactors mpPBShift;
      --error "debug me C";
      isSqFreeResultant = all(facs / last, i -> i == 1);
   );
   facs = facs / first;
   shiftBackFacs := for h0 in facs list mapToR sub(h0, RprimFoverZ_0 => RprimFoverZ_0+a*RprimFoverZ_1);
   retval := apply(shiftBackFacs, h0 -> monicGCDModular(h0, f));
   --error "debug me D";   
   retval
)

-- caveat: this function requires R = F[x], one variable.
--         the char p case (actually, the non-separable case) is not functional yet.
distinctDegreeFactors = method()
distinctDegreeFactors RingElement := (f) -> (
    -- f should be a polynomial in R == F[x], where F is
    -- a field in normal form.  Currently this works only in the separable case
    R := ring f;
    --p := char R;
    x := R_0;
    T := monicGCDModular(f,diff(x,f));
    V := f // T; -- exact division
    k := 0;
    result := while degree_x(V) =!= 0 list (
        k = k+1;
        W := monicGCDModular(T,V);
        Ak := V // W; -- exact division.
        V = W;
        T = T // V; -- myExactDivision(T,V);
        if degree_x(Ak) =!= 0 then 
            (k, primitiveAssociate Ak)
        else continue
        );
    if degree_x T != 0 then (
        -- we have a polynomial in x^p
        error "char p square free decomposition is not yet implemented";
        -- result2 := squarefree lowerP(T);
        -- result2 = apply(result2, a -> (p*a#0, a#1));
        -- result = join(result,result2);
        );
    result
    )

factorData = method()
factorData RingElement := FactorData => f -> (
    if numgens ring f == 1 then
        univarFactorData f
    else
        multivarFactorData f
)

monicFactorData = method()
monicFactorData RingElement := FactorData => f -> (
    facDat := factorData f;
    lcf := leadCoefficient f;
    new FactorData from { (symbol Coefficient) => lcf,
                          (symbol Factors) => apply(facDat.Factors, p -> {p#0,makeMonic p#1}) }
)

univarFactorData = method()
univarFactorData RingElement := FactorData => f -> (
    if hasFiniteExtension coefficientRing ring f then
       factorDataOverFiniteExtension f
    else
       factorDataOverRationalBaseField f       
)    

factorDataOverRationalBaseField = method()
factorDataOverRationalBaseField RingElement := FactorData => f -> (
    R := ring f;
    facs := (factor f) // toList / toList;
    coeff := 1_(coefficientRing R);
    posDegFacs := for p in facs list (
	if support p#0 != {} then
	   {p#1,p#0}
	else (
	   coeff = leadCoefficient p#0;
	   continue
	)
    );
    facData := new FactorData from { (symbol Coefficient) => coeff,
	                             (symbol Factors) => posDegFacs };
    facData
)

factorDataOverFiniteExtension = method()
factorDataOverFiniteExtension RingElement := FactorData => f -> (
    lcf := leadCoefficient f;
    distinctdegs := distinctDegreeFactors f; -- list of form {d, fac}
    facPairs := flatten for z in distinctdegs list (
        facs := squareFreeFactors z_1;
        for fac in facs list {z_0, fac}
        );
    lcOfFacs := product apply(facPairs, p -> (leadCoefficient p#1)^(p#0));
    facData := new FactorData from { (symbol Coefficient) => lcf / lcOfFacs,
	                             (symbol Factors) => facPairs };
    facData
)

multivarFactorData = method()
multivarFactorData RingElement := List => f -> (
    R := ring f;
    L := coefficientRing R;
    lcf := leadCoefficient f;
    firstVar := {first gens R};
    varsNotToInvert := drop(gens R, 1);
    S1 := L (monoid [firstVar]);
    L1 := field S1;
    R1 := L1 (monoid [varsNotToInvert]);
    phi := map(R,S1,firstVar);
    phiBack := map(S1,R,{S1_0} | toList((numgens R - 1):0));
    psi := map(R1,R, {S1.cache.FieldInclusion S1_0} | gens R1);
    psiBack := map(R,R1,varsNotToInvert);  -- this only works on numerators
    coeffFactor := f -> (
        coeffMat := phiBack last coefficients(f, Variables => varsNotToInvert);
        coeffFac := monicGCD(flatten entries coeffMat);   
        coeffFacs := factors coeffFac;
        (coeffFacs, f // (phi coeffFac))
    );
    (svFacs,newf) := singleVariableFactors f;
    f = psi newf;
    facsf := factors f;   -- factors call on one less variable
    fixedFacs := apply(facsf, p -> (
                           (spurious,goodFac) := coeffFactor psiBack primitiveAssociate p#1;
                           {p#0,goodFac}));
    allFacs := svFacs | fixedFacs;
    offBy := product apply(allFacs, p -> (leadCoefficient p#1)^(p#0));
    new FactorData from { (symbol Coefficient) => offBy^(-1)*lcf,
                          (symbol Factors) => allFacs }
)

value FactorData := RingElement => facData -> value prettyFactor facData

factors = method()
factors RingElement := List => f -> (
    facData := factorData f;
    facData.Factors
)

monicFactors = method()
monicFactors RingElement := List => f -> (
    facData := monicFactorData f;
    facData.Factors
)

-- find all the factors in a single variable of a multivariate polynomial
singleVariableFactors = method()
singleVariableFactors RingElement := Sequence => f -> (
    curf := f;
    R := ring f;
    L := coefficientRing R;
    svFacs := flatten for v in gens R list (
        S1 := L (monoid [v]);
        phiBack := map(S1,R);   -- TODO: Be more careful here?
        phi := map(R,S1,{v});   
        otherVars := select(gens R, m -> m != v);
        coeffs := phiBack last coefficients(curf, Variables => otherVars);
        coeffFac := monicGCD flatten entries coeffs;
        curf = curf // (phi coeffFac);
        coeffFacs := factors coeffFac;
        apply(coeffFacs, p -> {p#0, phi p#1})
    );
    (svFacs,curf)
)

-- TODO: add a hook for roots to use rawRoots for InexactFields and select roots
--       from factors for other fields (if available)
rootsFromFactors = method()
rootsFromFactors RingElement := List => f -> (
    facData := monicFactorData f;
    linFacs := select(facData.Factors, p -> degree p#1 == {1});
    apply(linFacs, l -> sub(-(part_0 (l#1)), coefficientRing ring f))
)

prettyFactor = method()
prettyFactor RingElement := Expression => f -> (
    prettyFactor factorData f
)

prettyFactor FactorData := Expression => facData -> (
    facs := facData.Factors;
    if facData.Coefficient != 1 then facs = append(facs, {1,facData.Coefficient});
    Product apply(facs, p -> Power(p#1, p#0))
)

monicGCD0 = method()
monicGCD0(RingElement, RingElement, Ideal, RingElement) := (F, G, IZ, randa) -> (
      -- MAJOR ASSUMPTION: there is one x, one z, one t.
      -- TODO: remove these restrictions!  Might need to change the interface...
      Ap := ring F;
      kk := coefficientRing Ap;
      if ring G =!= Ap then error "expected same ring";
      if ring IZ =!= Ap then error "expected same ring";
      if ring randa =!= kk then error "expected element in base field";
      Bp := kk[Ap_1];
      phi2 := map(Bp, Ap, {0, Bp_0, randa});
      Cp := field(Bp/(phi2 IZ)); -- kk[z]/Iz0, where Iz0 is Iz, but with t |--> randa.
      Dp := Cp[Ap_0];
      phi3 := map(Dp, Ap, {Dp_0, Cp_0, randa});
      F' := phi3 F;
      G' := phi3 G;
      sub(monicGCDNaive(F', G'), Ap)
      )

translatedResultant = method()
translatedResultant(RingElement, Ring, ZZ, RingElement) := (F, R, a, z) -> (
    -- F is in RZ
    -- R is of the form F[x], F is in "normal form"
    -- a is the constant to try with z
    -- z is the next (finite) variable to eliminate, in RZ.
    -- returns: polynomial in RZ: res(F(x-a*z, mz, z)) reduced mod equations.
    --   here mz is the equation in z from the field.
    -- this should have degree degree_x(F) * degree_x(mz)
    RZ := ring F;
    if ring z =!= RZ then error "expected variable in flattened polynomial ring";
    k := index z;
    if k === null then error "expected last argument to be a variable in the ring of the first argument";
    k = k-1; -- one x variable...
    eqns := (ideal (coefficientRing R).cache.FieldInfo.Finites)_*;
    R0 := ring eqns#0; -- better have some.  TODO: give error if none.
    these := select(eqns, m -> support leadTerm m === {R0_k});
    if #these != 1 then error("expected a single generator in variable "|toString(z));
    f1 := sub(F, {RZ_0 => RZ_0 - a*z});
    f1R := sub(f1, R);
    f1 = sub(f1R, RZ); -- TODO BUG: what if now f1R has denominators...? this line fails...
    g := resultant(f1, sub(these#0, RZ), z);
    gR := sub(g, R); -- TODO: use a ringmap here.
    g = sub(gR, RZ);
    g
    )

-- need: function that takes R = F[x], returns a ring RZ (or RZp)
-- and elements in it, one for each finite extension minimal polynomial.
-- if no finites: then QQ[ts] or ZZ[ts] or ZZ/p[ts]?
-- if finites, then what??

-- this code is defunct, but is simpler than squareFreeFactors since
-- resultant code is isolated.  Should use that in squareFreeFactors as well.
-*
myFactors2 = method()
myFactors2(RingElement, Ring) := List => (f, RZ) -> (
    R := ring f;
    F := coefficientRing R;
    -- need RZ
    eqns := ideal F.cache.FieldInfo.Finites;
    --RZ := ring eqns;
    fZ := sub(f, RZ);
    prevFZ := fZ;
    elem := 0_RZ;
    forwardstep := for mz in eqns list (
        deg := sum exponents leadTerm mz; -- TODO: get at this info better.
        z := first support leadTerm mz; -- should be entire support.  TODO: check this.
        expecteddeg := degree(RZ_0, prevFZ) * degree(z, mz);
        actualdeg := -1; -- not set yet
        newRes := null;
        a := 0;
        while actualdeg != expecteddeg do (
            a = a+1;
            newRes = translatedResultant(prevFZ, R, a, z);
            actualdeg = degree(RZ_0, newRes);
            );
        prevFZ = newRes;
        elem := elem + a*z;
        );
    facs := (factor prevFZ)//toList/toList/first; -- TODO: make sure it is squarefree?
    newfacs := facs/(g -> sub(sub(g, {R_0 => R_0 + elem}), R));
    for g in newfacs list monicGCDModular(g, f)
    )

-- this might be good after myFactors2 handles multiplicity...
myFactor2 = method()
myFactor2 RingElement := Expression => f -> (
    facs := myFactors2 f;
    Product apply(facs, p -> Power(facs#1, facs#0))
    )
*-

numeratorMap = method()
numeratorMap Ring := Sequence => R -> numeratorMap(R, null)
    -- F := if isFieldInNormalForm R then R
    --   else (
    --     F' := coefficientRing R;
    --     if not isFieldInNormalForm F' then error "expected a field in normal form";
    --     F'
    --     );
    -- FI := fieldInfo F;
    -- kk := if FI.Base === QQ then ZZ else FI.Base;
    -- z := if FI.Finites === null then {} else gens baseRing FI.Finites; -- base ring is numerator ring
    -- t := if FI.Independents === null then {} else gens baseRing FI.Independents; -- base ring is numerator ring
    -- x := if R === F then {} else gens R;
    -- A := kk(monoid [x, z, t, MonomialOrder => {#x, #z, #t}]); -- be careful not to set ring vars.
    -- xvars := (gens A)_{0..#x-1};
    -- zvars := (gens A)_{#x..#x+#z-1};
    -- tvars := (gens A)_{#x + #z .. numgens A - 1};
    -- Iz := ideal FI.Finites; -- in F.
    -- fieldvars := matrix {flatten{zvars, tvars}};
    -- Iz' := ideal(Iz_*/(f -> sub(primitiveAssociate f, fieldvars)));
    -- (map(R, A), map(A, R, gens A), {xvars, zvars, tvars}, Iz')
    -- )

numeratorMap(Ring, Nothing) :=
numeratorMap(Ring, Ring) := Sequence => (R, AZZ) -> (
    -- R is either a field in normal form or a polynomial ring over that
    -- if AZZ is not null, it should be a polynomial ring with all the variables of R
    --   (as obtained with numeratorMap RQQ.  This version is here to allow reductionMap and numeratorMap
    --   to interact better).
    -- return:
    -- (AtoRp, RtoA, xztvars, Iz), all in the created ring A
    F := if isFieldInNormalForm R then R
      else (
        F' := coefficientRing R;
        if not isFieldInNormalForm F' then error "expected a field in normal form";
        F'
        );
    FI := fieldInfo F;
    kk := if FI.Base === QQ then ZZ else FI.Base;
    z := if FI.Finites === null then {} else gens baseRing FI.Finites; -- base ring is numerator ring
    t := if FI.Independents === null then {} else gens baseRing FI.Independents; -- base ring is numerator ring
    x := if R === F then {} else gens R;
    A := if AZZ === null then
            kk(monoid [x, z, t, MonomialOrder => {#x, #z, #t}]) -- be careful not to set ring vars.
         else
            kk (monoid AZZ);
    xvars := (gens A)_{0..#x-1};
    zvars := (gens A)_{#x..#x+#z-1};
    tvars := (gens A)_{#x + #z .. numgens A - 1};
    fieldvars := matrix {flatten{zvars, tvars}};
    Iz' := if FI.Finites === null then ideal 0_A else (
	Iz := ideal FI.Finites;
        ideal(Iz_*/(f -> sub(primitiveAssociate f, fieldvars))));
    (map(R, A), map(A, R, gens A), (xvars, zvars, tvars), Iz')
    )


-- reduction mod p --
-- input: F: a field, over QQ
--        p: a prime number (reasonably small, e.g. < 2^64)
-- output: Rp = Fp
reductionMap = method()
-- reductionMap(Ring, ZZ) := (F, p) -> (
--     if not isFieldInNormalForm F then error "expected a field in normal form";
--     FI := fieldInfo F;
--     if FI.Base =!= QQ then error "expected field over QQ";
--     kk := ZZ/p;
--     if FI.Independents =!= null then
--       kk = field(kk(monoid FI.Independents));
--     if FI.Finites =!= null then (
--         A := kk (monoid FI.Finites);
--         Iz := sub(ideal FI.Finites, A);
--         kk = field(A/Iz);
--         );
--     map(kk, F)
--     )
reductionMap(Ring, ZZ) := (R, p) -> (
    F := if isFieldInNormalForm R then R
      else (
        F' := coefficientRing R;
        if not isFieldInNormalForm F' then error "expected a field in normal form";
        F'
        );
    FI := fieldInfo F;
    if FI.Base =!= QQ then error "expected field over QQ";
    kk := ZZ/p;
    if FI.Independents =!= null then
      kk = field(kk(monoid FI.Independents));
    if FI.Finites =!= null then (
        A := kk (monoid FI.Finites);
        Iz := sub(ideal FI.Finites, A);
        kk = field(A/Iz);
        );
    if F =!= R then (
        kk = kk (monoid R); -- kk not a field after this!!
        );
    map(kk, R)
    )

-- this method creates a field for each case of the normal forms used in the code
-- not meant to be exported, only for testing.
allFieldCases = method()
allFieldCases ZZ := p -> (
    t1 := getSymbol "t1";
    t2 := getSymbol "t2";
    z1 := getSymbol "z1";
    z2 := getSymbol "z2";

    K1 := QQ;

    A2 := K1[z1,z2,MonomialOrder => Lex];
    z1 = A2_0;
    z2 = A2_1;
    K2 := field(A2/(z1^2-z2-1, z2^3+z2+3));

    K3 := field(K1[t1,t2]);
    t1 = K3_0;
    t2 = K3_1;

    A4 := K3[z1,z2,MonomialOrder => Lex];
    z1 = A4_0;
    z2 = A4_1;
    K4 := field(A4/(z1^2-t1, z2^3-t2*z1));

    K5 := if isPrime p then ZZ/p else GF p;

    A6 := K5[z1,z2,MonomialOrder=>Lex];
    z1 = A6_0;
    z2 = A6_1;
    K6 := field(A6/(z1^2-z2, z2^3+z2+2004));

    K7 := field(K5[t1,t2]);
    t1 = K7_0;
    t2 = K7_1;

    A8 := K7[z1,z2,MonomialOrder => Lex];
    z1 = A8_0;
    z2 = A8_1;
    K8 := field(A8/(z1^2-z2-t1, z2^3+z2+t2));

    (K1,K2,K3,K4,K5,K6,K7,K8)
)    

randomNonzero = method()
randomNonzero Ring := R -> (
    r := random R;
    while (r == 0) do r = random R;
    r
)

beginDocumentation()

load "./Fields/FieldsDoc.m2"
load "./Fields/FieldsTests.m2"

end--

-* Development section *-
restart
needsPackage "Fields"
check "Fields"

restart
uninstallPackage "Fields"
restart
installPackage "Fields"
viewHelp "Fields"

///
-- Examples for modular GCD over tower extensions.
x = symbol x
R = ZZ[x]
f = (x-1)^2*(x^2+x+1)^3*(x^3+x+1)
g = (x-1)^2*(x^2-x+1)^3*(x^3+x+1)
gcd(f,g)

nextPrime (2^28)
Rp = ZZ/268435459[x]
f1 = sub(f, Rp)
g1 = sub(g, Rp)
gcdCoefficients(f1, g1)

-- Here is one extension field
R1 = QQ[a]/(a^2+a+1)
R2 = R1[b, Join => false]/(b^3-2)
R3 = R2[x, Join => false]
use first flattenRing R3
use ambient oo
gcdCoefficients(a+b, b^3-2)

QQ[a]
gcdCoefficients(a+1, a^2+a+1)

A = QQ[a]
B = A[b, Join => false]
monicGCDNaive(f, g) -- f, g are in K[x], for some field K.
f = a+b
g = b^3-2
r0 = g
r1 = f
r2 = r0 - b^2*r1 + a*b*r1 - a^2 * r1 +(a-1)*(a^2+a+1)
r2 = -(1/3) * r2


A1 = toField (QQ[a]/(a^2+a+1))
a
a^-1
(2*a^2+a+1)^-1
r0 = a * r0
g - b^2*f
-- need inverse of -a.  It is a+1
((-a) * (a+1) ) % (a^2+a+1)

///

///
restart
needsPackage "Fields"
F = field(QQ[a]/(a^2 - 2))
phi = map(F,F,{-a})
G = field(QQ[a]/(a^2 + a + 1))
psi = map(G,G,{a^2})
psi a
isWellDefined psi
///

///
restart
needsPackage "Fields"
K0 = field(QQ[c]/(c^3 - 2))
K1 = field(K0[d]/(d^2 + c*d + c^2))
--phi = map(source fieldInclusion K1, K0)
useTower K1
phi1 = map(K1,K0,{c})
phi2 = map(K1,K0,{d})

K0 = field(QQ[c]/(c^3 - 2))
K1 = field(K0[d]/(d^2 + d + 1))
K2 = field(K1[e]/(e^3 - c))
--phi = map(source fieldInclusion K1, K0)
useTower K1
phi1 = map(K1,K0,{c})
phi2 = map(K1,K0,{d*c})
assert isWellDefined phi1
assert isWellDefined phi2

useTower K2
phi1 = map(K2,K0,{c})
phi2 = map(K2,K0,{d*c})
assert isWellDefined phi1
assert isWellDefined phi2

psi1 = map(K2,K1,{d,c})
psi1 d_K1 == d_K2
assert isWellDefined psi1

psi2 = map(K2,K1,{d^2,d*c})
psi2 d_K1 == (d^2)_K2
assert isWellDefined psi2

K1 = field (QQ[t])
K1 = frac (QQ[t])
phi = map(K1,K1,{t^2})
isWellDefined phi -- fails
///


--- Notes on interface for this package 8/8/25

1. Create a field with 'field';  Eventually this will be done directly by toField and frac.
2. (done) Be able to take the inverse of an element in the field.
3. (done) Make denominator/numerator work; depending on whether there are transcendental elements or not.
4. (done) Primitive associates, content, etc (along the same lines as the above)
5. (done) monic GCD of a pair(?) of polynomials;  Need to get the coefficients.
6. (single variable separable done) Be able to factor a multivariable polynomial over such a field.
7. Compute the minimalPolynomial of an element
8. Compute the norm/trace of an element in an extension (given as a ring map)
9. Compute the ring of integers of a number field
10. Compute a better generator for a number field or a curve (e.g. polredbest)
11. Compute discriminant of a field extension (again, given as a ring map)
12. Getting primary decomposition working using these fields.
13. Absolute factorization/primary decomposition

-- Questions
1. How should generators work?  Does one mean *all* the generators? Transcendental/Finite?
2. Should we get rid of "linear" finite variables in our presentation? (see monomialCurveIdeal example)
3. Iterated resultants in squareFreeFactor?
4. ideal of Field should return the defining ideal, but in what ring? in flattened ring or over the fraction field adjoin variables?
5. Maps of fields are not very robust at this point.  Can we improve this?  In particular,
   can we take a map of fields not in normal form and return the corresponding map between nf fields?

-- notes from 1/22:
1. in the below example, make sure one can take kernel of map(D,A).
///
      A = QQ[a..d]
      B = A/monomialCurveIdeal(A, {1,2,3})
      D = field B
      phi = map(D,A)
      ker phi -- fails
      psi = map(D,B)
      ker psi -- fails
///

-- notes from 2/19:
///
--- think about some good tests of GBs over field created using field()

--- GCDs
--- need to extend this in two directions:
--- a) GCD of several polynomials in one variable, and
---     (completed above)
--- b) GCD of multivariate polynomials

--- Setup: L = K(t_1..t_r)[a_1..a_s]/I
---        K : basic field (either QQ, ZZ/p or a GF)
---        t_1..t_r independents
---        a_1..a_s algebraic elements, finite over t_1..t_r
---        R = L[x_1..x_n]
---        L_1 := L(x_1)
---        S_1 := L[x_1]
---        R_1 := L_1[x_2..x_n]
---        f \in R
--- 1) Get gcd of all the coefficients of f in R1.  This will be a polynomial in S_1.
--- 2) Factors of the lead coefficient from 1) will be factors of f.
--- 3) Factor f in R1.  For each irreducible factor, take a primitive associate, if necessary to clear denominators
---      and perform the procedure from 1).  This gives a polynomial in S_1 for each factor which is a spurious factor
---      of this term from S_1.  Replace the factor by the result of dividing by the spurious factor and return the results.

--- ideas:
---    1) Should we look for all linear factors involving only a single variable

restart
debug needsPackage "Fields"

-- need something like fieldGens (Field)

-- factoring two variable case
A = QQ[a..d]
B = A/monomialCurveIdeal(A, {1,2,3})
L = field B
useTower L
R = L[x,y]
f = ((y+1)*x + a*y)*(x*y + c*y + b)*(x+y+a)*(y+a)*(x+c)
facData = multivarFactorData f
assert(facData.Coefficient * product apply(facData.Factors, p -> (p#1)^(p#0)) == f)
multivarFactors f

-- factoring three variable case
A = QQ[a..d]
B = A/monomialCurveIdeal(A, {1,2,3})
L = field B
useTower L
R = L[x,y,z]
f = ((y+1)*x + y + c*z)*(x*y + a*y + d*z)*(x+y+a)*(x+z+b)*(y+a)*(z+b)*(x+c);
facData = multivarFactorData f
elapsedTime multivarFactors f
assert(facData.Coefficient * product apply(facData.Factors, p -> (p#1)^(p#0)) == f)
elapsedTime singVarLinFacs = singleVariableLinearFactors f -- not sure if this is actually helpful
assert(product apply(singVarLinFacs#0, p -> (p#1)^(p#0)) * singVarLinFacs#1 == f)
g = last singVarLinFacs
elapsedTime multivarFactors g

-- gcd two variable case
A = QQ[a..d]
B = A/monomialCurveIdeal(A, {1,2,3})
D = field B
useTower D
R = D[x,y]
f = ((y+1)*x + a*y)*(x*y + c*y + b)*(x+y+a)*(y+a)*(x+c);
g = ((y+1)*x + a*y)*(x*y + d*y + b)*(x+y+a)*(y+a)*(x+c);
(monsF,coeffsF) = coefficients(f, Variables => {x})
S = D[y]
coeffsF = sub(coeffsF, S)
fCoeffList = flatten entries coeffsF
coeffGCD = monicGCD fCoeffList
f2 = f // sub(coeffGCD,R)
g2 = g // sub(coeffGCD,R)

E = field(D[y])
R2 = E[x]
useTower E
f2 = sub(f2,R2)
g2 = sub(g2,R2)
h = monicGCD(f2,g2,Strategy=>"Modular")
h = (mydenominator h) * h
assert(h == ((y+1)*x + a*y)*(x+y+a)*(x+c))
h = monicGCD(f2,g2,Strategy=>"Naive")
h = (mydenominator h) * h
assert(h == ((y+1)*x + a*y)*(x+y+a)*(x+c))

-- gcd three variable case (not working yet, need to adapt the above example)
A = QQ[a..d]
B = A/monomialCurveIdeal(A, {1,2,3})
D = field B
useTower D
R = D[x,y,z]
f = ((y+1)*x + y + c*z)*(x*y + a*y + d*z)*(x+y+a)*(x+z+b)*(y+a)*(z+b)*(x+c);
g = ((y+1)*x + y + c*z)*(x*y + d*y + a*z)*(x+y+a)*(x+z+b)*(y+a)*(z+b)*(x+c);
(monsF,coeffsF) = coefficients(f, Variables => {x})
fCoeffList = flatten entries coeffsF


E1 = field (D[y,z])
useTower E1
R1 = E1[x]
f1 = sub(f,R1);
g1 = sub(g,R1);
h1 = monicGCD(f1,g1,Strategy=>"Naive");
assert(h1 == ((y+1)*x+y+c*z)*(x+y+a)*(x+z+b)*(x+c))
assert(f1 // h1 == (x*y + a*y + d*z)*(y+a)*(z+b))
assert(g1 // h1 == (x*y + d*y + a*z)*(y+a)*(z+b))
f2 = f1 // h1
g2 = g1 // h1
///

2.  Things we would want to work before release:
    a.  Make it easy to adjoin an element to a field:
           algebraic case: have a field F, and an irreducible polynomial p(x), adjoin a root of it
           transcendental case: R SPACE Symbol (ideally R(x) but this translates to R SPACE Symbol)
           TODO: make the above work well with VariableIterators
    b.  Want to use any fields we create as the coefficient field in a GB
    c.  Would like factorization working, at least in the separable case.
    d.  GCDs of polynomials defined over such a field.
    e.  kernels of ring maps with rings involving these fields.
    f.  Easy creation of Frobenius map, if applicable
    g.  Random elements of a field (take care with transcendental variables, but should be easy for finite extensions)

    Galois field things:
    g.  Field compositum
    h.  Field intersection
    i.  Automorphism group of an extension (?)
    j.  Finding a primitive element, when it exists, together with maps in both directions
    h.  Determining separability and normality 

