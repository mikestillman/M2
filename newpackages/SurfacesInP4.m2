newPackage("SurfacesInP4",
    Authors => {{Name => "David Eisenbud", 
                 Email => "de@msri.org", 
                 HomePage => "http://www.msri.org/~de"},
                {Name => "Mike Stillman", 
                 Email => "mike@math.cornell.edu", 
                 HomePage => "http://pi.math.cornell.edu/~mike"}},
    Version => "0.1",
    Date => "January 5, 2021",
    Headline => "Smooth surfaces in P4, not of general type",
    AuxiliaryFiles => true,
    DebuggingMode => true
    )

export {
    "findRegularSequence",
    "Colon",
    "Random",
    "readExampleFile",
    "example",
    "names",
    "surfacesP4",
    "sectionalGenus",
    "arithmeticGenus",
    "canonicalModule",
    "intersectionProduct",
    "intersectionMatrix"
    }

--SurfacesInP4#"source directory"|"SurfacesInP4/P4Surfaces.txt"

readExampleFile = method()
--beginning of each example is ---*\\s
--ending of each is beginning of next
--each example is a string or collection of strings, looking like M2 code.
--allow several lines of comments (beginning with --)

readExampleFile String := HashTable => name -> (
    filename := if fileExists name then name else SurfacesInP4#"source directory" | "SurfacesInP4/" | name;
    --filename := currentFileDirectory | "SurfacesInP4/" | name;
    --“SurfacesInP4/P4Surfaces.txt”;
    << "file: " << filename << endl;
    N := lines get filename;
    --N := lines get name;
    re := "^---+ *(.*)"; -- at least -'s, followed by spaces, then grab the last match.
    pos := positions(N, s -> match(re,s));
    indices := for p in pos list (
            m := last regex(re, N#p);
            substring(m, N#p)
            );
    hashTable for i from 0 to #pos - 1 list indices#i => (
        p := pos#i;
        concatenate between("\n", if i == #pos - 1 then
            for j from p+1 to #N-1 list N#j
        else
            for j from p+1 to pos#(i+1)-1 list N#j
        ))
    )

example = method()
example(String, HashTable) := (ind, exampleHash) -> (
    if not exampleHash#?ind then error "example does not exist";
    trim value exampleHash#ind
    )

names = method()
names HashTable := (H) -> sort keys H

sectionalGenus  = method()
sectionalGenus Ideal := I -> (genera I)_1

arithmeticGenus = method()
arithmeticGenus Ideal := I -> (genera I)_0

findRegularSequence = method()
findRegularSequence Ideal := Ideal => J -> (
    --finds a random homogeneous maximal regular sequence in J of minimal
    --degree, and returns the link of J with respect to this sequence.
    S := ring J;
    if J == ideal(1_S) then return J;
    genlist := J_*;
    deglist :=  sort unique (genlist/(g -> (degree g)_0));
    D := #deglist;
    II := apply(deglist, d -> ideal select(genlist, g -> (degree g)_0 <= d));
    codims := apply(II, I -> codim I);
    levels := apply(D, i -> gens II_i * matrix basis(deglist_i, II_i));
    regseq := levels_0 * random(source levels_0, S^{codims_0:-deglist_0});
    for i from 1 to D-1 do(
	regseq = regseq | 
	         levels_i * random(source levels_i, S^{codims_i-codims_(i-1):-deglist_i}));
    regs := ideal regseq;
    assert (isHomogeneous regs);
    assert (codim regs == codims_(D-1));
    regs
    )

canonicalModule = method(Options => {Strategy => Colon})--Ext, Random, Colon})
canonicalModule Ideal := opts ->  I -> (
    S := ring I;
    n := numgens S;
    c := codim I;
    if not opts.Strategy === Ext then (
        CI := ideal take(I_*, c);
	twist := CI/degree/first//sum - n;
        if codim CI == c then return S^{twist}**((CI:I)/CI);

        << "didn't quickly find a complete intersection, using Ext..." << endl;
        );
    -- either the first c gens of I are not a CI, or the user asked to not use that method...
    Ext^(codim I)(S^1/I, S^{-n})
    )

intersectionProduct = method()
intersectionProduct (Ideal, Module, Module) := ZZ => (I,M,N) -> (
    euler comodule I - euler M - euler N + euler(M**N)
)
intersectionMatrix = method()
intersectionMatrix(Ideal, List) := Matrix=> (I,L) -> (
   matrix for M in L list for N in L list intersectionProduct(I,M,N)
)

--surfacesP4 = readExampleFile "./SurfacesInP4/P4Surfaces.txt"

-* Documentation section *-
beginDocumentation()

doc///
Key
  SurfacesInP4
Headline
  List of surfaces not of general type in P^4. 
Description
  Text
   It is known that the degrees of smooth projective complex surfaces, not of general type, embedded in P^4,
   are bounded. It is conjectured that the bound is 15, but the known bound is 80; see ***.
  Example
   P = readExampleFile "P4Surfaces.txt";
   names P
  Text
   Each example has a name consisting of the Enriques classification
   (ab = Abelian, enr = Enriques, ell = Elliptic, rat = rational etc.)
  Example
   I = example("enr.d11.g10", P);
  Text
   This is an enriques surface of degree 11 and sectional genus 10 in P4.
  Example
   degree I
   euler I
   arithmeticGenus I
   sectionalGenus I
   minimalBetti I
   K = canonicalModule I
   H = S^1/I**S^{1}
   intersectionMatrix(I,{H,K})
Acknowledgement
Contributors
References
Caveat
 Though these are supposed be examples in characterist 0, they are actually computed in characteristic p.
 This was done in Macaulay classic, and seemed necessary because of limitations in speed, and because
 the adjunction of roots of unity was not possible there.
SeeAlso
///

///
Key
Headline
Usage
Inputs
Outputs
Consequences
  Item
Description
  Text
  Example
  CannedExample
  Code
  Pre
ExampleFiles
Contributors
References
Caveat
SeeAlso
///

-* Test section *-
///
-*
  restart
  needsPackage "SurfacesInP4"
*-
P = readExampleFile "P4Surfaces.txt";
#keys P
--P = surfacesP4;
names P
for k in names P do elapsedTime (
    if k === "ell.d12.g14.ssue" then ( << "skipping " << k << endl; continue);
    if k === "k3.d11.g11.ss2" then ( << "skipping " << k << endl; continue);
    if k === "k3.d11.g11.ss1" then ( << "skipping " << k << endl; continue);
    if k === "k3.d11.g11.ss3" then ( << "skipping " << k << endl; continue);
    if k === "rat.d10.g8" then ( << "skipping " << k << endl; continue);
    << "doing " << k << endl;
    deg := null;g := null;
    I := example(k,P);
    R := regex("\\.d([0-9]+)\\.",k);
    if R =!= null and #R > 1 then
    deg = value substring(R#1,k);
    
    R = regex("\\.g([0-9]+)",k);
    if R =!= null and #R > 1 then        
    g =  value substring(R#1,k);
    assert(3 == dim I);
    assert(deg == degree I);
    assert(g == sectionalGenus I);
    S := ring I;
    elapsedTime K = canonicalModule I;
    H = S^1/I**S^{1};
    M = elapsedTime intersectionMatrix(I,{H,K});
    print {k, deg, g, M};
    )
///
///
-*
  restart
  needsPackage "SurfacesInP4"
*-
P = readExampleFile "P4Surfaces.txt";
#keys P
--P = surfacesP4;
names P
elapsedTime for k in names P do elapsedTime (
    << "doing " << k << endl;
    I := example(k,P);
    S := ring I;
    J := jacobian I;
elapsedTime    singI = minors(2, J)+I;
elapsedTime c = codim singI;
    print {k, c}
    )

elapsedTime for k in names P do elapsedTime (
    << "doing " << k << endl;
    I := example(k,P);
    S := ring I;
    J := jacobian I;
elapsedTime    singI = minors(2, J)+I;
elapsedTime gbsingI := groebnerBasis (singI, Strategy => "F4");
elapsedTime c = codim ideal leadTerm gbsingI;
    print {k, c}
    )


///

TEST ///
-*
  restart
  needsPackage "SurfacesInP4"
*-
P = readExampleFile "P4Surfaces.txt";
#keys P
--P = surfacesP4;
I = example("ab.d10.g6", P)
elapsedTime K=canonicalModule(I); -- 0.0499788 seconds elapsed
elapsedTime K=canonicalModule(I, UseColon =>false); -- 0.091749 seconds elapsed
elapsedTime K=canonicalModule(I, UseExt => true); -- 0.091749 seconds elapsed

I = example("ell.d12.g14.ssue", P);
elapsedTime K=canonicalModule(I);  -- 0.597377 seconds elapsed
elapsedTime K=canonicalModule(I, UseColon =>false);  -- 1.33254 seconds elapsed
elapsedTime K=canonicalModule(I, UseExt => true); -- too long

I = example("k3.d11.g11.ss1",P);
elapsedTime K=canonicalModule(I);  -- 3.08853 seconds elapsed
elapsedTime K=canonicalModule(I, UseColon =>false); --too long
elapsedTime K=canonicalModule(I, UseExt => true); --too long

I = example("k3.d11.g11.ss3",P);
elapsedTime K=canonicalModule(I);  -- 0.571776 seconds elapsed
elapsedTime K=canonicalModule(I, UseColon =>false);  -- 3.49462 seconds elapsed
elapsedTime K=canonicalModule(I, UseExt => true); 

I = example("rat.d10.g8",P);
elapsedTime K=canonicalModule(I, Strategy => Colon);  -- 0.392106 seconds elapsed
elapsedTime K=canonicalModule(I, UseColon =>false); 
elapsedTime K=canonicalModule(I, UseExt => true); 


debug needsPackage "Divisor"
R = (ring I)/I
elapsedTime K = canonicalDivisor(R, IsGraded=>true);
K
elapsedTime KM = divisorToModule K
euler oo
euler(KM ** KM)

CI = ideal(I_0, I_1)
codim CI
S^{first degree CI_0 + first degree CI_1 - 5} ** (prune Hom(S^1/I, S^1/CI))
euler oo
Ext^2(S^1/I, S^{-5})
euler oo
res o60
///
end--
-* Development section *-
restart
uninstallPackage "SurfacesInP4"
restart
installPackage "SurfacesInP4"
peek loadedFiles
restart
debug needsPackage "SurfacesInP4"
check "SurfacesInP4"
viewHelp SurfacesInP4
viewHelp

needsPackage "SurfacesInP4"
P = readExampleFile "P4Surfaces.txt";
names P

Ilist = for s in names P list s => elapsedTime example(s,P);

I = last Ilist_4;
    assert(deg == degree I);
    assert(g == sectionalGenus I);
    K = canonicalModule I;
    H = S^1/I**S^{1};
    {k,deg,g, elapsedTime intersectionMatrix(I,{H,K})}


H = (ring I1)^{1}**comodule I1
K
intersectionProduct(I1,H,saturate image presentation(K**K))
elapsedTime saturate image presentation(K**K)


analyzeExample = k -> (
    deg := null;g := null;
    I = example(k,P);
    R := regex("\\.d([0-9]+)\\.",k);
    if R =!= null and #R > 1 then
    deg = value substring(R#1,k);
    
    R = regex("\\.g([0-9]+)",k);
    if R =!= null and #R > 1 then        
    g =  value substring(R#1,k);
    assert(3 == dim I);
    assert(deg == degree I);
    assert(g == sectionalGenus I);
    K = canonicalModule I;
    S = ring I;
    H = S^1/I**S^{1};
     {k,deg,g}
)
elapsedTime intersectionMatrix(I,{H,K})}
k = "biellitic.d10.g6"
analyzeExample k
intersectionProduct(I,H,H)
intersectionProduct(I,H,K)
intersectionProduct(I,K,K)
minimalBetti K
