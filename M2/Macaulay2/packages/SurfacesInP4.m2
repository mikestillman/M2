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
    "readExampleFile",
    "example",
    "names",
    "surfacesP4",
    "sectionalGenus",
    "arithmeticGenus",
    "canonicalModule"
    }

readExampleFile = method()
--beginning of each example is ---*\\s
--ending of each is beginning of next
--each example is a string or collection of strings, looking like M2 code.
--allow several lines of comments (beginning with --)

readExampleFile String := HashTable => name -> (
    filename := if fileExists name then name else currentFileDirectory | "SurfacesInP4/" | name;
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
    value exampleHash#ind
    )

names = method()
names HashTable := (H) -> sort keys H

sectionalGenus  = method()
sectionalGenus Ideal := I -> (genera I)_1

arithmeticGenus = method()
arithmeticGenus Ideal := I -> (genera I)_0

   canonicalModule = method()
   canonicalModule Ideal := I -> (
       S := ring I;
       n := numgens S;
       Ext^(codim I)(S^1/I, S^{-n})
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
   are bounded. It is conjectured that the bound is 15, but the known bound is ****; see ****.
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
   canonicalModule I
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
TEST///
P = readExampleFile "P4Surfaces.txt";
--P = surfacesP4;
for k in keys P list (
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
    assert(g == (genera I)#1);
    {k,deg,g}
    )
///

end--
-* Development section *-
restart
uninstallPackage "SurfacesInP4"
restart
installPackage "SurfacesInP4"
restart
debug needsPackage "SurfacesInP4"
check "SurfacesInP4"
viewHelp SurfacesInP4



needsPackage "SurfacesInP4"
P = readExampleFile "P4Surfaces.txt";
names P
I = example("enr.d11.g10", P);
minimalBetti I
degree I
genera I
genus I
euler I
sectionalGenus  = I -> (genera I)_1
arithmeticGenus = I -> (genera I)_0

(gens sub( I1, S))%I
(gens I) % (sub( I1, S))
minimalBetti I1
regex("^---* *(.*)", "---   ab c d")
regex("^---* *(.*)", "---   --")

restart
needsPackage "SurfacesInP4"
P = readExampleFile "SurfacesInP4/P4Surfaces.txt";
names P

I = example("rat.d8.g6", P)
degree I
(genera I)#1 -- sectional genus
minimalBetti I

I = example("elliptic.scroll", P);
describe kk
minimalBetti I
degree I
genera I

for k in keys P list (
    << "doing " << k << endl;
    I = example(k, P);
    time {k, degree I, genera I, minimalBetti I}
    )

restart
needsPackage "SurfacesInP4"



netList oo
    << "doing " << k << endl;
    I = example(k, P);
    time {k, degree I, genera I, minimalBetti I}
    )


netList oo
I = example("enr.d11.g10", P) -- hmmm, not good
keys P
S = ZZ/31991[
-*
--bad:
"bielliptic.d10.g6"
"bielliptic.d15.g21"
"enr.d11.g1"

S = ZZ/911[x,y,z,u,v]
I = value P#"bielliptic.d10.g6";
minimalBetti I

S = ZZ/911[x,y,z,u,v]
I = value P#"bielliptic.d15.g21";
minimalBetti I

S = ZZ/43[x,y,z,u,v]
I = value P#"enr.d11.g10";
minimalBetti I
*-
