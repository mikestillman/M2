newPackage(
    "CanonicalMaps",
    Version => "0.1",
    Date => "16 June 2025",
    Authors => {
        {   Name => "Gregory G. Smith", 
            Email => "ggsmith@mast.queensu.ca", 
            HomePage => "http://www.mast.queensu.ca/~ggsmith"
            },
        {   Name => "Mike Stillman", 
            Email => "mike@math.cornell.edu", 
            HomePage => "http://www.math.cornell.edu/~mike"
            }},
    Headline => "implements canonical and standard maps for modules",
    Keywords => {"Commutative Algebra"},
    AuxiliaryFiles => false,
    DebuggingMode => true
    )

export {
    "kernelMap",
    "cokernelMap",
    "coimageMap",
    "imageMap",
    "coimageImageMap"
    }

kernelMap = method()
kernelMap Matrix := Matrix => f -> (
    -- the kernelMap of `f : M --> N` is
    -- the canonical inclusion `ker f --> M`.
    M := source f;
    K := kernel f;
    map(M, K, generators K // generators M)
    )

-- Question: would we like to add this functionality?
-- kernelMap Module := Matrix => K -> (
--     if not K.cache.?kernel then
--         error "expected module to be constructed as a kernel";
--     kernelMap K.cache.kernel
--     )

kernelMap(Matrix, Matrix) := Matrix => (g, f) -> (
    -- f : B --> C
    -- g : A --> B
    -- kermap f: ker f --> B
    -- result should be A --> ker f.
    -- assume f*g = 0.
    -- returns ghat : A -> ker f s.t. (kermap f)*ghat == g
    if source f != target g then error "expected target of first map to be the same as source of the second map";
    if f*g != 0 then error "expected the composite map to be zero";
    eta := kernelMap f;
    quotient(g, eta)
    )

cokernelMap = method()
cokernelMap Matrix := Matrix => (f) -> (
    C := target f;
    map(coker f, C, id_C)
    )

cokernelMap(Matrix, Matrix) := Matrix => (g, f) -> (
    -- f : B --> C
    -- g : C --> A
    --  s.t. g*f = 0
    -- if p : C --> coker f is the cokernel map of f
    -- result should be coker f --> A.
    -- return the map ghat : coker f --> A s.t. ghat * p = g,
    if target f != source g then error "expected target of second map to be the same as source of the first map";
    if g*f != 0 then error "expected the composite map to be zero";
    p := cokernelMap f;
    map(target g, target p, matrix g)
    )

coimageMap = method()
coimageMap Matrix := Matrix => (f) -> cokernelMap kernelMap f

imageMap = method()
imageMap Matrix := Matrix => (f) -> kernelMap cokernelMap f

coimageImageMap = method()
coimageImageMap Matrix := Matrix => (f) -> (
    eta := kernelMap f; -- eta: ker f --> B
    p := cokernelMap f; -- p: C --> coker f
    theta' := cokernelMap eta; -- theta' : B --> coker eta == coim f
    theta := kernelMap(f, p); -- theta:  B --> ker p == im f
    mu := cokernelMap(theta, eta); -- coim f --> im f
    mu
    )

-- axiom of an Abelian category: coimageToImage f is an isomorphism

beginDocumentation()

doc ///
    Key
        CanonicalMaps
    Headline
        implements canonical and standard maps for modules
    Description
        Text
    Caveat
    SeeAlso
///

///
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

-*
  restart
  needsPackage "CanonicalMaps"
*-
TEST ///
  R = ZZ/101[a..d]
  f = vars R
  eta = kernelMap f
  assert isWellDefined eta
  assert(source eta === kernel f)
  assert(target eta === source f)
  assert(f * eta == 0)
  assert(kernelMap f === eta)
  assert(ker eta == 0)
///

-*
  restart
  needsPackage "CanonicalMaps"
*-
TEST ///
  R = ZZ/101[a..d]
  f = inducedMap(R^1/ideal(a^3, b^3), ideal(a^2, a*b^2)/ideal(a^4, b^4))
  assert isWellDefined f
  eta = kernelMap f
  assert isWellDefined eta

  eta = kernelMap f
  assert isWellDefined eta
  assert(source eta === kernel f)
  assert(target eta === source f)
  assert(f * eta == 0)
  assert(kernelMap f === eta)
  assert(kernel eta == 0)

  h = map(source f, R^1, matrix{{a},{0}})
  assert isWellDefined h
  assert(f*h == 0)
  hlift = kernelMap(h, f)
  assert isWellDefined hlift
  assert(eta * hlift === h)
///

-*
  restart
  needsPackage "CanonicalMaps"
*-
TEST ///
  R = ZZ/101[a..d]
  f = vars R
  p = cokernelMap f
  assert isWellDefined p
  assert(source p === target f)
  assert(target p === cokernel f)
  assert(p * f  == 0)
  assert(cokernelMap f === p)
  assert(coker p == 0)
///


-*
  restart
  needsPackage "CanonicalMaps"
*-
TEST ///
  R = ZZ/101[a..d]
  f = inducedMap(R^1/ideal(a^3, b^3), ideal(a^2, a*b^2)/ideal(a^4, b^4))
  assert isWellDefined f
  p = cokernelMap f
  assert isWellDefined p
  assert(cokernel p == 0)

  assert(source p === target f)
  assert(target p === cokernel f)
  assert(p * f == 0)
  assert(cokernelMap f === p)

  D = coker matrix{{a^2, b^2}} ++ coker matrix{{a^2, a*b^2, b^3}}
  h = map(D, target f, matrix{{1_R},{1_R}})
  assert isWellDefined h
  assert(h*f == 0)
  hlift = cokernelMap(h, f)
  assert isWellDefined hlift
  assert(hlift * p === h)
///

TEST ///

///

end--

-* Development section *-
restart
debug needsPackage "CanonicalMaps"
check "CanonicalMaps"

uninstallPackage "CanonicalMaps"
restart
installPackage "CanonicalMaps"
viewHelp "CanonicalMaps"

