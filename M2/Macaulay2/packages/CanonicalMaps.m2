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
    "coimageImageMap",
    "fiberProduct",
    "fiberProductMap",
    "fiberSum",
    "fiberSumMap",
    "superMap",
    "cosuper",
    "cosuperMap",
    "trimMap",
    "pruneMap"
    }

-- TODO:
--  various "standard" canonical maps (adjoint maps)
--  (in issues.m2)

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
    -- f: B --> C
    eta := kernelMap f; -- eta: ker f --> B
    p := cokernelMap f; -- p: C --> coker f
    theta' := cokernelMap eta; -- theta' : B --> coker eta == coim f
    theta := kernelMap(f, p); -- theta:  B --> ker p == im f
    mu := cokernelMap(theta, eta); -- coim f --> im f
    mu
    )

-- axiom of an Abelian category: coimageToImage f is an isomorphism

fiberProduct = method()
fiberProduct(Matrix, Matrix) := Module => (phi, phi') -> (
    -- Given: phi : B --> C
    -- Given: phi' : B' --> C
    -- return: (B x_C B', p, p'), and stash the kernel map and map B ++ B' --> C
    C := target phi;
    if C =!= target phi' then error "expected maps to have the same target";
    direct := map(C, source phi ++ source phi', (matrix phi) | (-matrix phi'));
    eta := kernelMap direct;
    E := source eta;
    E.cache#fiberProduct = (eta, direct); -- note that phi == direct_[0], phi' == -direct_[1]
    E
    )
fiberProductMap = method()
fiberProductMap Module := Sequence => E -> (
    if not E.cache#?fiberProduct then error "expected argument to be constructed as a fiber product";
    (eta, direct) := E.cache#fiberProduct;
    (eta^[0], eta^[1]) -- phi: B --> C, phi' : B' --> C, E = B xC B', eta^[0]: E --> B, eta^[1]: E --> B'
    )
    
fiberProductMap(Module, Matrix, Matrix) := Matrix => (E, alpha, alpha') -> (
    -- if alpha, alpha' are maps A --> B, A --> B', and
    -- E is the fiber product of (f,f') : B ++ B' --> C
    -- and if phi*alpha = phi'*alpha', then this function returns the unique map
    -- h:A --> E such that alpha = p*h, alpha' = p'*h.
    if not E.cache#?fiberProduct then error "expected first argument to be constructed as a fiber product";
    if source alpha =!= source alpha' then error "expected maps to have the same source";
    (gmap, direct) := E.cache#fiberProduct;
    phi := direct_[0];
    phi' := -direct_[1];
    if phi*alpha != phi'*alpha' then error "expected maps to commute";
    h := map(source direct, source alpha, (matrix alpha) || (matrix alpha'));
    kernelMap(h, direct)
    )

fiberSum = method()
fiberSum(Matrix, Matrix) := Module => (phi, phi') -> (
    -- Given: phi : B --> C
    -- Given: phi' : B --> C'
    -- return: (C ++_B C', q, q'), and stash the cokernel map and map B --> C ++ C'
    B := source phi;
    if B =!= source phi' then error "expected maps to have the same source";
    direct := map(target phi ++ target phi', B, (matrix phi) || (-matrix phi'));
    rho := cokernelMap direct;
    E := target rho;
    E.cache#fiberSum = (rho, direct); -- note that phi == direct^[0], phi' == -direct^[1]
    E
    )
fiberSumMap = method()
fiberSumMap Module := Sequence => E -> (
    if not E.cache#?fiberSum then error "expected argument to be constructed as a fiber sum";
    (rho, direct) := E.cache#fiberSum;
    (rho_[0], rho_[1]) -- phi: B --> C, phi' : B --> C', E = C ++_B C', rho_[0]: B --> E, rho_[1]: B' --> E
    )
    
fiberSumMap(Module, Matrix, Matrix) := Matrix => (E, alpha, alpha') -> (
    -- if alpha, alpha' are maps C --> D, C' --> D, and
    -- E is the fiber sum of (phi,phi') : B --> C ++_B C' = E
    -- and if alpha * phi = alpha' * phi', then this function returns the unique map
    -- h:E --> D such that alpha = h * q, alpha' = h * q'.
    if not E.cache#?fiberSum then error "expected first argument to be constructed as a fiber sum";
    if target alpha =!= target alpha' then error "expected maps to have the same target";
    (rho, direct) := E.cache#fiberSum;
    phi := direct^[0];
    phi' := -direct^[1];
    if alpha * phi != alpha' * phi' then error "expected maps to commute";
    h := map(target alpha, target direct, (matrix alpha) | (matrix alpha'));
    cokernelMap(h, direct)
    )

superMap = method()
superMap Module := Matrix => M -> map(super M, M, generators M)

cosuper = method()
cosuper Module := Module => M -> image generators M

cosuperMap = method()
cosuperMap Module := Matrix => M -> map(M, cosuper M, id_(cosuper M))

pruneMap = method(Options => options prune)

-- pruneMap M : M --> prune M (opposite of the current pruningMap)
--  (pruneMap M)^-1 : prune M --> M

pruneMap Module := opts -> M -> (
    M' := prune(M, opts);
    f := M'.cache.pruningMap;
    map(M', M, f^(-1))
    )

-- trimMap is complicated by strategies in trim.  Not sure how to handle this?
-- trimMap M : M --> trim M (basically the identity on generators)
--  (trimMap M)^-1 : trim M --> M (what about for ideals?)



-- coverMap, superMap
-- given a subquotient module M = P/Q of F (Q \subset P \subset F), F free.
-- ambient M := F (not functorial, i.e. cannot 
-- cover M := G, the free module whose basis elements correspond
--   to the given basis of M (equivalently, basis of P)
-- coverMap M := cover M --> M --> 0 (already exists)
-- super M := F/Q
-- cosuper M := P/0
-- superMap M := M --> F/Q
-- cosuperMap M := P/0 --> P/Q = M (quotient by Q)
-- internal info about these: (stored data)
--   gens M := G --> F, image gens M == P
--   relations M := cover Q --> F, image relations M == Q

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

-*
  restart
  needsPackage "CanonicalMaps"
*-
TEST ///
  -- testing ker and coker universal maps, for complexes
  S = ZZ/11[x,y,z];
  f = random(S^2, S^{-1,-1,-1})

  imf = imageMap f
  cof = coimageMap f
  assert isWellDefined imf
  assert(ker imf == 0)
  assert(source imf == image f) -- not nec ===
  assert(target imf === target f)
  assert(imf * (f // imf) === f) -- f factors through the image
  assert(imf * kernelMap(f, cokernelMap f) === f)

  assert isWellDefined cof
  assert(coker cof == 0)
  assert(source cof === source f)
  assert(target cof == coimage f)
  assert((cof \\ f) * cof === f) -- f factors through the coimage
  assert(cokernelMap(f, kernelMap f) * cof === f) -- f factors through the coimage  

  -- two ways to construct coimage f --> image f.
  eta = kernelMap f
  p = cokernelMap f
  choice1 = cokernelMap(kernelMap(f, p), eta)
  assert(source choice1 === target coimageMap f)
  assert(target choice1 === source imageMap f)
  -- 
  choice2 = kernelMap(cokernelMap(f, eta), p)
  assert(choice1 === choice2)
  assert(kernel choice1 == 0)
  assert(cokernel choice1 == 0)

  g = coimageImageMap f
  assert(choice1 === g)
  h = g^-1
  assert isWellDefined g
  assert isWellDefined h
  assert(h * g == 1)
  assert(g * h == 1)
///

-*
  restart
  needsPackage "CanonicalMaps"
*-
TEST /// -- fiberProduct
  -- given: phi : B --> C
  --        gamma : C --> D
  -- Check if (ker gamma) x_C phi = kernelMap(gamma * phi).
  -- There is a natural map between them, mu.
  -- Is it an isomorphism, by using universal property
  --  of kernel, and fiber product.
  R = ZZ/101[a..d]
  phi = random(R^2, R^{3:-1})
  gamma = random(R^{2}, R^2)

  g = gamma*phi
  eta = kernelMap gamma
  h2 = kernelMap g
  h1 = kernelMap(phi * h2, gamma) -- induced map from ker g --> ker gamma.
  assert(eta * h1 === phi * h2)

  P = fiberProduct(eta, phi)
  --assert isWellDefined P -- isWellDefined does not yet apply to Module
  (p, p') = fiberProductMap P
  assert isWellDefined p
  assert isWellDefined p'
  assert(source p === P)
  assert(source p' === P)
  assert(target p === source eta)
  assert(target p' === source phi)
  assert(eta * p === phi * p')

  mu = fiberProductMap(P, h1, h2)
  assert isWellDefined mu
  assert isIsomorphism mu
  assert(target mu === P)
  assert(source mu === source h2)
  assert(p * mu === h1)
  assert(p' * mu === h2)

  -- let's construct the inverse of mu using the univ property of kernels
  nu = kernelMap(p', g)
  assert isWellDefined nu
  assert isIsomorphism nu
  assert(target nu === source h2)
  assert(source nu === P)
  assert(nu * mu == 1)
  assert(mu * nu == 1)
  assert(h2 * nu === p')
  assert(h1 * nu === p)

///

TEST /// -- fiberSum
  -- the dual of the previous test.
  -- given: phi : B --> C
  --        gamma : C --> D
  -- Check if (coker phi) ++_C gamma = cokernelMap(gamma * phi).
  -- There is a natural map between them, mu.
  -- Is it an isomorphism, by using universal property
  --  of cokernel, and fiber sum.
  R = ZZ/101[a..d]
  phi = random(R^2, R^{3:-1})
  gamma = random(R^{2}, R^2)

  g = gamma*phi
  pC = cokernelMap phi
  pD = cokernelMap g
  h = cokernelMap(pD * gamma, phi) -- induced map from coker phi --> coker g.
  assert(h * pC === pD * gamma)

  P = fiberSum(pC, gamma)
  --assert isWellDefined P -- isWellDefined does not yet apply to Module
  (q, q') = fiberSumMap P
  assert isWellDefined q
  assert isWellDefined q'
  assert(target q === P)
  assert(target q' === P)
  assert(source q === target pC)
  assert(source q' === target gamma)
  assert(q * pC === q' * gamma)

  mu = fiberSumMap(P, h, pD)
  assert isWellDefined mu
  assert isIsomorphism mu
  assert(target mu === target pD)
  assert(source mu === P)
  assert(pD === mu * q')
  assert(h === mu * q)

  -- let's construct the inverse of mu using the univ property of cokernels
  nu = cokernelMap(q', g)
  assert isWellDefined nu
  assert isIsomorphism nu
  assert(source nu === target h)
  assert(target nu === P)
  assert(nu * mu == 1)
  assert(mu * nu == 1)
  assert(nu * pD === q')
  assert(nu * h === q)
///

TEST ///
  -- given phi : B --> C,
  -- construct the canonical isomorphism mu from image phi to
  --   C *_(C ++_B C) C
  -- TODO: construct the 
  R = ZZ/101[a..d]
  phi = random(R^2, R^{3:-1})
  imap = kernelMap cokernelMap phi -- image phi --> C
  assert(source imap == image phi)
  assert(target imap === target phi)
  S = fiberSum(phi, phi)
  (q, q') = fiberSumMap S
  P = fiberProduct(q, q')
  assert(q * imap === q' * imap)
  mu = fiberProductMap(P, imap, imap)
  assert(source mu === source imap)
  assert(target mu === P)
  assert isIsomorphism mu -- Exercise: show that this is an isomorphism (probably is true...!)

  jmap = cokernelMap kernelMap phi -- B --> coimage phi
  assert(source jmap == source phi)
  assert(target jmap === coimage phi)
  P = fiberProduct(phi, phi)
  (p, p') = fiberProductMap P
  S = fiberSum(p, p')
  assert(jmap * p === jmap * p')
  mu = fiberSumMap(S, jmap, jmap) -- isom S --> coimage phi
  assert(source mu === S)
  assert(target mu === target jmap)
  assert isIsomorphism mu
///

-*
  restart
  needsPackage "CanonicalMaps"
*-
TEST ///
  -- super, superMap, cosuper, cosuperMap, cover, coverMap
  a = matrix{{6,0,0},{0,3,0},{0,0,0},{0,0,0}}
  b = matrix{{12,0,0},{0,3,0},{0,0,2},{0,0,0}}
  M = subquotient(a,b)
  assert(super M == coker relations M) -- or === should work too
  f = superMap M
  assert(source f === M)
  assert(target f === super M)
  assert(ker f == 0)
  g = cosuperMap M
  assert(source g === cosuper M)
  assert(target g === M)
  assert(coker g == 0)
  assert(cosuper M === image generators M) -- or === should work too
  h = coverMap M
  assert(cover M === source generators M)
  assert(source h === cover M)
  assert(target h === M)
  assert(coker h == 0)

  f === superMap M
  j = map(M, ZZ^1, transpose matrix{{1,0,1}})
  assert(super j === (superMap target j) * j)

  h === coverMap M
  j = map(M, ZZ^1, transpose matrix{{1,0,1}})
  assert(cover j === matrix j)
  assert(coverMap M * cover j === j)


  
  
  -- testing module with no relations
  M = image a
    
  assert(super M == coker relations M) -- or === should work too
  f = superMap M
  assert(source f === M)
  assert(target f === super M)
  assert(ker f == 0)
  g = cosuperMap M
  assert(source g === cosuper M)
  assert(target g === M)
  assert(coker g == 0)
  assert(cosuper M === image generators M) -- or === should work too
  h = coverMap M
  assert(cover M === source generators M)
  assert(source h === cover M)
  assert(target h === M)
  assert(coker h == 0)

  -- testing module with generators matrix not present (cokernels)
  M = coker b
    
  assert(super M == coker relations M) -- or === should work too
  f = superMap M
  assert(source f === M)
  assert(target f === super M)
  assert(ker f == 0)
  g = cosuperMap M
  assert(source g === cosuper M)
  assert(target g === M)
  assert(coker g == 0)
  assert(cosuper M === image generators M) -- or === should work too
  h = coverMap M
  assert(cover M === source generators M)
  assert(source h === cover M)
  assert(target h === M)
  assert(coker h == 0)

  -- testing free modules
  M = ZZ^7
  assert(super M == coker relations M) -- or === should work too
  f = superMap M
  assert(source f === M)
  assert(target f === super M)
  assert(ker f == 0)
  g = cosuperMap M
  assert(source g === cosuper M)
  assert(target g === M)
  assert(coker g == 0)
  assert(cosuper M === image generators M) -- or === should work too
  h = coverMap M
  assert(cover M === source generators M)
  assert(source h === cover M)
  assert(target h === M)
  assert(coker h == 0)

  f === superMap M
  j = map(M, ZZ^1, transpose matrix{{1,0,1,2,3,4,5}})
  assert(super j === (superMap target j) * j)

  h === coverMap M
  assert(cover j === matrix j)
  assert(coverMap M * cover j === j)
///

TEST ///
  R = ZZ/101[x,y,z]
  a = matrix{{x^3, x*z, y^2, y*z^2}}
  b = matrix{{x^3, y^3}}

  M = subquotient(a,b)
  prune M
  assert(super M === coker relations M) -- or === should work too
  f = superMap M
  assert(source f === M)
  assert(target f === super M)
  assert(ker f == 0)
  g = cosuperMap M
  assert(source g === cosuper M)
  assert(target g === M)
  assert(coker g == 0)
  assert(cosuper M === image generators M) -- or === should work too
  h = coverMap M
  assert(cover M === source generators M)
  assert(source h === cover M)
  assert(target h === M)
  assert(coker h == 0)

  f === superMap M
  j = map(M, R^1, transpose matrix{{x,y,z,x-y}})
  assert(super j === (superMap target j) * j)

  h === coverMap M
  assert(cover j === matrix j)
  assert(coverMap M * cover j === j)
  
  -- testing module with no relations
  M = image a
    
  assert(super M == coker relations M) -- or === should work too
  f = superMap M
  assert(source f === M)
  assert(target f === super M)
  assert(ker f == 0)
  g = cosuperMap M
  assert(source g === cosuper M)
  assert(target g === M)
  assert(coker g == 0)
  assert(cosuper M === image generators M) -- or === should work too
  h = coverMap M
  assert(cover M === source generators M)
  assert(source h === cover M)
  assert(target h === M)
  assert(coker h == 0)

  -- testing module with generators matrix not present (cokernels)
  M = coker b
    
  assert(super M == coker relations M) -- or === should work too
  f = superMap M
  assert(source f === M)
  assert(target f === super M)
  assert(ker f == 0)
  g = cosuperMap M
  assert(source g === cosuper M)
  assert(target g === M)
  assert(coker g == 0)
  assert(cosuper M === image generators M) -- or === should work too
  h = coverMap M
  assert(cover M === source generators M)
  assert(source h === cover M)
  assert(target h === M)
  assert(coker h == 0)
///

-*
  restart
  needsPackage "CanonicalMaps"
*-
TEST ///
  a = matrix{{6,0,0},{0,3,0},{0,0,0},{0,0,0}}
  b = matrix{{12,0,0},{0,3,0},{0,0,2},{0,0,0}}
  M = subquotient(a,b)
  prune M
  phi = pruneMap M
  assert(source phi === M)
  assert(target phi === prune M)
  assert(kernel phi == 0 and cokernel phi == 0)
  assert((prune M).cache.pruningMap^-1 === phi)
  assert(phi^-1 === (prune M).cache.pruningMap)

  R = ZZ/101[x,y,z]
  a = matrix{{x^3, x*z, y^2, y*z^2}}
  b = matrix{{x^3, y^3, x^4, y^4}}
  M = subquotient(a,b)

  prune M
  phi = pruneMap M
  assert(source phi === M)
  assert(target phi === prune M)
  assert(kernel phi == 0 and cokernel phi == 0)
  assert((prune M).cache.pruningMap^-1 === phi)
  assert(phi^-1 === (prune M).cache.pruningMap)

  M = R^{-1,2,3}
  phi = pruneMap M
  assert(source phi === M)
  assert(target phi === prune M)
  assert(kernel phi == 0 and cokernel phi == 0)
  assert((prune M).cache.pruningMap^-1 === phi)
  assert(phi^-1 === (prune M).cache.pruningMap)
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
