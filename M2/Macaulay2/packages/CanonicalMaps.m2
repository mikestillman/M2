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
    "pruneMap",
    "unitorMap",
    "counitorMap",
    "tensorCommutativity", -- needs tests
    -- "tensorAssociativity" is currently in Core: modules2.m2, needs tests
    "swapMap",
    "adjunctionMap"
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

-- trimMap M : M --> trim M (basically the identity on generators)
--  (trimMap M)^-1 : trim M --> M (what about for ideals?)
trimMap = method(Options => options trim)
trimMap Module := opts -> M -> (
    M' := trim(M, opts);
    f := (gens M) // ((gens M') | (relations M'));
    map(M', M, f^{0..numcols gens M' - 1})
    )

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

unitorMap = method()
unitorMap Module := Matrix => M -> map(M, (ring M)^1 ** M, 1)

counitorMap = method(Options => options Hom)
counitorMap Module := Matrix => opts -> M -> (
    if opts.DegreeLimit =!= null then error "no counitor map defined for truncated Hom's";
    if opts.MinimalGenerators then
        trimMap M
    else
        id_M
    )

tensorCommutativity = method()
tensorCommutativity(Module, Module) := Matrix => (M,N) -> (
    -- implement the isomorphism M ** N --> N ** M
    MN := M ** N;
    NM := N ** M;
    m := numgens source gens M;
    n := numgens source gens N;
    perm := flatten for i from 0 to m - 1 list
      for j from 0 to n - 1 list (
          -- (i,j) (in M**N) to m*i + j
          -- map to column (j,i) <--> n*j + i
          m*j+i
          );
    FMN := source gens MN;
    f := ((id)_FMN)_perm;
    map(NM, MN, f)
    )


swapMap = method()
-- swap map Hom_R(A, Hom_R(B, C)) --> Hom_R(B, Hom_R(A, C))
-- where R is commutative and A, B, C are R-modules
swapMap(Module, Module, Module) := Matrix => (A, B, C) -> (
    BC := Hom(B, C);
    AC := Hom(A, C);
    ABC := Hom(A, BC);
    BAC := Hom(B, AC);
    -- want ABC --> BAC
    perm := tensorCommutativity(dual cover A, dual cover B) ** cover C;
    permLift := (perm * gens ABC) //  gens BAC;
    map(BAC, ABC, permLift)
    )

adjunctionMap = method()
-- adjunction: Hom_R(A ** B, C) --> Hom_R(B, Hom_R(A, C))
-- where R is commutative and A, B, C are R-modules
adjunctionMap(Module, Module, Module) := Matrix => (A, B, C) -> (
    )

checkSwapMap = method()
checkSwapMap(Matrix, Module, Module) := Boolean => (sw, A, B) -> (
    -- sw := swapMap(A, B, C);
    -- checks that this is the canonical isomorphism
    -- from Hom(A, Hom(B,C)) --> Hom(B, Hom(A,C))
    -- We check the following, for all psi, a, b generators of their respective modules.
    -- psi : A --> Hom(B, C)
    -- a in A, b in B
    -- sw = swapMap(A,B,C) : Hom(A, Hom(B,C)) --> Hom(B, Hom(A,C))
    -- psi(a) : B --> C
    -- sw(psi) : B --> Hom(A,C), (sw(psi)(b))(a) == (psi(a))(b)
    ABC := source sw;
    BAC := target sw;
    all(numgens ABC, abc -> (
        all(numgens A, a -> (
            all(numgens B, b -> (
                psi := homomorphism ABC_{abc};
                f1 := psi * A_{a};
                f2 := homomorphism f1;
                f3 := B_{b}; -- so val1 is f2 * f3
                val1 := (homomorphism(psi * A_{a})) * B_{b};
                g1 := sw * ABC_{abc};
                g2 := homomorphism g1;
                g3 := g2 * B_{b};
                g4 := homomorphism g3;
                g5 := A_{a}; -- so val2 is g4 * g5.
                val2 := (homomorphism(homomorphism(sw * ABC_{abc}) * B_{b})) * A_{a};
                val2 := ((homomorphism(sw * ABC_{abc}) * B_{b})) * A_{a};
                result := (val1 == val2);
                if debugLevel > 0 and not result then (
                    << "swap map failed: abc=" << abc << " a=" << a << " b=" << b << endl;
                    << "  val1 = " << val1 << endl;
                    << "  val2 = " << val2 << endl;
                    error "debug me";
                    );
                result
    )))))))

-*
  restart
  needsPackage "CanonicalMaps"
*-
TEST ///
  debug needsPackage "CanonicalMaps"
  C = ZZ^3 ++ ZZ^1/ideal(32)
  B = ZZ^2 ++ ZZ^1/ideal(16)
  A = ZZ^1/ideal(8) ++ ZZ^1/ideal(4) ++ ZZ^2
  debugLevel = 1
  sw = swapMap(A, B, C)
  assert isWellDefined sw
  assert isHomogeneous sw
  assert(ker sw == 0)
  assert(coker sw == 0)
  -- note: this doesn't show that we have the correct map yet!
  assert checkSwapMap(sw, A, B)

  R = ZZ/101[a..d]
  A = R^{0,1,2,3}
  B = R^{0,10,20}
  C = R^{0,100,200,300,400}
  sw = swapMap(A, B, C)
  assert isWellDefined sw
  assert isHomogeneous sw
  assert(ker sw == 0)
  assert(coker sw == 0)
  -- note: this doesn't show that we have the correct map yet!
  debugLevel = 1
  assert checkSwapMap(sw, A, B)

  BC = Hom(B, C)
  AC = Hom(A, C)
  ABC = Hom(A, BC)
  BAC = Hom(B, AC)
  gens ABC
  gens BAC

  phi1 = map(BAC, ABC, 1)
  isWellDefined phi1
  isHomogeneous phi1 -- false
  ker phi1 == 0
  coker phi1 == 0
  
  perm = tensorCommutativity(dual cover A, dual cover B) ** cover C
  permLift = (perm * gens ABC) //  gens BAC
  phi = map(BAC, ABC, permLift)
  isHomogeneous phi


  target gens ABC
  target gens BAC
  permAB = tensorCommutativity(dual cover A, dual cover B)
  permABC = (permAB) ** (cover C)
  netList{degrees source permABC, degrees target gens ABC}
  degrees source permABC === degrees target gens ABC -- true
  source permABC === target gens ABC
  target permABC === target gens BAC
  phi = map(BAC, ABC, permABC)
  isWellDefined phi
  ker phi == 0
  coker phi == 0
  isHomogeneous phi

  
  /// 
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
  assert isWellDefined phi
  assert(source phi === M)
  assert(target phi === prune M)
  assert(kernel phi == 0 and cokernel phi == 0)
  assert((prune M).cache.pruningMap^-1 === phi)
  assert(phi^-1 === (prune M).cache.pruningMap)

  phi = trimMap M
  assert isWellDefined phi
  assert(source phi === M)
  assert(target phi === trim M)
  assert(kernel phi == 0 and cokernel phi == 0)

  R = ZZ/101[x,y,z]
  a = matrix{{x^3, x*z, y^2, y*z^2}}
  b = matrix{{x^3, y^3, x^4, y^4}}
  M = subquotient(a,b)

  prune M
  phi = pruneMap M
  assert isWellDefined phi
  assert(source phi === M)
  assert(target phi === prune M)
  assert(kernel phi == 0 and cokernel phi == 0)
  assert((prune M).cache.pruningMap^-1 === phi)
  assert(phi^-1 === (prune M).cache.pruningMap)

  phi = trimMap M
  assert isWellDefined phi
  assert(source phi === M)
  assert(target phi === trim M)
  assert(kernel phi == 0 and cokernel phi == 0)
  
  M = R^{-1,2,3}
  phi = pruneMap M
  assert isWellDefined phi
  assert(source phi === M)
  assert(target phi === prune M)
  assert(kernel phi == 0 and cokernel phi == 0)
  assert((prune M).cache.pruningMap^-1 === phi)
  assert(phi^-1 === (prune M).cache.pruningMap)

  phi = trimMap M
  assert isWellDefined phi
  assert(source phi === M)
  assert(target phi === trim M)
  assert(kernel phi == 0 and cokernel phi == 0)
///


-*
  restart
  needsPackage "CanonicalMaps"
*-
TEST /// -- unitor
  M = coker matrix{{3,0,0},{2,1,0},{0,0,0}}
  f = unitorMap M
  assert isWellDefined f
  assert(source f === (ring M)^1 ** M)
  assert(target f === M)
  assert(ker f == 0)
  assert(coker f == 0)
  assert(f == 1)

  g = counitorMap M
  assert isWellDefined g
  assert(source g === M)
  assert(target g === Hom((ring M)^1, M))
  assert(ker g == 0)
  assert(coker g == 0)

  M = prune coker matrix{{3,0,0},{2,1,0},{0,0,0}}
  f = unitorMap M
  assert(f == 1)
  assert isWellDefined f
  assert(ker f == 0)
  assert(coker f == 0)

  R = ZZ/101[x,y,z]/(x^2, y^2, z^2)
  M = module ideal(x*y, x*z-y*z)
  f = unitorMap M
  assert isWellDefined f
  assert(source f === (ring M)^1 ** M)
  assert(target f === M)
  assert(ker f == 0)
  assert(coker f == 0)
  assert(f == 1)

  g = counitorMap M
  assert isWellDefined g
  assert(source g === M)
  assert(target g === Hom((ring M)^1, M))
  assert(ker g == 0)
  assert(coker g == 0)

  R = ZZ/101[x,y,z]/(x^2, y^2, z^2)
  M = module ideal(x*y, x*z-y*z) ++ R^1/(x*y*z)
  f = unitorMap M
  assert isWellDefined f
  assert(source f === (ring M)^1 ** M)
  assert(target f === M)
  assert(ker f == 0)
  assert(coker f == 0)
  assert(f == 1)

  g = counitorMap M
  assert isWellDefined g
  assert(source g === M)
  assert(target g === Hom((ring M)^1, M))
  assert(ker g == 0)
  assert(coker g == 0)

  R = ZZ/101[x,y,z]
  M = module ideal(x^2, y^5, z^10, z^9)
  g = counitorMap(M, MinimalGenerators => false)
  assert isWellDefined g
  assert(source g === M)
  assert(target g === Hom((ring M)^1, M, MinimalGenerators => false))
  assert(ker g == 0)
  assert(coker g == 0)
///

TEST ///
  -- BUG, git issue #
  R = ZZ/101[x,y,z]
  M = subquotient(matrix{{x^2, x^2-y^2, y^2}}, matrix{{x^3-y^3, y^3 - x^3}})
  M' = trim M
  f = (gens M) // ((gens M') | (relations M'))
  g = map(M', M, f^{0..numcols gens M' - 1})

  assert(ker g == 0)
  assert(coker g == 0)
  assert isWellDefined g

  f' = (gens M') // ((gens M) | (relations M))
  g' = map(M, M', f'^{0..numcols gens M - 1})

  assert(ker g' == 0)
  assert(coker g' == 0)
  assert isWellDefined g'

  assert(g * g' == 1) -- so g, g' are inverses of each other.
  assert(g' * g == 1)
  
  assert(g' == g^(-1)) -- FAILS: Macaulay2/m2/matrix.m2:110:20-119:5 has an incorrect check: raw f === raw g.
  assert(g'^(-1) == g) -- ok 
  
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
