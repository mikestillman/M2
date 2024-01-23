-- This file contains functions implementing the category of 
-- f.g. modules over a ring R, and R-linear maps between them

-- each module M comes equipped with generators (a map F --> M, where F is a free module).
-- Recall that all modules in Macaulay2 come with a (ordered) generating set.
-- The generating set for a free module are the standard basis vectors.
-- A map between two is given by a matrix between the two generating set free modules.

-- TODO:
--  0. Include this a a file when loading Complexes?
--  1. get kernelMap, cokernelMap working over complexes.
--  2. remove use of 'quotient'?
--  3. perhaps remove 'injectModule'
--  4. images, coimages, natural maps and universal properties
--  5. fiberSum, fiberProduct

needsPackage "Complexes"

-- need: how to take a matrix, and make it a complex map?
injectModule = method()
injectModule Module := Complex => M -> complex M
injectModule Matrix := ComplexMap => f -> (
    C := injectModule source f;
    D := injectModule target f;
    map(D, C, i -> if i === 0 then f else map(D_i, C_i, 0))
    )

randomMatrix = method()
randomMatrix(Module, Module) := Matrix => (N, M) -> (
    g := randomComplexMap(complex N, complex M);
    g_0
    )

kernelMap = method()
kernelMap Matrix := Matrix => (f) -> (
    C := injectModule source f;
    g := injectModule f;
    kerg := ker g;
    eta := inducedMap(C, kerg);
    eta_0
    )
kernelMap ComplexMap := ComplexMap => (f) -> inducedMap(source f, ker f)

kernelMap(Matrix, Matrix) := Matrix => (g, f) -> (
    -- f : B --> C
    -- g : A --> B
    -- kermap f: ker f --> B
    -- result should be A --> ker f.
    -- assume f*g = 0.
    -- returns ghat : A -> ker f s.t. (kermap f)*ghat == g
    if f*g != 0 then error "expected composite map to be zero";
    eta := kernelMap f;
    quotient(g, eta)
    )
kernelMap(ComplexMap, ComplexMap) := ComplexMap => (g, f) -> (
    -- f : B --> C
    -- g : A --> B
    -- kermap f: ker f --> B
    -- result should be A --> ker f.
    -- assume f*g = 0.
    -- returns ghat : A -> ker f s.t. (kermap f)*ghat == g
    if f*g != 0 then error "expected composite map to be zero";
    map(ker f, source g, i -> kernelMap(g_i, f_i))
    )

cokernelMap = method()
cokernelMap Matrix := Matrix => (f) -> (
    D := injectModule target f;
    g := injectModule f;
    cokerg := cokernel g;
    p := inducedMap(cokerg, D);
    p_0
    )
cokernelMap ComplexMap := ComplexMap => (f) -> inducedMap(cokernel f, target f)

cokernelMap(Matrix, Matrix) := Matrix => (g, f) -> (
    -- f : B --> C
    -- g : C --> A
    --  s.t. g*f = 0
    -- if p : C --> coker f is the cokernel map of f
    -- result should be coker f --> A.
    -- return the map ghat : coker f --> A s.t. ghat * p = g,
    if target f =!= source g then error "expected target of second map to be the same as source of the first map";
    if g*f != 0 then error "expected the composite map to be zero";
    p := cokernelMap f;
    map(target g, target p, matrix g)
    )
cokernelMap(ComplexMap, ComplexMap) := ComplexMap => (g, f) -> (
    -- f : B --> C
    -- g : C --> A
    -- returns a lift of g, ghat : coker f --> A
    --  s.t. g*f = 0
    if target f =!= source g then error "expected target of second map to be the same as source of the first map";
    if g*f != 0 then error "expected the composite map to be zero";
    -- if p : C --> coker f is the cokernel map of f
    -- result should be coker f --> A.
    -- return the map ghat : coker f --> A s.t. ghat * p = g,
    map(target g, coker f, i -> cokernelMap(g_i, f_i))
    )
    
coimageMap = method()
imageMap = method()
coimageToImage = method()
coimageToImageInverse = method() -- axiom of an Abelian category: coimageToImage f is an isomorphism
coimageMap Matrix := (f) -> cokernelMap kernelMap f
imageMap Matrix := (f) -> kernelMap cokernelMap f
coimageMap ComplexMap := (f) -> cokernelMap kernelMap f
imageMap ComplexMap := (f) -> kernelMap cokernelMap f
coimageToImage ComplexMap :=
coimageToImage Matrix := (f) -> (
    eta := kernelMap f; -- eta: ker f --> B
    p := cokernelMap f; -- p: C --> coker f
    theta' := cokernelMap eta; -- theta' : B --> coker eta == coim f
    theta := kernelMap(f, p); -- theta:  B --> ker p == im f
    mu := cokernelMap(theta, eta); -- coim f --> im f
    mu
    )
coimageToImageInverse ComplexMap :=
coimageToImageInverse Matrix := (f) -> (
    g := coimageToImage f;
    g^(-1) -- todo: for complexes, does this work?
    )

TEST ///
  restart
  needs "./Modules.m2"
  R = ZZ/101[a..d]
  I = ideal (a^2, b^2, c^2, d^2, a*b*c*d)
  J = ideal (a^3, b^3, c^3, d^3, a*b*c*d)
  M = module I
  N = module J
  f = inducedMap(M, N)
  M1 = M ++ comodule I
  N1 = N ++ comodule J
  f = randomMatrix(M1, N1)
  isWellDefined f
  prune ker f
  prune coker f

  eta = kernelMap f
  assert(source eta === ker f)
  assert(target eta === source f)
  assert(ker eta == 0)
  assert(f.cache.kernel === ker f) -- make sure value is acrtually cached

  p = cokernelMap f
  assert(source p === target f)
  assert(target p === coker f)
  assert(coker p == 0)
  assert(f.cache.cokernel === coker f) -- make sure value is acrtually cached

  eta2 = kernelMap(kernelMap f, f)
  isWellDefined eta2

  p2 = kernelMap(f, cokernelMap f)
  
  f = randomComplexMap(complex M1, complex N1, Cycle => true)
  assert isWellDefined f
  assert isComplexMorphism f
  g = f_0
  assert(source g === N1)
  assert(target g === M1)
  ker g
  eta = inducedMap(complex N1, ker f)
  eta0 = eta_0
  assert(source eta0 === ker g)
  assert(target eta0 === N1)
  
  -- kernelMap universal property
  R = ZZ/101[a..d]
  I = monomialCurveIdeal(R, {1,3,4})
  C = freeResolution I
  D = dual C
  f = D.dd_-2
  g = D.dd_-1
  ghat = kernelMap(g, f)
  -- check the kernel map result (for modules, not complexes) 
  assert(target ghat === ker f)
  assert(source ghat === source g)
  assert(g === (kernelMap f) * ghat)

  D = Hom(C, R^1/I)
  f = D.dd_-2
  g = D.dd_-1
  ghat = kernelMap(g, f)
  -- check the kernel map result (for modules, not complexes)
  assert(target ghat === ker f)
  assert(source ghat === source g)
  assert(g == (kernelMap f) * ghat)

  D = Hom(C, R^1/I_0 ++ R^1/I_1)
  f = D.dd_-2
  g = D.dd_-1
  ghat = kernelMap(g, f)
  -- check the kernel map result (for modules, not complexes)
  assert(target ghat === ker f)
  assert(source ghat === source g)
  assert(g === (kernelMap f) * ghat)

  -- cokermap universal property (for modules)
  R = ZZ/101[a..d]
  I = monomialCurveIdeal(R, {1,3,4})
  C = freeResolution I
  D = dual C
  f = D.dd_-1
  g = D.dd_-2
  g * f == 0
  cokernel f
  cokernelMap f
  ghat = cokernelMap(g, f)
  -- check the cokernel map result (for modules, not complexes)
  assert(target ghat === target g)
  assert(source ghat === cokernel f)
  assert(g === ghat * cokernelMap f)

  D = Hom(C, R^1/I_0 ++ R^1/I_1)
  f = D.dd_-1
  g = D.dd_-2
  g * f == 0
  cokernel f
  cokernelMap f
  ghat = cokernelMap(g, f)
  -- check the cokernel map result (for modules, not complexes)
  assert(target ghat === target g)
  assert(source ghat === cokernel f)
  assert(g === ghat * cokernelMap f)
  ///

TEST ///
-*
  restart
  needs "./Modules.m2"
*-
  -- testing ker and coker universal maps, for complexes
  S = ZZ/11[x,y,z];
  K2 = koszulComplex matrix{{x,y}}
  K3 = koszulComplex matrix{{x,y,z}}
  psi = randomComplexMap(K3,K2, Cycle => true, InternalDegree => 1)
  assert isComplexMorphism psi
  ker psi == 0 -- this map is a monmorphism

  eta = kernelMap psi -- 0 map
  cokernelMap eta === id_(source psi) -- false... why?
  assert(cokernelMap eta == id_(source psi)) -- true

  p = cokernelMap psi
  source imageMap psi == image psi -- but not ===, why?
  target coimageMap psi == coimage psi -- but not ===, why?
  image psi  
  coimage psi
  imageMap psi
  coimageMap psi
  coimageToImage psi * coimageToImageInverse psi === id_(coimage psi)
  g = coimageToImage psi
  h = coimageToImageInverse psi
  g*h === id_(image g) -- this is false
  g*h == id_(image g) -- this is true

-- an example which is not injective nor surjective
  S = ZZ/11[x,y,z];
  K2 = koszulComplex matrix{{x,y}}
  K3 = koszulComplex matrix{{x,y,z}}
  f1 = randomComplexMap(K3,K2, Cycle => true, InternalDegree => 1)
  f2 = randomComplexMap(K2, K3, Cycle => true, InternalDegree => 1)
  g = f1*f2
  isWellDefined g
  source g === K3
  target g === K3
  degree g_0 == {2} -- degrees are inside the maps
  assert isComplexMorphism g
  eta = kernelMap g
  assert(ker eta == 0)
  p = cokernelMap g
  assert(coker p == 0)
  kernelMap p
  mu = coimageToImage g
  mu1 = coimageToImageInverse g
  assert(mu * mu1 == 1)
  assert(mu1 * mu == 1)
  assert(mu^(-1) == mu1)
///

TEST ///
-*
  restart
  needs "./Modules.m2"
*-
  -- coimage to image map for complexes
  S = ZZ/11[x,y,z];
  K2 = koszulComplex matrix{{x,y}}
  K3 = koszulComplex matrix{{x,y,z}}
  psi = randomComplexMap(K3,K2, Cycle => true, InternalDegree => 1)
  assert isComplexMorphism psi
  ker psi == 0 -- this map is a monmorphism
  
  source imageMap psi == image psi -- but not ===, why?
  target coimageMap psi == coimage psi -- but not ===, why?
  image psi  
  coimage psi
  imageMap psi
  coimageMap psi
  coimageToImage psi * coimageToImageInverse psi === id_(coimage psi)
  g = coimageToImage psi
  h = coimageToImageInverse psi
  g*h === id_(image g) -- this is false, why?
  assert(g*h == id_(image g)) -- this is true
///

TEST ///
  -- images and coimages
  -- and the 2 universal properties (or is it 4?)

  R = ZZ/101[a..d]
  I = monomialCurveIdeal(R, {1,3,4})
  C = freeResolution I
  D = dual C
  f = D.dd_-1
  g = D.dd_-2
  image f
  cokernelMap kernelMap f
  kernelMap cokernelMap f
  image f
  coimage f
  imf = imageMap f
  target imf === target f
  coimf = coimageMap f
  image f 
  target coimf
  coimageToImage f
  coimageToImageInverse f

    eta = kernelMap f; -- eta: ker f --> B
      source eta === ker f
      target eta === source f
    p = cokernelMap f; -- p: C --> coker f
      source p === target f
      target p === cokernel f
      f * eta == 0
      p * f == 0
    theta' = cokernelMap eta; -- theta' : B --> coker eta
      source theta' === source f
      target theta' === coker eta
    theta = kernelMap(f, p); -- theta:  target p --> target f
      source theta === source f
      target theta === kernel p
    mu = cokernelMap(theta, eta)
      source mu === coker eta
      target mu === target theta
      source mu == prune image f
      target mu 

  -- want the induced maps (given f : B --> C)
  -- First we have these two:
  -- p : C --> coker f, p = cokernelMap f
  -- eta : ker f --> B, eta = kernelMap f
  -- kernelMap p : image f --> C
  -- cokernelMap eta : B --> 
  eta = kernelMap f
    assert(target eta === source f)
    assert(source eta == ker f)
  p = cokernelMap f
    assert(source p === target f)
    assert(target p === coker f)
  rho = kernelMap p
    assert(source rho === ker p)
    assert(target rho === target f)
  theta' = cokernelMap eta
    assert(source theta' === source f)
    assert(target theta' === coker eta)

  theta = kernelMap(f, p)
    assert(source theta === source f)
    assert(target theta === kernel p)
    assert(rho * theta == f)
  rho' = cokernelMap(f, eta) -- seems ok
    assert(f * eta == 0) -- so this lifting should be ok
    assert(source rho' === target theta')
    assert(target rho' === target f)
    assert(rho' * theta' == f)
  mu = kernelMap(rho', p)
    source mu === target theta'
    target mu === kernel p
    isIsomorphism mu -- this is a natural isomorphism
    -- BUT: in an arbitrary category with Ker, Coker's, this is not always an isom.
    -- Hence it is an axiom: we must be given this isomorphism.
    -- It is easy to compute/invert for modules, complexes.

  coimf = target theta'
  imf = target theta
  
  ///

TEST ///
  -- Exercise:
  -- Given a R-linear map (of modules or complexes)
  -- f : B --> C,
  -- suppose that ker f = 0, coker f = 0.  We know that then f is an isomorphism.
  -- Find the (unique) inverse map g : C --> B.
  -- Use kernelMap, cokernelMap functions to find g.
///

TEST ///
  -- Exercise:
  -- Given a R-linear maps f : B --> C, f' : B' --> C.
  --   write a function which implements the fiberProduct (one function which constructs it, 
  --   one function which gives the 2 augmented maps, and one function which implements the
  --   universal property.

  -- Do the same for the fiber sum of R-linear maps f : A --> B, f; : A --> B':
  --   write a function which implements the fiberSum (one function which constructs it, 
  --   one function which gives the 2 augmented maps, and one function which implements the
  --   universal property.


  -- f : B --> C,
  -- suppose that ker f = 0, coker f = 0.  We know that then f is an isomorphism.
  -- Find the (unique) inverse map g : C --> B.
  -- Use kernelMap, cokernelMap functions to find g.
///

TEST ///
  -- Exercise:
  --  Write the following function(s):
  --  Given a R-map or R-complex map, f : B --> C
  -- (a) implement the imageMap universal property.
  -- (b) implement the coimageMap universal property.
  -- (c) get the isomorphism from coimage f --> image f (and vice versa).
///
