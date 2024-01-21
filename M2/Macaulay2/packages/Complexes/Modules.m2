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
    p := cokernelMap f;
    map(target g, target p, matrix g)
    )
cokernelMap(ComplexMap, ComplexMap) := ComplexMap => (g, f) -> (
    -- f : B --> C
    -- g : C --> A
    --  s.t. g*f = 0
    -- if p : C --> coker f is the cokernel map of f
    -- result should be coker f --> A.
    -- return the map ghat : coker f --> A s.t. ghat * p = g,
    map(coker f, target g, i -> cokernelMap(g_i, f_i))
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

  p2 = cokernelMap(f, cokernelMap f)
  
  f = randomComplexMap(complex M1, complex N1)
  isWellDefined f
  g = f_0
  source g === N1
  target g === M1
  ker g
  eta = inducedMap(complex N1, ker f)
  eta0 = eta_0
  source eta0 === ker g  
  target eta0 === N1
  
  -- kernelMap universal property
  R = ZZ/101[a..d]
  I = monomialCurveIdeal(R, {1,3,4})
  C = freeResolution I
  D = dual C
  f = D.dd_-2
  g = D.dd_-1
  ghat = kernelMap(g, f)
  assert(target ghat == ker f)
  assert(source ghat == source g)
  degrees source ghat, degrees source g
  g == (kernelMap f) * ghat

  D = Hom(C, R^1/I)
  f = D.dd_-2
  g = D.dd_-1
  ghat = kernelMap(g, f)
  assert(target ghat == ker f)
  assert(source ghat == source g)
  g == (kernelMap f) * ghat

  D = Hom(C, R^1/I_0 ++ R^1/I_1)
  f = D.dd_-2
  g = D.dd_-1
  ghat = kernelMap(g, f)
  assert(target ghat == ker f)
  assert(source ghat == source g)
  g == (kernelMap f) * ghat
  
  -- cokermap universal property
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
  assert(target ghat == target g)
  assert(source ghat == cokernel f)
  assert(g == ghat * cokernelMap f)

  D = Hom(C, R^1/I_0 ++ R^1/I_1)
  f = D.dd_-1
  g = D.dd_-2
  g * f == 0
  cokernel f
  cokernelMap f
  ghat = cokernelMap(g, f)
  assert(target ghat == target g)
  assert(source ghat == cokernel f)
  assert(g == ghat * cokernelMap f)
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
  -- want the induced maps (given f : B --> C)
  -- Firat we have these two:
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
