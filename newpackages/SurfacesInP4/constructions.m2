-- Construction of smooth surfaces in P4 not of general type.
-- This set consists of the ones which are vanishing ideals
-- of 2 standard sheaves (direct sums of OO, OO(-1), omega(R, 1), omega(R, 2))
///
-*
  restart
  needsPackage "SurfacesInP4"
*-
  -- rat.d4.g0.veronese
  kk = QQ
  R = kk[x_1..x_5]
  
  -- method 1
  time IX = randomVanishingIdeal(omega(R,1), R^{-1,-1,-1});
  fIX = res coker gens IX
  betti fIX
  surfaceInvariants IX

  -- method 2
  time f = randomMap(omega(R,1), R^{-1,-1,-1})
  IX = trim ideal syz transpose presentation coker f
  betti res IX
  

  -- method 3
  needsPackage "BGG"
  E = kk[e_1..e_5, SkewCommutative => true]
  a1 = random(E^{-1}, E^{-4}^3)
  f1 = beilinson(a1, R)
  IX = trim ideal syz transpose presentation coker f1
  betti res IX
///

///
-*
  restart
  needsPackage "SurfacesInP4"
*-
  -- rat.d5.g2.castelnuovo
  R = QQ[x_1..x_5]
  time IX = randomVanishingIdeal(R^{1,0,0}, R^{-1,-1});
  fIX = res coker gens IX
  betti fIX
  surfaceInvariants IX

  -- method 2  
  IX = randomVanishingIdeal(R^{1} ++ R^2, (omega(R,4))^2)
  betti res IX
///

///
-*
  restart
  needsPackage "SurfacesInP4"
*-
  -- I believe this is a ruled.d5.g1.elliptic-scroll
  R = ZZ/32003[x_1..x_5]
  F = R^{5:-1}
  G = omega(R,2)
  time IX = randomVanishingIdeal(G, F);
  fIX = res coker gens IX
  betti fIX
  elapsedTime surfaceInvariants IX 
  
  surfacesInP4(Degree => 5, Genus => 1, Type => "ruled")
  I' = example first oo
  assert(betti res I' == betti fIX)

  -- method 2
  time f = randomMap(G, F)
  IX = trim ideal syz transpose presentation coker f
  betti res IX

  -- method 3
  needsPackage "BGG"
  E = kk[e_1..e_5, SkewCommutative => true]
  a1 = random(E^{-2}, E^{-4}^5)
  f1 = beilinson(a1, R)
  IX = trim ideal syz transpose presentation coker f1
  betti res IX
///

///
-*
  restart
  needsPackage "SurfacesInP4"
*-
  -- rat.d6.g3.bordiga
  R = QQ[x_1..x_5]
  time IX = randomVanishingIdeal(R^4, R^{-1,-1,-1});
  fIX = res coker gens IX
  betti fIX
  surfaceInvariants IX
///

///
-*
  restart
  needsPackage "SurfacesInP4"
*-
-- rat.d7.g4
  R = QQ[x_1..x_5]
  time IX = randomVanishingIdeal(omega(R,1) ++ R^1, R^{-1,-1,-1,-1});
  fIX = res coker gens IX
  betti fIX
  surfaceInvariants IX
  
  surfacesInP4(Degree => 7, Genus => 4)
  I' = example first oo
  assert(betti res I' == betti fIX)
///

///
-*
  restart
  needsPackage "SurfacesInP4"
*-
-- k3.d7.g5
  R = QQ[x_1..x_5]
  time IX = randomVanishingIdeal(R^3, R^{-1,-2});
  fIX = res coker gens IX
  betti fIX
  surfaceInvariants IX

  surfacesInP4(Degree => 7, Genus => 5)
  I' = example first oo
  betti res I' == betti fIX
///

///
-*
  restart
  needsPackage "SurfacesInP4"
*-
  -- ell.d7.g6
  R = ZZ/32003[x_1..x_5]
  IX = minors(2, random(R^{-2,-4,-4}, R^{-5,-5}));
  -- or: IX = randomVanishingIdeal(R^{-2,-4,-4}, R^{-5,-5})
  -- or the usual way:
  -- F = R^{-5,-5}
  -- G = R^{-2,-4,-4}
  -- time IX = randomVanishingIdeal(G, F);
  fIX = res coker gens IX
  betti fIX
  elapsedTime surfaceInvariants IX 
  
  surfacesInP4(Degree => 7, Genus => 6)
  I' = example first oo
  betti res I' == betti fIX
///

///
-*
  restart
  needsPackage "SurfacesInP4"
*-
-- rat.d8.g5
  R = ZZ/32003[x_1..x_5]
  time IX = randomVanishingIdeal((omega(R,1))^2 ++ R^5, (omega(R,2))^2);
  fIX = res coker gens IX
  betti fIX
  elapsedTime surfaceInvariants IX -- takes 22 sec over QQ, .5 sec over ZZ/32003
///

///
-*
  restart
  needsPackage "SurfacesInP4"
*-
  -- I believe this is a rat.d8.g6
  R = ZZ/32003[x_1..x_5]
  F = (omega(R,3))
  G = R^{1, 0, 0, 0, 0}
  
  time IX = randomVanishingIdeal(G, F);
  fIX = res coker gens IX
  betti fIX
  elapsedTime surfaceInvariants IX 
  
  surfacesInP4(Degree => 8, Genus => 6, Type => "rat")
  I' = example first oo
  assert(betti res I' == betti fIX)
///

///
-*
  restart
  needsPackage "SurfacesInP4"
*-
  -- I believe this is a k3.d8.g6
  R = ZZ/32003[x_1..x_5]
  F = R^{-2,-1,-1}
  G = omega(R,1)
  time IX = randomVanishingIdeal(G, F);
  fIX = res coker gens IX
  betti fIX
  elapsedTime surfaceInvariants IX 
  
  surfacesInP4(Degree => 8, Genus => 6, Type => "k3")
  I' = example first oo
  assert(betti res I' == betti fIX)
///

///
-*
  restart
  needsPackage "SurfacesInP4"
*-
  -- ell.d8.g7
  R = ZZ/32003[x_1..x_5]
  IX = minors(2, random(R^{-3,-3,-4}, R^{-5,-5}));
  -- or the usual way:
  -- F = R^{-5,-5}
  -- G = R^{-2,-4,-4}
  -- time IX = randomVanishingIdeal(G, F);
  fIX = res coker gens IX
  betti fIX
  elapsedTime surfaceInvariants IX 
  
  surfacesInP4(Degree => 8, Genus => 7)
  I' = example first oo
  assert(betti res I' == betti fIX)
///

///
-*
  restart
  needsPackage "SurfacesInP4"
*-
  -- I believe this is a k3.d9.g8
  R = ZZ/32003[x_1..x_5]
  F = R^{-1} ++ omega(R,3)
  G = R^6
  time IX = randomVanishingIdeal(G, F);
  fIX = res coker gens IX
  betti fIX
  elapsedTime surfaceInvariants IX 
  
  surfacesInP4(Degree => 9, Genus => 8, Type => "k3")
  I' = example first oo
  assert(betti res I' == betti fIX)
///

///
-*
  restart
  needsPackage "SurfacesInP4"
*-
  -- I believe this is a rat.d9.g7
  R = ZZ/32003[x_1..x_5]
  F = (omega(R,1))^2 ++ R^3
  G = omega(R,2) ++ omega(R,3)
  time IX = randomVanishingIdeal(F, G);
  fIX = res coker gens IX
  betti fIX
  elapsedTime surfaceInvariants IX 
  
  surfacesInP4(Degree => 9, Genus => 7, Type => "rat")
  I' = example first oo
  assert(betti res I' == betti fIX)
///

///
-*
  restart
  needsPackage "SurfacesInP4"
*-
-- rat.d10.g9.quart1
  R = ZZ/32003[x_1..x_5]
  F = omega(R,3) ++ omega(R,3)
  G = omega(R,1) ++ omega(R,1) ++ R^1
  time IX = randomVanishingIdeal(G, F);
  fIX = res coker gens IX
  betti fIX
  elapsedTime surfaceInvariants IX 

  surfacesInP4(Degree => 10, Genus => 9, Type => "rat")
  I' = example first oo -- this is the one with one quartic
  assert(betti res I' == betti fIX)
///

///
-*
  restart
  needsPackage "SurfacesInP4"
*-
  -- I believe this is rat.d11.g11.0-sixsecants
  R = ZZ/32003[x_1..x_5]
  F = (omega(R,3)) ^ 3
  G = prune kernel ( randomMap(R^1, omega(R,2) ++ (omega(R,1))^2) );
  time IX = randomVanishingIdeal(G, F);
  fIX = res coker gens IX
  betti fIX
  elapsedTime surfaceInvariants IX 
  
  E = surfacesInP4(Degree => 11, Genus => 11)
  for e in E list e => betti res example e == betti fIX
  I' = example "rat.d11.g11.0-sixsecants"
  assert(betti res I' == betti fIX)
///

///
-*
  restart
  needsPackage "SurfacesInP4"
*-

  -- I believe this is a k3.d12.g14
x = symbol x

  R = ZZ/32003[x_1..x_5]
  F = R^{-1} ++ (omega(R,3))^4
  G = (omega(R,2)) ^ 3
  time IX = randomVanishingIdeal(G, F);
  fIX = res coker gens IX
  betti fIX
  elapsedTime surfaceInvariants IX 
  
  surfacesInP4(Degree => 12, Genus => 14, Type => "k3")
  I' = example first oo
  betti res I' == betti fIX
///

