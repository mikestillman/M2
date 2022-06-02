------------------------
-- Construction #1 -----
------------------------
-- Do rational-deg12.m2
-- until get idealX

betti res idealX
degree idealX
genera idealX

needsPackage "SurfacesInP4"
needsPackage "Truncations"

sectionalGenus idealX == 13
degree idealX == 12
singX = idealX + minors(codim idealX, jacobian idealX);
codim singX == 5 -- so nonsingular
char ring idealX == 5 -- this is over ZZ/5.

I5 = ideal submatrixByDegrees(gens idealX, 0, 5);
I5 : idealX -- looks like one 6-secant.

-- One needs to consider the adjunction process in perhaps a bit more detail?

------------------------
-- Construction #2 -----
------------------------


restart
-- read in first file too
-- Do monadConstruction.m2
-- now we need to do what?
elapsedTime I1 = randomSmoothSurface 114; -- seems to take a while, perhaps put in info about what is happening?
elapsedTime I2 = randomSmoothSurface 115;  -- the following 3 are relatively quick
elapsedTime I3 = randomSmoothSurface 116;
elapsedTime I4 = randomSmoothSurface 117;
elapsedTime I0 = randomSmoothSurface 113; -- this one might not lift to char 0? Also maybe takes longer?
