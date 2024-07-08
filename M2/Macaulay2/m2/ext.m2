--		Copyright 1995 by Daniel R. Grayson

needs "basis.m2"
needs "gateway.m2" -- for ScriptedFunctor
needs "matrix1.m2"
needs "modules.m2"
needs "Hom.m2"

-- TODO: should this be fixed for all Ext methods,
-- or should they each have their own options?
ExtOptions = new OptionTable from {
    MinimalGenerators => true
     }

Ext = new ScriptedFunctor from {
    superscript => i -> new ScriptedFunctor from {
	-- Ext^1(F, G)
	argument => ExtOptions >> opts -> X -> applyMethodWithOpts''(Ext, functorArgs(i, X), opts)
	},
    argument => ExtOptions >> opts -> X -> applyMethodWithOpts''(Ext, X, opts)
    }

-- TODO: Ext^i(R, S) should work as well
Ext(ZZ, Ring, Ring)   :=
Ext(ZZ, Ring, Ideal)  :=
Ext(ZZ, Ring, Module) :=
Ext(ZZ, Ideal, Ring)   :=
Ext(ZZ, Ideal, Ideal)  :=
Ext(ZZ, Ideal, Module) :=
Ext(ZZ, Module, Ring)   :=
Ext(ZZ, Module, Ideal)  := Module => opts -> (i,M,N) -> Ext^i(module M, module N, opts)
Ext(ZZ, Module, Module) := Module => opts -> (i,M,N) -> (
     R := ring M;
     if not isCommutative R then error "'Ext' not implemented yet for noncommutative rings.";
     if R =!= ring N then error "expected modules over the same ring";
     if i < 0 then R^0
     else if i === 0 then Hom(M, N, opts)
     else (
	  C := resolution(M,LengthLimit=>i+1);
	  b := C.dd;
	  --complete b;
	prune' := if opts.MinimalGenerators then prune else identity;
	prune' if b#?i then (
	    if b#?(i+1)
	    then homology(Hom(b_(i+1), N, opts), Hom(b_i, N, opts))
	    else cokernel Hom(b_i,     N, opts))
	else (
	    if b#?(i+1)
	    then kernel Hom(b_(i+1), N, opts)
	    else Hom(C_i, N, opts))))

Ext(ZZ, Matrix, Ring)   :=
Ext(ZZ, Matrix, Ideal)  := Matrix => opts -> (i,f,N) -> Ext^i(f, module N, opts)
Ext(ZZ, Matrix, Module) := Matrix => opts -> (i,f,N) -> (
     R := ring f;
     if not isCommutative R then error "'Ext' not implemented yet for noncommutative rings.";
     if R =!= ring N then error "expected modules over the same ring";
     prune' := if opts.MinimalGenerators then prune else identity;
     if i < 0 then map(R^0, R^0, {})
     else if i === 0 then Hom(f, N, opts)
     else prune'(
	  g := resolution(f,LengthLimit=>i+1);
	  Es := Ext^i(source f, N, opts);
	  Et := Ext^i(target f, N, opts);
	  psi := if Es.cache.?pruningMap then Es.cache.pruningMap else id_Es;
	  phi := if Et.cache.?pruningMap then Et.cache.pruningMap else id_Et;
	  psi^-1 * inducedMap(target psi, target phi, Hom(g_i, N, opts)) * phi))

-- TODO: is this correct?
-- c.f. https://github.com/Macaulay2/M2/issues/246
Ext(ZZ, Ring,   Matrix) :=
Ext(ZZ, Ideal,  Matrix) := Matrix => opts -> (i,N,f) -> Ext^i(module N, f, opts)
Ext(ZZ, Module, Matrix) := Matrix => opts -> (i,N,f) -> (
     R := ring f;
     if not isCommutative R then error "'Ext' not implemented yet for noncommutative rings.";
     if R =!= ring N then error "expected modules over the same ring";
     prune' := if opts.MinimalGenerators then prune else identity;
     if i < 0 then map(R^0, R^0, {})
     else if i === 0 then Hom(N, f, opts)
     else prune'(
	  C := resolution(N,LengthLimit=>i+1);
	  Es := Ext^i(N, source f, opts);
	  Et := Ext^i(N, target f, opts);
	  psi := if Es.cache.?pruningMap then Es.cache.pruningMap else id_Es;
	  phi := if Et.cache.?pruningMap then Et.cache.pruningMap else id_Et;
	  phi^-1 * inducedMap(target phi, target psi, Hom(C_i, f, opts)) * psi))


-- Local Variables:
-- compile-command: "make -C $M2BUILDDIR/Macaulay2/m2 "
-- End:
