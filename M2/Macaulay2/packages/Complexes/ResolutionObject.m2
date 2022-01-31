-- todo 7 Feb 2022
-- 1. debug DegreeLimit, LengthLimit, interrupting for Engine resolution
-- 2. after that: other engine strategies
-- 3. after that: other strategies

-- todo 10 Dec 2021.
-- 1. res M -- needs length limit if the ring is not a polynomial ring over a field (or ZZ?)
-- 2. resolutionDegreeLimit: should check that argument is null, an integer, or a list of integers of the right length.
--      at the moment (1.19.1): it handles null, integer case, but doesn't verify it is a list otherwise.

importFrom_Core { "RawComputation", "raw" }
importFrom_Core { "degreeToHeft", 
    "rawBetti", 
    "rawStartComputation", 
    "rawGBSetStop", 
    "rawStatus1", 
    "rawGBBetti", "rawResolution",
    "rawResolutionGetFree", "rawResolutionGetMatrix"
    }

ResolutionObject = new Type of MutableHashTable
ResolutionObject.synonym = "resolution object"
toString ResolutionObject := C -> toString raw C
raw ResolutionObject := X -> X.RawComputation

inf := t -> if t === infinity then -1 else t

-*
resolutionObject = method(Options => {
        SortStrategy => 0, 
        Strategy => 0,
        LengthLimit => infinity,
        DegreeLimit => infinity})
resolutionObject Module := ResolutionObject => opts -> M -> (
    RO := new ResolutionObject;
    RO.ring = ring M;
    -- the following line needs to change logic.
    lengthlimit := if opts.LengthLimit === infinity then numgens RO.ring + 1 else opts.LengthLimit;
    RO.RawComputation = rawResolution(
      raw M,            -- the matrix
      true,             -- whether to resolve the cokernel of the matrix
      lengthlimit,      -- how long a resolution to make, (hard : cannot be increased by stop conditions below)
      false,	        -- useMaxSlantedDegree
      0,                -- maxSlantedDegree (is this the same as harddegreelimit?)
      opts.Strategy,    -- algorithm number
      opts.SortStrategy	-- strategy
      );
    RO.Strategy = opts.Strategy;
    RO.LengthLimit = lengthlimit;
    RO.returnCode = rawStatus1 RO.RawComputation;
    RO
    )

compute = method(Options => true)
compute ResolutionObject := {
      DegreeLimit => {},
      SyzygyLimit => infinity,
      PairLimit => infinity
      } >> opts -> (RO) -> (
    rawGBSetStop(
        RO.RawComputation,
        false,                                      -- always_stop
        degreeToHeft(RO.ring, inf opts.DegreeLimit), -- degree_limit
        0,                                          -- basis_element_limit (not relevant for resolutions)
        inf opts.SyzygyLimit,                       -- syzygy_limit
        inf opts.PairLimit,                         -- pair_limit
        0,                                          -- codim_limit (not relevant for resolutions)
        0,                                          -- subring_limit (not relevant for resolutions)
        false,                                      -- just_min_gens
        {}                                          -- length_limit
        );
    rawStartComputation RO.RawComputation;
    RO.returnCode = rawStatus1 RO.RawComputation;
    RO.DegreeLimit = opts.DegreeLimit;
    RO
    )
*-

-- moduleAt = method()
-- moduleAt(ResolutionObject, ZZ) := (W,i) ->
--     new Module from (W.ring, rawResolutionGetFree(W.RawComputation, i))

-- matrixAt = method()
-- matrixAt(ResolutionObject, ZZ) := (W,i) -> (
--     src := moduleAt(W, i); -- TODO: stash these
--     tar := moduleAt(W, i-1);
--     map(tar, src, rawResolutionGetMatrix(W.RawComputation, i))
--     )

-*
complex ResolutionObject := Complex => opts -> RO -> (
    lengthlimit := RO.LengthLimit;
    modules := for i from 0 to lengthlimit list 
        new Module from (RO.ring, rawResolutionGetFree(RO.RawComputation, i));
    maps := hashTable for i from 1 to lengthlimit list (
        if modules#i == 0 then break;
        i => map(modules#(i-1), modules#i, rawResolutionGetMatrix(RO.RawComputation, i))
        );
    complex maps
    )
*-

-*
freeResolution Module := Complex => opts -> M -> (
    -- TODO: handle caching and strategies and hooks via Mahrud's new method.
    local F;
    if opts.LengthLimit < 0 then error "expected a non-negative value for LengthLimit";
    
    if not M.cache.?freeResolution
      or M.cache.freeResolution.cache.LengthLimit < opts.LengthLimit
      then M.cache.freeResolution = (
          R := ring M;
          strategy := if instance(opts.Strategy, Number) then opts.Strategy else
              if isQuotientRing R or isSkewCommutative R then 2 else 1;
          -- some strategies require a GB, some don't.  The next line implements this choice.
          f := if member(strategy, {0,4}) then gens gb presentation M else presentation M;
          lengthlimit := defaultLengthLimit(ring M, 0, opts.LengthLimit);
          RO := resolutionObject(f, 
              LengthLimit => lengthlimit,
              Strategy => strategy
              );
          compute(RO, DegreeLimit => opts.DegreeLimit);
          -- TODO: check that this is complete.
          F = complex RO;
          F.cache.LengthLimit = if length F < lengthlimit then infinity else lengthlimit;
          F.cache.Module = M;
          F
         );
    F = M.cache.freeResolution;
    if opts.LengthLimit < length F
    then (
        F = naiveTruncation(F, 0, opts.LengthLimit);
        F.cache.Module = M;
        );
    F
    )
*-

naiveTruncationByLengthAndDegree = method()
naiveTruncationByLengthAndDegree(Complex, ZZ, ZZ) := Complex => (C, lengthlimit, degreelimit) -> (
    naiveTruncation(C, -infinity, lengthlimit); -- TODO: also truncate by (slanted) degrees.
    )

freeResolution Module := Complex => opts -> M -> (
    -- This handles caching, hooks for different methods of computing 
    -- resolutions or over different rings which require different algorithms.
    if M.cache.?Resolution then (
        C := M.cache.Resolution;
        if not C.cache.?LengthLimit or not C.cache.?DegreeLimit then
            error "internal error: Resolution should have both a LengthLimit and DegreeLimit";
        if C.cache.LengthLimit === opts.LengthLimit and C.cache.DegreeLimit === opts.DegreeLimit then
            return C;
        if C.cache.LengthLimit >= opts.LengthLimit and C.cache.DegreeLimit >= opts.DegreeLimit then
            return naiveTruncationByLengthAndDegree(C, opts.LengthLimit, opts.DegreeLimit);
        remove(M.cache, symbol Resolution); -- will be replaced below
        );
    if M.cache.?ResolutionObject then (
        RO := M.cache.ResolutionObject;
        if opts.Strategy === null or opts.Strategy === RO.Strategy
        then (
            if RO.isComputable(opts.LengthLimit, opts.DegreeLimit) -- can change RO.LengthLimit, RO.DegreeLimit
            then (
                RO.compute(); -- it is possible to interrupt this and then the following lines do not happen.
                C = RO.complex();
                C.cache.LengthLimit = opts.LengthLimit;
                C.cache.DegreeLimit = opts.DegreeLimit;
                C.cache.Module = M;
                M.cache.Resolution = C;
                return C;
                )
            );
        remove(M.cache, symbol ResolutionObject);
        );

    RO = new ResolutionObject from {
        symbol ring => ring M,
        symbol LengthLimit => opts.LengthLimit,
        symbol DegreeLimit => opts.DegreeLimit,
        symbol Strategy => opts.Strategy,
        symbol Module => M
        };
    M.cache.ResolutionObject = RO;

    -- the following will return a complex (or error), and perhaps modify M.cache.ResolutionObject, M.Resolution?    
    runHooks((freeResolution, Module), (opts, M), Strategy => opts.Strategy)
    
    -- each hook must do the following:
    -- set Strategy.
    -- create any data it needs (in the RO object).
    -- place functions RO.isComputatable, RO.compute, RO.complex into RO. (or have some other way of doing that).
    -- or, perhaps, make a ResolutionObjectHook type, and have each hook create methods on that.
    -- either way, each hook has to create these functions...

    -- Question: where is the actual computation happening? In the hook!
    );

resolutionInEngine = (opts, M) -> (
    -- opts are the options from resolution.  Includes Strategy, LengthLimit, DegreeLimit.
    -- M is a Module.
    
    -- first determine if this method applies.  
    -- Return null if not, as quickly as possible
    R := ring M;
    if not (
        R.?Engine and
        heft R =!= null and
        isHomogeneous M and
        (isCommutative R or isSkewCommutative R) and (
            A := ultimate(coefficientRing, R);
            A =!= R and isField A
        ))
    then return null;

    -- otherwise: we set the Strategy to be Engine.
    RO := M.cache.ResolutionObject;  -- this must exist?
    if RO.Strategy === null then RO.Strategy = Engine;

    if RO.?RawComputation then error "internal error: our logic is wrong";

    RO.LengthLimit = if opts.LengthLimit === infinity then numgens R else opts.LengthLimit;
    RO.DegreeLimit = if opts.DegreeLimit === null then infinity else degreeToHeft(R, opts.DegreeLimit);
    RO.RawComputation = rawResolution(
        raw presentation M, -- the matrix
        true,             -- whether to resolve the cokernel of the matrix
        RO.LengthLimit,   -- how long a resolution to make, (hard : cannot be increased by stop conditions below)
        false,            -- useMaxSlantedDegree
        0,                -- maxSlantedDegree (is this the same as harddegreelimit?)
        1,                -- algorithm number, 1 in this case.
        opts.SortStrategy -- sorting strategy, for advanced use
        );
    RO.returnCode = rawStatus1 RO.RawComputation; -- do we need this?

    RO.compute = () -> (
        deglimit := if RO.DegreeLimit === infinity then {} else {RO.degreeLimit};
        rawGBSetStop(
            RO.RawComputation,
            false,                                      -- always_stop
            deglimit,                                   -- degree_limit
            0,                                          -- basis_element_limit (not relevant for resolutions)
            -1, -- inf opts.SyzygyLimit,                       -- syzygy_limit
            -1, -- inf opts.PairLimit,                         -- pair_limit
            0,                                          -- codim_limit (not relevant for resolutions)
            0,                                          -- subring_limit (not relevant for resolutions)
            false,                                      -- just_min_gens
            {}                                          -- length_limit
            );
        rawStartComputation RO.RawComputation;
        RO.returnCode = rawStatus1 RO.RawComputation;
        RO.DegreeLimit = opts.DegreeLimit;
        );

    RO.isComputable = (lengthlimit, degreelimit) -> (
        -- returns Boolean, and if it returns true, might set RO.LengthLimit, RO.DegreeLimit.
        << "calling isComputable" << endl;
        if lengthlimit > RO.LengthLimit then return false;
        RO.LengthLimit = lengthlimit;
        RO.DegreeLimit = degreelimit;
        true
        );

    RO.complex = () -> (
        -- returns a Complex. 
        lengthlimit := RO.LengthLimit;
        modules := for i from 0 to lengthlimit list 
            new Module from (R, rawResolutionGetFree(RO.RawComputation, i));
        maps := hashTable for i from 1 to lengthlimit list (
            if modules#i == 0 then break;
            i => map(modules#(i-1), modules#i, rawResolutionGetMatrix(RO.RawComputation, i))
            );
        complex maps
        );
    
    RO.compute();
    return RO.complex();
    -- now: create the engine computation
    --      create isComputable func
    --      create compute func
    --      create complex func.
    )

addHook((freeResolution, Module), resolutionInEngine, Strategy => Engine)


--scan({Engine}, strategy ->
--    addHook(key := (resolution, Module), algorithms#key#strategy, Strategy => strategy))

-- Note: the RawComputation below can only appear in some hooks...
-*    
    -- call the correct hook.  Note that 
    lengthlimit := if opts.LengthLimit === infinity then numgens RO.ring + 1 else opts.LengthLimit;
    RO.RawComputation = rawResolution(
      raw M,            -- the matrix
      true,             -- whether to resolve the cokernel of the matrix
      lengthlimit,      -- how long a resolution to make, (hard : cannot be increased by stop conditions below)
      false,	        -- useMaxSlantedDegree
      0,                -- maxSlantedDegree (is this the same as harddegreelimit?)
      opts.Strategy,    -- algorithm number
      opts.SortStrategy	-- strategy
      );
    RO.Strategy = opts.Strategy;
    RO.LengthLimit = lengthlimit;
    RO.returnCode = rawStatus1 RO.RawComputation;
    RO
    )

    RO := resolutionObject(M, 
        LengthLimit => lengthlimit,
        DegreeLimit => degreelimit,
        Strategy => strategy
        );
    
    -- TODO: handle caching and strategies and hooks via Mahrud's new method.
    local F;
    if opts.LengthLimit < 0 then error "expected a non-negative value for LengthLimit";
    
    if not M.cache.?freeResolution
      or M.cache.freeResolution.cache.LengthLimit < opts.LengthLimit
      then M.cache.freeResolution = (
          R := ring M;
          strategy := if instance(opts.Strategy, Number) then opts.Strategy else
              if isQuotientRing R or isSkewCommutative R then 2 else 1;
          -- some strategies require a GB, some don't.  The next line implements this choice.
          f := if member(strategy, {0,4}) then gens gb presentation M else presentation M;
          lengthlimit := defaultLengthLimit(ring M, 0, opts.LengthLimit);
          RO := resolutionObject(f, 
              LengthLimit => lengthlimit,
              Strategy => strategy
              );
          compute(RO, DegreeLimit => opts.DegreeLimit);
          -- TODO: check that this is complete.
          F = complex RO;
          F.cache.LengthLimit = if length F < lengthlimit then infinity else lengthlimit;
          F.cache.Module = M;
          F
         );
    F = M.cache.freeResolution;
    if opts.LengthLimit < length F
    then (
        F = naiveTruncation(F, 0, opts.LengthLimit);
        F.cache.Module = M;
        );
    F
    )
*-

end--
restart
debug needsPackage  "Complexes"
load "ResolutionObject.m2"
gbTrace=1
S = ZZ/101[a..d]
I = ideal(a*b-c*d, a^3-c^3, a*b^2-c*d^2)
M = S^1/I
F = freeResolution(M, Strategy => Engine)
assert isWellDefined F
F2 = freeResolution(I, LengthLimit => 2)
dd^F2
betti F2
F3 = freeResolution(I, LengthLimit => 3)
F3 = freeResolution(I, LengthLimit => 10)

I = ideal(a*b-c*d, a^3-c^3, a*b^2-c*d^2)
F = freeResolution(I, Strategy => 2)
assert isWellDefined F

I = ideal(a*b-c*d, a^3-c^3, a*b^2-c*d^2)
F = freeResolution(I, Strategy => 0)
assert isWellDefined F

I = ideal(a*b-c*d, a^3-c^3, a*b^2-c*d^2)
F = freeResolution(I, Strategy => 3)
assert isWellDefined F

I = ideal(a*b-c*d, a^3-c^3, a*b^2-c*d^2)
F = freeResolution(I, Strategy => 4) -- nonminimal...
assert isWellDefined F

I = ideal I_*
F = freeResolution(I, DegreeLimit => 3, LengthLimit => 2)
F = freeResolution(I, DegreeLimit => 2, LengthLimit => 2)
F = freeResolution I
-- change strategy
-- degree limit, changing degree limit
-- hooks
-- ComputationContext stuff...


use S
R = S/(a^2, b^2, c^2, d^2)
I = ideal(a,b,c,d)
F = freeResolution I
betti F
assert isWellDefined F

I = ideal(a,b,c,d)
F = freeResolution(I, LengthLimit => 3)
F = freeResolution(I, LengthLimit => 4)
F = freeResolution(I, LengthLimit => 6)
F = freeResolution(I, LengthLimit => 4)

W = resolutionObject(gens I, Strategy => 4)
compute W
F = complex W
assert isWellDefined F
assert(prune HH F == complex comodule I)

raw W
peek W
raw W

restart
R = ZZ/101[a..d]
M = coker vars R
C = res M
C.cache
debug Core
peek M.cache#(new ResolutionContext)
