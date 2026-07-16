-- Note: taken from ~/Dropbox/MikeLocal/conferences/2024-july-isaac-m2-tutorial/
-- I left a version there.
newPackage(
    "ModularMethods",
    Version => "0.11", 
    Date => "8 April 2025",
    Authors => {
        {
            Name => "Frank Moore", 
            Email => "moorewf@wfu.edu",
            HomePage => "https://sites.google.com/wfu.edu/frank-moore"},
        {
            Name => "Mike Stillman",  
            Email => "mike@math.cornell.edu", 
            HomePage => "http://www.math.cornell.edu/~mike"}
        },
    Headline => "modular methods",
    Keywords => {"Computer Algebra"},
    PackageExports => {},
    AuxiliaryFiles => false,
    DebuggingMode => true
    )

export {
    "chineseRemainder",
    "reduceMod",    -- currently documented, need to remove
    "ringOverZZ",
    "ringOverQQ",
    "rationalReconstruction",  -- used in Fields.m2?
    "rationalFunctionReconstruction",
    "gbMod",
    "gbOverQQProbable",
    "kernelViaModular"
    -- "monicGCDModular" defined in Fields.m2
    }

-- Used for testing result of the rationalReconstruction function.
ratReconstruct = method()
ratReconstruct(ZZ, ZZ, ZZ, ZZ) := QQ => (a, m, N, D) -> (
    v := {m, 0};
    w := {a, 1};
    while w#0 > N do (
        q := v#0//w#0;
        z := v - q * w;
        (v, w) = (w, z);
        print w;
        );
    << "----" << endl;
    if w#1 < 0 then w = -w;
    if w#1 > D then null else w#0/w#1
    )
ratReconstruct(ZZ, ZZ) := QQ => (a, m) -> (
    v := {m, 0};
    w := {a, 1};
    while abs(2 * w#0 * w#1) > m do (
        q := v#0//w#0;
        z := v - q * w;
        (v, w) = (w, z);
        print w;
        );
    << "----" << endl;
    if w#1 < 0 then w = -w;
    w#0/w#1
    )

  primes = {65521, 65519, 65497, 65479, 65449, 65447, 65437, 65423, 65419, 65413, 65407, 65393, 
    65381, 65371, 65357, 65353, 65327, 65323, 65309, 65293, 65287, 65269, 65267, 65257, 65239, 
    65213, 65203, 65183, 65179, 65173, 65171, 65167, 65147, 65141, 65129, 65123, 65119, 65111, 
    65101, 65099, 65089, 65071, 65063, 65053, 65033, 65029, 65027, 65011, 65003, 64997, 64969, 
    64951, 64937, 64927, 64921, 64919, 64901, 64891, 64879, 64877, 64871, 64853, 64849, 64817, 
    64811, 64793, 64783, 64781, 64763, 64747, 64717, 64709, 64693, 64679, 64667, 64663, 64661, 
    64633, 64627, 64621, 64613, 64609, 64601, 64591, 64579, 64577, 64567, 64553, 64513, 64499, 
    64489, 64483, 64453, 64451, 64439, 64433, 64403, 64399, 64381, 64373, 64333, 64327, 64319, 
    64303, 64301, 64283, 64279, 64271, 64237, 64231, 64223, 64217, 64189, 64187, 64171, 64157, 
    64153, 64151, 64123, 64109, 64091, 64081, 64067, 64063, 64037, 64033, 64019, 64013, 64007, 
    63997, 63977, 63949, 63929, 63913, 63907, 63901, 63863, 63857, 63853, 63841, 63839, 63823, 
    63809, 63803, 63799, 63793, 63781, 63773, 63761, 63743, 63737, 63727, 63719, 63709, 63703, 
    63697, 63691, 63689, 63671, 63667, 63659, 63649, 63647, 63629, 63617, 63611, 63607, 63601}

importFrom_Core { "raw", "rawMatrixRatConversion", "rawMatrixCRA" }

ringOverQQ = method()
ringOverQQ Ring := Ring => R -> (
    -- TODO: make sure this is a polynomial ring over ZZ.
    --   handle flattening?
    --   handle quotient rings?
    -- checks that RZ is over the integers, and if so
    --   creates RQ, same ring over rationals.
    -- this info is stashed in the rings RZ, RQ so we can keep the same rings.
    if R#?"ring over QQ" then R#"ring over QQ"
    else (
        if coefficientRing R =!= ZZ then error "expected polynomial ring over ZZ";
        RQ := QQ (monoid R);
        R#"ring over QQ" = RQ;
        RQ#"ring over ZZ" = R;
        RQ
        )
    )
ringOverZZ = method()
ringOverZZ Ring := Ring => R -> (
    if R#?"ring over ZZ" then R#"ring over ZZ"
    else (
        if coefficientRing R =!= QQ then error "expected polynomial ring over QQ";
        RZ := ZZ (monoid R);
        R#"ring over ZZ" = RZ;
        RZ#"ring over QQ" = R;
        RZ
        )
    )

-- Use locally TODO: should not need these.  Rewrite engine routines...
RZ0 = ZZ[]
RQ0 = ringOverQQ RZ0

-- this should also really return a pair
reduceMod = method()
reduceMod(QQ, ZZ) := ZZ => (a, N) -> (
    b := denominator a;
    (g, a1, b1) := toSequence gcdCoefficients(b, N);
    if g != 1 then error("reduceMod: denominator "|b|" is not relatively prime with modulus "|N);
    binv := a1 % N;
    ((numerator a)*binv) % N
    )
reduceMod(ZZ, ZZ) := ZZ => (a, N) -> a % N
reduceMod(List, ZZ) := List => (alist, N) -> alist/(a -> reduceMod(a, N))
reduceMod(RingElement, ZZ) := RingElement => (F, N) -> (
    RQ := ring F;
    tF := terms F;
    
    result := sum for a in terms F list (reduceMod(leadCoefficient a, N) * leadMonomial a);
    if coefficientRing RQ === ZZ then result
    else (
        RZ := ringOverZZ RQ;
        sub(result, RZ)
        )
    )
reduceMod(Matrix, ZZ) := Matrix => (mat, N) -> (
    if not isFreeModule source mat or not isFreeModule target mat then
        error "expected a matrix between free modules";
    matrix for row in entries mat list for f in row list reduceMod(f, N)
    )

-- now for reduceMod, for rational functions or polynomials in a variable t.
reduceMod(RingElement, RingElement, RingElement, ZZ) := (F, t, tval, m) -> (
     numer := reduceMod(sub(numerator F, {t => tval}), m);
     denom := reduceMod(sub(denominator F, {t => tval}), m);
     if liftable(denom, coefficientRing ring denom) then (
	  c := lift(denom, coefficientRing ring denom);
	  c = c%m;
	  if c == 0 then error "cannot reduce fraction";
	  (g,a,b) := toSequence gcdCoefficients(c, m);
	  (a * numer) % m
	  )
     else
          error "cannot reduce fraction"
     )


-- given a pair (a,N), returns a rational number
-- c/d such that c,d ~<= \sqrt{N}, d is invertible mod N and c = a*d mod N.
-- returns null if no such rational exists.

rationalReconstruction = method()
rationalReconstruction(ZZ, ZZ) := QQ => (a, N) -> (
    mat := matrix(RZ0, {{a}});
    result := map(RQ0, rawMatrixRatConversion(raw mat, N, raw RQ0));
    leadCoefficient result_(0,0)
    )

rationalReconstruction(List, ZZ) := List => (alist, N) -> (
    mat := matrix(RZ0, {alist});
    result := map(RQ0, rawMatrixRatConversion(raw mat, N, raw RQ0));
    (flatten entries result)/leadCoefficient
    )

rationalReconstruction(Matrix, ZZ, Ring) := (M, N, R) -> (
    -- M is a matrix over ZZ[vars...]
    -- N is a positive integer.  M is only defined up to mod N.
    -- R is the ring QQ[vars...]
    map(R, rawMatrixRatConversion(raw M, N, raw R))
    )

rationalReconstruction(Matrix, ZZ) := (M, N) -> (
    -- M is a matrix over ZZ[vars...]
    -- N is a positive integer.  M is only defined up to mod N.
    R := ring M;
    RQ := ringOverQQ R;
    rationalReconstruction(M, N, RQ)
    )

rationalReconstruction(RingElement, ZZ) := RingElement => (F, N) -> (
    fmat := rationalReconstruction(matrix{{F}}, N);
    fmat_(0,0)
    )

-- would like chineseRemainder to have the same interface as polyCRA
-- and the name changed to integerCRA
-- may want to add one that uses chineseRemainder List, which returns a sequence
--   this would do all the lifts coming from the List at once.

chineseRemainder = method()
chineseRemainder(Sequence, Sequence) := Sequence => (an1, an2) -> (
    -- an1, an2 are pairs (a,n1) and (b,n2)
    -- returns the lift (c,n1*n2)
    if class an1#1 === ZZ then
        integerCRA(an1,an2)
    else
        polyCRA(an1,an2)
    )

chineseRemainder(Sequence,Sequence,RingElement) := Sequence => (an1,an2,t) -> (
    polyCRA(an1,an2,t)
)

--chineseRemainder List
--chineseRemainder(List, RingElement)

integerCRA = method()

integerCRA(Sequence,Sequence) := Sequence => (an1,an2) -> (
    (a,n1) := an1;
    (b,n2) := an2;
    integerCRA(a,n1,b,n2)
)

integerCRA(ZZ,ZZ,ZZ,ZZ) := Sequence => (F1, N1, F2, N2) -> (
    -- N1, N2 are the moduli
    -- F1, F2 are the residues that we are lifting
    -- returns a pair (lift, N1*N2)
    f1 := matrix(RZ0, {{F1}});
    f2 := matrix(RZ0, {{F2}});
    result := map(RZ0, rawMatrixCRA(raw f1, raw f2, N1, N2));
    (leadCoefficient result_(0,0),N1*N2)
    )

integerCRA(List, ZZ, List, ZZ) := Sequence => (F1, N1, F2, N2) -> (
    -- N1, N2 are the moduli
    -- F1, F2 are lists of residues that we are lifting
    -- returns a pair (lift, N1*N2)
    f1 := matrix(RZ0, {F1});
    f2 := matrix(RZ0, {F2});
    result := map(RZ0, rawMatrixCRA(raw f1, raw f2, N1, N2));
    (flatten entries lift(result, ZZ),N1*N2)
    )

integerCRA(RingElement, ZZ, RingElement, ZZ) := Sequence => (F1, N1, F2, N2) -> (
    -- N1, N2 are the moduli
    -- F1, F2 are residues (of polynomials) that we are lifting
    -- returns a pair (lift, N1*N2)
    if ring F1 =!= ring F2 then error "expected ring elements over the same ring";
    R := ring F1;
    if coefficientRing R =!= ZZ then error "expected polynomial ring over the integers";
    result := map(R, rawMatrixCRA(raw matrix{{F1}}, raw matrix{{F2}}, N1, N2));
    (result_(0,0),N1*N2)
    )

integerCRA(Matrix, ZZ, Matrix, ZZ) := Sequence => (mat1, N1, mat2, N2) -> (
    -- N1, N2 are the moduli
    -- mat1, mat2 are matrices of residues (of polynomials) that we are lifting
    -- returns a pair (lift, N1*N2)
    if ring mat1 =!= ring mat2 then error "expected matrices over the same ring";
    R := ring mat1;
    result := if R === ZZ then (
             m := map(RZ0, rawMatrixCRA(raw promote(mat1, RZ0), raw promote(mat2, RZ0), N1, N2));
             lift(m, ZZ)
             )
        else if coefficientRing R === ZZ then 
            map(R, rawMatrixCRA(raw mat1, raw mat2, N1, N2))
        else error "expected polynomial ring over the integers";
    (result,N1*N2)
    )

-- Interface change:
-- polyCRA should be performing computations in a ring with one variable.
--   if the ring has more than one variable, the user may specify the variable.
-- polyCRA(Sequence,Sequence) := Sequence 
--      Input: (M,f), (N,g)
-- polyCRA(Sequence,Sequence,RingElement) := Sequence 
--      Input: (M,f), (N,g), t
-- M and N could either be RingElement, a List, or a Matrix (both with same type and shape/length)

polyCRA = method()

polyCRA(Sequence,Sequence) := Sequence => (an1,an2) -> (
    (a,n1) := an1;
    (b,n2) := an2;
    polyCRA(a,n1,b,n2)
)

polyCRA(Matrix,RingElement,Matrix,RingElement) := Sequence => (as,f,bs,g) -> (
     -- given matrices of polynomials as,bs and moduli f,g in K[x]
     -- where deg a < deg f, and deg b < deg g for all entries a in as and b in bs
     -- return a pair (matrix,polynomial) of polys poly h modulo fg s.t. h#i == a#i mod f, and h#i == b#i mod g
     (y,u,v) := toSequence gcdCoefficients(f,g);
     if y != 1 then error "gcd is not one!";
     u1 := (bs * u) % g;
     v1 := (as * v) % f;
     (u1 * f + v1 * g, f*g)
)

polyCRA(List,RingElement,List,RingElement) := Sequence => (as,f,bs,g) -> (
    result := polyCRA(matrix {as},f,matrix {bs},g);
    (flatten entries first result, last result)
)

polyCRA(RingElement, RingElement, RingElement, RingElement) := Sequence => (a,f,b,g) -> (
    result := polyCRA(matrix{{a}},f,matrix{{b}},g);
    ((result#0)_(0,0),last result)
)

polyCRA(Sequence, Sequence, RingElement) := (F,G,t) -> (
     -- F should be (f(t), m(t)), G = (g(t), n(t)).
     -- construct h(t) (mod m(t)*n(t)) s.t. h == f mod m, h == g mod n.
     -- All variables except t are considered coefficients.
     (f,m) := F;
     (g,n) := G;
     R := ring f;
     othervars := toList(set gens R - set{t});
     monF := set flatten entries monomials(f, Variables=>othervars);
     monG := set flatten entries monomials(g, Variables=>othervars);
     mons := toList(monF + monG);
     (mnsF, cfsF) := coefficients(f, Monomials=>mons, Variables=>othervars);
     (mnsG, cfsG) := coefficients(g, Monomials=>mons, Variables=>othervars);
     if not R#?"polyCRARing" then (T := local T; R#"polyCRARing" = (coefficientRing R)[T];);
     Rt := R#"polyCRARing";
     toRt := map(Rt, R, for f in gens R list if f == t then Rt_0 else 0_Rt);
     fromRt := map(R,Rt, {t});
     cfsF = toRt cfsF;
     cfsG = toRt cfsG;
     newcoeffs := polyCRA(cfsF,toRt m,cfsG,toRt n);
     ((mnsF * (fromRt first newcoeffs))_(0,0), fromRt(last newcoeffs))
     )

-- computation of the kernel of a matrix over QQ via Chinese remaindering

kernelViaModular = method()
kernelViaModular Matrix := (M) -> (
    -- assumption: M is an integer matrix, want the kernel over QQ.
    done := false;
    N := 1;
    Z := null; -- chinese remaindered kernel of M. -- (matrix, N)
    nextprime := nextPrime 2^25;
    i := 0;
    while i < 500 do (
        i = i+1;
        p := nextprime;
        nextprime = nextPrime (nextprime + 1);
        Rp := ZZ/p;
        Mp := sub(M, Rp);
        Zp := (sub(groebnerBasis syz Mp, RZ0), p);
        if Z === null then Z = Zp
        else (
            print i;
            Z = chineseRemainder(Zp, Z);
            ans := rationalReconstruction(Z);
            --<< "---- " << i << " -- " << (if Z =!= null then Z_1 else "") << endl;
            --<< "chinese remainder: " << Z << endl;
            --<< "rat reconstruct : " << ans << endl;
            -- TODO: Think about how often to check the answer...
            --       Currently checking every iteration.
            if i % 1 == 0 and M * sub(ans, QQ) == 0 then return sub(ans,QQ);
            )
        );
    )

gbMod = method()
gbMod(ZZ, Ideal) := Sequence => (p, I) -> (
    -- I should be an ideal in a ring QQ[vars].
    RQ := ring I;
    RZ := ringOverZZ RQ;
    Rp := (ZZ/p) (monoid RQ);
    Ip := sub(I, vars Rp); -- Question: does this match the output of reduceMod (likely not, probably balanced remainders here).
    -*elapsedTime*- GB1 := gens forceGB groebnerBasis(Ip, Strategy=>"F4"); -- TODO: this forceGB should not be needed?
    GB1 = sub(GB1, RZ);
    in1 := sub(leadTerm GB1, RZ);
    (in1, GB1)
    )

gbOverQQProbable = method()
gbOverQQProbable Ideal := (I) -> (
    -- mathicgb is limited to 16 bit primes.  So the largest prime
    -- available is 65521.
    R := ring I;
    RZ := ringOverZZ R;
    -- Do the first prime
    thisprime := primes#0;
    nextprimeIndex := 1;
    (firstIn, currentGBp0) := gbMod(thisprime, I);
    prevCR := (currentGBp0, thisprime);
    prevGB := rationalReconstruction prevCR;
    thisCR := null;
    thisGB := null;
    currentInp := null;
    while true do (
        p := primes#nextprimeIndex;
        --<< "About to try p = " << p << endl;
        nextprimeIndex = nextprimeIndex+1;
        (currentInp, currentGBp0) = gbMod(p, I);
        currentGBp := (currentGBp0, p);
        -- now, check the initial ideal
        if currentInp != firstIn then (
            -- a problem: either the ones we have done until now are bad, or this one is.
            -- so we need to choose which is better, and keep it.
            << "initial ideals are not the expected.  We do not yet handle this case.  Need to do so!" << endl;
            break;
            )
        else (
            -- this last one was good
            -- so now CRA lift to mod a larger currentN.
            -- rationalReconstruct it.
            -- if the same, then done (well, go to the checking phase).
            -- if not, we continue in the loop
            thisCR = chineseRemainder(prevCR, currentGBp);
            thisGB = rationalReconstruction thisCR;
            --<< "newGBZ after reconstruct: " << toString newGBQ_(0,126) << endl << endl;
            if thisGB - prevGB == 0 then break;
            prevCR = thisCR;
            prevGB = thisGB;
            );
        );
    -- at this point, currentGBQ holds the probable GB over QQ.
    -- we need to optionally check if this is the GB
    --<< "modular GB took " << nextprimeIndex << " number of iterations" << endl;
    thisGB
    )


-- this function is a helper function for rationalFunctionReconstruction
-- defined below, and will eventually be moved into the engine.
rationalFunctionReconstruction0 = method()
rationalFunctionReconstruction0(RingElement, RingElement) := (u,m) -> (
     -- expected: m and u are polynomials in 1 variable, over ZZ/p
     -- outputs: either null, or (a,b), where a,b are polynomials in the
     --  same ring as m, u and satisfy:
     --    (1) deg(a) + deg(b) < deg(m)
     --    (2) lc(b) = 1
     --    (3) gcd(a,b) = 1
     --    (4) gcd(b,m) = 1
     --    (5) a/b == u mod m
     -- currently taken almost verbatim from 2004-AFGCD (Monagan-vHoeij 2004)
     R := ring m;
     M := first degree m;
     -- the following two numbers are chosen smaller so that it will
     -- more likely succeed (see note from Monagan-vHoeij 2004).
     N := (M-1)//2; -- M//2; 
     D := M-N-2; -- M-N-1;
     (r0,s0) := (m,0_R);
     (r1,s1) := (u,1_R);
     while first degree r1 > N do (
	  q := r0 // r1;
	  (r0,r1) = (r1,r0 - q * r1);
	  (s0,s1) = (s1,s0 - q * s1);
	  );
     (a,b) := (r1,s1);
     if first degree b > D or gcd(b,m) != 1 then null
     else (
	  c := 1 / leadCoefficient(b);
	  (c*a, c*b)
	  )
     )

checkRatRecon = (F, u, ans) -> (
     if ans === null then return null;
     (numer,denom) := ans;
     -- we want to check that if a(t) := 1/denom (mod u)
     -- then F * a == numer mod u
     (g,a,b) := toSequence gcdCoefficients(denom, u);
     if g != 1 then error "check rat recon: gcd is not 1";
     rem := (F  - a*numer) % u;
     if rem != 0 then error ("remainder: "|toString rem);
     )
 
rationalFunctionReconstruction = method()

rationalFunctionReconstruction(Sequence, RingElement) := (Fmt,t) -> (
    (F,mt) := Fmt;
    rationalFunctionReconstruction1(F,mt,t)
)

rationalFunctionReconstruction1 = method()
rationalFunctionReconstruction1(RingElement, RingElement, RingElement) := (F, mt, t) -> (
     -- F should be a poly in R = ZZ/p[vars]
     -- t is one of the vars
     -- mt is a poly in t, coeffs in ZZ/p, but mt is in R.
     -- output is (G, denom), G and denom are in ZZ[all vars], but denom only involves t.
     R := ring F;
     othervars := toList(set gens R - set{t});
     (mons, cfs) := coefficients(F, Variables=>othervars);
     if not R#?"polyCRARing" then (T := local T; R#"polyCRARing" = (coefficientRing R)[T];);
     Rt := R#"polyCRARing";
     toRt := map(Rt, R, for f in gens R list if f == t then Rt_0 else 0_Rt);
     fromRt := map(R,Rt, {t});
     cfs = flatten entries toRt cfs;
     mtInRt := toRt mt;
     newpairs := for i from 0 to #cfs - 1 list (
	  ans := rationalFunctionReconstruction0(cfs#i, mtInRt);
          -- the next line is for debugging only
          -- checkRatRecon(cfs#i, mtInRt, ans);
	  if ans === null then return null;
	  ans);     -- now find lcm of the denoms
     newdenom := newpairs/last//lcm;
     newnumers := apply(newpairs, (numer, denom) -> {(newdenom//denom) * numer});
     ((mons * fromRt matrix newnumers)_(0,0), fromRt newdenom)
     )

-- TODO!
--rationalFunctionReconstruction1(List, RingElement, RingElement) := (F, mt, t) ->
--rationalFunctionReconstruction1(Matrix, RingElement, RingElement) := (F, mt, t) ->

----------------------------------------------------------
-- rational function reconstruction over a finite field --
----------------------------------------------------------
-- plan:
--   L = kk(t1, ..., tr)[z1, ..., zs]/Izt is a field in normal form
--   F is in L[x1, ..., xn].
-- reduceMod(F, ti=>a), where a is in kk.
-- F, G are in kk[x, z, t], mt and nt are monic polynomials (usually products of (t-a)'s), relatively prime.
-- polyCRA((F,mt), (G,nt)) ==> (H, mt*nt) -- H is also in Ap (this works already?)
-- polyRationalReconstruction((F,mt), t)

---- keep this snippet??
---- reduceMod(RingElement, RingElement, RingElement) := (F, t, val) -> (
----     (map(ring F, ring F, {t => val})) F
----     )


-- methods for Chinese remainder and poly rational reconstruction in
-- R = L[xs], L = ZZ/p(ts)[zs]/Iz.
-- Ap = ZZ/p[xs, zs, ts]
--
-- myterms: returns hashtable of terms => coeffs(t)
myterms = method()
myterms RingElement := List => (F) -> (
    -- F is in R
    -- gives hash table of monomial in x,z => rational function in t.
    flatten for x in terms F list (
        monx := leadMonomial x;
        -- if z vars:
        cf := leadCoefficient leadCoefficient x;
        -- if no z vars:
        -- cf := leadCoefficient
        flatten for y in terms cf list (
            mony := leadMonomial y;
            cfy := leadCoefficient y;
            (monx * mony, cfy)
            ))
    )

-- this is *only* used for testing, is allowed to be slow.
reduceMod(RingElement, RingElement, Ring) := (F, mt, Ap) -> (
    H := myterms F;
    mt = sub(mt, ring denominator H_0_1);
    tms := for x in H list (
        ft := x#1;
        (g, u, v) := gcdCoefficients(denominator ft, mt);
        print (g,u,v);
        if g != 1 then return null;
        ht := ((numerator ft) * u) % mt;
        (x#0, ht)
        );
    sub(tms/times//sum, Ap)
    )

-- reduceMod
-- polyCRA
-- rationalFunctionReconstruction


beginDocumentation()

doc ///
  Key
    ModularMethods
  Headline
    rational reconstruction and Chinese remainder algorithms
  Description
    Text
  SeeAlso
///

doc ///
  Key
    reduceMod
    (reduceMod, QQ, ZZ)
    (reduceMod, ZZ, ZZ)
    (reduceMod, List, ZZ)
  Headline
    reduce a rational number or list of numbers mod an integer
  Usage
    reduceMod(a, N)
  Inputs
    a:QQ
      or an integer or a list of rational numbers and integers
    N:ZZ
      a non-negative integer
  Outputs
    :ZZ
      or a list of integers
  Description
    Text
      Reduce each rational number or integer in $a$ by the positive integer $N$.

      This is a service/debugging function, mostly used to test the other functions in
      this package.
    Example
      needsPackage "ModularMethods"
      N = 346324763283783264
      b = reduceMod(13/29, N)
      (b * 29 - 13) % N == 0
    Text
      If the denominator of $a$ is not relatively prime with $N$, then an error
      is raised.
    Example
      try (reduceMod(13/(29*31), 29*37); false) else true
    Text
      For integers, this is just @TO "operator%"@.  Note that this operator
      applied to a rational number does {\it not} give the desired answer here.
    Example
      a = 33289478947389573857389573897538975839759387
      reduceMod(a, N) == a % N
      reduceMod(-a, N) == (-a) % N
      (13/29) % N -- not what we want in this setting! This is why we wrote the function reduceMod.
    Text
      This works given a list of rational numbers, a matrix over ZZ or QQ,
      a  polynomial over the rationals or integers, or even a matrix
      of polynomials over the integers or rationals.
    Example
      reduceMod({13/25, 707, 28/31}, 101)
      reduceMod(matrix{{13/25, 707, 28/31}}, 101)
      R = QQ[x,y]
      F = 13/25 * x^3 + 707 * x*y^5 + 28/31 * y^7
      FZ = reduceMod(F, 101)
      reduceMod(matrix{{F}}, 101)
  SeeAlso
    rationalReconstruction
    chineseRemainder
///

doc ///
  Key
    rationalReconstruction
    (rationalReconstruction, ZZ, ZZ)
    (rationalReconstruction, List, ZZ)
    (rationalReconstruction, RingElement, ZZ)
    (rationalReconstruction, Matrix, ZZ)
  Headline
    construct a rational number equivalent to a given integer (or list of integers)
  Usage
    rationalReconstruction(a, N)
  Inputs
    a:ZZ
    N:ZZ
  Outputs
    :QQ
      a rational number $b/c$ congruent to $a$ modulo $N$,
      where if possible $b$ and $c$ are taken to
      be such that $2bc < N$.
  Description
    Text
      Each integer coefficient appearing in a ring element, list or matrix
      is lifted to a rational number $b/c$ where if possible $b$ and $c$ are taken to
      be such that $2bc < N$.  If this is not possible, then should we return (answer, false)
      and if it is possible, (answer, true)?
    Example
      debug needsPackage "ModularMethods" -- for ratReconstruct
      N = 346324763283783264
      b = reduceMod(13/29, N)
      rationalReconstruction(b, N)
      N = 1684 -- works, but 1683 does not...
      b = reduceMod(13/29, N)
      rationalReconstruction(b, N)
      ratReconstruct(b, N, 29, 29)

      N = 1683
      b = reduceMod(13/29, N)
      rationalReconstruction(b, N) -- fails
      ratReconstruct(b, N, 29, 29) -- works
      N - 2*29^2 == 1
    Text
      The main use case is when the first argument is a polynomial, or a matrix.
    Example
      m = matrix{{123/101, -34/19, 12/17}}
      N = 1073741827
      m1 = reduceMod(m, N)
      --rationalReconstruction(m1, N) -- error: no coefficient ring present
    Example
      R = QQ[x,y]
      m = matrix{{123/101 * x + y, -34/19 * x^2, 12/17 * y^3}}
      N = 1073741827
      m1 = reduceMod(m, N)
      m2 = rationalReconstruction(m1, N)
      m == m2 -- gives false.  degrees don't match.  Seems like we want to keep the source and target the same...
      m - m2 == 0
  SeeAlso
    chineseRemainder
    reduceMod
///

doc ///
  Key
    chineseRemainder
    (chineseRemainder, Sequence, Sequence)
    (chineseRemainder, Sequence, Sequence, RingElement)
  Headline
    use chinese remainder theorem to solve a pair of integer or polynomial congruences
  Usage
    chineseRemainder((a1, N1), (a2, N2))
    chineseRemainder((a1, N1), (a2, N2), t)
  Inputs
    a1:{ZZ,RingElement,List,Matrix}
    N1:{ZZ,RingElement}
    a2:{ZZ,RingElement,List,Matrix}
    N2:{ZZ,RingElement}
      $N1$ and $N2$ must be relatively prime positive integers or polynomials
     t:RingElement
  Outputs
    :Sequence
      The pair (b,N_1 N_2) where (the entries of) b are such that $-N_1 N_2/2 \le b < N_1 N_2 /2$
      and $b mod N_1 = a_1$ and $b mod N_2 = a_2$
  Description
    Text
      This implements the Chinese remainder algorithm: given
      two integers (or polynomials) $a_1$ and $a_2$, and two relatively prime positive integers
      $N_1$, $N_2$, returns the unique integer $b$ in the range
      $-N_1 N_2/2 \le b < N_1 N_2 /2$ such that $b mod N_1 = a_1$ and $b mod N_2 = a_2$
    Example
      (b,N) = chineseRemainder((5, 12), (7, 25))
      reduceMod(b, 12) == 5
      reduceMod(b, 25) == 7
      b + 12*25
    Text
      If a list of integers is given for both $a_1$, $a_2$, then
      the Chinese remainder algorithm is applied to each $(a_1)_i$ and $(a_2)_i$
      in turn, returning the list of results.
    Example
      (b,N) = chineseRemainder((matrix{{9,10,11,0,1}}, 12), (matrix{{14,15,16,17,28}}, 25))
      flatten entries b == {-111, -110, -109, -108, -47}
    Text
      If $a_1$ and $a_2$ are both polynomials over ZZ or both matrices
      over a polynomial ring over ZZ, then apply the Chinese remainder algorithm
      to the coefficients of each monomial in the support of $a_1$ or $a_2$.
    Example
      RZZ = ZZ[x,y,z]
      RQQ = ringOverQQ RZZ
      F = 3/10*x^2-101/5*x*y + 1/17*y^3
      f = reduceMod(F, 32003)
      g = reduceMod(F, 32009)
      h = reduceMod(F, 32027)
      (fg,N) = chineseRemainder((f, 32003), (g, 32009))
      rationalReconstruction(fg, N)
      (fgh,N) = chineseRemainder((fg, N), (h, 32027))
      rationalReconstruction(fgh, N)
    Example
      G = 41*x^2-4/7*x*y + 1/19*y^3
      M = matrix{{F,G}}
      a1 = reduceMod(M, 32003)
      a2 = reduceMod(M, 32009)
      (b,N) = chineseRemainder((a1, 32003), (a2, 32009))
      rationalReconstruction(b, N)
    Example
      F = 3/10*x^2-101/5*x*y + 1/17*y^3
      f = (reduceMod(F, 32003), 32003)
      g = (reduceMod(F, 32009), 32009)
      h = (reduceMod(F, 32027), 32027)
      fg = chineseRemainder(f, g)
      rationalReconstruction fg
      fgh = chineseRemainder(fg, h)
      rationalReconstruction fgh
  SeeAlso
    reduceMod
    rationalReconstruction
    ringOverQQ
    ringOverZZ
///

-- the below doc node is a duplicate of the above... oops!
-*
doc ///
  Key
    (chineseRemainder, Sequence, Sequence)
  Headline
    Chinese remainder algorithm applied to coefficients of a polynomial
  Usage
    (F,r) = chineseRemainder((g,m),(h,n))
  Inputs
    :Sequence
      (g,m)
    :Sequence
      (h,n), g and h are elements in a polynomial ring over $\mathbb{Z},
      $m$ and $n$ are positive, relatively prime integers
  Outputs
    :Sequence
      $(F,r)$, where
      $F$ is a polynomial such that $F == g mod m$, and $F == h mod n$.
      $F$ is uniquely defined modulo $r = mn$.
  Description
    Example
      RZZ = ZZ[a..d]
      F = a^3 - 12 * a^2*b + 11*a*b*c - 1450 * c^3
      f = F % 11
      g = F % 13
      h = F % 41
      (f1,r1) = chineseRemainder((f,11),(g,13))
      (f2,r2) = chineseRemainder((f1,r1),(h,41))
      f2 == F
      rationalReconstruction(f2,r2)
  SeeAlso
    chineseRemainder
    rationalReconstruction
///
*-

-----------------------
-- Tests --------------
-----------------------
-*
  restart
  debug  needsPackage "ModularMethods"
*-
-- removing this test for now, as this version of polyCRA has been commented out
-*
TEST ///
  debug  needsPackage "ModularMethods"
  RZZ = ZZ[a..d,s, MonomialOrder=>Lex]
  RK = frac RZZ
  F = (s^2+1) * a^3 - 12*(s+1)/s * a^2*b + (11*s^2-s-1)*a*b*c - 1/45 * s * c^3

  use RZZ
  f1 = reduceMod(F, s, 5_RZZ, 11)
  f2 = reduceMod(F, s, 6_RZZ, 11)
  f3 = reduceMod(F, s, 7_RZZ, 11)
  f4 = reduceMod(F, s, 8_RZZ, 11)
  
  (g,r) = polyCRA((f1,s-5), (f2,s-6), s, 11)
  (g,r) = polyCRA((f3,s-7), (g,r), s, 11)  
  (g,r) = polyCRA((f4,s-8), (g,r), s, 11)  

  -- can't lift this one...
  polyRationalReconstruction(g,s,r,11)


  use RZZ
  f1 = reduceMod(F, s, 5_RZZ, 32003)
  f2 = reduceMod(F, s, 6_RZZ, 32003)
  f3 = reduceMod(F, s, 7_RZZ, 32003)
  f4 = reduceMod(F, s, 8_RZZ, 32003)
  f5 = reduceMod(F, s, 9_RZZ, 32003)
  f6 = reduceMod(F, s, 10_RZZ, 32003)

  (g,r) = polyCRA((f1,s-5), (f2,s-6), s, 32003)
  (g,r) = polyCRA((f3,s-7), (g,r), s, 32003)  
  (g,r) = polyCRA((f4,s-8), (g,r), s, 32003)  
  (g,r) = polyCRA((f5,s-9), (g,r), s, 32003)
  (g,r) = polyCRA((f6,s-10), (g,r), s, 32003)  

  G = polyRationalReconstruction(g,s,r,32003)
  G#0 / G#1 == F

  use RZZ
  f1 = reduceMod(F, s, 1_RZZ, 134217757)
  f2 = reduceMod(F, s, 2_RZZ, 134217757)
  f3 = reduceMod(F, s, 3_RZZ, 134217757)
  f4 = reduceMod(F, s, 4_RZZ, 134217757)
  f5 = reduceMod(F, s, 5_RZZ, 134217757)
  f6 = reduceMod(F, s, 6_RZZ, 134217757)

  (g,r) = polyCRA((f1,s-1), (f2,s-2), s, 134217757)
  (g,r) = polyCRA((f3,s-3), (g,r), s, 134217757)  
  (g,r) = polyCRA((f4,s-4), (g,r), s, 134217757)  
  (g,r) = polyCRA((f5,s-5), (g,r), s, 134217757)
  (g,r) = polyCRA((f6,s-6), (g,r), s, 134217757)  

  G = polyRationalReconstruction(g,s,r,134217757)
  G#0 / G#1 , F -- TODO: evenutally want the test to have them equal!!  This will never happen, for one prime...?
///
*-

-*
  restart
  debug  needsPackage "ModularMethods"
*-
TEST ///
  debug  needsPackage "ModularMethods"
  RZZ = ZZ[a..d,s, MonomialOrder=>Lex]
  RK = frac RZZ
  F = (s^2+1) * a^3 - 12*(s+1)/(s-32) * a^2*b + (11*s^2-s-1)*a*b*c/(12*s^2 + 32) - 1/45 * s * c^3
  use RZZ

  p = 32003
  Rp = (ZZ/p) (monoid RZZ)
  fracRp = frac Rp
  Fp = sub(F,fracRp)  

  f1 = sub(reduceMod(F, s, 5_RZZ, 32003),Rp)
  f2 = sub(reduceMod(F, s, 6_RZZ, 32003),Rp)
  f3 = sub(reduceMod(F, s, 7_RZZ, 32003),Rp)
  f4 = sub(reduceMod(F, s, 8_RZZ, 32003),Rp)
  f5 = sub(reduceMod(F, s, 9_RZZ, 32003),Rp)
  f6 = sub(reduceMod(F, s, 10_RZZ, 32003),Rp)

  use Rp
  hk = chineseRemainder((f1,s-5),(f2,s-6),s)
  hk = chineseRemainder((f3,s-7),hk,s)
  hk = chineseRemainder((f4,s-8),hk,s)
  hk = chineseRemainder((f5,s-9),hk,s)
  hk = chineseRemainder((f6,s-10),hk,s)

  pr = rationalFunctionReconstruction(hk,s)
  assert((pr#0 / pr#1) == Fp)
///

 -*
  restart
  needsPackage "ModularMethods"
*-
TEST ///
  debug needsPackage "ModularMethods"
  RQQ = QQ[a..d]
  --RK = frac RZZ
  --numerator(1/3 * a)
  --R = ZZ/32003[a..d]
  --use RK
  F = a^3 - 12/37 * a^2*b + 11*a*b*c - 1/45 * c^3
  F11 = reduceMod(F, 11)
  RZZ = ring F11
  assert try (reduceMod(F, 37); false) else true
  assert try (reduceMod(F, 15); false) else true
  --assert(reduceMod(F, 37) === null) -- gives error instead of null? want both behaviors probably...
  --assert(reduceMod(F, 15) === null) -- gives error instead of null?
  reduceMod(F, 101)
  f1 = reduceMod(F, 11)
  f2 = reduceMod(F, 13)
  (g,r) = chineseRemainder((f1,11),(f2,13))
  assert(f1 == reduceMod(g, 11))
  assert(f2 == reduceMod(g, 13))
  (g,r) = chineseRemainder((reduceMod(F, 32003), 32003), (g,r))
  H = rationalReconstruction (g,r)
  assert(H == F)
///

-*
  restart
  needsPackage "ModularMethods"
*-
TEST /// -- moved to ModularMethods
  debug needsPackage "ModularMethods"
  R=QQ[x_0..x_5];
  F = sum apply(flatten entries basis(2, R), m -> (random 1000)/(1 + random 100) * m)
  select(1..100, i -> isPrime(2^58+2*i+1))
  P1 = 2^58 + 2*34+1
  G = reduceMod(F, P1)
  assert(F == rationalReconstruction(G, P1))
  P2 = 101
  G = reduceMod(F, P2)
  rationalReconstruction(G, P2) -- needs to return an indication as to whether it succeeded
  G = reduceMod(F, P2^4)  
  rationalReconstruction(G, P2^4) -- needs to return an indication as to whether it succeeded
  F == oo 

  f1 = reduceMod(F, 101)
  f2 = reduceMod(F, 103)
  (g,m) = chineseRemainder((f1,101),(f2,103))
  rationalReconstruction(g, m) == F
  (g,m) = chineseRemainder((reduceMod(F, 107),107),(g,m))
  rationalReconstruction(g, m) == F
  (g,m) = chineseRemainder((reduceMod(F, 109),109),(g,m))
  assert(rationalReconstruction(g, m) == F) -- true
///

-*
  restart
  needsPackage "ModularMethods"
*-
TEST /// -- ratReconstruct (private function, currently)
-- TODO: this test has few asserts.  FIXME!
  debug ModularMethods  -- for ratReconstruct
  a = reduceMod(2/3, 101)
  assert(a == 68)
  assert(ratReconstruct(a, 101, 8, 8) == 2/3)

  a = reduceMod(2/5, 101)
  assert(a == 61)
  assert(ratReconstruct(a, 101, 8, 8) == 2/5)

  reduceMod(-3/5, 101)
  ratReconstruct(60, 101, 6,7)
  allfracs6 = sort unique flatten for i from -6 to 6 list for j from 1 to 6 list i/j
  allfracsmod = for x in allfracs6 list reduceMod(x, 101)
  for x in allfracsmod list ratReconstruct(x, 101, 5, 5)
  for x in allfracsmod list rationalReconstruction(x, 101)
  for x in allfracsmod list ratReconstruct(x, 101, 6, 6) == rationalReconstruction(x, 101)
  reduceMod(7/6, 101)
  reduceMod(8/5, 101)
  ratReconstruct(18, 101, 7, 7) == rationalReconstruction(18, 101)
  ratReconstruct(42, 101, 8, 6) -- does here
  ratReconstruct(42, 101, 7, 7) -- doesn't list here
  ratReconstruct(42, 101) -- doesn't list here
  rationalReconstruction(42, 101)
  ratReconstruct(42, 101)
///


-*
  restart
  needsPackage "ModularMethods"
*-
TEST /// -* ringOverZZ, ringOverQQ *-
  R = ZZ[x,y]
  RQ = ringOverQQ R
  RZ = ringOverZZ RQ
  RQ2 = ringOverQQ RZ
  assert(R === RZ)
  assert(RQ === RQ2)

  S = QQ[x,y]
  SZ = ringOverZZ S
  SQ = ringOverQQ SZ
  SZ2 = ringOverZZ SQ
  assert(S === SQ)
  assert(SZ === SZ2)

  assert(RQ =!= S) -- it cannot be equal, as they know nothing about each other.
///

-*
  restart
  needsPackage "ModularMethods"
*-
TEST /// -* reduceMod *-
  -- test 1: for integers, rationals
  -- Question: do we want this to return balanced remainder, not
  -- nonnegative remainder?
  debug needsPackage "ModularMethods"
  assert(0 === reduceMod(13/17, 13))
  assert(0 === reduceMod(0, 13))
  assert(1 === reduceMod(1, 13))
  assert(10 === reduceMod(10, 13))
  assert(1 === reduceMod(27, 13))
  assert(12 === reduceMod(-1, 13))
  
  
  -- test 2: for list of integers/rationals
  -- TODO: how to handle this?  Have numerator, denominator defined for all rings?
  numerator ZZ := x -> x
  denominator ZZ := x -> 1

  L = {6,7,8,9/7,10,11/12,12,13,14,15/4}
  ans = reduceMod(L, 13)
  assert(#ans == #L)
  assert all(ans, x -> instance(x, ZZ) and x >= 0 and x < 13)
  for i from 0 to #L - 1 do (
      assert( ((denominator L#i) * ans#i - numerator L#i) % 13 == 0 )
      ) 

  -- test 3: for matrix over the integers or rationals
  assert(reduceMod(matrix{L}, 13) == matrix{ans})
  assert(reduceMod(matrix{ans}, 13) == matrix{ans})
  
  -- test 4: for polynomials over the integers or rationals
  -- test 5: for matrices of polynomials over integers or rationals
  R = ZZ[x,y]
  RQ = ringOverQQ R
  f = 6*x+7*y + 13*x^4
  f1 = reduceMod(6*x+7*y + 13*x^4, 13)
  assert(ring f1 === R)
  assert(size f1 == 2)
  use R
  assert(f1 == 6*x + 7*y)

  use RQ
  f = 6*x+7*y + 13/7*x^4
  h = reduceMod(f, 13)
  g = reduceMod(matrix{{f, 0}}, 13)
  assert(ring g === R)
  assert instance(g, Matrix)
  assert(g_(0,0) == h)
///

-*
restart
needsPackage "ModularMethods"
*-
TEST ///
-- test of CRA and rational reconstruction.
  RZZ = ZZ[x,y]
  RQQ = ringOverQQ RZZ
  f = x^2*y + (101*107*109)/14103 * x  * y
  R101 = (ZZ/101)(monoid RZZ)
  R32003 = (ZZ/32003)(monoid RZZ);
  R65521 = (ZZ/65521)(monoid RZZ);
  R65537 = (ZZ/65537)(monoid RZZ);

  f1 = sub(sub(f,R32003), RZZ)
  f2 = sub(sub(f,R65521), RZZ)
  f3 = sub(sub(f,R101), RZZ)  
  f4 = sub(sub(f,R65537), RZZ)
  
  (g,N) = chineseRemainder((f1,32003),(f2,65521))
  (g,N) = chineseRemainder((g,N),(f3,101))
  (g,N) = chineseRemainder((g,N),(f4,65537))
  h = rationalReconstruction(g, N)
  assert(f == h)
///

-*
restart
needsPackage "ModularMethods"
*-
TEST ///
  -- oscillator ideal for graph: allG7#14#5
  -- here is the graph:
  ---Graph{0 => {3, 4, 5, 6}      }
  ---      1 => {4, 5, 6}
  ---      2 => {4, 5, 6}
  ---      3 => {0, 5, 6}
  ---      4 => {0, 1, 2, 6}
  ---      5 => {3, 0, 1, 2, 6}
  ---      6 => {3, 0, 4, 1, 2, 5}

  -- good example for speed, but not so much for testing
  -*
  R = QQ[x_1..y_6]
  I = ideal(y_3+y_4+y_5+y_6,
      -x_4*y_1-x_5*y_1-x_6*y_1+x_1*y_4+x_1*y_5+x_1*y_6,
      -x_4*y_2-x_5*y_2-x_6*y_2+x_2*y_4+x_2*y_5+x_2*y_6,
      -x_5*y_3-x_6*y_3+x_3*y_5+x_3*y_6-y_3,
      x_4*y_1+x_4*y_2-x_1*y_4-x_2*y_4-x_6*y_4+x_4*y_6-y_4,
      x_5*y_1+x_5*y_2+x_5*y_3-x_1*y_5-x_2*y_5-x_3*y_5-x_6*y_5+x_5*y_6-y_5,
      x_6*y_1+x_6*y_2+x_6*y_3+x_6*y_4+x_6*y_5-x_1*y_6-x_2*y_6-x_3*y_6-x_4*y_6-x_5*y_6-y_6,
      x_1^2+y_1^2-1,x_2^2+y_2^2-1,x_3^2+y_3^2-1,x_4^2+y_4^2-1,x_5^2+y_5^2-1,x_6^2+y_6^2-1
      )
  *-

  -- here is how to get oscillator examples:
  -*
  needsPackage "Oscillators"
  needsPackage "NautyGraphs"
  Gstrs = generateGraphs(6, OnlyConnected => true, MinDegree => 2);
  Gs = Gstrs/stringToGraph;
  G = Gs_60
  R = oscRing(G, CoefficientRing => QQ, Reduced => true)
  I = oscSystem(G,R)
  *-

  R = QQ[x_1..y_5]
  I = ideal(-y_1-y_2-y_3-y_4-y_5,
    x_2*y_1+x_3*y_1+x_4*y_1+x_5*y_1-x_1*y_2-x_1*y_3-x_1*y_4-x_1*y_5+y_1,
    -x_2*y_1+x_1*y_2+x_3*y_2+x_4*y_2+x_5*y_2-x_2*y_3-x_2*y_4-x_2*y_5+y_2,
    -x_3*y_1-x_3*y_2+x_1*y_3+x_2*y_3+x_4*y_3+x_5*y_3-x_3*y_4-x_3*y_5+y_3,
    -x_4*y_1-x_4*y_2-x_4*y_3+x_1*y_4+x_2*y_4+x_3*y_4+x_5*y_4-x_4*y_5+y_4,
    -x_5*y_1-x_5*y_2-x_5*y_3-x_5*y_4+x_1*y_5+x_2*y_5+x_3*y_5+x_4*y_5+y_5,
    x_1^2+y_1^2-1,x_2^2+y_2^2-1,x_3^2+y_3^2-1,x_4^2+y_4^2-1,x_5^2+y_5^2-1)

  needsPackage "Msolve" 
  elapsedTime msolveGBI = msolveGB I; -- .42s (255 generators)

  elapsedTime gbI = gbOverQQProbable I;

  H2 = hashTable for f in (ideal msolveGBI)_*  list (g := 1/(leadCoefficient f) * f; leadMonomial g => g);
  H1 = hashTable for f in (ideal gbI)_*  list (leadMonomial f => f);

  assert(H1 === H2)
  assert(keys H1 === keys H2)

  -- a check with a slower algorithm  
  G1 = elapsedTime gens gb I;
  G1 = flatten entries G1;
  G1 = for g in G1 list (1/(leadCoefficient g)) * g;

  G = flatten entries gbI;
  assert(G1 == G)
///

-*
restart
needsPackage "ModularMethods"
*-
TEST ///
setRandomSeed(42)
M = mutableMatrix(ZZ/2,100,99);
N = mutableMatrix(ZZ/2,99,100);
fillMatrix(M, Density => .1);
fillMatrix(N, Density => .1);
M = sub(matrix M,ZZ);
N = sub(matrix N,ZZ);
X = M * N;
elapsedTime kerX1 = kernelViaModular X;
elapsedTime kerX2 = gens ker (X ** QQ);
leadCoeff = K -> first flatten entries ((transpose leadTerm K) * K);    
kerX1 = (leadCoeff(kerX1))^(-1) * kerX1;
kerX2 = (leadCoeff(kerX2))^(-1) * kerX2;
assert(kerX1 == kerX2)
///

-*
  restart
  needsPackage "ModularMethods"
*-
TEST /// -* chineseRemainder  XXX TODO *-
  -- test 1: for integers, rationals
///


end--

-* Development section *-
restart
needsPackage "ModularMethods"
check "ModularMethods"

uninstallPackage "ModularMethods"
restart
installPackage "ModularMethods"
viewHelp "ModularMethods"

beginDocumentation()

doc ///
  Key
    GBoverQQ
  Headline
    probably Groebner basis over QQ via computation over finite fields
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
  Caveat
  SeeAlso
///

-- Applications (these are relative to the inclusion ZZ \subseteq QQ, but could work
--               for a function field over QQ as well)
-- 1. Compute rank of a matrix over QQ (kinda dumb -- just compute rank mod lots of primes)
-- 2. Compute kernel of a matrix over QQ by computing in ZZ/p for various p and CRTing up
-- 3. GB of an ideal over QQ (or better yet, a fraction field over QQ) by computing GBs over ZZ/p and CRTing up
-- 4. Compute GCD of polynomials over QQ modulo p
-- 5. Compute an elimination ideal over QQ by computing it modulo p for various p.

-- To do these things, we would need to improve/flesh out:
-- 1. Improve interface/naming etc (throughout!)
-- 2. Flesh out the applications using the infrastructure in the package.  Would help users understand how to use.
-- 3. Determine what should go into the engine (see: rationalFunctionReconstruction)
-- 4. Look at FLINT interface to see what we could use there.  (Is FLINT threadsafe?)
--      Add univariate FLINT polynomial data type in engine over F_q?  Top level?
