--Does the (integralClosure, Ring) code produce a set of module generators? I think it does.
--Note that the (integralClosure,Ring) code works in the inhomog case. At the moment
--the use of pushForward in this routine prevents us doing the inhomog case.
--I *think* the package PushForward fixes that, but the doc there doesn't say... .

needsPackage "IntegralClosure"
needsPackage "PushForward"

extendIdeal = method()

integralClosure(Ideal, RingElement, ZZ) := opts -> (I,a,D) -> (
    S := ring I;
    if a % I != 0 then error "The ring element should be an element of the ideal.";
    if ((ideal 0_S):a) != 0 then error "The given ring element must be a nonzerodivisor of the ring.";
    z := local z;
    w := local w;
    I = trim I;
    Reesi := (flattenRing reesAlgebra(I,a,Variable => z))_0;
    Rbar := integralClosure(Reesi, opts, Variable => w);
    psi := map(Rbar,S,DegreeMap =>d->prepend(0,d));
    zIdeal := ideal(map(Rbar,Reesi))((vars Reesi)_{0..numgens I -1});
    zIdealD := module zIdeal^D;
    ID := I^D;
    LD := prepend(D,toList(degreeLength S:null));
    LDplus := prepend(D+1,toList(degreeLength S:null));    
    degD := image basisOfDegreeD(LD,Rbar); --all gens of first-degree D.
    degDplus := image basisOfDegreeD(LDplus,Rbar); --all gens of first-degree D.
    degsM := apply(degrees cover degD,d->drop(d,1));
    M := coimage map(degD,S^(-degsM),psi,id_(cover degD));
--    M := pushFwd(psi,degD/degDplus,NoPrune => true);
    mapback := map(S,Rbar, matrix{{numgens Rbar-numgens S:0_S}}|(vars S), DegreeMap => d -> drop(d, 1));
    phi := map(M,module ID, mapback matrix inducedMap(degD,zIdealD));
--    phi := map(M,module ID,id_M);
    if isHomogeneous I and isHomogeneous a then assert(isHomogeneous phi);
    assert(isWellDefined phi);
--error();
--    extendIdeal(ID,phi)
    extendIdeal phi
    )
integralClosure(Ideal,ZZ) := Ideal => o -> (I,D) -> integralClosure(I, I_0, D, o)
integralClosure(Ideal,RingElement) := Ideal => o -> (I,a) -> integralClosure(I, a, 1, o)
integralClosure(Ideal) := Ideal => o -> I -> integralClosure(I, I_0, 1, o)


extendIdeal(Matrix) := Ideal => phi -> ( --This method is WRONG on integralClosure ideal"a2,b2".
    --input: f: (module I) --> M, an inclusion from an ideal 
    --to a module that is isomorphic to the inclusion of I into an ideal J containing I.
    --output: the ideal J, so that f becomes the inclusion I subset J.
    inc := transpose gens source phi;
    phi0 := transpose matrix phi;
    sz := syz transpose presentation target phi;    
    (q,r) = quotientRemainder(inc,phi0*sz);
    if r !=0 then error "phi is not isomorphic to an inclusion of ideals";
    ideal (sz*q) -- is the "trim" doing anything?
    )

basisOfDegreeD = method()
basisOfDegreeD (List,Ring) := Matrix => (L,R) ->(
    --assumes degrees of R are non-negative
    --change to a heft value sometime.
    PL := positions(L, d-> d=!=null);    
    PV := positions(degrees R, D->any(PL,i->D#i > 0));
    PVars := (gens R)_PV;
    PDegs := PVars/degree/(D->D_PL);
      kk := ultimate(coefficientRing, R);
    R1 := kk(monoid[PVars,Degrees =>PDegs]);
    back := map(R,R1,PVars);
    g := back basis(L_PL, R1);
    map(target g,,g)
    )
--we should still add:    
--basisOfDegreeD (List,Module)
--basisOfDegreeD (List,Ideal)

///
R = ZZ/101[a,b,c,Degrees=>{{1,1,0},{1,0,0},{0,0,2}}]
L = {2,2,null}
basisOfDegreeD({2,null,2}, S)

S = ZZ/101[vars(0..10), Degrees => {{2, 6}, {1, 3}, {1, 3}, {1, 3}, {1, 3}, {0, 1}, {0, 1}, {0, 1}, {0, 1}, {0, 1}, {0, 1}}]
basisOfDegreeD({2,null}, S)
///

--used for examples made with Dedekind-Mertens theorem
unflatten = method()
unflatten(RingElement) := (x) -> (
    -- check that x is a variable
    i := index x;
    R := ring x;
    A := (coefficientRing R)[drop(gens R, {i,i})];
    A[x]
    )        

content(RingElement, RingElement) := Ideal => (f,x) ->(
--second argument should be a variable.    
    S := ring x;
    R := unflatten x;
    psi := map(R,S);
    phi := map(S,R);
    trim ideal phi ((coefficients psi f)_1)
    )

end--

restart
needs "bug-integralClosure.m2"
TEST///
    S = ZZ/101[a,b,c,d]
    K =ideal(a,b)
    I = c*d*K
    M = module (c*K)
    M' = module(d*K)
    phi = map(M,module I,d*id_M)
    phi' = map(M',module I,c*id_M')
    assert(isWellDefined phi)
    assert(extendIdeal phi == c*K)
    assert(extendIdeal phi'== d*K)    
    assert(integralClosure I == I)
    assert(integralClosure ideal"a2,b2" == ideal"a2,ab,b2")
///

TEST///
    S = ZZ/101[a,b,c]/ideal(a^3-b*(b-c)*(b+c))
    K =ideal(a,b)
    I = c*(b+c)*K
    M = module (c*K)
    M' = module((b+c)*K)
    phi = map(M,module I,(b+c)*id_M)
    phi' = map(M',module I,c*id_M')
    assert(isWellDefined phi)
    assert(isWellDefined phi')    
    assert(extendIdeal phi == c*K)
    assert(extendIdeal phi'== (b+c)*K)    
    assert(integralClosure I == I) 
///

TEST///
-*
  restart
  needs "bug-integralClosure.m2"
*-
    S = ZZ/101[a,b,c]/ideal(a^3-b^2*c)
    K =ideal(a,b)
    I = c*(b+c)*K
    M = module (c*K)
    M' = module((b+c)*K)
    phi = map(M,module I,(b+c)*id_M)
    phi' = map(M',module I,c*id_M')
    assert(isWellDefined phi)
    assert(isWellDefined phi')    
--    assert(extendIdeal(I,phi)== c*K)
--    assert(extendIdeal(I,phi')== (b+c)*K)    
    assert(extendIdeal(phi)== c*K)
    assert(extendIdeal(phi')== (b+c)*K)    
    assert(integralClosure I == I)
    assert(integralClosure(ideal(a^2,b^2))==ideal"a2,ab,b2")
///



TEST ///
    S=ZZ/32003[a,b,c,d,e,f]
    S=QQ[a,b,c,d,e,f]
    I=ideal(a*b*d,a*c*e,b*c*f,d*e*f);
    trim(J=I^2)
    K=integralClosure(I,I_0,2) -- integral closure of J = I^2
    assert(K == J+ideal"abcdef") 
    
    load "tmp"
    load "brian-example1-answers.m2"
    assert(ideal1 == elapsedTime integralClosure(I, I_0, 1))
    assert(ideal2 == elapsedTime integralClosure(I, I_0, 2))
    assert(ideal3 == elapsedTime integralClosure(I, I_0, 3))
    assert(ideal4 == elapsedTime integralClosure(I, I_0, 4))
    assert(ideal5 == elapsedTime integralClosure(I, I_0, 5))
///

--family of inhomogeneous examples suggested by craig:
--integral dependence of a power series on its derivatives.
restart
needs "bug-integralClosure.m2"
kk = QQ
S = kk[a,b]
mm = ideal vars S
T = kk[t]
f = (ker map(T,S,{t^4,t^6+t^7}))_0
--the simplest plane curve singularity with 2 characteristic pairs,
--thus NOT quasi-homogeneous.
--f could be any polynomial, preferably inhomogeneous, since then it's not obvious.
I = ideal diff(vars S,f)
assert(f%(I+f*mm)!=0)--f is not even locally in I
J = integralClosure I
assert(f%J != 0)--f is not in the integral closure of I; but 
assert(f % (J+f*mm) == 0) --f IS locally in the integral closure of I
---------------------------

--Dedekind-Mertens example
--Let c(f,x) be the content of f with respect to the variable x. 
--Theorem: c(f,x)*c(g,x) is integral over c(f*g, x).
restart
needs "bug-integralClosure.m2"
setRandomSeed 0
kk = QQ
S = kk[a,b,c]
f = random(2,S)
g = random(3,S)
f' = f-sub(f, {S_0=>0,S_2=>0})
g' = g-sub(g, {S_0=>0,S_2=>0})
If = content(f',S_1)
Ig = content(g',S_1)
Ifg = content(f'*g',S_1)
assert((gens(If*Ig) % Ifg)!=0)
assert(gens(If*Ig) % integralClosure Ifg == 0)

