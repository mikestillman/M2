factorize = method()
factorize RingElement := (F) -> (
    facs := factor F;
    facs//toList/toList/reverse
    )

trager = method()
trager(Ring, RingElement) := (R, Q) -> (
     --R: ring generated via noetherPosition in TraceForm.m2
     --Q: element of the coefficient field of R in the conductor of R
     K := coefficientRing R;
     if not ring Q === K then error "expected first argument to be an element of the coefficientRing of the second.";
     print "--  trace form   --";
     time traceR := traceForm R;
     oldRing := fractionalIdeal ideal 1_R;
     radQ := traceRadical(Q, oldRing);
     print "-- endomorphisms --";
     time currentRing := Hom(radQ, radQ);
     while oldRing != currentRing do (
	  oldRing = currentRing;	  
	  --radQOld = traceRadicalOld(Q, currentRing);
	  radQ = traceRadical(Q, currentRing);
	  --if not radQOld == radQ then error "outputs do not agree for old and new";
          print "-- endomorphisms --";	  
	  time currentRing = Hom(radQ, radQ);
	  );
     currentRing
     )

traceRadicalOld = method()
traceRadicalOld(RingElement, FractionalIdeal) := (Q, J) -> (
     --first check that Q is in the coefficient ring of the ring of J
     R := ring J;
     K := coefficientRing R;
     if not ring Q === K then error "expected first argument to be an element of the coefficientRing of the second.";
     traceR := traceForm R;
     B := getBasis R;
     G := matrix{B} ** gens numerator J;
     print "--------------------";
     time M := last coefficients(G, Monomials => B);
     M = lift(M,K);
     time newTrace := transpose(M) * traceR * M;
     denom := denominator J;
     try denom = lift(denom, K) else error "expected denominator of ideal to be liftable to the coefficient ring"; 
     Qdiag := Q * (denom^2) * id_(target newTrace);
     time radGens := modulo(newTrace,Qdiag);
     << "slow version has size M = " << numColumns M << endl;
     rad := fractionalIdeal(denom, trim ideal(G*radGens));
     rad
     )

traceRadical = method()
traceRadical(RingElement, FractionalIdeal) := (Q, J) -> (
     --first check that Q is in the coefficient ring of the ring of J
     R := ring J;
     K := coefficientRing R;
     if not ring Q === K then error "expected first argument to be an element of the coefficientRing of the second.";
     traceR := traceForm R;
     B := getBasis R;
     G := matrix{B} ** gens numerator J;
     print "--------------------";
     print "--  computing M   --";
     time M := last coefficients(G, Monomials => B);
     << "fast version has size M = " << numColumns M << endl;     
     M = gens trim image lift(M,K);
     print "--  matrix mult   --";
     time newTrace := transpose(M) * traceR * M;
     denom := denominator J;
     try denom = lift(denom, K) else error "expected denominator of ideal to be liftable to the coefficient ring"; 
     Qdiag := Q * (denom^2) * id_(target newTrace);
     print "--   modulo       --";
     time radGens := modulo(newTrace,Qdiag);
     print "-- make frac ideal--";
     time rad := fractionalIdeal(denom, trim ideal(((matrix {B})*M)*radGens));
     rad
     )

displayTrager = method()
displayTrager(FractionalIdeal) := I -> (
     R := ring I;
     L := noetherField R;
     nums := apply(flatten entries gens numerator I, i-> sub(i,L));
     denom := sub(denominator I, coefficientRing L);
     apply(nums, p -> 1/denom * p)
     )

testIntegrality = method()
testIntegrality(RingElement, RingElement) := (num, denom) -> (
     -- num, denom: elements of a noetherRing R
     -- denom should be liftable to the coefficient ring
     -- returns true iff num/denom is an integral element of frac R over R
     R := ring num;
     K := coefficientRing R;
     denom = lift(denom,K);
     B := getBasis R;
     n := #B;
     M := matrix ({{1_K}}|toList (n-1:{0}));
     i := 1;
     while ker M == 0 do (
	  nextPower := num^i;
	  newCol := lift(last coefficients(nextPower, Monomials => B), K);
	  M = newCol | M;
	  i = i + 1;
	  );
     intEqn := flatten entries gens ker M;
     all(#intEqn, (i -> (intEqn#i) % (denom^i) == 0))
     )

testIntegrality FractionalIdeal := I -> (
     denom := denominator I;
     apply(flatten entries gens numerator I, num -> testIntegrality(num,denom))
     )

--getIntegralEquation = method()
getIntegralEquation(RingElement, RingElement, Ring) := (num, denom, Kt) -> (
     -- num, denom: elements of a noetherRing R
     -- denom should be liftable to the coefficient ring
     -- returns true iff num/denom is an integral element of frac R over R
     R := ring num;
     K := coefficientRing R;
     denom = lift(denom,K);     
     if not K === coefficientRing Kt then error "expected third argument to be polynomial ring over coefficient ring of ring of first argument";
     B := getBasis R;
     n := #B;
     M := matrix ({{1_K}}|toList (n-1:{0}));
     i := 1;
     while ker M == 0 do (
	  nextPower := num^i;
	  newCol := lift(last coefficients(nextPower, Monomials => B), K);
	  M = newCol | M;
	  i = i + 1;
	  );
     intEqn := flatten entries gens ker M;
     if not all(#intEqn, (i -> (intEqn#i) % (denom^i) == 0)) then return null;
     t := Kt_0;
     m := #intEqn - 1;
     result := sum for i from 0 to m list (
	  ((intEqn#i) // (denom^i)) * t^(m-i)
	  );
     print result;
     result
     )

getIntegralEquation FractionalIdeal := I -> (
     denom := denominator I;
     K := coefficientRing ring numerator I;
     Kt := K[t];
     apply(flatten entries gens numerator I, num -> getIntegralEquation(num,denom,Kt))
     )

simplifyFraction = method()
simplifyFraction(RingElement,RingElement) := (f,g) -> (
     -- given f/g an element of the fraction field of a Noether ring R
     -- re-express as a fraction with denominator in the coefficient ring of R
     I := (ideal g):f;
     denoms := first entries selectInSubring(1, gens gb I);
     if #denoms > 1 then print "more than one potential denom!";
     denom := denoms_0;
     numer := denom*f // g;
     K := coefficientRing ring denom;
     denom = lift(denom,K);
     (numer,denom)
     )

fractionalIdealFromICFracs = method() 
fractionalIdealFromICFracs(List, Ring) := (icFracs, R) -> (
     -- icFracs: output of icFractions
     -- R: Noether normalization of ring of icFracs
     numdenompairs := icFracs / (p -> (sub(numerator p, R), sub(denominator p,R)));
     numdenompairs = numdenompairs / simplifyFraction;
     denom = lcm (numdenompairs / last);
     I := ideal for P in numdenompairs list (
	  P#0 * (denom // P#1)
	  );
     I = I + ideal denom;
     J := fractionalIdeal(promote(denom,R), I);
     previous := J;
     output := J*J;
     while output != previous do (
	  print "got here";
	  previous = output;
	  output = output * J;
	  );
     output
     )


end

--test code--
restart
--errorDepth = 0
needsPackage "TraceForm"
needsPackage "FractionalIdeals"
load "Trager.m2"
S = ZZ/13[u,v, MonomialOrder=>{1,1}]
F = 5*v^6+7*v^2*u^4+6*u^6+21*v^2*u^3+12*u^5+21*v^2*u^2+6*u^4+7*v^2*u
R = S/F
R = noetherPosition{u}
Q = u*(u+1)*(u-9850)*(u^4 - 8451*u^3 - 7146*u^2 + 13901*u - 2285)
Q = u*(u+1)
time tragerOutput = simplify trager(R,Q)
factor lift(denominator tragerOutput, coefficientRing R)
displayTrager tragerOutput
gbTrace = 1
noetherize tragerOutput
simplify trager(R,u+1)
testIntegrality tragerOutput
getIntegralEquation tragerOutput

A = S/F
Afracs = icFractions A
Aideal = fractionalIdealFromICFracs(Afracs,R)
Aideal == tragerOutput -- trager and icFractions agree on this example

--boehm5
S = ZZ/32003[u,v] -- QQ is currently out of range, this one is just the dehomogenization of boehm4, and takes much longer!
F = 25*u^8+184*u^7*v+518*u^6*v^2+720*u^5*v^3+576*u^4*v^4+282*u^3*v^5+84*u^2*v^6+14*u*v^7+v^8+244*u^7+1326*u^6*v+2646*u^5*v^2+2706*u^4*v^3+1590*u^3*v^4+546*u^2*v^5+102*u*v^6+8*v^7+854*u^6+3252*u^5*v+4770*u^4*v^2+3582*u^3*v^3+1476*u^2*v^4+318*u*v^5+28*v^6+1338*u^5+3740*u^4*v+4030*u^3*v^2+2124*u^2*v^3+550*u*v^4+56*v^5+1101*u^4+2264*u^3*v+1716*u^2*v^2+570*u*v^3+70*v^4+508*u^3+738*u^2*v+354*u*v^2+56*v^3+132*u^2+122*u*v+28*v^2+18*u+8*v+1
R = S/F
R = noetherPosition {v}
Q = (v+3)*(v^2-1)
time tragerOutput = trager(R,Q)
A = S/F
Afracs = icFractions A -- slow
Aideal = fractionalIdealFromICFracs(Afracs,R)
Aideal == tragerOutput -- trager and icFractions agree on this example
J = simplify tragerOutput
displayTrager J
