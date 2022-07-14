needsPackage "BGG"
needsPackage "Truncations"

-- checkMorphismsForDeg12Surf:  This checks whether a map
-- from 3E to 4E(-2) has the following betti diagram:
--
--  total: 4 3 4 4 
--     -2: 4 . . .
--     -1: . 3 2 .
--      0: . . 2 4

checkMorphismsForDeg12Surf=(a)->(     
     (tally degrees source a.dd_2)_{1}==2      
     and (tally degrees source a.dd_2)_{2}==2    
     and (tally degrees source a.dd_3)_{3}==4
     );
numberOfGoodMorForDeg12Surf=(N, g)->(
    E := ring g;
     i:=0;          
     L:={};    
     usedTime:=timing
     while i<N do (
           a:=random(E^{4:2},target g)*g;
           fa:=res(coker a,LengthLimit=>3);
           if checkMorphismsForDeg12Surf(fa)==true
           then(
		L=append(L,betti fa);
                );
          i=i+1;
          );
     collectGarbage();
     << "--used time=" << usedTime#0 << endl;
     tally L);

-- randomMonadForDeg12Surf: This detects a map B2 from 2E(2) to 3E
-- such that the cokernel of B1|B2 : 2E(1) \oplus 2E(2) -> 3E 
-- has the following Betti diagram:
-- 
--  total: 3 4 9  
--      0: 3 2 . 
--      1: . 2 4 
--      2: . . 5 
-- 
-- and the submatrix of the syzygy matrix of B1|B2 has 
-- the following Betti diagram:
--
--  total: 4 4 13  
--      1: 2 . . 
--      2: 2 4 . 
--      3: . . 13 

randomMonadForDeg12Surf=(k,l)->(    
     i:=0;    
     isGoodMonad:=false;    
     while not isGoodMonad do (
           a:=random(E^{4:2},target g)*g;
	   fa:=res (coker a,LengthLimit=>4);
	   if checkMorphismsForDeg12Surf(fa)==true  then (
                b1:=fa.dd_2;
                b2:=submatrix(fa.dd_3,{0..3},{0..3});
                fb1:=res(coker b1, LengthLimit=>2);
                fb2:=res(coker b2, LengthLimit=>2);
                if 
                (tally degrees source fb1.dd_2)_{4}==k 
                and (tally degrees source fb2.dd_2)_{5}==l 
                then (
                      isGoodMonad=true;
                       );
                 );
           i=i+1;
	   collectGarbage();
           );
      a) 

-- idealOfDeg12Surf: This computes the ideal corresponding to 
-- the monad obtained by randomMonadForDeg12Surf and then 
-- check smoothness of the surface. 
-- If the surface is smooth, then this command returns 
-- the ideal. 

idealOfDeg12Surf=(k,l)->(
     i:=0;
     isSmooth:=false;
     while not isSmooth do (
	  a:=randomMonadForDeg12Surf(k,l);    
          fa:=res(coker a,LengthLimit=>3);    
          b:=fa.dd_2;    
          c:=submatrix(fa.dd_3,{0..3},{0..3});     
          alpha:=beilinson(c,S);     
          beta:=beilinson(b,S);     
	  h:=prune homology(beta,alpha);     
          if rank h===1 then (      
	       phi:=transpose presentation h;     
               fphi:=res coker phi;     
               I:=ideal(flatten fphi.dd_2);
	       if codim I===2 and degree I===12 then (
		    singI:=minors(2,jacobian I)+I;
		    if codim singI===5 then (
			 isSmooth=true;
			 );
		    );
	       );
	  i=i+1;
	  collectGarbage();
	  );
     "B2" << b << close;
--     print("used"|substring(toString(engineMemory()),0,38));
     I)

-- Adjunction process
-- 1st

firstAdjoint=(a)->(
     S:=ring a;
     omega:=Ext^1(a,S); 
     << betti omega << endl;
     n1:=rank target presentation omega;
     n2:=rank source presentation omega;
     K:=coefficientRing S;
     y:=symbol y;
     U1:=K[x_0..x_4,y_0..y_(n1-1)];
     b:=substitute(presentation omega,U1);
     c:=matrix{{y_0..y_(n1-1)}}*map(U1^{n1:-1},U1^{n2:-2},b);
     x1:=ideal(c):ideal(x_4);
     << betti x1 << endl;
     h0':=substitute(c,matrix{{0,x_1..x_4,y_0..y_(n1-1)}});
     h1':=substitute(c,matrix{{x_0,0,x_2..x_4,y_0..y_(n1-1)}});
     h2':=substitute(c,matrix{{x_0,x_1,0,x_3,x_4,y_0..y_(n1-1)}});
     h3':=substitute(c,matrix{{x_0..x_2,0,x_4,y_0..y_(n1-1)}});
     --h4':=substitute(c,matrix{{x_0..x_3,0,y_0..y_(n1-1)}});
     h0:=ideal(h0'):ideal(x_4);
     h1:=ideal(h1'):ideal(x_4);
     h2:=ideal(h2'):ideal(x_4);
     h3:=ideal(h3'):ideal(x_4);
     S1:=K[y_0..y_(n1-1)];
     H0:=substitute(h0,S1);
     H1:=substitute(h1,S1);
     H2:=substitute(h2,S1);
     H3:=substitute(h3,S1);
     H:=ideal(gens H0,gens H1,gens H2,gens H3);
     <<"-- # of (-1)-curves="<<degree H<<endl;
     X1:=trim substitute(x1,S1)
     );

tangentSpaceOfDeg12Surfs=(T)->(
     alpha:=submatrix(T.dd_4,{5..7},{0..3});
     beta:=T.dd_5;
     alphaf:=flatten alpha;
     betaf:=flatten beta;
     n1:=(tally degrees source alphaf)_{1};
     n2:=(tally degrees source alphaf)_{2};
     m1:=(tally degrees source betaf)_{1};
     m2:=(tally degrees source betaf)_{2};
     a:=symbol a;
     b:=symbol b;
     c:=symbol c;
     d:=symbol d;
     K:=coefficientRing ring T;  
     R:=K[a_0..a_(n1-1),b_0..b_(n2-1),c_0..c_(m1-1),d_0..d_(m2-1),e_0..e_4,
	  Degrees=>{n1:1,n2:2,m1:1,m2:2,5:1},SkewCommutative=>true];
     salpha:=substitute(alpha,R);
     sbeta:=substitute(beta,R);
     alpha':=map(target salpha,source salpha,
	  {{a_0,a_1,b_0,b_2},{a_2,a_3,b_2,b_2},{a_4,a_5,b_4,b_5}});
     beta':=map(target sbeta,source sbeta,
	  {{c_0..c_3},{c_4..c_7},{d_0..d_3},{d_4..d_7}});
     gamma:=map(flatten (salpha*beta'+alpha'*sbeta));
     delta:=substitute(contract(matrix{{a_0..a_(n1-1),b_0..b_(n2-1),c_0..c_(m1-1),d_0..d_(m2-1)}},transpose gamma),E);
     mu:=syz(delta,DegreeLimit=>1);
     bmu:=basis(1,image mu);
     r:=rank source bmu;
     tangent:=mu*map(source mu,E^r,bmu);
     << "-- Dimension=" << rank source tangent <<endl;
     tangent);


------------------------------------
-- monadConstruction ---------------
------------------------------------

-- makeSystemOfEquations: This function makes the homogeneous 
-- system of 140 linear equations with 120 unknowns from maps 
-- A_1:4E(3)->2E(1) \oplus 2E(2) and B_1:2E(1) \oplus 2E(2)->3E.  
-- This also returns B:2E(2) \oplus 2E(1)->3E with 60 unknowns 
-- whose linear part is B_1: 
 
makeSystemOfEquations=(mor1,mor2)->(
     use T;
     phi11:=matrix{{a_(0,0)..a_(0,9)}}*transpose substitute(basis(2,E),T);
     phi12:=matrix{{a_(1,0)..a_(1,9)}}*transpose substitute(basis(2,E),T);
     phi21:=matrix{{a_(2,0)..a_(2,9)}}*transpose substitute(basis(2,E),T);
     phi22:=matrix{{a_(3,0)..a_(3,9)}}*transpose substitute(basis(2,E),T);
     phi31:=matrix{{a_(4,0)..a_(4,9)}}*transpose substitute(basis(2,E),T);
     phi32:=matrix{{a_(5,0)..a_(5,9)}}*transpose substitute(basis(2,E),T);
     phi2:=(phi11|phi12)||(phi21|phi22)||(phi31|phi32);
     phi:=mor1|phi2;
     psi11:=matrix{{b_(0,0)..b_(0,9)}}*transpose substitute(basis(2,E),T);
     psi12:=matrix{{b_(1,0)..b_(1,9)}}*transpose substitute(basis(2,E),T);
     psi13:=matrix{{b_(2,0)..b_(2,9)}}*transpose substitute(basis(2,E),T);
     psi14:=matrix{{b_(3,0)..b_(3,9)}}*transpose substitute(basis(2,E),T);
     psi21:=matrix{{b_(4,0)..b_(4,9)}}*transpose substitute(basis(2,E),T);
     psi22:=matrix{{b_(5,0)..b_(5,9)}}*transpose substitute(basis(2,E),T);
     psi23:=matrix{{b_(6,0)..b_(6,9)}}*transpose substitute(basis(2,E),T);
     psi24:=matrix{{b_(7,0)..b_(7,9)}}*transpose substitute(basis(2,E),T);
     psi2:=(psi11|psi12|psi13|psi14)||(psi21|psi22|psi23|psi24);
     psi:=psi2||mor2;
     basisE:=substitute(basis(3,E),T);
     gamma:=phi*psi;
     gamma0:=contract(basisE,transpose gamma);
     {trim ideal gamma0,phi}
     )

-- checkRationalNormalCurve: This checks whether a map 
-- 4E(3)->2E(2) \oplus 2E(1) chosen at random satisfies 
-- the following conditions: 
--
-- (c1) the corresponding curve C in P(V) is smooth; 
-- (c2) C does not intersect X. 

checkRationalNormalCurve=(mat)->(
     normal:=minors(2,substitute(mat,E'));
     codim(normal+scroll)===5 
     and codim(minors(3,jacobian normal)+normal)===5
     );

-- equationOfParameters: This is a function for finding a map 
-- A_1:4E(3)->2E(2) satisfying Conditions (c1) and (c2)  whose  
-- homogeneous system has N_{A_1}=num linear equations 
-- by using Commands makeSystemOfEquations and 
-- checkRationalNormalCurve. Then this solves the 
-- homogeneous system for a_i's by computing 
-- the Groebner basis in terms of GLex.  This function also returns 
-- B:2E(2) \oplus 2E(1)->3E with 60 unknowns 
-- whose linear part is B_1:

equationsOfParameters=(num)->(
     i:=0;
     isCurve:=false;
     while not isCurve do (
 --          ran:=map(T^{2:-1},T^{2:-3},{{e_3,e_1-e_4+e_0-e_3},
 --          {e_4,e_1-e_4-e_0+e_3}})|
           ran:=mt | sub(random(E^{2:-2},E^{2:-3}),T);
           if checkRationalNormalCurve(ran)==true then (
           G:=(makeSystemOfEquations(phi1,ran));
           if num===numgens (G#0) then (
                     isCurve=true;
                     G':=substitute(G#0,R);
                     stdG':=ideal selectInSubring(1,gens gb G');
                     );
                 );
           i=i+1;
           collectGarbage();
           );
   {stdG',G#1})

-- substitution: this replaces the leading variables in terms of 
-- the parameters.  

substitution=(idl,mat)->(
     i:=0;
     ngens:=numgens idl;
     mt:=mat;
     idl':=substitute(ideal(0),T);
     while i<ngens do (
           lead:=leadTerm (gens idl)_{i};
           rest:=lead-(gens idl)_{i};
           idl'=idl'+ideal(rest);
           mt=substitute(mt,lead_(0,0)=>rest_(0,0));
           i=i+1;
           collectGarbage();
           );
      mt)

-- parameters: This determines free variables of 
-- the homogeneous system computed by equationOfParameters. 

parameters=(idl)->(
     i:=0;
     ngens:=numgens idl;
     monomial:=substitute(ideal(0),T);
     while i<ngens do (
          lead:=leadTerm (gens idl)_{i};
          rest:=lead-(gens idl)_{i};
          term:=terms rest_(0,0);
          monomial=monomial+substitute(ideal(term),T);
          i=i+1;
          collectGarbage();
          );
      trim monomial)
     
-- substituteIntoMap: This returns the matrix obtained from the matrix B 
-- by random choices of values for the parameters determined 
-- by the function parameters:

substitutionIntoMap=(idl,mor)->(
     i:=0;
     ngens:=numgens idl;
     ran:=substitute(random(R^1,R^ngens),T);
     while i<ngens do (
           mor=substitute(mor,(gens idl)_(0,i)=>ran_(0,i));
           i=i+1;
           collectGarbage();
           );
     mor)

-- randomSmoothSurface: This computes the ideal of a smooth surface of degree 12,  
-- sectional genus 13 and euler characteristic 1 corresponding to N_{A_1}=num. 

randomSmoothSurface=(num)->(
     i:=0;
     isSmooth:=false;
     while not isSmooth do (
         << "i = " << i << endl;
           eq:=equationsOfParameters(num);
           mor:=substitution(substitute(eq#0,T),eq#1);
           par:=parameters(substitute(eq#0,T));
           mor':=substitutionIntoMap(par,mor);
           use E;
           alpha':=map(E^{3:0},E^{2:-1,2:-2},substitute(mor',E));
           falpha':=res(coker alpha',LengthLimit=>2);
           if (tally degrees source falpha'.dd_2)_{2}===0 
           and (tally degrees source falpha'.dd_2)_{3}===4 
           then (
               alpha0:=alpha';
               beta0:=submatrix(falpha'.dd_2,{0..3},{0..3});
               ringP4:=KK[x_0..x_4];
               alpha0':=beilinson(alpha0,ringP4);
               beta0':=beilinson(beta0,ringP4);
               presentationY:=prune homology(alpha0',beta0');
               if rank presentationY===1 then (
                       ftpresentationY:=res coker transpose presentation presentationY;
                       idealX:=saturate ideal ftpresentationY.dd_2;
                       if codim idealX==2 and degree idealX==12 then (
                             cod:=codim singularLocus idealX;
                             if cod===5 then ( 
                                  isSmooth=true;
                                  );
                             );
                       );
               );
          i=i+1;
          collectGarbage();
          );
     "A1" << submatrix(falpha'.dd_2,{2,3},{0..3}) << close;
 --    print("used"|substring(toString(engineMemory()),0,38));
     idealX)


end-----------------------------------------

restart
needs "mes-rewrite.m2"
--needsPackage "TateOnProducts"
needsPackage "SurfacesInP4"

kk = ZZ/5;
E = kk[e_0..e_4, SkewCommutative=>true];
S = kk[x_0..x_4]; 

--- Example of Hiro Abo, 2004.
--- smooth surface in P^4, degree 12, sec genus 13 over ZZ/5, Construction I.


-- define the map 2E(2) \oplus 2E(1)->3E 
-- and compute the cokernel of this map

B1=map(E^{3:0},E^{2:-1},{{e_0,e_1},{e_1,e_2},{e_3,e_4}});
B1t=transpose B1;
fB1t=res (coker B1t,LengthLimit=>2);     
betti fB1t
g=transpose fB1t.dd_2;
fg=res (coker g, LengthLimit=>2);
betti fg

elapsedTime numberOfGoodMorForDeg12Surf(5^4*10, g)
--              0 1 2  3
-- Tally{total: 4 3 4 10 => 1 }
--          -2: 4 . .  .
--          -1: . 3 2  .
--           0: . . 2  4
--           1: . . .  6
--              0 1 2  3
--       total: 4 3 4 14 => 11
--          -2: 4 . .  .
--          -1: . 3 2  .
--           0: . . 2  4
--           1: . . . 10
--              0 1 2 3
--       total: 4 3 4 9 => 16
--          -2: 4 . . .
--          -1: . 3 2 .
--           0: . . 2 4
--           1: . . . 5

time idealX=idealOfDeg12Surf(5,13);
get "B2"

time idealX1=firstAdjoint(idealX);

use S
time T=tateResolution(syz gens idealX,E,3,7);
betti T

-- or maybe use this:
cohomologyTable(syz gens idealX, E, 3, 7)

time Z=tangentSpaceOfDeg12Surfs(T);


-------------------------------------------
-- Construction II ------------------------
-------------------------------------------
-- Construct smooth rational surfaces in P^4 with degree 12 and 
-- sectional genus 13 over F_5 by Construction II. 

restart
needs "mes-rewrite.m2"
--needsPackage "TateOnProducts"
--needsPackage "SurfacesInP4"
 
KK=ZZ/5;
E=KK[e_0..e_4,SkewCommutative=>true];

R=KK[b_(0,0)..b_(7,9),a_(0,0)..a_(5,9),MonomialOrder=>Eliminate 80];
T=KK[b_(0,0)..b_(7,9),a_(0,0)..a_(5,9),e_0..e_4,Degrees=>{140:2,5:1},
           SkewCommutative=>true];

use T

-- Fix a map from 2E(2) \oplus 2E(1) to 3E: 

phi1=map(T^{3:0},T^{2:-1},{{e_0,e_1},{e_1,e_2},{e_3,e_4}})

-- Define the homogeneous coordinate ring of P(V): 

E'=KK[e_0..e_4];

-- Compute the ideal of the rational cubic scroll X corresponding 
-- to phi1:

scroll=minors(2,substitute(phi1,E'));

use T
mt = map(T^{2:-1},T^{2:-3},{{e_3,e_1-e_4+e_0-e_3},{e_4,e_1-e_4-e_0+e_3}})

N = 117 -- 113 <= N <= 117
elapsedTime randomSmoothSurface N
elapsedTime I117 = randomSmoothSurface 117; -- infinity many 6-secants?
  minimalBetti I117
  Iquintics = ideal select(I117_*, f -> first degree f == 5);
  Iquintics : I117
  degree oo, codim oo
elapsedTime I116 = randomSmoothSurface 116; -- has 1 6-secant
  minimalBetti I116
  Iquintics = ideal select(I116_*, f -> first degree f == 5);
  Iquintics : I116
  degree oo, codim oo
elapsedTime I115 = randomSmoothSurface 115; -- has 2 6-secants
  minimalBetti I115
  Iquintics = ideal select(I115_*, f -> first degree f == 5);
  Iquintics : I115
  degree oo, codim oo


  
R = ring I115  
phi = map(R, R, for i from 1 to 5 list random(1, R))
inI = monomialIdeal phi I115
isBorel inI
o64
minimalBetti o64
see o64
