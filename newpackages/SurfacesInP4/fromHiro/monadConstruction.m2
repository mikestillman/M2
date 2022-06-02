
-- Construct smooth rational surfaces in P^4 with degree 12 and 
-- sectional genus 13 over F_5 by Construction II. 
 
KK=ZZ/5;
E=KK[e_0..e_4,SkewCommutative=>true];
R=KK[b_(0,0)..b_(7,9),a_(0,0)..a_(5,9),MonomialOrder=>Eliminate 80];
T=KK[b_(0,0)..b_(7,9),a_(0,0)..a_(5,9),e_0..e_4,Degrees=>{140:2,5:1},
           SkewCommutative=>true];

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
use T

-- Fix a map from 2E(2) \oplus 2E(1) to 3E: 

phi1=map(T^{3:0},T^{2:-1},{{e_0,e_1},{e_1,e_2},{e_3,e_4}})

-- Define the homogeneous coordinate ring of P(V): 

E'=KK[e_0..e_4];

-- Compute the ideal of the rational cubic scroll X corresponding 
-- to phi1:

scroll=minors(2,substitute(phi1,E'));

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

use T
mt = map(T^{2:-1},T^{2:-3},{{e_3,e_1-e_4+e_0-e_3},{e_4,e_1-e_4-e_0+e_3}})

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
