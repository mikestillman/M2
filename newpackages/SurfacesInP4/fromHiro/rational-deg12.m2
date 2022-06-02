restart 
sortedBasis=(i,E)->(
     m:=basis(i,E);
     p:=sortColumns(m,MonomialOrder=>Descending);
     m_p);
beilinson1=(e,dege,i,S)->(
     E:=ring e;
     mi:=if i<0 or i>=numgens E then map(E^1,E^0,0) 
     else if i===0 then id_(E^1) 
     else sortedBasis(i+1,E);
     r:=i-dege;
     mr:=if r<0 or r>=numgens E then map(E^1,E^0,0) 
     else sortedBasis(r+1,E);
     s:=numgens source mr;
     if i===0 and r===0 then 
     substitute(map(E^1,E^1,{{e}}),S) 
     else if i>0 and r===i then substitute(e*id_(E^s),S) 
     else if i>0 and r===0 then 
     (vars S)*substitute(contract(diff(e,mi),transpose mr),S)
     else substitute(contract(diff(e,mi),transpose mr),S));
U=(i,S)->(
     if i<0 or i>=numgens S then S^0 
     else if i===0 then S^1 
     else coker koszul(i+2,vars S)**S^{i});
beilinson=(o,S)->(
     coldegs:=degrees source o;
     rowdegs:=degrees target o;
     mats=table(numgens target o,numgens source o,
	  (r,c)->(
	       rdeg=first rowdegs#r;
	       cdeg=first coldegs#c;
	       overS=beilinson1(o_(r,c),cdeg-rdeg,cdeg,S);
	       map(U(rdeg,S),U(cdeg,S),overS)));
     if #mats===0 then matrix(S,{{}})
     else matrix(mats));


-- Hirotachi Abo, September 9, 2004 
-- construct a smooth surface in P^4 with degree 12 and 
-- sectional genus 13 over F_5 by Constrution I.

-- Define the exterior algebra with variables e_0..e_4 over F_5

KK=ZZ/5;
E=KK[e_0..e_4,SkewCommutative=>true];

-- define the map 2E(2) \oplus 2E(1)->3E 
-- and compute the cokernel of this map

B1=map(E^{3:0},E^{2:-1},{{e_0,e_1},{e_1,e_2},{e_3,e_4}});
B1t=transpose B1;
fB1t=res (coker B1t,LengthLimit=>2);     
betti fB1t
g=transpose fB1t.dd_2;
fg=res (coker g, LengthLimit=>2);
betti fg

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
numberOfGoodMorForDeg12Surf=(N)->(     
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
numberOfGoodMorForDeg12Surf(5^4*10)

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

-- define the homogeneous coordinate ring of P^4 over F_5 

S=KK[x_0..x_4]; 

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
time idealX=idealOfDeg12Surf(5,13);
get "B2"

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
time idealX1=firstAdjoint(idealX);



-- Tangent space 
needsPackage "Truncations"
symExt=(m,E) -> (
     ev:=map (E,ring m, vars E);
     mt:=transpose jacobian m;
     jn:=gens kernel mt;
     q:=vars(ring m)**id_(target m);
     ans:=transpose ev(q*jn);
     map (E^{(rank target ans):1},E^{(rank source ans):0},ans));
bgg=(i,M,E)->(
     S:=ring(M);
     numvarsE:=rank source vars E;
     ev:=map(E,S,vars E);
     f0:=basis(i,M);
     f1:=basis(i+1,M);
     g:=((vars S)**f0)//f1;
     b:=(ev g)*((transpose vars E)**(ev source f0));
     map(E^{(rank target b):i+1},E^{(rank source b):i},b)
     );
tateResolution=(m,E,loDeg,hiDeg)->(
     M:=coker m;
     reg:=regularity M;
     bnd:=max(reg+1,hiDeg-1);
     mt:=presentation truncate (bnd,M);
     o:=symExt(mt,E);
     ofixed:=map(E^{(rank target o):bnd+1},E^{(rank source o):bnd},o);
     res (coker ofixed, LengthLimit=>max(1,bnd-loDeg+1))
     );

use S
time T=tateResolution(syz gens idealX,E,3,7);
betti T
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
time Z=tangentSpaceOfDeg12Surfs(T);

     
     

     
     
