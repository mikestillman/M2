R=QQ[x,y,z];
I=ideal(x^6+x^3*z+y^3*z^2);
A=R/I;
time ic0=integralClosure(A,Verbosity=>6)
ic0
see ideal ic0

end--
----------------------------------------------------------
-- email from Doug Leonard, July 13, 2025, 8:28 pm
R=QQ[x,y,z];
I=ideal(x^6+x^3*z+y^3*z^2);
A=R/I;
time ic0=integralClosure(A,Verbosity=>6)
-- It looks like the fractions produced are:
-- w_(0,0)=y^2z/x
-- w_(1,0)=yz/x, w_(1,1)=y^2z/x^2,
-- so w_(0,0) is no longer necessary, 
-- w_(2,0)=(-x^3-z)/z
-- Please explain why w_(1,0) disappeared!
-- Doug

----------------------------------------------------------
-- Another email: 14 July 2025, 8:57 pm
loadPackage "QthPower";
wt=matrix{{19,15,12,9,9},{12,9,9,9,0}};
R=ZZ/2[z,y1,y2,x2,x1,Weights=>entries weightGrevlex(wt)];
I=ideal(
    y1^2-y2*x2*x1,
    y1*y2-y1-x2^2*x1-x2*x1^2,
    y2^2-y2-y1*(x2+x1),
    z^3-(y2+y1)*(x2+1)*x1*z-(y2*(x2*x1+1)-y1*(x2+x1))*x2^2*x1);
A=R/I;
time ic0=integralClosure(A,Verbosity=>6)
-- Again w_(1,0) and w_(1,1) are produced
-- then w_(2,0) and w_(2,1) are produced
-- but somehow w_(1,1) disappears


----------------------------------------------------------
--Did I ask you about this before?

R=QQ[y,x];
b=(y^12-4*y^10*x+6*y^8*x^2-4*y^6*x^3+8*y^5*x^7+y^4*x^4+8*y^3*x^8-x^13);
A=R/ideal(b)
time G=gens gb ideal integralClosure(A);
toString G
time icf=icFractions(A);
toString icf

--The outputs (below) are clearly a mess, and not even close to being correct. Do you know why this was the answer?
-- :
--  {{x^3, y^2*x^2, y^4-16*y^2*x, 1280*w_(4,0)-37*y^3*x+85072*y*x^2,
--      w_(4,1)*x, w_(4,1)*y-240*y*x^2, w_(4,4)*y, w_(4,4)*x^2-4*y^3*x+64*y*x^2,
--      w_(4,3)*y-w_(4,4)*x+4*y^3-64*y*x, w_(4,3)*x^2, w_(4,2)*x-4000*y*x^2,
--      4*w_(4,2)*y+5*w_(4,3)*x-320*x^2, w_(4,1)^2,
--      w_(4,1)*w_(4,4)-952*y^3*x+15232*y*x^2, w_(4,1)*w_(4,3), w_(4,1)*w_(4,2),
--      w_(4,4)^2, w_(4,3)*w_(4,4)-256*w_(4,4)*x+768*y^3-12288*y*x,
--      w_(4,2)*w_(4,4), w_(4,3)^2-512*w_(4,3)*x-6144*w_(4,1)-256*y^2*x+1478656*x^
--      2, 2*w_(4,2)*w_(4,3)+52885*y^3*x-1357520*y*x^2, w_(4,2)^2}}

i6 : time icf=icFractions(A);
 -- used 1.3294e-05s (cpu); 9.17e-06s (thread); 0s (gc)

i7 : toString icf

o7 = {(37*y^3*x-85072*y*x^2)/1280,
     (y^3*x^6+5*y*x^7+96*y^2*x^3+16*x^4)/(y^4+6*y^2*x+x^2),
     (25*y^11+200*y^4*x^7-225*y^9*x+200*y^2*x^8+1375*y^7*x^2-400*x^9-7975*y^5*x
     ^3-67600*y^3*x^4-11600*y*x^5)/(25*y^4*x^2+150*y^2*x^3+25*x^4),
     (328125*y^11+2625000*y^4*x^7-1115625*y^9*x+9712500*y^2*x^8+1194375*y^7*x^2
     +840000*x^9-721875*y^5*x^3+5040000*y^3*x^4+24360000*y*x^5-840000*y^4+
     13440000*y^2*x)/(65625*y^3*x^3+380625*y*x^4+210000*y^2),
     (5*y^9*x+40*y^2*x^8-46*y^7*x^2-68*x^9+285*y^5*x^3-1660*y^3*x^4-336*y*x^5
     )/(x^5+20*y^3+4*y*x), y, x}

------------------------------------------
-- git issue #1423 -- this one does crash on 32 bit build, out of memory.
restart
S = QQ[x,y]
f = ideal (y^4-2*x^3*y^2-4*x^5*y+x^6-x^7)
R = S/f
time R' = integralClosure(R, Strategy => Radical)
icFractions R

use S
f = ideal (y^4-2*x^3*y^2-4*x^5*y+x^6-x^7)
R = S/f
time R' = integralClosure R
icFractions R

use S
f = ideal (y^4-2*x^3*y^2-4*x^5*y+x^6-x^7)
R = S/f
time R' = integralClosure(R, Strategy => AllCodimensions)
icFractions R

needsPackage("Fields", FileName => "~/src/M2-current-branches/fields-m2/Fields.m2")
use S
S = QQ[y,x]
f = ideal (y^4-2*x^3*y^2-4*x^5*y+x^6-x^7)
R = S/f
F = field R
for alpha in icFractions R list sub(alpha, F)
use S
resultant(f_0, diff(y, f_0), y)
resultant(f_0, diff(x, f_0), x)
 *** out of memory trying to allocate 4672 bytes, exiting ***

 ----------------------------------------------------
 -- email from Doug 12 June 2024
 restart
 loadPackage "QthPower";
wt = matrix{{19,15,12,9,9},{12,9,9,9,0}};
R2 = ZZ/2[z19,y15,y12,x9,u9,Weights=>entries(weightGrevlex(wt))];
GB2 = {y15^2+y12*x9*u9,
       y15*y12+x9^2*u9+x9*u9^2+y15,
       y12^2+y15*x9+y15*u9+y12,
       z19^3+z19*(y15+y12)*(x9+1)*u9+(y15*(x9+u9)+y12*(x9*u9+1))*x9^2*u9};
time ic2 = qthIntegralClosure(wt,R2,GB2); toString(ic2)

A2=R2/ideal(GB2);

time icfp=icFracP A2;
toString icfp
--1(unnecessary),f2624,f2924,f3224 (should be f2315x99),f3430

time icf2=icFractions A2;
toString icf2
--f2624,f3430,f2315,(missing f2924),z1912,y159,y129,x99,u90

time G2=gens gb ideal integralClosure A2;
toString G2

icFractions A2
