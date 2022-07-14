-- Construction of a surface in P4:
-- rational, degree 11, sectional genu s 11
-- 2 six-secants.  OVER ZZ/2...

-- construct a surface over F_2 using frobenius orbits
-- define coordinate ring of P^2 over F_2
F2 = GF(2)
S2 = F2[x,y,z]

-- define coordinate ring of P^2 over F_2^14 and F_2^5
St = F2[x,y,z,t]
use St; I14 = ideal(t^14+t^13+t^11+t^10+t^8+t^6+t^4+t+1); S14 = St/I14
use St; I5 = ideal(t^5+t^3+t^2+t+1); S5 = St/I5
-- the points
use S2; P = matrix{{0_S2, 0_S2, 1_S2}}
use S14;Q = matrix{{t^11898, t^137, 1_S14}}
use S5; R = matrix{{t^6, t^15, 1_S5}}
-- their ideals
IP = ideal ((vars S2)*syz P)
IQ = ideal ((vars S14)_{0..2}*syz Q)
IR = ideal ((vars S5)_{0..2}*syz R)
-- their orbits
f14 = map(S14/IQ,S2); Qorbit = ker f14
degree Qorbit -- degree = 14
f5 = map(S5/IR,S2); Rorbit = ker f5
degree Rorbit -- degree = 5


-- ideal of 3P
P3 = IP^3;
-- orbit of 2Q
f14square = map(S14/IQ^2,S2); Q2orbit = ker f14square;
-- ideal of 3P + 2Qorbit + 1Rorbit
I = intersect(P3,Q2orbit,Rorbit);
-- extract 9-tics
H = super basis(9,I)
rank source H -- affine dimension = 5
-- count basepoints (with multiplicities)
degree ideal H -- degree = 53
-- construct map to P^4
T = F2[x0,x1,x2,x3,x4]
fH = map(S2,T,H);
-- calculate the ideal of the image
Isurface = ker fH;

-- check invariants
betti res coker gens Isurface
codim Isurface -- codim = 2
degree Isurface -- degree = 11
genera Isurface -- genera = {0,11,10}
sectionalGenus Isurface == 11

-- check smoothness
J = jacobian Isurface;
mJ = minors(2,J) + Isurface;
codim mJ -- codim = 5
-- count 6-secants
-- ideal of 1 quartic and 5 quintics
Iquintics = ideal (mingens Isurface)_{0..5};
-- calculate the extra components where these vanish
secants = Iquintics : Isurface;
codim secants -- codim = 3
degree secants -- degree = 2
secantlist = decompose secants -- two components
-- check number of intersections
degree (Isurface+secantlist#0) -- degree = 6
codim (Isurface+secantlist#0) -- codim = 4
degree (Isurface+secantlist#1) -- degree = 6
codim (Isurface+secantlist#1) -- codim = 4
