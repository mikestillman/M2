-- The following is a simple routine which displays some basic
-- numerical invariants of a smooth projective surface.

-- The following formula for N6 is not correct!!
N6 = (d,secgenus,chi) -> (
    -- Le Barz 6-secant formula, if X is in P4.
    -- degree of a double curve of a generic projection to P3.
    delta := binomial(d-1,2) - secgenus;
    -- the number of triple points of this curve.
    t := binomial(d-1,3) - secgenus*(d-3) + 2*chi - 2;
    -- the number of apparent double points.
    << "t = " << t << endl;
    h := (delta * (delta - d + 2) - 3*t) // 2;
    -- N6: the value to be returned.
    - d*(d-4)*(d-5)*(d^3 + 30*d^2 - 577*d + 786) // 144
         + delta * ( 2*binomial(d,4) + 2*binomial(d,3) - 45*binomial(d,2) + 148*d - 317)
         - binomial(delta,2) * (d^2 - 27*d + 120) // 2
         - 2 * binomial(delta,3)
         + h * (delta - 8*d + 56) + t * (9*d - 3*delta - 28) + binomial(t,2)
    ) 
	
TEST ///
N6(10,9,1)  -- should be 7!!
-- for this: 
  d = 10
  secgenus = 9
  chi = 1
  delta = binomial(d-1,2) - secgenus                   -- 27
  t = binomial(d-1,3) - secgenus*(d-3) + 2*chi - 2     -- 21
  h = (delta * (delta - d + 2) - 3*t) // 2             -- 225
///
numinfo = method()
numinfo Ideal := (I) -> (
     if dim I =!= 3 then error "expected the ideal of a projective surface";
     -- We assume that V(I) is smooth, but we don't check it.
     -- We compute here the canonical module, although in general it is better
     --  to avoid this, or do it elsewhere.
     R := ring I;
     n := numgens R;
     c := codim I;
     -- basics
     d := degree I;
     secgenus := (genera coker gens I)#1;
     -- pg
     KX = Ext^c(coker gens I, R);
     KX = KX ** R^{-n};
     pg := numgens source basis(0,KX);
     -- q
     H1O = Ext^(c+1)(coker gens I, R);
     H1O = H1O ** R^{-n};
     q := numgens source basis(1,H1O);
     -- chi
     chi := 1 - q + pg;
     -- h11.  Currently this is time consuming
     -- unless X lies in P4.
     local K2, h11, eX;
     if n === 5 then (
	  HK := 2*secgenus - d - 2;
	  K2 = (d^2 - 10*d - 5*HK + 12*chi) // 2;
	  eX = 12*chi - K2;
	  h11 = eX - 2 + 4*q - 2*pg;
	  n6 = N6(d,secgenus,chi);
	  )
     else (
          X = Proj (R/I);
          Omega = cotangentSheaf X;
          H1Omega = HH^1(Omega);
          h11 = numgens source basis(0,H1Omega);
          eX = 2 - 4*q + (2*pg + h11);
          K2 = 12*chi - eX;
	  );
     << "degree    = " << d << endl;
     << "sec genus = " << secgenus << endl;
     << "irreg q   = " << q << endl;
     << "pg        = " << pg << endl;
     << "e(X)      = " << eX << endl;
     << "K^2       = " << K2 << endl;
     << "h11       = " << h11 << endl;
     << "chi       = " << chi << endl;
     if n === 5 then (
       << "N6        = " << n6 << endl;
       );
     )
     
///
numinfo I

R = ZZ/101[a..e]
J = ideal random(R^1, R^{-3,-3})
numinfo J
HH^1(cotangentSheaf Proj(R/J))
///
end--
load"numinvariants.m2"
