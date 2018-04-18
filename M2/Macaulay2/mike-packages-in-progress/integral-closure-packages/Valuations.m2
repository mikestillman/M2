liftFractions = method(Options => {
	  Variable => null
	  })
liftFractions(Ideal, RingElement, ZZ) := opts -> (P, f, n) -> (
     R := ring P;
     K := frac R;
     var := if opts.Variable === null then findVar(P,f) else opts.Variable;
     f' := promote(diff(var,f),K);
     f'inverse := f'^-1;
     x := promote(var, K);
     for i from 1 to n do (
	  fx := sub(f,var => x);
	  x = x - f'inverse * fx;
	  );
     map(K,K, for z in gens R list (if z == var then x else promote(z,K)))
     )

expansion = method(Options => {
	  NumSteps => 1
	  })
expansion(RingElement, RingElement, RingMap, Ideal) := opts -> (z, f, g, P) -> (
     n := opts.NumSteps;
     Q := P^(n+1);
     L = prepend(z, for i from 1 to n list (
	  print "calculating g(z)";
	  time z = z - g(z);
	  num := numerator z;
	  if num % f != 0 then error "numerator not divisible by f";
	  num = (num // f) % Q;
	  z = num / ((denominator z) % Q)
	  ));
     L / (i -> ((numerator i) % P)/((denominator i) % P))
     )

findVar = method()
findVar(Ideal, RingElement) := (P,f) -> (
     
     )

end
restart
load "Valuations.m2"
kk = QQ
R = kk[y, x, Degrees => {3,2}]
f = y^2 - x^3
P = ideal f
use R
n = 4
g = liftFractions(P,f,n, Variable => x)
K = frac R
x' = g(lift(x,K))
num = numerator x'
x' = (num % f^(n+1)) / denominator x'
g = map(K,K, {x => x'})
time E = expansion(x,f,g,P,NumSteps => n-1)
x - (sum apply(#E, i -> f^i * g(E#i)))
factor numerator oo

Rp = R/P
Kp = frac Rp
Kpt = Kp[T]/(T^n)
xt = sum for i from 0 to #E - 1 list sub(E#i, Kp) * T^i
yt = sub(y,Kp) * T^0
yt^2 - xt^3
