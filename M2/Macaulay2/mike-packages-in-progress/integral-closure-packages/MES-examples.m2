-- Nov 2013, trying to get this code up

-- LocalBasis
restart
loadPackage "LocalBasis"
loadPackage "IntegralBases"

TEST ///
kk = ZZ/2
R1 = kk[y,x,MonomialOrder=>{1,1}]
P = x^3+x^2+1
F = y^3*(y-1) + P^2*y + P^3
factorize discriminant(F,y)
localBases(F, PrintLevel=>3)
G = numerator(x^12 * sub(F, {x => 1/x, y => y/x^3}))
localBases(G, PrintLevel=>3)
///

kk = ZZ/13
R1 = kk[y,x,MonomialOrder=>{1,1}]
F = y^5-x^2
G = numerator(sub(F, {x => 1/x, y => y/x}))
localBases(F, PrintLevel=>3)
localBases(G, PrintLevel=>3)

R2 = kk[x,y,z]
Fh = homogenize(sub(F,R2), z)
P3 = kk[a,b,c,d]
map(R2/Fh, P3, super basis(2, intersect(ideal(x,y), ideal(y,z))))
J = kernel oo
radical (J + minors(2,jacobian J))

P5 = kk[a,b,c,d,e,f]
map(R2/Fh, P5, {x*z^3, x^2*z^2, x*y*z^2, x*y^2*z, y^3*z, y^4})
J = ker oo
J = trim J
singJ = trim(J + minors(4, jacobian J))
singJ = radical singJ
codim J
trim J
gens gb J
hilbertPolynomial(J, Projective=>false)

-- NEED: write localBasis using Puiseux/vH method.

R = QQ[x,y]
F = - x^3 + x^4 - 2*x^2*y - x*y^2 + 2*x*y^4 + y^5
puiseux(F, 10)
netList oo
sub(F, {y=>0})

R = QQ[x,y]
F = - x^3 + x^4 + x^2*y - x*y^2 + 2*x*y^4 + y^5
puiseux(F, 10)
netList oo
sub(F, {y=>0})

R = QQ[x,y]
F = y^5+2*x*y^2+2*x*y^3+x^2*y-4*x^3*y+2*x^6
puiseux(F, 10)
netList oo
factor discriminant(F,y)
