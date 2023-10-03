document {
     Key => bFunction,
     Headline => "b-function",
     UL {
	  {TO (bFunction, LeftIdeal,List), " - for an ideal"},
	  {TO (bFunction, Module,List,List), " - for a module"}  
	  }
     }

document {
     Key => {
	 [bFunction,Strategy],
	 NonGeneric,
     	 TryGeneric,
     	 IntRing
	 },
     Headline => "specify strategy for computing b-function",
     UL { 
	  {BOLD "IntRing", " -- the simplest algorithm available. 
     	       The idea is to compute ", EM "in", SUB "(-w,w)", EM "(I) ", "
     	       intersect it with ", 
	       EM {"k[t", SUB "1", ",...,t", SUB "n", "]"}, 
	       "(", EM {"t", SUB "i", " = x", SUB "i", "D", SUB "i"}, ")",
     	       "Call the ideal obtained ", EM "J", ". 
	       Finally ", 
	       EM {"J + (t", SUB "1", 
		    " + ... + t", SUB "n", "- s) \\cap k[s]"},
	       " is generated by the b-function that we are looking for."
	       },
	  {BOLD "TryGeneric", " -- checks whether the ideal is generic 
	       and if that is the case uses Alg.5.1.5 
	       in Saito-Sturmfels-Takayama (1999) otherwise is equivalent 
	       to ", TT "NonGeneric",
     	       },
	  {BOLD "NonGeneric", 
	       " -- uses 5.1.6 in Saito-Sturmfels-Takayama (1999)"
	       },
	  {"Default:", BOLD "IntRing"}
	  }
     }

document {
     Key => (bFunction, LeftIdeal, List),
     Headline => "b-function of an ideal",
     Usage => "b = bFunction(I,w)",
     Inputs => {
	  "I" => {"a holonomic ideal in the Weyl algebra ", 
	       EM {"A", SUB "n", "(K)"}, "."},
	  "w" => {"a list of integer weights corresponding 
	       to the differential variables in the Weyl algebra."}
	       },
    Outputs => {
	  "b" => {"a polynomial ", EM "b(s)", " which is the b-function of ", 
	       EM "I", " with respect to ", EM "w"}
	  },
     "Use ", TO "setHomSwitch", "(true) to force all the subroutines 
     to use homogenized ", TO "WeylAlgebra",
     PARA {  
	  BOLD "Definition. ", "The b-function ", EM "b(s)", 
	  " is defined as the monic generator  
	  of the intersection of ", 
	  EM {"in", SUB "(-w,w)", "(I)"}, " and ", 
	  EM "K[s]",
	  ", where ", 
	  EM {"s = [w", SUB "1", "t", SUB "1", " + ... + w", 
	       SUB "n", "t", SUB "n", "]"}, 
	  " (here ", EM {"t", SUB "i", " = x", SUB "i", "D", SUB "i"}, ")."}, 
     EXAMPLE {
	  "R = QQ[x_1,x_2,D_1,D_2,WeylAlgebra=>{x_1=>D_1,x_2=>D_2}]",
     	  "I = ideal(x_1, D_2-1)",
     	  "bFunction(I,{1, 0})",
     	  },
     Caveat => {
	  "The ring of I should not have any parameters: 
     	  it should be a pure Weyl algebra. Similarly, this ring 
	  should not be a homogeneous ", TO "WeylAlgebra"
	  },
     SeeAlso => { "globalBFunction", "factorBFunction" }
     }

document {
     Key => (bFunction, Module, List, List),
     Headline => "b-function of a holonomic D-module",
     Usage => "b = bFunction(M,w,m)",
     Inputs => {
	  "M" => {"a holonomic module over a Weyl algebra ", 
	       EM {"A", SUB "n", "(K)"}},
	  "w" => {"a list of integer weights corresponding 
	       to the differential variables in the Weyl algebra"},
	  "m" => {"a list of integers, each of which is 
	       the shift for the corresponding component"}
	       },
     Outputs => {
	  "b" => {"a polynomial ", EM "b(s)", " which is the b-function of ", 
	       	EM "M", " with respect to ", EM "w", 
	       	" and ", EM "m"}
	  },
     "The algorithm represents ", EM "M", " as ", EM "F/N", 
     " where ", EM "F", " is free and ", 
     EM "N", " is a submodule of ", EM "F", ". 
     Then it computes b-functions ", EM {"b", SUB "i", "(s)"}, 
     " for ", EM {"N \\cap F", SUB "i"}, " (i-th component of ", EM "F", 
     ") and outputs ",
     EM {"lcm{ b", SUB "i", "(s-m", SUB "i",") }"},
     EXAMPLE{
	  "R = QQ[x, dx, WeylAlgebra => {x=>dx}]",
	  "M = cokernel matrix {{x^2, 0, 0}, {0, dx^3, 0}, {0, 0, x^3}}",
	  "factorBFunction bFunction(M, {1}, {0,0,0})",
	  "factorBFunction bFunction(M, {1}, {1,2,3})"
     	  },
     Caveat => {
	  "The Weyl algebra should not have any parameters. 
     	  Similarly, it should not be a homogeneous Weyl algebra"
	  },
     SeeAlso => { "globalBFunction", "factorBFunction" }
     }


document {
     Key => {
	 [globalBFunction,Strategy],
	 ViaAnnFs,
     	 ReducedB
	 },
     Headline => "specify strategy for computing global b-function",
     UL { 
	  {BOLD "IntRing, TryGeneric, NonGeneric", 
	       " -- passed to ", TO "bFunction",  ", see ", 
	       TO [bFunction,Strategy] },
	  {BOLD "ViaAnnFs", " -- computes ", 
	       EM "J(s)=Ann(f", SUP "s", EM ")", " and then intersects ", 
	       EM "J(s)+D[s]f}", " with ", EM "K[s]"},
	  {BOLD "ReducedB", " -- computes ", EM "b(s)/(s+1)", 
	       " by taking the intersection of ",
	       EM "J(s)+D[s](f,df/dx1,...,df/dxn)", " with ", EM "K[s]",
	       ", then multiplies by ", EM "s+1", "."},
	  {BOLD "GeneralBernsteinSato", " -- calls ", TO "generalB", "{f}."},
	  {"Default: ", BOLD "GeneralBernsteinSato"}
	  }
     }

document { 
     Key => {(globalBFunction,RingElement), globalBFunction},
     Headline => "global b-function (else known as the Bernstein-Sato polynomial)",
     Usage => "b = globalBFunction f",
     Inputs => {
	  "f" => {"a polynomial"}
	  },
     Outputs => {
	  "b" => RingElement => {"the b-function ", EM "b(s)",  " in ", EM "Q[s]"}
	  },
     PARA {
	  BOLD "Definition. ", "Let ", 
	  EM "D = A_{2n}(K) = K<x_1,...,x_n,d_1,...,d_n>", 
	  " be a Weyl algebra. 
	  The Bernstein-Sato polynomial of a polynomial f is defined 
	  to be the monic generator of the ideal of all polynomials ", 
	  EM "b(s)", " in ", EM "K[s]", " such that
	  ", EM " b(s) f^s = Q(s,x,d) f^{s+1}", " where ", EM "Q", 
	  " lives in ", EM "D[s]."},
     PARA {
	  BOLD "Algorithm. ", 
	  "Let ", 
	  EM "I_f = D<t,dt>*<t-f, d_1+df/dx_1*dt, ..., d_n+df/dx_n*dt> ",
	  "Let ", EM "B(s) = bFunction(I, {1, 0, ..., 0})", 
	  " where 1 in the weight that corresponds to ", EM "dt. ", 
	  "Then the global b-function is ", EM "b_f = B(-s-1)"},
     EXAMPLE lines ///
	  R = QQ[x]
     	  f = x^10
    	  b = globalBFunction f
	  factorBFunction b
     	  ///,
     SeeAlso => { "bFunction", "factorBFunction", "generalB", "globalB" }
     }

document { 
     Key => {(generalB,List,RingElement), (generalB,List), generalB},
     Headline => "global generalized Bernstein-Sato polynomial",
     Usage => "b = generalB(F,g), b = generalB F",
     Inputs => {
	  "F" => {"a list of polynomials"},
	  "g" => {"a polynomial"}
	  },
     Outputs => {
	  "b" => RingElement => {"the general Bernstein-Sato polynomial ", 
	       EM "b(s)",  " in ", EM "Q[s]"}
	  },
     "Bernstein-Sato polynomial for an arbitrary affine variety was introduced in ",
     "Budur, Mustata, and Saito ", "``Bernstein--Sato polynomials of arbitrary varieties''. ",
     "If the option ", TO "Exponent", " is specified, then the m-generalized Bernstein-Sato polynomial is computed. ",
     "See ", EM "Berkesch and Leykin", " ``Algorithms for Bernstein-Sato polynomials and multiplier ideals'' for definitions.",     
     EXAMPLE lines ///
     W = makeWA(QQ[x_1..x_3]);
     factorBFunction generalB ({x_2^2-x_1*x_3, x_1^3-x_3^2}, x_2)
     ///,
     Caveat => {
	  "The input could be either in a polynomial ring or the Weyl algebra. In the latter case the algebra 
	  should not have any central variables and should not be a homogeneous Weyl algebra."
	  },
     SeeAlso => { "bFunction", "globalBFunction", "lct", "multiplierIdeal" }
     }
document {
     Key => {[generalB,Strategy], InitialIdeal, StarIdeal},
     Headline => "specify strategy for computing generalized Bernstein-Sato polynomial",
     UL { 
	  { BOLD "InitialIdeal", 
	       " -- use the initial ideal in_{(-w,w)} Ann f^s; this Strategy is the fastest on many examples, 
	       but can not be used with the ", TO "Exponent", " option." },
	  { BOLD "StarIdeal", 
	       " -- use ``star ideal'', the (-w,w) homogeneous elements of the Ann f^s"}
	  },
     "See ", EM "Berkesch and Leykin", " ``Algorithms for Bernstein-Sato polynomials and multiplier ideals''."
     }
document {
     Key => {[generalB,Exponent], Exponent},
     Headline => "specify exponent m for m-generalized Bernstein-Sato polynomial",
     "See ", EM "Berkesch and Leykin", " ``Algorithms for Bernstein-Sato polynomials and multiplier ideals''."
     }
document {
     Key => ViaLinearAlgebra,
     Headline => "an option for generalB=>Strategy",
     "see ", TO "generalB"
     } 
document { 
     Key => {(lct,Ideal), lct},
     Headline => "compute the log canonical threshold for an ideal",
     Usage => "l = lct I",
     Inputs => {
	  "I" => {"an ideal in a polynomial ring"}
	  },
     Outputs => {
	  "l" => RingElement => {"a rational number, the log canonical threshold of ", EM "I"}
	  },
     EXAMPLE lines ///
     QQ[x_1..x_3];
     I = ideal (x_2^2-x_1*x_3, x_1^3-x_3^2);
     lct I
     ///,
     SeeAlso => { "bFunction", "generalB" }
     }
document {
     Key => [lct,Strategy],
     Headline => "specify strategy for computing lct",
     UL { 
	  {BOLD "ViaBFunction", " -- use ", TO "bFunction" },
	  {BOLD "GeneralBernsteinSato", " -- use ", TO "globalB" }
	  }
     }
document {
     Key => GeneralBernsteinSato,
     Headline => "a strategy option for lct, globalBFunction",
     "see ", TO "lct", TO "globalBFunction", "."
     }
document {
     Key => ViaBFunction,
     Headline => "a strategy option for lct",
     "see ", TO "lct"
     }
document {
     Key => {(factorBFunction, RingElement),factorBFunction},
     Headline => "factorization of a b-function",
     Usage => "bFunction b",
     Inputs => {
	  "b" => {"a polynomial obtained via one of the b-function routines"}
	  },
     Outputs => {
	  Product => {"the factorization of ", TT "b"}
	  },
     BOLD "Fact. ", "The roots of any b-function are rational.",
     EXAMPLE {
	"R = QQ[x, dx, WeylAlgebra => {x=>dx}]",
     	  "f = x^10",
     	  "b = globalBFunction f",
     	  "factorBFunction b"
     	  },
     Caveat => {
	  "f should be an output of one of the b-function routines"
     	  },
     SeeAlso => { 
	  "bFunction",
	  "globalBFunction"
	  }
     }  

document {
     Key => {(getIntRoots, RingElement), getIntRoots},
     Headline => "get integer roots of a b-function",
     Usage => "getIntRoots b",
     Inputs => {
     	  "b" => "the output of one of the b-function routines" 
	  },
     Outputs => {
	  List => {"the list of the integer roots of ", TT "b"}   
	  },
     SeeAlso => {"globalBFunction", "bFunction"}
     }

document {
     Key => {(bFunctionRoots, RingElement), bFunctionRoots},
     Headline => "get roots of a b-function",
     Usage => "bFunctionRoots b",
     Inputs => {
     	  "b" => "the output of one of the b-function routines" 
	  },
     Outputs => {
	  List => {"the list of the roots of ", TT "b"}   
	  },
     SeeAlso => {"globalBFunction", "bFunction", "generalB"}
     }

document {
     Key => {(globalB, LeftIdeal, RingElement), globalB},
     Headline => "compute global b-function and b-operator 
          for a D-module and a polynomial",
     Usage => "H = globalB(I,f)", 
     Inputs => {
	  "I" => {"a holonomic ideal"},
	  "f" => {"a polynomial in a Weyl algebra 
	       (should not contain differential variables)"}
	       },
     Outputs => {
	  "H" => HashTable => {"containing the keys ",  
	       TT "Bpolynomial", " and ", TT "Boperator"}
	  },
     "The algorithm used here is a modification of the original
     algorithm of Oaku for computing Bernstein-Sato polynomials",
     EXAMPLE lines ///
	  R = QQ[x, dx, WeylAlgebra => {x=>dx}]
     	  f = x^7
     	  b = globalB(ideal dx, f)
     	  factorBFunction b.Bpolynomial 
     	  ///,
     SeeAlso => { "bFunction", "globalBFunction", "factorBFunction" }
     }  
document {
     Key => Boperator,
     Headline => "a key attached by globalB and Dlocalize",
     SeeAlso => { "globalB", "Dlocalize" }
     }
document {
     Key => Bpolynomial,
     Headline => "a key attached by globalB",
     "see ", TO "globalB"
     }
document {
     Key => {(globalBoperator, RingElement), globalBoperator},
     Headline => "compute a b-operator of a polynomial",
     SeeAlso => {"globalB"}
     } 

document { 
     Key => {(localBFunction,RingElement,LeftIdeal), localBFunction},
     Headline => "local b-function (a.k.a. the local Bernstein-Sato polynomial)",
     Usage => "b = localBFunction(f,P)",
     Inputs => {
	  "f" => {"a polynomial"},
	  "P" => {"a (prime) ideal"}
	  },
     Outputs => {
	  "b" => RingElement => {"the local b-function ", EM "b_P(s)",  " in ", EM "Q[s]"}
	  },
     PARA {
	  "Computes the local b-function of f at P, if P is a prime ideal."
	  },
     Caveat => {"(feature) If P is not prime, computes the 
	  lcm of local b-functions over all primes containing P"},
     	  EXAMPLE lines ///
	  R = QQ[x,y]; f = x^2*(x+y+1); P = ideal(x,y);
    	  b = localBFunction(f,P)
	  factorBFunction b
     	  ///,
     SeeAlso => { "bFunction", "factorBFunction", "globalBFunction", "generalB", "globalB" }
     }

document {
     Key => {(paramBpoly, RingElement, File), paramBpoly},
     Headline => "compute the list of all possible Bernstein-Sato polynomials 
     for a polynomial with parametric coefficients",
     Usage => "paramBpoly(f,file)", 	  
     Inputs => {
     	  "f" => RingElement => {
	       "a polynomial in Weyl algebra ", EM "A_n(Q)"
	       },
	  "file" => File => {"a file for TeX output (or stdio)"}
	  },
     Outputs => {
	  List => {"all possible Bernstein-Sato polynomials"}
	  },
     "Along with the finite list of B.-S. polynomials this function creates latex code 
     describing strata in the parameter space 
     corresponding to the B.-S. polynomials --- each stratum is a constructible set. ",     
     "This is an implementation of the algorithmic approach in ", 
     EM {"Anton Leykin. Constructibility of the Set of Polynomials with a Fixed Bernstein-Sato Polynomial: an Algorithmic Approach. 
     Journal of Symbolic Computation, 32(6):663–675, 2001."},
     EXAMPLE lines ///
	  A =  (QQ [a,b,c]) [x, y, Dx, Dy, WeylAlgebra => {x=>Dx, y=>Dy}]
     	  paramBpoly(a*x^2 + b*x*y + c*y^2, stdio)
	  ///,
     Caveat => {
	  "A finite field ZZ/p is used to speed up computations. 
	  Option ", TT {"\"ground field\""}," may be used to change the characteristic p.
	  If p=0 the computation will be attempted over QQ."
	  },
     SeeAlso => {"globalBFunction"}
     }  
