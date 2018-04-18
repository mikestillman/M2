newPackage(
        "MatrixNormalForms",
        Version => "0.1", 
        Date => "6 Nov 2009",
        Authors => {{Name => "Mike Stillman", 
                  Email => "mike@math.cornell.edu", 
                  HomePage => "http://www.math.cornell.edu/~mike"}},
        Headline => "toplevel and engine implementation of various normal forms for matrices",
        DebuggingMode => true
        )

export {
    "hermiteNF", 
    "HNF", 
    "JaegerWagnerB", 
    "JaegerWagnerC", 
    "degreeProfile", 
    "smithNF", 
    "weakPopovForm"
    }

callnum = 0;
gcdCoeffs2 = args -> (
     callnum = callnum + 1;
     (g,h,str) := args;
     return gcdCoefficients(g,h);
     if h == 0 then {g, 1_(ring g), 0_(ring g)} else (
     << "gcdCoefficients " << callnum << " : " << args << endl << flush;
     g1 := (trim ideal g)_0;
     h1 := (trim ideal h)_0;
     a1 := g1 // g;
     b1 := h1 // h;
     result := gcdCoefficients(g1,h1);
     << "  gcdCoefficients: returning" << endl << flush;
     {result#0, a1*result#1, b1*result#2}
     ))

degreeProfile = method()
degreeProfile MutableMatrix := (A) -> (
     if ring A === ZZ then (
        map(RR^(numRows A), RR^(numColumns A), (i,j) -> log abs(A_(i,j)))
	  )
     else (
        map(ZZ^(numRows A), ZZ^(numColumns A), (i,j) -> first degree A_(i,j))
     ))

maxdeg = (A, prevmax) -> (
     if ring A === ZZ then
       max(max apply(flatten entries A, f -> log abs f), prevmax)
     else
       max(max apply(flatten entries A, f -> first degree f), prevmax)
     )
debug Core

-- row2by2 NOT USED YET: (so not debugged!)
row2by2 = (ri, rj, c, A, V) -> (
     -- modifies A, V
     a := A_(ri,c);
     b := A_(rj,c);
     (g,u,v) := toSequence gcdCoeffs2(a,b);
     a' := - a//g;
     b' := b//g; 
     rawMatrixRowOperation2(raw A, ri, rj, raw u, raw v, raw b', raw a', false);
     if V =!= null then rawMatrixRowOperation2(raw V, ri, rj, raw u, raw v, raw b', raw a', false);
     A
     )

column2by2 = (ci, cj, r, A, V) -> (
     -- modifies A, V
     a := A_(r,ci);
     b := A_(r,cj);
     (g,u,v) := toSequence gcdCoeffs2(a,b, "col2by2");
     cg := if ring A === ZZ then g else leadCoefficient g;
     if cg != 1 and ring A =!= ZZ then (
	  cginv := 1/cg;
	  g = cginv * g;
	  u = cginv * u;
	  v = cginv * v);
     a' := - a//g;
     b' := b//g;
     rawMatrixColumnOperation2(raw A, ci, cj, raw u, raw v, raw b', raw a', false);
     if V =!= null then rawMatrixColumnOperation2(raw V, ci, cj, raw u, raw v, raw b', raw a', false);
     A
     )

--------------------------------------------------
-- Hermite normal form: Kannan-Bachem algorithm --
-- at least roughly! -----------------------------
--------------------------------------------------
maxsize = 0

makemonicKt = (s,t,A,V) -> (
     -- for poly rings kk[x]
     a := A_(s,t);
     ca := leadCoefficient a;
     columnMult(A, t, 1/ca);
     if V =!= null then columnMult(V, t, 1/ca);
     )

makemonicZZ = (s,t,A,V) -> (
     -- for ZZ
     a := A_(s,t);
     if a < 0 then (
       columnMult(A, t, -1);
       if V =!= null then columnMult(V, t, -1);
       );
     )

HNF0 = (t, A,V, makemonic) -> (
     -- this does the 'forward' part of the HNF for the first t columns
     -- 0 <= t < numColumns A
     -- the return value: an integer, which row the pivot occurs in
     m := numRows A;
     c := -1; -- this is a column index
     --<< "." << flush;
     for s from 0 to m-1 do (
	  if A_(s,c+1) != 0 or A_(s,t) != 0 then (
             c = c+1;
	     if t == c then makemonic(s,t,A,V)
	     else column2by2(c,t, s, A,V);
	     -- Now make sure all entries in row s are small
       	     for ell from 0 to c-1 do (
	  	  q := A_(s,ell) // A_(s,c);
	  	  if q != 0 then (
	       	       columnAdd(A, ell, -q, c);
	       	       if V =!= null then columnAdd(V, ell, -q, c);
	       	       ));
	     if t == c then (
		  maxsize = maxdeg(A, maxsize);
		  --<< degreeProfile A << "   " << 
		  --(if V =!= null then degreeProfile V else "") 
		  --<< endl << "----------------------" << endl; 
		  return s);
	     );
	  ))

HNF = (A,V) -> (
     -- A is a MutableMatrix, n by m
     -- V is either null or a MutableMatrix, m by m
     -- the (common) ring of A or V should be either ZZ or F[x]
     --  but this is not checked
     -- A is m by n
     -- V is n by n unimodular.
     -- A and V are modified, but A*V is the same
     makemonic := if ring A === ZZ then makemonicZZ else makemonicKt;
     n := numColumns A;
     pivotrows := for t from 0 to n-1 list HNF0(t, A,V, makemonic);
     -- now: make the other entries smaller
--     for c1 from 1 to n-1 do (
--       c := n-c1;
--       s := pivotrows#c;
--       for ell from 0 to c-1 do (
--	  q := A_(s,ell) // A_(s,c);
--	  if q != 0 then (
--	       columnAdd(A, ell, -q, c);
--	       if V =!= null then columnAdd(V, ell, -q, c);
--	       )));
     )

hermiteNF = method(Options => {ChangeMatrix => false, Dense => true})
hermiteNF Matrix := opts -> (M) -> (
     -- ring of M must be either ZZ or K[x], for K a field
     -- return value: matrix H, or pair (H,V)
     --  where V is the transform matrix
     dense := opts.Dense;
     A := mutableMatrix(M, Dense=>dense);
     V := if opts.ChangeMatrix then mutableIdentity(ring M, numColumns M, Dense=>dense) else null;
     maxsize = 0;
     HNF(A,V);
     << "max size: " << maxsize << endl;
     if opts.ChangeMatrix then (matrix A, matrix V) else matrix A
     )

hermiteNF(MutableMatrix, MutableMatrix) := opts = HNF

isDiagonal = (A) -> (
     m := numRows A;
     n := numColumns A;
     for i from 0 to m-1 do
       for j from 0 to n-1 do
         if i =!= j and A_(i,j) != 0 then return false;
     true)

diagToSmithNF = (A,U,V) -> (
     -- A, U, V are all MutableMatrix'
     -- A is m by n, diagonal
     -- U is m by m, V is n by n, r <= min(m,n)
     -- changes A, so that A_(i,i) | A_(i+1,i+1), all i.
     -- U and V are the corresponding transform matrices
     R := ring A;
     m := numRows A;
     n := numColumns A;
     r := min(m,n);
     for k from 0 to r-2 do (
	for ell1 from 0 to r-2-k do (
	     ell := r-1-ell1-1;
	     f := A_(ell,ell);
	     g := A_(ell+1,ell+1);
	     if g % f != 0 then (
		  (d,u,v) := toSequence gcdCoeffs2(f,g, "diag");
		  f1 := f//d;
		  g1 := g//d;
		  A_(ell,ell) = d;
		  A_(ell+1,ell+1) = f * g1;
     		  if V =!= null then rawMatrixColumnOperation2(raw V, ell, ell+1, raw (1_R), raw(1_R), raw (-v*g1), raw (u*f1), false);
     	       	  if U =!= null then rawMatrixColumnOperation2(raw U, ell, ell+1, raw u, raw v, raw(-g1), raw f1, false);
		  );
	));
     )

smithNF = method(Options => {ChangeMatrix => {false,false}, Dense => true})
smithNF Matrix := opts -> (M) -> (
     dense := opts.Dense;
     A := mutableMatrix(M, Dense=>dense);
     V := if opts.ChangeMatrix#1 then mutableIdentity(ring M, numColumns M, Dense=>dense) else null;
     U := if opts.ChangeMatrix#0 then mutableIdentity(ring M, numRows M, Dense=>dense) else null;
     while not isDiagonal A do (
	  HNF(A,V);
	  B := mutableMatrix(transpose matrix A, Dense=>dense);
	  HNF(B,U);
	  A = mutableMatrix(transpose matrix B, Dense => true);
	  );
     diagToSmithNF(A,U,V);
     if U === null and V === null then matrix A
     else apply(select((A,U,V), z -> z =!= null), matrix)
     )

JaegerWagnerB = method()
JaegerWagnerB(ZZ, Ring) := (n,kk) -> (
     M1 := if kk === QQ then map(QQ^n, QQ^n, (i,j) -> (random 200) - 99)
           else random(kk^n, kk^n);
     x := getSymbol "x";
     R := kk[x];
     M1 - R_0*id_(R^n)
     )

JaegerWagnerC = method()
JaegerWagnerC(ZZ, Ring, ZZ) := (n,kk,qi) -> (
     p := char kk;
     if p <= 2 then error "these examples are for small odd finite characteristic";
     ltop := ceiling(n/p);
     x := getSymbol "x";
     R := kk[x];
     x = R_0;
     Q := if qi === 1 then x^5 + x^4 + x + 2
     else if qi === 2 then 2*x^4+3*x+3
     else error "third argument must be 1 or 2";
     L := flatten for i from 0 to ltop list (
	  xpower := if i === 0 then 0_R else x^i;
	  for j from 0 to p-1 list (xpower + j)
	  );
     map(R^n, R^n, (i,j) -> L#i^j % Q)
     )

-------------------------------------------------
-- Weak Popov "normal" form ---------------------
-- see paper: Mulders, Storjohann, JSC 35(2003) 377-401
--  see also Trager thesis, preprint of Mark van Hoeij, and
--  paper by Hess.  They are all doing this.

getRowInfo = (M, r) -> (
     -- returns: (maxdeg, col)
     degs := for j to numColumns M - 1 list
	       first degree M_(r,j);
     m := max degs;
     if m === -1 
       then {-1, -1} 
       else (
	    loc := last positions(degs, d -> d === m);
	    {m, loc})
     )

findMaxDegrees = (M) -> (
     -- M is a matrix over a ring in one variable
     -- returns two mutable lists (D,I)
     -- D#i is the max degree in row i
     --  == -1 if row is zero.
     -- I#i is the rightmost column in which this occurs.
     --  == -1 if row is zero.
     degs := transpose for i from 0 to numRows M - 1 list getRowInfo(M,i);
     (new MutableList from degs#0,
	  new MutableList from degs#1)
     )

findPopovMove = (M, D, I) -> (
     -- returns a triple (rpivot, r2, c), or null, if none
     -- we need a pair of rows for which the max column is the same.
     -- rpivot will be the smaller degree of the two.
     )

popovMove = (M, rpivot, r2, c, D, I) -> (
     -- makes a "simple transformation of firstkind" on M
     --   (with data rpivot, r2, c).
     -- update D#r2, L#r2 appropriately
     x := (ring M)_0;
     a := "xxx";  -- this function is not yet finished!!
     rowAdd(M, r2, a, rpivot);
     (deg,col) := getRowInfo(M, r2);
     D#r2 = deg;
     I#r2 = col;
     )

weakPopovForm = method()
weakPopovForm(MutableMatrix, MutableMatrix) := (M,N) -> (
     -- apply "simple transforms of first kind" to M
     -- apply the same transform to N, if N is not null.
     error "not written yet";     
     n := numRows M;
     (D,I) := findMaxDegrees M; -- 0..numRows M-1.  -1 in entry means row is zero.
     while ((rpivot, r2, c) := findPopovMove(M,D,I)) =!= null do (
	  popovMove(M, rpivot, r2, c, D, I);
	  );
     )
-------------------------------------------------
beginDocumentation()

doc ///
Key
  MatrixNormalForms
Headline
  Hermite, Smith, Popov, and other normal forms for matrices
Description
  Text
    This package provides implementations for Hermite and Smith normal forms
    for matrices over a PID (currently restricted to ZZ and kk[x], where kk is a field).
    These functions should be recoded in the Macaulay2 engine.  The advantage to these
    routines is that they are easy to modify.
    
    Other normal forms will hopefully be included eventually, including
    rational canonical form, weak Popov form, Frobenius form, and others.
    
  Example
Caveat
SeeAlso
///

multidoc ///
Node
   Key
     hermiteNF
     (hermiteNF,Matrix)
   Headline
     hermite normal form over ZZ or a polynomial ring over a field
   Usage
     H = hermiteNF A
     (H,U) = hermiteNF(A, ChangeMatrix => true)
   Inputs
     A:Matrix
       over either ZZ, or kk[x], where kk is a field
     ChangeMatrix => Boolean
       whether to also return the change of basis matrix
     Dense => Boolean
       whether to use dense (rather than sparse) mutable matrices during the computation
   Outputs
     H:Matrix
       of the same shape as A, in Hermite normal form (see below).
     U:Matrix
       a matrix such that H = A*U.  This will be unique only if
       A has linearly independent columns
   Description
    Text
      A matrix $A$ over a PID $R$ is in Hermite normal form if the pivots run
      from top left to bottom right (the pivot in a column is the first
      non-zero entry in that column, if any), if the zero columns all appear
      last, and if the pivots are monic (or positive, over ZZ), and the other
      entries in that row have lower absolute value (over ZZ) or degree (over a
      poly ring over a field).
    Example
      R = QQ[x];
      M = matrix"1,x-2,x-3;
           x2-1,x3-1,x5-1;
	   x2+1,x3+1,0"
      H0 = hermiteNF M;
      (H,U) = hermiteNF(M, ChangeMatrix => true)
      H == H0
      H
      U
      assert(M*U - H == 0)
   Caveat
     Operations over QQ[x] should be improved, to remove as much intermediate expression
     swell as possible
   SeeAlso
     smithNF

Node
   Key
     smithNF
     (smithNF, Matrix)
   Headline
     Smith normal form over ZZ or a polynomial ring over a field
   Usage
     S = smithNF A
     (S,U) = smithNF(A, ChangeMatrix => {true, false})
     (S,V) = smithNF(A, ChangeMatrix => {false, true})
     (S,U,V) = smithNF(A, ChangeMatrix => {true, true})
   Inputs
     A:Matrix
       of size $m x n$ over a P.I.D $R$, either ZZ, or kk[x], where kk is a field
     ChangeMatrix => List
       of two boolean values, whether to return the change of basis matrices U 
       or V
     Dense => Boolean
       whether to use dense (rather than sparse) mutable matrices during the computation
   Outputs
     S:Matrix
       of the same shape as A, in Smith normal form (see below).
     U:Matrix
       a unimodular $m x m$ matrix over $R$
     V:Matrix
       a unimodular $n x n$ matrix over $R$
   Description
    Text
      The Smith Normal Form of a matrix $A$ over a P.I.D. is a diagonal matrix
      $S = diag(f_1, f_2, \ldots, f_n)$ (i.e. zeros off the diagonal), such that 
      $f_i$ divides $f_{i+1}$ for all $i$, where $S = (transpose U) A V$, with $U$ 
      and $V$ unimodular square matrices.  The Smith Normal Form is unique, although the
      change of basis matrices (the "transform" matrices) are not unique.
    Example
      R = QQ[x];
      M = matrix"1,x-2,x-3;
           x2-1,x3-1,x5-1;
	   x2+1,x3+1,0"
      S0 = smithNF M
      (S,U,V) = smithNF(M, ChangeMatrix => {true,true});
      S == S0
      U
      V
      (transpose U) * M * V - S == 0
    Text
      The base ring may be ZZ too.
    Example
      M = random(ZZ^6, ZZ^4)
      S0 = smithNF M
      (S,U,V) = smithNF(M, ChangeMatrix => {true,true})
   Caveat
     Operations over QQ[x] should be improved, to remove as much intermediate expression
     swell as possible.
   SeeAlso
     hermiteNF
Node
   Key
     JaegerWagnerB
     (JaegerWagnerB,ZZ,Ring)
   Headline
     example matrix set B from Jaeger-Wagner
   Usage
     M = JaegerWagnerB(n,R)
   Inputs
     n:ZZ
       the size of the resulting matrix
     R:Ring
       should be a field
   Outputs
     M:Matrix
       det(A-xI), where A is a random n by n matrix over R
   Description
    Text
      This is one of the examples sets used in the paper
      {\it Efficient parallelizations of Hermite and Smith normal form algorithms},
      by G. Jaeger and C. Wagner, Parallel Computing (2009) 35, 345-357.
    Example
      JaegerWagnerB(40,ZZ/32003)
   SeeAlso
     JaegerWagnerC
     smithNF
     hermiteNF
Node
   Key
     JaegerWagnerC
     (JaegerWagnerC,ZZ,Ring,ZZ)
   Headline
     example matrix set C from Jaeger-Wagner
   Usage
     M = JaegerWagnerC(n,R,1)
     M = JaegerWagnerC(n,R,2)    
   Inputs
     n:ZZ
       the size of the resulting matrix
     R:Ring
       should be a field with small odd characteristic
   Outputs
     M:Matrix
   Description
    Text
      This is one of the examples sets used in the paper
      {\it Efficient parallelizations of Hermite and Smith normal form algorithms},
      by G. Jaeger and C. Wagner, Parallel Computing (2009) 35, 345-357.
    Example
      A = JaegerWagnerC(10,ZZ/7,1)
      B = JaegerWagnerC(10,ZZ/7,2)
      hermiteNF A
      smithNF A
      smithNF B
   SeeAlso
     JaegerWagnerB
     smithNF
     hermiteNF
Node
   Key
     "implementation issues"
   Description
     Text
       The following papers are potentially useful for coding Smith, Hermite and Popov normal forms.
       This is not a comprehensive list, but it does include (most of) the papers I considered before
       implementation.
     Code
       UL {
	    LI {ITALIC "Parallel Algorithms for Matrix Normal Forms", ", by Kaltofen and Saunders"},
	    LI {ITALIC "Fast Parallel Computation of Hermite and Smith Forms of Polynomial Matrices", ", by Kaltofen and Saunders"},
	    LI {ITALIC "Fast computation of the Smith form of a sparse integer matrix", ", by M. Giesbrecht, Comput. Complexity, 10 (2001), 41-69"},
	    LI {ITALIC "Algorithmic Methods for Finitely Generated Abelian Groups", ", by H. Cohen, F. Diaz, M. Olivier, J. Symbolic Comp (2001) 31, 133-147"},
	    LI {ITALIC "On Efficient Sparse Integer Matrix Smith Normal Form Computations", 
		 ", by J-G Dumas, D. Saunders, G. Villard, J. Symbolic Comp (2001) 32, 71-99"},
	    LI {ITALIC "Normal forms for general polynomial matrices", 
		 ", by B. Beckermann, G. Labahn, G. Villard, J. Symbolic Comp (2006) 41, 708-737"},
	    LI {ITALIC "Efficient parallelizations of Hermite and Smith normal form algorithms",
		 ", by G. Jaeger, C. Wagner, Parallel Computing (2009) 35, 345-357"},
	    LI {ITALIC "Polynomial algorithms for computing the Smith and Hermite normal forms 
		 of an integer matrix",
		 ", by R. Kannan and A. Bachem, Siam J. Computing (1979) vol 8, no 4, 499-507"}
	    }
///


TEST ///
R = QQ[x]
M = matrix"1,x-2,x-3;
           x2-1,x3-1,x5-1;
	   x2+1,x3+1,0"
(H,U) = hermiteNF(M, ChangeMatrix => true)
assert(M*U - H == 0)
///	   

TEST ///
n = 2
M = matrix"6,4;3,8"
(H,U) = hermiteNF(M, ChangeMatrix => true)
assert(M*U - H == 0)
///

TEST ///
R = QQ[x]
M = matrix"1,x-2,x-3;
           x2-1,x3-1,x5-1;
	   x2+1,x3+1,0"
(H,U) = hermiteNF(M, ChangeMatrix => true)
assert(M*U - H == 0)

(S,U,V) = smithNF(M, ChangeMatrix => {true,true})
det U
det V
assert((transpose U) * M * V - S == 0)
///	   

TEST ///
R = QQ[x]
M = matrix"4x2+3x+5, 4x2+3x+4, 6x2+1;
           3x+6, 3x+5, 3+x;
	   6x2+4x+2, 6x2, 2x2+x"
(H,U) = hermiteNF(M, ChangeMatrix => true)
assert(M*U - H == 0)

(S,U,V) = smithNF(M, ChangeMatrix=>{true,true})
det U
det V
assert((transpose U) * M * V - S == 0)
///

TEST ///
n = 40
M = random(ZZ^n, ZZ^n);
time (H,U) = hermiteNF(M, ChangeMatrix => true);
assert(M*U - H == 0)
assert((M ** QQ)^-1 * H - U == 0)
time(H1 = hermiteNF M);
assert(H == H1)

time (S,U,V) = smithNF(M, ChangeMatrix=>{true,true})
assert((transpose U) * M * V == S)
time S1 = smithNF(M);
assert(S == S1)

time (S,U1) = smithNF(M, ChangeMatrix=>{true,false});
assert (U1 == U)

time (S,V1) = smithNF(M, ChangeMatrix=>{false,true});
assert(V1 == V)

///

TEST ///
-- test of diagToSmithNF
debug MatrixNormalForms
A = mutableMatrix diagonalMatrix{21,49}
U = mutableIdentity(ZZ, 2)
V = mutableIdentity(ZZ, 2)
Aorig = matrix A
diagToSmithNF(A, U, V)
assert((transpose matrix U) * Aorig * (matrix V) == matrix A)

A = mutableMatrix diagonalMatrix{21,49,81}
U = mutableIdentity(ZZ, 3)
V = mutableIdentity(ZZ, 3)
Aorig = matrix A
diagToSmithNF(A, U, V)
assert((transpose matrix U) * Aorig * (matrix V) == matrix A)
///

TEST ///
kk = ZZ/101
R = kk[x]
n = 30
M = random(kk^n, kk^n) - x * id_(R^n)
time (H,U) = hermiteNF(M, ChangeMatrix => true);
assert(M*U - H == 0)
time H1 = hermiteNF(M);
assert(H1 == H)

time (S,U,V) = smithNF(M, ChangeMatrix=>{true,true});
assert((transpose U) * M * V - S == 0)
///

TEST ///
M = JaegerWagnerB(10,QQ)
time (H,U) = hermiteNF(M, ChangeMatrix => true); -- this line can crash or give wrong results here.  Why?!
assert(M*U - H == 0)

time (S,U,V) = smithNF(M, ChangeMatrix=>{true,true})
assert((transpose U) * M * V - S == 0)
time S1 = smithNF M;
assert(S == S1)
///

TEST ///
M = JaegerWagnerC(20,ZZ/5,1)
time (H,U) = hermiteNF(M, ChangeMatrix => true);
assert(M*U - H == 0)
det M
time H1 = hermiteNF(M, ChangeMatrix => false, Dense => true);
assert(H1 == H)

time (H,U,V) = smithNF(M, ChangeMatrix => {true,true})
assert((transpose U) * M * V - H == 0)
diagH = for i from 0 to min(numRows H, numColumns H)-1 list H_(i,i)
scan(1..#diagH-1, i -> assert(diagH_i % diagH_(i-1) == 0))
///

end

Node
   Key
   Headline
   Usage
   Inputs
   Outputs
   Consequences
    Item
   Description
    Text
    Code
    Pre
    Example
   Subnodes
   Caveat
   SeeAlso
Node
   Key
   Headline
   Usage
   Inputs
   Outputs
   Consequences
    Item
   Description
    Text
    Code
    Pre
    Example
   Subnodes
   Caveat
   SeeAlso

TEST ///
restart
loadPackage "MatrixNormalForms"
loadPackage "TraceForm"

S = QQ[x,y]
ideal"y20+y13x+x4y5+x3(x+1)2"
A = QQ[y]
R = (frac A)[x]/ideal"y20+y13x+x4y5+x3(x+1)2"
traceForm0 R
traceForm R
M = lift(oo,A)
M1 = (y * id_(A^5)) | M
(H,U) = hermiteNF(M, ChangeMatrix => true)
assert(M * U - H == 0)

debug MatrixNormalForms
findMaxDegrees M
oo/peek
///

TEST ///
--singular-sakai4
(m,p,q) = (9,2,9); -- q =2..9 -- modifying these gives other good examples

(m,p,q) = (9,3,9); -- q =2..9 -- modifying these gives other good examples

-- this
A = QQ[y]
R = (frac A)[x]/ideal(y^m - x^p*(x - 1)^q)

-- or
A = QQ[x]
R = (frac A)[y]/ideal(y^m - x^p*(x - 1)^q)

traceForm0 R
traceForm R
M = lift(oo,A)
hermiteNF(M)
smithNF M
///

doc ///
Key
Headline
Usage
Inputs
Outputs
Consequences
Description
  Text
  Example
Caveat
SeeAlso
///

debug loadPackage "MatrixNormalForms"
R = QQ[x]
M = matrix {{5105269578402295766364455796813235558023168000*x^35-1274312254112612522484348501527382667551257395200*x^33+145689146520704294368438497901965405449836929269760*x^31-1243711539715558647326444770373366352577607535607296*x^29+604317569862579057218856289436969836199980121049780*x^27+855216841261389435366255988546218484537124211800952*x^25-665090408662778074830045297241548055090984685476237*x^23+12800742038631428280985919272138510192348552226337*x^21+79062151286254888580136544524217313900625219658908*x^19-7420550102685003574133726047618095141946600222908*x^17-4109745747488307096127129491221128824852809122902*x^15+312745136916858316872503176714428773985388544622*x^13+105138807713322975378420268012429108850337963168*x^11-3546211749213429262862558760055854360137488452*x^9-1116487675614866804005711104422730663249199077*x^7+6491065295991043918739307757433261881725945*x^5+3539199263559937867640496473791332887568600*x^3+43226708325292071166799436097536000*x, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 4988*x^2-948, 0, 4271440*x^4-2086656*x^2+111888, 0, 5034656168*x^6-2768449320*x^4+249900888*x^2-13238424, 0, 6556853239720*x^8-3690827136672*x^6+210199294960*x^4+64576949088*x^2+1566919080, 0}, 
    {0, 5105269578402295766364455796813235558023168000*x^35-1274312254112612522484348501527382667551257395200*x^33+145689146520704294368438497901965405449836929269760*x^31-1243711539715558647326444770373366352577607535607296*x^29+604317569862579057218856289436969836199980121049780*x^27+855216841261389435366255988546218484537124211800952*x^25-665090408662778074830045297241548055090984685476237*x^23+12800742038631428280985919272138510192348552226337*x^21+79062151286254888580136544524217313900625219658908*x^19-7420550102685003574133726047618095141946600222908*x^17-4109745747488307096127129491221128824852809122902*x^15+312745136916858316872503176714428773985388544622*x^13+105138807713322975378420268012429108850337963168*x^11-3546211749213429262862558760055854360137488452*x^9-1116487675614866804005711104422730663249199077*x^7+6491065295991043918739307757433261881725945*x^5+3539199263559937867640496473791332887568600*x^3+43226708325292071166799436097536000*x, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4988*x^2-948, 0, 4271440*x^4-2086656*x^2+111888, 0, 5034656168*x^6-2768449320*x^4+249900888*x^2-13238424, 0, 6556853239720*x^8-3690827136672*x^6+210199294960*x^4+64576949088*x^2+1566919080, 0, 8744748472951448*x^10-5386495129920840*x^8-39914119899600*x^6+424894440995760*x^4-43560655832520*x^2-185527830888}, 
    {0, 0, 5105269578402295766364455796813235558023168000*x^35-1274312254112612522484348501527382667551257395200*x^33+145689146520704294368438497901965405449836929269760*x^31-1243711539715558647326444770373366352577607535607296*x^29+604317569862579057218856289436969836199980121049780*x^27+855216841261389435366255988546218484537124211800952*x^25-665090408662778074830045297241548055090984685476237*x^23+12800742038631428280985919272138510192348552226337*x^21+79062151286254888580136544524217313900625219658908*x^19-7420550102685003574133726047618095141946600222908*x^17-4109745747488307096127129491221128824852809122902*x^15+312745136916858316872503176714428773985388544622*x^13+105138807713322975378420268012429108850337963168*x^11-3546211749213429262862558760055854360137488452*x^9-1116487675614866804005711104422730663249199077*x^7+6491065295991043918739307757433261881725945*x^5+3539199263559937867640496473791332887568600*x^3+43226708325292071166799436097536000*x, 0, 0, 0, 0, 0, 0, 0, 4988*x^2-948, 0, 4271440*x^4-2086656*x^2+111888, 0, 5034656168*x^6-2768449320*x^4+249900888*x^2-13238424, 0, 6556853239720*x^8-3690827136672*x^6+210199294960*x^4+64576949088*x^2+1566919080, 0, 8744748472951448*x^10-5386495129920840*x^8-39914119899600*x^6+424894440995760*x^4-43560655832520*x^2-185527830888, 0}, 
    {0, 0, 0, 5105269578402295766364455796813235558023168000*x^35-1274312254112612522484348501527382667551257395200*x^33+145689146520704294368438497901965405449836929269760*x^31-1243711539715558647326444770373366352577607535607296*x^29+604317569862579057218856289436969836199980121049780*x^27+855216841261389435366255988546218484537124211800952*x^25-665090408662778074830045297241548055090984685476237*x^23+12800742038631428280985919272138510192348552226337*x^21+79062151286254888580136544524217313900625219658908*x^19-7420550102685003574133726047618095141946600222908*x^17-4109745747488307096127129491221128824852809122902*x^15+312745136916858316872503176714428773985388544622*x^13+105138807713322975378420268012429108850337963168*x^11-3546211749213429262862558760055854360137488452*x^9-1116487675614866804005711104422730663249199077*x^7+6491065295991043918739307757433261881725945*x^5+3539199263559937867640496473791332887568600*x^3+43226708325292071166799436097536000*x, 0, 0, 0, 0, 0, 0, 0, 4271440*x^4-2086656*x^2+111888, 0, 5034656168*x^6-2768449320*x^4+249900888*x^2-13238424, 0, 6556853239720*x^8-3690827136672*x^6+210199294960*x^4+64576949088*x^2+1566919080, 0, 8744748472951448*x^10-5386495129920840*x^8-39914119899600*x^6+424894440995760*x^4-43560655832520*x^2-185527830888, 0, 11724314600672230600*x^12-8241635056733266032*x^10-330965591397176136*x^8+1282807940804091360*x^6-267453155393866056*x^4+14517496177208208*x^2+21974875975368}, 
    {0, 0, 0, 0, 5105269578402295766364455796813235558023168000*x^35-1274312254112612522484348501527382667551257395200*x^33+145689146520704294368438497901965405449836929269760*x^31-1243711539715558647326444770373366352577607535607296*x^29+604317569862579057218856289436969836199980121049780*x^27+855216841261389435366255988546218484537124211800952*x^25-665090408662778074830045297241548055090984685476237*x^23+12800742038631428280985919272138510192348552226337*x^21+79062151286254888580136544524217313900625219658908*x^19-7420550102685003574133726047618095141946600222908*x^17-4109745747488307096127129491221128824852809122902*x^15+312745136916858316872503176714428773985388544622*x^13+105138807713322975378420268012429108850337963168*x^11-3546211749213429262862558760055854360137488452*x^9-1116487675614866804005711104422730663249199077*x^7+6491065295991043918739307757433261881725945*x^5+3539199263559937867640496473791332887568600*x^3+43226708325292071166799436097536000*x, 0, 0, 0, 0, 0, 4271440*x^4-2086656*x^2+111888, 0, 5034656168*x^6-2768449320*x^4+249900888*x^2-13238424, 0, 6556853239720*x^8-3690827136672*x^6+210199294960*x^4+64576949088*x^2+1566919080, 0, 8744748472951448*x^10-5386495129920840*x^8-39914119899600*x^6+424894440995760*x^4-43560655832520*x^2-185527830888, 0, 11724314600672230600*x^12-8241635056733266032*x^10-330965591397176136*x^8+1282807940804091360*x^6-267453155393866056*x^4+14517496177208208*x^2+21974875975368, 0}, 
    {0, 0, 0, 0, 0, 5105269578402295766364455796813235558023168000*x^35-1274312254112612522484348501527382667551257395200*x^33+145689146520704294368438497901965405449836929269760*x^31-1243711539715558647326444770373366352577607535607296*x^29+604317569862579057218856289436969836199980121049780*x^27+855216841261389435366255988546218484537124211800952*x^25-665090408662778074830045297241548055090984685476237*x^23+12800742038631428280985919272138510192348552226337*x^21+79062151286254888580136544524217313900625219658908*x^19-7420550102685003574133726047618095141946600222908*x^17-4109745747488307096127129491221128824852809122902*x^15+312745136916858316872503176714428773985388544622*x^13+105138807713322975378420268012429108850337963168*x^11-3546211749213429262862558760055854360137488452*x^9-1116487675614866804005711104422730663249199077*x^7+6491065295991043918739307757433261881725945*x^5+3539199263559937867640496473791332887568600*x^3+43226708325292071166799436097536000*x, 0, 0, 0, 0, 0, 5034656168*x^6-2768449320*x^4+249900888*x^2-13238424, 0, 6556853239720*x^8-3690827136672*x^6+210199294960*x^4+64576949088*x^2+1566919080, 0, 8744748472951448*x^10-5386495129920840*x^8-39914119899600*x^6+424894440995760*x^4-43560655832520*x^2-185527830888, 0, 11724314600672230600*x^12-8241635056733266032*x^10-330965591397176136*x^8+1282807940804091360*x^6-267453155393866056*x^4+14517496177208208*x^2+21974875975368, 0, 15737202047774974930328*x^14-12697023261040123192824*x^12-403727883641782255976*x^10+2844174196900893039624*x^8-882627006702171924088*x^6+97974312600059696472*x^4-3756370093598518200*x^2-2603762234164584}, 
    {0, 0, 0, 0, 0, 0, 5105269578402295766364455796813235558023168000*x^35-1274312254112612522484348501527382667551257395200*x^33+145689146520704294368438497901965405449836929269760*x^31-1243711539715558647326444770373366352577607535607296*x^29+604317569862579057218856289436969836199980121049780*x^27+855216841261389435366255988546218484537124211800952*x^25-665090408662778074830045297241548055090984685476237*x^23+12800742038631428280985919272138510192348552226337*x^21+79062151286254888580136544524217313900625219658908*x^19-7420550102685003574133726047618095141946600222908*x^17-4109745747488307096127129491221128824852809122902*x^15+312745136916858316872503176714428773985388544622*x^13+105138807713322975378420268012429108850337963168*x^11-3546211749213429262862558760055854360137488452*x^9-1116487675614866804005711104422730663249199077*x^7+6491065295991043918739307757433261881725945*x^5+3539199263559937867640496473791332887568600*x^3+43226708325292071166799436097536000*x, 0, 0, 0, 5034656168*x^6-2768449320*x^4+249900888*x^2-13238424, 0, 6556853239720*x^8-3690827136672*x^6+210199294960*x^4+64576949088*x^2+1566919080, 0, 8744748472951448*x^10-5386495129920840*x^8-39914119899600*x^6+424894440995760*x^4-43560655832520*x^2-185527830888, 0, 11724314600672230600*x^12-8241635056733266032*x^10-330965591397176136*x^8+1282807940804091360*x^6-267453155393866056*x^4+14517496177208208*x^2+21974875975368, 0, 15737202047774974930328*x^14-12697023261040123192824*x^12-403727883641782255976*x^10+2844174196900893039624*x^8-882627006702171924088*x^6+97974312600059696472*x^4-3756370093598518200*x^2-2603762234164584, 0}, 
    {0, 0, 0, 0, 0, 0, 0, 5105269578402295766364455796813235558023168000*x^35-1274312254112612522484348501527382667551257395200*x^33+145689146520704294368438497901965405449836929269760*x^31-1243711539715558647326444770373366352577607535607296*x^29+604317569862579057218856289436969836199980121049780*x^27+855216841261389435366255988546218484537124211800952*x^25-665090408662778074830045297241548055090984685476237*x^23+12800742038631428280985919272138510192348552226337*x^21+79062151286254888580136544524217313900625219658908*x^19-7420550102685003574133726047618095141946600222908*x^17-4109745747488307096127129491221128824852809122902*x^15+312745136916858316872503176714428773985388544622*x^13+105138807713322975378420268012429108850337963168*x^11-3546211749213429262862558760055854360137488452*x^9-1116487675614866804005711104422730663249199077*x^7+6491065295991043918739307757433261881725945*x^5+3539199263559937867640496473791332887568600*x^3+43226708325292071166799436097536000*x, 0, 0, 0, 6556853239720*x^8-3690827136672*x^6+210199294960*x^4+64576949088*x^2+1566919080, 0, 8744748472951448*x^10-5386495129920840*x^8-39914119899600*x^6+424894440995760*x^4-43560655832520*x^2-185527830888, 0, 11724314600672230600*x^12-8241635056733266032*x^10-330965591397176136*x^8+1282807940804091360*x^6-267453155393866056*x^4+14517496177208208*x^2+21974875975368, 0, 15737202047774974930328*x^14-12697023261040123192824*x^12-403727883641782255976*x^10+2844174196900893039624*x^8-882627006702171924088*x^6+97974312600059696472*x^4-3756370093598518200*x^2-2603762234164584, 0, 21128891321416948544291080*x^16-19386883041104640514989120*x^14+58341013038845353953504*x^12+5332974248699739466638912*x^10-2181609584680549388990416*x^8+357550899387782541300288*x^6-26722164080243101202208*x^4+842356054614853918656*x^2+308628712948033800}, 
    {0, 0, 0, 0, 0, 0, 0, 0, 5105269578402295766364455796813235558023168000*x^35-1274312254112612522484348501527382667551257395200*x^33+145689146520704294368438497901965405449836929269760*x^31-1243711539715558647326444770373366352577607535607296*x^29+604317569862579057218856289436969836199980121049780*x^27+855216841261389435366255988546218484537124211800952*x^25-665090408662778074830045297241548055090984685476237*x^23+12800742038631428280985919272138510192348552226337*x^21+79062151286254888580136544524217313900625219658908*x^19-7420550102685003574133726047618095141946600222908*x^17-4109745747488307096127129491221128824852809122902*x^15+312745136916858316872503176714428773985388544622*x^13+105138807713322975378420268012429108850337963168*x^11-3546211749213429262862558760055854360137488452*x^9-1116487675614866804005711104422730663249199077*x^7+6491065295991043918739307757433261881725945*x^5+3539199263559937867640496473791332887568600*x^3+43226708325292071166799436097536000*x, 0, 6556853239720*x^8-3690827136672*x^6+210199294960*x^4+64576949088*x^2+1566919080, 0, 8744748472951448*x^10-5386495129920840*x^8-39914119899600*x^6+424894440995760*x^4-43560655832520*x^2-185527830888, 0, 11724314600672230600*x^12-8241635056733266032*x^10-330965591397176136*x^8+1282807940804091360*x^6-267453155393866056*x^4+14517496177208208*x^2+21974875975368, 0, 15737202047774974930328*x^14-12697023261040123192824*x^12-403727883641782255976*x^10+2844174196900893039624*x^8-882627006702171924088*x^6+97974312600059696472*x^4-3756370093598518200*x^2-2603762234164584, 0, 21128891321416948544291080*x^16-19386883041104640514989120*x^14+58341013038845353953504*x^12+5332974248699739466638912*x^10-2181609584680549388990416*x^8+357550899387782541300288*x^6-26722164080243101202208*x^4+842356054614853918656*x^2+308628712948033800, 0}, 
    {0, 0, 0, 0, 0, 0, 0, 0, 0, 5105269578402295766364455796813235558023168000*x^35-1274312254112612522484348501527382667551257395200*x^33+145689146520704294368438497901965405449836929269760*x^31-1243711539715558647326444770373366352577607535607296*x^29+604317569862579057218856289436969836199980121049780*x^27+855216841261389435366255988546218484537124211800952*x^25-665090408662778074830045297241548055090984685476237*x^23+12800742038631428280985919272138510192348552226337*x^21+79062151286254888580136544524217313900625219658908*x^19-7420550102685003574133726047618095141946600222908*x^17-4109745747488307096127129491221128824852809122902*x^15+312745136916858316872503176714428773985388544622*x^13+105138807713322975378420268012429108850337963168*x^11-3546211749213429262862558760055854360137488452*x^9-1116487675614866804005711104422730663249199077*x^7+6491065295991043918739307757433261881725945*x^5+3539199263559937867640496473791332887568600*x^3+43226708325292071166799436097536000*x, 0, 8744748472951448*x^10-5386495129920840*x^8-39914119899600*x^6+424894440995760*x^4-43560655832520*x^2-185527830888, 0, 11724314600672230600*x^12-8241635056733266032*x^10-330965591397176136*x^8+1282807940804091360*x^6-267453155393866056*x^4+14517496177208208*x^2+21974875975368, 0, 15737202047774974930328*x^14-12697023261040123192824*x^12-403727883641782255976*x^10+2844174196900893039624*x^8-882627006702171924088*x^6+97974312600059696472*x^4-3756370093598518200*x^2-2603762234164584, 0, 21128891321416948544291080*x^16-19386883041104640514989120*x^14+58341013038845353953504*x^12+5332974248699739466638912*x^10-2181609584680549388990416*x^8+357550899387782541300288*x^6-26722164080243101202208*x^4+842356054614853918656*x^2+308628712948033800, 0, 28369374942202464500143534808*x^18-29242916017048725431448371688*x^16+1490639428560518435121092064*x^14+9053594037375634693657756512*x^12-4573517990331371241493365552*x^10+963450760694097898221871824*x^8-101297277836969694600089760*x^6+5772956207858243005010400*x^4-171745120373567508927720*x^2-36596028375789721128}};
time hermiteNF(M);

gcdCoefficients(x^35+1, 0_R)
gcdCoefficients(x^2+1, 0_R)
collectGarbage()
gcdCoefficients(M_(0,0), 0_R)
