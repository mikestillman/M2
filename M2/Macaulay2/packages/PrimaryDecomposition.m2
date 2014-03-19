-- -*- coding: utf-8 -*-
newPackage(
     "PrimaryDecomposition",
     Version => "1.8",
     Date => "March 2014",
     AuxiliaryFiles => true,
     Authors => {
         {Name => "Frank Moore", 
             Email => "", 
             HomePage => ""},
         {Name => "Michael E. Stillman", 
             Email => "mike@math.cornell.edu",
             HomePage=>""}
         },
     Headline => "functions for primary decomposition"
     )

export {
     primaryDecomposition,
     irreducibleDecomposition,
     isPrimary,
     EisenbudHunekeVasconcelos,					    -- cryptic
     Hybrid,
     Increment,
     GTZ,
     ShimoyamaYokoyama,
--     binomialCD,
--     extract,
--     findNonMember,
--     flattener,
     localize,
--     minSat,
     primaryComponent
--     quotMin,
--     radicalContainment
     }

-- private symbols used as keys:
protect H, protect U, protect W

--     EHVprimaryDecomposition,			    -- cryptic
--     HprimaryDecomposition,
--     Hybrid,
--     primdecComputation,
--     minSatPPD,
--     sortByDegree

primaryDecomposition = method( TypicalValue => List, Options => { Strategy => null } )


load "./PrimaryDecomposition/GTZ.m2"
load "./PrimaryDecomposition/Shimoyama-Yokoyama.m2"
load "./PrimaryDecomposition/Eisenbud-Huneke-Vasconcelos.m2"
load "./PrimaryDecomposition/radical.m2"

binomialCD = (I) -> error "Binomial strategy not implemented yet"

Hybrid = new SelfInitializingType of BasicList

primedecomp = (I,strategy) -> (
     -- Determine the strategy to use.
     opt := ShimoyamaYokoyama;
     if strategy =!= null then (
	  opt = strategy;
	  if opt === Monomial and not isMonomialIdeal I
	  then error "cannot use 'Monomial' strategy on non monomial ideal";
	  )
     else (
	  -- if we have a monomial ideal: use Monomial
	  if isMonomialIdeal I then 
	     opt = Monomial;
	  );
     -- Now call the correct algorithm
     if opt === Monomial then (
	  C := primaryDecomposition monomialIdeal I;
	  I.cache#"AssociatedPrimes" = apply(C, I -> ideal radical I);
	  C/ideal
	  )
     else if opt === Binomial then binomialCD I
     else if opt === EisenbudHunekeVasconcelos then EHVprimaryDecomposition I
     else if opt === ShimoyamaYokoyama then SYprimaryDecomposition I
     else if class opt === Hybrid then (
	  if #opt =!= 2 then error "the Hybrid strategy requires 2 arguments";
	  assStrategy := opt#0;
	  localizeStrategy := opt#1;
	  HprimaryDecomposition ( I, assStrategy, localizeStrategy )
	  )
     else error "unimplemented strategy"
     )

primaryDecomposition Ideal := List => o -> (J) -> (
     R := ring J;
     (J',F) := flattenRing J;
     A := ring J';
     if not isPolynomialRing A then error "expected ideal in a polynomial ring or a quotient of one";
     if not isCommutative A then
       error "expected commutative polynomial ring";
     kk := coefficientRing A;
     if kk =!= QQ and not instance(kk,QuotientRing) then
       error "expected base field to be QQ or ZZ/p";
     if J === J'
     then primedecomp(J, o.Strategy)
     else (
	  G := map(R, ring J', generators(R, CoefficientRing => coefficientRing ring J'));
	  C := primedecomp(J', o.Strategy);
	  J.cache#"AssociatedPrimes" = apply(associatedPrimes J', P -> trim G P);
	  apply(C, Q -> trim G Q)
	  ))

isPrimary = method()
isPrimary(Ideal) := Q -> isPrimary(Q, radical Q)
isPrimary(Ideal,Ideal) := (Q,P) -> (
     if isPrime P then Q == top Q
     else false
     )

load "./PrimaryDecomposition/pd-monideals.m2"

beginDocumentation()


load "./PrimaryDecomposition/doc.m2"
load "./PrimaryDecomposition/tests.m2"

end
loadPackage("PrimaryDecomposition", Reload=>true)

-- Local Variables:
-- compile-command: "make -C $M2BUILDDIR/Macaulay2/packages PACKAGES=PrimaryDecomposition pre-install"
-- End:
