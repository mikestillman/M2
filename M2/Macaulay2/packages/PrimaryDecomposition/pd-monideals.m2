minimalPrimes MonomialIdeal := decompose MonomialIdeal := (cacheValue symbol minimalPrimes) (
     (I) -> (
	  minI := dual radical I;
	  apply(flatten entries generators minI, monomialIdeal @@ support)))

irreducibleDecomposition = method();
irreducibleDecomposition MonomialIdeal := List => (I) -> (
     -- probably written by Greg Smith
     R := ring I;
     aI := first exponents lcm I;
     M := first entries generators dual I;
     apply(M, m -> (
	       s := first keys standardForm leadMonomial m;
	       if #s === 0 then return monomialIdeal 0_R;
	       monomialIdeal apply(keys s, v -> R_v^(aI#v + 1 - s#v))))
     )

--  ASSOCIATED PRIMES  -------------------------------------
ass0 = (I) -> (
     if I.cache#?associatedPrimes
     then I.cache#associatedPrimes
     else I.cache#associatedPrimes = (
     	  R := ring I;
     	  J := dual I;
     	  M := first entries generators J;
	  H := new MutableHashTable;
     	  scan(M, m -> (
		    s := rawIndices raw m;
		    if not H#?s then H#s = true));
	  inds := sort apply(keys H, ind -> (#ind, ind));
	  apply(inds, s -> s#1)
     ))

associatedPrimes MonomialIdeal := List => o -> (I) -> (
     inds := ass0 I;
     R := ring I;
     apply(inds, ind -> monomialIdeal apply(ind, v -> R_v)))

primaryDecomposition MonomialIdeal := List => o -> (I) -> (
     R := ring I;
     aI := first exponents lcm I;
     J := dual I;
     M := first entries generators J;
     H := new MutableHashTable;
     scan(M, m -> (
	       s := first keys standardForm leadMonomial m;
	       Q := monomialIdeal apply(keys s, v -> R_v^(aI#v + 1 - s#v));
	       ind := sort keys s;
	       if not H#?ind then H#ind = Q
	       else H#ind = intersect(H#ind,Q)));
     apply(ass0 I, ind -> H#ind)
     )
