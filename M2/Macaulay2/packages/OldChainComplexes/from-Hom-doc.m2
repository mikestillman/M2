doc ///
  Key
   (Hom, Module, ChainComplex)
   (Hom, ChainComplex, Module)
   (Hom, Module, ChainComplexMap)
   (Hom, ChainComplexMap, Module)
  Headline
    the Hom functor
  Usage
    Hom(M, C)
    Hom(C, M)
  Inputs
    M:Module
    C:ChainComplex
    DegreeLimit => {ZZ,List}
      see @TO [Hom, DegreeLimit]@
    MinimalGenerators => Boolean
      see @TO [Hom, MinimalGenerators]@
    Strategy => Thing
      see @TO [Hom, Strategy]@
  Outputs
    :ChainComplex
      the chain complex whose $i$-th spot is $\mathrm{Hom}(M, C_i)$,
      in the first case, or $\mathrm{Hom}(C_(-i), M)$ in the second case.
  Description
    Example
      R = QQ[a..d];
      C = res coker vars R
      M = R^1/(a,b)
      C' = Hom(C,M)
      C'.dd_-1
      C'.dd^2 == 0
  Synopsis
    Heading
      induced map on Hom
    Usage
      Hom(f,M)
      Hom(M,f)
    Inputs
      f:ChainComplexMap
      M:Module
      DegreeLimit => {ZZ,List}
        see @TO [Hom, DegreeLimit]@
      MinimalGenerators => Boolean
        see @TO [Hom, MinimalGenerators]@
      Strategy => Thing
        see @TO [Hom, Strategy]@
    Outputs
       :ChainComplexMap
         the induced map on Hom
  Caveat
    See @TO "Complexes :: Hom(Complex,Complex)"@ for Hom of two chain complexes.
  SeeAlso
    resolution
///
