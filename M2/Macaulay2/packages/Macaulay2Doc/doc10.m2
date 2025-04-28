-- -*- coding: utf-8 -*-
--		Copyright 1993-2002 by Daniel R. Grayson


document { Key => toRR,
     Headline => "convert to high-precision real number",
     Usage => "toRR(prec,x)",
     Inputs => {
	  "prec" => ZZ => {"the number of bits of precision desired"},
	  "x" => {ofClass{RR,ZZ,QQ}}
	  },
     Outputs => {RR => {"the result of converting ", TT "x", " to a high-precision real number"}},
     EXAMPLE lines ///
     toRR(200,1/7)
     precision oo
     ///
     }

document {
     Key => {toCC,
 	  (toCC, ZZ, ZZ), (toCC, ZZ, QQ), (toCC, ZZ, RR), (toCC, ZZ, CC),
 	  (toCC, RR, RR), (toCC, ZZ, ZZ, ZZ), (toCC, ZZ, ZZ, QQ),
	  (toCC, ZZ, QQ, ZZ), (toCC, ZZ), (toCC, ZZ, QQ, QQ), (toCC, QQ),
	  (toCC, ZZ, RR, ZZ), (toCC, ZZ, ZZ, RR), (toCC, ZZ, RR, QQ),
	  (toCC, ZZ, QQ, RR), (toCC, RR), (toCC, CC), (toCC, ZZ, RR, RR)
	  },
     Headline => "convert to high-precision complex number",
     SYNOPSIS (
	  Usage => "toCC(prec,x,y)\ntoCC(prec,x)",
	  Inputs => {
	       "prec" => ZZ => {"the number of bits of precision desired"},
	       "x" => {ofClass{ZZ,QQ,RR}},
	       "y" => {ofClass{ZZ,QQ,RR}}
	       },
	  Outputs => {CC => {"the complex number with real part ", TT "x", " and complex part ", TT "y", ".  If
		    ", TT "y", " is omitted, the imaginary part is zero."}},
	  EXAMPLE lines ///
	  toCC(200,7)
	  toCC(100,7,3.)
	  ///
	  ),
     SYNOPSIS (
	  Usage => "toCC(x,y)\ntoCC x",
	  Inputs => { "x" => RR, "y" => RR },
	  Outputs => {CC => {"the complex number with real part ", TT "x", " and complex part ", TT "y", ".  If
		    ", TT "y", " is omitted, the imaginary part is zero.  The precision of the result is
		    the minimum precision of the arguments."}},
	  EXAMPLE lines ///
	  toCC(3.,4.)
	  toCC(3.p100,4.p200)
	  ///
	  )
     }


document { Key => InexactField,
     Headline => "the class of inexact fields",
     PARA {
	  "An inexact field is one whose elements are real or complex numbers,
	  represented floating point approximations of varying accuracy or precision."
	  },
     EXAMPLE lines ///
     numeric_100 pi
     ring oo
     class oo
     parent oo
     ///,
     Subnodes => { TO RealField, TO ComplexField },
     }

document { Key => InexactFieldFamily,
     Headline => "the class of all families of inexact fields",
     PARA {
	  "All real numbers have the same class, ", TO "RR", ", but the rings they
	  belong to depends on the number of binary digits of precision used
	  to represent them.  Similarly for complex numbers, which all belong
	  to the class ", TO "CC", ".  Thus ", TO "RR", " and ", TO "CC", " are regarded not as inexact
	  fields, but as families of inexact fields."
	  },
     EXAMPLE lines ///
     x = 1/3.
     class x
     ring x
     x = 1/3.p200
     class x
     ring x
     ///,
     SeeAlso => { InexactField }
     }

document { Key => RealField,
     Headline => "the class of all real fields",
     PARA { "A real number ring is a ring whose elements are real numbers of variable precision." }
     }

undocumented {
     (NewOfFromMethod,ComplexField,Nothing,ZZ),
     (NewOfFromMethod,RealField,Nothing,ZZ)
     }

document { Key => ComplexField,
     Headline => "the class of all complex fields",
     PARA { "A complex number ring is a ring whose elements are complex numbers of variable precision." }
     }

-- Local Variables:
-- compile-command: "make -C $M2BUILDDIR/Macaulay2/m2 "
-- End:
