-------------------  File Amelia is working on! -----------------------

----------------------------
-- IDEAL nodes ---------
----------------------------

document {
     Key => "creating an ideal",
    
	SUBSECTION "ideal",
     	     "An ideal ", TT "I", " is represented by its generators.  
     	     We use the function ", TO "ideal", " to construct an ideal.",
     	     EXAMPLE {
	  	  "R = QQ[a..d];",
	  	  "I = ideal (a^2*b-c^2, a*b^2-d^3, c^5-d)"
	  	  }
   	     , 
	SUBSECTION "monomial ideals",
     	     "For a monomial ideal you can use the 
     	     function ", TO "monomialIdeal", ".",
     	     EXAMPLE {
	  	  "J = monomialIdeal (a^2*b, b*c*d, c^5)"
	  	  },
     	     "The distinction is small since a monomial ideal can be 
     	     constructed using ", TT "ideal", " .  However, there are a 
     	     few functions, like ", TO "primaryDecomposition", " that run 
     	     faster if you define a monomial ideal 
     	     using ", TT "monomialIdeal", ".",
     	     PARA,
   	     , 
	SUBSECTION "monomialCurveIdeal",
     	     "An interesting class of ideals can be obtained as the 
     	     defining ideals in projective space of monomial curves.  
     	     For example the twisted cubic is the closure of the set of 
     	     points ", TT "(1,t^1,t^2,t^3)", " in projective space.  We 
     	     use a list of the exponents and ", TO "monomialCurveIdeal", " to 
     	     get the ideal.",
     	     EXAMPLE {
	  	  "monomialCurveIdeal(R,{1,2,3})"
	  	  }
	     
	
   }


document {
     Key => "ideals to and from matrices",
     
	  SUBSECTION "forming an ideal from a matrix",
	       "After defining a matrix (see ", TO "input a matrix", ")
     	       , ", TT "M", ", the ideal generated by the entries of the matrix 
     	       is obtained using the command ", TO "ideal", ".",
     	       EXAMPLE {
	  	    "R = ZZ/101[a..e];",
	  	    "M = matrix{{a^2*b-c^2, a*b^2-d^3, c^5-d},{a^2*b, b*c*d, c^5}}",
	  	    "ideal M"
	  	    },
	       ,
	  SUBSECTION "forming a matrix from an ideal",
     	       "In much the same way we can construct a 1 by 
     	       n (where n is the number of generators of ", TT "I", "), 
     	       matrix from the n generators of an ideal ", TT "I", " using 
     	       the command, ", TO "generators", ".",
     	       EXAMPLE {
	  	    "I = ideal(a^2*b-c^2+c*d, a*b^2-b*d^3, c^5,d+e);",
	  	    "generators I"
	  	    },
     	       "The abbreviation ", TO "gens", " can be used for ", TT "generators", "." 
     	       
	  
     }


document {
     Key => "ideals to and from modules",
     
	  SUBSECTION "from ideals to modules",
	       --     "There are two main ways to consider an ideal as 
	       --     a module.  First, as a submodule of the rank one free 
	       --     module, ", TT "R", " as the image of the map defined 
	       --     by the 1 by n matrix consisting of the generators. The 
	       --     easiest way to do this is to use the 
	       --     function ", TT "module", ".",
	       "An ideal ", TT "I", " is also an ", TT, "R", "-submodule.  In
	       Macaulay 2 we distinguish between when we are thinking of ", TT "I", " as
	       as ideal or a module.  If it is first defined as an ideal, it is easily
	       turned into a module using the function ", TO "module", " and for any
	       submodule of the rank one free module ", TT "R", " we can obtain an ideal 
	       of the generators using the function ", TO "ideal", ".",
	       EXAMPLE {
		    "R = ZZ/32003[x,y,z];",
		    "I = ideal(x^2,y*z-x);",
		    "module I"
		    }
	       ,
	  SUBSECTION "from modules to ideals",
	       "For any submodule of the rank one free 
	       module ", TT "R", " we can obtain an ideal of the generators 
	       using the function ", TT "ideal", ".",
	       EXAMPLE {
		    "A = matrix{{x*y-z,z^3}};",
		    "M = image A",
		    "ideal M",
		    }
	       ,
	  SUBSECTION "getting the quotient module corresponding to an ideal",
	       NOINDENT, "We also often work with ", TT "R/I", " as 
	       an ", TT "R", "-module.  Simply typing ", TT "R/I", " at a prompt
	       in Macaulay 2 constructs the quotient ring (see ", TO "quotient rings", ").  
	       There are two ways to tell Macaulay 2 that we want to work with this 
	       as a module.",
	       EXAMPLE {
		    "coker generators I",
		    "R^1/I"
		    }
	       ,
	  SUBSECTION "modules versus ideals for computations",
	       "Some functions in Macaulay 2 try to make an informed decision 
	       about ideal and modules.  For example, if ", TO "resolution", " is
	       given an ideal ", TT "I", ", it will compute a resolution of
	       the module ", TT "R^1/I", ", as in the following example.",
	       EXAMPLE {
		    --"J = ideal(x*y-z^2,x*z^3-y^4);",
		    "resolution I"
		    },
	       "The functions ", TO "dimension", " and ", TO "degree", " also 
	       operate on ", TT "R^1/I", " if the input 
	       is ", TT "I", " or ", TT "R^1/I", ".  However, the 
	       function ", TO "hilbertPolynomial", " computes the Hilbert 
	       polynomial of the module ", TT "I", " if the input 
	       is ", TT "hilbertPolynomial I", ".",     
	       PARA, "For basic information about working with 
	       modules see ", TO "modules: part I", "."
	       
	  
     }

document {
     Key => "sums, products, and powers of ideals",
     "Arithmetic for ideals uses the standard symbols.  Below are examples 
     of the basic arithmetic functions for ideal.", 
     EXAMPLE {
	  "R = ZZ/101[a..d]/(b*c-a*d,c^2-b*d,b^2-a*c);",
	  },
     "For more information about quotient rings see ", TO "quotient rings", ".",
     EXAMPLE {
	  "I = ideal (a*b-c,d^3);",
	  "J = ideal (a^3,b*c-d);",
	  "I+J",
	  "I*J",
	  "I^2"
	  },
     "For more information see ", TO (symbol+,Ideal,Ideal), ", 
     ", TO (symbol*,Ideal,Ideal), ", and ", TO (symbol^,Ideal,ZZ), "."
     }

document {
     Key => "equality and containment",
     "Equality and containment can sometimes be subtle in Macaulay 2.  For 
     example, testing if an ideal is equal to 0 or 1 are special functions 
     so we give an example here.  We try to illustrate the subtleties. ",
     
     	  SUBSECTION "equal and not equal",
     	       "To test if two ideals in the same ring are equal use ", TO "==", ".",
     	       EXAMPLE {
	  	    "R = QQ[a..d];",
	  	    "I = ideal (a^2*b-c^2, a*b^2-d^3, c^5-d);",
	  	    "J = ideal (a^2,b^2,c^2,d^2);",
	  	    "I == J",
	  	    "I != J",
	  	    }
	       ,
	  SUBSECTION "reduction with respect to a Groebner basis and membership",
     	       "The function ", TO "%", " reduces an element with 
     	       respect to a Groebner basis of the ideal. ", 
     	       EXAMPLE {
	  	    "(1+a+a^3+a^4) % J"
	  	    },
     	       "We can then test membership in the ideal by comparing 
     	       the answer to 0 using ", TO "==", ".",
     	       EXAMPLE {
	  	    "(1+a+a^3+a^4) % J == 0",
      	  	    "a^4 % J == 0",
	  	    }
	       ,
     SUBSECTION "containment for two ideals",
	  "Containment for two ideals is tested 
     	  using ", TO "isSubset", ".",
     	  EXAMPLE {
	       "isSubset(I,J)",
	       "isSubset(I,I+J)",
	       "isSubset(I+J,I)"
	       }
	  ,
     SUBSECTION "ideal equal to 1 or 0",
     	  "The function ", TT "I == 1", " checks to see if the 
     	  ideal is equal to the ring.  The function ", TT "I == 0", " checks 
     	  to if the ideal is identically zero in the given ring.",
     	  EXAMPLE {
	       "I = ideal (a^2-1,a^3+2);",
	       "I == 1",
	       "S = R/I",
	       "S == 0"
	       }
	  
     
}

document {
     Key => "extracting generators of an ideal",
     
     	  SUBSECTION "obtain a single generator as an element",
	       "Once an ideal has been constructed it is possible to 
     	       obtain individual elements using ", TO "_", ".   As 
	       always in Macaulay 2, indexing starts at 0. ",
     	       EXAMPLE {
	       	    "R = ZZ[w,x,y,z];",
	       	    "I = ideal(z*w-2*x*y, 3*w^3-z^3,w*x^2-4*y*z^2,x);",
	       	    "I_0",
	       	    "I_3"
	       	    },
	       ,
     	  SUBSECTION "the generators as a matrix or list of elements",
	       "Use ", TO "generators", " or its abbreviation ", TO "gens", " to 
	       get the generators of an ideal ", TT "I", " as a matrix.  
	       Applying ", TT "first entries", " to this matrix converts it 
	       to a list.",
               EXAMPLE{
	       	    "gens I",
	       	    "first entries gens I"
	       	    }
	       ,
     	  SUBSECTION "number of generators",
	       "The command ", TO "numgens", " gives the number of generators 
	       of an ideal ", TT "I", ".",
     	       EXAMPLE{
	       	    "numgens I"
	       	    }     
	       ,
     	  SUBSECTION "minimal generating set",
	       "To obtain a minimal generating set of a homogeneous ideal 
     	       use ", TO "mingens", " to get the minimal generators as a matrix 
	       and use ", TO "trim", " to get the minimal generators as an ideal.",
     	       EXAMPLE {
	       	    "mingens I",
	       	    "trim I"
	       	    },
     	       NOINDENT, "The function ", TT "mingens", " is only well-defined for a 
     	       homogeneous ideal or in a local ring.  However, one can still try to 
     	       get as small a generating set as possible and when it is implemented
     	       this function will be done by ", TT "trim", "."
	       ,
     	  SUBSECTION "obtaining the input form of an ideal",
     	       "If the ideal was defined using a function 
     	       like ", TT "monomialCurveIdeal", " and the generators 
     	       are desired in the usual format for input of an ideal, the 
     	       function ", TO "toString", " is very useful. 
     	       (Note:  We are changing rings because ", TO "monomialCurveIdeal", " 
	       	    is not implemented for rings over ", TT "ZZ", ".)",
     	       EXAMPLE {
	       	    "R = QQ[a..d];",
	       	    "I = monomialCurveIdeal(R,{1,2,3});",
	       	    "toString I"
	       	    }
	       
	  
     }

document {
     Key => "dimension, codimension, and degree",
     "Use ", TO "dim", ", ", TO "codim", ", and ", TO "degree", " to 
     compute the dimension, codimension and degree, respectively, 
     of an ideal.  The functions ", TO "dim", " and ", TO "degree", " compute 
     the dimension and degree of the ring ", TT "R/I", ".",
     EXAMPLE {
	  "R = ZZ/101[x,y,z];",
	  "I = ideal(x^3-y*z^2,x*y-z^2,x*z);",
	  "dim I",
	  "codim I",
	  "degree I",
	  }
     }

document {
     Key => "intersection of ideals",
     "Use ", TO "intersect", " to compute the intersection of two or 
     more ideals.",
     EXAMPLE {
	  "R = QQ[a..d];",
	  "intersect(ideal(a,b),ideal(c*d,a*b),ideal(b*d,a*c))"
	  }
     }

document {
     Key => "ideal quotients and saturation",
     
     	  SUBSECTION "colon and quotient",
	       "The ", TO "quotient", " of two ideals ", TT "I", " 
	       and ", TT "J", " is the same as ", TT "I:J", " and is 
	       the ideal of elements ", TT "f", " such that ", TT "f*J", " is 
	       contained in ", TT "I", ".",
     	       EXAMPLE {
	  	    "R = QQ[a..d];",
	  	    "I = ideal (a^2*b-c^2, a*b^2-d^3, c^5-d);",
	  	    "J = ideal (a^2,b^2,c^2,d^2);",
	  	    "I:J",
	  	    "P = quotient(I,J)"},
     	       "The functions ", TO ":", " and ", TO "quotient", " perform 
     	       the same basic operation, however ", TT "quotient", " takes 
     	       two options.  The first is ", TT "MinimalGenerators", " which 
     	       has default value ", TT "true", " meaning the computation is done 
     	       computing a minimal generating set.  You may want to see all of the 
     	       generators found, setting ", TT "MinimalGenerators", " to ", TT "false", 
     	       " accomplishes this.",
     	       EXAMPLE {
	  	    "Q = quotient(I,J,MinimalGenerators => false)", -- gives odd output.
	  	    "Q == P"
	  	    },
     	       "The second option is ", TT "Strategy", ".  The default 
     	       is to use ", TT "Iterate", " which computes successive 
     	       ideal quotients.  Currently (16 May 2001) the other possible options
     	       do not work.",
	       --     "The other option is ", TT "Linear", " as 
	       --     illustrated.",
	       --     EXAMPLE {
	       --	  "quotient(I,J,Strategy => Linear)" -- NOT IMPLEMENTED!
	       --	  }
     	       ,
	  SUBSECTION "saturation",
     	       "The saturation of an ideal ", TT "I", " with respect to another 
	       ideal ", TT "J", " is the ideal ", TT "(I : J^*)", " defined to 
	       be the set of elements ", TT "f", " in the ring such that J^N*f 
	       is contained in I for some N large enough.  Use the 
	       function ", TO "saturate", " to compute this ideal.  If the 
	       ideal ", TT "J", " is not given, 
	       the ideal ", TT "J", " is taken to be the ideal generated by the 
	       variables of the ring ", TT "R", " of ", TT "I", ".",
    	       PARA,
     	       "For example, one way to homogenize an ideal is to
     	       homogenize the generators and then saturate with respect to
     	       the homogenizing variable.",
	       EXAMPLE {
	  	    "R = ZZ/32003[a..d];",
	  	    "I = ideal(a^3-b, a^4-c)",
	  	    "Ih = homogenize(I,d)",
	  	    "saturate(Ih,d)",
	  	    },
	       "The function ", TT "saturate", " has three optional arguments.  First 
	       a strategy for computation can be chosen.  The options are , ", TO "Linear",
	       ", ", TO "Iterate", ", ", TO "Bayer", ", and ", TO "Elimination", ".  We 
	       leave descriptions of the options to their links, but give an example of the
	       syntax for optional arguments.",
	       EXAMPLE {
		    "saturate(Ih,d,Strategy => Bayer)",
		    },
     	       "The second option is ", TT "DegreeLimit => n", " which specifies that 
	       the computation should halt after dealing with degree n.  The third 
	       option is ", TT "MinimalGenerators => true", " which specifies 
	       that the computation should not only compute the saturation, but a 
	       minimal generating set for that ideal.",
	       
	  
     }



document {
     Key => "radical of an ideal",
      "There are two main ways to find the radical of an ideal.  The first is to use 
      the function ", TO "radical", " and the second is to find the intersection of 
      the minimal prime ideals.  On some large examples the second method is faster.",
       
	   SUBSECTION "using radical",
     		EXAMPLE {
	  	     "S = ZZ/101[x,y,z]",
	  	     "I = ideal(x^3-y^2,y^2*z^2)",
	  	     "radical I"
     	  	     }
		,
	   SUBSECTION "using minimal prime ideals",
     		"An alternate way to find the radical of an 
     		ideal ", TT "I", " is to take the intersection of its 
     		minimal prime ideals.  To find 
		the ", TO "minimal primes of an ideal ", TT "I", " use the 
		function ", TO "decompose", ".  Then use ", TO "intersect", ".",
     		EXAMPLE {
	  	     "intersect decompose I"
	  	     }
     		
	   
      }
 
document {
     Key => "minimal primes of an ideal",
     
	  SUBSECTION "using decompose",
     	       "To obtain a list of the minimal associated primes for an 
     	       ideal ", TT "I", " (i.e. the smallest primes 
     		    containing ", TT "I", "), use the function ", TO "decompose", ".",
     	       EXAMPLE {
	  	    "R = QQ[w,x,y,z];",
	  	    "I = ideal(w*x^2-42*y*z, x^6+12*w*y+x^3*z, w^2-47*x^4*z-47*x*z^2)",
	  	    "decompose I"
	  	    },
     	       NOINDENT, "If the ideal given is a prime ideal 
     	       then ", TT "decompose", " will return the ideal given.",
     	       EXAMPLE {
	  	    "R = ZZ/101[w..z];",
	  	    "I = ideal(w*x^2-42*y*z, x^6+12*w*y+x^3*z, w^2-47*x^4*z-47*x*z^2);",
	  	    "decompose I"
     	  	    },
	       ,
	  SUBSECTION "warning",
     	       "Warning (15 May 2001):  If you stop a 
     	       function mid process and then run ", TT "decompose", " an 
     	       error is given.  Restarting Macaulay 2 and then 
     	       running ", TT "decompose", " works around this.",
     	       PARA,
     	       "See ", TO "associated primes of an ideal", " for information 
     	       on finding associated prime ideals 
     	       and ", TO "primary decomposition", " for more information 
     	       about finding the full primary decomposition of an ideal."   
     	       
	  
     }


document {
     Key => "associated primes of an ideal",
       "The function ", TO "ass", " returns a list of the 
       associated prime ideals for a given ideal ", "I", ".  The 
       associated prime ideals correspond to the irreducible 
       components of the variety associated to ", TT "I", ".  They are 
       useful in many applications in commutative algebra, algebraic 
       geometry and combinatorics.",  
       -- For a tutorial about associated prime ideals and 
       -- primary decomposition, see ", TO "commutative algebra", ".",
       EXAMPLE {
	    "R = ZZ/101[a..d];",
	    "I = ideal(a*b-c*d, (a*c-b*d)^2);",
	    "ass I"
	    },
     "See ", TO "primary decomposition", " for more information 
     about finding primary decompositions.  To find just the 
     minimal prime ideals see ", TO "minimal primes of an ideal", "."   
     }

document {
     Key => "primary decomposition",
     
	  SUBSECTION "introduction",
	       "It is now possible to find the primary decomposition 
     	       of an ideal in Macaulay 2.  The 
     	       function ", TO "primaryDecomposition", " applied to an 
     	       ideal ", TT "I", " returns a list of ideals.  These ideals 
     	       have two key features, first, their intersection is equal to 
     	       the ideal ", TT "I", " and second the ideals are primary.  Therefore 
	       these ideals form
	       a primary decomposition of the ideal.  Since the ideals are primary 
     	       their corresponding varieties are irreducible.  
     	       The decomposition returned is irredundant, which means that 
     	       the radicals of the ideals returned are distinct prime ideals 
     	       which are the associated prime ideals 
     	       for ", TT "I", " (see ", TO "associated primes of an ideal", ")."
	       ,
	  SUBSECTION "example",
	       EXAMPLE {
		    "R = ZZ/101[a..d];",
		    "I = ideal(a*b-c*d, (a*c-b*d)^2);",
		    "primaryDecomposition I"
		    },
	       NOINDENT, "To obtain the associated prime ideals corresponding to the
	       primary components returned by ", TT "primaryDecomposition", " use 
	       the function ", TO "ass", ".  The first entry 
     	       in the list given by ", TT "ass", " is the radical of the first 
     	       entry in the list given by ", TT "primary decomposition", "."
	       ,
     	  SUBSECTION "strategies",
	       "The algorithms available for computing primary decompositions are 
	       Shimoyama-Yokoyama, ", TT "SY", ",  
     	       Eisenbud-Huneke-Vasconcelos, ", TT "EHV", ", a 
     	       hybrid of these two algorithms (SY and EHV), ", TT "Hybrid", ", 
	       and Gianni-Trager-Zacharias, ", TT "GTZ", ".  The 
	       default algorithm in Macaulay 2 is Shimoyama-Yokoyama.  Two 
	       other arguments for the strategy option are available.  These 
	       arguments are ", TT "Monomial", " which computes the unique 
	       irreducible decomposition of a monomial ideal 
	       and ", TT "Binomial", " which computes a cellular decomposion 
	       of a binomial ideal.  For more information on the strategy 
	       options see ", TO "primaryDecomposition(..., Strategy => ...)", ".",
		EXAMPLE {
	       	    "primaryDecomposition(I, Strategy => EHV)",
	       	    },
	       ,
--     	  "An example of a monomial ideal using both monomial and binomial.",
--     	  EXAMPLE {	  "I = ideal(a^2*b,a*c^2,b*d,c*d^2);",
--	       "primaryDecomposition(I, Strategy => Monomial)",
--	       "primaryDecomposition(I, Strategy => Binomial)"
--	       },
	  SUBSECTION "warning",
     	       "Warning (15 May 2001):  This function is under construction.  For 
     	       example, the 
     	       strategies, ", TT "Monomial", ", ", TT "GTZ", " and ", TT "Hybrid", " are 
     	       not written, or do not function as stated.  Further, both 
     	       the ", TT "Monomial", " and ", TT "Binomial", " strategies may 
     	       be moved to separate functions.  "
     	       
	  
     }

       


-------------------
-- RING MAP nodes -
-------------------

document {
     Key => "substitute values for variables",
     "Once a ring is defined that has variables, values can be 
     given to these variables using ", TO "substitute", ".  We give 
     an example.",
     EXAMPLE { 
	  "R = ZZ/101[x,y,z];",
	  "f = x^3+3*y^2*z+2*z^3;",
	  "substitute(f,matrix{{-1,2,5}})",
	  "substitute(f,{x=>-1,y=>2,z=>5})"
	  },
     "The same command works for putting values into ideals or 
     matrices.  Also, it is not required that the values be 
     elements from the coefficient ring, nor do you have to give
     a value for every variable.",
     EXAMPLE {
	  "M = matrix{{x^2,x-y},{x-z,z^2},{y-z,y^2}}",
	  "substitute(M,matrix{{-1,2,x+y}})",
	  "I = ideal M",
	  "substitute(I,{x=>-1,y=>2})"
	  }
     }

document {
     Key => "working with multiple rings",   -- DOUBLE CHECK BEING DONE WITH THIS ONE!
     "Working with multiple rings is more subtle than simply 
     replacing values of the variables in a ring.  On the other 
     hand it is particularly easy in Macaulay2.  We define a 
     sequence of rings below and move between each to show both 
     the dangers and the convenience.",
     
     	  SUBSECTION "defining multiple rings",
     	       EXAMPLE {
	       	    "R1 = ZZ/101;",
	       	    "R2 = ZZ/101[s,t];",
	       	    "describe R2"
	       	    },
     	       "Notice that Macaulay 2 sees the coefficient ring as R1, we could 
     	       just as easily defined ", TT "R2", " as ", TT "R1[s,t]", " .  
     	       Movement and addition between these rings is easy.",
     	       EXAMPLE {
	       	    "I = ideal (s^4+t^2+1);",
	       	    "R3 = R2/I;",
	       	    "describe R3"
	       	    },
     	       "Since ", TT "I", " is defined as an ideal in ", TT "R2", " we
     	       cannot type ", TT "ZZ/101[s,t]/I", " as the computer 
     	       sees ", TT "ZZ/101[s,t]", " as different from ", TT "R2", " and 
     	       so does not see ", TT "I", " as being in this ring.  For more 
     	       about defining rings see ", TO "rings", ".  We now work with 
     	       moving between ", TT "R2", " and ", TT "R3", ".",
	       ,
     	  SUBSECTION "moving between rings using use and substitute",
     	       EXAMPLE {
	       	    "f = s^4+1",
	       	    "g = s^4+t^2+1"
	       	    },
     	       "f and g are elements in ", TT "R3", " now and this is shown by the fact that 
     	       Macaulay2 sees them as ", TT "-t^2", " and ", "0.  To recover 
     	       these elements as polynomials in ", TT "R2", " type ", TT "use R2", " and 
     	       define them again in ", TT "R2", ".  The command substitute 
     	       does not work well here, where as if we want to see the image
     	       of elements of ", TT "R2", " in ", TT "R3", " it does work well 
     	       and without using the command ", TT "use", ".  Macaulay2 always tells you 
     	       which ring an element is in on the line after it prints the 
     	       ring element.",
     	       EXAMPLE {
	       	    "use R2;",
	       	    "substitute(g,R2)",
	       	    "f = s^4+1",
	       	    "g = s^4+t^2+1",
	       	    "substitute(f,R3)"
	       	    },
	       ,
     	  SUBSECTION "subtleties of substitute and describe",
     	       "Now we complicate things further by constructing a fraction 
     	       field and then further constructing polynomial rings and 
     	       quotient rings.  First we see that while ", TT "describe", " helped
     	       us to see how we defined ", TT "R2", " and ", TT "R3", ", the 
     	       same does not hold when 
     	       a fraction field is constructed.  Note that R3 is a domain.",
     	       EXAMPLE {
	       	    "describe R3",
	       	    "R4 = frac R3;",
	       	    "describe R4"
	       	    },
     	       "The command ", TT "substitute", " works well to move elements 
     	       from ", TT "R2", " or ", TT "R3", " to ", TT "R4", " substitute 
     	       works well here. An alternative to substitute is to form the canonical 
     	       injection of R3 into R4 (the same can be done for the canonical 
	       	    projection from R2 to R3 above - we do the example here).   For 
     	       more on ring maps, 
     	       see ", TO "basic construction source and target of a ring map", ".  
     	       Again to move elements 
      	       from ", TT "R4", " back to ", TT "R3", " an alternate method must 
	       be used.  Also, 
     	       the method of constructing a map does not work well in the reverse 
     	       direction for the same reasons ", TT "substitute", " does not.",
     	       EXAMPLE {
	       	    "use R2;",
	       	    "f = s^4+1;",
	       	    "substitute(f,R4)",
	       	    "use R3;",
	       	    "g = substitute(f,R3);",
	       	    "substitute(g,R4)",
	       	    "F = map(R4,R3)",
	       	    "F(f)"
	       	    },
	       ,
     	  SUBSECTION "non-standard coefficient fields",
	       "We can go through the whole process again using R4 now as the field.",
	       EXAMPLE {
	       	    "R5 = R4[u,v,w];",
	       	    "describe R5",
	       	    "J = ideal(u^3-v^2*w+w^3,v^2+w^2,u*v-v*w+u*w)",
	       	    "R6 = R5/J;",
	       	    "describe R6"
	       	    },
	       "Notice that at each stage Macaulay2 only refers back to the last 
	       ring we defined.  All of the methods above work still here in theory, but 
	       caution is advised.  We give an example below to illustrate.  Also, 
	       note that many other computations will no longer work, because 
	       Groebner basis computations only work 
	       over ", TT "ZZ", ", ", TT "ZZ/n", " and ", TT "QQ", " at this time. "
	       ,
     	  SUBSECTION "using maps to move between rings",
	       EXAMPLE {
	       	    "map(R6,R2)",
	       	    "substitute(f,R6)"
	       	    },
	       "Macaulay 2 claims this is the zero map, and that the image 
	       of ", TT "f", " is 1, but we know better.  By 
	       forming a series of maps and composing them we see the map that 
	       makes sense.  We also contrast the map with 
	       using ", TT "substitute", ".",
	       EXAMPLE {
	       	    "use R2;",
	       	    "f = s^4+1;",
	       	    "F = map(R4,R2);",
	       	    "G = map(R5,R4);",
	       	    "H = map(R6,R5);",
	       	    "H(G(F(f)))",
	       	    "f1 = substitute(f,R4)",
	       	    "f2 = substitute(f1,R5)",
	       	    "substitute(f2,R6)"
	       	    },
	       ,
     	  SUBSECTION "elements versus matrices",
	       "Finally, note that everywhere we used the element ", TT "f", " we 
	       can place a matrix or an ideal and get similar results."
	       ,
     	  SUBSECTION "substitute(J,vars R)",
	       "We close this long example with a brief discussion 
	       of ", TT "substitute(J,vars R)", ".  This command is more 
	       sensitive than ", TT "substitute", " as it will give an error 
	       message when the variables involved do not match up.",
	       EXAMPLE {
	       	    "substitute(f,vars R3)",
	       	    ///try substitute(f,vars R5) else "found error"///
	       	    }
	       
     	  
     }

document {
     Key => "basic construction, source and target of a ring map",
     
	  SUBSECTION "constructing a ring map", 
	       "Use the function ", TO "map", " construct a map 
	       between two rings.  The input, in order, is the 
	       target, the source, and the images of the 
	       variables of the source ring.  The images can 
	       be given as a matrix or a list.",
	       EXAMPLE {
		    "S = QQ[x,y,z]/ideal(x^3+y^3+z^3);",
		    "T = QQ[u,v,w]/ideal(u^3+v^3+w^3);",
		    "G = map(T,S,matrix{{u,v,w^2}})",
		    "G(x^3+y^3+z)",
		    },
	       "If the third argument is not given there are two 
	       possibilities.  If a variable 
	       in the source ring also appears in the target ring then that 
	       variable is mapped to itself and if a variable does not appear 
	       in the target ring then it is mapped to zero.",
	       EXAMPLE {
		    "R = QQ[x,y,w];",
		    "F = map(S,R)",
		    "F(x^3)"
		   }
	      ,
	 SUBSECTION "source and target",
	      "Once a ring map is defined the functions ", TO "source", " 
	      and ", TO "target", " can be used to find out what the source 
	      and target of a map are.  These functions are particularly useful 
	      when working with matrices (see the next example). ",
	      EXAMPLE {
		   "U = QQ[s,t,u, Degrees => {{1,2},{1,1},{1,3}}];",
		   "H = map(U,R,matrix{{s^2,t^3,u^4}})",
		   "use R; H(x^2+y^2+w^2)",
		   "source H",
		   "target H",
		   },
	      ,
	 SUBSECTION "obtaining the matrix defining a map",
	      "Use ", TT "F.matrix", " to obtain the matrix defining
	      the map F.",
	      EXAMPLE {
	      	   "H.matrix",
		   "source H.matrix",
		   "target H.matrix",
		   },
	      "For more on matrices from maps see ", TO "input a matrix", "."
	      
	 
    }

document {
     Key => "evaluation and composition of ring maps",
     
	  SUBSECTION "evaluating ring maps",
     	       "Once a ring map ", TT "F", " is defined, the image of an 
     	       element ", TT "m", " in the source ring can be found by applying 
     	       the map as ", TT "F(m)", ".",
	       EXAMPLE {
		    "R = ZZ[x,y,z];",
		    "S = ZZ/101[x,y,z,Degrees => {{1,2},{1,3},{1,3}}]/ideal(x+z^3);",
		    "F = map(S,R,{x,y^2,z^3})",
		    "use R; F(107*x+y+z)"
		    }
	       ,
	  SUBSECTION "composition of ring maps",  
	       -- see if you can't do something with galois.
	       "The function ", TO (symbol*,RingMap,RingMap), "performs a 
	       composition of ring maps.  Evaluation of elements in the source 
	       of a ring map ", TT "G"," can also be done using", TT "F(G(m))", ".",
	       EXAMPLE { 
		    "T = ZZ/5[x,y];",
		    "G = map(T,S);",
		    "G*F",
		    "use R; G(F(107*x+y+z))",
		    },
	       
	  
     }


document {
     Key => "kernel and image of a ring map",
     "The kernel and image of a ring map can be computed 
     using ", TO "image", " and ", TO "ker", " .  The output 
     of ", TT "ker", " is an ideal and the output of ", TT "image", "is a 
     ring or quotient ring.",
     EXAMPLE {
	  "R = QQ[x,y,w]; U = QQ[s,t,u]/ideal(s^2);",
	  "H = map(U,R,matrix{{s^2,t^3,u^4}})",
	  "ker H",
	  "image H"
	  }
     -- if module and ring map are homogeneous, and Hilbert F is known,
     -- this is used in computing the kernel (or image).
     }

--- For matrices in overview.m2  --- GB stuff is in there also.

-------------------
-- Matrix nodes ---
-------------------

document {
     Key => "input a matrix",
     
	  SUBSECTION "by its entries",
	       "Using the function ", TO "matrix", " is the most basic method 
	       for inputting a matrix.  The entries are typed in by rows.",
	       EXAMPLE {
		    "R = ZZ/5[s..z];",
		    "M = matrix {{ x^2+y, z^3}, {y^3-z,3*z-6*x-5*y}}"
		    }
	       ,
	  SUBSECTION "by a function",  
	       "The function ", TO "map", " can be used to construct 
	       matrices. ", 
	       EXAMPLE {
		    "G = map(R^3,3,(i,j)->R_i^j)",
		    "f = 3*s^2*v-t*u*v+s*t^2",
		    "H = map(R^4,R^4,(i,j)->diff(R_j*R_i,f))"
		    }
	       ,
	  SUBSECTION "identity matrix",
	       "The function ", TO "id", " is used to form the identity matrix 
	       as a map from a module to itself.  ",
	       EXAMPLE {
		    "id_(R^3)",
		    "id_(coker M)"
		    },
	       "The first example gives a 3x3 identity matrix formed in the ambient ring. "
	       
	  
     }

document {
     Key => "random and generic matrices",
     
	  SUBSECTION "random matrices",
	       "To construct a random m by n matrix with entries in a ring 
	       R use the function ", TO "random", " by 
	       typing ", TT "random(R^m,R^n)", ".",
	       EXAMPLE {
		    "R = GF(3^2,Variable => a);",
		    "random(R^3,R^4)"
		    }
	       ,
	  SUBSECTION "matrices of variables",
	       "To build an m by n matrix of variables drawn from the ring R, 
	       use ", TO "genericMatrix", ".  The syntax 
	       is ", TT "genericMatrix(R,x,m,n)", " where R is the ring, x is 
	       the variable where we start and m and n specify the size of 
	       the matrix.",
	       EXAMPLE {
		    "S = R[p..z];",
		    "genericMatrix(S,t,3,2)",
		       },
		  "Note that to use the function genericMatrix the number of 
		  variables in the ring R must be at least as large as ", TT "m*n", "."
		  ,
	  SUBSECTION "genericSymmetricMatrix",
	       "To construct an n by n symmetric matrix whose entries on and above 
	       the diagonal are the variables of R use ", TO "genericSymmetricMatrix", ".  
	       The syntax is ", TT "genericSymmetricMatrix(R,x,n)", " where R is 
	       the ring, x is the variable you want to start with and n is the 
	       size of the matrix.",
	       EXAMPLE { 
		    "genericSymmetricMatrix(S,s,3)"
		    }
	       ,
	  SUBSECTION "genericSkewMatrix",
	       "To construct an n by n skew symmetric matrix whose 
	       entries above the diagonal are the variables of R 
	       use ", TO "genericSkewMatrix", ".  The syntax 
	       is ", TT "genericSkewMatrix(R,x,n)", " where R is the 
	       ring, x is the variable you want to start with and n is the 
	       size of the matrix.",
	       EXAMPLE { 
		    "genericSymmetricMatrix(S,u,3)"
	       	    }     
	       
	  
     }

document {
     Key => "concatenating matrices",
     
	  SUBSECTION "concatenate horizontally",
	       "Use ", TO "|", "to concatenate two matrices horizontally.",
	       EXAMPLE {
		    "R = ZZ/32003[a..f];",
		    "M = genericMatrix(R,a,3,2)",
		    "N = matrix{{d^2,a*d},{b*c,b*d},{a,c}}",
		    "M|N"
		    }
	       ,	       
	  SUBSECTION "concatenate vertically",
	       "Use ", TO "||", "to concatenate two matrices vertically.",
	       EXAMPLE {
		    "P = matrix{{d^2,a*d,e*f},{b*c,b*d,b*e},{a,c,d}}",
		    "transpose(M)||P"
		    }
	       ,	       
	  SUBSECTION "making block matrices",
	       "The matrix function can take matrices as input as long as the sizes 
	       match up.  ",
	       EXAMPLE { 
	       "matrix{{id_(R^3),M,P},{random(R^1,R^3),random(R^1,R^3),random(R^1,R^2)}}"
	       	    },
	       "Also, the number input entries in each row must be equal.  It might 
	       seem like we could form the same matrix with the 
	       input ", TT "matrix{{id_(R^3),M,P},{random(R^1,R^8)}}", " 
	       since ", TT "random(R^1,R^8)", " will construct a 1 by 8 matrix which 
	       has the same number of columns as 
	       matrix ", TT "matrix{{id_(R^3),M,P}}", " but as input into the 
	       matrix function that row entry must have 3 entries."
	       ,	       
	  SUBSECTION "direct sum of matrices as maps between modules", 
	       "++"
	       
	  
     }

document {
     Key => "simple information about a matrix",
      
	  SUBSECTION "ring",
	       ,	       
	  SUBSECTION "target",
	       ,	       
	  SUBSECTION "source",
	       ,	       
	  SUBSECTION "extracting an element from a matrix",
	       ,	       
	  SUBSECTION "submatrix",
	       ,	       
	  SUBSECTION "number of rows or columns",
	       ,	       
	  SUBSECTION "entries"
	       
	  
     }

document {
     Key => "basic arithmetic of matrices",
     
	  SUBSECTION "+",
	       ,	       
	  SUBSECTION "-",
	       ,	       
	  SUBSECTION "*",
	       ,	       
	  SUBSECTION "^",
	       ,	       
	  SUBSECTION "inverse of a matrix",
	       ,	       
	  SUBSECTION "==", -- m == n, m-n == 0 are different
	       ,	       
	  SUBSECTION "!=",
	       ,	       
	  SUBSECTION "**"
	       
	  
     }

document {
     Key => "kernel, cokernel and image of a matrix",
     
	  SUBSECTION "kernel", " -- (synonym is 'ker')",
	       ,	       
	  SUBSECTION "image",
	       ,	       
	  SUBSECTION "cokernel"
	       
	  
     }

document {
     Key => "differentiation",
     
	  SUBSECTION "diff",
	       ,	       
	  SUBSECTION "diff'",
	       ,	       
	  SUBSECTION "contract",
	       ,	       
	  SUBSECTION "contract'",
	       ,	       
	  SUBSECTION "jacobian"
	       
	  
     }

document {
     Key => "rank of a matrix",
     
	  SUBSECTION "rank",
	       ,	       
	  SUBSECTION "random rank of a matrix"
	       
	  
     }

document {
     Key => "determinants and minors",
     
	  SUBSECTION "det",
	       ,	       
	  SUBSECTION "minors"
	       
	  
     }

document {
     Key => "Pfaffians",
     
	  SUBSECTION "pfaffians"
	       
	  
     }

document {
     Key => "exterior power of a matrix",
     
	  SUBSECTION "exteriorPower"
	       
	  
     }

document {
     Key => "format and display of matrices in Macaulay 2",
     
	  SUBSECTION "compactMatrixForm",
	       
	  
     }

document {
     Key => "importing and exporting matrices",
     
	  SUBSECTION "toString",
	       ,
	  SUBSECTION "toExternalString"
	       	       
	  
     }


-- Local Variables:
-- compile-command: "make -C $M2BUILDDIR/Macaulay2/m2 "
-- End:
