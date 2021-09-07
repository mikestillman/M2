restart
L = lines get "P4Surfaces.txt";
--L/(s -> if #s < 20 then s else substring(s, 0, 20))

toClassic = method()
toClassic RingElement := (f) -> (
    s := toString f;
    s = replace("\\*", "", s);
    s = replace("\\^", "", s);
    s
    )
toClassic Ideal := (I) -> (
    innards := concatenate between(",", I_*/toClassic);
    "ideal\"" | innards | "\""
    )

count = 0
outstuff = for s in L list (
    print count;
    count = count + 1;
    if match("Surfaces =", s) then s else
    if not match("ideal", s) then (value s; s)
    else (
        I = elapsedTime value s;
        trimI = elapsedTime trim I;
        toClassic trimI
    )
);
"foo" << concatenate between("\n", outstuff) << endl << close

needsPackage("SurfacesInP4", FileName => "../SurfacesInP4.m2")
Ptrimmed = readExampleFile "./foo";
P = readExampleFile "P4surfaces.txt";
keys Ptrimmed === keys P
for k in keys P do (
    I1 := example(k, P);
    I2 := example(k, Ptrimmed);
    I2 = sub(I2, ring I1);
    if gens trim I1 != gens I2 then error ("trimming not correct: "|k);
    if I1 != I2 then error ("not correct: "|k);
    )
    
elapsedTime for k in keys P list example(k, P); -- 13.1 sec
elapsedTime for k in keys P list example(k, Ptrimmed); -- 7.3 sec
