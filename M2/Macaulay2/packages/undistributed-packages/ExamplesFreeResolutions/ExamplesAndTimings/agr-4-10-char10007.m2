R1 = (ZZ/10007)[a, b, c, d, e, f, g, h, i, j, k]
I1 = ideal(
    j^2*k-361*a*k^2-2561*b*k^2-728*c*k^2+1107*d*k^2+301*e*k^2+2607*f*k^2+4010*g*k^2-2035*h*k^2+1252*i*k^2-4830*j*k^2+3475*k^3,
    i*j*k-1450*a*k^2+367*b*k^2-3197*c*k^2+31*d*k^2-2144*e*k^2+453*f*k^2+439*g*k^2-3295*h*k^2+1812*i*k^2+422*j*k^2-2426*k^3,
    h*j*k+320*a*k^2+4407*b*k^2-4506*c*k^2+2048*d*k^2-4185*e*k^2-3284*f*k^2+3144*g*k^2+358*h*k^2-1845*i*k^2-2650*j*k^2-303*k^3,
    g*j*k+4315*a*k^2-4971*b*k^2-2182*c*k^2-2569*d*k^2+4611*e*k^2-1220*f*k^2+4477*g*k^2+1241*h*k^2-4018*i*k^2-425*j*k^2-2032*k^3,
    f*j*k+2193*a*k^2+2540*b*k^2+3962*c*k^2-3732*d*k^2+2883*e*k^2+3654*f*k^2+2166*g*k^2-2330*h*k^2+4795*i*k^2+61*j*k^2+4580*k^3,
    e*j*k+270*a*k^2+2976*b*k^2+2499*c*k^2+4038*d*k^2+225*e*k^2+4120*f*k^2-1059*g*k^2+1964*h*k^2-3869*i*k^2+1841*j*k^2+821*k^3,
    d*j*k-1068*a*k^2-2024*b*k^2+4877*c*k^2-3431*d*k^2-2817*e*k^2-3191*f*k^2+4226*g*k^2-3439*h*k^2-4101*i*k^2-1122*j*k^2-4433*k^3,
    c*j*k+2853*a*k^2-687*b*k^2-513*c*k^2+1379*d*k^2+4900*e*k^2+3631*f*k^2-4609*g*k^2+655*h*k^2-4849*i*k^2+980*j*k^2-1740*k^3,
    b*j*k+1622*a*k^2-824*b*k^2-457*c*k^2+464*d*k^2-1190*e*k^2+1091*f*k^2+4837*g*k^2+1671*h*k^2-3718*i*k^2-306*j*k^2-3671*k^3,
    a*j*k-407*a*k^2+2226*b*k^2+1270*c*k^2-833*d*k^2-60*e*k^2-4585*f*k^2-3110*g*k^2+3452*h*k^2-1973*i*k^2-329*j*k^2+115*k^3,
    i^2*k-2478*a*k^2+2060*b*k^2+657*c*k^2-4364*d*k^2+4026*e*k^2+3775*f*k^2-4275*g*k^2-1502*h*k^2+487*i*k^2+1298*j*k^2+637*k^3,
    h*i*k-1944*a*k^2+3293*b*k^2-3880*c*k^2-1054*d*k^2+585*e*k^2-1932*f*k^2-3112*g*k^2+1132*h*k^2-4573*i*k^2-556*j*k^2+3249*k^3,
    g*i*k+4596*a*k^2-3190*b*k^2+3599*c*k^2-1615*d*k^2+3244*e*k^2+3311*f*k^2-2115*g*k^2+1603*h*k^2-3142*i*k^2+693*j*k^2-792*k^3,
    f*i*k-587*a*k^2-2266*b*k^2-1006*c*k^2+3668*d*k^2+2124*e*k^2+2446*f*k^2-2668*g*k^2-4255*h*k^2+4952*i*k^2-782*j*k^2-537*k^3,
    e*i*k+2573*a*k^2-56*b*k^2-3584*c*k^2+3493*d*k^2-4817*e*k^2+4174*f*k^2-3225*g*k^2+1107*h*k^2-1031*i*k^2+4008*j*k^2-4912*k^3,
    d*i*k+962*a*k^2+611*b*k^2+2133*c*k^2-2378*d*k^2-2658*e*k^2-829*f*k^2+2805*g*k^2+297*h*k^2+170*i*k^2+3171*j*k^2-2645*k^3,
    c*i*k-4843*a*k^2-3051*b*k^2+1091*c*k^2+2913*d*k^2-2533*e*k^2-2712*f*k^2-4216*g*k^2-2278*h*k^2-4263*i*k^2+1149*j*k^2-3988*k^3,
    b*i*k-4941*a*k^2-2626*b*k^2+737*c*k^2+1457*d*k^2-4247*e*k^2+2346*f*k^2+3819*g*k^2+2395*h*k^2+3308*i*k^2+3733*j*k^2-2162*k^3,
    a*i*k+3107*a*k^2-3772*b*k^2-2929*c*k^2+1568*d*k^2+4384*e*k^2+3426*f*k^2+1390*g*k^2-2267*h*k^2-219*i*k^2+4426*j*k^2+1343*k^3,
    h^2*k-4784*a*k^2-4940*b*k^2-165*c*k^2-3695*d*k^2-4573*e*k^2-2949*f*k^2-1973*g*k^2-4610*h*k^2+589*i*k^2+3727*j*k^2-2928*k^3,
    g*h*k-2681*a*k^2+2618*b*k^2+822*c*k^2+330*d*k^2+2400*e*k^2-4447*f*k^2+511*g*k^2-2705*h*k^2-2901*i*k^2-4371*j*k^2-3693*k^3,
    f*h*k+4362*a*k^2+4178*b*k^2-3108*c*k^2-4038*d*k^2+2210*e*k^2-2452*f*k^2-1623*g*k^2+2569*h*k^2-3733*i*k^2+1500*j*k^2-864*k^3,
    e*h*k+4071*a*k^2+1386*b*k^2+3404*c*k^2+3158*d*k^2-3178*e*k^2+3505*f*k^2-1730*g*k^2-2679*h*k^2-4639*i*k^2-1517*j*k^2+1533*k^3,
    d*h*k-2412*a*k^2-1251*b*k^2-1649*c*k^2-2496*d*k^2+853*e*k^2-3139*f*k^2+2561*g*k^2+1910*h*k^2+5001*i*k^2-1086*j*k^2+2536*k^3,
    c*h*k+1351*a*k^2+3000*b*k^2-433*c*k^2+4459*d*k^2+4969*e*k^2+1914*f*k^2+4729*g*k^2+4221*h*k^2+2587*i*k^2+3007*j*k^2+3595*k^3,
    b*h*k-2434*a*k^2+4334*b*k^2+4553*c*k^2+3724*d*k^2-1904*e*k^2-4589*f*k^2-3437*g*k^2-2030*h*k^2-2036*i*k^2-4427*j*k^2-323*k^3,
    a*h*k-4786*a*k^2-1974*b*k^2+3696*c*k^2+2160*d*k^2-2070*e*k^2-3886*f*k^2-2035*g*k^2+5001*h*k^2-366*i*k^2+4642*j*k^2-4900*k^3,
    g^2*k+3470*a*k^2+838*b*k^2+4220*c*k^2+3588*d*k^2+2630*e*k^2+441*f*k^2+2853*g*k^2-4620*h*k^2-2758*i*k^2-2003*j*k^2-180*k^3,
    f*g*k-4080*a*k^2-90*b*k^2+3383*c*k^2-2685*d*k^2-1760*e*k^2+929*f*k^2+1713*g*k^2-948*h*k^2+1395*i*k^2-4959*j*k^2+3762*k^3,
    e*g*k-3688*a*k^2-2993*b*k^2+2995*c*k^2+947*d*k^2+4929*e*k^2+3082*f*k^2+1768*g*k^2-4137*h*k^2+1963*i*k^2+3343*j*k^2-3056*k^3,
    d*g*k-156*a*k^2-4925*b*k^2+976*c*k^2-2666*d*k^2+2846*e*k^2-1001*f*k^2-104*g*k^2-4275*h*k^2+3867*i*k^2+3794*j*k^2-1203*k^3,
    c*g*k-2648*a*k^2-161*b*k^2-4894*c*k^2-3558*d*k^2+1208*e*k^2+917*f*k^2+2783*g*k^2-2514*h*k^2-252*i*k^2+3833*j*k^2+1266*k^3,
    b*g*k+4988*a*k^2-4466*b*k^2+351*c*k^2-2994*d*k^2+3673*e*k^2+f*k^2+282*g*k^2+4292*h*k^2+2408*i*k^2-3564*j*k^2+2377*k^3,
    a*g*k+45*a*k^2+4499*b*k^2-2506*c*k^2-2819*d*k^2+4052*e*k^2-3921*f*k^2+18*g*k^2-3308*h*k^2-3438*i*k^2-4796*j*k^2-2137*k^3,
    f^2*k-836*a*k^2+1646*b*k^2+1957*c*k^2-3529*d*k^2-3977*e*k^2-1753*f*k^2+4435*g*k^2-571*h*k^2+1565*i*k^2-2624*j*k^2-4174*k^3,
    e*f*k-836*a*k^2+4038*b*k^2+643*c*k^2+428*d*k^2+4790*e*k^2-3133*f*k^2+1752*g*k^2-4394*h*k^2+2568*i*k^2-338*j*k^2-236*k^3,
    d*f*k-4236*a*k^2-4443*b*k^2+3308*c*k^2-3974*d*k^2-4293*e*k^2+2504*f*k^2-881*g*k^2+950*h*k^2+4937*i*k^2+204*j*k^2-2379*k^3,
    c*f*k-3230*a*k^2-3860*b*k^2-1291*c*k^2-2267*d*k^2-4405*e*k^2-4172*f*k^2+1882*g*k^2-599*h*k^2-4432*i*k^2+129*j*k^2+2152*k^3,
    b*f*k-1178*a*k^2+994*b*k^2+3350*c*k^2+4925*d*k^2+133*e*k^2-1828*f*k^2-4260*g*k^2+2456*h*k^2-837*i*k^2+1517*j*k^2-3605*k^3,
    a*f*k-2848*a*k^2+4176*b*k^2-1817*c*k^2-4951*d*k^2-1039*e*k^2+1759*f*k^2-3053*g*k^2-3856*h*k^2+2487*i*k^2-1079*j*k^2+1615*k^3,
    e^2*k-1097*a*k^2-4420*b*k^2-2737*c*k^2-2019*d*k^2+2498*e*k^2-1154*f*k^2-275*g*k^2-1720*h*k^2+3447*i*k^2+816*j*k^2+2643*k^3,
    d*e*k-1384*a*k^2+3380*b*k^2+3233*c*k^2-1596*d*k^2+2058*e*k^2+3783*f*k^2-643*g*k^2+364*h*k^2+2296*i*k^2-379*j*k^2+1677*k^3,
    c*e*k-114*a*k^2+2768*b*k^2+3898*c*k^2+1817*d*k^2-3651*e*k^2-1281*f*k^2-874*g*k^2-822*h*k^2+1284*i*k^2-1458*j*k^2+3581*k^3,
    b*e*k-4917*a*k^2-721*b*k^2-4042*c*k^2+4018*d*k^2+4617*e*k^2+310*f*k^2-4477*g*k^2+2229*h*k^2+594*i*k^2-1023*j*k^2+4036*k^3,
    a*e*k-2867*a*k^2+4820*b*k^2-4827*c*k^2+4569*d*k^2-3566*e*k^2-543*f*k^2+3238*g*k^2-4964*h*k^2+4265*i*k^2+881*j*k^2+3072*k^3,
    d^2*k-4867*a*k^2+4807*b*k^2-2470*c*k^2-672*d*k^2+1577*e*k^2+4004*f*k^2+2254*g*k^2+436*h*k^2-753*i*k^2+160*j*k^2+1499*k^3,
    c*d*k-4800*a*k^2-2959*b*k^2-3391*c*k^2+2200*d*k^2+2343*e*k^2+1011*f*k^2+1791*g*k^2+585*h*k^2+808*i*k^2+1310*j*k^2+4356*k^3,
    b*d*k-3101*a*k^2-2014*b*k^2-4637*c*k^2-3430*d*k^2-4953*e*k^2-4021*f*k^2-4076*g*k^2-2872*h*k^2+2142*i*k^2+821*j*k^2+1082*k^3,
    a*d*k+1162*a*k^2-3971*b*k^2+773*c*k^2+4866*d*k^2+4831*e*k^2-1251*f*k^2-1192*g*k^2+292*h*k^2+3329*i*k^2+4255*j*k^2-3554*k^3,
    c^2*k+2265*a*k^2-1802*b*k^2+3310*c*k^2+1790*d*k^2-3734*e*k^2+3335*f*k^2+2975*g*k^2-3047*h*k^2-1846*i*k^2+2007*j*k^2+3728*k^3,
    b*c*k+1905*a*k^2+4308*b*k^2-2100*c*k^2+1794*d*k^2-355*e*k^2-1429*f*k^2+542*g*k^2+4235*h*k^2-4243*i*k^2-2250*j*k^2+3330*k^3,
    a*c*k-4202*a*k^2+3013*b*k^2+4098*c*k^2+3012*d*k^2-3870*e*k^2+3165*f*k^2+1985*g*k^2+4079*h*k^2-1418*i*k^2-1813*j*k^2+1180*k^3,
    b^2*k+2152*a*k^2-1809*b*k^2-4062*c*k^2-2371*d*k^2-1891*e*k^2+735*f*k^2-354*g*k^2+87*h*k^2-3321*i*k^2+820*j*k^2+1500*k^3,
    a*b*k-1058*a*k^2-2760*b*k^2-529*c*k^2-85*d*k^2+595*e*k^2+3208*f*k^2+3852*g*k^2-4004*h*k^2-3377*i*k^2+3960*j*k^2-3098*k^3,
    a^2*k-403*a*k^2+480*b*k^2-4709*c*k^2-71*d*k^2+4068*e*k^2+3875*f*k^2+1748*g*k^2+2502*h*k^2+4570*i*k^2-4752*j*k^2-2750*k^3,
    j^3-2387*a*k^2-3778*b*k^2-136*c*k^2-2718*d*k^2-187*e*k^2-4181*f*k^2-1387*g*k^2-276*h*k^2+3474*i*k^2-3935*j*k^2-2470*k^3,
    i*j^2-1888*a*k^2-1743*b*k^2-3488*c*k^2+882*d*k^2-600*e*k^2-820*f*k^2-2209*g*k^2-1790*h*k^2-1214*i*k^2-1332*j*k^2-458*k^3,
    h*j^2+399*a*k^2+1648*b*k^2-452*c*k^2-2075*d*k^2-2440*e*k^2-4593*f*k^2+2980*g*k^2+481*h*k^2+1970*i*k^2+2440*j*k^2-4541*k^3,
    g*j^2+519*a*k^2-3342*b*k^2+4616*c*k^2+2004*d*k^2-4377*e*k^2-1287*f*k^2-2533*g*k^2-576*h*k^2+1654*i*k^2-47*j*k^2-2711*k^3,
    f*j^2-582*a*k^2-4977*b*k^2-3685*c*k^2-420*d*k^2-1572*e*k^2-356*f*k^2+749*g*k^2-1837*h*k^2+2614*i*k^2+2232*j*k^2-3438*k^3,
    e*j^2-3927*a*k^2-3513*b*k^2+4233*c*k^2-357*d*k^2-308*e*k^2-1970*f*k^2-1266*g*k^2-4865*h*k^2+2360*i*k^2+385*j*k^2-3878*k^3,
    d*j^2+4835*a*k^2+1640*b*k^2+1912*c*k^2+3189*d*k^2+3930*e*k^2-4660*f*k^2-1164*g*k^2-46*h*k^2+2570*i*k^2-1704*j*k^2-2637*k^3,
    c*j^2+331*a*k^2+3493*b*k^2-2705*c*k^2-3750*d*k^2-171*e*k^2-3988*f*k^2+1520*g*k^2+750*h*k^2+995*i*k^2+4764*j*k^2+2886*k^3,
    b*j^2-2092*a*k^2+1832*b*k^2-1581*c*k^2+2236*d*k^2-3319*e*k^2+4625*f*k^2+1765*g*k^2+3539*h*k^2-1811*i*k^2+3056*j*k^2-1865*k^3,
    a*j^2-1674*a*k^2+3796*b*k^2+8*c*k^2+2255*d*k^2-2197*e*k^2+3035*f*k^2-3935*g*k^2+1864*h*k^2+4814*i*k^2-1463*j*k^2-3885*k^3,
    i^2*j+397*a*k^2+3445*b*k^2-2829*c*k^2+808*d*k^2+1448*e*k^2+4663*f*k^2-2581*g*k^2-2483*h*k^2+604*i*k^2-2129*j*k^2+505*k^3,
    h*i*j-3766*a*k^2+1160*b*k^2-1362*c*k^2+2434*d*k^2-1361*e*k^2-450*f*k^2+401*g*k^2-4426*h*k^2-1416*i*k^2-4104*j*k^2+2010*k^3,
    g*i*j-2431*a*k^2-2680*b*k^2+1882*c*k^2+1770*d*k^2-2499*e*k^2+619*f*k^2-1409*g*k^2+2363*h*k^2+4083*i*k^2+3396*j*k^2-4815*k^3,
    f*i*j-2170*a*k^2-3629*b*k^2-4890*c*k^2+807*d*k^2-4160*e*k^2+3137*f*k^2-3190*g*k^2-1940*h*k^2-319*i*k^2+3092*j*k^2-3983*k^3,
    e*i*j-1886*a*k^2+4092*b*k^2-1892*c*k^2+1158*d*k^2-3547*e*k^2+330*f*k^2+1254*g*k^2+761*h*k^2+1104*i*k^2+3961*j*k^2+3683*k^3,
    d*i*j+3962*a*k^2+232*b*k^2-463*c*k^2+494*d*k^2-2053*e*k^2+108*f*k^2+2939*g*k^2-1798*h*k^2-623*i*k^2+675*j*k^2-3903*k^3,
    c*i*j-1196*a*k^2+1533*b*k^2-2367*c*k^2-1024*d*k^2+49*e*k^2-3720*f*k^2+4188*g*k^2-311*h*k^2-1547*i*k^2-3977*j*k^2-1600*k^3,
    b*i*j+3044*a*k^2-4517*b*k^2-2486*c*k^2-4921*d*k^2+870*e*k^2+2426*f*k^2-1636*g*k^2+3515*h*k^2-3521*i*k^2-3359*j*k^2+967*k^3,
    a*i*j+3826*a*k^2-4433*b*k^2+4359*c*k^2+652*d*k^2+2937*e*k^2-161*f*k^2-1684*g*k^2-4096*h*k^2+2045*i*k^2-2304*j*k^2-2969*k^3,
    h^2*j+2524*a*k^2-2151*b*k^2+4288*c*k^2+468*d*k^2-965*e*k^2-3335*f*k^2-326*g*k^2+446*h*k^2+3844*i*k^2-4146*j*k^2+3377*k^3,
    g*h*j-585*a*k^2+790*b*k^2+2939*c*k^2-668*d*k^2+2644*e*k^2+4282*f*k^2-4287*g*k^2+806*h*k^2-547*i*k^2-496*j*k^2+4472*k^3,
    f*h*j-4799*a*k^2+3363*b*k^2-3361*c*k^2-4425*d*k^2-1785*e*k^2+2047*f*k^2+2358*g*k^2+2770*h*k^2-2712*i*k^2-2958*j*k^2-3151*k^3,
    e*h*j-3732*a*k^2-3472*b*k^2-1990*c*k^2-519*d*k^2+982*e*k^2+3265*f*k^2+928*g*k^2-1804*h*k^2+4588*i*k^2+2888*j*k^2-4164*k^3,
    d*h*j-4477*a*k^2+396*b*k^2-807*c*k^2+271*d*k^2-4247*e*k^2-3260*f*k^2+3001*g*k^2+4464*h*k^2+1636*i*k^2-4083*j*k^2-2004*k^3,
    c*h*j+2202*a*k^2-2992*b*k^2+4709*c*k^2-3727*d*k^2+521*e*k^2-4674*f*k^2-3203*g*k^2-2070*h*k^2+1820*i*k^2-1283*j*k^2+587*k^3,
    b*h*j+3332*a*k^2-848*b*k^2+4619*c*k^2+1765*d*k^2-4724*e*k^2-472*f*k^2-3277*g*k^2-4407*h*k^2-2014*i*k^2+3763*j*k^2-1884*k^3,
    a*h*j-1012*a*k^2+4684*b*k^2+3374*c*k^2+2639*d*k^2-396*e*k^2+2887*f*k^2+610*g*k^2+3581*h*k^2-3057*i*k^2-1876*j*k^2+4054*k^3,
    g^2*j-1021*a*k^2+3886*b*k^2-4689*c*k^2+1464*d*k^2-412*e*k^2+792*f*k^2-356*g*k^2+519*h*k^2-2920*i*k^2-4066*j*k^2+3662*k^3,
    f*g*j+3858*a*k^2+3300*b*k^2-363*c*k^2+2989*d*k^2-2575*e*k^2-1602*f*k^2-1609*g*k^2-4229*h*k^2-3658*i*k^2-4851*j*k^2+2499*k^3,
    e*g*j+2294*a*k^2-2418*b*k^2-2704*c*k^2+2843*d*k^2+1995*e*k^2+4344*f*k^2-3744*g*k^2-833*h*k^2+3*i*k^2-3327*j*k^2-3062*k^3,
    d*g*j-2625*a*k^2+4373*b*k^2-2190*c*k^2+4171*d*k^2-1297*e*k^2+888*f*k^2+264*g*k^2-3586*h*k^2+3283*i*k^2-376*j*k^2-3589*k^3,
    c*g*j+1101*a*k^2+423*b*k^2+1095*c*k^2-353*d*k^2-3640*e*k^2+2752*f*k^2+2116*g*k^2+1130*h*k^2-2015*i*k^2+2448*j*k^2-4928*k^3,
    b*g*j+416*a*k^2+3250*b*k^2+2016*c*k^2-600*d*k^2-4638*e*k^2+2454*f*k^2+2211*g*k^2+2501*h*k^2-40*i*k^2+3527*j*k^2-4668*k^3,
    a*g*j-4884*a*k^2+2074*b*k^2+2851*c*k^2-2746*d*k^2+2608*e*k^2+492*f*k^2-795*g*k^2+4049*h*k^2+683*i*k^2-3569*j*k^2-1229*k^3,
    f^2*j-1729*a*k^2-689*b*k^2+2009*c*k^2-1967*d*k^2-579*e*k^2-517*f*k^2-3079*g*k^2-1221*h*k^2-1608*i*k^2-4050*j*k^2+4815*k^3,
    e*f*j-4763*a*k^2-2152*b*k^2-1704*c*k^2+2626*d*k^2-3984*e*k^2+2919*f*k^2-1665*g*k^2+946*h*k^2-4925*i*k^2-4031*j*k^2+3494*k^3,
    d*f*j+123*a*k^2+2023*b*k^2+4559*c*k^2-2080*d*k^2-30*e*k^2+3404*f*k^2+3393*g*k^2-199*h*k^2+4740*i*k^2-1086*j*k^2-537*k^3,
    c*f*j-4164*a*k^2+4926*b*k^2-1248*c*k^2-4291*d*k^2+1147*e*k^2-2209*f*k^2-3240*g*k^2-80*h*k^2+2836*i*k^2+141*j*k^2-3442*k^3,
    b*f*j-2262*a*k^2+1588*b*k^2-4955*c*k^2+2899*d*k^2+1811*e*k^2-800*f*k^2+623*g*k^2-917*h*k^2-128*i*k^2-4859*j*k^2+3649*k^3,
    a*f*j-2330*a*k^2+3175*b*k^2+623*c*k^2+2390*d*k^2-2639*e*k^2-3728*f*k^2-2718*g*k^2-2866*h*k^2+951*i*k^2+243*j*k^2+4278*k^3,
    e^2*j-96*a*k^2+1661*b*k^2-1276*c*k^2-2728*d*k^2+3556*e*k^2+1921*f*k^2-1477*g*k^2+85*h*k^2-3351*i*k^2-4440*j*k^2+151*k^3,
    d*e*j-2658*a*k^2-3903*b*k^2-2133*c*k^2+3629*d*k^2+345*e*k^2+3768*f*k^2-1751*g*k^2+2255*h*k^2-3835*i*k^2-1592*j*k^2+2725*k^3,
    c*e*j-2001*a*k^2+195*b*k^2+3805*c*k^2-3458*d*k^2-1823*e*k^2-4899*f*k^2-3522*g*k^2-4386*h*k^2-30*i*k^2+2637*j*k^2-1686*k^3,
    b*e*j-4116*a*k^2+3268*b*k^2+3399*c*k^2-3111*d*k^2-4036*e*k^2+4319*f*k^2-4219*g*k^2+131*h*k^2+3714*i*k^2+4107*j*k^2-4352*k^3,
    a*e*j-150*a*k^2-1352*b*k^2-2924*c*k^2-3199*d*k^2+607*e*k^2+85*f*k^2+836*g*k^2+2129*h*k^2-380*i*k^2+182*j*k^2+562*k^3,
    d^2*j-2155*a*k^2-2319*b*k^2-3146*c*k^2+4855*d*k^2+3561*e*k^2+1816*f*k^2-2846*g*k^2+4687*h*k^2-1303*i*k^2-3779*j*k^2+487*k^3,
    c*d*j+3961*a*k^2+1507*b*k^2-3087*c*k^2-4003*d*k^2-891*e*k^2+899*f*k^2+979*g*k^2+1204*h*k^2+4928*i*k^2+2411*j*k^2-4483*k^3,
    b*d*j-3837*a*k^2-1269*b*k^2+1938*c*k^2-2461*d*k^2-1492*e*k^2+479*f*k^2-2617*g*k^2-308*h*k^2+4275*i*k^2-4085*j*k^2-556*k^3,
    a*d*j-1159*a*k^2+1143*b*k^2-4761*c*k^2-2156*d*k^2+3007*e*k^2+3336*f*k^2-1199*g*k^2-1432*h*k^2+2661*i*k^2-1468*j*k^2+3871*k^3,
    c^2*j+4251*a*k^2-2310*b*k^2+3931*c*k^2+1651*d*k^2+2519*e*k^2+410*f*k^2-1202*g*k^2-4055*h*k^2+3723*i*k^2+2729*j*k^2+4880*k^3,
    b*c*j+4502*a*k^2-2732*b*k^2+3297*c*k^2-126*d*k^2+1707*e*k^2+1185*f*k^2-4984*g*k^2-1393*h*k^2+4181*i*k^2-4106*j*k^2-3005*k^3,
    a*c*j+1706*a*k^2+2497*b*k^2+3768*c*k^2-4825*d*k^2+2518*e*k^2+563*f*k^2+1918*g*k^2+4538*h*k^2+1382*i*k^2-3523*j*k^2+4334*k^3,
    b^2*j-363*a*k^2-3837*b*k^2-4769*c*k^2+3194*d*k^2-2597*e*k^2+1214*f*k^2+1582*g*k^2-2256*h*k^2+3675*i*k^2+3494*j*k^2+2681*k^3,
    a*b*j-476*a*k^2-4187*b*k^2-1536*c*k^2-4736*d*k^2+4434*e*k^2-3138*f*k^2+2676*g*k^2+619*h*k^2+3112*i*k^2+696*j*k^2-999*k^3,
    a^2*j+4526*a*k^2+3485*b*k^2-2802*c*k^2+3889*d*k^2+3237*e*k^2+4905*f*k^2-1164*g*k^2+4519*h*k^2-4891*i*k^2-2635*j*k^2+4541*k^3,
    i^3-3744*a*k^2+1673*b*k^2+2638*c*k^2+1619*d*k^2+3484*e*k^2+3360*f*k^2-2567*g*k^2+3382*h*k^2+84*i*k^2+1145*j*k^2-1294*k^3,
    h*i^2-1152*a*k^2+4056*b*k^2+1486*c*k^2-3852*d*k^2-1990*e*k^2-2198*f*k^2-1057*g*k^2+349*h*k^2+4536*i*k^2-96*j*k^2+2259*k^3,
    g*i^2+1344*a*k^2-4095*b*k^2-3614*c*k^2-4687*d*k^2-582*e*k^2-2750*f*k^2-1132*g*k^2+3305*h*k^2+4981*i*k^2+3899*j*k^2-1473*k^3,
    f*i^2+1475*a*k^2+3143*b*k^2-681*c*k^2+145*d*k^2-3467*e*k^2-2039*f*k^2+4993*g*k^2+3765*h*k^2-3726*i*k^2-102*j*k^2-242*k^3,
    e*i^2+2193*a*k^2-1697*b*k^2-4720*c*k^2+4235*d*k^2+1813*e*k^2-2238*f*k^2+1560*g*k^2+4064*h*k^2+4214*i*k^2+556*j*k^2+4017*k^3,
    d*i^2-662*a*k^2+3665*b*k^2+219*c*k^2+4861*d*k^2+3708*e*k^2+4329*f*k^2-4301*g*k^2-390*h*k^2-2524*i*k^2-4586*j*k^2+4317*k^3,
    c*i^2+1438*a*k^2+2547*b*k^2-2310*c*k^2+3716*d*k^2+2692*e*k^2+911*f*k^2-4361*g*k^2+3732*h*k^2-324*i*k^2+1264*j*k^2+1507*k^3,
    b*i^2-2567*a*k^2-3581*b*k^2+4734*c*k^2+4134*d*k^2+4381*e*k^2+252*f*k^2+4682*g*k^2+4044*h*k^2+3061*i*k^2-2923*j*k^2+2672*k^3,
    a*i^2+971*a*k^2+2480*b*k^2-3187*c*k^2-3293*d*k^2+2265*e*k^2-2628*f*k^2-1144*g*k^2-3141*h*k^2+2643*i*k^2-2360*j*k^2+4224*k^3,
    h^2*i+4797*a*k^2+3148*b*k^2+2195*c*k^2-2621*d*k^2+2768*e*k^2-4141*f*k^2+4040*g*k^2-796*h*k^2+2686*i*k^2-1970*j*k^2-3173*k^3,
    g*h*i+4495*a*k^2+4396*b*k^2-2444*c*k^2-4495*d*k^2+2097*e*k^2+74*f*k^2-4495*g*k^2-4365*h*k^2-1754*i*k^2-3560*j*k^2-2886*k^3,
    f*h*i-4206*a*k^2-1790*b*k^2-967*c*k^2+954*d*k^2-4031*e*k^2+2458*f*k^2-562*g*k^2-2467*h*k^2+4282*i*k^2-4291*j*k^2-4736*k^3,
    e*h*i+2412*a*k^2-923*b*k^2+4659*c*k^2-3213*d*k^2-3818*e*k^2-3619*f*k^2+3299*g*k^2-333*h*k^2-1670*i*k^2+4078*j*k^2+1405*k^3,
    d*h*i+2372*a*k^2+2279*b*k^2+1641*c*k^2+2461*d*k^2-2407*e*k^2+4412*f*k^2+722*g*k^2-756*h*k^2+2447*i*k^2+1564*j*k^2+1998*k^3,
    c*h*i-1561*a*k^2+370*b*k^2+2614*c*k^2+107*d*k^2+1317*e*k^2-4495*f*k^2+300*g*k^2+4741*h*k^2-3917*i*k^2-1520*j*k^2+4584*k^3,
    b*h*i+4986*a*k^2+1466*b*k^2-3946*c*k^2-3289*d*k^2-3886*e*k^2-2087*f*k^2-1503*g*k^2+3740*h*k^2+138*i*k^2+1285*j*k^2+4434*k^3,
    a*h*i-766*a*k^2-350*b*k^2+3560*c*k^2-585*d*k^2-3824*e*k^2-1961*f*k^2-731*g*k^2-1954*h*k^2-3046*i*k^2+3051*j*k^2-3280*k^3,
    g^2*i-3800*a*k^2-1910*b*k^2+2922*c*k^2+2565*d*k^2-4112*e*k^2+2021*f*k^2+694*g*k^2-1569*h*k^2+1101*i*k^2-3314*j*k^2+1086*k^3,
    f*g*i+3703*a*k^2-3692*b*k^2+1192*c*k^2-3879*d*k^2+4990*e*k^2-4892*f*k^2-1817*g*k^2+3397*h*k^2+430*i*k^2-2256*j*k^2-3739*k^3,
    e*g*i-4641*a*k^2-247*b*k^2+4877*c*k^2+942*d*k^2+101*e*k^2-4644*f*k^2+625*g*k^2+3696*h*k^2+705*i*k^2+3144*j*k^2+4100*k^3,
    d*g*i+2287*a*k^2+4260*b*k^2-936*c*k^2-2135*d*k^2+382*e*k^2+129*f*k^2+1135*g*k^2-3157*h*k^2+276*i*k^2+3362*j*k^2+2393*k^3,
    c*g*i-1360*a*k^2+1558*b*k^2+3233*c*k^2+1399*d*k^2+426*e*k^2+927*f*k^2-4863*g*k^2-2775*h*k^2-2703*i*k^2+4826*j*k^2+3603*k^3,
    b*g*i-1122*a*k^2+4678*b*k^2-1860*c*k^2-3569*d*k^2-2104*e*k^2-2846*f*k^2-200*g*k^2-2081*h*k^2+2132*i*k^2+2530*j*k^2-1467*k^3,
    a*g*i-1324*a*k^2-21*b*k^2-2475*c*k^2+810*d*k^2-3238*e*k^2-794*f*k^2+2175*g*k^2-2721*h*k^2-1267*i*k^2+2288*j*k^2+3123*k^3,
    f^2*i+1936*a*k^2+3000*b*k^2+3867*c*k^2+2107*d*k^2+2947*e*k^2-2745*f*k^2+17*g*k^2-4119*h*k^2-3693*i*k^2+3377*j*k^2-2852*k^3,
    e*f*i+4378*a*k^2+2832*b*k^2+1762*c*k^2+2272*d*k^2+2406*e*k^2-3436*f*k^2+2536*g*k^2-734*h*k^2+1833*i*k^2-3592*j*k^2-1795*k^3,
    d*f*i-1950*a*k^2+4018*b*k^2-924*c*k^2-4342*d*k^2-1429*e*k^2-980*f*k^2+2864*g*k^2-529*h*k^2-3158*i*k^2+3053*j*k^2+2039*k^3,
    c*f*i-2326*a*k^2-3205*b*k^2+1169*c*k^2+2232*d*k^2+1834*e*k^2+3568*f*k^2-1029*g*k^2-4358*h*k^2-434*i*k^2+1057*j*k^2+4867*k^3,
    b*f*i-4417*a*k^2-2437*b*k^2+3642*c*k^2+3625*d*k^2-4085*e*k^2+2177*f*k^2+2618*g*k^2+1648*h*k^2+4111*i*k^2+4600*j*k^2+1780*k^3,
    a*f*i+2320*a*k^2-2761*b*k^2+324*c*k^2-2175*d*k^2+11*e*k^2+2188*f*k^2-980*g*k^2+1211*h*k^2-298*i*k^2-172*j*k^2+1800*k^3,
    e^2*i+54*a*k^2+1714*b*k^2+1136*c*k^2+384*d*k^2-869*e*k^2+485*f*k^2-567*g*k^2-825*h*k^2-2896*i*k^2+2112*j*k^2-1175*k^3,
    d*e*i-1858*a*k^2+2997*b*k^2+3829*c*k^2+3522*d*k^2+4940*e*k^2-4174*f*k^2-4120*g*k^2-1949*h*k^2-3492*i*k^2+2476*j*k^2-1840*k^3,
    c*e*i+117*a*k^2-2613*b*k^2-4261*c*k^2-2963*d*k^2-2418*e*k^2-1429*f*k^2-1741*g*k^2-4095*h*k^2-328*i*k^2+1173*j*k^2-3275*k^3,
    b*e*i+610*a*k^2-4271*b*k^2-696*c*k^2-921*d*k^2-3290*e*k^2-1580*f*k^2+4882*g*k^2+4695*h*k^2-2189*i*k^2+1028*j*k^2-4406*k^3,
    a*e*i-3216*a*k^2+283*b*k^2+247*c*k^2+4933*d*k^2+301*e*k^2+3048*f*k^2-165*g*k^2-3910*h*k^2+2538*i*k^2+4854*j*k^2-1255*k^3,
    d^2*i+2920*a*k^2+1430*b*k^2+521*c*k^2+1697*d*k^2-2318*e*k^2+1023*f*k^2-1036*g*k^2-1762*h*k^2-2086*i*k^2+197*j*k^2+4310*k^3,
    c*d*i+1836*a*k^2-1067*b*k^2-4546*c*k^2+4667*d*k^2+916*e*k^2+3202*f*k^2+1999*g*k^2+305*h*k^2-2403*i*k^2+270*j*k^2+441*k^3,
    b*d*i+3995*a*k^2-4942*b*k^2+1465*c*k^2+4138*d*k^2+2591*e*k^2-4224*f*k^2+3121*g*k^2+3611*h*k^2-324*i*k^2+1155*j*k^2+1295*k^3,
    a*d*i+474*a*k^2-2525*b*k^2-1630*c*k^2+1193*d*k^2+1964*e*k^2-727*f*k^2-289*g*k^2+3756*h*k^2+1375*i*k^2-1196*j*k^2-1096*k^3,
    c^2*i+45*a*k^2+225*b*k^2-1546*c*k^2+1492*d*k^2+3056*e*k^2-1969*f*k^2-3211*g*k^2-2342*h*k^2+4215*i*k^2-2899*j*k^2-2340*k^3,
    b*c*i-3665*a*k^2+2784*b*k^2+4274*c*k^2+2226*d*k^2+426*e*k^2-185*f*k^2-2295*g*k^2+4348*h*k^2+689*i*k^2+4815*j*k^2-100*k^3,
    a*c*i+4734*a*k^2+3052*b*k^2-4171*c*k^2+3429*d*k^2-470*e*k^2-388*f*k^2+602*g*k^2+568*h*k^2-3353*i*k^2+2027*j*k^2+2912*k^3,
    b^2*i+2916*a*k^2-3833*b*k^2-1057*c*k^2+4269*d*k^2+2176*e*k^2+1780*f*k^2+4793*g*k^2-1197*h*k^2-3654*i*k^2+2453*j*k^2-1303*k^3,
    a*b*i+3856*a*k^2+1364*b*k^2+4264*c*k^2-4027*d*k^2-756*e*k^2+1350*f*k^2+2293*g*k^2-4937*h*k^2-3458*i*k^2-905*j*k^2-3183*k^3,
    a^2*i-384*a*k^2-2025*b*k^2+166*c*k^2-2499*d*k^2-3084*e*k^2+1293*f*k^2+3220*g*k^2+2568*h*k^2-493*i*k^2+4651*j*k^2+3945*k^3,
    h^3+1674*a*k^2+895*b*k^2+392*c*k^2+1468*d*k^2-2202*e*k^2-2228*f*k^2-2655*g*k^2-1893*h*k^2-4366*i*k^2-205*j*k^2+4143*k^3,
    g*h^2+1962*a*k^2+1601*b*k^2-4357*c*k^2-618*d*k^2+386*e*k^2+4724*f*k^2+3952*g*k^2+1261*h*k^2+2156*i*k^2+3107*j*k^2+2951*k^3,
    f*h^2-1041*a*k^2-1451*b*k^2-1376*c*k^2+1412*d*k^2+3183*e*k^2-3123*f*k^2+3599*g*k^2-806*h*k^2+388*i*k^2-2342*j*k^2+4722*k^3,
    e*h^2-4327*a*k^2-1704*b*k^2-4794*c*k^2+1724*d*k^2+924*e*k^2+1709*f*k^2+4229*g*k^2-707*h*k^2-2118*i*k^2+4978*j*k^2+3704*k^3,
    d*h^2+2614*a*k^2-2643*b*k^2+486*c*k^2+1015*d*k^2+261*e*k^2+286*f*k^2+3536*g*k^2-618*h*k^2+4914*i*k^2-36*j*k^2-1636*k^3,
    c*h^2-406*a*k^2-2006*b*k^2-2783*c*k^2-2524*d*k^2+896*e*k^2-2327*f*k^2+4556*g*k^2-4282*h*k^2+3134*i*k^2+3736*j*k^2+478*k^3,
    b*h^2-3084*a*k^2-996*b*k^2-1716*c*k^2+2808*d*k^2-2404*e*k^2+2132*f*k^2+20*g*k^2+4964*h*k^2+1825*i*k^2+1532*j*k^2-642*k^3,
    a*h^2-3482*a*k^2+1409*b*k^2-3513*c*k^2+3035*d*k^2-364*e*k^2+1888*f*k^2-634*g*k^2+1481*h*k^2-3619*i*k^2-4211*j*k^2+2496*k^3,
    g^2*h-662*a*k^2+4458*b*k^2-3365*c*k^2-2722*d*k^2-2517*e*k^2+3377*f*k^2-2115*g*k^2+4089*h*k^2-1737*i*k^2-2821*j*k^2+3878*k^3,
    f*g*h+250*a*k^2-3954*b*k^2-1962*c*k^2-3420*d*k^2+465*e*k^2+787*f*k^2+135*g*k^2-3391*h*k^2+4188*i*k^2-861*j*k^2-1322*k^3,
    e*g*h-323*a*k^2+1154*b*k^2-408*c*k^2-3070*d*k^2+3028*e*k^2-386*f*k^2-2515*g*k^2-881*h*k^2-695*i*k^2+4869*j*k^2+510*k^3,
    d*g*h+4044*a*k^2+4031*b*k^2-4141*c*k^2-2981*d*k^2+3673*e*k^2+2819*f*k^2+425*g*k^2-572*h*k^2+4171*i*k^2+2753*j*k^2-2237*k^3,
    c*g*h+2159*a*k^2+1465*b*k^2+2761*c*k^2+574*d*k^2+1645*e*k^2-263*f*k^2+3610*g*k^2-110*h*k^2+3127*i*k^2-1948*j*k^2-722*k^3,
    b*g*h+4157*a*k^2-3085*b*k^2-3266*c*k^2+1816*d*k^2+3149*e*k^2-1370*f*k^2+2425*g*k^2+951*h*k^2-1062*i*k^2-58*j*k^2+1807*k^3,
    a*g*h-3957*a*k^2+2821*b*k^2+339*c*k^2-3796*d*k^2+573*e*k^2+768*f*k^2+1632*g*k^2+1612*h*k^2+1039*i*k^2+4072*j*k^2+1605*k^3,
    f^2*h+1703*a*k^2+2224*b*k^2+728*c*k^2-744*d*k^2+4908*e*k^2-144*f*k^2+4456*g*k^2-2095*h*k^2+2920*i*k^2+1227*j*k^2-2529*k^3,
    e*f*h+2826*a*k^2+357*b*k^2-2376*c*k^2+2245*d*k^2-1143*e*k^2-1230*f*k^2+3631*g*k^2+3448*h*k^2-1698*i*k^2+177*j*k^2+3914*k^3,
    d*f*h-497*a*k^2-1278*b*k^2-3387*c*k^2-3939*d*k^2+71*e*k^2-2486*f*k^2-1258*g*k^2-4798*h*k^2-3480*i*k^2-3795*j*k^2+2752*k^3,
    c*f*h+4723*a*k^2-4*b*k^2-3591*c*k^2-4497*d*k^2-4873*e*k^2+86*f*k^2-3080*g*k^2-4453*h*k^2-4490*i*k^2+4712*j*k^2+4102*k^3,
    b*f*h-3183*a*k^2-107*b*k^2-1525*c*k^2-809*d*k^2-3*e*k^2+3035*f*k^2+511*g*k^2-4092*h*k^2+1414*i*k^2+4778*j*k^2+3790*k^3,
    a*f*h+4390*a*k^2+3291*b*k^2-2026*c*k^2+4529*d*k^2-2291*e*k^2-41*f*k^2-3770*g*k^2-2325*h*k^2+788*i*k^2+4271*j*k^2-2962*k^3,
    e^2*h-3242*a*k^2+461*b*k^2-4412*c*k^2-4987*d*k^2+4287*e*k^2+1054*f*k^2-1873*g*k^2-1272*h*k^2-3269*i*k^2-2053*j*k^2-3024*k^3,
    d*e*h+4614*a*k^2+2853*b*k^2+2190*c*k^2-2546*d*k^2+4187*e*k^2-450*f*k^2-4947*g*k^2+4359*h*k^2-1956*i*k^2-4644*j*k^2+991*k^3,
    c*e*h-4885*a*k^2-4972*b*k^2+3246*c*k^2-2685*d*k^2-783*e*k^2+224*f*k^2-1248*g*k^2-4794*h*k^2+4251*i*k^2-1601*j*k^2-4942*k^3,
    b*e*h-4679*a*k^2-3102*b*k^2+3055*c*k^2-1957*d*k^2+1402*e*k^2+647*f*k^2-2865*g*k^2+974*h*k^2-685*i*k^2-4908*j*k^2-3552*k^3,
    a*e*h-1876*a*k^2-2551*b*k^2+2768*c*k^2+867*d*k^2-1636*e*k^2+2797*f*k^2-2290*g*k^2-3023*h*k^2+1392*i*k^2+4357*j*k^2-698*k^3,
    d^2*h+115*a*k^2+453*b*k^2-1155*c*k^2-37*d*k^2+3503*e*k^2+2405*f*k^2+138*g*k^2+1031*h*k^2-112*i*k^2-1310*j*k^2-2790*k^3,
    c*d*h-4309*a*k^2+667*b*k^2+1066*c*k^2+4227*d*k^2+1416*e*k^2-836*f*k^2-3680*g*k^2-4360*h*k^2+4292*i*k^2+1259*j*k^2+2947*k^3,
    b*d*h+1015*a*k^2+1541*b*k^2-28*c*k^2+2227*d*k^2+2162*e*k^2+4348*f*k^2+3499*g*k^2-326*h*k^2+438*i*k^2-830*j*k^2+58*k^3,
    a*d*h+3317*a*k^2+1097*b*k^2-1048*c*k^2+2640*d*k^2-772*e*k^2-635*f*k^2+4097*g*k^2-1284*h*k^2+2717*i*k^2-494*j*k^2-919*k^3,
    c^2*h+176*a*k^2-765*b*k^2-2369*c*k^2-3248*d*k^2+3449*e*k^2+73*f*k^2-446*g*k^2+3362*h*k^2+4515*i*k^2-4587*j*k^2+2616*k^3,
    b*c*h-4766*a*k^2-1784*b*k^2-3049*c*k^2-4156*d*k^2-156*e*k^2+4766*f*k^2-4927*g*k^2+3039*h*k^2-1760*i*k^2+1184*j*k^2+4562*k^3,
    a*c*h+1831*a*k^2+3025*b*k^2-1617*c*k^2+4550*d*k^2+497*e*k^2-1320*f*k^2+4423*g*k^2+2043*h*k^2+4271*i*k^2-4935*j*k^2-1393*k^3,
    b^2*h-93*a*k^2+2046*b*k^2+4757*c*k^2-77*d*k^2-1281*e*k^2-3514*f*k^2+619*g*k^2+1299*h*k^2+2535*i*k^2-3314*j*k^2-4812*k^3,
    a*b*h+3209*a*k^2-2820*b*k^2-4316*c*k^2+3224*d*k^2+2149*e*k^2+3761*f*k^2-361*g*k^2-1188*h*k^2-2519*i*k^2-4516*j*k^2-182*k^3,
    a^2*h-2828*a*k^2+2415*b*k^2-1547*c*k^2-4385*d*k^2-2327*e*k^2-1590*f*k^2-2927*g*k^2-4149*h*k^2+3486*i*k^2-1073*j*k^2-3502*k^3,
    g^3+3454*a*k^2-112*b*k^2+2204*c*k^2+2102*d*k^2+56*e*k^2-4395*f*k^2-1331*g*k^2+2732*h*k^2-2205*i*k^2+2808*j*k^2-3880*k^3,
    f*g^2+4629*a*k^2-2639*b*k^2-2414*c*k^2-2500*d*k^2-1662*e*k^2-2829*f*k^2+4131*g*k^2-3992*h*k^2+4185*i*k^2-660*j*k^2+3687*k^3,
    e*g^2+2995*a*k^2+3513*b*k^2-3105*c*k^2-208*d*k^2-1529*e*k^2-4667*f*k^2-120*g*k^2-2282*h*k^2+1286*i*k^2-4888*j*k^2+3629*k^3,
    d*g^2-4700*a*k^2+4452*b*k^2-2265*c*k^2+3055*d*k^2-4581*e*k^2-3833*f*k^2+1194*g*k^2-296*h*k^2+2874*i*k^2+876*j*k^2-3563*k^3,
    c*g^2-1099*a*k^2-1641*b*k^2-713*c*k^2+1069*d*k^2+4592*e*k^2+1890*f*k^2-534*g*k^2-4129*h*k^2-3047*i*k^2-3452*j*k^2+575*k^3,
    b*g^2+1383*a*k^2-3521*b*k^2-4779*c*k^2-4521*d*k^2-1287*e*k^2+2033*f*k^2-3815*g*k^2+3899*h*k^2-2067*i*k^2+966*j*k^2+289*k^3,
    a*g^2+3633*a*k^2-2595*b*k^2+3222*c*k^2+2549*d*k^2-1285*e*k^2+4237*f*k^2+4555*g*k^2-4086*h*k^2-3885*i*k^2-1811*j*k^2+2105*k^3,
    f^2*g-4506*a*k^2+2050*b*k^2+371*c*k^2-1859*d*k^2-2422*e*k^2-4752*f*k^2-726*g*k^2+2437*h*k^2-870*i*k^2+4852*j*k^2-2278*k^3,
    e*f*g-1097*a*k^2-3272*b*k^2-1002*c*k^2+3752*d*k^2+3033*e*k^2-4785*f*k^2+4826*g*k^2-3555*h*k^2-997*i*k^2-3333*j*k^2-4507*k^3,
    d*f*g-1232*a*k^2-1428*b*k^2-2164*c*k^2-267*d*k^2+1193*e*k^2+1253*f*k^2-3005*g*k^2+3566*h*k^2+1131*i*k^2+2828*j*k^2+1724*k^3,
    c*f*g-2957*a*k^2-705*b*k^2+4189*c*k^2+3350*d*k^2-3385*e*k^2+2533*f*k^2+2534*g*k^2+1656*h*k^2+2226*i*k^2+2186*j*k^2+1400*k^3,
    b*f*g-4373*a*k^2+3407*b*k^2-1232*c*k^2-1465*d*k^2-4833*e*k^2-2784*f*k^2+3509*g*k^2-4685*h*k^2+254*i*k^2-1881*j*k^2-4205*k^3,
    a*f*g-1525*a*k^2-2843*b*k^2-3215*c*k^2-5003*d*k^2+2320*e*k^2+2864*f*k^2+2964*g*k^2-4932*h*k^2-4514*i*k^2-4299*j*k^2-1112*k^3,
    e^2*g-2841*a*k^2+2864*b*k^2-2173*c*k^2-3484*d*k^2-4223*e*k^2-1593*f*k^2-2691*g*k^2+2028*h*k^2-3647*i*k^2+3905*j*k^2+1853*k^3,
    d*e*g-2930*a*k^2+1458*b*k^2+255*c*k^2+1753*d*k^2-183*e*k^2+22*f*k^2-204*g*k^2-4423*h*k^2-1819*i*k^2-137*j*k^2+4851*k^3,
    c*e*g+757*a*k^2-1889*b*k^2+3632*c*k^2-3895*d*k^2-4731*e*k^2+3739*f*k^2-2997*g*k^2-1954*h*k^2+1454*i*k^2+739*j*k^2+528*k^3,
    b*e*g+2003*a*k^2+2604*b*k^2+646*c*k^2-4935*d*k^2+2258*e*k^2+1108*f*k^2+4625*g*k^2-1104*h*k^2-3976*i*k^2+4858*j*k^2+4314*k^3,
    a*e*g-1329*a*k^2-1754*b*k^2-30*c*k^2+2066*d*k^2-2363*e*k^2-4713*f*k^2+1656*g*k^2+3220*h*k^2+1183*i*k^2+2547*j*k^2+3432*k^3,
    d^2*g+2043*a*k^2-2149*b*k^2-1323*c*k^2-3709*d*k^2+931*e*k^2-4439*f*k^2-3416*g*k^2-4966*h*k^2+1845*i*k^2-3252*j*k^2-2976*k^3,
    c*d*g-2571*a*k^2+4426*b*k^2-821*c*k^2-382*d*k^2+2632*e*k^2+2847*f*k^2-3229*g*k^2-960*h*k^2-2792*i*k^2+2596*j*k^2+4207*k^3,
    b*d*g-3223*a*k^2-882*b*k^2-3067*c*k^2-4560*d*k^2-4114*e*k^2-4166*f*k^2-1993*g*k^2+2895*h*k^2-1702*i*k^2-4511*j*k^2+4606*k^3,
    a*d*g+1903*a*k^2+1551*b*k^2+2608*c*k^2-801*d*k^2-2351*e*k^2+3216*f*k^2-4588*g*k^2+2138*h*k^2-3338*i*k^2+4472*j*k^2+4045*k^3,
    c^2*g+477*a*k^2-4027*b*k^2+4436*c*k^2-3024*d*k^2-3880*e*k^2-492*f*k^2+2492*g*k^2+1894*h*k^2-3598*i*k^2+4744*j*k^2+3274*k^3,
    b*c*g+1005*a*k^2-3895*b*k^2-256*c*k^2+2706*d*k^2-3169*e*k^2+1101*f*k^2+105*g*k^2-1896*h*k^2-1432*i*k^2+1518*j*k^2-290*k^3,
    a*c*g+4995*a*k^2-4038*b*k^2+1683*c*k^2+1426*d*k^2-4269*e*k^2-650*f*k^2-3823*g*k^2-4730*h*k^2-3292*i*k^2+2970*j*k^2-3081*k^3,
    b^2*g+1951*a*k^2-4252*b*k^2-4751*c*k^2+3460*d*k^2-2203*e*k^2+36*f*k^2+2757*g*k^2-991*h*k^2-4741*i*k^2+2436*j*k^2-2838*k^3,
    a*b*g-1677*a*k^2-3237*b*k^2+3715*c*k^2+310*d*k^2-4875*e*k^2-122*f*k^2+1177*g*k^2-4286*h*k^2-4350*i*k^2-3846*j*k^2-2719*k^3,
    a^2*g-1759*a*k^2+4387*b*k^2-2781*c*k^2+2883*d*k^2-4087*e*k^2+855*f*k^2-2371*g*k^2+999*h*k^2-3144*i*k^2+4683*j*k^2-3851*k^3,
    f^3-4672*a*k^2+2492*b*k^2-2588*c*k^2+1173*d*k^2-1511*e*k^2-605*f*k^2-2723*g*k^2-1746*h*k^2-2689*i*k^2+3700*j*k^2+946*k^3,
    e*f^2+901*a*k^2-460*b*k^2-4644*c*k^2-1009*d*k^2+1254*e*k^2+2885*f*k^2+2172*g*k^2+4043*h*k^2+1108*i*k^2-2599*j*k^2+24*k^3,
    d*f^2+4700*a*k^2-2231*b*k^2-4771*c*k^2-1396*d*k^2+4587*e*k^2-1308*f*k^2-3738*g*k^2-1088*h*k^2+2327*i*k^2-3286*j*k^2-1496*k^3,
    c*f^2-3308*a*k^2-3113*b*k^2+1272*c*k^2-1907*d*k^2+3184*e*k^2+2954*f*k^2+695*g*k^2+2620*h*k^2-2002*i*k^2-4049*j*k^2+800*k^3,
    b*f^2-4677*a*k^2+1140*b*k^2+956*c*k^2+692*d*k^2+2598*e*k^2-1357*f*k^2+3235*g*k^2+4072*h*k^2+1746*i*k^2-812*j*k^2-4695*k^3,
    a*f^2+771*a*k^2+1570*b*k^2-1920*c*k^2+4873*d*k^2-185*e*k^2+659*f*k^2-4598*g*k^2+2554*h*k^2+3097*i*k^2-3224*j*k^2-4429*k^3,
    e^2*f+2526*a*k^2+2696*b*k^2-4386*c*k^2-4098*d*k^2+2415*e*k^2-1859*f*k^2+1265*g*k^2-2113*h*k^2-2629*i*k^2-3229*j*k^2+2436*k^3,
    d*e*f-2999*a*k^2-4740*b*k^2-1877*c*k^2+1616*d*k^2-4128*e*k^2-4179*f*k^2+2433*g*k^2-3542*h*k^2-55*i*k^2-3528*j*k^2-604*k^3,
    c*e*f+4811*a*k^2+2444*b*k^2+3911*c*k^2+2543*d*k^2+1009*e*k^2+930*f*k^2-3897*g*k^2+546*h*k^2-2336*i*k^2-1674*j*k^2+1516*k^3,
    b*e*f+1621*a*k^2+1352*b*k^2-4321*c*k^2+4176*d*k^2+3702*e*k^2-1541*f*k^2+1175*g*k^2+1126*h*k^2-3234*i*k^2-104*j*k^2-647*k^3,
    a*e*f+4354*a*k^2-2166*b*k^2+4231*c*k^2+2968*d*k^2+1949*e*k^2-2937*f*k^2+4539*g*k^2+2064*h*k^2-981*i*k^2-896*j*k^2-4934*k^3,
    d^2*f-3920*a*k^2+2546*b*k^2-2379*c*k^2-2730*d*k^2-3945*e*k^2-1479*f*k^2-6*g*k^2+1230*h*k^2+3261*i*k^2+2136*j*k^2+2830*k^3,
    c*d*f-2887*a*k^2-3708*b*k^2-3602*c*k^2-2312*d*k^2-3888*e*k^2+3775*f*k^2-3634*g*k^2-2381*h*k^2+4858*i*k^2-3773*j*k^2+1385*k^3,
    b*d*f-2025*a*k^2-1980*b*k^2+2759*c*k^2+1801*d*k^2+134*e*k^2-3976*f*k^2-3716*g*k^2-2688*h*k^2-1409*i*k^2-4532*j*k^2+4349*k^3,
    a*d*f+4606*a*k^2-3026*b*k^2+2417*c*k^2-1504*d*k^2+742*e*k^2-3755*f*k^2-1482*g*k^2+1781*h*k^2-3602*i*k^2-888*j*k^2+3033*k^3,
    c^2*f-4233*a*k^2+14*b*k^2+3168*c*k^2+3555*d*k^2+2515*e*k^2-2899*f*k^2+733*g*k^2+1373*h*k^2+2579*i*k^2+2627*j*k^2-2823*k^3,
    b*c*f+3671*a*k^2+367*b*k^2-4739*c*k^2-4859*d*k^2-777*e*k^2+4930*f*k^2-4920*g*k^2-1397*h*k^2-3211*i*k^2-3245*j*k^2-3549*k^3,
    a*c*f-3725*a*k^2-2590*b*k^2+4610*c*k^2-4955*d*k^2+4194*e*k^2+891*f*k^2+1067*g*k^2-2272*h*k^2+463*i*k^2+1136*j*k^2-4888*k^3,
    b^2*f-1391*a*k^2+3288*b*k^2-1816*c*k^2+1441*d*k^2-1994*e*k^2+3613*f*k^2+1450*g*k^2-266*h*k^2+3426*i*k^2-4197*j*k^2-3416*k^3,
    a*b*f+1893*a*k^2+2234*b*k^2-3233*c*k^2-227*d*k^2+1034*e*k^2-3669*f*k^2+3352*g*k^2-4524*h*k^2+3000*i*k^2+608*j*k^2-921*k^3,
    a^2*f-3429*a*k^2+1678*b*k^2-3307*c*k^2-2291*d*k^2+848*e*k^2+1489*f*k^2+662*g*k^2+4831*h*k^2-1269*i*k^2-4462*j*k^2+3105*k^3,
    e^3-3297*a*k^2-1158*b*k^2+3307*c*k^2-3880*d*k^2-2628*e*k^2+2738*f*k^2+949*g*k^2+1960*h*k^2+4736*i*k^2+2491*j*k^2-2876*k^3,
    d*e^2-1644*a*k^2-1506*b*k^2-1956*c*k^2+3329*d*k^2+1495*e*k^2+3255*f*k^2+1335*g*k^2+1247*h*k^2-1114*i*k^2-3016*j*k^2-388*k^3,
    c*e^2-103*a*k^2+2002*b*k^2+1933*c*k^2+3242*d*k^2-890*e*k^2+2312*f*k^2+114*g*k^2-1395*h*k^2+3128*i*k^2-1730*j*k^2+1349*k^3,
    b*e^2-4150*a*k^2-2099*b*k^2-3993*c*k^2+175*d*k^2-3629*e*k^2+2149*f*k^2-1468*g*k^2-3456*h*k^2+4507*i*k^2+1313*j*k^2+454*k^3,
    a*e^2+107*a*k^2+2045*b*k^2-3715*c*k^2+826*d*k^2+4861*e*k^2-897*f*k^2+4883*g*k^2+3960*h*k^2-3760*i*k^2+2248*j*k^2-3061*k^3,
    d^2*e-1875*a*k^2+1772*b*k^2+1075*c*k^2-4378*d*k^2+4800*e*k^2+539*f*k^2+2249*g*k^2+1463*h*k^2-889*i*k^2+28*j*k^2+4195*k^3,
    c*d*e-4497*a*k^2+3781*b*k^2+4534*c*k^2+3749*d*k^2-4200*e*k^2+303*f*k^2-4454*g*k^2+2814*h*k^2-3825*i*k^2+3577*j*k^2-1048*k^3,
    b*d*e-4819*a*k^2+3989*b*k^2-470*c*k^2+2236*d*k^2+70*e*k^2-2288*f*k^2-1374*g*k^2+1605*h*k^2-808*i*k^2+876*j*k^2+1289*k^3,
    a*d*e+463*a*k^2-3310*b*k^2+2582*c*k^2-2868*d*k^2-3831*e*k^2-1720*f*k^2-3321*g*k^2-600*h*k^2-1798*i*k^2-2736*j*k^2-2791*k^3,
    c^2*e+1997*a*k^2-4412*b*k^2-4504*c*k^2+4191*d*k^2+2566*e*k^2-681*f*k^2+1025*g*k^2+4903*h*k^2+1376*i*k^2+2581*j*k^2+3777*k^3,
    b*c*e+2103*a*k^2+4184*b*k^2+3408*c*k^2-223*d*k^2+802*e*k^2+4749*f*k^2-941*g*k^2-4959*h*k^2-1472*i*k^2+4700*j*k^2-2983*k^3,
    a*c*e+3723*a*k^2-323*b*k^2-3773*c*k^2+179*d*k^2+768*e*k^2-2798*f*k^2+3686*g*k^2+1716*h*k^2-3606*i*k^2-315*j*k^2+4119*k^3,
    b^2*e+2177*a*k^2-4281*b*k^2-3107*c*k^2+2169*d*k^2-3045*e*k^2+3667*f*k^2-3165*g*k^2+660*h*k^2+2709*i*k^2-2021*j*k^2+1555*k^3,
    a*b*e-4965*a*k^2-3805*b*k^2-4664*c*k^2+4284*d*k^2+1001*e*k^2-4851*f*k^2+3784*g*k^2+175*h*k^2+3339*i*k^2+4085*j*k^2-2809*k^3,
    a^2*e-2472*a*k^2+1965*b*k^2+2930*c*k^2+1136*d*k^2-2961*e*k^2-3634*f*k^2+4782*g*k^2-2302*h*k^2-4580*i*k^2-936*j*k^2-919*k^3,
    d^3+3921*a*k^2+1644*b*k^2+2900*c*k^2+4805*d*k^2+2791*e*k^2+1650*f*k^2+2944*g*k^2-3451*h*k^2+3524*i*k^2+2886*j*k^2-2899*k^3,
    c*d^2+2651*a*k^2+3076*b*k^2+2934*c*k^2-1563*d*k^2+355*e*k^2-1488*f*k^2+2742*g*k^2-2402*h*k^2+4474*i*k^2+4257*j*k^2-3132*k^3,
    b*d^2-1187*a*k^2-2411*b*k^2+2785*c*k^2+4945*d*k^2+1999*e*k^2-3334*f*k^2-1492*g*k^2+3879*h*k^2-2853*i*k^2-820*j*k^2+1735*k^3,
    a*d^2+1195*a*k^2+2412*b*k^2-2426*c*k^2-4395*d*k^2+2394*e*k^2-1700*f*k^2+4096*g*k^2+829*h*k^2-1938*i*k^2+2643*j*k^2+1479*k^3,
    c^2*d+818*a*k^2-2239*b*k^2+3976*c*k^2+206*d*k^2+596*e*k^2+4143*f*k^2+2563*g*k^2-1347*h*k^2+3192*i*k^2-1698*j*k^2+2228*k^3,
    b*c*d+476*a*k^2-1103*b*k^2-1271*c*k^2-3617*d*k^2-4466*e*k^2+2899*f*k^2-2938*g*k^2-3295*h*k^2+479*i*k^2-376*j*k^2+131*k^3,
    a*c*d+4177*a*k^2+2017*b*k^2-3791*c*k^2-11*d*k^2-143*e*k^2+2893*f*k^2+3941*g*k^2+4602*h*k^2+2349*i*k^2+2469*j*k^2+2989*k^3,
    b^2*d-476*a*k^2+266*b*k^2+2743*c*k^2-4293*d*k^2-1104*e*k^2-1103*f*k^2+1018*g*k^2-4968*h*k^2+873*i*k^2+4078*j*k^2-2091*k^3,
    a*b*d+2387*a*k^2+1716*b*k^2-1318*c*k^2+1758*d*k^2-2037*e*k^2-2126*f*k^2+2421*g*k^2-572*h*k^2-1121*i*k^2-2384*j*k^2+2002*k^3,
    a^2*d-4539*a*k^2+2503*b*k^2-4492*c*k^2+2401*d*k^2-1757*e*k^2-1425*f*k^2-2004*g*k^2+2566*h*k^2-4598*i*k^2+1407*j*k^2-2701*k^3,
    c^3+2126*a*k^2+2787*b*k^2+1543*c*k^2+3623*d*k^2+4926*e*k^2+1610*f*k^2-3249*g*k^2+3735*h*k^2+3522*i*k^2+2121*j*k^2-2531*k^3,
    b*c^2+114*a*k^2+268*b*k^2-3640*c*k^2-2257*d*k^2+809*e*k^2-1014*f*k^2+4805*g*k^2+3189*h*k^2-4444*i*k^2+1691*j*k^2-2770*k^3,
    a*c^2+3670*a*k^2+1965*b*k^2-3152*c*k^2-1329*d*k^2-3568*e*k^2-4111*f*k^2+3836*g*k^2+855*h*k^2+3055*i*k^2+1947*j*k^2-3086*k^3,
    b^2*c+2047*a*k^2+1115*b*k^2-2978*c*k^2+4165*d*k^2+250*e*k^2+926*f*k^2-2052*g*k^2+973*h*k^2+4653*i*k^2+1990*j*k^2-3017*k^3,
    a*b*c+1150*a*k^2-2424*b*k^2-898*c*k^2+1130*d*k^2+4588*e*k^2-3261*f*k^2+1578*g*k^2+2253*h*k^2-2948*i*k^2-3921*j*k^2+4022*k^3,
    a^2*c-1791*a*k^2-3415*b*k^2+1019*c*k^2-1534*d*k^2+3673*e*k^2-2468*f*k^2+3149*g*k^2-3288*h*k^2-827*i*k^2+110*j*k^2+4540*k^3,
    b^3+3652*a*k^2+2647*b*k^2-573*c*k^2-4554*d*k^2-2454*e*k^2+2251*f*k^2+4904*g*k^2-1969*h*k^2-1681*i*k^2-648*j*k^2+4684*k^3,
    a*b^2+214*a*k^2-1234*b*k^2-4637*c*k^2-3556*d*k^2-3118*e*k^2+568*f*k^2-1457*g*k^2-2459*h*k^2+4411*i*k^2+1038*j*k^2+3231*k^3,
    a^2*b-2258*a*k^2+4385*b*k^2-3693*c*k^2-4425*d*k^2+1716*e*k^2+2113*f*k^2+2104*g*k^2+1807*h*k^2-4196*i*k^2-3535*j*k^2-2249*k^3,
    a^3+2309*a*k^2-2462*b*k^2+1894*c*k^2+1736*d*k^2-4345*e*k^2+757*f*k^2-4681*g*k^2-4313*h*k^2-1004*i*k^2-3839*j*k^2+4027*k^3
    )
