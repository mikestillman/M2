restart
uninstallAllPackages()
restart
installPackage "TowerRings"
installPackage "TraceForm"
installPackage "FractionalIdeals"
installPackage "AdjoinRoots"
installPackage "UPolynomials"
installPackage "Puiseux" -- 1 error
installPackage "MatrixNormalForms"
installPackage "IntegralBases"
installPackage "LocalBasis"

restart
check "TowerRings" -- 3 errors
check "TraceForm" -- 1 error
check "FractionalIdeals" -- 1 error
check "AdjoinRoots" -- 3 errors
check "UPolynomials" -- 1 error
check "Puiseux" -- 1 error
check "MatrixNormalForms" -- 3 errors
check "IntegralBases" -- no tests
check "LocalBasis" -- 6 tests fail.  At least one takes a long time. (check_26)

-- what about Trager.m2? UPolynomials2.m2?