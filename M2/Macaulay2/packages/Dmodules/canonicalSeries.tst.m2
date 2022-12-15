-*
-- Idea:

Power = new HeaderType of Expression
Power.synonym = "power expression"
Power#operator = "^"
expressionValue Power := (x) -> (expressionValue x#0) ^ (expressionValue x#1)
*-


Dtrace 1
pInfo(1, "testing canonicalSeries...")

------------------------------------
-- 
------------------------------------
W = makeWA(QQ[x_1,x_2])
for b in {0,1} do(
    F1 = ideal(x_1*dx_1*(x_1*dx_1+b), x_1*dx_1*(x_2*dx_2+b),  
	x_2*dx_2*(x_1*dx_1+b), x_2*dx_2*(x_2*dx_2+b));
    assert(isTorusFixed F1 == true)
    )
for b in {0,1} do(
    F2 = ideal(x_1*dx_1*x_2*dx_2-1, x_1*dx_1-b*x_2*dx_2-b+1)
    assert(isTorusFixed F2 == true)
    )





--A homog 012
I = ideal(D_2^2-D_1*D_3,x_1*D_1+x_2*D_2+x_3*D_3,x_2*D_2+2*x_3*D_3+1)
w = {{



needsPackage "Dmodules"
H = gkz(matrix{{1,1,1},{0,1,2}},{0,-1})
toString H



path = prepend("~/Desktop/Workshop-2019-Minneapolis/M2/Macaulay2/packages/", path)
installPackage "Dmodules"
