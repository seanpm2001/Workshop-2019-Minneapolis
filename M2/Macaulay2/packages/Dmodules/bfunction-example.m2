restart
needsPackage "Dmodules"

R = QQ[x,y,z,w,t,Dx,Dy,Dz,Dw,Dt, WeylAlgebra => {x=>Dx, y=>Dy, z=>Dz, w=>Dw, t=>Dt}]
m = matrix {{x, y}, {z, w}}
f = det m
I = ideal(t - f, Dx + w * Dt, Dy -z * Dt, Dz -y * Dt, Dw + x * Dt)
w = {0,0,0,0,-1,0,0,0,0,1}

J = inw(I, w)

(-Dt * t + 1) * (-Dt * t + 2)
