--This file computes Betti tables for P^1 for d = 7 and b = 4
A := degreesRing 2
new HashTable from {
--tb stands for Total Betti numbers
"tb"=>new HashTable from {(6,1) => 2, (0,0) => 5, (1,0) => 28, (0,1) => 0, (1,1) => 0, (2,0) => 63, (2,1) => 0, (3,0) => 70, (3,1) => 0, (4,0) => 35, (4,1) => 0, (5,0) => 0, (5,1) => 7, (6,0) => 0},
--mb stands for Multigraded Betti numbers
"mb"=>new HashTable from {(6,1) => A_0^27*A_1^26+A_0^26*A_1^27, (0,0) => A_0^4+A_0^3*A_1+A_0^2*A_1^2+A_0*A_1^3+A_1^4, (0,1) => 0, (1,0) => A_0^10*A_1+2*A_0^9*A_1^2+3*A_0^8*A_1^3+4*A_0^7*A_1^4+4*A_0^6*A_1^5+4*A_0^5*A_1^6+4*A_0^4*A_1^7+3*A_0^3*A_1^8+2*A_0^2*A_1^9+A_0*A_1^10, (2,0) => A_0^15*A_1^3+2*A_0^14*A_1^4+4*A_0^13*A_1^5+5*A_0^12*A_1^6+7*A_0^11*A_1^7+8*A_0^10*A_1^8+9*A_0^9*A_1^9+8*A_0^8*A_1^10+7*A_0^7*A_1^11+5*A_0^6*A_1^12+4*A_0^5*A_1^13+2*A_0^4*A_1^14+A_0^3*A_1^15, (1,1) => 0, (2,1) => 0, (3,0) => A_0^19*A_1^6+2*A_0^18*A_1^7+3*A_0^17*A_1^8+5*A_0^16*A_1^9+7*A_0^15*A_1^10+8*A_0^14*A_1^11+9*A_0^13*A_1^12+9*A_0^12*A_1^13+8*A_0^11*A_1^14+7*A_0^10*A_1^15+5*A_0^9*A_1^16+3*A_0^8*A_1^17+2*A_0^7*A_1^18+A_0^6*A_1^19, (3,1) => 0, (4,0) => A_0^22*A_1^10+A_0^21*A_1^11+2*A_0^20*A_1^12+3*A_0^19*A_1^13+4*A_0^18*A_1^14+4*A_0^17*A_1^15+5*A_0^16*A_1^16+4*A_0^15*A_1^17+4*A_0^14*A_1^18+3*A_0^13*A_1^19+2*A_0^12*A_1^20+A_0^11*A_1^21+A_0^10*A_1^22, (4,1) => 0, (5,0) => 0, (6,0) => 0, (5,1) => A_0^26*A_1^20+A_0^25*A_1^21+A_0^24*A_1^22+A_0^23*A_1^23+A_0^22*A_1^24+A_0^21*A_1^25+A_0^20*A_1^26},
--sb represents the betti numbers as sums of Schur functors
"sb"=>new HashTable from {(6,1) => {({27,26},1)}, (0,0) => {({4,0},1)}, (1,0) => {({10,1},1)}, (0,1) => {}, (1,1) => {}, (2,0) => {({15,3},1)}, (2,1) => {}, (3,0) => {({19,6},1)}, (3,1) => {}, (4,0) => {({22,10},1)}, (4,1) => {}, (5,0) => {}, (5,1) => {({26,20},1)}, (6,0) => {}},
--dw encodes the dominant weights in each entry
"dw"=>new HashTable from {(6,1) => {{27,26}}, (0,0) => {{4,0}}, (1,0) => {{10,1}}, (0,1) => {}, (1,1) => {}, (2,0) => {{15,3}}, (2,1) => {}, (3,0) => {{19,6}}, (3,1) => {}, (4,0) => {{22,10}}, (4,1) => {}, (5,0) => {}, (5,1) => {{26,20}}, (6,0) => {}},
--lw encodes the lex leading weight in each entry
"lw"=>new HashTable from {(6,1) => {27,26}, (0,0) => {4,0}, (1,0) => {10,1}, (0,1) => {}, (1,1) => {}, (2,0) => {15,3}, (2,1) => {}, (3,0) => {19,6}, (3,1) => {}, (4,0) => {22,10}, (4,1) => {}, (5,0) => {}, (5,1) => {26,20}, (6,0) => {}},
--nr encodes the number of disctinct reprsentations in each entry
"nr"=>new HashTable from {(6,1) => 1, (0,0) => 1, (1,0) => 1, (0,1) => 0, (1,1) => 0, (2,0) => 1, (2,1) => 0, (3,0) => 1, (3,1) => 0, (4,0) => 1, (4,1) => 0, (5,0) => 0, (5,1) => 1, (6,0) => 0},
--nrm encodes the number of representations with multiplicity in each entry
"nrm"=>new HashTable from {(6,1) => 1, (0,0) => 1, (1,0) => 1, (0,1) => 0, (1,1) => 0, (2,0) => 1, (2,1) => 0, (3,0) => 1, (3,1) => 0, (4,0) => 1, (4,1) => 0, (5,0) => 0, (5,1) => 1, (6,0) => 0},
--er encodes the errors in the computed multigraded Hilbert series via our Schur method in each entry
"er"=>new HashTable from {(6,1) => 2, (0,0) => 5, (1,0) => 28, (0,1) => 0, (1,1) => 0, (2,0) => 63, (2,1) => 0, (3,0) => 70, (3,1) => 0, (4,0) => 35, (4,1) => 0, (5,0) => 0, (5,1) => 7, (6,0) => 0},
--bs encodes the Boij-Soederberg coefficients each entry
"bs"=>{5040/1},
}