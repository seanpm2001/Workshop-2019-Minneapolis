needsPackage "Dmodules"

--Input: element in D
--Output: corresponding gens in the distraction, viewed in ring S
genToDistractionGens = (f,S)->(
    n := numgens ring f//2;
    E := exponents f;
    C := flatten entries (coefficients f)#1;
    --Each exponent pair (a,b) for writing terms in f as x^a*p(theta)*\del^b, as in the proof of SST Lem. 2.3.1:
    abList := apply(E,e->(
	    thetaExp := apply(n,i-> min(e#(n+i),e#i)); 
	    e-(thetaExp|thetaExp)
	    ));
    --List of unique exponent pairs (a,b) that occur in abList:
    UabList := unique abList;
    --The poly p(theta) in x^a*p(theta)*\del^b for each pair (a,b):
    pPolyList := apply(length UabList,l->(  
	    apply(length E,i-> (
		if UabList#l == abList#i then {C#i,drop(E#i-abList#i,n)} else {}))
	));
    --Now for each pair (a,b), match each [theta]_b with the correct p(theta - b), as in SST Thm 2.3.4:
    apply(length UabList,i->(
	    b := drop(UabList#i,n);
	    tSubb := thetaBracketSub(b,S);
	    pTheta := sum apply(pPolyList#i,j-> 
		if j == {} then 0 else sub(j#0,S) * product apply(numgens S,k->( product apply((j#1)#k,l->(S_k-l))))
		);
	    phi := map(S,S,S_*-b);
	    pThetaMinusb := phi(pTheta);
	    tSubb*pThetaMinusb
	    ))
    )

--Input: torus-fixed left D-ideal J
--Output: the distraction of J, viewed in ring S
thetaIdeal = (J,S) ->(
    n := numgens ring J//2;
    if n != numgens S then error "mismatched numbers of variables";
    ideal flatten apply(J_*,j-> genToDistractionGens(j,S))
)
	    
		    
--Input: b is a List of length n (= numVars of ambient space for D)
--       S is a ring for the output
--Output: [theta]_b as in SST p.68
thetaBracketSub = (b,S)->( 
    n := length b;
    if n != numgens S then error "length of exponent vector does not match number of variables";
    product apply(n,i-> product apply(b#i,j-> S_i - j))
    )	            

--Input: 0-dimensional primary ideal
--Output: corresponding point, as a vector, with its multiplicity  
solveMax = (I)->(
   l := numgens ring I;
   v := apply(l,i-> 0);
   J = radical I;
   scan(J_*,f->(
	   N := (coefficients f)_0;
	   M := (coefficients f)_1;
	   if numcols N == 2 then v=v+(-M_0_1/M_0_0)*(entries ((basis ZZ^l)_(index N_0_0)))
	   ));
     v
 )


expts = (H,w)->(
        J := inw(H,flatten {-w,w});
	if sub(J,ring H) != H then error "ideal is not torus-fixed";
	S := QQ[t_1..t_(numgens ring J//2)];
        L := decompose thetaIdeal(H,S);
    	apply(L,l-> solveMax(l))
	)


exptsMult = (H,w)->(
        J := inw(H,flatten {-w,w});
--	if sub(J,ring H) != H then error "ideal is not torus-fixed";
	S := QQ[t_1..t_(numgens ring J//2)];
        L := primaryDecomposition thetaIdeal(J,S);
	apply(L,l->( 
		m := 1; 
		r := radical l; 
		while (l:(r^m)) != (ideal 1_(ring l)) do( 
		    m = m+1 
		    );
		{m, solveMax(l)}
		))
	)
    
end;
--------------------
--------------------
