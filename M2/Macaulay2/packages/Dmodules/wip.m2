
end--
-- Ex 2.3.16

restart
load "wip.m2"




isPrimary I

Betas#3
Alphas = {}

t_0*t_1 % I


beta = first exponents L#1


NilssonElement = new Type of MonoidELement

------------------------------------------------------------------------------
-- Constructing terms in the Nilsson ring
------------------------------------------------------------------------------

NilssonTerm = new Type of MutableHashTable
NilssonTerm.synonym = "a function of the Nilsson class"
expression NilssonTerm := X -> if hasAttribute (X, ReverseDictionary) 
    then expression getAttribute (X, ReverseDictionary) else 
    new FunctionApplication from {normalToricVariety, (rays X, max X)}

NilssonTerm == NilssonTerm := (S,T) -> S === T
NilssonTerm  + NilssonTerm := (S,T) -> merge(C,D,plus)
NilssonTerm  * NilssonTerm := (S,T) -> combine(C,D,(j,k)->apply(j,k,plus),times,plus)

nilssonTerm = method (TypicalValue => NilssonTerm, 
    Options => {
	WeylAlgebra       => null
	MonomialExponents => {1/2,0},
 	PolynomialInLog   => 1,
    	Variable          => getSymbol "x",
	}
    )
nilssonTerm (List, List) := opts -> (rayList, coneList) -> (
    coneList' := sort apply(coneList, sigma -> sort sigma);
    X := new NilssonTerm from {
    	symbol rays  => rayList,
    	symbol max   => coneList',
    	symbol cache => new CacheTable
	};
    if opts.WeilToClass =!= null then X.cache.fromWDivToCl = opts.WeilToClass;
    X.cache.CoefficientRing = opts.CoefficientRing;
    X.cache.Variable = opts.Variable;
    X
    )
