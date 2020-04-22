// To Do:
// 1. precision for real/padic case
// 2. timing names









// GESolver.m

//============================================================================//
//============================================================================//
/*
This code computes integer solutions of the Goormaghtigh Equation
                    (x^m-1)/(x-1) = (y^n-1)/(y-1)
for y > x > 1 and m > n > 2, for fixed n. In particular, fixing x,n yields a
Thue-Mahler equation of the form
                    (x-1)y^(n-1) + ... + (x-1)y + x = x^m.
This algorithm computes solution (y,m) of this equation, and is based on the
Thue-Mahler algorithm of Tzanakis-de Weger, as well as its updated version by
A. Gherga, R. von Känel, B. Matschke, and S. Siksek.

Authors: Michael A. Bennett, Adela Gherga, Dijana Kreso
Last Update: Aug. 17, 2018

Details of this code can be found in the authors' paper
"An old and new approach to Goormaghtigh's Equation."

//============================================================================//

Remarks:
    This current implementation primarily supports Goormaghtigh equations with
    n = 5. Note that as listed in the authors' aforementioned paper, this
    algorithm is only needed for x in [2,719].

Bottlenecks of this current implementation:
    - computing the class group
    - computing the ring of integers of the splitting field of the TM equation
    - computing the unit group

//============================================================================//

INPUT:

OUTPUT:

EXAMPLE:

*/
//============================================================================//
//============================================================================//


ModpCheck:= function(F,RHSprimes,q : qDividesRHS:=false)

    /*
     Description: default to where z = 0 nad p does not divide RHS
     Input: F:= polynomial F(X,Y) in question
            RHSprimes:= primes appearing on RHS of TM equation in local test
            q:= rational prime under which the local test is performed
                that is, we search for solutions of the TM equations mod q
            qDividesRHS:= boolean value determining whether q | RHS
                          default value is false
     Output: hasSolutions:= boolean value determining whether TM equation has nontrivial local
                            solutions mod q
     Example:
   */

    hasSolutions:= false;

    if (qDividesRHS eq true) then
	// set hasSolutions to true if F(X,Y) has a solution (u,v) != (0,0) mod q when q | RHS
	for u,v in [1..q-1] do
	    assert [u,v] ne [0,0];
	    F_q:= Integers()! (Evaluate(F,[u,v]));
	    if (F_q mod q eq 0) then
		hasSolutions:= true;
		break u;
	    end if;
	end for;
    else
	// when q does not divide RHS
	Zmodq:=FiniteField(q,1);
	RHSprimesModq:= [];
	rhs:= [];
	// determine all possibilites of p^i mod q
	for p in RHSprimes do
	    pModq:= Zmodq! p;
	    Append(~RHSprimesModq, [Zmodq! (p^i) : i in [0..Order(pModq)-1]]);
	end for;
	RHSprod:= CartesianProduct(RHSprimesModq);
	// determine all possibilities of RHS mod q
	for prod in RHSprod do
	    Append(~rhs, Integers()! &*prod);
	end for;
	// set hasSolutions to true if F(X,Y) has a solution (u,v) != (0,0) moq q
	// when q does not divide RHS
	for u,v in [1..q-1] do
	    assert [u,v] ne [0,0];
	    F_q:= Integers()! (Evaluate(F,[u,v]));
	    if (F_q mod q in rhs) then
		hasSolutions:= true;
		break u;
	    end if;
	end for;
    end if;
    return hasSolutions;
end function;

localtest:= function(N,F,DiscF)

    /*
     Description: determines whether the TM equation has local or partial local obstructions
     Input: N:= conductor of corresponding elliptic curves in question
            F:= polynomial F(X,Y) in question
            DiscF:= discriminant of F(X,Y)
     Output: partialObstruction:= set of primes p for which solutions can only be possible
     	     			  with p having exponent 0 on RHS of the TM equation
             localobstruction:= set of primes p presenting obstructions for the TM equation
	                        that is, an obstruction exists at p as per Theorem 1 of BeGhRe
                                or no solution of the TM equation exists mod p
     Example:
   */

    // determine rational primes to verify; 2,3 and all prime factors of N
    testPrimes:= PrimeFactors(N);
    if 2 notin testPrimes then
	Append(~testPrimes, 2);
    end if;
    if 3 notin testPrimes then
	Append(~testPrimes, 3);
    end if;

    localObstruction:= [];
    partialObstruction:= [];
    for p in testPrimes do
	// search for solutions (u,v) of F(u,v) mod p
	// under the assumption that the exponent on p is > 0
	if (p le 13) or (p in [13..151] and (#testPrimes le 3)) then
	    // the bounds 13,1513 are arbitrary, but serve to decrease search time

	    posExpSol:= ModpCheck(F,testPrimes,p : qDividesRHS:= true);
	    if (p ge 3) and (Valuation(N,p) eq 1) and (DiscF mod p ne 0) then
		// verify local obstructions as per Theorem 1 of BeGhRe
		// ie. if Valuation(N,p) = 1 for p >= 3, then p | DiscF*F(u,v)
		// thus if DiscF != 0 mod p, then F(u,v) = 0 mod p for some (u,v)
		// if u = v = 0 mod p is the only solution, gcd(u,v) != 1
		// hence locMal obstruction at p
		if (posExpSol eq false) then
		    Append(~localObstruction, p);
		    return partialObstruction, localObstruction;
		end if;
	    else
		// verify local obstructions for primes possible on RHS
		// this includes divisors of N, and 2,3

		// search for solutions (u,v) of F(u,v) mod p
		// under the assumption that the exponent on p is 0
		zeroExpSol:= ModpCheck(F,Exclude(testPrimes,p),p :
				       qDividesRHS:=false);
		if (zeroExpSol eq false) and (posExpSol eq false) then
		    // if u = v = 0 mod p is the only solution in both cases
		    // gcd(u,v) != 1, hence local obstruction at p
	    	    Append(~localObstruction, p);
		    return partialObstruction, localObstruction;
		elif (zeroExpSol eq true) and (posExpSol eq false) then
		    // if a solution (u,v) != (0,0) mod p exists
		    // when the exponent on p is 0
		    // but u = v = 0 mod p is the only solution
		    // when the exponent on p is > 0
		    // partial obstruction at p; can remove p from primelist
		    Append(~partialObstruction, p);
		end if;
	    end if;
	end if;
    end for;

    return partialObstruction, localObstruction;
end function;

prep0:= function(hash,LogFile,clist,N)

    /*
     Description: Verify conditions of Theorem 1 of BeReGh for clist,N
     Input: hash:= string set appended to the start of every output line;
                   used to ensure output corresponds to correct Thue Mahler form
     	    LogFile:= store running times and additional information as "SUnitEqLogs.txt"
            clist:= [c_0, \dots, c_n], the coefficients of F(X,Y)
            N:= conductor of corresponding elliptic curves in question
     Output: f:= monic polynomial defining the number field K = Q(th)
             enterTM:= boolean value determining whether to enter the TM solver
             TMSolutions:= solutions for the TM equation arising from Thue equations
             RemainingCasesAllAs:= list of primelist and all corresponding a values
                                   comprising the RHS of F(x,y)
     Example:
   */

    QUV<U,V>:=PolynomialRing(Rationals(),2);
    Qx<x>:= PolynomialRing(Rationals());

    // general setup for Thue-Mahler solver
    assert &and[c in Integers() : c in clist];
    c0:=Integers()!clist[1];
    assert c0 ne 0;
    n:=#clist-1;
    assert n eq 3;

    // generate the relevant Thue Mahler polynomial
    F:=&+[clist[i+1]*U^(n-i)*V^i : i in [0..n]];
    assert IsHomogeneous(F);
    DiscF:= -27*clist[1]^2*clist[4]^2 + clist[2]^2*clist[3]^2;
    DiscF:= DiscF + 18*clist[1]*clist[2]*clist[3]*clist[4];
    DiscF:= DiscF - 4*clist[1]*clist[3]^3 - 4*clist[2]^3*clist[4];
    assert DiscF eq Discriminant(Evaluate(F,[x,1]));

    fclist:= [1] cat [clist[i+1]*c0^(i-1) : i in [1..n]];
    f:=&+[fclist[i+1]*x^(n-i) : i in [0..n]];
    c0:= Integers()!fclist[1]; // update c0
    assert c0 eq 1;
    assert IsMonic(f);
    assert Coefficients(f) eq
	   Coefficients(clist[1]^(n-1)*Evaluate(F,[x/clist[1],1]));
    assert Degree(f) eq n;
    assert IsIrreducible(f);
    assert &and[c in Integers() : c in Coefficients(f)];

    // verify conditions of Theorem 1 of BeReGh
    alpha:= Valuation(N,2);
    beta:= Valuation(N,3);
    alpha0:= Valuation(DiscF,2);
    beta0:= Valuation(DiscF,3);
    N0:= Integers()! ( N/((2^alpha)*(3^beta)));
    N1:= Integers()! (DiscF/((2^alpha0)*(3^beta0)));
    primelist:= PrimeDivisors(N0);
    assert &and[IsPrime(p) : p in primelist];
    assert (2 notin primelist) and (3 notin primelist);
    assert alpha in [0..8];
    assert beta in [0..5];
    assert IsDivisibleBy(N0,N1);

    enterTM:= true;
    TMSolutions:= []; // store all Thue-Mahler solutions
    RemainingCasesAllAs:= [];

    // verify local and partial local obstructions
    partialObstruction, localObstruction:= localtest(N,F,DiscF);
    // assert TM forms with local obstructions have been removed from !!!!!!!
    assert IsEmpty(localObstruction);
    if (IsEmpty(partialObstruction) eq false) then
	// partial local obstructions present; remove p from primelist
	printf hash cat " Partial local obstructions present \n";
	printf hash cat " No solutions with positive exponent of %o are possible \n",
	       partialObstruction;
    end if;

    // generate a record to store relevant prime bounds
    // determine any bounds as per Theorem 1 of BeGhRe correspondence
    primeInfo:= recformat<prime,alpha1,unbounded>;
    primeBounds:= [[],[]];

    // verify behaviour at p = 2
    if (alpha eq 0) then
	if alpha0 eq 2 then
	    Append(~primeBounds[1], rec<primeInfo | prime:= 2, alpha1:= 0>);
	    Append(~primeBounds[1], rec<primeInfo | prime:= 2, alpha1:= 3>);
	end if;
    elif (alpha eq 1) then
        if (alpha0 eq 2) then
	    Append(~primeBounds[1], rec<primeInfo | prime:= 2, alpha1:= 4, unbounded:= "yes">);
	elif (alpha0 eq 3) then
	    Append(~primeBounds[1], rec<primeInfo | prime:= 2, alpha1:= 3, unbounded:= "yes">);
	end if;
    elif (alpha eq 2) then
        if (alpha0 eq 2) then
	    Append(~primeBounds[1], rec<primeInfo | prime:= 2, alpha1:= 1>);
        elif (alpha0 eq 4) then
	    Append(~primeBounds[1], rec<primeInfo | prime:= 2, alpha1:= 0>);
	    Append(~primeBounds[1], rec<primeInfo | prime:= 2, alpha1:= 1>);
        end if;
    elif (alpha eq 3) then
        if (alpha0 eq 2) then
	    Append(~primeBounds[1], rec<primeInfo | prime:= 2, alpha1:= 1>);
	    Append(~primeBounds[1], rec<primeInfo | prime:= 2, alpha1:= 2>);
        elif (alpha0 eq 3) then
	    Append(~primeBounds[1], rec<primeInfo | prime:= 2, alpha1:= 2>);
        elif (alpha0 eq 4) then
	    Append(~primeBounds[1], rec<primeInfo | prime:= 2, alpha1:= 0>);
	    Append(~primeBounds[1], rec<primeInfo | prime:= 2, alpha1:= 1>);
        end if;
    elif (alpha eq 4) then
        if (alpha0 eq 2) then
	    Append(~primeBounds[1], rec<primeInfo | prime:= 2, alpha1:= 0, unbounded:= "yes">);
	elif (alpha0 eq 3) then
	    Append(~primeBounds[1], rec<primeInfo | prime:= 2, alpha1:= 2, unbounded:= "yes">);
        elif (alpha0 eq 4) then
	    Append(~primeBounds[1], rec<primeInfo | prime:= 2, alpha1:= 0>);
	    Append(~primeBounds[1], rec<primeInfo | prime:= 2, alpha1:= 1>);
        end if;
    elif (alpha eq 5) then
        if (alpha0 eq 2) then
	    Append(~primeBounds[1], rec<primeInfo | prime:= 2, alpha1:= 0>);
        elif (alpha0 eq 3) then
	    Append(~primeBounds[1], rec<primeInfo | prime:= 2, alpha1:= 1>);
        end if;
    elif (alpha eq 6) then
        if (alpha0 eq 2) then
	    Append(~primeBounds[1], rec<primeInfo | prime:= 2, alpha1:= 0, unbounded:= "yes">);
        elif (alpha0 eq 3) then
	    Append(~primeBounds[1], rec<primeInfo | prime:= 2, alpha1:= 1, unbounded:= "yes">);
        elif (alpha0 eq 4) then
	    Append(~primeBounds[1], rec<primeInfo | prime:= 2, alpha1:= 0>);
	    Append(~primeBounds[1], rec<primeInfo | prime:= 2, alpha1:= 1>);
        end if;
    elif (alpha eq 7) then
        if (alpha0 eq 3) then
	    Append(~primeBounds[1], rec<primeInfo | prime:= 2, alpha1:= 0>);
        elif (alpha0 eq 4) then
	    Append(~primeBounds[1], rec<primeInfo | prime:= 2, alpha1:= 0>);
        end if;
    elif (alpha eq 8) then
        if (alpha0 eq 3) then
	    Append(~primeBounds[1], rec<primeInfo | prime:= 2, alpha1:= 1>);
        end if;
    end if;

    // verify behaviour at p = 3
    if (beta eq 0) then
        if (beta0 eq 0) then
	    Append(~primeBounds[2], rec<primeInfo | prime:= 3, alpha1:= 0>);
        end if;
    elif (beta eq 1) then
        if (beta0 eq 0) then
	    Append(~primeBounds[2], rec<primeInfo | prime:= 3, alpha1:= 1, unbounded:= "yes">);
        elif (beta0 eq 1) then
	    Append(~primeBounds[2], rec<primeInfo | prime:= 3, alpha1:= 0, unbounded:= "yes">);
	end if;
    elif (beta eq 2) then
        if (beta0 eq 0) then
	    Append(~primeBounds[2], rec<primeInfo | prime:= 3, alpha1:= 0, unbounded:= "yes">);
	elif (beta0 eq 1) then
	    Append(~primeBounds[2], rec<primeInfo | prime:= 3, alpha1:= 0, unbounded:= "yes">);
	elif (beta0 eq 3) then
	    Append(~primeBounds[2], rec<primeInfo | prime:= 3, alpha1:= 0>);
	end if;
    elif (beta ge 3) then
        if (beta0 eq beta) then
	    Append(~primeBounds[2], rec<primeInfo | prime:= 3, alpha1:= 0>);
	    Append(~primeBounds[2], rec<primeInfo | prime:= 3, alpha1:= 1>);
        else
	    // when all coefficients of the form F_1 are  divisible by 3,
	    // since also beta1 = {0,1} and 3|LHS we must have that 3|RHS,  hence beta1 = 1
	    // in this case, we may divide 3 from both sides
	    // this yields the form F = F_1/3, whose discriminant has
	    // Valuation(DiscF,3) != beta0 = beta
	    // thus since beta1=1 is divided out, so beta1=0
	    Append(~primeBounds[2], rec<primeInfo | prime:= 3, alpha1:= 0>);
        end if;
    end if;

    // verify behaviour at primes dividing N1
    for p in PrimeDivisors(N1) do
	if IsDivisibleBy(N1,p^2) then
	    assert p in PrimeDivisors(N0);
	    primeBounds[#primeBounds+1]:= [];
	    Append(~primeBounds[#primeBounds],rec<primeInfo | prime:= p, alpha1:= 0>);
	    Append(~primeBounds[#primeBounds],rec<primeInfo | prime:= p, alpha1:= 1>);
	end if;
    end for;

    // remove superflous cases where a partial obstruction at p exists
    primeBoundsNew:= [];
    for pset in primeBounds do
	toRemove:= [];
	ps:= [i`prime : i in pset];
	// verify the pset corresponds to only 1 prime
	assert &and[p eq ps[1] : p in ps];
	p:= ps[1];
	if (p in partialObstruction) then
	    for i in [1..#pset] do
		x:= pset[i];
		assert x`prime eq p;
		// assert TM forms where Theorem 1 of BeReGh does not align with partial!!!!
		// obstructions have been removed
		assert ((assigned x`unbounded) and (x`alpha1 ge 1)) eq false;
		if (assigned x`unbounded) and (x`alpha1 eq 0) then
		    delete x`unbounded; // update bound at p
		elif (assigned x`unbounded eq false) and (x`alpha1 ge 1) then
		    // remove extra cases at p which are now not possible
		    Append(~toRemove,i);
		end if;
	    end for;
	end if;
	psetNew:= [pset[i] : i in [1..#pset] | i notin toRemove];

	// assert TM forms where Theorem 1 of BeReGh does not align with partial obstructions!!!!
	// have been removed
	assert (IsEmpty(psetNew) eq false);
	// verify pset now only includes the exponent 0 case at p
	if (p in partialObstruction) then
	    assert (#psetNew eq 1);
	    assert (assigned psetNew[1]`unbounded eq false);
	    assert (psetNew[1]`alpha1 eq 0);
	end if;
	Append(~primeBoundsNew, psetNew);
    end for;
    primeBounds:= primeBoundsNew;

    // generate all combinations of exponent restrictions as determined above
    Sdata:= []; // stores all combinations of prime bounds on each p
    expCombos:= CartesianProduct([[1..#pset] : pset in primeBounds]);
    for c in expCombos do
	Append(~Sdata, [primeBounds[i][c[i]] : i in [1..#c]]);
    end for;
    aprimelist:=[]; // store corresponding a value and primelist
    for pset in Sdata do
	a:= 1;
	primes:= primelist;
	for i in pset do
	    if (assigned i`unbounded) then
		if (i`prime notin primes) then
		    assert (i`prime eq 2) or (i`prime eq 3);
		    assert i`prime notin partialObstruction;
		    Append(~primes, i`prime);
		end if;
	    else
		if (i`prime in primes) then
		    Exclude(~primes,i`prime);
		end if;
		a:= a*(i`prime)^(i`alpha1);
	    end if;
	end for;
	Sort(~primes);
	if <a,primes> notin aprimelist then
	    Append(~aprimelist, <a,primes>);
	end if;
    end for;

    // store Thue-Mahler equations to be solved
    // corresponding Thue cases ignored; resolved in GenerateSUnitEquations.m
    RemainingCases:=aprimelist;

    for pset in aprimelist do
	if IsEmpty(pset[2]) then // no unbounded primes
	    Exclude(~RemainingCases, pset);
	end if;
    end for;

    // assert TM forms resolved via Thue equations have been removed FROM !!!!
    assert (IsEmpty(RemainingCases) eq false);

    // generate the corresponding S-unit equations
    // remove redundancy so that each primeset has all corresponding a values
    CaseInfoAllAs:= recformat<avalues,primelist>;
    RemainingCasesCopy:= RemainingCases;
    for pset in RemainingCases do
	if pset in RemainingCasesCopy then
	    a:= pset[1];
	    primelist:= pset[2];
	    avalues:= [a];
	    Exclude(~RemainingCasesCopy, pset);
	    for pset2 in RemainingCasesCopy do
		a2:= pset2[1];
		primelist2:= pset2[2];
		if (primelist eq primelist2) then
		    Append(~avalues, a2);
		    Exclude(~RemainingCasesCopy, pset2);
		end if;
	    end for;
	    Sort(~avalues);
	    apset:=rec<CaseInfoAllAs | avalues:=avalues, primelist:= primelist>;
	    Append(~RemainingCasesAllAs, apset);
	end if;
    end for;

    // if the code has made it this far, the following must hold
    assert enterTM and IsEmpty(TMSolutions);
    return f, enterTM, TMSolutions, RemainingCasesAllAs;
end function;

ijkAutL:= function(fieldLinfo)

    /*
     Description: generate automorphisms of L, i0,j,k as in Section 6.1 of Gh
     Input: fieldLinfo: record of the splitting field L of K = Q(th)
     Output: ijk:= automorphisms i0,j,k: L -> C as in Section 6.1 of Gh
             AutL:= all automorphisms L -> C of L
     Example:
   */

    L:= fieldLinfo`field;
    tl:= fieldLinfo`gen;
    G,Aut,tau:= AutomorphismGroup(L);
    assert IsIsomorphic(G, Sym(3)) or IsIsomorphic(G, Alt(3));

    ijk:= [];
    if Order(G.1) eq 3 then
        assert G.1^3 eq Id(G);
        if (tau(G.1))(tl[1]) eq tl[2] then
            ijk[1]:= tau(G.1);
            ijk[2]:= tau(G.1^2);
        else
            ijk[1]:= tau(G.1^2);
            ijk[2]:= tau(G.1);
        end if;
        ijk[3]:= tau(G.1^3); // identity map
    elif Order(G.2) eq 3 then
        assert G.2^3 eq Id(G);
        if (tau(G.2))(tl[1]) eq tl[2] then
            ijk[1]:= tau(G.2);
            ijk[2]:= tau(G.2^2);
        else
            ijk[1]:= tau(G.2^2);
            ijk[2]:= tau(G.2);
        end if;
        ijk[3]:= tau(G.2^3);
    end if;

    AutL:= [];
    for x in G do
        Append(~AutL, tau(x));
    end for;

    // verify that i,j,k permutes the roots tl
    assert (ijk[1](tl[1]) eq tl[2]) and (ijk[2](tl[1]) eq tl[3]) and (ijk[3](tl[1]) eq tl[1]);
    assert (ijk[1](tl[2]) eq tl[3]) and (ijk[2](tl[2]) eq tl[1]) and (ijk[3](tl[2]) eq tl[2]);
    assert (ijk[1](tl[3]) eq tl[1]) and (ijk[2](tl[3]) eq tl[2]) and (ijk[3](tl[3]) eq tl[3]);

    return ijk, AutL;
end function;

monic:= function(fieldKinfo,clist,primelist,avalues)

    /*
     Description: Reduce F(X,Y) = a_i p_1^(z_1) \cdots p_v^(z_v) to a
                  monic equation via a change of variables and output the new corresponding
                  a values (c_d), along with [a,u_d,d] as in Section 3.1 of Gh
     Input: fieldKinfo:= record of the field K = Q(th)
            clist:= [c_0, \dots, c_n], the coefficients of F(X,Y)
            primelist:= [p_1, \dots, p_v], rational primes on RHS of F(X,Y)
            avalues:= [a_1, \dots, a_m], fixed coefficients on RHS of F(X,Y)
     Output: alistNew:= list of records of all c_d (newa) values with all corresponding
                        [a,u_d,d] values as in Section 3.1 of Gh
     Example:
   */

    assert &and[IsPrime(p) : p in primelist];
    assert &and[c in Integers() : c in clist];
    assert &and[a ne 0 : a in avalues];
    c0:=Integers()!clist[1];
    assert c0 ne 0;
    n:=#clist-1;
    assert n ge 3;
    QUV<U,V>:=PolynomialRing(Rationals(),2);

    // generate the relevant Thue Mahler polynomial
    F:=&+[clist[i+1]*U^(n-i)*V^i : i in [0..n]];
    assert IsHomogeneous(F);
    Qx<x>:= PolynomialRing(Rationals());

    // generate the corresponding monic polynomial f(x,y)
    fclist:= [1] cat [clist[i+1]*c0^(i-1) : i in [1..n]];
    f:=&+[fclist[i+1]*x^(n-i) : i in [0..n]];
    assert f eq fieldKinfo`minpoly;

    aInfo:= recformat<newa,adu>;
    alist:= [];
    for a in avalues do
	// generate the prime factors of a
	afactors:= [q[1] : q in Factorization(a)];
	// generate the possible exponents on these primes appearing in gcd(a,Y)
	if IsEmpty(afactors) then
            product1:= [1];
	else
            exponents1:=[
	    [0..Min(Valuation(a,afactors[i]),Valuation(c0,afactors[i]))] :
	    i in [1..#afactors]];
            product1:= [];
	    // determine all possible combinations for primes of a appearing in gcd(a,Y)
            expCombos1:= CartesianProduct(exponents1);
            for c in expCombos1 do
		Append(~product1, &*{afactors[i]^c[i] : i in [1..#afactors]});
            end for;
	end if;

	// generate the possible exponents on the primes of primelist appearing in gcd(a,Y)
	exponents2:= [[0..Valuation(c0,primelist[i])] : i in [1..#primelist]];
	assert IsEmpty(exponents2) eq false;
	product2:= [];
	expCombos2:= CartesianProduct(exponents2);
	for c in expCombos2 do
            Append(~product2, &*{primelist[i]^c[i] : i in [1..#primelist]});
	end for;
	assert IsEmpty(product2) eq false;

	// generate the set of all positive integers m dividing c0
	// such that ord_p(m) <= ord_p(a) for each prime notin primelist
	// this is the set D in Section 3.1 of Gh
	curlyD:= [];
	for c in product1, d in product2 do
            if c*d notin curlyD then
		Append(~curlyD, c*d);
            end if;
	end for;
	Sort(~curlyD);

	// generate all possible values of gcd(a,Y) and corresponding new value of a
	// this information is used to write F(X,Y) as a monic equation
	duc:= [];
	for d in curlyD do
            u:= (c0^(n-1))/d^n;
            c:= Sign(u*a)*u*a/&*[p^Valuation(u*a, p) : p in primelist];
            assert &and[Valuation(c,p) eq 0 : p in primelist];
            assert c in Integers();
            f0:= u*Evaluate(F,[d*U/c0, V*d]);
            f:= Evaluate(f0,[x,1]);
	    assert f eq fieldKinfo`minpoly;
            Append(~duc, [d,u,Integers()!c]);
	end for;

	// remove redundancy and store the relevant data in a record
	// that is, store only the unique values of a and all corresponding values of u,d
	ducCopy:= duc;
	for dset in duc do
	    if dset in ducCopy then
		c:= dset[3];
		temp:= rec<aInfo |newa:= c, adu:=[]>;
		for dset2 in ducCopy do
		    c2:= dset2[3];
		    if (c eq c2) then
			Append(~temp`adu,[a,dset2[1],dset2[2]]);
			Exclude(~ducCopy,dset2);
		    end if;
		end for;
		Append(~alist, temp);
	    end if;
	end for;
	assert IsEmpty(ducCopy);
    end for;

    // remove redundancy across new a values by consolidating all corresponding a,d,u values
    alistIndex:= [1..#alist];
    alistNew:= [];
    for i in [1..#alist] do
	if i in alistIndex then
	    c:= alist[i]`newa;
	    temp:= rec< aInfo | newa:=c, adu:=[] >;
	    for j in alistIndex do
		c2:= alist[j]`newa;
		if (c eq c2) then
		    temp`adu:= temp`adu cat alist[j]`adu;
		    Exclude(~alistIndex, j);
		end if;
	    end for;
	    Append(~alistNew, temp);
	end if;
    end for;
    assert IsEmpty(alistIndex);

    return alistNew;
end function;

algs1and2:=function(fieldKinfo,p)

    /*
     Description: application of Algorithm 3.3.3 and 3.3.4 of Gh
     Input: fieldKinfo:= record of the field K = Q(th)
            p:= rational prime used as in Lemma 3.3.1 and 3.3.2 of Gh
     Output: Lp:= the set Lp as in Algorithms 3.3.3 and 3.3.4 of Gh
                  displayed as [[#fprs+1],aaa], where #fprs+1 indicates no unbounded prime
                  and aaa[i] is the exponent on the prime ideal fprs[i] in the ideal b
             Mp:= the set Mp as in Algorithms 3.3.3 and 3.3.4 of Gh
                  displayed as [[k],aaa], where k indicates the unbounded prime ideal
                  and aaa[i] is the exponent on the prime ideal fprs[i] in the ideal b
             fprs:= prime ideals in K above p
     Example:
   */

    K:=fieldKinfo`field;
    th:= K.1;
    OK:=fieldKinfo`ringofintegers;
    f:= fieldKinfo`minpoly;
    fprs:=Factorisation(p*OK);
    fprs:=[fact[1] : fact in fprs]; // generate all prime ideals above p

    prec:=10*(Valuation(Discriminant(f),p)+1);
    Zp:=pAdicRing(p,prec);
    rts:=Roots(f,Zp);
    rts:=[Integers()!r[1] : r in rts]; // generate all Zp-roots of f(t,1)
    Lp:=[];
    Mp:=[];

    // apply Algorithm 3.3.3 of Gh
    t:=1;
    ulist:=[w : w in [0..(p-1)]];
    while #ulist ne 0 do
        ulistNew:=[];
        for u in ulist do
	    // determine indices of prime ideals satisfying criteria of P_u of Algorithm 3.3.3
            cPu:=[i : i in [1..#fprs] | Valuation((u-th)*OK,fprs[i]) ge
					t*RamificationDegree(fprs[i])];
	    // determine all exponents in b_u of Algorithm 3.3.3
            fbu:= [ Min([Valuation((u-th)*OK,fprs[i]),
			 t*RamificationDegree(fprs[i])]) : i in [1..#fprs]];
            assert &*[fprs[i]^fbu[i] : i in [1..#fprs]] eq p^t*OK+(u-th)*OK;
	    // set index k of unbounded prime to #fprs + 1 to indicate no
	    // unbounded prime ideals
            k:= #fprs + 1;
            if #cPu eq 0 then
                if [[k],fbu] notin Lp then
                    Append(~Lp, [[k],fbu]);
                end if;
            elif #cPu eq 1 then
                fp:=fprs[cPu[1]]; // determine corresponding prime ideal of P_u
                efp:=RamificationDegree(fp)*InertiaDegree(fp);
                rtcount:=#[alpha : alpha in rts | Valuation(u-alpha,p) ge t];
		// verify conditions for membership in set M_p
                if (efp eq 1) and (rtcount ge 1) then
                    if [[cPu[1]],fbu] notin Mp then
			// set index k of unbounded prime to P_u[1]
                        Append(~Mp, [[cPu[1]],fbu]);
                    end if;
                else
                    ulistNew:=ulist cat [ u+p^(t)*w : w in [0..(p-1)]];
                end if;
            else
                ulistNew:=ulist cat [ u+p^(t)*w : w in [0..(p-1)]];
            end if;
        end for;
        ulist:=ulistNew;
        t:=t+1;
    end while; // end of Algorithm 3.3.3

    // apply Algorithm 3.3.4 of Gh
    // c0 = 1, so that Valuation(c0,p) = 1 by default
    ulist:=[p*w : w in [0..(p-1)]];
    t:=2;
    while #ulist ne 0 do
        ulistNew:=[];
        for u in ulist do
	    // determine indices of prime ideals satisfying criteria of P_u of Algorithm 3.3.4
            cPu:=[i : i in [1..#fprs] | Valuation(1-u*th,fprs[i]) ge
					t*RamificationDegree(fprs[i])];
	    // determine all exponents in b_u of Algorithm 3.3.4
            fbu:= [ Min([Valuation(1-u*th,fprs[i]),
			 t*RamificationDegree(fprs[i])]) : i in [1..#fprs]];
            assert &*[fprs[i]^fbu[i] : i in [1..#fprs]] eq (1-u*th)*OK+p^t*OK;
	    // set index k of unbounded prime to #fprs + 1 to indicate no
	    // unbounded prime ideals
            k:= #fprs + 1;
            if #cPu eq 0 then
                if [[k],fbu] notin Lp then
                    Append(~Lp, [[k],fbu]);
                end if;
            else
                ulistNew:=ulistNew cat [u+p^(t)*w : w in [0..(p-1)]];
            end if;
        end for;
        ulist:=ulistNew;
        t:=t+1;
    end while; // end of Algorithm 3.3.4

    // refinements
    // set aaa[k]=0 for each [[k],aaa] in Mp and remove subsequently identical cases
    for i in [1..#Mp] do
        pr1:= Mp[i];
        k:= pr1[1][1];
        Mp[i][2][k]:= 0;
    end for;
    MpNew:= [];
    for i in [1..#Mp] do
	if Mp[i] notin MpNew then
	    Append(~MpNew,Mp[i]);
	end if;
    end for;
    Mp:= MpNew;

    // remove redundancy
    // that is, remove cases of Lp covered by Mp
    toRemove:= [];
    for i in [1..#Lp] do
	fb:=&*[fprs[j]^Lp[i][2][j] : j in [1..#fprs]];
	for j in [1..#Mp] do
	    fb_:=&*[fprs[k]^Mp[j][2][k] : k in [1..#fprs]];
	    fp:=fprs[Mp[j][1][1]];
	    if IsIntegral(fb/fb_) and (fb/fb_ eq fp^(Valuation(fb/fb_,fp))) then
		if (Valuation(fb/fb_,fp) ge 0) then
		    Append(~toRemove,i);
		    break j;
		end if;
	    end if;
	end for;
    end for;
    LpNew:= [Lp[i] : i in [1..#Lp] | i notin toRemove];
    Lp:= LpNew;

    return Lp,Mp,fprs;
end function;

normInv:= function(R,OK)

    /*
     Description: generate all ideals of OK having norm R
     Input: R:= a positive integer
            OK:= corresponding ring of integers of the field K
     Output: all ideals of OK having norm R, displayed in an enumerated set
     Example:
   */

    assert R in Integers();
    assert R ge 1;
    R:=Integers()!R;
    assert R ge 1;
    if R eq 1 then
	return { 1*OK };
    end if;
    p:=Max(PrimeDivisors(R));
    fpr:=[fp[1] : fp in Factorisation(p*OK)];
    fpr:=[fp : fp in fpr | Valuation(Norm(fp),p) le Valuation(R,p)];
    if #fpr eq 0 then
	return {};
    else
	return &join{{fp*fa : fa in $$(R div Norm(fp), OK)} : fp in fpr };
    end if;
end function;

prep1:= function(fieldKinfo,clist,apset)

    /*
     Description: generate all ideal equations (3.8) of Gh for each set of primes and
     		  corresponding a values
     Input: fieldKinfo:= record of the field K = Q(th)
            clist:= [c_0, \dots, c_n], the coefficients of F(X,Y)
            apset:= a possible primelist and all its corresponding a values,
	            comprising the RHS of F(x,y)
     Output: afplist:= [aset,primelist,ideal_a,prime_ideal_list] where
                       ideal_a and prime_ideal_list are as in (3.8) of Gh
     Example:
   */

    avalues:= apset`avalues;
    primelist:= apset`primelist;
    assert &and[IsPrime(p) : p in primelist];
    assert &and[c in Integers() : c in clist];
    assert &and[a ne 0 : a in avalues];
    assert &and[GCD(a,p) eq 1 : a in avalues, p in primelist];
    n:=#clist-1;
    assert n ge 3;

    K:= fieldKinfo`field;
    OK:= fieldKinfo`ringofintegers;
    th:= OK!fieldKinfo`gen;
    f:= fieldKinfo`minpoly;
    fclist:= [Coefficient(f,i) : i in [3..0 by -1]];
    c0:= Integers()!fclist[1];
    assert c0 eq 1;

    afplist:=[* [* 1*OK, [] *] *];
    for p in primelist do
	// apply Algorithm 3.3.3 and Algorithm 3.3.4 of Gh
        Lp,Mp,fprs:=algs1and2(fieldKinfo,p);
	// determine all possible combinations of prime ideals as arising from the PIRL of Gh
	afplistNew1:=[*
		      [*pr[1]*&*[fprs[i]^fb[2][i] : i in [1..#fprs]], pr[2]*]:
		      fb in Lp, pr in afplist  *];
	afplistNew2:=[* [* pr[1]*&*[fprs[i]^qr[2][i] :
				    i in [1..#fprs]], pr[2] cat fprs[qr[1]] *] :
		      qr in Mp, pr in afplist  *];
	afplist:=afplistNew1 cat afplistNew2;
    end for;

    // for each a in avalues, generate all new values of a after applying monic
    // linear transformation
    alist:= monic(fieldKinfo,clist,primelist,avalues);

    afplistNew:=[* *];
    for aset in alist do
	a:= Integers()!aset`newa;
	for pr in afplist do
            af:=pr[1];
            assert GCD(Norm(af),a) eq 1;
            assert &and[Valuation(a,p) eq 0 : p in primelist];
	    invs:=normInv(a,OK); // generate all ideals of norm a
	    // for each aset and corresponding primelist, generate the ideal a
	    // and prime ideal list as in (3.8) of Gh
            afplistNew:= afplistNew cat [*[*aset,primelist,af*I,pr[2]*] : I in invs *];
        end for;
    end for;
    afplist:=afplistNew;

    // sanity checks
    for pr in afplist do
        a:=pr[1]`newa; // new_a value
	ideal_a:= pr[3];
        fplist:=pr[4];
        assert &and[InertiaDegree(fq)*RamificationDegree(fq) eq 1: fq in fplist];
        normlist:=[Norm(fq) : fq in fplist];
        assert #Set(normlist) eq #normlist; // verify prime ideals are coprime
        assert Set(normlist) subset Set(primelist); // verify prime ideals have correct norms
	assert IsDivisibleBy(Integers()!Norm(ideal_a),a);
	tt:= [Valuation(Norm(ideal_a), primelist[i]) : i in [1..#primelist]];
	assert Integers()!Norm(ideal_a) eq Abs(a)*&*[primelist[i]^tt[i] : i in [1..#primelist]];
        assert Set(PrimeDivisors(Integers()!Norm(ideal_a) div Integers()!a))
		  subset Set(primelist);
    end for;
	return afplist;
end function;

principalize:=function(fieldKinfo,ClK,ideal_a,fplist)

    /*
     Description: convert ideal equation (3.8), given by ideal_a, fplist, into S-unit		 equations (3.9) via procedure of Section 3.4.2 of Gh
     Input: fieldKinfo:= record of the field K = Q(th)
            ClK:= record of relevant class group info of the field K = Q(th)
            ideal_a:= the ideal as in (3.8) of Gh
            fplist:= list of prime ideals as in (3.8) of Gh
     Output: tf:= boolean value determining whether the ideal equation with ideal_a, fplist
                  has solutions, determind by whether [ideal_a]^{-1} is in the image of phi
                  if false, all other values return 0
             alpha:= principal ideal generator as in (3.9) of Gh
             gammalist:= list of principal ideal generators as in (3.9) of Gh
             matA:= nu x nu matrix as in Section 3.4.2 of Gh
             rr:= nu x 1 vector r as in Section 3.4.2 of Gh
     Example:
   */

    K:=fieldKinfo`field;
    OK:=fieldKinfo`ringofintegers;
    nu:=#fplist;
    assert nu ne 0;
    Zu:=FreeAbelianGroup(nu);

    phi:= hom< Zu -> ClK`classgroup | [ fp@@ClK`map : fp in fplist ]>;
    img:= Image(phi);
    if -ideal_a@@ClK`map in img then
        rr:=(-ideal_a@@ClK`map)@@phi;
        rr:=Eltseq(Zu!rr);
	// update vector r to have only positive entries, to avoid precision errors
        for i in [1..#rr] do
            while rr[i] lt 0 do
                rr[i]:= rr[i]+ClK`classnumber;
            end while;
        end for;
        ker:= Kernel(phi);
	// generate the list of vectors to comprise matrix A as in Section 3.4.2 of Gh
        A:=[Eltseq(Zu!a) : a in Generators(ker)];
        assert #A eq nu; // verify the kernel ker(phi) has rank nu
	// generate the matrix A
        matA:=Transpose(Matrix(Rationals(),A));
        assert AbsoluteValue(Determinant(matA)) eq #img;
	// generate the product ideal_a*ideal_tilde(p) as in Section 3.4.2 of Gh
	ideal_atildep:= ideal_a*&*[fplist[i]^rr[i] : i in [1..nu]];
	tf,alpha:=IsPrincipal(ideal_atildep); // generate principal ideal with generator alpha
        assert tf;

	// compute the ideals c_i as in Section 3.4.2 of Gh and their corresponding generators
        ideal_clist:=[ &*[fplist[i]^a[i] : i in [1..nu] ]  : a in A ];
        gammalist:=[];
        for fc in ideal_clist do
            tf, gamma:=IsPrincipal(fc);
            assert tf;
            Append(~gammalist,gamma);
        end for;
        tf, matAinv:= IsInvertible(matA);
        assert tf;
        return true, alpha, gammalist, matA, rr;
    else
        return false, 0, 0, 0, 0;
    end if;
end function;

prep2:=function(fieldKinfo,ClK,afplist)

    /*
     Description: iterate through each ideal equation (3.8) to generate all S-unit equations
     		  (3.9) of Gh
     Input: fieldKinfo:= record of the field K = Q(th)
            ClK:= record of relevant class group info of the field K = Q(th)
            afplist:= [aset,primelist,ideal_a,prime_ideal_list] where
                      ideal_a and prime_ideal_list are as in (3.8) of Gh
     Output: alphgamlist:= record of all S-unit equations corresponding to F(X,Y)
     Example:
   */

    K:= fieldKinfo`field;
    OK:=fieldKinfo`ringofintegers;

    // generate a record to store relevant S-unit equation info
    SUnitInfo:= recformat< primelist,newa,adu,alpha,gammalist,matA,vecR,ideallist,bound >;

    alphgamlist:=[ ];
    for pr in afplist do
	primelist:= pr[2];
        ideal_a:= pr[3];
        fplist:= pr[4];
	v:= #primelist;
        tf,alpha,gammalist,matA,rr:=principalize(fieldKinfo,ClK,ideal_a,fplist);
	if tf then
	    // sanity checks on exponents of alpha, ideal_a, and ideal generators gamma
            assert #gammalist eq #fplist;
            nu:= #fplist;
            Nm:= [Norm(fp) : fp in fplist];
            assert #Nm eq nu;
            assert &and[IsPrime(fp) : fp in Nm];
            rtest:= [];
            for i in [1..v] do
                p:= primelist[i];
                if p in Nm then
                    ind:= Index(Nm, p);
                    rtest[i]:= rr[ind];
                else
                    rtest[i]:= 0;
                end if;
            end for;
            tt:= [Valuation(Norm(ideal_a), primelist[i]) : i in [1..v]];
            zz:= [Valuation(Norm(ideal<OK|alpha>), primelist[i]) : i in [1..v]];
            assert [tt[i] + rtest[i] : i in [1..v]] eq zz;
            for i in [1..nu] do
                gamma:= gammalist[i];
                aa:= [Valuation(Norm(ideal<OK|gamma>), Nm[j]) : j in [1..nu]];
                assert aa eq Eltseq(ColumnSubmatrixRange(matA,i,i));
            end for;
	    temp:=rec<SUnitInfo|primelist:=primelist,newa:=pr[1]`newa,adu:=pr[1]`adu,
				alpha:=alpha,gammalist:=gammalist,matA:=matA,vecR:=rr,
				ideallist:=fplist>;
            Append(~alphgamlist,temp);
        end if;
    end for;
    return alphgamlist;
end function;

UpperBounds:=procedure(fieldKinfo,clist,~alphgamlist,complexPrec)

    /*
     Description: append upper bound on all S-unit equations as per Section 6.2 of Gh
     Input: fieldKinfo:= record of the field K = Q(th)
            clist:= [c_0, \dots, c_n], the coefficients of F(X,Y)
	    alphgamlist:= record of all S-unit equations corresponding to F(X,Y)
            complexPrec:= precision on complex field, C
     Output: alphgamlist[i]`bound:= upper bound on ith S-unit equation as per Section 6.2 of Gh
     Example:
   */

    c0:=Integers()!clist[1];
    assert c0 ne 0;
    n:=#clist-1;
    assert n ge 3;
    assert &and[c in Integers() : c in clist];
    Qx<x>:=PolynomialRing(Rationals());

    F:=&+[clist[i+1]*x^(n-i) : i in [0..n]];
    DiscF:= Discriminant(F);

    K:=fieldKinfo`field;
    OK:=fieldKinfo`ringofintegers;
    th:=fieldKinfo`gen;
    f:=fieldKinfo`minpoly;
    assert &and[ c in Integers() : c in Coefficients(f) ];
    assert IsMonic(f);
    assert (n eq Degree(f)) and (n eq Degree(NumberField(OK)));

    thetaC:= Conjugates(th);
    assert n eq #thetaC;
    CField<i>:= ComplexField(complexPrec);

    taus:=[hom< K -> CField | thetaC[i] > : i in [1..n]];
    // compute the Weil height of theta
    hth:= (1/n)*&+[Max((Log(Abs(taus[i](th)))), 0) : i in [1..n]];

    for i in [1..#alphgamlist] do
	a:= alphgamlist[i]`newa;
	primelist:=alphgamlist[i]`primelist;
        alpha:= alphgamlist[i]`alpha;
	NS:= &*[p : p in primelist];
	hpoly:= Max([Log(Abs(c)) : c in clist | c ne 0] cat [Log(Abs(a))]);
	m:= Integers()! (432*DiscF*a^2);
	if IsEmpty([p : p in PrimeDivisors(m) | p notin primelist]) then
	    mS:= 1728*NS^2;
	else
	    mS:= 1728*NS^2*(&*[p^(Min(2,Valuation(m,p))) :
			       p in PrimeDivisors(m) | p notin primelist]);
	end if;
	gam:= 2*hth + 2*Log(2) + 4*(2*mS*Log(mS) + 172*hpoly);
	halpha:= (1/n)*&+[Max((Log(Abs(taus[j](alpha)))), 0) : j in [1..n]];
        alphgamlist[i]`bound:= Ceiling(gam + 2*halpha);
    end for;
end procedure;



// for each Case, padic:

ImageInL:=function(mapsLL,elt);
    /*
    eltK:= an element in K or L
    This operation applies the ijk: L -> L maps to the element in K or L, elt
    */

    ImageUnderMap:= [];
    for i in [1..#mapsLL] do
        ImageUnderMap[i]:= [];
        for j in [1..#mapsLL[i]] do
            ImageUnderMap[i][j]:= mapsLL[i][j](elt);
        end for;
    end for;

    return ImageUnderMap;
end function;


pAdicLog:=function(elt,p);
    // DETAILS TO ADD
    //Input: p = rational prime, x = p-adic unit belonging to a finite extension of Q_p
    //output: the p-adic logarithm of x

    e:=AbsoluteRamificationIndex(Parent(elt));
    f:=AbsoluteInertiaDegree(Parent(elt));
    r:=1;
    for o in Divisors(p^f - 1) do
        if Valuation(elt^o - 1) gt 0 then
            r:=o;
            break;
        end if;
    end for;
    k:=1;
    while p^k le e do
        k:= k+1;
    end while;
    return Log( elt^(r*p^k) )/(r*p^k);
end function;



Ellipsoid:= function(fieldKinfo,fieldLinfo,Case,i0jjkk,AutL,mapsLL,HeightBounds,RealPrec);

    // will need this later for real case too

    K:= fieldKinfo`field;
    OK:= fieldKinfo`ringofintegers;
    th:= fieldKinfo`gen;
    zeta:= fieldKinfo`zeta;
    epslist:= fieldKinfo`fundamentalunits;
    L:= fieldLinfo`field;
    OL:= fieldLinfo`ringofintegers;

    CasePrimes:= [Norm(fp) : fp in Case`ideallist];
    gammalist:= Case`gammalist;
    fplist:= Case`ideallist;
    alpha:= Case`alpha;
    matA:= Case`matA;

    i0:= i0jjkk[1];
    jj:= i0jjkk[2];
    kk:= i0jjkk[3];

    tau:= alpha*zeta;
    nu:= #gammalist;
    r:= #epslist;
    assert #CasePrimes eq nu;

    HeightBoundonGammalist:= HeightBounds`heightgammalist;
    HeightBoundonEpslist:= HeightBounds`heightepslist;

    // choose i0jk, mapsLL
    // generate images under the maps ijk: L-> L, th -> theta[i][j]
    tauL:=ImageInL(mapsLL,L!tau);
    gammalistL:= [ImageInL(mapsLL,L!gamma) : gamma in gammalist];
    epslistL:= [ImageInL(mapsLL,L!eps) : eps in epslist];

    RField:= RealField(RealPrec);
    SetDefaultRealField(RField);

    // verify that the prime ideals in L above gamma do not cancel
    for i in [1..nu] do
        faci0:= Factorization(ideal<OL|gammalistL[i][i0[1]][i0[2]]>);
        facjj:= Factorization(ideal<OL|gammalistL[i][jj[1]][jj[2]]>);
        fackk:= Factorization(ideal<OL|gammalistL[i][kk[1]][kk[2]]>);
        assert (#faci0 eq #facjj) and (#facjj eq #fackk);
        assert &and[faci0[j][1] ne facjj[j][1] : j in [1..#faci0]];
        assert &and[facjj[j][1] ne fackk[j][1] : j in [1..#faci0]];
        assert &and[faci0[j][1] ne fackk[j][1] : j in [1..#faci0]];
    end for;

    CField<i>:= ComplexField(RealPrec);
    LintoC:= hom< L -> CField | Conjugates(L.1)[1] >;

    // compute i1, i2: L- > C to generate matrix R
    for i1 in [1..#AutL] do
        for i2 in [i1 + 1..#AutL] do
            a:= (AutL[i1])(epslistL[1][jj[1]][jj[2]]/epslistL[1][i0[1]][i0[2]]);
            a:= RField!(Log(Abs(LintoC(a))));

            b:= (AutL[i1])(epslistL[2][jj[1]][jj[2]]/epslistL[2][i0[1]][i0[2]]);
            b:= Log(Abs(LintoC(b)));

            c:= (AutL[i2])(epslistL[1][jj[1]][jj[2]]/epslistL[1][i0[1]][i0[2]]);
            c:= Log(Abs(LintoC(c)));

            d:= (AutL[i2])(epslistL[2][jj[1]][jj[2]]/epslistL[2][i0[1]][i0[2]]);
            d:= Log(Abs(LintoC(d)));
            if (a*d - b*c) ne 0 then
                iotalist:= [i1,i2];
                break i1;
            end if;
        end for;
    end for;

    matR:= Matrix(ComplexField(RealPrec),2,2,[a,b,c,d]);
    tR, matRinv:= IsInvertible(matR);
    tA, matAinv:= IsInvertible(matA);
    assert tR and tA;
    i1:= iotalist[1];
    i2:= iotalist[2];

    // compute iota 1 gammas and iota 2 in definition of wgamlklist
    logamlistLi1:= [ Log(Abs(LintoC( (AutL[i1])(gammalistL[k][jj[1]][jj[2]]/gammalistL[k][i0[1]][i0[2]]) ))) : k in [1..nu]];
    logamlistLi2:= [ Log(Abs(LintoC( (AutL[i2])(gammalistL[k][jj[1]][jj[2]]/gammalistL[k][i0[1]][i0[2]]) ))) : k in [1..nu]];

    // compute the coefficients w_{gam,l,k} in the bound for Beps
    wgamlklist:= [];
    for l in [1..r] do
        wgamlklist[l]:= [];
        for k in [1..nu] do
            alphagamlk:= matRinv[l,1]*(&+[matAinv[i][k]*logamlistLi1[i] : i in [1..nu]]);
            alphagamlk:= alphagamlk + matRinv[l,2]*(&+[matAinv[i][k]*logamlistLi2[i] : i in [1..nu]]);
            wgamlklist[l][k]:= Abs(alphagamlk)*Degree(K, Rationals())/Log(CasePrimes[k]);
        end for;
    end for;

    // compute the coefficients w_{eps,l,k} in the bound for Beps
    wepslklist:= [];
    for l in [1..r] do
        wepslklist[l]:= [];
        m:= Max(Abs(matRinv[l,1]), Abs(matRinv[l,2]));
        for i in [1..#AutL] do
            if i eq i1 then
                wepslklist[l][i]:= (m+Abs(matRinv[l,1]))*(Degree(L, Rationals()));
            elif i eq i2 then
                wepslklist[l][i]:= (m+Abs(matRinv[l,2]))*(Degree(L, Rationals()));
            else
                wepslklist[l][i]:= m*(Degree(L, Rationals()));
            end if;
        end for;
    end for;

    Bgam:= Ceiling((1/Log(2)^2)*&+[ h^2 : h in HeightBoundonGammalist]);

    // compute bound b_eps; since r = 2, there is only 1 such b_eps where eps =! eps^*
        // choose eps^* = epslist[2]; hence l = 1 here
    Beps:= [];
    for l in [1..r] do
        Beps[l]:= ((1/Degree(K,Rationals()))*&+[HeightBoundonGammalist[k]*wgamlklist[l][k] : k in [1..nu]]);
        Beps[l]:= (Beps[l] + (1/Degree(L,Rationals()))*&+[HeightBoundonEpslist[k]*wepslklist[l][k] : k in [1..#AutL]])^2;
    end for;

    matD:= DiagonalMatrix(Integers(), [ Floor(Log(p)^2/Log(2)^2) : p in CasePrimes]);
    matM:= IdentityMatrix(Integers(),nu+r);
    InsertBlock(~matM, (&*[Ceiling(Beps[l]) : l in [1..r]])*(Transpose(matA)*matD*matA), 1, 1);
    for l in [1..r] do
        matM[nu+l,nu+l]:= Bgam*(&*[Ceiling(Beps[k]) : k in [1..r] | k ne l]);
    end for;

    return matM,Bgam,Beps;
end function;



pLatticePrep:=procedure(fieldKinfo,fieldLinfo,Case,~localpinfo,ijkL,AutL,HeightBounds,Prec : UseSmallBound:=true);
    /*
    INPUT:
        primelist
        L
    OUTPUT:
       // for each prime p[l], stores theta[l][i][j]:= theta_i^{(j)}, tje associated roots of g in the completion of Q_{p[l]}
        // ie. for i in {1,...,m[l]}, theta[l][i] satisfies gp[l][i](theta[l][i]) = 0; ie g_i(theta_i) = 0
        // theta[l][i][1], ..., theta[l][i][n_i]:= theta_i^{(1)}, ..., theta_i^{(n_i)} for p[l] are the conjugates of theta[l][i]
    */

    pAdicPrec:= Prec[1];
    RealPrec:= Prec[2];

    K:= fieldKinfo`field;
    OK:= fieldKinfo`ringofintegers;
    th:= fieldKinfo`gen;
    f:= fieldKinfo`minpoly;
    L:= fieldLinfo`field;
    OL:= fieldLinfo`ringofintegers;
    zeta:= fieldKinfo`zeta;
    epslist:= fieldKinfo`fundamentalunits;
    n:= Degree(K);

    p:= localpinfo`prime;
    Lp:= localpinfo`Lp;
    mapLLp:= localpinfo`mapLLp;
    //fprsL:= localpinfo`idealinL;

    gammalist:= Case`gammalist;
    fplist:= Case`ideallist;
    alpha:= Case`alpha;
    nu:= #gammalist;
    r:= #epslist;

    //Lp, mapLLp:= Completion(L, fprsL : Precision:=pAdicPrec);
    fprs:=[f[1] : f in Factorisation(p*OK)];        // the prime ideals above p

    thetaL:=[];
    mapsLL:=[];
    for i in [1..#fprs] do      // runs through each prime ideal above p
        thetaL[i]:=[];
        mapsLL[i]:=[];       // the preimage of thetap in L
                                    // ie. for th in L, mLp(ijk(th)) is one of the thetap in Lp
        Kp, mKp:= Completion(K,fprs[i] : Precision:=pAdicPrec);
        gp_i:= MinimalPolynomial( mKp(th), PrimeField(Kp));
        temp:= Roots(gp_i, Lp);   // #temp = degree of gp_i = e_i*f_i
        for j in [1..#temp] do
            vals, ind:= Max([Valuation(mapLLp(ijkL[k](L!th)) - temp[j][1]) : k in [1..3]]);
            mapsLL[i][j]:= ijkL[ind];        // mLp(ijk[i][j](th)) maps to thetap[i][j]
            thetaL[i][j]:= ijkL[ind](L!th);
        end for;
    end for;

    assert n eq &+[#thetaL[i] : i in [1..#fprs]];       // check we have the correct number of thetas
    Lpt:=ChangePrecision(Lp,Min([Precision(mapLLp(thetaL[i][j])) : j in [1..#thetaL[i]], i in [1..#thetaL]]));
    check:= [Precision(mapLLp(thetaL[i][j])) : j in [1..#thetaL[i]], i in [1..#thetaL]];
    // verify that thetap[i][j] are roots of f
    assert &and[Lpt!0 eq (Lpt!0 - Evaluate(f,mapLLp(thetaL[i][j]))) : j in [1..#thetaL[i]], i in [1..#thetaL]];
    // verify the precision has not been changed by the above test
    assert [Precision(mapLLp(thetaL[i][j])) : j in [1..#thetaL[i]], i in [1..#thetaL]] eq check;
    // verify the thetap[i][j] are the same roots as would be obtained by sending th in L into Lp
        // Note: this correspondence will not generate the roots in the correct order
        // This is due to the fact that we cannot work in the algebraic closure of Qp, but only in one Lp
        // ideally, we would be working in each Lp above each prime ideal over p in K,
        // but Magma does not allow this

    assert (#thetaL eq 2) or (#thetaL eq 3);
    inds:= [];  // stores the indices of the unbounded primes in fplist
    // verifies there is a prime ideal above p in fplist
    assert &or[fq in fplist : fq in fprs];
    for i in [1..#fplist] do
        fp:= fplist[i];
        for j in [1..#fprs] do
            fq:= fprs[j];
            if fq eq fp then
    // index of prime ideal above p appearing in fplist
                Append(~inds, j);
            end if;
        end for;
    end for;
    assert #inds eq 1;  // this is i0
    i0:=[inds[1],1];    // root of g_inds(t), first (and only) element
    // verifies the unbounded ideal corresponds to deg(gp) = 1
    assert #thetaL[i0[1]] eq 1;
    assert fprs[i0[1]] in fplist;

    // chooses j,k where g(t) = g_1(t)g_2(t), deg(g_1) = 1, deg(g_2) = 2
    indjk:= [i : i in [1..#thetaL] | i ne inds[1]];
    if #thetaL eq 2 then
        assert #indjk eq 1;
        assert #thetaL[indjk[1]] eq 2;
        jj:= [indjk[1],1];
        kk:= [indjk[1],2];
    elif #thetaL eq 3 then
        assert (#thetaL[indjk[1]] eq 1) and (#thetaL[indjk[2]] eq 1);
        assert #indjk eq 2;
        jj:= [indjk[1],1];
        kk:= [indjk[2],1];
    end if;

    assert thetaL[jj[1]][jj[2]] ne thetaL[kk[1]][kk[2]];
    tau:=alpha*zeta;

    // generate images under the maps ijk: L-> L, th -> theta[i][j]
    tauL:=ImageInL(mapsLL,L!tau);
    gammalistL:= [ImageInL(mapsLL,L!gamma) : gamma in gammalist];
    epslistL:= [ImageInL(mapsLL,L!eps) : eps in epslist];

    // verify that the prime ideals in L above gamma do not cancel
    for i in [1..nu] do
        faci0:= Factorization(ideal<OL|gammalistL[i][i0[1]][i0[2]]>);
        facjj:= Factorization(ideal<OL|gammalistL[i][jj[1]][jj[2]]>);
        fackk:= Factorization(ideal<OL|gammalistL[i][kk[1]][kk[2]]>);
        assert (#faci0 eq #facjj) and (#facjj eq #fackk);
        assert &and[faci0[j][1] ne facjj[j][1] : j in [1..#faci0]];
        assert &and[facjj[j][1] ne fackk[j][1] : j in [1..#faci0]];
        assert &and[faci0[j][1] ne fackk[j][1] : j in [1..#faci0]];
    end for;

    // check if we can bound Nail early (Lemma 6.5)
    delta1L:=(thetaL[i0[1]][i0[2]] - thetaL[jj[1]][jj[2]])/(thetaL[i0[1]][i0[2]] - thetaL[kk[1]][kk[2]]);
    delta1L:=delta1L*(tauL[kk[1]][kk[2]]/tauL[jj[1]][jj[2]]);
    delta2L:=(thetaL[jj[1]][jj[2]] - thetaL[kk[1]][kk[2]])/(thetaL[kk[1]][kk[2]] - thetaL[i0[1]][i0[2]]);
    delta2L:=delta2L*(tauL[i0[1]][i0[2]]/tauL[jj[1]][jj[2]]);

    if (Valuation(mapLLp(delta1L)) ne 0) then
        smallbound:= Min[Valuation(mapLLp(delta1L)),0] - Valuation(mapLLp(delta2L));
        if smallbound ge 0 then
            localpinfo`smallbound:= smallbound;
        else
            localpinfo`smallbound:= -1;     // negative bound; Case can be removed
        end if;
    else
        Logdelta1:= pAdicLog(mapLLp(delta1L),p);
        Loggammalist:=[pAdicLog(mapLLp(gammalistL[i][kk[1]][kk[2]]/gammalistL[i][jj[1]][jj[2]]), p) : i in [1..nu]];
        Logepslist:=[pAdicLog(mapLLp(epslistL[i][kk[1]][kk[2]]/epslistL[i][jj[1]][jj[2]]), p) : i in [1..r]];
        LogList:= Loggammalist cat Logepslist;
        assert #LogList eq (nu+r);

        minval,ihat:= Min([Valuation(LogList[i]) :i in [1..nu+r]]);

        if Valuation(Logdelta1) lt minval then
            smallbound:= Max([Floor((1/(p-1) - Valuation(mapLLp(delta2L)))),Ceiling(minval - Valuation(mapLLp(delta2L)))-1]);
            if smallbound ge 0 then
                localpinfo`smallbound:= smallbound;
            else
                localpinfo`smallbound:= -1;     // negative bound; Case can be removed
            end if;
    // if the program makes it this far, there are no small bounds on Nail
    // arising from Lemma 6.5 and Lemma 6.9
    // hence the code must enter the FP process to reduce the bounds
    // generates the linear forms in p-adic logs elements for the Special Case
        else
            logihat:= LogList[ihat];  // offset the first term, Logdelta1
            betalist:= [-LogList[i]/logihat : i in [1..nu+r]];
            // assert that we are indeed in the special case, where neither lemma can immediately reduce the bound
            beta1:= -Logdelta1/logihat;
            assert &and[beta in pAdicRing(p) : beta in betalist] and (beta1 in pAdicRing(p));

            localpinfo`ihat:= ihat;
            localpinfo`logihat:= logihat;
            localpinfo`delta1inQp:= mapLLp(delta1L);
            localpinfo`delta2inQp:= mapLLp(delta2L);
            localpinfo`betalist:= [*beta1,betalist*];

            matM,Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,Case,[i0,jj,kk],AutL,mapsLL,HeightBounds,RealPrec);
            localpinfo`ellipsoid:= matM;
            localpinfo`bgam:= Bgam;
            localpinfo`bepslist:= BepsList;
        end if;
    end if;
end procedure;


pInteger:= function(Lp,p,mu,pAdicPrec,elt);
    /* thought i didn't need this. I definitely do

    // see spiel about magmas completion function
    // may need to verify this
    end if;*/
    coeffs:=Coefficients(elt);
    Ainv:=1;
    LpT:=5;
    d1:=Degree(Lp,CoefficientField(Lp));
    d2:=Degree(CoefficientField(Lp),PrimeField(Lp));
    d3:=Degree(Lp,PrimeField(Lp));   // NB, d3:= d1*d2;
    if AbsoluteRamificationIndex(Lp) eq 1 then
        LpT:=1;
        //u:=(1/2)*Valuation(Discriminant(DefiningPolynomial(Lp)));
        assert Valuation(Lp.1) ge 0;
    end if;
    if AbsoluteInertiaDegree(Lp) eq 1 then
        LpT:=2;
        //u:=(1/2)*Valuation(Discriminant(DefiningPolynomial(Lp)));
        assert Valuation(Lp.1) ge 0;
    end if;
    if (AbsoluteInertiaDegree(Lp) gt 1) and (d1 eq 1) then
        LpT:=3;
        //u:=(1/2)*Valuation(Discriminant(DefiningPolynomial(CoefficientField(Lp))));
        assert Valuation(CoefficientField(Lp).1) ge 0;
        coeffs:=Coefficients(Coefficient(elt,1));
    end if;
    if (d1 gt 1) and (d2 gt 1) then
        LpT:= 4;
        k:=1;
        gen:= k*Lp.1 + (Lp ! CoefficientField(Lp).1);
        while (Degree(MinimalPolynomial(gen,PrimeField(Lp))) ne d3) do
            k:= k+1;
            gen:= k*Lp.1 + (Lp ! CoefficientField(Lp).1);
        end while;
        //u:= (1/2)*Valuation(Discriminant(MinimalPolynomial(gen,PrimeField(Lp))));
        assert Valuation(gen) ge 0;
        AA:=ZeroMatrix( PrimeField(Lp), d3, d3);
        temp1:=Coefficients(gen);
        temp2:=Coefficients(temp1[1]);
        for k in [1..d3] do
            temp1:=Coefficients(gen^(k-1));
            for i in [1..d1] do
                temp2:=Coefficients(temp1[i]);
                for j in [1..d2] do
                    AA[(i-1)*d2 + j,k]:=temp2[j];
                end for;
            end for;
        end for;
        Ainv:=AA^(-1);
        B:=ZeroMatrix( PrimeField(Lp), d3, 1);
        temp1:=Coefficients(elt);
        temp2:=Coefficients(temp1[1]);
        for i in [1..d1] do
            temp2:=Coefficients(temp1[i]);
            for j in [1..d2] do
                B[(i-1)*d2 + j,1]:=temp2[j];
            end for;
        end for;
        C:=Ainv*B;
        coeffs:=[C[i][1] : i in [1..d3]];
    end if;
    assert LpT ne 5;
    assert #coeffs eq AbsoluteDegree(Lp);

    /*
    Input: m = positive integer, p a prime
    x = an element in the p-adic field Q_{p} that belongs to the subring Z_{p} (the ring of p-adic integers in Q_{p}).
    Output: The unique integer x^{m} in [0,p^m - 1] with ord_{p}(x - x^{m}) >= m
    */
    y:=pAdicRing(p : Precision:=pAdicPrec) ! coeffs[1];
    y:=pAdicQuotientRing(p, mu) ! y;

    y:=IntegerRing() ! y;
    if y lt 0 then
        y:=y+p^(mu);
    end if;

    return y;
end function;


pLattice:= function(fieldLinfo,localpinfo,pAdicPrec,mu);

    p:= localpinfo`prime;
    Lp:= localpinfo`Lp;
    beta1:= localpinfo`betalist[1];
    betalist:= localpinfo`betalist[2];
    ihat:= localpinfo`ihat;
    matM:= localpinfo`ellipsoid;
    Bgam:= localpinfo`bgam;
    Bepslist:= localpinfo`bepslist;
    nuplusr:= #betalist;
    r:= #Bepslist;

    //assert &and[mu le Precision(beta) : be
    betalist:= [pInteger(Lp,p,mu,pAdicPrec,beta) : beta in betalist];
    // asserts that beta_ihat = -alpha_ihat/alpha_ihat = -1
    assert (betalist[ihat] eq (p^mu)-1);

    betalist[ihat]:= p^mu;
    beta1:= pInteger(Lp,p,mu,pAdicPrec,beta1);

    // define matrix
    matAm:= IdentityMatrix(Rationals(), (nuplusr));
    for i in [1..nuplusr] do
        matAm[ihat,i]:= betalist[i];
    end for;
    assert matAm[ihat,ihat] eq p^mu;

    // generates Transpose(matB)*matB
    matBtmatB:= Transpose(matAm)*matM*matAm;

    vecc:= ZeroMatrix(Rationals(), nuplusr, 1);
    vecc[ihat,1]:= -beta1/p^mu;
    boundForNormSquared:= Ceiling((1+r)*(Bgam*&*Bepslist));

    return matBtmatB, vecc, boundForNormSquared;

end function;



IsZeroLocal:=function(elt,S);
    /* DONT THINK I NEED THIS EITHER

    /*if Valuation(x) ge Valuation(Zero(Parent(x))) - 2*(AbsoluteDegree(Parent(x))-1) then
    return true;
    else
    return false;
    end if;*/
    if Valuation(elt) ge Valuation(Zero(Parent(elt))) - 2*(S-1) then
        return true;
    else
        return false;
    end if;
end function;


My_QuadraticForm:= function(matA);
    n:= NumberOfColumns(matA);     // computes the size of A
    matQ:= ZeroMatrix(RationalField(),n,n);
    for i in [1..n] do
        for j in [i..n] do
            s:= 0;
            for k in [1..i-1] do
                s:= s + matQ[k,i]*matQ[k,j]*matQ[k,k];
            end for;
            matQ[i,j]:= matA[i,j] - s;
            if i ne j then
                matQ[i,j]:= matQ[i,j]/matQ[i,i];
            end if;
        end for;
    end for;
    return matQ;
end function;


My_FinckePohst:= function(matA,boundForNormSquared: center:=0,maxNumSolutions:=-1,lllReduce:=true,breakSymmetry:=true);

    //forward traverseShortVectors;
    procedure traverseShortVectors(Q,n,i,~x,center,~shortVectors,RemainingBoundForNormSquared,~numSolutions, maxNumSolutions,finalTransformation, xIsCenterSoFar,~stillEnumerating)


//        print "k,xIsCenterSoFar", i,xIsCenterSoFar;
//        print "===============";
//        print "start:,k,x ",i,x;
        if i eq 0 then
            if maxNumSolutions ne -1 and numSolutions ge maxNumSolutions then
                stillEnumerating:= false; //return false,x,shortVectors,Ts,numSolutions,xIsCenterSoFar;
            else
                numSolutions:= numSolutions + 1;
                y:= Transpose(finalTransformation*Transpose(x));
                Append(~shortVectors, y);
                //print "y = ", y;
                //print "Short Vectors = ", shortVectors;
                stillEnumerating:= true; //return true,x,shortVectors,Ts,numSolutions,xIsCenterSoFar;
            end if;
        else
            stillEnumerating:= true;
            updatingEntries:= true;
            //print "pre-center:,k", center, i;
            u:= -center[1,i];
            for j in [i+1..n] do
                u:= u + Q[i,j]*(x[1,j] - center[1,j]);
            end for;
            uCeil:= Ceiling(u);
            uFloor:= Floor(u);
//            print "-------------------";
//            print "Floor Ceil", -uFloor, -uCeil;
//            print "Floor Ceil", Floor(Sqrt(20/Q[i,i]) - u), Ceiling(-Sqrt(20/Q[i,i]) - u);
//            print "-------------------";

            xk0_up:= -uFloor;
            xk0_down:= -uCeil;
            //print "pose-center:,x,k,u,Q", x,i,u,Q, uFloor, uCeil;

            x[1,i]:= xk0_down;
            while updatingEntries do
                //print "preBOUND1:ONE k,x,u ",i,x,u;
                t:= Q[i,i]*(x[1,i]+u)^2;
                //print "t1 =", RealField()!t;
                //print "BOUND1", RemainingBoundForNormSquared; // last element
                if t gt RemainingBoundForNormSquared then
                   // print "prebreak1:ONE k,x,t,u ",i,x,t, u;
                    if x[1,i] ge xk0_up then
                     //   print "break1";
                        updatingEntries:= false;
                        break;
                    end if;
                    x[1,i]:= x[1,i] + 1;
                    continue;
                end if;
               // print "ONE k,x,t,u ",i,x,t, u;

                $$(Q,n,i-1,~x,center,~shortVectors,RemainingBoundForNormSquared-t,~numSolutions,maxNumSolutions,finalTransformation,xIsCenterSoFar and x[1,i] eq center[1,i],~stillEnumerating);
                if stillEnumerating eq false then

                 //   print "ohno!";
                    updatingEntries:= false;
                    break;

                end if;
                x[1,i]:= x[1,i] + 1;
                //print "end of loop1:", x;
            end while;

//            print "switch";
//    //        print "MID k,x,t,u", i, x, t, u;
//    //        print "MID BOUND", RemainingBoundForNormSquared; // last element
//            print "stillEnumerating, xisCenter", stillEnumerating, xIsCenterSoFar;
//            print "=======================";

            if (xIsCenterSoFar eq false) and (stillEnumerating eq true) then
                x[1,i]:= xk0_down-1;
                updatingEntries:= true;
                while updatingEntries do
                    t:= Q[i,i]*(x[1,i]+u)^2;
    //                print "t2 =", RealField()!t;
    //                print "BOUND2", RemainingBoundForNormSquared; // last element
                    if t gt RemainingBoundForNormSquared then
                        //print "break2";
                        updatingEntries:= false;
                        break;
                    end if;
                    //print "TWO k,x,t,u ",i,x,t, u;
                    $$(Q,n,i-1,~x,center,~shortVectors,RemainingBoundForNormSquared-t,~numSolutions,maxNumSolutions,finalTransformation,false,~stillEnumerating);
                    if stillEnumerating eq false then
                    //if tf eq false then
                      //  print "ohno!";
                        updatingEntries:= false;
                        break;
                        //return false, x,shortVectors,RemainingBoundForNormSquared,numSolutions,xIsCenterSoFar;
                    end if;
                    x[1,i]:= x[1,i] - 1;
                end while;
            end if;
        //return true, x,shortVectors,Ts,numSolutions,xIsCenterSoFar;
        end if;

    end procedure;

    n:= NumberOfColumns(matA);     // computes dimension of square input matrix A
    assert IsSymmetric(matA);
    assert IsPositiveDefinite(matA);

    if IsZero(center) then
        center:= ZeroMatrix(Integers(), n, 1);
    end if;
    assert (BaseRing(center) eq Integers()) or (BaseRing(center) eq Rationals());

    if NumberOfColumns(center) ne n then
        center:= Transpose(center);
    end if;
    assert (NumberOfColumns(center) eq n) and (NumberOfRows(center) eq 1);

    if &and[center[1,i] notin Integers() : i in [1..n]] then
        breakSymmetry:= false;  //#We check this here, as after multiplication with U, center.base_ring() might become QQ! (even though U's base_ring is ZZ as well...)
    end if;

    if lllReduce then
        matG,matU,n:= LLLGram(matA);
        assert n eq NumberOfColumns(matG);
        assert matG eq matU*matA*Transpose(matU);
        if BaseRing(center) eq Rationals() then
            matU:= ChangeRing(Transpose(matU), Rationals());
        else
            matU:= Transpose(matU);
        end if;
        tf,matUinv:= IsInvertible(matU);
        assert tf;
        finalTransformation:= matU;
        if not IsZero(center) then
            center:= Transpose(matUinv*Transpose(center));
        end if;
    end if;

    assert (NumberOfColumns(center) eq n) and (NumberOfRows(center) eq 1);
    assert IsSymmetric(matG);
    assert IsPositiveDefinite(matG);

    Q:= My_QuadraticForm(matG);
    x:= ZeroMatrix(Rationals(),1,n);

    stillEnumerating:= true;
    solutionsList:= []; // stores short vectors
    numSolutions:= 0;
    finalTransformation:= ChangeRing(finalTransformation, Rationals());

    traverseShortVectors(Q,n,n,~x,center,~solutionsList,boundForNormSquared, ~numSolutions, maxNumSolutions,finalTransformation,breakSymmetry, ~stillEnumerating); //stillEnumerating);
    bufferWasBigEnough:= stillEnumerating;
    assert #solutionsList eq numSolutions;
    assert (maxNumSolutions eq -1) or (#solutionsList le maxNumSolutions);

    return bufferWasBigEnough, solutionsList;
end function;


//Gamma:= Matrix(Integers(),4,4,[1,5,3,4,3,1,2,3,4,1,2,3,4,5,6,7]);
//print "Gamma:";
//print Gamma;

////The associated Gram matrix:
//matA:= Transpose(Gamma)*Gamma;
//print "A:";
//print matA;

//center:= Matrix(Rationals(),4,1,[0,0,0,6/7]);
//print "center of ellipsoid:",center;

//boundForNormSquared:= 2;
//maxNumSolutions:= 100;
//bufferWasBigEnough, solutionsList:= My_FinckePohst(matA,boundForNormSquared:center:=center, maxNumSolutions:=-1,lllReduce:=true, breakSymmetry:= true);






// test:
clist:= [1,-23,5,24];
primelist:= [2,3,5,7];
a:= 1;

clist:= [1,23,17,2];    // something weird about algs1and2
primelist:= [7,41];
a:= 1;

clist:= [1,7,23,-25];   // gives an error in principalize; r = 1
primelist:= [2,3,7,37,53];
a:= 1;

clist:= [1,17,23,-27];
primelist:= [2,3,7,37,53];
a:= 1;

clist:= [1,17,23,-27];
primelist:= [1987,1999];
a:= 1;




    /////
    //To DO: temp!
        // pprecs:= padicprecision(primelist, L);      // estimated required precision
        // precision calculations
    /////
    // generate a record to store relevant p-adic field info

    pAdicPrec:= 400;
    RealPrec:= 100;
    ComplexPrec:= 100;
    // compute the initial height bound: change me







    // begin cycling through cases
    CaseNo:= 1;
    for Case in alphgamlist do
//Case:= alphgamlist[1];

        CasePrimes:= [Norm(fp) : fp in Case`ideallist];
        nu:= #Case`gammalist;
        assert #CasePrimes eq nu;
        assert &and[p in primelist : p in CasePrimes];
        printf "-"^(80) cat "\n";
        printf "Case: %o\n", CaseNo;
        printf "Initial height bound: %o\n", Case`bound;

        HeightBoundInfo:= recformat<heightgammalist,heightepslist>;
        HeightBounds:= rec<HeightBoundInfo | heightgammalist:= [Case`bound : i in [1..nu]],heightepslist:= [Case`bound : i in [1..#AutL]]>;

         //pprecs:= padicprecision(primelist, L);      // estimated required precision
        // generate a record to store relevant local info

// padic:
    pCaseInfo:= recformat<prime,Lp,mapLLp,smallbound,delta1inQp,delta2inQp,ihat,logihat,betalist,ellipsoid,bgam,bepslist>;
    //printf "Computing all roots of f in Cp...";
        t3:= Cputime();
    localpinfoList:= [];


UseSmallBound:= false;  // still to include
pAdicPrec:= 400;
RealPrec:= 100;

// run through all possible combos of embeddings

Prec:= [pAdicPrec,RealPrec];
    for i in [1..nu] do
        p:= CasePrimes[i];
        idealinL:= (Factorisation(p*OL))[1][1];
        Lp, mapLLp:= Completion(L, idealinL : Precision:=pAdicPrec);

        localpinfoList[i]:=rec< pCaseInfo | prime:= p, Lp:= Lp, mapLLp:= mapLLp>;


        // compute thetas, relevant maps for each prime in the TM equation
        pLatticePrep(fieldKinfo,fieldLinfo,Case,~localpinfoList[i],ijkL,AutL,HeightBounds,Prec : UseSmallBound);

        if (assigned localpinfoList[i]`smallbound) and (UseSmallBound eq true) then
            // reduce equation to move alpha into other cases
            // should check if now, we are in one of the other cases
            // ie shuffle throught the other cases to see if there is a match
        end if;
        delta1:= localpinfoList[i]`delta1inQp;
        delta2:= localpinfoList[i]`delta2inQp;
        logihat:= localpinfoList[i]`logihat;

        lv:= 200;
        cp:= Log(p)*(Max(1/(p-1),Valuation(delta1)) - Valuation(delta2));
        assert lv ge cp;
        assert HeightBounds`heightgammalist[i] gt Max(0,cp);

        mu:= Floor(lv/Log(p) - Valuation(logihat) + Valuation(delta2));

        print "mu:", mu;
        //print "mu/Case`bound", RealField()!(mu/Case`bound);
        matBtmatB, vecc, boundForNormSquared:= pLattice(fieldLinfo,localpinfoList[i],pAdicPrec,mu);

        boundForNormSquared;
        bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=100,lllReduce:=true, breakSymmetry:= true);
        #solutionsList;


    end for;
    printf "Done! Duration: %o\n", Cputime(t3);

end for;


// Real


t0:= Cputime();
// generate relevant files
LogFile:= "/home/adela/ThueMahler/Data/SUnitEqData/SUnitEqLogs.txt";
SUnitEq:= "/home/adela/ThueMahler/Data/SUnitEqData/AllSUnitEq.txt";

SetLogFile(LogFile);
SetAutoColumns(false);
SetColumns(235);

// convert bash input into magma integers, sets
N:= [];
i:= 2;
while set[i] ne "," do
    Append(~N, set[i]);
    i:= i+1;
end while;
N:= StringToInteger(&cat(N)); // convert bash input N into an integer

// determine indices of ",", "[", "]" from bash input
brackets:= []; // store indices of seperating brackets of clist
commas:= []; // store indices of seperating commas in S
i:= i+1;
assert set[i] eq "[";
Append(~brackets,i);
while set[i] ne "]" do
    if set[i] eq "," then
	Append(~commas, i);
    end if;
    i:= i + 1;
end while;
assert set[i] eq "]";
assert #commas eq 4;
Append(~brackets,i);

// convert bash symbols of clist into integers
DiscF:= 4*StringToInteger(&cat[set[i] : i in [brackets[1]+1..commas[1]-1]]);
clist:=[];
for j in [1..#commas-1] do
    n:= [set[i] : i in [(commas[j]+1)..(commas[j+1]-1)]];
    Append(~clist,StringToInteger(&cat(n)));
end for;
Append(~clist,StringToInteger(&cat[set[i] : i in [commas[4]+1..brackets[2]-1]]));

hash:= set;

printf hash cat " Resolving Thue-Mahler equation with...\n";
printf hash cat " Coefficients: %o, Conductor: %o \n", clist, N;

t1:= Cputime();
f, enterTM, TMSolutions, RemainingCases:= prep0(hash,LogFile,clist,N);
printf hash cat " Total time to determine local obstructions: %o \n", Cputime(t1);

// assert TM forms with no S-unit equations to resolve are removed !!!!!!!!!
assert enterTM;
// generate a record to store relevant info of the field K = Q(th)
FieldInfo:= recformat<field,gen,ringofintegers,minpoly,zeta,fundamentalunits>;
K<th>:=NumberField(f);
OK:=MaximalOrder(K);
th:=OK!th;
fieldKinfo:= rec<FieldInfo | field:= K,gen:= th,ringofintegers:= OK,minpoly:= f>;

// generate a record to store relevant info of the splitting field L of K = Q(th)
L, tl:= SplittingField(f);
t2:= Cputime();
OL:= MaximalOrder(L);
printf hash cat " Total time to compute the ring of integers of L: %o \n", Cputime(t2);
tf,mapKL:= IsSubfield(K,L);
assert tf;
assert (L!th eq mapKL(th)) and (mapKL(th) in tl);
fieldLinfo:= rec<FieldInfo | field:= L, gen:=tl,ringofintegers:= OL>;

// generate all automorphisms of L, including i0,j,k as in Section 6.1 of Gh
ijkL,AutL:= ijkAutL(fieldLinfo);
assert ijkL[3](th) eq L!th; // this is the identity automorphism

t3:= Cputime();
// generate a record to store relevant class group info
ClassGroupInfo:= recformat<classgroup,classnumber,map>;
ClK:= rec< ClassGroupInfo | >;
ClK`classgroup, ClK`map:= ClassGroup(K);
printf hash cat " Total time to compute the class group: %o \n", Cputime(t3);
ClK`classnumber:= ClassNumber(K);

n:= Degree(f);
assert (n eq #clist-1);
s,t:= Signature(K);
r:= s+t-1;
assert (s+2*t) eq n;
assert (r eq 1) or (r eq 2);
t4:= Cputime();
U,psi:= UnitGroup(OK); // generate fundamental units
printf hash cat " Total time to compute the unit group: %o \n", Cputime(t4);
// expresse the fundamental units as elts in OK in terms of the integral basis
epslist:=[psi(U.(i+1)) : i in [1..r]];
assert (#epslist eq 1) or (#epslist eq 2);
zetalist:= [psi(U.1)]; // generator for units of finite order
zeta:= (psi(U.1))^2;
while (zeta ne psi(U.1)) and (zeta notin zetalist) and (-zeta notin zetalist) do
    Append(~zetalist, zeta);
    zeta:= zeta*psi(U.1);
end while;
// assert torsion subgroup of K is {1,-1}, as K has at least 1 real embedding {1,-1}
assert #zetalist eq 1;
zeta:= zetalist[1];
fieldKinfo`zeta:= zeta;
fieldKinfo`fundamentalunits:= epslist;

assert #RemainingCases eq 1; // mulitple primelists not possible
remainingCase:= RemainingCases[1];
t5:= Cputime();
afplist:= prep1(fieldKinfo,clist,remainingCase); // generate all ideal equations
printf hash cat " Total time to compute all ideal equations: %o \n", Cputime(t5);

// assert setup
QUV<U,V>:=PolynomialRing(Rationals(),2);
Z<x_>:= PolynomialRing(Integers());
c0:=Integers()!clist[1];
assert c0 ne 0;
n:=#clist-1;
assert n eq 3;
fclist:= [Integers()!Coefficient(f,i) : i in [3..0 by -1]];
Integerf:=&+[fclist[i+1]*x_^(n-i) : i in [0..n]];
assert f eq ChangeRing(Integerf,Rationals());
F:=&+[clist[i+1]*U^(n-i)*V^i : i in [0..n]];
assert DiscF eq Discriminant(Evaluate(F,[x_,1]));

t6:= Cputime();
// remove ideal equations which have exponent 0 on all prime ideals by solving
// corresponding Thue equations
toRemove:= [];

for i in [1..#afplist] do
    fplist:= afplist[i][4];
    if IsEmpty(fplist) then
	Append(~toRemove,i);
    end if;
end for;

// remove cases covered by Thue solver
afplistNew:= [afplist[i] : i in [1..#afplist] | i notin toRemove];
afplist:= afplistNew;
printf hash cat " Total time to remove ideal equations covered by Thue solver: %o \n",
       Cputime(t6);

// these should have been removed !!
assert (IsEmpty(afplist) eq false);
printf hash cat " Number of ideal equations: %o \n", #afplist;
t7:= Cputime();
alphgamlist:= prep2(fieldKinfo,ClK,afplist);
printf hash cat " Total time to compute all S-unit equations: %o \n", Cputime(t7);
printf hash cat " Number of S-unit equations: %o \n", #alphgamlist;

// empty alphgamlist should have been remvoed !!!
assert (IsEmpty(alphgamlist) eq false);
complexPrec:= 400;
t8:= Cputime();
UpperBounds(fieldKinfo,clist,~alphgamlist,complexPrec);
printf hash cat " Total time to compute initial height bounds: %o \n", Cputime(t8);

// didn't run any Thue tests !!!!!!!!!!!
assert IsEmpty(TMSolutions);

for j in [1..#alphgamlist] do
    idealEq:= alphgamlist[j];
    jhash:= hash cat "Case" cat IntegerToString(j);

    /*fprintf SUnitEq, jhash cat " Minimal polynomial for K: %o \n", fclist;
    fprintf SUnitEq, jhash cat " Class number: %o \n", ClK`classnumber;
    if #fieldKinfo`fundamentalunits eq 1 then
	fprintf SUnitEq, jhash cat " Fundamental unit: " cat
			 Sprint(K!fieldKinfo`fundamentalunits[1]) cat "\n";
    elif #fieldKinfo`fundamentalunits eq 2 then
	fprintf SUnitEq, jhash cat " Fundamental units: " cat
			 Sprint(K!fieldKinfo`fundamentalunits[1]) cat
			 Sprint(K!fieldKinfo`fundamentalunits[2]) cat "\n";
    end if;
    fprintf SUnitEq, jhash cat " Zeta: %o \n", K!fieldKinfo`zeta;
    fprintf SUnitEq, jhash cat " Alpha: %o \n", K!idealEq`alpha;
    if #idealEq`gammalist eq 1 then
	fprintf SUnitEq, jhash cat " Gamma: " cat Sprint(K!idealEq`gammalist[1])
			 cat "\n";
    else
	fprintf SUnitEq,
		jhash cat " Gammas: " cat
		&cat[Sprintf( "%o, ", K!idealEq`gammalist[i], K!idealEq`gammalist[i]): i in [1..#idealEq`gammalist-1]]
		cat Sprint(K!idealEq`gammalist[#idealEq`gammalist]) cat "\n";
    end if;
    fprintf SUnitEq, jhash cat " S-unit equation rank: %o \n",
	    #idealEq`gammalist+#fieldKinfo`fundamentalunits;
    fprintf SUnitEq, jhash cat " Initial bound: %o \n", idealEq`bound;
   */






end for;




printf hash cat " Total time: %o\n", Cputime(t0);
UnsetLogFile();
exit;






 bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=100,lllReduce:=true, breakSymmetry:= true);












                // if r = 2:


Reallattice:


 compute wgamlatlist,wepslatlist, then matM, then:  and add Bepstar in
// generates real lattice matrix
    ///////
    // CHECK THAT CONDITIONS OF THE LEMMATA ARE MET; choose tau // shuffle through tau;
    i:= 1;      // TEMP
    tauAut:= AutL[i];
    ctau:= Log(Max(1,2*Abs( LintoC(tauAut(delta2L)))));
    assert hepslist[i] gt ctau; // MIGHT NEED TO BE AN IF STATEMENT
    ktau:= (3/2)*Abs( LintoC(tauAut(delta2L))); // TEMP
    ltau:= Floor(1/2*Log(quadbound));   //TEMP; try 1000
    ltau:= 200;
    c:= Ceiling(Exp(ltau)); // TEMP
    // compute bound b
    Bgam:= Ceiling((1/Log(2)^2)*&+[ h^2 : h in hgamlist]);

    // compute bound b_eps; since r = 2, there is only 1 such b_eps where eps =! eps^*
        // choose eps^* = epslist[2]; hence l = 1 here
    Beps:= ((1/Degree(K,Rationals()))*&+[hgamlist[k]*wgamlklist[1][k] : k in [1..nu]]);
    Beps:= Ceiling((Beps + (1/Degree(L,Rationals()))*&+[hepslist[k]*wepslklist[1][k] : k in [1..#AutL]])^2);

    // compute bound b_eps^*; since r = 2, there is only 1 such b_eps where eps =! eps^*
        // choose eps^* = epslist[2]; hence l = 2 here

    sum1:= (1/Degree(K,Rationals()))*&+[hgamlist[k]*wgamlatlist[k] : k in [1..nu]];
    sum2:= (1/Degree(L,Rationals()))*&+[hepslist[k]*wepslatlist[k] : k in [1..#AutL]];
    Bepstar:= Ceiling(((1/2)*(sum1 + sum2) + 1/2 + c*ktau*Exp(-ltau))^2);


    /////////
    // should make eps^* more explicit maybe

    // compute alpha_{gam, k} for the lattice Gamma_tau
    alpha0:= Round(c*Log(Abs(LintoC(tauAut(delta1L)))));     // might have to consider what Round is doing here
    alphagamlist:= [Round(c*Log(Abs(LintoC( tauAut(gammalistLk[k]/gammalistLj[k]) )))) : k in [1..nu]];

    // compute alpha_{eps, 1} for the lattice Gamma_tau
        // choose eps^* = epslist[2];
    alphaepslist:= [Round(c*Log(Abs(LintoC( tauAut(epslistLk[k]/epslistLj[k]) )))) : k in [1..r]];

    // generate the matrix defining the lattice Gamma_tau
    matGtau:= IdentityMatrix(Integers(),nu+r);
    for i in [1..nu] do
        matGtau[nu+r,i]:= alphagamlist[i];
    end for;
    for i in [nu+1..nu+r] do
        matGtau[nu+r,i]:= alphaepslist[i-nu];
    end for;

//            // TESTING TRANSLATED LATTICE
//            matGtau:= IdentityMatrix(Rationals(),nu+r);
//            for i in [1..nu] do
//                matGtau[nu+r,i]:= alphagamlist[i];
//            end for;
//            for i in [nu+1..nu+r] do
//                matGtau[nu+r,i]:= alphaepslist[i-nu];
//            end for;

//             // generate the translation vector w_tau of the lattice Gamma_tau
//            vecWtau:= ZeroMatrix(Rationals(),nu+r,1);
//            vecWtau[nu+r,1]:= alpha0;
//           // END OF TEST




//            // generate the translation vector w_tau of the lattice Gamma_tau
//            vecWtau:= ZeroMatrix(Integers(),nu+r,1);
//            vecWtau[nu+r,1]:= alpha0;

    // generate the matrix representing the ellipsoid, M^T*M;
    matM:= IdentityMatrix(Integers(),nu+r);
    InsertBlock(~matM, (Beps*Bepstar)*(Transpose(matA)*matD*matA), 1, 1);
    //InsertBlock(~matM, (Transpose(matA)*matD*matA), 1, 1);
    matM[nu+1, nu+1]:= Floor(Bgam*Bepstar);
    matM[nu+2, nu+2]:= Floor(Bgam*Beps);

    // generate the matrix B^T*B
    matB:= Transpose(matGtau)*matM*matGtau;
    center:= ZeroMatrix(Rationals(), nu+r, 1);
    center[nu+r,1]:= -alpha0/alphaepslist[r];
    boundForNormSquared:= Ceiling((1+r)*(Bgam*Beps*Bepstar));

return matB, boundForNormSquared, center;
            maxNumSolutions:= 10;
            bufferWasBigEnough, solutionsList:= My_FinckePohst(matB,boundForNormSquared:center:=center, maxNumSolutions:=-1,lllReduce:=true, breakSymmetry:= true);


////////////////////////////////////////////////////////////////////////////////
///// NON-ARCHIMEDEAN CASE /////////////////////////////////////////////////////
////oh how i wish all of the code would fit in the lines properly///////////////



prec:= 30; //placeholder
Thetaps:= [];
printf "Computing all roots of f in Cp...";
t3:= Cputime();
for i in [1..#gammalist] do
    p:=primelist[i];
    fprsL:= Factorisation(p*OL);
    fprsL:= fprsL[1][1];
    //prec:= pprecs[i];
    Thetaps[i]:= thetas(th,p,prec,L,fprsL);
end for;

// need Realijk here






Roundp:=function(elt);
    /*
    Input: x = a real number
    Ouput: The nearest positive integer to x.  If two postive integers are the
    same distance to x, take the largest of the two.
    */
    assert elt ge 0;
    y:= Round(elt);
    if y eq 0 then
        y:=1;
    end if;
    return y;
end function;


RNTO:=function(elt);
    /*
    RNTO = Round Nonpositive to One
    Input: x = a real number
    Output: x if x > 0, 1 if x <= 0
    */
    if elt le 0 then
        return 1;
    else
        return elt;
    end if;
end function;


pInteger:=function(elt,p,m,prec);

    /*
    Input: m = positive integer, p a prime
    x = an element in the p-adic field Q_{p} that belongs to the subring Z_{p} (the ring of p-adic integers in Q_{p}).
    Output: The unique integer x^{m} in [0,p^m - 1] with ord_{p}(x - x^{m}) >= m
    */
    y:=pAdicRing(p : Precision:=prec) ! elt;
    y:=pAdicQuotientRing(p, m) ! y;

    y:=IntegerRing() ! y;
    if y lt 0 then
        y:=y+p^m;
    end if;
    return y;
end function;








latticeprep:=function(p,prec,L,fprsL,eps,zeta,thetap,quad);
     /*
    INPUT:
        fa:= an ideal in OK such that
            fa * fp_1^{n_1} * ... * fp_u^{n_u} = principal ideal
        fplist:= a list of prime ideals

    OUTPUT:
        tf, alpha, gammalist, matA, rr.
	// Here tf is true or false. False means that [fa]^{-1} is not in the image
	// of phi (in the notation of the letter) and so the equation has no solution.
	// If tf is false then the other values return are all zero.
	// If tf is true ([fa]^{-1} is in the image of phi),
	// then alpha \in K^*
	// gammalist is a list gamma_1,..,gamma_u, and these
	// values are as in equation (4) of the letter.
	// It also returns the matrix A, and the vector rr
	// in the notation of the letter.
	// If fplist is empty then it just returns tf, alpha, [], 0, 0
	// where tf is true/false depending on whether fa is principal or not,
	// and if so alpha will be a generator.

    REMARKS:
        // I shouldn't start with this since this isn't the first thing we do...


    EXAMPLE:

    // clist is a list of coefficients c_0,c_1,..,c_n.
    // a is an integer.
    // primelist is a list of the primes p_1,p_2,..,p_v.
    // This returns a list of the possible quadruples [* alpha, gammalist, matA, r *]
    // where alpha in K^*, and gammalist is a list gamma_1,...,gamma_u
    // so that (c_0 X - th Y)OK =alpha*gamma_1^{m_1}*..*gamma_u^{m_u} (as in equation (4)).
    // matA and rr are the matrix A and the vector rr, so that
    // nn = mm A + rr, where nn is the vector of exponents in (3)
    // and mm is the vector of exponents in (4).
    // DETERMINE PRECISION FOR P OUTSIDE LOOP

    // chooses d_l, ihat, h;
    returns return MBnail, beta, h, ihat, dd, delta2;
    */
    K:=NumberField(Universe([quad[1]]));
    OK:=MaximalOrder(K);
    th:=K.1;
    f:=MinimalPolynomial(th);
    assert &and[ c in Integers() : c in Coefficients(f) ];
    assert IsMonic(f);
    assert IsIrreducible(f);
    n:=Degree(NumberField(OK));
    assert n eq Degree(f);
    f:=MinimalPolynomial(th);
    Lp, mLp:= Completion(L, fprsL : Precision:=prec);
    Nail, i0jk:= pAdicjk(p,prec,L,fprsL,eps,zeta,thetap,quad);
    // verify Lemma 6.5
    if (Nail ne -1) and (i0jk ne [[],[],[]]) then
        assert Nail ge 0;
        //return Nail,[],0,0,0;
    end if;
    assert #i0jk eq 3;
   // assert (zeta eq K![-1,0,0,0] or zeta eq K![1,0,0,0]);
    alpha:= quad[1];
    gammalist:= quad[2];
    v:= #gammalist;
    // image of gamma under th -> thetap[i][j]
    gammap:= [ImageInp(th,thetap,gamma) : gamma in gammalist];
    fprs:= Factorisation(p*OK);
    fprs:=[fact[1] : fact in fprs];     // the prime ideals above p
    assert &and[#thetap[i] eq RamificationDegree(fprs[i])*InertiaDegree(fprs[i]) : i in [1..#fprs]];
    // image of eps under th -> thetap[i][j]
    epsp:= ImageInp(th,thetap,eps);
    tau:=alpha*zeta;
    // image of tau under th -> thetap[i][j]
    taup:= ImageInp(th,thetap,tau);
    i0:= i0jk[1];
    jj:= i0jk[2];
    kk:= i0jk[3];
    assert #thetap[i0][1] eq 1;
    delta1:=(thetap[i0][1] - thetap[j[1]][j[2]])/(thetap[i0][1] - thetap[k[1]][k[2]]);
    delta1:= delta1*(taup[k[1]][k[2]]/taup[j[1]][j[2]]);
    assert Valuation(delta1) eq 0;
    delta2:=(thetap[j[1]][j[2]] - thetap[k[1]][k[2]])/(thetap[k[1]][k[2]] - thetap[i0][1]);
    delta2:= delta2*(taup[i0][1]/taup[j[1]][j[2]]);
    logalph:= pAdicLog(delta1,p);
    assert IsZeroLocal(logalph,AbsoluteDegree(Lp)) eq false;
    temp1:=[pAdicLog(gammap[i][k[1]][k[2]]/gammap[i][j[1]][j[2]], p) : i in [1..v]];
    temp2:=[pAdicLog(epsp[k[1]][k[2]]/epsp[j[1]][j[2]], p)];
    logalph:= [logalph] cat temp1 cat temp2;
    assert #logalph eq (v+2);
    // verify Lemma 6.9(i)
    vals:= Min([Valuation(logalph[i]) : i in [2..(v+2)]]);
    if Valuation(logalph[1]) lt vals then
        Nail:=Max([Floor((1/(p-1) - Valuation(delta2))), Ceiling(vals - Valuation(delta2))-1]);
        if Nail ge 0 then
            return Nail,[],0,0,0;
        else
            return 0,[],0,0,0;
        end if;
    end if;
    // verify Lemma 6.9(ii)
    cals:= [LpType(la,p,Lp)[2] : la in logalph];        // coefficients of alpha_{ih}
    u:= LpType(logalph[1],p,Lp)[1];
    temph:= 1;
    for h in [1..AbsoluteDegree(Lp)] do
        nailh:=[];      // stores bounds for each h, where they exist
        if IsZeroLocal(cals[1][h],AbsoluteDegree(Lp)) eq false then
            temph:= h;
            valsh:= Min([Valuation(cals[i][h]) : i in [2..v+2]]);
            if Valuation(cals[1][h]) lt valsh then
                Append(~nailh, Max([Floor((1/(p-1) - Valuation(delta2))), Ceiling(valsh - Valuation(delta2) + u)-1]));
            end if;
        end if;
    end for;
    if #nailh ge 1 then // holds for at least 1 h
        Nail:= Min(nailh);
        if Nail ge 0 then
            return Nail,[],0,0,0;
        else
            return 0,[],0,0,0;
        end if;
    end if;
    // if the program makes it this far, there are no small bounds on Nail
        // arising from Lemma 6.5 and Lemma 6.9
        // hence the code must enter the LLL process to reduce the bounds
    // generates the linear forms in p-adic logs elements for the Special Case
    if SpecialCase eq true then
        min:=Valuation(logalph[2]);
        vals, ihat:= Min([Valuation(logalph[i]) : i in [2..(v+2)]]);
        ihat:= ihat + 1;
        assert Valuation(logalph[1]) ge vals;
        assert Valuation(logalph[ihat]) eq vals;
        beta:= [-logalph[i]/logalph[ihat] : i in [1..v+2]];
        beta:= [LpType(b,p,Lp)[2][1] : b in beta];
        dl:= Valuation(delta2) - Valuation(logalph[ihat]);
        return -1, beta, ihat, dl, delta2;
    // generates the linear forms in p-adic logs elements for the General Case
    else
        cals:= [LpType(la,p,Lp)[2] : la in logalph];        // coefficients of alpha_{ih}
        u:= LpType(logalph[1],p,Lp)[1];
        h:= temph;  // fix h in [1..AbsoluteDegree(Lp)] arbitrarily to be temph
        assert IsZeroLocal(cals[1][h],AbsoluteDegree(Lp)) eq false;
        valsh, ihat:= Min([Valuation(cals[i][h]) : i in [2..v+2]]);
        ihat:= ihat + 1;
        assert Valuation(cals[1][h]) ge valsh;
        assert Valuation(cals[ihat][h]) eq valsh;
        assert IsZeroLocal(cals[ihat][h],AbsoluteDegree(Lp)) eq false;
        beta:= [-cals[i][h]/cals[ihat][h] : i in [1..v+2]];
        dl:= Valuation(delta2) - Valuation(logalph[ihat]) - u;
        return -1, beta, ihat, dl, delta2;
    end if;
end function;



    sc1:= false;        // placeholder to verify Lemma 6.5
    for jk in pairs do
        j:= jk[1];
        k:=jk[2];
        delta1:=(thetap[i0][1] - thetap[j[1]][j[2]])/(thetap[i0][1] - thetap[k[1]][k[2]]);
        delta1:= delta1*(taup[k[1]][k[2]]/taup[j[1]][j[2]]);
        if Valuation(delta1) ne 0 then
            delta2:=(thetap[j[1]][j[2]] - thetap[k[1]][k[2]])/(thetap[k[1]][k[2]] - thetap[i0][1]);
            delta2:= delta2*(taup[i0][1]/taup[j[1]][j[2]]);
            Nail:= Min[Valuation(delta1),0] - Valuation(delta2);
            if Nail ge 0 then
                //sc1:= true;
                // OLD
                // return Nail, [[],[],[]], false;
                print Nail;
                break jk;
            else
    // no solutions are possible from this S-unit equation
        // set default bound to 0
                sc1:= true;
                print 0;
                //OLD
                //return 0, false;
                break jk;
            end if;
        end if;
    end for;
    assert (sc1 eq false);      // else the program will have ended

     -1, [[i0,1],j,k], false;




//        // if f has at least 3 linear factors in Qp[t];
//        // choose j,k to correspond to the roots of these linear factors
//        // NB. each factor corresponds to a prime ideal above p
//    if (&+[1 : i in [1..#fprs] | #thetap[i] eq 1] ge 3) then
//        jsks:= [[j,k] : j in [1..#fprs], k in [1..#fprs] | (j ne k) and (j ne i0) and (k ne i0)];
//        jsks:= [jk : jk in jsks | (#thetap[jk[1]] eq 1) and (#thetap[jk[2]] eq 1)];
//        j:= [jsks[1][1],1];
//        k:= [jsks[1][2],1];
//        assert (#thetap[j[1]] eq 1) and (#thetap[k[1]] eq 1);
//        assert (j[1] ne k[1]) and (j[1] ne i0) and (k[1] ne i0);
//        SpecialCase:= true;
//        return -1, [[i0,1],j,k], SpecialCase;
//    // if f has an irreducible factor in Qp[t] of degree 2
//        // choose j,k to correspond to the roots of this quadratic factor
//    elif (2 in [#thetap[i] : i in [1..#fprs]]) then
//    // determines the index of the degree 2 linear factor
//        jk:= Index([#thetap[i] : i in [1..#fprs]], 2);
//        assert #thetap[jk] eq 2;
//        j:= [jk,1];
//        k:= [jk,2];
//        SpecialCase:= true;
////        return -1, [[i0,1],j,k], SpecialCase;
////    // we are not in the special case
////        // choose j,k to correspond to the roots of the same irred. factor in Qp[t]
////    else
////    // the upper bound on deg(gp) < [Lp:Qp]
////        Lpdeg:= Degree(Lp,PrimeField(Lp));
////        for i in [1..#fprs] do
////            RI:= RamificationIndex(fprs[i]);
////            ID:= InertiaDegree(fprs[i]);
////            if (RI*ID gt 1) and (RI*ID lt Lpdeg) then
////                Lpdeg:= RI*ID;
////                j:= [i,1];
////                k:= [i,2];
////            end if;
////        end for;
////        assert #thetap[j[1]] gt 2;
////        return -1, [[i0,1],j,k], false;

//    assert &and[thetap[jk[1][1]][jk[1][2]] ne thetap[jk[2][1]][jk[2][2]] : jk in pairs];




//      if (&+[1 : i in [1..#fprs] | #thetap[i] eq 1] ge 3) then
//        jsks:= [[j,k] : j in [1..#fprs], k in [1..#fprs] | (j ne k) and (j ne i0) and (k ne i0)];
//        jsks:= [jk : jk in jsks | (#thetap[jk[1]] eq 1) and (#thetap[jk[2]] eq 1)];
//        j:= [jsks[1][1],1];
//        k:= [jsks[1][2],1];
//        assert (#thetap[j[1]] eq 1) and (#thetap[k[1]] eq 1);
//        assert (j[1] ne k[1]) and (j[1] ne i0) and (k[1] ne i0);
//        SpecialCase:= true;
//        return -1, [[i0,1],j,k], SpecialCase;
//    // if f has an irreducible factor in Qp[t] of degree 2
//        // choose j,k to correspond to the roots of this quadratic factor
//    elif (2 in [#thetap[i] : i in [1..#fprs]]) then
//    // determines the index of the degree 2 linear factor
//        jk:= Index([#thetap[i] : i in [1..#fprs]], 2);
//        assert #thetap[jk] eq 2;
//        j:= [jk,1];
//        k:= [jk,2];
//        SpecialCase:= true;


//    jsks:= [[j,jj] : jj in [1..#thetap[j]], j in [1..#thetap] | j ne i0 ];
//    // generates all possible pairs (embeddings) j,k
//    pairs:= [[j,k] : j in jsks, k in jsks | j ne k ];
//    npairs:= [];
//    for jk in pairs do
//        if (jk notin npairs) and ([jk[2],jk[1]] notin npairs) then
//            Append(~npairs, jk);        // removes repetition
//        end if;
//    end for;
//    pairs:=npairs;
//    assert &and[thetap[jk[1][1]][jk[1][2]] ne thetap[jk[2][1]][jk[2][2]] : jk in pairs];
    //end if;
end function;







////////////////////////////////////////////////////////////////////////////////
///// OTHER/OLD TESTS/IDEAS FOR NON- ARCHIMEDEAN CASE //////////////////////////


//// theres a possibility that my elements in L may be moving around - should avoid this
//Realprep:= function(L, OL, AutL, Realijk, quad, tl, epslist, prc)
//    K:=NumberField(Universe([quad[1]]));
//    OK:=MaximalOrder(K);
//    th:=K.1;
//    f:=MinimalPolynomial(th);
//    assert &and[ c in Integers() : c in Coefficients(f) ];
//    assert IsMonic(f);
//    n:=Degree(NumberField(OK));
//    assert n eq Degree(f);
//    tf,mapKL:= IsSubfield(K,L);
//    assert tf;
//    assert (L!th eq mapKL(th)) and (mapKL(th) in tl);

//    alpha:= quad[1];
//    gammalist:= quad[2];
//    matA:= quad[3];
//    fplist:= quad[5];
//    quadprimes:= [Norm(fp) : fp in fplist];
//    assert #quadprimes eq #gammalist;

//    r:= #epslist;
//    assert r eq 2;

//    // apply automorphisms i,j,k: L -> L on the units
//    epslistLi:= [Realijk[1](L!eps) : eps in epslist];
//    epslistLj:= [Realijk[2](L!eps) : eps in epslist];
//    epslistLk:= [Realijk[3](L!eps) : eps in epslist];
//    // apply automorphisms i,j,k: L -> L on the elements gamma of the S-unit equation
//    gammalistLi:= [Realijk[1](L!gamma) : gamma in gammalist];
//    gammalistLj:= [Realijk[2](L!gamma) : gamma in gammalist];
//    gammalistLk:= [Realijk[3](L!gamma) : gamma in gammalist];

//    gammafacLi:= [Factorization(ideal<OL|gammaL>) : gammaL in gammalistLi];
//    gammafacLj:= [Factorization(ideal<OL|gammaL>) : gammaL in gammalistLj];
//    gammafacLk:= [Factorization(ideal<OL|gammaL>) : gammaL in gammalistLk];

//    // ensure that the prime ideals in L above gamma don't cancel
//    for i in [1..#gammalist] do
//        assert (#gammafacLi[i] eq #gammafacLj[i]) and (#gammafacLj[i] eq #gammafacLk[i]);
//        assert &and[gammafacLi[i][j] ne gammafacLj[i][j] : j in [1..#gammafacLi[i]]];
//        assert &and[gammafacLi[i][j] ne gammafacLk[i][j] : j in [1..#gammafacLi[i]]];
//        assert &and[gammafacLj[i][j] ne gammafacLk[i][j] : j in [1..#gammafacLj[i]]];
//    end for;

//    CField<i>:= ComplexField(prc);
//    LintoC:= hom< L -> CField | Conjugates(L.1)[1] >;

//    for i1 in [1..#AutL] do
//        for i2 in [i1 + 1..#AutL] do
//            a:= (AutL[i1])(epslistLj[1]/epslistLi[1]);
//            a:= Log(Abs(LintoC(a)));

//            b:= (AutL[i1])(epslistLj[2]/epslistLi[2]);
//            b:= Log(Abs(LintoC(b)));

//            c:= (AutL[i2])(epslistLj[1]/epslistLi[1]);
//            c:= Log(Abs(LintoC(c)));

//            d:= (AutL[i2])(epslistLj[2]/epslistLi[2]);
//            d:= Log(Abs(LintoC(d)));
//            if (a*d - b*c) ne 0 then
//                iotalist:= [i1,i2];
//                break i1;
//            end if;
//        end for;
//    end for;
//    matR:= Matrix(ComplexField(),r,r,[a,b,c,d]);
//    tR, matRinv:= IsInvertible(matR);
//    tA, matAinv:= IsInvertible(matA);
//    assert tR and tA;
//    i1:= iotalist[1];
//    i2:= iotalist[2];

//    // iota 1 gammas and iota 2
//    loggammalistLi1:= [ Log(Abs(LintoC( (AutL[i1])(gammalistLj[k]/gammalistLi[k]) ))) : k in [1..#gammalist]];
//    loggammalistLi2:= [ Log(Abs(LintoC( (AutL[i2])(gammalistLj[k]/gammalistLi[k]) ))) : k in [1..#gammalist]];

//    wgammalist:= [];
//    for l in [1..r] do
//        wgammalist[l]:= [];
//        for k in [1..#gammalist] do
//            alphalk:= matRinv[l,1]*&+[matAinv[i,k]*loggammalistLi1[i] : i in [1..#gammalist]];
//            alphalk:= alphalk + matRinv[l,2]*&+[matAinv[i,k]*loggammalistLi2[i] : i in [1..#gammalist]];
//            wgammalist[l][k]:= Abs(alphalk)*Degree(K, Rationals())/Log(quadprimes[k]);
//        end for;
//    end for;

//    wepslist:= [];
//    for l in [1..r] do
//        wepslist[l]:= [];
//        m:= Max(Abs(matRinv[l,1]), Abs(matRinv[l,2]));
//        for i in [1..#AutL] do
//            if i eq i1 then
//                wepslist[l][i]:= (m+Abs(matRinv[l,1]))*(Degree(L, Rationals()));
//            elif i eq i2 then
//                wepslist[l][i]:= (m+Abs(matRinv[l,2]))*(Degree(L, Rationals()));
//            else
//                wepslist[l][i]:= m*(Degree(L, Rationals()));
//            end if;
//        end for;
//    end for;

//    // bound on lin form in log
//    wepslatlist:= [];
//    wgammalatlist:= [];
//    for i in [1..#AutL] do
//        sig:= AutL[i];
//        wepslatlist[i]:= (wepslist[1][i] + wepslist[2][i])/2;
//    end for;
//    for k in [1..#gammalist] do
//        wgammalatlist[k]:= (wgammalist[1][k] + wgammalist[2][k])/2;
//        abar:= &+[Abs(matAinv[j,k]) : j in [1..#gammalist]];
//        wgammalatlist[k]:= wgammalatlist[k] + (Degree(K, Rationals()))/(2*Log(quadprimes[k]))*abar;
//    end for;



//    return wepslist, wgammalist, wepslatlist, wgammalatlist;
//end function;


//Reallattice:= function(L, OL, AutL, Realijk, quad, tl, epslist, h, prc)
//    K:=NumberField(Universe([quad[1]]));
//    OK:=MaximalOrder(K);
//    th:=K.1;
//    f:=MinimalPolynomial(th);
//    assert &and[ c in Integers() : c in Coefficients(f) ];
//    assert IsMonic(f);
//    n:=Degree(NumberField(OK));
//    assert n eq Degree(f);
//    tf,mapKL:= IsSubfield(K,L);
//    assert tf;
//    assert (L!th eq mapKL(th)) and (mapKL(th) in tl);

//    alpha:= quad[1];
//    gammalist:= quad[2];
//    matA:= quad[3];
//    fplist:= quad[5];
//    quadprimes:= [Norm(fp) : fp in fplist];
//    assert #quadprimes eq #gammalist;

//    r:= #epslist;
//    assert r eq 2;

//    diag:= [ ((Log(p))^2)/Degree(K,Rationals()) : p in quadprimes];
//    matD2:= DiagonalMatrix(ComplexField(), diag);





//    // compute the bound on |a_l|^2
//    alsquarebound:= [];
//    for l in [1..r] do
//        al1:= 0;
//        for i in [1..#AutL] do
//            al1:= al1 + wepslist[l][i]*h[i];
//        end for;
//        al1:= (1/(Degree(L, Rationals())))*al1;

//        al2:= 0;
//        for i in [1..#gammalist] do
//            al2:= al2 + (1/Degree(K, Rationals()))*wgammalist[l][i]*h[#AutL+i];
//        end for;
//        alsquarebound[l]:= (al1 + al2)^2;
//    end for;





//        lin2bound:= [];
//        for l in [1..r] do
//            if #AutL eq 3 then
//                al1:= (2/(Degree(L, Rationals())))* Max([wsiglist[l][i]*h[i] : i in [1..#AutL]]);
//            else
//                al1:= (1/(Degree(L, Rationals())))* Max([wsiglist[l][i]*h[i] : i in [1..#AutL]]);
//            end if;
//            for i in [1..#gammalist] do
//                al1:= al1 + (1/Degree(K, Rationals()))*wklist[l][i]*h[i];
//            end for;
//            kappa:= 3/2;


//            al1:= al1 + 1/2 + c*kappa*e^ltau // LEFT OFF HERE


//            lin2bound[l]:= al1^2;
//        end for;



Dec:= Decomposition(OL,p);
for fp in Dec do
    fprsL:= fp[1];
    Lp, mLp:= Completion(L, fprsL : Precision:=prec);
    fprs:=Factorisation(p*OK);
    fprs:=[fact[1] : fact in fprs];     // the prime ideals above p
    thetap:=[];
    ths:= [mLp( ijk[i](th)) : i in [1..3]];
    for i in [1..#fprs] do      // runs through each prime ideal above p
        thetap[i]:= [* *];
        Kp, mKp:= Completion(K,fprs[i] : Precision:=prec);
        gp_i:= MinimalPolynomial( mKp(th), PrimeField(Kp));
        gp_i;
        temp:= Roots(gp_i, Lp);   // #temp = degree of gp_i = e_i*f_i
        for j in [1..#temp] do
            thetap[i][j]:= temp[j][1];
        end for;
    end for;
    print thetap;
    print ths;
    print "=====================";
end for;

// rearrange ijks so that L!th eq Realijk[1](th) (identity operation)
// ensure that for deg1 prime ideal, we choose the ideal in L above it for fprsL
// is it possible that magma's initial choice of representative for th is the wrong one?









////////////////////////////////////////////////////////////////////////////////
///// OTHER/OL TESTS/IDEAS FOR ARCHIMEDEAN CASE ////////////////////////////////

// using symmetry
            center[nu+r,1]:= -alpha0;
            boundForNormSquared:= Ceiling((1+r)*(alphaepslist[r]^2*Bgam*Beps*Bepstar));


// OLD BOUND THING
            vTv:= (Transpose(vecWtau)*matM*vecWtau)[1,1];

            Bound:= Ceiling(Abs( (1+r)*(Bgam*Beps*Bepstar) + vTv ) + 2*Abs(alpha0)*Bgam*Beps*Sqrt(Bepstar));
            //Bound:= (Abs( Bgam + Beps + Bepstar) + vTv ) + 2*Abs(alpha0)*Bepstar*Sqrt(Bepstar);
            NoSol:= 100;

            M, z, maxReached:= FinckePohst(matB,Bound,NoSol);
          //  M, z, maxReached:= FinckePohst(matM,Bound,NoSol);
            //M, z, maxReached:= FinckePohst(matM,Integers()! (Abs( (1+r)*(Bgam*Beps*Bepstar))),NoSol);
            #z;

        // TEST: new ellipsoid
            matGtau:= IdentityMatrix(Integers(),nu+r+1);
            for i in [1..nu] do
                matGtau[nu+r+1,i+1]:= alphagamlist[i];
            end for;
            for i in [1..r] do
                matGtau[nu+r+1,nu+i+1]:= alphaepslist[i];
            end for;
            matGtau[nu+r+1,1]:= alpha0;

            matM:= IdentityMatrix(Integers(),nu+r+1);
            InsertBlock(~matM, (Beps*Bepstar)*(Transpose(matA)*matD*matA), 2, 2);
            //InsertBlock(~matM, (Transpose(matA)*matD*matA), 1, 1);
            matM[1,1]:= Floor(Bgam);
            matM[nu+2, nu+2]:= Floor(Bgam*Bepstar);
            matM[nu+3, nu+3]:= Floor(Bgam*Beps);

            matB:= Transpose(matGtau)*matM*matGtau;
            Bound:= Ceiling(Abs( (1+1+r)*(Bgam*Beps*Bepstar)));
            //Bound:= (Abs( Bgam + Beps + Bepstar) + vTv ) + 2*Abs(alpha0)*Bepstar*Sqrt(Bepstar);
            NoSol:= 100;

            M, z, maxReached:= FinckePohst(matB,Bound,NoSol);
          //  M, z, maxReached:= FinckePohst(matM,Bound,NoSol);
            //M, z, maxReached:= FinckePohst(matM,Integers()! (Abs( (1+r)*(Bgam*Beps*Bepstar))),NoSol);
            #z;


            // for some reason, the bound T in short vectors becomes negative
            // still can't figure out why we have so many sols though


////////////////////////////////////////////////////////////////////////////////
///// NON ARCHIMEDEAN CASE /////////////////////////////////////////////////////








SmallBoundsCheck:= procedure(fieldKinfo,fieldLinfo,Case,~pCaseInfoList[i],prec);
    K:=fieldKinfo`field;
    OK:=fieldKinfo`ringofintegers;
    th:= fieldKinfo`gen;
    zeta:= fieldKinfo`zeta;
    epslist:= fieldKinfo`fundamentalunits;
    n:= Degree(K);

    gammalist:= Case`gammalist;
    fplist:= Case`ideallist;
    alpha:= Case`alpha;
    nu:= #gammalist;
    r:= #epslist;

    p:= localpinfo`prime;
    Lp:= localpinfo`Lp;
    thetaL:= localpinfo`thetas;
    mapLL:= localpinfo`mapLL;
    mapLLp:= localpinfo`mapLLp;


    // add conditional function to either do the quick exists or not

    tau:=alpha*zeta;

    // generate images under the maps ijk: L-> L, th -> theta[i][j]
    tauL:=ImageInL(localpinfo,L!tau);
    gammalistL:= [ImageInL(localpinfo,L!gamma) : gamma in gammalist];
    epslistL:= [ImageInL(localpinfo,L!eps) : eps in epslist];

    // check if we can bound Nail early (Lemma 6.5)
    delta1L:=(thetaL[i0[1]][i0[2]] - thetaL[jj[1]][jj[2]])/(thetaL[i0[1]][i0[2]] - thetaL[kk[1]][kk[2]]);
    delta1L:=delta1L*(tauL[kk[1]][kk[2]]/tauL[jj[1]][jj[2]]);
    delta2L:=(thetaL[jj[1]][jj[2]] - thetaL[kk[1]][kk[2]])/(thetaL[kk[1]][kk[2]] - thetaL[i0[1]][i0[2]]);
    delta2L:=delta2L*(tauL[i0[1]][i0[2]]/tauL[jj[1]][jj[2]]);

    pCaseinfo


    if (Valuation(mapLLp(delta1L)) ne 0) then
        Nail:= Min[Valuation(mapLLp(delta1L)),0] - Valuation(mapLLp(delta2L));
        if Nail ge 0 then
            return Nail,0,
        else

        Nail,beta,ihat,dl,delta2

            localpinfo`Nail:= -1;
        end if;
    else
        Logdelta1:= pAdicLog(mapLLp(delta1L),p);
        Loggammalist:=[pAdicLog(mapLLp(gammalistL[i][kk[1]][kk[2]]/gammalistL[i][jj[1]][jj[2]]), p) : i in [1..nu]];
        Logepslist:=[pAdicLog(mapLLp(epslistL[i][kk[1]][kk[2]]/epslistL[i][jj[1]][jj[2]]), p) : i in [1..r]];
        assert (1+#Loggammalist+#Logepslist) eq (1+nu+r);

        minval,ihat:= Min([Valuation(eps) : eps in Logepslist]cat[Valuation(gam) : gam in Loggammalist]);
        if ihat le r then
            ihat:= Logepslist[ihat];
        else
            ihat:= Loggammalist[ihat-r];
        end if;

        if Valuation(Logdelta1) lt minval then
            Nail:= Max([Floor((1/(p-1) - Valuation(mapLLp(delta2L)))),Ceiling(minval - Valuation(mapLLp(delta2L)))-1]);
            if Nail ge 0 then
                localpinfo`Nail:= Nail;
            else
                localpinfo`Nail:= -1;
            end if;
         // if the program makes it this far, there are no small bounds on Nail
        // arising from Lemma 6.5 and Lemma 6.9
        // hence the code must enter the LLL process to reduce the bounds
    // generates the linear forms in p-adic logs elements for the Special Case
        else
            // assert that we are indeed in the special case, where neither lemma can immediately reduce the bound
            assert &and[-loggam/ihat in pAdicRing(p): loggam in Loggammalist];
            assert &and[-logeps/ihat in pAdicRing(p): logeps in Logepslist];
            assert -Logdelta1/ihat in pAdicRing(p);
            gammabetalist:= [-loggam/ihat : loggam in Loggammalist];
            epsbetalist:= [-logeps/ihat : logeps in Logepslist];
            delta1beta:= -Logdelta1/ihat;
            localpinfo`i0jjkk:= [i0,jj,kk];
            localpinfo`linearpform:= [delta1beta] cat gammabetalist cat epsbetalist;
        end if;
    end if;

end function;


ail,beta,ihat,dl,delta2






























function FinckePohst(B,C,Bound)
//    A:= Transpose(B)*B;         // symmetric, positive-definite matrix B
    A:= B;
    n:= NumberOfColumns(A);     // computes dimension of square input matrix A
    A1:= ZeroMatrix(IntegerRing(),n,n);        // creates matrix A1, intentionally not positive-definite
    A1[2,1]:= -1;      // changes matrix A1 so that it is not symmetric; nb. n >= 2 since S contains at least 3 primes
    prc0:= Integers()!Max( [ Max([ A[i,j] : j in [1..n] ]) : i in [1..n] ] );      // computes the largest integer in the matrix A
    prc:= Max(100,#IntegerToString(prc0));      // sets precision for the Cholesky decomposition based on the number of digits in the largest integer in the matrix A

    while IsSymmetric(A1) eq false do
        R:= Transpose(Cholesky(A, RealField(prc))); // applies Cholesky Decomposition to the input matrix
        t,Ri:= IsInvertible(R);             // computes R^{-1} (easy to compute since R is upper triangular)
        Si,Ui:= LLL(Ri);            // computes row-reduced version S^{-1} of R^{-1}, along with U^{-1}, where S^{-1} = U^{-1}*R^{-1}

        t,U:=IsInvertible(Ui);      // computes inverse U of U^{-1}
        S:= R*U;

        norms:= [Sqrt(Norm(Si[i])) : i in [1..n]];        // computes norms of rows of S^{-1}
        order:= Reverse(Sort(norms));                     // sorts norms by decreasing size
        per:= [Index(norms, i) : i in order];       // computes the permutation on (1..n) for which the n rows of S^{-1} have decreasing norms
        for i in [1..n] do
            a:=  &+[1: x in per | x eq i];    // counts repetition of index i
            if a gt 1 then                    // corrects repetition in per, ie. in the event any two norms are equal
                for j in [1..a-1] do
                    Ind:= Index(per,i);       // computes index of i in per
                    per[Index(per[Ind + 1..n],i) + Ind]:= i + 1;    // replaces repeated index, if any
                end for;
            end if;
        end for;

        P:= Transpose(PermutationMatrix(IntegerRing(),per));        // computes the permutation matrix corresponding to the permutation, per
        S1:= S*P;           // rewrites S with columns rearranged by the permutation per, above
        A10:= Transpose(S1)*S1;     // symmetric, positive-definite matrix A1, with entries significantly smaller than those of A
        A1:= Matrix(IntegerRing(),n,n,[IntegerRing()! Round(A10[i][j]) : j in [1..n], i in [1..n]]);        // converts matrix parent (RealField()) of A10 to IntegerRing()
        prc:= prc + 5;  // increases precision on RealField until A1 is Symmetric
    end while;

    while IsPositiveDefinite(A1) eq false do
        R:= Transpose(Cholesky(A, RealField(prc))); // applies Cholesky Decomposition to the input matrix
        t,Ri:= IsInvertible(R);             // computes R^{-1} (easy to compute since R is upper triangular)
        Si,Ui:= LLL(Ri);            // computes row-reduced version S^{-1} of R^{-1}, along with U^{-1}, where S^{-1} = U^{-1}*R^{-1}

        t,U:=IsInvertible(Ui);      // computes inverse U of U^{-1}
        S:= R*U;

        norms:= [Sqrt(Norm(Si[i])) : i in [1..n]];        // computes norms of rows of S^{-1}
        order:= Reverse(Sort(norms));                     // sorts norms by decreasing size
        per:= [Index(norms, i) : i in order];       // computes the permutation on (1..n) for which the n rows of S^{-1} have decreasing norms
        for i in [1..n] do
            a:=  &+[1: x in per | x eq i];    // counts repetition of index i
            if a gt 1 then                    // corrects repetition in per, ie. in the event any two norms are equal
                for j in [1..a-1] do
                    Ind:= Index(per,i);       // computes index of i in per
                    per[Index(per[Ind + 1..n],i) + Ind]:= i + 1;    // replaces repeated index, if any
                end for;
            end if;
        end for;

        P:= Transpose(PermutationMatrix(IntegerRing(),per));        // computes the permutation matrix corresponding to the permutation, per
        S1:= S*P;           // rewrites S with columns rearranged by the permutation per, above
        A10:= Transpose(S1)*S1;     // symmetric, positive-definite matrix A1, with entries significantly smaller than those of A
        A1:= Matrix(IntegerRing(),n,n,[IntegerRing()! Round(A10[i][j]) : j in [1..n], i in [1..n]]);        // converts matrix parent (RealField()) of A10 to IntegerRing()
        prc:= prc + 5;  // increases precision on RealField until A1 is PositiveDefinite
    end while;

    assert IsSymmetric(A1);     // verification that indeed A1 is a symmetric matrix; if false, there is an error in FinckePohst.m
    assert IsPositiveDefinite(A1);      // verification that indeed A1 is a positive definite matrix; if false, there is an error in FinckePohst.m

    //maxReached:= false;     // TEMPORARY TEST!!!!!
    //L:= LatticeWithGram(A1);
    //z1:= ShortVectorsMatrix(L,C);
    //delete L;
    //z:= [Matrix(z1[i]) : i in [1..NumberOfRows(z1)]];       // END TEST

    z,maxReached:= ShortVectors(A1,C,Bound);     // computes coefficient matrix of lattice points x in L with norm(x) <= C. ie. x*A1*Transpose(x) = [y], where y <= C; maxReached
    M:= U*P;      // computes permutation matrix B*U*P such that y:= Transpose(B*U*P*Transpose(z[i])) is a short lattice vector, for z[i] a short coefficient vector

    return M, z, maxReached;    // returns associated lattice matrix, M; short coefficient vectors, z; whether Bound was reached before the algorithm terminated, maxReached

end function;

for x in z do
    y:= Transpose(M*Transpose(x));
    y*Transpose(y);
end for;





        // code for now, r = 2


    alpha:= quad[1];
    gammalist:= quad[2];
    matA:= quad[3];
    fplist:= quad[5];
    quadprimes:= [Norm(fp) : fp in fplist];
    assert #quadprimes eq #gammalist;

    r:= #epslist;
    assert r eq 2;




    // TEMP lower bound on eps star, c, embedding into C;
    ltau:= Floor(1/2*Log(quadbound));
    assert ltau ge Log(2);
    kappatau:= 3/2;
    c:= 1000;
    taus:= AutL[1]; // we run over all taus
    // then run over all eps
    bepsno:= 1;         // TEMP choice of eps*

    bepstar:= (bepstar + (1/2) + c*kappatau*Exp(-ltau))^2;

    // pick one l in r to reduce the bound of
    // for a given l, lowerbound, eps star (??)


    CField<i>:= ComplexField(prc);
    LintoC:= hom< L -> CField | Conjugates(L.1)[1] >;

    delta1L:= (Realijk[1](L!th) - Realijk[2](L!th))/(Realijk[1](L!th) - Realijk[3](L!th));
    delta1L:= delta1L*(Realijk[3](L!taus*alpha)/Realijk[1](L!tau*alpha));

    alpha0:= Round(c*Log(Abs(LintoC(taus(delta1L)))));     // might have to consider what Round is doing here

    alphagam:= [];
    for i in [1..#gammalist] do
        alphagam[i]:= Round(c*Log(Abs(LintoC(taus(Realijk[3](gammalist[i])/Realijk[2](gammalist[i]))))));
    end for;

    alphaeps:= [];
    for i in [1..r] do
        alphaeps[i]:= Round(c*Log(Abs(LintoC(taus(Realijk[3](epslist[i])/Realijk[2](epslist[i]))))));
    end for;
    // swap eps so that eps_* is at the end
    Remove(~alphaeps,bepsno);
    alphaeps[r]:= Round(c*Log(Abs(LintoC(taus(Realijk[3](epslist[bepsno])/Realijk[2](epslist[bepsno]))))));

    Gam:= IdentityMatrix(Integers(),#gammalist+r);
    for i in [1.. #gammalist] do
        Gam[#gammalist+r,i]:= alphagam[i];
    end for;
    for i in [#gammalist+1..#gammalist + r] do
        Gam[#gammalist+r,i]:= alphaeps[i-#gammalist];
    end for;

    // compute matrix D^2

    // shit, this is taking logs, so it cannot be an integral matrix
    // in the notes, I need to change the matrix D back to the way it was
        D2:= DiagonalMatrix(ComplexField(), ds);
















        //wepslist, wgammalist, wepslatlist, wgammalatlist:= Realprep(L, OL, AutL, Realijk, quad, tl, epslist, h, prc);





        ds:= [ ((Log(p))^2)/Degree(K,Rationals()) : p in plist];
        D2:= DiagonalMatrix(ComplexField(), ds);







        D2:= Matrix(ComlpexField(),#gammalist, #gammalist, [
         R:= Matrix(ComplexField(),r,r, [a,b,c,d]);

        delta1L:= (ijk[1](L!th) - ijk[2](L!th))/(ijk[1](L!th) - ijk[3](L!th));
        delta1L:= delta1L*(ijk[3](L!tau)/ijk[1](L!tau));








    // then use embeddings into C to embedd elts of L into C;
    // assert that the tls go to the same things as conjugates of th
    // find invertible matrix R in C

    // compute betas
    // compute alphas

    // compute w's
    // bound on al^2 (using local bound h_sigma?) - beps
    // bound on lin form in log
    // all of this is for the bound to use FP with.


    // then define matrix



    thetaC:= Conjugates(th);
    assert #thetaC eq n;
    L, tl:= SplittingField(f);
     // choose an embedding of L.1 into C by selecting a conjufate of L.1
    L1C:= Conjugates(L.1)[1];
    tlC:= [];
    CField<i>:= ComplexField(prc);
    for j in [1..n] do
        tempf:= hom< K -> CField | L1C[j] >;
        tlC[j]:= tempf(tl[j]);
    end for;

    // determine the preimage in L of thetaC[i] under the embedding L -> C
    ijkC:= [];
    min:=Abs(thetaC[1] - tlC[1]);
    for i in [1..n] do
        if Abs(thetaC[1] - tlC[i]) lt min then
            min:=Abs(thetaC[1] - tlC[i]);
            ijkC[1]:= i;
        end if;
    end for;

    min:=Abs(thetaC[2] - tlC[1]);
    for i in [1..n] do
        if Abs(thetaC[2] - tlC[i]) lt min then
            min:=Abs(thetaC[2] - tlC[i]);
            ijkC[2]:= i;
        end if;
    end for;

    min:=Abs(thetaC[3] - tlC[1]);
    for i in [1..n] do
        if Abs(thetaC[3] - tlC[i]) lt min then
            min:=Abs(thetaC[3] - tlC[i]);
            ijkC[3]:= i;
        end if;
    end for;










        tauC:= ImageInC(th,thetaC,tau);
        epslistC:= [ImageInC(th,thetaC,eps) : eps in epslist];
        gammalistC:= [ImageInC(th,thetaC,gamma) : gamma in gammalist];


        if r eq 2 then
            delta1C:= (thetaC[1] - thetaC[2])/(thetaC[1] - thetaC[3]);
            delta1C:= delta1C*(tauC[3]/tauC[2]);

            delta2C:= (thetaC[2] - thetaC[3])/(thetaC[3] - thetaC[1]);
            delta2C:= delta2C*(tauC[1]/tauC[2]);







        // verify that mathfark{P}s dont cancel...?
        // and that the exponents make sense like we did in GESolver

        // choose an embedding of L into C to get invertible matrix R

        // define quadratic form qf(n) (and associated matrix)




    // DO A THING IF THE LIST OF ALPHGAMMLIST IS EMPTY, ie.
//    //clist;
//[ 6, 1, 4, 10 ]
//> primelist;
////[ 2, 3, 5, 787 ]

//sig1:= hom< K -> L | tl[2]>;
//> sig1:= hom< K -> L | tl[1]>;
//> sig2:= hom< K -> L | tl[2]>;
//> sig3:= hom< K -> L | tl[3]>;


    L, tl:= SplittingField(f);
    printf "Computing the ring of integers of the splitting field...";
    t2:= Cputime();
    OL:= MaximalOrder(L);
    printf "Done! Duration: %o\n", Cputime(t2);




    assert #BoundonM + #ideallist eq #afplist;
    printf "Done!\n";
    printf "Reduced number of ideal equations: %o\n", #ideallist;

    //SetClassGroupBounds("GRH");      // for testing only; comment out otherwise
    printf "Computing the class group...";
    t1:= Cputime();
    ClK,eta:=ClassGroup(K);
    printf "Done! Duration: %o\n", Cputime(t1);
    h_K:= ClassNumber(K);
    L, tl:= SplittingField(f);
    printf "Computing the ring of integers of the splitting field...";
    t2:= Cputime();
    OL:= MaximalOrder(L);
    printf "Done! Duration: %o\n", Cputime(t2);

    pprecs:= padicprecision(primelist, L);      // estimated required precision
    Thetaps:= [];
    printf "Computing all roots of f in Cp...";
    t3:= Cputime();
    for i in [1..v] do
        p:=primelist[i];
        fprsL:= Factorisation(p*OL);
        fprsL:= fprsL[1][1];
        prec:= pprecs[i];
        Thetaps[i]:= thetas(th,p,prec,L,fprsL);
    end for;
    printf "Done! Duration: %o\n", Cputime(t3);
    printf "Computing all S-unit equations...";
    t4:= Cputime();
    alphgamlist:=prep2(ideallist,primelist,ClK,eta,h_K);
    printf "Done! Duration: %o\n", Cputime(t4);
    printf "Number of S-unit equations: %o\n", #alphgamlist;


    printf "Computing the large upper bound on the n_i...";
    t6:= Cputime();
    C10:= UpperBoundm(x,AbsDiscF,n,h_K);
    printf "Done! Duration: %o\n", Cputime(t6);
    printf "Large bound on m: %o\n", C10;

    count:= 1;
    for quad in alphgamlist do
        printf "=========================================\n";
        printf "Case: %o\n", count;
        printf "Computing the large upper bound on |a_1|...";
        t7:= Cputime();
        Nails, maxA:= UpperBounda(x,C10,eps,zeta,quad);
        printf "Done! Duration: %o\n", Cputime(t6);
        printf "Large bound on |a_1|: %o\n", maxA;
        alpha:= quad[1];
        matA:= quad[3]; // used to determine the bound on max|n_i|
        rr:= quad[4];
        af:= quad[6];
        tt:= [Valuation(Norm(af), primelist[i]) : i in [1..v]];
        zz:= [Valuation(Norm(ideal<OK|alpha>), primelist[i]) : i in [1..v]];
        assert [tt[i] + rr[i] : i in [1..v]] eq zz;
        Z:= [Valuation(x,primelist[i]) : i in [1..v]];
        rownormA:=RowSumNorm((ChangeRing(matA, Rationals()))^(-1));
        B:= [1] cat [Ceiling(rownormA*Max(Nails)) : i in [1..v]] cat [maxA];
        printf "Current upper bounds: %o\n", B;
        assert #B eq (v+2);
        printf "Starting reduction...\n";
        t8:= Cputime();
        Improvement:= true;
        while Improvement do
            for i in [1..v] do
                p:=primelist[i];
                fprsL:= Factorisation(p*OL);
                fprsL:= fprsL[1][1];
                prec:= pprecs[i];
                thetap:= Thetaps[i];
                Nail:= pLLL(x,prec,L,fprsL,eps,zeta,thetap,quad,B,i);
                if Nail ne -1 then      // else no improvement was made
                    M:= Floor( (Nail+zz[i])/Z[i] ); // updates M
                    if M lt 3000 then
                        printf "Done reduction! Reduced upper bound on m: %o\n", M;
                        printf "Duration of reduction: %o\n", Cputime(t8);
                        Append(~BoundonM, M);
                        Improvement:= false;
                        break i;
                    else
    // update Nails with new bound M on m
                        Nails:= [M*Z[i]-tt[i]-rr[i] : i in [1..#primelist]];
    // update max|n_i|, hence also B
                        rownormA:=RowSumNorm((ChangeRing(matA, Rationals()))^(-1));
                        B:= [1] cat [Ceiling(rownormA*Max(Nails)) : i in [1..v]] cat [maxA];
                        printf "Reduced upper bounds B after reduction step: %o\n", B;
                        printf "Need to reduce further...\n";
                    end if;
                end if;
            end for;
        end while;
        count:= count + 1;
    end for;
    printf "=========================================\n";
    printf "=========================================\n";

    printf "Done iterating through all the cases.\n";
    printf "Upper bound on m: %o\n", Max(BoundonM);

    printf "Computing all solutions below M: %o ...", Max(BoundonM);
    t9:= Cputime();
    Sol:= finalsol(Floor(Max(BoundonM)),x,deg);
    printf "Done! Duration: %o\n", Cputime(t9);
    printf "All solutions: %o\n", Sol;
    printf "Total running time: %o\n", Cputime(t00);
    return Sol;
end function;
