/*
SUnitEquations.m

Author: Adela Gherga <adelagherga@gmail.com>
Copyright © 2020, Adela Gherga, all rights reserved.
Created: 23 January 2020

Description: This program generates all S-unit equations corresponding to the Thue-Mahler forms of absolute discriminant <= 10^{10}

Commentary:

To do list:  0. Create the appropriate folders (determine rank possibilities)
      	     1. Write the code
      	     2. Generate appropriate output files
	     3. Port output files onto github or dropbox folder

             1. Output results from LocalObstruction, RemainingCases = []
             2. Reference list for: BeReGh, Gh, Si
Example:

*/

/*
Organizational ideas:

1. use bash code to read each line, and use the input to run (this) magma code. This code handles only 1 TM equaiton at a time, and ports the ouput to an apporpriate text file (based on rank, ie number of primes and infinite places);
   Advantages: can parallelize
   Disadvantages: writing bash code is damn hard and I'm not that good at it
   		  won't be able to sort the S-unit equations among each file,
		  will only be able to append them at the end of the files
		  (by rank)


2. Alternatively, this code reads the forms file, and for each on (one at a time), goes through and generates teh S-unit equation and ouptuts it appropriately;

   Advantages: significantly easier to code
	       will be able to further sort the S-unit equations among each
	       file (by more than just rank)
   Disadvantages: parallelization won't be possible here
   		  slow code that might take too long to run


It seems the clear winner is to write bash code that does this. Folder format should be as follows

No. real/complex embeddings (R=0,1,2): 1 folder each
    No of finite places (so total rank should be obvious): 1 folder for each

*/

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
	elif (p le 13) or (p in [13..151] and (#testPrimes le 3)) then
	    // verify local obstructions for primes possible on RHS
	    // this includes divisors of N, and 2,3
	    // the bound 151 is arbitrary, but serves to decrease search time

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
    end for;

    return partialObstruction, localObstruction;
end function;

prep0:= function(OutFiles,LogFile,clist,N)

    /*
     Description: Verify conditions of Theorem 1 of BeReGh for clist,N
     Input: OutFiles:= store all possible outcomes for [N,clist] in one of
     	    	       "[N,clist]NoSUnitEqPossible.txt"
		       "[N,clist]NoSUnitEqNeeded.txt", or
     	    	       "[N,clist]SUnitEq.txt"
            LogFile:= store running times and additional information as "[N,clist]Log.txt"
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
    Zx<x_>:= PolynomialRing(Integers());

    NoSUnitEqPossible:= OutFiles[1];
    NoSUnitEqNeeded:= OutFiles[2];
    SUnitEq:= OutFiles[3];

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

    if (IsEmpty(localObstruction) eq false) then
	// local obstructions present; do not enter TM solver
	enterTM:= false;
//	fprintf NoSUnitEqPossible, "Coefficients: %o, Conductor: %o \n", clist, N;
//	fprintf NoSUnitEqPossible, "Local obstruction at primes:= %o \n",
		localObstruction;
//	fprintf NoSUnitEqPossible, "-"^(75) cat "\n";
	return f, enterTM, TMSolutions, RemainingCasesAllAs;
    end if;
    if (IsEmpty(partialObstruction) eq false) then
	// partial local obstructions present; remove p from primelist
	printf "Partial local obstructions present \n";
	printf 	"No solutions with positive exponent of %o are possible \n",
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
		if (assigned x`unbounded) and (x`alpha1 ge 1) then
		    enterTM:= false;
		   // fprintf NoSUnitEqPossible, "Coefficients: %o, Conductor: %o \n", clist, N;
		  //  fprintf NoSUnitEqPossible,
			    "Theorem 1 of BeReGh does not align with partial obstruction at p:= %o \n", p;
		   // fprintf NoSUnitEqPossible, "-"^(75) cat "\n";
		    return f, enterTM, TMSolutions, RemainingCasesAllAs;
		elif (assigned x`unbounded) and (x`alpha1 eq 0) then
		    delete x`unbounded; // update bound at p
		elif (assigned x`unbounded eq false) and (x`alpha1 ge 1) then
		    // remove extra cases at p which are now not possible
		    Append(~toRemove,i);
		end if;
	    end for;
	end if;
	psetNew:= [pset[i] : i in [1..#pset] | i notin toRemove];

	if IsEmpty(psetNew) then
	    enterTM:= false;
	   // fprintf NoSUnitEqPossible, "Coefficients: %o, Conductor: %o \n", clist, N;
	   // fprintf NoSUnitEqPossible,
		    "Theorem 1 of BeReGh does not align with partial
			 obstruction at p:= %o \n", p;
	   // fprintf NoSUnitEqPossible, "-"^(75) cat "\n";
	    return f, enterTM, TMSolutions, RemainingCasesAllAs;
	end if;
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
    // solve corresponding Thue equations, if any
    RemainingCases:=aprimelist;
    Thuef:= Thue(Evaluate(F,[x_,1])); // generate Thue equation

    RHSlist:= [];
    for pset in aprimelist do
	if IsEmpty(pset[2]) then // no unbounded primes
	    rhs:= Integers()! pset[1];
	    if rhs notin RHSlist then
		Append(~RHSlist, rhs);
	    end if;
	    Exclude(~RemainingCases, pset);
	end if;
    end for;

    // remove Thue cases covered by Thue-Mahler cases
    RHSlistNew:= RHSlist;
    for a in RHSlist do
	for pset in RemainingCases do
	    if IsEmpty(pset[2]) eq false then
		b:= pset[1];
		primelist:= pset[2];
		check1:= &and[p in primelist : p in PrimeDivisors(a) |
			      p notin PrimeDivisors(b)];
		check2:= &and[Valuation(b,p) eq Valuation(a,p) : p in PrimeDivisors(b)];
		if (check1) and (check2) then
		    assert IsDivisibleBy(a,b);
		    DivisorsCheck:= [p : p in PrimeDivisors(a) | p in PrimeDivisors(b)] cat
				    [p : p in primelist |
				     p in PrimeDivisors(a) and p notin PrimeDivisors(b)];
		    assert PrimeDivisors(a) eq DivisorsCheck;
		    Exclude(~RHSlistNew,a);
		    break pset;
		end if;
	    end if;
	end for;
    end for;
    RHSlist:= RHSlistNew;

    // generate all Thue solutions
    for rhs in RHSlist do
	sol:= Solutions(Thuef,rhs);
	for s in sol do
	    if <s,rhs> notin TMSolutions then
		Append(~TMSolutions,<s,rhs>);
	    end if;
	end for;
    end for;

    // if all cases are resolved via Thue equations
    if IsEmpty(RemainingCases) then
	enterTM:=false;
//	fprintf NoSUnitEqNeeded, "Coefficients: %o, Conductor: %o \n", clist, N;
//	fprintf NoSUnitEqNeeded,
		"Thue-Mahler equation has reduced to several Thue equations \n";
//	fprintf NoSUnitEqNeeded,
		"All solutions thus computed via Magma built-in Thue solver \n";
//	fprintf NoSUnitEqNeeded,
		"All solutions: \n%o\n", TMSolutions;
//	fprintf NoSUnitEqNeeded, "-"^(75) cat "\n";
	return f, enterTM, TMSolutions, RemainingCasesAllAs;
    end if;

    // if there are Thue-Mahler equations yet to be solved, not resolvable via Thue equations
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
	    apset:=rec<CaseInfoAllAs | avalues:=avalues,
				       primelist:= primelist>;
	    Append(~RemainingCasesAllAs, apset);
	end if;
    end for;

    // if the code has made it this far, the following must hold
    assert enterTM and IsEmpty(TMSolutions);
    return f, enterTM, TMSolutions, RemainingCasesAllAs;
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


ijkAutL:= function(fieldLinfo)

    /*
     Description:
     Input:
     Output:
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
        ijk[3]:= tau(G.1^3);    // identity map
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
    assert (ijk[1](tl[1]) eq tl[2]) and (ijk[2](tl[1]) eq tl[3])
	   and (ijk[3](tl[1]) eq tl[1]);
    assert (ijk[1](tl[2]) eq tl[3]) and (ijk[2](tl[2]) eq tl[1])
	   and (ijk[3](tl[2]) eq tl[2]);
    assert (ijk[1](tl[3]) eq tl[1]) and (ijk[2](tl[3]) eq tl[2])
	   and (ijk[3](tl[3]) eq tl[3]);

    return ijk, AutL;
end function;

principalize:=function(fieldKinfo,ClK,fa,fplist)

    /*
     Description:
     Input:
     Output:
     Example:
   */
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

    REFERENCE:
    EXAMPLE:
    alpha here has norm (x-1)^3 p_1^{t_1+r_1} \cdots p_v^{t_v+r_v}
    */
    K:=fieldKinfo`field;
    OK:=fieldKinfo`ringofintegers;

    u:=#fplist;
    if u eq 0 then
        tf,alpha:=IsPrincipal(fa);
        if tf then
            return tf, alpha, [K | ], 0, 0;
        else
            return tf, 0, 0, 0, 0;
        end if;
    end if;
    Zu:=FreeAbelianGroup(u);
    phi := hom< Zu -> ClK`classgroup | [ fp@@ClK`map : fp in fplist ]>;
    img:=Image(phi);
    if -fa@@ClK`map in img then
        rr:=(-fa@@ClK`map)@@phi;
        rr:=Eltseq(Zu!rr);
	// to avoid precision errors
	// updates rr to have only positive entries
        for i in [1..#rr] do
            while rr[i] lt 0 do
                rr[i]:= rr[i]+ClK`classnumber;
            end while;
        end for;
        ker:=Kernel(phi);
	// A is a list of vectors for now
        A:=[Eltseq(Zu!a) : a in Generators(ker)];
        assert #A eq u; // hence the kernel has rank u
        matA:=Transpose(Matrix(Rationals(),A)); // the matrix A as denoted in Si
        assert AbsoluteValue(Determinant(matA)) eq #img;
        fa2:=fa*&*[fplist[i]^rr[i] : i in [1..u]];
        tf,alpha:=IsPrincipal(fa2);
        assert tf; // the principal ideal with generator alpha
	// computes the ideals as denoted by \mathfrak{c} in the Si
        clist:=[ &*[fplist[i]^a[i] : i in [1..u] ]  : a in A ];
        gammalist:=[];
        for fc in clist do
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
     Description:
     Input:
     Output:
     Example:
   */

   // INPUT:
//        fa:= an ideal in OK such that
  //          fa * fp_1^{n_1} * ... * fp_u^{n_u} = principal ideal
    //    fplist:= a list of prime ideals

//    OUTPUT:
  //      tf, alpha, gammalist, matA, rr.
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

    //REMARKS:
        // I shouldn't start with this since this isn't the first thing we do...


//    EXAMPLE:

    // clist is a list of coefficients c_0,c_1,..,c_n.
    // a is an integer.
    // primelist is a list of the primes p_1,p_2,..,p_v.
    // This returns a list of the possible quadruples [* alpha, gammalist, matA, r *]
    // where alpha in K^*, and gammalist is a list gamma_1,...,gamma_u
    // so that (c_0 X - th Y)OK =alpha*gamma_1^{m_1}*..*gamma_u^{m_u} (as in equation (4)).
    // matA and rr are the matrix A and the vector rr, so that
    // nn = mm A + rr, where nn is the vector of exponents in (3)
    // and mm is the vector of exponents in (4).


    K:= fieldKinfo`field;
    OK:=fieldKinfo`ringofintegers;

    // generate a record to store relevant case info
    SUnitInfo:= recformat< primelist,avalue,du,alpha,
			   gammalist,matA,vecR,ideallist,bound >;

    alphgamlist:=[ ];
    for pr in afplist do
	primelist:= pr[2];
        af:=pr[3];
        fplist:=pr[4];
	v:= #primelist;
        tf,alpha,gammalist,matA,rr:=principalize(fieldKinfo,ClK,af,fplist);
	if tf then
            assert #gammalist eq #fplist;
            nu:= #fplist;
            Nm:= [Norm(fp) : fp in fplist];
            assert #Nm eq nu;
            assert &and[IsPrime(fp) : fp in Nm];
            rtest:= [];
            for i in [1..#primelist] do
                p:= primelist[i];
                if p in Nm then
                    ind:= Index(Nm, p);
                    rtest[i]:= rr[ind];
                else
                    rtest[i]:= 0;
                end if;
            end for;
            tt:= [Valuation(Norm(af), primelist[i]) : i in [1..v]];
            zz:= [Valuation(Norm(ideal<OK|alpha>), primelist[i]) :
		  i in [1..v]];
	    // sanity checks on exponents of alpha, ideal af, and gammas
            assert [tt[i] + rtest[i] : i in [1..v]] eq zz;
            for i in [1..nu] do
                gamma:= gammalist[i];
                aa:= [Valuation(Norm(ideal<OK|gamma>), Nm[j]) : j in [1..nu]];
                assert aa eq Eltseq(ColumnSubmatrixRange(matA,i,i));
            end for;

            Append(~alphgamlist,
		   rec< SUnitInfo|primelist:=primelist, avalue:=pr[1]`avalue,
				  du:=pr[1]`du, alpha:=alpha,
				  gammalist:=gammalist,matA:=matA,
				  vecR:=rr,ideallist:=fplist>);
        end if;
    end for;
    return alphgamlist;
end function;

UpperBounds:=procedure(fieldKinfo,clist,~alphgamlist,ComplexPrec)

    /*
     Description:
     Input:
     Output:
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
    CField<i>:= ComplexField(ComplexPrec);

    taus:=[hom< K -> CField | thetaC[i] > : i in [1..n]];
    // compute the Weil height of theta
    hth:= (1/n)*&+[Max((Log(Abs(taus[i](th)))), 0) : i in [1..n]];

    for i in [1..#alphgamlist] do
	a:= alphgamlist[i]`avalue;
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


/*
     Description: generate all S-unit equations corresponding to N, clist
     Input: set:=[N,[discF,c_1,c_2,c_3,c_4]], bash input
     Output:
     Example: run with
nohup cat /home/adela/ThueMahler/Data/FormsCond10To6/FormsCond10To6.txt | parallel magma set:={} /home/adela/ThueMahler/Code/GenerateSUnitEquations/GenerateSUnitEquations.m 2>&1 &

*/

// convert bash input into magma integers, sets

LogFile:= "/home/adela/ThueMahler/Data/SUnitEqData/SUnitEqLogs/" cat set cat "Log.txt";
NoSUnitEqPossible:=
    "/home/adela/ThueMahler/Data/SUnitEqData/NoSUnitEqPossible/" cat set cat "NoSUnitEqPossible.txt";
NoSUnitEqNeeded:=
    "/home/adela/ThueMahler/Data/SUnitEqData/NoSUnitEqNeeded/" cat set cat "NoSUnitEqNeeded.txt";
SUnitEq:= "/home/adela/ThueMahler/Data/SUnitEqData/AllSUnitEq/" cat set cat "SUnitEq.txt";

SetLogFile(LogFile);
OutFiles:= [NoSUnitEqPossible,NoSUnitEqNeeded,SUnitEq];

// LEFT OFF HERE; start code on new vms, kill it on r7-bennett3.

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
while set[i] ne "]" do // i should start at ","
    if set[i] eq "," then
	Append(~commas, i);
    end if;
    i:= i + 1;
end while;
assert set[i] eq "]";
assert #commas eq 4;
Append(~brackets,i);

// convert bash symbols of clist into integers
discF:= StringToInteger(&cat[set[i] : i in [brackets[1]+1..commas[1]-1]]);
clist:=[];
for j in [1..#commas-1] do
    n:= [set[i] : i in [(commas[j]+1)..(commas[j+1]-1)]];
    Append(~clist,StringToInteger(&cat(n)));
end for;
Append(~clist,StringToInteger
		  (&cat[set[i] : i in [commas[4]+1..brackets[2]-1]]));

printf "Resolving Thue-Mahler equation with... \n";
printf "Coefficients: %o, Conductor: %o \n", clist, N;
//printf "-"^(75) cat "\n" cat "-"^(75) cat "\n";

// TEMP
LogFile:= [];
OutFiles:= [[],[],[]];
// END OF TEMP
f, enterTM, TMSolutions, RemainingCases:= prep0(OutFiles,LogFile,clist,N);
if (enterTM eq false) then
    printf "No S-unit equations to resolve for this Thue-Mahler equation\n";
    printf "-"^(75) cat "\n";
else

    // generate a record to store relevant field K info
    FieldInfo:= recformat<field,gen,ringofintegers,
			  minpoly,zeta,fundamentalunits>;

    K<th>:=NumberField(f);
    OK:=MaximalOrder(K);
    th:=OK!th;
    fieldKinfo:= rec<FieldInfo | field:= K,gen:= th,
				 ringofintegers:= OK,minpoly:= f>;

    printf "Computing the class group...";
    t2:= Cputime();
    // generate a record to store relevant class group info
    ClassGroupInfo:= recformat<classgroup,classnumber,map>;
    ClK:= rec< ClassGroupInfo | >;
    ClK`classgroup, ClK`map:= ClassGroup(K);
    printf "Done! Duration: %o\n", Cputime(t2);
    ClK`classnumber:= ClassNumber(K);

    n:= Degree(f);
    assert (n eq #clist-1);
    s,t:= Signature(K);
    r:= s+t-1;
    assert (s+2*t) eq n;
    assert (r eq 1) or (r eq 2);
    printf "Computing the Unit Group...";
    t5:= Cputime();
    U,psi:= UnitGroup(OK);      // generates the fundamental units
    printf "Done! Duration: %o\n", Cputime(t5);
    // expresses the fund. units as elts in OK in terms of the integral basis
    epslist:=[psi(U.(i+1)) : i in [1..r]];
    assert (#epslist eq 1) or (#epslist eq 2);
    zetalist:= [psi(U.1)];      // generator for the units of finite order
    zeta:= (psi(U.1))^2;
    while (zeta ne psi(U.1)) and (zeta notin zetalist) and
	  (-zeta notin zetalist) do
	Append(~zetalist, zeta);
	zeta:= zeta*psi(U.1);
    end while;
    // K has at least 1 real embedding, thus the torsion subgroup is {1,-1}
    assert #zetalist eq 1;
    zeta:= zetalist[1];
    fieldKinfo`zeta:= zeta;
    fieldKinfo`fundamentalunits:= epslist;

    L, tl:= SplittingField(f);
    printf "Computing the ring of integers of the splitting field...";
    t2:= Cputime();
    OL:= MaximalOrder(L);
    printf "Done! Duration: %o\n", Cputime(t2);
    tf,mapKL:= IsSubfield(K,L);
    assert tf;
    assert (L!th eq mapKL(th)) and (mapKL(th) in tl);
    fieldLinfo:= rec<FieldInfo | field:= L, gen:=tl,ringofintegers:= OL>;

    // DONT NEED THIS FOR SUNITGENERATOR
    ijkL,AutL:= ijkAutL(fieldLinfo);
    assert ijkL[3](th) eq L!th; // this is the identity automorphism

    // generate all ideal equations
    afplistAll:= [**];
    for apset in RemainingCases do
	afplist:=prep1(fieldKinfo,clist,apset);
	afplistAll:= afplistAll cat afplist;
    end for;

    // remove ideal equations which have exponent 0 on all prime ideals by solving
    // corresponding Thue equations
    Zx<x_>:= PolynomialRing(Integers());
    fclist:= [Integers()!Coefficient(f,i) : i in [3..0 by -1]];
    Integerf:=&+[fclist[i+1]*x_^(n-i) : i in [0..n]];
    assert f eq ChangeRing(Integerf,Rationals());
    Thuef:= Thue(Integerf);
    // LEFT OFF HERE.

    // TO DO: TEST PROGRAM; CHOOSE A SAMPLE FROM LIST OF FILES
//    for set in sets do
//N:= set[1];
//clist:= [set[2][i] : i in [2..5]];
//f, enterTM, TMSolutions, RemainingCases:= prep0(OutFiles,LogFile,clist,N);
//if #RemainingCases gt 2 then
//print set;
//end if;
    //end for;
    // CAN WE AMALGAMATE ASETS? IS IT POSSIBLE THAT WE"RE GETTING THE SAME NEW A AND PRIMESET? IS THERE A WAY THAT WE CAN REMOVE REDUNDANCY?

    toRemove:= [];
    RHSlist:= [];
    for i in [1..#afplistAll] do
	fplist:= afplistAll[i][4];
	if IsEmpty(fplist) then
	    a:= afplistAll[i][1]`newa
	    adu:= afplistAll[i][1]`adu;
	    primelist:= afplistAll[i][2];
	    ideal_a:= afplistAll[i][3];
	    v:= #primelist;
	    tt:= [Valuation(Norm(ideal_a), primelist[i]) : i in [1..v]];
	    assert Norm(ideal_a) eq Abs(a)*&*[primelist[i]^tt[i] : i in [1..v]];
	    rhs:= Integers()! a*&*[primelist[i]^tt[i] : i in [1..v]];
	    if rhs notin RHSlist then
		Append(~RHSlist, RHS);
	    end if;
	    Append(~toRemove,i);
	end if;
    end for;


    for i in [1..#afplistAll] do
	fplist:= afplistAll[i][4];
	if i notin toRemove then
	    a:= afplistAll[i][1]`avalue;
	    du:= afplistAll[i][1]`du;
	    primelist:= afplistAll[i][2];
	    af:= afplistAll[i][3];
	    v:= #primelist;
	    tt:= [Valuation(Norm(af), primelist[i]) : i in [1..v]];
	    assert Norm(af) eq Abs(a)*&*[primelist[i]^tt[i] : i in [1..v]];
	    RHS:= Integers()! a*&*[primelist[i]^tt[i] : i in [1..v]];
	    if RHS in RHSlist then
		print "RHS";
	    end if;
	end if;
    end for;






    for RHS in RHSlist do
	sol:= Solutions(Thuef,RHS);
	for s in sol do
	    if s notin TMSolutions then
		Append(~TMSolutions,s);
	    end if;
	end for;
    end for;

    afplistAllNew:= [afplistAll[i] : i in [1..#afplistAll] | i notin toRemove];
    afplistAll:= afplistAllNew;

    if IsEmpty(afplistAll) then
//	fprintf NoSUnitEqNeeded, "Coefficients: %o, Conductor: %o \n", clist, N;
//	fprintf NoSUnitEqNeeded, "No S-unit equations to resolve for this Thue-Mahler equation\n";
//	fprintf NoSUnitEqNeeded, "All solutions: \n%o\n", TMSolutions;

//	fprintf NoSUnitEqNeeded, "-"^(75) cat "\n";
    else

	printf "Number of ideal equations: %o\n", #afplist;
	printf "Computing all S-unit equations...";
	t2:= Cputime();
	alphgamlistAll:= prep2(fieldKinfo,ClK,afplistAll);

	printf "Done! Duration: %o\n", Cputime(t2);
	printf "Number of S-unit equations: %o\n", #alphgamlistAll;
	assert #alphgamlistAll ne 0;

	ComplexPrec:= 400;
	// compute the initial height bound: change me
	printf "Computing initial height bounds...";
	t1:= Cputime();
	UpperBounds(fieldKinfo,clist,~alphgamlistAll,ComplexPrec);
	printf "Done! Duration: %o\n", Cputime(t1);

//	fprintf SUnitEq, "Coefficients: %o, Conductor: %o \n", clist, N;
//	fprintf SUnitEq, "solutions obtained via Thue equations: \n%o\n", TMSolutions;
//	fprintf SUnitEq, "-"^(75) cat "\n";
	for Case in alphgamlistAll do
	   // fprintf SUnitEq, "Coefficients: %o, Conductor: %o \n", clist, N;
	   // fprintf SUnitEq, "minimal polynomial for K:= %o\n", f;
	   // fprintf SUnitEq, "class number:= %o\n", ClK`classnumber;
	   // fprintf SUnitEq, "fundamental units:= ";
	    for i in [1..#fieldKinfo`fundamentalunits-1] do
	//	fprintf SUnitEq, "%o, ", K!fieldKinfo`fundamentalunits[i];
	    end for;
	   // fprintf SUnitEq, "%o \n",
		    K!fieldKinfo`fundamentalunits[#fieldKinfo`fundamentalunits];
	   // fprintf SUnitEq, "alpha:= %o\n", K!Case`alpha;
	   // fprintf SUnitEq, "gammas:= ";
	    for i in [1..#Case`gammalist-1] do
	//	fprintf SUnitEq, "%o, ", K!Case`gammalist[i];
	    end for;
	   // fprintf SUnitEq, "%o \n", K!Case`gammalist[#Case`gammalist];
	   // fprintf SUnitEq, "S-unit equation rank:= %o\n",
		    #Case`gammalist+#fieldKinfo`fundamentalunits;
	   // fprintf SUnitEq, "initial bound:= %o\n", Case`bound;
	   // fprintf SUnitEq, "-"^(75) cat "\n";
	end for;
    end if;
end if;


// LEFT OFF HERE
// Now availble to run, but with errors
// need to be able to record errors
// need to increase precision on ComplexPrec (done, but not update on r7-bennett3 yet
// cases which don't align with BeGhRe - might just be that they align with BeGhRe, but the partial local obstructions don't, and so the equation really has a local obstruction

// **********************set AllSUnitEq, LogFile, Error File, tempname for SUnit output




// some cases are very slow: set:=[1430,[2,0,1,2]] running for 37 minutes now to generate S unit eqns
// was caused by using too many primes on the RHS for the PrimesUpTo(67) test; fixed, but not updated on r7-bennett3 yet
UnsetLogFile();
exit;
