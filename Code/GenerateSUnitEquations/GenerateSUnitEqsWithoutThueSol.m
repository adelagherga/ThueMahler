/*

GenerateSUnitEqsWithoutThueSol.m

Author: Adela Gherga <adelagherga@gmail.com>
Copyright © 2020, Adela Gherga, all rights reserved.
Created:  6 May 2020

Description: This program generates all S-unit equations corresponding to the Thue-Mahler
	     forms of absolute discriminant <= 10^{10}. Output is printed among
	     "SUnitEqLogs.txt", "NoSUnitEqPossible.txt", "NoSUnitEqNeeded.txt",
	     "ThueEqToSolve.txt", and "AllSUnitEq.txt". The corresponding S-unit equations are
	     printed on "AllSUnitEq.txt," while "NoSUnitEqPossible.txt" lists the Thue-Mahler
	     equations which cannot yield solutions. The file "NoSUnitEqNeeded.txt" lists
	     Thue-Mahler forms which either reduce to Thue equations or which do not yield any
	     S-unit equations. The file "ThueEqToSolve.txt" lists all Thue equations remaining
	     to be solved. Finally, "SUnitEqLogs.txt" tracks all relevant data. Each such file
	     uses a hash in order to distinquish forms printed to the file in parallel.

Commentary: In this algorithm, neither Thue nor Thue-Mahler equations are solved.
            run with
	    nohup cat /home/adela/ThueMahler/Data/FormsCond10To6/FormsCond10To6.txt | parallel -j32 --joblog tmplog magma set:={} /home/adela/ThueMahler/Code/GenerateSUnitEquations/GenerateSUnitEqsWithoutThueSol.m 2>&1 &

To do list: 1. test this version - DONE
            2. move current files on remote - DONE
	    3. run with parallel joblog (limit jobs #s) + check for errors - DONE
	    4. edit intro to GenerateSUnit+solve Thue - DONE
            5. add SL2Z actions; find a way to choose a,b,c,d - DONE
            6. print SL2Z tests in logfile
            7. test + comment
            8. check and compare changes with FormsForBenjamin.txt
	    9. Reference list for: BeReGh, Gh, Si
            10. compress files with gzip -k filename.txt ? and add original files to gitignore ?

seems like changing the order may not be the best option always...

Example:

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
	for u,v in [0..q-1] do
	    if [u,v] ne [0,0] then
		F_q:= Integers()! (Evaluate(F,[u,v]));
		if (F_q mod q eq 0) then
		    hasSolutions:= true;
		    break u;
		end if;
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
	for u,v in [0..q-1] do
	    if [u,v] ne [0,0] then
		F_q:= Integers()! (Evaluate(F,[u,v]));
		if (F_q mod q in rhs) then
		    hasSolutions:= true;
		    break u;
		end if;
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

prep0:= function(hash,OutFiles,LogFile,clist,N : printOutput:=true)

    /*
     Description: Verify conditions of Theorem 1 of BeReGh for clist,N
     Input: hash:= string set appended to the start of every output line;
                   used to ensure output corresponds to correct Thue Mahler form
     	    OutFiles:= store all possible outcomes for [N,clist] in one of
     	    	       "NoSUnitEqPossible.txt"
		       "NoSUnitEqNeeded.txt", or
     	    	       "SUnitEq.txt,"
                       and store Thue equations to be solved in "ThueEqToSolve.txt"
            LogFile:= store running times and additional information as "SUnitEqLogs.txt"
            clist:= [c_0, \dots, c_n], the coefficients of F(X,Y)
            N:= conductor of corresponding elliptic curves in question
            printOutput:= boolean value determining whether to print to LogFile
                          default value is set to true
     Output: f:= monic polynomial defining the number field K = Q(th)
             enterTM:= boolean value determining whether to enter the TM solver
             RemainingCasesAllAs:= list of primelist and all corresponding a values
                                   comprising the RHS of F(x,y)
     Example:
   */

    QUV<U,V>:=PolynomialRing(Rationals(),2);
    Qx<x>:= PolynomialRing(Rationals());

    NoSUnitEqPossible:= OutFiles[1];
    NoSUnitEqNeeded:= OutFiles[2];
    ThueEqToSolve:= OutFiles[3];
    SUnitEq:= OutFiles[4];

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
    RemainingCasesAllAs:= [];

    // verify local and partial local obstructions
    partialObstruction, localObstruction:= localtest(N,F,DiscF);

    if (IsEmpty(localObstruction) eq false) then
	// local obstructions present; do not enter TM solver
	enterTM:= false;
	fprintf NoSUnitEqPossible, hash cat " Local obstruction at p:= %o \n",
		localObstruction[1];
	return f, enterTM, RemainingCasesAllAs;
    end if;
    if (IsEmpty(partialObstruction) eq false) and (printOutput eq true) then
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
		if (assigned x`unbounded) and (x`alpha1 ge 1) then
		    enterTM:= false;
		    fprintf NoSUnitEqPossible, hash cat " Theorem 1 of BeReGh does not align with partial obstruction at p:= %o \n", p;
		    return f, enterTM, RemainingCasesAllAs;
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
	    fprintf NoSUnitEqPossible, hash cat " Theorem 1 of BeReGh does not align with partial obstruction at p:= %o \n", p;
	    return f, enterTM, RemainingCasesAllAs;
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
    // store corresponding Thue equations to be solved, if any
    RemainingCases:=aprimelist;

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

    // store Thue equations to be solved in "ThueEqToSolve.txt"
    if (#RHSlist eq 1) and (printOutput eq true) then
	fprintf ThueEqToSolve, hash cat " Thue equation to be solved: %o \n", clist;
	fprintf ThueEqToSolve, hash cat " Right-hand side: " cat Sprint(RHSlist[1]) cat "\n";
    elif (#RHSlist gt 1) and (printOutput eq true) then
	fprintf ThueEqToSolve, hash cat " Thue equation to be solved: %o \n", clist;
	fprintf ThueEqToSolve, hash cat " Right-hand side: " cat
				 &cat[Sprintf( "%o, ", RHSlist[i], RHSlist[i]): i in [1..#RHSlist-1]] cat Sprint(RHSlist[#RHSlist]) cat "\n";
    end if;

    // if all cases are resolved via Thue equations
    if IsEmpty(RemainingCases) then
	enterTM:=false;
	fprintf NoSUnitEqNeeded,
		hash cat " Thue-Mahler equation has reduced to several Thue equations \n";
	return f, enterTM, RemainingCasesAllAs;
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
    assert enterTM;
    return f, enterTM, RemainingCasesAllAs;
end function;

GL2Zactions:= function(clist)

     /*
     Description: generate all possible GL2(Z) actions under which c0 lies in [1..20]
     Input: clist:= [c_0, \dots, c_n], the coefficients of F(X,Y)
     Output: GL2Zclists:= all possible coefficients of F(X,Y) under GL2(Z) action under which
                          c0 lies in the interval [1..20]
     Example:
    */

    QUV<U,V>:=PolynomialRing(Rationals(),2);
    Qx<x>:= PolynomialRing(Rationals());
    Zx_<x_>:= PolynomialRing(Integers());

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

    // generate possible GL2(Z) actions under which c0 lies in the interval [1..20]
    // solve corresponding Thue equation F(a,c) = c0 for new potential c0
    ThueF:= Thue(Evaluate(F,[x_,1])); // generate Thue equation
    GL2Zclists:= [];
    testset:= PrimesInInterval(1,200) cat [i: i in [1..20] | i notin PrimesInInterval(1,200)];
    for i in testset do
	if IsEmpty(Solutions(ThueF,i)) eq false then
	    hasGL2Zaction:= false;
	    a:= Solutions(ThueF,i)[1][1];
	    c:= Solutions(ThueF,i)[1][2];
	    if ((a eq 0) and (Abs(c) eq 1)) then
		b:= -1/c;
		d:= 0;
		hasGL2Zaction:= true;
	    elif ((c eq 0) and (Abs(a) eq 1)) then
		d:= 1/a;
		b:= 0;
		hasGL2Zaction:= true;
	    elif ((a ne 0) and (c ne 0) and (GCD(a,c) eq 1)) then
		g,d,b:= XGCD(a,c);
		b:= -b;
		assert g eq 1;
		hasGL2Zaction:= true;
	    end if;

	    if hasGL2Zaction then
		assert (a*d - b*c eq 1);
		GL2ZF:= Evaluate(F,[a*U+b*V,c*U+d*V]);
		newclist:= [Integers()! MonomialCoefficient(GL2ZF,U^(n-i)*V^i) : i in [0..n]];
		assert newclist eq Reverse(Coefficients(Evaluate(GL2ZF,[x,1])));
		assert newclist[1] eq i;
		Append(~GL2Zclists,newclist);
	    end if;
	end if;
    end for;
    return GL2Zclists;
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
     Description: appends upper bound on all S-unit equations as per Section 6.2 of Gh
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


/*
     Description: generate all S-unit equations corresponding to N, clist
     Input: set:=[N,[discF,c_1,c_2,c_3,c_4]], bash input
     Output: N/A
     Example:
*/

t0:= Cputime();
// generate relevant files
LogFile:= "/home/adela/ThueMahler/Data/SUnitEqData/SUnitEqLogs.txt";
NoSUnitEqPossible:= "/home/adela/ThueMahler/Data/SUnitEqData/NoSUnitEqPossible.txt";
NoSUnitEqNeeded:= "/home/adela/ThueMahler/Data/SUnitEqData/NoSUnitEqNeeded.txt";
ThueEqToSolve:= "/home/adela/ThueMahler/Data/SUnitEqData/ThueEqToSolve.txt";
SUnitEq:= "/home/adela/ThueMahler/Data/SUnitEqData/AllSUnitEq.txt";

/*
LogFile:= "tmplog";
NoSUnitEqPossible:= "tmpno";
NoSUnitEqNeeded:= "tmpno";
ThueEqToSolve:= "tmpthue";
SUnitEq:= "tmpall";
*/

SetLogFile(LogFile);
OutFiles:= [NoSUnitEqPossible,NoSUnitEqNeeded,ThueEqToSolve,SUnitEq];
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
f, enterTM, RemainingCases:= prep0(hash,OutFiles,LogFile,clist,N:printOutput:=false);
printf hash cat " Total time to determine local obstructions: %o \n", Cputime(t1);

if (enterTM eq false) then
    printf hash cat " No S-unit equations to resolve for this Thue-Mahler equation \n";
else
    // generate a record to store relevant info of the field K = Q(th)
    FieldInfo:= recformat<field,gen,ringofintegers,minpoly,zeta,fundamentalunits>;

    t2:= Cputime();
    // verify whether action of GL2(Z) group leads to fewer S-unit equations
    // this comparison is based on the number of divisors of c0 and subsequent ideals of norm a
    // as all resulting fields K are isomorphic (and thus ideal splitting remains unchanged)
    GL2Zclists:= GL2Zactions(clist);
    if clist in GL2Zclists then
	Exclude(~GL2Zclists, clist);
    end if;
    Insert(GL2Zclists, 1, clist);

    GL2Zcases:= [0 : i in [1..#GL2Zclists]];
    for i in [1..#GL2Zclists] do
	tempclist:= GL2Zclists[i];
	f, enterTM, RemainingCases:=
	    prep0(hash,OutFiles,LogFile,tempclist,N:printOutput:=false);
	assert enterTM;
	K<th>:=NumberField(f);
	OK:=MaximalOrder(K);
	th:=OK!th;
	fieldKinfo:= rec<FieldInfo | field:= K,gen:= th,ringofintegers:= OK,minpoly:= f>;
	assert #RemainingCases eq 1; // mulitple primelists not possible
	remainingCase:= RemainingCases[1];
	afplist:= prep1(fieldKinfo,tempclist,remainingCase); // generate all ideal equations

	// remove ideal equations which have exponent 0 on all prime ideals by generating
	// corresponding Thue equations to be solved
	toRemove:= [];
	RHSlist:= [];
	for i in [1..#afplist] do
	    fplist:= afplist[i][4];
	    if IsEmpty(fplist) then
		a:= afplist[i][1]`newa;
		adu:= afplist[i][1]`adu;
		primelist:= afplist[i][2];
		ideal_a:= afplist[i][3];
		v:= #primelist;
		tt:= [Valuation(Norm(ideal_a), primelist[i]) : i in [1..v]];
		assert Norm(ideal_a) eq Abs(a)*&*[primelist[i]^tt[i] : i in [1..v]];
		rhs:= Integers()! a*&*[primelist[i]^tt[i] : i in [1..v]];
		tf,alpha:=IsPrincipal(ideal_a); // verify ideal_a is principal
		if (tf) and (rhs notin RHSlist) then
		    Append(~RHSlist, rhs);
		end if;
		Append(~toRemove,[i,rhs]);
	    end if;
	end for;

	// remove cases covered by Thue solver
	toRemoveNew:= [i[1] : i in toRemove];
	afplistNew:= [afplist[i] : i in [1..#afplist] | i notin toRemoveNew];
	afplist:= afplistNew;
	GL2Zcases[i]:= #afplist;
    end for;

    // determine which action of GL2(Z) yields least number of ideal equations
    min,ind:= Min(GL2Zcases);
    clist:= GL2Zclists[ind]; // redefine clist
    printf hash cat " Total time to determine optimal GL2(Z) action: %o \n", Cputime(t2);
    printf hash cat " New Thue-Mahler equation coefficients: %o \n", clist;

    f, enterTM, RemainingCases:= prep0(hash,OutFiles,LogFile,clist,N:printOutput:=true);
    assert enterTM;
    K<th>:=NumberField(f);
    OK:=MaximalOrder(K);
    th:=OK!th;
    fieldKinfo:= rec<FieldInfo | field:= K,gen:= th,ringofintegers:= OK,minpoly:= f>;

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

    // general setup and assertions
    Zx<x_>:= PolynomialRing(Integers());
    QUV<U,V>:=PolynomialRing(Rationals(),2);
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
    // remove ideal equations which have exponent 0 on all prime ideals by generating
    // corresponding Thue equations to be solved
    toRemove:= [];
    RHSlist:= [];
    for i in [1..#afplist] do
	fplist:= afplist[i][4];
	if IsEmpty(fplist) then
	    a:= afplist[i][1]`newa;
	    adu:= afplist[i][1]`adu;
	    primelist:= afplist[i][2];
	    ideal_a:= afplist[i][3];
	    v:= #primelist;
	    tt:= [Valuation(Norm(ideal_a), primelist[i]) : i in [1..v]];
	    assert Norm(ideal_a) eq Abs(a)*&*[primelist[i]^tt[i] : i in [1..v]];
	    rhs:= Integers()! a*&*[primelist[i]^tt[i] : i in [1..v]];
	    tf,alpha:=IsPrincipal(ideal_a); // verify ideal_a is principal
	    if (tf) and (rhs notin RHSlist) then
		Append(~RHSlist, rhs);
	    end if;
	    Append(~toRemove,[i,rhs]);
	end if;
    end for;

    // remove cases covered by Thue solver
    toRemoveNew:= [i[1] : i in toRemove];
    afplistNew:= [afplist[i] : i in [1..#afplist] | i notin toRemoveNew];
    afplist:= afplistNew;
    printf hash cat " Total time to remove ideal equations covered by Thue solver: %o \n",
	   Cputime(t6);

    // store Thue equations to be solved in "ThueEqToSolve.txt"
    if #RHSlist eq 1 then
	fprintf ThueEqToSolve, hash cat " Thue equation to be solved: %o \n", fclist;
	fprintf ThueEqToSolve, hash cat " Right-hand side: " cat Sprint(RHSlist[1])
				 cat "\n";
    elif #RHSlist gt 1 then
	fprintf ThueEqToSolve, hash cat " Thue equation to be solved: %o \n", fclist;
	fprintf ThueEqToSolve, hash cat " Right-hand side: " cat
				 &cat[Sprintf( "%o, ", RHSlist[i], RHSlist[i]): i in [1..#RHSlist-1]] cat Sprint(RHSlist[#RHSlist]) cat "\n";
    end if;

    if IsEmpty(afplist) then
	fprintf NoSUnitEqNeeded,
		hash cat " No S-unit equations to resolve for this Thue-Mahler equation \n";
    else
	printf hash cat " Number of ideal equations: %o \n", #afplist;
	t7:= Cputime();
	alphgamlist:= prep2(fieldKinfo,ClK,afplist);
	printf hash cat " Total time to compute all S-unit equations: %o \n", Cputime(t7);
	printf hash cat " Number of S-unit equations: %o \n", #alphgamlist;

	if IsEmpty(alphgamlist) then
	    fprintf NoSUnitEqNeeded,
		    hash cat " No S-unit equations to resolve for this Thue-Mahler equation\n";
	else
	    assert #alphgamlist ne 0;
	    complexPrec:= 400;
	    t8:= Cputime();
	    UpperBounds(fieldKinfo,clist,~alphgamlist,complexPrec);
	    printf hash cat " Total time to compute initial height bounds: %o \n", Cputime(t8);

	    for j in [1..#alphgamlist] do
		idealEq:= alphgamlist[j];
		jhash:= hash cat "Case" cat IntegerToString(j);
		fprintf SUnitEq,
			jhash cat " Optimal Thue-Mahler equation coefficients: %o \n", clist;
		fprintf SUnitEq, jhash cat " Minimal polynomial for K: %o \n", fclist;
		fprintf SUnitEq, jhash cat " Class number: %o \n", ClK`classnumber;
		if #fieldKinfo`fundamentalunits eq 1 then
		    fprintf SUnitEq, jhash cat " Fundamental unit: " cat
				     Sprint(K!fieldKinfo`fundamentalunits[1]) cat "\n";
		elif #fieldKinfo`fundamentalunits eq 2 then
		    fprintf SUnitEq, jhash cat " Fundamental units: " cat
				     Sprint(K!fieldKinfo`fundamentalunits[1]) cat ", " cat
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
	    end for;
	    fprintf SUnitEq, hash cat " Total cases: %o \n", #alphgamlist;
	end if;
    end if;
end if;

printf hash cat " Total time: %o\n", Cputime(t0);
UnsetLogFile();
exit;
