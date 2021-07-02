/*

TM_LocalTest.m

Author: Adela Gherga <adelagherga@gmail.com>
Copyright © 2021, Adela Gherga, all rights reserved.
Created: 17 June 2021

Description: This program iterates through "RegeneratedTMFormData.csv" to
	     regenerate all S-unit equations corresponding to the Thue-Mahler forms of
	     absolute discriminant <= 10^{10}, generating  updated a-values, primelists,
	     and any additional Thue equations, via an updated local obstructions test.
	     Output is printed among "ObsRegeneratedSUnitErr.txt", "ObsNoSUnitEqPossible.csv",
	     "ObsRegeneratedThueEqToSolve.csv", and "ObsRegeneratedTMFormData.csv".
	     The file "ObsRegeneratedTMFormData.csv" will supercede the file
	     "RegeneratedTMFormData.csv" to include updated partial obstructions, a values,
	     and primelists, whereas "ObsNoSUnitEqPossible.csv" and
	     "ObsRegeneratedThueEqToSolve.csv" will be merged with
	     "NoSUnitEqPossible.csv", "RegeneratedThueEqToSolve.csv" respectively.

             This update to "ObsRegeneratedTMFormData.csv" is necessary to remove redundancy
	     arising from partial and local obstructions not verified in the previous 2
	     iterations of S-unit output, "TMFormData.csv" and "RegeneratedTMFormData.csv".
	     Using the updated "ObsRegeneratedTMFormData.csv", we will be able to remove
	     repeated TM-equations.

Commentary:  This algorithm needs to be applied once to "RegeneratedTMFormData.csv" via

nohup cat /home/adela/ThueMahler/Data/SUnitEqData/RegeneratedTMFormData.csv | parallel -j20 --joblog tmplog magma set:={} /home/adela/ThueMahler/Code/GenerateSUnitEquations/TM_LocalTest.m 2>&1 &

To do list:  N/A

Example:     N/A

*/

SeqEnumToString:= function(X : Quotations:=true)

    /*
     Description: convert a SeqEnum into a string without whitespace, enclosed by "( )" for
     		  .csv input
     Input: X:= [x_1, _2, \dots, x_n] where Type(X):= SeqEnum
            Quotiations:= boolean value determining whether to enclose the output in quotations
                          default is set to true
     Output: stX:= "\"(x_1, \dots ,x_n)\"", where Type(strX):= MonStgElt
     Example:
   */

    strX:= "(";
    for i in [1..#X] do
	if X[i] in Integers() then
	    strX:= strX cat IntegerToString(Integers()!X[i]);
	elif X[i] in Rationals() then
	    strX:= strX cat IntegerToString(Numerator(X[i])) cat "/" cat
		   IntegerToString(Denominator(X[i]));
	end if;
	if (i ne #X) then
	    strX:= strX cat ",";
	end if;
    end for;
    strX:= strX cat ")";

    if Quotations then
	strX:= "\"" cat strX cat "\"";
    end if;

    return strX;
end function;

ModpCheckDivRHS:= function(F,q)

    /*
     Description: determine whether F(X,Y) = 0 mod q has a non-trivial solution;
                  ie. when q divides the RHS
     Input: F:= polynomial F(X,Y) in question
            q:= rational integer under which the local test is performed
                that is, we search for solutions of the TM equations mod q
     Output: hasSolutions:= boolean value determining whether F(X,Y) = 0 mod q has a
     	     		    nontrivial solution
             F_qs:= all possible values of F(u,v) mod q where u,v ranges through [0..q-1]
                    NB. this set is empty if F(X,Y) = 0 mod q has a nontrivial solution
     Example:
   */

    hasSolutions:= false;
    F_qs:= [];
    if IsPrime(q) then
	Zmodq:= FiniteField(q,1);
    else
	Zmodq:= ResidueClassRing(q);
    end if;

    // set hasSolutions to true if F(X,Y) = 0 has a solution (u,v) != (0,0) mod q
    for u,v in [0..q-1] do
	if [u,v] ne [0,0] then
	    F_q:= Zmodq! (Evaluate(F,[u,v]));
	    if F_q notin F_qs then
		Append(~F_qs, F_q);
	    end if;

	    if (F_q eq 0) then
		hasSolutions:= true;
		return [], hasSolutions;
	    end if;
	end if;
    end for;

    // local, partial local obstructions are only possible where hasSolutions returns false
    // return all F(u,v) mod q values if false; will be used for further local
    // obstruction tests
    // NB. F_qs does not contain 0 in this case
    Sort(~F_qs);
    assert (IsEmpty(F_qs) eq false);
    assert IsSubsequence(F_qs,[1..q-1]: Kind:="Setwise");

    return F_qs, hasSolutions;
end function;

ModpCheck:= function(F_qs,RHSprimes,avalues,q)

    /*
     Description: determine whether F(X,Y) has a non-trivial solution
     		  ie. when q does not divide the RHS
     Input: F_qs:= all possible values F(u,v) mod p, where u,v ranges through [0..q-1]
            RHSprimes:= primes appearing on RHS of TM equation in local test
            avalues:= [a_1, \dots, a_m], fixed coefficients on RHS of F(X,Y)
            q:= rational prime under which the local test is performed
                that is, we search for solutions of the TM equations mod q
     Output: hasSolutions:= boolean values determining whether TM equation has nontrivial
                            local solutions mod q at the corresponding a value
     Example:
   */

    assert (IsEmpty(F_qs) eq false);
    hasSolutions:= [false : a in avalues];
    Zmodq:= FiniteField(q,1);
    avalues_q:= [Zmodq! a : a in avalues];

    // set hasSolutions to true if, for all (u,v) != (0,0), F(X,Y) moq q
    // can take on all values in [1..q-1]
    if (F_qs eq [1..q-1]) then
	hasSolutions:= [true : a in avalues];
    else
	if IsEmpty(RHSprimes) then
	    // when q is the only prime on the RHS; ie. a is the only possible RHS value

	    // set hasSolutions to true if F(X,Y) = a has a solution (u,v) != (0,0) moq q
	    for i in [1..#avalues] do
		if (avalues_q[i] in F_qs) then
		    hasSolutions[i]:= true;
		end if;
	    end for;
	else
	    // when q is not the only prime on the RHS

	    RHSprimesModq:= [];
	    // determine all possibilites of p^i mod q
	    for p in RHSprimes do
		pModq:= Zmodq! p;
		Append(~RHSprimesModq, [Zmodq! (p^i) : i in [0..Order(pModq)-1]]);
	    end for;
	    RHSprod:= CartesianProduct(RHSprimesModq);

	    // set hasSolutions to true if F(X,Y) has a solution (u,v) != (0,0) moq q
	    for i in [1..#avalues] do
		for prod in RHSprod do
		    prod_q:= Zmodq! (avalues_q[i]*&*prod);
		    if (prod_q in F_qs) then
			hasSolutions[i]:= true;
			break prod;
		    end if;
		end for;
	    end for;
	end if;
    end if;

    return hasSolutions;
end function;

localtest:= function(N,F,DiscF,testPrimes,avalues)

    /*
     Description: determines whether the TM equation has local or partial local obstructions
     Input: N:= conductor of corresponding elliptic curves in question
     	    F:= polynomial F(X,Y) in question
            DiscF:= discriminant of F(X,Y)
	    testPrimes:= [p_1, \dots, p_v], rational primes on RHS of F(X,Y) along with the
	    		 incomplete list of partial obstructions
            avalues:= [a_1, \dots, a_m], fixed coefficients on RHS of F(X,Y)
     Output: avaluesNew:= updated list of possible a values generated after discarding
                          those which are not possible
	     partialObstruction:= set of primes p for which solutions can only be possible
     	     			  with p having exponent 0 on RHS of the TM equation
             localobstruction:= set of primes p presenting obstructions for the TM equation
	                        that is, an obstruction exists at p as per Theorem 1 of BeGhRe
                                or no solution of the TM equation exists mod p
     Example:
   */

    // verify all a values divide the RHS
    for a in avalues do
	if (a ne 1) then
	    _, hasSol:= ModpCheckDivRHS(F,a);
	    assert hasSol;
	end if;
    end for;

    localObstruction:= [];
    partialObstruction:= [];
    for p in testPrimes do
	// search for solutions (u,v) of F(u,v) mod p
	// under the assumption that the exponent on p is > 0
	F_ps, posExpSol:= ModpCheckDivRHS(F,p);

	if (posExpSol eq false) then
	    if (p ge 3) and (Valuation(N,p) eq 1) and (DiscF mod p ne 0) then
		// verify local obstructions as per Theorem 1 of BeGhRe
		// ie. if Valuation(N,p) = 1 for p >= 3, then p | DiscF*F(u,v)
		// thus if DiscF != 0 mod p, then F(u,v) = 0 mod p for some (u,v)
		// if u = v = 0 mod p is the only solution, gcd(u,v) != 1
		// hence local obstruction at p
		Append(~localObstruction, p);
		return avalues, partialObstruction, localObstruction;
	    else
		// verify local obstructions for primes possible on RHS

		// search for solutions (u,v) of F(u,v) mod p across all a values
		// under the assumption that the exponent on p is 0
		zeroExpSol:= ModpCheck(F_ps,Exclude(testPrimes,p),avalues,p);

		// discard a value where u = v = 0 mod p is the only solution in both cases
		// gcd(u,v) != 1, hence no solutions possible at this a value
		toRemove:= [];
		for i in [1..#avalues] do
		    if (zeroExpSol[i] eq false) then
			Append(~toRemove, i);
		    end if;
		end for;
		avaluesNew:= [avalues[i] : i in [1..#avalues] | i notin toRemove];
		assert (#avaluesNew le #avalues);
		avalues:= avaluesNew;

		if (IsEmpty(avalues)) then
		    // if u = v = 0 mod p is the only solution in both cases for all a values
		    // gcd(u,v) != 1, hence local obstruction at p
	    	    Append(~localObstruction, p);
		    return avalues, partialObstruction, localObstruction;
		else
		    // if, for all a values, a solution (u,v) != (0,0) mod p exists
		    // when the exponent on p is 0
		    // but u = v = 0 mod p is the only solution
		    // when the exponent on p is > 0
		    // partial obstruction at p; can remove p from primelist
		    Append(~partialObstruction, p);
		end if;
	    end if;
	end if;
    end for;

    Sort(~partialObstruction);
    assert (IsEmpty(avalues) eq false);

   return avalues, partialObstruction, localObstruction;
end function;

prep0:= function(N,clist,fclist,partialObstruction,avalues,primelist)

    /*
     Description: verify conditions of Theorem 1 of BeGhRe for clist, N
     Input: N:= conductor of corresponding elliptic curves in question
     	    clist:= [c_0, \dots, c_n], the coefficients of F(X,Y)
	    fclist:= [1,c_1, \dots, c_n], the coefficients of monic polynomial defining
                     the number field K = Q(th)
            partialObstruction:= set of primes p for which solutions can only be possible
     	    			 with p having exponent 0 on RHS of the TM equation
            avalues:= [a_1, \dots, a_m], fixed coefficients on RHS of F(X,Y)
            primelist:= [p_1, \dots, p_v], rational primes on RHS of F(X,Y)
     Output: f:= monic polynomial defining the number field K = Q(th)
             remainingCase:= list of primelist and all corresponding a values
             		     comprising the RHS of F(x,y)
	     partialObstruction:= set of primes p for which solutions can only be possible
     	     			  with p having exponent 0 on RHS of the TM equation
             localobstruction:= set of primes p presenting obstructions for the TM equation
	                        that is, an obstruction exists at p as per Theorem 1 of BeGhRe
                                or no solution of the TM equation exists mod p
     Example:
   */

    QUV<U,V>:=PolynomialRing(Rationals(),2);
    Qx<x>:= PolynomialRing(Rationals());

    // general setup for Thue-Mahler solver
    assert &and[c in Integers() : c in clist];
    c0:=Integers()!clist[1];
    assert c0 ne 0;
    assert &and[IsPrime(p) : p in primelist];
    assert &and[a ne 0 : a in avalues];
    assert &and[GCD(a,p) eq 1 : a in avalues, p in primelist];
    n:=#clist-1;
    assert n eq 3;

    // generate the relevant Thue-Mahler polynomial
    F:=&+[clist[i+1]*U^(n-i)*V^i : i in [0..n]];
    assert IsHomogeneous(F);
    DiscF:= -27*clist[1]^2*clist[4]^2 + clist[2]^2*clist[3]^2;
    DiscF:= DiscF + 18*clist[1]*clist[2]*clist[3]*clist[4];
    DiscF:= DiscF - 4*clist[1]*clist[3]^3 - 4*clist[2]^3*clist[4];
    assert DiscF eq Discriminant(Evaluate(F,[x,1]));

    assert fclist eq ([1] cat [clist[i+1]*c0^(i-1) : i in [1..n]]);
    f:=&+[fclist[i+1]*x^(n-i) : i in [0..n]];
    c0:= Integers()!fclist[1]; // update c0
    assert c0 eq 1;
    assert IsMonic(f);
    assert Coefficients(f) eq
	   Coefficients(clist[1]^(n-1)*Evaluate(F,[x/clist[1],1]));
    assert Degree(f) eq n;
    assert IsIrreducible(f);
    assert &and[c in Integers() : c in Coefficients(f)];

    testPrimes:= primelist;
    for p in partialObstruction do
	if p notin testPrimes then
	    Append(~testPrimes, p);
	end if;
    end for;
    Sort(~testPrimes);

    // verify local and partial local obstructions
    avaluesNew,partialObstructionNew,localObstruction:=
	localtest(N,F,DiscF,testPrimes,avalues);

    assert &and[p in partialObstructionNew : p in partialObstruction];
    partialObstruction:= partialObstructionNew;

    if (IsEmpty(localObstruction) eq false) then
	// local obstructions present; do not enter TM solver
	return f,[],partialObstruction,localObstruction;
    end if;

    assert (IsEmpty(avaluesNew) eq false);
    avalues:= avaluesNew;

    // remove superflous cases where a partial obstruction at p exists
    toRemove:= [];
    for i in [1..#primelist] do
	if primelist[i] in partialObstruction then
	    Append(~toRemove, i);
	end if;
    end for;
    primelistNew:= [primelist[i] : i in [1..#primelist] | i notin toRemove];
    assert (#primelistNew le #primelist);
    assert IsSubsequence(primelistNew,primelist: Kind:="Setwise");
    primelist:= primelistNew;

    // ensure there are remaining cases not resolvable via Thue equations
    assert (IsEmpty(primelist) eq false);

    /*
    // if all cases are resolved via Thue equations
    // store corresponding Thue equations to be solved, if any
    if IsEmpty(primelist) then // no unbounded primes
	ThueToSolve:= avalues;

	enterTM:=false;
	exitline:= ",None," cat IntegerToString(#ThueToSolve);
	exitfile:= "NoSUnitEqNeeded";
	return f,enterTM,remainingCase,partialObstruction,ThueToSolve,exitline,exitfile;
    end if;
   */

    // if there are Thue-Mahler equations yet to be solved, not resolvable via Thue equations
    // generate the corresponding S-unit equations
    CaseInfoAllAs:= recformat<avalues,primelist>;
    remainingCase:= rec<CaseInfoAllAs | avalues:=avalues, primelist:= primelist>;

    // if the code has made it this far, the following must hold
    assert IsEmpty(localObstruction);
    return f,remainingCase,partialObstruction,localObstruction;

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

/*
     Description: generate all S-unit equations corresponding to N, optimal clist
     Input: set:= N,"form","optimal form","min poly","partial obstructions",
     	    	  class number,r,no ideal eq,no Thue eq,"a values","primelist"
     Output: N/A
     Example:
*/

// initialize timings array to store CPU runtime of relevant checkpoints
// store as < CPUtime, checkpoint >
t0:= Cputime();
timings:= [];

// generate relevant files; these files should already exist on the appropriate server folder
// setup for manual .csv input

// logfile tracking any errors
SUnitErr:= "/home/adela/ThueMahler/Data/SUnitEqData/ObsRegeneratedSUnitErr.txt";

// .csv format is
// N,"form",local obstruction,partial vs BeGhRe,local obstructions time,total time
// local obstruction, partial vs BeGhRe may be output as p or None
NoSUnitEqPossible:= "/home/adela/ThueMahler/Data/SUnitEqData/ObsNoSUnitEqPossible.csv";

// .csv format is
// N,"form","optimal form","RHSlist"
// optimal form is also Thue equation to solve
ThueEqToSolve:= "/home/adela/ThueMahler/Data/SUnitEqData/ObsRegeneratedThueEqToSolve.csv";

// .csv format is
// N,"form","optimal form","min poly","partial obstructions",class number,r,no ideal eq,
// no Thue eq,"a values","primelist"
SUnitEq:= "/home/adela/ThueMahler/Data/SUnitEqData/ObsRegeneratedTMFormData.csv";

SetLogFile(SUnitErr);
SetAutoColumns(false);
SetColumns(235);

// convert bash input into magma integers, sets
// bash input format is
// N,"form","optimal form","min poly","partial obstructions",class number,r,no ideal eq,
// no Thue eq,"a values","primelist"

CommaSplit:= Split(set,","); // split bash input by ","
RBracketSplit:= Split(set,"()"); // split bash input by "(" and ")"

// delimiter for form
assert CommaSplit[2][2] eq "(" and CommaSplit[5][#CommaSplit[5]-1] eq ")";
// delimiter for optimal form
assert CommaSplit[6][2] eq "(" and CommaSplit[9][#CommaSplit[9]-1] eq ")";
// delimiter for min poly
assert CommaSplit[10][2] eq "(" and CommaSplit[13][#CommaSplit[13]-1] eq ")";
assert (#RBracketSplit eq 11) or (#RBracketSplit eq 13);

N:= StringToInteger(CommaSplit[1]); // convert bash input N into an integer
hash:= CommaSplit[1] cat ","; // set hash as first element of .csv row, N

// convert bash input for optimal form, min poly into a sequence of integers
clist:= [StringToInteger(i) : i in Split(RBracketSplit[4],",")];
fclist:= [StringToInteger(i) : i in Split(RBracketSplit[6],",")];

if (#RBracketSplit eq 11) then
    assert CommaSplit[14] eq "None";
    partialObstruction:= [];
    classnumber:= StringToInteger(CommaSplit[15]);
    r:= StringToInteger(CommaSplit[16]);
    NoIdealEq:= StringToInteger(CommaSplit[17]);
    NoThueEq:= StringToInteger(CommaSplit[18]);
    avalues:= [StringToInteger(i) : i in Split(RBracketSplit[8],",")];
    primelist:= [StringToInteger(i) : i in Split(RBracketSplit[10],",")];
else
    partialObstruction:= [StringToInteger(i) : i in Split(RBracketSplit[8],",")];
    classnumber:= StringToInteger(Split(RBracketSplit[9],",")[2]);
    r:= StringToInteger(Split(RBracketSplit[9],",")[3]);
    NoIdealEq:= StringToInteger(Split(RBracketSplit[9],",")[4]);
    NoThueEq:= StringToInteger(Split(RBracketSplit[9],",")[5]);
    avalues:= [StringToInteger(i) : i in Split(RBracketSplit[10],",")];
    primelist:= [StringToInteger(i) : i in Split(RBracketSplit[12],",")];
end if;
Sort(~partialObstruction);

// add original form to hash in .csv format
hash:= hash cat "\"(" cat RBracketSplit[2] cat ")\"";
assert hash eq &cat[set[i] : i in [1..#hash]];
// print out hash in LogFile in the event of errors
printf hash cat "\n";

t1:= Cputime();
f,remainingCase,partialObstruction,localObstruction:=
    prep0(N,clist,fclist,partialObstruction,avalues,primelist);
Append(~timings,<Cputime(t1),"local obstructions">);

if (IsEmpty(localObstruction)) then

    // generate a record to store relevant info of the field K = Q(th)
    FieldInfo:= recformat<field,gen,ringofintegers,minpoly,zeta,fundamentalunits>;
    K<th>:=NumberField(f);
    OK:=MaximalOrder(K);
    th:=OK!th;
    fieldKinfo:= rec<FieldInfo | field:= K,gen:= th,ringofintegers:= OK,minpoly:= f>;

    n:= Degree(f);
    assert (n eq #clist-1);
    s,t:= Signature(K);
    assert r eq (s+t-1);
    assert (s+2*t) eq n;
    assert (r eq 1) or (r eq 2);

    afplist:= prep1(fieldKinfo,clist,remainingCase); // generate all ideal equations
    ThueToSolve:= [];

    // general setup and assertions
    Qx<x>:= PolynomialRing(Rationals());
    c0:=Integers()!clist[1];
    assert c0 ne 0;
    n:=#clist-1;
    assert n eq 3;
    assert fclist eq ([1] cat [clist[i+1]*c0^(i-1) : i in [1..n]]);
    assert f eq &+[fclist[i+1]*x^(n-i) : i in [0..n]];
    assert classnumber eq Integers()! ClassNumber(K);

    // remove ideal equations which have exponent 0 on all prime ideals by generating
    // corresponding Thue equations to be solved
    toRemove:= [];
    for i in [1..#afplist] do
	fplist:= afplist[i][4];
	if IsEmpty(fplist) then
	    a:= afplist[i][1]`newa;
	    aduset:= afplist[i][1]`adu;
	    primelist:= afplist[i][2];
	    ideal_a:= afplist[i][3];
	    v:= #primelist;
	    tt:= [Valuation(Norm(ideal_a), primelist[i]) : i in [1..v]];
	    assert Norm(ideal_a) eq Abs(a)*&*[primelist[i]^tt[i] : i in [1..v]];
	    tf,alpha:=IsPrincipal(ideal_a); // verify ideal_a is principal
	    if tf then
		for adu in aduset do
		    zz:= [tt[i] - Valuation(adu[3]*adu[1],primelist[i]) : i in [1..v]];
		    rhs:= Integers()! adu[1]*&*[primelist[i]^zz[i] : i in [1..v]];
		    assert adu[3]*rhs eq Integers()!a*&*[primelist[i]^tt[i] : i in [1..v]];
		    // store Thue equations to be solved
		    if (rhs in Integers()) and (rhs notin ThueToSolve) then
			Append(~ThueToSolve, rhs);
		    end if;
		end for;
	    end if;
	    Append(~toRemove,i);
	end if;
    end for;
    Sort(~ThueToSolve);

    // remove cases covered by Thue solver
    afplistNew:= [afplist[i] : i in [1..#afplist] | i notin toRemove];
    afplist:= afplistNew;
    assert #afplist eq NoIdealEq;
    assert IsEmpty(afplist) eq false;
    assert #ThueToSolve eq NoThueEq;

    // export Thue data into .csv file
    hash:= hash cat ",\"(" cat RBracketSplit[4] cat ")\"";
    assert hash eq &cat[set[i] : i in [1..#hash]];

    if (ThueToSolve ne []) then
	strRHS:= SeqEnumToString(Sort(ThueToSolve));
	fprintf ThueEqToSolve, hash cat "," cat strRHS cat "\n";
    end if;

    // export SUnit data into .csv file
    strFclist:= SeqEnumToString(fclist);
    if IsEmpty(partialObstruction) then
	strPartialObs:= "None";
    else
	strPartialObs:= SeqEnumToString(partialObstruction);
    end if;
    strAvalues:= SeqEnumToString(remainingCase`avalues);
    strPrimelist:= SeqEnumToString(remainingCase`primelist);

    hash:= hash cat "," cat strFclist cat "," cat strPartialObs cat ","
	   cat IntegerToString(classnumber) cat "," cat IntegerToString(r) cat
	   "," cat IntegerToString(#afplist) cat "," cat IntegerToString(#ThueToSolve)
	   cat "," cat strAvalues cat "," cat strPrimelist cat "\n";

    fprintf SUnitEq, hash;
else
    Append(~timings,<Cputime(t0),"total time">);
    assert (#timings eq 2) and (timings[1][2] eq "local obstructions");

    // export local obstruciotn into .csv file
    hash:= hash cat "," cat Sprint(localObstruction[1]) cat ",None";

    strTimings:= Sprint([t[1] : t in timings]);
    toRemove:= [];
    for i in [1..#strTimings] do
	j:= strTimings[i];
	if (j eq "[") or (j eq " ") or (j eq "]") then
	    Append(~toRemove, i);
	end if;
    end for;
    strTimings:= "," cat &cat[strTimings[i] : i in [1..#strTimings] | i notin toRemove];
    fprintf NoSUnitEqPossible, hash cat strTimings cat "\n";

end if;

UnsetLogFile();
