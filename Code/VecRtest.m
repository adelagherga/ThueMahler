/*
vecRtest.m

Author: Adela Gherga <adelagherga@gmail.com>
Copyright © 2020, Adela Gherga, all rights reserved.
Created: 26 August 2020

Description:

Commentary:

To do list:

Example:

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

prep0:= function(N,clist,fclist,partialObstruction)

    /*
     Description: Verify conditions of Theorem 1 of BeGhRe for clist, N
     Input: N:= conductor of corresponding elliptic curves in question
     	    clist:= [c_0, \dots, c_n], the coefficients of F(X,Y)
	    fclist:= [1,c_1, \dots, c_n], the coefficients of monic polynomial defining
                     the number field K = Q(th)
            partialObstruction:= set of primes p for which solutions can only be possible
     	    			 with p having exponent 0 on RHS of the TM equation
     Output: f:= monic polynomial defining the number field K = Q(th)
     	     remainingCase:= list of primelist and all corresponding a values
             		     comprising the RHS of F(x,y)
             ThueToSolve:= Thue equations to be solved, stored as [ RHS ]
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

    // verify conditions of Theorem 1 of BeGhRe
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

    RemainingCasesAllAs:= [];
    ThueToSolve:= [];

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
		// ensure there is no conflict between Theorem 1 of BeGhRe
		// and partial obstructions
		assert (((assigned x`unbounded) and (x`alpha1 ge 1)) eq false);
		if (assigned x`unbounded) and (x`alpha1 eq 0) then
		    delete x`unbounded; // update bound at p
		elif (assigned x`unbounded eq false) and (x`alpha1 ge 1) then
		    // remove extra cases at p which are now not possible
		    Append(~toRemove,i);
		end if;
	    end for;
	end if;
	psetNew:= [pset[i] : i in [1..#pset] | i notin toRemove];

	// ensure there is no conflict between Theorem 1 of BeGhRe and partial obstructions
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

    // store Thue equations to be solved, if any
    if (RHSlist ne []) then
	ThueToSolve:= RHSlist;
    end if;

    // ensure there are remaining cases not resolvable via Thue equations
    assert (IsEmpty(RemainingCases) eq false);

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
	    apset:=rec<CaseInfoAllAs | avalues:=avalues, primelist:= primelist>;
	    Append(~RemainingCasesAllAs, apset);
	end if;
    end for;

    assert #RemainingCasesAllAs eq 1; // mulitple primelists not possible
    remainingCase:= RemainingCasesAllAs[1];

    return f,remainingCase,ThueToSolve;
end function;

ijkAutL:= function(fieldLinfo)

    /*
     Description: generate automorphisms i0,j,k of L, as in Section 6.1 of Gh
     Input: fieldLinfo:= record of the splitting field L of K = Q(th)
     Output: ijk:= automorphisms i0,j,k: L -> L as in Section 6.1 of Gh
             AutL:= all automorphisms of L
     Example:
   */

    L:= fieldLinfo`field;
    tl:= fieldLinfo`gen;
    G,Aut,tau:= AutomorphismGroup(L);
    assert IsIsomorphic(G, Sym(3)) or IsIsomorphic(G, Alt(3));

    ijk:= [];
    for x in G do
	if (Order(x) eq 3) and (tau(x)(tl[1]) eq tl[2]) then
	    assert x^3 eq Id(G);
	    ijk[1]:= tau(x);
	    ijk[2]:= tau(x^2);
	    ijk[3]:= tau(x^3); // identity map
	    break x;
	end if;
    end for;

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

principalize:= function(fieldKinfo,ClK,ideal_a,fplist)

    /*
     Description: convert ideal equation (3.8), given by ideal_a, fplist, into S-unit
                  equations (3.9) via procedure of Section 3.4.2 of Gh
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
    SUnitInfo:= recformat< primelist,newa,adu,alpha,gammalist,matA,
			   vecR,ideallist,bound,pi0jk >;

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

ImageInL:= function(mapsLL,x)

    /*
     Description: Apply the automorphisms i0,j,k: L -> L to the element x in K or L,
     		  corresponding to th -> thetaL[i][j]
     Input: mapsLL:= automorphishs i0,j,k: L -> L
            x: an element of K or L
     Output: xImage:= all images of x in L under the automorphisms i0,j,k: L -> L,
                      where Image[i][j]:= x_i^(j), corresponding to th -> thetaL[i][j]
     Example:
   */

    xImage:= [];
    for i in [1..#mapsLL] do
	xImage[i]:= [];
	for j in [1..#mapsLL[i]] do
	    xImage[i][j]:= mapsLL[i][j](x);
	end for;
    end for;
    return xImage;

end function;

Ordp:= function(Fp,x)

    /*
     Description: Compute the p-adic order of x in Fp, a finite extension of Qp
     Input: Fp:= a field extension of Qp, complete with respect to the p-adic valuation
            x:= an element of Fp
     Output: ord_px:= ord_p(x), extended to Fp as ord_p(x) = 1/[Fp:Qp]*ord_p(N_{Fp/Qp}(x))
     Example:
   */

    ord_px:= (1/Degree(Fp,PrimeField(Fp)))*Valuation(Norm(x,PrimeField(Fp)));
    return ord_px;
end function;

pAdicLog:= function(primeInfo,x)

/*
     Description: Compute the p-adic log of x in Lp, a finite extension of Qp
     Input: primeInfo:= record of rational prime data and corresponding field Lp
            x:= an element of Lp
     Output: log_px:= log_p(x), the p-adic logarithm of x
     Example:
*/

    p:= primeInfo`prime;
    Lp:= primeInfo`Lp;
    k:= primeInfo`logk;
    divs:= primeInfo`logdivs;

    assert Lp eq Parent(x);
    assert Ordp(Lp,x) eq 0; // verify x is a p-adic unit

    r:=1;
    for r in divs do
	if Ordp(Lp, x^r - 1) gt 0 then
	    break r;
	end if;
    end for;
    log_px:= Log( x^(r*p^k) )/(r*p^k);

    return log_px;
end function;

thetasL:= function(fieldKinfo,fieldLinfo,ijkL,alphgamlist,pAdicPrec,hash)

    /*
     Description:
     Input: fieldKinfo:= record of the field K = Q(th)
            fieldLinfo:= record of the splitting field L of K = Q(th)
	    ijkL:= automorphisms i0,j,k: L -> L as in Section 6.1 of Gh
	    alphgamlist:= record of all S-unit equations corresponding to F(X,Y)
            pAdicPrec:= precision on all p-adic fields
     Output: allprimeInfo:= record of relevant rational prime data across all cases
             lemmattaInfo:= <alphgamlist index,p, bound 3.5.2, bound 5.5.5> where lemma 3.5.2
	     		    or lemma 3.5.5 of Gh hold, if at all
     Example:
   */

    K:= fieldKinfo`field;
    OK:= fieldKinfo`ringofintegers;
    th:=fieldKinfo`gen;
    epslist:= fieldKinfo`fundamentalunits;
    f:= fieldKinfo`minpoly;
    n:= Degree(f);
    L:= fieldLinfo`field;
    OL:= fieldLinfo`ringofintegers;

    // determine all rational primes yielding unbounded prime ideals across all cases
    allprimes:= [];
    for i in [1..#alphgamlist] do
	fplist:= alphgamlist[i]`ideallist;
	primelist:= alphgamlist[i]`primelist;
	caseprimes:= [Norm(fp) : fp in fplist];
	assert &and[p in primelist : p in caseprimes];
	for p in caseprimes do
	    if p notin allprimes then
		Append(~allprimes, p);
	    end if;
	end for;
    end for;
    Sort(~allprimes);

    allprimeInfo:= [];
    // store < C,p,3.5.2 bound,3.5.5 bound >,
    // where lemma 3.5.2 or 3.5.5 hold, respectively
    lemmattaInfo:= [];

    // generate a record to store relevant rational prime data across all cases
    pInfo:= recformat<prime,ideals,Lp,logk,logdivs,mapLLp,Kp,mapKKp,mapsLL,thetaL>;

    for l in [1..#allprimes] do
	p:= allprimes[l];
	pL:= Factorization(p*OL)[1][1]; // the chosen prime ideal above p in L
	Lp, mapLLp:= Completion(L, pL : Precision:= pAdicPrec);
	fprs:= [f[1] : f in Factorization(p*OK)]; // prime ideals in K over p
	// at least one prime ideal above p must have e(P|p)*f(P|p) = 1 to be unbounded
	assert &or([RamificationDegree(fp)*InertiaDegree(fp) eq 1 : fp in fprs]);
	eLp:= AbsoluteRamificationIndex(Lp);
	fLp:= AbsoluteInertiaDegree(Lp);
	// determine k, divisors of p^fLp - 1 for faster convergence of p-adic log, as in Ha
	divs:= Divisors(p^fLp -1);
	k:= 1;
	while (p^k)*(p-1) le eLp do
	    k:= k+1;
	end while;
	thetaL:= []; // roots of th in L, grouped according to prime factorization of p in K
	mapsLL:= []; // automorphism of L such that mapsLL[i][j](th) = thetaL[i][j]

	for i in [1..#fprs] do
	    // roots of g(t) in L, corresponding to prime ideal fprs[i] above p in K
	    thetaL[i]:= [];
	    mapsLL[i]:= [];
	    Kp, mapKKp:= Completion(K, fprs[i] : Precision:= pAdicPrec);
	    gp:= MinimalPolynomial(mapKKp(th), PrimeField(Kp));
	    allroots:= Roots(gp, Lp);
	    assert RamificationDegree(fprs[i])*InertiaDegree(fprs[i]) eq #allroots;
	    // verify multiplicity of all roots of g(t) is 1
	    assert &and[allroots[j][2] eq 1 : j in [1..#allroots]];
	    allroots:= [allroots[j][1] : j in [1..#allroots]];

            for j in [1..#allroots] do
		// determine the automorphism of L sending th to the listed root of g(t) in Lp
		vals:= [Ordp(Lp,mapLLp(ijkL[k](L!th)) - allroots[j]) : k in [1..n]];
		maxval, ind:= Max(vals);
		assert &and[vals[i] ne maxval : i in [1..n] | i ne ind];

		mapsLL[i][j]:= ijkL[ind];
		thetaL[i][j]:= ijkL[ind](L!th);
	    end for;
	    assert (IsEmpty(thetaL[i]) eq false);
	end for;
	assert &or([#thetaL[i] eq 1 : i in [1..#fprs]]);
	assert (#thetaL eq 2) or (#thetaL eq 3);

	allprimeInfo[l]:= rec<pInfo | prime:= p,ideals:= fprs,Lp:=Lp,logk:=k,logdivs:=divs,
				      mapLLp:=mapLLp,Kp:=Kp,mapKKp:=mapKKp,mapsLL:=mapsLL,
				      thetaL:=thetaL>;
    end for;

    for C in [1..#alphgamlist] do // iterate through each S-unit equation
	pi0jk:= [];
	alpha:= alphgamlist[C]`alpha;
	gammalist:= alphgamlist[C]`gammalist;
	fplist:= alphgamlist[C]`ideallist;
	caseprimes:= [Norm(fp) : fp in fplist];
	tau:= alpha*fieldKinfo`zeta;
	vecR:= alphgamlist[C]`vecR;

	for l in [1..#caseprimes] do
	    p:= caseprimes[l];
	    pindex:= [i : i in [1..#allprimeInfo] | allprimeInfo[i]`prime eq p];
	    assert #pindex eq 1;
	    pindex:= pindex[1];
	    assert allprimeInfo[pindex]`prime eq p;
	    fprs:= allprimeInfo[pindex]`ideals;
	    thetaL:= allprimeInfo[pindex]`thetaL;
	    mapsLL:= allprimeInfo[pindex]`mapsLL;
	    Lp:= allprimeInfo[pindex]`Lp;
	    mapLLp:= allprimeInfo[pindex]`mapLLp;

	    fp:= [fplist[i] : i in [1..#fplist] | Norm(fplist[i]) eq p];
	    assert (#fp eq 1) and (fp[1] in fprs);
	    fp:= fp[1];
	    assert fp eq fplist[l];
	    // determine and store index i0 of unbounded prime ideal fp above p
	    // thus thetaL[pi0][1] and mapsLL[pi0][1] correspond to fp
	    // where fp corresponds to f_1(t) such that f(t) = f_1(t)g(t) and deg(f_1(t)) = 1
	    pi0:= [i : i in [1..#fprs] | fprs[i] eq fp];
	    assert (#pi0 eq 1) and (#thetaL[pi0[1]] eq 1);
	    pi0:= pi0[1];
	    // choose indices j,k; these correspond to bounded prime ideals above p
	    indjk:= [i : i in [1..#thetaL] | i ne pi0];
	    if #thetaL eq 2 then
		// select j,k corresponding to roots of f_2(t)
		// here f(t) = f_1(t)f_2(t) where deg(f_2(t)) = 2
		assert #indjk eq 1;
		assert #thetaL[indjk[1]] eq 2;
		pj:= [indjk[1],1];
		pk:= [indjk[1],2];
		assert Ordp(Lp,mapLLp(thetaL[pj[1],pj[2]]))
		       eq Ordp(Lp,mapLLp(thetaL[pk[1],pk[2]]));
	    elif #thetaL eq 3 then
		// select j,k corresponding to root of f_2(t),f_3(t) respectively
		// here f(t) = f_1(t)f_2(t)f_3(t) where deg(f_2(t)) = deg(f_3(t)) = 1
		assert #indjk eq 2;
		assert (#thetaL[indjk[1]] eq 1) and (#thetaL[indjk[2]] eq 1);
		pj:= [indjk[1],1];
		pk:= [indjk[2],1];
	    end if;
	    assert thetaL[pj[1],pj[2]] ne thetaL[pk[1],pk[2]];
	    discf:= Integers()!Discriminant(f);
	    disctest:= ((thetaL[pi0,1] - thetaL[pj[1],pj[2]])*
			(thetaL[pi0,1] - thetaL[pk[1],pk[2]])*
			(thetaL[pj[1],pj[2]] - thetaL[pk[1],pk[2]]))^2;
	    assert Ordp(Lp,mapLLp(discf)) eq Ordp(Lp,mapLLp(disctest));
	    assert Ordp(Lp,mapLLp(discf)) eq Valuation(discf,p);

	    // generate images under the maps i0,j,k: L -> L, th -> thetaL[i][j]
	    epslistL:= [ImageInL(mapsLL,L!eps) : eps in epslist];
	    tauL:= ImageInL(mapsLL,tau);
	    delta1L:= ((thetaL[pi0,1]-thetaL[pj[1],pj[2]])*(tauL[pk[1],pk[2]]))/
		      ((thetaL[pi0,1]-thetaL[pk[1],pk[2]])*(tauL[pj[1],pj[2]]));
	    delta2L:= ((thetaL[pj[1],pj[2]]-thetaL[pk[1],pk[2]])*(tauL[pi0,1]))/
		      ((thetaL[pk[1],pk[2]]-thetaL[pi0,1])*(tauL[pj[1],pj[2]]));
	    ord_delta1L:= Ordp(Lp,mapLLp(delta1L));
	    ord_delta2L:= Ordp(Lp,mapLLp(delta2L));


	    // verify whether Lemma 3.5.2 of Gh holds
	    if (ord_delta1L ne 0) then
		l352bound:= Min(ord_delta1L,0) - ord_delta2L;
		exitline:= "\"(" cat IntegerToString(C) cat "," cat IntegerToString(p) cat
			   "," cat IntegerToString(l352bound) cat ",None)\"";
		Append(~lemmattaInfo, exitline);
	    else
		// generate images under the maps i0,j,k: L -> L, th -> thetaL[i][j]
		gammalistL:= [ImageInL(mapsLL,L!gamma) : gamma in gammalist];
		for i in [1..#gammalist] do
		    // ensure the prime ideals in L above gamma do not cancel
		    faci0:= Factorization(ideal<OL|gammalistL[i][pi0]>);
		    facj:= Factorization(ideal<OL|gammalistL[i][pj[1],pj[2]]>);
		    fack:= Factorization(ideal<OL|gammalistL[i][pk[1],pk[2]]>);
		    assert (#faci0 eq #facj) and (#facj eq #fack);
		    assert &and[facj[j][1] ne fack[j][1] : j in [1..#faci0]];
		    assert &and[faci0[j][1] ne facj[j][1] : j in [1..#faci0]];
		    assert &and[faci0[j][1] ne fack[j][1] : j in [1..#faci0]];
		end for;

		log_delta1L:= pAdicLog(allprimeInfo[pindex],mapLLp(delta1L));
		log_gammalistL:= [];
		log_epslistL:= [];

		// compute p-adic log of epslistL in Lp
		for i in [1..#epslist] do
		    epsLkj:= epslistL[i][pk[1],pk[2]]/epslistL[i][pj[1],pj[2]];
		    assert (Ordp(Lp,mapLLp(epsLkj)) eq 0);
		    log_epslistL[i]:= pAdicLog(allprimeInfo[pindex],mapLLp(epsLkj));
		end for;

		// compute p-adic log of gammalistL in Lp
		for i in [1..#gammalist] do
		    gamLkj:= gammalistL[i][pk[1],pk[2]]/gammalistL[i][pj[1],pj[2]];
		    assert (Ordp(Lp,mapLLp(gamLkj)) eq 0);
		    log_gammalistL[i]:= pAdicLog(allprimeInfo[pindex],mapLLp(gamLkj));
		end for;

		loglist:= log_gammalistL cat log_epslistL;
		assert #loglist eq (#gammalist + #epslist);
		ord_loglist:= [Ordp(Lp,loglist[i]) : i in [1..#loglist]];
		minord, ihat:= Min(ord_loglist);

		// verify whether Lemma 3.5.5 of Gh holds
		if Ordp(Lp,log_delta1L) lt minord then
		    fl:= Floor(1/(p-1) - ord_delta2L);
		    cl:= Ceiling(minord - ord_delta2L);
		    l355bound:= Max( fl, cl - 1);
		    exitline:= "\"(" cat IntegerToString(C) cat "," cat IntegerToString(p)
			       cat ",None," cat IntegerToString(l355bound) cat
			       ")\"";
		    Append(~lemmattaInfo, exitline);
		else
		    printf hash cat "," cat ord_delta2L cat"," cat vecR;
		end if;
	    end if;
	end for;
    end for;
    return allprimeInfo,lemmattaInfo;
end function;

/*
     Description: generate all S-unit equations corresponding to N, optimal clist
     Input: set:= N,"form","optimal form","min poly","partial obstructions",
     	    	  class number,r,no ideal eq,no Thue eq,"S-unit ranks",
		  local obstruction time,GL2Z action time,class group time,unit group time,
		  ideal eq time,Thue eq time,S-unit time,bound time,total time
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
SUnitErr:= "/home/adela/ThueMahler/Data/vecRtest.csv";

// .csv format is
// N,"form","optimal form","(alphgamlist index,p,lemma 3.5.2 bound,lemma 3.5.5 bound)"
//Lemmatta:= "/home/adela/ThueMahler/Data/SUnitEqData_Alpha/Lemmatta.csv";

// .csv format is
// N,"form","optimal form","RHSlist"
// optimal form is also Thue equation to solve
//ThueEqToSolve:= "/home/adela/ThueMahler/Data/SUnitEqData_Alpha/ThueEqToSolve.csv";

// .csv format is
// N,"form","optimal form","min poly","partial obstructions",class number,r,no ideal eq,
// no Thue eq,"setup time,splitting field time,class group time,
// unit group time,ideal eq time,Thue eq time,S-unit time,thetas time,total time,
// "adu","primelist","alpha"
//SUnitEq:= "/home/adela/ThueMahler/Data/SUnitEqData_Alpha/TMFormData_Alpha.csv";

SetLogFile(SUnitErr);
SetAutoColumns(false);
SetColumns(235);

// convert bash input into magma integers, sets
// bash input format is
// N,"form","optimal form","min poly","partial obstructions",class number,r,no ideal eq,
// no Thue eq,"S-unit ranks",local obstruction time,GL2Z action time,class group time,
// unit group time,ideal eq time,Thue eq time,S-unit time,bound time,total time

CommaSplit:= Split(set,","); // split bash input by ","
BracketSplit:= Split(set,"[]"); // split bash input by "[" and "]"
RBracketSplit:= Split(set,"()"); // split bash input by "(" and ")"

// delimiter for form
assert CommaSplit[2][2] eq "(" and CommaSplit[5][#CommaSplit[5]-1] eq ")";
// delimiter for optimal form
assert CommaSplit[6][2] eq "(" and CommaSplit[9][#CommaSplit[9]-1] eq ")";
// delimiter for min poly
assert CommaSplit[10][2] eq "(" and CommaSplit[13][#CommaSplit[13]-1] eq ")";
assert (#BracketSplit eq 3) or (#BracketSplit eq 5);
assert #RBracketSplit eq 7;

N:= StringToInteger(CommaSplit[1]); // convert bash input N into an integer
hash:= CommaSplit[1] cat ","; // set hash as first element of .csv row, N

// convert bash input for optimal form, min poly into a sequence of integers
clist:= [StringToInteger(i) : i in Split(RBracketSplit[4],",")];
fclist:= [StringToInteger(i) : i in Split(RBracketSplit[6],",")];

if (#BracketSplit eq 3) then
    assert CommaSplit[14] eq "None";
    partialObstruction:= [];
    classnumber:= StringToInteger(CommaSplit[15]);
    r:= StringToInteger(CommaSplit[16]);
    NoIdealEq:= StringToInteger(CommaSplit[17]);
    NoThueEq:= StringToInteger(CommaSplit[18]);
    ranks:= [StringToInteger(i) : i in Split(BracketSplit[2],",")];
else
    partialObstruction:= [StringToInteger(i) : i in Split(BracketSplit[2],",")];
    classnumber:= StringToInteger(Split(BracketSplit[3],",")[2]);
    r:= StringToInteger(Split(BracketSplit[3],",")[3]);
    NoIdealEq:= StringToInteger(Split(BracketSplit[3],",")[4]);
    NoThueEq:= StringToInteger(Split(BracketSplit[3],",")[5]);
    ranks:= [StringToInteger(i) : i in Split(BracketSplit[4],",")];
end if;

// add original form, clist to hash in .csv format
hash:= hash cat "\"(" cat RBracketSplit[2] cat ")\"," cat
       "\"(" cat RBracketSplit[4] cat ")\"";
assert hash eq &cat[set[i] : i in [1..#hash]];

// print out hash in LogFile in the event of errors
//printf hash cat "\n";

t1:= Cputime();
f,remainingCase,ThueToSolve:= prep0(N,clist,fclist,partialObstruction);
Append(~timings,<Cputime(t1),"setup">);

// generate a record to store relevant info of the field K = Q(th)
FieldInfo:= recformat<field,gen,ringofintegers,minpoly,zeta,fundamentalunits>;
K<th>:=NumberField(f);
OK:=MaximalOrder(K);
th:=OK!th;
fieldKinfo:= rec<FieldInfo | field:= K,gen:= th,ringofintegers:= OK,minpoly:= f>;

t2:= Cputime();
// generate a record to store relevant info of the splitting field L of K = Q(th)
L, tl:= SplittingField(f);
OL:= MaximalOrder(L);
tf,mapKL:= IsSubfield(K,L);
assert tf;
assert (L!th eq mapKL(th)) and (mapKL(th) in tl);
fieldLinfo:= rec<FieldInfo | field:= L, gen:=tl,ringofintegers:= OL>;
Append(~timings,<Cputime(t2),"splitting field">);

// generate all automorphisms of L, including i0,j,k as in Section 6.1 of Gh
ijkL,AutL:= ijkAutL(fieldLinfo);
assert ijkL[3](th) eq L!th; // this is the identity automorphism

t3:= Cputime();
// generate a record to store relevant class group info
ClassGroupInfo:= recformat<classgroup,classnumber,map>;
ClK:= rec< ClassGroupInfo | >;
ClK`classgroup, ClK`map:= ClassGroup(K);
Append(~timings,<Cputime(t3),"class group">);
assert classnumber eq Integers()! ClassNumber(K);
ClK`classnumber:= classnumber;

n:= Degree(f);
assert (n eq #clist-1);
s,t:= Signature(K);
assert r eq (s+t-1);
assert (s+2*t) eq n;
assert (r eq 1) or (r eq 2);

t4:= Cputime();
U,psi:= UnitGroup(OK); // generate fundamental units
Append(~timings,<Cputime(t4),"unit group">);

// express the fundamental units as elts in OK in terms of the integral basis
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

t5:= Cputime();
afplist:= prep1(fieldKinfo,clist,remainingCase); // generate all ideal equations
Append(~timings,<Cputime(t5),"ideal equations">);

// general setup and assertions
Qx<x>:= PolynomialRing(Rationals());
QUV<U,V>:=PolynomialRing(Rationals(),2);
c0:=Integers()!clist[1];
assert c0 ne 0;
n:=#clist-1;
assert n eq 3;
assert fclist eq ([1] cat [clist[i+1]*c0^(i-1) : i in [1..n]]);
assert f eq &+[fclist[i+1]*x^(n-i) : i in [0..n]];

t6:= Cputime();
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
Append(~timings,<Cputime(t6),"thue equations">);

if #ThueToSolve eq 0 then
    assert NoThueEq eq 0;
end if;

t7:= Cputime();
alphgamlist:= prep2(fieldKinfo,ClK,afplist);
Append(~timings,<Cputime(t7),"S-unit equations">);
assert #alphgamlist ne 0;

t8:= Cputime();
allprimeInfo,lemmattaInfo:= thetasL(fieldKinfo,fieldLinfo,ijkL,alphgamlist,100,hash);
Append(~timings,<Cputime(t8),"thetasL">);

Append(~timings,<Cputime(t0),"total time">);
assert #timings eq 9;

UnsetLogFile();
