/*
reducedForms.m

<description>

Authors
    Adela Gherga <adelagherga@gmail.com>
Created
    16 September 2022
*/

primes23:=function(alpha,beta)
    /*
      Given ord_2(N) and ord_3(N) of an elliptic curve conductor N, determines
      the behaviour at the primes 2 and 3 in the corresponding Thue--Mahler
      forms and their discriminants.

      Parameters
          alpha: RngIntElt
	      The valuation ord_2(N).
          beta: RngIntElt
              The valuation ord_3(N).
      Returns
          prime2: SeqEnum
	      A list of all elements (alpha0,alpha1,tf) where alpha0 is the
	      possible valuation ord_2(DF), alpha1 is the possible
	      exponent on 2 in the right-hand-side of the Thue--Mahler form
	      having discriminant DF, and tf is a true/false value which is set
	      to false if alpha1 is not a lower bound.
          prime3: SeqEnum
	      A list of all elements (beta0,beta1,tf) where beta0 is the
	      possible valuation ord_3(DF), beta1 is the possible
	      exponent on 3 in the right-hand-side of the Thue--Mahler form
	      having discriminant DF, and tf is a true/false value which is set
	      to false if beta1 is not a lower bound.
   */
    assert alpha in [0..8];
    assert beta in [0..5];
    prime2:=[];
    prime3:=[];
    if (alpha eq 0) then
	Append(~prime2,<2,0,false>);
	Append(~prime2,<2,3,false>);
    elif (alpha eq 1) then
	Append(~prime2,<2,4,true>);
	Append(~prime2,<3,3,true>);
    elif (alpha eq 2) then
	Append(~prime2,<2,1,false>);
	Append(~prime2,<4,0,false>);
	Append(~prime2,<4,1,false>);
    elif (alpha eq 3) then
	Append(~prime2,<2,1,false>);
	Append(~prime2,<2,2,false>);
	Append(~prime2,<3,2,false>);
	Append(~prime2,<4,0,false>);
	Append(~prime2,<4,1,false>);
    elif (alpha eq 4) then
	Append(~prime2,<2,0,true>);
	Append(~prime2,<3,2,true>);
	Append(~prime2,<4,0,false>);
	Append(~prime2,<4,1,false>);
    elif (alpha eq 5) then
	Append(~prime2,<2,0,false>);
	Append(~prime2,<3,1,false>);
    elif (alpha eq 6) then
	Append(~prime2,<2,0,true>);
	Append(~prime2,<3,1,true>);
	Append(~prime2,<4,0,false>);
	Append(~prime2,<4,1,false>);
    elif (alpha eq 7) then
	Append(~prime2,<3,0,false>);
	Append(~prime2,<4,0,false>);
    elif (alpha eq 8) then
	Append(~prime2,<3,1,false>);
    end if;
    if (beta eq 0) then
	Append(~prime3,<0,0,false>);
    elif (beta eq 1) then
	Append(~prime3,<0,1,true>);
	Append(~prime3,<1,0,true>);
    elif (beta eq 2) then
	Append(~prime3,<3,0,false>);
	Append(~prime3,<0,0,true>);
	Append(~prime3,<1,0,true>);
    elif (beta ge 3) then
	Append(~prime3,<beta,0,false>);
	Append(~prime3,<beta,1,false>);
    end if;
    return prime2,prime3;
end function;

verifyPosReduced:=function(a,b,c,d,df)
    /*
      Verifies whether the integral binary cubic form
      a x^3 + b x^2 y + c x y^2 + d y^3, having positive discriminant,
      is reduced.

      Parameters
          a: RngIntElt
          b: RngIntElt
          c: RngIntElt
          d: RngIntElt
          df: RngIntElt
              The absolute value of the discriminant of the cubic form.
      Returns
          tf: BoolElt
	      A true/false value. This value is true if the cubic form
              is reduced and false otherwise.
   */
    Z<x,y>:=PolynomialRing(Rationals(),2);
    gcd:=GCD(GCD(GCD(a,b),c),d);
    F:=a*x^3+b*x^2*y+c*x*y^2+d*y^3;
    DF:=-27*a^2*d^2+b^2*c^2+18*a*b*c*d-4*a*c^3-4*b^3*d;
    beta0:=Valuation(DF,3);
    if (a le 0) or (b lt 0) then
        return false;
    end if;
    if (b eq 0) and (d ge 0) then
        return false;
    end if;
    if (b*c eq 9*a*d) and (d ge 0) then
        return false;
    end if;
    if ((b^2-3*a*c) eq (b*c-9*a*d)) and (b ge Abs(3*a-b)) then
        return false;
    end if;
    if ((b^2-3*a*c) eq (c^2-3*b*d)) and (a gt Abs(d)) then
        return false;
    end if;
    if ((b^2-3*a*c) eq (c^2-3*b*d)) and (a eq Abs(d)) and (b ge Abs(c)) then
        return false;
    end if;
    if (Abs(b*c-9*a*d) gt (b^2-3*a*c)) then
        return false;
    end if;
    if ((b^2-3*a*c) gt (c^2-3*b*d)) then
        return false;
    end if;
    if (DF ne df) then
	return false;
    end if;
    if &or[Valuation(DF,p) ge 3 : p in PrimeDivisors(DF) | p notin [2,3]] then
	// Verify that ord_p(DF) le 2 for p > 3.
	return false;
    end if;
    if (Valuation(DF,2) le 1) or (Valuation(DF,2) gt 4) then
        // Verify that ord_2(DF) lies in {2,3,4}.
        return false;
    end if;
    if (Valuation(DF,3) eq 2) or (Valuation(DF,3) gt 5) then
        // Verify that ord_3(DF) lies in {0,1,3,4,5}
        return false;
    end if;
    if (IsIrreducible(F/gcd) eq false) then
	return false;
    end if;
    if (beta0 ge 3) and (IsDivisibleBy(b,3) eq false) and
       (IsDivisibleBy(b,3) eq false) then
	return false;
    end if;
    return true;
end function;

posDiscriminant:=function(DFList)
    /*
      Generates all reduced, irreducible binary integral forms having positive
      discriminant DF in DFList.

      Parameters
          DFList: SetEnum
	      A list of absolute values of possible discriminants.
      Returns
          forms: SeqEnum
	      A list of reduced forms (DF,[a,b,c,d]), where DF is the
	      positive-valued discriminant of the form defined by the
	      coefficients (a,b,c,d).
   */
    forms:=[];
    R<t>:=PolynomialRing(Integers());
    X:=Max(DFList)+1;
    for a in [1..Floor(2*X^(1/4)/(3*Sqrt(3)))] do
	for b in [0..Floor(3*a/2+Sqrt(Sqrt(X)-(27*a^2)/4))] do
	    f:=-4*t^3+(3*a+2*b)^2*t^2+27*a^2*X;
            P2:=(Roots(f,RealField()))[1][1];
	    for c in [Ceiling((b^2-P2)/(3*a))..Floor(b-3*a)] do
		for df in DFList do
		    tf,U:=IsSquare(4*(b^2-3*a*c)^3-27*df*a^2);
		    if tf then
			num1:=(U-2*b^3+9*a*b*c);
			num2:=(-U-2*b^3+9*a*b*c);
			tf1,d1:=IsDivisibleBy(num1,27*a^2);
			tf2,d2:=IsDivisibleBy(num2,27*a^2);
			if tf1 then
			    if verifyPosReduced(a,b,c,d1,df) then
				Append(~forms,<df,[a,b,c,d1]>);
			    end if;
			end if;
			if tf2 then
			    if verifyPosReduced(a,b,c,d2,df) then
				Append(~forms,<df,[a,b,c,d2]>);
			    end if;
			end if;
		    end if;
		end for;
	    end for;
	end for;
    end for;
    return forms;
end function;

verifyNegReduced:=function(a,b,c,d,df)
    /*
      Verifies whether the integral binary cubic form
      a x^3 + b x^2 y + c x y^2 + d y^3, having negative discriminant,
      is reduced.

      Parameters
          a: RngIntElt
          b: RngIntElt
          c: RngIntElt
          d: RngIntElt
          df: RngIntElt
              The absolute value of the discriminant of the cubic form.
      Returns
          tf: BoolElt
	      A true/false value. This value is true if the cubic form
              is reduced and false otherwise.
   */
    Z<x,y>:=PolynomialRing(Rationals(),2);
    gcd:=GCD(GCD(GCD(a,b),c),d);
    F:=a*x^3+b*x^2*y+c*x*y^2+d*y^3;
    DF:=-27*a^2*d^2+b^2*c^2+18*a*b*c*d-4*a*c^3-4*b^3*d;
    beta0:=Valuation(DF,3);
    if (a le 0) or (b lt 0) then
	return false;
    end if;
    if (b eq 0) and (d le 0) then
        return false;
    end if;
    if ((d^2-a^2) le (b*d-a*c)) then
        return false;
    end if;
    if ((-(a-b)^2-a*c) ge (a*d-b*c)) then
        return false;
    end if;
    if ((a*d-b*c) ge ((a+b)^2+a*c)) then
        return false;
    end if;
    if (DF ne -df) then
	return false;
    end if;
    if &or[Valuation(DF,p) ge 3 : p in PrimeDivisors(DF) | p notin [2,3]] then
	// Verify that ord_p(DF) le 2 for p > 3.
	return false;
    end if;
    if (Valuation(DF,2) le 1) or (Valuation(DF,2) gt 4) then
        // Verify that ord_2(DF) lies in {2,3,4}.
        return false;
    end if;
    if (Valuation(DF,3) eq 2) or (Valuation(DF,3) gt 5) then
        // Verify that ord_3(DF) lies in {0,1,3,4,5}
        return false;
    end if;
    if (IsIrreducible(F/gcd) eq false) then
	return false;
    end if;
    if (beta0 ge 3) and (IsDivisibleBy(b,3) eq false) and
       (IsDivisibleBy(b,3) eq false) then
	return false;
    end if;
    return true;
end function;

negDiscriminant:=function(DFList)
    /*
      Generates all reduced, irreducible binary integral forms having negative
      discriminant -DF in DFList.

      Parameters
          DFList: SetEnum
	      A list of absolute values of possible discriminants.
      Returns
          forms: SeqEnum
	      A list of reduced forms (DF,[a,b,c,d]), where DF is the
	      negative-valued discriminant of the form defined by the
	      coefficients (a,b,c,d).
   */
    forms:=[];
    X:=Max(DFList)+1;
    for a in [1..Floor((16*X/27)^(1/4))] do
	for b in [0..Floor((3*a)/2+Sqrt(Sqrt(X/3)-(3*a^2)/4))] do
            if (a ge 2*b/3) then
		C:=[Ceiling(1-b)..Floor((X/(4*a))^(1/3)+(b^2/(3*a)))];
	    else
		C:=[Ceiling(1-b)..Floor((X/(4*a))^(1/3)+(b-(3*a)/4))];
            end if;
	    for c in C do
		for df in DFList do
		    tf,U:=IsSquare(4*(b^2-3*a*c)^3+27*df*a^2);
		    if tf then
			num1:=(U-2*b^3+9*a*b*c);
			num2:=(-U-2*b^3+9*a*b*c);
			tf1,d1:=IsDivisibleBy(num1,27*a^2);
			tf2,d2:=IsDivisibleBy(num2,27*a^2);
			if tf1 then
			    if verifyNegReduced(a,b,c,d1,df) then
				Append(~forms,<-df,[a,b,c,d1]>);
			    end if;
			end if;
			if tf2 then
			    if verifyNegReduced(a,b,c,d2,df) then
				Append(~forms,<-df,[a,b,c,d2]>);
			    end if;
			end if;
		    end if;
		end for;
	    end for;
	end for;
    end for;
    return forms;
end function;

modpCheckDivRHS:=function(F,q)
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

    // local, partial local obstructions are only possible where hasSolutions returns false
    // return all F(u,v) mod q values if false; will be used for further local
    // obstruction tests
    // NB. F_qs does not contain 0 in this case


   */
    FmodqList:=[];
    if IsPrime(q) then
	Zmodq:=FiniteField(q,1);
    else
	Zmodq:=ResidueClassRing(q);
    end if;
    for u,v in [0..q-1] do
	if [u,v] ne [0,0] then
	    F_q:=Zmodq!(Evaluate(F,[u,v]));
	    if F_q notin FmodqList then
		Append(~FmodqList,F_q);
	    end if;
	    if (F_q eq 0) then
		// F(u,v) = 0 mod q has a nontrivial solution.
		return [],true;
	    end if;
	end if;
    end for;
    // There are no nontrivial solutions to F(u,v) mod q when the exponent on
    // q is strictly positive.
    Sort(~FmodqList);
    assert (IsEmpty(FmodqList) eq false);
    assert IsSubsequence(FmodqList,[1..q-1]: Kind:="Setwise");
    return FmodqList,false;
end function;

modpCheck:=function(FmodqList,a,rhsPrimes,q)

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
    assert (IsEmpty(FmodqList) eq false);
    Zmodq:=FiniteField(q,1);
    a_q:=Zmodq!a;

    if (FmodqList eq [1..q-1]) then
	// Nontrivial solutions exist if F(u,v) mod q can take on all values
	// in [1..q-1], regardless of the RHS value.
	return true;
    end if;
    if IsEmpty(rhsPrimes) and (a_q in FmodqList) then
	// A nontrivial solution exists to F(u,v) = a mod q, when q is the only
	// prime on the RHS.
	return true;
    end if;
    rhsPrimesModq:=[];
    for p in rhsPrimes do
	pModq:=Zmodq!p;
	Append(~rhsPrimesModq,[Zmodq!(p^i) : i in [0..Order(pModq)-1]]);
	// Determine all possibilites of p^i mod q.
    end for;
    RHSprod:=CartesianProduct(rhsPrimesModq);
    for prod in RHSprod do
	prod_q:=Zmodq!(a_q*&*prod);
	if (prod_q in FmodqList) then
	    // A nontrivial solution exists to F(u,v) mod q when q does not
	    // divide the RHS.
	    return true;
	end if;
    end for;
    return false;
end function;

localTest:=function(N,alist,a,primelist)

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


    QUV<U,V>:=PolynomialRing(Rationals(),2);
    Qx<x>:= PolynomialRing(Rationals());
    assert &and[a_i in Integers() : a_i in alist];
    assert &and[IsPrime(p) : p in primelist];
    assert a ne 0;
    assert (#alist-1) eq 3;
    F:=&+[alist[i+1]*U^(3-i)*V^i : i in [0..3]];
    assert IsHomogeneous(F);
    DF:=Integers()!Discriminant(Evaluate(F,[x,1]));
    if (a ne 1) and (a lt 5000) then
	_,hasSol:=modpCheckDivRHS(F,a);
	// Verify the value a can divide the RHS.
	if (hasSol eq false) then
	    return {};
	end if;
    end if;
    testPrimes:=[p : p in primelist | p lt 5000];
    toRemove:=[];
    for p in testPrimes do
	// Search for solutions (u,v) of F(u,v) mod p under the assumption
	// that the exponent on p is strictly positive.
	FmodpList,hasSol1:=modpCheckDivRHS(F,p);
	if (hasSol1 eq false) then
	    if (p ge 3) and (Valuation(N,p) eq 1) and (DF mod p ne 0) then
		// If ord_p(N) = 1 for p >= 3, then p | DF*F(u,v).
		// Thus if F(u,v) = 0 mod p has only the trivial solution
		// u = v = 0 mod p, then there is a local obstruction at p since
		// gcd(u,v) != 1.
		return {};
	    end if;
	    // Search for solutions (u,v) of F(u,v) mod p under the
	    // assumption that the exponent on p is 0.
	    hasSol2:=modpCheck(FmodpList,a,Exclude(primelist,p),p);
	    if (hasSol2 eq false) then
		// There are no nontrivial solutions F(u,v) mod p whether p
		// divides the RHS or not.
		return {};
	    end if;
	    Append(~toRemove,p);
	    // Nontrivial solutions exist only when the exponent on p is 0.
	end if;
    end for;
    primelist:=[p : p in primelist | p notin toRemove];
    return {<alist,a,primelist>};
end function;

testForm:=function(N,prime2,prime3,form)
    /*
      <description>

      Parameters
          <param>: <param type>
	      <param description>
      Returns
          <param>: <param type>
	      <param description>
   */
    DF:=form[1];
    alist:=form[2];
    alpha:=Valuation(N,2);
    beta:=Valuation(N,3);
    N0:=Integers()!(N/((2^alpha)*(3^beta)));
    primelist:=PrimeDivisors(N0);
    assert (2 notin primelist) and (3 notin primelist);
    gcd:=GCD(GCD(GCD(alist[1],alist[2]),alist[3]),alist[4]);
    assert gcd in [1,2,3,6];
    alpha0:=Valuation(DF,2);
    beta0:=Valuation(DF,3);
    alpha1:=[<2,A[2],A[3]> : A in prime2 | A[1] eq alpha0];
    beta1:=[<3,B[2],B[3]> : B in prime3 | B[1] eq beta0];
    primeBounds:=[alpha1,beta1];
    N1:=Integers()!(DF/((2^alpha0)*(3^beta0)));
    assert IsDivisibleBy(N0,N1);
    for p in PrimeDivisors(N1) do
	if IsDivisibleBy(N1,p^2) then
	    assert p in PrimeDivisors(N0);
	    primeBounds[#primeBounds+1]:=[];
	    Append(~primeBounds[#primeBounds],<p,0,false>);
	    Append(~primeBounds[#primeBounds],<p,1,false>);
	end if;
    end for;
    primeBoundSets:=[];
    expCombos:=CartesianProduct([[1..#pset] : pset in primeBounds]);
    // Generate all combinations of exponent restrictions as determined above.
    for c in expCombos do
	Append(~primeBoundSets,[primeBounds[i][c[i]] : i in [1..#c]]);
    end for;
    validForms:={};
    for pSet in primeBoundSets do
	a:=1;
	primes:=primelist;
	for pS in pSet do
	    if (pS[3] eq true) then
		if (pS[1] notin primes) then
		    assert (pS[1] eq 2) or (pS[1] eq 3);
		    Append(~primes, pS[1]);
		end if;
	    else
		if (pS[1] in primes) then
		    Exclude(~primes,pS[1]);
		end if;
		a:=a*(pS[1])^(pS[2]);
	    end if;
	end for;
	Sort(~primes);
	assert &and[GCD(a,p) eq 1 : p in primes];
	if (gcd gt 1) then
	    assert (alpha in [2,3,4,6,7]) or (beta in [4,5]);
	    assert (alpha0 eq 4) or (beta0 in [4,5]);
	    tf,newa:=IsDivisibleBy(a,gcd);
	    if tf then
		newalist:=[Integers()!(a/gcd) : a in alist];
		validForms:=validForms join localTest(N,newalist,newa,primes);
	    end if;
	else
	    validForms:=validForms join localTest(N,alist,a,primes);
	end if;
    end for;
    return validForms;
end function;

findForms:=function(N)
    /*
      Determines all Thue--Mahler forms to be solved in order to compute all
      elliptic curves E of conductor N, where E has non-zero j-invariant and no
      non-trivial rational 2-torsion.

      Parameters
          N: RngIntElt
      Returns
          validForms: SeqEnum
	      A list of elements (alist,a,primelist) defining a Thue--Mahler
	      form.
   */
    assert N gt 1;
    alpha:=Valuation(N,2);
    beta:=Valuation(N,3);
    N0:=Integers()!(N/((2^alpha)*(3^beta)));
    primelist:=PrimeDivisors(N0);
    assert (2 notin primelist) and (3 notin primelist);
    if &or[Valuation(N0,p) ge 3 : p in primelist] then
	return {};
    end if;
    if (alpha ge 9) then
	return {};
    end if;
    if (beta ge 6) then
	return {};
    end if;
    prime2,prime3:=primes23(alpha,beta);
    DFList:={};
    for alpha0 in prime2 do
	for beta0 in prime3 do
	    for df in Divisors(N0) do
		DFList:=DFList join {2^(alpha0[1])*3^(beta0[1])*df};
	    end for;
	end for;
    end for;
    posForms:=posDiscriminant(DFList);
    negForms:=negDiscriminant(DFList);
    allForms:=Sort(posForms cat negForms);
    validForms:={};
    for form in allForms do
	validForms:=validForms join testForm(N,prime2,prime3,form);
    end for;
    return validForms;
end function;

findGL2Zaction:=function(a,c)
    actions:={};
    if ((a eq 0) and (Abs(c) eq 1)) then
	b:=-1/c;
	d:=0;
	assert (a*d-b*c eq 1);
	actions:=actions join {[a,b,c,d]};
    elif ((c eq 0) and (Abs(a) eq 1)) then
	d:=1/a;
	b:=0;
	assert (a*d-b*c eq 1);
	actions:=actions join {[a,b,c,d]};
    elif ((a ne 0) and (c ne 0) and (GCD(a,c) eq 1)) then
	g,d,b:=XGCD(a,c);
	b:=-b;
	assert g eq 1;
	assert (a*d-b*c eq 1);
	actions:=actions join {[a,b,c,d]};
    end if;
    return actions;
end function;

equivForm:=function(alist)

    /*
     Description: generate all possible GL2(Z) actions under which c0 lies in [1..20]
     Input: clist:= [c_0, \dots, c_n], the coefficients of F(X,Y)
     Output: GL2Zclists:= all possible coefficients of F(X,Y) under GL2(Z) action under which
                          c0 lies in the interval [1..20]
     Example:
   */

    QUV<U,V>:=PolynomialRing(Rationals(),2);
    Qx<x>:= PolynomialRing(Integers());
    assert &and[a_i in Integers() : a_i in alist];
    assert (#alist-1) eq 3;
    F:=&+[alist[i+1]*U^(3-i)*V^i : i in [0..3]];
    assert IsHomogeneous(F);

    // generate possible GL2(Z) actions under which c0 is small, avoiding Thue solver
    ThueF:=Thue(Evaluate(F,[x,1]));
    GL2Zactions:={};
    testset:=PrimesInInterval(1,200) cat [1,4,9,25];
    Sort(~testset);
    for i in testset do
	if IsEmpty(Solutions(ThueF,i)) eq false then
	    a:=Solutions(ThueF,i)[1][1];
	    c:=Solutions(ThueF,i)[1][2];
	    GL2Zactions:=GL2Zactions join findGL2Zaction(a,c);
	end if;
    end for;
    absMax:=25;
    for a,c in [-absMax..absMax] do
	if GCD(a,c) eq 1 then
	    GL2Zactions:=GL2Zactions join findGL2Zaction(a,c);
	end if;
    end for;
    GL2Zalists:=[];
    for action in GL2Zactions do
	a,b,c,d:=Explode(action);
	assert (a*d-b*c eq 1);
	GL2ZF:=Evaluate(F,[a*U+b*V,c*U+d*V]);
	newalist:=[MonomialCoefficient(GL2ZF,U^(3-i)*V^i) : i in [0..3]];
	newalist:=[Integers()!a_i : a_i in newalist];
	if (newalist[1] lt 0) then
	    newalist:=[-a_i : a_i in newalist];
	end if;
	a0:=newalist[1];
	if (#Divisors(a0) le 3) and (a0 le 5000) then
	    if (newalist notin GL2Zalists) then
		Append(~GL2Zalists,newalist);
	    end if;
	end if;
    end for;
    a0Eq1:=[newalist : newalist in GL2Zalists | newalist[1] eq 1];
    a0IsPrime:=[newalist : newalist in GL2Zalists | IsPrime(newalist[1])];
    a0Other:=[newalist : newalist in GL2Zalists |
	      newalist notin a0Eq1 and newalist notin a0IsPrime ];
    GL2Zalists:=Sort(a0Eq1) cat Sort(a0IsPrime) cat Sort(a0Other);
    if alist in GL2Zalists then
	Exclude(~GL2Zalists,alist);
    end if;
    if #GL2Zalists lt 10 then
	return [alist] cat GL2Zalists;
    else
	return [alist] cat GL2Zalists[1..10];
    end if;
end function;

optimalForm:=function(alist,a,primelist)
    GL2Zalists:=equivForm(alist);
    if #GL2Zalists eq 1 then
	return GL2Zalists[1];
    end if;
    caseNo:=[0 : i in [1..#GL2Zalists]];
    for i in [1..#GL2Zalists] do
	alist:=GL2Zalists[i];
	assert &and[IsPrime(p) : p in primelist];
	assert &and[a_i in Integers() : a_i in alist];
	a0:=Integers()!alist[1];
	assert a0 ne 0;
	d:=#alist-1;
	assert d ge 3;
	QUV<U,V>:=PolynomialRing(Rationals(),2);
	Qx<x>:=PolynomialRing(Rationals());
	F:=&+[alist[j+1]*U^(d-j)*V^j : j in [0..d]];
	assert IsHomogeneous(F);
	f:=a0^(d-1)*Evaluate(F,[x/a0,1]);
	assert IsMonic(f);
	assert Degree(f) eq d;
	assert IsIrreducible(f);
	falist:=Reverse(Coefficients(f));
	assert &and[a_i in Integers() : a_i in falist];
	falist:=[Integers()!a_i : a_i in falist];
	newablist:=makeMonic(alist,a,primelist);
	no:=0;
	for j in [1..#newablist] do
            new_a:=Integers()!newablist[j][1][1];
            blist:=newablist[j][2];
	    assert &and[Valuation(new_a,p) eq 0 : p in primelist];
	    no:=no+#equationsInK(falist,new_a,primelist);
	end for;
	caseNo[i]:=no;
    end for;
    min,ind:=Min(caseNo);
    return GL2Zalists[ind];
end function;

validForms:=findForms(N);
for form in validForms do
    print form;
    optimalForm(form[1],form[2],form[3]);
    print "-========================";
end for;




seqEnumToString:=function(X : quotes:=false)
    /*
      Convert a SeqEnum into a string without whitespace, enclosed by "[ ]" for
      .csv input

      Parameters
          X: SeqEnum
          quotes: BoolElt
              A true/false vale. If set to true, encloses the output in
	      quotations.
      Returns
          stX: MonStgElt
	      The set X as a string without whitespace.
   */
    strX:= "[";
    for i in [1..#X] do
	if X[i] in Integers() then
	    strX:=strX cat IntegerToString(Integers()!X[i]);
	elif X[i] in Rationals() then
	    strX:=strX cat IntegerToString(Numerator(X[i])) cat "/" cat
		  IntegerToString(Denominator(X[i]));
	end if;
	if (i ne #X) then
	    strX:=strX cat ",";
	end if;
    end for;
    strX:=strX cat "]";
    if quotes then
	strX:="\"" cat strX cat "\"";
    end if;
    return strX;
end function;


OutFile:="../Data/TMForms/" cat N cat ".txt";
N:=StringToInteger(N);
