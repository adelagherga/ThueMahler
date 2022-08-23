/*
solveThueMahlerAll.m

This solves a_0 X^d + ... + a_d Y^d = a * p_1^{z_1} ... p_v^{z_v} subject to
the assumptions that X, Y are integers and gcd(X,Y) = 1. Note that we do not
assume a_0, Y are coprime here.

Authors
    Adela Gherga <adelagherga@gmail.com>
    Samir Siksek <samir.siksek@gmail.com>
Created
    22 August 2022
*/

load "./solveThueMahler.m";

makeMonic:=function(alist,a,primelist)
    /*
      Determine all possible values of b = gcd(Y,a_0) and apply the
      corresponding linear change of variables to the the Thue--Mahler form
      a_0 X^d + ... + a_d Y^d = a p_1^{z_1} ... p_v^{z_v}, ensuring a_0 = 1.
      This is necessary in order to compute all solutions subject to the
      assumptions that X, Y are coprime integers and Y, a_0 are not necessarily
      coprime.

      Parameters
          alist: SeqEnum
              A list of coefficients a_0, a_1,...,a_d.
          a: RngIntElt
          primelist: SeqEnum
              A list of rational primes p_1, p_2,...,p_v.
      Returns
          newablist: SeqEnum
	      A list of sets (new_a,blist) where
	      X^d + ... + a_d Y^d = new_a p_1^{z_1} ... p_v^{z_v} under the
	      change of variables arising from b = gcd(a_0,Y), where b is an
	      integer element of blist.
   */
    assert &and[IsPrime(p) : p in primelist];
    assert &and[a_i in Integers() : a_i in alist];
    a0:=Integers()!alist[1];
    assert a0 ne 0;
    d:=#alist-1;
    assert d ge 3;
    v:=#primelist;
    qlist:=[f[1] : f in Factorization(a)];
    ordpa:=[[0..Valuation(a0,primelist[i])] : i in [1..v]];
    ordqa:=[[0..Min(Valuation(a,qlist[i]),Valuation(a0,qlist[i]))]
	    : i in [1..#qlist]];

    prod1:={1};
    prod2:={1};
    expCombos1:=CartesianProduct(ordpa);
    for c in expCombos1 do
        prod1:=prod1 join {&*{primelist[i]^c[i] : i in [1..v]}};
    end for;
    if (a ne 1) then
        expCombos2:=CartesianProduct(ordqa);
        for c in expCombos2 do
            prod2:=prod2 join {&*{qlist[i]^c[i] : i in [1..#qlist]}};
        end for;
    end if;
    cD:=[];
    for p1 in prod1 do
        for p2 in prod2 do
            Append(~cD,p1*p2);
        end for;
    end for;
    Sort(~cD);

    newAs:=[];
    for i in [1..#cD] do
        b:=cD[i];
        new_a:=(a*a0^(d-1))/b^d;
        for j in [1..v] do
	    // Divide out factors of p_i from a; ensure gcd(a,p_1,...,p_v) = 1.
            new_a:=new_a/(primelist[j]^Valuation(new_a,primelist[j]));
        end for;
        newAs[i]:=new_a;
    end for;
    newAs2:=[];
    for i in [1..#cD] do
        if newAs[i] notin newAs2 then
            Append(~newAs2,newAs[i]);
        end if;
    end for;
    Sort(~newAs2);

    newablist:=[];
    for i in [1..#newAs2] do
        newablist[i]:=[* [newAs2[i]] *];
        newablist[i][2]:=[];
        for j in [1..#cD] do
            if newAs[j] eq newAs2[i] then
                Append(~newablist[i][2],cD[j]);
            end if;
        end for;
    end for;
    return newablist;
end function;

recoverXY:=function(alist,a,primelist,x,y,b)
    /*
      Given a_0 X^d + ... + a_d Y^d = a * p_1^{z_1} ... p_v^{z_v} and a solution
      (x,y) to this equation under a linear change of variables associated to
      b = gcd(a_0,Y), recover the solution X, Y, where possible.

      Parameters
          alist: SeqEnum
              A list of integer coefficients a_0, a_1,...,a_d.
          a: RngIntElt
          primelist: SeqEnum
              A list of rational primes p_1, p_2,...,p_v.
          x: RngIntElt
          y: RngIntElt
          b: RngIntElt
      Returns
          sol: SetEnum
              A list of solutions [X,Y,z_1,...,z_v].
   */
    d:=#alist-1;
    ZUV<U,V>:=PolynomialRing(Integers(),2);
    F:=&+[alist[i+1]*U^(d-i)*V^i : i in [0..d]];
    a0:=alist[1];

    if (IsDivisibleBy(b*x,a0) eq false) then
	return {};
    end if;
    sol:=[Integers()!(b*x/a0),Integers()!(b*y)];
    if (GCD(sol[1],sol[2]) ne 1) then
	return {};
    end if;
    Fsol:=Evaluate(F,sol);
    if (Fsol eq 0) then
	return {};
    end if;
    if (IsDivisibleBy(Fsol,a) eq false) then
	return {};
    end if;
    Fsol:=Fsol div a;
    zlist:=[];
    for p in primelist do
	z:=Valuation(Fsol,p);
	Append(~zlist,z);
	Fsol:=Fsol div p^z;
    end for;
    if Fsol eq 1 then
	if IsEven(d) then
	    return {sol cat zlist,[-sol[1],-sol[2]] cat zlist};
	else
	    return {sol cat zlist};
	end if;
    elif Fsol eq -1 then
	if IsOdd(d) then
	    return {[-sol[1],-sol[2]] cat zlist};
	end if;
    end if;
end function;

solveThueMahlerAll:=function(alist,a,primelist : verb:=false)
    /*
      Solves a_0 X^d + ... + a_d Y^d = a p_1^{z_1} ... p_v^{z_v}
      subject to the assumptions that X, Y are integers and
      gcd(X,Y) = 1, with a_0, Y not necessarily coprime.

      Parameters
          alist: SeqEnum
              A list of coefficients a_0, a_1,...,a_d.
          a: RngIntElt
          primelist: SeqEnum
              A list of rational primes p_1, p_2,...,p_v.
          verb: BoolElt
              A true/false value. If set to true, this function returns status
	      updates as it proceeds.
      Returns
          sols: SetEnum
              A list of solutions [X,Y,z_1,...,z_v] to the Thue-Mahler
	      equation.
   */
    assert &and[IsPrime(p) : p in primelist];
    assert &and[a_i in Integers() : a_i in alist];
    a0:=Integers()!alist[1];
    assert a0 ne 0;
    d:=#alist-1;
    assert d ge 3;
    QUV<U,V>:=PolynomialRing(Rationals(),2);
    Qx<x>:=PolynomialRing(Rationals());
    F:=&+[alist[i+1]*U^(d-i)*V^i : i in [0..d]];
    assert IsHomogeneous(F);
    f:=a0^(d-1)*Evaluate(F,[x/a0,1]);
    assert IsMonic(f);
    assert Degree(f) eq d;
    assert IsIrreducible(f);
    falist:=Reverse(Coefficients(f));
    assert &and[a_i in Integers() : a_i in falist];
    falist:=[Integers()!a_i : a_i in falist];
    newablist:=makeMonic(alist,a,primelist);

    allSols:={};
    for i in [1..#newablist] do
        new_a:=Integers()!newablist[i][1][1];
        blist:=newablist[i][2];
	assert &and[Valuation(new_a,p) eq 0 : p in primelist];
	time sols:=solveThueMahler(falist,new_a,primelist : verb:=verb);
        for b in blist do
            for sol in sols do
                x:=sol[1];
		y:=sol[2];
		allSols:=allSols join recoverXY(alist,a,primelist,x,y,b);
	    end for;
	end for;
    end for;
    return allSols;
end function;
