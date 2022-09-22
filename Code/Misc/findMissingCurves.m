/*
findMissingCurves.m

These functions determine the corresponding Thue--Mahler form of a given
elliptic curve. This is primarily used when the Thue--Mahler-form-to-ellptic-
curve computation misses forms from the LMFDB.

Authors
    Adela Gherga <adelagherga@gmail.com>
Created
    18 September 2022
*/

findMissingForms:=function(N,aInvs)
    /*
      Computes the corresponding Thue--Mahler form of a given elliptic curve.

      Parameters
          N: RngIntElt
              The conductor of the elliptic curve.
          aInvs: SeqEnum
              The a-invariants defining the elliptic curve.
      Returns
          alist: SeqEnum
              A list of coefficients a_0, a_1,...,a_d defining the Thue--Mahler
	      form.
          DF: RngIntElt
              The discriminant of the Thue--Mahler form.
   */
    QUV<U,V>:=PolynomialRing(Rationals(),2);
    Qx<x>:= PolynomialRing(Rationals());
    E:=MinimalModel(EllipticCurve(aInvs));
    assert Conductor(E) eq N;
    c4:=Integers()!(cInvariants(E)[1]);
    c6:=Integers()!(cInvariants(E)[2]);
    deltaE:=Discriminant(E);
    if deltaE lt 0 then
	delta:=1;
    else
	delta:=0;
    end if;
    D:=&*[p^Min(Floor(Valuation(c4,p)/2),Floor(Valuation(c6,p)/3))
	  : p in PrimeDivisors(GCD(c4,c6))];
    X:=Integers()!(c4/D^2);
    Y:=Integers()!(c6/D^3);
    M:=Integers()!(D^(-6)*2^6*3^3*Abs(deltaE));
    assert Y^2 eq (X^3 + (-1)^(delta+1)*M);
    M1:=&*[p^(Valuation(M,p)) : p in PrimeDivisors(X)];
    M2:=&*[p^(Valuation(M,p))
	   : p in PrimeDivisors(M) | p notin PrimeDivisors(X)];
    assert M eq M1*M2;
    a1:=&*[p^(Floor((Valuation(M,p)-1)/2)) : p in PrimeDivisors(M1)];
    if (Valuation(X,3) eq 0) and (Valuation(M,3) mod 2 eq 0) and
       (Valuation(M,3) ge 4) then
	a2:=3^(-1)*&*[p^(Floor(Valuation(M,p)/2)) : p in PrimeDivisors(M2)];
    else
	a2:=&*[p^(Floor(Valuation(M,p)/2)) : p in PrimeDivisors(M2)];
    end if;
    a:=a1*a2;
    assert IsDivisibleBy(M1,a1^2);
    assert IsDivisibleBy(M2,a2^2);
    assert IsDivisibleBy(X,a1);
    assert IsDivisibleBy(Y,a1^2);
    X1:=Integers()!(X/a1);
    K:=Integers()!(M/a^2);
    assert ((Y^2-X^3) eq (-1)^(delta+1)*K*a^2);
    B:=Integers()! (InverseMod(a2,Abs(X)^3)*Integers()!(-Y/a1)) mod Abs(X)^3;
    assert ((a*B+Y) mod Abs(a1*X^3)) eq 0;
    b0:=Integers()!(a*B+Y)/X;
    c0:=Integers()!(b0^2-X)/a;
    d:=Integers()!(b0*c0-2*B)/a;
    alist:=[a,3*b0,3*c0,d];
    F:=&+[alist[i+1]*U^(3-i)*V^i : i in [0..3]];
    assert IsHomogeneous(F);
    DF:=Discriminant(Evaluate(F,[x,1]));
    assert DF eq (108/a^2)*(X^3-Y^2);
    if (Valuation(M,3) ge 3) then
	if ((Valuation(X*Y,3) eq 0) or (Valuation(Y,3) ge 3)) then
	    alist:=[Integers()!(a/3),b0,c0,Integers()!(d/3)];
	end if;
    else
	alist:=[a,3*b0,3*c0,d];
    end if;
    F:=&+[alist[i+1]*U^(3-i)*V^i : i in [0..3]];
    assert IsHomogeneous(F);
    DF:=Discriminant(Evaluate(F,[x,1]));
    return alist,Integers()!DF;
end function;
