/*
discList.m

<description>

Authors
    Adela Gherga <adelagherga@gmail.com>
Created
    21 September 2022
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

verifyReduced:=function(a,b,c,d,df)
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
