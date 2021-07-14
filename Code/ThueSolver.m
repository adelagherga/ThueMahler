/*
ThueSolver.m

Author: Adela Gherga <adelagherga@gmail.com>
Copyright © 2021, Adela Gherga, all rights reserved.
Created:  3 July 2021

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

prep0:= function(clist,rhs_values)

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
    Zx<x>:= PolynomialRing(Rationals());

    // general setup for Thue-Mahler solver
    assert &and[c in Integers() : c in clist];
    c0:=Integers()!clist[1];
    assert c0 ne 0;
    n:=#clist-1;
    assert n eq 3;

    // generate the relevant Thue-Mahler polynomial
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

    ThueF:= Thue(ChangeRing(f,Integers()));
    rhssol:= [];

    for rhs in rhs_values do
	sol:= Solutions(ThueF,rhs);
	Append(~rhssol, <rhs,sol>);
    end for;

    return rhssol;
end function;

CommaSplit:= Split(set,","); // split bash input by ","
BracketSplit:= Split(set,"[]"); // split bash input by "[" and "]"
RBracketSplit:= Split(set,"()"); // split bash input by "(" and ")"

// delimiter for form
assert CommaSplit[1][2] eq "(" and CommaSplit[4][#CommaSplit[4]-1] eq ")";
// delimiter for rhs
assert CommaSplit[5][2] eq "[";
assert (#BracketSplit eq 3) and (#RBracketSplit eq 3);

// convert bash input for optimal form, min poly into a sequence of integers
clist:= [StringToInteger(i) : i in Split(RBracketSplit[2],",")];
rhs_values:= [StringToInteger(i) : i in Split(BracketSplit[2],",")];

// add original form to hash in .csv format
hash:= set;
printf hash cat "\n";

rhssol:= prep0(clist,rhs_values);


	for s in sol do
	    strSol:=strSol cat "," cat SeqEnumToString(s : Quotations:=false);
	end for;
