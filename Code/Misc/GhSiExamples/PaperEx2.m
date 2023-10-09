/*
PaperEx2.m

This function solves the Thue--Mahler equations defined in the Example 2 of the
GhSi Thue--Mahler paper, computes the corresponding elliptic curves, and outputs
the logfile and elliptic curve data in seperate files.

Returns
    OutFile: MonStgElt
        A .csv file named "Example2Out.csv" containing, for each elliptic curve
	E, the row "N,aInvariants(E),alist,a,primelist,sol". If there are no
	elliptic curves corresponding to this set, no such file is created.
    LogFile: MonStgElt
        A .txt file named "Example2Log.txt" containing all output, timings, and
	solutions.
Authors
    Adela Gherga <adelagherga@gmail.com>
    Samir Siksek <samir.siksek@gmail.com>
Created
    14 June 2022
*/

ChangeDirectory("../../TMSolver");
load "./solveThueMahler.m";
LogFile:="../../GhSiData/Example2/Example2Log.txt";
ECFile:="../../GhSiData/Example2/Example2ECs.csv";
SetOutputFile(LogFile);

convertTMToEllipticCurves:=function(N,alist,sols)
    /*
      Determine elliptic curves over Q of conductor N associated to the
      solutions of the Thue--Mahler form
      a_0 X^d + ... + a_d Y^d = a p_1^{z_1} ... p_v^{z_v}. Here, all elliptic
      curves have no nontrivial rational 2-torsion points.

      Parameters
          N: RngIntElt
	  alist: SeqEnum
              A list of coefficients a_0, a_1,...,a_d.
          sols: SetEnum
              A list of solutions [X,Y,z_1,...,z_v] to the Thue-Mahler
	      equation.
      Returns
          relECs: SetEnum
              A list of sets (N,aInvs,[X,Y]), where aInvs are the a-invariants
	      defining an elliptic curve of minimal model and conductor N,
	      determined by the solution [X,Y] of the Thue--Mahler form given
	      by alist.
   */
    d:=#alist-1;
    assert d eq 3;
    QXY<X,Y>:=PolynomialRing(Integers(),2);
    F:=&+[alist[i+1]*X^(d-i)*Y^i : i in [0..d]];
    a0,a1,a2,a3:=Explode(alist);
    G:=(-27*a0^2*a3+9*a0*a1*a2-2*a1^3)*X^3 +
       (-3*a1^2*a2-27*a0*a1*a3+18*a0*a2^2)*X^2*Y +
       (3*a1*a2^2-18*a1^2*a3+27*a0*a2*a3)*X*Y^2 +
       (-9*a1*a2*a3+2*a2^3+27*a0*a3^2)*Y^3;
    H:=(a1^2-3*a0*a2)*X^2 + (a1*a2-9*a0*a3)*X*Y + (a2^2-3*a1*a3)*Y^2;
    DF:=-27*a0^2*a3^2 + a1^2*a2^2 + 18*a0*a1*a2*a3 - 4*a0*a2^3 - 4*a1^3*a3;

    alpha:=Integers()!Valuation(N,2);
    beta:=Integers()!Valuation(N,3);
    assert (alpha in [0..8]);
    assert (beta in [0..5]);
    divs6N:=[D : D in Divisors(6*N) | IsSquarefree(D)];
    assert 1 in divs6N;
    ECs:=[];
    for sol in sols do
        u:=sol[1];
        v:=sol[2];
	a4:=-27*(Evaluate(H,[u,v]));
	a6:=27*(Evaluate(G,[u,v]));
        E:=[0,0,0,a4,a6];
        minE:=MinimalModel(EllipticCurve(E));
        condE:=Conductor(minE);
        Append(~ECs,<condE,aInvariants(minE),[u,v]>);
	for D in divs6N do
	    minE2:=MinimalModel(QuadraticTwist(minE,D));
	    condE2:=Conductor(minE2);
	    Append(~ECs,<condE2,aInvariants(minE2),[u,v]>);
	    twistMinE2:=MinimalModel(QuadraticTwist(minE2,-1));
	    twistCondE2:=Conductor(twistMinE2);
	    Append(~ECs,<twistCondE2,aInvariants(twistMinE2),[u,v]>);
	end for;
    end for;
    Sort(~ECs);
    relECs:={};
    for E in ECs do
	if E[1] eq N then
	    relECs:=relECs join {E};
	end if;
    end for;
    return relECs;
end function;

//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++//
// Example 2 //

// alist:=[7,1,29,-25];
// For the EC computation, the exponent on 2 can only be either 0 or 1.
Nlist:=[400044,
	800088,
	1200132,
	1600176,
	2400264,
	4800528,
	6400704,
	12801408,
	19202112,
	38404224];
primelist:=[2,3,17,37,53];
a:=1;
alist:=[17,-182,92,-12]; // This is the optimal form (a is 1 here, vs 17).

sols:=solveThueMahler(alist,a,primelist : coprime:=false);
printf "sols:=%o\n",sols;

for N in Nlist do
    printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
    printf "N:=%o; alist:=%o; a:=%o; primelist:=%o;\n",N,alist,a,primelist;
    printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
    ECs:=convertTMToEllipticCurves(N,alist,sols);
    printf "%o\n",ECs;
    for E in ECs do
	fprintf ECFile, "%o %o %o %o %o %o\n",E[1],seqEnumToString(E[2]),
		seqEnumToString(alist),IntegerToString(a),
		seqEnumToString(primelist),seqEnumToString(E[3]);
    end for;
end for;
printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
printf "Total time: %o",Cputime();
exit;
