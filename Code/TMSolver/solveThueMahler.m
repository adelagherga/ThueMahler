/*
solveThueMahler.m

This solves a_0 X^d + ... + a_d Y^d = a * p_1^{z_1} ... p_v^{z_v} subject to
the assumptions that X, Y are integers and gcd(X,Y) = gcd(a_0,Y) = 1.

Authors
    Adela Gherga <adelagherga@gmail.com>
    Samir Siksek <samir.siksek@gmail.com>
Created
    14 June 2022
*/

load "./multGroup.m";
load "./equationsInK.m";
load "./reducedBound.m";
load "./sieveInfo.m";
load "./sift.m";
load "./solutionVectors.m";
SetAutoColumns(false);
SetColumns(235);

solveThueMahler:=function(alist,a,primelist : verb:=false)
    /*
      Solves a_0 X^d + ... + a_d Y^d = a p_1^{z_1} ... p_v^{z_v}
      subject to the assumptions that X, Y are integers and
      gcd(X,Y) = gcd(a_0,Y) = 1.

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
              A list of solutions [X, Y, z_1,...,z_v] to the Thue-Mahler
	      equation.
   */
    printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
    printf "alist:=%o; a:=%o; primelist:=%o; \n",alist,a,primelist;
    printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
    tauDeltaList:=equationsInK(alist,a,primelist);
    if (#tauDeltaList eq 0) then
	printf "No S-unit equations to solve!\n";
	printf "Done solving the Thue-Mahler equation.\n";
	printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";
	printf "++\n";
    	return {};
    elif (#tauDeltaList eq 1) then
	printf "We have %o S-unit equation to solve.\n",#tauDeltaList;
	printf "The rank is %o.\n",Sort([#pr[2] : pr in tauDeltaList]);
    else
	printf "We have %o S-unit equations to solve.\n",#tauDeltaList;
	printf "The ranks are %o.\n",Sort([#pr[2] : pr in tauDeltaList]);
    end if;
    a0:=alist[1];
    K:=Universe([pr[1] : pr in tauDeltaList]
		cat &cat[pr[2] : pr in tauDeltaList]);
    K:=NumberField(K);
    theta:=K.1;
    smallInfs:=smallSieveInfo([* *],a0,theta,200);
    sols:={};
    eqncount:=0;
    printf "++++++++++++++++++++++++++++++++++\n";
    for pr in tauDeltaList do
	eqncount:=eqncount+1;
	printf "Working on equation number %o...\n",eqncount;
	tau:=pr[1];
	deltaList:=pr[2];
	vecB,S,range:=reducedBound(tau,deltaList : verb:=verb);
	print "S is ",S;
	printf "The range is %o.\n",range;
	cBfsq:= &+[i^2 : i in vecB];
	printf "The bound on the norm squared of (b1,..,br) is %o.\n",cBfsq;
	printf "Applying the Dirichlet sieve to equation number %o ",eqncount;
	printf "out of %o.\n",#tauDeltaList;
	if cBfsq gt 500000 then
	    qBound:= 500;
	else
	    qBound:=200;
	end if;
	smallInfs:=smallSieveInfo(smallInfs,a0,theta,qBound);
	Zr,bigInfs:=bigSieveInfo(tau,deltaList,smallInfs);
	vecs:=sift(tau,deltaList,Zr,Zr,Zr!0,S,range,cBfsq,bigInfs,1);
	printf "Finished applying the Dirichlet sieve to equation number %o.\n",
	       eqncount;
	printf "++++++++++++++++++++++++++++++++++\n";
	sols:=sols join solutionVectors(alist,a,primelist,tau,deltaList,vecs);
    end for;
    printf "Done solving the Thue-Mahler equation.\n";
    printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
    return sols;
end function;
