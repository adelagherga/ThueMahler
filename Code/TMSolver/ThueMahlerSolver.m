/*
ThueMahlerSolver.m

Authors: Adela Gherga <adelagherga@gmail.com>
         Samir Siksek <samir.siksek@gmail.com>
Created: 14 June 2022

Description: Input: clist, a, primelist, bound
	            clist is a list of coefficients c_0,c_1,..,c_n.
		    a is an integer.
		    primelist is a list of rational primes p_1,p_2,..,p_v.
	     This solves c_0 X^n+...+c_n Y^n= a \times p_1^{z_1} ... p_t^{z_t}
	     subject to the assumptions that X, Y are coprime integers
	     and gcd(Y,c_0)=1.
	     Output: sols.
	     	     sols is a list of solutions to the Thue--Mahler equation.

Commentary:

Example: clist:=[3,2,7,2];
	 a:=1;
	 primelist:=[2,3,7,41];
	 time sols:=solveThueMahler(clist,a,primelist);
	 sols;

*/

// problem: given ideal fa in OK
// and elements alpha_1,..,alpha_n of K^*
// whose support is disjoint from fa
// return an abstract abelian group isomorphic to (OK/fa)^*
// and the images of alpha_1,..,alpha_n in this group.
// (We can use Magma's UnitGroup(quo<OK|fa>) for this,
// but it is too slow when fa is divisible by a very large
// power of a prime ideal.)

// The code below is based on Section 4.2 of
// H. Cohen, "Advanced Topics in Computational Algebraic Number Theory",
// Springer.

reduce:=function(delta,modaf,af)
    // INPUT: delta, modaf, af
    // Here delta is a non-zero element of K,
    // af is an ideal of OK, and pi is the residue class map
    // modaf : OK --> OK/af.
    // We require that
    // the denominator ideal of delta to be coprime
    // to af (otherwise we'll get an error).
    // OUTPUT: the image of delta in OK/af.
    K:=Universe([delta] cat Basis(af));
    OK:=MaximalOrder(K);
    if delta in OK then
	return modaf(delta);
    end if;
    facts:=Factorisation(Denominator(delta)*OK);
    facts:=[ fact[1] : fact in facts];
    facts:=[ fact : fact in facts | Valuation(delta*OK,fact) lt 0];
    ppow:=&*[fact^(-Valuation(delta*OK,fact)) : fact in facts];
    assert ppow+af eq 1*OK;
    beta:=CRT(af,ppow,OK!1,OK!0); // CRT=Chinese Remainder Theorem.
    // beta is congruent to 1 mod af
    // and 0 mod ppow (which the denominator
    // ideal of delta).
    assert beta in OK;
    alpha:=OK!(delta*beta);
    return modaf(alpha)/modaf(beta);
end function;

multQuo:=function(fp,a,b,alphaList)
    // INPUT: fp, a, b, alphaList
    // fp is a prime ideal,
    // a, b integers with b>a
    // alphaList is a list of elements belonging to (1+fp^a).
    //
    // OUTPUT: D, l
    // D is an abstract abelian group isomorphic to (1+fp^a)/(1+fp^b)
    // l is a list of the images of the elements in alphaList.
    assert b gt a;
    K:=NumberField(Universe(Basis(fp)));
    n:=Degree(K);
    OK:=MaximalOrder(K);
    assert &and[Valuation((alpha-1)*OK,fp) ge a : alpha in alphaList];
    fpb:=fp^b;
    _,modfpb:=quo<OK | fpb>;
    p:=Characteristic(ResidueClassField(fp));
    e:=Valuation(p*OK,fp);
    assert e ge 1;
    k0:=1+Floor(e/(p-1));
    if b gt 2*a and a lt k0 then
	D2,l2,D2gens:=$$(fp,a,2*a,alphaList);
	betaList:=[];
	assert #l2 eq #alphaList;
	for i in [1..#alphaList] do
	    alpha:=alphaList[i];
	    coords:=Eltseq(l2[i]);
	    assert #coords eq #D2gens;
	    beta:=(modfpb(alpha)/&*[ modfpb(D2gens[j])^coords[j] :
				     j in [1..#coords]  ])@@modfpb;
	    assert Valuation(beta-1,fp) ge 2*a;
	    Append(~betaList,beta);
	end for;
	s:=#OrderedGenerators(D2);
	invsD2:=Invariants(D2);
	betaList:=[ D2gens[j]^invsD2[j] : j in [1..s]  ] cat betaList;
	D1,l1:=$$(fp,2*a,b,betaList);
	r:=#OrderedGenerators(D1);
	A:=FreeAbelianGroup(r+s);
	invsD1:=Invariants(D1);
	rels:=[invsD1[i]*A.i : i in [1..r]];
	for j in [1..s] do
	    Append(~rels,A!(Eltseq(l1[j]) cat [0 : i in [1..s]])-invsD2[j]*A.(r+j));
	end for;
	D,pi:=quo<A | rels>;
	l1:=l1[s+1..#l1];
	assert #l1 eq #alphaList;
	assert #l2 eq #alphaList;
	l:=[];
	for j in [1..#alphaList] do
	    Append(~l,pi(A!(Eltseq(l1[j]) cat Eltseq(l2[j]))));
	end for;
	return D,l;
    end if;
    if b le 2*a then
	fpb:=fp^b;
	fpa:=fp^a;
	GOK:=FreeAbelianGroup(n);
	A:=sub<GOK | [ GOK!Eltseq(OK!l) :  l in Basis(fpa)]>;
	B:=sub<GOK | [ GOK!Eltseq(OK!l) :  l in Basis(fpb)]>;
	C,modB:=quo<GOK|B>;
	D:=sub<C | [modB(h) : h in OrderedGenerators(A)]>;
	assert #C eq Norm(fp)^b;
	assert #D eq Norm(fp)^(b-a);
	alphaList:=[GOK!(Eltseq(OK!(alpha-1))) : alpha in alphaList];
	assert &and[alpha in A : alpha in alphaList];
	alphaList:=[D!(modB(alpha)) : alpha in alphaList];
	Dgens:=[ OK!(Eltseq(d@@modB))  : d in OrderedGenerators(D)];
	assert &and[ d in fpa : d in Dgens];
	Dgens:=[ 1+d : d in Dgens];
	return D,alphaList, Dgens;
    end if;
    if a ge k0 then
	fpb:=fp^b;
	fpa:=fp^a;
	GOK:=FreeAbelianGroup(n);
	A:=sub<GOK | [ GOK!Eltseq(OK!l) :  l in Basis(fpa)]>;
	B:=sub<GOK | [ GOK!Eltseq(OK!l) :  l in Basis(fpb)]>;
	C,modB:=quo<GOK|B>;
	D:=sub<C | [modB(h) : h in OrderedGenerators(A)]>;
	assert #C eq Norm(fp)^b;
	assert #D eq Norm(fp)^(b-a);
	OKfp,mapToComp:=Completion(OK,fp : Precision:=b+1);
	alphaList:=[ (Log(mapToComp(alpha)))@@mapToComp : alpha in alphaList];
	assert &and[alpha in fpa : alpha in alphaList];
	alphaList:=[GOK!Eltseq(OK!alpha) : alpha in alphaList];
	assert &and[alpha in A : alpha in alphaList];
	alphaList:=[D!(modB(alpha)) : alpha in alphaList];
	return D, alphaList;
    end if;
    error("should not reach here!");
end function;

multGroupPrimePower:=function(fp,k,alphaList)
    // INPUT: fp, k, alphaList
    // fp is a prime ideal of OK,
    // k a positive integer
    // alphaList is a list of elements belonging to OK whose
    // support is coprime to fp.
    //
    // OUTPUT: D, l
    // D is an abstract abelian group isomorphic to (OK/fp)^*
    // l is a list of the images of the elements in alphaList.
    // For the algorithm see Proposition 4.2.4 of Cohen's book.
    K := NumberField(Universe(Basis(fp)));
    n := Degree(K);
    OK := MaximalOrder(K);
    assert &and[ Valuation(alpha*OK,fp) eq 0 : alpha in alphaList ];
    assert k ge 1;
    if k eq 1 then
	R, modfp := ResidueClassField(fp);
	D1, phi1 := MultiplicativeGroup(R);
	return D1, [ (modfp(alpha))@@phi1 : alpha in alphaList ];
    end if;
    q:=Norm(fp);
    fpk := fp^k;
    _, modfpk := quo<OK | fpk>;
    prec:=Ceiling(Log(k)/Log(2));
    xList:=[];
    yList:=[];
    for alpha in alphaList do
	z := modfpk(alpha);
	x := z;
	for i in [1..prec] do
	    x := x - (x^(q-1)-1)/(modfpk(q-1)*x^(q-2)) ;
	end for;
	assert x^(q-1) eq 1;
	y := (z/x)@@modfpk;
	x := x@@modfpk;
	assert Valuation(x-alpha,fp) ge 1;
	assert Valuation(y-1,fp) ge 1;
	Append(~xList,x);
	Append(~yList,y);
	// We've written each alpha as alpha \equiv x y \pmod{\fp^k}
	// where x is the Teichmueller lift of alpha,
	// and y \equiv 1 \pmod{\fp^k}.
    end for;
    R, modfp := ResidueClassField(fp);
    D1, phi1 := MultiplicativeGroup(R);
    xList := [(modfp(x))@@phi1 : x in xList];
    D2, yList := multQuo(fp,1,k,yList);
    D, phi1, phi2 := DirectSum(D1,D2);
    assert #xList eq #yList;
    return D, [ phi1(xList[i])+phi2(yList[i])  : i in [1..#xList] ];
end function;

multGroup := function(fb,alphaList)
    // INPUT: fb, alphaList
    // fb is an ideal of OK,
    // alphaList is a list of elements belonging to K^* whose
    // support is coprime to fb.
    //
    // OUTPUT: D, l
    // D is an abstract abelian group isomorphic to (OK/fb)^*
    // l is a list of the images of the elements in alphaList.
    K := NumberField(Universe(Basis(fb)));
    n := Degree(K);
    OK := MaximalOrder(K);
    facts := Factorisation(fb);
    D := AbelianGroup([]);
    alphaListImage := [D!0 : i in [1..#alphaList]];
    if #facts eq 0 then
	return D, alphaListImage;
    end if;
    _, modfb := quo< OK | fb >;
    alphaList := [ (reduce(alpha,modfb,fb))@@modfb : alpha in alphaList ];
    // Replaced each alpha by an element of OK representing the same
    // class modulo fb.
    for fact in facts do
	fp := fact[1];
	k := fact[2];
	D1, alphaListImage1 := multGroupPrimePower(fp,k,alphaList);
	D, phi, psi := DirectSum(D, D1);
	assert #alphaListImage eq #alphaListImage1;
	alphaListImage := [  phi(alphaListImage[i])+psi(alphaListImage1[i])    :  i in [1..#alphaListImage] ];
    end for;
    return D, alphaListImage;
end function;

degL:=function(K)
    // Given K=\Q(\theta) of degree at least 3, determine the smallest possible
    // degree for L=\Q(\theta_1,\theta_2,\theta_3) where
    // the \theta_i are three distinct conjugates of \theta.
    d:=Degree(K);
    assert d ge 3;
    G:=GaloisGroup(K);
    S:=[[i,j,k] : i,j,k in [1..d] | i lt j and j lt k];
    inds:=[Index(G,Stabilizer(G,l)) : l in S];
    ans:=Min(inds);
    if IsTransitive(G,3) then
	assert ans eq d*(d-1)*(d-2); // Sanity check!
    end if;
    return ans;
/*  // Slower for big d.
	subs:=Subgroups(G);
	subs:=[H`subgroup : H in subs];
	d:=Degree(K);
	S:=GSet(G,{1..d});
	subs:=[H : H in subs | #Fix(H,S) ge 3];
	dif := func<H1,H2 | Index(G,H1)-Index(G,H2)>;
	Sort(~subs,dif);
	return Index(G,subs[1]);
*/
end function;

initialBound:=function(K,theta,tau,deltaList,S)
    // We are looking at the equation (*).
    // This routine returns
    // c20, c17
    // c20 is an upper bound for
    // B:=max(|b_1|,..,|b_r|)
    // derived using the bounds of Matveev and Yu.
    // For c17 see the paper.
    OK:=MaximalOrder(K);
    assert &and[ IsPrime(P) : P in S ];
    assert #Set(S) eq #S;
    assert &and[ RamificationIndex(P) eq 1 : P in S];
    assert &and[ InertiaDegree(P) eq 1 : P in S];
    assert &join[Support(delta*OK) : delta in deltaList] eq Set(S);
    s1,s2:=Signature(K);
    assert #deltaList eq #S+s1+s2-1; // This is a sanity check.
    // We want deltaList to be a basis for the S-unit group
    // modulo torsion, and the S-unit group has rank #S+s_1+s_2-1.
    T := [ Characteristic(ResidueClassField(P)) : P in S];
    assert #Set(T) eq #T;
    d:=Degree(K);
    D:=degL(K);
    assert IsDivisibleBy(D,d);
    assert K.1 eq theta;
    assert tau in K;
    assert &and[delta in K : delta in deltaList];
    e := Exp(1);
    pi := Pi(RealField());
    htheta := AbsoluteLogarithmicHeight(theta);
    htau := AbsoluteLogarithmicHeight(tau);
    c7 := Log(2) + 2*htheta + htau ;
    c8 := 2*D*c7 ;
    r := #deltaList;
    hdeltaList := [ AbsoluteLogarithmicHeight(delta) : delta in deltaList ];
    hstarprod := &*[ (4*hs^2 + pi^2/D^2)^(1/2) : hs in hdeltaList ];
    hstarprod := hstarprod*( 4*c7^2 + pi^2/D^2 )^(1/2);
    c9 := 6*30^(r+5)*(r+2)^(5.5)*D^(r+3)*Log(e*D)*hstarprod ;
    c10 := c8 + c9*Log(e*(r+1));
    hdaggerprod := &* [ Max(2*h, 1/(16*e^2*D^2))  : h in hdeltaList];
    hdaggerprod := hdaggerprod*Max(2*c7,1/(16*e^2*D^2));
    relD := D div d;
    c11 := 0;
    for p in T do // Recall T is the set of rational primes
	// below the primes in S.
	for u in [1..relD] do
	    for v in [1..Floor(relD/u)] do
		// Looking at all pairs u, v such that uv <= D/d
		c11 := Max( c11, u^(r+1)*p^v/(v*Log(p)) );
	    end for;
	end for;
    end for;
    c12 := (16*e*D)^(2*(r+1)+2)*(r+1)^(5/2)*Log(2*(r+1)*D)*Log(2*D);
    c12 := c12*c11*hdaggerprod ;
    embeds:=InfinitePlaces(K);
    assert d eq s1+2*s2;
    assert #embeds eq s1+s2;
    c13 := (s1+s2+2*#S)/d;
    c14 := 2*htau + c13*Max(c8,c10);
    c15 := c13*Max(c9,c12);
    c16 := c14 + (3/2)*Log(2) + 2*htheta + htau ;

    c17list:= [];
    for i in [1..#S + #embeds] do
	if i le #S then
	    shortS:= [S[j] : j in [1..#S] | j ne i];
	    shortembeds:= embeds;
	else
	    shortS:= S;
 	    shortembeds:=[embeds[j] : j in [1..#embeds] | j ne (i - #S)];
	end if;
	M := [ [LocalDegree(j)*Log(AbsoluteValue(Evaluate(delta,j))) : j in shortembeds] cat
	       [Log(Norm(P)^(-Valuation(delta*OK,P))) : P in shortS] : delta in deltaList ];

	M:=Transpose(Matrix(RealField(),M));
	assert NumberOfRows(M) eq r;
	assert NumberOfColumns(M) eq r;
	Minv:=M^(-1);
	Minv:=Rows(Minv);
	Minv:=[Eltseq(r) : r in Minv];
	Minv:=&cat(Minv);
	assert #Minv eq r^2 ;
	Minv := [ AbsoluteValue(m) : m in Minv ];
	c17 := Max(Minv);
	Append(~c17list, c17);
    end for;
    c17:= Min(c17list);
    c18 := 2*d*c17*c16;
    c19 := 2*d*c17*c15;
    c20 := 2*c18 + Max(4*e^2, 2*c19*Log(c19));
    return c20, c17;
end function;

distanceLBsq:=function(LL,ww)
    // Given a lattice LL (contained in \Z^r)
    // and a vector ww in \Z^r,
    // this returns a lower bound for D(LL,ww)
    // (the shortest distance from a vector in LL
    // to ww).

    //if ww in LL then
    // return 0;
    // end if;
    ww:=AmbientSpace(Parent(ww))!ww; // Changing
    // the coefficient ring of ww to the rationals.
    n:=Rank(LL);
    assert n eq Degree(LL);
    LL:=LLL(LL);
    B:=Basis(LL);
    b1:=B[1];
    if ww in LL then
	return (2^(1-n))*Norm(b1);
    end if;
    B:=[Eltseq(b) : b in B];
    B:=[[Rationals()!a : a in b] : b in B];
    B:=Matrix(B);
    Binv:=B^-1;
    sigma:=Eltseq(ww*B^-1);
    sigma:=[AbsoluteValue(t-Round(t)) : t in sigma];
    sigma:=[t : t in sigma | t ne 0];
    sigmai0:=sigma[#sigma];
    return (2^(1-n))*sigmai0*Norm(b1);
end function;

valuationBound:=function(theta,tau,deltaList,fp,cB1)
    // We're looking at (*)
    // fp is a prime in S.
    // cB1 is an upper bound for the L^2-norm of (b_1,..,b_r).
    // This returns an upper bound for the valuation of \ord_\fp(c_0 X - \theta Y).
    if cB1 lt 1 then
        return Valuation(tau,fp);   // TO CHECK THIS IS WHAT WE WANT!
    end if;
    K:=NumberField(Universe([theta] cat [tau] cat deltaList));
    d:=Degree(K);
    assert d ge 3;
    assert theta eq K.1;
    OK:=MaximalOrder(K);
    r:=#deltaList;
    p:=Characteristic(ResidueClassField(fp));
    assert Degree(fp) eq 1;
    assert Valuation(p*OK,fp) eq 1;
    fa:=p*OK/fp;
    for fact in Factorisation(fa) do
	assert &and[Valuation(delta*OK,fact[1]) eq 0 : delta in deltaList];
    end for;
    k:=Floor(r*Log(cB1)/((d-2)*Log(p)));
    repeat
	k:=k+1;

	mpol:=MinimalPolynomial(theta);
	lcf:=LeadingCoefficient(mpol);
	assert lcf eq 1; // Surely \theta is an algebraic integer!
	hprec:=2*Valuation(Discriminant(mpol),p)+k+1;
	rts:=Roots(mpol,pAdicRing(p,hprec));
	rts:=[Integers()!r[1] : r in rts];
	rts:=[r : r in rts | Valuation((r-theta)*OK,fp) ge k];
	assert #rts ge 1;
	theta0:=rts[1]; // Thus \ord_\fp(theta-theta_0) \ge k.
	taufacts:=Factorisation(tau*OK);
	taunumfacts:=[ fact : fact in taufacts | fact[2] gt 0  ];
	// The factorization
	// of the numerator ideal of tau*OK.
	if #taunumfacts eq 0 then
	    taunum:=1*OK;
	else
	    taunum:=&*[fact[1]^(fact[2]) : fact in taunumfacts];
	end if;
	// Now taunum is the numerator ideal of \tau.
	if (taunum+fa^k) ne ((theta-theta0)*OK+fa^k) then
	    // Condition (i) of the proposition.
	    return k-1;
	end if;
	fb:=fa^k/(taunum+fa^k);
	tau0:=(theta0-theta)/tau;
	for fact in Factorisation(fb) do
	    assert Valuation(tau0*OK,fact[1]) eq 0; // Sanity check!
	end for;
	if (fb eq ideal<OK|1>) then
	    kprime:= 0;
	else
	    kprime:=Max([ Ceiling(fact[2]/Valuation(p*OK,fact[1])) :
			  fact in Factorisation(fb)]);
	end if;
	pkprime:=p^kprime;
	assert Denominator(pkprime*OK/fb) eq 1;
	if kprime ge 1 then
	    assert Denominator((p^(kprime-1)*OK)/fb) ne 1;
	end if;  // kprime really is the smallest positive
	// integer such thta fb divides p^kprime.
	Zmod:=Integers(pkprime);
	U,eps:=UnitGroup(Zmod);
	gens:=[ Integers()!(u@eps) : u in OrderedGenerators(U)];
	if IsOdd(p) and kprime ge 1 then
	    assert #gens eq 1; // Sanity check: there is a primitive root.
	end if;
	alphaList:=[K!tau0] cat [K!g : g in gens] cat [K!delta: delta in deltaList];
	D,alphaList:=multGroup(fb,alphaList);
	// D is (isomorphic to) the group (OK/fb)^* and alphaList
	// is the image in D of the original alphaList defined above,
	// i.e. the images in D of tau0, the generators of (\Z/p^\prime)^*, and the \delta_i.
	tau0im:=alphaList[1];
	alphaList:=alphaList[2..#alphaList];
	gensim:=alphaList[1..#gens];
	alphaList:=alphaList[(#gens+1)..#alphaList];
	assert #alphaList eq #deltaList;
	G,pi:=quo< D | sub<D | gensim> >;
	tau0im:=pi(tau0im);
	alphaList:=[pi(alpha) : alpha in alphaList];
	assert #alphaList eq r;
	Zr:=FreeAbelianGroup(r);
	phi:=hom<Zr->G | alphaList>;
	// This the map \phi in the paper.
	if tau0im in Image(phi) eq false then
	    // Condition (ii) of the proposition.
	    return k-1;
	end if;
	w:=tau0im@@phi;
	L:=Kernel(phi);
	ZZr:=StandardLattice(r);
	LL:=sub<ZZr | [ ZZr!(Eltseq((Zr!l))) : l in OrderedGenerators(L)]>;
	ww:=ZZr!Eltseq(Zr!w);
	DLwsq:=Norm(ClosestVectors(LL,-ww)[1]+ww);
	// This is D(L,w)^2 in the notation of the paper.
    until DLwsq gt cB1^2; // We keep increasing k until condtion (iii)
    // (or conditions (i), (ii)) are satisfied.
    return k-1;
end function;

cvp:=function(LL,vv,distSq)

    assert distSq ge 0;
    if distSq gt 0 then
	cvp:= [];
	P:= CloseVectorsProcess(LL, vv, distSq);
	while (IsEmpty(P) eq false) do
	    Append(~cvp, NextVector(P));
	end while;
    else
	if vv in LL then
	    cvp:=[vv];
	else
	    cvp:=[];
	end if;
    end if;

    return cvp;
end function;

cosetIntersect:=function(Zr,w1,L1,w2,L2)
    // Zr is the free abelian group of rank r,
    // L1, L2 are subgroups of Zr
    // w1, w2 are elements of Zr
    // This function returns
    // tf, w2, L3
    // where if tf is true, then w3+L3=(w1+L1) \cap (w2+L2)
    // and if tf is false, then (w1+L1) \cap (w2+L2)=\emptyset.
    if w1-w2 in L1+L2 eq false then
	return false, Zr!0, L1;
    end if;
    D,i1,i2,p1,p2:=DirectSum(L1,L2);
    kappa:=hom<D->Zr | [ p2(d)-p1(d)  : d in OrderedGenerators(D)]>;
    L3:=L1 meet L2;

    //if w1-w2 in Image(kappa) eq false then
    //	return false, Zr!0, L3;
    //end if;

    dv:=(w1-w2)@@kappa;
    l1:=p1(dv);
    l2:=p2(dv);
    assert w1+l1 eq w2+l2;
    return true, w1+l1, L3;
end function;

vectorsInCoset:=function(Zr,L,w,distSq)
    // L is a subgroup of Z^r
    // w is an element of Z^r
    // distSq is an integer
    // Determine all elements of L+w
    // of norm <= distSq.
    assert L subset Zr;
    r:=#Invariants(Zr);
    ZZr:=StandardLattice(r);
    ww:=ZZr!(Eltseq(w));
    LL:=sub<ZZr | [ Eltseq(Zr!l) : l in OrderedGenerators(L)] >;
    vecs:=cvp(LL,-ww,distSq);
    vecs:=[ww+vv : vv in vecs];
    vecs:=[Eltseq(ZZr!vv) : vv in vecs];
    return vecs;
end function;

detSVP:=function(Zr,L)
    // L is a subgroup of Z^r
    // return the determinant of L regarded as a lattice
    // and also the norm of the shortest vector.
    assert L subset Zr;
    r:=#Invariants(Zr);
    ZZr:=StandardLattice(r);
    LL:=sub<ZZr | [ Eltseq(Zr!l) : l in OrderedGenerators(L)] >;
    len:=Norm(ShortestVectors(LL)[1]);
    return Determinant(LL), len;
end function;

deeperSift:=function(tau,deltaList,Zr,Lcum,wcum,cB1sq,bigInfs,depth)
    rk:=#Invariants(Lcum);
    det,len:=detSVP(Zr,Lcum);

    //expect:=(1/det)*Pi(RealField())^(rk/2)*cB1sq^(rk/2)/Gamma(1+rk/2);
    if len gt 4*cB1sq or #bigInfs eq 0 then
	vecs:=vectorsInCoset(Zr,Lcum,wcum,cB1sq);
	//print "Expecting", expect;
	//print "found", #vecs;
	for I in bigInfs do
	    phiq:=I[3];
	    Tq:=I[4];
	    vecs:=[v : v in vecs | phiq(Domain(phiq)!v) in Tq];
	end for;
	//print "cut down to", #vecs;
	return vecs;
    end if;
    imLList:=[ #I[4]/Index(Zr,Kernel(I[3])+Lcum) : I in bigInfs];
    Sort(~imLList,~permut);
    bigInfs:=[* bigInfs[i^permut] : i in [1..#bigInfs] *];
    bigInf:=bigInfs[1];
    bigInfs:=bigInfs[2..#bigInfs];
    phiq:=bigInf[3];
    Tq:=bigInf[4];
    phiqLcum:=phiq(Lcum);
    phiwcum:=phiq(wcum);
    Tqcut:=[t : t in Tq | (t-phiwcum) in phiqLcum ];
    K:=Kernel(phiq);
    vecs:=[];
    for t in Tqcut do
	s:=t@@phiq;
	tf,wcumNew,LcumNew:=cosetIntersect(Zr,wcum,Lcum,s,K);
	if tf then
	    vecs:=vecs cat $$(tau,deltaList,Zr,LcumNew,wcumNew,cB1sq,bigInfs,depth+1);
	end if;
    end for;
    return vecs;
end function;

sift:=function(tau,deltaList,Zr,Lcum,wcum,SLeft,rangeLeft,cB1sq,bigInfs,depth)
    assert #rangeLeft eq #SLeft;
    rk:=#Invariants(Lcum);
    det,len:=detSVP(Zr,Lcum);
    //expect:=(1/det)*Pi(RealField())^(rk/2)*cB1sq^(rk/2)/Gamma(1+rk/2);
    if len gt 4*cB1sq then // len is the squared norm, hence use 4*squared(cB1)
	vecs:=vectorsInCoset(Zr,Lcum,wcum,cB1sq);
	//print "Expecting", expect;
	//print "found", #vecs;
	for I in bigInfs do
	    phiq:=I[3];
	    Tq:=I[4];
	    vecs:=[v : v in vecs | phiq(Domain(phiq)!v) in Tq];
	end for;
	//print "cut down to", #vecs;
	return vecs;
    end if;
    if #SLeft eq 0 then
	return deeperSift(tau,deltaList,Zr,Lcum,wcum,cB1sq,bigInfs,depth+1);
    end if;
    K:=NumberField(Universe([tau] cat deltaList));
    theta:=K.1;
    d:=Degree(K);
    assert d ge 3;
    OK:=MaximalOrder(K);
    r:=#deltaList;
    fp:=SLeft[1];
    SLeft:=SLeft[2..#SLeft];
    krange:=rangeLeft[1];
    rangeLeft:=rangeLeft[2..#rangeLeft];
    assert #SLeft eq #rangeLeft;
    kmin:=krange[1];
    kmax:=krange[2]; // k is the valution of (c_0 X- \theta Y) at fp.
    assert kmin ge 0;
    assert kmax ge kmin;
    p:=Characteristic(ResidueClassField(fp));
    assert Degree(fp) eq 1;
    assert Valuation(p*OK,fp) eq 1;
    fa:=p*OK/fp;
    for fact in Factorisation(fa) do
	assert &and[Valuation(delta*OK,fact[1]) eq 0 : delta in deltaList];
    end for;
    mpol:=MinimalPolynomial(theta);
    lcf:=LeadingCoefficient(mpol);
    assert lcf eq 1; // Surely \theta is an algebraic integer!
    henPrec:=2*(Valuation(Discriminant(mpol),p))+kmax+1;
    rts:=Roots(mpol,pAdicRing(p,henPrec));
    rts:=[Integers()!r[1] : r in rts];
    rts:=[r : r in rts | Valuation((r-theta)*OK,fp) ge kmax+1];
    assert #rts ge 1;
    theta0:=rts[1]; // Thus \ord_\fp(theta-theta_0) \ge kmax+1.
    taufacts:=Factorisation(tau*OK);
    taunumfacts:=[ fact : fact in taufacts | fact[2] gt 0  ];
    // The factorization
    // of the numerator ideal of tau*OK.
    if #taunumfacts eq 0 then
	taunum:=1*OK;
    else
	taunum:=&*[fact[1]^(fact[2]) : fact in taunumfacts];
    end if;
    // Now taunum is the numerator ideal of \tau.
    //Zr:=FreeAbelianGroup(r);
    Z1:=FreeAbelianGroup(1);
    eta:=hom<Zr->Z1 | [ Valuation(delta,fp)*Z1.1  : delta in deltaList  ]>;
    etaLcum:=eta(Lcum);
    assert #OrderedGenerators(etaLcum) eq 1;
    modulus:=Eltseq(Z1!(etaLcum.1))[1];
    class:=Valuation(tau,fp)+Eltseq(Z1!(eta(wcum)))[1];
    krange:=[kmin..kmax];
    krange:=[k : k in krange | IsDivisibleBy(k-class,modulus) ];
    if #krange eq 0 then
	return [];
    end if;
    H:=Kernel(eta);
    vecs:=[];
    kmin:=Minimum(krange);

    assert kmin ge 0;
    if kmin eq 0 then
	vp:=(-Valuation(tau,fp))*Z1.1;
	tf,wcumNew,LcumNew:=cosetIntersect(Zr,vp@@eta,H,wcum,Lcum);
	if tf then
	    invs:=Invariants(LcumNew);
	    assert #invs eq rk-1; // Checking that the rank has gone done by 1.
	    //LcumNew:=sub<ZZr | [ZZr!Eltseq(Zr!l) : l in OrderedGenerators(LcumNew)]>;
	    //wcumNew:=ZZr!(Eltseq(Zr!wcumNew));
	    vecs:=vecs cat
		  $$(tau,deltaList,Zr,LcumNew,wcumNew,SLeft,rangeLeft,cB1sq,bigInfs,depth+1);
	end if;
    end if;
    krange:=[k : k in krange | k ge 1];
    krange:=[ k : k in krange | (taunum+fa^k) eq ((theta-theta0)*OK+fa^k)];

    for k in krange do
	fb:=fa^k/(taunum+fa^k);
	tau0:=(theta0-theta)/tau;
	for fact in Factorisation(fb) do
	    assert Valuation(tau0*OK,fact[1]) eq 0; // Sanity check!
	end for;
	if (fb eq ideal<OK|1>) then
	    kprime:= 0;
	else
	    kprime:=Max([ Ceiling(fact[2]/Valuation(p*OK,fact[1])) :
			  fact in Factorisation(fb)]);
	end if;
	pkprime:=p^kprime;
	assert Denominator(pkprime*OK/fb) eq 1;
	if kprime ge 1 then
	    assert Denominator((p^(kprime-1)*OK)/fb) ne 1;
	end if;  // kprime really is the smallest positive
	// integer such that fb divides p^kprime.
	Zmod:=Integers(pkprime);
	U,eps:=UnitGroup(Zmod);
	gens:=[ Integers()!(u@eps) : u in OrderedGenerators(U)];
	if IsOdd(p) and kprime ge 1 then
	    assert #gens eq 1; // Sanity check: there is a primitive root.
	end if;
	alphaList:=[K!tau0] cat [K!g : g in gens] cat [K!delta: delta in deltaList];
	D,alphaList:=multGroup(fb,alphaList);
	// D is (isomorphic to) the group (OK/fb)^* and alphaList
	// is the image in D of the original alphaList defined above,
	// i.e. the images in D of tau0, the generators of (\Z/p^\prime)^*, and the \delta_i.
	tau0im:=alphaList[1];
	alphaList:=alphaList[2..#alphaList];
	gensim:=alphaList[1..#gens];
	alphaList:=alphaList[(#gens+1)..#alphaList];
	assert #alphaList eq #deltaList;
	G,pi:=quo< D | sub<D | gensim> >;
	tau0im:=pi(tau0im);
	alphaList:=[pi(alpha) : alpha in alphaList];
	assert #alphaList eq r;
	phi:=hom<Zr->G | alphaList>;
	// This the map \phi in the paper.
	if tau0im in Image(phi) then
	    w:=tau0im@@phi;
	    L:=Kernel(phi);
	    tf,wcumNew,LcumNew:=cosetIntersect(Zr,w,L,wcum,Lcum);
	    if tf then
		invs:=Invariants(LcumNew);
		assert #invs eq rk; // Checking that the rank has is same.
		vp:=(k-Valuation(tau,fp))*Z1.1;
		//if vp in Image(eta) then
		v:=vp@@eta;
		tf,wcumNew,LcumNew:=cosetIntersect(Zr,v,H,wcumNew,LcumNew);
		if tf then
		    invs:=Invariants(LcumNew);
		    assert #invs eq rk-1; // Checking that the rank has is reduced by 1.
		    //LcumNew:=sub<ZZr | [ZZr!Eltseq(Zr!l) : l in OrderedGenerators(LcumNew)]>;
		    //wcumNew:=ZZr!(Eltseq(Zr!wcumNew));
		    vecs:=vecs cat $$(tau,deltaList,Zr,LcumNew,wcumNew,SLeft,rangeLeft,cB1sq,bigInfs,depth+1);
		end if;
	    end if;
	end if;
    end for;
    return vecs;
end function;

c21Func:=function(theta,tau,deltaList,S,absMinv,vecU,vecB)
    // Evaluate c_21 in the notation of the paper.
    // Here cB1 is an upper bound for the L^2-norm
    // of (b_1,..,b_r).
    K:=NumberField(Universe([theta] cat [tau] cat deltaList));
    d:=Degree(K);
    assert d ge 3;
    assert theta eq K.1;
    OK:=MaximalOrder(K);
    r:= #deltaList;
    s:=#S;
    u,v:= Signature(K);
    assert d eq u+2*v;
    assert s eq (r-(u+v-1));
    assert &and[Abs(Norm(delta)) eq 1 : delta in deltaList[1..u+v-1]];
    assert &and[Abs(Norm(delta)) ne 1 : delta in deltaList[u+v..r]];

    expSbds:=[];
    c21:=0;
    cB2:= Sqrt(&+[i^2 : i in vecB]);

    for i in [1..s] do
	fp:= S[i];
	km1:=valuationBound(theta,tau,deltaList,fp,cB2); // This is k-1
	// in the notation of the paper.
	kfpp:=Valuation(tau*OK,fp);
	kfppp:=km1-kfpp;
	Append(~expSbds,<-kfpp,kfppp>);

	vecU[i,1]:= Abs(Log(Norm(fp)))*Max([Abs(kfpp),Abs(kfppp)]);
	vecBnew:= Eltseq(absMinv*vecU);
	for j in [1..s] do
	    if vecBnew[j] lt vecB[u+v-1+j] then
		vecB[r-s+j]:= Round(vecBnew[j]);
	    end if;
	end for;
	cB2:= Sqrt(&+[i^2 : i in vecB]);
	// <-kfpp,kfppp> are lower and upper bounds
	// for the fp-valuation of epsilon=delta_1^b_1 ... delta_r^b_r.

	c21:=c21+Max(0,kfppp)*Log(Norm(fp));
    end for;

    return c21,expSbds,vecU,vecB;
end function;

constants:=function(K,theta,tau)
    // Returns the constants c22, c23, c27, c28 in the notation of
    // the paper.
    d:=Degree(K);
    assert d ge 3;
    u,v:=Signature(K);
    pls:=InfinitePlaces(K);
    realPls:=[pl : pl in pls | LocalDegree(pl) eq 1];
    cmxPls:=[pl : pl in pls | LocalDegree(pl) eq 2];
    assert #realPls eq u;
    assert #cmxPls eq v;

    if #cmxPls eq 0 then
	c22:=0;
    else
	c22:=2*&+[Log(Max(1,AbsoluteValue(Evaluate(tau,pl)/Imaginary(Evaluate(theta,pl)))))
		  : pl in cmxPls ];
    end if;
    realtheta:=[Evaluate(theta,pl) : pl in realPls];
    realtau:=[Evaluate(tau,pl) : pl in realPls];
    if u le 1 then
	c23:=1; // We in fact do not use c23 when #realPls is 0.
    else
	c23:=Min([(AbsoluteValue(realtheta[i]-realtheta[j]))/
		  (AbsoluteValue(realtau[i])+AbsoluteValue(realtau[j]))
		  : i,j in [1..u] | i lt j]);
    end if;

    return c22, c23;
end function;

constantsDivc25:=function(K,theta,tau,c23,sigma)
    // Returns the constants c27, c28 in the notation of
    // the paper.
    d:=Degree(K);
    assert d ge 3;
    u,v:=Signature(K);
    pls:=InfinitePlaces(K);
    realPls:=[pl : pl in pls | LocalDegree(pl) eq 1];
    cmxPls:=[pl : pl in pls | LocalDegree(pl) eq 2];
    assert #realPls eq u;
    assert #cmxPls eq v;

    otherRealPls:= [pl : pl in realPls | pl ne sigma];
    otherPls:= otherRealPls cat cmxPls;
    assert #otherPls eq (u+v-1);
    sigma2:= otherPls[1];
    tau1:= AbsoluteValue(Evaluate(tau,sigma));
    if sigma2 in realPls then
	otherRealPls:= [pl : pl in otherRealPls | pl ne sigma2];
	assert #otherRealPls eq (u-2);
	tau2:= AbsoluteValue(Evaluate(tau,sigma2));
	tauconjAbs:= [ AbsoluteValue(Evaluate(tau,pl)) : pl in otherRealPls ];
	thetaconjIms:= [Imaginary(Evaluate(theta,pl)) : pl in cmxPls ];
	c27divc25:= tau1/(Min(tauconjAbs cat [tau2])*c23);
	if IsEmpty(thetaconjIms) then
	    c28divc25:= 1;
	else
	    c28divc25:= tau1/(Min(thetaconjIms));
	end if;
	c29divc25:= [0] cat [tau1/(tau2*c23)] cat [tau1/tau*c23 : tau in tauconjAbs]
		    cat [tau1/Imth : Imth in thetaconjIms];
    else
	assert IsEmpty(otherRealPls);
	otherCmxPls:= [pl : pl in cmxPls | pl ne sigma2];
	assert #otherCmxPls eq (v-1);
	theta2:= Imaginary(Evaluate(theta,sigma2));
	thetaconjIms:= [Imaginary(Evaluate(theta,pl)) : pl in otherCmxPls ];
	c27divc25:= 1;
	c28divc25:= tau1/(Min(thetaconjIms cat [theta2]));
	c29divc25:= [0] cat [tau1/theta2] cat [tau1/thetaj : thetaj in thetaconjIms];
    end if;
    assert #c29divc25 eq (u+v);

    return c27divc25, c28divc25, c29divc25, sigma2;
end function;

approxLattice:=function(tau,deltaList,S,sigma,sigma2,C)
    // Given a real embedding sigma that minimises $|\sigma(\epsilon)|$
    // and a positive integer C,
    // this returns the matrix M and vector \mathbf{w}
    // in the notation of the paper.
    K:=Universe([tau] cat deltaList);
    K:=NumberField(K);
    theta:=K.1;
    pls:=InfinitePlaces(K);
    realpls:=[pl : pl in pls | LocalDegree(pl) eq 1];
    assert sigma in realpls;
    cmxpls:=[pl : pl in pls | LocalDegree(pl) eq 2];
    assert LocalDegree(sigma) eq 1;
    s:=#S;
    d:=Degree(K);
    r:=#deltaList;
    u,v:=Signature(K);
    w:=u+v-2;
    n:=d+s-1;
    assert #realpls eq u;
    assert #cmxpls eq v;
    assert d eq u+2*v;
    assert r eq (u+v+s-1);
    assert n eq r+v;
    prec:=2*Ceiling(Log(C)/Log(10))+2000;
    theta1:=Evaluate(theta,sigma : Precision:=prec);
    pi:=Pi(RealField(prec));
    saj:=C*pi;
    _,xp:=MantissaExponent(saj);
    assert xp lt -100; // This a test to
    // make sure that we have enough precision
    // to compute
    // the nearest integer correctly.
    Cpi:=Round(saj);
    matblock1:= ZeroMatrix(Integers(),w,r+v);
    matblock2:= HorizontalJoin(IdentityMatrix(Integers(),s+1),ZeroMatrix(Integers(),s+1,d-2));
    matblock3:= ZeroMatrix(Integers(),v,r+v);
    LatMat:= VerticalJoin(<matblock1,matblock2,matblock3>);
    assert NumberOfColumns(LatMat) eq NumberOfRows(LatMat);
    assert NumberOfColumns(LatMat) eq ((s+1)+(d-2));

    for i in [1..v] do
	LatMat[r+i,s+1+w+i] := Cpi;
    end for;
    ww:=[0 : j in [1..(s+1)]];
    otherRealPls:=[pl : pl in realpls | pl ne sigma];
    otherPls:=otherRealPls cat cmxpls;
    assert #otherPls eq u+v-1;

    otherPls:=[pl : pl in otherPls | pl ne sigma2];
    assert #otherPls eq w;
    theta2:=Evaluate(theta,sigma2 : Precision:=prec);
    tau2:=Evaluate(tau,sigma2 : Precision:=prec);
    for j in [1..w] do
	sigma3:=otherPls[j];
	theta3:=Evaluate(theta,sigma3 : Precision:=prec);
	tau3:=Evaluate(tau,sigma3 : Precision:=prec);
	betaj:=Log(AbsoluteValue((theta2-theta1)*tau3))
	       - Log(AbsoluteValue((theta3-theta1)*tau2));
	saj:=C*betaj;
	_,xp:=MantissaExponent(saj);
	assert xp lt -100;
	saj:=Round(saj);
	ww:=ww cat [saj];
	for i in [1..r] do
	    delta:=deltaList[i];
	    ld2:=Log(AbsoluteValue(Evaluate(delta,sigma2 : Precision:=prec)));
	    ld3:=Log(AbsoluteValue(Evaluate(delta,sigma3 : Precision:=prec)));
	    saj:=C*(ld3-ld2);
	    _,xp:=MantissaExponent(saj);
	    assert xp lt -100;
	    saj:=Round(saj);
	    LatMat[i , s+1+j] := saj;
	end for;
    end for;
    for j in [1..v] do
	CC:=ComplexField(prec);
	sigma2:=cmxpls[j];
	theta2:=CC!Evaluate(theta,sigma2 : Precision:=prec);
	tau2:=CC!Evaluate(tau,sigma2 : Precision:=prec);
	beta:=Imaginary(Log((theta1-theta2)/tau2));
	saj:=C*beta;
	_,xp:=MantissaExponent(saj);
	assert xp lt -100;
	saj:=Round(saj);
	ww:=ww cat [saj];
	for i in [1..r] do
	    delta:=deltaList[i];
	    alphai:=-Imaginary(Log(CC!Evaluate(delta,sigma2 : Precision:=prec)));
	    saj:=C*alphai;
	    _,xp:=MantissaExponent(saj);
	    assert xp lt -100;
	    saj:=Round(saj);
	    LatMat[i,s+1+w+j] := saj;
	end for;
    end for;
    assert #ww eq n;
    return LatMat, ww;
end function;

nonunitExps:=function(K,S,deltaList,vecB)
    // Compute initial matrix and vector u for reducing
    // the exponents of the non-unit delta_i, as well as
    // the initial vector b
    d:=Degree(K);
    OK:=MaximalOrder(K);
    r:=#deltaList;
    u,v:=Signature(K);
    w:=u+v-2;
    s:=#S;
    assert d eq u+2*v;
    assert s eq (r-(u+v-1));
    assert &and[Abs(Norm(delta)) eq 1 : delta in deltaList[1..u+v-1]];
    assert &and[Abs(Norm(delta)) ne 1 : delta in deltaList[u+v..r]];

    if (s eq 0) then
	return [],[],vecB;
    else
	M:= Matrix([ [Log(Norm(P)^(-Valuation(deltaList[i]*OK,P))) : i in [u+v..r]]
		     : P in S]);
	assert NumberOfRows(M) eq s;
	assert NumberOfColumns(M) eq s;
	// using in place of M^(-1) to avoid precision errors
	Minv:= 1/Determinant(M)*Adjoint(M);
	absM:= Matrix([ [Abs(M[i,j]) : j in [1..s]] : i in [1..s]]);
	absMinv:= Matrix([ [Abs(Minv[i,j]) : j in [1..s]] : i in [1..s]]);
	vecU:= absM*Matrix(RealField(),s,1,vecB[u+v..r]);
    end if;

    return absMinv,vecU;
end function;

reducedBoundFixedEmbedding2:=function(K,theta,tau,deltaList,S,consts,sigma : verb:=false)
    // sigma is a fixed REAL embedding of K.
    // Compute a reduced bound for B under the assumption
    // that \eta makes |sigma(epsilon)| minimal.
    // Here consts is the list [c20,c17,c22,c23,c26,c27,c28].
    c20,c17,c22,c23,c26:=Explode(consts);
    c27divc25, c28divc25, c29divc25, sigma2:= constantsDivc25(K,theta,tau,c23,sigma);
    cB0:=c20;
    if verb then
	printf "The initial bound is %o.\n", c20;
    end if;
    d:=Degree(K);
    OK:=MaximalOrder(K);
    r:=#deltaList;
    u,v:=Signature(K);
    w:=u+v-2;
    s:=#S;
    n:=r+v;
    assert d eq u+2*v;
    assert s eq (r-(u+v-1));
    assert &and[Abs(Norm(delta)) eq 1 : delta in deltaList[1..u+v-1]];
    assert &and[Abs(Norm(delta)) ne 1 : delta in deltaList[u+v..r]];
    vecB:= [cB0 : i in [1..#deltaList]]; // Converting from a bound on the infinity norm
    absMinv,vecU:= nonunitExps(K,S,deltaList,vecB);

    finished:=false;

    repeat
	if (s gt 0) then
	    c21,expSbds,vecU,vecB:=c21Func(theta,tau,deltaList,S,absMinv,vecU,vecB);
	    if verb then
		printf "The exponent bounds are %o.\n", expSbds;
	    end if;
	else
	    c21:= 0;
	    expSbds:= [];
	end if;
	c24:=c21+c22+(u-1)*Log(Max(1,1/c23));
	c25:=Exp(c24);
	c27:= c27divc25*c25;
	c28:= c28divc25*c25;
	c29:= [c29divc25[j]*c25 : j in [1..(u+v)]];
	if u eq 1 then
	    c30:=Max([2*c17*c24, Log(2*c28)/c26]);
	elif v eq 0 then
	    c30:=Max([2*c17*c24, Log(2*c27)/c26]);
	else
	    c30:=Max([2*c17*c24, Log(2*c27)/c26, Log(2*c28)/c26]);
	end if;

	cB0:= Max(vecB);
	cB1:= &+[Abs(i) : i in vecB];
	cB2:= Sqrt(&+[i^2 : i in vecB]);
	cA1:= (1 + cB1)/2;
	cA2:= (1 + cB1) + 1/(2*Pi(RealField()));
	cB3:= 0;
	cB4:= 0;
	for j in [1..w] do
	    cB3:= cB3 + (c29[2] + c29[j+2])^2;
	    cB4:= cB4 + cA1*(c29[2] + c29[j+2]);
	end for;
	for j in [1..v] do
	    cB3:= cB3 + (c29[u+j])^2;
	    cB4:= cB4 + cA2*(c29[u+j]);
	end for;
	cB5:= (cB2^2 - w*cB0^2 + w*cA1^2 + v*cA2^2)^(1/2);
	C:=Ceiling(cB5^(n/(d-2)));
	// We follow the procedure in the section "Reduction of Bounds"
	// to repeatedly reduce the initial bound.
	repeat
	    ZZn:=StandardLattice(n);
	    M,ww:=approxLattice(tau,deltaList,S,sigma,sigma2,C);
	    ww:=ZZn!ww;
	    LL:=Lattice(M);
	    DLwsq:=distanceLBsq(LL,ww);
	    // This D(L,w)^2 in the notation of paper.
	    tf1:=DLwsq gt cB5^2;
	    if tf1 eq false then
		if verb then
		    printf "Increasing C.\n";
		end if;
		C:=10*C;
	    end if;
	    //	until tf1 and tf2;
	until tf1;
	denom:= (cB3*(DLwsq^2-cB5^2) + cB4^2)^(1/2) - cB4;
	cB0New:=(1/c26)*Log((2*C*cB3)/denom);

	cB0New:=Max(c30,cB0New);
	if cB0New lt 10^10 then
	    cB0New:=Floor(cB0New);
	end if;
	if cB0New lt cB0 then
	    if verb then
		printf "The new bound is %o.\n", cB0New;
	    end if;
	    cB0:=cB0New;
	    for i in [1..r] do
		if cB0 lt vecB[i] then
		    vecB[i]:= cB0;
		end if;
	    end for;
	else
	    finished:=true;
	end if;
    until finished;
    return vecB, expSbds;
end function;

reducedBound:=function(tau,deltaList : verb:=false)
    // This gives the final bound for B:=max(|b_1|,..,|b_r|)
    // where the b_i are as in (*).
    K:=Universe([tau] cat deltaList);
    K:=NumberField(K);
    theta:=K.1;
    OK:=MaximalOrder(K);
    S:=&join[Support(delta*OK) : delta in deltaList];
    S:=SetToSequence(S);
    fn:=func<P1,P2 | Norm(P2)-Norm(P1) >;
    Sort(~S,fn); // Sorting S so that the prime ideals with largest norm come first.
    s:= #S;
    assert &and[ fact[1] in S : fact in Factorisation(tau*OK) | fact[2] lt 0 ];
    // This is a sanity check. According to the paper
    // the denominator ideal of tau is supported
    // on S.
    c20,c17:=initialBound(K,theta,tau,deltaList,S);
    c22, c23:=constants(K,theta,tau);
    c26:=1/(2*c17);
    consts:=[c20,c17,c22,c23,c26];
    r:=#deltaList;
    d:=Degree(K);
    assert d ge 3;
    pls:=InfinitePlaces(K);
    realPls:=[pl : pl in pls | LocalDegree(pl) eq 1];
    cmxPls:=[pl : pl in pls | LocalDegree(pl) eq 2];
    t:=#realPls;
    assert d eq t+2*#cmxPls;

    if t eq 0 then
	// The totally complex case.
	if verb then
	    printf "We're in the totally complex case.\n";
	    printf "The initial bound is %o.\n", c20;
	end if;
	cB0:= c20;
	vecB:= [cB0 : i in [1..#deltaList]]; // Converting from a bound on the infinity norm
	absMinv,vecU:= nonunitExps(K,S,deltaList,vecB);

	finished:=false;
	repeat
	    if (s gt 0) then
		c21,expSbds,vecU,vecB:=c21Func(theta,tau,deltaList,S,absMinv,vecU,vecB);
		if verb then
		    printf "The exponent bounds are %o.\n", expSbds;
		end if;
	    else
		c21:= 0;
		expSbds:= [];
	    end if;
	    cB0New:=2*c17*(c21+c22);
	    if cB0New lt cB0 then
		if verb then
		    printf "The reduction process gives a new bound of %o.\n", Floor(cB0New);
		end if;
		cB0:=Floor(cB0New);
		for i in [1..r] do
		    if cB0 lt vecB[i] then
			vecB[i]:= cB0;
		    end if;
		end for;
	    else
		if verb then
		    printf "The reduction process gives a worse bound of %o.\n",
			   Floor(cB0New);
		end if;
		finished:=true;
	    end if;
	until finished;
	for i in [1..#S] do
	    expSbds[i,1]:=expSbds[i,1]+Valuation(tau,S[i]);
	    expSbds[i,2]:=expSbds[i,2]+Valuation(tau,S[i]);
	end for;
	return [Integers()!b : b in vecB], S, expSbds;
    end if;
    assert t ge 1; // We've now finished with the totally complex case.
    if verb then
	printf "The initial bound is %o.\n", c20;
	printf
	    "We're carrying out the reduction process for each real embedding separately.\n";
    end if;
    vecBList:=[];
    expSbdsList:=[];
    for i in [1..t] do
	if verb then
	    print "++++++++++++++++++++++++++";
	    if (i mod 10) eq 1 then
		printf "Dealing with the %o-st real embedding.\n", i;
	    elif (i mod 10) eq 2 then
		printf "Dealing with the %o-nd real embedding.\n", i;
	    elif (i mod 10) eq 3 then
		printf "Dealing with the %o-rd real embedding.\n", i;
	    else
		printf "Dealing with the %o-th real embedding.\n", i;
	    end if;
	end if;
	eta:=realPls[i];
	vecBeta, expSbds:= reducedBoundFixedEmbedding2(K,theta,tau,deltaList,S,consts,eta
						       : verb:=verb);
	Append(~vecBList,vecBeta);
	Append(~expSbdsList,expSbds);
    end for;
    expSbds:=expSbdsList[1];
    for expSbds2 in expSbdsList[2..#expSbdsList] do
	assert #expSbds2 eq #S;
	for i in [1..#S] do
	    expSbds[i,1]:=Min(expSbds[i,1], expSbds2[i,1]);
	    expSbds[i,2]:=Max(expSbds[i,2], expSbds2[i,2]);
	end for;
    end for;
    for i in [1..#S] do
	expSbds[i,1]:=expSbds[i,1]+Valuation(tau,S[i]);
	expSbds[i,2]:=expSbds[i,2]+Valuation(tau,S[i]);
    end for;
    vecB:= vecBList[1];
    for vecB2 in vecBList[2..#vecBList] do
	assert #vecB eq r;
	for i in [1..r] do
	    vecB[i]:= Max(vecB[i],vecB2[i]);
	end for;
    end for;

    return [Integers()!b : b in vecB], S, expSbds;
end function;

principalize:=function(fa,S)
    // fa is an ideal of \OO_K
    // and S:=[fp_1,..,fp_s] is a list of prime ideals.
    // We consider the equation
    // (c_0 X - Y \theta)*\OO_K = fa * fp_1^{n_1} * ... * fp_s^{n_s}.
    // If the class [fa] is not contained in the subgroup of the
    // class group generated by [fp_i] then then is is impossible.
    // In this case the function returns
    // false, [], [].
    // Otherwise
    // (c_0 X- Y \theta) = tau  \delta_1^{b_1} \cdots \delta_r^{b_r}
    // and \delta_1,..,\delta_r are a basis for the S-unit group
    // \OO_S^* modulo the roots of unity.
    // The function returns
    // true, tauList, deltaList.
    // tauList is the set of possibilities for tau. This is equal
    // to 1/2 of the number of roots of unity in K (since
    // we can absorb \pm 1 in (X,Y)).
    K:=NumberField(Parent(Basis(fa)[1]));
    OK:=MaximalOrder(K);
    ClK,eta:=ClassGroup(K); // Given an ideal fa, we obtain
    // the class in ClK by fa@@eta.
    s:=#S;
    Zs:=FreeAbelianGroup(s);
    phi := hom< Zs -> ClK | [ClK | fp@@eta : fp in S ]>;
    img:=Image(phi);
    if -fa@@eta in img eq false then
	return false, [K | ], [K | ];
    end if;
    if s eq 0 then
	fa2:=fa;
    else
	rr:=(-fa@@eta)@@phi;
	rr:=Eltseq(Zs!rr);
	fa2:=fa*&*[S[i]^rr[i] : i in [1..s]];
    end if;
    tf,alpha:=IsPrincipal(fa2);
    assert tf; // The ideal really is principal, and alpha
    if #S eq 0 then
	U,mu:=UnitGroup(K);
    else
	U,mu:=SUnitGroup(S);
    end if;
    deltaList:=[ K!(mu(u)) : u in OrderedGenerators(U)  ];
    rtun:=deltaList[1];
    assert IsRootOfUnity(rtun);
    deltaList:=deltaList[2..#deltaList];

    // Reorder deltaList so that the fundamental units apear first
    deltaList:= [delta : delta in deltaList | Abs(Norm(delta)) eq 1] cat
		[delta : delta in deltaList | Abs(Norm(delta)) ne 1];
    r:=Order(U.1) div 2;
    assert rtun^r eq OK!(-1);
    tauList:=[alpha*rtun^i : i in [0..(r-1)]];
    return true, tauList, deltaList;
end function;

alg1:=function(alpha,beta,p)
    // This Algorithm 1 as in the paper.
    // Outputs L, M adequate for (\alpha,\beta).
    OK:=MaximalOrder(Universe([alpha,beta]));
    fprs:=Factorisation(p*OK);
    fprs:=[fact[1] : fact in fprs]; // the prime ideals above p.
    cB:=[];
    uset:={};
    bb:=1*OK;
    for P in fprs do
        vbeta:=Valuation(beta*OK,P);
        valpha:=Valuation(alpha*OK,P);
        bb:=bb*P^(vbeta+Min(valpha,0));
        if valpha ge 0 then
            FP,piP:=ResidueClassField(P);
            Fp:=PrimeField(FP);
            u:=reduce(-alpha,piP,P);
            if u in Fp then
                Append(~cB,P);
                u:=Integers()!(Fp!u);
                assert u ge 0 and u le p-1;
                Include(~uset,u);
            end if;
        end if;
    end for;
    if #cB eq 0 then
        return {bb}, {};
    end if;
    if #cB eq 1 then
        P:=cB[1];
        if InertiaDegree(P) eq 1 and RamificationDegree(P) eq 1 then
            return {},{<bb,P>};
        end if;
    end if;
    M:={};
    if #uset eq p then
        L:={};
    else
        L:={bb};
    end if;
    for u in uset do
        add1,add2:=$$((u+alpha)/p,p*beta,p);
        L:=L join add1;
        M:=M join add2;
    end for;
    return L join {1*OK},M;
end function;

alg2:=function(c0,th,p)
    // This is an implementation of Algorithm
    // 2 in the paper, plus the refinements explained
    // in the remarks.
    // Input: c0, th (=\theta), p.
    // Returns Lp, Mp.
    OK:=MaximalOrder(Parent(th));
    Lp,Mp:=alg1( -th/c0 , c0, p);

    // Now for the refinements.
    Mp:={ <pr[1]/pr[2]^Valuation(pr[1],pr[2]) , pr[2]> : pr in Mp  };
    for pr in Mp do
	fbd:=pr[1];
	fp:=pr[2];
	Lp:={fb : fb in Lp | IsIntegral(fb/fbd) eq false or
			     fb/fbd ne fp^Valuation(fb/fbd,fp)};
    end for;
    if IsDivisibleBy(c0,p) then
	d:=Degree(NumberField(OK));
	Mp1:= {};
	Lp:={fb : fb in Lp | Valuation(Norm(fb),p) ge (d-1)*Valuation(c0,p)};
	for pr in Mp do
	    fbd:=pr[1];
	    fp:=pr[2];
	    while Valuation(Norm(fbd),p) le (d-1)*Valuation(c0,p) do
		if Valuation(Norm(fbd),p) eq (d-1)*Valuation(c0,p) then
		    Mp1:= Mp1 join {<fbd,fp>};
		    break;
		else
		    fbd:= fbd*fp;
		end if;
	    end while;
	end for;
	Mp:= Mp1;
    end if;
    return Lp,Mp;
end function;

normInv:=function(c0,th,R)
    // R a positive integer.
    // Returns all ideals of OK with norm equal to R.
    OK:=MaximalOrder(Parent(th));
    assert R in Integers();
    R:=Integers()!R;
    assert R ge 1;
    if R eq 1 then
	return { 1*OK };
    end if;
    p:=Max(PrimeDivisors(R));
    ideals:= [];

    Lp,Mp:=alg1( -th/c0, c0, p);
    for fb in Lp do
	if Valuation(Norm(fb),p) eq Valuation(R,p) then
	    Append(~ideals,fb);
	end if;
    end for;
    for pr in Mp do
	fb:=pr[1];
	fp:=pr[2];
	while Valuation(Norm(fb),p) le Valuation(R,p) do
	    if Valuation(Norm(fb),p) eq Valuation(R,p) then
		Append(~ideals,fb);
		break;
	    else
		fb:= fb*fp;
	    end if;
	end while;
    end for;

    if IsEmpty(ideals) then
	return {};
    else
	return &join{{fp*fa : fa in $$(c0,th, R div Norm(fp))} : fp in ideals };
    end if;
end function;

prep1:=function(clist,a,primelist)
    // clist is a list of coefficients c_0,c_1,..,c_n.
    // a is an integer.
    // primelist is a list of the primes p_1,p_2,..,p_v.
    // This returns a list of pairs [* fa, fplist *]
    // where fa is an ideal and fplist is a list of prime ideals fp_1,..,fp_v
    // so that (c_0 X - th Y)O_K =fa*fp_1^{n_1}*..*fp_u^{n_u} (as in equation (3)).
    assert &and[IsPrime(p) : p in primelist];
    assert &and[Valuation(a,p) eq 0 : p in primelist];
    assert &and[c in Integers() : c in clist];
    c0:=Integers()!clist[1];
    assert c0 ne 0;
    n:=#clist-1;
    assert n ge 3;
    QUV<U,V>:=PolynomialRing(Rationals(),2);
    F:=&+[clist[i+1]*U^(n-i)*V^i : i in [0..n]];
    assert IsHomogeneous(F);
    Qx<x>:=PolynomialRing(Rationals());
    f:=c0^(n-1)*Evaluate(F,[x/c0,1]);
    assert IsMonic(f);
    assert Degree(f) eq n;
    assert IsIrreducible(f);
    assert &and[c in Integers() : c in Coefficients(f)];
    K<theta>:=NumberField(f);
    OK:=MaximalOrder(K);
    theta:=OK!theta;
    afplist:=[* [* 1*OK, [] *] *];
    for p in primelist do
	afplistNew:=[* *];
	Lp,Mp:=alg2(c0,theta,p);
	afplistNew1:=[* [* pr[1]*fb, pr[2] *] : fb in Lp, pr in afplist  *];
	afplistNew2:=[* [* pr[1]*qr[1], pr[2] cat [qr[2]] *] : qr in Mp, pr in afplist  *];
	afplist:=afplistNew1 cat afplistNew2;
    end for;

    R:=Integers()!(a*c0^(n-1));
    afplistNew:=[* *];
    for pr in afplist do
	af:=pr[1];
	R0:=AbsoluteValue(R div GCD(Norm(af),R));
	//assert &and[Valuation(R0,p) eq 0 : p in primelist];
	invs:=normInv(c0,theta,R0);
	afplistNew:=afplistNew cat [* [* af*I, pr[2] *] : I in invs  *];
    end for;
    afplist:=afplistNew;
    for pr in afplist do // running sanity checks!
	af:=pr[1];
	fplist:=pr[2];
	assert &and[InertiaDegree(fq)*RamificationDegree(fq) eq 1: fq in fplist];
	normlist:=[Norm(fq) : fq in fplist];
	assert #Set(normlist) eq #normlist;
	assert Set(normlist) subset Set(primelist);
	Naf:=Norm(af);
	assert IsDivisibleBy(Naf,a*c0^(n-1));
	assert Set(PrimeDivisors(Naf div (a*c0^(n-1)))) subset Set(primelist);
    end for;
    return afplist;
end function;

prep2:=function(clist,a,primelist)
    // clist is a list of coefficients c_0,c_1,..,c_n.
    // a is an integer.
    // primelist is a list of the primes p_1,p_2,..,p_v.
    // This returns a list of the possible pairs [* tau, deltaList *]
    // so that c_0 X - th Y =tau*delta_1^{b_1}*..*delta_r^{b_r}.
    afplist:=prep1(clist,a,primelist);
    if (#afplist eq 1) then
	printf "There is %o ideal equations to solve.\n", #afplist;
    else
	printf "There are %o ideal equations to solve.\n", #afplist;
    end if;
    tauDeltaList:=[* *];
    for pr in afplist do
	af:=pr[1];
	fplist:=pr[2];
	tf,tauList,deltaList:=principalize(af,fplist);
	if tf then
	    for tau in tauList do
		tauDeltaList:=tauDeltaList cat [* [* tau, deltaList *] *];
	    end for;
	end if;
    end for;
    ranks:= [#pr[2] : pr in tauDeltaList];
    Sort(~ranks,~permut); // sort the elements in order of rank for smallSieveInfo
    return [*tauDeltaList[i^permut] : i in [1..#tauDeltaList]*];

end function;

smallSieveInfo:=function(smallInf,c0,theta,qBound)
    if IsEmpty(smallInf) then
	qMax:= 0;
    else
	qMax:= smallInf[#smallInf][1]; //primes already computed
    end if;
    if (qBound lt qMax+1) then
	return smallInf;
    end if;
    if IsEmpty(PrimesInInterval(qMax+1,qBound)) then
	return smallInf;
    end if;

    printf "Getting the small sieve information";
    K:=NumberField(Parent(theta));
    assert K.1 eq theta;
    OK:=MaximalOrder(K);
    qlist:=[q : q in PrimesInInterval(qMax+1,qBound) | Valuation(c0,q) eq 0];

    for q in qlist do
	qfacts:=[fq[1] : fq in Factorisation(q*OK)];
	if &and[Norm(fq) lt 10^10 : fq in qfacts] then
	    AqOrd:=&*[Norm(fq)-1 : fq in qfacts];
	    assert IsDivisibleBy(AqOrd,q-1);
	    BqOrd:=AqOrd div (q-1);
	    OModq,modq:=quo<OK | q*OK>;
	    Aq,eta:=UnitGroup(OModq);
	    Zqs,fromZqs:=UnitGroup(Integers(q));
	    ZqsGens:=[Integers()!(z@fromZqs) : z in Generators(Zqs)];
	    Bq,toBq:=quo<Aq | sub<Aq | [(modq(OK!z))@@eta : z in ZqsGens]> >;
	    // This is \mathfrak{B}_q.
	    if IsPrime(q) and (IsDivisibleBy(Discriminant(OK),q) eq false) then
		assert #Bq eq ((&*[Norm(fq)-1 : fq in qfacts]) div (q-1));
	    end if;
	    factq:=Factorisation(q);
	    assert #factq eq 1;
	    p:=factq[1,1]; t:=factq[1,2];
	    Rq:=[(c0*u-theta) : u in [0..(q-1)]] cat [c0-theta*p*u : u in [0..(p^(t-1)-1)]];
	    Rqstar:=[ rho : rho in Rq | &and [Valuation(rho*OK,fq) eq 0 :
					      fq in qfacts ]];	// R_q \cap \OO_q^\times.
	    imdelFunc:=func<del | toBq((reduce(del,modq,q*OK))@@eta)>;
	    // Function to compute the image of del in Bq. Here del
	    // must be an element of O_q.
	    SqShifted:=[toBq((modq(rho))@@eta) : rho in Rqstar];
	    // Subtract the image of tau from SqShifted to get Sq.
	    Append(~smallInf, [* q, Bq, imdelFunc, SqShifted, Rqstar, eta, modq, fromZqs *]);
	end if;
    end for;
    printf "...Done.\n";
    return smallInf;
end function;

bigSieveInfo:=function(tau,deltaList,smallInf)
    K:=NumberField(Universe([tau] cat deltaList));
    OK:=MaximalOrder(K);
    supp:=&join[Support(delta*OK) : delta in deltaList];
    supp:=supp join Support(tau*OK);
    r:=#deltaList;
    Zr:=FreeAbelianGroup(r);
    bigInf:=[* *];
    for I in smallInf do
	q:=I[1];
	Bq:=I[2];
	imdelFunc:=I[3];
	SqShifted:=I[4];
	Rqstar:=I[5];
	eta:=I[6];
	modq:=I[7];
	fromZqs:=I[8];
	qfacts:=[fq[1] : fq in Factorisation(q*OK)];
	if #(Set(qfacts) meet supp) eq 0 then
	    imsDelta:=[ imdelFunc(delta) : delta in deltaList];
	    Cq:=sub< Bq | imsDelta>;
	    phiq:=hom<Zr->Cq | [Cq!delta : delta in imsDelta]>;
	    imtau:=imdelFunc(tau);
	    Sq:=[rho-imtau : rho in SqShifted];
	    RqstarNew:=[];
            Tq:=[];
            for j in [1..#Sq] do
                rho:=Sq[j];
                if rho in Cq then
                    Append(~Tq,Cq!rho);
                    Append(~RqstarNew, Rqstar[j]);
                end if;
            end for;
	    Append(~bigInf, [* q, Cq, phiq, Tq, RqstarNew, imdelFunc, eta, modq, fromZqs *]);
	end if;
    end for;
    return Zr, bigInf;
end function;

function furtherreduced(tau, deltaList, c21, vecB)
    K:=Universe([tau] cat deltaList);
    K:=NumberField(K);
    theta:=K.1;
    OK:=MaximalOrder(K);
    S:=&join[Support(delta*OK) : delta in deltaList];
    S:=SetToSequence(S);
    fn:=func<P1,P2 | Norm(P2)-Norm(P1) >;
    Sort(~S,fn); // Sorting S so that the prime ideals with largest norm come first.
    s:= #S;
    assert &and[ fact[1] in S : fact in Factorisation(tau*OK) | fact[2] lt 0 ];
    // This is a sanity check. According to the paper
    // the denominator ideal of tau is supported
    // on S.
    c20,c17:=initialBound(K,theta,tau,deltaList,S);
    c22, c23:=constants(K,theta,tau);
    c26:=1/(2*c17);
    r:=#deltaList;
    d:=Degree(K);
    assert d ge 3;
    pls:=InfinitePlaces(K);
    realPls:=[pl : pl in pls | LocalDegree(pl) eq 1];
    cmxPls:=[pl : pl in pls | LocalDegree(pl) eq 2];
    sigma:= realPls[1];

    u,v:= Signature(K);
    assert d eq u+2*v;
    assert s eq (r-(u+v-1));
    assert &and[Abs(Norm(delta)) eq 1 : delta in deltaList[1..u+v-1]];
    assert &and[Abs(Norm(delta)) ne 1 : delta in deltaList[u+v..r]];

     c27divc25, c28divc25, c29divc25, sigma2:= constantsDivc25(K,theta,tau,c23,sigma);
     w:=u+v-2;
     n:=r+v;

     c24:=c21+c22+(u-1)*Log(Max(1,1/c23));
     c25:=Exp(c24);
     c27:= c27divc25*c25;
     c28:= c28divc25*c25;
     c29:= [c29divc25[j]*c25 : j in [1..(u+v)]];
     if u eq 1 then
	 c30:=Max([2*c17*c24, Log(2*c28)/c26]);
     elif v eq 0 then
	 c30:=Max([2*c17*c24, Log(2*c27)/c26]);
     else
	 c30:=Max([2*c17*c24, Log(2*c27)/c26, Log(2*c28)/c26]);
     end if;

     cB0:= Max(vecB);
     cB1:= &+[Abs(i) : i in vecB];
     cB2:= Sqrt(&+[i^2 : i in vecB]);
     cA1:= (1 + cB1)/2;
     cA2:= (1 + cB1) + 1/(2*Pi(RealField()));
     cB3:= 0;
     cB4:= 0;
     for j in [1..w] do
	 cB3:= cB3 + (c29[2] + c29[j+2])^2;
	 cB4:= cB4 + cA1*(c29[2] + c29[j+2]);
     end for;
     for j in [1..v] do
	 cB3:= cB3 + (c29[u+j])^2;
	 cB4:= cB4 + cA2*(c29[u+j]);
     end for;
     cB5:= (cB2^2 - w*cB0^2 + w*cA1^2 + v*cA2^2)^(1/2);
     C:=Ceiling(cB5^(n/(d-2)));

     repeat
	 ZZn:=StandardLattice(n);
	 M,ww:=approxLattice(tau,deltaList,S,sigma,sigma2,C);
	 ww:=ZZn!ww;
	 LL:=Lattice(M);
	 DLwsq:=distanceLBsq(LL,ww);
	 //print C,DLwsq+0.0;
	 // This D(L,w)^2 in the notation of paper.
	 tf1:=DLwsq gt cB5^2;
	 tf2:=(ww in LL) eq false;
	 if (tf1 and tf2) eq false then
	     C:=10*C;
	 end if;
     until tf1 and tf2;
     denom:= (cB3*(DLwsq^2-cB5^2) + cB4^2)^(1/2) - cB4;
     cB0New:=(1/c26)*Log((2*C*cB3)/denom);

     cB0New:=Max(c30,cB0New);
     if cB0New lt 10^10 then
	 cB0New:=Floor(cB0New);
     end if;
     if cB0New lt cB0 then
	 cB0:=cB0New;
	 for i in [1..r] do
	     if cB0 lt vecB[i] then
		 vecB[i]:= cB0;
	     end if;
	 end for;
     end if;
     return vecB;
end function;

SetAutoColumns(false);
SetColumns(235);

solveThueMahler:=function(clist,primelist,a : verb:=false)
    // Input: clist, a, primelist
    // clist is a list of coefficients c_0,c_1,..,c_n.
    // a is an integer.
    // primelist is a list of the primes p_1,p_2,..,p_v.
    // This solves c_0 X^n+...+c_n Y^n= a \times p_1^{z_1} ... p_t^{z_t}
    // subject to the assumptions that X, Y are coprime integers
    // and gcd(Y,c_0)=1.
    // Output: sols.
    // sols is a list of solutions to the Thue--Mahler equation.
    printf
"++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
    printf "clist:=%o; primelist:=%o; a:=%o; \n", clist,primelist,a;
    printf
"++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";

    d:=#clist-1;
    ZUV<U,V>:=PolynomialRing(Integers(),2);
    F:=&+[clist[i+1]*U^(d-i)*V^i : i in [0..d]];
    c0:=clist[1];
    tauDeltaList:=prep2(clist,a,primelist);
    if #tauDeltaList eq 0 then
	printf "No S-unit equations to solve!\n";
	printf "Done solving the Thue-Mahler equation.\n";
	printf
"++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
    	return {};
    end if;
    K:=Universe([pr[1] : pr in tauDeltaList] cat &cat[pr[2] : pr in tauDeltaList]);
    K:=NumberField(K);
    theta:=K.1;
    OK:=MaximalOrder(K);
    assert Degree(K) eq (#clist-1);
    sols:={};
    eqncount:=0;

    smallInf:=smallSieveInfo([* *],c0, theta, 200);
    if (#tauDeltaList eq 1) then
	printf "We have %o S-unit equation to solve.\n", #tauDeltaList;
	printf "The rank is %o.\n", Sort([#pr[2] : pr in tauDeltaList]);
    else
	printf "We have %o S-unit equations to solve.\n", #tauDeltaList;
	printf "The ranks are %o.\n", Sort([#pr[2] : pr in tauDeltaList]);
    end if;
    print "+++++++++++++++++++++++++++++++++++++";
    for pr in tauDeltaList do
	eqncount:=eqncount+1;
	printf "Working on equation number %o...\n", eqncount;
	tau:=pr[1];
	deltaList:=pr[2];
	vecB,S,range:=reducedBound(tau,deltaList : verb:=verb);
	print "S is ", S;
	printf "The range is %o.\n", range;
	cB2sq:= &+[i^2 : i in vecB];
	printf "The bound on the norm squared of (b1,..,br) is %o.\n", cB2sq;
	printf "Applying the Dirichlet sieve to equation number %o out of %o.\n",
	      eqncount, #tauDeltaList;

	if cB2sq gt 500000 then
	    qBound:= 500;
	else
	    qBound:=200;
	end if;
	smallInf:=smallSieveInfo(smallInf,c0,theta,qBound);
	Zr, bigInfs:=bigSieveInfo(tau,deltaList,smallInf);
	vecs:=sift(tau,deltaList,Zr,Zr,Zr!0,S,range,cB2sq,bigInfs,1);
	printf "Finished applying the Dirichlet sieve to equation number %o.\n", eqncount;
	print "+++++++++++++++++++++++++++++++++++++";
	if #vecs ne 0 then
	    for ww in vecs do
		lincom:=tau*&*[deltaList[i]^ww[i] : i in [1..#deltaList]];
		lincom:=Eltseq(K!lincom);
		if &and[ lincom[i] eq 0 : i in [3..Degree(K)]] and lincom[1] in Integers()
		   and lincom[2] in Integers() then
		    lincom:=[Integers()!lincom[1],Integers()!lincom[2]];
		    if IsDivisibleBy(lincom[1],c0) then
			sol:=[lincom[1] div c0, -lincom[2]];
			Fsol:=Evaluate(F,sol);
			if GCD(sol[1],sol[2]) eq 1 and GCD(c0,sol[2]) eq 1 and
			   IsDivisibleBy(Fsol,a) then
			    Fsol:=Fsol div a;
			    mlist:=[];
			    for p in primelist do
				m:=Valuation(Fsol,p);
				Append(~mlist,m);
				Fsol:=Fsol div p^m;
			    end for;
			    if Fsol eq 1 then
				if IsEven(d) then
				    sols:=sols join { sol cat mlist,[-sol[1],-sol[2]]
								    cat mlist };
				else
				    sols:=sols join {  sol cat mlist };
				end if;
			    elif Fsol eq -1 then
				if IsOdd(d) then
				    sols:=sols join { [-sol[1],-sol[2]] cat  mlist };
				end if;
			    end if;
			end if;
		    end if;
		end if;
	    end for;
	end if;
    end for;

    if (Abs(c0) eq 1) and (Abs(a) eq 1) then
	if (c0 eq a) then
	    assert (Evaluate(F,[1,0]) eq c0);
	    sols:= sols join { [1,0] cat [0 : i in [1..#primelist]] };
	elif (c0*(-1)^d eq a) then
	    assert (Evaluate(F,[-1,0]) eq a);
	    sols:= sols join { [-1,0] cat [0 : i in [1..#primelist]] };
	end if;
    end if;

    printf "Done solving the Thue-Mahler equation.\n";
    printf
"++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
    return sols;
end function;


//----------------------------------------------//

// Example 1
//clist:=[3,2,7,2];
//a:=1;
//primelist:=[2,3,7,41];
//time sols:=solveThueMahler(clist,primelist,a : verb:=true);
//sols;

//clist:=[1,2,4,6];
//a:=1;
//primelist:=[2,3,7,41,1109];
//time sols:=solveThueMahler(clist,primelist,a : verb:=true);
//sols;


// Example 2
//clist:=[7,1,29,-25];
//a:=1;
//primelist:=[2,3,7,37,53];
//time sols:=solveThueMahler(clist,primelist,a);
//sols;

// Example 3a (improvement on Soydan and Tzanakis)
//clist:=[3,65,-290,-2110,975,3149];
//a:= -(2^5)*(3^4);
//primelist:=[5,11];
//time sols:=solveThueMahler(clist,primelist,a);
//sols;

// Example 3b (improvement on Soydan and Tzanakis)
//clist:=[3,65,-290,-2110,975,3149];
//a:= -1;
//primelist:=[2,3,5,7,11,13,17];
//time sols:=solveThueMahler(clist,primelist,a);
//sols;

// Example 4
//clist:=[1,0,0,0,-2];
//primelist:=[2, 7, 23, 31, 47, 71, 73, 79, 89];
//time sols1:=solveThueMahler(clist,primelist,1);
//time sols2:=solveThueMahler(clist,primelist,-1);
//sols1;
//sols2;

// Example 5
//SetClassGroupBounds("GRH");
//clist:=[ 5,  1,  4,  1,  6,  1,  6,  0,  6,  0,  4, -2];
//a:=1;
//primelist:=[2,3,5,7,11];
//time sols:=solveThueMahler(clist,primelist,a : verb:=true);
//sols;

// Example 6 (de Weger--Tzanakis)
//clist:=[1,-23,5,24];
//primelist:=[2,3,5,7];
//time sols:=solveThueMahler(clist,primelist,1) join solveThueMahler(clist,primelist,-1);
//sols;

// Example 7 (no real places)
//clist:=[ 1, 0, 0, 0, 3 ];
//a:= 1;
//primelist:= [ 2, 7, 23, 31 ];
//time sols:=solveThueMahler(clist,primelist,1) join solveThueMahler(clist,primelist,-1);

// Mike's Example
//SetClassGroupBounds("GRH");
//clist:= [ 486, 2673, 8910, 13365, 17820, 12474, 8316, 2970, 990, 165, 22, 1 ];
//a:= 1;
//primelist:= [3];
//time sols:=solveThueMahler(clist,primelist,a : verb:=false); sols;

// Goormaghtigh's Example
// 2 hours... any way to speed this up? Why is it so slow? Fund. unit is huge
//clist:= [718,718,718,718,719];
//a:=1;
//primelist:= [719];
//SetClassGroupBounds("GRH");
//time solveThueMahler(clist,primelist,a : verb:=true);

// Goormaghtigh's Example
//clist:= [189,189,189,189,190];
//a:=1;
//primelist:= [2,5,19]; //[190];
//SetClassGroupBounds("GRH");
//time solveThueMahler(clist,primelist,a : verb:=true);

//clist:=[14,20,24,15];
//a:=1;
//primelist:= [2,3,17,37,53];
//time sols:= solveThueMahler(clist,primelist,a : verb:=false); sols;
