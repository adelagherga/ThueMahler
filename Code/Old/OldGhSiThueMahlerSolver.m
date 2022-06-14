// To solve F(X,Y)=a p1^z1 \cdots pv^zv
// Here F is irreducible homogeneous polynomial with coefficients in \Z
// of degree \ge 3
// a an integer coprime to the p_i
// X,Y are coprime
// and Y is coprime to c0 which the leading coefficients of F.

// Let x := c0 X, y:=Y.
// Then we still have gcd(x,y)=1.

load "structure.m";
// For the commands reduce, multGroup.

//=================================================================
//
// Bounds!!
//
// We are looking at the equation
//
// (*) c_0 X-\theta Y =  \tau \cdot \delta_1^{b_1} \cdots \delta_r^{b_r}.
//
// The commands below give a bound for B:=max(|b_1|,...,|b_r|)
// using the Baker's theory (the bounds of Matveev and of Yu).
// They also reduce these bounds using lattice reduction
// as explained in the paper. The number of constants
// c1, c2, ... follows exactly that of the paper.
//
// Notation:
// K	the number field \Q(\theta) of degree \ge 3.
// \tau, \delta_i 	non-zero elements of K.
// deltaList 	the list delta_1,...,delta_r.
// S	a set of prime ideals of K satisfying e(fp/p)=f(fp/p)=1
// 	(delta_1,..,delta_r is in fact a basis for the $S$-unit
// 	group \OO_S^\times (modulo torsion)).
// 	Moreover the rational primes p_i
// 	that are below the fp_i in S are distinct.
//
// verb..	is a flag. The default is false.
//		If set to true, prints out verbose output.
//
//================================================================

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
    s1,s2 := Signature(K);
    assert d eq s1+2*s2;
    assert #embeds eq s1+s2;
    c13 := (s1+s2+2*#S)/d;
    c14 := 2*htau + c13*Max(c8,c10);
    c15 := c13*Max(c9,c12);
    c16 := c14 + (3/2)*Log(2) + 2*htheta + htau ;
    if #S ne 0 then
	shortS := S[1..(#S-1)];
	M := [ [LocalDegree(i)*Log(AbsoluteValue(Evaluate(delta,i))) : i in embeds] cat [Log(Norm(P)^(-Valuation(delta*OK,P))) : P in shortS] : delta in deltaList ];
    else
	embeds:=embeds[1..(#embeds-1)];
	M := [ [LocalDegree(i)*Log(AbsoluteValue(Evaluate(delta,i))) : i in embeds]  : delta in deltaList ];
    end if;
    M:=Matrix(M);
    assert NumberOfRows(M) eq r;
    assert NumberOfColumns(M) eq r;
    Minv:=M^(-1);
    Minv:=Rows(Minv);
    Minv:=[Eltseq(r) : r in Minv];
    Minv:=&cat(Minv);
    assert #Minv eq r^2 ;
    Minv := [ AbsoluteValue(m) : m in Minv ];
    c17 := Max(Minv);
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
    if ww in LL then
	return 0;
    end if;
    ww:=AmbientSpace(Parent(ww))!ww; // Changing
    // the coefficient ring of ww to the rationals.
    n:=Rank(LL);
    assert n eq Degree(LL);
    LL:=LLL(LL);
    B:=Basis(LL);
    b1:=B[1];
    B:=[Eltseq(b) : b in B];
    B:=[[Rationals()!a : a in b] : b in B];
    B:=Matrix(B);
    Binv:=B^-1;
    sigma:=Eltseq(ww*B^-1);
    sigma:=[AbsoluteValue(t-Round(t)) : t in sigma];
    sigma:=[t : t in sigma | t ne 0];
    sigmai0:=sigma[#sigma];
    return 2^n*sigmai0*Norm(b1);
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
	kprime:=Max([ Ceiling(fact[2]/Valuation(p*OK,fact[1]))  : fact in Factorisation(fb)]);
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

/*
valuationNeq:=function(theta,tau,deltaList,fp,cB1,k);
	// We're looking at (*)
	// fp is a prime in S.
	// cB1 is an upper bound for the L^2-norm of (b_1,..,b_r).
	// This return true if \ord_\fp(c_0 X - Y \theta) = k leads
	// to a contradiction, otherwise returns false.
	// (i.e. true means we've succeed in showing
	// \ord_\fp(c_0 X- Y\theta) < k).
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
		return true;
	end if;
	fb:=fa^k/(taunum+fa^k);
	tau0:=(theta0-theta)/tau;
	for fact in Factorisation(fb) do
		assert Valuation(tau0*OK,fact[1]) eq 0; // Sanity check!
	end for;
	if fb eq 1*OK then
		kprime:=0;
	else
		kprime:=Max([ Ceiling(fact[2]/Valuation(p*OK,fact[1]))  : fact in Factorisation(fb)]);
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
		return true;
	end if;
	w:=tau0im@@phi;
	L:=Kernel(phi);
	Z1:=FreeAbelianGroup(1);
	eta:=hom<Zr->Z1 | [ Valuation(delta,fp)*Z1.1  : delta in deltaList  ]>;
	H:=Kernel(eta);
	vp:=(k-Valuation(tau,fp))*Z1.1;
	if vp in Image(eta) eq false then
		return true;
	end if;
	v:=vp@@eta;
	D,i1,i2,p1,p2:=DirectSum(H,L);
	kappa:=hom<D->Zr | [ p1(d)+p2(d)  : d in OrderedGenerators(D)]>;
	assert Image(kappa) eq sub<Zr | OrderedGenerators(H) cat OrderedGenerators(L) >;
	if v-w in Image(kappa) eq false then
		return true;
	end if;
	vmw:=(v-w)@@kappa;
	h1:=p1(vmw);
	l1:=p2(vmw);
	assert v-w eq h1+l1;
	M:=H meet L;
	u:=w+l1;
	ZZr:=StandardLattice(r);
	MM:=sub<ZZr | [ ZZr!(Eltseq((Zr!m))) : m in OrderedGenerators(M)]>;
	uu:=ZZr!Eltseq(Zr!u);
	DMusq:=Norm(ClosestVectors(MM,-uu)[1]+uu);
	// This is D(M,u)^2 in the notation of the paper.
	if DMusq gt cB1^2 then
		return true;
	else
		return false;
	end if;
end function;
*/

cvp:=function(LL,vv,distSq)
    assert distSq ge 0;
    if distSq gt 0 then
	cvp:=[pr[1] : pr in CloseVectors(LL,vv,distSq)];
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
    //print "depth=", depth;
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

/*
cK:=function(tau,deltaList,Zr,fp,krange);
	K:=NumberField(Universe([tau] cat deltaList));
	theta:=K.1;
	d:=Degree(K);
	assert d ge 3;
	OK:=MaximalOrder(K);
	r:=#deltaList;
	assert r eq #Invariants(Zr);
	ZZr:=StandardLattice(r);
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
	Z1:=FreeAbelianGroup(1);
	eta:=hom<Zr->Z1 | [ Valuation(delta,fp)*Z1.1  : delta in deltaList  ]>;
	etaLcum:=eta(Zr);
	assert #OrderedGenerators(etaLcum) eq 1;
	modulus:=Eltseq(Z1!(etaLcum.1))[1];
	class:=Valuation(tau,fp);
	krange:=[kmin..kmax];
	krange:=[k : k in krange | IsDivisibleBy(k-class,modulus) ];
	if #krange eq 0 then
		return [], [* *], [* *];
	end if;
	H:=Kernel(eta);
	ckList:=[];
	cosetPairs:=[* *];
	latPairs:=[* *];
	kmin:=Minimum(krange);
	assert kmin ge 0;
	if kmin eq 0 then
		Append(~ckList,0);
		vp:=(-Valuation(tau,fp))*Z1.1;
		cosetPairs:=cosetPairs cat [* [* vp@@eta, H *] *];
		LLcumNew:=sub<ZZr | [ ZZr!Eltseq((Zr!g)) : g in OrderedGenerators(H)]>;
		wwcumNew:=ZZr!Eltseq(Zr!(vp@@eta));
		latPairs:=latPairs cat [* [* wwcumNew, LLcumNew *] *];
	end if;
	krange:=[k : k in krange | k ge 1];
	krange:=[ k : k in krange | (taunum+fa^k) eq ((theta-theta0)*OK+fa^k)];
	for k in krange do
		fb:=fa^k/(taunum+fa^k);
		tau0:=(theta0-theta)/tau;
		for fact in Factorisation(fb) do
			assert Valuation(tau0*OK,fact[1]) eq 0; // Sanity check!
		end for;
		kprime:=Max([ Ceiling(fact[2]/Valuation(p*OK,fact[1]))  : fact in Factorisation(fb)]);
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
		phi:=hom<Zr->G | alphaList>;
		// This the map \phi in the paper.
		if tau0im in Image(phi)  then
			w:=tau0im@@phi;
			L:=Kernel(phi);
			vp:=(k-Valuation(tau,fp))*Z1.1;
			v:=vp@@eta;
			tf,wcumNew,LcumNew:=cosetIntersect(Zr,v,H,w,L);
			if tf then
				invs:=Invariants(LcumNew);
				assert #invs eq r-1; // Checking that the rank has is reduced by 1.
				Append(~ckList,k);
				cosetPairs:=cosetPairs cat [* [* wcumNew, LcumNew *] *];
				LLcumNew:=sub<ZZr | [ ZZr!Eltseq((Zr!g)) : g in OrderedGenerators(LcumNew)]>;
				wwcumNew:=ZZr!Eltseq(Zr!wcumNew);
				latPairs:=latPairs cat [* [* wwcumNew, LLcumNew *] *];
			end if;
		end if;
	end for;
	return ckList, cosetPairs, latPairs;
end function;

horzSift:=function(tau,deltaList,Zr,S,range,cB1sq,res1,res2,res3);
	r:=#deltaList;
	assert r eq #Invariants(Zr);
	ZZr:=StandardLattice(r);
	if #S eq 0 then
		return res1,res2,res3;
	end if;
	fp:=S[1];
	krange:=range[1];
	ckList,cosetPairs:=cK(tau,deltaList,Zr,fp,krange);
	resNew1:=[* *];
	resNew2:=res2;
	resNew3:=res3;
	for i in [1..#ckList] do
		kfp:=ckList[i];
		wfp:=cosetPairs[i,1];
		Lfp:=cosetPairs[i,2];
		for j in [1..#res1] do
			path:=res1[j,1];
			wres:=res1[j,2];
			Lres:=res1[j,3];
			tf,wres,Lres:=cosetIntersect(Zr,wres,Lres,wfp,Lfp);
			if tf then
				det,len:=detSVP(Zr,Lres);
        			if len gt 4*cB1sq then
                			vecs:=vectorsInCoset(Zr,Lres,wres,cB1sq);
					resNew2:=resNew2 cat [* [* path cat [* kfp *], wres,Lres, vecs  *] *];
				else
					resNew1:=resNew1 cat [* [* path cat [* kfp *], wres,Lres  *] *];
				end if;
			else
				resNew3:=resNew3 cat [* path cat [* kfp *] *];
			end if;
		end for;
	end for;
	return $$(tau,deltaList,Zr,S[2..#S],range[2..#range], cB1sq, resNew1, resNew2, resNew3);
end function;

deeperHorzSift:=function(tau,deltaList,Zr,cB1sq,res1,res2,res3);
	if #res1 eq 0 then
		return res2,res3;
	end if;
	path:=res1[1,1];
	wcum:=res1[1,2];
	Lcum:=res1[1,3];
	bigInfs:=res1[1,4];
	assert #bigInfs ge 1;
	res1:=res1[2..#res1];
	rk:=#Invariants(Lcum);
	imLList:=[ #I[4]/Index(Zr,Kernel(I[3])+Lcum) : I in bigInfs];
	Sort(~imLList,~permut);
	bigInfs:=[* bigInfs[i^permut] : i in [1..#bigInfs] *];
	bigInf:=bigInfs[1];
	bigInfs:=bigInfs[2..#bigInfs];
	q:=bigInf[1];
	phiq:=bigInf[3];
	Tq:=bigInf[4];
	phiqLcum:=phiq(Lcum);
	phiwcum:=phiq(wcum);
	Tqcut:=[t : t in Tq | (t-phiwcum) in phiqLcum ];
	K:=Kernel(phiq);
	for t in Tqcut do
		s:=t@@phiq;
		tf,wcumNew,LcumNew:=cosetIntersect(Zr,wcum,Lcum,s,K);
		if tf then
			det,len:=detSVP(Zr,Lcum);
			if len gt 4*cB1sq or #bigInfs eq 0 then
				vecs:=vectorsInCoset(Zr,LcumNew,wcumNew,cB1sq);
				res2:=res2 cat [* [* path cat [* <q,s> *], wcumNew, LcumNew, vecs  *] *];
				res3:=res3 cat [* path cat [* <q,s> *] *];
			else
				res1:=res1 cat [* [* path cat [* <q,s> *], wcumNew, LcumNew, bigInfs  *] *];
			end if;
		else
			res3:=res3 cat [* path cat [* <q,s> *] *];
		end if;
	end for;
	return $$(tau,deltaList,Zr,cB1sq,res1,res2,res3);
end function;
*/

sift:=function(tau,deltaList,Zr,Lcum,wcum,SLeft,rangeLeft,cB1sq,bigInfs,depth)
    //print "depth=", depth;
    assert #rangeLeft eq #SLeft;
    rk:=#Invariants(Lcum);
    det,len:=detSVP(Zr,Lcum);
    //expect:=(1/det)*Pi(RealField())^(rk/2)*cB1sq^(rk/2)/Gamma(1+rk/2);
    if len gt 4*cB1sq then
	vecs:=vectorsInCoset(Zr,Lcum,wcum,cB1sq);
	//print "Expecting", expect;
	//print "found", #vecs;
	for I in bigInfs do
	    phiq:=I[3];
	    Tq:=I[4];
	    vecs:=[v : v in vecs | phiq(Domain(phiq)!v) in Tq];
	end for;
	//print "cut down to", #vecs;
	//print #SLeft;
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
	    vecs:=vecs cat $$(tau,deltaList,Zr,LcumNew,wcumNew,SLeft,rangeLeft,cB1sq,bigInfs,depth+1);
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
	kprime:=Max([ Ceiling(fact[2]/Valuation(p*OK,fact[1]))  : fact in Factorisation(fb)]);
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
	phi:=hom<Zr->G | alphaList>;
	// This the map \phi in the paper.
	if tau0im in Image(phi)  then
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
		//end if;
	    end if;
	end if;
    end for;
    return vecs;
end function;

c21Func:=function(theta,tau,deltaList,S,cB1)
    // Evaluate c_21 in the notation of the paper.
    // Here cB1 is an upper bound for the L^2-norm
    // of (b_1,..,b_r).
    K:=NumberField(Universe([theta] cat [tau] cat deltaList));
    d:=Degree(K);
    assert d ge 3;
    assert theta eq K.1;
    OK:=MaximalOrder(K);
    expSbds:=[];
    c21:=0;
    for fp in S do
	km1:=valuationBound(theta,tau,deltaList,fp,cB1); // This is k-1
	// in the notation of the paper.
	kfpp:=Valuation(tau*OK,fp);
	kfppp:=km1-kfpp;
	Append(~expSbds,<-kfpp,kfppp>);
	// <-kfpp,kfppp> are lower and upper bounds
	// for the fp-valuation of epsilon=delta_1^b_1 ... delta_r^b_r.
	c21:=c21+Max(0,kfppp)*Log(Norm(fp));
    end for;
    return c21, expSbds;
end function;

constants:=function(K,theta,tau)
    // Returns the constants c22, c23, c27, c28 in the notation of
    // the paper.
    d:=Degree(K);
    assert d ge 3;
    s1,s2:=Signature(K);
    pls:=InfinitePlaces(K);
    realPls:=[pl : pl in pls | LocalDegree(pl) eq 1];
    cmxPls:=[pl : pl in pls | LocalDegree(pl) eq 2];
    assert s1 eq #realPls;
    assert s2 eq #cmxPls;
    if #cmxPls eq 0 then
	c22:=0;
    else
	c22:=2*&+[Log(Max(1,AbsoluteValue(Evaluate(tau,pl)/Imaginary(Evaluate(theta,pl)))))
		  : pl in cmxPls ];
    end if;
    t:=#realPls;
    realtheta:=[Evaluate(theta,pl) : pl in realPls];
    realtau:=[Evaluate(tau,pl) : pl in realPls];
    if t le 1 then
	c23:=1; // We in fact do not use c23 when #realPls is 0.
    else
	c23:=Min([(AbsoluteValue(realtheta[i]-realtheta[j]))/
		  (AbsoluteValue(realtau[i])+AbsoluteValue(realtau[j]))
		  : i,j in [1..t] | i lt j]);
    end if;
    tauconjAbs:=[ AbsoluteValue(Evaluate(tau,pl)) : pl in pls ];
    c27:=Min(tauconjAbs);
    c28:=Max(tauconjAbs);
    return c22, c23, c27, c28;
end function;

approxLattice:=function(tau,deltaList,S,sigma,C)
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
    LatMat:=DiagonalMatrix([1 : j in [1..s+1]] cat [0 : j in [1..d-2]]);
    for i in [1..v] do
	LatMat[r+i,s+1+w+i] := Cpi;
    end for;
    ww:=[0 : j in [1..(s+1)]];
    otherRealPls:=[pl : pl in realpls | pl ne sigma];
    otherPls:=otherRealPls cat cmxpls;
    assert #otherPls eq u+v-1;
    sigma2:=otherPls[1];
    otherPls:=otherPls[2..(u+v-1)];
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

reducedBoundFixedEmbedding2:=function(K,theta,tau,deltaList,S,consts,sigma : verb:=false)
    // sigma is a fixed REAL embedding of K.
    // Compute a reduced bound for B under the assumption
    // that \eta makes |sigma(epsilon)| minimal.
    // Here consts is the list [c20,c17,c22,c23,c26,c27,c28].
    c20,c17,c22,c23,c26,c27,c28:=Explode(consts);
    cB0:=c20;
    if verb then
	print "The initial bound is", c20;
    end if;
    d:=Degree(K);
    r:=#deltaList;
    u,v:=Signature(K);
    w:=u+v-2;
    s:=#S;
    n:=r+v;
    finished:=false;
    repeat
	cB1:=r^(1/2)*cB0; // Converting from a bound on the infinity norm
	// to a bound on the L^2 norm.
	c21,expSbds:=c21Func(theta,tau,deltaList,S,cB1);
	if verb then
	    print "Exponent bounds", expSbds;
	end if;
	c24:=c21+c22+(u-1)*Log(Max(1,1/c23));
	c25:=Exp(c24);
	c29:=(c25*c28)/(c23*c27);
	c30:=Max(2*c17*c24, Log(2*c29)/c26);
	cB2:=(r*cB0+1)/2;
	cB3:=(2*r*cB0+3)/2;
	cB4:=(2*w*cB2+v*cB3)/(4*w+v);
	cB5:=((s+1)*cB0^2+w*cB2^2+v*cB3^2)^(1/2);
	C:=Ceiling(cB5^(n/(d-2)));
	// We follow the procedure in the section "Reduction of Bounds"
	// to repeatedly reduce the initial bound.
	repeat
	    ZZn:=StandardLattice(n);
	    M,ww:=approxLattice(tau,deltaList,S,sigma,C);
	    ww:=ZZn!ww;
	    LL:=Lattice(M);
	    DLwsq:=distanceLBsq(LL,ww);
	    //print C,DLwsq+0.0;
	    // This D(L,w)^2 in the notation of paper.
	    tf1:=DLwsq gt cB5^2;
	    tf2:=(ww in LL) eq false;
	    if (tf1 and tf2) eq false then
		if verb then
		    print "Increasing C";
		end if;
		C:=10*C;
	    end if;
	until tf1 and tf2;
	denom := ((DLwsq-cB5^2+(4*w+v)*cB4^2)/(4*w+v))^(1/2) - cB4;
	cB0New:=(1/c26)*Log((2*C*c29)/denom);
	cB0New:=Max(c30,cB0New);
	if cB0New lt 10^10 then
	    cB0New:=Floor(cB0New);
	end if;
	if cB0New lt cB0 then
	    if verb then
		print "The new bound is", cB0New;
	    end if;
	    cB0:=cB0New;
	else
	    finished:=true;
	end if;
    until finished;
    return cB0, expSbds;
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
    Sort(~S,fn); // Sorting S so that the prime ideals
    // with largest norm come first.
    assert &and[ fact[1] in S : fact in Factorisation(tau*OK) | fact[2] lt 0 ];
    // This is a sanity check. According to the paper
    // the denominator ideal of tau is supported
    // on S.
    c20,c17:=initialBound(K,theta,tau,deltaList,S);
    c22, c23, c27, c28:=constants(K,theta,tau);
    c26:=1/(2*c17);
    consts:=[c20,c17,c22,c23,c26,c27,c28];
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
	    print "We're in the totally complex case";
	    print "The initial bound is", c20;
	end if;
	cB0:=c20;
	finished:=false;
	repeat
	    cB1:=r^(1/2)*cB0; // Converting from a bound on the infinity norm
	    // to a bound on the L^2 norm.
	    c21,expSbds:=c21Func(theta,tau,deltaList,S,cB1);
	    if verb then
		print "Exponent bounds", expSbds;
	    end if;
	    cB0New:=2*c17*(c21+c22);
	    if cB0New lt cB0 then
		if verb then
		    print "The reduction process gives a new bound of", cB0New;
		end if;
		cB0:=cB0New;
	    else
		if verb then
		    print "The reduction process gives a worse bound of", cB0New;
		end if;
		finished:=true;
	    end if;
	until finished;
	for i in [1..#S] do
	    expSbds[i,1]:=expSbds[i,1]+Valuation(tau,S[i]);
	    expSbds[i,2]:=expSbds[i,2]+Valuation(tau,S[i]);
	end for;
	return cB0, S, expSbds;
    end if;
    assert t ge 1; // We've now finished with the totally complex case.
    if verb then
	print "The initial bound is", c20;
	print "We're carrying out the reduction process for each real embedding separately";
    end if;
    cB0List:=[];
    expSbdsList:=[];
    for i in [1..t] do
	if verb then
	    print "++++++++++++++++++++++++++";
	    print "Dealing with the", i, "-th real embedding";
	end if;
	eta:=realPls[i];
	cB0eta, expSbds := reducedBoundFixedEmbedding2(K,theta,tau,deltaList,S,consts,eta : verb:=verb);
	Append(~cB0List,cB0eta);
	Append(~expSbdsList,expSbds);
    end for;
    expSbds:=expSbdsList[1];
    for expSbds2 in  expSbdsList[2..#expSbdsList] do
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
    return Max(cB0List), S, expSbds;
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
    return L,M;
end function;

alg2:=function(c0,th,p)
    // This is an implementation of Algorithm
    // 2 in the paper, plus the refinements explained
    // in the remarks.
    // Input: c0, th (=\theta), p.
    // Returns Lp, Mp.
    OK:=MaximalOrder(Parent(th));
    L1,M1:=alg1( -th/c0 , c0, p);
    L2,M2:=alg1(c0/(p*th) , -p*th, p);
    Lp:=L1 join L2;
    Mp:=M1 join M2;
    // Now for the refinements.
    Mp:={ <pr[1]/pr[2]^Valuation(pr[1],pr[2]) , pr[2]> : pr in Mp  };
    for pr in Mp do
	fbd:=pr[1];
	fp:=pr[2];
	Lp:={fb : fb in Lp | IsIntegral(fb/fbd) eq false or fb/fbd ne fp^Valuation(fb/fbd,fp)};
    end for;
    if IsDivisibleBy(c0,p) then
	d:=Degree(NumberField(OK));
	Lp:={fb : fb in Lp | Valuation(Norm(fb),p) ge (d-1)*Valuation(c0,p)};
    end if;
    print Lp,Mp;
    return Lp,Mp;
end function;

/*
algs1and2:=function(c0,th,p);
    // This is the old algs1and2
	// This is an implementation of Algorithms
	// 1 and 2 in the paper, plus the refinements explained
	// in the remarks.
	// Input: c0, th (=\theta), p.
	// Returns Lp, Mp.
	OK:=MaximalOrder(Parent(th));
	fprs:=Factorisation(p*OK);
	fprs:=[fact[1] : fact in fprs]; // the prime ideals above p.
	f:=MinimalPolynomial(th);
	assert &and[ c in Integers() : c in Coefficients(f) ];
	assert IsMonic(f);
	d:=Degree(NumberField(OK));
	assert d eq Degree(f);
	v:=Valuation(Discriminant(f),p);
	prec:=10*(v+1);
	Zp:=pAdicRing(p,prec);
	rts:=Roots(f,Zp);
	rts:=[Integers()!r[1] : r in rts];
	Lp:={};
	Mp:={};
	// Algorithm 1.
	t:=Valuation(c0,p)+1;
	ulist:=[c0*w : w in [0..(p-1)]];
	repeat
		ulistNew:=[];
		for u in ulist do
			cPu:=[fq : fq in fprs | Valuation((u-th)*OK,fq) ge t*RamificationDegree(fq)];
			fbu:=p^t*OK+(u-th)*OK;
			if #cPu eq 0 then
				Lp:=Lp join {fbu};
			elif #cPu eq 1 then
				fp:=cPu[1];
				efp:=RamificationDegree(fp)*InertiaDegree(fp);
				rtcount:=#[alpha : alpha in rts | Valuation(u-alpha,p) ge t];
				if efp eq 1 and rtcount ge 1 then
					Mp:=Mp join {<fbu,fp>};
				else
					ulistNew:=ulist cat [ u+p^t*w : w in [0..(p-1)]];
				end if;
			else
				ulistNew:=ulist cat [ u+p^t*w : w in [0..(p-1)]];
			end if;
		end for;
		ulist:=ulistNew;
		t:=t+1;
	until #ulist eq 0; // End of Algorithm 1.
	// Algorithm 2.
	if Valuation(c0,p) eq 0 then
		ulist:=[p*w : w in [0..(p-1)]];
		t:=2;
		repeat
			ulistNew:=[];
			for u in ulist do
				cPu:=[fq : fq in fprs | Valuation(c0-u*th,fq) ge t*RamificationDegree(fq)];
				fbu:=(c0-u*th)*OK+p^t*OK;
				if #cPu eq 0 then
					Lp:=Lp join {fbu};
				else
					ulistNew:=ulistNew cat [u+p^t*w : w in [0..(p-1)]];
				end if;
			end for;
			ulist:=ulistNew;
			t:=t+1;
		until #ulist eq 0;
	end if; // End of Algorithm 2.
	// Now for the refinements.
	Mp:={ <pr[1]/pr[2]^Valuation(pr[1],pr[2]) , pr[2]> : pr in Mp  };
	for pr in Mp do
		fbd:=pr[1];
		fp:=pr[2];
		Lp:={fb : fb in Lp | IsIntegral(fb/fbd) eq false or fb/fbd ne fp^Valuation(fb/fbd,fp)};
	end for;
	//repeat
	//	removal:=[];
	//	for pr1,pr2 in Mp do
	//		if pr1 ne pr2 then
	//			if pr1[2] eq pr2[2] then
	//				fp:=pr1[2];
	//				fb:=pr1[1];
	//				fbd:=pr2[1];
	//				if IsIntegral(fb/fbd) and fb/fbd eq fp^Valuation(fb/fbd) then
	//					removal:=removal cat [pr1];
	//				end if;
	//			end if;
	//		end if;
	//		if #removal ge 1 then
	//			Exclude(~Mp,removal[1]);
	//		end if;
	//	end for;
	//until #removal eq 0;
	//Now for the more refinements.
	if IsDivisibleBy(c0,p) then
		Lp:={fb : fb in Lp | Valuation(Norm(fb),p) ge (d-1)*Valuation(c0,p)};
	end if;
	return Lp,Mp;
end function;
*/

normInv:=function(R,OK)
    // R a positive integer.
    // Returns all ideals of OK with norm equal to R.
    assert R in Integers();
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
	invs:=normInv(R0,OK);
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
    return tauDeltaList;
end function;

smallSieveInfo:=function(c0, theta)
    qBound:=200;
    print "Getting the small sieve information.";
    K:=NumberField(Parent(theta));
    assert K.1 eq theta;
    OK:=MaximalOrder(K);
    qlist:=[q : q in PrimesInInterval(2,qBound) | Valuation(c0,q) eq 0];
    smallInf:=[* *];
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
	    Rqstar:=[ rho : rho in Rq | &and [Valuation(rho*OK,fq) eq 0 : fq in qfacts ]];	// R_q \cap \OO_q^\times.
	    imdelFunc:=func<del | toBq((reduce(del,modq,q*OK))@@eta)>;
	    // Function to compute the image of del in Bq. Here del
	    // must be an element of O_q.
	    SqShifted:=[toBq((modq(rho))@@eta) : rho in Rqstar];
	    // Subtract the image of tau from SqShifted to get Sq.
	    Append(~smallInf, [* q, Bq, imdelFunc, SqShifted, Rqstar, eta, modq, fromZqs *]);
	end if;
    end for;
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

solveThueMahler:=function(clist,a,primelist : verb:=false)
    // Input: clist, a, primelist, bound
    // clist is a list of coefficients c_0,c_1,..,c_n.
    // a is an integer.
    // primelist is a list of the primes p_1,p_2,..,p_v.
    // This solves c_0 X^n+...+c_n Y^n= a \times p_1^{z_1} ... p_t^{z_t}
    // subject to the assumptions that X, Y are coprime integers
    // and gcd(Y,c_0)=1.
    // Output: sols.
    // sols is a list of solutions to the Thue--Mahler equation.
    d:=#clist-1;
    ZUV<U,V>:=PolynomialRing(Integers(),2);
    F:=&+[clist[i+1]*U^(d-i)*V^i : i in [0..d]];
    c0:=clist[1];
    tauDeltaList:=prep2(clist,a,primelist);
    if #tauDeltaList eq 0 then
	print "tauDeltaList is empty!";
	return {};
    end if;
    K:=Universe([pr[1] : pr in tauDeltaList] cat &cat[pr[2] : pr in tauDeltaList]);
    K:=NumberField(K);
    theta:=K.1;
    OK:=MaximalOrder(K);
    assert Degree(K) eq (#clist-1);
    sols:={};
    eqncount:=0;
    //smallInf:=smallSieveInfo(c0, theta, qBound, smoothBound);
    smallInf:=smallSieveInfo(c0, theta); // qBound);
    print "We have to solve", #tauDeltaList, "equations.";
    print "The ranks are", Sort([#pr[2] : pr in tauDeltaList]);
    for pr in tauDeltaList do
	eqncount:=eqncount+1;
	tau:=pr[1];
	deltaList:=pr[2];
	cB0,S,range:=reducedBound(tau,deltaList : verb:=verb);
	print "S is", S;
	print "range is", range;
	cB0:=Floor(cB0);
	cB1sq:=(#deltaList)*cB0^2;
	print "Bound on norm squared of (b1,..,br) is", cB1sq;
	print "Applying the Dirichlet sieve to equation number",
	      eqncount, "out of", #tauDeltaList;
	Zr, bigInfs:=bigSieveInfo(tau,deltaList,smallInf);
	vecs:=sift(tau,deltaList,Zr,Zr,Zr!0,S,range,cB1sq,bigInfs,1);
	print "Finished applying the Dirichlet sieve to equation number", eqncount;
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
			if GCD(sol[1],sol[2]) eq 1 and GCD(a,sol[2]) eq 1 and
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
    return sols;
end function;

// Example 1
//clist:=[3,2,7,2];
//a:=1;
//primelist:=[2,3,7,41];
//time sols:=solveThueMahler(clist,a,primelist);
//sols;

// Example 2
//clist:=[7,1,29,-25];
//a:=1;
//primelist:=[2,3,7,37,53];
//time sols:=solveThueMahler(clist,a,primelist);
//sols;

// Example 3 (improvement on Soydan and Tzanakis)
//clist:=[3,65,-290,-2110,975,3149];
//a:= -1;
//primelist:=[2,3,5,7,11,13,17];
//time sols:=solveThueMahler(clist,a,primelist);
//sols;

/*
// Example 4
clist:=[1,0,0,0,-2];
primelist:=[2, 7, 23, 31, 47, 71, 73, 79, 89];
//time sols1:=solveThueMahler(clist,1,primelist);
//time sols2:=solveThueMahler(clist,-1,primelist);
//sols1;
//sols2;

// Example 5
SetClassGroupBounds("GRH");
clist:=[ 5,  1,  4,  1,  6,  1,  6,  0,  6,  0,  4, -2];
a:=1;
primelist:=[2,3,5,7,11];
//time sols:=solveThueMahler(clist,a,primelist);
//sols;

// Example 6 (de Weger--Tzanakis)
clist:=[1,-23,5,24];
primelist:=[2,3,5,7];
//time sols:=solveThueMahler(clist,1,primelist) join solveThueMahler(clist,-1,primelist);
//sols;
*/
