// To reduce F(X,Y)=a p1^z1 \cdots pv^zv
// to S-unit equations.
// Here F is irreducible hgs with coefficients in \Z
// of degree \ge 3
// a an integer coprime to the p_i
// X,Y are coprime
// and Y is coprime to c0 which the leading coefficients of F. 

// Let x := c0 X, y:=Y.
// Then we still have gcd(x,y)=1.


		
                


principalize:=function(fa,fplist);
	// fa is an ideal of \OO_K
	// and fplist is a list of prime ideals.
	// We consider the equation fa * fp_1^{n_1} * ... * fp_u^{n_u} = principal ideal. 
	// This returns 
	// tf, alpha, gammalist, matA, rr.
	// Here tf is true or false. False means that [fa]^{-1} is not in the image
	// of phi (in the notation of the letter) and so the equation has no solution.
	// If tf is false then the other values return are all zero.
	// If tf is true ([fa]^{-1} is in the image of phi),
	// then alpha \in K^*
	// gammalist is a list gamma_1,..,gamma_u, and these
	// values are as in equation (4) of the letter.
	// It also returns the matrix A, and the vector rr
	// in the notation of the letter.
	// If fplist is empty then it just returns tf, alpha, [], 0, 0
	// where tf is true/false depending on whether fa is principal or not,
	// and if so alpha will be a generator.
	K:=NumberField(Parent(Basis(fa)[1]));
	OK:=MaximalOrder(K);
	ClK,eta:=ClassGroup(K); // Given an ideal fa, we obtain
							// the class in ClK by fa@@eta.
	u:=#fplist;
	if u eq 0 then
		tf,alpha:=IsPrincipal(fa);
		if tf then
			return tf, alpha, [K | ], 0, 0;
		else
			return tf, 0, 0, 0, 0;
		end if;
	end if;
	Zu:=FreeAbelianGroup(u);
	phi := hom< Zu -> ClK | [ fp@@eta : fp in fplist ]>;
	img:=Image(phi);
	if -fa@@eta in img then
		rr:=(-fa@@eta)@@phi;
		rr:=Eltseq(Zu!rr);
		ker:=Kernel(phi);
		A:=[Eltseq(Zu!a) : a in Generators(ker)]; // For now A is a list of vectors.
		assert #A eq u; // So the kernel has rank u.
		matA:=Transpose(Matrix(A)); // This is the matrix denoted by A
									// in the letter.
		assert AbsoluteValue(Determinant(matA)) eq #img;		
		fa2:=fa*&*[fplist[i]^rr[i] : i in [1..u]];
		tf,alpha:=IsPrincipal(fa2);
		assert tf; // The ideal really is principal, and alpha
					// is a generator.
		clist:=[ &*[fplist[i]^a[i] : i in [1..u] ]  : a in A ]; // These
				// are the ideals denoted by \mathfrak{c} in note.
		gammalist:=[];
		for fc in clist do
			tf, gamma:=IsPrincipal(fc);
			assert tf;
			Append(~gammalist,gamma);
		end for;
		return true, alpha, gammalist, matA, rr;
	else	
		return false, 0, 0, 0, 0;
	end if; 
end function;


algs1and2:=function(c0,th,p);
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
	n:=Degree(NumberField(OK));
	assert n eq Degree(f);
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
					ulistNew:=ulist cat [ u+p^(t+1)*w : w in [0..(p-1)]];
				end if;
			else
				ulistNew:=ulist cat [ u+p^(t+1)*w : w in [0..(p-1)]];
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
					ulistNew:=ulistNew cat [u+p^(t+1)*w : w in [0..(p-1)]];
				end if; 
			end for;	
			ulist:=ulistNew;
			t:=t+1;
		until #ulist eq 0;
	end if; // End of Algorithm 2.
	// Now for the refinements.
	for pr in Mp do
		fbd:=pr[1];
		fp:=pr[2];
		Lp:={fb : fb in Lp | IsIntegral(fb/fbd) eq false or fb/fbd ne fp^Valuation(fb/fbd,fp)};
	end for;
	repeat
		removal:=[];
		for pr1,pr2 in Mp do
			if pr1 ne pr2 then
				if pr1[2] eq pr2[2] then
					fp:=pr1[2];
					fb:=pr1[1];
					fbd:=pr2[1];
					if IsIntegral(fb/fbd) and fb/fbd eq fp^Valuation(fb/fbd) then
						removal:=removal cat [pr1];
					end if;
				end if;
			end if;
			if #removal ge 1 then
				Exclude(~Mp,removal[1]);
			end if;	
		end for;
	until #removal eq 0;
	//Now for the more refinements.
	if IsDivisibleBy(c0,p) then
		Lp:={fb : fb in Lp | Valuation(Norm(fb),p) ge (n-1)*Valuation(c0,p)};
	end if;	
	MpNew:={};
	for pr in Mp do
		fb:=pr[1];
		fp:=pr[2];
		if Valuation(Norm(fb),p) lt (n-1)*Valuation(c0,p) then
			fbd:=fb*fp^((n-1)*Valuation(c0,p)-Valuation(Norm(fb),p));
			MpNew:=MpNew join {<fbd,fp>};
		else
			MpNew:=MpNew join {pr};
		end if;
	end for;
	Mp:=MpNew;
	return Lp,Mp;
end function;

normInv:=function(R,OK);
	// R a positive integer.
	// Returns all ideals of OK with norm equal to R.
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

prep1:=function(clist,a,primelist);
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
	K<th>:=NumberField(f);
	OK:=MaximalOrder(K);
	th:=OK!th;
	afplist:=[* [* 1*OK, [] *] *];
	for p in primelist do
		afplistNew:=[* *];
		Lp,Mp:=algs1and2(c0,th,p);	
		afplistNew1:=[* [* pr[1]*fb, pr[2] *] : fb in Lp, pr in afplist  *];
		afplistNew2:=[* [* pr[1]*qr[1], pr[2] cat [qr[2]] *] : qr in Mp, pr in afplist  *];
		afplist:=afplistNew1 cat afplistNew2;
	end for;
	R:=Integers()!(a*c0^(n-1));
	afplistNew:=[* *];
	for pr in afplist do
		af:=pr[1];
		R0:=AbsoluteValue(R div GCD(Norm(af),R));
		assert &and[Valuation(R0,p) eq 0 : p in primelist];
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

prep2:=function(clist,a,primelist);
	// clist is a list of coefficients c_0,c_1,..,c_n.
	// a is an integer.
	// primelist is a list of the primes p_1,p_2,..,p_v.
	// This returns a list of the possible quadruples [* alpha, gammalist, matA, r *] 
	// where alpha in K^*, and gammalist is a list gamma_1,...,gamma_u 
	// so that (c_0 X - th Y)OK =alpha*gamma_1^{m_1}*..*gamma_u^{m_u} (as in equation (4)).
	// matA and rr are the matrix A and the vector rr, so that 
	// nn = mm A + rr, where nn is the vector of exponents in (3)
	// and mm is the vector of exponents in (4).
	afplist:=prep1(clist,a,primelist);
	alphgamlist:=[* *];
	for pr in afplist do
		af:=pr[1];
		fplist:=pr[2];
		tf,alpha,gammalist,matA,rr:=principalize(af,fplist);
		if tf then
			assert #gammalist eq #fplist;
			alphgamlist:=alphgamlist cat [* [* alpha, gammalist, matA, rr   *] *];
		end if;
	end for;
	return alphgamlist;
end function;

/*
// This example is taken from New6PirlTMlog.txt.
clist:=[7,1,29,-25];
primelist:=[2,3,7,37,53];
a:=1;
afplist:=prep1(clist,a,primelist);
print #afplist;
alphgamlist:=prep2(clist,a,primelist);
print #alphgamlist; // This is the number of possibilities for the S-unit equation.

print "++++++++++++++++++++++++++++++++++++++++++";

// This example is taken from New5PirlTMlog.txt.
clist:=[ 14, 20, 24, 15 ]; 
primelist:=[ 2, 3, 17, 37, 53 ]; 
a:=1;
afplist:=prep1(clist,a,primelist);
print #afplist;
alphgamlist:=prep2(clist,a,primelist);
print #alphgamlist; // This is the number of possibilities for the S-unit equation.
*/


reduce:=function(delta,modaf,af);
	// Input: delta, modaf, af
	// Here delta is a non-zero element of K,
	// af is an ideal of OK, and pi is the residue class map
	// modaf : OK --> OK/af.
	// We require that
	// the denominator ideal of delta to be coprime
	// to af (otherwise we'll get an error).
	// Return: the image of delta in OK/af. 
	K:=Universe([delta] cat Basis(af));
	OK:=MaximalOrder(K);
	if delta in OK then
		return modaf(delta);
	end if;
	facts:=Factorisation(delta*OK);
	ppow:=&*[fact[1]^(-fact[2]) : fact in facts | fact[2] lt 0];
	assert ppow+af eq 1*OK;
	beta:=CRT(af,ppow,OK!1,OK!0);
	assert beta in OK;
	alpha:=OK!(delta*beta);
	return modaf(alpha)/modaf(beta);
end function;




DirichletSieve:=function(c0, theta, tau, deltaList : qBound:=1500, smoothBound:=40); 
	// To apply the Dirichlet sieve to the equation
	// c_0 X- Y \theta=\tau \cdot \delta_1^{m_1} \cdots \delta_r^{m_r}.
	// Input: c0, theta, tau, deltaList.
	// Output: WW, LL
	// where LL is a sublattice of Z^r of finite index,
	// and WW is a finite subset of Z^r,
	// such that all the solutions (m_1,..,m_r) are
	// contained in WW+LL.
	// There are optional parameters qBound, and smoothBound.
	// The sieve makes use of all primes q up to qBound
	// such that \# \mathcal{B}_q is supported by primes < smoothBound.
	// The default values are respectively 1500 and 40.	
	K:=NumberField(Universe([theta,tau] cat deltaList));
	assert K.1 eq theta;
	OK:=MaximalOrder(K);
	supp:=&join[Support(delta*OK) : delta in deltaList];
	supp:=supp join {fact[1] : fact in Factorisation(tau*OK)};
	// supp is the supports of tau and the delta_i.
	rk:=#deltaList;
	print "Rank=", rk;
	Zrk:=FreeAbelianGroup(rk);
	L:=Zrk;
	W:=[L!0]; 
	qlist:=PrimesInInterval(1,qBound);
	orderBq:=func<q | &*[Norm(fact[1])-1 : fact in Factorisation(q*OK)] div (q-1) >; // Given q, this gives the order of \mathcal{B}_q.
	PBq:=func<q | Max([1] cat PrimeDivisors(orderBq(q)))>; // And this
	// gives the largest prime dividing the order of \mathcal{B}_q.
	sort1:=func<q1,q2 | orderBq(q1)-orderBq(q2)>;
	sort2:=func<q1,q2 | PBq(q1)-PBq(q2)>;
	Sort(~qlist,sort1);
	Sort(~qlist,sort2); 	
	primeCount:=0;
	for q in qlist do
                print q;
		qfacts:=[fq[1] : fq in Factorisation(q*OK)];
		if #(Set(qfacts) meet supp) eq 0 and PBq(q) lt smoothBound then  
			primeCount:=primeCount+1;
			OModq,modq:=quo<OK | q*OK>;	
			Aq,eta:=UnitGroup(OModq);
			primElt:=Integers()!(PrimitiveElement(GF(q)));
			Bq,toBq:=quo<Aq | sub<Aq | (modq(OK!primElt))@@eta> >;
			// This is \mathcal{B}_q.
			imsDelta:=[ toBq((reduce(delta,modq,q*OK))@@eta) : delta in deltaList];
			phiq:=hom<Zrk->Bq | imsDelta>; 
			// \phi_q : Z^r \rightarrow \mathcal{B}_q.
			phiqL:=hom<L->Bq | [phiq(l) : l in OrderedGenerators(L)]>;
			imZr:=Image(phiq);
			imL:=Image(phiqL);
			imWL:=sub<Bq | [phiq(w) : w in W] cat [phiq(l) : l in OrderedGenerators(L)]>;	// The subgroup inside \mathcal{B}_q generated by the images
			// of W and L under \phi_q.
			imtau:=toBq((reduce(tau,modq,q*OK))@@eta);
			Rq:=[(c0*u-theta) : u in [0..(q-1)]] cat [c0];
			Rqstar:=[ rho : rho in Rq | &and [Valuation(rho*OK,fq) eq 0 : fq in qfacts ]];	// R_q \cap \OO_q^\times.
			Sq:=[toBq((modq(rho))@@eta)-imtau : rho in Rqstar];
			Tq:=[ rho : rho in Sq | rho in imWL ]; 
			Lnew:=Kernel(phiq) meet L;
			Lnew:=sub<Zrk | [Zrk!l : l in OrderedGenerators(Lnew)]>; 
			Q,modLnew:=quo<L|Lnew>;
			if #Q lt #Tq then
				// We will form the list Qreps consists of pairs, where the first element runs
				// through coset representatives for L/Lnew, and the
				// second is the corresponding image under psi.
				//
				// First we want to compute a set coset representatives 
				// for L/Lnew.
				// [Zrk!(q@@pi) : q in Q] is way too slow. 
				// Instead we work with generators of the quotient.
				invs:=Invariants(Q);
				preQ:=[(Q.i)@@modLnew : i in [1..#invs]]; //Subset of L generating  
													// L/Lnew.
				Qreps:=[* [* Zrk!0, Bq!0 *] *]; 
				for j in [1..#invs] do
					qj:=preQ[j];
					qjphi:=phiq(qj);
					ordj:=invs[j];
					Qreps:=[* [* q[1]+x*qj, q[2]+x*qjphi *] : q in Qreps, x in [0..(ordj-1)] *];
				end for; // Finished computing Qreps.
				Wreps:=[* [* w, phiq(w) *] : w in W *];
				Wnew:=[Zrk!(w[1]+q[1]) : w in Wreps, q in Qreps | w[2]+q[2] in Tq];
			else
				Wnew:=[]; // I think this is the part that makes it slow
				for w in W do
					wphi:=phiq(w);
					Tqshift:=[j-wphi : j in Tq];
					Tqshift:=[j : j in Tqshift | j in imL];
					Wnew:=Wnew cat [Zrk!(w+j@@phiqL) : j in Tqshift];		
				end for;
			end if;
			W:=Wnew;
			L:=Lnew;
			if #Wnew eq 0 then
				print "succeeded in eliminating a possibility";
				ZZrk:=StandardLattice(rk);
				WW:=[ZZrk!(Eltseq(Zrk!(w))) : w in W];
				LL:=sub<ZZrk | [ ZZrk!(Eltseq((Zrk!l))) : l in OrderedGenerators(L)]>;
				return WW, LL; // changed from return
			end if; 
			G:=GCD([GCD(Eltseq(Zrk!g)) : g in OrderedGenerators(L)]);
			print "After", primeCount, "primes q";
			print "#W=", #W, "G=", G, "#Z^r/L=", Index(Zrk,L), "Density=", #W/Index(Zrk,L)+0.0;
		end if;	
	end for;
        			
	ZZrk:=StandardLattice(rk);
	WW:=[ZZrk!(Eltseq(Zrk!(w))) : w in W];
	LL:=sub<ZZrk | [ ZZrk!(Eltseq((Zrk!l))) : l in Generators(L)] >;
	return WW,LL;
	/*
	WWnew:=[ZZrk | ];
	WWbad:=[ZZrk | ];
	for ww in WW do
		vv:=ClosestVectors(LL,-ww)[1];
		wwnew:=ww+vv;
		if Max([AbsoluteValue(a) : a in Eltseq(wwnew)]) lt 100 then
			Append(~WWnew,wwnew);
		else
			Append(~WWbad,wwnew);
		end if;
	end for;
	if #WWnew eq 0 then
		return WW, LL;
	end if;
	for ww in WWbad do
		Q,modLL:=quo<ZZrk | LL>;
		profDist:=func<ww1, ww2 | Order(modLL(ww-ww1))-Order(modLL(ww-ww2))>;
		Sort(~WWnew,profDist);
		print "losing index", Order(modLL(ww-WWnew[1]));
		LL:=sub<ZZrk | Basis(LL) cat [ww-WWnew[1]]	>;
	end for;
	print #WWnew, Index(ZZrk,LL);
	return WWnew, LL;
	*/
end function;
	

solveThueMahler:=function(clist,a,primelist,bound);
	// Input: clist, a, primelist, bound
	// clist is a list of coefficients c_0,c_1,..,c_n.
	// a is an integer.
	// primelist is a list of the primes p_1,p_2,..,p_v.
	// This solves c_0 X^n+...+c_n Y^n= a \times p_1^{z_1} ... p_t^{z_t}
	// subject to the assumptions that X, Y are coprime integers
	// and gcd(Y,c_0)=1, under the assumption that the vector
	// of exponents (m_1,..,m_r) (see below) has length \le bound.
	// Output: sols, biglist.
	// sols is a list of solutions to the Thue--Mahler equation.
	// biglist is a list of ninetuples
	// [* tau,deltaList, alpha,gammaList, matA, rr, WW, WWshort, LL *].
	// Here alpha, gammaList, matA, rr are as in the output of prep2.
	// For each choice of alpha, gammaList, we obtain one or more
	// equations of the form
	// (*) c_0 X-Y\theta= \tau \cdot \delta_1^{m_1} \cdots \delta_r^{m_r}.  
	// So tau and deltalist are as in here. 
	// LL is a lattice of full rank in \Z^r, and WW is a finite subset of
	// \Z^r such that the solutions (m_1,..,m_r) to (*) are contained
	// in WW+LL. 
	// WWshort is the list of vectors as in Lemma 1.2 which will contain
	// the solutions for (*) provided \lambda_1(LL)>2*bound. If the inequality
	// is not satisfied then an error message is given. In that case the
	// the qBound in the DirichletSieve command should be increased.
	n:=#clist-1;
	ZUV<U,V>:=PolynomialRing(Integers(),2);
	F:=&+[clist[i+1]*U^(n-i)*V^i : i in [0..n]];
	c0:=clist[1];
	//alphgamlist:=prep2(clist,a,primelist);
	K:=Universe([quad`alpha : quad in alphgamlist]);
	K:=NumberField(K);
	theta:=K.1;
	OK:=MaximalOrder(K);
	assert Degree(K) eq (#clist-1);
	UG,om:=UnitGroup(OK);
	rnk:=#Generators(UG)-1;
	rtun:=UG.1;
	fu:=[om(UG.i) : i in [2..(rnk+1)]];
	r:=Order(rtun) div 2;
	assert om(UG.1)^r eq OK!(-1);
	rtun:=[om(UG.1)^i : i in [0..(r-1)]];
	bigList:=[* *];
	sols:={};
	eqncount:=0;
	for quad in alphgamlist do
		for zet in rtun do
			eqncount:=eqncount+1;
			alpha:=quad`alpha;
			gammaList:=quad`gammalist;
			matA:=quad`matA;
			r:=quad`vecR;
			tau:=alpha*zet;
			deltaList:=fu cat gammaList;
			print "Applying the Dirichlet sieve to equation number", eqncount;
			WW,LL:=DirichletSieve(c0, theta, tau, deltaList);
			print "Finished applying the Dirichlet sieve to equation number", eqncount;
			print "+++++++++++++++++++++++++++++++++++++";
			if #WW ne 0 then
				if Norm(ShortestVectors(LL)[1]) lt 4*bound^2 then
					print "Error! Need to increase qBound in the Dirichlet sieve";
					assert 1 eq 0;
				end if;
				WWshort:=[ww+ClosestVectors(LL,-ww)[1] : ww in WW];
				WWshort:=[ww : ww in WWshort | Norm(ww) lt bound^2];
				for ww in WWshort do
					lincom:=tau*&*[deltaList[i]^ww[i] : i in [1..#deltaList]];
					lincom:=Eltseq(K!lincom);
					if &and[ lincom[i] eq 0 : i in [3..Degree(K)]] and lincom[1] in Integers() and lincom[2] in Integers() then
						lincom:=[Integers()!lincom[1],Integers()!lincom[2]];
						if IsDivisibleBy(lincom[1],c0) then
							sol:=[lincom[1] div c0, -lincom[2]];
							Fsol:=Evaluate(F,sol);		
							if IsDivisibleBy(Fsol,a) then
								Fsol:=Fsol div a;
								mlist:=[];
								for p in primelist do
									m:=Valuation(Fsol,p);
									Append(~mlist,m);	
									Fsol:=Fsol div p^m;
								end for;
								if Fsol eq 1 then
									if IsEven(n) then
										sols:=sols join { sol cat  mlist , [-sol[1],-sol[2]]cat mlist };
									else
										sols:=sols join {  sol cat mlist };
									end if;
								elif Fsol eq -1 then
									if IsOdd(n) then
										sols:=sols join { [-sol[1],-sol[2]] cat  mlist };
									end if;
								end if;
							end if;
						end if;
					end if;
				end for;
				Append(~bigList, [* tau, deltaList , alpha, gammaList, matA, r,  WW, WWshort, LL *]);
			end if;
		end for;
	end for;
	return sols, bigList;
end function;

// This example is taken from New6PirlTMlog.txt.
//clist:=[7,1,29,-25];
//primelist:=[2,3,7,37,53];
//a:=1;
//solveThueMahler(clist,a,primelist);

// This example is taken from New5PirlTMlog.txt.
//clist:=[ 14, 20, 24, 15 ]; 
//primelist:=[ 2, 3, 17, 37, 53 ]; 
//a:=1;

// Example from Adela:

//clist:=[ 2, 1, 8, 3 ]; 
//primelist:=[ 2, 3, 173 ]; 
//a:=1;
//sols,biglist:=solveThueMahler(clist,a,primelist);


// Example from Adela:

clist:=[ 3, 2, 7, 2 ]; 
primelist:=[ 2, 3, 7, 41 ];
a:= 1;
bound:=10^15;
//time sols, biglist:=solveThueMahler(clist,a,primelist,bound);

// Example from Adela

clist:=[ 2, 1, 8, 3 ]; 
primelist:=[ 2, 3, 173 ]; 
a:=1;
bound:=10^15;
//time sols, biglist:=solveThueMahler(clist,a,primelist,bound);

// Example from Adela

clist:= [ 1, 5, -8, -2 ];
primelist:=[ 2, 5, 13, 23 ]; 
a:=1;
bound:=10^15;
time sols, biglist:=solveThueMahler(clist,a,primelist,bound);

