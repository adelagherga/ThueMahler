

// Problem: given ideal fa in OK
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



	
reduce:=function(delta,modaf,af);
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


multQuo:=function(fp,a,b,alphaList);
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
			beta:=(modfpb(alpha)/&*[ modfpb(D2gens[j])^coords[j]  : j in [1..#coords]  ])@@modfpb;
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

multGroupPrimePower:=function(fp,k,alphaList);
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

multGroup := function(fb,alphaList);
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
/*
Qx<x>:=PolynomialRing(Rationals());
f:=x^6-x-1;
K<theta>:=NumberField(f);
OK:=MaximalOrder(K);
fp1:=Factorisation(5*OK)[1,1];
fp2:=Factorisation(5*OK)[2,1];
fp3:=2*OK;
fb:=fp1^350*fp2^550*fp3^250;
alphaList:=[theta,theta-1,theta+3,7,theta^30,(theta^2-theta)/7,theta/(theta+3),1];
time D,l:=multGroup(fb, alphaList);
assert l[8] eq D!0;
assert l[5] eq 30*l[1];       
assert l[6] eq l[1]+l[2]-l[4];
assert l[7] eq l[1]-l[3];

// Compare times with the inbuilt Magma implementation:
time R,phi:=quo<OK | fb>;
time U,psi:=UnitGroup(R);
assert IsIsomorphic(D,U);
// WARNING: the next one will take forever!
time lU:=[ (phi(alpha))@@psi : alpha in [theta,theta-1,theta+3,7,theta^30,1]];
*/
