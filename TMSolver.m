// To Do: 
// 1. precision for real/padic case
// 2. timing names
// learning emacs








// GESolver.m

//============================================================================//
//============================================================================//
/* 
This code computes integer solutions of the Goormaghtigh Equation
                    (x^m-1)/(x-1) = (y^n-1)/(y-1)
for y > x > 1 and m > n > 2, for fixed n. In particular, fixing x,n yields a 
Thue-Mahler equation of the form
                    (x-1)y^(n-1) + ... + (x-1)y + x = x^m.
This algorithm computes solution (y,m) of this equation, and is based on the 
Thue-Mahler algorithm of Tzanakis-de Weger, as well as its updated version by 
A. Gherga, R. von Känel, B. Matschke, and S. Siksek. 

Authors: Michael A. Bennett, Adela Gherga, Dijana Kreso
Last Update: Aug. 17, 2018

Details of this code can be found in the authors' paper
"An old and new approach to Goormaghtigh's Equation."

//============================================================================//

Remarks:
    This current implementation primarily supports Goormaghtigh equations with 
    n = 5. Note that as listed in the authors' aforementioned paper, this 
    algorithm is only needed for x in [2,719].

Bottlenecks of this current implementation:
    - computing the class group
    - computing the ring of integers of the splitting field of the TM equation
    - computing the unit group
        
//============================================================================//

INPUT:

OUTPUT:

EXAMPLE:

*/
//============================================================================//
//============================================================================//

// To reduce F(X,Y)=a p1^z1 \cdots pv^zv
// to S-unit equations.
// Here F is irreducible hgs with coefficients in \Z
// of degree \ge 3
// a an integer coprime to the p_i
// X,Y are coprime
// and Y is coprime to c0 which the leading coefficients of F. 

// Let x := c0 X, y:=Y.
// Then we still have gcd(x,y)=1.


// TO BE FIXED
monic:= function(clist,primelist,a);
    assert &and[IsPrime(p) : p in primelist];
    assert &and[c in Integers() : c in clist];
    c0:=Integers()!clist[1];
    assert c0 ne 0;
    n:=#clist-1;
    assert n ge 3;
    assert a ne 0;
    QUV<U,V>:=PolynomialRing(Rationals(),2);
    F:=&+[clist[i+1]*U^(n-i)*V^i : i in [0..n]];
    assert IsHomogeneous(F);
    
    fac_a:= [q[1] : q in Factorization(a)];
    if IsEmpty(fac_a) then
        Prod1:= [1];
    else
        si:= [[0..Min(Valuation(a,fac_a[i]),Valuation(c0,fac_a[i]))] : i in [1..#fac_a]];
        Prod1:= [];
        ExponentCombos1:= CartesianProduct(si);
        for c in ExponentCombos1 do
            Append(~Prod1, &*{fac_a[i]^c[i] : i in [1..#fac_a]});
        end for;
    end if;
    
    ti:= [[0..Valuation(c0,primelist[i])] : i in [1..#primelist]];
    assert IsEmpty(ti) eq false;
    Prod2:=[];
    ExponentCombos2:= CartesianProduct(ti);
    for c in ExponentCombos2 do
        Append(~Prod2, &*{primelist[i]^c[i] : i in [1..#primelist]});
    end for;
    assert IsEmpty(Prod2) eq false;
    
    D:=[];
    for c in Prod1, d in Prod2 do
        if c*d notin D then
            Append(~D, c*d);
        end if;
    end for;
    Sort(~D);
    alist:= [];
    duc:= [];
    
    Qx<x>:= PolynomialRing(Rationals());
    fclist:= Reverse([1] cat [clist[i+1]*c0^(i-1) : i in [1..n]]);
    for d in D do
        u:= (c0^(n-1))/d^n;
        c:= Sign(u*a)*u*a/&*[p^Valuation(u*a, p) : p in primelist];
        assert &and[Valuation(c,p) eq 0 : p in primelist];
        assert c in Integers();
        f0:= u*Evaluate(F,[d*U/c0, V*d]);
        f:= Evaluate(f0,[x,1]);
        assert IsMonic(f);
        assert Degree(f) eq n;
        assert IsIrreducible(f);
        assert &and[ci in Integers() : ci in Coefficients(f)];
        assert Coefficients(f) eq fclist;
        if c notin alist then
            Append(~alist, c); 
        end if;
        Append(~duc, [d,u,c]);
    end for;
    
    nD:=[];
    for i in [1..#alist] do
        c:= alist[i];
        nD[i]:= [* Integers()!c *];
        nD[i][2]:=[];
        for j in [1..#duc] do
            if c eq duc[j][3] then
                Append(~nD[i][2], [duc[j][1],duc[j][2]]);
            end if;
        end for;
    end for;
    alist:= nD;
    
    
    return alist;
end function;

algs1and2:=function(fieldKinfo,c0,p);
	// This is an implementation of Algorithms
	// 1 and 2 in the paper, plus the refinements explained
	// in the remarks.
	// Input: c0, th (=\theta), p.
	// Returns Lp, Mp.
	
        K:=fieldKinfo`field;
        th:= K.1;
        OK:=fieldKinfo`ringofintegers;
        f:= fieldKinfo`minpoly;
        fprs:=Factorisation(p*OK);
	fprs:=[fact[1] : fact in fprs]; // the prime ideals above p.
	
	v:=Valuation(Discriminant(f),p);
	prec:=10*(v+1);
	Zp:=pAdicRing(p,prec);
	rts:=Roots(f,Zp);	
	rts:=[Integers()!r[1] : r in rts];
	Lp:=[];
	Mp:=[];
	// Algorithm 1.
	t:=Valuation(c0,p)+1;
	ulist:=[c0*w : w in [0..(p-1)]];
        
	while #ulist ne 0 do
        
            ulistNew:=[];
            for u in ulist do
                cPu:=[i : i in [1..#fprs] | Valuation((u-th)*OK,fprs[i]) ge t*RamificationDegree(fprs[i])];
                fbu:= [ Min([Valuation((u-th)*OK,fprs[i]),t*RamificationDegree(fprs[i])]) : i in [1..#fprs]]; 
                assert &*[fprs[i]^fbu[i] : i in [1..#fprs]] eq p^t*OK+(u-th)*OK;
                k:= #fprs + 1;
                if #cPu eq 0 then
                    if [[k],fbu] notin Lp then
                        Append(~Lp, [[k],fbu]);
                    end if;
                elif #cPu eq 1 then
                    fp:=fprs[cPu[1]];
                    efp:=RamificationDegree(fp)*InertiaDegree(fp);
                    rtcount:=#[alpha : alpha in rts | Valuation(u-alpha,p) ge t];
                    if efp eq 1 and rtcount ge 1 then
                        if [[cPu[1]],fbu] notin Mp then
                            Append(~Mp, [[cPu[1]],fbu]); 
                        end if;
                    else
                        ulistNew:=ulist cat [ u+p^(t)*w : w in [0..(p-1)]];
                    end if;
                else
                    ulistNew:=ulist cat [ u+p^(t)*w : w in [0..(p-1)]];
                end if;
            end for;		
            ulist:=ulistNew;
            t:=t+1;
	end while;      // End of Algorithm 1.
	// Algorithm 2.
	if Valuation(c0,p) eq 0 then  
            ulist:=[p*w : w in [0..(p-1)]];
            t:=2;
            while #ulist ne 0 do
                ulistNew:=[];
                for u in ulist do
                    cPu:=[i : i in [1..#fprs] | Valuation(c0-u*th,fprs[i]) ge t*RamificationDegree(fprs[i])];
                    fbu:= [ Min([Valuation(c0-u*th,fprs[i]), t*RamificationDegree(fprs[i])]) : i in [1..#fprs]]; 
                    assert &*[fprs[i]^fbu[i] : i in [1..#fprs]] eq (c0-u*th)*OK+p^t*OK;
                    k:= #fprs + 1;
                    if #cPu eq 0 then
                        if [[k],fbu] notin Lp then
                            Append(~Lp, [[k],fbu]);
                        end if;
                    else 
                        ulistNew:=ulistNew cat [u+p^(t+1)*w : w in [0..(p-1)]];
                    end if; 
                end for;	
                ulist:=ulistNew;
                t:=t+1;
		
            end while;
	end if; // End of Algorithm 2.
	// Now for the refinements.
	
        keep:= [];
        for pr in Mp do
            fbd:=&*[fprs[i]^pr[2][i] : i in [1..#fprs]];
            fp:=fprs[pr[1][1]];
            for i in [1..#Lp] do
                br:= Lp[i];
                fb:=&*[fprs[i]^br[2][i] : i in [1..#fprs]];
                if (IsIntegral(fb/fbd) eq false) or (fb/fbd ne fp^Valuation(fb/fbd,fp)) then
                    Append(~keep, i);
                end if;
            end for;
            Lp:= [Lp[k] : k in keep];
        end for;
        
//// SOMETHING FUCKED IS HAPPENING HERE; CHECK        
//clist:= [1,2,17,2];
//primelist:= [7,41]; 
//a:= 1;
// AT P = 7// NB. SAMIR'S CODE FOR THIS HAS CHANGED....
        repeat
            removal:=[];
            for pr1,pr2 in Mp do
                if pr1 ne pr2 then
                    if pr1[1] eq pr2[1] then
                        fp:=fprs[pr1[1][1]];
                        fb1:=&*[fprs[i]^pr1[2][i] : i in [1..#fprs]];
                        fb2:=&*[fprs[i]^pr2[2][i] : i in [1..#fprs]];
                        Valuation(fb1/fb2);
                        
                        if (IsIntegral(fb1/fb2)) and (fb1/fb2 eq fp^Valuation(fb1/fb2)) then
                            Append(~removal, pr1); 
                        end if;
                    end if;
                end if;
                if #removal ge 1 then
                    Exclude(~Mp,removal[1]);
                end if;	
            end for;
	until #removal eq 0;
        
        //Now for the more refinements a la Kyle

   /*
        Removes those cases where everything between the cases is the same except the exponent on the unbounded part
        
        
        MpCopy:= Mp;
        for pr1 in MpCopy do
            k:= pr1[1][1];
            removal:= -1;
            for i in [1..#Mp] do
                pr2:= Mp[i];
                if pr2[1][1] eq k then
                    if [pr1[2][j] :  j in [1..k-1] cat [k+1..#fprs]] eq [pr2[2][j] :  j in [1..k-1] cat [k+1..#fprs]] then
                        if pr1[2][k] gt pr2[2][k] then
                            removal:= i;
                            break i;
                        end if;
                    end if;
                end if;
            end for;
            if removal ne -1 then
                Remove(~Mp, removal);
            end if;
        end for; */
                
                    // Set aaa[k]=0 for each [[k],aaa] in Mp
        for i in [1..#Mp] do
            pr1:= Mp[i];
            k:= pr1[1][1];
            Mp[i][2][k]:= 0;
        end for;
                
         // More refinements
        LpCopy:= Lp;
        for pr2 in LpCopy do
            for i in [1..#Mp] do
                pr1:= Mp[i];
                k:= pr1[1][1];
                
                    if &and[pr2[2][j] le pr1[2][j] : j in [1..k-1] cat [k+1..#fprs]] then
                        npr:= [[k],pr2[2]];
                        npr[2][k]:= 0;
                        if npr notin Mp then
                            Append(~Mp, npr);
                        end if;
                        Exclude(~Lp, pr2);
                        break i;
                //    end if;
                end if;
            end for;
        end for;
                
                
        ////////////////////////////////////////////
        
        
	//Now for the more refinements.
//	if IsDivisibleBy(c0,p) then     // c0 will always be set to 1; so this never happens
//		Lp:={fb : fb in Lp | Valuation(Norm(fb),p) ge (n-1)*Valuation(c0,p)};
//	end if;	
//	MpNew:={};
//	for pr in Mp do
//		fb:=pr[1];
//		fp:=pr[2];
//		if Valuation(Norm(fb),p) lt (n-1)*Valuation(c0,p) then
//			fbd:=fb*fp^((n-1)*Valuation(c0,p)-Valuation(Norm(fb),p));
//			MpNew:=MpNew join {<fbd,fp>};
//		else
//			MpNew:=MpNew join {pr};
//		end if;
//	end for;
//	Mp:=MpNew;
	return Lp,Mp,fprs;
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


prep1:=function(clist,primelist,a);
	// clist is a list of coefficients c_0,c_1,..,c_n.
	// a is an integer.
	// primelist is a list of the primes p_1,p_2,..,p_v.
	// This returns a list of pairs [* fa, fplist *] 
	// where fa is an ideal and fplist is a list of prime ideals fp_1,..,fp_v
	// so that (c_0 X - th Y)O_K =fa*fp_1^{n_1}*..*fp_u^{n_u} (as in equation (3)).
	assert &and[IsPrime(p) : p in primelist];
        assert &and[c in Integers() : c in clist];
        c0:=Integers()!clist[1];
        assert c0 ne 0;
        n:=#clist-1;
        assert n ge 3;
        assert a ne 0;
        QUV<U,V>:=PolynomialRing(Rationals(),2);
        F:=&+[clist[i+1]*U^(n-i)*V^i : i in [0..n]];
        assert IsHomogeneous(F);
        Qx<x>:=PolynomialRing(Rationals());
        alist:= monic(clist, primelist, a);
        fclist:= [1] cat [clist[i+1]*c0^(i-1) : i in [1..n]];
        
        f:=&+[fclist[i+1]*x^(n-i) : i in [0..n]];
        c0:= Integers()!fclist[1];
        assert c0 eq 1;
        assert IsMonic(f);
        assert Coefficients(f) eq Reverse(Coefficients(clist[1]^(n-1)*Evaluate(F,[U/clist[1],1])));
	assert Degree(f) eq n;
	assert IsIrreducible(f);
	assert &and[c in Integers() : c in Coefficients(f)];
	K<th>:=NumberField(f);
	OK:=MaximalOrder(K);
	th:=OK!th;
        // generate a record to store relevant field info
        FieldInfo:= recformat<field,gen,ringofintegers,minpoly,zeta,fundamentalunits>;
        fieldKinfo:= rec<FieldInfo | field:= K,gen:= th,ringofintegers:= OK,minpoly:= f>;
        
	afplist:=[* [* 1*OK, [] *] *];
	for p in primelist do
            afplistNew:=[* *];
            Lp,Mp,fprs:=algs1and2(fieldKinfo,c0,p);
                afplistNew1:=[* [* pr[1]*&*[fprs[i]^fb[2][i] : i in [1..#fprs]], pr[2] *] : fb in Lp, pr in afplist  *];
		afplistNew2:=[* [* pr[1]*&*[fprs[i]^qr[2][i] : i in [1..#fprs]], pr[2] cat fprs[qr[1]] *] : qr in Mp, pr in afplist  *];
		afplist:=afplistNew1 cat afplistNew2;
	end for;
        
        afplistNew:=[* *];
        for al in alist do
            R:=Integers()!(al[1]);
            for pr in afplist do
                af:=pr[1];
                assert GCD(Norm(af),R) eq 1;
                assert &and[Valuation(R,p) eq 0 : p in primelist];
                invs:=normInv(R,OK);
                afplistNew:=afplistNew cat [* [* af*I, pr[2] *] : I in invs  *];
            end for;
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
            assert &and[IsDivisibleBy(Naf,newa[1]) : newa in alist];
            assert &and[Set(PrimeDivisors(Naf div newa[1])) subset Set(primelist) : newa in alist];
	end for;
	return alist, afplist, fieldKinfo; 
end function;
                


principalize:=function(fieldKinfo,ClK,fa,fplist);
    /*
    INPUT:
        fa:= an ideal in OK such that
            fa * fp_1^{n_1} * ... * fp_u^{n_u} = principal ideal
        fplist:= a list of prime ideals
        
    OUTPUT:
        tf, alpha, gammalist, matA, rr.
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
    
    REMARKS:
        // I shouldn't start with this since this isn't the first thing we do...
    
    REFERENCE:
    EXAMPLE:
    alpha here has norm (x-1)^3 p_1^{t_1+r_1} \cdots p_v^{t_v+r_v}
    */
    K:=fieldKinfo`field;
    OK:=fieldKinfo`ringofintegers;
    
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
    phi := hom< Zu -> ClK`classgroup | [ fp@@ClK`map : fp in fplist ]>;
    img:=Image(phi);
    if -fa@@ClK`map in img then
        rr:=(-fa@@ClK`map)@@phi;
        rr:=Eltseq(Zu!rr);
    // updates rr to have only positive entries so as to avoid precision errors
        for i in [1..#rr] do        
            while rr[i] lt 0 do
                rr[i]:= rr[i]+ClK`classnumber;
            end while;
        end for;
        ker:=Kernel(phi);
        A:=[Eltseq(Zu!a) : a in Generators(ker)];       // A is a list of vectors for now 
        assert #A eq u; // hence the kernel has rank u
        matA:=Transpose(Matrix(A));     // the matrix A as denoted in the Reference
        assert AbsoluteValue(Determinant(matA)) eq #img;		
        fa2:=fa*&*[fplist[i]^rr[i] : i in [1..u]];
        tf,alpha:=IsPrincipal(fa2);
        assert tf;      // the principal ideal with generator alpha
    // computes the ideals as denoted by \mathfrak{c} in the Reference
        clist:=[ &*[fplist[i]^a[i] : i in [1..u] ]  : a in A ];
        gammalist:=[];
        for fc in clist do
            tf, gamma:=IsPrincipal(fc);
            assert tf;
            Append(~gammalist,gamma);
        end for;
        tf, matAinv:= IsInvertible(matA);
        assert tf;
        return true, alpha, gammalist, matA, rr;
    else	
        return false, 0, 0, 0, 0;
    end if; 
end function;


prep2:=function(fieldKinfo,ClK,afplist,primelist);
    /*
    INPUT:
        fa:= an ideal in OK such that
            fa * fp_1^{n_1} * ... * fp_u^{n_u} = principal ideal
        fplist:= a list of prime ideals
        
    OUTPUT:
        tf, alpha, gammalist, matA, rr.
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
    
    REMARKS:
        // I shouldn't start with this since this isn't the first thing we do...
    
    
    EXAMPLE:
    
    // clist is a list of coefficients c_0,c_1,..,c_n.
    // a is an integer.
    // primelist is a list of the primes p_1,p_2,..,p_v.
    // This returns a list of the possible quadruples [* alpha, gammalist, matA, r *] 
    // where alpha in K^*, and gammalist is a list gamma_1,...,gamma_u 
    // so that (c_0 X - th Y)OK =alpha*gamma_1^{m_1}*..*gamma_u^{m_u} (as in equation (4)).
    // matA and rr are the matrix A and the vector rr, so that 
    // nn = mm A + rr, where nn is the vector of exponents in (3)
    // and mm is the vector of exponents in (4).
    */
    
    K:= fieldKinfo`field;
    OK:=fieldKinfo`ringofintegers;
  
    // generate a record to store relevant case info
    CaseInfo:= recformat< alpha,gammalist,matA,vecR,ideallist,bound >; 
    
    alphgamlist:=[ ];
    v:= #primelist;
    for pr in afplist do
        af:=pr[1]; 
        fplist:=pr[2];
        tf,alpha,gammalist,matA,rr:=principalize(fieldKinfo,ClK,af,fplist);
	if tf then
            assert #gammalist eq #fplist;
            nu:= #fplist;
            Nm:= [Norm(fp) : fp in fplist];
            assert #Nm eq nu;
            assert &and[IsPrime(fp) : fp in Nm];
            rtest:= [];
            for i in [1..#primelist] do
                p:= primelist[i];
                if p in Nm then
                    ind:= Index(Nm, p);
                    rtest[i]:= rr[ind];
                else
                    rtest[i]:= 0;
                end if;
            end for;
            tt:= [Valuation(Norm(af), primelist[i]) : i in [1..v]];
            zz:= [Valuation(Norm(ideal<OK|alpha>), primelist[i]) : i in [1..v]];
    // sanity checks on the exponents of alpha, the ideal af, and gammas
            assert [tt[i] + rtest[i] : i in [1..v]] eq zz;
            for i in [1..nu] do
                gamma:= gammalist[i];
                aa:= [Valuation(Norm(ideal<OK|gamma>), Nm[j]) : j in [1..nu]];
                assert aa eq Eltseq(ColumnSubmatrixRange(matA,i,i));
            end for;
            
            Append(~alphgamlist, rec<CaseInfo | alpha:=alpha,gammalist:=gammalist,matA:=matA,vecR:=rr,ideallist:=fplist>);
        end if;
    end for;
    return alphgamlist;
end function;

ijkAutL:= function(fieldLinfo)
    L:= fieldLinfo`field;
    tl:= fieldLinfo`gen;
    G,Aut,tau:= AutomorphismGroup(L);
    assert IsIsomorphic(G, Sym(3)) or IsIsomorphic(G, Alt(3));

    ijk:= [];
    if Order(G.1) eq 3 then
        assert G.1^3 eq Id(G);
        if (tau(G.1))(tl[1]) eq tl[2] then
            ijk[1]:= tau(G.1);
            ijk[2]:= tau(G.1^2);
        else
            ijk[1]:= tau(G.1^2);
            ijk[2]:= tau(G.1);
        end if;
        ijk[3]:= tau(G.1^3);    // identity map
    elif Order(G.2) eq 3 then
        assert G.2^3 eq Id(G);
        if (tau(G.2))(tl[1]) eq tl[2] then
            ijk[1]:= tau(G.2);
            ijk[2]:= tau(G.2^2);
        else
            ijk[1]:= tau(G.2^2);
            ijk[2]:= tau(G.2);
        end if;
        ijk[3]:= tau(G.2^3);
    end if;
    
    AutL:= [];
    for x in G do
        Append(~AutL, tau(x));
    end for;
    
    // verify that i,j,k permutes the roots tl
    assert (ijk[1](tl[1]) eq tl[2]) and (ijk[2](tl[1]) eq tl[3]) and (ijk[3](tl[1]) eq tl[1]);
    assert (ijk[1](tl[2]) eq tl[3]) and (ijk[2](tl[2]) eq tl[1]) and (ijk[3](tl[2]) eq tl[2]);
    assert (ijk[1](tl[3]) eq tl[1]) and (ijk[2](tl[3]) eq tl[2]) and (ijk[3](tl[3]) eq tl[3]);
    
    return ijk, AutL;
end function;


UpperBounds:=procedure(fieldKinfo,clist,primelist,a,~alphgamlist,ComplexPrec);
    /*
    */
    assert &and[IsPrime(p) : p in primelist];
    assert &and[c in Integers() : c in clist];
    assert a in Integers();
    c0:=Integers()!clist[1];
    assert c0 ne 0;
    n:=#clist-1;
    assert n ge 3;
    assert a ne 0;
    Q<X>:=PolynomialRing(Rationals());
    F:=&+[clist[i+1]*X^(n-i) : i in [0..n]];
    
    DiscF:= Discriminant(F);
    NS:= &*[p : p in primelist];
    hpoly:= Max([Log(Abs(c)) : c in clist] cat [Log(Abs(a))]);
    m:= Integers()! (432*DiscF*a^2);
    mS:= 1728*NS^2*(&*[p^(Min(2,Valuation(m,p))) : p in PrimeDivisors(m) | p notin primelist]);
    
    K:=fieldKinfo`field;
    OK:=fieldKinfo`ringofintegers;
    th:=fieldKinfo`gen;
    f:=fieldKinfo`minpoly;
    
    assert &and[ c in Integers() : c in Coefficients(f) ];
    assert IsMonic(f);
    n:=Degree(NumberField(OK));
    assert n eq Degree(f);
    
    thetaC:= Conjugates(th);
    assert n eq #thetaC;
    CField<i>:= ComplexField(ComplexPrec);
    
    taus:=[hom< K -> CField | thetaC[i] > : i in [1..n]];
    hth:= (1/n)*&+[Max((Log(Abs(taus[i](th)))), 0) : i in [1..n]];      // computes the Weil height of theta
    gam:= 2*hth + 2*Log(2) + 4*(2*mS*Log(mS) + 172*hpoly);
    
    for i in [1..#alphgamlist] do
        alpha:= alphgamlist[i]`alpha;
        halpha:= (1/n)*&+[Max((Log(Abs(taus[j](alpha)))), 0) : j in [1..n]];
        alphgamlist[i]`bound:= Ceiling(gam + 2*halpha);
    end for;
     
end procedure;



// for each Case, padic:

ImageInL:=function(mapsLL,elt);
    /*
    eltK:= an element in K or L
    This operation applies the ijk: L -> L maps to the element in K or L, elt
    */  
    
    ImageUnderMap:= [];
    for i in [1..#mapsLL] do
        ImageUnderMap[i]:= [];
        for j in [1..#mapsLL[i]] do
            ImageUnderMap[i][j]:= mapsLL[i][j](elt);
        end for;
    end for;
    
    return ImageUnderMap;
end function;


pAdicLog:=function(elt,p);
    // DETAILS TO ADD
    //Input: p = rational prime, x = p-adic unit belonging to a finite extension of Q_p
    //output: the p-adic logarithm of x
    
    e:=AbsoluteRamificationIndex(Parent(elt));
    f:=AbsoluteInertiaDegree(Parent(elt));
    r:=1;
    for o in Divisors(p^f - 1) do
        if Valuation(elt^o - 1) gt 0 then 
            r:=o; 
            break; 
        end if;
    end for;
    k:=1;
    while p^k le e do
        k:= k+1;
    end while;
    return Log( elt^(r*p^k) )/(r*p^k);
end function;   



Ellipsoid:= function(fieldKinfo,fieldLinfo,Case,i0jjkk,AutL,mapsLL,HeightBounds,RealPrec);

    // will need this later for real case too
    
    K:= fieldKinfo`field;
    OK:= fieldKinfo`ringofintegers;
    th:= fieldKinfo`gen;
    zeta:= fieldKinfo`zeta;
    epslist:= fieldKinfo`fundamentalunits;
    L:= fieldLinfo`field;
    OL:= fieldLinfo`ringofintegers;
    
    CasePrimes:= [Norm(fp) : fp in Case`ideallist];
    gammalist:= Case`gammalist;
    fplist:= Case`ideallist;
    alpha:= Case`alpha;
    matA:= Case`matA;
    
    i0:= i0jjkk[1];
    jj:= i0jjkk[2];
    kk:= i0jjkk[3];
    
    tau:= alpha*zeta;
    nu:= #gammalist;
    r:= #epslist;
    assert #CasePrimes eq nu;
    
    HeightBoundonGammalist:= HeightBounds`heightgammalist;
    HeightBoundonEpslist:= HeightBounds`heightepslist;
   
    // choose i0jk, mapsLL
    // generate images under the maps ijk: L-> L, th -> theta[i][j]
    tauL:=ImageInL(mapsLL,L!tau);
    gammalistL:= [ImageInL(mapsLL,L!gamma) : gamma in gammalist];
    epslistL:= [ImageInL(mapsLL,L!eps) : eps in epslist];

    RField:= RealField(RealPrec);
    SetDefaultRealField(RField); 
    
    // verify that the prime ideals in L above gamma do not cancel
    for i in [1..nu] do
        faci0:= Factorization(ideal<OL|gammalistL[i][i0[1]][i0[2]]>);
        facjj:= Factorization(ideal<OL|gammalistL[i][jj[1]][jj[2]]>);
        fackk:= Factorization(ideal<OL|gammalistL[i][kk[1]][kk[2]]>);
        assert (#faci0 eq #facjj) and (#facjj eq #fackk);
        assert &and[faci0[j][1] ne facjj[j][1] : j in [1..#faci0]];
        assert &and[facjj[j][1] ne fackk[j][1] : j in [1..#faci0]];
        assert &and[faci0[j][1] ne fackk[j][1] : j in [1..#faci0]];
    end for;
            
    CField<i>:= ComplexField(RealPrec);
    LintoC:= hom< L -> CField | Conjugates(L.1)[1] >; 
    
    // compute i1, i2: L- > C to generate matrix R
    for i1 in [1..#AutL] do
        for i2 in [i1 + 1..#AutL] do
            a:= (AutL[i1])(epslistL[1][jj[1]][jj[2]]/epslistL[1][i0[1]][i0[2]]);
            a:= RField!(Log(Abs(LintoC(a))));
            
            b:= (AutL[i1])(epslistL[2][jj[1]][jj[2]]/epslistL[2][i0[1]][i0[2]]);
            b:= Log(Abs(LintoC(b)));
            
            c:= (AutL[i2])(epslistL[1][jj[1]][jj[2]]/epslistL[1][i0[1]][i0[2]]);
            c:= Log(Abs(LintoC(c))); 
            
            d:= (AutL[i2])(epslistL[2][jj[1]][jj[2]]/epslistL[2][i0[1]][i0[2]]);
            d:= Log(Abs(LintoC(d))); 
            if (a*d - b*c) ne 0 then
                iotalist:= [i1,i2];
                break i1;
            end if;
        end for;
    end for;
            
    matR:= Matrix(ComplexField(RealPrec),2,2,[a,b,c,d]);
    tR, matRinv:= IsInvertible(matR);
    tA, matAinv:= IsInvertible(matA);
    assert tR and tA;
    i1:= iotalist[1];
    i2:= iotalist[2];
    
    // compute iota 1 gammas and iota 2 in definition of wgamlklist
    logamlistLi1:= [ Log(Abs(LintoC( (AutL[i1])(gammalistL[k][jj[1]][jj[2]]/gammalistL[k][i0[1]][i0[2]]) ))) : k in [1..nu]];
    logamlistLi2:= [ Log(Abs(LintoC( (AutL[i2])(gammalistL[k][jj[1]][jj[2]]/gammalistL[k][i0[1]][i0[2]]) ))) : k in [1..nu]];
    
    // compute the coefficients w_{gam,l,k} in the bound for Beps
    wgamlklist:= [];
    for l in [1..r] do
        wgamlklist[l]:= [];
        for k in [1..nu] do
            alphagamlk:= matRinv[l,1]*(&+[matAinv[i][k]*logamlistLi1[i] : i in [1..nu]]); 
            alphagamlk:= alphagamlk + matRinv[l,2]*(&+[matAinv[i][k]*logamlistLi2[i] : i in [1..nu]]);
            wgamlklist[l][k]:= Abs(alphagamlk)*Degree(K, Rationals())/Log(CasePrimes[k]);
        end for;
    end for;
    
    // compute the coefficients w_{eps,l,k} in the bound for Beps
    wepslklist:= [];
    for l in [1..r] do
        wepslklist[l]:= [];
        m:= Max(Abs(matRinv[l,1]), Abs(matRinv[l,2]));
        for i in [1..#AutL] do
            if i eq i1 then
                wepslklist[l][i]:= (m+Abs(matRinv[l,1]))*(Degree(L, Rationals()));
            elif i eq i2 then
                wepslklist[l][i]:= (m+Abs(matRinv[l,2]))*(Degree(L, Rationals()));
            else
                wepslklist[l][i]:= m*(Degree(L, Rationals()));
            end if;
        end for;
    end for;
                        
    Bgam:= Ceiling((1/Log(2)^2)*&+[ h^2 : h in HeightBoundonGammalist]);
    
    // compute bound b_eps; since r = 2, there is only 1 such b_eps where eps =! eps^*
        // choose eps^* = epslist[2]; hence l = 1 here
    Beps:= [];
    for l in [1..r] do
        Beps[l]:= ((1/Degree(K,Rationals()))*&+[HeightBoundonGammalist[k]*wgamlklist[l][k] : k in [1..nu]]);
        Beps[l]:= (Beps[l] + (1/Degree(L,Rationals()))*&+[HeightBoundonEpslist[k]*wepslklist[l][k] : k in [1..#AutL]])^2;
    end for;

    matD:= DiagonalMatrix(Integers(), [ Floor(Log(p)^2/Log(2)^2) : p in CasePrimes]); 
    matM:= IdentityMatrix(Integers(),nu+r);
    InsertBlock(~matM, (&*[Ceiling(Beps[l]) : l in [1..r]])*(Transpose(matA)*matD*matA), 1, 1);
    for l in [1..r] do
        matM[nu+l,nu+l]:= Bgam*(&*[Ceiling(Beps[k]) : k in [1..r] | k ne l]);
    end for;
    
    return matM,Bgam,Beps;
end function;



pLatticePrep:=procedure(fieldKinfo,fieldLinfo,Case,~localpinfo,ijkL,AutL,HeightBounds,Prec : UseSmallBound:=true);
    /*
    INPUT:
        primelist
        L
    OUTPUT:
       // for each prime p[l], stores theta[l][i][j]:= theta_i^{(j)}, tje associated roots of g in the completion of Q_{p[l]}
        // ie. for i in {1,...,m[l]}, theta[l][i] satisfies gp[l][i](theta[l][i]) = 0; ie g_i(theta_i) = 0
        // theta[l][i][1], ..., theta[l][i][n_i]:= theta_i^{(1)}, ..., theta_i^{(n_i)} for p[l] are the conjugates of theta[l][i]
    */
    
    pAdicPrec:= Prec[1];
    RealPrec:= Prec[2];
    
    K:= fieldKinfo`field;
    OK:= fieldKinfo`ringofintegers;
    th:= fieldKinfo`gen;
    f:= fieldKinfo`minpoly;
    L:= fieldLinfo`field;
    OL:= fieldLinfo`ringofintegers;
    zeta:= fieldKinfo`zeta;
    epslist:= fieldKinfo`fundamentalunits;
    n:= Degree(K);
    
    p:= localpinfo`prime;
    Lp:= localpinfo`Lp;
    mapLLp:= localpinfo`mapLLp;
    //fprsL:= localpinfo`idealinL;
    
    gammalist:= Case`gammalist;
    fplist:= Case`ideallist;
    alpha:= Case`alpha;
    nu:= #gammalist;
    r:= #epslist;
    
    //Lp, mapLLp:= Completion(L, fprsL : Precision:=pAdicPrec);
    fprs:=[f[1] : f in Factorisation(p*OK)];        // the prime ideals above p
    
    thetaL:=[];
    mapsLL:=[]; 
    for i in [1..#fprs] do      // runs through each prime ideal above p
        thetaL[i]:=[];
        mapsLL[i]:=[];       // the preimage of thetap in L 
                                    // ie. for th in L, mLp(ijk(th)) is one of the thetap in Lp 
        Kp, mKp:= Completion(K,fprs[i] : Precision:=pAdicPrec);
        gp_i:= MinimalPolynomial( mKp(th), PrimeField(Kp));
        temp:= Roots(gp_i, Lp);   // #temp = degree of gp_i = e_i*f_i
        for j in [1..#temp] do
            vals, ind:= Max([Valuation(mapLLp(ijkL[k](L!th)) - temp[j][1]) : k in [1..3]]);
            mapsLL[i][j]:= ijkL[ind];        // mLp(ijk[i][j](th)) maps to thetap[i][j]
            thetaL[i][j]:= ijkL[ind](L!th);
        end for;
    end for;

    assert n eq &+[#thetaL[i] : i in [1..#fprs]];       // check we have the correct number of thetas
    Lpt:=ChangePrecision(Lp,Min([Precision(mapLLp(thetaL[i][j])) : j in [1..#thetaL[i]], i in [1..#thetaL]]));
    check:= [Precision(mapLLp(thetaL[i][j])) : j in [1..#thetaL[i]], i in [1..#thetaL]];
    // verify that thetap[i][j] are roots of f 
    assert &and[Lpt!0 eq (Lpt!0 - Evaluate(f,mapLLp(thetaL[i][j]))) : j in [1..#thetaL[i]], i in [1..#thetaL]];
    // verify the precision has not been changed by the above test
    assert [Precision(mapLLp(thetaL[i][j])) : j in [1..#thetaL[i]], i in [1..#thetaL]] eq check;
    // verify the thetap[i][j] are the same roots as would be obtained by sending th in L into Lp
        // Note: this correspondence will not generate the roots in the correct order
        // This is due to the fact that we cannot work in the algebraic closure of Qp, but only in one Lp
        // ideally, we would be working in each Lp above each prime ideal over p in K, 
        // but Magma does not allow this
        
    assert (#thetaL eq 2) or (#thetaL eq 3);
    inds:= [];  // stores the indices of the unbounded primes in fplist
    // verifies there is a prime ideal above p in fplist
    assert &or[fq in fplist : fq in fprs];     
    for i in [1..#fplist] do
        fp:= fplist[i];
        for j in [1..#fprs] do
            fq:= fprs[j];
            if fq eq fp then
    // index of prime ideal above p appearing in fplist
                Append(~inds, j);   
            end if;
        end for;
    end for;
    assert #inds eq 1;  // this is i0
    i0:=[inds[1],1];    // root of g_inds(t), first (and only) element
    // verifies the unbounded ideal corresponds to deg(gp) = 1
    assert #thetaL[i0[1]] eq 1;    
    assert fprs[i0[1]] in fplist;
    
    // chooses j,k where g(t) = g_1(t)g_2(t), deg(g_1) = 1, deg(g_2) = 2
    indjk:= [i : i in [1..#thetaL] | i ne inds[1]];
    if #thetaL eq 2 then
        assert #indjk eq 1;
        assert #thetaL[indjk[1]] eq 2;
        jj:= [indjk[1],1];
        kk:= [indjk[1],2];
    elif #thetaL eq 3 then
        assert (#thetaL[indjk[1]] eq 1) and (#thetaL[indjk[2]] eq 1);
        assert #indjk eq 2;
        jj:= [indjk[1],1];
        kk:= [indjk[2],1];
    end if;
    
    assert thetaL[jj[1]][jj[2]] ne thetaL[kk[1]][kk[2]]; 
    tau:=alpha*zeta;
    
    // generate images under the maps ijk: L-> L, th -> theta[i][j]
    tauL:=ImageInL(mapsLL,L!tau);
    gammalistL:= [ImageInL(mapsLL,L!gamma) : gamma in gammalist];
    epslistL:= [ImageInL(mapsLL,L!eps) : eps in epslist];

    // verify that the prime ideals in L above gamma do not cancel
    for i in [1..nu] do
        faci0:= Factorization(ideal<OL|gammalistL[i][i0[1]][i0[2]]>);
        facjj:= Factorization(ideal<OL|gammalistL[i][jj[1]][jj[2]]>);
        fackk:= Factorization(ideal<OL|gammalistL[i][kk[1]][kk[2]]>);
        assert (#faci0 eq #facjj) and (#facjj eq #fackk);
        assert &and[faci0[j][1] ne facjj[j][1] : j in [1..#faci0]];
        assert &and[facjj[j][1] ne fackk[j][1] : j in [1..#faci0]];
        assert &and[faci0[j][1] ne fackk[j][1] : j in [1..#faci0]];
    end for;
    
    // check if we can bound Nail early (Lemma 6.5)
    delta1L:=(thetaL[i0[1]][i0[2]] - thetaL[jj[1]][jj[2]])/(thetaL[i0[1]][i0[2]] - thetaL[kk[1]][kk[2]]);
    delta1L:=delta1L*(tauL[kk[1]][kk[2]]/tauL[jj[1]][jj[2]]);
    delta2L:=(thetaL[jj[1]][jj[2]] - thetaL[kk[1]][kk[2]])/(thetaL[kk[1]][kk[2]] - thetaL[i0[1]][i0[2]]);
    delta2L:=delta2L*(tauL[i0[1]][i0[2]]/tauL[jj[1]][jj[2]]);
        
    if (Valuation(mapLLp(delta1L)) ne 0) then
        smallbound:= Min[Valuation(mapLLp(delta1L)),0] - Valuation(mapLLp(delta2L));
        if smallbound ge 0 then
            localpinfo`smallbound:= smallbound;
        else
            localpinfo`smallbound:= -1;     // negative bound; Case can be removed
        end if;
    else
        Logdelta1:= pAdicLog(mapLLp(delta1L),p); 
        Loggammalist:=[pAdicLog(mapLLp(gammalistL[i][kk[1]][kk[2]]/gammalistL[i][jj[1]][jj[2]]), p) : i in [1..nu]];
        Logepslist:=[pAdicLog(mapLLp(epslistL[i][kk[1]][kk[2]]/epslistL[i][jj[1]][jj[2]]), p) : i in [1..r]];
        LogList:= Loggammalist cat Logepslist;
        assert #LogList eq (nu+r);
        
        minval,ihat:= Min([Valuation(LogList[i]) :i in [1..nu+r]]);
        
        if Valuation(Logdelta1) lt minval then
            smallbound:= Max([Floor((1/(p-1) - Valuation(mapLLp(delta2L)))),Ceiling(minval - Valuation(mapLLp(delta2L)))-1]);
            if smallbound ge 0 then
                localpinfo`smallbound:= smallbound;
            else
                localpinfo`smallbound:= -1;     // negative bound; Case can be removed
            end if;
    // if the program makes it this far, there are no small bounds on Nail
    // arising from Lemma 6.5 and Lemma 6.9
    // hence the code must enter the FP process to reduce the bounds
    // generates the linear forms in p-adic logs elements for the Special Case
        else
            logihat:= LogList[ihat];  // offset the first term, Logdelta1
            betalist:= [-LogList[i]/logihat : i in [1..nu+r]];
            // assert that we are indeed in the special case, where neither lemma can immediately reduce the bound
            beta1:= -Logdelta1/logihat;
            assert &and[beta in pAdicRing(p) : beta in betalist] and (beta1 in pAdicRing(p));
            
            localpinfo`ihat:= ihat;
            localpinfo`logihat:= logihat;
            localpinfo`delta1inQp:= mapLLp(delta1L);
            localpinfo`delta2inQp:= mapLLp(delta2L);
            localpinfo`betalist:= [*beta1,betalist*];
            
            matM,Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,Case,[i0,jj,kk],AutL,mapsLL,HeightBounds,RealPrec);
            localpinfo`ellipsoid:= matM;
            localpinfo`bgam:= Bgam;
            localpinfo`bepslist:= BepsList;
        end if;
    end if;
end procedure;


pInteger:= function(Lp,p,mu,pAdicPrec,elt);
    /* thought i didn't need this. I definitely do
    
    // see spiel about magmas completion function
    // may need to verify this
    end if;*/
    coeffs:=Coefficients(elt);
    Ainv:=1;
    LpT:=5;
    d1:=Degree(Lp,CoefficientField(Lp));                   
    d2:=Degree(CoefficientField(Lp),PrimeField(Lp));             
    d3:=Degree(Lp,PrimeField(Lp));   // NB, d3:= d1*d2;
    if AbsoluteRamificationIndex(Lp) eq 1 then 
        LpT:=1;
        //u:=(1/2)*Valuation(Discriminant(DefiningPolynomial(Lp)));
        assert Valuation(Lp.1) ge 0;
    end if;
    if AbsoluteInertiaDegree(Lp) eq 1 then 
        LpT:=2; 
        //u:=(1/2)*Valuation(Discriminant(DefiningPolynomial(Lp)));
        assert Valuation(Lp.1) ge 0;
    end if;
    if (AbsoluteInertiaDegree(Lp) gt 1) and (d1 eq 1) then 
        LpT:=3;
        //u:=(1/2)*Valuation(Discriminant(DefiningPolynomial(CoefficientField(Lp))));
        assert Valuation(CoefficientField(Lp).1) ge 0;
        coeffs:=Coefficients(Coefficient(elt,1)); 
    end if;
    if (d1 gt 1) and (d2 gt 1) then
        LpT:= 4;
        k:=1;
        gen:= k*Lp.1 + (Lp ! CoefficientField(Lp).1);
        while (Degree(MinimalPolynomial(gen,PrimeField(Lp))) ne d3) do
            k:= k+1;
            gen:= k*Lp.1 + (Lp ! CoefficientField(Lp).1);
        end while;
        //u:= (1/2)*Valuation(Discriminant(MinimalPolynomial(gen,PrimeField(Lp))));
        assert Valuation(gen) ge 0;
        AA:=ZeroMatrix( PrimeField(Lp), d3, d3);    
        temp1:=Coefficients(gen);
        temp2:=Coefficients(temp1[1]); 
        for k in [1..d3] do
            temp1:=Coefficients(gen^(k-1));
            for i in [1..d1] do
                temp2:=Coefficients(temp1[i]);
                for j in [1..d2] do
                    AA[(i-1)*d2 + j,k]:=temp2[j];
                end for;
            end for;
        end for;
        Ainv:=AA^(-1);
        B:=ZeroMatrix( PrimeField(Lp), d3, 1);
        temp1:=Coefficients(elt);
        temp2:=Coefficients(temp1[1]); 
        for i in [1..d1] do
            temp2:=Coefficients(temp1[i]);
            for j in [1..d2] do
                B[(i-1)*d2 + j,1]:=temp2[j];
            end for;
        end for;
        C:=Ainv*B;
        coeffs:=[C[i][1] : i in [1..d3]];
    end if;    
    assert LpT ne 5;
    assert #coeffs eq AbsoluteDegree(Lp);
    
    /*
    Input: m = positive integer, p a prime 
    x = an element in the p-adic field Q_{p} that belongs to the subring Z_{p} (the ring of p-adic integers in Q_{p}).
    Output: The unique integer x^{m} in [0,p^m - 1] with ord_{p}(x - x^{m}) >= m
    */
    y:=pAdicRing(p : Precision:=pAdicPrec) ! coeffs[1];
    y:=pAdicQuotientRing(p, mu) ! y;

    y:=IntegerRing() ! y;
    if y lt 0 then 
        y:=y+p^(mu); 
    end if;
    
    return y;
end function;


pLattice:= function(fieldLinfo,localpinfo,pAdicPrec,mu);
                        
    p:= localpinfo`prime;
    Lp:= localpinfo`Lp;
    beta1:= localpinfo`betalist[1];
    betalist:= localpinfo`betalist[2];
    ihat:= localpinfo`ihat;
    matM:= localpinfo`ellipsoid;
    Bgam:= localpinfo`bgam;
    Bepslist:= localpinfo`bepslist;
    nuplusr:= #betalist;
    r:= #Bepslist;
    
    //assert &and[mu le Precision(beta) : be
    betalist:= [pInteger(Lp,p,mu,pAdicPrec,beta) : beta in betalist];
    // asserts that beta_ihat = -alpha_ihat/alpha_ihat = -1
    assert (betalist[ihat] eq (p^mu)-1);
    
    betalist[ihat]:= p^mu;
    beta1:= pInteger(Lp,p,mu,pAdicPrec,beta1);
    
    // define matrix
    matAm:= IdentityMatrix(Rationals(), (nuplusr));
    for i in [1..nuplusr] do
        matAm[ihat,i]:= betalist[i];
    end for;
    assert matAm[ihat,ihat] eq p^mu;
    
    // generates Transpose(matB)*matB
    matBtmatB:= Transpose(matAm)*matM*matAm;
    
    vecc:= ZeroMatrix(Rationals(), nuplusr, 1);
    vecc[ihat,1]:= -beta1/p^mu;
    boundForNormSquared:= Ceiling((1+r)*(Bgam*&*Bepslist));
   
    return matBtmatB, vecc, boundForNormSquared;
 
end function;



IsZeroLocal:=function(elt,S);
    /* DONT THINK I NEED THIS EITHER
   
    /*if Valuation(x) ge Valuation(Zero(Parent(x))) - 2*(AbsoluteDegree(Parent(x))-1) then
    return true;
    else
    return false;
    end if;*/
    if Valuation(elt) ge Valuation(Zero(Parent(elt))) - 2*(S-1) then
        return true;
    else
        return false;
    end if;
end function;


My_QuadraticForm:= function(matA);
    n:= NumberOfColumns(matA);     // computes the size of A
    matQ:= ZeroMatrix(RationalField(),n,n);
    for i in [1..n] do
        for j in [i..n] do
            s:= 0;
            for k in [1..i-1] do
                s:= s + matQ[k,i]*matQ[k,j]*matQ[k,k];
            end for;
            matQ[i,j]:= matA[i,j] - s;
            if i ne j then
                matQ[i,j]:= matQ[i,j]/matQ[i,i];
            end if;
        end for;
    end for;
    return matQ;
end function;


My_FinckePohst:= function(matA,boundForNormSquared: center:=0,maxNumSolutions:=-1,lllReduce:=true,breakSymmetry:=true);

    //forward traverseShortVectors;
    procedure traverseShortVectors(Q,n,i,~x,center,~shortVectors,RemainingBoundForNormSquared,~numSolutions, maxNumSolutions,finalTransformation, xIsCenterSoFar,~stillEnumerating) 
        
        
//        print "k,xIsCenterSoFar", i,xIsCenterSoFar;
//        print "===============";
//        print "start:,k,x ",i,x;
        if i eq 0 then
            if maxNumSolutions ne -1 and numSolutions ge maxNumSolutions then
                stillEnumerating:= false; //return false,x,shortVectors,Ts,numSolutions,xIsCenterSoFar;
            else
                numSolutions:= numSolutions + 1;
                y:= Transpose(finalTransformation*Transpose(x));
                Append(~shortVectors, y);
                //print "y = ", y;
                //print "Short Vectors = ", shortVectors;
                stillEnumerating:= true; //return true,x,shortVectors,Ts,numSolutions,xIsCenterSoFar;
            end if;
        else
            stillEnumerating:= true;
            updatingEntries:= true;
            //print "pre-center:,k", center, i;
            u:= -center[1,i];
            for j in [i+1..n] do
                u:= u + Q[i,j]*(x[1,j] - center[1,j]);
            end for;
            uCeil:= Ceiling(u);
            uFloor:= Floor(u);
//            print "-------------------";
//            print "Floor Ceil", -uFloor, -uCeil;
//            print "Floor Ceil", Floor(Sqrt(20/Q[i,i]) - u), Ceiling(-Sqrt(20/Q[i,i]) - u);
//            print "-------------------";
            
            xk0_up:= -uFloor;
            xk0_down:= -uCeil;
            //print "pose-center:,x,k,u,Q", x,i,u,Q, uFloor, uCeil;
            
            x[1,i]:= xk0_down;
            while updatingEntries do
                //print "preBOUND1:ONE k,x,u ",i,x,u;
                t:= Q[i,i]*(x[1,i]+u)^2;
                //print "t1 =", RealField()!t;
                //print "BOUND1", RemainingBoundForNormSquared; // last element
                if t gt RemainingBoundForNormSquared then
                   // print "prebreak1:ONE k,x,t,u ",i,x,t, u;
                    if x[1,i] ge xk0_up then
                     //   print "break1";
                        updatingEntries:= false;
                        break;
                    end if;
                    x[1,i]:= x[1,i] + 1;
                    continue;
                end if;
               // print "ONE k,x,t,u ",i,x,t, u;
               
                $$(Q,n,i-1,~x,center,~shortVectors,RemainingBoundForNormSquared-t,~numSolutions,maxNumSolutions,finalTransformation,xIsCenterSoFar and x[1,i] eq center[1,i],~stillEnumerating);
                if stillEnumerating eq false then
                 
                 //   print "ohno!";
                    updatingEntries:= false;
                    break;
                   
                end if;
                x[1,i]:= x[1,i] + 1;
                //print "end of loop1:", x;
            end while;
            
//            print "switch";
//    //        print "MID k,x,t,u", i, x, t, u;
//    //        print "MID BOUND", RemainingBoundForNormSquared; // last element
//            print "stillEnumerating, xisCenter", stillEnumerating, xIsCenterSoFar;
//            print "=======================";
            
            if (xIsCenterSoFar eq false) and (stillEnumerating eq true) then
                x[1,i]:= xk0_down-1;
                updatingEntries:= true;
                while updatingEntries do
                    t:= Q[i,i]*(x[1,i]+u)^2;
    //                print "t2 =", RealField()!t;
    //                print "BOUND2", RemainingBoundForNormSquared; // last element
                    if t gt RemainingBoundForNormSquared then
                        //print "break2";
                        updatingEntries:= false;
                        break;
                    end if;
                    //print "TWO k,x,t,u ",i,x,t, u;
                    $$(Q,n,i-1,~x,center,~shortVectors,RemainingBoundForNormSquared-t,~numSolutions,maxNumSolutions,finalTransformation,false,~stillEnumerating);
                    if stillEnumerating eq false then
                    //if tf eq false then
                      //  print "ohno!";
                        updatingEntries:= false;
                        break;
                        //return false, x,shortVectors,RemainingBoundForNormSquared,numSolutions,xIsCenterSoFar;
                    end if;
                    x[1,i]:= x[1,i] - 1;
                end while;
            end if;
        //return true, x,shortVectors,Ts,numSolutions,xIsCenterSoFar;
        end if;

    end procedure;

    n:= NumberOfColumns(matA);     // computes dimension of square input matrix A
    assert IsSymmetric(matA);
    assert IsPositiveDefinite(matA);
    
    if IsZero(center) then
        center:= ZeroMatrix(Integers(), n, 1);
    end if;
    assert (BaseRing(center) eq Integers()) or (BaseRing(center) eq Rationals()); 
    
    if NumberOfColumns(center) ne n then
        center:= Transpose(center);
    end if;
    assert (NumberOfColumns(center) eq n) and (NumberOfRows(center) eq 1);
    
    if &and[center[1,i] notin Integers() : i in [1..n]] then
        breakSymmetry:= false;  //#We check this here, as after multiplication with U, center.base_ring() might become QQ! (even though U's base_ring is ZZ as well...)
    end if;
    
    if lllReduce then
        matG,matU,n:= LLLGram(matA);
        assert n eq NumberOfColumns(matG);
        assert matG eq matU*matA*Transpose(matU);
        if BaseRing(center) eq Rationals() then
            matU:= ChangeRing(Transpose(matU), Rationals());
        else
            matU:= Transpose(matU);
        end if;
        tf,matUinv:= IsInvertible(matU);
        assert tf;
        finalTransformation:= matU;
        if not IsZero(center) then
            center:= Transpose(matUinv*Transpose(center));
        end if;
    end if;
    
    assert (NumberOfColumns(center) eq n) and (NumberOfRows(center) eq 1);
    assert IsSymmetric(matG);
    assert IsPositiveDefinite(matG);

    Q:= My_QuadraticForm(matG);
    x:= ZeroMatrix(Rationals(),1,n);
    
    stillEnumerating:= true;
    solutionsList:= []; // stores short vectors
    numSolutions:= 0;
    finalTransformation:= ChangeRing(finalTransformation, Rationals());
    
    traverseShortVectors(Q,n,n,~x,center,~solutionsList,boundForNormSquared, ~numSolutions, maxNumSolutions,finalTransformation,breakSymmetry, ~stillEnumerating); //stillEnumerating);
    bufferWasBigEnough:= stillEnumerating;
    assert #solutionsList eq numSolutions;
    assert (maxNumSolutions eq -1) or (#solutionsList le maxNumSolutions);
    
    return bufferWasBigEnough, solutionsList;
end function;


//Gamma:= Matrix(Integers(),4,4,[1,5,3,4,3,1,2,3,4,1,2,3,4,5,6,7]);
//print "Gamma:";
//print Gamma;

////The associated Gram matrix:
//matA:= Transpose(Gamma)*Gamma;
//print "A:";
//print matA;

//center:= Matrix(Rationals(),4,1,[0,0,0,6/7]);
//print "center of ellipsoid:",center;

//boundForNormSquared:= 2;
//maxNumSolutions:= 100;
//bufferWasBigEnough, solutionsList:= My_FinckePohst(matA,boundForNormSquared:center:=center, maxNumSolutions:=-1,lllReduce:=true, breakSymmetry:= true);






// test:
clist:= [1,-23,5,24];
primelist:= [2,3,5,7]; 
a:= 1;
 
clist:= [1,23,17,2];    // something weird about algs1and2
primelist:= [7,41]; 
a:= 1;
 
clist:= [1,7,23,-25];   // gives an error in principalize; r = 1
primelist:= [2,3,7,37,53]; 
a:= 1;
 
clist:= [1,17,23,-27];  
primelist:= [2,3,7,37,53]; 
a:= 1; 
 
clist:= [1,17,23,-27];  
primelist:= [1987,1999]; 
a:= 1; 
 
 
 
 
 
 
// for now assumes gcd(x,y) = 1 and gct(y,c_0) = 1 
//TMSolver:= function(clist,primelist,a);
// Real Case only for now
        
    //t0:= Cputime();
    assert &and[IsPrime(p) : p in primelist];
    assert &and[c in Integers() : c in clist];
    c0:=Integers()!clist[1];
    assert c0 ne 0;
    n:=#clist-1;
    assert n eq 3;
    assert a ne 0;
    printf "Resolving Thue-Mahler equation with... \n";
    printf "Coefficients: %o, Primes: %o \n", clist, primelist;
    printf "-"^(80) cat "\n" cat "-"^(80) cat "\n"; 
    
    // generate a record to store relevant field info
    FieldInfo:= recformat<field,gen,ringofintegers,minpoly,zeta,fundamentalunits>;
    
    alist, afplist, fieldKinfo:=prep1(clist, primelist, a);
    K:= fieldKinfo`field;
    th:= fieldKinfo`gen;
    f:= fieldKinfo`minpoly;
    OK:= fieldKinfo`ringofintegers;
    
    // alist is from the monic function; not used yet
    printf "Number of ideal equations: %o\n", #afplist;
    
    printf "Computing the class group...";
    t2:= Cputime();
    // generate a record to store relevant class group info
    ClassGroupInfo:= recformat<classgroup,classnumber,map>;
    ClK:= rec< ClassGroupInfo | >;
    ClK`classgroup, ClK`map:= ClassGroup(K);   
    printf "Done! Duration: %o\n", Cputime(t2);
    ClK`classnumber:= ClassNumber(K);
    
    printf "Computing all S-unit equations...";
    t2:= Cputime();
    alphgamlist:=prep2(fieldKinfo,ClK,afplist,primelist);
    printf "Done! Duration: %o\n", Cputime(t2);
    printf "Number of S-unit equations: %o\n", #alphgamlist;
    assert #alphgamlist ne 0;   
    
    s,t:= Signature(K);
    r:= s+t-1;
    assert (s+2*t) eq n;
    assert (r eq 1) or (r eq 2);
    printf "Computing the Unit Group...";
    t5:= Cputime();
    U,psi:= UnitGroup(OK);      // generates the fundamental units
    printf "Done! Duration: %o\n", Cputime(t5);
    // expresses the fund. units as elts in OK in terms of the integral basis
    epslist:=[psi(U.(i+1)) : i in [1..r]];    
    assert (#epslist eq 1) or (#epslist eq 2);  
    zetalist:= [psi(U.1)];      // generator for the units of finite order
    zeta:= (psi(U.1))^2;
    while (zeta ne psi(U.1)) and (zeta notin zetalist) and (-zeta notin zetalist) do
        Append(~zetalist, zeta);
        zeta:= zeta*psi(U.1);
    end while;
    // K has at least 1 real embedding, thus the torsion subgroup is {1,-1}
    assert #zetalist eq 1;      
    zeta:= zetalist[1];
    fieldKinfo`zeta:= zeta;
    fieldKinfo`fundamentalunits:= epslist;
    
    L, tl:= SplittingField(f); 
    printf "Computing the ring of integers of the splitting field...";
    t2:= Cputime();
    OL:= MaximalOrder(L);
    printf "Done! Duration: %o\n", Cputime(t2);
    tf,mapKL:= IsSubfield(K,L);
    assert tf;
    assert (L!th eq mapKL(th)) and (mapKL(th) in tl);
    fieldLinfo:= rec<FieldInfo | field:= L, gen:=tl,ringofintegers:= OL>;
    
    ijkL,AutL:= ijkAutL(fieldLinfo);
    assert ijkL[3](th) eq L!th; // this is the identity automorphism

    /////
    //To DO: temp!
        // pprecs:= padicprecision(primelist, L);      // estimated required precision 
        // precision calculations
    ///// 
    // generate a record to store relevant p-adic field info
    
    pAdicPrec:= 400;
    RealPrec:= 100;
    ComplexPrec:= 100;
    // compute the initial height bound: change me
    printf "Computing initial height bounds...";
    t1:= Cputime();
    UpperBounds(fieldKinfo,clist,primelist,a,~alphgamlist,ComplexPrec);
    printf "Done! Duration: %o\n", Cputime(t1);
 
    // begin cycling through cases
    CaseNo:= 1;
    for Case in alphgamlist do
//Case:= alphgamlist[1];

        CasePrimes:= [Norm(fp) : fp in Case`ideallist];
        nu:= #Case`gammalist;
        assert #CasePrimes eq nu;
        assert &and[p in primelist : p in CasePrimes];
        printf "-"^(80) cat "\n"; 
        printf "Case: %o\n", CaseNo;
        printf "Initial height bound: %o\n", Case`bound;
        
        HeightBoundInfo:= recformat<heightgammalist,heightepslist>;
        HeightBounds:= rec<HeightBoundInfo | heightgammalist:= [Case`bound : i in [1..nu]],heightepslist:= [Case`bound : i in [1..#AutL]]>;
        
         //pprecs:= padicprecision(primelist, L);      // estimated required precision 
        // generate a record to store relevant local info

// padic: 
    pCaseInfo:= recformat<prime,Lp,mapLLp,smallbound,delta1inQp,delta2inQp,ihat,logihat,betalist,ellipsoid,bgam,bepslist>;
    //printf "Computing all roots of f in Cp...";
        t3:= Cputime();
    localpinfoList:= [];
        

UseSmallBound:= false;  // still to include
pAdicPrec:= 400; 
RealPrec:= 100;

// run through all possible combos of embeddings 

Prec:= [pAdicPrec,RealPrec];
    for i in [1..nu] do
        p:= CasePrimes[i];
        idealinL:= (Factorisation(p*OL))[1][1];
        Lp, mapLLp:= Completion(L, idealinL : Precision:=pAdicPrec);
        
        localpinfoList[i]:=rec< pCaseInfo | prime:= p, Lp:= Lp, mapLLp:= mapLLp>;


        // compute thetas, relevant maps for each prime in the TM equation
        pLatticePrep(fieldKinfo,fieldLinfo,Case,~localpinfoList[i],ijkL,AutL,HeightBounds,Prec : UseSmallBound);        
        
        if (assigned localpinfoList[i]`smallbound) and (UseSmallBound eq true) then
            // reduce equation to move alpha into other cases
            // should check if now, we are in one of the other cases
            // ie shuffle throught the other cases to see if there is a match
        end if;
        delta1:= localpinfoList[i]`delta1inQp;
        delta2:= localpinfoList[i]`delta2inQp;
        logihat:= localpinfoList[i]`logihat;
        
        lv:= 200; 
        cp:= Log(p)*(Max(1/(p-1),Valuation(delta1)) - Valuation(delta2));
        assert lv ge cp;
        assert HeightBounds`heightgammalist[i] gt Max(0,cp);
        
        mu:= Floor(lv/Log(p) - Valuation(logihat) + Valuation(delta2));
            
        print "mu:", mu;
        //print "mu/Case`bound", RealField()!(mu/Case`bound);
        matBtmatB, vecc, boundForNormSquared:= pLattice(fieldLinfo,localpinfoList[i],pAdicPrec,mu);
        
        boundForNormSquared;
        bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=100,lllReduce:=true, breakSymmetry:= true);
        #solutionsList;
        

    end for;
    printf "Done! Duration: %o\n", Cputime(t3);
    
end for;
        
         
// Real
 
        
 
 bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=100,lllReduce:=true, breakSymmetry:= true);

 
 
 
 
 
 
 
 
 
 
        
                // if r = 2:

    
Reallattice:
          
          
 compute wgamlatlist,wepslatlist, then matM, then:  and add Bepstar in 
// generates real lattice matrix
    ///////
    // CHECK THAT CONDITIONS OF THE LEMMATA ARE MET; choose tau // shuffle through tau;
    i:= 1;      // TEMP
    tauAut:= AutL[i];
    ctau:= Log(Max(1,2*Abs( LintoC(tauAut(delta2L)))));
    assert hepslist[i] gt ctau; // MIGHT NEED TO BE AN IF STATEMENT
    ktau:= (3/2)*Abs( LintoC(tauAut(delta2L))); // TEMP
    ltau:= Floor(1/2*Log(quadbound));   //TEMP; try 1000
    ltau:= 200;
    c:= Ceiling(Exp(ltau)); // TEMP
    // compute bound b
    Bgam:= Ceiling((1/Log(2)^2)*&+[ h^2 : h in hgamlist]);
    
    // compute bound b_eps; since r = 2, there is only 1 such b_eps where eps =! eps^*
        // choose eps^* = epslist[2]; hence l = 1 here
    Beps:= ((1/Degree(K,Rationals()))*&+[hgamlist[k]*wgamlklist[1][k] : k in [1..nu]]);
    Beps:= Ceiling((Beps + (1/Degree(L,Rationals()))*&+[hepslist[k]*wepslklist[1][k] : k in [1..#AutL]])^2);
    
    // compute bound b_eps^*; since r = 2, there is only 1 such b_eps where eps =! eps^*
        // choose eps^* = epslist[2]; hence l = 2 here
        
    sum1:= (1/Degree(K,Rationals()))*&+[hgamlist[k]*wgamlatlist[k] : k in [1..nu]];
    sum2:= (1/Degree(L,Rationals()))*&+[hepslist[k]*wepslatlist[k] : k in [1..#AutL]];
    Bepstar:= Ceiling(((1/2)*(sum1 + sum2) + 1/2 + c*ktau*Exp(-ltau))^2);
    
    
    /////////
    // should make eps^* more explicit maybe

    // compute alpha_{gam, k} for the lattice Gamma_tau
    alpha0:= Round(c*Log(Abs(LintoC(tauAut(delta1L)))));     // might have to consider what Round is doing here
    alphagamlist:= [Round(c*Log(Abs(LintoC( tauAut(gammalistLk[k]/gammalistLj[k]) )))) : k in [1..nu]];
    
    // compute alpha_{eps, 1} for the lattice Gamma_tau
        // choose eps^* = epslist[2];
    alphaepslist:= [Round(c*Log(Abs(LintoC( tauAut(epslistLk[k]/epslistLj[k]) )))) : k in [1..r]];
    
    // generate the matrix defining the lattice Gamma_tau
    matGtau:= IdentityMatrix(Integers(),nu+r);
    for i in [1..nu] do
        matGtau[nu+r,i]:= alphagamlist[i];
    end for;
    for i in [nu+1..nu+r] do
        matGtau[nu+r,i]:= alphaepslist[i-nu];
    end for;
    
//            // TESTING TRANSLATED LATTICE
//            matGtau:= IdentityMatrix(Rationals(),nu+r);
//            for i in [1..nu] do
//                matGtau[nu+r,i]:= alphagamlist[i];
//            end for;
//            for i in [nu+1..nu+r] do
//                matGtau[nu+r,i]:= alphaepslist[i-nu];
//            end for;
    
//             // generate the translation vector w_tau of the lattice Gamma_tau
//            vecWtau:= ZeroMatrix(Rationals(),nu+r,1);
//            vecWtau[nu+r,1]:= alpha0;
//           // END OF TEST
    
    
    
    
//            // generate the translation vector w_tau of the lattice Gamma_tau
//            vecWtau:= ZeroMatrix(Integers(),nu+r,1);
//            vecWtau[nu+r,1]:= alpha0;
    
    // generate the matrix representing the ellipsoid, M^T*M;
    matM:= IdentityMatrix(Integers(),nu+r);
    InsertBlock(~matM, (Beps*Bepstar)*(Transpose(matA)*matD*matA), 1, 1);
    //InsertBlock(~matM, (Transpose(matA)*matD*matA), 1, 1); 
    matM[nu+1, nu+1]:= Floor(Bgam*Bepstar);
    matM[nu+2, nu+2]:= Floor(Bgam*Beps);
    
    // generate the matrix B^T*B
    matB:= Transpose(matGtau)*matM*matGtau;
    center:= ZeroMatrix(Rationals(), nu+r, 1);
    center[nu+r,1]:= -alpha0/alphaepslist[r];
    boundForNormSquared:= Ceiling((1+r)*(Bgam*Beps*Bepstar));

return matB, boundForNormSquared, center;
            maxNumSolutions:= 10;
            bufferWasBigEnough, solutionsList:= My_FinckePohst(matB,boundForNormSquared:center:=center, maxNumSolutions:=-1,lllReduce:=true, breakSymmetry:= true);


////////////////////////////////////////////////////////////////////////////////
///// NON-ARCHIMEDEAN CASE /////////////////////////////////////////////////////
////oh how i wish all of the code would fit in the lines properly///////////////



prec:= 30; //placeholder
Thetaps:= [];
printf "Computing all roots of f in Cp...";
t3:= Cputime();
for i in [1..#gammalist] do
    p:=primelist[i];
    fprsL:= Factorisation(p*OL);
    fprsL:= fprsL[1][1];
    //prec:= pprecs[i];
    Thetaps[i]:= thetas(th,p,prec,L,fprsL);
end for;

// need Realijk here




           

Roundp:=function(elt);
    /*
    Input: x = a real number
    Ouput: The nearest positive integer to x.  If two postive integers are the 
    same distance to x, take the largest of the two.
    */
    assert elt ge 0;
    y:= Round(elt);
    if y eq 0 then 
        y:=1; 
    end if;
    return y;
end function;


RNTO:=function(elt);
    /*
    RNTO = Round Nonpositive to One
    Input: x = a real number
    Output: x if x > 0, 1 if x <= 0
    */
    if elt le 0 then 
        return 1;
    else
        return elt;
    end if;
end function;


pInteger:=function(elt,p,m,prec);

    /*
    Input: m = positive integer, p a prime 
    x = an element in the p-adic field Q_{p} that belongs to the subring Z_{p} (the ring of p-adic integers in Q_{p}).
    Output: The unique integer x^{m} in [0,p^m - 1] with ord_{p}(x - x^{m}) >= m
    */
    y:=pAdicRing(p : Precision:=prec) ! elt;
    y:=pAdicQuotientRing(p, m) ! y;

    y:=IntegerRing() ! y;
    if y lt 0 then 
        y:=y+p^m; 
    end if;
    return y;
end function;




           
           


latticeprep:=function(p,prec,L,fprsL,eps,zeta,thetap,quad);
     /*
    INPUT:
        fa:= an ideal in OK such that
            fa * fp_1^{n_1} * ... * fp_u^{n_u} = principal ideal
        fplist:= a list of prime ideals
        
    OUTPUT:
        tf, alpha, gammalist, matA, rr.
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
    
    REMARKS:
        // I shouldn't start with this since this isn't the first thing we do...
    
    
    EXAMPLE:
    
    // clist is a list of coefficients c_0,c_1,..,c_n.
    // a is an integer.
    // primelist is a list of the primes p_1,p_2,..,p_v.
    // This returns a list of the possible quadruples [* alpha, gammalist, matA, r *] 
    // where alpha in K^*, and gammalist is a list gamma_1,...,gamma_u 
    // so that (c_0 X - th Y)OK =alpha*gamma_1^{m_1}*..*gamma_u^{m_u} (as in equation (4)).
    // matA and rr are the matrix A and the vector rr, so that 
    // nn = mm A + rr, where nn is the vector of exponents in (3)
    // and mm is the vector of exponents in (4).
    // DETERMINE PRECISION FOR P OUTSIDE LOOP
    
    // chooses d_l, ihat, h;
    returns return MBnail, beta, h, ihat, dd, delta2;
    */
    K:=NumberField(Universe([quad[1]]));
    OK:=MaximalOrder(K);
    th:=K.1;
    f:=MinimalPolynomial(th); 
    assert &and[ c in Integers() : c in Coefficients(f) ];
    assert IsMonic(f);
    assert IsIrreducible(f);
    n:=Degree(NumberField(OK));
    assert n eq Degree(f);
    f:=MinimalPolynomial(th); 
    Lp, mLp:= Completion(L, fprsL : Precision:=prec);
    Nail, i0jk:= pAdicjk(p,prec,L,fprsL,eps,zeta,thetap,quad);
    // verify Lemma 6.5
    if (Nail ne -1) and (i0jk ne [[],[],[]]) then
        assert Nail ge 0;
        //return Nail,[],0,0,0;
    end if;        
    assert #i0jk eq 3;
   // assert (zeta eq K![-1,0,0,0] or zeta eq K![1,0,0,0]);
    alpha:= quad[1];
    gammalist:= quad[2];
    v:= #gammalist;
    // image of gamma under th -> thetap[i][j]
    gammap:= [ImageInp(th,thetap,gamma) : gamma in gammalist];
    fprs:= Factorisation(p*OK);
    fprs:=[fact[1] : fact in fprs];     // the prime ideals above p
    assert &and[#thetap[i] eq RamificationDegree(fprs[i])*InertiaDegree(fprs[i]) : i in [1..#fprs]];
    // image of eps under th -> thetap[i][j]
    epsp:= ImageInp(th,thetap,eps);    
    tau:=alpha*zeta;
    // image of tau under th -> thetap[i][j]
    taup:= ImageInp(th,thetap,tau); 
    i0:= i0jk[1];
    jj:= i0jk[2];
    kk:= i0jk[3];
    assert #thetap[i0][1] eq 1;
    delta1:=(thetap[i0][1] - thetap[j[1]][j[2]])/(thetap[i0][1] - thetap[k[1]][k[2]]);
    delta1:= delta1*(taup[k[1]][k[2]]/taup[j[1]][j[2]]);
    assert Valuation(delta1) eq 0;
    delta2:=(thetap[j[1]][j[2]] - thetap[k[1]][k[2]])/(thetap[k[1]][k[2]] - thetap[i0][1]);
    delta2:= delta2*(taup[i0][1]/taup[j[1]][j[2]]);
    logalph:= pAdicLog(delta1,p); 
    assert IsZeroLocal(logalph,AbsoluteDegree(Lp)) eq false;   
    temp1:=[pAdicLog(gammap[i][k[1]][k[2]]/gammap[i][j[1]][j[2]], p) : i in [1..v]];
    temp2:=[pAdicLog(epsp[k[1]][k[2]]/epsp[j[1]][j[2]], p)];
    logalph:= [logalph] cat temp1 cat temp2;
    assert #logalph eq (v+2);
    // verify Lemma 6.9(i)
    vals:= Min([Valuation(logalph[i]) : i in [2..(v+2)]]);
    if Valuation(logalph[1]) lt vals then
        Nail:=Max([Floor((1/(p-1) - Valuation(delta2))), Ceiling(vals - Valuation(delta2))-1]);
        if Nail ge 0 then
            return Nail,[],0,0,0;
        else
            return 0,[],0,0,0;
        end if;
    end if;
    // verify Lemma 6.9(ii)
    cals:= [LpType(la,p,Lp)[2] : la in logalph];        // coefficients of alpha_{ih}
    u:= LpType(logalph[1],p,Lp)[1];
    temph:= 1;
    for h in [1..AbsoluteDegree(Lp)] do
        nailh:=[];      // stores bounds for each h, where they exist
        if IsZeroLocal(cals[1][h],AbsoluteDegree(Lp)) eq false then
            temph:= h;
            valsh:= Min([Valuation(cals[i][h]) : i in [2..v+2]]);
            if Valuation(cals[1][h]) lt valsh then
                Append(~nailh, Max([Floor((1/(p-1) - Valuation(delta2))), Ceiling(valsh - Valuation(delta2) + u)-1]));
            end if;
        end if;
    end for;
    if #nailh ge 1 then // holds for at least 1 h
        Nail:= Min(nailh);
        if Nail ge 0 then
            return Nail,[],0,0,0;
        else
            return 0,[],0,0,0;
        end if;
    end if;
    // if the program makes it this far, there are no small bounds on Nail
        // arising from Lemma 6.5 and Lemma 6.9
        // hence the code must enter the LLL process to reduce the bounds
    // generates the linear forms in p-adic logs elements for the Special Case
    if SpecialCase eq true then
        min:=Valuation(logalph[2]);
        vals, ihat:= Min([Valuation(logalph[i]) : i in [2..(v+2)]]);
        ihat:= ihat + 1;
        assert Valuation(logalph[1]) ge vals;     
        assert Valuation(logalph[ihat]) eq vals;
        beta:= [-logalph[i]/logalph[ihat] : i in [1..v+2]];
        beta:= [LpType(b,p,Lp)[2][1] : b in beta];
        dl:= Valuation(delta2) - Valuation(logalph[ihat]);
        return -1, beta, ihat, dl, delta2;
    // generates the linear forms in p-adic logs elements for the General Case
    else
        cals:= [LpType(la,p,Lp)[2] : la in logalph];        // coefficients of alpha_{ih}
        u:= LpType(logalph[1],p,Lp)[1];
        h:= temph;  // fix h in [1..AbsoluteDegree(Lp)] arbitrarily to be temph
        assert IsZeroLocal(cals[1][h],AbsoluteDegree(Lp)) eq false; 
        valsh, ihat:= Min([Valuation(cals[i][h]) : i in [2..v+2]]);
        ihat:= ihat + 1;
        assert Valuation(cals[1][h]) ge valsh;
        assert Valuation(cals[ihat][h]) eq valsh;
        assert IsZeroLocal(cals[ihat][h],AbsoluteDegree(Lp)) eq false;
        beta:= [-cals[i][h]/cals[ihat][h] : i in [1..v+2]];
        dl:= Valuation(delta2) - Valuation(logalph[ihat]) - u;
        return -1, beta, ihat, dl, delta2;
    end if; 
end function;


    
    sc1:= false;        // placeholder to verify Lemma 6.5
    for jk in pairs do
        j:= jk[1];
        k:=jk[2];
        delta1:=(thetap[i0][1] - thetap[j[1]][j[2]])/(thetap[i0][1] - thetap[k[1]][k[2]]);
        delta1:= delta1*(taup[k[1]][k[2]]/taup[j[1]][j[2]]);
        if Valuation(delta1) ne 0 then
            delta2:=(thetap[j[1]][j[2]] - thetap[k[1]][k[2]])/(thetap[k[1]][k[2]] - thetap[i0][1]);
            delta2:= delta2*(taup[i0][1]/taup[j[1]][j[2]]);
            Nail:= Min[Valuation(delta1),0] - Valuation(delta2);
            if Nail ge 0 then
                //sc1:= true;
                // OLD
                // return Nail, [[],[],[]], false;
                print Nail;
                break jk;
            else
    // no solutions are possible from this S-unit equation
        // set default bound to 0
                sc1:= true;
                print 0;
                //OLD
                //return 0, false;
                break jk;
            end if;
        end if;
    end for;
    assert (sc1 eq false);      // else the program will have ended

     -1, [[i0,1],j,k], false;
        
            
                
                    
//        // if f has at least 3 linear factors in Qp[t]; 
//        // choose j,k to correspond to the roots of these linear factors
//        // NB. each factor corresponds to a prime ideal above p
//    if (&+[1 : i in [1..#fprs] | #thetap[i] eq 1] ge 3) then 
//        jsks:= [[j,k] : j in [1..#fprs], k in [1..#fprs] | (j ne k) and (j ne i0) and (k ne i0)];
//        jsks:= [jk : jk in jsks | (#thetap[jk[1]] eq 1) and (#thetap[jk[2]] eq 1)];         
//        j:= [jsks[1][1],1];
//        k:= [jsks[1][2],1];
//        assert (#thetap[j[1]] eq 1) and (#thetap[k[1]] eq 1);
//        assert (j[1] ne k[1]) and (j[1] ne i0) and (k[1] ne i0);
//        SpecialCase:= true;
//        return -1, [[i0,1],j,k], SpecialCase;
//    // if f has an irreducible factor in Qp[t] of degree 2
//        // choose j,k to correspond to the roots of this quadratic factor
//    elif (2 in [#thetap[i] : i in [1..#fprs]]) then
//    // determines the index of the degree 2 linear factor
//        jk:= Index([#thetap[i] : i in [1..#fprs]], 2);  
//        assert #thetap[jk] eq 2;
//        j:= [jk,1];
//        k:= [jk,2];
//        SpecialCase:= true;
////        return -1, [[i0,1],j,k], SpecialCase;
////    // we are not in the special case
////        // choose j,k to correspond to the roots of the same irred. factor in Qp[t]
////    else
////    // the upper bound on deg(gp) < [Lp:Qp]
////        Lpdeg:= Degree(Lp,PrimeField(Lp));
////        for i in [1..#fprs] do
////            RI:= RamificationIndex(fprs[i]);
////            ID:= InertiaDegree(fprs[i]);
////            if (RI*ID gt 1) and (RI*ID lt Lpdeg) then
////                Lpdeg:= RI*ID;
////                j:= [i,1];
////                k:= [i,2];
////            end if;
////        end for;
////        assert #thetap[j[1]] gt 2;
////        return -1, [[i0,1],j,k], false;

//    assert &and[thetap[jk[1][1]][jk[1][2]] ne thetap[jk[2][1]][jk[2][2]] : jk in pairs]; 
    

    
    
//      if (&+[1 : i in [1..#fprs] | #thetap[i] eq 1] ge 3) then 
//        jsks:= [[j,k] : j in [1..#fprs], k in [1..#fprs] | (j ne k) and (j ne i0) and (k ne i0)];
//        jsks:= [jk : jk in jsks | (#thetap[jk[1]] eq 1) and (#thetap[jk[2]] eq 1)];         
//        j:= [jsks[1][1],1];
//        k:= [jsks[1][2],1];
//        assert (#thetap[j[1]] eq 1) and (#thetap[k[1]] eq 1);
//        assert (j[1] ne k[1]) and (j[1] ne i0) and (k[1] ne i0);
//        SpecialCase:= true;
//        return -1, [[i0,1],j,k], SpecialCase;
//    // if f has an irreducible factor in Qp[t] of degree 2
//        // choose j,k to correspond to the roots of this quadratic factor
//    elif (2 in [#thetap[i] : i in [1..#fprs]]) then
//    // determines the index of the degree 2 linear factor
//        jk:= Index([#thetap[i] : i in [1..#fprs]], 2);  
//        assert #thetap[jk] eq 2;
//        j:= [jk,1];
//        k:= [jk,2];
//        SpecialCase:= true;
    
    
//    jsks:= [[j,jj] : jj in [1..#thetap[j]], j in [1..#thetap] | j ne i0 ];
//    // generates all possible pairs (embeddings) j,k
//    pairs:= [[j,k] : j in jsks, k in jsks | j ne k ];
//    npairs:= [];
//    for jk in pairs do
//        if (jk notin npairs) and ([jk[2],jk[1]] notin npairs) then
//            Append(~npairs, jk);        // removes repetition
//        end if;
//    end for;
//    pairs:=npairs;
//    assert &and[thetap[jk[1][1]][jk[1][2]] ne thetap[jk[2][1]][jk[2][2]] : jk in pairs]; 
    //end if;
end function;







////////////////////////////////////////////////////////////////////////////////
///// OTHER/OLD TESTS/IDEAS FOR NON- ARCHIMEDEAN CASE //////////////////////////


//// theres a possibility that my elements in L may be moving around - should avoid this
//Realprep:= function(L, OL, AutL, Realijk, quad, tl, epslist, prc)
//    K:=NumberField(Universe([quad[1]]));
//    OK:=MaximalOrder(K);
//    th:=K.1;
//    f:=MinimalPolynomial(th); 
//    assert &and[ c in Integers() : c in Coefficients(f) ];
//    assert IsMonic(f);
//    n:=Degree(NumberField(OK));
//    assert n eq Degree(f);
//    tf,mapKL:= IsSubfield(K,L);
//    assert tf;
//    assert (L!th eq mapKL(th)) and (mapKL(th) in tl);
    
//    alpha:= quad[1];
//    gammalist:= quad[2];
//    matA:= quad[3];
//    fplist:= quad[5];
//    quadprimes:= [Norm(fp) : fp in fplist];
//    assert #quadprimes eq #gammalist;
    
//    r:= #epslist;
//    assert r eq 2;
    
//    // apply automorphisms i,j,k: L -> L on the units
//    epslistLi:= [Realijk[1](L!eps) : eps in epslist];
//    epslistLj:= [Realijk[2](L!eps) : eps in epslist];
//    epslistLk:= [Realijk[3](L!eps) : eps in epslist];
//    // apply automorphisms i,j,k: L -> L on the elements gamma of the S-unit equation
//    gammalistLi:= [Realijk[1](L!gamma) : gamma in gammalist];
//    gammalistLj:= [Realijk[2](L!gamma) : gamma in gammalist];
//    gammalistLk:= [Realijk[3](L!gamma) : gamma in gammalist];
       
//    gammafacLi:= [Factorization(ideal<OL|gammaL>) : gammaL in gammalistLi];
//    gammafacLj:= [Factorization(ideal<OL|gammaL>) : gammaL in gammalistLj];
//    gammafacLk:= [Factorization(ideal<OL|gammaL>) : gammaL in gammalistLk];
        
//    // ensure that the prime ideals in L above gamma don't cancel
//    for i in [1..#gammalist] do
//        assert (#gammafacLi[i] eq #gammafacLj[i]) and (#gammafacLj[i] eq #gammafacLk[i]);
//        assert &and[gammafacLi[i][j] ne gammafacLj[i][j] : j in [1..#gammafacLi[i]]];
//        assert &and[gammafacLi[i][j] ne gammafacLk[i][j] : j in [1..#gammafacLi[i]]];
//        assert &and[gammafacLj[i][j] ne gammafacLk[i][j] : j in [1..#gammafacLj[i]]];
//    end for;
        
//    CField<i>:= ComplexField(prc);
//    LintoC:= hom< L -> CField | Conjugates(L.1)[1] >; 
    
//    for i1 in [1..#AutL] do
//        for i2 in [i1 + 1..#AutL] do
//            a:= (AutL[i1])(epslistLj[1]/epslistLi[1]);
//            a:= Log(Abs(LintoC(a)));
            
//            b:= (AutL[i1])(epslistLj[2]/epslistLi[2]);
//            b:= Log(Abs(LintoC(b)));
            
//            c:= (AutL[i2])(epslistLj[1]/epslistLi[1]);
//            c:= Log(Abs(LintoC(c))); 
            
//            d:= (AutL[i2])(epslistLj[2]/epslistLi[2]);
//            d:= Log(Abs(LintoC(d))); 
//            if (a*d - b*c) ne 0 then
//                iotalist:= [i1,i2];
//                break i1;
//            end if;
//        end for;
//    end for;
//    matR:= Matrix(ComplexField(),r,r,[a,b,c,d]);
//    tR, matRinv:= IsInvertible(matR);
//    tA, matAinv:= IsInvertible(matA);
//    assert tR and tA;
//    i1:= iotalist[1];
//    i2:= iotalist[2];
    
//    // iota 1 gammas and iota 2
//    loggammalistLi1:= [ Log(Abs(LintoC( (AutL[i1])(gammalistLj[k]/gammalistLi[k]) ))) : k in [1..#gammalist]];
//    loggammalistLi2:= [ Log(Abs(LintoC( (AutL[i2])(gammalistLj[k]/gammalistLi[k]) ))) : k in [1..#gammalist]];
    
//    wgammalist:= [];
//    for l in [1..r] do
//        wgammalist[l]:= [];
//        for k in [1..#gammalist] do
//            alphalk:= matRinv[l,1]*&+[matAinv[i,k]*loggammalistLi1[i] : i in [1..#gammalist]];
//            alphalk:= alphalk + matRinv[l,2]*&+[matAinv[i,k]*loggammalistLi2[i] : i in [1..#gammalist]];
//            wgammalist[l][k]:= Abs(alphalk)*Degree(K, Rationals())/Log(quadprimes[k]);
//        end for;
//    end for;
            
//    wepslist:= [];
//    for l in [1..r] do
//        wepslist[l]:= [];
//        m:= Max(Abs(matRinv[l,1]), Abs(matRinv[l,2]));
//        for i in [1..#AutL] do
//            if i eq i1 then
//                wepslist[l][i]:= (m+Abs(matRinv[l,1]))*(Degree(L, Rationals()));
//            elif i eq i2 then
//                wepslist[l][i]:= (m+Abs(matRinv[l,2]))*(Degree(L, Rationals()));
//            else
//                wepslist[l][i]:= m*(Degree(L, Rationals()));
//            end if;
//        end for;
//    end for;
    
//    // bound on lin form in log
//    wepslatlist:= [];
//    wgammalatlist:= [];
//    for i in [1..#AutL] do
//        sig:= AutL[i];
//        wepslatlist[i]:= (wepslist[1][i] + wepslist[2][i])/2;
//    end for;
//    for k in [1..#gammalist] do
//        wgammalatlist[k]:= (wgammalist[1][k] + wgammalist[2][k])/2;
//        abar:= &+[Abs(matAinv[j,k]) : j in [1..#gammalist]];
//        wgammalatlist[k]:= wgammalatlist[k] + (Degree(K, Rationals()))/(2*Log(quadprimes[k]))*abar;
//    end for;
        
        
    
//    return wepslist, wgammalist, wepslatlist, wgammalatlist;
//end function;


//Reallattice:= function(L, OL, AutL, Realijk, quad, tl, epslist, h, prc)
//    K:=NumberField(Universe([quad[1]]));
//    OK:=MaximalOrder(K);
//    th:=K.1;
//    f:=MinimalPolynomial(th); 
//    assert &and[ c in Integers() : c in Coefficients(f) ];
//    assert IsMonic(f);
//    n:=Degree(NumberField(OK));
//    assert n eq Degree(f);
//    tf,mapKL:= IsSubfield(K,L);
//    assert tf;
//    assert (L!th eq mapKL(th)) and (mapKL(th) in tl);
    
//    alpha:= quad[1];
//    gammalist:= quad[2];
//    matA:= quad[3];
//    fplist:= quad[5];
//    quadprimes:= [Norm(fp) : fp in fplist];
//    assert #quadprimes eq #gammalist;
    
//    r:= #epslist;
//    assert r eq 2;
    
//    diag:= [ ((Log(p))^2)/Degree(K,Rationals()) : p in quadprimes];
//    matD2:= DiagonalMatrix(ComplexField(), diag);
    



    
//    // compute the bound on |a_l|^2
//    alsquarebound:= [];
//    for l in [1..r] do
//        al1:= 0;
//        for i in [1..#AutL] do
//            al1:= al1 + wepslist[l][i]*h[i];
//        end for;
//        al1:= (1/(Degree(L, Rationals())))*al1;
        
//        al2:= 0;
//        for i in [1..#gammalist] do
//            al2:= al2 + (1/Degree(K, Rationals()))*wgammalist[l][i]*h[#AutL+i];
//        end for;
//        alsquarebound[l]:= (al1 + al2)^2;
//    end for;
        
        
        
        
        
//        lin2bound:= [];
//        for l in [1..r] do
//            if #AutL eq 3 then
//                al1:= (2/(Degree(L, Rationals())))* Max([wsiglist[l][i]*h[i] : i in [1..#AutL]]);
//            else
//                al1:= (1/(Degree(L, Rationals())))* Max([wsiglist[l][i]*h[i] : i in [1..#AutL]]);
//            end if;
//            for i in [1..#gammalist] do
//                al1:= al1 + (1/Degree(K, Rationals()))*wklist[l][i]*h[i];
//            end for;
//            kappa:= 3/2;
            
            
//            al1:= al1 + 1/2 + c*kappa*e^ltau // LEFT OFF HERE   
            
            
//            lin2bound[l]:= al1^2;
//        end for;



Dec:= Decomposition(OL,p);
for fp in Dec do
    fprsL:= fp[1];
    Lp, mLp:= Completion(L, fprsL : Precision:=prec);
    fprs:=Factorisation(p*OK);
    fprs:=[fact[1] : fact in fprs];     // the prime ideals above p
    thetap:=[];
    ths:= [mLp( ijk[i](th)) : i in [1..3]];
    for i in [1..#fprs] do      // runs through each prime ideal above p
        thetap[i]:= [* *];
        Kp, mKp:= Completion(K,fprs[i] : Precision:=prec);
        gp_i:= MinimalPolynomial( mKp(th), PrimeField(Kp));
        gp_i;
        temp:= Roots(gp_i, Lp);   // #temp = degree of gp_i = e_i*f_i
        for j in [1..#temp] do
            thetap[i][j]:= temp[j][1];
        end for;
    end for;
    print thetap;
    print ths;
    print "=====================";
end for;
    
// rearrange ijks so that L!th eq Realijk[1](th) (identity operation)
// ensure that for deg1 prime ideal, we choose the ideal in L above it for fprsL
// is it possible that magma's initial choice of representative for th is the wrong one?
    








////////////////////////////////////////////////////////////////////////////////
///// OTHER/OL TESTS/IDEAS FOR ARCHIMEDEAN CASE ////////////////////////////////

// using symmetry
            center[nu+r,1]:= -alpha0;
            boundForNormSquared:= Ceiling((1+r)*(alphaepslist[r]^2*Bgam*Beps*Bepstar));
            
            
// OLD BOUND THING
            vTv:= (Transpose(vecWtau)*matM*vecWtau)[1,1];
            
            Bound:= Ceiling(Abs( (1+r)*(Bgam*Beps*Bepstar) + vTv ) + 2*Abs(alpha0)*Bgam*Beps*Sqrt(Bepstar));
            //Bound:= (Abs( Bgam + Beps + Bepstar) + vTv ) + 2*Abs(alpha0)*Bepstar*Sqrt(Bepstar);
            NoSol:= 100;
            
            M, z, maxReached:= FinckePohst(matB,Bound,NoSol);
          //  M, z, maxReached:= FinckePohst(matM,Bound,NoSol);
            //M, z, maxReached:= FinckePohst(matM,Integers()! (Abs( (1+r)*(Bgam*Beps*Bepstar))),NoSol);
            #z;
            
        // TEST: new ellipsoid
            matGtau:= IdentityMatrix(Integers(),nu+r+1);
            for i in [1..nu] do
                matGtau[nu+r+1,i+1]:= alphagamlist[i];
            end for;
            for i in [1..r] do
                matGtau[nu+r+1,nu+i+1]:= alphaepslist[i];
            end for;
            matGtau[nu+r+1,1]:= alpha0;
            
            matM:= IdentityMatrix(Integers(),nu+r+1);
            InsertBlock(~matM, (Beps*Bepstar)*(Transpose(matA)*matD*matA), 2, 2);
            //InsertBlock(~matM, (Transpose(matA)*matD*matA), 1, 1); 
            matM[1,1]:= Floor(Bgam);
            matM[nu+2, nu+2]:= Floor(Bgam*Bepstar);
            matM[nu+3, nu+3]:= Floor(Bgam*Beps);
            
            matB:= Transpose(matGtau)*matM*matGtau; 
            Bound:= Ceiling(Abs( (1+1+r)*(Bgam*Beps*Bepstar)));
            //Bound:= (Abs( Bgam + Beps + Bepstar) + vTv ) + 2*Abs(alpha0)*Bepstar*Sqrt(Bepstar);
            NoSol:= 100;
            
            M, z, maxReached:= FinckePohst(matB,Bound,NoSol);
          //  M, z, maxReached:= FinckePohst(matM,Bound,NoSol);
            //M, z, maxReached:= FinckePohst(matM,Integers()! (Abs( (1+r)*(Bgam*Beps*Bepstar))),NoSol);
            #z;
          
   
            // for some reason, the bound T in short vectors becomes negative
            // still can't figure out why we have so many sols though


////////////////////////////////////////////////////////////////////////////////
///// NON ARCHIMEDEAN CASE /////////////////////////////////////////////////////








SmallBoundsCheck:= procedure(fieldKinfo,fieldLinfo,Case,~pCaseInfoList[i],prec);
    K:=fieldKinfo`field;
    OK:=fieldKinfo`ringofintegers;
    th:= fieldKinfo`gen;
    zeta:= fieldKinfo`zeta;
    epslist:= fieldKinfo`fundamentalunits;
    n:= Degree(K);
    
    gammalist:= Case`gammalist;
    fplist:= Case`ideallist;
    alpha:= Case`alpha;
    nu:= #gammalist;
    r:= #epslist;
    
    p:= localpinfo`prime;
    Lp:= localpinfo`Lp;
    thetaL:= localpinfo`thetas;
    mapLL:= localpinfo`mapLL;
    mapLLp:= localpinfo`mapLLp;


    // add conditional function to either do the quick exists or not
    
    tau:=alpha*zeta;
    
    // generate images under the maps ijk: L-> L, th -> theta[i][j]
    tauL:=ImageInL(localpinfo,L!tau);
    gammalistL:= [ImageInL(localpinfo,L!gamma) : gamma in gammalist];
    epslistL:= [ImageInL(localpinfo,L!eps) : eps in epslist];

    // check if we can bound Nail early (Lemma 6.5)
    delta1L:=(thetaL[i0[1]][i0[2]] - thetaL[jj[1]][jj[2]])/(thetaL[i0[1]][i0[2]] - thetaL[kk[1]][kk[2]]);
    delta1L:=delta1L*(tauL[kk[1]][kk[2]]/tauL[jj[1]][jj[2]]);
    delta2L:=(thetaL[jj[1]][jj[2]] - thetaL[kk[1]][kk[2]])/(thetaL[kk[1]][kk[2]] - thetaL[i0[1]][i0[2]]);
    delta2L:=delta2L*(tauL[i0[1]][i0[2]]/tauL[jj[1]][jj[2]]);
    
    pCaseinfo
    
    
    if (Valuation(mapLLp(delta1L)) ne 0) then
        Nail:= Min[Valuation(mapLLp(delta1L)),0] - Valuation(mapLLp(delta2L));
        if Nail ge 0 then
            return Nail,0,
        else
        
        Nail,beta,ihat,dl,delta2
        
            localpinfo`Nail:= -1;
        end if;
    else
        Logdelta1:= pAdicLog(mapLLp(delta1L),p); 
        Loggammalist:=[pAdicLog(mapLLp(gammalistL[i][kk[1]][kk[2]]/gammalistL[i][jj[1]][jj[2]]), p) : i in [1..nu]];
        Logepslist:=[pAdicLog(mapLLp(epslistL[i][kk[1]][kk[2]]/epslistL[i][jj[1]][jj[2]]), p) : i in [1..r]];
        assert (1+#Loggammalist+#Logepslist) eq (1+nu+r);
        
        minval,ihat:= Min([Valuation(eps) : eps in Logepslist]cat[Valuation(gam) : gam in Loggammalist]);
        if ihat le r then
            ihat:= Logepslist[ihat];
        else
            ihat:= Loggammalist[ihat-r];
        end if;
        
        if Valuation(Logdelta1) lt minval then
            Nail:= Max([Floor((1/(p-1) - Valuation(mapLLp(delta2L)))),Ceiling(minval - Valuation(mapLLp(delta2L)))-1]);
            if Nail ge 0 then
                localpinfo`Nail:= Nail;
            else
                localpinfo`Nail:= -1;
            end if;
         // if the program makes it this far, there are no small bounds on Nail
        // arising from Lemma 6.5 and Lemma 6.9
        // hence the code must enter the LLL process to reduce the bounds
    // generates the linear forms in p-adic logs elements for the Special Case
        else
            // assert that we are indeed in the special case, where neither lemma can immediately reduce the bound
            assert &and[-loggam/ihat in pAdicRing(p): loggam in Loggammalist];
            assert &and[-logeps/ihat in pAdicRing(p): logeps in Logepslist];
            assert -Logdelta1/ihat in pAdicRing(p);
            gammabetalist:= [-loggam/ihat : loggam in Loggammalist];
            epsbetalist:= [-logeps/ihat : logeps in Logepslist];
            delta1beta:= -Logdelta1/ihat;
            localpinfo`i0jjkk:= [i0,jj,kk];
            localpinfo`linearpform:= [delta1beta] cat gammabetalist cat epsbetalist;
        end if;
    end if;
           
end function;


ail,beta,ihat,dl,delta2




























            
            
function FinckePohst(B,C,Bound)
//    A:= Transpose(B)*B;         // symmetric, positive-definite matrix B
    A:= B;
    n:= NumberOfColumns(A);     // computes dimension of square input matrix A
    A1:= ZeroMatrix(IntegerRing(),n,n);        // creates matrix A1, intentionally not positive-definite
    A1[2,1]:= -1;      // changes matrix A1 so that it is not symmetric; nb. n >= 2 since S contains at least 3 primes
    prc0:= Integers()!Max( [ Max([ A[i,j] : j in [1..n] ]) : i in [1..n] ] );      // computes the largest integer in the matrix A 
    prc:= Max(100,#IntegerToString(prc0));      // sets precision for the Cholesky decomposition based on the number of digits in the largest integer in the matrix A
    
    while IsSymmetric(A1) eq false do
        R:= Transpose(Cholesky(A, RealField(prc))); // applies Cholesky Decomposition to the input matrix
        t,Ri:= IsInvertible(R);             // computes R^{-1} (easy to compute since R is upper triangular)
        Si,Ui:= LLL(Ri);            // computes row-reduced version S^{-1} of R^{-1}, along with U^{-1}, where S^{-1} = U^{-1}*R^{-1}
        
        t,U:=IsInvertible(Ui);      // computes inverse U of U^{-1}
        S:= R*U;

        norms:= [Sqrt(Norm(Si[i])) : i in [1..n]];        // computes norms of rows of S^{-1}
        order:= Reverse(Sort(norms));                     // sorts norms by decreasing size
        per:= [Index(norms, i) : i in order];       // computes the permutation on (1..n) for which the n rows of S^{-1} have decreasing norms
        for i in [1..n] do                          
            a:=  &+[1: x in per | x eq i];    // counts repetition of index i
            if a gt 1 then                    // corrects repetition in per, ie. in the event any two norms are equal
                for j in [1..a-1] do
                    Ind:= Index(per,i);       // computes index of i in per 
                    per[Index(per[Ind + 1..n],i) + Ind]:= i + 1;    // replaces repeated index, if any
                end for;
            end if;
        end for;    
        
        P:= Transpose(PermutationMatrix(IntegerRing(),per));        // computes the permutation matrix corresponding to the permutation, per
        S1:= S*P;           // rewrites S with columns rearranged by the permutation per, above
        A10:= Transpose(S1)*S1;     // symmetric, positive-definite matrix A1, with entries significantly smaller than those of A
        A1:= Matrix(IntegerRing(),n,n,[IntegerRing()! Round(A10[i][j]) : j in [1..n], i in [1..n]]);        // converts matrix parent (RealField()) of A10 to IntegerRing()
        prc:= prc + 5;  // increases precision on RealField until A1 is Symmetric
    end while;
    
    while IsPositiveDefinite(A1) eq false do
        R:= Transpose(Cholesky(A, RealField(prc))); // applies Cholesky Decomposition to the input matrix
        t,Ri:= IsInvertible(R);             // computes R^{-1} (easy to compute since R is upper triangular)
        Si,Ui:= LLL(Ri);            // computes row-reduced version S^{-1} of R^{-1}, along with U^{-1}, where S^{-1} = U^{-1}*R^{-1}
        
        t,U:=IsInvertible(Ui);      // computes inverse U of U^{-1}
        S:= R*U;

        norms:= [Sqrt(Norm(Si[i])) : i in [1..n]];        // computes norms of rows of S^{-1}
        order:= Reverse(Sort(norms));                     // sorts norms by decreasing size
        per:= [Index(norms, i) : i in order];       // computes the permutation on (1..n) for which the n rows of S^{-1} have decreasing norms
        for i in [1..n] do                          
            a:=  &+[1: x in per | x eq i];    // counts repetition of index i
            if a gt 1 then                    // corrects repetition in per, ie. in the event any two norms are equal
                for j in [1..a-1] do
                    Ind:= Index(per,i);       // computes index of i in per 
                    per[Index(per[Ind + 1..n],i) + Ind]:= i + 1;    // replaces repeated index, if any
                end for;
            end if;
        end for;    
        
        P:= Transpose(PermutationMatrix(IntegerRing(),per));        // computes the permutation matrix corresponding to the permutation, per
        S1:= S*P;           // rewrites S with columns rearranged by the permutation per, above
        A10:= Transpose(S1)*S1;     // symmetric, positive-definite matrix A1, with entries significantly smaller than those of A
        A1:= Matrix(IntegerRing(),n,n,[IntegerRing()! Round(A10[i][j]) : j in [1..n], i in [1..n]]);        // converts matrix parent (RealField()) of A10 to IntegerRing()
        prc:= prc + 5;  // increases precision on RealField until A1 is PositiveDefinite
    end while;
        
    assert IsSymmetric(A1);     // verification that indeed A1 is a symmetric matrix; if false, there is an error in FinckePohst.m
    assert IsPositiveDefinite(A1);      // verification that indeed A1 is a positive definite matrix; if false, there is an error in FinckePohst.m
    
    //maxReached:= false;     // TEMPORARY TEST!!!!!
    //L:= LatticeWithGram(A1);
    //z1:= ShortVectorsMatrix(L,C);
    //delete L;
    //z:= [Matrix(z1[i]) : i in [1..NumberOfRows(z1)]];       // END TEST
    
    z,maxReached:= ShortVectors(A1,C,Bound);     // computes coefficient matrix of lattice points x in L with norm(x) <= C. ie. x*A1*Transpose(x) = [y], where y <= C; maxReached
    M:= U*P;      // computes permutation matrix B*U*P such that y:= Transpose(B*U*P*Transpose(z[i])) is a short lattice vector, for z[i] a short coefficient vector
    
    return M, z, maxReached;    // returns associated lattice matrix, M; short coefficient vectors, z; whether Bound was reached before the algorithm terminated, maxReached
   
end function;
            
for x in z do
    y:= Transpose(M*Transpose(x));
    y*Transpose(y);
end for;
            
            
            
            
        
        // code for now, r = 2
    
    
    alpha:= quad[1];
    gammalist:= quad[2];
    matA:= quad[3];
    fplist:= quad[5];
    quadprimes:= [Norm(fp) : fp in fplist];
    assert #quadprimes eq #gammalist;
    
    r:= #epslist;
    assert r eq 2;
    
   
    
    
    // TEMP lower bound on eps star, c, embedding into C;
    ltau:= Floor(1/2*Log(quadbound));
    assert ltau ge Log(2);
    kappatau:= 3/2;
    c:= 1000;
    taus:= AutL[1]; // we run over all taus
    // then run over all eps
    bepsno:= 1;         // TEMP choice of eps*
    
    bepstar:= (bepstar + (1/2) + c*kappatau*Exp(-ltau))^2;
        
    // pick one l in r to reduce the bound of     
    // for a given l, lowerbound, eps star (??)
     
    
    CField<i>:= ComplexField(prc);
    LintoC:= hom< L -> CField | Conjugates(L.1)[1] >; 
    
    delta1L:= (Realijk[1](L!th) - Realijk[2](L!th))/(Realijk[1](L!th) - Realijk[3](L!th));
    delta1L:= delta1L*(Realijk[3](L!taus*alpha)/Realijk[1](L!tau*alpha));
    
    alpha0:= Round(c*Log(Abs(LintoC(taus(delta1L)))));     // might have to consider what Round is doing here

    alphagam:= [];
    for i in [1..#gammalist] do
        alphagam[i]:= Round(c*Log(Abs(LintoC(taus(Realijk[3](gammalist[i])/Realijk[2](gammalist[i]))))));
    end for;
    
    alphaeps:= [];
    for i in [1..r] do
        alphaeps[i]:= Round(c*Log(Abs(LintoC(taus(Realijk[3](epslist[i])/Realijk[2](epslist[i]))))));
    end for;
    // swap eps so that eps_* is at the end
    Remove(~alphaeps,bepsno);
    alphaeps[r]:= Round(c*Log(Abs(LintoC(taus(Realijk[3](epslist[bepsno])/Realijk[2](epslist[bepsno]))))));
    
    Gam:= IdentityMatrix(Integers(),#gammalist+r);
    for i in [1.. #gammalist] do
        Gam[#gammalist+r,i]:= alphagam[i];
    end for;
    for i in [#gammalist+1..#gammalist + r] do
        Gam[#gammalist+r,i]:= alphaeps[i-#gammalist];
    end for;
            
    // compute matrix D^2
   
    // shit, this is taking logs, so it cannot be an integral matrix
    // in the notes, I need to change the matrix D back to the way it was
        D2:= DiagonalMatrix(ComplexField(), ds);       
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        //wepslist, wgammalist, wepslatlist, wgammalatlist:= Realprep(L, OL, AutL, Realijk, quad, tl, epslist, h, prc);
        
            
            
        
        
        ds:= [ ((Log(p))^2)/Degree(K,Rationals()) : p in plist];
        D2:= DiagonalMatrix(ComplexField(), ds);
        
        
        
        
        
        
        
        D2:= Matrix(ComlpexField(),#gammalist, #gammalist, [ 
         R:= Matrix(ComplexField(),r,r, [a,b,c,d]);
      
        delta1L:= (ijk[1](L!th) - ijk[2](L!th))/(ijk[1](L!th) - ijk[3](L!th));
        delta1L:= delta1L*(ijk[3](L!tau)/ijk[1](L!tau));
        
        
        
        
        
        
            
    
    // then use embeddings into C to embedd elts of L into C;
    // assert that the tls go to the same things as conjugates of th
    // find invertible matrix R in C
    
    // compute betas
    // compute alphas
    
    // compute w's
    // bound on al^2 (using local bound h_sigma?) - beps
    // bound on lin form in log
    // all of this is for the bound to use FP with.
    
    
    // then define matrix
    
    
    
    thetaC:= Conjugates(th);
    assert #thetaC eq n;
    L, tl:= SplittingField(f);
     // choose an embedding of L.1 into C by selecting a conjufate of L.1
    L1C:= Conjugates(L.1)[1]; 
    tlC:= [];
    CField<i>:= ComplexField(prc);
    for j in [1..n] do
        tempf:= hom< K -> CField | L1C[j] >;      
        tlC[j]:= tempf(tl[j]);
    end for;
    
    // determine the preimage in L of thetaC[i] under the embedding L -> C
    ijkC:= [];
    min:=Abs(thetaC[1] - tlC[1]);
    for i in [1..n] do
        if Abs(thetaC[1] - tlC[i]) lt min then
            min:=Abs(thetaC[1] - tlC[i]);
            ijkC[1]:= i;
        end if;
    end for;
    
    min:=Abs(thetaC[2] - tlC[1]);
    for i in [1..n] do
        if Abs(thetaC[2] - tlC[i]) lt min then
            min:=Abs(thetaC[2] - tlC[i]);
            ijkC[2]:= i;
        end if;
    end for;
    
    min:=Abs(thetaC[3] - tlC[1]);
    for i in [1..n] do
        if Abs(thetaC[3] - tlC[i]) lt min then
            min:=Abs(thetaC[3] - tlC[i]);
            ijkC[3]:= i;
        end if;
    end for;

        
        
        
        
        
        
        
        
        
        tauC:= ImageInC(th,thetaC,tau);
        epslistC:= [ImageInC(th,thetaC,eps) : eps in epslist]; 
        gammalistC:= [ImageInC(th,thetaC,gamma) : gamma in gammalist];
        
        
        if r eq 2 then
            delta1C:= (thetaC[1] - thetaC[2])/(thetaC[1] - thetaC[3]);
            delta1C:= delta1C*(tauC[3]/tauC[2]);
            
            delta2C:= (thetaC[2] - thetaC[3])/(thetaC[3] - thetaC[1]);
            delta2C:= delta2C*(tauC[1]/tauC[2]);
            
            
            
            
            
            
        
        // verify that mathfark{P}s dont cancel...?
        // and that the exponents make sense like we did in GESolver 
        
        // choose an embedding of L into C to get invertible matrix R
        
        // define quadratic form qf(n) (and associated matrix)
        
    
    
    
    // DO A THING IF THE LIST OF ALPHGAMMLIST IS EMPTY, ie. 
//    //clist;
//[ 6, 1, 4, 10 ]
//> primelist;
////[ 2, 3, 5, 787 ]

//sig1:= hom< K -> L | tl[2]>;
//> sig1:= hom< K -> L | tl[1]>;
//> sig2:= hom< K -> L | tl[2]>;
//> sig3:= hom< K -> L | tl[3]>;
    
    
    L, tl:= SplittingField(f); 
    printf "Computing the ring of integers of the splitting field...";
    t2:= Cputime();
    OL:= MaximalOrder(L);
    printf "Done! Duration: %o\n", Cputime(t2);
    
    
    
   
    assert #BoundonM + #ideallist eq #afplist;
    printf "Done!\n";
    printf "Reduced number of ideal equations: %o\n", #ideallist;
    
    //SetClassGroupBounds("GRH");      // for testing only; comment out otherwise
    printf "Computing the class group...";
    t1:= Cputime();
    ClK,eta:=ClassGroup(K);
    printf "Done! Duration: %o\n", Cputime(t1);
    h_K:= ClassNumber(K);
    L, tl:= SplittingField(f); 
    printf "Computing the ring of integers of the splitting field...";
    t2:= Cputime();
    OL:= MaximalOrder(L);
    printf "Done! Duration: %o\n", Cputime(t2);
    
    pprecs:= padicprecision(primelist, L);      // estimated required precision 
    Thetaps:= [];
    printf "Computing all roots of f in Cp...";
    t3:= Cputime();
    for i in [1..v] do
        p:=primelist[i];
        fprsL:= Factorisation(p*OL);
        fprsL:= fprsL[1][1];
        prec:= pprecs[i];
        Thetaps[i]:= thetas(th,p,prec,L,fprsL);
    end for;
    printf "Done! Duration: %o\n", Cputime(t3);
    printf "Computing all S-unit equations...";
    t4:= Cputime();
    alphgamlist:=prep2(ideallist,primelist,ClK,eta,h_K);
    printf "Done! Duration: %o\n", Cputime(t4);
    printf "Number of S-unit equations: %o\n", #alphgamlist;
    
        
    printf "Computing the large upper bound on the n_i...";
    t6:= Cputime();
    C10:= UpperBoundm(x,AbsDiscF,n,h_K);
    printf "Done! Duration: %o\n", Cputime(t6);
    printf "Large bound on m: %o\n", C10;
    
    count:= 1;
    for quad in alphgamlist do
        printf "=========================================\n";
        printf "Case: %o\n", count;
        printf "Computing the large upper bound on |a_1|...";
        t7:= Cputime();
        Nails, maxA:= UpperBounda(x,C10,eps,zeta,quad);
        printf "Done! Duration: %o\n", Cputime(t6);
        printf "Large bound on |a_1|: %o\n", maxA;
        alpha:= quad[1];
        matA:= quad[3]; // used to determine the bound on max|n_i|
        rr:= quad[4];
        af:= quad[6];
        tt:= [Valuation(Norm(af), primelist[i]) : i in [1..v]];
        zz:= [Valuation(Norm(ideal<OK|alpha>), primelist[i]) : i in [1..v]];
        assert [tt[i] + rr[i] : i in [1..v]] eq zz;
        Z:= [Valuation(x,primelist[i]) : i in [1..v]];
        rownormA:=RowSumNorm((ChangeRing(matA, Rationals()))^(-1));
        B:= [1] cat [Ceiling(rownormA*Max(Nails)) : i in [1..v]] cat [maxA];
        printf "Current upper bounds: %o\n", B;
        assert #B eq (v+2);
        printf "Starting reduction...\n";
        t8:= Cputime();
        Improvement:= true;
        while Improvement do
            for i in [1..v] do
                p:=primelist[i];
                fprsL:= Factorisation(p*OL);
                fprsL:= fprsL[1][1];
                prec:= pprecs[i];
                thetap:= Thetaps[i];
                Nail:= pLLL(x,prec,L,fprsL,eps,zeta,thetap,quad,B,i);
                if Nail ne -1 then      // else no improvement was made
                    M:= Floor( (Nail+zz[i])/Z[i] ); // updates M            
                    if M lt 3000 then
                        printf "Done reduction! Reduced upper bound on m: %o\n", M;
                        printf "Duration of reduction: %o\n", Cputime(t8);
                        Append(~BoundonM, M);
                        Improvement:= false;
                        break i;
                    else
    // update Nails with new bound M on m
                        Nails:= [M*Z[i]-tt[i]-rr[i] : i in [1..#primelist]];
    // update max|n_i|, hence also B
                        rownormA:=RowSumNorm((ChangeRing(matA, Rationals()))^(-1));                       
                        B:= [1] cat [Ceiling(rownormA*Max(Nails)) : i in [1..v]] cat [maxA];
                        printf "Reduced upper bounds B after reduction step: %o\n", B;
                        printf "Need to reduce further...\n";
                    end if;
                end if;
            end for;
        end while;
        count:= count + 1;
    end for;
    printf "=========================================\n";
    printf "=========================================\n";
        
    printf "Done iterating through all the cases.\n";
    printf "Upper bound on m: %o\n", Max(BoundonM);
    
    printf "Computing all solutions below M: %o ...", Max(BoundonM);
    t9:= Cputime();
    Sol:= finalsol(Floor(Max(BoundonM)),x,deg);
    printf "Done! Duration: %o\n", Cputime(t9);
    printf "All solutions: %o\n", Sol;
    printf "Total running time: %o\n", Cputime(t00);
    return Sol;
end function;
  
