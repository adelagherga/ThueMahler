// TMSolver.m

//============================================================================//
//============================================================================//
/* 

Let S = [p_1,...,p_v] be a set of rational primes p_i and let u be an S-unit. 
This code computes integer solutions of the Thue-Mahler Equation
            f(x,y) = c_1x^3 + c_2x^2y + c_3xy^2 + c_4y^3 = au 
for integers c_i, a such that
                    gcd(x,y) = 1        gcd(c_1,y) = 1.


This algorithm computes solution (x,y) of this equation, and is based on the 
Thue-Mahler algorithm of Tzanakis-de Weger, as well as the work of R. von Känel, 
B. Matschke, and S. Siksek. 

Authors: Adela Gherga, R. von Känel
Last Update: June 21, 2019

Details of this code can be found in the authors' forthcoming paper
"The efficient resolution of Thue-Mahler equations."

//============================================================================//

Remarks:
    This current implementation primarily supports Thue-Mahler equations of 
    degree 3. 

Bottlenecks of this current implementation:
    - 

To Do:
1. precision for real/padic case
2. timing tests

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

ijkAutL:= procedure(fieldKinfo,~fieldLinfo);
    L:= fieldLinfo`field;
    tl:= fieldLinfo`gen;
    th:= fieldKinfo`gen;
    
    G,Aut,tau:= AutomorphismGroup(L);
    assert IsIsomorphic(G, Sym(3)) or IsIsomorphic(G, Alt(3));

    ijk:= [];
    if Order(G.1) eq 3 then     // is G is the alternating group, this is automatically true
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
    assert ijk[3](th) eq L!th; // this is the identity automorphism
    
    fieldLinfo`automorphisms:= AutL;
    fieldLinfo`ijk:= ijk;
    
end procedure;


ComplexFieldInfo:= procedure(fieldKinfo,fieldLinfo,~fieldCinfo);
    th:= fieldKinfo`gen;
    f:= fieldKinfo`minpoly;
    L:= fieldLinfo`field;
    tl:= fieldLinfo`gen;
    ijk:= fieldLinfo`ijk;
    heuristicPrec:= fieldCinfo`precision; 
    
    CField<i>:= ComplexField(heuristicPrec);
    
    // choose an embedding of L.1 into C by selecting a conjugate of L.1
    L1C:= Roots(MinimalPolynomial(L.1), CField)[1][1];
    mapLC:= hom< L -> CField | L1C >;       
    thetaL:= [[ijk[j](L!th)] : j in [1..3]];
    
    // note here that we take ijk as sigma, sigma^2, id
    // it does not matter that ijk corresponds to roots of gp here
    assert #Conjugates(th) eq 3;
    // Conjugates(th) with heuristicPrec
    temp:= [Roots(MinimalPolynomial(th), CField)[j][1] : j in [1..3]]; 
    smallno:= 10^(Floor(-heuristicPrec+10));

    // verify that thetaC is the same as Conjugate(th) with heuristicPrec
    for j in [1..3] do
        vals, ind:= Min([Abs(mapLC(thetaL[k][1]) - temp[j]) : k in [1..3]]);
        assert (vals lt smallno);
    end for;
    
    // verify that thetaL in C are roots of f 
    assert &and[Abs(Evaluate(f,mapLC(thetaL[j][1]))) lt smallno : j in [1..#thetaL]];
   
    mapsLL:= [[ijk[1]], [ijk[2]], [ijk[3]]];
    i0:= [1,1];
    jj:= [2,1];
    kk:= [3,1];
    
    fieldCinfo`idealinL:= L1C;
    fieldCinfo`field:= CField;
    fieldCinfo`mapLLp:= mapLC;
    fieldCinfo`thetaL:= thetaL;
    fieldCinfo`mapsLL:= mapsLL;
    fieldCinfo`i0jk:= [i0,jj,kk];
    
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


UpperBounds:=procedure(fieldKinfo,fieldLinfo,~fieldCinfo,clist,primelist,a,~alphgamlist);
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
    
    L:= fieldLinfo`field;
    PrecMultiplier:= fieldCinfo`precMultiple;
    heuristicPrec:= fieldCinfo`precision;
   
    runningPrecloop:= true;
    while runningPrecloop do
        CField:= fieldCinfo`field;
        mapLC:= fieldCinfo`mapLLp;
        mapsLL:= fieldCinfo`mapsLL;
        thetaL:= fieldCinfo`thetaL;
        i0jk:= fieldCinfo`i0jk;
        
        thetaC:= [mapLC(thetaL[j]) : j in [1..n]];
        assert #thetaC eq 3;
        
        if &or[thC[1] eq CField!0 : thC in thetaC] then // if any thetas get mapped to 0 in C
            fieldCinfo`precMultiple:= (10)*PrecMultiplier;
            ComplexFieldInfo(fieldKinfo,fieldLinfo,~fieldCinfo);
        else
            hth:= (1/n)*&+[Max( Log(Abs(thetaC[j][1])), 0) : j in [1..n]];      // computes the Weil height of theta
            gam:= 2*hth + 2*Log(2) + 4*(2*mS*Log(mS) + 172*hpoly);
            
            alphalistC:= [];
            for j in [1..#alphgamlist] do
                alphaL:= ImageInL(mapsLL,L!alphgamlist[j]`alpha);
                alphaC:= [mapLC(alphaL[k])[1] : k in [1..n]];
                alphalistC:= alphalistC cat alphaC;  // generate image of all alpha in C under mapLC
            end for;
                         
            if &or[alphaC eq CField!0 : alphaC in alphalistC] then // if any alphas are mapped to 0 in C
                PrecMultiplier:= 10*PrecMultiplier;
                heuristicPrec:= Floor(PrecMultiplier*167);
                
                fieldCinfo`precMultiple:= PrecMultiplier;
                fieldCinfo`precision:= heuristicPrec;
                ComplexFieldInfo(fieldKinfo,fieldLinfo,~fieldCinfo);
            else
                runningPrecloop:= false;
            end if;
        end if;
    end while;
    
    for j in [1..#alphgamlist] do
        alphaL:= ImageInL(mapsLL,L!alphgamlist[j]`alpha);
        alphaC:= [mapLC(alphaL[k])[1] : k in [1..n]];
        halpha:= (1/n)*&+[Max( Log(Abs(alphaC[k])), 0) : k in [1..n]];
        alphgamlist[j]`bound:= Ceiling( Degree(K,Rationals())*(gam + 2*halpha) );
    end for;
        
end procedure;

RealLatticePrep:= procedure(fieldKinfo,fieldLinfo,~fieldCvinfo,Case);
    
    K:= fieldKinfo`field;
    OK:= fieldKinfo`ringofintegers;
    th:= fieldKinfo`gen;
    f:= fieldKinfo`minpoly;
    zeta:= fieldKinfo`zeta;
    epslist:= fieldKinfo`fundamentalunits;
    assert Degree(K) eq 3;
    
    L:= fieldLinfo`field;
    OL:= fieldLinfo`ringofintegers;
    tl:= fieldLinfo`gen;
    
    gammalist:= Case`gammalist;
    fplist:= Case`ideallist;
    alpha:= Case`alpha;
    nu:= #gammalist;
    r:= #epslist;
    assert r eq 2;
    
    v:= fieldCvinfo`place;
    PrecMultiplier:= fieldCvinfo`precMultiple;
    heuristicPrec:= Floor(PrecMultiplier*(Log(Case`bound)));
    
    fieldCvinfo`precMultiple:= PrecMultiplier;
    fieldCvinfo`precision:= heuristicPrec;
    ComplexFieldInfo(fieldKinfo,fieldLinfo,~fieldCvinfo);// update precMultiple since it now comes from Log(Case`bound)
 
    runningPrecloop:= true;
    while runningPrecloop do
        CField:= fieldCvinfo`field;
        mapLC:= fieldCvinfo`mapLLp;
        mapsLL:= fieldCvinfo`mapsLL;
        thetaL:= fieldCvinfo`thetaL;
        i0:= fieldCvinfo`i0jk[1];
        jj:= fieldCvinfo`i0jk[2];
        kk:= fieldCvinfo`i0jk[3];
        
        tau:=alpha*zeta;
        // generate images under the maps ijk: L-> L, th -> theta[i][1]
        // here ijk are just sigma, sigma^2, id
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
    
        fieldCvinfo`tauL:= tauL;
        fieldCvinfo`gammalistL:= gammalistL;
        fieldCvinfo`epslistL:= epslistL;
        
        // check if we can bound Nail early (Lemma 6.5)
        delta1L:=(thetaL[i0[1]][i0[2]] - thetaL[jj[1]][jj[2]])/(thetaL[i0[1]][i0[2]] - thetaL[kk[1]][kk[2]]);
        delta1L:=delta1L*(tauL[kk[1]][kk[2]]/tauL[jj[1]][jj[2]]);
        delta1Cv:= mapLC(v(delta1L));   // apply auto v:L -> L, then map into C
        delta2L:=(thetaL[jj[1]][jj[2]] - thetaL[kk[1]][kk[2]])/(thetaL[kk[1]][kk[2]] - thetaL[i0[1]][i0[2]]);
        delta2L:=delta2L*(tauL[i0[1]][i0[2]]/tauL[jj[1]][jj[2]]);
        delta2Cv:= mapLC(v(delta2L));    // apply auto v:L -> L, then map into C
        
        Logdelta1:= Log(Abs(delta1Cv));
        Loggammalist:=[Log(Abs(mapLC(v( gammalistL[i][kk[1]][kk[2]]/gammalistL[i][jj[1]][jj[2]] )))) : i in [1..nu]];
        Logepslist:=[Log(Abs(mapLC(v( epslistL[i][kk[1]][kk[2]]/epslistL[i][jj[1]][jj[2]] )))) : i in [1..r]];
        LogList:= Loggammalist cat Logepslist;
        assert #LogList eq (nu+r);
        
        // assert things don't get mapped to 0 in C
        if (delta1Cv eq CField!0) or (delta2Cv eq CField!0) or &or[LogList[i] eq CField!0 : i in [1..nu+r]] then
            PrecMultiplier:= (1.3)*PrecMultiplier;
            heuristicPrec:= Floor(PrecMultiplier*(Log(Case`bound)));  // restart with higher precision
            
            fieldCvinfo`precMultiple:= PrecMultiplier;
            fieldCvinfo`precision:= heuristicPrec;
            ComplexFieldInfo(fieldKinfo,fieldLinfo,~fieldCvinfo);
        else
            runningPrecloop:= false;
        end if;
        
    end while;

    fieldCvinfo`delta1L:= delta1L;
    fieldCvinfo`delta2L:= delta2L;
    fieldCvinfo`delta1Lp:= delta1Cv;
    fieldCvinfo`delta2Lp:= delta2Cv;
    fieldCvinfo`betalist:= [*Logdelta1,Loggammalist,Logepslist*];
    fieldCvinfo`precision:= heuristicPrec;  
    fieldCvinfo`precMultiple:= PrecMultiplier;  
             
end procedure;   


Ellipsoid:= function(fieldKinfo,fieldLinfo,fieldCinfo,Case,Localinfo,HeightBounds: Place:="NonArch");

    K:= fieldKinfo`field;
    L:= fieldLinfo`field;
    AutL:= fieldLinfo`automorphisms;
    
    CasePrimes:= [Norm(fp) : fp in Case`ideallist];
    matA:= Case`matA;
    HeightBoundonGammalist:= HeightBounds`heightgammalist;
    HeightBoundonEpslist:= HeightBounds`heightepslist;
    
    //print "Ellipsoid HeightBounds", HeightBoundonGammalist, HeightBoundonEpslist;
    
    tauL:= Localinfo`tauL;
    gammalistL:= Localinfo`gammalistL;
    epslistL:= Localinfo`epslistL;
    ijk:= Localinfo`i0jk;
    
    nu:= #gammalistL;
    r:= #epslistL;
       
    i0:= ijk[1];
    jj:= ijk[2];
    kk:= ijk[3];
    assert nu eq #Case`gammalist;
    assert nu eq #CasePrimes;
    assert r eq #fieldKinfo`fundamentalunits;
    
    mapLC:= fieldCinfo`mapLLp;
    PrecMultiplier:= fieldCinfo`precMultiple;
    heuristicPrec:= fieldCinfo`precision;
    
    runningPrecloop:= true;
    while runningPrecloop do
        mapLC:= fieldCinfo`mapLLp;
        CField:= fieldCinfo`field;
    
        for i1 in [1..#AutL] do
            for i2 in [i1 + 1..#AutL] do
                a:= (AutL[i1])(epslistL[1][jj[1]][jj[2]]/epslistL[1][i0[1]][i0[2]]);
                a:= Log(Abs(mapLC(a)));
                
                b:= (AutL[i1])(epslistL[2][jj[1]][jj[2]]/epslistL[2][i0[1]][i0[2]]);
                b:= Log(Abs(mapLC(b)));
                
                c:= (AutL[i2])(epslistL[1][jj[1]][jj[2]]/epslistL[1][i0[1]][i0[2]]);
                c:= Log(Abs(mapLC(c))); 
                
                d:= (AutL[i2])(epslistL[2][jj[1]][jj[2]]/epslistL[2][i0[1]][i0[2]]);
                d:= Log(Abs(mapLC(d))); 
                if (a*d - b*c) ne 0 then
                    iotalist:= [i1,i2];
                    break i1;
                end if;
            end for;
        end for;
        
        matR:= Matrix(CField,2,2,[a,b,c,d]);
        tR, matRinv:= IsInvertible(matR);
        tA, matAinv:= IsInvertible(matA);
        assert tR and tA;
        i1:= iotalist[1];
        i2:= iotalist[2];
        
        // compute iota 1 gammas and iota 2 in definition of wgamlklist
        gamlistLi1:= [ mapLC( (AutL[i1])(gammalistL[k][jj[1]][jj[2]]/gammalistL[k][i0[1]][i0[2]]) ) : k in [1..nu]];
        gamlistLi2:= gamlistLi1 cat [ mapLC( (AutL[i2])(gammalistL[k][jj[1]][jj[2]]/gammalistL[k][i0[1]][i0[2]]) ) : k in [1..nu]];
       
        if &or[gamLi1 eq CField!0 : gamLi1 in gamlistLi1] then // if any alphas are mapped to 0 in C
            PrecMultiplier:= 10*PrecMultiplier;
            heuristicPrec:= Floor(PrecMultiplier*167);
            
            fieldCinfo`precMultiple:= PrecMultiplier;
            fieldCinfo`precision:= heuristicPrec;
            ComplexFieldInfo(fieldKinfo,fieldLinfo,~fieldCinfo);
        else
            runningPrecloop:= false;
        end if;
    end while;
             
    // compute iota 1 gammas and iota 2 in definition of wgamlklist
    logamlistLi1:= [ Log(Abs(mapLC( (AutL[i1])(gammalistL[k][jj[1]][jj[2]]/gammalistL[k][i0[1]][i0[2]]) ))) : k in [1..nu]];
    logamlistLi2:= [ Log(Abs(mapLC( (AutL[i2])(gammalistL[k][jj[1]][jj[2]]/gammalistL[k][i0[1]][i0[2]]) ))) : k in [1..nu]];
    
    // compute the coefficients w_{gam,l,k} in the bound for Beps
    wgamlklist:= [];
    for l in [1..r] do
        wgamlklist[l]:= [];
        for k in [1..nu] do
            alphagamlk:= matRinv[l,1]*(&+[matAinv[i][k]*logamlistLi1[i] : i in [1..nu]]); 
            alphagamlk:= alphagamlk + matRinv[l,2]*(&+[matAinv[i][k]*logamlistLi2[i] : i in [1..nu]]);
            wgamlklist[l][k]:= Abs(alphagamlk)/Log(CasePrimes[k]);
        end for;
    end for;
    
    // compute the coefficients w_{eps,l,k} in the bound for Beps
    if #AutL eq 6 then
        b:= 2;
    elif #AutL eq 3 then
        b:= 1;
    end if;
    wepsllist:= [];
    for l in [1..r] do
        m:= Max(Abs(matRinv[l,1]), Abs(matRinv[l,2]));
        wepsllist[l]:= (b+1)*m;
    end for;
        
    Bgam:= Ceiling((1/Log(2)^2)*&+[ h^2 : h in HeightBoundonGammalist]);
    
   // print "wepsllist", wepsllist;
   // print "wgamlklist", wgamlklist;
    
    // compute bound b_eps; since r = 2, there is only 1 such b_eps where eps =! eps^*
        // choose eps^* = epslist[2]; hence l = 1 here
    Beps:= [];
    for l in [1..r] do
        Beps[l]:= &+[HeightBoundonGammalist[k]*wgamlklist[l][k] : k in [1..nu]];
        Beps[l]:= (Beps[l] + wepsllist[l]*Degree(L,Rationals())*Max(HeightBoundonEpslist))^2;
    end for;
     
    if Place eq "Real" then
        // bound on lin form in log
        wepslat:= (wepsllist[1] + wepsllist[2])/2;
        wgamlatlist:= [];
        for k in [1..nu] do
            abar:= &+[Abs(matAinv[j,k]) : j in [1..nu]];
            wgamlatlist[k]:= (wgamlklist[1][k] + wgamlklist[2][k])/2 + abar/(2*Log(CasePrimes[k]));
        end for;
    
        // compute bound b_eps^*; since r = 2, there is only 1 such b_eps where eps =! eps^*
        // choose eps^* = epslist[2]; hence l = 2 here// default to last element of Beps
        Beps[r]:= &+[HeightBoundonGammalist[k]*wgamlatlist[k] : k in [1..nu]];
        Beps[r]:= Beps[r] + wepslat*Degree(L,Rationals())*Max(HeightBoundonEpslist) + 1/2;
        // add the ck_taue^{-l_t} outside of this function
    end if;
        
    return Bgam,Beps;
end function;


RealLattice:= function(fieldCvinfo,Case,Bgam,BepsList,mu);
    
    v:= fieldCvinfo`place;
    CField:= fieldCvinfo`field;
    Logdelta1:= fieldCvinfo`betalist[1];
    Loggammalist:= fieldCvinfo`betalist[2];
    Logepslist:= fieldCvinfo`betalist[3];
    CasePrimes:= [Norm(fp) : fp in Case`ideallist];
    matA:= Case`matA;
   
    r:= #Logepslist;
    nu:= #Loggammalist;
    
     // generate matrix M^TM
    matD:= DiagonalMatrix(Integers(), [ Floor(Log(p)^2/Log(2)^2) : p in CasePrimes]); 
    matM:= IdentityMatrix(Integers(),nu+r);
    InsertBlock(~matM, (&*[Ceiling(BepsList[l]) : l in [1..r]])*(Transpose(matA)*matD*matA), 1, 1);
    for l in [1..r] do
        matM[nu+l,nu+l]:= Bgam*(&*[Ceiling(BepsList[k]) : k in [1..r] | k ne l]);
    end for;
    
    betalist:= [Round(mu*Loggam) : Loggam in Loggammalist] cat [Round(mu*Logeps) : Logeps in Logepslist];
    beta1:= Round(mu*Logdelta1);
    
     // define matrix
    matAm:= IdentityMatrix(Rationals(), (nu+r));
    for i in [1..nu+r] do
        matAm[nu+r,i]:= betalist[i];
    end for;
     // generates Transpose(matB)*matB
    matBtmatB:= Transpose(matAm)*matM*matAm;
    
    vecc:= ZeroMatrix(Rationals(), nu+r, 1);
    vecc[nu+r,1]:= -beta1/betalist[r];
    
    boundForNormSquared:= Ceiling((1+r)*(Bgam*&*BepsList));
    
    return matBtmatB, vecc, boundForNormSquared;
 
end function;


// padic reduction procedures and functions
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

pAdicLatticePrep:= procedure(fieldKinfo,fieldLinfo,~fieldLpinfo,Case);

    K:= fieldKinfo`field;
    OK:= fieldKinfo`ringofintegers;
    th:= fieldKinfo`gen;
    f:= fieldKinfo`minpoly;
    zeta:= fieldKinfo`zeta;
    epslist:= fieldKinfo`fundamentalunits;
    assert Degree(K) eq 3;
    
    L:= fieldLinfo`field;
    OL:= fieldLinfo`ringofintegers;
    ijkL:= fieldLinfo`ijk;
    
    gammalist:= Case`gammalist;
    fplist:= Case`ideallist;
    alpha:= Case`alpha;
    nu:= #gammalist;
    r:= #epslist;
    
    p:= fieldLpinfo`place;
    PrecMultiplier:= fieldLpinfo`precMultiple;
    // iniital precision heuristic
    heuristicPrec:= Floor(PrecMultiplier*(Log(Case`bound)));        // placeholder
    idealinL:= fieldLpinfo`idealinL;
    
    runningPrecloop:= true;
    while runningPrecloop do
        Lp, mapLLp:= Completion(L, idealinL : Precision:= heuristicPrec);
        fieldLpinfo`field:= Lp;
        fieldLpinfo`mapLLp:= mapLLp;
        
        fprs:=[f[1] : f in Factorisation(p*OK)];        // the prime ideals above p

        thetaL:=[];
        mapsLL:=[]; 
        for i in [1..#fprs] do      // runs through each prime ideal above p
            thetaL[i]:=[];
            mapsLL[i]:=[];       // the preimage of thetap in L 
                                        // ie. for th in L, mLp(ijk(th)) is one of the thetap in Lp 
            Kp, mKp:= Completion(K,fprs[i] : Precision:= heuristicPrec);
            gp_i:= MinimalPolynomial( mKp(th), PrimeField(Kp));
            temp:= Roots(gp_i, Lp);   // #temp = degree of gp_i = e_i*f_i
            for j in [1..#temp] do
                vals, ind:= Max([Valuation(mapLLp(ijkL[k](L!th)) - temp[j][1]) : k in [1..3]]);
                mapsLL[i][j]:= ijkL[ind];        // mLp(ijk[i][j](th)) maps to thetap[i][j]
                thetaL[i][j]:= ijkL[ind](L!th);
            end for;
        end for;
        
        assert Degree(K) eq &+[#thetaL[i] : i in [1..#fprs]];       // check we have the correct number of thetas
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
        fieldLpinfo`thetaL:= thetaL;
        fieldLpinfo`mapsLL:= mapsLL;

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
        fieldLpinfo`i0jk:= [i0,jj,kk];

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
        
        fieldLpinfo`tauL:= tauL;
        fieldLpinfo`gammalistL:= gammalistL;
        fieldLpinfo`epslistL:= epslistL;
        
        // check if we can bound Nail early (Lemma 6.5)
        delta1L:=(thetaL[i0[1]][i0[2]] - thetaL[jj[1]][jj[2]])/(thetaL[i0[1]][i0[2]] - thetaL[kk[1]][kk[2]]);
        delta1L:=delta1L*(tauL[kk[1]][kk[2]]/tauL[jj[1]][jj[2]]);
        delta1Lp:= mapLLp(delta1L);
        delta2L:=(thetaL[jj[1]][jj[2]] - thetaL[kk[1]][kk[2]])/(thetaL[kk[1]][kk[2]] - thetaL[i0[1]][i0[2]]);
        delta2L:=delta2L*(tauL[i0[1]][i0[2]]/tauL[jj[1]][jj[2]]);
        delta2Lp:= mapLLp(delta2L);
        
        fieldLpinfo`delta1L:= delta1L;
        fieldLpinfo`delta2L:= delta2L;
        fieldLpinfo`delta1Lp:= delta1Lp;
        fieldLpinfo`delta2Lp:= delta2Lp;
              
        if (Valuation(delta1Lp) eq 0) then
            cp:= Log(p)*(Max(1/(p-1),Valuation(delta1Lp)) - Valuation(delta2Lp));
            if heuristicPrec lt cp then
                PrecMultiplier:= (1.3)*PrecMultiplier;
                heuristicPrec:= Floor(PrecMultiplier*(Log(Case`bound)));  // restart loop with higher precision
            else
                runningPrecloop:= false;        // exit loop after the following commands
                Logdelta1:= pAdicLog(delta1Lp,p); 
                Loggammalist:=[pAdicLog(mapLLp(gammalistL[i][kk[1]][kk[2]]/gammalistL[i][jj[1]][jj[2]]), p) : i in [1..nu]];
                Logepslist:=[pAdicLog(mapLLp(epslistL[i][kk[1]][kk[2]]/epslistL[i][jj[1]][jj[2]]), p) : i in [1..r]];
                LogList:= Loggammalist cat Logepslist;
                assert #LogList eq (nu+r);
        
                minval,ihat:= Min([Valuation(LogList[i]) :i in [1..nu+r]]);
                if (Valuation(Logdelta1) ge minval) then
                    // if the program makes it this far, there are no small bounds on Nail
                    // arising from Lemma 6.5 and Lemma 6.9
                    // hence the code must enter the FP process to reduce the bounds
                    // generates the linear forms in p-adic logs elements for the Special Case
                        
                    logihat:= LogList[ihat];  // offset the first term, Logdelta1
                    betalist:= [-LogList[i]/logihat : i in [1..nu+r]];
                    // assert that we are indeed in the special case, where neither lemma can immediately reduce the bound
                    beta1:= -Logdelta1/logihat;
                    assert &and[beta in pAdicRing(p) : beta in betalist] and (beta1 in pAdicRing(p));
                    
                    fieldLpinfo`ihat:= ihat;
                    fieldLpinfo`logihat:= logihat;
                    fieldLpinfo`betalist:= [*beta1,betalist*];
                    fieldLpinfo`precision:= heuristicPrec;  
                    fieldLpinfo`precMultiple:= PrecMultiplier;  
                                       
                else // Lemma 2 holds; early bound
                    smallbound:= Max([Floor((1/(p-1) - Valuation(delta2Lp))),Ceiling(minval - Valuation(delta2Lp))-1]);
                    if smallbound ge 0 then
                        fieldLpinfo`smallbound:= smallbound;
                    else
                        fieldLpinfo`smallbound:= -1;     // negative bound; Case can be removed
                    end if;
                    
                end if;
            end if;
        else        //Lemma holds; (Valuation(delta1Lp) ne 0), early bound
            smallbound:= Min[Valuation(delta1Lp),0] - Valuation(delta2Lp);
            if smallbound ge 0 then
                fieldLpinfo`smallbound:= smallbound;
            else
                fieldLpinfo`smallbound:= -1;     // negative bound; Case can be removed
            end if;
            runningPrecloop:= false;    // exit loop
        end if;
        
    end while;
end procedure;

CheckpAdicPrecision:= procedure(fieldKinfo,fieldLinfo,~fieldLpinfo,Case,mu,cp);
    p:= fieldLpinfo`place;
    ijkLp:= fieldLpinfo`i0jk;
    precision:= fieldLpinfo`precision;
    
    while (mu+100) gt precision do       // recompute deltas with new pAdicPrec:= 3*mu
        //print "+1";
        fieldLpinfo`precMultiple:= (1.3)*fieldLpinfo`precMultiple;
        pAdicLatticePrep(fieldKinfo, fieldLinfo,~fieldLpinfo,Case);
        precision:= fieldLpinfo`precision;
        delta1Lp:= fieldLpinfo`delta1Lp;
        delta2Lp:= fieldLpinfo`delta2Lp;
        
        // assert that i0,j,k has not changed
        assert fieldLpinfo`i0jk eq ijkLp;  
        // assert that cp has not changed
        assert cp eq Log(p)*(Max(1/(p-1),Valuation(delta1Lp)) - Valuation(delta2Lp));
    end while;
    assert ((mu+100) le precision);
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

pAdicLattice:= function(fieldLpinfo,Case,Bgam,BepsList,mu);
    
    p:= fieldLpinfo`place;
    Lp:= fieldLpinfo`field;
    beta1:= fieldLpinfo`betalist[1];
    betalist:= fieldLpinfo`betalist[2];
    ihat:= fieldLpinfo`ihat;
    PrecMultiplier:= fieldLpinfo`precMultiple;
    precision:= fieldLpinfo`precision;
    CasePrimes:= [Norm(fp) : fp in Case`ideallist];
    matA:= Case`matA;
    
    //matM,Bgam,Bepslist:= Ellipsoid(fieldLinfo,Case,Localinfo,HeightBounds,RealPrec);
    r:= #BepsList;
    nu:= #CasePrimes;
    
     // generate matrix M^TM
    matD:= DiagonalMatrix(Integers(), [ Floor(Log(p)^2/Log(2)^2) : p in CasePrimes]); 
    matM:= IdentityMatrix(Integers(),nu+r);
    InsertBlock(~matM, (&*[Ceiling(BepsList[l]) : l in [1..r]])*(Transpose(matA)*matD*matA), 1, 1);
    for l in [1..r] do
        matM[nu+l,nu+l]:= Bgam*(&*[Ceiling(BepsList[k]) : k in [1..r] | k ne l]);
    end for;
    
    //assert &and[mu le Precision(beta) : be
    betalist:= [pInteger(Lp,p,mu,precision,beta) : beta in betalist];
    // asserts that beta_ihat = -alpha_ihat/alpha_ihat = -1
    assert (betalist[ihat] eq (p^mu)-1);
    
    betalist[ihat]:= p^mu;
    beta1:= pInteger(Lp,p,mu,precision,beta1);
    
    // define matrix
    matAm:= IdentityMatrix(Rationals(), (nu+r));
    for i in [1..nu+r] do
        matAm[ihat,i]:= betalist[i];
    end for;
    assert matAm[ihat,ihat] eq p^mu;
    
    vecw:= ZeroMatrix(Rationals(), nu+r, 1);
    vecw[ihat,1]:= beta1;
    
    // generates Transpose(matB)*matB
    matBtmatB:= Transpose(matAm)*matM*matAm;
    
    vecc:= ZeroMatrix(Rationals(), nu+r, 1);
    vecc[ihat,1]:= -beta1/p^mu;
    boundForNormSquared:= Ceiling((1+r)*(Bgam*&*BepsList));
   
    return matBtmatB, vecc, boundForNormSquared, matAm,vecw;
 
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


// LEFT OFF HERE; NEED TO TEST THIS CONVERSION OF SOLUTIONS TO SAMIRS;
// ALSO NEED TO TEST OUT WHAT HAPPENS to reduction
// include Samir's sieve at the end
infNorm:= function(HeightBounds,Case,allBeps);
    
    CasePrimes:= [Norm(fp) : fp in Case`ideallist];
    nu:= #Case`gammalist;
    assert #CasePrimes eq nu;
    
    VectorInfNorm:= Max([HeightBounds`heightgammalist[i]/Log(CasePrimes[i]) : i in [1..nu]]);
    
    // compute the infinity norm of matAinv (max row sum)
    matA:= Case`matA;
    tf,matAinv:= IsInvertible(matA);
    assert tf;
    
    n:= NumberOfRows(matAinv);
    RowSum:= [];
    for i in [1..n] do
        RowSum[i]:=  &+[Abs(matAinv[i,j]) : j in [1..n]];
    end for;
    MatrixInfNorm:= Max(RowSum);
    
    nBound:= MatrixInfNorm*VectorInfNorm;
    
    // bound on a;
    aBound:= [];
    aBound[1]:= Ceiling(Min([Sqrt(allBeps[i][1]) : i in [1..#allBeps]]));
    aBound[2]:= Ceiling(Min([Sqrt(allBeps[i][2]) : i in [1..nu]]));
    
    return Ceiling(nBound),Max(aBound);
end function;



pAdicSolutionTest:= function(fieldKinfo,Case, sol);
    K:= fieldKinfo`field;
    OK:= fieldKinfo`ringofintegers;
    th:= fieldKinfo`gen;
    zeta:= fieldKinfo`zeta;
    epslist:= fieldKinfo`fundamentalunits;
    assert Degree(K) eq 3;
    
    gammalist:= Case`gammalist;
    fplist:= Case`ideallist;
    alpha:= Case`alpha;
    nu:= #gammalist;
    r:= #epslist;
    assert r eq 2;
  
    tau:= alpha*zeta;
    candidateSol:= [];
    for y in sol do
        z:= tau*&*[gammalist[i]^(Integers()!y[1,i]) : i in [1..nu]]*epslist[1]^(Integers()!y[1,nu+1])*epslist[2]^(Integers()!y[1,nu+2]);    
        if z[3] eq 0 then
            Append(~candidateSol,[*y,z*]);
        end if;
        y2:= -y;
        z:= tau*&*[gammalist[i]^(Integers()!y2[1,i]) : i in [1..nu]]*epslist[1]^(Integers()!y2[1,nu+1])*epslist[2]^(Integers()!y2[1,nu+2]);    
        if z[3] eq 0 then
            Append(~candidateSol,[*y2,z*]);
        end if;
    end for;
   
    return candidateSol;
end function;




// procedure starts here
ReductionIteration:= procedure(fieldKinfo,fieldLinfo,fieldCinfo,~LocalinfoList,Case,HeightBounds,~NewHeightBounds: iterationNo:= 1);

    CasePrimes:= [Norm(fp) : fp in Case`ideallist];
    nu:= #Case`gammalist;
    assert #CasePrimes eq nu;
    r:= #fieldKinfo`fundamentalunits;
    stillEnumerating:= true;
    candidateVectors:= [];
       
    iterationNo:= 0;
    while stillEnumerating do
        iterationNo:= iterationNo + 1;
 
        allBeps:= [];
        for i in [1..nu] do
            p:= LocalinfoList[i]`place;
            hp:= HeightBounds`heightgammalist[i];
            pAdicLatticePrep(fieldKinfo, fieldLinfo,~LocalinfoList[i], Case);   
            
            if assigned LocalinfoList[i]`smallbound then
                print "Small bound met: still need to add code for this";
            ///////////////////////////////////////////////////
            ///// check if smallbound is met ///////////////////
            ////////////////////////////////////////////////////// 
            end if;
            
            delta1Lp:= LocalinfoList[i]`delta1Lp;
            delta2Lp:= LocalinfoList[i]`delta2Lp;
            logihat:= LocalinfoList[i]`logihat;
            cp:= Log(p)*(Max(1/(p-1),Valuation(delta1Lp)) - Valuation(delta2Lp));
            lp:= Max(cp,10*Log(hp)); // heuristic for initial value of lv; lv >= cp
            mu:= Floor(lp/Log(p) - Valuation(logihat) + Valuation(delta2Lp));
            
            assert mu gt (Valuation(delta2Lp) - Valuation(logihat));
            assert (cp le lp) and (lp lt hp);
            assert (hp gt Max(0,cp));
            CheckpAdicPrecision(fieldKinfo,fieldLinfo,~LocalinfoList[i],Case,mu,cp);
            // redifine constants (with better precision)
            delta1Lp:= LocalinfoList[i]`delta1Lp;
            delta2Lp:= LocalinfoList[i]`delta2Lp;
            logihat:= LocalinfoList[i]`logihat;
            
            // we now should have high enough precision to keep rum through FP at least once
            Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i],HeightBounds: Place:="NonArch");
            matBtmatB, vecc, boundForNormSquared,matAm,vecw:= pAdicLattice(LocalinfoList[i],Case,Bgam,BepsList,mu);
            bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
            
            // initial reduction to ensure that lp is chosen so that no solutions appear
                // increase lv until there are no solutions or lp is no longer in range and (Max(0,cp) lt lv) and (lv lt hp)
            while (#solutionsList ne 0) do
                lp:= lp*(1.3);        // increase lv
                mu:= Floor(lp/Log(p) - Valuation(logihat) + Valuation(delta2Lp)); // recompute mu
                if mu le (Valuation(delta2Lp) - Valuation(logihat)) then
                    print "mu is smaller than would allow";
                    stillEnumerating:= false;
                    break i;
                end if;
                assert mu gt (Valuation(delta2Lp) - Valuation(logihat));
                if (cp gt lp) or (lp gt hp) then
                    lp:= hp - Log(p);   // decrease lp by Log(p); equivalently decreases mu by 1
                    mu:=Floor(lp/Log(p) - Valuation(logihat) + Valuation(delta2Lp)); // recompute mu
                    Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i],HeightBounds: Place:="NonArch");
                    matBtmatB, vecc, boundForNormSquared,matAm,vecw:= pAdicLattice(LocalinfoList[i],Case,Bgam,BepsList,mu);
                    bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
                    if (#solutionsList ne 0) then // highly unlikey to happen in very first iteration, but possible in later iterations
                        print "solutions found - no smaller lp possible; shouldn't update hp then...", p;
                        stillEnumerating:= false;
                        break i;    // exits iteration over non-archimedean places
                    end if;
                end if;
                
                assert (cp le lp) and (lp lt hp);
                // ensure that precision is high enough
                CheckpAdicPrecision(fieldKinfo,fieldLinfo,~LocalinfoList[i],Case,mu,cp);
                
                Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i],HeightBounds: Place:="NonArch");
                matBtmatB, vecc, boundForNormSquared,matAm,vecw:= pAdicLattice(LocalinfoList[i],Case,Bgam,BepsList,mu);
                bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
            end while; // exits when lp is found such that there are no solutions
            
            assert bufferWasBigEnough and (#solutionsList eq 0);
            NewHeightBounds`heightgammalist[i]:= Ceiling(lp);
            allBeps[i]:= BepsList;
        end for;

        if stillEnumerating then
        // archimedean places
            for i in [1..#fieldLinfo`ijk] do      //[1..#AutL] do // just need to run through i0,j,k
                v:= LocalinfoList[i+nu]`place;      // this corresponds to i0,j,k
                hv:= HeightBounds`heightepslist[i];
                RealLatticePrep(fieldKinfo,fieldLinfo,~LocalinfoList[i+nu],Case);        
                
                // ensure that v is the correct automorphism of i0,jk,
                assert v eq LocalinfoList[i+nu]`mapsLL[LocalinfoList[i+nu]`i0jk[i][1]][LocalinfoList[i+nu]`i0jk[i][2]];
                delta1Cv:= LocalinfoList[i+nu]`delta1Lp;
                delta2Cv:= LocalinfoList[i+nu]`delta2Lp;
                cv:= Log(Max( 2*Abs(delta2Cv),1 ));
                lv:= Max([Log(2),cv,10*Log(hv)]); // heuristic for initial value of lv; lv >= cp
                mu:= Exp(lv);
                
                assert mu gt 0;
                assert (cv le lv) and (lv lt hv);
                assert hv gt cv;
                
                Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i+nu],HeightBounds: Place:="Real");
                BepsList[r]:= (BepsList[r] + mu*(3/2)*Exp(-lv))^2;
                matBtmatB, vecc, boundForNormSquared:= RealLattice(LocalinfoList[i+nu],Case,Bgam,BepsList,mu);
                bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
                
                // increase lv until there are no solutions or lp is no longer in range and (Max(0,cp) lt lv) and (lv lt hp)
                while (#solutionsList ne 0) do
                    lv:= lv*(1.3);        // increase lv
                    mu:= Exp(lv);
                    if (cv gt lv) or (lv gt hv) then
                        lv:= hv - 1;
                        mu:= Exp(lv);    // recompute mu
                        Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i+nu],HeightBounds: Place:="Real");
                        BepsList[r]:= (BepsList[r] + mu*(3/2)*Exp(-lv))^2;
                        matBtmatB, vecc, boundForNormSquared:= RealLattice(LocalinfoList[i+nu],Case,Bgam,BepsList,mu);
                        bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
                        if (#solutionsList ne 0) then // highly unlikey to happen in very first iteration, but possible in later iterations
                            print "solutions found - no smaller lv possible; shouldn't update hv then...", i, lv;
                            stillEnumerating:= false;
                            break i;        // exits iteration over archimedean places 
                        end if;
                    end if;
                    assert mu gt 0;
                    assert (cv le lv) and (lv lt hv);
                    
                    Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i+nu],HeightBounds: Place:="Real");
                    BepsList[r]:= (BepsList[r] + mu*(3/2)*Exp(-lv))^2;
                    matBtmatB, vecc, boundForNormSquared:= RealLattice(LocalinfoList[i+nu],Case,Bgam,BepsList,mu);
                    bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
                end while; // exits when lp is found such that there are no solutions
                
            
                assert bufferWasBigEnough and (#solutionsList eq 0);
                NewHeightBounds`heightepslist[i]:= Ceiling(lv);
                allBeps[nu+i]:= [BepsList[1],-1];

            end for;
        end if;
         
        // if stillEnumerating eq false    // nothing to change in this case, revert to HeightBounds (ie. don't update HeightBounds with NewHeightBounds)
        if stillEnumerating then
            if (NewHeightBounds`heightgammalist eq HeightBounds`heightgammalist) and (NewHeightBounds`heightepslist eq HeightBounds`heightepslist) then
                stillEnumerating:= false;
            else
                HeightBounds:= NewHeightBounds;
                nBound, aBound:= infNorm(HeightBounds,Case,allBeps);
                HeightBounds`infheight:= [nBound, aBound];
            end if;
        end if;
    
    end while;
    
    print iterationNo;
    print HeightBounds;
    print NewHeightBounds;
    print stillEnumerating;
    print "=========================";

            
/////////////// second iteration ///////////////////////////////////////////////
    stillEnumerating:= true;
    
    while stillEnumerating do
        iterationNo:= iterationNo + 1;
 
        allBeps:= [];
        for i in [1..nu] do
            p:= LocalinfoList[i]`place;
            hp:= HeightBounds`heightgammalist[i];
            pAdicLatticePrep(fieldKinfo, fieldLinfo,~LocalinfoList[i], Case);   
            
            if assigned LocalinfoList[i]`smallbound then
                print "Small bound met: still need to add code for this";
            ///////////////////////////////////////////////////
            ///// check if smallbound is met ///////////////////
            ////////////////////////////////////////////////////// 
            end if;
            
            delta1Lp:= LocalinfoList[i]`delta1Lp;
            delta2Lp:= LocalinfoList[i]`delta2Lp;
            logihat:= LocalinfoList[i]`logihat;
            cp:= Log(p)*(Max(1/(p-1),Valuation(delta1Lp)) - Valuation(delta2Lp));
            lp:= Max(cp,hp - 1); // heuristic for initial value of lv; lv >= cp
            mu:= Floor(lp/Log(p) - Valuation(logihat) + Valuation(delta2Lp));
            
            if (mu le (Valuation(delta2Lp) - Valuation(logihat))) then
                print "mu is smaller than would allow";
                stillEnumerating:= false;
                break i;
            end if;
            
            assert mu gt (Valuation(delta2Lp) - Valuation(logihat));
            assert (cp le lp) and (lp lt hp);
            assert (hp gt Max(0,cp));
            CheckpAdicPrecision(fieldKinfo,fieldLinfo,~LocalinfoList[i],Case,mu,cp);
            // redifine constants (with better precision)
            delta1Lp:= LocalinfoList[i]`delta1Lp;
            delta2Lp:= LocalinfoList[i]`delta2Lp;
            logihat:= LocalinfoList[i]`logihat;
            
            // we now should have high enough precision to keep rum through FP at least once
            Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i],HeightBounds: Place:="NonArch");
            matBtmatB, vecc, boundForNormSquared, matAm,vecw:= pAdicLattice(LocalinfoList[i],Case,Bgam,BepsList,mu);
            bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
            
            if (#solutionsList eq 0) then
                while (#solutionsList eq 0) do
                    lp:= lp - 1;        // continue to decrease lp until solutions appear
                    mu:= Floor(lp/Log(p) - Valuation(logihat) + Valuation(delta2Lp)); // recompute mu
                     if mu le (Valuation(delta2Lp) - Valuation(logihat)) then
                        print "mu is smaller than would allow; terminating reduction";
                        stillEnumerating:= false;
                        break i;
                    end if;
                    assert mu gt (Valuation(delta2Lp) - Valuation(logihat));
                    if (cp gt lp) or (lp gt hp) then // only decreasing lp here; should terminate algorithm if this happens
                        print "lp is smaller than would allow; terminating reduction";
                        stillEnumerating:= false;
                        break i;
                    end if;
                    assert mu gt (Valuation(delta2Lp) - Valuation(logihat));
                    assert (cp le lp) and (lp lt hp);
                    assert ((mu+100) le LocalinfoList[i]`precision);
                    
                    Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i],HeightBounds: Place:="NonArch");
                    matBtmatB, vecc, boundForNormSquared, matAm,vecw:= pAdicLattice(LocalinfoList[i],Case,Bgam,BepsList,mu);
                    bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
                end while; // exits when lp is found such that there are no solutions
                
                lp:= lp + 1;  // smallest value of lp such that there are 0 solutions
                mu:= Floor(lp/Log(p) - Valuation(logihat) + Valuation(delta2Lp)); // recompute mu
                assert mu gt (Valuation(delta2Lp) - Valuation(logihat));
                assert (cp le lp) and (lp lt hp);
                Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i],HeightBounds: Place:="NonArch");
                matBtmatB, vecc, boundForNormSquared, matAm,vecw:= pAdicLattice(LocalinfoList[i],Case,Bgam,BepsList,mu);
                bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
                assert bufferWasBigEnough and (#solutionsList eq 0);
                
            else        // if solutions appear
                print "solutions found at p", p;
                bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=50000,lllReduce:=true, breakSymmetry:= true);
                if bufferWasBigEnough eq false then
                    print "far too many solutions; terminate reduction";
                    stillEnumerating:= false;
                    break i;
                end if;
                
                for x in solutionsList do
                    y:= x*Transpose(matAm) + Transpose(vecw);
                    if y notin candidateVectors then
                        Append(~candidateVectors,y);
                    end if;
                end for;
                
                //allSolutions[i]:= allSolutions[i] cat solutionsList;
            end if;
            NewHeightBounds`heightgammalist[i]:= Ceiling(lp);
            allBeps[i]:= BepsList;
        end for;
        
        if stillEnumerating then
          // archimedean places
            for i in [1..#fieldLinfo`ijk] do      //[1..#AutL] do // just need to run through i0,j,k
                v:= LocalinfoList[i+nu]`place;      // this corresponds to i0,j,k
                hv:= HeightBounds`heightepslist[i];
                RealLatticePrep(fieldKinfo,fieldLinfo,~LocalinfoList[i+nu],Case);        
                
                // ensure that v is the correct automorphism of i0,jk,
                assert v eq LocalinfoList[i+nu]`mapsLL[LocalinfoList[i+nu]`i0jk[i][1]][LocalinfoList[i+nu]`i0jk[i][2]];
                delta1Cv:= LocalinfoList[i+nu]`delta1Lp;
                delta2Cv:= LocalinfoList[i+nu]`delta2Lp;
                cv:= Log(Max( 2*Abs(delta2Cv),1 ));
                lv:= Max([Log(2),cv,hv - 1]); // heuristic for initial value of lv; lv >= cp
                mu:= Exp(lv);
                
                assert mu gt 0;
                assert (cv le lv) and (lv lt hv);
                assert hv gt cv;
                
                Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i+nu],HeightBounds: Place:="Real");
                BepsList[r]:= (BepsList[r] + mu*(3/2)*Exp(-lv))^2;
                matBtmatB, vecc, boundForNormSquared:= RealLattice(LocalinfoList[i+nu],Case,Bgam,BepsList,mu);
                bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
                
                if (#solutionsList eq 0) then
                      // decrease lp until there are solutions or lp is no longer in range and (Max(0,cp) lt lv) and (lv lt hp)
                    while (#solutionsList eq 0) do
                        lv:= lv - 1;        // decrease lv
                        mu:= Exp(lv);
                        assert mu gt 0;
                        if (cv gt lv) or (lv ge hv) then
                            print "lv is smaller than would allow; terminating reduction";
                            stillEnumerating:= false;
                            break i;
                        end if;
                        assert (cv le lv) and (lv lt hv);
                        
                        Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i+nu],HeightBounds: Place:="Real");
                        BepsList[r]:= (BepsList[r] + mu*(3/2)*Exp(-lv))^2;
                        matBtmatB, vecc, boundForNormSquared:= RealLattice(LocalinfoList[i+nu],Case,Bgam,BepsList,mu);
                        bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
                    end while; // exits when lp is found such that there are no solutions
                    lv:= lv + 1;  // smallest value of lp such that there are 0 solutions
                    mu:= Exp(lv);
                    assert mu gt 0;
                    assert (cv le lv) and (lv lt hv);
                    Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i+nu],HeightBounds: Place:="Real");
                    BepsList[r]:= (BepsList[r] + mu*(3/2)*Exp(-lv))^2;
                    matBtmatB, vecc, boundForNormSquared:= RealLattice(LocalinfoList[i+nu],Case,Bgam,BepsList,mu);
                    bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
                    assert bufferWasBigEnough and (#solutionsList eq 0);
                
                else        // if solutions appear
                    print "solutions found at v", i;
                    bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=50000,lllReduce:=true, breakSymmetry:= true);
                    if bufferWasBigEnough eq false then
                        print "far too many solutions; terminate reduction";
                        stillEnumerating:= false;
                        break i;
                    end if;
                    //allSolutions[i+nu]:= allSolutions[i+nu] cat solutionsList;
                    for x in solutionsList do
                        if x notin candidateVectors then
                            Append(~candidateVectors,x);
                        end if;
                    end for;
                    
                end if;
                NewHeightBounds`heightepslist[i]:= Ceiling(lv);
                allBeps[nu+i]:= [BepsList[1],-1];
            end for;
        end if;
            
        print iterationNo;
        print HeightBounds;
        print NewHeightBounds;
        print stillEnumerating;
        print "=========================";
        
        if stillEnumerating then
            HeightBounds:= NewHeightBounds;
            nBound, aBound:= infNorm(HeightBounds,Case,allBeps);
            HeightBounds`infheight:= [nBound, aBound];
            
            if Max(HeightBounds`infheight) le 50 then
                stillEnumerating:= false;
            end if;
        end if;
    end while;
    
    
    
    candidateSol:= pAdicSolutionTest(fieldKinfo,Case,candidateVectors);
    
    





   // K!tau*&*[gammalist[i]^(Integers()!y[1,i]) : i in [1..nu]]*epslist[1]^(Integers()!y[1,nu+1])*epslist[2]^(Integers()!y[1,nu+2]);

// To do: 
// 1. organize first iteration and speed it up (maybe start with 10*Log(bound)) - DONE
// 2. stop second iteration at a point when solutions are > something? - DONE
// 3. solutions checker (see what Kyle did)


  // stopped here; need to test with others and include inf heights; 
            // need to make sure it exists before lv >= cv (just copied the wrong decrease thing)
        // need to include next iteration where solutions are checked
        // need to include solutions checks
                
   


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
 
clist:= [1,17,23,-27];  
primelist:= [2,3,5,7,1987,1999]; 
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
    FieldInfo:= recformat<field,gen,ringofintegers,minpoly,zeta,fundamentalunits,automorphisms,ijk,LintoC>;
    LocalInfo:= recformat<place,idealinL,field,mapLLp,thetaL,mapsLL,i0jk,tauL,gammalistL,epslistL,delta1L,delta2L,delta1Lp,delta2Lp,ihat,logihat,betalist,precision,precMultiple,smallbound,solutions>;
    HeightBoundInfo:= recformat<heightgammalist,heightepslist,infheight>;
    
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
    ijkAutL(fieldKinfo,~fieldLinfo);
    AutL:= fieldLinfo`automorphisms;
    
    fieldCinfo:= rec<LocalInfo | precMultiple:= 1, precision:= 167>;
    ComplexFieldInfo(fieldKinfo,fieldLinfo,~fieldCinfo);
 
    // compute the initial height bound
    printf "Computing initial height bounds...";
    t1:= Cputime();
    UpperBounds(fieldKinfo,fieldLinfo, ~fieldCinfo,clist,primelist,a,~alphgamlist);
    printf "Done! Duration: %o\n", Cputime(t1);
 
    // begin cycling through cases
    CaseNo:= 1;
    
    for Case in alphgamlist do
        printf "-"^(80) cat "\n"; 
       // printf "Case: %o\n", CaseNo;
        printf "Initial height bound: %o\n", Case`bound;
        
        CasePrimes:= [Norm(fp) : fp in Case`ideallist];
        nu:= #Case`gammalist;
        assert #CasePrimes eq nu;
        assert &and[p in primelist : p in CasePrimes];
       
        ///////////////////////////////////////////////////
        ///// can we write the heightbounds more concisely/
        ///////////////////////////////////////////////////
        HeightBounds:= rec<HeightBoundInfo | heightgammalist:= [Case`bound : i in [1..nu]],heightepslist:= [Case`bound : i in [1..#fieldLinfo`ijk]]>;
        NewHeightBounds:= rec<HeightBoundInfo | heightgammalist:= [],heightepslist:= []>;
        // nonarchimedean
        LocalinfoList:= [];
        for i in [1..nu] do
            p:= CasePrimes[i];
            idealinL:= (Factorisation(p*OL))[1][1];
            LocalinfoList[i]:=rec< LocalInfo | place:= p, idealinL:= idealinL, precMultiple:= 1.3^5>;
        end for;
        for i in [1..#fieldLinfo`ijk] do      //[1..#AutL] do // just need to run through i0,j,k
            v:= fieldLinfo`ijk[i];      // this corresponds to i0,j,k
            hv:= HeightBounds`heightepslist[i];
            LocalinfoList[i+nu]:=rec< LocalInfo | place:= v, precMultiple:= 1.3^5>;
        end for;
        




















        // nonArchimedean initial reduction
        pAdicReductionIteration(fieldKinfo,fieldLinfo,fieldCinfo,~LocalinfoList,Case,HeightBounds,~NewHeightBounds);
    
        
//////////////// Archimedean ///////////////////////////        
        for i in [1..#fieldLinfo`ijk] do      //[1..#AutL] do // just need to run through i0,j,k
            v:= fieldLinfo`ijk[i];      // this corresponds to i0,j,k
            //AutL[i];
            hv:= HeightBounds`heightepslist[i];
            
            LocalinfoList[i+nu]:=rec< LocalInfo | place:= v, precMultiple:= 1.3^5>;
            RealLatticePrep(fieldKinfo,fieldLinfo,~LocalinfoList[i+nu],Case);        
            
            // ensure that v is the correct automorphism of i0,jk,
            assert v eq LocalinfoList[i+nu]`mapsLL[LocalinfoList[i+nu]`i0jk[i][1]][LocalinfoList[i+nu]`i0jk[i][2]];
            delta1Cv:= LocalinfoList[i+nu]`delta1Lp;
            delta2Cv:= LocalinfoList[i+nu]`delta2Lp;
            cv:= Log(Max( 2*Abs(delta2Cv),1 ));
            lv:= Max([Log(2),cv,(1.3)^3*Log(Case`bound)]); // heuristic for initial value of lv; lv >= cp
            mu:= Exp(lv);
            
            assert mu gt 0;
            assert (cv le lv) and (lv lt hv);
            assert hv gt cv;
            
            Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i+nu],HeightBounds: Place:="Real");
            BepsList[r]:= BepsList[r] + mu*(3/2)*Exp(-lv);
            matBtmatB, vecc, boundForNormSquared:= RealLattice(LocalinfoList[i+nu],Case,Bgam,BepsList,mu);
            bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
            
            if (#solutionsList ne 0) then
            // increase lv until there are no solutions or lp is no longer in range and (Max(0,cp) lt lv) and (lv lt hp)
                while (#solutionsList ne 0) and (cv le lv) and (lv lt hv) do
                  //  print "*1";
                    lv:= lv*(1.3);        // decrease lv
                    mu:= Exp(lv);
                    assert mu gt 0;
                    assert (cv le lv) and (lv lt hv);
                    
                    Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i+nu],HeightBounds: Place:="Real");
                    BepsList[r]:= BepsList[r] + mu*(3/2)*Exp(-lv);
                    matBtmatB, vecc, boundForNormSquared:= RealLattice(LocalinfoList[i+nu],Case,Bgam,BepsList,mu);
                    bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
                end while; // exits when lp is found such that there are no solutions
                
            else // otherwise we have 0 solutions; try to find a smaller bound
            // decrease lp until there are solutions or lp is no longer in range and (Max(0,cp) lt lv) and (lv lt hp)
                while (#solutionsList eq 0) and (cv le lv) and (lv lt hv) do
                    //print "/1";
                    lv:= lv/(1.3);        // decrease lv
                    mu:= Exp(lv);
                    assert mu gt 0;
                    assert (cv le lv) and (lv lt hv);
                    
                    Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i+nu],HeightBounds: Place:="Real");
                    BepsList[r]:= BepsList[r] + mu*(3/2)*Exp(-lv);
                    matBtmatB, vecc, boundForNormSquared:= RealLattice(LocalinfoList[i+nu],Case,Bgam,BepsList,mu);
                    bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
                end while; // exits when lp is found such that there are no solutions
                lv:= lv*(1.3);  // smallest value of lp such that there are 0 solutions
                mu:= Exp(lv);
                assert mu gt 0;
                assert (cv le lv) and (lv lt hv);
                
                Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i+nu],HeightBounds: Place:="Real");
                BepsList[r]:= BepsList[r] + mu*(3/2)*Exp(-lv);
                matBtmatB, vecc, boundForNormSquared:= RealLattice(LocalinfoList[i+nu],Case,Bgam,BepsList,mu);
                bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
                assert bufferWasBigEnough and (#solutionsList eq 0);
            end if;
            
            
           // print "BEFRORE mu,lv", mu, lv;
            while (#solutionsList eq 0) and (cv le lv) and (lv lt hv) do
              //  print "-lv", lv;
                //print "/1";
                lv:= lv-1;        // decrease lv
                mu:= Exp(lv);
                assert mu gt 0;
                assert (cv le lv) and (lv lt hv);
                
                Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i+nu],HeightBounds: Place:="Real");
                BepsList[r]:= BepsList[r] + mu*(3/2)*Exp(-lv);
                matBtmatB, vecc, boundForNormSquared:= RealLattice(LocalinfoList[i+nu],Case,Bgam,BepsList,mu);
                bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
            end while; // exits when lp is found such that there are no solutions
            lv:= lv+1;  // smallest value of lp such that there are 0 solutions
            mu:= Exp(lv);
            assert mu gt 0;
            assert (cv le lv) and (lv lt hv);
            
            Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i+nu],HeightBounds: Place:="Real");
            BepsList[r]:= BepsList[r] + mu*(3/2)*Exp(-lv);
            matBtmatB, vecc, boundForNormSquared:= RealLattice(LocalinfoList[i+nu],Case,Bgam,BepsList,mu);
            bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
            assert bufferWasBigEnough and (#solutionsList eq 0);
        
     //   print "lv", lv;
        NewHeightBounds`heightepslist[i]:= Ceiling(lv);
    end for;
    
    // update Height Bounds; ie set the vector h to the vector l and continue
    // from here on out, we will obtain solutions when using Fincke-Pohst
    HeightBounds:= NewHeightBounds;     
    
    
    
    // ROUND 2
 ////////////////////////////////////////////////////////////////////////////////////////////////
    pAdicReductionIteration(fieldKinfo,fieldLinfo,fieldCinfo,~LocalinfoList,Case,HeightBounds,~NewHeightBounds: iterationNo:= 1);
    
    for i in [1..#fieldLinfo`ijk] do
        v:= fieldLinfo`ijk[i];
        hv:= HeightBounds`heightepslist[i];
        
        delta1Cv:= LocalinfoList[i+nu]`delta1Lp;
        delta2Cv:= LocalinfoList[i+nu]`delta2Lp;
        cv:= Log(Max( 2*Abs(delta2Cv),1 ));
        lv:= Max([Log(2),cv,hv - 5]); // heuristic for initial value of lv; lv >= cp
        mu:= Exp(lv);
        
        assert mu gt 0;
        assert (cv le lv) and (lv lt hv);
        assert hv gt cv;
        
        Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i+nu],HeightBounds: Place:="Real");
        BepsList[r]:= BepsList[r] + mu*(3/2)*Exp(-lv);
        matBtmatB, vecc, boundForNormSquared:= RealLattice(LocalinfoList[i+nu],Case,Bgam,BepsList,mu);
        bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc,lllReduce:=true, breakSymmetry:= true);
        
        if (#solutionsList ne 0) then
        // increase lv until there are no solutions or lp is no longer in range and (Max(0,cp) lt lv) and (lv lt hp)
            print "TEST SOLUTIONS";
        else // otherwise we have 0 solutions; try to find a smaller bound
        // decrease lp until there are solutions or lp is no longer in range and (Max(0,cp) lt lv) and (lv lt hp)
            while (#solutionsList eq 0) and (cv le lv) and (lv lt hv) do
                //print "/1";
                lv:= lv-1;        // decrease lv
                mu:= Exp(lv);
                assert mu gt 0;
                assert (cv le lv) and (lv lt hv);
                
                Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i+nu],HeightBounds: Place:="Real");
                BepsList[r]:= BepsList[r] + mu*(3/2)*Exp(-lv);
                matBtmatB, vecc, boundForNormSquared:= RealLattice(LocalinfoList[i+nu],Case,Bgam,BepsList,mu);
                bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
            end while; // exits when lp is found such that there are no solutions
            lv:= lv+1;  // smallest value of lp such that there are 0 solutions
            mu:= Exp(lv);
            assert mu gt 0;
            assert (cv le lv) and (lv lt hv);
            
            Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i+nu],HeightBounds: Place:="Real");
            BepsList[r]:= BepsList[r] + mu*(3/2)*Exp(-lv);
            matBtmatB, vecc, boundForNormSquared:= RealLattice(LocalinfoList[i+nu],Case,Bgam,BepsList,mu);
            bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
            assert bufferWasBigEnough and (#solutionsList eq 0);
        end if;
        
        NewHeightBounds`heightepslist[i]:= Ceiling(lv);
    end for;
    
    
       // update Height Bounds; ie set the vector h to the vector l and continue
    // from here on out, we will obtain solutions when using Fincke-Pohst
    HeightBounds:= NewHeightBounds;     
    
    // ROUND 3
 ////////////////////////////////////////////////////////////////////////////////////////////////
    for i in [1..nu] do
        p:= CasePrimes[i];
        hp:= HeightBounds`heightgammalist[i];
        idealinL:= (Factorisation(p*OL))[1][1];
        
        delta1Lp:= LocalinfoList[i]`delta1Lp;
        delta2Lp:= LocalinfoList[i]`delta2Lp;
        logihat:= LocalinfoList[i]`logihat;
        cp:= Log(p)*(Max(1/(p-1),Valuation(delta1Lp)) - Valuation(delta2Lp));
        ijkLp:= LocalinfoList[i]`i0jk;
        precision:= LocalinfoList[i]`precision;
        PrecMultiplier:= LocalinfoList[i]`precMultiple;
        lp:= Max(cp,hp - 5*Log(p)); // decrease mu by 1 (so degrease lp by Log(p) from original hp)
        mu:= Floor(lp/Log(p) - Valuation(logihat) + Valuation(delta2Lp));
        //print "MU", mu;
        assert mu gt (Valuation(delta2Lp) - Valuation(logihat));
        assert (cp le lp) and (lp lt hp);
        assert (hp gt Max(0,cp));

        while (mu+100) gt precision do       // recompute deltas with new pAdicPrec:= 3*mu
            print "+1";
            LocalinfoList[i]`precMultiple:= (1.3)*LocalinfoList[i]`precMultiple;
            pAdicLatticePrep(fieldKinfo, fieldLinfo,~LocalinfoList[i], Case);
            precision:= LocalinfoList[i]`precision;
            delta1Lp:= LocalinfoList[i]`delta1Lp;
            delta2Lp:= LocalinfoList[i]`delta2Lp;
            logihat:= LocalinfoList[i]`logihat;
            assert LocalinfoList[i]`i0jk eq ijkLp; // assert that i0,j,k has not changed 
            // assert that cp has not changed
            assert cp eq Log(p)*(Max(1/(p-1),Valuation(delta1Lp)) - Valuation(delta2Lp));
            PrecMultiplier:= LocalinfoList[i]`precMultiple;
        end while;
        assert ((mu+100) le precision);
        
        // we now should have high enough precision to keep rum through FP at least once
        Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i],HeightBounds);
        matBtmatB, vecc, boundForNormSquared:= pAdicLattice(LocalinfoList[i],Case,Bgam,BepsList,mu);
        bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc,lllReduce:=true, breakSymmetry:= true);
        
        if (#solutionsList ne 0) then
        // increase lv until there are no solutions or lp is no longer in range and (Max(0,cp) lt lv) and (lv lt hp)
           print "TEST SOLUTIONS", #solutionsList;
            
        else // otherwise we have 0 solutions; try to find a smaller bound
        // decrease lp until there are solutions or lp is no longer in range and (Max(0,cp) lt lv) and (lv lt hp)
            while (#solutionsList eq 0) and (cp le lp) and (lp lt hp) and (lp gt Log(p)*(Valuation(logihat) - Valuation(delta2Lp))) do
                //print "/1";
                lp:= lp - 5*Log(p);        // decrease lv
                mu:= Floor(lp/Log(p) - Valuation(logihat) + Valuation(delta2Lp)); // recompute mu
                assert mu gt (Valuation(delta2Lp) - Valuation(logihat));
                assert (cp le lp) and (lp lt hp);
                assert ((mu+100) le precision);
                Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i],HeightBounds);
                matBtmatB, vecc, boundForNormSquared:= pAdicLattice(LocalinfoList[i],Case,Bgam,BepsList,mu);
                bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
            end while; // exits when lp is found such that there are no solutions
            lp:= lp + 5*Log(p);  // smallest value of lp such that there are 0 solutions
            mu:= Floor(lp/Log(p) - Valuation(logihat) + Valuation(delta2Lp)); // recompute mu
            Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i],HeightBounds);
            matBtmatB, vecc, boundForNormSquared:= pAdicLattice(LocalinfoList[i],Case,Bgam,BepsList,mu);
            bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
            assert bufferWasBigEnough and (#solutionsList eq 0);
        end if;
        
        NewHeightBounds`heightgammalist[i]:= Ceiling(lp);
    end for;
    
    for i in [1..#AutL] do
        v:= AutL[i];
        hv:= HeightBounds`heightepslist[i];
        
        delta1Cv:= LocalinfoList[i+nu]`delta1Lp;
        delta2Cv:= LocalinfoList[i+nu]`delta2Lp;
        cv:= Log(Max( 2*Abs(delta2Cv),1 ));
        lv:= Max([Log(2),cv,hv - 5]); // heuristic for initial value of lv; lv >= cp
        mu:= Exp(lv);
        
        assert mu gt 0;
        assert (cv le lv) and (lv lt hv);
        assert hv gt cv;
        
        Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i+nu],HeightBounds: Place:="Real");
        BepsList[r]:= BepsList[r] + mu*(3/2)*Exp(-lv);
        matBtmatB, vecc, boundForNormSquared:= RealLattice(LocalinfoList[i+nu],Case,Bgam,BepsList,mu);
        bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc,lllReduce:=true, breakSymmetry:= true);
        
        if (#solutionsList ne 0) then
        // increase lv until there are no solutions or lp is no longer in range and (Max(0,cp) lt lv) and (lv lt hp)
            print "TEST SOLUTIONS", #solutionsList;
        else // otherwise we have 0 solutions; try to find a smaller bound
        // decrease lp until there are solutions or lp is no longer in range and (Max(0,cp) lt lv) and (lv lt hp)
            while (#solutionsList eq 0) and (cv le lv) and (lv lt hv) do
                //print "/1";
                lv:= lv-5;        // decrease lv
                mu:= Exp(lv);
                assert mu gt 0;
                assert (cv le lv) and (lv lt hv);
                
                Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i+nu],HeightBounds: Place:="Real");
                BepsList[r]:= BepsList[r] + mu*(3/2)*Exp(-lv);
                matBtmatB, vecc, boundForNormSquared:= RealLattice(LocalinfoList[i+nu],Case,Bgam,BepsList,mu);
                bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
            end while; // exits when lp is found such that there are no solutions
            lv:= lv+5;  // smallest value of lp such that there are 0 solutions
            mu:= Exp(lv);
            assert mu gt 0;
            assert (cv le lv) and (lv lt hv);
            
            Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i+nu],HeightBounds: Place:="Real");
            BepsList[r]:= BepsList[r] + mu*(3/2)*Exp(-lv);
            matBtmatB, vecc, boundForNormSquared:= RealLattice(LocalinfoList[i+nu],Case,Bgam,BepsList,mu);
            bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
            assert bufferWasBigEnough and (#solutionsList eq 0);
        end if;
        
        NewHeightBounds`heightepslist[i]:= Ceiling(lv);
    end for;
    HeightBounds:= NewHeightBounds;  
    
    
////////////////////////////
////////////////////////ROUND 4/////////////////
while &or[HeightBounds`heightgammalist[i] gt 15 : i in [1..nu]] do
  for i in [1..nu] do
        p:= CasePrimes[i];
        hp:= HeightBounds`heightgammalist[i];
        idealinL:= (Factorisation(p*OL))[1][1];
        
        delta1Lp:= LocalinfoList[i]`delta1Lp;
        delta2Lp:= LocalinfoList[i]`delta2Lp;
        logihat:= LocalinfoList[i]`logihat;
        cp:= Log(p)*(Max(1/(p-1),Valuation(delta1Lp)) - Valuation(delta2Lp));
        ijkLp:= LocalinfoList[i]`i0jk;
        precision:= LocalinfoList[i]`precision;
        PrecMultiplier:= LocalinfoList[i]`precMultiple;
        lp:= Max(cp,hp - 2*Log(p)); // decrease mu by 1 (so degrease lp by Log(p) from original hp)
        mu:= Floor(lp/Log(p) - Valuation(logihat) + Valuation(delta2Lp));
        //print "MU", mu;
        assert mu gt (Valuation(delta2Lp) - Valuation(logihat));
        assert (cp le lp) and (lp lt hp);
        assert (hp gt Max(0,cp));

        while (mu+100) gt precision do       // recompute deltas with new pAdicPrec:= 3*mu
            print "+1";
            LocalinfoList[i]`precMultiple:= (1.3)*LocalinfoList[i]`precMultiple;
            pAdicLatticePrep(fieldKinfo, fieldLinfo,~LocalinfoList[i], Case);
            precision:= LocalinfoList[i]`precision;
            delta1Lp:= LocalinfoList[i]`delta1Lp;
            delta2Lp:= LocalinfoList[i]`delta2Lp;
            logihat:= LocalinfoList[i]`logihat;
            assert LocalinfoList[i]`i0jk eq ijkLp; // assert that i0,j,k has not changed 
            // assert that cp has not changed
            assert cp eq Log(p)*(Max(1/(p-1),Valuation(delta1Lp)) - Valuation(delta2Lp));
            PrecMultiplier:= LocalinfoList[i]`precMultiple;
        end while;
        assert ((mu+100) le precision);
        
        // we now should have high enough precision to keep rum through FP at least once
        Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i],HeightBounds);
        matBtmatB, vecc, boundForNormSquared:= pAdicLattice(LocalinfoList[i],Case,Bgam,BepsList,mu);
        bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc,lllReduce:=true, breakSymmetry:= true);
        
        if (#solutionsList ne 0) then
        // increase lv until there are no solutions or lp is no longer in range and (Max(0,cp) lt lv) and (lv lt hp)
           print "TEST SOLUTIONS", #solutionsList;
            
        else // otherwise we have 0 solutions; try to find a smaller bound
        // decrease lp until there are solutions or lp is no longer in range and (Max(0,cp) lt lv) and (lv lt hp)
            while (#solutionsList eq 0) and (cp le lp) and (lp lt hp) and (lp gt Log(p)*(Valuation(logihat) - Valuation(delta2Lp))) do
                //print "/1";
                lp:= lp - 2*Log(p);        // decrease lv
                mu:= Floor(lp/Log(p) - Valuation(logihat) + Valuation(delta2Lp)); // recompute mu
                assert mu gt (Valuation(delta2Lp) - Valuation(logihat));
                assert (cp le lp) and (lp lt hp);
                assert ((mu+100) le precision);
                Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i],HeightBounds);
                matBtmatB, vecc, boundForNormSquared:= pAdicLattice(LocalinfoList[i],Case,Bgam,BepsList,mu);
                bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
            end while; // exits when lp is found such that there are no solutions
            lp:= lp + 2*Log(p);  // smallest value of lp such that there are 0 solutions
            mu:= Floor(lp/Log(p) - Valuation(logihat) + Valuation(delta2Lp)); // recompute mu
            Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i],HeightBounds);
            matBtmatB, vecc, boundForNormSquared:= pAdicLattice(LocalinfoList[i],Case,Bgam,BepsList,mu);
            bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
            assert bufferWasBigEnough and (#solutionsList eq 0);
        end if;
        
        NewHeightBounds`heightgammalist[i]:= Ceiling(lp);
    end for;
    
    for i in [1..#AutL] do
        v:= AutL[i];
        hv:= HeightBounds`heightepslist[i];
        
        delta1Cv:= LocalinfoList[i+nu]`delta1Lp;
        delta2Cv:= LocalinfoList[i+nu]`delta2Lp;
        cv:= Log(Max( 2*Abs(delta2Cv),1 ));
        lv:= Max([Log(2),cv,hv - 1]); // heuristic for initial value of lv; lv >= cp
        mu:= Exp(lv);
        
        assert mu gt 0;
        assert (cv le lv) and (lv lt hv);
        assert hv gt cv;
        
        Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i+nu],HeightBounds: Place:="Real");
        BepsList[r]:= BepsList[r] + mu*(3/2)*Exp(-lv);
        matBtmatB, vecc, boundForNormSquared:= RealLattice(LocalinfoList[i+nu],Case,Bgam,BepsList,mu);
        bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc,lllReduce:=true, breakSymmetry:= true);
        
        if (#solutionsList ne 0) then
        // increase lv until there are no solutions or lp is no longer in range and (Max(0,cp) lt lv) and (lv lt hp)
            print "TEST SOLUTIONS", #solutionsList;
        else // otherwise we have 0 solutions; try to find a smaller bound
        // decrease lp until there are solutions or lp is no longer in range and (Max(0,cp) lt lv) and (lv lt hp)
            while (#solutionsList eq 0) and (cv le lv) and (lv lt hv) do
                //print "/1";
                lv:= lv-1;        // decrease lv
                mu:= Exp(lv);
                assert mu gt 0;
                assert (cv le lv) and (lv lt hv);
                
                Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i+nu],HeightBounds: Place:="Real");
                BepsList[r]:= BepsList[r] + mu*(3/2)*Exp(-lv);
                matBtmatB, vecc, boundForNormSquared:= RealLattice(LocalinfoList[i+nu],Case,Bgam,BepsList,mu);
                bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
            end while; // exits when lp is found such that there are no solutions
            lv:= lv+1;  // smallest value of lp such that there are 0 solutions
            mu:= Exp(lv);
            assert mu gt 0;
            assert (cv le lv) and (lv lt hv);
            
            Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i+nu],HeightBounds: Place:="Real");
            BepsList[r]:= BepsList[r] + mu*(3/2)*Exp(-lv);
            matBtmatB, vecc, boundForNormSquared:= RealLattice(LocalinfoList[i+nu],Case,Bgam,BepsList,mu);
            bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
            assert bufferWasBigEnough and (#solutionsList eq 0);
        end if;
        
        NewHeightBounds`heightepslist[i]:= Ceiling(lv);
    end for;
    HeightBounds;
    HeightBounds:= NewHeightBounds;
    HeightBounds;      
end while;
    
    
    
    
    
    
            

intrinsic ExtractTuplePadic(~bbb::SeqEnum[FldRatElt],~ExtractTuplePadicInput::List,~uuu::LatElt[RngInt])
{}
//Extract tuple (b_{JJJ[2]},...,b_{JJJ[nJJJ]})
//ExtractTuplePadicInput:=[*bbb,l,ihat,istar,yyy,zzz,JJJ,nJJJ,nJ,W,B,v*];
//bbb:=ExtractTuplePadicInput[1];
l:=ExtractTuplePadicInput[2];
ihat:=ExtractTuplePadicInput[3];
istar:=ExtractTuplePadicInput[4];
yyy:=ExtractTuplePadicInput[5];
zzz:=ExtractTuplePadicInput[6];
JJJ:=ExtractTuplePadicInput[7];
nJJJ:=ExtractTuplePadicInput[8];
nJ:=ExtractTuplePadicInput[9];
W:=ExtractTuplePadicInput[10];
B:=ExtractTuplePadicInput[11];
v:=ExtractTuplePadicInput[12];

bbb[1]:=1;
if ihat[l] le 1+v then

for i:=2 to istar[l]-1 do
bbb[i]:=(uuu[i-1]-(yyy[i-1][1]-zzz[i-1][1]) + (1/2)*W[JJJ[i]]*B[JJJ[i]])/W[JJJ[i]];
end for;
bbb[istar[l]]:=(uuu[nJJJ-1]-(yyy[nJJJ-1][1]-zzz[nJJJ-1][1]) + (1/2)*W[JJJ[istar[l]]]*B[JJJ[istar[l]]])/W[JJJ[istar[l]]];
for i:=istar[l]+1 to 1+nJ do
bbb[i]:=(uuu[i-2]-(yyy[i-2][1]-zzz[i-2][1]) + (1/2)*W[JJJ[i]]*B[JJJ[i]])/W[JJJ[i]];
end for;
for i:=2+nJ to nJJJ do
bbb[i]:=(uuu[i-2]-(yyy[i-2][1]-zzz[i-2][1]))/W[JJJ[i]];
end for;

else //ihat[l] gt 1+v

for i:=2 to 1+nJ do
bbb[i]:=(uuu[i-1]-(yyy[i-1][1]-zzz[i-1][1]) + (1/2)*W[JJJ[i]]*B[JJJ[i]])/W[JJJ[i]];
end for;
for i:=2+nJ to istar[l]-1 do
bbb[i]:=(uuu[i-1]-(yyy[i-1][1]-zzz[i-1][1]))/W[JJJ[i]];
end for;
bbb[istar[l]]:=(uuu[nJJJ-1]-(yyy[nJJJ-1][1]-zzz[nJJJ-1][1]))/W[JJJ[istar[l]]];
for i:=istar[l]+1 to nJJJ do
bbb[i]:=(uuu[i-2]-(yyy[i-2][1]-zzz[i-2][1]))/W[JJJ[i]];
end for;

end if;

end intrinsic;

//////////////////////////////////////////////////////////////////

intrinsic TestTuplePadic(~bbb::SeqEnum[FldRatElt],~TestTuplePadicInput::List,~passes::BoolElt)
{}
//bbb:=TestTuplePadicInput[1];


l:=TestTuplePadicInput[2];
JJJ:=TestTuplePadicInput[3];
nJJJ:=TestTuplePadicInput[4];
nJ:=TestTuplePadicInput[5];
jl:=TestTuplePadicInput[6];
beta:=TestTuplePadicInput[7];
hh:=TestTuplePadicInput[8];
dd:=TestTuplePadicInput[9];
p:=TestTuplePadicInput[10];
SpecialCase:=TestTuplePadicInput[11];
NewUpperBoundFornl:=TestTuplePadicInput[12];
delta2:=TestTuplePadicInput[13];
LogarithmicAlphap:=TestTuplePadicInput[14];
B:=TestTuplePadicInput[15];
I:=TestTuplePadicInput[16];

while true do //this while loop is a hack to provide a way to "jump to line X" 

for i:=2 to nJJJ do
    if not IsIntegral(bbb[i]) then 
        passes:=false; 
        break; 
    end if;
end for;

if passes eq false then 
    break; 
end if;

for i:=2 to 1+nJ do
    if bbb[i] gt B[JJJ[i]] or bbb[i] lt 0 then 
        passes:=false; 
        break; 
    end if;
end for;
if passes eq false then 
    break; 
end if;

for i:=2+nJ to nJJJ do
    if bbb[i] gt B[JJJ[i]] or bbb[i] lt -B[JJJ[i]] then 
        passes:=false; 
        break; 
    end if;
end for;
if passes eq false then 
    break; 
end if;


/*test if tuple fits in the new box.  If so, throw it away (it's not exceptional).  Recall bbb[jl[l]] = b_{l+1} = n_l*/
if bbb[jl[l]] le NewUpperBoundFornl then 
    passes:=false; 
    break; 
end if;



LAMBDAprime:=0;
for i:=1 to nJJJ do 
    LAMBDAprime:=LAMBDAprime + bbb[i]*beta[l][JJJ[i]];
end for;
if SpecialCase[l] eq true then
    if Valuation(LAMBDAprime) ne bbb[jl[l]]*hh[l] + dd[l] then 
        passes:=false; 
        break; 
    end if; 
else //SpecialCase[l] eq false
    if Valuation(LAMBDAprime) lt bbb[jl[l]]*hh[l] + dd[l] then 
        passes:=false; 
        break; 
    end if;
end if;


// ADELA'S FUCKERY: have to remove this sieve (questionably, though), as it causes loss of solutions. 
/*
for ll in I do
    if ll ne l then

        LAMBDAprime:=0;
        for i:=1 to nJJJ do 
            LAMBDAprime:=LAMBDAprime + bbb[i]*beta[ll][JJJ[i]];
        end for;
        if SpecialCase[ll] eq true then
            if bbb[jl[ll]] gt (1/hh[ll])*(1/(p[ll]-1) - Valuation(delta2[ll])) and Valuation(LAMBDAprime) ne bbb[jl[ll]]*hh[ll] + dd[ll] then
                passes:=false; 
                print "passes, 8688:", passes, ll;
                break ll; 
            end if;
            if bbb eq [ 1, 0, 0, 1, 3, 2, 0, 0 ] then
                print "yes, enters TestTuple, Line 8691";
                print "passes?:", passes;
            end if;
            
            
        else //SpecialCase[ll] eq false
            if bbb[jl[ll]] gt (1/hh[ll])*(1/(p[ll]-1) - Valuation(delta2[ll])) and Valuation(LAMBDAprime) lt bbb[jl[ll]]*hh[ll] + dd[ll] then
                passes:=false;      
                break ll;
            end if;
        end if;

    end if;
end for;
*/
if passes eq false then 
    break; 
end if;


if SpecialCase[l] eq false then
LAMBDA:=0;
for i:=1 to nJJJ do
LAMBDA:=LAMBDA + bbb[i]*LogarithmicAlphap[l][JJJ[i]];
end for;
if Valuation(LAMBDA) ne bbb[jl[l]]*hh[l] + Valuation(delta2[l]) then passes:=false; break; end if;
end if; //end IF controlled by SpecialCase[l] 


for ll in I do
if ll ne l then
if SpecialCase[ll] eq false then
LAMBDA:=0;
for i:=1 to nJJJ do 
LAMBDA:=LAMBDA + bbb[i]*beta[ll][JJJ[i]];
end for;
if bbb[jl[ll]] gt (1/hh[ll])*(1/(p[ll]-1) - Valuation(delta2[ll])) and Valuation(LAMBDA) ne bbb[jl[ll]]*hh[ll] + Valuation(delta2[ll]) then
passes:=false; break ll;
end if;
end if; //end IF controlled by SpecialCase[ll] 
end if;
end for;
if passes eq false then break; end if;


break;
end while; //end hack while loop

end intrinsic;

////////////////////////////////////////////////////////////////////////////////////////////
intrinsic ExtractTupleRealCase(~bbb::SeqEnum[FldRatElt],~ExtractTupleRealCaseInput::List,~uuu::LatElt[RngInt])
{}
//Extract tuple (b_{JJJ[2]},...,b_{JJJ[#JJJ]})
//bbb:=ExtractTupleRealCaseInput[1];
yyy:=ExtractTupleRealCaseInput[2];
zzz:=ExtractTupleRealCaseInput[3];
JJJ:=ExtractTupleRealCaseInput[4];
nJJJ:=ExtractTupleRealCaseInput[5];
nJ:=ExtractTupleRealCaseInput[6];
W:=ExtractTupleRealCaseInput[7];
B:=ExtractTupleRealCaseInput[8];
phi:=ExtractTupleRealCaseInput[9];


bbb[1]:=1;

for i:=2 to 1+nJ do
bbb[i] := (uuu[i-1] - (yyy[i-1][1]-zzz[i-1][1]) + (1/2)*W[JJJ[i]]*B[JJJ[i]])/W[JJJ[i]];
end for;
for i:=2+nJ to nJJJ-1 do
bbb[i] := (uuu[i-1] - (yyy[i-1][1]-zzz[i-1][1]))/W[JJJ[i]];
end for;
sum:=0;
for i:=1 to nJJJ-1 do
sum:=sum+bbb[i]*phi[JJJ[i]];
end for;
bbb[nJJJ] := (uuu[nJJJ-1] - (yyy[nJJJ-1][1]-zzz[nJJJ-1][1]) - sum)/phi[JJJ[nJJJ]];

end intrinsic;

/////////////////////////////////////////////////////////////////////////////////

intrinsic TestTupleRealCase(~bbb::SeqEnum[FldRatElt],~TestTupleRealCaseInput::List,~passes::BoolElt)
{}
//Test the tuple
//bbb:=TestTupleRealCaseInput[1];
JJJ:=TestTupleRealCaseInput[2];
nJJJ:=TestTupleRealCaseInput[3];
nJ:=TestTupleRealCaseInput[4];
NewConditionalUpperBoundForAi0:=TestTupleRealCaseInput[5];
jl:=TestTupleRealCaseInput[6];
SpecialCase:=TestTupleRealCaseInput[7];
p:=TestTupleRealCaseInput[8];
delta2:=TestTupleRealCaseInput[9];
hh:=TestTupleRealCaseInput[10];
dd:=TestTupleRealCaseInput[11];
B:=TestTupleRealCaseInput[12];
I:=TestTupleRealCaseInput[13];
beta:=TestTupleRealCaseInput[14];

while true do //this while loop is a hack to provide a way to "jump to line X" 

for i:=2 to nJJJ do
if not IsIntegral(bbb[i]) then passes:=false; break; end if;
end for;
if passes eq false then break; end if;

for i:=2 to 1+nJ do
if bbb[i] gt B[JJJ[i]] or bbb[i] lt 0 then passes:=false; break; end if;
end for;
if passes eq false then break; end if;

for i:=2+nJ to nJJJ do
if bbb[i] gt B[JJJ[i]] or bbb[i] lt -B[JJJ[i]] then passes:=false; break; end if;
end for;
if passes eq false then break; end if;

/*Test if the tuple fits in the new box.  If so, throw it away (it's not exceptional).*/
FitsInTheNewBox:=true;
for i:=2+nJ to nJJJ do
if Abs(bbb[i]) gt NewConditionalUpperBoundForAi0 then 
FitsInTheNewBox:=false; break i; 
end if;
end for;
if FitsInTheNewBox eq true then passes:=false; break; end if;

for ll in I do
LAMBDAprime:=0;
for i:=1 to nJJJ do 
LAMBDAprime:=LAMBDAprime + bbb[i]*beta[ll][JJJ[i]];
end for;
if SpecialCase[ll] eq true then
if bbb[jl[ll]] gt (1/hh[ll])*(1/(p[ll]-1) - Valuation(delta2[ll])) and Valuation(LAMBDAprime) ne bbb[jl[ll]]*hh[ll] + dd[ll] then
passes:=false; break ll; 
end if;
else //SpecialCase[ll] eq false
if bbb[jl[ll]] gt (1/hh[ll])*(1/(p[ll]-1) - Valuation(delta2[ll])) and Valuation(LAMBDAprime) lt bbb[jl[ll]]*hh[ll] + dd[ll] then
passes:=false; break ll;
end if;
end if;
end for;
if passes eq false then break; end if;

for ll in I do
if SpecialCase[ll] eq false then
LAMBDA:=0;
for i:=1 to nJJJ do 
LAMBDA:=LAMBDA + bbb[i]*beta[ll][JJJ[i]];
end for;
if bbb[jl[ll]] gt (1/hh[ll])*(1/(p[ll]-1) - Valuation(delta2[ll])) and Valuation(LAMBDA) ne bbb[jl[ll]]*hh[ll] + Valuation(delta2[ll]) then
passes:=false; break ll;
end if;
end if;
end for;
if passes eq false then break; end if;


break;
end while; //end hack while loop

end intrinsic;
   
            
                     
                              
                                       
                                                
                                                                  
       



           

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
  
  
  
    
                          
                            
                            
                                  
            
            
            
            
        
        
            //else
                // decrease lp by dividing by 1.3
//                precision:= LocalinfoList[i]`precision;
//                while (#solutionsList eq 0) do
//                    lp:= lp/(1.3);        // decrease lv
//                    mu:= Floor(lp/Log(p) - Valuation(logihat) + Valuation(delta2Lp)); // recompute mu
//                    assert mu gt (Valuation(delta2Lp) - Valuation(logihat));
//                    if (cp gt lp) or (lp gt hp) then
//                        break;
//                    end if;
//                    assert (cp le lp) and (lp lt hp);
//                    assert ((mu+100) le precision);
                    
//                    Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i],HeightBounds: Place:="NonArch");
//                    matBtmatB, vecc, boundForNormSquared:= pAdicLattice(LocalinfoList[i],Case,Bgam,BepsList,mu);
//                    bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
//                end while; // exits when lp is found such that there are no solutions
//                lp:= lp*(1.3);  // smallest value of lp such that there are 0 solutions
//                mu:= Floor(lp/Log(p) - Valuation(logihat) + Valuation(delta2Lp)); // recompute mu
//                assert (cp le lp) and (lp lt hp);
//                Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i],HeightBounds: Place:="NonArch");
//                matBtmatB, vecc, boundForNormSquared:= pAdicLattice(LocalinfoList[i],Case,Bgam,BepsList,mu);
//                bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
//                assert bufferWasBigEnough and (#solutionsList eq 0);


               
    //            else // otherwise we have 0 solutions; try to find a smaller bound
    //            // decrease lp until there are solutions or lp is no longer in range and (Max(0,cp) lt lv) and (lv lt hp)
    //                while (#solutionsList eq 0) do
    //                    //print "/1";
    //                    lv:= lv/(1.3);        // decrease lv
    //                    mu:= Exp(lv);
    //                    if (cv gt lv) or (lv gt hv) then
    //                        break;
    //                    end if;
    //                    assert mu gt 0;
    //                    assert (cv le lv) and (lv lt hv);
                        
    //                    Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i+nu],HeightBounds: Place:="Real");
    //                    BepsList[r]:= (BepsList[r] + mu*(3/2)*Exp(-lv))^2;
    //                    matBtmatB, vecc, boundForNormSquared:= RealLattice(LocalinfoList[i+nu],Case,Bgam,BepsList,mu);
    //                    bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
    //                end while; // exits when lp is found such that there are no solutions
    //                lv:= lv*(1.3);  // smallest value of lp such that there are 0 solutions
    //                mu:= Exp(lv);
    //                assert mu gt 0;
    //                assert (cv le lv) and (lv lt hv);
                    
    //                Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i+nu],HeightBounds: Place:="Real");
    //                BepsList[r]:= (BepsList[r] + mu*(3/2)*Exp(-lv))^2;
    //                matBtmatB, vecc, boundForNormSquared:= RealLattice(LocalinfoList[i+nu],Case,Bgam,BepsList,mu);
    //                bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
    //                assert bufferWasBigEnough and (#solutionsList eq 0);
            
            
            
            
            
           // print "BEFRORE mu,lv", mu, lv;
            while (#solutionsList eq 0) and (cv le lv) and (lv lt hv) do
              //  print "-lv", lv;
                //print "/1";
                lv:= lv-1;        // decrease lv
                mu:= Exp(lv);
                assert mu gt 0;
                assert (cv le lv) and (lv lt hv);
                
                Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i+nu],HeightBounds: Place:="Real");
                BepsList[r]:= BepsList[r] + mu*(3/2)*Exp(-lv);
                matBtmatB, vecc, boundForNormSquared:= RealLattice(LocalinfoList[i+nu],Case,Bgam,BepsList,mu);
                bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
            end while; // exits when lp is found such that there are no solutions
            lv:= lv+1;  // smallest value of lp such that there are 0 solutions
            mu:= Exp(lv);
            assert mu gt 0;
            assert (cv le lv) and (lv lt hv);
            
            Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,LocalinfoList[i+nu],HeightBounds: Place:="Real");
            BepsList[r]:= BepsList[r] + mu*(3/2)*Exp(-lv);
            matBtmatB, vecc, boundForNormSquared:= RealLattice(LocalinfoList[i+nu],Case,Bgam,BepsList,mu);
            bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=1,lllReduce:=true, breakSymmetry:= true);
            assert bufferWasBigEnough and (#solutionsList eq 0);
        
     //   print "lv", lv;
        NewHeightBounds`heightepslist[i]:= Ceiling(lv);
    end for;
    
    // update Height Bounds; ie set the vector h to the vector l and continue
    // from here on out, we will obtain solutions when using Fincke-Pohst
    HeightBounds:= NewHeightBounds;     
    
    
        
        
        
        for j in [1..r] do
            NewHeightBounds`infheightepslist[j]:= Min([aBound[i][j] : i in [1..nu]]);
        end for;
        
        



            
            
      //  end if;
            
            // decrease lp by dividing by 1.3
            lp, solutionsList:= pAdicReduction(fieldKinfo,fieldLinfo,fieldCinfo,LocalinfoList[i],Case,HeightBounds,cp,lp,hp,[],1.3: NumSolutionsInLoop:= 0, decreaseMethod:= "divide");
            // decrease lp by subtracting by Log(p)
            lp, solutionsList:= pAdicReduction(fieldKinfo,fieldLinfo,fieldCinfo,LocalinfoList[i],Case,HeightBounds,cp,lp,hp,[],Log(p): NumSolutionsInLoop:= 0, decreaseMethod:= "subtract");
     
            NewHeightBounds`heightgammalist[i]:= Ceiling(lp);
            aBound[i]:= BepsList;
            
        end for;
        aBound;
        
        for j in [1..r] do
            NewHeightBounds`infheightepslist[j]:= Min([aBound[i][j] : i in [1..nu]]);
        end for;
    end if;
end procedure;

pAdicReduction:= function(fieldKinfo, fieldLinfo, fieldCinfo, fieldLpinfo,Case,HeightBounds,cp,lp,hp,solutionsList,decreaseFactor: NumSolutionsInLoop:= 0, decreaseMethod:= "divide");
    p:= fieldLpinfo`place;
    delta1Lp:= fieldLpinfo`delta1Lp;
    delta2Lp:= fieldLpinfo`delta2Lp;
    logihat:= fieldLpinfo`logihat;
    precision:= fieldLpinfo`precision;
    
    if decreaseMethod eq "divide" then
        while (#solutionsList eq NumSolutionsInLoop) and (cp le lp) and (lp lt hp) do
            lp:= lp/(decreaseFactor);
            mu:= Floor(lp/Log(p) - Valuation(logihat) + Valuation(delta2Lp)); // recompute mu
            assert mu gt (Valuation(delta2Lp) - Valuation(logihat));
            assert (cp le lp) and (lp lt hp);
            assert ((mu+100) le precision);
            Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,fieldLpinfo,HeightBounds: Place:="NonArch");
            matBtmatB, vecc, boundForNormSquared:= pAdicLattice(fieldLpinfo,Case,Bgam,BepsList,mu);
            bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:= NumSolutionsInLoop+1,lllReduce:=true, breakSymmetry:= true);
        end while; // exits when lp is found such that there are no solutions
        lp:= lp*decreaseFactor;  // smallest value of lp such that there are 0 solutions
        mu:= Floor(lp/Log(p) - Valuation(logihat) + Valuation(delta2Lp)); // recompute mu
        Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,fieldLpinfo,HeightBounds: Place:="NonArch");
        matBtmatB, vecc, boundForNormSquared:= pAdicLattice(fieldLpinfo,Case,Bgam,BepsList,mu);
        bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=NumSolutionsInLoop+1,lllReduce:=true, breakSymmetry:= true);
        assert bufferWasBigEnough and (#solutionsList eq NumSolutionsInLoop);
    elif decreaseMethod eq "subtract" then
        while (#solutionsList eq NumSolutionsInLoop) and (cp le lp) and (lp lt hp) do
            lp:= lp -  decreaseFactor;
            mu:= Floor(lp/Log(p) - Valuation(logihat) + Valuation(delta2Lp)); // recompute mu
            assert mu gt (Valuation(delta2Lp) - Valuation(logihat));
            assert (cp le lp) and (lp lt hp);
            assert ((mu+100) le precision);
            Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,fieldLpinfo,HeightBounds: Place:="NonArch");
            matBtmatB, vecc, boundForNormSquared:= pAdicLattice(fieldLpinfo,Case,Bgam,BepsList,mu);
            bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=NumSolutionsInLoop+1,lllReduce:=true, breakSymmetry:= true);
        end while; // exits when lp is found such that there are no solutions
        lp:= lp + decreaseFactor;  // smallest value of lp such that there are 0 solutions
        mu:= Floor(lp/Log(p) - Valuation(logihat) + Valuation(delta2Lp)); // recompute mu
        Bgam,BepsList:= Ellipsoid(fieldKinfo,fieldLinfo,fieldCinfo,Case,fieldLpinfo,HeightBounds: Place:="NonArch");
        matBtmatB, vecc, boundForNormSquared:= pAdicLattice(fieldLpinfo,Case,Bgam,BepsList,mu);
        bufferWasBigEnough, solutionsList:= My_FinckePohst(matBtmatB,boundForNormSquared:center:=vecc, maxNumSolutions:=NumSolutionsInLoop+1,lllReduce:=true, breakSymmetry:= true);
        assert bufferWasBigEnough and (#solutionsList eq NumSolutionsInLoop);
    end if;
    return lp, solutionsList;
end function;



// LEFT OFF HERE; NEED TO TEST THIS CONVERSION OF SOLUTIONS TO SAMIRS;
// ALSO NEED TO TEST OUT WHAT HAPPENS to reduction
// include Samir's sieve at the end
infNorm:= function(HeightBounds,Case,allBeps);
    
    CasePrimes:= [Norm(fp) : fp in Case`ideallist];
    nu:= #Case`gammalist;
    assert #CasePrimes eq nu;
    
    VectorInfNorm:= Max([HeightBounds`heightgammalist[i]/Log(CasePrimes[i]) : i in [1..nu]]);
    
    // compute the infinity norm of matAinv (max row sum)
    matA:= Case`matA;
    tf,matAinv:= IsInvertible(matA);
    assert tf;
    
    n:= NumberOfRows(matAinv);
    RowSum:= [];
    for i in [1..n] do
        RowSum[i]:=  &+[Abs(matAinv[i,j]) : j in [1..n]];
    end for;
    MatrixInfNorm:= Max(RowSum);
    
    nBound:= MatrixInfNorm*VectorInfNorm;
    
    // bound on a;
    aBound:= [];
    aBound[1]:= Ceiling(Min([Sqrt(allBeps[i][1]) : i in [1..#allBeps]]));
    aBound[2]:= Ceiling(Min([Sqrt(allBeps[i][2]) : i in [1..nu]]));
    
    return Ceiling(nBound),Max(aBound);
end function;

    
    
  
  
