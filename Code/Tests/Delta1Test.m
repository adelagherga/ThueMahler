;; This buffer is for text that is not saved, and for Lisp evaluation.
;; To create a file, visit it with <open> and enter text in its buffer.

>     K:= fieldKinfo`field;
>     OK:= fieldKinfo`ringofintegers;
>     th:=fieldKinfo`gen;
>     epslist:= fieldKinfo`fundamentalunits;
>     r:= #epslist;
>     f:= fieldKinfo`minpoly;
>     n:= Degree(f);
>     L:= fieldLinfo`field;
>     OL:= fieldLinfo`ringofintegers;
>
>     // determine all rational primes yielding unbounded prime ideals across all cases
>     allprimes:= [];
>     for i in [1..#alphgamlist] do
for>    fplist:= alphgamlist[i]`ideallist;
for>    primelist:= alphgamlist[i]`primelist;
for>    caseprimes:= [Norm(fp) : fp in fplist];
for>    assert &and[p in primelist : p in caseprimes];
for>    for p in caseprimes do
for|for>            if p notin allprimes then
for|for|if>             Append(~allprimes, p);
for|for|if>         end if;
for|for>        end for;
for>     end for;
>     Sort(~allprimes);
>
>     allprimeInfo:= [];
>     // store < C,p,3.5.2 bound,3.5.5 bound >,
>     // where lemma 3.5.2 or 3.5.5 hold, respectively
>     lemmattaInfo:= [];
>
>     // generate a record to store relevant rational prime data across all cases
>     pInfo:= recformat<prime,ideals,Lp,logk,logdivs,mapLLp,Kp,mapKKp,mapsLL,thetaL>;
>
>     for l in [1..#allprimes] do
for>    p:= allprimes[l];
for>    pL:= Factorization(p*OL)[1][1]; // the chosen prime ideal above p in L
for>    Lp, mapLLp:= Completion(L, pL : Precision:= pAdicPrec);
for>    fprs:= [f[1] : f in Factorization(p*OK)]; // prime ideals in K over p
for>    // at least one prime ideal above p must have e(P|p)*f(P|p) = 1 to be unbounded
for>    assert &or([RamificationDegree(fp)*InertiaDegree(fp) eq 1 : fp in fprs]);
for>    eLp:= AbsoluteRamificationIndex(Lp);
for>    fLp:= AbsoluteInertiaDegree(Lp);
for>    // determine k, divisors of p^fLp - 1 for faster convergence of p-adic log, as in Ha
for>    divs:= Divisors(p^fLp -1);
for>    k:= 1;
for>    while (p^k)*(p-1) le eLp do
for|while>          k:= k+1;
for|while>      end while;
for>    thetaL:= []; // roots of th in L, grouped according to prime factorization of p in K
for>    mapsLL:= []; // automorphism of L such that mapsLL[i][j](th) = thetaL[i][j]
for>
for>    for i in [1..#fprs] do
for|for>            // roots of g(t) in L, corresponding to prime ideal fprs[i] above p in K
for|for>            thetaL[i]:= [];
for|for>            mapsLL[i]:= [];
for|for>            Kp, mapKKp:= Completion(K, fprs[i] : Precision:= pAdicPrec);
for|for>            gp:= MinimalPolynomial(mapKKp(th), PrimeField(Kp));
for|for>            allroots:= Roots(gp, Lp);
for|for>            assert RamificationDegree(fprs[i])*InertiaDegree(fprs[i]) eq #allroots;
for|for>            // verify multiplicity of all roots of g(t) is 1
for|for>            assert &and[allroots[j][2] eq 1 : j in [1..#allroots]];
for|for>            allroots:= [allroots[j][1] : j in [1..#allroots]];
for|for>
for|for>             for j in [1..#allroots] do
for|for|for>            // determine the automorphism of L sending th to the listed root of g(t) in Lp
for|for|for>            vals:= [Ordp(Lp,mapLLp(ijkL[k](L!th)) - allroots[j]) : k in [1..n]];
for|for|for>            maxval, ind:= Max(vals);
for|for|for>            assert &and[vals[i] ne maxval : i in [1..n] | i ne ind];
for|for|for>
for|for|for>            mapsLL[i][j]:= ijkL[ind];
for|for|for>            thetaL[i][j]:= ijkL[ind](L!th);
for|for|for>        end for;
for|for>            assert (IsEmpty(thetaL[i]) eq false);
for|for>        end for;
for>    assert &or([#thetaL[i] eq 1 : i in [1..#fprs]]);
for>    assert (#thetaL eq 2) or (#thetaL eq 3);
for>
for>    allprimeInfo[l]:= rec<pInfo | prime:= p,ideals:= fprs,Lp:=Lp,logk:=k,logdivs:=divs,
for>                                  mapLLp:=mapLLp,Kp:=Kp,mapKKp:=mapKKp,mapsLL:=mapsLL,
for>                                  thetaL:=thetaL>;
for>     end for;
>
>     for C in [1..#alphgamlist] do // iterate through each S-unit equation
for>    pi0jk:= [];
for>    alpha:= alphgamlist[C]`alpha;
for>    gammalist:= alphgamlist[C]`gammalist;
for>    fplist:= alphgamlist[C]`ideallist;
for>    caseprimes:= [Norm(fp) : fp in fplist];
for>    tau:= alpha*fieldKinfo`zeta;
for>    vecR:= alphgamlist[C]`vecR;
for>    matA:= alphgamlist[C]`matA;
for>
for>    for l in [1..#caseprimes] do
for|for>            p:= caseprimes[l];
for|for>            pindex:= [i : i in [1..#allprimeInfo] | allprimeInfo[i]`prime eq p];
for|for>            assert #pindex eq 1;
for|for>            pindex:= pindex[1];
for|for>            assert allprimeInfo[pindex]`prime eq p;
for|for>            fprs:= allprimeInfo[pindex]`ideals;
for|for>            thetaL:= allprimeInfo[pindex]`thetaL;
for|for>            mapsLL:= allprimeInfo[pindex]`mapsLL;
for|for>            Lp:= allprimeInfo[pindex]`Lp;
for|for>            mapLLp:= allprimeInfo[pindex]`mapLLp;
for|for>
for|for>            fp:= [fplist[i] : i in [1..#fplist] | Norm(fplist[i]) eq p];
for|for>            assert (#fp eq 1) and (fp[1] in fprs);
for|for>            fp:= fp[1];
for|for>            assert fp eq fplist[l];
for|for>            // determine and store index i0 of unbounded prime ideal fp above p
for|for>            // thus thetaL[pi0][1] and mapsLL[pi0][1] correspond to fp
for|for>            // where fp corresponds to f_1(t) such that f(t) = f_1(t)g(t) and deg(f_1(t)) = 1
for|for>            pi0:= [i : i in [1..#fprs] | fprs[i] eq fp];
for|for>            assert (#pi0 eq 1) and (#thetaL[pi0[1]] eq 1);
for|for>            pi0:= pi0[1];
for|for>            // choose indices j,k; these correspond to bounded prime ideals above p
for|for>            indjk:= [i : i in [1..#thetaL] | i ne pi0];
for|for>            if #thetaL eq 2 then
for|for|if>             // select j,k corresponding to roots of f_2(t)
for|for|if>             // here f(t) = f_1(t)f_2(t) where deg(f_2(t)) = 2
for|for|if>             assert #indjk eq 1;
for|for|if>             assert #thetaL[indjk[1]] eq 2;
for|for|if>             pj:= [indjk[1],1];
for|for|if>             pk:= [indjk[1],2];
for|for|if>             assert Ordp(Lp,mapLLp(thetaL[pj[1],pj[2]]))
for|for|if|assert>                     eq Ordp(Lp,mapLLp(thetaL[pk[1],pk[2]]));
for|for|if>         elif #thetaL eq 3 then
for|for|if>             // select j,k corresponding to root of f_2(t),f_3(t) respectively
for|for|if>             // here f(t) = f_1(t)f_2(t)f_3(t) where deg(f_2(t)) = deg(f_3(t)) = 1
for|for|if>             assert #indjk eq 2;
for|for|if>             assert (#thetaL[indjk[1]] eq 1) and (#thetaL[indjk[2]] eq 1);
for|for|if>             pj:= [indjk[1],1];
for|for|if>             pk:= [indjk[2],1];
for|for|if>         end if;
for|for>            assert thetaL[pj[1],pj[2]] ne thetaL[pk[1],pk[2]];
for|for>            discf:= Integers()!Discriminant(f);
for|for>            disctest:= ((thetaL[pi0,1] - thetaL[pj[1],pj[2]])*
for|for>                        (thetaL[pi0,1] - thetaL[pk[1],pk[2]])*
for|for>                        (thetaL[pj[1],pj[2]] - thetaL[pk[1],pk[2]]))^2;
for|for>            assert Ordp(Lp,mapLLp(discf)) eq Ordp(Lp,mapLLp(disctest));
for|for>            assert Ordp(Lp,mapLLp(discf)) eq Valuation(discf,p);
for|for>
for|for>            // generate images under the maps i0,j,k: L -> L, th -> thetaL[i][j]
for|for>            epslistL:= [ImageInL(mapsLL,L!eps) : eps in epslist];
for|for>            tauL:= ImageInL(mapsLL,tau);
for|for>            delta1L:= ((thetaL[pi0,1]-thetaL[pj[1],pj[2]])*(tauL[pk[1],pk[2]]))/
for|for>                      ((thetaL[pi0,1]-thetaL[pk[1],pk[2]])*(tauL[pj[1],pj[2]]));
for|for>            delta2L:= ((thetaL[pj[1],pj[2]]-thetaL[pk[1],pk[2]])*(tauL[pi0,1]))/
for|for>                      ((thetaL[pk[1],pk[2]]-thetaL[pi0,1])*(tauL[pj[1],pj[2]]));
for|for>            ord_delta1L:= Ordp(Lp,mapLLp(delta1L));
for|for>            ord_delta2L:= Ordp(Lp,mapLLp(delta2L));
for|for>            print Ordp(Lp,mapLLp((thetaL[pi0,1]-thetaL[pj[1],pj[2]])));
for|for>            print Ordp(Lp,mapLLp((thetaL[pi0,1]-thetaL[pk[1],pk[2]])));
for|for>            print Ordp(Lp,mapLLp(tauL[pk[1],pk[2]]));
for|for>            print Ordp(Lp,mapLLp(tauL[pj[1],pj[2]]));
for|for>            print "----------";
for|for> end for;
for> end for;
