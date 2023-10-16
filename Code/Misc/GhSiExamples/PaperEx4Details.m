/*
PaperEx4.m

This function solves the Thue--Mahler equations defined in the Example 4 of the
GhSi Thue--Mahler paper, and outputs the corresponding logfile.

Returns
    LogFile: MonStgElt
        A .txt file named "Example4Log.txt" containing all output, timings, and
	solutions.
Authors
    Adela Gherga <adelagherga@gmail.com>
    Samir Siksek <samir.siksek@gmail.com>
Created
    14 June 2022
*/

ChangeDirectory("../../TMSolver");
load "./solveThueMahler.m";
//LogFile:="../../GhSiData/Example4/Example4DetailedLog.txt";
//SetOutputFile(LogFile);
SetAutoColumns(false);
SetColumns(235);
SetClassGroupBounds("GRH");

//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++//
// Example 4 //

primelist:=[2,3,5,7,11];
a:=1;
alist:=[5,1,4,1,6,1,6,0,6,0,4,-2];

printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
printf "alist:=%o; a:=%o; primelist:=%o; \n",alist,a,primelist;
printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
time tauDeltaList:=equationsInK(alist,a,primelist);
printf "We have %o S-unit equations to solve.\n",#tauDeltaList;
printf "The ranks are %o.\n",Sort([#pr[2] : pr in tauDeltaList]);
a0:=alist[1];
K:=Universe([pr[1] : pr in tauDeltaList]
	    cat &cat[pr[2] : pr in tauDeltaList]);
K:=NumberField(K);
OK:=MaximalOrder(K);
theta:=K.1;
smallInfs:=smallSieveInfo([* *],a0,theta,200);
sols:={};
eqncount:=0;
printf "+++++++++++++++++ Part 1 +++++++++++++++++\n";

printf "Degree(K)=%o.\n",Degree(K);
u,v:=Signature(K);
printf "Signature(K)=(%o,%o).\n",u,v;
printf "Minimal polynomial for theta is %o.\n",MinimalPolynomial(theta);
deltaList:=[
    1/1953125*(62639*theta^10 - 748196*theta^9 - 4621980*theta^8 -
        22207025*theta^7 + 38965000*theta^6 - 34195000*theta^5 -
        449543750*theta^4 - 21271312500*theta^3 - 51765703125*theta^2 -
        209809765625*theta + 942912109375),
    1/390625*(-304507*theta^10 - 1286200*theta^9 - 8286278*theta^8 -
        14744530*theta^7 - 120138150*theta^6 + 295735000*theta^5 +
        31769375*theta^4 + 19645671875*theta^3 - 1856078125*theta^2 +
        159741562500*theta - 1543269140625),
    1/1953125*(-506181269733*theta^10 - 15199081379048*theta^9 +
        3417039996000*theta^8 + 20631263730850*theta^7 - 862101634598875*theta^6
        - 11248761245089375*theta^5 + 13277953474900000*theta^4 -
        47969344104562500*theta^3 - 481688292060625000*theta^2 -
        5526042413395703125*theta + 13231499496662109375),
    1/1953125*(375938718*theta^10 + 1113068513*theta^9 + 9701253830*theta^8 +
        28420450900*theta^7 + 337680104250*theta^6 + 897075371250*theta^5 +
        8807817215625*theta^4 + 17270145140625*theta^3 + 210084124843750*theta^2
        + 411927193359375*theta + 3744720025390625),
    1/1953125*(-44039*theta^10 - 174484*theta^9 - 2041150*theta^8 -
        12553050*theta^7 - 48229625*theta^6 - 380426875*theta^5 -
        367550000*theta^4 - 6470828125*theta^3 + 8499687500*theta^2 -
        60500781250*theta + 157595703125),
    1/1953125*(156*theta^10 + 1076*theta^9 + 7590*theta^8 + 32475*theta^7 +
        181375*theta^6 + 466250*theta^5 + 1753125*theta^4 - 4156250*theta^3 -
        7578125*theta^2 - 133984375*theta + 267578125),
    1/1953125*(3783*theta^10 - 10047*theta^9 - 20595*theta^8 + 94800*theta^7 +
        2714750*theta^6 - 9815000*theta^5 + 11365625*theta^4 + 6562500*theta^3 +
        1218125000*theta^2 - 6610156250*theta + 7017578125),
    1/1953125*(21*theta^10 - 169*theta^9 + 680*theta^8 - 325*theta^7 -
        2500*theta^6 - 11875*theta^5 + 459375*theta^4 - 3640625*theta^3 +
        20156250*theta^2 - 65625000*theta + 72265625),
    1/1953125*(-2386*theta^10 - 126366*theta^9 - 363925*theta^8 +
        2473650*theta^7 - 14427125*theta^6 - 87118750*theta^5 - 55203125*theta^4
        + 281968750*theta^3 - 4114296875*theta^2 - 68742968750*theta +
        152501953125),
    1/1953125*(-173*theta^10 - 1528*theta^9 - 4840*theta^8 + 6800*theta^7 +
        54125*theta^6 - 298750*theta^5 - 4609375*theta^4 - 19546875*theta^3 -
        11953125*theta^2 + 270703125*theta + 1181640625)
];
tau:=1/390625*(11114*theta^10 - 156626*theta^9 - 3960*theta^8 + 713050*theta^7 +
    3733000*theta^6 - 129663750*theta^5 + 175803125*theta^4 - 184687500*theta^3
    + 1457890625*theta^2 - 70168750000*theta + 134298828125);
assert #deltaList eq 10;
// Choose deltaList and tau as in the paper.

for i in [j : j in [1..#deltaList] | Abs(Norm(deltaList[j])) ne 1] do
    K!Generators(Factorization(ideal<OK | deltaList[i]>)[1][1])[1];
    K!Generators(Factorization(ideal<OK | deltaList[i]>)[1][1])[2];
    // Print ideal generators.
    printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
end for;

S:=&join[Support(delta*OK) : delta in deltaList];
S:=SetToSequence(S);
fn:=func<P1,P2 | Norm(P2)-Norm(P1) >;
// Sort S so that the prime ideals with largest norm come first.
Sort(~S,fn);
s:=#S;
assert &and[fact[1] in S : fact in Factorisation(tau*OK) | fact[2] lt 0];
// This is a sanity check. According to the paper, the denominator ideal
// of tau is supported on S.
c17,c20:=initialBound(tau,deltaList,S);
printf "Initial bound for B is %o.\n",c20;

printf "+++++++++++++++++ Part 2 +++++++++++++++++\n";

c22,c23:=boundConstants(K,theta,tau);
c26:=1/(2*c17);
consts:=[c17,c20,c22,c23,c26];
r:=#deltaList;
d:=Degree(K);
assert d ge 3;
assert u eq 1;
pls:=InfinitePlaces(K);
realPls:=[pl : pl in pls | LocalDegree(pl) eq 1];
cmxPls:=[pl : pl in pls | LocalDegree(pl) eq 2];
assert #realPls eq u;
assert #cmxPls eq v;
assert d eq u+2*v;

vecBList:=[];
expSbdsList:=[];
i:=1;
printf "Dealing with the %o-st real embedding.\n",i;
sigma:=realPls[i];

w:=u+v-2;
s:=#S;
n:=r+v;
assert d eq u+2*v;
assert s eq (r-(u+v-1));
assert &and[Abs(Norm(delta)) eq 1 : delta in deltaList[1..u+v-1]];
assert &and[Abs(Norm(delta)) ne 1 : delta in deltaList[u+v..r]];
c17,c20,c22,c23,c26:=Explode(consts);
constsDivc25,sigma2:=boundConstantsDivc25(K,theta,tau,c23,sigma);
c27divc25,c28divc25,c29divc25:=Explode(constsDivc25);
cBinf:=c20;
vecB:=[cBinf : i in [1..r]];
cB2:=Sqrt(&+[i^2 : i in vecB]); // The L^2 norm of the vector b.
printf "The initial L^2 bound, cB2, is %o.\n",cB2;
absMinv,vecUpp:=nonUnitExps(K,S,deltaList,vecB);
vecs:={};

expSbds:=[];
c21:=0;
assert Norm(S[1]) eq 11;
i:=1;
fp:=S[i];

p:=Characteristic(ResidueClassField(fp));
assert Degree(fp) eq 1;
assert Valuation(p*OK,fp) eq 1;
fa:=p*OK/fp;
for fact in Factorisation(fa) do
    assert &and[Valuation(delta*OK,fact[1]) eq 0 : delta in deltaList];
end for;
assert cB2 ge 1;
printf "Choose k larger than %o.\n",r*Log(cB2)/((d-2)*Log(p));
k:=Floor(r*Log(cB2)/((d-2)*Log(p)));
printf "Try k=%o.\n",k+1;
k:=k+1;
mpol:=MinimalPolynomial(theta);
lcf:=LeadingCoefficient(mpol);
assert lcf eq 1; // Surely theta is an algebraic integer!
hprec:=2*Valuation(Discriminant(mpol),p)+k+1;
rts:=Roots(mpol,pAdicRing(p,hprec));
rts:=[Integers()!r[1] : r in rts];
rts:=[r : r in rts | Valuation((r-theta)*OK,fp) ge k];
assert #rts ge 1;
theta0:=rts[1]; // Thus ord_{fp}(theta-theta_0) \ge k.
taufacts:=Factorisation(tau*OK);
taunumfacts:=[fact : fact in taufacts | fact[2] gt 0];
// The factorization of the numerator ideal of tau*OK.
if #taunumfacts eq 0 then
    taunum:=1*OK;
else
    taunum:=&*[fact[1]^(fact[2]) : fact in taunumfacts];
end if;
// Now taunum is the numerator ideal of tau.
assert (taunum+fa^k) eq ((theta-theta0)*OK+fa^k);
printf "Condition (i) of the proposition does not hold.\n";
fb:=fa^k/(taunum+fa^k);
tau0:=(theta0-theta)/tau;
for fact in Factorisation(fb) do
    assert Valuation(tau0*OK,fact[1]) eq 0; // Sanity check!
end for;
if (fb eq ideal<OK|1>) then
    kprime:= 0;
else
    kprime:=Max([Ceiling(fact[2]/Valuation(p*OK,fact[1])) :
		 fact in Factorisation(fb)]);
end if;
printf "kprime is %o.\n",kprime;
pkprime:=p^kprime;
assert Denominator(pkprime*OK/fb) eq 1;
if kprime ge 1 then
    assert Denominator((p^(kprime-1)*OK)/fb) ne 1;
end if;
// kprime really is the smallest positive integer such
// that fb divides p^kprime.
Zmod:=Integers(pkprime);
U,eps:=UnitGroup(Zmod);
gens:=[Integers()!(u@eps) : u in OrderedGenerators(U)];
if IsOdd(p) and kprime ge 1 then
    assert #gens eq 1; // Sanity check: there is a primitive root.
end if;
alphaList:=[K!tau0] cat [K!g : g in gens] cat
	   [K!delta: delta in deltaList];
D,alphaList:=multGroup(fb,alphaList);
// D is (isomorphic to) the group (OK/fb)^* and alphaList is the image
// in D of the original alphaList defined above, i.e. the images in D
// of tau0, the generators of (\Z/p^\prime)^*, and the \delta_i.
tau0im:=alphaList[1];
alphaList:=alphaList[2..#alphaList];
gensim:=alphaList[1..#gens];
alphaList:=alphaList[(#gens+1)..#alphaList];
assert #alphaList eq #deltaList;
G,pi:=quo<D | sub<D | gensim>>;
tau0im:=pi(tau0im);
alphaList:=[pi(alpha) : alpha in alphaList];
assert #alphaList eq r;
Zr:=FreeAbelianGroup(r);
phi:=hom<Zr->G | alphaList>;
printf "Is phi surgective? %o.\n",IsSurjective(phi);
assert (tau0im in Image(phi));
w:=tau0im@@phi;
L:=Kernel(phi);
ZZr:=StandardLattice(r);
LL:=sub<ZZr | [ ZZr!(Eltseq((Zr!l))) : l in OrderedGenerators(L)]>;
ww:=ZZr!Eltseq(Zr!w);
printf "The lattice has index %o.\n",Factorization(Integers()!#G);
// ClosestVectors is error-prone in Magma V2.26-10.
// If there are no vectors in P, then there are no vectors v in w+L
// such that |v+w| < cB2.
P:=CloseVectorsProcess(LL,-ww,Integers()!50*Floor(cB2^2));
// until DLwsq gt cB2^2; // We keep increasing k until condtion (iii)
norms:=[];
while (IsEmpty(P) eq false) do
    Append(~norms,Norm(NextVector(P)+ww));
end while;
printf "D(L,w):=%o.\n",Sqrt(Min(norms));

printf "Try k-1=%o.\n",k-1;
k:=k-1;
mpol:=MinimalPolynomial(theta);
lcf:=LeadingCoefficient(mpol);
assert lcf eq 1; // Surely theta is an algebraic integer!
hprec:=2*Valuation(Discriminant(mpol),p)+k+1;
rts:=Roots(mpol,pAdicRing(p,hprec));
rts:=[Integers()!r[1] : r in rts];
rts:=[r : r in rts | Valuation((r-theta)*OK,fp) ge k];
assert #rts ge 1;
theta0:=rts[1]; // Thus ord_{fp}(theta-theta_0) \ge k.
taufacts:=Factorisation(tau*OK);
taunumfacts:=[fact : fact in taufacts | fact[2] gt 0];
// The factorization of the numerator ideal of tau*OK.
if #taunumfacts eq 0 then
    taunum:=1*OK;
else
    taunum:=&*[fact[1]^(fact[2]) : fact in taunumfacts];
end if;
// Now taunum is the numerator ideal of tau.
assert (taunum+fa^k) eq ((theta-theta0)*OK+fa^k);
printf "Condition (i) of the proposition does not hold.\n";
fb:=fa^k/(taunum+fa^k);
tau0:=(theta0-theta)/tau;
for fact in Factorisation(fb) do
    assert Valuation(tau0*OK,fact[1]) eq 0; // Sanity check!
end for;
if (fb eq ideal<OK|1>) then
    kprime:= 0;
else
    kprime:=Max([Ceiling(fact[2]/Valuation(p*OK,fact[1])) :
		 fact in Factorisation(fb)]);
end if;
printf "kprime is %o.\n",kprime;
pkprime:=p^kprime;
assert Denominator(pkprime*OK/fb) eq 1;
if kprime ge 1 then
    assert Denominator((p^(kprime-1)*OK)/fb) ne 1;
end if;
// kprime really is the smallest positive integer such
// that fb divides p^kprime.
Zmod:=Integers(pkprime);
U,eps:=UnitGroup(Zmod);
gens:=[Integers()!(u@eps) : u in OrderedGenerators(U)];
if IsOdd(p) and kprime ge 1 then
    assert #gens eq 1; // Sanity check: there is a primitive root.
end if;
alphaList:=[K!tau0] cat [K!g : g in gens] cat
	   [K!delta: delta in deltaList];
D,alphaList:=multGroup(fb,alphaList);
// D is (isomorphic to) the group (OK/fb)^* and alphaList is the image
// in D of the original alphaList defined above, i.e. the images in D
// of tau0, the generators of (\Z/p^\prime)^*, and the \delta_i.
tau0im:=alphaList[1];
alphaList:=alphaList[2..#alphaList];
gensim:=alphaList[1..#gens];
alphaList:=alphaList[(#gens+1)..#alphaList];
assert #alphaList eq #deltaList;
G,pi:=quo<D | sub<D | gensim>>;
tau0im:=pi(tau0im);
alphaList:=[pi(alpha) : alpha in alphaList];
assert #alphaList eq r;
Zr:=FreeAbelianGroup(r);
phi:=hom<Zr->G | alphaList>;
printf "Is phi surgective? %o.\n",IsSurjective(phi);
assert (tau0im in Image(phi));
w:=tau0im@@phi;
L:=Kernel(phi);
ZZr:=StandardLattice(r);
LL:=sub<ZZr | [ ZZr!(Eltseq((Zr!l))) : l in OrderedGenerators(L)]>;
ww:=ZZr!Eltseq(Zr!w);
printf "The lattice has index I^(1/10)=%o.\n",#G^(1/10);
// ClosestVectors is error-prone in Magma V2.26-10.
// If there are no vectors in P, then there are no vectors v in w+L
// such that |v+w| < cB2.
P:=CloseVectorsProcess(LL,-ww,Integers()!Floor(cB2^2));
// until DLwsq gt cB2^2; // We keep increasing k until condtion (iii)
norms:=[];
while (IsEmpty(P) eq false) do
    Append(~norms,Norm(NextVector(P)+ww));
end while;
printf "D(L,w):=%o.\n",Sqrt(Min(norms));

c21,expSbds,vecUpp,vecB:=c21Func(tau,deltaList,S,absMinv,vecUpp,vecB);
printf "Upper bounds are %o.\n",expSbds;

printf "+++++++++++++++++ Part 3 +++++++++++++++++\n";
c24:=c21+c22+(u-1)*Log(Max(1,1/c23));
c25:=Exp(c24);
c27:=c27divc25*c25;
c28:=c28divc25*c25;
c29:=[c29divc25[j]*c25 : j in [1..(u+v)]];
if u eq 1 then
    c30:=Max([2*c17*c24,Log(2*c28)/c26]);
elif v eq 0 then
    c30:=Max([2*c17*c24,Log(2*c27)/c26]);
else
    c30:=Max([2*c17*c24,Log(2*c27)/c26,Log(2*c28)/c26]);
end if;
printf "c21=%o.\n",c21;
printf "c22=%o.\n",c22;
printf "c23=%o.\n",c23;
printf "c24=%o.\n",c24;
printf "c25=%o.\n",c25;
printf "c26=%o.\n",c26;
printf "c27=%o.\n",c27;
printf "c28=%o.\n",c28;
printf "c29=%o.\n",c29;
printf "c30=%o.\n",c30;

w:=u+v-2;
s:=#S;
n:=r+v;
printf "w=%o.\n",u+v-2;

cBinf:=Max(vecB);
cB1:=&+[Abs(i) : i in vecB];
cB2:=Sqrt(&+[i^2 : i in vecB]);
cA1:=(1+cB1)/2;
cA2:=(1+cB1) + 1/(2*Pi(RealField()));
cB3:=0;
cB4:=0;
for j in [1..w] do
    cB3:=cB3 + (c29[2] + c29[j+2])^2;
    cB4:=cB4 + cA1*(c29[2] + c29[j+2]);
end for;
for j in [1..v] do
    cB3:=cB3 + (c29[u+j])^2;
    cB4:=cB4 + cA2*(c29[u+j]);
end for;
cB5:=(cB2^2 - w*cBinf^2 + w*cA1^2 + v*cA2^2)^(1/2);
C:=Ceiling(cB5^(n/(d-2)));
printf "C=%o.\n",RealField()!C;
ZZn:=StandardLattice(n);
M,ww:=approxLattice(tau,deltaList,S,sigma,sigma2,C);
assert (Rank(M) eq n);
printf "[Z^{15} : L]=%o.\n",RealField()!Abs(Determinant(M));
ww:=ZZn!ww;
LL:=Lattice(M);
assert ww notin LL;
DLwsq:=distanceLBsq(LL,-ww);
tf:=DLwsq gt cB5^2;
if (tf eq false) then
    shortvecs,DLwsq:=distanceLBsq2(LL,ww,cB5^2);
    vecs:=vecs join {(vv*ChangeRing(M,Rationals())^(-1))[1]
		     : vv in shortvecs};
    tf:=DLwsq gt cB5^2;
end if;
printf "D(L,w)=%o.\n",RealField()!Sqrt(DLwsq);
printf "D(L,w) > cB5 : %o.\n",tf;
denom:=(cB3*(DLwsq-cB5^2) + cB4^2)^(1/2) - cB4;
cBinfNew:=(1/c26)*Log((2*C*cB3)/denom);
cBinfNew:=Max(c30,cBinfNew);
if cBinfNew lt 10^10 then
    cBinfNew:=Floor(cBinfNew);
end if;
if cBinfNew lt cBinf then
    vprintf User1: "The new bound is %o.\n",cBinfNew;
    cBinf:=cBinfNew;
    for i in [1..r] do
	if cBinf lt vecB[i] then
	    vecB[i]:=cBinf;
	end if;
    end for;
else
    finished:=true;
end if;
if (cBinf eq 0) then
    finished:=true;
end if;
printf "New bound is %o.\n",cBinfNew;

c21,expSbds,vecUpp,vecB:=c21Func(tau,deltaList,S,absMinv,vecUpp,vecB);
printf "Upper bounds are %o.\n",expSbds;












vecsig,vecBsig,expSbds:=
	    fixedRealEmbeddingRed(tau,deltaList,S,consts,sigma : verb:=verb);
	Append(~vecBList,vecBsig);
	Append(~expSbdsList,expSbds);
	vecs:=vecs join vecsig;
    end for;





c22,c23:=boundConstants(K,theta,tau);
c26:=1/(2*c17);
consts:=[c17,c20,c22,c23,c26];





time sols:=solveThueMahler(alist,a,primelist);
printf "sols:=%o\n",sols;
printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
printf "Timing under GRH\n";
SetClassGroupBounds("GRH");
time sols:=solveThueMahler(alist,a,primelist);
printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
printf "Total time: %o",Cputime();
exit;
