freeze;

intrinsic TMAllCases(C::[RngIntElt],p::[RngIntElt],A::RngIntElt,LogFile::MonStgElt,OutFile::MonStgElt,FindAll::BoolElt) -> []
{}
////////////////////////////////////////////////////
//Description of Input
////////////////////////////////////////////////////
/*
LogFile is a string giving the name of the log file
OutFile is a string giving the name of the output file

FindAll is a boolean variable. If FindAll is false, 
the function only finds the small solutions of the 
Thue-Mahler equation. Otherwise, it finds all the 
solutions.

C is the (integer) sequence of coefficients of F(x,y).
C[i+1] = c_i for i = 0,...,n from (3).
Note that the coefficient c_0 of x^n is entered explicity. 
It is NOT assumed that c_0 = 1.
It is assumed that c_0 neq 0.

p is the sequence of rational primes. p[i]=p_i from (3)

A is the integer a from (3).

It is NOT assumed that (a,p_i)=1 for i=1,..,v.

If F is not irreducible, an error is raised.

The function checks whether the equation has solutions mod q 
for each prime q <= 151 in p, each prime q<=151 dividing a, and every other prime 
q <= 101.

For the example equation solved in [TW2], we would use
C:=[1,-23,5,24];
p:=[2,3,5,7];
A:=1;
LogFile:="log.txt";
//LogFile:="output/log.txt";
OutFile:="out.txt";
*/
////////////////////////////////////////////////
//Description of Output:
////////////////////////////////////////////////
/*
The list of solutions [X,Y,z_1,...,z_v] of the Thue-Mahler 
equation with gcd(X,Y)=1 and gcd(c_0,Y) = 1.
*/
///////////////////////////////////////////////
PrintFile(OutFile,"////////////////////////////////////////");
fprintf OutFile, "C:=%o; p:=%o; A:=%o;\n", C, p, A;
PrintFile(LogFile,"////////////////////////////////////////");
//fprintf LogFile, "C:=%o; p:=%o; A:=%o;", C, p, A;
printf "C:=%o; p:=%o; A:=%o;\n", C, p, A;

LogFileOUtFile:=[LogFile,OutFile];

DoneAllCases:=false;
SOL2:=[];
NumberOfCasesInBatch:=700;
StartCase:=0;
EndCase:=0;


while DoneAllCases eq false do
StartCase:=EndCase+1;
EndCase:=EndCase+NumberOfCasesInBatch;
StartEndCase:=[StartCase,EndCase];
SOL1:=TMCases(C,p,A,LogFileOUtFile,FindAll,StartEndCase);
if not IsEmpty(SOL1) then
if SOL1[1] eq [-1] then
DoneAllCases:=true;
else
for x in SOL1 do
Include(~SOL2,x);
end for;
end if;
end if;
end while;

PrintFile(OutFile, "Solutions For All Cases:");
PrintFile(OutFile, SOL2);

//PrintFile(LogFile, "Solutions For All Cases:");
//PrintFile(LogFile, SOL2);
print("Solutions For All Cases:");
return SOL2;

end intrinsic;



intrinsic TMCases(C::[RngIntElt],p::[RngIntElt],A::RngIntElt,LogFileOutFile::[MonStgElt],FindAll::BoolElt,StartEndCase::[RngIntElt]) -> []
{}
////////////////////////////////////////////////////
//Description of Input
////////////////////////////////////////////////////
/*

StartEndCase:=[StartCase,EndCase];
StartCase and EndCase are positive integers. They specify which cases will be considered.

LogFileOutFile:=[LogFile,OUtFile];
LogFile is a string giving the name of the log file
OutFile is a string giving the name of the output file

FindAll is a boolean variable. If FindAll is false, 
the function only finds the small solutions of the 
Thue-Mahler equation. Otherwise, it finds all the 
solutions.

C is the (integer) sequence of coefficients of F(x,y).
C[i+1] = c_i for i = 0,...,n from (3).
Note that the coefficient c_0 of x^n is entered explicity. 
It is NOT assumed that c_0 = 1.
It is assumed that c_0 neq 0.

p is the sequence of rational primes. p[i]=p_i from (3)

A is the integer a from (3).

It is NOT assumed that (a,p_i)=1 for i=1,..,v.

If F is not irreducible, an error is raised.

The function checks whether the equation has solutions mod q 
for each prime q <= 151 in p, each prime q<=151 dividing a, and every other prime 
q <= 101.

For the example equation solved in [TW2], we would use
C:=[1,-23,5,24];
p:=[2,3,5,7];
A:=1;
LogFile:="log.txt";
//LogFile:="output/log.txt";
OutFile:="out.txt";
*/
////////////////////////////////////////////////
//Description of Output:
////////////////////////////////////////////////
/*
The list of solutions [X,Y,z_1,...,z_v] of the Thue-Mahler 
equation with gcd(X,Y)=1 and gcd(c_0,Y) = 1 that come from cases
i=StartCases to i=FinalCases.
*/
///////////////////////////////////////////////
StartCase:=StartEndCase[1];
EndCase:=StartEndCase[2];
LogFile:=LogFileOutFile[1];
OutFile:=LogFileOutFile[2];

PrintFile(OutFile,"////////////////////////////////////////");
fprintf OutFile, "C:=%o; p:=%o; A:=%o;\n", C, p, A;
fprintf OutFile, "StartCase:=%o; EndCase:=%o;\n", StartCase, EndCase;
PrintFile(LogFile,"////////////////////////////////////////");
//fprintf LogFile, "C:=%o; p:=%o; A:=%o;", C, p, A;
printf "C:=%o; p:=%o; A:=%o;\n", C, p, A;
printf "StartCase:=%o; EndCase:=%o;\n", StartCase, EndCase;

n:=#C-1;
v:=#p;
originalv:=v;
c:=[];
b:=[];
for i:=1 to n do
c[i]:=C[i+1]*C[0+1]^(i-1);
end for;
a:=C[0+1]^(n-1)*A;
for i:=1 to originalv do
b[i]:=Valuation(a,p[i]);
a:=a/(p[i]^b[i]);
end for;
a:=Integers() ! a;

if FIsIrreducible(c) then
else
print("F is reducible. The algorithm requires F to be irreducible.");
return [[-1]];
end if;

N:=[Min([Max(p),151]),Min([Abs(a),151]),101];
LacksLocalSolutions:=false;
//OriginalIndicesOfRemovedPrimes:=[[-1]];
OriginalIndicesOfRemovedPrimes:=[];

cpaN:=[*c,p,a,N*];
Local(~cpaN,~LacksLocalSolutions,~OriginalIndicesOfRemovedPrimes,~LogFile);
c:=cpaN[1]; p:=cpaN[2]; a:=cpaN[3]; N:=cpaN[4];
if LacksLocalSolutions then return [[-1]]; end if;


time SOL1:=TdWCases(c,p,a,LogFileOutFile,FindAll,StartEndCase);

if not IsEmpty(SOL1) then
if SOL1[1] eq [-1] then
return SOL1;
end if;
end if;

SOL2:=[];
sol2:=[];

for sol1 in SOL1 do

//X:=sol1[1];
//if IsDivisibleBy(X,C[0+1]) then
//x:=X/C[0+1];
if IsDivisibleBy(sol1[1],C[0+1]) then
x:=sol1[1]/C[0+1];    
sol2[1]:=Integers() ! x;
sol2[2]:=sol1[2];

i:=1; //index for sol1
for k:=1 to originalv do

if k in OriginalIndicesOfRemovedPrimes then

sol2[2+k]:=0-b[k];
if sol2[2+k] lt 0 then continue sol1; end if;

else

sol2[2+k]:=sol1[2+i]-b[k];
i+:=1;
if sol2[2+k] lt 0 then continue sol1; end if;

end if;

end for; //end k loop

Append(~SOL2,sol2);
end if;

end for; //end sol1 loop


PrintFile(OutFile, "Solutions:");
PrintFile(OutFile, SOL2);

PrintFile(LogFile, "Solutions:");
//PrintFile(LogFile, SOL2);
return SOL2;

end intrinsic;



intrinsic FIsIrreducible(c::[RngIntElt]) -> BoolElt
{}
////////////////////////////////////////////////////
//Description of Input
////////////////////////////////////////////////////
/*
c is the (integer) sequence of coefficients of F(x,y). 
c[i]=c_i from (3). 
The coefficient c_0 of x^n is not to be entered.  
It is assumed that c_0=1.
*/
////////////////////////////////////////////////////
//Description of Output
////////////////////////////////////////////////////
/*
Outputs true if F(x,y) is irreducible.
Outputs false if F(x,y) is reducible.
*/
//////////////////////////////////////
n:=#c;
Zxy<x,y>:=PolynomialRing(IntegerRing(), 2); 
F:=x^n+c[n]*y^n;
for i:=1 to n-1 do
F:=F+c[i]*x^(n-i)*y^i;
end for;
return IsIrreducible(F);
end intrinsic;





intrinsic HasSolutionModqWhereqDividesRHS(c::[RngIntElt],q::RngIntElt) -> BoolElt
{}
////////////////////////////////////////////////////
//Description of Input
////////////////////////////////////////////////////
/*
c is the (integer) sequence of coefficients of F(x,y). 
c[i]=c_i from (3). The 
coefficient c_0 of x^n is not to be entered.  
It is assumed that c_0=1.  
It is also assumed that F(x,y) is irreducible.

p is the sequence of rational primes. p[i]=p_i from (3).

**q is a prime dividing RHS = a*p[1]^z[1]*...*p[v]^z[v]**

a is the integer a from (3).

It is assumed that (a,p_i)=1 for i=1,..,v.
  
For the example equation solved in [TW2], we would use
c:=[-23,5,24];
p:=[2,3,5,7];
a:=1;
N:=53; (for example)
*/
////////////////////////////////////////////////////
//Description of Output
////////////////////////////////////////////////////
/*
Returns true if the equation has a solution mod q.
Returns false otherwise.

Note: If the function returns false, and if q is a prime in p, and then the equation has no solution with the exponent of q positive.
*/
/////////////////////////////////////////////////////
n:=#c;
Zmodq:=FiniteField(q, 1);
flag:=false;

//XY = Zmodq x Zmodq - {(0,0)}
XY:=[];
for x in Zmodq do
for y in Zmodq do
Append(~XY,[x,y]);
end for;
end for;
Remove(~XY, 1);

for xy in XY do
/*
For all integers a,b not both zero, there are integers x,y 
such that x = a (mod q), y = b (mod q), and gcd(x,y) = 1.
So we only need to exclude the case x = y = 0 (mod q) to 
account for the condition (x,y)=1.
*/
x:=xy[1];
y:=xy[2];
LHS:=x^n + c[n]*y^n;
for i:=1 to n-1 do
LHS:=LHS+c[i]*x^(n-i)*y^i;
end for;
if IsZero(LHS) then //there is a solution mod q
flag:=true;  
break xy;
end if;

end for; //end xy loop
return flag;
end intrinsic;






intrinsic HasSolutionModqWhereqDoesNotDivideRHS(c::[RngIntElt],p::[RngIntElt],a::RngIntElt,q::RngIntElt) -> BoolElt
{}
////////////////////////////////////////////////////
//Description of Input
////////////////////////////////////////////////////
/*
c is the (integer) sequence of coefficients of F(x,y). 
c[i]=c_i from (3). The 
coefficient c_0 of x^n is not to be entered.  
It is assumed that c_0=1.  
It is also assumed that F(x,y) is irreducible.

p is the sequence of rational primes. p[i]=p_i from (3).

**q is a prime NOT dividing RHS = a*p[1]^z[1]*...*p[v]^z[v]**
**q is NOT in p**

a is the integer a from (3).

It is assumed that (a,p_i)=1 for i=1,..,v.
  
For the example equation solved in [TW2], we would use
c:=[-23,5,24];
p:=[2,3,5,7];
a:=1;
N:=53; (for example)
*/
////////////////////////////////////////////////////
//Description of Output
////////////////////////////////////////////////////
/*
Returns true if the equation has a solution mod q.
Returns false otherwise.
*/
/////////////////////////////////////////////////////
n:=#c;
v:=#p;
Zmodq:=FiniteField(q, 1);
aq:=Zmodq ! a;
pq:=[];
for i:=1 to v do
pq[i]:=Zmodq ! p[i];
end for;
z:=[];
for i:=1 to v do
z[i]:=0;
end for;
flag:=false;

//XY = Zmodq x Zmodq - {(0,0)}
XY:=[];
for x in Zmodq do
for y in Zmodq do
Append(~XY,[x,y]);
end for;
end for;
Remove(~XY, 1);

procedure rec(k,~z,~flag)

if k le v then

for i:=0 to Order(pq[k])-1 do
z[k]:=i;
rec(k+1,~z,~flag);
if flag eq true then break i; end if;
end for;

else

for xy in XY do
/*
For all integers a,b not both zero, there are integers x,y 
such that x = a (mod q), y = b (mod q), and gcd(x,y) = 1.
So we only need to exclude the case x = y = 0 (mod q) to 
account for the condition (x,y)=1.
*/
x:=xy[1];
y:=xy[2];
LHS:=x^n + c[n]*y^n;
for i:=1 to n-1 do
LHS:=LHS+c[i]*x^(n-i)*y^i;
end for;

RHS:=aq;
for i:=1 to v do
RHS:=RHS*pq[i]^z[i];
end for;

if IsZero(LHS-RHS) then //there is a solution mod q
flag:=true;  
break xy;
end if;

end for; //end xy loop

end if;

end procedure;

rec(1,~z,~flag);
return flag;

end intrinsic;



intrinsic Local(~cpaN::List,~LacksLocalSolutions::BoolElt,~OriginalIndicesOfRemovedPrimes::SeqEnum,~LogFile::MonStgElt)
{}
c:=cpaN[1];
p:=cpaN[2];
a:=cpaN[3];
N:=cpaN[4];
////////////////////////////////////////////////////
//Description of Input
////////////////////////////////////////////////////
/*
c is the (integer) sequence of coefficients of F(x,y). 
c[i]=c_i from (3). The 
coefficient c_0 of x^n is not to be entered.  
It is assumed that c_0=1.  
It is also assumed that F(x,y) is irreducible.

p is the sequence of rational primes. p[i]=p_i from (3)

a is the integer a from (3).

It is assumed that (a,p_i)=1 for i=1,..,v.

It is assumed that N is a sequence of three positive integers.

The value of LacksLocalSolutions has no meaning as input.

It is assumed that OriginalIndicesOfRemovedPrimes = [].

For the example equation solved in [TW2], we would use
c:=[-23,5,24];
p:=[2,3,5,7];
a:=1;
N:=[Max(p),Abs(a),101]; (for example)
LogFile:="log.txt";
*/
////////////////////////////////////////////////////
//Description
////////////////////////////////////////////////////
/*
1. For each p[i] <= N[1], we check if the equation has a solution mod p[i]. 
If the equation has no solutions modulo p[i], then we set 
LacksLocalSolutions:=true and exit. If the equation has solutions modulo 
p[i] when the exponent z[i]=0, but has no solutions modulo p[i] when the exponent z[i]>0, then we remove p[i] from the list of primes p. We also keep track of the original indices of the removed primes in the sequence 
OriginalIndicesOfRemovedPrimes.

2. We check if the equation has solutions mod q for each prime q <= N[2] 
which divides a. If the equation has no solutions mod q, then then we set LacksLocalSolutions:=true and exit.

3. We check if the equation has solutions mod q for each prime q <= N[3]. 
If the equation has no solutions mod q, then then we set LacksLocalSolutions:=true and exit.

4. If the function makes it this far, the equation has local solutions for 
every prime we have tested. We set LacksLocalSolutions:=false and exit.

Note: Large primes mean checking the congruences can take a long time. 
The purpose of N is to let use avoid these large primes to save time.
*/
/////////////////////////////////////////////////// 
for j:=0 to 0 do //this loop is a hack to let us exit when we want 
originalv:=#p;
v:=originalv;  //current size of p

i:=1; //i = index in current p of current prime
for k:=1 to originalv do //k = index in orginal p of current prime
if p[i] le N[1] then

if HasSolutionModqWhereqDoesNotDivideRHS(c,Remove(p,i),a,p[i]) then

if HasSolutionModqWhereqDividesRHS(c,p[i]) then
else 
fprintf LogFile, "No solutions with positive exponent of %o\n", p[i];
Remove(~p,i);
i-:=1;
v-:=1;
Append(~OriginalIndicesOfRemovedPrimes,k); 
//k = original index of removed prime
end if;

else

if HasSolutionModqWhereqDividesRHS(c,p[i]) then
else
LacksLocalSolutions:=true; 
printf "No solutions mod %o\n", p[i];
break j;
end if;

end if;

end if;
i+:=1;
end for; //end k loop



PrimeDivisorsOfa:=PrimeDivisors(a);
for q in PrimeDivisorsOfa do
if q le N[2] then
if HasSolutionModqWhereqDividesRHS(c,q) then
else
LacksLocalSolutions:=true;
printf "No solutions mod %o\n", q;
break j;
end if;
end if;
end for;


Q:=PrimesUpTo(N[3]);
for q in p do
Exclude(~Q,q);
end for;
for q in PrimeDivisorsOfa do
Exclude(~Q,q);
end for;

for q in Q do
if HasSolutionModqWhereqDoesNotDivideRHS(c,p,a,q) then
else
LacksLocalSolutions:=true;
printf "No solutions mod %o\n", q;
break j;
end if;
end for;

LacksLocalSolutions:=false;

end for; //end j
cpaN:=[*c,p,a,N*];
end intrinsic;


intrinsic TdWCases(c::[RngIntElt],p::[RngIntElt],a::RngIntElt,LogFileOutFile::[MonStgElt],FindAll::BoolElt,StartEndCase::[RngIntElt]) -> []
{Return the solutions of the Thue-Mahler equation}
//SetOutputFile("intout.txt": Overwrite := true);

////////////////////////////////////////////////////
//Description of Input
////////////////////////////////////////////////////
/*
LogFile is a string giving the name of the log file
OutFile is a string giving the name of the output file

FindAll is a boolean variable. If FindAll is false, 
the function only finds the small solutions of the 
Thue-Mahler equation. Otherwise, it finds all the 
solutions.

c is the (integer) sequence of coefficients of F(x,y). 
c[i]=c_i from (3). 
The coefficient c_0 of x^n is not to be entered.  
It is assumed that c_0=1. 
It is also assumed that F(x,y) is irreducible.

p is the sequence of rational primes. p[i]=p_i from (3)

a is the integer a from (3).

It is assumed that (a,p_i)=1 for i=1,..,v.
  
For the example equation solved in [TW2], we would use
c:=[-23,5,24];
p:=[2,3,5,7];
a:=1; 
LogFile:="output/log.txt";
*/

///////////////////////////////////////////////
//Description of Output:
////////////////////////////////////////////////
/*
The list of solutions [X,Y,z_1,...,z_v] of the Thue-Mahler 
equation with gcd(X,Y)=1.
*/

StartCase:=StartEndCase[1];
EndCase:=StartEndCase[2];
LogFile:=LogFileOutFile[1];
OutFile:=LogFileOutFile[2];

////////////////////////////////////////////////////////
//Define the n = degree of g(t) and v = number of primes
///////////////////////////////////////////////////////
n:=#c;  //degree of F(t,1)=g(t)
v:=#p;  //number of primes 

////////////////////////////////////////////////////
//List of Solutions
////////////////////////////////////////////////////
Solutions:=[]; //to be filled
//SolutionsTest:=[];
//ExceptionalTuplesTest:=[];


//////////////////////////////////////////////
//Define g and compute its discriminant
/////////////////////////////////////////////
Zt<t>:=PolynomialRing(Integers());
g:=t^n+c[n];
for i:=1 to n-1 do
g:=g+c[i]*t^(n-i);
end for;

DiscriminantOfg:=Discriminant(g);

//////////////////////////////////////////////////
//Define K and compute number field data
//////////////////////////////////////////////////
//define K=Q(theta)

K<theta>:=NumberField(g);

//Compute the ring of integers OK of K
OK:=MaximalOrder(K); 

//Compute an integral basis for K
IntegralBasisK:=IntegralBasis(K);

//For each element of the integral basis for K, compute its 
//coefficients on the power basis of K: 1,theta,...,theta^{n-1}
CoefficientsOfIntegralBasisElement:=[];
for i:=1 to n do
CoefficientsOfIntegralBasisElement[i]:=
Eltseq(IntegralBasisK[i]);
end for;

/*
//TEST
fprintf LogFile, "IntegralBasisK = %o\n", IntegralBasisK;
fprintf LogFile, "CoefficientsOfIntegralBasisElement = %o\n", CoefficientsOfIntegralBasisElement;
CoefficientsOfIntegralBasisElement[1][1]*theta^(1-1) + CoefficientsOfIntegralBasisElement[1][2]*theta^(2-1) + CoefficientsOfIntegralBasisElement[1][3]*theta^(3-1) eq
IntegralBasisK[1];
CoefficientsOfIntegralBasisElement[2][1]*theta^(1-1) + CoefficientsOfIntegralBasisElement[2][2]*theta^(2-1) + CoefficientsOfIntegralBasisElement[2][3]*theta^(3-1) eq
IntegralBasisK[2];
CoefficientsOfIntegralBasisElement[3][1]*theta^(1-1) + CoefficientsOfIntegralBasisElement[3][2]*theta^(2-1) + CoefficientsOfIntegralBasisElement[3][3]*theta^(3-1) eq
IntegralBasisK[3];
*/

//s = number of real embeddings, 2t = number of complex 
//embeddings
s,t:=Signature(K);

//number of fundamental units
r:=s+t-1; 

//Compute a set of fundamental units and 
//express them as elements in OK in terms of the integral basis
//they are represented by their coefficients on the integral basis
U,psi:=UnitGroup(OK);
eps:=[];
for i:= 1 to r do
eps[i]:=psi(U.(i+1));
end for;
eps[s+t]:=psi(U.1); //generator for units of finite order

//TESTING
fprintf LogFile, "eps = %o\n", eps;
PrintFile(LogFile,"Are they units?");
for i:=1 to s+t do
PrintFile(LogFile,IsUnit(eps[i]));
end for;

for i:=1 to r do
for j:=1 to n do
if eps[i][j] eq 0 then
fprintf LogFile, "Digits(eps[%o][%o]) = %o\n", i, j, 0;
else
fprintf LogFile, "Digits(eps[%o][%o]) = %o\n", i, j, Ceiling(Log(Abs(eps[i][j]))/Log(10));
end if;
end for;
end for;

//Compute the divisors of the class number of K
DivisorsOfClassNumberOfK:=Divisors(ClassNumber(K));

//fprintf LogFile, "DivisorsOfClassNumberOfK = %o\n", DivisorsOfClassNumberOfK;

///////////////////////////////////////////////////////////////////////
/*
Compute the splitting field F of g over Q (FFF), the roots of g in F (rootsofginFFF), and the ring of integers of F (OF)
*/
///////////////////////////////////////////////////////////////////////
FFF,rootsofginFFF:=SplittingField(g);
OF:=MaximalOrder(FFF);

////////////////////////////////////////////////////////////////////
/*
Set precision for real/complex and p-adic computations

We want the precision for real/complex computations (realprecision) to be about three time as large as the largest value of Log(C)/Log(10) (the number of decimal digits in C)  that we expect will occur in the real reduction step (Section 19).  C will about the size of H_0^(v+r), so we want to take
realprecision \approx 2*(v+r)*Log(H_0)/Log(10).  (We would be fine if instead of "four times as large" it was just "larger" than.  We go four times as large as a safety factor to avoid having to back up and do all the calculations again with an increased precision.)

We want to choose the precision for p_i-adic computations (padicprecision[i]) is about three times as large as the largest value of m that we expect will occur in the p_i-adic reduction step (Section 18).  m will be of a size that makes p_i^m \approx H_0^(v+r), so we want to take
padicprecision[i] \approx 2*(v+r)*Log(H_0)/Log(p[i]).  (We would be fine if instead of "four times as large" it was just "larger" than.  We go four times as large as a safety factor to avoid having to back up and do all the calculations again with an increased precision.)

We cannot calculate H_0 a priori.  But we know H_0 will be essentially of the size of that largest of the constants coming from using Yu's and Matveev's theorems to bound the relevant linear forms in logarithms.

The constant c_2 \cdot \min{ c_3^{\prime}, c_3^{prime}  } from Yu's theorem will be bounded by something of the size

(16*Exp(1)*Degree(F))^(2*(2+v+r)) * (1+v+r)^3 * Log(Degree(F)*(1+v+r)) * Max(p[1],...,p[v])^(Degree(F)) * (10)^(1+v+r)

(see [Yu2] p.190, first consequence.  We have assummed the modified heights are are < 10.  This is okay because if the precision is not high enough, we back up and start again with more precision).

The constant c_17 from Matveev's Theorem will be bounded by something of the size

2^(6*(1+v+r)+20) * Degree(F)^(3+v+r) * Log(Degree(F)) * 10^(1+v+r)

Here we are assuming that the absolute logarithmic heights involved are <= 10.  

We set the up a loop so that, if the precisions are not high enough, 
we back up and start again with more precision.
*/
////////////////////////////////////////////////////////////////////////////

RealPrecisionMultiplier:=1;
PadicPrecisionMultiplier:=[];
for i:=1 to v do
PadicPrecisionMultiplier[i]:=1;
end for;

for PrecisionLoopVariable:=1 to 5 do

if PrecisionLoopVariable eq 5 then
print("Something is wrong. 
The required precision for the computation seems to be very large.");
break PrecisionLoopVariable;
end if;

H0estimate:=Max([
(16*Exp(1)*Degree(FFF))^(2*(2+v+r)) * (1+v+r)^3 * Log(Degree(FFF)*(1+v+r)) * Max(p)^(Degree(FFF)) * (10)^(1+v+r),
2^(6*(1+v+r)+20) * Degree(FFF)^(3+v+r) * Log(Degree(FFF)) * 10^(1+v+r)
]);

realprecision:=4*Ceiling((v+r)*Log(H0estimate)/Log(10));
realprecision:=realprecision*RealPrecisionMultiplier;

padicprecision:=[];
for i:=1 to v do
padicprecision[i]:=4*Ceiling((v+r)*Log(H0estimate)/Log(p[i]));
padicprecision[i]:=padicprecision[i]*PadicPrecisionMultiplier[i];
end for;

realprecision:=realprecision;
SetDefaultRealField(RealField(realprecision));
PI:=Pi(RealField());


///////////////////////////////////////////////////////////////////////////////
/*
For each prime p[i], compute the primes of OK dividing p[i] (pp[i][j]), their number (m[i]), their ramification indicies (e[i][j]), and their residue degrees (f[i][j]).

For each pp[i][j] with e[i][j]=f[i][j]=1 (i.e. for each unramified degree one prime ideal above p[i]), compute the least positive integer h[i][j] such that pp[i][j]^h[i][j] is principal and the generator pi[i][j] of pp[i][j]^h[i][j].

Also store the indices j of the unramified degree one primes pp[i][j] above p[i].
*/
///////////////////////////////////////////////////////////////////////////////

pp:=[];
m:=[];
e:=[];
f:=[];
IndicesOfUnramifiedDegreeOnePrimesAbovep:=[];
h:=[];
pi:=[];
DecompositionOfp:=[];
for i:=1 to v do
pp[i]:=[];
e[i]:=[];
f[i]:=[];
IndicesOfUnramifiedDegreeOnePrimesAbovep[i]:=[];
h[i]:=[];
pi[i]:=[];
DecompositionOfp[i]:=Decomposition(OK,p[i]);
m[i]:=#DecompositionOfp[i]; //number of distinct prime factors of p[i]
for j:=1 to m[i] do
pp[i][j]:=DecompositionOfp[i][j][1];
e[i][j]:=DecompositionOfp[i][j][2];
f[i][j]:=InertiaDegree(pp[i][j]);
if e[i][j]*f[i][j] eq 1 then
Append(~IndicesOfUnramifiedDegreeOnePrimesAbovep[i],j);
for k:=1 to #DivisorsOfClassNumberOfK do
if IsPrincipal(pp[i][j]^DivisorsOfClassNumberOfK[k]) then
h[i][j]:=DivisorsOfClassNumberOfK[k];
temp,pi[i][j]:=IsPrincipal(pp[i][j]^DivisorsOfClassNumberOfK[k]);
break k;
end if;
end for;
else
h[i][j]:=0;            //initialization, never used
pi[i][j]:=eps[s+t];   //initialization, never used
end if;
end for; //end j loop
end for; //end i loop


/////////////////////////////////////////////////
/*
Compute completion of K at each pp[i][j] (Kpp[i][j]) 
and the embedding of K into 
Kpp[i][j] (mKpp[i][j]).  
Also, for each pp[i][j], compute the corresponding factor of g(t) in \QQ_{p[i]}[t] (gp[i][j])
gp[i][j] = g_j(t) from Section 3 with p=p_i
*/
////////////////////////////////////////////////
Kpp:=[];
mKpp:=[];
gp:=[**];
for i:=1 to v do
Kpp[i]:=[];
mKpp[i]:=[**];
gp[i]:=[];
for j:=1 to m[i] do //m[i]:=number of distinct prime factors of p[i]
Kpp[i][j], mKpp[i][j]:=Completion(K,pp[i][j] : Precision :=padicprecision[i] );
gp[i][j]:=MinimalPolynomial( mKpp[i][j](theta), PrimeField(Kpp[i][j]));
end for;
end for;

//LocalFactorization(PolynomialRing(pAdicRing(p[1] : Precision:=20)) ! g : Ideals:=true);

//////////////////////////////////////////////////////////////////////
/*
For each p[i], compute the completion FFFppF of FFF at a prime ideal ppF of OF.  Also compute the embedding of FFF into FFFppF (mFFFppF).

Note FFFppF contains the splitting field of g over Q_{p[i]}.

MAGMA currently does not support the direct computation of the splitting field of g over Q_{p[i]}.  The function that purports to do this fails for p[i] that ramify in the K.

Note that since F/Q is Galois, every prime ideal of OF above p[i] has the same 
ramification index and residue degree 
*/
/////////////////////////////////////////////////////////////////////
ppF:=[];  //ppF[i] is a prime of FFF above p[i] selected essentially arbitrarily
eF:=[];   //eF[i] is the ramification index of ppF over Q
fF:=[];   //fF[i] is the residue degree of ppF over Q
FFFppF:=[];
mFFFppF:=[**];
SS:=[];    //SS[i] is the degree of FFFppF[i] over Q_p[i]
DecompositionInFFFOfp:=[];

for i:=1 to v do
DecompositionInFFFOfp[i]:=Decomposition(OF,p[i]);
eF[i]:=DecompositionInFFFOfp[i][1][2];
fF[i]:=InertiaDegree(DecompositionInFFFOfp[i][1][1]);
ppF[i]:=DecompositionInFFFOfp[i][1][1];
FFFppF[i],mFFFppF[i]:=Completion(FFF,ppF[i]:Precision:=padicprecision[i]);
SS[i]:=AbsoluteDegree(FFFppF[i]);
end for;  //end i loop



////////////////////////////////////////////////////////////////
/*
Magma's Completion() function will make FFFppF[l] as one the following types of field extensions 
1. an unramified extension over the p_l-adic field
2. a totally ramified extension over a p_l-adic field
3. an unramified extension over an unramified extension over a p_l-adic field
4. a totally ramified extension over an unramified extension over a p-adic field

We will later want to find the coefficients of elements of FFFppF[l] on the (canonical) power basis of FFFppF[l] over Q_{p_l}.  For this, it will be important to know what type of extension FFFppF[l] is.  The variable 
FFFppFType will indicate this.

The first two types are easy to identify and they come as simple extensions, which will let us use MAGMA built-in function for finding the coefficients of elements on the power basis.
  
The third type seems to be a quirk of Magma.  The top extension always has degree 1 relative to the intermediate extension.  Moreover, the minimal polynomial of the top extension over the intermediate extension is always x.  Finding the coefficients of elements on the power basis will be only slighlty harder than in cases 1. and 2.

For the fourth type, the top extension will always have relative degree greater than one.  We will have to work a bit harder to find coefficients of elements here.  

First we find an element generator[l] that generates FFFppF[l] over Q_{p_l}.  Then we construct a matrix A[l] containing the information necessary to find the coefficients of elements of FFppF[l] on the basis 1,generator[l],...,generator[l]^(d3 - 1), where d3 = degree of FFFpFF[l] over Q_{p_l}.  We will actually need the inverse of this matrix, so we take it now.

More explictly, we construct A[l] as follows.
Let \alpha be the generator of FFFpFF[l] over its coefficient field
Let \beta be the generator of the coefficient field of FFFpFF[l] over Q_{p_l}
d1 = degree of FFFpFF[l] over its coefficient field
d2 = degree of the coefficient field over Q_{p_l}
d3 = d1*d2 = degree of FFFpFF[l] over Q_{p_l}
Let c_{ijk} be the numbers in Q_{p_l} such that
generator^{k-1} = sum_{i,j} c_{ijk} \alpha^{i-1} \beta^{j-1}
Here i ranges from 1 to d1, j ranges from 1 to d2, k ranges from 1 to d3.
A[l] =
c_{1 1 1} ... c_{1 1 d3}
.                  . 
.                  .
.                  .
c_{1 d2 1} ... c_{1 d2 d3}
.                  .
.                  .
.                  .
c_{d1 1 1} ... c_{d1 1 d3}
.                  .
.                  .
.                  .
c_{d1 d2 1} ... c_{d1 d2 d3}


We also define here u_l = (1/2) * \ord_{p_l}(Discr G(t)) from Section 8

u[l]:=(1/2)*Valuation(Discriminant(DefiningPolynomial(CoefficientField(FFFppF[l]))));
*/
////////////////////////////////////////////////////////////////

FFFppFType:=[];
generator:=[**];
Ainverse:=[**];
d1:=[];
d2:=[];
d3:=[];
u:=[RationalField() | ];
for l:=1 to v do
FFFppFType[l]:=5;           //initialize
generator[l]:=FFFppF[l].1;   //initialize, only used in case FFFppFType[l]=4
Ainverse[l]:=1;                    //initialize
d1[l]:=Degree(FFFppF[l],CoefficientField(FFFppF[l]));                   
d2[l]:=Degree(CoefficientField(FFFppF[l]),PrimeField(FFFppF[l]));             
d3[l]:=Degree(FFFppF[l],PrimeField(FFFppF[l]));
u[l]:=1;     

if AbsoluteRamificationIndex(FFFppF[l]) eq 1 then 
FFFppFType[l]:=1;
u[l]:=(1/2)*Valuation(Discriminant(DefiningPolynomial(FFFppF[l])));
if Valuation(FFFppF[l].1) lt 0 then print("Error. Generator has negative valuation.  Results invalid. l="); l; end if;
end if;

if AbsoluteInertiaDegree(FFFppF[l]) eq 1 then 
FFFppFType[l]:=2; 
/*FFFppF[l];
DefiningPolynomial(FFFppF[l]);
Discriminant(DefiningPolynomial(FFFppF[l]));
Parent((1/2)*Valuation(Discriminant(DefiningPolynomial(FFFppF[l]))));
(1/2)*Valuation(Discriminant(DefiningPolynomial(FFFppF[l])));*/
u[l]:=(1/2)*Valuation(Discriminant(DefiningPolynomial(FFFppF[l])));
if Valuation(FFFppF[l].1) lt 0 then print("Error. Generator has negative valuation.  Results invalid. l="); l; end if; 
end if;

if AbsoluteInertiaDegree(FFFppF[l]) gt 1 and d1[l] eq 1 then 
FFFppFType[l]:=3;
u[l]:=(1/2)*Valuation(Discriminant(DefiningPolynomial(CoefficientField(FFFppF[l]))));
if Valuation(CoefficientField(FFFppF[l]).1) lt 0 then print("Error. Generator has negative valuation.  Results invalid. l="); l; end if;
end if;

if d1[l] gt 1 and d2[l] gt 1 then
 
FFFppFType[l]:=4;

k:=1; 
while true do
generator[l] := k*FFFppF[l].1 + (FFFppF[l] ! CoefficientField(FFFppF[l]).1);
if Degree(MinimalPolynomial(generator[l],PrimeField(FFFppF[l]))) eq d3[l] then
break;
end if;
k +:= 1;
end while;

u[l]:=(1/2)*Valuation(Discriminant(MinimalPolynomial(generator[l],PrimeField(FFFppF[l]))));

if Valuation(generator[l]) lt 0 then print("Error. Generator has negative valuation.  Results invalid. l="); l; end if;

//Note: d3[l]:=d1[l]*d2[l];
A:=ZeroMatrix( PrimeField(FFFppF[l]), d3[l], d3[l]); //initialize
temp1:=Coefficients(generator[l]); //initialize
temp2:=Coefficients(temp1[1]); //initialize
for k:=1 to d3[l] do
temp1:=Coefficients(generator[l]^(k-1));
for i:=1 to d1[l] do
temp2:=Coefficients(temp1[i]);
for j:=1 to d2[l] do
A[(i-1)*d2[l] + j,k]:=temp2[j];
end for;
end for;
end for;
Ainverse[l]:=A^(-1);

end if;

if FFFppFType[l] eq 5 then print("Error in FFFppFType. l:"); l; end if;
end for; //end l loop

/*
fprintf LogFile, "FFFppF = %o\n", FFFppF;
fprintf LogFile, "FFFppFType = %o\n", FFFppFType;
for l:=1 to v do
fprintf LogFile, "DefiningPolynomial(FFFppF[l]) = %o\n", DefiningPolynomial(FFFppF[l]);
end for;
*/

/////////////////////////////////////////////////////////////////////////
/*
Define a function to compute the coefficients of an element x in FFFppF[l]
*/
/////////////////////////////////////////////////////////////////////////

function GetCoefficients(x,l)
/*
Input: l in {1,...,v}, x = an element of FFFppF[l]
Output:  The coefficients of x on the basis power basis for FFFppF[l] over Q_{p_l}.
*/
output:=Coefficients(x);
if FFFppFType[l] eq 3 then output:=Coefficients(Coefficient(x,1)); end if;
if FFFppFType[l] eq 4 then 
B:=ZeroMatrix( PrimeField(FFFppF[l]), d3[l], 1);
temp1:=Coefficients(x);
temp2:=Coefficients(temp1[1]); //initialize
for i:=1 to d1[l] do
temp2:=Coefficients(temp1[i]);
for j:=1 to d2[l] do
B[(i-1)*d2[l] + j,1]:=temp2[j];
end for;
end for;
C:=Ainverse[l]*B;
output:=[];
for i:=1 to d3[l] do
output[i]:=C[i][1];
end for;
end if;
return output;
end function;


//////////////////////////////////////////////////////////////////////
/*
thetap[l][i][j]:= theta_i^{(j)} from Section 3 with p=p_l
*/
//////////////////////////////////////////////////////////////////////
thetap:=[];
for l:=1 to v do
thetap[l]:=[];
for i:=1 to m[l] do
thetap[l][i]:=[**];
temp:=Roots(gp[l][i],FFFppF[l]);
for j:=1 to #temp do             //#temp = degree of gp[l][i] = e[l][i]*f[l][i]
thetap[l][i][j]:=temp[j][1];
end for;
end for;
end for;

///////////////////////////////////////////////////////////////
/*
ImageOfIntegralBasisElementp[L][i][j][k] = image of the kth element in the integral basis for K under the embedding of K into \overline{\QQ_{p_L}} defined by the map theta --> thetap[L][i][j]=
*/ 
///////////////////////////////////////////////////////////////
ImageOfIntegralBasisElementp:=[];
for l:=1 to v do
ImageOfIntegralBasisElementp[l]:=[];
for i:=1 to m[l] do
ImageOfIntegralBasisElementp[l][i]:=[];
for j:=1 to e[l][i]*f[l][i] do
ImageOfIntegralBasisElementp[l][i][j]:=[**];
for k:=1 to n do
ImageOfIntegralBasisElementp[l][i][j][k]:=0;
for ii:= 1 to n do
ImageOfIntegralBasisElementp[l][i][j][k]:=ImageOfIntegralBasisElementp[l][i][j][k] + CoefficientsOfIntegralBasisElement[k][ii]*thetap[l][i][j]^(ii-1);
end for; //ii
end for; //k
end for; //j
end for; //i 
end for; //l

////////////////////////////////////////////////////////////////////////
/*
ImageOfpip[L][k][l][i][j] := the image of pi[L][k] under the embedding of K into \overline{\QQ_{p_l}} defined by the map theta --> thetap[l][i][j].  Recall pi[L][k] is the generator of pp_{Lk}^h[L][k].

ImageOfepsp[L][l][i][j] := the image of eps[L] under the embedding of K into \overline{\QQ_{p_l}} defined by the map theta --> thetap[l][i][j].
*/
///////////////////////////////////////////////////////////////////////
ImageOfpip:=[];
for L:=1 to v do
ImageOfpip[L]:=[];
for k:=1 to m[L] do
if e[L][k]*f[L][k] eq 1 then
ImageOfpip[L][k]:=[];
for l:=1 to v do
ImageOfpip[L][k][l]:=[];
for i:=1 to m[l] do
ImageOfpip[L][k][l][i]:=[**];
for j:=1 to e[l][i]*f[l][i] do
ImageOfpip[L][k][l][i][j]:=0;
for ii:= 1 to n do
ImageOfpip[L][k][l][i][j]:=ImageOfpip[L][k][l][i][j] 
+ pi[L][k][ii]*ImageOfIntegralBasisElementp[l][i][j][ii];
end for; //ii
end for; //j
end for; //i
end for; //l
else
ImageOfpip[L][k]:=[[[*0*]]];
end if;
end for; //k
end for; //L

ImageOfepsp:=[];
for L:=1 to r do
ImageOfepsp[L]:=[];
for l:=1 to v do
ImageOfepsp[L][l]:=[];
for i:=1 to m[l] do
ImageOfepsp[L][l][i]:=[**];
for j:=1 to e[l][i]*f[l][i] do
ImageOfepsp[L][l][i][j]:=0;
for ii:= 1 to n do
ImageOfepsp[L][l][i][j]:=ImageOfepsp[L][l][i][j] 
+ eps[L][ii]*ImageOfIntegralBasisElementp[l][i][j][ii];
end for; //ii
end for; //j
end for; //i
end for; //l
end for; //L


//////////////////////////////////////////////////////////////////////////
/*
thetaC:= the conjugates of theta as elements in the field of complex numbers
= the roots of the minimal polynomial of theta (i.e. of g) in the field of complex numbers
*/
//////////////////////////////////////////////////////////////////////////
thetaC:=Conjugates(theta);


//TESTING
//fprintf LogFile, "thetaC[1] = %o\n", thetaC[1];
//fprintf LogFile, "thetaC[1]^0 = %o\n", thetaC[1]^0;
//fprintf LogFile, "thetaC[1]^1 = %o\n", thetaC[1]^1;
//fprintf LogFile, "thetaC[1]^2 = %o\n", thetaC[1]^2;
//fprintf LogFile, "c = %o\n", c;
//fprintf LogFile, "g = %o\n", g;
//fprintf LogFile, "Conjugates(theta) = %o\n", Conjugates(theta);
//fprintf LogFile, "Roots(g) = %o\n", Roots(PolynomialRing(ComplexField())! g);
//fprintf LogFile, "RealField() = %o\n", RealField();
//fprintf LogFile, "ComplexField() = %o\n", ComplexField();
//BitPrecision(RealField());
//BitPrecision(RealField())*Log(2)/Log(10);
//fprintf LogFile, "realprecision = %o\n", realprecision;
//thetaC[1]:=Roots(PolynomialRing(ComplexField())! g)[3][1];

/*
In the thesis, the roots of g in C are ordered so that 
thetaC[s+i] = overline(thetaC[s+t+i]) (i=1,...,t)
Magma (and hence this program) orders the roots so that 
thetaC[s+2i-1] = overline(thetaC[s+2i]) (i=1,...,t).
*/

///////////////////////////////////////////////////////////////
/*
ImageOfIntegralBasisElementC[i][k] = image of the kth element in the integral basis for K under the embedding of K into \CC defined by the map theta --> thetaC[i]
*/ 
///////////////////////////////////////////////////////////////
ImageOfIntegralBasisElementC:=[];
for i:=1 to n do
ImageOfIntegralBasisElementC[i]:=[**];
for k:=1 to n do
ImageOfIntegralBasisElementC[i][k]:=0;
for ii:= 1 to n do
ImageOfIntegralBasisElementC[i][k]:=ImageOfIntegralBasisElementC[i][k] + CoefficientsOfIntegralBasisElement[k][ii]*thetaC[i]^(ii-1);
end for; //ii
end for; //k
end for; //i

/*
for i:=1 to n do
Embed(K, ComplexField(), thetaC[i]);
for k:=1 to n do
ImageOfIntegralBasisElementC[i][k]:= ComplexField() ! IntegralBasisK[i];
end for;
end for;
*/

/*
//TESTING
LinRel:=[];
LinRelDig:=[];
for i:=1 to 3 do
LinRel[i]:=LinearRelation([ImageOfIntegralBasisElementC[i][1],ImageOfIntegralBasisElementC[i][2],ImageOfIntegralBasisElementC[i][3]]);
LinRelDig[i]:=LinRel[i];
for j:=1 to 3 do
//Type(LinRel[i][j]);
//Type(LinRelDig[i][j]);
LinRelDig[i][j]:=Dig(LinRel[i][j]);
//Type(LinRel[i][j]);
//Type(LinRelDig[i][j]);
fprintf LogFile, "LinRelDig[%o][%o] = %o\n", i, j, LinRelDig[i][j];
end for;
end for;

lat:=AllLinearRelations([ImageOfIntegralBasisElementC[1][1],ImageOfIntegralBasisElementC[1][2],ImageOfIntegralBasisElementC[1][3]],100);
fprintf LogFile, "lat = %o\n", lat;
//latelt:= lat ! [eps[1][1], eps[1][2], eps[1][3]];
//fprintf LogFile, "latelt = %o\n", latelt;
*/

/*
fprintf LogFile, "LinearRelation(ImageOfIntegralBasisElementC[1]) = %o\n", LinearRelation([ImageOfIntegralBasisElementC[1][1],ImageOfIntegralBasisElementC[1][2],ImageOfIntegralBasisElementC[1][3]]);
fprintf LogFile, "LinearRelation(ImageOfIntegralBasisElementC[2]) = %o\n", LinearRelation([ImageOfIntegralBasisElementC[2][1],ImageOfIntegralBasisElementC[2][2],ImageOfIntegralBasisElementC[2][3]]);
fprintf LogFile, "LinearRelation(ImageOfIntegralBasisElementC[3]) = %o\n", LinearRelation([ImageOfIntegralBasisElementC[3][1],ImageOfIntegralBasisElementC[3][2],ImageOfIntegralBasisElementC[3][3]]);
*/



////////////////////////////////////////////////////////////////////////
/*
ImageOfpiC[L][k][i] := the image of pi[L][k] under the embedding of K into \CC defined by the map theta --> thetaC[i].  Recall pi[L][k] is the generator of pp_{Lk}^h[L][k].

ImageOfepsC[L][i] := the image of eps[L] under the embedding of K into \CC defined by the map theta --> thetaC[i].
*/
///////////////////////////////////////////////////////////////////////

ImageOfpiC:=[];
for L:=1 to v do
ImageOfpiC[L]:=[];
for k:=1 to m[L] do
if e[L][k]*f[L][k] eq 1 then
ImageOfpiC[L][k]:=[**];
for i:=1 to n do
ImageOfpiC[L][k][i]:=0;
for ii:= 1 to n do
ImageOfpiC[L][k][i]:=ImageOfpiC[L][k][i] 
+ pi[L][k][ii]*ImageOfIntegralBasisElementC[i][ii];
end for; //ii
end for; //i
else
ImageOfpiC[L][k]:=[*0*];
end if;
end for; //k
end for;  //L

ImageOfepsC:=[];
for L:=1 to r do
ImageOfepsC[L]:=[**];
for i:=1 to n do
ImageOfepsC[L][i]:=0;
for ii:= 1 to n do
ImageOfepsC[L][i]:=ImageOfepsC[L][i]
+ eps[L][ii]*ImageOfIntegralBasisElementC[i][ii];
end for; //ii
end for; //i
end for; //L




///////////////////////////////////////////////////////////////////////
/*
Recall F = the splitting field of g over Q

thetaF:= the conjugates of theta as elements in F 
= the roots of the minimal polynomial of theta (i.e. of g) in F
*/
//////////////////////////////////////////////////////////////////////
thetaF:=rootsofginFFF;

///////////////////////////////////////////////////////////////
/*
ImageOfIntegralBasisElementF[i][k] = image of the kth element in the integral basis for K under the embedding of K into F defined by the map theta --> thetaF[i]
*/ 
///////////////////////////////////////////////////////////////
ImageOfIntegralBasisElementF:=[];
for i:=1 to n do
ImageOfIntegralBasisElementF[i]:=[**];
for k:=1 to n do
ImageOfIntegralBasisElementF[i][k]:=0;
for ii:= 1 to n do
ImageOfIntegralBasisElementF[i][k]:=ImageOfIntegralBasisElementF[i][k] + CoefficientsOfIntegralBasisElement[k][ii]*thetaF[i]^(ii-1);
end for; //ii
end for; //k
end for; //i

////////////////////////////////////////////////////////////////////////
/*
ImageOfpiF[L][k][i] := the image of pi[L][k] under the embedding of K into F defined by the map theta --> thetaF[i].  Recall pi[L][k] is the generator of pp_{Lk}^h[L][k].

ImageOfepsF[L][i] := the image of eps[L] under the embedding of K into F defined by the map theta --> thetaF[i].
*/
///////////////////////////////////////////////////////////////////////

ImageOfpiF:=[];
for L:=1 to v do
ImageOfpiF[L]:=[];
for k:=1 to m[L] do
if e[L][k]*f[L][k] eq 1 then
ImageOfpiF[L][k]:=[**];
for i:=1 to n do
ImageOfpiF[L][k][i]:=0;
for ii:= 1 to n do
ImageOfpiF[L][k][i]:=ImageOfpiF[L][k][i] 
+ pi[L][k][ii]*ImageOfIntegralBasisElementF[i][ii];
end for; //ii
end for; //i
else
ImageOfpiF[L][k]:=[*0*];
end if;
end for; //k
end for;  //L

ImageOfepsF:=[];
for L:=1 to r do
ImageOfepsF[L]:=[**];
for i:=1 to n do
ImageOfepsF[L][i]:=0;
for ii:= 1 to n do
ImageOfepsF[L][i]:=ImageOfepsF[L][i]
+ eps[L][ii]*ImageOfIntegralBasisElementF[i][ii];
end for; //ii
end for; //i
end for; //L



//////////////////////////////////////////////////////////////////////////////
/*
Compute the constant constant c10 = c_{10} from Section 12

Note: If kappa = {k_1,...,k_r} with 1 <= k_1 < ... < k_r <= s+t, then there is a unique index k* in {1,...,s+t}-{k_1,...,k_r} and U_kappa from Section 12 is equal to the matrix formed by starting with the r by s+t matrix 
U = (log|\eps_j^{(i)}|) and removing the k*th row.

We use this equivalent definition of U_kappa below.
*/
////////////////////////////////////////////////////////////////////////////

//Function to compute maximum absolute row sum of an r by r matrix U
function MaximumAbsoluteRowSum(U,r) 
max:=0;
for i:=1 to r do
sum:=0;
for j:=1 to r do 
sum:=sum+Abs(U[i][j]);
end for;
if sum gt max then max:=sum; end if;
end for;
return max;
end function;

/*
In the thesis, the roots of g in C are ordered so that 
thetaC[s+i] = overline(thetaC[s+t+i]) (i=1,...,t)
Magma (and hence this program) orders the roots so that 
thetaC[s+2i-1] = overline(thetaC[s+2i]) (i=1,...,t).
*/

U:=ZeroMatrix(ComplexField(),s+t,r);
for i:=1 to s do
for j:=1 to r do
fprintf LogFile, "ImageOfepsC[%o][%o]) = %o\n", j,i,ImageOfepsC[j][i];
U[i][j]:=Log(Abs(ImageOfepsC[j][i]));
end for;
end for;
for i:=1 to t do
ii:=s+2*i-1;
for j:=1 to r do
U[s+i][j]:=Log(Abs(ImageOfepsC[j][ii]));
end for;
end for;

//return [];

currentmin:=MaximumAbsoluteRowSum( RemoveRow(U,1)^(-1),r );
for skippedindex:=1 to s+t do  //skipped index = k*
potentialmin:=MaximumAbsoluteRowSum( RemoveRow(U,skippedindex)^(-1),r );
if potentialmin lt currentmin then
currentmin:=potentialmin;
end if;
end for;

c10:=1/currentmin;


//Now we go essentially in the order of the thesis starting at Section 6.

///////////////////////////////////////////////////////////////////
//Apply Prime Ideal Removing Lemma (PIRL)
///////////////////////////////////////////////////////////////////
/*
The elements of ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L] will be of the form [[k],aaa].  

If k <= m[L], then k has the meaning that pp[L][k] is the unconstrained prime above p[L] (pp[L][k] must have e[L][k]=f[L][k]=1).  

If k = m[L]+1, there is no prime above p[L] with ramification index and residue degree equal to one, hence no unconstrained prime above p[L].

In either case, aaa is a tuple of nonnegative integers such that that PowerProduct(pp[L],aaa) is the factor of bb=\mathfrak{b} consisting of primes above p[L].
Note aaa[k]=0 if k <= m[L].
*/
///////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////
/*
Define the procedures we need
*/
///////////////////////////////////////////////////////////////////////
procedure BuildListOfValidTuplesWhenppLkIsTheUnconstrainedPrimeAbovepL(i,L,k,~aaa,~D,~m,~CC,~LIST)
/*
RngIntElt
RngIntElt
RngIntElt
SeqEnum
SeqEnum
SeqEnum
SeqEnum
SeqEnum
*/
for l:=0 to D[i] do
aaa[i]:=l;
if i eq m[L] then
//aaa[k]:=0; 
Include(~LIST,[[k],aaa]);
else
for j:=i+1 to m[L] do
if aaa[i] gt CC[i][j] then D[j]:=Min(D[j],CC[j][i]); end if;
end for;
BuildListOfValidTuplesWhenppLkIsTheUnconstrainedPrimeAbovepL(i+1,L,k,~aaa,~D,~m,~CC,~LIST);
end if;
end for;
end procedure;

procedure BuildListOfValidTuplesWhenNoUnramifiedDegreeOnePrimesAbovepL(i,L,k,~aaa,~D,~m,~CC,~LIST)
/*print("BuildListOfValidTuplesWhenNoUnramifiedDegreeOnePrimesAbovepL");
Type(i);
Type(L);
Type(k);
Type(aaa);
Type(D);
Type(m);
Type(CC);
Type(LIST);*/
for l:=0 to D[i] do
aaa[i]:=l;
if i eq m[L] then
Include(~LIST,[[k],aaa]);
else
for j:=i+1 to m[L] do
if aaa[i] gt CC[i][j] then D[j]:=Min(D[j],CC[j][i]); end if;
end for;
BuildListOfValidTuplesWhenNoUnramifiedDegreeOnePrimesAbovepL(i+1,L,k,~aaa,~D,~m,~CC,~LIST);
end if;
end for;
end procedure;

//////////////////////////////////////////////////////////////////////
//The algorithm
/////////////////////////////////////////////////////////////////////
ListOfTuplesOfExponentsForPrimesDividingbbAbovep:=[**];
for L:=1 to v do
ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L]:=[];


////////////////////////////////////////////////////////////
/*
CC[i][j]:= \max\cbr{e_i,e_j} \cdot 
\min_{k,l} \cbr{ord_p(theta_{i}^{(k)} - theta_{j}^{(l)})}
*/
/////////////////////////////////////////////////////////////
CC:=[];
for i:=1 to m[L] do
CC[i]:=[];
for j:=1 to m[L] do
temp:=[];
for k:=1 to #thetap[L][i] do
for l:=1 to #thetap[L][j] do
Append(~temp, Valuation( thetap[L][i][k] - thetap[L][j][l] ));
end for;
end for;
CC[i][j]:=e[L][i]*Min(temp);
end for;
end for;

for i:=1 to m[L] do
if e[L][i]*f[L][i] eq 1 then
CC[i][i]:=2^15; //placeholder, never used
else
temp:=[];
for k:=1 to #thetap[L][i] do
for l:=k+1 to #thetap[L][i] do
Append(~temp,Valuation( thetap[L][i][k] - thetap[L][i][l] ) );
end for;
end for;
CC[i][i]:=e[L][i]*Min(temp);
end if;
end for;


/*
CC:=[];
for i:=1 to m[L] do
CC[i]:=[];
for j:=1 to i-1 do
temp:=[];
for k:=1 to #thetap[L][i] do
for l:=1 to #thetap[L][j] do
Append(~temp, Valuation( thetap[L][i][k] - thetap[L][j][l] ));
end for;
end for;
CC[i][j]:=Max([e[L][i],e[L][j]])*Min(temp);
end for;
end for;

for i:=1 to m[L] do
if e[L][i]*f[L][i] eq 1 then
CC[i][i]:=2^15; //placeholder, never used
else
temp:=[];
for k:=1 to #thetap[L][i] do
for l:=k+1 to #thetap[L][i] do
Append(~temp,Valuation( thetap[L][i][k] - thetap[L][i][l] ) );
end for;
end for;
CC[i][i]:=e[L][i]*Min(temp);
end if;
end for;

for i:=1 to m[L] do
for j:=i+1 to m[L] do
CC[i][j]:=CC[j][i];
end for;
end for;
*/


//DD:=Floor((1/2)*Max(e[L])*Valuation(DiscriminantOfg, p[L]));
DD:=[];
for i:=1 to m[L] do
DD[i]:=Floor((1/2)*e[L][i]*Valuation(DiscriminantOfg, p[L]));
end for;

///////////////////////////////////////////////////////
/*
For each unramified degree 1 prime pp[L][k] above p[L], list all valid tuples
assuming pp[L][k] is the unconstrained prime ideal above p[L] dividing (x-y\theta).  

The assumption means that, for i=1,...,m[L],i \neq k, we assume the 
exponent of the prime ideal pp[L][i] above p[L] in the factorization of 
(x-y\theta) is \leq (1/2)*max(e[L][1],...,e[L][m[L]])*ord_p(D_g).  We 
assume nothing about the exponent ord_pp[L][k](x-y\theta) of pp[L][k] 
in the factorization of (x-y\theta).

For i=1,...,m[L],i \neq k, D[i] is an upper bound on the exponent of the 
prime ideal pp[L][i] above p[L] in the factorization of bb=\mathfrak{b}

The exponent of pp[L][k] in the factorization of (x-y\theta) is 
ord_pp[L][k](x-y\theta) (obviously).
Suppose A < B.  The valid tuples aaa when ord_pp[L][k](x-y\theta) = B are a 
subset of the valid tuples aaa when ord_pp[L][k](x-y\theta) = A.  So we only 
need to consider ord_pp[L][k](x-y\theta) <= DD+1 to find all valid tuples in 
when ord_pp[L][k](x-y\theta) >= DD+1 and when ord_pp[L][k](x-y\theta) <= DD
Hence the definition of D[k] below.
*/
///////////////////////////////////////////////////////

if #IndicesOfUnramifiedDegreeOnePrimesAbovep[L] gt 0 then

for kk:=1 to #IndicesOfUnramifiedDegreeOnePrimesAbovep[L] do
k:=IndicesOfUnramifiedDegreeOnePrimesAbovep[L][kk];
//k will go through all the indices of primes ideals above p=p[L] with e_i=f_i=1

D:=[];

for i:=1 to k-1 do
if e[L][i]*f[L][i] eq 1 then
D[i]:=DD[i];
else
D[i]:=Min(CC[i][i],DD[i]);
end if;
end for;

D[k]:=DD[k]+1;

for i:=k+1 to m[L] do
if e[L][i]*f[L][i] eq 1 then
D[i]:=DD[i];
else
D[i]:=Min(CC[i][i],DD[i]);
end if;
end for;

/*
Populate ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L] assuming pp[L][k]
is the unconstrained prime ideal above p[L] dividing (x-y\theta)
*/
aaa:=[];
BuildListOfValidTuplesWhenppLkIsTheUnconstrainedPrimeAbovepL(1,L,k,~aaa,~D,~m,~CC,~ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L]);


/*
Remove redundant tuples from ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L]
*/
CopyOfListOfTuplesOfExponentsForPrimesDividingbbAbovepL:=ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L];
i1:=1;
while i1 le #CopyOfListOfTuplesOfExponentsForPrimesDividingbbAbovepL do
bbb:=CopyOfListOfTuplesOfExponentsForPrimesDividingbbAbovepL[i1];
if bbb[1][1] ne k then i1:=i1+1; continue; end if;
IndexOfTupleToRemove:=-1;
for i2:=1 to #ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L] do
ccc:=ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L][i2];

if ccc[1][1] ne k then continue i2; end if;
for i:=1 to k-1 do
if bbb[2][i] ne ccc[2][i] then continue i2; end if;
end for; //end i loop
for i:=k+1 to #bbb[2] do
if bbb[2][i] ne ccc[2][i] then continue i2; end if;
end for; //end i loop
if bbb[2][k] le ccc[2][k] then continue i2; end if;
//know we know that bbb covers ccc
IndexOfTupleToRemove:=i2;
break i2;

end for;
if IndexOfTupleToRemove ne -1 then 
Remove(~ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L],IndexOfTupleToRemove);
else
i1:=i1+1;
end if;
end while; 
/*
Done removing tuples (for now...)
*/


end for; //end kk loop



/*
Remove more redundant tuples from ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L]
*/
CopyOfListOfTuplesOfExponentsForPrimesDividingbbAbovepL:=ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L];
i1:=1;
while i1 le #CopyOfListOfTuplesOfExponentsForPrimesDividingbbAbovepL do
bbb:=CopyOfListOfTuplesOfExponentsForPrimesDividingbbAbovepL[i1];
if bbb[2][bbb[1][1]] ne DD[bbb[1][1]]+1 then i1:=i1+1; continue; end if;
IndexOfTupleToRemove:=-1;
for i2:=1 to #ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L] do
ccc:=ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L][i2];

if ccc[2][ccc[1][1]] eq DD[ccc[1][1]]+1 then continue i2; end if; //now we know ccc[2][ccc[1][1]] le DD
for i:=1 to bbb[1][1]-1 do
if bbb[2][i] ne ccc[2][i] then continue i2; end if;
end for;
for i:=bbb[1][1]+1 to #bbb[2] do
if bbb[2][i] ne ccc[2][i] then continue i2; end if;
end for;
//know we know that bbb covers ccc
IndexOfTupleToRemove:=i2;
break i2;

end for;
if IndexOfTupleToRemove ne -1 then 
Remove(~ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L],IndexOfTupleToRemove); 
else
i1:=i1+1;
end if;
end while;


/*
Go through and set aaa[k]=0 for each [[k],aaa] in 
ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L]
*/
for i1:=1 to #ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L] do
ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L][i1][2][

ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L][i1][1][1]

]:=0;
end for;

//fprintf LogFile, "ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L] = %o\n", ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L];
//fprintf LogFile, "h[L] = %o\n", h[L];

end if; //controlled by #IndicesOfUnramifiedDegreeOnePrimesAbovep[L] gt 0

//////////////////////////////////////////////////////////////////////////
/*
List all valid tuples in the case there are no unramified degree one primes above p[L].

For i=1,...,m[L], D[i] is an upper bound on the exponent of the prime ideal pp[L][i] above p[L] in the factorization of bb=\mathfrak{b}  

Should remove p[L] from consideration in certain things below.  (Done.)
*/
///////////////////////////////////////////////////////////////////////////

if #IndicesOfUnramifiedDegreeOnePrimesAbovep[L] eq 0 then

k:=m[L]+1;

D:=[];

for i:=1 to m[L] do
if e[L][i]*f[L][i] eq 1 then
D[i]:=DD[i];
else
D[i]:=Min(CC[i][i],DD[i]);
end if;
end for;

//Populate ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L]
aaa:=[];
BuildListOfValidTuplesWhenNoUnramifiedDegreeOnePrimesAbovepL(1,L,k,~aaa,~D,~m,~CC,~ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L]);

//fprintf LogFile, "ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L] = %o\n", ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L];
//fprintf LogFile, "h[L] = %o\n", h[L];

end if; //controlled by #IndicesOfUnramifiedDegreeOnePrimesAbovep[L] eq 0


//////////////////////////////////////////////////////////////

end for; //end L loop

////////////////////////////////////////////////////////////
//END Application of Prime Ideal Removing Lemma
////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////
//Build ModifiedListOfTuplesOfExponentsForPrimesDividingbbAbovep
/////////////////////////////////////////////////////////
/*
For each p[L], if there are unramifed degree one prime ideals of OK above p[L], 
we augment ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L] by taking a 
given choice of unbounded prime p[L][k] and allowing for all the possible 
values of the parameter s_{Lk}=s[L][k], which are 0,...,h[L][k]-1 (cf. Section 6)

More precisely, for L = 1,...,v we do the following:
For each element [[k],aaa] of ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L], 
we form the elements [[k],aaa,[0]],...,[[k],aaa,[h[L][k]-1]] and adjoin them to a 
new list ModifiedListOfTuplesOfExponentsForPrimesDividingbbAbovep[L].

If there are no unramifed degree one prime ideals of OK above p[L], then for each 
element [[k],aaa] of ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L], we form 
the element [[k],aaa,0] and adjoin them to 
ModifiedListOfTuplesOfExponentsForPrimesDividingbbAbovep[L].

As a minor optimization, all this could be done as part of building 
ListOfTuplesOfExponentsForPrimesDividingbbAbovep.
*/
/////////////////////////////////////////////////////////
ModifiedListOfTuplesOfExponentsForPrimesDividingbbAbovep:=[**];
for L:=1 to v do
ModifiedListOfTuplesOfExponentsForPrimesDividingbbAbovep[L]:=[];
for i:=1 to #ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L] do
k:=ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L][i][1][1];
if k ne m[L]+1 then
for s:=0 to h[L][k]-1 do
Append(~ModifiedListOfTuplesOfExponentsForPrimesDividingbbAbovep[L],Append(ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L][i],[s]));
end for;
else //k eq m[L]+1
Append(~ModifiedListOfTuplesOfExponentsForPrimesDividingbbAbovep[L],Append(ListOfTuplesOfExponentsForPrimesDividingbbAbovep[L][i],[0]));
end if;
end for;
end for;

delete ListOfTuplesOfExponentsForPrimesDividingbbAbovep;

///////////////////////////////////////////////////////////////////////////
/*
Compute
ListOfIdealsOfNorma = list containing a representation of each ideal in OK having norm a.  

The representation is such that the ideal corresponding to ListIdealsOfNorma[i]ideals is PowerProduct(pI,ListIdealsOfNorma[i]), where pI is the sequence of the prime ideals of OK that divide a.

We follow the strategy layed out in the Example on p.125 of [ST]
*/
//////////////////////////////////////////////////////////////////////////
procedure BuildListOfIdealsOfNorma(k,~bbb,~epI,~NpI,~ListOfIdealsOfNorma)
/*print("BuildListOfIdealsOfNorma");
Type(k);
Type(bbb);
Type(epI);
Type(NpI);
Type(ListOfIdealsOfNorma);*/
for j:=0 to epI[k] do
bbb[k]:=j;
if k eq #epI then
prod:=1;
for i:=1 to #epI do
prod:=prod*NpI[i]^bbb[i];
end for;
if prod eq a or prod eq -a then Append(~ListOfIdealsOfNorma,bbb); end if;
else
BuildListOfIdealsOfNorma(k+1,~bbb,~epI,~NpI,~ListOfIdealsOfNorma);
end if;
end for;
end procedure;

ListOfIdealsOfNorma:=[];
if a eq 1 or a eq -1 then
pI:=[ideal<OK|1>];
ListOfIdealsOfNorma:=[[1]];
else
//I = ideal<OK|a> = principal ideal generated by a
FI:=Factorization(ideal<OK|a>);
pI:=[];
epI:=[];
NpI:=[];
for i:=1 to #FI do
pI[i]:=FI[i][1]; //ith prime ideal in the factorization of I
epI[i]:=FI[i][2]; //ramification index of pI[i] 
NpI[i]:=Norm(FI[i][1]);
end for;
bbb:=[];
BuildListOfIdealsOfNorma(1,~bbb,~epI,~NpI,~ListOfIdealsOfNorma);
end if;

//fprintf LogFile, "ListOfIdealsOfNorma = %o\n", ListOfIdealsOfNorma;

/////////////////////////////////////////////////
/*
Form the list of all units of finite order \zeta in OK (i.e, the list of all roots of unity \zeta in OK) 
with the understanding that we include only one of \zeta and -\zeta.
*/
////////////////////////////////////////////////////
ListOfUnitsOfFiniteOrder:=[eps[s+t]];
zeta:=eps[s+t]^2;
while(zeta ne eps[s+t]) do
Append(~ListOfUnitsOfFiniteOrder,zeta);
zeta:=zeta*eps[s+t];
end while;
CopyOfListOfUnitsOfFiniteOrder:=ListOfUnitsOfFiniteOrder;
NumberOfUnitsOfFiniteOrder:=#ListOfUnitsOfFiniteOrder;
for i:=1 to NumberOfUnitsOfFiniteOrder do
if CopyOfListOfUnitsOfFiniteOrder[i] in ListOfUnitsOfFiniteOrder and -CopyOfListOfUnitsOfFiniteOrder[i] in ListOfUnitsOfFiniteOrder then
Exclude(~ListOfUnitsOfFiniteOrder,-CopyOfListOfUnitsOfFiniteOrder[i]);
end if;
end for;

delete CopyOfListOfUnitsOfFiniteOrder;
delete NumberOfUnitsOfFiniteOrder;

/*
T:=TorsionUnitGroup(K);
a:=[];
for u in T do
Append(~a,u);
end for;
a;
*/

//fprintf LogFile, "ListOfUnitsOfFiniteOrder = %o\n", ListOfUnitsOfFiniteOrder; 

///////////////////////////////////////////////////////////////////////// 
/*
Construct 
ListOfCases = the list of all cases of the factorized Thue-Mahler 
equation (11) that we need to solve.

Each element in ListOfCases will be a sequence.  Consider ListOfCases[i].  
For L = 1 to v, ListOfCases[i][L] is of the form [[k],aaa,[s]].  
The meaning here is that pp[L][k] is the unbounded prime above p[L], 
PowerProduct(pp[L],aaa) is the factor of bb consisting of primes above 
pp[L] and s is the value of the parameter s_{kl}.  

ListOfCases[i][v+1] has the meaning that the value of the parameter aa 
is PowerProduct(pI,ListOfCases[i][v+1]). 

Finally, ListOfCases[i][v+2] is the value of the parameter \zeta
*/
//////////////////////////////////////////////////////////////////////////
procedure BuildListOfCases(L,~bbb,~LIST,~ListOfCases)
/*
RngIntElt
SeqEnum
List
SeqEnum
*/
for i:=1 to #LIST[L] do
bbb[L]:=i;
if L eq v+2 then
temp:=[**];
for j:=1 to v+2 do 
temp[j]:=LIST[j][bbb[j]];
end for;
Append(~ListOfCases,temp);
else
BuildListOfCases(L+1,~bbb,~LIST,~ListOfCases);
end if;
end for;
end procedure;

//////////////////////////////////////////////////////////////
//preprocessing
ModifiedListOfTuplesOfExponentsForPrimesDividingbbAbovep[v+1]:=ListOfIdealsOfNorma;
ModifiedListOfTuplesOfExponentsForPrimesDividingbbAbovep[v+2]:=ListOfUnitsOfFiniteOrder;

//Populate the list of cases
bbb:=[];
ListOfCases:=[];
BuildListOfCases(1,~bbb,~ModifiedListOfTuplesOfExponentsForPrimesDividingbbAbovep,~ListOfCases);

delete ModifiedListOfTuplesOfExponentsForPrimesDividingbbAbovep;


//////////////////////////////////////////////////////
/*
Before we start the loop through the cases, we discard those cases where the ideal
\mathfrak{a} \mathfrak{b} \mathfrak{p}_{1}^{s_1} \ldots \mathfrak{p}_{v}^{s_v}
from Section 6 is not principal.
If the case of (11) we are considering has a solution, this ideal must be principal.  
So if it is not principal, we know there are no solutions to the case of (11) under 
consideration and can ignore the case.
*/
fprintf LogFile, "Number of cases: %o\n", #ListOfCases;
PrintFile(LogFile,"Removing cases where no solutions are possible because the ideal is not principle.");
kk:=[];
ppp:=[];
ss:=[];
nListOfCases:=#ListOfCases;

for iiii := nListOfCases to 1 by -1 do

for L:=1 to v do

kk[L]:=ListOfCases[iiii][L][1][1]; //index of the unconstrained prime above p[L]

if kk[L] ne m[L] + 1 then
ppp[L]:=pp[L][kk[L]]; //the unconstrained prime above p[L]
else //kk[L] eq m[L] + 1 
//there are no unramified degree one primes above p[L]
ppp[L]:=ideal<OK | 1>;
end if;

ss[L]:=ListOfCases[iiii][L][3][1]; // the parameter s_L

end for; //end L loop

aa:=PowerProduct(pI,ListOfCases[iiii][v+1]);

aatimesbb:=aa;
for L:=1 to v do
aaa:=ListOfCases[iiii][L][2];
aatimesbb:=aatimesbb*PowerProduct(pp[L],aaa);
end for;

TheIdeal:=aatimesbb;
for L:=1 to v do
TheIdeal:=TheIdeal*(ppp[L]^ss[L]);
end for;

IsTheIdealPrinciple,alpha:=IsPrincipal(TheIdeal);

if IsTheIdealPrinciple eq false then 
Remove(~ListOfCases,iiii);
end if;

end for; // end iiii loop



//////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////
//////////////////////////////////////////////
/*
Now we are ready to start the loop through the cases.  
We first declare the procedures that we will need in the loop (they have all been made intrinsics).
We also initialize some variables that we will use in the loop.  We initialize them now to avoid having to add additional inputs for the procedures.
*/
/////////////////////////////////////////////
/////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////
//See the intrinsics at the end of the file.

////////////////////////////////////////////////////////////////
/*
Start the loop over cases.
The loop variable is iiii.
*/
////////////////////////////////////////////////////////////////
NumberOfCases:=#ListOfCases;

fprintf LogFile, "Number of cases: %o\n", NumberOfCases;


if StartCase gt NumberOfCases then
fprintf OutFile, "No more cases to consider. Total number of cases = %o.\n", NumberOfCases;
printf "No more cases to consider. Total number of cases = %o.\n", NumberOfCases;
return [[-1]];
end if;

if EndCase gt NumberOfCases then
EndCase:=NumberOfCases;
//DoneAllCases:=true;
end if;


//for iiii:=1 to NumberOfCases do
for iiii:=StartCase to EndCase do


fprintf LogFile,"Starting case iiii = %o\n", iiii;

///////////////////////////////////////////////////////////////////
/*
Give easy-to-use names to the parameters determining the case of the factorized Thue-Mahler equation (11) that we are working with.  Do the same for some numbers derived from these parameters.  These names essentially coincide with the names given to them in Section 6.
*/
///////////////////////////////////////////////////////////////
zeta:=ListOfCases[iiii][v+2];

kk:=[];
ppp:=[];
ppi:=[];
hh:=[];
ss:=[];
tt:=[];
for L:=1 to v do
kk[L]:=ListOfCases[iiii][L][1][1]; //index of the unconstrained prime above p[L]

if kk[L] ne m[L] + 1 then
ppp[L]:=pp[L][kk[L]]; //the unconstrained prime above p[L]
hh[L]:=h[L][kk[L]]; //smallest positive integer such that ppp[L]^hh[L] is principal
ppi[L]:=pi[L][kk[L]]; //generator of ppp[L]^hh[L]
else //kk[L] eq m[L] + 1 
//there are no unramified degree one primes above p[L]
ppp[L]:=ideal<OK | 1>;
hh[L]:=1;
ppi[L]:=OK ! 1;
end if;
ss[L]:=ListOfCases[iiii][L][3][1]; // the parameter s_L
tt[L]:=0;
for j:=1 to m[L] do
tt[L]:=tt[L] + f[L][j]*ListOfCases[iiii][L][2][j]; //tt[L] = ord_p[L](N(bb))
end for;
end for; //end L loop


/*
The last thing to do is compute a generator alpha for the ideal
\mathfrak{a} \mathfrak{b} \mathfrak{p}_{1}^{s_1} \ldots \mathfrak{p}_{v}^{s_v}
from Section 6, provided it is principal.
If the case of (11) we are considering has a solution, this ideal must be principal.  
So if it is not principal, we know there are no solutions to case of (11) under 
consideration and skip directly to the next case (by using the continue command)
We removed all the cases where the ideal is not principle before we began. So 
*/

aa:=PowerProduct(pI,ListOfCases[iiii][v+1]);

aatimesbb:=aa;
for L:=1 to v do
aaa:=ListOfCases[iiii][L][2];
aatimesbb:=aatimesbb*PowerProduct(pp[L],aaa);
end for;

TheIdeal:=aatimesbb;
for L:=1 to v do
TheIdeal:=TheIdeal*(ppp[L]^ss[L]);
end for;

IsTheIdealPrinciple,alpha:=IsPrincipal(TheIdeal);

fprintf LogFile, "ListOfCases[iiii][v+1] = %o\n", ListOfCases[iiii][v+1];
fprintf LogFile, "pI = %o\n", pI;
fprintf LogFile, "aa = %o\n", aa;
for L:=1 to v do
fprintf LogFile, "ListOfCases[iiii][L][2] = %o\n", ListOfCases[iiii][L][2];
fprintf LogFile, "pp[L] = %o\n", pp[L];
end for;
fprintf LogFile, "aatimesbb = %o\n", aatimesbb;
for L:=1 to v do
fprintf LogFile, "ss[L] = %o\n", ss[L];
fprintf LogFile, "ppp[L] = %o\n", ppp[L];
end for;
fprintf LogFile, "TheIdeal = %o\n", TheIdeal;
fprintf LogFile, "alpha = %o\n", alpha;
fprintf LogFile, "IsZero(alpha) = %o\n", IsZero(alpha);
fprintf LogFile, "ideal<OK | alpha> eq TheIdeal = %o\n", ideal<OK | alpha> eq TheIdeal;
fprintf LogFile, "aatimesbb eq TheIdeal = %o\n", aatimesbb eq TheIdeal;


if IsTheIdealPrinciple eq false then 
/*This should never happen because we have 
removed all such cases before we began the loop*/
fprintf LogFile, "Ideal not principal. No solutions possible in case iiii = %o\n", iiii;
continue iiii; 
end if;

delete aa;
delete aatimesbb;
delete TheIdeal;




/////////////////////////////////////////////////////////////////////////
/*
ImageOfzetap[l][i][j] := the image of zeta under the embedding of K into \overline{\QQ_{p_l}} defined by the map theta --> thetap[l][i][j].

ImageOfalphap[l][i][j] := the image of alpha under the embedding of K into \overline{\QQ_{p_l}} defined by the map theta --> thetap[l][i][j].
*/
////////////////////////////////////////////////////////////////////////

ImageOfzetap:=[];
for l:=1 to v do
ImageOfzetap[l]:=[];
for i:=1 to m[l] do
ImageOfzetap[l][i]:=[**];
for j:=1 to e[l][i]*f[l][i] do
ImageOfzetap[l][i][j]:=0;
for ii:= 1 to n do
ImageOfzetap[l][i][j]:=ImageOfzetap[l][i][j] 
+ zeta[ii]*ImageOfIntegralBasisElementp[l][i][j][ii];
end for; //ii
end for; //j
end for; //i
end for; //l

ImageOfalphap:=[];
for l:=1 to v do
ImageOfalphap[l]:=[];
for i:=1 to m[l] do
ImageOfalphap[l][i]:=[**];
for j:=1 to e[l][i]*f[l][i] do
ImageOfalphap[l][i][j]:=0;
for ii:= 1 to n do
ImageOfalphap[l][i][j]:=ImageOfalphap[l][i][j] 
+ alpha[ii]*ImageOfIntegralBasisElementp[l][i][j][ii];
end for; //ii
end for; //j
end for; //i
end for; //l

////////////////////////////////////////////////////////////////////////
/*
ImageOfzetaC[i] := the image of zeta under the embedding of K into \CC defined by the map theta --> thetaC[i].

ImageOfalphaC[i] := the image of alpha under the embedding of K into \CC defined by the map theta --> thetaC[i].
*/
///////////////////////////////////////////////////////////////////////



ImageOfzetaC:=[ComplexField() | ]; 
for i:=1 to n do
ImageOfzetaC[i]:=0;
for ii:= 1 to n do
ImageOfzetaC[i]:=ImageOfzetaC[i] 
+ zeta[ii]*ImageOfIntegralBasisElementC[i][ii];
end for; //ii
end for; //i

ImageOfalphaC:=[ComplexField() | ]; 
for i:=1 to n do
ImageOfalphaC[i]:=0;
for ii:= 1 to n do
ImageOfalphaC[i]:=ImageOfalphaC[i] 
+ alpha[ii]*ImageOfIntegralBasisElementC[i][ii];
end for; //ii
end for; //i

//TESTING
/*
fprintf LogFile, "ImageOfalphaC = %o\n", ImageOfalphaC;
fprintf LogFile, "ImageOfIntegralBasisElementC[1] = %o\n", ImageOfIntegralBasisElementC[1];
alpha[2]*ImageOfIntegralBasisElementC[1][2]
+alpha[3]*ImageOfIntegralBasisElementC[1][3];
alpha[1]*ImageOfIntegralBasisElementC[1][1];
*/
////////////////////////////////////////////////////////////////////////////
/*
For each p[l]:

If we are NOT in the case where there are no unramified degree one primes above p[l], we fix the index i0 as in Section 7.  We will represent i0 by the unique pair of integers (i,j) such that 
theta^{(i_0)} = theta_i^{(j)}.  
i0[l] will be a sequence of two integers such that
theta^{(i_0)} is represented by thetap[l][i0[l][1]][i0[l][2]]

If there are no unramified degree one primes above p[l], i0[l] will still be a sequence of two integers, but it will have no real meaning. 
*/
////////////////////////////////////////////////////////////////////////////
i0:=[];
for l:=1 to v do
i0[l]:=[kk[l],1];
end for;


////////////////////////////////////////////////////////////////////////////
/*
For each p[l]:

If we are NOT in the case where there are no unramified degree one primes 
above p[l], we choose the indices j,k according to the guidelines in 
Section 9.  As with i0 we represent j by a sequence of two integers jjj[l] 
in such a way that theta^{(j)} is represented by 
thetap[l][jjj[l][1]][jjj[l][2]].  Similarly, for k.  

Suppose we find a choice of j,k that lets us use Lemma 7.4 to compute n_l 
immediately.  If we compute a value for n_l that is not a nonnegative 
integer, we move onto the next case using the continue command.  If we 
compute a value for n_l that is nonnegative, then we absorb 
pi_l^n_l = ppi[l]^n_l into alpha and stop considering the index l in the 
rest of the algorithm, except in the last steps. 

If there are no unramified degree one primes above p[l], we know that the 
value of n_l is zero and we will stop considering the index l in the 
algorithm, except in the last steps.

For l = 1,...,v:
If we know the value of n_l, then ValueOfn[l]:= that value
If we don't know the value of n_l, then ValueOfn[l]:=-1

JJ = set of those indices l in {1,...,v} for which there is at least one 
unramified degree one prime above p[l].

By the end of this block of code, 
J = the set of all indices in {1,...,v} that we need to consider in the 
rest of the algorithm, except the last steps.  These are the indices l 
for which there is at least one unramified degree one prime above p[l] 
and there is no choice of j,k that lets us use Lemma 7.4 to compute n_l. 

It will be convenient to have defined the following set of indices
JJJ := {1} union { 1+l : l in J} union { 1+v+i : i in {1,...,r}} 

I = set of those l in J for which there is no choice of j,k that lets us 
use Lemma 8.3 to bound n_l.

I2 = J - I.

For each l in I, jl[l] is the unique index such that JJJ[jl[l]]=l+1.

We will compute delta_1 and delta_2 for each l in J

We will compute the numbers alpha_i from Section 8 for each l in J:
alpha_i = LogarithmicAlphap[l][i]

We could compute the alpha_i and delta1, delta2 from Section 8 for each 
l in {1,...,v} for which there is at least one unramified degree one prime 
above p[l] or even for each l in {1,...,v}, 
but we don't.

For l in I:
SpecialCase[l] = true if the choice of j,k puts us in the special 
case of Section 17.
SpecialCase[l] = false otherwise (general case)

Nstar[l] = N_{l}^{*} from Section 11.

Initialize ihat[l] from Section 17.  Note ihat[l] in JJJ, ihat[l] neq 2.

Intizalize istar[l]. 

Eventually, istar[l] will be the index in {2,...,1+v+r} such that
ihat[l] = JJJ[istar[l]].

Possibly define ihat[l] and istar[l] for some l.
*/
////////////////////////////////////////////////////////////////////////////
ValueOfn:=[];
for l:=1 to v do
ValueOfn[l]:=-1; //initialize
end for;

Nstar:=[];
for l:=1 to v do
Nstar[l]:=padicprecision[l]+1; //initialize
/*the largest possible value of Valuation(x) for x an element of FFFppF[l] is padicprecision[l]*/
end for;

u:=[];
for l:=1 to v do
u[l]:=-1; //initialize
end for;

SpecialCase:=[];
for l:=1 to v do
SpecialCase[l]:=false; //initialize
end for;

ihat:=[];
for l:=1 to v do
ihat[l]:=0; //initialize to a value that ihat[l] can never assume
end for;

istar:=[];
for l:=1 to v do
istar[l]:=0; //initialize to a value that istar[l] can never assume
end for;


//start with J={1,...,v}
J:=[];
for l:=1 to v do
J[l]:=l;
end for;


/* 
Remove from J all the indices l such that p[l] has no unramified degree one primes above it.  
After they are removed, we know that, for every l in J, g has at least one linear factor 
in Q_{p_l}.  Also set the value of n_l for these indices l. 
*/
for l:=1 to v do
if kk[l] eq m[l]+1 then /*no degree one unramified primes above p_l*/
ValueOfn[l]:=0; 
/* now absorb pi_l^n_l = ppi[l]^n_l into alpha and remove the index l from J */
//alpha:=alpha*ppi[l]^ValueOfn[l]; //this does nothing!
Exclude(~J,l);
end if; 
end for;
 
/*JJ = set of those indices l in {1,...,v} for which there is at least one unramified degree one prime above p[l].*/
JJ:=J;

//fprintf LogFile, "JJ = %o\n", JJ;


//initialize delta1,delta2
delta1:=[**];
delta2:=[**];
for l:=1 to v do
delta1[l]:=FFFppF[l] ! 1;
delta2[l]:=FFFppF[l] ! 1;
end for;

//Now select j,k.  We will remove indices from J and I (if possible) as we go.
jjj:=[];
kkk:=[];
LogarithmicAlphap:=[];
CoefficientsLogarithmicAlphap:=[];
for l:=1 to v do
LogarithmicAlphap[l]:=[**];
CoefficientsLogarithmicAlphap[l]:=[**];
for i:=1 to 1+v+r do
LogarithmicAlphap[l][i]:=0;
CoefficientsLogarithmicAlphap[l][i]:=0;
end for;
end for;

for l in JJ do
/*try to find a choice of j,k that gives ord_{p_l}(delta_1) \neq 0*/
for i:=1 to m[l] do
if i eq i0[l][1] then continue i; end if;
for j:=1 to e[l][i]*f[l][i] do
jjj[l]:=[i,j];
for ii:=i to m[l] do
if ii eq i0[l][1] then continue ii; end if;
for jj:=1 to e[l][ii]*f[l][ii] do
if ii eq i and jj le j then continue jj; end if;
kkk[l]:=[ii,jj];
/*the last if statement ensures that we never try both j=a,k=b and j=b,k=a*/

delta1[l]:= ((thetap[l][i0[l][1]][i0[l][2]] - thetap[l][jjj[l][1]][jjj[l][2]])/(thetap[l][i0[l][1]][i0[l][2]] - thetap[l][kkk[l][1]][kkk[l][2]]))*(ImageOfzetap[l][kkk[l][1]][kkk[l][2]]/ImageOfzetap[l][jjj[l][1]][jjj[l][2]])*(ImageOfalphap[l][kkk[l][1]][kkk[l][2]]/ImageOfalphap[l][jjj[l][1]][jjj[l][2]]);

if Valuation(delta1[l]) ne 0 then

delta2[l]:= ((thetap[l][jjj[l][1]][jjj[l][2]] - thetap[l][kkk[l][1]][kkk[l][2]])/(thetap[l][kkk[l][1]][kkk[l][2]] - thetap[l][i0[l][1]][i0[l][2]]))*(ImageOfzetap[l][i0[l][1]][i0[l][2]]/ImageOfzetap[l][jjj[l][1]][jjj[l][2]])*(ImageOfalphap[l][i0[l][1]][i0[l][2]]/ImageOfalphap[l][jjj[l][1]][jjj[l][2]]);

tempValueOfnl:=(Min([Valuation(delta1[l]),0]) - Valuation(delta2[l]))/hh[l];

if not IsIntegral(tempValueOfnl) or tempValueOfnl lt 0 then 
fprintf LogFile, "No solutions possible in case iiii = %o\n", iiii;
fprintf LogFile, "Valuation(delta1[l]) = %o, ValueOfn[l] = %o\n", Valuation(delta1[l]), tempValueOfnl;
continue iiii; // b/c no solutions
end if;

ValueOfn[l]:=Integers() ! tempValueOfnl;
 
/* now absorb pi_l^n_l = ppi[l]^n_l into alpha and remove the index l from J */
alpha:=alpha*ppi[l]^ValueOfn[l];
Exclude(~J,l);

//Recompute ImageOfalphap[l]
ImageOfalphap[l]:=[];
for i1:=1 to m[l] do
ImageOfalphap[l][i1]:=[**];
for j1:=1 to e[l][i1]*f[l][i1] do
ImageOfalphap[l][i1][j1]:=0;
for ii1:= 1 to n do
ImageOfalphap[l][i1][j1]:=ImageOfalphap[l][i1][j1] 
+ alpha[ii1]*ImageOfIntegralBasisElementp[l][i1][j1][ii1];
end for; //ii1
end for; //j1
end for; //i1

//Recompute ImageOfalphaC
ImageOfalphaC:=[ComplexField()|];
for i1:=1 to n do
ImageOfalphaC[i1]:=0;
for ii1:= 1 to n do
ImageOfalphaC[i1]:=ImageOfalphaC[i1] 
+ alpha[ii1]*ImageOfIntegralBasisElementC[i1][ii1];
end for; //ii1
end for; //i1

//found a choice of j,k that gives ord_{p_l}(delta_1) \neq 0 for the current l, 
//move onto the next l
continue l;
end if; // controlled by Valuation(delta1[l]) ne 0

end for; //end jj loop
end for; //end ii loop
end for; //end j loop
end for; //end i loop
end for; //end l loop

//We are now finished defining J
/*J = the set of all indices in {1,...,v} that we need to consider in the rest of the algorithm, 
except the last steps.  These are the indices l for which there is at least one unramified degree 
one prime above p[l] and there is no choice of j,k that lets us use Lemma 6.4 to compute n_l.*/

nJ:=#J;
//fprintf LogFile, "J = %o\n", J;


////////////
/*
It will be convenient to have defined the following set of indices
JJJ := {1} union { 1+l : l in J} union { 1+v+i : i in {1,...,r} }
*/
//////////
JJJ:=[1];
for l in J do
Append(~JJJ,1+l);
end for;
for i:=1 to r do
Append(~JJJ,1+v+i);
end for;
nJJJ:=#JJJ;

/*we start with I = J and remove indices from I as we go. 
Want to make I = set of those l in J for which there is 
no choice of j,k that lets us use Lemma 8.3 to bound n_l.*/
I:=J;

for l in J do
if FindAll then
/*
If the program makes it this far, we know that there is no choice of j,k such that ord_{p_l}(delta_1) \neq 0.
Now we try to find a choice of j,k such that Lemma 8.3 can be used to find an upper bound on n_l
*/
bestjjjl:=[0,0];
bestkkkl:=[0,0];
bestNstarl:=padicprecision[l]+1;

for i:=1 to m[l] do
if i eq i0[l][1] then continue i; end if;
for j:=1 to e[l][i]*f[l][i] do
jjj[l]:=[i,j];
for ii:=i to m[l] do
if ii eq i0[l][1] then continue ii; end if;
for jj:=1 to e[l][ii]*f[l][ii] do
if ii eq i and jj le j then continue jj; end if;
kkk[l]:=[ii,jj];
/*the last if statement ensures that we never try both j=a,k=b and j=b,k=a*/

//define delta1[l] and delta2[l]
delta1[l]:= ((thetap[l][i0[l][1]][i0[l][2]] - thetap[l][jjj[l][1]][jjj[l][2]])/(thetap[l][i0[l][1]][i0[l][2]] - thetap[l][kkk[l][1]][kkk[l][2]]))*(ImageOfzetap[l][kkk[l][1]][kkk[l][2]]/ImageOfzetap[l][jjj[l][1]][jjj[l][2]])*(ImageOfalphap[l][kkk[l][1]][kkk[l][2]]/ImageOfalphap[l][jjj[l][1]][jjj[l][2]]);
delta2[l]:= ((thetap[l][jjj[l][1]][jjj[l][2]] - thetap[l][kkk[l][1]][kkk[l][2]])/(thetap[l][kkk[l][1]][kkk[l][2]] - thetap[l][i0[l][1]][i0[l][2]]))*(ImageOfzetap[l][i0[l][1]][i0[l][2]]/ImageOfzetap[l][jjj[l][1]][jjj[l][2]])*(ImageOfalphap[l][i0[l][1]][i0[l][2]]/ImageOfalphap[l][jjj[l][1]][jjj[l][2]]);

//define alpha_i's for i in JJJ
LogarithmicAlphap[l][1]:=pAdicLog(delta1[l],p[l],padicprecision[l]);
if IsZeroLocal(pAdicLog(delta1[l],p[l],padicprecision[l]),SS[l]) then
else
for iii in J do
LogarithmicAlphap[l][1+iii]:=pAdicLog(ImageOfpip[iii][kk[iii]][l][kkk[l][1]][kkk[l][2]]/ImageOfpip[iii][kk[iii]][l][jjj[l][1]][jjj[l][2]],p[l],padicprecision[l]);
end for;
for iii:=1 to r do
LogarithmicAlphap[l][1+v+iii]:=pAdicLog(ImageOfepsp[iii][l][kkk[l][1]][kkk[l][2]]/ImageOfepsp[iii][l][jjj[l][1]][jjj[l][2]],p[l],padicprecision[l]);
end for;

/*
function TestpAdicLog(x,p)
e:=AbsoluteRamificationIndex(Parent(x));
fprintf LogFile, "e = %o\n", e;
f:=AbsoluteInertiaDegree(Parent(x));
fprintf LogFile, "f = %o\n", f;
CandidateOrders:=Divisors(p^f - 1);
o:=1;
for oo in CandidateOrders do
if Valuation(x^oo - 1) gt 0 then o:=oo; break; end if;
end for;
j:=1;
while p^j le e do
j +:= 1; //j:=j+1;
end while;
fprintf LogFile, "j = %o\n", j;
fprintf LogFile, "x^(o*p^j) = %o\n", x^(o*p^j);
fprintf LogFile, "Log(x^(o*p^j)) = %o\n", Log(x^(o*p^j));
fprintf LogFile, "Coefficients(Log(x^(o*p^j))) = %o\n", Coefficients(Log(x^(o*p^j)));
fprintf LogFile, "Parent(x) ! Coefficients(Log(x^(o*p^j)))[2] = %o\n", Parent(x) ! Coefficients(Log(x^(o*p^j)))[2];
fprintf LogFile, "o*p^j = %o\n", o*p^j;
fprintf LogFile, "o*p^j = %o\n", Parent(x) ! o*p^j;
fprintf LogFile, "Coefficients(o*p^j) = %o\n", Coefficients(Parent(x) ! o*p^j);
return Log( x^(o*p^j) )/(o*p^j);
end function;
*/

//get the coefficients of the alpha_i's: the alpha_{ih}'s
for iii in JJJ do
CoefficientsLogarithmicAlphap[l][iii]:=GetCoefficients(LogarithmicAlphap[l][iii],l);
end for;


/*Check if Lemma 8.3 can be applied and, if so, compute Nstar[l] = N_{l}^{*}.*/
min:=Valuation(LogarithmicAlphap[l][JJJ[2]]);
for iii:=2 to nJJJ do
if Valuation(LogarithmicAlphap[l][JJJ[iii]]) lt min then 
min:=Valuation(LogarithmicAlphap[l][JJJ[iii]]); 
end if;
end for; 

if Valuation(LogarithmicAlphap[l][1]) lt min then
temp:=Max([  Floor((1/hh[l])*(1/(p[l]-1) - Valuation(delta2[l]))), 
Ceiling((1/hh[l])*(min - Valuation(delta2[l])))-1  ]);
if temp lt 0 then 
fprintf LogFile, "No solutions possible in case iiii = %o because Nstar[l] < 0, l = %o\n", iiii, l;
continue iiii; 
end if; //no solutions in the current case
if temp lt Nstar[l] then Nstar[l]:=temp; end if;
end if;


for hhh:=1 to SS[l] do
if IsZeroLocal(CoefficientsLogarithmicAlphap[l][1][hhh],SS[l]) then continue hhh;
else

min:=Valuation(CoefficientsLogarithmicAlphap[l][JJJ[2]][hhh]);
for iii:=2 to nJJJ do
//fprintf LogFile, "Valuation(CoefficientsLogarithmicAlphap[l][JJJ[iii]][hhh]) = %o\n", Valuation(CoefficientsLogarithmicAlphap[l][JJJ[iii]][hhh]);
if Valuation(CoefficientsLogarithmicAlphap[l][JJJ[iii]][hhh]) lt min then 
min:=Valuation(CoefficientsLogarithmicAlphap[l][JJJ[iii]][hhh]); 
end if;
end for; //end iii loop
if Valuation(CoefficientsLogarithmicAlphap[l][1][hhh]) lt min then
temp:=Max([  Floor((1/hh[l])*(1/(p[l]-1) - Valuation(delta2[l]))), 
Ceiling((1/hh[l])*(u[l] + min - Valuation(delta2[l])))-1   ]);
if temp lt 0 then 
fprintf LogFile, "No solutions possible in case iiii = %o because Nstar[l] < 0, l = %o\n", iiii, l;
continue iiii; 
end if; //no solutions in the current case
if temp lt Nstar[l] then Nstar[l]:=temp; end if;
end if;

end if; //controlled by IsZeroLocal(CoefficientsLogarithmicAlphap[l][1][hhh],SS[l])
end for; //end hhh loop

if Nstar[l] lt bestNstarl then
//we've found a choice of j,k that lets us use Lemma 8.3 to bound n_l
//and its better (smaller bound) than the previous best choice for j,k that lets us 
//use Lemma 8.3.
bestjjjl:=jjj[l];
bestkkkl:=kkk[l]; 
bestNstarl:=Nstar[l]; 
end if;

/*
if Nstar[l] lt padicprecision[l]+1 then 
//we've found a choice of j,k that lets us use Lemma 8.3 to bound n_l
Exclude(~I,l);
continue l; 
end if;
*/
 
end if; //controlled by IsZeroLocal(pAdicLog(delta1[l],p[l],padicprecision[l]),SS[l])

end for;
end for;
end for;
end for;

if bestNstarl lt padicprecision[l]+1 then
//we've found a choice of j,k that lets us use Lemma 8.3 to bound n_l
//and it's the best choice
jjj[l]:=bestjjjl;
kkk[l]:=bestkkkl;
Nstar[l]:=bestNstarl;
Exclude(~I,l);
continue l; 
end if;

end if; //controlled by FindAll


/*
If the program makes it this far, we know that there is no choice of j,k 
such that ord_{p_l}(delta_1) \neq 0 and also there is no choice of j,k 
that lets us use Lemma 8.3 to get an upper bound on n_l.  So we will 
eventually need to use linear forms in logs + lattice reduction to get 
a small upper bound on n_l
  
Now we try to find a choice of j,k according to the remaining guidlines 
in Section 9.  The whole point is to try to choose j,k so that 
alpha_i /  alpha_{ihat} is in Q_{p_l} for all i in J.

For each candidate j,k, we first do some simple checks for conditions that imply alpha_i /  alpha_{ihat} is in Q_{p_l} for all i in J.  If we are forced to check directly whether alpha_i /  alpha_{ihat} is in Q_{p_l} for all i, we do this for all candidates for ihat.  If we find a candidate for ihat that works, we remember it.
*/


/* check if we can take j,k so that theta^{(j)},theta^{(k)} are roots of linear factors of g(t) in Q_{p_l}[t] */
jfound:=false;
for i:=1 to m[l] do
if i eq i0[l][1] then continue i; end if;
if Degree(gp[l][i]) eq 1 then
 
if jfound eq false then 
jjj[l]:=[i,1];
jfound:=true;
continue i;
end if;

if jfound eq true then 
kkk[l]:=[i,1];
/* we've found a choice for j,k so that theta^{(j)},theta^{(k)} are roots of linear factors of g(t) in Q_{p_l}[t] Section 17 */
SpecialCase[l]:=true;
continue l; 
end if;

end if;
end for; //end i loop


/* 
check if we can take j,k so that theta^{(j)}, theta^{(k)} are the roots of a degree 2 factor of g(t) Q_{p_l}[t] 
*/
for i:=1 to m[l] do
if Degree(gp[l][i]) eq 2 then
jjj[l]:=[i,1];
kkk[l]:=[i,2];
/* 
we've found a j,k so that theta^{(j)}, theta^{(k)} are the roots of a degree 2 factor of g(t) Q_{p_l}[t] 
*/
SpecialCase[l]:=true;
continue l;
end if;
end for; //end i loop


/*
If there is a nonlinear factor g^{\prime}(t) of g(t) in Q_{p_l}[t] such that the 
extension of Q_{p_l} that g^{\prime}(t) generates contains all the 
roots of g^{\prime}(t) (equivalently, the extension is Galois), then 
taking j,k so that \theta^{(j)},\theta^{(k)} are two roots of 
g^{\prime}(t) will ensure that alpha_i /  alpha_{ihat} is in Q_{p_l} 
for all i.

If an irreducible polynomial over Q_{p_l}[t] is neither inertial nor 
eisenstein, MAGMA does not support directly constructing the extension 
of Q_{p_l} generated by the polynomial.  However, we know that the 
extension of Q_{p_l} generated by g^{\prime}(t) is isomorphic to the 
completion of K at the prime ideal above p_l which corresponds to 
g^{\prime}(t).  

Note also that irreducible polynomials over p-adic fields have no 
repeated roots (since p-adic fields have characteristic zero).
*/

for i:=1 to m[l] do
if Degree(gp[l][i]) gt 1 and 
#Roots(gp[l][i],Kpp[l][i]) eq Degree(gp[l][i]) then
jjj[l]:=[i,1];
kkk[l]:=[i,2];
/* 
we've found j,k that ensure alpha_i / alpha_{ihat} is in Z_{p_l} for all i and all candidates for ihat.
*/
SpecialCase[l]:=true;
continue l;
end if;
end for; 

/* 
Now we do the more difficult checks to see if we can choose j,k such that 
alpha_i /  alpha_{ihat} is in Z_{p_l} for all i,j
*/

for i:=1 to m[l] do
if i eq i0[l][1] then continue i; end if;
for j:=1 to e[l][i]*f[l][i] do
jjj[l]:=[i,j];
for ii:=i to m[l] do
if ii eq i0[l][1] then continue ii; end if;
for jj:=1 to e[l][ii]*f[l][ii] do
if ii eq i and jj le j then continue jj; end if;
kkk[l]:=[ii,jj];


//define delta1[l] and delta2[l]
delta1[l]:= ((thetap[l][i0[l][1]][i0[l][2]] - thetap[l][jjj[l][1]][jjj[l][2]])/(thetap[l][i0[l][1]][i0[l][2]] - thetap[l][kkk[l][1]][kkk[l][2]]))*(ImageOfzetap[l][kkk[l][1]][kkk[l][2]]/ImageOfzetap[l][jjj[l][1]][jjj[l][2]])*(ImageOfalphap[l][kkk[l][1]][kkk[l][2]]/ImageOfalphap[l][jjj[l][1]][jjj[l][2]]);

delta2[l]:= ((thetap[l][jjj[l][1]][jjj[l][2]] - thetap[l][kkk[l][1]][kkk[l][2]])/(thetap[l][kkk[l][1]][kkk[l][2]] - thetap[l][i0[l][1]][i0[l][2]]))*(ImageOfzetap[l][i0[l][1]][i0[l][2]]/ImageOfzetap[l][jjj[l][1]][jjj[l][2]])*(ImageOfalphap[l][i0[l][1]][i0[l][2]]/ImageOfalphap[l][jjj[l][1]][jjj[l][2]]);

//define alpha_i's for i in JJJ
LogarithmicAlphap[l][1]:=pAdicLog(delta1[l],p[l],padicprecision[l]);
for iii in J do
LogarithmicAlphap[l][1+i]:=pAdicLog(ImageOfpip[iii][kk[iii]][l][kkk[l][1]][kkk[l][2]]/ImageOfpip[iii][kk[iii]][l][jjj[l][1]][jjj[l][2]],p[l],padicprecision[l]);
end for;
for iii:=1 to r do
LogarithmicAlphap[l][1+v+i]:=pAdicLog(ImageOfepsp[iii][l][kkk[l][1]][kkk[l][2]]/ImageOfepsp[iii][l][jjj[l][1]][jjj[l][2]],p[l],padicprecision[l]);
end for;

//get the coefficients of the alpha_i's: the alpha_{ih}'s
for iii in JJJ do
CoefficientsLogarithmicAlphap[l][iii]:=GetCoefficients(LogarithmicAlphap[l][iii],l);
end for;


/* 
Check if there is a choice of j,k such that the alpha_i (i in JJJ) all belong to $\QQ_{p_l}$.  
*/
flag:=true;
for iii in JJJ do
for hhh:=2 to SS[l] do
if not IsZero(CoefficientsLogarithmicAlphap[l][iii][hhh]) then flag:=false; break iii; end if;
end for;
end for;
if flag eq true then 
//we've found a choice of j,k with desired properties
SpecialCase[l]:=true; 
continue l;
end if;


/*
Now we check directly whether we have alpha_i /  alpha_{ihat} in Q_{p_l} for all i.  We do this for all candidates for ihat.
*/

//find all candidates for istar (hence for ihat)
candidatesforistar:=[];
min:=Valuation(LogarithmicAlphap[l][JJJ[2]]);
for iii:=JJJ[2] to JJJ[nJJJ] do
if Valuation(LogarithmicAlphap[l][iii]) lt min then 
min:=Valuation(LogarithmicAlphap[l][iii]); 
end if;
end for;
for iiiiii:=2 to nJJJ do
iii:=JJJ[iiiiii];
if min eq Valuation(LogarithmicAlphap[l][iii]) then Append(~candidatesforistar,iiiiii); end if;
end for; 


/* For all candidates for ihat, check whether alpha_i /  alpha_{ihat} in Q_{p_l} for all i in JJJ */
temp:=[];
for istarstar in candidatesforistar do
ihathat:=JJJ[istarstar];
for iii in JJJ do
temp[iii]:=GetCoefficients(LogarithmicAlphap[l][iii]/LogarithmicAlphap[l][ihathat],l);
end for;
flag:=true;
for iii in JJJ do
for hhh:=2 to SS[l] do
if not IsZero(temp[iii][hhh]) then flag:=false; break iii; end if;
end for;
end for;
if flag eq true then 
/* we've found a choice of j,k with the desired properties */
SpecialCase[l]:=true;
ihat[l]:=ihathat;
istar[l]:=istarstar; 
continue l;
end if;
end for;


end for; //jj
end for; //ii
end for; //j
end for; //i


/*
If the program makes it this far, it means there is no choice of j,k for 
which ord_{p_l}(delta_1) = 0, no choice for which Lemma 8.3 gives an upper 
bound for n_l, and no choice which puts us in the special case of Section 17 
(alpha_i /  alpha_{ihat} in Z_{p_l} for all i).

We know that there are at most two degree one factors of g(t) in Q_{p_l}[t] 
and there are no degree two factors.  So there is at least one factor of 
degree >= 3.  We choose a nonlinear factor of g(t) in Q_{p_l}[t] of minimal 
degree and choose j,k so that \theta^{(j)}, \theta^{(k)} are roots of that factor.
*/

minimaldegreegreaterthan1:=Degree(FFFppF[l],PrimeField(FFFppF[l])); 
//initialize, no gp[l][i] can have degree strictly larger than this

for i:=1 to m[l] do
if Degree(gp[l][i]) gt 1 and Degree(gp[l][i]) lt minimaldegreegreaterthan1 then
minimaldegreegreaterthan1:=Degree(gp[l][i]);
jjj[l]:=[i,1];
kkk[l]:=[i,2];
end if;
end for;

end for; //end l loop

I2:=J; //J = I union I2, I intersect I2 = empty
for l in I do
Exclude(~I2,l);
end for;

//For each l in I, jl[l] is the unique index such that JJJ[jl[l]]=l+1.
jl:=[];
for i:=1 to v do
jl[i]:=0;
end for;
for l in I do
for i:=2 to 1+#J do
if JJJ[i] eq l+1 then jl[l]:=i; break i; end if;
end for;
end for;


///////////////////////////////////////////////////////////////////////////
/*
For each l in I, we will find a value for the index ihat 
and compute the beta_i's from Section 17: ihat[l], beta[l][i]

We also define d_l from Section 17: dd[l]

If we are in the special case, it can be that a choice of ihat[l] was 
already made in the last step. If ihat[l] >0, we know this choice has 
been made. Otherwise, ihat[l] = 0 and we know a choice hasn't been 
made yet.
*/
//////////////////////////////////////////////////////////////////////////


beta:=[];
dd:=[];
for l:=1 to v do
beta[l]:=[**];
end for;

for l in I do

//define delta1[l] and delta2[l]

delta1[l]:= ((thetap[l][i0[l][1]][i0[l][2]] - thetap[l][jjj[l][1]][jjj[l][2]])/(thetap[l][i0[l][1]][i0[l][2]] - thetap[l][kkk[l][1]][kkk[l][2]]))*(ImageOfzetap[l][kkk[l][1]][kkk[l][2]]/ImageOfzetap[l][jjj[l][1]][jjj[l][2]])*(ImageOfalphap[l][kkk[l][1]][kkk[l][2]]/ImageOfalphap[l][jjj[l][1]][jjj[l][2]]);

delta2[l]:= ((thetap[l][jjj[l][1]][jjj[l][2]] - thetap[l][kkk[l][1]][kkk[l][2]])/(thetap[l][kkk[l][1]][kkk[l][2]] - thetap[l][i0[l][1]][i0[l][2]]))*(ImageOfzetap[l][i0[l][1]][i0[l][2]]/ImageOfzetap[l][jjj[l][1]][jjj[l][2]])*(ImageOfalphap[l][i0[l][1]][i0[l][2]]/ImageOfalphap[l][jjj[l][1]][jjj[l][2]]);

//define alpha_i's
LogarithmicAlphap[l][1]:=pAdicLog(delta1[l],p[l],padicprecision[l]);
for iii in J do
LogarithmicAlphap[l][1+iii]:=pAdicLog(ImageOfpip[iii][kk[iii]][l][kkk[l][1]][kkk[l][2]]/ImageOfpip[iii][kk[iii]][l][jjj[l][1]][jjj[l][2]],p[l],padicprecision[l]);
end for;
for iii:=1 to r do
LogarithmicAlphap[l][1+v+iii]:=pAdicLog(ImageOfepsp[iii][l][kkk[l][1]][kkk[l][2]]/ImageOfepsp[iii][l][jjj[l][1]][jjj[l][2]],p[l],padicprecision[l]);
end for;

if SpecialCase[l] eq true then

if ihat[l] eq 0 then
min:=Valuation(LogarithmicAlphap[l][JJJ[2]]);
ihat[l]:=JJJ[2];
istar[l]:=2;
for i:=3 to #JJJ do
iii:=JJJ[i];
if Valuation(LogarithmicAlphap[l][iii]) lt min then 
min:=Valuation(LogarithmicAlphap[l][iii]);
ihat[l]:=iii;
istar[l]:=i;
end if;
end for;
end if;

for iii:=1 to 1+v+r do
beta[l][iii] := -LogarithmicAlphap[l][iii]/LogarithmicAlphap[l][ihat[l]];
/* 
For l in I, we know that the beat_i's live in Z_{p_l}.  So their 
coefficients on the power basis for FFFppF[l] are all zero, except for the 
first.  We can use this to save on computations with the beta_i's: 
*/
beta[l][iii] := GetCoefficients(beta[l][iii],l)[1];
end for;

dd[l]:=Valuation(delta2[l]) - Valuation(LogarithmicAlphap[l][ihat[l]]);

else //SpecialCase[l] eq false //general case

//get the coefficients of the alpha_i's: the alpha_{ih}'s
for iii:=1 to 1+v+r do
CoefficientsLogarithmicAlphap[l][iii]:=GetCoefficients(LogarithmicAlphap[l][iii],l);
end for;

// Choose an index h in {1,...,S[l]} such that alpha_{ih} nonzero for at least one i>1.
temphhh:=1;
for hhh:=1 to SS[l] do
min:=Valuation(CoefficientsLogarithmicAlphap[l][JJJ[2]][hhh]);
ihat[l]:=JJJ[2];
istar[l]:=2;
for i:=3 to #JJJ do
iii:=JJJ[i];
if Valuation(CoefficientsLogarithmicAlphap[l][iii][hhh]) lt min then 
min:=Valuation(CoefficientsLogarithmicAlphap[l][iii][hhh]);
ihat[l]:=iii;
istar[l]:=i;
end if;
end for; //end i loop
if IsZeroLocal(CoefficientsLogarithmicAlphap[l][ihat[l]][hhh],SS[l]) then
else
temphhh:=hhh; break hhh;
end if;
end for; // end hhh loop
hhh:=temphhh;

for iii:=1 to 1+v+r do
beta[l][iii] := -CoefficientsLogarithmicAlphap[l][iii][hhh] / CoefficientsLogarithmicAlphap[l][ihat[l]][hhh];
end for;

dd[l]:=Valuation(delta2[l]) - Valuation(LogarithmicAlphap[l][ihat[l]]) - u[l];

end if;

end for; //end l






//////////////////////////////////////////////////////////////////////////
////////////////////////////////////
/////////////////
/*
Compute c_1(l) = c1[l] for each l in I 
*/
////////////////
///////////////////////////////////
//////////////////////////////////////////////////////////////////////////

//////////////////////
/*

For each l in I:

Find preimages in FFF of theta^{(i_0)}, theta^{(j)}, theta^{(k)} under the embedding sigma = mFFFppF[L] of FFF into FFFppF[l].  We choose not to use MAGMA's bulit in preimage-finder to avoid round-off errors.

To find the preimage of theta^{(i_0)}, we actually find the index ii0 in {1,...,n} such that mFFFppF[L](thetaF[ii0]) = thetap[l][i0[1]][i0[2]].
Similarly for theta^{(j)}, theta^{(k)}.

PreimageOfalphaj = preimage in FFF of \alpha^{(j)} under the embedding sigma = mFFFppF[L] of FFF into FFFppF[l]

PreimageOfzetaj = preimage in FFF of \zeta^{(j)} under the embedding sigma = mFFFppF[L] of FFF into FFFppF[l]

PreimageOfalphak = preimage in FFF of \alpha^{(k)} under the embedding sigma = mFFFppF[L] of FFF into FFFppF[l]

PreimageOfzetak = preimage in FFF of \zeta^{(k)} under the embedding sigma = mFFFppF[L] of FFF into FFFppF[l]

We also find the preimages of 
pi_{i}^{(j)}, pi_{i}^{(k)}, eps_{i}^{(j)}, eps_{i}^{(k)}
*/
/////////////////////

//intialization
c1:=[**];
rootsofginFFFppF:=[**];
PreimageOfalphaj:=[];
PreimageOfzetaj:=[];
PreimageOfalphak:=[];
PreimageOfzetak:=[];
for l:=1 to v do
c1[l]:=0;
rootsofginFFFppF[l]:=mFFFppF[l](rootsofginFFF);
end for;

for l in I do

//find preimage of \theta^{(i_0)}
max:=Valuation(thetap[l][i0[l][1]][i0[l][2]] - rootsofginFFFppF[l][1]);
ii0:=1;
for i:=2 to n do
if Valuation(thetap[l][i0[l][1]][i0[l][2]] - rootsofginFFFppF[l][i]) gt max then
max:=Valuation(thetap[l][i0[l][1]][i0[l][2]] - rootsofginFFFppF[l][i]);
ii0:=i;
end if;
end for;

//find preimage of \theta^{(j)}
max:=Valuation(thetap[l][jjj[l][1]][jjj[l][2]] - rootsofginFFFppF[l][1]);
ijjj:=1;
for i:=2 to n do
if Valuation(thetap[l][jjj[l][1]][jjj[l][2]] - rootsofginFFFppF[l][i]) gt max then
max:=Valuation(thetap[l][jjj[l][1]][jjj[l][2]] - rootsofginFFFppF[l][i]);
ijjj:=i;
end if;
end for;

//find preimage of \theta^{(k)}
max:=Valuation(thetap[l][kkk[l][1]][kkk[l][2]] - rootsofginFFFppF[l][1]);
ikkk:=1;
for i:=2 to n do
if Valuation(thetap[l][kkk[l][1]][kkk[l][2]] - rootsofginFFFppF[l][i]) gt max then
max:=Valuation(thetap[l][kkk[l][1]][kkk[l][2]] - rootsofginFFFppF[l][i]);
ikkk:=i;
end if;
end for;

PreimageOfzetaj:=0;
for i:= 1 to n do
PreimageOfzetaj:=PreimageOfzetaj + zeta[i]*ImageOfIntegralBasisElementF[ijjj][i];
end for; //i
PreimageOfalphaj:=0;
for i:= 1 to n do
PreimageOfalphaj:=PreimageOfalphaj + alpha[i]*ImageOfIntegralBasisElementF[ijjj][i];
end for; //i
PreimageOfzetak:=0;
for i:= 1 to n do
PreimageOfzetak:=PreimageOfzetak + zeta[i]*ImageOfIntegralBasisElementF[ikkk][i];
end for; //i
PreimageOfalphak:=0;
for i:= 1 to n do
PreimageOfalphak:=PreimageOfalphak + alpha[i]*ImageOfIntegralBasisElementF[ikkk][i];
end for; //i

/*
Note that: 
preimage of pi_{i}^{(j)} = ImageOfpiF[i][kk[i]][ijjj]
preimage of pi_{i}^{(k)} = ImageOfpiF[i][kk[i]][ikkk]
preimage of eps_{i}^{(j)} = ImageOfepsF[i][ijjj]
preimage of eps_{i}^{(k)} = ImageOfepsF[i][ikkk]
*/

///////////////////////////////////////
/*
Define the alpha_i for i in J, construct L, and find the prime ideal of L corresponding to sigma (see Section 11).
*/
//////////////////////////////////////
alphaALGEBRAIC:=[FFF|];
for i:=1 to 1 + v + r do
alphaALGEBRAIC[i]:=1; //initialize
end for;
alphaALGEBRAIC[1]:=((thetaF[ii0] - thetaF[ijjj]) / (thetaF[ii0] - thetaF[ikkk]))*(PreimageOfalphak/PreimageOfalphaj)*(PreimageOfzetak/PreimageOfzetaj);
for i in J do
alphaALGEBRAIC[1+i]:=ImageOfpiF[i][kk[i]][ikkk]/ImageOfpiF[i][kk[i]][ijjj];
end for;
for i:=1 to r do
alphaALGEBRAIC[1+v+i]:=ImageOfepsF[i][ikkk]/ImageOfepsF[i][ijjj];
end for;

LL:=sub<FFF | alphaALGEBRAIC>;
LLx<x>:=PolynomialRing(LL);
D:=Degree(LL);
mm:=1+#J+r;

ppL:=ppF[l] meet MaximalOrder(LL);
eppL:=RamificationIndex(ppL);
fppL:=InertiaDegree(ppL);



///////////////////////////////////////////////////////////////////////////////////
/*
Compute all the constants that go into Yu's Theorem
*/
///
////////////////////////////////////////////////////////////////////////////////
d:=D;
ff:=fppL;

if p[l] eq 2 and IsIrreducible(x^2 + x + 1) then
d:=2*D;
ff:=Max([2,fppL]);
end if;

if p[l] ge 3 and ((p[l]^fppL mod 4) eq 1) and IsIrreducible(x^3 + x^2 + x + 1) then
d:=2*D;
ff:=Max([2,fppL]);
end if;

delete x;
delete LLx;

kappa:=Floor(2*eppL*Log(p[l])/(p[l]-1));

//note d \geq 2 for us

// default case: p=2
kappa1:=160;
kappa2:=32;
kappa3:=40;
kappa4:=276;
kappa5:=16;
kappa6:=8;

if p[l] eq 3 then
kappa1:=759;
kappa2:=16;
kappa3:=20;
kappa4:=1074;
kappa5:=8;
kappa6:=4;
end if;

if p[l] ge 5 then
kappa5:=8;
kappa6:=4;

if eppL eq 1 then
kappa2:=8*(p[l]-1)/(p[l]-2);
kappa3:=10;
if p[l] mod 4 eq 1 then
kappa1:=1473;
kappa4:=394*(p[l]-1)/(p[l]-2);
end if;
if p[l] mod 4 eq 3 then
kappa1:=1282;
kappa4:=366*(p[l]-1)/(p[l]-2);
end if;
end if;

if eppL ge 2 then
kappa2:=16;
kappa3:=20;
if p[l] eq 5 then
kappa1:=319;
kappa4:=402;
end if;
if p[l] ge 7 and p[l] mod 4 eq 1 then
kappa1:=1502;
kappa4:=1372;
end if;
if p[l] ge 7 and p[l] mod 4 eq 3 then
kappa1:=2190;
kappa4:=1890;
end if;
end if;
end if;  

c2:=((((mm+1)^(mm+2)) * d^(mm+2))/(Factorial(mm-1))) * ( p[l]^ff / (ff*Log(p[l]))^3 ) * Max([1,Log(d)]) * Max( [4+Log(mm+1)+Log(d),eppL,ff*Log(p[l])] );


halphaALGEBRAIC:=[];
for i:=1 to 1+v+r do
halphaALGEBRAIC[i]:=AbsoluteLogarithmicHeight(alphaALGEBRAIC[i]);
end for;

c3prime:=kappa1 * kappa2^mm * (mm / ff*Log(p[l]) )^(mm-1);
for i in JJJ do
c3prime:=c3prime*Max([ halphaALGEBRAIC[i], ff*Log(p[l])/(kappa3*(mm+4)*d) ]);
end for;

c3primeprime:= kappa4 * kappa5^mm * Exp(mm) * p[l]^(kappa*(mm-1));
for i in JJJ do
c3primeprime:=c3primeprime*Max([ halphaALGEBRAIC[i], ff*Log(p[l])/(Exp(2)*kappa6*(p[l]^kappa)*d)  ]);
end for;

qu:=4; //default case: p \geq 3, p^f_pp \equiv 1 mod 4
if p[l] eq 2 then qu:=3; end if;
if p[l] ge 3 and p[l]^fppL mod 4 eq 3 then qu:=1; end if;

c1[l]:=(1/eppL)*(c2/qu)*Max([c3prime,c3primeprime]);

end for; //end l loop


////////////////////////////////////////////////////////////////////////////
/*
Done computing c1[l] for all l in I
*/
////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////
/*
Compute c4, c5 (with primed versions), c7
*/
///////////////////////////////////////////////////////////////////////////
c4prime:=0;
for l in I do
if c4prime lt c1[l]/hh[l] then c4prime:=c1[l]/hh[l]; end if;
end for;

c4primeprime:=0;
c5primeprime:=0;
for l in I2 do
if c4primeprime lt Nstar[l] then c4primeprime:=Nstar[l]; end if;
end for;

c4:=c4prime;
if c4prime lt c4primeprime then c4:=c4primeprime; end if;

c5:=0;
for l in I do
if c5 lt -Valuation(delta2[l])/hh[l] then c5:=-Valuation(delta2[l])/hh[l]; 
end if;
end for;


c6:=0;
if not IsEmpty(I) then

l:=I[1];
max:=c1[l]/hh[l]; if Exp(2) gt max then max:=Exp(2); end if;
c6:=2*(-Valuation(delta2[l])/hh[l] + max*Log(max));

for l in I do
max:=c1[l]/hh[l]; if Exp(2) gt max then max:=Exp(2); end if; 
if 2*( -Valuation(delta2[l])/hh[l] + max*Log(max)) gt c6 then 
c6:=2*( -Valuation(delta2[l])/hh[l] + max*Log(max));
end if;
end for;
c6:=Ceiling(c6)-1;

end if;

c7:=2;
if c4primeprime gt c7 then c7:=c4primeprime; end if; 

c7:=Max([2,c4primeprime,c6]);

///////////////////////////////////////////////////////////////////////////
/*
Compute c_{8}^{\prime}, c_{8}^{\prime \prime}, c_{9}^{\prime}, c_{9}^{\prime \prime}
*/
///////////////////////////////////////////////////////////////////////////
min:=Abs(ImageOfalphaC[1]*ImageOfzetaC[1]);
for i:=2 to n do
if Abs(ImageOfalphaC[i]*ImageOfzetaC[i]) lt min then min:=Abs(ImageOfalphaC[i]*ImageOfzetaC[i]); end if; 
end for;
c8prime:=Abs(a);
for i:=1 to v do
if i in J then
c8prime:= c8prime*p[i]^(ss[i]+tt[i]);
else
c8prime:= c8prime*p[i]^(ss[i]+tt[i]+ValueOfn[i]*hh[i]);
end if;
end for;
c8prime:=Log(c8prime/min);

prod:=1;
for i in J do
l:=i;
prod:=prod*ImageOfpiC[i][kk[i]][1];
end for;
min:=Abs(prod);
for ii:=2 to n do
prod:=1; 
for i in J do 
l:=i;
prod:=prod*ImageOfpiC[i][kk[i]][ii];
end for;
if Abs(prod) lt min then min:=Abs(prod); end if;
end for;
c9prime:=1;
for i in J do
c9prime:=c9prime*p[i]^hh[i];
end for;
c9prime:=Log(c9prime/min);

max:=Abs(ImageOfalphaC[1]*ImageOfzetaC[1]);
for i:=2 to n do
if Abs(ImageOfalphaC[i]*ImageOfzetaC[i]) gt max then max:=Abs(ImageOfalphaC[i]*ImageOfzetaC[i]); end if; 
end for;
c8primeprime:=Log(max);

prod:=1;
for i in J do
prod:=prod*ImageOfpiC[i][kk[i]][1];
end for;
max:=Abs(prod);
for ii:=2 to n do
prod:=1; 
for i in J do 
prod:=prod*ImageOfpiC[i][kk[i]][ii];
end for;
if Abs(prod) gt max then max:=Abs(prod); end if;
end for;
c9primeprime:=Log(max);

////////////////////////////////////////////////////////////////////////////
/*
If s > 0:
For each i0 in {1,...,s}, compute the indices j=j(i0), k=k(i0), and the numbers c16=c16(i0), c17=c17(i0), c18=c18(i0).
*/
////////////////////////////////////////////////////////////////////////////
jjjjjj:=[];
kkkkkk:=[];
c16:=[];
c17:=[];
c18:=[];
////////////////////////////////////////////////////////////////////////////
/*
s >= 3 case
*/
////////////////////////////////////////////////////////////////////////////
if s ge 3 then

sFFF:=Signature(FFF); //sFFF = number of real embeddings of \CC
LogarithmicAlphaC:=[];

for i0i0i0:=1 to s do

////////////////////////
/*
Choose j,k and compute c16
*/
/////////////////////////
max:=0;
for j:=1 to s do
if j eq i0i0i0 then continue j; end if;
for k:=j+1 to s do
if k eq i0i0i0 then continue k; end if;
OneOverc16:=(Abs(thetaC[i0i0i0] - thetaC[j])/2)*(Abs(thetaC[k] - thetaC[i0i0i0])/Abs(thetaC[j] - thetaC[k]));
if OneOverc16 gt max then 
max:=OneOverc16; 
jjjjjj[i0i0i0]:=j;
kkkkkk[i0i0i0]:=k;
end if;
end for;
end for;
c16[i0i0i0]:=1/max;
///////////////////////
/*
Select an embedding (sigma in Section 13) of FFF into the complex numbers
by selecting a conjugate in \CC (phidot) of the generator of FFF (FFF.1).

Find the images of the roots of g in \CC under this embedding: rootsofginC

Embedding FFF into \RR will produce a smaller constant c17[i0i0i0].

Define kappa.
*/
///////////////////////
kappa:=1;
if sFFF eq 0 then kappa:=2; end if;
phidot:=Conjugates(FFF.1)[1];
rootsofginC:=[];
for i:=1 to n do
rootsofginC[i]:=0*phidot;
for ii:=1 to Degree(FFF) do
rootsofginC[i]:=rootsofginC[i]+rootsofginFFF[i][ii]*phidot^(ii-1);
end for;
end for;

////////////////////////
/*
Find preimages in FFF of theta^{(i_0)}, theta^{(j)}, theta^{(k)} under the embedding sigma of FFF into \CC.  We choose not to use MAGMA's bulit in preimage-finder to avoid round-off errors.

To find the preimage of theta^{(i_0)}, we actually find the index ii0 in {1,...,n} such that sigma(thetaF[ii0]) = thetaC[i0i0i0].
Similarly for theta^{(j)}, theta^{(k)}.

PreimageOfalphaj = preimage in FFF of \alpha^{(j)} under the embedding sigma of FFF into \CC

PreimageOfzetaj = preimage in FFF of \zeta^{(j)} under the embedding sigma of FFF into \CC

PreimageOfalphak = preimage in FFF of \alpha^{(k)} under the embedding sigma of FFF into \CC

PreimageOfzetak = preimage in FFF of \zeta^{(k)} under the embedding sigma of FFF into \CC

We also find the preimages of 
pi_{i}^{(j)}, pi_{i}^{(k)}, eps_{i}^{(j)}, eps_{i}^{(k)}
*/
//////////////////////////
//find preimage of \theta^{(i_0)}
min:=Abs(thetaC[i0i0i0] - rootsofginC[1]);
ii0:=1;
for i:=2 to n do
if Abs(thetaC[i0i0i0] - rootsofginC[i]) lt min then
min:=Abs(thetaC[i0i0i0] - rootsofginC[i]);
ii0:=i;
end if;
end for;

//find preimage of \theta^{(j)}
min:=Abs(thetaC[jjjjjj[i0i0i0]] - rootsofginC[1]);
ijjj:=1;
for i:=2 to n do
if Abs(thetaC[jjjjjj[i0i0i0]] - rootsofginC[i]) lt min then
min:=Abs(thetaC[jjjjjj[i0i0i0]] - rootsofginC[i]);
ijjj:=i;
end if;
end for;

//find preimage of \theta^{(k)}
min:=Abs(thetaC[kkkkkk[i0i0i0]] - rootsofginC[1]);
ikkk:=1;
for i:=2 to n do
if Abs(thetaC[kkkkkk[i0i0i0]] - rootsofginC[i]) lt min then
min:=Abs(thetaC[kkkkkk[i0i0i0]] - rootsofginC[i]);
ikkk:=i;
end if;
end for;

PreimageOfzetaj:=0;
for i:= 1 to n do
PreimageOfzetaj:=PreimageOfzetaj + zeta[i]*ImageOfIntegralBasisElementF[ijjj][i];
end for; //i
PreimageOfalphaj:=0;
for i:= 1 to n do
PreimageOfalphaj:=PreimageOfalphaj + alpha[i]*ImageOfIntegralBasisElementF[ijjj][i];
end for; //i
PreimageOfzetak:=0;
for i:= 1 to n do
PreimageOfzetak:=PreimageOfzetak + zeta[i]*ImageOfIntegralBasisElementF[ikkk][i];
end for; //i
PreimageOfalphak:=0;
for i:= 1 to n do
PreimageOfalphak:=PreimageOfalphak + alpha[i]*ImageOfIntegralBasisElementF[ikkk][i];
end for; //i

/*
Note that: 
preimage of pi_{i}^{(j)} = ImageOfpiF[i][kk[i]][ijjj]
preimage of pi_{i}^{(k)} = ImageOfpiF[i][kk[i]][ikkk]
preimage of eps_{i}^{(j)} = ImageOfepsF[i][ijjj]
preimage of eps_{i}^{(k)} = ImageOfepsF[i][ikkk]
*/

///////////////////////////////////////
/*
Define the alpha_i for i in J, construct L.
*/
//////////////////////////////////////
alphaALGEBRAIC:=[FFF|];
for i:=1 to 1 + v + r do
alphaALGEBRAIC[i]:=1; //initialize
end for;
alphaALGEBRAIC[1]:=((thetaF[ii0] - thetaF[ijjj]) / (thetaF[ii0] - thetaF[ikkk]))*(PreimageOfalphak/PreimageOfalphaj)*(PreimageOfzetak/PreimageOfzetaj);
for i in J do
alphaALGEBRAIC[1+i]:=ImageOfpiF[i][kk[i]][ikkk]/ImageOfpiF[i][kk[i]][ijjj];
end for;
for i:=1 to r do
alphaALGEBRAIC[1+v+i]:=ImageOfepsF[i][ikkk]/ImageOfepsF[i][ijjj];
end for;

LL:=sub<FFF | alphaALGEBRAIC>;
d:=Degree(LL);
mm:=1+#J+r;

////////////////////////////////////
/* 
Compute c17.

Also compute the alpha_i as defined in Sections 18 and 20: LogarithmicAlphaC[i0i0i0][i]
*/
/////////////////////////////////////
LogarithmicAlphaC[i0i0i0]:=[RealField() | ];
for i:=1 to 1+v+r do
LogarithmicAlphaC[i0i0i0][i]:=0;
end for;

temp:=((thetaC[i0i0i0] - thetaC[jjjjjj[i0i0i0]])/(thetaC[i0i0i0] - thetaC[kkkkkk[i0i0i0]]))*(ImageOfzetaC[kkkkkk[i0i0i0]]/ImageOfzetaC[jjjjjj[i0i0i0]])*(ImageOfalphaC[kkkkkk[i0i0i0]]/ImageOfalphaC[jjjjjj[i0i0i0]]);
LogarithmicAlphaC[i0i0i0][1]:=Log(Abs(temp));

//fprintf LogFile, "(ImageOfalphaC[kkkkkk[i0i0i0]]/ImageOfalphaC[jjjjjj[i0i0i0]]) = %o\n", (ImageOfalphaC[kkkkkk[i0i0i0]]/ImageOfalphaC[jjjjjj[i0i0i0]]);
//fprintf LogFile, "(ImageOfzetaC[kkkkkk[i0i0i0]]/ImageOfzetaC[jjjjjj[i0i0i0]]) = %o\n", (ImageOfzetaC[kkkkkk[i0i0i0]]/ImageOfzetaC[jjjjjj[i0i0i0]]);
//fprintf LogFile, "((thetaC[i0i0i0] - thetaC[jjjjjj[i0i0i0]])/(thetaC[i0i0i0] - thetaC[kkkkkk[i0i0i0]])) = %o\n", ((thetaC[i0i0i0] - thetaC[jjjjjj[i0i0i0]])/(thetaC[i0i0i0] - thetaC[kkkkkk[i0i0i0]]));
//fprintf LogFile, "Abs(temp) = %o\n", Abs(temp);
//fprintf LogFile, "LogarithmicAlphaC[i0i0i0][1] = %o\n", LogarithmicAlphaC[i0i0i0][1];

H:=Max( [d*AbsoluteLogarithmicHeight(alphaALGEBRAIC[1]), Abs(Log(Abs(temp))), 0.16] );

for i in J do
temp:=ImageOfpiC[i][kk[i]][kkkkkk[i0i0i0]]/ImageOfpiC[i][kk[i]][jjjjjj[i0i0i0]];
LogarithmicAlphaC[i0i0i0][1+i]:=Log(Abs(temp));
H:=H*Max( [d*AbsoluteLogarithmicHeight(alphaALGEBRAIC[1+i]), Abs(Log(Abs(temp))), 0.16] );
end for;

for i:=1 to r do
temp:=ImageOfepsC[i][kkkkkk[i0i0i0]]/ImageOfepsC[i][jjjjjj[i0i0i0]];
LogarithmicAlphaC[i0i0i0][1+v+i]:=Log(Abs(temp));
H:=H*Max( [d*AbsoluteLogarithmicHeight(alphaALGEBRAIC[1+v+i]), Abs(Log(Abs(temp))), 0.16] );
end for;

c17[i0i0i0]:=Min([(1/kappa)*((Exp(1)*mm/2)^(kappa))*(30^(mm+3))*(mm^(3.5)), (2^(6*mm+20))])*(d^2)*(1+Log(d))*H;

//////////////////////////////
/*
Compute c18
*/
//////////////////////////////

c18[i0i0i0]:= Log(2*Log(2)*c16[i0i0i0]) + c17[i0i0i0];
end for; //end i0i0i0 loop
end if;

//////////////////////////////////////////////////////////////////////////////
/*
s=1,2 case
*/
//////////////////////////////////////////////////////////////////////////////

if s eq 1 or s eq 2 then

sFFF:=Signature(FFF); //sFFF = number of real embeddings of \CC
LogarithmicAlphaC:=[];

for i0i0i0:=1 to s do

////////////////////////
/*
Choose j,k and compute c16
*/
/////////////////////////
max:=0;
for i:=1 to t do
j:=s-1 + 2*i;
k:=j+1;
OneOverc16:=(Abs(thetaC[i0i0i0] - thetaC[j])/2)*(Abs(thetaC[k] - thetaC[i0i0i0])/Abs(thetaC[j] - thetaC[k]));
if OneOverc16 gt max then 
max:=OneOverc16; 
jjjjjj[i0i0i0]:=j;
kkkkkk[i0i0i0]:=k;
end if;
end for;
c16[i0i0i0]:=1/max;

///////////////////////
/*
Select an embedding (sigma in Section 13) of FFF into the complex numbers
by selecting a conjugate in \CC (phidot) of the generator of FFF (FFF.1).

Find the images of the roots of g in \CC under this embedding: rootsofginC

Embedding FFF into \CC will produce a smaller constant c17[i0i0i0].

Define kappa.
*/
///////////////////////
kappa:=1;
if sFFF eq 0 then kappa:=2; end if;
phidot:=Conjugates(FFF.1)[1];
rootsofginC:=[];
for i:=1 to n do
rootsofginC[i]:=0*phidot;
for ii:=1 to Degree(FFF) do
rootsofginC[i]:=rootsofginC[i]+rootsofginFFF[i][ii]*phidot^(ii-1);
end for;
end for;

////////////////////////
/*
Find preimages in FFF of theta^{(i_0)}, theta^{(j)}, theta^{(k)} under the embedding sigma of FFF into \CC.  We choose not to use MAGMA's bulit in preimage-finder to avoid round-off errors.

To find the preimage of theta^{(i_0)}, we actually find the index ii0 in {1,...,n} such that sigma(thetaF[ii0]) = thetaC[i0i0i0].
Similarly for theta^{(j)}, theta^{(k)}.

PreimageOfalphaj = preimage in FFF of \alpha^{(j)} under the embedding sigma of FFF into \CC

PreimageOfzetaj = preimage in FFF of \zeta^{(j)} under the embedding sigma of FFF into \CC

PreimageOfalphak = preimage in FFF of \alpha^{(k)} under the embedding sigma of FFF into \CC

PreimageOfzetak = preimage in FFF of \zeta^{(k)} under the embedding sigma of FFF into \CC

We also find the preimages of 
pi_{i}^{(j)}, pi_{i}^{(k)}, eps_{i}^{(j)}, eps_{i}^{(k)}
*/
//////////////////////////
//find preimage of \theta^{(i_0)}
min:=Abs(thetaC[i0i0i0] - rootsofginC[1]);
ii0:=1;
for i:=2 to n do
if Abs(thetaC[i0i0i0] - rootsofginC[i]) lt min then
min:=Abs(thetaC[i0i0i0] - rootsofginC[i]);
ii0:=i;
end if;
end for;

//find preimage of \theta^{(j)}
min:=Abs(thetaC[jjjjjj[i0i0i0]] - rootsofginC[1]);
ijjj:=1;
for i:=2 to n do
if Abs(thetaC[jjjjjj[i0i0i0]] - rootsofginC[i]) lt min then
min:=Abs(thetaC[jjjjjj[i0i0i0]] - rootsofginC[i]);
ijjj:=i;
end if;
end for;

//find preimage of \theta^{(k)}
min:=Abs(thetaC[kkkkkk[i0i0i0]] - rootsofginC[1]);
ikkk:=1;
for i:=2 to n do
if Abs(thetaC[kkkkkk[i0i0i0]] - rootsofginC[i]) lt min then
min:=Abs(thetaC[kkkkkk[i0i0i0]] - rootsofginC[i]);
ikkk:=i;
end if;
end for;

PreimageOfzetaj:=0;
for i:= 1 to n do
PreimageOfzetaj:=PreimageOfzetaj + zeta[i]*ImageOfIntegralBasisElementF[ijjj][i];
end for; //i
PreimageOfalphaj:=0;
for i:= 1 to n do
PreimageOfalphaj:=PreimageOfalphaj + alpha[i]*ImageOfIntegralBasisElementF[ijjj][i];
end for; //i
PreimageOfzetak:=0;
for i:= 1 to n do
PreimageOfzetak:=PreimageOfzetak + zeta[i]*ImageOfIntegralBasisElementF[ikkk][i];
end for; //i
PreimageOfalphak:=0;
for i:= 1 to n do
PreimageOfalphak:=PreimageOfalphak + alpha[i]*ImageOfIntegralBasisElementF[ikkk][i];
end for; //i

/*
Note that: 
preimage of pi_{i}^{(j)} = ImageOfpiF[i][kk[i]][ijjj]
preimage of pi_{i}^{(k)} = ImageOfpiF[i][kk[i]][ikkk]
preimage of eps_{i}^{(j)} = ImageOfepsF[i][ijjj]
preimage of eps_{i}^{(k)} = ImageOfepsF[i][ikkk]
*/

///////////////////////////////////////
/*
Define the alpha_i for i in J, construct L.
*/
//////////////////////////////////////
alphaALGEBRAIC:=[FFF|];
for i:=1 to 1 + v + r do
alphaALGEBRAIC[i]:=1; //initialize
end for;
alphaALGEBRAIC[1]:=(thetaF[ii0] - thetaF[ijjj] / thetaF[ii0] - thetaF[ikkk])*(PreimageOfalphak/PreimageOfalphaj)*(PreimageOfzetak/PreimageOfzetaj);
for i in J do
alphaALGEBRAIC[1+i]:=ImageOfpiF[i][kk[i]][ikkk]/ImageOfpiF[i][kk[i]][ijjj];
end for;
for i:=1 to r do
alphaALGEBRAIC[1+v+i]:=ImageOfepsF[i][ikkk]/ImageOfepsF[i][ijjj];
end for;

LL:=sub<FFF | alphaALGEBRAIC>;
d:=Degree(LL);
mm:=2+#J+r;


////////////////////////////////////
/* 
Compute c17.

Also compute the alpha_i as defined in Sections 18 and 20: LogarithmicAlphaC[i0i0i0][i]
*/
/////////////////////////////////////
LogarithmicAlphaC[i0i0i0]:=[RealField() | ];
for i:=1 to 1+v + r do
LogarithmicAlphaC[i0i0i0][i]:=0;
end for;


temp:=((thetaC[i0i0i0] - thetaC[jjjjjj[i0i0i0]])/(thetaC[i0i0i0] - thetaC[kkkkkk[i0i0i0]]))*(ImageOfzetaC[kkkkkk[i0i0i0]]/ImageOfzetaC[jjjjjj[i0i0i0]])*(ImageOfalphaC[kkkkkk[i0i0i0]]/ImageOfalphaC[jjjjjj[i0i0i0]]);
LogarithmicAlphaC[i0i0i0][1]:=Imaginary(Log(temp));
H:=Max( [d*AbsoluteLogarithmicHeight(alphaALGEBRAIC[1]), Abs(Log(temp)), 0.16] );

for i in J do
temp:=ImageOfpiC[i][kk[i]][kkkkkk[i0i0i0]]/ImageOfpiC[i][kk[i]][jjjjjj[i0i0i0]];
LogarithmicAlphaC[i0i0i0][1+i]:=Imaginary(Log(temp));
H:=H*Max( [d*AbsoluteLogarithmicHeight(alphaALGEBRAIC[1+i]), Abs(Log(temp)), 0.16] );
end for;

for i:=1 to r do
temp:=ImageOfepsC[i][kkkkkk[i0i0i0]]/ImageOfepsC[i][jjjjjj[i0i0i0]];
LogarithmicAlphaC[i0i0i0][1+v+i]:=Imaginary(Log(temp));
H:=H*Max( [d*AbsoluteLogarithmicHeight(alphaALGEBRAIC[1+v+i]), Abs(Log(temp)), 0.16] );
end for;

LogarithmicAlphaC[i0i0i0][2+v+r]:=PI; // = Im Log(-1)

H:=H*Max([d*0, PI, 0.16]); //AbsoluteLogarithmicHeight(-1) = 0

c17[i0i0i0]:=Min([(1/kappa)*((Exp(1)*mm/2)^(kappa))*(30^(mm+3))*(mm^(3.5)), (2^(6*mm+20))])*(d^2)*(1+Log(d))*H;


//////////////////////////////
/*
Compute c18
*/
//////////////////////////////

c18[i0i0i0]:= Log(4*Arcsin(1/4)*c16[i0i0i0]) + c17[i0i0i0] + c17[i0i0i0]*Log(#JJJ);


end for; //end i0i0i0 loop
end if;

/////////////////////////////////////////////////////////////////////////////
/*
Done computing the indices j=j(i0), k=k(i0), and the numbers c16=c16(i0), c17=c17(i0), c18=c18(i0) for every i0 in {1,...,s} (when s > 0)
*/
/////////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////
///////////////////
/*
Choose c11 to minimize the value of c22, the upper bound for H.  In the process, compute the constants that depend on c11: 
c11, c12, c13, c14, c15, c19, c20, c21, c22
*/
//////////////////
////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////

if s gt 0 then

c11:=(1/1000000)*c10/(n-1);

c12prime:=(c8prime + c5*c9prime)/(c10 - (n-1)*c11);
c13prime:=c4*c9prime/(c10 - (n-1)*c11);
if c13prime lt Exp(2) then c13prime:=Exp(2); end if;
c12primeprime:=(c8primeprime + c5*c9primeprime)/(c10 - c11);
c13primeprime:=c4*c9primeprime/(c10 - c11);
if c13primeprime lt Exp(2) then c13primeprime:=Exp(2); end if;

c14:=2*Ceiling(c12prime + c13prime*Log(c13prime))-1;
if c14 lt 2*Ceiling(c12primeprime + c13primeprime*Log(c13primeprime))-1 then
c14:=2*Ceiling(c12primeprime + c13primeprime*Log(c13primeprime))-1;
end if;
if c14 lt 2 then c14:=2; end if;

/*
In the thesis, the roots of g in C are ordered so that 
thetaC[s+i] = overline(thetaC[s+t+i]) (i=1,...,t)
Magma (and hence this program) orders the roots so that 
thetaC[s+2i-1] = overline(thetaC[s+2i]) (i=1,...,t).
*/

c15:=0;
if t gt 0 then
min:=Abs(Imaginary(thetaC[s+1]));
for ii:=2 to t do
j:=s + 2*ii - 1;
if Abs(Imaginary(thetaC[j])) lt min then min:=Abs(Imaginary(thetaC[j])); end if;
end for; //end ii
if Floor(-Log(min)/c11) gt 0 then c15:=Floor(-Log(min)/c11); end if;
end if;

c19:=Ceiling(Log(2*c16[1])/c11)-1;
max1:=c17[1]/c11;
if max1 lt Exp(2) then max1:=Exp(2); end if;
c20:=2*( (c18[1]/c11) + max1*Log(max1) );
for i0i0i0:=2 to s do
c19:=Ceiling(Log(2*c16[i0i0i0])/c11)-1;
max1:=c17[i0i0i0]/c11;
if max1 lt Exp(2) then max1:=Exp(2); end if;
c20:=2*( (c18[i0i0i0]/c11) + max1*Log(max1) );
end for;
c20:=Ceiling(c20)-1;

c21:=Max([c15,c19,c20,1]);

c22:=Max([c7,c14,c21]);

////

c11:=((1000000 - 1)/1000000)*c10/(n-1);

c12prime:=(c8prime + c5*c9prime)/(c10 - (n-1)*c11);
c13prime:=c4*c9prime/(c10 - (n-1)*c11);
if c13prime lt Exp(2) then c13prime:=Exp(2); end if;
c12primeprime:=(c8primeprime + c5*c9primeprime)/(c10 - c11);
c13primeprime:=c4*c9primeprime/(c10 - c11);
if c13primeprime lt Exp(2) then c13primeprime:=Exp(2); end if;

c14:=2*Ceiling(c12prime + c13prime*Log(c13prime))-1;
if c14 lt 2*Ceiling(c12primeprime + c13primeprime*Log(c13primeprime))-1 then
c14:=2*Ceiling(c12primeprime + c13primeprime*Log(c13primeprime))-1;
end if;
if c14 lt 2 then c14:=2; end if;

c15:=0;
if t gt 0 then
min:=Abs(Imaginary(thetaC[s+1]));
for ii:=2 to t do
j:=s-1 + 2*ii;
if Abs(Imaginary(thetaC[j])) lt min then min:=Abs(Imaginary(thetaC[j])); end if;
end for; //end ii
if Floor(-Log(min)/c11) gt 0 then c15:=Floor(-Log(min)/c11); end if;
end if;

c19:=Ceiling(Log(2*c16[1])/c11)-1;
max1:=c17[1]/c11;
if max1 lt Exp(2) then max1:=Exp(2); end if;
c20:=2*( (c18[1]/c11) + max1*Log(max1) );
for i0i0i0:=2 to s do
c19:=Ceiling(Log(2*c16[i0i0i0])/c11)-1;
max1:=c17[i0i0i0]/c11;
if max1 lt Exp(2) then max1:=Exp(2); end if;
c20:=2*( (c18[i0i0i0]/c11) + max1*Log(max1) );
end for;
c20:=Ceiling(c20)-1;

c21:=Max([c15,c19,c20,1]);

if Max([c7,c14,c21]) lt c22 then c22:=Max([c7,c14,c21]); end if;

////

for i:=1 to 999 do

c11:=(i/1000)*c10/(n-1);

c12prime:=(c8prime + c5*c9prime)/(c10 - (n-1)*c11);
c13prime:=c4*c9prime/(c10 - (n-1)*c11);
if c13prime lt Exp(2) then c13prime:=Exp(2); end if;
c12primeprime:=(c8primeprime + c5*c9primeprime)/(c10 - c11);
c13primeprime:=c4*c9primeprime/(c10 - c11);
if c13primeprime lt Exp(2) then c13primeprime:=Exp(2); end if;

c14:=2*Ceiling(c12prime + c13prime*Log(c13prime))-1;
if c14 lt 2*Ceiling(c12primeprime + c13primeprime*Log(c13primeprime))-1 then
c14:=2*Ceiling(c12primeprime + c13primeprime*Log(c13primeprime))-1;
end if;
if c14 lt 2 then c14:=2; end if;

c15:=0;
if t gt 0 then
min:=Abs(Imaginary(thetaC[s+1]));
for ii:=2 to t do
j:=s-1 + 2*ii;
if Abs(Imaginary(thetaC[j])) lt min then min:=Abs(Imaginary(thetaC[j])); end if;
end for; //end ii
if Floor(-Log(min)/c11) gt 0 then c15:=Floor(-Log(min)/c11); end if;
end if;

c19:=Ceiling(Log(2*c16[1])/c11)-1;
max1:=c17[1]/c11;
if max1 lt Exp(2) then max1:=Exp(2); end if;
c20:=2*( (c18[1]/c11) + max1*Log(max1) );
for i0i0i0:=2 to s do
c19:=Ceiling(Log(2*c16[i0i0i0])/c11)-1;
max1:=c17[i0i0i0]/c11;
if max1 lt Exp(2) then max1:=Exp(2); end if;
c20:=2*( (c18[i0i0i0]/c11) + max1*Log(max1) );
end for;
c20:=Ceiling(c20)-1;

c21:=Max([c15,c19,c20,1]);

if Max([c7,c14,c21]) lt c22 then c22:=Max([c7,c14,c21]); end if;


end for; //end i



////////////////////////////////////////////////////////////////
else //s = 0
///////////////////////////////////////////////////////////////

c11:=(1/1000000)*c10/(n-1);

c12prime:=(c8prime + c5*c9prime)/(c10 - (n-1)*c11);
c13prime:=c4*c9prime/(c10 - (n-1)*c11);
if c13prime lt Exp(2) then c13prime:=Exp(2); end if;
c12primeprime:=(c8primeprime + c5*c9primeprime)/(c10 - c11);
c13primeprime:=c4*c9primeprime/(c10 - c11);
if c13primeprime lt Exp(2) then c13primeprime:=Exp(2); end if;

c14:=2*Ceiling(c12prime + c13prime*Log(c13prime))-1;
if c14 lt 2*Ceiling(c12primeprime + c13primeprime*Log(c13primeprime))-1 then
c14:=2*Ceiling(c12primeprime + c13primeprime*Log(c13primeprime))-1;
end if;
if c14 lt 2 then c14:=2; end if;

c15:=0;
if t gt 0 then
min:=Abs(Imaginary(thetaC[s+1]));
for ii:=2 to t do
j:=s-1 + 2*ii;
if Abs(Imaginary(thetaC[j])) lt min then min:=Abs(Imaginary(thetaC[j])); end if;
end for; //end ii
if Floor(-Log(min)/c11) gt 0 then c15:=Floor(-Log(min)/c11); end if;
end if;


c22:=Max([c7,c14,c15]);

////

c11:=((1000000 - 1)/1000000)*c10/(n-1);

c12prime:=(c8prime + c5*c9prime)/(c10 - (n-1)*c11);
c13prime:=c4*c9prime/(c10 - (n-1)*c11);
if c13prime lt Exp(2) then c13prime:=Exp(2); end if;
c12primeprime:=(c8primeprime + c5*c9primeprime)/(c10 - c11);
c13primeprime:=c4*c9primeprime/(c10 - c11);
if c13primeprime lt Exp(2) then c13primeprime:=Exp(2); end if;

c14:=2*Ceiling(c12prime + c13prime*Log(c13prime))-1;
if c14 lt 2*Ceiling(c12primeprime + c13primeprime*Log(c13primeprime))-1 then
c14:=2*Ceiling(c12primeprime + c13primeprime*Log(c13primeprime))-1;
end if;
if c14 lt 2 then c14:=2; end if;

c15:=0;
if t gt 0 then
min:=Abs(Imaginary(thetaC[s+1]));
for ii:=2 to t do
j:=s-1 + 2*ii;
if Abs(Imaginary(thetaC[j])) lt min then min:=Abs(Imaginary(thetaC[j])); end if;
end for; //end ii
if Floor(-Log(min)/c11) gt 0 then c15:=Floor(-Log(min)/c11); end if;
end if;


if Max([c7,c14,c15]) lt c22 then c22:=Max([c7,c14,c15]); end if;

////

for i:=1 to 999 do

c11:=(i/1000)*c10/(n-1);

c12prime:=(c8prime + c5*c9prime)/(c10 - (n-1)*c11);
c13prime:=c4*c9prime/(c10 - (n-1)*c11);
if c13prime lt Exp(2) then c13prime:=Exp(2); end if;
c12primeprime:=(c8primeprime + c5*c9primeprime)/(c10 - c11);
c13primeprime:=c4*c9primeprime/(c10 - c11);
if c13primeprime lt Exp(2) then c13primeprime:=Exp(2); end if;

c14:=2*Ceiling(c12prime + c13prime*Log(c13prime))-1;
if c14 lt 2*Ceiling(c12primeprime + c13primeprime*Log(c13primeprime))-1 then
c14:=2*Ceiling(c12primeprime + c13primeprime*Log(c13primeprime))-1;
end if;
if c14 lt 2 then c14:=2; end if;

c15:=0;
if t gt 0 then
min:=Abs(Imaginary(thetaC[s+1]));
for ii:=2 to t do
j:=s-1 + 2*ii;
if Abs(Imaginary(thetaC[j])) lt min then min:=Abs(Imaginary(thetaC[j])); end if;
end for; //end ii
if Floor(-Log(min)/c11) gt 0 then c15:=Floor(-Log(min)/c11); end if;
end if;

if Max([c7,c14,c15]) lt c22 then c22:=Max([c7,c14,c15]); end if;

end for; //end i

end if;

/////////////////////////////////////////////////////////////////////////////
/*
UpperBoundForH:= current best upper bound for H = H_0 from Section 15.

UpperBoundForA:= current best upper bound for A = A_0 from Section 15.

ConditionalUpperBoundForA[i0]:= current best i_0-conditonal upper bound for A 
= A_0(i_0) from Section 19.

UpperBoundForn[l]:= current best upper bound for n_l = N_l from Section 15.

UpperBoundForN:= current best upper bound for N

For l in I2, N_{l}^{*} bounds n_l.
For l in I, we use Corollary 14.2.

B[i]:= current best upper bound for |b_i| = B_i from section 15.
*/
/////////////////////////////////////////////////////////////////////////////
UpperBoundForn:=[];
ConditionalUpperBoundForA:=[];
UpperBoundForH:=c22;
UpperBoundForA:=UpperBoundForH;
for i0:=1 to s do
ConditionalUpperBoundForA[i0]:=UpperBoundForA;
end for;
for l:=1 to v do
UpperBoundForn[l]:=1; //initialize
end for;
for l in I2 do
UpperBoundForn[l]:=Nstar[l];
end for;
for l in I do
UpperBoundForn[l]:=Ceiling( (c1[l]/hh[l])*Log(c22) - (1/hh[l])*Valuation(delta2[l]) ) - 1;
if 2 gt UpperBoundForn[l] then UpperBoundForn[l]:=2; end if;
if c22 lt UpperBoundForn[l] then UpperBoundForn[l]:=c22; end if;
end for;

UpperBoundForN:=Max(UpperBoundForn);

B:=[];
for i:=1 to 1+v+r do
B[i]:=0; //initialize
end for;
B[1]:=1;
for i in J do
B[1+i]:=UpperBoundForn[i];
end for;
for i:=1 to r do
B[1+v+i]:=UpperBoundForA;
end for;

//print("B");
//B;


/////////////////////////////////////////////
/*
If UpperBoundForA < 0, then we know there are 
no solutions for the current case of (11).

If UpperBoundForn[i] < 0 for some i in J, then 
we know there are no solutions for the current 
case of (11).
*/
/////////////////////////////////////////////
if UpperBoundForA lt 0 then
PrintFile(LogFile, "No solutions in the current case.");
fprintf LogFile, "UpperBoundForA = %o\n", UpperBoundForA;
continue iiii;
end if;
for l in J do 
if UpperBoundForn[l] lt 0 then
PrintFile(LogFile, "No solutions in the current case.");
fprintf LogFile, "p[l] = %o\n", p[l];
fprintf LogFile, "UpperBoundForn[l] = %o\n", UpperBoundForn[l];
continue iiii;
end if;
end for;

if FindAll then
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////
//////////////////////
/*
Start Of Loop For Repeated Basic Reductions
*/
///////////////////////
///////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//fprintf LogFile, "I = %o\n", I;
PrintFile(LogFile, "Starting basic reduction procedures.");
fprintf LogFile, "UpperBoundForn = %o\n", UpperBoundForn;
fprintf LogFile, "UpperBoundForA = %o\n", UpperBoundForA;


ExceptionalTuples:=[];
Improvement:=true;

while Improvement do
Improvement:=false;
ExceptionalTuplesInsideLoop:=[];

/////////////////////////////////////////////////////////////////////
/*
If the number of tuples to sieve through is small enough, jump directly to the 
final sieving procedure.
*/
//////////////////////////////////////////////////////////////////////////////
prod:=1;
for i in J do
prod:=prod*(UpperBoundForn[i]+1);
end for;
prod:=prod*(2*UpperBoundForA + 1)^r;
if prod lt 1000000 then 
break; 
end if; //prod = number of tuples to sieve


///////////////////////////////////////////////////////////////////////////////
/*
Basic p_l-adic reduction for each l in I (Section 18)
*/
///////////////////////////////////////////////////////////////////////////////


for l in I do
//RGB
//print("basic p_l, l=");
//l;

//////////////////////////////////////////////////////////////////////////////
/*
Define:
W[i] = W_i (weights) for p_l (Section 18)
QQ = Q (Section 18)
mmmm = m for p_l (Section 18)

Initialize:
betam[i] = beta_i^(m) for p[L],
Tm, where Transpose(Tm) = U_m from Section 18
*/
//////////////////////////////////////////////////////////////////////////////
W:=[];
for i:=1 to 1+v+r do
W[i]:=0; //initialize
end for;

W[1]:=0;
for i:=2 to #JJJ do
W[JJJ[i]]:=RoundP(UpperBoundForH/  RNTO(B[JJJ[i]])  );
end for;

QQ:=0;
for i in JJJ do
QQ:=QQ+(W[i]^2)*(B[i]^2); //recall W[1]=0
end for;
if QQ eq 0 then QQ:=1; end if;

prod:=1;
for i:=2 to #JJJ do
prod:=prod*W[JJJ[i]];
end for;

/*
mmmm0:=Ceiling(
( (#JJJ - 1)/(2*Log(p[l])) )*Log( 2^(#JJJ - 1) * QQ / prod^(2/(#JJJ - 1)) )  
);
*/
mmmm0:=Ceiling(
( (#JJJ - 1)/(2*Log(p[l])) )*Log( QQ / prod^(2/(#JJJ - 1)) )  
);
if mmmm0 le 0 then mmmm0:=1; end if;

betam:=[];
for i:=1 to 1+v+r do
betam[i]:=0;
end for;

Tm:=ScalarMatrix(IntegerRing(),#JJJ-1,1);
/*initialize as #JJJ-1 by #JJJ-1 identity matrix*/

///////////////////////////////////////////////////////////////////////////
/* 
Start while loop that will increase m until the p_l-adic reduction yeilds a new upper bound for n_l or until a number of increases has been made with no success
*/
///////////////////////////////////////////////////////////////////////////
flag:=true;
RunThroughNumber:=0;
while flag do 

/////////////////////////////////////////////////////////////////////////////
/*
Increase mmmm = m (if this is not the first attempt with the basic p_l-reduction procedure).
Calculuate betam[i] = beta_i^(m).
*/
//////////////////////////////////////////////////////////////////////////
mmmm:=Ceiling( mmmm0 + RunThroughNumber*(5/100)*mmmm0 );

if mmmm gt (0.95)*padicprecision[l] then
PadicPrecisionMultiplier[l] := PadicPrecisionMultiplier[l] + 1;
continue PrecisionLoopVariable;
end if;

for i in JJJ do
//fprintf LogFile, "AbsolutePrecision(beta[l][i]) = %o\n", AbsolutePrecision(beta[l][i]);
betam[i]:= SmallestNonnegativeRemainderModpLToThem(beta[l][i],p[l],mmmm,padicprecision[l]);
end for;

//////////////////////////////////////////////////////////////////////////////
/*
Define:
Am = A_m for p[L]
Gamma_m = lattice generated by columns of A_m
*/
//////////////////////////////////////////////////////////////////////////////
Am:=ZeroMatrix(IntegerRing(), v+r+2, v+r+2);
for i:=1 to v+r+1 do
Am[i][i]:=W[i];
end for;
for j:=1 to v+r+1 do
Am[v+r+2][j]:=W[ihat[l]]*betam[j];
end for;
Am[v+r+2][v+r+2]:=W[ihat[l]]*p[l]^mmmm;

for i:=1+v+r to 2 by -1 do
if i eq ihat[l] or not i in JJJ then
RemoveColumn(~Am,i);
RemoveRow(~Am,i);
end if;
end for;

RemoveColumn(~Am,1);
RemoveRow(~Am,1);

//Am is now a #JJJ-1 by #JJJ-1 matrix

Am:=Am*Transpose(Tm); //Transpose(Tm) = Um from Setion 15
/* 
If this is the first run through, Tm is the identity. If this is not 
the first run through, this will save computation time.
*/

//////////////////////////////////////////////////////////////////////////////
/*
Compute an LLL reduced basis for the lattice Gamma_m generated by columns of A_m.  The algorithm used is de Weger's exact integer version of LLL.

Note: LLL(X) assumes ROWS of X span the lattice, so we need to feed it the transpose of A_m.  Similarly, it spits out the transpose of B_m and the transpose of U_m
*/
//////////////////////////////////////////////////////////////////////////////

temp,Tm,rank:=LLL( Transpose(Am) : Proof:=true, Method:="Integral", Delta:=0.75, Eta:=0.5 );

Bm:=MatrixRing(RationalField(),#JJJ-1) ! Transpose(temp); 
//columns are LLL-reduced basis for Gamma_m

/*
Here Tm*Transpose(Am) = Transpose(Bm). 
So with Um=Transpose(Tm) we have Am*Um = Bm,
and With 
Vm = Bm*Transpose(Tm)*Bm^(-1) = Am*Transpose(Tm)*Am^(-1), we have Vm*Am = Bm.
*/

///////////////////////////////////////////////////////////////////////////////
/*
Compute the lower bound for l(Gamma_m,y) using Lemma 16.1.  If it is large enough (bigger than sqrt(Q)), compute the new upper bound for n[L].  Otherwise, increase m and reduce again (go back to the start of the while loop).
*/
///////////////////////////////////////////////////////////////////////////////
lowerbound:=0;


//START IF
if betam[1] eq 0 then //y = 0 case (vectors)

//c1 = Transpose(Bm)[1]
lowerbound:= 2^(-(#JJJ-2)/2)*Norm(Transpose(Bm)[1])^(1/2);

else   //y neq 0 case

yyy:=ZeroMatrix(RationalField(),#JJJ-1,1);
yyy[#JJJ-1][1]:= -W[ihat[l]]*betam[1];
sss:=(Bm^(-1))*yyy;

/*
//RGBRGB
YYY:=RSpace(RationalField(),#JJJ-1) ! [0,-W[ihat[l]]*betam[1]];
TEMP1, TEMP2:=ClosestVectors(Lattice(Transpose(Bm)), YYY);
print("distance between y and closest lattice vector");
RealField() ! (TEMP2)^(1/2);
*/

IndicesjWithsjNotIntegral:=[];
for j:=1 to #JJJ-1 do
if not IsIntegral(sss[j][1]) then
Append(~IndicesjWithsjNotIntegral,j);
end if;
end for;

delta:=[RealField() | ];
for j:=1 to #JJJ-2 do
delta[j]:=0;
for i:=j+1 to #JJJ-1 do
if delta[j] lt DistanceToNearestInteger(sss[i][1])*Norm(Transpose(Bm)[i])^(1/2) then
delta[j]:=DistanceToNearestInteger(sss[i][1])*Norm(Transpose(Bm)[i])^(1/2);
end if;
end for;
end for;
delta[#JJJ-1]:=0;

/*
//RGBRGB
for i:=1 to #JJJ-1 do 
print("DistanceToNearestInteger(sss[i][1])");
print("i=");
i;
RealField() ! DistanceToNearestInteger(sss[i][1]);
end for;
*/

max:=0;
for j in IndicesjWithsjNotIntegral do
if max lt 2^(-(#JJJ-2)/2) * DistanceToNearestInteger(sss[j][1]) * Norm(Transpose(Bm)[1])^(1/2) - (#JJJ - 1 - j)*delta[j] then
max:=2^(-(#JJJ-2)/2) * DistanceToNearestInteger(sss[j][1]) * Norm(Transpose(Bm)[1])^(1/2) - (#JJJ - 1 - j)*delta[j];
end if;
end for;
lowerbound:=max;

end if;
//END IF

/*
//RGBRGB
print("lowerbound");
Round(lowerbound);
print("QQ^(1/2)");
Round(QQ^(1/2));
continue iiii;
*/

if lowerbound gt QQ^(1/2) then

flag:=false; //ready to get out of while loop that increases m if necessary

OldUpperBoundFornl:=UpperBoundForn[l];

NewUpperBoundFornl:= Max([
Floor( (1/hh[l])*(1/(p[l] - 1) - Valuation(delta2[l])) ),
Ceiling((1/hh[l])*(mmmm-dd[l]))-1,
0
]);

if NewUpperBoundFornl lt OldUpperBoundFornl then
Improvement:=true;
UpperBoundForn[l]:=NewUpperBoundFornl;
B[1+l]:=UpperBoundForn[l];
end if;


else
 
RunThroughNumber+:=1;  //increase m and try again
///
/*
If increasing m 20 times (in which case m will be double its original value) fails to 
produce a new upper bound for n_l, move onto the next value of l in I.  Also, print a 
message indicating that the basic p_l-adic reduction procedure was unsuccesful.
*/
/////
if RunThroughNumber eq 20 then 
PrintFile(LogFile, "Basic p-adic reduction taking a long time.");
fprintf LogFile, "Case: iiii = %o\n", iiii;
fprintf LogFile, "l = %o\n", l;
fprintf LogFile, "UpperBoundForn[l] = %o\n", UpperBoundForn[l];
continue l;
end if;

end if; /* IF controlled by lowerbound gt QQ^(1/2) */

end while; /*this is the loop that increases m if necessary, the while loop controlled by flag*/

if UpperBoundForn[l] lt 0 then
//there are no solutions of the current case of (11)
fprintf LogFile, "UpperBoundForn[l] lt 0. No solutions possible in case iiii = %o\n", iiii;
continue iiii;
end if;
end for; // end l loop

UpperBoundForN:=Max(UpperBoundForn);

/*
print("Starting basic real reduction");
print("Log_10 of Upper Bound For A");
Log(UpperBoundForA)/Log(10);
*/


//////////////////////////////////////////////////////////////////////////////
/*
Basic Real Reduction (Section 19)
*/
/////////////////////////////////////////////////////////////////////////////
for i0:=1 to s do
ConditionalUpperBoundForA[i0]:=UpperBoundForA;
end for;

//////////////////////////////////////////////////////////////////////////////
/*
Totally Complex Case, i.e, s=0
*/
//////////////////////////////////////////////////////////////////////////
if s eq 0 then

//Choose c11 to find an choose optimal upper bound for A from Lemma 19.1
MIN:=UpperBoundForA;

c11:=(1/1000000)*c10/(n-1);

c15:=0;
min:=Abs(Imaginary(thetaC[s+1]));
for ii:=2 to t do
j:=s-1 + 2*ii;
if Abs(Imaginary(thetaC[j])) lt min then min:=Abs(Imaginary(thetaC[j])); end if;
end for; //end ii
if Floor(-Log(min)/c11) gt 0 then c15:=Floor(-Log(min)/c11); end if;

max:=Ceiling((c8prime + c9prime*UpperBoundForN)/(c10-(n-1)*c11))-1;
if max lt Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1 then
max:=Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1;
end if;
if max lt c15 then max:=c15; end if; 
//now max is the upper bound for A in Lemma 19.1 with a certain value of c11
if max lt MIN then MIN:=max; end if;

c11:=((1000000 - 1)/1000000)*c10/(n-1);

c15:=0;
min:=Abs(Imaginary(thetaC[s+1]));
for ii:=2 to t do
j:=s-1 + 2*ii;
if Abs(Imaginary(thetaC[j])) lt min then min:=Abs(Imaginary(thetaC[j])); end if;
end for; //end ii
if Floor(-Log(min)/c11) gt 0 then c15:=Floor(-Log(min)/c11); end if;

max:=Ceiling((c8prime + c9prime*UpperBoundForN)/(c10-(n-1)*c11))-1;
if max lt Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1 then
max:=Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1;
end if;
if max lt c15 then max:=c15; end if;
//now max is the upper bound for A in Lemma 19.1 with a certain value of c11 
if max lt MIN then MIN:=max; end if;

for i:=1 to 999 do
c11:=(i/1000)*c10/(n-1);

c15:=0;
min:=Abs(Imaginary(thetaC[s+1]));
for ii:=2 to t do
j:=s-1 + 2*ii;
if Abs(Imaginary(thetaC[j])) lt min then min:=Abs(Imaginary(thetaC[j])); end if;
end for; //end ii
if Floor(-Log(min)/c11) gt 0 then c15:=Floor(-Log(min)/c11); end if;

max:=Ceiling((c8prime + c9prime*UpperBoundForN)/(c10-(n-1)*c11))-1;
if max lt Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1 then
max:=Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1;
end if;
if max lt c15 then max:=c15; end if;
//now max is the upper bound for A in Lemma 19.1 with a certain value of c11
if max lt MIN then MIN:=max; end if;
end for;  //end i loop


OldUpperBoundForA:=UpperBoundForA;
NewUpperBoundForA:=MIN;


if NewUpperBoundForA lt OldUpperBoundForA then
Improvement:=true;
UpperBoundForA:=NewUpperBoundForA;
end if;

else //s > 0
//////////////////////////////////////////////////////////////////////////////
/*
s>0 Case 
*/
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
/*
Real Case, i.e., s \geq 3
*/
//////////////////////////////////////////////////////////////////////////////

if s ge 3 then // s>=3 real case

JumpToEndOfRealReduction:=false;
for i0:=1 to s do 


////////////////////////////////////////////////////////////////////////////
/*
Define 
weights W[i] (Section 19)
R (Section 19)
S (Section 19)
CCCCCC = C (Section 19)

Initialize:
TC, where Transpose(TC) = U_C from Section 19
phi[i]:= phi_i from Section 19
*/
////////////////////////////////////////////////////////////////////////////
W:=[];
for i:=1 to 1+v+r do
W[i]:=0; //initialize
end for;

H0prime:=0;
for i:=2 to #JJJ-1 do
if H0prime lt B[JJJ[i]] then H0prime:=B[JJJ[i]]; end if;
end for;

W[1]:=0;
for i:=2 to #JJJ-1 do
W[JJJ[i]]:=RoundP(H0prime/ RNTO(B[JJJ[i]]) );
end for;

R:=0;
for i in JJJ do 
R:=R + B[i];
end for;
R:=(1/2)*R;
//this is just an approximation to R

S:=0;
for i:=2 to #JJJ-1 do
S:=S+(W[JJJ[i]]^2)*(B[JJJ[i]]^2);
end for;

prod:=1;
for i:=2 to #JJJ-1 do
prod:=prod*W[JJJ[i]];
end for;

/*
LogC:= ((#JJJ-1)/2)*Log( 
(R^2 + S) / ( 2^(-(#JJJ-1)) * (Abs(LogarithmicAlphaC[i0][JJJ[#JJJ]])*prod)^(2/(#JJJ-1)) )
);
*/

LogC:= ((#JJJ-1)/2)*Log(  
(R^2 + S) / ( 2^(-2*(#JJJ-1)) * (Abs(LogarithmicAlphaC[i0][JJJ[#JJJ]])*prod)^(2/(#JJJ-1)) )
);

TC:=ScalarMatrix(IntegerRing(),#JJJ-1,1); //#JJJ-1 by #JJJ-1 identity matrix

phi:=[];
for i:=1 to 1+v+r do
phi[i]:=0;
end for;

/////////////////////////////////////////////////////////////////////////////
/*
Start the while loop where C will be increased until a new conditional upper for A is found that improves on the uncondtional upper bound for A or until a number of increases of C have been made with no success.
*/
////////////////////////////////////////////////////////////////////////////
RunThroughNumber1:=0;
RunThroughNumber2:=0;
flag:=true;
while flag do

//////////////////////////////////////////////////////////////////////////////
/*
Increase CCCCCC = C (if this is not the first attempt the basic real reduction procedure).

Calculate the phi_i for i in JJJ.

Calculate R.
*/
////////////////////////////////////////////////////////////////////////////
CCCCCC:=Ceiling(Exp(LogC + RunThroughNumber1*(5/100)*LogC + RunThroughNumber2*(-25/100)*LogC));

if RunThroughNumber1 eq 21 and UpperBoundForA gt 100000 then 
CCCCCC:=Ceiling(Exp(LogC + 9*LogC));
end if;
if RunThroughNumber1 eq 22 and UpperBoundForA gt 100000 then 
CCCCCC:=Ceiling(Exp(LogC + 9*LogC));
end if;
/*
if RunThroughNumber1 eq 23 and UpperBoundForA gt 100000 then 
CCCCCC:=Ceiling(Exp(LogC + 9*LogC));
end if;
if RunThroughNumber1 eq 24 and UpperBoundForA gt 100000 then 
CCCCCC:=Ceiling(Exp(LogC + 9*LogC));
end if;
*/

if LogC/Log(10) gt (0.95)*realprecision then
RealPrecisionMultiplier := RealPrecisionMultiplier + 1;
/*
print("LogC/Log(10)");
LogC/Log(10);
print("realprecision");
realprecision;
*/
continue PrecisionLoopVariable;
end if;

for i in JJJ do
phi[i]:=Round(CCCCCC*LogarithmicAlphaC[i0][i]);
//fprintf LogFile, "LogarithmicAlphaC[i0][i] = %o\n", LogarithmicAlphaC[i0][i];
//fprintf LogFile, "CCCCCC*LogarithmicAlphaC[i0][i] = %o\n", CCCCCC*LogarithmicAlphaC[i0][i];
//fprintf LogFile, "phi[i] = %o\n", phi[i];
end for;

//fprintf LogFile, "Log(CCCCCC)/Log(10) = %o\n", Log(CCCCCC)/Log(10);

/*
if Abs(phi[JJJ[#JJJ]]) lt 2 then
if CCCCCC*LogarithmicAlphaC[i0][JJJ[#JJJ]] ge 0 then 
phi[JJJ[#JJJ]]:=2;
else
phi[JJJ[#JJJ]]:=-2;
end if;
end if;

if IsIntegral(phi[1]/phi[JJJ[#JJJ]]) then
if Abs(phi[1]+1 - CCCCCC*LogarithmicAlphaC[i0][1]) le 1 then
phi[1]:=phi[1]+1;
else
phi[1]:=phi[1]-1;
end if;
end if;
*/

if phi[JJJ[#JJJ]] eq 0 then
if CCCCCC*LogarithmicAlphaC[i0][JJJ[#JJJ]] ge 0 then 
phi[JJJ[#JJJ]]:=1;
else
phi[JJJ[#JJJ]]:=-1;
end if;
end if;

if IsIntegral(phi[1]/phi[JJJ[#JJJ]]) then
bbb:=[1];
for i:=2 to #JJJ-1 do bbb[i]:=0; end for;
bbb[#JJJ]:=-phi[1]/phi[JJJ[#JJJ]];
Include(~ExceptionalTuplesInsideLoop,bbb);
end if;

R:=0;
for i in JJJ do 
R:=R + B[i]*Abs( CCCCCC*LogarithmicAlphaC[i0][i] -  phi[i] );
end for;

///////////////////////////////////////////////////////////////////////////////
/*
Compute:
AC = A_C
*/
//////////////////////////////////////////////////////////////////////////////
AC:=ZeroMatrix(IntegerRing(),v+r+1,v+r+1);

for i:=1 to v+r do
AC[i][i]:=W[i];
end for;
for j:=1 to v+r+1 do
AC[v+r+1][j]:=phi[j];
end for;

for i:=1+v+r to 2 by -1 do
if not i in JJJ then
RemoveColumn(~AC,i);
RemoveRow(~AC,i);
end if;
end for;

RemoveRow(~AC,1);
RemoveColumn(~AC,1);

//AC is now a #JJJ-1 by #JJJ-1 matrix

AC:=AC*Transpose(TC);
/* If this is the first run through Transpose(TC) is the identity. Otherwise Transpose(TC) is UC.  This will time in the LLL reduction. */

///////////////////////////////////////////////////////////////////////////////
/*
Compute LLL reduced basis for the lattice Gamma_C generated by columns of A_C.  The algoritm used is de Weger's exact integer version of LLL.

Note: LLL(X) assumes ROWS of X span the lattice, so we need to feed it the transpose of A_C.  Similarly, it spits out the transpose of B_C and the transpose of U_C
*/
///////////////////////////////////////////////////////////////////////////////

temp,TC,rank:=LLL(Transpose(AC) : Proof:=true, Method:="Integral", Delta:=0.75, Eta:=0.5 );

BC:=MatrixRing(RationalField(),#JJJ-1) ! Transpose(temp); 
//columns are LLL-reduced basis for Gamma_C

/*
Here TC*Transpose(AC) = Transpose(BC). 
So with UC=Transpose(TC) we have AC*UC = BC,
and With 
VC = BC*Transpose(TC)*BC^(-1) = AC*Transpose(TC)*AC^(-1), we have VC*AC = BC.
*/

///////////////////////////////////////////////////////////////////////////////
/*
Compute the lower bound for l(Gamma_C,y).  If it is large enough (bigger than sqrt(R^2 + S)), compute the new upper bound for n[L].  Otherwise, increase C and reduce again (go back to the start of the while loop)
*/
///////////////////////////////////////////////////////////////////////////////
lowerbound:=0;

//START IF
if phi[1] eq 0 then //y = 0 case (vectors) //never happens by choice of phi[1]

// \vec{c}_1 = Transpose(BC)[1]
lowerbound:= 2^(-(#JJJ-2)/2)*Norm( Transpose(BC)[1] )^(1/2);
else    //y neq 0 case

yyy:=ZeroMatrix(RationalField(),#JJJ-1,1);
yyy[#JJJ-1][1]:=-phi[1];
sss:=(BC^(-1))*yyy;

IndicesjWithsjNotIntegral:=[];
for j:=1 to #JJJ-1 do
if not IsIntegral(sss[j][1]) then
Append(~IndicesjWithsjNotIntegral,j);
end if;
end for;

delta:=[RealField() | ];
for j:=1 to #JJJ-2 do
delta[j]:=0;
for i:=j+1 to #JJJ-1 do
if delta[j] lt DistanceToNearestInteger(sss[i][1])*Norm(Transpose(BC)[i])^(1/2) then
delta[j]:=DistanceToNearestInteger(sss[i][1])*Norm(Transpose(BC)[i])^(1/2);
end if;
end for;
end for;
delta[#JJJ-1]:=0;

max:=0;
for j in IndicesjWithsjNotIntegral do
if max lt 2^(-(#JJJ-2)/2) * DistanceToNearestInteger(sss[j][1]) * Norm(Transpose(BC)[1])^(1/2) - (#JJJ - 1 - j)*delta[j] then
max:=2^(-(#JJJ-2)/2) * DistanceToNearestInteger(sss[j][1]) * Norm(Transpose(BC)[1])^(1/2) - (#JJJ - 1 - j)*delta[j];
end if;
end for;
lowerbound:=max;

/*
fprintf LogFile, "phi[1] = %o\n", phi[1];
fprintf LogFile, "(R^2 + S)^(1/2) = %o\n", (R^2 + S)^(1/2);
fprintf LogFile, "lowerbound = %o\n", lowerbound;
fprintf LogFile, "IndicesjWithsjNotIntegral = %o\n", IndicesjWithsjNotIntegral;
for i:=1 to #JJJ-1 do
fprintf LogFile, "DistanceToNearestInteger(sss[i][1]) = %o\n", RealField() ! DistanceToNearestInteger(sss[i][1]);
end for;
fprintf LogFile, "Norm(Transpose(BC)[1])^(1/2) = %o\n", Norm(Transpose(BC)[1])^(1/2);
*/

/*
print("phi[1]");
phi[1];
print("(R^2 + S)^(1/2):");
Floor((R^2 + S)^(1/2));
print("lowerbound, y ne 0:");
Floor(lowerbound);
print("IndicesjWithsjNotIntegral");
IndicesjWithsjNotIntegral;
print("DistanceToNearestInteger(sss[#JJJ-1][1]);");
RealField() ! DistanceToNearestInteger(sss[#JJJ-1][1]);
print("DistanceToNearestInteger(sss[#JJJ-2][1]);");
RealField() ! DistanceToNearestInteger(sss[#JJJ-2][1]);
print("Norm(Transpose(BC)[1]^(1/2))");
Norm(Transpose(BC)[1])^(1/2);
print("2^(-(#JJJ-2)/2)");
2^(-(#JJJ-2)/2);
*/


end if;
//END IF



if lowerbound gt (R^2 + S)^(1/2) then

//////////
/*
Choose c11 to find an optimal i0-conditional upper bound for A from Lemma 19.2
*/
//////////
MIN:=UpperBoundForA;

c11:=(1/1000000)*c10/(n-1);
max:=Max([
Floor((1/c11)*( Log(2*Log(2)*c16[i0]) + Log(CCCCCC) - Log((lowerbound^2 - S)^(1/2) - R) )),
Ceiling((c8prime + c9prime*UpperBoundForN)/(c10 - (n-1)*c11))-1,
Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10 - c11))-1,
Ceiling(Log(2*c16[i0])/c11)-1,
0
]);
if max lt MIN then MIN:=max; end if;

c11:=((1000000-1)/1000000)*c10/(n-1);
max:=Max([
Floor((1/c11)*( Log(2*Log(2)*c16[i0]) + Log(CCCCCC) - Log((lowerbound^2 - S)^(1/2) - R) )),
Ceiling((c8prime + c9prime*UpperBoundForN)/(c10 - (n-1)*c11))-1,
Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10 - c11))-1,
Ceiling(Log(2*c16[i0])/c11)-1,
0
]);
if max lt MIN then MIN:=max; end if;

for i:=1 to 999 do
c11:=(i/1000)*c10/(n-1);
max:=Max([
Floor((1/c11)*( Log(2*Log(2)*c16[i0]) + Log(CCCCCC) - Log((lowerbound^2 - S)^(1/2) - R) )),
Ceiling((c8prime + c9prime*UpperBoundForN)/(c10 - (n-1)*c11))-1,
Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10 - c11))-1,
Ceiling(Log(2*c16[i0])/c11)-1,
0
]);
if max lt MIN then MIN:=max; end if;
end for; //end i loop
////


OldUnconditionalUpperBoundForA:=UpperBoundForA;
NewConditionalUpperBoundForAi0:=MIN;

if NewConditionalUpperBoundForAi0 lt OldUnconditionalUpperBoundForA then
ConditionalUpperBoundForA[i0]:=NewConditionalUpperBoundForAi0;
flag:=false; //ready to get out of while loop that increases C if necessary
else
RunThroughNumber2:=RunThroughNumber2+1; //increase C and try again
////////
/*
In case we find a new conditional upper bound that fails to improve on 
the current unconditional upper bound for A, we decrease log(C) by 25 percent 
and try again. If this doesn't result in an improved bound, we then we abort 
the real reduction procedure.  There is no need to print a message in this case.
*/
///////
if RunThroughNumber2 eq 2 then 
JumpToEndOfRealReduction:=true;
break i0;
end if;
end if; /*controlled by NewConditionalUpperBoundForAi0 lt OldUnconditionalUpperBoundForA*/

else //controlled by lowerbound gt (R^2 + S)^(1/2)

RunThroughNumber1:=RunThroughNumber1+1; //increase C and try again
/////
/*
If increasing log(C) 22 times (with log(C) being increased 5% the first 
twenty times and by 1000% the last two times, so that log(C) will be 
20 times original value) fails to produce a new conditional upper 
bound for A, then we abort the real reduction procedure.  Also, print 
a message to the user indicating the basic real reduction procedure 
was unsuccesful for this reason.  Note: tries 21 and 22 only happen 
if the upper for A has not been reduced much (or at all) from the linear 
forms in logs bound.
*/
////
if RunThroughNumber1 eq 23 then
PrintFile(LogFile,"Basic real reduction taking a long time."); 
fprintf LogFile, "case: iiii = %o\n", iiii;
fprintf LogFile, "i0 = %o\n", i0;
fprintf LogFile, "Improvement = %o\n", Improvement;
fprintf LogFile, "UpperBoundForn = %o\n", UpperBoundForn;
fprintf LogFile, "UpperBoundForA = %o\n", UpperBoundForA;
fprintf LogFile, "Log(CCCCCC) = %o\n", Log(CCCCCC);

if UpperBoundForA gt 1000000000000 then //10^12
print "Basic real reduction taking a long time."; 
printf "case: iiii = %o\n", iiii;
printf "i0 = %o\n", i0;
printf "Improvement = %o\n", Improvement;
printf "UpperBoundForn = %o\n", UpperBoundForn;
printf "UpperBoundForA = %o\n", UpperBoundForA;
printf "Log(CCCCCC) = %o\n", Log(CCCCCC);
PrintFile(OutFile,"Basic real reduction taking a long time."); 
fprintf OutFile, "case: iiii = %o\n", iiii;
fprintf OutFile, "i0 = %o\n", i0;
fprintf OutFile, "Improvement = %o\n", Improvement;
fprintf OutFile, "UpperBoundForn = %o\n", UpperBoundForn;
fprintf OutFile, "UpperBoundForA = %o\n", UpperBoundForA;
fprintf OutFile, "Log(CCCCCC) = %o\n", Log(CCCCCC);
end if;
/*
GammaC:=Lattice(Transpose(AC));
w:=CoordinateSpace(GammaC) ! [0,yyy[2][1]];
ClosestVectorsMatrix(GammaC,w : Max:=5);
*/
JumpToEndOfRealReduction:=true;
break i0;
end if;

end if; //controlled by lowerbound gt (R^2 + S)^(1/2)

end while; /* this is the loop that increases log(C) if necessary, the while loop controlled by flag */

end for; //end i0 loop


if JumpToEndOfRealReduction eq false then
/////////////
/* 
Choose c11 to find an optimal i0-conditional upper bound for A for 
i0 in {s+1,...,s+2t} from Lemma 19.1 
*/
///////////
MIN:=UpperBoundForA;

c11:=(1/1000000)*c10/(n-1);

c15:=0;
if t gt 0 then
min:=Abs(Imaginary(thetaC[s+1]));
for ii:=2 to t do
j:=s-1 + 2*ii;
if Abs(Imaginary(thetaC[j])) lt min then min:=Abs(Imaginary(thetaC[j])); end if;
end for; //end ii
if Floor(-Log(min)/c11) gt 0 then c15:=Floor(-Log(min)/c11); end if;
end if;

max:=Ceiling((c8prime + c9prime*UpperBoundForN)/(c10-(n-1)*c11))-1;
if max lt Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1 then
max:=Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1;
end if;
if max lt c15 then max:=c15; end if; 
//now max is the upper bound for A in Lemma 19.1
if max lt MIN then MIN:=max; end if;

c11:=((1000000 - 1)/1000000)*c10/(n-1);

c15:=0;
if t gt 0 then
min:=Abs(Imaginary(thetaC[s+1]));
for ii:=2 to t do
j:=s-1 + 2*ii;
if Abs(Imaginary(thetaC[j])) lt min then min:=Abs(Imaginary(thetaC[j])); end if;
end for; //end ii
if Floor(-Log(min)/c11) gt 0 then c15:=Floor(-Log(min)/c11); end if;
end if;

max:=Ceiling((c8prime + c9prime*UpperBoundForN)/(c10-(n-1)*c11))-1;
if max lt Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1 then
max:=Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1;
end if;
if max lt c15 then max:=c15; end if; 
//now max is the upper bound for A in Lemma 19.1
if max lt MIN then MIN:=max; end if;

for i:=1 to 999 do
c11:=(i/1000)*c10/(n-1);

c15:=0;
if t gt 0 then
min:=Abs(Imaginary(thetaC[s+1]));
for ii:=2 to t do
j:=s-1 + 2*ii;
if Abs(Imaginary(thetaC[j])) lt min then min:=Abs(Imaginary(thetaC[j])); end if;
end for; //end ii
if Floor(-Log(min)/c11) gt 0 then c15:=Floor(-Log(min)/c11); end if;
end if;

max:=Ceiling((c8prime + c9prime*UpperBoundForN)/(c10-(n-1)*c11))-1;
if max lt Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1 then
max:=Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1;
end if;
if max lt c15 then max:=c15; end if; 
//now max is the upper bound for A in Lemma 19.1
if max lt MIN then MIN:=max; end if;
end for;  //end i loop

/////
/*
Compute the new unconditional bound for A
*/
/////

OldUpperBoundForA:=UpperBoundForA;
NewUpperBoundForA:=Max([Max(ConditionalUpperBoundForA),MIN]);

if NewUpperBoundForA lt OldUpperBoundForA then
Improvement:=true;
UpperBoundForA:=NewUpperBoundForA;
for i:=1 to r do
B[1+v+i]:=UpperBoundForA;
end for;
end if;

end if; //controlled by JumpToEndOfRealReduction

if UpperBoundForA lt 0 then 
//there are no solutions to the current case of (11)
fprintf LogFile, "UpperBoundForA lt 0. No solutions possible in case iiii = %o\n", iiii;
continue iiii;
end if;



//////////////////////////////////////////////////////////////////////////////
/*
Complex Case, i.e., s = 1,2
*/
//////////////////////////////////////////////////////////////////////////////
else //s=1,2 complex case

B[2+v+r]:=Floor(2*Arcsin(1/4)/PI);
for i in JJJ do
B[2+v+r]:=B[2+v+r] + B[i];
end for;


JumpToEndOfRealReduction:=false;
for i0:=1 to s do 

//RGB
//print("basic real, s=, i0=");
//s;
//i0;


////////////////////////////////////////////////////////////////////////////
/*
Define 
weights W[i] (Section 19)
R (Section 19)
S (Section 19)
CCCCCC = C (Section 19)

Initialize:
TC, where Transpose(TC) = U_C from Section 19
phi[i]:= phi_i from Section 19
*/
////////////////////////////////////////////////////////////////////////////
W:=[];
for i:=1 to 1+v+r do
W[i]:=0; //initialize
end for;

H0prime:=0;
for i:=2 to #JJJ do
if H0prime lt B[JJJ[i]] then H0prime:=B[JJJ[i]]; end if;
end for;

W[1]:=0;
for i:=2 to #JJJ do
W[JJJ[i]]:=RoundP(H0prime/ RNTO(B[JJJ[i]]) );
end for;
//print("weights");
//W;
//print("B");
//B;

R:=B[2+v+r];
for i in JJJ do 
R:=R + B[i];
end for;
R:=(1/2)*R;
//this is just an approximation to R

S:=0;
for i:=2 to #JJJ do
S:=S+(W[JJJ[i]]^2)*(B[JJJ[i]]^2);
end for;

prod:=1;
for i:=2 to #JJJ do
prod:=prod*W[JJJ[i]];
end for;

/*
LogC:= ((#JJJ)/2)*Log( 
(R^2 + S) / ( 2^(-(#JJJ)) * (Abs(LogarithmicAlphaC[i0][2+v+r])*prod)^(2/(#JJJ)) )
);
*/
LogC:= ((#JJJ)/2)*Log( 
(R^2 + S) / ( 2^(-2*(#JJJ)) * (Abs(LogarithmicAlphaC[i0][2+v+r])*prod)^(2/(#JJJ)) )
);


//CCCCCC:=Ceiling(Exp(LogC));

TC:=ScalarMatrix(IntegerRing(),#JJJ,1); //#JJJ by #JJJ identity matrix

phi:=[];
for i:=1 to 2+v+r do
phi[i]:=0;
end for;

/////////////////////////////////////////////////////////////////////////////
/*
Start the while loop where C will be increased until a new conditional upper for A is found that improves on the uncondtional upper bound for A or until a number of increases of C have been made with no success.
*/
////////////////////////////////////////////////////////////////////////////
RunThroughNumber1:=0;
RunThroughNumber2:=0;
flag:=true;
while flag do

//////////////////////////////////////////////////////////////////////////////
/*
Increase CCCCCC = C (if this is not the first attempt the basic real reduction procedure).

Calculate the phi_i for i in JJJ.

Calculate R.
*/
////////////////////////////////////////////////////////////////////////////
CCCCCC:=Ceiling(Exp( LogC + RunThroughNumber1*(5/100)*LogC + RunThroughNumber2*(-25/100)*LogC ));
if RunThroughNumber1 eq 21 and UpperBoundForA gt 100000 then 
CCCCCC:=Ceiling(Exp(LogC + 9*LogC));
end if;
if RunThroughNumber1 eq 22 and UpperBoundForA gt 100000 then 
CCCCCC:=Ceiling(Exp(LogC + 19*LogC));
end if;

if LogC/Log(10) gt (0.95)*realprecision then
RealPrecisionMultiplier := RealPrecisionMultiplier + 1;
/*
print("LogC/Log(10)");
LogC/Log(10);
print("realprecision");
realprecision;
*/
continue PrecisionLoopVariable;
end if;

for i in JJJ do
phi[i]:=Round(CCCCCC*LogarithmicAlphaC[i0][i]);
end for;
phi[2+v+r]:=Round(CCCCCC*LogarithmicAlphaC[i0][2+v+r]);


/*This will never happen because LogarithmicAlphaC[i0][2+v+r] = Pi */
/*
if Abs(phi[2+v+r]) lt 2 then 
if CCCCCC*LogarithmicAlphaC[i0][2+v+r] ge 0 then 
phi[2+v+r]:=2;
else
phi[2+v+r]:=-2;
end if;
end if;

if IsIntegral(phi[1]/phi[2+v+r]) then
if Abs(phi[1]+1 - CCCCCC*LogarithmicAlphaC[i0][1]) le 1 then
phi[1]:=phi[1]+1;
else
phi[1]:=phi[1]-1;
end if;
end if;
*/


//phi[2+v+r] neq 0 because LogarithmicAlphaC[i0][2+v+r] = Pi
if IsIntegral(phi[1]/phi[2+v+r]) then
bbb:=[1];
for i:=2 to #JJJ do bbb[i]:=0; end for;
bbb[#JJJ+1]:=-phi[1]/phi[2+v+r];
Include(~ExceptionalTuplesInsideLoop,bbb);
end if;


R:=B[2+v+r]*Abs( CCCCCC*LogarithmicAlphaC[i0][2+v+r] -  phi[2+v+r] );
for i in JJJ do 
R:=R + B[i]*Abs( CCCCCC*LogarithmicAlphaC[i0][i] -  phi[i] );
end for;

///////////////////////////////////////////////////////////////////////////////
/*
Compute:
AC = A_C
*/
//////////////////////////////////////////////////////////////////////////////
AC:=ZeroMatrix(IntegerRing(),v+r+2,v+r+2);

for i:=1 to 1+v+r do
AC[i][i]:=W[i];
end for;
for j:=1 to v+r+2 do
AC[v+r+2][j]:=phi[j];
end for;

for i:=1+v+r to 2 by -1 do
if not i in JJJ then
RemoveColumn(~AC,i);
RemoveRow(~AC,i);
end if;
end for;

RemoveRow(~AC,1);
RemoveColumn(~AC,1);

//AC is now a #JJJ by #JJJ matrix

AC:=AC*Transpose(TC);
/* If this is the first run through Transpose(TC) is the identity. 
Otherwise Transpose(TC) is UC.  This will time in the LLL reduction. */

///////////////////////////////////////////////////////////////////////////////
/*
Compute LLL reduced basis for the lattice Gamma_C generated by columns of A_C.  The algoritm used is de Weger's exact integer version of LLL.

Note: LLL(X) assumes ROWS of X span the lattice, so we need to feed it the transpose of A_C.  Similarly, it spits out the transpose of B_C and the transpose of U_C
*/
///////////////////////////////////////////////////////////////////////////////

temp,TC,rank:=LLL(Transpose(AC) : Proof:=true, Method:="Integral", Delta:=0.75, Eta:=0.5 );

BC:=MatrixRing(RationalField(),#JJJ) ! Transpose(temp); 
//columns are LLL-reduced basis for Gamma_C

/*
Here TC*Transpose(AC) = Transpose(BC). 
So with UC=Transpose(TC) we have AC*UC = BC,
and With 
VC = BC*Transpose(TC)*BC^(-1) = AC*Transpose(TC)*AC^(-1), we have VC*AC = BC.
*/

///////////////////////////////////////////////////////////////////////////////
/*
Compute the lower bound for l(Gamma_C,y).  If it is large enough (bigger than sqrt(R^2 + S)), compute the new upper bound for n[L].  Otherwise, increase C and reduce again (go back to the start of the while loop)
*/
///////////////////////////////////////////////////////////////////////////////
lowerbound:=0;

//START IF
if phi[1] eq 0 then //y = 0 case (vectors) //never happens by choice of phi[1]

// \vec{c}_1 = Transpose(BC)[1]
lowerbound:= 2^(-(#JJJ-1)/2)*Norm( Transpose(BC)[1] )^(1/2);

else    //y neq 0 case

yyy:=ZeroMatrix(RationalField(),#JJJ,1);
yyy[#JJJ][1]:=-phi[1];
sss:=(BC^(-1))*yyy;

IndicesjWithsjNotIntegral:=[];
for j:=1 to #JJJ do
if not IsIntegral(sss[j][1]) then
Append(~IndicesjWithsjNotIntegral,j);
end if;
end for;

delta:=[RealField() | ];
for j:=1 to #JJJ-1 do
delta[j]:=0;
for i:=j+1 to #JJJ do
if delta[j] lt DistanceToNearestInteger(sss[i][1])*Norm(Transpose(BC)[i])^(1/2) then
delta[j]:=DistanceToNearestInteger(sss[i][1])*Norm(Transpose(BC)[i])^(1/2);
end if;
end for;
end for;
delta[#JJJ]:=0;

max:=0;
for j in IndicesjWithsjNotIntegral do
if max lt 2^(-(#JJJ-1)/2) * DistanceToNearestInteger(sss[j][1]) * Norm(Transpose(BC)[1])^(1/2) - (#JJJ - j)*delta[j] then
max := 2^(-(#JJJ-1)/2) * DistanceToNearestInteger(sss[j][1]) * Norm(Transpose(BC)[1])^(1/2) - (#JJJ - j)*delta[j];
end if;
end for;
lowerbound:=max;

end if;
//END IF

if lowerbound gt (R^2 + S)^(1/2) then

//////////
/*
Choose c11 to find an optimal i0-conditional upper bound for A from Lemma 19.2
*/
//////////
MIN:=UpperBoundForA;

c11:=(1/1000000)*c10/(n-1);
max:=Max([
Floor((1/c11)*( Log(4*Arcsin(1/4)*c16[i0]) + Log(CCCCCC) - Log((lowerbound^2 - S)^(1/2) - R) )),
Ceiling((c8prime + c9prime*UpperBoundForN)/(c10 - (n-1)*c11))-1,
Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10 - c11))-1,
Ceiling(Log(2*c16[i0])/c11)-1,
0
]);
if max lt MIN then MIN:=max; end if;

c11:=((1000000-1)/1000000)*c10/(n-1);
max:=Max([
Floor((1/c11)*( Log(4*Arcsin(1/4)*c16[i0]) + Log(CCCCCC) - Log((lowerbound^2 - S)^(1/2) - R) )),
Ceiling((c8prime + c9prime*UpperBoundForN)/(c10 - (n-1)*c11))-1,
Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10 - c11))-1,
Ceiling(Log(2*c16[i0])/c11)-1,
0
]);
if max lt MIN then MIN:=max; end if;

for i:=1 to 999 do
c11:=(i/1000)*c10/(n-1);
max:=Max([
Floor((1/c11)*( Log(4*Arcsin(1/4)*c16[i0]) + Log(CCCCCC) - Log((lowerbound^2 - S)^(1/2) - R) )),
Ceiling((c8prime + c9prime*UpperBoundForN)/(c10 - (n-1)*c11))-1,
Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10 - c11))-1,
Ceiling(Log(2*c16[i0])/c11)-1,
0
]);
if max lt MIN then MIN:=max; end if;
end for; //end i loop
////


OldUnconditionalUpperBoundForA:=UpperBoundForA;
NewConditionalUpperBoundForAi0:=MIN;

if NewConditionalUpperBoundForAi0 lt OldUnconditionalUpperBoundForA then
ConditionalUpperBoundForA[i0]:=NewConditionalUpperBoundForAi0;
flag:=false; //ready to get out of while loop that increases C if necessary
else
RunThroughNumber2:=RunThroughNumber2+1; //increase C and try again
////////
/*
In case we find a new conditional upper bound that fails to improve on 
the current unconditional upper bound for A, we decrease log(C) by 25 percent 
and try again. If this doesn't result in an improved bound, we then we abort 
the real reduction procedure.  There is no need to print a message in this case.
*/
///////
if RunThroughNumber2 eq 2 then 
JumpToEndOfRealReduction:=true;
break i0;
end if;
end if; /*controlled by NewConditionalUpperBoundForAi0 lt OldUnconditionalUpperBoundForA*/

else //controlled by lowerbound gt (R^2 + S)^(1/2)

RunThroughNumber1:=RunThroughNumber1+1; //increase C and try again
/////
/*
If increasing log(C) 22 times (with log(C) being increased 5% the first 
twenty times and by 1000% the last two times, so that log(C) will be 
20 times original value) fails to produce a new conditional upper 
bound for A, then we abort the real reduction procedure.  Also, print 
a message to the user indicating the basic real reduction procedure 
was unsuccesful for this reason.  Note: tries 21 and 22 only happen 
if the upper for A has not been reduced much (or at all) from the linear 
forms in logs bound.
*/
////
if RunThroughNumber1 eq 23 then 
PrintFile(LogFile,"Basic real reduction taking a long time."); 
fprintf LogFile, "case: iiii = %o\n", iiii;
fprintf LogFile, "i0 = %o\n", i0;
fprintf LogFile, "Improvement = %o\n", Improvement;
fprintf LogFile, "UpperBoundForn = %o\n", UpperBoundForn;
fprintf LogFile, "UpperBoundForA = %o\n", UpperBoundForA;
fprintf LogFile, "Log(CCCCCC) = %o\n", Log(CCCCCC);

if UpperBoundForA gt 1000000000000 then //10^12
print "Basic real reduction taking a long time."; 
printf "case: iiii = %o\n", iiii;
printf "i0 = %o\n", i0;
printf "Improvement = %o\n", Improvement;
printf "UpperBoundForn = %o\n", UpperBoundForn;
printf "UpperBoundForA = %o\n", UpperBoundForA;
printf "Log(CCCCCC) = %o\n", Log(CCCCCC);
end if;

JumpToEndOfRealReduction:=true;
break i0;
end if;

end if; //controlled by lowerbound gt (R^2 + S)^(1/2)

end while; /* this is the loop that increases log(C) if necessary, the while loop controlled by flag */

end for; //end i0 loop


if JumpToEndOfRealReduction eq false then
/////////////
/* 
Choose c11 to find an optimal i0-conditional upper bound for A for i0 in {s+1,...,s+2t} from Lemma 19.1 
*/
///////////
MIN:=UpperBoundForA;

c11:=(1/1000000)*c10/(n-1);

c15:=0;
if t gt 0 then
min:=Abs(Imaginary(thetaC[s+1]));
for ii:=2 to t do
j:=s-1 + 2*ii;
if Abs(Imaginary(thetaC[j])) lt min then min:=Abs(Imaginary(thetaC[j])); end if;
end for; //end ii
if Floor(-Log(min)/c11) gt 0 then c15:=Floor(-Log(min)/c11); end if;
end if;

max:=Ceiling((c8prime + c9prime*UpperBoundForN)/(c10-(n-1)*c11))-1;
if max lt Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1 then
max:=Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1;
end if;
if max lt c15 then max:=c15; end if; 
//now max is the upper bound for A in Lemma 19.1
if max lt MIN then MIN:=max; end if;

c11:=((1000000 - 1)/1000000)*c10/(n-1);

c15:=0;
if t gt 0 then
min:=Abs(Imaginary(thetaC[s+1]));
for ii:=2 to t do
j:=s-1 + 2*ii;
if Abs(Imaginary(thetaC[j])) lt min then min:=Abs(Imaginary(thetaC[j])); end if;
end for; //end ii
if Floor(-Log(min)/c11) gt 0 then c15:=Floor(-Log(min)/c11); end if;
end if;

max:=Ceiling((c8prime + c9prime*UpperBoundForN)/(c10-(n-1)*c11))-1;
if max lt Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1 then
max:=Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1;
end if;
if max lt c15 then max:=c15; end if; 
//now max is the upper bound for A in Lemma 19.1
if max lt MIN then MIN:=max; end if;

for i:=1 to 999 do
c11:=(i/1000)*c10/(n-1);

c15:=0;
if t gt 0 then
min:=Abs(Imaginary(thetaC[s+1]));
for ii:=2 to t do
j:=s-1 + 2*ii;
if Abs(Imaginary(thetaC[j])) lt min then min:=Abs(Imaginary(thetaC[j])); end if;
end for; //end ii
if Floor(-Log(min)/c11) gt 0 then c15:=Floor(-Log(min)/c11); end if;
end if;

max:=Ceiling((c8prime + c9prime*UpperBoundForN)/(c10-(n-1)*c11))-1;
if max lt Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1 then
max:=Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1;
end if;
if max lt c15 then max:=c15; end if; 
//now max is the upper bound for A in Lemma 19.1
if max lt MIN then MIN:=max; end if;
end for;  //end i loop

//MIN is now an i0-conditional upper bound for A for i0 in {s+1,...,s+2t}

/////
/*
Compute the new unconditional bound for A
*/
/////

OldUpperBoundForA:=UpperBoundForA;
NewUpperBoundForA:=Max([Max(ConditionalUpperBoundForA),MIN]);

if NewUpperBoundForA lt OldUpperBoundForA then
Improvement:=true;
UpperBoundForA:=NewUpperBoundForA;
for i:=1 to r do
B[1+v+i]:=UpperBoundForA;
end for;
end if;

end if; //controlled by JumpToEndOfRealReduction

if UpperBoundForA lt 0 then 
//there are no solutions to the current case of (11)
fprintf LogFile, "UpperBoundForA lt 0. No solutions possible in case iiii = %o\n", iiii;
continue iiii;
end if;



end if; //end of IF for distinguishing (s>=3) (s=1,2) cases

end if; //end of IF for s=0, s>=3, s=1or2 cases    

//done finding new upper bound for A

UpperBoundForH:=Max([UpperBoundForN, UpperBoundForA]);
//print("at end of improvement loop:");

/*
RGB
print("Upper bounds for the n_l and A, respectively:");
UpperBoundForn;
Floor(UpperBoundForA);
*/

for tup in ExceptionalTuplesInsideLoop do
Include(~ExceptionalTuples,tup);
end for;

end while;  //end loop for repeated simple reductions (the improvement loop)
//////////////////////////////////////////////////////////////////////////////
/*
End Of Loop For Repeated Basic Reductions (the improvement loop)
*/
//////////////////////////////////////////////////////////////////////////////

PrintFile(LogFile, "Starting refined reduction procedures.");
fprintf LogFile, "UpperBoundForn = %o\n", UpperBoundForn;
fprintf LogFile, "UpperBoundForA = %o\n", UpperBoundForA;

/////////////////////////////////////////////////////////////////////////////
/*
Initialize the set of exceptional tuples.  It will be filled as we work through 
the refined redcution procedures.

At the end, it will consist of the tuples that pass all the easy tests.  The tuples 
will not have been tested for (11) directly and they won't all necessarily be 
soltutions of (11).  We will test them more in the final sieve step.

Each element of ExceptionalTuples will be a sequence of the form
[b_{JJJ[2]},...,b_{JJJ[#JJJ]}].
*/
/////////////////////////////////////////////////////////////////////////////
//ExceptionalTuples:=[];
ExceptionalTuplesInsideLoop:=[];

////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////
////////////////////////
/*
Start Of Loop For Repeated Refined Reductions
*/
////////////////////////
//////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////
Improvement:=true;

while Improvement do 
Improvement:=false;
ExceptionalTuplesInsideLoop:=[];

/////////////////////////////////////////////////////////////////////////////
/*
If the number of tuples to sieve through is small enough, jump directly to the 
final sieving procedure.

If the number of exceptional tuples has grown excessively large, jump to the 
final sieving procedure and inform that user that this has been done.
*/
//////////////////////////////////////////////////////////////////////////////
prod:=1;
for i in J do
prod:=prod*(UpperBoundForn[i]+1);
end for;
prod:=prod*(2*UpperBoundForA + 1)^r;
if prod lt 5000000 then 
break; 
end if; //prod = number of tuples to sieve

if #ExceptionalTuples gt 100000 then 
fprintf LogFile, "The number of exceptional tuples is large. Jumping to the final sieving procedure. Case iiii = %o\n", iiii;
break; 
end if;


////////////////////////////////////////////////////////////////////////////
/*
Refined p_l-adic reduction for each l in I (Section 20)
*/
////////////////////////////////////////////////////////////////////////////



for l in I do

//RGB
//print("refined p_l, l=");
//l;


//////////////////////////////////////////////////////////////////////////////
/*
Define:
W[i] = W_i (weights) for p_l (Section 20)
QQ = Q (Section 20)
mmmm = m for p_l (Section 20)

Initialize:
betam[i] = beta_i^(m) for p[L],
Tm, where Transpose(Tm) = U_m from Section 20
*/
//////////////////////////////////////////////////////////////////////////////
W:=[];
for i:=1 to 1+v+r do
W[i]:=0; //initialize
end for;

W[1]:=0;
for i:=2 to #JJJ do
W[JJJ[i]]:=RoundP(UpperBoundForH/ RNTO(B[JJJ[i]]) );
end for;
for i in J do
W[1+i]:=2*W[i+1];
end for;
//print("weights");
//W;
//print("B");
//B;

QQ:=0;
for i in JJJ do
QQ:=QQ+(W[i]^2)*(B[i]^2); //recall W[1]=0
end for;

prod:=1;
for i:=2 to #JJJ do
prod:=prod*W[JJJ[i]];
end for;

/*
mmmm0:=Ceiling(
(3/4)*( (#JJJ - 1)/(2*Log(p[l])) )*Log( 2^(#JJJ - 1) * QQ / prod^(2/(#JJJ-1)) )  
);
*/

mmmm0:=Min([
Ceiling(
(2/3)*( (#JJJ - 1)/(2*Log(p[l])) )*Log( QQ / prod^(2/(#JJJ-1)) )  
),
Ceiling((2/3)*UpperBoundForn[l])
]);

if mmmm0 le 0 then mmmm0:=1; end if;

betam:=[];
for i:=1 to 1+v+r do
betam[i]:=0;
end for;

Tm:=ScalarMatrix(IntegerRing(),#JJJ-1,1);/*initialize as #JJJ-1 by #JJJ-1 identity matrix*/

///////////////////////////////////////////////////////////////////////////
/* 
Start while loop that will increase m until the p_l-adic reduction yeilds a 
new upper bound for n_l or until a number of increases has been made with no 
success
*/
///////////////////////////////////////////////////////////////////////////
flag:=true;
RunThroughNumber:=0;
while flag do 

/////////////////////////////////////////////////////////////////////////////
/*
Increase mmmm = m (if this is not the first attempt with the basic p_l-reduction procedure).
Calculuate betam[i] = beta_i^(m).
*/
//////////////////////////////////////////////////////////////////////////
mmmm:=Ceiling( mmmm0 + RunThroughNumber*(5/100)*mmmm0 );
for i in JJJ do
betam[i]:= SmallestNonnegativeRemainderModpLToThem(beta[l][i],p[l],mmmm,padicprecision[l]);
end for;

/////////////////////////////////////////////////////////////////////////////
/*
Compute the (soon to be) new upper bound for n_l.  If it is better than the 
old upper bound, then we do the enumeration procedure.  If it is not better, 
there is no need to do the enumeration and we move on to the next l in I
*/
/////////////////////////////////////////////////////////////////////////////
NewUpperBoundFornl:=Max([
Floor(   (1/hh[l])*( 1/(p[l]-1) - Valuation(delta2[l]) )    ),
Ceiling((1/hh[l])*(mmmm-dd[l]))-1
]);

OldUpperBoundFornl:=UpperBoundForn[l];

//PrintFile(LogFile,l);
//PrintFile(LogFile,[
//Floor( (1/hh[l])*(1/(p[l]-1) - Valuation(delta2[l])) ),
//Ceiling((1/hh[l])*(mmmm-dd[l]))-1
//]);
//PrintFile(LogFile,OldUpperBoundFornl);

if NewUpperBoundFornl ge OldUpperBoundFornl then
continue l;
else // NewUpperBoundFornl lt OldUpperBoundFornl


//////////////////////////////////////////////////////////////////////////////
/*
Define:
Am = A_m for p[L]
Gamma_m = lattice generated by columns of A_m
*/
//////////////////////////////////////////////////////////////////////////////
Am:=ZeroMatrix(IntegerRing(), v+r+2, v+r+2);
for i:=1 to v+r+1 do
Am[i][i]:=W[i];
end for;
for j:=1 to v+r+1 do
Am[v+r+2][j]:=W[ihat[l]]*betam[j];
end for;
Am[v+r+2][v+r+2]:=W[ihat[l]]*p[l]^mmmm;

for i:=1+v+r to 2 by -1 do
if i eq ihat[l] or not i in JJJ then
RemoveColumn(~Am,i);
RemoveRow(~Am,i);
end if;
end for;

RemoveColumn(~Am,1);
RemoveRow(~Am,1);

//Am is now a #JJJ-1 by #JJJ-1 matrix

Am:=Am*Transpose(Tm); //Transpose(Tm) = Um from Setion 15
/* 
If this is the first run through, Tm is the identity. 
If this is not the first run through, this will save computation time.
*/

//////////////////////////////////////////////////////////////////////////////
/*
Compute an LLL reduced basis for the lattice Gamma_m generated by columns of A_m.  The algorithm used is de Weger's exact integer version of LLL.

Note: LLL(X) assumes ROWS of X span the lattice, so we need to feed it the transpose of A_m.  Similarly, it spits out the transpose of B_m and the transpose of U_m
*/
//////////////////////////////////////////////////////////////////////////////
//time 
temp,Tm,rank:=LLL( Transpose(Am) : Proof:=true, Method:="Integral", Delta:=0.75, Eta:=0.5 );

Bm:=MatrixRing(RationalField(),#JJJ-1) ! Transpose(temp); 
//columns are LLL-reduced basis for Gamma_m

/*
Here Tm*Transpose(Am) = Transpose(Bm). 
So with Um=Transpose(Tm) we have Am*Um = Bm,
and With 
Vm = Bm*Transpose(Tm)*Bm^(-1) = Am*Transpose(Tm)*Am^(-1), we have Vm*Am = Bm.
*/

///////////////////////////////////////////////////////////////////////////////
/*
Define:
yyy = \vec{y} from Section 20
sss = \vec{s} from Section 20
ttt = \vec{t} from Section 20
zzz = \vec{z} from Section 20
DDD = D from Section 20
*/
///////////////////////////////////////////////////////////////////////////////

yyy:=ZeroMatrix(RationalField(),2+v+r,1);
for i:=1 to v do
yyy[1+i][1]:=(1/2)*W[i+1]*B[i+1];
end for;
for i:=1+v+r to 2 by -1 do
if i eq ihat[l] or not i in JJJ then
RemoveRow(~yyy,i);
end if;
end for;
RemoveRow(~yyy,1);
//yyy is now a #JJJ-1 by 1 column vector
if ihat[l] le 1+v then
yyy[#JJJ-1][1]:=-W[ihat[l]]*betam[1]+(1/2)*W[ihat[l]]*B[ihat[l]];
else //ihat[l] gt 1+v
yyy[#JJJ-1][1]:=-W[ihat[l]]*betam[1];
end if;

sss:=(Bm^(-1))*yyy;

ttt:=sss;
for i:=1 to #JJJ-1 do
ttt[i][1]:=Floor(sss[i][1]);
end for;
Floorsss:=ttt;
potentialttt:=ttt;
min:=LengthOfVector(Bm*ttt - yyy);

mm:=#JJJ-1;
yyytttpotentialtttFloorsss:=[yyy,ttt,potentialttt,Floorsss];
//Type(yyytttpotentialtttFloorsss);
Choosettt(~yyytttpotentialtttFloorsss,~min,~Bm,~mm,1);

zzz:=Bm*ttt;

DDD:=0;
for i in J do
DDD:=DDD + ((1/2)*W[1+i]*B[1+i])^2;
end for;
for i:=1 to r do
DDD:=DDD + (W[1+v+i]*B[1+v+i])^2;
end for;
DDD:=DDD^(1/2);
DDD:=DDD+min;


////////////////////////////////////////////////////////////////////////
/*
Construct the lattice Gamma_m.  The MAGMA function Lattice() assumes

Use the function EnumerationCost to compute an estimate the number of nodes 
in the tree to be visited during the execution of the algorithm that will 
enumerate all lattice vectors u with |u| \leq D.  The number of nodes is 
essentially directly proportional to the time needed for the enumeration.

If the number of nodes is too large for the enumration to be done in a 
reasonable amount of time, we increase m and try the reduction procedure 
again.  If several increases of m fail to result in a small enough estimate 
for the number of nodes, then we move onto the next l in I.

In Stehle and Watkins (2006), it is asserted that MAGMA's enumeration 
algorithm has a traversal rate of about 7.5 millon nodes per second.  
Based on the examples in the MAGMA Handbook, the rate is appears to be 20 to 
40 millon nodes per second. We will assume a traversal rate of 10 millon nodes 
per second.  Assuming we want the enumeration to take less than 10 minutes, we 
want to abort if the estimated number of nodes is > 10*60*10^7 = 6000000000

The enumeration algorithm may be fast, but the extraction and testing of the 
tuples can take time. So we abort if the estimated number of nodes is 
> 10*60*10^4 

Note: To MAGMA, Norm(v) = |v|^2.
*/
////////////////////////////////////////////////////////////////////////

Gammam:=Lattice(Transpose(Bm));

fprintf LogFile, "l = %o, RunThroughNumber = %o, enumcost = %o\n", l, RunThroughNumber, EnumerationCost(Gammam,RealField() ! DDD^2);


if EnumerationCost(Gammam,RealField() ! DDD^2) gt 6000000 then

RunThroughNumber+:=1;  //increase m and try again
///
/*
If increasing m 20 times (with m being increased by 5% each time, so that 
m will be double its original value after 20 increases) fails to result in 
a sufficiently small estimate for the number of nodes, then we move on to the 
next value of l in I.  Also, print a message indicating that the refined 
p_l-adic reduction procedure was unsuccesful.
*/
/////
if RunThroughNumber eq 20 then 
fprintf LogFile, "Refined p-adic reduction taking too long. Case iiii = %o, l = %o\n", iiii, l;
continue l;
end if;

else // EnumerationCost(Gammam,UpperBoundForu^2) <= 6000000
flag:=false; //ready to get out of while loop that increases m if necessary
///////////////////////////////////////////////////////////////////////////
/*
Create a process P to enumerate all the vectors u in the lattice Gamma_m with length squared |u|^2 <= D^2 (equivalently length |u| <= D).  

To enumerate the vectors, we will need to repeatedly call NextVector(P).  Calling NextVector(P) will return the next vector found in the enumeration (along with its norm).

IsEmpty(P) returns true if the process P has finished enumerating all the vectors.  It returns false otherwise.
*/
///////////////////////////////////////////////////////////////////////////
P:=ShortVectorsProcess(Gammam,Floor(DDD^2));

///////////////////////////////////////////////////////////////////////////
/*
Enumerate those lattice vectors u with ||u|| <= D, extract 
the corresponding tuples, and test those tuples.

Extracted tuple = (b_{JJJ[2]},...,b_{JJJ[#JJJ]})

bbb[i] = b_{JJJ[i]}, i=1 to #JJJ

Recall: For each ll in I, jl[ll] is the unique index such that JJJ[jl[ll]]=ll+1.
So bbb[jl[ll]] = b_{ll+1} = n_ll
*/
//////////////////////////////////////////////////////////////////////////
bbb:=[RationalField() | ];

ExtractTuplePadicInput:=[*bbb,l,ihat,istar,yyy,zzz,JJJ,nJJJ,nJ,W,B,v*];
TestTuplePadicInput:=[*bbb,l,JJJ,nJJJ,nJ,jl,beta,hh,dd,p,SpecialCase,NewUpperBoundFornl,delta2,LogarithmicAlphap,B,I*];


while not IsEmpty(P) do

uuu:=NextVector(P);

ExtractTuplePadic(~bbb,~ExtractTuplePadicInput,~uuu);

if bbb[1] ne 1 then print("something is wrong!"); bbb[1]; istar[l]; break iiii; end if;

//test the tuple
passes:=true;
TestTuplePadic(~bbb,~TestTuplePadicInput,~passes);


//If the tuple passes all the tests, add it to the list of exceptional tuples
if passes eq true then Remove(~bbb,1); Include(~ExceptionalTuplesInsideLoop, bbb); end if;

//Since the enumeration process only spits out one of u and -u, we now need to do the same thing with -u.

uuu:=-uuu;

ExtractTuplePadic(~bbb,~ExtractTuplePadicInput,~uuu);

if bbb[1] ne 1 then print("something is wrong!"); bbb[1]; istar[l]; break iiii; end if;

//test the tuple
passes:=true;
TestTuplePadic(~bbb,~TestTuplePadicInput,~passes);

//If the tuple passes all the tests, add it to the list of exceptional tuples
if passes eq true then Remove(~bbb,1); Include(~ExceptionalTuplesInsideLoop, bbb); end if;

end while; //enumeration loop

//Enumeration done


Improvement:=true;
UpperBoundForn[l]:=NewUpperBoundFornl;
B[1+l]:=UpperBoundForn[l];

end if; // end of IF controlled by EnumerationCost(Gammam,D^2)


end if; // end of IF controlled by NewUpperBoundFornl ge OldUpperBoundFornl


end while; //this is the loop that increases m if needed

end for; // end l loop

UpperBoundForN:=Max(UpperBoundForn);

//fprintf LogFile, "UpperBoundForn = %o\n", UpperBoundForn;



/////////////////////////////////////////////////////////////////////////////
/*
Refined Real Reduction (Section 21)
*/
/////////////////////////////////////////////////////////////////////////////
for i0:=1 to s do
ConditionalUpperBoundForA[i0]:=UpperBoundForA;
end for;

//RGB
//print("refined real, s=");
//s;

//////////////////////////////////////////////////////////////////////////////
/*
Totally Complex Case, i.e, s=0
*/
//////////////////////////////////////////////////////////////////////////
if s eq 0 then

//Choose c11 to find an choose optimal upper bound for A from Lemma 19.1
MIN:=UpperBoundForA;

c11:=(1/1000000)*c10/(n-1);

c15:=0;
min:=Abs(Imaginary(thetaC[s+1]));
for ii:=2 to t do
j:=s-1 + 2*ii;
if Abs(Imaginary(thetaC[j])) lt min then min:=Abs(Imaginary(thetaC[j])); end if;
end for; //end ii
if Floor(-Log(min)/c11) gt 0 then c15:=Floor(-Log(min)/c11); end if;

max:=Ceiling((c8prime + c9prime*UpperBoundForN)/(c10-(n-1)*c11))-1;
if max lt Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1 then
max:=Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1;
end if;
if max lt c15 then max:=c15; end if; 
//now max is the upper bound for A in Lemma 19.1
if max lt MIN then MIN:=max; end if;

c11:=((1000000 - 1)/1000000)*c10/(n-1);

c15:=0;
min:=Abs(Imaginary(thetaC[s+1]));
for ii:=2 to t do
j:=s-1 + 2*ii;
if Abs(Imaginary(thetaC[j])) lt min then min:=Abs(Imaginary(thetaC[j])); end if;
end for; //end ii
if Floor(-Log(min)/c11) gt 0 then c15:=Floor(-Log(min)/c11); end if;

max:=Ceiling((c8prime + c9prime*UpperBoundForN)/(c10-(n-1)*c11))-1;
if max lt Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1 then
max:=Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1;
end if;
if max lt c15 then max:=c15; end if; 
//now max is the upper bound for A in Lemma 19.1
if max lt MIN then MIN:=max; end if;

for i:=1 to 999 do
c11:=(i/1000)*c10/(n-1);

c15:=0;
min:=Abs(Imaginary(thetaC[s+1]));
for ii:=2 to t do
j:=s-1 + 2*ii;
if Abs(Imaginary(thetaC[j])) lt min then min:=Abs(Imaginary(thetaC[j])); end if;
end for; //end ii
if Floor(-Log(min)/c11) gt 0 then c15:=Floor(-Log(min)/c11); end if;

max:=Ceiling((c8prime + c9prime*UpperBoundForN)/(c10-(n-1)*c11))-1;
if max lt Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1 then
max:=Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1;
end if;
if max lt c15 then max:=c15; end if; 
//now max is the upper bound for A in Lemma 19.1
if max lt MIN then MIN:=max; end if;
end for;  //end i loop

OldUpperBoundForA:=UpperBoundForA;
NewUpperBoundForA:=MIN;

if NewUpperBoundForA lt OldUpperBoundForA then
Improvement:=true;
UpperBoundForA:=NewUpperBoundForA;
end if;

else //s > 0
//////////////////////////////////////////////////////////////////////////////
/*
s>0 Case 
*/
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
/*
Real Case, i.e., s \geq 3
*/
//////////////////////////////////////////////////////////////////////////////
if s ge 3 then // s>=3 real case


JumpToEndOfRealReduction:=false;
for i0:=1 to s do 


//RGB
//print("refined real, s=, i0=");
//s;
//i0;

////////////////////////////////////////////////////////////////////////////
/*
Define 
weights W[i] (Section 21)
R (approximation) (Section 21)
S (Section 21)
CCCCCC = C (Section 21)

Initialize:
TC, where Transpose(TC) = U_C from Section 21
phi[i]:= phi_i from Section 21
*/
////////////////////////////////////////////////////////////////////////////
W:=[];
for i:=1 to 1+v+r do
W[i]:=0; //initialize
end for;

H0prime:=0;
for i:=2 to #JJJ-1 do
if H0prime lt B[JJJ[i]] then H0prime:=B[JJJ[i]]; end if;
end for;

W[1]:=0;
for i:=2 to #JJJ-1 do
W[JJJ[i]]:=RoundP(H0prime/ RNTO(B[JJJ[i]]) );
end for;
for i in J do
W[1+i]:=2*W[i+1];
end for;
//print("weights");
//W;
//print("B");
//B;

R:=0;
for i in JJJ do 
R:=R + B[i];
end for;
R:=(1/2)*R;
//this is just an approximation to R

S:=0;
for i:=2 to #JJJ-1 do
S:=S+(W[JJJ[i]]^2)*(B[JJJ[i]]^2);
end for;

prod:=1;
for i:=2 to #JJJ-1 do
prod:=prod*W[JJJ[i]];
end for;

/*
LogC:= (3/4) * ((#JJJ-1)/2) * Log( 
(R^2 + S) / ( 2^(-(#JJJ-1)) * (Abs(LogarithmicAlphaC[i0][JJJ[#JJJ]])*prod)^(2/(#JJJ-1)) ) 
);
*/

LogC:= Min([
(2/3) * ((#JJJ-1)/2) * Log( 
(R^2 + S) / (  (Abs(LogarithmicAlphaC[i0][JJJ[#JJJ]])*prod)^(2/(#JJJ-1)) ) 
),
(2/3)*UpperBoundForA
]);

//CCCCCC:=Ceiling(Exp(LogC));

TC:=ScalarMatrix(IntegerRing(),#JJJ-1,1); //#JJJ-1 by #JJJ-1 identity matrix

phi:=[];
for i:=1 to 1+v+r do
phi[i]:=0;
end for;

/////////////////////////////////////////////////////////////////////////////
/*
Start the while loop where C will be increased until we find a new conditional upper for A that is smaller than the uncondtional upper bound for A or until a number of increases of C have been made with no success.
*/
////////////////////////////////////////////////////////////////////////////
RunThroughNumber1:=0;
RunThroughNumber2:=0;
flag:=true;
while flag do


//////////////////////////////////////////////////////////////////////////////
/*
Increase CCCCCC = C (if this is not the first attempt the basic real reduction procedure).
*/
//////////////////////////////////////////////////////////////////////////////

CCCCCC:=Ceiling(Exp(LogC + RunThroughNumber1*(5/100)*LogC + RunThroughNumber2*(-25/100)*LogC  ));
/*
print("RunThroughNumber1=");
RunThroughNumber1;
print("RunThroughNumber2=");
RunThroughNumber2;
print("CCCCCC");
CCCCCC;
*/

//////////////////////////////////////////////////////////////////////////////
/*
Calculate the phi_i for i in JJJ.

Calculate R.

DDD = D from Section 21
*/
//////////////////////////////////////////////////////////////////////////////
for i in JJJ do
phi[i]:=Round(CCCCCC*LogarithmicAlphaC[i0][i]);
end for;

/*
if Abs(phi[JJJ[#JJJ]]) lt 2 then
if CCCCCC*LogarithmicAlphaC[i0][JJJ[#JJJ]] ge 0 then 
phi[JJJ[#JJJ]]:=2;
else
phi[JJJ[#JJJ]]:=-2;
end if;
end if;

if IsIntegral(phi[1]/phi[JJJ[#JJJ]]) then
if Abs(phi[1]+1 - CCCCCC*LogarithmicAlphaC[i0][1]) le 1 then
phi[1]:=phi[1]+1;
else
phi[1]:=phi[1]-1;
end if;
end if;
*/

if phi[JJJ[#JJJ]] eq 0 then
if CCCCCC*LogarithmicAlphaC[i0][JJJ[#JJJ]] ge 0 then 
phi[JJJ[#JJJ]]:=1;
else
phi[JJJ[#JJJ]]:=-1;
end if;
end if;


R:=0;
for i in JJJ do 
R:=R + B[i]*Abs( CCCCCC*LogarithmicAlphaC[i0][i] -  phi[i] );
end for;


DDD:=((R+1)^2 + S)^(1/2);


///////////////////////////////////////////////////////////////////////////////
/*
Compute the (soon to be) new i0-conditional upper bound for A. We choose c11 to optimize this bound.

If it is better than the old unconditional upper bound, then we do the enumeration procedure.  If it is not better, then we first retry several times with larger values of C, but if that doesn't work we abandon the refined real reduction procedure (there is no point in moving on to the next i0 in {1,...,s} because the uncondtional upper bound on A will not be improved).
*/
//////////////////////////////////////////////////////////////////////////////
MIN:=UpperBoundForA;

c11:=(1/1000000)*c10/(n-1);
//maxseq:=[
//Ceiling((1/c11)*( Log(2*Log(2)*c16[i0]) + Log(CCCCCC) - Log((DDD^2 - S)^(1/2) - R) ))-1,
//Ceiling((c8prime + c9prime*UpperBoundForN)/(c10 - (n-1)*c11))-1,
//Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10 - c11))-1,
//Ceiling(Log(2*c16[i0])/c11)-1,
//0
//];
max:=Max([
Ceiling((1/c11)*( Log(2*Log(2)*c16[i0]) + Log(CCCCCC) - Log((DDD^2 - S)^(1/2) - R) ))-1,
Ceiling((c8prime + c9prime*UpperBoundForN)/(c10 - (n-1)*c11))-1,
Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10 - c11))-1,
Ceiling(Log(2*c16[i0])/c11)-1,
0
]);
//fprintf LogFile, "Log(CCCCCC) = %o\n", Log(CCCCCC);
//for ijij:=1 to 4 do
//fprintf LogFile, "maxseq[%o] = %o\n", ijij,maxseq[ijij];
//end for;
if max lt MIN then MIN:=max; end if;

c11:=((1000000-1)/1000000)*c10/(n-1);
//maxseq:=[
//Ceiling((1/c11)*( Log(2*Log(2)*c16[i0]) + Log(CCCCCC) - Log((DDD^2 - S)^(1/2) - R) ))-1,
//Ceiling((c8prime + c9prime*UpperBoundForN)/(c10 - (n-1)*c11))-1,
//Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10 - c11))-1,
//Ceiling(Log(2*c16[i0])/c11)-1,
//0
//];
max:=Max([
Ceiling((1/c11)*( Log(2*Log(2)*c16[i0]) + Log(CCCCCC) - Log((DDD^2 - S)^(1/2) - R) ))-1,
Ceiling((c8prime + c9prime*UpperBoundForN)/(c10 - (n-1)*c11))-1,
Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10 - c11))-1,
Ceiling(Log(2*c16[i0])/c11)-1,
0
]);
//fprintf LogFile, "Log(CCCCCC) = %o\n", Log(CCCCCC);
//for ijij:=1 to 4 do
//fprintf LogFile, "maxseq[%o] = %o\n", ijij,maxseq[ijij];
//end for;
if max lt MIN then MIN:=max; end if;

for i:=1 to 999 do
c11:=(i/1000)*c10/(n-1);
//maxseq:=[
//Ceiling((1/c11)*( Log(2*Log(2)*c16[i0]) + Log(CCCCCC) - Log((DDD^2 - S)^(1/2) - R) ))-1,
//Ceiling((c8prime + c9prime*UpperBoundForN)/(c10 - (n-1)*c11))-1,
//Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10 - c11))-1,
//Ceiling(Log(2*c16[i0])/c11)-1,
//0
//];
max:=Max([
Ceiling((1/c11)*( Log(2*Log(2)*c16[i0]) + Log(CCCCCC) - Log((DDD^2 - S)^(1/2) - R) ))-1,
Ceiling((c8prime + c9prime*UpperBoundForN)/(c10 - (n-1)*c11))-1,
Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10 - c11))-1,
Ceiling(Log(2*c16[i0])/c11)-1,
0
]);
//fprintf LogFile, "Log(CCCCCC) = %o\n", Log(CCCCCC);
//fprintf LogFile, "i0 = %o\n", i0;
//for ijij:=1 to 4 do
//fprintf LogFile, "maxseq[%o] = %o\n", ijij,maxseq[ijij];
//end for;
if max lt MIN then MIN:=max; end if;
end for; //end i loop

NewConditionalUpperBoundForAi0:=MIN;
OldUnconditionalUpperBoundForA:=UpperBoundForA;

/*
PrintFile( LogFile, "/////////////////////////////////////////////////////////");
fprintf LogFile, "refined real, s >= 3, RunThroughNumber2 = %o\n", RunThroughNumber2;
fprintf LogFile, "refined real, s >= 3, RunThroughNumber1 = %o\n", RunThroughNumber1;
fprintf LogFile, "Log(CCCCCC) = %o\n", Log(CCCCCC);
fprintf LogFile, "i0 = %o\n", i0;
fprintf LogFile, "NewConditionalUpperBoundForAi0 = %o\n", NewConditionalUpperBoundForAi0;
fprintf LogFile, "OldUnconditionalUpperBoundForA = %o\n", OldUnconditionalUpperBoundForA;
fprintf LogFile, "UpperBoundForN = %o\n", UpperBoundForN;
*/


if NewConditionalUpperBoundForAi0 ge OldUnconditionalUpperBoundForA then 
RunThroughNumber2:=RunThroughNumber2+1; //decrease C and try again
////////
/*
In case we find a new conditional upper bound that fails to improve on 
the current unconditional upper bound for A, we decrease log(C) by 25 percent 
and try again. If this doesn't result in an improved bound, we then we abort 
the real reduction procedure.  There is no need to print a message in this case.
*/
///////
if RunThroughNumber2 eq 2 then 
JumpToEndOfRealReduction:=true;
break i0;
end if;

else //NewConditionalUpperBoundForAi0 lt OldUnconditionalUpperBoundForA


///////////////////////////////////////////////////////////////////////////////
/*
Compute
AC = A_C
*/
//////////////////////////////////////////////////////////////////////////////
AC:=ZeroMatrix(IntegerRing(),v+r+1,v+r+1);

for i:=1 to v+r do
AC[i][i]:=W[i];
end for;
for j:=1 to v+r+1 do
AC[v+r+1][j]:=phi[j];
end for;

for i:=1+v+r to 2 by -1 do
if not i in JJJ then
RemoveColumn(~AC,i);
RemoveRow(~AC,i);
end if;
end for;

RemoveRow(~AC,1);
RemoveColumn(~AC,1);

//AC is now a #JJJ-1 by #JJJ-1 matrix

AC:=AC*Transpose(TC);
/* If this is the first run through Transpose(TC) is the identity. Otherwise Transpose(TC) is UC.  This will save time in the LLL reduction. */

///////////////////////////////////////////////////////////////////////////////
/*
Compute an LLL reduced basis for the lattice Gamma_C generated by columns of A_C.  The algoritm used is de Weger's exact integer version of LLL.

Note: LLL(X) assumes ROWS of X span the lattice, so we need to feed it the transpose of A_C.  Similarly, it spits out the transpose of B_C and the transpose of U_C
*/
///////////////////////////////////////////////////////////////////////////////
//time 
temp,TC,rank:=LLL(Transpose(AC) : Proof:=true, Method:="Integral", Delta:=0.75, Eta:=0.5 );

BC:=MatrixRing(RationalField(),#JJJ-1) ! Transpose(temp); 
//columns are LLL-reduced basis for Gamma_C

/*
Here TC*Transpose(AC) = Transpose(BC). 
So with UC=Transpose(TC) we have AC*UC = BC,
and With 
VC = BC*Transpose(TC)*BC^(-1) = AC*Transpose(TC)*AC^(-1), we have VC*AC = BC.
*/

///////////////////////////////////////////////////////////////////////////////
/*
Define:
yyy = \vec{y} from Section 21
sss = \vec{s} from Section 21
ttt = \vec{t} from Section 21
zzz = \vec{z} from Section 21
*/
///////////////////////////////////////////////////////////////////////////////
yyy:=ZeroMatrix(RationalField(),1+v+r,1);
for i:=1 to v do
yyy[1+i][1]:=(1/2)*W[1+i]*B[1+i];
end for;
for i:=1+v+r to 2 by -1 do
if not i in JJJ then
RemoveRow(~yyy,i);
end if;
end for;
RemoveRow(~yyy,1);
//yyy is now a #JJJ-1 by 1 column vector
yyy[#JJJ-1][1]:=-phi[1];

sss:=(BC^(-1))*yyy;

ttt:=sss;
for i:=1 to #JJJ-1 do
ttt[i][1]:=Floor(sss[i][1]);
end for;
Floorsss:=ttt;
potentialttt:=ttt;
min:=LengthOfVector(BC*ttt - yyy);

mm:=#JJJ-1;
yyytttpotentialtttFloorsss:=[yyy,ttt,potentialttt,Floorsss];
//Type(yyytttpotentialtttFloorsss);
Choosettt(~yyytttpotentialtttFloorsss,~min,~BC,~mm,1);

zzz:=BC*ttt;

/*Now zzz is likely the closest vector in the lattice Gamma_C to yyy and 
min = |zzz-yyy|*/


////////////////////////////////////////////////////////////////////////
/*
Construct the lattice Gamma_C.  The MAGMA function Lattice() assumes

Use the function EnumerationCost to compute an estimate the number of 
nodes in the tree to be visited during the execution of the algorithm 
that will enumerate all lattice vectors u with |u| \leq D + |y-z|.  The 
number of nodes is essentially directly proportional to the time needed 
for the enumeration.

If the number of nodes is too large for the enumration to be done in a 
reasonable amount of time, we increase C and try the reduction procedure 
again.  If several increases of C fail to result in a small enough 
estimate for the number of nodes, then we abort the refined real reduction 
(there is no point in moving on to the next i0 in {1,...,s} because the 
uncondtional upper bound on A will not be improved).

In Stehle and Watkins (2006), it is asserted that MAGMA's enumeration 
algorithm has a traversal rate of about 7.5 millon nodes per second.  
Based on the examples in the MAGMA Handbook, the rate is appears to be 
20 to 40 millon nodes per second. We will assume a traversal rate of 10 
millon nodes per second.  Assuming we want the enumeration to take less 
than 10 minutes, we want to abort if the estimated number of nodes is 
> 10*60*10^7 = 6000000000

The enumeration algorithm may be fast, but the extraction and testing of the 
tuples can take time. So we abort if the estimated number of nodes is 
> 10*60*10^4

Note: To MAGMA, Norm(v) = |v|^2.
*/
////////////////////////////////////////////////////////////////////////

GammaC:=Lattice(Transpose(BC));

fprintf LogFile, "s = %o, i0 = %o, RunThroughNumber1 = %o, enumcost = %o\n", s, i0, RunThroughNumber1, EnumerationCost(GammaC,RealField() ! (DDD+min)^2);


if EnumerationCost(GammaC,RealField() ! (DDD+min)^2) gt 6000000 then

RunThroughNumber1+:=1;  //increase C and try again
/////
/*
If increasing log(C) 20 times (with log(C) being increased 5% each time, so that log(C) will be double its original value) fails to produce a new conditional upper bound for A, then we abort the real reduction procedure.  Also, print a message to the user indicating the refined real reduction procedure was unsuccesful for this reason.
*/
////
if RunThroughNumber1 eq 20 then 
fprintf LogFile, "Refined real reduction taking too long. Case iiii = %o, i0 = %o\n", iiii, i0;
JumpToEndOfRealReduction:=true;
break i0;
end if;

else // EnumerationCost(GammaC,(DDD+min)^2) <= 6000000
flag:=false; //ready to get out of while loop that increases C if necessary
///////////////////////////////////////////////////////////////////////////
/*
Create a process P to enumerate all the vectors u in the lattice Gamma_C with lenght squared |u|^2 <= (D+|y-z|)^2 (equivalently length |u| <= D+|y-z|).

To enumerate the vectors, we will need to repeatedly call NextVector(P).  Callign NextVector(P) will return the next vector found in the enumeration (along with its norm).

IsEmpty(P) returns true if the process P has finished enumerating all the vectors.  It returns false otherwise.
*/
//////////////////////////////////////////////////////////////////////////
P:=ShortVectorsProcess(GammaC,Floor((DDD+min)^2));

/////////////////////////////////////////////////////////////////////////
/*
Enumerate those lattice vectors u with |u| <= D+|y-z|, extract 
the corresponding tuples, and test those tuples.

Extracted tuple = (b_{JJJ[2]},...,b_{JJJ[#JJJ]})

bbb[i] = b_{JJJ[i]}, i=1 to #JJJ
*/
////////////////////////////////////////////////////////////////////////
bbb:=[RationalField() | ];

ExtractTupleRealCaseInput:=[*bbb,yyy,zzz,JJJ,nJJJ,nJ,W,B,phi*];
TestTupleRealCaseInput:=[*bbb,JJJ,nJJJ,nJ,NewConditionalUpperBoundForAi0,jl,SpecialCase,p,delta2,hh,dd,B,I,beta*];

while not IsEmpty(P) do

uuu:=NextVector(P);

//Extract tuple (b_{JJJ[2]},...,b_{JJJ[#JJJ]})
ExtractTupleRealCase(~bbb,~ExtractTupleRealCaseInput,~uuu);

//Test the tuple
passes:=true;
TestTupleRealCase(~bbb,~TestTupleRealCaseInput,~passes);

/*If the tuple passes all the tests, add it to the list of exceptional tuples*/
if passes eq true then Remove(~bbb,1); Include(~ExceptionalTuplesInsideLoop, bbb); end if;


/*Since the enumeration process only spits out one of u and -u, we now need to do the same thing with -u.*/

uuu:=-uuu;

//Extract tuple (b_{JJJ[2]},...,b_{JJJ[#JJJ]})
ExtractTupleRealCase(~bbb,~ExtractTupleRealCaseInput,~uuu);

//Test the tuple
passes:=true;
TestTupleRealCase(~bbb,~TestTupleRealCaseInput,~passes);

/*If the tuple passes all the tests, add it to the list of exceptional tuples*/
if passes eq true then Remove(~bbb,1); Include(~ExceptionalTuplesInsideLoop, bbb); end if;

end while; //enumeration loop

//Enumeration done

ConditionalUpperBoundForA[i0]:=NewConditionalUpperBoundForAi0;


end if; //end of IF controlled by EnumerationCost(GammaC,(DDD+min)^2)

end if; /* end of IF controlled by NewConditionalUpperBoundForAi0 ge OldUnconditionalUpperBoundForA */

end while; /* this is the while loop that increases log(C) if necessary, the while loop controlled by flag */


end for; //end i0 loop


if JumpToEndOfRealReduction eq false then
/////////////
/* 
Choose c11 to find an optimal i0-conditional upper bound for A for i0 in {s+1,...,s+2t} from Lemma 19.1 
*/
///////////
MIN:=UpperBoundForA;

c11:=(1/1000000)*c10/(n-1);

c15:=0;
if t gt 0 then
min:=Abs(Imaginary(thetaC[s+1]));
for ii:=2 to t do
j:=s-1 + 2*ii;
if Abs(Imaginary(thetaC[j])) lt min then min:=Abs(Imaginary(thetaC[j])); end if;
end for; //end ii
if Floor(-Log(min)/c11) gt 0 then c15:=Floor(-Log(min)/c11); end if;
end if;

max:=Ceiling((c8prime + c9prime*UpperBoundForN)/(c10-(n-1)*c11))-1;
if max lt Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1 then
max:=Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1;
end if;
if max lt c15 then max:=c15; end if; 
//now max is the upper bound for A in Lemma 19.1
if max lt MIN then MIN:=max; end if;

c11:=((1000000 - 1)/1000000)*c10/(n-1);

c15:=0;
if t gt 0 then
min:=Abs(Imaginary(thetaC[s+1]));
for ii:=2 to t do
j:=s-1 + 2*ii;
if Abs(Imaginary(thetaC[j])) lt min then min:=Abs(Imaginary(thetaC[j])); end if;
end for; //end ii
if Floor(-Log(min)/c11) gt 0 then c15:=Floor(-Log(min)/c11); end if;
end if;

max:=Ceiling((c8prime + c9prime*UpperBoundForN)/(c10-(n-1)*c11))-1;
if max lt Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1 then
max:=Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1;
end if;
if max lt c15 then max:=c15; end if; 
//now max is the upper bound for A in Lemma 19.1
if max lt MIN then MIN:=max; end if;

for i:=1 to 999 do
c11:=(i/1000)*c10/(n-1);

c15:=0;
if t gt 0 then
min:=Abs(Imaginary(thetaC[s+1]));
for ii:=2 to t do
j:=s-1 + 2*ii;
if Abs(Imaginary(thetaC[j])) lt min then min:=Abs(Imaginary(thetaC[j])); end if;
end for; //end ii
if Floor(-Log(min)/c11) gt 0 then c15:=Floor(-Log(min)/c11); end if;
end if;

max:=Ceiling((c8prime + c9prime*UpperBoundForN)/(c10-(n-1)*c11))-1;
if max lt Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1 then
max:=Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1;
end if;
if max lt c15 then max:=c15; end if; 
//now max is the upper bound for A in Lemma 19.1
if max lt MIN then MIN:=max; end if;
end for;  //end i loop

/////
/*
Compute the new unconditional bound for A
*/
/////

OldUpperBoundForA:=UpperBoundForA;
NewUpperBoundForA:=Max([Max(ConditionalUpperBoundForA),MIN]);

if NewUpperBoundForA lt OldUpperBoundForA then
Improvement:=true;
UpperBoundForA:=NewUpperBoundForA;
for i:=1 to r do
B[1+v+i]:=UpperBoundForA;
end for;
end if;

end if; //controlled by JumpToEndOfRealReduction

if UpperBoundForA lt 0 then 
//there are no solutions to the current case of (11)
fprintf LogFile, "UpperBoundForA lt 0. No solutions possible in case iiii = %o\n", iiii;
continue iiii;
end if;



//////////////////////////////////////////////////////////////////////////////
/*
Complex Case, i.e., s = 1,2
*/
//////////////////////////////////////////////////////////////////////////////
else //s=1,2 complex case

B[2+v+r]:=Floor(2*Arcsin(1/4)/PI);
for i in JJJ do
B[2+v+r]:=B[2+v+r] + B[i];
end for;


JumpToEndOfRealReduction:=false;
for i0:=1 to s do 


////////////////////////////////////////////////////////////////////////////
/*
Define 
weights W[i] (Section 21)
R (approximation) (Section 21)
S (Section 21)
CCCCCC = C (Section 21)

Initialize:
TC, where Transpose(TC) = U_C from Section 21
phi[i]:= phi_i from Section 21
*/
////////////////////////////////////////////////////////////////////////////
W:=[];
for i:=1 to 1+v+r do
W[i]:=0; //initialize
end for;

H0prime:=0;
for i:=2 to #JJJ do
if H0prime lt B[JJJ[i]] then H0prime:=B[JJJ[i]]; end if;
end for;

W[1]:=0;
for i:=2 to #JJJ do
W[JJJ[i]]:=RoundP(H0prime/ RNTO(B[JJJ[i]]) );
end for;
for i in J do
W[1+i]:=2*W[i+1];
end for;

R:=B[2+v+r];
for i in JJJ do 
R:=R + B[i];
end for;
R:=(1/2)*R;
//this is just an approximation to R

S:=0;
for i:=2 to #JJJ do
S:=S+(W[JJJ[i]]^2)*(B[JJJ[i]]^2);
end for;

prod:=1;
for i:=2 to #JJJ do
prod:=prod*W[JJJ[i]];
end for;

/*
LogC:= (3/4) * ((#JJJ)/2) * Log( 
(R^2 + S) / ( 2^(-(#JJJ)) * (Abs(LogarithmicAlphaC[i0][2+v+r])*prod)^(2/(#JJJ)) ) 
);
*/

LogC:= Min([
(2/3) * ((#JJJ)/2) * Log( 
(R^2 + S) / ( (Abs(LogarithmicAlphaC[i0][2+v+r])*prod)^(2/(#JJJ)) ) 
),
(2/3)*UpperBoundForA
]);

//CCCCCC:=Ceiling(Exp(LogC));

TC:=ScalarMatrix(IntegerRing(),#JJJ,1); //#JJJ by #JJJ identity matrix

phi:=[];
for i:=1 to 2+v+r do
phi[i]:=0;
end for;

/////////////////////////////////////////////////////////////////////////////
/*
Start the while loop where C will be increased until we find a new conditional upper for A that is smaller than the uncondtional upper bound for A or until a number of increases of C have been made with no success.
*/
////////////////////////////////////////////////////////////////////////////
RunThroughNumber1:=0;
RunThroughNumber2:=0;
flag:=true;
while flag do

//////////////////////////////////////////////////////////////////////////////
/*
Increase CCCCCC = C (if this is not the first attempt the basic real reduction procedure).
*/
//////////////////////////////////////////////////////////////////////////////

CCCCCC:=Ceiling(Exp(LogC + RunThroughNumber1*(5/100)*LogC + RunThroughNumber2*(-25/100)*LogC ));


//////////////////////////////////////////////////////////////////////////////
/*
Calculate the phi_i for i in JJJ.

Calculate R.

DDD = D from Section 21
*/
//////////////////////////////////////////////////////////////////////////////
for i in JJJ do
phi[i]:=Round(CCCCCC*LogarithmicAlphaC[i0][i]);
end for;
phi[2+v+r]:=Round(CCCCCC*LogarithmicAlphaC[i0][2+v+r]);

/*This will never happen because LogarithmicAlphaC[i0][2+v+r] = Pi */
/*
if Abs(phi[2+v+r]) lt 2 then 
if CCCCCC*LogarithmicAlphaC[i0][2+v+r] ge 0 then 
phi[#JJJ]:=2;
else
phi[#JJJ]:=-2;
end if;
end if;

if IsIntegral(phi[1]/phi[2+v+r]) then
if Abs(phi[1]+1 - CCCCCC*LogarithmicAlphaC[i0][1]) le 1 then
phi[1]:=phi[1]+1;
else
phi[1]:=phi[1]-1;
end if;
end if;
*/


R:=B[2+v+r]*Abs( CCCCCC*LogarithmicAlphaC[i0][2+v+r] -  phi[2+v+r] );
for i in JJJ do 
R:=R + B[i]*Abs( CCCCCC*LogarithmicAlphaC[i0][i] -  phi[i] );
end for;

DDD:=((R+1)^2 + S)^(1/2);

///////////////////////////////////////////////////////////////////////////////
/*
Compute the (soon to be) new i0-conditional upper bound for A. We choose c11 to optimize this bound.

If it is better than the old unconditional upper bound, then we do the enumeration procedure.  If it is not better, then we first retry several times with larger values of C, but if that doesn't work we abandon the refined real reduction procedure (there is no point in moving on to the next i0 in {1,...,s} because the uncondtional upper bound on A will not be improved).
*/
//////////////////////////////////////////////////////////////////////////////
MIN:=UpperBoundForA;

c11:=(1/1000000)*c10/(n-1);
max:=Max([
Ceiling((1/c11)*( Log(4*Arcsin(1/4)*c16[i0]) + Log(CCCCCC) - Log((DDD^2 - S)^(1/2) - R) ))-1,
Ceiling((c8prime + c9prime*UpperBoundForN)/(c10 - (n-1)*c11))-1,
Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10 - c11))-1,
Ceiling(Log(2*c16[i0])/c11)-1,
0
]);
if max lt MIN then MIN:=max; end if;

c11:=((1000000-1)/1000000)*c10/(n-1);
max:=Max([
Ceiling((1/c11)*( Log(4*Arcsin(1/4)*c16[i0]) + Log(CCCCCC) - Log((DDD^2 - S)^(1/2) - R) ))-1,
Ceiling((c8prime + c9prime*UpperBoundForN)/(c10 - (n-1)*c11))-1,
Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10 - c11))-1,
Ceiling(Log(2*c16[i0])/c11)-1,
0
]);
if max lt MIN then MIN:=max; end if;

for i:=1 to 999 do
c11:=(i/1000)*c10/(n-1);
max:=Max([
Ceiling((1/c11)*( Log(4*Arcsin(1/4)*c16[i0]) + Log(CCCCCC) 
- Log((DDD^2 - S)^(1/2) - R) ))-1,
Ceiling((c8prime + c9prime*UpperBoundForN)/(c10 - (n-1)*c11))-1,
Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10 - c11))-1,
Ceiling(Log(2*c16[i0])/c11)-1,
0
]);
if max lt MIN then MIN:=max; end if;
end for; //end i loop

NewConditionalUpperBoundForAi0:=MIN;
OldUnconditionalUpperBoundForA:=UpperBoundForA;

if NewConditionalUpperBoundForAi0 ge OldUnconditionalUpperBoundForA then 
RunThroughNumber2:=RunThroughNumber2+1; //increase C and try again
////////
/*
In case we find a new conditional upper bound that fails to improve on 
the current unconditional upper bound for A, we decrease log(C) by 25 percent 
and try again. If this doesn't result in an improved bound, we then we abort 
the real reduction procedure.  There is no need to print a message in this case.
*/
///////
if RunThroughNumber2 eq 2 then 
JumpToEndOfRealReduction:=true;
fprintf LogFile, "refined real, s < 3, RunThroughNumber2 = %o\n", RunThroughNumber2;
fprintf LogFile, "NewConditionalUpperBoundForAi0 = %o\n", NewConditionalUpperBoundForAi0;
fprintf LogFile, "OldUnconditionalUpperBoundForA = %o\n", OldUnconditionalUpperBoundForA;
fprintf LogFile, "Log(CCCCCC) = %o\n", Log(CCCCCC);
fprintf LogFile, "UpperBoundForN = %o\n", UpperBoundForN;
break i0;
end if;

else //NewConditionalUpperBoundForAi0 lt OldUnconditionalUpperBoundForA



///////////////////////////////////////////////////////////////////////////////
/*
Compute
AC = A_C
*/
//////////////////////////////////////////////////////////////////////////////
AC:=ZeroMatrix(IntegerRing(),v+r+2,v+r+2);

for i:=1 to 1+v+r do
AC[i][i]:=W[i];
end for;
for j:=1 to v+r+2 do
AC[v+r+2][j]:=phi[j];
end for;

for i:=1+v+r to 2 by -1 do
if not i in JJJ then
RemoveColumn(~AC,i);
RemoveRow(~AC,i);
end if;
end for;

RemoveRow(~AC,1);
RemoveColumn(~AC,1);

//AC is now a #JJJ by #JJJ matrix

AC:=AC*Transpose(TC);
/* If this is the first run through Transpose(TC) is the identity. Otherwise Transpose(TC) is UC.  This will time in the LLL reduction. */

///////////////////////////////////////////////////////////////////////////////
/*
Compute an LLL reduced basis for the lattice Gamma_C generated by columns of A_C.  The algoritm used is de Weger's exact integer version of LLL.

Note: LLL(X) assumes ROWS of X span the lattice, so we need to feed it the transpose of A_C.  Similarly, it spits out the transpose of B_C and the transpose of U_C
*/
///////////////////////////////////////////////////////////////////////////////
//time 
temp,TC,rank:=LLL(Transpose(AC) : Proof:=true, Method:="Integral", Delta:=0.75, Eta:=0.5 );

BC:=MatrixRing(RationalField(),#JJJ) ! Transpose(temp); 
//columns are LLL-reduced basis for Gamma_C

/*
Here TC*Transpose(AC) = Transpose(BC). 
So with UC=Transpose(TC) we have AC*UC = BC,
and With 
VC = BC*Transpose(TC)*BC^(-1) = AC*Transpose(TC)*AC^(-1), we have VC*AC = BC.
*/

///////////////////////////////////////////////////////////////////////////////
/*
Define:
yyy = \vec{y} from Section 21
sss = \vec{s} from Section 21
ttt = \vec{t} from Section 21
zzz = \vec{z} from Section 21
*/
///////////////////////////////////////////////////////////////////////////////
yyy:=ZeroMatrix(RationalField(),2+v+r,1);
for i:=1 to v do
yyy[1+i][1]:=(1/2)*W[1+i]*B[1+i];
end for;
for i:=1+v+r to 2 by -1 do
if not i in JJJ then
RemoveRow(~yyy,i);
end if;
end for;
RemoveRow(~yyy,1);
//yyy is now a #JJJ by 1 column vector
yyy[#JJJ][1]:=-phi[1];

sss:=(BC^(-1))*yyy;

ttt:=sss;
for i:=1 to #JJJ do
ttt[i][1]:=Floor(sss[i][1]);
end for;
Floorsss:=ttt;
potentialttt:=ttt;
min:=LengthOfVector(BC*ttt - yyy);

mm:=#JJJ;
yyytttpotentialtttFloorsss:=[yyy,ttt,potentialttt,Floorsss];
//Type(yyytttpotentialtttFloorsss);
Choosettt(~yyytttpotentialtttFloorsss,~min,~BC,~mm,1);

zzz:=BC*ttt;

/*Now zzz is likely the closest vector in the lattice Gamma_C to yyy and 
min = |zzz-yyy|*/


////////////////////////////////////////////////////////////////////////
/*
Construct the lattice Gamma_C.  The MAGMA function Lattice() assumes

Use the function EnumerationCost to compute an estimate the number of 
nodes in the tree to be visited during the execution of the algorithm 
that will enumerate all lattice vectors u with |u| \leq D + |y-z|.  The 
number of nodes is essentially directly proportional to the time needed 
for the enumeration.

If the number of nodes is too large for the enumration to be done in a 
reasonable amount of time, we increase C and try the reduction procedure 
again.  If several increases of C fail to result in a small enough 
estimate for the number of nodes, then we abort the refined real 
reduction (there is no point in moving on to the next i0 in {1,...,s} 
because the uncondtional upper bound on A will not be improved).

In Stehle and Watkins (2006), it is asserted that MAGMA's enumeration 
algorithm has a traversal rate of about 7.5 millon nodes per second.  
Based on the examples in the MAGMA Handbook, the rate is appears to be 
20 to 40 millon nodes per second. We will assume a traversal rate of 10 
millon nodes per second.  Assuming we want the enumeration to take less 
than 10 minutes, we want to abort if the estimated number of nodes is 
> 10*60*10^7 = 6000000000

The enumeration algorithm may be fast, but the extraction and testing of 
the tuples can take time. So we abort if the estimated number of nodes is 
> 10*60*10^4

Note: To MAGMA, Norm(v) = |v|^2.
*/
////////////////////////////////////////////////////////////////////////

GammaC:=Lattice(Transpose(BC));

fprintf LogFile, "s = %o, i0 = %o, RunThroughNumber1 = %o, enumcost = %o\n", s, i0, RunThroughNumber1, EnumerationCost(GammaC,RealField() ! (DDD+min)^2);

if EnumerationCost(GammaC,RealField() ! (DDD+min)^2) gt 6000000 then

RunThroughNumber1+:=1;  //increase C and try again
/////
/*
If increasing log(C) 20 times (with log(C) being increased 5% each time, so that log(C) will be double its original value) fails to produce a new conditional upper bound for A, then we abort the real reduction procedure.  Also, print a message to the user indicating the refined real reduction procedure was unsuccesful for this reason.
*/
////
if RunThroughNumber1 eq 20 then 
fprintf LogFile, "Refined real reduction taking too long. Case iiii = %o, i0 = %o\n", iiii, i0;
JumpToEndOfRealReduction:=true;
break i0;
end if;

else // EnumerationCost(GammaC,(DDD + min)^2) <= 6000000
flag:=false; //ready to get out of while loop that increases C if necessary
///////////////////////////////////////////////////////////////////////////
/*
Create a process P to enumerate all the vectors u in the lattice Gamma_C with lenght squared |u|^2 <= (D+|y-z|)^2 (equivalently length |u| <= D+|y-z|).

To enumerate the vectors, we will need to repeatedly call NextVector(P).  Callign NextVector(P) will return the next vector found in the enumeration (along with its norm).

IsEmpty(P) returns true if the process P has finished enumerating all the vectors.  It returns false otherwise.
*/
//////////////////////////////////////////////////////////////////////////
P:=ShortVectorsProcess(GammaC,Floor((DDD+min)^2));

/////////////////////////////////////////////////////////////////////////
/*
Enumerate those lattice vectors u with |u| <= D+|y-z|, extract 
the corresponding tuples, and test those tuples.

Extracted tuple = (b_{JJJ[2]},...,b_{JJJ[#JJJ]},b_{2+v+r})

bbb[i] = b_{JJJ[i]}, i=1 to #JJJ
bbb[#JJJ+1] = b_{2+v+r}
*/
////////////////////////////////////////////////////////////////////////
bbb:=[RationalField() | ];
bbb[1]:=1;

ExtractTupleComplexCaseInput:=[*bbb,yyy,zzz,JJJ,nJJJ,nJ,W,B,phi,2+v+r*];
TestTupleComplexCaseInput:=[*bbb,JJJ,nJJJ,nJ,NewConditionalUpperBoundForAi0,jl,SpecialCase,p,delta2,hh,dd,B,2+v+r,I,beta*];

while not IsEmpty(P) do

uuu:=NextVector(P);

//Extract tuple (b_{JJJ[2]},...,b_{JJJ[#JJJ]},b_{2+v+r})
ExtractTupleComplexCase(~bbb,~ExtractTupleComplexCaseInput,~uuu);

//Test the tuple
passes:=true;
TestTupleComplexCase(~bbb,~TestTupleComplexCaseInput,~passes);


/*If the tuple passes all the tests, add it to the list of exceptional tuples*/
if passes eq true then Remove(~bbb,nJJJ+1); Remove(~bbb,1); Include(~ExceptionalTuplesInsideLoop, bbb); end if;

//

/*Since the enumeration process only spits out one of u and -u, we now need to do the same thing with -u.*/

uuu:=-uuu;

//Extract tuple (b_{JJJ[2]},...,b_{JJJ[#JJJ]},b_{2+v+r})
ExtractTupleComplexCase(~bbb,~ExtractTupleComplexCaseInput,~uuu);

//Test the tuple
passes:=true;
TestTupleComplexCase(~bbb,~TestTupleComplexCaseInput,~passes);

/*If the tuple passes all the tests, add it to the list of exceptional tuples*/
if passes eq true then Remove(~bbb,nJJJ+1); Remove(~bbb,1); Include(~ExceptionalTuplesInsideLoop, bbb); end if;


end while; //enumeration loop

//Enumeration done

ConditionalUpperBoundForA[i0]:=NewConditionalUpperBoundForAi0;

end if; //end of IF controlled by EnumerationCost(GammaC,(DDD+min)^2)

end if; /* end of IF controlled by NewConditionalUpperBoundForAi0 ge OldUnconditionalUpperBoundForA */

end while; /* this is the while loop that increases log(C) if necessary, the while loop controlled by flag */


end for; //end i0 loop

if JumpToEndOfRealReduction eq false then
/////////////
/* 
Choose c11 to find an optimal i0-conditional upper bound for A for i0 in {s+1,...,s+2t} from Lemma 19.1 
*/
///////////
MIN:=UpperBoundForA;

c11:=(1/1000000)*c10/(n-1);

c15:=0;
if t gt 0 then
min:=Abs(Imaginary(thetaC[s+1]));
for ii:=2 to t do
j:=s-1 + 2*ii;
if Abs(Imaginary(thetaC[j])) lt min then min:=Abs(Imaginary(thetaC[j])); end if;
end for; //end ii
if Floor(-Log(min)/c11) gt 0 then c15:=Floor(-Log(min)/c11); end if;
end if;

max:=Ceiling((c8prime + c9prime*UpperBoundForN)/(c10-(n-1)*c11))-1;
if max lt Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1 then
max:=Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1;
end if;
if max lt c15 then max:=c15; end if; 
//now max is the upper bound for A in Lemma 19.1
if max lt MIN then MIN:=max; end if;

c11:=((1000000 - 1)/1000000)*c10/(n-1);

c15:=0;
if t gt 0 then
min:=Abs(Imaginary(thetaC[s+1]));
for ii:=2 to t do
j:=s-1 + 2*ii;
if Abs(Imaginary(thetaC[j])) lt min then min:=Abs(Imaginary(thetaC[j])); end if;
end for; //end ii
if Floor(-Log(min)/c11) gt 0 then c15:=Floor(-Log(min)/c11); end if;
end if;

max:=Ceiling((c8prime + c9prime*UpperBoundForN)/(c10-(n-1)*c11))-1;
if max lt Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1 then
max:=Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1;
end if;
if max lt c15 then max:=c15; end if; 
//now max is the upper bound for A in Lemma 19.1
if max lt MIN then MIN:=max; end if;

for i:=1 to 999 do
c11:=(i/1000)*c10/(n-1);

c15:=0;
if t gt 0 then
min:=Abs(Imaginary(thetaC[s+1]));
for ii:=2 to t do
j:=s-1 + 2*ii;
if Abs(Imaginary(thetaC[j])) lt min then min:=Abs(Imaginary(thetaC[j])); end if;
end for; //end ii
if Floor(-Log(min)/c11) gt 0 then c15:=Floor(-Log(min)/c11); end if;
end if;

max:=Ceiling((c8prime + c9prime*UpperBoundForN)/(c10-(n-1)*c11))-1;
if max lt Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1 then
max:=Ceiling((c8primeprime + c9primeprime*UpperBoundForN)/(c10-c11))-1;
end if;
if max lt c15 then max:=c15; end if; 
//now max is the upper bound for A in Lemma 19.1
if max lt MIN then MIN:=max; end if;
end for;  //end i loop

//MIN is now an i0-conditional upper bound for A for i0 in {s+1,...,s+2t}

/////
/*
Compute the new unconditional bound for A
*/
/////

OldUpperBoundForA:=UpperBoundForA;
NewUpperBoundForA:=Max([Max(ConditionalUpperBoundForA),MIN]);

if NewUpperBoundForA lt OldUpperBoundForA then
Improvement:=true;
UpperBoundForA:=NewUpperBoundForA;
for i:=1 to r do
B[1+v+i]:=UpperBoundForA;
end for;
end if;

end if; //controlled by JumpToEndOfRealReduction

if UpperBoundForA lt 0 then 
//there are no solutions to the current case of (11)
fprintf LogFile, "UpperBoundForA lt 0. No solutions possible in case iiii = %o\n", iiii;
continue iiii;
end if;



end if; //end of IF for distinguishing (s>=3) (s=1,2) cases

end if; //end of IF for s=0, s>=3, s=1or2 cases    

//done finding new upper bound for A

UpperBoundForH:=Max([UpperBoundForN, UpperBoundForA]);
/*
RGB
print("Upper bounds for the n_l and A, respectively:");
UpperBoundForn;
Floor(UpperBoundForA);
*/

for tup in ExceptionalTuplesInsideLoop do
Include(~ExceptionalTuples,tup);
end for;

end while;  //end loop for repeated refined reductions (the improvement loop)

//////////////////////////////////////////////////////////////////////////////
/*
End Of Loop For Repeated Refined Reductions (the improvement loop)
*/
//////////////////////////////////////////////////////////////////////////////


else  //FindAll eq false
ExceptionalTuples:=[];
for j:=0 to 29 do

minpJ:=Max(p);
for i in J do
if p[i] lt minpJ then minpJ:=p[i]; end if;
end for;
for i in J do
UpperBoundForn[i]:=Ceiling( (30-j)*Log(minpJ)/Log(p[i]) );
end for;
UpperBoundForA:=Ceiling( Max(UpperBoundForn)*(130/100) );

NumberOfTuplesToCheck:=1;
for i in J do 
NumberOfTuplesToCheck := NumberOfTuplesToCheck * (UpperBoundForn[i] + 1);
end for;
NumberOfTuplesToCheck := NumberOfTuplesToCheck * (2*UpperBoundForA + 1)^r;

if NumberOfTuplesToCheck lt 10000000000 then 
fprintf LogFile, "Log(NumberOfTuplesToCheck)/Log(10) = %o\n", Log(NumberOfTuplesToCheck)/Log(10); 
break j; 
end if;

end for;

end if;  //controlled by FindAll


/////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////
///////////////////////
/*
Final Sieve (Section 22)
*/
///////////////////////
/////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////////
/*
Compute
NumberOfTuplesToCheck = the number of tuples to sieve through (excluding the [small number of] exceptional tuples)

Select rational primes q_1,...q_k such that each q_i has at least three prime ideal factors in O_K that have residue degree one and such that the product 
q_1 ... q_k is > NumberOfTuplesToCheck

For each q=q_h, pick three residue degree 1 prime ideal factors of q in O_K: qq_1, qq_2, qq_3.  For each  qq_i, we compute the integers m_i, A_i, P_ij, E_ij from Section 22.  Actually, we compute these not as integers but as elements in the finite field Z/qZ.  We store these elements in the sequence
Q[h][i]=[P_i1, ..., P_iv, E_i1, ..., E_ir, A_i, m_i]
Q[h][i]=[P_{i,JJJ[2]-1}, ..., P_{i,JJJ[1+#J]-1}, E_i1, ..., E_ir, A_i, m_i]
       =[P_{i,J[1]}, ..., P_{i,J[#J]}, E_i1, ..., E_ir, A_i, m_i]

We don't store the primes q_1,...,q_k or their prime ideal factors.


*/
/////////////////////////////////////////////////////////////////////////////
NumberOfTuplesToCheck:=1;
for i in J do 
NumberOfTuplesToCheck := NumberOfTuplesToCheck * (UpperBoundForn[i] + 1);
end for;
NumberOfTuplesToCheck := NumberOfTuplesToCheck * (2*UpperBoundForA + 1)^r;



if NumberOfTuplesToCheck gt 10000000000 then //10^10
print "There are too many tuples to check.";
printf "NumberOfTuplesToCheck = %o\n", NumberOfTuplesToCheck;
printf "UpperBoundForn = %o\n", UpperBoundForn;
printf "UpperBoundForA = %o\n", UpperBoundForA;
PrintFile(LogFile, "There are too many tuples to check.");
fprintf LogFile, "NumberOfTuplesToCheck = %o\n", NumberOfTuplesToCheck;
fprintf LogFile, "UpperBoundForn = %o\n", UpperBoundForn;
fprintf LogFile, "UpperBoundForA = %o\n", UpperBoundForA;
return [];
end if;

ProductOfAllqSelected:=1;
Q:=[**];
hhh:=0;

j:=0;
while ProductOfAllqSelected le NumberOfTuplesToCheck do

ListOfPrimesInInterval:=PrimesInInterval(150*j+1,150*(j+1));

for i:=#ListOfPrimesInInterval to 1 by -1 do
if ProductOfAllqSelected gt NumberOfTuplesToCheck then break i; end if;
q:=ListOfPrimesInInterval[i];
DecompositionOfq:=Decomposition(OK,q);
if #DecompositionOfq ge 3 then 
IndicesOfFirstThreeResidueDegreeOnePrimesAboveqEncountered:=[];
for ii:=1 to #DecompositionOfq do
if InertiaDegree(DecompositionOfq[ii][1]) eq 1 then 
Append(~IndicesOfFirstThreeResidueDegreeOnePrimesAboveqEncountered,ii); 
end if;
if #IndicesOfFirstThreeResidueDegreeOnePrimesAboveqEncountered eq 3 then 
break ii; 
end if;
end for; //ii
if #IndicesOfFirstThreeResidueDegreeOnePrimesAboveqEncountered eq 3 then

hhh:=hhh+1;
Q[hhh]:=[];
ProductOfAllqSelected:=ProductOfAllqSelected*q;
ZmodqZ:=FiniteField(q, 1);
for ii in IndicesOfFirstThreeResidueDegreeOnePrimesAboveqEncountered do
temp:=[];
for jj:=1 to #J do 
temp[jj]:=ZmodqZ ! (pi[J[jj]][kk[J[jj]]] mod DecompositionOfq[ii][1]); 
end for;
for jj:=1 to r do
temp[#J+jj]:=ZmodqZ ! (eps[jj] mod DecompositionOfq[ii][1]); 
end for;
temp[1+#J+r]:=ZmodqZ ! ((OK ! alpha*zeta) mod DecompositionOfq[ii][1]);
temp[2+#J+r]:=ZmodqZ ! ((OK ! theta) mod DecompositionOfq[ii][1]);
Append(~Q[hhh],temp);
end for; //ii

end if;// controlled by #IndicesOfFirstThreeResidueDegreeOnePrimesAboveqEncountered eq 3
end if;// controlled by #DecompositionOfq ge 3
end for; //i

j:=j+1;
end while;



//////////////////////////////////////////////////////////////////////////////
/*
Suppose bbb[i] = b_{JJJ[1+i]}, for i=1 to #JJJ-1.
Note: bbb[i] = b_{JJJ[1+i]} = b_{1+J[i]}=n_{J[i]} for i:=1 to #J
Note: bbb[#J+i] = b_{JJJ[1+#J+i]} = b_{1+v+i}=a_i for i:=1 to r

We define BBBupper and BBBlower so that
BBBlower[i] <= bbb[i] <= BBBupper[i]
*/
/////////////////////////////////////////////////////////////////////////////
BBBupper:=[];
BBBlower:=[];
for i:=1 to #J do
BBBupper[i]:=UpperBoundForn[J[i]];
BBBlower[i]:=0;
end for;
for i:=#J+1 to #J+r do
BBBupper[i]:=UpperBoundForA;
BBBlower[i]:=-UpperBoundForA;
end for;
BBBupperlower:=[BBBupper,BBBlower];


//Solutions:=[];

///////////////////////////////////////////////////////////////////////////////
/*
Sieve through all tuples in the box defined by the bounds on the n_i (i in J) and the a_i
*/
//////////////////////////////////////////////////////////////////////////////
PrintFile(LogFile,"Starting the sieve.");
fprintf LogFile, "UpperBoundForn = %o\n", UpperBoundForn;
fprintf LogFile, "UpperBoundForA = %o\n", UpperBoundForA;


bbb:=[]; //needed for SieveBox() to work

nJ:=#J;
nQ:=#Q;
nJr:=[nJ+r,nJ+r+1,nJ+r+2];
Input:=[*ImageOfzetaC,ImageOfalphaC,ImageOfpiC,ImageOfepsC,thetaC,J,ValueOfn,kk,hh,ss,tt,s,t,c,p,a,r,n,v,nJ,nQ,nJr*];

SieveBox(~bbb,~Solutions,~BBBupperlower,~Q,~Input,1);

//////////////////////////////////////////////////////////////////////////////
/*
Sieve through all exceptional tuples that we found in the refined reduction steps.

After this procedure is done, Solutions will contain all the exceptional solutions (X,Y,z_1,...,z_v) of the sign-relaxed version of Thue-Mahler equation (1) that also satisfy the current case of (11).  Recall:  Every solution of the Thue-Mahler equation satisfies some case of (11).
*/
//////////////////////////////////////////////////////////////////////////////
bbb:=[];
//ExceptionalTuples;
//ExceptionalTuplesTest[iiii]:=ExceptionalTuples;

for i:=1 to #ExceptionalTuples do

temp:=ExceptionalTuples[i];
for j:=1 to #temp do
bbb[j]:=IntegerRing() ! temp[j];
end for;


//Test the tuple bbb for the congruences (25)
passes:=true;
for hhh:=1 to #Q do
//test the tuple for the q=q_hhh congruence (25)
CongruenceTest(~bbb,hhh,~passes,~Q,~nJr);
if passes eq false then break hhh; end if;
end for;

if passes eq true then

/* 
Use the tuple bbb (where bbb[i]=b_{JJJ[1+i]}, i=1 to #JJJ-1) to get 
the tuple
bb (where bb[i] = b_{1+i}, i=1 to v).  Compute the corresponding X,Y. 
Test if (X,Y,b_{2},...,b_{1+v}) gives a solution of the Thue-Mahler 
equation (1) and record the solution if so. 
*/
ThueMahlerEquationTest(~bbb,~Solutions,~Input);  

end if;

end for;








//////////////////////////////////////////////////////////////////////////
/*
At this point almost all of the solutions of the sign-relaxed version of 
the Thue-Mahler equation have been found.  In the language of Section 6, 
the ones we have found come from instances of (11) with \zeta equal to an 
element of T^{\prime}.  The missing ones come from instances of (11) with 
\zeta equal to an element of $T \setminus T^{\prime}$.  The missing ones 
are of the form (-x,-y,z_1,...,z_v) where (x,y,z_1,...,z_v) is a solution 
we have found.

Now we find the missing solutions.
*/
//////////////////////////////////////////////////////////////////////////
SolutionsCopy:=Solutions;
for ii:=1 to #SolutionsCopy do
sol:=SolutionsCopy[ii]; //sol = (X,Y,z_1,...,z_v)
sol[1]:=-sol[1];
sol[2]:=-sol[2];
//now sol = (-X,-Y,z_1,...,z_v)

//Build RHS and LHS expressions
RHSexpression:=a;
for i:=1 to v do
RHSexpression *:= p[i]^(sol[2+i]);
end for;
LHSexpression:= sol[1]^n + c[n]*sol[2]^n;
for i:=1 to n-1 do
LHSexpression:=LHSexpression + c[i]*sol[1]^(n-i)*sol[2]^i;
end for;

/*Test if sol=(-X,-Y,z_1,...,z_v) is a solution of the Thue-Mahler 
equation (in the form Abs(LHSexpression)-Abs(RHSexpression) = 0).  
If so, append it to Solutions*/
if IsZero(Abs(LHSexpression)-Abs(RHSexpression)) then 
Include(~Solutions,sol);
end if;

end for;


//////////////////////////////////////////////////////////////////////////
/*
At this point all the solutions of the sign-relaxed version of the 
Thue-Mahler equation have been found.  

It is now a simple matter to go through these solutions and eliminate 
the ones that are not solutions of the Thue-Mahler equation proper.
WE SKIP THIS.

Recall: Each element of Solutions is of the form
[X,Y,z_1,...,z_v]
*/
/////////////////////////////////////////////////////////////////////////
/*
SolutionsCopy:=Solutions;
for ii:=#SolutionsCopy to 1 by -1 do

//Build RHS and LHS expressions
RHSexpression:=a;
for i:=1 to v do
RHSexpression *:= p[i]^(SolutionsCopy[ii][2+i]);
end for;
LHSexpression:= SolutionsCopy[ii][1]^n + c[n]*SolutionsCopy[ii][2]^n;
for i:=1 to n-1 do
LHSexpression:=LHSexpression + c[i]*SolutionsCopy[ii][1]^(n-i)*SolutionsCopy[ii][2]^i;
end for;

//test if =(X,Y,z_1,...,z_v) is a solution of the Thue-Mahler 
//equation (in the form LHSexpression-RHSexpression = 0).  
//If not, remove it from Solutions
if not IsZero(LHSexpression-RHSexpression) then 
Remove(~Solutions,ii); 
end if;

end for; //end ii loop
*/
//////////////////////////////////////////////////////////////////////////
end for;  //end iiii loop (the loop through the cases)

break PrecisionLoopVariable;
end for; //end the precision loop  //this loop is a bit of hack

//print("Solutions:");
return Solutions;

//UnsetOutputFile();

end intrinsic;

////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////


/////////////////////////////////////////////////////////////////////////
intrinsic pAdicMyLog(x::FldPadElt,p::RngIntElt,padicprecision::RngIntElt) -> FldPadElt
{}
/*
Input: p = rational prime, x = p-adic unit belonging to a finite 
extension of Q_p
output: the p-adic logarithm of x
*/
e:=AbsoluteRamificationIndex(Parent(x));
f:=AbsoluteInertiaDegree(Parent(x));
CandidateOrders:=Divisors(p^f - 1);
o:=1;
for oo in CandidateOrders do
if Valuation(x^oo - 1) gt 0 then o:=oo; break; end if;
end for;
j:=1;
while p^j le e do
j +:= 1; //j:=j+1;
end while;
z:=x^(o*p^j);
n:=1;
while n*Valuation(z-1) lt Valuation(n, p) + 10*padicprecision do
n +:= 1;
end while;
beta:=0;
delta:=1;
for i:=1 to n do
delta:=delta*(1-z);
beta:=beta - delta/i;
end for;
return beta/o*p^j;
end intrinsic;


////////////////////////////////////////////////////////////
intrinsic pAdicLog(x::FldPadElt, p::RngIntElt, padicprecision::RngIntElt) -> FldPadElt 
{}
/*
Input: p = rational prime, x = p-adic unit belonging to a finite extension of Q_p
output: the p-adic logarithm of x
*/
e:=AbsoluteRamificationIndex(Parent(x));
f:=AbsoluteInertiaDegree(Parent(x));
CandidateOrders:=Divisors(p^f - 1);
o:=1;
for oo in CandidateOrders do
if Valuation(x^oo - 1) gt 0 then o:=oo; break; end if;
end for;
j:=1;
while p^j le e do
j +:= 1; //j:=j+1;
end while;
return Log( x^(o*p^j) )/(o*p^j);
end intrinsic;

//////////////////////////////////////////////////////////////////////////

intrinsic DistanceToNearestInteger(x::FldRatElt) -> FldRatElt
{}
return Min( [x-Floor(x), Ceiling(x)-x] );
end intrinsic;

//////////////////////////////////////////////////////////////////////////
intrinsic RoundP(x::FldRatElt) -> RngIntElt
{}
/*
Input: x = a real number
Ouput: The nearest positive integer to x.  If two postive integers are the 
same distance to x, take the largest of the two.
*/
require x ge 0: "Argument 1 is < 0";
y:=Round(x);
if y eq 0 then y:=1; end if;
return y;
end intrinsic;

//////////////////////////////////////////////////////////////////
intrinsic SmallestNonnegativeRemainderModpLToThem(x::FldPadElt, p::RngIntElt, m::RngIntElt, padicprecision::RngIntElt) -> RngIntElt
{}
/*
Input: m = positive integer, p a prime 
x = an element in the p-adic field Q_{p} that belongs to the subring Z_{p} (the ring of p-adic integers in Q_{p}).
Output: The unique integer x^{m} in [0,p^m - 1] with ord_{p}(x - x^{m}) >= m
*/
y:=pAdicRing(p : Precision:=padicprecision) ! x;
y:=pAdicQuotientRing(p, m) ! y;
y:=IntegerRing() ! y;
if y lt 0 then y:=y+p^m; end if;
return y;
end intrinsic;


//////////////////////////////////////////////////////////////////

intrinsic LengthOfVector(v::ModMatFldElt) -> FldReElt
{}
/*
Input: v = n by 1 column matrix
Output: The length of v = the square root of the sum of the squares of the entries of v.
*/
size:=NumberOfRows(v);
length:=0;
for i:=1 to size do
length +:= v[i][1]*v[i][1];
end for;
length:=length^(1/2);
return length;
end intrinsic;

////////////////////////////////////////////////////
intrinsic MaxAbsLog(a::FldNumElt) -> FldReElt
{}
/*
Input: a = number field element
Output: The maximum of the numbers |Log(a^{(1)})|,..., =|Log(a^{(n)})|, 
where the a^{(i)} are the conjugates of a in \CC and Log denotes the principal branch of the complex logarithm
*/
minpoly:=MinimalPolynomial(a,IntegerRing());
ConjugatesOfa:=Roots(PolynomialRing(ComplexField()) ! minpoly);
deg:=Degree(minpoly);
max:=Modulus(Log(ConjugatesOfa[1][1]));
for i:=2 to deg do
temp:=Modulus(Log(ConjugatesOfa[i][1]));
if temp gt max then max:=temp; end if;
end for;
return max;
end intrinsic;

///////////////////////////////////////////////////////////////
intrinsic RNTO(x::RngIntElt) -> RngIntElt
{}
/*
RNTO = Round Nonpositive to One
Input: x = a real number
Output: x if x > 0, 1 if x <= 0
*/
if x le 0 then 
return 1;
else
return x;
end if;
end intrinsic;

///////////////////////////////////////////////////////////////

intrinsic Choosettt(~yyytttpotentialtttFloorsss::[],~min::FldReElt,~Bm::AlgMatElt,~mm::RngIntElt,k::RngIntElt)
{}
/*
Assumption:  sss is a mm by 1 column vector with real entries
Input: Floorsss = yyytttpotentialtttFloorsss[4] is a mm by 1 column vector with Floorsss[i][1]=Floor(sss[i][1])
Input: yyy = yyytttpotentialtttFloorsss[1] is a given mm by 1 vector with real entries
Input: Bm is a given mm by mm matrix with real entries
Input: potentialttt = yyytttpotentialtttFloorsss[3] is a mm by 1 vector used as a placeholder by this procedure
Input: ttt = yyytttpotentialtttFloorsss[2] is a mm by 1 column vector
Input: min is a real number
Assumption: This procedure calls itself.  When it is called by the user, we assume min is equal to the length of the column vector Bm*Floorsss - yyy 
Input: k is a postive integer
Assumption: This procedure calls itself.  When this procedure is called by the user, we assume k=1.
Result:  If the three assumptions above hold, then, after this procedure is completed ttt, will be a mm by 1 column vector with integer entries such that 
|ttt[i][1] - sss[i][1]| <= 1 and such that the length of Bm*ttt - yyy is minimal (among all choices of ttt with integral and |ttt[i][1] - sss[i][1]| <= 1).  Also, min will be the length of Bm*ttt - yyy.
*/
if k eq mm+1 then

potentialmin:=LengthOfVector(Bm*yyytttpotentialtttFloorsss[3] - yyytttpotentialtttFloorsss[1]);
if potentialmin lt min then
yyytttpotentialtttFloorsss[2]:=yyytttpotentialtttFloorsss[3];
min:=potentialmin;
end if;

else

for j:=0 to 1 do
yyytttpotentialtttFloorsss[3][k][1]:=yyytttpotentialtttFloorsss[4][k][1]+j;
Choosettt(~yyytttpotentialtttFloorsss,~min,~Bm,~mm,k+1);
end for;

end if;

end intrinsic;

//////////////////////////////////////////////////////////////////////

intrinsic CongruenceTest(~bbb::SeqEnum,hhh::RngIntElt,~passes::BoolElt,~Q::List,~nJr::SeqEnum)
{}
/*
Input: bbb is a sequence of #JJJ-1 integers.
Input: hhh is a positive integer
Assumption: Q[hhh] is a sequence of #JJJ+1 elements of the finite field Z/qZ, where q is a rational prime.
Input: A boolean variable
Assumption: bbb[i] = b_{JJJ[1+i]}, i=1 to #JJJ-1
Note: bbb[i] = b_{JJJ[1+i]} = b_{1+J[i]}=n_{J[i]} for i:=1 to #J
Note: bbb[#J+i] = b_{JJJ[1+#J+i]} = b_{1+v+i}=a_i for i:=1 to r
Assumption: q has at least three residue degree one prime ideals of OK above it. Assumption: For i=1,2,3, 
Qh[i]=[P_{i,JJJ[2]-1}, ..., P_{i,JJJ[1+#J]-1}, E_i1, ..., E_ir, A_i, m_i]
     =[P_{i,J[1]}, ..., P_{i,J[#J]}, E_i1, ..., E_ir, A_i, m_i]
where m_i, A_i, P_ij, E_ij are the numbers from Section 22 corresponding to three residue degree one prime ideals of OK above q.
Assumption: passes = true on entry to this procedure
Result:  Provided the assumptions hold, passes will have the value true if b_{JJJ[i+1]} satisfies the congruence (25) (with those Pij,n_j with j not in J removed) and will have the value false otherwise.
*/
//nJr:=[#J+r,#J+r+1,#J+r+2];

prod1:=Q[hhh][1][nJr[2]];
prod2:=Q[hhh][2][nJr[2]];
prod3:=Q[hhh][3][nJr[2]];
for ii:=1 to nJr[1] do
prod1 *:= Q[hhh][1][ii]^bbb[ii];
prod2 *:= Q[hhh][2][ii]^bbb[ii];
prod3 *:= Q[hhh][3][ii]^bbb[ii];
end for;

if IsZero(
(Q[hhh][2][nJr[3]]-Q[hhh][3][nJr[3]])*prod1 + 
(Q[hhh][3][nJr[3]]-Q[hhh][1][nJr[3]])*prod2 + 
(Q[hhh][1][nJr[3]]-Q[hhh][2][nJr[3]])*prod3
) then
else
passes:=false;
end if;

end intrinsic;

///////////////////////////////////////////////////////////////////////////////////////////////////////
intrinsic ThueMahlerEquationTest(~bbb::SeqEnum,~Solutions::SeqEnum,~Input::List)
{}
/* 
Use the tuple bbb (where bbb[i]=b_{JJJ[1+i]}, i=1 to #JJJ-1) and the sequence ValueOfn to get the tuple bb (where bb[i] = b_{1+i}=n_i, i=1 to v).
  
Compute the corresponding X,Y.  We can actually compute X,Y before the getting bb because \pi_{l}^{n_{l}} for l not in J is already part of \alpha.  We do this.

Test if (X,Y,b_{2},...,b_{1+v+r}) gives solution of the Thue-Mahler equation (1) and record it if so. 

Note: bbb[i]=b_{JJJ[1+i]} = b_{1+J[i]}=n_{J[i]}=bb[J[i]] for i:=1 to #J
Note: bbb[#J+i]=b_{JJJ[1+#J+i]} = b_{1+v+i}=a_i=bb[v+i] for i:=1 to r
*/
ImageOfzetaC:=Input[1];
ImageOfalphaC:=Input[2];
ImageOfpiC:=Input[3];
ImageOfepsC:=Input[4];
thetaC:=Input[5];
J:=Input[6];
ValueOfn:=Input[7];
kk:=Input[8];
hh:=Input[9];
ss:=Input[10];
tt:=Input[11];
s:=Input[12];
t:=Input[13];
c:=Input[14];
p:=Input[15];
a:=Input[16];
r:=Input[17];
n:=Input[18];
v:=Input[19];
nJ:=Input[20];



//Calculate X,Y
if t gt 0 then

BETA1:= ImageOfzetaC[s+1] * ImageOfalphaC[s+1];
for i:=1 to nJ do
BETA1 *:= ImageOfpiC[J[i]][kk[J[i]]][s+1]^bbb[i];
end for;
for i:=1 to r do
BETA1 *:= ImageOfepsC[i][s+1]^bbb[nJ+i];
end for;
THETA1:=thetaC[s+1];

Y:= -Imaginary(BETA1)/Imaginary(THETA1);
X:=Round(  Real( BETA1 + THETA1*Y )  );
Y:=Round(Y);

else //t=0

BETA1:= ImageOfzetaC[1] * ImageOfalphaC[1];
for i:=1 to nJ do
BETA1 *:= ImageOfpiC[J[i]][kk[J[i]]][1]^bbb[i];
end for;
for i:=1 to r do
BETA1 *:= ImageOfepsC[i][1]^bbb[nJ+i];
end for;
THETA1:=thetaC[1];

BETA2:= ImageOfzetaC[2] * ImageOfalphaC[2];
for i:=1 to nJ do
BETA2 *:= ImageOfpiC[J[i]][kk[J[i]]][2]^bbb[i];
end for;
for i:=1 to r do
BETA2 *:= ImageOfepsC[i][2]^bbb[nJ+i];
end for;
THETA2:=thetaC[2];

Y:= Real(-(BETA1 - BETA2)/(THETA1 - THETA2));
X:=Round(Real(BETA1 + Y*THETA1));
Y:=Round(Y);

end if;

//Get the tuple bb from bbb and ValueOfn
bb:=[];
for i:=1 to v do
bb[i]:=ValueOfn[i]; //initialize
end for;
for i:=1 to nJ do
bb[J[i]]:=bbb[i];
end for;
/*for i:=1 to r do
bb[v+i]:=bbb[nJ+i];
end for;*/


//Build RHS and LHS expressions
RHSexpression:=a;
for i:=1 to v do
RHSexpression *:= p[i]^(bb[i]*hh[i] + ss[i] + tt[i]);
end for;
LHSexpression:= X^n + c[n]*Y^n;
for i:=1 to n-1 do
LHSexpression:=LHSexpression + c[i]*X^(n-i)*Y^i;
end for;

/*test if (X,Y,bb[1],...,bb[v])=(X,Y,b_{2},...,b_{1+v}) gives a solution of the sign-relaxed Thue-Mahler equation (in the form |LHS|-|RHS| = 0) */
if IsZero(Abs(LHSexpression) - Abs(RHSexpression)) and Gcd(X,Y) eq 1 then 
temp:=[X,Y];
for i:=1 to v do
Append( ~temp, bb[i]*hh[i] + ss[i] + tt[i] );
end for;
Include(~Solutions,temp); 
end if;

end intrinsic;


/////////////////////////////////////////////////////////////////////////
intrinsic SieveBox(~bbb::SeqEnum,~Solutions::SeqEnum,~Bupperlower::SeqEnum,~Q::List,~Input::List,k::RngIntElt)
{}
/*
This procedure calls itself.

When this procedure is called by the user, we assume that k=1 and Solutions is a (possibly empty) list of solutions for the Thue-Mahler equation.

After this procedure is finished executing its call by the user, Solutions will contain all the solutions (X,Y,n_1,...,n_v,a_1,...,a_r) of the sign-relaxed version of the Thue-Mahler equation that satisfy the currently known bounds on the n_i and the a_i and that satisfy the current case of (11).  Note that these bounds miss finitely many explicitly known exceptional tuples.  

Recall:  Every solution of the Thue-Mahler equation satisfies some case of (11).
*/
J:=Input[6];
Bupper:=Bupperlower[1];
Blower:=Bupperlower[2];
s:=Input[12];
t:=Input[13];
r:=Input[17];
nJ:=Input[20];
nQ:=Input[21];
nJr:=Input[22]; //nJr:=[#J+r,#J+r+1,#J+r+2];



if k gt nJr[1] then //done k-1 loops and k-1 >= #J+r loops, so the tuple is built

//Test the tuple bbb for the congruences (25)
passes:=true;
for hhh:=1 to nQ do
//test the tuple for the q=q_hhh congruence (25)
CongruenceTest(~bbb,hhh,~passes,~Q,~nJr);
if passes eq false then break hhh; end if;
end for;

if passes eq true then

/* Use the tuple bbb (where bbb[i]=b_{JJJ[1+i]}, i=1 to #JJJ-1) to get the tuple
bb (where bb[i] = b_{1+i}, i=1 to v).  Compute the corresponding X,Y. Test if (X,Y,b_{2},...,b_{1+v}) gives a solution of the sign-relaxed version of the Thue-Mahler equation (1) and record it if so. */
ThueMahlerEquationTest(~bbb,~Solutions,~Input); 

end if;


else //k le #J+r. Done k-1 loops and k-1 < #J+r, so the tuple is not built.  Only k-1 entries of the tuple have been picked.
for i:=Blower[k] to Bupper[k] do
bbb[k]:=i;
SieveBox(~bbb,~Solutions,~Bupperlower,~Q,~Input,k+1);
end for;

end if; 

end intrinsic;

//////////////////////////////////////////////////////////

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

/*test if tuple fits in the new box.  If so, throw it away (it's not exceptional).  Recall bbb[jl[l]] = b_{l+1} = n_l*/
if bbb[jl[l]] le NewUpperBoundFornl then passes:=false; break; end if;


LAMBDAprime:=0;
for i:=1 to nJJJ do 
LAMBDAprime:=LAMBDAprime + bbb[i]*beta[l][JJJ[i]];
end for;
if SpecialCase[l] eq true then
if Valuation(LAMBDAprime) ne bbb[jl[l]]*hh[l] + dd[l] then passes:=false; break; end if; 
else //SpecialCase[l] eq false
if Valuation(LAMBDAprime) lt bbb[jl[l]]*hh[l] + dd[l] then passes:=false; break; end if;
end if;


for ll in I do
if ll ne l then

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

end if;
end for;
if passes eq false then break; end if;


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

////////////////////////////////////////////////////////////////////////////////////
intrinsic ExtractTupleComplexCase(~bbb::SeqEnum[FldRatElt],~ExtractTupleComplexCaseInput::List,~uuu::LatElt[RngInt])
{}
//Extract tuple (b_{JJJ[2]},...,b_{JJJ[#JJJ]},b_{2+v+r})
//ExtractTupleComplexCaseInput:=[*bbb,yyy,zzz,JJJ,nJJJ,nJ,W,B,phi,2+v+r*];
//bbb:=ExtractTupleComplexCaseInput[1];
yyy:=ExtractTupleComplexCaseInput[2];
zzz:=ExtractTupleComplexCaseInput[3];
JJJ:=ExtractTupleComplexCaseInput[4];
nJJJ:=ExtractTupleComplexCaseInput[5];
nJ:=ExtractTupleComplexCaseInput[6];
W:=ExtractTupleComplexCaseInput[7];
B:=ExtractTupleComplexCaseInput[8];
phi:=ExtractTupleComplexCaseInput[9];
twoplusvplusr:=ExtractTupleComplexCaseInput[10];

for i:=2 to 1+nJ do
bbb[i] := (uuu[i-1] - (yyy[i-1][1]-zzz[i-1][1]) + (1/2)*W[JJJ[i]]*B[JJJ[i]])/W[JJJ[i]];
end for;
for i:=2+nJ to nJJJ do
bbb[i] := (uuu[i-1] - (yyy[i-1][1]-zzz[i-1][1]))/W[JJJ[i]];
end for;
sum:=0;
for i:=1 to nJJJ do
sum:=sum+bbb[i]*phi[JJJ[i]];
end for;
bbb[nJJJ+1] := (uuu[nJJJ] - (yyy[nJJJ][1]-zzz[nJJJ][1]) - sum)/phi[twoplusvplusr];

end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
intrinsic TestTupleComplexCase(~bbb::SeqEnum[FldRatElt],~TestTupleComplexCaseInput::List,~passes::BoolElt)
{}
//Test the tuple
//TestTupleComplexCaseInput:=[*bbb,JJJ,nJJJ,nJ,NewConditionalUpperBoundForAi0,jl,SpecialCase,p,delta2,hh,dd,B,2+v+r,I,beta*];
//bbb:=TestTupleComplexCaseInput[1];
JJJ:=TestTupleComplexCaseInput[2];
nJJJ:=TestTupleComplexCaseInput[3];
nJ:=TestTupleComplexCaseInput[4];
NewConditionalUpperBoundForAi0:=TestTupleComplexCaseInput[5];
jl:=TestTupleComplexCaseInput[6];
SpecialCase:=TestTupleComplexCaseInput[7];
p:=TestTupleComplexCaseInput[8];
delta2:=TestTupleComplexCaseInput[9];
hh:=TestTupleComplexCaseInput[10];
dd:=TestTupleComplexCaseInput[11];
B:=TestTupleComplexCaseInput[12];
twoplusvplusr:=TestTupleComplexCaseInput[13];
I:=TestTupleComplexCaseInput[14];
beta:=TestTupleComplexCaseInput[15];


while true do //this while loop is a hack to provide a way to "jump to line X" 

for i:=2 to nJJJ do
if not IsIntegral(bbb[i]) then passes:=false; break; end if;
end for;
if passes eq false then break; end if;

if not IsIntegral((1/2)*bbb[nJJJ+1]) then passes:=false; break; end if;

for i:=2 to 1+nJ do
if bbb[i] gt B[JJJ[i]] or bbb[i] lt 0 then passes:=false; break; end if;
end for;
if passes eq false then break; end if;

for i:=2+nJ to nJJJ do
if bbb[i] gt B[JJJ[i]] or bbb[i] lt -B[JJJ[i]] then passes:=false; break; end if;
end for;
if passes eq false then break; end if;

if bbb[nJJJ+1] gt B[twoplusvplusr] or bbb[nJJJ+1] lt -B[twoplusvplusr] then passes:=false; break; end if;

/*Test if the tuple fits in the new box.  If so, throw it away (it's not exceptional). */
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

/////////////////////////////////////////////////////////////////////////////////////
intrinsic IsZeroLocal(x::FldPadElt,S::RngIntElt) -> BoolElt
{}
/*if Valuation(x) ge Valuation(Zero(Parent(x))) - 2*(AbsoluteDegree(Parent(x))-1) then
return true;
else
return false;
end if;*/
if Valuation(x) ge Valuation(Zero(Parent(x))) - 2*(S-1) then
return true;
else
return false;
end if;
end intrinsic;

////////////////////////////////////////////////////////////////////////////////////
intrinsic Dig(x::RngIntElt) -> RngIntElt
{}
return Floor(Log(Abs(x))/Log(10));
end intrinsic;
