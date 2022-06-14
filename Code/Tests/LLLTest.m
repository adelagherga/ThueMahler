//;; This buffer is for text that is not saved, and for Lisp evaluation.
//;; To create a file, visit it with <open> and enter text in its buffer.

n:=4;
Za<a1,a2,a3,a4>:= PolynomialRing(Rationals(),n);
R:= IdentityMatrix(Za,n);
//a1:= 100; a2:= 98; a3:= 209; a4:= 8765;

R[n,1]:= a1;
R[n,2]:= a2;
R[n,3]:= a3;
R[n,4]:= a4;
//R[n,5]:= a5;
R;

function set_column(M,N,i)
    n:= NumberOfColumns(M);
    assert n eq NumberOfColumns(N);
    assert (i gt 0) and (i le n);

    for j in [1..n] do
	M[j,i]:= N[j,i];
    end for;

    assert ColumnSubmatrix(M,i,1) eq ColumnSubmatrix(N,i,1);
    return M;
end function;

function Aprime(k,l,B,L,U,V,d)
    if 2*(L[k,l]) gt d[l+1,1] then
	r:= L[k,l]/d[l+1,1]; // so you round up, because 2*A/B > 1 so A/B > 1/2
	tempB:= ZeroMatrix(Za,n,1);
	for j in [1..n] do
	    tempB[j,1]:= B[j,k] - r*B[j,l];
	end for;
	InsertBlock(~B,tempB,1,k);

	for j in [1..l] do
            L[k,j]:= L[k,j] - r*L[l,j];
	end for;
        L[k,l]:= L[k,l] - r*d[l+1,1];
    end if;

    return B,L,U,V,d;
end function;

function Bprime(k,B,L,U,V,d,n)
    SwapColumns(~B,k,k-1);
    for j in [1..k-1] do
	temp1:= L[k-1,j];
	temp2:= L[k,j];
	L[k-1,j]:= temp2;
	L[k,j]:= temp1;
    end for;
    for i in [k+1..n-1] do
        t:= L[i,k-1];
        L[i,k-1]:= (L[i,k-1]*L[k,k-1] + L[i,k]*d[k-1,1])/d[k,1];
        L[i,k]:= (t*d[k+1,1] - L[i,k]*L[k,k-1])/d[k,1];
    end for;
    d[k,1]:= (d[k-1,1]*d[k+1,1] + (L[k,k-1])^2)/d[k,1];

    return k,B,L,U,V,d;
end function;

// first part of myLLL(R)
B:= R;
n:= NumberOfColumns(R);
V:= IdentityMatrix(Za,n);
U:= IdentityMatrix(Za,n);
L:= ZeroMatrix(FieldOfFractions(Za),n,n);
C:= ZeroMatrix(Za,n,n);
d:= ZeroMatrix(FieldOfFractions(Za),n+1,1);
d[1,1]:= 1;

for i in [1..n] do
    C:= set_column(C,B,i);
    for j in [1..i-1] do
	L[i,j]:= (Transpose(ColumnSubmatrix(B,i,1))*ColumnSubmatrix(C,j,1))[1,1];
	multC1:= ColumnSubmatrix(MultiplyColumn(C,d[j+1,1],i),i,1);
	multC2:= ColumnSubmatrix(MultiplyColumn(C,L[i,j],j),j,1);
	tempC:= ZeroMatrix(Za,n,1);
	for k in [1..n] do
	    tempC[k,1]:= (multC1-multC2)[k,1]/d[j,1];
	end for;
	InsertBlock(~C,tempC,1,i);
    end for;
    d[i+1,1]:= (Transpose(ColumnSubmatrix(C,i,1))*ColumnSubmatrix(C,i,1))[1,1]/d[i,1];
end for;

k:=2;
while (k lt n) do
    B,L,U,V,d:= Aprime(k,k-1,B,L,U,V,d);
    if 4*d[k-1,1]*d[k+1,1] lt 3*(d[k,1]^2) - 4*(L[k,k-1]^2) then
	k,B,L,U,V,d:= Bprime(k,B,L,U,V,d,n);
	if k gt 2 then
            k:= k-1;
	end if;
    else
        for l in [k-2..0 by -1] do
	    B,L,U,V,d:= Aprime(k,l,B,L,U,V,d);
	end for;
	k:=k+1;
    end if;
end while;
