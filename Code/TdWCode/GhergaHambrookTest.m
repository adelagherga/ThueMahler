/*
GhergaHambrookTest.m

Author: Adela Gherga <adelagherga@gmail.com>
Copyright © 2021, Adela Gherga, all rights reserved.
Created: 11 January 2021

Description: This program is set up to test hangups and memory leaks in GhergaHambrook.m. The
	     code is identical to GhergaHambrook.m, but avoids many loops so that the user
             may debug or speed up each section accordingly.

Commentary:  N/A

To do list:  N/A

Example:     N/A

*/

// attach GhergaHambrook.m to add all intrinsics
Attach("/home/adela/ThueMahler/Code/TdWCode/GhergaHambrook.m");
C:=[1,-6,5,-1];
p:= PrimesInInterval(1,41);
A:=1;
FindAll:=true;
LogFile:= "testlog.txt";
OutFile:= "testout.txt";



PrintFile(OutFile,"////////////////////////////////////////");
fprintf OutFile, "C:=%o; p:=%o; A:=%o;\n", C, p, A;
PrintFile(LogFile,"////////////////////////////////////////");
//fprintf LogFile, "C:=%o; p:=%o; A:=%o;", C, p, A;
printf "C:=%o; p:=%o; A:=%o;\n", C, p, A;

LogFileOutFile:=[LogFile,OutFile];

DoneAllCases:=false;
SOL2:=[];
NumberOfCasesInBatch:=700;
StartCase:=0;
EndCase:=0;

///////////////////////////////////////////////////////
// intrinsic TMCases
//////////////////////////////////////////////////////
//while DoneAllCases eq false do
StartCase:=EndCase+1;
EndCase:=EndCase+NumberOfCasesInBatch;
StartEndCase:=[StartCase,EndCase];
//SOL1:=TMCases(C,p,A,LogFileOUtFile,FindAll,StartEndCase);

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
