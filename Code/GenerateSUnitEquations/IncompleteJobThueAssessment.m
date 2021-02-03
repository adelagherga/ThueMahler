/*
IncompleteJobThueAssessment.m

Author: Adela Gherga <adelagherga@gmail.com>
Copyright © 2021, Adela Gherga, all rights reserved.
Created:  3 February 2021

Description: Iterates through IncompleteJobs to determine if the error is related to Magma's Thue
	     solver.

Commentary:  The result of this code is to be sent to John Cannon to assess the Thue patch.
             Runt with
cat /home/adela/ThueMahler/Data/SUnitEqData/OldIncompleteJobs | parallel -j1 magma set:={} /home/adela/ThueMahler/Code/GenerateSUnitEquations/IncompleteJobThueAssessment.m


To do list:  N/A

Example:     N/A

*/

LogFile:= "/home/adela/ThueMahler/Data/SUnitEqData/MagmaInternalErrors.txt";
SetLogFile(LogFile);

print set;
BracketSplit:= Split(set,"[]"); // split bash input by "[" and "]"
assert (#BracketSplit eq 2);

clist:= [StringToInteger(i) : i in Split(BracketSplit[2],",")];
clist:= clist[2..5];

n:= #clist - 1;
QUV<U,V>:= PolynomialRing(Rationals(),2);
Zx_<x_>:= PolynomialRing(Integers());
F:= &+[clist[i+1]*U^(n-i)*V^i : i in [0..n]];
ThueF:= Thue(Evaluate(F,[x_,1])); // generate Thue equation

testset:= PrimesInInterval(1,200) cat [i: i in [1..20] | i notin PrimesInInterval(1,200)];
for i in testset do
    print clist, i;
    s:= Solutions(ThueF,i);
end for;
print "---------------------";
