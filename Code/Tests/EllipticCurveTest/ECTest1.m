CommaSplit:=Split(set,","); // Split bash input by ",".
RBracketSplit:=Split(set,"()"); // Split bash input by "(" and ")".
// Delimiter for form.
assert CommaSplit[2][2] eq "(" and CommaSplit[5][#CommaSplit[5]-1] eq ")";
// Delimiter for optimal form.
assert CommaSplit[6][2] eq "(" and CommaSplit[9][#CommaSplit[9]-1] eq ")";
// Delimiter for min poly.
assert CommaSplit[10][2] eq "(" and CommaSplit[13][#CommaSplit[13]-1] eq ")";
assert (#RBracketSplit eq 11) or (#RBracketSplit eq 13);
N:=StringToInteger(CommaSplit[1]);
// Convert bash input for optimal form, min poly into a sequence of integers.
alist:=[StringToInteger(i) : i in Split(RBracketSplit[4],",")];
if (#RBracketSplit eq 11) then
    assert CommaSplit[14] eq "None";
    aconsts:=[StringToInteger(i) : i in Split(RBracketSplit[8],",")];
    primelist:=[StringToInteger(i) : i in Split(RBracketSplit[10],",")];
else
    aconsts:=[StringToInteger(i) : i in Split(RBracketSplit[10],",")];
    primelist:=[StringToInteger(i) : i in Split(RBracketSplit[12],",")];
end if;

SetLogFile("test.txt");
for a in aconsts do
    sols:=solveThueMahlerAll(alist,a,primelist);
    ECs:=convertTMToEllipticCurves(N,alist,sols);
    printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
    printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
    printf "Elliptic curves of conductor N = %o from alist:=%o :\n ",N,alist;
    print relECs;

    for E in ECs do
	assert E[1] eq N;
	fprintf "outtest.m", N,E[2],alist,a,primelist,E[3];
    end for;

f,remainingCase,partialObstruction,localObstruction:=
    prep0(N,clist,fclist,partialObstruction,avalues,primelist);
Append(~timings,<Cputime(t1),"local obstructions">);

UnsetLogFile();
