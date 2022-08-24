/*
computeEllipticCurvesTM.m

This function solves the Thue--Mahler equations defined in the string "set",
computes the corresponding elliptic curves, and outputs the logfile and elliptic
curve data in seperate files. Note that these output files may contain multiple
Thue--Mahler form solutions, one for each integer a in "a values" and for each
monic form arising from "optimal form".

Parameters
    set: MonStgElt
        A string in the format
	"N,\"form\",\"optimal form\",\"min poly\",\"partial obstructions\",
	class number,r,no ideal eq,no Thue eq,\"a values\",\"primelist\"".
Returns
    OutFile: MonStgElt
        A .csv file named "N,[optimal form]Out.csv" containing, for each
	elliptic curve E, the row
	"N,aInvariants(E),optimal form,a,primelist,sol". If there are no
	elliptic curves corresponding to this set, no such file is created.
    LogFile: MonStgElt
        A .txt file named "N,[optimal form]Log.txt" containing
	all output, timings, and solutions.
Authors
    Adela Gherga <adelagherga@gmail.com>
Created
    24 August 2022
*/

ChangeDirectory("./Code");
load "./solveThueMahler.m";
load "./convertTMToEllipticCurves.m";

seqEnumToString:=function(X : quotes:=false)
    /*
      Convert a SeqEnum into a string without whitespace, enclosed by "[ ]" for
      .csv input

      Parameters
          X: SeqEnum
          quotes: BoolElt
              A true/false vale. If set to true, encloses the output in
	      quotations.
      Returns
          stX: MonStgElt
	      The set X as a string without whitespace.
   */
    strX:= "[";
    for i in [1..#X] do
	if X[i] in Integers() then
	    strX:=strX cat IntegerToString(Integers()!X[i]);
	elif X[i] in Rationals() then
	    strX:=strX cat IntegerToString(Numerator(X[i])) cat "/" cat
		  IntegerToString(Denominator(X[i]));
	end if;
	if (i ne #X) then
	    strX:=strX cat ",";
	end if;
    end for;
    strX:=strX cat "]";
    if quotes then
	strX:="\"" cat strX cat "\"";
    end if;
    return strX;
end function;

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
alist:=[StringToInteger(i) : i in Split(RBracketSplit[4],",")];
if (#RBracketSplit eq 11) then
    assert CommaSplit[14] eq "None";
    aconsts:=[StringToInteger(i) : i in Split(RBracketSplit[8],",")];
    primelist:=[StringToInteger(i) : i in Split(RBracketSplit[10],",")];
else
    aconsts:=[StringToInteger(i) : i in Split(RBracketSplit[10],",")];
    primelist:=[StringToInteger(i) : i in Split(RBracketSplit[12],",")];
end if;
OutFile:="../Data/TMOutfiles/" cat
	 CommaSplit[1] cat "\,\[" cat RBracketSplit[4] cat "\]Out.csv";
LogFile:="../Data/TMLogfiles/" cat
	 CommaSplit[1] cat "\,\[" cat RBracketSplit[4] cat "\]Log.txt";
SetLogFile(LogFile);
for a in aconsts do
    sols:=solveThueMahler(alist,a,primelist : coprime:=false);
    printf "sols:=%o\n",sols;
    ECs:=convertTMToEllipticCurves(N,alist,sols);
    printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
    printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
    printf "N:=%o; alist:=%o; a:=%o; primelist:=%o; \n",N,alist,a,primelist;
    printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
    printf "%o\n",ECs;
    for E in ECs do
	assert E[1] eq N;
	fprintf OutFile, "%o, %o, %o, %o, %o, %o\n",
		N,seqEnumToString(E[2]),seqEnumToString(alist),a,
		seqEnumToString(primelist),seqEnumToString(E[3]);
    end for;
end for;
UnsetLogFile();
