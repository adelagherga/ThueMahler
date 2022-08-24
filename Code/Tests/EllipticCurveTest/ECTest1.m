sets:= ["500004,\"(2,4,4,11)\",\"(3,-12,-8,-2)\",\"(1,-12,-24,-18)\",None,1,1,8,0,\"(2)\",\"(3,17,19,43)\"",
"500004,\"(1,4,8,44)\",\"(1,4,8,44)\",\"(1,4,8,44)\",None,1,1,16,0,\"(1,2)\",\"(3,17,19,43)\"",
"500004,\"(1,6,9,38)\",\"(1,6,9,38)\",\"(1,6,9,38)\",None,1,1,8,0,\"(2)\",\"(17,19,43)\"",
"500004,\"(11,9,15,3)\",\"(3,-15,9,-11)\",\"(1,-15,27,-99)\",None,3,1,4,0,\"(2)\",\"(17,19,43)\"",
"500004,\"(2,5,4,13)\",\"(1,61,44,8)\",\"(1,61,44,8)\",None,1,1,24,0,\"(1,2)\",\"(3,17,19,43)\"",
"500004,\"(6,6,6,11)\",\"(6,6,6,11)\",\"(1,6,36,396)\",None,3,1,8,0,\"(2)\",\"(17,19,43)\"",
"500004,\"(7,12,21,12)\",\"(3,-57,-30,-4)\",\"(1,-57,-90,-36)\",None,1,1,4,0,\"(2)\",\"(17,19,43)\"",
"500004,\"(7,3,15,1)\",\"(1,-15,3,-7)\",\"(1,-15,3,-7)\",None,1,1,4,0,\"(2)\",\"(17,19,43)\"",
"500004,\"(2,1,26,-12)\",\"(17,-34,7,-2)\",\"(1,-34,119,-578)\",None,8,1,15,0,\"(2)\",\"(3,17,19,43)\"",
"500004,\"(3,6,12,44)\",\"(3,6,12,44)\",\"(1,6,36,396)\",None,3,1,8,0,\"(1,2)\",\"(17,19,43)\"",
"500004,\"(7,9,9,19)\",\"(19,-9,9,-7)\",\"(1,-9,171,-2527)\",None,3,1,12,0,\"(1,2)\",\"(17,19,43)\"",
"500004,\"(6,21,24,28)\",\"(19,0,3,-6)\",\"(1,0,57,-2166)\",None,1,1,8,0,\"(1,2)\",\"(17,19,43)\"",
"500004,\"(1,2,53,100)\",\"(1,2,53,100)\",\"(1,2,53,100)\",None,8,1,30,0,\"(1,2)\",\"(3,17,19,43)\"",
"500004,\"(4,6,0,17)\",\"(17,0,6,-4)\",\"(1,0,102,-1156)\",None,1,1,12,0,\"(1,2)\",\"(17,19,43)\"",
"500004,\"(18,15,30,13)\",\"(13,-30,15,-18)\",\"(1,-30,195,-3042)\",None,8,1,14,1,\"(2)\",\"(17,19,43)\""];

for set in sets do

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
	sols:=solveThueMahler(alist,a,primelist : coprime:=false);
	ECs:=convertTMToEllipticCurves(N,alist,sols);
	printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
	printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
	printf "N:=%o; alist:=%o; a:=%o; primelist:=%o; \n",N,alist,a,primelist;
	print ECs;
	for E in ECs do
	    assert E[1] eq N;
	    fprintf "outtest.m", "%o, %o, %o, %o, %o, %o\n",N,E[2],alist,a,primelist,E[3];
	end for;
    end for;
end for;
