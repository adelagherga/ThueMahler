/*
SoydenTM.m

This function solves the Thue--Mahler equations given in Soyden's email and
outputs the logfile and solution data in seperate files.

Returns
    OutFile: MonStgElt
        A .csv file named "SoydenOut.csv" containing, for each Thue--Mahler
	equation, the row "alist,a,primelist,sol". If there are no solutions
	corresponding to this set, no such file is created.
    LogFile: MonStgElt
        A .txt file named "SoydenLog.txt" containing all output, timings, and
	solutions.
Authors
    Adela Gherga <adelagherga@gmail.com>
Created
    10 August 2023
*/

ChangeDirectory("../../TMSolver");
load "./solveThueMahler.m";
LogFile:="../../Data/SoydenLog.txt";
OutFile:="../../Data/SoydenOut.csv";
SetOutputFile(LogFile);

aLists:=[<[1,5,-70,-70,245,49], 32,[7]>, // primelist:=[7];
	 <[1,5,-70,-70,245,49],-32,[7]>,
	 <[1,-15,-70,210,245,-147], 32,[7]>,
	 <[1,-15,-70,210,245,-147],-32,[7]>,
	 <[-1,-25,70,350,-245,-245], 32,[7]>,
	 <[-1,-25,70,350,-245,-245],-32,[7]>,
	 <[-3,5,210,-70,-735,49], 32,[7]>,
	 <[-3,5,210,-70,-735,49],-32,[7]>,
	 <[-1,55,70,-770,-245,539], 32,[7]>,
	 <[-1,55,70,-770,-245,539],-32,[7]>,
	 <[1,-225,-230,10350,2645,-23805], 16384,[23]>, // primelist:=[23];
	 <[1,-225,-230,10350,2645,-23805],-16384,[23]>,
	 <[-45,5005,10350,-230230,-119025,529529], 8388608,[23]>,
	 <[-45,5005,10350,-230230,-119025,529529],-8388608,[23]>,
	 <[1513,-110025,-347990,5061150,4001885,-11640645], 4294967296,[23]>,
	 <[1513,-110025,-347990,5061150,4001885,-11640645],-4294967296,[23]>,
	 <[-45045,2388565,10360350,-109873990,-119144025,252710177], 2199023255552,[23]>,
	 <[-45045,2388565,10360350,-109873990,-119144025,252710177],-2199023255552,[23]>,
	 <[1252369,-51152625,-288044870,2353020750,3312516005,-5411947725],
	  1125899906842624,[23]>,
	 <[1252369,-51152625,-288044870,2353020750,3312516005,-5411947725],
	  -1125899906842624,[23]>,
	 <[-7,-115,2170,7130,-33635,-22103], 16384,[31]>, // primelist:=[31];
	 <[-7,-115,2170,7130,-33635,-22103],-16384,[31]>,
	 <[161,-2475,-49910,153450,773605,-475695], 8388608,[31]>,
	 <[161,-2475,-49910,153450,773605,-475695],-8388608,[31]>,
	 <[-119,115805,36890,-7179910,-571795,22257721], 4294967296,[31]>,
	 <[-119,115805,36890,-7179910,-571795,22257721],-4294967296,[31]>,
	 <[-79695,-1396315,24705450,86571530,-382934475,-268371743], 2199023255552,[31]>,
	 <[-79695,-1396315,24705450,86571530,-382934475,-268371743],-2199023255552,[31]>,
	 <[1893913,-27176915,-587113030,1684968730,9100251965,-5223403063],
	  1125899906842624,[31]>,
	 <[1893913,-27176915,-587113030,1684968730,9100251965,-5223403063],
	  -1125899906842624,[31]>];

for set in aLists do
    alist:=set[1];
    a:=set[2];
    primelist:=set[3];
    printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
    printf "alist:=%o; a:=%o; primelist:=%o;\n",alist,a,primelist;
    printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
    sols:=solveThueMahler(alist,a,primelist : coprime:=false);
    printf "sols:=%o\n",sols;
    for sol in sols do
	fprintf OutFile, "%o %o %o %o\n",seqEnumToString(alist),
		IntegerToString(a),seqEnumToString(primelist),
		seqEnumToString(sol);
    end for;
end for;
printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
printf "Total time: %o",Cputime();
exit;
