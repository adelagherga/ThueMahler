/*
PaperEx3.m

This function solves the Thue--Mahler equations defined in the Example 3 of the
GhSi Thue--Mahler paper, and outputs the corresponding logfile.

Returns
    LogFile: MonStgElt
        A .txt file named "Example3Log.txt" containing all output, timings, and
	solutions.
Authors
    Adela Gherga <adelagherga@gmail.com>
    Samir Siksek <samir.siksek@gmail.com>
Created
    14 June 2022
*/

ChangeDirectory("../../TMSolver");
load "./solveThueMahler.m";
LogFile:="../../GhSiData/Example3/Example3Log.txt";
SetOutputFile(LogFile);

//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++//
// Example 3 //

primelist:=[2, 7, 23, 31, 47, 71, 73, 79, 89];
alist:=[1,0,0,0,-2];
time sols:=solveThueMahler(alist,1,primelist);
time sols:=sols join solveThueMahler(alist,-1,primelist);
printf "sols:=%o\n",sols;
printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
printf "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
printf "Total time: %o",Cputime();
exit;
