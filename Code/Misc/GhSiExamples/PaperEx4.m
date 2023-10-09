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
LogFile:="../../GhSiData/Example4/Example4Log.txt";
SetOutputFile(LogFile);

//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++//
// Example 4 //

primelist:=[2,3,5,7,11];
a:=1;
alist:=[5,1,4,1,6,1,6,0,6,0,4,-2];
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
