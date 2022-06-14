/*

PIRLtest.m

Author: Adela Gherga <adelagherga@gmail.com>
Copyright © 2021, Adela Gherga, all rights reserved.
Created: 19 July 2021

Description: This program runs "tmpackAllCasesChanges1001.m" on various sets in
	     "ObsRegeneratedTMFormData.csv". The output will be used to ensure that the PIRL
	     applied to a-values is correct and that no solutions are missing. All output is
	     printed in "PIRLtestout.txt" and "PIRLtestlog.txt".

Commentary:  Run with
             nohup magma /home/adela/ThueMahler/Code/Tests/PIRLtest.m &

To do list:

Example:

*/

Attach("/home/adela/ThueMahler/Code/TdWCode/tmpackAllCasesChanges1001.m");

clist:= [24,1,16,15];
p:= [2,5,7,27061];
A:= 1;
LogFile:= "/home/adela/ThueMahler/Data/Tests/PIRLtest4log.txt";
OutFile:= "/home/adela/ThueMahler/Data/Tests/PIRLtest4out.txt";

TMAllCases(clist,p,A,LogFile,OutFile,true);
exit;
