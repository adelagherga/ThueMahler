
// Here is an example of how to solve a Thue--Mahler equation.
// As an example, take the equation
//
// 3 X^3 + 2 X^2 Y + 7 X Y^2 + 2 Y^3 = 2^{z_1} 3^{z_2} 7^{z_3} 41^{z_4}.

load "ThueMahlerSolver.m";

clist:=[3,2,7,2];
a:=1;
primelist:=[2,3,7,41];
time sols:=solveThueMahler(clist,a,primelist);
sols;

