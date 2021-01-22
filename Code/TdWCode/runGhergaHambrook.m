

Attach("/home/adela/ThueMahler/Code/TdWCode/GhergaHambrook.m");
C:=[1,-6,5,-1];
p:= PrimesInInterval(1,41);
A:=1;
FindAll:=true;
LogFile:= "tau3_41log.txt";
OutFile:= "tau3_41out.txt";
sols:= TMAllCases(C,p,A,LogFile,OutFile,FindAll);

for s in sols do
    if (s[1] ne 0) then
	f1:= Factorization(s[1]);
	if #f1 eq 1 and f1[1][2] eq 11 then
	    print s;
	end if;
    end if;
    if (s[2] ne 0) then
	f2:= Factorization(s[2]);
	if #f2 eq 1 and f2[1][2] eq 11 then
	    print s;
	end if;
    end if;
end for;
