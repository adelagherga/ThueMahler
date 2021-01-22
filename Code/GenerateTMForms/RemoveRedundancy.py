#!/usr/bin/python
# RemoveRedundancy.py

# Author: Adela Gherga <adelagherga@gmail.com>
# Copyright © 2020, Adela Gherga, all rights reserved.
# Created:  2 December 2020
#
# Description: This program iterates through each line of the files irred_pos.txt,
#              irred_neg.txt, as compute by as computed by A. Rechnitzer.
#              It takes as input discF c_1 .. c_4 and outputs
#              on each line of FormsCond10To6.txt
#              N [disc(F),c_1,..,c_4]
#
# Commentary:
#
# To do list:
#
# Example:
#




#
# Description: This program iterates through each line of the files irred_pos.txt,
#              irred_neg.txt, as compute by as computed by A. Rechnitzer.
#              It takes as input discF c_1 .. c_4 and outputs
#              on each line of FormsCond10To6.txt
#              N [disc(F),c_1,..,c_4]
#
# Commentary: This program only needs to be applied once.
#             Run with
#             python3 /Users/adela016/Documents/Work/Postdoc/ThueMahler/Code/GenerateTMForms/conductorForms.py > /Users/adela016/Documents/Work/Postdoc/ThueMahler/Data/FormsCond10To6/FormsCond10To6.txt
#
# To do list: N/A
#
# Example: N/A
#

import re

class Form:
    def __init__(self,line):
        self.N = int(line.split(',')[0]) # convert bash input N into an integer
        clist, optimal_clist, fclist, partial_obstruction = self.parse_line(line)
        self.clist = clist
        self.optimal_clist = optimal_clist
        self.fclist = fclist

    def parse_line(self,line):
        bracket_split = re.split('[\[\]]', line)
        r_bracket_split = re.split('[\(\)]', line)
        assert (len(bracket_split) == 3) or (len(bracket_split) == 5)
        assert (len(r_bracket_split) == 7)
        if len(bracket_split) == 3:
            assert comma_split[13] == 'None'
            partial_obstruction = []
        else:
            partial_obstruction = [int(i) for i in bracket_split[1].split(',')]
        clist = [int(i) for i in r_bracket_split[1].split(',')]
        optimal_clist = [int(i) for i in r_bracket_split[3].split(',')]
        fclist = [int(i) for i in r_bracket_split[5].split(',')]
        return clist, optimal_clist, fclist, partial_obstruction












for line in open("/Users/adela016/Documents/Work/Postdoc/ThueMahler/Data/SUnitEqData/TMFormData.csv"):
    print(Form(line).N)
    print(Form(line).partial_obstruction)






import sys
import itertools
import sympy
import numpy

def exponents(N,DiscF,N_factors,DiscF_factors):
    N_primes = sorted(N_factors)
    DiscF_primes = sorted(DiscF_factors)

    if 2 in N_primes:
        alpha = N_factors[2]
    else:
        alpha = 0
    if 3 in N_primes:
        beta = N_factors[3]
    else:
        beta = 0

    if 2 in DiscF_primes:
        alpha0 = DiscF_factors[2]
    else:
        alpha0 = 0
    if 3 in DiscF_primes:
        beta0 = DiscF_factors[3]
    else:
        beta0 = 0

    N0 = int( N/((2**alpha)*(3**beta)))
    N1 = abs(int(DiscF/((2**alpha0)*(3**beta0))))

    N0_factors = {k:v for k,v in N_factors.items() if k not in {2,3}}
    N1_factors = {k:v for k,v in DiscF_factors.items() if k not in {2,3}}
    N0_primes = sorted(N0_factors)
    N1_primes = sorted(N1_factors)

    assert alpha in range(0,9)
    assert beta in range(0,6)
    assert N0 % N1 == 0
    prime_bounds = [[],[]]

    # verify behaviour at p = 2
    if (alpha == 0):
        if (alpha0 == 2):
            prime_bounds[0].append([2,0])
            prime_bounds[0].append([2,3])
    elif (alpha == 1):
        if (alpha0 == 2):
            prime_bounds[0].append([2,4,"+"])
        elif (alpha0 == 3):
            prime_bounds[0].append([2,3,"+"])
    elif (alpha == 2):
        if (alpha0 == 2):
            prime_bounds[0].append([2,1])
        elif (alpha0 == 4):
            prime_bounds[0].append([2,0])
            prime_bounds[0].append([2,1])
    elif (alpha == 3):
        if (alpha0 == 2):
            prime_bounds[0].append([2,1])
            prime_bounds[0].append([2,2])
        elif (alpha0 == 3):
            prime_bounds[0].append([2,2]);
        elif (alpha0 == 4):
            prime_bounds[0].append([2,0]);
            prime_bounds[0].append([2,1]);
    elif (alpha == 4):
        if (alpha0 == 2):
            prime_bounds[0].append([2,0,"+"])
        elif (alpha0 == 3):
            prime_bounds[0].append([2,2,"+"])
        elif (alpha0 == 4):
            prime_bounds[0].append([2,0])
            prime_bounds[0].append([2,1])
    elif (alpha == 5):
        if (alpha0 == 2):
            prime_bounds[0].append([2,0])
        elif (alpha0 == 3):
            prime_bounds[0].append([2,1])
    elif (alpha == 6):
        if (alpha0 == 2):
            prime_bounds[0].append([2,0,"+"])
        elif (alpha0 == 3):
            prime_bounds[0].append([2,1,"+"])
        elif (alpha0 == 4):
            prime_bounds[0].append([2,0])
            prime_bounds[0].append([2,1])
    elif (alpha == 7):
        if (alpha0 == 3):
            prime_bounds[0].append([2,0])
        elif (alpha0 == 4):
            prime_bounds[0].append([2,0])
    elif (alpha == 8):
        if (alpha0 == 3):
            prime_bounds[0].append([2,1])

    # verify behaviour at p = 3
    if (beta == 0):
        if (beta0 == 0):
            prime_bounds[1].append([3,0])
    elif (beta == 1):
        if (beta0 == 0):
            prime_bounds[1].append([3,1,"+"])
        elif (beta0 == 1):
            prime_bounds[1].append([3,0,"+"])
    elif (beta == 2):
        if (beta0 == 0):
            prime_bounds[1].append([3,0,"+"])
        elif (beta0 == 1):
            prime_bounds[1].append([3,0,"+"])
        elif (beta0 == 3):
            prime_bounds[1].append([3,0])
    elif (beta >= 3):
        if (beta0 == beta):
            prime_bounds[1].append([3,0])
            prime_bounds[1].append([3,1])
        else:
            # when all coefficients of the form F_1 are  divisible by 3,
            # since also beta1 = {0,1} and 3|LHS we must have that 3|RHS,  hence beta1 = 1
            # in this case, we may divide 3 from both sides
            # this yields the form F = F_1/3, whose discriminant has
            # Valuation(DiscF,3) != beta0 = beta
            # thus since beta1=1 is divided out, so beta1=0
            prime_bounds[1].append([3,0])

    assert (prime_bounds[0] != []) and (prime_bounds[1] != [])

    # verify behaviour at primes dividing N1
    for p in N1_primes:
        if N1_factors[p] >= 2:
            assert N0 % p == 0
            prime_bounds.append([])
            prime_bounds[len(prime_bounds)-1].append([p,0])
            prime_bounds[len(prime_bounds)-1].append([p,1])
    return prime_bounds,N0_primes

def sort_N(DF,forms,all_N_factors):
    Nf = 1.0*1000*1000
    DiscF_factors = sympy.factorint(DF*4)
    a0 = twos[DF]
    b0 = threes[DF]
    N1 = noTwoThree(DF, a0, b0)
    DF_info = {}
    DF_obstructions = {}
    for k in range(1, int(Nf / N1) + 1):
        N = N1 * k
        a = twos[N]
        b = threes[N]
        if a_okay(a, a0) and b_okay(b, b0):
            N_factors = all_N_factors[N]
            prime_bounds,prime_list = exponents(N,DF*4,N_factors,DiscF_factors)
            all_local_obstructions = []
            new_forms = []
            for F in forms:
                local_obstruction = local_test(F,DF*4,N_factors)
            print(N)



                if local_obstruction == []:
                    new_forms.append(F)
                else:
                    all_local_obstructions.append([N,F,local_obstruction[0]])
            if new_forms != []:
                DF_info[N] = [N,new_forms,prime_bounds,prime_list]
            if all_local_obstructions != []:
                DF_obstructions[N] = all_local_obstructions
# need to figure out if we can remove local_obstruction test
# then remove redundancy as we do below
    return






    DiscF = 4*F[0]
    local_obstruction = local_test(F,DiscF,N_factors)
    if local_obstruction != []:
        return local_obstruction,[],[]

    # determine all exponent bounds
    prime_bounds,prime_list = exponents(N,DiscF,N_factors,DiscF_factors)
    return [],prime_bounds,prime_list




    # generate all combinations of exponent restrictions as determined above
    Sdata = list(itertools.product(*prime_bounds) # store all combinations of prime bounds
    aprimelist = [] # store corresponding a value and primelist
    for pset in Sdata:
        a = 1
        primes = list(prime_list)
        for x in pset:
            if len(x) == 3:
                if x[0] not in primes:
                    assert (x[0] == 2) or (x[0] == 3)
                    assert (x[0] not in all_forms[i][1])
                    primes.append(x[0])
            else:
                if x[0] in primes:
                    primes.remove(x[0])
                a = a*(x[0]**x[1])
        primes.sort()
        if [a,primes] not in aprimelist:
            aprimelist.append([a,primes])

    # store Thue-Mahler equations to be solved
    # store corresponding Thue equations to be solved, if any
    remaining_cases = aprimelist

    RHS_list = []
        for pset in aprimelist:
            if pset[1] == []: # no unbounded primes
                rhs = pset[0]
                if rhs not in RHS_list:
                    RHS_list.append(rhs)
                remaining_cases.remove(pset)

        # remove Thue cases covered by Thue-Mahler cases
        RHS_list_new = deepcopy(RHS_list)
        for a in RHS_list:
            afactors = sympy.factorint(a)
            aprimes = sorted(afactors)
            for pset in remaining_cases:
                if pset[1] != []:
                    b = pset[0]
                    primelist = pset[1]
                    bfactors = sympy.factorint(b)
                    bprimes = sorted(bfactors)
                    check1 = all([p in primelist for p in aprimes if p not in bprimes])
                    check2 = all([bfactors[p] == afactors[p] for p in bprimes])
                    if check1 and check2:
                        assert (a % b == 0)
                        divisors_check = [p for p in aprimes if p in bprimes]
                        divisors_check.extend([p for p in primelist if (p in aprimes and p not in bprimes)])
                        assert aprimes == divisors_check
                        RHS_list_new.remove(a)
                        break
        RHS_list = RHS_list_new

        # store Thue equations to be solved in array as < Thue equation, RHS >, if any
        if (RHS_list != []):
            Thue_eq_to_solve.append([N,all_forms[i],RHS_list])

        # if all cases are resolved via Thue equations
        if remaining_cases == []:
            no_SUnit_eq_needed.append([N,all_forms[i],'None',len(RHS_list)])
            return TM_forms,no_SUnit_eq_needed,no_SUnit_eq_possible, Thue_eq_to_solve

        # if there are Thue-Mahler equations yet to be solved, not resolvable via Thue equations
        # generate the corresponding S-unit equations
        # remove redundancy so that each primeset has all corresponding a values
        remaining_cases_new = []
        remaining_cases_copy = deepcopy(remaining_cases)
        for pset in remaining_cases:

            if pset in remaining_cases_copy:

                a = pset[0]
                primelist = pset[1]
                a_values = [a]
                remaining_cases_copy.remove(pset)
                for pset2 in remaining_cases_copy:
                    a2 = pset2[0]
                    primelist2 = pset2[1]
                    if primelist == primelist2:
                        a_values.append(a2)
                        remaining_cases_copy.remove(pset2)
                a_values.sort()
                remaining_cases_new.append([a_values,primelist])

        assert len(remaining_cases_new) == 1
        remaining_cases = remaining_cases_new[0]
        assert len(remaining_cases) == 2
        form = [tuple(all_forms[i][0]),all_forms[i][1],remaining_cases[0],remaining_cases[1]]
        if form not in TM_forms:
            TM_forms.append(form)

    return TM_forms,no_SUnit_eq_needed,no_SUnit_eq_possible, Thue_eq_to_solve



# determine prime factorization of all integers in (1,..,1000000)
all_N_factors = {}
for N in range(1,1000*1000+1):
    all_N_factors[N] = sympy.factorint(N)

for line in open("/Users/adela016/Documents/Work/Postdoc/ThueMahler/Data/FormsCond10To6/FormsCond10To6.txt"):





                 line = re.sub("\[","",line) # remove all "[" characters
    line = re.sub("\]","",line) # remove all "]" characters
    line_list = [int(x) for x in line.split(',')]
    N = line_list[0]
    DF = line_list[1]*4
    F = line_list[2:]
    local_





for DF in sorted(pos_forms):
    new_forms,all_local_obstructions = sort_N(DF,pos_forms[DF],all_N_factors)






     a = twos[N]
         b = threes[N]
if a_okay(a, a0) and b_okay(b, b0):
         N_factors = all_N_factors[N]



                 print(local_obstruction)
                 print(prime_bounds)
                 print(prime_list)
                 print('----------')
                 # seperate local obstruction for each F; don't need it after that - can just do prime_bounds, prime_list on DF,N only


            print(N)
            for f in o


            TM_forms,no_SUnit_eq_needed,no_SUnit_eq_possible, Thue_eq_to_solve = prep0(N,pos_forms[DF],+1)
            for form in TM_forms:
                if (form[0] in DF_forms):
                    DF_forms[form[0]] = DF_forms[form[0]] + [form[1:]]
                else:
                    DF_forms[form[0]] = [form[1:]]
    DF_forms_new = {}
    for form in sorted(DF_forms):
        for cs in form:
            for ds in form:
                if (set(cs[2]) <= set(ds[2])) and (cs[0] == ds[0]) and (cs[1] == ds[1]):
                    if form in DF_forms_new:
                        DF_forms_new[form]


                    form[3]
            if N in all_forms:
                all_forms[N] = all_forms[N] + TM_forms
            else:
                all_forms[N] = TM_forms

    print(DF)

# 2999484
# 2998431



    # N,"form",local obstruction,partial vs BeGhRe
    # local obstruction, partial vs BeGhRe may be output as p or None
    no_SUnit_eq_possible = []
    # N,"form","optimal form",no Thue eq,
    # "optimal form" may be output as form or None
    no_SUnit_eq_needed = []
    # N,form,Thue eq, RHSlist
    Thue_eq_to_solve = []
    # N,form,local_obstruction,a_values,primelist
    TM_forms = []


x,y = sympy.symbols('x y')
n = 3
F = sum([clist[i]*x**(n-i)*y**i for i in range(0,n+1)])
DiscF= -27*clist[0]**2*clist[3]**2 + clist[1]**2*clist[2]**2
DiscF= DiscF + 18*clist[0]*clist[1]*clist[2]*clist[3]
DiscF= DiscF - 4*clist[0]*clist[2]**3 - 4*clist[1]**3*clist[3]
assert DiscF == DF*4

for clist in pos_forms[DF]:
    F = sum([clist[i+1]*x**(n-i)*y**i for i in range(0,n+1)])
    DiscF= -27*clist[1]**2*clist[4]**2 + clist[2]**2*clist[3]**2;
    DiscF= DiscF + 18*clist[1]*clist[2]*clist[3]*clist[4];
    DiscF= DiscF - 4*clist[1]*clist[3]**3 - 4*clist[2]**3*clist[4];
    assert DiscF == DF*4
    partial_obstruction,local_obstruction = localtest(N0,F,DiscF)
    print(partial_obstruction)
    print(local_obstruction)




for N0 in N0s:
    partial_obstruction,local_obstruction = localtest(N0,F,DiscF)
    if partial_obstruction != []:
        print(N0)
    if local_obstruction != []:
        print("n0")
        print(N0)
        print("--")



#            if N0 in all_forms:
#                all_forms[N0] = all_forms[N0] + pos_forms[DF]
#            else:
#                all_forms[N0] = pos_forms[DF]


for DF in sorted(neg_forms):
    a0 = twos[DF]
    b0 = threes[DF]
    N1 = noTwoThree(DF, a0, b0)
    for k in range(1, int(Nf / N1) + 1):
        N0 = N1 * k
        a = twos[N0]
        b = threes[N0]
        if a_okay(a, a0) and b_okay(b, b0):
            if N0 in all_forms:
                all_forms[N0] = all_forms[N0] + neg_forms[DF]
            else:
                all_forms[N0] = neg_forms[DF]

for key in sorted(all_forms):
    for form in all_forms[key]:
        print( "[" + str(key)+ "," + str(form).replace(" ","") + "]")
