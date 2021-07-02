#!/usr/bin/python
# GatherRedundancy_TMEq.py

# Author: Adela Gherga <adelagherga@gmail.com>
# Copyright © 2021, Adela Gherga, all rights reserved.
# Created: 15 June 2021
#
# Description:
#
# Commentary:
#
# To do list:
#
# Example:
#

# format is
# "75,\"(2,2,4,1)\",\"(2,2,4,1)\",\"(1,2,8,4)\",None,1,1,4,4,\"(1,5,8,40)\",\"(3)\""
# "461084,\"(2,0,16,5)\",\"(13,22,6,2)\",\"(1,22,78,338)\",\"(3)\",3,1,6,0,\"(2)\",\"(13,8867)\""
# "512600,\"(1,2,4,4)\",\"(1,2,4,4)\",\"(1,2,4,4)\",\"(3,5)\",1,1,4,0,\"(1,2)\",\"(5,11,233)\""
# "512610,\"(4,7,10,12)\",\"(12,-10,7,-4)\",\"(1,-10,84,-576)\",None,1,1,12,0,\"(1)\",\"(2,3,5,7,2441)\""

# N,"form","optimal form","min poly","partial obstructions",class number,r,no ideal eq,
# no Thue eq,"a values","primelist"



# seperate all lines of Thue-Mahler data by (original) "form"
def fragle(line):
    line_list = line.split("\"")
    assert (len(line_list) == 11) or (len(line_list) == 13)
    form = line_list[1]

    new_line = [line_list[0].split(",")[0]]
    new_line += [i for i in line_list[2:6] if (i != ',') and (i != "")]

    if len(line_list) == 11:
        assert line_list[6].split(",")[1] == "None"
        new_line += [line_list[6].split(",")[1]] + [line_list[6][6:-1]]
    else:
        new_line += [line_list[7]] + [line_list[8][1:-1]]
    new_line += [line_list[-4]] + [line_list[-2]]
    return form, new_line

# process csv input to determine partial obstructions, class number, r
# 3, 4[0], 4[1]

def extract_field_info(line):
    if line[3] == 'None':
        partial_obstruction = []
    else:
        partial_obstruction = [int(i) for i in line[3][1:-1].split(",")]
    class_number = int(line[4].split(",")[0])
    r = int(line[4].split(",")[1])
    return partial_obstruction,class_number,r


# seperate all lines of Thue-Mahler data by (original) "form"
all_forms = {}
for line in open("/Users/adela016/Desktop/RegeneratedTMFormData.csv"):
    form, new_line = fragle(line)
    partial_obstruction,class_number,r = extract_field_info(new_line)
    if partial_obstruction != []:
        if form in all_forms:
            all_forms[form].append(new_line)
        else:
            all_forms[form] = [new_line]


# iterate through each Thue-Mahler form to ensure to ensure that all partial obstructions, class numbers, r values are the same
for key in sorted(all_forms):
    for form in all_forms[key]:
        extract_field_info(form)


primes = [7,13,19,37,61,67,73,79,97,103,139,151,163,181,193,199,211,241,271,313,331,337,349,367,373,379]

for prs in all_forms['(1,3,3,3)']:
    ps= [int(i) for i in prs[6][1:-1].split(",")]
    for p in ps:
        if p in primes:
            print(prs)





    optimal_form = line_list[3]
    min_poly = line_list[5]

    if len(line_list) == 11:
        partial_obstruction = line_list[6].split(",")[1]
        assert partial_obstruction == 'None'
    else:
        partial_obstruction = line_list[7]


    partial_obstruction = line_list[
    new_line = [line_list[0].split(",")[0], line_list[3], line_list[5]]
    return form, new_line

# process csv input to determine all conductors, N, and rhs values per line
def extract_rhs(line):
    line_list = line[2].replace("(","").replace(")","").split(",")
    rhs = [int(i) for i in line_list]
    N = int(line[0])
    return N, rhs;

# process python data for output into csv file as
# "(original) form",rhs value,"list of conductors"
def print_format(output,rhs,Nset):
    output = output + str(rhs) + ",\"" + str(Nset) + "\""
    return output.replace(" ","")

# seperate all lines of Thue data by (original) "form"
all_forms = {}
for line in open("/home/adela/ThueMahler/Data/SUnitEqData/RegeneratedThueEqToSolve.csv"):
    form, new_line = fragle(line)
    if form in all_forms:
        all_forms[form].append(new_line)
    else:
        all_forms[form] = [new_line]

# sort data in a dictionary as (original) "form": rhs value : [N values]
all_forms_rhs = {}
for key in sorted(all_forms):
    all_forms_rhs[key] = {}
    for form in all_forms[key]:
        N,rhs = extract_rhs(form)
        for r in rhs:
            if r in all_forms_rhs[key]:
                all_forms_rhs[key][r].append(N)
            else:
                all_forms_rhs[key][r] = [N]

# output all data to "ThueEqToSolve_ByRHS.csv", in the format
# (original) "form",rhs-value,"list of conductors"
ThueEqToSolve_ByRHS=open("/home/adela/ThueMahler/Data/SUnitEqData/ThueEqToSolve_ByRHS.csv",
                         "w")
for form in sorted(all_forms_rhs):
    output0 = "\"" + form + "\","
    for rhs in sorted(all_forms_rhs[form]):
        output = print_format(output0,rhs,all_forms_rhs[form][rhs])
        ThueEqToSolve_ByRHS.write("%s\n" % output)
ThueEqToSolve_ByRHS.close()

# output all data to "ThueEqToSolve_ByForm.csv" in the format
# (original) "form",rhs-value
ThueEqToSolve_ByForm=open("/home/adela/ThueMahler/Data/SUnitEqData/ThueEqToSolve_ByForm.csv",
                          "w")
for form in sorted(all_forms_rhs):
    output = "\"" + form + "\",\"" + str(sorted(all_forms_rhs[form])).replace(" ","") + "\""
    ThueEqToSolve_ByForm.write("%s\n" % output)
ThueEqToSolve_ByForm.close()
