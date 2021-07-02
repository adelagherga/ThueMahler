#!/usr/bin/python
# GatherRedundancy_ThueEq.py

# Author: Adela Gherga <adelagherga@gmail.com>
# Copyright © 2021, Adela Gherga, all rights reserved.
# Created: 14 June 2021
#
# Description: This program iterates through each line of "RegeneratedThueEqToSolve.csv", as
#              computed by "RegeneratedThueEqToSolve_NoSUnitEqNeeded.m" and
#              "RegeneratedThueEqToSolve_TMFormData.m", and generates a list of all unique Thue
#              equations to solve, removing the redundancy present in the aforementioned files.
#              The output is
#
#              "RegeneratedThueEqToSolve.csv" lists all Thue forms to be solved in the format
#              N,"form","optimal form","RHSlist", where the same form and right-hand-side may
#              appear for multiple conductors. This algorithm removes this redundancy.
#
#              The output is printed in the files "ThueEqToSolve_ByRHS.csv" in the format
#              (original) "form",rhs_value,"list of conductors"
#              and "ThueEqToSolve_ByForm.csv" in the format
#              (original) "form",rhs_value
#              Here "ThueEqToSolve_ByRHS.csv" is generated for processing repetitions among
#              conductors, and is not used to solve the Thue equations as it requires
#              reinitializing the same form (and magma) for each rhs value
#
# Commentary:  We ignore the "optimal form" here as it is only optimal in regards to the
#              associated number of S-unit equations, and simply use the original form instead.
#
#              This program only needs to be appli once. Run with
#              python3 /home/adela/ThueMahler/Code/GenerateSUnitEquations/GatherRedundancy_ThueEq.py
#
# To do list:
#
# Example:
#

# seperate all lines of Thue data by (original) "form"
def fragle(line):
    line_list = line.split("\"")
    form = line_list[1]
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
