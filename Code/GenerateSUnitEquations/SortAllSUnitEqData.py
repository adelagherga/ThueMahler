#!/usr/bin/python
# SortAllSUnitEqData.py

# Author: Adela Gherga <adelagherga@gmail.com>
# Copyright © 2020, Adela Gherga, all rights reserved.
# Created: 16 May 2020
#
# Description: This program iterates through the file
#              "/home/adela/ThueMahler/Data/SUnitEqData/AllSUnitEq.txt" and generates the corresponding list of optimal forms to be solved, ignoring those cases for which no sunit equations are needed or where local obstructions occur
#
# Commentary: This program only needs to be applied once.
#             Run with
#             python3 /home/adela/ThueMahler/Code/GenerateSUnitEquations/SortAllSUnitEqData.py > /home/adela/ThueMahler/Data/SUnitEqData/OptimalRequiredSUnitEqs.txt
#
# To do list: 0. write code for optimal forms
#             1. graph data on ranks, time to generate S-unit eqs, size of terms? Possibly in
#                python notebook
#
# Example:
#

def fargle(X):
    Y = []
    for char in X.split():
        Y.append(int(char.replace(",","")))
    return [Y]

import re

optimal_forms = {}
for line in open("/home/adela/ThueMahler/Data/SUnitEqData/AllSUnitEq.txt"):
    if "Optimal Thue-Mahler equation coefficients:" in line:
        form = (re.search('coefficients: \[(.*)\]',line)).group(1)
        N = int((re.search('\[(.*),\[', line)).group(1))
        if N in optimal_forms:
            optimal_forms[N] = optimal_forms[N] + fargle(form)
        else:
            optimal_forms[N] = fargle(form)

for key in sorted(optimal_forms):
    for form in optimal_forms[key]:
        print( "[" + str(key) + "," + str(form).replace(" ","") + "]")
