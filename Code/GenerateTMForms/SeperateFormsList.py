#!/usr/bin/python
# SeperateFormsList.py

# Author: Adela Gherga <adelagherga@gmail.com>
# Copyright © 2021, Adela Gherga, all rights reserved.
# Created: 12 February 2021
#
# Description: This program iterates through each line of the files irred_pos.txt, irred_neg.txt
#              as computed by A. Rechnitzer.
#              It takes as input discF c_1 .. c_4 and outputs on each line of
#              FormsCond10To6_NoN.txt \"(c_1,..,c_4)\"
#
# Commentary:  This program only needs to be applied once.
#              Run with
#              python3 /Users/adela016/Documents/Work/Postdoc/ThueMahler/Code/GenerateTMForms/SeperateFormsList.py > /Users/adela016/Documents/Work/Postdoc/ThueMahler/Data/FormsCond10To6/FormsCond10To6_NoN.txt
#
# To do list:  N/A
#
# Example:     N/A
#

def fargle(X):
    Y = []
    for char in X.split():
        Y.append(int(char))
    return [Y]

pos_forms = {}
neg_forms = {}

for line in open("/Users/adela016/Documents/Work/Postdoc/ThueMahler/Data/FormsCond10To6/Raw/irreduc_pos.txt"):
    conductor = int(line.split()[0])
    if conductor in pos_forms:
        pos_forms[conductor] = pos_forms[conductor] + fargle(line)
    else:
        pos_forms[conductor] = fargle(line)

for line in open("/Users/adela016/Documents/Work/Postdoc/ThueMahler/Data/FormsCond10To6/Raw/irreduc_neg.txt"):
    conductor = -int(line.split()[0])
    if conductor in neg_forms:
        neg_forms[conductor] = neg_forms[conductor] + fargle(line)
    else:
        neg_forms[conductor] = fargle(line)

for key in sorted(pos_forms):
    for form in pos_forms[key]:
        print("\\\"(" + str(form[1:]).replace(" ","").replace("[","").replace("]","") + ")\\\"")

for key in sorted(neg_forms):
    for form in neg_forms[key]:
        print("\\\"(" + str(form[1:]).replace(" ","").replace("[","").replace("]","") + ")\\\"")
