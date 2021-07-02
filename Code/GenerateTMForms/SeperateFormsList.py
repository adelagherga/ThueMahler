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
    for char in X.split()[1:]:
        Y.append(int(char))
    return tuple(Y)

all_forms = set()

for line in open("/Users/adela016/Documents/Work/Postdoc/ThueMahler/Data/FormsCond10To6/Raw/irreduc_pos.txt"):
    all_forms.add(fargle(line))

for line in open("/Users/adela016/Documents/Work/Postdoc/ThueMahler/Data/FormsCond10To6/Raw/irreduc_neg.txt"):
    all_forms.add(fargle(line))

all_forms = sorted(all_forms)

for form in all_forms:
    print(str(form).replace(" ",""))
