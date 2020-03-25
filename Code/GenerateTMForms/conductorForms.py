#!/usr/bin/python
# conductorForms.py

# Author: Adela Gherga <adelagherga@gmail.com>, Andrew Rechnitzer <andrewr@math.ubc.ca>
# Copyright © 2020, Adela Gherga, all rights reserved.
# Created: 17 March 2020
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


import sys

N = 1000 * 1000
Nf = N * 1.0

twos = {}
for k in range(1, 3 * N + 1):
    if k % 2 == 0:
        twos[k] = twos[k / 2] + 1
    else:
        twos[k] = 0
    # print k,twos[k]

threes = {}
for k in range(1, 3 * N + 1):
    if k % 3 == 0:
        threes[k] = threes[k / 3] + 1
    else:
        threes[k] = 0
    # print k,threes[k]


def a_okay(
    a, a0
):  # note that in BeRe a0 is 2 higher, since I factor out 4 from every discrim in my code.
    if a == 0:
        return a0 == 0
    elif a == 1:
        return a0 <= 1
    elif a == 2:
        return a0 == 0 or a0 == 2
    elif a == 3:
        return a0 <= 2
    elif a == 4:
        return a0 <= 2
    elif a == 5:
        return a0 <= 1
    elif a == 6:
        return a0 <= 2
    elif a == 7:
        return a0 == 1 or a0 == 2
    elif a == 8:
        return a0 == 1
    else:
        return 0


def b_okay(b, b0):
    if b == 0:
        return b0 == 0
    elif b == 1:
        return b0 <= 1
    elif b == 2:
        return (b0 == 3) or (b0 <= 1)
    elif b >= 3:
        return b0 == b
    else:
        return 0


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


def noTwoThree(DF, a0, b0):
    return DF // (2 ** a0) // (3 ** b0)


all_forms = {}
for DF in sorted(pos_forms):
    a0 = twos[DF]
    b0 = threes[DF]
    N1 = noTwoThree(DF, a0, b0)
    for k in range(1, int(Nf / N1) + 1):
        N0 = N1 * k
        a = twos[N0]
        b = threes[N0]
        if a_okay(a, a0) and b_okay(b, b0):
            if N0 in all_forms:
                all_forms[N0] = all_forms[N0] + pos_forms[DF]
            else:
                all_forms[N0] = pos_forms[DF]


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
