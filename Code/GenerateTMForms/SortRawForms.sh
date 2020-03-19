#!/bin/bash
# GenerateSUnitEquations.sh

# Author: Adela Gherga <adelagherga@gmail.com>
# Copyright © 2020, Adela Gherga, all rights reserved.
# Created: 17 March 2020
#
# Description: This program iterates through each line of the file FormsCond10To6.txt,
#              as computed by A. Rechnitzer.
#              It takes as input N [disc(F_1),c_1,..,c_4],..,[disc(F_n),c_1,..,c_4] and outputs
#              on each line of SortedFormsCond10To6.txt, [N,[disc(F_i),c_1,..,c_4]]
#
# Commentary: This program only needs to be applied once
#
# To do list: N/A
#
# Example: N/A
#

# Description: this is for sortedFormsforCond10to6 (find text)

# runs through every line of FormsCond10To6.txt
{ cat /Users/adela016/Documents/Work/Postdoc/ThueMahler/Data/FormsCond10To6.txt;
  echo; } | while read line; do

    # extract the conductor; ie. the first number before the whitespace
    N=$(echo $line | awk '{print $1;}')
    sets=$(echo $line | awk '{print $2;}')
    echo $sets | awk 'NR>1{print "[" '$N' ",[" $1"]]"}' RS=[ FS=] >> /Users/adela016/Documents/Work/Postdoc/ThueMahler/Data/SortedFormsCond10To6.txt

done
