#!/bin/bash
# GatherKilledFormsCheck.sh

# Author: Adela Gherga <adelagherga@gmail.com>
# Copyright © 2021, Adela Gherga, all rights reserved.
# Created: 22 January 2021
#
# Description: Verify all killed jobs in GNU parallel generated from GenerateSUnitEq.m output
#
# Commentary:  This program onle needs to be executed once. Run with
#              chmod +x GatherKilledFormsCheck.sh
#              nohup ./GatherKilledFormsCheck.sh &
#
# To do list:  N/A
#
# Example:     N/A
#

FORMS=/home/adela/ThueMahler/Data/FormsCond10To6/FormsCond10To6.txt
cd /home/adela/ThueMahler/Data/SUnitEqData

{ cat $FORMS; echo } | while read line; do
    # rewrite [N,[discF,c_1,c_2,c_3,c_4]] into N,"(c_1,c_2,c_3,c_4)" format
    set=$(echo $line | sed 's/^.\(.*\).$/\1/' | sed 's/[\[][^,]*,/\"(/' | sed 's/\]/)\"/')

    if (! grep -q ^$set NoSUnitEqNeeded.csv) &&
	   (! grep -q ^$set NoSUnitEqPossible.csv) &&
	   (! grep -q ^$set TMFormData.csv); then
	# print line in new file
	echo $line >> KilledJobs2
    fi
done
