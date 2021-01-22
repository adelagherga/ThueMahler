#!/bin/bash
# GatherKilledForms.sh

# Author: Adela Gherga <adelagherga@gmail.com>
# Copyright © 2021, Adela Gherga, all rights reserved.
# Created: 21 January 2021
#
# Description: Finds all killed jobs in GNU parallel joblog generated from GenerateSUnitEq.m
#
# Commentary:
#
# To do list:
#
# Example:
#

cd /home/adela/ThueMahler/Data/SUnitEqData

#Organize TMFiles JobLogTime files
{ cat tmplog; echo; } | while read line; do
    set=$(echo $line | awk '{print $10 }')
    set=${set//"set:="/}
    signal=$(echo $line | awk '{print $8 }')
    if [[ "$signal" != 0 ]]; then
	echo $set"t"$signal >> tmpKilledJobs
    fi
done
column -t -s't' tmpKilledJobs > KilledJobs
