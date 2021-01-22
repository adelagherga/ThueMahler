#!/bin/bash
# GatherKilledForms.sh

# Author: Adela Gherga <adelagherga@gmail.com>
# Copyright © 2021, Adela Gherga, all rights reserved.
# Created: 21 January 2021
#
# Description: Finds all killed jobs in GNU parallel joblog generated from GenerateSUnitEq.m
#
# Commentary:  This program only needs to be executed once. Run with
#              chmod +x GatherKilledForms.sh
#              nohup ./GatherKilledForms.sh &
#
# To do list:  N/A
#
# Example:     N/A
#

cd /home/adela/ThueMahler/Data/SUnitEqData

#Organize TMFiles JobLogTime files
{ cat tmplog; echo; } | while read line; do
    set=$(echo $line | awk '{print $10 }')
    set=${set//"set:="/}
    signal=$(echo $line | awk '{print $8 }')
    if [[ "$signal" != 0 ]]; then
	echo $set | tr -d \' >> tmpKilledJobs # remove symbol ' and print set in temp file
    fi
done

sed '/^[[:space:]]*$/d' tmpKilledJobs >> KilledJobs # remove whitespace lines
rm tmpKilledJobs
