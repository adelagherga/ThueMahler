#!/usr/bin/env bash

# compile the loops that build forms
g++ pos_forms.cpp -O9 -lgsl -o pos.out
g++ neg_forms.cpp -O9 -lgsl -o neg.out

# pipe the output of those loops through some sorting (not strictly needed, but doesnt take long)
./pos.out | sort -k1n > forms_pos.txt
./neg.out | sort -k1n > forms_neg.txt

# now need to check if forms are factorable or not - pipe through sage.
# You'll need to tweak the path to sage for your machine

~/Apps/SageMath/sage factorCheck.sage forms_pos.txt > irreduc_pos.txt
~/Apps/SageMath/sage factorCheck.sage forms_neg.txt > irreduc_neg.txt

# Now put things together
python3 ./conductorForms.py > requiredForms.txt
