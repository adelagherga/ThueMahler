#!/bin/bash
# $ chmod u+x Code/computeEllipticCurves.sh


while getopts ":l:" opt; do
    case $opt in
	l)
	    # List of conductors.
	    list+=("$OPTARG")
	    ;;
	\?)
	    echo "Invalid option: -$OPTARG." >&2
	    exit 1 ;;
	:)
	    echo "Option -$OPTARG requires an argument." >&2
	    exit 1 ;;
    esac
done
if [ -z "${list}" ]; then
    if [ $# -eq 0 ]; then
	echo "Argument required." >&2
	exit 1
    fi
    if [ $# -eq 1 ]; then
	list=($1)
    elif [ $# -eq '2' ]; then
	list=($(seq $1 $2))
    else
	echo "Invalid argument." >&2
	exit 1
    fi
fi
for N in "${list[@]}"; do
    echo "Data/EllipticCurves/${N}.csv"
done
