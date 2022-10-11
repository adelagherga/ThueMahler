#!/bin/bash
# chmod u+x Code/Tests/runOptions.sh

function usage {
    echo "usage: "
    echo "  $0 N1 [N2]"
    echo "  $0 [-l N1] N2..."
    echo ""
    echo "  Generate elliptic curves having conductors in the range N1 to N2."
    echo "  If N2 is omitted, generate elliptic curves having conductor N1."
    echo ""
    echo "  -l  Generate elliptic curves having conductors in the list"\
	 "[N1,N2,...]."
    1>&2
    exit 1
}

getConductorList() {

    # Parses terminal input and generates the list of conductors to be resolved,
    # along with an appropriate directory name. This function handles a single
    # conductor N, a range of conductors [N1,...,N2], or, with the flag -l, an
    # arbitrary finite list of conductors.

    # Parameters
    #     N1
    #         A single conductor.
    #     N1 N2: [OPTIONAL]
    #         Two conductor values to generate the range [N1,...,N2].
    #     -l Ni: [OPTIONAL]
    #         A single conductor Ni, to be parsed with the flag -l, indicating a
    #         list. This command can be repeated to parse any finite list of
    #         conductors.

    local OPTIND
    local i
    local N1
    local N2
    local Nlist

    while getopts ":l:" opt; do
	case $opt in
	    l)
		# List of conductors.
		list+=("$((10#${OPTARG}))")
		;;
	    \?)
		echo "Invalid option: -${OPTARG}." >&2
		usage
		;;
	    :)
		echo "Option -$OPTARG requires an argument." >&2
		usage
		;;
	esac
    done
    shift $(($OPTIND - 1))

    for i in $@; do
	if ! [[ "$i" =~ ^[0-9]+$ ]]; then
	    echo "Invalid input: positive integers only." >&2
	    usage
	fi
    done
    if [ -z "${list}" ]; then
	if [ $# -eq 1 ]; then
	    N1=$((10#$1))
	    list=(${N1})
	    name="[""${N1}""]"
	elif [ $# -eq '2' ]; then
	    if [ "$1" -eq "$2" ]; then
		N1=$((10#$1))
		list=(${N1})
		name="[""${N1}""]"
	    elif [ "$1" -lt "$2" ]; then
		N1=$((10#$1))
		N2=$((10#$2))
		list=($(seq ${N1} ${N2}))
		name="[""${N1}""..""${N2}""]"
	    else
		echo "Invalid input: N1 must be less than or equal to N2." >&2
		usage
	    fi
	else
	    echo "Invalid input: too many arguments: use option -l." >&2
	    usage
	fi
    else
	for i in $@; do
	    list+=("$((10#$i))")
	done
	printf -v Nlist '%s,' "${list[@]}"
	name="[""${Nlist%,}""]"
    fi
}

generateDirectories() {

    # Generates a directory Data/${name} for all output, as well as all
    # necessary subdirectories and files. If such a directory
    # already exists in Data/, generates a directory Data/${name}i, where
    # Data/${name}j exists for all j < i.

    local iter
    local tmpname
    local N
    Dir="Data/${name}"
    ECDir="${Dir}/EllipticCurves"
    TMOutDir="${Dir}/TMOutfiles"
    TMLogDir="${Dir}/TMLogfiles"

    # Generate Data directory, if it does not already exist.
    if [ ! -d "Data/" ]; then
	mkdir "Data/"
    fi

    # Generate Data/${name} directory.
    if [ ! -d "Data/${name}" ]; then
	mkdir "Data/${name}"
    else
	iter=1
	tmpname="${name}${iter}"
	while [ -d "Data/${tmpname}" ]; do
	    iter=$(( "${iter}" + 1 ))
	    tmpname="${name}${iter}"
	done
	mkdir "Data/${tmpname}"
    fi

    # Generate necessary subdirectories and files.
    mkdir "${ECDir}"
    mkdir "${TMOutDir}"
    mkdir "${TMLogDir}"
    touch "${Dir}/Errors.txt"

    # Generate files for each conductor.
    for N in "${list[@]}"; do
	touch "${ECDir}/${N}.csv"
    done
}

runInParallel() {

    # Runs code in parallel.
    #
    # Parameters
    #     input
    #         The input for gnu parallel.
    #     varName
    #         A variable name for magma.
    #     funcFile
    #         The filename in of the magma function to be run.

    echo "$1" | parallel -j20 --joblog ${Dir}/TMLog magma -b "$2":={} \
			 name:=${name} Code/"$3" 2>&1
}


main () {

    # Establishes run order.

    local N
    local line
    getConductorList "$@"
    generateDirectories

    # Generate all required Thue--Mahler forms in parallel, applying all
    # necessary local tests in the process.
    printf "Generating all required cubic forms for conductors in ${name}..."
    echo ${list[*]}
    runInParallel "$(printf '%s\n' "${list[@]}")" N findForms.m

}

main "$@"
