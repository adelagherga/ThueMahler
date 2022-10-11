#!/bin/bash
# chmod u+x Code/Tests/runOptions.sh


getConductorList() {

    # Parses terminal input and generates the list of conductors to be resolved,
    # along with an appropriate directory name. This function handles a single
    # conductor N, a range of conductors [N1,...,Nn], or, with the flag -l, an
    # arbitrary finite list of conductors.

    # Parameters
    #     N1
    #         A single conductor.
    #     N1 Nn: [OPTIONAL]
    #         Two conductor values to generate the range [N1,...,Nn].
    #     -l Ni: [OPTIONAL]
    #         A single conductor Ni, to be parsed with the flag -l, indicating a
    #         list. This command can be repeated to parse any finite list of
    #         conductors.
    # Returns
    #

    local OPTIND
    local Nlist
    while getopts ":l:" opt; do
	case $opt in
	    l)
		# List of conductors.
		list+=("$((10#${OPTARG}))")
#		name+="${OPTARG}"
#		name="["${list//${IFS:0:1}/,}"]"
		;;
	    \?)
		echo "Invalid option: -${OPTARG}." >&2
		exit 1 ;;
	    :)
		echo "Option -$OPTARG requires an argument." >&2
		exit 1 ;;
	esac
    done
    shift $(($OPTIND - 1))


    for i in $@; do
	if ! [[ "$i" =~ ^[0-9]+$ ]]; then
	    echo "Invalid input: integers only."
	    exit 1
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
		echo "error"
		exit 1
	    fi
	else
	    echo "error"
	    exit 1
	fi
    else
	for i in $@; do
	    list+=("$((10#$i))")
	done
	printf -v Nlist '%s,' "${list[@]}"
	name="[""${Nlist%,}""]"
    fi

}

main () {

    # Establishes run order.

    local N
    local line
    getConductorList "$@"
    printf "Generating all required cubic forms for conductors in ${name}..."
    echo ${list[*]}
}

main "$@"
