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
		list+=("${OPTARG}")
		name+="${OPTARG}"
		name="["${list//${IFS:0:1}/,}"]"
		;;
	    \?)
		echo "Invalid option: -${OPTARG}." >&2
		exit 1 ;;
	    :)
		echo "Option -$OPTARG requires an argument." >&2
		exit 1 ;;
	esac
    done

    echo $#
    if [ -z "${list}" ]; then
	if [ $# -eq 0 ]; then
	    echo "Argument required." >&2
	    exit 1
	fi
	if [ $# -eq 1 ]; then
	    list=($1)
	    name="[$1]"
	elif [ $# -eq '2' ]; then
	    list=($(seq $1 $2))
	    name="[$1..$2]"
	else
	    echo "Invalid argument."
	    exit 1
	fi
    else
	if [ $# -gt 0 ]; then
	    echo "wtf"
	    exit 1
	fi
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
