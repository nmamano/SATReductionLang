#!/bin/bash

if [ "$#" -eq 0 ]; then
	echo "missing problem name"
	exit
fi

f="problems/${1}/"

if [ "$#" -eq 1 ]; then
	fproposal="${f}proposals/correct/"
	dbg=""
fi

if [ "$#" -eq 2 ]; then
	if [ "${2}" == "-d" ]; then
		fproposal="${f}proposals/correct/"
		dbg="-d"
	else
		fproposal="${f}proposals/${2}/"
		dbg=""
	fi
fi

if [ "$#" -eq 3 ]; then
	fproposal="${f}proposals/${2}/"
	dbg="-d"
fi

s="./juezejecutable ${dbg} ${f}jp ${f}jp2input ${f}input2sat ${fproposal}propuestasolucion ${f}validator ${f}format"
echo "${s}"
eval "${s}"
