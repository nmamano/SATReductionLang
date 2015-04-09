#!/bin/bash
f=problemas/"${1}"/

if [ "$#" -eq 0 ]; then
	echo "missing problem name"
fi
if [ "$#" -eq 1 ]; then
	./juezejecutable "${f}jp" "${f}jp2input" "${f}input2sat" "${f}propuestasolucion" "${f}validator" "${f}format"
fi
if [ "$#" -eq 2 ]; then
    ./juezejecutable "-d" "${f}jp" "${f}jp2input" "${f}input2sat" "${f}propuestasolucion" "${f}validator" "${f}format"
fi
