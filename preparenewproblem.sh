#!/bin/bash

cd ~/redsat

if [ "$#" -eq 0 ]; then
	echo "missing problem name"
	exit
fi

NAME="${1}"
mkdir problems/"${NAME}"
cp other/reduccionessat/"${NAME}"/{format,jp,jp2input,input2sat,validator} problems/"${NAME}"/
mkdir -p problems/"${NAME}"/proposals/correct
touch problems/"${NAME}"/proposals/correct/propuestasolucion
cp problems/nreinas/proposals/correct/{answer.cor,answer.long.cor,std.err.cor} problems/"${NAME}"/proposals/correct/
echo "run_problem ${NAME} correct" >> fulltests.sh

echo "copiar propuestasolucion de un envio de la web"
echo "adaptar format, jp2input, input2sat, validator, propuestasolucion"
echo "./run.sh "${NAME}" correct > problems/"${NAME}"/proposals/correct/std.out.cor"