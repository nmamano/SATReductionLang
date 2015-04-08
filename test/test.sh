#!/bin/bash
cd ~/redsat/test
rm -f juezejecutable
(cd ~/redsat && make && cp juezejecutable test)


function run_problem {
    local problem=$1
	echo "${problem}"

	rm -f answer answer.long std.out std.err

	f=../problemas/"${problem}"/
	./juezejecutable "${f}"jp "${f}"jp2input "${f}"input2sat "${f}"propuestasolucion "${f}"validator "${f}"format > std.out 2> std.err
	echo "diff answer answer.cor"
	diff answer answer.cor
	echo "diff answer.long answer.long.cor"
	diff answer.long answer.long.cor
	#diff std.out std.out.cor
	diff std.err std.err.cor   

}

run_problem nreinas
run_problem horarios
