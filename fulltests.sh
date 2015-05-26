#!/bin/bash
cd ~/redsat/test
rm -f juezejecutable
(cd ~/redsat && make && cp juezejecutable test)


function run_problem {
    local problem=$1
    local proposal=$2
	echo "${problem} ${proposal}"

	rm -f answer answer.long std.out std.err

	f="../problems/${problem}/"
	fproposal="${f}proposals/${proposal}/"
	./juezejecutable "${f}"jp "${f}"jp2input "${f}"input2sat "${fproposal}"propuestasolucion "${f}"validator "${f}"format > std.out 2> std.err
	echo "diff answer answer.cor"
	diff answer "${fproposal}answer.cor"
	echo "diff answer.long answer.long.cor"
	diff answer.long "${fproposal}answer.long.cor"
	echo "diff std.out std.out.cor"
	diff std.out "${fproposal}std.out.cor"
	echo "diff std.err std.err.cor"
	diff std.err "${fproposal}std.err.cor"   
}

run_problem nreinas correct
run_problem horarios correct
