#!/bin/bash
cd ~/redsat/test


#make sure we are running the "actual" version of the judge
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

	#the test failed if either answer.long or std.out differs
	if [[ $(diff -q answer.long ${fproposal}answer.long.cor) ]] || [[ $(diff -q std.out ${fproposal}std.out.cor) ]]; then
		echo "===== FAILED TEST ====="
		echo ">>>> diff std.out std.out.cor"
		diff std.out "${fproposal}std.out.cor"
		echo ">>>> diff std.err std.err.cor"
		diff std.err "${fproposal}std.err.cor"
		echo ">>>> diff answer answer.cor"
		diff answer "${fproposal}answer.cor"
		echo ">>>> diff answer.long answer.long.cor"
		diff answer.long "${fproposal}answer.long.cor"

		#execute again with debug flag, save output in test/dbg
		./juezejecutable -d "${f}"jp "${f}"jp2input "${f}"input2sat "${fproposal}"propuestasolucion "${f}"validator "${f}"format > dbg 2> /dev/null

		#dont continue running tests
		exit
	fi
	
	#if the test doesn't fail, don't print anything
	#if the test fails, the output files are not removed so they can be inspected
	rm -f answer answer.long std.out std.err
}

run_problem minitest correct
run_problem minitest scopeexpressions
run_problem minitest reconexpressions
run_problem "test" correct
run_problem "test" scopeexpressions
run_problem "test" emptyscopeexpressions
run_problem "test" reconexpressions
run_problem "test" varwithdash
run_problem "test" showred
run_problem sudoku correct #does not contain cardinality constraints
run_problem nreinas correct
run_problem nreinas badred
run_problem nreinas badrec
run_problem nreinas mirrorrec
run_problem nreinas writetoin
run_problem nreinas readfromout
run_problem nreinas varnamedout
run_problem horarios correct
run_problem horarios showred
run_problem ligadeportiva correct
run_problem horariodetrenes correct
run_problem cancionukelele correct
run_problem networkalignment correct
