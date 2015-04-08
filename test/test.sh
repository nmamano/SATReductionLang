#!/bin/bash
cd ~/redsat/test
rm -f juezejecutable answer.cat answer.cat.long answer.esp answer.esp.long answer.eng answer.eng.long std.out std.err
(cd ~/redsat && make && cp juezejecutable test)


function run_problem {
    local problem=$1

	rm -f answer.cat answer.cat.long answer.esp answer.esp.long answer.eng answer.eng.long std.out std.err

	f=../problemas/"${problem}"/
	./juezejecutable "${f}"jp "${f}"jp2input "${f}"input2sat "${f}"propuestasolucion "${f}"validator "${f}"format > std.out 2> std.err
	diff answer.cat answer.cat.cor
	diff answer.cat.long answer.cat.long.cor
	diff answer.esp answer.esp.cor
	diff answer.esp.long answer.esp.long.cor
	diff answer.eng answer.eng.cor
	diff answer.eng.long answer.eng.long.cor
	#diff std.out std.out.cor
	diff std.err std.err.cor   

}

run_problem nreinas
run_problem horarios
