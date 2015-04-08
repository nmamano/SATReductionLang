#!/bin/bash

rm -f juezejecutable answer.cat answer.cat.long answer.esp answer.esp.long answer.eng answer.eng.long std.out std.err
(cd .. && make && cp juezejecutable test)
./juezejecutable ../nreinas/jp ../nreinas/jp2input ../nreinas/input2sat ../nreinas/propuestasolucion ../nreinas/validator ../nreinas/format > std.out 2> std.err
diff answer.cat answer.cat.cor
diff answer.cat.long answer.cat.long.cor
diff answer.esp answer.esp.cor
diff answer.esp.long answer.esp.long.cor
diff answer.eng answer.eng.cor
diff answer.eng.long answer.eng.long.cor
#diff std.out std.out.cor
diff std.err std.err.cor


