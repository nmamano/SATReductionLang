# SAT Reduction Language

This is the interpreter for the online judge for the exercises on SAT reductions at
https://racso.cs.upc.edu/juezwsgi/exercise-list?inputkind=redsat

This judge is for computation theory courses covering SAT or NP-hard reductions in general.
It offers exercises to practice writing reductions to SAT, and offers counterexamples in the case of wrong submissions.

Each exercise consists of a decision problem. For each one, the goal is to give a valid reduction to SAT, i.e., a SAT formula that is satisfiable if and only if the instance of the original problem is a "yes" instance. In order to write the reduction, the user uses a C-inspired language that we made to make expressing SAT reductions convenient (while at the same time limiting the users' capabilities so that they cannot simply write a program to solve the original problem directly and bypass the reduction). For instance,

    or(f1,f2,...,fN):

 returns a formula that is satisfiable if and only if at least one of the formulas f1, f2, . . . , fN is true, and other primitives like

    atleast(k,f1,f2,...,fN)

have similar purposes.

The judge started as a clone of the judge for general NC-hard reductions. This project contains the modifications made to adapt it to a SAT-reductions-specific judge.
