
common_prolog_abolish(X, Y) :-
 abolish(X, Y).

common_prolog_logEval(X,Y,Res) :-
 Res is (log(Y) / log(X)).

common_prolog_remove_dups([], []).

common_prolog_remove_dups([Head|Tail1], [Head|Tail2]) :- 
 delete(Tail1, Head, Residue),
 common_prolog_remove_dups(Residue, Tail2).
