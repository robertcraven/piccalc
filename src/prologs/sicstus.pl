
:- use_module(library(lists), [max_member/2,min_member/2,remove_dups/2]).

common_prolog_abolish(X, Y) :-
 abolish(X/Y, [force(true)]).

common_prolog_logEval(X, Y, Res) :-
 Res is log(X,Y).

common_prolog_remove_dups(X, Y) :-
 remove_dups(X, Y).

max_list(List,Max) :-
 max_member(Max,List).

min_list(X, Y) :-
 min_member(Y, X).
