
%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% 

%%%%%%%%%% def: print_versions/0

print_versions :-
 iccalc_var(prolog_version, Dialect),
 iccalc_var(piccalc_version, Version),
 format("~n%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%~n",[]),
 format("%~n", []),
 format("% piCCalc Version ~w, for ~w~n", [Version,Dialect]),
 format("%~n", []),
 format("% Type 'help.' for online help.~n",[]),
 format("%~n", []),
 format("%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%~n~n",[]).
