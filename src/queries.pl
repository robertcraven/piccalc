
%%%%%%%%%% def: builtin_query/3

builtin_query(states, 0, []).

builtin_query(trans, 1, []).

builtin_query(runs(N), N, []) :-
 integer(N),
 N >= 0.

%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% predicates called from iccalc.py

%%%%%%%%%% def: cnf_clause/3

cnf_clause(QueryLabel, T, Clause) :-
 builtin_query(QueryLabel, _, Query),
 !,
 get_cnf_clause(T, Query, Clause).

cnf_clause(QueryLabel, T, Clause) :-
 query(QueryLabel, _, Query),
 !,
 get_cnf_clause(T, Query, Clause).

%%%%%%%%%% def: get_query_time/2

get_query_time_range(QueryLabel, Tmin, Tmax) :-
 builtin_query(QueryLabel, TimeRange, _),
 time_range(TimeRange, Tmin, Tmax).

get_query_time_range(QueryLabel, Tmin, Tmax) :-
 query(QueryLabel, T, _),
 time_range(T, Tmin, Tmax).

%%%%%%%%%% def: time_range

time_range(Tmin..Tmax, Tmin, Tmax) :-
 !.

time_range(T, T, T).

%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% 

%%%%%%%%%% def: get_cnf_clause/3
%
% a clause can come from:
%  1. the completion
%  2. the query
%  3. the tautologies we add, forced by pysat

get_cnf_clause(T, _Query, Clause) :-
 iccalc_var(n_statetrans_vars, N_statetrans_vars),
 completion_clause(T, C),
 clause_to_dimacs(C, N_statetrans_vars, Clause).

get_cnf_clause(T, Query, Clause) :-
 parse_query(Query, T, QueryF),
 mvc_to_boolean(QueryF, QueryFBool),
 nnf_to_cnf(QueryFBool, QueryCNF),
 iccalc_var(n_statetrans_vars, N_statetrans_vars),
 !,
 member(C, QueryCNF),
 clause_to_dimacs(C, N_statetrans_vars, Clause).

get_cnf_clause(_T, _Query, [N,NN]) :-
 iccalc_var(state_integers, NstateVs),
 member(N, NstateVs),
 atom_integer(_, _, N, 1),
 domain(_, _, fc, _Dom, 2, 1),
 NN is -N.

%%%%%%%%%% def: clause_to_dimacs/3

clause_to_dimacs([], _, []).

clause_to_dimacs([Atom=Val|Rest], NBasicVars, [NN|RestDimacs]) :-
 atom_to_integer(Atom, NBasicVars, N),
 (
  Val = 1
  -> NN = N
  ;  NN is -N
 ),
 clause_to_dimacs(Rest, NBasicVars, RestDimacs).

%%%%%%%%%% def: atom_to_integer/2

atom_to_integer(T:bool(J,Index), NBasicVars, N) :-
 !,
 N is NBasicVars*T + J + Index - 1.

%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% 

%%%%%%%%%% def: parse_query/3

parse_query([], _Max, true) :-
 !.

parse_query([F|Rest], Max, ParsedQ) :-
 !,
 parse_query(F & Rest, Max, ParsedQ).
   
% nnf_to_cnf will sort out occurrences of true/false but
% do a basic check (most ParsedQMax will be 'true')   

parse_query(F & G, Max, ParsedQ) :-
 !,
 parse_query(F, Max, ParsedF),
 (
  ParsedF = true
  -> ParsedQ = ParsedG 
  ;  ParsedQ = (ParsedF & ParsedG)
 ),
 !,
 parse_query(G, Max, ParsedG).
   
parse_query(F ++ G, Max, ParsedQ) :-
 !,
 parse_query(F, Max, ParsedF),
 (
  ParsedF = true
  -> ParsedQ = ParsedG 
  ;  ParsedQ = (ParsedF ++ ParsedG)
 ),
 !,
 parse_query(G, Max, ParsedG).

parse_query(-(F), Max, ParsedNegF) :-
 equivnot(F, NegF),
 !, 
 parse_query(NegF, Max, ParsedNegF).

% the following deals with N:F and max:F, but also has to
% deal with -(N:F) and -(max:F)

parse_query(QTerm, Max, ParsedF) :-
 time_stamped_formula(QTerm, F, Stamp),         % deals with e.g. -2:p
 !,
 parse_query_item(F, Stamp, Max, ParsedF).

%%%%%%%%%% def: time_stamped_formula/3

time_stamped_formula(-(max:F), -(F), max).

time_stamped_formula(max:F, F, max).

time_stamped_formula(-(N:F), -(F), N) :-
 integer(N), 
 N >= 0,
 !.
   
time_stamped_formula(N:F, F, N) :-
 integer(N), 
 N >= 0,
 !.

%%%%%%%%%% def: parse_query_item/4

parse_query_item(F, max, Max, ParsedF) :-
 !,
 parse_stamp_fmla(F, ParsedF, Max, _Sig).

parse_query_item(F, N, _Max, ParsedF) :-
 !,
 parse_stamp_fmla(F, ParsedF, N, _Sig).
