
%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% main predicates

%%%%%%%%%% def: load_action_description/1

load_action_description(Filenames) :-
 read_files(Filenames),
 add_variable_conditions,
 process_signature.

%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% syntax for input files

%%%%%%%%%% def: cplus_keyword/1

cplus_keyword(caused(_)).
cplus_keyword(default(_)).
cplus_keyword(exogenous(_)).
cplus_keyword(inertial(_)).
cplus_keyword(causes(_,_)).
cplus_keyword(nonexecutable(_)).
cplus_keyword(constraint(_)).
cplus_keyword(always(_)).
cplus_keyword(rigid(_)).
cplus_keyword(maycause(_,_)).

%%%%%%%%%% def: iccalc_predicate/1

iccalc_predicate(fc(_)).
iccalc_predicate(sdfc(_)).
iccalc_predicate(ac(_)).
iccalc_predicate(domain(_,_)).
iccalc_predicate(query(_,_,_)).

%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% load terms from input file

%%%%%%%%%% def: read_files/1

read_files([]).

read_files([Filename|Filenames]) :-
 read_file(Filename),
 read_files(Filenames).

%%%%%%%%%% def: read_file/1

read_file(Filename) :-
 open(Filename, read, Fd),
 repeat,
  read_term(Fd, Term, [variable_names(VarPairs)]),
  process_fail(Term, VarPairs),
 close(Fd),
 !.

%%%%%%%%%% def: process_fail/2

process_fail(end_of_file, _) :-
 !.

process_fail(:-(Body), _) :-
 !,
 call(Body),
 fail.

process_fail((VarDec :: Body), VarPairs) :-
 !,
 tuple_list(VarDec, Vars),
 Vars = [KeyVar|_],
 (
  member(=(_, KeyVarCopy), VarPairs),
  KeyVar == KeyVarCopy
  ->
   member(Var, Vars),
   member(=(VarName, VarCopy), VarPairs),
   Var == VarCopy,
   Var = KeyVar,
   assert(:-(variable_rule(VarName, Var), Body))
 ),
 fail.

process_fail(:-(Head, Body), VarPairs) :-
 iccalc_predicate(Head),
 !,
 assert(file_term(iccalc, Head, Body, VarPairs)),
 fail.

process_fail(:-(Head, Body), VarPairs) :-
 cplus_keyword(Head),
 !,
 assert(file_term(cplus, Head, Body, VarPairs)),
 fail.

process_fail(:-(Head, Body), VarPairs) :-
 !,
 functor(Head, Functor, Arity),
 (
  user_predicate(Functor, Arity)
  -> true
  ;  assert(user_predicate(Functor, Arity)) 
 ),
 assert(file_term(user, Head, Body, VarPairs)),
 fail.

process_fail(Head, VarPairs) :-
 process_fail(:-(Head,true), VarPairs).

%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% post-processing once terms loaded

%%%%%%%%%% def: add_variable_conditions/0

add_variable_conditions :-
 file_term(Type, Head, Body, VarNames),
 replace_varnames(VarNames, Body, ExpandedBody),
 (
  Type = cplus
  -> assert(:-(causal_law(Head), ExpandedBody))
  ;  assert(:-(Head,ExpandedBody))
 ),
 fail.

add_variable_conditions :-
 retractall(file_term(_,_,_,_)).

%%%%%%%%%% def: replace_varnames/3

% First argument is a list of equations of the
% form <VarName>=Var; if a clause in the input file
% had a variable T, then the pair 'T'=T will be in
% the list. Some of these variable names will be governed
% by variable_rule/2 clauses and we take account of this. 

replace_varnames([], ExpBody, ExpBody) :-
 !.

replace_varnames([=(VarName, Var)|RestVarNames], InBody, ExpBody) :- !,
 (
  clause(variable_rule(VarName, _), _) 
  -> OutBody = (variable_rule(VarName, Var), InBody)
  ;  OutBody = InBody
 ),
 !,
 replace_varnames(RestVarNames, OutBody, ExpBody).

%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% processing the signature

%%%%%%%%%% def: process_signature/0

process_signature :-
 assert_boolean_domains,
 assert_domains.

%%%%%%%%%% def: assert_boolean_domains/0

assert_boolean_domains :-
 iccalc_option(boolean_symbols, [Tval, Fval]), 
 aug_constant(C, Sig, Type),
 \+ domain(C, _),
 assert(domain(C, Tval)),
 assert(domain(C, Fval)),
 (
  domain(C, _, _, _, _, _) 
  -> true
  ;  assert(domain(C, Sig, Type, [Tval,Fval], 2, 1)) 
 ),
 fail.

assert_boolean_domains.

%%%%%%%%%% def: assert_domains/0

assert_domains :-
 aug_constant(C, Sig, Type),
 \+ domain(C, _, _, _, _, _),
 findall(V, domain(C,V), Values),
 Values \= [],
 (
  domain(C, _, _, _, _, _) 
  -> true
  ;  common_prolog_remove_dups(Values, Domain),
     length(Domain, N),
     common_prolog_logEval(2, N, Result),
     NBits is integer(ceiling(Result)),
     assert(domain(C, Sig, Type, Domain, N, NBits))
 ),
 fail.

assert_domains.  

%%%%%%%%%% def: aug_constant/3

aug_constant(C, state, fc) :-
 fc(C).

aug_constant(C, state, sdfc) :-
 sdfc(C).
 
aug_constant(C, trans, ac) :-
 ac(C).

%%%%%%%%%% def: aug_constant/1

aug_constant(C) :-
 aug_constant(C, _, _).

%%%%%%%%%% def: boolean_domain/1

boolean_domain(C) :-
 domain(C, _, _, Booleans, 2, 1),
 !,
 iccalc_option(boolean_symbols, Booleans).

%%%%%%%%%% def: nth_domain/3

nth_domain(C, Nth, V) :-
 domain(C,_Sig,_Type,Dom,_NDom,_NBits),
 nth1(Nth, Dom, V).
