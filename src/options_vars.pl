
:- use_module(library(ordsets), [list_to_ord_set/2]).

:-
 dynamic
  iccalc_option/2,
  iccalc_var/2.

%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% iccalc options

%%%%%%%%%% def: iccalc_option/2

iccalc_option(boolean_symbols, [tt,ff]).
iccalc_option(ccalc_optimize_clause_gen, 1).
iccalc_option(dir:domains, '../domains/').
iccalc_option(dir:tmp, '/tmp/').
iccalc_option(dir:working, './').
iccalc_option(num_models, all).
iccalc_option(remove_tautologies, 1).

%%%%%%%%%% def: set_option/2

set_option(Option, Value) :-
 retractall(iccalc_option(Option,_)),
 assert(iccalc_option(Option, Value)).

%%%%%%%%%% def: set_domains/1

set_domains(DIR) :-
 iccalc_option(dir:domains_base, DOMAINS_BASE_DIR),
 atoms_concat([DOMAINS_BASE_DIR,DIR,'/'], DOMAINS_DIR),
 set_option(dir:domains, DOMAINS_DIR).

%%%%%%%%%% def: options/0

options :-
 findall(t(Option,Value), iccalc_option(Option, Value), OptionValueList),
 list_to_ord_set(OptionValueList, Ord_OptionValueList),
 format(' OPTIONS~n~n', []),
 member(t(Option, Value), Ord_OptionValueList),
 format(' ~w~30|= ~q~n', [Option,Value]),
 fail.

options.

%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% iccalc vars

%%%%%%%%%% def: set_var/2

set_var(Var, Value) :-
 remove_var(Var),
 assert(iccalc_var(Var, Value)).

%%%%%%%%%% def: remove_var/2

remove_var(Var) :-
 retractall(iccalc_var(Var, _)).

%%%%%%%%%% def: incr_var/3

incr_var(Var, K, NewValue) :-
 (
  iccalc_var(Var, Value)
  -> NewValue is Value + K
  ;  NewValue = K
 ),
 set_var(Var, NewValue).

%%%%%%%%%% def: vars/0

vars :-
 findall(t(Option,Value), iccalc_var(Option, Value), OptionValueList),
 list_to_ord_set(OptionValueList, Ord_OptionValueList),
 format(' VARS~n~n', []),
 member(t(Option, Value), Ord_OptionValueList),
 format(' ~w~30|= ~q~n', [Option,Value]),
 fail.

vars.

%%%%%%%%%% def: incr_var/2

incr_var(Var, NewValue) :-
 incr_var(Var, 1, NewValue).

%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% initial settings

%%%%%%%%%% def: set_initial_options_vars/0

set_initial_options_vars(Version) :-
 set_directories,
 set_prolog_version,
 set_var(piccalc_version, Version).

%%%%%%%%%% def: set_directories/0

set_directories :-
 prolog_load_context(directory, SRC_DIR),
 (
  atom_concat(PICCALC_DIR, 'src', SRC_DIR)
  -> atom_concat(SRC_DIR, '/', SRC_DIR_FULL)
  ;  atom_concat(PICCALC_DIR, 'src/', SRC_DIR),
     SRC_DIR_FULL = SRC_DIR
 ),
 atom_concat(PICCALC_DIR, 'domains/', DOMAINS_DIR),
 set_option(dir:domains, DOMAINS_DIR),
 set_var(dir:piccalc, PICCALC_DIR),
 set_var(dir:src, SRC_DIR_FULL),
 set_option(dir:working, './').

%%%%%%%%%% def: set_prolog_version/0

set_prolog_version :-
 prolog_flag(version_data, Prolog),
 iccalc_var(dir:src, SRC_DIR),
 (
  Prolog = sicstus(N1,N2,N3,_,_)
  ->
   findall(Atom, (member(N, [N1,N2,N3]), number_atom(N, Atom)), [AtomN1,AtomN2,AtomN3]),
   atoms_concat(['SICStus Prolog ',AtomN1,'.',AtomN2,'.',AtomN3], PrologVersion),
   atom_concat(SRC_DIR, 'prologs/sicstus', PROLOG_SPECIFIC_FILE)
  ;
  Prolog = swi(N1,N2,N3,_)
  -> 
   findall(Atom, (member(N, [N1,N2,N3]), number_atom(N, Atom)), [AtomN1,AtomN2,AtomN3]),
   atoms_concat(['SWI Prolog ',AtomN1,'.',AtomN2,'.',AtomN3], PrologVersion),
   atom_concat(SRC_DIR, 'prologs/swi', PROLOG_SPECIFIC_FILE)
 ),
 ensure_loaded(PROLOG_SPECIFIC_FILE),
 set_var(prolog_version, PrologVersion).






