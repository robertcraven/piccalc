
:- ensure_loaded(declarations).
:- ensure_loaded(loading).
:- ensure_loaded(queries).
:- ensure_loaded(options_vars).
:- ensure_loaded(statistics).
:- ensure_loaded(utilities).

:-
 set_initial_options_vars('1.0'),       % piccalc version
 (
  current_predicate(piccalc_python/0)   % true iff being loaded from the python
  -> true
  ;  print_versions
 ).