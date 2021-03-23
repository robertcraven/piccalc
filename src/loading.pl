
:- use_module(library(lists), [reverse/2]).

:- ensure_loaded('loading/action_description').
:- ensure_loaded('loading/causal_theory').
:- ensure_loaded('loading/completion').

:-
 dynamic
  atom_integer/4,
  causal_law/1,
  completion_if_clause/2,
  completion_onlyif_clause/2,
  domain/6,
  file_term/4,
  rule_body/2,
  shiftable_rule/3,
  user_predicate/2,
  variable_rule/2.

%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% main predicates

%%%%%%%%%% def: loadf/1

loadf([FilenamePart|FilenameParts]) :-
 !,
 preloading,
 full_filenames([FilenamePart|FilenameParts], Filenames),
 load_action_description(Filenames),
 make_causal_theory,
 make_completion,
 postloading([FilenamePart|FilenameParts], Filenames).

loadf(FilenamePart) :-
 loadf([FilenamePart]).

%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% preloading and postloading

%%%%%%%%%% def: preloading/0

preloading :-
  preloading_retractions,
  preloading_iccvar_settings.

%%%%%%%%%% def: preloading_retractions/0 

preloading_retractions :-
 user_predicate(Functor, Arity),
 common_prolog_abolish(Functor, Arity),
 fail.

preloading_retractions :-
 retractall(user_predicate(_,_)),
 fail.

preloading_retractions :-
 iccalc_predicate(Predicate),
 retractall(Predicate),
 fail.

preloading_retractions :-
 cplus_keyword(Predicate),
 retractall(Predicate),
 fail.

preloading_retractions :-
 retractall(atom_integer(_,_,_,_)),
 retractall(causal_law(_)),
 retractall(completion_if_clause(_,_)),
 retractall(completion_onlyif_clause(_,_)),
 retractall(domain(_,_,_,_,_,_)),
 retractall(file_term(_,_,_,_)),
 retractall(rule_body(_,_)),
 retractall(shiftable_rule(_,_,_)),
 retractall(variable_rule(_,_)).

%%%%%%%%%% def: preloading_iccvar_settings/0

preloading_iccvar_settings :-
 set_var(max_tval, 0),
 set_var(total_rule_count, 0).

%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% finding files

%%%%%%%%%% def: full_filenames/2

full_filenames([], []).

full_filenames([FilenamePart|FilenameParts], [Filename|Filenames]) :-
 full_filename(FilenamePart, Filename),
 !,
 full_filenames(FilenameParts, Filenames).

%%%%%%%%%% def: full_filename/2
%
% When a file is loadfed, try these directories in order:
%  - The current working directory in the Unix shell
%  - The value of the user-specified 'dir:domains' option
%  - None (i.e. take File as an absolute filename)

full_filename(FilenamePart, Filename) :-
 iccalc_option(dir:working, DirFull),
 atom_concat(Dir, '/', DirFull),
 absolute_file_name(FilenamePart, Filename,
                    [access(exist), file_errors(fail), relative_to(Dir)]).

full_filename(FilenamePart, Filename) :-
 iccalc_option(dir:domains, Dir),
 absolute_file_name(FilenamePart, Filename,
                    [access(exist), file_errors(fail), relative_to(Dir)]).

full_filename(FilenamePart, Filename) :-
 absolute_file_name(FilenamePart, Filename,
                    [access(exist), file_errors(fail)]).

%%%%%%%%%% def: postloading/2

postloading([File|RestFiles], [FilePart|RestFileParts]) :-
 filenames_parts([FilePart|RestFileParts], [Path|_], [Base|RestBases]),
 set_var(loadf_filenames, [FilePart|RestFileParts]),
 set_var(files, [File|RestFiles]),
 set_var(file_basenames, [Base|RestBases]),
 set_var(mainfile, File),
 set_var(mainfile_basename, Base),
 set_option(dir:domains, Path).

%%%%%%%%%% def: filenames_parts/3

filenames_parts([], [], []).

filenames_parts([FileName|Rest], [Path|RestPaths], [Base|RestBases]) :-
 filename_parts(FileName, Path, Base),
 filenames_parts(Rest, RestPaths, RestBases).

%%%%% filename_parts/3

filename_parts(FileName, Path, Base) :-
 atom_codes(FileName, FileNameString),
 reverse(FileNameString, RevFileName),
 append(RevBase, [47|RevPath], RevFileName),
 !,
 reverse(RevBase, BaseString),
 reverse(RevPath, PathString),
 atom_codes(Path, PathString),
 atom_codes(Base, BaseString).

filename_parts(FileName, '', FileName).