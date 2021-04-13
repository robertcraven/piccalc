
:- use_module(library(ordsets), [ord_subset/2, ord_union/3]).

%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% 

%%%%%%%%%% def: nnf_to_cnf/2

nnf_to_cnf([[]],[]) :-
 !.
nnf_to_cnf([],[[]]) :-
 !.

nnf_to_cnf([[A]],Cnf) :-
 !,
 nnf_to_cnf(A,Cnf).

nnf_to_cnf([[A|B]],Cnf) :-
 !,
 nnf_to_cnf(([[A]]&[B]),Cnf).

nnf_to_cnf([A|B],Cnf) :-
 !,
 nnf_to_cnf(([A]++B),Cnf).

% for formulas

nnf_to_cnf(true, []) :-
 !.

nnf_to_cnf(false, [[]]) :-
 !.

nnf_to_cnf((A ++ B), Cnf) :-
 !,
 nnf_to_cnf(A, CnfA),
 (
  CnfA = []                             % true
  -> nnf_to_cnf(true, Cnf)
  ;
  CnfA = [[]]                           % false
  -> nnf_to_cnf(B, Cnf)
  ;  nnf_to_cnf(B, CnfB),               % otherwise
     (
      CnfB = []                         % true
      -> nnf_to_cnf(true, Cnf)
      ;
      CnfB = [[]]                        % false
      -> Cnf = CnfA
      ;  pairwise_combinations(CnfA, CnfB, Cnf) % otherwise
     )
 ).

nnf_to_cnf((A & B), Cnf) :-
 !,
 nnf_to_cnf(A, CnfA),
 (
  CnfA = [[]]           % false
  -> nnf_to_cnf(false, Cnf)
  ;
  CnfA = []             % true
  -> nnf_to_cnf(B, Cnf)
  ;  nnf_to_cnf(B, CnfB),% otherwise
     (
      CnfB = [[]]       % false
      -> nnf_to_cnf(false, Cnf)
      ;
      CnfB = []         % true
      -> Cnf = CnfA
      ;                 % otherwise
        % transform (A && B) -- this is easy since A and B are already
        % in CNF after recursion
        append(CnfA, CnfB, Cnf)
     )
 ).

% atoms

nnf_to_cnf(Atom, [[Atom]]).

%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%% def: nnf_to_dnf/2

nnf_to_dnf(true, [[]]) :-
 !.
nnf_to_dnf(false, []) :-
 !.

nnf_to_dnf((A & B), Dnf) :-
 !,
 nnf_to_dnf(A, DnfA),
 (
  DnfA = []     % false
  -> nnf_to_dnf(false, Dnf)
  ;
  DnfA = [[]]   % true
  -> nnf_to_dnf(B, Dnf)
  ;             % otherwise
     nnf_to_dnf(B, DnfB),
     (
      DnfB = [] % false
      -> nnf_to_dnf(false, Dnf)
      ;
      DnfB = [[]]  % true
      -> Dnf = DnfA
      ;         % otherwise
         pairwise_combinations(DnfA, DnfB, Dnf)
     )
  ).

nnf_to_dnf((A ++ B), Dnf) :-
 !,
 nnf_to_dnf(A, DnfA),
 (
  DnfA = [[]]           % true
  -> nnf_to_dnf(true, Dnf)
  ;
  DnfA = []             % false
  -> nnf_to_dnf(B, Dnf)
  ;                     % otherwise
     nnf_to_dnf(B, DnfB),
     (
      DnfB = [[]]       % true
      -> nnf_to_dnf(true, Dnf)
      ;
      DnfB = []         % false
      -> Dnf = DnfA
      ;                 % otherwise
         append(DnfA, DnfB, Dnf)
    )
 ).

nnf_to_dnf(Atom, [[Atom]]).
  
%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%% def: pairwise_combinations/3

pairwise_combinations(ListA, ListB, Combs) :-
 length(ListA, NA),
 length(ListB, NB),
 pairwise_combinations(ListA, NA, ListB, NB, Combs).

%%%%%%%%%% def: pairwise_combinations/5

pairwise_combinations(ListA, NA, ListB, NB, Combs) :-
 (
  NA > NB
  -> pairwise_comb(ListB, ListA, [], Combs)
  ;  pairwise_comb(ListA, ListB, [], Combs)
 ).

%%%%%%%%%% def: pairwise_comb/4

pairwise_comb([], _ListB, Sofar, Sofar) :-
 !.

pairwise_comb([DA|RestA], ListB, Sofar, Combs) :-
 union_all_x(ListB, DA, Sofar, SofarX),
 !,
 pairwise_comb(RestA, ListB, SofarX, Combs).

%%%%%%%%%% def: union_all/4

union_all([], _DA, Tail, Tail) :-
 !.

union_all([DB|ListB], DA, [DAB|Rest], Tail) :-
 ord_union(DA, DB, DAB), 
 !,
 union_all(ListB, DA, Rest, Tail).

%%%%%%%%%% def: union_all_x/4

union_all_x([], _DA, Sofar, Sofar) :-
 !.

union_all_x([DB|ListB], DA, Sofar, Result) :-
 ord_union(DA, DB, DAB), 
 insert_new_list(Sofar, DAB, SofarX),
 !,
 union_all_x(ListB, DA, SofarX, Result).

%%%%%%%%%% def: insert_new_list/4

insert_new_list([], New, [New]) :-
 !.

insert_new_list([X|Rest], New, [X|Rest]) :- 
 ord_subset(X, New), !.
insert_new_list([X|Rest], New, Result) :- 
 (
  ord_subset(New, X)
  -> Result = NewInRest
  ;  Result = [X|NewInRest]
 ),
 !,
 insert_new_list(Rest, New, NewInRest).
