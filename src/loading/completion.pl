
:- use_module(library(ordsets), [ord_union/3]).

%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% completion clauses

%%%%%%%%%% def: make_completion/0

make_completion :-
 make_completion_clauses_if,            % shiftable rules
 iccalc_var(max_tval, MaxTval),
 make_completion_clauses_only_if(0, MaxTval),
 make_mvc_constraints.

%%%%%%%%%% def: make_completion_clauses_if/0

make_completion_clauses_if :-
 shiftable_rule(HeadMVC, T, RN),
 rule_body(RN, Body),
 negate_mvc_lits_to_boolean(Body, NegBodyBool),
 nnf_to_cnf(NegBodyBool, BodyCNF),
 member(BodyAtoms, BodyCNF),
 (
  HeadMVC = false
  -> % there are no tautologies in a rule body
     Clause = BodyAtoms
  ;  mvc_atom_to_atom_list(HeadMVC, HeadAtomList),
     member(Head, HeadAtomList),
     ord_add_element(BodyAtoms, Head, Clause),
     (
      iccalc_option(remove_tautologies, 1)  
      -> \+ has_complementary_lits(Clause)
      ;  true
     )
 ),
 assert(completion_if_clause(T, Clause)),
 fail.

make_completion_clauses_if.

%%%%%%%%%% def: negate_mvc_lits_to_boolean/2

negate_mvc_lits_to_boolean([],false).

negate_mvc_lits_to_boolean([Atom=Val|Ns],(BoolF ++ Cs)) :-
 OppVal is 1 - Val,
 mvc_atom_to_boolean(Atom=OppVal, BoolF),
 !,
 negate_mvc_lits_to_boolean(Ns,Cs).

%%%%%%%%%% def: mvc_to_boolean/2

mvc_to_boolean(true, true) :-
 !.

mvc_to_boolean(false, false) :-
 !.

mvc_to_boolean((A & B), F) :-
 !,
 mvc_to_boolean(A, Ax),
 (
  Ax = false
  -> F = false ;
  Ax = true
  -> mvc_to_boolean(B, F)
  ;  mvc_to_boolean(B, Bx),
     (
      Bx = false
      -> F = false ;
      Bx = true
      -> F = Ax
      ;  F = (Ax & Bx)
     )
 ).

mvc_to_boolean((A ++ B), F) :-
 !,
 mvc_to_boolean(A, Ax),
 (
  Ax = true
  -> F = true ;
  Ax = false
  -> mvc_to_boolean(B, F)
  ;  mvc_to_boolean(B, Bx),
     (
      Bx = false
      -> F = Ax ;
      Bx = true
      -> F = true
      ;  F = (Ax ++ Bx)
     )
 ). 

mvc_to_boolean(F,Fx) :-
 mvc_atom_to_boolean(F, Fx).

%%%%%%%%%% def: mvc_atom_to_boolean/2

mvc_atom_to_boolean((T:eq_dom(C1,C2))=Val, (T:eq_dom(C1,C2))=Val) :-
 !.

mvc_atom_to_boolean((T:mvc(J, Nth, Sig, _Type, NDom, Nbits))=Val, Formula) :- 
 nth_to_bool_formula(Nbits, Nth, NDom, 1, Nbits, constant(J,Sig), Val, T, Formula).

%%%%%%%%%% def: mvc_atom_to_atom_list/2

mvc_atom_to_atom_list((T:mvc(J, Nth, Sig, _Type, NDom, Nbits))=Val, AtomList) :- 
 nth_to_atom_list(Nbits, Nth, NDom, 1, Nbits, constant(J,Sig), Val, T, AtomList).

%%%%%%%%%% def: nth_to_bool_formula/9

nth_to_bool_formula(Nbits, Nth, NDom, Index, MaxBits, constant(Var,Sig), Val, T, Formula) :-
 Bit is Nth rem 2,
 (
  Val = 1
  -> BitVal = Bit
  ;  BitVal is 1-Bit
 ),
 Term = ((T:bool(Var,Index)) = BitVal), 
 (
  Nbits = 1 
  -> Formula = Term
  ;  (
      Val = 1
      -> Formula = (Term & Rest)
      ;  Formula = (Term ++ Rest)
     ),
     Next is Index + 1,
     NNbits is Nbits - 1,
     NNth is Nth >> 1,
     nth_to_bool_formula(NNbits,NNth, NDom, Next, MaxBits, constant(Var,Sig), Val, T, Rest)
 ).

%%%%%%%%%% def: make_completion_clauses_only_if/2

make_completion_clauses_only_if(T, MaxTval) :- 
 T > MaxTval,
 !.

make_completion_clauses_only_if(T, MaxTval) :-
 Tnext is T + 1,
 make_completion_clauses_only_if(T),
 !,
 make_completion_clauses_only_if(Tnext, MaxTval).

%%%%%%%%%% def: make_completion_clauses_only_if/1

% this generates and stores what I call Sigma_T in my notes
   
make_completion_clauses_only_if(T) :-
 aug_atom_mvc(Atom, Sig, Type),
 (
  T = 0,
  Type = fc
  -> fail
  ;  true
 ), % exogeneity simple fc at 0
 (
  Sig = state
  -> J = T
  ;  T > 0,
     J is T - 1
 ),
 HeadMVC = ((J:Atom)=1),   % ASSUME Val is ALWAYS 1 HERE
 findall(BodyAtoms,
         (rule_applicable_at(T, HeadMVC, Body), 
          mvc_lits_to_boolean(Body,BodyAtoms)),
         Bodies),
 NegHeadMVC = ((J:Atom)=0),  % OppVal here
 (
  nnf_to_cnf(Bodies, BodiesCnf)
  -> true
 ),
 mvc_atom_to_atom_list(NegHeadMVC, NegHeadAtoms),
 (
  member(RB, BodiesCnf),
  ord_union(NegHeadAtoms, RB, Clause),
  (
   iccalc_option(remove_tautologies, 1),
   has_complementary_lits(Clause)
   -> true
   ;  assert(completion_onlyif_clause(T, Clause))
  )
 ),
 fail.   

make_completion_clauses_only_if(_T).

%%%%%%%%%% def: aug_atom_mvc/3

aug_atom_mvc(Atom, Sig, Type) :-
 domain(C, Sig, Type, _Dom, NDom, Nbits),
 atom_integer(C, Sig, J, Nbits),
 generate_integer(1, NDom, Nth),
 Atom = mvc(J, Nth, Sig, Type, NDom, Nbits).

%%%%%%%%%% def: generate_integer/3

generate_integer(Min,Max,_J) :-
 Min > Max,
 !,
 fail.

generate_integer(Min,_Max,Min).

generate_integer(Min,Max,J) :-
 NewMin is Min + 1,
 generate_integer(NewMin,Max,J).

%%%%%%%%%% def: rule_applicable_at/3

rule_applicable_at(T, Head, Body) :-
 shiftable_rule(Head, T, RN),
 rule_body(RN, Body).
  
rule_applicable_at(T, false, Body) :-
 shiftable_rule(false, TX, RN),
 TX < T,
 Tshift is T - TX,
 rule_body(RN, BodyX),
 shift_atoms(BodyX, Tshift, Body).
  
rule_applicable_at(T, (N:Atom)=Val, Body) :-
 shiftable_rule((M:Atom)=Val, TX, RN),
 TX < T,
 Tshift is T - TX,
 N is M + Tshift,
 rule_body(RN, BodyX),
 shift_atoms(BodyX, Tshift, Body).

%%%%%%%%%% def: shift_atoms/3

shift_atoms([], _, []) :-
 !.

shift_atoms([Atom|Rest], Tshift, [AtomX|RestX]) :-
 (
  Atom = ((N:Core)=Val)
  -> NN is N + Tshift,
     AtomX = ((NN:Core)=Val)
  ;  AtomX = Atom
 ),
 !,
 shift_atoms(Rest, Tshift, RestX).

%%%%%%%%%% def: mvc_lits_to_boolean/2

mvc_lits_to_boolean([],[]).

mvc_lits_to_boolean([Atom|Ns],[BoolF|Cs]) :-
 mvc_atom_to_boolean(Atom, BoolF),
 !,
 mvc_lits_to_boolean(Ns,Cs).

%%%%%%%%%% def: make_mvc_constraints/0

make_mvc_constraints :-
 mvc_constraint_clause(T, Clause),
 assert(completion_if_clause(T, Clause)),
 fail.

make_mvc_constraints.

%%%%%%%%%% def: mvc_constraint_clause/2

mvc_constraint_clause(T, Clause) :-
 domain(C, Sig, _, _, NDom, Nbits),
 atom_integer(C, Sig, J, Nbits),
 (Sig = state -> T = 0 ; T = 1),
 MaxNth is 2 << (Nbits - 1),            % MaxNth = 2^Nbits
 MaxNth > NDom,
 FirstNoVal is NDom + 1,
 generate_integer(FirstNoVal, MaxNth, Nth),
 nth_to_atom_list(Nbits, Nth, NDom, 1, Nbits, constant(J,Sig), 0, 0, Clause).

%%%%%%%%%% def: nth_to_atom_list/9

nth_to_atom_list(Nbits, Nth, NDom, Index, MaxBits, constant(Var,Sig), Val, T, AtomList) :-
 Bit is Nth rem 2,
 (
  Val = 1
  -> BitVal = Bit
  ;  BitVal is 1-Bit
 ),
 Term = ((T:bool(Var,Index)) = BitVal),
 (

  Nbits = 1 
  -> AtomList = [Term]
  ;  AtomList = [Term|Rest],
     Next is Index + 1,
     NNbits is Nbits - 1,
     NNth is Nth >> 1,
     nth_to_atom_list(NNbits,NNth, NDom, Next, MaxBits, constant(Var,Sig), Val, T, Rest)
 ).

%%%%%%%%%% def: completion_clause/2

completion_clause(T, Clause) :-
 iccalc_var(max_tval, MaxTval),
 !,
 completion_clause(T, MaxTval, Clause).

%%%%%%%%%% def: completion_clause/3

completion_clause(T, _MaxTval, Clause) :-
 generate_integer(0, T, N),
 generate_integer(0, N, J),
 Tshift is N - J,
 completion_if_clause(J, ClauseJ),
 shift_atoms(ClauseJ, Tshift, Clause).

% completion clauses from stored 'only if' part

completion_clause(T, MaxTval, Clause) :-
 Tm is min(T, MaxTval),
 generate_integer(0, Tm, J),
 completion_onlyif_clause(J, Clause).

completion_clause(T, MaxTval, Clause) :-
 T > MaxTval,
 MaxTshift is T - MaxTval,
 generate_integer(1, MaxTshift, Tshift),
 completion_onlyif_clause(MaxTval, ClauseM),
 shift_atoms(ClauseM, Tshift, Clause).