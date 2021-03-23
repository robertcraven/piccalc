
:- use_module(library(lists),   [nth1/3]).
:- use_module(library(ordsets), [ord_add_element/3]).

:- ensure_loaded('../cnf_dnf').

%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% main predicates

%%%%%%%%%% def: make_causal_theory/0

make_causal_theory :-
 make_atom_integer_map,
 make_store_causal_rules.

%%%%%%%%%% def: atom_info/4

atom_info(J, C, NBits, NDom) :-
 atom_integer(C, _, J, NBits),
 domain(C, _, _, _, NDom, _).

%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% atom integer map

%%%%%%%%%% def: make_atom_integer_map/0

make_atom_integer_map :-
 set_var(n_state_vars, 0),
 member(Type, [fc,sdfc]),
 domain(C, state, Type, _, _, NBits),
 iccalc_var(n_state_vars, PrevN),
 N is PrevN + 1,
 assert(atom_integer(C, state, N, NBits)),
 incr_var(n_state_vars, NBits, _),
 fail.

make_atom_integer_map :-
 iccalc_var(n_state_vars, Nstate),
 set_var(n_trans_vars, 0),
 domain(C, trans, ac, _, _, Nbits),
 iccalc_var(n_trans_vars, PrevN),
 N is Nstate + PrevN + 1,
 assert(atom_integer(C, trans, N, Nbits)),
 incr_var(n_trans_vars, Nbits, _),
 fail.

make_atom_integer_map :-
 iccalc_var(n_state_vars, Nstate),
 iccalc_var(n_trans_vars, Ntrans),
 Nstatetrans is Nstate + Ntrans,
 set_var(n_statetrans_vars, Nstatetrans),
 setof(Ns, A^B^atom_integer(A, state, Ns, B), StateNs), 
 (
  setof(NNs, AA^BB^atom_integer(AA, trans, NNs, BB), TransNs)
  -> true
  ;  TransNs = []
 ),
 set_var(state_integers, StateNs),
 set_var(trans_integers, TransNs).

%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% top-level control for storing causal rules

%%%%%%%%%% def: make_store_causal_rules/0

make_store_causal_rules :-
 causal_law(CausalLawOrFamily),
 make_store_causal_rules(CausalLawOrFamily),
 fail.

make_store_causal_rules.

%%%%%%%%%% def: make_store_causal_rules/1

% families of causal laws: inertial, exogenous, rigid

make_store_causal_rules(LawFamily) :-
 law_family(LawFamily, Law, _C=V, Dom),
 !,
 (
  member(V, Dom),
  parse_stamp_law(Law, Head, Body, T),
  rule_to_clause_store(Head, Body, T, Law),
  fail
  ;
  true
 ).

% individual causal laws

make_store_causal_rules(Law) :-
 parse_stamp_law(Law, Head, Body, T),
 rule_to_clause_store(Head, Body, T, Law).

%%%%%%%%%% def: law_family/4

law_family(LawFamily, Law, C=V, Dom) :-
 law_family(LawFamily, Law, C=V),
 !,
 domain(C, _, _, Dom, _, _).

%%%%%%%%%% def: law_family/3

law_family((exogenous C if G), (caused C=V if C=V & G), C=V).
law_family((exogenous C),      (caused C=V if C=V), C=V).
law_family((inertial C if G),  (caused C=V if C=V after C=V & G), C=V).
law_family((inertial C),       (caused C=V if C=V after C=V), C=V).
law_family((rigid C),          (caused false if C \= V after C=V), C=V).

%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% parsing of causal laws: medium-level

%%%%%%%%%% def: parse_stamp_law/4

%% caused

parse_stamp_law((caused F if G after H), Head, Body, T) :-
 !,   
 parse_stamp_fluent_dynamic(F, G, H, Head, Body, T).

parse_stamp_law((caused F after H), Head, Body, T) :-
 !,   
 parse_stamp_fluent_dynamic(F, true, H, Head, Body, T).

parse_stamp_law((caused F if G), Head, Body, T) :-
 !,
 parse_stamp_causal_general(F, G, Head, Body, T).

parse_stamp_law((caused F), Head, Body, T) :-
 !,
 parse_stamp_causal_general(F, true, Head, Body, T).

%% constraint

parse_stamp_law((constraint F after G), Head, Body, T) :-
 !,   
 parse_stamp_law((caused false if -(F) after G), Head, Body, T). 

parse_stamp_law((constraint F), Head, Body, T) :-
 !,   
 parse_stamp_law((caused false if -(F)), Head, Body, T). 
   
%% always

parse_stamp_law((always F), Head, Body, T) :-
 !,   
 parse_stamp_law((caused false after -(F)), Head, Body, T). 
   
%% nonexecutable

parse_stamp_law((nonexecutable F if G), Head, Body, T) :-
 !,   
 parse_stamp_law((F causes false if G), Head, Body, T). 

parse_stamp_law((nonexecutable F), Head, Body, T) :-
 !,   
 parse_stamp_law((F causes false), Head, Body, T). 

%% causes

parse_stamp_law((F causes G if H), Head, Body, T) :-
 !,
 parse_formula_sig(G, SigG),
 (
  SigG = trans
  -> parse_stamp_law((caused G if F & H), Head, Body, T)
  ;  parse_stamp_law((caused G after F & H), Head, Body, T) 
 ).

parse_stamp_law((F causes G), Head, Body, T) :-
 !,  
 parse_formula_sig(G, SigG),
 (
  SigG = trans
  -> parse_stamp_law((caused G if F), Head, Body, T)
  ;  parse_stamp_law((caused G after F), Head, Body, T)
 ).
      
%% default

parse_stamp_law((default F if G after H), Head, Body, T) :-
 !,   
 parse_stamp_law((caused F if F & G after H), Head, Body, T). 
   
parse_stamp_law((default F after H), Head, Body, T) :-
 !,   
 parse_stamp_law((caused F if F after H), Head, Body, T). 
   
parse_stamp_law((default F if G), Head, Body, T) :-
 !,
 parse_stamp_law((caused F if F & G), Head, Body, T). 
   
parse_stamp_law((default F), Head, Body, T) :-
 !,
 parse_stamp_law((caused F if F), Head, Body, T). 

%% may cause

parse_stamp_law((F maycause G if H), Head, Body, T) :-
 !,  
 parse_formula_sig(G, SigG),
 (
  SigG = trans
  -> parse_stamp_law((caused G if G & F & H), Head, Body, T)
  ;  parse_stamp_law((caused G if G after F & H), Head, Body, T) 
 ).

parse_stamp_law((F maycause G), Head, Body, T) :-
 !,  
 parse_formula_sig(G, SigG),
 (
  SigG = trans
  -> parse_stamp_law((caused G if G & F), Head, Body, T)
  ;  parse_stamp_law((caused G if G after F), Head, Body, T) 
 ).

%%%%%%%%%% def: parse_stamp_fluent_dynamic/6

parse_stamp_fluent_dynamic(F, G, H, StampF, StampG & StampH, 1) :-
 parse_stamp_fmla(F, StampF, 1, _SigF),
 parse_stamp_fmla(G, StampG, 1, _SigG),
 parse_stamp_fmla(H, StampH, 0, _SigH).

%%%%%%%%%% def: parse_stamp_causal_general/5

parse_stamp_causal_general(F, G, StampF, StampG, T) :-
 parse_stamp_fmla(F, StampF, 0, SigF),
 parse_stamp_fmla(G, StampG, 0, _SigG),
 (
  SigF = trans
  -> T = 1
  ;  T = 0
 ).

%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% parsing of causal laws: low-level

%%%%%%%%%% def: parse_stamp_fmla/3

parse_stamp_fmla(true, true, _, any) :-
 !.

parse_stamp_fmla(false, false, _, any) :-
 !.

parse_stamp_fmla(-C=V, StampF, T, Sig) :-
 !,
 parse_stamp_fmla(C\=V, StampF, T, Sig).

parse_stamp_fmla(-C\=V, StampF, T, Sig) :-
 !,
 parse_stamp_fmla(C=V, StampF, T, Sig).

parse_stamp_fmla(-(C), StampF, T, Sig) :-
 aug_constant(C),
 !,
 boolean_domain(C),
 iccalc_option(boolean_symbols,[_,FF]),
 parse_stamp_fmla(C=FF, StampF, T, Sig).

parse_stamp_fmla(-(F), StampNegF, T, Sig) :-
 equivnot(F, NegF),
 !,
 parse_stamp_fmla(NegF, StampNegF, T, Sig).

parse_stamp_fmla(F & G, StampF & StampG, T, Sig) :-
 !,
 parse_stamp_fmla(F, StampF, T, SigF),
 parse_stamp_fmla(G, StampG, T, SigG),
 signature_of_formula(SigF, SigG, Sig).

parse_stamp_fmla(F ++ G, StampF ++ StampG, T, Sig) :-
 !,
 parse_stamp_fmla(F, StampF, T, SigF),
 parse_stamp_fmla(G, StampG, T, SigG),
 signature_of_formula(SigF, SigG, Sig).

% C=X could be an atom or an expression C1=C2 

parse_stamp_fmla(C=X, (T:Atom)=1, T, Sig) :-
 !,
 parse_stamp_eq_fmla(C, X, Atom, Sig).

% C \= X could be negation of an atom or C1\=C2 

parse_stamp_fmla(C\=X, (T:Atom)=0, T, Sig) :-
 !,
 parse_stamp_eq_fmla(C, X, Atom, Sig).

% boolean atoms

parse_stamp_fmla(C, StampF, T, Sig) :-
 aug_constant(C), 
 boolean_domain(C),  % domain(C,tt) might hold for non-boolean C
 iccalc_option(boolean_symbols,[TT,_]), 
 !,
 parse_stamp_fmla(C=TT, StampF, T, Sig).

%%%%%%%%%% def: parse_formula_sig/2

parse_formula_sig(F, Sig) :-
 parse_stamp_fmla(F, _StampF, _T, Sig).

%%%%%%%%%% def: signature_of_formula/3

signature_of_formula(Sig1, Sig2, Sig) :-
 (
  Sig1 = any
  -> Sig = Sig2 ;
  Sig2 = any
  -> Sig = Sig1 ;
  Sig1 = mixed
  -> Sig = mixed ;
  Sig2 = mixed
  -> Sig = mixed ;
  Sig1 = Sig2
  -> Sig = Sig1
  ;  Sig = mixed
 ).

%%%%%%%%%% def: equivnot/2

equivnot(true, false).
equivnot(false, true).
equivnot((A & B), (-A ++ -B)).
equivnot((A ++ B), (-A & -B)).
equivnot((C=X), C \= X).
equivnot((C \= X), C = X).
equivnot(-(A), A).

%%%%%%%%%% def: parse_stamp_eq_fmla/4

parse_stamp_eq_fmla(C, V, Atom, Sig) :-
 domain(C, V), 
 domain(C, Sig, Type, Dom, NDom, Nbits), 
 atom_integer(C, Sig, J, Nbits),
 !,
 nth1(Nth, Dom, V),
 Atom = mvc(J, Nth, Sig, Type, NDom, Nbits).

parse_stamp_eq_fmla(C1, C2, Atom, Sig) :-
 domain(C1, Sig1, _, _, _, _),
 domain(C2, Sig2, _, _, _, _), 
 signature_of_formula(Sig1, Sig2, Sig),
 !,
 Atom = eq_dom(C1,C2).

%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% 

%%%%%%%%%% def: rule_to_clause_store/4

rule_to_clause_store(Head, Body, T, _Law) :-
 nnf_to_cnf(Head, HCNF),
 nnf_to_dnf(Body, BDNF),
 !,
 (
  HCNF = []
  ->
   format('Trivial rule: head true~n', [])
  ;
  \+ (member(B, BDNF), \+ has_complementary_lits(B))
  ->
   format('Trivial rule: body false~n', [])
  ;
   store_rule_schemas(HCNF, BDNF, T) 
 ).

%%%%%%%%%% def: has_complementary_lits/1

has_complementary_lits([Atom=0,Atom=1|_]) :-
 !.

has_complementary_lits(
  [(T:mvc(V, N1, Sig, Type, NDom, Nbits))=1,(T:mvc(V, N2, Sig, Type, NDom, Nbits))=1|_]) :- 
 N1 \= N2,
 !.

has_complementary_lits([_|OrdList]) :-
 has_complementary_lits(OrdList).

%%%%%%%%%% def: store_rule_schemas/3

store_rule_schemas(HCNF, BDNF, T) :-
 member(H, HCNF),
 H \= [_,_|_],  % we know H must have complementary literals; non-def checked
 (
  H = []
  -> D = false
  ;  H = [D]
 ),
 member(B, BDNF),
 \+ has_complementary_lits(B),
 incr_var(total_rule_count, RN),
 assert(rule_body(RN, B)),
 assert(shiftable_rule(D, T, RN)),
 iccalc_var(max_tval, Current),
 (
  Current < T
  -> set_var(max_tval, T)
  ;  true
 ),
 fail.

store_rule_schemas(_,_,_).
