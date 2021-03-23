
%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% string utilities

%%%%%%%%%% atoms_concat/2

atoms_concat([Atom|RestAtoms], AtomsConcat) :-
 atoms_concat(RestAtoms, Atom, AtomsConcat).

%%%%%%%%%% atoms_concat/3

atoms_concat([], Atom, Atom).

atoms_concat([Atom|RestAtoms], InAtom, AtomsConcat) :-
 atom_concat(InAtom, Atom, OutAtom),
 atoms_concat(RestAtoms, OutAtom, AtomsConcat).

%%%%%%%%%% number_atom/2

number_atom(Number, Atom) :-
 var(Number),
 !,
 atom_chars(Atom, Chars),
 number_chars(Number, Chars).

number_atom(Number, Atom) :-
 number_chars(Number, Chars),
 atom_chars(Atom, Chars).

%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% converting between terms

%%%%%%%%%% tuple_list/2

tuple_list(X, Y) :-
 (
  var(Y)
  -> (
      var(X)
      -> Y = [X]
      ;
      X = (X1,X2)
      -> Y = [X1|Rest],
         tuple_list(X2, Rest)
      ;  Y = [X]
     )
  ;  Y = [Y1|Rest],
     (
      Rest = []
      -> X = Y1
      ;  X = (Y1,X2),
         tuple_list(X2, Rest)
     )
 ).
