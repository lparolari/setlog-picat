% (X=a or X=b) & f(X)=f(a) (Conjunctive Normal Form)

%[or(eq(X,a),eq(X,b)),eq(f(X),f(a))]

%-----

% (X=a or (X neq c & Z=b)) & f(X) neq f(a)

%[or(eq(X,a),neq(X,c)), or(eq(X,a),eq(Z,b)), neq(f(X),f(a))]


clpset :-
  read(F),
  solve(F,FRis),
  write(F),nl,write(FRis).

solve(F,FRis) :-
  step(F,FNew),
  solvecont(F,FNew,FRis).

solvecont(F1,F2,F2) :-
  F1 == F2,!.
solvecont(_F1,F2,FRis) :-
  solve(F2,FRis).

step([],[]) :- !.
step([F1|FR],FnewR) :-
  rule(F1,F1new),nonvar(F1new),F1new=[],!,
  step(FR,FnewR).
step([F1|FR],[F1new|FnewR]) :-
  rule(F1,F1new),
  step(FR,FnewR).

rule(eq(T1,T2),[]) :-
  ground(T1),ground(T2),
  T1 == T2,!.
rule(eq(T1,T2),[]) :-
  T1 = T2.

rule(neq(T1,T2),neq(T1,T2)) :-
  var(T1),!.
rule(neq(T1,T2),[]) :-
  ground(T1),ground(T2),
  T1 \== T2,!.

rule(or(F1,_F2),F1Ris) :-
  solve([F1],F1Ris).
rule(or(_F1,F2),F2Ris) :-
  solve([F2],F2Ris).




  
  