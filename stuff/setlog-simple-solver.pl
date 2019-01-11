:-op(980,xfx,:).
:-op(970,xfy,or).
:-op(950,xfy,&).
:-op(900,fy,neg).
:-op(800,xf,!).
:-op(700,xfx,in).   
:-op(700,xfx,neq).  
:-op(700,xfx,nin).   
:-op(650,yfx,with).


setlog :- top_level.

top_level :-
       nl, write('{log}=> '),
       read_term(Goal,[variable_names(VarNames)]),
       solve(Goal,Constr),
       skip_return, 
       mk_subs_ext(VarNames,VarNames_ext),
       nl, write_subs_constr(VarNames_ext,Constr),
       top_level.
top_level :-
       nl,write(no),nl,
       skip_return, 
       top_level.

solve(Goal_ext,Constr):-     %% {log} interpreter main predicate
       preproc(Goal_ext,Goal),!,
       call_goal(Goal,Constr).
 
call_goal(G,ClistNew) :-
       constrlist(G,GClist,GAlist),
       solve_goal(GClist,GAlist,ClistNew). 

mk_subs_ext(VarSubs,VarSubsMin) :-      
       postproc(VarSubs,VarSubsExt),
       mk_subs_vv(VarSubsExt,VarSubsMin).
mk_subs_vv([],[]).                  
mk_subs_vv([N1=V1|Subs],R) :-
       var(V1),!,
       V1 = N1,
       mk_subs_vv(Subs,SubsMin),
       append(SubsMin,[true],R).  
mk_subs_vv([N1=V1|Subs],[N1=V1|R]) :-
       mk_subs_vv(Subs,R).  

write_subs_constr([],[]) :- !,
       write(yes), nl.                       
write_subs_constr(Subs,Constr) :- 
      (Subs = [],!,true ; 
       Subs = [true|_],!,write('true') ;
       write_subs_all(Subs)),
       write_constr(Constr), nl,
       nl, write('Another solution?  (y/n)'),
       get_single_char(C), 
       (C \== 121,!    % 'y'
        ; 
        fail
       ).

write_subs_all([]).
write_subs_all([N1=V1|R]) :-
       nl, write(N1), write(' = '), write(V1),
       (R = [],!,true ; 
        R = [true|_],!,true ;
        write(',  '), write_subs_all(R) ).  

write_constr([]) :-   !.                
write_constr(Constr) :-             
       nl, write('Constraint:'), 
       postproc(Constr,Constr_ext),
       write(Constr_ext).

skip_return :-    
      read_pending_input(user_input,_C,[]).

%%%% solve_goal(Constraint(in),Non_Constraint(in),Constraint(out))

solve_goal(Clist,[],CListCan):- !, 
       sat(Clist,CListCan). 
solve_goal(Clist,[true],CListCan):- !, 
       sat(Clist,CListCan). 
solve_goal(Clist,[A|B],CListOut):-
       sat(Clist,ClistSolved),
       ssolve(A,ClistCl,AlistCl),
       append(ClistSolved,ClistCl,ClistNew),
       append(AlistCl,B,AlistNew),
       solve_goal(ClistNew,AlistNew,CListOut).

ssolve(true,[],[]):- !.                  %% unit goal
ssolve( (G1 or G2),ClistNew,[]):-        %% goal disjunction 
        !,(call_goal(G1,ClistNew)
          ;
          call_goal(G2,ClistNew) ).                
     
constrlist(A & B,[A|B1],B2):-
        constraint(A),!,
        constrlist(B,B1,B2).         
constrlist(A & B,B1,[A|B2]):-
        !,constrlist(B,B1,B2).                       
constrlist(A,[A],[]):-
        constraint(A),!.        
constrlist(A,[],[A]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%   Set/Multiset constraints    %%%%%%%%%%%               
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constraint(_ = _). 
constraint(_ neq _).  
constraint(_ in _). 
constraint(_ nin _).

%%%%%%%%%   Set/Multiset constraint satsfiability procedure  %%%%%%%%%              

%%%% sat(Constraint(in),Solved_Form_Constraint(out))
sat(C,SFC):- 
      sat_step(C,NewC,R),
      sat_cont(R,NewC,SFC).
sat_cont(R,NewC,SFC) :-
      R == stop,!,
      norep_in_list(NewC,SFC).     
sat_cont(_R,NewC,SFC) :-
      sat(NewC,SFC).

sat_step([],[],stop) :- !.
sat_step([X = Y|R1],R2,Z):- !,
          sat_eq([X = Y|R1],R2,Z).
sat_step([X neq Y|R1],R2,Z):- !,
          sat_neq([X neq Y|R1],R2,Z).
sat_step([X in Y|R1],R2,Z):- !,
          sat_in([X in Y|R1],R2,Z).
sat_step([X nin Y|R1],R2,Z):- !,
          sat_nin([X nin Y|R1],R2,Z).

%%%%%%%%%%%%% equality

sat_eq([T1 = T2|R1],R2,c):-                    
      sunify(T1,T2,C),
      append(C,R1,R3), 
      sat_step(R3,R2,_).

sunify(X,Y,C) :- 
      var(X),!,
      sunifyXt(X,Y,C).
sunify(X,Y,C) :- 
      var(Y),!,
      sunify(Y,X,C).                % 2
sunify(R,S,C) :-                                         
      tail(R,TR),
      tail(S,TS),!,
      (samevar(TR,TS),!,
       stunify_samevar(R,S,TR,C)
      ;
       stunify_ss(R,S,C) ). 
sunify(X,Y,C) :-                             % 8 
      X=..[F|Ax],Y=..[F|Ay],!,
      sunifylist(Ax,Ay,C).

sunifyXt(X,Y,[]) :-                          % 5
      tail(Y,TY),var(TY),samevar(X,TY),!,
      replace_tail(Y,_N,NewY),
%     occur_check(X,NewY),  
      X = NewY.               
sunifyXt(X,Y,[]) :-                          % 6 
%     occur_check(X,Y),  % occur-check supressed for efficiency 
      X = Y.             % reasons (drop % to reactivate it)

%%  Sets: distinct tail vars.
stunify_ss(R with X,S with Y,C) :-    % 9(a) special
      ground(X), ground(Y),!,
      (sunify(X,Y,_),!, stunify1_2_3(R,S,X,Y,C)
      ;
       sunify(R,N with Y,C1), 
       sunify(S,N with X,C2),
       append(C1,C2,C) ).
stunify_ss(R with X,S with Y,C) :-                           
      sunify(X,Y,C1),
      stunify1_2_3(R,S,X,Y,C2),
      append(C1,C2,C).
stunify_ss(R with X,S with Y,C) :-    % 9(a).4
      sunify(R,N with Y,C1),
      sunify(S,N with X,C2),
      append(C1,C2,C).

stunify1_2_3(R,S,_,_,C) :-            % 9(a).1
      sunify(R,S,C).
stunify1_2_3(R,S,_,Y,C) :-            % 9(a).2
      sunify(R,S with Y,C).
stunify1_2_3(R,S,X,_,C) :-            % 9(a).3 
      sunify(R with X,S,C).

%% Sets: same tail vars. (action 9(b))
stunify_samevar(R with X,S with Y,_TR,C):-
      select(Z,S with Y,Rest),
      sunify(X,Z,C1),
      (sunify(R,Rest,C2)              % 9(b).1
      ;
       sunify(R with X,Rest,C2)       % 9(b).2
      ;
       sunify(R,S with Y,C2)),        % 9(b).3
      append(C1,C2,C).
stunify_samevar(R with X,S with Y,TR,C):-   % 9(b).4
      replace_tail(R,N,NewR),
      replace_tail(S with Y,N,NewSS),
      sunify(TR,N with X,C1),
      sunify(NewR,NewSS,C2),
      append(C1,C2,C).

sunifylist([],[],[]).
sunifylist([X|AX],[Y|AY],C):-
      sunify(X,Y,C1),
      sunifylist(AX,AY,C2),
      append(C1,C2,C).

% Auxiliar predicates for unification

select(_,S,_):-
       var(S), !, fail.
select(Z, R with Z, R).
select(Z, R with Y, A with Y):-
       select(Z, R, A).

samevar(X,Y) :- var(X), var(Y), X == Y.

tail(R with _,R) :- var(R),!.
tail({} with _,{}) :- !.
tail(R with _,T) :- 
      tail(R,T).

replace_tail(R,N,N) :- var(R),!.
replace_tail({},N,N) :- !.
replace_tail(R1 with X,N,R2 with X) :- 
      replace_tail(R1,N,R2).

occur_check(X,Y):-
      var(Y),!,X \== Y.
occur_check(X,Y):-
      Y =.. [_|R],
      occur_check_list(X,R).

occur_check_list(_X,[]):-!.
occur_check_list(X,[A|R]):-
      occur_check(X,A),
      occur_check_list(X,R).

%%%%%%%%%%%%% inequality

sat_neq([F neq G|R1],R2,c):-                           % ground case
         ground(F),ground(G),!,
         \+sunify(F,G,_),
         sat_step(R1,R2,_).
sat_neq([F neq G|R1],R2,c):-                           % 1
         nonvar(F),nonvar(G),
         functor(F,Fname,Far),functor(G,Gname,Gar),
         (Fname \== Gname ; Far \== Gar),!,
         sat_step(R1,R2,_).
sat_neq([F neq G|R1],R2,c):-                           % 2, 3
         nonvar(F),nonvar(G),
         functor(F,Fname,Far),functor(G,Gname,Gar),
         Fname == Gname, Far == Gar, 
         Fname \== with, 
         F =.. [_|Flist], G =.. [_|Glist],!,
         memberall(A,B,Flist,Glist),
         sat_step([A neq B|R1],R2,_).
sat_neq([T neq X|R1],R2,c):-                           % 4
         var(X),nonvar(T),! ,
         sat_step([X neq T|R1],R2,_).
sat_neq([X neq Y|_],_,_):-                             % 3
         var(X),var(Y),
         samevar(X,Y),!,fail.
sat_neq([X neq T|R1],R2,c):-                           % 5
         var(X),nonvar(T),
         functor(T,Tname,_),
         Tname \== with, 
         occurs(X,T),!,
         sat_step(R1,R2,_).
sat_neq([X neq Set|R1],R2,c):-                         % 7 
         var(X), nonvar(Set), Set = _S with _T,
         tail(Set,TS),samevar(X,TS),!,
         split(Set,_,L), 
         member(Ti,L) ,
         sat_step([Ti nin X|R1],R2,_).
sat_neq([X neq Set|R1],R2,c):-                         % 6         
         var(X), nonvar(Set), Set = _S with _T,
         occurs(X,Set),!,
         sat_step(R1,R2,_).
sat_neq([T1 neq T2|R1],R2,c):-      % 8(i) inequality between sets
         nonvar(T1),nonvar(T2), 
         T1 = _S with _A, T2 = _R with _B,
         sat_step([Z in T1, Z nin T2 | R1],R2,_).
sat_neq([T1 neq T2|R1],R2,c):-      % 8(ii)
         nonvar(T1),nonvar(T2), 
         T1 = _S with _A, T2 = _R with _B,!,
         sat_step([Z in T2, Z nin T1 | R1],R2,_).
sat_neq([X|R1],[X|R2],Stop):-
         sat_step(R1,R2,Stop).

%%%%%%%%%%%%%  membership

sat_in([T in Aggr|R1],R2,c):-                          % ground case
         ground(T), ground(Aggr),!,
         set_member(T,Aggr), 
         sat_step(R1,R2,_).
sat_in([T in Aggr|R1],R2,c):-                          % 2(i)
         nonvar(Aggr), Aggr = _R with A,
         sunify(A,T,C), 
         append(C,R1,R3), 
         sat_step(R3,R2,_).
sat_in([T in Aggr|R1],R2,c):-                          % 2(ii)
         nonvar(Aggr), Aggr = R with _A,!,
         sat_step([T in R|R1],R2,_).
sat_in([T in X|R1],R2,c):-                            % 3
         var(X), X = _N with T,
         sat_step(R1,R2,_).
         %N.B.: no test for X in T; replace
         %'X = N with T' with 'sunify(X,N with T,_)' to enforce it

%%%%%%%%%%%%%   non-membership

sat_nin([T1 nin Aggr|R1],R2,c):-                         % ground case
        ground(T1), ground(Aggr),!,
        \+set_member(T1,Aggr), 
        sat_step(R1,R2,_).
sat_nin([_T1 nin Aggr|R1],R2,c):-                         % 1
        nonvar(Aggr), Aggr == {},!,
        sat_step(R1,R2,_).
sat_nin([T1 nin Aggr|R1],R2,c):-                         % 2
        nonvar(Aggr), Aggr = S with T2,!,
        sat_step([T1 neq T2,T1 nin S|R1],R2,_).
sat_nin([T1 nin V|R1],R2,c):-
        var(V), occurs(V,T1),!,                         % 3
        sat_step(R1,R2,_).
sat_nin([X|R1],[X|R2],Stop):-
        sat_step(R1,R2,Stop).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     Preprocessing 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%   Set  preprocessor: 
%%%%%%%   from {...} to 'with'  notation  

preproc(X,X):- 
        var(X),!.      
preproc(X,Y1):-
        nonvar(X), is_set(X), !,
        set_preproc(X,Y),
        norep_in_set(Y,Y1). 
preproc(X,X):-
        atomic(X),!.
preproc((A & B), (A1 & B1)):-
        !, preproc(A,A1), preproc(B,B1).              
preproc(X,Z):-
        nonvar(X), 
        functor(X,F,_A), 
        =..(X,[F|ListX]),
        preproc_all(ListX,ListZ),
        =..(Z,[F|ListZ]).

preproc_all([],[]).
preproc_all([A|L1],[B|L2]):-
        preproc(A,B),
        preproc_all(L1,L2).

set_preproc(A,A) :- var(A),!.
set_preproc({},{}):- !.
set_preproc('{}'(A),B):-
       preproc_list(A,B),!.
set_preproc(_,_):-
       write(' wrong set term '),nl, fail.

preproc_list( A, {} with A):-
        var(A), !.
preproc_list((A1,B1),B2 with A2):- !,
        preproc(A1,A2),preproc_list(B1,B2).
preproc_list((A / X),X with B):-
        var(X),!, preproc(A,B).
preproc_list((A / X),Y with B):- 
        is_set(X),!,
        preproc(A,B), preproc(X,Y).
preproc_list((A / X),Y with B):- 
        X = _ with _,!,
        preproc(A,B), preproc(X,Y).
preproc_list(A1,{} with A2):-
        preproc(A1,A2).

%%%%%%  Set (multiset) postprocessor:  
%%%%%%  from 'with' ('mwith') to {...} (+{...}) notation  

postproc(X,X):- 
        var(X),!.      
postproc(X,X):-
        atomic(X),!.
postproc(X,Y):-
        nonvar(X), X = _ with _,!,
        norep_in_set(X,X1),
        with_postproc(X1,Y). 
postproc(X,Z):-
        nonvar(X), 
        =..(X,[F|ListX]),
        postproc_all(ListX,ListZ),
        =..(Z,[F|ListZ]).

postproc_all([],[]).
postproc_all([A|L1],[B|L2]):-
        postproc(A,B),
        postproc_all(L1,L2).

with_postproc(A,A) :- var(A),!.
with_postproc(K,K):- is_ker(K), !.
with_postproc(A,'{}'(B)):-
        postproc_list(A,B).

postproc_list(X with A1,(A2 / X)):-
        var(X),!,postproc(A1,A2).
postproc_list({} with A1,A2):- !,
        postproc(A1,A2).
postproc_list(K with A1,(A2 / K)):- 
        is_ker(K),!,postproc(A1,A2).
postproc_list(B1 with A1,(A2,B2)):-
        postproc(A1,A2),postproc_list(B1,B2).

%%%%%%%%%%%%%  Set manipulation pred's %%%%%%%%%%%

norep_in_set(X,X):- var(X),!.
norep_in_set(K,K) :- is_ker(K), !.
norep_in_set(R with A,S):-
       set_member_strong(A,R),!,
       norep_in_set(R,S).
norep_in_set(R with A,S with A):-
       norep_in_set(R,S).        

set_member(X,_R with Y):-
       sunify(X,Y,_), !.
set_member(X,R with _Y):-
       set_member(X,R).

set_member_strong(A,B):-
       nonvar(B),
       B = _ with X, 
       A == X,!.
set_member_strong(A,B):-
       nonvar(B), 
       B = Y with _,
       set_member_strong(A,Y).

is_set(X):- nonvar(X),functor(X,{},_).

is_ker(T) :-
        nonvar(T), functor(T,F,N),
        (F \== with,! ; N \== 2).

%%%%%%%%%%%%%  List manipulation pred's %%%%%%%%%%%

member(X,[X|_R]).
member(X,[_|R]):-member(X,R).

member_strong(A,[B|_R]):- 
         A == B, !.
member_strong(A,[_|R]):- 
         member_strong(A,R).

append([],L,L).                                        
append([X|L1],L2,[X|L3]):-
        append(L1,L2,L3).

norep_in_list([],[]):-!.
norep_in_list([A|R],S):-
         member_strong(A,R),!,
         norep_in_list(R,S).
norep_in_list([A|R],[A|S]):-
         norep_in_list(R,S).

list_to_conj(A & B,[A|R]):-
    !,list_to_conj(B,R).
list_to_conj(A,[A]):- !.
list_to_conj(true,[]).

occurs(X,Y):-
         var(Y),samevar(X,Y),!.
occurs(X,Y):-
         nonvar(Y),
         Y =.. [_|R],
         occur_list(X,R).

occur_list(_X,[]):-!,fail.
occur_list(X,[A|_R]):-
       occurs(X,A),!.
occur_list(X,[_|R]):-
       occur_list(X,R).




