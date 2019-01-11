
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  VERSION 4.9.1-20

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                          
%%                The {log} interpreter and solver                  
%%                                                           
%%                           VERSION 4.9.1   
%%                                             
%%                      original development by                                                          
%%                Agostino Dovier     Eugenio Omodeo          
%%                Enrico Pontelli     Gianfranco Rossi  
%%
%%                    subsequent enhancements by
%%                         Gianfranco Rossi
%%
%%                    with the contribution of 
%%       B.Bazzan  S.Manzoli  S.Monica  C.Piazza  L.Gelsomino
%%
%%                        Last revision by 
%%               Gianfranco Rossi and Maximiliano Cristia'
%%                         (April 2016)           
%%                                                              
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


:- module(setlog,[
             op(980,xfx,:),
             op(970,xfy,or),
             op(950,xfy,&),
             op(900,fy,[neg,naf]),
             op(800,xf,!),
             op(700,xfx,[in,neq,nin]), 
             op(670,xfx,\),                    
             op(650,yfx,[with,mwith]), 
             op(150,fx,*),
             setlog/0,           % for interactive use
             setlog/1,           % to call setlog from Prolog
             setlog/2,
             setlog/3,
             setlog/4,
             setlog_sc/3,
             setlog_consult/1,
             consult_lib/0,
             setlog_clause/1,
             setlog_config/1, 
             setlog_clear/0,   
             setlog_rw_rules/0,  
             setlog_help/0,           
             h/1 
   ]).

:- use_module(library(clpfd)). 
:- use_module(library(dialect/sicstus/timeout)).         

:- dynamic isetlog/2.                                  
:- dynamic newpred_counter/1. 
:- dynamic context/1. 
:- dynamic final/0.
:- dynamic nowarning/0.
:- dynamic filter_on/0.

:- dynamic nolabel/0.
:- dynamic noneq_elim/0.
:- dynamic noran_elim/0.
:- dynamic noirules/0.                                 
:- dynamic trace/1.

:- dynamic strategy/1.           % configuration params  
:- dynamic path/1. 
:- dynamic rw_rules/1. 
     
:- multifile replace_rule/6.     
:- multifile inference_rule/7.
:- multifile fail_rule/6.
:- multifile equiv_rule/3.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%                                    %%%%%%%%%%%%%%           
%%%%%%%%%%%   {log} interactive environment    %%%%%%%%%%%%%%               
%%%%%%%%%%%                                    %%%%%%%%%%%%%%               
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% The following predicates implement the {log} 
% interactive programming environment. This environment 
% offers a Prolog-like user interface, enriched with facilities
% for manipulating sets and multi-sets. The most notable
% syntactic differences w.r.t. std Prolog are: the use of '&' in 
% place of ',' to represent goal conjunction; the  use of 'or' 
% in place of ';' to represent goal disjunction; the use of 
% 'neg' or 'naf' in place of '\+' to represent negation (resp., 
% simplified Constructive Negation and Negation as Failure).  
% To enter the {log} interactive environment call the goal
% 'setlog.'. To exit, call the goal 'halt.'.
% N.B. {log}, in the current version, provides only a small 
% subset of Prolog built-ins and no support for program
% debugging at {log} program level.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

setlog :-
       top_level.

top_level :-
       retract_nowarning,  
       nl, write('{log}=> '),
       setlog_read_term(Goal,[variable_names(VarNames)]),
       solve(Goal,Constr),
       skip_return, 
       add_FDc(Constr,ConstrAll,Warning),
       fd_warning(Warning),
       chvar([],_,v(VarNames,ConstrAll),_,_,v(VarNames1,Constr1)),  
       mk_subs_ext(VarNames1,VarNames_ext1),    
       extract_vars(VarNames_ext1,Vars),
       nl, write_subs_constr(VarNames_ext1,Constr1,Vars),
       top_level.
top_level :-
       nl,write(no),nl,
       skip_return,  
       top_level.

welcome_message :-                                     
       nl, nl,
       write('              WELCOME TO {log} - version 4.7           '),
       nl, nl.

%%%%%%%%%%%%%%%%

setlog_read_term(Goal,Vars) :- 
       on_exception(Msg,read_term(Goal,Vars),syntax_error_msg(Msg)).  

syntax_error_msg(Text) :-
       write('Syntax error:'), nl,   
       write(Text), nl, 
       fail.

skip_return :-    
      read_pending_input(user_input,_C,[]).

%%%%%%%%%%%%%%%%

fd_warning(R) :- 
       var(R),!.
fd_warning(_) :- 
       print_warning('***WARNING***: non-finite domain').

print_warning(Msg) :-
       \+nowarning,!,
       nl, write(Msg), nl,
       assert(nowarning).
print_warning(_).

retract_nowarning :-
       retract(nowarning),!.
retract_nowarning.

%%%%%%%%%%%%%%%%

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

%%%%%%%%%%%%%%%% write substitutions and constraints

write_subs_constr([],[],_) :- !,    
       write(yes), nl.                       
write_subs_constr(Subs,Constr,Vars) :-  
      (Subs = [],!, true
       ; 
       Subs = [true|_],!,write('true'),Prn=y
       ;
       write_subs_all(Subs,Prn)
      ), 
       write_constr(Constr,Vars,Prn), 
       ask_the_user(Prn).

ask_the_user(Prn):-
       var(Prn),!.
ask_the_user(_):-
       nl,  
       nl, write('Another solution?  (y/n)'),
%       get(C), skip(10),
       get_single_char(C), 
       (C \== 121,! 
        ; 
        retract_nowarning, fail
       ).

write_subs_all([],_).
write_subs_all([N1=V1|R],Prn) :-
        write(N1), write(' = '), write(V1), Prn=y,
       (R = [],!,true ; 
        R = [true|_],!,true ;
        write(',  '), nl, write_subs_all(R,Prn) ).  

write_constr(Constr,Vars,Prn) :-             
       postproc(Constr,Constr_ext),
       write_constr_first(Constr_ext,Vars,Prn).

write_constr_first([],_,_) :- !.                
write_constr_first([C|Constr],Vars,Prn) :-             
       nl, write('Constraint: '), 
       write_atomic_constr(C), Prn=y,
       write_constr_all(Constr,Vars).

write_constr_all([],_) :- !.                
write_constr_all([C|Constr],Vars) :-             
       write(', '), write_atomic_constr(C),
       write_constr_all(Constr,Vars).
         
write_atomic_constr(solved(C,_,_,_)) :- !,
       write(C).
write_atomic_constr(delay(irreducible(C)&true,_)) :- !, 
    write(irreducible(C)).
write_atomic_constr(C) :- !,
       write(C).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%   Prolog to {log} interface  %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% The following predicates allow a Prolog program to use the 
% {log} facilities for set/bag definition and manipulation
% (without leaving the Prolog execution environment).
% In particular, they provide a (Prolog) predicate for calling 
% any {log} goal G, possibly involving {log} set constraints.
% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%% setlog(+Goal) 
%
setlog(Goal) :-
       setlog(Goal,_).

%%%% setlog(+Goal,-OutConstraintList) 
%
setlog(Goal,OutConstrLst) :-
       nonvar(Goal), 
       retract_nowarning,  
       copy_term(Goal,NewGoal),
       solve(NewGoal,C),
       remove_solved(C,C1),                   %remove info about "solved" constraints    
       add_FDc(C1,Constr,Warning),            %add the possibly remaining interval constr's
       fd_warning(Warning),
       postproc(Constr,OutConstrLst),         %from 'with' to {...} notation  
       postproc(NewGoal,NewGoal_ext),
       postproc(Goal,Goal_ext),
       Goal_ext = NewGoal_ext.                %apply sustitutions to the original variables

%%%% setlog(+Goal,+InConstraintList,-OutConstraintList) 
%
setlog(Goal,InConstrLst,OutConstrLst) :-  
       nonvar(Goal), nonvar(InConstrLst),
       retract_nowarning,  
       list_to_conj(InConstr,InConstrLst),             %from list (InConstrLst) to conjunction (InConstr)     
       conj_append(Goal,InConstr,ExtdGoal),
       copy_term(ExtdGoal,NewGoal),
       solve(NewGoal,OutCLstIntl),
       remove_solved(OutCLstIntl,ROutCLstIntl),        %remove info about "solved" constraints
       add_FDc(ROutCLstIntl,OutFinalCLstIntl,Warning), %add the possibly remaining interval constr's
       fd_warning(Warning),
       postproc(OutFinalCLstIntl,OutConstrLst),        %from 'with' to {...} notation      
       postproc(NewGoal,NewGoal_ext),
       postproc(ExtdGoal,ExtdGoal_ext),
       ExtdGoal_ext = NewGoal_ext.                     %apply sustitutions to the original variables         

%%%% setlog_partial(+Goal,+InConstraintList,-OutConstraintList) 
%
setlog_partial(Goal,InConstrLst,OutConstrLst) :-  
       nonvar(Goal), nonvar(InConstrLst),
       retract_nowarning,  
       list_to_conj(InConstr,InConstrLst),    %from list (InConstrLst) to conjunction (InConstr)     
       conj_append(Goal,InConstr,ExtdGoal),
       copy_term(ExtdGoal,NewGoal),       
       transform_goal(NewGoal,B),             %from extl to internal repr. (remove SF, RUQ, {...})
       solve_goal(B,Constr),                  %call the constraint solver (in 'non-final' mode)
       postproc(Constr,OutConstrLst),         %from 'with' to {...} notation     
       postproc(NewGoal,NewGoal_ext),
       postproc(ExtdGoal,ExtdGoal_ext),
       ExtdGoal_ext = NewGoal_ext.            %apply sustitutions to the original variables             

%%%% setlog_sc(+Constraint,+InConstraintList,-OutConstraintList) 
%
setlog_sc(Constr,InConstrLst,OutConstrLst) :- %to solve {log} set constraints (partial solve)
       nonvar(Constr), nonvar(InConstrLst),
       retract_nowarning,  
       list_to_conj(InConstr,InConstrLst),    %from list (InConstrLst) to conjunction (InConstr) 
       conj_append(Constr,InConstr,CS),
       copy_term(CS,NewCS),
       preproc_goal(NewCS,NewCSIntl),         %from {...} to 'with' notation;   
       solve_goal(NewCSIntl,OutCLstIntl),     %call the constraint solver (in 'non-final' mode)
       postproc(OutCLstIntl,OutConstrLst),    %from 'with' to {...} notation  
       postproc(CS,CSExt),
       postproc(NewCS,NewCSExt),
       CSExt = NewCSExt.                      %apply sustitutions to the original variables

%%%% setlog with timeout
%%%% setlog(+Goal,+TimeOut,-OutConstraintList,-Res) (Res = success | time_out | maybe)
%
setlog(Goal,TimeOut,OutConstrLst,Res) :-
       integer(TimeOut),!,
       time_out(setlog(Goal,OutConstrLst),TimeOut,Return),
       setlogTimeOut_cont1(Goal,TimeOut,OutConstrLst,Return,Res).

setlogTimeOut_cont1(_Goal,_TimeOut,_OutConstrLst,success,success) :- !.
setlogTimeOut_cont1(Goal,TimeOut,OutConstrLst,time_out,Res) :-
       ssolve(noirules,[],[]),
       time_out(setlog(Goal,OutConstrLst),TimeOut,Return),
       setlogTimeOut_cont2(Goal,TimeOut,OutConstrLst,Return,Res).

setlogTimeOut_cont2(_Goal,_TimeOut,_OutConstrLst,success,success) :- !.
setlogTimeOut_cont2(Goal,TimeOut,OutConstrLst,time_out,Res) :-
       ssolve(noneq_elim,[],[]),
       time_out(setlog(Goal,OutConstrLst),TimeOut,Return),!,
       setlogTimeOut_cont3(Goal,TimeOut,OutConstrLst,Return,Res).
setlogTimeOut_cont2(_Goal,_TimeOut,_OutConstrLst,time_out,_) :-
       fail.

setlogTimeOut_cont3(_Goal,_TimeOut,_OutConstrLst,success,maybe) :- !,
       write('WARNING: possible not solved form'),nl.
setlogTimeOut_cont3(Goal,TimeOut,OutConstrLst,time_out,Res) :-
       ssolve(noran_elim,[],[]),
       time_out(setlog(Goal,OutConstrLst),TimeOut,Return),!,
       setlogTimeOut_cont4(Goal,TimeOut,OutConstrLst,Return,Res).
setlogTimeOut_cont3(_Goal,_TimeOut,_OutConstrLst,time_out,_) :-
       fail.

setlogTimeOut_cont4(_Goal,_TimeOut,_OutConstrLst,success,maybe) :- !,
       write('WARNING: possible not solved form'),nl.
setlogTimeOut_cont4(_Goal,_TimeOut,_OutConstrLst,time_out,time_out) :-
       write('WARNING: time out'),nl.

setlog_clear :-
       ssolve(irules,[],[]),
       ssolve(neq_elim,[],[]),
       ssolve(ran_elim,[],[]).

%%%% other predicates for Prolog to {log} interface 

setlog_consult(File) :-                   %like setlog(consult(File))
       setlog(consult(File,mute),_).      %but no message is sent to the std output

setlog_clause(Clause) :-                  %for compatibility with previous versions      
       setlog(assert(Clause),_).

consult_lib :-                            %to consult the {log} library file
       setlog(consult_lib,_).             

setlog_config(ConfigParams) :-            %to modify {log}'s configuration parameters
       set_params(ConfigParams).                      
  
setlog_rw_rules :-                        %to load the filtering rule library
       rw_rules(Lib),
       mk_file_name(Lib,FullName),
       consult(FullName). 
 
%%%% auxiliary predicates for Prolog to {log} interface 

remove_solved([],[]).
remove_solved([solved(C,_,_,_)|R],[C|RR]) :- !,
    remove_solved(R,RR).
remove_solved([delay(irreducible(C)&true,_)|R],[irreducible(C)|RR]) :- !, 
    remove_solved(R,RR).
remove_solved([C|R],[C|RR]) :-
    remove_solved(R,RR).
   
set_params([]).                          
set_params([P1|ParamsList]) :-
    apply_params(P1),
    set_params(ParamsList).

apply_params(strategy(Str)) :- !,         
    replace_unitCl(strategy(_),Str).
apply_params(path(Path)) :- !,
    replace_unitCl(path(_),Path).
apply_params(rw_rules(FileName)) :- !,
    replace_unitCl(rw_rules(_),FileName).
%%% to be continued

replace_unitCl(Cl,NewParm) :-             
    retract(Cl),!,
    Cl =.. [F,_X], NewCl =.. [F,NewParm], 
    assert(NewCl).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%        The help sub-system   %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

setlog_help :- h(setlog).           

h(setlog) :- 
   nl, 
   write('   -   h(syntax), h(constraints), h(builtins), h(lib), h(prolog) to get help '), nl,
   write('       information (resp., about: {log} syntactic convenctions, {log} constraints, '), nl,
   write('       {log} built-in predicates, {log} library predicates, Prolog predicates'), nl,
   write('       for accessing {log})'), nl,
   write('   -   h(all) to get all available help information'), nl,
   write('   -   setlog/0: to enter the {log} interactive environment'),nl,
   write('   -   setlog(G), setlog(G,C): to call a {log} goal G, '), nl,
   write('       possibly getting an (output) {log} constraint C'), nl,
   write('   -   setlog(G,InCLst,OutCLst), setlog_partial(G,InCLst,OutCLst), '), nl,
   write('       setlog_sc(C,InCLst,OutCLst): to solve a {log} goal G / constraint C '), nl,
   write('       with a (possibly empty) input constraint list InCLst '), nl,
   write('       and output constraint list OutCLst '), nl.

h(all) :-
   h(syntax), 
   h(constraints),
   h(builtins),
   h(prolog),
   h(lib).

h(syntax) :- 
   nl,    
   write('%%%%%%%%%   Syntactic conventions  %%%%%%%%%'),
   nl, nl,
write('   1.  Extensional set/multiset terms:'), nl,                  
   write('        - {a,b,c} is a set containing three elements, a, b, c'),nl,
   write('          (equivalent to {} with c with b with a)'), nl,         
   write('        - {a,b\\R} is the set {a,b} U R'), nl,          
   write('          (equivalent to R with b with a)'), nl,       
   write('        - *({a,b,b}) (or, * {a,b,b}) is a multiset containing the elements,'),nl,
   write('          ''a'' (1 occurrence) and  ''b'' (2 occurrences)'),nl,   
   write('          (equivalent to {} mwith c mwith b mwith a)'), nl,         
   write('        - *({a,b\\R}) is the multiset *({a,b}) U R'), nl,      
   write('          (equivalent to R mwith b mwith a)'), nl,       
   write('        - {} is the empty set/multiset'), nl,                             
   write('        - int(h,k) (interval, h,k integer constants) is the set of'), nl,
   write('          integer numbers ranging from h to k (k>=h) or the empty set (k<h)'), nl, 
   nl,      
write('   2.  RUQs: '), nl,                            
   write('       (''a'' either a set or a multiset or a list or an interval int(h,k))'), nl,
   write('        - forall(X in a, G),'), nl, 
   write('          X variable and G any {log} goal containing X'), nl,  
   write('        - forall(X in a, exists(V,G)),'),nl,
   write('        - forall(X in a, exists([V1,...,Vn],G)),'), nl, 
   write('          V1,...,Vn variables local to G'), nl,
   nl,
write('   3.  Intensional set terms:'), nl,                                 
   write('        - {X : G}, X variable and G any {log} goal containing X'), nl,
   write('        - {X : exists(V,G)}, V variable local to G'), nl,
   write('        - {X : exists([V1,...,Vn],G)}, '), nl, 
   write('          V1,...,Vn variables local to G'), nl,
   nl,
write('   4.  Syntactic differences w.r.t. std Prolog:'), nl,
   write('        - &  is used in place of  ,  in clause bodies'), nl,
   write('        - or  is used in place of  ;'),
                    write('  to represent goal disjunction.'), nl,
   write('        - neg or naf are used in place of  \\+'),
                    write('  to represent negation (resp., '), nl,
   write('          simplified Constructive Negation and Negation as Failure)'),  
   nl.    

h(constraints) :- 
   nl,    
   write('%%%%%%%%%   {log} constraints  %%%%%%%%%'),
   nl, nl,
write('   1.  General constraints:'), nl,
   write('       (''t_i'' any term, including non-ground intervals)'), nl,
   write('        - t1 = t2  (equality)'), nl,
   write('        - t1 neq t2  (non-equality)'), nl, 
   nl, 
write('   2.  Set/multiset/list constraints:'), nl,
   write('       (''t'',''t_i'' any term, including non-ground intervals,'), nl,
   write('        ''s'',''s_i'' either a set or a bounded interval,'), nl,
   write('        ''sint'' either a set of non-negative integers or a bounded interval,'), nl,
   write('        ''n'' a variable or an integer constant)'), nl,
   write('        - t1 in t2 (membership)'), nl,
   write('        - t1 nin t2 (non-membership)'), nl,   
   write('        - inters(t1,t2,t3) (intersection)'), nl,
   write('        - un(s1,s2,s3) (union)'), nl,
   write('        - nun(s1,s2,s3) (non-union)'), nl,   
   write('        - disj(s1,s2) (disjointness)'), nl,
   write('        - ndisj(s1,s2) (non-disjointness)'), nl,  
   write('        - less(s1,t,s3) (element removal)'), nl,
   write('        - subset(s1,s2) (subset)'), nl,
   write('        - nsubset(s1,s2) (not subset)'), nl,
   write('        - ssubset(s1,s2) (strict subset)'), nl,
   write('        - ninters(s1,s2,s3) (not intersection)'), nl,
   write('        - diff(s1,s2,s3) (difference)'), nl,
   write('        - ndiff(s1,s2,s3) (not difference)'), nl,
   write('        - sdiff(s1,s2,s3) (symmetric difference)'), nl,
   write('        - size(s,n) (cardinality)'), nl,
   write('        - sum(sint,n) (sum all elements (non-negative integers only))'), nl,
   write('        - smin(sint,n) (minimum element)'), nl,
   write('        - smax(sint,n) (maximum element)'), nl,
   write('        - set(t) (t is a set)'), nl,  
   write('        - bag(t) (t is a multiset)'), nl, 
   write('        - list(t) (t is a list)'), nl, 
   write('        - npair(t) (t is not a pair)'), nl, 
   nl,
write('   3.  Integer constraints:'), nl,
   write('       (''e_i'' an integer expression, ''n'' a variable or an integer constant)'), nl,
   write('        - n is e1 (equality - with evaluation of expression e)'), nl,
   write('        - e1 =< e2 (less or equal), e1 < e2 (less)'), nl,  
   write('        - e1 >= e2 (greater or equal), e1 > e2 (greater)'), nl,  
   write('        - e1 =:= e2 (equal), e1 =\\= e2 (not equal)'), nl,  
   write('        - integer(n) (n is an integer number)'), nl,  
   write('        - ninteger(n) (n is not an integer number)'),nl,   
   nl, 
write('   4.  Binary relation and partial function constraints:'), nl,   
   write('       (''t'' any term, "s",  ''s_i'' either a set or a bounded interval,'), nl,
   write('         ''r'', ''r_i'' a binary relation, ''f'' a partial function)'), nl,
   write('        - rel(t)/nrel(t) (t is/is_not a binary relation)'), nl,  
   write('        - dom(r,s) (domain)'), nl,   
   write('        - ran(r,s) (range)'), nl,   
   write('        - inv(r,s) (inverse relation)'), nl,   
   write('        - comp(r1,r2,r3) (composition)'), nl, 
   write('        - dres(s,r1,r2) (domain restriction)'), nl,   
   write('        - rres(s,r1,r2) (range restriction)'), nl,   
   write('        - ndres(s,r1,r2) domain anti-restriction)'), nl,   
   write('        - nrres(s,r1,r2) (range anti-restriction)'), nl, 
   write('        - rimg(s1,r,s2) (relational image)'), nl,   
   write('        - oplus(r1,r2,r3) (overriding)'), nl,  
   write('        - pfun(t)/npfun(t)(t is/is_not a partial function)'), nl,  
   write('        - apply(f,t1,t2) (function application)'), nl,  
   write('        - id(s,f) (identity relation)'), nl,   
   write('        - dompf(f,s) (domain of a partial function)'), nl,   
   write('        - comppf(r1,f,r2) (composition of partial functions)'), nl, 
   nl.
        
h(builtins) :-
   h(sbuilt),
   h(pbuilt).

h(sbuilt) :-
   nl,
   write('%%%%%%%%% {log} specific built-in predicates %%%%%%%%%'),
   nl, nl,
   write('   -   halt/0: to leave the {log} interactive environment'),
        write(' (go back to the host environment) '), nl,
   write('   -   help/0: to get general help information about {log}'), nl,
   write('   -   prolog_call(G): to call any Prolog goal G from {log}'),nl,  
   write('   -   call(G), call(G,C): to call a {log} goal G, possibly with constraint C'),nl,  
   write('   -   solve(G): like call(G) but all constraints generated by G are immediately solved'),nl,  
   write('   -   consult_lib/0: to consult the {log} library file setloglib.slog'),nl,  
   write('   -   add_lib(F): to add any file F to the {log} library '),nl,  
   write('   -   G!: to make a {log} goal G deterministic'), nl,
   write('   -   delay(G,C), G, C {log} goals: to delay execution of G '),nl,     
   write('       until either C holds or the computation ends; '), nl,
   write('   -   delay(irreducible(G),C), G, C {log} goals: to delay execution of G '),nl,
   write('       until C holds; otherwise return irreducible(G)'), nl,
   write('   -   nolabel/0, label/0: to deactivate/activate the global FD labeling'),nl,
   write('       (default: label)'), nl, 
   write('   -   labeling(X): to force labeling for the domain variable X'),nl,
   write('   -   strategy(S): to change goal atom selection strategy to S'),nl,
   write('       (S: cfirst, ordered, cfirst(list_of_atoms))'), nl, 
   write('   -   notrace/0, trace(Mode): to deactivate/activate constraint solving tracing; '),nl,
   write('       Mode=sat: general, Mode=irules: inference rules only (default: notrace)'), nl, 
   write('   -   noneq_elim/0, neq_elim/0: to deactivate/activate elimination of neq-'),nl,
   write('       constraints (default: neq_elim)'), nl, 
   write('   -   nonran_elim/0, ran_elim/0: to deactivate/activate elimination of ran-'),nl,
   write('       constraints of the form ran(R,{...}) (default: ran_elim)'), nl, 
   write('   -   noirules/0, irules/0: to deactivate/activate inference rules '),nl,
   write('       (default: irules)'), nl, 
   write('   -   time(G,T): to get CPU time (in milliseconds) for solving goal G'),
   nl.

h(pbuilt) :-
   nl,
   write('%%%%%%%% Prolog-like built-in predicates (redefined in {log} %%%%%%%%'),
   nl, nl,
   write_built_list,
   write('   -   read/1'),nl,
   write('   -   write/1'),nl,
   write('   -   call/1'),nl,
   write('   -   assert/1'),nl,
   write('   -   consult/1'),nl,
   write('   -   listing/0'),nl,
   write('   -   abolish/0'),nl.
  
h(lib) :-
   nl,
   write('%%%%%%%% {log} library %%%%%%%%'), nl, nl,
   check_lib,
   nl. 

h(prolog) :- 
   nl,
   write('%%%%%%%% Prolog predicates for accessing {log} facilities %%%%%%%%%'),
   nl,nl,
   write('   -   setlog/0: to enter the {log} interactive environment'),nl,
   write('   -   setlog(G), setlog(G,C): to call a {log} goal G, '), nl,
   write('       possibly getting an (output) {log} constraint C'), nl,
   write('   -   setlog(G,InCLst,OutCLst), setlog_partial(G,InCLst,OutCLst), '), nl,
   write('       setlog_sc(C,InCLst,OutCLst): to solve a {log} goal G / constraint C '), nl,
   write('       with a (possibly empty) input constraint list InCLst '), nl,
   write('       and output constraint list OutCLst '), nl,
   write('   -   setlog_consult(F): to consult a {log} file F '),nl,
   write('   -   consult_lib: to consult the {log} library file '),nl,
   write('   -   setlog_clause(Cl): to add a {log} clause Cl to the current {log} program '),nl,
   write('   -   setlog_config(list_of_params): to modify {log} configuration parameters '),nl,
   write('       (parameters: strategy(S), path(Path), rw_rules(File))'), nl,
   write('   -   setlog_rw_rules: to load the filtering rule library'),
   nl.
 
write_built_list :-
   sys(N,Ar),
   write('   -   '),write(N),write('/'),write(Ar),nl,
   fail.
write_built_list.
 
check_lib :-
   solve(setlog_lib_help,_),!.
check_lib :-
   write('{log} library predicates not available'),nl,
   write('Type consult_lib to load the {log} library '),nl.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%     The inference engine     %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
        
%%%% solve(+Goal,-Constraint)            Goal: {log} goal in external form
%
solve(Goal_int_ruq,Constr):-   
       transform_goal(Goal_int_ruq,B),
%DBG%  nl,write('NEW GOAL: '),write(B),nl, 
       solve_goal_fin(B,Constr).

%%%% solve_goal_fin(+Goal,-Constraint)   Goal: {log} goal in internal form
%
solve_goal_fin(G,ClistNew) :-
       constrlist(G,GClist,GAlist),
       solve_goal_fin_constr(GClist,GAlist,ClistNew).

solve_goal_fin_constr(GClist,GAlist,ClistNew):-  
       solve_goal_constr(GClist,GAlist,Clist), 
       final_sat(Clist,ClistNew).

%%%% solve_goal(+Goal,-Constraint)       Goal: {log} goal in internal form
%
solve_goal(G,ClistNew) :-
       constrlist(G,GClist,GAlist),
       solve_goal_constr(GClist,GAlist,ClistNew). 

%%%% solve_goal_constr(+Constraint,+Non_Constraint,-Constraint)
%
solve_goal_constr(Clist,[],CListCan):- !, 
       sat(Clist,CListCan,nf). 
solve_goal_constr(Clist,[true],CListCan):- !, 
       sat(Clist,CListCan,nf). 
solve_goal_constr(Clist,[A|B],CListOut):-
       sat(Clist,ClistSolved,nf),
       sat_or_solve(A,ClistSolved,ClistNew,AlistCl,nf),
       append(AlistCl,B,AlistNew),
       solve_goal_constr(ClistNew,AlistNew,CListOut).

sat_or_solve(A,Clist_in,Clist_out,[],F) :-
       atomic_constr(A),!,
       sat([A|Clist_in],Clist_out,F).
sat_or_solve(A,Clist_in,Clist_out,Alist_out,_) :-
       ssolve(A,ClistCl,Alist_out),
       append(Clist_in,ClistCl,Clist_out).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
%%%% ssolve(+Atom,-Constraint,-Non_Constraint)

ssolve(true,[],[]):- !.                  %% unit goal

ssolve(neg A,ClistNew,[]):-              %% simplified constructive negation
        !,c_negate(A,ClistNew).
ssolve(naf A,ClistNew,[]):-              %% negation as failure
        !,naf_negate(A,ClistNew).

ssolve((G1 or G2),ClistNew,[]):-         %% goal disjunction 
        !,(solve_goal(G1,ClistNew)
          ;
           solve_goal(G2,ClistNew) ).

ssolve(call(A),C,[]):-                   %% meta call    
        !,solve_goal(A,C).

ssolve(call(A,C),C,[]):-                 %% meta call       
        !,solve_goal(A,C).

ssolve(solve(A),C,[]):-                  %% forces goal A to be completely solved    
        !,solve_goal_fin(A,C).

ssolve((A)!,C,[]):-                      %% deterministic call
        !,solve_goal(A,C),!.
  
ssolve(ruq_call(S,InName,VarList),Cout,[]) :-       %% RUQs
        !,solve_RUQ(S,InName,VarList,[],Cout).   

ssolve(sf_call(S,GName,PName,VarList),Cout,[]) :-   %% SF
        !, solve_SF(S,GName,PName,VarList,[],Cout).   

ssolve(prolog_call(A),[],[]):-    %% Prolog call (any predicate)
        nonvar(A),!,A.   
                 
ssolve(A,[],[]):-                 %% Prolog built-in predicates
        nonvar(A),functor(A,F,N),
        sys(F,N),!,A.   

ssolve(A,C,[]):-                  %% {log} built-in predicates
        sys_special(A,C),!.   

ssolve(labeling(X),[],[]):-       %% explicit clpfd labeling
        nonvar(X),!. 
ssolve(labeling(X),[],[]):- !,    
        get_domain(X,X in D), 
        labeling1(X,D).                

ssolve(label,[],[]):- !,          %% (re-)activate automatic clpfd labeling
        retract_nolabel.

ssolve(nolabel,[],[]):-           %% deactivate automatic clpfd labeling
        nolabel,!.
ssolve(nolabel,[],[]):-    
        assert(nolabel).

ssolve(notrace,[],[]):- !,        %% deactivate constraint solving tracing
        retract_trace.

ssolve(trace(sat),[],[]):-        %% activate constraint solving tracing
        trace(sat),!.
ssolve(trace(irules),[],[]):-        
        trace(irules),!.
ssolve(trace(Mode),[],[]):-  
        (Mode==sat,! ; Mode==irules),   
        assert(trace(Mode)).

ssolve(neq_elim,[],[]):- !,       %% (re-)activate automatic neq elimination
        retract_noneq_elim.

ssolve(noneq_elim,[],[]):-        %% deactivate automatic neq elimination
        noneq_elim.
ssolve(noneq_elim,[],[]):-     
        assert(noneq_elim).

ssolve(ran_elim,[],[]):- !,       %% (re-)activate automatic ran elimination
        retract_noran_elim.

ssolve(noran_elim,[],[]):-        %% deactivate automatic ran elimination
        noran_elim.
ssolve(noran_elim,[],[]):-     
        assert(noran_elim).

ssolve(irules,[],[]):- !,         %% (re-)activate automatic application of inference rules
        retract_irules.

ssolve(noirules,[],[]):-          %% deactivate automatic application of inference rules
        noirules,!.
ssolve(noirules,[],[]):-    
        assert(noirules).

ssolve(strategy(Str),[],[]):- !,  %% change goal atom selection strategy    
        retract(strategy(_)),!,
        assert(strategy(Str)).

ssolve(A,C,D):-                   %% program defined predicates
        our_clause(A,B,C1),
        constrlist(B,C2,D),
        append(C1,C2,C).
our_clause(A,B,C):-
        functor(A,Pname,N),
        functor(P,Pname,N),
        isetlog((P :- B),_), 
        sunify(P,A,C).

retract_nolabel :-
        retract(nolabel),!.
retract_nolabel.

retract_noneq_elim :-
        retract(noneq_elim),!.
retract_noneq_elim.

retract_noran_elim :-
        retract(noran_elim),!.
retract_noran_elim.

retract_irules :-
        retract(noirules),!.
retract_noirules.

retract_trace :-
        retractall(trace(_)),!.
retract_trace.


%%%% constrlist(+Atom_conj,-Constraint_list,-Constraint/Non_Constraint_list)

constrlist(A,CList,C_NCList) :-    
        constrlist(A,CList,StdC_NCList,SpecC_NCList),
        append(SpecC_NCList,StdC_NCList,C_NCList).
constrlist(A & B,[A|B1],B2,B3):-
        selected_atomic_constr(A),!,  
        constrlist(B,B1,B2,B3).         
constrlist(A & B,B1,B2,[A|B3]):-
        selected_user_atom(A),!,  
        constrlist(B,B1,B2,B3).         
constrlist(A & B,B1,[A|B2],B3):-
        !,constrlist(B,B1,B2,B3).                       
constrlist(A,[A],[],[]):-
        selected_atomic_constr(A),!.   
constrlist(A,[],[],[A]):-
        selected_user_atom(A),!.   
constrlist(A,[],[A],[]).

selected_atomic_constr(A) :-       
        strategy(cfirst),!,        %% cfirst: select primitive constraints first    
        atomic_constr(A).
selected_atomic_constr(A) :-
        strategy(cfirst(_)),!,
        atomic_constr(A).
selected_atomic_constr(A) :-
        strategy(ordered),!,       %% ordered: select all atoms in the order they occur    
        A = (_ = _).

selected_user_atom(A) :-           
        strategy(cfirst(LAtoms)),  %% cfirst(LAtoms): select atoms in LAtoms just after primitive constraints  
        member(A,LAtoms).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%   Negation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

naf_negate(A,[]) :-                 %% Negation as Failure
       \+ solve_goal_fin(A,_).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

c_negate(A,ClistNew) :-             %% Simplified Constructive Negation 
       chvar([],L1,A,[],L1new,B),
       constrlist(B,Clist,Alist),
       solve_goal_fin_constr(Clist,Alist,Clist0),
       final_sat(Clist0,Clist1),!, 
       dis(L1,L1new,Dis),
       append(Clist1,Dis,CC),
       neg_solve(CC,ClistNew,L1).
c_negate(_A,[]). 
       
neg_solve([],[],_) :- !, fail.
neg_solve(Clist,ClistNew,LVars) :-
       neg_constr_l(Clist,ClistNew,LVars).     

neg_constr_l([],_,_) :- !,fail.
neg_constr_l(Clist,ClistNew,LVars) :-
       member(C,Clist),
       neg_constr(C,ClistNew,LVars).       

neg_constr(A nin B,[A in B],_) :- !.           
neg_constr(A neq B,[],LVars) :- !,            
      extract_vars(B,V),
      subset_strong(V,LVars),
      sunify(A,B,_).     
neg_constr(A = B,[A neq B],LVars) :-   
      extract_vars(B,V),
      subset_strong(V,LVars),!.
neg_constr(_A = _B,_,_) :-   
      print_warning('***WARNING***: unimplemented form of negation').

dis([],[],[]):-!.
dis([X|L1],[Y|L2],[X=Y|L3]):-
      nonvar(Y),!,
      dis(L1,L2,L3).
dis([X|L1],[Y|L2],[X=Y|L3]):-
      var(Y),
      member_strong(Y,L2),!,
      dis(L1,L2,L3).
dis([X|L1],[Y|L2],L3):-
      X=Y,
      dis(L1,L2,L3).     


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%  Intensional sets and RUQs processing   
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Intensional sets

solve_SF(S,_GName,PName,VarList,Cin,Cout) :- 
        nonvar(S), S = {},!,
        InPred =.. [PName,{}|VarList],     
        solve_goal_fin_constr(Cin,[neg(InPred & true)],Cout).
        % print_warning_SF(VarList).
solve_SF({},_GName,PName,VarList,Cin,Cout) :- 
        InPred =.. [PName,{}|VarList],     
        solve_goal_fin_constr(Cin,[neg(InPred & true)],Cout).
        % print_warning_SF(VarList).
solve_SF(S,GName,_PName,VarList,_Cin,Cout) :- 
        InPred =.. [GName,X|VarList],
        setof(X,solve_goal_fin(InPred,C1),L),
        list_to_set(L,S,C2),
        append(C2,C1,Cout).
        % print_warning_SF(VarList).

%print_warning_SF(VarList) :-      % uncomment to check possibly unsafe uses of intensional sets
%         \+ground(VarList),!,     
%         print_warning('***WARNING***: uninstantiated free vaiable in intensional set').


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% RUQs

solve_RUQ(S,_,_,C,C) :-
        nonvar(S), 
        empty_aggr(S),!.
solve_RUQ(S,InName,VarList,Cin,Cout) :-
        nonvar(S), S = int(L,H),!,                % solve RUQ's over intervals
        force_bounds_values(L,H),
        solve_RUQ_int(int(L,H),InName,VarList,Cin,Cout).
solve_RUQ(S,InName,VarList,Cin,Cout) :-           % over a given aggregate
        nonvar(S),!,
        aggr_comps(S,X,R),
        InPred =.. [InName,X|VarList],
        solve_goal_fin_constr(Cin,[InPred],C2),
        solve_RUQ(R,InName,VarList,C2,Cout).
solve_RUQ(S,_,_,C,C) :-
        var(S), S = {}.
solve_RUQ(S,InName,VarList,Cin,Cout) :-           % over an unspecified aggregate
        var(S), S = R with X,                             
        InPred =.. [InName,X|VarList],
        solve_goal_fin_constr([X nin R|Cin],[InPred],C2),
        solve_RUQ(R,InName,VarList,C2,Cout), 
        aggr_ordered(S).

solve_RUQ_int(int(L,L),InName,VarList,Cin,Cout) :- !,   
        InPred =.. [InName,L|VarList],    % forall(X in int(L,L),InName(X,VarList))
        solve_goal_fin_constr(Cin,[InPred],Cout).
solve_RUQ_int(int(L,H),InName,VarList,Cin,Cout) :-    
        InPred =.. [InName,L|VarList],    % forall(X in int(L,H),InName(X,VarList))
        solve_goal_fin_constr(Cin,[InPred],C2),
        L1 is L + 1,
        solve_RUQ(int(L1,H),InName,VarList,C2,Cout).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% auxiliary predicates for solve_RUQ/5

aggr_ordered(S) :- var(S),!.
aggr_ordered({}) :- !.
aggr_ordered(S) :- 
       S = R with X,
       in_order(X,R), 
       aggr_ordered(R).

in_order(_A,S) :- var(S),!.
in_order(_A,{}) :- !.
in_order(A,S) :-  
       S = _R with _B,
       var(A), !.
in_order(A,S) :-  
       S = R with B,
       var(B), in_order(A,R),!.
in_order(A,S) :-  
       S = _R with B,
       A @=< B.

force_bounds_values(A,B) :-
       solve_FD(A =< B),     
       (var(A),!, labeling(A) ; true),
       (var(B),!, labeling(B) ; true).

  
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%  "Built-in" predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Prolog built-in predicates

sys(nl,0).
sys(ground,1).
sys(var,1).
sys(nonvar,1).
sys(name,2).
sys(functor,3).
sys(arg,3).
sys(=..,2).
sys(==,2).
sys(\==,2).
sys(@<,2).
sys(@>,2).
sys(@=<,2).
sys(@>=,2).
%%********* list to be completed!!********* 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% {log} built-in predicates

sys_special(write(T),[]) :-            %% write
      !,postproc(T,NewT),
      write(NewT).

sys_special(read(T),C) :-              %% read
      !,setlog_read(Tout),
      preproc(Tout,T,C).

sys_special(assert(Clause),[]):-       %% assert
      !,setassert(Clause).

sys_special(consult_lib,[]):-          %% stores clauses contained in the {log} library file into                       
      !,rem_clause(lib), rem_clause(tmp(lib)),       %% the current program in the library ctxt   
      setlog_open('setloglib.slog',read,FileStream), %% (removing all clauses possibly stored 
      switch_ctxt(lib,OldCtxt),                      %% in the same ctxt) 
      read_loop_np(FileStream),
      switch_ctxt(OldCtxt,_),
      close(FileStream). 

sys_special(add_lib(File),[]):-        %% adds clauses contained in file F to the current 
      !, setlog_open(File,read,FileStream),          %% program in the library ctxt (without
      switch_ctxt(lib,OldCtxt),                      %% removing existing clauses)
      read_loop_np(FileStream),
      switch_ctxt(OldCtxt,_),
      close(FileStream). 

sys_special(consult(File),[]):-        %% stores clauses contained in file F into                            
      !, setlog_open(File,read,FileStream),          %% the current program in the user ctxt
      write('consulting file '), write(File),        %% (removing all clauses possibly stored
      write(' ...'), nl,                             %% in the same ctxt)
      sys_special(abolish,_),
      read_loop(FileStream,1),
      write('file '), write(File), write(' consulted.'), nl,
      close(FileStream). 

sys_special(consult(File,mute),[]):-   %% consult using mute mode 
      !, setlog_open(File,read,FileStream), 
      sys_special(abolish,_),
      read_loop_np(FileStream),
      close(FileStream). 

sys_special(listing,[]):-              %% listing
      !,nl, list_all.
          
sys_special(abolish,[]):-              %% abolish
      !,rem_clause(usr),
      rem_clause(tmp(usr)).

sys_special(abort,[]):-                %% abort
      !,nl, write('Execution aborted'), nl,
      setlog. 

sys_special(help,[]):- !, h(setlog).   %% help
sys_special(h(X),[]):- !, h(X). 

sys_special(halt,[]):-                 %% halt
%     confirm, !, 
      abort.     
% sys_special(halt,[]). 

sys_special(time(G,T),C):-             %% time
      statistics(runtime,_),
      write('STARTING ...'),nl,
      solve_goal_fin(G,C),!,
      write('END'),nl,
      statistics(runtime,[_,T]).
sys_special(time(_G,T),_C):-           %% time
      write('END'),nl,
      statistics(runtime,[_,T]).

consult_mute(File) :-                    %% like setlog(consult(File),_)
      setlog_open(File,read,FileStream), %% but no message is sent to the std output
      sys_special(abolish,_),
      read_loop_np(FileStream),
      close(FileStream). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% auxiliary predicates for sys_special/2

setlog_read(Term) :- 
      on_exception(Msg,read(Term),syntax_error_msg(Msg)).   

setlog_open(File,Mode,Stream) :- 
      mk_file_name(File,FullName),       
      on_exception(Msg,open(FullName,Mode,Stream),existence_error_msg(Msg)).    

existence_error_msg(Text) :-
      write('Existence error:'), nl,    
      write('file '), write(Text), write(' does not exist'), nl,
      fail.

rem_clause(Ctxt):-              
      retract(isetlog(_,Ctxt)), 
      fail. 
rem_clause(_).

confirm :-
      nl, write('Are you sure you want to leave {log}? (y/n)'),
      get(C), skip(10),
      C == 121,
      nl, write('Bye, bye. See you later').

mk_file_name(F,FullName) :-             
      path(Dir),
      name(Dir,DirList),
      name(F,FList),
      append(DirList,FList,FullNameList),
      name(FullName,FullNameList).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%% Program storing and printing %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%   Consulting and storing {log} clauses  
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

context(usr).

read_loop_np(FileStream):-
       setlog_read(FileStream,Clause), 
       Clause \== end_of_file,!, 
       assert_or_solve(Clause),   
       read_loop_np(FileStream).
read_loop_np(_).

read_loop(FileStream,N):-
       setlog_read(FileStream,Clause), 
       Clause \== end_of_file,!, 
       assert_or_solve(Clause,N),
       N1 is N + 1,
       read_loop(FileStream,N1).
read_loop(_,_).

setlog_read(Stream,Term) :- 
       on_exception(Msg,read(Stream,Term),syntax_error_cont_msg(Msg)).   

assert_or_solve((:- Goal)):-!,  
       solve(Goal,_).
assert_or_solve(Clause):- 
       setassert(Clause).

assert_or_solve((:- Goal),_):-!,
       solve(Goal,_).
assert_or_solve(Clause,N):- 
       setassert(Clause),
       write('Clause '), write(N), write(' stored'), nl.

setassert(Clause):- 
       context(Ctxt),
       setassert(Clause,Ctxt).
setassert(Clause,Ctxt):- 
       transform_clause(Clause,BaseClause),
       assert(setlog:isetlog(BaseClause,Ctxt)).

switch_ctxt(NewCtxt,OldCtxt) :-
       retract(context(OldCtxt)),
       assert(context(NewCtxt)).

tmp_switch_ctxt(OldCtxt) :-
       context(OldCtxt), 
       functor(OldCtxt,tmp,_),!.
tmp_switch_ctxt(OldCtxt) :-
       retract(context(OldCtxt)),
       NewCtxt =.. [tmp,OldCtxt],
       assert(context(NewCtxt)).

syntax_error_cont_msg(Text) :-
       write('Syntax error:'), nl,      
       write(Text), nl.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%   Program listing
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

list_all :-                            
      isetlog((H :- B),usr), 
      postproc(H,Hnew), write(Hnew), 
      write_body(B).
list_all. 

write_body(true) :-
      !, write('.'),nl,nl,
      fail.
write_body(type(_) & true) :-
      !, write('.'),nl,nl,
      fail.
write_body(B) :-
      write((:-)), nl, 
      write('   '), postproc(B,Bnew), write_atoms(Bnew), write('.'),nl,nl,
      fail.

write_atoms(B & true) :-
      !, write_atom(B).
write_atoms(B1 & B2) :- 
      write_atom(B1), 
      (B2 = (type(_) & _), ! 
      ;
       write(' & '), nl, write('   ')), 
      write_atoms(B2).

write_atom(A) :-    
      var(A),!,
      write(A).
write_atom(ruq_call(Aggr,Goal_name,FV)) :- 
      !, write('forall('),write(X),write(' in '),write(Aggr),write(','), 
      RUQ_body_pred =.. [Goal_name,X|FV], isetlog((RUQ_body_pred :- RUQ_body),_),
      extract_vars(RUQ_body,Vars),
      remove_list([X|FV],Vars,LocalVars),
      postproc(RUQ_body,RUQ_bodyNew),
      (LocalVars = [],!,
       write_atoms(RUQ_bodyNew), write(')')
       ;
       write('exists('),write(LocalVars),write(','),
       write_atoms(RUQ_bodyNew), write('))') 
      ).
write_atom(type(_)) :- !.
write_atom(neg A) :- !,
      write('neg '), 
      write('('), write_atoms(A), write(')').
write_atom(naf A) :- !,
      write('naf '), 
      write('('), write_atoms(A), write(')').
write_atom(call(A)) :- !,
      write(call),
      write('('), write_atoms(A), write(')').
write_atom(call(A,C)) :- !,     
      write(call),
      write('('), write_atoms(A),write(','),write(C),write(')').
write_atom(solve(A)) :- !,
      write(solve),
      write('('), write_atoms(A), write(')').
write_atom((A)!) :- !,
      write('('),
      write_atoms(A),
      write(')!').
write_atom(delay(A,G)) :- !,
      write(delay),write('('),
      write_atoms(A),write(','),
      write_atoms(G),
      write(')').
write_atom((A1 or A2)) :- !,
      write('('), write_atoms(A1),
      write(' or '),
      write_atoms(A2), write(')').
write_atom(B) :- 
      write(B).

               
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%% The {log] Constraint Solver  %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Exported predicates:
%
%             atomic_constr/1,
%             sat/3,
%             final_sat/2,
%             sunify/3,
%             add_FDc/3,
%             get_domain/2,
%             labeling/1,
%             labeling1/2


%%%%%%%%%%%%%%%%%%% Atomic constraints %%%%%%%%%%%%%%%%%%%%%%

atomic_constr(_ nin _) :-!.
atomic_constr(_ in _) :-!. 
atomic_constr(_ neq _) :-!.  
atomic_constr(_ = _) :-!.      
atomic_constr(type(_)) :-!.
atomic_constr(set(_)) :-!.
atomic_constr(integer(_)) :-!.        
atomic_constr(delay(_,_)) :-!.
atomic_constr(un(_,_,_)) :-!.
atomic_constr(subset(_,_)) :-!.  
atomic_constr(disj(_,_)) :-!.
atomic_constr(inters(_,_,_)) :-!.   
atomic_constr(ssubset(_,_)) :-!.  

atomic_constr(size(_,_)) :-!.   
atomic_constr(sum(_,_)) :-!.  
atomic_constr(smin(_,_)) :-!.             
atomic_constr(smax(_,_)) :-!.  
        
atomic_constr(ninteger(_)) :-!.        
atomic_constr(bag(_)) :-!.
atomic_constr(list(_)) :-!.
atomic_constr(nun(_,_,_)) :-!.
atomic_constr(ndisj(_,_)) :-!.
atomic_constr(solved(_,_,_,_)) :-!.   

atomic_constr(_ is _) :-!.     
atomic_constr(_ =< _) :-!.      
atomic_constr(_ < _) :-!.       
atomic_constr(_ >= _) :-!.      
atomic_constr(_ > _) :-!. 
      
atomic_constr(pfun(_)) :-!.
atomic_constr(rel(_)) :-!.     
atomic_constr(dom(_,_)) :-!. 
atomic_constr(inv(_,_)) :-!.    
atomic_constr(ran(_,_)) :-!. 
atomic_constr(comp(_,_,_)) :-!.  
atomic_constr(dompf(_,_)).             
atomic_constr(comppf(_,_,_)) :-!. 
atomic_constr(apply(_,_,_)) :-!.  
atomic_constr(dres(_,_,_)) :-!.
atomic_constr(drespf(_,_,_)) :-!.
atomic_constr(rres(_,_,_)) :-!.  
atomic_constr(ndres(_,_,_)) :-!.
atomic_constr(nrres(_,_,_)) :-!.  

atomic_constr(npfun(_)) :-!.
atomic_constr(nrel(_)) :-!.
atomic_constr(npair(_)) :-!.


%%%%%%%%%%%%  Constraint solver main procedure %%%%%%%%%%%%   

%%%% sat(+Constraint,-Solved_Form_Constraint,+final/non-final)

sat([],[],_) :-!.
sat(C,SFC,F):- 
      trace_in(C,1),
      sat_step(C,NewC,R,F), 
      sat_cont(R,NewC,SFC,F).

sat_cont(R,NewC,SFC,F) :-           %if R=='stop', then no rule has changed the CS in the last 
      R == stop,!,                  %call to 'sat_step' (-> fixpoint); otherwise, call 'sat' again
      trace_out(NewC,1),

      norep_in_list_split(NewC,RedC,RedCS),   %remove possibly repeated constraints in the CS
                                              %and split the CS into <neq-constraints,other-constraints>
      trace_in(RedC,2),
      global_check(RedC,RedCS,RevC,F), %rewrite RedC to RevC
      (RevC == RedC,!,SFC=RevC,     %if RedC==RevC, then no rewriting has been applied:
       trace_out(NewC,2)
       ;                            %RevC is the resulting constraint; 
       sat(RevC,SFC,F)              %otherwise, call 'sat' again
      ).
sat_cont(_R,NewC,SFC,F) :-
      sat(NewC,SFC,F).

norep_in_list_split([],[],cs([],[])):-!.
norep_in_list_split([A|R],S,CS):-
        member_strong(A,R),!,
        norep_in_list_split(R,S,CS).
norep_in_list_split([A|R],[A|S],cs([A|NeqCS],OtherCS)) :-
        A = (_ neq _),!,
        norep_in_list_split(R,S,cs(NeqCS,OtherCS)).
norep_in_list_split([A|R],[A|S],cs(NeqCS,[A|OtherCS])) :-
        norep_in_list_split(R,S,cs(NeqCS,OtherCS)).

%DBG% sat_step(InC,_OutC,_Stop,_F):-   %only for debugging purposes
%DBG%        write('    >>>>> sat step: '), write(InC),nl,
%DBG%        get0(_),
%DBG%        fail. 

sat_step([],[],stop,_F) :- !.
%%%%%%%%%%%%%             % general constraints
sat_step([X neq Y|R1],R2,Z,F):- !,
          sat_neq([X neq Y|R1],R2,Z,F).
sat_step([X = Y|R1],R2,Z,F):- !,
          sat_eq([X = Y|R1],R2,Z,F).
%%%%%%%%%%%%%             % set/bag/list/interval constraints
sat_step([X nin Y|R1],R2,Z,F):- !,
          sat_nin([X nin Y|R1],R2,Z,F).
sat_step([X in Y|R1],R2,Z,F):- !,
          sat_in([X in Y|R1],R2,Z,F).
%%%%%%%%%%%%%             % set/interval constraints
sat_step([un(X,Y,W)|R1],R2,Z,F):- !,
          sat_un([un(X,Y,W)|R1],R2,Z,F).
sat_step([subset(X,Y)|R1],R2,Z,F):- !,     
          sat_sub([subset(X,Y)|R1],R2,Z,F).
sat_step([ssubset(X,Y)|R1],R2,Z,F):- !,     
          sat_ssub([ssubset(X,Y)|R1],R2,Z,F).
sat_step([inters(X,Y,W)|R1],R2,Z,F):- !,     
          sat_inters([inters(X,Y,W)|R1],R2,Z,F).
sat_step([disj(X,Y)|R1],R2,Z,F):- !,
          sat_disj([disj(X,Y)|R1],R2,Z,F).
sat_step([nun(X,Y,W)|R1],R2,Z,F):- !,
          sat_nun([nun(X,Y,W)|R1],R2,Z,F).
sat_step([ndisj(X,Y)|R1],R2,Z,F):- !,
          sat_ndisj([ndisj(X,Y)|R1],R2,Z,F).
sat_step([size(X,Y)|R1],R2,Z,F):- !,       
          sat_size([size(X,Y)|R1],R2,Z,F).
sat_step([sum(X,Y)|R1],R2,Z,F):- !,       
          sat_sum([sum(X,Y)|R1],R2,Z,F).   
sat_step([smin(X,Y)|R1],R2,Z,F):- !,         
          sat_min([smin(X,Y)|R1],R2,Z,F).  
sat_step([smax(X,Y)|R1],R2,Z,F):- !,            
          sat_max([smax(X,Y)|R1],R2,Z,F).                      
%%%%%%%%%%%%%             % type constraints
sat_step([set(X)|R1],R2,Z,F):- !,             
          sat_set([set(X)|R1],R2,Z,F).
sat_step([integer(X)|R1],R2,Z,F):-!,            
          sat_integer([integer(X)|R1],R2,Z,F).
sat_step([type(TypeC)|R1],R2,Z,F):- !,          % type(C), where C is a type constraint, 
          sat_step([TypeC|R1],R2,Z,F).          % is dealt with as C, but it is not printed
sat_step([bag(X)|R1],R2,Z,F):- !,               % when listing a program
          sat_bag([bag(X)|R1],R2,Z,F).
sat_step([list(X)|R1],R2,Z,F):- !,
          sat_list([list(X)|R1],R2,Z,F).
sat_step([ninteger(X)|R1],R2,Z,F):-!,            
          sat_ninteger([ninteger(X)|R1],R2,Z,F).
%%%%%%%%%%%%%             % control constraints
sat_step([delay(A,G)|R1],R2,Z,F):- !,
          sat_delay([delay(A,G)|R1],R2,Z,F).
sat_step([solved(C,G,Lev,Mode)|R1],R2,Z,F):- !,         % "solved" constraints: used to avoid 
          sat_solved([solved(C,G,Lev,Mode)|R1],R2,Z,F). % repeated additions of the same constraints
%%%%%%%%%%%%%             % arithmetic constraints
sat_step([X is Y|R1],R2,Z,F):-                  % ris set grouping
          nonvar(Y), is_ris(Y,Ris),!,
          check_ris(Ris),
          sat_riseq([X is Y|R1],R2,Z,F).
sat_step([X is Y|R1],R2,Z,F):- !,               % integer equality
          sat_eeq([X is Y|R1],R2,Z,F).
sat_step([C|R1],R2,Z,F):-                       % integer comparison relations
          C =.. [OP,X,Y], 
          member(OP,['=<','<','>=','>']),!,
          sat_crel([[OP,X,Y]|R1],R2,Z,F).

%%%%%%%%%%%%%             % binary relation and partial function constraints
sat_step([rel(X)|R1],R2,Z,F):- !,               
          sat_rel([rel(X)|R1],R2,Z,F).  
sat_step([pfun(X)|R1],R2,Z,F):- !,               
          sat_pfun([pfun(X)|R1],R2,Z,F).
sat_step([inv(X,Y)|R1],R2,Z,F):- !,
          sat_inv([inv(X,Y)|R1],R2,Z,F).
sat_step([dom(X,Y)|R1],R2,Z,F):- !,
          sat_dom([dom(X,Y)|R1],R2,Z,F).
sat_step([dompf(R,A)|R1],R2,Z,F):- !,
          sat_dompf([dompf(R,A)|R1],R2,Z,F).       
sat_step([comp(R,S,T)|R1],R2,Z,F):- !,
          sat_comp([comp(R,S,T)|R1],R2,Z,F).
sat_step([comppf(R,S,T)|R1],R2,Z,F):- !,
          sat_comppf([comppf(R,S,T)|R1],R2,Z,F).   
sat_step([ran(X,Y)|R1],R2,Z,F):- !,
          sat_ran([ran(X,Y)|R1],R2,Z,F).
sat_step([dres(A,R,S)|R1],R2,Z,F):- !,
          sat_dres([dres(A,R,S)|R1],R2,Z,F).
sat_step([drespf(A,R,S)|R1],R2,Z,F):- !,
          sat_drespf([drespf(A,R,S)|R1],R2,Z,F).
sat_step([rres(A,R,S)|R1],R2,Z,F):- !,
          sat_rres([rres(A,R,S)|R1],R2,Z,F).
sat_step([ndres(A,R,S)|R1],R2,Z,F):- !,
          sat_ndres([ndres(A,R,S)|R1],R2,Z,F).
sat_step([nrres(A,R,S)|R1],R2,Z,F):- !,
          sat_nrres([nrres(A,R,S)|R1],R2,Z,F).
sat_step([apply(S,X,Y)|R1],R2,Z,F):- !,
          sat_apply([apply(S,X,Y)|R1],R2,Z,F).

sat_step([npfun(X)|R1],R2,Z,F):- !,               
          sat_npfun([npfun(X)|R1],R2,Z,F).
sat_step([nrel(X)|R1],R2,Z,F):- !,               
          sat_nrel([nrel(X)|R1],R2,Z,F).
sat_step([npair(X)|R1],R2,Z,F):- !,               
          sat_npair([npair(X)|R1],R2,Z,F).

%%%%%%%%%%%%%%%%%%%% constraint solving tracing

trace_in(C,L) :-
      trace(sat),!,
      write('>>> Entering Level '), write(L),nl, 
      write('>>> Input constraint: '), write(C), nl,
      write('Press return to continue '), nl,
      get0(_). 
trace_in(_,_).

trace_out(_C,L) :-
      trace(sat),!,
      write('<<< Level '), write(L), write(' fixed point reached'),nl,
%DBG% write('<<< Output constraint: '), write(C),nl,
      nl.
trace_out(_,_).

trace_irules(Rule) :-
      trace(irules),!,
      write('\n>>> Using inference rule '), write(Rule),nl.
trace_irules(_).
   
trace_firules(Rule) :-
      trace(irules),!,
      write('\n>>> Using filtering inference rule '), write(Rule),nl.
trace_firules(_).
  
trace_ffrules(Rule) :-
      trace(irules),!,
      write('\n>>> Using filtering fail rule '), write(Rule),nl.
trace_ffrules(_).
 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%      Level 1     %%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%
%%%%%%%%%%%% Rewriting rules for general constraints %%%%%%%%%%%%%              
%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%% equality (=/2)

sat_eq([T1 = T2|R1],[T1 = T2|R2],Stop,nf):-     % delayed until final_sat is called  
        nonvar(T1), T1 = int(A,B), var(A), var(B),
        nonvar(T2), is_empty(T2),!,                        
        sat_step(R1,R2,Stop,nf).                   
sat_eq([T1 = T2|R1],[T2 = T1|R2],Stop,nf):-     % delayed until final_sat is called 
        nonvar(T2), T2 = int(A,B), var(A), var(B),
        nonvar(T1), is_empty(T1),!,                        
        sat_step(R1,R2,Stop,nf).                   
 
sat_eq([T1 = T2|R1],R2,c,F):-                   % X = t or t = X
        (var(T1),! ; var(T2)),!,
        sunify(T1,T2,C),
        append(C,R1,R3), 
        sat_step(R3,R2,_,F).  
sat_eq([T1 = T2|R1],R2,c,F):-  
        \+is_ris(T1,ris(_,_,_,_,_)),
        \+is_ris(T2,ris(_,_,_,_,_)),
        sunify(T1,T2,C),
        append(C,R1,R3), 
        sat_step(R3,R2,_,F).
                   
sat_eq([T1 = T2|R1],R2,c,F) :-                  % t = ris(...) --> ris(...) = t   (t not ris-term)
        nonvar(T1), \+is_ris(T1,ris(_,_,_,_,_)),
        nonvar(T2), is_ris(T2,ris(_,_,_,_,_)),!,
        sat_eq([T2 = T1|R1],R2,_,F).                        
sat_eq([T1 = T2|R1],R2,c,F):-                   % ris(V,{},F,P) = T --> T={}
        nonvar(T1), is_ris(T1,ris(_,Dom,_,_,_)),
        nonvar(Dom), is_empty(Dom),!,
        sunify(T2,{},C), append(C,R1,R3), 
        sat_step(R3,R2,_,F).
sat_eq([T1 = E|R1],[T1 = E|R2],Stop,F):-    
        nonvar(T1), is_ris(T1,ris(_,Dom,_,_,_)),
        var(Dom), nonvar(E), is_empty(E),!,     % ris(V,D,F,P) = {} --> irreducible   (var(D))
        sat_step(R1,R2,Stop,F).
sat_eq([T1 = E |R1],R2,c,F):-                   % ris(V,{...},F,P) = {}    
        nonvar(T1), is_ris(T1,ris(LV,Dom,Fl,P,PP)), nonvar(LV), LV=[X0|V],
        nonvar(Dom), first_rest(Dom,X,D),             
        nonvar(E), is_empty(E),!,
        chvar([X0|V],[],Vars,Fl,[],VarsNew,FlNew),
        find_corr(X0,X,Vars,VarsNew),    
        negate(FlNew,NegFl),
        mk_atomic_constraint(NegFl,NegFlD),
        sat_step([NegFlD,ris([X0|V],D,Fl,P,PP) = E|R1],R2,_,F).                     
sat_eq([T1 = S |R1],R2,c,F):-                   % ris(V,{...},F,P) = {...}   
        nonvar(T1), is_ris(T1,ris(LV,Dom,Fl,P,PP)), nonvar(LV), LV=[X0|V],
        nonvar(Dom), first_rest(Dom,X,D),     
        nonvar(S), first_rest(S,_,_),!,
        chvar([X0|V],[],FVars,[Fl,P,PP],[],FVarsNew,[FlNew,PNew,PPNew]),
        find_corr(X0,X,FVars,FVarsNew), 
        mk_atomic_constraint(PPNew,PPNewD), 
       (
        solve_expression(Z,PNew),
        mk_atomic_constraint(FlNew,FlNewD),
        sat_step([FlNewD,PPNewD,ris([X0|V],D,Fl,P,PP) with Z = S |R1],R2,_,F)                         
       ;
        negate(FlNew,NegFl),
        mk_atomic_constraint(NegFl,NegFlD),
        sat_step([NegFlD,PPNewD,ris([X0|V],D,Fl,P,PP)=S |R1],R2,_,F)   
       ).                      
sat_eq([T1 = S|R1],R2,c,F):-                    % ris(V,D,F,P) = {...}   (var(D))
        nonvar(T1), is_ris(T1,ris(LV,Dom,Fl,P,PP)), nonvar(LV), LV=[X0|V],
        var(Dom), nonvar(S), first_rest(S,X,A),!,  
        Dom = B with Y,
        chvar([X0|V],[],Vars,[Fl,P,PP],[],VarsNew,[FlNew,PNew,PPNew]),
        find_corr(X0,Y,Vars,VarsNew), 
        solve_expression(Z,PNew),
        mk_atomic_constraint(FlNew,FlNewD),
        mk_atomic_constraint(PPNew,PPNewD),
        sat_step([FlNewD,Z=X,PPNewD,ris([X0|V],B,Fl,P,PP)=A |R1],R2,_,F).  
sat_eq([T1 = S|R1],[T1 = S|R2],Stop,F):-    
        nonvar(T1), is_ris(T1,ris(_,Dom,_,_,_)), 
        var(Dom), var(S),!,                     % ris(V,D,F,P) = S --> irreducible   (var(D), var(S))
        sat_step(R1,R2,Stop,F).  
sat_eq([T1 = T2 |R1],R2,c,F):-                  % ris(V1,{...},F1,P1) =  ris(V2,{...},F2,P2)  
        nonvar(T1), is_ris(T1,ris(LV1,Dom1,Fl1,P1,PP1)), nonvar(LV1), LV1=[X01|V1],
        nonvar(Dom1), first_rest(Dom1,X,D1),         
        nonvar(T2), is_ris(T2,ris(LV2,Dom2,Fl2,P2,PP2)), nonvar(LV2), LV2=[X02|V2],
        nonvar(Dom2), first_rest(Dom2,Y,D2),!, 
        chvar([X01|V1],[],Vars1,[Fl1,P1,PP1],[],VarsNew1,[FlNew1,PNew1,PPNew1]),
        find_corr(X01,X,Vars1,VarsNew1),  
        chvar([X02|V2],[],Vars2,[Fl2,P2,PP2],[],VarsNew2,[FlNew2,PNew2,PPNew2]),
        find_corr(X02,Y,Vars2,VarsNew2),  
        solve_expression(Z1,PNew1),
        solve_expression(Z2,PNew2),
        mk_atomic_constraint(PPNew1,PPNew1D),
        mk_atomic_constraint(PPNew2,PPNew2D),
       (
        mk_atomic_constraint(FlNew1,FlNew1D),
        mk_atomic_constraint(FlNew2,FlNew2D),
        sat_step([FlNew1D,FlNew2D,PPNew1D,PPNew2D,
                  ris([X01|V1],D1,Fl1,P1,PP1) with Z1 = ris([X02|V2],D2,Fl2,P2,PP2) with Z2 |R1],R2,_,F)
       ;
        negate(FlNew1,NegFl1),
        mk_atomic_constraint(NegFl1,NegFl1D),
        sat_step([NegFl1D,FlNew2,PPNew1D,PPNew2D, 
                  ris([X01|V1],D1,Fl1,P1,PP1)=ris([X02|V2],D2,Fl2,P2,PP2) with Z2 |R1],R2,_,F)
       ;
        negate(FlNew2,NegFl2),
        mk_atomic_constraint(NegFl2,NegFl2D),
        sat_step([FlNew1,NegFl2D,PPNew1D,PPNew2D,
                  ris([X01|V1],D1,Fl1,P1,PP1) with Z1 = ris([X02|V2],D2,Fl2,P2,PP2) |R1],R2,_,F)
       ;
        negate(FlNew1,NegFl1),
        negate(FlNew2,NegFl2),
        mk_atomic_constraint(NegFl1,NegFl1D),
        mk_atomic_constraint(NegFl2,NegFl2D),
        sat_step([NegFl1D,NegFl2D,PPNew1D,PPNew2D, 
                  ris([X01|V1],D1,Fl1,P1,PP1)=ris([X02|V2],D2,Fl2,P2,PP2) |R1],R2,_,F)
       ).
sat_eq([T2 = T1 |R1],R2,c,F):-                       % ris(V2,D2,F2,P2) = ris(V1,{...},F1,P1)    (var(D2))
        nonvar(T1), is_ris(T1,ris(_,Dom1,_,_,_)),
        nonvar(Dom1), first_rest(Dom1,_X,_D1),         
        nonvar(T2), is_ris(T2,ris(_,Dom2,_,_,_)),
        var(Dom2),!,
        sat_eq([T1 = T2|R1],R2,_,F).
sat_eq([T1 = T2 |R1],R2,c,F):-                       % ris(V1,{...},F1,P1) = ris(V2,D2,F2,P2)    (var(D2))
        nonvar(T1), is_ris(T1,ris(LV1,Dom1,Fl1,P1,PP1)), nonvar(LV1), LV1=[X01|V1],
        nonvar(Dom1), first_rest(Dom1,X,D1),          
        nonvar(T2), is_ris(T2,ris(LV2,Dom2,Fl2,P2,PP2)), nonvar(LV2), LV2=[X02|V2],
        var(Dom2),!,
        chvar([X01|V1],[],Vars1,[Fl1,P1,PP1],[],VarsNew1,[FlNew1,PNew1,PPNew1]),
        find_corr(X01,X,Vars1,VarsNew1),  
        chvar([X02|V2],[],Vars2,[Fl2,P2,PP2],[],VarsNew2,[FlNew2,PNew2,PPNew2]),
        find_corr(X02,Y,Vars2,VarsNew2),  
        solve_expression(Z1,PNew1),
        solve_expression(Z2,PNew2),
        mk_atomic_constraint(PPNew1,PPNew1D),
        mk_atomic_constraint(PPNew2,PPNew2D),
       (
         Dom2 = D2 with Y,
         mk_atomic_constraint(FlNew1,FlNew1D),
         mk_atomic_constraint(FlNew2,FlNew2D),
         sat_step([FlNew1D,FlNew2D,Z1=Z2,PPNew1D,PPNew2D, 
                  ris([X01|V1],D1,Fl1,P1,PP1)=ris([X02|V2],D2,Fl2,P2,PP2) |R1],R2,_,F)
       ;
        negate(FlNew1,NegFl1),
        mk_atomic_constraint(NegFl1,NegFl1D),
        sat_step([NegFl1D,PPNew1D,PPNew2D, 
                  ris([X01|V1],D1,Fl1,P1,PP1)=ris([X02|V2],Dom2,Fl2,P2,PP2) |R1],R2,_,F)
       ).
sat_eq([T1 = T2|R1],[T1 = T2|R2],Stop,F):-           % ris(V1,D1,F1,P1) = ris(V2,D2,F2,P2)  (var(D1),var(D2)) --> irreducible
        nonvar(T1), is_ris(T1,ris(_,Dom1,_,_,_)),
        var(Dom1),
        nonvar(T2), is_ris(T2,ris(_,Dom2,_,_,_)),
        var(Dom2),!,
        sat_step(R1,R2,Stop,F).

sat_riseq([X is RIS|R1],R2,c,F) :-                   % collecting all values satisfying the RIS
        nonvar(RIS), is_ris(RIS,ris(_,Dom,_,_,_)),   % if var(Dom) return the RIS itself
        var(Dom), !, 
        X = RIS,                   
        sat_step(R1,R2,_,F).
sat_riseq([X is RIS|R1],R2,c,F):-                    % collecting all values satisfying the RIS
        final_sat([RIS = R with A],C),!,
        append(C,R1,R3),
        X = RR with A,   
        sat_step([RR is R|R3],R2,_,F).
sat_riseq([X is RIS|R1],R2,c,F):-                      
        final_sat([RIS = {}],C),
        append(C,R1,R3),
        X = {},      
        sat_step(R3,R2,_,F).

is_ris(ris(LVars,Dom,Fl,P),ris(LVars,Dom,Fl,P,a=a)).           % ris/4 --> ris/5
is_ris(ris(LVars,Dom,Fl,P,PP),ris(LVars,Dom,Fl,P,PP)).

check_ris(ris(LVars,Dom,_Fl,_P,_PP)) :-
       (nonvar(LVars), ground_elems(Dom),! 
        ;
        write('ERROR: is/2: Arguments are not sufficiently instantiated'),nl,
        fail).

ground_elems(R) :- 
   var(R),!.
ground_elems(R) :- 
   is_int(R,_,_),!.
ground_elems({}) :- !.
ground_elems(R with A) :- 
   ground(A), ground_elems(R).

first_rest(R with X,X,R) :- !.   % first_rest(S,X,R): true if S is a not-empty set or a not-empty interval         
first_rest(int(X,B),X,R) :-      % and X is its first component and R the remaining part
        integer(X), integer(B),
        X < B,!, X1 is X + 1,
        R = int(X1,B).
first_rest(int(X,X),X,{}).
                   
negate(true,true) :- !.         % exists X,Y (not p(X,Y))
negate(A=B,A neq B) :- !.
negate(A neq B,A = B) :- !.
negate(A in B,A nin B) :- !.
negate(A nin B,A in B) :- !.
negate(A >= B,A < B) :- !.
negate(A > B,A =< B) :- !.
negate(A =< B,A > B) :- !.
negate(A < B,A >= B) :- !.
negate(disj(A,B),ndisj(A,B)) :- !.
negate(ndisj(A,B),disj(A,B)) :- !.
negate((B1 & B2),(NB1 or NB2)) :- !,   
    negate(B1,NB1), 
    negate(B2,NB2).
negate((B1 or B2),(NB1 & NB2)) :- !,   
    negate(B1,NB1), 
    negate(B2,NB2).
negate(A,NegA) :-               % user-defined predicates, with user-defined negative counterparts
    nonvar(A), functor(A,F,N),  % check if the negation of A is present; otherwise use the next clause
    functor(AGen,F,N), isetlog((exists_not(AGen) :- _B),_),!,
    NegA = exists_not(A).
negate(A,NegA) :-               % user-defined predicates, without user-defined negative counterparts
    (\+ground(A),!, write('************* Unsafe use of negation for predicate '), write(A), nl ; true),
    NegA = (naf A).

solve_expression(X,E) :-
     nonvar(E),   
     test_integer_expr(E),!,
     solve_FD(X is E).
solve_expression(X,E) :-
     X = E.

test_integer_expr(E) :-       % true if E is an integer expression       
     on_exception(_Error,fd_eq(_X,E),fail).

chvar(V,L1,L1,X,L2,L2,X) :-   %chvar(LocalVars,InitialVars,FinalVars,Term,InitialNewVars,FinalNewVars,NewTerm):
    var(X), notin(X,V), !.    %same as chvar/6 but it replaces only variables which odccur in the list 'LocalVars'
chvar(_,L1,[X|L1],X,L2,[Y|L2],Y):-        %e.g. chvar([X,Y],[],f(X,g(Y,Z),Z,X),V1,[],T2,V2) --> 
    var(X), notin(X,L1), !.               % T2 = f(X',g(Y',Z),Z,X'), V1 = [Y,X], V2 = [Y',X']
chvar(_,L1,L1,X,L2,L2,Y):-
    var(X), find_corr(X,Y,L1,L2),!.
chvar(_,L1,L1,F,L2,L2,F):-
    atomic(F),!.
chvar(V,L1,L1new,F,L2,L2new,F1):-
    F =.. [Fname|Args],
    chvar_all(V,L1,L1new,Args,L2,L2new,Brgs),
    F1 =.. [Fname|Brgs].

chvar_all(_,L1,L1,[],L2,L2,[]).
chvar_all(V,L1,L1b,[A|R],L2,L2b,[B|S]):-
    chvar(V,L1,L1a,A,L2,L2a,B),
    chvar_all(V,L1a,L1b,R,L2a,L2b,S).

mk_atomic_constraint(B,delay(BB,true)) :- 
    nonvar(B), B=(_B1 & _B2), !,
    conj_append(B,true,BB).
mk_atomic_constraint(B,delay(BB,true)) :- 
    nonvar(B), B=(_B1 or _B2), !,
    conj_append(B,true,BB).
mk_atomic_constraint(B,delay(B & true,true)) :-   % user-defned atomic predicates
    nonvar(B), \+atomic_constr(B), !.
mk_atomic_constraint(B,B).                        % primitive atomic constraints


%%%%%%%%%%%  Set/Multiset Unification Algorithm  %%%%%%%%%%%%               
         
sunify(X,Y,[]) :-                   % X = X  
      var(X),var(Y),                                
      X == Y,!.
sunify(X,Y,C) :-                    % X = t  
      var(X),!,
      sunifyXt(X,Y,C).
sunify(X,Y,C) :-                    % t = Y  
      var(Y),!,
      sunify(Y,X,C).  
sunify(T1,T2,C) :-                  % intervals 
      int_term(T1),int_term(T2),!,
      intint_unify(T1,T2,C). 
sunify(T1,T2,C) :-                  % intervals
      int_term(T1), set_term(T2),!,
      int_unify(T1,T2,C). 
sunify(T1,T2,C) :-                  % intervals
      int_term(T2), set_term(T1),!,
      int_unify(T2,T1,C). 

sunify(T1,T2,[T1 = T2]) :-          % ris
      nonvar(T1), is_ris(T1,ris(_,_,_,_,_)), 
      nonvar(T2),!.
sunify(T1,T2,[T1 = T2]) :-          % ris
      nonvar(T1),
      nonvar(T2), is_ris(T2,ris(_,_,_,_,_)),!.

sunify(R,S,C) :-                    % {...} = {...}                     
      tail(R,TR),
      tail(S,TS),!,
      (samevar(TR,TS),!,
       stunify_samevar(R,S,TR,C)
       ;
       stunify_ss(R,S,C) ). 
sunify(X,Y,C) :-                    % bag unification +{...} = +{...}
      bag_tail(X,BX),
      bag_tail(Y,BY),!,
      (samevar(BX,BY),!,
       stunify_bag_same(X,Y,C)
       ;
       stunify_bag(X,Y,C) ).
sunify(X,Y,C) :-                    % f(...) = f(...) 
      X=..[F|Ax],Y=..[F|Ay],!,
      sunifylist(Ax,Ay,C).

sunifyXt(X,Y,[set(N)]) :-           % X = {...|X} 
      nonvar(Y),tail(Y,TY),samevar(X,TY),!,
      replace_tail(Y,N,NewY),
%     occur_check(X,NewY),          % temporarily suppressed for efficiency reasons - uncomment to reactivate
      X = NewY.               
sunifyXt(X,Y,[]) :-                 % X = t  
%     occur_check(X,Y),             % temporarily suppressed for efficiency reasons - uncomment to reactivate
      (is_fd_var(X),!,              % if X is a domain variable
       simple_integer_expr(Y)       % then Y must be a simple_integer_expr;
       ;                            % otherwise, it fails (without doing var. substitution)
       true),
      X = Y.             

%%%%%%%%%%% Set unification %%%%%%%%%%%%%%%%%
%%  distinct tail vars.

stunify_ss(R with X,S with Y,C) :-  % ground case: {...} = {...}
      ground(X), ground(Y),!,
      (sunify(X,Y,C1),!, 
       stunify1_2_3(R,S,X,Y,C2),
       append(C1,C2,C)
      ;
       sunify(R,N with Y,C1), 
       sunify(S,N with X,C2),
       append(C1,C2,C3),
       C = [set(N)|C3] ).       
stunify_ss(R with X,S with Y,C) :-  % {...|X} = {...|Y}                        
      sunify(X,Y,C1),
      stunify1_2_3(R,S,X,Y,C2),
      append(C1,C2,C).
stunify_ss(R with X,S with Y,C) :-  % {...|X} = {...|Y} (permutativity)
      sunify(R,N with Y,C1),
      sunify(S,N with X,C2),
      append(C1,C2,C3),
      C = [set(N)|C3].      

stunify1_2_3(R,S,_,_,C) :-          % 1
      sunify(R,S,C).
stunify1_2_3(R,S,_,Y,C) :-          % 2
      sunify(R,S with Y,C).
stunify1_2_3(R,S,X,_,C) :-          % 3 
      sunify(R with X,S,C).

%%  same tail vars.
stunify_samevar(R with X,S with Y,_TR,C):-   % {...|X} = {...|X} 
      select_var(Z,S with Y,Rest),
      sunify(X,Z,C1),
      (sunify(R,Rest,C2)            % 1
      ;
       sunify(R with X,Rest,C2)     % 2
      ;
       sunify(R,S with Y,C2)),      % 3
      append(C1,C2,C).
stunify_samevar(R with X,S with Y,TR,C):-    % 4
      replace_tail(R,N,NewR),
      replace_tail(S with Y,N,NewSS),
      sunify(TR,N with X,C1),
      sunify(NewR,NewSS,C2),
      append(C1,C2,C3),
      C = [set(N)|C3].      

sunifylist([],[],[]).
sunifylist([X|AX],[Y|AY],C):-
      sunify(X,Y,C1),
      sunifylist(AX,AY,C2),
      append(C1,C2,C).

%%%%%%%%%%% Interval unification %%%%%%%%%%%%%%%%%

intint_unify(int(L,H),T2,[int(L,H) = T2]) :-            % int(A,B) = int(a,b), a > b (delayed)
        var(L), var(H), is_empty_int(T2), !.    
intint_unify(T2,int(L,H),[int(L,H) = T2]) :-            % int(a,b) = int(A,B), a > b  (delayed)
        var(L), var(H), is_empty_int(T2), !.  
intint_unify(int(L,H),T2,[integer(H), integer(L), H < L]) :-    % int(t1,t2) = int(a,b), a > b
        is_empty_int(T2), !. 
intint_unify(T2,int(L,H),[integer(H), integer(L), H < L]) :-    % int(a,b) = int(t1,t2), a > b
        is_empty_int(T2), !. 

intint_unify(int(L1,H1),int(L2,H2),[]) :-               % int(t1,t2) = int(a,b), a =< b                      
        ground(int(L2,H2)), L2 =< H2,!,
        L1 = L2, H1 = H2.
intint_unify(int(L1,H1),int(L2,H2),[]) :-               % int(a,b) = int(t1,t2), a =< b, \+ground(int(t1,t2))            
        ground(int(L1,H1)), L1 =< H1,!,
        L1 = L2, H1 = H2.
intint_unify(T1,T2,C) :-                                % int(t1,t2) = int(s1,s2)
        T1 = int(L1,H1), T2 = int(L2,H2),
        \+ground(T1), \+ground(T2), !,
        (C = [T1 neq {}, T2 neq {}, L1 = L2, H1 = H2]
         ;
         C = [T1 = {}, T2 = {}] 
        ).

int_unify(int(L,H),S2,[int(L,H) = S2]) :-            % int(A,B) = {}
        var(L), var(H), nonvar(S2), S2 = {}, !.   
int_unify(int(L,H),T2,C) :-                          % int(t1,t2) = {}
        T2 = {}, !,
        C = [integer(H), integer(L), H < L]. 
int_unify(T1,T2,C) :-                                % int(L,H) = {...} 
        T2 = _ with _, T1 = int(A,B),          
        C = [smin(T2,A), smax(T2,B), size(T2,K), K is B-A+1].

is_empty_int(int(A,B)) :-             
        integer(A), integer(B),
        A > B.

%%%%%%%%%%% Multiset unification %%%%%%%%%%%%%%%%%

stunify_bag_same(R mwith X, S mwith Y, C) :-   % +{...|X} = +{...|X} 
        de_tail(R mwith X,ZX),
        de_tail(S mwith Y,ZY),
        sunify(ZX,ZY,C).

stunify_bag(R mwith X, S mwith Y, C) :-        % +{...|X} = +{...|Y} 
        sunify(X,Y,C1),
        sunify(R,S,C2),
        append(C1,C2,C).
stunify_bag(R mwith X, S mwith Y,C) :-
        sunify(R, N mwith Y, C1),
        sunify(S, N mwith X, C2),
        append(C1,C2,C3),
        C = [bag(N)|C3].        

%%%%%%%%%%%%%% Auxiliary predicates for unification

select_var(_,S,_):-
        var(S), !, fail.
select_var(Z, R with Z, R).
select_var(Z, R with Y, A with Y):-
        select_var(Z, R, A).


%%%%%%%%%%%%%%%%%%%%%% inequality (neq/2)

sat_neq([T1 neq T2|R1],R2,R,F):-                     % X neq t
         var(T1), nonvar(T2),!,
         sat_neq_vn([T1 neq T2|R1],R2,R,F).                         
sat_neq([T1 neq T2|R1],R2,c,F):-                     % t neq X  
         nonvar(T1), var(T2),!,
         sat_neq([T2 neq T1|R1],R2,_,F).                         
sat_neq([T1 neq T2|R1],R2,R,F):-                     % X neq Y
         var(T1), var(T2),!,
         sat_neq_vv([T1 neq T2|R1],R2,R,F).  
sat_neq([T1 neq T2|R1],[T1 neq T2|R2],Stop,nf):-     % unbounded intervals int(A,B) neq {}    
         nonvar(T1), T1 = int(A,B), var(A), var(B),  % delayed until final_sat is called (--> Level 3)
         nonvar(T2), is_empty(T2),!,                            
         sat_step(R1,R2,Stop,nf).                   
sat_neq([T1 neq T2|R1],R2,R,F):-                     % unbounded intervals int(A,B) neq t
         nonvar(T1), int_term(T1), \+ground(T1), !,
         sat_neq_ui([T1 neq T2|R1],R2,R,F).  
sat_neq([T1 neq T2|R1],R2,R,F):-                     % unbounded intervals t neq int(A,B) 
         nonvar(T2), int_term(T2), \+ground(T2), !,
         sat_neq_ui([T2 neq T1|R1],R2,R,F).  
sat_neq([T1 neq T2|R1],R2,R,F):-                     % bounded intervals int(a,b) neq t
         nonvar(T1), T1 = int(A,B),
         integer(A), integer(B),!,
         sat_neq_i([T1 neq T2|R1],R2,R,F).   
sat_neq([T1 neq T2|R1],R2,R,F):-                     % bounded intervals t neq int(a,b)
         nonvar(T2), T2 = int(A,B),
         integer(A), integer(B),!,
         sat_neq_i([T2 neq T1|R1],R2,R,F).   

sat_neq([T1 neq T2|R1],R2,c,F):-                     % ris: t neq ris(...) (t not ris-term)
         nonvar(T1), \+is_ris(T1,ris(_,_,_,_,_)),
         nonvar(T2), is_ris(T2,ris(_,_,_,_,_)),!,
         sat_neq([T2 neq T1|R1],R2,_,F).                        
sat_neq([T1 neq T2|R1],R2,R,F):-                     % ris: ris(...) neq t 
         nonvar(T1), is_ris(T1,ris(V,D,Fl,P,PP)),!,
         sat_neq_ris([ris(V,D,Fl,P,PP) neq T2|R1],R2,R,F).                      

sat_neq([T1 neq T2|R1],R2,R,F):-                     % t1 neq t2
         nonvar(T1), nonvar(T2),!,
         sat_neq_nn([T1 neq T2|R1],R2,R,F).   
                                                % unbounded intervals
sat_neq_ui([int(A,B) neq T2|R1],R2,c,F):-       % int(A,B) neq empty 
         nonvar(T2), is_empty(T2),!,
         sat_step([A =< B|R1],R2,_,F).   
sat_neq_ui([int(A,B) neq T2|R1],R2,c,F):-       % int(A,B) neq {S|R}
         nonvar(T2), T2 = _ with _, !,
         (sat_step([Z >= A, Z =< B, Z nin T2|R1],R2,_,F)
         ;  
          sat_step([Z < A, Z in T2|R1],R2,_,F)
         ;
          sat_step([Z > B, Z in T2|R1],R2,_,F)
         ).
sat_neq_ui([int(A,B) neq T2|R1],R2,c,F):-       % int(A,B) neq int(C,D)
         nonvar(T2), T2 = int(C,D), !,
         (sat_step([Z >= A, Z =< B, Z < C|R1],R2,_,F)
         ;  
          sat_step([Z >= A, Z =< B, Z > D|R1],R2,_,F)
         ; 
          sat_step([Z < A, Z >= C, Z =< D|R1],R2,_,F)
         ).
sat_neq_ui([_T1 neq _T2|R1],R2,c,F):-           % int(A,B) neq t  (t non-set term)
         sat_step(R1,R2,_,F).   
                  
sat_neq_vn([X neq T|R1],R2,c,F):-               % X neq t[X] 
         is_ker(T),
         occurs(X,T),!,
         sat_step(R1,R2,_,F).
sat_neq_vn([X neq T|R1],R2,c,F):-               % X neq {... | X} 
         T = _S with _T,
         tail(T,TS),samevar(X,TS),!,
         split(T,_,L), 
         member(Ti,L) ,
         sat_step([Ti nin X|R1],R2,_,F).
sat_neq_vn([X neq T|R1],R2,c,F):-               % X neq {...,t[X],...}
         T = _S with _T,
         occurs(X,T),!,
         sat_step(R1,R2,_,F).
sat_neq_vn([X neq T|R1],[X neq T|R2],Stop,F):-  % X neq t, t simple integer expr 
         simple_integer_expr(T),   % to catch and handle type errors within {log} 
         is_fd_var(X), !,
         solve_FD(X neq T),
         sat_step(R1,R2,Stop,F).  
sat_neq_vn([C|R1],[C|R2],Stop,F):-              % X neq t (irreducible form)
         sat_step(R1,R2,Stop,F).

sat_neq_vv([X neq Y|_],_,_,_F):-                % X neq X 
         samevar(X,Y),!,fail.
sat_neq_vv([X neq Y|R1],[X neq Y|R2],Stop,F):-  % X neq Y, X,Y domain variables  
         is_fd_var(X),
         is_fd_var(Y),!,
         solve_FD(X neq Y),
         sat_step(R1,R2,Stop,F).
sat_neq_vv([T1 neq T2|R1],R2,c,F):-             % Y neq X --> X neq Y
         T1 @> T2,!,
         sat_step([T2 neq T1|R1],R2,_,F).                         
sat_neq_vv([C|R1],[C|R2],Stop,F):-              % X neq Y (irreducible form)
         sat_step(R1,R2,Stop,F).

sat_neq_i([T1 neq T2|_R1],_R2,_,_F):-           % int(a,b) neq empty
         nonvar(T1), nonvar(T2), 
         is_empty(T1),is_empty(T2),!, fail.
sat_neq_i([T1 neq T2|R1],R2,c,F):-              % int(a,b) neq int(c,d)
         is_int(T1,A1,_B1), is_int(T2,A2,_B2), 
         A1 \== A2,!,
         sat_step(R1,R2,_,F).
sat_neq_i([T1 neq T2|R1],R2,c,F):-              % int(a,b) neq int(c,d)
         is_int(T1,_A1,B1), is_int(T2,_A2,B2), 
         B1 \== B2,!, 
         sat_step(R1,R2,_,F).
sat_neq_i([T1 neq T2|R1],R2,c,F):-              % int(a,b) neq {S|R} (special)
         set_length(T2,SetL),
         int_length(T1,IntL),
         SetL < IntL, !,
         sat_step(R1,R2,_,F).
sat_neq_i([T1 neq T2|R1],R2,c,F):-              % int(a,b) neq {S|R} 
         nonvar(T2), T2 = _ with _, !,
         (sat_step([Z in T1, Z nin T2, integer(Z) | R1],R2,_,F)     % (i)
          ;
          sat_step([Z nin T1, Z in T2| R1],R2,_,F)                  % (ii)
         ).
sat_neq_i([_T1 neq _T2|R1],R2,c,F):-            % int(a,b) neq t (t non-set term)
         sat_step(R1,R2,_,F).   

sat_neq_nn([F neq G|R1],R2,c,Fin):-             % ground case: t1 neq t2
         ground(F),ground(G),!,
         g_neq(F,G),
         sat_step(R1,R2,_,Fin).
sat_neq_nn([F neq G|R1],R2,c,Fin):-             % t1 neq t2 
         functor(F,Fname,Far),functor(G,Gname,Gar),
         (Fname \== Gname ; Far \== Gar),!,
         sat_step(R1,R2,_,Fin).
sat_neq_nn([F neq G|R1],R2,c,Fin):-             % t1 neq t2 
         functor(F,Fname,Far),functor(G,Gname,Gar),
         Fname == Gname, Far == Gar, 
         Fname \== with, Fname \== mwith,
         F =.. [_|Flist], G =.. [_|Glist],!,
         memberall(A,B,Flist,Glist),
         sat_step([A neq B|R1],R2,_,Fin).
sat_neq_nn([T1 neq T2|R1],R2,c,F):-             % inequality between sets
         T1 = _S with _A, T2 = _R with _B,      % {A|S} neq {B|R} (i)
         sat_step([Z in T1, Z nin T2 | R1],R2,_,F).
sat_neq_nn([T1 neq T2|R1],R2,c,F):-             % inequality between sets
         T1 = _S with _A, T2 = _R with _B,!,    % {A|S} neq {B|R} (ii)
         sat_step([Z in T2, Z nin T1 | R1],R2,_,F).

%%%%%%%%%%%% multisets 
sat_neq_nn([T1 neq T2|R1],R2,c,F):-             % inequality between multisets
         nonvar(T1),nonvar(T2),                 % with the same tail variables
         bag_tail(T1,TT1), bag_tail(T2,TT2), 
         samevar(TT1,TT2),!,
         de_tail(T1,DT1), de_tail(T2,DT2),
         sat_step([DT1 neq DT2|R1],R2,_,F).
sat_neq_nn([T1 neq T2|R1],R2,c,F):-             % inequality between multisets
         T1 = _S mwith A, T2 = R mwith B,       % with distinct tail variables
         sat_step([A neq B, A nin R| R1],R2,_,F).
sat_neq_nn([T1 neq T2|R1],R2,c,F):-      
         T1 = _S mwith A, T2 = R mwith B,!,
         sunify(R mwith B, _N mwith A,C),
         append(C,R1,R3),
         sat_step([Z in T2, Z nin T1 | R3],R2,_,F).

sat_neq_ris([T1 neq T2|_R1],_R2,c,_F):-          % ris(...) neq {}
        nonvar(T1), is_ris(T1,ris(_,D,_,_,_)),
        nonvar(D), is_empty(D),
        nonvar(T2), is_empty(T2),!,fail.
sat_neq_ris([T1 neq T2|R1],R2,c,F):-             % ris(...) neq t
        nonvar(T1), is_ris(T1,ris(LV,D,Fl,P,PP)), nonvar(LV), LV=[X0|V],!,
       (sat_step([Z in ris([X0|V],D,Fl,P,PP),Z nin T2|R1],R2,_,F)                         
       ;
        sat_step([Z nin ris([X0|V],D,Fl,P,PP),Z in T2|R1],R2,_,F)   
       ).                      


%%%%%%%%%%%%
%%%%%%%%%%%% Rewriting rules for arithmetic constraints %%%%%%%%%%%% 
%%%%%%%%%%%%            

sat_eeq([X is E|R1],R2,c,F):-        % integer equality (is/2)            
        ground(E),!,
        simple_arithm_expr(X),       % to catch type errors within {log} 
        arithm_expr(E),           
        X is E,
        sat_step(R1,R2,_,F).
sat_eeq([X is E|R1],R2,c,F):-        % integer equality             
        simple_integer_expr(X),      % to catch type errors within {log} 
        integer_expr(E),           
        solve_FD(X is E),
        allintvars(X is E,Intc),
        append(Intc,R1,Newc),
        sat_step(Newc,R2,_,F).

sat_crel([[OP,E1,E2]|R1],R2,c,F):-   % integer comparison relations (=<,<,>=,>)                 
        ground(E1), ground(E2),!,
        arithm_expr(E1),             % to catch type errors within {log} 
        arithm_expr(E2), 
        Rel =.. [OP,E1,E2],
        call(Rel),          
        sat_step(R1,R2,_,F).
sat_crel([[OP,E1,E2]|R1],R2,c,F):-                   
        integer_expr(E1),            % to catch type errors within {log} 
        integer_expr(E2),
        Rel =.. [OP,E1,E2],
        solve_FD(Rel),
        allintvars(Rel,Intc),
        append(Intc,R1,Newc),
        sat_step(Newc,R2,_,F).

allintvars(E,Evars) :-     % true if E is an arithmetic expression and Evars
    E =.. [_F|Args],       % is a list containing a contraint integer(X) for 
    addint(Args,Evars).    % each variable X in E
    
addint([],[]):-!.
addint([X|R],[integer(X)|Rvars]) :-
    var(X),!,
    addint(R,Rvars).
addint([E|R],Allvars) :-
    allintvars(E,Evars),
    addint(R,Rvars),
    append(Evars,Rvars,Allvars).


%%%%%%%%%%%%
%%%%%%%%%%%% Rewriting rules for set/bag/list/interval constraints %%%%%%%%%%%%
%%%%%%%%%%%%              

%%%%%%%%%%%%%%%%%%%%%% membership (in/2)

sat_in([T in I|R1],R2,R,F):-                         
         var(I),!,
         sat_in_v([T in I|R1],R2,R,F).   
sat_in([T in I|R1],R2,R,F):-                 % bounded interval: t in int(a,b)                         
         nonvar(I), is_int(I,L,H),!,
         sat_in_i([T in int(L,H)|R1],R2,R,F).                      
sat_in([T in I|R1],R2,R,F):-                 % unbounded interval: t in int(A,B)         
         nonvar(I), int_term(I),!,
         sat_in_ui([T in I|R1],R2,R,F). 

sat_in([T in I|R1],R2,R,F):-                 % ris                              
         nonvar(I), is_ris(I,ris(V,D,Fl,P,PP)),!,
         sat_in_ris([T in ris(V,D,Fl,P,PP)|R1],R2,R,F).                      

sat_in([T in I|R1],R2,R,F):-                 % extensional set/multiset/list;  t in {...}                  
         nonvar(I),!,
         sat_in_s([T in I|R1],R2,R,F).                         

sat_in_v([T in X|R1],R2,c,F):-               % t in X, set 
         sunify(X,N with T,_),
         sat_step([set(N)|R1],R2,_,F).
sat_in_v([T in X|R1],R2,c,F):-               % t in X, multiset
         sunify(X,N mwith T,_),
         sat_step([bag(N)|R1],R2,_,F).
sat_in_v([T in X|R1],                        
         [solved(T in X,(var(X),occur_check(X,T)),3,f),list(X)|R2],Stop,F):-  
         occur_check(X,T),                   % t in X, list (irreducible form)
         sat_step(R1,R2,Stop,F).  
           
sat_in_i([T in int(A,B)|R1],R2,c,F):-        % bounded interval: t in int(a,b)
         simple_integer_expr(T),!,            
         solve_FD(T in int(A,B)),
         sat_step([integer(T)|R1],R2,_,F).  
 
sat_in_ui([T in I|R1],R2,c,F):-              % unbounded interval: t in int(A,B)
         simple_integer_expr(T),!,           % either A or B vars  
         I=int(A,B),
         solve_FD(T >= A),solve_FD(T =< B),
         sat_step([integer(T)|R1],R2,_,F).  

sat_in_s([T in Aggr|R1],R2,c,F):-            % ground set/multiset/list: t in {...} 
         ground(T), ground(Aggr),!,
         g_member(T,Aggr), 
         sat_step(R1,R2,_,F).
sat_in_s([T in Aggr|R1],R2,c,F):-            % non-ground set/multiset/list (case i): t in {...} 
         aggr_comps(Aggr,A,_R),
         sunify(A,T,C), 
         append(C,R1,R3), 
         sat_step(R3,R2,_,F).
sat_in_s([T in Aggr|R1],R2,c,F):-            % non-ground set/multiset/list (case ii): t in {...}
         aggr_comps(Aggr,_A,R),!,
         sat_step([T in R|R1],R2,_,F).

sat_in_ris([X in ris([X0|V],D,Fl,P,PP)|R1],R2,c,F):-    % ris: X in ris{v,D,...)    (var(D))
         var(D),!,  
         chvar([X0|V],[],Vars,[Fl,P,PP],[],VarsNew,[FlNew,PNew,PPNew]),
         find_corr(X0,Y,Vars,VarsNew), 
         solve_expression(Z,PNew),
         X = Z,                                                   
         mk_atomic_constraint(PPNew,PPNewD),
        (
         FlNew = (D1 or D2),
         D2 = (apply(this,XX,FF) & A),!,                            
         chvar([],_Vars,ris([X0|V],D,Fl,P,PP),[],_VarsNew,RisNew),
         FlNew1 = (D1 or (delay([XX,FF] in RisNew,a=b) & A)),
         mk_atomic_constraint(FlNew1,FlNewD)
         ;
         mk_atomic_constraint(FlNew,FlNewD)
        ),
         sat_step([Y in D,set(D),FlNewD,PPNewD |R1],R2,_,F).   

sat_in_ris([X in ris([X0|V],Dom,Fl,P,PP)|R1],R2,c,F):-  % ris: X in ris{v,{...},...)   
         nonvar(Dom), first_rest(Dom,Y,D),!,  
         chvar([X0|V],[],Vars,[Fl,P,PP],[],VarsNew,[FlNew,PNew,PPNew]),
         find_corr(X0,Y,Vars,VarsNew), 
         solve_expression(Z,PNew),
         mk_atomic_constraint(FlNew,FlNewD),
         mk_atomic_constraint(PPNew,PPNewD),
        (sat_step([FlNewD,PPNewD,X in ris([X0|V],D,Fl,P,PP) with Z |R1],R2,_,F)
         ;
         negate(FlNew,NegFl),
         mk_atomic_constraint(NegFl,NegFlD),
         sat_step([NegFlD,X in ris([X0|V],D,Fl,P,PP) |R1],R2,_,F) 
         ).

%%%%%%%%%%%%%%%%%%%%%% non-membership (nin/2)

sat_nin([T nin A|R1],R2,c,F):-              % ground set/multiset/list/interval: 
        ground(T), ground(A),!,             % t nin {A|R} or t nin +{A|R} or t nin [A|R] or t nin int(a,b)
        \+g_member(T,A), 
        sat_step(R1,R2,_,F).
sat_nin([T nin A|R1],R2,c,F):-              % t nin X, t[X] 
        var(A), occurs(A,T),!,                          
        sat_step(R1,R2,_,F).
sat_nin([T nin A|R1],[T nin A|R2],Stop,F):- % t nin X, irreducible form
        var(A),!, 
        sat_step(R1,R2,Stop,F).
sat_nin([_T nin A|R1],R2,c,F):-             % empty set/multiset/list/bounded interval:  
        nonvar(A), empty_aggr(A),!,         % t nin {}  or  t nin []  or  t nin int(a,b) with a>b
        sat_step(R1,R2,_,F).
sat_nin([R nin I|R1],R2,c,F) :-             % unbouded interval: t nin int(A,B)
        nonvar(I), int_term(I),             %   (case i)
        simple_integer_expr(R),                          
        I=int(S,_T),
        solve_FD(R + 1 =< S),
        sat_step([integer(R),integer(S)|R1], R2, _, F).

sat_nin([X nin I|R1],[X nin I|R2],Stop,F):- % ris: X nin ris{v,D,...) (var(D)): irreducible
        nonvar(I), is_ris(I,ris(_,Dom,_,_,_)),
        var(Dom), !, 
        sat_step(R1,R2,Stop,F).
sat_nin([_X nin I|R1],R2,c,F):-             % ris: X nin ris{v,{},...) -> true
        nonvar(I), is_ris(I,ris(_,Dom,_,_,_)),
        nonvar(Dom), is_empty(Dom), !, 
        sat_step(R1,R2,_,F).
sat_nin([X nin I|R1],R2,c,F):-              % ris: X nin ris{v,{...},...)   
        nonvar(I), is_ris(I,ris(LV,Dom,Fl,P,PP)), nonvar(LV), LV=[X0|V],
        nonvar(Dom), first_rest(Dom,Y,D),!,  
        chvar([X0|V],[],Vars,[Fl,P,PP],[],VarsNew,[FlNew,PNew,PPNew]),
        find_corr(X0,Y,Vars,VarsNew), 
        solve_expression(Z,PNew),
        mk_atomic_constraint(FlNew,FlNewD),
        mk_atomic_constraint(PPNew,PPNewD),
       (sat_step([FlNewD,PPNewD,X neq Z,X nin ris([X0|V],D,Fl,P,PP) |R1],R2,_,F)
        ;
        negate(FlNew,NegFl),
        mk_atomic_constraint(NegFl,NegFlD),
        sat_step([NegFlD,X nin ris([X0|V],D,Fl,P,PP) |R1],R2,_,F) 
        ).

sat_nin([R nin I|R1],R2,c,F) :-             %   (case ii)
        nonvar(I), int_term(I),
        simple_integer_expr(R), 
        I=int(_S,T),                         
        solve_FD(T + 1 =< R),
        sat_step([integer(R),integer(T)|R1], R2, _, F).
sat_nin([R nin I|R1], R2, c, F) :-          %   (case iii)
        nonvar(I), int_term(I),!,       
        sat_step([ninteger(R)|R1], R2, _, F).
sat_nin([T1 nin A|R1],R2,c,F):-             % non-ground set/multiset/list:   
        nonvar(A), aggr_comps(A,T2,S),!,    % t nin {...} or t nin +{...} or t nin [...]
        sat_step([T1 neq T2,T1 nin S|R1],R2,_,F).
sat_nin([_T nin A|R1],R2,c,F):-             % t nin a, a not a set neither an interval 
        nonvar(A),                           
        sat_step(R1,R2,_,F).


%%%%%%%%%%%%
%%%%%%%%%%%% Rewriting rules for set/interval constraints %%%%%%%%%%%%
%%%%%%%%%%%%              

%%%%%%%%%%%%%%%%%%%%%% subset (subset/2)  

sat_sub([subset(S1,S2)|R1],R2,c,F):-                 % ground case: subset({X|R},S2)            
         ground(S1), ground(S2),
         set_term(S1), set_term(S2),!,
         g_subset(S1,S2),
         sat_step(R1,R2,_,F).
sat_sub([subset(S1,I2)|R1],R2,c,F):-                 % subset(X,int(L,H))    
         var(S1), nonvar(I2), is_int(I2,_,_),!,      
         (S1 = {},
          sat_step(R1,R2,_,F) 
         ;
          S1 = _R with X,
          sat_step([X in I2,subset(S1,setlog_term(I2))|R1],R2,_,F)
         ). 
sat_sub([subset(S,I)|R1],R2,c,F):-                   % subset({A/X},setlog_term(int(L,H)))    
         nonvar(I), I = setlog_term(I2),!,           % for internal use only
         S = S1 with Z,
         (S1 = {},
          sat_step([Z in I2|R1],R2,_,F) 
         ;
          S1 = _R with X,
          sat_step([Z in I2,X in I2,X > Z,subset(S1,I)|R1],R2,_,F)
         ).
sat_sub([subset(S1,S2)|R1],R2,c,F):-                 % subset(X,S2)                   
         var(S1),!,
         sat_step([un(S1,S2,S2)|R1],R2,_,F). 
sat_sub([subset({},_S2)|R1],R2,c,F):- !,             % subset({},S2)                  
         sat_step(R1,R2,_,F). 
sat_sub([subset(R with X,I2)|R1],R2,c,F):-           % subset({X|R},int(L,H))                 
         nonvar(I2), is_int(I2,_,_),!,
         sat_step([X in I2,subset(R,I2)|R1],R2,_,F).
sat_sub([subset(R with X,S2)|R1],R2,c,F):- !,        % subset({X|R},S2)  
         sunify(S2,N with X,_),
         sat_step([set(N),subset(R,S2)|R1],R2,_,F).
sat_sub([subset(I,_)|R1],R2,c,F):-                   % subset(int(L,H),S2), with L>H   %EInt
         is_int(I,L,H),L>H,!,             
         sat_step(R1,R2,_,F). 
sat_sub([subset(I,I2)|R1],R2,c,F):-                  % subset(int(L,H),int(L2,H2))
         is_int(I,L,H), nonvar(I2), is_int(I2,L2,H2),!,
         L2 =< L, H2 >= H,
         sat_step(R1,R2,_,F). 
sat_sub([subset(I,S2)|R1],R2,c,F):-                  % subset(int(L,L),S2), S2 not interval   
         is_int(I,L,H), L==H, !,
         sat_step([L in S2|R1],R2,_,F).
sat_sub([subset(I,S2)|R1],R2,c,F):-                  % subset(int(L,H),S2), S2 not interval
         is_int(I,L,H),
         L1 is L+1,
         sat_step([L in S2,subset(int(L1,H),S2)|R1],R2,_,F).


%%%%%%%%%%%%%%%%%%%%%% strict subset (ssubset/2)  

sat_ssub([ssubset(S1,S2)|R1],R2,c,F):-                           
          sat_step([subset(S1,S2),S1 neq S2|R1],R2,_,F).


%%%%%%%%%%%%%%%%%%%%%% intersection (inters/3)          


sat_inters([inters(S1,S2,S3)|R1],R2,c,F):-              % inters(S,S,S)      
         S1 == S2,!,
         sunify(S1,S3,C),
         append(C,R1,R3), 
         sat_step(R3,R2,_,F).

sat_inters([inters(S1,S2,S3)|R1],R2,c,F):-              % ground set: inters({...},{...},t)          
         ground(S1), ground(S2), 
         set_term(S1), set_term(S2),!,
         g_inters(S1,S2,S1_2),
         sunify(S1_2,S3,C),
         append(C,R1,R3), 
         sat_step(R3,R2,_,F).

sat_inters([inters(I1,I2,S3)|R1],R2,c,F):-              % ground interval: inters(int(a,b),int(c,d),t),  
         nonvar(I1), is_int(I1,L1,H1),                  % a,b,c,d constants
         nonvar(I2), is_int(I2,L2,H2),!,
         g_greater(L1,L2,L3), g_smaller(H1,H2,H3),
         (L3 > H3,!,
          sunify({},S3,C), 
          append(C,R1,R3)
          ; 
          sunify(int(L3,H3),S3,C),
          append(C,R1,R3)
         ), 
         sat_step(R3,R2,_,F).

sat_inters([inters(I1,I2,S3)|R1],R2,c,F):-              % non-ground interval - empty-interval case:
         nonvar(I1), int_term(I1),                      % inters(int(L1,H1),int(L2,H2),t)
         nonvar(I2), int_term(I2),                      % either L1 or H1 or L2 or H2 var 
         (sunify({},I1,C1) 
          ;
          sunify({},I2,C1)
         ),
         sunify({},S3,C2), 
         append(C1,C2,C12), append(C12,R1,R3),
         sat_step(R3,R2,_,F).
sat_inters([inters(I1,I2,S3)|R1],R2,c,F):-              % non-ground interval - not empty-interval case:
         nonvar(I1), int_term(I1),                      % inters(int(L1,H1),int(L2,H2),t)
         nonvar(I2), int_term(I2), !,                   % either L1 or H1 or L2 or H2 var
         I1=int(L1,H1), I2=int(L2,H2),
         fd_max(L1,L2,L3), fd_min(H1,H2,H3),
         (solve_FD(L3 > H3),
          sunify({},S3,C), 
          append(C,R1,R3)
          ; 
          solve_FD(L3 =< H3),
          sunify(int(L3,H3),S3,C),
          append(C,R1,R3)
         ), 
         sat_step([I1 neq {},I2 neq {}|R3],R2,_,F).

sat_inters([inters(_S1,S2,S3)|R1],R2,c,F):-             % ground empty-set/empty-interval:
         nonvar(S2), is_empty(S2),!,                    % (case i) inters(t1,empty,t2) or
         sunify(S3,{},C),
         append(C,R1,R3),
         sat_step(R3,R2,_,F).
sat_inters([inters(S1,_S2,S3)|R1],R2,c,F):-             % (case ii) inters(empty,t1,t2)
         nonvar(S1), is_empty(S1),!,
         sunify(S3,{},C),
         append(C,R1,R3),
         sat_step(R3,R2,_,F).

sat_inters([inters(S1,S2,S3)|R1],R2,c,F):-              % set/interval - set - variable (A,B either constants or vars)
         nonvar(S1),                                    % inters({...},{...},S3) or inters(int(A,B),{...},S3), S3 var                   
         nonvar(S2), S2 = RS2 with X,
         var(S3),!,
         (S3 = RS3 with X,
          sat_step([set(RS2),X in S1,inters(S1,RS2,RS3)|R1],R2,_,F)
          ;
          sat_step([set(RS2),X nin S1,inters(S1,RS2,S3)|R1],R2,_,F)
         ).
sat_inters([inters(S1,S2,S3)|R1],R2,c,F):-              % set/interval - set - set/interval (A,B,C,D either constants or vars)
         nonvar(S1),                                    % inters({...},{...},{...}) or inters({...},{...},int(A,B)) or                            
         nonvar(S2), S2 = _RS2 with _X,                 % inters(int(A,B),{...},{...}) or inters(int(A,B),{...},int(C,D))
         nonvar(S3),!,      
         sat_step([inters(S1,S2,SRes),SRes=S3|R1],R2,_,F).

sat_inters([inters(S1,S2,S3)|R1],R2,c,F):-              % set - set/interval - set/interval (A,B,C,D either constants or vars)
         nonvar(S2),                                    % inters({...},int(A,B)),{...}) or inters({...},int(A,B)),int(C,D))                           
         nonvar(S1), S1 = _RS1 with _X,!,               % inters({...},int(A,B),S3) 
         sat_step([inters(S2,S1,S3)|R1],R2,_,F).

sat_inters([inters(S1,S2,S3)|R1],[inters(S1,S2,S3)|R2],Stop,nf):-  % general cases: inters(S1,.,.) or inters(.,S2,.), S1,S2 vars   
         var(S1),!,                                     % delayed until final_sat is called 
         sat_step(R1,R2,Stop,nf).                   
sat_inters([inters(S1,S2,S3)|R1],[inters(S1,S2,S3)|R2],Stop,nf):-               
         var(S2),!,                                     % delayed until final_sat is called 
         sat_step(R1,R2,Stop,nf).                   
sat_inters([inters(S1,S2,S3)|R1],R2,c,f):-              % LEVEL 3: inters(t1,t2,t3)
         (var(S1),! ; var(S2)),
         sat_step([un(D,S3,S1),un(E,S3,S2),disj(D,E)|R1],R2,_,f). 


%%%%%%%%%%%%%%%%%%%%%% union (un/3)

sat_un([un(S1,S2,T)|R1],R2,c,F):-                    % un(s,s,t) 
         S1==S2,!,                                   % includes un({},{},t)
         sunify(S1,T,C), 
         append(C,R1,R3), 
         sat_step(R3,R2,_,F). 
sat_un([un(X,Y,Z)|R1],R2,c,F):-                      % un(Y,X,Z) --> un(X,Y,Z)
         var(X),var(Y),var(Z),
         X @> Y,!,
         sat_step([un(Y,X,Z)|R1],R2,_,F).                         
sat_un([un(X,Y,Z)|R1],[un(X,Y,Z)|R2],Stop,F):-       % un(X,Y,Z) (irreducible form)
         var(X),var(Y),var(Z),!,                     
         sat_step(R1,R2,Stop,F).
sat_un([un(T1,T2,S)|R1],R2,c,F):-                    % un({},s,t) 
         nonvar(T1), is_empty(T1),!, 
         sunify(S,T2,C), 
         append(C,R1,R3), 
         sat_step(R3,R2,_,F).         
sat_un([un(T1,T2,S)|R1],R2,c,F):-                    % un(t,{},s) 
         nonvar(T2), is_empty(T2),!,
         sunify(S,T1,C), 
         append(C,R1,R3),  
         sat_step(R3,R2,_,F).         
sat_un([un(T1,T2,T3)|R1],R2,c,F):-                   % un(s,t,{}) 
         nonvar(T3), is_empty(T3),!, 
         unify_empty(T1), unify_empty(T2), 
         sat_step(R1,R2,_,F).

sat_un([un(I1,I2,S)|R1], R2, c, F) :-                % un(int(...),int(...),s) 
         nonvar(I1), nonvar(I2),
         is_int(I1,A1,B1), is_int(I2,A2,B2), 
         B1 >= A2,!,
         A3 is min(A1,A2),
         B3 is max(B1,B2),
         sunify(int(A3,B3),S,C),
         append(C,R1,R3),  
         sat_step(R3,R2,_,F).  
sat_un([un(I1,I2,S)|R1], R2, c, F) :-                % un(int(...),int(...),s) 
         nonvar(I1), nonvar(I2),
         is_int(I1,_A1,B1), is_int(I2,A2,_B2), 
         B1 < A2,!,
         int_to_set(I2,S2),
         int_to_set(I1,S1,S2),
         sunify(S1,S,C),
         append(C,R1,R3),  
         sat_step(R3,R2,_,F).  

sat_un([un(S1,S2,I)|R1], R2, c, F) :-                % un(s1,s2,int(L,L)) 
         nonvar(I), is_int(I,T1,T2), T1==T2, !,
         sat_step([un(S1,S2,{} with T1)|R1],R2,_,F).               
sat_un([un(S1,S2,I)|R1], R2, c, F) :-                % un(s1,s2,int(...)) 
         nonvar(I), is_int(I,T1,T2), 
         sunify(N1 with T1,S1,C1), append(C1,R1,C2),
         T3 is T1 + 1,
         sat_step([T1 nin N1,set(N1),un(N1,S2,int(T3,T2)) | C2],R2,_,F).               
sat_un([un(S1,S2,I)|R1], R2, c, F) :-                % un(s1,s2,int(...)) 
         nonvar(I), is_int(I,T1,T2), 
         sunify(N1 with T1,S2,C1), append(C1,R1,C2),
         T3 is T1 + 1,
         sat_step([T1 nin N1,set(N1),un(S1,N1,int(T3,T2)) | C2],R2,_,F).
sat_un([un(S1,S2,I)|R1], R2, c, F) :-                % un(s1,s2,int(...)) 
         nonvar(I), is_int(I,T1,T2), !,
         sunify(N1 with T1,S1,C1),
         sunify(N2 with T1,S2,C2),
         append(C1,R1,C3), append(C2,C3,C4),
         T3 is T1 + 1,
         sat_step([T1 nin N1,T1 nin N2,set(N1),set(N2),un(N1,N2,int(T3,T2)) | C4],R2,_,F).

sat_un([un(S1,S2,S3)|R1],R2,c,F):-                   % un({.../R},s2,{.../R}) or un(s1,{.../R},{.../R}) (special cases) 
         nonvar(S3), S3=_ with T1,
         tail(S1,TS1), tail(S2,TS2), tail(S3,TS3),
         samevar(TS3,TS1,TS2),!, 
         sunify(N with T1,S3,C1),
         ( sunify(N1 with T1,S1,C2),                               % (i)
           append(C1,C2,C3), 
           R = [T1 nin N,T1 nin N1,T1 nin S2,set(N1),set(N),un(N1,S2,N)|C3]
         ;
           sunify(N1 with T1,S2,C2),                               % (ii)
           append(C1,C2,C3), 
           R = [T1 nin N,T1 nin N1,T1 nin S1,set(N1),set(N),un(S1,N1,N)|C3]
         ;
           sunify(N1 with T1,S1,C21), sunify(N2 with T1,S2,C22),   % (iii)
           append(C21,C22,C2), append(C1,C2,C3), 
           R = [T1 nin N,T1 nin N1,T1 nin N2,set(N1),set(N2),set(N),un(N1,N2,N)|C3] 
         ),                
         append(R,R1,R3),
         sat_step(R3,R2,_,F).

sat_un([un(S1,S2,S3)|R1],R2,c,F):-                   % un(s1,s2,{...})  
         nonvar(S3), S3=N with T1,!, 
         ( sunify(N1 with T1,S1,C2),                               % (i)
           R = [T1 nin S2,set(N1),set(N),un(S2,N1,N)|C2]
         ;
           sunify(N1 with T1,S2,C2),                               % (ii)
           R = [T1 nin S1,set(N1),set(N),un(S1,N1,N)|C2]
         ;
           sunify(N1 with T1,S1,C21), sunify(N2 with T1,S2,C22),   % (iii)
           append(C21,C22,C2), 
           R = [set(N1),set(N2),set(N),un(N1,N2,N)|C2] 
         ),                
         append(R,R1,R3),
         sat_step(R3,R2,_,F).

sat_un([un(I,S,X)|R1], R2, c, F) :-                  % un(int(L,L),s,X) 
         var(X), 
         nonvar(I), is_int(I,T1,T2), T1==T2, !, 
         sat_step([un({} with T1,S,X)|R1],R2,_,F).               
sat_un([un(I,S,X)|R1], R2, c, F) :-                  % un(int(...),s,X) (i)
         var(X), 
         nonvar(I), is_int(I, T1, T2),  
         T3 is T1 + 1,
         sunify(N with T1, X, C1),
         append(C1, R1, C2),
         sat_step([T1 nin N,T1 nin S,set(N),un(int(T3,T2),S,N) | C2], R2, _, F).
sat_un([un(I,S,X)|R1], R2, c, F) :-                  % un(int(...),s,X) (ii)
         var(X), 
         nonvar(I), is_int(I, T1, T2),!,
         T3 is T1 + 1,
         sunify(N with T1, X, C1),
         sunify(N1 with T1, S, C2),
         append(C1, R1, C3),
         append(C2, C3, C4),
         sat_step([T1 nin N,T1 nin N1,set(N),set(N1),un(int(T3,T2),N1,N) | C4], R2, _, F).
sat_un([un(S,I,X)|R1],R2,c,F):-                      % un(s,int(...),X)           
         var(X),
         nonvar(I), is_int(I, _T1, _T2),!,
         sat_step([un(I,S,X)|R1],R2,_,F).   

sat_un([un(S,T,X)|R1],R2,R,F):-                      % un({...},s2,X) (bounded sets) 
         var(X),
         occur_check(X,S), occur_check(X,T),
         bounded(S),!,
         sat_un_s([un(S,T,X)|R1],R2,R,F).
sat_un([un(S,T,X)|R1],R2,R,F):-                      % un(s1,{...},X) (bounded sets) 
         var(X),
         occur_check(X,S), occur_check(X,T),
         bounded(T),!,
         sat_un_t([un(S,T,X)|R1],R2,R,F).

sat_un([un(S,T,X)|R1],R2,c,F):-                      % un({...|X},t,X)    
         nonvar(S), var(X),
         tail(S,TS),samevar(TS,X),!,
         replace_tail(S,N,NewS),
        (samevar(TS,T),!,sat_step([X=NewS,set(N)|R1],R2,_,F)  % un({...|X},X,X)
         ;
         sat_step([X=NewS,un(T,N,N),set(N)|R1],R2,_,F)).   
sat_un([un(S,T,X)|R1],R2,c,F):-                      % un(s,{...|X},X)    
         nonvar(T), var(X),
         tail(T,TT),samevar(TT,X),!,
         replace_tail(T,N,NewT),
        (samevar(TT,S),!,sat_step([X=NewT,set(N)|R1],R2,_,F)  % un(X,{...|X},X) 
         ;
         sat_step([X=NewT,un(S,N,N),set(N)|R1],R2,_,F)).   

sat_un([un(S,T,X)|R1],[un(S,T,X)|R2],Stop,nf):-      %  
         var(X),!,                                   % delayed until final_sat is called
         sat_step(R1,R2,Stop,nf).                    % (--> Level 3)
sat_un([un(S,T,X)|R1],R2,c,f):-                      % un({.../R},s,X) 
         var(X), nonvar(S), 
         S = N1 with T1,
         occur_check(X,S), novar_occur_check(X,T),!,     
         X = N with T1,
         sat_step([set(N),set(N1),un(N1,T,N)|R1],R2,_,f).
sat_un([un(T,S,X)|R1],R2,c,f):-                      % un(t,{.../S},X)            
         var(X), nonvar(S), 
         S=_T2 with _T1, !,
         sat_step([un(S,T,X)|R1],R2,_,f).  

sat_un_s([un(S,T,X)|R1],R2,c,F):-                    % un({...},s2,X) (bounded set case)
         g_union(S,T,X),
         sat_step(R1,R2,_,F).
sat_un_t([un(S,T,X)|R1],R2,c,F):-                    % un(s1,{...},X) (bounded set case)
         g_union(T,S,X),
         sat_step(R1,R2,_,F).

unify_empty(S) :-
        var(S), !, S = {}.
unify_empty({}) :- !.
unify_empty(S) :- !,   
        is_int(S,L,H),
        L > H.

samevar(X,Y,_Z) :-
       samevar(X,Y),!.
samevar(X,_Y,Z) :-
       samevar(X,Z).

novar_occur_check(_X,T) :-
      var(T),!.
novar_occur_check(X,T) :-
      occur_check(X,T).

%%%%%%%%%%%%%%%%%%%%%% disjointness (disj/2)

sat_disj([disj(X,Y)|R1],R2,c,F):-                            % disj(X,X)
        var(X), var(Y), samevar(X,Y),!,
        X = {},
        sat_step(R1,R2,_,F).                                 
sat_disj([disj(X,Y)|R1],R2,c,F):-                            % disj(Y,X) --> disj(X,Y)
        var(X),var(Y),
        X @> Y,!,
        sat_step([disj(Y,X)|R1],R2,_,F).                         
sat_disj([disj(X,Y)|R1],[disj(X,Y)|R2],Stop,F):-             % disj(X,Y) (irreducible form)
        var(X), var(Y),!,
        sat_step(R1,R2,Stop,F).
sat_disj([disj(Set1,Set2)|R1],R2,c,F):-                      % disj({...},{...}) 
        nonvar(Set1), Set1 = S1 with T1,
        nonvar(Set2), Set2 = S2 with T2,!,
        sat_step([T1 neq T2,T1 nin S2,T2 nin S1,set(S1),set(S2),disj(S1,S2)|R1],R2,_,F).
sat_disj([disj(Set,X)|R1],R2,c,F):-                          % disj({...},X)   
        nonvar(Set), Set = T2 with T1,
        var(X),!,
        sat_step([T1 nin X,set(T2),disj(X,T2)|R1],R2,_,F).
sat_disj([disj(X,Set)|R1],R2,c,F):-                          % disj(X,{...})   
        nonvar(Set), Set = T2 with T1,
        var(X),!,
        sat_step([T1 nin X,set(T2),disj(X,T2)|R1],R2,_,F).
sat_disj([disj(Set1,_)|R1],R2,c,F):-                         % disj({},t) or disj(int(a,b),t) with a > b 
        nonvar(Set1), is_empty(Set1),!,
        sat_step(R1,R2,_,F).
sat_disj([disj(_,Set2)|R1],R2,c,F):-                         % disj(t,{}) or disj(t,int(a,b)) with a > b  
        nonvar(Set2), is_empty(Set2),!,
        sat_step(R1,R2,_,F).
sat_disj([disj(I1,I2)|R1],R2,c,F):-                          % disj(int(a,b),int(c,d)) 
        nonvar(I1), is_int(I1,S1,S2),        
        nonvar(I2), is_int(I2,T1,T2),!,        
        (solve_FD(S2 + 1 =< T1)
         ;
         solve_FD(T2 + 1 =< S1)
         ;
         solve_FD(S2 + 1 =< T1), solve_FD(T2 + 1 =< S1)
        ),
        sat_step(R1,R2,_,F).
sat_disj([disj(I1,Set)|R1],R2,c,F):-                         % disj(int(A,A),t)  
        nonvar(I1), is_int(I1,S1,S2), S1==S2, !,
        sat_step([S1 nin Set|R1],R2,_,F).
sat_disj([disj(I1,Set)|R1],R2,c,F):-                         % disj(int(a,b),t)  
        nonvar(I1), is_int(I1,S1,S2),!,
        S3 is S1 + 1,
        sat_step([S1 nin Set, disj(int(S3,S2),Set)|R1],R2,_,F).
sat_disj([disj(Set,I1)|R1],R2,c,F):-                         % disj(t,int(a,b))  
        nonvar(I1), is_int(I1,_S1,_S2),
        sat_step([disj(I1,Set)|R1],R2,_,F).
       
%%%%%%%%%%%%%%%%%%%%%% not union (nun/3)

sat_nun([nun(S1,S2,S3)|R1],R2,c,F):-               % nun(s1,s2,s3) 
        sat_step([N in S3,N nin S1,N nin S2|R1],R2,_,F).
sat_nun([nun(S1,_S2,S3)|R1],R2,c,F):-              % 
        sat_step([N in S1,N nin S3|R1],R2,_,F).
sat_nun([nun(_S1,S2,S3)|R1],R2,c,F):-              % 
        sat_step([N in S2,N nin S3|R1],R2,_,F).

%%%%%%%%%%%%%%%%%%%%%% not disjointness (ndisj/2)

sat_ndisj([ndisj(I1,I2)|R1],R2,c,F):-              % ndisj(int(...),int(...)) 
        nonvar(I1), is_int(I1,S1,S2),        
        nonvar(I2), is_int(I2,T1,T2),!,        
        (solve_FD(S1 =< T1), solve_FD(T1 =< S2)
         ;
         solve_FD(T1 =< S1), solve_FD(S1 =< T2)
        ),
        sat_step(R1,R2,_,F).
sat_ndisj([ndisj(X,Y)|R1],R2,c,F):-                % ndisj(X,X)
        var(X), var(Y), samevar(X,Y),!,
        sat_step(R1,R2,_,F).                                 
sat_ndisj([ndisj(S,T)|R1],R2,c,F):-                % ndisj({...},{...})
        sat_step([N in S, N in T|R1],R2,_,F).

%%%%%%%%%%%%
%%%%%%%%%%%% Rewriting rules for aggregate constraints %%%%%%%%%%%%
%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%% set cardinality (size/2)              

sat_size([size(S,N)|R1],
        [solved(size(S,N),(var(S),var(N)),1,f)|R2],c,F):-   %   
        var(S),var(N),!,                           % size(S,N) (irreducible form)
        solve_FD(N >= 0),
        sat_step(R1,R2,_,F).
sat_size([size(S,0)|R1],R2,c,F):-                  % size({},t) or size(int(a,b),t), 
        is_empty(S),!,                             % with a>b (S either var or nonvar)           
        sat_step(R1,R2,_,F).                       
sat_size([size(I,T)|R1],R2,c,F):-                  % size(int(a,b),t)
        nonvar(I), is_int(I,A,B),!,   
        simple_integer_expr(T),     
        solve_FD(T is B-A+1),
        sat_step(R1,R2,_,F).
sat_size([size(S,T)|R1],R2,c,F):-                  % ground case
        ground(S),!,                
        simple_integer_expr(T),     
        g_size(S,T),
        sat_step(R1,R2,_,F).
sat_size([size(S,T)|R1],[size(S,T)|R2],Stop,nf):-  % size(S,k), S var., k nonvar
        var(S),!,                                  % delayed until final_sat is called 
        sat_step(R1,R2,Stop,nf).                   
sat_size([size(S,T)|R1],R2,c,f):-                  % LEVEL 3: size(S,k), S var., k int. const.
        var(S),!,                                  
        integer(T),         
        solve_FD(T >= 1),
        S = R with X,
        solve_FD(M is T-1),
        sat_step([X nin R,set(R),integer(M),size(R,M)|R1],R2,_,f). 
%sat_size([size(S,T)|R1],[solved(size(S,T),true,1,nf)|R2],c,nf):-   %   
%        bounded(S),!,                       % size(S,t), S bounded set {t1,...,tn}          
%        simple_integer_expr(T),             % delayed until final_sat is called 
%        solve_FD(T >= 1),            
%        count_var(S,NVar,Var),   % FOR SET OF VARs ONLY: TO BE EXTENDED TO GENERAL TERMS!              
%        MaxNoTerm is NVar + Var,
%        (NVar==0, MinNoTerm=1 ; NVar>0, MinNoTerm=NVar),
%        solve_FD(T in int(MinNoTerm,MaxNoTerm)),
%        sat_step(R1,R2,_,nf). 
sat_size([size(R with X,T)|R1],[size(R with X,T)|R2],Stop,nf) :- !,   %size({...|R},t)
        sat_step(R1,R2,Stop,nf).                   % delayed until final_sat is called  
sat_size([size(R with X,T)|R1],R2,c,f):-           
        simple_integer_expr(T),                    % LEVEL 3: size({...},t)
        solve_FD(T >= 1),
        solve_FD(M is T-1),
        (sat_step([X nin R,set(R),integer(M),size(R,M)|R1],R2,_,f)     
         ;
         sat_step([R=N with X,set(N),X nin N,integer(M),size(N,M)|R1],R2,_,f)).

count_var(T,0,0) :-      % count_var/3 not used at present
        is_empty(T),!.                
count_var(R with A,NonVar,Var):-           % var(A)
        var(A),!,     
        count_var(R,NonVar,Var1),
        Var is Var1 + 1.
count_var(R with A,NonVar,Var):-           % nonvar(A), duplicate A
        find_gdup(A,R),!,
        count_var(R,NonVar,Var).
count_var(R with _A,NonVar,Var):-          % nonvar(A)
        count_var(R,NonVar1,Var),
        NonVar is NonVar1 + 1.

find_gdup(X,R with Y) :-
        var(Y),!,
        find_gdup(X,R).
find_gdup(X,_R with Y) :-
        sunify(X,Y,_),!.
find_gdup(X,R with _Y) :-
        find_gdup(X,R).

%%%%%%%%%%%%%%%%%%%%% set sum (sum/2)              

sat_sum([sum(S,N)|R1],
        [solved(sum(S,N),(var(S),var(N)),1,f)|R2],c,F):-   %  
        var(S),var(N),!,                           % sum(S,N) (irreducible form)
        solve_FD(N >= 0),
        sat_step(R1,R2,_,F).
sat_sum([sum(S,0)|R1],R2,c,F):-                    % sum({},t) or sum(int(a,b),t), 
        is_empty(S),!,                             % with a>b (S either var or nonvar)
        sat_step(R1,R2,_,F).                       
sat_sum([sum(I,T)|R1],R2,c,F):-                    % sum(int(a,b),t)
        nonvar(I),is_int(I,A,B),
        A =< B,!,  
        simple_integer_expr(T),     
        solve_FD(T is ((B*(B+1))-(A*(A-1)))/2),
        sat_step(R1,R2,_,F).
sat_sum([sum(S,T)|R1],R2,c,F):-                    % ground case
        ground(S),!,                
        simple_integer_expr(T),     
        g_sum(S,T),                 
        sat_step(R1,R2,_,F).
sat_sum([sum(S,T)|R1],[sum(S,T)|R2],Stop,nf):-     % sum(S,k), k int. const, S var.
        var(S), integer(T),!,                      % delayed until final_sat is called
        sat_step(R1,R2,Stop,nf).                   % (--> Level 3)
sat_sum([sum(S,T)|R1],[solved(sum(S,T),var(S),1,f)|R2],Stop,f):-        
        var(S), integer(T),                        % LEVEL 3: sum(S,k), k int. const, S var.
        nolabel,!,                                 % if nolabel --> irreducible form
        sat_step(R1,R2,Stop,f).
sat_sum([sum(S,T)|R1],R2,c,f):-                    % LEVEL 3: sum(S,k), k int. const, S var.
        var(S), integer(T),!, 
        solve_FD(T >= 0),            
        sum_all(S,T,int(0,T),[]),
        sat_step(R1,R2,_,f). 
sat_sum([sum(R with X,T)|R1],
        [solved(sum(R with X,T),true,1,nf)|R2],c,nf):-   %  
        integer(T),!,                              % sum({...},k)
        solve_FD(T >= 0),                          % delayed until final_sat is called
        add_elem_domain(R with X,T),        
        sat_step(R1,R2,_,nf). 
sat_sum([sum(R with X,T)|R1],[sum(R with X,T)|R2],Stop,nf):- !,  
%        var(T),!,                                 % sum({...},N)
        sat_step(R1,R2,Stop,nf).                   % delayed until final_sat is called 
sat_sum([sum(R with X,T)|R1],R2,c,f):-              
        simple_integer_expr(T),                    % LEVEL 3: sum({...},t)  
        simple_integer_expr(X),     
        solve_FD(T >= 0),            
        solve_FD(X >= 0),            
        solve_FD(T is M+X),
        (sat_step([integer(X),X nin R,set(R),sum(R,M)|R1],R2,_,f) 
        ; 
        sat_step([integer(X),R=N with X,X nin N,set(N),sum(N,M)|R1],R2,_,f) ). 

sum_all({},0,_,_).
sum_all(R with X,N,L,G) :-
        solve_FD(X in L), 
        in_order_list(X,G),
        solve_FD(N is X + M),
        sum_all(R,M,L,[X|G]),
        clpfd:indomain(X).

in_order_list(_A,[]) :- !.
in_order_list(A,[B|_R]) :-  
        solve_FD(A > B).

add_elem_domain(R,_):-     
       var(R),!.
add_elem_domain(T,_) :-
       is_empty(T),!.
add_elem_domain(R with A,N):-                
       solve_FD(A in int(0,N)),   
       add_elem_domain(R,N).


%%%%%%%% Under development - to be completed and tested

%%%%%%%%%%%%%%%%%%%%%%  min  (min/2)   %%%%%%%%%%%        
% find the minimum of a set S of non-negative integers.

sat_min([smin(S,N)|R1],
        [solved(smin(S,N),(var(S),var(N)),1,f)|R2],c,F):-   %  
        var(S),var(N),!,               % smin(S,N) (irreducible form)
        solve_FD(N >= 0),                    
        sat_step(R1,R2,_,F).
sat_min([smin(S,_)|_],_,c,_):-         % smin({},t) or smin(int(a,b),t) with a>b 
        nonvar(S),is_empty(S),!,
        fail.                       
sat_min([smin(S,T)|R1],R2,c,F):-       % smin({X},T)                       
        nonvar(S),S=R with X,
        nonvar(R),is_empty(R),!,
        T = X,
        simple_integer_expr(T),
        solve_FD(T >= 0),
        sat_step(R1,R2,_,F).       
sat_min([smin(I,T)|R1],R2,c,F):-       % smin(int(a,b),t) t=a
        nonvar(I),is_int(I,A,_B),!,
%        solve_FD(A=<B),   
        T = A,
        solve_FD(T >= 0),
        sat_step(R1,R2,_,F).
sat_min([smin(S,T)|R1],R2,c,F):-       % ground case 
        ground(S),!,                
        simple_integer_expr(T),     
        g_min(S,T),
        sat_step(R1,R2,_,F).
sat_min([smin(S,T)|R1],[smin(S,T)|R2],Stop,nf):-  % smin(S,t), S var., t nonvar
        var(S),!,                     % delayed until final_sat is called
        sat_step(R1,R2,Stop,nf).      % (--> Level 3)
sat_min([smin(S,T)|R1],R2,R,f):-      % LEVEL 3: smin(S,k) S var., k nonvar      
        var(S),!,                     % (k integer constant)          
        integer(T),        
        solve_FD(T >= 0),
        (sat_step([S=N with X,set(N),integer(X),X nin N,X = T,smin(N,M),M > T|R1],R2,R,f)
         ;
         sat_step([S={} with X,integer(X),X = T|R1],R2,R,f)). 
sat_min([smin(R with X,T)|R1],[smin(R with X,T)|R2],Stop,nf):- 
        bounded(R with X),!,          % smin(s,t), s bounded
        simple_integer_expr(X),
        solve_FD(T >= 0),    
        minim(R with X,T),       
        sat_step(R1,R2,Stop,nf).  
sat_min([smin(R with X,T)|R1],[smin(R with X,T)|R2],Stop,nf):-!,  % smin({...|R},t)
        sat_step(R1,R2,Stop,nf).                % delayed until final_sat is called
sat_min([smin({} with X,T)|R1],R2,c,f):-        % LEVEL 3: smin({...},t)           
        simple_integer_expr(X),
        solve_FD(T >= 0), 
        sat_step([integer(X),X = T|R1],R2,_,f). 
sat_min([smin(R with X,T)|R1],R2,c,f):-         % LEVEL 3: smin({...},t)           
        simple_integer_expr(T),
        simple_integer_expr(X),
        solve_FD(T >= 0), 
        (sat_step([integer(X),set(R),X = T,smin(R,M),M >= T|R1],R2,_,f)
         ; 
         sat_step([integer(X),set(R),X > T,smin(R,T)|R1],R2,_,f)
        ). 

minim({},_). 
minim(int(A,_),A).                 
minim(R with A,N):- 
        simple_integer_expr(A),               
        solve_FD(A >= N),  
        minim(R,N).

g_min(L,X) :-
        L = _R with A,
        integer(A),A>=0,
        gg_min(L,A,X).
  
gg_min({},P,M):-
        solve_FD(M is P).
gg_min(int(A,_),P,M) :-
        fd_min(A,P,M).
gg_min(R with A,P,M) :-
        integer(A), A>=0,
        fd_min(A,P,G),
        gg_min(R,G,M).
   
fd_min(X,Y,J) :-
        solve_FD(X > Y),
        solve_FD(J is Y). 
fd_min(X,Y,J) :-
        solve_FD(X =< Y),
        solve_FD(J is X).

%%%%%%%%%%%%%%%%%%%%%% max (max/2)  %%%%%%%%%          

sat_max([smax(S,N)|R1],
        [solved(smax(S,N),(var(S),var(N)),1,f)|R2],c,F):-   %   
        var(S),var(N),!,                % smax(S,N) (irreducible form)
        solve_FD(N >= 0),           
        sat_step(R1,R2,_,F).
sat_max([smax(S,_)|_],_,c,_) :-         % smax({},t) or smax(int(a,b),t) with a>b 
        nonvar(S),is_empty(S),!,
        fail.                       
sat_max([smax(S,T)|R1],R2,c,F):-        % smax({X},t)                       
        nonvar(S),S=R with X,
        nonvar(R),is_empty(R),!,
        T = X,
        simple_integer_expr(T),
        solve_FD(T >= 0),
        sat_step(R1,R2,_,F).       
sat_max([smax(I,T)|R1],R2,c,F):-        % smax(int(a,b),t) t=b
        nonvar(I), is_int(I,_A,B),!,
%        solve_FD(A=<B),   
        T = B,
        solve_FD(T >= 0),
        sat_step(R1,R2,_,F).
sat_max([smax(S,T)|R1],R2,c,F):-        % ground case
        ground(S),!,                
        simple_integer_expr(T),     
        g_max(S,T),
        sat_step(R1,R2,_,F).
sat_max([smax(S,T)|R1],[smax(S,T)|R2],Stop,nf) :-  % smax(S,t), S var., t nonvar
        var(S),!,                       % delayed until final_sat is called 
        sat_step(R1,R2,Stop,nf).        % (--> Level 3)    
sat_max([smax(S,T)|R1],R2,R,f):-        % LEVEL 3: smax(S,k) S var., k nonvar      
        var(S),!,                       % (k integer constant)          
        integer(T),     
        solve_FD(T >= 0),
        (sat_step([S=N with X,set(N),integer(X),X nin N,X = T,smax(N,M),M < T|R1],R2,R,f)
         ;
         sat_step([S={} with X,integer(X),X = T|R1],R2,R,f)). 
sat_max([smax(R with X,T)|R1],[smax(R with X,T)|R2],Stop,nf):- 
        bounded(R with X),!, 
        simple_integer_expr(X),         % smax(s,t), s bounded
        solve_FD(T >= 0),  
        mass(R with X,T),       
        sat_step(R1,R2,Stop,nf).  
sat_max([smax(R with X,T)|R1],[smax(R with X,T)|R2],Stop,nf):-!,  % smax({...|R},t)
        sat_step(R1,R2,Stop,nf).                % delayed until final_sat is called
sat_max([smax({} with X,T)|R1],R2,_,f) :-       % LEVEL 3: smax({...},t)  
        simple_integer_expr(X),
        solve_FD(T >= 0), 
        sat_step([integer(X),X = T|R1],R2,_,f). 
sat_max([smax(R with X,T)|R1],R2,_,f) :-        % LEVEL 3: smax({...},t)  
        simple_integer_expr(T),
        simple_integer_expr(X),
        solve_FD(T >= 0), 
        (sat_step([set(R),integer(X),X = T,smax(R,M),M =< T|R1],R2,_,f)
        ; 
         sat_step([set(R),integer(X),X < T,smax(R,T)|R1],R2,_,f)). 

mass({},_).
mass(int(_,B),B).                 
mass(R with A,N):-
        simple_integer_expr(A),   
        solve_FD(A >= 0),
        solve_FD(A =< N),
        mass(R,N).

g_max(L,X) :-
        gg_max(L,0,X).

gg_max({},P,M):- 
        solve_FD(M is P).
gg_max(int(_,B),P,M) :-
        fd_max(B,P,M).
gg_max(R with A,P,M) :-
        integer(A), A>=0,
        fd_max(A,P,G),
        gg_max(R,G,M).
   
fd_max(X,Y,X) :-
        solve_FD(X >= Y). 
fd_max(X,Y,Y) :-
        solve_FD(X < Y).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%% implementation of ground cases %%%%%%%%%%%%%%%%%%%              

g_neq(T1,T2) :- 
         \+g_equal(T1,T2).

% deterministic membership (for intervals/sets/multisets/lists): 
% g_member(T,A) is true if A contains T (T, A non-variable terms)
g_member(X,I):-                
        is_int(I,A,B),integer(X),!, 
        X >= A, X =< B.
g_member(X,S):-
        aggr_comps(S,Y,_R),
        g_equal(X,Y),!.
g_member(X,S):-
        aggr_comps(S,_Y,R),
        g_member(X,R).

g_subset(T,_) :-
        is_empty(T).
g_subset(I,S) :-
        is_int(I,A,A),!,
        g_member(A,S).
g_subset(I,S) :-
        is_int(I,A,B),!,
        g_member(A,S),
        A1 is A + 1,
        g_subset(int(A1,B),S).
g_subset(R with X,S2) :-
        g_member(X,S2),
        g_subset(R,S2).

g_equal(T1,T2) :- 
        is_empty(T1), is_empty(T2),!.
g_equal(T1,T2) :-
        T1 = T2,!.
g_equal(T1,T2) :-
        g_subset(T1,T2),
        g_subset(T2,T1).

g_union(T,S,S) :-
        is_empty(T),!.              
g_union(S1 with X,S2,S3 with X) :-
        g_union(S1,S2,S3).

g_inters(T,_S,{}) :- 
        is_empty(T),!.
g_inters(_S,T,{}) :- 
        is_empty(T),!.
g_inters(S1 with X,S2,S3 with X) :-
        g_member(X,S2),!,
        g_inters(S1,S2,S3).
g_inters(S1 with _X,S2,S3) :-
        g_inters(S1,S2,S3).

g_size(T,0) :-
        is_empty(T),!.            
g_size(int(A,B),N) :- !, 
        N is B-A+1.            
g_size(R with A,N):-
        g_member(A,R),!,
        g_size(R,N).
g_size(R with _A,N):-
        solve_FD(N is M+1),
        g_size(R,M).
 
g_sum(T,0) :-
        is_empty(T),!. 
g_sum(R with A,N):-
        integer(A), A >= 0,         
        g_member(A,R),!,
        g_sum(R,N).
g_sum(R with A,N):-          
        integer(A), A >= 0,            
        solve_FD(N is M+A),   
        g_sum(R,M).

g_greater(X,Y,X) :- X >= Y,!.
g_greater(_X,Y,Y).

g_smaller(X,Y,X) :- X =< Y,!.
g_smaller(_X,Y,Y).


%%%%%%%%%%%%
%%%%%%%%%%%% Rewriting rules for type constraints %%%%%%%%%%%%
%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%% set (set/1)

sat_set([set(X)|R1],[set(X)|R2],Stop,F):-        % set(X) (irreducible form)
        var(X),!,
        sat_step(R1,R2,Stop,F).
sat_set([set(X)|R1],R2,c,F):-                    % set({}) 
        X == {}, !,
        sat_step(R1,R2,_,F).
sat_set([set(X)|R1],R2,c,F):-                    % set({...}) 
        X = _S with _A, !,
        sat_step(R1,R2,_,F).
sat_set([set(X)|R1],R2,c,F):-                    % set(int(...))    
        X = int(A,B),!, 
        sat_step([integer(A),integer(B)|R1],R2,_,F).    
sat_set([set(X)|R1],R2,c,F) :- 
        is_ris(X,ris(_,_,_,_,_)),!,                 
        sat_step(R1,R2,_,F).    

%%%%%%%%%%%%%%%%%%%%%% bag (bag/1)

sat_bag([bag(X)|R1],[bag(X)|R2],Stop,F):-        % bag(X) (irreducible form)
        var(X),!, 
        sat_step(R1,R2,Stop,F).
sat_bag([bag(X)|R1],R2,c,F):- 
        X == {}, !,
        sat_step(R1,R2,_,F).
sat_bag([bag(X)|R1],R2,c,F):-                    
        X = _S mwith _A,
        sat_step(R1,R2,_,F).

%%%%%%%%%%%%%%%%%%%%%% list (list/1)

sat_list([list(X)|R1],[list(X)|R2],Stop,F):-     % list(X) (irreducible form)
        var(X),!, 
        sat_step(R1,R2,Stop,F).
sat_list([list(X)|R1],R2,c,F):- 
        X == [], !,
        sat_step(R1,R2,_,F).
sat_list([list(X)|R1],R2,c,F):-                    
        X = [_A|_S],
        sat_step(R1,R2,_,F).

%%%%%%%%%%%%%%%%%%%%%% integer (integer/1)

sat_integer([integer(X)|R1],[integer(X)|R2],Stop,F):-  % integer(X) (irreducible form)
        var(X),!,    
        sat_step(R1,R2,Stop,F).
sat_integer([integer(T)|R1],R2,c,F):-                  % integer(t), t is an integer constant            
        integer(T),
        sat_step(R1,R2,_,F).

%%%%%%%%%%%%%%%%%%%%%% not integer (ninteger/1)

sat_ninteger([ninteger(X)|R1],[ninteger(X)|R2],Stop,F) :-  % ninteger(X) (irreducible form)
       var(X), !,    
       sat_step(R1,R2,Stop,F).
sat_ninteger([ninteger(X)|R1],R2,c,F) :-
       \+integer(X),
       sat_step(R1,R2,_,F).

%%%%%%%%%%%%
%%%%%% Rewriting rules for constraints over binary relations and partial functions %%%%%%%%%%%%
%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%% binary relation (rel/1)  

sat_rel([rel(X)|R1],[rel(X)|R2],Stop,F):-          % rel(X) (irreducible form)
        var(X),!,
        sat_step(R1,R2,Stop,F).
sat_rel([rel(X)|R1],R2,c,F):-                      % rel({}) or or rel(int(a,b)) with a>b
        nonvar(X),is_empty(X),!,
        sat_step(R1,R2,_,F).
sat_rel([rel(X)|R1],R2,c,F):-                      % rel({[t1,t2],...,[t1,t2],...})   
        X = S with [_A1,_A2],!, 
        sat_step([rel(S)|R1],R2,_,F).  


%%%%%%%%%%%%%%%%%%%%%% partial function (pfun/1)

sat_pfun([pfun(X)|R1],[pfun(X)|R2],Stop,F):-       % pfun(X) (irreducible form)
        var(X),!,
        sat_step(R1,R2,Stop,F).
sat_pfun([pfun(X)|R1],R2,c,F):-                    % pfun({}) or or pfun(int(a,b)) with a>b
        nonvar(X),is_empty(X),!,
        sat_step(R1,R2,_,F).
sat_pfun([pfun(X)|R1],R2,c,F):-                    % pfun(F), with F closed set and dom(F) ground
        dom_all_known(X),!,
        is_pfun(X),
        sat_step(R1,R2,_,F).
sat_pfun([pfun(X)|R1],R2,c,F):-                    % pfun({[...],[...],...})
        X = S with [A1,_A2],
        not_occur(A1,S,C),
        append(C,R1,R3),
        sat_step([pfun(S)|R3],R2,_,F).   
sat_pfun([pfun(X)|R1],R2,c,F):-                    % pfun({[t1,t2],...,[t1,t2],...})   
        X = S with [A1,A2], 
        sunify(S,R with [A1,A2],_),                
        not_occur(A1,R,C),
        append(C,R1,R3),
        sat_step([pfun(R)|R3],R2,_,F).  
%       sat_step([[A1,A2] nin R,pfun(R)|R3],R2,_,F).  

not_occur(A,S,[dompf(S,D),A nin D,set(D)]) :-       
        var(S),!.
not_occur(_A,{},[]) :- !.
not_occur(A,R with [A1,_A2],[A neq A1|CR]) :-
        not_occur(A,R,CR).

is_pfun({}) :- !.
is_pfun(PFun with P) :- 
    is_pfun_cont(PFun,P), 
    is_pfun(PFun).

is_pfun_cont({},_P1) :- !.
is_pfun_cont(F1 with P2,P1) :- 
    nofork(P1,P2), 
    is_pfun_cont(F1,P1).

nofork([X1,_Y1],[X2,_Y2]) :- 
    X1 \== X2,!.
nofork([X1,Y1],[X2,Y2]) :- 
    X1 = X2, Y1 = Y2.

dom_all_known(R) :-      
    nonvar(R), R={}, !.
dom_all_known(R with [X,_]) :- 
    ground(X),
    dom_all_known(R).


%%%%%%%%%%%%%%%%%%%%%% domain of a binary relation (dom/2)  

sat_dom([dom(X,Y)|R1],R2,c,F):-                   % dom(X,X)
        var(X),var(Y),X==Y,!, X = {},                          
        sat_step(R1,R2,_,F).
sat_dom([dom(S,D)|R1],[dom(S,D)|R2],Stop,F):-     % dom(S,D) (irreducible form) 
        var(S),var(D),!,                           
        sat_step(R1,R2,Stop,F).
sat_dom([dom(S,D)|R1],R2,c,F):-                   % dom({},d) or dom(int(a,b),d) with a>b
        nonvar(S),is_empty(S),!, 
        sunify(D,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).                         
sat_dom([dom(S,D)|R1],R2,c,F):-                   % dom(s,{}) or dom(s,int(a,b)) with a>b
        nonvar(D),is_empty(D),!, 
        sunify(S,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).                     
sat_dom([dom(S,D)|R1],R2,c,F):-                   % dom({[...],...},D) or dom({[...],...},{...}) or dom({[...],...},int(t1,t2))      
        nonvar(S), S = SR with [A1,_A2], !,
        sunify(D,DR with A1,C),
        append(C,R1,R3),
        sat_step([dom(SR,DR)|R3],R2,_,F).                                          
sat_dom([dom(S,D)|R1],[dom(S,D)|R2],Stop,F):-     % dom(S,R) (irreducible form) 
        var(S),var(D),!,                           
        sat_step(R1,R2,Stop,F).                                                  
sat_dom([dom(S,D)|R1],R2,c,F):-                   % dom(S,{t}) 
        var(S), nonvar(D), D = E with A, nonvar(E), is_empty(E), !,                          
        sat_step([comp({} with [A,A],R,R),S = R with [A,Z],[A,Z] nin R|R1],R2,_,F).   
sat_dom([dom(S,D)|R1],R2,c,F):-                   % dom(S,{t1,...,tn}), n > 1 or dom(S,{t1/R}),
        var(S),nonvar(D), D = DR with A,!,                           
        sat_step([dom(S1,{} with A),dom(S2,DR),disj(S1,S2),delay(un(S1,S2,S),false)|R1],R2,_,F).


%%%%%%%%%%%%%%%%%%%%%% inverse of a binary relation (inv/2)

sat_inv([inv(R,S)|R1],[inv(R,S)|R2],Stop,F):-     % inv(X,Y) (irreducible form) 
        var(R),var(S),!,                           
        sat_step(R1,R2,Stop,F).
sat_inv([inv(R,S)|R1],R2,c,F):-                   % inv({},S) 
        nonvar(R),R={},!, 
        sunify(S,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).                         
sat_inv([inv(R,S)|R1],R2,c,F):-                   % inv(R,{}) 
        nonvar(S),S={},!, 
        sunify(R,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).                         
sat_inv([inv(R,S)|R1],R2,c,F):-                   % inv({...},S) or inv({...},{...})      
        nonvar(R), R = _ with [X,Y], !,
        sunify(R,RR with [X,Y],C1), append(C1,R1,C1R1),
        sunify(S,SR with [Y,X],C2), append(C1R1,C2,R3),
        sat_step([[X,Y] nin RR,[Y,X] nin SR,inv(RR,SR)|R3],R2,_,F).                                          
sat_inv([inv(R,S)|R1],R2,c,F):-                   % inv(R,{...})     
        var(R), nonvar(S), S = _ with [X,Y], !,
        sunify(S,SR with [X,Y],C1), append(C1,R1,R3),
        R = RR with [Y,X],
        sat_step([[X,Y] nin SR,inv(RR,SR)|R3],R2,_,F).                                          
                       

%%%%%%%%%%%%%%%%%%%%%% range of a binary relation (ran/2)

%sat_ran2dom([ran(R,A)|R1],R2,c,F) :-                  
%        sat_step([inv(R,S),dom(S,A)|R1],R2,_,F).
                 
%%%%%%%%%%%%%%%%%%%%%% range of a binary relation (ran/2)

sat_ran([ran(X,Y)|R1],R2,c,F):-                   % ran(X,X)
        var(X),var(Y),X==Y,!, X = {},                          
        sat_step(R1,R2,_,F).
sat_ran([ran(S,D)|R1],R2,c,F):-                   % ran({},r) or ran(int(a,b),r) with a>b
        nonvar(S),is_empty(S),!, 
        sunify(D,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).                         
sat_ran([ran(S,D)|R1],R2,c,F):-                   % ran(S,{}) or ran(S,int(a,b)) with a>b
        nonvar(D), is_empty(D),!, 
        sunify(S,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).  
sat_ran([ran(S,D)|R1],[ran(S,D)|R2],Stop,F):-     % ran(S,R) or ran(S,r) (irreducible forms) 
        var(S), noran_elim,!,                           
        sat_step(R1,R2,Stop,F).
sat_ran([ran(S,D)|R1],R2,c,F):-                   % ran({[...],...},R) or ran({[...],...},{...}) or ran({[...],...},int(t1,t2))
        nonvar(S), S = SR with [_A1,A2], noran_elim,!,
        sunify(D,DR with A2,C),
        append(C,R1,R3),
        (var(SR),nonvar(DR), DR=_ with _,!,                      
         sat_step([solved(ran(SR,DR),var(SR),[],f)|R3],R2,_,F)   
         ;
         sat_step([ran(SR,DR)|R3],R2,_,F)                     
        ).
sat_ran([ran(S,D)|R1],[ran(S,D)|R2],Stop,F):-     % ran(S,R) (irreducible form) 
        var(S),var(D),!,                           
        sat_step(R1,R2,Stop,F).                                                
sat_ran([ran(S,D)|R1],R2,c,F):-                   % ran(S,{t}) 
        var(S), nonvar(D), D = E with A, nonvar(E), is_empty(E), !,                          
        sat_step([comp(R,{} with [A,A],R),S = R with [Z,A],[Z,A] nin R|R1],R2,_,F).  
sat_ran([ran(S,D)|R1],R2,c,F):-                   % ran(S,{t1,...,tn}), n > 1 or  ran(S,{t1/R}),
        var(S),nonvar(D),D = DR with A,!,                           
        sat_step([ran(S1,{} with A),ran(S2,DR),disj(S1,S2),delay(un(S1,S2,S),false)|R1],R2,_,F).                       
sat_ran([ran(S,D)|R1],R2,c,F):-                   % ran({[...],...},R) or ran({[...],...},{...}) or ran({[...],...},int(t1,t2))
        nonvar(S), S = SR with [_A1,A2],!,
        sunify(D,DR with A2,C),
        append(C,R1,R3),
        sat_step([ran(SR,DR)|R3],R2,_,F) .                  


%%%%%%%%%%%%%%%%%%%%%% composition of binary relations (comp/3)  

sat_comp([comp(R,_S,T)|R1],R2,c,F):-             % comp({},s,t) or comp(int(a,b),s,t) with a>b
        nonvar(R),is_empty(R),!, 
        sunify(T,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).                         
sat_comp([comp(_R,S,T)|R1],R2,c,F):-             % comp(r,{},t) or comp(r,int(a,b),t) with a>b
        nonvar(S),is_empty(S),!, 
        sunify(T,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).    
sat_comp([comp(R,S,T)|R1],R2,c,F):-              % comp(r,s,{}) or comp(r,s,int(a,b)) with a>b
        nonvar(T),is_empty(T),!, 
        sat_step([ran(R,RR),dom(S,DS),disj(RR,DS)|R1],R2,_,F).                         
sat_comp([comp(R,S,T)|R1],[comp(R,S,T)|R2],Stop,F):-  
        (var(R),var(T),! ; var(S),var(T)),!,     % comp(R,s,T) or comp(r,S,T), r and s not empty set,                        
        sat_step(R1,R2,Stop,F).                  % irreducible forms                        

sat_comp([comp(R,S,Q)|CR1],CR2,c,F):-            % special case: comp({[A,A]},{[X,Z]/N},{[X,Z]/N}), var(N)     
        nonvar(R), R = {} with [A,A], 
        nonvar(S), S = N with [X,_], var(N), var(X),
        nonvar(Q), Q = S,!,                      
        X = A,            
        sat_step([comp({} with [A,A],N,N) | CR1],CR2,_,F). 
sat_comp([comp(R,S,Q)|CR1],CR2,c,F):-            % special case: comp({[X,Z]/N},{[A,A]},{[X,Z]/N}), var(N)     
        nonvar(R), R = N with [_,Y], var(N), var(Y),
        nonvar(S), S = {} with [A,A], 
        nonvar(Q), Q = R,!,                      
        Y = A,         
        sat_step([comp(N,{} with [A,A],N) | CR1],CR2,_,F). 
  
sat_comp([comp(R,S,Q)|CR1],CR2,c,F):-            % comp(R,S,{[X,Z]}), var(R), var(S)     
        nonvar(Q), var(R), var(S), 
        Q = QQ with [X,Z], nonvar(QQ), is_empty(QQ), !,
        sat_step([un(R1,R2,R),un(S1,S2,S),disj(R1,R2),disj(S1,S2),
                  dom(R1,{} with X),ran(S1,{} with Z),
                  ran(R1,A1),dom(S1,B1),A1=B1,    
                  dom(S2,B2),ran(R2,A2),
                  disj(A1,B2),disj(A2,B1),disj(A2,B2) | CR1],CR2,_,F). 
sat_comp([comp(R,S,T)|R1],R2,c,F):-              % comp(r,s,{[X,Y],...})      
        nonvar(T), T = _ with [X,Z], !,
        sunify(R,RR with [X,Y],C1),
        sunify(S,SR with [Y,Z],C2),
        append(C1,C2,C12),
        append(C12,R1,R3),
        sat_step([[X,Y] nin RR,[Y,Z] nin SR,[X,Z] nin Q1,
                  comp({} with [X,Y],SR,Q1),
                  comp(RR,{} with [Y,Z],Q2),
                  comp(RR,SR,Q3), Q11 = Q1 with [X,Z],
                  un(Q11,Q2,Q1_2),un(Q1_2,Q3,T), 
                  disj(Q11,Q2),disj(Q1_2,Q3) | R3],R2,_,F).   
 
sat_comp([comp(R,S,T)|R1],R2,c,F):-              % comp({[X,Y]},{[Z,V]},T), T var.     
        var(T),
        nonvar(R), R = {} with [X,Y],           
        nonvar(S), S = {} with [Y,Z],   
        T = {} with [X,Z],
        sat_step(R1,R2,_,F).    
sat_comp([comp(R,S,T)|R1],R2,c,F):-              % comp({[X,Y],...},{...},T), T var.  
        var(T),                                  % forall(Z,[Y,Z] nin S)    
        nonvar(R), R = {} with [_X,Y],
        nonvar(S), S = {} with [_Y,_Z],!, 
        T = {},                     
        sat_step([dom(S,DS),Y nin DS|R1],R2,_,F). 
                                    
sat_comp([comp(R,S,T)|R1],R2,c,F):-              % comp({[X,Y],...},{...},T), T var.     
        var(T),!,
        comp_distribute(R,S,C,{},T),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).    

comp_distribute(R,S,C,T0,T) :-
        var(R),!,
        comp_distribute_first(R,S,C,T0,T).
comp_distribute({},_S,[],T,T) :- !.
comp_distribute(RR with P,S,C,T0,T) :-
        comp_distribute_first(P,S,C1,T0,T1),
        comp_distribute(RR,S,C2,T1,T),
        append(C1,C2,C).

comp_distribute_first(P,S,C,T0,T2) :-
        var(S),var(P),!,
        C = [comp(P,S,T1),un(T0,T1,T2)].
comp_distribute_first(P,S,C,T0,T2) :-
        var(S),!,
        C = [comp({} with P,S,T1),un(T0,T1,T2)].
comp_distribute_first(_P,{},[],T,T) :- !.
comp_distribute_first(P1,SR with P2,C,T0,T) :-
        var(P1),!,
        C = [comp(P1,{} with P2,T1),un(T0,T1,T2) | CR],
        comp_distribute_first(P1,SR,CR,T2,T).
comp_distribute_first(P1,SR with P2,C,T0,T) :-
        C = [comp({} with P1,{} with P2,T1),un(T0,T1,T2) | CR],
        comp_distribute_first(P1,SR,CR,T2,T).
         

%%%%%%%%%%%%%%%%%%%%%% domain of partial function (dompf/2) 

sat_dompf([dompf(X,Y)|R1],R2,c,F):-                   % dom(X,X)
        var(X),var(Y),X==Y,!, X = {},                          
        sat_step(R1,R2,_,F).
sat_dompf([dompf(S,D)|R1],[dompf(S,D)|R2],Stop,F):-   % dom(S,D) (irreducible form) 
        var(S),var(D),!,            
        sat_step(R1,R2,Stop,F).
sat_dompf([dompf(S,D)|R1],R2,c,F):-                   % dom({},d) or dom(int(a,b),d) with a>b
        nonvar(S),is_empty(S),!, 
        sunify(D,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).                         
sat_dompf([dompf(S,D)|R1],R2,c,F):-                   % dom(s,{}) or dom(s,int(a,b)) with a>b
        nonvar(D),is_empty(D),!, 
        sunify(S,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).                      
sat_dompf([dompf(S,D)|R1],R2,c,F):-                   % dom({[...],...},D) or dom({[...],...},{...}) or dom({[...],...},int(t1,t2))      
        nonvar(S), S = SR with [A1,_A2], !,
        sunify(D,DR with A1,C),
        append(C,R1,R3),
        sat_step([dompf(SR,DR)|R3],R2,_,F).                      
sat_dompf([dompf(S,D)|R1],R2,c,F):-                   % dom(S,int(a,a)), var(S)
        var(S), nonvar(D), is_int(D,A,B), A==B,!,
        S = {} with [A,_],
        sat_step(R1,R2,_,F).                         
sat_dompf([dompf(S,D)|R1],R2,c,F):-                   % dom(S,int(a,b)), var(S)
        var(S), nonvar(D), is_int(D,A,B), A<B,!,
        S = SR with [A,_],
        A1 is A + 1,
        sat_step([dompf(SR,int(A1,B))|R1],R2,_,F).                           
sat_dompf([dompf(S,D)|R1],R2,c,F):-                   % dom(S,{...}) or dom(S,int(A,B)), var(S)
        var(S), nonvar(D),
        sunify(D,DR with A1,C),!,
        S = SR with [A1,_A2],
        append(C,R1,R3),
        sat_step([dompf(SR,DR)|R3],R2,_,F).  
%        sat_step([A1 nin DR,dompf(SR,DR)|R3],R2,_,F). 


%%%%%%%%%%%%%%%%%%%%%% composition of partial functions (comppf/3) 

sat_comppf([comppf(R,_S,T)|R1],R2,c,F):-         % comppf({},s,t) or comppf(int(a,b),s,t) with a>b
        nonvar(R),is_empty(R),!, 
        sunify(T,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).                         
sat_comppf([comppf(_R,S,T)|R1],R2,c,F):-         % comppf(r,{},t) or comppf(r,int(a,b),t) with a>b
        nonvar(S),is_empty(S),!, 
        sunify(T,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).    
sat_comppf([comppf(R,S,T)|R1],R2,c,F):-          % comppf(r,s,{}) or comppf(r,s,int(a,b)) with a>b
        nonvar(T),is_empty(T),!, 
        sat_step([ran(R,RR),dompf(S,DS),disj(RR,DS)|R1],R2,_,F).                         
sat_comppf([comppf(R,S,T)|R1],[comppf(R,S,T)|R2],Stop,F):-  
        var(R),var(T),!,                         % comppf(R,s,T), s not empty set,                        
        sat_step(R1,R2,Stop,F).                  % irreducible forms                        
sat_comppf([comppf(R,S,T)|R1],R2,c,F):-          % comppf(r,s,{[X,Y],...})      
        nonvar(T), T = _ with [X,Y], !,
        sunify(T,RT with [X,Y],C0),              
        sunify(R,RR with [X,Z],C1),
        sunify(S,RS with [Z,Y],C2),
        append(C0,C1,C01),
        append(C01,C2,C012),
        append(C012,R1,R3),
        sat_step([[X,Y] nin RT,[X,Z] nin RR,[Z,Y] nin RS,comppf(RR,S,RT)|R3],R2,_,F).                                              
sat_comppf([comppf(R,S,T)|R1],R2,c,F):-          % comppf({[X,Y],...},{...},t), t var.     
        R = RR with [X,Y],           % exists(Z,[Y,Z] in S)
        sunify(S,SR with [Y,Z],C),   
        T = TR with [X,Z],
        append(C,R1,R3),
        sat_step([[Y,Z] nin SR,comppf(RR,S,TR)|R3],R2,_,F). 
sat_comppf([comppf(R,S,T)|R1],R2,c,F):-          % comppf({[X,Y],...},{...},t), t var.      
        R = RR with [_X,Y],                      % forall(Z,[Y,Z] nin S)
        sat_step([dompf(S,DS),Y nin DS,comppf(RR,S,T)|R1],R2,_,F). 


%%%%%%%%%%%%%%%%%%%%%% domain restriction (dres/3)
                        
sat_dres([dres(A,R,S)|R1],R2,Stop,nf) :-             % dres(A,R,S), A,R,S variables: delayed
        var(A), var(R), var(S), !,
        sat_step([delay(dres(A,R,S),novar3(A,R,S)) | R1],R2,Stop,nf).   
sat_dres([dres(A,R,S)|R1],R2,c,F):-                 % dres(A,R,S)
        sat_step([un(S,T,R),set(T),dom(S,B),set(B),subset(B,A),dom(T,C),set(C),disj(A,C)|R1],R2,_,F).   

sat_drespf([drespf(A,R,S)|R1],R2,c,F):-             % drespf(A,R,S) -  only for partial functions
        sat_step([dom(R,DR),set(DR),inters(A,DR,I),subset(S,R),dom(S,I)|R1],R2,_,F).                          

novar3(A,_R,_S) :- nonvar(A),!.
novar3(_A,R,_S) :- nonvar(R),!.
novar3(_A,_R,S) :- nonvar(S).

%%%%%%%%%%%%%%%%%%%%%% range restriction (rres/3)

sat_rres([rres(B,R,S)|R1],R2,c,F):-               
        sat_step([un(S,T,R),ran(S,RS),ran(R,RR),inters(B,RR,RS),
                  ran(T,RT),disj(RS,RT)|R1],R2,_,F).  


%%%%%%%%%%%%%%%%%%%%%% domain anti-restriction (ndres/3)

sat_ndres([ndres(A,R,S)|R1],R2,Stop,nf) :-         %  ndres(A,R,S), A,R,S variables: delayed
        var(A), var(R), var(S), !,
        sat_step([delay(ndres(A,R,S),novar3(A,R,S)) | R1],R2,Stop,nf).                         
sat_ndres([ndres(A,R,S)|R1],R2,c,F) :-             % ndres(A,R,S)
        sat_step([dres(A,R,B),
                  subset(S,R),un(B,S,D),subset(R,D),disj(B,S)    % diff(R,B,S)
                 |R1],R2,_,F).                         


%%%%%%%%%%%%%%%%%%%%%% range anti-restriction (nrres/3)

sat_nrres([nrres(A,R,S)|R1],R2,c,F):-            % nrres(A,R,S)
        sat_step([rres(A,R,B),
                 subset(S,R),un(B,S,D),subset(R,D),disj(B,S)    % diff(R,B,S)
                 |R1],R2,_,F).   


%%%%%%%%%%%%%%%%%%%%%% partial function application (apply/3)

sat_apply([apply(S,X,Y)|R1],R2,c,F):-            % apply(F,X,Y)
        sat_step([[X,Y] in S|R1],R2,_,F).                         


%%%%%%%%%%%%%%%%%%%%%% not partial function (npfun/1)

sat_npfun([npfun(X)|R1],R2,c,F):-                % npfun(X)
        (sat_step([set(X), [N1,N2] in X, [N1,N3] in X, N2 neq N3 |R1],R2,_,F)
         ;
         sat_step([nrel(X) |R1],R2,_,F)
        ).   

%%%%%%%%%%%%%%%%%%%%%% not binary relation (nrel/1)

sat_nrel([nrel(X)|R1],R2,c,F):-                  % nrel(X)
        sat_step([set(X), N in X, npair(N) |R1],R2,_,F).  


%%%%%%%%%%%%%%%%%%%%%% not pair (npair/1)

sat_npair([npair(X)|R1],[npair(X)|R2],Stop,F):-  % npair(X), var(X), (irreducible form)
        var(X),!,
        sat_step(R1,R2,Stop,F).
sat_npair([npair(X)|R1],R2,c,F):-                % npair(f(a,b)) 
        functor(X,Funct,Arity),
        (Funct \== '[|]',! ; Arity \== 2),!,
        sat_step(R1,R2,_,F).
sat_npair([npair(X)|R1],R2,c,F):-                % npair([a]) or npair([a,b,c,...])
        functor(X,'[|]',2), 
        length(X,M), M \== 2,
        sat_step(R1,R2,_,F).


%%%%%%%%%%%%
%%%%%%%%%%%% Rewriting rules for control constraints %%%%%%%%%%%%
%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%% delay mechanism               

sat_delay([delay(irreducible(A) & true,G)|R1],R2,c,f) :- 
        final,
        solve_goal(G,C1),!,
        solve_goal(A,C2),
        append(C1,C2,C3),
        append(C3,R1,R3),
        sat_step(R3,R2,_,f).
sat_delay([delay(irreducible(A) & true,G)|R1],[delay(irreducible(A) & true,G)|R2],Stop,f) :- 
        final, !,
        sat_step(R1,R2,Stop,f).

sat_delay([delay(A,_G)|R1],R2,c,f) :- 
        final, !,
        solve_goal_nodel(A,C2),
        append(C2,R1,R3),
        sat_step(R3,R2,_,f).

sat_delay([delay(A,G)|R1],R2,c,F) :- 
        solve_goal(G,C1),!,
        sat_delay_atom(A,A1),    
        solve_goal(A1,C2),
        append(C1,C2,C3),
        append(C3,R1,R3),
        sat_step(R3,R2,_,F).
sat_delay([X|R1],[X|R2],Stop,F):-
        sat_step(R1,R2,Stop,F).

sat_delay_atom(irreducible(A) & true,A) :- !.
sat_delay_atom(A,A).


%%%Solve goal G without generating any new delay
solve_goal_nodel(G,ClistNew) :-
       constrlist(G,GClist,GAlist),
       solve_goal_nodel(GClist,GAlist,ClistNew). 

solve_goal_nodel(Clist,[],CListCan):- !, 
       sat(Clist,CListCan,f). 
solve_goal_nodel(Clist,[true],CListCan):- !, 
       sat(Clist,CListCan,f). 
solve_goal_nodel(Clist,[A|B],CListOut):-
       sat(Clist,ClistSolved,f),
       sat_or_solve(A,ClistSolved,ClistNew,AlistCl,f),
       append(AlistCl,B,AlistNew),
       solve_goal_nodel(ClistNew,AlistNew,CListOut).


%%%%%%%%%%%%%%%%%%%%%%% solved mechanism              

% solved(C,G,Lev,Mode): constraint C is considered solved (i.e. not 
% further processed) at solver level Lev, while goal G is true;
% in final mode, if Mode is 'nf', the constraint C is anyway
% considered no longer solved

sat_solved([solved(C,G,Lev,Mode)|R1],R2,R,F):-
       call(G),!, 
       test_final([solved(C,G,Lev,Mode)|R1],R2,R,F).
sat_solved([solved(C,_,_,_)|R1],R2,c,F):-     
       sat_step([C|R1],R2,_,F).

test_final([solved(C,G,Lev,Mode)|R1],[solved(C,G,Lev,Mode)|R2],Stop,nf) :- !,
       sat_step(R1,R2,Stop,nf).
test_final([solved(C,G,Lev,Mode)|R1],[solved(C,G,Lev,Mode)|R2],Stop,f) :- 
       Mode == f,!,                            % final sat: G is true and in final mode
       sat_step(R1,R2,Stop,f).                 %  --> mantain solved
test_final([solved(C,_,_,_)|R1],R2,c,f) :-     % final sat: G is true and not in final mode
       sat_step([C|R1],R2,_,f).                %  --> remove solved

      
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%      Level 2     %%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%  Check pairs of constraints   %%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
     
global_check([],_,[],_) :- !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%% type clashes

global_check([C|RC],GC,[C|NewC],F) :-   % type clashes --> fail  
    type_constr(C),!,
    \+type_err(C,RC),   
    global_check(RC,GC,NewC,F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%% neq elimination
%%%%%%%%%%%%%%%%%%%%%%%%%%%% (X neq t and X a set variable) (only in final mode)

global_check([C|RC],GC,NewC,f) :-       % neq: W neq T and W or T set variables 
    is_neq(C,1,W,T),
    var(W), var(T),
    find_setconstraint(W,T,GC,X,Y),!,
    trace_irules('setvar-neq_var'),
    mk_new_constr(X,Y,OutC),
    append(OutC,CC,NewC),
    global_check(RC,GC,CC,f).
global_check([C|RC],GC,NewC,f) :-       % neq: W neq {...} and W a set variable
    is_neq(C,1,W,T),
    var(W), is_set(T),
    find_setconstraint(W,GC),!,
    trace_irules('setvar-neq_set'),
    mk_new_constr2(W,T,OutC),
    append(OutC,CC,NewC),
    global_check(RC,GC,CC,f).

%%%%%%%%%%%%%%%%%%%%%%%%%%%% inference rules

global_check([C|RC],GC,[C|NewC],F) :-   % suppress inference rules
    noirules,!,
    global_check(RC,GC,NewC,F).

global_check([C|RC],GC,NewC,F) :-       % dom-dom: dom(X,N) & dom(X,M) --> dom(X,M) & N=M
    is_dom_l(C,_,X,N,_),
    var(X),
    find_dom(X,RC,M),!,
    trace_irules('dom-dom'),
    N = M,
    global_check(RC,GC,NewC,F).

global_check([C|RC],GC,NewC,F) :-       % ran-ran: ran(X,N) & ran(X,M) --> ran(X,M) & N=M
    is_ran_l(C,_,X,N),
    var(X),
    find_ran(X,RC,M),!,
    trace_irules('ran-ran'),
    sunify(N,M,CEq),
    append(CEq,NewC1,NewC),
    global_check(RC,GC,NewC1,F).

global_check([C|RC],GC,NewC,F) :-       % un-un: un(X,Y,Z1) & un(Y,X,Z2) --> un(X,Y,Z1) & Z1 = Z2
    is_un_l(C,_,X,Y,Z1),
    var(X),var(Y),var(Z1),
    find_un2(X,Y,RC,Z2), !,
    trace_irules('un-un'),
    sunify(Z1,Z2,CEq),
    append(CEq,NewC1,NewC),
    global_check(RC,GC,NewC1,F).

global_check([C|RC],GC,NewC,F) :-       % size-size: size(S,N) & size(S,M) ---> size(S,M) & N=M
    is_size(C,1,X,N), 
    var(X),                                              
    find_size(X,RC,M),!,
    trace_irules('size-size'),
    N = M,
    global_check(RC,GC,NewC,F).

global_check([C|RC],GC,NewC,F) :-       % min-min: min(S,N) & min(S,M) ---> min(S,M) & N=M
    is_min(C,1,X,N),                   
    var(X), 
    find_min(X,RC,M),!,
    trace_irules('min-min'),
    N = M,
    global_check(RC,GC,NewC,F).

global_check([C|RC],GC,NewC,F) :-       % max-max: max(S,N) & max(S,M) ---> max(S,M) & N=M
    is_max(C,1,X,N),                 
    var(X),                        
    find_max(X,RC,M),!,
    trace_irules('max-max'),
    N = M,
    global_check(RC,GC,NewC,F).

global_check([C|RC],GC,NewC,F) :-       % sum-sum: sum(S,N) & sum(S,M) ---> sum(S,M) & N=M
    is_sum(C,1,X,N),
    var(X),
    find_sum(X,RC,M),!,
    trace_irules('sum-sum'),
    N = M,
    global_check(RC,GC,NewC,F).

                                        % dom-neq: dom(S,D) & D neq {} --> dom(S,D) & D neq {} & S neq {}
global_check([C|RC],GC,AddedC,F) :-    
    is_dom_l(C,L,S,D,RorF), 
    var(S),var(D),\+member(1,L),           
    find_neq(D,GC),!,   
    trace_irules('dom-neq_dom'),
    add_dom_neq(RorF,S,D,AddedC,L,NewC),
    global_check(RC,GC,NewC,F).
                                        % dom-neq: dom(S,D) & S neq {} --> dom(S,D) & D neq {} & S neq {}
global_check([C|RC],GC,AddedC,F) :-    
    is_dom_l(C,L,S,D,RorF), 
    var(S),var(D),\+member(1,L),           
    find_neq(S,GC),!,    
    trace_irules('dom-neq_rel'),
    add_dom_neqd(RorF,S,D,AddedC,L,NewC),
    global_check(RC,GC,NewC,F).
                                        % ran-neq: ran(S,D) & D neq {} --> ran(S,D) & D neq {} & S neq {}
global_check([C|RC],GC,[solved(ran(S,D),(var(S),var(D)),[1|L],f),S neq {}|NewC],F) :-    
    is_ran_l(C,L,S,D), 
    var(S),var(D),\+member(1,L),
    find_neq(D,GC),!,          
    trace_irules('ran_var-neq_ran'),
    global_check(RC,GC,NewC,F).
                                        % ran-neq: ran(S,{...}) --> ran(S,{...}) & S neq {}
global_check([C|RC],GC,[solved(ran(S,D),var(S),[],f),S neq {}|NewC],F) :-   
    C = ran(S,D),
    var(S), nonvar(D), noran_elim,!,          
    trace_irules('ran_nonvar-neq_ran'),
    global_check(RC,GC,NewC,F).
                                        % ran-neq: ran(S,D) & S neq {} --> ran(S,D) & D neq {} & S neq {}
global_check([C|RC],GC,[solved(ran(S,D),var(S),[1|L],f),D neq {}|NewC],F) :-    
    is_ran_l(C,L,S,D), 
    var(S),var(D),\+member(1,L),           
    find_neq(S,GC),!,    
    trace_irules('ran-neq_rel'),
    global_check(RC,GC,NewC,F).
                                        % un-size:  e.g., un(X,Y,Z) & size(Z,N) -+-> 
                                        %                 size(X,NX) & size(Y,NY) & size(Z,NZ) & 
                                        %                 NX =< NZ & NY =< NZ &NX + NY >= NZ
global_check([C|RC],GC,[solved(un(X,Y,Z),(var(X),var(Y),var(Z)),[1|L],f),   
                        size(X,NX),size(Y,NY),size(Z,NZ),
                        integer(NX),integer(NY),integer(NZ)|NewC],F) :-    
    is_un_l(C,L,X,Y,Z),                  
    var(X), var(Y), var(Z),            
    \+member(1,L), find_size3(X,Y,Z,GC,_),!,
    trace_irules('un-size'),
    solve_FD(NX =< NZ),
    solve_FD(NY =< NZ),
    solve_FD(NX + NY >= NZ),
    global_check(RC,GC,NewC,F).

                                         % dompf-size: e.g., dompf(S,D) & size(S,N) -+-> size(D,N)
global_check([C|RC],GC,[solved(dompf(S,D),(var(S),var(D)),[2|L],f),   
                        size(S,N),size(D,N),integer(N)|NewC],F) :-    
    is_dom_l(C,L,S,D,pfun),  
    var(S),var(D),\+member(2,L),          
    find_size2(S,D,GC,N),!,
    trace_irules('dom-size'),
    global_check(RC,GC,NewC,F).

                                         % ran-size: e.g., ran(S,R) & size(S,N) -+-> size(R,M) & M =< N
global_check([C|RC],GC,AddedC,F) :-    
    is_ran_l(C,L,S,R),
    var(S),var(R),\+member(2,L),            
    find_size2(S,R,GC,_),!,
    trace_irules('ran-size'),
    solve_FD(M =< N),
    add_ran_size(S,R,M,N,AddedC,L,NewC),
    global_check(RC,GC,NewC,F).

                                         % in-nin: T in X & T1 nin X (X is a list) --> T neq T1
global_check([solved(T in X,G,3,f)|RC],GC,                        
             [solved(T in X,G,2,f),T neq T1|NewC],F) :- % called only after executing level 3 rules
    find_nin(X,GC,T1),!,                                                   
    global_check(RC,GC,NewC,F). 

                                         % int-not empty: int(A,B)={} & int(A,B) neq {} (A,B var) --> fail 
global_check([T1 = T2|RC],GC,[T1 = T2|NewC],F) :-   
    nonvar(T1), T1 = int(A,B), nonvar(T2), is_empty(T2), !,
    \+find_neq(int(A,B),GC),
    global_check(RC,GC,NewC,F).

                                         % un-rel/pfun: un(X,Y,Z) & rel(Z)/pfun(Z) --> ...
global_check([C|RC],GC,AddedC,f) :-    
    is_un_l(C,L,X,Y,Z), 
    var(X), var(Y), var(Z),            
    \+member(2,L), find_rel_pfun(Z,GC,RorF),   
    !,
    trace_irules('un-pfun-dom'),
    add_dom_un(RorF,X,Y,Z,AddedC,L,NewC),
    global_check(RC,GC,NewC,f).
                                         % un-rel/pfun: un(X,Y,Z) & rel(Z)/pfun(Z) --> ...
global_check([C|RC],GC,AddedC,f) :-    
   is_un_l(C,L,X,Y,Z),                  
   var(X), var(Y), var(Z),            
   \+member(3,L), find_rel_pfun(Z,GC,RorF),    
   !,
   trace_irules('un-pfun-ran'),
   add_ran_un(RorF,X,Y,Z,AddedC,L,NewC),
   global_check(RC,GC,NewC,f).

 
%%%%%%%%%%%%%%%%%%%%%%%%%%%% all other constraints - nothing to do

global_check([C|RC],GC,[C|NewC],F) :-
    global_check(RC,GC,NewC,F).


%%%%%%%%%%%%%%%%%%%%%%%%%%%% auxiliary predicates for global_check/3

is_un(un(X,Y,Z),_,X,Y,Z) :- !.              
is_un(solved(un(X,Y,Z),_,Lev,_),Lev,X,Y,Z).              
is_un_l(un(X,Y,Z),[],X,Y,Z) :- !.                            
is_un_l(solved(un(X,Y,Z),_,L,_),L,X,Y,Z).              

is_size(size(X,N),_,X,N) :- !.   
is_size(solved(size(X,N),_,Lev,_),Lev,X,N) :- !.   
is_size(delay( (size(X,N) & true), _),_,X,N).   
%is_size(delay( (irreducible(size(X,N)) & true), _),_,X,N) :- 

is_sum(sum(X,N),_,X,N) :- !.     
is_sum(solved(sum(X,N),_,Lev,_),Lev,X,N).     

is_min(smin(X,N),_,X,N) :- !.          
is_min(solved(smin(X,N),_,Lev,_),Lev,X,N).     

is_max(smax(X,N),_,X,N) :- !.          
is_max(solved(smax(X,N),_,Lev,_),Lev,X,N).     

is_neq(X neq Y,_,X,Y) :- !.            
is_neq(solved(X neq Y,_,Lev,_),Lev,X,Y).          

is_nin(X nin Y,_,X,Y) :- !.          
is_nin(solved(X nin Y,_,Lev,_),Lev,X,Y).          

is_dom_l(dom(X,N),[],X,N,rel) :- !.     
is_dom_l(solved(dom(X,N),_,L,_),L,X,N,rel) :- !.
is_dom_l(dompf(X,N),[],X,N,pfun) :- !.     
is_dom_l(solved(dompf(X,N),_,L,_),L,X,N,pfun).

is_ran_l(ran(X,N),[],X,N) :- !.         
is_ran_l(solved(ran(X,N),_,L,_),L,X,N).
    
is_comp(comp(X,Y,Z),_,X,Y,Z) :- !.                                  
is_comp(solved(comp(X,Y,Z),_,Lev,_),Lev,X,Y,Z) :- !.                            
is_comp(comppf(X,Y,Z),_,X,Y,Z) :- !.                
is_comp(solved(comppf(X,Y,Z),_,Lev,_),Lev,X,Y,Z).                            
 
is_rel(rel(X),_,X) :- !.     
is_rel(solved(rel(X),_,Lev,_),Lev,X). 

is_pfun(pfun(X),_,X) :- !.     
is_pfun(solved(pfun(X),_,Lev,_),Lev,X). 

has_ris(RIS = E,_,D) :- 
      nonvar(RIS), is_ris(RIS,ris(_,D,_,_,_)),  
      var(D), nonvar(E), is_empty(E),!.             
has_ris(_ nin RIS,_,D) :- 
      nonvar(RIS), is_ris(RIS,ris(_,D,_,_,_)),  
      var(D),!.             
has_ris2(RIS1 = RIS2,_,D1,D2) :- 
      nonvar(RIS1), is_ris(RIS1,ris(_,D1,_,_,_)), var(D1), 
      nonvar(RIS2), is_ris(RIS2,ris(_,D2,_,_,_)), var(D2),!.             

%%%%%% searching constraints in the entire CS

find_neq(Int,cs([I neq E|_],_)) :-             
       nonvar(E), is_empty(E), I == Int,!.
find_neq(Int,cs([_|R],Others)) :- 
       find_neq(Int,cs(R,Others)).

find_setconstraint(X,cs(_,[C|_])) :-                    
       is_un_l(C,_,S1,S2,S3),                % un(X,_Y,_Z) or un(_Y,X,_Z) or un(_Y,_Z,X) is in the CS
       var(S1), var(S2), var(S3),
       (X == S1,! ; X == S2,! ; X == S3),!.
find_setconstraint(X,cs(Neqs,[_|R])) :-      % suppress neq elimination
       noneq_elim,!,
       find_setconstraint(X,cs(Neqs,R)).
find_setconstraint(X,cs(_,[C|_])) :-                    
       is_dom_l(C,_,S1,S2,_),                % dom(X,_Y) or dom(_Y,X) is in the CS
       var(S1), var(S2),
       (X == S1,! ; X == S2),!.
find_setconstraint(X,cs(_,[C|_])) :-                    
       is_ran_l(C,_,S1,S2),                  % ran(X,_Y) or ran(_Y,X) is in the CS
       var(S1), var(S2),
       (X == S1,! ; X == S2),!.
find_setconstraint(X,cs(_,[C|_])) :-                    
       is_comp(C,_,S1,S2,S3),                % comp(X,_Y,_Z) or comp(_Y,X,_Z) or comp(_Y,_Z,X) is in the CS
       var(S3),
       (X == S1,! ; X == S2,! ; X == S3),!.
find_setconstraint(X,cs(_,[C|_])) :-                    
       has_ris(C,_,D),                       % ris(_,D,_,_,_) = {} or T neq ris(_,D,_,_,_), D var., is in the CS 
       X == D,!.
find_setconstraint(X,cs(_,[C|_])) :-                    
       has_ris2(C,_,D1,D2),                  % ris(_,D1,_,_,_) = ris(_,D2,_,_,_), D1, D2 var., is in the CS 
       (X == D1,! ; X == D2),!.
find_setconstraint(X,cs(Neqs,[_|R])) :- 
       find_setconstraint(X,cs(Neqs,R)).

find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-     
       is_un(C,_,S1,S2,S3),                  % un(X,Y,Z) or un(Y,X,Z) or un(Y,Z,X) is in the CS?
       var(S1), var(S2), var(S3),
       one_of3(X,Y,S1,S2,S3,Z1,Z2),!.
find_setconstraint(X,Y,cs(Neqs,[_|R]),Z1,Z2) :-  % suppress neq elimination
       noneq_elim,!,
       find_setconstraint(X,Y,cs(Neqs,R),Z1,Z2).
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-     
       is_dom_l(C,_,S1,S2,_),                % dom(X,Y) or dompf(Y,X) is in the CS?
       var(S1), var(S2),
       one_of2(X,Y,S1,S2,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-     
       is_ran_l(C,_,S1,S2),                  % ran(X,Y) or ran(Y,X) is in the CS?
       var(S1), var(S2),
       one_of2(X,Y,S1,S2,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-     
       is_comp(C,_,S1,S2,S3),                % comp(X,Y,Z) or comp(Y,X,Z) or comp(Y,Z,X) is in the CS?
       var(S3),
       one_of3(X,Y,S1,S2,S3,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-     
       has_ris(C,_,D),                       % ris(_,D,_,_,_) = {} or T neq ris(_,D,_,_,_), D var., is in the CS  
       one_of1(X,Y,D,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-     
       has_ris2(C,_,D1,D2),                  % ris(_,D1,_,_,_) = ris(_,D2,_,_,_), D1, D2 var., is in the CS  
       one_of2(X,Y,D1,D2,Z1,Z2),!.

find_setconstraint(X,Y,cs(Neqs,[_|R]),Z1,Z2) :- 
       find_setconstraint(X,Y,cs(Neqs,R),Z1,Z2).

one_of3(X,Y,S1,_,_,X,Y) :- X == S1,!.
one_of3(X,Y,_,S2,_,X,Y) :- X == S2,!.
one_of3(X,Y,_,_,S3,X,Y) :- X == S3,!.
one_of3(X,Y,S1,_,_,Y,X) :- Y == S1,!.
one_of3(X,Y,_,S2,_,Y,X) :- Y == S2,!.
one_of3(X,Y,_,_,S3,Y,X) :- Y == S3.

one_of2(X,Y,S1,_,X,Y) :- X == S1,!.
one_of2(X,Y,_,S2,X,Y) :- X == S2,!.
one_of2(X,Y,S1,_,Y,X) :- Y == S1,!.
one_of2(X,Y,_,S2,Y,X) :- Y == S2.

one_of1(X,Y,S1,X,Y) :- X == S1,!.
one_of1(X,Y,S1,Y,X) :- Y == S1.

find_nin(X,cs(_,[C|_]),T) :-        % T nin X is in the CS
       is_nin(C,_,T,Y),     
       X == Y,!.
find_nin(X,cs(Neqs,[_|R]),T) :-
       find_nin(X,cs(Neqs,R),T).

find_size2(X,Y,cs(_,[C|_]),N) :-    % size(X,N) or size(Y,N) is in the CS
       is_size(C,_,S,N),
       (X == S,! ; Y == S),!.
find_size2(X,Y,cs(Neqs,[_|R]),M) :- 
       find_size2(X,Y,cs(Neqs,R),M).

find_size3(X,Y,Z,cs(_,[C|_]),N) :-  % size(X,N) or size(Y,N) or size(Z,N) is in the CS
       is_size(C,_,S,N),
       (X == S,! ; Y == S,! ; Z == S),!.
find_size3(X,Y,Z,cs(Neqs,[_|R]),M) :- 
       find_size3(X,Y,Z,cs(Neqs,R),M).

find_rel(X,cs(_,[C|_])) :-          % rel(X) is in the CS  
       is_rel(C,_,Y),
       X == Y,!.
find_rel(X,cs(Neqs,[_|R])) :- 
       find_rel(X,cs(Neqs,R)).

find_pfun(X,cs(_,[C|_])) :-         % pfun(X) is in the CS  
       is_pfun(C,_,Y),
       X == Y,!.
find_pfun(X,cs(Neqs,[_|R])) :- 
       find_pfun(X,cs(Neqs,R)).

find_rel_pfun(X,CS,RorF) :-         % either rel(X) or pfun(X) is in the CS  
       (find_rel(X,CS),!, RorF=rel ; find_pfun(X,CS), RorF=pfun).

%%%%%% searching constraints in the rest of the CS

find_un2(X,Y,[C|_],S3) :-           % un(X,Y,_Z) or un(Y,X,_Z) is in the CS
       is_un_l(C,_,S1,S2,S3), 
       (X == S1, Y == S2,! ; X == S2, Y == S1),!.
find_un2(X,Y,[_|R],S3) :- 
       find_un2(X,Y,R,S3).

find_size(X,[C|_],N) :-             % size(X,N) is in the CS
       is_size(C,_,S,N),
       X == S,!.
find_size(X,[_|R],M) :- 
       find_size(X,R,M).

find_sum(X,[C|_],N) :-              % sum(X,N) is in the CS
       is_sum(C,_,S,N),
       X == S,!.
find_sum(X,[_|R],M) :- 
       find_sum(X,R,M).

find_min(X,[C|_],N) :-              % smin(X,N) is in the CS  
       is_min(C,_,S,N),
       X == S,!.
find_min(X,[_|R],M) :- 
       find_min(X,R,M).

find_max(X,[C|_],N) :-              % smax(X,N) is in the CS 
       is_max(C,_,S,N),
       X == S,!.
find_max(X,[_|R],M) :- 
       find_max(X,R,M).

find_dom(X,[C|_],N) :-              % dom(X,N) is in the CS  
       is_dom_l(C,_,S,N,_),
       X == S,!.
find_dom(X,[_|R],M) :- 
       find_dom(X,R,M).

find_ran(X,[C|_],N) :-              % ran(X,N) is in the CS  
       is_ran_l(C,_,S,N),
       X == S,!.
find_ran(X,[_|R],M) :- 
       find_ran(X,R,M).

%%%%%% type checking 

type_constr(C) :-
       (p_type_constr(C),! ; n_type_constr(C)).

p_type_constr(set(_)).                     % positive type constraints
p_type_constr(bag(_)).
p_type_constr(list(_)).
p_type_constr(integer(_)).  
p_type_constr(rel(_)).   
p_type_constr(pfun(_)).    

n_type_constr(ninteger(_)).                % negative type constraints

rel_constr(rel(_)) :- !.                   % rel or pfun constraints
rel_constr(pfun(_)) :- !.

type_err(set(X),[C|R]):-                   % set(S) & rel(S)/pfun(S): compatible; check other constraints in R
       rel_constr(C),!,
       type_err(set(X),R).
type_err(C,[set(_)|R]):-                   % rel(S)/pfun(S) & set(S): compatible; check other constraints in R
       rel_constr(C),!,
       type_err(C,R).
type_err(C1,[C2|R]):-                      % rel(S)/pfun(S) & rel(S)/pfun(S): compatible; check other constraints in R
       rel_constr(C1),
       rel_constr(C2),!,
       type_err(C1,R).

type_err(integer(X),[ninteger(Y)|_R]):-    % integer(X) & ninteger(X): not compatible
       X == Y, !.
type_err(ninteger(X),[integer(Y)|_R]):-    % ninteger(X) & integer(X): not compatible
       X == Y, !.
type_err(C,[B|_R]):-                       % (other) different type constraints for the same variable: not compatible
       p_type_constr(C), p_type_constr(B), 
       C =.. [F1,X], B =.. [F2,Y],
       X == Y, F1 \== F2,!.
type_err(A,[_|R]):-                        % compatible; check other constraints in R
       type_err(A,R).

%%%%%% replacing constraints neq

mk_new_constr(W,T,OutC):-
       W = M with N, OutC = [N nin T,set(M)].
mk_new_constr(W,T,OutC):-
       T = _M with N, OutC = [N nin W,set(T)].
mk_new_constr(W,T,OutC):-
       W = {}, OutC = [T neq {}].  

mk_new_constr2(W,T,OutC):-
       nonvar(T), is_empty(T),!,
       W = M with _N, OutC = [set(M)].

mk_new_constr2(W,T,OutC):-
       W = M with N, OutC = [N nin T,set(M)].
mk_new_constr2(W,T,OutC):-
       T = _M with N, OutC = [N nin W].

%%%%%% adding dom and ran for relations/partial functions

add_dom_un(rel,X,Y,Z,AddedC,L,NewC) :-
    AddedC = [solved(un(X,Y,Z),(var(X),var(Y),var(Z)),[2|L],f),   
                        rel(X),rel(Y),dom(X,DX),dom(Y,DY),dom(Z,DZ),
                        un(DX,DY,DZ)|NewC].
add_dom_un(pfun,X,Y,Z,AddedC,L,NewC) :-
    AddedC = [solved(un(X,Y,Z),(var(X),var(Y),var(Z)),[2|L],f),   
                        pfun(X),pfun(Y),dompf(X,DX),dompf(Y,DY),dompf(Z,DZ),
                        un(DX,DY,DZ)|NewC].

add_ran_un(rel,X,Y,Z,AddedC,L,NewC) :-
   AddedC = [solved(un(X,Y,Z),(var(X),var(Y),var(Z)),[3|L],f),   
                        rel(X),rel(Y),ran(X,RX),ran(Y,RY),ran(Z,RZ),
                        un(RX,RY,RZ)|NewC].
add_ran_un(pfun,X,Y,Z,AddedC,L,NewC) :-
   AddedC = [solved(un(X,Y,Z),(var(X),var(Y),var(Z)),[3|L],f),   
                        pfun(X),pfun(Y),ran(X,RX),ran(Y,RY),ran(Z,RZ),
                        un(RX,RY,RZ)|NewC].

add_dom_neq(rel,S,D,AddedC,L,NewC) :-
    AddedC = [solved(dom(S,D),(var(S),var(D)),[1|L],f),S neq {}|NewC].
add_dom_neq(pfun,S,D,AddedC,L,NewC) :-
    AddedC = [solved(dompf(S,D),(var(S),var(D)),[1|L],f),S neq {}|NewC].

add_dom_neqd(rel,S,D,AddedC,L,NewC) :-
    AddedC = [solved(dom(S,D),(var(S),var(D)),[1|L],f),D neq {}|NewC].
add_dom_neqd(pfun,S,D,AddedC,L,NewC) :-
    AddedC = [solved(dompf(S,D),(var(S),var(D)),[1|L],f),D neq {}|NewC].

add_ran_size(S,R,M,N,AddedC,L,NewC) :-
    noran_elim,!,
    AddedC = [solved(ran(S,R),(var(S),var(R);var(S),nonvar(R),\+(is_empty(R))),[2|L],f),   
               size(S,N),size(R,M),integer(N),integer(M)|NewC].
add_ran_size(S,R,M,N,AddedC,L,NewC) :-
    AddedC = [solved(ran(S,R),(var(S),var(R)),[2|L],f),   
               size(S,N),size(R,M),integer(N),integer(M)|NewC].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%           Level 3           %%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%  Labeling and final check   %%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 
final_sat(C,SFC):- 
      trace_in(C,3),
      final_sat1(C,SFC0), 
      final_sat2(SFC0,SFC),
      trace_out(SFC,3).  

final_sat1([],[]) :-!.
final_sat1(C,SFC):- 
      sat_empty_intv(C,CC),   
      check_domain(CC),                  %force labeling for integer variables;  
      sat(CC,RevC,f),                    %call the constraint solver (in 'final' mode); 
      final_sat_cont(RevC,CC,SFC).

final_sat_cont(RevC,C,RevC) :-
      RevC == C,!.
final_sat_cont(RevC,_C,SFC) :-           %RevC is the resulting constraint; 
      final_sat1(RevC,SFC).              %otherwise, call 'final_sat' again
 
final_sat2([],[]) :-!.
final_sat2(C,SFC):- 
      check_domain(C),                   %force labeling for integer variables;
      set_final, 
      sat(C,RevC,f),                     %call the constraint solver (in 'final' mode); 
      final_sat_cont2(RevC,C,SFC).

final_sat_cont2(RevC,C,RevC) :-
      RevC == C,!,
      retract_final.
final_sat_cont2(RevC,_C,SFC) :-          %RevC is the resulting constraint; 
      final_sat2(RevC,SFC).              %otherwise, call 'final_sat' again
 
check_domain(C):-                        %to force labeling (if possible) for integer         
      memberrest(integer(X),C,CRest),!,  %variables that are still uninstantiated in 
      labeling(X),                       %the constraint C 
      check_domain(CRest).
check_domain(_).
                      
sat_empty_intv([],[]) :- !.              
sat_empty_intv([T1 = T2|R1],[integer(A),integer(B)|R2]) :- 
      nonvar(T1), T1 = int(A,B), nonvar(T2), is_empty(T2),!,
      solve_FD(A > B),
      sat_empty_intv(R1,R2).
sat_empty_intv([T1 neq T2|R1],[integer(A),integer(B)|R2]) :- 
      nonvar(T1), T1 = int(A,B), nonvar(T2), is_empty(T2),!,
      solve_FD(A =< B),
      sat_empty_intv(R1,R2).
sat_empty_intv([C|R1],[C|R2]) :- 
      sat_empty_intv(R1,R2).

set_final :-             
        final,!.
set_final :-    
        assert(final).

retract_final :-
        retract(final),!.
retract_final.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     FD constraints 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

solve_FD(Constr) :-             % Solve the constraint 'Constr' using the FD solver
       tau(Constr,FD_Constr),
       call(FD_Constr).

fd_eq(X,E) :-
       X #= E.
       
tau(X is E,X #= E).             % The translation function: from SET constraints to FD
tau(X =< Y,X #=< Y).            % constraints, and vice versa
tau(X >= Y,X #>= Y).             
tau(X < Y,X #< Y).              
tau(X > Y,X #> Y).              
tau(X neq T,X #\= T).
tau(T in int(A,B),T in A..B) :- !.
tau(T in D,T in D).

labeling(_) :-                     % if nolabel, do nothing        
       nolabel,!.                     
labeling(X) :-                     % if the variable X has a closed domain associated 
       get_domain(X,X in D),!,     % with it, then X is (non-deterministically) instantiated 
       labeling1(X,D).             % to every value belonging to the domain.             
labeling(_).                       % Otherwise, the predicate is true and X remains unchanghed

is_fd_var(X) :-
       clpfd:fd_var(X).

get_domain(X,(X in D)) :-          % get_domain(X,FDc): true if X is a variable and 
       var(X),                     % FDc is the interval membership constraint for X
       clpfd:fd_dom(X,D).


labeling1(_X,inf.._B) :- !.        % e.g., X in inf..1  --> no labeling
labeling1(_X,_A..sup) :- !.        % e.g., X in 1..sup  --> no labeling
labeling1(X,(I) \/ (A..sup)) :-    % e.g., X in (inf..2)\/(4..5)\/(7..9)\/(11..sup)
        first_int(I,inf..B,J),!,   % --> labeling on the bounded part
       (X in J,
        clpfd:indomain(X)
        ;
        X in (inf..B)
        ;
        X in (A..sup)).
labeling1(X,(I) \/ (A..sup)) :- !, % e.g., X in (1..2)\/(4..5)\/(7..sup)
       (X in I,                    % --> labeling on the bounded part
        clpfd:indomain(X)
        ;
        X in (A..sup)).
labeling1(X,(I) \/ (In)) :-        % e.g., X in (inf..2)\/(4..5)\/(7..9)
        first_int(I,inf..B,J),!,   % --> labeling on the bounded part
       (X in (J) \/ (In),
        clpfd:indomain(X)
        ;
        X in (inf..B)).
labeling1(X,_D) :-                 % e.g., X in (1..2)\/(4..5)\/(7..9)
        clpfd:indomain(X).  
%DBG%   clpfd:labeling([ff,down,enum],[X]).


first_int((A .. B),(A .. B),(1 .. 0)) :- !.      % first_int(+Int,?Rest,?First) 
first_int((I) \/ (In),I0,(IRest) \/ (In)) :-     % 'Int' is a disj. of intervals and
       first_int(I,I0,IRest).                    % 'First' is the first disjunct
                                                 % 'Rest' the remaining part

%%%%%%%%%%%%%%

%add_FDc(SETc,SETFDc,R)       
%SETFDc is the list of contraints obtained by appending the list FDc
%of interval constraints still occurring in the FD constraint store
%to the list of constraints SETc. R is either 'y' if at least one 
%such interval constraints is found; otherwise, R is uninitialized

add_FDc([],[],_) :- !.                                          
add_FDc([C|SETc],[C|FDc],Warning) :-  
       \+(C = integer(_)),!,
       add_FDc(SETc,FDc,Warning).                                           
add_FDc([integer(X)|SETc],[integer(X)|FDc],Warning) :-  
       \+is_fd_var(X),!,
       add_FDc(SETc,FDc,Warning).  
add_FDc([integer(X)|SETc],FDc,Warning) :-  
       get_domain(X,FD),
       tau(X in D,FD), 
       (nolabel,! ; Warning = y),
       (D == int(inf,sup),!,FDc = [integer(X)|FDcCont]
        ;
        FDc = [(X in D)|FDcCont]
       ),
       add_FDc(SETc,FDcCont,Warning).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     Program defined constraints 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

isetlog((true :- true),sys).
isetlog((less(A,X,C) :- 
         A = C with X & set(C) & X nin C & true),sys).
isetlog((nsubset(A,B) :- 
         set(A) & set(B) & X in A & X nin B & true),sys).
isetlog((ninters(A,B,C) :- 
         set(A) & set(B) & set(C) & X in C &
         (X nin A & true or X nin B & true) & true),sys).
isetlog((diff(A,B,C) :- 
         set(A) & set(B) & set(C) &
         subset(C,A) & un(B,C,D) & subset(A,D) & disj(B,C) & true),sys).
isetlog((ndiff(A,B,C) :- 
         set(A) & set(B) & set(C) &
         diff(A,B,D) & D neq C & true),sys).
isetlog((sdiff(A,B,C) :- 
         set(A) & set(B) & set(C) &
         diff(A,B,D) & diff(B,A,E) & un(D,E,C) & true),sys).

isetlog((A =:= B :- 
         X is A & Y is B & X = Y & true),sys).
isetlog((A =\= B :- 
         X is A & Y is B & X neq Y & true),sys).

isetlog((rimg(B,R,S) :-   
         set(B) & set(S) & rel(R) & dres(B,R,RB) & ran(RB,S) & true),sys).
isetlog((oplus(R,S,T) :-  
         rel(R) & rel(S) & rel(T) & un(RS,S,T) & ndres(DS,R,RS) & dom(S,DS) & true),sys).
isetlog((id(A,R) :-        % for partial functions only
         set(A) & pfun(R) & dompf(R,A) & ran(R,A) & comp(R,R,R) & true),sys).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%     Pre / post-processor     %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Exported predicates:
%
%             preproc_goal/2,
%             preproc/3,
%             postproc/2,
%             transform_goal/2,
%             transform_clause/2,
%             is_ker/1,
%             is_sf/3 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     Preprocessing 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%% Set (multiset) preprocessor: 
%%%%%%%%%%%%% from {...} (*({...})) to 'with' ('mwith') notation  

preproc_goal(G,PGext) :-
        preproc(G,PG,TypeCL), 
        norep_in_list(TypeCL,TypeCLRid),   
        list_to_conj(TypeCC,TypeCLRid),
        conj_append(PG,TypeCC,PGext).

preproc_clause(Cl,(PA :- PBext)) :-
        preproc(Cl,(PA :- PB),TypeCL), 
        norep_in_list(TypeCL,TypeCLRid),   
        list_to_conj(TypeCC,TypeCLRid),
        conj_append(PB,TypeCC,PBext).

preproc(X,X,[]):- 
        var(X),!.      
preproc(X,X,[]):-
        atomic(X),!.
preproc(X,Y1,C):-
        is_set_ext(X), !,
        set_preproc(X,Y,C),
        norep_in_set(Y,Y1). 
preproc(X,Y,C):-
        is_bag_ext(X),!,
        bag_preproc(X,Y,C).
preproc([A|X],[A1|X],[type(list(X))|C]):- 
        var(X), !,
        preproc(A,A1,C).
preproc((A & B),(A1 & B1),C):-
        !, preproc(A,A1,C1), preproc(B,B1,C2),
        append(C1,C2,C).
preproc((A :- B ),(A1 :- B1 ),C) :-
        !, preproc(A,A1,C1), preproc(B,B1,C2),
        append(C1,C2,C).

preproc(prolog_call(G),prolog_call(G),[]) :- !.    
preproc(naf A,naf(A1),[]) :-     
        !, preproc_goal(A,A1).
preproc(call(A),call(A1),[]) :-     
        !, preproc_goal(A,A1).
preproc(call(A,C),call(A1,C),[]) :-    
        !, preproc_goal(A,A1).
preproc(solve(A),solve(A1),[]) :-    
        !, preproc_goal(A,A1).
preproc((A)!,(A1)!,[]) :-        
        !, preproc_goal(A,A1).
preproc(delay(A,G),delay(A1,G),[]) :-    
        !, preproc_goal(A,A1).
preproc(neg A,neg(A1),[]) :-    
        !, preproc_goal(A,A1).

preproc(X,Z,C):-
        nonvar(X), 
        functor(X,F,_A), 
        =..(X,[F|ListX]),
        preproc_all(ListX,ListZ,C1),
        =..(Z,[F|ListZ]),
        (gen_type_constrs(Z,TypeC),!,
         append(C1,TypeC,C)
        ;
         C1 = C
        ).

preproc_all([],[],[]).
preproc_all([A|L1],[B|L2],C):-
        preproc(A,B,C1),
        preproc_all(L1,L2,C2),
        append(C1,C2,C).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% set preprocessing

set_preproc({},{},[]):- !.
set_preproc(X with A,X with B,[type(set(X))|Constrs]) :-
        var(X),!, preproc(A,B,Constrs).       
set_preproc(X with A,Y with B,Constrs) :-
        is_set_ext(X),!,
        preproc(A,B,Constrs1), preproc(X,Y,Constrs2),
        append(Constrs1,Constrs2,Constrs). 
set_preproc({}(A),B,Constrs):-
        set_preproc_elems(A,B,Constrs),!.
set_preproc(_,_,_):-
        msg_sort_error(set), 
        fail.

set_preproc_elems(A,{} with A,[]):-
        var(A), !.
set_preproc_elems((A1,B1),B2 with A2,Constrs):- !,
        preproc(A1,A2,Constrs1),
        set_preproc_elems(B1,B2,Constrs2),
        append(Constrs1,Constrs2,Constrs).
set_preproc_elems(S,WT,Constrs):- 
        aggr_comps_ext(S,_A,_X),!,
        set_preproc_set(S,WT,Constrs). 
set_preproc_elems(A1,{} with A2,Constrs):-
        preproc(A1,A2,Constrs).

set_preproc_set(S,X with B,[type(set(X))|Constrs]):-  
        aggr_comps_ext(S,A,X), 
        var(X),!, 
        preproc(A,B,Constrs).
set_preproc_set(S,Y with B,Constrs):-   
        aggr_comps_ext(S,A,X), 
        is_set_ext(X),!,
        preproc(A,B,Constrs1), preproc(X,Y,Constrs2),
        append(Constrs1,Constrs2,Constrs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% bag preprocessing

bag_preproc({},{},[]):-!.   
bag_preproc(X mwith A,X mwith B,[type(bag(X))|Constrs]) :-
        var(X),!, preproc(A,B,Constrs).       
bag_preproc(X mwith A,Y with B,Constrs) :-
        is_bag_ext(X),!,
        preproc(A,B,Constrs1), preproc(X,Y,Constrs2),
        append(Constrs1,Constrs2,Constrs). 
bag_preproc((*({}(A))),B,Constrs):- 
        bag_preproc_elems(A,B,Constrs),!.
bag_preproc(_,_,_):-
        msg_sort_error(bag), 
        fail. 

bag_preproc_elems(A, {} mwith A,[]):-
        var(A),!.
bag_preproc_elems((A1,B1),B2 mwith A2,Constrs):-
        !,preproc(A1,A2,Constrs1),
        bag_preproc_elems(B1,B2,Constrs2),
        append(Constrs1,Constrs2,Constrs).
bag_preproc_elems(M,MWT,Constrs):-         
        aggr_comps_ext(M,_A,_X),!,
        bag_preproc_bag(M,MWT,Constrs).    
bag_preproc_elems(A1,{} mwith A2,Constrs):-
        preproc(A1,A2,Constrs).

bag_preproc_bag(M,X mwith B,[type(bag(X))|Constrs]):-       
        aggr_comps_ext(M,A,X), var(X),!,
        preproc(A,B,Constrs).
bag_preproc_bag(M,Y mwith B,Constrs):-!,    
        aggr_comps_ext(M,A,X), is_bag_ext(X),!,
        preproc(A,B,Constrs1), preproc(X,Y,Constrs2),
        append(Constrs1,Constrs2,Constrs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% type constraints generation

gen_type_constrs(un(T1,T2,T3),[type(set(T1)),type(set(T2)),type(set(T3))]) :- !.
gen_type_constrs(nun(T1,T2,T3),[type(set(T1)),type(set(T2)),type(set(T3))]) :- !.
gen_type_constrs(disj(T1,T2),[type(set(T1)),type(set(T2))]) :- !.  
gen_type_constrs(ndisj(T1,T2),[type(set(T1)),type(set(T2))]) :- !.
gen_type_constrs(subset(T1,T2),[type(set(T1)),type(set(T2))]) :- !.
gen_type_constrs(ssubset(T1,T2),[type(set(T1)),type(set(T2))]) :- !.
gen_type_constrs(inters(T1,T2,T3),[type(set(T1)),type(set(T2)),type(set(T3))]) :- !.
gen_type_constrs(size(T1,T2),[type(set(T1)),type(integer(T2))]) :- !.   
gen_type_constrs(sum(T1,T2),[type(set(T1)),type(integer(T2))]) :- !.
gen_type_constrs(smin(T1,T2),[type(set(T1)),type(integer(T2))]) :- !.  
gen_type_constrs(smax(T1,T2),[type(set(T1)),type(integer(T2))]) :- !. 

gen_type_constrs(dom(T1,T2),[type(rel(T1)),type(set(T2))]) :- !.   
gen_type_constrs(inv(T1,T2),[type(rel(T1)),type(set(T2))]) :- !.   
gen_type_constrs(ran(T1,T2),[type(rel(T1)),type(set(T2))]) :- !.   
gen_type_constrs(comp(T1,T2,T3),[type(rel(T1)),type(rel(T2)),type(rel(T3))]) :- !. 
gen_type_constrs(dompf(T1,T2),[type(pfun(T1)),type(set(T2))]) :- !. 
gen_type_constrs(comppf(T1,T2,T3),[type(rel(T1)),type(pfun(T2)),type(rel(T3))]) :- !. 
gen_type_constrs(dres(T1,T2,T3),[type(set(T1)),type(rel(T2)),type(rel(T3))]) :- !. 
gen_type_constrs(drespf(T1,T2,T3),[type(set(T1)),type(rel(T2)),type(rel(T3))]) :- !. 
gen_type_constrs(rres(T1,T2,T3),[type(set(T1)),type(rel(T2)),type(rel(T3))]) :- !. 
gen_type_constrs(ndres(T1,T2,T3),[type(set(T1)),type(rel(T2)),type(rel(T3))]) :- !. 
gen_type_constrs(nrres(T1,T2,T3),[type(set(T1)),type(rel(T2)),type(rel(T3))]) :- !. 

gen_type_constrs(apply(F,_,_),[type(pfun(F))]) :-        % for partial functions only
      var(F),!.
gen_type_constrs(apply(F,_,_),[type(pfun(F))]) :-        
      nonvar(F), F \== this.

%%%%%%%%%%%%% Auxiliary predicates for set/multiset preprocessing

is_set_ext(X):- functor(X,{},_),!.
is_set_ext(_ with _).

is_bag_ext({}):-!.
is_bag_ext(X):- X = *A, functor(A,{},_), !.
is_bag_ext(_ mwith _).

aggr_comps_ext((A \ R),A,R) :-!. 
aggr_comps_ext((A / R),A,R).          %for compatibility with previous releases

is_ker(T) :-
        nonvar(T), functor(T,F,N),
        (F \== with,! ; N \== 2).

msg_sort_error(set) :- 
       write(' wrong set term '), nl.
msg_sort_error(bag) :- 
       write(' wrong multiset term '), nl.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%   Intensional set preprocessing        
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                            
sf_in_clause((H :- B),(H1 :- B1)):-
    !,sf_in_literal(H,[H1|List1]),
    sf_in_goal(B,List2),
    append(List1,List2,List),
    list_to_conj(B1,List).      
sf_in_clause(A,(H :- B)):-
    sf_in_hliteral(A,[H|List]),
    list_to_conj(B,List).

sf_in_goal(A,[A]):-
    var(A),!.    
sf_in_goal(true,[]):-!.                   
sf_in_goal(A & B,NewL):-    
    !, sf_in_literal(A,A1),
    sf_in_goal(B,B1),
    append(A1,B1,NewL).
sf_in_goal(A,NewL):-
    !, sf_in_literal(A,NewL).    

sf_in_literal(A,[A]):-                    
    var(A),!.
sf_in_literal(A or B,[A1 or B1]):-
    !, sf_in_goal(A,L1),
    sf_in_goal(B,L2),
    list_to_conj(A1,L1),
    list_to_conj(B1,L2).
sf_in_literal(prolog_call(A),[prolog_call(A)]):-!. 
sf_in_literal(neg A,[neg A1]):-
    !, sf_in_goal(A,L1),
    list_to_conj(A1,L1).
sf_in_literal(naf A,[naf A1]):-
    !, sf_in_goal(A,L1),
    list_to_conj(A1,L1).
sf_in_literal(call(A),[call(A1)]):-
    !, sf_in_goal(A,L1),
    list_to_conj(A1,L1).
sf_in_literal(call(A,C),[call(A1,C)]):-   
    !, sf_in_goal(A,L1),
    list_to_conj(A1,L1).
sf_in_literal(solve(A),[solve(A1)]):-
    !, sf_in_goal(A,L1),
    list_to_conj(A1,L1).
sf_in_literal(assert(Cl),[assert(Cl1)]):-
    !, sf_in_clause(Cl,Cl1).
sf_in_literal((A)!,[(A1)!]):-
    !, sf_in_goal(A,L1),
    list_to_conj(A1,L1).
sf_in_literal(delay(A,G),[delay(A1,G1)]):-
    !, sf_in_goal(A,L1),
    sf_in_goal(G,L2),
    list_to_conj(A1,L1),
    list_to_conj(G1,L2).
sf_in_literal(forall(X in S,exists(V,A)),L):-
    !, sf_find([S],[S1],L1),
    sf_in_goal(A,L2),
    list_to_conj(A1,L2),
    append(L1,[forall(X in S1,exists(V,A1))],L).
sf_in_literal(forall(X in S,A),L):-
    !, sf_find([S],[S1],L1),
    sf_in_goal(A,L2),
    list_to_conj(A1,L2),
    append(L1,[forall(X in S1,A1)],L).
sf_in_literal(A,NewA):-   
    A =.. [Pname|Args],
    sf_find(Args,Args1,NewL),
    B =.. [Pname|Args1],
    append(NewL,[B],NewA).
        
sf_in_hliteral(A,[B|NewL]):-                                      
    A =.. [Pname|Args],
    sf_find(Args,Args1,NewL),
    B =.. [Pname|Args1].
        
sf_find([],[],[]).
sf_find([Int|R],[Var|S],List):-
    is_sf(Int,X,G),!,
    extract_vars(G,Vars),
    remove_var(X,Vars,Finalvars),
    check_control_var1(Vars,Finalvars),
    sf_translate(Int,Var,L1,Finalvars),
    sf_find(R,S,L2),
    append(L1,L2,List).    
sf_find([A|R],[B|S],List):-
    nonvar(A),
    A =.. [Fname|Rest],
    Rest \== [],!,
    sf_find(Rest,Newrest,List1),
    B =.. [Fname|Newrest],
    sf_find(R,S,List2),
    append(List1,List2,List).
sf_find([A|R],[A|S],List):-
    sf_find(R,S,List).

check_control_var1(Vars,Finalvars) :-
    Vars == Finalvars, !,
    write('ERROR - Formula of a set former must'),
    write(' contain the set former control variable'), nl, 
    fail.
check_control_var1(_Vars,_Finalvars).

sf_translate(SF,Y,[Pred],Vars):-
    (SF={X:exists(_Var,Goal)},! ; SF={X : Goal}),
    length([_|Vars],N),    
    newpred(Aux,N,[115, 101, 116, 108, 111, 103, 83, 70, 95]),    % "setlogSF_"
    Aux=..[AuxName,Y|Vars],
    newpred(Aux1,N,[115, 101, 116, 108, 111, 103, 83, 70, 95]),   
    Aux1 =.. [Aux1Name,X|Vars],
    Pred = sf_call(Y,Aux1Name,AuxName,Vars),
    setassert((Aux1 :- Goal)),
    setassert((Aux :- X nin Y & Aux1)). 
        
is_sf(Int,X,Phi) :-
    nonvar(Int), Int = {SExpr}, 
    nonvar(SExpr), SExpr = (X : Phi),
    check_control_var2(X).

check_control_var2(X) :-
    nonvar(X), !,
    write('ERROR - Control variable in a set former'),
    write(' must be a variable term!'), nl,  
    fail.
check_control_var2(_X).
              

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%    R.U.Q. preprocessing  %%%%%%%%%%%           
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                      
ruq_in_clause((H :- B),(H :- NewB)) :-    
    ruq_in_goal(B,NewB,B,no),!.
ruq_in_clause(H,H).

ruq_in_goal(Goal,NewGoal) :-
    rewrite_goal(Goal,NewGoal).
%DBG%     write('***NEW GOAL:***'), write(NewGoal), nl.   % only for debugging

rewrite_goal(G,NewG) :-
    filter_on,!,
    normalize(G,G1),           
    ruq_in_goal(G1,G2,G1,infer_rules),    
    ruq_in_goal(G2,NewG,G2,fail_rules).    
rewrite_goal(G,NewG) :-
    ruq_in_goal(G,NewG,G,no).    

ruq_in_goal(A,A,_,_):-
    var(A),!.    
ruq_in_goal(A & B,GExt,G,RR):-
    !, ruq_in_goal(A,A1,G,RR), ruq_in_goal(B,B1,G,RR),
    conj_append(A1,B1,GExt).    
ruq_in_goal((A or B),((A1) or (B1)),_,RR):-
    !, ruq_in_goal(A,A1,A,RR), ruq_in_goal(B,B1,B,RR). 

ruq_in_goal(prolog_call(A),prolog_call(A),_,_):-!. 
ruq_in_goal(neg A,neg(A1),_,RR):-
    !, ruq_in_goal(A,A1,A,RR).    
ruq_in_goal(naf A,naf(A1),_,RR):-
    !, ruq_in_goal(A,A1,A,RR).    
ruq_in_goal(call(A),call(A1),_,no):-
    !, rewrite_goal(A,A1).
ruq_in_goal(call(A),call(A1),_,RR):-
    !, ruq_in_goal(A,A1,A,RR).
ruq_in_goal(call(A,C),call(A1,C),_,RR):-    
    !, ruq_in_goal(A,A1,A,RR).   
ruq_in_goal(solve(A),solve(A1),_,RR):-
    !, ruq_in_goal(A,A1,A,RR).    
ruq_in_goal((A)!,(A1)!,_,RR):-
    !, ruq_in_goal(A,A1,A,RR).    
ruq_in_goal(delay(A,G),delay(A1,G1),_,RR):-
    !, ruq_in_goal(A,A1,A,RR),
    ruq_in_goal(G,G1,G,RR).   
 
ruq_in_goal(forall(X in _S,_Y),_,_,_):- 
    nonvar(X), !, 
    write('ERROR - Control variable in a R.U.Q. must be a variable term!'), nl, 
    fail.
ruq_in_goal(forall(X in S,G),NewG,_,_):-
    !, extract_vars(G,V),
    remove_var(X,V,Vars),
    check_control_var_RUQ(V,Vars), 
    length(V,N),
    newpred(Gpred,N,[115, 101, 116, 108, 111, 103, 82, 85, 81, 95]),       %"setlogRUQ_"
    Gpred =.. [_,X|Vars],
    tmp_switch_ctxt(OldCtxt),
    ( G = exists(_Var,B),!, 
      setassert((Gpred :- B))     
     ;
      setassert((Gpred :- G)) ),  
    switch_ctxt(OldCtxt,_),
    functor(Gpred,F,N),
    NewG = ruq_call(S,F,Vars).

ruq_in_goal(true,true,_,_) :- !. 
ruq_in_goal(A,NewG,G,RR) :-      % try to call filtering rules
    RR \== no,
    user_def_rules(A,NewG,G,RR),!.
ruq_in_goal(A,A,_,_).
    %% N.B. no check for 'forall(X in {...,t[X],...})'
    %% add 'occur_check(X,S)' to enforce it

check_control_var_RUQ(Vars,Finalvars) :-
    Vars == Finalvars, !,
    write('ERROR - Formula of a R.U.Q. must'),
    write(' contain the R.U.Q. control variable'), nl, 
    fail.
check_control_var_RUQ(_Vars,_Finalvars).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%% User-defined rewriting rules %%%%%%%%%% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

load_rwrules_lib :-                           
    rw_rules(Lib),
    mk_file_name(Lib,FullName),
    (exists_file(FullName),!,consult(FullName) 
     ; 
     true).

normalize(Goal,NewGoal) :-   
    ruq_in_goal(Goal,NewGoal1,Goal,replace_rules),    
    (Goal == NewGoal1,!,NewGoal=NewGoal1
    ;
     normalize(NewGoal1,NewGoal)
    ).   

user_def_rules(A,NewC,G,replace_rules) :- !,
    replace_rule(_RuleName,C,C_Conds,D,D_Conds,AddC),       
    check_atom(C,A,R),
    list_call(C_Conds),
    conj_member_strong(D,D_Conds,G,[]),
    apply_equiv(R,AddC,NewC).                                 

user_def_rules(A,NewC,G,infer_rules) :- !,
    inference_rule(RuleName,C,C_Conds,D,D_Conds,E,AddC),  
    check_atom(C,A,_R),
    list_call(C_Conds),
    conj_member_strong(D,D_Conds,G,E),
    trace_firules(RuleName),
    conj_append(AddC,A,NewC). 
 
user_def_rules(A,NewC,G,fail_rules) :- !,
    fail_rule(RuleName,C,C_Conds,D,D_Conds,E),   
    check_atom(C,A,_R),
    list_call(C_Conds),
    conj_member_strong(D,D_Conds,G,E),
    trace_ffrules(RuleName),
    conj_append((a = b),A,NewC).

conj_member_strong([],_,_,_):- !.
conj_member_strong([T],D_Conds,G,E):-    
    conj_member_strong1(T,D_Conds,G,E),
    list_call(D_Conds),!.
conj_member_strong([T|R],D_Conds,G,E):- 
    R \== [],
    conj_member_strong1(T,D_Conds,G,E),
    conj_member_strong(R,D_Conds,G,E),!.

conj_member_strong1(T,_D_Conds,(A & _Cj),E) :- 
    check_atom(T,A,_R),
    list_ex(E,T). 
conj_member_strong1(T,D_Conds,(_Y & RCj),E):- 
    conj_member_strong1(T,D_Conds,RCj,E).
 
check_atom(T,A,no) :-    
    A=T,!.
check_atom(T,A,RuleId) :-  
    equiv_rule(RuleId,T,T1),!,  
    A=T1.

list_call([]) :- !.
list_call([G|R]) :-
    call(G), 
    list_call(R).

list_ex([],_).
list_ex([A|R],T) :-
    T \== A, list_ex(R,T).   % to exclude identical atoms

apply_equiv(no,A,A).
apply_equiv(R,A & B,A1 & B1) :-
    equiv_rule(R,A,A1),!,
    apply_equiv(R,B,B1).
apply_equiv(R,A & B,A & B1) :- !,
    apply_equiv(R,B,B1).
apply_equiv(R,A,A1) :-
    equiv_rule(R,A,A1),!.
apply_equiv(_R,A,A).
    

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% New predicate generation

newpred_counter(0).

newpred(P,A,T):-
    retract(newpred_counter(Y)), !,
    Z is Y + 1,
    assert(setlog:newpred_counter(Z)),
    name(Y,Ylist),
    append(T,Ylist,Plist),
    name(Pred,Plist),
    mklist(L,A),
    P =.. [Pred|L].


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% transform_goal/2 
% Transform a goal from the external representation to the
% internal representation, by rewriting intensional sets,
% RUQs, set and bag terms

transform_goal(Goal_external,Goal_internal) :-
       sf_in_goal(Goal_external,Goal_ruqL),
       list_to_conj(Goal_ruq,Goal_ruqL),
       preproc_goal(Goal_ruq,Goal),!,
       ruq_in_goal(Goal,Goal_internal).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% transform_clause/2 
% Transform a clause from the external representation to the
% internal representation, by rewriting intensional sets,
% RUQs, set and bag terms

transform_clause(Clause_external,Clause_internal) :-
       sf_in_clause(Clause_external,ExplClause),
       preproc_clause(ExplClause,ExtClause),
       ruq_in_clause(ExtClause,Clause_internal).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     Postprocessing 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%% Set (multiset) postprocessor:  
%%%%%%%%%%%%% from 'with' ('mwith') to {...} (*({...})) notation  

postproc(X,X):- 
        var(X),!.      
postproc(X,X):-
        atomic(X),!.
postproc(X,Y):-
        nonvar(X), X = _ with _,!,
        norep_in_set(X,X1),
        with_postproc(X1,Y). 
postproc(X,Y):-
        nonvar(X), X = _ mwith _,!,
        mwith_postproc(X,Z),
        mwith_out(Z,Y).
postproc(X,Z):-
        nonvar(X), 
        =..(X,[F|ListX]),
        postproc_all(ListX,ListZ),
        =..(Z,[F|ListZ]).

postproc_all([],[]).
postproc_all([A|L1],[B|L2]):-
        postproc(A,B),
        postproc_all(L1,L2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% set postprocessing 

with_postproc(A,A) :- var(A),!.
with_postproc(K,K):- is_ker(K), !.
with_postproc(A,{}(B)):-
        postproc_list(A,B).

%postproc_list(X with A1,(A2 \ X)) :-  
postproc_list(X with A1,(A2 / X)) :-  
        var(X),!,postproc(A1,A2).
postproc_list({} with A1,A2):- !,
        postproc(A1,A2).
%postproc_list(K with A1,(A2 \ K)) :-  
postproc_list(K with A1,(A2 / K)) :-  
        is_ker(K),!,postproc(A1,A2).
postproc_list(B1 with A1,(A2,B2)):-
        postproc(A1,A2),postproc_list(B1,B2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% bag postprocessing

mwith_out({}(X),*({}(X))).

mwith_postproc(A,A) :- var(A),!.
mwith_postproc({},{}):- !.
mwith_postproc(A,{}(B)):-
    bag_postproc_list(A,B).

%bag_postproc_list(X mwith A1,(A2 \ X)) :-   
bag_postproc_list(X mwith A1,(A2 / X)) :-   
    var(X),!,postproc(A1,A2).
bag_postproc_list({} mwith A, A):-
    var(A),!.
bag_postproc_list({} mwith A1,A2):-!,
    postproc(A1,A2).
bag_postproc_list(B1 mwith A1,(A2,B2)):-
    postproc(A1,A2), bag_postproc_list(B1,B2).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%     Auxiliary predicates     %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Exported predicates:
%
%             list_to_conj/2,
%             conj_append/3,
%             list_term/1,
%             mklist/2,
%%             member/2,
%             memberrest/3,
%             memberall/4,
%             member_strong/2,
%%             append/3,
%             listunion/3,
%             subset_strong/2,
%             norep_in_list/2,
%             remove_list/3,
%             list_to_set/3,
%             set_term/1,
%             tail/2,
%             replace_tail/3,
%             split/3,
%             bounded/1
%             set_length/2,
%             set_member/3,
%             is_empty/1,
%             int_term/1,
%             is_int/3,
%             int_to_set/2,
%             int_length/2,
%             norep_in_set/2,
%             bag_term/1,
%             bag_tail/2,
%             de_tail/2,
%             empty_aggr/1,
%             aggr_comps/3,
%             alldist/1,
%             extract_vars/2,
%             remove_var/3,
%             samevar/2,
%             occurs/2,
%             occur_check/2
%             chvar/6,
%             simple_integer_expr/1,
%             simple_arithm_expr/1,
%             integer_expr/1,
%             arithm_expr/1


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     List manipulation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

list_term(T) :- 
        nonvar(T), 
        (T=[],! ; T=[_ | _]).  

mklist([],0):- !.
mklist([_|R],N):-
        M is N-1,
        mklist(R,M).

%member(X,[X|_R]).
%member(X,[_|R]):-member(X,R).

memberrest(X,[X|R],R) :- !.
memberrest(X,[_|R],L):-
        memberrest(X,R,L).

memberall(A,B,[A|_R],[B|_S]).
memberall(A,B,[_|R],[_|S]):- 
        memberall(A,B,R,S).

%append([],L,L).                                     
%append([X|L1],L2,[X|L3]):-
%       append(L1,L2,L3).

member_strong(A,[B|_R]):- 
         A == B, !.
member_strong(A,[_|R]):- 
        member_strong(A,R).

notin(_,[]).       % not member strong
notin(A,[B|R]):-
        A \== B, notin(A,R).

listunion([],L,L).   
listunion([A|R],X,[A|S]):- 
        notin(A,X),!,
        listunion(R,X,S).
listunion([_A|R],X,S):-
        listunion(R,X,S).

subset_strong([],_L):-!.
subset_strong([X|L1],L2) :-
        member_strong(X,L2),
        subset_strong(L1,L2).

norep_in_list([],[]):-!.
norep_in_list([A|R],S):-
        member_strong(A,R),!,
        norep_in_list(R,S).
norep_in_list([A|R],[A|S]):-
        norep_in_list(R,S).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     Set manipulation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

set_term(T) :- 
       nonvar(T), 
       (T={},! ; T=_ with _).     

is_set(S) :- set_term(S),!.  
is_set(S) :- int_term(S).   

tail(R,R) :- var(R),!.
tail(R with _,R) :- var(R),!.
tail({} with _,{}) :- !.
tail(int(_A,_B) with _,{}) :- !.
tail(ris(_,_,_,_,_),{}) :- !.     %ris
tail(R with _,T) :- 
       tail(R,T).

bounded(T) :- 
       var(T),!,fail.
bounded({}) :- !.
bounded(R with _) :- 
       bounded(R).

replace_tail(R,N,N) :- var(R),!.
replace_tail({},N,N) :- !.
replace_tail(R1 with X,N,R2 with X) :- 
       replace_tail(R1,N,R2).

%%%% split(S,N,L) true if S is a set term of the form N with tn with ... with t1
%%%% (n >= 0) and L is the list [t1,...,tn]
split(N,N,[]):-
       var(N),!.
split(S with T, N, [T|R]):-
       split(S,N,R).

norep_in_set(X,X):- var(X),!.
norep_in_set(K,K) :- is_ker(K), !.
norep_in_set(R with A,S):-
       set_member_strong(A,R),!,
       norep_in_set(R,S).
norep_in_set(R with A,S with A):-
       norep_in_set(R,S).        

set_length(S,N) :-
       set_length(S,0,N).
set_length(X,_,_) :-
       var(X), !, fail.
set_length(S,N,N) :-
       is_empty(S), !.
set_length(int(A,B),N,M) :- !,
       M is N + (B - A) + 1.
set_length(R with _X,N,M):-
       N1 is N + 1,
       set_length(R,N1,M).

set_member(X,_R with Y,C):-
       sunify(X,Y,C).
set_member(X,R with _Y,C):-
       set_member(X,R,C).

set_member_strong(A,B):-
       nonvar(B),
       B = _ with X, 
       A == X,!.
set_member_strong(A,B):-
       nonvar(B), 
       B = Y with _,
       set_member_strong(A,Y).

list_to_set(L,S,[]) :-            % list_to_set(+list,?set,-constraint)
       var(S),!, 
       mk_set(L,S).             
list_to_set(L,S,C) :-            
       mk_test_set(L,S,C).   
          
mk_set([],{}) :- !.             
mk_set([X|L],R with X) :-
       mk_set(L,R).

mk_test_set([],{},[]) :- !.
mk_test_set([X|L],S,Cout) :-
       sunify(S,R with X,C1),
       list_to_set(L,R,C2),
       append(C1,C2,Cout).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     Interval manipulation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

int_term(T) :- 
       nonvar(T), 
       T=int(A,B), 
       (var(A),! ; integer(A)),
       (var(B),! ; integer(B)). 

is_int(T,A,B) :-                     % is_int(I,A,B) is true if I is a term that denotes an interval
       T=int(A,B),
       nonvar(A), nonvar(B),      
       integer(A), integer(B),!.     
is_int(_T,_A,_B) :-  
       fail.

int_to_set(int(A,A),{} with A) :- !. % int_to_set(+I,?S) is true if S denotes the set
int_to_set(int(A,B),S with A) :-     % of all elements of the interval I 
       A < B,
       A1 is A + 1,
       int_to_set(int(A1,B),S).

int_to_set(int(A,A),R with A,R) :- !.% int_to_set(+I,?S) is true if S contains the set
int_to_set(int(A,B),S with A,R) :-   % of all elements of the interval I 
       A < B,
       A1 is A + 1,
       int_to_set(int(A1,B),S,R).

int_length(int(A,B),L) :-
       N is B - A + 1,
      (N < 0,!, L = 0           
       ;
       L = N
       ).       


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     Bag manipulation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

bag_term(T) :- 
       nonvar(T), 
       (T={},! ; T=_ mwith _).  

bag_tail(R mwith _ ,R) :- var(R),!.
bag_tail({} mwith _ ,{}) :- !.
bag_tail(R mwith _ ,T) :- 
       bag_tail(R,T).

de_tail(R,{}) :- var(R),!.
de_tail({},{}) :- !.
de_tail(R mwith S,K mwith S) :- 
       de_tail(R,K).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%   List/Set/Bag/Interval manipulation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

empty_aggr(A) :-                  % empty set/multiset/list
       (is_empty(A),! ; A == []).
                                  
is_empty({}) :- !.                % empty set (also specified as int(L,H) with L>H)
is_empty(S) :- !,            
       is_int(S,L,H),
       L > H.

aggr_comps(R with X,X,R) :- !.    % set
aggr_comps(R mwith X,X,R) :- !.   % bag
aggr_comps([X | R],X,R).          % list


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%  Arithmetic expressions manipulation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

simple_integer_expr(E) :- 
      (var(E),! ; integer(E)).

simple_arithm_expr(E) :-
      (var(E),! ; number(E)).

integer_expr(E) :-       % true if E is an integer expression       
      on_exception(_Error,fd_eq(_X,E),(write('Problem in arithmetic expression'),nl,fail)).

arithm_expr(E) :-        % true if E is a ground arithmetic expression       
      on_exception(_Error,_X is E,(write('Problem in arithmetic expression'),nl,fail)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%  Variable manipulation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

samevar(X,Y) :- 
      var(X), var(Y), X == Y.

chvar(L1,[X|L1],X,L2,[Y|L2],Y):-
    var(X), notin(X,L1), !.
chvar(L1,L1,X,L2,L2,Y):-
    var(X), find_corr(X,Y,L1,L2),!.
chvar(L1,L1new,(H :- B),L2,L2new,(H1 :- B1)):-
    !, chvar(L1,L1a,H,L2,L2a,H1),
    chvar(L1a,L1new,B,L2a,L2new,B1).
chvar(L1,L1new,(B1 & B2),L2,L2new,(B1a & B2a)):-
    !, chvar(L1,L1a,B1,L2,L2a,B1a),
    chvar(L1a,L1new,B2,L2a,L2new,B2a).       
chvar(L1,L1,F,L2,L2,F):-
    atomic(F),!.
chvar(L1,L1new,F,L2,L2new,F1):-
    F =.. [Fname|Args],
    chvar_all(L1,L1new,Args,L2,L2new,Brgs),
    F1 =.. [Fname|Brgs].
    
chvar_all(L1,L1,[],L2,L2,[]).
chvar_all(L1,L1b,[A|R],L2,L2b,[B|S]):-
    chvar(L1,L1a,A,L2,L2a,B),
    chvar_all(L1a,L1b,R,L2a,L2b,S).
        
find_corr(X,Y,[A|_R],[Y|_S]):-
    X == A,!.    
find_corr(X,Y,[_|R],[_|S]):-
    find_corr(X,Y,R,S).   

occurs(X,Y):-   % occur(X,T): true if variable X occurs in term T
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

occur_check(X,Y):-    % occur_check(X,T): true if variable X DOES NOT occur in term T
      var(Y),!,X \== Y.
occur_check(X,Y):-
      Y =.. [_|R],
      occur_check_list(X,R).
occur_check_list(_X,[]):-!.
occur_check_list(X,[A|R]):-
      occur_check(X,A),
      occur_check_list(X,R).

extract_vars(A,[A]):-
    var(A),!.                 
extract_vars(exists(V,B),Vars):-
    var(V),!,
    extract_vars(B,List),
    remove_var(V,List,Vars). 
extract_vars(exists(V,B),Vars):-
    !,extract_vars(B,List),
    remove_list(V,List,Vars).
extract_vars(forall(X in Y,B),Vars):-
    !, extract_vars(Y,L1),
    extract_vars(B,L2),
    listunion(L1,L2,L),
    remove_var(X,L,Vars).    
extract_vars(Int,Vars):-
    is_sf(Int,X,G),!,
    extract_vars(G,Vars1),
    remove_var(X,Vars1,Vars).   
extract_vars(P,Vars):-
    functor(P,_,A),
    !, findallvars(P,A,Vars).
    
findallvars(_P,0,[]):- !.   
findallvars(P,A,Vars):-
    arg(A,P,Arg),
    extract_vars(Arg,L1),
    B is A-1,
    findallvars(P,B,L2),
    listunion(L1,L2,Vars).
        
remove_var(_,[],[]).
remove_var(X,[Y|L],S):-
    X == Y,!,remove_var(X,L,S).
remove_var(X,[Y|L],[Y|S]):-
    remove_var(X,L,S).  
        
remove_list([],L,L).
remove_list([X|R],Vars,Finalvars):-
    remove_var(X,Vars,S),
    remove_list(R,S,Finalvars).   

alldist([]).
alldist([A|R]):-
    var(A), not_in_vars(A,R),
    alldist(R).
    
not_in_vars(_X,[]).
not_in_vars(X,[A|R]):-
    X \== A, not_in_vars(X,R).
   

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%  Conjunction manipulation 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

list_to_conj(A & B,[A|R]):-
    !,list_to_conj(B,R).
list_to_conj(true,[]):-!.
list_to_conj(A,[A]).

conj_append(Cj1,Cj2,(Cj1 & Cj2)) :-    
        var(Cj1),!.
conj_append(true,Cj2,Cj2) :- !.
conj_append((X & Cj1),Cj2,(X & Cj3)) :- !,
        conj_append(Cj1,Cj2,Cj3).
conj_append(X,Cj2,(X & Cj2)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%% Configuration parameters %%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

path('').                         % the default path (= the working director '.')  

rw_rules('setlog_rules.pl').      % the default library of filtering rules    

strategy(cfirst).                 % the default atom selection strategy (= "constraint first") 
%strategy(cfirst(UserPredList)).  % UserPredList is a list of user defined predicates to be 
                                  % executed just after constraint solution (before all other
                                  % user-defined predicates)
                                  % e.g., strategy(cfirst([ttf_list(_),ttf_nat(_),ttf_int(_),ttf_btype(_)])).       


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%% Starting the {log} interpreter %%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%:- setlog(consult_lib,_).

:- load_rwrules_lib.     % load the library of filtering rules  

:- nl,write('Use ?- setlog_help to get help information about {log}'),nl,nl.
