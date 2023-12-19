
% Jean-Michel C. (20031706), Nicolas D-P. (20105266)
%% -*- mode: prolog; coding: utf-8 -*-

%% GNU Prolog défini `new_atom`, mais SWI Prolog l'appelle `gensym`.
genatom(X, A) :-
    (predicate_property(new_atom/2, built_in);    % Older GNU Prolog
     predicate_property(new_atom(_,_), built_in)) % Newer GNU Prolog
    -> new_atom(X, A);
    gensym(X, A).


%% type(+T)
%% Prédicat qui décrit la forme d'un type d'une valeur dans Cat.
type(int).
type(bool).
type(list(T)) :- type(T).
type((T1 -> T2)) :- stype(T1), stype(T2).
type(var(X)) :- atom(X).                        % A type variable.
type(forall(X, T)) :- atom(X), type(T).         % A polymorphic type.typeof_val(nil, X).
%% stype(+ST)
%% Prédicat qui décrit la forme d'un type d'une pile dans Cat.
stype(nil).
stype(H^T) :- type(H), stype(T).

%% value(+V)
%% Prédicat qui décrit la forme d'une valeur dans Cat.
value(Num) :- number(Num).
value(true).
value(false).
value(nil).                             % An empty list.
value(X^Xs) :- value(X), value(Xs).     % A single-linked list node.
value(Fun) :- function(Fun).

%% stack(+S)
%% Prédicat qui décrit la forme d'une pile dans Cat.
stack(nil).
stack(V^VS) :- value(V), stack(VS).

%% functions(+Ops)
%% Prédicat qui décrit la forme d'une function dans Cat.
function([]).
function([Op | Ops]) :- oper(Op), function(Ops).

%% oper(+Op)
%% Prédicat qui décrit la forme d'une opération dans Cat.
oper(dup).                              % Duplique le ToS.
oper(swap).                             % Échange les deux ToS.
oper(pop).                              % Enlève l'élément au ToS.
oper(get(N)) :- integer(N), N >= 0.     % Cherche le Nième élément de la pile.
oper(set(N)) :- integer(N), N >= 0.     % Change le Nième élément de la pile.
oper(Val) :- value(Val).                % Ajoute la constante Val sur ToS.
oper(add).                              % Fait la somme des 2 éléments au ToS.
oper(if).                               % Teste le booléen au ToS.
oper(cons).                             % Crée un nouvel élément de liste.
oper(emptyp).                           % Teste si la liste au ToS est vide.
oper(car).                              % Retourne la tête de la liste au ToS.
oper(cdr).                              % Retourne la queue de la liste au ToS.
oper(apply).                            % Appelle une fonction.
oper(papply).                           % Construit une fermeture.
oper(Op:Type) :- oper(Op), type(Type).  % Annotation de type explicite.

%% Prédicats auxiliaires.


%------------------------------------------------------------------------------------------

% length of stack
lenStack(X, 1) :- check_elem(X), !.
lenStack(X^XS, N) :- len(X^XS,0,N).
len(X,I,I2):- I2 is I + 1, check_elem(X), !.
len(X^XS,I,N):- I2 is I + 1, len(XS,I2,N).

% check if it's not a stack
check_elem(X^(XS)) :- !, false.
check_elem(_) :- true.

% Prédicat qui indique si c'est une liste ou un nombre
check_nat(X^(XS)) :- !, false.
check_nat(N) :- nat(N).

% Prédicat pour les nombres naturels
nat(0).
nat(N) :- nat(N1), N is N1 + 1.

% contrainte hors borne du stack
check_bounds(N,J) :- N + 1 > 0, J > N.


%-----------------------------------------------------------------------------

%% stack_get_nth(+N, +S, -V)
%% Renvoie le Nième élément de la pile S.
stack_get_nth(N, H, X) :- lenStack(H, K),
                          check_bounds(N,K), !,
                          stack_get_n(N, H, X).
stack_get_n(0, H^_, H) :- !.
stack_get_n(0, H, H) :- check_elem(H) , !. %last element
stack_get_n(N, H^(HS), X) :- N1 is N - 1, stack_get_n(N1, HS, X) .


%-----------------------------------------------------------------------------


%% stack_set_nth(+N, +V, +S1, -S2)
%% Renvoie une pile S2 identique à S1 sauf pour le Nième élément, remplacé par V.
stack_set_nth(N, V, H, X) :-check_elem(V),
                            lenStack(H, K),
                            check_bounds(N,K), !,
                            stack_set_n(N, V, H, X).
stack_set_n(0, V, T, V) :- check_elem(T), !.
stack_set_n(0, V, _^T, V^T) :- !.
stack_set_n(N, V, H^HS1, H^HS2) :- check_elem(N), N1 is N - 1,
                                   stack_set_n(N1, V, HS1, HS2), !.


%-----------------------------------------------------------------------------
%%% Polymorphisme paramétrique  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% type_subst(+T1, +X, +T2, -T3)
%% Renvoie T3 = T1[T2/X].
%% I.e. T3 est le résultat de la substitution de X par T2 dans T1.
%% Utile pour implémenter la règle d'élimination du polymorphisme.
type_subst(T1, _, _, T2) :- var(T1), !, T1 = T2.
type_subst(var(Y), X, T1, T2) :- X = Y -> T2 = T1; T2 = var(Y).
type_subst(int, _, _, int).
type_subst(bool, _, _, bool).
type_subst(list(T1), X, T, list(T2)) :- type_subst(T1, X, T, T2).
type_subst((T11 -> T12), X, T, (T21 -> T22)) :- 
        type_subst(T11, X, T, T21), type_subst(T12, X, T, T22).
type_subst(forall(X1, T1), X, T, forall(X2, T2)) :-
        %% Fait une étape de renommage α pour éviter la capture de nom.
        genatom(X1, X2), type_subst(T1, X1, var(X2), T12),
        type_subst(T12, X, T, T2).
type_subst(nil, _, _, nil).
type_subst(H1^T1, X, T, H2^T2) :-
        type_subst(H1, X, T, H2), type_subst(T1, X, T, T2).

%% type_instantiate(+T1, ?T2)
%% T2 est une instantiation de T1.
type_instantiate(forall(X, T1), T3) :- 
    type_subst(T1, X, _, T2), type_instantiate(T2, T3).
type_instantiate(T, T).

%% type_uiv(+T, -XS)
%% Cherche les variables Prolog non instanciées dans le type T, les instancie
%% par `var(X)` avec un X instancié à un atome tout frais, et
%% renvoie la liste des atomes frais ainsi créés.
%% Utile pour implémenter la règle d'introduction du polymorphisme.
type_uiv(var(X), []) :- atom(X), !.
type_uiv(var(X), [X]) :- genatom(t, X), !.
type_uiv(int, []).
type_uiv(bool, []).
type_uiv(list(T), VS) :- type_uiv(T, VS).

type_uiv((ST1 -> ST2), XS) :- type_uiv(ST1,XS), !.
% ------------------------------------------------------------------------------
type_uiv(H^HS, VS) :- type_uiv(H,X), type_uiv(HS,XS), list_redux([X|XS], VS), !.
type_uiv(forall(X,T), VS) :- atom(X), type_uiv(T, VS), !.


% Fonction qui enlève les sous-listes vides et regroupe toutes les sous-listes
% dans une seule liste.
list_redux([[X1]|X2], [X1|X3]) :- list_redux(X2,X3), !.
list_redux([[]|X1], X2) :- list_redux(X1, X2), !.
list_redux([X1|X2], [X1|X3]) :- list_redux(X2, X3), !.
list_redux(X,X).   



%-----------------------------------------------------------------------------
%%% Inférence de types  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% typeof_val(+V, -T)
%% Infère le type T de la valeur V.  Équivalent à "⊢ V : T".
%% Si V est une fonction, renvoie un type T aussi polymorphe que possible.
%% Pour trouver le polymorphisme, utiliser `type_uiv`.
typeof_val(Num, int) :- number(Num), !.
typeof_val(true, bool) :- !.
typeof_val(false, bool) :- !.
typeof_val(nil, list(T)) :- type(T).
typeof_val(X^(XS), list(T)) :- value(X),
                               typeof_val(X, T),
                               typeof_val(XS, list(T)),
                               type(T), !.

% Polymorphisme
typeof_val([], forall(XS, (ST -> ST))) :- type_uiv((ST -> ST), XS), !.
typeof_val([OP | []], forall(H, (ST1 -> ST2))) :- oper(OP),
                                  typeof_op(OP, ST1, ST2) ,
                                  type_uiv((ST1 -> ST2), [H|[]]), !.
typeof_val([OP | []], forall(H, T)) :- oper(OP),
                                  typeof_op(OP, ST1, ST2) ,
                                  forall_comp(HS, (ST1 -> ST2), T),
                                  type_uiv((ST1 -> ST2), [H|HS]), !.
typeof_val([Op | Ops], forall(H ,(ST1 -> ST2))) :- op_comp([Op | Ops], (ST1 -> ST2), [H|[]]),
                                       type_uiv((ST1 -> ST2), X), !.
typeof_val([Op | Ops], forall(H ,T)) :- op_comp([Op | Ops], (ST1 -> ST2), [H|HS]),
                                       forall_comp(HS, (ST1 -> ST2), T), 
                                       type_uiv((ST1 -> ST2), X), !.

typeof_val(V, forall(X,T)) :-
    % On teste `atom(X)` pour être sûr qu'on est en train de *vérifier*
    % que V a un type forall(...) déjà fourni en entrée, plutôt qu'en train
    % d'*inférer* un type polymorphe.
    atom(X),
    genatom(t, X2), type_subst(T, X, var(X2), T2), typeof_val(V, T2).
typeof_val(_,_,_):- false.

% Permet de faire les étapes intermédiaire lors d'un composition d'opération dans une fonction
op_comp([OP | []], (ST1 -> ST2), XS) :- oper(OP), 
                                    typeof_op(OP, ST1, ST2) ,
                                    type_uiv((ST1 -> ST2), XS), !.
op_comp([Op | Ops], (ST1 -> ST3), XS) :-oper(Op),
                                    typeof_op(Op, ST1, ST2), 
                                    op_comp(Ops, (ST2 -> ST3), XS), !.

% Composition de forall
forall_comp([H|[]], (ST1 -> ST2), forall(H, (ST1 -> ST2))).
forall_comp([H|HS], (ST1 -> ST2), forall(H, T)) :- 
                                forall_comp(HS, (ST1 -> ST2), T), !.






%-----------------------------------------------------------------------------
%% typeof_op(+Op, ?ST1, ?ST2)
%% Si l'opération Op est exécutée avec une pile de type ST1, le résultat est
%% une pile de type ST2.  Équivalent à "⊢ Op : ST1 ⇒ ST2".
typeof_op(V, ST, T^ST) :- typeof_val(V, T).
% dup, swap et pop son identique aux règles données dans la figure 2.
typeof_op(dup, T^ST, T^T^ST) :- !.
typeof_op(swap, T1^T2^ST, T2^T1^ST) :- !.
typeof_op(pop, T^ST, ST) :- !.
% On vérifie que T est bien le type du N-ieme élément
typeof_op(get(0), T^ST, T^T^ST) :- !.
typeof_op(get(0), T, T^T) :- !.
typeof_op(get(N), T0^ST, T^T0^ST) :- check_nat(N), N1 is N - 1, 
                                     typeof_op(get(N1), ST, T^ST), !.
% On set la remplace le N+1-ieme type par le premier et on enlève le premier
typeof_op(set(0), T1^T2^ST, T1^ST) :- !.
typeof_op(set(0), T1^T2, T1) :- !.
typeof_op(set(0), _, _) :- !, false.
typeof_op(set(N), T0^T1^ST1, T1^ST2) :- check_nat(N), N1 is N - 1,
                                        typeof_op(set(N1), T0^ST1, ST2), !.
% On peut seulement additionner 2 entiers
typeof_op(add, int^int^ST, int^ST) :- !.
% Le if ne fonctionne que si le premier élément est un bool. 
typeof_op(if, bool^T^T^ST, T^ST) :- !.
% cons, emptyp, car et cdr son identique aux règles données dans la figure 2.
typeof_op(cons, T^list(T)^ST, list(T)^ST) :- !.
typeof_op(emptyp, list(T)^ST, bool^ST) :- !.
typeof_op(car, list(T)^ST, T^ST) :- !.
typeof_op(cdr, list(T)^ST, list(T)^ST) :- !.
typeof_op(apply,(ST1->ST2)^ST1 , ST2 ) :- !.
typeof_op(apply,forall(X,T)^T0^ST,T1^ST) :- type_subst(T,X,T0,T1),!.
typeof_op(papply, ((T^ST1)->ST2)^T^ST3, (ST1->ST2)^ST3 ) :- !.
typeof_op(papply,forall(X,T)^T0^ST,T1^ST) :- type_subst(T,X,T0,T1), !.
typeof_op(OP:T, ST, T^ST) :- typeof_op(OP, ST, T^ST), !.
typeof_op(_,_,_):- false.
%% typeof(+Ops, ?ST1, ?ST2)
%% Si les opération Ops sont exécutées avec une pile de type ST1, le résultat est
%% une pile de type ST2.
typeof([], S, S).
typeof([Op | Ops], S1, S3) :- typeof_op(Op, S1, S2), typeof(Ops, S2, S3).







%-----------------------------------------------------------------------------
%%% Evaluation  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% eval(+Ops, +S1, -S2)
%% Évalue les opértions Ops avec S1 comme pile de départ.
%% Renvoie la pile résultante S2.
eval([], S, S).
%% ¡¡ À COMPLÉTER !!
% Val (ajout d'un valeur ToS)
eval([[]], X, []^X):- !.
eval([[Op]], X, [Op]^X):- !.
eval([Op]:T, X, [Op]^X):-  !.
eval([[Op]:T], X, [Op]^X):- !.
eval([nil],Xs,(nil)^Xs):- !.
eval([Val],Y, Val^Y):-  typeof_val(Val, int) ; typeof_val(Val, bool), !.
eval([X^Xs],Y,(X^Xs)^Y):- !.
eval([add],X1^X2^Xs,X3^Xs):- X3 is X1 + X2, !.
eval([swap],X1^X2^Xs,X2^X1^Xs):- !.
eval([if],true^X1^X2^Xs, X1^Xs ) :- !.
eval([if],false^X1^X2^Xs, X2^Xs ) :- !.
eval([get(N)],X^Xs, X1^X^Xs):- stack_get_nth(N, X^Xs, X1) ,
                               typeof_val(X1, Type) , !.
eval([set(N)],X^Xs, Y):-  stack_set_nth(N, X, Xs, Y), !.
eval([cons],X1^X2^Xs,(X1^X2)^Xs):- !.
eval([car],(X^Xs)^XXs, X^XXs):- !.
eval([cdr],(X^Xs)^XXs, Xs^XXs):- !.
eval([emptyp], (nil)^Xs, true^Xs):- !.
eval([emptyp], (_)^Xs, false^Xs):- !.
eval([apply], Func^Xs, Y):- eval(Func,Xs, Y), !.
eval([papply], []^V^Xs, [V]^Xs):-  !.
eval([papply], [V2]^V^Xs, [V,V2]^Xs):-  !.
% pour pop et dup
eval([Op|[]],X^Xs, Y):- typeof_op(Op, X^Xs, Y), !.
eval([X|Xs],Y,R):- eval([X],Y,Z), eval(Xs,Z,R), !.
eval(_,_,_):- false.











