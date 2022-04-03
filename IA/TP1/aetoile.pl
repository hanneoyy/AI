%*******************************************************************************
%                                    AETOILE
%*******************************************************************************

/*
Rappels sur l'algorithme
 
- structures de donnees principales = 2 ensembles : P (etat pendants) et Q (etats clos)
- P est dedouble en 2 arbres binaires de recherche equilibres (AVL) : Pf et Pu
 
   Pf est l'ensemble des etats pendants (pending states), ordonnes selon
   f croissante (h croissante en cas d'egalite de f). Il permet de trouver
   rapidement le prochain etat a developper (celui qui a f(U) minimum).
   
   Pu est le meme ensemble mais ordonne lexicographiquement (selon la donnee de
   l'etat). Il permet de retrouver facilement n'importe quel etat pendant

   On gere les 2 ensembles de fa�on synchronisee : chaque fois qu'on modifie
   (ajout ou retrait d'un etat dans Pf) on fait la meme chose dans Pu.

   Q est l'ensemble des etats deja developpes. Comme Pu, il permet de retrouver
   facilement un etat par la donnee de sa situation.
   Q est modelise par un seul arbre binaire de recherche equilibre.

Predicat principal de l'algorithme :

   aetoile(Pf,Pu,Q)

   - reussit si Pf est vide ou bien contient un etat minimum terminal
   - sinon on prend un etat minimum U, on genere chaque successeur S et les valeurs g(S) et h(S)
	 et pour chacun
		si S appartient a Q, on l'oublie
		si S appartient a Ps (etat deja rencontre), on compare
			g(S)+h(S) avec la valeur deja calculee pour f(S)
			si g(S)+h(S) < f(S) on reclasse S dans Pf avec les nouvelles valeurs
				g et f 
			sinon on ne touche pas a Pf
		si S est entierement nouveau on l'insere dans Pf et dans Ps
	- appelle recursivement etoile avec les nouvelles valeurs NewPF, NewPs, NewQs

*/

%*******************************************************************************

:- ['avl.pl'].       % predicats pour gerer des arbres bin. de recherche   
:- ['taquin.pl'].    % predicats definissant le systeme a etudier

%*******************************************************************************
main :-
    % Fixer la situation de d��part �� 0
    initial_state(S0),
    heuristique(S0, H0),  
    G0 is 0,
    F0 is H0 + G0,
    
    empty(Pf0),
    empty(Pu0),
    empty(Q),

    % Inserer un noeud dans Pf et un noeud dans Pu
    insert([[F0,H0,G0],S0], Pf0, Pf),
    insert([S0, [F0,H0,G0], nil, nil], Pu0, Pu),

	% lancement de Aetoile
	aetoile(Pf,Pu,Q).

%*******************************************************************************

aetoile(nil, nil, _) :- print("PAS de SOLUTION : L'ETAT FINAL N'EST PAS ATTEIGNABLE !").
% aetoile(Pf, _, Qs) :- 
%     suppress_min([[_, _, _], Umin], Pf, _),
%     final_state(Umin),
%     affiche_solution(Qs),
%     print("ON EST DANS SOLUTION"), !.

aetoile(Pf, Ps, Qs) :-
    writeln("ON EST DANS AETOILE"),
    suppress_min([[_, _, G], Umin], Pf, Pf2),
    (final_state(Umin) ->
    affiche_solution(Qs)
    ;
    suppress([Umin,[_,_,_], _, _], Ps, Ps2),

    % insertion dans Q
    insert(Umin, Qs, QsNew),
    writeln("NEW QS ETTER INSERT Umin : " + QsNew),

    % Developpement de u
    expand(Umin, S, G),
    writeln("S ICI      " + S + "         "),
    loop_successors(S, Pf2, Ps2, QsNew, PfNew, PsNew),

    % recursivity 
    aetoile(PfNew, PsNew, QsNew)
    ).
    
affiche_solution(Qs) :- put_90(Qs).

% Qu'est-ce que c'est G ?
expand(Umin, S, G) :- 
    G1 is G + 1, 
    findall([U, [F, H, G1], Umin, A], (rule(A,1,Umin,U), heuristique(U, H), F is H + G1), S).

loop_successors([], _, _, _, _, _, _) :- true.

% loop_successors([[Uh, [Fh, Hh, G1h], Uminh, Ah]|Tail], Pf, Ps, Qs) :- 
%     (belongs([Uh, [_, _, _], _, _],Qs) -> loop_successors(Tail, Ps, Pf, Qs) ; 
%         (belongs([Uh, [_, _, _], _, _],Ps) -> 
%                         suppress([Uh, [F, H, G1], Umin, A], Ps, Ps2),
%                         suppress([[_, _, _], Uh], Pf, Pf2),
%                         ((H < Hh) -> insert([Uh, [F, H, G1], Umin, A], Ps2, Ps3), insert([[F, H, G1], Uh], Pf2, Pf3) ; insert([Uh, [Fh, Hh, G1h], Uminh, Ah], Ps2, Ps3), insert([[Fh, Hh, G1h], Uh], Pf2, Pf3)) ;
%                             insert([Uh, [Fh, Hh, G1h], Uminh, Ah], Ps, Ps3), 
%                             insert([[Fh, Hh, G1h], Uh], Pf, Pf3)
%                         )
%     ),
%     loop_successors(Tail, Pf3, Ps3, Qs).

loop_successors([[Uh, [Fh, Hh, G1h], Uminh, Ah]|Tail], Pf, Ps, Qs, PfNew, PsNew) :-
    writeln("UH : " + Uh),  
    writeln("PF : " + Pf),
    writeln("PS : " + Ps),
    writeln("QS : " + Qs),
    (belongs([Uh, [_, _, _], _, _],Qs) -> 
    writeln("Inn i Qs"),
        Pf3 = Pf, 
        Ps3 = Ps        
        ; 
        writeln("INN I ikke Qs"),
        (belongs([Uh, [Fold, _, _], _, _],Ps) -> 
            writeln("Inn i Ps"),
            % suppress([Uh, [F, H, G1], Umin, A], Ps, Ps2),
            % suppress([[_, _, _], Uh], Pf, Pf2),
            ((Hh + G1h < Fold) -> 
                suppress([Uh, [_, _, _], _, _], Ps, Ps2),
                insert([Uh, [Fh, Hh, G1h], Uminh, Ah], Ps2, Ps3), 
                suppress([[_, _, _], Uh], Pf, Pf2),
                insert([[Fh, Hh, G1h], Uh], Pf2, Pf3)
                % add([Uh, [F, H, G1], Umin, A],Qs)
            ; 
            writeln("INN i ikke Ps"),
                true
                % insert([Uh, [Fh, Hh, G1h], Uminh, Ah], Ps2, Ps3), 
                % insert([[Fh, Hh, G1h], Uh], Pf2, Pf3),
                % add([Uh, [F, H, G1], Umin, A],Qs)
            )
        ;
            true
        ),
        insert([Uh, [Fh, Hh, G1h], Uminh, Ah], Ps, Ps3), 
        insert([[Fh, Hh, G1h], Uh], Pf, Pf3)
    ),
    loop_successors(Tail, Pf3, Ps3, Qs, PfNew, PsNew),
    writeln("Pf : " + Pf3),
    writeln("Ps : " + Ps3),
    writeln("Qs : " + Qs).

/*

 - reussit si Pf est vide ou bien contient un etat minimum terminal
   - sinon on prend un etat minimum U, on genere chaque successeur S et les valeurs g(S) et h(S)
	 et pour chacun
		si S appartient a Q, on l'oublie
		si S appartient a Ps (etat deja rencontre), on compare
			g(S)+h(S) avec la valeur deja calculee pour f(S)
			si g(S)+h(S) < f(S) on reclasse S dans Pf avec les nouvelles valeurs
				g et f 
			sinon on ne touche pas a Pf
		si S est entierement nouveau on l'insere dans Pf et dans Ps
	- appelle recursivement etoile avec les nouvelles valeurs NewPF, NewPs, NewQs

*/
	
   
