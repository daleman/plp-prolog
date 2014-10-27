%Autómatas de ejemplo. Si agregan otros, mejor.

ejemplo(1, a(s1, [s2], [(s1, a, s2)])).
ejemplo(2, a(s1, [s1], [(s1, a, s1)])).
ejemplo(3, a(s1, [s1], [])).
ejemplo(4, a(s1, [s2, s3], [(s1, a, s1), (s1, a, s2), (s1, b, s3)])).
ejemplo(5, a(s1, [s2, s3], [(s1, a, s1), (s1, b, s2), (s1, c, s3), (s2, c, s3)])).
ejemplo(6, a(s1, [s3], [(s1, b, s2), (s3, n, s2), (s2, a, s3)])).
ejemplo(7, a(s1, [s2], [(s1, a, s3), (s3, a, s3), (s3, b, s2), (s2, b, s2)])).
ejemplo(8, a(s1, [s5], [(s1, a, s2), (s2, a, s3), (s2, b, s3), (s3, a, s1), (s3, b, s2),
	(s3, b, s4), (s4, f, s5)])). % No deterministico :)
ejemplo(9, a(s1, [s1], [(s1, a, s2), (s2, b, s1)])).
ejemplo(10, a(s1, [s10, s11], [(s2, a, s3), (s4, a, s5), (s9, a, s10), (s5, d, s6), (s7, g, s8),
	(s15, g, s11), (s6, i, s7), (s13, l, s14), (s8, m, s9), (s12, o, s13), (s14, o, s15),
	(s1, p, s2), (s3, r, s4), (s2, r, s12), (s10, s, s11)])).

ejemploMalo(1, a(s1, [s2],
	[(s1, a, s1), (s1, b, s2), (s2, b, s2), (s2, a, s3)])). %s3 es un estado sin salida.
ejemploMalo(2, a(s1, [s2], [(s1, a, s1), (s2, b, s2)])). %s2 no es alcanzable.
ejemploMalo(3, a(s1, [s2, s3], [(s1, a, s3), (s1, b, s3)])). %s2 no es alcanzable.
ejemploMalo(4, a(s1, [s3], [(s1, a, s3), (s2, b, s3)])). %s2 no es alcanzable.
ejemploMalo(5, a(s1, [s3, s2, s3], [(s1, a, s2), (s2, b, s3)])). %Tiene un estado final repetido.
ejemploMalo(6, a(s1, [s3], [(s1, a, s2), (s2, b, s3), (s1, a, s2)])). %Tiene una transición repetida.
ejemploMalo(7, a(s1, [], [(s1, a, s2), (s2, b, s3)])). %No tiene estados finales.

%%Proyectores
inicialDe(a(I, _, _), I).

finalesDe(a(_, F, _), F).

transicionesDe(a(_, _, T), T).

%Auxiliar dada en clase
%desde(+X, -Y).
desde(X, X).
desde(X, Y):-desde(X, Z),  Y is Z + 1.

% Auxiliar: nos permite definir que transicion es conveniente tomar desde un estado I
% para llegar a un estado F. Útil para generar caminos cuando son infinitos.
% transicionOptima(+Automata,+Inicial,+Final,-Transicion).
transicionOptima(A,I,F,(I,E,F)) :- transicionesDe(A,T), member((I,E,F),T).
transicionOptima(A,I,F,(I,E,M)) :-
		estados(A,Estados),
		length(Estados,K),
		transicionesDe(A,T),
		between(2,K,N),
		member(M,Estados), M\=I,
		caminoDeLongitud(A,N,_,_,M,F),
		member((I,E,M),T).
transicionOptima(A,I,_,(I,E,I)) :- transicionesDe(A,T), member((I,E,I),T).

%%Predicados pedidos.

% 1) esDeterministico(+Automata) :- ∀ (q1,e1,p1) y (q2,e2,p2) transiciones,
									% si q1=q2 y e1=e2 =>
									% p1=p2.
esDeterministico(A) :- forall((transicionesDe(A,Transiciones),
						member((Q,E,P1),Transiciones), member((Q,E,P2),Transiciones)),
						(P1 = P2)).

% 2) estados(+Automata, -Estados) :- estados = {inicial} U finales U
									% estadosDeTransiciones
estados(A, EstadosOrd) :- inicialDe(A,Inicial), finalesDe(A,Finales), transicionesDe(A,Transiciones),
								estadosDeTransiciones(Transiciones,EstadosDeTransiciones),
								union([Inicial|Finales],EstadosDeTransiciones,Estados),
								sort(Estados,EstadosOrd).

% Auxiliar: agrupa los estados de un autómata a partir de las transiciones del mismo.
% estadosDeTransiciones(+Transiciones,-Estados) :- estados = [q | (q,e,p) ∈ transiciones] U
												% [p | (q,e,p) ∈ transiciones]
estadosDeTransiciones([],[]).
estadosDeTransiciones([(Q,_,P)|Transiciones],MasEstados) :-
											estadosDeTransiciones(Transiciones,Estados),
											union([Q,P],Estados,MasEstados).

% 3) esCamino(+Automata, ?EstadoInicial, ?EstadoFinal, +Camino)
% TODO: correjir este comentario...
% Nos fijamos en las transiciones y vemos si hay camino en un paso, o
% si hay camino a n-1 pasos desde un estado posterior al estado inicial.
esCamino(_, E, E, [E]).
esCamino(A, Inicial, Final, [Inicial,Medio|Es]) :- transicionOptima(A,Inicial,Final,(Inicial,_,Medio)),
													esCamino(A,Medio,Final,[Medio|Es]), !.
% Agregamos el '!' para que sólo devuelva una unificación. Si para un par de estados consecutivos en
% el camino, existen dos transiciones posibles, 'esCamino' devolvería otra unificación pero idéntica.
% Como todas las unificaciones posibles son iguales (determinadas por los estados primero y último
% del camino), sólo le permitimos devolver una. Esta aclaración es válida teniendo en cuenta que el
% parámetro 'Camino' siepmre viene instanciado.

% 4) ¿el predicado anterior es o no reversible con respecto a Camino y por qué?
% No, al agregar el '!' al final le impedimos que genere más de un camino distinto. Para que
% lo sea, hay que quitarle el '!'.
% esCamino(+Automata, ?EstadoInicial, ?EstadoFinal, -Camino)
esCaminoReversible(_, E, E, [E]).
esCaminoReversible(A, Inicial, Final, [Inicial,Medio|Es]) :-
	transicionOptima(A,Inicial,Final,(Inicial,_,Medio)),
	esCaminoReversible(A,Medio,Final,[Medio|Es]).

% 5) caminoDeLongitud(+Automata, +N, -Camino, -Etiquetas, ?S1, ?S2)
% La misma idea, pero restringiendo la longitud del camino.
caminoDeLongitud(_,1,[S1],[],S1,S1).
caminoDeLongitud(A,2,[S1,S2],[E],S1,S2) :- transicionesDe(A,T), member((S1,E,S2),T).
caminoDeLongitud(A,N,[S1|Cs],[E|Es],S1,S2):- N>2, Nm1 is N-1,
												transicionesDe(A,T), member((S1,E,SMedio),T),
												caminoDeLongitud(A,Nm1,Cs,Es,SMedio,S2).
% Agregamos la restricción 'N>2' para evitar colisión con la segunda regla.

% 6) alcanzable(+Automata, +Estado) :- ∃ N2 tq ∃ (q0,...,q) camino de longitud N.
alcanzable(A,E):- inicialDe(A,I), estados(A,Estados), length(Estados,CantEstados),
					CEMasUno is CantEstados+1,
					not(not((between(2,CEMasUno,N), caminoDeLongitud(A,N,_,_,I,E)))).

% 7) automataValido(+Automata) :- cumple las 5 cosas.
automataValido(A) :- transicionesSalientes(A),
						todosAlcanzables(A),
						algunFinal(A),
						sinFinalesRepetidos(A),
						sinTransicionesRepetidas(A).

% transicionesSalientes(+Automata) :- ∀ E estado, ¬(E final) => ∃ algunaTransicionSaliente
transicionesSalientes(A) :- forall(
					(estados(A,Estados), member(E,Estados), finalesDe(A,Fs), not(member(E,Fs))),
					algunaTransicionSaliente(A,E)
								).

% todosAlcanzables(+Automata) :- ∀ E estado, ¬(E inicial) => alcanzable(E)
todosAlcanzables(A) :- forall(
					(estados(A,Estados), member(E,Estados), inicialDe(A,I), E\=I),
					alcanzable(A,E)
							).

% algunFinal(+Automata) :- length (finales) > 0
algunFinal(A):- finalesDe(A,Finales), length(Finales,N), N>0.

% sinFinalesRepetidos(+Automata) :- ∀ E estado final, |finales|_E = 1
sinFinalesRepetidos(A) :- forall(
					(finalesDe(A,Finales), member(E,Finales)),
					cuenta(E,Finales,1)
								).

% sinTransicionesRepetidas(+Automata) :- ∀ T transicion, |transiciones|_T = 1
sinTransicionesRepetidas(A) :- forall(
					(transicionesDe(A,Transiciones), member(T,Transiciones)),
					cuenta(T,Transiciones,1)
									).

% algunaTransicionSaliente(+Automata,+Estado) :- ∃ T transicion de la forma (Estado,_,_)
algunaTransicionSaliente(A,E) :- not(not((
					transicionesDe(A,Transiciones), member((E,_,_),Transiciones)
										))).

% cuenta(+Elemento,+Lista,-N) : Cantidad de apariciones
cuenta(_,[],0).
cuenta(E,[E|FS],Nm1) :- cuenta(E,FS,N), Nm1 is N+1.
cuenta(E,[F|FS],N) :- E\=F, cuenta(E,FS,N).

%--- NOTA: De acá en adelante se asume que los autómatas son válidos.

% 8) hayCiclo(+Automata) :- ∃ E estado tq ∃ (E,....,E) camino
hayCiclo(A) :- estados(A,Estados), length(Estados,CantEstados), CEMasUno is CantEstados+1,
				between(2,CEMasUno,N), member(S1,Estados), caminoDeLongitud(A,N,_,_,S1,S1), !.
% Agregamos el '!' para que sólo devuelva una unificación. Es posible que haya más de un
% 'caminoDeLongitud' y varios valores de 'N' par los cuales encontrarlos. Sin embargo, sólo
% nos interesa recibir un true o false, así que si encuentra un camino, dejamos de buscar otros.

% 9) reconoce(+Automata, ?Palabra) :- recorrer(transiciones, finales, inicial, palabra)
% TODO: Cambiar para que en lugar de usar 'transicionesReordenadas', use 'transicionOptima'
reconoce(A,P) :- inicialDe(A,I), finalesDe(A,F), transicionesDe(A,T1),
					transicionesReordenadas(T1,T2), recorrer(T2,F,I,P).

% TODO: recorrer(
recorrer(_,F,E,[]) :- member(E,F).
recorrer(T,F,E,[X|Xs]) :- member((E,X,Q),T), recorrer(T,F,Q,Xs).

% 10) PalabraMásCorta(+Automata, ?Palabra)
palabraMasCorta(_, _).

%-----------------
%----- Tests -----
%-----------------

% Algunos tests de ejemplo. Deben agregar los suyos.

test(1) :- forall(ejemplo(_, A),  automataValido(A)).
test(2) :- not((ejemploMalo(_, A),  automataValido(A))).
test(3) :- ejemplo(10, A), reconoce(A, [p, X, r, X, d, i, _, m, X, s]).
test(4) :- ejemplo(9, A), reconoce(A, [a,  b,  a,  b,  a,  b,  a,  b]).
test(5) :- ejemplo(7, A), reconoce(A, [a,  a,  a,  b,  b]).
test(6) :- ejemplo(7, A), not(reconoce(A, [b])).
test(7) :- ejemplo(2, A),  findall(P, palabraMasCorta(A, P), [[]]).
test(8) :- ejemplo(4, A),  findall(P, palabraMasCorta(A, P), Lista),
	length(Lista, 2), sort(Lista, [[a], [b]]).
test(9) :- ejemplo(5, A),  findall(P, palabraMasCorta(A, P), Lista),
	length(Lista, 2), sort(Lista, [[b], [c]]).
test(10) :- ejemplo(6, A),  findall(P, palabraMasCorta(A, P), [[b, a]]).
test(11) :- ejemplo(7, A),  findall(P, palabraMasCorta(A, P), [[a, b]]).
test(12) :- ejemplo(8, A),  findall(P, palabraMasCorta(A, P), Lista),
	length(Lista, 2), sort(Lista, [[a,a,b,f], [a,b,b,f]]).
test(13) :- ejemplo(10, A),  findall(P, palabraMasCorta(A, P), [[p,r,o,l,o,g]]).
test(14) :- forall(member(X, [2,4,5,6,7,8,9]), (ejemplo(X, A), hayCiclo(A))).
test(15) :- not((member(X, [1, 3, 10]), ejemplo(X, A), hayCiclo(A))).

% Test determinístico
test(16) :- ejemplo(1, A1), esDeterministico(A1), ejemplo(2, A2), esDeterministico(A2),
	ejemplo(3, A3), esDeterministico(A3), ejemplo(4, A4), not(esDeterministico(A4)),
	ejemplo(5, A5), esDeterministico(A5), ejemplo(6, A6), esDeterministico(A6),
	ejemplo(7, A7), esDeterministico(A7), ejemplo(8, A8), not(esDeterministico(A8)),
	ejemplo(9, A9), esDeterministico(A9), ejemplo(10, A), esDeterministico(A),
	ejemploMalo(1, M1), esDeterministico(M1), ejemploMalo(2, M2), esDeterministico(M2),
	ejemploMalo(3, M3), esDeterministico(M3), ejemploMalo(4, M4), esDeterministico(M4),
	ejemploMalo(5, M5), esDeterministico(M5), ejemploMalo(6, M6), esDeterministico(M6),
	ejemploMalo(7, M7), esDeterministico(M7).

% Test estados
test(17) :- ejemplo(1, A1), estados(A1,[s1,s2]), ejemplo(2, A2), estados(A2,[s1]),
	ejemplo(3, A3), estados(A3,[s1]), ejemplo(4, A4), estados(A4,[s1,s2,s3]),
	ejemplo(5, A5), estados(A5,[s1,s2,s3]), ejemplo(6, A6), estados(A6,[s1,s2,s3]),
	ejemplo(7, A7), estados(A7,[s1,s2,s3]), ejemplo(8, A8), estados(A8,[s1,s2,s3,s4,s5]),
	ejemplo(9, A9), estados(A9,[s1,s2]), ejemplo(10, A),
	estados(A,[s1,s10,s11,s12,s13,s14,s15,s2,s3,s4,s5,s6,s7,s8,s9]),
	ejemploMalo(1, M1), estados(M1,[s1,s2,s3]), ejemploMalo(2, M2), estados(M2,[s1,s2]),
	ejemploMalo(3, M3), estados(M3,[s1,s2,s3]), ejemploMalo(4, M4), estados(M4,[s1,s2,s3]),
	ejemploMalo(5, M5), estados(M5,[s1,s2,s3]), ejemploMalo(6, M6), estados(M6,[s1,s2,s3]),
	ejemploMalo(7, M7), estados(M7,[s1,s2,s3]).

% Test camino
test(18) :- ejemplo(1, A1), esCamino(A1,s1,s1,[s1]), esCamino(A1,s1,s2,[s1,s2]),
		not(esCamino(A1,s2,s1,_)),
	ejemplo(2, A2), esCamino(A2,s1,s1,[s1]), esCamino(A2,s1,s1,[s1,s1]),
		esCamino(A2,s1,s1,[s1,s1,s1]), esCamino(A2,s1,s1,[s1,s1,s1,s1,s1]),
		esCamino(A2,s1,s1,[s1,s1,s1,s1,s1,s1,s1,s1,s1,s1]),
	ejemplo(3, A3), esCamino(A3,s1,s1,[s1]), not(esCamino(A3,s1,s1,[s1,s1])),
	ejemplo(4, A4), esCamino(A4,s1,s2,[s1,s2]), esCamino(A4,s1,s2,[s1,s1,s1,s1,s1,s2]),
		esCamino(A4,s1,s3,[s1,s3]), not(esCamino(A4,s2,s3,_)), not(esCamino(A4,s3,s2,_)),
		not(esCamino(A4,s2,s1,_)), not(esCamino(A4,s3,s1,_)),
	ejemplo(5, A5), esCamino(A5,s1,s2,[s1,s1,s1,s2]), esCamino(A5,s1,s3,[s1,s1,s1,s3]),
		esCamino(A5,s2,s3,[s2,s3]), esCamino(A5,s1,s3,[s1,s1,s1,s1,s1,s2,s3]),
	ejemplo(6, A6), esCamino(A6,s1,s3,[s1,s2,s3]),
		esCamino(A6,s1,s3,[s1,s2,s3,s2,s3,s2,s3,s2,s3,s2,s3]),
	ejemplo(7, A7), esCamino(A7,s1,s2,[s1,s3,s2]),
		esCamino(A7,s1,s2,[s1,s3,s3,s3,s3,s2,s2,s2,s2,s2,s2,s2]),
	ejemplo(8, A8), esCamino(A8,s1,s1,[s1]), esCamino(A8,s1,s1,[s1,s2,s3,s1]),
		esCamino(A8,s1,s5,[s1,s2,s3,s4,s5]),
		esCamino(A8,s1,s5,[s1,s2,s3,s2,s3,s2,s3,s2,s3,s2,s3,s4,s5]),
	ejemplo(9, A9), esCamino(A9,s1,s1,[s1]), esCamino(A9,s1,s1,[s1,s2,s1]),
		esCamino(A9,s1,s1,[s1,s2,s1,s2,s1]),
	ejemplo(10, A), esCamino(A,s1,s11,[s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11]),
		esCamino(A,s1,s15,[s1,s2,s12,s13,s14,s15]),
	ejemploMalo(1, M1), not(esCamino(M1,s3,s1,_)), not(esCamino(M1,s3,s2,_)),
	ejemploMalo(2, M2), not(esCamino(M2,s1,s2,[s1,s2])),
	ejemploMalo(3, M3), not(esCamino(M3,s1,s2,_)),
	ejemploMalo(4, M4), not(esCamino(M4,s1,s2,_)), ejemploMalo(5, M5), esCamino(M5,s1,s3,[s1,s2,s3]),
	ejemploMalo(6, M6), esCamino(M6,s1,s3,[s1,s2,s3]),
	ejemploMalo(7, M7), esCamino(M7,s1,s3,[s1,s2,s3]).

% Test camino de longitud
test(19) :- ejemplo(1, A1), caminoDeLongitud(A1,2,[s1,s2],[a],s1,s2),
		not(caminoDeLongitud(A1,3,_,_,_,_)),
	ejemplo(2, A2), caminoDeLongitud(A2,5,[s1,s1,s1,s1,s1],[a,a,a,a],s1,s1),
	ejemplo(3, A3), not(caminoDeLongitud(A3,2,_,_,_,_)),
	ejemplo(4, A4), caminoDeLongitud(A4,5,[s1,s1,s1,s1,s3],[a,a,a,b],s1,s3),
	ejemplo(5, A5), caminoDeLongitud(A5,5,[s1,s1,s1,s2,s3],[a,a,b,c],s1,s3),
	ejemplo(6, A6), caminoDeLongitud(A6,7,[s1,s2,s3,s2,s3,s2,s3],[b,a,n,a,n,a],s1,s3),
		caminoDeLongitud(A6,6,[s2,s3,s2,s3,s2,s3],[a,n,a,n,a],s2,s3),
		caminoDeLongitud(A6,5,[s3,s2,s3,s2,s3],[n,a,n,a],s3,s3),
		caminoDeLongitud(A6,4,[s2,s3,s2,s3],[a,n,a],s2,s3),
	ejemplo(7, A7), caminoDeLongitud(A7,7,[s1,s3,s3,s3,s2,s2,s2],[a,a,a,b,b,b],s1,s2),
	ejemplo(8, A8), caminoDeLongitud(A8,2,[s3,s2],[b],s3,s2), caminoDeLongitud(A8,2,[s3,s4],[b],s3,s4),
	ejemplo(9, A9), caminoDeLongitud(A9,6,[s1,s2,s1,s2,s1,s2],[a,b,a,b,a],s1,s2),
		caminoDeLongitud(A9,6,[s2,s1,s2,s1,s2,s1],[b,a,b,a,b],s2,s1),
	ejemplo(10, A), caminoDeLongitud(A,7,[s1,s2,s12,s13,s14,s15,s11],[p,r,o,l,o,g],s1,s11),
		caminoDeLongitud(A,10,[s1,s2,s3,s4,s5,s6,s7,s8,s9,s10],[p,a,r,a,d,i,g,m,a],s1,s10),
	ejemploMalo(1, M1), caminoDeLongitud(M1,3,[s1,s2,s3],[b,a],s1,s3),
		 caminoDeLongitud(M1,7,[s1,s1,s1,s1,s2,s2,s2],[a,a,a,b,b,b],s1,s2),
	ejemploMalo(2, M2), caminoDeLongitud(M2,3,[s1,s1,s1],[a,a],s1,s1),
		 caminoDeLongitud(M2,4,[s2,s2,s2,s2],[b,b,b],s2,s2),
	ejemploMalo(3, M3), not( (between(2,10,N), caminoDeLongitud(M3,N,_,_,_,s2)) ),
		caminoDeLongitud(M3,2,[s1,s3],[a],s1,s3), caminoDeLongitud(M3,2,[s1,s3],[a],s1,s3),
	ejemploMalo(4, M4), not( (between(2,10,N), caminoDeLongitud(M4,N,_,_,_,s2)) ),
		caminoDeLongitud(M4,2,[s2,s3],[b],s2,s3), caminoDeLongitud(M4,2,[s1,s3],[a],s1,s3),
	ejemploMalo(5, M5), findall(C,caminoDeLongitud(M5,2,C,[b],s2,s3),Caminos5), length(Caminos5,1),
	ejemploMalo(6, M6), findall(C,caminoDeLongitud(M6,2,C,[a],s1,s2),Caminos6), length(Caminos6,2),
	ejemploMalo(7, M7), caminoDeLongitud(M7,3,[s1,s2,s3],[a,b],s1,s3).

% Test alcanzable
test(20) :- ejemplo(1, A1), not(alcanzable(A1,s1)), alcanzable(A1,s2),
	ejemplo(2, A2), alcanzable(A2,s1), ejemplo(3, A3), not(alcanzable(A3,s1)),
	ejemplo(4, A4), alcanzable(A4,s1), alcanzable(A4,s2), alcanzable(A4,s3),
	ejemplo(5, A5), alcanzable(A5,s1), alcanzable(A5,s2), alcanzable(A5,s3),
	ejemplo(6, A6), not(alcanzable(A6,s1)), alcanzable(A6,s2), alcanzable(A6,s3),
	ejemplo(7, A7), not(alcanzable(A7,s1)), alcanzable(A7,s2), alcanzable(A7,s3),
	ejemplo(8, A8), alcanzable(A8,s1), alcanzable(A8,s2), alcanzable(A8,s3),
		alcanzable(A8,s4), alcanzable(A8,s5),
	ejemplo(9, A9), alcanzable(A9,s1), alcanzable(A9,s2),
	ejemplo(10, A), not(alcanzable(A,s1)), alcanzable(A,s2), alcanzable(A,s3),
		alcanzable(A,s4), alcanzable(A,s5), alcanzable(A,s6),
		alcanzable(A,s7), alcanzable(A,s8), alcanzable(A,s9),
		alcanzable(A,s10), alcanzable(A,s11), alcanzable(A,s12),
		alcanzable(A,s13), alcanzable(A,s14), alcanzable(A,s15),
	ejemploMalo(1, M1), alcanzable(M1,s1), alcanzable(M1,s2), alcanzable(M1,s3),
	ejemploMalo(2, M2), alcanzable(M2,s1), not(alcanzable(M2,s2)),
	ejemploMalo(3, M3), not(alcanzable(M3,s1)), not(alcanzable(M3,s2)), alcanzable(M3,s3),
	ejemploMalo(4, M4), not(alcanzable(M4,s1)), not(alcanzable(M4,s2)), alcanzable(M4,s3),
	ejemploMalo(5, M5), not(alcanzable(M5,s1)), alcanzable(M5,s2), alcanzable(M5,s3),
	ejemploMalo(6, M6), not(alcanzable(M6,s1)), alcanzable(M6,s2), alcanzable(M6,s3),
	ejemploMalo(7, M7), not(alcanzable(M7,s1)), alcanzable(M7,s2), alcanzable(M7,s3).

% Test valido
test(21) :- forall(between(1,10,N), (ejemplo(N, A),automataValido(A))), 
			forall(between(1,7,N), (ejemploMalo(N, A),not(automataValido(A)))).

% Test ciclo
test(22) :- ejemplo(1, A1), not(hayCiclo(A1)), ejemplo(2, A2), hayCiclo(A2),
			ejemplo(3, A3), not(hayCiclo(A3)), ejemplo(4, A4), hayCiclo(A4),
			ejemplo(5, A5), hayCiclo(A5), ejemplo(6, A6), hayCiclo(A6),
			ejemplo(7, A7), hayCiclo(A7), ejemplo(8, A8), hayCiclo(A8),
			ejemplo(9, A9), hayCiclo(A9), ejemplo(10, A), not(hayCiclo(A)).

% Test reconoce
test(23) :- ejemplo(1, A1), reconoce(A1,[a]), not(reconoce(A1,[a,a])),
	ejemplo(2, A2), reconoce(A2,[a]), reconoce(A2,[a,a,a,a,a]),
	ejemplo(3, A3), reconoce(A3,[]), not(reconoce(A3,[_])),
	ejemplo(4, A4), reconoce(A4,[a]), reconoce(A4,[a,a,a,a]),
		reconoce(A4,[b]), reconoce(A4,[a,a,a,a,b]), not(reconoce(A4,[b,b])),
	ejemplo(5, A5), not(reconoce(A5,[a])), reconoce(A5,[b]), reconoce(A5,[a,b]),
		reconoce(A5,[a,a,a,a,b]), reconoce(A5,[a,a,a,a,c]), reconoce(A5,[b,c]),
	ejemplo(6, A6), not(reconoce(A6,[a])), not(reconoce(A6,[b])), reconoce(A6,[b,a]),
		not(reconoce(A6,[b,a,n])), reconoce(A6,[b,a,n,a]), reconoce(A6,[b,a,n,a,n,a]),
	ejemplo(7, A7), not(reconoce(A7,[a])), not(reconoce(A7,[a,a])), reconoce(A7,[a,b]),
		reconoce(A7,[a,a,a,a,a,b,b,b]), not(reconoce(A7,[b])), reconoce(A7,[a,b,b,b]),
	ejemplo(8, A8), reconoce(A8,[a,b,b,f]), reconoce(A8,[a,a,b,f]), reconoce(A8,[a,b,b,b,b,b,b,f]),
		reconoce(A8,[a,b,a,a,b,b,a,b,f]), reconoce(A8,[a,a,a,a,a,b,f]), not(reconoce(A8,[_,_,_])),
	ejemplo(9, A9), reconoce(A9,[]), reconoce(A9,[a,b]), reconoce(A9,[a,b,a,b,a,b]),
	ejemplo(10, A), reconoce(A,[p,a,r,a,d,i,g,m,a]), reconoce(A,[p,r,o,l,o,g]),
		reconoce(A,[p,a,r,a,d,i,g,m,a,s]).

% Test palabra mas corta
test(24) :- ejemplo(1, A1), palabraMasCorta(A1, [a]), ejemplo(2, A2), palabraMasCorta(A2, []),
	ejemplo(3, A3), palabraMasCorta(A3, []),
	ejemplo(4, A4), palabraMasCorta(A4, [a]), palabraMasCorta(A4, [b]),
	ejemplo(5, A5), palabraMasCorta(A5, [b]), palabraMasCorta(A5, [c]),
	ejemplo(6, A6), palabraMasCorta(A6, [ba]), ejemplo(7, A7), palabraMasCorta(A7, [ab]),
	ejemplo(8, A8), palabraMasCorta(A8, [aabf]), palabraMasCorta(A8, [abbf]),
	ejemplo(9, A9), palabraMasCorta(A9, []), ejemplo(10, A), palabraMasCorta(A, [prolog]).

tests :- forall(between(1, 24, N), test(N)).

% otros Tests (En estos tests no queremos que nos devuelva true, sino que queremos ver qué se genera):

% Test estados
testEstados(E1q2,E2q1,E3q1,E4q3,E5q3,E6q3,E7q3,E8q5,E9q2,Eq15,F1q3,F2q2,F3q3,F4q3,F5q3,F6q3,F7q3) :-
	ejemplo(1, A1), estados(A1,E1q2), ejemplo(2, A2), estados(A2,E2q1),
	ejemplo(3, A3), estados(A3,E3q1), ejemplo(4, A4), estados(A4,E4q3),
	ejemplo(5, A5), estados(A5,E5q3), ejemplo(6, A6), estados(A6,E6q3),
	ejemplo(7, A7), estados(A7,E7q3), ejemplo(8, A8), estados(A8,E8q5),
	ejemplo(9, A9), estados(A9,E9q2), ejemplo(10, A), estados(A,Eq15),
	ejemploMalo(1, M1), estados(M1,F1q3), ejemploMalo(2, M2), estados(M2,F2q2),
	ejemploMalo(3, M3), estados(M3,F3q3), ejemploMalo(4, M4), estados(M4,F4q3),
	ejemploMalo(5, M5), estados(M5,F5q3), ejemploMalo(6, M6), estados(M6,F6q3),
	ejemploMalo(7, M7), estados(M7,F7q3).
	% Debería devolver:
	% Eiqṇ = [s1,...,sṇ], Fiqṇ = [s1,...,sṇ]

% Test caminos
testCaminos(I1s1,F1s2,I2s1,F2s1,I3s1,F3s1,I4s1,F4s3,I5s1,F5s3,I6s1,F6s2,
											I7s3,F7s2,I8s1,F8s5,I9s2,F9s1,I0a1,I0s10) :-
	ejemplo(1, A1), esCamino(A1,I1s1,F1s2,[s1,s2]), not(esCamino(A1,_,_,[s2,s1])),
	ejemplo(2, A2), esCamino(A2,I2s1,F2s1,[s1]), esCamino(A2,I2s1,F2s1,[s1,s1]),
		esCamino(A2,I2s1,F2s1,[s1,s1,s1]), esCamino(A2,I2s1,F2s1,[s1,s1,s1,s1,s1]),
	ejemplo(3, A3), esCamino(A3,I3s1,F3s1,[s1]),
	ejemplo(4, A4), not(esCamino(A4,_,_,[s2,s3])), esCamino(A4,I4s1,F4s3,[s1,s3]),
	ejemplo(5, A5), esCamino(A5,I5s1,F5s3,[s1,s1,s1,s2,s3]), esCamino(A5,I5s1,F5s3,[s1,s1,s3]),
	ejemplo(6, A6), esCamino(A6,I6s1,F6s2,[s1,s2]), esCamino(A6,I6s1,F6s2,[s1,s2,s3,s2,s3,s2,s3,s2]),
	ejemplo(7, A7), esCamino(A7,I7s3,F7s2,[s3,s2,s2,s2,s2]), esCamino(A7,I7s3,F7s2,[s3,s3,s3,s3,s2]),
	ejemplo(8, A8), esCamino(A8,I8s1,F8s5,[s1,s2,s3,s4,s5]),
		esCamino(A8,I8s1,F8s5,[s1,s2,s3,s1,s2,s3,s2,s3,s4,s5]),
	ejemplo(9, A9), esCamino(A9,I9s2,F9s1,[s2,s1]), esCamino(A9,I9s2,F9s1,[s2,s1,s2,s1,s2,s1,s2,s1]),
	ejemplo(10, A), esCamino(A,I0a1,I0s10,[s1,s2,s3,s4,s5,s6,s7,s8,s9,s10]).
	% Debería devolver:
	% Iisṇ = sṇ, Fisṇ = sṇ

% Test camino reversible Con estados instanciados (-Camino,+Ejemplo(N°),+Inicial,+Final)
% Debería generar todos los posibles caminos entre el par de estados dados.
testCaminoReversible1(Camino,A,Inicial,Final) :-
	ejemplo(A,M), esCaminoReversible(M,Inicial,Final,Camino).
	% Deberían devolver (según el número de ejemplo ingresado y los estados incial y final):
	% 1:	s1,s1: [s1]		s1,s2: [s1,s2]		s2,s2: [s2]
	% 2:	s1,s1: [s1-...-s1]
	% 3:	s1,s1: [s1]
	% 4:	s1,s1: [s1-...-s1]	s1,s2: [s1-...-s1-s2]	s2,s2: [s2]		
		%	s1,s3: [s1-...-s1-s3]	s3,s3: [s3]
	% 5:	s1,s1: [s1-...-s1]	s1,s2: [s1-...-s1-s2]	s2,s2: [s2]		s2,s3: [s2-s3]
		%	s3,s3: [s3]		s1,s3: [s1-...s1-s3], [s1-...s1-s2-s3]
	% 6:	s1,s1: [s1]		s1,s2: [s1-s2-s3-s2...-s3-s2]	s2,s2: [s2-s3-s2-...-s3-s2]
		%	s2-s3: [s2-s3-...-s2-s3]	s1,s3: [s1-s2-s3-...-s2-s3]
		%	s3,s3: [s3-s2-s3-...-s2-s3]		s3,s2: [s3-s2-...-s3-s2]
	% 7:	s1,s1: [s1]		s1-s2: [s1-s3-...-s3-s2-...-s2]		s2,s2: [s2-...-s2]
		%	s3,s2: [s3-...-s3-s2-...-s2]	s3,s3: [s3-...-s3]	s1,s3: [s1-s3-...-s3]
	% 8:	s1,s1: [s1-s2-s3-.*.-s1]	s1,s2:	[s1-s2-s3-.*.-s1-s2]	s1,s3: [s1-s2-s3-.*-s3]
		%	s3,s3: [s3-.*.-s3]		s2,s3: [s2-s3-.*.-s2-s3]	s2,s2: [s2-s3-.*.-s2]
		%	s2,s1: [s2-s3-.*.-s3-s1]	s3,s1: [s3-.*.-s3-s1]	s3,s2: [s3-.*.-s2]
		% 	*: Alguna cantidad de loops s3-s2-s3 o s3-s1-s2-s3
	% 9:	s1,s1: [s1-s2-s1...-s2-s1]		s1,s2: [s1-s2-...-s1-s2]
		%	s2,s2: [s2-s1-s2-...-s1-s2]		s2,s1: [s2-s1-s2-...-s1-s2]

% Test camino reversible para todo par de estados (-Camino,+Ejemplo(N°))
% Debería generar todos los caminos del automata.
testCaminoReversible2(Camino,A) :-
	% FIXME: primero toma el inicial, después el final y después busca los caminos.
		% Si hay infinitos caminos entre algún par de estados, no va a recorrer los demás.
		% Solución: debería tomar en otro orden.
		% Otra solución: Quitar este test, no es indispensable.
	ejemplo(A,M), estados(M,Estados), member(Inicial,Estados), member(Final,Estados),
	esCaminoReversible(M,Inicial,Final,Camino).
	% Deberían devolver (según el número de ejemplo ingresado):
	% 1:	[si], [s1-s2]
	% 2:	[si], [s1-...-s1]
	% 3:	[s1]
	% 4:	[si], [s1-...-s1], [s1-...-s1-s2], [s1-...-s1-s3]
	% 5:	[si], [s2,s3], [s1-...-s1], [s1-...-s1-s2], [s1-...-s1-s3], [s1-...-s1,s2,s3]
	% 6:	[si], [s1-s2-s3-....-s2-s3], [s2-s3-....-s2-s3], [s3-s2-....-s3-s2]
	% 7:	[si], [s1-s3-...-s3], [s1-s3-...-s3-s2-...-s2], [s2-...-s2], [s3-...-s3-s2-...-s2],
		%	[s3-...-s3]
	% 8:	[si], [s1-s2], [s1-s2-s3], [s1-s2-s3-s2], [s1-s2-s3-s1], [s1-s2-s3-s4], [s1-s2-s3-s4-s5],
		%	[s1-s2-s3-.*.-s2-s3-s4],  [s1-s2-s3-.*.-s2-s3-s4-s5]
		% 	*: Alguna cantidad de loops s3-s2-s3 o s3-s1-s2-s3
	% 9:	[si], [s1-s2-....-s1-s2], [s2-s2-....-s2-s1]
	% 10:	[si], subcamino de [s1-....-s11], subcamino de [s1-s2-s12-...-s15-s11]

% Test camino reversible sin instanciar estados (-Camino,+Ejemplo(N°))
% Debería generar todos los caminos del automata (igual que testCaminoReversible2).
testCaminoReversible3(Camino,A) :-
	ejemplo(A,M), esCaminoReversible(M,_,_,Camino).

% Test camino de longitud (?Ejemplo(N°), -Camino, +MaxLongitud)
% Debería generar todos los caminos de longitud menor o igual a MaxLongitud.
% Si no se instancia el número de autómata, se ejecuta para los 10.
testCaminoDeLongitud(A, Camino, MaxLongitud) :-
	between(1,10,A), ejemplo(A,M), between(2,MaxLongitud,N),
	caminoDeLongitud(M,N,Camino,_,_,_).

% Test reconoce (-Palabra, +Ejemplo(N°))
testReconoce(Palabra, A) :-
	ejemplo(A,M), reconoce(M,Palabra).
	% Deberían devolver (según el número de ejemplo ingresado):
	% 1:	[a]
	% 2:	[], [a....a]
	% 3:	[]
	% 4:	[a...a], [b], [a...ab]
	% 5:	[b], [c], [b,c], [a...ab], [a...ac], [a...abc]
	% 6:	[ba], [bana...na]
	% 7:	[ab], [a...ab...b]
	% 8:	[(aa|ab)·(aaa|aab|ba|bb)*·bf] ← Notación de TLeng (Expresión regular)
	% 9:	[], [ab], [ab...ab]
	% 10:	[prolog], [paradigma], [paradigmas]

%Test palabra mas corta (-Palabra, ?Ejemplo(N°))
testPalabraMasCorta(Palabra, A) :-
	between(1,10,A), ejemplo(A,M), palabraMasCorta(M,Palabra).
	% Deberían devolver (según el número de ejemplo):
	% 1:	[a]
	% 2:	[]
	% 3:	[]
	% 4:	[a], [b]
	% 5:	[b], [c]
	% 6:	[ba]
	% 7:	[ab]
	% 8:	[aabf], [abbf]
	% 9:	[]
	% 10:	[prolog]

%% TODO: Estaría bueno hacer un generador de autómatas...
%generadorAutomatas(a(1,[1],[])).
%generadorAutomatas(a(1,Fs,[(p,e,q)|Ts])) :- generadorAutomata(1,Fs,Ts), .
