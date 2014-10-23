%Autómatas de ejemplo. Si agregan otros, mejor.

ejemplo(1, a(s1, [s2], [(s1, a, s2)])).
ejemplo(2, a(s1, [s1], [(s1, a, s1)])).
ejemplo(3, a(s1, [s1], [])).
ejemplo(4, a(s1, [s2, s3], [(s1, a, s1), (s1, a, s2), (s1, b, s3)])).
ejemplo(5, a(s1, [s2, s3], [(s1, a, s1), (s1, b, s2), (s1, c, s3), (s2, c, s3)])).
ejemplo(6, a(s1, [s3], [(s1, b, s2), (s3, n, s2), (s2, a, s3)])).
ejemplo(7, a(s1, [s2], [(s1, a, s3), (s3, a, s3), (s3, b, s2), (s2, b, s2)])).
ejemplo(8, a(s1, [s5], [(s1, a, s2), (s2, a, s3), (s2, b, s3), (s3, a, s1), (s3, b, s2), (s3, b, s4), (s4, f, s5)])). % No deterministico :)
ejemplo(9, a(s1, [s1], [(s1, a, s2), (s2, b, s1)])).
ejemplo(10, a(s1, [s10, s11], 
        [(s2, a, s3), (s4, a, s5), (s9, a, s10), (s5, d, s6), (s7, g, s8), (s15, g, s11), (s6, i, s7), (s13, l, s14), (s8, m, s9), (s12, o, s13), (s14, o, s15), (s1, p, s2), (s3, r, s4), (s2, r, s12), (s10, s, s11)])).

ejemploMalo(1, a(s1, [s2], [(s1, a, s1), (s1, b, s2), (s2, b, s2), (s2, a, s3)])). %s3 es un estado sin salida.
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


%%Predicados pedidos.

% 1) esDeterministico(+Automata) :- ∀ (q1,e1,p1),(q2,e2,p2) transiciones:
									% si q1=q2 y e1=e2 =>
									% p1=p2.
esDeterministico(A) :- forall((transicionesDe(A,Transiciones),
						member((Q,E,P1),Transiciones), member((Q,E,P2),Transiciones)),
						(P1 = P2)).

% 2) estados(+Automata, -Estados) :- Estados = inicial(Automata) U finales(Automata) U
									% estadosDeTransiciones
estados(A, EstadosOrdenados) :- inicialDe(A,Inicial), finalesDe(A,Finales), transicionesDe(A,Transiciones),
								estadosDeTransiciones(Transiciones,EstadosDeTransiciones),
								union([Inicial|Finales],EstadosDeTransiciones,Estados),
								sort(Estados,EstadosOrdenados).

%estadosDeTransiciones(+Transiciones,-Estados) :- Estados = [q | (q,e,p) ∈ Transiciones] U
												% [p | (q,e,p) ∈ Transiciones]
estadosDeTransiciones([],[]).
estadosDeTransiciones([(Q,_,P)|Transiciones],MasEstados) :-
											estadosDeTransiciones(Transiciones,Estados),
											union([Q,P],Estados,MasEstados).

% 3) esCamino(+Automata, ?EstadoInicial, ?EstadoFinal, +Camino)
%Nos fijamos en las transiciones y vemos si hay camino en un paso, o si hay camino a n-1 pasos desde un estado posterior al estado inicial.
esCamino(_, S1, S1, [S1]).
esCamino(A, S1, S2, [S1,S2]):- estadoSiguiente(A,S1,S2).
esCamino(A, S1, S2, [S1|CS]):- estadoSiguiente(A,S1,SMedio), SMedio \= S2,
								not(member(SMedio,CS)), esCamino(A,SMedio,S2,CS).
%Agregamos la restricción 'not(member(SMedio,CS))' para evitar caer en ciclos infinitos.

%estadoSiguiente(+Automata, +Estado, -Siguiente) :- ∃ (q,e,p) transición tq Estado=q y Siguiente=p
estadoSiguiente(A,E,S):- transicionesDe(A,T), member((E,_,S),T).

% 4) ¿el predicado anterior es o no reversible con respecto a Camino y por qué?
% Responder aquí.

% 5) caminoDeLongitud(+Automata, +N, -Camino, -Etiquetas, ?S1, ?S2)
%La misma idea, pero restringiendo la longitud del camino.
caminoDeLongitud(_,1,[S1],[],S1,S1).
caminoDeLongitud(A,2,[S1,S2],[E],S1,S2) :- transicionesDe(A,T), member((S1,E,S2),T).
caminoDeLongitud(A,N,[S1|Cs],[E|Es],S1,S2):- N>2, Nm1 is N-1,
												transicionesDe(A,T), member((S1,E,SMedio),T),
												caminoDeLongitud(A,Nm1,Cs,Es,SMedio,S2).
%Agregamos la restricción 'N>2' para evitar colisión con la segunda regla.

% 6) alcanzable(+Automata, +Estado) :- ∃ N2 tq ∃ (q0,...,q) camino de longitud N.
alcanzable(A, E):- inicialDe(A,I), estados(A,Estados), length(Estados,CantEstados), CEMasUno is CantEstados+1,
					not(not((between(2,CEMasUno,N), caminoDeLongitud(A,N,_,_,I,E)))).

% 7) automataValido(+Automata)
automataValido(_).

%--- NOTA: De acá en adelante se asume que los autómatas son válidos.


% 8) hayCiclo(+Automata)
hayCiclo(_).

% 9) reconoce(+Automata, ?Palabra)
reconoce(_, _).

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
test(8) :- ejemplo(4, A),  findall(P, palabraMasCorta(A, P), Lista), length(Lista, 2), sort(Lista, [[a], [b]]).
test(9) :- ejemplo(5, A),  findall(P, palabraMasCorta(A, P), Lista), length(Lista, 2), sort(Lista, [[b], [c]]).
test(10) :- ejemplo(6, A),  findall(P, palabraMasCorta(A, P), [[b, a]]).
test(11) :- ejemplo(7, A),  findall(P, palabraMasCorta(A, P), [[a, b]]).
test(12) :- ejemplo(8, A),  findall(P, palabraMasCorta(A, P), Lista), length(Lista, 2), sort(Lista, [[a,  a,  b,  f], [a,  b,  b,  f]]).
test(13) :- ejemplo(10, A),  findall(P, palabraMasCorta(A, P), [[p, r, o, l, o, g]]).
test(14) :- forall(member(X, [2, 4, 5, 6, 7, 8, 9]), (ejemplo(X, A), hayCiclo(A))).
test(15) :- not((member(X, [1, 3, 10]), ejemplo(X, A), hayCiclo(A))).

%Test determinístico
test(16) :- ejemplo(1, A1), esDeterministico(A1),
			ejemplo(2, A2), esDeterministico(A2),
			ejemplo(3, A3), esDeterministico(A3),
			ejemplo(4, A4), not(esDeterministico(A4)),
			ejemplo(5, A5), esDeterministico(A5),
			ejemplo(6, A6), esDeterministico(A6),
			ejemplo(7, A7), esDeterministico(A7),
			ejemplo(8, A8), not(esDeterministico(A8)),
			ejemplo(9, A9), esDeterministico(A9),
			ejemplo(10, A), esDeterministico(A),
			ejemploMalo(1, M1), esDeterministico(M1),
			ejemploMalo(2, M2), esDeterministico(M2),
			ejemploMalo(3, M3), esDeterministico(M3),
			ejemploMalo(4, M4), esDeterministico(M4),
			ejemploMalo(5, M5), esDeterministico(M5),
			ejemploMalo(6, M6), esDeterministico(M6),
			ejemploMalo(7, M7), esDeterministico(M7).

%Test alcanzable
test(22) :- ejemplo(1, A1), not(alcanzable(A1,s1)), alcanzable(A1,s2),
			ejemplo(2, A2), alcanzable(A2,s1),
			ejemplo(3, A3), not(alcanzable(A3,s1)),
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

%Test estados
test(17) :- ejemplo(1, A1), estados(A1,[s1,s2]),
			ejemplo(2, A2), estados(A2,[s1]),
			ejemplo(3, A3), estados(A3,[s1]),
			ejemplo(4, A4), estados(A4,[s1,s2,s3]),
			ejemplo(5, A5), estados(A5,[s1,s2,s3]),
			ejemplo(6, A6), estados(A6,[s1,s2,s3]),
			ejemplo(7, A7), estados(A7,[s1,s2,s3]),
			ejemplo(8, A8), estados(A8,[s1,s2,s3,s4,s5]),
			ejemplo(9, A9), estados(A9,[s1,s2]),
			ejemplo(10, A), estados(A,[s1,s10,s11,s12,s13,s14,s15,s2,s3,s4,s5,s6,s7,s8,s9]),
			ejemploMalo(1, M1), estados(M1,[s1,s2,s3]),
			ejemploMalo(2, M2), estados(M2,[s1,s2]),
			ejemploMalo(3, M3), estados(M3,[s1,s2,s3]),
			ejemploMalo(4, M4), estados(M4,[s1,s2,s3]),
			ejemploMalo(5, M5), estados(M5,[s1,s2,s3]),
			ejemploMalo(6, M6), estados(M6,[s1,s2,s3]),
			ejemploMalo(7, M7), estados(M7,[s1,s2,s3]).

%test(30) :- ejemplo(1, A1),
%			ejemplo(2, A2),
%			ejemplo(3, A3),
%			ejemplo(4, A4),
%			ejemplo(5, A5),
%			ejemplo(6, A6),
%			ejemplo(7, A7),
%			ejemplo(8, A8),
%			ejemplo(9, A9),
%			ejemplo(10, A),
%			ejemploMalo(1, M1),
%			ejemploMalo(2, M2),
%			ejemploMalo(3, M3),
%			ejemploMalo(4, M4),
%			ejemploMalo(5, M5),
%			ejemploMalo(6, M6),
%			ejemploMalo(7, M7),

tests :- forall(between(1, 15, N), test(N)). %IMPORTANTE: Actualizar la cantidad total de tests para contemplar los que agreguen ustedes.
