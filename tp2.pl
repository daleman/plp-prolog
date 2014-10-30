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
ejemplo(11, a(s1, [s2], [(s1,a,s2),(s1,a,s3),(s3,a,s4),(s4,a,s3)])).

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
% Utilizamos el predicado union(A,B,C) que asegura que C tenga los elementos de B más los
% elementos de A que no estén en B. Si en B no hay repetidos, entonces en C no va a haber repetidos.
% Si en A hay repetidos, el predicado se encarga de eliminarlos. 

% Auxiliar: obtiene los estados de un autómata a partir de las transiciones del mismo.
% estadosDeTransiciones(+Transiciones,-Estados) :- estados = [q | (q,e,p) ∈ transiciones] U
												% [p | (q,e,p) ∈ transiciones]
estadosDeTransiciones([],[]).
estadosDeTransiciones([(Q,_,P)|Transiciones],MasEstados) :-
											estadosDeTransiciones(Transiciones,Estados),
											union([Q,P],Estados,MasEstados).

% 3) esCamino(+Automata, ?EstadoInicial, ?EstadoFinal, +Camino)
% Un camino de un solo estado es un camino válido entre un estado y él mismo.
% Dado un camino válido entre un estado medio y el final, si existe una transición entre
% el estado inicial y el estado medio, obtenemos un camino válido entre el estado inicial y el final.
esCamino(A, E, E, [E]) :- estados(A, Estados), member(E, Estados), !.
esCamino(A, Inicial, Final, [Inicial,Medio|Es]) :-
	transicionesDe(A,T), member((Inicial,_,Medio),T),
	esCamino(A,Medio,Final,[Medio|Es]), !.
% Agregamos el '!' para que sólo devuelva una unificación. Si para un par de estados consecutivos en
% el camino, existen dos transiciones posibles, 'esCamino' devolvería otra unificación pero idéntica.
% Como todas las unificaciones posibles son iguales (determinadas por los estados primero y último
% del camino), sólo le permitimos devolver una. Esta aclaración es válida teniendo en cuenta que el
% parámetro 'Camino' siempre viene instanciado.

% 4) ¿el predicado anterior es o no reversible con respecto a Camino y por qué?
% No, al agregar el '!' al final, le impedimos que genere más de un camino distinto, por lo que si
% se utilizara sin instanciar 'Camino' devolvería a lo sumo un camino posible¹. Además, el hecho de
% que 'Camino' esté instanciado nos permite recorrerlo para obtener los estados inicial y final en
% el caso que estos no estén instanciados. Si los estados inicial y final están instanciados pero
% el camino no lo está, el predicado debería generar un camino entre dicho par de estados, pero
% podría quedarse ciclando inifinitamente y nunca llegar al estado inicial² (notar que construye el
% camino desde el final). Si los estados inicial y final no están instanciados también habría un
% problema. El predicado no se colgaría pero podría quedarse en un ciclo y no generar todos los
% caminos posibles³.

%1:	?- ejemplo(2,A), esCamino(A,s1,s1,Camino).
	% Camino = [s1].
	% Devuelve sólo el camino [s1] pero hay infinitos caminos entre s1 y s1.
%2:	?- ejemplo(4,A), esCamino(A,s1,s2,Camino).
	% ...
	% Se cuelga ya que se queda generando caminos de la pinta [s1,...,s1] y nunca llega a s2.
%3 (sacando el '!'):
%	?- ejemplo(4,A), esCamino(A,Inicial,Final,Camino).
	% Inicial = Final = s1
	% Camino = [s1], [s1,s1], [s1,s1,s1], ...
	% Siempre que genera un nuevo camino lo hace a través de la transición (s1,a,s1), por lo que
	% nunca va a generar el camino [s1,s2].

% En el apéndice implementamos una versión reversible del predicado 'esCamino'.

% 5) caminoDeLongitud(+Automata, +N, -Camino, -Etiquetas, ?S1, ?S2)
% Un camino de un solo estado es un camino válido de longitud 1 entre un estado y él mismo.
% Un camino de longitud 2 es válido si hay una transición entre el par de estados involucrados.
% Dado un camino válido de longitud N-1 entre un estado medio y el final, si existe una
% transición entre el estado inicial y el estado medio, obtenemos un camino válido de longitud N
% entre el estado inicial y el final. Como la cantidad de caminos de una longitud dada es finita,
% este predicado siempre encuentra todos los caminos de la longitud especificada (no podría
% quedarse ciclando porque en seguida superaría tal longitud).
caminoDeLongitud(A,1,[S1],[],S1,S1) :- estados(A, Estados), member(S1, Estados).
caminoDeLongitud(A,2,[S1,S2],[E],S1,S2) :- transicionesDe(A,T), member((S1,E,S2),T).
caminoDeLongitud(A,N,[S1|Cs],[E|Es],S1,S2):- N>2, Nm1 is N-1,
												transicionesDe(A,T), member((S1,E,SMedio),T),
												caminoDeLongitud(A,Nm1,Cs,Es,SMedio,S2).
% Agregamos la restricción 'N>2' en la tercera regla para evitar colisión con la segunda regla.

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

% Auxiliar: transicionesSalientes(+Automata) :- ∀ E estado, ¬(E final) => ∃ algunaTransicionSaliente.
transicionesSalientes(A) :- forall(
					(estados(A,Estados), member(E,Estados), finalesDe(A,Fs), not(member(E,Fs))),
					algunaTransicionSaliente(A,E)
								).

% Auxiliar: todosAlcanzables(+Automata) :- ∀ E estado, ¬(E inicial) => alcanzable(E)
todosAlcanzables(A) :- forall(
					(estados(A,Estados), member(E,Estados), inicialDe(A,I), E\=I),
					alcanzable(A,E)
							).

% Auxiliar: algunFinal(+Automata) :- length (finales) > 0
algunFinal(A):- finalesDe(A,Finales), length(Finales,N), N>0.

% Auxiliar: sinFinalesRepetidos(+Automata) :- ∀ E estado final, |finales|_E = 1
sinFinalesRepetidos(A) :- forall(
					(finalesDe(A,Finales), member(E,Finales)),
					cuenta(E,Finales,1)
								).

% Auxiliar: sinTransicionesRepetidas(+Automata) :- ∀ T transicion, |transiciones|_T = 1
sinTransicionesRepetidas(A) :- forall(
					(transicionesDe(A,Transiciones), member(T,Transiciones)),
					cuenta(T,Transiciones,1)
									).

% Auxiliar: algunaTransicionSaliente(+Automata,+Estado) :- ∃ T transicion de la forma (Estado,_,_)
algunaTransicionSaliente(A,E) :- not(not((
					transicionesDe(A,Transiciones), member((E,_,_),Transiciones)
										))).

% Auxiliar: cuenta(+Elemento,+Lista,-N) :- Cantidad de apariciones del elemento en la lista.
cuenta(_,[],0).
cuenta(E,[E|FS],Nm1) :- cuenta(E,FS,N), Nm1 is N+1.
cuenta(E,[F|FS],N) :- E\=F, cuenta(E,FS,N).

%--- NOTA: De acá en adelante se asume que los autómatas son válidos.

% 8) hayCiclo(+Automata) :- ∃ E estado tq ∃ (E,....,E) camino
hayCiclo(A) :- estados(A,Estados), length(Estados,CantEstados), CEMasUno is CantEstados+1,
				between(2,CEMasUno,N), member(S1,Estados), caminoDeLongitud(A,N,_,_,S1,S1), !.
% Agregamos el '!' para que sólo devuelva una unificación. Es posible que haya más de un
% 'caminoDeLongitud' y varios valores de 'N' par los cuales encontrarlos. Sin embargo, sólo
% nos interesa recibir un true o false, así que si encuentra un ciclo, dejamos de buscar otros.
% La longitud máxima de un ciclo es la cantidad de estados más uno.

% 9) reconoce(+Automata, ?Palabra) :- ∃ (s0,...,sn,s(n+1)) camino con s0 inicial y s(n+1) final tq
									% palabra = (a0,...,an) = lista de etiquetas del camino.
reconoce(A,P) :- nonvar(P), length(P,N), inicialDe(A,I), finalesDe(A,Finales), M is N+1,
					member(F,Finales), caminoDeLongitud(A,M,_,P,I,F).
reconoce(A,P) :- var(P), not(hayCicloPalabra(A)), estados(A,Estados), length(Estados,K), Km1 is K+1,
					inicialDe(A,I), finalesDe(A,Finales), between(1,Km1,N), member(F,Finales),
					caminoDeLongitud(A,N,_,P,I,F).
reconoce(A,P) :- var(P), hayCicloPalabra(A), inicialDe(A,I), finalesDe(A,Finales),
					desde(1,N), member(F,Finales),
					caminoDeLongitud(A,N,_,P,I,F).
% Debemos separar este predicado en 3 reglas. Si la palabra viene instanciada, el camino que buscamos
% tiene longitud N+1 con N la longitud de la palabra. Si la palabra no viene instanciada, el
% predicado debe generar todas las palabras. Como en el caso de 'esCaminoReversible', debemos
% distinguir si la cantidad de palabras es finita o no. Esto es equivalente a determinar si el
% automata tiene ciclos o no. Más específicamente, si tiene ciclos que puedan ser alcanzados por
% una palabra (el ejemplo 11 es un automata con un ciclo pero con una sola palabra).

% Auxiliar: determina si el automata tiene un ciclo alcanzable por una palabra.
% hayCicloPalabra(+Automata)
hayCicloPalabra(A) :- estados(A,Estados), length(Estados,CantEstados), CEMasUno is CantEstados+1,
				finalesDe(A,Finales),
				between(2,CEMasUno,N), member(S1,Estados), caminoDeLongitud(A,N,_,_,S1,S1),
				between(2,CEMasUno,M), member(F,Finales), caminoDeLongitud(A,M,_,_,S1,F), !.
% Similar a 'esCiclo', con la condición adicional, de que debe existir un camino entre algún estado
% del ciclo (si existe para uno, existe para todos) y algún estado final. Como asumimos que el
% automata es válido, no es necesario chequear también que exista un camino entre el estado inicial
% y algún estado del ciclo.

% 10) PalabraMásCorta(+Automata, ?Palabra) :- reconoce(A,P) ^ noHayPalabraMasCorta(A,long(P))
palabraMasCorta(A,P) :-
	estados(A,Estados), length(Estados,K), inicialDe(A,I), finalesDe(A,Fs),
	between(1,K,N),	member(F,Fs),									% for N { for F {
	caminoDeLongitud(A,N,_,P,I,F), noHayPalabraMasCorta(A,N).
% Si bien el pseudocódigo utiliza el predicado 'reconoce', no podemos usarlo en la implementación.
% 'palabraMasCorta' debe devolver una cantidad finita de palabras y, si el automata tiene ciclos,
% 'reconoce' generaría todas las palabras posibles, que luego se determinaría que no son las más
% cortas⁴. En lugar de eso, se generan las palabras de longitud a los sumo, la cantidad de estados
% (si existe una palabra más larga, contiene un ciclo y, por lo tanto existe otra más corta,
% entonces la primerea no era la más corta).

%4: ?- ejemplo(4,A), reconoce(A,Palabra), length(Palabra,N), M is N+1, noHayPalabraMasCorta(A,M).
	% Palabra = [a], [b],
	% ...
	% Después de generar las únicas dos palabras más cortas, genera todas las demás pero no
	% muestra ninguna. Nota: Al predicado noHayPalabraMasCorta se le pasa la longitud del camino
	% correspondiente (que es uno más que la longitud de la palabra).

% Auxiliar: determina si es cierto que no existe una palabra cuyo camino tenga longitud menor a N
% noHayPalabraMasCorta(+Automata,+N).
noHayPalabraMasCorta(A,N) :- inicialDe(A,I), finalesDe(A,Fs), not((		% ∄ camino tq
	Nm1 is N-1, between(1,Nm1,M), member(F,Fs),							% for M { for F {
	caminoDeLongitud(A,M,_,_,I,F) )).

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
	ejemploMalo(7, M7), esDeterministico(M7), ejemplo(11, B1), not(esDeterministico(B1)).

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
	ejemploMalo(7, M7), estados(M7,[s1,s2,s3]), ejemplo(11, B1), estados(B1,[s1,s2,s3,s4]).

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
	ejemploMalo(7, M7), esCamino(M7,s1,s3,[s1,s2,s3]),
	ejemplo(11, B1), esCamino(B1,s1,s2,[s1,s2]), esCamino(B1,s3,s3,[s3,s4,s3]).

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
	ejemplo(10, A), not(alcanzable(A,s1)), alcanzable(A,s2), alcanzable(A,s3), alcanzable(A,s4),
		alcanzable(A,s5), alcanzable(A,s6), alcanzable(A,s7), alcanzable(A,s8), alcanzable(A,s9),
		alcanzable(A,s10), alcanzable(A,s11), alcanzable(A,s12), alcanzable(A,s13),
		alcanzable(A,s14), alcanzable(A,s15),
	ejemploMalo(1, M1), alcanzable(M1,s1), alcanzable(M1,s2), alcanzable(M1,s3),
	ejemploMalo(2, M2), alcanzable(M2,s1), not(alcanzable(M2,s2)),
	ejemploMalo(3, M3), not(alcanzable(M3,s1)), not(alcanzable(M3,s2)), alcanzable(M3,s3),
	ejemploMalo(4, M4), not(alcanzable(M4,s1)), not(alcanzable(M4,s2)), alcanzable(M4,s3),
	ejemploMalo(5, M5), not(alcanzable(M5,s1)), alcanzable(M5,s2), alcanzable(M5,s3),
	ejemploMalo(6, M6), not(alcanzable(M6,s1)), alcanzable(M6,s2), alcanzable(M6,s3),
	ejemploMalo(7, M7), not(alcanzable(M7,s1)), alcanzable(M7,s2), alcanzable(M7,s3),
	ejemplo(11, B1), not(alcanzable(B1,s1)), alcanzable(B1,s2), alcanzable(B1,s3), alcanzable(B1,s4).

% Test valido
test(21) :- forall(between(1,11,N), (ejemplo(N, A),automataValido(A))), 
			forall(between(1,7,N), (ejemploMalo(N, A),not(automataValido(A)))).

% Test ciclo
test(22) :- ejemplo(1, A1), not(hayCiclo(A1)), ejemplo(2, A2), hayCiclo(A2),
			ejemplo(3, A3), not(hayCiclo(A3)), ejemplo(4, A4), hayCiclo(A4),
			ejemplo(5, A5), hayCiclo(A5), ejemplo(6, A6), hayCiclo(A6),
			ejemplo(7, A7), hayCiclo(A7), ejemplo(8, A8), hayCiclo(A8),
			ejemplo(9, A9), hayCiclo(A9), ejemplo(10, A), not(hayCiclo(A)),
			ejemplo(11, B1), hayCiclo(B1).

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
		reconoce(A,[p,a,r,a,d,i,g,m,a,s]),
	ejemplo(11, B1), reconoce(B1,[a]), not(reconoce(B1,[_,_])).

% Test palabra mas corta
test(24) :- ejemplo(1, A1), palabraMasCorta(A1, [a]), ejemplo(2, A2), palabraMasCorta(A2, []),
	ejemplo(3, A3), palabraMasCorta(A3, []),
	ejemplo(4, A4), palabraMasCorta(A4, [a]), palabraMasCorta(A4, [b]),
	ejemplo(5, A5), palabraMasCorta(A5, [b]), palabraMasCorta(A5, [c]),
	ejemplo(6, A6), palabraMasCorta(A6, [b,a]), ejemplo(7, A7), palabraMasCorta(A7, [a,b]),
	ejemplo(8, A8), palabraMasCorta(A8, [a,a,b,f]), palabraMasCorta(A8, [a,b,b,f]),
	ejemplo(9, A9), palabraMasCorta(A9, []), ejemplo(10, A), palabraMasCorta(A, [p,r,o,l,o,g]),
	ejemplo(11, B1), palabraMasCorta(B1, [a]).

tests :- forall(between(1, 24, N), test(N)).

% Tests Generadores
% En estos tests no queremos que nos devuelva true, sino que queremos ver qué se genera.

% Test estados
testEstados(E1q2,E2q1,E3q1,E4q3,E5q3,E6q3,E7q3,E8q5,E9q2,Eq15,
													F1q3,F2q2,F3q3,F4q3,F5q3,F6q3,F7q3,B1q4) :-
	ejemplo(1, A1), estados(A1,E1q2), ejemplo(2, A2), estados(A2,E2q1),
	ejemplo(3, A3), estados(A3,E3q1), ejemplo(4, A4), estados(A4,E4q3),
	ejemplo(5, A5), estados(A5,E5q3), ejemplo(6, A6), estados(A6,E6q3),
	ejemplo(7, A7), estados(A7,E7q3), ejemplo(8, A8), estados(A8,E8q5),
	ejemplo(9, A9), estados(A9,E9q2), ejemplo(10, A), estados(A,Eq15),
	ejemploMalo(1, M1), estados(M1,F1q3), ejemploMalo(2, M2), estados(M2,F2q2),
	ejemploMalo(3, M3), estados(M3,F3q3), ejemploMalo(4, M4), estados(M4,F4q3),
	ejemploMalo(5, M5), estados(M5,F5q3), ejemploMalo(6, M6), estados(M6,F6q3),
	ejemploMalo(7, M7), estados(M7,F7q3), ejemplo(11, B1), estados(B1,B1q4).
	% Debería devolver:
	% Eiqṇ = [s1,...,sṇ], Fiqṇ = [s1,...,sṇ], Biqṇ = [s1,...,sṇ]

% Test caminos
testCaminos(I1s1,F1s2,I2s1,F2s1,I3s1,F3s1,I4s1,F4s3,I5s1,F5s3,I6s1,F6s2,
										I7s3,F7s2,I8s1,F8s5,I9s2,F9s1,I0s1,I0s10,B1s1,B1s3) :-
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
	ejemplo(10, A), esCamino(A,I0s1,I0s10,[s1,s2,s3,s4,s5,s6,s7,s8,s9,s10]),
	ejemplo(11, B1), esCamino(B1,B1s1,B1s3,[s1,s3,s4,s3,s4,s3,s4,s3]).
	% Debería devolver:
	% Iisṇ = sṇ, Fisṇ = sṇ, Bisṇ = sṇ

% Test camino de longitud (?Ejemplo(N°), -Camino, +MaxLongitud)
testCaminoDeLongitud(A, Camino, MaxLongitud) :-
	between(1,10,A), ejemplo(A,M), between(2,MaxLongitud,N),
	caminoDeLongitud(M,N,Camino,_,_,_).
	% Debería generar todos los caminos de longitud menor o igual a MaxLongitud (ignoramos los de
	% longitud 1 que son triviales).
	% Si no se instancia el número de autómata, se ejecuta para los 10.

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
	% 11:	[a]

%Test palabra mas corta (-Palabra, ?Ejemplo(N°))
testPalabraMasCorta(Palabra, A) :-
	between(1,11,A), ejemplo(A,M), palabraMasCorta(M,Palabra).
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
	% 11:	[a]

%% TODO: Estaría bueno hacer un generador de autómatas...
%generadorAutomatas(a(1,[1],[])).
%generadorAutomatas(a(1,Fs,[(p,e,q)|Ts])) :- generadorAutomata(1,Fs,Ts), ... .

% Apéndice: esCaminoReversible
% Para hacer que el predicado esCamino sea reversible hay que sacarle el '!', así podrá generar
% más de un camino. Además, es necesario que pueda generarlos todos y no colgarse en un ciclo. La
% forma más fácil de hacer eso (lo sabemos porque intentamos otras más complejas) es establecer una
% longitud y generar todos los caminos de dicha longitud. Luego incrementar la longitud y volver a
% iterar.
% esCaminoReversible(+Automata, ?EstadoInicial, ?EstadoFinal, -Camino)
esCaminoReversible(A, I, F, C) :- not(hayCiclo(A)),
					estados(A,Estados), length(Estados,K), Km1 is K+1, between(1,Km1,N),
					caminoDeLongitud(A,N,C,_,I,F).
esCaminoReversible(A, I, F, C) :- hayCiclo(A), nonvar(I), var(F), hayCicloDesde(A,I),
					desde(1,N), caminoDeLongitud(A,N,C,_,I,F).
esCaminoReversible(A, I, F, C) :- hayCiclo(A), nonvar(I), var(F), not(hayCicloDesde(A,I)),
					estados(A,Estados), length(Estados,K), Km1 is K+1, between(1,Km1,N),
					caminoDeLongitud(A,N,C,_,I,F).
esCaminoReversible(A, I, F, C) :- hayCiclo(A), var(I), nonvar(F), hayCicloHasta(A,I),
					desde(1,N), caminoDeLongitud(A,N,C,_,I,F).
esCaminoReversible(A, I, F, C) :- hayCiclo(A), var(I), nonvar(F), not(hayCicloHasta(A,I)),
					estados(A,Estados), length(Estados,K), Km1 is K+1, between(1,Km1,N),
					caminoDeLongitud(A,N,C,_,I,F).
esCaminoReversible(A, I, F, C) :- hayCiclo(A), nonvar(I), nonvar(F), hayCicloEntre(A,I,F),
					desde(1,N), caminoDeLongitud(A,N,C,_,I,F).
esCaminoReversible(A, I, F, C) :- hayCiclo(A), nonvar(I), nonvar(F), not(hayCicloEntre(A,I,F)),
					estados(A,Estados), length(Estados,K), Km1 is K+1, between(1,Km1,N),
					caminoDeLongitud(A,N,C,_,I,F).
esCaminoReversible(A, I, F, C) :- hayCiclo(A), var(I), var(F),
					desde(1,N), caminoDeLongitud(A,N,C,_,I,F).
% Debemos separar este predicado en 2 partes. Si el automata no tiene ciclos, la cantidad de caminos
% es siempre finita y la longitud máxima de un camino es la cantidad de estados más 1. Si el automata
% tiene ciclos, la cantidad de caminos es infinita y no hay longitud máxima (dado cualquier camino
% que contenga un ciclo, puedo generar uno más grande agregando otro recorrido al ciclo). Sin
% embargo, si los estados inicial y/o final están instanciados, puede que la cantidad de caminos que
% deba generar no sea infinita. Entonces también hay que separar los casos según las instanciaciones
% de los estados inicial y final. Para que la cantidad de caminos siga siendo infinita cuando sólo
% un estado está instanciado, debe haber un ciclo alcanzable desde o hasta dicho estado. Si no lo
% hay, la cantidad de caminos es finita.

% Auxiliarles: determinan si hay un ciclo alcanzable desde un estado, hasta un estado o entre un
% par de estados.
% hayCicloDesde(+Automata,+Inicial).
hayCicloDesde(A,I) :- estados(A,Estados), length(Estados,CantEstados), CEMasUno is CantEstados+1,
				between(2,CEMasUno,N), member(S1,Estados), caminoDeLongitud(A,N,_,_,S1,S1),
				between(2,CEMasUno,M), caminoDeLongitud(A,M,_,_,I,S1), !.
% hayCicloHasta(+Automata,+Final).
hayCicloHasta(A,F) :- estados(A,Estados), length(Estados,CantEstados), CEMasUno is CantEstados+1,
				between(2,CEMasUno,N), member(S1,Estados), caminoDeLongitud(A,N,_,_,S1,S1),
				between(2,CEMasUno,M), caminoDeLongitud(A,M,_,_,S1,F), !.
% hayCicloEntre(+Automata,+Inicial,+Final).
hayCicloEntre(A,I,F) :- estados(A,Estados), length(Estados,CantEstados), CEMasUno is CantEstados+1,
				between(2,CEMasUno,N), member(S1,Estados), caminoDeLongitud(A,N,_,_,S1,S1),
				between(2,CEMasUno,M), caminoDeLongitud(A,M,_,_,I,S1),
				between(2,CEMasUno,W), caminoDeLongitud(A,W,_,_,S1,F), !.

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

	% Nota: con el ejemplo 8 devuelve repetidos.

% Test camino reversible sin instanciar estados (-Camino,+Ejemplo(N°))
% Debería generar todos los caminos del automata.
testCaminoReversible2(Camino,A) :-
	ejemplo(A,M), esCaminoReversible(M,_,_,Camino).
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
