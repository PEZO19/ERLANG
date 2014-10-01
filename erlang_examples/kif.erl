-module(kif).
-compile(export_all).
-author('kapolnai@iit.bme.hu').
-vsn('$LastChangedDate: 2013-02-13 23:39:18 +0100 (Wed, 13 Feb 2013) $$').

%  @type muvelet() = '+' | '-' | '*' | '/'.
%  @type kif() = integer() | {kif(), muvelet(), kif()}.
%  @spec kifek([integer()]) -> [kif()].
% kifek(L) = az L számokból alapműveletekkel előálló
%            összes lehetséges kifejezések listája,
%            ahol a levelek in-order sorrendje az L-beli sorrend.
% megj: Erlangban explicit felsoroljuk, nincs automatikus visszalépés.
kifek([H]) ->
    [H];
kifek(L) ->
    [ {B, M, J}
      || {BalLista, JobbLista} <- kettevagasok(L),
         B <- kifek(BalLista),
         J <- kifek(JobbLista),
         M <- ['+', '-', '*', '/']
    ].

% kettevagasok(L) = az összes olyan nemüres lista-párok,
%                   melyek összefűzve az L listát adják.
kettevagasok(L) ->
    [ {BalLista, JobbLista}
      || I <- lists:seq(1, length(L) - 1),
         {BalLista, JobbLista} <- [lists:split(I, L)]
    ].

% ertek(K) = a K kifejezés számértéke.
% megj: Erlangban explicit el kell végezni a kiértékelést.
ertek({BalFa, Muvelet, JobbFa}) ->
    erlang:Muvelet(ertek(BalFa), ertek(JobbFa));
ertek(I) ->
    I.
% megj: a klózok sorrendje itt számít

% permutaciok(L) = az L lista elemeinek minden permutációja.
permutaciok([]) ->
    [[]];
permutaciok(L) ->
    [[H|T] || H <- L, T <- permutaciok(L -- [H])].

% megoldasok() = azok kifejezések listája, melyek megoldják a feladatot.
megoldasok() -> megoldasok([1,3,4,6], 24).

megoldasok(Szamok, Eredmeny) ->
    [Kif || L <- permutaciok(Szamok),
            Kif <- kifek(L),
            (catch ertek(Kif)) == Eredmeny].
% megj: catch: kivétel mellőzése 0-val osztásnál


% ----------------------- BEMELEGÍTÉS ------------------------------


% @type fa() = 1 | {fa(), '+', fa()}.
% fak(N) = az összes N levelű fa listája.
fak(1) ->
    [1];
fak(N) ->
    [ {BalFa, '+', JobbFa}
      || I <- lists:seq(1, N - 1),
         BalFa <- fak(I),
         JobbFa <- fak(N - I)
    ].

pelda(1) ->
    [X || X <- [1,2,3]];
pelda(2) ->
    [X || X <- [1,2,3], X*X > 5];
pelda(3) ->
    lists:seq(1,3);
pelda(4) ->
    [{X,Y} || X <- [1,2,3,4], Y <- lists:seq(1,X)];
pelda(5) ->
    fak(4);
pelda(6) ->
    length(fak(4));
pelda(7) ->
    kifek([1,3,4]);
pelda(8) ->
    ertek({{1, '-', {3, '*', 4} }, '+', 6});
pelda(9) ->
    permutaciok([1,3,4]);
pelda(10) ->
    L = [-1,-2,-3,-4],
    [{Elso,Masodik} || I <- [1,2,3], {Elso,Masodik} <- [lists:split(I, L)]].

