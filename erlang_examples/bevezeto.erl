-module(bevezeto).
-export([fac/1, sum/1, append/2, revapp/2]).
%-compile(export_all).
-author('kapolnai@iit.bme.hu').
-vsn('$LastChangedDate: 2011-10-16 18:12:55 +0200 (Sun, 16 Oct 2011) $$').

%% @spec fac(N::integer()) -> F::integer().
%% F = N! (F az N faktorialisa).
fac(0) -> 1;
fac(N) -> N * fac(N-1).

%% @spec sum(L::[number()]) -> S::number().
%% S az L lista elemeinek az osszege.
sum([]) -> 0;
sum(L)  -> H = hd(L), T = tl(L), H + sum(T).

%% @spec append(L1::[term()], L2::[term()]) -> L::[term()].
%% L az L1 elemeinek az L2 ele fuzesevel eloallo lista.
append([], L2) -> L2;
append(L1, L2) -> [hd(L1)|append(tl(L1), L2)].

%% @spec revapp(L1::[term()], L2::[term()]) -> L::[term()].
%% L az L1 forditottja elemeinek az L2 ele fuzesevel eloallo lista.
revapp([], L2) -> L2;
revapp(L1, L2) -> revapp(tl(L1), [hd(L1)|L2]).

