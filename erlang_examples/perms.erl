-module(perms).
-export([perms/1]).
%-compile(export_all).
-author(hanak@inf.bme.hu).
-vsn('2011-09-07').

% @spec perms(Xs::[term()]) -> Xss::[[term()]].
% Xss az Xs lista minden permutációjának listája.
perms([]) -> [[]];
perms(L)  -> [[H|T] || H <- L, T <- perms(L--[H])].
