-module(khf).
%-compile(export_all).
-export([elofordul1/2,
         elofordul1b/2,
         elofordul2/2,
         elofordul3/2,
         elofordul4/2,
         filter/2,
         kiadott/1,
         kiadott_v2/1,
         megfelelt/2,
         safe_kiadott/1,
         safe_teljesitmeny/2,
         teszt/0]).
-author(kapolnai@iit.bme.hu).
-vsn('$LastChangedDate: 2011-10-21 01:08:35 +0200 (Fri, 21 Oct 2011) $$').

%% @spec kiadott_kishazik(Ny::atom()) -> Db::integer().
%% Az Ny nyelven Db darab kisházit adtak ki.
kiadott(cekla)  -> 1;
kiadott(prolog) -> 3;
kiadott(erlang) -> 3.

%% @spec safe_kiadott(Ny::atom()) -> {ok, Db::integer()} | error.
%% Az Ny nyelven Db darab kisházit adtak ki.
safe_kiadott(cekla)  -> {ok, 1};
safe_kiadott(prolog) -> {ok, 3};
safe_kiadott(erlang) -> {ok, 3};
safe_kiadott(_Ny)    -> error.

% felhasználása pl. teljesítés %-ban:
%% @spec safe_teljesites(Nyelv::atom(), Beadott_db::integer()) ->
%%     {ok, Teljesitmeny::float()} | error.
safe_teljesitmeny(Nyelv, Beadott_db) ->
    case safe_kiadott(Nyelv) of
        {ok, Kiadott_db} -> {ok, Beadott_db / Kiadott_db};
        error            -> error
    end.
    
% kiadott/1 case-zel:
kiadott_v2(Ny)  ->
    case Ny of
        cekla  -> 1;
        prolog -> 3;
        erlang -> 3
    end.

%% @spec elofordul1(E::term(), L::[term()]) -> N::integer().
%% E elem az L listában N-szer fordul elő.
elofordul1(_, [])              -> 0;
elofordul1(Elem, [Elem|Farok]) -> 1 + elofordul1(Elem, Farok);
elofordul1(Elem, [_Fej|Farok]) -> elofordul1(Elem, Farok).

elofordul1b(_, []) ->
    0;
elofordul1b(Elem, [Fej|Farok]) ->
    case Fej of
        Elem -> 1;
        _    -> 0
    end
	+ elofordul1b(Elem, Farok).

%% @spec filter(P::fun(term()->bool()), L::[term()]) -> F::[term()]
%% Az F lista az L lista azon E elemeinek listája, melyekre P(E) teljesül.
filter(_, []) ->
    [];
filter(P, [Fej|Farok]) ->
    case P(Fej) of
        true  -> [Fej|filter(P,Farok)];
        false -> filter(P,Farok)
    end.

elofordul2(Elem, L) ->
    length(filter(fun(X) -> X=:=Elem end, L)).

elofordul3(Elem, L) ->
    length([X || X <- L, X=:=Elem]).

elofordul4(_, []) ->
    0;
elofordul4(Elem, [Fej|Farok]) ->
    if 
        Fej =:= Elem -> 1;
        true         -> 0
    end
        + elofordul4(Elem, Farok).


%% @type hallgato() = {nev(), [ {kovetelmenytipus(), munka()} ] }.
%% @type nev() = atom().
%% @type kovetelmenytipus() = atom().
%% @type munka() = [atom()] | integer() | ... .
%% @spec megfelelt(K::kovetelmenytipus(), H::hallgato()) -> true | false.
%% true, ha H hallgató megfelelt a K követelménynek.
megfelelt(khf, {_Nev, [{khf, L}|_]}) ->
    C = elofordul1(cekla, L),
    P = elofordul1(prolog, L),
    E = elofordul1(erlang, L),
    (P >= 1) and (E >= 1) and (C + P + E >= 3);
%megfelelt(zh, {Nev, [{zh, Pont}|_]}) ->
%    Pont > ...;
megfelelt(K, {Nev, [_|F]}) ->
    megfelelt(K, {Nev, F});
megfelelt(_, {_, []}) ->
    false.

teszt() ->
    Hallgato1 = {'Diak Detti',
                  [{khf, [cekla,prolog,erlang,prolog]},
                   {nzh, 59}]},
    Hallgato2 = {'Lusta Ludvig', []},
    lists:map(fun(H={Nev,_}) -> {Nev, megfelelt(khf, H)} end,
	      [Hallgato1, Hallgato2]).