-module(sendmory).
-compile([export_all,debug_info]).
-author('patai@iit.bme.hu, hanak@inf.bme.hu, kapolnai@iit.bme.hu').
-vsn('$LastChangedDate: 2012-10-29 21:26:40 +0100 (Mon, 29 Oct 2012) $$').

%      S E N D
%    + M O R E
%  = M O N E Y

% @type d() = 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9.
% @type octet() = {d(),d(),d(),d(),d(),d(),d(),d()}.

% @spec mynum(Ns::[d()]) -> N::integer().
% Az Ns számjegylista decimális számként N.
mynum([], Sz) -> Sz;
mynum([X|Xs], Sz) -> mynum(Xs, Sz*10 + X).

% @spec num(Ns::[d()]) -> N::integer().
% Az Ns számjegylista decimális számként N.
num(Ns)->
    lists:foldl(fun(X,E) -> E*10+X end, 0, Ns).

% @spec check_sum(octet()) -> bool().
% A jelölt teljesíti-e az összeadási feltételt.
check_sum({S,E,N,D,M,O,R,Y}) ->
    Send = num([S,E,N,D]),
    More = num([M,O,R,E]),
    Money = num([M,O,N,E,Y]),
    Send+More =:= Money.
    %% (1000*S + 100*E + 10*N + D) + (1000*M + 100*O + 10*R + E) =:=
    %%	(10000*M + 1000*O + 100*N + 10*E + Y).

% @spec all_different(Xs::[any()]) -> B::bool()
% B igaz, ha az L lista minden eleme különbözik.
all_different(L) -> length(L) =:= length(lists:usort(L)).

% @spec smm0() -> [octet()].
% Minden ellenőrzés a generálás után történik.
% 10 elem minden 8-adosztályú ismétléses variációját generálja (10^8 jelölt).
% Esélytelenül lassú.
smm0() ->
    Ds = lists:seq(0, 9),
    [{S,E,N,D,M,O,R,Y} ||
        S <- Ds,
        E <- Ds,
        N <- Ds,
        D <- Ds,
        M <- Ds,
        O <- Ds,
        R <- Ds,
        Y <- Ds,
        statistics_count(),
        all_different([S,E,N,D,M,O,R,Y]),
        S > 0, M > 0,
        check_sum({S,E,N,D,M,O,R,Y})].


% @spec smm0e() -> [octet()] when length([octet()]) =< 1.
% Minden ellenőrzés a generálás után történik,
% de csak a legelső megoldást adja vissza.
% Tehát nem egzakt megoldást ad, hanem heurisztikus!
% Esélytelenül lassú, de a demo kedvéért csalunk: megmondjuk, hogy az S-et 9-től kezdje...
smm0e() ->
    try
        Ds = lists:seq(0, 9),
        [{S,E,N,D,M,O,R,Y} ||
            S <- lists:reverse(Ds),  % itt csalunk, különben örökké tart 
            E <- Ds,
            N <- Ds,
            D <- Ds,
            M <- Ds,
            O <- Ds,
            R <- Ds,
            Y <- Ds,
            all_different([S,E,N,D,M,O,R,Y]),
            S > 0, M > 0,
            check_sum({S,E,N,D,M,O,R,Y}),
            throw({S,E,N,D,M,O,R,Y})]
    catch
        throw:Solution -> [Solution]
    end.


% @spec smm1() -> [octet()].
% Ellenőrzések generálás közben is.
smm1() ->
    Ds = lists:seq(0, 9),
    [{S,E,N,D,M,O,R,Y} ||
        S <- Ds,
        E <- Ds, E =/= S,
        N <- Ds, not lists:member(N, [S,E]),
        D <- Ds, not lists:member(D, [S,E,N]),
        M <- Ds, not lists:member(M, [S,E,N,D]),
        O <- Ds, not lists:member(O, [S,E,N,D,M]),
        R <- Ds, not lists:member(R, [S,E,N,D,M,O]),
        Y <- Ds, not lists:member(Y, [S,E,N,D,M,O,R]),
        statistics_count(),
        S > 0, M > 0,
        check_sum({S,E,N,D,M,O,R,Y})].

% @spec smm2() -> [octet()].
% Minden ellenőrzés a generálás után történik,
% de csak 10!/2! jelöltet generál 10^8 helyett (8-adosztályú ismétlés nélküli variációk).
smm2() ->
    Ds = lists:seq(0, 9),
    [{S,E,N,D,M,O,R,Y} ||
        S <- Ds -- [],
        E <- Ds -- [S],
        N <- Ds -- [S,E],
        D <- Ds -- [S,E,N],
        M <- Ds -- [S,E,N,D],
        O <- Ds -- [S,E,N,D,M],
        R <- Ds -- [S,E,N,D,M,O],
        Y <- Ds -- [S,E,N,D,M,O,R],
        statistics_count(),
        S > 0, M > 0,
        check_sum({S,E,N,D,M,O,R,Y})].

% @spec perms() -> [octet()].
% Számjegyek ismétlés nélküli 8-adosztályú variációi (10!/2! = 1814400).
perms8() ->
    Ds = lists:seq(0,9),
    [{S,E,N,D,M,O,R,Y} ||
        S <- Ds -- [],
        E <- Ds -- [S],
        N <- Ds -- [S,E],
        D <- Ds -- [S,E,N],
        M <- Ds -- [S,E,N,D],
        O <- Ds -- [S,E,N,D,M],
        R <- Ds -- [S,E,N,D,M,O],
        Y <- Ds -- [S,E,N,D,M,O,R]
    ].

% @spec smm3() -> [octet()].
% Ellenőrzés a generálás után történik, de ismétlés nélkül generál.
% Memóriaigényes! Megfigyelhető Linuxban:
% top `ps aux | grep beam.smp | grep -v grep | awk '{print "-p "  $2}'`
smm3() ->
    [Solution ||
        {S,_E,_N,_D,M,_O,_R,_Y} = Solution <- perms8(),
        statistics_count(),
        S > 0, M > 0,
        check_sum(Solution)].


% @spec smm4() -> [octet()].
% További ellenőrzések generálás közben.
smm4() ->
    Ds = lists:seq(0,9),
    [{S,E,N,D,M,O,R,Y} ||
        S <- Ds -- [0],              % 0 kizárva
        E <- Ds -- [S],
        N <- Ds -- [S,E],
        D <- Ds -- [S,E,N],
        M <- Ds -- [0,S,E,N,D],      % 0 kizárva
        O <- Ds -- [S,E,N,D,M],
        R <- Ds -- [S,E,N,D,M,O],
        Y <- Ds -- [S,E,N,D,M,O,R],
        statistics_count(),
        check_sum({S,E,N,D,M,O,R,Y})].


% @spec smm5() -> [octet()].
% Hátulról építi a számokat, folyamatosan ellenőrzi a részösszegeket.
smm5() ->
    Ds = lists:seq(0, 9),
    [{S,E,N,D,M,O,R,Y} ||
        %%      S E N D
        %%    + M O R E
        %%  = M O N E Y
        D <- Ds -- [],
        E <- Ds -- [D],
        Y <- Ds -- [D,E],
        (D+E) rem 10 =:= Y,
        N <- Ds -- [D,E,Y],
        R <- Ds -- [D,E,Y,N],
        (num([N,D])+num([R,E])) rem 100 =:= num([E,Y]),
        O <- Ds -- [D,E,Y,N,R],
        (num([E,N,D])+num([O,R,E])) rem 1000 =:= num([N,E,Y]),
        S <- Ds -- [D,E,Y,N,R,O,0],
        M <- Ds -- [D,E,Y,N,R,O,S,0],
        statistics_count(),
%        S > 0, M > 0,
        check_sum({S,E,N,D,M,O,R,Y})].


% @spec smm6() -> [octet()].
% Hátulról építi a számokat, folyamatosan ellenőrzi a részösszegeket.
% Továbbiakban használt feltípus:
% @type partial_solution() = {[d()], [d()], [d()]}.
smm6() ->
    smm6({[],[],[]}, 5, lists:seq(0,9)).

% @spec check_equals(partial_solution()) -> bool().
% Ellenőrzi, hogy a részmegoldásban helyes-e a megegyező számjegyek pozíciója.
% A többi számjegynek eltérőnek kell lennie.
check_equals(PartialSolution) ->
    %%      S E N D   
    %%    + M O R E   
    %%  = M O N E Y   
    case PartialSolution of
        {[D], [E], [Y]}                         -> all_different([D,E,Y]);
        {[N,D], [R,E], [E,Y]}                   -> all_different([N,D,R,E,Y]);
        {[E,N,D], [O,R,E], [N,E,Y]}             -> all_different([O,N,D,R,E,Y]);
        {[S,E,N,D], [M,O,R,E], [O,N,E,Y]}       -> all_different([S,M,O,N,D,R,E,Y]);
        {[0,S,E,N,D], [0,M,O,R,E], [M,O,N,E,Y]} -> all_different([S,M,O,N,D,R,E,Y])
                                                    andalso all_different([0,S,M]);
        _ -> false
    end.

% @spec check_sum(partial_solution()) -> bool().
% Ellenőrzi, hogy aritmetikai szempontból helyes-e a részmegoldás.
% Az átvitellel (carry) nem foglalkozik, mert mindkettő helyes:
% {[1,2],[3,4],[4,6]}, és {[9],[2],[1]}, mert építhető belőlük teljes megoldás.
check_partialsum({Send, More, Money}) ->
    S = num(Send), M = num(More), My = num(Money),
    (S+M) rem round(math:pow(10,length(Send))) =:= My.

% @spec smm6(PS::partial_solution(),
%            Num::integer(), Domain::[d()]) -> [octet()].
% Felsorolja az összes megoldást, mely a PS részmegoldásból építhető,
% mérete (Send hossza) legfeljebb Num, számjegyek tartománya Domain.
smm6({Send,_,_} = PS, Num, _Domain) when length(Send) =:= Num ->
    {[0,S,E,N,D], [0,M,O,R,E], [M,O,N,E,Y]} = PS,
    [{S,E,N,D,M,O,R,Y}];
smm6({Send,More,Money}, Num, Domain) ->
    [Solution ||
        Dsend <- Domain,
        Dmore <- Domain,
        %% ez is javítana:
        %% Dmoney <- [ begin Carry = if Send =:= [] -> 0 ;
        %%                              true -> (hd(Send) + hd(More)) div 10
        %%                           end,
        %%                   (Dsend + Dmore + Carry) rem 10
        %%             end ],
        Dmoney <- Domain,
        PartialSolution <- [ {[Dsend|Send], [Dmore|More], [Dmoney|Money]} ],
        check_equals(PartialSolution),
        if length([Dsend|Send]) =:= 4 -> statistics_count();
           true -> true
        end,
        check_partialsum(PartialSolution),
        Solution <- smm6(PartialSolution, Num, Domain)
    ].


% @spec smm7() -> [octet()].
% Hátulról építi a számokat, folyamatosan ellenőrzi a részösszegeket.
smm7() ->
    [{S,E,N,D,M,O,R,Y} ||
        {[0,S,E,N,D], [0,M,O,R,E], [M,O,N,E,Y]} <- smm7(5, lists:seq(0,9))].


% @spec smm7(Num::integer(), Domain::[d()]) -> PS::partial_solution().
% Visszaadja Num méretű (Send hossza) részmegoldások listáját,
% Domain a számjegyek készlete.
smm7(0, _)      ->
    [{[],[],[]}];
smm7(N, Domain) ->
    [ PartialSolution ||
        {Send,More,Money} <- smm7(N-1, Domain),
        Dsend <- Domain,
        Dmore <- Domain,
        Dmoney <- Domain,
        begin PartialSolution = {[Dsend|Send], [Dmore|More], [Dmoney|Money]}, true end,
        check_equals(PartialSolution),
        if length([Dsend|Send]) =:= 4 -> statistics_count();
           true -> true
        end,
        check_partialsum(PartialSolution)
    ].


% exercise: generalise the task to specifications given in strings:
%
% smm_gen("send","more","money")  ==>
% [{9567,1085,10652}]%
% smm_gen("four","five","nine")  ==>
% [{2970,2381,5351},{2970,2481,5451},...,{1970,1568,3538}]


% @type selector() -> integer().
% @spec stopper(selector()) -> ().
% Run the selected smm function and measure its run-time.
stopper(V) ->
    garbage_collect(),    % prevent garbage collection during measurement,
    timer:sleep(500),     %   and wait for it a bit
    put(counter, 0),
    _T = statistics(runtime),
    [{S,E,N,D,M,O,R,Y}|_] =
        case V of
            0 ->
                smm0();
            e0 ->
                smm0e();
            1 ->
                smm1();
            2 ->
                smm2();
            3 ->
                smm3();
            4 ->
                smm4();
            5 ->
                smm5();
            6 ->
                smm6();
            7 ->
                smm7();
            99 ->
                smm99:smm()
        end,
    {_,T} = statistics(runtime),
    io:format("~-2w: SEND+MORE=MONEY: ~w~w~w~w+~w~w~w~w=~w~w~w~w~w~8wms~10w candidates~n",
	      [V,S,E,N,D,M,O,R,E,M,O,N,E,Y,T,get(counter)]).

statistics_count() ->
    put(counter, get(counter)+1),
    true.

teljes_test() -> [sendmory:stopper(I) || I <- [0, 1,2,3,4,5,6,7,99]].

test() -> [sendmory:stopper(I) || I <- [1,2,3,4,5,6,99]].

%% 1> sendmory:teljes_test().
%% 0 : SEND+MORE=MONEY: 9567+1085=10652   97270ms 100000000 candidates
%% 1 : SEND+MORE=MONEY: 9567+1085=10652    1830ms   1814400 candidates
%% 2 : SEND+MORE=MONEY: 9567+1085=10652    1560ms   1814400 candidates
%% 3 : SEND+MORE=MONEY: 9567+1085=10652    3180ms   1814400 candidates
%% 4 : SEND+MORE=MONEY: 9567+1085=10652    1450ms   1451520 candidates
%% 5 : SEND+MORE=MONEY: 9567+1085=10652      10ms      1536 candidates
%% 6 : SEND+MORE=MONEY: 9567+1085=10652     120ms      2196 candidates
%% 7 : SEND+MORE=MONEY: 9567+1085=10652     110ms      2196 candidates
%% 99: SEND+MORE=MONEY: 9567+1085=10652      10ms        21 candidates
