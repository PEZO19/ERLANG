-module(kiv).
-compile(export_all).
-author('kapolnai@iit.bme.hu, hanak@iit.bme.hu, genExc is inspired by "J.Armstrong: Programming Erlang. The Pragmatic Bookshelf, 2007."').
-vsn('$LastChangedDate: 2011-10-16 18:12:55 +0200 (Sun, 16 Oct 2011) $$').

%% @spec safe_apply(Fun::fun(Arg) -> Val, Arg) -> {ok, Val} | error.
%% Ha Fun(Arg) hibát jelez, 'error', különben {ok, Fun(Arg)} becsomagolva.
%% A legsúlyosabb, 'exit' típusú hibát nem kapja el.
safe_apply(Fun, Arg) ->
    try Fun(Arg) of
        V -> {ok,V}
    catch
        throw:_Why -> error;
        error:_Why -> error % például error:function_clause
    end.


genExc(A,1) -> A;
genExc(A,2) -> throw(A);
genExc(A,3) -> exit(A);
genExc(A,4) -> erlang:error(A).

tryGenExc(X,I) ->
    try genExc(X,I) of
        Val -> {I, 'Lefutott', Val}
    catch
        throw:X -> {I, 'Kivetelt dobott', X};
        exit:X  -> {I, 'Befejezodott', X};
        error:X -> {I, 'Sulyos hibat jelzett', X}
    end.
%[catch dpr:genExc(X,I) || {X,I} <- [{’No’,1},{’Th’,2},{’Ex’,3},{’Er’,4}]].
