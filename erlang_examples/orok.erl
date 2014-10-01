-module(orok).
-compile(export_all).
-author(kapolnai@iit.bme.hu).
-vsn('$LastChangedDate: 2011-10-19 20:26:08 +0200 (Wed, 19 Oct 2011) $$').

% absz(Num) Num abszolutértéke.
absz(X) when X<0 -> -X;
%abs(X)          -> X.
absz(X) when is_number(X) -> X.

% kategoria(V) a V term egy lehetséges osztalyozása.
kategoria(V) ->
    case V of
        X when is_atom(X) ->
            atom;
        X when is_number(X), X < 0 ->
            negativ_szam;
        X when is_integer(X) ;
               is_float(X), abs(X-round(X)) < 0.0001 ->
            kerek_szam;
        X when is_list(X), length(X) > 5 ->
            hosszu_lista;
        {X,Y,Z} when X*X+Y*Y =:= Z*Z, is_integer(Z) ;
                     Z*Z+Y*Y =:= X*X, is_integer(X) ;
                     X*X+Z*Z =:= Y*Y, is_integer(Y) ->
            pitagoraszi_szamharmas;
        {Nev, []} when is_atom(Nev) ->
            talan_hallgato;
        {Nev, [{Tipus,_}|_]} when is_atom(Nev), is_atom(Tipus) ->
            talan_hallgato;
        [Ny1|_] when Ny1 =:= cekla ; Ny1 =:= prolog ; Ny1 =:= erlang ->
            talan_programozasi_nyelvek_listaja;
        {tort, Sz, N} when abs(Sz div N) >= 0 ->
            tort;
        _ -> egyeb
    end.

 

teszt() ->
    [{K,orok:kategoria(K)} || K <- [true, haho, -5, 5.000001, "kokusz",
                                    {3,5,4}, {'D.D.',[]}, {tort,1,a},
                                    {tort,1,2},[cekla,prolog,erlang]]
    ]
    .

