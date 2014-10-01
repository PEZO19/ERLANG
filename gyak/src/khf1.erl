-module(khf1).
%% -author(pezo1919@gmail.com).
%% -vsn('2014-09-27').
-export([cella/2]).
-export([board_to_smartboard/1]).
-export([smartthing_filter_by_col/2]).
-export([smartthing_filter_by_row/2]).
-export([smartthing_filter_by_cella/2]).
-export([smartthing_oszloprendez/2]).


-compile(export_all).



%% @type field() = integer().
%% @type board() = [[field()]].
%% @spec khf1:cella(S::board(), I::integer()) -> C::[field()].
%%   C egy olyan lista, amely az S Sudoku-mátrix I.
%%   cellájának elemeit oszlopfolytonosan tartalmazza.
cella(S,I)    ->
    L = length(S),
    Smartboard = board_to_smartboard(S),
    Smartboard_oszloprendezve = smartthing_oszloprendez(Smartboard,L),
    Smartcella = smartthing_filter_by_cella(Smartboard_oszloprendezve,I-1), % nekem a bal felso 0.cella, nekik 1.
    smartthing_to_thing(Smartcella).

%% A visszakapott Smartboard egy olyan lista, amely az S Sudoku-mátrix elemeit mellett,
%% az elemek X sor és Y oszlop szerinti elhelyezkedését és C cellájuk azonosítószámát is tartalmazzák ennesek
%% formájában.
%% Az ennesek: {{{X_coord, Y_coord}, Cella}, Ertek} alakúak.
board_to_smartboard(S) ->
    K = trunc(math:sqrt(length(S))),
    Lapos = lists:flatten(S),
    Smartboard =
        [
            {
                {
                    {(N-1) rem (K*K), trunc((N-1)/(K*K))},
                        melyik_smartcella(K, (N-1) rem (K*K), trunc((N-1)/(K*K)))
                    },
                lists:nth(N,Lapos)}
            ||  N  <-  lists:seq(1,length(Lapos))
        ],
    Smartboard.

%% Megadja, hogy a cella K méretétől függően melyik cellába tartozik az {X,Y} koordinátájú elem.
melyik_smartcella(K,X,Y) -> trunc(X / K) + trunc(Y / K) * K .

%% Megadja egy Smartboard oszlopát.
smartthing_filter_by_col(S, X1) ->
   [ {{{X2,Y},C},E}
       ||   {{{X2,Y},C},E}   <-  S,
            X1 =:= X2
   ].

%% Megadja egy Smartboard sorát.
smartthing_filter_by_row(S, Y1) ->
    [ {{{X,Y2},C},E}
        ||   {{{X,Y2},C},E}   <-  S,
             Y1 =:= Y2
    ].

% Megadja (szűr) egy SmartErteket tartalmazó lista adott cellához tartozó Smartelemeket.
smartthing_filter_by_cella(S, Cella)    ->  [ {{{X1,Y2},C},E3} || {{{X1,Y2},C},E3}<-S, C=:=Cella].

% SmartErtekeket alakít Ertek-ekké
smartthing_to_thing(S)      ->      [ E || {_,E} <- S].

% Smartértéket rendez oszlopok szerint növekvő sorrendbe.
smartthing_oszloprendez(S,L)    ->   lists:flatten(smartthing_oszloprendez(S,L,0)). % flatten! - ezt ki kéne venni

smartthing_oszloprendez(S,L,N) when  N<L  ->
    [smartthing_filter_by_col(S,N)|smartthing_oszloprendez(S,L,N+1)]; % TODO:flatten! - ezt kéne hozzá átalakítani,
    %% feleslegesen építünk több listát az 1 nagy külső listában.
smartthing_oszloprendez(_,_,_) -> [].











%% type coordinate = integer().
%% type coordinate_x = coordinate().
%% type coordinate_y = coordinate().
%% type smartfield() = {{coordinate_x(), coordinate_y()}, field()}.
%% type smartboard() = [[smartfield()]].
%%
%% spec khf1:board_to_smartboard(S::board()) -> SB::smartboard().







