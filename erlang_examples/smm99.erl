-module(smm99).
-compile([export_all,debug_info]).
-author('szeredi@cs.bme.hu').
-vsn('$LastChangedDate: 2012-10-29 21:26:40 +0100 (Mon, 29 Oct 2012) $$').
% -export([smm/1]).

% Make this function return false if you do not want a trace printed.
wants_trace() -> true.

% Usage: sendmory:stopper(99).

% The SEND+MORE=MONEY problem is decomposed into five decimal additions using
% carry over variables C1..C4

%		D + E +  0 = Y +10*C1
%		N + R + C1 = E +10*C2
%		E + O + C2 = N +10*C3
%		S + M + C3 = O +10*C4
%		0 + 0 + C4 = M +10* 0

% We use the lower case versions of the above variable names, as the atoms
% naming the constraint variables.

% vars_domains() = the list of variables paired with domains (pairs of
% lower and upper bounds).  The problem variables, denoted by atoms
% s,e,n,d,m,o,r,y are preceded by the auxiliary variables c1..c4 for the
% carry-over values and the constant variable named 0.
vars_domains() ->
    VarNames = [0,c1,c2,c3,c4,s,e,n,d,m,o,r,y],
    From     = [0, 0, 0, 0, 0,1,0,0,0,1,0,0,0],
    To       = [0, 1, 1, 1, 1,9,9,9,9,9,9,9,9],
    lists:zip(VarNames,lists:zip(From,To)).

problem_vars(St) ->
    lists:nthtail(5,St).
% split(5, [0,c1,c2,c3,c4,s,e,n,d,m,o,r,y]) =:= {[0,c1,c2,c3,c4],[s,e,n,d,m,o,r,y]}

% initial_state() = St iff St describes the variables of the SEND MORE
% MONEY problem.
initial_state() ->
    [{V,lists:seq(F,T)} || {V,{F,T}} <- vars_domains()].

smm() ->
    St = initial_state(),
    trace({init,St}),
    process(St, [], []).

% A State St is a list of pairs of form {VarName,Domain}, where
%    VarName could be anything (but here we only use atoms and integer 0);
%    Domain is a strictly ascending (possibly empty) list of integers.

% dec_adder([A, B, CI, S, CO], St0) = St, iff St is obtained by making the
% constraint A + B + CI =:= 10 * C0 + S arc-consistent in state St0.
% CI =:= carry in, CO =:= carry out.
dec_adder(VarNames, St0) ->
    [ADom0, BDom0, CIDom0, SDom0, CODom0] = 
	[ element(2,lists:keyfind(VarName,1,St0)) || VarName <- VarNames ],
    Sols =
	[ {A,B,CI,S,CO} ||
	    A <- ADom0, B <- BDom0, CI <- CIDom0, S <- SDom0, CO <- CODom0,
            A + B + CI =:= 10 * CO + S ],
    NewDoms =
	[ lists:usort([ element(I,Sol) || Sol <- Sols]) ||
	    I <- lists:seq(1,5) ],
    lists:foldl(fun new_var_dom/2, St0, lists:zip(VarNames,NewDoms)).

new_var_dom({VarName,_}=VND, St) ->
    lists:keyreplace(VarName, 1, St, VND).

narrow_domains(St0) ->
    St1 = dec_adder([d, e,  0, y, c1], St0),
    St2 = dec_adder([n, r, c1, e, c2], St1),
    St3 = dec_adder([e, o, c2, n, c3], St2),
    St4 = dec_adder([s, m, c3, o, c4], St3),
    St5 = dec_adder([0, 0, c4, m,  0], St4),
    Singletons = [ V || {_,[V]} <- problem_vars(St5) ],
    if length(Singletons) =:= 8 ->
            sendmory:statistics_count();
       true ->
            true
    end,
    AllDiff = sendmory:all_different(Singletons),
    if AllDiff -> St5;
       true -> new_var_dom({0,[]},St5)  % infeasible state
    end.
	     
% process(St0, Sts, Sols0) = Sols iff Sols1 is the set of solutions
% obtained from state list [St0|Sts] and Sols = Sols1++Sols0.
process(final, [], Sols0) ->
    [{S,E,N,D,M,O,R,Y} || [S,E,N,D,M,O,R,Y] <- Sols0];
process(final, [St|Sts], Sols0) ->
    trace({backtrack,St}),
    process(St, Sts, Sols0);
process(St0, Sts, Sols0) ->
    St = narrow_domains(St0),
    trace({domains,St}),
    DomSizes = [ length(Dom) || {_,Dom} <- St ],
    Max = lists:max(DomSizes),
    Min = lists:min(DomSizes),
    if Min =:= 0 ->      % there are empty domains
	    trace({failure}),
	    process(final, Sts, Sols0);
       (St =/= St0) ->  % state changed
	    process(St, Sts, Sols0);
       Max =:= 1 ->      % all domains singletons, i.e. solution found
	    trace({solution}), 
	    Sol = [Val || {_,[Val]} <- problem_vars(St)],
	    process(final, Sts, [Sol|Sols0]);
       true ->
	    {CSt1, CSt2} = make_choice(St),   % labeling
	    process(CSt1, [CSt2|Sts], Sols0)
    end.

% make_choice(St) = {CSt1, CSt2}: The union of the sets of solutions of
% states CSt1 and CSt2 is the same as that of St.  The new states are
% obtained by finding the first non-singleton domain [H|T] and splitting it
% to [H] and T. Precondition: there are no empty domains in St.
make_choice(St) ->
    {L1,L2} = lists:splitwith(fun({_,Dom}) -> length(Dom) =:= 1 end, St),
    [{V,[H|T]}|L3] = L2,
    trace({choice,V,H}),
    {L1++[{V,[H]}]++L3, L1++[{V,T}]++L3}.


% --------------------- TRACING ------------------------


trace(Msg) ->
    DoTrace = wants_trace(),
    case {DoTrace,Msg} of
	{false,_} -> true;
	{_,{init,St}} ->
	    put(choice_counter, 1),
	    put(choice_stack, []),
	    io:format("% --- Initial state:~n", []),
	    print_state(St);
	{_,{solution}} ->
	    io:format("% *** *** *** *** *** *** *** *** *** *** "
		      "Solution found, see line above. *** *** "
		      "*** *** *** *** *** *** *** *** ~n", []);
	{_,{domains,St}} ->
	    print_state(St);
	{_,{choice,Var,Val}} ->
	    C = get(choice_counter), put(choice_counter,C+1),
	    put(choice_stack, [{C,Var,Val}|get(choice_stack)]),
	    io:format("% --- Choice point  ~w, branch: ~w = ~w.~n",
		      [C,Var,Val]);
	{_,{failure}} ->
	    io:format("% *** Failing, empty domain or repeated singleton found.~n", []);
	{_,{backtrack,St}} ->
	    [{C,Var,Val}|Choices] = get(choice_stack),
	    put(choice_stack,Choices),
	    io:format("% --- Back to ch.p. ~w, branch: ~w > ~w.~n",
		      [C,Var,Val]),
	    print_state(St)
    end.

print_state([_|St]) ->
    [_|VDs] = vars_domains(),
    io:format("% ", []),
    print_state(St, VDs).

print_state([{_,Dom}|St], [{V,{F,T}}|VDs]) ->
    DString = [ case lists:member(I,Dom) of true -> $0+I; _ -> $ end
		|| I <- lists:seq(F,T) ],
    io:format(" ~w: ~s", [V,DString]),
    print_state(St, VDs);
print_state(_, []) -> io:nl().

%%%% Trace output %%%%

% --- Initial state:
%  c1: 01 c2: 01 c3: 01 c4: 01 s: 123456789 e: 0123456789 n: 0123456789 d: 0123456789 m: 123456789 o: 0123456789 r: 0123456789 y: 0123456789
%  c1: 01 c2: 01 c3: 01 c4:  1 s: 123456789 e: 0123456789 n: 0123456789 d: 0123456789 m: 1         o: 0123456789 r: 0123456789 y: 0123456789
%  c1: 01 c2: 01 c3: 01 c4:  1 s:        89 e: 0123456789 n: 0123456789 d: 0123456789 m: 1         o: 01         r: 0123456789 y: 0123456789
%  c1: 01 c2: 01 c3: 01 c4:  1 s:        89 e: 0123456789 n: 0123456789 d: 0123456789 m: 1         o: 01         r: 0123456789 y: 0123456789
% --- Choice point  1, branch: c1 = 0.
%  c1: 0  c2: 01 c3: 01 c4:  1 s:        89 e: 0123456789 n: 0123456789 d: 0123456789 m: 1         o: 01         r: 0123456789 y: 0123456789
% --- Choice point  2, branch: c2 = 0.
%  c1: 0  c2: 0  c3: 01 c4:  1 s:        89 e: 0123456789 n: 0123456789 d: 0123456789 m: 1         o: 01         r: 0123456789 y: 0123456789
% --- Choice point  3, branch: c3 = 0.
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e: 0123456789 n: 0123456789 d: 0123456789 m: 1         o: 0          r: 0123456789 y: 0123456789
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e: 0123456789 n: 0123456789 d: 0123456789 m: 1         o: 0          r: 0123456789 y: 0123456789
% --- Choice point  4, branch: e = 0.
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e: 0          n: 0          d: 0123456789 m: 1         o: 0          r: 0          y: 0123456789
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 4, branch: e > 0.
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:  123456789 n: 0123456789 d: 0123456789 m: 1         o: 0          r: 0123456789 y: 0123456789
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:  123456789 n:  123456789 d: 012345678  m: 1         o: 0          r: 0123456789 y:  123456789
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:  123456789 n:  123456789 d: 012345678  m: 1         o: 0          r: 012345678  y:  123456789
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:  123456789 n:  123456789 d: 012345678  m: 1         o: 0          r: 012345678  y:  123456789
% --- Choice point  5, branch: e = 1.
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:  1         n:  1         d: 012345678  m: 1         o: 0          r: 0          y:  123456789
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 5, branch: e > 1.
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:   23456789 n:  123456789 d: 012345678  m: 1         o: 0          r: 012345678  y:  123456789
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:   23456789 n:   23456789 d: 01234567   m: 1         o: 0          r: 012345678  y:   23456789
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:   23456789 n:   23456789 d: 01234567   m: 1         o: 0          r: 01234567   y:   23456789
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:   23456789 n:   23456789 d: 01234567   m: 1         o: 0          r: 01234567   y:   23456789
% --- Choice point  6, branch: e = 2.
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:   2        n:   2        d: 01234567   m: 1         o: 0          r: 0          y:   23456789
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 6, branch: e > 2.
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:    3456789 n:   23456789 d: 01234567   m: 1         o: 0          r: 01234567   y:   23456789
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:    3456789 n:    3456789 d: 0123456    m: 1         o: 0          r: 01234567   y:    3456789
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:    3456789 n:    3456789 d: 0123456    m: 1         o: 0          r: 0123456    y:    3456789
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:    3456789 n:    3456789 d: 0123456    m: 1         o: 0          r: 0123456    y:    3456789
% --- Choice point  7, branch: e = 3.
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:    3       n:    3       d: 0123456    m: 1         o: 0          r: 0          y:    3456789
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 7, branch: e > 3.
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:     456789 n:    3456789 d: 0123456    m: 1         o: 0          r: 0123456    y:    3456789
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:     456789 n:     456789 d: 012345     m: 1         o: 0          r: 0123456    y:     456789
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:     456789 n:     456789 d: 012345     m: 1         o: 0          r: 012345     y:     456789
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:     456789 n:     456789 d: 012345     m: 1         o: 0          r: 012345     y:     456789
% --- Choice point  8, branch: e = 4.
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:     4      n:     4      d: 012345     m: 1         o: 0          r: 0          y:     456789
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 8, branch: e > 4.
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:      56789 n:     456789 d: 012345     m: 1         o: 0          r: 012345     y:     456789
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:      56789 n:      56789 d: 01234      m: 1         o: 0          r: 012345     y:      56789
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:      56789 n:      56789 d: 01234      m: 1         o: 0          r: 01234      y:      56789
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:      56789 n:      56789 d: 01234      m: 1         o: 0          r: 01234      y:      56789
% --- Choice point  9, branch: e = 5.
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:      5     n:      5     d: 01234      m: 1         o: 0          r: 0          y:      56789
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 9, branch: e > 5.
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:       6789 n:      56789 d: 01234      m: 1         o: 0          r: 01234      y:      56789
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:       6789 n:       6789 d: 0123       m: 1         o: 0          r: 01234      y:       6789
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:       6789 n:       6789 d: 0123       m: 1         o: 0          r: 0123       y:       6789
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:       6789 n:       6789 d: 0123       m: 1         o: 0          r: 0123       y:       6789
% --- Choice point  10, branch: e = 6.
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:       6    n:       6    d: 0123       m: 1         o: 0          r: 0          y:       6789
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 10, branch: e > 6.
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:        789 n:       6789 d: 0123       m: 1         o: 0          r: 0123       y:       6789
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:        789 n:        789 d: 012        m: 1         o: 0          r: 0123       y:        789
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:        789 n:        789 d: 012        m: 1         o: 0          r: 012        y:        789
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:        789 n:        789 d: 012        m: 1         o: 0          r: 012        y:        789
% --- Choice point  11, branch: e = 7.
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:        7   n:        7   d: 012        m: 1         o: 0          r: 0          y:        789
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 11, branch: e > 7.
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:         89 n:        789 d: 012        m: 1         o: 0          r: 012        y:        789
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:         89 n:         89 d: 01         m: 1         o: 0          r: 012        y:         89
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:         89 n:         89 d: 01         m: 1         o: 0          r: 01         y:         89
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:         89 n:         89 d: 01         m: 1         o: 0          r: 01         y:         89
% --- Choice point  12, branch: e = 8.
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:         8  n:         8  d: 01         m: 1         o: 0          r: 0          y:         89
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 12, branch: e > 8.
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:          9 n:         89 d: 01         m: 1         o: 0          r: 01         y:         89
%  c1: 0  c2: 0  c3: 0  c4:  1 s:         9 e:          9 n:          9 d: 0          m: 1         o: 0          r: 01         y:          9
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 3, branch: c3 > 0.
%  c1: 0  c2: 0  c3:  1 c4:  1 s:        89 e: 0123456789 n: 0123456789 d: 0123456789 m: 1         o: 01         r: 0123456789 y: 0123456789
%  c1: 0  c2: 0  c3:  1 c4:  1 s:         9 e:          9 n: 0          d: 0123456789 m: 1         o:  1         r: 0123456789 y: 0123456789
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 2, branch: c2 > 0.
%  c1: 0  c2:  1 c3: 01 c4:  1 s:        89 e: 0123456789 n: 0123456789 d: 0123456789 m: 1         o: 01         r: 0123456789 y: 0123456789
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e: 012345678  n:  123456789 d: 0123456789 m: 1         o: 0          r:  123456789 y: 0123456789
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e: 012345678  n:  123456789 d: 0123456789 m: 1         o: 0          r:  123456789 y: 0123456789
% --- Choice point  13, branch: e = 0.
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e: 0          n:  1         d: 0123456789 m: 1         o: 0          r:  123456789 y: 0123456789
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 13, branch: e > 0.
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:  12345678  n:  123456789 d: 0123456789 m: 1         o: 0          r:  123456789 y: 0123456789
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:  12345678  n:   23456789 d: 012345678  m: 1         o: 0          r:   23456789 y:  123456789
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:  12345678  n:   23456789 d: 012345678  m: 1         o: 0          r:   23456789 y:  123456789
% --- Choice point  14, branch: e = 1.
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:  1         n:   2        d: 012345678  m: 1         o: 0          r:   23456789 y:  123456789
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 14, branch: e > 1.
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:   2345678  n:   23456789 d: 012345678  m: 1         o: 0          r:   23456789 y:  123456789
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:   2345678  n:    3456789 d: 01234567   m: 1         o: 0          r:    3456789 y:   23456789
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:   2345678  n:    3456789 d: 01234567   m: 1         o: 0          r:    3456789 y:   23456789
% --- Choice point  15, branch: e = 2.
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:   2        n:    3       d: 01234567   m: 1         o: 0          r:    3456789 y:   23456789
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:   2        n:    3       d: 01234567   m: 1         o: 0          r:          9 y:   23456789
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 15, branch: e > 2.
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:    345678  n:    3456789 d: 01234567   m: 1         o: 0          r:    3456789 y:   23456789
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:    345678  n:     456789 d: 0123456    m: 1         o: 0          r:     456789 y:    3456789
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:    345678  n:     456789 d: 0123456    m: 1         o: 0          r:     456789 y:    3456789
% --- Choice point  16, branch: e = 3.
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:    3       n:     4      d: 0123456    m: 1         o: 0          r:     456789 y:    3456789
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:    3       n:     4      d: 0123456    m: 1         o: 0          r:          9 y:    3456789
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 16, branch: e > 3.
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:     45678  n:     456789 d: 0123456    m: 1         o: 0          r:     456789 y:    3456789
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:     45678  n:      56789 d: 012345     m: 1         o: 0          r:      56789 y:     456789
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:     45678  n:      56789 d: 012345     m: 1         o: 0          r:      56789 y:     456789
% --- Choice point  17, branch: e = 4.
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:     4      n:      5     d: 012345     m: 1         o: 0          r:      56789 y:     456789
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:     4      n:      5     d: 012345     m: 1         o: 0          r:          9 y:     456789
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 17, branch: e > 4.
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:      5678  n:      56789 d: 012345     m: 1         o: 0          r:      56789 y:     456789
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:      5678  n:       6789 d: 01234      m: 1         o: 0          r:       6789 y:      56789
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:      5678  n:       6789 d: 01234      m: 1         o: 0          r:       6789 y:      56789
% --- Choice point  18, branch: e = 5.
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:      5     n:       6    d: 01234      m: 1         o: 0          r:       6789 y:      56789
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:      5     n:       6    d: 01234      m: 1         o: 0          r:          9 y:      56789
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 18, branch: e > 5.
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:       678  n:       6789 d: 01234      m: 1         o: 0          r:       6789 y:      56789
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:       678  n:        789 d: 0123       m: 1         o: 0          r:        789 y:       6789
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:       678  n:        789 d: 0123       m: 1         o: 0          r:        789 y:       6789
% --- Choice point  19, branch: e = 6.
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:       6    n:        7   d: 0123       m: 1         o: 0          r:        789 y:       6789
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:       6    n:        7   d: 0123       m: 1         o: 0          r:          9 y:       6789
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 19, branch: e > 6.
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:        78  n:        789 d: 0123       m: 1         o: 0          r:        789 y:       6789
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:        78  n:         89 d: 012        m: 1         o: 0          r:         89 y:        789
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:        78  n:         89 d: 012        m: 1         o: 0          r:         89 y:        789
% --- Choice point  20, branch: e = 7.
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:        7   n:         8  d: 012        m: 1         o: 0          r:         89 y:        789
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:        7   n:         8  d: 012        m: 1         o: 0          r:          9 y:        789
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 20, branch: e > 7.
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:         8  n:         89 d: 012        m: 1         o: 0          r:         89 y:        789
%  c1: 0  c2:  1 c3: 0  c4:  1 s:         9 e:         8  n:          9 d: 01         m: 1         o: 0          r:          9 y:         89
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 1, branch: c1 > 0.
%  c1:  1 c2: 01 c3: 01 c4:  1 s:        89 e: 0123456789 n: 0123456789 d: 0123456789 m: 1         o: 01         r: 0123456789 y: 0123456789
%  c1:  1 c2: 01 c3: 01 c4:  1 s:        89 e:  123456789 n: 0123456789 d:  123456789 m: 1         o: 01         r: 0123456789 y: 012345678 
%  c1:  1 c2: 01 c3: 01 c4:  1 s:        89 e:  123456789 n: 0123456789 d:  123456789 m: 1         o: 01         r: 0123456789 y: 012345678 
% --- Choice point  21, branch: c2 = 0.
%  c1:  1 c2: 0  c3: 01 c4:  1 s:        89 e:  123456789 n: 012345678  d:  123456789 m: 1         o: 01         r: 012345678  y: 012345678 
%  c1:  1 c2: 0  c3: 01 c4:  1 s:        89 e:  123456789 n: 012345678  d:  123456789 m: 1         o: 01         r: 012345678  y: 012345678 
% --- Choice point  22, branch: c3 = 0.
%  c1:  1 c2: 0  c3: 0  c4:  1 s:         9 e:  12345678  n:  12345678  d:  123456789 m: 1         o: 0          r: 012345678  y: 012345678 
%  c1:  1 c2: 0  c3: 0  c4:  1 s:         9 e:   234567   n:   234567   d:   23456789 m: 1         o: 0          r: 0123456    y: 01234567  
%  c1:  1 c2: 0  c3: 0  c4:  1 s:         9 e:    3456    n:    3456    d:    3456789 m: 1         o: 0          r: 01234      y: 0123456   
%  c1:  1 c2: 0  c3: 0  c4:  1 s:         9 e:     45     n:     45     d:     456789 m: 1         o: 0          r: 012        y: 012345    
%  c1:  1 c2:    c3:    c4:    s:           e:            n:            d:      56789 m:           o:            r: 0          y: 01234     
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 22, branch: c3 > 0.
%  c1:  1 c2: 0  c3:  1 c4:  1 s:        89 e:  123456789 n: 012345678  d:  123456789 m: 1         o: 01         r: 012345678  y: 012345678 
%  c1:  1 c2: 0  c3:  1 c4:  1 s:         9 e:          9 n: 0          d:  123456789 m: 1         o:  1         r: 012345678  y: 012345678 
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 21, branch: c2 > 0.
%  c1:  1 c2:  1 c3: 01 c4:  1 s:        89 e:  123456789 n: 0123456789 d:  123456789 m: 1         o: 01         r: 0123456789 y: 012345678 
%  c1:  1 c2:  1 c3: 01 c4:  1 s:        89 e:  123456789 n:  123456789 d:  123456789 m: 1         o: 01         r:  123456789 y: 012345678 
%  c1:  1 c2:  1 c3: 01 c4:  1 s:        89 e:  123456789 n:  123456789 d:  123456789 m: 1         o: 01         r:  123456789 y: 012345678 
% --- Choice point  23, branch: c3 = 0.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:  12345678  n:   23456789 d:  123456789 m: 1         o: 0          r:  123456789 y: 012345678 
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:  12345678  n:   23456789 d:   23456789 m: 1         o: 0          r:  123456789 y: 01234567  
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:  12345678  n:   23456789 d:   23456789 m: 1         o: 0          r:  123456789 y: 01234567  
% --- Choice point  24, branch: e = 1.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:  1         n:   2        d:          9 m: 1         o: 0          r:  12345678  y: 0         
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 24, branch: e > 1.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:   2345678  n:   23456789 d:   23456789 m: 1         o: 0          r:  123456789 y: 01234567  
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:   2345678  n:    3456789 d:   23456789 m: 1         o: 0          r:   23456789 y: 01234567  
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:   2345678  n:    3456789 d:   23456789 m: 1         o: 0          r:   23456789 y: 01234567  
% --- Choice point  25, branch: e = 2.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:   2        n:    3       d:         89 m: 1         o: 0          r:   2345678  y: 01        
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:   2        n:    3       d:         89 m: 1         o: 0          r:         8  y: 01        
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:   2        n:    3       d:         89 m: 1         o: 0          r:         8  y: 01        
% --- Choice point  26, branch: d = 8.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:   2        n:    3       d:         8  m: 1         o: 0          r:         8  y: 0         
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 26, branch: d > 8.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:   2        n:    3       d:          9 m: 1         o: 0          r:         8  y: 01        
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:   2        n:    3       d:          9 m: 1         o: 0          r:         8  y:  1        
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 25, branch: e > 2.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:    345678  n:    3456789 d:   23456789 m: 1         o: 0          r:   23456789 y: 01234567  
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:    345678  n:     456789 d:   23456789 m: 1         o: 0          r:    3456789 y: 01234567  
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:    345678  n:     456789 d:   23456789 m: 1         o: 0          r:    3456789 y: 01234567  
% --- Choice point  27, branch: e = 3.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:    3       n:     4      d:        789 m: 1         o: 0          r:    345678  y: 012       
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:    3       n:     4      d:        789 m: 1         o: 0          r:         8  y: 012       
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:    3       n:     4      d:        789 m: 1         o: 0          r:         8  y: 012       
% --- Choice point  28, branch: d = 7.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:    3       n:     4      d:        7   m: 1         o: 0          r:         8  y: 0         
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 28, branch: d > 7.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:    3       n:     4      d:         89 m: 1         o: 0          r:         8  y: 012       
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:    3       n:     4      d:         89 m: 1         o: 0          r:         8  y:  12       
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:    3       n:     4      d:         89 m: 1         o: 0          r:         8  y:  12       
% --- Choice point  29, branch: d = 8.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:    3       n:     4      d:         8  m: 1         o: 0          r:         8  y:  1        
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 29, branch: d > 8.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:    3       n:     4      d:          9 m: 1         o: 0          r:         8  y:  12       
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:    3       n:     4      d:          9 m: 1         o: 0          r:         8  y:   2       
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 27, branch: e > 3.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:     45678  n:     456789 d:   23456789 m: 1         o: 0          r:    3456789 y: 01234567  
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:     45678  n:      56789 d:   23456789 m: 1         o: 0          r:     456789 y: 01234567  
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:     45678  n:      56789 d:   23456789 m: 1         o: 0          r:     456789 y: 01234567  
% --- Choice point  30, branch: e = 4.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:     4      n:      5     d:       6789 m: 1         o: 0          r:     45678  y: 0123      
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:     4      n:      5     d:       6789 m: 1         o: 0          r:         8  y: 0123      
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:     4      n:      5     d:       6789 m: 1         o: 0          r:         8  y: 0123      
% --- Choice point  31, branch: d = 6.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:     4      n:      5     d:       6    m: 1         o: 0          r:         8  y: 0         
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 31, branch: d > 6.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:     4      n:      5     d:        789 m: 1         o: 0          r:         8  y: 0123      
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:     4      n:      5     d:        789 m: 1         o: 0          r:         8  y:  123      
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:     4      n:      5     d:        789 m: 1         o: 0          r:         8  y:  123      
% --- Choice point  32, branch: d = 7.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:     4      n:      5     d:        7   m: 1         o: 0          r:         8  y:  1        
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 32, branch: d > 7.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:     4      n:      5     d:         89 m: 1         o: 0          r:         8  y:  123      
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:     4      n:      5     d:         89 m: 1         o: 0          r:         8  y:   23      
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:     4      n:      5     d:         89 m: 1         o: 0          r:         8  y:   23      
% --- Choice point  33, branch: d = 8.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:     4      n:      5     d:         8  m: 1         o: 0          r:         8  y:   2       
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 33, branch: d > 8.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:     4      n:      5     d:          9 m: 1         o: 0          r:         8  y:   23      
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:     4      n:      5     d:          9 m: 1         o: 0          r:         8  y:    3      
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 30, branch: e > 4.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:      5678  n:      56789 d:   23456789 m: 1         o: 0          r:     456789 y: 01234567  
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:      5678  n:       6789 d:   23456789 m: 1         o: 0          r:      56789 y: 01234567  
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:      5678  n:       6789 d:   23456789 m: 1         o: 0          r:      56789 y: 01234567  
% --- Choice point  34, branch: e = 5.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:      5     n:       6    d:      56789 m: 1         o: 0          r:      5678  y: 01234     
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:      5     n:       6    d:      56789 m: 1         o: 0          r:         8  y: 01234     
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:      5     n:       6    d:      56789 m: 1         o: 0          r:         8  y: 01234     
% --- Choice point  35, branch: d = 5.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:      5     n:       6    d:      5     m: 1         o: 0          r:         8  y: 0         
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 35, branch: d > 5.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:      5     n:       6    d:       6789 m: 1         o: 0          r:         8  y: 01234     
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:      5     n:       6    d:       6789 m: 1         o: 0          r:         8  y:  1234     
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:      5     n:       6    d:       6789 m: 1         o: 0          r:         8  y:  1234     
% --- Choice point  36, branch: d = 6.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:      5     n:       6    d:       6    m: 1         o: 0          r:         8  y:  1        
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 36, branch: d > 6.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:      5     n:       6    d:        789 m: 1         o: 0          r:         8  y:  1234     
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:      5     n:       6    d:        789 m: 1         o: 0          r:         8  y:   234     
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:      5     n:       6    d:        789 m: 1         o: 0          r:         8  y:   234     
% --- Choice point  37, branch: d = 7.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:      5     n:       6    d:        7   m: 1         o: 0          r:         8  y:   2       
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:      5     n:       6    d:        7   m: 1         o: 0          r:         8  y:   2       
% *** *** *** *** *** *** *** *** *** *** Solution found, see line above. *** *** *** *** *** *** *** *** *** *** 
% --- Back to ch.p. 37, branch: d > 7.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:      5     n:       6    d:         89 m: 1         o: 0          r:         8  y:   234     
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:      5     n:       6    d:         89 m: 1         o: 0          r:         8  y:    34     
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:      5     n:       6    d:         89 m: 1         o: 0          r:         8  y:    34     
% --- Choice point  38, branch: d = 8.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:      5     n:       6    d:         8  m: 1         o: 0          r:         8  y:    3      
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 38, branch: d > 8.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:      5     n:       6    d:          9 m: 1         o: 0          r:         8  y:    34     
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:      5     n:       6    d:          9 m: 1         o: 0          r:         8  y:     4     
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 34, branch: e > 5.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:       678  n:       6789 d:   23456789 m: 1         o: 0          r:      56789 y: 01234567  
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:       678  n:        789 d:   23456789 m: 1         o: 0          r:       6789 y: 01234567  
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:       678  n:        789 d:   23456789 m: 1         o: 0          r:       6789 y: 01234567  
% --- Choice point  39, branch: e = 6.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:       6    n:        7   d:     456789 m: 1         o: 0          r:       678  y: 012345    
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:       6    n:        7   d:     456789 m: 1         o: 0          r:         8  y: 012345    
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:       6    n:        7   d:     456789 m: 1         o: 0          r:         8  y: 012345    
% --- Choice point  40, branch: d = 4.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:       6    n:        7   d:     4      m: 1         o: 0          r:         8  y: 0         
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 40, branch: d > 4.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:       6    n:        7   d:      56789 m: 1         o: 0          r:         8  y: 012345    
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:       6    n:        7   d:      56789 m: 1         o: 0          r:         8  y:  12345    
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:       6    n:        7   d:      56789 m: 1         o: 0          r:         8  y:  12345    
% --- Choice point  41, branch: d = 5.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:       6    n:        7   d:      5     m: 1         o: 0          r:         8  y:  1        
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 41, branch: d > 5.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:       6    n:        7   d:       6789 m: 1         o: 0          r:         8  y:  12345    
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:       6    n:        7   d:       6789 m: 1         o: 0          r:         8  y:   2345    
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:       6    n:        7   d:       6789 m: 1         o: 0          r:         8  y:   2345    
% --- Choice point  42, branch: d = 6.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:       6    n:        7   d:       6    m: 1         o: 0          r:         8  y:   2       
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 42, branch: d > 6.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:       6    n:        7   d:        789 m: 1         o: 0          r:         8  y:   2345    
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:       6    n:        7   d:        789 m: 1         o: 0          r:         8  y:    345    
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:       6    n:        7   d:        789 m: 1         o: 0          r:         8  y:    345    
% --- Choice point  43, branch: d = 7.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:       6    n:        7   d:        7   m: 1         o: 0          r:         8  y:    3      
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 43, branch: d > 7.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:       6    n:        7   d:         89 m: 1         o: 0          r:         8  y:    345    
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:       6    n:        7   d:         89 m: 1         o: 0          r:         8  y:     45    
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:       6    n:        7   d:         89 m: 1         o: 0          r:         8  y:     45    
% --- Choice point  44, branch: d = 8.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:       6    n:        7   d:         8  m: 1         o: 0          r:         8  y:     4     
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 44, branch: d > 8.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:       6    n:        7   d:          9 m: 1         o: 0          r:         8  y:     45    
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:       6    n:        7   d:          9 m: 1         o: 0          r:         8  y:      5    
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 39, branch: e > 6.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:        78  n:        789 d:   23456789 m: 1         o: 0          r:       6789 y: 01234567  
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:        78  n:         89 d:   23456789 m: 1         o: 0          r:        789 y: 01234567  
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:        78  n:         89 d:   23456789 m: 1         o: 0          r:        789 y: 01234567  
% --- Choice point  45, branch: e = 7.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:        7   n:         8  d:    3456789 m: 1         o: 0          r:        78  y: 0123456   
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:        7   n:         8  d:    3456789 m: 1         o: 0          r:         8  y: 0123456   
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 45, branch: e > 7.
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:         8  n:         89 d:   23456789 m: 1         o: 0          r:        789 y: 01234567  
%  c1:  1 c2:  1 c3: 0  c4:  1 s:         9 e:         8  n:          9 d:   23456789 m: 1         o: 0          r:         89 y: 01234567  
% *** Failing, empty domain or repeated singleton found.
% --- Back to ch.p. 23, branch: c3 > 0.
%  c1:  1 c2:  1 c3:  1 c4:  1 s:        89 e:  123456789 n:  123456789 d:  123456789 m: 1         o: 01         r:  123456789 y: 012345678 
%  c1:  1 c2:  1 c3:  1 c4:  1 s:         9 e:          9 n:  1         d:  123456789 m: 1         o:  1         r:  123456789 y: 012345678 
% *** Failing, empty domain or repeated singleton found.
