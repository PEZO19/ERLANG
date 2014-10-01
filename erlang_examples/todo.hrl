% @type todo() = {todo, atom(), atom(), term()}.
% 'todo' rekord, 3 mezővel: sts, who, txt.
-record(todo,{sts=remind,who='HP',txt}).
