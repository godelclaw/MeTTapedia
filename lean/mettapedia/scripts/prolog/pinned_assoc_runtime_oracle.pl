:- use_module(library(assoc)).

tree(t(m, root, -, t(a, left, -, t, t), t(z, right, -, t, t))).

emit(Label, Key) :-
    tree(Tree),
    findall(Value, get_assoc(Key, Tree, Value), Answers),
    format('~w=~q~n', [Label, Answers]).

main :-
    emit(root, m),
    emit(left, a),
    emit(right, z),
    emit(missing, x).

:- initialization(main, main).
