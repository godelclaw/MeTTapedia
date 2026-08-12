:- use_module(library(assoc)).

tree(t(m, root, -, t(a, left, -, t, t), t(z, right, -, t, t))).

emit(Label, Key) :-
    tree(Tree),
    findall(Value, get_assoc(Key, Tree, Value), Answers),
    format('~w=~q~n', [Label, Answers]).

emit_goal(Label, Template, Goal) :-
    findall(Template, Goal, Answers),
    format('~w=~q~n', [Label, Answers]).

main :-
    emit(root, m),
    emit(left, a),
    emit(right, z),
    emit(missing, x),
    tree(Tree),
    emit_goal(keys, Keys, assoc_to_keys(Tree, Keys)),
    emit_goal(values, Values, assoc_to_values(Tree, Values)),
    emit_goal(generated_keys, Key, gen_assoc(Key, Tree, _)),
    emit_goal(min_key, MinKey, min_assoc(Tree, MinKey, _)),
    emit_goal(min_value, MinValue, min_assoc(Tree, _, MinValue)),
    emit_goal(max_key, MaxKey, max_assoc(Tree, MaxKey, _)),
    emit_goal(max_value, MaxValue, max_assoc(Tree, _, MaxValue)),
    emit_goal(update_old, Old,
        ( get_assoc(a, Tree, Old, Updated, updated),
          get_assoc(a, Updated, _)
        )),
    emit_goal(update_new, Seen,
        ( get_assoc(a, Tree, _, Updated, updated),
          get_assoc(a, Updated, Seen)
        )),
    emit_goal(insert_lookup, InsertedValue,
        ( put_assoc(x, Tree, middle, Inserted),
          get_assoc(x, Inserted, InsertedValue)
        )),
    emit_goal(insert_keys, InsertedKeys,
        ( put_assoc(x, Tree, middle, Inserted),
          assoc_to_keys(Inserted, InsertedKeys)
        )).

:- initialization(main, main).
