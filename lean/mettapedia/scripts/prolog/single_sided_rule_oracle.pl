/* Exact SWI-Prolog oracle for the canonical single-sided rule regressions. */

specific(a, Y) => Y = specific.
specific(_, Y) => Y = fallback.

guarded(a, Y), fail => Y = first.
guarded(_, Y) => Y = second.

committed(a, Y), true => Y = first.
committed(_, Y) => Y = second.

shape(pair(_A, _B), Y) => Y = matched.
shape(_, Y) => Y = fallback.

ordinary(a).

emit(Label, Template, Goal) :-
    findall(Template, Goal, Answers),
    format('~w=~q~n', [Label, Answers]).

main :-
    emit(caller_binding_rejected, Y, specific(_X, Y)),
    emit(ground_match_commits, Y, specific(a, Y)),
    emit(failed_guard_falls_through, Y, guarded(a, Y)),
    emit(successful_guard_commits, Y, committed(a, Y)),
    emit(fresh_head_bindings_allowed, Y, shape(pair(a, b), Y)),
    emit(ordinary_head_binds_caller, X, ordinary(X)).

:- initialization(main, main).
