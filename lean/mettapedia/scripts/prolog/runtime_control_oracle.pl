:- initialization(main, main).

choose(a) :- !.
choose(b).

emit(Label, Goal, Template) :-
    findall(Template, Goal, Answers),
    atomic_list_concat(Answers, ',', Joined),
    format('~w=~w~n', [Label, Joined]).

main(_) :-
    emit(source_order, (X = a ; X = b), X),
    emit(restore_before_right, (Y = a, fail ; var(Y), Y = b), Y),
    emit(cut_prunes_right, (Z = a, ! ; Z = b), Z),
    emit(callee_cut_retains_caller, (choose(W) ; W = c), W).
