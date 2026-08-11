:- initialization(main, main).

main([Path]) :-
    load_files(Path, [silent(true)]),
    findall(1, (add_sexp(space, [rel, a]), space(rel, a)), Answers),
    length(Answers, Count),
    format('spaces_add=~w~n', [Count]).
