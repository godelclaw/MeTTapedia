:- initialization(main, main).

expanded_head((Head :- _), Head) :- !.
expanded_head(Head, Head).

expanded_clause(Clauses, Clause) :- is_list(Clauses), !, last(Clauses, Clause).
expanded_clause(Clause, Clause).

read_dcgs(Stream, Label, Index0, Index) :-
    read_term(Stream, Term, []),
    (   Term == end_of_file
    ->  Index = Index0
    ;   Term = (_ --> _)
    ->  expand_term(Term, Clause),
        expanded_clause(Clause, OrdinaryClause),
        expanded_head(OrdinaryClause, Head),
        functor(Head, Name, Arity),
        format('~w:~w=~w/~w~n', [Label, Index0, Name, Arity]),
        Index1 is Index0 + 1,
        read_dcgs(Stream, Label, Index1, Index)
    ;   read_dcgs(Stream, Label, Index0, Index)
    ).

check_file(Label, Path, Count) :-
    setup_call_cleanup(open(Path, read, Stream),
                       read_dcgs(Stream, Label, 0, Count),
                       close(Stream)).

main([ParserPath, FileReaderPath]) :-
    check_file(parser, ParserPath, ParserCount),
    check_file(filereader, FileReaderPath, FileReaderCount),
    Total is ParserCount + FileReaderCount,
    format('total=~w~n', [Total]).
