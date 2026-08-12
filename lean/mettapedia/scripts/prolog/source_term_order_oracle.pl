:- initialization(main, main).

emit(Label, Goal, Term) :-
    once(Goal),
    term_string(Term, Rendered, [quoted(true), numbervars(true)]),
    format('~w=~w~n', [Label, Rendered]).

main(_) :-
    emit(sort_mixed,
         sort([b,"x",1,1.0,a,b], SortedMixed),
         SortedMixed),
    emit(msort_duplicates,
         msort([b,a,a], MsortedDuplicates),
         MsortedDuplicates),
    emit(keysort_stable,
         keysort([b-0,a-1,a-2], KeysortedStable),
         KeysortedStable),
    emit(sort_key_one,
         sort(1, @=<, [b-0,a-1,a-2], SortedKeyOne),
         SortedKeyOne),
    emit(sort_key_two,
         sort(2, @=<, [b-3,a-1,c-2], SortedKeyTwo),
         SortedKeyTwo),
    emit(sort_descending_unique,
         sort(0, @>, [a,c,b,c], SortedDescendingUnique),
         SortedDescendingUnique),
    emit(sort_signed_zero,
         sort([0.0,-0.0], SortedSignedZero),
         SortedSignedZero).
