:- initialization(main, main).

:- use_module(library(apply)).
:- use_module(library(clpfd)).

source_head((Head :- _), Head) :- !.
source_head(Head, Head).

selected_source_term(Term) :-
    source_head(Term, Head),
    functor(Head, Name, Arity),
    ( Name == id, Arity =:= 2
    ; Name == register_fun, Arity =:= 1
    ).

read_registration(Stream, Registration) :-
    read_term(Stream, Term, []),
    ( Term == end_of_file
    -> throw(error(missing_registration_directive, _))
    ; Term = (:- maplist(register_fun, _))
    -> Registration = Term
    ; selected_source_term(Term)
    -> assertz(Term),
       read_registration(Stream, Registration)
    ; read_registration(Stream, Registration)
    ).

load_registration(Path, Registration) :-
    setup_call_cleanup(open(Path, read, Stream),
                       read_registration(Stream, Registration),
                       close(Stream)).

main([MettaPath]) :-
    dynamic(fun/1),
    load_registration(MettaPath, (:- Registration)),
    call(Registration),
    fun(id),
    format('metta_fun_id_registered=exact~n', []),
    id(a, a),
    format('metta_id_direct=exact~n', []).
