:- use_module(library(http/json)).

variable_shape(Term, Variables, Names, [v, Name, Index]) :-
    nth0(Index, Variables, Variable),
    Variable == Term,
    !,
    (   member(NameAtom=Named, Names), Named == Term
    ->  atom_string(NameAtom, Name)
    ;   Name = "_"
    ).

term_shape(Term, Variables, Names, Shape) :-
    (   var(Term)
    ->  variable_shape(Term, Variables, Names, Shape)
    ;   integer(Term)
    ->  number_string(Term, Text), Shape = [i, Text]
    ;   float(Term)
    ->  ( Term =:= 1.0Inf
        -> Bits = "9218868437227405312"
        ; Term =:= -1.0Inf
        -> Bits = "18442240474082181120"
        ; throw(error(unmeasured_finite_float(Term), _))
        ),
        Shape = [f, Bits]
    ;   string(Term)
    ->  Shape = [s, Term]
    ;   Term == []
    ->  Shape = [a, "[]"]
    ;   atom(Term)
    ->  atom_string(Term, Name), Shape = [a, Name]
    ;   compound_name_arguments(Term, NameAtom, Arguments),
        atom_string(NameAtom, Name),
        maplist(term_shape_(Variables, Names), Arguments, Children),
        Shape = [c, Name, Children]
    ).

term_shape_(Variables, Names, Term, Shape) :-
    term_shape(Term, Variables, Names, Shape).

read_shapes(Stream, Count) :-
    read_term(Stream, Term, [variable_names(Names)]),
    (   Term == end_of_file
    ->  Count = 0
    ;   term_variables(Term, Variables),
        term_shape(Term, Variables, Names, Shape),
        json_write(current_output, Shape, [width(0)]), nl,
        read_shapes(Stream, Rest),
        Count is Rest + 1
    ).

check_file(Path, Count) :-
    setup_call_cleanup(open(Path, read, Stream), read_shapes(Stream, Count),
                       close(Stream)).

main :-
    op(200, fy, @),
    op(50, fx, #),
    use_module(library(clpfd)),
    current_prolog_flag(argv, Paths),
    maplist(check_file, Paths, Counts),
    sum_list(Counts, 317).

:- initialization(main, main).
