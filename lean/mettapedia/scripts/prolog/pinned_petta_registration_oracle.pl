:- initialization(main, main).

:- use_module(library(apply)).
:- use_module(library(clpfd)).
:- use_module(library(lists)).
:- use_module(library(pairs)).
:- use_module(library(yall), except([(/)/3])).

read_source(Stream, Registration0, Registration) :-
    read_term(Stream, Term, []),
    ( Term == end_of_file
    -> Registration = Registration0
    ; Term = (:- maplist(register_fun, _))
    -> read_source(Stream, Term, Registration)
    ; Term = (:- dynamic(Declaration))
    -> dynamic(Declaration),
       read_source(Stream, Registration0, Registration)
    ; Term = (:- _)
    -> read_source(Stream, Registration0, Registration)
    ; assertz(Term),
      read_source(Stream, Registration0, Registration)
    ).

load_source(Path, Registration0, Registration) :-
    setup_call_cleanup(open(Path, read, Stream),
                       read_source(Stream, Registration0, Registration),
                       close(Stream)).

emit_answers(Label, Input, ExpectedAnswers) :-
    findall(Out, eval(Input, Out), Answers),
    ( Answers == ExpectedAnswers
    -> format('~w=exact~n', [Label])
    ; throw(error(eval_mismatch(Label, Answers, ExpectedAnswers), _))
    ).

emit_eval(Label, Input, Expected) :-
    emit_answers(Label, Input, [Expected]).

main([MettaPath, TranslatorPath, SpecializerPath]) :-
    load_source(TranslatorPath, none, _),
    load_source(SpecializerPath, none, _),
    load_source(MettaPath, none, RegistrationTerm),
    RegistrationTerm = (:- Registration),
    call(Registration),
    fun(id),
    format('metta_fun_id_registered=exact~n', []),
    id(a, a),
    format('metta_id_direct=exact~n', []),
    term_variables(pair(TermVariablesLeft, TermVariablesRight), TermVariables),
    TermVariables = [TermVariablesLeft, TermVariablesRight],
    format('metta_term_variables_direct=exact~n', []),
    emit_eval(metta_eval_compound, [id,a], a),
    emit_eval(metta_eval_nested_arithmetic, [id,['+',1,2]], 3),
    emit_eval(metta_eval_imported_reverse, [reverse,[a,b]], [b,a]),
    emit_eval(metta_eval_if, [if,[>,2,1],then,else], then),
    emit_eval(metta_eval_map_atom, ['map-atom',[a,b],id], [a,b]),
    emit_eval(metta_eval_foldl_atom, ['foldl-atom',[1,2],0,'+'], 3),
    emit_eval(metta_eval_first_pair, ['first-from-pair',[a,b]], a),
    emit_eval(metta_eval_size, ['size-atom',[a,b]], 2),
    emit_eval(metta_eval_unique, ['unique-atom',[b,a,b]], [b,a]),
    emit_answers(metta_eval_superpose_order, [superpose,[a,b]], [a,b]),
    emit_eval(metta_eval_collapse, [collapse,[superpose,[a,b]]], [a,b]),
    emit_eval(metta_eval_once, [once,[superpose,[a,b]]], a),
    emit_eval(metta_eval_if_false, [if,[>,1,2],then,else], else),
    emit_answers(metta_eval_empty, [empty], []),
    emit_eval(metta_eval_transaction, [transaction,[id,a]], a),
    emit_eval(metta_eval_copy_term, [copy_term,[a,b]], [a,b]).
