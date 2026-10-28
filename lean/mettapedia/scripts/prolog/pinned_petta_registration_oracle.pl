:- initialization(main, main).

:- use_module(library(apply)).
:- use_module(library(clpfd)).
:- use_module(library(dcg/basics)).
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

read_expanded_source(Stream) :-
    read_term(Stream, Term, []),
    ( Term == end_of_file
    -> true
    ; Term = (:- dynamic(Declaration))
    -> dynamic(Declaration), read_expanded_source(Stream)
    ; Term = (:- _)
    -> read_expanded_source(Stream)
    ; expand_term(Term, Expanded),
      assert_expanded(Expanded),
      read_expanded_source(Stream)
    ).

assert_expanded([]).
assert_expanded([Head|Tail]) :- !,
    assertz(Head),
    assert_expanded(Tail).
assert_expanded(Term) :- assertz(Term).

load_expanded_source(Path) :-
    setup_call_cleanup(open(Path, read, Stream),
                       read_expanded_source(Stream),
                       close(Stream)).

emit_answers(Label, Input, ExpectedAnswers) :-
    findall(Out, eval(Input, Out), Answers),
    ( Answers == ExpectedAnswers
    -> format('~w=exact~n', [Label])
    ; throw(error(eval_mismatch(Label, Answers, ExpectedAnswers), _))
    ).

emit_eval(Label, Input, Expected) :-
    emit_answers(Label, Input, [Expected]).

main([MettaPath, TranslatorPath, SpecializerPath,
      ParserPath, FilereaderPath, SpacesPath, MettaInputPath,
      IdentityInputPath]) :-
    load_source(TranslatorPath, none, _),
    load_source(SpecializerPath, none, _),
    load_expanded_source(ParserPath),
    load_expanded_source(SpacesPath),
    load_expanded_source(FilereaderPath),
    load_source(MettaPath, none, RegistrationTerm),
    RegistrationTerm = (:- Registration),
    call(Registration),
    assertz(silent(true)),
    format('metta_silent_setup=exact~n', []),
    load_metta_file(MettaInputPath, [a], '&self'),
    format('metta_load_file=exact~n', []),
    'file-id'(a, a),
    format('metta_loaded_file_definition=exact~n', []),
    with_output_to(string("is 1, should 1. ✅ \n"),
      load_metta_file(IdentityInputPath, [true], '&self')),
    format('metta_identity_format_output_and_result=exact~n', []),
    f(3, 9),
    format('metta_identity_definition_after_format=exact~n', []),
    fun(id),
    format('metta_fun_id_registered=exact~n', []),
    id(a, a),
    format('metta_id_direct=exact~n', []),
    term_variables(pair(TermVariablesLeft, TermVariablesRight), TermVariables),
    TermVariables = [TermVariablesLeft, TermVariablesRight],
    format('metta_term_variables_direct=exact~n', []),
    numbervars(pair(Numbered, pair(Numbered, Singleton)), 0, NumberEnd,
      [singletons(true)]),
    result(Numbered, Singleton, NumberEnd) =
      result('$VAR'(0), '$VAR'('_'), 1),
    format('metta_numbervars_direct=exact~n', []),
    normalize_specialization_key(
      pair(Normalized, pair(Normalized, _NormalizedSingleton)),
      NormalizedKey),
    NormalizedKey = pair('$VAR'(0), pair('$VAR'(0), '$VAR'('_'))),
    format('metta_normalize_specialization_key=exact~n', []),
    normalize_specialization_key(
      pair(HashInput, pair(HashInput, _HashSingleton)), HashKey),
    term_hash(HashKey, HashValue),
    HashValue = 4245664480,
    format('metta_term_hash_normalized_key=exact~n', []),
    functor(pair(a,b), pair, 2),
    format('metta_functor_decompose_direct=exact~n', []),
    functor(FunctorConstructed, pair, 2),
    FunctorConstructed = pair(a,b),
    format('metta_functor_construct_direct=exact~n', []),
    nb_setval(metta_runtime_global, f(GlobalSource)),
    GlobalSource = source,
    nb_getval(metta_runtime_global, GlobalStored),
    GlobalStored = f(stored),
    format('metta_nb_global_direct=exact~n', []),
    emit_eval(metta_eval_compound, [id,a], a),
    emit_eval(metta_eval_nested_arithmetic, [id,['+',1,2]], 3),
    emit_eval(metta_eval_imported_reverse, [reverse,[a,b]], [b,a]),
    emit_eval(metta_eval_if, [if,[>,2,1],then,else], then),
    emit_eval(metta_eval_map_atom, ['map-atom',[a,b],id], [a,b]),
    emit_eval(metta_eval_foldl_atom, ['foldl-atom',[1,2],0,'+'], 3),
    emit_eval(metta_eval_first_pair, ['first-from-pair',[a,b]], a),
    emit_eval(metta_eval_size, ['size-atom',[a,b]], 2),
    emit_eval(metta_eval_unique, ['unique-atom',[b,a,b]], [b,a]),
    process_metta_string(
        "(= (fresh-id $x) (id $x))\n!(fresh-id a)", [a]),
    format('metta_process_string=exact~n', []),
    'fresh-id'(a, a),
    format('metta_fresh_id_persisted=exact~n', []),
    'alpha-unique-atom'(
        [pair(X,X),pair(Y,Y),pair(Z,a)], AlphaUnique),
    AlphaUnique == [pair(X,X),pair(Z,a)],
    format('metta_alpha_unique_direct=exact~n', []),
    emit_answers(metta_eval_alpha_unique,
        ['alpha-unique',[superpose,[b,a,b]]],
        [b,a,['alpha-unique',b],['alpha-unique',a],['alpha-unique',b]]),
    emit_answers(metta_eval_superpose_order, [superpose,[a,b]], [a,b]),
    emit_eval(metta_eval_collapse, [collapse,[superpose,[a,b]]], [a,b]),
    emit_eval(metta_eval_once, [once,[superpose,[a,b]]], a),
    emit_eval(metta_eval_if_false, [if,[>,1,2],then,else], else),
    emit_answers(metta_eval_empty, [empty], []),
    emit_eval(metta_eval_transaction, [transaction,[id,a]], a),
    emit_eval(metta_eval_copy_term, [copy_term,[a,b]], [a,b]).
