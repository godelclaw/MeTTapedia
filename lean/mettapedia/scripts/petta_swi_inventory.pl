#!/usr/bin/env swipl
/*  Generate a deterministic static call inventory for the pinned PeTTa core.

    This intentionally delegates Prolog parsing, operators, directives and
    meta-predicate recognition to SWI-Prolog's own prolog_xref library.  It is
    an inventory, not a claim that static xref closes dynamic call/1 targets.
*/

:- use_module(library(http/json)).
:- use_module(library(lists)).
:- use_module(library(prolog_xref)).

:- initialization(main, main).

pinned_source('src/metta.pl').
pinned_source('src/translator.pl').
pinned_source('src/parser.pl').
pinned_source('src/specializer.pl').
pinned_source('src/filereader.pl').
pinned_source('src/spaces.pl').

main([Root0]) :- !,
    absolute_file_name(Root0, Root, [file_type(directory), access(read)]),
    findall(Absolute-Relative,
            ( pinned_source(Relative),
              directory_file_path(Root, Relative, Candidate),
              absolute_file_name(Candidate, Absolute,
                                 [file_type(prolog), access(read)])
            ),
            Sources),
    maplist(index_source, Sources),
    findall(Entry,
            ( member(Source, Sources),
              call_entry(Sources, Source, Entry)
            ),
            Calls0),
    sort(Calls0, Calls),
    findall(Import,
            ( member(Source, Sources),
              import_entry(Source, Import)
            ),
            Imports0),
    sort(Imports0, Imports),
    findall(_{path:Relative}, member(_-Relative, Sources), SourceRows),
    classification_counts(Calls, Counts),
    length(Calls, CallCount),
    length(Imports, ImportCount),
    Document = _{
        schema_version:1,
        generator:"SWI library(prolog_xref)",
        completeness:"static-only; dynamic and generated call targets require runtime traces",
        sources:SourceRows,
        calls:Calls,
        imports:Imports,
        summary:_{calls:CallCount, imports:ImportCount, classifications:Counts}
    },
    json_write_dict(current_output, Document, [width(0)]),
    nl.
main(_) :-
    format(user_error, 'usage: petta_swi_inventory.pl PETTA_ROOT~n', []),
    halt(2).

index_source(Absolute-_) :-
    xref_source(Absolute, [silent(true), register_called(all)]).

call_entry(Sources, Absolute-Relative, Entry) :-
    xref_called(Absolute, Called, By, Condition, Line),
    canonical_string(Called, CalledText),
    canonical_string(By, ByText),
    canonical_string(Condition, ConditionText),
    predicate_indicator(Called, Indicator),
    classify_call(Sources, Absolute, Called, Classification, Definition),
    Entry = _{
        source:Relative,
        line:Line,
        caller:ByText,
        called:CalledText,
        indicator:Indicator,
        condition:ConditionText,
        classification:Classification,
        definition:Definition
    }.

import_entry(Absolute-Relative, Entry) :-
    xref_uses_file(Absolute, Spec, Path),
    canonical_string(Spec, SpecText),
    canonical_string(Path, PathText),
    Entry = _{source:Relative, specification:SpecText, resolved:PathText}.

classify_call(_, _, Called, "meta-or-variable", "") :-
    strip_module_term(Called, Plain),
    var(Plain), !.
classify_call(_, _, Called, "swi-builtin", "") :-
    strip_module_term(Called, Plain),
    prolog_xref:xref_built_in(Plain), !.
classify_call(_, Absolute, Called, "source-accessible", HowText) :-
    ( xref_defined(Absolute, Called, How)
    ; strip_module_term(Called, Plain), xref_defined(Absolute, Plain, How)
    ), !,
    canonical_string(How, HowText).
classify_call(Sources, _, Called, "defined-in-pinned-source", Relative) :-
    member(Other-Relative, Sources),
    ( xref_defined(Other, Called, _)
    ; strip_module_term(Called, Plain), xref_defined(Other, Plain, _)
    ), !.
classify_call(_, _, _, "external-or-dynamic", "").

strip_module_term(_Module:Goal, Plain) :- !,
    strip_module_term(Goal, Plain).
strip_module_term(Goal, Goal).

predicate_indicator(Term, Indicator) :-
    strip_module_term(Term, Plain),
    ( var(Plain) ->
        Indicator = "<variable>"
    ; callable(Plain) ->
        functor(Plain, Name, Arity),
        format(string(Indicator), '~q/~d', [Name, Arity])
    ; Indicator = "<non-callable>"
    ).

canonical_string(Term, Text) :-
    copy_term(Term, Copy),
    numbervars(Copy, 0, _),
    with_output_to(string(Text), write_canonical(Copy)).

classification_counts(Calls, Counts) :-
    findall(Classification,
            ( member(Entry, Calls), Classification = Entry.classification ),
            Classes),
    msort(Classes, Sorted),
    run_counts(Sorted, Counts).

run_counts([], []).
run_counts([Head|Tail], [_{classification:Head, count:Count}|Counts]) :-
    take_same(Tail, Head, Same, Rest),
    length([Head|Same], Count),
    run_counts(Rest, Counts).

take_same([Head|Tail], Head, [Head|Same], Rest) :- !,
    take_same(Tail, Head, Same, Rest).
take_same(Rest, _, [], Rest).
