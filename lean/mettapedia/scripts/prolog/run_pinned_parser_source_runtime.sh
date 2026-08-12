#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 <PeTTa git tree> <SWI-Prolog git tree>" >&2
  exit 2
fi

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
PETTA_TREE="$(realpath "$1")"
SWI_TREE="$(realpath "$2")"
PIN="6b7f52f064bdbc82fabd0a0998404121fb01d52e"
SWI_PIN="6be143dbd030cc9ea621cde719a37f8385575453"
SWI_VERSION="SWI-Prolog version 10.1.9"

if [[ "$(swipl --version)" != "$SWI_VERSION"* ]]; then
  echo "pinned parser runtime gate requires $SWI_VERSION" >&2
  exit 1
fi

git -C "$PETTA_TREE" cat-file -e "$PIN^{commit}"
if [[ "$(git -C "$SWI_TREE" rev-parse HEAD)" != "$SWI_PIN" ]]; then
  echo "pinned parser runtime gate requires SWI source commit $SWI_PIN" >&2
  exit 1
fi

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
git -C "$PETTA_TREE" archive "$PIN" \
  src/metta.pl src/parser.pl src/translator.pl src/specializer.pl \
  src/filereader.pl src/spaces.pl examples/identity.metta | tar -x -C "$TMP"
git -C "$SWI_TREE" archive "$SWI_PIN" library/assoc.pl | tar -x -C "$TMP"

DCG_BASICS="$(swipl -q -g \
  "absolute_file_name(library('dcg/basics'), P, [file_type(prolog), access(read)]), write(P), halt")"
LISTS="$(swipl -q -g \
  "absolute_file_name(library(lists), P, [file_type(prolog), access(read)]), write(P), halt")"
ERROR="$(swipl -q -g \
  "absolute_file_name(library(error), P, [file_type(prolog), access(read)]), write(P), halt")"
APPLY="$(swipl -q -g \
  "absolute_file_name(library(apply), P, [file_type(prolog), access(read)]), write(P), halt")"
PAIRS="$(swipl -q -g \
  "absolute_file_name(library(pairs), P, [file_type(prolog), access(read)]), write(P), halt")"
ASSOC="$TMP/library/assoc.pl"

pushd "$ROOT_DIR" >/dev/null
if ! lake env lean --run scripts/prolog/pinned_parser_source_runtime.lean \
    "$TMP/src/metta.pl" "$TMP/src/parser.pl" \
    "$TMP/src/translator.pl" "$TMP/src/specializer.pl" \
    "$TMP/src/filereader.pl" "$TMP/src/spaces.pl" \
    "$DCG_BASICS" "$LISTS" "$ERROR" "$APPLY" "$PAIRS" "$ASSOC" \
    "$ROOT_DIR/scripts/prolog/pinned_file_runtime_fixture.metta" \
    "$TMP/examples/identity.metta" \
    > "$TMP/lean.out"; then
  cat "$TMP/lean.out" >&2
  popd >/dev/null
  exit 1
fi
popd >/dev/null

cat > "$TMP/lean.expected" <<'EOF'
empty_codes=[40,41]
empty_cleanup=0/0
atom_list_codes=[40,97,41]
atom_list_cleanup=0/0
integer_codes=[45,52,50]
integer_cleanup=0/0
read_atom=[|](a,[])
read_cleanup=0/0
qualified_number=exact
read_list=exact
read_integer=exact
read_negative=exact
read_float=exact
read_exponent=exact
read_string=exact
read_nested=exact
read_hyphen_atom=exact
read_numeric_looking_atom=exact
read_hash_atom=exact
read_escaped_string=exact
read_variable=exact
read_variable_reuse=exact
read_anonymous_separation=exact
sread_string=exact
sread_atom=exact
sread_variable_reuse=exact
swrite_list=exact
swrite_compound=exact
metta_parse=exact
metta_repr=exact
metta_eval_atomic=exact
metta_silent_setup=exact
metta_read_file_capability=exact
metta_load_file=exact
metta_loaded_file_definition=exact
metta_identity_diagnostic_gap_lean_empty=exact
metta_identity_definition_despite_diagnostic_gap=exact
metta_fun_id_registered=exact
metta_id_direct=exact
metta_copy_term_direct=exact
metta_term_variables_direct=exact
metta_numbervars_direct=exact
metta_normalize_specialization_key=exact
metta_term_hash_normalized_key=exact
metta_functor_decompose_direct=exact
metta_functor_construct_direct=exact
metta_nb_global_direct=exact
metta_eval_compound=exact
metta_eval_nested_arithmetic=exact
metta_eval_imported_reverse=exact
metta_eval_if=exact
metta_eval_map_atom=exact
metta_eval_foldl_atom=exact
metta_eval_first_pair=exact
metta_eval_size=exact
metta_eval_unique=exact
metta_process_string=exact
metta_fresh_id_persisted=exact
metta_alpha_unique_direct=exact
metta_eval_alpha_unique=exact
metta_eval_superpose_order=exact
metta_eval_collapse=exact
metta_eval_once=exact
metta_eval_if_false=exact
metta_eval_empty=exact
metta_eval_transaction=exact
metta_eval_copy_term=exact
EOF
diff -u "$TMP/lean.expected" "$TMP/lean.out"

swipl -q -s "$TMP/src/parser.pl" -s "$TMP/src/translator.pl" \
  -g "phrase(swrite_exp([]), Empty), write_canonical(Empty), nl, phrase(swrite_exp([a]), AtomList), write_canonical(AtomList), nl, phrase(swrite_exp(-42), IntegerCodes), write_canonical(IntegerCodes), nl, phrase(sexpr(ReadAtom, [], _), [40,97,41]), write_canonical(ReadAtom), nl, phrase(sexpr(ReadList, [], _), [40,97,32,98,41]), write_canonical(ReadList), nl, phrase(sexpr(ReadInteger, [], _), [40,49,41]), write_canonical(ReadInteger), nl, phrase(sexpr(ReadNegative, [], _), [40,45,50,41]), write_canonical(ReadNegative), nl, phrase(sexpr(ReadFloat, [], _), [40,49,46,53,41]), write_canonical(ReadFloat), nl, phrase(sexpr(ReadExponent, [], _), [40,49,101,50,41]), write_canonical(ReadExponent), nl, phrase(sexpr(ReadString, [], _), [40,34,97,34,41]), write_canonical(ReadString), nl, phrase(sexpr(ReadNested, [], _), [40,40,97,41,41]), write_canonical(ReadNested), nl, phrase(sexpr(ReadHyphen, [], _), [40,97,45,98,41]), write_canonical(ReadHyphen), nl, phrase(sexpr(ReadNumericAtom, [], _), [40,49,95,50,95,51,41]), write_canonical(ReadNumericAtom), nl, phrase(sexpr(ReadHash, [], _), [40,35,102,111,111,41]), write_canonical(ReadHash), nl, phrase(sexpr(ReadEscaped, [], _), [40,34,97,92,110,98,34,41]), write_canonical(ReadEscaped), nl, phrase(sexpr([ReadVariable], [], _), [40,36,120,41]), var(ReadVariable), writeln(variable), phrase(sexpr([ReuseLeft,ReuseRight], [], _), [40,36,120,32,36,120,41]), ReuseLeft==ReuseRight, writeln(reused), phrase(sexpr([AnonymousLeft,AnonymousRight], [], _), [40,36,95,32,36,95,41]), AnonymousLeft\\==AnonymousRight, writeln(anonymous_distinct), sread(\"(a b)\", SReadString), write_canonical(SReadString), nl, sread('(1)', SReadAtom), write_canonical(SReadAtom), nl, string_codes(SReadVariableInput, [40,36,120,32,36,120,41]), sread(SReadVariableInput, [SReadLeft,SReadRight]), SReadLeft==SReadRight, writeln(sread_reused), swrite([a,b], SWriteList), write_canonical(SWriteList), nl, swrite(pair(a,b), SWriteCompound), write_canonical(SWriteCompound), nl, open('$TMP/src/metta.pl', read, MettaStream), repeat, read_term(MettaStream, MettaTerm, []), (MettaTerm = (repr(_,_):-_) -> assertz(MettaTerm), fail ; MettaTerm = (parse(_,_):-_) -> assertz(MettaTerm), ! ; MettaTerm == end_of_file -> throw(error(missing_metta_wrappers, _)) ; fail), close(MettaStream), parse(\"(a b)\", MettaParse), write_canonical(MettaParse), nl, repr(pair(a,b), MettaRepr), write_canonical(MettaRepr), nl, use_module(library(clpfd)), open('$TMP/src/metta.pl', read, MettaEvalStream), repeat, read_term(MettaEvalStream, MettaEvalTerm, []), (MettaEvalTerm = (eval(_,_):-_) -> assertz(MettaEvalTerm), fail ; MettaEvalTerm = call_goals([]) -> assertz(MettaEvalTerm), fail ; MettaEvalTerm = (call_goals([_|_]):-_) -> assertz(MettaEvalTerm), ! ; MettaEvalTerm == end_of_file -> throw(error(missing_metta_eval, _)) ; fail), close(MettaEvalStream), eval(a, MettaEval), write_canonical(MettaEval), nl, halt" \
  > "$TMP/swi.out"
printf '%s\n' '[40,41]' '[40,97,41]' '[45,52,50]' '[a]' '[a,b]' '[1]' '[-2]' '[1.5]' '[100.0]' '["a"]' '[[a]]' "['a-b']" "['1_2_3']" "['#foo']" '["a\nb"]' 'variable' 'reused' 'anonymous_distinct' '[a,b]' '[1]' 'sread_reused' '"(a b)"' '"(pair a b)"' '[a,b]' '"(pair a b)"' 'a' > "$TMP/swi.expected"
diff -u "$TMP/swi.expected" "$TMP/swi.out"

swipl -q -f scripts/prolog/pinned_petta_registration_oracle.pl -- \
  "$TMP/src/metta.pl" "$TMP/src/translator.pl" "$TMP/src/specializer.pl" \
  "$TMP/src/parser.pl" "$TMP/src/filereader.pl" "$TMP/src/spaces.pl" \
  "$ROOT_DIR/scripts/prolog/pinned_file_runtime_fixture.metta" \
  "$TMP/examples/identity.metta" \
  > "$TMP/swi-registration.out"
printf '%s\n' 'metta_silent_setup=exact' \
  'metta_load_file=exact' 'metta_loaded_file_definition=exact' \
  'metta_identity_diagnostic_gap_swi_true=exact' \
  'metta_identity_definition_swi=exact' \
  'metta_fun_id_registered=exact' 'metta_id_direct=exact' \
  'metta_term_variables_direct=exact' \
  'metta_numbervars_direct=exact' \
  'metta_normalize_specialization_key=exact' \
  'metta_term_hash_normalized_key=exact' \
  'metta_functor_decompose_direct=exact' \
  'metta_functor_construct_direct=exact' \
  'metta_nb_global_direct=exact' \
  'metta_eval_compound=exact' \
  'metta_eval_nested_arithmetic=exact' \
  'metta_eval_imported_reverse=exact' \
  'metta_eval_if=exact' \
  'metta_eval_map_atom=exact' \
  'metta_eval_foldl_atom=exact' \
  'metta_eval_first_pair=exact' \
  'metta_eval_size=exact' \
  'metta_eval_unique=exact' \
  'metta_process_string=exact' \
  'metta_fresh_id_persisted=exact' \
  'metta_alpha_unique_direct=exact' \
  'metta_eval_alpha_unique=exact' \
  'metta_eval_superpose_order=exact' \
  'metta_eval_collapse=exact' \
  'metta_eval_once=exact' \
  'metta_eval_if_false=exact' \
  'metta_eval_empty=exact' \
  'metta_eval_transaction=exact' \
  'metta_eval_copy_term=exact' \
  > "$TMP/swi-registration.expected"
diff -u "$TMP/swi-registration.expected" "$TMP/swi-registration.out"

echo "Pinned PeTTa source runtime: PASS (actual .metta file, parser wrappers, atomic/compound eval, and source registration exact; diagnostic-builtin gap pinned separately)"
