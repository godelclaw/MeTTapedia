# Prolog Conformance Suite

This harness validates that the Lean formalization of Prolog semantics
([Mettapedia/Logic/Prolog](../../Mettapedia/Logic/Prolog)) agrees with
real Prolog implementations.  It cross-checks 242 Lean-proven fixture
theorems against SWI-Prolog execution and verifies coverage of 63 ISO
test IDs from the Logtalk conformance suite.

## How it works

The suite has three tiers:

1. **Lean-aligned parity.**
   `swi_fixture_cases.pl` defines 183 test goals.  `swi_fixture_runner.pl`
   executes them in SWI-Prolog and writes JSONL results.
   `check_lean_swi_parity.py` then verifies that every case has both a
   matching theorem in `FixtureCorpus.lean` and a passing SWI execution.

2. **Runtime-error boundary probes.**
   Four ISO cases (`\+ 3`, `\+ G`, `findall(_, G, _)`, `findall(_, 4, _)`)
   require runtime error detection that falls outside the typed `PrologGoal`
   AST.  These are formalized as theorem-level boundary declarations in
   `RuntimeErrorSpec.lean` and validated by `check_iso_probe_error_cases.py`.

3. **Logtalk ISO-ID coverage.**
   `report_logtalk_iso_coverage.py` extracts all `iso_*` identifiers from
   9 upstream Logtalk test files and checks that every ID is covered by both
   a Lean theorem and a `lean_aligned` case.
   Hard threshold: 63/63 for both.

## Current counts

| Metric | Count |
|--------|------:|
| Lean fixture theorems | 242 |
| SWI `lean_aligned` cases | 183 |
| SWI `iso_probe` cases | 11 |
| Unique ISO IDs covered | 63 |
| Runtime-error boundary probes | 4 |

## Upstream ISO Source Set (Exact Files)

- `tests/prolog/control/true_0/tests.lgt`
- `tests/prolog/control/fail_0/tests.lgt`
- `tests/prolog/control/conjunction_2/tests.lgt`
- `tests/prolog/control/disjunction_2/tests.lgt`
- `tests/prolog/predicates/once_1/tests.lgt`
- `tests/prolog/predicates/not_1/tests.lgt`
- `tests/prolog/predicates/unify_2/tests.lgt`
- `tests/prolog/predicates/not_unifiable_2/tests.lgt`
- `tests/prolog/predicates/findall_3/tests.lgt`

Upstream repository:
- <https://github.com/LogtalkDotOrg/logtalk3/tree/master/tests/prolog>

## Exact ISO IDs Used

Count: `63`

```text
iso_conjunction_2_01
iso_conjunction_2_02
iso_conjunction_2_03
iso_disjunction_2_01
iso_disjunction_2_02
iso_disjunction_2_03
iso_disjunction_2_04
iso_disjunction_2_05
iso_fail_0_01
iso_findall_3_01
iso_findall_3_02
iso_findall_3_03
iso_findall_3_04
iso_findall_3_05
iso_findall_3_06
iso_findall_3_07
iso_findall_3_08
iso_not_1_01
iso_not_1_02
iso_not_1_03
iso_not_1_04
iso_not_1_05
iso_not_1_06
iso_not_1_07
iso_not_1_08
iso_not_unifiable_2_01
iso_not_unifiable_2_02
iso_not_unifiable_2_03
iso_not_unifiable_2_04
iso_not_unifiable_2_05
iso_not_unifiable_2_06
iso_not_unifiable_2_07
iso_not_unifiable_2_08
iso_not_unifiable_2_09
iso_not_unifiable_2_10
iso_not_unifiable_2_11
iso_not_unifiable_2_12
iso_not_unifiable_2_13
iso_not_unifiable_2_14
iso_not_unifiable_2_15
iso_once_1_01
iso_once_1_02
iso_once_1_03
iso_once_1_04
iso_once_1_05
iso_true_0_01
iso_unify_2_01
iso_unify_2_02
iso_unify_2_03
iso_unify_2_04
iso_unify_2_05
iso_unify_2_06
iso_unify_2_07
iso_unify_2_08
iso_unify_2_09
iso_unify_2_10
iso_unify_2_11
iso_unify_2_12
iso_unify_2_13
iso_unify_2_14
iso_unify_2_15
iso_unify_2_16
iso_unify_2_17
```

## Commands

From repo root:

```bash
scripts/prolog/run_conformance.sh
```

With explicit Logtalk corpus path and hard coverage thresholds:

```bash
scripts/prolog/run_conformance.sh \
  artifacts/prolog/swi_fixture_results_latest.jsonl \
  ../_ext/prolog-tests/logtalk3/tests/prolog
```

Direct tools:

```bash
swipl -q -s scripts/prolog/swi_fixture_runner.pl -- artifacts/prolog/swi_fixture_results_latest.jsonl
python3 scripts/prolog/check_lean_swi_parity.py --results-file artifacts/prolog/swi_fixture_results_latest.jsonl
python3 scripts/prolog/check_iso_probe_error_cases.py --results-file artifacts/prolog/swi_fixture_results_latest.jsonl
python3 scripts/prolog/report_logtalk_iso_coverage.py --logtalk-root ../_ext/prolog-tests/logtalk3/tests/prolog --require-lean-theorem-exact 63 --require-lean-case-exact 63 --require-lean-theorem-normalized 63 --require-lean-case-normalized 63
```

### Canonical reader differential

The canonical `Logic.LP.Term` reader has a separate exact-shape differential:

```bash
scripts/prolog/run_pinned_reader_differential.sh /path/to/PeTTa
```

The gate extracts the seven source files from PeTTa commit
`6b7f52f064bdbc82fabd0a0998404121fb01d52e`, ignoring worktree changes. It
then compares all 317 terms recursively against SWI-Prolog 10.1.9: functor and
arity, ordered children, variable spelling and sharing, and atomic payloads.
The comparison fails on a version mismatch, a changed term count, malformed
JSON, or any structural difference.

The source-unit closure gate reads pinned PeTTa's `parser.pl` together with
SWI 10.1.9's real `library(dcg/basics)`, `library(lists)`, and `library(error)`
sources.  It checks 297 canonical clauses after DCG expansion and retains
`library(pairs)`, `library(debug)`, four declarations, and three load-time goals
as explicit obligations rather than silently dropping them:

```bash
scripts/prolog/run_pinned_parser_unit_closure.sh /path/to/PeTTa
```

The corresponding source-execution gate then runs the real pinned
`parser.pl` DCG clauses `phrase(swrite_exp([]), Codes)`,
`phrase(swrite_exp([a]), Codes)`, `phrase(swrite_exp(-42), Codes)`, and
`phrase(sexpr(Term, [], _), Codes)` for `(a)`, `(a b)`, `(1)`, `(-2)`,
`(1.5)`, `(1e2)`, `("a")`, `((a))`, `(a-b)`, `(1_2_3)`, `(#foo)`, an
escaped string, `$x`, `$x $x`, and `$_ $_` through the same
canonical `Logic.Prolog.SourceRuntime`, with those 297 linked clauses and no
translated replacement.  It requires the exact SWI answers `[40,41]` and
`[40,97,41]`, and `[45,52,50]` for the writers and `[a]`, `[a,b]`, `[1]`,
`[-2]`, `[1.5]`, `[100.0]`, `["a"]`, and `[[a]]` for the original readers.
The additional checks pin atom token boundaries, escape decoding, named
variable reuse, and distinct anonymous occurrences.  Every run must leave a
clean final heap and trail.  Five further paths call the actual exported
`sread/2` and `swrite/2` wrappers on string and atom input, named-variable
reuse, lists, and compounds rather than invoking their internal DCGs directly:

```bash
scripts/prolog/run_pinned_parser_source_runtime.sh /path/to/PeTTa
```

This is a deliberately narrow executable slice.  The retained external
imports, declarations, and load-time goals remain explicit closure
obligations; passing this gate does not claim that the entire parser source is
yet executable.  Numeric reading covers the decimal and scientific forms
produced by pinned `dcg/basics:number//1`; integer writing is exact, while
float-to-code rendering remains explicitly unsupported.

### Shared-runtime control differential

The canonical runtime's structured-choice path has a separate observable gate:

```bash
scripts/prolog/run_runtime_control_differential.sh
```

It compares 164 exact answer, exception, and persistent-store traces against
SWI-Prolog 10.1.9:
left-first disjunction, restoration before entering the right branch, cut
pruning the right branch, and a callee-local cut retaining its caller's older
disjunction choice; plus hard-if first-answer commitment, then-failure without
condition retry, false-condition else entry, condition-local cut scope, and
restoration of ordinary caller cut scope inside the then branch.  Lean-side
cleanup is additionally required to restore an empty heap and trail.  Five
soft-if cases distinguish it from hard-if: all condition answers remain live,
then failure retries the condition, false condition enters else, a cut in the
condition preserves the else delimiter, and a cut in then retains ordinary
caller scope.  Five `once/1` cases cover first-answer commitment, total
failure, cut opacity, caller-scope restoration after success, and binding
restoration before a caller alternative.  Four meta-call cases cover dynamic
heap decoding, local cut scope, argument extension, and heap-built callables.
Seven derived-control cases cover negation-as-failure and non-unifiability,
including trial-binding restoration and cut opacity; both reuse the canonical
hard-if checkpoint rather than adding a search path.
Five dynamic-call cases additionally pin `nonvar/1` and `forall/2` as
elaborations into those same derived forms, including universal failure and
binding isolation.
Fourteen shallow term-test cases cover `atom/1`, `atomic/1`, `compound/1`,
`number/1`, and `string/1` after canonical heap dereference, including a
heap-built meta-call and SWI's opaque database-reference distinction: a
clause reference is atomic but is not an atom.  The special empty-list
constant is likewise atomic but not an atom, matching SWI's term classes.
Five recursive `ground/1` cases additionally cover a nested finite term,
an unbound root, a nested free leaf, a closed rational cycle, and a rational
cycle with a free leaf.  The cycle cases ensure graph traversal terminates
without confusing revisitation with an unbound variable.
Five `is_list/1` cases cover a finite list, an improper tail, an unbound root,
a rationally cyclic spine, and a proper spine whose head is cyclic.  The last
case pins the SWI distinction between list-spine recognition and whole-term
acyclicity or groundness.
Six bidirectional text-code cases cover Unicode `atom_codes/2` and
`string_codes/2` in both directions, binding a variable list element, and a
ground mismatch that fails without binding.  Lean canaries additionally pin
typed rejection of both-unbound arguments, improper and cyclic code lists,
and invalid Unicode scalar values.
Eight `atom_chars/2` cases cover Unicode character-list production, reverse
conversion from character atoms, integer character codes, and a SWI string,
the bound-atom code-list and string modes, element binding, and ground
mismatch.  The real parser gate additionally
uses the integer-code input mode to preserve `$name` sharing and keep `$_`
occurrences distinct.
Five `atom_string/2` cases cover atom-to-string conversion, reverse conversion
from both SWI strings and atoms, ground mismatch, and heap-built meta-call.
The real parser gate uses this same decoder at the `sread/2` entry point; both
arguments unbound and non-text values remain typed errors in Lean canaries.
Eight `number_codes/2` cases cover exact integer rendering; positive and
negative integer reading; positive and negative decimal floats; exponent
syntax; ground mismatch; and heap-built meta-call.  Lean canaries additionally
pin typed errors for both-unbound arguments, invalid and improper code lists,
non-number values, and the intentionally unsupported float-rendering direction.
Six ground ASCII `code_type/2` cases cover spaces, decimal digits, rejection,
and a heap-built meta-call through the same read-only binary-test action.  The
source runtime intentionally fails closed on Unicode and the remaining SWI
character-class modes until their exact behavior is implemented.
Fourteen strict-identity cases compare `==/2` and `\==/2` through the shared
read-only heap traversal: same and distinct variables, structural compounds,
variable sharing, separately allocated rational cycles, non-binding failure,
heap-built meta-call, numeric type distinction, strings, and the atom versus
explicit zero-arity-compound distinction.
Eight `=../2` cases cover decomposition and construction of compounds, atoms,
and integers, preserve variable sharing in both directions, and execute a
heap-built meta-call through the same service.  Malformed lists, unbound or
non-atom functors, and explicit zero-arity compounds additionally fail through
typed engine errors in Lean canaries; exact ISO exception packets for those
cases remain outside this differential claim.
Nine integer-arithmetic cases cover exact `is/2` results for addition,
subtraction, multiplication, nested expressions, and both signs of `mod/2`;
result-unification failure; all six numeric comparisons; restoration into a
caller alternative; and heap-built meta-call.  Float, division, and
transcendental arithmetic remain explicitly unsupported.
Eleven `catch/3` and `throw/1` cases cover throw-time catcher selection,
entry-context recovery, rethrow, guarded and recovery cut opacity, retained
guarded answers, nested-catcher throw-time preservation, variable-copy
separation, sharing, non-collapse, and SWI's exact
`error(instantiation_error, context(system:throw/1,_))` behavior for a bare
variable ball.  Findall cases pin answer order and multiplicity, binding
isolation, empty collection, cut scope, exception transparency, and copied
variable sharing/separation.  Dynamic-database cases cover persistent
`asserta/1,2`/`assertz/1,2`, opaque stable-reference binding and round-trip,
call-snapshot isolation, and nondeterministic
`retract/1`: source-order retry, cut pruning, fact/rule distinction,
non-backtrackable erasure, snapshot isolation from later assertions, and
retry of a snapshotted occurrence erased by a nested operation.
The same frozen reflected-clause cursor also covers `clause/3`: source-order
enumeration, stable-reference filtering and round-trip, fact/rule body
reflection, cut pruning, isolation from later assertion, and retention of an
occurrence erased after the snapshot was opened.

## What a pass means

Passing all three tiers means the Lean `PrologEval` semantics agrees with
SWI-Prolog on every modelled case, and every ISO test ID in the selected
upstream set is represented.  This is strong evidence of semantic alignment
for the covered fragment.  It is not a full mechanized proof of SWI/ISO
runtime error semantics — runtime-error boundaries are tracked explicitly
in `RuntimeErrorSpec.lean` rather than modelled inside `PrologEval`.

## Related Lean modules

- [Prolog layer](../../Mettapedia/Logic/Prolog) — goal AST, evaluation, fixtures
- [LP kernel](../../Mettapedia/Logic/LP) — unification, SLD, Herbrand model
- [PeTTa layer](../../Mettapedia/Languages/MeTTa/PeTTa) — MeTTa evaluation pipeline
