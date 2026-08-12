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

The corresponding source-execution gate combines the real pinned `metta.pl`,
`parser.pl`, `translator.pl`, and `specializer.pl` units with those three SWI
libraries plus the real `library(apply)` and `library(pairs)` sources using the static
module-aware linker.  The linker separates user `exp/2` from
`dcg_basics:exp/2`, resolves explicit imports and the unique loaded export
used by SWI autoload, and fails on ambiguous exports or a literal predicate
that would collide with generated qualification. Module-less units additionally
materialize one canonical forwarding clause per imported predicate so that
runtime-built calls and ground predicate reflection see the same `user`-module
visibility as statically written calls. The pinned `specializer.pl` dependency
is linked as source rather than relying on missing-predicate failure. The
resulting 832
canonical clauses execute `phrase(swrite_exp([]), Codes)`,
`phrase(swrite_exp([a]), Codes)`, `phrase(swrite_exp(-42), Codes)`, and
`phrase(sexpr(Term, [], _), Codes)` for `(a)`, `(a b)`, `(1)`, `(-2)`,
`(1.5)`, `(1e2)`, `("a")`, `((a))`, `(a-b)`, `(1_2_3)`, `(#foo)`, an
escaped string, `$x`, `$x $x`, and `$_ $_` through the same
canonical `Logic.Prolog.SourceRuntime`, with the linked source clauses and no
translated replacement.  It requires the exact SWI answers `[40,41]` and
`[40,97,41]`, and `[45,52,50]` for the writers and `[a]`, `[a,b]`, `[1]`,
`[-2]`, `[1.5]`, `[100.0]`, `["a"]`, and `[[a]]` for the original readers.
The additional checks pin atom token boundaries, escape decoding, named
variable reuse, and distinct anonymous occurrences.  Every run must leave a
clean final heap and trail.  Five further paths call the actual exported
`sread/2` and `swrite/2` wrappers on string and atom input, named-variable
reuse, lists, and compounds rather than invoking their internal DCGs directly.
Two final paths execute the actual pinned `metta.pl` wrappers `parse/2` and
`repr/2`; the SWI oracle reads those exact source clauses from the pinned file
without executing unrelated load-time effects.  A further path executes
`eval(a, Out)` through the actual `eval/2`, `translate_expr/3`, and
`call_goals/1` clauses, pinning the first PeTTa evaluator path on atomic data.
Finally, the gate executes the exact retained
`maplist(register_fun, ...)` source goal through SWI's real `apply:maplist/2`
clauses using the canonical persistent runtime.  The returned database must
make `fun(id)` visible to a fresh query, and the actual pinned `id/2` clause
must then produce `a`.  The next path runs `eval([id,a], Out)` through the
pinned translator, real `lists:list_to_set/2`, real `pairs_keys/2`, shared
finite standard-order sorting, finite `length/2`, call-time
`current_predicate/1`, and the registered `id/2` clause, producing exactly
`a`. Nine more evaluator paths cover nested arithmetic, imported `reverse/2`,
translated conditionals, recursive `map-atom` and `foldl-atom`, pair
projection, list size, stable uniqueness, and the actual `alpha-unique`
rewrite/evaluator answer stream.  A direct path through pinned
`alpha-unique-atom/2` then distinguishes repeated alpha-equivalent variable
terms from a structurally different term through the portable conditional arm
of SWI `library(assoc)`.  The closure
asserts that `library(assoc)` is no longer external, its qualified definitions
are present, and PeTTa's alpha-list predicates call the qualified
`empty_assoc/1`, `get_assoc/3`, and `put_assoc/4` definitions. An independent
SWI oracle reads the same pinned translator, specializer, and runtime clauses,
executes the same registration directive, and requires the exact singleton
result for all ten compound evaluations plus the direct alpha-variant result:

```bash
scripts/prolog/run_pinned_parser_source_runtime.sh \
  /path/to/PeTTa /path/to/swipl-devel
```

The same gate now explicitly links pinned `filereader.pl` and `spaces.pl` and
executes a two-form string defining `(= (fresh-id $x) (id $x))` and then
running `!(fresh-id a)`, producing the exact result `[a]`.  Because `fresh-id`
does not exist in the loaded program (an explicit pre-execution assertion in
the gate), this forces PeTTa's source compiler and persistent dynamic-clause
path before the subsequent runnable can succeed.
For this finite canary, the complete pinned `.metta` text-to-answer path runs
on the shared runtime: PeTTa's own string-to-codes conversion, DCG parser,
form classifier, translator, source-space predicates, persistent database,
and evaluator all run as their Prolog clauses.  The gate installs
`silent(true)` through the ordinary persistent `assertz/1` transition to model
a silent CLI invocation;
the retained `current_prolog_flag(argv, ...)` loader goal is not claimed.

The gate also executes pinned `load_metta_file/3` on a physical `.metta`
fixture.  The host installs that file's already-read text through an explicit
read-only capability; pinned `filereader.pl`, the DCG parser, translator,
space operations, and dynamic database perform every language-level step.
The same file is passed to SWI and must produce the exact `[a]` result and a
persistently callable `file-id/2` definition.  The capability is disabled in
ordinary source services, accepts only the `read_file_to_string(Path,Text,[])`
fragment, and cannot construct goals, clauses, continuations, or answers.
`library(pcre)` remains an external obligation.  A separate expected-
divergence canary pins `identity.metta`: SWI obtains `[true]`, while the Lean
runtime currently obtains `[]` because PeTTa's diagnostic `test/3` depends on
observable `format/2`, whose output-effect transition is not implemented yet.
Variant equality `=@=/2`, previously the first failing goal in `test/3`, is
now covered by the shared read-only graph relation and exact SWI differential.
The test deliberately does not replace the remaining effect with silent
success.
The world returned by `process_metta_string/2` is then reused as a persistent
database, and a fresh query executes `fresh-id(a, Out)` again with exact
`Out = a` and empty query-local heap/trail cleanup.  This distinguishes an
answer produced only inside the defining call from a clause that was actually
installed for later calls.

This is a deliberately narrow executable slice.  Loader goals other than the
named registration directive remain explicit closure obligations; linked
clauses retain their original units as provenance while the qualified
executable projection clears context-dependent source-term reflection.
General meta-predicate argument qualification, reexports, runtime module
creation, and full source-order loader scheduling remain unsupported.
`length/2` currently covers finite proper-list inputs, and
`current_predicate/1` covers fully instantiated indicators against the exact
call-time visible program; their generative modes fail closed as explicit
runtime errors rather than false Prolog failure.  No PeTTa-specific
replacement is substituted.  Passing this gate therefore does not claim that
the entire PeTTa source closure is yet executable.  Numeric reading covers the
decimal and scientific forms
produced by pinned `dcg/basics:number//1`; integer writing is exact, while
float-to-code rendering remains explicitly unsupported.

The finite standard-order implementation has its own exact SWI 10.1.9
differential over mixed integers/floats, strings, atoms, duplicate retention,
pair-key stability, positional keys, and descending unique order:

```bash
scripts/prolog/run_source_term_order_differential.sh
```

### Single-sided rule differential

Committed `Head => Body` and guarded `Head, Guard => Body` rules execute on
the shared clause cursor and graph unifier.  The engine accepts a head match
only when the match's new trail suffix contains no write into the caller's
pre-materialization heap prefix.  It then runs the guard normally and reaches
the existing cut transition only after guard success.

```bash
scripts/prolog/run_single_sided_rule_differential.sh
```

The six exact SWI 10.1.9 traces distinguish rejection of caller-binding,
specific ground selection, guard fall-through, guard commitment, legal fresh
clause-variable bindings, and unchanged ordinary-head unification.  The
pinned-assoc source gate additionally requires the portable conditional arm
to contain exactly 18 typed SSU rules and no private `$btree_find_node/5`
call:

```bash
scripts/prolog/run_pinned_assoc_conditional.sh /path/to/swipl-devel
```

This tranche does not yet model SWI's catchable
`existence_error(matching_rule, Goal)` when an SSU predicate has no matching
rule or its permission error for mixing `=>` and `:-` in one predicate.  The
separate deterministic `?=>` rule neck is rejected explicitly rather than
silently compiled as an ordinary predicate.
Pinned `library(assoc)` covers the constructors of its intended `t`/`t(...)`
tree representation, so normal portable-library calls do not require the
unmatched-rule path.  Malformed tree inputs may reach that path and therefore
remain outside the current parity claim.

The portable arm can now execute lookup, traversal, enumeration, extrema,
functional update, and insertion through those SSU rules and the canonical
shared-runtime `compare/3` action.  The gate loads the pinned source into Lean
and compares 15 exact ordered traces with the pinned SWI library.  It covers
`get_assoc/3`, `get_assoc/5`, `assoc_to_keys/2`, `assoc_to_values/2`,
`gen_assoc/3`, `min_assoc/3`, `max_assoc/3`, and `put_assoc/4`, exercising
selection, recursion, backtracking, and term comparison together rather than
as compatible isolated fixtures:

```bash
scripts/prolog/run_pinned_assoc_runtime.sh /path/to/swipl-devel
```

### Shared-runtime control differential

The canonical runtime's structured-choice path has a separate observable gate:

```bash
scripts/prolog/run_runtime_control_differential.sh
```

It compares 262 exact answer, exception, and persistent-store traces against
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
Seven `compare/3` cases expose the existing standard-term-order traversal
through the shared runtime: atom order, structural equality, compound arity,
output-unification failure, and SWI's distinct invalid-order-atom versus
non-atom error classes.  The language decoder returns only an error or
`Ordering`; the engine owns result-atom allocation and graph unification.
Exact ISO exception-packet construction for invalid result values remains
outside this differential claim.
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
variable sharing/separation.  Seven non-backtrackable-global cases cover copied
set values, sharing across repeated gets, ordinary binding rollback, set and
delete persistence across older choice points, absent-name deletion, and the
exact catchable `error(existence_error(variable, Name),
context(system:nb_getval/2,_))` shape for a missing get.  Dynamic-database
cases cover persistent
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
