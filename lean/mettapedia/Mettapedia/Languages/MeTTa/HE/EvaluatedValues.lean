import Mettapedia.Languages.MeTTa.HE.EvaluatedValues.Term
import Mettapedia.Languages.MeTTa.HE.EvaluatedValues.Demand
import Mettapedia.Languages.MeTTa.HE.EvaluatedValues.Calculus
import Mettapedia.Languages.MeTTa.HE.EvaluatedValues.Laws
import Mettapedia.Languages.MeTTa.HE.EvaluatedValues.Contexts
import Mettapedia.Languages.MeTTa.HE.EvaluatedValues.Simulation
import Mettapedia.Languages.MeTTa.HE.EvaluatedValues.Conservativity
import Mettapedia.Languages.MeTTa.HE.EvaluatedValues.CoherenceCheck
import Mettapedia.Languages.MeTTa.HE.EvaluatedValues.CodeFree
import Mettapedia.Languages.MeTTa.HE.EvaluatedValues.Probes
import Mettapedia.Languages.MeTTa.HE.EvaluatedValues.Bridge

/-!
# Evaluated values: the call-return rule of Hyperon Experimental

## The rule

When a MeTTa call returns a value through an ordinary (`%Undefined%`-typed)
return, HE evaluates the returned atom again, because the returned atom may be
code that still has to run (a right-hand side such as `(wrap $x)` after
substitution). The question is what happens when the returned atom is already
the result of an evaluation. One definition covers three rules, which differ
only in which answers are marked and whether the mark is read
(`ReturnRule`):

* **Re-evaluation** (`reevaluate`): the mark is not read; every returned
  expression is evaluated again. This was the rule of the Lean specification
  of HE.
* **Rust HE** (`rustEqualToInput`): an evaluation marks the answers equal, up
  to marks, to the term it evaluated, and a marked expression is returned as
  itself.
* **Evaluated values** (`evaluatedValues`, the repair): in addition, a call
  that is stuck after its arguments were evaluated (no equation applies, or
  one replies `NotReducible`) is marked: the value is the call over its
  arguments' values.

Under every rule the mark is per node: substitution keeps the marks of
inserted values and unmarks every node whose subtree changed, so in
`(pair $x (fr a))` the inserted `$x` is a value while the written `(fr a)` is
code. Syntax returned through an `Atom` result, a `car-atom` child and a
`collapse` tuple stay code: macros keep working. Observation forgets the
marks.

In call-by-push-value terms: a returned atom is either a value (already
produced; returning it is `return v`) or a computation (code to be run).
Re-evaluation forgets that distinction at the return boundary and runs values
as if they were code; Rust's rule keeps it except for stuck calls whose
arguments were reduced.

## Why the old and the Rust rules are incoherent

A stuck call such as `(fr a)` with two refusing equations has two results,
both `(fr a)`. Under re-evaluation each return of such a value chooses again:
`(g (fr a))` with `g` an alias of `wrap` has 4 results, `(g1 (fr a))` with `g1`
an alias of `g` has 8, `(twice (fr a))` has 8, and
`(let $c (collapse (fr a)) (superpose $c))` has 4. Rust's rule fixes these but
not `(fr (h))` with `(= (h) a)`: the stuck `(fr a)` is not the evaluated term,
so `(g (fr (h)))` has 4 results while `(wrap (fr (h)))` has 2, and collapsing
and re-superposing `(fr (h))` doubles it. The repaired rule gives 2 in every
case (`Probes`).

## What is proved

* `eval_codeFree`, `eval_kleisli_idempotent_codeFree` — under
  `evaluatedValues`, every result of a code-free term (no `collapse`,
  `car-atom` or `Atom`-result head among its symbols, in a program whose
  right-hand sides are code-free) is a code-free value, and evaluation is a
  projection on such terms. `ValueResults.call_stuck` — an untyped call
  returns values whenever its replies do. `ga_result_is_code` — an `Atom`
  result is code by design. `reevaluate_not_idempotent` — the old rule fails
  projection on `(fr a)`.
* `eval_call_untyped`, `eval_twice` — applicative compositionality (every
  rule) and call-time choice (rules that read the mark) on arguments with
  value results.
* `eval_alias_codeFree`, `eval_plugAll_codeFree`,
  `unfold_preserves_eval_codeFree` — under `evaluatedValues`, aliases,
  evaluation contexts and linear unfolding of one-parameter definitions, with
  no hypothesis beyond code-freeness. `eval_alias`, `eval_plugAll`,
  `unfold_preserves_eval` — the versions that hold for Rust's rule too, under
  value-result and self-reproduction hypotheses.
* `eval_superpose_collapse`, `eval_unique`, `unique_nodup`, `unique_support` —
  on arguments with value results (all code-free terms under the repaired
  rule), `collapse` then `superpose` is the identity and `unique` keeps one
  result per erasure.
* `rust_violates_alias`, `rust_violates_superpose_collapse`, `fr_h_values` —
  Rust's rule breaks both laws on `(fr (h))`; the repaired rule keeps them.
* `conservativity` — wherever the old rule's evaluation is coherent (every
  value it passes through a return comes back unchanged and once when
  evaluated again), every rule makes the observations of the old rule. The
  repair is conservative: it changes only the incoherent cases.
  `coherentAt_of_check` makes coherence checkable by computation.
* `bridge_*` — the core calculus under the old rule returns exactly the
  answers of the executable evaluator `HE.eval` on the equation-only probes.

## Context

Call-time choice (CRWL; González-Moreno, Hortalá-González, López-Fraguas,
Rodríguez-Artalejo, J. Logic Programming 1999; the languages Curry and Toy)
shares a parameter's choice among its occurrences; run-time choice (term
rewriting; Hussmann, J. Logic Programming 1992) chooses again at each
occurrence. HE has call-time choice for value parameters and run-time choice
for `Atom` parameters (`twicem_coin_obs`). The old return rule was
neither on stuck results. Sharing a computed value rather than re-running it
is the discipline of Fischer, Kiselyov and Shan, *Purely functional lazy
non-deterministic programming* (ICFP 2009).
-/
