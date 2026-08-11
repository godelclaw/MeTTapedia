import Mettapedia.Logic.Prolog.Syntax
import Mettapedia.Logic.Prolog.SourceSignature
import Mettapedia.Logic.Prolog.SourceSignatureRegression
import Mettapedia.Logic.Prolog.ReaderLexer
import Mettapedia.Logic.Prolog.ReaderLexerRegression
import Mettapedia.Logic.Prolog.ReaderNumber
import Mettapedia.Logic.Prolog.ReaderNumberRegression
import Mettapedia.Logic.Prolog.ReaderOperator
import Mettapedia.Logic.Prolog.ReaderOperatorRegression
import Mettapedia.Logic.Prolog.ReaderTerm
import Mettapedia.Logic.Prolog.ReaderTermRegression
import Mettapedia.Logic.Prolog.ReaderSource
import Mettapedia.Logic.Prolog.ReaderSourceRegression
import Mettapedia.Logic.Prolog.RuntimeControl
import Mettapedia.Logic.Prolog.RuntimeControlRegression
import Mettapedia.Logic.Prolog.PureRuntimeSoundness
import Mettapedia.Logic.Prolog.PureRuntimeRegression
import Mettapedia.Logic.Prolog.Core
import Mettapedia.Logic.Prolog.Eval
import Mettapedia.Logic.Prolog.RuntimeErrorSpec
import Mettapedia.Logic.Prolog.FixtureCorpus

/-!
# Prolog Syntax and Characterization Barrel

Barrel import for the canonical LP-based Prolog syntax and the older
pattern-level ISO characterization corpus.

`Syntax.lean` formalizes **Prolog = LP + control** without changing the LP
representation: `Goal.call` contains `Logic.LP.Atom`, all data arguments are
`Logic.LP.Term`, and definite LP programs embed and project back exactly.

`Core.lean`, `Eval.lean`, and `FixtureCorpus.lean` contain a separate
`MeTTaIL.Pattern`-level characterization used to record ISO/Logtalk examples.
That relation is evidence and a requirements source; it is not the executable
resolver and is not the semantic foundation of `Logic.LP.RuntimeQuery`.

## Architecture

```
Mettapedia.Logic.LP                    pure syntax, SLD, runtime, least model
  ↑ reused definitionally by
Mettapedia.Logic.Prolog.Goal/Clause    Prolog control syntax

Mettapedia.Logic.Prolog.PrologGoal     pattern-level ISO characterization
  (separate evidence; not an executable-engine dependency)
```

## File Index

| File | Contents |
|------|----------|
| `Syntax` | canonical `Goal` and `Clause` over `Logic.LP`, exact pure-Horn embedding |
| `SourceSignature` | name/arity-indexed concrete source symbols and exact atomic payloads |
| `ReaderLexer` | SWI-shaped located tokens for the concrete source reader |
| `ReaderNumber` | exact integer, character-code, and IEEE float token interpretation |
| `ReaderOperator` | checked ISO/SWI operator declarations and dynamic updates |
| `ReaderTerm` | operator-aware parsing directly into canonical `Logic.LP.Term` |
| `ReaderSource` | direct clause/directive/DCG classification on canonical terms |
| `RuntimeControl` | typed control materialization into the canonical LP heap and variable map |
| `RuntimeControlRegression` | sharing and typed-control executable materialization gates |
| `PureRuntime` | demand-driven pure-Prolog entrypoint delegating to the canonical LP runtime |
| `PureRuntimeSoundness` | transport of runtime answers to standardized-apart SLD and the least Herbrand model |
| `PureRuntimeRegression` | ordered-answer and control-rejection executable gates |
| `Core` | pattern-level `PrologGoal`, `PEnv`, and fixture helpers |
| `Eval` | `EvalOracle`, `PrologSpace`, `PrologEvalResult` (normal/cutThrown), `PrologEval` (inductive), `PrologConjAll` (derived Prop) |
| `RuntimeErrorSpec` | theorem-level ISO runtime-error boundary map (`instantiation_error`, `type_error(callable, ...)`) |
| `FixtureCorpus` | ISO/Logtalk-sourced fixture theorems (positive + negative constructor-level regressions) |

## Key Design Decisions

- **Canonical calls**: executable predicate calls contain `Logic.LP.Atom`
  directly; the Prolog layer does not own another term or clause language.
- **Pairs-witness pattern** for the characterization relation's conjunction/spaceMatch: avoids `mutual inductive` while
  still expressing "run g on each element of a list" inside the `PrologEval` inductive.
- **`EvalOracle`** abstracts `reduceCall` inside the pattern-level
  characterization. It is not an authority used by the canonical runtime.
- **Cut semantics**: `cutThrown` is caught by `disj`, `findall`, and `once`; in conjunction,
  g2 runs left-to-right over g1 answers; if a cut is thrown in either g1/g2,
  current-branch answers are kept and suffix branches are pruned.
- **`PrologConjAll`** is a derived `Prop` (not an inductive type), using the pairs witness.

## References

- Lloyd, *Foundations of Logic Programming*, 2nd ed. (1987)
- Sterling & Shapiro, *The Art of Prolog*, 2nd ed. (1994)
- PeTTa `translator.pl`: `translate_expr/3`, `call_goals/1`, `reduce/2`
-/
