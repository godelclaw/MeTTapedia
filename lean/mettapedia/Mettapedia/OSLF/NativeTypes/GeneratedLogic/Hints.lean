import Mettapedia.OSLF.NativeTypes.GeneratedLogic.BackwardReach
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search

/-!
# Hints found by search

The front door checks every certificate it is given, so where a hint comes from does not bear on soundness. This module
derives what a hint search needs from the language and the formula alone:

- `signatureOf`: the slots a model of the language interprets: each constructor with its number of arguments,
  abstraction over one variable when some constructor binds one, abstraction over several for each number some
  constructor binds, and the unit and join of each collection kind its sorts use.
- `certificateGoals?`: the goals a formula is about, when it says that a run reaches them (`reachFormula`) or that no
  run does (its dual). A certificate separating the term from the goals refutes the first and proves the second.
- `findHint`: the finder's cells over carriers of increasing size, up to a bound, separating the term from the goals
  under the contextual semantics, as a candidate for `ask`.
- `askFound`: `ask` with the language's signature and the finder's hint. It is `ask`, so its answers are sound by
  `ask_proved` and `ask_refuted` (`askFound_proved`, `askFound_refuted`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.FiniteModels (Signature Slot findCells)

/-- The collection kinds of a sort. -/
def collectionKinds : TypeExpr → List CollType
  | .base _ => []
  | .arrow domain codomain => collectionKinds domain ++ collectionKinds codomain
  | .multiBinder inner => collectionKinds inner
  | .collection kind element => kind :: collectionKinds element

/-- The sort of a constructor's argument. -/
def paramSort : TermParam → TypeExpr
  | .simple _ sort => sort
  | .abstractionNamed _ _ sort => sort
  | .multiAbstractionNamed _ _ sort => sort

/-- **The signature of a language**: its constructors with their numbers of arguments, then abstraction over one
variable, over several, and the units and joins of its collection kinds, each when the language uses it. -/
def signatureOf (language : LanguageDef) : Signature :=
  let params := language.terms.flatMap (·.params)
  let operations := language.terms.map fun rule => Slot.operation rule.label rule.params.length
  let abstraction := if params.any (fun param => match param with | .abstractionNamed .. => true | _ => false)
    then [Slot.abstraction] else []
  let several := (params.filterMap fun param => match param with
    | .multiAbstractionNamed binders _ _ => some (Slot.multiAbstraction binders.length)
    | _ => none).eraseDups
  let kinds := (params.flatMap fun param => collectionKinds (paramSort param)).eraseDups
  operations ++ abstraction ++ several ++ kinds.flatMap fun kind => [.collectionUnit kind, .collectionJoin kind]

/-- **The goals of a formula**: those it says a run reaches, or that no run reaches. -/
def certificateGoals? (formula : Formula 0) : Option (List Pattern) :=
  (reachGoals? formula).orElse fun _ => reachGoals? formula.dual

/-- The finder's cells over `Fin (size + 1)`, trying each junk value. -/
def findAt (signature : Signature) (language : LanguageDef) (goals : List Pattern) (term : Pattern) (size : ℕ) :
    Option CertificateCandidate :=
  (List.finRange (size + 1)).findSome? fun junk =>
    (findCells (List.finRange (size + 1)) junk signature language [] goals term .contextual).map
      fun cells => ⟨size, junk, cells⟩

/-- **A hint by search**: for a formula about goals, the finder's cells separating the term from them, over carriers
of two values up to `bound + 1`. -/
def findHint (signature : Signature) (language : LanguageDef) (formula : Formula 0) (term : Pattern) (bound : ℕ) :
    Option CertificateCandidate := do
  let goals ← certificateGoals? formula
  (List.range bound).findSome? fun size => findAt signature language goals term (size + 1)

/-- **Ask with a hint by search**: the signature from the language, and the finder's cells, over carriers up to
`bound + 1` values, as the hint. -/
def askFound (relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv) (language : LanguageDef) (fuel : ℕ)
    (formula : Formula 0) (term : Pattern) (bound rounds : ℕ)
    (forms : Option (CanonicalForms relEnv language fuel) := none) : Answer :=
  ask relEnv (signatureOf language) language fuel formula term
    (findHint (signatureOf language) language formula term bound) rounds forms

section Soundness

variable {relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv} {language : LanguageDef} {fuel : ℕ}
  {formula : Formula 0} {term : Pattern} {bound rounds : ℕ} {forms : Option (CanonicalForms relEnv language fuel)}
  {evidence : Evidence}

theorem askFound_proved (answered : askFound relEnv language fuel formula term bound rounds forms = .proved evidence) :
    (referenceStructure relEnv language (formsReading forms)).sat Env.closed formula term :=
  ask_proved answered

theorem askFound_refuted (answered : askFound relEnv language fuel formula term bound rounds forms = .refuted evidence) :
    ¬ (referenceStructure relEnv language (formsReading forms)).sat Env.closed formula term :=
  ask_refuted answered

end Soundness

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
