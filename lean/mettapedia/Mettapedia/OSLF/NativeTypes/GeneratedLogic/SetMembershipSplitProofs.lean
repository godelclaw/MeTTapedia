import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipProofTerms

/-!
# Splits through the certificate compiler, in two profiles

The certificate compiler takes splits as it takes the other formers. A split of a set is a pair of sets whose union
it is, so its parts are subsets; the compiler works on regions closed under parts, and the decision goes through the
coverings of a term's members.

- **Proving a split**: the parts are separated from the set by the members of a covering the decision chooses
  (`partTerm`, `partsSplit`, `partDescribed`), and their types are proved there. The parts are described only forward
  and existentially (`describesSome`), which is how the compiler describes all its subjects.
- **Refuting an every-split**: the same parts, as witnesses that some split has neither part with its type.
- **Refuting a split**: for an arbitrary split, a case analysis on which members land in each part (`coverBranches`):
  its goal is falsity, so from `P → ⊥` and `(P → ⊥) → ⊥` it gets falsity, and no excluded middle is assumed.
- **Proving an every-split**: the same case analysis, with a disjunctive goal, so by excluded middle
  (`Laws.excludedMiddle`); or, when both parts have upward shapes, by the union's own case analysis, with no excluded
  middle.

The compiler is uniform in polarity: proving a type proves its parts, and refuting it refutes them. So:

- **Refutations need only the three laws**, for every regional native type, every-splits included
  (`sentenceRefutation`, `refutation_proofTerm_regional`).
- **Proofs need excluded middle only for every-splits whose parts are not upward**: the core profile proves every
  regional native type whose every-splits have upward parts from the three laws (`sentenceProof`); the classical
  profile proves all of them from the three laws and excluded middle, as the implication from it
  (`sentenceProofClassical`, `compileVerdictClassical`).
- **The certified set front door** (`askSets`) decides a regional native type on the parts region and returns the
  closed package term its profile gives: proved, proved from excluded middle, or refuted (`askSets_refuted_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (Symbol)

section Package

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.MegalodonHOTG
open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseInterpretation (embed)

variable {L : Type} [LevelOrder L]

/-- **The classical verdict compiler into the package**: for a regional native type at a hereditary term, a closed
term of the implication from excluded middle to its proposition, or a closed term of its negation, which needs no
excluded middle. -/
def compileVerdictClassical {formula : Formula 0} (regional : formula.regional = true) {term : Pattern}
    (holds : IsHF term) :
    {proofTerm : CTm (Head L) 0 // CTyped (setLaws L) .nil proofTerm
        (cHolds (trTerm (embed (.imp middleLaw (nativeTypeSentence formula term)))))} ⊕
      {proofTerm : CTm (Head L) 0 //
        CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (negCore (nativeTypeSentence formula term)))))} :=
  match compileSentenceClassical regional holds with
  | .inl proof => .inl ⟨packageTerm proof, packageTerm_typed proof⟩
  | .inr proof => .inr ⟨packageTerm proof, packageTerm_typed proof⟩

/-- **Every regional native type that fails has a closed refutation term in the package**, from the three laws:
every-splits included, with no excluded middle. -/
theorem refutation_proofTerm_regional {formula : Formula 0} (regional : formula.regional = true) {term : Pattern}
    (holds : IsHF term) (fails : ¬ Membership.sat Env.closed formula term) :
    ∃ proofTerm : CTm (Head L) 0,
      CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (negCore (nativeTypeSentence formula term))))) :=
  ⟨packageTerm (sentenceRefutation regional holds fails), packageTerm_typed _⟩

/-- **Every regional native type that holds has a closed term of the implication from excluded middle to its
proposition** in the package. -/
theorem classical_proofTerm {formula : Formula 0} (regional : formula.regional = true) {term : Pattern}
    (holds : IsHF term) (holdsAt : Membership.sat Env.closed formula term) :
    ∃ proofTerm : CTm (Head L) 0,
      CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (.imp middleLaw (nativeTypeSentence formula term))))) :=
  ⟨packageTerm (sentenceProofClassical regional holds holdsAt), packageTerm_typed _⟩

/-! ### The certified set front door -/

/-- **A certified answer for the membership language**: proved from the three laws, proved from them and excluded
middle, or refuted from the three laws, each with its closed term in the package of set theory. -/
inductive SetVerdict (formula : Formula 0) (term : Pattern) where
  | proved (proofTerm : {proofTerm : CTm (Head L) 0 //
      CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (nativeTypeSentence formula term))))})
  | provedClassically (proofTerm : {proofTerm : CTm (Head L) 0 //
      CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (.imp middleLaw (nativeTypeSentence formula term)))))})
  | refuted (proofTerm : {proofTerm : CTm (Head L) 0 //
      CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (negCore (nativeTypeSentence formula term)))))})

/-- **Ask the set front door, and certify**: a regional native type of a hereditary term is decided on its parts
region; a proof uses excluded middle only when the type has every-splits, and a refutation never does. -/
def askSets {formula : Formula 0} (regional : formula.regional = true) {term : Pattern} (holds : IsHF term) :
    SetVerdict (L := L) formula term :=
  if accepted : decideRegional formula term = true then
    if core : formula.regionalWith false = true then
      .proved ⟨packageTerm (sentenceProof core holds ((decideRegional_iff regional holds).mp accepted)),
        packageTerm_typed _⟩
    else
      .provedClassically ⟨packageTerm (sentenceProofClassical regional holds
        ((decideRegional_iff regional holds).mp accepted)), packageTerm_typed _⟩
  else
    .refuted ⟨packageTerm (sentenceRefutation regional holds fun holdsAt => accepted
      ((decideRegional_iff regional holds).mpr holdsAt)), packageTerm_typed _⟩

/-- **The set front door answers on the right side**: it proves exactly the regional native types that hold. -/
theorem askSets_refuted_iff {formula : Formula 0} (regional : formula.regional = true) {term : Pattern}
    (holds : IsHF term) :
    (∃ proofTerm, askSets (L := L) regional holds = .refuted proofTerm) ↔ ¬ Membership.sat Env.closed formula term := by
  rw [← decideRegional_iff regional holds]
  unfold askSets
  split
  · rename_i accepted
    split <;> simp [accepted]
  · rename_i rejected
    simp [rejected]

end Package

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
