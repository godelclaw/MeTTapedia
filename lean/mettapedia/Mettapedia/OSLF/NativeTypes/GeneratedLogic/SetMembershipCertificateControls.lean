import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipProofTerms

/-!
# Controls: the certificate compiler runs

The compiler (`compileSentence`) is an ordinary program. These controls run it on front-door verdicts of the
membership language, and run the translation of its derivations into closed terms of the package (`compileVerdict`).
Each verdict lands on the side its decision gives, with a derivation of the reported size. The certified front door
(`askCertified`) attaches the closed package term to the front door's own proved and refuted answers.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.HOL (Term)
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (Symbol)
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Annotated (CTm)

/-- Every descent from `3` ends. -/
def descentsEnd : Formula 0 := .mu (.necessarily .any (.var 0))

/-- The set has the member. -/
def hasMember (member : Pattern) : Formula 0 := .possibly .any (.is member)

/-- Every member of a member is `0` or `1`. -/
def membersOfMembersSmall : Formula 0 := .necessarily .any (.necessarily .any (.or (.is zero) (.is one)))

/-- Some descent reaches the empty set: `μX. empty ∨ ◇X`. -/
def reachesEmpty : Formula 0 := .mu (.or (.empty .hashSet) (.possibly .any (.var 0)))

/-- There is an infinite descent: `νX. ◇X`. -/
def descendsForever : Formula 0 := .nu (.possibly .any (.var 0))

/-- The set has exactly one member, and it is `0`. -/
def onlyZero : Formula 0 := .single .hashSet (.is zero)

/-- If the set has exactly one member, that member is empty. -/
def singleEmpty : Formula 0 := .everySingle .hashSet (.empty .hashSet)

/-- At least `k` members. -/
def membersAtLeast (k : ℕ) : Formula 0 := .atLeast k .forward .any .top

/-- At least `k` empty members. -/
def emptyMembersAtLeast (k : ℕ) : Formula 0 := .atLeast k .forward .any (.empty .hashSet)

/-- Fewer than `k` members are empty. -/
def fewerEmptyThan (k : ℕ) : Formula 0 := .allButFewer k .forward .any (.nonEmpty .hashSet)

theorem one_holds : IsHF one := (hereditary_iff _).mp (by decide)

/-- `{0, 0}`: a presentation of `1` with a repeated member. -/
def oneTwice : Pattern := set [zero, zero]

theorem oneTwice_holds : IsHF oneTwice := (hereditary_iff _).mp (by decide)

/-- `{1}`. -/
def justOne : Pattern := set [one]

theorem justOne_holds : IsHF justOne := (hereditary_iff _).mp (by decide)

/-- The side and the size of a compiled certificate. -/
def report {φ : Term Symbol [] .prop} (certificate : Proof lawList φ ⊕ Proof lawList (negCore φ)) : String :=
  match certificate with
  | .inl proof => s!"proved in {proofSize proof} rules"
  | .inr proof => s!"refuted in {proofSize proof} rules"

/-- The number of nodes of a package term. -/
def termSize {Head : Type} : {n : ℕ} → CTm Head n → ℕ
  | _, .var _ | _, .const _ | _, .head _ => 1
  | _, .pi a b | _, .sigma a b | _, .lam a b | _, .app a b | _, .pair a b => termSize a + termSize b + 1
  | _, .id a b c => termSize a + termSize b + termSize c + 1
  | _, .fst a | _, .snd a | _, .refl a => termSize a + 1

/-! ## Positive verdicts -/

#guard (compileSentence (formula := descentsEnd) rfl three_holds).isLeft
#guard (compileSentence (formula := hasMember zero) rfl two_holds).isLeft
#guard (compileSentence (formula := membersOfMembersSmall) rfl three_holds).isLeft
#guard (compileSentence (formula := reachesEmpty) rfl three_holds).isLeft
#guard (compileSentence (formula := onlyZero) rfl one_holds).isLeft
#guard (compileSentence (formula := onlyZero) rfl oneTwice_holds).isLeft
#guard (compileSentence (formula := singleEmpty) rfl one_holds).isLeft
#guard (compileSentence (formula := singleEmpty) rfl three_holds).isLeft
#guard (compileSentence (formula := membersAtLeast 3) rfl three_holds).isLeft
#guard (compileSentence (formula := emptyMembersAtLeast 1) rfl three_holds).isLeft
#guard (compileSentence (formula := fewerEmptyThan 2) rfl three_holds).isLeft
#guard (compileSentence (formula := membersAtLeast 1) rfl oneTwice_holds).isLeft

/-! ## Negative verdicts -/

#guard (compileSentence (formula := hasMember three) rfl three_holds).isRight
#guard (compileSentence (formula := descendsForever) rfl three_holds).isRight
#guard (compileSentence (formula := hasMember two) rfl one_holds).isRight
#guard (compileSentence (formula := onlyZero) rfl two_holds).isRight
#guard (compileSentence (formula := onlyZero) rfl justOne_holds).isRight
#guard (compileSentence (formula := singleEmpty) rfl justOne_holds).isRight
#guard (compileSentence (formula := membersAtLeast 4) rfl three_holds).isRight
#guard (compileSentence (formula := emptyMembersAtLeast 2) rfl three_holds).isRight
#guard (compileSentence (formula := fewerEmptyThan 1) rfl three_holds).isRight
#guard (compileSentence (formula := membersAtLeast 2) rfl oneTwice_holds).isRight

/-! ## Sizes -/

/-- info: "proved in 4089 rules" -/
#guard_msgs in
#eval report (compileSentence (formula := descentsEnd) rfl three_holds)

/-- info: "proved in 1397 rules" -/
#guard_msgs in
#eval report (compileSentence (formula := hasMember zero) rfl two_holds)

/-- info: "refuted in 2634 rules" -/
#guard_msgs in
#eval report (compileSentence (formula := hasMember three) rfl three_holds)

/-- info: "refuted in 2663 rules" -/
#guard_msgs in
#eval report (compileSentence (formula := descendsForever) rfl three_holds)

/-- info: "proved in 6886 rules" -/
#guard_msgs in
#eval report (compileSentence (formula := membersAtLeast 3) rfl three_holds)

/-- info: "refuted in 1372 rules" -/
#guard_msgs in
#eval report (compileSentence (formula := membersAtLeast 2) rfl oneTwice_holds)

/-- info: "refuted in 20326 rules" -/
#guard_msgs in
#eval report (compileSentence (formula := membersAtLeast 4) rfl three_holds)

/-! ## Native types of set terms, and steps as membership proofs -/

#guard (compileAtSetTerm (formula := descentsEnd) rfl three_holds).isLeft
#guard (compileAtSetTerm (formula := hasMember three) rfl three_holds).isRight

/-- The size of the derivation that the set term of `2` is a member of the set term of `3`. -/
def stepSize : ℕ := proofSize (memberProof three_holds ⟨2, by decide⟩)

/-- info: 565 -/
#guard_msgs in
#eval stepSize

/-! ## Closed terms of the package -/

/-- The size of the closed package term of a verdict, and its side. -/
def verdictReport {formula : Formula 0} (regional : formula.regionalWith false = true) {term : Pattern}
    (holds : IsHF term) : String :=
  match compileVerdict (L := ℕ) regional holds with
  | .inl found => s!"proof term of {termSize found.1} nodes"
  | .inr found => s!"refutation term of {termSize found.1} nodes"

/-- info: "proof term of 85205 nodes" -/
#guard_msgs in
#eval verdictReport (formula := hasMember zero) rfl two_holds

/-! ## The certified front door -/

/-- The side of a certified verdict, and the size of its proof term. -/
def certifiedReport {formula : Formula 0} {term : Pattern} : CertifiedVerdict (L := ℕ) formula term → String
  | .proved _ found => s!"proved, term of {termSize found.1} nodes"
  | .refuted _ found => s!"refuted, term of {termSize found.1} nodes"
  | .unknown rounds => s!"open after {rounds} rounds"

/-- info: "proved, term of 85205 nodes" -/
#guard_msgs in
#eval certifiedReport (askCertified (formula := hasMember zero) rfl two_holds 4)

/-- info: "refuted, term of 213915 nodes" -/
#guard_msgs in
#eval certifiedReport (askCertified (formula := hasMember three) rfl three_holds 4)

/-- info: "open after 0 rounds" -/
#guard_msgs in
#eval certifiedReport (askCertified (formula := descentsEnd) rfl three_holds 0)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
