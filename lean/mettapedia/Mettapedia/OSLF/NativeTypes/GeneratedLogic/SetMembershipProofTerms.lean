import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipProofs
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipSplits
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.MegalodonHOTG.SetProofs
import Mettapedia.Logic.HOL.ProofSyntaxModuloConservativity

/-!
# Front-door verdicts as closed proof terms of the package of set theory

For a native type `φ` of the regional fragment and a hereditary term `s` of the membership language:

- **If `s` has `φ`**, the checker's calculus proves the sentence of the native type (`sentenceProofIn`): the witness of
  the term, its description, and the proof of the native type at it (`proveNative`), on the term's parts region.
  - In the core profile, from the laws of the empty set, the power set and separation, for every type whose
    every-splits have upward parts (`sentenceProof`).
  - In the classical profile, from the three laws and excluded middle, for every regional type
    (`sentenceProofClassical`, the implication from excluded middle).
- **If `s` lacks `φ`**, it proves the negation from the three laws alone, every-splits included
  (`sentenceRefutation`): unpacking the set the sentence claims and refuting the native type there (`refuteNative`).
- **The certificate compilers** (`compileSentence`, `compileSentenceClassical`) are programs: they decide the native
  type on the term's parts region (`decideRegional`) and return the derivation of the sentence or of its negation,
  with every branch and witness chosen by the decision. They prove exactly the native types that hold
  (`compileSentence_isLeft_iff`, `compileSentenceClassical_isLeft_iff`).
- **In the package of set theory with its eleven laws** each derivation is a computed closed term of the type of the
  proofs of the proposition (`packageTerm`, `packageTerm_typed`): the proof is read with the constants of the
  package, and each of the three laws is discharged by its proof constant (`lawOccurrences`). The verdict compiler
  into the package (`compileVerdict`) returns the term of the proposition or of its negation.
- So a native type of the core profile holds at a hereditary term exactly when its proposition has a closed proof
  term in the package (`sat_iff_proofTerm`), relative to cofinally many inaccessible cardinals in two universes,
  which give the package its set model; and every such native type is decided there, by a computed proof of it or of
  its negation (`proofTerm_decides`).
- **The front door's verdicts** become proof terms (`verdict_proofTerms`): every descent from `3` ends and `0 ∈ 2`
  are proved, and `3 ∈ 3` is refuted, by closed terms of the package.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.HOL (Ty Ctx Var Term ClosedFormula weaken rename subst instantiate Subst Rename
  ProofSyntaxModulo DefiningEquation weakenHyps)
open Mettapedia.Logic.HOL.ImpredicativeConnectives (truth falsity conjunctionFormula disjunctionFormula
  existentialInline subst_conjunctionFormula subst_disjunctionFormula subst_existentialInline)
open Mettapedia.Logic.HOL.ImpredicativeConnectives.Modulo (truthIntro conjunctionIntro conjunctionLeft
  conjunctionRight disjunctionLeft disjunctionRight disjunctionElim existentialIntro existentialElim)
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (Symbol member separate)

/-! ## Proofs from three laws -/

/-- The laws of the empty set, the power set and separation, with their connectives written out. -/
def lawList : List (ClosedFormula Symbol) := [lawEmpty, lawPower, lawSeparation]

theorem atContext_nil (φ : ClosedFormula Symbol) : atContext [] φ = φ := by
  unfold atContext
  conv_rhs => rw [← Mettapedia.Logic.HOL.subst_id φ]
  apply Mettapedia.Logic.HOL.subst_ext
  intro _ index
  exact nomatch index

/-- The three laws, as the hypotheses. -/
def lawsOfList : HasLaws lawList where
  empty := Proof.cast (atContext_nil _).symm (.hyp ⟨0, by decide⟩)
  power := Proof.cast (atContext_nil _).symm (.hyp ⟨1, by decide⟩)
  separation := Proof.cast (atContext_nil _).symm (.hyp ⟨2, by decide⟩)

theorem isCore_witness {Γ : Ctx Unit} (term : Pattern) : (witness term : Term Symbol Γ setTy).isCore = true := by
  simp only [witness, separate, Mettapedia.Logic.HOL.Term.isCore, isCore_powerIter, isCore_describesOne (membersOf term)
    (y := (.var .vz : Term Symbol (setTy :: Γ) setTy)) rfl, Bool.and_self]

theorem instantiate_sentenceBody {formula : Formula 0} (regional : formula.regional = true) (term : Pattern)
    (t : Term Symbol [] setTy) :
    instantiate t (conjunctionFormula (describes term (.var .vz)) (nativeFormula formula (.var .vz) Fin.elim0)) =
      conjunctionFormula (describes term t) (nativeFormula formula t Fin.elim0) := by
  unfold instantiate
  rw [subst_conjunctionFormula, subst_describes, subst_nativeFormula_regional _ formula regional]
  congr 2
  funext index
  exact index.elim0

/-- **The sentence of a native type that holds, proved from a profile's laws**: the witness of the term, its
description, and the compiler's proof of the type at it, on the term's parts region. -/
def sentenceProofIn {classical : Bool} {Δ : List (Term Symbol [] .prop)} (laws : Laws classical Δ)
    {formula : Formula 0} (regional : formula.regionalWith classical = true) {term : Pattern}
    (holds : IsHF term) (holdsAt : Membership.sat Env.closed formula term) : Proof Δ (nativeTypeSentence formula term) :=
  existentialIntro (witness term) (Proof.cast (instantiate_sentenceBody (Formula.regional_of_regionalWith _ regional)
    term (witness term)).symm
    (conjunctionIntro (describedWitness laws.toHasLaws term holds)
      (proveNative (Region.withParts term holds) (withParts_partsClosed holds) classical formula regional laws Fin.elim0
        Env.closed Fin.elim0 (agrees_closed _) (fun index => index.elim0) term holds (self_mem_zfParts term)
        ((sat_iff_extensional (Formula.forward_of_regional formula (Formula.regional_of_regionalWith _ regional))
          holds).mp holdsAt) (witness term) (isCore_witness term)
        (describesSomeOfTerm laws.toHasLaws holds (describedWitness laws.toHasLaws term holds)))))

/-- **The negation of the sentence of a regional native type that fails, proved from the three laws**: refutations
need no excluded middle, every-splits included. -/
def sentenceRefutationIn {Δ : List (Term Symbol [] .prop)} (laws : HasLaws Δ) {formula : Formula 0}
    (regional : formula.regional = true) {term : Pattern} (holds : IsHF term)
    (fails : ¬ Membership.sat Env.closed formula term) : Proof Δ (negCore (nativeTypeSentence formula term)) :=
  .impI (existentialElim (Proof.newest _)
    (.impE (refuteNative (Region.withParts term holds) (withParts_partsClosed holds) formula regional
      (((laws.prepend _).lift setTy).prepend _) Fin.elim0 Env.closed Fin.elim0 (agrees_closed _)
      (fun index => index.elim0) term holds (self_mem_zfParts term)
      (fun holdsAt => fails ((sat_iff_extensional (Formula.forward_of_regional formula regional) holds).mpr holdsAt))
      (.var .vz) rfl (describesSomeOfTerm (((laws.prepend _).lift setTy).prepend _) holds
        (conjunctionLeft (Proof.newest _)))) (conjunctionRight (Proof.newest _))))

/-! ### The core profile: the three laws -/

/-- **The sentence of a native type that holds, proved from the three laws**, for the core profile's regional
fragment: every-splits only with upward parts. -/
def sentenceProof {formula : Formula 0} (regional : formula.regionalWith false = true) {term : Pattern}
    (holds : IsHF term) (holdsAt : Membership.sat Env.closed formula term) :
    Proof lawList (nativeTypeSentence formula term) :=
  sentenceProofIn lawsOfList.core regional holds holdsAt

/-- **The negation of the sentence of a regional native type that fails, proved from the three laws.** -/
def sentenceRefutation {formula : Formula 0} (regional : formula.regional = true) {term : Pattern}
    (holds : IsHF term) (fails : ¬ Membership.sat Env.closed formula term) :
    Proof lawList (negCore (nativeTypeSentence formula term)) :=
  sentenceRefutationIn lawsOfList regional holds fails

/-- **The certificate compiler**: the sentence of a native type of the core profile's regional fragment at a
hereditary term, proved or refuted from the three laws. The type is decided on the term's parts region
(`decideRegional`), and the decision chooses every branch and witness of the derivation. -/
def compileSentence {formula : Formula 0} (regional : formula.regionalWith false = true) {term : Pattern}
    (holds : IsHF term) :
    Proof lawList (nativeTypeSentence formula term) ⊕ Proof lawList (negCore (nativeTypeSentence formula term)) :=
  if accepted : decideRegional formula term = true then
    .inl (sentenceProof regional holds
      ((decideRegional_iff (Formula.regional_of_regionalWith _ regional) holds).mp accepted))
  else
    .inr (sentenceRefutation (Formula.regional_of_regionalWith _ regional) holds fun holdsAt => accepted
      ((decideRegional_iff (Formula.regional_of_regionalWith _ regional) holds).mpr holdsAt))

/-- **The compiler proves exactly the native types that hold.** -/
theorem compileSentence_isLeft_iff {formula : Formula 0} (regional : formula.regionalWith false = true)
    {term : Pattern} (holds : IsHF term) :
    (compileSentence regional holds).isLeft = true ↔ Membership.sat Env.closed formula term := by
  rw [← decideRegional_iff (Formula.regional_of_regionalWith _ regional) holds]
  unfold compileSentence
  split <;> simp_all

/-! ### The classical profile: excluded middle as a hypothesis -/

/-- The laws of the classical profile: the three laws, and excluded middle as a further hypothesis. -/
def classicalLaws : Laws true (atContext [] middleLaw :: lawList) where
  toHasLaws := lawsOfList.prepend _
  middle := fun _ => Proof.newest _

theorem atContext_middle : atContext [] middleLaw = middleLaw := atContext_nil middleLaw

/-- **The sentence of a regional native type that holds, proved from the three laws and excluded middle**: the
implication from excluded middle, so that the derivation names its classical assumption. -/
def sentenceProofClassical {formula : Formula 0} (regional : formula.regional = true) {term : Pattern}
    (holds : IsHF term) (holdsAt : Membership.sat Env.closed formula term) :
    Proof lawList (.imp middleLaw (nativeTypeSentence formula term)) :=
  Proof.cast (by rw [atContext_middle])
    (.impI (sentenceProofIn classicalLaws (Formula.regionalWith_true formula regional) holds holdsAt))

/-- **The classical certificate compiler**: for every regional native type, every-splits included, the sentence from
the three laws and excluded middle, or its negation from the three laws alone. -/
def compileSentenceClassical {formula : Formula 0} (regional : formula.regional = true) {term : Pattern}
    (holds : IsHF term) :
    Proof lawList (.imp middleLaw (nativeTypeSentence formula term)) ⊕
      Proof lawList (negCore (nativeTypeSentence formula term)) :=
  if accepted : decideRegional formula term = true then
    .inl (sentenceProofClassical regional holds ((decideRegional_iff regional holds).mp accepted))
  else
    .inr (sentenceRefutation regional holds fun holdsAt => accepted ((decideRegional_iff regional holds).mpr holdsAt))

theorem compileSentenceClassical_isLeft_iff {formula : Formula 0} (regional : formula.regional = true) {term : Pattern}
    (holds : IsHF term) :
    (compileSentenceClassical regional holds).isLeft = true ↔ Membership.sat Env.closed formula term := by
  rw [← decideRegional_iff regional holds]
  unfold compileSentenceClassical
  split <;> simp_all

/-! ## Hereditarily finite sets as set terms -/

/-- **The set term of a hereditary term**: its witness, the members of an iterated power set of the empty set that
its members describe. It is a closed term of the sets, and the term describes it (`describedWitness`). -/
abbrev setTerm (term : Pattern) : Term Symbol [] setTy := witness term

/-- **A step is a membership proof**: the set term of a member of a hereditary term is a member of the term's set
term, from the three laws. -/
def memberProof {term : Pattern} (holds : IsHF term) (index : Fin (membersOf term).length) :
    Proof lawList (member (setTerm ((membersOf term).get index)) (setTerm term)) :=
  describesBackward (describesAsSet holds (describedWitness lawsOfList term holds))
    (oneIntro (membersOf term) index (describedWitness lawsOfList _ (hf_members holds _ (List.get_mem _ _))))

/-- **A native type of the core profile's regional fragment, as a predicate of a hereditary term's set term**, proved
or refuted from the three laws by the certificate compiler. -/
def compileAtSetTerm {formula : Formula 0} (regional : formula.regionalWith false = true) {term : Pattern}
    (holds : IsHF term) :
    Proof lawList (nativeFormula formula (setTerm term) Fin.elim0) ⊕
      Proof lawList (negCore (nativeFormula formula (setTerm term) Fin.elim0)) :=
  if accepted : decideRegional formula term = true then
    .inl (proveNative (Region.withParts term holds) (withParts_partsClosed holds) false formula regional
      lawsOfList.core Fin.elim0 Env.closed Fin.elim0 (agrees_closed _) (fun index => index.elim0) term holds
      (self_mem_zfParts term)
      ((sat_iff_extensional (Formula.forward_of_regional formula (Formula.regional_of_regionalWith _ regional))
        holds).mp ((decideRegional_iff (Formula.regional_of_regionalWith _ regional) holds).mp accepted))
      (setTerm term) (isCore_witness term)
      (describesSomeOfTerm lawsOfList holds (describedWitness lawsOfList term holds)))
  else
    .inr (refuteNative (Region.withParts term holds) (withParts_partsClosed holds) formula
      (Formula.regional_of_regionalWith _ regional) lawsOfList Fin.elim0 Env.closed Fin.elim0 (agrees_closed _) (fun index => index.elim0) term holds
      (self_mem_zfParts term)
      (fun holdsAt => accepted ((decideRegional_iff (Formula.regional_of_regionalWith _ regional) holds).mpr
        ((sat_iff_extensional (Formula.forward_of_regional formula (Formula.regional_of_regionalWith _ regional))
          holds).mpr holdsAt)))
      (setTerm term) (isCore_witness term)
      (describesSomeOfTerm lawsOfList holds (describedWitness lawsOfList term holds)))

/-- The number of rules in a derivation of the checker. -/
def proofSize {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)} {φ : Term Symbol Γ .prop} : Proof Δ φ → ℕ
  | .hyp _ => 1
  | .impI body => proofSize body + 1
  | .impE function argument => proofSize function + proofSize argument + 1
  | .allI body => proofSize body + 1
  | .allE _ function => proofSize function + 1
  | .convert _ inner => proofSize inner + 1

/-! ## In the package of set theory -/

section Package

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.MegalodonHOTG
open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseInterpretation (embed coreDefinition universeTheory UniverseSymbol)
open ZFSetUniverseClosure (CofinalInaccessibles)

theorem coreDefinition_core : Mettapedia.Logic.HOL.ConstSubstCore (coreDefinition) := fun _ => rfl

theorem coreDefinition_interprets :
    Mettapedia.Logic.HOL.ConstSubstInterprets (coreDefinition) ([] : List (DefiningEquation Symbol))
      ([] : List (DefiningEquation UniverseSymbol)) :=
  fun _ member => absurd member List.not_mem_nil

/-- **The three laws among the package's eleven**, written out: the laws of the empty set, the power set and separation
are the second, fourth and fifth. -/
def lawOccurrences : Mettapedia.Logic.HOL.ProofSyntax.OccurrenceMap
    (lawList.map (Mettapedia.Logic.HOL.substConst coreDefinition))
    (universeTheory.map Mettapedia.Logic.HOL.ImpredicativeConnectives.expandInline) where
  index i := ⟨[1, 3, 4].getD i.1 0, by
    have small : i.1 < 3 := i.2
    interval_cases h : i.1 <;> decide⟩
  get_eq i := by
    have small : i.1 < 3 := i.2
    obtain ⟨k, within⟩ := i
    interval_cases k <;> rfl

variable {L : Type} [LevelOrder L]

/-- **The closed term of the package for a proof from the three laws**: the proof read with the constants of the
package, each law discharged by its proof constant. -/
def packageTerm {φ : ClosedFormula Symbol} (proof : Proof lawList φ) : CTm (Head L) 0 :=
  trProof equationOps constName ((ProofSyntaxModulo.substConst coreDefinition_core coreDefinition_interprets proof).mono
    lawOccurrences) idRen fun i => lawConstants (i.cast (List.length_map ..))

/-- **The closed term of a proof from the three laws has the type of the proofs of its conclusion** in the package
with the laws. -/
theorem packageTerm_typed {φ : ClosedFormula Symbol} (proof : Proof lawList φ) :
    CTyped (setLaws L) .nil (packageTerm proof) (cHolds (trTerm (embed φ))) :=
  expandedLawProof_typed (equationsHold_nil constName) _

/-- **The verdict compiler into the package**: for a native type of the core profile at a hereditary term, a closed term of the
type of the proofs of its proposition, or of its negation. -/
def compileVerdict {formula : Formula 0} (regional : formula.regionalWith false = true) {term : Pattern} (holds : IsHF term) :
    {proofTerm : CTm (Head L) 0 //
        CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (nativeTypeSentence formula term))))} ⊕
      {proofTerm : CTm (Head L) 0 //
        CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (negCore (nativeTypeSentence formula term)))))} :=
  match compileSentence regional holds with
  | .inl proof => .inl ⟨packageTerm proof, packageTerm_typed proof⟩
  | .inr proof => .inr ⟨packageTerm proof, packageTerm_typed proof⟩

/-- **A step as a closed term of the package**: the proof that a member's set term is a member of the term's set
term. -/
def stepTerm {term : Pattern} (holds : IsHF term) (index : Fin (membersOf term).length) :
    {proofTerm : CTm (Head L) 0 // CTyped (setLaws L) .nil proofTerm
      (cHolds (trTerm (embed (member (setTerm ((membersOf term).get index)) (setTerm term)))))} :=
  ⟨packageTerm (memberProof holds index), packageTerm_typed _⟩

/-- **The proposition of a native type that holds has a closed proof term in the package with the laws.** -/
theorem sentence_proofTerm {formula : Formula 0} (regional : formula.regionalWith false = true) {term : Pattern} (holds : IsHF term)
    (holdsAt : Membership.sat Env.closed formula term) :
    ∃ proofTerm : CTm (Head L) 0, CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (nativeTypeSentence formula term)))) :=
  ⟨packageTerm (sentenceProof regional holds holdsAt), packageTerm_typed _⟩

/-- **The negation of the proposition of a native type that fails has a closed proof term in the package with the
laws.** -/
theorem refutation_proofTerm {formula : Formula 0} (regional : formula.regionalWith false = true) {term : Pattern} (holds : IsHF term)
    (fails : ¬ Membership.sat Env.closed formula term) :
    ∃ proofTerm : CTm (Head L) 0,
      CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (negCore (nativeTypeSentence formula term))))) :=
  ⟨packageTerm (sentenceRefutation (Formula.regional_of_regionalWith _ regional) holds fails), packageTerm_typed _⟩

/-- **Every native type of the core profile at a hereditary term is decided in the package**: its proposition or the negation has
a closed proof term, which the compiler computes. -/
theorem proofTerm_decides {formula : Formula 0} (regional : formula.regionalWith false = true) {term : Pattern} (holds : IsHF term) :
    (∃ proofTerm : CTm (Head L) 0,
        CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (nativeTypeSentence formula term))))) ∨
      ∃ proofTerm : CTm (Head L) 0,
        CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (negCore (nativeTypeSentence formula term))))) :=
  match compileVerdict (L := L) regional holds with
  | .inl found => .inl ⟨found.1, found.2⟩
  | .inr found => .inr ⟨found.1, found.2⟩

/-! ### The certified front door -/

open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv) in
/-- **A front-door verdict with its proof term**: a proved verdict carries a closed term of the type of the proofs of
the proposition, a refuted one a term for its negation, and an open answer stays open. -/
inductive CertifiedVerdict (formula : Formula 0) (term : Pattern) where
  | proved (evidence : Evidence)
      (proofTerm : {proofTerm : CTm (Head L) 0 //
        CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (nativeTypeSentence formula term))))})
  | refuted (evidence : Evidence)
      (proofTerm : {proofTerm : CTm (Head L) 0 //
        CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (negCore (nativeTypeSentence formula term)))))})
  | unknown (rounds : ℕ)

open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv) in
/-- **Ask, and certify**: the front door's answer about a native type of the core profile of a hereditary term, with the closed
proof term of the package that the certificate compiler builds for its side. -/
def askCertified {formula : Formula 0} (regional : formula.regionalWith false = true) {term : Pattern} (holds : IsHF term)
    (rounds : ℕ) : CertifiedVerdict (L := L) formula term :=
  match answered : ask RelationEnv.empty [] membership 2 formula term none rounds (some membershipForms) with
  | .proved evidence =>
    .proved evidence ⟨packageTerm (sentenceProof regional holds (ask_proved answered)), packageTerm_typed _⟩
  | .refuted evidence =>
    .refuted evidence ⟨packageTerm (sentenceRefutation (Formula.regional_of_regionalWith _ regional) holds (ask_refuted answered)), packageTerm_typed _⟩
  | .unknown rounds => .unknown rounds

variable (small : CofinalInaccessibles.{0}) (large : CofinalInaccessibles.{1})

include small large in
/-- **A native type of the core profile holds at a hereditary term exactly when its proposition has a closed proof term in the
package with the laws**, relative to cofinally many inaccessible cardinals in two universes. -/
theorem sat_iff_proofTerm {formula : Formula 0} (regional : formula.regionalWith false = true) {term : Pattern} (holds : IsHF term) :
    Membership.sat Env.closed formula term ↔
      ∃ proofTerm : CTm (Head L) 0,
        CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (nativeTypeSentence formula term)))) := by
  refine ⟨sentence_proofTerm regional holds, fun proved => ?_⟩
  have true' := models_of_hasProof (L := L) small large proved
  rw [ZFSetUniverseInterpretation.models_embed] at true'
  exact (denote_nativeTypeSentence_regional (Formula.regional_of_regionalWith _ regional) holds _).mp true'

/-- **The front door's verdicts as closed proof terms**: every descent from `3` ends and `0 ∈ 2` are proved, and
`3 ∈ 3` is refuted. -/
theorem verdict_proofTerms :
    (∃ proofTerm : CTm (Head L) 0, CTyped (setLaws L) .nil proofTerm
        (cHolds (trTerm (embed (nativeTypeSentence (.mu (.necessarily .any (.var 0))) three))))) ∧
      (∃ proofTerm : CTm (Head L) 0, CTyped (setLaws L) .nil proofTerm
        (cHolds (trTerm (embed (nativeTypeSentence (.possibly .any (.is zero)) two))))) ∧
      ∃ proofTerm : CTm (Head L) 0, CTyped (setLaws L) .nil proofTerm
        (cHolds (trTerm (embed (negCore (nativeTypeSentence (.possibly .any (.is three)) three))))) :=
  ⟨sentence_proofTerm rfl three_holds (ask_proved three_wellFounded_answer),
    sentence_proofTerm rfl two_holds (ask_proved zero_mem_two_answer),
    refutation_proofTerm rfl three_holds (ask_refuted three_not_mem_self_answer)⟩

end Package

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
