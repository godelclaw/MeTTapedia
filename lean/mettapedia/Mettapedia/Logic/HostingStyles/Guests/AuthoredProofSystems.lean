import Mettapedia.Logic.HostingStyles.AuthoredCertificates
import Mettapedia.Logic.HostingStyles.ContextReadings.ProofSystemsAsData
import Mettapedia.Logic.HostingStyles.Guests.PatternNumbering

/-!
# The proof system of an authored calculus is finitary and numbered

An authored calculus of the shared checker has rules and an authored family of
facts.  Its derivations, kept apart, are a proof system
(`derivationTheory K`): a node is a rule instance or a fact
(`derivationSignature`).

**This proof system is finitary and numbered for every authored calculus,
with nothing assumed** (`derivationTheory_numbered`).

* A rule node is determined by its rule instance: the premises and the
  conclusion of a rule instance are unique.  A rule instance is a name with a
  list of patterns, and has a number (`ruleInstanceCode`).
* A fact node carries no data beyond its judgment: that the judgment is a
  fact is a proposition, so a judgment has at most one fact node
  (`factNode_unique`).  Its number is the number of the judgment.

So the queries, the answers and the programs of the authored family play no
part in the numbering, however many they are.  They would in a numbering of
certificates, whose leaves name a query, an answer and a fuel.

The number of a node also determines the judgment it concludes
(`nodeCode_judgment`).  Hence a derivation kept as data determines the
judgment it derives, under both readings of derivations as atoms: as the
numeral of its number (`derivationCode_judgment`) and node by node
(`derivationAtom_judgment`).

## What the candidate presentation hosts of it

For every authored calculus, as instances of the statements about numbered
proof systems:

| | linear | regions | cartesian |
|---|---|---|---|
| derivations of a judgment, on terms | `numeralsMap_hosting` | `atomsMap_hosting`, restricted | `cartesianAtomsMap_hosting`, restricted |
| derivations with all derived rules | no map at all, as soon as a judgment is derivable: `isEmpty_contextMap_presented_of_derivable` | `atomsMap_hosting` | `cartesianAtomsMap_hosting` |

None of the maps exhausts the atoms (`numeralsMap_not_exhausting`,
`atomsMap_not_exhausting`): the dropping of the quoted unit atom stands for no
derivation (`droppedAtom_not_derivationNumeral`, `not_standsFor_droppedAtom`).

`StandsFor K base goal atom` says that an atom of the candidate is the atom of
a derivation of the judgment, up to the static equivalence.  A judgment has
such an atom exactly when it is derivable (`exists_standsFor_iff_derivable`),
which is exactly when the shared checker accepts a certificate for it
(`exists_standsFor_iff_accepts`); an atom stands for one derivation of one
judgment at most (`standsFor_judgment`, `standsFor_unique`).  Atoms have no
step (existing `probeData_static`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.Guests

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.Contexts (termSetoid)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.GSLT.LanguageDef.InferenceChecker (RuleInstance RuleApplication)
open Mettapedia.GSLT.LanguageDef.Authored
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef (language)
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.ContextReadings
open RuleSignature

variable (K : AuthoredCalculus)

/-! ## The numbering -/

/-- **The number of a node of a derivation**: odd for a rule node, from the
number of its rule instance; even for a fact node, from the number of its
judgment. -/
def nodeCode {goal : Pattern} : DerivationShape K goal → Nat
  | .byRule ruleInstance _ _ => 2 * ruleInstanceCode ruleInstance + 1
  | .fact _ => 2 * patternCode goal

/-- **A judgment has at most one fact node**: that it is a fact is a
proposition. -/
theorem factNode_unique {goal : Pattern} (first second : K.family.Fact goal) :
    (DerivationShape.fact first : DerivationShape K goal) = DerivationShape.fact second :=
  rfl

/-- **The number of a node determines the judgment it concludes.** -/
theorem nodeCode_judgment {goal other : Pattern} (first : DerivationShape K goal)
    (second : DerivationShape K other) (same : nodeCode K first = nodeCode K second) :
    goal = other := by
  cases first with
  | byRule ruleInstance premises application =>
      cases second with
      | byRule otherInstance otherPremises otherApplication =>
          have codes : ruleInstanceCode ruleInstance = ruleInstanceCode otherInstance := by
            have unfolded : 2 * ruleInstanceCode ruleInstance + 1 =
                2 * ruleInstanceCode otherInstance + 1 := same
            omega
          obtain rfl := ruleInstanceCode_injective codes
          exact (application.outputs_unique otherApplication).2
      | fact holds =>
          have unfolded : 2 * ruleInstanceCode ruleInstance + 1 = 2 * patternCode other := same
          omega
  | fact holds =>
      cases second with
      | byRule otherInstance otherPremises otherApplication =>
          have unfolded : 2 * patternCode goal = 2 * ruleInstanceCode otherInstance + 1 := same
          omega
      | fact otherHolds =>
          have unfolded : 2 * patternCode goal = 2 * patternCode other := same
          exact patternCode_injective (by omega)

/-- **Different nodes that conclude one judgment have different numbers.** -/
theorem nodeCode_injective {goal : Pattern} {first second : DerivationShape K goal}
    (same : nodeCode K first = nodeCode K second) : first = second := by
  cases first with
  | byRule ruleInstance premises application =>
      cases second with
      | byRule otherInstance otherPremises otherApplication =>
          have codes : ruleInstanceCode ruleInstance = ruleInstanceCode otherInstance := by
            have unfolded : 2 * ruleInstanceCode ruleInstance + 1 =
                2 * ruleInstanceCode otherInstance + 1 := same
            omega
          obtain rfl := ruleInstanceCode_injective codes
          obtain ⟨rfl, -⟩ := application.outputs_unique otherApplication
          rfl
      | fact holds =>
          have unfolded : 2 * ruleInstanceCode ruleInstance + 1 = 2 * patternCode goal := same
          omega
  | fact holds =>
      cases second with
      | byRule otherInstance otherPremises otherApplication =>
          have unfolded : 2 * patternCode goal = 2 * ruleInstanceCode otherInstance + 1 := same
          omega
      | fact otherHolds => rfl

/-- **The nodes of the derivations of an authored calculus are numbered.** -/
def derivationNumbering : (derivationSignature K).Numbering where
  code := fun shape => nodeCode K shape
  injective := fun same => nodeCode_injective K same

/-- **The proof system of an authored calculus**: its derivations from the
rules and the facts, kept apart, with its derived rules as contexts. -/
noncomputable abbrev derivationTheory : ContextTheory.{0} :=
  (derivationSignature K).proofTheory (ProofCongruence.identity (derivationSignature K))

/-- **The proof system of every authored calculus is finitary and numbered.**
Nothing is assumed of the calculus or of its authored family. -/
theorem derivationTheory_numbered : NumberedProofSystem (derivationTheory K) :=
  ⟨Pattern, derivationSignature K, derivationFinitary K, derivationNumbering K, rfl⟩

/-- The proof systems of the authored calculi. -/
def AuthoredProofSystem (source : ContextTheory.{0}) : Prop :=
  ∃ K : AuthoredCalculus, source = derivationTheory K

/-- **Positive**: the proof system of each authored calculus. -/
theorem authoredProofSystem_member : AuthoredProofSystem (derivationTheory K) := ⟨K, rfl⟩

/-- They are numbered finitary proof systems. -/
theorem AuthoredProofSystem.numbered (source : ContextTheory.{0})
    (member : AuthoredProofSystem source) : NumberedProofSystem source := by
  obtain ⟨K, rfl⟩ := member
  exact derivationTheory_numbered K

/-- **Every judgment of a numbered finitary proof system has countably many
derivations.** -/
theorem NumberedProofSystem.countable_term {source : ContextTheory.{0}}
    (numbered : NumberedProofSystem source) (interface : source.Interface) :
    Countable (source.Term interface) := by
  obtain ⟨J, P, finitary, numbering, rfl⟩ := numbered
  exact Function.Injective.countable (f := finitary.proofCode numbering)
    fun first second same => finitary.proofCode_injective numbering first second same

/-- **Negative**, for `NumberedProofSystem`: the proof system with an axiom
for each set of natural numbers is none; its one judgment has uncountably many
derivations. -/
theorem continuumAxioms_not_numberedProofSystem :
    ¬ NumberedProofSystem
      (continuumAxioms.proofTheory (ProofCongruence.identity continuumAxioms)) := by
  intro numbered
  have countable : Countable (continuumAxioms.Proof ()) :=
    NumberedProofSystem.countable_term numbered ()
  obtain ⟨number, injective⟩ := exists_injective_nat (continuumAxioms.Proof ())
  refine Function.cantor_injective (fun shape : Set Nat =>
    number (continuumAxioms.node (j := ()) shape fun position => position.elim)) ?_
  intro first second same
  exact congrArg continuumAxioms.rootShape (injective same)

/-- **Negative**, for `AuthoredProofSystem`: so it is the proof system of no
authored calculus. -/
theorem continuumAxioms_not_authoredProofSystem :
    ¬ AuthoredProofSystem
      (continuumAxioms.proofTheory (ProofCongruence.identity continuumAxioms)) :=
  fun member => continuumAxioms_not_numberedProofSystem (AuthoredProofSystem.numbered _ member)

/-! ## The number and the atom of a derivation -/

/-- **The number of a derivation.** -/
noncomputable def derivationCode {goal : Pattern} (tree : (derivationSignature K).Proof goal) :
    Nat :=
  (derivationFinitary K).proofCode (derivationNumbering K) tree

/-- Different derivations of one judgment have different numbers. -/
theorem derivationCode_injective {goal : Pattern}
    (first second : (derivationSignature K).Proof goal)
    (same : derivationCode K first = derivationCode K second) : first = second :=
  (derivationFinitary K).proofCode_injective (derivationNumbering K) first second same

/-- **The number of a derivation determines the judgment it derives.** -/
theorem derivationCode_judgment {goal other : Pattern}
    (first : (derivationSignature K).Proof goal) (second : (derivationSignature K).Proof other)
    (same : derivationCode K first = derivationCode K second) : goal = other := by
  obtain ⟨shape, children, rfl⟩ := RuleSignature.Proof.exists_node _ first
  obtain ⟨otherShape, otherChildren, rfl⟩ := RuleSignature.Proof.exists_node _ second
  have unfolded : Nat.pair (nodeCode K shape)
        (Encodable.encode (((derivationFinitary K).positions shape).map fun position =>
          derivationCode K (children position))) =
      Nat.pair (nodeCode K otherShape)
        (Encodable.encode (((derivationFinitary K).positions otherShape).map fun position =>
          derivationCode K (otherChildren position))) := same
  exact nodeCode_judgment K shape otherShape (Nat.pair_eq_pair.mp unfolded).1

/-- **The atom of a derivation**, node by node: the number of its last node
and the atoms of its immediate subderivations. -/
noncomputable def derivationAtom {goal : Pattern} (tree : (derivationSignature K).Proof goal) :
    ProbeAtom :=
  encodeProof (derivationFinitary K) (derivationNumbering K) tree

/-- The static equivalence of the candidate keeps different derivations of
one judgment apart. -/
theorem derivationAtom_apart (base : BasePremiseEvaluator) {goal : Pattern}
    (first second : (derivationSignature K).Proof goal)
    (related : (termSetoid base language closedAtom).r (derivationAtom K first)
      (derivationAtom K second)) : first = second :=
  encodeProof_apart (derivationFinitary K) (derivationNumbering K) base first second related

/-- **The atom of a derivation determines the judgment it derives**, up to
the static equivalence of the candidate. -/
theorem derivationAtom_judgment (base : BasePremiseEvaluator) {goal other : Pattern}
    (first : (derivationSignature K).Proof goal) (second : (derivationSignature K).Proof other)
    (related : (termSetoid base language closedAtom).r (derivationAtom K first)
      (derivationAtom K second)) : goal = other := by
  have same := language_quoteDropOnly.contract_eq related
  rw [derivationAtom, derivationAtom, contract_encodeProof, contract_encodeProof] at same
  obtain ⟨shape, children, rfl⟩ := RuleSignature.Proof.exists_node _ first
  obtain ⟨otherShape, otherChildren, rfl⟩ := RuleSignature.Proof.exists_node _ second
  rw [encodeProof_val_node, encodeProof_val_node] at same
  simp only [nodePattern, keyPattern, Pattern.apply.injEq, List.cons.injEq, and_true,
    true_and] at same
  exact nodeCode_judgment K shape otherShape (numeral_injective same.1)

/-- **No derivation of a numbered finitary proof system is read as the
dropping of the quoted unit atom**, up to the static equivalence: the atom of
a derivation is headed by the pairing constructor and contains no dropping. -/
theorem droppedAtom_not_encodeProof {J : Type} {P : RuleSignature J} (finitary : P.Finitary)
    (numbering : P.Numbering) (base : BasePremiseEvaluator) {j : J} (proof : P.Proof j) :
    ¬ (termSetoid base language closedAtom).r droppedAtom
      (encodeProof finitary numbering proof) := by
  intro related
  have same := language_quoteDropOnly.contract_eq (base := base) related
  obtain ⟨shape, children, rfl⟩ := RuleSignature.Proof.exists_node _ proof
  have image : contract (encodeProof finitary numbering (P.node shape children)).1 =
      (encodeProof finitary numbering (P.node shape children)).1 :=
    contract_encodeProof finitary numbering _
  have heads : head? (contract droppedAtom.1) =
      head? (encodeProof finitary numbering (P.node shape children)).1 :=
    congrArg head? (same.trans image)
  rw [encodeProof_val_node] at heads
  have left : head? (contract droppedAtom.1) = some "prime-drop" := by decide
  rw [left] at heads
  have impossible : some "prime-drop" = some "prime-need-key" := heads
  exact absurd impossible (by decide)

/-! ## The hosting maps -/

/-- **On terms, under the linear reading**: the derivations of one judgment,
each kept as the numeral atom of its number. -/
noncomputable def numeralsMap (base : BasePremiseEvaluator) (goal : Pattern) :
    ContextMap ((derivationTheory K).gslt goal).termsAlone (presentedReading base) :=
  (probeAtoms base).codeMap (source := (derivationTheory K).gslt goal) (derivationCode K)
    (fun same => congrArg _ same)

/-- It is hosting, for every evaluator of the premises of the candidate. -/
theorem numeralsMap_hosting (base : BasePremiseEvaluator) (goal : Pattern) :
    (numeralsMap K base goal).Hosting :=
  (probeAtoms base).codeMap_hosting (source := (derivationTheory K).gslt goal) (derivationCode K)
    (fun same => congrArg _ same)
    (fun first second same => derivationCode_injective K first second same)
    (fun _ _ step => step)

/-- **A term of the candidate outside its image**: the dropping of the quoted
unit atom is the numeral of no derivation. -/
theorem droppedAtom_not_derivationNumeral (base : BasePremiseEvaluator) {goal : Pattern}
    (tree : (derivationSignature K).Proof goal) :
    ¬ ((presentedReading base).equations closedAtom).r droppedAtom
      ((numeralsMap K base goal).term (origin := PUnit.unit) tree) :=
  droppedAtom_not_numeral base (derivationCode K tree)

/-- So the map to numerals does not exhaust the atoms. -/
theorem numeralsMap_not_exhausting (base : BasePremiseEvaluator) (goal : Pattern) :
    ¬ (numeralsMap K base goal).Exhausting :=
  presentedAtoms_not_exhausting base (source := (derivationTheory K).gslt goal) (derivationCode K)
    (fun same => congrArg _ same)

/-- **With all derived rules, under the reading with regions**: a derivation
is its atom, a derived rule a context over atoms. -/
noncomputable def atomsMap (base : BasePremiseEvaluator) :
    ContextMap (derivationTheory K) (regionProbe base) :=
  proofsAsAtoms (derivationFinitary K) (derivationNumbering K) base

/-- It is hosting, for every evaluator. -/
theorem atomsMap_hosting (base : BasePremiseEvaluator) : (atomsMap K base).Hosting :=
  proofsAsAtoms_hosting (derivationFinitary K) (derivationNumbering K) base

/-- **With all derived rules, under the cartesian reading.** -/
noncomputable def cartesianAtomsMap (base : BasePremiseEvaluator) :
    ContextMap (derivationTheory K) (cartesianProbe base) :=
  ((presentedReading base).regionToCartesian probeData).comp (atomsMap K base)

/-- It is hosting, for every evaluator. -/
theorem cartesianAtomsMap_hosting (base : BasePremiseEvaluator) :
    (cartesianAtomsMap K base).Hosting :=
  ((presentedReading base).regionToCartesian_hosting probeData).comp (atomsMap_hosting K base)

/-- **A term of the candidate outside the image of both**: the dropping of the
quoted unit atom is the atom of no derivation of any judgment. -/
theorem droppedAtom_not_derivationAtom (base : BasePremiseEvaluator) {goal : Pattern}
    (tree : (derivationSignature K).Proof goal) :
    ¬ (termSetoid base language closedAtom).r droppedAtom (derivationAtom K tree) :=
  droppedAtom_not_encodeProof (derivationFinitary K) (derivationNumbering K) base tree

/-- So the map to atoms does not exhaust them, as soon as the calculus has a
judgment; and it has: every pattern is one. -/
theorem atomsMap_not_exhausting (base : BasePremiseEvaluator) : ¬ (atomsMap K base).Exhausting :=
  proofsAsAtoms_not_exhausting (derivationFinitary K) (derivationNumbering K) base (.bvar 0)

/-- **Under the linear reading no map of theories goes from the proof system
of an authored calculus to the candidate**, as soon as one judgment is
derivable: a derived rule may ignore an assumption, and a context of the
candidate uses each hole once. -/
theorem isEmpty_contextMap_presented_of_derivable (base : BasePremiseEvaluator) {goal : Pattern}
    (derivable : K.Derivable goal) :
    IsEmpty (ContextMap (derivationTheory K) (presentedReading base)) := by
  obtain ⟨tree⟩ := (nonempty_tree_iff_derivable K goal).mpr derivable
  exact presented_isEmpty_contextMap_proofTheory base (derivationSignature K) _ tree

/-! ## The class, against the three readings -/

/-- **Under every evaluator the candidate is a host of the proof systems of
the authored calculi, on terms.** -/
theorem presented_hostOf_authoredProofSystem_terms (base : BasePremiseEvaluator) :
    HostOf (presentedReading base) AuthoredProofSystem .terms .hosting :=
  (presented_hostOf_numberedProofSystem_terms base).mono AuthoredProofSystem.numbered

/-- **Its reading with regions is a host of them with all their derived
rules.** -/
theorem regionProbe_hostOf_authoredProofSystem_contexts (base : BasePremiseEvaluator) :
    HostOf (regionProbe base) AuthoredProofSystem .contexts .hosting :=
  (regionProbe_hostOf_numberedProofSystem_contexts base).mono AuthoredProofSystem.numbered

/-- **So is its cartesian reading.** -/
theorem cartesianProbe_hostOf_authoredProofSystem_contexts (base : BasePremiseEvaluator) :
    HostOf (cartesianProbe base) AuthoredProofSystem .contexts .hosting :=
  (cartesianProbe_hostOf_numberedProofSystem_contexts base).mono AuthoredProofSystem.numbered

/-! ## Which atoms stand for a derivation -/

/-- **An atom of the candidate stands for a derivation of a judgment**: it is
the atom of one, up to the static equivalence.  This is the image of the
judgment under the reading of derivations as atoms. -/
def StandsFor (base : BasePremiseEvaluator) (goal : Pattern) (atom : ProbeAtom) : Prop :=
  ContextMap.ImageClass (source := (derivationTheory K).gslt goal) (target := presentedReading base)
    closedAtom (derivationAtom K) atom

/-- The atom of a derivation stands for it. -/
theorem standsFor_derivationAtom (base : BasePremiseEvaluator) {goal : Pattern}
    (tree : (derivationSignature K).Proof goal) : StandsFor K base goal (derivationAtom K tree) :=
  ⟨tree, (termSetoid base language closedAtom).iseqv.refl _⟩

/-- **A judgment has an atom that stands for a derivation of it exactly when
it is derivable** from the rules and the facts of the calculus. -/
theorem exists_standsFor_iff_derivable (base : BasePremiseEvaluator) (goal : Pattern) :
    (∃ atom, StandsFor K base goal atom) ↔ K.Derivable goal := by
  rw [← nonempty_tree_iff_derivable]
  exact ⟨fun ⟨_, tree, _⟩ => ⟨tree⟩,
    fun ⟨tree⟩ => ⟨_, standsFor_derivationAtom K base tree⟩⟩

/-- **Exactly when the shared checker accepts a certificate for it.** -/
theorem exists_standsFor_iff_accepts (base : BasePremiseEvaluator) (goal : Pattern) :
    (∃ atom, StandsFor K base goal atom) ↔ K.Accepts goal :=
  (exists_standsFor_iff_derivable K base goal).trans (K.accepts_iff goal).symm

/-- **An atom stands for derivations of one judgment at most.** -/
theorem standsFor_judgment (base : BasePremiseEvaluator) {goal other : Pattern} {atom : ProbeAtom}
    (first : StandsFor K base goal atom) (second : StandsFor K base other atom) : goal = other := by
  obtain ⟨tree, related⟩ := first
  obtain ⟨otherTree, otherRelated⟩ := second
  exact derivationAtom_judgment K base tree otherTree
    ((termSetoid base language closedAtom).iseqv.trans
      ((termSetoid base language closedAtom).iseqv.symm related) otherRelated)

/-- **And for one derivation of it.** -/
theorem standsFor_unique (base : BasePremiseEvaluator) {goal : Pattern} {atom : ProbeAtom}
    {first second : (derivationSignature K).Proof goal}
    (firstRelated : (termSetoid base language closedAtom).r atom (derivationAtom K first))
    (secondRelated : (termSetoid base language closedAtom).r atom (derivationAtom K second)) :
    first = second :=
  derivationAtom_apart K base first second
    ((termSetoid base language closedAtom).iseqv.trans
      ((termSetoid base language closedAtom).iseqv.symm firstRelated) secondRelated)

/-- **Negative**, for `StandsFor`: the dropping of the quoted unit atom stands
for no derivation of any judgment. -/
theorem not_standsFor_droppedAtom (base : BasePremiseEvaluator) (goal : Pattern) :
    ¬ StandsFor K base goal droppedAtom :=
  fun ⟨tree, related⟩ => droppedAtom_not_derivationAtom K base tree related

#print axioms nodeCode_judgment
#print axioms nodeCode_injective
#print axioms derivationNumbering
#print axioms derivationTheory_numbered
#print axioms NumberedProofSystem.countable_term
#print axioms continuumAxioms_not_numberedProofSystem
#print axioms continuumAxioms_not_authoredProofSystem
#print axioms derivationCode_judgment
#print axioms derivationAtom_judgment
#print axioms droppedAtom_not_encodeProof
#print axioms numeralsMap_hosting
#print axioms droppedAtom_not_derivationNumeral
#print axioms numeralsMap_not_exhausting
#print axioms atomsMap_not_exhausting
#print axioms atomsMap_hosting
#print axioms cartesianAtomsMap_hosting
#print axioms droppedAtom_not_derivationAtom
#print axioms isEmpty_contextMap_presented_of_derivable
#print axioms presented_hostOf_authoredProofSystem_terms
#print axioms regionProbe_hostOf_authoredProofSystem_contexts
#print axioms cartesianProbe_hostOf_authoredProofSystem_contexts
#print axioms exists_standsFor_iff_derivable
#print axioms exists_standsFor_iff_accepts
#print axioms standsFor_judgment
#print axioms standsFor_unique
#print axioms not_standsFor_droppedAtom

end Mettapedia.Logic.HostingStyles.Guests
