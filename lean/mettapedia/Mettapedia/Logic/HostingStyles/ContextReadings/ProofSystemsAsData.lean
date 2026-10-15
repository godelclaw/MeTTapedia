import Mettapedia.Logic.HostingStyles.ContextReadings.ProbeReadings

/-!
# Proof systems with their derived rules, hosted as data

A proof system presented by its rules is a theory whose terms are derivations
and whose contexts are derived rules; a derived rule may use an assumption
any number of times, so the theory discards, and as soon as it has a
derivation no map of theories goes from it into the linear reading of the
candidate presentation.

**The reading with regions hosts every numbered finitary proof system with
all its contexts**, derivations kept apart
(`regionProbe_hostOf_numberedProofSystem_contexts`), and so does the cartesian
reading (`cartesianProbe_hostOf_numberedProofSystem_contexts`).

* A derivation is read as an atom, node by node (`encodeProof`): the number
  of its last rule instance paired with the list of the atoms of its
  immediate subderivations.  Different derivations of a judgment are read as
  atoms that the static equivalence keeps apart (`encodeProof_apart`): the
  atoms contain no quotation, so nothing in them is contracted.
* A derived rule is read as a context of the reading over holes that are
  atoms (`encodeOpen`): an assumption is the projection at its hole, a rule
  applied to derived rules is the node pattern over shared holes.  Only data
  is involved, so every hole may be used any number of times.
* Reading commutes with plugging derivations into assumptions
  (`encodeProof_fill`), on the nose.
* Atoms do not reduce, and a proof system has no transition, so the map is
  hosting (`proofsAsAtoms_hosting`).  It is not exhausting: the dropping of a
  quoted atom is an atom that is no derivation (`proofsAsAtoms_not_exhausting`).

The three readings are separated by this one class of sources
(`numberedProofSystems_separate_readings`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.ContextReadings

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeCandidates.Language (Model)
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open RuleSignature

/-! ## The patterns that code a derivation -/

/-- The pattern that pairs two atoms. -/
def keyPattern (first second : Pattern) : Pattern := .apply "prime-need-key" [first, second]

/-- The pattern that puts an atom before a list of atoms. -/
def consPattern (head tail : Pattern) : Pattern :=
  .apply "prime-space-atom-dependency" [head, tail]

/-- The pattern of a list of atoms: ended by the unit atom. -/
def listPattern : List Pattern → Pattern
  | [] => unitAtom
  | head :: tail => consPattern head (listPattern tail)

/-- **The pattern of one node of a derivation**: the number of its rule
instance and the patterns of its immediate subderivations. -/
def nodePattern (code : Nat) (children : List Pattern) : Pattern :=
  keyPattern (numeral code) (listPattern children)

/-- Different lists of patterns have different patterns. -/
theorem listPattern_injective : Function.Injective listPattern := by
  intro first
  induction first with
  | nil =>
      intro second same
      cases second with
      | nil => rfl
      | cons head tail => simp [listPattern, consPattern, unitAtom] at same
  | cons head tail ih =>
      intro second same
      cases second with
      | nil => simp [listPattern, consPattern, unitAtom] at same
      | cons otherHead otherTail =>
          simp only [listPattern, consPattern, Pattern.apply.injEq, List.cons.injEq, and_true,
            true_and] at same
          rw [same.1, ih same.2]

/-- A pair of patterns without quotation has none. -/
theorem contract_keyPattern {first second : Pattern} (plainFirst : contract first = first)
    (plainSecond : contract second = second) :
    contract (keyPattern first second) = keyPattern first second := by
  rw [keyPattern, contract_apply_of_ne (by decide)]
  simp only [List.map_cons, List.map_nil, plainFirst, plainSecond]

/-- A pattern before a list of patterns, none with a quotation, has none. -/
theorem contract_consPattern {head tail : Pattern} (plainHead : contract head = head)
    (plainTail : contract tail = tail) :
    contract (consPattern head tail) = consPattern head tail := by
  rw [consPattern, contract_apply_of_ne (by decide)]
  simp only [List.map_cons, List.map_nil, plainHead, plainTail]

/-- A list of patterns without quotation has none. -/
theorem contract_listPattern : ∀ {patterns : List Pattern},
    (∀ pattern ∈ patterns, contract pattern = pattern) →
      contract (listPattern patterns) = listPattern patterns
  | [], _ => contract_numeral 0
  | head :: _, plain =>
      contract_consPattern (plain head (List.mem_cons_self))
        (contract_listPattern fun pattern member => plain pattern (List.mem_cons_of_mem _ member))

/-- **The pattern of a node contains no quotation to contract**, when the
patterns of its subderivations contain none. -/
theorem contract_nodePattern (code : Nat) {children : List Pattern}
    (plain : ∀ pattern ∈ children, contract pattern = pattern) :
    contract (nodePattern code children) = nodePattern code children :=
  contract_keyPattern (contract_numeral code) (contract_listPattern plain)

/-! ## The atoms that code a derivation -/

/-- The closed atoms of the candidate presentation. -/
abbrev ProbeAtom : Type := Contexts.Term language closedAtom

/-- The numeral atom of a number. -/
def numeralTerm (count : Nat) : ProbeAtom := ⟨numeral count, numeral_wellSorted count⟩

/-- The constructor that pairs two atoms, as a context of two holes. -/
def keyContext :
    Contexts.Context queryFirstCandidatePresentation (fun _ : Bool => closedAtom) closedAtom :=
  binaryContext queryFirstCandidatePresentation (rule := needKeyConstructor)
    (firstName := "revision") (secondName := "subject") (fun _ => "Atom") (by decide) rfl rfl []

/-- The constructor that puts an atom before a list, as a context of two
holes. -/
def consContext :
    Contexts.Context queryFirstCandidatePresentation (fun _ : Bool => closedAtom) closedAtom :=
  binaryContext queryFirstCandidatePresentation (rule := spaceAtomDependencyConstructor)
    (firstName := "key") (secondName := "atom") (fun _ => "Atom") (by decide) rfl rfl []

/-- The pair of two atoms. -/
def keyTerm (first second : ProbeAtom) : ProbeAtom :=
  keyContext.fill fun index => bif index then second else first

@[simp] theorem keyTerm_val (first second : ProbeAtom) :
    (keyTerm first second).1 = keyPattern first.1 second.1 :=
  rfl

/-- An atom before a list of atoms. -/
def consTerm (head tail : ProbeAtom) : ProbeAtom :=
  consContext.fill fun index => bif index then tail else head

@[simp] theorem consTerm_val (head tail : ProbeAtom) :
    (consTerm head tail).1 = consPattern head.1 tail.1 :=
  rfl

/-- The atom of a list of atoms. -/
def listTerm : List ProbeAtom → ProbeAtom
  | [] => unitTerm
  | head :: tail => consTerm head (listTerm tail)

/-- The pattern of the atom of a list of atoms. -/
theorem listTerm_val : ∀ atoms : List ProbeAtom,
    (listTerm atoms).1 = listPattern (atoms.map Subtype.val)
  | [] => rfl
  | head :: tail => by
      rw [listTerm, consTerm_val, listTerm_val tail]
      rfl

/-- The atom of one node of a derivation. -/
def nodeTerm (code : Nat) (children : List ProbeAtom) : ProbeAtom :=
  keyTerm (numeralTerm code) (listTerm children)

/-- The pattern of the atom of a node. -/
theorem nodeTerm_val (code : Nat) (children : List ProbeAtom) :
    (nodeTerm code children).1 = nodePattern code (children.map Subtype.val) := by
  rw [nodeTerm, keyTerm_val, listTerm_val]
  rfl

/-! ## Contexts of the reading over holes that are atoms -/

/-- **The contexts of the reading with regions whose holes and result are
closed atoms.**  Every hole is data, so each may be used any number of
times. -/
abbrev AtomContext (base : BasePremiseEvaluator) (arity : Type) : Type :=
  (presentedReading base).RegionContext probeData (fun _ : arity => closedAtom) closedAtom

namespace AtomContext

variable {base : BasePremiseEvaluator} {arity : Type}

/-- The context that returns what fills one hole. -/
def hole (index : arity) : AtomContext base arity :=
  ContextTheory.RegionContext.project (theory := presentedReading base) (declared := probeData)
    (fun _ : arity => closedAtom) index fun _ => probeData_closedAtom

/-- The context that returns one atom, whatever fills its holes. -/
def constant (atom : ProbeAtom) : AtomContext base arity :=
  ContextTheory.RegionContext.substitute (theory := presentedReading base) (declared := probeData)
    (sharedHoles := fun _ : arity => closedAtom)
    (ContextTheory.RegionContext.constant (holes := fun impossible : Empty => impossible.elim) atom)
    (fun impossible => impossible.elim) fun _ => probeData_closedAtom

/-- The pair of two contexts over the same holes. -/
def key (first second : AtomContext base arity) : AtomContext base arity :=
  ContextTheory.RegionContext.substitute (theory := presentedReading base) (declared := probeData)
    (ContextTheory.RegionContext.ofContext (theory := presentedReading base) keyContext
      fun _ _ => probeData_closedAtom)
    (fun index : Bool => bif index then second else first) fun _ => probeData_closedAtom

/-- A context before a list of contexts over the same holes. -/
def cons (head tail : AtomContext base arity) : AtomContext base arity :=
  ContextTheory.RegionContext.substitute (theory := presentedReading base) (declared := probeData)
    (ContextTheory.RegionContext.ofContext (theory := presentedReading base) consContext
      fun _ _ => probeData_closedAtom)
    (fun index : Bool => bif index then tail else head) fun _ => probeData_closedAtom

/-- The list of contexts over the same holes. -/
def list : List (AtomContext base arity) → AtomContext base arity
  | [] => constant unitTerm
  | head :: tail => cons head (list tail)

/-- The context of one node over the contexts of its subderivations. -/
def node (code : Nat) (children : List (AtomContext base arity)) : AtomContext base arity :=
  key (constant (numeralTerm code)) (list children)

@[simp] theorem act_hole (index : arity) (filling : arity → ProbeAtom) :
    (hole (base := base) index).act filling = filling index :=
  rfl

@[simp] theorem act_constant (atom : ProbeAtom) (filling : arity → ProbeAtom) :
    (constant (base := base) atom).act filling = atom :=
  rfl

/-- The pattern of what a pair of contexts does. -/
theorem act_key_val (first second : AtomContext base arity) (filling : arity → ProbeAtom) :
    ((key first second).act filling).1 =
      keyPattern (first.act filling).1 (second.act filling).1 :=
  rfl

/-- The pattern of what a context before a list of contexts does. -/
theorem act_cons_val (head tail : AtomContext base arity) (filling : arity → ProbeAtom) :
    ((cons head tail).act filling).1 = consPattern (head.act filling).1 (tail.act filling).1 :=
  rfl

/-- The pattern of what a list of contexts does. -/
theorem act_list_val (filling : arity → ProbeAtom) :
    ∀ contexts : List (AtomContext base arity),
      ((list contexts).act filling).1 =
        listPattern (contexts.map fun context => (context.act filling).1)
  | [] => rfl
  | head :: tail => by
      rw [list, act_cons_val, act_list_val filling tail]
      rfl

/-- The pattern of what the context of a node does. -/
theorem act_node_val (code : Nat) (children : List (AtomContext base arity))
    (filling : arity → ProbeAtom) :
    ((node code children).act filling).1 =
      nodePattern code (children.map fun context => (context.act filling).1) := by
  rw [node, act_key_val, act_list_val]
  rfl

end AtomContext

/-! ## Derivations and derived rules -/

section Encoding

variable {J : Type} {P : RuleSignature J} (finitary : P.Finitary) (numbering : P.Numbering)

/-- **The atom of a derivation**: node by node, the number of the rule
instance and the atoms of the immediate subderivations. -/
noncomputable def encodeProof {j : J} (proof : P.Proof j) : ProbeAtom :=
  Fix.fold P (carrier := fun _ _ => ProbeAtom)
    (fun _ _ applied =>
      nodeTerm (numbering.code applied.1) ((finitary.positions applied.1).map applied.2))
    PUnit.unit j proof

@[simp] theorem encodeProof_node {j : J} (shape : P.Shape PUnit.unit j)
    (children : (position : P.Position shape) → P.Proof (P.next shape position)) :
    encodeProof finitary numbering (P.node shape children) =
      nodeTerm (numbering.code shape)
        ((finitary.positions shape).map fun position =>
          encodeProof finitary numbering (children position)) :=
  rfl

/-- The pattern of the atom of a derivation that ends in a rule. -/
theorem encodeProof_val_node {j : J} (shape : P.Shape PUnit.unit j)
    (children : (position : P.Position shape) → P.Proof (P.next shape position)) :
    (encodeProof finitary numbering (P.node shape children)).1 =
      nodePattern (numbering.code shape)
        ((finitary.positions shape).map fun position =>
          (encodeProof finitary numbering (children position)).1) := by
  rw [encodeProof_node, nodeTerm_val, List.map_map]
  rfl

/-- **Different derivations of a judgment have different patterns.** -/
theorem encodeProof_val_injective {j : J} (first : P.Proof j) :
    ∀ second : P.Proof j,
      (encodeProof finitary numbering first).1 = (encodeProof finitary numbering second).1 →
        first = second := by
  induction first using Proof.induction with
  | node shape children ih =>
      intro second same
      obtain ⟨otherShape, otherChildren, rfl⟩ := RuleSignature.Proof.exists_node _ second
      rw [encodeProof_val_node, encodeProof_val_node] at same
      simp only [nodePattern, keyPattern, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and] at same
      obtain ⟨codes, lists⟩ := same
      obtain rfl := numbering.injective (numeral_injective codes)
      have pointwise := List.map_inj_left.mp (listPattern_injective lists)
      have childrenSame : children = otherChildren := funext fun position =>
        ih position _ (pointwise position (finitary.complete shape position))
      rw [childrenSame]

/-- The pattern of a derivation contains no quotation to contract. -/
theorem contract_encodeProof {j : J} (proof : P.Proof j) :
    contract (encodeProof finitary numbering proof).1 = (encodeProof finitary numbering proof).1 := by
  induction proof using Proof.induction with
  | node shape children ih =>
      rw [encodeProof_val_node]
      refine contract_nodePattern _ fun pattern member => ?_
      obtain ⟨position, -, rfl⟩ := List.mem_map.mp member
      exact ih position

/-- **The static equivalence of the candidate keeps different derivations
apart**, for every evaluator of premises. -/
theorem encodeProof_apart (base : BasePremiseEvaluator) {j : J} (first second : P.Proof j)
    (related : (termSetoid base language closedAtom).r (encodeProof finitary numbering first)
      (encodeProof finitary numbering second)) : first = second := by
  have same := language_quoteDropOnly.contract_eq related
  rw [contract_encodeProof, contract_encodeProof] at same
  exact encodeProof_val_injective finitary numbering first second same

/-- **The context of a derived rule**: an assumption is the projection at its
hole, a rule applied to derived rules is the node over their contexts. -/
noncomputable def encodeOpen (base : BasePremiseEvaluator) {arity : Type}
    {assumptions : arity → J} {j : J} (context : P.Open assumptions j) : AtomContext base arity :=
  Free.fold P (carrier := fun _ _ => AtomContext base arity)
    (fun _ _ slot => AtomContext.hole slot.1)
    { act := fun _ _ applied =>
        AtomContext.node (numbering.code applied.1) ((finitary.positions applied.1).map applied.2) }
    PUnit.unit j context

@[simp] theorem encodeOpen_assume (base : BasePremiseEvaluator) {arity : Type}
    {assumptions : arity → J} (index : arity) :
    encodeOpen finitary numbering base (P.assume (holes := assumptions) index) =
      AtomContext.hole index :=
  rfl

@[simp] theorem encodeOpen_node (base : BasePremiseEvaluator) {arity : Type}
    {assumptions : arity → J} {j : J} (shape : P.Shape PUnit.unit j)
    (children : (position : P.Position shape) → P.Open assumptions (P.next shape position)) :
    encodeOpen finitary numbering base (Free.node P shape children) =
      AtomContext.node (numbering.code shape)
        ((finitary.positions shape).map fun position =>
          encodeOpen finitary numbering base (children position)) :=
  rfl

/-- **Reading commutes with plugging**: the atom of a derived rule with its
assumptions filled is the context of the rule filled with the atoms of the
fillings. -/
theorem encodeProof_fill (base : BasePremiseEvaluator) {arity : Type} {assumptions : arity → J}
    {j : J} (context : P.Open assumptions j)
    (filling : (index : arity) → P.Proof (assumptions index)) :
    encodeProof finitary numbering (P.fill context filling) =
      (encodeOpen finitary numbering base context).act fun index =>
        encodeProof finitary numbering (filling index) := by
  induction context using Open.induction with
  | assume index => rfl
  | node shape children ih =>
      apply Subtype.ext
      rw [fill_node, encodeProof_val_node, encodeOpen_node, AtomContext.act_node_val,
        List.map_map]
      congr 1
      apply List.map_congr_left
      intro position _
      exact congrArg Subtype.val (ih position)

/-- **A proof system read into the data of the candidate**: a derivation is
an atom, a derived rule a context over atoms. -/
noncomputable def proofsAsAtoms (base : BasePremiseEvaluator) :
    ContextMap (P.proofTheory (ProofCongruence.identity P)) (regionProbe base) where
  interface := fun _ => closedAtom
  term := fun proof => encodeProof finitary numbering proof
  context := fun context => encodeOpen finitary numbering base context
  term_resp := fun same =>
    ContextMap.equations_of_eq (target := regionProbe base) (interface := closedAtom)
      (congrArg (encodeProof finitary numbering) same)
  equivariant := fun context filling =>
    ContextMap.equations_of_eq (target := regionProbe base) (interface := closedAtom)
      (encodeProof_fill finitary numbering base context filling)

/-- **The reading is hosting**: derivations are kept apart, and atoms do not
reduce. -/
theorem proofsAsAtoms_hosting (base : BasePremiseEvaluator) :
    (proofsAsAtoms finitary numbering base).Hosting := by
  rw [ContextMap.hosting_iff, ContextMap.preservesTransitions_iff_rewrites,
    ContextMap.reflectsTransitions_iff_rewrites]
  refine ⟨fun related => encodeProof_apart finitary numbering base _ _ related,
    fun step => step.elim, fun step => ?_⟩
  exact (probeData_static base probeData_closedAtom _ _ step).elim

/-- **The reading is not exhausting**: the dropping of the quoted unit atom
is an atom that is no derivation. -/
theorem proofsAsAtoms_not_exhausting (base : BasePremiseEvaluator) (j : J) :
    ¬ (proofsAsAtoms finitary numbering base).Exhausting := by
  intro exhausting
  obtain ⟨preimage, related⟩ :=
    ContextMap.Exhausting.term_surjective _ exhausting (origin := j) droppedAtom
  have same := language_quoteDropOnly.contract_eq (base := base) related
  obtain ⟨shape, children, rfl⟩ := RuleSignature.Proof.exists_node _ preimage
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

end Encoding

/-! ## The class of numbered proof systems, against the three readings -/

/-- **The reading with regions is a host of the numbered proof systems, with
all their contexts.** -/
theorem regionProbe_hostOf_numberedProofSystem_contexts (base : BasePremiseEvaluator) :
    HostOf (regionProbe base) NumberedProofSystem .contexts .hosting := by
  rintro reading ⟨J, P, finitary, numbering, rfl⟩
  exact ⟨proofsAsAtoms finitary numbering base, proofsAsAtoms_hosting finitary numbering base⟩

/-- **So is the cartesian reading.** -/
theorem cartesianProbe_hostOf_numberedProofSystem_contexts (base : BasePremiseEvaluator) :
    HostOf (cartesianProbe base) NumberedProofSystem .contexts .hosting :=
  (regionProbe_hostOf_numberedProofSystem_contexts base).trans
    ⟨(presentedReading base).regionToCartesian probeData,
      (presentedReading base).regionToCartesian_hosting probeData⟩

/-- **One class of sources, three readings**: the linear reading receives no
hosting map from the numbered proof systems with their contexts; the reading
with regions and the cartesian reading are hosts of the class. -/
theorem numberedProofSystems_separate_readings (base : BasePremiseEvaluator) :
    ¬ HostOf (presentedReading base) NumberedProofSystem .contexts .hosting ∧
      HostOf (regionProbe base) NumberedProofSystem .contexts .hosting ∧
        HostOf (cartesianProbe base) NumberedProofSystem .contexts .hosting :=
  ⟨fun hosts =>
      let ⟨map, _⟩ := hosts _ twoAxioms_numberedProofSystem
      (presented_isEmpty_contextMap_proofTheory base twoAxioms _ (chosenAxiom true)).false map,
    regionProbe_hostOf_numberedProofSystem_contexts base,
    cartesianProbe_hostOf_numberedProofSystem_contexts base⟩

#print axioms listPattern_injective
#print axioms contract_nodePattern
#print axioms encodeProof_val_injective
#print axioms encodeProof_apart
#print axioms encodeProof_fill
#print axioms proofsAsAtoms
#print axioms proofsAsAtoms_hosting
#print axioms proofsAsAtoms_not_exhausting
#print axioms regionProbe_hostOf_numberedProofSystem_contexts
#print axioms cartesianProbe_hostOf_numberedProofSystem_contexts
#print axioms numberedProofSystems_separate_readings

end Mettapedia.Logic.HostingStyles.ContextReadings
