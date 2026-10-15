import Mathlib.Order.Closure
import Mathlib.CategoryTheory.Adjunction.Basic
import Mettapedia.GSLT.LanguageDef.MultiSortedClone

/-!
# Pi-institutions, closed theories and proof fibres

Consequence is a Tarski closure operator over a covariant sentence functor.
Signature translations preserve consequence. Closed theories form a category,
and proof calculi retain proof fibres independently of their theorem images.
Thin and tagged constructions exhibit what proof erasure preserves and loses.
-/

namespace Mettapedia.Logic.Consequence

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT.LanguageDef (MultiSortedClone)

universe uSignature uHom uSentence uFormula uEvidence uProof

/-! ## Pi-institutions -/

/-- A Pi-institution presents consequence directly, without choosing models.
Sentence translation is covariant, and every signature carries a Tarski
closure operator compatible with translation. -/
structure PiInstitution (Signature : Type uSignature)
    [CategoryTheory.Category.{uHom} Signature] where
  sentence : CategoryTheory.Functor Signature (Type (max uSentence 0))
  consequence : (signature : Signature) →
    ClosureOperator (Set (sentence.obj signature))
  translation : ∀ {source target : Signature} (map : source ⟶ target)
      (premises : Set (sentence.obj source)),
    Set.image (sentence.map map) (consequence source premises) ⊆
      consequence target (Set.image (sentence.map map) premises)

namespace PiInstitution

variable {Signature : Type uSignature}
    [CategoryTheory.Category.{uHom} Signature]
    (institution : PiInstitution Signature)

/-- The consequence judgment induced by closure membership. -/
def Derives (signature : Signature)
    (premises : Set (institution.sentence.obj signature))
    (conclusion : institution.sentence.obj signature) : Prop :=
  conclusion ∈ institution.consequence signature premises

/-- Every premise is derivable. -/
theorem derives_of_mem (signature : Signature)
    {premises : Set (institution.sentence.obj signature)}
    {formula : institution.sentence.obj signature}
    (member : formula ∈ premises) :
    institution.Derives signature premises formula :=
  institution.consequence signature |>.le_closure premises member

/-- Consequence is monotone in its hypotheses. -/
theorem derives_mono (signature : Signature)
    {source target : Set (institution.sentence.obj signature)}
    (subset : source ⊆ target)
    {formula : institution.sentence.obj signature}
    (derives : institution.Derives signature source formula) :
    institution.Derives signature target formula :=
  institution.consequence signature |>.monotone subset derives

/-- Cutting a whole layer of already-derived premises is idempotence of the
closure operator. -/
theorem derives_cut (signature : Signature)
    {premises : Set (institution.sentence.obj signature)}
    {formula : institution.sentence.obj signature}
    (derives : institution.Derives signature
      (institution.consequence signature premises) formula) :
    institution.Derives signature premises formula := by
  change formula ∈ institution.consequence signature
    (institution.consequence signature premises) at derives
  change formula ∈ institution.consequence signature premises
  rw [← (institution.consequence signature).idempotent premises]
  exact derives

/-- The theorem set is consequence from no local hypotheses. -/
def theorems (signature : Signature) :
    Set (institution.sentence.obj signature) :=
  institution.consequence signature ∅

/-- Signature translation preserves theorems. -/
theorem map_theorem {source target : Signature} (map : source ⟶ target)
    {formula : institution.sentence.obj source}
    (theoremhood : formula ∈ institution.theorems source) :
    institution.sentence.map map formula ∈ institution.theorems target := by
  have transported := institution.translation map ∅
    (Set.mem_image_of_mem (institution.sentence.map map) theoremhood)
  simpa [theorems] using transported

/-- A theory is a consequence-closed set of sentences. -/
def Theory (signature : Signature) :=
  { formulas : Set (institution.sentence.obj signature) //
    institution.consequence signature formulas = formulas }

/-! ### Signature-changing comorphisms -/

/-- A signature-changing comorphism of Pi-institutions in the
Fiadeiro--Sernadas direction: signatures and sentences map covariantly, and
translated consequence is preserved.  Source and target signature categories
may differ; the later `Hom` is the useful vertical specialization over one
fixed signature category. -/
structure Comorphism
    {SourceSignature TargetSignature : Type uSignature}
    [CategoryTheory.Category.{uHom} SourceSignature]
    [CategoryTheory.Category.{uHom} TargetSignature]
    (source : PiInstitution.{uSignature, uHom, uSentence} SourceSignature)
    (target : PiInstitution.{uSignature, uHom, uSentence} TargetSignature) where
  mapSignature : CategoryTheory.Functor SourceSignature TargetSignature
  mapSentence : ∀ signature, source.sentence.obj signature →
    target.sentence.obj (mapSignature.obj signature)
  mapSentence_natural : ∀ {sourceSignature targetSignature}
      (translation : sourceSignature ⟶ targetSignature)
      (formula : source.sentence.obj sourceSignature),
    target.sentence.map (mapSignature.map translation)
        (mapSentence sourceSignature formula) =
      mapSentence targetSignature (source.sentence.map translation formula)
  preserves : ∀ (signature : SourceSignature)
      (premises : Set (source.sentence.obj signature))
      (formula : source.sentence.obj signature),
    formula ∈ source.consequence signature premises →
      mapSentence signature formula ∈
        target.consequence (mapSignature.obj signature)
          (Set.image (mapSentence signature) premises)

namespace Comorphism

/-- A signature-changing consequence route is determined by its signature
functor and sentence translation.  Naturality and preservation are
propositions and do not add a second notion of arrow identity. -/
@[ext]
theorem ext
    {SourceSignature TargetSignature : Type uSignature}
    [CategoryTheory.Category.{uHom} SourceSignature]
    [CategoryTheory.Category.{uHom} TargetSignature]
    {source : PiInstitution.{uSignature, uHom, uSentence} SourceSignature}
    {target : PiInstitution.{uSignature, uHom, uSentence} TargetSignature}
    {left right : Comorphism source target}
    (signature : left.mapSignature = right.mapSignature)
    (sentence : HEq left.mapSentence right.mapSentence) :
    left = right := by
  cases left
  cases right
  cases signature
  cases sentence
  rfl

def identity
    {Signature : Type uSignature}
    [CategoryTheory.Category.{uHom} Signature]
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature) :
    Comorphism institution institution where
  mapSignature :=
    { obj := id
      map := fun translation => translation
      map_id := by intro signature; rfl
      map_comp := by intro source target last earlier later; rfl }
  mapSentence := fun _ formula => formula
  mapSentence_natural := by intro source target translation formula; rfl
  preserves := by
    intro signature premises formula derives
    simp only [id, Set.image_id']
    exact derives

def comp
    {FirstSignature MiddleSignature LastSignature : Type uSignature}
    [CategoryTheory.Category.{uHom} FirstSignature]
    [CategoryTheory.Category.{uHom} MiddleSignature]
    [CategoryTheory.Category.{uHom} LastSignature]
    {first : PiInstitution.{uSignature, uHom, uSentence} FirstSignature}
    {middle : PiInstitution.{uSignature, uHom, uSentence} MiddleSignature}
    {last : PiInstitution.{uSignature, uHom, uSentence} LastSignature}
    (earlier : Comorphism first middle) (later : Comorphism middle last) :
    Comorphism first last where
  mapSignature := CategoryTheory.Functor.comp earlier.mapSignature
    later.mapSignature
  mapSentence := fun signature formula =>
    later.mapSentence (earlier.mapSignature.obj signature)
      (earlier.mapSentence signature formula)
  mapSentence_natural := by
    intro sourceSignature targetSignature translation formula
    change last.sentence.map
        (later.mapSignature.map (earlier.mapSignature.map translation))
        (later.mapSentence (earlier.mapSignature.obj sourceSignature)
          (earlier.mapSentence sourceSignature formula)) = _
    rw [later.mapSentence_natural, earlier.mapSentence_natural]
  preserves := by
    intro signature premises formula derives
    have firstDerives := earlier.preserves signature premises formula derives
    have lastDerives := later.preserves (earlier.mapSignature.obj signature)
      (Set.image (earlier.mapSentence signature) premises)
      (earlier.mapSentence signature formula) firstDerives
    rw [Set.image_image] at lastDerives
    change later.mapSentence (earlier.mapSignature.obj signature)
        (earlier.mapSentence signature formula) ∈
      last.consequence
        (later.mapSignature.obj (earlier.mapSignature.obj signature))
        (Set.image
          (fun sourceFormula =>
            later.mapSentence (earlier.mapSignature.obj signature)
              (earlier.mapSentence signature sourceFormula)) premises)
    exact lastDerives

end Comorphism

/-! ### Morphisms over a fixed signature category -/

/-- A morphism of Pi-institutions over the same signature category.  Sentence
translation is natural, and derivability is preserved after translating every
hypothesis.  More general morphisms may also change the signature category;
this vertical category is the exact part needed for comparing consequence
layers over one SemanticService authority diagram. -/
structure Hom
    (source target : PiInstitution.{uSignature, uHom, uSentence} Signature) where
  mapSentence : source.sentence ⟶ target.sentence
  preserves : ∀ (signature : Signature)
      (premises : Set (source.sentence.obj signature))
      (formula : source.sentence.obj signature),
    formula ∈ source.consequence signature premises →
      mapSentence.app signature formula ∈
        target.consequence signature
          (Set.image (mapSentence.app signature) premises)

namespace Hom

variable {source middle target :
  PiInstitution.{uSignature, uHom, uSentence} Signature}

def identity (institution :
    PiInstitution.{uSignature, uHom, uSentence} Signature) :
    Hom institution institution where
  mapSentence := CategoryTheory.NatTrans.id institution.sentence
  preserves := by
    intro signature premises formula derives
    simpa using derives

def comp (earlier : Hom source middle) (later : Hom middle target) :
    Hom source target where
  mapSentence := CategoryTheory.CategoryStruct.comp earlier.mapSentence
    later.mapSentence
  preserves := by
    intro signature premises formula derives
    have first := earlier.preserves signature premises formula derives
    have second := later.preserves signature
      (Set.image (earlier.mapSentence.app signature) premises)
      (earlier.mapSentence.app signature formula) first
    have imageComposition :
        Set.image (later.mapSentence.app signature)
            (Set.image (earlier.mapSentence.app signature) premises) =
          Set.image
            ((CategoryTheory.CategoryStruct.comp earlier.mapSentence
              later.mapSentence).app signature) premises := by
      ext translated
      constructor
      · rintro ⟨middleFormula, ⟨sourceFormula, member, rfl⟩, rfl⟩
        exact ⟨sourceFormula, member, rfl⟩
      · rintro ⟨sourceFormula, member, rfl⟩
        exact ⟨earlier.mapSentence.app signature sourceFormula,
          ⟨sourceFormula, member, rfl⟩, rfl⟩
    rw [imageComposition] at second
    exact second

@[ext]
theorem ext {left right : Hom source target}
    (mapSentenceEqual : left.mapSentence = right.mapSentence) :
    left = right := by
  cases left
  cases right
  cases mapSentenceEqual
  rfl

end Hom

instance instQuiverPiInstitution :
    Quiver (PiInstitution.{uSignature, uHom, uSentence} Signature) where
  Hom := Hom

instance instCategoryPiInstitution :
    CategoryTheory.Category
      (PiInstitution.{uSignature, uHom, uSentence} Signature) where
  id := Hom.identity
  comp := Hom.comp
  id_comp morphism := by
    apply Hom.ext
    exact CategoryTheory.Category.id_comp morphism.mapSentence
  comp_id morphism := by
    apply Hom.ext
    exact CategoryTheory.Category.comp_id morphism.mapSentence
  assoc first second third := by
    apply Hom.ext
    exact CategoryTheory.Category.assoc first.mapSentence second.mapSentence
      third.mapSentence

/-! ### The category of closed theories -/

/-- A closed theory retains both its signature and its consequence-closed
set of sentences. -/
structure TheoryObject
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature) where
  signature : Signature
  theory : institution.Theory signature

/-- The theory generated by an arbitrary axiom set is its consequence
closure. -/
def generatedTheory
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature)
    (signature : Signature)
    (axioms : Set (institution.sentence.obj signature)) :
    TheoryObject institution where
  signature := signature
  theory := ⟨institution.consequence signature axioms,
    (institution.consequence signature).idempotent axioms⟩

@[simp]
theorem mem_generatedTheory_iff
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature)
    (signature : Signature)
    (axioms : Set (institution.sentence.obj signature))
    (formula : institution.sentence.obj signature) :
    formula ∈ (generatedTheory institution signature axioms).theory.1 ↔
      formula ∈ institution.consequence signature axioms :=
  Iff.rfl

/-- A theory morphism translates the signature and sends every source theorem
to a target theorem. -/
structure TheoryHom
    {institution : PiInstitution.{uSignature, uHom, uSentence} Signature}
    (source target : TheoryObject institution) where
  mapSignature : source.signature ⟶ target.signature
  preserves : ∀ {formula}, formula ∈ source.theory.1 →
    institution.sentence.map mapSignature formula ∈ target.theory.1

namespace TheoryHom

variable {institution :
  PiInstitution.{uSignature, uHom, uSentence} Signature}
  {first middle last : TheoryObject institution}

def identity (theory : TheoryObject institution) : TheoryHom theory theory where
  mapSignature := CategoryTheory.CategoryStruct.id theory.signature
  preserves := by
    intro formula theoremhood
    simpa using theoremhood

def comp (earlier : TheoryHom first middle) (later : TheoryHom middle last) :
    TheoryHom first last where
  mapSignature := CategoryTheory.CategoryStruct.comp earlier.mapSignature
    later.mapSignature
  preserves := by
    intro formula theoremhood
    have middleTheorem := earlier.preserves theoremhood
    have lastTheorem := later.preserves middleTheorem
    simpa using lastTheorem

@[ext]
theorem ext {source target : TheoryObject institution}
    {left right : TheoryHom source target}
    (mapEqual : left.mapSignature = right.mapSignature) : left = right := by
  cases left
  cases right
  cases mapEqual
  rfl

end TheoryHom

instance instQuiverTheoryObject
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature) :
    Quiver (TheoryObject institution) where
  Hom := TheoryHom

instance instCategoryTheoryObject
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature) :
    CategoryTheory.Category (TheoryObject institution) where
  id := TheoryHom.identity
  comp := TheoryHom.comp
  id_comp morphism := by
    apply TheoryHom.ext
    exact CategoryTheory.Category.id_comp morphism.mapSignature
  comp_id morphism := by
    apply TheoryHom.ext
    exact CategoryTheory.Category.comp_id morphism.mapSignature
  assoc first second third := by
    apply TheoryHom.ext
    exact CategoryTheory.Category.assoc first.mapSignature second.mapSignature
      third.mapSignature

/-- Sentences indexed by the category of closed theories. -/
def theorySentence (institution :
    PiInstitution.{uSignature, uHom, uSentence} Signature) :
    CategoryTheory.Functor (TheoryObject institution) (Type uSentence) where
  obj theory := institution.sentence.obj theory.signature
  map translation := institution.sentence.map translation.mapSignature
  map_id theory := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro formula
    exact institution.sentence.map_id_apply theory.signature formula
  map_comp earlier later := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro formula
    exact institution.sentence.map_comp_apply earlier.mapSignature
      later.mapSignature formula

/-! ### The proof-projection nucleus of a Meseguer proof calculus -/

/-- Proof objects functorial in closed theories, whose projection has exactly
each theory's theorem set as image.  This is the proof-to-sentence nucleus of
Meseguer's proof-calculus account.  Models and satisfaction are not part of
it, and richer proof structures may replace the present Type-valued functor. -/
structure ProofCalculus
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature) where
  proof : CategoryTheory.Functor (TheoryObject institution) (Type uSentence)
  projection : proof ⟶ theorySentence institution
  theorem_image : ∀ (theory : TheoryObject institution)
      (formula : institution.sentence.obj theory.signature),
    (∃ evidence : proof.obj theory,
      projection.app theory evidence = formula) ↔
        formula ∈ theory.theory.1

namespace ProofCalculus

variable {institution :
  PiInstitution.{uSignature, uHom, uSentence} Signature}

/-- The canonical thin proof functor has exactly one proof-irrelevant object
for each theorem of each closed theory. -/
def thinProofFunctor (institution :
    PiInstitution.{uSignature, uHom, uSentence} Signature) :
    CategoryTheory.Functor (TheoryObject institution) (Type uSentence) where
  obj theory := { formula : institution.sentence.obj theory.signature //
    formula ∈ theory.theory.1 }
  map translation := TypeCat.ofHom fun theoremObject =>
    ⟨institution.sentence.map translation.mapSignature theoremObject.1,
      translation.preserves theoremObject.2⟩
  map_id theory := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro theoremObject
    apply Subtype.ext
    exact institution.sentence.map_id_apply theory.signature theoremObject.1
  map_comp earlier later := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro theoremObject
    apply Subtype.ext
    exact institution.sentence.map_comp_apply earlier.mapSignature
      later.mapSignature theoremObject.1

/-- Every Pi-institution admits a canonical thin proof-calculus nucleus. -/
def thin (institution :
    PiInstitution.{uSignature, uHom, uSentence} Signature) :
    ProofCalculus institution where
  proof := thinProofFunctor institution
  projection :=
    { app := fun _ => TypeCat.ofHom Subtype.val
      naturality := by intro source target translation; rfl }
  theorem_image := by
    intro theory formula
    constructor
    · rintro ⟨proof, projected⟩
      simpa [thinProofFunctor] using projected ▸ proof.2
    · intro theoremhood
      exact ⟨⟨formula, theoremhood⟩, rfl⟩

/-- A proof-relevant presentation with the same theorem image as the thin
calculus.  The Boolean tag is retained by theory translation but erased by
the proof-to-sentence projection. -/
def taggedProofFunctor (institution :
    PiInstitution.{uSignature, uHom, uSentence} Signature) :
    CategoryTheory.Functor (TheoryObject institution) (Type uSentence) where
  obj theory :=
    { formula : institution.sentence.obj theory.signature //
      formula ∈ theory.theory.1 } × Bool
  map translation := TypeCat.ofHom fun proof =>
    (⟨institution.sentence.map translation.mapSignature proof.1.1,
      translation.preserves proof.1.2⟩, proof.2)
  map_id theory := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro proof
    apply Prod.ext
    · apply Subtype.ext
      exact institution.sentence.map_id_apply theory.signature proof.1.1
    · rfl
  map_comp earlier later := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro proof
    apply Prod.ext
    · apply Subtype.ext
      exact institution.sentence.map_comp_apply earlier.mapSignature
        later.mapSignature proof.1.1
    · rfl

/-- The theorem-image law permits genuinely proof-relevant fibres; it does
not identify a logic with its thin closure presentation. -/
def tagged (institution :
    PiInstitution.{uSignature, uHom, uSentence} Signature) :
    ProofCalculus institution where
  proof := taggedProofFunctor institution
  projection :=
    { app := fun _ => TypeCat.ofHom fun proof => proof.1.1
      naturality := by intro source target translation; rfl }
  theorem_image := by
    intro theory formula
    constructor
    · rintro ⟨proof, projected⟩
      simpa [taggedProofFunctor] using projected ▸ proof.1.2
    · intro theoremhood
      exact ⟨(⟨formula, theoremhood⟩, false), rfl⟩

/-- Positive proof relevance can coexist with the exact same theorem image:
the tagged calculus has two proofs of every theorem that project to the same
sentence. -/
theorem tagged_projection_not_injective
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature)
    (theory : TheoryObject institution)
    (formula : institution.sentence.obj theory.signature)
    (theoremhood : formula ∈ theory.theory.1) :
    ¬ Function.Injective ((tagged institution).projection.app theory) := by
  intro injective
  let falseProof : (tagged institution).proof.obj theory :=
    (⟨formula, theoremhood⟩, false)
  let trueProof : (tagged institution).proof.obj theory :=
    (⟨formula, theoremhood⟩, true)
  have equalProofs : falseProof = trueProof := injective rfl
  have equalTags := congrArg Prod.snd equalProofs
  change false = true at equalTags
  cases equalTags

/-- The theorem-image law turns theoremhood back into an actual proof object;
this direction is exactly what a raw proof projection without adequacy lacks. -/
theorem proof_of_theorem (calculus : ProofCalculus institution)
    (theory : TheoryObject institution)
    (formula : institution.sentence.obj theory.signature)
    (theoremhood : formula ∈ theory.theory.1) :
    ∃ evidence : calculus.proof.obj theory,
      calculus.projection.app theory evidence = formula :=
  (calculus.theorem_image theory formula).mpr theoremhood

/-- A theory with a theorem cannot have an empty proof fibre in any adequate
proof calculus.  This is the negative boundary supplied by the image law. -/
theorem theorem_forbids_empty_proof_fibre
    (calculus : ProofCalculus institution) (theory : TheoryObject institution)
    (formula : institution.sentence.obj theory.signature)
    (theoremhood : formula ∈ theory.theory.1) :
    ¬ IsEmpty (calculus.proof.obj theory) := by
  intro emptyProofs
  obtain ⟨evidence, projected⟩ :=
    calculus.proof_of_theorem theory formula theoremhood
  exact emptyProofs.false evidence

end ProofCalculus

/-! ### Proof fibres with retained composition equations -/

/-- A proof fibre over one closed theory upgraded from a set of closed proofs
to a multisorted clone.  Its operations are proofs from ordered contexts,
projections retain hypothesis occurrences, and clone substitution is proof
composition.  The theorem-image law concerns only the nullary operations. -/
structure CloneProofFibre
    (theory : TheoryObject institution) where
  proof : MultiSortedClone.{uSentence, uProof}
    (institution.sentence.obj theory.signature)
  theorem_image : ∀ formula,
    Nonempty (proof.Hom [] formula) ↔ formula ∈ theory.theory.1

/-- Consequence relative to a closed theory: the theory is available as a
fixed collection of global hypotheses while `premises` remains local. -/
noncomputable def relativeClosure
    (theory : TheoryObject institution) :
    ClosureOperator (Set (institution.sentence.obj theory.signature)) :=
  ClosureOperator.mk'
    (fun premises => institution.consequence theory.signature
      (theory.theory.1 ∪ premises))
    (by
      intro source target subset
      exact (institution.consequence theory.signature).monotone
        (Set.union_subset_union_right _ subset))
    (by
      intro premises formula member
      exact (institution.consequence theory.signature).le_closure _
        (Set.mem_union_right _ member))
    (by
      intro premises formula twice
      have narrowed := (institution.consequence theory.signature).monotone
        (show theory.theory.1 ∪
              institution.consequence theory.signature
                (theory.theory.1 ∪ premises) ⊆
            institution.consequence theory.signature
              (theory.theory.1 ∪ premises) by
          intro hypothesis member
          rcases member with theoryMember | derived
          · exact (institution.consequence theory.signature).le_closure _
              (Set.mem_union_left _ theoryMember)
          · exact derived)
        twice
      simpa only [(institution.consequence theory.signature).idempotent]
        using narrowed)

@[simp]
theorem relativeClosure_empty
    (theory : TheoryObject institution) :
    institution.relativeClosure theory ∅ = theory.theory.1 := by
  change institution.consequence theory.signature
      (theory.theory.1 ∪ ∅) = theory.theory.1
  simpa using theory.theory.2

/-- Thin evidence for a closure operator forms a genuine multisorted clone.
The equations hold because every inhabited proof fibre is subsingleton; this
is the proof-irrelevant cartesian boundary, not a reconstruction of native
proof identity. -/
noncomputable def thinCloneOfClosure
    {Formula : Type uFormula}
    (closure : ClosureOperator (Set Formula)) :
    MultiSortedClone Formula where
  Hom context goal := PLift (goal ∈ closure { formula | formula ∈ context })
  project := fun {context} index =>
    ⟨closure.le_closure _ (List.get_mem context index)⟩
  substitute := by
    intro sourceContext targetContext output operation environment
    refine ⟨?_⟩
    have twice : output ∈ closure
        (closure { formula | formula ∈ targetContext }) :=
      closure.monotone (fun hypothesis member => by
        obtain ⟨index, indexEq⟩ := List.get_of_mem member
        exact indexEq ▸ (environment index).down) operation.down
    simpa only [closure.idempotent] using twice
  substitute_project := by
    intro sourceContext targetContext environment index
    exact Subsingleton.elim _ _
  substitute_projects := by
    intro context output operation
    exact Subsingleton.elim _ _
  substitute_assoc := by
    intro firstContext secondContext thirdContext output operation first second
    exact Subsingleton.elim _ _

/-- Every Pi-institution has a canonical proof-irrelevant clone fibre over
each closed theory.  Its nullary operations are exactly that theory's
theorems. -/
noncomputable def CloneProofFibre.thin
    (theory : TheoryObject institution) :
    CloneProofFibre.{uSignature, uHom, uSentence, 0} institution theory where
  proof := thinCloneOfClosure (institution.relativeClosure theory)
  theorem_image := by
    intro formula
    change Nonempty (PLift
        (formula ∈ institution.relativeClosure theory
          { sentence | sentence ∈ ([] : List
            (institution.sentence.obj theory.signature)) })) ↔ _
    simp only [List.not_mem_nil, Set.ofPred_false, relativeClosure_empty]
    constructor
    · rintro ⟨proof⟩
      exact proof.down
    · intro theoremhood
      exact ⟨⟨theoremhood⟩⟩

end PiInstitution

end Mettapedia.Logic.Consequence
