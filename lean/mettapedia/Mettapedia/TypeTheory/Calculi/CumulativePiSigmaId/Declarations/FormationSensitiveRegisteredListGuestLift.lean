import Mettapedia.TypeTheory.IndexedContainerInduction
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeList

/-!
# A proof-relevant guest lift for registered Lists

A nested List field needs one recursive result or induction witness per source
element.  For canonical typed List spines, the native proof-relevant `mapRel`
already carries exactly this information.  This module proves the exact
equivalence and connects it to the existing formation-sensitive syntax and
semantic-evidence theorem.

The result qualifies canonical finite List spines.  An arbitrary open List
term still needs the native List eliminator in the generated nested recursor;
that later compiler edge is not claimed here.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveRegisteredListGuestLift

open Presentation NativeIndexedFamilies IntrinsicCanonicalSemantics
open FormationSensitiveNativeList (Typing ListTyping EvidenceTyping)
open Mettapedia.TypeTheory.IndexedContainer

universe u

variable {n : Nat} {context : Tower.Ctx n}
variable {source target relation : Tower.Tm n}

/-- For one source element, retain its target and the actual typed relation
evidence connecting them. -/
abbrev ElementLift (target relation : Tower.Tm n)
    (sourceTerm : TypedTerm context source) :=
  Σ targetTerm : TypedTerm context target,
    TypedRelationEvidence relation sourceTerm targetTerm

/-- One selected target List and a proof-relevant pointwise lifting from the
fixed source List. -/
abbrev CanonicalLift (target relation : Tower.Tm n)
    (sourceList : CanonicalList context source) :=
  Σ targetList : CanonicalList context target,
    CanonicalMapRel relation sourceList targetList

/-- Read a proof-relevant relation spine as one target/evidence pair per
source element. -/
def toAll (target relation : Tower.Tm n) :
    ∀ (sourceList : CanonicalList context source),
      CanonicalLift target relation sourceList →
        ListAll (ElementLift target relation) sourceList
  | [], ⟨[], .nil⟩ => .nil
  | _ :: sourceTail, ⟨targetHead :: targetTail, .cons headEvidence tailEvidence⟩ =>
      .cons ⟨targetHead, headEvidence⟩
        (toAll target relation sourceTail ⟨targetTail, tailEvidence⟩)

/-- Rebuild the target List and proof-relevant relation spine from the
positionwise bundle. -/
def ofAll (target relation : Tower.Tm n) :
    ∀ (sourceList : CanonicalList context source),
      ListAll (ElementLift target relation) sourceList →
        CanonicalLift target relation sourceList
  | [], .nil => ⟨[], .nil⟩
  | _ :: sourceTail, .cons headLift tailLift =>
      let tail := ofAll target relation sourceTail tailLift
      ⟨headLift.1 :: tail.1, .cons headLift.2 tail.2⟩

theorem ofAll_toAll (target relation : Tower.Tm n) :
    ∀ (sourceList : CanonicalList context source)
      (lifted : CanonicalLift target relation sourceList),
      ofAll target relation sourceList (toAll target relation sourceList lifted) = lifted := by
  intro sourceList
  induction sourceList with
  | nil =>
      intro lifted
      rcases lifted with ⟨targetList, evidence⟩
      cases evidence
      rfl
  | cons sourceHead sourceTail ih =>
      intro lifted
      rcases lifted with ⟨targetList, evidence⟩
      cases evidence with
      | cons headEvidence tailEvidence =>
          simp only [toAll, ofAll]
          rw [ih ⟨_, tailEvidence⟩]

theorem toAll_ofAll (target relation : Tower.Tm n) :
    ∀ (sourceList : CanonicalList context source)
      (lifted : ListAll (ElementLift target relation) sourceList),
      toAll target relation sourceList (ofAll target relation sourceList lifted) = lifted := by
  intro sourceList
  induction sourceList with
  | nil => intro lifted; cases lifted; rfl
  | cons sourceHead sourceTail ih =>
      intro lifted
      cases lifted with
      | cons headLift tailLift =>
      simp only [ofAll, toAll]
      rw [ih tailLift]

/-- A relational List spine is exactly a source-ordered dependent list of
target/evidence pairs. -/
def canonicalLiftEquiv (target relation : Tower.Tm n)
    (sourceList : CanonicalList context source) :
    CanonicalLift target relation sourceList ≃
      ListAll (ElementLift target relation) sourceList where
  toFun := toAll target relation sourceList
  invFun := ofAll target relation sourceList
  left_inv := ofAll_toAll target relation sourceList
  right_inv := toAll_ofAll target relation sourceList

/-- Equivalently, a canonical lift supplies one target/evidence pair at every
actual List position. -/
def canonicalLiftPositionEquiv (target relation : Tower.Tm n)
    (sourceList : CanonicalList context source) :
    CanonicalLift target relation sourceList ≃
      (∀ position : Fin sourceList.length,
        ElementLift target relation (sourceList.get position)) :=
  (canonicalLiftEquiv target relation sourceList).trans
    (listAllEquiv (ElementLift target relation) sourceList)

/-- The canonical source List as the actual registered List-container value. -/
def semanticValue (sourceList : CanonicalList context source) :
    IndexedContainer.Examples.list.Extension
      (TypedTerm context source) () :=
  ⟨sourceList.length, sourceList.get⟩

/-- The native relational spine is an object representation of the exact
semantic induction bundle selected by the registered List entry. -/
noncomputable def canonicalLiftSemanticBundleEquiv
    (target relation : Tower.Tm n)
    (sourceList : CanonicalList context source) :
    CanonicalLift target relation sourceList ≃
      (IndexedContainer.listInductionBundle
        (ElementLift target relation)).Bundle (semanticValue sourceList) :=
  (canonicalLiftEquiv target relation sourceList).trans
    (Equiv.cast (congrArg (ListAll (ElementLift target relation))
      (List.ofFn_get sourceList).symm))

/-- Composing the object representation with the registered-container law
recovers exactly one recursive witness at every actual List position. -/
noncomputable def canonicalLiftRegisteredPositionEquiv
    (target relation : Tower.Tm n)
    (sourceList : CanonicalList context source) :
    CanonicalLift target relation sourceList ≃
      (∀ position : IndexedContainer.Examples.list.Position
          (semanticValue sourceList).1,
        ElementLift target relation ((semanticValue sourceList).2 position)) :=
  (canonicalLiftSemanticBundleEquiv target relation sourceList).trans
    ((IndexedContainer.listInductionBundle
      (ElementLift target relation)).exact (semanticValue sourceList))

/-- The registered semantic route and direct source-list route preserve the
same target and proof-relevant evidence at every position. -/
theorem canonicalLiftRegisteredPositionEquiv_eq
    (target relation : Tower.Tm n) (sourceList : CanonicalList context source) :
    canonicalLiftRegisteredPositionEquiv target relation sourceList =
      canonicalLiftPositionEquiv target relation sourceList := by
  apply Equiv.ext
  intro lifted
  funext position
  exact IndexedContainer.listInductionBundle_exact_cast
    (ElementLift target relation) sourceList
    (toAll target relation sourceList lifted) position

/-- Formation-sensitive evidence required to publish the native List lift. -/
structure QualifiedLift (target relation : Tower.Tm n)
    (sourceList : CanonicalList context source) where
  targetList : CanonicalList context target
  evidence : CanonicalMapRel relation sourceList targetList
  sourceLeaves : ListTyping sourceList
  evidenceLeaves : EvidenceTyping evidence

namespace QualifiedLift

/-- The selected target spine is formation-sensitively typed. -/
theorem targetLeaves {sourceList : CanonicalList context source}
    (lift : QualifiedLift target relation sourceList) :
    ListTyping lift.targetList :=
  lift.evidenceLeaves.targetList

/-- A qualified lift publishes both the actual typed `mapRel` term and the
matching semantic position evidence. -/
theorem judgment_and_positionEvidence
    {sourceList : CanonicalList context source}
    (lift : QualifiedLift target relation sourceList)
    (formedContext : FormationSensitive.ContextFormation IntrinsicRelator.rules context)
    (sourceTyping : Typing context source (sortTm Intrinsic.elementLevel))
    (targetTyping : Typing context target (sortTm Intrinsic.elementLevel))
    (relationTyping : Typing context relation
      (.pi source (.pi (rename wk target) (sortTm Intrinsic.motiveLevel)))) :
    FormationSensitive.Judgment IntrinsicRelator.rules context
      (encodeMapRel lift.evidence)
      (IntrinsicRelator.mapRelApp source target relation
        (encodeList source sourceList) (encodeList target lift.targetList)) ∧
      Nonempty ((∀ position : Fin sourceList.length,
        ElementLift target relation (sourceList.get position))) := by
  have checked := FormationSensitiveNativeList.encodeMapRel_judgment_and_semanticEvidence formedContext
    sourceTyping targetTyping relationTyping lift.evidence lift.evidenceLeaves
  refine ⟨checked.1, ?_⟩
  exact ⟨canonicalLiftPositionEquiv target relation sourceList
    ⟨lift.targetList, lift.evidence⟩⟩

/-- The published native judgment transports along every typed context
substitution; no private nested-substitution rule is introduced. -/
theorem substitute
    {sourceList : CanonicalList context source}
    (lift : QualifiedLift target relation sourceList)
    (formedContext : FormationSensitive.ContextFormation IntrinsicRelator.rules context)
    (sourceTyping : Typing context source (sortTm Intrinsic.elementLevel))
    (targetTyping : Typing context target (sortTm Intrinsic.elementLevel))
    (relationTyping : Typing context relation
      (.pi source (.pi (rename wk target) (sortTm Intrinsic.motiveLevel))))
    {m : Nat} {targetContext : Tower.Ctx m} (substitution : Sub Tower.Head n m)
    (targetFormed : FormationSensitive.ContextFormation IntrinsicRelator.rules targetContext)
    (typedSubstitution : FormationSensitive.CtxMor IntrinsicRelator.rules
      context targetContext substitution) :
    FormationSensitive.Judgment IntrinsicRelator.rules targetContext
      (subst substitution (encodeMapRel lift.evidence))
      (subst substitution (IntrinsicRelator.mapRelApp source target relation
        (encodeList source sourceList) (encodeList target lift.targetList))) :=
  (judgment_and_positionEvidence lift formedContext sourceTyping targetTyping
    relationTyping).1.substitute targetFormed typedSubstitution

end QualifiedLift

/-! ## Positive and negative controls -/

namespace Controls

theorem singleton_position_target
    (sourceHead : TypedTerm context source)
    (targetHead : TypedTerm context target)
    (headEvidence : TypedRelationEvidence relation sourceHead targetHead) :
    (canonicalLiftPositionEquiv target relation [sourceHead]
      ⟨[targetHead], .cons headEvidence .nil⟩ (0 : Fin 1)).1 =
        targetHead := by
  rfl

theorem empty_target_refused
    (sourceHead : TypedTerm context source) :
    IsEmpty (CanonicalMapRel (source := source) (target := target)
      relation [sourceHead] []) := by
  constructor
  intro evidence
  cases evidence

end Controls

#print axioms canonicalLiftEquiv
#print axioms canonicalLiftPositionEquiv
#print axioms canonicalLiftSemanticBundleEquiv
#print axioms canonicalLiftRegisteredPositionEquiv
#print axioms canonicalLiftRegisteredPositionEquiv_eq
#print axioms QualifiedLift.judgment_and_positionEvidence
#print axioms QualifiedLift.substitute
#print axioms Controls.singleton_position_target
#print axioms Controls.empty_target_refused

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveRegisteredListGuestLift
