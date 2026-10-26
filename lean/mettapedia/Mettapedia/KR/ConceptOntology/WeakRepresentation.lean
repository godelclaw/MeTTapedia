import Mettapedia.KR.ConceptOntology.FCA

/-!
# Distinction-Preserving Representation Layer

Objects and attributes with identical complete evidence profiles may be
identified. Closed evidence concepts respect these identifications automatically;
the crisp concept lattices before and after identification are order isomorphic.
Images compress a closed concept, and preimages recover its extent and intent.
Thus all meets and joins are preserved, without a finiteness assumption.

The quotient is relative to the supplied membership matrix. Arbitrary labels
need not descend, agreement at one gate need not imply evidence equivalence,
and a later revision may split formerly indistinguishable profiles.
-/

namespace Mettapedia.KR.ConceptOntology

open Mettapedia.Algebra.QuantaleWeakness

universe u v w

variable {Obj : Type u} {Con : Type v} {Q : Type w}
variable (M : Obj → Con → Q)

/-- Objects are indistinguishable when they have the same membership-evidence
profile across all concepts. -/
def ObjectIndistinguishable (x y : Obj) : Prop :=
  ∀ c, M x c = M y c

/-- Concepts are indistinguishable when they present the same membership
evidence across all objects. -/
def ConceptIndistinguishable (c d : Con) : Prop :=
  ∀ x, M x c = M x d

def objectSetoid : Setoid Obj where
  r := ObjectIndistinguishable M
  iseqv := ⟨fun _ _ => rfl, fun h c => (h c).symm,
    fun h₁ h₂ c => (h₁ c).trans (h₂ c)⟩

def conceptSetoid : Setoid Con where
  r := ConceptIndistinguishable M
  iseqv := ⟨fun _ _ => rfl, fun h x => (h x).symm,
    fun h₁ h₂ x => (h₁ x).trans (h₂ x)⟩

/-- Membership evidence factors through the quotient by object and concept
indistinguishability. -/
noncomputable def factoredMemberEvidence :
    Quotient (objectSetoid M) → Quotient (conceptSetoid M) → Q :=
  Quotient.lift₂ M <| by
    intro x c y d hxy hcd
    calc
      M x c = M y c := hxy c
      _ = M y d := hcd y

@[simp] theorem factoredMemberEvidence_mk
    (x : Obj) (c : Con) :
    factoredMemberEvidence M ⟦x⟧ ⟦c⟧ = M x c := rfl

/-- An object-indexed predicate respects the indistinguishability classes induced
by the membership relation. -/
def ObjectPredicateInvariant (E : Obj → Q) : Prop :=
  ∀ ⦃x y : Obj⦄, ObjectIndistinguishable M x y → E x = E y

/-- A concept-indexed predicate respects the indistinguishability classes induced
by the membership relation. -/
def ConceptPredicateInvariant (I : Con → Q) : Prop :=
  ∀ ⦃c d : Con⦄, ConceptIndistinguishable M c d → I c = I d

/-- Invariant object-predicates factor through the object quotient. -/
noncomputable def factoredObjectPredicate
    (E : Obj → Q) (hE : ObjectPredicateInvariant M E) :
    Quotient (objectSetoid M) → Q :=
  Quotient.lift E (fun _ _ hxy => hE hxy)

/-- Invariant concept-predicates factor through the concept quotient. -/
noncomputable def factoredConceptPredicate
    (I : Con → Q) (hI : ConceptPredicateInvariant M I) :
    Quotient (conceptSetoid M) → Q :=
  Quotient.lift I (fun _ _ hcd => hI hcd)

@[simp] theorem factoredObjectPredicate_mk
    (E : Obj → Q) (hE : ObjectPredicateInvariant M E) (x : Obj) :
    factoredObjectPredicate M E hE ⟦x⟧ = E x := rfl

@[simp] theorem factoredConceptPredicate_mk
    (I : Con → Q) (hI : ConceptPredicateInvariant M I) (c : Con) :
    factoredConceptPredicate M I hI ⟦c⟧ = I c := rfl

section QuantaleFactorization

variable [CommSemigroup Q] [CompleteLattice Q]

theorem upperAdjoint_factored_mk
    (extent : Obj → Q) (hExtent : ObjectPredicateInvariant M extent)
    (c : Con) :
    upperAdjoint (factoredMemberEvidence M)
        (factoredObjectPredicate M extent hExtent) ⟦c⟧ =
      upperAdjoint M extent c := by
  exact (Quotient.mk_surjective.iInf_comp _).symm

theorem lowerAdjoint_factored_mk
    (intent : Con → Q) (hIntent : ConceptPredicateInvariant M intent)
    (x : Obj) :
    lowerAdjoint (factoredMemberEvidence M)
        (factoredConceptPredicate M intent hIntent) ⟦x⟧ =
      lowerAdjoint M intent x := by
  exact (Quotient.mk_surjective.iInf_comp _).symm

/-- Closed evidence extents are constant on complete membership profiles. -/
theorem EvidenceConcept.extent_invariant (A : EvidenceConcept M) :
    ObjectPredicateInvariant M A.extent := by
  intro x y hxy
  rw [← A.lower_intent]
  exact iInf_congr fun c => congrArg (quantaleImplies (A.intent c)) (hxy c)

/-- Closed evidence intents are constant on complete membership profiles. -/
theorem EvidenceConcept.intent_invariant (A : EvidenceConcept M) :
    ConceptPredicateInvariant M A.intent := by
  intro c d hcd
  rw [← A.upper_extent]
  exact iInf_congr fun x => congrArg (quantaleImplies (A.extent x)) (hcd x)

/-- Quotient a closed evidence concept; invariance follows from closedness. -/
noncomputable def EvidenceConcept.factor
    (A : EvidenceConcept M) :
    EvidenceConcept (factoredMemberEvidence M) where
  extent := factoredObjectPredicate M A.extent (A.extent_invariant M)
  intent := factoredConceptPredicate M A.intent (A.intent_invariant M)
  upper_extent := funext <| Quotient.ind fun c => by
    simpa only [upperAdjoint_factored_mk, factoredConceptPredicate_mk] using congrFun A.upper_extent c
  lower_intent := funext <| Quotient.ind fun x => by
    simpa only [lowerAdjoint_factored_mk, factoredObjectPredicate_mk] using congrFun A.lower_intent x

@[simp] theorem EvidenceConcept_factor_extent_mk
    (A : EvidenceConcept M) (x : Obj) :
    (A.factor M).extent ⟦x⟧ = A.extent x := rfl

@[simp] theorem EvidenceConcept_factor_intent_mk
    (A : EvidenceConcept M) (c : Con) :
    (A.factor M).intent ⟦c⟧ = A.intent c := rfl

end QuantaleFactorization

section CrispInvariance

variable [Preorder Q]
variable (G : EvidenceGate Q) (M : Obj → Con → Q)

theorem crispRelation_congr_left
    {x y : Obj} (hxy : ObjectIndistinguishable M x y) (c : Con) :
    crispRelation G M x c ↔ crispRelation G M y c := by
  simp [crispRelation, hxy c]

theorem crispRelation_congr_right
    {c d : Con} (hcd : ConceptIndistinguishable M c d) (x : Obj) :
    crispRelation G M x c ↔ crispRelation G M x d := by
  simp [crispRelation, hcd x]

theorem crispExtent_eq_of_conceptIndistinguishable
    {c d : Con} (hcd : ConceptIndistinguishable M c d) :
    crispExtent G M c = crispExtent G M d := by
  ext x
  simp [mem_crispExtent_iff, hcd x]

theorem crispIntent_eq_of_objectIndistinguishable
    {x y : Obj} (hxy : ObjectIndistinguishable M x y) :
    crispIntent G M x = crispIntent G M y := by
  ext c
  simp [mem_crispIntent_iff, hxy c]

theorem crispExtensionalInherits_congr_left
    {c c' d : Con} (hcc' : ConceptIndistinguishable M c c') :
    crispExtensionalInherits G M c d ↔ crispExtensionalInherits G M c' d := by
  simp [crispExtensionalInherits, crispExtent_eq_of_conceptIndistinguishable (G := G) (M := M) hcc']

theorem crispExtensionalInherits_congr_right
    {c d d' : Con} (hdd' : ConceptIndistinguishable M d d') :
    crispExtensionalInherits G M c d ↔ crispExtensionalInherits G M c d' := by
  simp [crispExtensionalInherits, crispExtent_eq_of_conceptIndistinguishable (G := G) (M := M) hdd']

theorem crispExtensionalInherits_congr
    {c c' d d' : Con}
    (hcc' : ConceptIndistinguishable M c c')
    (hdd' : ConceptIndistinguishable M d d') :
    crispExtensionalInherits G M c d ↔ crispExtensionalInherits G M c' d' := by
  rw [crispExtensionalInherits_congr_left (G := G) (M := M) hcc']
  rw [crispExtensionalInherits_congr_right (G := G) (M := M) hdd']

theorem factoredCrispRelation_mk
    (x : Obj) (c : Con) :
    crispRelation G (factoredMemberEvidence M) ⟦x⟧ ⟦c⟧ ↔ crispRelation G M x c := by
  simp [crispRelation, factoredMemberEvidence]

theorem factoredCrispExtensionalInherits_mk_iff
    (c d : Con) :
    crispExtensionalInherits G (factoredMemberEvidence M) ⟦c⟧ ⟦d⟧
      ↔ crispExtensionalInherits G M c d := by
  rw [crispExtensionalInherits_iff, crispExtensionalInherits_iff]
  exact Quotient.forall

/-- Send a closed concept to the images of its extent and intent. -/
noncomputable def crispConceptFactor (A : CrispConcept G M) :
    CrispConcept G (factoredMemberEvidence M) where
  extent := Quotient.mk (objectSetoid M) '' A.extent
  intent := Quotient.mk (conceptSetoid M) '' A.intent
  upperPolar_extent := by
    ext qc
    refine Quotient.inductionOn qc fun c => ?_
    simp only [upperPolar, Set.mem_ofPred_eq, Set.forall_mem_image]
    constructor
    · intro h
      exact ⟨c, A.upperPolar_extent ▸ h, rfl⟩
    · rintro ⟨d, hd, hdc⟩ x hx
      rw [← hdc]
      exact A.rel_extent_intent hx hd
  lowerPolar_intent := by
    ext qx
    refine Quotient.inductionOn qx fun x => ?_
    simp only [lowerPolar, Set.mem_ofPred_eq, Set.forall_mem_image]
    constructor
    · intro h
      exact ⟨x, A.lowerPolar_intent ▸ h, rfl⟩
    · rintro ⟨y, hy, hyx⟩ c hc
      rw [← hyx]
      exact A.rel_extent_intent hy hc

/-- Pull a quotient concept back along the representative maps. -/
noncomputable def crispConceptPullback (B : CrispConcept G (factoredMemberEvidence M)) :
    CrispConcept G M where
  extent := Quotient.mk (objectSetoid M) ⁻¹' B.extent
  intent := Quotient.mk (conceptSetoid M) ⁻¹' B.intent
  upperPolar_extent := by
    ext c
    rw [← B.upperPolar_extent]
    simp only [upperPolar, Set.mem_ofPred_eq, Set.mem_preimage,
      Quotient.forall, factoredCrispRelation_mk]
  lowerPolar_intent := by
    ext x
    rw [← B.lowerPolar_intent]
    simp only [lowerPolar, Set.mem_ofPred_eq, Set.mem_preimage,
      Quotient.forall, factoredCrispRelation_mk]

/-- Closed concepts are saturated: quotienting forgets no extent membership. -/
@[simp] theorem crispConceptFactor_preimage_extent (A : CrispConcept G M) :
    Quotient.mk (objectSetoid M) ⁻¹' (crispConceptFactor G M A).extent = A.extent := by
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [← A.lowerPolar_intent]
    intro c hc
    exact (crispRelation_congr_left G M (Quotient.exact hyx) c).mp (A.rel_extent_intent hy hc)
  · intro hx; exact ⟨x, hx, rfl⟩

@[simp] theorem crispConceptFactor_preimage_intent (A : CrispConcept G M) :
    Quotient.mk (conceptSetoid M) ⁻¹' (crispConceptFactor G M A).intent = A.intent := by
  ext c
  constructor
  · rintro ⟨d, hd, hdc⟩
    rw [← A.upperPolar_extent]
    intro x hx
    exact (crispRelation_congr_right G M (Quotient.exact hdc) x).mp (A.rel_extent_intent hx hd)
  · intro hc; exact ⟨c, hc, rfl⟩

/-- Removing duplicate evidence rows and columns preserves the entire concept lattice.
The forward map uses images, the inverse uses preimages; no finiteness is required. -/
@[simps! apply_extent apply_intent symm_apply_extent symm_apply_intent]
noncomputable def crispConceptQuotientOrderIso :
    CrispConcept G M ≃o CrispConcept G (factoredMemberEvidence M) where
  toFun := crispConceptFactor G M
  invFun := crispConceptPullback G M
  left_inv A := Concept.ext (crispConceptFactor_preimage_extent G M A)
  right_inv B := Concept.ext (Set.image_preimage_eq _ Quotient.mk_surjective)
  map_rel_iff' := by
    intro A B
    change (_ '' A.extent ⊆ _ '' B.extent) ↔ A.extent ⊆ B.extent
    constructor
    · intro h x hx
      have := h (Set.mem_image_of_mem _ hx)
      exact (Set.ext_iff.mp (crispConceptFactor_preimage_extent G M B) x).mp this
    · exact Set.image_mono

end CrispInvariance


end Mettapedia.KR.ConceptOntology
