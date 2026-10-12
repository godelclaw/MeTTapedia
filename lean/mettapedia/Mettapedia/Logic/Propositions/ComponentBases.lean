import Mettapedia.Logic.Propositions.InformationStates
import Mettapedia.Logic.Propositions.Totality

/-!
# Component-preserving epistemic bases

A base can retain separately named physical, phenomenal and indexical
sentence sets.  Their joined base uses ordinary set union; componentwise
refinement preserves which component supplied each statement.  Joining loses
that provenance and therefore cannot reflect componentwise refinement.

Interpretations, scrutability and information-state revision are the existing
ones.  The decomposition asserts neither that its components exhaust a
language nor that their truths determine all other truths.  In particular,
these laws do not assume or prove global PQI adequacy or a physical realization
of the represented phenomenal descriptions.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Propositions

universe u uS uW uD uN uP

inductive BaseComponent where
  | physical
  | phenomenal
  | indexical
  deriving DecidableEq

/-- Named statement sets, without an automatic exhaustiveness, disjointness,
consistency or scrutability claim. -/
structure ComponentBases (Statement : Type u) where
  physical : Set Statement
  phenomenal : Set Statement
  indexical : Set Statement

namespace ComponentBases

variable {Statement : Type u}

def component (bases : ComponentBases Statement) : BaseComponent -> Set Statement
  | .physical => bases.physical
  | .phenomenal => bases.phenomenal
  | .indexical => bases.indexical

def joined (bases : ComponentBases Statement) : Set Statement :=
  bases.physical ∪ bases.phenomenal ∪ bases.indexical

/-- Refinement retains component identity as well as statement inclusion. -/
def Refines (first second : ComponentBases Statement) : Prop :=
  forall kind, first.component kind ⊆ second.component kind

/-- Combine information without forgetting its named component. -/
def union (first second : ComponentBases Statement) : ComponentBases Statement where
  physical := first.physical ∪ second.physical
  phenomenal := first.phenomenal ∪ second.phenomenal
  indexical := first.indexical ∪ second.indexical

/-- Select statements while retaining their component provenance. -/
def filter (bases : ComponentBases Statement) (admitted : Statement -> Prop) :
    ComponentBases Statement where
  physical := {statement | statement ∈ bases.physical /\ admitted statement}
  phenomenal := {statement | statement ∈ bases.phenomenal /\ admitted statement}
  indexical := {statement | statement ∈ bases.indexical /\ admitted statement}

theorem component_subset_joined (bases : ComponentBases Statement)
    (kind : BaseComponent) : bases.component kind ⊆ bases.joined := by
  intro statement member
  cases kind with
  | physical => exact Or.inl (Or.inl member)
  | phenomenal => exact Or.inl (Or.inr member)
  | indexical => exact Or.inr member

theorem mem_joined_iff (bases : ComponentBases Statement) (statement : Statement) :
    statement ∈ bases.joined ↔ exists kind, statement ∈ bases.component kind := by
  constructor
  · rintro ((physical | phenomenal) | indexical)
    · exact ⟨.physical, physical⟩
    · exact ⟨.phenomenal, phenomenal⟩
    · exact ⟨.indexical, indexical⟩
  · rintro ⟨kind, member⟩
    exact component_subset_joined bases kind member

theorem Refines.refl (bases : ComponentBases Statement) : bases.Refines bases :=
  fun _ => Set.Subset.refl _

theorem Refines.trans {first second third : ComponentBases Statement}
    (left : first.Refines second) (right : second.Refines third) : first.Refines third :=
  fun kind => (left kind).trans (right kind)

/-- Componentwise refinement entails refinement after joining.  The converse
is not licensed by this implication. -/
theorem joined_monotone {first second : ComponentBases Statement}
    (refines : first.Refines second) : first.joined ⊆ second.joined := by
  intro statement member
  rcases (mem_joined_iff first statement).1 member with ⟨kind, inComponent⟩
  exact component_subset_joined second kind (refines kind inComponent)

theorem joined_union (first second : ComponentBases Statement) :
    (first.union second).joined = first.joined ∪ second.joined := by
  ext statement
  simp only [joined, union, Set.mem_union]
  tauto

theorem filter_refines (bases : ComponentBases Statement) (admitted : Statement -> Prop) :
    (bases.filter admitted).Refines bases := by
  intro kind statement member
  cases kind <;> exact member.1

theorem joined_filter (bases : ComponentBases Statement) (admitted : Statement -> Prop) :
    (bases.filter admitted).joined = {statement | statement ∈ bases.joined /\ admitted statement} := by
  ext statement
  simp only [joined, filter, Set.mem_union, Set.mem_ofPred_eq]
  tauto

/-- Agreement on the joined base is exactly agreement on each named
component.  This preserves distinctions between the questions being asked. -/
theorem agreement_joined_iff (bases : ComponentBases Statement)
    (first second : Statement -> Prop) :
    (∀ statement ∈ bases.joined, first statement ↔ second statement) ↔
      forall kind, ∀ statement ∈ bases.component kind,
        first statement ↔ second statement := by
  constructor
  · intro agrees kind statement member
    exact agrees statement (component_subset_joined bases kind member)
  · intro agrees statement member
    rcases (mem_joined_iff bases statement).1 member with ⟨kind, inComponent⟩
    exact agrees kind statement inComponent

end ComponentBases

namespace Interpretation

variable {S : Type uS} {W : Type uW} {D : Type uD} {N : Type uN} {P : Type uP}
variable (I : Interpretation S W D N P)

/-- Accepting the joined base intersects the component information states. -/
theorem stateOf_component_join (bases : ComponentBases (Sentence N P)) :
    I.stateOf bases.joined =
      I.stateOf bases.physical ∩ I.stateOf bases.phenomenal ∩ I.stateOf bases.indexical := by
  change I.stateOf ((bases.physical ∪ bases.phenomenal) ∪ bases.indexical) = _
  rw [I.stateOf_union, I.stateOf_union]
  rfl

/-- More accepted statements leave fewer compatible scenarios. -/
theorem stateOf_component_refinement {first second : ComponentBases (Sentence N P)}
    (refines : first.Refines second) : I.stateOf second.joined ⊆ I.stateOf first.joined := by
  intro scenario verifies statement member
  exact verifies statement (ComponentBases.joined_monotone refines member)

theorem scrutableFrom_component {bases : ComponentBases (Sentence N P)}
    (kind : BaseComponent) {sentence : Sentence N P}
    (scrutable : I.ScrutableFrom (bases.component kind) sentence) :
    I.ScrutableFrom bases.joined sentence :=
  Interpretation.ScrutableFrom.mono I scrutable
    (ComponentBases.component_subset_joined bases kind)

/-- Selecting the truths of each component and joining commutes with
selecting truths from their union.  It does not settle omitted truths. -/
theorem truthsIn_component_join (actual : S) (bases : ComponentBases (Sentence N P)) :
    I.truthsIn actual bases.joined = (bases.filter (I.TrueIn actual)).joined :=
  (ComponentBases.joined_filter bases (I.TrueIn actual)).symm

end Interpretation

/-! ## Loss of component provenance -/

namespace ComponentBaseControls

def separated : ComponentBases (Fin 3) where
  physical := {0}
  phenomenal := {1}
  indexical := {2}

def exchanged : ComponentBases (Fin 3) where
  physical := {1}
  phenomenal := {0}
  indexical := {2}

theorem all_components_inhabited :
    separated.physical.Nonempty /\ separated.phenomenal.Nonempty /\
      separated.indexical.Nonempty := by
  exact ⟨⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩⟩

/-- Joining can suppress a real exchange of physical and phenomenal labels. -/
theorem same_joined_different_components : separated.joined = exchanged.joined := by
  ext statement
  simp only [ComponentBases.joined, separated, exchanged, Set.mem_union,
    Set.mem_singleton_iff]
  tauto

theorem joined_agreement_does_not_reflect_refinement :
    separated.joined = exchanged.joined /\ ¬ separated.Refines exchanged := by
  refine ⟨same_joined_different_components, ?_⟩
  intro refines
  have member : (0 : Fin 3) ∈ exchanged.physical := refines .physical rfl
  simp [exchanged] at member

end ComponentBaseControls

end Mettapedia.Logic.Propositions

#print axioms Mettapedia.Logic.Propositions.ComponentBases.joined_monotone
#print axioms Mettapedia.Logic.Propositions.Interpretation.stateOf_component_join
#print axioms Mettapedia.Logic.Propositions.ComponentBaseControls.joined_agreement_does_not_reflect_refinement
