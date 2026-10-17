import Mathlib.Logic.Encodable.Basic
import Mettapedia.GSLT.Logic.CircularPropositions
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedLabelledBisimulation

/-!
# Circular propositions as hypersets

Circular propositions over countable base facts are read as hypersets, faithfully, and their
grounded meaning is read as hypersets of the same universe.

**The reading.**  A circular proposition is a labelled graph: one transition to a terminal
state carrying its root connective, and one transition to each part carrying the root and
the position (`step`).  Labels are read as finite singleton chains of their codes, and a
transition as the Kuratowski pair of its label with its target, so the material reading of a
proposition (`material`) is the hyperset whose members are those pairs
(`mem_material`).  Equality of readings is labelled bisimilarity, and labelled
bisimilarity of propositions is equality in the final coalgebra, so the reading is
injective (`material_injective`).

**Shape.**  Base facts and the connectives applied to well-founded readings read as
well-founded hypersets (`material_base_wf`, `material_neg_wf`, `material_truth_wf`,
`material_conj_wf`, `material_disj_wf`); the self-negating proposition reads as a hyperset
on a membership cycle, not well-founded (`material_selfNegation_not_wf`).

**Meaning in the same universe.**  The truth set and the falsity set of grounded truth are
hypersets (`truthSet`, `falsitySet`) whose members are exactly the readings of the
propositions held and failed (`material_mem_truthSet_iff`, `material_mem_falsitySet_iff`).
The truth schema holds at the level of hypersets (`truthSchema`), no reading lies in both
sets (`not_mem_truthSet_and_falsitySet`), and the self-negating proposition lies in neither
(`selfNegation_outside`).  A circular proposition can be grounded: "the fact, or this
proposition" is held, so the truth set has a non-well-founded member and is itself not
well-founded (`Controls.truthSet_not_wf`).  Groundedness is a property of evidence, not of
the shape of what is true.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.KripkeTruth

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Proposition

universe v

/-! ## Labels -/

namespace Node

variable {Base : Type v}

/-- A root, as a base fact or one of four connectives. -/
def toSum : Node Base → Base ⊕ Fin 4
  | .base fact => .inl fact
  | .truth => .inr 0
  | .neg => .inr 1
  | .conj => .inr 2
  | .disj => .inr 3

/-- The root of a base fact or of one of four connectives. -/
def ofSum : Base ⊕ Fin 4 → Node Base
  | .inl fact => .base fact
  | .inr ⟨0, _⟩ => .truth
  | .inr ⟨1, _⟩ => .neg
  | .inr ⟨2, _⟩ => .conj
  | .inr ⟨_ + 3, _⟩ => .disj

/-- Roots are base facts or four connectives. -/
def equivSum : Node Base ≃ Base ⊕ Fin 4 where
  toFun := toSum
  invFun := ofSum
  left_inv node := by cases node <;> rfl
  right_inv sum := by
    rcases sum with fact | ⟨index, bound⟩
    · rfl
    · match index, bound with
      | 0, _ => rfl
      | 1, _ => rfl
      | 2, _ => rfl
      | 3, _ => rfl

instance [Encodable Base] : Encodable (Node Base) := Encodable.ofEquiv _ equivSum

/-- The position of a part, as a Boolean. -/
def partIndex : (node : Node Base) → node.Part → Bool
  | .base _, impossible => nomatch impossible
  | .truth, _ => false
  | .neg, _ => false
  | .conj, side => side
  | .disj, side => side

theorem partIndex_injective : ∀ node : Node Base, Function.Injective (partIndex node)
  | .base _ => fun impossible => nomatch impossible
  | .truth => fun _ _ _ => rfl
  | .neg => fun _ _ _ => rfl
  | .conj => fun _ _ same => same
  | .disj => fun _ _ same => same

end Node

/-- The label of a transition: the root, and either nothing (the root transition) or the
position of a part. -/
abbrev Label (Base : Type v) : Type v := Node Base × Option Bool

/-! ## The reading -/

section Reading

variable {Base : Type v}

/-- The labelled transitions out of a root with given parts: the root transition reaches
the terminal state, and each part is reached by its position. -/
def stepOf (node : Node Base) (children : node.Part → Proposition Base) :
    Label Base → Option (Proposition Base) → Prop
  | (labelNode, none), target => labelNode = node ∧ target = none
  | (labelNode, some index), target =>
      labelNode = node ∧ ∃ part : node.Part, Node.partIndex node part = index ∧
        target = some (children part)

/-- **The labelled transitions** of a circular proposition, with a terminal state. -/
def step : Option (Proposition Base) → Label Base → Option (Proposition Base) → Prop
  | none, _, _ => False
  | some p, label, target => stepOf (PFunctor.M.dest p).1 (PFunctor.M.dest p).2 label target

/-- The transitions of a proposition are those of its root and parts. -/
theorem step_some_eq {p : Proposition Base} {node : Node Base}
    {children : node.Part → Proposition Base}
    (decomposed : PFunctor.M.dest p = ⟨node, children⟩) :
    step (some p) = stepOf node children := by
  funext label target
  show stepOf (PFunctor.M.dest p).1 (PFunctor.M.dest p).2 label target = _
  rw [decomposed]

theorem chainValue_wf : ∀ n : ℕ, (OutcomeLabels.chainValue.{v} n).WF
  | 0 => HSet.wf_of_forall_mem fun _ member => absurd member (HSet.notMem_empty _)
  | n + 1 => (chainValue_wf n).singleton

theorem empty_wf : (∅ : HSet.{v}).WF :=
  HSet.wf_of_forall_mem fun _ member => absurd member (HSet.notMem_empty _)

variable [Encodable Base]

/-- Labels are read as finite singleton chains of their codes. -/
def reading (label : Label Base) : HSet.{v} :=
  OutcomeLabels.chainValue (Encodable.encode label)

theorem reading_injective : Function.Injective (reading (Base := Base)) :=
  fun _ _ same => Encodable.encode_injective (OutcomeLabels.chainValue_injective same)

/-- The supplied graphs of the labels. -/
def presented : HSet.PresentedLabels (reading (Base := Base)) where
  graph label := OutcomeLabels.chainGraph (Encodable.encode label)
  mk_graph _ := OutcomeLabels.mk_chainGraph _

/-- **The material reading** of a circular proposition. -/
def material (p : Proposition Base) : HSet.{v} :=
  presented.decorate step (some p)

/-- The terminal state reads as the empty set. -/
theorem terminal_eq_empty :
    presented.decorate step (none : Option (Proposition Base)) = ∅ := by
  apply HSet.ext
  intro y
  rw [presented.mem_decorate]
  constructor
  · rintro ⟨_, _, impossible, _⟩
    exact impossible.elim
  · intro member
    exact absurd member (HSet.notMem_empty y)

/-- **Members of a reading**: the pair of the root label with the empty set, and for each
part the pair of its label with the part's reading. -/
theorem mem_material {p : Proposition Base} {y : HSet.{v}} :
    y ∈ material p ↔
      y = HSet.kpair (reading ((PFunctor.M.dest p).1, none)) ∅ ∨
        ∃ part, y = HSet.kpair (reading ((PFunctor.M.dest p).1,
          some (Node.partIndex _ part))) (material ((PFunctor.M.dest p).2 part)) := by
  unfold material
  rw [presented.mem_decorate]
  constructor
  · rintro ⟨⟨node, index⟩, target, transition, rfl⟩
    cases index with
    | none =>
        obtain ⟨rfl, rfl⟩ := transition
        exact Or.inl (by rw [terminal_eq_empty])
    | some index =>
        obtain ⟨sameNode, part, sameIndex, rfl⟩ := transition
        subst sameNode
        subst sameIndex
        exact Or.inr ⟨part, rfl⟩
  · rintro (rfl | ⟨part, rfl⟩)
    · exact ⟨((PFunctor.M.dest p).1, none), none, ⟨rfl, rfl⟩, by rw [terminal_eq_empty]⟩
    · exact ⟨((PFunctor.M.dest p).1, some (Node.partIndex _ part)),
        some ((PFunctor.M.dest p).2 part), ⟨rfl, part, rfl, rfl⟩, rfl⟩

/-- **The reading is faithful**: equal readings are equal propositions. -/
theorem material_injective : Function.Injective (material (Base := Base)) := by
  intro p q same
  obtain ⟨R, bisimulation, related⟩ :=
    (presented.decorate_eq_iff_labelledBisimilar presented).mp same
  refine PFunctor.M.bisim (fun first second => R (some first) (some second)) ?_ p q related
  intro first second relatedPair
  obtain ⟨forth, _⟩ := bisimulation relatedPair
  rcases hFirstParts : PFunctor.M.dest first with ⟨node, children⟩
  rcases hSecondParts : PFunctor.M.dest second with ⟨node', children'⟩
  rw [step_some_eq hFirstParts, step_some_eq hSecondParts] at forth
  -- The root transitions carry equal labels, so the roots agree.
  obtain ⟨label, target, rootStep, labelsEqual, _⟩ :=
    forth (node, none) none ⟨rfl, rfl⟩
  have sameLabel := (reading_injective labelsEqual).symm
  subst sameLabel
  obtain ⟨sameRoot, _⟩ := rootStep
  subst sameRoot
  refine ⟨node, children, children', rfl, rfl, fun part => ?_⟩
  obtain ⟨label', target', partStep, partLabels, partRelated⟩ :=
    forth (node, some (Node.partIndex node part)) (some (children part)) ⟨rfl, part, rfl, rfl⟩
  have sameLabel' := (reading_injective partLabels).symm
  subst sameLabel'
  obtain ⟨_, part', indices, rfl⟩ := partStep
  have samePart : part' = part := Node.partIndex_injective node indices
  subst samePart
  exact partRelated

/-! ## Shape: well-founded and circular readings -/

theorem reading_wf (label : Label Base) : (reading label).WF := chainValue_wf _

/-- A reading is well-founded when the readings of its parts are. -/
theorem material_wf_of_parts {p : Proposition Base}
    (parts : ∀ part, (material ((PFunctor.M.dest p).2 part)).WF) : (material p).WF := by
  refine HSet.wf_of_forall_mem fun y member => ?_
  rcases mem_material.mp member with rfl | ⟨part, rfl⟩
  · exact (reading_wf _).kpair empty_wf
  · exact (reading_wf _).kpair (parts part)

theorem material_base_wf (fact : Base) : (material (base fact)).WF :=
  material_wf_of_parts fun impossible => nomatch impossible

theorem material_truth_wf {p : Proposition Base} (wf : (material p).WF) :
    (material (truth p)).WF :=
  material_wf_of_parts fun _ => wf

theorem material_neg_wf {p : Proposition Base} (wf : (material p).WF) :
    (material (neg p)).WF :=
  material_wf_of_parts fun _ => wf

theorem material_conj_wf {p q : Proposition Base} (left : (material p).WF)
    (right : (material q).WF) : (material (conj p q)).WF :=
  material_wf_of_parts fun side => by cases side <;> assumption

theorem material_disj_wf {p q : Proposition Base} (left : (material p).WF)
    (right : (material q).WF) : (material (disj p q)).WF :=
  material_wf_of_parts fun side => by cases side <;> assumption

/-- The reading of an argument lies two membership steps below the reading of its
negation. -/
theorem mem_mem_mem_material_neg (p : Proposition Base) :
    ∃ y z, y ∈ material (neg p) ∧ z ∈ y ∧ material p ∈ z := by
  refine ⟨HSet.kpair (reading ((.neg : Node Base), some false)) (material p),
    {reading ((.neg : Node Base), some false), material p}, ?_,
    HSet.mem_pair.mpr (Or.inr rfl), HSet.mem_pair.mpr (Or.inr rfl)⟩
  exact mem_material.mpr (Or.inr ⟨(), rfl⟩)

/-- **The self-negating proposition reads as a non-well-founded hyperset**: its reading lies
on a membership cycle of length three. -/
theorem material_selfNegation_not_wf : ¬ (material (selfNegation : Proposition Base)).WF := by
  obtain ⟨y, z, first, second, third⟩ := mem_mem_mem_material_neg (selfNegation : Proposition Base)
  rw [neg_selfNegation] at first
  exact HSet.not_wf_of_cycle first second third

/-- The reading of the second disjunct lies two membership steps below the reading of
the disjunction. -/
theorem mem_mem_mem_material_disj (p q : Proposition Base) :
    ∃ y z, y ∈ material (disj p q) ∧ z ∈ y ∧ material q ∈ z := by
  refine ⟨HSet.kpair (reading ((.disj : Node Base), some false)) (material q),
    {reading ((.disj : Node Base), some false), material q}, ?_,
    HSet.mem_pair.mpr (Or.inr rfl), HSet.mem_pair.mpr (Or.inr rfl)⟩
  exact mem_material.mpr (Or.inr ⟨false, rfl⟩)

end Reading

/-! ## Meaning in the same universe -/

section Meaning

variable {Base : Type v} [Encodable Base] (world : World Base)

/-- The graph that pictures the reading of a proposition. -/
def materialGraph (p : Proposition Base) : AccessiblePointedGraph.{v} :=
  AccessiblePointedGraph.generated (presented.edge step) (HSet.LabelCarrier.atom (some p))

theorem mk_materialGraph (p : Proposition Base) : HSet.mk (materialGraph p) = material p :=
  rfl

/-- **The truth set**: the hyperset of the readings of the propositions held by grounded
truth. -/
def truthSet : HSet.{v} :=
  HSet.range fun p : {p : Proposition Base // p ∈ (universal world).least.holds} =>
    materialGraph p.1

/-- **The falsity set**: the hyperset of the readings of the propositions failed by grounded
truth. -/
def falsitySet : HSet.{v} :=
  HSet.range fun p : {p : Proposition Base // p ∈ (universal world).least.fails} =>
    materialGraph p.1

theorem mem_truthSet {y : HSet.{v}} :
    y ∈ truthSet world ↔ ∃ p ∈ (universal world).least.holds, material p = y := by
  unfold truthSet
  rw [HSet.mem_range]
  exact ⟨fun ⟨⟨p, held⟩, same⟩ => ⟨p, held, same⟩, fun ⟨p, held, same⟩ => ⟨⟨p, held⟩, same⟩⟩

theorem mem_falsitySet {y : HSet.{v}} :
    y ∈ falsitySet world ↔ ∃ p ∈ (universal world).least.fails, material p = y := by
  unfold falsitySet
  rw [HSet.mem_range]
  exact ⟨fun ⟨⟨p, failed⟩, same⟩ => ⟨p, failed, same⟩, fun ⟨p, failed, same⟩ => ⟨⟨p, failed⟩, same⟩⟩

/-- **A reading is in the truth set exactly when its proposition is held.** -/
theorem material_mem_truthSet_iff {p : Proposition Base} :
    material p ∈ truthSet world ↔ p ∈ (universal world).least.holds := by
  rw [mem_truthSet]
  constructor
  · rintro ⟨q, held, same⟩
    rwa [← material_injective same]
  · exact fun held => ⟨p, held, rfl⟩

/-- **A reading is in the falsity set exactly when its proposition is failed.** -/
theorem material_mem_falsitySet_iff {p : Proposition Base} :
    material p ∈ falsitySet world ↔ p ∈ (universal world).least.fails := by
  rw [mem_falsitySet]
  constructor
  · rintro ⟨q, failed, same⟩
    rwa [← material_injective same]
  · exact fun failed => ⟨p, failed, rfl⟩

/-- **The truth schema, for hypersets**: the reading of "`p` is true" is in the truth set
exactly when the reading of `p` is. -/
theorem truthSchema (p : Proposition Base) :
    material (truth p) ∈ truthSet world ↔ material p ∈ truthSet world := by
  rw [material_mem_truthSet_iff, material_mem_truthSet_iff]
  exact mem_least_truth world p true

/-- **Negation exchanges the two sets.** -/
theorem negationSchema (p : Proposition Base) :
    material (neg p) ∈ truthSet world ↔ material p ∈ falsitySet world := by
  rw [material_mem_truthSet_iff, material_mem_falsitySet_iff]
  exact mem_least_neg world p true

/-- **No reading is in both sets.** -/
theorem not_mem_truthSet_and_falsitySet (p : Proposition Base) :
    ¬ (material p ∈ truthSet world ∧ material p ∈ falsitySet world) := by
  rw [material_mem_truthSet_iff, material_mem_falsitySet_iff]
  exact fun ⟨held, failed⟩ => (universal world).least_consistent p held failed

/-- **The self-negating proposition is in neither set.** -/
theorem selfNegation_outside :
    material (selfNegation : Proposition Base) ∉ truthSet world ∧
      material (selfNegation : Proposition Base) ∉ falsitySet world := by
  rw [material_mem_truthSet_iff, material_mem_falsitySet_iff]
  exact selfNegation_undetermined world

/-- **One hyperset universe for sentences and meaning.**  Circular propositions read
faithfully as hypersets; grounded truth and grounded falsity are two hypersets of the same
universe, satisfying the truth schema and the negation schema on readings, never sharing a
reading, and both omitting the self-negating proposition. -/
theorem hypersetUniverse :
    Function.Injective (material (Base := Base)) ∧
      (∀ p : Proposition Base,
        material (truth p) ∈ truthSet world ↔ material p ∈ truthSet world) ∧
      (∀ p : Proposition Base,
        material (neg p) ∈ truthSet world ↔ material p ∈ falsitySet world) ∧
      (∀ p : Proposition Base,
        ¬ (material p ∈ truthSet world ∧ material p ∈ falsitySet world)) ∧
      (material (selfNegation : Proposition Base) ∉ truthSet world ∧
        material (selfNegation : Proposition Base) ∉ falsitySet world) ∧
      ¬ (material (selfNegation : Proposition Base)).WF :=
  ⟨material_injective, truthSchema world, negationSchema world,
    not_mem_truthSet_and_falsitySet world, selfNegation_outside world,
    material_selfNegation_not_wf⟩

end Meaning

/-! ## Controls -/

namespace Controls

/-- One true base fact. -/
def trueWorld : World Unit := ⟨fun _ => True, fun _ => False, fun _ _ failed => failed⟩

/-- The true fact is in the truth set and not in the falsity set. -/
theorem base_mem_truthSet :
    material (base ()) ∈ truthSet trueWorld ∧ material (base ()) ∉ falsitySet trueWorld := by
  rw [material_mem_truthSet_iff, material_mem_falsitySet_iff]
  refine ⟨?_, ?_⟩
  · change (universal trueWorld).least.Mem (base ()) true
    rw [(universal trueWorld).mem_least_iff, universal_spec, spec_base]
    exact trivial
  · intro failed
    have failedSpec := ((universal trueWorld).mem_least_iff
      (judgment := base ()) (polarity := false)).mp failed
    rw [universal_spec, spec_base] at failedSpec
    exact failedSpec

/-- "The fact, or this proposition" is held. -/
theorem orSelf_mem_truthSet : material (orSelf (base ())) ∈ truthSet trueWorld :=
  (material_mem_truthSet_iff trueWorld).mpr
    (orSelf_held trueWorld ((material_mem_truthSet_iff trueWorld).mp base_mem_truthSet.1))

/-- Its reading is not well-founded: it contains itself two steps down. -/
theorem material_orSelf_not_wf : ¬ (material (orSelf (base ()) : Proposition Unit)).WF := by
  obtain ⟨y, z, first, second, third⟩ :=
    mem_mem_mem_material_disj (base ()) (orSelf (base ()) : Proposition Unit)
  rw [← orSelf_eq] at first
  exact HSet.not_wf_of_cycle first second third

/-- **The truth set is not well-founded**: something circular is true. -/
theorem truthSet_not_wf : ¬ (truthSet trueWorld).WF :=
  HSet.not_wf_of_mem orSelf_mem_truthSet material_orSelf_not_wf

/-- The true fact reads as a well-founded hyperset. -/
theorem base_wf : (material (base () : Proposition Unit)).WF := material_base_wf ()

end Controls

#print axioms material_injective
#print axioms material_selfNegation_not_wf
#print axioms material_mem_truthSet_iff
#print axioms truthSchema
#print axioms negationSchema
#print axioms not_mem_truthSet_and_falsitySet
#print axioms selfNegation_outside
#print axioms Controls.base_mem_truthSet
#print axioms Controls.truthSet_not_wf
#print axioms hypersetUniverse

end Mettapedia.GSLT.KripkeTruth
