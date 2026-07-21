import Mettapedia.GraphTheory.FourColor.ClassicalCertificateContractColorSearch

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateExactTraceEnumeration

open ClassicalCertificateContractColorSearch
open ClassicalCertificateContractComponents
open ClassicalCertificateFacePartition
open ClassicalCertificateHypermapColoring
open ClassicalCertificateTraceTree
open ClassicalCertificateTraceWitness

namespace TraceTree

/-- A trace trie is uniform at depth `length` when all of its accepted words
have exactly that length. -/
def Uniform : Nat → ClassicalCertificateTraceTree.TraceTree → Prop
  | _, .empty => True
  | 0, .leaf => True
  | length + 1, .node red blue purple =>
      Uniform length red ∧ Uniform length blue ∧ Uniform length purple
  | _, _ => False

/-- Structural union of two uniform trace tries. -/
def union : ClassicalCertificateTraceTree.TraceTree →
    ClassicalCertificateTraceTree.TraceTree →
      ClassicalCertificateTraceTree.TraceTree
  | .empty, right => right
  | left, .empty => left
  | .leaf, _ => .leaf
  | _, .leaf => .leaf
  | .node leftRed leftBlue leftPurple,
      .node rightRed rightBlue rightPurple =>
    .node (union leftRed rightRed) (union leftBlue rightBlue)
      (union leftPurple rightPurple)

/-- Structural inclusion test for two exact trace tries. -/
def subset : ClassicalCertificateTraceTree.TraceTree →
    ClassicalCertificateTraceTree.TraceTree → Bool
  | .empty, _ => true
  | .leaf, .leaf => true
  | .node leftRed leftBlue leftPurple,
      .node rightRed rightBlue rightPurple =>
    subset leftRed rightRed && subset leftBlue rightBlue &&
      subset leftPurple rightPurple
  | _, _ => false

theorem accepts_of_subset : ∀
    (left right : ClassicalCertificateTraceTree.TraceTree),
    subset left right = true → ∀ word,
      left.accepts word = true → right.accepts word = true
  | .empty, _, _, word, haccepts => by
      simp [ClassicalCertificateTraceTree.TraceTree.accepts] at haccepts
  | .leaf, .empty, hsubset, _, _ => by simp [subset] at hsubset
  | .leaf, .leaf, _, word, haccepts => by
      simpa [ClassicalCertificateTraceTree.TraceTree.accepts] using haccepts
  | .leaf, .node _ _ _, hsubset, _, _ => by simp [subset] at hsubset
  | .node _ _ _, .empty, hsubset, _, _ => by simp [subset] at hsubset
  | .node _ _ _, .leaf, hsubset, _, _ => by simp [subset] at hsubset
  | .node leftRed leftBlue leftPurple,
      .node rightRed rightBlue rightPurple, hsubset, word, haccepts => by
      simp only [subset, Bool.and_eq_true] at hsubset
      rcases hsubset with ⟨⟨hred, hblue⟩, hpurple⟩
      cases word with
      | nil =>
          simp [ClassicalCertificateTraceTree.TraceTree.accepts] at haccepts
      | cons symbol rest =>
          cases symbol with
          | red =>
              exact accepts_of_subset leftRed rightRed hred rest (by
                simpa [ClassicalCertificateTraceTree.TraceTree.accepts,
                  ClassicalCertificateTraceTree.TraceTree.child]
                    using haccepts)
          | blue =>
              exact accepts_of_subset leftBlue rightBlue hblue rest (by
                simpa [ClassicalCertificateTraceTree.TraceTree.accepts,
                  ClassicalCertificateTraceTree.TraceTree.child]
                    using haccepts)
          | purple =>
              exact accepts_of_subset leftPurple rightPurple hpurple rest (by
                simpa [ClassicalCertificateTraceTree.TraceTree.accepts,
                  ClassicalCertificateTraceTree.TraceTree.child]
                    using haccepts)

theorem uniform_singleton (word : List TraceSymbol) :
    Uniform word.length (ClassicalCertificateTraceTree.TraceTree.singleton word) := by
  induction word with
  | nil => simp [Uniform, ClassicalCertificateTraceTree.TraceTree.singleton]
  | cons symbol rest ih =>
      cases symbol <;>
        simp [Uniform, ClassicalCertificateTraceTree.TraceTree.singleton, ih]

theorem uniform_union {length : Nat}
    {left right : ClassicalCertificateTraceTree.TraceTree}
    (hleft : Uniform length left) (hright : Uniform length right) :
    Uniform length (union left right) := by
  induction length generalizing left right with
  | zero =>
      cases left <;> cases right <;> simp_all [Uniform, union]
  | succ length ih =>
      cases left <;> cases right <;>
        simp_all [Uniform, union]

theorem accepts_union_iff {length : Nat}
    {left right : ClassicalCertificateTraceTree.TraceTree}
    (hleft : Uniform length left) (hright : Uniform length right)
    (word : List TraceSymbol) (hword : word.length = length) :
    (union left right).accepts word = true ↔
      left.accepts word = true ∨ right.accepts word = true := by
  induction length generalizing left right word with
  | zero =>
      cases word with
      | nil =>
          cases left <;> cases right <;>
            simp_all [Uniform, union,
              ClassicalCertificateTraceTree.TraceTree.accepts]
      | cons => simp at hword
  | succ length ih =>
      cases word with
      | nil => simp at hword
      | cons symbol rest =>
          have hrest : rest.length = length := by simpa using hword
          cases symbol <;> cases left <;> cases right <;>
            simp_all [Uniform, union,
              ClassicalCertificateTraceTree.TraceTree.accepts,
              ClassicalCertificateTraceTree.TraceTree.child]

theorem length_eq_of_uniform_accepts {length : Nat}
    {tree : ClassicalCertificateTraceTree.TraceTree}
    (huniform : Uniform length tree) (word : List TraceSymbol)
    (haccepts : tree.accepts word = true) :
    word.length = length := by
  induction length generalizing tree word with
  | zero =>
      cases tree <;> cases word <;>
        simp_all [Uniform,
          ClassicalCertificateTraceTree.TraceTree.accepts]
  | succ length ih =>
      cases tree with
      | empty =>
          simp [ClassicalCertificateTraceTree.TraceTree.accepts] at haccepts
      | leaf => simp [Uniform] at huniform
      | node red blue purple =>
          cases word with
          | nil =>
              simp [ClassicalCertificateTraceTree.TraceTree.accepts] at haccepts
          | cons symbol rest =>
              simp only [Uniform] at huniform
              cases symbol with
              | red =>
                  have hrest := ih huniform.1 rest (by
                    simpa [ClassicalCertificateTraceTree.TraceTree.accepts,
                      ClassicalCertificateTraceTree.TraceTree.child]
                        using haccepts)
                  simpa using hrest
              | blue =>
                  have hrest := ih huniform.2.1 rest (by
                    simpa [ClassicalCertificateTraceTree.TraceTree.accepts,
                      ClassicalCertificateTraceTree.TraceTree.child]
                        using haccepts)
                  simpa using hrest
              | purple =>
                  have hrest := ih huniform.2.2 rest (by
                    simpa [ClassicalCertificateTraceTree.TraceTree.accepts,
                      ClassicalCertificateTraceTree.TraceTree.child]
                        using haccepts)
                  simpa using hrest

end TraceTree

variable {hypermap : ClassicalCertificateConfiguration.HypermapCode}
  {partition : ClassicalCertificateFacePartition.Code}
  {partitionValid : ClassicalCertificateFacePartition.Valid hypermap partition}
  {contract : Finset (Fin hypermap.dartCount)}
  {components : ClassicalCertificateContractComponents.Code}

theorem symbolTraceOfAssignment_length
    (ring : List (Fin hypermap.dartCount))
    (assignment : Fin partition.faceCount → Color) :
    (symbolTraceOfAssignment partitionValid ring assignment).length =
      ring.length := by
  simp [symbolTraceOfAssignment, ringTraceOfAssignment,
    ClassicalCertificateColorTrace.length_trace,
    ClassicalCertificateHypermapColoring.FiniteHypermap.ringColorWord]

/-- Exhaustively enumerate the boundary traces of all component colorings,
pruning a branch as soon as a fully assigned edge violates the contract. -/
def enumerateAux
    (componentsValid : ClassicalCertificateContractComponents.Valid
      partitionValid contract components)
    (ring : List (Fin hypermap.dartCount))
    (assigned : List (AssignedColor components.componentCount)) :
    List (Fin components.componentCount) →
      ClassicalCertificateTraceTree.TraceTree
  | [] =>
      if PartialViolation componentsValid assigned then .empty
      else
        .singleton
          (symbolTraceOfAssignment partitionValid ring
            (liftAssignment componentsValid
              (assignmentOfAssigned assigned)))
  | component :: remaining =>
      if PartialViolation componentsValid assigned then .empty
      else
        TraceTree.union
          (enumerateAux componentsValid ring
            ((component, .zero) :: assigned) remaining)
          (TraceTree.union
            (enumerateAux componentsValid ring
              ((component, .red) :: assigned) remaining)
            (TraceTree.union
              (enumerateAux componentsValid ring
                ((component, .blue) :: assigned) remaining)
              (enumerateAux componentsValid ring
                ((component, .purple) :: assigned) remaining)))

def enumerate
    (componentsValid : ClassicalCertificateContractComponents.Valid
      partitionValid contract components)
    (ring : List (Fin hypermap.dartCount))
    (order : List (Fin components.componentCount)) :
    ClassicalCertificateTraceTree.TraceTree :=
  enumerateAux componentsValid ring [] order

theorem enumerateAux_uniform
    (componentsValid : ClassicalCertificateContractComponents.Valid
      partitionValid contract components)
    (ring : List (Fin hypermap.dartCount))
    (assigned : List (AssignedColor components.componentCount))
    (remaining : List (Fin components.componentCount)) :
    TraceTree.Uniform ring.length
      (enumerateAux componentsValid ring assigned remaining) := by
  induction remaining generalizing assigned with
  | nil =>
      by_cases hviolation : PartialViolation componentsValid assigned
      · simp [enumerateAux, hviolation, TraceTree.Uniform]
      · simp only [enumerateAux, hviolation, ↓reduceIte]
        rw [← symbolTraceOfAssignment_length ring
          (liftAssignment componentsValid (assignmentOfAssigned assigned))]
        exact TraceTree.uniform_singleton _
  | cons component remaining ih =>
      by_cases hviolation : PartialViolation componentsValid assigned
      · simp [enumerateAux, hviolation, TraceTree.Uniform]
      · simp only [enumerateAux, hviolation, ↓reduceIte]
        apply TraceTree.uniform_union (ih _)
        apply TraceTree.uniform_union (ih _)
        exact TraceTree.uniform_union (ih _) (ih _)

theorem enumerate_uniform
    (componentsValid : ClassicalCertificateContractComponents.Valid
      partitionValid contract components)
    (ring : List (Fin hypermap.dartCount))
    (order : List (Fin components.componentCount)) :
    TraceTree.Uniform ring.length
      (enumerate componentsValid ring order) :=
  enumerateAux_uniform componentsValid ring [] order

private theorem accepts_union_left
    (_componentsValid : ClassicalCertificateContractComponents.Valid
      partitionValid contract components)
    (ring : List (Fin hypermap.dartCount))
    {left right : ClassicalCertificateTraceTree.TraceTree}
    (hleft : TraceTree.Uniform ring.length left)
    (hright : TraceTree.Uniform ring.length right)
    (word : List TraceSymbol) (hword : word.length = ring.length)
    (haccepts : left.accepts word = true) :
    (TraceTree.union left right).accepts word = true :=
  (TraceTree.accepts_union_iff hleft hright word hword).2 (Or.inl haccepts)

private theorem accepts_union_right
    (_componentsValid : ClassicalCertificateContractComponents.Valid
      partitionValid contract components)
    (ring : List (Fin hypermap.dartCount))
    {left right : ClassicalCertificateTraceTree.TraceTree}
    (hleft : TraceTree.Uniform ring.length left)
    (hright : TraceTree.Uniform ring.length right)
    (word : List TraceSymbol) (hword : word.length = ring.length)
    (haccepts : right.accepts word = true) :
    (TraceTree.union left right).accepts word = true :=
  (TraceTree.accepts_union_iff hleft hright word hword).2 (Or.inr haccepts)

/-- Every genuine contract assignment follows one branch of the automatic
enumerator and reaches its canonical boundary word. -/
theorem enumerateAux_accepts_of_contract
    (componentsValid : ClassicalCertificateContractComponents.Valid
      partitionValid contract components)
    (ring : List (Fin hypermap.dartCount))
    (assigned : List (AssignedColor components.componentCount))
    (remaining : List (Fin components.componentCount))
    (assignment : Fin components.componentCount → Color)
    (hagrees : Agrees assigned assignment)
    (hcontract : IsContractAssignment partitionValid contract
      (liftAssignment componentsValid assignment))
    (hcovered : AllCovered assigned remaining) :
    (enumerateAux componentsValid ring assigned remaining).accepts
      (symbolTraceOfAssignment partitionValid ring
        (liftAssignment componentsValid assignment)) = true := by
  induction remaining generalizing assigned with
  | nil =>
      have hnoViolation := not_partialViolation_of_agrees_contract
        componentsValid assigned assignment hagrees hcontract
      have hcomplete : ∀ component : Fin components.componentCount,
          component ∈ assigned.map Prod.fst := by
        intro component
        exact (hcovered component).resolve_right (by simp)
      have heq : assignmentOfAssigned assigned = assignment :=
        assignmentOfAssigned_eq hagrees hcomplete
      simp [enumerateAux, hnoViolation, heq,
        ClassicalCertificateTraceTree.TraceTree.accepts_singleton_iff]
  | cons component remaining ih =>
      have hnoViolation := not_partialViolation_of_agrees_contract
        componentsValid assigned assignment hagrees hcontract
      let word := symbolTraceOfAssignment partitionValid ring
        (liftAssignment componentsValid assignment)
      have hword : word.length = ring.length :=
        symbolTraceOfAssignment_length ring _
      have uniform (code : FaceColorCode) :
          TraceTree.Uniform ring.length
            (enumerateAux componentsValid ring
              ((component, code) :: assigned) remaining) :=
        enumerateAux_uniform componentsValid ring _ _
      rcases color_four_cases (assignment component) with
        hzero | hred | hblue | hpurple
      · have hbranch := ih ((component, .zero) :: assigned)
          (agrees_cons hagrees component .zero (by
            simpa [FaceColorCode.toColor] using hzero))
          (allCovered_step .zero hcovered)
        simp only [enumerateAux, hnoViolation, ↓reduceIte]
        exact accepts_union_left componentsValid ring
          (uniform .zero)
          (TraceTree.uniform_union (uniform .red)
            (TraceTree.uniform_union (uniform .blue) (uniform .purple)))
          word hword hbranch
      · have hbranch := ih ((component, .red) :: assigned)
          (agrees_cons hagrees component .red (by
            simpa [FaceColorCode.toColor] using hred))
          (allCovered_step .red hcovered)
        simp only [enumerateAux, hnoViolation, ↓reduceIte]
        apply accepts_union_right componentsValid ring
          (uniform .zero)
          (TraceTree.uniform_union (uniform .red)
            (TraceTree.uniform_union (uniform .blue) (uniform .purple)))
          word hword
        exact accepts_union_left componentsValid ring
          (uniform .red)
          (TraceTree.uniform_union (uniform .blue) (uniform .purple))
          word hword hbranch
      · have hbranch := ih ((component, .blue) :: assigned)
          (agrees_cons hagrees component .blue (by
            simpa [FaceColorCode.toColor] using hblue))
          (allCovered_step .blue hcovered)
        simp only [enumerateAux, hnoViolation, ↓reduceIte]
        apply accepts_union_right componentsValid ring
          (uniform .zero)
          (TraceTree.uniform_union (uniform .red)
            (TraceTree.uniform_union (uniform .blue) (uniform .purple)))
          word hword
        apply accepts_union_right componentsValid ring
          (uniform .red)
          (TraceTree.uniform_union (uniform .blue) (uniform .purple))
          word hword
        exact accepts_union_left componentsValid ring
          (uniform .blue) (uniform .purple) word hword hbranch
      · have hbranch := ih ((component, .purple) :: assigned)
          (agrees_cons hagrees component .purple (by
            simpa [FaceColorCode.toColor] using hpurple))
          (allCovered_step .purple hcovered)
        simp only [enumerateAux, hnoViolation, ↓reduceIte]
        apply accepts_union_right componentsValid ring
          (uniform .zero)
          (TraceTree.uniform_union (uniform .red)
            (TraceTree.uniform_union (uniform .blue) (uniform .purple)))
          word hword
        apply accepts_union_right componentsValid ring
          (uniform .red)
          (TraceTree.uniform_union (uniform .blue) (uniform .purple))
          word hword
        exact accepts_union_right componentsValid ring
          (uniform .blue) (uniform .purple) word hword hbranch

/-- The automatic trace trie covers every coloring of the checked contracted
map whenever the supplied component order is complete. -/
theorem enumerate_accepts_of_contract
    (componentsValid : ClassicalCertificateContractComponents.Valid
      partitionValid contract components)
    (ring : List (Fin hypermap.dartCount))
    (order : List (Fin components.componentCount))
    (horder : ∀ component : Fin components.componentCount,
      component ∈ order)
    (assignment : Fin components.componentCount → Color)
    (hcontract : IsContractAssignment partitionValid contract
      (liftAssignment componentsValid assignment)) :
    (enumerate componentsValid ring order).accepts
      (symbolTraceOfAssignment partitionValid ring
        (liftAssignment componentsValid assignment)) = true := by
  apply enumerateAux_accepts_of_contract componentsValid ring [] order
    assignment (by simp [Agrees]) hcontract
  intro component
  exact Or.inr (horder component)

private theorem exists_assignedColor?_eq_some_of_mem
    {componentCount : Nat}
    (assigned : List (AssignedColor componentCount))
    (component : Fin componentCount)
    (hmem : component ∈ assigned.map Prod.fst) :
    ∃ color, assignedColor? assigned component = some color := by
  induction assigned with
  | nil => simp at hmem
  | cons entry assigned ih =>
      by_cases hcomponent : entry.1 = component
      · exact ⟨entry.2.toColor, by
          simp [assignedColor?, hcomponent]⟩
      · have htail : component ∈ assigned.map Prod.fst := by
          have hcomponent' : component ≠ entry.1 := Ne.symm hcomponent
          simpa [hcomponent'] using hmem
        obtain ⟨color, hcolor⟩ := ih htail
        exact ⟨color, by
          simpa [assignedColor?, hcomponent] using hcolor⟩

/-- A complete partial assignment with no violated edge satisfies every
contract equation after it is pulled back to the face classes. -/
theorem isContractAssignment_of_not_partialViolation
    (componentsValid : ClassicalCertificateContractComponents.Valid
      partitionValid contract components)
    (assigned : List (AssignedColor components.componentCount))
    (hcomplete : ∀ component : Fin components.componentCount,
      component ∈ assigned.map Prod.fst)
    (hnoViolation : ¬ PartialViolation componentsValid assigned) :
    IsContractAssignment partitionValid contract
      (liftAssignment componentsValid (assignmentOfAssigned assigned)) := by
  intro dart
  let dartComponent := component componentsValid
    (faceClass partitionValid dart)
  let edgeComponent := component componentsValid
    (faceClass partitionValid
      ((edgeTable hypermap).toFin dart))
  obtain ⟨dartColor, hdartColor⟩ :=
    exists_assignedColor?_eq_some_of_mem assigned dartComponent
      (hcomplete dartComponent)
  obtain ⟨edgeColor, hedgeColor⟩ :=
    exists_assignedColor?_eq_some_of_mem assigned edgeComponent
      (hcomplete edgeComponent)
  have hequation :
      (edgeColor = dartColor) ↔ InRawContract contract dart := by
    by_contra hfalse
    apply hnoViolation
    refine ⟨dart, ?_⟩
    change (match assignedColor? assigned dartComponent,
        assignedColor? assigned edgeComponent with
      | some dartColor, some edgeColor =>
          !(decide ((edgeColor = dartColor) ↔ InRawContract contract dart))
      | _, _ => false) = true
    rw [hdartColor, hedgeColor]
    simp [hfalse]
  change (assignmentOfAssigned assigned edgeComponent =
      assignmentOfAssigned assigned dartComponent) ↔
        InRawContract contract dart
  simpa [assignmentOfAssigned, hdartColor, hedgeColor] using hequation

/-- Every word in the automatically enumerated trie is realized by a genuine
component coloring satisfying the checked contract. -/
theorem enumerateAux_sound
    (componentsValid : ClassicalCertificateContractComponents.Valid
      partitionValid contract components)
    (ring : List (Fin hypermap.dartCount))
    (assigned : List (AssignedColor components.componentCount))
    (remaining : List (Fin components.componentCount))
    (hcovered : AllCovered assigned remaining)
    (word : List TraceSymbol)
    (haccepts :
      (enumerateAux componentsValid ring assigned remaining).accepts word =
        true) :
    ∃ assignment : Fin components.componentCount → Color,
      IsContractAssignment partitionValid contract
        (liftAssignment componentsValid assignment) ∧
      symbolTraceOfAssignment partitionValid ring
        (liftAssignment componentsValid assignment) = word := by
  have hword : word.length = ring.length :=
    TraceTree.length_eq_of_uniform_accepts
      (enumerateAux_uniform componentsValid ring assigned remaining)
        word haccepts
  induction remaining generalizing assigned with
  | nil =>
      by_cases hviolation : PartialViolation componentsValid assigned
      · simp [enumerateAux, hviolation,
          ClassicalCertificateTraceTree.TraceTree.accepts] at haccepts
      · have hcomplete : ∀ component : Fin components.componentCount,
            component ∈ assigned.map Prod.fst := by
          intro component
          exact (hcovered component).resolve_right (by simp)
        have hwordEq :=
          (ClassicalCertificateTraceTree.TraceTree.accepts_singleton_iff
            (symbolTraceOfAssignment partitionValid ring
              (liftAssignment componentsValid
                (assignmentOfAssigned assigned))) word).1 (by
                  simpa [enumerateAux, hviolation] using haccepts)
        exact ⟨assignmentOfAssigned assigned,
          isContractAssignment_of_not_partialViolation componentsValid
            assigned hcomplete hviolation,
          hwordEq.symm⟩
  | cons next remaining ih =>
      by_cases hviolation : PartialViolation componentsValid assigned
      · simp [enumerateAux, hviolation,
          ClassicalCertificateTraceTree.TraceTree.accepts] at haccepts
      · have uniform (code : FaceColorCode) :
            TraceTree.Uniform ring.length
              (enumerateAux componentsValid ring
                ((next, code) :: assigned) remaining) :=
          enumerateAux_uniform componentsValid ring _ _
        have hsplit :=
          (TraceTree.accepts_union_iff (uniform .zero)
            (TraceTree.uniform_union (uniform .red)
              (TraceTree.uniform_union (uniform .blue) (uniform .purple)))
            word hword).1 (by
              simpa [enumerateAux, hviolation] using haccepts)
        rcases hsplit with hzero | hnonzero
        · exact ih ((next, .zero) :: assigned)
            (allCovered_step .zero hcovered) hzero
        · have hsplit' :=
            (TraceTree.accepts_union_iff (uniform .red)
              (TraceTree.uniform_union (uniform .blue) (uniform .purple))
              word hword).1 hnonzero
          rcases hsplit' with hred | hbluePurple
          · exact ih ((next, .red) :: assigned)
              (allCovered_step .red hcovered) hred
          · have hsplit'' :=
              (TraceTree.accepts_union_iff (uniform .blue) (uniform .purple)
                word hword).1 hbluePurple
            rcases hsplit'' with hblue | hpurple
            · exact ih ((next, .blue) :: assigned)
                (allCovered_step .blue hcovered) hblue
            · exact ih ((next, .purple) :: assigned)
                (allCovered_step .purple hcovered) hpurple

/-- Exact semantics of the automatically enumerated contract-trace trie. -/
theorem enumerate_accepts_iff
    (componentsValid : ClassicalCertificateContractComponents.Valid
      partitionValid contract components)
    (ring : List (Fin hypermap.dartCount))
    (order : List (Fin components.componentCount))
    (horder : ∀ component : Fin components.componentCount,
      component ∈ order)
    (word : List TraceSymbol) :
    (enumerate componentsValid ring order).accepts word = true ↔
      ∃ assignment : Fin components.componentCount → Color,
        IsContractAssignment partitionValid contract
          (liftAssignment componentsValid assignment) ∧
        symbolTraceOfAssignment partitionValid ring
          (liftAssignment componentsValid assignment) = word := by
  constructor
  · intro haccepts
    apply enumerateAux_sound componentsValid ring [] order
    · intro component
      exact Or.inr (horder component)
    · exact haccepts
  · rintro ⟨assignment, hcontract, rfl⟩
    exact enumerate_accepts_of_contract componentsValid ring order horder
      assignment hcontract

/-- The automatic symbolic language is exactly the standard color-valued
contract-ring language of the checked finite hypermap. -/
theorem enumerate_accepts_iff_contractRingTrace
    (componentsValid : ClassicalCertificateContractComponents.Valid
      partitionValid contract components)
    (ring : List (Fin hypermap.dartCount))
    (order : List (Fin components.componentCount))
    (horder : ∀ component : Fin components.componentCount,
      component ∈ order)
    (hcycle : RawReverseBoundaryCycle hypermap ring)
    (havoid : ContractAvoidsBoundary contract ring)
    (word : List TraceSymbol) :
    (enumerate componentsValid ring order).accepts word = true ↔
      ClassicalCertificateHypermapColoring.FiniteHypermap.ContractRingTrace
        (checkedHypermap partitionValid) contract ring
          (word.map TraceSymbol.toColor) := by
  constructor
  · intro haccepts
    obtain ⟨assignment, hcontract, hword⟩ :=
      (enumerate_accepts_iff componentsValid ring order horder word).1
        haccepts
    apply (contractRingTrace_iff_exists_assignment partitionValid contract
      ring _).2
    refine ⟨liftAssignment componentsValid assignment, hcontract, ?_⟩
    rw [← hword]
    exact symbolTraceOfAssignment_toColor partitionValid contract ring
      (liftAssignment componentsValid assignment) hcontract hcycle havoid
  · intro htrace
    obtain ⟨assignment, hcontract, hboundary⟩ :=
      (contractRingTrace_iff_exists_assignment partitionValid contract
        ring _).1 htrace
    let componentAssignment :=
      restrictAssignment componentsValid assignment
    have hfactor :
        liftAssignment componentsValid componentAssignment = assignment :=
      lift_restrictAssignment_eq componentsValid assignment hcontract
    have hcomponentContract :
        IsContractAssignment partitionValid contract
          (liftAssignment componentsValid componentAssignment) := by
      rw [hfactor]
      exact hcontract
    apply (enumerate_accepts_iff componentsValid ring order horder word).2
    refine ⟨componentAssignment, hcomponentContract, ?_⟩
    apply TraceSymbol.map_toColor_injective
    rw [symbolTraceOfAssignment_toColor partitionValid contract ring
      (liftAssignment componentsValid componentAssignment)
        hcomponentContract hcycle havoid]
    simpa [hfactor] using hboundary.symm

end ClassicalCertificateExactTraceEnumeration

end Mettapedia.GraphTheory.FourColor
