import Mettapedia.GraphTheory.FourColor.ClassicalCertificateContractComponents
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateTraceWitness

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateContractColorSearch

open ClassicalCertificateColorTrace
open ClassicalCertificateConfiguration
open ClassicalCertificateContractComponents
open ClassicalCertificateFacePartition
open ClassicalCertificateTraceTree
open ClassicalCertificateTraceWitness

/-- A total executable inverse to `TraceSymbol.toColor` on nonzero colors. -/
def symbolOfColor (color : Color) : TraceSymbol :=
  if color = FourColor.red then .red
  else if color = FourColor.blue then .blue
  else .purple

theorem toColor_symbolOfColor_of_ne_zero {color : Color}
    (hnonzero : color ≠ 0) : (symbolOfColor color).toColor = color := by
  obtain ⟨symbol, hsymbol, _⟩ :=
    TraceSymbol.existsUnique_toColor_eq color hnonzero
  cases symbol <;> subst color <;> decide

/-- The canonical symbol spelling of a color-valued boundary trace. -/
def symbolTraceOfAssignment {hypermap : HypermapCode}
    {partition : ClassicalCertificateFacePartition.Code}
    (partitionValid : ClassicalCertificateFacePartition.Valid hypermap partition)
    (ring : List (Fin hypermap.dartCount))
    (assignment : Fin partition.faceCount → Color) : List TraceSymbol :=
  (ringTraceOfAssignment partitionValid ring assignment).map symbolOfColor

theorem symbolTraceOfAssignment_toColor
    {hypermap : HypermapCode}
    {partition : ClassicalCertificateFacePartition.Code}
    (partitionValid : ClassicalCertificateFacePartition.Valid hypermap partition)
    (contract : Finset (Fin hypermap.dartCount))
    (ring : List (Fin hypermap.dartCount))
    (assignment : Fin partition.faceCount → Color)
    (hcontract : IsContractAssignment partitionValid contract assignment)
    (hcycle : RawReverseBoundaryCycle hypermap ring)
    (havoid : ContractAvoidsBoundary contract ring) :
    (symbolTraceOfAssignment partitionValid ring assignment).map
        TraceSymbol.toColor =
      ringTraceOfAssignment partitionValid ring assignment := by
  rw [symbolTraceOfAssignment, List.map_map]
  calc
    List.map (TraceSymbol.toColor ∘ symbolOfColor)
        (ringTraceOfAssignment partitionValid ring assignment) =
        List.map id
          (ringTraceOfAssignment partitionValid ring assignment) := by
      apply List.map_congr_left
      intro color hcolor
      apply toColor_symbolOfColor_of_ne_zero
      exact mem_trace_ne_zero
        (cyclicallyDistinct_ringColorWord_of_contract partitionValid contract
          ring assignment hcontract hcycle havoid) color hcolor
    _ = ringTraceOfAssignment partitionValid ring assignment := by simp

/-- Four-way search syntax. Rejected nodes are justified by a fully assigned
violated edge; accepted leaves carry a root trace. -/
inductive SearchTree where
  | reject
  | accept
  | node (zero red blue purple : SearchTree)
  deriving DecidableEq, Repr

abbrev AssignedColor (componentCount : Nat) :=
  Fin componentCount × FaceColorCode

def assignedColor? {componentCount : Nat}
    (assigned : List (AssignedColor componentCount))
    (component : Fin componentCount) : Option Color :=
  (assigned.find? fun entry => entry.1 = component).map
    (fun entry => entry.2.toColor)

def assignmentOfAssigned {componentCount : Nat}
    (assigned : List (AssignedColor componentCount)) :
    Fin componentCount → Color :=
  fun component => (assignedColor? assigned component).getD 0

def Agrees {componentCount : Nat}
    (assigned : List (AssignedColor componentCount))
    (assignment : Fin componentCount → Color) : Prop :=
  ∀ entry ∈ assigned, assignment entry.1 = entry.2.toColor

instance {componentCount : Nat}
    (assigned : List (AssignedColor componentCount))
    (assignment : Fin componentCount → Color) :
    Decidable (Agrees assigned assignment) := by
  unfold Agrees
  infer_instance

theorem assignment_eq_of_assignedColor?_eq_some {componentCount : Nat}
    {assigned : List (AssignedColor componentCount)}
    {assignment : Fin componentCount → Color}
    (hagrees : Agrees assigned assignment) (component : Fin componentCount)
    (color : Color) (hfound : assignedColor? assigned component = some color) :
    assignment component = color := by
  unfold assignedColor? at hfound
  cases hentry : List.find? (fun entry : AssignedColor componentCount =>
      decide (entry.1 = component)) assigned with
  | some entry =>
    have hmem : entry ∈ assigned := List.mem_of_find?_eq_some hentry
    have hcomponent : entry.1 = component := by
      have := List.find?_some hentry
      simpa using this
    have hcolor : entry.2.toColor = color := by
      rw [hentry] at hfound
      simpa using hfound
    calc
      assignment component = assignment entry.1 := by rw [hcomponent]
      _ = entry.2.toColor := hagrees entry hmem
      _ = color := hcolor
  | none => rw [hentry] at hfound; simp at hfound

theorem assignmentOfAssigned_eq {componentCount : Nat}
    {assigned : List (AssignedColor componentCount)}
    {assignment : Fin componentCount → Color}
    (hagrees : Agrees assigned assignment)
    (hcomplete : ∀ component : Fin componentCount,
      component ∈ assigned.map Prod.fst) :
    assignmentOfAssigned assigned = assignment := by
  funext component
  obtain ⟨entry, hentry, hcomponent⟩ :=
    (List.mem_map.1 (hcomplete component))
  unfold assignmentOfAssigned
  cases hfound : assignedColor? assigned component with
  | none =>
      unfold assignedColor? at hfound
      cases hfind : List.find? (fun candidate : AssignedColor componentCount =>
          decide (candidate.1 = component)) assigned with
      | none =>
          have hnone := List.find?_eq_none.1 hfind entry hentry
          simp [hcomponent] at hnone
      | some candidate => simp [hfind] at hfound
  | some color =>
      rw [Option.getD_some]
      exact (assignment_eq_of_assignedColor?_eq_some hagrees component color
        hfound).symm

theorem agrees_cons {componentCount : Nat}
    {assigned : List (AssignedColor componentCount)}
    {assignment : Fin componentCount → Color}
    (hagrees : Agrees assigned assignment) (component : Fin componentCount)
    (code : FaceColorCode) (hcolor : assignment component = code.toColor) :
    Agrees ((component, code) :: assigned) assignment := by
  intro entry hentry
  rcases List.mem_cons.1 hentry with rfl | htail
  · exact hcolor
  · exact hagrees entry htail

def AllCovered {componentCount : Nat}
    (assigned : List (AssignedColor componentCount))
    (remaining : List (Fin componentCount)) : Prop :=
  ∀ component : Fin componentCount,
    component ∈ assigned.map Prod.fst ∨ component ∈ remaining

theorem allCovered_step {componentCount : Nat}
    {assigned : List (AssignedColor componentCount)}
    {remaining : List (Fin componentCount)}
    {component : Fin componentCount} (code : FaceColorCode)
    (hcovered : AllCovered assigned (component :: remaining)) :
    AllCovered ((component, code) :: assigned) remaining := by
  intro index
  rcases hcovered index with hassigned | hremaining
  · exact Or.inl (by simp [hassigned])
  · rcases List.mem_cons.1 hremaining with rfl | htail
    · exact Or.inl (by simp)
    · exact Or.inr htail

theorem color_four_cases (color : Color) :
    color = 0 ∨ color = FourColor.red ∨ color = FourColor.blue ∨
      color = FourColor.purple := by
  rcases color with ⟨first, second⟩
  fin_cases first <;> fin_cases second
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inr rfl))

def violatesAt {hypermap : HypermapCode}
    {partition : ClassicalCertificateFacePartition.Code}
    {partitionValid : ClassicalCertificateFacePartition.Valid hypermap partition}
    {contract : Finset (Fin hypermap.dartCount)}
    {components : ClassicalCertificateContractComponents.Code}
    (componentsValid : ClassicalCertificateContractComponents.Valid
      partitionValid contract components)
    (assigned : List (AssignedColor components.componentCount))
    (dart : Fin hypermap.dartCount) : Bool :=
  let dartComponent := component componentsValid (faceClass partitionValid dart)
  let edgeComponent := component componentsValid
    (faceClass partitionValid ((edgeTable hypermap).toFin dart))
  match assignedColor? assigned dartComponent,
      assignedColor? assigned edgeComponent with
  | some dartColor, some edgeColor =>
      !(decide ((edgeColor = dartColor) ↔ InRawContract contract dart))
  | _, _ => false

def PartialViolation {hypermap : HypermapCode}
    {partition : ClassicalCertificateFacePartition.Code}
    {partitionValid : ClassicalCertificateFacePartition.Valid hypermap partition}
    {contract : Finset (Fin hypermap.dartCount)}
    {components : ClassicalCertificateContractComponents.Code}
    (componentsValid : ClassicalCertificateContractComponents.Valid
      partitionValid contract components)
    (assigned : List (AssignedColor components.componentCount)) : Prop :=
  ∃ dart, violatesAt componentsValid assigned dart = true

instance {hypermap : HypermapCode}
    {partition : ClassicalCertificateFacePartition.Code}
    {partitionValid : ClassicalCertificateFacePartition.Valid hypermap partition}
    {contract : Finset (Fin hypermap.dartCount)}
    {components : ClassicalCertificateContractComponents.Code}
    (componentsValid : ClassicalCertificateContractComponents.Valid
      partitionValid contract components)
    (assigned : List (AssignedColor components.componentCount)) :
    Decidable (PartialViolation componentsValid assigned) := by
  unfold PartialViolation
  infer_instance

theorem not_partialViolation_of_agrees_contract
    {hypermap : HypermapCode}
    {partition : ClassicalCertificateFacePartition.Code}
    {partitionValid : ClassicalCertificateFacePartition.Valid hypermap partition}
    {contract : Finset (Fin hypermap.dartCount)}
    {components : ClassicalCertificateContractComponents.Code}
    (componentsValid : ClassicalCertificateContractComponents.Valid
      partitionValid contract components)
    (assigned : List (AssignedColor components.componentCount))
    (assignment : Fin components.componentCount → Color)
    (hagrees : Agrees assigned assignment)
    (hcontract : IsContractAssignment partitionValid contract
      (liftAssignment componentsValid assignment)) :
    ¬ PartialViolation componentsValid assigned := by
  rintro ⟨dart, hviolation⟩
  let dartComponent :=
    component componentsValid (faceClass partitionValid dart)
  let edgeComponent := component componentsValid
    (faceClass partitionValid ((edgeTable hypermap).toFin dart))
  change (match assignedColor? assigned dartComponent,
      assignedColor? assigned edgeComponent with
    | some dartColor, some edgeColor =>
        !(decide ((edgeColor = dartColor) ↔ InRawContract contract dart))
    | _, _ => false) = true at hviolation
  cases hdart : assignedColor? assigned dartComponent with
  | none => simp [hdart] at hviolation
  | some dartColor =>
      cases hedge : assignedColor? assigned edgeComponent with
      | none => simp [hdart, hedge] at hviolation
      | some edgeColor =>
          have hbad : ¬ ((edgeColor = dartColor) ↔
              InRawContract contract dart) := by
            simpa [hdart, hedge] using hviolation
          have hdartColor : assignment dartComponent = dartColor :=
            assignment_eq_of_assignedColor?_eq_some hagrees dartComponent
              dartColor hdart
          have hedgeColor : assignment edgeComponent = edgeColor :=
            assignment_eq_of_assignedColor?_eq_some hagrees edgeComponent
              edgeColor hedge
          have hactual :
              (assignment edgeComponent = assignment dartComponent) ↔
                InRawContract contract dart := by
            simpa [colorOfAssignment, liftAssignment, dartComponent,
              edgeComponent] using hcontract dart
          exact hbad (by simpa [hdartColor, hedgeColor] using hactual)

namespace SearchTree

/-- Semantic validity of one pruned search subtree. -/
def Valid {hypermap : HypermapCode}
    {partition : ClassicalCertificateFacePartition.Code}
    {partitionValid : ClassicalCertificateFacePartition.Valid hypermap partition}
    {contract : Finset (Fin hypermap.dartCount)}
    {components : ClassicalCertificateContractComponents.Code}
    (componentsValid : ClassicalCertificateContractComponents.Valid
      partitionValid contract components)
    (ring : List (Fin hypermap.dartCount)) (covered : TraceTree) :
    SearchTree → List (AssignedColor components.componentCount) →
      List (Fin components.componentCount) → Prop
  | .reject, assigned, _ => PartialViolation componentsValid assigned
  | .accept, assigned, remaining =>
      remaining = [] ∧
        covered.accepts
          (symbolTraceOfAssignment partitionValid ring
            (liftAssignment componentsValid
              (assignmentOfAssigned assigned))) = true
  | .node zero red blue purple, assigned, component :: remaining =>
      Valid componentsValid ring covered zero
          ((component, .zero) :: assigned) remaining ∧
        Valid componentsValid ring covered red
          ((component, .red) :: assigned) remaining ∧
        Valid componentsValid ring covered blue
          ((component, .blue) :: assigned) remaining ∧
        Valid componentsValid ring covered purple
          ((component, .purple) :: assigned) remaining
  | .node _ _ _ _, _, [] => False

/-- Executable verifier for a pruned search tree. -/
def check {hypermap : HypermapCode}
    {partition : ClassicalCertificateFacePartition.Code}
    {partitionValid : ClassicalCertificateFacePartition.Valid hypermap partition}
    {contract : Finset (Fin hypermap.dartCount)}
    {components : ClassicalCertificateContractComponents.Code}
    (componentsValid : ClassicalCertificateContractComponents.Valid
      partitionValid contract components)
    (ring : List (Fin hypermap.dartCount)) (covered : TraceTree)
    : SearchTree → List (AssignedColor components.componentCount) →
      List (Fin components.componentCount) → Bool
  | .reject, assigned, _ => decide (PartialViolation componentsValid assigned)
  | .accept, assigned, remaining =>
      decide (remaining = []) &&
        covered.accepts
          (symbolTraceOfAssignment partitionValid ring
            (liftAssignment componentsValid
              (assignmentOfAssigned assigned)))
  | .node zero red blue purple, assigned, component :: remaining =>
      check componentsValid ring covered zero
          ((component, .zero) :: assigned) remaining &&
        check componentsValid ring covered red
          ((component, .red) :: assigned) remaining &&
        check componentsValid ring covered blue
          ((component, .blue) :: assigned) remaining &&
        check componentsValid ring covered purple
          ((component, .purple) :: assigned) remaining
  | .node _ _ _ _, _, [] => false

theorem valid_of_check_true {hypermap : HypermapCode}
    {partition : ClassicalCertificateFacePartition.Code}
    {partitionValid : ClassicalCertificateFacePartition.Valid hypermap partition}
    {contract : Finset (Fin hypermap.dartCount)}
    {components : ClassicalCertificateContractComponents.Code}
    (componentsValid : ClassicalCertificateContractComponents.Valid
      partitionValid contract components)
    (ring : List (Fin hypermap.dartCount)) (covered : TraceTree)
    (tree : SearchTree)
    (assigned : List (AssignedColor components.componentCount))
    (remaining : List (Fin components.componentCount))
    (hcheck : check componentsValid ring covered tree assigned remaining = true) :
    tree.Valid componentsValid ring covered assigned remaining := by
  induction tree generalizing assigned remaining with
  | reject =>
      simpa [check, Valid] using Bool.of_decide_true hcheck
  | accept =>
      simp only [check, Bool.and_eq_true] at hcheck
      exact ⟨Bool.of_decide_true hcheck.1, hcheck.2⟩
  | node zero red blue purple ihZero ihRed ihBlue ihPurple =>
      cases remaining with
      | nil => simp [check] at hcheck
      | cons component remaining =>
          simp only [check, Bool.and_eq_true] at hcheck
          exact ⟨ihZero _ _ hcheck.1.1.1,
            ihRed _ _ hcheck.1.1.2,
            ihBlue _ _ hcheck.1.2,
            ihPurple _ _ hcheck.2⟩

theorem accepts_of_valid {hypermap : HypermapCode}
    {partition : ClassicalCertificateFacePartition.Code}
    {partitionValid : ClassicalCertificateFacePartition.Valid hypermap partition}
    {contract : Finset (Fin hypermap.dartCount)}
    {components : ClassicalCertificateContractComponents.Code}
    (componentsValid : ClassicalCertificateContractComponents.Valid
      partitionValid contract components)
    (ring : List (Fin hypermap.dartCount)) (covered : TraceTree)
    (tree : SearchTree)
    (assigned : List (AssignedColor components.componentCount))
    (remaining : List (Fin components.componentCount))
    (hvalid : tree.Valid componentsValid ring covered assigned remaining)
    (assignment : Fin components.componentCount → Color)
    (hagrees : Agrees assigned assignment)
    (hcontract : IsContractAssignment partitionValid contract
      (liftAssignment componentsValid assignment))
    (hcovered : AllCovered assigned remaining) :
    covered.accepts
      (symbolTraceOfAssignment partitionValid ring
        (liftAssignment componentsValid assignment)) = true := by
  induction tree generalizing assigned remaining with
  | reject =>
      exact (not_partialViolation_of_agrees_contract componentsValid assigned
        assignment hagrees hcontract hvalid).elim
  | accept =>
      have hcomplete : ∀ component : Fin components.componentCount,
          component ∈ assigned.map Prod.fst := by
        intro component
        rcases hcovered component with hassigned | hremaining
        · exact hassigned
        · simpa [hvalid.1] using hremaining
      have heq : assignmentOfAssigned assigned = assignment :=
        assignmentOfAssigned_eq hagrees hcomplete
      simpa [heq] using hvalid.2
  | node zero red blue purple ihZero ihRed ihBlue ihPurple =>
      cases remaining with
      | nil => exact hvalid.elim
      | cons next remaining =>
          rcases color_four_cases (assignment next) with
            hzero | hred | hblue | hpurple
          · apply ihZero ((next, .zero) :: assigned) remaining hvalid.1
            · exact agrees_cons hagrees next .zero (by
                simpa [FaceColorCode.toColor] using hzero)
            · exact allCovered_step .zero hcovered
          · apply ihRed ((next, .red) :: assigned) remaining hvalid.2.1
            · exact agrees_cons hagrees next .red (by
                simpa [FaceColorCode.toColor] using hred)
            · exact allCovered_step .red hcovered
          · apply ihBlue ((next, .blue) :: assigned) remaining
              hvalid.2.2.1
            · exact agrees_cons hagrees next .blue (by
                simpa [FaceColorCode.toColor] using hblue)
            · exact allCovered_step .blue hcovered
          · apply ihPurple ((next, .purple) :: assigned) remaining
              hvalid.2.2.2
            · exact agrees_cons hagrees next .purple (by
                simpa [FaceColorCode.toColor] using hpurple)
            · exact allCovered_step .purple hcovered

end SearchTree

/-- A component order together with a pruned four-color search tree. -/
structure Certificate (componentCount : Nat) where
  order : List (Fin componentCount)
  tree : SearchTree
  deriving DecidableEq, Repr

namespace Certificate

def OrderComplete {componentCount : Nat}
    (certificate : Certificate componentCount) : Prop :=
  ∀ component : Fin componentCount, component ∈ certificate.order

instance {componentCount : Nat}
    (certificate : Certificate componentCount) :
    Decidable certificate.OrderComplete := by
  unfold OrderComplete
  infer_instance

/-- Reflected checker for component coverage and every node of the pruned
search. -/
def checker {hypermap : HypermapCode}
    {partition : ClassicalCertificateFacePartition.Code}
    {partitionValid : ClassicalCertificateFacePartition.Valid hypermap partition}
    {contract : Finset (Fin hypermap.dartCount)}
    {components : ClassicalCertificateContractComponents.Code}
    (componentsValid : ClassicalCertificateContractComponents.Valid
      partitionValid contract components)
    (ring : List (Fin hypermap.dartCount)) (covered : TraceTree)
    (certificate : Certificate components.componentCount) : Bool :=
  decide certificate.OrderComplete &&
    SearchTree.check componentsValid ring covered certificate.tree []
      certificate.order

theorem accepts_of_checker_true {hypermap : HypermapCode}
    {partition : ClassicalCertificateFacePartition.Code}
    {partitionValid : ClassicalCertificateFacePartition.Valid hypermap partition}
    {contract : Finset (Fin hypermap.dartCount)}
    {components : ClassicalCertificateContractComponents.Code}
    (componentsValid : ClassicalCertificateContractComponents.Valid
      partitionValid contract components)
    (ring : List (Fin hypermap.dartCount)) (covered : TraceTree)
    (certificate : Certificate components.componentCount)
    (hchecker : certificate.checker componentsValid ring covered = true)
    (assignment : Fin components.componentCount → Color)
    (hcontract : IsContractAssignment partitionValid contract
      (liftAssignment componentsValid assignment)) :
    covered.accepts
      (symbolTraceOfAssignment partitionValid ring
        (liftAssignment componentsValid assignment)) = true := by
  simp only [checker, Bool.and_eq_true] at hchecker
  have horder : certificate.OrderComplete :=
    Bool.of_decide_true hchecker.1
  have hvalid := SearchTree.valid_of_check_true componentsValid ring covered
    certificate.tree [] certificate.order hchecker.2
  apply SearchTree.accepts_of_valid componentsValid ring covered
    certificate.tree [] certificate.order hvalid assignment
  · simp [Agrees]
  · exact hcontract
  · intro component
    exact Or.inr (horder component)

/-- Every genuine face-class contract assignment reaches the certified root
trace tree. -/
theorem accepts_of_contractAssignment {hypermap : HypermapCode}
    {partition : ClassicalCertificateFacePartition.Code}
    {partitionValid : ClassicalCertificateFacePartition.Valid hypermap partition}
    {contract : Finset (Fin hypermap.dartCount)}
    {components : ClassicalCertificateContractComponents.Code}
    (componentsValid : ClassicalCertificateContractComponents.Valid
      partitionValid contract components)
    (ring : List (Fin hypermap.dartCount)) (covered : TraceTree)
    (certificate : Certificate components.componentCount)
    (hchecker : certificate.checker componentsValid ring covered = true)
    (assignment : Fin partition.faceCount → Color)
    (hcontract : IsContractAssignment partitionValid contract assignment) :
    covered.accepts
      (symbolTraceOfAssignment partitionValid ring assignment) = true := by
  let componentAssignment := restrictAssignment componentsValid assignment
  have hfactor : liftAssignment componentsValid componentAssignment = assignment :=
    lift_restrictAssignment_eq componentsValid assignment hcontract
  have hcontract' : IsContractAssignment partitionValid contract
      (liftAssignment componentsValid componentAssignment) := by
    rw [hfactor]
    exact hcontract
  have haccepted := certificate.accepts_of_checker_true componentsValid ring
    covered hchecker componentAssignment hcontract'
  simpa [hfactor] using haccepted

/-- Root completeness in the external word spelling used by the ranked Kempe
certificate. -/
theorem accepts_of_contractWord {hypermap : HypermapCode}
    {partition : ClassicalCertificateFacePartition.Code}
    {partitionValid : ClassicalCertificateFacePartition.Valid hypermap partition}
    {contract : Finset (Fin hypermap.dartCount)}
    {components : ClassicalCertificateContractComponents.Code}
    (componentsValid : ClassicalCertificateContractComponents.Valid
      partitionValid contract components)
    (ring : List (Fin hypermap.dartCount)) (covered : TraceTree)
    (certificate : Certificate components.componentCount)
    (hchecker : certificate.checker componentsValid ring covered = true)
    (hcycle : RawReverseBoundaryCycle hypermap ring)
    (havoid : ContractAvoidsBoundary contract ring)
    (assignment : Fin partition.faceCount → Color)
    (hcontract : IsContractAssignment partitionValid contract assignment)
    (word : List TraceSymbol)
    (hword : word.map TraceSymbol.toColor =
      ringTraceOfAssignment partitionValid ring assignment) :
    covered.accepts word = true := by
  have haccepted := certificate.accepts_of_contractAssignment componentsValid
    ring covered hchecker assignment hcontract
  have hcanonical := symbolTraceOfAssignment_toColor partitionValid contract
    ring assignment hcontract hcycle havoid
  have heq : word = symbolTraceOfAssignment partitionValid ring assignment :=
    TraceSymbol.map_toColor_injective (hword.trans hcanonical.symm)
  simpa [heq] using haccepted

end Certificate

end ClassicalCertificateContractColorSearch

end Mettapedia.GraphTheory.FourColor
