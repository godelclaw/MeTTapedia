import Mettapedia.TypeTheory.MaterialSets.Hypersets.CodedFamilyTypeOperations

/-!
# Contextual comparison of coded and material dependent type operations

The codomain family is transported through the actual comprehension
isomorphism. Product and sum formation then agree with the independently
constructed material hyperset operations. Abstraction compares actual
function graphs, including the values of the dependent body.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.CodedFamilyTypeComparison
open CodedFamilies CodedFamilyCwf
universe u

/-- Decode the dependent codomain along the comprehension comparison. -/
def codomain (p : HSet.Presentation.{u}) {Γ : Code.{u}} (A : Family Γ)
    (B : Family (sigmaCode p A)) : FamilyCwf.Family (FamilyCwf.extension p (decodedFamily A)) :=
  fun point => decode (B ((comprehensionEquiv p A).symm point))

theorem inverseMember_value {context : Code.{u}} (point : FamilyCwf.Elements (decode context)) :
    decode ((memberEquiv context).symm point).1 = point.1 := by
  rw [memberEquiv_symm_value, decode_encode]

/-- The inverse comparison sends an actual material pair to the pair of its
actual inverse member codes. No arbitrary representative is selected. -/
theorem comprehension_pair_inverse (p : HSet.Presentation.{u}) {Γ : Code.{u}} (A : Family Γ)
    (point : FamilyCwf.Elements (decode Γ)) (argument : FamilyCwf.Elements (decodedFamily A point)) :
    (comprehensionEquiv p A).symm
        ((FamilyCwf.extensionDecode p (decodedFamily A)).symm ⟨point, argument⟩) =
      pairCode p A ⟨(memberEquiv Γ).symm point,
        (memberEquiv (A ((memberEquiv Γ).symm point))).symm argument⟩ := by
  apply (comprehensionEquiv p A).injective
  rw [Equiv.apply_symm_apply]
  apply El.ext HSet.propositional
  change HSet.kpair point.1 argument.1 =
    ((encodedMemberEquiv (materialSigma p A)) (pairCode p A
      ⟨(memberEquiv Γ).symm point, (memberEquiv (A ((memberEquiv Γ).symm point))).symm argument⟩)).1
  rw [encodedMemberEquiv_value, pairCode_value, inverseMember_value, inverseMember_value]

/-- The dependent fibre agrees after the whole extended context is decoded. -/
theorem fibreFamily_comparison (p : HSet.Presentation.{u}) {Γ : Code.{u}} (A : Family Γ)
    (B : Family (sigmaCode p A)) (point : FamilyCwf.Elements (decode Γ)) :
    decodedFamily (CodedFamilyTypeOperations.fibreFamily p A B ((memberEquiv Γ).symm point)) =
      FamilyCwf.fibreFamily p (decodedFamily A) (codomain p A B) point := by
  funext argument
  exact (congrArg (fun index => decode (B index))
    (comprehension_pair_inverse p A point argument)).symm

/-- Actual product type sets agree, not only their element cardinalities. -/
theorem piFamily_comparison (p : HSet.Presentation.{u}) {Γ : Code.{u}} (A : Family Γ)
    (B : Family (sigmaCode p A)) :
    decodedFamily (CodedFamilyTypeOperations.piFamily p A B) =
      FamilyCwf.piFamily p (decodedFamily A) (codomain p A B) := by
  funext point
  change decode (encode (materialPi p (CodedFamilyTypeOperations.fibreFamily p A B
    ((memberEquiv Γ).symm point)))) = _
  rw [decode_encode]
  change HSet.dependentProduct p _ _ = _
  rw [fibreFamily_comparison]
  rfl

/-- Actual dependent-sum sets likewise agree at the same decoded context. -/
theorem sigmaFamily_comparison (p : HSet.Presentation.{u}) {Γ : Code.{u}} (A : Family Γ)
    (B : Family (sigmaCode p A)) :
    decodedFamily (CodedFamilyTypeOperations.sigmaFamily p A B) =
      FamilyCwf.sigmaFamily p (decodedFamily A) (codomain p A B) := by
  funext point
  change decode (encode (materialSigma p (CodedFamilyTypeOperations.fibreFamily p A B
    ((memberEquiv Γ).symm point)))) = _
  rw [decode_encode]
  change sigmaSet (HSet.dependentReplacement p) HSet.union HSet.kuratowski _ _ = _
  rw [fibreFamily_comparison]
  rfl

/-- A dependent body is decoded at the corresponding actual extension point. -/
def body (p : HSet.Presentation.{u}) {Γ : Code.{u}} (A : Family Γ)
    (B : Family (sigmaCode p A)) (term : Section B) : FamilyCwf.Section (codomain p A B) :=
  fun point => memberEquiv (B ((comprehensionEquiv p A).symm point))
    (term ((comprehensionEquiv p A).symm point))

theorem body_pair_value (p : HSet.Presentation.{u}) {Γ : Code.{u}} (A : Family Γ)
    (B : Family (sigmaCode p A)) (term : Section B)
    (point : FamilyCwf.Elements (decode Γ)) (argument : FamilyCwf.Elements (decodedFamily A point)) :
    (body p A B term ((FamilyCwf.extensionDecode p (decodedFamily A)).symm ⟨point, argument⟩)).1 =
      decode (term (pairCode p A ⟨(memberEquiv Γ).symm point,
        (memberEquiv (A ((memberEquiv Γ).symm point))).symm argument⟩)).1 := by
  change decode (term ((comprehensionEquiv p A).symm
    ((FamilyCwf.extensionDecode p (decodedFamily A)).symm ⟨point, argument⟩))).1 = _
  exact congrArg (fun index => decode (term index).1) (comprehension_pair_inverse p A point argument)

/-- Abstraction agrees as an actual material graph in the corresponding
context. This compares the two constructed lambda operations. -/
theorem lam_value_comparison (p : HSet.Presentation.{u}) {Γ : Code.{u}} (A : Family Γ)
    (B : Family (sigmaCode p A)) (term : Section B)
    (point : FamilyCwf.Elements (decode Γ)) :
    decode (CodedFamilyTypeOperations.lam p (Γ := Γ) (A := A) (B := B) term
      ((memberEquiv Γ).symm point)).1 =
      (FamilyCwf.lam p (Γ := decode Γ) (A := decodedFamily A) (B := codomain p A B)
        (body p A B term) point).1 := by
  rw [CodedFamilyTypeOperations.lam_value]
  change HSet.image p (decodedFamily A point) (fun argument => HSet.kpair argument.1
    (sectionEquiv (CodedFamilyTypeOperations.fibreFamily p A B ((memberEquiv Γ).symm point))
      (fun x => term (pairCode p A ⟨(memberEquiv Γ).symm point, x⟩)) argument).1) =
    HSet.image p (decodedFamily A point) (fun argument => HSet.kpair argument.1
      (body p A B term ((FamilyCwf.extensionDecode p (decodedFamily A)).symm ⟨point, argument⟩)).1)
  apply congrArg (HSet.image p (decodedFamily A point))
  funext argument
  apply congrArg (HSet.kpair argument.1)
  rw [body_pair_value]
  have compared := sectionEquiv_apply_value
    (CodedFamilyTypeOperations.fibreFamily p A B ((memberEquiv Γ).symm point))
    (fun x => term (pairCode p A ⟨(memberEquiv Γ).symm point, x⟩))
    ((memberEquiv (A ((memberEquiv Γ).symm point))).symm argument)
  exact (congrArg (fun x =>
    (sectionEquiv (CodedFamilyTypeOperations.fibreFamily p A B ((memberEquiv Γ).symm point))
      (fun value => term (pairCode p A ⟨(memberEquiv Γ).symm point, value⟩)) x).1)
    ((memberEquiv (A ((memberEquiv Γ).symm point))).apply_symm_apply argument)).symm.trans compared

/-- Decoding any section retains its value at the inverse context point. -/
theorem section_value {Γ : Code.{u}} (A : Family Γ) (term : Section A)
    (point : FamilyCwf.Elements (decode Γ)) :
    (sectionEquiv A term point).1 = decode (term ((memberEquiv Γ).symm point)).1 := by
  have compared := sectionEquiv_apply_value A term ((memberEquiv Γ).symm point)
  exact (congrArg (fun point => (sectionEquiv A term point).1)
    ((memberEquiv Γ).apply_symm_apply point)).symm.trans compared

/-- A code-valued function is transported to the corresponding actual
material product family using the proved formation comparison. -/
def function (p : HSet.Presentation.{u}) {Γ : Code.{u}} (A : Family Γ)
    (B : Family (sigmaCode p A)) (term : Section (CodedFamilyTypeOperations.piFamily p A B)) :
    FamilyCwf.Section (FamilyCwf.piFamily p (decodedFamily A) (codomain p A B)) :=
  FamilyCwf.sectionTransport (piFamily_comparison p A B)
    (sectionEquiv (CodedFamilyTypeOperations.piFamily p A B) term)

theorem function_value (p : HSet.Presentation.{u}) {Γ : Code.{u}} (A : Family Γ)
    (B : Family (sigmaCode p A)) (term : Section (CodedFamilyTypeOperations.piFamily p A B))
    (point : FamilyCwf.Elements (decode Γ)) :
    (function p A B term point).1 = decode (term ((memberEquiv Γ).symm point)).1 := by
  rw [function, FamilyCwf.sectionTransport_value]
  exact section_value _ _ _

/-- The two lambda operations agree as dependent sections after the
specified product-family comparison. -/
theorem lam_comparison (p : HSet.Presentation.{u}) {Γ : Code.{u}} (A : Family Γ)
    (B : Family (sigmaCode p A)) (term : Section B) :
    function p A B (CodedFamilyTypeOperations.lam p (Γ := Γ) (A := A) (B := B) term) =
      FamilyCwf.lam p (Γ := decode Γ) (A := decodedFamily A) (B := codomain p A B)
        (body p A B term) := by
  funext point
  apply El.ext HSet.propositional
  rw [function_value]
  exact lam_value_comparison p A B term point

theorem app_value_comparison (p : HSet.Presentation.{u}) {Γ : Code.{u}} (A : Family Γ)
    (B : Family (sigmaCode p A)) (term : Section (CodedFamilyTypeOperations.piFamily p A B))
    (argument : Section A) (point : FamilyCwf.Elements (decode Γ)) :
    decode (CodedFamilyTypeOperations.app p (Γ := Γ) (A := A) (B := B) term argument
      ((memberEquiv Γ).symm point)).1 =
      (FamilyCwf.app p (Γ := decode Γ) (A := decodedFamily A) (B := codomain p A B)
        (function p A B term) (sectionEquiv A argument) point).1 := by
  rw [CodedFamilyTypeOperations.app_value, FamilyCwf.app_value, function_value, section_value]

/-- The decoded argument returns the same code at the inverse base point. -/
theorem argument_inverse {Γ : Code.{u}} (A : Family Γ) (term : Section A)
    (point : FamilyCwf.Elements (decode Γ)) :
    (memberEquiv (A ((memberEquiv Γ).symm point))).symm (sectionEquiv A term point) =
      term ((memberEquiv Γ).symm point) := by
  apply (memberEquiv (A ((memberEquiv Γ).symm point))).injective
  rw [Equiv.apply_symm_apply]
  apply El.ext HSet.propositional
  exact section_value A term point

/-- Application's dependent result type agrees under the same context and
argument comparison, rather than a separately chosen fibre equivalence. -/
theorem applicationFamily_comparison (p : HSet.Presentation.{u}) {Γ : Code.{u}} (A : Family Γ)
    (B : Family (sigmaCode p A)) (argument : Section A) :
    decodedFamily (B ∘ pairSubstitution p id A argument) =
      codomain p A B ∘ FamilyCwf.pair p id (decodedFamily A) (sectionEquiv A argument) := by
  funext point
  have paired := comprehension_pair_inverse p A point (sectionEquiv A argument point)
  rw [argument_inverse] at paired
  exact (congrArg (fun index => decode (B index)) paired).symm

/-- The complete application square compares actual dependent terms. -/
theorem app_comparison (p : HSet.Presentation.{u}) {Γ : Code.{u}} (A : Family Γ)
    (B : Family (sigmaCode p A)) (term : Section (CodedFamilyTypeOperations.piFamily p A B))
    (argument : Section A) :
    FamilyCwf.sectionTransport (applicationFamily_comparison p A B argument)
        (sectionEquiv (B ∘ pairSubstitution p id A argument)
          (CodedFamilyTypeOperations.app p (Γ := Γ) (A := A) (B := B) term argument)) =
      FamilyCwf.app p (Γ := decode Γ) (A := decodedFamily A) (B := codomain p A B)
        (function p A B term) (sectionEquiv A argument) := by
  funext point
  apply El.ext HSet.propositional
  rw [FamilyCwf.sectionTransport_value, section_value]
  exact app_value_comparison p A B term argument point

/-- Decode a dependent result at the corresponding actual argument. -/
def result (p : HSet.Presentation.{u}) {Γ : Code.{u}} (A : Family Γ)
    (B : Family (sigmaCode p A)) (argument : Section A)
    (term : Section (B ∘ pairSubstitution p id A argument)) :
    FamilyCwf.Section (codomain p A B ∘ FamilyCwf.pair p id (decodedFamily A) (sectionEquiv A argument)) :=
  FamilyCwf.sectionTransport (applicationFamily_comparison p A B argument)
    (sectionEquiv (B ∘ pairSubstitution p id A argument) term)

theorem result_value (p : HSet.Presentation.{u}) {Γ : Code.{u}} (A : Family Γ)
    (B : Family (sigmaCode p A)) (argument : Section A)
    (term : Section (B ∘ pairSubstitution p id A argument)) (point : FamilyCwf.Elements (decode Γ)) :
    (result p A B argument term point).1 = decode (term ((memberEquiv Γ).symm point)).1 := by
  rw [result, FamilyCwf.sectionTransport_value]
  exact section_value _ _ _

def sumValue (p : HSet.Presentation.{u}) {Γ : Code.{u}} (A : Family Γ)
    (B : Family (sigmaCode p A)) (term : Section (CodedFamilyTypeOperations.sigmaFamily p A B)) :
    FamilyCwf.Section (FamilyCwf.sigmaFamily p (decodedFamily A) (codomain p A B)) :=
  FamilyCwf.sectionTransport (sigmaFamily_comparison p A B)
    (sectionEquiv (CodedFamilyTypeOperations.sigmaFamily p A B) term)

theorem sumValue_value (p : HSet.Presentation.{u}) {Γ : Code.{u}} (A : Family Γ)
    (B : Family (sigmaCode p A)) (term : Section (CodedFamilyTypeOperations.sigmaFamily p A B))
    (point : FamilyCwf.Elements (decode Γ)) :
    (sumValue p A B term point).1 = decode (term ((memberEquiv Γ).symm point)).1 := by
  rw [sumValue, FamilyCwf.sectionTransport_value]
  exact section_value _ _ _

/-- Pairing commutes with the actual sum and dependent-result comparisons. -/
theorem sigmaPair_comparison (p : HSet.Presentation.{u}) {Γ : Code.{u}} (A : Family Γ)
    (B : Family (sigmaCode p A)) (first : Section A)
    (second : Section (B ∘ pairSubstitution p id A first)) :
    sumValue p A B (CodedFamilyTypeOperations.sigmaPair p (Γ := Γ) (A := A) (B := B) first second) =
      FamilyCwf.sigmaPair p (Γ := decode Γ) (A := decodedFamily A) (B := codomain p A B)
        (sectionEquiv A first) (result p A B first second) := by
  funext point
  apply El.ext HSet.propositional
  rw [sumValue_value, CodedFamilyTypeOperations.sigmaPair_value, FamilyCwf.sigmaPair_value,
    section_value, result_value]

theorem sigmaFirst_comparison (p : HSet.Presentation.{u}) {Γ : Code.{u}} (A : Family Γ)
    (B : Family (sigmaCode p A)) (term : Section (CodedFamilyTypeOperations.sigmaFamily p A B)) :
    sectionEquiv A (CodedFamilyTypeOperations.sigmaFirst p (Γ := Γ) (A := A) (B := B) term) =
      FamilyCwf.sigmaFirst p (Γ := decode Γ) (A := decodedFamily A) (B := codomain p A B)
        (sumValue p A B term) := by
  funext point
  apply El.ext HSet.propositional
  rw [section_value, CodedFamilyTypeOperations.sigmaFirst_value, FamilyCwf.sigmaFirst_value, sumValue_value]

private theorem materialMember_heq {first second : HSet.{u}} (same : first = second)
    (left : FamilyCwf.Elements first) (right : FamilyCwf.Elements second)
    (values : left.1 = right.1) : HEq left right := by
  cases same
  exact heq_of_eq (El.ext HSet.propositional values)

set_option maxHeartbeats 800000 in
/-- The dependent second projection agrees after transporting its result
family along the already proved first-projection comparison. -/
theorem sigmaSecond_comparison (p : HSet.Presentation.{u}) {Γ : Code.{u}} (A : Family Γ)
    (B : Family (sigmaCode p A)) (term : Section (CodedFamilyTypeOperations.sigmaFamily p A B)) :
    HEq (result p A B (CodedFamilyTypeOperations.sigmaFirst p (Γ := Γ) (A := A) (B := B) term)
        (CodedFamilyTypeOperations.sigmaSecond p (Γ := Γ) (A := A) (B := B) term))
      (FamilyCwf.sigmaSecond p (Γ := decode Γ) (A := decodedFamily A) (B := codomain p A B)
        (sumValue p A B term)) := by
  apply CodedFamilyCwf.dependentFunction_heq
  intro point
  apply materialMember_heq
    (congrArg (fun first => codomain p A B (FamilyCwf.pair p id (decodedFamily A) first point))
      (sigmaFirst_comparison p A B term))
  rw [result_value, CodedFamilyTypeOperations.sigmaSecond_value, FamilyCwf.sigmaSecond_value, sumValue_value]

end Mettapedia.TypeTheory.MaterialSets.Hypersets.CodedFamilyTypeComparison
