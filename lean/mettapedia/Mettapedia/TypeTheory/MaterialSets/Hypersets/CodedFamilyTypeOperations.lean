import Mettapedia.TypeTheory.MaterialSets.Hypersets.CodedFamilyCwf

/-!
# Dependent products and sums in the coded hyperset CwF

The existing material product and sum codes are formed pointwise over coded
context comprehension. Abstraction builds a code for the actual dependent
function graph; application decodes that graph at the supplied member.
Pairing retains both component codes. Formation commutes with the CwF's
actual extension substitution, and beta/eta retain complete member values.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.CodedFamilyTypeOperations
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualProductComparison
open Mettapedia.TypeTheory.ContextualSumComparison
open Mettapedia.TypeTheory.ContextualTypeOperations
open CodedFamilies CodedFamilyCwf
universe u

/-- The dependent result family above one point of the base context. -/
def fibreFamily (p : HSet.Presentation.{u}) {Γ : Code.{u}}
    (A : Family Γ) (B : Family (sigmaCode p A)) (γ : CodedFamilies.Members Γ) : Family (A γ) :=
  fun x => B (pairCode p A ⟨γ, x⟩)

def piFamily (p : HSet.Presentation.{u}) {Γ : Code.{u}}
    (A : Family Γ) (B : Family (sigmaCode p A)) : Family Γ :=
  fun γ => piCode p (fibreFamily p A B γ)

def sigmaFamily (p : HSet.Presentation.{u}) {Γ : Code.{u}}
    (A : Family Γ) (B : Family (sigmaCode p A)) : Family Γ :=
  fun γ => sigmaCode p (fibreFamily p A B γ)

theorem fibreFamily_substitution (p : HSet.Presentation.{u}) {Γ Δ : Code.{u}}
    (σ : CodedFamilyCwf.Substitution Γ Δ) (A : Family Δ) (B : Family (sigmaCode p A))
    (γ : CodedFamilies.Members Γ) :
    fibreFamily p A B (σ γ) =
      fibreFamily p (A ∘ σ) (B ∘ mapSigma p σ A) γ := by
  funext x
  exact (congrArg B (mapSigma_pair p σ A ⟨γ, x⟩)).symm

theorem piFamily_substitution (p : HSet.Presentation.{u}) {Γ Δ : Code.{u}}
    (σ : CodedFamilyCwf.Substitution Γ Δ) (A : Family Δ) (B : Family (sigmaCode p A)) :
    piFamily p A B ∘ σ = piFamily p (A ∘ σ) (B ∘ mapSigma p σ A) := by
  funext γ
  exact congrArg (piCode p) (fibreFamily_substitution p σ A B γ)

theorem sigmaFamily_substitution (p : HSet.Presentation.{u}) {Γ Δ : Code.{u}}
    (σ : CodedFamilyCwf.Substitution Γ Δ) (A : Family Δ) (B : Family (sigmaCode p A)) :
    sigmaFamily p A B ∘ σ = sigmaFamily p (A ∘ σ) (B ∘ mapSigma p σ A) := by
  funext γ
  exact congrArg (sigmaCode p) (fibreFamily_substitution p σ A B γ)

def lam (p : HSet.Presentation.{u}) {Γ : Code.{u}} {A : Family Γ}
    {B : Family (sigmaCode p A)} (body : Section B) : Section (piFamily p A B) :=
  fun γ => abstractPi p (fibreFamily p A B γ) (fun x => body (pairCode p A ⟨γ, x⟩))

def app (p : HSet.Presentation.{u}) {Γ : Code.{u}} {A : Family Γ}
    {B : Family (sigmaCode p A)} (function : Section (piFamily p A B)) (argument : Section A) :
    Section (B ∘ pairSubstitution p id A argument) :=
  fun γ => applyPi p (fibreFamily p A B γ) (function γ) (argument γ)

theorem app_lam (p : HSet.Presentation.{u}) {Γ : Code.{u}} {A : Family Γ}
    {B : Family (sigmaCode p A)} (body : Section B) (argument : Section A) :
    app p (lam p body) argument = fun γ => body (pairSubstitution p id A argument γ) := by
  funext γ
  exact applyPi_abstract p (fibreFamily p A B γ) _ _

/-- This decoder reads the actual code of a dependent pair. -/
def sigmaDecode (p : HSet.Presentation.{u}) {Γ : Code.{u}}
    (A : Family Γ) (B : Family (sigmaCode p A)) (γ : CodedFamilies.Members Γ) :
    CodedFamilies.Members (sigmaFamily p A B γ) ≃ Pairs (fibreFamily p A B γ) :=
  sigmaMembersEquiv p (fibreFamily p A B γ)

def sigmaPair (p : HSet.Presentation.{u}) {Γ : Code.{u}} {A : Family Γ}
    {B : Family (sigmaCode p A)} (first : Section A)
    (second : Section (B ∘ pairSubstitution p id A first)) : Section (sigmaFamily p A B) :=
  fun γ => pairCode p (fibreFamily p A B γ) ⟨first γ, second γ⟩

def sigmaFirst (p : HSet.Presentation.{u}) {Γ : Code.{u}} {A : Family Γ}
    {B : Family (sigmaCode p A)} (value : Section (sigmaFamily p A B)) : Section A :=
  fun γ => (sigmaDecode p A B γ (value γ)).1

def sigmaSecond (p : HSet.Presentation.{u}) {Γ : Code.{u}} {A : Family Γ}
    {B : Family (sigmaCode p A)} (value : Section (sigmaFamily p A B)) :
    Section (B ∘ pairSubstitution p id A (sigmaFirst p value)) :=
  fun γ => (sigmaDecode p A B γ (value γ)).2

theorem sigmaFirst_pair (p : HSet.Presentation.{u}) {Γ : Code.{u}} {A : Family Γ}
    {B : Family (sigmaCode p A)} (first : Section A)
    (second : Section (B ∘ pairSubstitution p id A first)) :
    sigmaFirst p (sigmaPair p first second) = first := by
  funext γ
  exact congrArg PSigma.fst ((sigmaDecode p A B γ).apply_symm_apply ⟨first γ, second γ⟩)

theorem sigmaSecond_pair_heq (p : HSet.Presentation.{u}) {Γ : Code.{u}} {A : Family Γ}
    {B : Family (sigmaCode p A)} (first : Section A)
    (second : Section (B ∘ pairSubstitution p id A first)) :
    HEq (sigmaSecond p (sigmaPair p first second)) second := by
  apply CodedFamilyCwf.dependentFunction_heq
  intro γ
  exact (PSigma.mk.inj_iff.mp ((sigmaDecode p A B γ).apply_symm_apply ⟨first γ, second γ⟩)).2

theorem sigma_eta (p : HSet.Presentation.{u}) {Γ : Code.{u}} {A : Family Γ}
    {B : Family (sigmaCode p A)} (value : Section (sigmaFamily p A B)) :
    sigmaPair p (sigmaFirst p value) (sigmaSecond p value) = value := by
  funext γ
  exact (sigmaDecode p A B γ).symm_apply_apply (value γ)

/-- Transporting fibre membership retains the very same valid code. -/
def memberTransport {first second : Code.{u}} (same : first = second)
    (value : CodedFamilies.Members first) : CodedFamilies.Members second := same ▸ value

theorem memberTransport_value {first second : Code.{u}} (same : first = second)
    (value : CodedFamilies.Members first) : (memberTransport same value).1 = value.1 := by
  cases same
  rfl

/-- Evaluate a contextual function on the generic argument in comprehension. -/
def evaluationBody (p : HSet.Presentation.{u}) {Γ : Code.{u}} {A : Family Γ}
    {B : Family (sigmaCode p A)} (function : Section (piFamily p A B)) : Section B :=
  fun point => memberTransport (congrArg B ((sigmaMembersEquiv p A).symm_apply_apply point))
    (applyPi p (fibreFamily p A B (projection p A point))
      (function (projection p A point)) (lastVariable p A point))

theorem evaluationBody_pair (p : HSet.Presentation.{u}) {Γ : Code.{u}} {A : Family Γ}
    {B : Family (sigmaCode p A)} (function : Section (piFamily p A B))
    (γ : CodedFamilies.Members Γ) (x : CodedFamilies.Members (A γ)) :
    evaluationBody p function (pairCode p A ⟨γ, x⟩) =
      applyPi p (fibreFamily p A B γ) (function γ) x := by
  apply Subtype.ext
  rw [evaluationBody, memberTransport_value]
  simp only [projection, lastVariable, pairCode]
  rw [(sigmaMembersEquiv p A).apply_symm_apply ⟨γ, x⟩]

theorem lam_eta (p : HSet.Presentation.{u}) {Γ : Code.{u}} {A : Family Γ}
    {B : Family (sigmaCode p A)} (function : Section (piFamily p A B)) :
    lam p (evaluationBody p function) = function := by
  funext γ
  apply (piMembersEquiv p (fibreFamily p A B γ)).injective
  change piMembersEquiv p _ ((piMembersEquiv p _).symm _) = _
  rw [Equiv.apply_symm_apply]
  funext x
  exact evaluationBody_pair p function γ x

theorem evaluationBody_lam (p : HSet.Presentation.{u}) {Γ : Code.{u}} {A : Family Γ}
    {B : Family (sigmaCode p A)} (body : Section B) : evaluationBody p (lam p body) = body := by
  funext point
  obtain ⟨⟨γ, x⟩, rfl⟩ := (sigmaMembersEquiv p A).symm.surjective point
  change evaluationBody p (lam p body) (pairCode p A ⟨γ, x⟩) = body (pairCode p A ⟨γ, x⟩)
  rw [evaluationBody_pair]
  exact applyPi_abstract p _ _ _

def piSectionEquiv (p : HSet.Presentation.{u}) {Γ : Code.{u}}
    (A : Family Γ) (B : Family (sigmaCode p A)) : Section B ≃ Section (piFamily p A B) where
  toFun := lam p
  invFun := evaluationBody p
  left_inv := evaluationBody_lam p
  right_inv := lam_eta p

private theorem abstractPi_heq (p : HSet.Presentation.{u}) {base : Code.{u}}
    {first second : Family base} (same : first = second)
    {left : Section first} {right : Section second} (sections : HEq left right) :
    HEq (abstractPi p first left) (abstractPi p second right) := by
  cases same
  cases sections
  rfl

private theorem applyPi_heq (p : HSet.Presentation.{u}) {base : Code.{u}}
    {first second : Family base} (same : first = second)
    {left : CodedFamilies.Members (piCode p first)}
    {right : CodedFamilies.Members (piCode p second)} (functions : HEq left right)
    (argument : CodedFamilies.Members base) :
    HEq (applyPi p first left argument) (applyPi p second right argument) := by
  cases same
  cases functions
  rfl

private theorem section_at_heq {Γ : Code.{u}} {first second : Family Γ}
    (families : first = second) {left : Section first} {right : Section second}
    (sections : HEq left right) (point : CodedFamilies.Members Γ) :
    HEq (left point) (right point) := by
  cases families
  cases sections
  rfl

theorem lam_substitution (p : HSet.Presentation.{u}) {Γ Δ : Code.{u}}
    (σ : CodedFamilyCwf.Substitution Γ Δ) {A : Family Δ} {B : Family (sigmaCode p A)}
    (body : Section B) :
    HEq (fun γ => lam p body (σ γ)) (lam p (fun point => body (mapSigma p σ A point))) := by
  apply CodedFamilyCwf.dependentFunction_heq
  intro γ
  apply abstractPi_heq p (fibreFamily_substitution p σ A B γ)
  apply CodedFamilyCwf.dependentFunction_heq
  intro x
  exact congr_arg_heq body (mapSigma_pair p σ A ⟨γ, x⟩).symm

theorem app_substitution (p : HSet.Presentation.{u}) {Γ Δ : Code.{u}}
    (σ : CodedFamilyCwf.Substitution Γ Δ) {A : Family Δ} {B : Family (sigmaCode p A)}
    (function : Section (piFamily p A B)) (argument : Section A)
    (reindexed : Section (piFamily p (A ∘ σ) (B ∘ mapSigma p σ A)))
    (same : HEq (fun γ => function (σ γ)) reindexed) :
    HEq (fun γ => app p function argument (σ γ))
      (app p reindexed (fun γ => argument (σ γ))) := by
  apply CodedFamilyCwf.dependentFunction_heq
  intro γ
  exact applyPi_heq p (fibreFamily_substitution p σ A B γ)
    (section_at_heq (piFamily_substitution p σ A B) same γ) (argument (σ γ))

private theorem pairCode_heq (p : HSet.Presentation.{u}) {base : Code.{u}}
    {first second : Family base} (same : first = second)
    (point : CodedFamilies.Members base) {left : CodedFamilies.Members (first point)}
    {right : CodedFamilies.Members (second point)} (values : HEq left right) :
    HEq (pairCode p first ⟨point, left⟩) (pairCode p second ⟨point, right⟩) := by
  cases same
  cases values
  rfl

private theorem sigmaFirst_eq (p : HSet.Presentation.{u}) {base : Code.{u}}
    {first second : Family base} (same : first = second)
    {left : CodedFamilies.Members (sigmaCode p first)}
    {right : CodedFamilies.Members (sigmaCode p second)} (values : HEq left right) :
    (sigmaMembersEquiv p first left).1 = (sigmaMembersEquiv p second right).1 := by
  cases same
  cases values
  rfl


theorem argumentFamily_substitution (p : HSet.Presentation.{u}) {Γ Δ : Code.{u}}
    (σ : CodedFamilyCwf.Substitution Γ Δ) (A : Family Δ) (B : Family (sigmaCode p A))
    (argument : Section A) :
    (B ∘ pairSubstitution p id A argument) ∘ σ =
      (B ∘ mapSigma p σ A) ∘ pairSubstitution p id (A ∘ σ) (fun γ => argument (σ γ)) := by
  funext γ
  exact (congrArg B (mapSigma_pair p σ A ⟨γ, argument (σ γ)⟩)).symm

theorem sigmaPair_substitution (p : HSet.Presentation.{u}) {Γ Δ : Code.{u}}
    (σ : CodedFamilyCwf.Substitution Γ Δ) {A : Family Δ} {B : Family (sigmaCode p A)}
    (first : Section A) (second : Section (B ∘ pairSubstitution p id A first))
    (reindexed : Section ((B ∘ mapSigma p σ A) ∘
      pairSubstitution p id (A ∘ σ) (fun γ => first (σ γ))))
    (same : HEq (fun γ => second (σ γ)) reindexed) :
    HEq (fun γ => sigmaPair p first second (σ γ))
      (sigmaPair p (fun γ => first (σ γ)) reindexed) := by
  apply CodedFamilyCwf.dependentFunction_heq
  intro γ
  exact pairCode_heq p (fibreFamily_substitution p σ A B γ) (first (σ γ))
    (section_at_heq (argumentFamily_substitution p σ A B first) same γ)

theorem sigmaFirst_substitution (p : HSet.Presentation.{u}) {Γ Δ : Code.{u}}
    (σ : CodedFamilyCwf.Substitution Γ Δ) {A : Family Δ} {B : Family (sigmaCode p A)}
    (value : Section (sigmaFamily p A B))
    (reindexed : Section (sigmaFamily p (A ∘ σ) (B ∘ mapSigma p σ A)))
    (same : HEq (fun γ => value (σ γ)) reindexed) :
    (fun γ => sigmaFirst p value (σ γ)) = sigmaFirst p reindexed := by
  funext γ
  exact sigmaFirst_eq p (fibreFamily_substitution p σ A B γ)
    (section_at_heq (sigmaFamily_substitution p σ A B) same γ)

private theorem section_heq_of_values {Γ : Code.{u}} {first second : Family Γ}
    (families : first = second) {left : Section first} {right : Section second}
    (values : ∀ point, (left point).1 = (right point).1) : HEq left right := by
  cases families
  exact heq_of_eq (funext (fun point => Subtype.ext (values point)))

private theorem sigmaSecond_value_eq (p : HSet.Presentation.{u}) {base : Code.{u}}
    {first second : Family base} (same : first = second)
    {left : CodedFamilies.Members (sigmaCode p first)}
    {right : CodedFamilies.Members (sigmaCode p second)} (values : HEq left right) :
    (sigmaMembersEquiv p first left).2.1 = (sigmaMembersEquiv p second right).2.1 := by
  cases same
  cases values
  rfl

section SecondProjectionSubstitution
attribute [local irreducible] CodedFamilies.sigmaCode CodedFamilies.sigmaMembersEquiv
set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 800000 in
theorem sigmaSecond_substitution (p : HSet.Presentation.{u}) {Γ Δ : Code.{u}}
    (σ : CodedFamilyCwf.Substitution Γ Δ) {A : Family Δ} {B : Family (sigmaCode p A)}
    (value : Section (sigmaFamily p A B))
    (reindexed : Section (sigmaFamily p (A ∘ σ) (B ∘ mapSigma p σ A)))
    (same : HEq (fun γ => value (σ γ)) reindexed) :
    HEq (fun γ => sigmaSecond p (Γ := Δ) (A := A) (B := B) value (σ γ))
      (sigmaSecond p (Γ := Γ) (A := A ∘ σ) (B := B ∘ mapSigma p σ A) reindexed) := by
  have firsts := sigmaFirst_substitution p (Γ := Γ) (Δ := Δ) σ (A := A) (B := B) value reindexed same
  have families :
      (B ∘ pairSubstitution p id A (sigmaFirst p (A := A) (B := B) value)) ∘ σ =
        (B ∘ mapSigma p σ A) ∘ pairSubstitution p id (A ∘ σ)
          (sigmaFirst p (A := A ∘ σ) (B := B ∘ mapSigma p σ A) reindexed) := by
    rw [argumentFamily_substitution, firsts]
  apply section_heq_of_values (Γ := Γ) families
  intro γ
  dsimp only [sigmaSecond, sigmaDecode]
  have pointValues : HEq (value (σ γ)) (reindexed γ) :=
    section_at_heq (Γ := Γ)
      (first := sigmaFamily p A B ∘ σ)
      (second := sigmaFamily p (A ∘ σ) (B ∘ mapSigma p σ A))
      (sigmaFamily_substitution p σ A B) same γ
  exact sigmaSecond_value_eq p (base := A (σ γ))
    (first := fibreFamily p A B (σ γ))
    (second := fibreFamily p (A ∘ σ) (B ∘ mapSigma p σ A) γ)
    (fibreFamily_substitution p σ A B γ)
    (left := value (σ γ)) (right := reindexed γ)
    pointValues

end SecondProjectionSubstitution

/-- The operations inhabit the existing product interface at this same CwF. -/
def codedProducts (p : HSet.Presentation.{u}) : DependentProductBeta (codedCwf p) where
  pi := piFamily p
  lam := lam p
  app := app p
  beta := app_lam p

def codedSums (p : HSet.Presentation.{u}) : DependentSumBeta (codedCwf p) where
  sigma := sigmaFamily p
  pair := sigmaPair p
  fst := sigmaFirst p
  snd := sigmaSecond p
  fst_pair := sigmaFirst_pair p
  snd_pair := sigmaSecond_pair_heq p

/-- Formation uses the CwF's canonical comprehension map. -/
theorem codedProducts_formation_substitution (p : HSet.Presentation.{u})
    {Γ Δ : (codedCwf p).Ctx} (σ : (codedCwf p).Sub Γ Δ)
    (A : (codedCwf p).Ty Δ) (B : (codedCwf p).Ty ((codedCwf p).ext Δ A)) :
    (codedCwf p).tySub ((codedProducts p).pi A B) σ =
      (codedProducts p).pi ((codedCwf p).tySub A σ)
        ((codedCwf p).tySub B (TypeOver.extensionSubstitution σ A)) :=
  piFamily_substitution p σ A B

theorem codedSums_formation_substitution (p : HSet.Presentation.{u})
    {Γ Δ : (codedCwf p).Ctx} (σ : (codedCwf p).Sub Γ Δ)
    (A : (codedCwf p).Ty Δ) (B : (codedCwf p).Ty ((codedCwf p).ext Δ A)) :
    (codedCwf p).tySub ((codedSums p).sigma A B) σ =
      (codedSums p).sigma ((codedCwf p).tySub A σ)
        ((codedCwf p).tySub B (TypeOver.extensionSubstitution σ A)) :=
  sigmaFamily_substitution p σ A B

def codedPiOperations (p : HSet.Presentation.{u}) : PiOperations (codedCwf p) :=
  PiOperations.ofQualified (codedProducts p)

set_option maxHeartbeats 800000 in
/-- Both introduction and elimination commute with the same substitution
that transports the domain and dependent codomain. -/
theorem codedPiOperations_substitution (p : HSet.Presentation.{u}) :
    StrictPiSubstitution (codedPiOperations p) := by
  dsimp only [StrictPiSubstitution, StrictPiFormationSubstitution, codedPiOperations,
    PiOperations.ofQualified, codedProducts, codedCwf, TypeOver.extensionSubstitution]
  refine ⟨?_, ?_, ?_⟩
  · intro Γ Δ σ A B
    exact piFamily_substitution p σ A B
  · intro Γ Δ σ A B body
    exact lam_substitution p (Γ := Γ) (Δ := Δ) σ (A := A) (B := B) body
  · intro Γ Δ σ A B function argument reindexed same
    exact app_substitution p (Γ := Γ) (Δ := Δ) σ (A := A) (B := B) function argument reindexed same

def codedSigmaOperations (p : HSet.Presentation.{u}) : SigmaOperations (codedCwf p) :=
  SigmaOperations.ofQualified (codedSums p)

set_option maxHeartbeats 800000 in
/-- Pairing and both dependent projections preserve their complete values
under the canonical comprehension substitution. -/
theorem codedSigmaOperations_substitution (p : HSet.Presentation.{u}) :
    StrictSigmaSubstitution (codedSigmaOperations p) := by
  dsimp only [StrictSigmaSubstitution, StrictSigmaFormationSubstitution, codedSigmaOperations,
    SigmaOperations.ofQualified, codedSums, codedCwf, TypeOver.extensionSubstitution,
    selfExtend]
  refine ⟨?_, ?_, ?_⟩
  · intro Γ Δ σ A B
    exact sigmaFamily_substitution p σ A B
  · intro Γ Δ σ A B first second reindexed same
    exact sigmaPair_substitution p (Γ := Γ) (Δ := Δ) σ (A := A) (B := B) first second reindexed same
  · intro Γ Δ σ A B value reindexed same
    exact ⟨heq_of_eq (sigmaFirst_substitution p (Γ := Γ) (Δ := Δ) σ (A := A) (B := B) value reindexed same),
      sigmaSecond_substitution p (Γ := Γ) (Δ := Δ) σ (A := A) (B := B) value reindexed same⟩

/-- Abstraction decodes to the actual material function graph. -/
theorem lam_value (p : HSet.Presentation.{u}) {Γ : Code.{u}} {A : Family Γ}
    {B : Family (sigmaCode p A)} (body : Section B) (γ : CodedFamilies.Members Γ) :
    decode (lam p body γ).1 =
      functionGraph (HSet.dependentReplacement p) HSet.kuratowski
        (sectionEquiv (fibreFamily p A B γ) (fun x => body (pairCode p A ⟨γ, x⟩))) :=
  abstractPi_value p _ _

/-- Application reads the actual material graph at the decoded argument. -/
theorem app_value (p : HSet.Presentation.{u}) {Γ : Code.{u}} {A : Family Γ}
    {B : Family (sigmaCode p A)} (function : Section (piFamily p A B)) (argument : Section A)
    (γ : CodedFamilies.Members Γ) :
    decode (app p function argument γ).1 =
      graphValue (HSet.dependentReplacement p) HSet.union HSet.kuratowski HSet.separation
        (decode (function γ).1) (decode (argument γ).1) := by
  refine (applyPi_value p (fibreFamily p A B γ) (function γ) (argument γ)).trans ?_
  change graphValue (HSet.dependentReplacement p) HSet.union HSet.kuratowski HSet.separation
    ((encodedMemberEquiv (materialPi p (fibreFamily p A B γ))) (function γ)).1
    (memberEquiv (A γ) (argument γ)).1 = _
  rw [encodedMemberEquiv_value, memberEquiv_value]

/-- Pair introduction retains the actual decoded component values. -/
theorem sigmaPair_value (p : HSet.Presentation.{u}) {Γ : Code.{u}} {A : Family Γ}
    {B : Family (sigmaCode p A)} (first : Section A)
    (second : Section (B ∘ pairSubstitution p id A first)) (γ : CodedFamilies.Members Γ) :
    decode (sigmaPair p first second γ).1 = HSet.kpair (decode (first γ).1) (decode (second γ).1) :=
  pairCode_value p _ _

private theorem sigmaMember_first_value (p : HSet.Presentation.{u}) {base : Code.{u}}
    (family : Family base) (value : CodedFamilies.Members (sigmaCode p family)) :
    decode (sigmaMembersEquiv p family value).1.1 = HSet.fst (decode value.1) := by
  obtain ⟨pair, rfl⟩ := (sigmaMembersEquiv p family).symm.surjective value
  change decode ((sigmaMembersEquiv p family) ((sigmaMembersEquiv p family).symm pair)).1.1 =
    HSet.fst (decode (pairCode p family pair).1)
  rw [(sigmaMembersEquiv p family).apply_symm_apply pair, pairCode_value, HSet.fst_kpair]

private theorem sigmaMember_second_value (p : HSet.Presentation.{u}) {base : Code.{u}}
    (family : Family base) (value : CodedFamilies.Members (sigmaCode p family)) :
    decode (sigmaMembersEquiv p family value).2.1 = HSet.snd (decode value.1) := by
  obtain ⟨pair, rfl⟩ := (sigmaMembersEquiv p family).symm.surjective value
  change decode ((sigmaMembersEquiv p family) ((sigmaMembersEquiv p family).symm pair)).2.1 =
    HSet.snd (decode (pairCode p family pair).1)
  calc
    _ = decode pair.2.1 := congrArg (fun pair : Pairs family => decode pair.2.1)
      ((sigmaMembersEquiv p family).apply_symm_apply pair)
    _ = _ := by rw [pairCode_value, HSet.snd_kpair]

/-- The coded first projection reads the actual first hyperset component. -/
theorem sigmaFirst_value (p : HSet.Presentation.{u}) {Γ : Code.{u}} {A : Family Γ}
    {B : Family (sigmaCode p A)} (value : Section (sigmaFamily p A B)) (point : CodedFamilies.Members Γ) :
    decode (sigmaFirst p (Γ := Γ) (A := A) (B := B) value point).1 =
      HSet.fst (decode (value point).1) :=
  sigmaMember_first_value p (fibreFamily p A B point) (value point)

/-- The second projection preserves its value despite its dependent fibre. -/
theorem sigmaSecond_value (p : HSet.Presentation.{u}) {Γ : Code.{u}} {A : Family Γ}
    {B : Family (sigmaCode p A)} (value : Section (sigmaFamily p A B)) (point : CodedFamilies.Members Γ) :
    decode (sigmaSecond p (Γ := Γ) (A := A) (B := B) value point).1 =
      HSet.snd (decode (value point).1) :=
  sigmaMember_second_value p (fibreFamily p A B point) (value point)

namespace Controls

def domain : Family terminalContext.{u} := fun _ => quineDomain

def codomain (p : HSet.Presentation.{u}) : Family (sigmaCode p domain.{u}) := fun _ => quineDomain

def body (p : HSet.Presentation.{u}) : Section (codomain p) := fun _ => quineArgument

def argument : Section domain.{u} := fun _ => quineArgument

/-- Actual coded abstraction and application retain a cyclic guest value. -/
theorem application_quine (p : HSet.Presentation.{u}) (γ : CodedFamilies.Members terminalContext.{u}) :
    decode (app p (A := domain) (B := codomain p) (lam p (body p)) argument γ).1 = HSet.quineAtom := by
  have beta := congrFun (app_lam p (A := domain) (B := codomain p) (body p) argument) γ
  exact (congrArg (fun value => decode value.1) beta).trans quineArgument_value

/-- Empty dependent fibres remain empty in this CwF even though its contexts
can contain cycles. There is no total-choice operation on all such types. -/
theorem empty_codomain_no_section (p : HSet.Presentation.{u}) :
    ¬ Nonempty (Section (piFamily p domain.{u} (fun _ => encode (∅ : HSet.{u})))) := by
  rintro ⟨function⟩
  let point : CodedFamilies.Members terminalContext.{u} := toTerminal quineDomain quineArgument
  exact no_piCode_of_empty_fibre p (fibreFamily p domain (fun _ => encode (∅ : HSet.{u})) point)
    quineArgument (decode_encode _) ⟨function point⟩

end Controls

end Mettapedia.TypeTheory.MaterialSets.Hypersets.CodedFamilyTypeOperations
