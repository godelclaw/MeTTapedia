import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalRelationOperator
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16OrbitCarrierBridge

/-!
# The physical relation operator on genuine field-label orbits

The exact contextual target is sent to the ordinary quotient by simultaneous
field relabeling.  The resulting free rational module is the honest finite
carrier counted by the proved cycle-index character theorem.  Its signed
hypercubic action is packaged as a representation, the quotient map is an
intertwiner, and the off-shell/on-shell physical relation operator is composed
with that map.

No physical rank or conditioning claim is made in this file.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalOrbitOperator

open V14HypercubicFDCensus
open HypercubicRawFDCharacterCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16OrbitCarrierBridge
open HypercubicDimension16PhysicalRelationOperator

/-! ## The exact dependent orbit carrier -/

abbrev ExactFieldRelabelOrbitCarrier :=
  (fieldCount : Fin 9) ×'
    FieldRelabelOrbitCarrier fieldCount.1
      (dimension16DerivativeCount fieldCount)

abbrev ExactFieldRelabelOrbitSpace :=
  ExactFieldRelabelOrbitCarrier →₀ ℚ

/-- The ordinary field-label orbit of one oriented local monomial. -/
def exactFieldRelabelOrbitOfOriented
    (target : ExactOrientedLocalCarrier) :
    ExactFieldRelabelOrbitCarrier :=
  ⟨target.1,
    Quotient.mk _
      (orientedLocalSectorEquivLabeled target.1.1
        (dimension16DerivativeCount target.1) target.2)⟩

def normalizeExactFieldRelabelBasis
    (target : ExactOrientedLocalCarrier) :
    ExactFieldRelabelOrbitSpace :=
  Finsupp.single (exactFieldRelabelOrbitOfOriented target) 1

/-- Linear quotient map from labeled oriented local monomials to genuine
field-label orbits. -/
def normalizeExactFieldRelabel :
    ExactOrientedLocalSpace →ₗ[ℚ] ExactFieldRelabelOrbitSpace :=
  Finsupp.linearCombination ℚ normalizeExactFieldRelabelBasis

@[simp] theorem normalizeExactFieldRelabel_single
    (target : ExactOrientedLocalCarrier) (coefficient : ℚ) :
    normalizeExactFieldRelabel (Finsupp.single target coefficient) =
      coefficient • normalizeExactFieldRelabelBasis target := by
  simp [normalizeExactFieldRelabel]

/-- Every genuine field-label orbit basis vector has a labeled oriented
preimage; the quotient map misses no column. -/
theorem normalizeExactFieldRelabel_surjective :
    Function.Surjective normalizeExactFieldRelabel := by
  intro value
  induction value using Finsupp.induction_linear with
  | zero =>
      exact ⟨0, by simp⟩
  | add left right hleft hright =>
      rcases hleft with ⟨leftSource, hleft⟩
      rcases hright with ⟨rightSource, hright⟩
      exact ⟨leftSource + rightSource, by simp [hleft, hright]⟩
  | single target coefficient =>
      rcases target with ⟨fieldCount, orbit⟩
      refine Quotient.inductionOn orbit ?_
      intro labeled
      let oriented :=
        (orientedLocalSectorEquivLabeled fieldCount.1
          (dimension16DerivativeCount fieldCount)).symm labeled
      refine ⟨Finsupp.single
        (⟨fieldCount, oriented⟩ : ExactOrientedLocalCarrier)
        coefficient, ?_⟩
      rw [normalizeExactFieldRelabel_single]
      simp [normalizeExactFieldRelabelBasis,
        exactFieldRelabelOrbitOfOriented, oriented]

/-! ## Exact linear kernel of field relabeling -/

def exactOrientedLocalRelabel
    (target : ExactOrientedLocalCarrier)
    (rename : Equiv.Perm (Fin target.1.1)) :
    ExactOrientedLocalCarrier :=
  ⟨target.1, orientedLocalRelabel rename target.2⟩

theorem exactFieldRelabelOrbitOfOriented_relabel
    (target : ExactOrientedLocalCarrier)
    (rename : Equiv.Perm (Fin target.1.1)) :
    exactFieldRelabelOrbitOfOriented
        (exactOrientedLocalRelabel target rename) =
      exactFieldRelabelOrbitOfOriented target := by
  rcases target with ⟨fieldCount, sector⟩
  apply congrArg
    (fun orbit : FieldRelabelOrbitCarrier fieldCount.1
        (dimension16DerivativeCount fieldCount) =>
      (⟨fieldCount, orbit⟩ : ExactFieldRelabelOrbitCarrier))
  apply Quotient.sound
  change MulAction.orbitRel (Equiv.Perm (Fin fieldCount.1))
    (LabeledLocalWordSector fieldCount.1
      (dimension16DerivativeCount fieldCount))
    (orientedLocalSectorEquivLabeled fieldCount.1
      (dimension16DerivativeCount fieldCount)
      (orientedLocalRelabel rename sector))
    (orientedLocalSectorEquivLabeled fieldCount.1
      (dimension16DerivativeCount fieldCount) sector)
  rw [orientedLocalSectorEquivLabeled_relabel,
    MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨rename, rfl⟩

structure ExactFieldRelabelRelationSite where
  source : ExactOrientedLocalCarrier
  rename : Equiv.Perm (Fin source.1.1)

def exactFieldRelabelRelationRow
    (site : ExactFieldRelabelRelationSite) :
    ExactOrientedLocalSpace :=
  Finsupp.single site.source 1 -
    Finsupp.single
      (exactOrientedLocalRelabel site.source site.rename) 1

def exactFieldRelabelRelationSubmodule :
    Submodule ℚ ExactOrientedLocalSpace :=
  Submodule.span ℚ (Set.range exactFieldRelabelRelationRow)

theorem normalizeExactFieldRelabel_relationRow
    (site : ExactFieldRelabelRelationSite) :
    normalizeExactFieldRelabel
        (exactFieldRelabelRelationRow site) = 0 := by
  simp [exactFieldRelabelRelationRow,
    normalizeExactFieldRelabelBasis,
    exactFieldRelabelOrbitOfOriented_relabel]

theorem exactFieldRelabelRelationSubmodule_le_kernel :
    exactFieldRelabelRelationSubmodule ≤
      LinearMap.ker normalizeExactFieldRelabel := by
  unfold exactFieldRelabelRelationSubmodule
  rw [Submodule.span_le]
  rintro value ⟨site, rfl⟩
  exact LinearMap.mem_ker.mpr
    (normalizeExactFieldRelabel_relationRow site)

/-- Chosen oriented representative of an orbit. It is used only to prove the
kernel theorem; rank certificates remain stated on the quotient carrier. -/
def exactOrientedRepresentative
    (target : ExactFieldRelabelOrbitCarrier) :
    ExactOrientedLocalCarrier :=
  ⟨target.1,
    (orientedLocalSectorEquivLabeled target.1.1
      (dimension16DerivativeCount target.1)).symm target.2.out⟩

theorem exactFieldRelabelOrbitOfOriented_representative
    (target : ExactFieldRelabelOrbitCarrier) :
    exactFieldRelabelOrbitOfOriented
        (exactOrientedRepresentative target) = target := by
  rcases target with ⟨fieldCount, orbit⟩
  apply congrArg
    (fun result : FieldRelabelOrbitCarrier fieldCount.1
        (dimension16DerivativeCount fieldCount) =>
      (⟨fieldCount, result⟩ : ExactFieldRelabelOrbitCarrier))
  change Quotient.mk _
      (orientedLocalSectorEquivLabeled fieldCount.1
        (dimension16DerivativeCount fieldCount)
        ((orientedLocalSectorEquivLabeled fieldCount.1
          (dimension16DerivativeCount fieldCount)).symm orbit.out)) = orbit
  rw [(orientedLocalSectorEquivLabeled fieldCount.1
    (dimension16DerivativeCount fieldCount)).apply_symm_apply]
  exact Quotient.out_eq orbit

def embedExactFieldRelabelBasis
    (target : ExactFieldRelabelOrbitCarrier) :
    ExactOrientedLocalSpace :=
  Finsupp.single (exactOrientedRepresentative target) 1

def embedExactFieldRelabel :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] ExactOrientedLocalSpace :=
  Finsupp.linearCombination ℚ embedExactFieldRelabelBasis

@[simp] theorem embedExactFieldRelabel_single
    (target : ExactFieldRelabelOrbitCarrier) (coefficient : ℚ) :
    embedExactFieldRelabel (Finsupp.single target coefficient) =
      coefficient • embedExactFieldRelabelBasis target := by
  simp [embedExactFieldRelabel]

theorem normalizeExactFieldRelabel_embedExactFieldRelabel
    (value : ExactFieldRelabelOrbitSpace) :
    normalizeExactFieldRelabel (embedExactFieldRelabel value) = value := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [map_add, hleft, hright]
  | single target coefficient =>
      simp [embedExactFieldRelabelBasis,
        normalizeExactFieldRelabelBasis,
        exactFieldRelabelOrbitOfOriented_representative]

theorem exactOrientedRepresentative_exists_relabel
    (source : ExactOrientedLocalCarrier) :
    ∃ rename : Equiv.Perm
        (Fin (exactOrientedRepresentative
          (exactFieldRelabelOrbitOfOriented source)).1.1),
      exactOrientedLocalRelabel
          (exactOrientedRepresentative
            (exactFieldRelabelOrbitOfOriented source)) rename = source := by
  rcases source with ⟨fieldCount, sector⟩
  let bridge := orientedLocalSectorEquivLabeled fieldCount.1
    (dimension16DerivativeCount fieldCount)
  let orbit : FieldRelabelOrbitCarrier fieldCount.1
      (dimension16DerivativeCount fieldCount) :=
    Quotient.mk _ (bridge sector)
  have hsame : MulAction.orbitRel (Equiv.Perm (Fin fieldCount.1))
      (LabeledLocalWordSector fieldCount.1
        (dimension16DerivativeCount fieldCount))
      (bridge sector) orbit.out := by
    apply Quotient.eq''.mp
    exact (Quotient.out_eq' orbit).symm
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hsame
  rcases hsame with ⟨rename, hrename⟩
  refine ⟨rename, ?_⟩
  apply congrArg (fun oriented : OrientedLocalSector fieldCount.1
      (dimension16DerivativeCount fieldCount) =>
    (⟨fieldCount, oriented⟩ : ExactOrientedLocalCarrier))
  apply bridge.injective
  change bridge
      (orientedLocalRelabel rename (bridge.symm orbit.out)) =
    bridge sector
  rw [orientedLocalSectorEquivLabeled_relabel,
    bridge.apply_symm_apply]
  exact hrename

theorem single_sub_exactOrientedRepresentative_mem
    (source : ExactOrientedLocalCarrier) :
    Finsupp.single source 1 -
        Finsupp.single
          (exactOrientedRepresentative
            (exactFieldRelabelOrbitOfOriented source)) 1 ∈
      exactFieldRelabelRelationSubmodule := by
  rcases exactOrientedRepresentative_exists_relabel source with
    ⟨rename, hrename⟩
  let site : ExactFieldRelabelRelationSite :=
    { source := exactOrientedRepresentative
        (exactFieldRelabelOrbitOfOriented source)
      rename := rename }
  have hrow : exactFieldRelabelRelationRow site ∈
      exactFieldRelabelRelationSubmodule :=
    Submodule.subset_span ⟨site, rfl⟩
  have hneg := exactFieldRelabelRelationSubmodule.neg_mem hrow
  simpa [exactFieldRelabelRelationRow, site, hrename] using hneg

theorem value_sub_embed_normalize_mem_fieldRelabelRelations
    (value : ExactOrientedLocalSpace) :
    value - embedExactFieldRelabel
        (normalizeExactFieldRelabel value) ∈
      exactFieldRelabelRelationSubmodule := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      have hadd := exactFieldRelabelRelationSubmodule.add_mem hleft hright
      have hdecompose :
          left + right - embedExactFieldRelabel
              (normalizeExactFieldRelabel (left + right)) =
            (left - embedExactFieldRelabel
                (normalizeExactFieldRelabel left)) +
              (right - embedExactFieldRelabel
                (normalizeExactFieldRelabel right)) := by
        simp only [map_add]
        abel
      rw [hdecompose]
      exact hadd
  | single source coefficient =>
      have hbase := single_sub_exactOrientedRepresentative_mem source
      have hscaled := exactFieldRelabelRelationSubmodule.smul_mem
        coefficient hbase
      simpa [normalizeExactFieldRelabelBasis,
        embedExactFieldRelabelBasis, smul_sub] using hscaled

/-- Explicit simultaneous field-renaming rows span exactly the kernel of the
ordinary field-label orbit map. -/
theorem ker_normalizeExactFieldRelabel_eq_relationSubmodule :
    LinearMap.ker normalizeExactFieldRelabel =
      exactFieldRelabelRelationSubmodule := by
  apply le_antisymm
  · intro value membership
    have hresidual :=
      value_sub_embed_normalize_mem_fieldRelabelRelations value
    have hzero := LinearMap.mem_ker.mp membership
    rw [hzero, map_zero, sub_zero] at hresidual
    exact hresidual
  · exact exactFieldRelabelRelationSubmodule_le_kernel

def exactFieldRelabelRelationQuotientEquiv :
    (ExactOrientedLocalSpace ⧸ exactFieldRelabelRelationSubmodule) ≃ₗ[ℚ]
      ExactFieldRelabelOrbitSpace :=
  (Submodule.quotEquivOfEq exactFieldRelabelRelationSubmodule
      (LinearMap.ker normalizeExactFieldRelabel)
      ker_normalizeExactFieldRelabel_eq_relationSubmodule.symm).trans
    (normalizeExactFieldRelabel.quotKerEquivOfSurjective
      normalizeExactFieldRelabel_surjective)

/-! ## Signed hypercubic representation on the orbit module -/

def exactFieldRelabelOrbitAct (h : Hypercubic4)
    (target : ExactFieldRelabelOrbitCarrier) :
    ExactFieldRelabelOrbitCarrier :=
  ⟨target.1, target.2.hypercubicAct h⟩

def exactFieldRelabelOrbitTensorSign (h : Hypercubic4)
    (target : ExactFieldRelabelOrbitCarrier) : ℚ :=
  target.2.tensorSign h

@[simp] theorem exactFieldRelabelOrbitAct_one
    (target : ExactFieldRelabelOrbitCarrier) :
    exactFieldRelabelOrbitAct 1 target = target := by
  rcases target with ⟨fieldCount, orbit⟩
  exact congrArg
    (fun result : FieldRelabelOrbitCarrier fieldCount.1
        (dimension16DerivativeCount fieldCount) =>
      (⟨fieldCount, result⟩ : ExactFieldRelabelOrbitCarrier))
    (FieldRelabelOrbitCarrier.hypercubicAct_one orbit)

theorem exactFieldRelabelOrbitAct_mul
    (left right : Hypercubic4)
    (target : ExactFieldRelabelOrbitCarrier) :
    exactFieldRelabelOrbitAct (left * right) target =
      exactFieldRelabelOrbitAct left
        (exactFieldRelabelOrbitAct right target) := by
  rcases target with ⟨fieldCount, orbit⟩
  exact congrArg
    (fun result : FieldRelabelOrbitCarrier fieldCount.1
        (dimension16DerivativeCount fieldCount) =>
      (⟨fieldCount, result⟩ : ExactFieldRelabelOrbitCarrier))
    (FieldRelabelOrbitCarrier.hypercubicAct_mul left right orbit)

@[simp] theorem exactFieldRelabelOrbitTensorSign_one
    (target : ExactFieldRelabelOrbitCarrier) :
    exactFieldRelabelOrbitTensorSign 1 target = 1 := by
  exact FieldRelabelOrbitCarrier.tensorSign_one target.2

theorem exactFieldRelabelOrbitTensorSign_mul
    (left right : Hypercubic4)
    (target : ExactFieldRelabelOrbitCarrier) :
    exactFieldRelabelOrbitTensorSign (left * right) target =
      exactFieldRelabelOrbitTensorSign right target *
        exactFieldRelabelOrbitTensorSign left
          (exactFieldRelabelOrbitAct right target) := by
  exact FieldRelabelOrbitCarrier.tensorSign_mul left right target.2

def signedExactFieldRelabelOrbitActionBasis (h : Hypercubic4)
    (target : ExactFieldRelabelOrbitCarrier) :
    ExactFieldRelabelOrbitSpace :=
  exactFieldRelabelOrbitTensorSign h target •
    Finsupp.single (exactFieldRelabelOrbitAct h target) 1

def signedExactFieldRelabelOrbitAction (h : Hypercubic4) :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] ExactFieldRelabelOrbitSpace :=
  Finsupp.linearCombination ℚ (signedExactFieldRelabelOrbitActionBasis h)

@[simp] theorem signedExactFieldRelabelOrbitAction_single
    (h : Hypercubic4) (target : ExactFieldRelabelOrbitCarrier)
    (coefficient : ℚ) :
    signedExactFieldRelabelOrbitAction h
        (Finsupp.single target coefficient) =
      Finsupp.single (exactFieldRelabelOrbitAct h target)
        (coefficient * exactFieldRelabelOrbitTensorSign h target) := by
  simp [signedExactFieldRelabelOrbitAction,
    signedExactFieldRelabelOrbitActionBasis]

@[simp] theorem signedExactFieldRelabelOrbitAction_one
    (value : ExactFieldRelabelOrbitSpace) :
    signedExactFieldRelabelOrbitAction 1 value = value := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      calc
        signedExactFieldRelabelOrbitAction 1 (left + right) =
            signedExactFieldRelabelOrbitAction 1 left +
              signedExactFieldRelabelOrbitAction 1 right :=
          (signedExactFieldRelabelOrbitAction 1).map_add left right
        _ = left + right := congrArg₂ (fun x y => x + y) hleft hright
  | single target coefficient =>
      rw [signedExactFieldRelabelOrbitAction_single,
        exactFieldRelabelOrbitAct_one,
        exactFieldRelabelOrbitTensorSign_one]
      simp

theorem signedExactFieldRelabelOrbitAction_mul
    (left right : Hypercubic4)
    (value : ExactFieldRelabelOrbitSpace) :
    signedExactFieldRelabelOrbitAction (left * right) value =
      signedExactFieldRelabelOrbitAction left
        (signedExactFieldRelabelOrbitAction right value) := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add first second hfirst hsecond =>
      calc
        signedExactFieldRelabelOrbitAction (left * right)
            (first + second) =
          signedExactFieldRelabelOrbitAction (left * right) first +
            signedExactFieldRelabelOrbitAction (left * right) second :=
              (signedExactFieldRelabelOrbitAction
                (left * right)).map_add first second
        _ = signedExactFieldRelabelOrbitAction left
              (signedExactFieldRelabelOrbitAction right first) +
            signedExactFieldRelabelOrbitAction left
              (signedExactFieldRelabelOrbitAction right second) :=
          congrArg₂ (fun x y => x + y) hfirst hsecond
        _ = signedExactFieldRelabelOrbitAction left
            (signedExactFieldRelabelOrbitAction right
              (first + second)) := by
          rw [(signedExactFieldRelabelOrbitAction right).map_add,
            (signedExactFieldRelabelOrbitAction left).map_add]
  | single target coefficient =>
      rw [signedExactFieldRelabelOrbitAction_single,
        signedExactFieldRelabelOrbitAction_single,
        signedExactFieldRelabelOrbitAction_single,
        exactFieldRelabelOrbitAct_mul,
        exactFieldRelabelOrbitTensorSign_mul]
      congr 1
      ring

def signedExactFieldRelabelOrbitRepresentation :
    Representation ℚ Hypercubic4 ExactFieldRelabelOrbitSpace where
  toFun := signedExactFieldRelabelOrbitAction
  map_one' := by
    apply LinearMap.ext
    exact signedExactFieldRelabelOrbitAction_one
  map_mul' left right := by
    apply LinearMap.ext
    exact signedExactFieldRelabelOrbitAction_mul left right

/-! ## Equivariance of the orbit quotient -/

theorem exactFieldRelabelOrbitOfOriented_act
    (h : Hypercubic4) (target : ExactOrientedLocalCarrier) :
    exactFieldRelabelOrbitOfOriented (exactOrientedLocalAct h target) =
      exactFieldRelabelOrbitAct h
        (exactFieldRelabelOrbitOfOriented target) := by
  rcases target with ⟨fieldCount, sector⟩
  apply congrArg
    (fun orbit : FieldRelabelOrbitCarrier fieldCount.1
        (dimension16DerivativeCount fieldCount) =>
      (⟨fieldCount, orbit⟩ : ExactFieldRelabelOrbitCarrier))
  change Quotient.mk _
      (orientedLocalSectorEquivLabeled fieldCount.1
        (dimension16DerivativeCount fieldCount)
        (sector.hypercubicAct h)) =
    FieldRelabelOrbitCarrier.hypercubicAct h
      (Quotient.mk _
        (orientedLocalSectorEquivLabeled fieldCount.1
          (dimension16DerivativeCount fieldCount) sector))
  rw [FieldRelabelOrbitCarrier.hypercubicAct_mk]
  exact congrArg (Quotient.mk _)
    (orientedLocalSectorEquivLabeled_hypercubicAct h sector)

theorem exactFieldRelabelOrbitOfOriented_tensorSign
    (h : Hypercubic4) (target : ExactOrientedLocalCarrier) :
    exactFieldRelabelOrbitTensorSign h
        (exactFieldRelabelOrbitOfOriented target) =
      target.2.tensorSign h := by
  rcases target with ⟨fieldCount, sector⟩
  exact orientedLocalSectorEquivLabeled_tensorSign h sector

theorem normalizeExactFieldRelabelBasis_signed_equivariant
    (h : Hypercubic4) (target : ExactOrientedLocalCarrier) :
    normalizeExactFieldRelabel
        (signedExactOrientedLocalActionBasis h target) =
      signedExactFieldRelabelOrbitActionBasis h
        (exactFieldRelabelOrbitOfOriented target) := by
  simp [signedExactOrientedLocalActionBasis,
    normalizeExactFieldRelabelBasis,
    signedExactFieldRelabelOrbitActionBasis,
    exactFieldRelabelOrbitOfOriented_act,
    exactFieldRelabelOrbitOfOriented_tensorSign]

/-- The ordinary field-label quotient is a signed `H(4)` intertwiner. -/
theorem normalizeExactFieldRelabel_signed_equivariant
    (h : Hypercubic4) (value : ExactOrientedLocalSpace) :
    normalizeExactFieldRelabel
        (signedExactOrientedLocalAction h value) =
      signedExactFieldRelabelOrbitAction h
        (normalizeExactFieldRelabel value) := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp [map_add, hleft, hright]
  | single target coefficient =>
      rw [signedExactOrientedLocalAction_single,
        LinearMap.map_smul,
        normalizeExactFieldRelabelBasis_signed_equivariant,
        normalizeExactFieldRelabel_single,
        LinearMap.map_smul]
      simp [normalizeExactFieldRelabelBasis,
        signedExactFieldRelabelOrbitActionBasis]

/-! ## The physical operator on the orbit carrier -/

def orbitPhysicalRelationOperator
    (policy : PhysicalRelationPolicy) :
    PhysicalRelationGeneratorSpace policy →ₗ[ℚ]
      ExactFieldRelabelOrbitSpace :=
  normalizeExactFieldRelabel.comp
    (normalizedPhysicalRelationOperator policy)

theorem orbitPhysicalRelationOperator_equivariant
    (policy : PhysicalRelationPolicy) (h : Hypercubic4)
    (value : PhysicalRelationGeneratorSpace policy) :
    orbitPhysicalRelationOperator policy
        (signedPhysicalRelationGeneratorAction policy h value) =
      signedExactFieldRelabelOrbitAction h
        (orbitPhysicalRelationOperator policy value) := by
  rw [orbitPhysicalRelationOperator, LinearMap.comp_apply,
    normalizedPhysicalRelationOperator_equivariant]
  exact normalizeExactFieldRelabel_signed_equivariant h
    (normalizedPhysicalRelationOperator policy value)

def orbitPhysicalRelationSubmodule
    (policy : PhysicalRelationPolicy) :
    Submodule ℚ ExactFieldRelabelOrbitSpace :=
  LinearMap.range (orbitPhysicalRelationOperator policy)

theorem orbitPhysicalRelationSubmodule_signed_invariant
    (policy : PhysicalRelationPolicy) (h : Hypercubic4)
    (value : ExactFieldRelabelOrbitSpace)
    (membership : value ∈ orbitPhysicalRelationSubmodule policy) :
    signedExactFieldRelabelOrbitAction h value ∈
      orbitPhysicalRelationSubmodule policy := by
  rcases membership with ⟨source, rfl⟩
  exact ⟨signedPhysicalRelationGeneratorAction policy h source,
    orbitPhysicalRelationOperator_equivariant policy h source⟩

end HypercubicDimension16PhysicalOrbitOperator
end YangMills
end QuantumTheory
end Mettapedia
