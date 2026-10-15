import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.PresentationTransport
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.SemanticGluingControls
import Mettapedia.GSLT.Core.PresentationChange

/-! # Controls for interface changes and semantic module transport -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.PresentationTransportControls

open Mettapedia.GSLT Mettapedia.OSLF.Binding
open PresentationTransport SemanticGluing SemanticGluingControls
open _root_.CategoryTheory

/-! ## Canonical printing need not recover source-equivalent text -/

inductive Term where
  | written (value : Nat)
  | expanded (value : Nat)
  | rejected
  deriving DecidableEq

def syntaxTheory : GSLT where
  Term := Term
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun first second => ∃ value, first = .expanded value ∧ second = .written value
  rewrites_resp_left := by intro first other target equal step; cases equal; exact ⟨_, step, rfl⟩
  rewrites_resp_right := by intro first target other step equal; cases equal; exact step

def decode : Term → Option Nat
  | .written value | .expanded value => some value
  | .rejected => none

def interface (expanded : Bool) : GSLT.ExactElaboration syntaxTheory Nat where
  elaborate := decode
  quote := fun value => if expanded then .expanded value else .written value
  elaborate_quote := by intro value; cases expanded <;> rfl
  equation := fun equal => congrArg decode equal
  rewrite := by rintro first second ⟨value, rfl, rfl⟩; rfl

def interfaces (_ : Bool) : GSLT := syntaxTheory
def family (choice : Bool) : GSLT.ExactElaboration (interfaces choice) Nat := interface choice

theorem normalization_changes_authored_term :
    GSLT.ExactElaboration.translate (interface false) (interface false) (.expanded 7) =
      some (.written 7) := rfl

theorem payload_equality_need_not_be_source_equivalence :
    decode (.expanded 7) = decode (.written 7) ∧
      ¬ syntaxTheory.Equiv (.expanded 7) (.written 7) := by
  exact ⟨rfl, by intro impossible; cases impossible⟩

theorem roundTrip_is_not_supplied_by_exact_elaboration :
    ¬ ∀ term value, (interface false).elaborate term = some value →
      syntaxTheory.Equiv term ((interface false).quote value) := by
  intro roundTrip
  have impossible := roundTrip (.expanded 7) 7 rfl
  cases impossible

theorem target_interface_actually_changes_representation :
    PresentationChange.switch family true ⟨false, .written 7⟩ =
      some ⟨true, .expanded 7⟩ := rfl

theorem switching_preserves_rejection :
    PresentationChange.switch family true ⟨false, .rejected⟩ = none := rfl

abbrev State := PresentationChange.State interfaces
def start : State := ⟨false, .expanded 7⟩
def middle : State := ⟨false, .written 7⟩
def finish : State := ⟨true, .expanded 7⟩

def direct : IndexedOperational.ExecutionPath (PresentationChange.system family) start finish :=
  .cons ⟨.change true rfl⟩ (.refl finish)

def staged : IndexedOperational.ExecutionPath (PresentationChange.system family) start finish :=
  .cons ⟨.source ⟨7, rfl, rfl⟩⟩ (.cons ⟨.change true rfl⟩ (.refl finish))

/-- Fusion can preserve the payload while changing the actual path length. -/
theorem fused_and_staged_paths_differ : direct.length = 1 ∧ staged.length = 2 := ⟨rfl, rfl⟩

theorem staged_payload_preserved :
    PresentationChange.observe family start = PresentationChange.observe family finish :=
  PresentationChange.path_observe family staged

def corruptSystem : GSLT where
  Term := Term
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun first second => first = .written 0 ∧ second = .written 1
  rewrites_resp_left := by intro first other target equal step; cases equal; exact ⟨_, step, rfl⟩
  rewrites_resp_right := by intro first target other step equal; cases equal; exact step

/-- The independently defined observer rejects an extra transition, even
when an implementer supplies a purported invariant certificate. -/
theorem extra_behavior_has_no_decode_invariant :
    ¬ ∃ invariant : SemanticInvariant corruptSystem (Option Nat), invariant.denote = decode := by
  rintro ⟨invariant, equal⟩
  have impossible := invariant.rewrite (show corruptSystem.Step (.written 0) (.written 1)
    from ⟨rfl, rfl⟩)
  rw [equal] at impossible
  cases impossible

/-! ## Reversing authored equation sides preserves full binding models -/

def labels : String ≃ String := Equiv.swap "First" "Private First"
def bodies : (Op × Op) ≃ (Op × Op) := Equiv.prodComm Op Op

universe u

/-- This generator law is derived from actual contextual equation semantics;
it does not assume model equivalence or quotient transport. -/
theorem reverse_preserves (A : BindingCloneAlgebra.Algebra.{u} signature) (body : Op × Op) :
    equationSat schema A (bodies body) ↔ equationSat schema A body := by
  constructor <;> intro satisfied index Γ Δ valuation ambient ordinary
  · have zero : index = 0 := Fin.eq_zero index
    subst index
    exact (satisfied 0 valuation ambient ordinary).symm
  · have zero : index = 0 := Fin.eq_zero index
    subst index
    exact (satisfied 0 valuation ambient ordinary).symm

theorem changed_presentation_is_distinct : mapPresentation labels bodies left ≠ left := by
  decide

theorem changed_presentation_keeps_origins :
    origins (mapPresentation labels bodies left).val = origins left.val := origins_map _ _ _

theorem changed_modules_still_join :
    join (mapPresentation labels bodies left) (mapPresentation labels bodies right) =
      some (mapPresentation labels bodies whole) := by
  rw [← map_join, private_instances_join]
  rfl

theorem changed_constraints_keep_independent_private_values (first second : Bool) :
    BindingEquationInterpretation.Satisfies (pointAlgebra first second)
        (equations schema (mapPresentation labels bodies whole)) ↔
      BindingEquationInterpretation.Satisfies (pointAlgebra first second) (equations schema whole) :=
  satisfies_map_iff labels bodies schema schema reverse_preserves _ _

noncomputable def reversedQuotientIso := quotientIso labels bodies schema schema reverse_preserves left

theorem reversed_quotient_inverse_law :
    reversedQuotientIso.hom ≫ reversedQuotientIso.inv =
      𝟙 (FreeBindingEquationModel.presented (equations schema left)).algebra :=
  reversedQuotientIso.hom_inv_id

/-! ## Declaration bijections need not preserve their equation meanings -/

def wrongBodies : (Op × Op) ≃ (Op × Op) :=
  Equiv.prodCongr (Equiv.swap Op.zero Op.one) (Equiv.refl Op)

theorem body_bijection_alone_is_insufficient :
    ¬ (equationSat schema (pointAlgebra false true) (wrongBodies (.zero, .zero)) ↔
      equationSat schema (pointAlgebra false true) (.zero, .zero)) := by
  simp only [point_satisfies_iff]
  decide

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.PresentationTransportControls
