import Mettapedia.Languages.Metamath.MMLean4Bridge
import Mathlib.Data.Finset.Basic

/-!
# Metamath's explicit substitution and distinct-variable discipline

The observer follows the existing operational proof steps. Its least inventory
is a statement about this interface, not a complexity classification or an
absolute minimum kernel. The original runtime distinct-variable checker is
used in the controls; correctly typed substitution images can still violate
its independence condition. The declarative control shows that this is a
semantic constraint, not merely a parser convention.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.CheckingDiscipline

open _root_.Metamath

inductive Operation where
  | lookup | syntaxComparison | typecodeChecking | substitution
  | distinctVariableChecking | stackOperations | implicitNormalization
deriving DecidableEq, Repr

abbrev Basis := Finset Operation

def operations : Spec.ProofStep → Basis
  | .useHyp _ => {.lookup, .stackOperations}
  | .useAssertion _ _ =>
      {.lookup, .syntaxComparison, .typecodeChecking, .substitution,
        .distinctVariableChecking, .stackOperations}

def Covers (basis : Basis) : Prop := ∀ step, operations step ⊆ basis

def requiredBasis : Basis :=
  {.lookup, .syntaxComparison, .typecodeChecking, .substitution,
    .distinctVariableChecking, .stackOperations}

theorem required_basis_covers : Covers requiredBasis := by
  intro step
  cases step <;> simp [operations, requiredBasis]

theorem covers_iff_contains_required (basis : Basis) :
    Covers basis ↔ requiredBasis ⊆ basis := by
  constructor
  · intro covered
    exact covered (.useAssertion "rule" (fun _ => ⟨⟨"wff"⟩, []⟩))
  · intro included step
    exact (required_basis_covers step).trans included

theorem no_implicit_normalization (step : Spec.ProofStep) :
    Operation.implicitNormalization ∉ operations step := by
  cases step <;> simp [operations]

namespace Controls

def image (name : String) : Verify.Formula := #[.const "set", .var name]
def separated : Std.HashMap String Verify.Formula :=
  (Std.HashMap.emptyWithCapacity.insert "x" (image "z")).insert "y" (image "w")
def coincident : Std.HashMap String Verify.Formula :=
  (Std.HashMap.emptyWithCapacity.insert "x" (image "z")).insert "y" (image "z")

theorem independent_images_accept :
    Verify.DB.dvCheckBool ["z", "w"] #[("w", "z")] #[("x", "y")] separated = true := by
  simp [Verify.DB.dvCheckBool, separated, image, Verify.Formula.varsIn, Verify.Sym.value, Std.HashMap.getElem_insert]

theorem coincident_images_refuse :
    Verify.DB.dvCheckBool ["z", "w"] #[("w", "z")] #[("x", "y")] coincident = false := by
  simp [Verify.DB.dvCheckBool, coincident, image, Verify.Formula.varsIn, Verify.Sym.value, Std.HashMap.getElem_insert]

theorem missing_target_independence_refuses :
    Verify.DB.dvCheckBool ["z", "w"] #[] #[("x", "y")] separated = false := by
  simp [Verify.DB.dvCheckBool, separated, image, Verify.Formula.varsIn, Verify.Sym.value, Std.HashMap.getElem_insert]

theorem no_source_constraint_accepts :
    Verify.DB.dvCheckBool ["z", "w"] #[] #[] coincident = true := by decide +kernel

theorem image_typecodes_agree :
    (image "z")[0]? = some (.const "set") ∧
    (image "w")[0]? = some (.const "set") := by decide +kernel

/-- Correct typecodes do not repair a diagonal substitution of a declared
distinct pair. This is the original independent specification. -/
theorem typecodes_do_not_imply_dv :
    (∀ v : Spec.Variable, ((fun _ => (⟨⟨"set"⟩, ["z"]⟩ : Spec.Expr)) v).typecode = ⟨"set"⟩) ∧
    ¬ Spec.dvOK [⟨"z"⟩] [(⟨"x"⟩, ⟨"y"⟩)] []
      (fun _ => ⟨⟨"set"⟩, ["z"]⟩) := by
  refine ⟨fun _ => rfl, ?_⟩
  intro admitted
  have impossible := admitted ⟨"x"⟩ ⟨"y"⟩ (by simp)
    ⟨"z"⟩ (by simp [Spec.varsInExpr]) ⟨"z"⟩ (by simp [Spec.varsInExpr])
  exact impossible.1 rfl

end Controls

end Mettapedia.Languages.Metamath.CheckingDiscipline
