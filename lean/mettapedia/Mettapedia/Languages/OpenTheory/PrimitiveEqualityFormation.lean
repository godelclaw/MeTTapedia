import Mettapedia.Languages.OpenTheory.SignatureFormation

/-!
# Formation from a registered polymorphic equality declaration

The equality instance is constructed by the actual type substitution.
Result annotations also retain registered function and Boolean carriers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory.PrimitiveEqualityFormation

open SignatureFormation

/-- Instantiate the actual primitive equality declaration at any operand
type. Registration and annotation formation are distinct obligations. -/
theorem equality_instance (signature : Signature) (parameter : Name) (operand : Ty)
    (registered : signature.constants Const.equality = some (Ty.equality (.var parameter))) :
    ConstantInstance signature Const.equality (Ty.equality operand) := by
  refine ⟨Ty.equality (.var parameter), ⟨[(parameter, operand)]⟩, registered, ?_⟩
  simp [Ty.equality, Ty.function, Ty.bool, TypeSubst.lookup]

theorem equation_annotations (signature : Signature) (parameter : Name) (operand : Ty)
    (functionArity : signature.typeOperators TypeOp.function = some 2)
    (booleanFormed : TypeFormed signature Ty.bool)
    (operandFormed : TypeFormed signature operand)
    (registered : signature.constants Const.equality = some (Ty.equality (.var parameter)))
    (left right : DBTerm) (leftFormed : AnnotationsFormed signature left)
    (rightFormed : AnnotationsFormed signature right) :
    AnnotationsFormed signature (CanonicalTerm.equalityDB operand left right) := by
  have equalityFormed : TypeFormed signature (Ty.equality operand) :=
    TypeFormed.function signature functionArity operandFormed
      (TypeFormed.function signature functionArity operandFormed booleanFormed)
  exact .app (.app (.constant equalityFormed (equality_instance signature parameter operand registered))
    leftFormed) rightFormed

end Mettapedia.Languages.OpenTheory.PrimitiveEqualityFormation
