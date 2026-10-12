import Mettapedia.Languages.MeTTa.HE.HOLContract.Signature
import Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent

/-!
# Replaceable backends of the contract

The contract is the meaning of HE's type declarations; a type checker that
decides it is a backend, and backends are replaceable.  A backend
(`Backend`) has its own types and terms, translates the contract's closed
intrinsic terms and their types, and is admitted only with two laws:

* **preservation**: every translated term is typed at its translated type;
* **reflection**: a translated term has no other translated type.

Together with injectivity of the type translation, the laws make the backend
decide the contract on its image (`Backend.decides`): for the intrinsic term
of a contract typing, the backend accepts a translated type exactly when it
is the term's type.  `typed_iff_backend` restates contract typing through any
admitted backend.

The contract does not depend on any backend: this module imports the
contract, never the converse.  The minimal dependent core of
`Logic.HOL.Embedding.SimpleSliceOfDependent` is admitted (`dependentCore`):
the contract's simple types are its non-dependent slice.  What that core does
not supply is computation (it has no conversion rule) and an executable
checker; a backend that runs needs both, with the same two laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.HOLContract

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.TypeGrounding
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.NamedElaboration

universe u

/-- A backend of the contract over a constant family, with its laws. -/
structure Backend (Const : Ty Atom → Type) where
  BackendType : Type u
  BackendTerm : Type u
  HasType : BackendTerm → BackendType → Prop
  translateType : Ty Atom → BackendType
  translateTerm : {type : Ty Atom} → Term Const [] type → BackendTerm
  translateType_injective : Function.Injective translateType
  preserves : ∀ {type : Ty Atom} (term : Term Const [] type),
    HasType (translateTerm term) (translateType type)
  reflects : ∀ {type other : Ty Atom} (term : Term Const [] type),
    HasType (translateTerm term) (translateType other) → other = type

namespace Backend

variable {Const : Ty Atom → Type}

/-- **An admitted backend decides the contract on its image.** -/
theorem decides (backend : Backend.{u} Const) {type other : Ty Atom}
    (term : Term Const [] type) :
    backend.HasType (backend.translateTerm term) (backend.translateType other) ↔ other = type :=
  ⟨backend.reflects term, fun equal => equal ▸ backend.preserves term⟩

end Backend

/-- Contract typing through an admitted backend: some HOL term of the
expression elaborates to an intrinsic term that the backend types at the
translated type. -/
theorem typed_iff_backend {space : Space} (backend : Backend.{u} (Const space))
    {expression type : Atom} :
    Typed space expression type ↔
      ∃ term, Annotates expression term ∧
        ∃ elaborated : SomeTerm (Const space) [],
          infer (signature space) (BinderNames.nil : BinderNames Atom String []) term =
              .ok elaborated ∧
            backend.HasType (backend.translateTerm elaborated.term)
              (backend.translateType (toTy type)) := by
  constructor
  · rintro ⟨term, annotates, intrinsic, inferred⟩
    exact ⟨term, annotates, ⟨toTy type, intrinsic⟩, inferred, backend.preserves intrinsic⟩
  · rintro ⟨term, annotates, ⟨found, intrinsic⟩, inferred, accepted⟩
    have typeEq := backend.reflects intrinsic accepted
    subst typeEq
    exact ⟨term, annotates, intrinsic, inferred⟩

open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent in
/-- **The minimal dependent core is an admitted backend.**  The contract's
simple types are its non-dependent slice: closed HOL terms are typed there at
their embedded types and at no other embedded type. -/
def dependentCore (space : Space) : Backend.{0} (Const space) where
  BackendType := Expr Atom (Const space)
  BackendTerm := Expr Atom (Const space)
  HasType := fun term type => HasType [] term type
  translateType := tyToExpr
  translateTerm := fun term => termToExpr term
  translateType_injective := fun _ _ equal => tyToExpr_injective equal
  preserves := fun term => termToExpr_typed term
  reflects := fun term accepted => image_typing_reflects term accepted

open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent in
/-- The dependent core's types reach beyond the contract: a genuinely
dependent type is formed there and is not the image of a contract type. -/
theorem dependentCore_exceeds_contract (space : Space) (base : Atom) :
    HasType ([] : List (Expr Atom (Const space))) (dependentType base) .univ ∧
      ∀ type : Ty Atom, (dependentCore space).translateType type ≠ dependentType base :=
  ⟨dependentType_formed [] base, fun type equal => dependentType_not_image base ⟨type, equal⟩⟩

#print axioms Backend.decides
#print axioms typed_iff_backend
#print axioms dependentCore
#print axioms dependentCore_exceeds_contract

end Mettapedia.Languages.MeTTa.HE.HOLContract
