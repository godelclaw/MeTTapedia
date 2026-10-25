import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConstantRenamingTransport
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCode

/-!
# Root computation and decoder transport under constant-name permutations

Pulling a root relation back along a constant-name map retains variable
renaming and substitution. A bijection supplies the inverse laws needed to
transport a qualified finite decoder. Codes stay in the source format while
the decoded endpoints are renamed; soundness and completeness concern the
independently transported root relation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

variable {Head : Type} {n : Nat}

@[simp] theorem Tm.mapConst_equiv_left (names : DeclName ≃ DeclName) (term : Tm Head n) :
    (term.mapConst names).mapConst names.symm = term := by
  rw [Tm.mapConst_mapConst]
  have inverse : (fun name => names.symm (names name)) = (fun name => name) :=
    funext names.symm_apply_apply
  rw [inverse, Tm.mapConst_id]

@[simp] theorem Tm.mapConst_equiv_right (names : DeclName ≃ DeclName) (term : Tm Head n) :
    (term.mapConst names.symm).mapConst names = term := by
  rw [Tm.mapConst_mapConst]
  have inverse : (fun name => names (names.symm name)) = (fun name => name) :=
    funext names.apply_symm_apply
  rw [inverse, Tm.mapConst_id]

def RootComputation.pullbackConst (names : DeclName → DeclName)
    (source : RootComputation Head) : RootComputation Head where
  step left right := source.step (left.mapConst names) (right.mapConst names)
  rename := by
    intro n m renameMap left right step
    simpa only [Tm.mapConst_rename] using source.rename renameMap step
  substitute := by
    intro n m substitution left right step
    simpa only [Tm.mapConst_subst] using
      source.substitute (fun index => (substitution index).mapConst names) step

theorem RootComputation.pullbackConst_forward (names : DeclName ≃ DeclName)
    (source : RootComputation Head) {left right : Tm Head n}
    (step : source.step left right) :
    (source.pullbackConst names.symm).step (left.mapConst names) (right.mapConst names) := by
  change source.step ((left.mapConst names).mapConst names.symm)
    ((right.mapConst names).mapConst names.symm)
  simpa only [Tm.mapConst_equiv_left] using step

namespace StructuralConversionCode.RootDecoder

variable {source : RootComputation Head}

def renameConst (names : DeclName ≃ DeclName) (original : RootDecoder source) :
    RootDecoder (source.pullbackConst names.symm) where
  Code := original.Code
  decode code := (original.decode code).map fun endpoints =>
    (endpoints.1.mapConst names, endpoints.2.mapConst names)
  sound := by
    intro n code left right decoded
    cases found : original.decode code with
    | none => simp only [found, Option.map_none, reduceCtorEq] at decoded
    | some endpoints =>
        simp only [found, Option.map_some, Option.some.injEq, Prod.mk.injEq] at decoded
        obtain ⟨rfl, rfl⟩ := decoded
        exact source.pullbackConst_forward names (original.sound code found)
  complete := by
    intro n left right step
    obtain ⟨code, decoded⟩ := original.complete step
    refine ⟨code, ?_⟩
    rw [decoded]
    simp only [Option.map_some, Tm.mapConst_equiv_right]

theorem renameConst_decode (names : DeclName ≃ DeclName) (original : RootDecoder source)
    {code : original.Code n} {left right : Tm Head n}
    (decoded : original.decode code = some (left, right)) :
    (original.renameConst names).decode code =
      some (left.mapConst names, right.mapConst names) := by
  change (original.decode code).map _ = _
  rw [decoded]
  rfl

end StructuralConversionCode.RootDecoder

#print axioms RootComputation.pullbackConst
#print axioms RootComputation.pullbackConst_forward
#print axioms StructuralConversionCode.RootDecoder.renameConst

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
