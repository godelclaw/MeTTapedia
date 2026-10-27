import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorJudgmentReplay
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorAnnotatedPrograms
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ContextChecking

/-!
# Executed annotated replay and original-row refusal controls

The certificates below are finite rule data, constructed independently of
the source soundness theorem. They check an annotated beta proof and retain
all original Nat/Vec row addresses. Wrong conclusions, missing premises,
disabled rows, malformed arities and changed binder domains are refused.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
namespace Programs.Annotated.JudgmentReplay.Controls

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated

def enabled : ComputationProfiles.Selection := fun _ => true
abbrev u0 : Tower.Head := .sort Tower.zero
abbrev u1 : Tower.Head := .sort (.succ Tower.zero)
abbrev u00 : Tower.Head := .sort (.max Tower.zero Tower.zero)

def node {statement : CStatement Tower.Head}
    (code : Checking.Code Tower.Head (decoder enabled).Code statement)
    (children : List (Certificate enabled)) : Certificate enabled :=
  .node statement ⟨statement, code⟩ children.length children.get

def universeZero : Certificate enabled :=
  node (.headType (Γ := .nil) (h := u0) (u := u1)) []

def natural {n : Nat} (context : CCtx Tower.Head n) : Certificate enabled :=
  node (.const (Γ := context) (name := natName) (type := .head u0) (u := u1)) [universeZero]

def zero {n : Nat} (context : CCtx Tower.Head n) : Certificate enabled :=
  node (.const (Γ := context) (name := zeroName) (type := .const natName) (u := u0)) [natural .nil]

def functionType : Certificate enabled :=
  node (.piForm (Γ := .nil) (A := .const natName) (B := .const natName) (u := u0) (v := u0) (w := u00))
    [natural .nil, natural (.snoc .nil (.const natName))]

def identityBody : Certificate enabled := node (.var (Γ := .snoc .nil (.const natName)) 0) []

def identity : Certificate enabled :=
  node (.lamIntro (Γ := .nil) (A := .const natName) (body := .var 0)
    (B := .const natName) (u := u00) (w := u0)) [natural .nil, functionType, identityBody]

def pairType : Certificate enabled :=
  node (.sigmaForm (Γ := .nil) (A := .const natName) (B := .const natName) (u := u0) (v := u0) (w := u00))
    [natural .nil, natural (.snoc .nil (.const natName))]

def pair : Certificate enabled :=
  node (.pairIntro (Γ := .nil) (a := .const zeroName) (b := .const zeroName)
    (A := .const natName) (B := .const natName) (u := u00)) [pairType, zero .nil, zero .nil]

theorem pair_checked : check enabled pair
    (.typing .nil (.pair (.const zeroName) (.const zeroName)) (.sigma (.const natName) (.const natName))) = true := by decide

theorem identity_checked : check enabled identity
    (.typing .nil (.lam (.const natName) (.var 0)) (.pi (.const natName) (.const natName))) = true := by decide

def naturalContext : ContextCertificate enabled 1 := .snoc .nil u0 (natural .nil)

theorem natural_context_checked : checkContext enabled (.snoc .nil (.const natName)) naturalContext = true := by decide

theorem natural_context_formed : CCtxFormed (church enabled) (.snoc .nil (.const natName)) :=
  context_sound enabled natural_context_checked

theorem changed_domain_refused : checkContext enabled
    (.snoc .nil (.pi (.const natName) (.const natName))) naturalContext = false := by decide

def beta : Certificate enabled :=
  node (.betaPi (Γ := .nil) (A := .const natName) (a := .const zeroName) (body := .var 0)
    (B := .const natName) (u := u00)) [functionType, identityBody, zero .nil]

def betaStatement : CStatement Tower.Head :=
  .equality .nil (.app (.lam (.const natName) (.var 0)) (.const zeroName)) (.const zeroName) (.const natName)

theorem beta_checked : check enabled beta betaStatement = true := by decide

theorem beta_source_equal : CDerivable (church enabled) betaStatement := check_sound enabled beta_checked

/-- An independent declarative proof supplies the completeness theorem's
input; it is not recovered from the finite certificate above. -/
theorem independent_beta : CDerivable (church enabled) betaStatement :=
  .betaPi (.piForm (Functions.natural_typed enabled) (.sort _)
    (Functions.natural_typed enabled) (.sort _) (.sorts _ _)) (.sort _)
    (.var 0) (Functions.zero_typed enabled)

theorem beta_has_certificate : ∃ certificate : Certificate enabled,
    check enabled certificate betaStatement = true := check_complete enabled independent_beta

theorem beta_has_graph : ∃ (nodes : List (DerivationGraph.Node (CStatement Tower.Head) (Witness enabled) Unit))
    (cache : Array (CStatement Tower.Head)) (root : Nat),
    DerivationGraph.replay (interface enabled) nodes = some cache ∧ cache[root]? = some betaStatement :=
  (checked_graph_iff enabled betaStatement).mpr independent_beta

theorem forged_beta_refused : check enabled beta
    (.equality .nil (.app (.lam (.const natName) (.var 0)) (.const zeroName))
      (.app (.const succName) (.const zeroName)) (.const natName)) = false := by decide

def missingArgument : Certificate enabled :=
  node (.betaPi (Γ := .nil) (A := .const natName) (a := .const zeroName) (body := .var 0)
    (B := .const natName) (u := u00)) [functionType, identityBody]

theorem missing_argument_refused : check enabled missingArgument betaStatement = false := by decide

def swappedChildren : Certificate enabled :=
  node (.betaPi (Γ := .nil) (A := .const natName) (a := .const zeroName) (body := .var 0)
    (B := .const natName) (u := u00)) [functionType, zero .nil, identityBody]

theorem swapped_children_refused : check enabled swappedChildren betaStatement = false := by decide

def graphNode (certificate : Certificate enabled) (parents : List Nat) :
    DerivationGraph.Node (CStatement Tower.Head) (Witness enabled) Unit :=
  match certificate with
  | .node statement witness _ _ => ⟨statement, witness, parents, ()⟩

def betaGraph := [graphNode universeZero [], graphNode (natural .nil) [0],
  graphNode (natural (.snoc .nil (.const natName))) [0], graphNode functionType [1, 2],
  graphNode identityBody [], graphNode (zero .nil) [1], graphNode beta [3, 4, 5]]

theorem graph_checked :
    ((DerivationGraph.replay (interface enabled) betaGraph).bind (fun cache => cache[6]?)) = some betaStatement := by decide

theorem forward_reference_refused :
    DerivationGraph.replay (interface enabled) (betaGraph.take 6 ++ [graphNode beta [3, 4, 7]]) = none := by decide

theorem swapped_references_refused :
    DerivationGraph.replay (interface enabled) (betaGraph.take 6 ++ [graphNode beta [3, 5, 4]]) = none := by decide

def citedRow (index : Fin NativeNaturalVectorFamilies.Checking.table.length) :
    SchemaJudgmentCode.Code Tower.Head (NativeNaturalVectorFamilies.Checking.table.get index).1 :=
  SchemaJudgmentCode.encode NativeNaturalVectorFamilies.Checking.table index CTm.ids

theorem zero_row_encoding : (decoder enabled).decode (citedRow ⟨0, by decide⟩) =
    some (SchemaJudgmentCode.Instance.result (enabled := enabled) (church enabled).constantType
      ⟨(⟨0, by decide⟩ : Fin NativeNaturalVectorFamilies.Checking.table.length), rfl, CTm.ids⟩) :=
  SchemaJudgmentCode.decode_encode (church enabled).constantType NativeNaturalVectorFamilies.Checking.table
    enabled ⟨0, by decide⟩ rfl CTm.ids

theorem all_rows_decode : (List.finRange 4).all (fun index => ((decoder enabled).decode (citedRow index)).isSome) = true := by
  decide

theorem all_disabled_rows_refused : (List.finRange 4).all
    (fun index => ((decoder (fun _ => false)).decode (citedRow index)).isNone) = true := by decide

theorem wrong_arity_refused : (decoder enabled).decode
    (⟨0, [(.const zeroName : CTm Tower.Head 0)]⟩ : SchemaJudgmentCode.Code Tower.Head 0) = none := by decide

theorem wrong_address_refused : (decoder enabled).decode
    (⟨4, []⟩ : SchemaJudgmentCode.Code Tower.Head 0) = none := by decide

def zeroRowResult := ((decoder enabled).decode (citedRow ⟨0, by decide⟩)).getD
  ⟨.const zeroName, .const zeroName, []⟩

theorem zero_row_has_required_arguments : zeroRowResult.premises.length = 3 := by decide

def zeroRowWitness : Witness enabled :=
  ⟨.equality (context ⟨0, by decide⟩) zeroRowResult.left zeroRowResult.right (resultType ⟨0, by decide⟩),
    .root (citedRow ⟨0, by decide⟩)⟩

def zeroRowPremises : List (CStatement Tower.Head) :=
  [.typing (context ⟨0, by decide⟩) zeroRowResult.left (resultType ⟨0, by decide⟩),
   .typing (context ⟨0, by decide⟩) zeroRowResult.right (resultType ⟨0, by decide⟩)] ++
    zeroRowResult.premises.map (CPremise.statement (context ⟨0, by decide⟩))

theorem zero_row_local_checked : (interface enabled).isInstance zeroRowWitness zeroRowPremises zeroRowWitness.1 = true := by
  decide

theorem zero_row_missing_guard_refused : (interface enabled).isInstance zeroRowWitness
    (zeroRowPremises.take 2) zeroRowWitness.1 = false := by decide

#print axioms beta_source_equal
#print axioms all_rows_decode
#print axioms zero_row_local_checked
#print axioms zero_row_missing_guard_refused

end Programs.Annotated.JudgmentReplay.Controls
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
