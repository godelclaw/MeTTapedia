import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Joined
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSignatureSumSubstitution

/-!
# Substitution through indexed modal parameter telescopes

The laws use simultaneous substitutions of arbitrary native terms. A rely
parameter protects both its supplied value and its membership witness. The
continuation operation below extends the existing renaming-based operation to
term substitutions, with a proved agreement on variables.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf
open CubeEnrichment CubeNativeDeclarations

variable {D : CubeEnrichment.Signature}

@[simp] theorem codeType_substitute (carrier : D.Carrier) {n m : Nat}
    (mapping : Substitution (symbols D) n m) :
    (codeType carrier n).substitute mapping = codeType carrier m := by
  apply congrArg (TypeExpr.family (S := symbols D) (.code carrier))
  funext position
  exact Fin.elim0 position

@[simp] theorem sortCode_substitute (carrier : D.Carrier) (sort : HSort) {n m : Nat}
    (mapping : Substitution (symbols D) n m) :
    (sortCode carrier sort n).substitute mapping = sortCode carrier sort m := by
  apply congrArg (TermExpr.primitive (S := symbols D) (.sort carrier sort))
  funext position
  exact Fin.elim0 position

@[simp] theorem typingType_substitute (carrier : D.Carrier) {n m : Nat}
    (value classifier : TermExpr (symbols D) n)
    (mapping : Substitution (symbols D) n m) :
    (typingType carrier value classifier).substitute mapping =
      typingType carrier (value.substitute mapping) (classifier.substitute mapping) := by
  apply congrArg (TypeExpr.family (S := symbols D) (.typing carrier))
  funext position
  cases position using Fin.cases with
  | zero => rfl
  | succ rest =>
      cases rest using Fin.cases with
      | zero => rfl
      | succ impossible => exact Fin.elim0 impossible

@[simp] theorem certifiedCode_substitute (carrier : D.Carrier) (sort : HSort)
    {n m : Nat} (mapping : Substitution (symbols D) n m) :
    (certifiedCode carrier sort n).substitute mapping = certifiedCode carrier sort m := by
  simp only [certifiedCode, TypeExpr.substitute, codeType_substitute,
    typingType_substitute, TermExpr.substitute, liftSubstitution_zero, sortCode_substitute]

@[simp] theorem classifierValue_substitute (carrier : D.Carrier) (sort : HSort)
    {n m : Nat} (value : TermExpr (symbols D) n)
    (mapping : Substitution (symbols D) n m) :
    (classifierValue carrier sort value).substitute mapping =
      classifierValue carrier sort (value.substitute mapping) := by
  simp only [classifierValue, TermExpr.substitute, codeType_substitute,
    typingType_substitute, liftSubstitution_zero, sortCode_substitute]

@[simp] theorem indexType_substitute (carrier : D.Carrier) (sort : HSort)
    {n m : Nat} (mapping : Substitution (symbols D) n m) :
    (indexType carrier sort n).substitute mapping = indexType carrier sort m := by
  simp only [indexType, TypeExpr.substitute, certifiedCode_substitute,
    codeType_substitute, typingType_substitute, classifierValue_substitute,
    TermExpr.substitute, liftSubstitution_zero]
  rfl

@[simp] theorem relyFunction_substitute (carrier : D.Carrier) {n m : Nat}
    (classifier : TermExpr (symbols D) n) (body : TypeExpr (symbols D) (n + 2))
    (mapping : Substitution (symbols D) n m) :
    (relyFunction carrier classifier body).substitute mapping =
      relyFunction carrier (classifier.substitute mapping)
        (body.substitute (liftSubstitution (liftSubstitution mapping))) := by
  simp only [relyFunction, TypeExpr.substitute, codeType_substitute,
    typingType_substitute, TermExpr.substitute, liftSubstitution_zero,
    TermExpr.substitute_weaken]

/-- Weaken a substituted ambient value past a rely value and its witness. -/
def weakenTwice {n m : Nat} (mapping : Substitution (symbols D) n m) :
    Substitution (symbols D) n (m + 2) :=
  fun position => ((mapping position).rename Fin.succ).rename Fin.succ

theorem weakenTwice_substitute {n m k : Nat}
    (first : Substitution (symbols D) n m) (second : Substitution (symbols D) m k) :
    composeSubstitution (weakenTwice first) (liftSubstitution (liftSubstitution second)) =
      weakenTwice (composeSubstitution first second) := by
  funext position
  simp only [composeSubstitution, weakenTwice, TermExpr.substitute_weaken]

/-- The actual native continuation telescope with arbitrary open arguments. -/
def continuationAt {n m : Nat} (target : D.Carrier) (sort : HSort)
    (relies : List (D.Carrier × TermExpr (symbols D) n))
    (mapping : Substitution (symbols D) n m) : TypeExpr (symbols D) m :=
  match relies with
  | [] => certifiedCode target sort m
  | (carrier, classifier) :: remaining =>
      relyFunction carrier (classifier.substitute mapping)
        (continuationAt target sort remaining (weakenTwice mapping))

/-- The new operation agrees with the existing generated continuation. -/
theorem continuationAt_variables {n m : Nat} (target : D.Carrier) (sort : HSort)
    (relies : List (D.Carrier × TermExpr (symbols D) n)) (mapping : Renaming n m) :
    continuationAt target sort relies (fun position => .var (mapping position)) =
      continuationType target sort relies mapping := by
  induction relies generalizing m with
  | nil => rfl
  | cons entry remaining induction =>
      simp only [continuationAt, continuationType, TermExpr.substitute_variables]
      congr 1
      exact induction (twice mapping)

/-- Both binders are lifted before substituting the next target telescope. -/
theorem continuationAt_substitute {n m k : Nat} (target : D.Carrier) (sort : HSort)
    (relies : List (D.Carrier × TermExpr (symbols D) n))
    (first : Substitution (symbols D) n m) (second : Substitution (symbols D) m k) :
    (continuationAt target sort relies first).substitute second =
      continuationAt target sort relies (composeSubstitution first second) := by
  induction relies generalizing m k with
  | nil => exact certifiedCode_substitute target sort second
  | cons entry remaining induction =>
      simp only [continuationAt, relyFunction_substitute, TermExpr.substitute_comp]
      rw [induction, weakenTwice_substitute]
      rfl

/-- Applying an arbitrary term substitution to an existing modal continuation. -/
theorem continuationType_substitute {n m k : Nat} (target : D.Carrier) (sort : HSort)
    (relies : List (D.Carrier × TermExpr (symbols D) n)) (rho : Renaming n m)
    (mapping : Substitution (symbols D) m k) :
    (continuationType target sort relies rho).substitute mapping =
      continuationAt target sort relies (fun position => mapping (rho position)) := by
  rw [← continuationAt_variables, continuationAt_substitute]
  rfl

/-- Composition is exact even when the second substitution contains lambdas. -/
theorem continuationAt_compose {n m k l : Nat} (target : D.Carrier) (sort : HSort)
    (relies : List (D.Carrier × TermExpr (symbols D) n))
    (first : Substitution (symbols D) n m) (second : Substitution (symbols D) m k)
    (third : Substitution (symbols D) k l) :
    ((continuationAt target sort relies first).substitute second).substitute third =
      continuationAt target sort relies
        (composeSubstitution first (composeSubstitution second third)) := by
  rw [continuationAt_substitute, continuationAt_substitute, composeSubstitution_assoc]

@[simp] theorem indexType_rename (carrier : D.Carrier) (sort : HSort)
    {n m : Nat} (mapping : Renaming n m) :
    (indexType carrier sort n).rename mapping = indexType carrier sort m := by
  rw [← TypeExpr.substitute_variables]
  exact indexType_substitute carrier sort _

@[simp] theorem relyFunction_rename (carrier : D.Carrier) {n m : Nat}
    (classifier : TermExpr (symbols D) n) (body : TypeExpr (symbols D) (n + 2))
    (mapping : Renaming n m) :
    (relyFunction carrier classifier body).rename mapping =
      relyFunction carrier (classifier.rename mapping)
        (body.rename (liftRenaming (liftRenaming mapping))) := by
  rw [← TypeExpr.substitute_variables]
  simp only [relyFunction_substitute, TermExpr.substitute_variables,
    liftSubstitution_variables, TypeExpr.substitute_variables]

theorem continuationAt_rename {n m k : Nat} (target : D.Carrier) (sort : HSort)
    (relies : List (D.Carrier × TermExpr (symbols D) n))
    (arguments : Substitution (symbols D) n m) (mapping : Renaming m k) :
    (continuationAt target sort relies arguments).rename mapping =
      continuationAt target sort relies (fun position => (arguments position).rename mapping) := by
  rw [← TypeExpr.substitute_variables, continuationAt_substitute]
  apply congrArg (continuationAt target sort relies)
  funext position
  exact TermExpr.substitute_variables mapping (arguments position)

theorem continuationType_rename {n m k : Nat} (target : D.Carrier) (sort : HSort)
    (relies : List (D.Carrier × TermExpr (symbols D) n))
    (first : Renaming n m) (second : Renaming m k) :
    (continuationType target sort relies first).rename second =
      continuationType target sort relies (fun position => second (first position)) := by
  rw [← continuationAt_variables, continuationAt_rename]
  exact continuationAt_variables target sort relies _

/-- Substituted classifiers remain ordinary generated continuation syntax. -/
theorem continuationAt_reindexed {n m k : Nat} (target : D.Carrier) (sort : HSort)
    (relies : List (D.Carrier × TermExpr (symbols D) n))
    (arguments : Substitution (symbols D) n m) (mapping : Renaming m k) :
    continuationAt target sort relies (fun position => (arguments position).rename mapping) =
      continuationType target sort
        (relies.map (fun entry => (entry.1, entry.2.substitute arguments))) mapping := by
  induction relies generalizing k with
  | nil => rfl
  | cons entry remaining induction =>
      simp only [continuationAt, continuationType, List.map_cons]
      rw [← TermExpr.rename_substitute]
      congr 1
      have square : weakenTwice (fun position => (arguments position).rename mapping) =
          (fun position => (arguments position).rename (twice mapping)) := by
        funext position
        simp only [weakenTwice, TermExpr.rename_comp]
        rfl
      rw [square]
      exact induction (twice mapping)

theorem continuationAt_mapped {n m : Nat} (target : D.Carrier) (sort : HSort)
    (relies : List (D.Carrier × TermExpr (symbols D) n))
    (arguments : Substitution (symbols D) n m) :
    continuationAt target sort relies arguments =
      continuationType target sort
        (relies.map (fun entry => (entry.1, entry.2.substitute arguments))) id := by
  simpa only [TermExpr.rename_identity] using
    continuationAt_reindexed target sort relies arguments id

/-- The full substitution law expressed entirely with the generated former. -/
theorem continuationType_substitute_explicit {n m k : Nat}
    (target : D.Carrier) (sort : HSort)
    (relies : List (D.Carrier × TermExpr (symbols D) n)) (rho : Renaming n m)
    (mapping : Substitution (symbols D) m k) :
    (continuationType target sort relies rho).substitute mapping =
      continuationType target sort
        (relies.map (fun entry => (entry.1, (entry.2.rename rho).substitute mapping))) id := by
  rw [continuationType_substitute, continuationAt_mapped]
  simp only [TermExpr.substitute_rename]
  rfl

def continuationAtFormed (vertex : Vertex D) {n m : Nat}
    (target : D.Carrier) (sort : HSort)
    (relies : List (D.Carrier × TermExpr (symbols D) n))
    (arguments : Substitution (symbols D) n m) {context : ContextExpr (symbols D) m}
    (formed : Derivation (Theory vertex) (.context context))
    (classifiers : ∀ entry ∈ relies, Derivation (Theory vertex)
      (.term context (entry.2.substitute arguments) (codeType entry.1 m))) :
    Derivation (Theory vertex) (.type context (continuationAt target sort relies arguments)) := by
  rw [continuationAt_mapped]
  apply continuationFormed vertex target sort _ id formed
  intro position
  let original : Fin relies.length := ⟨position.val, by
    simpa only [List.length_map] using position.isLt⟩
  have equation :
      (relies.map (fun entry => (entry.1, entry.2.substitute arguments)))[position] =
        (relies[original].1, relies[original].2.substitute arguments) := by
    simp only [List.getElem_map, Fin.getElem_fin]
    rfl
  rw [equation, TermExpr.rename_identity]
  exact classifiers relies[original] (List.get_mem relies original)

/-- The continuation parameter computed from the language supports arbitrary
ambient substitution; indices and rely classifiers can be actual terms. -/
theorem targetParameter_substitute (interface : Interface D.Carrier) {n : Nat}
    (mapping : Substitution (symbols D) (prefixSize interface) n) :
    (targetParameter interface).substitute mapping =
      continuationAt interface.target interface.resultSort (relyArguments interface) mapping := by
  exact continuationType_substitute interface.target interface.resultSort _ id mapping

@[simp] theorem result_substitute (interface : Interface D.Carrier) {n : Nat}
    (mapping : Substitution (symbols D) (arity interface) n) :
    (result interface).substitute mapping = certifiedCode interface.focus interface.resultSort n :=
  certifiedCode_substitute interface.focus interface.resultSort mapping

namespace Controls

/-- A closed native identity, used as a substituted ambient classifier value. -/
def closedIdentity (carrier : D.Carrier) (n : Nat) : TermExpr (symbols D) n :=
  .lam (codeType carrier n) (codeType carrier (n + 1)) (.var 0)

/-- The second classifier crosses the first value and membership binders.
The actual generated syntax receives a lambda, rather than a variable rename. -/
theorem two_rely_lambda_substitution (carrier : D.Carrier) (sort : HSort) :
    (continuationType carrier sort
      [(carrier, (.var 0 : TermExpr (symbols D) 1)), (carrier, .var 0)] id).substitute
        (fun _ => closedIdentity carrier 0) =
      relyFunction carrier (closedIdentity carrier 0)
        (relyFunction carrier (closedIdentity carrier 2) (certifiedCode carrier sort 4)) := by
  rw [continuationType_substitute]
  simp only [continuationAt, TermExpr.substitute, weakenTwice, closedIdentity,
    TermExpr.rename, codeType_rename, liftRenaming_zero]

/-- A capture-blind treatment of the second rely classifier is observably
different from the result of the genuine generated substitution. -/
theorem two_rely_capture_rejected (carrier : D.Carrier) (sort : HSort) :
    (continuationType carrier sort
      [(carrier, (.var 0 : TermExpr (symbols D) 1)), (carrier, .var 0)] id).substitute
        (fun _ => closedIdentity carrier 0) ≠
      relyFunction carrier (closedIdentity carrier 0)
        (relyFunction carrier (.var 0) (certifiedCode carrier sort 4)) := by
  rw [two_rely_lambda_substitution]
  intro equality
  have outer := (TypeExpr.pi.inj equality).2
  have inner := (TypeExpr.pi.inj outer).2
  have body := (TypeExpr.pi.inj inner).2
  have domains := (TypeExpr.pi.inj body).1
  have arguments := (TypeExpr.family.inj domains).2
  have impossible := congrFun (eq_of_heq arguments) 1
  cases impossible

end Controls

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open
