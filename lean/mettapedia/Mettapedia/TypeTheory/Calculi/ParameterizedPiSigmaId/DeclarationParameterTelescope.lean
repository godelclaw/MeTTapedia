import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationSignature
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConstantExpansion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.HeadMorphism
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.ContextualSubstitutionEquality
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.ConstantInstantiation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.TypedReduction

/-!
# Dependent declaration-parameter telescopes

An ordered declaration array becomes a telescope by interpreting preceding
names as variables in each successive type. Unselected names retain their
constant spelling. Source context formation and actual target declaration
lookups construct a typed substitution to those constants. Type dependencies
between selected operations are retained.

The source and target rule packages are explicit. The result concerns typing
and exact syntax readback; semantic interpretation and target conservativity
are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Declaration.DependentParameters

open TypedEquality
open TypedEquality.Normalization (CtxFormed)

variable {Head : Type} {total : Nat}

def positions (names : Fin total → DeclName) (count : Nat) (bound : count ≤ total)
    (name : DeclName) : Option (Fin count) :=
  (List.finRange count).find? fun index => names (Fin.castLE bound index.rev) == name

def values (names : Fin total → DeclName) (count : Nat) (bound : count ≤ total) :
    ConstantSubstitution.Values Head count :=
  fun name => match positions names count bound name with
    | some index => .var index
    | none => .const name

def context (names : Fin total → DeclName) (types : Fin total → Tm Head 0) :
    (count : Nat) → count ≤ total → Ctx Head count
  | 0, _ => .nil
  | count + 1, bound =>
      .snoc (context names types count (by omega))
        (ConstantSubstitution.interpret (values names count (by omega)) Fin.elim0
          (types ⟨count, by omega⟩))

def constantArguments (names : Fin total → DeclName) (count : Nat) (bound : count ≤ total) :
    Sub Head count 0 :=
  fun index => .const (names (Fin.castLE bound index.rev))

theorem value_readback (names : Fin total → DeclName) (count : Nat) (bound : count ≤ total)
    (name : DeclName) :
    subst (constantArguments names count bound) (values names count bound name) =
      (.const name : Tm Head 0) := by
  cases found : positions names count bound name with
  | none => simp only [values, found, subst]
  | some index =>
      have matched : names (Fin.castLE bound index.rev) == name :=
        List.find?_some (p := fun i : Fin count => names (Fin.castLE bound i.rev) == name)
          (a := index) found
      simpa only [values, found, subst, constantArguments] using
        congrArg (Tm.const (Head := Head) (n := 0)) (LawfulBEq.eq_of_beq matched)

theorem type_readback (names : Fin total → DeclName) (count : Nat) (bound : count ≤ total)
    (term : Tm Head 0) :
    subst (constantArguments names count bound)
      (ConstantSubstitution.interpret (values names count bound) Fin.elim0 term) = term := by
  rw [ConstantSubstitution.subst_interpret]
  simp only [value_readback]
  rw [ConstantSubstitution.interpret_constants, TypedEquality.Normalization.subst_closed,
    Tm.liftClosed_at_zero]

theorem context_prefix {source : Rules Head} (names : Fin total → DeclName)
    (types : Fin total → Tm Head 0) {larger smaller : Nat}
    (upper : larger ≤ total) (bound : smaller ≤ larger)
    (formed : CtxFormed source (context names types larger upper)) :
    CtxFormed source (context names types smaller (by omega)) := by
  induction larger with
  | zero =>
      have zero : smaller = 0 := by omega
      subst smaller
      exact .nil
  | succ larger ih =>
      by_cases same : smaller = larger + 1
      · subst smaller; exact formed
      · cases formed with
        | snoc previous _ => exact ih (by omega) (by omega) previous

theorem constantArguments_succ (names : Fin total → DeclName)
    (count : Nat) (bound : count + 1 ≤ total) :
    constantArguments (Head := Head) names (count + 1) bound =
      consSub (.const (names ⟨count, by omega⟩)) (constantArguments names count (by omega)) := by
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro previous
    change Tm.const (names (Fin.castLE bound previous.succ.rev)) =
      Tm.const (names (Fin.castLE (by omega) previous.rev))
    rw [Fin.rev_succ]
    rfl

/-- Reading any parameter type after restoring constants recovers that
entry's original closed type, including its references to earlier names. -/
theorem lookup_readback (names : Fin total → DeclName) (types : Fin total → Tm Head 0)
    (count : Nat) (bound : count ≤ total) (index : Fin count) :
    subst (constantArguments names count bound) (Ctx.lookup (context names types count bound) index) =
      types (Fin.castLE bound index.rev) := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      rw [constantArguments_succ]
      refine Fin.cases ?_ ?_ index
      · simp only [context, Ctx.lookup_snoc_zero, subst_consSub_rename_wk, type_readback]
        rfl
      · intro previous
        simp only [context, Ctx.lookup_snoc_succ, subst_consSub_rename_wk]
        rw [ih (by omega) previous, Fin.rev_succ]
        rfl

/-- Source formation supplies each successive type; the target constant rule
then supplies the next typed argument at its exact original declared type. -/
theorem constantArguments_typed {source target : Rules Head}
    (morphism : source.Morphism target (fun head => head))
    (names : Fin total → DeclName) (types : Fin total → Tm Head 0)
    (known : ∀ index, target.constantType (names index) = some (types index))
    (formed : CtxFormed source (context names types total (by omega))) :
    ∀ (count : Nat) (bound : count ≤ total),
      SubstMor target (context names types count bound) (.nil : Ctx Head 0)
        (constantArguments names count bound) := by
  intro count
  induction count with
  | zero => intro bound index; exact Fin.elim0 index
  | succ count ih =>
      intro bound
      have previous := ih (by omega)
      have formedNext := context_prefix names types (by omega : total ≤ total) bound formed
      cases formedNext with
      | snoc _ typeFormation =>
          obtain ⟨levelHead, isUniverse, sourceType⟩ := typeFormation
          have interpreted := sourceType.of_morphism morphism
          have sourceClosed := interpreted.substitute previous
          have actualType : Typed target .nil (types ⟨count, by omega⟩) (.head levelHead) := by
            simpa only [type_readback, subst] using sourceClosed
          have primitive : Typed target .nil (.const (names ⟨count, by omega⟩))
              (types ⟨count, by omega⟩) := by
            have typed := Derivable.const (Γ := (.nil : Ctx Head 0))
              (known ⟨count, by omega⟩) actualType (morphism.isUniverse isUniverse)
            simpa only [Tm.liftClosed_at_zero] using typed
          rw [constantArguments_succ]
          exact TypedEquality.SubstMor.cons previous _ (by simpa only [type_readback] using primitive)

/-- Every original declaration is typed at its exact original type, as a
component of the constructed substitution. -/
theorem constant_typed {source target : Rules Head}
    (morphism : source.Morphism target (fun head => head))
    (names : Fin total → DeclName) (types : Fin total → Tm Head 0)
    (known : ∀ index, target.constantType (names index) = some (types index))
    (formed : CtxFormed source (context names types total (by omega))) (index : Fin total) :
    Typed target .nil (.const (names index)) (types index) := by
  have assigned := constantArguments_typed morphism names types known formed total (by omega)
  simpa only [constantArguments, lookup_readback, Fin.rev_rev, Fin.castLE_refl] using assigned index.rev

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Declaration.DependentParameters
