import Mettapedia.OSLF.Syntax.DeclaredBindingOperational
import Mettapedia.GSLT.LanguageDef.TemplateScope.Spectrum

/-!
# Declared local binding and the existing lexical-fresh activation

The scope-policy model elaborates a lexical binding to an activation with
owned store names and an internal lambda parameter. Its value lies outside
that activation. Actual activation substitution keeps that argument intact,
copies owned names by activation identity, and then matches the fresh pattern.
These are properties of the existing elaborator, substitution and matcher.

The scoped interpretation reads the successfully bound local variable as
the beta argument. The target beta equation is proved separately, including
open values. No statement here identifies every evaluation profile or the
native runtime with the scope-model evaluator.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.Binding.DeclaredBindingInterpretation.Activation

open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

variable {S : Type u} {X : Type v} [DecidableEq X]

/-- Every nonempty introduced pattern list uses the existing activation
construction. The source expression is elaborated in the unextended frame. -/
theorem lexical_pattern_activation (root : Owner) (env : REnv X) (crossing : List X) (pos : Owner)
    (written : Option (List X)) (pattern value body : Src S X) (first : X) (rest : List X)
    (introduced : lfIntro written pattern crossing = first :: rest) :
    elabLF root env crossing pos (.letS pattern value body written) =
      .app
        (.lam (letParam (pos ++ [2]) first)
          ((first :: rest).map fun y => (pos ++ [2], y))
          (.letP
            (elabLF root (env.update (first :: rest) (pos ++ [2]))
              (crossIn written (first :: rest) crossing) (pos ++ [0]) pattern)
            (.pvar (letParam (pos ++ [2]) first))
            (elabLF root (env.update (first :: rest) (pos ++ [2]))
              (crossIn written (first :: rest) crossing) (pos ++ [2]) body)))
        (elabLF root env crossing (pos ++ [1]) value) := by
  simp only [elabLF, introduced]

/-- The declared `where` instance actually introduces its one pattern name;
this construction data is proved rather than supplied as an interface field. -/
theorem lexical_single_introduction (name : X) :
    lfIntro (S := S) none (.sv name) [] = [name] := by
  simp [lfIntro, Src.patNames]

theorem lexical_where_shape (root : Owner) (env : REnv X) (pos : Owner) (name : X)
    (value body : Src S X) :
    elabLF root env [] pos (.letS (.sv name) value body none) =
      .app (.lam (letParam (pos ++ [2]) name) [(pos ++ [2], name)]
        (.letP (.var (.src (pos ++ [2], name)))
          (.pvar (letParam (pos ++ [2]) name))
          (elabLF root (env.update [name] (pos ++ [2])) [] (pos ++ [2]) body)))
        (elabLF root env [] (pos ++ [1]) value) := by
  simpa only [List.map_cons, List.map_nil, elabLF, slotVar, REnv.update,
    List.mem_singleton, if_pos rfl, crossIn, Option.getD_none, List.filter_nil,
    List.nil_append, ite_true] using
    lexical_pattern_activation root env [] pos none (.sv name) value body name []
      (lexical_single_introduction (S := S) name)

/-- Activation substitutes the supplied argument directly for the internal
parameter. It does not freshen names occurring in that argument; the owned
names of the pattern and the body are copied, inside their sealed code too. -/
theorem activation_value_outside (store : GStore S X) (path : Path)
    (parameter : Nm X) (own : List X) (pattern body argument : Tm S X) :
    activate .static store path parameter own
        (.letP pattern (.pvar parameter) body) argument =
      .letP
        (subst (renameOwn path own) (Sub.single parameter argument) (sealRen path own pattern))
        argument
        (subst (renameOwn path own) (Sub.single parameter argument) (sealRen path own body)) := by
  simp [activate, sealRen, subst, Sub.single]

/-- Each declared store variable is copied to the current activation, while
the received argument keeps its dependencies in the enclosing context. -/
theorem activation_fresh_pattern (store : GStore S X) (path : Path)
    (parameter : Nm X) (own : List X) (localName : X) (member : localName ∈ own)
    (body argument : Tm S X) :
    activate .static store path parameter own
        (.letP (.var (.src localName)) (.pvar parameter) body) argument =
      .letP (.var (.inst path (.src localName))) argument
        (subst (renameOwn path own) (Sub.single parameter argument) (sealRen path own body)) := by
  rw [activation_value_outside]
  simp [sealRen, subst, renameOwn, ownKey, member]

omit [DecidableEq X] in
theorem fresh_identity_differs_from_source (path : Path) (name : X) :
    (Nm.inst path (.src name) : Nm X) ≠ .src name := by
  intro impossible
  cases impossible

omit [DecidableEq X] in
theorem distinct_activations (first second : Path) (different : first ≠ second) (name : X) :
    (Nm.inst first (.src name) : Nm X) ≠ .inst second (.src name) := by
  intro equal
  exact different (Nm.inst.inj equal).1

variable [DecidableEq S]

/-- A concrete successful match is constructed for every ground argument.
The fresh variable's readout is exactly that argument, and previous bindings
persist. No fresh-store carrier or matching existence is assumed. -/
theorem fresh_match_constructed (store : GStore S X) (name : Nm X)
    (unbound : store name = Option.none) (argument : GVal S X) :
    ∃ next : GStore S X,
      Mettapedia.GSLT.LanguageDef.TemplateScope.matchT store (.var name) argument.toTm = some next ∧
      next name = some argument ∧ store ⊑ next ∧
      act next (.var name) = argument.toTm ∧
      (∀ other, other ≠ name → next other = store other) := by
  let next : GStore S X := fun key => if key = name then some argument else store key
  have matching : Mettapedia.GSLT.LanguageDef.TemplateScope.matchT store (.var name) argument.toTm = some next := by
    simp only [Mettapedia.GSLT.LanguageDef.TemplateScope.matchT, GVal.toTm_toGVal?]
    simp only [refineStep, unbound]
    rfl
  have binding : next name = some argument := by simp [next]
  refine ⟨next, matching, binding, ?_, ?_, ?_⟩
  · exact refineStep_mono (by
      simpa only [Mettapedia.GSLT.LanguageDef.TemplateScope.matchT, GVal.toTm_toGVal?] using matching)
  · simp [act, subst, envSub, binding]
  · intro other different
    simp only [next, if_neg different]

/-- A concrete caller store retains every supplied source binding. Activation
identities are a disjoint constructor and therefore begin unbound. -/
def sourceStore (caller : X → Option (GVal S X)) : GStore S X
  | .src name => caller name
  | .inst _ _ => none

/-- Distinct activation paths construct two compatible local bindings, for
arbitrary caller stores and ground values. Their readouts remain separate,
and every caller binding persists. -/
theorem two_fresh_activations (caller : X → Option (GVal S X))
    (first second : Path) (different : first ≠ second) (name : X)
    (left right : GVal S X) :
    ∃ one two : GStore S X,
      Mettapedia.GSLT.LanguageDef.TemplateScope.matchT (sourceStore caller)
        (.var (.inst first (.src name))) left.toTm = some one ∧
      Mettapedia.GSLT.LanguageDef.TemplateScope.matchT one
        (.var (.inst second (.src name))) right.toTm = some two ∧
      two (.inst first (.src name)) = some left ∧
      two (.inst second (.src name)) = some right ∧
      sourceStore caller ⊑ two := by
  have separate : (Nm.inst second (.src name) : Nm X) ≠ .inst first (.src name) :=
    distinct_activations second first different.symm name
  obtain ⟨one, firstMatch, firstValue, firstExtension, _, firstFrame⟩ :=
    fresh_match_constructed (sourceStore caller) (.inst first (.src name)) rfl left
  have secondFresh : one (.inst second (.src name)) = none := by
    rw [firstFrame _ separate]
    rfl
  obtain ⟨two, secondMatch, secondValue, secondExtension, _, _⟩ :=
    fresh_match_constructed one (.inst second (.src name)) secondFresh right
  refine ⟨one, two, firstMatch, secondMatch, secondExtension _ _ firstValue,
    secondValue, ?_⟩
  intro key value present
  exact secondExtension key value (firstExtension key value present)

/-- Lambda values use the actual evaluator's substitution case, under the
same fresh-name condition. This covers higher-order arguments as well as
the preceding ground-store case. -/
theorem fresh_lambda_argument (disc : Disc) (program : S → Option (Tm S X))
    (fuel : Nat) (path : Path) (store : GStore S X) (localName parameter : Nm X)
    (own : List X) (body consumer : Tm S X) (unbound : store localName = Option.none) :
    run disc program (fuel + 1) path store
        (.letP (.var localName) (.lam parameter own body) consumer) =
      run disc program fuel path store
        (subst (Sub.single localName (.lam parameter own body)) Sub.none consumer) :=
  run_letP_lam disc program fuel path store localName parameter own body consumer unbound

/-- The scoped interpretation retains precisely the same outside-value
boundary: its actual beta rule substitutes the supplied outer term only in
the body opened by the declaration. -/
theorem interpreted_where_activation {Γ : Ctx sig} (value : Term sig Γ .term)
    (body : Term sig (.term :: Γ) .term) :
    LambdaContextualRung.Step Γ (lower (whereBinding value body))
      (inst (S := Target.sig) (lower body) (lower value)) := by
  rw [lower_where]
  exact .beta (lower body) (lower value)

end Mettapedia.OSLF.Binding.DeclaredBindingInterpretation.Activation
