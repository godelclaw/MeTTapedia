import Mettapedia.Languages.Megalodon.SourceEtaBoundary
import Mettapedia.Languages.Megalodon.SourceDefinitionInvariant

/-!
# Publication-style beta/eta normalization

This independent pass uses the publication traversal for term substitution
and its occurrence-test/minus-one-shift eta rules. The native pass instead
uses checked binder removal. Their outputs and stability observations agree
on the protected fragment, not just on a set of closed examples. Finite
iteration and definition expansion preserve the correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.SourcePublicationNormalization
open MathdataKernel SourceScopeInvariant SourceEtaBoundary

def pass : Tm → Tm × Bool
  | .app function argument =>
      let (f, fs) := pass function
      let (a, ars) := pass argument
      match f with
      | .lam _ body => (SourceTermFragment.publicationSubstitute 0 a body, false)
      | _ => (.app f a, fs && ars)
  | .lam type body =>
      let (b, stable) := pass body
      match b with
      | .app function (.db 0) =>
          if freeTerm 0 function then (.lam type b, stable) else (lowerTerm 0 function, false)
      | _ => (.lam type b, stable)
  | .typeApp function type =>
      let (f, stable) := pass function
      match f with
      | .typeLam body => (Tm.typeInstantiate type body, false)
      | _ => (.typeApp f type, stable)
  | .typeLam body =>
      let (b, stable) := pass body
      match b with
      | .typeApp function (.var 0) =>
          if freeTypeInTerm 0 function then (.typeLam b, stable) else (lowerTypeInTerm 0 function, false)
      | _ => (.typeLam b, stable)
  | .imp domain codomain =>
      let (d, ds) := pass domain
      let (c, cs) := pass codomain
      (.imp d c, ds && cs)
  | .all type body =>
      let (b, stable) := pass body
      (.all type b, stable)
  | .typeAll body =>
      let (b, stable) := pass body
      (.typeAll b, stable)
  | term => (term, true)

theorem pass_agrees {body : Tm} (safe : Protected body) : pass body = Tm.normalizeOne body := by
  induction body with
  | db | named | prim => rfl
  | app function argument ihf iha =>
      simp only [pass, ihf safe.1, iha safe.2, Tm.normalizeOne]
      cases fn : Tm.normalizeOne function with
      | mk f fs =>
          cases an : Tm.normalizeOne argument with
          | mk a ars =>
              cases f <;> try rfl
              rename_i type body
              have protectedBody := pass_protected safe.1
              rw [fn] at protectedBody
              simp only [Protected] at protectedBody
              simp only [Tm.instantiate, publication_substitution_agrees protectedBody]
  | lam type body ih =>
      simp only [pass, ih safe, Tm.normalizeOne]
      cases normalized : Tm.normalizeOne body with
      | mk result stable =>
          cases result <;> try rfl
          rename_i function argument
          cases argument <;> try rfl
          rename_i index
          cases index with
          | succ index => rfl
          | zero =>
              have protectedFunction := pass_protected (body := body) safe
              rw [normalized] at protectedFunction
              change (if freeTerm 0 function then (.lam type (.app function (.db 0)), stable)
                else (lowerTerm 0 function, false)) =
                (match Tm.dropAt? 0 function with
                | some contracted => (contracted, false)
                | none => (.lam type (.app function (.db 0)), stable))
              rw [term_removal protectedFunction.1 0]
              by_cases used : freeTerm 0 function = true <;> simp [used]
  | typeApp function type ih => simp only [pass, ih safe.2, Tm.normalizeOne]; rfl
  | typeLam body ih =>
      simp only [pass, ih safe.2, Tm.normalizeOne]
      cases normalized : Tm.normalizeOne body with
      | mk result stable =>
          cases result <;> try rfl
          rename_i function type
          cases type <;> try rfl
          rename_i index
          cases index with
          | succ index => rfl
          | zero =>
              change (if freeTypeInTerm 0 function then (.typeLam (.typeApp function (.var 0)), stable)
                else (lowerTypeInTerm 0 function, false)) =
                (match Tm.typeDropAt? 0 function with
                | some contracted => (contracted, false)
                | none => (.typeLam (.typeApp function (.var 0)), stable))
              rw [term_type_removal function 0]
              by_cases used : freeTypeInTerm 0 function = true <;> simp [used]
  | imp domain codomain ihd ihc => simp only [pass, ihd safe.1, ihc safe.2, Tm.normalizeOne]
  | all type body ih => simp only [pass, ih safe, Tm.normalizeOne]
  | typeAll body ih => simp only [pass, ih safe.2, Tm.normalizeOne]

def normalize : Nat → Tm → Option Tm
  | 0, body => let (result, stable) := pass body; if stable then some result else none
  | fuel + 1, body =>
      let (result, stable) := pass body
      if stable then some result else normalize fuel result

theorem normalize_agrees (fuel : Nat) {body : Tm} (safe : Protected body) :
    normalize fuel body = Tm.normalize fuel body := by
  induction fuel generalizing body with
  | zero => simp only [normalize, Tm.normalize, pass_agrees safe]
  | succ fuel ih =>
      simp only [normalize, Tm.normalize, pass_agrees safe]
      cases normalized : Tm.normalizeOne body with
      | mk result stable =>
          by_cases stopped : stable = true
          · simp [stopped]
          · simp only [stopped, Bool.false_eq_true, ↓reduceIte]
            exact ih (by simpa only [normalized] using pass_protected safe)

theorem expanded_normalize_agrees {environment : Environment} (definitions : Definitions environment)
    (fuel : Nat) {body : Tm} (safe : Protected body) :
    ((deltaNormalize environment fuel body).bind (normalize fuel)) = MathdataKernel.normalize environment fuel body := by
  cases expanded : deltaNormalize environment fuel body with
  | none => simp [MathdataKernel.normalize, expanded]
  | some result =>
      simp only [MathdataKernel.normalize, expanded, Option.bind_some]
      exact normalize_agrees fuel ((delta_invariants environment definitions fuel body result expanded).2 safe)

end Mettapedia.Languages.Megalodon.SourcePublicationNormalization
