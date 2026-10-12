import Mettapedia.Languages.OpenTheory.Syntax

/-!
# Exact function-carrier recognition

The existing recognizer checks the operator's complete provenance and its
two arguments. Successful recognition therefore determines the actual type,
rather than merely a printed operator name.
-/

namespace Mettapedia.Languages.OpenTheory.Ty

theorem destFunction?_eq_some_iff (type domain codomain : Ty) :
    type.destFunction? = some (domain, codomain) ↔ type = .function domain codomain := by
  constructor
  · intro recognized
    cases type with
    | var name => simp [destFunction?] at recognized
    | op operator arguments =>
        cases arguments with
        | nil => simp [destFunction?] at recognized
        | cons first rest =>
            cases rest with
            | nil => simp [destFunction?] at recognized
            | cons second remaining =>
                cases remaining with
                | cons third tail => simp [destFunction?] at recognized
                | nil =>
                    simp only [destFunction?] at recognized
                    split at recognized
                    · rename_i same
                      have operatorSame := (TypeOp.same_eq_true_iff _ _).mp same
                      have components := Option.some.inj recognized
                      cases components
                      simp [function, operatorSame]
                    · contradiction
  · intro same
    rw [same]
    exact destFunction?_function domain codomain

end Mettapedia.Languages.OpenTheory.Ty
