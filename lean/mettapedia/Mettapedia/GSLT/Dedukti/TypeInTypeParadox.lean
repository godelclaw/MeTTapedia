import Mettapedia.GSLT.Dedukti.PureTypeSystemChecker

/-!
# A universal `Type : Type` is inconsistent

In the pure type system with one sort `∗`, the axiom `∗ : ∗` and the single
product rule `(∗, ∗, ∗)` (`typeInType`), the type `Π p : ∗. p` is inhabited by a
closed term (`typeInType_inconsistent`), and hence every type is inhabited
(`typeInType_inhabits`). The term is Hurkens' simplification of Girard's
paradox (A. J. C. Hurkens, *A simplification of Girard's paradox*, TLCA 1995),
written with names (`Named`) and compiled to the sorted de Bruijn syntax.

Its derivation is produced by the sound inference procedure of
`PureTypeSystemChecker`, evaluated by the kernel. The type conversions the
paradox needs, such as `σ (τ X) p ≡ X (λy. p (τ (σ y)))`, are witnessed by the
reductions the procedure performs.

Controls: the inference procedure refuses an ill-typed application
(`refuses_star_applied`); in the calculus of constructions, where `∗ : □` and
`□` has no sort, it refuses the paradox term (`constructions_refuses_paradox`).
The refusal is a statement about the procedure, not a proof of
underivability: consistency of the calculus of constructions is not proved
here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.TypeInTypeParadox

open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFProfile (Profile ProductRule)
open Checker

/-- `∗ : ∗` with the product rule `(∗, ∗, ∗)`. -/
def typeInType : Profile where
  sortAxiom := fun _ => some .type
  products := [⟨.type, .type, .type⟩]

/-- The only product rule of `typeInType`. -/
abbrev starRule : ProductRule := ⟨.type, .type, .type⟩

/-! ## Named terms -/

/-- Terms with named binders, for writing the paradox legibly. -/
inductive Named where
  | var (name : String)
  | star
  | pi (name : String) (domain body : Named)
  | lam (name : String) (domain body : Named)
  | app (function argument : Named)

/-- Compile to de Bruijn indices; every product uses `(∗, ∗, ∗)` and every
abstraction has a domain of sort `∗`. -/
def Named.compile (scope : List String) : Named → PTerm
  | .var name => .var (scope.idxOf name)
  | .star => .sort .type
  | .pi name domain body => .pi starRule (domain.compile scope) (body.compile (name :: scope))
  | .lam name domain body => .lam .type (domain.compile scope) (body.compile (name :: scope))
  | .app function argument => .app (function.compile scope) (argument.compile scope)

open Named

/-- A non-dependent product. The bound name `_` is never referenced. -/
def arrow (domain codomain : Named) : Named := .pi "_" domain codomain

def falsum : Named := .pi "A" .star (.var "A")

def neg (proposition : Named) : Named := arrow proposition falsum

/-- Predicates on a type. -/
def pow (carrier : Named) : Named := arrow carrier .star

/-- Hurkens' powerful universe. -/
def U : Named :=
  .pi "X" .star (arrow (arrow (pow (pow (.var "X"))) (.var "X")) (pow (pow (.var "X"))))

def tau : Named :=
  .lam "t" (pow (pow U))
    (.lam "X" .star
      (.lam "f" (arrow (pow (pow (.var "X"))) (.var "X"))
        (.lam "p" (pow (.var "X"))
          (.app (.var "t")
            (.lam "x" U
              (.app (.var "p")
                (.app (.var "f") (.app (.app (.var "x") (.var "X")) (.var "f")))))))))

def sigma : Named :=
  .lam "s" U (.app (.app (.var "s") U) (.lam "t" (pow (pow U)) (.app tau (.var "t"))))

def Delta : Named :=
  .lam "y" U
    (neg (.pi "p" (pow U)
      (arrow (.app (.app sigma (.var "y")) (.var "p"))
        (.app (.var "p") (.app tau (.app sigma (.var "y")))))))

def Omega : Named :=
  .app tau (.lam "p" (pow U)
    (.pi "x" U (arrow (.app (.app sigma (.var "x")) (.var "p")) (.app (.var "p") (.var "x")))))

/-- `Π p. (Π x. σ x p → p x) → p Ω`. -/
def lemma0Type : Named :=
  .pi "p" (pow U)
    (arrow (.pi "x" U (arrow (.app (.app sigma (.var "x")) (.var "p")) (.app (.var "p") (.var "x"))))
      (.app (.var "p") Omega))

def lemma0 : Named :=
  .lam "p" (pow U)
    (.lam "h1" (.pi "x" U (arrow (.app (.app sigma (.var "x")) (.var "p")) (.app (.var "p") (.var "x"))))
      (.app (.app (.var "h1") Omega)
        (.lam "x" U (.app (.var "h1") (.app tau (.app sigma (.var "x")))))))

/-- `Π x. σ x Δ → Δ x`. -/
def middle : Named :=
  .lam "x" U
    (.lam "h2" (.app (.app sigma (.var "x")) Delta)
      (.lam "h3" (.pi "p" (pow U)
          (arrow (.app (.app sigma (.var "x")) (.var "p"))
            (.app (.var "p") (.app tau (.app sigma (.var "x"))))))
        (.app (.app (.app (.var "h3") Delta) (.var "h2"))
          (.lam "p" (pow U)
            (.app (.var "h3") (.lam "y" U (.app (.var "p") (.app tau (.app sigma (.var "y"))))))))))

/-- Hurkens' paradox: a closed proof of `Π p : ∗. p`. -/
def paradox : Named :=
  .app
    (.lam "h0" lemma0Type
      (.app (.app (.app (.var "h0") Delta) middle)
        (.lam "p" (pow U)
          (.app (.var "h0") (.lam "y" U (.app (.var "p") (.app tau (.app sigma (.var "y")))))))))
    lemma0

abbrev paradoxTerm : PTerm := paradox.compile []

abbrev falsumTerm : PTerm := falsum.compile []

/-! ## The paradox -/

theorem paradox_inferred :
    inferTerm typeInType 400 200 [] paradoxTerm = some (falsumTerm, .type) := by
  decide +kernel

/-- **`Type : Type` is inconsistent**: `Π p : ∗. p` has a closed proof. -/
theorem typeInType_inconsistent :
    Derives typeInType [] (.term paradoxTerm falsumTerm .type) :=
  inferTerm_sound paradox_inferred

/-- Consequently every closed type of sort `∗` is inhabited. -/
theorem typeInType_inhabits {type : PTerm} (formed : Derives typeInType [] (.type type .type)) :
    Derives typeInType [] (.term (.app paradoxTerm type) type .type) := by
  have bodyFormed : Derives typeInType [(.sort .type, .type)] (.type (.var 0) .type) :=
    .ofTerm (.var rfl) rfl
  have applied := Derives.app (.sort rfl) bodyFormed (by decide) typeInType_inconsistent
    (.toTerm formed rfl)
  have substituted : PTerm.subst0 type (.var 0) = type := by
    simp [PTerm.subst0, PTerm.subst]
  rw [substituted] at applied
  exact applied

/-- Derivability grows along inclusion of profiles. -/
theorem derives_mono {small large : Profile} (included : small ⊑ large)
    {context : SortedCtx} {judgment : Judgment} (derivation : Derives small context judgment) :
    Derives large context judgment := by
  induction derivation with
  | sort axiomHolds => exact .sort (included.1 _ _ axiomHolds)
  | pi _ _ member ihDomain ihBody => exact .pi ihDomain ihBody (included.2 _ member)
  | ofTerm _ axiomHolds ih => exact .ofTerm ih (included.1 _ _ axiomHolds)
  | toTerm _ axiomHolds ih => exact .toTerm ih (included.1 _ _ axiomHolds)
  | var found => exact .var found
  | lam _ _ member _ ihDomain ihBodyType ihBody =>
      exact .lam ihDomain ihBodyType (included.2 _ member) ihBody
  | app _ _ member _ _ ihDomain ihBodyType ihFunction ihArgument =>
      exact .app ihDomain ihBodyType (included.2 _ member) ihFunction ihArgument
  | conv _ convertible _ ihTerm ihTarget => exact .conv ihTerm convertible ihTarget

/-- Every profile containing `∗ : ∗` and `(∗, ∗, ∗)` proves `Π p : ∗. p`. -/
theorem inconsistent_of_typeInType {profile : Profile} (included : typeInType ⊑ profile) :
    Derives profile [] (.term paradoxTerm falsumTerm .type) :=
  derives_mono included typeInType_inconsistent

/-! ## Controls -/

/-- The procedure refuses applying `∗` to `∗`. -/
theorem refuses_star_applied :
    inferTerm typeInType 10 10 [] (.app (.sort .type) (.sort .type)) = none := by
  decide +kernel

/-- In the calculus of constructions the procedure refuses the paradox term. -/
theorem constructions_refuses_paradox :
    inferTerm constructions 400 200 [] paradoxTerm = none := by
  decide +kernel

#print axioms typeInType_inconsistent
#print axioms typeInType_inhabits
#print axioms inconsistent_of_typeInType

end Mettapedia.GSLT.Dedukti.TypeInTypeParadox
