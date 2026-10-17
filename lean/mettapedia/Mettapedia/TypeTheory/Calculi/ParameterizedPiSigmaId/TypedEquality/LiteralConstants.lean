import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.PartialConstants
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Generation

/-!
# Literals are declared constants

A literal of a host language (a number, a string or a truth value written in a
program) is typed the way a declared constant is typed.  The host says only
which sort a literal belongs to.  That sort is an ordinary constant, which the
theory declares at a universe, and the literal enters the rule package as one
more declared constant at that sort (`Rules.addConstant`): through the same
`constantType` field as every declaration.  No rule of the judgment mentions
literals.

* `literal_typed`: a literal has its sort as a type, by the constant rule at
  its declaration; `literal_type_below`: every type of a literal lies above its
  sort, by generation for constants.  The typing of a literal is an instance
  of the typing of a declared constant.
* `undeclared_untyped`: a constant the package does not declare has no type.
  A literal whose sort the theory does not declare is not declared either, so
  the kernel has nothing to establish or refute about it.
* `Derivable.mapConst_iff`: renaming constants along a bijection both
  preserves and reflects every judgment, so it preserves and reflects every
  refutation.
* `RulesRenaming.addConstant`: a renaming of packages extends to the packages
  with one more declared constant, sent to its image.
* `literal_verdict_sort_blind`: a renaming of a package into itself that is an
  involution decides every statement as it decides its image.  Over the tower
  of universes (`Instances.TowerLiteralConstants`), a theory declares the host
  sort `String` with the literal `banana`, and a user's sort `Color` with the
  user's constant `red`; swapping `String` with `Color` and `banana` with `red`
  is a symmetry of the package.  So every judgment about the literal is
  derivable exactly when the same judgment about the user's constant is: a
  mismatch is refuted for the literal exactly when it is refuted for a
  constant of a user's sort in its place.  The judgment never inspects which
  sort a literal has.

The theorems say that the verdicts coincide.  That a particular mismatch is
refuted is the kernel's generic refutation for declared constants, which
applies to both alike: the instance refutes the literal as a type, as a
function and as an argument of the successor of the numbers
(`Synth.not_typed`, `Synth.not_applicable`, `not_equal_of_distinct_rigid`),
and reads the same refutations of the user's constant off them through the
symmetry.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

variable {Head : Type}

/-! ## Renaming composes -/

theorem Tm.mapConst_mapConst (f g : DeclName → DeclName) {n : Nat} (t : Tm Head n) :
    (t.mapConst f).mapConst g = t.mapConst (fun c => g (f c)) := by
  induction t with
  | var => rfl
  | const => rfl
  | head => rfl
  | pi A B ihA ihB => simp only [Tm.mapConst, ihA, ihB]
  | sigma A B ihA ihB => simp only [Tm.mapConst, ihA, ihB]
  | id A a b ihA iha ihb => simp only [Tm.mapConst, ihA, iha, ihb]
  | lam body ih => simp only [Tm.mapConst, ih]
  | app h a ihh iha => simp only [Tm.mapConst, ihh, iha]
  | pair a b iha ihb => simp only [Tm.mapConst, iha, ihb]
  | fst p ih => simp only [Tm.mapConst, ih]
  | snd p ih => simp only [Tm.mapConst, ih]
  | refl a ih => simp only [Tm.mapConst, ih]

theorem Ctx.mapConst_mapConst (f g : DeclName → DeclName) {n : Nat} (Γ : Ctx Head n) :
    (Γ.mapConst f).mapConst g = Γ.mapConst (fun c => g (f c)) := by
  induction Γ with
  | nil => rfl
  | snoc Γ A ih => simp only [Ctx.mapConst, ih, Tm.mapConst_mapConst]

namespace TypedEquality

theorem Statement.mapConst_mapConst (f g : DeclName → DeclName) (st : Statement Head) :
    (st.mapConst f).mapConst g = st.mapConst (fun c => g (f c)) := by
  cases st <;>
    simp only [Statement.mapConst, Tm.mapConst_mapConst, Ctx.mapConst_mapConst]

/-- Renaming back along a left inverse returns the statement. -/
theorem Statement.mapConst_leftInverse {f g : DeclName → DeclName}
    (inverse : ∀ c, g (f c) = c) (st : Statement Head) :
    (st.mapConst f).mapConst g = st := by
  rw [Statement.mapConst_mapConst]
  have identity : (fun c => g (f c)) = (fun c => c) := funext inverse
  rw [identity]
  cases st <;> simp only [Statement.mapConst, Tm.mapConst_id, Ctx.mapConst_id]

/-- **Renaming along a bijection preserves and reflects derivability.** -/
theorem Derivable.mapConst_iff {R R' : Rules Head} {f g : DeclName → DeclName}
    (forward : RulesRenaming R R' f) (backward : RulesRenaming R' R g)
    (inverse : ∀ c, g (f c) = c) {st : Statement Head} :
    Derivable R st ↔ Derivable R' (st.mapConst f) := by
  constructor
  · exact Derivable.mapConst forward
  · intro derivation
    have back := Derivable.mapConst backward derivation
    rwa [Statement.mapConst_leftInverse inverse] at back

/-- A renaming of packages extends to the packages with one more declared
constant `c : T`, sent to `f c : T` renamed, when `f` sends no other name to
`f c`. -/
theorem RulesRenaming.addConstant {R R' : Rules Head} {f : DeclName → DeclName}
    (ren : RulesRenaming R R' f) {c : DeclName} {T : Tm Head 0}
    (separates : ∀ d, f d = f c → d = c) :
    RulesRenaming (R.addConstant c T) (R'.addConstant (f c) (T.mapConst f)) f where
  headTyping h := ren.headTyping h
  isUniverse h := ren.isUniverse h
  join h := ren.join h
  cumulative h := ren.cumulative h
  headEq h := ren.headEq h
  constantType := by
    intro name type declared
    cases hb : name == c with
    | true =>
        have same : name = c := LawfulBEq.eq_of_beq hb
        subst same
        have hT : T = type := by
          simp only [Rules.addConstant, beq_self_eq_true, cond_true] at declared
          injection declared
        subst hT
        simp only [Rules.addConstant, beq_self_eq_true, cond_true]
    | false =>
        have different : name ≠ c := by
          intro same
          rw [same, beq_self_eq_true] at hb
          exact Bool.noConfusion hb
        have declaredR : R.constantType name = some type := by
          simpa only [Rules.addConstant, hb, cond_false] using declared
        have imageDifferent : (f name == f c) = false := by
          cases hf : f name == f c with
          | false => rfl
          | true => exact absurd (separates name (LawfulBEq.eq_of_beq hf)) different
        simp only [Rules.addConstant, imageDifferent, cond_false]
        exact ren.constantType declaredR
  computation step := ren.computation step

/-! ## The typing of a literal is the typing of a declared constant -/

section Literal

variable {R : Rules Head} {literal sort : DeclName}

/-- **A literal has its sort as a type**, by the constant rule at its
declaration `literal : sort`, once the theory declares the sort at a
universe. -/
theorem literal_typed (fresh : R.constantType literal = none) {u : Head}
    (sortTyped : Typed R .nil (.const sort) (.head u)) (isU : R.isUniverse u)
    {n : Nat} (Γ : Ctx Head n) :
    Typed (R.addConstant literal (.const sort)) Γ (.const literal) (.const sort) := by
  have formed := Normalization.Typed.to_addConstant (T := .const sort) fresh sortTyped
  have declared :
      (R.addConstant literal (.const sort)).constantType literal = some (.const sort) := by
    simp only [Rules.addConstant, beq_self_eq_true, cond_true]
  exact Derivable.const (Γ := Γ) declared formed isU

/-- **Every type of a literal lies above its sort**: generation for a
constant reads the literal's declared type, and nothing else. -/
theorem literal_type_below {n : Nat} {Γ : Ctx Head n} {T : Tm Head n}
    (typed : Typed (R.addConstant literal (.const sort)) Γ (.const literal) T) :
    TypeLe (R.addConstant literal (.const sort)) Γ (.const sort) T := by
  obtain ⟨type, _, declared, _, _, below⟩ := Typed.generation typed
  have hType : type = .const sort := by
    simp only [Rules.addConstant, beq_self_eq_true, cond_true] at declared
    injection declared with same
    exact same.symm
  subst hType
  exact below

end Literal

/-- **No declaration, no type.**  A constant the package does not declare,
a literal at a sort the theory does not declare among them, has no type. -/
theorem undeclared_untyped {R : Rules Head} {c : DeclName}
    (undeclared : R.constantType c = none) {n : Nat} {Γ : Ctx Head n} {T : Tm Head n} :
    ¬ Typed R Γ (.const c) T := by
  intro typed
  obtain ⟨_, _, declared, _, _, _⟩ := Typed.generation typed
  rw [undeclared] at declared
  cases declared

/-! ## The verdict is blind to the sort -/

/-- **A symmetry decides a statement as it decides its image.**  An involution
of names that renames a package into itself decides every statement as it
decides the renamed statement: a statement is refuted exactly when its image
is. -/
theorem literal_verdict_sort_blind {R : Rules Head} {f : DeclName → DeclName}
    (symmetry : RulesRenaming R R f) (involution : ∀ c, f (f c) = c)
    (st : Statement Head) :
    Derivable R st ↔ Derivable R (st.mapConst f) :=
  Derivable.mapConst_iff symmetry symmetry involution

end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
