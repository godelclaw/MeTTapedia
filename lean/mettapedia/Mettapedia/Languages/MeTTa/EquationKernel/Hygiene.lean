import Mettapedia.Languages.MeTTa.EquationKernel.Certificate

/-!
# Hygiene of equation application

Equation variables are local to each use. Three facts make that precise
without trusting any renaming performed by a producer.

* Alpha-invariance (`reaches_alphaVariant`): replacing stored equations by
  variable-renamed copies does not change reachability. A certificate may
  cite the stored spelling; the bindings carry the per-use instance.
* No capture in the core step: the bindings of a step instantiate the
  equation only, and the subject's variables are constants. Freshness is
  therefore not a soundness condition of `Reaches`.
* Fresh instances are most general (`fresh_most_general`): when every
  variable that occurs only on the right side is sent to a distinct variable
  absent from the subject, every other result of the same equation at the
  same position is an instance of that result by a substitution that leaves
  the subject untouched. `freshRows` checks this on certificate rows;
  identifying a new variable with a subject variable is refused there, while
  the core judgment still accepts it as an instance.

`narrowing_step`: a supplied substitution that unifies a subatom with an
instance of a stored left side licenses rewriting the instantiated subject,
whatever the renaming of the rule. It does not compute a unifier, and it does
not establish HE's query semantics, evaluation strategy, freshness
discipline or results multiset; a correspondence with HE evaluation is a
separate obligation. Renaming apart matters for finding unifiers, not for
this soundness (`no_unifier_without_renaming`, `unifier_after_renaming`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.EquationKernel

open Mettapedia.Languages.MeTTa.OSLFCore (Atom Atomspace)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (Var Subst subst vars)

/-! ## Variables -/

theorem varsList_eq_flatMap : ∀ atoms : List Atom, vars.varsList atoms = atoms.flatMap vars
  | [] => rfl
  | atom :: atoms => by simp [vars.varsList, varsList_eq_flatMap atoms]

theorem vars_expression (atoms : List Atom) : vars (.expression atoms) = atoms.flatMap vars := by
  simp only [vars, varsList_eq_flatMap]

theorem mem_vars_expression {atoms : List Atom} {name : Var} :
    name ∈ vars (.expression atoms) ↔ ∃ child ∈ atoms, name ∈ vars child := by
  simp [vars_expression]

/-- Substitutions that agree, as replacements, on the variables of an atom
give the same instance. Silence and the identity binding agree. -/
theorem subst_congr_getD (σ τ : Subst) (atom : Atom)
    (agree : ∀ name ∈ vars atom, (σ name).getD (.var name) = (τ name).getD (.var name)) :
    subst σ atom = subst τ atom := by
  match atom with
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .var name => simpa [subst] using agree name (by simp [vars])
  | .expression atoms =>
      rw [subst_expression, subst_expression]
      congr 1
      apply List.map_congr_left
      intro child member
      exact subst_congr_getD σ τ child fun name inner =>
        agree name (mem_vars_expression.mpr ⟨child, member, inner⟩)
termination_by sizeOf atom
decreasing_by
  have := List.sizeOf_lt_of_mem member
  simp_wf
  omega

/-- Equal instances of one atom agree as replacements on its variables. -/
theorem getD_agree_of_subst_eq (σ τ : Subst) (atom : Atom) (same : subst σ atom = subst τ atom) :
    ∀ name ∈ vars atom, (σ name).getD (.var name) = (τ name).getD (.var name) := by
  match atom with
  | .symbol _ => simp [vars]
  | .grounded _ => simp [vars]
  | .var name =>
      intro other member
      simp only [vars, List.mem_singleton] at member
      subst member
      simpa [subst] using same
  | .expression atoms =>
      intro name member
      obtain ⟨child, childMember, inner⟩ := mem_vars_expression.mp member
      rw [subst_expression, subst_expression] at same
      have mapped := Atom.expression.inj same
      have childSame : subst σ child = subst τ child :=
        (List.map_inj_left.mp mapped) child childMember
      exact getD_agree_of_subst_eq σ τ child childSame name inner
termination_by sizeOf atom
decreasing_by
  have := List.sizeOf_lt_of_mem childMember
  simp_wf
  omega

/-- Variables of an instance come from the substituted variables' values or
from silent variables. -/
theorem vars_subst_subset (σ : Subst) (atom : Atom) :
    ∀ name ∈ vars (subst σ atom), ∃ source ∈ vars atom,
      name ∈ vars ((σ source).getD (.var source)) := by
  match atom with
  | .symbol _ => simp [subst, vars]
  | .grounded _ => simp [subst, vars]
  | .var source =>
      intro name member
      exact ⟨source, by simp [vars], by simpa [subst] using member⟩
  | .expression atoms =>
      intro name member
      rw [subst_expression, mem_vars_expression] at member
      obtain ⟨child, childMember, inner⟩ := member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp childMember
      obtain ⟨source, sourceMember, found⟩ := vars_subst_subset σ original name inner
      exact ⟨source, mem_vars_expression.mpr ⟨original, originalMember, sourceMember⟩, found⟩
termination_by sizeOf atom
decreasing_by
  have := List.sizeOf_lt_of_mem originalMember
  simp_wf
  omega

theorem subst_eq_self_of_silent (θ : Subst) (atom : Atom)
    (silent : ∀ name ∈ vars atom, θ name = none) : subst θ atom = atom :=
  SubstitutionAlgebra.subst_eq_self_of_silentOn θ atom silent

/-! ## Alpha-invariance of stored equations -/

/-- Rename every variable by a bijection of names. -/
def variableRenaming (ρ : Var ≃ Var) : Subst := fun name => some (.var (ρ name))

def rename (ρ : Var ≃ Var) (atom : Atom) : Atom := subst (variableRenaming ρ) atom

/-- Two equation atoms are alpha-variants when one bijective renaming takes
both sides of the first to the sides of the second. -/
def AlphaVariant (equation other : Atom) : Prop :=
  ∃ (left right : Atom) (ρ : Var ≃ Var), equation = Atom.equality left right ∧
    other = Atom.equality (rename ρ left) (rename ρ right)

/-- The instance of a renamed atom that undoes the renaming. -/
def unrename (ρ : Var ≃ Var) (σ : Subst) : Subst :=
  fun name => some ((σ (ρ.symm name)).getD (.var (ρ.symm name)))

theorem subst_unrename (ρ : Var ≃ Var) (σ : Subst) (atom : Atom) :
    subst (unrename ρ σ) (rename ρ atom) = subst σ atom := by
  unfold rename
  rw [SubstitutionAlgebra.subst_subst]
  apply subst_congr_getD
  intro name _
  simp [SubstitutionAlgebra.comp, variableRenaming, unrename, subst]

theorem Step.of_alphaVariant {space other : Atomspace}
    (variant : ∀ equation ∈ space.atoms, ∃ copy ∈ other.atoms, AlphaVariant equation copy)
    {source target : Atom} (step : Step space source target) : Step other source target := by
  cases step with
  | rewrite context σ stored =>
      obtain ⟨copy, copyStored, left, right, ρ, same, rfl⟩ := variant _ stored
      have sides := (equationSides_eq_some.mpr same).symm.trans (equationSides_equality _ _)
      simp only [Option.some.injEq, Prod.mk.injEq] at sides
      obtain ⟨rfl, rfl⟩ := sides
      rw [← subst_unrename ρ σ, ← subst_unrename ρ σ right]
      exact .rewrite context _ copyStored

/-- Renamed copies of the stored equations reach exactly as the originals. -/
theorem reaches_alphaVariant {space other : Atomspace}
    (variant : ∀ equation ∈ space.atoms, ∃ copy ∈ other.atoms, AlphaVariant equation copy)
    {source target : Atom} (reaches : Reaches space source target) : Reaches other source target := by
  induction reaches with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step.of_alphaVariant variant)

theorem AlphaVariant.symm {equation other : Atom} (variant : AlphaVariant equation other) :
    AlphaVariant other equation := by
  obtain ⟨left, right, ρ, rfl, rfl⟩ := variant
  refine ⟨rename ρ left, rename ρ right, ρ.symm, rfl, ?_⟩
  have back : ∀ atom, rename ρ.symm (rename ρ atom) = atom := by
    intro atom
    unfold rename
    rw [SubstitutionAlgebra.subst_subst]
    calc subst (SubstitutionAlgebra.comp (variableRenaming ρ) (variableRenaming ρ.symm)) atom
        = subst SubstitutionAlgebra.empty atom := by
          apply subst_congr_getD
          intro name _
          simp [SubstitutionAlgebra.comp, variableRenaming, subst, SubstitutionAlgebra.empty]
      _ = atom := SubstitutionAlgebra.subst_empty atom
  rw [back, back]

/-! ## Variables of instances and contexts -/

/-- Each variable's replacement occurs in the instance. -/
theorem vars_replacement_subset (σ : Subst) (atom : Atom) :
    ∀ name ∈ vars atom, ∀ inner ∈ vars ((σ name).getD (.var name)), inner ∈ vars (subst σ atom) := by
  match atom with
  | .symbol _ => simp [vars]
  | .grounded _ => simp [vars]
  | .var name =>
      intro other member inner innerMember
      simp only [vars, List.mem_singleton] at member
      subst member
      simpa [subst] using innerMember
  | .expression atoms =>
      intro name member inner innerMember
      obtain ⟨child, childMember, nameInChild⟩ := mem_vars_expression.mp member
      rw [subst_expression, mem_vars_expression]
      exact ⟨subst σ child, List.mem_map.mpr ⟨child, childMember, rfl⟩,
        vars_replacement_subset σ child name nameInChild inner innerMember⟩
termination_by sizeOf atom
decreasing_by
  have := List.sizeOf_lt_of_mem childMember
  simp_wf
  omega

theorem vars_fill_inner (context : Context) (atom : Atom) :
    ∀ name ∈ vars atom, name ∈ vars (context.fill atom) := by
  induction context with
  | hole => exact fun _ member => member
  | arg left inner right ih =>
      intro name member
      exact mem_vars_expression.mpr ⟨inner.fill atom, by simp, ih name member⟩

/-- A substitution silent on a filled context leaves the context unchanged. -/
theorem Context.substitute_eq_self (θ : Subst) (context : Context) (atom : Atom)
    (silent : ∀ name ∈ vars (context.fill atom), θ name = none) :
    context.substitute θ = context := by
  induction context with
  | hole => rfl
  | arg left inner right ih =>
      have keep : ∀ child, child ∈ left ∨ child ∈ right → subst θ child = child := by
        intro child member
        apply subst_eq_self_of_silent
        intro name inner'
        apply silent
        refine mem_vars_expression.mpr ⟨child, ?_, inner'⟩
        rcases member with here | there
        · exact List.mem_append_left _ here
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ there)
      have innerSame := ih fun name member =>
        silent name (mem_vars_expression.mpr ⟨inner.fill atom, by simp, member⟩)
      simp only [Context.substitute, innerSame]
      congr 1
      · exact (List.map_congr_left fun child member => keep child (.inl member)).trans
          (List.map_id left)
      · exact (List.map_congr_left fun child member => keep child (.inr member)).trans
          (List.map_id right)

/-! ## Fresh instances -/

/-- Variables of the right side that do not occur on the left side. -/
def rightOnly (left right : Atom) : List Var := (vars right).filter fun name => name ∉ vars left

/-- A fresh instance sends every right-only variable to a distinct variable
that does not occur in the scope. -/
structure FreshFor (scope : List Var) (left right : Atom) (σ : Subst) : Prop where
  named : ∀ name ∈ rightOnly left right, ∃ fresh, σ name = some (.var fresh) ∧ fresh ∉ scope
  distinct : ∀ first ∈ rightOnly left right, ∀ second ∈ rightOnly left right,
    σ first = σ second → first = second

/-- Decide freshness of finite bindings. -/
def checkFresh (scope : List Var) (left right : Atom) (bindings : Bindings) : Bool :=
  (rightOnly left right).all (fun name => match bindings.toSubst name with
    | some (.var fresh) => decide (fresh ∉ scope)
    | _ => false) &&
    decide (∀ first ∈ rightOnly left right, ∀ second ∈ rightOnly left right,
      bindings.toSubst first = bindings.toSubst second → first = second)

theorem checkFresh_exact (scope : List Var) (left right : Atom) (bindings : Bindings) :
    checkFresh scope left right bindings = true ↔ FreshFor scope left right bindings.toSubst := by
  unfold checkFresh
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨named, distinct⟩
    refine ⟨fun name member => ?_, distinct⟩
    have image := named name member
    split at image
    · rename_i fresh bound
      exact ⟨fresh, bound, of_decide_eq_true image⟩
    · cases image
  · rintro ⟨named, distinct⟩
    refine ⟨fun name member => ?_, distinct⟩
    obtain ⟨fresh, bound, absent⟩ := named name member
    simp [bound, absent]

/-- The substitution that takes a fresh result to another choice of the
right-only variables. -/
def renewal (left right : Atom) (σ σ' : Subst) : Subst := fun name =>
  (rightOnly left right).findSome? fun original =>
    if σ original = some (.var name) then some ((σ' original).getD (.var original)) else none

theorem findSome?_unique {α β : Type} (items : List α) (f : α → Option β) (chosen : α)
    (member : chosen ∈ items) (value : β) (found : f chosen = some value)
    (unique : ∀ item ∈ items, (f item).isSome → item = chosen) :
    items.findSome? f = some value := by
  induction items with
  | nil => cases member
  | cons head rest ih =>
      cases selected : f head with
      | some other =>
          have same := unique head (List.mem_cons_self ..) (by simp [selected])
          subst same
          rw [found] at selected
          cases selected
          simp [List.findSome?, found]
      | none =>
          have later : chosen ∈ rest := by
            rcases List.mem_cons.mp member with here | there
            · subst here
              rw [found] at selected
              cases selected
            · exact there
          simp only [List.findSome?, selected]
          exact ih later fun item itemMember => unique item (List.mem_cons_of_mem _ itemMember)

theorem renewal_silent {scope : List Var} {left right : Atom} {σ : Subst}
    (fresh : FreshFor scope left right σ) (σ' : Subst) {name : Var} (inScope : name ∈ scope) :
    renewal left right σ σ' name = none := by
  unfold renewal
  rw [List.findSome?_eq_none_iff]
  intro original member
  obtain ⟨chosen, bound, absent⟩ := fresh.named original member
  have different : chosen ≠ name := fun same => absent (same ▸ inScope)
  simp [bound, different]

theorem renewal_at {scope : List Var} {left right : Atom} {σ : Subst}
    (fresh : FreshFor scope left right σ) (σ' : Subst) {original : Var}
    (member : original ∈ rightOnly left right) {chosen : Var}
    (bound : σ original = some (.var chosen)) :
    renewal left right σ σ' chosen = some ((σ' original).getD (.var original)) := by
  unfold renewal
  apply findSome?_unique _ _ original member _ (by simp [bound])
  intro item itemMember selected
  apply fresh.distinct item itemMember original member
  by_cases same : σ item = some (.var chosen)
  · rw [same, bound]
  · simp [same] at selected

/-- A fresh instance gives the most general result of its equation at its
position: any other instance with the same left side is reached from it by a
substitution that leaves the subject unchanged. -/
theorem fresh_most_general {left right : Atom} (context : Context) {σ σ' : Subst}
    (fresh : FreshFor (vars (context.fill (subst σ left))) left right σ)
    (sameMatch : subst σ' left = subst σ left) :
    ∃ θ : Subst, (∀ name ∈ vars (context.fill (subst σ left)), θ name = none) ∧
      subst θ (context.fill (subst σ right)) = context.fill (subst σ' right) := by
  let θ := renewal left right σ σ'
  have silent : ∀ name ∈ vars (context.fill (subst σ left)), θ name = none :=
    fun name member => renewal_silent fresh σ' member
  refine ⟨θ, silent, ?_⟩
  rw [Context.substitute_fill, Context.substitute_eq_self θ context _ silent,
    SubstitutionAlgebra.subst_subst]
  congr 1
  apply subst_congr_getD
  intro name member
  have agreeLeft := getD_agree_of_subst_eq σ' σ left sameMatch
  by_cases onLeft : name ∈ vars left
  · have inSubject : ∀ inner ∈ vars ((σ name).getD (.var name)),
        inner ∈ vars (context.fill (subst σ left)) := fun inner innerMember =>
      vars_fill_inner context _ inner (vars_replacement_subset σ left name onLeft inner innerMember)
    rw [agreeLeft name onLeft]
    cases bound : σ name with
    | none =>
        have here := inSubject name (by simp [bound, vars])
        simp [SubstitutionAlgebra.comp, bound, silent name here]
    | some value =>
        have keep : subst θ value = value := subst_eq_self_of_silent θ value fun inner innerMember =>
          silent inner (inSubject inner (by simpa [bound] using innerMember))
        simp [SubstitutionAlgebra.comp, bound, keep]
  · have rightMember : name ∈ rightOnly left right := by
      simp [rightOnly, member, onLeft]
    obtain ⟨chosen, bound, _⟩ := fresh.named name rightMember
    have renewed := renewal_at fresh σ' rightMember bound
    simp [SubstitutionAlgebra.comp, bound, subst, θ, renewed]

/-! ## Freshness of certificate rows -/

/-- A step row is fresh when its right-only variables become distinct
variables absent from the claim it extends. Other rows introduce no
variables. -/
def Row.fresh (table : List Claim) : Row → Bool
  | .step prior citation _ bindings =>
      match table[prior]?, equationSides citation.equation with
      | some (source, current), some (left, right) =>
          checkFresh (vars source ++ vars current) left right bindings
      | _, _ => false
  | _ => true

def freshRows (program : List Atom) : List Claim → List Row → Bool
  | _, [] => true
  | table, row :: rows =>
      match row.claim? program table with
      | some claim => row.fresh table && freshRows program (table ++ [claim]) rows
      | none => false

/-- The hygienic check: the certificate is accepted and every step instance
is fresh for the claim it extends. -/
def checkHygienic (program : List Atom) (certificate : Certificate) (claim : Claim) : Bool :=
  check program certificate claim && freshRows program [] certificate.rows

theorem Row.fresh_step_iff (table : List Claim) (prior : Nat) (citation : Citation)
    (path : List Nat) (bindings : Bindings) {source current left right : Atom}
    (atPrior : table[prior]? = some (source, current))
    (sides : equationSides citation.equation = some (left, right)) :
    (Row.step prior citation path bindings).fresh table = true ↔
      FreshFor (vars source ++ vars current) left right bindings.toSubst := by
  simp only [Row.fresh, atPrior, sides]
  exact checkFresh_exact _ _ _ _

theorem checkHygienic_sound {program : List Atom} {certificate : Certificate} {claim : Claim}
    (accepted : checkHygienic program certificate claim = true) :
    check program certificate claim = true ∧ freshRows program [] certificate.rows = true := by
  simpa [checkHygienic] using accepted

/-! ## Narrowing -/

/-- A supplied substitution `μ` that unifies a subatom with an instance of a
stored left side licenses rewriting the instantiated subject `μ source`. No
renaming apart is needed for this soundness. The theorem neither computes
`μ` nor says anything about HE's query semantics, strategy, freshness or
results. -/
theorem narrowing_step {space : Atomspace} {left right source focus target : Atom}
    {path : List Nat} (stored : Atom.equality left right ∈ space.atoms)
    (found : subatom? source path = some focus) (ρ μ : Subst)
    (unifies : subst μ focus = subst μ (subst ρ left))
    (replaced : replaceAt? source path (subst ρ right) = some target) :
    Step space (subst μ source) (subst μ target) := by
  obtain ⟨context, _, fill, replace⟩ := exists_context_of_subatom? found
  rw [replace] at replaced
  cases replaced
  rw [← fill, Context.substitute_fill, Context.substitute_fill, unifies,
    SubstitutionAlgebra.subst_subst, SubstitutionAlgebra.subst_subst]
  exact .rewrite _ _ stored

/-- `(f $x)` and `(f (g $x))` have no common instance: a rule variable that
shares its name with a subject variable can block the step. -/
theorem no_unifier_without_renaming (μ : Subst) :
    subst μ (.expression [.symbol "f", .var "x"]) ≠
      subst μ (.expression [.symbol "f", .expression [.symbol "g", .var "x"]]) := by
  intro same
  simp only [subst_expression, List.map_cons, List.map_nil, Atom.expression.injEq,
    List.cons.injEq, true_and, and_true] at same
  have sizes := congrArg sizeOf same
  simp [subst] at sizes
  omega

/-- After renaming the rule variable apart, the same subject and rule unify. -/
theorem unifier_after_renaming :
    ∃ μ : Subst, subst μ (.expression [.symbol "f", .var "x"]) =
      subst μ (.expression [.symbol "f", .expression [.symbol "g", .var "x1"]]) :=
  ⟨fun name => if name = "x" then some (.expression [.symbol "g", .var "x1"]) else none, by
    simp [subst, subst.substList]⟩

end Mettapedia.Languages.MeTTa.EquationKernel
