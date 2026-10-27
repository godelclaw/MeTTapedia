import Mettapedia.GSLT.Dedukti.LanguageDefSteps

/-!
# Steps keep terms well scoped

For a theory presented by a list of rules (`Presents`: no transparent definition, algebraic left sides, right sides that
use only the left side's pattern variables), a step from a term well scoped at a depth leads to a term well scoped at
that depth (`Step.wellScoped`). In particular steps of closed terms are closed.

- Lifting raises the depth by the amount lifted (`wellScoped_lift`), and substituting a well-scoped term for the
  outermost bound variable lowers it by one (`wellScoped_subst`), so beta keeps the depth.
- An instance of an algebraic pattern well scoped at a depth assigns well-scoped terms to the pattern's variables
  (`wellScoped_assignment`), and a term using only those variables is instantiated to a well-scoped term
  (`wellScoped_instantiate`), so a declared rule keeps the depth.
- A context lowers the depth by the binders it crosses (`wellScoped_plug`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti

open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0)
open Mettapedia.GSLT.LanguageDef.LFContextualBetaEta (Context)
open Mettapedia.GSLT.Dedukti.Language (Presents)

/-- **Lifting raises the depth** by the amount lifted. -/
theorem wellScoped_lift {term : Term} {depth : Nat} (wellScoped : WellScoped depth term) (amount : Nat) :
    ∀ cutoff, WellScoped (depth + amount) (lift amount cutoff term) := by
  induction wellScoped with
  | srt => intro _; exact .srt
  | con => intro _; exact .con
  | @var n k bound =>
    intro cutoff
    simp only [lift]
    split <;> exact .var (by omega)
  | @pi n domain body _ _ ihDomain ihBody =>
    intro cutoff
    exact .pi (ihDomain cutoff) (by simpa [Nat.add_right_comm] using ihBody (cutoff + 1))
  | @lam n domain body _ _ ihDomain ihBody =>
    intro cutoff
    exact .lam (ihDomain cutoff) (by simpa [Nat.add_right_comm] using ihBody (cutoff + 1))
  | app _ _ ihFunction ihArgument => intro cutoff; exact .app (ihFunction cutoff) (ihArgument cutoff)

/-- **Substitution lowers the depth by one**: a term well scoped one deeper, with a well-scoped term put in place of
a variable at or below the depth. -/
theorem wellScoped_subst : ∀ {term : Term} {depth : Nat}, WellScoped (depth + 1) term →
    ∀ {position : Nat} {replacement : Term}, position ≤ depth → WellScoped depth replacement →
      WellScoped depth (subst position replacement term)
  | .srt _, _, _, _, _, _, _ => .srt
  | .con _, _, _, _, _, _, _ => .con
  | .var k, depth, .var bound, position, replacement, below, replaced => by
    simp only [subst]
    split
    · exact replaced
    · split
      · exact .var (by omega)
      · exact .var (by omega)
  | .pi domain body, depth, .pi wellDomain wellBody, position, replacement, below, replaced =>
    .pi (wellScoped_subst wellDomain below replaced)
      (wellScoped_subst wellBody (by omega) (by simpa using wellScoped_lift replaced 1 0))
  | .lam domain body, depth, .lam wellDomain wellBody, position, replacement, below, replaced =>
    .lam (wellScoped_subst wellDomain below replaced)
      (wellScoped_subst wellBody (by omega) (by simpa using wellScoped_lift replaced 1 0))
  | .app function argument, depth, .app wellFunction wellArgument, position, replacement, below, replaced =>
    .app (wellScoped_subst wellFunction below replaced) (wellScoped_subst wellArgument below replaced)

theorem lift_zero_zero : ∀ term : Term, lift 0 0 term = term := by
  intro term
  have general : ∀ (term : Term) (cutoff : Nat), lift 0 cutoff term = term := by
    intro term
    induction term with
    | var k => intro cutoff; simp [lift]
    | srt => intro _; rfl
    | con => intro _; rfl
    | pi _ _ ihDomain ihBody => intro cutoff; simp [lift, ihDomain, ihBody]
    | lam _ _ ihDomain ihBody => intro cutoff; simp [lift, ihDomain, ihBody]
    | app _ _ ihFunction ihArgument => intro cutoff; simp [lift, ihFunction, ihArgument]
  exact general term 0

/-- **An instance of an algebraic pattern, well scoped at a depth, assigns well-scoped terms to its variables.** -/
theorem wellScoped_assignment {assignment : Nat → Term} {depth : Nat} :
    ∀ {pattern : Term} {headed : Bool}, algebraic headed pattern = true →
      WellScoped depth (instantiate assignment 0 pattern) → ∀ index ∈ patternVars pattern,
        WellScoped depth (assignment index)
  | .var k, _, _, wellScoped, index, found => by
    simp only [patternVars, List.mem_singleton] at found
    subst found
    simpa [instantiate, lift_zero_zero] using wellScoped
  | .app function argument, _, shape, wellScoped, index, found => by
    simp only [algebraic, Bool.and_eq_true] at shape
    simp only [instantiate] at wellScoped
    cases wellScoped with
    | app wellFunction wellArgument =>
      simp only [patternVars, List.mem_append] at found
      rcases found with found | found
      · exact wellScoped_assignment shape.1 wellFunction index found
      · exact wellScoped_assignment shape.2 wellArgument index found
  | .con _, _, _, _, _, found => by simp [patternVars] at found
  | .srt _, _, _, _, _, found => by simp [patternVars] at found
  | .pi _ _, _, shape, _, _, _ => by simp [algebraic] at shape
  | .lam _ _, _, shape, _, _, _ => by simp [algebraic] at shape

/-- **A term using only some variables is instantiated to a well-scoped term** when those variables are assigned
well-scoped terms. -/
theorem wellScoped_instantiate {allowed : List Nat} {assignment : Nat → Term} {depth : Nat}
    (assigned : ∀ index ∈ allowed, WellScoped depth (assignment index)) :
    ∀ (term : Term) (under : Nat), usesOnly allowed under term = true →
      WellScoped (depth + under) (instantiate assignment under term)
  | .var k, under, uses => by
    simp only [usesOnly, Bool.or_eq_true, decide_eq_true_eq] at uses
    simp only [instantiate]
    split
    · exact .var (by omega)
    · rcases uses with bound | found
      · omega
      · simpa [Nat.add_comm] using wellScoped_lift (assigned _ found) under 0
  | .srt _, _, _ => .srt
  | .con _, _, _ => .con
  | .pi domain body, under, uses => by
    simp only [usesOnly, Bool.and_eq_true] at uses
    have inner := wellScoped_instantiate assigned body (under + 1) uses.2
    rw [← Nat.add_assoc] at inner
    exact .pi (wellScoped_instantiate assigned domain under uses.1) inner
  | .lam domain body, under, uses => by
    simp only [usesOnly, Bool.and_eq_true] at uses
    have inner := wellScoped_instantiate assigned body (under + 1) uses.2
    rw [← Nat.add_assoc] at inner
    exact .lam (wellScoped_instantiate assigned domain under uses.1) inner
  | .app function argument, under, uses => by
    simp only [usesOnly, Bool.and_eq_true] at uses
    exact .app (wellScoped_instantiate assigned function under uses.1) (wellScoped_instantiate assigned argument under uses.2)

/-- The binders a context crosses. -/
def contextDepth : Context → Nat
  | .hole => 0
  | .piDomain rest _ | .lamDomain rest _ | .appFunction rest _ | .appArgument _ rest => contextDepth rest
  | .piBody _ rest | .lamBody _ rest => contextDepth rest + 1

/-- **A context lowers the depth by the binders it crosses**: the hole of a well-scoped plugging is well scoped one
binder deeper for each binder crossed, and plugging such a term back is well scoped. -/
theorem wellScoped_plug : ∀ (context : Context) {source : Term} {depth : Nat},
    WellScoped depth (context.plug source) →
      WellScoped (depth + contextDepth context) source ∧
        ∀ {target : Term}, WellScoped (depth + contextDepth context) target → WellScoped depth (context.plug target)
  | .hole, _, _, wellScoped => ⟨wellScoped, fun target => target⟩
  | .piDomain rest body, _, _, .pi wellDomain wellBody => by
    have inner := wellScoped_plug rest wellDomain
    exact ⟨inner.1, fun target => .pi (inner.2 target) wellBody⟩
  | .piBody domain rest, _, depth, .pi wellDomain wellBody => by
    have inner := wellScoped_plug rest wellBody
    have same : depth + 1 + contextDepth rest = depth + contextDepth (.piBody domain rest) := by
      simp only [contextDepth]
      omega
    rw [same] at inner
    exact ⟨inner.1, fun target => .pi wellDomain (inner.2 target)⟩
  | .lamDomain rest body, _, _, .lam wellDomain wellBody => by
    have inner := wellScoped_plug rest wellDomain
    exact ⟨inner.1, fun target => .lam (inner.2 target) wellBody⟩
  | .lamBody domain rest, _, depth, .lam wellDomain wellBody => by
    have inner := wellScoped_plug rest wellBody
    have same : depth + 1 + contextDepth rest = depth + contextDepth (.lamBody domain rest) := by
      simp only [contextDepth]
      omega
    rw [same] at inner
    exact ⟨inner.1, fun target => .lam wellDomain (inner.2 target)⟩
  | .appFunction rest argument, _, _, .app wellFunction wellArgument => by
    have inner := wellScoped_plug rest wellFunction
    exact ⟨inner.1, fun target => .app (inner.2 target) wellArgument⟩
  | .appArgument function rest, _, _, .app wellFunction wellArgument => by
    have inner := wellScoped_plug rest wellArgument
    exact ⟨inner.1, fun target => .app wellFunction (inner.2 target)⟩

variable {theory : Theory} {rules : List RewriteRule}

/-- **A root contraction keeps the depth.** -/
theorem RootStep.wellScoped (presents : Presents theory rules) {source target : Term}
    (step : RootStep theory source target) {depth : Nat} (wellScoped : WellScoped depth source) :
    WellScoped depth target := by
  cases step with
  | beta domain body argument =>
    cases wellScoped with
    | app wellFunction wellArgument =>
      cases wellFunction with
      | lam _ wellBody => exact wellScoped_subst wellBody (Nat.zero_le _) wellArgument
  | delta defined => rw [presents.undefined] at defined; cases defined
  | rule assignment declared =>
    have member := (presents.rule_iff _).mp declared
    have assigned := wellScoped_assignment (presents.leftAlgebraic _ member) wellScoped
    simpa using wellScoped_instantiate assigned _ 0 (presents.rightDetermined _ member)

/-- **A step keeps the depth**; steps of closed terms are closed. -/
theorem Step.wellScoped (presents : Presents theory rules) {source target : Term} (step : Step theory source target)
    {depth : Nat} (wellScoped : WellScoped depth source) : WellScoped depth target := by
  cases step with
  | inContext context root =>
    have split := wellScoped_plug context wellScoped
    exact split.2 (RootStep.wellScoped presents root split.1)

end Mettapedia.GSLT.Dedukti
