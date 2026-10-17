import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Normal

/-!
# Solution theory of finite type presentations

A finite type substitution denotes the equations carried by its entries.
Normal substitutions have a canonical syntactic valuation: apply the finite
substitution once to each variable.  This valuation satisfies every stored
equation, and every other satisfying valuation factors through it by ordinary
homomorphic atom substitution.  These facts separate principality from any
particular matcher or equality-class representation.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Theory

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement

/-- Equation semantics of one finite type presentation. -/
def TypeSubstSatisfied
    (valuation : String → Atom) (substitution : TypeSubst) : Prop :=
  ∀ name value, (name, value) ∈ substitution →
    valuation name = applyTypeValuation valuation value

/-- The syntactic valuation presented by one-pass finite substitution. -/
def presentedValuation (substitution : TypeSubst) : String → Atom :=
  fun name => substitution.apply (.var name)

private theorem atom_size_pos (atom : Atom) : 0 < sizeOf atom := by
  cases atom <;> simp

private theorem atom_size_lt_of_mem {atom : Atom} :
    ∀ {atoms : List Atom}, atom ∈ atoms → sizeOf atom < sizeOf atoms
  | head :: tail, hmem => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · simp
        omega
      · have hlt := atom_size_lt_of_mem htail
        simp
        omega

/-- Mapping every variable to itself is the identity valuation on atoms. -/
@[simp] theorem applyTypeValuation_var_identity : ∀ atom : Atom,
    applyTypeValuation (fun name => .var name) atom = atom := by
  intro atom
  suffices key : ∀ n (current : Atom), sizeOf current ≤ n →
      applyTypeValuation (fun name => .var name) current = current by
    exact key (sizeOf atom) atom le_rfl
  intro n
  induction n with
  | zero =>
      intro current hsize
      exact absurd hsize (by have := atom_size_pos current; omega)
  | succ n ih =>
      intro current hsize
      cases current with
      | symbol name => simp [applyTypeValuation]
      | var name => simp [applyTypeValuation]
      | grounded value => simp [applyTypeValuation]
      | expression atoms =>
          simp only [applyTypeValuation, Atom.expression.injEq]
          calc
            List.map
                (applyTypeValuation (fun name => .var name)) atoms =
                List.map id atoms := by
              apply List.map_congr_left
              intro child hchild
              apply ih child
              have hlt := atom_size_lt_of_mem hchild
              have hatoms : sizeOf atoms ≤ n := by
                simp at hsize
                omega
              omega
            _ = atoms := List.map_id atoms

/-- Applying a valuation after a finite presentation is the same as applying
the valuation induced by the presentation directly. -/
theorem applyTypeValuation_presentedValuation
    (valuation : String → Atom) (substitution : TypeSubst) :
    ∀ atom,
      applyTypeValuation valuation (substitution.apply atom) =
        applyTypeValuation
          (fun name => applyTypeValuation valuation
            (presentedValuation substitution name)) atom := by
  suffices key : ∀ n (atom : Atom), sizeOf atom ≤ n →
      applyTypeValuation valuation (substitution.apply atom) =
        applyTypeValuation
          (fun name => applyTypeValuation valuation
            (presentedValuation substitution name)) atom by
    intro atom
    exact key (sizeOf atom) atom le_rfl
  intro n
  induction n with
  | zero =>
      intro atom hsize
      exact absurd hsize (by have := atom_size_pos atom; omega)
  | succ n ih =>
      intro atom hsize
      cases atom with
      | symbol name => simp [TypeSubst.apply, applyTypeValuation]
      | var name => simp [applyTypeValuation, presentedValuation]
      | grounded value => simp [TypeSubst.apply, applyTypeValuation]
      | expression atoms =>
          simp only [TypeSubst.apply, applyTypeValuation,
            Atom.expression.injEq, List.map_map]
          apply List.map_congr_left
          intro child hchild
          apply ih child
          have hlt := atom_size_lt_of_mem hchild
          have hatoms : sizeOf atoms ≤ n := by
            simp at hsize
            omega
          omega

/-- A satisfying valuation absorbs one-pass presentation on every atom. -/
theorem TypeSubstSatisfied.absorbs
    {valuation : String → Atom} {substitution : TypeSubst}
    (satisfied : TypeSubstSatisfied valuation substitution) :
    ∀ atom,
      applyTypeValuation valuation (substitution.apply atom) =
        applyTypeValuation valuation atom := by
  intro atom
  rw [applyTypeValuation_presentedValuation]
  congr 1
  funext name
  unfold presentedValuation
  simp only [TypeSubst.apply]
  cases hlookup : substitution.lookup name with
  | none => simp [Option.getD, applyTypeValuation]
  | some value =>
      exact (satisfied name value
        (TypeSubst.lookup_eq_some_mem hlookup)).symm

/-- Applying the presented valuation homomorphically is literally one-pass
finite substitution. -/
theorem applyTypeValuation_presented_eq_apply
    (substitution : TypeSubst) (atom : Atom) :
    applyTypeValuation (presentedValuation substitution) atom =
      substitution.apply atom := by
  have composition := applyTypeValuation_presentedValuation
    (fun name => .var name) substitution atom
  simpa only [applyTypeValuation_var_identity] using composition.symm

private theorem lookup_eq_some_of_mem_of_nodup :
    ∀ {substitution : TypeSubst} {name : String} {value : Atom},
      substitution.keys.Nodup →
      (name, value) ∈ substitution →
      substitution.lookup name = some value := by
  intro substitution
  induction substitution with
  | nil => simp
  | cons head tail ih =>
      rcases head with ⟨key, stored⟩
      intro name value hnodup hmem
      simp only [TypeSubst.keys, List.map_cons,
        List.nodup_cons] at hnodup
      simp only [List.mem_cons, Prod.mk.injEq] at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨rfl, rfl⟩
        simp [TypeSubst.lookup]
      · have hne : name ≠ key := by
          intro heq
          subst name
          apply hnodup.1
          have : key ∈ tail.map Prod.fst := by
            exact List.mem_map.mpr ⟨(key, value), htail, rfl⟩
          simpa [TypeSubst.keys] using this
        simp [TypeSubst.lookup, hne, ih hnodup.2 htail]

/-- The presented valuation of a normal substitution satisfies every stored
equation. -/
theorem normal_presentedValuation_satisfied
    {substitution : TypeSubst} (normal : substitution.Normal) :
    TypeSubstSatisfied (presentedValuation substitution) substitution := by
  intro name value hmem
  have hlookup : substitution.lookup name = some value :=
    lookup_eq_some_of_mem_of_nodup normal.1 hmem
  have hleft : presentedValuation substitution name = value := by
    simp [presentedValuation, TypeSubst.apply, hlookup, Option.getD]
  rw [hleft]
  symm
  rw [applyTypeValuation_presented_eq_apply]
  apply TypeSubst.apply_eq_self_of_variables_not_keys
  exact normal.2 name value hmem

/-- Every satisfying valuation factors through the normal presentation's
canonical valuation. -/
theorem typeSubst_factorization
    {substitution : TypeSubst}
    {valuation : String → Atom}
    (satisfied : TypeSubstSatisfied valuation substitution) :
    ∀ atom,
      applyTypeValuation valuation
          (applyTypeValuation (presentedValuation substitution) atom) =
        applyTypeValuation valuation atom := by
  intro atom
  have hcanonicalApply :
      applyTypeValuation (presentedValuation substitution) atom =
        substitution.apply atom :=
    applyTypeValuation_presented_eq_apply substitution atom
  rw [hcanonicalApply]
  exact satisfied.absorbs atom

/-- A later normal presentation of a stronger theory absorbs an earlier
presentation on a whole syntactic operand. Rendered symbols and strings remain
opaque atoms; this is not an evaluator or contextual equivalence theorem. -/
theorem apply_absorbs_of_solution_implication {earlier later : TypeSubst}
    (normal : later.Normal)
    (refines : ∀ valuation, TypeSubstSatisfied valuation later →
      TypeSubstSatisfied valuation earlier) (atom : Atom) :
    later.apply (earlier.apply atom) = later.apply atom := by
  have satisfied := refines _ (normal_presentedValuation_satisfied normal)
  simpa only [applyTypeValuation_presented_eq_apply] using satisfied.absorbs atom

/-- Pending operands are transported together, retaining their physical order,
duplicates and shared variables under the same later presentation. -/
theorem map_apply_absorbs_of_solution_implication {earlier later : TypeSubst}
    (normal : later.Normal)
    (refines : ∀ valuation, TypeSubstSatisfied valuation later →
      TypeSubstSatisfied valuation earlier) (pending : List Atom) :
    (pending.map earlier.apply).map later.apply = pending.map later.apply := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro atom _
  exact apply_absorbs_of_solution_implication normal refines atom


/-! ## Boundary examples -/

private def tToA : TypeSubst := [("t", .symbol "A")]

/-- Positive: the canonical presentation of `$t := A` is a genuine model of
its stored equation. -/
theorem tToA_presented_model :
    TypeSubstSatisfied (presentedValuation tToA) tToA := by
  have normal : tToA.Normal := by
    simp [tToA, TypeSubst.Normal, TypeSubst.keys, TypeSubst.typeVars]
  exact normal_presentedValuation_satisfied normal

private def chainedNonNormal : TypeSubst :=
  [("x", .var "y"), ("y", .symbol "A")]

/-- Negative: a non-normal chained presentation is not generally its own
one-pass model; `$x := $y, $y := A` still presents `$x` as `$y` after one
pass, so its first equation is false under that presentation. -/
theorem chained_non_normal_presentation_not_model :
    ¬TypeSubstSatisfied
      (presentedValuation chainedNonNormal) chainedNonNormal := by
  intro satisfied
  have first := satisfied "x" (.var "y") (by
    simp [chainedNonNormal])
  simp [presentedValuation, chainedNonNormal,
    TypeSubst.apply, TypeSubst.lookup, applyTypeValuation,
    Option.getD] at first

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Theory

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.RuntimeRefinement Spec.Type.Presentation.Theory

/-- A finite readout table keeps exactly the nonidentity variable readings
on the supplied support. Its definition performs no proof search. -/
def finiteReadout (names : List String) (read : String → Atom) : TypeSubst :=
  (names.filter fun name => read name != .var name).map fun name => (name,read name)

theorem mem_finiteReadout {names : List String} {read : String → Atom} {name : String} {value : Atom} :
    (name,value)∈finiteReadout names read ↔
      name∈names ∧ read name≠.var name ∧ value=read name := by
  simp only [finiteReadout,List.mem_map,List.mem_filter,bne_iff_ne,Prod.mk.injEq]
  constructor
  · rintro ⟨key,⟨member,nonidentity⟩,same,value⟩
    subst key
    exact ⟨member,nonidentity,value.symm⟩
  · rintro ⟨member,nonidentity,rfl⟩
    exact ⟨name,⟨member,nonidentity⟩,rfl,rfl⟩

theorem finiteReadout_keys (names : List String) (read : String → Atom) :
    (finiteReadout names read).keys = names.filter (fun name => read name != .var name) := by
  simp only [finiteReadout,keys,List.map_map,Function.comp_def]
  exact List.map_id _

theorem finiteReadout_apply_var (names : List String) (read : String → Atom) (name : String) :
    (finiteReadout names read).apply (.var name)=
      if name∈names then read name else .var name := by
  induction names with
  | nil => simp [finiteReadout]
  | cons head tail ih =>
    by_cases self : read head=.var head
    · have tailEq : finiteReadout (head::tail) read=finiteReadout tail read := by
        simp [finiteReadout,self]
      rw [tailEq,ih]
      by_cases same : name=head
      · subst name
        simp [self]
      · simp [same]
    · have consEq : finiteReadout (head::tail) read=(head,read head)::finiteReadout tail read := by
        simp [finiteReadout,self]
      rw [consEq]
      by_cases same : name=head
      · subst name
        simp [apply,lookup]
      · simpa only [apply,lookup,same,↓reduceIte,List.mem_cons,false_or] using ih

/-- Matching a normal substitution's variable readout earns normality of
the finite table; an arbitrary table is not accepted as a presentation. -/
theorem finiteReadout_normal {names : List String} {read : String → Atom}
    {presentation : TypeSubst} (unique : names.Nodup) (normal : presentation.Normal)
    (same : ∀ name,read name=presentation.apply (.var name)) :
    (finiteReadout names read).Normal := by
  have supported : ∀ name∈(finiteReadout names read).keys,name∈presentation.keys := by
    intro name member
    rw [finiteReadout_keys] at member
    have different := (List.mem_filter.mp member).2
    by_contra absent
    have fixed : read name=.var name := by
      rw [same]
      simp [apply,lookup_eq_none_of_not_mem_keys absent]
    simp [fixed] at different
  refine ⟨?_,?_⟩
  · rw [finiteReadout_keys]
    exact unique.filter _
  · intro name value member key occurs inKeys
    obtain ⟨_,_,rfl⟩:=mem_finiteReadout.mp member
    rw [same] at occurs
    exact normal.apply_variable_not_key (.var name) key occurs (supported key inKeys)

/-- Two normal finite presentations with the same total variable readout
present precisely the same constraints. -/
theorem satisfied_iff_of_same_readout {left right : TypeSubst}
    (leftNormal : left.Normal) (rightNormal : right.Normal)
    (same : ∀ name,left.apply (.var name)=right.apply (.var name))
    (valuation : String → Atom) :
    TypeSubstSatisfied valuation left ↔ TypeSubstSatisfied valuation right := by
  have value_of_member {presentation : TypeSubst} (normal : presentation.Normal)
      {name : String} {value : Atom} (member : (name,value)∈presentation) :
      presentation.apply (.var name)=value := by
    have model := normal_presentedValuation_satisfied normal name value member
    change presentation.apply (.var name)=applyTypeValuation (presentedValuation presentation) value at model
    rw [applyTypeValuation_presented_eq_apply] at model
    exact model.trans (apply_eq_self_of_variables_not_keys _ _ (normal.2 name value member))
  constructor
  · intro satisfied name value member
    have absorbs := satisfied.absorbs (.var name)
    rw [same,value_of_member rightNormal member] at absorbs
    exact (by simpa only [applyTypeValuation] using absorbs.symm)
  · intro satisfied name value member
    have absorbs := satisfied.absorbs (.var name)
    rw [←same,value_of_member leftNormal member] at absorbs
    exact (by simpa only [applyTypeValuation] using absorbs.symm)

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst
